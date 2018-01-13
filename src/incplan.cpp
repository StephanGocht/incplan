#include "ipasir/ipasir_cpp.h"

#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <vector>
#include <iostream>
#include <fstream>
#include <limits>
#include <cassert>
#include <memory>
#include <cmath>
#include <set>
#include <map>
#include <random>
#include <stack>
#include <utility>
#include <sstream>

#include "tclap/CmdLine.h"

#include "TimeSlotMapping.h"
#include "TimePointBasedSolver.h"
#include "carj/carj.h"
#include "carj/logging.h"
#include "carj/ScopedTimer.h"

#include "TimeoutClock.h"
#include "DimspecProblem.h"

#include "PDR.h"

extern "C" {
	#include "lglib.h"
}

TCLAP::CmdLine& carj::getCmd() {
	static TCLAP::CmdLine cmd("This tool is does sat planing using an incremental sat solver.", ' ', "0.1");
	return cmd;
}

TCLAP::CmdLine& cmd = carj::getCmd();

namespace option{
	carj::TCarjArg<TCLAP::ValueArg,int> allSolutions("", "allSolutions", "0 do nothing, 1 avoid same solution, 2 avoid solution with same states, 3 avoid solution with same actions (only possible if action literals are provided)", /* necessary */ false, /*default*/ 0, /* type description */ "positive number", cmd);

	carj::TCarjArg<TCLAP::ValueArg,int> seed("", "seed", "Use a positive number to choose a seed for randomization, -1 to use a random seed or -2 to deactivate randomization.", /* necessary */ false, /*default*/ -2, /* type description */ "number", cmd);

	carj::TCarjArg<TCLAP::ValueArg,int> maxSizeLearnedClause("", "maxSizeLearnedClause", "Maximum number of literals in a learned clause that will be transformed to future time steps.", /* necessary */ false, /*default*/ 2, /* type description */ "positive number", cmd);

	carj::TCarjArg<TCLAP::ValueArg,int> exhaustMakeSpan("", "exhaustMakeSpan", "Maximum makespan to exhaust learn new transfer clauses.", /* necessary */ false, /*default*/ 2, /* type description */ "positive number", cmd);
	carj::TCarjArg<TCLAP::ValueArg,int> learnMakeSpan("", "learnMakeSpan", "Maximum makespan to learn new transfer clauses.", /* necessary */ false, /*default*/ 2, /* type description */ "positive number", cmd);
	carj::TCarjArg<TCLAP::ValueArg,float> timeout("", "timeout", "Timeout in seconds to switch strategies.", /* necessary */ false, /*default*/ 2, /* type description */ "positive float", cmd);
	//TCLAP::SwitchArg outputLinePerStep("", "outputLinePerStep", "Output each time point in a new line. Each time point will use the same literals.", /*default*/ false);
	carj::CarjArg<TCLAP::SwitchArg, bool> icaps2017Version("", "icaps2017", "Use this option to use encoding as used in the icaps paper.", cmd, /*default*/ false);
	carj::CarjArg<TCLAP::SwitchArg, bool> unitInGoal2Assume("u", "unitInGoal2Assume", "Add units in goal clauses using assume instead of add. (singleEnded only)", cmd, /*default*/ false);
	carj::CarjArg<TCLAP::SwitchArg, bool> useAddLearned("", "useAddLearned", "Use unofficial ipasir extension add_learned_clause.", cmd, /*default*/ false);
}

enum class HelperVariables { ZeroVariableIsNotAllowed_DoNotRemoveThis,
	ActivationLiteral, MarkerLiteral };

class Solver;

class ISolverStrategy {
public:
	virtual ~ISolverStrategy() = default;

	/**
	 * Initialize the first timepoints and return the timepoint inserted last.
	 */
	virtual void doInitialize() = 0;

	/**
	 * Finalize the formula after one or more time points have been added.
	 * This will be executed immedeatly before the call to solve of the
	 * SAT solver, so it is the place to make necessary assumptions.
	 */
	virtual void doFinalize() = 0;

	virtual void preSolveHook(){};
	virtual void preStepHook(){};

	/**
	 * This hook is called after a timeout occurs. Set the necessary assumptions
	 * for the next solve call here.
	 */
	virtual void timeoutHook(){};
	virtual void postStepHook(){};

	virtual Solver& getSolver(){return *this->solver;};
	virtual void setSolver(Solver* _solver) {this->solver = _solver;};

private:
	Solver *solver;
};

class ISolverStrategyDecorator: public ISolverStrategy {
public:
	ISolverStrategyDecorator(std::unique_ptr<ISolverStrategy> _strategy):
		strategy(std::move(_strategy))
	{

	}

	virtual ~ISolverStrategyDecorator() = default;

	virtual void doInitialize(){
		strategy->doInitialize();
	};
	virtual void doFinalize(){
		strategy->doFinalize();
	};
	virtual void preSolveHook(){
		strategy->preSolveHook();
	};
	virtual void preStepHook(){
		strategy->preStepHook();
	};
	virtual void postStepHook(){
		strategy->postStepHook();
	};
	virtual void timeoutHook(){
		strategy->timeoutHook();
	}

	virtual void setSolver(Solver* solver) {
		ISolverStrategy::setSolver(solver);
		strategy->setSolver(solver);
	};

private:
	std::unique_ptr<ISolverStrategy> strategy;
};

std::unique_ptr<ipasir::Ipasir> solverWithRandomizedOptions() {
	std::unique_ptr<ipasir::Ipasir> result;
	result = std::make_unique<ipasir::Solver>();

	if (option::seed.getValue() == -1) {
		result = std::make_unique<ipasir::RandomizedSolver>(std::move(result));
	} else if (option::seed.getValue() >= 0) {
		result = std::make_unique<ipasir::RandomizedSolver>(
			option::seed.getValue(),
			std::move(result));
	}

	LOG(INFO) << "Using solver " << result->signature();
	return result;
}

class Solver : public TimePointBasedSolver {
public:
	std::unique_ptr<ISolverStrategy> strategy;
	std::function<int(int)> stepToMakespan;
	TimePoint elementInsertedLast;
	DimspecProblem& problem;

	int finalMakeSpan;
	int makeSpan;
	ipasir::SolveResult solveResult;
	std::unique_ptr<TimePointManager> timePointManager;
	std::vector<TimePoint> newTimepoints;

	public:
		Solver(
			DimspecProblem& _problem,
			std::unique_ptr<ISolverStrategy> _strategy,
			std::function<int(int)> _stepToMakespan):

			TimePointBasedSolver(
				_problem.numberLiteralsPerTime,
				/* Number of Helper Variables */ 2,
				//std::make_unique<ipasir::Solver>(),
				solverWithRandomizedOptions(),
				option::icaps2017Version.getValue()?
					TimePointBasedSolver::HelperVariablePosition::AllBefore:
					TimePointBasedSolver::HelperVariablePosition::SingleAfter),
			strategy(std::move(_strategy)),
			stepToMakespan(_stepToMakespan),
			problem(_problem),
			finalMakeSpan(0),
			makeSpan(0),
			timePointManager(nullptr)
		{
			strategy->setSolver(this);
		}

		/**
		 * Solve the problem. Return true if a solution was found.
		 */
		bool solve(){
			int step = 0;
			strategy->doInitialize();

			ipasir::SolveResult result = ipasir::SolveResult::UNSAT;
			for (;result != ipasir::SolveResult::SAT;step++) {
				strategy->preStepHook();

				auto newTimepoint = addNewTimePoints(step);
				if (newTimepoint != nullptr) {
					elementInsertedLast = *newTimepoint;
				}

				strategy->preSolveHook();

				strategy->doFinalize();

				VLOG(1) << "Solving makespan " << makeSpan;
				auto& solves = carj::getCarj().data["/incplan/result/solves"_json_pointer];
				solves.push_back({
					{"makespan", makeSpan},
					{"time", -1}
				});
				{
					carj::ScopedTimer timer((*solves.rbegin())["time"]);
					TIMED_SCOPE(blkScope, "solve");
					bool done = false;
					while (!done) {
						result = solveSAT();
						if (result == ipasir::SolveResult::TIMEOUT) {
							strategy->timeoutHook();
						} else {
							done = true;
						}

					}
				}

				if (result != ipasir::SolveResult::SAT) {
					strategy->postStepHook();
				}
				newTimepoints.clear();
				carj::getCarj().write();
			}


			this->finalMakeSpan = this->makeSpan;
			this->solveResult = result;

			if (result == ipasir::SolveResult::SAT) {
				storeSolution();
			}

			return result == ipasir::SolveResult::SAT;
		}

		bool avoidLiteral(int lit) {
			switch (option::allSolutions.getValue()) {
				case 2:
					return std::find(
						problem.stateVariables.begin(),
						problem.stateVariables.end(),
						std::abs(lit))
						== problem.stateVariables.end();
				case 3:
					return std::find(
						problem.actionVariables.begin(),
						problem.actionVariables.end(),
						std::abs(lit))
						== problem.actionVariables.end();
				case 1:
				default:
					return false;
			}
		}

		bool nextSolution() {
			TimePoint t = timePointManager->getFirst();
			for (auto& timePointSolution: problem.solution) {
				for (int lit: timePointSolution) {
					if (!avoidLiteral(lit)) {
						addProblemLiteral(-lit, t);
					}
				}

				if (t == timePointManager->getLast()) {
					break;
				}
				try {
					// todo improve with propper itterator, as t == last
					// fails for double ended encoding, if no transition
					// was added
					t = timePointManager->getSuccessor(t);
				} catch (std::out_of_range& e){
					break;
				}
			}
			finalizeClause();

			strategy->doFinalize();
			ipasir::SolveResult result = solveSAT();
			if (result == ipasir::SolveResult::SAT) {
				storeSolution();
			}

			return (result == ipasir::SolveResult::SAT);
		}

		/**
		 * @arg outputSolverLike
		 *     if true print one line where variables from different time points
		 *         are named differently
		 *     if false print one line per time step
		 */
		void storeSolution() {
			problem.solution.clear();

			if (this->solveResult == ipasir::SolveResult::SAT) {
				TimePoint t = timePointManager->getFirst();
				int time = 0;

				do {
					problem.solution.push_back(std::vector<int>());
					for (unsigned j = 1; j <= this->problem.numberLiteralsPerTime; j++) {
						int val = valueProblemLiteral(j,t);
						problem.solution.back().push_back(val);
					}

					if (t == timePointManager->getLast()) {
						break;
					}
					try {
						// todo improve with propper itterator, as t == last
						// fails for double ended encoding, if no transition
						// was added
						t = timePointManager->getSuccessor(t);
					} catch (std::out_of_range& e){
						break;
					}

					time++;
				} while (true);
			}

			problem.storedSolutionNotifier();
		}

		~Solver(){
		}

	public:
		virtual void reset(){
			TimePointBasedSolver::reset();
			makeSpan = 0;
			timePointManager = nullptr;
		}

		void exhaustiveInitialFixed() {
			TIMED_SCOPE(blkScope, "initFixed");
			for (int lit: problem.goal) {
				assumeProblemLiteral(lit, timePointManager->getLast());
				assumeInitial(timePointManager->getFirst());
				solveSAT();
			}
		}

		void exhaustiveGoalFixed() {
			TIMED_SCOPE(blkScope, "goalFixed");
			for (int lit: problem.initial) {
				assumeProblemLiteral(lit, timePointManager->getFirst());
				assumeGoal(timePointManager->getLast());
				solveSAT();
			}
		}

		// void exhaustiveSearch() {
		// 	TIMED_SCOPE(blkScope, "exhaust");
		// 	unsigned numGoalLiterals = 0;
		// 	unsigned numUnreachabel = 0;

		// 	// check which goal/init variables are unreachable
		// 	const std::vector<int>* clauseSet;
		// 	if (timePointManager->isOnForwardStack(elementInsertedLast)) {
		// 		clauseSet = &problem.goal;
		// 	} else {
		// 		clauseSet = &problem.initial;
		// 	}
		// 	for (int lit: *clauseSet) {
		// 		if (lit != 0) {
		// 			numGoalLiterals++;
		// 			assumeProblemLiteral(lit, elementInsertedLast);
		// 			result = solveSAT();
		// 			if (result == ipasir::SolveResult::UNSAT) {
		// 				addProblemLiteral(-lit, elementInsertedLast);
		// 				finalizeClause();
		// 				numUnreachabel++;
		// 			};
		// 		}
		// 	}

		// 	LOG(INFO) << "Unreachable: " << numUnreachabel << "/" << numGoalLiterals;

		// 	std::function<TimePoint(TimePoint)> next = [this](TimePoint t) {
		// 		return timePointManager->getPredecessor(t);
		// 	};
		// 	TimePoint last = timePointManager->getFirst();
		// 	if (!timePointManager->isOnForwardStack(elementInsertedLast)) {
		// 		next = [this](TimePoint t) {
		// 			return timePointManager->getSuccessor(t);
		// 		};
		// 		last = timePointManager->getLast();
		// 	}

		// 	// int blockedStates = 0;
		// 	// for (int var: problem.stateVariables) {
		// 	// 	TimePoint t = elementInsertedLast;
		// 	// 	std::vector<TimePoint> timepoints;
		// 	// 	while(t != last) {
		// 	// 		assumeProblemLiteral(-var, t);
		// 	// 		timepoints.push_back(t);
		// 	// 		t = next(t);
		// 	// 	}
		// 	// 	result = solveSAT();
		// 	// 	if (result == ipasir::SolveResult::UNSAT) {
		// 	// 		blockedStates++;
		// 	// 		for (TimePoint t: timepoints) {
		// 	// 			addProblemLiteral(var, t);
		// 	// 		}
		// 	// 		finalizeClause();
		// 	// 	}
		// 	// }
		// 	// LOG(INFO) << "BlockedStates: " << blockedStates << "/" << problem.stateVariables.size();
		// }

		/*
		 * Returns the TimePoint added last or null if no Timepoint was added.
		 */
		std::unique_ptr<TimePoint> addNewTimePoints(unsigned step) {
			std::unique_ptr<TimePoint> tNew = nullptr;
			int targetMakeSpan = stepToMakespan(step);

			for (; this->makeSpan < targetMakeSpan; this->makeSpan++) {
				tNew = std::make_unique<TimePoint>(timePointManager->aquireNext());
				newTimepoints.push_back(*tNew);
				addInvariantClauses(*tNew);

				if (timePointManager->isOnForwardStack(*tNew)) {
					TimePoint pred = timePointManager->getPredecessor(*tNew);
					addTransferClauses(pred, *tNew);
				} else {
					TimePoint succ = timePointManager->getSuccessor(*tNew);
					addTransferClauses(*tNew, succ);
				}
			}

			return tNew;
		}


		void addInitialClauses(TimePoint t) {
			for (int literal:problem.initial) {
				addProblemLiteral(literal, t);
			}
		}

		void addInvariantClauses(TimePoint t) {
			for (int literal: problem.invariant) {
				addProblemLiteral(literal, t);
			}
		}

		void addTransferClauses(TimePoint source, TimePoint destination) {
			for (int literal: problem.transfer) {
				bool literalIsSourceTime = static_cast<unsigned>(std::abs(literal)) <= problem.numberLiteralsPerTime;
				if (!literalIsSourceTime) {
					if (literal > 0) {
						literal -= problem.numberLiteralsPerTime;
					} else {
						literal += problem.numberLiteralsPerTime;
					}
				}

				if (literalIsSourceTime) {
					addProblemLiteral(literal, source);
				} else {
					addProblemLiteral(literal, destination);
				}
			}
		}

		void assumeGoal(TimePoint t) {
			for (unsigned i = 0; i < problem.goal.size(); i += 2) {
				assumeProblemLiteral(problem.goal[i], t);
				assert(problem.goal[i + 1] == 0);
			}
		}

		void assumeInitial(TimePoint t) {
			for (unsigned i = 0; i < problem.initial.size(); i += 2) {
				assumeProblemLiteral(problem.initial[i], t);
				assert(problem.initial[i + 1] == 0);
			}
		}

		/*
		 * Returns true if problem.goal[i] is a literal in a unit clause
		 *         false otherwise.
		 */
		bool isUnitGoal(unsigned i) {
			if (!option::unitInGoal2Assume.getValue()) {
				return false;
			}

			if (i == 0) {
				return problem.goal[i + 1] == 0;
			}

			if (problem.goal[i] == 0) {
				return false;
			}

			assert(i > 0 && i + 1 < problem.goal.size());
			return problem.goal[i + 1] == 0 && problem.goal[i - 1] == 0;
		}

		void addGoalClauses(TimePoint t, bool isGuarded = false) {
			for (unsigned i = 0; i < problem.goal.size(); i++) {
				int literal = problem.goal[i];
				if (isUnitGoal(i) && isGuarded) {
					assumeProblemLiteral(literal, t);
					++i; // skip following 0
					assert(problem.goal[i] == 0);
				} else {
					if (literal == 0 && isGuarded) {
						int activationLiteral = static_cast<int>(HelperVariables::ActivationLiteral);
						addHelperLiteral(-activationLiteral, t);
					}
					addProblemLiteral(literal, t);
				}
			}
		}
};

class PreFinalizationSolveStrategy: public ISolverStrategyDecorator {
public:
	PreFinalizationSolveStrategy(std::unique_ptr<ISolverStrategy> _strategy):
		ISolverStrategyDecorator(std::move(_strategy))
	{
	}

	virtual void preSolveHook(){
		ISolverStrategyDecorator::preSolveHook();
		getSolver().solveSAT();
	}

	virtual ~PreFinalizationSolveStrategy() = default;
};

class CleanAktivationLiteralStrategy: public ISolverStrategyDecorator {
public:
	CleanAktivationLiteralStrategy(std::unique_ptr<ISolverStrategy> _strategy):
		ISolverStrategyDecorator(std::move(_strategy))
	{
	}

	virtual ~CleanAktivationLiteralStrategy() = default;

	virtual void postStepHook(){
		ISolverStrategyDecorator::postStepHook();
		int activationLiteral = static_cast<int>(HelperVariables::ActivationLiteral);
		getSolver().addHelperLiteral(-activationLiteral, getSolver().elementInsertedLast);
		getSolver().finalizeClause();
	}
};


class SingleEndedStrategy: public ISolverStrategy {
public:
	virtual ~SingleEndedStrategy() = default;

	virtual void doInitialize(){
		getSolver().timePointManager =
			std::make_unique<SingleEndedTimePointManager>();

		TimePoint t0 = getSolver().timePointManager->aquireNext();
		getSolver().addInitialClauses(t0);
		getSolver().addInvariantClauses(t0);

		getSolver().elementInsertedLast = t0;
	};

	virtual void doFinalize(){
		TimePoint elementInsertedLast = getSolver().elementInsertedLast;
		getSolver().addGoalClauses(elementInsertedLast, true);
		int activationLiteral = static_cast<int>(HelperVariables::ActivationLiteral);
		getSolver().assumeHelperLiteral(activationLiteral, elementInsertedLast);
	};
};

class NonIncrementalStrategy: public SingleEndedStrategy {
public:
	virtual ~NonIncrementalStrategy() = default;

	virtual void preStepHook(){
		getSolver().reset();
		doInitialize();
	}

	virtual void doFinalize(){
		TimePoint elementInsertedLast = getSolver().elementInsertedLast;
		getSolver().addGoalClauses(elementInsertedLast);
	};
};
// class NonIncrementalStrategy: public ISolverStrategyDecorator {
// public:
// 	NonIncrementalStrategy(std::unique_ptr<ISolverStrategy> _strategy):
// 		ISolverStrategyDecorator(std::move(_strategy))
// 	{
// 	}

// 	virtual void preStepHook(){
// 		getSolver().reset();
// 		doInitialize();
// 		ISolverStrategyDecorator::preStepHook();
// 	}
// };

class DoubleEndedStrategy: public ISolverStrategy {
private:
	float ratio;

public:
	DoubleEndedStrategy(float _ratio):
		ratio(_ratio)
	{

	}

	virtual ~DoubleEndedStrategy() = default;


	virtual void doInitialize(){
		getSolver().timePointManager =
			std::make_unique<DoubleEndedTimePointManager>(
				ratio,
				DoubleEndedTimePointManager::TopElementOption::Dublicated);
		TimePoint t0 = getSolver().timePointManager->aquireNext();
		getSolver().addInitialClauses(t0);
		getSolver().addInvariantClauses(t0);

		TimePoint tN = getSolver().timePointManager->aquireNext();
		getSolver().addGoalClauses(tN);
		getSolver().addInvariantClauses(tN);

		getSolver().elementInsertedLast = tN;
	};

	virtual void doFinalize(){
		TimePoint elementInsertedLast = getSolver().elementInsertedLast;
		auto& timePointManager = getSolver().timePointManager;

		TimePoint linkSource, linkDestination;
		if (elementInsertedLast == timePointManager->getLast()) {
			linkSource = timePointManager->getFirst();
			linkDestination = timePointManager->getLast();
		} else if (timePointManager->isOnForwardStack(elementInsertedLast)){
			linkSource = elementInsertedLast;
			linkDestination = timePointManager->getSuccessor(
				timePointManager->getPredecessor(elementInsertedLast));
		} else {
			linkSource = timePointManager->getPredecessor(
				timePointManager->getSuccessor(elementInsertedLast));
			linkDestination = elementInsertedLast;
		}

		addLink(linkSource, linkDestination, elementInsertedLast);

		int activationLiteral = static_cast<int>(HelperVariables::ActivationLiteral);
		getSolver().assumeHelperLiteral(activationLiteral, elementInsertedLast);

		freeze(linkSource, linkDestination);
	};

	void freeze(TimePoint src, TimePoint dst) {
		LOG(INFO) << "Freezing Variables";
		LGL* lgl = static_cast<LGL*>(this->getSolver().solver->internalSolverReference());
		lglmeltall(lgl);
		for (int i = 1; i <= this->getSolver().varsPerTime; i++) {
			lglfreeze(lgl, this->getSolver().problemLiteral2Ipasir(i, src));
			lglfreeze(lgl, this->getSolver().problemLiteral2Ipasir(i, dst));
		}
		for (int i = 1; i <= this->getSolver().helperPerTime; i++) {
			lglfreeze(lgl, this->getSolver().helperLiteral2Ipasir(i, src));
			lglfreeze(lgl, this->getSolver().helperLiteral2Ipasir(i, dst));
		}
	}

	void addLink(TimePoint A, TimePoint B, TimePoint helperLiteralBinding) {
		unsigned numberLiteralsPerTime = getSolver().problem.numberLiteralsPerTime;
		for (unsigned i = 1; i <= numberLiteralsPerTime; i++) {
			int activationLiteral = static_cast<int>(HelperVariables::ActivationLiteral);

			getSolver().addHelperLiteral(-activationLiteral, helperLiteralBinding);
			getSolver().addProblemLiteral(-i, A);
			getSolver().addProblemLiteral(i, B);
			getSolver().finalizeClause();

			getSolver().addHelperLiteral(-activationLiteral, helperLiteralBinding);
			getSolver().addProblemLiteral(i, A);
			getSolver().addProblemLiteral(-i, B);
			getSolver().finalizeClause();
		}
	}
};

class LooseDoubleEndedStrategy: public DoubleEndedStrategy {
private:
	float ratio;

public:
	LooseDoubleEndedStrategy(float _ratio):
		DoubleEndedStrategy(_ratio),
		ratio(_ratio)
	{

	}

	virtual ~LooseDoubleEndedStrategy() = default;


	virtual void doInitialize(){
		getSolver().timePointManager =
			std::make_unique<DoubleEndedTimePointManager>(
				ratio,
				DoubleEndedTimePointManager::TopElementOption::Dublicated);
		TimePoint t0 = getSolver().timePointManager->aquireNext();
		getSolver().addInvariantClauses(t0);
		addMarkedClauses(getSolver().problem.initial, t0);

		TimePoint tN = getSolver().timePointManager->aquireNext();
		getSolver().addInvariantClauses(tN);
		addMarkedClauses(getSolver().problem.goal, tN);

		getSolver().elementInsertedLast = tN;
	};

	virtual void doFinalize(){
		DoubleEndedStrategy::doFinalize();
		int markerLiteral = static_cast<int>(HelperVariables::MarkerLiteral);
		TimePoint t0 = getSolver().timePointManager->getFirst();
		TimePoint tN = getSolver().timePointManager->getLast();
		getSolver().assumeHelperLiteral(markerLiteral, t0);
		getSolver().assumeHelperLiteral(markerLiteral, tN);
	}

	void addMarkedClauses(const std::vector<int> &clauses, TimePoint t) {
		for (int literal:clauses) {
			if (literal == 0) {
				int markerLiteral = static_cast<int>(HelperVariables::MarkerLiteral);
				getSolver().addHelperLiteral(-markerLiteral, t);
			}
			getSolver().addProblemLiteral(literal, t);
		}
	}
};

class UltimateDoubleEndedStrategy: public LooseDoubleEndedStrategy {
private:
	std::vector<std::vector<TimedLiteral>> learnedClauses;
	std::vector<std::vector<TimedLiteral>> newLearnedClauses;
	std::vector<int> numNeccessaryTransferes;
	TimeoutClock timeOutClock;

	bool learning;
public:
	UltimateDoubleEndedStrategy(float _ratio):
			LooseDoubleEndedStrategy(_ratio)
	{
		timeOutClock.setTimeout(option::timeout.getValue());
	}

	virtual ~UltimateDoubleEndedStrategy() = default;

	virtual void doInitialize(){
		learning = true;
		LooseDoubleEndedStrategy::doInitialize();

		getSolver().solver->set_terminate(timeOutClock.getTimeoutCallback());
		setLearnedCallback();
	}

	bool hasMarkerLiteral(const std::vector<TimedLiteral>& clause) {
		int markerLiteral = static_cast<int>(HelperVariables::MarkerLiteral);
		int activationLiteral = static_cast<int>(HelperVariables::ActivationLiteral);
		for (const TimedLiteral &lit:clause) {
			if (lit.isHelper) {
				if ((lit.literal == -markerLiteral)
					|| lit.literal == -activationLiteral) {
					return true;
				}
			}
		}
		return false;
	}

	bool isOneSided(const std::vector<TimedLiteral>& clause) {
		if (clause.size() > 0) {
			int sideIdentifier = clause.front().t.first;
			for (const TimedLiteral &lit:clause) {
				if (lit.t.first != sideIdentifier) {
					return false;
				}
			}
		}

		return true;
	}

	void normalizeClause(std::vector<TimedLiteral>& clause){
		assert(isOneSided(clause));

		if (clause.front().t.first == DoubleEndedTimePointManager::FROM_END){
			int numTransferes = numNeccessaryTransferes.back();
			for (TimedLiteral& lit:clause){
				lit.t.first = DoubleEndedTimePointManager::FROM_BEGIN;
				lit.t.second = numTransferes - lit.t.second;
			}
		}
	}

	void adeptLearned() {
		DoubleEndedTimePointManager* tpm =
			dynamic_cast<DoubleEndedTimePointManager*>(
				getSolver().timePointManager.get());

		for (std::vector<TimedLiteral>& clause: newLearnedClauses) {
			if (clause.size() > 0 && !hasMarkerLiteral(clause)) {
				if (tpm->isOnForwardStack(clause.front().t)) {
					numNeccessaryTransferes.push_back(tpm->getBeginTop().second);
				} else {
					numNeccessaryTransferes.push_back(tpm->getEndTop().second);
				}
				normalizeClause(clause);
				learnedClauses.push_back(clause);
			}
		}

		auto& solve = carj::getCarj().data["/incplan/result/solves"_json_pointer].back();
		solve["learned"] =  newLearnedClauses.size();
		solve["transformable"] =  learnedClauses.size();
		VLOG(1) << "learned " << newLearnedClauses.size()
			<< " transformable: " << learnedClauses.size();
		newLearnedClauses.clear();
	}

	bool isApplicable(unsigned clauseIdx, const TimePoint& timePoint){
		DoubleEndedTimePointManager* tpm =
			dynamic_cast<DoubleEndedTimePointManager*>(
				getSolver().timePointManager.get());

		if (timePoint.first == DoubleEndedTimePointManager::FROM_BEGIN) {
			if (tpm->getBeginTop().second >= numNeccessaryTransferes[clauseIdx]) {
				return true;
			} else {
				return false;
			}
		} else {
			if (tpm->getEndTop().second >= numNeccessaryTransferes[clauseIdx]) {
				return true;
			} else {
				return false;
			}
		}
	}

	void addLearnedClause(unsigned clauseIdx, const TimePoint& timePoint) {
		if (isApplicable(clauseIdx, timePoint)) {
			unsigned nt = numNeccessaryTransferes[clauseIdx];
			for (TimedLiteral lit: learnedClauses[clauseIdx]) {
				if (timePoint.first == DoubleEndedTimePointManager::FROM_BEGIN) {
					lit.t.second += timePoint.second - nt;
				} else {
					lit.t.second = timePoint.second - lit.t.second;
				}
				lit.t.first = timePoint.first;
				if (option::useAddLearned.getValue()) {
					getSolver().addAsLearned(lit);
				} else {
					getSolver().add(lit);
				}
			}
			if (option::useAddLearned.getValue()) {
				getSolver().finalizeLearned();
			} else {
				getSolver().finalizeClause();
			}
		}
	}

	void stopLearning() {
		auto& solve = carj::getCarj().data["/incplan/result/solves"_json_pointer].back();
		solve["stopped learning"] = true;
		learning = false;
		getSolver().solver->set_learn(0, nullptr);

		int markerLiteral = static_cast<int>(HelperVariables::MarkerLiteral);
		TimePoint t0 = getSolver().timePointManager->getFirst();
		TimePoint tN = getSolver().timePointManager->getLast();
		getSolver().addHelperLiteral(markerLiteral, t0);
		getSolver().finalizeClause();
		getSolver().addHelperLiteral(markerLiteral, tN);
		getSolver().finalizeClause();
	}

	virtual void preSolveHook() {
		// shift all learned clauses accordingly
		for (size_t i = 0; i < learnedClauses.size(); i++) {
			for (const TimePoint& timePoint: getSolver().newTimepoints) {
				addLearnedClause(i, timePoint);
			}
		}

		if (learning && getSolver().makeSpan >= option::learnMakeSpan.getValue()) {
			stopLearning();
		}

		timeOutClock.resetTimeout();
	}

	virtual void timeoutHook(){
		getSolver().solver->set_terminate([]{return 0;});
		stopLearning();

		int activationLiteral = static_cast<int>(HelperVariables::ActivationLiteral);
		getSolver().assumeHelperLiteral(activationLiteral, getSolver().elementInsertedLast);
	}

	virtual void postStepHook(){
		adeptLearned();
	};

	void learnedCallback(int* learned) {
		newLearnedClauses.push_back(std::vector<TimedLiteral>());
		for (;*learned != 0; learned++) {
			TimedLiteral lit = getSolver().getInfo(*learned);
			newLearnedClauses.back().push_back(lit);
		}
	}

	void setLearnedCallback(){
		using namespace std::placeholders;
		std::function<void(int*)> f =
			std::bind(&UltimateDoubleEndedStrategy::learnedCallback, this, _1);
		getSolver().solver->set_learn(option::maxSizeLearnedClause.getValue(), f);
	}
};

class LooseEndedStrategy: public ISolverStrategy {
public:
	virtual ~LooseEndedStrategy() = default;

	virtual void doInitialize(){
		getSolver().timePointManager =
			std::make_unique<SingleEndedTimePointManager>();

		TimePoint t0 = getSolver().timePointManager->aquireNext();
		getSolver().addInvariantClauses(t0);

		getSolver().elementInsertedLast = t0;
	};

	virtual void doFinalize(){
		TimePoint t0 = getSolver().timePointManager->getFirst();
		TimePoint tN = getSolver().timePointManager->getLast();

		getSolver().assumeInitial(t0);
		getSolver().assumeGoal(tN);
	};
};

class TransfereLearnedStrategy: public LooseEndedStrategy {
private:
	std::vector<std::vector<TimedLiteral>> learnedClauses;
	std::vector<std::vector<TimedLiteral>> newLearnedClauses;
	std::vector<unsigned> timeSpan;
	TimeoutClock timeOutClock;

	bool learning;
public:
	TransfereLearnedStrategy(){
		timeOutClock.setTimeout(option::timeout.getValue());
	}

	virtual ~TransfereLearnedStrategy() = default;

	virtual void doInitialize(){
		learning = true;
		LooseEndedStrategy::doInitialize();

		getSolver().solver->set_terminate(timeOutClock.getTimeoutCallback());
		setLearnedCallback();
	}

	void initEndLiterals(TimedLiteral &at0, TimedLiteral &atN) {
		at0.t = getSolver().timePointManager->getFirst();
		at0.isHelper = false;
		atN.t = getSolver().timePointManager->getLast();
		atN.isHelper = false;
	}

	/* b@N -> -a@0
	 * -b@N or -a@0
	*/
	virtual void learnBlockedStates() {
		unsigned counter = 0;

		TimedLiteral at0, atN;
		initEndLiterals(at0, atN);

		for (int aLit:getSolver().problem.stateVariables) {
			at0.literal = aLit;
			for (int bLit:getSolver().problem.stateVariables) {
				atN.literal = bLit;
				if (testAndLearn({-atN, -at0})) {
					++counter;
				}
			}
		}

		VLOG(1) << "blocked: " << counter;
	}

	/* b@N -> a@0
	 * -b or a
	*/
	virtual void learnForcedStates() {
		unsigned counter = 0;

		TimedLiteral at0, atN;
		initEndLiterals(at0, atN);

		for (int aLit:getSolver().problem.stateVariables) {
			at0.literal = aLit;
			for (int bLit:getSolver().problem.stateVariables) {
				atN.literal = bLit;
				if (testAndLearn({-atN, at0})){
					++counter;
				}
			}
		}

		VLOG(1) << "forced: " << counter;
	}

	/**
	 * Tests whether the clause is universally valid
	 */
	bool testAndLearn(const std::vector<TimedLiteral>& clause) {
		for (TimedLiteral lit: clause) {
			getSolver().assume(-lit);
		}

		auto result = getSolver().solveSAT();
		if (result == ipasir::SolveResult::UNSAT) {
			std::vector<TimedLiteral> failed;
			for (TimedLiteral lit: clause) {
				if (getSolver().failed(-lit)) {
					failed.push_back(lit);
				}
			}
			newLearnedClauses.push_back(failed);

			return true;
		} else {
			return false;
		}
	}

	/*
	 * Test a@tN -> b1@t0 or b2 @t0 or ... for a,bi in state variables
	 */
	virtual void learnNeccessary() {
		unsigned counter = 0;

		TimedLiteral at0, atN;
		initEndLiterals(at0, atN);

		for (int aLit:getSolver().problem.stateVariables) {
			std::vector<TimedLiteral> clause;

			atN.literal = aLit;
			clause.push_back(-atN);
			for (int bLit:getSolver().problem.stateVariables) {
				at0.literal = bLit;
				clause.push_back(at0);
			}
			if (testAndLearn(clause)) {
				++counter;
			}
		}
		VLOG(1) << "necessary: " << counter;
	}

	void adeptLearned() {
		for (std::vector<TimedLiteral>& clause: newLearnedClauses) {
			int tMin = 0;
			int tMax = 0;
			bool init = false;

			for (TimedLiteral& lit:clause) {
				assert(lit.t.first == 0);
				int timepoint = lit.t.second;

				if (!init) {
					init = true;
					tMin = timepoint;
					tMax = timepoint;
				}

				tMin = std::min(timepoint, tMin);
				tMax = std::max(timepoint, tMax);
			}

			/* Learned clauses are universal valid, so we normalize them such
			 * that they start at the first timepoint.
			 */
			for (TimedLiteral& lit: clause) {
				lit.t.first  = 0;
				lit.t.second = lit.t.second - tMin;
			}

			TimePoint last = getSolver().timePointManager->getLast();
			assert(last.first == 0);
			int tN = last.second;
			int shift = tN - (tMax - tMin);

			learnedClauses.push_back(clause);
			timeSpan.push_back(tMax - tMin);
			for (int i = 0; i <= shift; i++) {
				TimePoint t;
				t.first = 0;
				t.second = i;
				addLearnedClause(clause, t);
			}
		}

		newLearnedClauses.clear();
	}

	void addLearnedClause(const std::vector<TimedLiteral> &clause,
			const TimePoint& timePoint) {
		int shift = timePoint.second;
		assert(timePoint.first == 0);
		for (TimedLiteral lit: clause) {
			assert(lit.t.first == 0);
			lit.t.second = lit.t.second + shift;
			if (option::useAddLearned.getValue()) {
					getSolver().addAsLearned(lit);
				} else {
					getSolver().add(lit);
				}
			}
			if (option::useAddLearned.getValue()) {
				getSolver().finalizeLearned();
			} else {
				getSolver().finalizeClause();
			}
	}

	void stopLearning() {
		auto& solve = carj::getCarj().data["/incplan/result/solves"_json_pointer].back();
		solve["stopped learning"] = true;

		TimePoint t0 = getSolver().timePointManager->getFirst();
		getSolver().addInitialClauses(t0);
		getSolver().solver->set_learn(0, nullptr);
		learning = false;
	}

	virtual void preSolveHook() {
		// shift all learned clauses one up
		for (size_t i = 0; i < learnedClauses.size(); i++) {
			for (TimePoint timePoint: getSolver().newTimepoints) {
				timePoint.second -= timeSpan[i];
				addLearnedClause(learnedClauses[i], timePoint);
			}
		}

		if (learning && getSolver().makeSpan >= option::learnMakeSpan.getValue()) {
			stopLearning();
		}

		if (learning && getSolver().makeSpan <= option::exhaustMakeSpan.getValue()) {
			learnNeccessary();
		// // 	// VLOG(1) << "learned pre blocked/ forced " << learnedClauses.size();
			learnBlockedStates();
			learnForcedStates();
			adeptLearned();
		}

		timeOutClock.resetTimeout();
	}

	virtual void timeoutHook(){
		getSolver().solver->set_terminate([]{return 0;});
		stopLearning();

		doFinalize();
	}

	virtual void postStepHook(){
		adeptLearned();
		auto& solve = carj::getCarj().data["/incplan/result/solves"_json_pointer].back();
		solve["learned"] =  learnedClauses.size();
		VLOG(1) << "learned " << learnedClauses.size();
	};

	void learnedCallback(int* learned) {
		newLearnedClauses.push_back(std::vector<TimedLiteral>());
		for (;*learned != 0; learned++) {
			TimedLiteral lit = getSolver().getInfo(*learned);
			newLearnedClauses.back().push_back(lit);
		}
	}

	void setLearnedCallback(){
		using namespace std::placeholders;
		std::function<void(int*)> f =
			std::bind(&TransfereLearnedStrategy::learnedCallback, this, _1);
		getSolver().solver->set_learn(option::maxSizeLearnedClause.getValue(), f);
	}
};



namespace option {
namespace setup {
	carj::CarjArg<TCLAP::SwitchArg, bool> printFrozenVariables("", "frozen", "Prints all variables that need to be frozen when preprocessing the formula.", cmd, /*default*/ false);

	carj::CarjArg<TCLAP::SwitchArg, bool> loose("", "loose", "Only assume init and goal.", cmd, /*default*/ false);
	carj::CarjArg<TCLAP::SwitchArg, bool> transformLearned("", "transformLearned", "Transform learned clauses from privious solves to new time step.", cmd, /*default*/ false);

	carj::CarjArg<TCLAP::SwitchArg, bool> solveBeforeGoalClauses("i", "intermediateSolveStep", "Add an additional solve step before adding the goal or linking clauses.", cmd, /*default*/ false);
	carj::CarjArg<TCLAP::SwitchArg, bool> cleanLitearl("c", "cleanLitearl", "Add a literal to remove linking or goal clauses.", cmd, /*default*/ false);

	carj::TCarjArg<TCLAP::ValueArg, unsigned>  linearStepSize("l", "linearStepSize", "Linear step size.", /*neccessary*/ false, 1, "natural number", cmd);
	carj::TCarjArg<TCLAP::ValueArg, float> exponentialStepBasis("e", "exponentialStepBasis", "Basis of exponential step size. Combinable with options -l and -o (varibale names are equal to parameter): step size = l*n + floor(e ^ (n + o))", /*neccessary*/ false, 0, "natural number", cmd);
	carj::TCarjArg<TCLAP::ValueArg, float> exponentialStepOffset("o", "exponentialStepOffset", "Basis of exponential step size.", /*neccessary*/ false, 0, "natural number", cmd);

	carj::CarjArg<TCLAP::SwitchArg, bool> outputSolverLike("", "outputSolverLike", "Output result like a normal solver is used. The literals for each time point t are in range t * [literalsPerTime] < lit <= (t + 1) * [literalsPerTime]", cmd, /*default*/ false);

	carj::CarjArg<TCLAP::SwitchArg, bool> singleEnded("s", "singleEnded", "Use naive incremental encoding.", cmd, /*default*/ false);
	carj::TCarjArg<TCLAP::ValueArg, double> ratio("r", "ratio", "Ratio between states from start to state from end.", /*neccessary*/ false, /*default*/ 0.5, "number between 0 and 1", cmd);
	carj::CarjArg<TCLAP::SwitchArg, bool> nonIncrementalSolving("n", "nonIncrementalSolving", "Do not use incremental solving.", cmd, /*default*/ false);

	carj::CarjArg<TCLAP::SwitchArg, bool> reEncode("", "reEncode", "Reencode problem with double ended strategy before solving.", cmd, /*default*/ false);
	carj::CarjArg<TCLAP::SwitchArg, bool> usePDR("", "usePDR", "Use property directed reachability.", cmd, /*default*/ false);
	carj::TCarjArg<TCLAP::UnlabeledValueArg,std::string>  inputFile("inputFile", "File containing the problem. Omit or use - for stdin.", /*neccessary*/ false, "-", "inputFile", cmd);
	carj::MCarjArg<TCLAP::MultiArg, std::string> pathSearchPrefix("", "pathSearchPrefix", "If passed files are not found their path will be prefixed with values of this parameter.", /*neccessary*/ false, "path", cmd);
}}

void parseOptions(int argc, const char **argv) {
	try {
		carj::init(argc, argv, cmd, "/incplan/parameters");
	} catch (TCLAP::ArgException &e) {
		LOG(FATAL) << e.error() << " for arg " << e.argId() << std::endl;
	}
}

std::function<int(int)> getStepFunction(){
	using namespace option::setup;
	int l = linearStepSize.getValue();
	float e = exponentialStepBasis.getValue();
	float o = exponentialStepOffset.getValue();
	if (e != 0) {
		return [l,e,o](int n){return l * n + std::floor(pow(e,(n + o)));};
	} else {
		return [l,e,o](int n){return l * n;};
	}
}

int incplan_main(int argc, const char **argv) {
	parseOptions(argc, argv);

	//LOG(INFO) << "Using the incremental SAT solver " << ipasir_signature();

	std::istream* in;
	std::ifstream is;
	std::string inputFileName = option::setup::inputFile.getValue();
	if (inputFileName == "-") {
		in = &std::cin;
		LOG(INFO) << "Using standard input.";
	} else {

		std::vector<std::string> prefixes = option::setup::pathSearchPrefix.getValue();
		prefixes.insert(prefixes.begin(), "");

		for (std::string prefix: prefixes) {
			is.open(prefix + inputFileName);
			if (!is.fail()) {
				break;
			}
		}

		if (is.fail()){
			LOG(FATAL) << "Input Error can't open file: " << inputFileName;
		}
		in = &is;
	}

	bool solved = false;

	DimspecProblem inProblem(*in);

	if (option::setup::printFrozenVariables.getValue()) {
		for (int var:inProblem.stateVariables) {
			std::cout << var << std::endl;
		}
		for (int var:inProblem.stateVariables) {
			std::cout << var + inProblem.numberLiteralsPerTime << std::endl;
		}
		return 0;
	}

	DimspecProblem* problem = &inProblem;
	std::unique_ptr<DoubleEndedProblem> reEncodedProblem;
	if (option::setup::reEncode.getValue() == true) {
		reEncodedProblem = std::make_unique<DoubleEndedProblem>(&inProblem);
		problem = reEncodedProblem.get();
	}

	if (option::setup::usePDR.getValue()) {
		PDRSolver solver(
			*problem,
			std::move(solverWithRandomizedOptions())
		);
		solved = solver.solve();
	} else {
		std::unique_ptr<ISolverStrategy> strategy = nullptr;
		if (option::setup::nonIncrementalSolving.getValue()) {
			strategy = std::make_unique<NonIncrementalStrategy>();
		} else if (option::setup::singleEnded.getValue()) {
			if (option::setup::transformLearned.getValue()) {
				strategy = std::make_unique<TransfereLearnedStrategy>();
			} else if (option::setup::loose.getValue()){
				strategy = std::make_unique<LooseEndedStrategy>();
			} else {
				strategy = std::make_unique<SingleEndedStrategy>();
			}
		} else {
			if (option::setup::transformLearned.getValue()) {
				strategy = std::make_unique<UltimateDoubleEndedStrategy>(
					option::setup::ratio.getValue());
			} else if (option::setup::loose.getValue()){
				strategy = std::make_unique<LooseDoubleEndedStrategy>(
					option::setup::ratio.getValue());
			} else {
				strategy = std::make_unique<DoubleEndedStrategy>(
					option::setup::ratio.getValue());
			}
		}

		if (option::setup::solveBeforeGoalClauses.getValue()) {
			strategy = std::make_unique<PreFinalizationSolveStrategy>(std::move(strategy));
		}
		if (option::setup::cleanLitearl.getValue()) {
			strategy = std::make_unique<CleanAktivationLiteralStrategy>(std::move(strategy));
		}

		Solver solver(
			*problem,
			std::move(strategy),
			getStepFunction());
		solved = solver.solve();

		if (solved && option::allSolutions.getValue() > 0) {
			bool hasNewSolution = true;
			int solutionNum = 0;
			while (hasNewSolution) {
				std::stringstream ss;
				ss << "variant" << solutionNum << ".sol";
				std::ofstream out(ss.str());
				inProblem.printSolution(option::setup::outputSolverLike.getValue(), out);

				solutionNum++;
				hasNewSolution = solver.nextSolution();
			}
		}
	}

	if (!solved) {
		LOG(WARNING) << "Did not get a solution within the maximal make span.";
		return 1;
	} else {
		LOG(INFO) << "Final Makespan: " << inProblem.solution.size() - 1;
		carj::getCarj().data["/incplan/result/finalMakeSpan"_json_pointer] = inProblem.solution.size() - 1;
		inProblem.printSolution(option::setup::outputSolverLike.getValue());
	}

	return 0;
}
