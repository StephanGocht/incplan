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

#include "tclap/CmdLine.h"

#include "TimeSlotMapping.h"
#include "TimePointBasedSolver.h"
#include "carj/carj.h"
#include "carj/logging.h"
#include "carj/ScopedTimer.h"

#include "DimspecProblem.h"

TCLAP::CmdLine cmd("This tool is does sat planing using an incremental sat solver.", ' ', "0.1");
namespace option{
	carj::CarjArg<TCLAP::SwitchArg, bool> exhaustive("", "exhaustiveSearch", "Solve problem for subsets of assumed literals.", cmd, /*default*/ false);
	carj::CarjArg<TCLAP::SwitchArg, bool> loose("", "loose", "Only assume init and goal.", cmd, /*default*/ false);
	carj::CarjArg<TCLAP::SwitchArg, bool> transformLearned("", "transformLearned", "Transform learned clauses from privious solves to new time step.", cmd, /*default*/ false);
	carj::TCarjArg<TCLAP::ValueArg,int> maxSizeLearnedClause("", "maxSizeLearnedClause", "Maximum number of literals in a learned clause that will be transformed to future time steps.", /* necessary */ false, /*default*/ 2, /* type description */ "positive number", cmd);
	carj::CarjArg<TCLAP::SwitchArg, bool> outputSolverLike("", "outputSolverLike", "Output result like a normal solver is used. The literals for each time point t are in range t * [literalsPerTime] < lit <= (t + 1) * [literalsPerTime]", cmd, /*default*/ false);
}

struct Options {
	bool error;
	std::string inputFile;
	bool unitInGoal2Assume;
	bool solveBeforeGoalClauses;
	bool nonIncrementalSolving;
	bool singleEnded;
	bool cleanLitearl;
	bool icaps2017Version;
	double ratio;
	std::function<int(int)> stepToMakespan;
};

Options options;

enum class HelperVariables { ZeroVariableIsNotAllowed_DoNotRemoveThis,
	ActivationLiteral };

class Solver;

class ISolverStrategy {
public:
	/**
	 * Initialize the first timepoints and return the timepoint inserted last.
	 */
	virtual void doInitialize() = 0;

	/**
	 * Finalize the formula after one or more time points have been added.
	 * This will be executed immedeatly before the call to solve of the
	 * SAT solver, so it is the place to make neccessary assumptions.
	 */
	virtual void doFinalize() = 0;

	virtual void preSolveHook(){};
	virtual void preStepHook(){};
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

	virtual void setSolver(Solver* solver) {
		ISolverStrategy::setSolver(solver);
		strategy->setSolver(solver);
	};

private:
	std::unique_ptr<ISolverStrategy> strategy;
};

class Solver : public TimePointBasedSolver {
public:
	std::unique_ptr<ISolverStrategy> strategy;
	TimePoint elementInsertedLast;

	public:
		Solver(const DimspecProblem& _problem):
			TimePointBasedSolver(
				problem.numberLiteralsPerTime,
				1,
				// std::make_unique<ipasir::Solver>(),
				std::make_unique<ipasir::RandomizedSolver>(0, std::make_unique<ipasir::Solver>()),
				options.icaps2017Version?
					TimePointBasedSolver::HelperVariablePosition::AllBefore:
					TimePointBasedSolver::HelperVariablePosition::SingleAfter),
			problem(_problem){

			strategy->setSolver(this);
		}

		/**
		 * Solve the problem. Return true if a solution was found.
		 */
		bool solve(){
			nlohmann::json solves;

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
				solves.push_back({
					{"makespan", makeSpan},
					{"time", -1}
				});
				{
					carj::ScopedTimer timer((*solves.rbegin())["time"]);
					TIMED_SCOPE(blkScope, "solve");
					result = solveSAT();
				}

				strategy->postStepHook();
			}

			LOG(INFO) << "Final Makespan: " << this->makeSpan;
			this->finalMakeSpan = this->makeSpan;

			carj::getCarj().data["/incplan/result/solves"_json_pointer] =
				solves;
			carj::getCarj().data["/incplan/result/finalMakeSpan"_json_pointer] = makeSpan;
			this->solveResult = result;

			return result == ipasir::SolveResult::SAT;
		}

		/**
		 * @arg outputSolverLike
		 *     if true print one line where variables from different time points
		 *         are named differently
		 *     if false print one line per time step
		 */
		void printSolution(bool outputSolverLike) {
			if (this->solveResult == ipasir::SolveResult::SAT) {
				std::cout << "solution " << this->problem.numberLiteralsPerTime << " " << this->finalMakeSpan + 1 << std::endl;
				TimePoint t = timePointManager->getFirst();
				int time = 0;

				do {
					for (unsigned j = 1; j <= this->problem.numberLiteralsPerTime; j++) {
						int val = valueProblemLiteral(j,t);
						if (outputSolverLike) {
							int offset = time * problem.numberLiteralsPerTime;
							if (val < 0) {
								offset = -offset;
							}
							val += offset;
						}
						std::cout << val << " ";
					}
					if (!outputSolverLike) {
						std::cout << std::endl;
					}
					if (t == timePointManager->getLast()) {
						break;
					}

					t = timePointManager->getSuccessor(t);
					time++;
				} while (true);

				if (outputSolverLike) {
					std::cout << std::endl;
				}
			} else {
				std::cout << "no solution" << std::endl;
			}
		}

		~Solver(){
		}

	public:
		const DimspecProblem& problem;

		int finalMakeSpan;
		int makeSpan;
		ipasir::SolveResult solveResult;
		std::unique_ptr<TimePointManager> timePointManager;

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

		std::unique_ptr<TimePoint> addNewTimePoints(unsigned step) {
			std::unique_ptr<TimePoint> tNew = nullptr;
			int targetMakeSpan = options.stepToMakespan(step);

			for (; this->makeSpan < targetMakeSpan; this->makeSpan++) {
				tNew = std::make_unique<TimePoint>(timePointManager->aquireNext());
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
			if (!options.unitInGoal2Assume) {
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

class NonIncrementalStrategy: public ISolverStrategyDecorator {
public:
	virtual void preStepHook(){
		getSolver().reset();
		doInitialize();
		ISolverStrategyDecorator::preStepHook();
	}
};

class PreFinalizationSolveStrategy: public ISolverStrategyDecorator {
public:
	virtual void preSolveHook(){
		ISolverStrategyDecorator::preSolveHook();
		getSolver().solveSAT();
	}
};

class CleanAktivationLiteralStrategy: public ISolverStrategyDecorator {
public:
	virtual void postStepHook(){
		ISolverStrategyDecorator::postStepHook();
		int activationLiteral = static_cast<int>(HelperVariables::ActivationLiteral);
		getSolver().addHelperLiteral(-activationLiteral, getSolver().elementInsertedLast);
		getSolver().finalizeClause();
	}
};


class SingleEndedStrategy: public ISolverStrategy {
public:
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


class DoubleEndedStrategy: public ISolverStrategy {
public:
	virtual void doInitialize(){
		getSolver().timePointManager =
			std::make_unique<DoubleEndedTimePointManager>(
				options.ratio,
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
	};

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

class LooseEndedStrategy: public ISolverStrategy {
public:
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
public:
	virtual void doInitialize(){
		LooseEndedStrategy::doInitialize();
		setLearnedCallback();
	}

	virtual void postStepHook() {
		VLOG(1) << "learned " << learnedClauses.size();
		// shift all learned clauses one up
		for (size_t i = 0; i < learnedClauses.size(); i++) {
			std::vector<int>& clause = learnedClauses[i];
			learnedClausesShift[i] += 1;
			for (int lit: clause) {
				int timedLiteral;
				TimePoint t;
				bool isHelper;
				getSolver().getInfo(lit, timedLiteral, t, isHelper);

				for (int k = 0; k < learnedClausesShift[i]; k++) {
					t = getSolver().timePointManager->getSuccessor(t);
				}
				if (isHelper) {
					getSolver().addHelperLiteral(timedLiteral, t);
				} else {
					getSolver().addProblemLiteral(timedLiteral, t);
				}
			}
			getSolver().finalizeClause();
		}
	}

	void rememberLearned(int* learned) {
		learnedClauses.push_back(std::vector<int>());
		for (;*learned != 0; learned++) {
			learnedClauses.back().push_back(*learned);
		}
		learnedClausesShift.push_back(0);
	}

	void setLearnedCallback(){
		using namespace std::placeholders;
		std::function<void(int*)> f =
			std::bind(&TransfereLearnedStrategy::rememberLearned, this, _1);
		getSolver().solver->set_learn(option::maxSizeLearnedClause.getValue(), f);
	}

private:
	std::vector<std::vector<int>> learnedClauses;
	std::vector<int> learnedClausesShift;
};


//bool defaultIsTrue = true;
bool defaultIsFalse = false;
bool neccessaryArgument = true;



carj::MCarjArg<TCLAP::MultiArg, std::string> pathSearchPrefix("", "pathSearchPrefix", "If passed files are not found their path will be prefixed with values of this parameter.", !neccessaryArgument, "path", cmd);
void parseOptions(int argc, const char **argv) {
	try {
		carj::TCarjArg<TCLAP::UnlabeledValueArg,std::string>  inputFile("inputFile", "File containing the problem. Omit or use - for stdin.", !neccessaryArgument, "-", "inputFile", cmd);
		carj::TCarjArg<TCLAP::ValueArg, double>  ratio("r", "ratio", "Ratio between states from start to state from end.", !neccessaryArgument, 0.5, "number between 0 and 1", cmd);
		carj::TCarjArg<TCLAP::ValueArg, unsigned>  linearStepSize("l", "linearStepSize", "Linear step size.", !neccessaryArgument, 1, "natural number", cmd);
		carj::TCarjArg<TCLAP::ValueArg, float> exponentialStepBasis("e", "exponentialStepBasis", "Basis of exponential step size. Combinable with options -l and -o (varibale names are equal to parameter): step size = l*n + floor(e ^ (n + o))", !neccessaryArgument, 0, "natural number", cmd);
		carj::TCarjArg<TCLAP::ValueArg, float> exponentialStepOffset("o", "exponentialStepOffset", "Basis of exponential step size.", !neccessaryArgument, 0, "natural number", cmd);
		carj::CarjArg<TCLAP::SwitchArg, bool> unitInGoal2Assume("u", "unitInGoal2Assume", "Add units in goal clauses using assume instead of add. (singleEnded only)", cmd, defaultIsFalse);
		carj::CarjArg<TCLAP::SwitchArg, bool> solveBeforeGoalClauses("i", "intermediateSolveStep", "Add an additional solve step before adding the goal or linking clauses.", cmd, defaultIsFalse);
		carj::CarjArg<TCLAP::SwitchArg, bool> nonIncrementalSolving("n", "nonIncrementalSolving", "Do not use incremental solving.", cmd, defaultIsFalse);
		carj::CarjArg<TCLAP::SwitchArg, bool> cleanLitearl("c", "cleanLitearl", "Add a literal to remove linking or goal clauses.", cmd, defaultIsFalse);

		carj::CarjArg<TCLAP::SwitchArg, bool> singleEnded("s", "singleEnded", "Use naive incremental encoding.", cmd, defaultIsFalse);
		//TCLAP::SwitchArg outputLinePerStep("", "outputLinePerStep", "Output each time point in a new line. Each time point will use the same literals.", defaultIsFalse);

		carj::CarjArg<TCLAP::SwitchArg, bool> icaps2017Version("", "icaps2017", "Use this option to use encoding as used in the icaps paper.", cmd, defaultIsFalse);

		carj::init(argc, argv, cmd, "/incplan/parameters");

		options.error = false;
		options.inputFile = inputFile.getValue();
		options.unitInGoal2Assume = unitInGoal2Assume.getValue();
		options.solveBeforeGoalClauses = solveBeforeGoalClauses.getValue();
		options.nonIncrementalSolving = nonIncrementalSolving.getValue();
		options.ratio = ratio.getValue();
		options.singleEnded = singleEnded.getValue();
		options.cleanLitearl = cleanLitearl.getValue();
		options.icaps2017Version = icaps2017Version.getValue();
		{
			int l = linearStepSize.getValue();
			float e = exponentialStepBasis.getValue();
			float o = exponentialStepOffset.getValue();
			if (e != 0) {
				options.stepToMakespan =
					[l,e,o](int n){return l * n + std::floor(pow(e,(n + o)));};
			} else {
				options.stepToMakespan =
					[l,e,o](int n){return l * n;};
			}

		}


		if (options.nonIncrementalSolving) {
			options.singleEnded = true;
		}

	} catch (TCLAP::ArgException &e) {
		options.error = true;
		std::cerr << "error: " << e.error() << " for arg " << e.argId() << std::endl;
	}
}


int incplan_main(int argc, const char **argv) {
	parseOptions(argc, argv);

	//LOG(INFO) << "Using the incremental SAT solver " << ipasir_signature();

	std::istream* in;
	std::ifstream is;
	if (options.inputFile == "-") {
		in = &std::cin;
		LOG(INFO) << "Using standard input.";
	} else {

		std::vector<std::string> prefixes = pathSearchPrefix.getValue();
		prefixes.insert(prefixes.begin(), "");

		for (std::string prefix: prefixes) {
			is.open(prefix + options.inputFile);
			if (!is.fail()) {
				break;
			}
		}

		if (is.fail()){
			LOG(FATAL) << "Input Error can't open file: " << options.inputFile;
		}
		in = &is;
	}

	bool solved;
	{
		DimspecProblem problem(*in);
		Solver solver(problem);
		solved = solver.solve();
		solver.printSolution(option::outputSolverLike.getValue());
	}

	if (!solved) {
		LOG(WARNING) << "Did not get a solution within the maximal make span.";
	}

	return 0;
}
