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
#include "logging.h"
INITIALIZE_EASYLOGGINGPP

#include "TimeSlotMapping.h"
#include "TimePointBasedSolver.h"

#define UNUSED(x) (void)(x)
#define MAX_STEPS 5000

const int SAT = 10;
const int UNSAT = 20;
const int TIMEOUT = 0;

struct Options {
	bool error;
	std::string inputFile;
	bool unitInGoal2Assume;
	bool solveBeforeGoalClauses;
	bool nonIncrementalSolving;
	bool normalOutput;
	bool singleEnded;
	bool cleanLitearl;
	double ratio;
	std::function<int(int)> stepToMakespan;
};

Options options;

class Problem {
public:
	Problem(std::istream& in){
		this->numberLiteralsPerTime = 0;
		parse(in);
		//inferAdditionalInformation();
	}

	std::vector<int> initial, invariant, goal , transfer;
	unsigned numberLiteralsPerTime;
	std::vector<int> actionVariables;
	std::vector<int> stateVariables;
	std::map<int, std::vector<int>> support;

private:
	void inferAdditionalInformation() {
		VLOG(2) << "Number Of Literals per Time: " << this->numberLiteralsPerTime;

		// state variables should all be set in the initial state
		std::set<int> stateVariables;
		for (int lit: this->initial) {
			stateVariables.insert(std::abs(lit));
		}
		stateVariables.erase(0);

		// {
		// 	std::stringstream ss;
		// 	ss << "State Variables: ";
		// 	for (int var: stateVariables) {
		// 		ss << var << ", ";
		// 	}
		// 	VLOG(2) << ss.str();
		// }


		// guess action variables from clauses containing states
		std::set<int> actionVariablesHelper;
		size_t clauseStart = 0;
		bool clauseHasStateVar = false;
		for (size_t i = 0; i < this->transfer.size(); i++) {
			unsigned var = std::abs(this->transfer[i]);
			var = var > this->numberLiteralsPerTime ? var - this->numberLiteralsPerTime: var;
			if (this->transfer[i] != 0) {
				if (stateVariables.find(var) != stateVariables.end()) {
					clauseHasStateVar = true;
				}
			} else {
				if (clauseHasStateVar) {
					for (size_t j = clauseStart; j < i; j++) {
						unsigned var = std::abs(this->transfer[j]);
						var = var > this->numberLiteralsPerTime ? var - this->numberLiteralsPerTime: var;
						actionVariablesHelper.insert(var);
					}
				}

				clauseStart = i + 1;
				clauseHasStateVar = false;
			}
		}

		std::set<int> actionVariables;
		std::set_difference(actionVariablesHelper.begin(), actionVariablesHelper.end(),
							stateVariables.begin(), stateVariables.end(),
							std::inserter(actionVariables, actionVariables.end()));

		std::vector<int> currentClauseActions;
		std::vector<int> currentClauseFutureState;
		for (size_t i = 0; i < this->transfer.size(); i++) {
			unsigned var = std::abs(this->transfer[i]);
			if (var == 0) {
				for (int stateVar: currentClauseFutureState) {
					auto res = support.insert(std::make_pair(stateVar, std::vector<int>()));
					std::copy(currentClauseActions.begin(), currentClauseActions.end(), std::back_inserter(res.first->second));
				}

			} else {
				bool isNextTime = false;
				if (var > this->numberLiteralsPerTime) {
					isNextTime = true;
					var -= this->numberLiteralsPerTime;
				}

				if (stateVariables.find(var) != stateVariables.end() && isNextTime) {
					currentClauseFutureState.push_back(var);
				}

				if (actionVariables.find(var) != actionVariables.end()) {
					assert(!isNextTime);
					currentClauseActions.push_back(var);
				}
			}
		}

		std::copy(actionVariables.begin(), actionVariables.end(), std::back_inserter(this->actionVariables));
		std::copy(stateVariables.begin(), stateVariables.end(), std::back_inserter(this->stateVariables));

		// {
		// 	std::stringstream ss;
		// 	ss << "State Variables: ";
		// 	for (int var: actionVariables) {
		// 		ss << var << ", ";
		// 	}
		// 	VLOG(2) << ss.str();
		// }

	}

	void skipComments(std::istream& in){
		char nextChar;
		in >> nextChar;
		while ( nextChar == 'c' ) {
			in.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
			in >> nextChar;
		}
		if (in.eof()) {
			std::cerr << "Input Error: Expected [iugt] cnf [0-9*] [0-9*] but got nothing. (File empty or only comments) " << std::endl;
			std::exit(1);
		}
		// Next character wasn't c, so revert the last get:
		in.unget();
		assert(in.good() && "Internal Error: Failed to put back character to stream. Change previous code.");
	}

	int parseCnfHeader(char expectedType, std::istream& in) {
		char type;
		unsigned literals;
		int numberClauses;
		std::string cnfString;
		in >> type >> cnfString >> literals >> numberClauses;
		if (!in.good() || cnfString != "cnf") {
			std::string line;
			in.clear();
			in >> line;
			LOG(FATAL) << "Input Error: Expected [iugt] cnf [0-9*] [0-9*] but got: " << line;
		}

		if (type != expectedType) {
			LOG(FATAL) << "Input Error: Expected type " << expectedType << " but got: " << type;
		}

		switch(type) {
			case 'i':
			case 'u':
			case 'g':
			case 't':
			break;
			default:
			LOG(FATAL) << "Input Error: Expected type i,u,g or t but got " << type;
		}

		if (numberLiteralsPerTime == 0) {
			numberLiteralsPerTime = literals;
		} else if (literals != numberLiteralsPerTime && (type != 't' || literals != 2 * numberLiteralsPerTime)) {
			LOG(FATAL) << "Input Error: Wrong Number of Literals!" << literals << ":" << numberLiteralsPerTime << type;
		}

		return numberClauses;
	}

	void parseCnf(std::vector<int>& cnf, std::istream& in) {
		int literal;
		while (in >> literal) {
			cnf.push_back(literal);
		}
		// The above will abort as soon as no further number is found.
		// Therefore, we need to reset the error state of the input stream:
		in.clear();
	}

	void parse(std::istream& in) {
		if (in.eof()) {
			LOG(FATAL) << "Input Error: Got empty File.";
		}
		skipComments(in);
		parseCnfHeader('i', in);
		parseCnf(initial, in);
		parseCnfHeader('u', in);
		parseCnf(invariant, in);
		parseCnfHeader('g', in);
		parseCnf(goal, in);
		parseCnfHeader('t', in);
		parseCnf(transfer, in);
	}
};

struct AddInfo {
	unsigned transitionSource;
	unsigned transitionGoal;
	unsigned addedSlot;
};


/**
 *  The prupose of this class is handle and organize time slots.
 */
class TimeSlotMapping {
public:
	TimeSlotMapping(double ratio, std::function<int(int)> makeSpanStep):
			_makeSpanStep(makeSpanStep) {
		this->ratio = ratio;
		this->_step = 0;
		startStack.push_back(0);
		goalStack.push_back(1);
	}

	unsigned getSlotForTime(unsigned time) {
		if (time < startStack.size()) {
			return startStack[time];
		} else {
			time -= startStack.size();
			// skip last time slot as they are equal in both slots
			time += 1;
			return goalStack[goalStack.size() - 1 - time];
		}
	}

	bool hasToAdd(){
		return getMakeSpan() > (getNumberOfTimeSlots() - 2);
	}

	unsigned getNumberOfTimeSlots() {
		return startStack.size() + goalStack.size();
	}

	unsigned getNextFreeSlot() {
		return getNumberOfTimeSlots();
	}

	AddInfo add() {
		AddInfo result;
		double currentRatio = startStack.size() / (double) getNumberOfTimeSlots();
		if (currentRatio <= ratio) {
			result.addedSlot = getNextFreeSlot();
			result.transitionSource = startTop();
			result.transitionGoal = result.addedSlot;

			startStack.push_back(result.addedSlot);
		} else {
			result.addedSlot = getNextFreeSlot();
			result.transitionSource = result.addedSlot;
			result.transitionGoal = goalTop();

			goalStack.push_back(result.addedSlot);
		}

		return result;
	};

	unsigned startTop(){
		return startStack.back();
	}

	unsigned goalTop(){
		return goalStack.back();
	}

	unsigned startSlot(){
		return startStack[0];
	}

	unsigned goalSlot(){
		return goalStack[0];
	}

	void incrementMakeSpan() {
		_step += 1;
	}

	unsigned getMakeSpan(){
		return _makeSpanStep(_step);
	}

private:
	std::function<int(int)> _makeSpanStep;
	unsigned _step;
	double ratio;
	std::vector<int> startStack;
	std::vector<int> goalStack;
};

extern "C" {
	int state;
	int terminate_callback(void* state){
		UNUSED(state);
		return 0;
	}
}

enum class HelperVariables { ZeroVariableIsNotAllowed_DoNotRemoveThis,
	ActivationLiteral };

class Solver : public TimePointBasedSolver {
	public:
		Solver(const Problem* problem):
			TimePointBasedSolver(problem->numberLiteralsPerTime,1){
			initIpasir();
			this->problem = problem;
		}

		/**
		 * returns a hint on the literal to be set or zero if no hint is available
		 */
		int selectLiteral() {
			static std::random_device rd;
			static std::mt19937 mt(rd());
			static std::stack<int> todo;

			static bool init = true;
			if (init) {
				init = false;
				for (int goalLit:this->problem->goal) {
					assert(goalLit > 0);
					assert(ipasir_val(this->ipasir, goalLit) > 0);
					todo.push(goalLit);
				}
			}

			std::uniform_real_distribution<double> varDist(0, this->problem->actionVariables.size() - 1);
			std::uniform_real_distribution<double> timeDist(0, this->mapping->getMakeSpan());
			size_t index = varDist(mt);
			uint time = timeDist(mt);
			int var = this->problem->actionVariables[index] + time * this->problem->numberLiteralsPerTime;
			if (ipasir_val(this->ipasir, var) == 0) {
				VLOG(1) << "Chose Variable " << var;
				return var;
			}

			return 0;
		}

		/**
		 * Solve the problem. Return true if a solution was found.
		 */
		bool solve(){
			bool result;
			if (options.singleEnded) {
				result = solveOneEnded();
			} else {
				result = solveDoubleEnded();
			}
			assert(slv() == result);
			assert(this->makeSpan == this->finalMakeSpan);
			LOG(INFO) << "Final Makespan: " << finalMakeSpan;
			return result;
		}

		void printSolution() {
			std::vector<int> result;

			if (this->result == SAT) {
				std::cout << "solution " << this->problem->numberLiteralsPerTime << " " << this->finalMakeSpan + 1 << std::endl;
				for (int time = 0; time <= this->finalMakeSpan; time++) {
					int slot = (options.singleEnded)?time:mapping->getSlotForTime(time);
					for (unsigned j = 1; j <= this->problem->numberLiteralsPerTime; j++) {
						int val = ipasir_val(ipasir, map(slot,j));
						val = unmap(slot, val);

						if (val == 0) {
							val = j;
						}

						if (options.normalOutput) {
							int offset = time * problem->numberLiteralsPerTime;
							if (val < 0) {
								offset = -offset;
							}
							val += offset;
						}
						result.push_back(val);

						std::cout << val << " ";
					}
					if (!options.normalOutput) {
						std::cout << std::endl;
					}
				}
				if (options.normalOutput) {
					std::cout << std::endl;
				}
			} else {
				std::cout << "no solution" << std::endl;
			}

			std::vector<int> resultNew;
			if (this->result == SAT) {
				std::cout << "solution " << this->problem->numberLiteralsPerTime << " " << this->finalMakeSpan + 1 << std::endl;
				TimePoint t = timePointManager->getFirst();
				int time = 0;
				do {
					for (unsigned j = 1; j <= this->problem->numberLiteralsPerTime; j++) {
						int val = valueProblemLiteral(j,t);
						if (options.normalOutput) {
							int offset = time * problem->numberLiteralsPerTime;
							if (val < 0) {
								offset = -offset;
							}
							val += offset;
						}
						resultNew.push_back(val);
					}

					t = timePointManager->getSuccessor(t);
					time++;
				} while (t != timePointManager->getLast());
			}

			assert(std::equal(result.begin(), result.end(), resultNew.begin()));
		}

		~Solver(){
			ipasir_release(ipasir);
		}

	private:
		const Problem* problem;
		void* ipasir;
		std::unique_ptr<TimeSlotMapping> mapping;

		int finalMakeSpan;
		int makeSpan;
		int result;
		std::unique_ptr<TimePointManager> timePointManager;

		void initIpasir() {
			this->ipasir = ipasir_init();
			ipasir_set_terminate(this->ipasir, this, &terminate_callback);
		}

		TimePoint initialize() {
			if (options.singleEnded) {
				timePointManager = std::make_unique<SingleEndedTimePointManager>();
			} else {
				timePointManager = std::make_unique<DoubleEndedTimePointManager>();
			}

			TimePoint t0 = timePointManager->aquireNext();
			addInitialClauses(t0);
			addInvariantClauses(t0);

			if (!options.singleEnded) {
				TimePoint tN = timePointManager->aquireNext();
				addGoalClauses(tN);
				addInvariantClauses(tN);

				return tN;
			}

			return t0;
		}

		void finalize(const TimePoint elementInsertedLast) {
			if (options.singleEnded) {
				addGoalClauses(elementInsertedLast, true);
			} else {
				TimePoint linkSource, linkDestination;
				if (timePointManager->isOnForwardStack(elementInsertedLast)){
					linkSource = elementInsertedLast;
					linkDestination = timePointManager->getSuccessor(elementInsertedLast);
				} else {
					linkSource = timePointManager->getPredecessor(elementInsertedLast);
					linkDestination = elementInsertedLast;
				}

				addLink(linkSource, linkDestination, elementInsertedLast);
			}
			int activationLiteral = static_cast<int>(HelperVariables::ActivationLiteral);
			assumeHelperLiteral(activationLiteral, elementInsertedLast);
		}

		bool slv(){
			LOG(INFO) << "Start solving";
			int step = 0;
			TimePoint elementInsertedLast = initialize();

			ipasir::SolveResult result = ipasir::SolveResult::UNSAT;
			for (;result != ipasir::SolveResult::SAT;step++) {
				LOG(INFO) << "Step " << step;
				if(options.nonIncrementalSolving) {
					elementInsertedLast = initialize();
				}

				int targetMakeSpan = options.stepToMakespan(step);
				for (; makeSpan < targetMakeSpan; makeSpan++) {
					TimePoint tNew = timePointManager->aquireNext();
					addInvariantClauses(tNew);

					if (timePointManager->isOnForwardStack(tNew)) {
						TimePoint pred = timePointManager->getPredecessor(tNew);
						addTransferClauses(pred, tNew);
					} else {
						TimePoint succ = timePointManager->getSuccessor(tNew);
						addTransferClauses(tNew, succ);
					}

					elementInsertedLast = tNew;
				}

				finalize(elementInsertedLast);
				result = solveSAT();
			}

			return result == ipasir::SolveResult::SAT;
		}

		bool solveOneEnded(){
			int step = 0;
			int makeSpan = options.stepToMakespan(0);
			int previousMakeSpan = 0;

			addInitialClauses();
			addInvariantClauses(0);
			addGoalClauses(0, onlyAtK(makeSpan));

			VLOG(1) << "Solving makespan " << makeSpan;
			{
				TIMED_SCOPE(blkScope, "solve");
				ipasir_assume(ipasir, onlyAtK(makeSpan));
				result = ipasir_solve(ipasir);
			}

			while (result == UNSAT && makeSpan < MAX_STEPS) {
				if (options.cleanLitearl) {
					ipasir_add(ipasir, onlyAtK(makeSpan));
				}
				step += 1;
				makeSpan = options.stepToMakespan(step);
				if (options.nonIncrementalSolving) {
					ipasir_release(this->ipasir);
					initIpasir();
					addInitialClauses();
					addInvariantClauses(0);
					previousMakeSpan = 0;
				}

				for (int k = previousMakeSpan + 1; k <= makeSpan; k++) {
					addInvariantClauses(k);
					addTransferClauses(k - 1, k);
				}
				previousMakeSpan = makeSpan;

				if (options.solveBeforeGoalClauses) {
					TIMED_SCOPE(blkScope, "solveBeforeGoalClauses");
					ipasir_solve(ipasir);
				}

				addGoalClauses(makeSpan, onlyAtK(makeSpan));

				VLOG(1) << "Solving makespan: " << makeSpan;
				{
					TIMED_SCOPE(blkScope, "solve");
					ipasir_assume(ipasir, onlyAtK(makeSpan));
					result = ipasir_solve(ipasir);
				}
			}

			this->finalMakeSpan = makeSpan;
			return result == SAT;
		}

		bool solveDoubleEnded(){
			addInitialClauses();
			{
				double ratio = options.ratio;
				mapping = std::unique_ptr<TimeSlotMapping>(
					new TimeSlotMapping(ratio, options.stepToMakespan));
			}

			addInvariantClauses(mapping->startSlot());
			addGoalClauses(mapping->goalSlot());
			addInvariantClauses(mapping->goalSlot());

			addLink(mapping->startTop(), mapping->goalTop(), onlyAtK(mapping->getMakeSpan()));

			VLOG(1) << "Solving makespan: " << mapping->getMakeSpan();
			{
				TIMED_SCOPE(blkScope, "solve");
				ipasir_assume(ipasir, onlyAtK(mapping->getMakeSpan()));
				result = ipasir_solve(ipasir);
			}

			while (result == UNSAT && mapping->getMakeSpan() < MAX_STEPS) {
				if (options.cleanLitearl) {
					ipasir_add(ipasir, onlyAtK(mapping->getMakeSpan()));
				}

				mapping->incrementMakeSpan();

				while (mapping->hasToAdd()) {
					AddInfo info = mapping->add();
					addInvariantClauses(info.addedSlot);
					addTransferClauses(info.transitionSource, info.transitionGoal);
				}

				if (options.solveBeforeGoalClauses) {
					TIMED_SCOPE(blkScope, "solveBeforeGoalClauses");
					ipasir_solve(ipasir);
				}

				addLink(mapping->startTop(), mapping->goalTop(), onlyAtK(mapping->getMakeSpan()));

				VLOG(1) << "Solving makespan: " << mapping->getMakeSpan();
				{
					TIMED_SCOPE(blkScope, "solve");
					ipasir_assume(ipasir, onlyAtK(mapping->getMakeSpan()));
					result = ipasir_solve(ipasir);
				}
			}

			this->finalMakeSpan = mapping->getMakeSpan();
			return result == SAT;
		}

		int onlyAtK(unsigned k) {
			return k + 1;
		}

		int unmap(int k, int literal){
			return map(k, literal, true);
		}

		int map(int k, int literal, bool unmap = false) {
			if (literal == 0) {
				return 0;
			}

			int offset = (MAX_STEPS + 1) + k * problem->numberLiteralsPerTime;
			if (literal < 0) {
				offset = -offset;
			}

			if (unmap) {
				literal -= offset;
			} else {
				literal += offset;
			}
			return literal;
		}

		void addInitialClauses(TimePoint t) {
			for (int literal:problem->initial) {
				addProblemLiteral(literal, t);
			}
		}

		void addInitialClauses() {
			for (int literal:problem->initial) {
				ipasir_add(ipasir, map(0, literal));
			}
		}

		void addInvariantClauses(TimePoint t) {
			for (int literal: problem->invariant) {
				addProblemLiteral(literal, t);
			}
		}

		void addInvariantClauses(unsigned k) {
			for (int literal: problem->invariant) {
				ipasir_add(ipasir, map(k, literal));
			}
		}

		void addTransferClauses(TimePoint source, TimePoint destination) {
			for (int literal: problem->transfer) {
				bool literalIsSourceTime = static_cast<unsigned>(std::abs(literal)) <= problem->numberLiteralsPerTime;
				if (!literalIsSourceTime) {
					if (literal > 0) {
						literal -= problem->numberLiteralsPerTime;
					} else {
						literal += problem->numberLiteralsPerTime;
					}
				}

				if (literalIsSourceTime) {
					addProblemLiteral(literal, source);
				} else {
					addProblemLiteral(literal, destination);
				}
			}
		}

		void addTransferClauses(unsigned transferSrc, unsigned transferDst) {
			for (int literal: problem->transfer) {
				int mapped;
				if ((unsigned) std::abs(literal) <= problem->numberLiteralsPerTime) {
					mapped = map(transferSrc, literal);
				} else {
					if (literal > 0) {
						literal -= problem->numberLiteralsPerTime;
					} else {
						literal += problem->numberLiteralsPerTime;
					}

					mapped = map(transferDst, literal);
				}
				ipasir_add(ipasir, mapped);
			}
		}

		/*
		 * Returns true if problem->goal[i] is a literal in a unit clause
		 *         false otherwise.
		 */
		bool isUnitGoal(unsigned i) {
			if (!options.unitInGoal2Assume) {
				return false;
			}

			if (i == 0) {
				return problem->goal[i + 1] == 0;
			}

			if (problem->goal[i] == 0) {
				return false;
			}

			assert(i > 0 && i + 1 < problem->goal.size());
			return problem->goal[i + 1] == 0 && problem->goal[i - 1] == 0;
		}

		void addGoalClauses(TimePoint t, bool isGuarded = false) {
			for (unsigned i = 0; i < problem->goal.size(); i++) {
				int literal = problem->goal[i];
				if (!isUnitGoal(i)) {
					if (literal == 0 && isGuarded) {
						int activationLiteral = static_cast<int>(HelperVariables::ActivationLiteral);
						addHelperLiteral(-activationLiteral, t);
					}
					addProblemLiteral(literal, t);
				} else {
					assumeProblemLiteral(literal, t);
					++i; // skip following 0
					assert(problem->goal[i] == 0);
				}
			}
		}

		void addGoalClauses(unsigned slot, int guard = 0) {
			for (unsigned i = 0; i < problem->goal.size(); i++) {
				int literal = problem->goal[i];
				if (!isUnitGoal(i)) {
					if (literal == 0 && guard != 0) {
						ipasir_add(ipasir, -guard);
					}
					ipasir_add(ipasir, map(slot, literal));
				} else {
					ipasir_assume(ipasir, map(slot,literal));
					++i; // skip following 0
					assert(problem->goal[i] == 0);
				}
			}
		}

		void addLink(TimePoint A, TimePoint B, TimePoint helperLiteralBinding) {
			for (unsigned i = 1; i <= problem->numberLiteralsPerTime; i++) {
				int activationLiteral = static_cast<int>(HelperVariables::ActivationLiteral);

				addHelperLiteral(-activationLiteral, helperLiteralBinding);
				addProblemLiteral(-i, A);
				addProblemLiteral(i, B);
				finalizeClause();

				addHelperLiteral(-activationLiteral, helperLiteralBinding);
				addProblemLiteral(i, A);
				addProblemLiteral(-i, B);
				finalizeClause();
			}
		}

		void addLink(unsigned slotA, unsigned slotB, int guard) {
			for (unsigned i = 1; i <= problem->numberLiteralsPerTime; i++) {
				int litA = map(slotA, i);
				int litB = map(slotB, i);

				ipasir_add(ipasir, -guard);
				ipasir_add(ipasir, -litA);
				ipasir_add(ipasir, litB);
				ipasir_add(ipasir, 0);

				ipasir_add(ipasir, -guard);
				ipasir_add(ipasir, litA);
				ipasir_add(ipasir, -litB);
				ipasir_add(ipasir, 0);
			}
		}
};

void parseOptions(int argc, char **argv) {
	try {
		//bool defaultIsTrue = true;
		bool defaultIsFalse = false;
		bool neccessaryArgument = true;
		TCLAP::CmdLine cmd("This tool is does sat planing using an incremental sat solver.", ' ', "0.1");
		TCLAP::UnlabeledValueArg<std::string>  inputFile( "inputFile", "File containing the problem. Omit or use - for stdin.", !neccessaryArgument, "-", "inputFile", cmd);
		TCLAP::ValueArg<double>  ratio("r", "ratio", "Ratio between states from start to state from end.", !neccessaryArgument, 1.0, "number between 0 and 1", cmd);
		TCLAP::ValueArg<unsigned>  linearStepSize("l", "linearStepSize", "Linear step size.", !neccessaryArgument, 1, "natural number", cmd);
		TCLAP::ValueArg<float> exponentialStepBasis("e", "exponentialStepBasis", "Basis of exponential step size. Combinable with options -l and -o (varibale names are equal to parameter): step size = l*n + floor(e ^ (n + o))", !neccessaryArgument, 0, "natural number", cmd);
		TCLAP::ValueArg<float> exponentialStepOffset("o", "exponentialStepOffset", "Basis of exponential step size.", !neccessaryArgument, 0, "natural number", cmd);
		TCLAP::SwitchArg unitInGoal2Assume("u", "unitInGoal2Assume", "Add units in goal clauses using assume instead of add. (singleEnded only)", cmd, defaultIsFalse);
		TCLAP::SwitchArg solveBeforeGoalClauses("i", "intermediateSolveStep", "Add an additional solve step before adding the goal or linking clauses.", cmd, defaultIsFalse);
		TCLAP::SwitchArg nonIncrementalSolving("n", "nonIncrementalSolving", "Do not use incremental solving.", cmd, defaultIsFalse);
		TCLAP::SwitchArg cleanLitearl("c", "cleanLitearl", "Add a literal to remove linking or goal clauses.", cmd, defaultIsFalse);

		TCLAP::SwitchArg singleEnded("s", "singleEnded", "Do not use incremental solving.", cmd, defaultIsFalse);
		//TCLAP::SwitchArg outputLinePerStep("", "outputLinePerStep", "Output each time point in a new line. Each time point will use the same literals.", defaultIsFalse);
		TCLAP::SwitchArg outputSolverLike("", "outputSolverLike", "Output result like a normal solver is used. The literals for each time point t are in range t * [literalsPerTime] < lit <= (t + 1) * [literalsPerTime]", cmd, defaultIsFalse);

		if (argc == 1) {
			cmd.getOutput()->usage(cmd);
			exit(0);
		}
		cmd.parse( argc, argv );

		options.error = false;
		options.inputFile = inputFile.getValue();
		options.unitInGoal2Assume = unitInGoal2Assume.getValue();
		options.solveBeforeGoalClauses = solveBeforeGoalClauses.getValue();
		options.nonIncrementalSolving = nonIncrementalSolving.getValue();
		options.normalOutput = outputSolverLike.getValue();
		options.ratio = ratio.getValue();
		options.singleEnded = singleEnded.getValue();
		options.cleanLitearl = cleanLitearl.getValue();
		{
			int l = linearStepSize.getValue();
			float e = exponentialStepBasis.getValue();
			float o = exponentialStepOffset.getValue();
			options.stepToMakespan = [l,e,o](int n){return l * n + std::floor(pow(e,(n + o)));};
		}


		if (options.nonIncrementalSolving) {
			options.singleEnded = true;
		}

	} catch (TCLAP::ArgException &e) {
		options.error = true;
		std::cerr << "error: " << e.error() << " for arg " << e.argId() << std::endl;
	}
}

void initLogger(){
el::Configurations conf;
conf.setToDefault();
conf.setGlobally(el::ConfigurationType::Format, "ci %level %fbase:%line; %msg");
conf.set(el::Level::Fatal, el::ConfigurationType::Format, "%level %fbase:%line; %msg");
el::Loggers::reconfigureAllLoggers(conf);

conf.setGlobally(el::ConfigurationType::Format, "ci %level %datetime{%H:%m:%s}; %msg");
el::Loggers::reconfigureLogger("performance", conf);
el::Loggers::setVerboseLevel(2);
}

int incplan_main(int argc, char **argv) {
	START_EASYLOGGINGPP(argc, argv);
	initLogger();
	parseOptions(argc, argv);

	LOG(INFO) << "Using the incremental SAT solver " << ipasir_signature();

	std::istream* in;
	std::ifstream is;
	if (options.inputFile == "-") {
		in = &std::cin;
		LOG(INFO) << "Using standard input.";
	} else {
		is.open(options.inputFile);
		if (is.fail()){
			LOG(FATAL) << "Input Error can't open file: " << options.inputFile;
		}
		in = &is;
	}

	bool solved;
	{
		Problem problem(*in);
		Solver solver(&problem);
		solved = solver.solve();
		solver.printSolution();
	}

	if (!solved) {
		LOG(WARNING) << "Did not get a solution within the maximal make span.";
	}

	return 0;
}