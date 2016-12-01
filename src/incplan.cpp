extern "C" {
    #include "ipasir.h"
}

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

#include "tclap/CmdLine.h"
#include "logging.h"
INITIALIZE_EASYLOGGINGPP

#define UNUSED(x) (void)(x)

#define MAX_STEPS 1000
#define SAT 10
#define UNSAT 20
#define TIMEOUT 0

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
	}

	std::vector<int> initial, invariant, goal , transfer;
	unsigned numberLiteralsPerTime;

private:
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
	int callback(void* state){
		UNUSED(state);
		return 0;
	}
}


class Solver {
	public:
		Solver(const Problem* problem){
			this->ipasir = ipasir_init();
			ipasir_set_terminate(this->ipasir, &state, &callback);
			this->problem = problem;
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
			LOG(INFO) << "Final Makespan: " << finalMakeSpan;
			return result;
		}

		void printSolution() {
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
		}

		~Solver(){
			ipasir_release(ipasir);
		}

	private:
		const Problem* problem;
		void* ipasir;
		std::unique_ptr<TimeSlotMapping> mapping;

		int finalMakeSpan;
		int result;

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
				makeSpan += options.stepToMakespan(step);
				if (options.nonIncrementalSolving) {
					ipasir_release(this->ipasir);
					this->ipasir = ipasir_init();
					ipasir_set_terminate(this->ipasir, &state, &callback);
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

		void addInitialClauses() {
			for (int literal:problem->initial) {
				ipasir_add(ipasir, map(0, literal));
			}
		}

		void addInvariantClauses(unsigned k) {
			for (int literal: problem->invariant) {
				ipasir_add(ipasir, map(k, literal));
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
el::Loggers::setVerboseLevel(1);
}

int main(int argc, char **argv) {
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
}
