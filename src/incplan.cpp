/*
 * genipaplan.cpp
 *
 *  Created on: Jul 20, 2015
 *      Author: Tomas Balyo, KIT
		Stephan Gocht, KIT
 */

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

#include <tclap/CmdLine.h>

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
};

Options options;

class Problem {
public:
	Problem(std::istream& in){
		this->numberLiterals = 0;
		parse(in);
	}

	std::vector<int> initial, invariant, goal , transfer;
	int numberLiterals;

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
		int literals;
		int numberClauses;
		std::string cnfString;
		in >> type >> cnfString >> literals >> numberClauses;
		if (!in.good() || cnfString != "cnf") {
			std::string line;
			in.clear();
			in >> line;
			std::cout << "Input Error: Expected [iugt] cnf [0-9*] [0-9*] but got: " << line << std::endl;
			std::exit(1);
		}

		if (type != expectedType) {
			std::cout << "Input Error: Expected type " << expectedType << " but got: " << type << std::endl;
			std::abort();
		}

		switch(type) {
			case 'i':
			case 'u':
			case 'g':
			case 't':
			break;
			default:
			std::cout << "Input Error: Expected type i,u,g or t but got " << type << std::endl;
			std::abort();
		}

		if (numberLiterals == 0) {
			numberLiterals = literals;
		} else if (literals != numberLiterals && (type != 't' || literals != 2 * numberLiterals)) {
			std::cout << "Input Error: Wrong Number of Literals!" << literals << ":" << numberLiterals << type << std::endl;
			std::abort();
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
			std::cout << "Input Error: Got empty File." << std::endl;
			std::abort();
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

class Solver {
	public:
		Solver(const Problem* problem){
			this->ipasir = ipasir_init();
			this->offset = 0;
			this->problem = problem;
		}

		/**
		 * Solve the problem. Return true if a solution was found.
		 */
		bool solve(){
			int makeSpan = 0;
			int previousMakeSpan = 0;

			addInitialClauses();
			addInvariantClauses(0);
			addGoalClauses(0);
			ipasir_assume(ipasir, onlyAtK(0));
			result = ipasir_solve(ipasir);

			while (result == UNSAT && makeSpan < MAX_STEPS) {
				makeSpan++;
				if (options.nonIncrementalSolving) {
					ipasir_release(ipasir);
					ipasir = ipasir_init();
					addInitialClauses();
					addInvariantClauses(0);
					previousMakeSpan = 0;
				}

				for (int k = previousMakeSpan + 1; k <= makeSpan; k++) {
					addInvariantClauses(k);
					addTransferClauses(k);
				}
				previousMakeSpan = makeSpan;

				if (options.solveBeforeGoalClauses) {
					ipasir_solve(ipasir);
				}

				addGoalClauses(makeSpan);
				ipasir_assume(ipasir, onlyAtK(makeSpan));
				result = ipasir_solve(ipasir);
			}

			this->finalMakeSpan = makeSpan;
			return result == SAT;
		}

		void printSolution() {
			if (this->result == SAT) {
				std::cout << "solution " << this->problem->numberLiterals << " " << this->finalMakeSpan + 1 << std::endl;
				for (int i = 0; i <= this->finalMakeSpan; i++) {
					for (int j = 1; j <= this->problem->numberLiterals; j++) {
						int val = ipasir_val(ipasir, map(i,j));
						val = unmap(i, val);

						if (val == 0) {
							val = j;
						}

						int offset = i * problem->numberLiterals;
						if (val < 0) {
							offset = -offset;
						}
						val += offset;

						//assert(abs(val) == j);
						std::cout << val << " ";
					}
					//std::cout << std::endl;
				}
				std::cout << std::endl;
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
		int offset;
		int finalMakeSpan;
		int result;

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

			int offset = (MAX_STEPS + 1) + k * problem->numberLiterals;
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

		void addTransferClauses(unsigned k) {
			for (int literal: problem->transfer) {
				ipasir_add(ipasir, map(k - 1, literal));
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

		void addGoalClauses(unsigned k) {
			for (unsigned i = 0; i < problem->goal.size(); i++) {
				int literal = problem->goal[i];
				if (!isUnitGoal(i)) {
					if (literal == 0) {
						ipasir_add(ipasir, -onlyAtK(k));
					}
					ipasir_add(ipasir, map(k, literal));
				} else {
					ipasir_assume(ipasir, map(k,literal));
					++i; // skip following 0
					assert(problem->goal[i] == 0);
				}
			}
		}
};

int main(int argc, char **argv) {
	try {
		bool defaultIsTrue = true;
		bool defaultIsFalse = false;
		bool neccessaryArgument = true;
		TCLAP::CmdLine cmd("This tool is does sat planing using an incremental sat solver.", ' ', "0.1");
		TCLAP::UnlabeledValueArg<std::string>  inputFile( "inputFile", "File containing the problem. Omit or use - for stdin.", !neccessaryArgument, "-", "inputFile", cmd);
		TCLAP::SwitchArg unitInGoal2Assume("u", "unitInGoal2Assume", "Add units in goal clauses using assume instead of add.", cmd, defaultIsFalse);
		TCLAP::SwitchArg solveBeforeGoalClauses("s", "solveBeforeGoalClauses", "Add an additional solve step before adding the goal clauses.", cmd, defaultIsFalse);
		TCLAP::SwitchArg nonIncrementalSolving("n", "nonIncrementalSolving", "Do not use incremental solving.", cmd, defaultIsFalse);
		cmd.parse( argc, argv );

		options.error = false;
		options.inputFile = inputFile.getValue();
		options.unitInGoal2Assume = unitInGoal2Assume.getValue();
		options.solveBeforeGoalClauses = solveBeforeGoalClauses.getValue();
		options.nonIncrementalSolving = nonIncrementalSolving.getValue();

	} catch (TCLAP::ArgException &e) {
		options.error = true;
		std::cerr << "error: " << e.error() << " for arg " << e.argId() << std::endl;
	}

	std::cout << "c Using the incremental SAT solver " << ipasir_signature() << std::endl;

	std::istream* in;
	std::ifstream is;
	if (options.inputFile == "-") {
		in = &std::cin;
		std::cout << "c Using standard input." << std::endl;
	} else {
		is.open(options.inputFile);
		if (is.fail()){
			std::cout << "Input Error can't open file: " << options.inputFile << std::endl;
			std::abort();
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
		std::cout << "c WARNING: did not get a solution within the maximal make span" << std::endl;
	}
}
