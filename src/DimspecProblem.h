#pragma once

#include <vector>
#include <set>
#include <map>
#include <iostream>
#include <memory>

class DimspecProblem {
public:
	DimspecProblem(std::istream& in);

	std::vector<int> initial, invariant, goal , transfer;
	unsigned numberLiteralsPerTime;
	std::vector<int> actionVariables;
	std::vector<int> stateVariables;
	std::map<int, std::vector<int>> support;

	std::vector<std::vector<int>> solution;

	void printSolution(bool outputSolverLike, std::ostream& out = std::cout) {
		if (!outputSolverLike) {
			out << "solution " << this->numberLiteralsPerTime << " " << this->solution.size() << std::endl;
		}
		int time = 0;
		for (auto& timedSolution: solution) {
			for (int lit:timedSolution) {
				if (outputSolverLike) {
					int offset = time * this->numberLiteralsPerTime;
					if (lit < 0) {
						offset = -offset;
					}
					lit += offset;
				}
				out << lit << " ";
			}
			if (!outputSolverLike) {
				out << std::endl;
			}
			time += 1;
		}
		if (outputSolverLike) {
			out << std::endl;
		}
	}

	virtual void storedSolutionNotifier() {};

protected:
	DimspecProblem(){};
	void inferAdditionalInformation();

private:
	void skipComments(std::istream& in);
	int parseCnfHeader(char expectedType, std::istream& in);
	void parseCnf(std::vector<int>& cnf, std::istream& in);
	void parse(std::istream& in);
};

class DoubleEndedProblem: public DimspecProblem {
private:
	DimspecProblem* originalProblem;

public:
	int addOffset(int lit, int offset) {
		if (lit == 0) {
			return 0;
		}

		if (lit < 0) {
			offset = -offset;
		}
		return lit + offset;
	}

	virtual void storedSolutionNotifier() {
		originalProblem->solution.clear();

		for(auto it = solution.begin();it < solution.end();it++) {
			std::vector<int>& timedSolution = *it;
			originalProblem->solution.push_back(std::vector<int>());
			for (int lit: timedSolution) {
				if (std::abs(lit) <= originalProblem->numberLiteralsPerTime) {
					originalProblem->solution.back().push_back(lit);
				}
			}
		}

		bool first = true;
		for (auto it = solution.rbegin();it < solution.rend();it++) {
			if (first) {
				// the turnaround state is duplicated.
				first = false;
				it++;
			}
			std::vector<int>& timedSolution = *it;
			originalProblem->solution.push_back(std::vector<int>());
			for (int lit: timedSolution) {
				if ((std::abs(lit) > originalProblem->numberLiteralsPerTime) &&
					(std::abs(lit) <= 2 * originalProblem->numberLiteralsPerTime))
				{
					lit = addOffset(lit, -originalProblem->numberLiteralsPerTime);
					originalProblem->solution.back().push_back(lit);
				}
			}
		}

		originalProblem->storedSolutionNotifier();
	};

	DoubleEndedProblem(DimspecProblem* problem):
		originalProblem(problem){
		this->numberLiteralsPerTime = 2 * originalProblem->numberLiteralsPerTime + 1;
		int activationVar = this->numberLiteralsPerTime;
		this->initial.insert(
			initial.end(),
			originalProblem->initial.begin(),
			originalProblem->initial.end());
		for (int lit: originalProblem->goal) {
			lit = addOffset(lit, originalProblem->numberLiteralsPerTime);
			this->initial.push_back(lit);
		}

		for (int lit: originalProblem->transfer) {
			if (std::abs(lit) <= originalProblem->numberLiteralsPerTime) {
				this->transfer.push_back(lit);
			} else {
				int offset = 0;
				offset -= originalProblem->numberLiteralsPerTime;
				offset += this->numberLiteralsPerTime;
				lit = addOffset(lit, offset);
				this->transfer.push_back(lit);
			}
		}

		for (int lit: originalProblem->transfer) {
			if (std::abs(lit) <= originalProblem->numberLiteralsPerTime) {
				int offset = 0;
				offset += originalProblem->numberLiteralsPerTime;
				offset += this->numberLiteralsPerTime;
				lit = addOffset(lit, offset);
				this->transfer.push_back(lit);
			} else {
				this->transfer.push_back(lit);
			}
		}

		for (unsigned var = 1; var <= originalProblem->numberLiteralsPerTime; var++) {
			unsigned varOther = var + originalProblem->numberLiteralsPerTime;

			this->invariant.push_back(-var);
			this->invariant.push_back(varOther);
			this->invariant.push_back(-activationVar);
			this->invariant.push_back(0);
			this->invariant.push_back(var);
			this->invariant.push_back(-varOther);
			this->invariant.push_back(-activationVar);
			this->invariant.push_back(0);
		}

		this->invariant.insert(
			invariant.end(),
			originalProblem->invariant.begin(),
			originalProblem->invariant.end());
		for (int lit: originalProblem->invariant) {
			lit = addOffset(lit, originalProblem->numberLiteralsPerTime);
			this->invariant.push_back(lit);
		}

		this->goal.push_back(activationVar);
		this->goal.push_back(0);

		inferAdditionalInformation();
	}
};
