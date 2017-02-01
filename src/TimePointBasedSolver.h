#pragma once

#include "ipasir/ipasir_cpp.h"

#include "TimeSlotMapping.h"

#include <vector>
#include <map>
#include <memory>

class TimePointBasedSolver {
private:
	int varsPerTime;
	int helperPerTime;

	std::map<TimePoint, int> timePoints;
	std::unique_ptr<ipasir::Ipasir> solver;

public:

	void addProblemLiteral(int lit, TimePoint t) {
		solver->add(problemLiteral2Ipasir(lit, t));
	}

	void addHelperLiteral(int lit, TimePoint t) {
		solver->add(helperLiteral2Ipasir(lit, t));
	}

	void assumeProblemLiteral(int lit, TimePoint t) {
		solver->assume(problemLiteral2Ipasir(lit, t));
	}

	void assumeHelperLiteral(int lit, TimePoint t) {
		solver->assume(helperLiteral2Ipasir(lit, t));
	}

	void finalizeClause() {
		solver->add(0);
	}

	int valueProblemLiteral(int lit, TimePoint t) {
		int value = solver->val(problemLiteral2Ipasir(lit, t));
		if (value == 0) {
			return 0;
		} else if (value < 0) {
			return -lit;
		} else {
			return lit;
		}
	}


	ipasir::SolveResult solveSAT() {
		return solver->solve();
	}

	/**
	 * This method provides a hint on the literal to be set or zero if no hint is available
	 * The result is stored in the provided, referenc variables.
	 */
	virtual void selectLiteral(int &resultLit, TimePoint& timePoint, bool& isHelper) {
		UNUSED(timePoint);
		UNUSED(isHelper);
		resultLit = 0;
	};

	TimePointBasedSolver(int _varsPerTime, int _helperPerTime,
		std::unique_ptr<ipasir::Ipasir> _solver):
		varsPerTime(_varsPerTime),
		helperPerTime(_helperPerTime),
		solver(std::move(_solver))
	{
	}

	TimePointBasedSolver(int _varsPerTime, int _helperPerTime):
		TimePointBasedSolver(_varsPerTime, _helperPerTime,
			std::make_unique<ipasir::Solver>())
	{
	}

	virtual ~TimePointBasedSolver(){

	}

private:
	void initIpasir() {
		solver->reset();
	}

	int getIndex(TimePoint t) {
		auto insertResult = timePoints.insert(std::make_pair(t, timePoints.size()));
		return insertResult.first->second;
	}

	int getOffset(int literal, TimePoint t) {
		if (literal == 0) {
			return 0;
		}

		int offset = getIndex(t) * (varsPerTime + helperPerTime);
		if (literal < 0) {
			offset = -offset;
		}
		return offset;
	}

	int problemLiteral2Ipasir(int literal, TimePoint t) {
		return getOffset(literal, t) + literal;
	}

	int helperLiteral2Ipasir(int literal, TimePoint t) {
		return getOffset(literal, t) + varsPerTime + literal;
	}

	int selectLiteralCallback() {
		// Return Values:
		int resultLit;
		TimePoint timePoint;
		bool isHelper;
		selectLiteral(resultLit, timePoint, isHelper);

		if (isHelper) {
			return helperLiteral2Ipasir(resultLit, timePoint);
		} else {
			return problemLiteral2Ipasir(resultLit, timePoint);
		}
	};
};