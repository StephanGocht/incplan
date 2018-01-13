#pragma once

#include "ipasir/ipasir_cpp.h"
#include "ipasir/randomized_ipasir.h"

#include "TimeSlotMapping.h"
#include "carj/logging.h"

#include <vector>
#include <map>
#include <memory>

struct TimedLiteral {
	int literal;
	TimePoint t;
	bool isHelper;

	TimedLiteral operator-(){
		TimedLiteral result = *this;
		result.literal = -result.literal;
		return result;
	}
};

class TimePointBasedSolver {
public:
	enum class HelperVariablePosition {AllBefore, SingleBefore, SingleAfter};

private:
	std::map<TimePoint, int> timePoints;

public:
	int varsPerTime;
	int helperPerTime;

	std::unique_ptr<ipasir::Ipasir> solver;
	const HelperVariablePosition helperVariablePosition;

	void add(const TimedLiteral& lit) {
		if (lit.isHelper) {
			addHelperLiteral(lit.literal, lit.t);
		} else {
			addProblemLiteral(lit.literal, lit.t);
		}
	}

	void addAsLearned(const TimedLiteral& lit) {
		if (lit.isHelper) {
			solver->addAsLearned(helperLiteral2Ipasir(lit.literal, lit.t));
		} else {
			solver->addAsLearned(problemLiteral2Ipasir(lit.literal, lit.t));
		}
	}

	void finalizeLearned() {
		solver->addAsLearned(0);
	}

	void addClause(const std::vector<TimedLiteral> clause) {
		for (const TimedLiteral& lit: clause) {
			add(lit);
		}
		finalizeClause();
	}

	void assume(const TimedLiteral &lit) {
		if (lit.isHelper) {
			assumeHelperLiteral(lit.literal, lit.t);
		} else {
			assumeProblemLiteral(lit.literal, lit.t);
		}
	}

	void assume(const std::vector<TimedLiteral> clause) {
		for (const TimedLiteral &lit: clause) {
			assume(lit);
		}
	}

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

	TimedLiteral getInfo(int ipasir_lit);

	bool failed(const TimedLiteral& lit) {
		int l;
		if (lit.isHelper) {
			l = helperLiteral2Ipasir(lit.literal, lit.t);
		} else {
			l = problemLiteral2Ipasir(lit.literal, lit.t);
		}
		return 1 == solver->failed(l);
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
		std::unique_ptr<ipasir::Ipasir> _solver,
		HelperVariablePosition _helperVariablePosition):
		varsPerTime(_varsPerTime),
		helperPerTime(_helperPerTime),
		solver(std::move(_solver)),
		helperVariablePosition(_helperVariablePosition)
	{
		if (helperVariablePosition == HelperVariablePosition::AllBefore) {
			VLOG(1) << "Placing helper variables before encoding.";
		}
	}

	TimePointBasedSolver(int _varsPerTime, int _helperPerTime,
			std::unique_ptr<ipasir::Ipasir> _solver):
		TimePointBasedSolver(_varsPerTime, _helperPerTime,
			std::move(_solver),
			HelperVariablePosition::SingleAfter)
	{
	}

	TimePointBasedSolver(int _varsPerTime, int _helperPerTime):
		TimePointBasedSolver(_varsPerTime, _helperPerTime,
			//std::make_unique<ipasir::RandomizedSolver>(std::make_unique<ipasir::Solver>()),
			std::make_unique<ipasir::Solver>(),
			HelperVariablePosition::SingleAfter)
	{
	}

	virtual ~TimePointBasedSolver(){

	}

	virtual void reset() {
		solver->reset();
	}

	int problemLiteral2Ipasir(int literal, TimePoint t) {
		return getOffset(literal, t) + literal;
	}

	int helperLiteral2Ipasir(int literal, TimePoint t) {
		return getOffsetHelper(literal, t) + literal;
	}

private:
	int getIndex(TimePoint t) {
		auto insertResult = timePoints.insert(std::make_pair(t, timePoints.size()));
		return insertResult.first->second;
	}

	int getOffsetHelper(int literal, TimePoint t) {
		return getOffset(literal, t, true);
	}

	int getOffset(int literal, TimePoint t, bool isHelper = false);


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
