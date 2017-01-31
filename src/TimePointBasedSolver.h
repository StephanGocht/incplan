#pragma once

extern "C" {
	#include "ipasir.h"
}

#include "TimeSlotMapping.h"

#include <vector>
#include <map>

#define SAT 10
#define UNSAT 20
#define TIMEOUT 0


extern "C" {
	int terminate_callback(void* state);
	int select_literal_callback(void* state);
}

class TimePointBasedSolver {
private:
	void *ipasir = nullptr;
	int varsPerTime;
	int helperPerTime;

	std::map<TimePoint, int> timePoints;

public:

	void addProblemLiteral(int lit, TimePoint t) {
		ipasir_add(ipasir, problemLiteral2Ipasir(lit, t));
	}

	void addHelperLiteral(int lit, TimePoint t) {
		ipasir_add(ipasir, helperLiteral2Ipasir(lit, t));
	}

	void assumeProblemLiteral(int lit, TimePoint t) {
		ipasir_assume(ipasir, problemLiteral2Ipasir(lit, t));
	}

	void assumeHelperLiteral(int lit, TimePoint t) {
		ipasir_assume(ipasir, helperLiteral2Ipasir(lit, t));
	}

	void finalizeClause() {
		ipasir_add(ipasir, 0);
	}

	int valueProblemLiteral(int lit, TimePoint t) {
		int value = ipasir_val(ipasir, problemLiteral2Ipasir(lit, t));
		if (value == 0) {
			return 0;
		} else if (value < 0) {
			return -lit;
		} else {
			return lit;
		}
	}


	int solveSAT() {
		return ipasir_solve(ipasir);
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

	TimePointBasedSolver(int _varsPerTime, int _helperPerTime):
		varsPerTime(_varsPerTime),
		helperPerTime(_helperPerTime)
	{
		initIpasir();
	}

	virtual ~TimePointBasedSolver(){
		ipasir_release(ipasir);
	}

private:
	void initIpasir() {
		if (ipasir != nullptr) {
			ipasir_release(ipasir);
		}

		this->ipasir = ipasir_init();
		ipasir_set_terminate(this->ipasir, this, &terminate_callback);
		#ifdef USE_EXTENDED_IPASIR
		eipasir_set_select_literal_callback(this->ipasir, this, &select_literal_callback);
		#endif
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

	friend int select_literal_callback(void* state);
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

extern "C" {
	int state;
	int terminate_callback(void* state){
		UNUSED(state);
		return 0;
	}

	int select_literal_callback(void* state){
		return static_cast<TimePointBasedSolver*>(state)->selectLiteralCallback();
	}
}