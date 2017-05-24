#include "TimePointBasedSolver.h"

#include <cassert>

TimedLiteral TimePointBasedSolver::getInfo(int ipasir_lit) {
	TimedLiteral result;
	if (ipasir_lit == 0) {
		result.literal = 0;
		return result;
	}

	assert(helperVariablePosition == HelperVariablePosition::SingleAfter);

	int var = std::abs(ipasir_lit) - 1;
	int allVarsPerTime = (varsPerTime + helperPerTime);
	int timePointId = var / allVarsPerTime;

	auto it = find_if(timePoints.begin(), timePoints.end(), [timePointId](const auto & p) {
		return p.second == timePointId;
	});
	if (it == timePoints.end()) {
		/*timepoint not found*/
		assert(false && "Internal Error");
	}

	TimePoint t = it->first;
	int literal = var % allVarsPerTime + 1;
	bool isHelper = false;
	if (literal > varsPerTime) {
		isHelper = true;
		literal -= varsPerTime;
	}

	if (ipasir_lit < 0) {
		literal = -literal;
	}

	result.literal = literal;
	assert(literal != 0 && "Internal Error");
	result.isHelper = isHelper;
	result.t = t;

	return result;
}

int TimePointBasedSolver::getOffset(int literal, TimePoint t, bool isHelper) {
	if (literal == 0) {
		return 0;
	}
	assert(helperPerTime == 2);

	int offset = 0;
	switch (helperVariablePosition) {
		case HelperVariablePosition::SingleBefore:
			offset = getIndex(t) * (varsPerTime + helperPerTime);
			if (!isHelper) {
				offset += helperPerTime;
			}
			break;

		case HelperVariablePosition::SingleAfter:
			offset = getIndex(t) * (varsPerTime + helperPerTime);
			if (isHelper) {
				offset += varsPerTime;
			}
			break;

		case HelperVariablePosition::AllBefore:
			if (isHelper) {
				offset = getIndex(t) * helperPerTime;
			} else {
				offset = getIndex(t) * varsPerTime + 1000;
			}
			break;
	}

	if (literal < 0) {
		offset = -offset;
	}

	return offset;
}
