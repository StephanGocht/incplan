#include "TimePointBasedSolver.h"

#include <cassert>

void TimePointBasedSolver::getInfo(int ipasir_lit, int& literal, TimePoint& t, bool& isHelper) {
	if (ipasir_lit == 0) {
		literal = 0;
		return;
	}

	assert(helperVariablePosition == HelperVariablePosition::SingleAfter);

	int var = std::abs(ipasir_lit);
	int allVarsPerTime = (varsPerTime + helperPerTime);
	int timePointId = var / allVarsPerTime;

	auto it = find_if(timePoints.begin(), timePoints.end(), [timePointId](const auto & p) {
		return p.second == timePointId;
	});
	if (it == timePoints.end()) {
		/*timepoint not found*/
		assert(false && "Internal Error");
	}

	t = it->first;
	literal = var % allVarsPerTime;
	isHelper = false;
	if (literal > varsPerTime) {
		isHelper = true;
		literal -= varsPerTime;
	}

	if (ipasir_lit < 0) {
		literal = -literal;
	}
}

int TimePointBasedSolver::getOffset(int literal, TimePoint t, bool isHelper) {
	if (literal == 0) {
		return 0;
	}

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