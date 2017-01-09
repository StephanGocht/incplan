#pragma once

#include <vector>
#include <functional>

#define UNUSED(x) (void)(x)

/**
 * The prupose of this class is handle and organize time slots. A time slot
 * is fixed size block of variables, similar to a time point. The time slot
 * provides an additional abstraction layer to allow an arbitrary order of
 * time points and space for additional helper variables.
 */
typedef int ProblemLiteral;
typedef int InternalLiteral;
typedef std::pair<int, int> TimePoint;
class TimePointManager {
public:
	virtual TimePoint aquireNext() = 0;
	virtual TimePoint getSuccessor(TimePoint t) = 0;
	virtual TimePoint getPredecessor(TimePoint t) = 0;
	virtual bool isOnForwardStack(TimePoint t) = 0;
	virtual TimePoint getFirst() = 0;
	virtual TimePoint getLast() = 0;
};

class SingleEndedTimePointManager: public TimePointManager {
public:
	virtual TimePoint aquireNext() {
		return std::make_pair(0, next++);
	};
	virtual TimePoint getSuccessor(TimePoint t) {
		return std::make_pair(0, t.second + 1);
	};
	virtual TimePoint getPredecessor(TimePoint t) {
		return std::make_pair(0, t.second - 1);
	};
	virtual bool isOnForwardStack(TimePoint t) {
		UNUSED(t);
		return true;
	}

	virtual TimePoint getFirst() {
		return std::make_pair(0, 0);
	};

	virtual TimePoint getLast() {
		return std::make_pair(0, next - 1);
	};
private:
	int next = 0;
};

class DoubleEndedTimePointManager: public TimePointManager {
public:
	enum class TopElementOption {Unique, Dublicated};

private:
	int currentBeginTop = -1;
	int currentEndTop = -1;
	float ratio;
	TopElementOption topElementOption;
	static const int FROM_BEGIN = 0;
	static const int FROM_END = 1;

public:
	/**
	 * There are two top elements. They represent either the same
	 * timepoint (Dublicated) or are two different timepoints (Unique)
	 */

	DoubleEndedTimePointManager(float _ratio, TopElementOption _topElementOption):
		ratio(_ratio),
		topElementOption(_topElementOption)
	{

	}

	DoubleEndedTimePointManager():
		DoubleEndedTimePointManager(1.f, TopElementOption::Unique)
	{

	}

	virtual TimePoint aquireNext() {
		double newRatio = (currentBeginTop + 2) / static_cast<double>(currentBeginTop + currentEndTop + 3);
		if (newRatio <= ratio) {
			return std::make_pair(FROM_BEGIN, ++currentBeginTop);
		} else {
			return std::make_pair(FROM_END, ++currentEndTop);
		}
	};

	virtual TimePoint getSuccessor(TimePoint t) {
		if (t.first == FROM_BEGIN) {
			if (t.second < currentBeginTop) {
				return std::make_pair(FROM_BEGIN, t.second + 1);
			} else {
				if (topElementOption == TopElementOption::Dublicated) {
					return std::make_pair(FROM_END, currentEndTop - 1);
				} else {
					return std::make_pair(FROM_END, currentEndTop);
				}
			}
		} else {
			if (t.second > 0) {
				return std::make_pair(FROM_END, t.second - 1);
			} else {
				return std::make_pair(-1, -1);
			}
		}
	};

	virtual TimePoint getPredecessor(TimePoint t) {
		if (t.first == FROM_BEGIN) {
			if (t.second > 0) {
				return std::make_pair(FROM_BEGIN, t.second - 1);
			} else {
				return std::make_pair(-1, -1);
			}
		} else {
			if (t.second < currentEndTop) {
				return std::make_pair(FROM_END, t.second + 1);
			} else {
				if (topElementOption == TopElementOption::Dublicated) {
					return std::make_pair(FROM_BEGIN, currentBeginTop - 1);
				} else {
					return std::make_pair(FROM_BEGIN, currentBeginTop);
				}
			}
		}
	};

	virtual bool isOnForwardStack(TimePoint t) {
		if (t.first == FROM_BEGIN) {
			return true;
		} else {
			return false;
		}
	};

	virtual TimePoint getFirst() {
		return std::make_pair(FROM_BEGIN, 0);
	};

	virtual TimePoint getLast() {
		return std::make_pair(FROM_END, 0);
	};

	TimePoint getBeginTop() {
		return std::make_pair(0, currentBeginTop);
	}

	TimePoint getEndTop() {
		return std::make_pair(0, currentEndTop);
	}
};