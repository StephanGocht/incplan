#include "ipasir_cpp.h"
#include <vector>

#include <algorithm>
#include <random>

namespace ipasir {
class RandomizedSolver : public Solver {
public:
	RandomizedSolver(int guessOnNumberLiterals) {
		extendMapping(guessOnNumberLiterals);
	}

	virtual void add(int lit_or_zero) {
		Solver::add(map(lit_or_zero));
	}

	virtual void assume(int lit) {
		Solver::assume(map(lit));
	}

	virtual int val(int lit) {
		return unmap(Solver::val(map(lit)));
	};

	virtual int failed (int lit) {
		return Solver::failed(map(lit));
	};


private:
	std::vector<int> toIpasir;
	std::vector<int> fromIpasir;

	int unmap(int literal) {
		return map(literal, true);
	}

	int map(int literal, bool unMap = false) {
		if (literal == 0) {
			return 0;
		}

		unsigned variable = std::abs(literal);
		int sign = (literal < 0)? -1 : 1;

		if (variable > toIpasir.size()) {
			extendMapping(2*toIpasir.size());
		}

		if (!unMap) {
			// Note that toIpasir is a permutation from [0,size())
			variable = toIpasir[variable - 1] + 1;
		} else {
			variable = fromIpasir[variable - 1] + 1;
		}

		return sign * variable;
	}

	void extendMapping(int newSize) {
		std::random_device rd;
		std::mt19937 g(rd());

		size_t oldSize = toIpasir.size();
		toIpasir.resize(newSize);
		fromIpasir.resize(newSize);

		for (auto i = oldSize; i < toIpasir.size(); i++) {
			toIpasir[i] = i;
		}

		std::shuffle(toIpasir.begin() + oldSize, toIpasir.end(), g);

		for (auto i = oldSize; i < toIpasir.size(); i++) {
			fromIpasir[toIpasir[i]] = i;
		}
	}
};
}