#pragma once

extern "C" {
	#include "ipasir/ipasir.h"
}

#include <string>
#include <functional>

namespace ipasir {
enum class SolveResult {SAT = 10, UNSAT = 20, TIMEOUT = 0};

class Ipasir {
public:
	virtual std::string signature() = 0;

	virtual ~Ipasir() = default;

	/**
	 * Add the given literal into the currently added clause
	 * or finalize the clause with a 0.  Clauses added this way
	 * cannot be removed. The addition of removable clauses
	 * can be simulated using activation literals and assumptions.
	 *
	 * Required state: INPUT or SAT or UNSAT
	 * State after: INPUT
	 *
	 * Literals are encoded as (non-zero) integers as in the
	 * DIMACS formats.  They have to be smaller or equal to
	 * INT_MAX and strictly larger than INT_MIN (to avoid
	 * negation overflow).  This applies to all the literal
	 * arguments in API functions.
	 */
	virtual void add(int lit_or_zero) = 0;

	/**
	 * Add an assumption for the next SAT search (the next call
	 * of ipasir_solve). After calling ipasir_solve all the
	 * previously added assumptions are cleared.
	 *
	 * Required state: INPUT or SAT or UNSAT
	 * State after: INPUT
	 */
	virtual void assume(int lit) = 0;

	/**
	 * Solve the formula with specified clauses under the specified assumptions.
	 * If the formula is satisfiable the function returns 10 and the state of the solver is changed to SAT.
	 * If the formula is unsatisfiable the function returns 20 and the state of the solver is changed to UNSAT.
	 * If the search is interrupted (see ipasir_set_terminate) the function returns 0 and the state of the solver remains INPUT.
	 * This function can be called in any defined state of the solver.
	 *
	 * Required state: INPUT or SAT or UNSAT
	 * State after: INPUT or SAT or UNSAT
	 */
	virtual SolveResult solve () = 0;

	/**
	 * Get the truth value of the given literal in the found satisfying
	 * assignment. Return 'lit' if True, '-lit' if False, and 0 if not important.
	 * This function can only be used if ipasir_solve has returned 10
	 * and no 'ipasir_add' nor 'ipasir_assume' has been called
	 * since then, i.e., the state of the solver is SAT.
	 *
	 * Required state: SAT
	 * State after: SAT
	 */
	virtual int val(int lit) = 0;

	/**
	 * Check if the given assumption literal was used to prove the
	 * unsatisfiability of the formula under the assumptions
	 * used for the last SAT search. Return 1 if so, 0 otherwise.
	 * This function can only be used if ipasir_solve has returned 20 and
	 * no ipasir_add or ipasir_assume has been called since then, i.e.,
	 * the state of the solver is UNSAT.
	 *
	 * Required state: UNSAT
	 * State after: UNSAT
	 */
	virtual int failed (int lit) = 0;

	/**
	 * Set a callback function used to indicate a termination requirement to the
	 * solver. The solver will periodically call this function and check its return
	 * value during the search. The ipasir_set_terminate function can be called in any
	 * state of the solver, the state remains unchanged after the call.
	 * The callback function is of the form "int terminate()"
	 *   - it returns a non-zero value if the solver should terminate.
	 *
	 * Required state: INPUT or SAT or UNSAT
	 * State after: INPUT or SAT or UNSAT
	 */
	virtual void set_terminate (std::function<int(void)> callback) = 0;

	virtual void reset() = 0;
};

extern "C" {
	int ipasir_terminate_callback(void* state);
	int ipasir_select_literal_callback(void* state);
}

class Solver: public Ipasir {
public:
	Solver():
		solver(nullptr),
		terminateCallback([]{return 0;}),
		selectLiteralCallback([]{return 0;}) {
		reset();
	}

	virtual ~Solver(){
		ipasir_release(solver);
	}

	virtual std::string signature() {
		return ipasir_signature();
	};

	virtual void add(int lit_or_zero) {
		ipasir_add(solver, lit_or_zero);
	}

	virtual void assume(int lit) {
		ipasir_assume(solver, lit);
	}

	virtual SolveResult solve() {
		return static_cast<SolveResult>(ipasir_solve(solver));
	};

	virtual int val(int lit) {
		return ipasir_val (solver, lit);
	};

	virtual int failed (int lit) {
		return ipasir_failed(solver, lit);
	};

	virtual void set_terminate (std::function<int(void)> callback) {
		terminateCallback = callback;
	};

	virtual void reset() {
		if (solver != nullptr) {
			ipasir_release(solver);
		}
		solver = ipasir_init();

		ipasir_set_terminate(this->solver, this, &ipasir_terminate_callback);
		#ifdef USE_EXTENDED_IPASIR
		eipasir_set_select_literal_callback(this->solver, this, &ipasir_select_literal_callback);
		#endif
	}

private:
	void* solver;
	std::function<int(void)> terminateCallback;
	std::function<int(void)> selectLiteralCallback;

	friend int ipasir_terminate_callback(void* state) {
		return static_cast<Solver*>(state)->terminateCallback();
	}

	friend int ipasir_select_literal_callback(void* state) {
		return static_cast<Solver*>(state)->selectLiteralCallback();
	}
};
}