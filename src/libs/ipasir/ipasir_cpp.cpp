#include "ipasir_cpp.h"

namespace ipasir {
	Solver::Solver():
		solver(nullptr),
		terminateCallback([]{return 0;}),
		selectLiteralCallback([]{return 0;}) {
		reset();
	}

	Solver::~Solver(){
		ipasir_release(solver);
	}

	std::string Solver::signature() {
		return ipasir_signature();
	}

	void Solver::add(int lit_or_zero) {
		ipasir_add(solver, lit_or_zero);
	}

	void Solver::assume(int lit) {
		ipasir_assume(solver, lit);
	}

	SolveResult Solver::solve() {
		return static_cast<SolveResult>(ipasir_solve(solver));
	}

	int Solver::val(int lit) {
		return ipasir_val (solver, lit);
	}

	int Solver::failed (int lit) {
		return ipasir_failed(solver, lit);
	}

	void Solver::set_terminate (std::function<int(void)> callback) {
		terminateCallback = callback;
	}

	void Solver::reset() {
		if (solver != nullptr) {
			ipasir_release(solver);
		}
		solver = ipasir_init();

		ipasir_set_terminate(this->solver, this, &ipasir_terminate_callback);
		#ifdef USE_EXTENDED_IPASIR
		eipasir_set_select_literal_callback(this->solver, this, &ipasir_select_literal_callback);
		#endif
	}

	int ipasir_terminate_callback(void* state) {
		return static_cast<Solver*>(state)->terminateCallback();
	}

	int ipasir_select_literal_callback(void* state) {
		return static_cast<Solver*>(state)->selectLiteralCallback();
	}
}