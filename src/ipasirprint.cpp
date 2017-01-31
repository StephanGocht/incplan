extern "C" {
	#include "ipasir.h"
}

#include <iostream>
#include <limits>

extern "C" {
	#define SAT 10
	#define UNSAT 20
	#define TIMEOUT 0

	const char * ipasir_signature (){
		return "printing all clauses";
	}

	void * ipasir_init (){
		return nullptr;
	}

	void ipasir_release (void * solver){}

	void ipasir_add (void * solver, int lit_or_zero){
		std::cout << lit_or_zero << " ";
		if (lit_or_zero == 0) {
			std::cout << std::endl;
		}
	}

	void ipasir_assume (void * solver, int lit){
		std::cout << "a" << lit << " ";
	}

	int ipasir_solve (void * solver){
		std::cout << " solved? 0/1 [0]: ";
		bool solved = false;
		if (std::cin.peek() == '\n') { //check if next character is newline
			solved = false; //and assign the default
		} else if (!(std::cin >> solved)) { //be sure to handle invalid input
			std::cout << "Invalid input. Using default.\n";
			std::cin.clear();
		//error handling
		}

		std::cin.ignore( std::numeric_limits<std::streamsize>::max(), '\n' );
		if (solved) {
			return SAT;
		} else {
			return UNSAT;
		}
	}

	int ipasir_val (void * solver, int lit){
		return 0;
	}


	int ipasir_failed (void * solver, int lit){
		return 0;
	}

	void ipasir_set_terminate (void * solver, void * state, int (*terminate)(void * state)){}
}