extern "C" {
	#include "ipasir.h"
}

#include <iostream>

void notImplemented(){
	// This will be called within a c function so we can not use exceptions
	std::cerr << "Fatal Error: Got call to function not part of the ipasir implementation!" <<  std::endl;
	std::abort();
}

void linkingError(){
	// This will be called within a c function so we can not use exceptions
	std::cerr << "Fatal Error: Something went wrong during linking of the program!" << std::endl;
	std::abort();
}

extern "C" {
	const char * ipasir_signature () {linkingError();}
	void * ipasir_init () {linkingError();}
	void ipasir_release (void * solver){linkingError();}
	void ipasir_add (void * solver, int lit_or_zero){linkingError();}
	void ipasir_assume (void * solver, int lit){linkingError();}
	int ipasir_solve (void * solver){linkingError();}
	int ipasir_val (void * solver, int lit){notImplemented();}
	int ipasir_failed (void * solver, int lit){notImplemented();}
	void ipasir_set_terminate (void * solver, void * state, int (*terminate)(void * state)){notImplemented();}
	void ipasir_set_learn (void * solver, void * state, int max_length, void (*learn)(void * state, int * clause)){notImplemented();}
	void ipasir_add_as_learned(void * solver, int lit_or_zero){notImplemented();}
}