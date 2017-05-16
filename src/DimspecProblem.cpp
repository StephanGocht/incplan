#include "DimspecProblem.h"

#include "carj/logging.h"
#include <cassert>

DimspecProblem::DimspecProblem(std::istream& in){
	this->numberLiteralsPerTime = 0;
	parse(in);
	inferAdditionalInformation();
}


void DimspecProblem::inferAdditionalInformation() {
	VLOG(2) << "Number Of Literals per Time: " << this->numberLiteralsPerTime;

	// state variables should all be set in the initial state
	std::set<int> stateVariables;
	for (int lit: this->initial) {
		stateVariables.insert(std::abs(lit));
	}
	stateVariables.erase(0);
	std::copy(stateVariables.begin(), stateVariables.end(), std::back_inserter(this->stateVariables));

	// {
	// 	std::stringstream ss;
	// 	ss << "State Variables: ";
	// 	for (int var: stateVariables) {
	// 		ss << var << ", ";
	// 	}
	// 	VLOG(2) << ss.str();
	// }


	// // guess action variables from clauses containing states
	// std::set<int> actionVariablesHelper;
	// size_t clauseStart = 0;
	// bool clauseHasStateVar = false;
	// for (size_t i = 0; i < this->transfer.size(); i++) {
	// 	unsigned var = std::abs(this->transfer[i]);
	// 	var = var > this->numberLiteralsPerTime ? var - this->numberLiteralsPerTime: var;
	// 	if (this->transfer[i] != 0) {
	// 		if (stateVariables.find(var) != stateVariables.end()) {
	// 			clauseHasStateVar = true;
	// 		}
	// 	} else {
	// 		if (clauseHasStateVar) {
	// 			for (size_t j = clauseStart; j < i; j++) {
	// 				unsigned var = std::abs(this->transfer[j]);
	// 				var = var > this->numberLiteralsPerTime ? var - this->numberLiteralsPerTime: var;
	// 				actionVariablesHelper.insert(var);
	// 			}
	// 		}

	// 		clauseStart = i + 1;
	// 		clauseHasStateVar = false;
	// 	}
	// }

	// std::set<int> actionVariables;
	// std::set_difference(actionVariablesHelper.begin(), actionVariablesHelper.end(),
	// 					stateVariables.begin(), stateVariables.end(),
	// 					std::inserter(actionVariables, actionVariables.end()));

	// std::vector<int> currentClauseActions;
	// std::vector<int> currentClauseFutureState;
	// for (size_t i = 0; i < this->transfer.size(); i++) {
	// 	unsigned var = std::abs(this->transfer[i]);
	// 	if (var == 0) {
	// 		for (int stateVar: currentClauseFutureState) {
	// 			auto res = support.insert(std::make_pair(stateVar, std::vector<int>()));
	// 			std::copy(currentClauseActions.begin(), currentClauseActions.end(), std::back_inserter(res.first->second));
	// 		}

	// 	} else {
	// 		bool isNextTime = false;
	// 		if (var > this->numberLiteralsPerTime) {
	// 			isNextTime = true;
	// 			var -= this->numberLiteralsPerTime;
	// 		}

	// 		if (stateVariables.find(var) != stateVariables.end() && isNextTime) {
	// 			currentClauseFutureState.push_back(var);
	// 		}

	// 		if (actionVariables.find(var) != actionVariables.end()) {
	// 			assert(!isNextTime);
	// 			currentClauseActions.push_back(var);
	// 		}
	// 	}
	// }

	// std::copy(actionVariables.begin(), actionVariables.end(), std::back_inserter(this->actionVariables));

	// {
	// 	std::stringstream ss;
	// 	ss << "State Variables: ";
	// 	for (int var: actionVariables) {
	// 		ss << var << ", ";
	// 	}
	// 	VLOG(2) << ss.str();
	// }

}

void DimspecProblem::skipComments(std::istream& in){
	char nextChar;
	in >> nextChar;
	while ( nextChar == 'c' ) {
		in.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
		in >> nextChar;
	}
	if (in.eof()) {
		std::cerr << "Input Error: Expected [iugt] cnf [0-9*] [0-9*] but got nothing. (File empty or only comments) " << std::endl;
		std::exit(1);
	}
	// Next character wasn't c, so revert the last get:
	in.unget();
	assert(in.good() && "Internal Error: Failed to put back character to stream. Change previous code.");
}

int DimspecProblem::parseCnfHeader(char expectedType, std::istream& in) {
	char type;
	unsigned literals;
	int numberClauses;
	std::string cnfString;
	in >> type >> cnfString >> literals >> numberClauses;
	if (!in.good() || cnfString != "cnf") {
		std::string line;
		in.clear();
		in >> line;
		LOG(FATAL) << "Input Error: Expected [iugt] cnf [0-9*] [0-9*] but got: " << line;
	}

	if (type != expectedType) {
		LOG(FATAL) << "Input Error: Expected type " << expectedType << " but got: " << type;
	}

	switch(type) {
		case 'i':
		case 'u':
		case 'g':
		case 't':
		break;
		default:
		LOG(FATAL) << "Input Error: Expected type i,u,g or t but got " << type;
	}

	if (numberLiteralsPerTime == 0) {
		numberLiteralsPerTime = literals;
	} else if (literals != numberLiteralsPerTime && (type != 't' || literals != 2 * numberLiteralsPerTime)) {
		LOG(FATAL) << "Input Error: Wrong Number of Literals!" << literals << ":" << numberLiteralsPerTime << type;
	}

	return numberClauses;
}

void DimspecProblem::parseCnf(std::vector<int>& cnf, std::istream& in) {
	int literal;
	while (in >> literal) {
		cnf.push_back(literal);
	}
	// The above will abort as soon as no further number is found.
	// Therefore, we need to reset the error state of the input stream:
	in.clear();
}

void DimspecProblem::parse(std::istream& in) {
	if (in.eof()) {
		LOG(FATAL) << "Input Error: Got empty File.";
	}
	skipComments(in);
	parseCnfHeader('i', in);
	parseCnf(initial, in);
	parseCnfHeader('u', in);
	parseCnf(invariant, in);
	parseCnfHeader('g', in);
	parseCnf(goal, in);
	parseCnfHeader('t', in);
	parseCnf(transfer, in);
}