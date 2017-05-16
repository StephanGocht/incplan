#include <vector>
#include <set>
#include <map>
#include <iostream>

class DimspecProblem {
public:
	DimspecProblem(std::istream& in);

	std::vector<int> initial, invariant, goal , transfer;
	unsigned numberLiteralsPerTime;
	std::vector<int> actionVariables;
	std::vector<int> stateVariables;
	std::map<int, std::vector<int>> support;

private:
	void inferAdditionalInformation();
	void skipComments(std::istream& in);
	int parseCnfHeader(char expectedType, std::istream& in);
	void parseCnf(std::vector<int>& cnf, std::istream& in);
	void parse(std::istream& in);
};