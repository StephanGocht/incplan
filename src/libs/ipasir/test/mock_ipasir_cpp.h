#pragma once
#include "gmock/gmock.h"
#include "ipasir/ipasir_cpp.h"

namespace ipasir {
class MockIpasir: public Ipasir {
public:
	MOCK_METHOD0(ipasir_signature, std::string ());
	MOCK_METHOD1(add, void (int lit_or_zero));
	MOCK_METHOD1(assume, void (int lit));
	MOCK_METHOD0(solve, ipasir::SolveResult ());
	MOCK_METHOD1(val, int (int lit));
	MOCK_METHOD1(failed, int  (int lit));
	MOCK_METHOD1(set_terminate, void  (std::function<int(void)> callback));
	MOCK_METHOD0(reset, void ());
};
}