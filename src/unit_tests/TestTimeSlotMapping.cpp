#include "gtest/gtest.h"
#include "TimeSlotMapping.h"

TEST( SingleEndedTimePointManager, basic) {
	SingleEndedTimePointManager tpm;

	auto t0 = tpm.aquireNext();
	ASSERT_TRUE( tpm.getFirst() == t0 );
	ASSERT_TRUE( tpm.getLast() == t0 );

	auto t1 = tpm.aquireNext();
	ASSERT_TRUE( tpm.getFirst() == t0 );
	ASSERT_TRUE( tpm.getLast() == t1 );
	ASSERT_TRUE( tpm.getPredecessor(t1) == t0 );
	ASSERT_TRUE( tpm.getSuccessor(t0) == t1 );

	auto t2 = tpm.aquireNext();
	ASSERT_TRUE( tpm.getFirst() == t0 );
	ASSERT_TRUE( tpm.getLast() == t2 );
	ASSERT_TRUE( tpm.getPredecessor(t1) == t0 );
	ASSERT_TRUE( tpm.getSuccessor(t1) == t2 );
}