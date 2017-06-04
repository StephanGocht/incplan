#pragma once

#include "DimspecProblem.h"
#include "ipasir/ipasir_cpp.h"

#include <memory>

class PDRSolverPIMPL;

class PDRSolver {
public:
    PDRSolver(
        const DimspecProblem& _problem,
        std::unique_ptr<ipasir::Ipasir> _satSolver
    );
    void printSolution(bool solverLike);
    bool solve();
    virtual ~PDRSolver();

private:
    std::unique_ptr<PDRSolverPIMPL> pimpl;
};