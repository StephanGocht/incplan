#pragma once

#include "DimspecProblem.h"
#include "ipasir/ipasir_cpp.h"

#include <memory>

class PDRSolverPIMPL;

class PDRSolver {
public:
    PDRSolver(
        DimspecProblem& _problem,
        std::unique_ptr<ipasir::Ipasir> _satSolver
    );
    bool solve();
    virtual ~PDRSolver();

private:
    std::unique_ptr<PDRSolverPIMPL> pimpl;
};