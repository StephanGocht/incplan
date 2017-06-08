#include "PDR.h"

#include "DimspecProblem.h"
#include "ipasir/ipasir_cpp.h"
#include "carj/carj.h"
#include "carj/logging.h"

#include <memory>
#include <vector>
#include <iostream>
#include <random>

struct InferedClause {
    int activationLiteral;
    int reach;
    std::vector<int> clause;
};

class PDRSolverPIMPL {
private:
    DimspecProblem& problem;
    std::unique_ptr<ipasir::Ipasir> satSolver;
    int numHelper = 0;
    int makespan;
    int goalActivation;
    int transferActivation;

    int refines;

    std::vector<int> abstractionActivationLiteral;
    std::vector<InferedClause> inferedClauses;
    std::vector<std::vector<int>> solutions;

    std::mt19937 g;
public:
    PDRSolverPIMPL(
        DimspecProblem& _problem,
        std::unique_ptr<ipasir::Ipasir> _satSolver,
        int seed
    ):
        problem(_problem),
        satSolver(std::move(_satSolver))
    {
        g = std::mt19937(seed);
    }

    PDRSolverPIMPL(
        DimspecProblem& _problem,
        std::unique_ptr<ipasir::Ipasir> _satSolver
    ):
        PDRSolverPIMPL(
            _problem,
            std::move(_satSolver),
            std::random_device()()
        )
    {

    }

    int at(int lit, int t) {
        int offset = t * problem.numberLiteralsPerTime;
        if (lit < 0) {
            offset = -offset;
        }
        return offset + lit;
    }

    void storeSolution() {
        problem.solution = std::move(this->solutions);
        problem.storedSolutionNotifier();
    }

    bool solve(){
        initialize();
        bool solved = false;
        makespan = 0;
        refines = 0;

        LOG(INFO) << "makespan: " << makespan;
        while (!solved) {
            satSolver->assume(abstractionActivationLiteral[makespan]);
            // satSolver->assume(transferActivation);
            satSolver->assume(goalActivation);
            if (satSolver->solve() == ipasir::SolveResult::SAT) {
                std::vector<int>& solution = extractSolution(makespan);
                solved = refine(makespan, solution);
            } else {
                LOG(INFO) << "refines: " << refines;
                refines = 0;
                LOG(INFO) << "infered: " << inferedClauses.size();

                solutions.push_back(std::vector<int>());
                abstractionActivationLiteral.push_back(newHelper());
                makespan +=1;
                LOG(INFO) << "makespan: " << makespan;

                satSolver->add(abstractionActivationLiteral[makespan]);
                satSolver->add(-abstractionActivationLiteral[makespan - 1]);
                satSolver->add(0);

                pushForward();
            }
        }
        carj::getCarj().data["/incplan/result/finalMakeSpan"_json_pointer] = makespan;
        storeSolution();
        return solved;
    }

    void addGuarded(const std::vector<int>& clauses, int guard, bool atNext = false){
        if (atNext) {
            for (int lit: clauses) {
                if (lit == 0) {
                    satSolver->add(-guard);
                }
                satSolver->add(atNextTimePoint(lit));
            }
        } else {
            for (int lit: clauses) {
                if (lit == 0) {
                    satSolver->add(-guard);
                }
                satSolver->add(lit);
            }
        }

    }

    void initialize() {
        goalActivation = newHelper();
        addGuarded(problem.goal, goalActivation);
        //addGuarded(problem.goal, goalActivation, /*at next*/ true);

        transferActivation = newHelper();
        addGuarded(problem.transfer, transferActivation);
        addGuarded(problem.invariant, transferActivation);
        addGuarded(problem.invariant, transferActivation, /*at next*/ true);

        abstractionActivationLiteral.push_back(newHelper());
        addGuarded(problem.initial, abstractionActivationLiteral[0]);
        addGuarded(problem.invariant, abstractionActivationLiteral[0]);

        solutions.push_back(std::vector<int>());
    }

    std::vector<int>& extractSolution(int level) {
        std::vector<int>& result = solutions[level];
        result.clear();
        for (unsigned var = 1; var <= problem.numberLiteralsPerTime; var++) {
            result.push_back(satSolver->val(var));
        }
        return result;
    }

    int atNextTimePoint(int lit) {
        if (lit == 0) {
            return 0;
        }

        int offset = problem.numberLiteralsPerTime;
        if (lit < 0) {
            offset = -offset;
        }
        return offset + lit;
    }

    /**
     * refines the abstraction at the given leven with the given solution
     * and returns false, or returns true if the counterexample is not
     * specious
     */
    bool refine(int level, const std::vector<int>& solution) {
        refines++;
        if (level == 0) {
            return true;
        }
        level -= 1;

        while (true) {
            satSolver->assume(transferActivation);
            satSolver->assume(abstractionActivationLiteral[level]);
            for (int lit: solution) {
                satSolver->assume(atNextTimePoint(lit));
            }
            if (satSolver->solve() == ipasir::SolveResult::UNSAT) {
                extractInferedClause(level, solution);
                return false;
            } else {
                if (refine(level, extractSolution(level))) {
                    return true;
                }
            }
        }
    }

    void extractInferedClause(int level, const std::vector<int>& solution) {
        inferedClauses.push_back(InferedClause());
        InferedClause& infered = inferedClauses.back();
        infered.activationLiteral = newHelper();

        std::vector<int> clause;
        for (int lit: solution) {
            if (satSolver->failed(atNextTimePoint(lit)) == 1) {
                clause.push_back(lit);
            }
        }

        std::shuffle(clause.begin(), clause.end(), g);

        std::vector<bool> neccessary;
        neccessary.resize(clause.size());
        std::fill(neccessary.begin(), neccessary.end(), true);

        //for (int i = clause.size() - 1; i >= 0; i--) {
        for (size_t i = 0; i < clause.size(); i++) {
            if (neccessary[i]) {
                neccessary[i] = false;

                satSolver->assume(transferActivation);
                satSolver->assume(abstractionActivationLiteral[level]);
                for (size_t j = 0; j < clause.size(); j++) {
                    if (neccessary[j]) {
                        satSolver->assume(atNextTimePoint(clause[j]));
                    }
                }

                if (satSolver->solve() == ipasir::SolveResult::UNSAT) {
                    for (size_t j = 0; j < clause.size(); j++) {
                        if ((neccessary[j] == true)
                            && (satSolver->failed(atNextTimePoint(clause[j])) == 0)) {
                            neccessary[j] = false;
                        }
                    }
                } else {
                    neccessary[i] = true;
                }
            }
        }

        for (size_t i = 0; i < clause.size(); i++) {
            if (neccessary[i]) {
                infered.clause.push_back(-clause[i]);
            }
        }

        for (int lit: infered.clause) {
            satSolver->add(lit);
        }
        satSolver->add(-infered.activationLiteral);
        satSolver->add(0);

        infered.reach = 0;
        pushForward(infered);
    }

    void pushForward(){
        for (int i = 0; i < makespan; i++) {
            for (auto& infered: inferedClauses) {
                if (infered.reach == i) {
                    satSolver->assume(transferActivation);
                    satSolver->assume(abstractionActivationLiteral[i]);
                    for (int lit: infered.clause) {
                        satSolver->assume(atNextTimePoint(-lit));
                    }
                    if (satSolver->solve() == ipasir::SolveResult::UNSAT) {
                        infered.reach = i + 1;
                        satSolver->add(-abstractionActivationLiteral[infered.reach]);
                        satSolver->add(infered.activationLiteral);
                        satSolver->add(0);
                    }
                }
            }
        }
    }

    void pushForward(InferedClause& infered){
        for (int i = infered.reach; i < makespan; i++) {
            satSolver->assume(transferActivation);
            satSolver->assume(abstractionActivationLiteral[i]);
            for (int lit: infered.clause) {
                satSolver->assume(atNextTimePoint(-lit));
            }
            if (satSolver->solve() == ipasir::SolveResult::UNSAT) {
                infered.reach = i + 1;

                satSolver->add(-abstractionActivationLiteral[infered.reach]);
                satSolver->add(infered.activationLiteral);
                satSolver->add(0);
            } else {
                break;
            }
        }
    }

    int newHelper() {
        this->numHelper += 1;
        return 2 * problem.numberLiteralsPerTime + numHelper;
    }
};

PDRSolver::PDRSolver(
    DimspecProblem& _problem,
    std::unique_ptr<ipasir::Ipasir> _satSolver
):
    pimpl(new PDRSolverPIMPL(_problem, std::move(_satSolver)))
{

}

bool PDRSolver::solve(){
    return pimpl->solve();
}

PDRSolver::~PDRSolver() = default;