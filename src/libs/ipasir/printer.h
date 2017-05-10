#include <vector>
#include <iostream>

namespace ipasir {
    class Printer: public Ipasir {
    public:
        Printer() {

        }

        virtual ~Printer(){

        }

        virtual std::string signature() {
            return "ipasir-to-std-out";
        }

        virtual void add(int lit_or_zero) {
            std::cout << lit_or_zero << " ";
            if (lit_or_zero == 0) {
                std::cout << std::endl;
            }
        }

        virtual void assume(int lit) {
            assumptions.push_back(lit);
        }

        virtual SolveResult solve() {
            std::cout << "c solve({";
            for (int lit: assumptions) {
                std::cout << lit << ", ";
            }
            std::cout << "})" << std::endl;
            assumptions.clear();
            return SolveResult::UNSAT;
        }

        virtual int val(int) {
            return 0;
        }

        virtual int failed (int) {
            return 0;
        }

        virtual void set_terminate (std::function<int(void)>) {

        }

        virtual void set_learn (int, std::function<void(int*)>) {

        }

        virtual void reset() {
            assumptions.clear();
        }
    private:
        std::vector<int> assumptions;
    };
}
