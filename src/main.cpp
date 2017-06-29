#include <iostream>

int incplan_main(int argc, const char **argv);

int main(int argc, const char **argv) {
	try {
		return incplan_main(argc, argv);
	} catch (const std::exception& e) {
		std::cerr << "Terminated due to exception: " << std::endl;
		std::cerr << e.what() << std::endl;
	} catch (char const* c) {
		std::cerr << "Terminated due to exception: " << std::endl;
		std::cerr << c << std::endl;
	} catch (...) {
		std::cerr << "Terminated due to unknown exception." << std::endl;
	}
	return 1;
}