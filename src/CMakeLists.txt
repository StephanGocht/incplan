cmake_minimum_required(VERSION 2.8)
project(incplan)

set(CMAKE_CXX_FLAGS "-std=c++14 -g -Wall -Wextra -Wpedantic")
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static-libstdc++")

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/../bin)

set(ipasir_lib_dir "${CMAKE_SOURCE_DIR}/../lib/ipasir")

file(GLOB ipasir_libs RELATIVE ${ipasir_lib_dir}
	${ipasir_lib_dir}/*.a
	)

include_directories(${CMAKE_SOURCE_DIR})
file(WRITE ${CMAKE_BINARY_DIR}/dummy.cpp "")

add_library(all_sources incplan.cpp)
add_library(ipasirdebugprint ipasirprint.cpp)

FOREACH(ipasir_lib ${ipasir_libs})
	string(REGEX REPLACE "libipasir(.*).a" "\\1" libname ${ipasir_lib})
	add_executable(incplan-${libname} dummy.cpp)
	target_link_libraries(incplan-${libname}
		all_sources
		${CMAKE_SOURCE_DIR}/../lib/ipasir/${ipasir_lib}
		)
ENDFOREACH()

