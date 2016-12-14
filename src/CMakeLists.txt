cmake_minimum_required(VERSION 2.8.12)
project(incplan)

set(CMAKE_CXX_FLAGS "-std=c++14 -O3 -Wall -Wextra -Wpedantic -pthread")
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static-libstdc++")

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/../bin)

set (CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/CMake")
include(cotire)
set (COTIRE_MINIMUM_NUMBER_OF_TARGET_SOURCES 1)

set(ipasir_lib_dir "${CMAKE_SOURCE_DIR}/../lib/ipasir")
file(GLOB ipasir_libs RELATIVE ${ipasir_lib_dir}
	${ipasir_lib_dir}/*.a
	)

include_directories(${CMAKE_SOURCE_DIR})
include_directories(${CMAKE_SOURCE_DIR}/libs)
file(WRITE ${CMAKE_BINARY_DIR}/dummy.cpp "")

add_library(all_sources incplan.cpp)
set_target_properties(all_sources PROPERTIES
	COTIRE_PREFIX_HEADER_IGNORE_PATH "${CMAKE_SOURCE_DIR}"
		_PREFIX_HEADER_INCLUDE_PATH "${CMAKE_SOURCE_DIR}/libs")
cotire(all_sources)

add_library(all_sources_extended incplan.cpp)
target_compile_definitions(all_sources_extended PRIVATE USE_EXTENDED_IPASIR=1)
set_target_properties(all_sources_extended PROPERTIES
	COTIRE_PREFIX_HEADER_IGNORE_PATH "${CMAKE_SOURCE_DIR}"
		_PREFIX_HEADER_INCLUDE_PATH "${CMAKE_SOURCE_DIR}/libs")
cotire(all_sources_extended)

add_library(ipasirdebugprint ipasirprint.cpp)
add_dependencies(all_sources ipasirdebugprint)

add_executable(incplan-heuristical dummy.cpp)
target_link_libraries(incplan-heuristical
	all_sources_extended
	${CMAKE_SOURCE_DIR}/../lib/libipasirExt_cominisatps2sun_nopre.a
	)

FOREACH(ipasir_lib ${ipasir_libs})
	string(REGEX REPLACE "libipasir(.*).a" "\\1" libname ${ipasir_lib})
	add_executable(incplan-${libname} dummy.cpp)
	target_link_libraries(incplan-${libname}
		all_sources
		${CMAKE_SOURCE_DIR}/../lib/ipasir/${ipasir_lib}
		)
ENDFOREACH()

