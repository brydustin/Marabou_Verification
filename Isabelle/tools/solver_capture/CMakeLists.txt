cmake_minimum_required(VERSION 3.16)
project(MarabouSolverCapture LANGUAGES CXX)

# Build the actual native engine from the pinned, untouched source tree.
# This embedding excludes CLI/network parsers and their ONNX dependencies.
# It does not replace engine methods, factories, arithmetic, or proof production.
get_filename_component(PROJECT_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../../.." ABSOLUTE)
set(MARABOU_SOURCE "${PROJECT_ROOT}/upstream/Marabou" CACHE PATH "Marabou checkout")
set(LOCAL_DEP_PREFIX "${PROJECT_ROOT}/Isabelle/generated/solver_deps/root"
    CACHE PATH "Optional extracted system packages")
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
find_package(Threads REQUIRED)
find_library(GMP_LIBRARY NAMES gmp REQUIRED)
find_library(GMPXX_LIBRARY NAMES gmpxx REQUIRED)
find_library(BOOST_PROGRAM_OPTIONS_LIBRARY
    NAMES boost_program_options libboost_program_options.so.1.83.0
    PATHS "${LOCAL_DEP_PREFIX}/usr/lib/x86_64-linux-gnu" REQUIRED)
find_library(BOOST_THREAD_LIBRARY NAMES boost_thread libboost_thread.so.1.83.0 REQUIRED)
find_library(BOOST_CHRONO_LIBRARY
    NAMES boost_chrono libboost_chrono.so.1.83.0
    PATHS "${LOCAL_DEP_PREFIX}/usr/lib/x86_64-linux-gnu" REQUIRED)

set(ENGINE_SOURCES "")
foreach(part common common/real configuration engine engine/real basis_factorization proofs nlr)
    file(GLOB PART_SOURCES CONFIGURE_DEPENDS "${MARABOU_SOURCE}/src/${part}/*.cpp")
    list(APPEND ENGINE_SOURCES ${PART_SOURCES})
endforeach()
list(FILTER ENGINE_SOURCES EXCLUDE REGEX "/(main|Marabou|MarabouMain|DnCMarabou|DnCManager|DnCWorker)\\.cpp$")
file(GLOB CONTEXT_SOURCES CONFIGURE_DEPENDS
    "${MARABOU_SOURCE}/deps/CVC4/context/*.cpp"
    "${MARABOU_SOURCE}/deps/CVC4/base/*.cpp")

add_executable(marabou_solver_capture
    capture.cpp ${ENGINE_SOURCES} ${CONTEXT_SOURCES})
foreach(part common configuration engine basis_factorization proofs nlr)
    target_include_directories(marabou_solver_capture PRIVATE "${MARABOU_SOURCE}/src/${part}")
endforeach()
target_include_directories(marabou_solver_capture PRIVATE
    "${MARABOU_SOURCE}/deps/CVC4" "${MARABOU_SOURCE}/deps/CVC4/include"
    "${MARABOU_SOURCE}/tools/cxxtest")
target_compile_definitions(marabou_solver_capture PRIVATE BOOST_NO_CXX98_FUNCTION_BASE)
target_compile_options(marabou_solver_capture PRIVATE -O1 -ffunction-sections -fdata-sections)
target_link_options(marabou_solver_capture PRIVATE -Wl,--gc-sections)
target_link_libraries(marabou_solver_capture PRIVATE
    ${BOOST_PROGRAM_OPTIONS_LIBRARY} ${BOOST_THREAD_LIBRARY} ${BOOST_CHRONO_LIBRARY}
    ${GMPXX_LIBRARY} ${GMP_LIBRARY} Threads::Threads)
