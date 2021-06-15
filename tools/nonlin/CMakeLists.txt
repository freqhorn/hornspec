add_executable (hornspec NonlinSolver.cpp)
target_link_libraries (hornspec ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
install(TARGETS hornspec RUNTIME DESTINATION bin)
