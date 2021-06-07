add_executable (freqn NonlinSolver.cpp)
target_link_libraries (freqn ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
install(TARGETS freqn RUNTIME DESTINATION bin)
