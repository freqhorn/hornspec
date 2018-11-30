add_executable (modver NonlinSolver.cpp)
target_link_libraries (modver ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
llvm_config (modver bitwriter)
install(TARGETS modver RUNTIME DESTINATION bin)
