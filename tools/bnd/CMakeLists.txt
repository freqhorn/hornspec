add_executable (expl BoundedExplorer.cpp)
target_link_libraries (expl ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
llvm_config (expl bitwriter)
install(TARGETS expl RUNTIME DESTINATION bin)
