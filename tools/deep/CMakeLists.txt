add_executable (freqhorn DeepHorn.cpp)
target_link_libraries (freqhorn ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB} ${ARMADILLO_LIBRARIES})
llvm_config (freqhorn bitwriter)
install(TARGETS freqhorn RUNTIME DESTINATION bin)
