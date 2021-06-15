HornSpec
========

Non-vacuous and Maximal Specification Synthesiser for constrained Horn clauses (CHCs). Based on FreqHorn, a SyGuS based satisfiability solver for CHCs. HornSpec uses a propagation based algorithm to find non-vacuous solution and then extends it to a maximal one by iteratively weakening it. For more details, refer our PLDI'21 <a href="https://www.cs.fsu.edu/~grigory/hornspec.pdf">paper</a>.

Installation
============

Compiles with gcc-5 (on Linux) and clang-900 (on Mac). Assumes preinstalled Svn, Gmp, and Boost (libboost-system1.55-dev) packages. 

* `cd hornspec ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (Z3)
* `make` (again) to build HornSpec

The binary of HornSpec can be found at `build/tools/nonlin/hornspec`.
Run `build/tools/nonlin/hornspec --help` for the usage info.

Benchmarks
==========

Collection of the SMT-LIB2 translations of the CHC systems for specification synthesis task can be found at `bench_pldi21`.

