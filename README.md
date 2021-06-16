HornSpec
========

Non-vacuous and Maximal Specification Synthesizer for Constrained Horn clauses (CHCs). HornSpec uses an alternation of forward/backward propagation of partial solutions, Houdini-based invariant strengthening, and SyGuS-like enumeration of candidate solutions. Non-vacuous solutions are then extended to maximal solutions by SMT-based weakening. For more details, refer our PLDI'21 <a href="https://www.cs.fsu.edu/~grigory/hornspec.pdf">paper</a>.

Installation
============

Compiles with gcc-9 (on Linux) and clang1001 (on Mac). Assumes preinstalled Boost (e.g., 1.71.0) and Gmp (e.g. 10.4.0) packages. 

* `cd hornspec ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (Z3)
* `make` (again) to build HornSpec

The binary of HornSpec can be found at `build/tools/nonlin/hornspec`.
Run `build/tools/nonlin/hornspec --help` for the usage info.
Note that HornSpec comes with its own version of Z3, but can optionally use an externally installed CVC4 (at the weakening stage).

Benchmarks
==========

Collection of the SMT-LIB2 translations of the CHC systems for specification synthesis task can be found at `bench_pldi21`.

