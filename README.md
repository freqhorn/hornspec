FreqHorn
========

Satisfiability solver for constrained Horn clauses (CHC) based on the Expression library of <a href="http://seahorn.github.io/">SeaHorn</a> and the <a href="https://github.com/Z3Prover/z3">Z3</a> SMT solver. It combines probabilistic and syntax-guided methods to sample candidate invariants and checks their inductiveness / safety. Find more details at <a href="https://homes.cs.washington.edu/~grigory/freqhorn_preprint.pdf">FMCAD'17</a>.

News
========

A more efficient release (FreqHorn-2) is now available. It features a two-stage process: 1) deterministic bootstrapping with itp-based proofs of bounded safety, 2) nondeterministic sampling with the inductive subset extraction and on-demand exploiting of counterexamples-to-induction. Check the usage message for more info.

Installation
============

Compiles with gcc-5 (on Linux) and clang-700 (on Mac). Assumes preinstalled Gmp and Boost (libboost-system1.55-dev) packages.

* `cd aeval ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (Z3 and LLVM)
* `make` (again) to build FreqHorn

The binary of FreqHorn can be found at `build/tools/deep/`.
Run `./tools/deep/freqhorn --help` for the usage info.

MinimizIng Generated Invariants
========================

Solutions discovered by FreqHorn can be further minimized using the FreqHorn-IVC utility:

* `make ivc` to build FreqHorn-IVC

The binary of FreqHorn-IVC can be found at `build/tools/ivc/`.

Benchmarks
==========

Collection of the SMT-LIB2 translations of the satisfiable CHC system can be found at `bench_horn`. FreqHorn is expected to eventually discover solutions for the systems. On the other hand, there are several unsatisfiable CHC systems at `bench_horn_cex`, for which FreqHorn is expected to diverge.

Parallel Solver
===============

MPI-based version of FreqHorn can be found at the <a href="https://github.com/grigoryfedyukovich/aeval/tree/rnd-parallel-master-slave">rnd-parallel-master-slave</a> branch.

