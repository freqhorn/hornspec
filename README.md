#About#

Skolemizer for AE-formulas in LIA/LRA based on the <a href="http://seahorn.github.io/">SeaHorn</a> verification framework and the <a href="https://github.com/Z3Prover/z3">Z3</a> SMT solver. This is the main computational engine used in the Incremental Model Checking (<a href="http://www.inf.usi.ch/phd/fedyukovich/simabs_paper.pdf">LPAR'15</a>, <a href="http://www.inf.usi.ch/phd/fedyukovich/pde_paper.pdf">CAV'16</a>) and in the Program Synthesis from Assume-Guarantee contracts (<a href="https://arxiv.org/abs/1610.05867">preprint</a>).

#Installation#

* `cd aeval ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (Z3 and LLVM)
* `make` to build AE-VAL

The binary of AE-VAL can be found in `build/tools/aeval/`

