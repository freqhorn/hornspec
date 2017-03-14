#include "ae/AeValSolver.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace ufo;

/** An AE-VAL wrapper for cmd
 *
 * Usage: specify 2 smt2-files that describe the formula \foral x. S(x) => \exists y . T (x, y)
 *   <s_part.smt2> = S-part (over x)
 *   <t_part.smt2> = T-part (over x, y)
 *
 * Notably, the tool automatically recognizes x and y based on their appearances in S or T.
 *
 * Example:
 *
 * ./tools/aeval/aeval
 *   ../test/ae/example1_s_part.smt2
 *   ../test/ae/example1_t_part.smt2
 *
 */

int main (int argc, char ** argv)
{

  ExprFactory efac;
  EZ3 z3(efac);

  ExprVector params;

  if (argc != 3)
  {
    outs() << "Unable to parse arguments\n";
    return 0;
  }

  aeSolveAndSkolemize(z3_from_smtlib_file (z3, argv [1]),
                      z3_from_smtlib_file (z3, argv [2]));

  return 0;
}
