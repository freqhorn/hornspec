#ifndef DATALEARNER__HPP__
#define DATALEARNER__HPP__

// currently only polynomials upto degree 2 is supported

#include <cstdlib>
#include <cstdio>
#include <fstream>
#include <vector>
#include <climits>
#include <ctime>

#include "armadillo"

#include "Horn.hpp"
#include "BndExpl.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

  const double approxEqualTol = 0.001;
  const char approxEqualMethod[] = "absdiff";

  enum loglevel {NONE, ERROR, INFO, DEBUG};

  unsigned int LOG_LEVEL = INFO;

  template <typename T>
  void printmsg(T t)
  {
    std::cout << t << std::endl;
  }

  template <typename T, typename... Args>
  void printmsg(T t, Args... args)
  {
    std::cout << t << " ";
    printmsg(args...);
  }

  template <typename... Args>
  void printmsg(loglevel level, Args... args)
  {
    if (level <= LOG_LEVEL) {
      printmsg(args...);
    }
  }

  //if multipleloops then executes entire program once and caches models of all inductive relations
  class loadDataFromSMTHelper
  {
  private:
    static loadDataFromSMTHelper * ptr;
    map <Expr, vector< vector<int> > > exprToModels;
    loadDataFromSMTHelper() {}

    bool
    executeEntireProgram(CHCs & rm, ufo::ZSolver<ufo::EZ3> & solver)
    {
      BndExpl bnd(rm);
      return bnd.unrollAndExecuteMultiple(solver, exprToModels);
    }

    bool
    exprModels(const Expr & inv, vector< vector<int> > & models)
    {
      auto itr = exprToModels.find(inv);
      if (itr == exprToModels.end()) {
	return false;
      } else {
	for (auto model : itr->second) {
	  models.push_back(model);
	}
	return true;
      }
    }

  public:
    static bool
    getModels(bool multipleLoops, const Expr & inv, CHCs & rm,
	      ufo::ZSolver<ufo::EZ3> & solver, vector< vector<int> > & models)
    {
      if (ptr == nullptr) {
	ptr = new loadDataFromSMTHelper();
	if (multipleLoops && !(ptr->executeEntireProgram(rm, solver))) {
	  return false;
	}
      }

      if(multipleLoops) {
	return ptr->exprModels(inv, models);
      } else {
	BndExpl bnd(rm);
	return bnd.unrollAndExecute(inv, solver, models);
      }
    }
    
  };
  class DataLearner
  {
    
  private:

    struct armaApproxEqual
    {
      bool operator() (const double & a, const double & b) const {
	if (!arma::approx_equal(arma::vec(1).fill(a), arma::vec(1).fill(b),
				approxEqualMethod, approxEqualTol)) {
	  return (a < b);
	}
	return false;	     
      }
    };

    CHCs& ruleManager;
    ExprFactory &m_efac;
    ufo::ZSolver<ufo::EZ3> m_smt_solver;

    Expr inv;
    bool multipleLoops;
    unsigned int numVars;
    int trIndex;
    arma::mat dataMatrix;
    unsigned int prevDataSize;
    
    unsigned int curPolyDegree;
    unsigned int maxPolyCompute[3];
    unsigned int numPolyCompute;

    map<unsigned int, Expr> monomialToExpr;

    map<double, Expr, armaApproxEqual> largeCoeffToExpr;

    ExprSet polynomialsComputed;
    vector<arma::mat> basisComputed;

    // return nonzero on error
    int
    loadDataFromFile(const std::string & fileName)
    {
      dataMatrix.load(fileName, arma::csv_ascii);

      if (dataMatrix.n_cols != numVars+1) {
	printmsg(ERROR, "data load failed from ", fileName);
	printmsg(INFO, "vars: ", numVars, "\ncolumns read: ", dataMatrix.n_cols);
	dataMatrix.clear();
	return 1;
      }

      printmsg(DEBUG, "vars: ", numVars, "\n row x col ", dataMatrix.n_rows, dataMatrix.n_cols);
      
      return 0;
    }

    arma::mat
    computeMonomial(arma::mat data)
    {
      arma::mat monomialMatrix;
      monomialMatrix.fill(0);
      if (curPolyDegree == 1) {
	monomialMatrix.set_size(dataMatrix.n_rows, dataMatrix.n_cols);
	for (int i = 0; i < dataMatrix.n_rows; i++) {
	  for (int j = 0; j < dataMatrix.n_cols; j++) {
	    monomialMatrix(i,j) = dataMatrix(i,j);
	  }
	}
      } else {
     	//compute all monomials upto degree 2
	monomialMatrix.set_size(dataMatrix.n_rows, (dataMatrix.n_cols * (dataMatrix.n_cols+1)) / 2);
	for (int i = 0; i < dataMatrix.n_rows; i++) {
	  for(int j = 0, dmcol=0; j < dataMatrix.n_cols; j++) {
	    for (int k = j; k < dataMatrix.n_cols; k++, dmcol++) {
	      monomialMatrix(i, dmcol) = dataMatrix(i,j) * dataMatrix(i, k);
	    }
	  }
	}
      }

      return monomialMatrix;
    }
    
    arma::mat
    gaussjordan(arma::mat input)
    {
      unsigned int cur_row = 0;
      unsigned int cur_col = 0;
      arma::vec rowToPivot = arma::vec(input.n_rows);
      const unsigned int UNDEFINED_PIVOT = 100;

      rowToPivot.fill(UNDEFINED_PIVOT);

      printmsg(DEBUG, "Before row\n", input);

      //row echleon form
      while (cur_col < input.n_cols && cur_row < input.n_rows) {

	if (input(cur_row, cur_col) == 0) {
	  unsigned int next_nonzero;
	  for (next_nonzero = cur_row; next_nonzero < input.n_rows; next_nonzero++) {
	    if (input(next_nonzero, cur_col) != 0) {
	      break;
	    }
	  }
	  if (next_nonzero == input.n_rows) {
	    cur_col++;
	    continue;
	  } else {
	    input.swap_rows(cur_row, next_nonzero);
	  }
	}

	if (input(cur_row, cur_col) != 1) {
	  double inverse = 1/input(cur_row, cur_col);
	  for (unsigned int k = cur_col; k < input.n_cols; k++) {
	    input(cur_row, k) = input(cur_row,k)*inverse;
	  }
	}
    
	for (unsigned int j = cur_row+1; j < input.n_rows; j++) {
	  double f = input(j, cur_col)/input(cur_row, cur_col);
	  for (unsigned int k = 0; k < input.n_cols; k++) {
	    input(j,k) = input(j,k) - input(cur_row, k)*f;
	  }
	  input(j,cur_col) = 0;
	}

	rowToPivot(cur_row) = cur_col;
    
	cur_col++;
	cur_row++;
      }

      rowToPivot(input.n_rows-1) = input.n_cols-1;

      //reduced row echloen form
      if (cur_row != input.n_rows) {
	//we have found a zero row before we reached last row
	cur_row = cur_row-1;
      } else {
	cur_row = input.n_rows-1;
      }
      
      cur_col = rowToPivot(cur_row);

      while (cur_row < input.n_rows) {

	cur_col = rowToPivot(cur_row);

	if (cur_col == UNDEFINED_PIVOT || input(cur_row,cur_col) == 0) {
	  cur_row--;
	  continue;
	}
    
	for (unsigned int j = cur_row-1; j < input.n_rows; j--) {
	  double f = input(j,cur_col)/input(cur_row,cur_col);
	  for (unsigned int k = 0; k < input.n_cols; k++) {
	    input(j,k) = input(j,k) - input(cur_row,k)*f;
	  }
	}
	cur_row--;
      }	    

      //      printmsg(INFO, "after row reduced\n", input);
      
      std::vector<unsigned int> independentVars;
      
      for (unsigned col = 0; col < input.n_cols; col++) {
	if (col < input.n_rows && input(col, col) == 0) {
	  independentVars.push_back(col);
	}
      }
	  
      arma::mat basis(input.n_cols, independentVars.size());
      basis.fill(0);
      unsigned int basis_col = 0;
  
      for (auto indVar : independentVars) {
	for (unsigned int row = 0; row < input.n_rows; row++) {
	  if (rowToPivot[row] == UNDEFINED_PIVOT) {
	    continue;
	  }
	  //TODO: replace -2 with lcm of column
	  //printmsg(DEBUG, input(row,indVar), row, indVar);
	  basis(rowToPivot(row), basis_col) = -1*input(row, indVar);
	}
	basis(indVar,basis_col)=1;
	basis_col++;
      }
  
      return basis;
    }

    void
    computetime(const string & msg, clock_t & start)
    {
      printmsg(DEBUG, msg, (clock() - start)/(CLOCKS_PER_SEC/1000.0));
      start = clock();
    }
    
    bool
    allowedPolyCoefficient(double val, Expr & coeffExpr)
    {
      //arma may not store exact 0 as val
      if (arma::approx_equal(arma::vec(1).fill(0), arma::vec(1).fill(val),
			     approxEqualMethod, approxEqualTol)) {
	return false;
      }

      auto search = largeCoeffToExpr.find(val);
      if (search != largeCoeffToExpr.end()) {
	coeffExpr = search->second;
	//	printmsg(DEBUG, "coefficient ", coeffExpr);
	return true;
      }

      if (val < 10000 && val > -10000) {
	return true;
      }
	
      return false;
    }

    int
    algExprFromBasis(const arma::mat & basis, vector<Expr> & polynomials)
    {

      /*TODO: fix this; not working for 8.c*/
      // if (arma::all(arma::vectorise(basis))) {
      // 	return 1;
      // }

      // create equations of the form a_1*x_1 + a_2*x_2 + ... = 0
      // where a_1, a_2, etc are from basis columns values
      // and x_1, x_2 etc are monomials from corresponding basis' rows
      // to disallow unsound invariants like a_1 = 0 add only candidates with atleast two terms
      Expr zero = mkTerm(mpz_class(0), m_efac);
      for (int col = 0; col < basis.n_cols; col++) {
	int numTerms = 0;
	Expr poly = nullptr;
	for (int row = 0; row < basis.n_rows; row++) {
	  //coeffcient is stored in a stream first to avoid incorrect type conversion error
	  std::stringstream coeffStream;
	  coeffStream << std::fixed << basis(row,col);

	  Expr abstractVar = nullptr;
          if (!allowedPolyCoefficient(basis(row,col), abstractVar)) {
            continue;
          }

          Expr mult;
          Expr monomialExpr = monomialToExpr[row];
          if (abstractVar != nullptr && (isNumericConst(monomialExpr) || curPolyDegree > 1)) {
            if (!isNumericConst(monomialExpr)) {
              mult = mk<MULT>(abstractVar, monomialExpr);
            } else {
              int monomialInt = lexical_cast<int>(monomialExpr);
              //assumption is that abstractVar will be of the form intConst * var or var * intConst                                            
              bool success = true;
              Expr var = nullptr;
              int varCoeff = 1;
              if (!isOpX<MULT>(abstractVar)) {
                success = false;
              } else {
                for (auto it = abstractVar->args_begin(), end = abstractVar->args_end(); it != end; ++it) {
                  if (isNumericConst(*it)) {
                    varCoeff = lexical_cast<int>(*it);
                  } else if (bind::isIntConst(*it)) {
                    var = *it;
                  } else {
                    success = false;
                  }
                }
              }
              if (!success || var == nullptr) {
                mult = mk<MULT>(abstractVar, monomialExpr);
              } else {
                mult = mk<MULT>(mkTerm(mpz_class(varCoeff*monomialInt), m_efac), var);
              }
	    }
	  } else {
	    int coeff;
	    coeffStream >> coeff;
	    mult = mk<MULT>(mkTerm(mpz_class(coeff), m_efac), monomialToExpr[row]);
	  }
	  
	  if (poly != nullptr) {
	    poly = mk<PLUS>(poly, mult);
	  } else {
	    poly = mult;
	  }
	  
	  numTerms++;
	}
	
	if (poly != nullptr && numTerms > 1) {
	  poly = mk<EQ>(poly, zero);
	  polynomials.push_back(poly);
	}
      }
      
      return 0;
    }

    void
    addpolytocands(ExprSet & cands, Expr poly)
    {
      cands.insert(poly);
    }

    void
    addpolytocands(ExprVector & cands, Expr poly)
    {
      cands.push_back(poly);
    }

    void
    initTrIndex(Expr invDecl)
    {
      for (int i = 0; i < ruleManager.chcs.size(); i++) {
	auto & r = ruleManager.chcs[i];
	if (r.isInductive && r.srcRelation == invDecl && r.dstRelation == invDecl) {
	  trIndex = i;
	}
      }
    }
    
    void
    initInvVars(Expr invDecl)
    {
      monomialToExpr.insert(pair<unsigned int, Expr>(0, mkTerm(mpz_class(1), m_efac)));
      
      //      Expr arg = invDecl->arg(0);
      for (auto var : ruleManager.invVars[invDecl]) {
	numVars++;
	monomialToExpr.insert(pair<unsigned int, Expr>(numVars, var));
      }

      //degree 2 monomials
      for (unsigned int vIndex1 = 1, mIndex = numVars+1; vIndex1 <= numVars; vIndex1++) {
	for (int vIndex2 = vIndex1; vIndex2 <= numVars; vIndex2++) {
	  monomialToExpr.insert(std::pair<unsigned int, Expr>(mIndex,
							    mk<MULT>(monomialToExpr[vIndex1],
								     monomialToExpr[vIndex2])));
	  mIndex++;
	}
      }
      
    }

    // adds monomial and constant multiples of it if corresponding
    // monomial column in datamatrix is constant
    void
    initLargeCoeffToExpr()
    {
      // first column is 1's
      for (unsigned int col = 1; col < dataMatrix.n_cols; col++) {

	double tmp = dataMatrix(0, col);
	unsigned int row;

	for (row = 1; row < dataMatrix.n_rows; row++) {
	  if (!arma::approx_equal(arma::vec(1).fill(dataMatrix(row, col)), arma::vec(1).fill(tmp),
				  approxEqualMethod, approxEqualTol)) {
	      break;
	    }
	}

	if (row != dataMatrix.n_rows) {
	  continue;
	}

	Expr var = monomialToExpr[col];
	for (int multiple = 1; multiple < 4; multiple++) {
	  Expr val1 = mk<MULT>(mkTerm(mpz_class(multiple), m_efac), var);
	  Expr val2 = mk<MULT>(mkTerm(mpz_class(-1*multiple), m_efac), var);
	  largeCoeffToExpr.insert(make_pair(multiple*tmp, val1));
	  largeCoeffToExpr.insert(make_pair(-1*multiple*tmp, val2));
	}
	
      }
    }

    
    Expr
    modelToExpr(vector<int> model)
    {
      ExprVector eqs;
      for (unsigned int index = 0; index < model.size(); index++) {
	Expr var = monomialToExpr[index+1];
	eqs.push_back(mk<EQ>(var, mkTerm(mpz_class(model[index]), m_efac)));
      }
      
      return conjoin(eqs, m_efac);
    }
    
    // return true only if all the data satisfies basis
    bool
    checkBasisSatisfiesData(arma::mat monomial, arma::vec basis)
    {
      if (monomial.n_cols != basis.n_elem) {
	return false;
      }

      arma::rowvec basisRow = arma::conv_to<arma::rowvec>::from(basis);
      
      for (int row = 0; row < monomial.n_rows; row++) {
	double sum = 0;
	for (int col = 0; col < monomial.n_cols; col++) {
	  sum += basisRow(col) * monomial(row, col);
	}
	if (!arma::approx_equal(arma::vec(1).fill(sum), arma::vec(1).fill(0),
				approxEqualMethod, approxEqualTol)) {
	  return false;
	}
      }

      return true;
	
    }
    
    template <class CONTAINERT>
    int
    getPolynomialsFromData(const arma::mat & data, CONTAINERT & cands, Expr assume = nullptr)
    {
      if (data.n_elem == 0) {
	return -1;
      }
      
      clock_t start = clock();

      arma::mat monomialMatrix = computeMonomial(data);

      arma::mat basis = gaussjordan(monomialMatrix);

      //      printmsg(INFO, "before basis check ", basis);

      if (basis.n_cols == 0) {
	return 0;
      }

      //      cout << endl << basis << endl; //DEBUG
      
      computetime("basis computation time ", start);

      // check if column of basis is unique
      if (assume == nullptr) {
	for (int col = 0; col < basis.n_cols; col++) {
	  int oldcol;
	  for (oldcol = 0; oldcol < basisComputed[curPolyDegree].n_cols; oldcol++) {
	    if (arma::approx_equal(basis.col(col), basisComputed[curPolyDegree].col(oldcol),
				   approxEqualMethod, approxEqualTol)) {
	      basis.shed_col(col);
	      break;
	    } 
	  }
	}
	
	for (int col = 0; col < basis.n_cols; col++) {
	  basisComputed[curPolyDegree].insert_cols(basisComputed[curPolyDegree].n_cols, basis.col(col));
	}
      }

      computetime("data unique check time ", start);
      
      // for some reason previous monomialmatrix is overwritten so copy to a different matrix
      arma::mat monomialMatrix2 = computeMonomial(data);
      for (int col = 0; col < basis.n_cols; col++) {
	if (!checkBasisSatisfiesData(monomialMatrix2, basis.col(col))) {
	  basis.shed_col(col);
	  continue;
	}

      }

      // if (assume != nullptr) {
      // 	printmsg(INFO, "\n dataMatrix \n", dataMatrix);
      // 	printmsg(INFO, "\n data \n", data);
      // 	printmsg(INFO, "\n monomial \n", monomialMatrix);
      // 	printmsg(INFO, "\n basis \n", basis);
      // }
      
      vector<Expr> polynomials;
      polynomials.reserve(basis.n_cols);
      
      if (!algExprFromBasis(basis, polynomials)) {
	for (auto poly : polynomials) {
	  Expr cand = (assume == nullptr) ? poly : mk<IMPL>(assume, poly);
	  if (polynomialsComputed.find(cand) == polynomialsComputed.end()) {
	    addpolytocands(cands, cand);
	    polynomialsComputed.insert(cand);
	    printmsg(DEBUG, "Adding polynomial: ", cand);
	  }
	}

	computetime("poly conversion time ", start);
	
	return polynomials.size();
      }

      return 0;

    }

        //non-zero on error
    int 
    loadDataFromSMT()
    {
      vector<vector<int> > models;
      printmsg(DEBUG, "Unrolling and solving via SMT");
      if (!loadDataFromSMTHelper::getModels(multipleLoops, inv, ruleManager, m_smt_solver, models)) {
	return 1;
      }

      for (auto model : models) {
	arma::rowvec row = arma::conv_to<arma::rowvec>::from(model);
	row.insert_cols(0, arma::rowvec(1, arma::fill::ones));
	dataMatrix.insert_rows(dataMatrix.n_rows, row);
      }

      //      cout << dataMatrix << endl; //DEBUG
      
      return 0;
      
    }

  public:
    
    DataLearner(CHCs& r, EZ3 &z3) :
      ruleManager(r), m_smt_solver(z3), m_efac(r.m_efac), trIndex(-1), numVars(0),
      curPolyDegree(1), numPolyCompute(0), prevDataSize(0)
    {
      multipleLoops = false;
      maxPolyCompute[1] = 5;
      maxPolyCompute[2] = numeric_limits<unsigned int>::max();
      //to let index start from 1
      basisComputed.push_back(arma::mat());
      basisComputed.push_back(arma::mat());
    }


    void
    setLogLevel(unsigned int l)
    {
      LOG_LEVEL = l;
    }


    void
    initialize(Expr invDecl, bool multiLoop = false, unsigned int loglevel = 2)
    {
      //      cout << *invDecl << endl;
      inv = invDecl;
      multipleLoops = multiLoop;
      setLogLevel(loglevel);
      //      initTrIndex(invDecl);
      initInvVars(invDecl);
    }

    // NOTE: should be called after initialize()
    bool
    computeData(const std::string & dataFile)
    {

      assert(numVars != 0);
      if (!multipleLoops && trIndex == -1) {
	printmsg(ERROR, "Relation without inductive clauses are not supported yet");
	return false;
      }

      if (dataFile.empty()) {
	if (loadDataFromSMT() != 0) {
	  printmsg(INFO, "failed to load data from smt (also no input file)");
	  return false;
	}
      } else {
	if (loadDataFromFile(dataFile) != 0) {
	  printmsg(ERROR, "failed to load data from file ", dataFile);
	  return false;
	}
      }
            
      initLargeCoeffToExpr();
      
      return true;
    }

    // Implementation of "A Data Driven Approach for Algebraic Loop Invariants", Sharma et al.
    // return number of candidate polynomials added (< 0 in case of error)
    template <class CONTAINERT>
    int
    computePolynomials(CONTAINERT & cands)
    {

      if (!multipleLoops && trIndex == -1) {
	printmsg(ERROR, "Relations without inductive clauses are not supported yet");
	return -1;
      }

      numPolyCompute++;

      if (numPolyCompute > maxPolyCompute[curPolyDegree]) {
	curPolyDegree++;
	basisComputed.push_back(arma::mat());
      }

      int retVal = getPolynomialsFromData(dataMatrix, cands);
      prevDataSize = dataMatrix.n_rows;
      return retVal;
    }

    void
    incPolyDegree()
    {
      if (curPolyDegree < 2) {
	curPolyDegree++;
	basisComputed.push_back(arma::mat());
      }
    }
    
    // adds a unique row
    void
    updateData(vector<int> data)
    {
      return ;
      
      arma::rowvec dataRow(data.size() + 1);
      dataRow(0) = 1;
      for (int i = 0; i < data.size(); i++) {
	dataRow(i+1) = data[i];
      }

      for (unsigned int i = 0; i < dataMatrix.n_rows; i++) {
	if (arma::approx_equal(dataMatrix.row(i), dataRow, approxEqualMethod, approxEqualTol)) {
	  return;
	}
      }
      
      dataMatrix.insert_rows(dataMatrix.n_rows, dataRow);

    }

  };

  loadDataFromSMTHelper * loadDataFromSMTHelper::ptr = nullptr;
}


#endif
