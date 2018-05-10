#ifndef COMMON__H
#define COMMON__H

#include <iostream>
#include <random>
#include <climits>
#include <fstream>
#include <ostream>

const unsigned int ASSERT_FAIL = 41;
const unsigned int ASSUME_FAIL = 42;
void assert(int predicate) { if (!predicate) exit(ASSERT_FAIL); }
void assume(int predicate) { if (!predicate) exit(ASSUME_FAIL); }

std::ofstream cur_ofstream;

std::vector<std::string> outputfiles;

std::ostream &
out()
{
  if(cur_ofstream) {
    return cur_ofstream;
  } else {
    return std::cerr;
  }
}

void cleanup()
{
  if (cur_ofstream) {
    cur_ofstream.close();
  }
}
/* call this after every loop to change the output filename*/
void RESET()
{
  cleanup();
  outputfiles.push_back(std::tmpnam(nullptr));
  cur_ofstream.open((outputfiles.back()).c_str(), std::ofstream::out | std::ofstream::trunc);
}

/* call this in the end to display filenames */
void FIN()
{
  cleanup();

  if (outputfiles.size() > 0) {
    std::cerr << "Output files are: " << std::endl;
    for (auto file : outputfiles) std::cerr << file << std::endl;
  }
}


unsigned int num_iter = 0;

template <typename T>
void myprint(T t)
{
  out() << t << std::endl;
  num_iter++;
}

template <typename T, typename... Args>
  void myprint(T t, Args... args)
{
  out() << t << ",";
  myprint(args...);
}

/*
#ifdef MAX_ITER
#define INIT(varlist...)					\
  auto PRINT = [&]() { if (num_iter > MAX_ITER) exit(0); out() << "1,"; myprint(varlist); };
#else
#define INIT(varlist...)					\
  auto PRINT = [&]() { out() << "1,"; myprint(varlist); };
#endif
*/

#ifdef MAX_ITER
#define PRINT(varlist...)					\
  { if (num_iter > MAX_ITER) break; out() << "1,"; myprint(varlist); }
#else
#define PRINT(varlist...)                                       \
  { out() << "1,"; myprint(varlist); }
#endif


int generateRandomInt(int min = INT_MIN, int max = INT_MAX)
{

#ifdef MIN_ITER
  if (min == 0 && max == 1 && num_iter < MIN_ITER) {
    return 1;
  }
#endif
  
  std::random_device device;
  std::default_random_engine engine(device());
  std::uniform_int_distribution<int> dist(min, max);
  return dist(engine);
}

 
#endif
