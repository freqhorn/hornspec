#!/usr/bin/env python2
from __future__ import print_function
from collections import namedtuple
import argparse
import glob
import os


AlgoConf = namedtuple('AlgoConf', 'iters hypers')


algo_confs = {
    'mcmc': AlgoConf(3, [None]),
    'ice': AlgoConf(3, [None]),
    'z3': AlgoConf(3, ['spacerhyp1', 'spacerhyp2']),
    'freqhorn': AlgoConf(3, ['v1', 'v1-eps', 'v1-eps-freqs',
                             'v1-eps-freqs-aggp', 'aggp', 'aggp-itp3',
                             'freqs-aggp', 'freqs-aggp-itp3'])
}


def smt2_names():
    benchnames = [os.path.splitext(os.path.split(x)[1])[0]
                  for x in glob.glob("../../../bench_horn/*.smt2")]
    benchnames.sort()
    return benchnames


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-b", "--bench", type=str,
                        help="comma-sep.'d list of benchmarks to output")
    parser.add_argument("ALGOS", type=str, nargs='+')
    args = parser.parse_args()

    bench_mask = set()
    if args.bench:
        bench_mask = set(args.bench.lower().split(','))

    max_iters = max(algo_confs[x.lower()].iters for x in args.ALGOS)

    for i in range(max_iters):
        for bench in smt2_names():
            if len(bench_mask) and bench.lower() not in bench_mask:
                continue
            for algo in args.ALGOS:
                aconf = algo_confs[algo]
                if i >= aconf.iters:
                    continue
                for hyper in aconf.hypers:
                    hypflag = "" if hyper is None else "--hyper"
                    hypval = "" if hyper is None else hyper
                    out = "%s ::: %s ::: %s ::: %s ::: %d" % \
                        (hypflag, bench, algo, hypval, i)
                    print(out)
            

if __name__ == '__main__':
    main()
