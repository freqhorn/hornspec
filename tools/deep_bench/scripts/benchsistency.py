#!/usr/bin/env python2
from __future__ import print_function
import os
import sys
from tabulate import tabulate


STD_SMT2_BENCH_DIR = "bench_horn"
STD_ICE_BENCH_DIR = "bench_horn_ice"
STD_MCMC_BENCH_DIR = "bench_horn_mcmc"
STD_ALL = [STD_SMT2_BENCH_DIR, STD_ICE_BENCH_DIR, STD_MCMC_BENCH_DIR]


class MissingRootException(Exception):
    pass


def plausible_root(path):
    for dirname in STD_ALL:
        if os.path.isdir(os.path.join(path, dirname)):
            return True
    return False


def list_benchmarks(path):
    dirname = os.path.split(path)[1].lower()
    for entry in os.listdir(path):
        if entry[0] == '.':
            continue
        if dirname == STD_SMT2_BENCH_DIR:
            name, ext = os.path.splitext(entry)
            if ext == '.smt2':
                yield name
        elif dirname == STD_ICE_BENCH_DIR:
            name, ext = os.path.splitext(entry)
            if ext == '.bpl':
                yield name
        elif dirname == STD_MCMC_BENCH_DIR:
            if os.path.isdir(path):
                yield entry
        else:
            raise ValueError("%s is of unrecognized typed" % dirname)


def main():
    root = os.getcwd()
    while not plausible_root(root):
        new_root = os.path.split(root)[0]
        if new_root == root:
            raise MissingRootException("didn't find benchmarks dirs above cwd")
        root = new_root

    found = dict((dirname, set(list_benchmarks(os.path.join(root, dirname))))
                 for dirname in STD_ALL)
    all_benchs = set.union(*found.values())

    check = u'\u2713'
    if "--ascii" in sys.argv:
        check = 'Y'
    
    sorted_keys = list(sorted(found.keys()))
    table = [[b] + [check if b in found[a] else '' for a in sorted_keys]
             for b in sorted(all_benchs)]
    print(tabulate(table, headers=[]+sorted_keys))


if __name__ == '__main__':
    main()