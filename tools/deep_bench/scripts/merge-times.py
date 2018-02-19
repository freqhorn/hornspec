#!/usr/bin/env python
from __future__ import print_function
import os
import sys
import json
import argparse
import tarfile
from collections import defaultdict


def merge_dicts_of_lists(*args):
    m = {}
    for a in args:
        for k, v in a.iteritems():
            assert isinstance(v, list)
            m.setdefault(k, []).extend(v)
    return m


def sum_dicts_of_ints(*args):
    m = {}
    for a in args:
        for k, v in a.iteritems():
            assert isinstance(v, int)
            m[k] = m.get(k, 0) + v
    return m


def clever_load(path):
    """Given a path, will either parse it as JSON or find times.json and parse.
    """
    try:
        with tarfile.open(path, 'r') as tar:
            times_ti = None
            for tarinfo in tar:
                if os.path.split(tarinfo.name)[-1].lower() == 'times.json':
                    assert times_ti is None
                    assert tarinfo.isfile()
                    times_ti = tarinfo
            return json.load(tar.extractfile(times_ti))
    except Exception:
        import traceback
        traceback.print_exc()
        pass

    with open(path, 'r') as f:
        return json.load(f)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("PATHS", nargs='+')
    args = parser.parse_args()

    merged = {'times': defaultdict(lambda: defaultdict(list)),
              'iterCnts': defaultdict(lambda: defaultdict(list)),
              'unsuccessCnts': defaultdict(lambda: defaultdict(lambda: 0))}
    for path in args.PATHS:
        obj = clever_load(path)
        for category in ['iterCnts', 'times']:
            for smttask in obj[category]:
                for hyperstr, contents in obj[category][smttask].iteritems():
                    merged[category][smttask][hyperstr].extend(contents)
        for smttask in obj['unsuccessCnts']:
            if isinstance(obj['unsuccessCnts'][smttask], int):
                print("old-style unsuccessCnts; skipping", file=sys.stderr)
                break
            for hyperstr in obj['unsuccessCnts'][smttask]:
                val = obj['unsuccessCnts'][smttask][hyperstr]
                merged['unsuccessCnts'][smttask][hyperstr] += val
    if len(merged['unsuccessCnts']) == 0:
        del merged['unsuccessCnts']
    json.dump(merged, sys.stdout)


if __name__ == '__main__':
    main()
