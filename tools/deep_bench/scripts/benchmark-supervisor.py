#!/usr/bin/env python2
from __future__ import print_function
import os
import re
import sys
import glob
import json
import time
import argparse
import subprocess32
import traceback
import tempfile
from functools import reduce
from collections import defaultdict, namedtuple
from datetime import datetime, tzinfo, timedelta


class simple_utc(tzinfo):
    def tzname(self,**kwargs):
        return "UTC"
    def utcoffset(self, dt):
        return timedelta(0)


ONE_MIN = 1 * 60  # in seconds
TOTAL_TIME_RE = re.compile(r'\s*[tT]otal [tT]ime:?\s+([\.0-9]*)\s*')
BOOGIE_RESULTS_RE = re.compile(r'\s*Boogie program verifier finished with [^0]\d* verified, 0 errors.*')
FREQHORN_ITER_LIMIT_RE = re.compile(r'\s*No success after (\d+) iterations\s*')
FREQHORN_V1_RE = re.compile(r'\s*\-+>\s*Success after (\d+) iterations\s*')
FREQHORN_V2_BOOT_RE = re.compile(r'\s*Success after (.+?\s+)?bootstrapping\s*')
FREQHORN_V2_SAMPLING_RE = re.compile(r'\s*Success after (.+?\s+)?sampling\s*')

RunResult = namedtuple('RunResult', 'reported_time proc_time iters success_kind')


class NoSuccessException(Exception):
    pass

class IterLimitHitException(NoSuccessException):
    def __init__(self, msg, iters=None):
        super(IterLimitHitException, self).__init__(msg)
        self.iters = iters


def win_path(orig):
    if 'SYSTEMDRIVE' in os.environ:
        # we're in Cygwin
        pfx = '/cygdrive/c'
        assert orig.startswith(pfx)
        return os.environ['SYSTEMDRIVE'] + orig[len(pfx):].replace("/", '\\')
    else:
        return orig


def subproc_check_output(*args, **kwargs):
    """`subprocess32.check_output` but stdout/-err is always logged to disk.
    
    `logfile` keyword arg is a path to the log file. All other arguments,
    keyword and otherwise, are passed through to `check_output`.
    """
    if 'stderr' not in kwargs:
        kwargs['stderr'] = subprocess32.STDOUT
    
    log_path = kwargs.pop('logfile', None)
    if log_path:
        fo = open(log_path, 'w')
    else:
        fo = open(os.devnull, 'w')
    
    output = ''
    try:
        output = subprocess32.check_output(*args, **kwargs)
    except Exception as e:
        if hasattr(e, 'output'):
            output = e.output
        raise
    finally:
        fo.write(output)
        fo.close()
    return output


def run_ice(bench_name, logfile, hyper, verbose=False, timeout=None):
    """Returns ICE Boogie.exe on `bench_name`."""
    if hyper:
        raise Exception("ICE doesn't accept hyperparameters")

    example_path = os.path.join(os.environ["ICE_BENCH"], bench_name + ".bpl")
    assert os.path.isfile(example_path)
    root = os.environ["ICE_ROOT"]
    cmd = os.path.join(root, "Boogie", "Binaries", "Boogie.exe")
    assert os.path.isfile(cmd)

    for cachepath in glob.glob(example_path + ".*"):
        if verbose:
            print("removing %s" % cachepath)
        os.remove(cachepath)

    # This was built with msys. It needs the relevant DLLs in PATH to work.
    new_env = dict(os.environ)
    new_env['PATH'] = "/cygdrive/c/tools/msys64/mingw64/bin:" + os.environ["PATH"]

    start = time.time()
    output = subproc_check_output([cmd, "-nologo", "-noinfer", "-contractInfer",
                                   "-mlHoudini:dt_penalty", "-printAssignment",
                                   win_path(example_path)],
                                  timeout=timeout,
                                  cwd=os.path.join(root, "Boogie", "Binaries"),
                                  logfile=logfile,
                                  env=new_env)
    end = time.time()

    success, t = False, 0
    for line in output.splitlines()[-40:]:
        if verbose:
            print(line)
        tm = TOTAL_TIME_RE.match(line)
        if tm:
            t = float(tm.group(1))
        sm = BOOGIE_RESULTS_RE.match(line)
        if sm:
            success = True
    if success:
        if t == 0:
            raise Exception("couldn't find time")
        return RunResult(t, proc_time=end-start, iters=None, success_kind=None)
    else:
        raise Exception("couldn't find '0 errors'")


def run_mcmc(bench_name, logfile, hyper, verbose=False, timeout=None):
    if hyper:
        raise Exception("ICE doesn't accept hyperparameters")
    
    example_dirpath = os.path.join(os.environ["MCMC_BENCH"], bench_name)
    root = os.environ['MCMC_ROOT']
    cmd = os.path.join(root, "Release", "numerical.exe")
    assert os.path.isfile(cmd)
    
    start = time.time()
    output = subproc_check_output([cmd], cwd=example_dirpath,
                                  timeout=timeout,
                                  logfile=logfile)
    end = time.time()
    for line in output.splitlines()[-20:]:
        if verbose:
            print(" ---", line)
        m = TOTAL_TIME_RE.match(line)
        if m:
            return RunResult(float(m.group(1)), end-start, None, None)
    raise Exception("couldn't find 'Total time'")


def run_z3(bench_name, logfile, hyper, verbose=False, timeout=None):
    if hyper == 'spacerhyp1':
        hyp_args = "fixedpoint.xform.slice=false fixedpoint.xform.inline_linear=false fixedpoint.xform.inline_eager=false fixedpoint.xform.tail_simplifier_pve=false".split()
    elif hyper == 'spacerhyp2':
        hyp_args = "fixedpoint.xform.slice=false fixedpoint.xform.inline_linear=false fixedpoint.xform.inline_eager=false fixedpoint.xform.tail_simplifier_pve=false fixedpoint.engine=spacer fixedpoint.use_heavy_mev=true fixedpoint.pdr.flexible_trace=true fixedpoint.reset_obligation_queue=false fixedpoint.spacer.elim_aux=false fixedpoint.spacer.reach_dnf=false".split()
    else:
        raise ValueError("expected spacerhyp{1, 2} as `hyper`; got: " + repr(hyper))
    
    example_path = os.path.join(os.environ["Z3_BENCH"], bench_name + '.smt2')
    root = os.environ["Z3_ROOT"]
    cmd = None
    for cand in [os.path.join(root, "bin", "z3.exe"), os.path.join(root, "z3")]:
        if os.path.isfile(cand):
            cmd = cand
            break
    assert os.path.isfile(cmd)

    opts = []
    if timeout is not None:
        opts.append("-T:" + str(int(timeout*1000)))
    opts += hyp_args
    start = time.time()
    output = subproc_check_output([cmd] + opts + ['--', win_path(example_path)],
                                  timeout=(timeout + 5),
                                  logfile=logfile)
    end = time.time()

    is_unsat, found_result = False, False
    for line in output.splitlines()[:10]:
        if verbose:
            print(" ---", line)
        split_line = line.lower().split()
        if 'sat' in split_line:
            assert not found_result
            is_unsat, found_result = False, True
        if 'unsat' in split_line:
            assert not found_result
            is_unsat, found_result = True, True
    if not found_result:
        raise Exception("couldn't find 'sat' or 'unsat'")
    if is_unsat:
        return RunResult(end-start, end-start, None, None)
    raise Exception("was 'sat'")


def run_freqhorn(bench_name, logfile, hyper, verbose=False, timeout=None):
    # We just interpret FreqHorn's `hyper` as pass-through args,
    # with the exception of `itp`, which is followed by an integer.
    hyp_args = [['--itp', x[3:]] if x.startswith('itp') else ['--' + x]
                for x in hyper.split('-')]
    hyp_args = reduce(lambda a, b: a + b, hyp_args, [])  # flatten

    example_path = os.path.join(os.environ['FREQHORN_BENCH'], bench_name + '.smt2')
    root = os.environ["FREQHORN_ROOT"]
    cmd = os.path.join(root, 'build', 'tools', 'deep', 'freqhorn')
    start = time.time()
    output = subproc_check_output([cmd] + hyp_args + [example_path],
                                  timeout=(timeout),
                                  logfile=logfile)
    end = time.time()

    result_found, success, iters, v2_kind = False, None, None, None
    for line in output.splitlines():
        if verbose:
            print(line)
        iter_limit_m = FREQHORN_ITER_LIMIT_RE.match(line)
        if iter_limit_m:
            assert not result_found
            result_found, success = True, False
            iters = int(iter_limit_m.group(1))
        elif '--v1' in hyp_args:
            m = FREQHORN_V1_RE.match(line)
            if m:
                assert not result_found
                result_found, success, iters = True, True, int(m.group(1))
        else:
            boot_m = FREQHORN_V2_BOOT_RE.match(line)
            samp_m = FREQHORN_V2_SAMPLING_RE.match(line)
            if boot_m:
                assert not result_found
                result_found, success, v2_kind = True, True, 'bootstrapping'
            elif samp_m:
                assert not result_found
                result_found, success, v2_kind = True, True, 'sampling'
    
    if not result_found:
        raise Exception("didn't find result in output")
    if not success:
        raise IterLimitHitException("no success after %d iterations" % iters,
                                    iters=iters)
    return RunResult(None, end-start, iters, v2_kind)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("ALGO", type=str)
    parser.add_argument("BENCHNAME", type=str)
    parser.add_argument("-o", "--outdir", type=str,
                        help="path to directory to fill with results")
    parser.add_argument('-v', "--verbose", action='store_true',
                        help="be noisier about what's going on")
    parser.add_argument("--hyper", type=str,
                        help="a hyperparameter string for the algo.")
    args = parser.parse_args(args=[x for x in sys.argv[1:] if len(x)])

    # Make the out/ directory
    outdir = args.outdir
    if not args.outdir:
        outdir = tempfile.mkdtemp()
    elif not os.path.exists(args.outdir):
        os.makedirs(outdir, mode=0700)

    # Set up environment for right ALGO
    if args.ALGO.upper() == 'MCMC':
        fn = run_mcmc
    elif args.ALGO.upper() == 'ICE':
        fn = run_ice
    elif args.ALGO.upper() == 'Z3':
        fn = run_z3
    elif args.ALGO.upper() == 'FREQHORN':
        fn = run_freqhorn
    else:
        raise Exception("unrecognized algo.: {}".format(args.ALGO))

    # Begin building the result.json object
    result_obj = {
        'algorithm': args.ALGO.upper(),
        'startDate': datetime.utcnow().replace(tzinfo=simple_utc()).isoformat(),
        'benchmarkName': args.BENCHNAME
    }
    if args.hyper:
        result_obj['hyperparams'] = args.hyper

    # Run the benchmark
    logpath = os.path.join(outdir, "out.log")
    resultpath = os.path.join(outdir, 'result.json')
    resultfile = open(resultpath, 'w')
    try:
        run_result = fn(args.BENCHNAME, logpath, args.hyper,
                        verbose=args.verbose, timeout=ONE_MIN)
    except subprocess32.CalledProcessError:
        traceback.print_exc()
        return 2
    except subprocess32.TimeoutExpired:
        if args.verbose:
            print("Timed out")
        result_obj['outcome'] = 'timeout'
        json.dump(result_obj, resultfile)
    except IterLimitHitException as e:
        if args.verbose:
            print("Iteration limit hit")
        result_obj['outcome'] = 'iterLimitHit'
        result_obj['iters'] = e.iters
        json.dump(result_obj, resultfile)
    except KeyboardInterrupt:
        return 0
    else:
        result_obj['outcome'] = 'success'
        result_obj['processTime'] = run_result.proc_time
        if run_result.reported_time:
            result_obj['reportedTime'] = run_result.reported_time
        if run_result.success_kind:
            result_obj['successKind'] = run_result.success_kind
        if run_result.iters is not None:
            result_obj['iters'] = run_result.iters
        json.dump(result_obj, resultfile)
    finally:
        resultfile.close()
        if os.path.getsize(resultpath) == 0:
            os.unlink(resultpath)


if __name__ == '__main__':
    ret = main()
    if ret:
        sys.exit(ret)
