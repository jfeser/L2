#!/usr/bin/env python3

import multiprocessing
from subprocess import Popen, PIPE

L2_PATH = '../src/timing.native'
TIMEOUT_PATH = 'timeout'

MAX_MEMORY = 500

BENCHMARKS = [
    "dupli", "add", "Reverse", "droplast", "last", "length", "max", "multfirst",
    "multlast", "append", "concat", "sum", "incrs", "sums", "join",
    "incrt", "leaves", "count_leaves", "membert", "maxt", "flatten", "height",
    "prependt", "appendt", "replacet", "sumnodes", "flattenl", "sumtrees", "dropmax",
    "shiftl", "shiftr", "Dedup", "searchnodes", "selectnodes", "dropmins", "cprod",
    "tconcat", "count_nodes", "largest_n", "evens", "intersect", "member", "sumt"
]

def run_benchmark(name):
    cmd = [ TIMEOUT_PATH, "-m", str(MAX_MEMORY), "-q", "--", L2_PATH, "-i", name ]
    proc = Popen(cmd, stdout=PIPE, stderr=PIPE)
    outs, errs = proc.communicate()
    return "Ran {}:\n{}\n{}".format(name, outs.decode('utf-8'), errs.decode('utf-8'))

def print_output(out):
    print(out)

if __name__ == '__main__':
    with multiprocessing.Pool() as pool:
        print("Running benchmarks...")
        results = []
        for name in BENCHMARKS:
            print(run_benchmark(name))
            # results.append(pool.apply_async(run_benchmark, args=(name,)))
            
