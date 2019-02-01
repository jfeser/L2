#!/usr/bin/env python3

'''
Usage: benchmark.py RUNFILE
'''

from docopt import docopt
from glob import glob
import json
import os
import shlex
from subprocess import Popen, PIPE
from tqdm import tqdm

def load_runfile(fn):
    with open(fn, 'r') as f:
        return json.load(f)

def run_benchmark(runfile):
    max_mem = runfile['max_memory']
    max_time = runfile['max_runtime']
    l2_args = runfile['l2_args']
    num_restarts = runfile['restarts']
    timeout_path = runfile['timeout_path']
    l2_path = runfile['l2_path']
    
    runs = []
    for bench in glob(runfile['bench']):
        for run in range(num_restarts):
            runs.append((bench, run))

    for (bench, run) in tqdm(runs):
        bench_name = os.path.splitext(os.path.basename(bench))[0]
        for r in range(num_restarts):
            run_fn = '{}-run_{}.json'.format(bench_name, r)
            synth_fn = '{}-synth_{}.json'.format(bench_name, r)
            cmd = '{} -t {} -m {} -q --machine-readable -- {} synth {} -d {} {}'.\
                  format(timeout_path, max_mem, max_time,
                         l2_path, l2_args, shlex.quote(synth_fn), shlex.quote(bench))
            p = Popen(cmd, stdout=PIPE, shell=True)
            p.wait()
            stdout, _ = p.communicate()
            with open(run_fn, 'wb') as f:
                f.write(stdout)

def main(args):
    print("Running benchmarks...")
    run_benchmark(load_runfile(args['RUNFILE']))
                
if __name__ == '__main__':
    args = docopt(__doc__)
    main(args)
