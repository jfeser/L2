#!/usr/bin/env python3

'''
Usage: benchmark.py [options] (--l2 <file>) (--timeout <file>) <benchmark>...

Options:
  -h --help               Show this screen.
  --l2 <file>
  --timeout <file>
  --l2-args <args>
  --max-memory <mem>      Maximum memory (Mb) [default: 500].
  --max-runtime <time>    Maximum runtime (seconds) [default: 600].
'''

from docopt import docopt
import os
import json
import subprocess
from subprocess import Popen, PIPE

args = docopt(__doc__)

def run_benchmark(name):
    out_file = os.path.splitext(os.path.basename(name))[0] + '-bench.json'
    cmd = '{--timeout} -m {--max-memory} -t {--max-runtime} -q -- {--l2} synth -d {out_file} {--l2-args} {name}'.format(out_file=out_file, name=name, **args)
    os.system(cmd)
    if not os.path.isfile(out_file):
        with open(out_file, 'w') as f:
            f.write(json.dumps({'testcase': name, 'solution': None}))

if __name__ == '__main__':
    print("Running benchmarks...")
    for name in args['<benchmark>']:
        print("\nRunning {}".format(name))
        run_benchmark(name)
        print()
            
