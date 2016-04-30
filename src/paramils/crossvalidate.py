#!/usr/bin/env python3

'''
usage: 
  crossvalidate.py setup [--test-perc PERC] [--num-tests TESTS] [--seed SEED] [--l2-path FILE] [--timeout-path FILE] OUT_DIR
  crossvalidate.py write-costs OUT_DIR

Options:
  --test-perc PERC     Percentage of instances to use as test set [default: 0.3].
  --num-tests TESTS    Number of individual tests to run [default: 8].
  --seed SEED          Random seed [default: 0].
  --l2-path FILE       Path to L2.
  --timeout-path FILE  Path to timeout.
'''

from docopt import docopt
import json
import math
import os
import random
import re
import shutil
import subprocess
import sys
import time

def relpath(path):
    return os.path.abspath(os.path.join(os.path.dirname(__file__), path))

DEFAULT_SPECS_DIR = relpath('../../specs')
DEFAULT_L2_PATH = relpath('../../l2.native')
DEFAULT_TIMEOUT_PATH_PREFIX = relpath('../../timeout')

RESOURCES = [
    'params.txt',
]
RESOURCES = [relpath(f) for f in RESOURCES]

CUTOFF_TIME = 600

SCENARIO = '''algo = {algo} "{l2_path}" "{timeout_path}"
execdir = .
deterministic = 1
run_obj = runtime
overall_obj = mean
cutoff_time = {cutoff_time}
cutoff_length = max
tunerTimeout = 30000
paramfile = params.txt
outdir = .
instance_file = train-instances.txt
test_instance_file = test-instances.txt
'''

def shuffle_split(items, num_splits, test_size):
    num_test = math.floor(test_size * len(items))
    num_train = len(items) - num_test
    
    for i in range(num_splits):
        items_shuf = random.sample(items, len(items))
        yield items_shuf[:num_train], items_shuf[num_train:]

def write_instances(items, output_fn):
    with open(output_fn, 'w') as out:
        out.write('\n'.join(items))

def setup(args):
    random.seed(int(args['--seed']))
    out_dir = args['OUT_DIR']
    num_tests = int(args['--num-tests'])
    test_perc = float(args['--test-perc'])
    
    specs_dir = DEFAULT_SPECS_DIR

    if args['--l2-path'] is None:
        l2_path = DEFAULT_L2_PATH
    else:
        l2_path = os.abspath(args['--l2-path'])
    
    if args['--timeout-path'] is None:
        if sys.platform == 'linux':
            timeout_path = DEFAULT_TIMEOUT_PATH_PREFIX + '_linux.native'
        elif sys.platform == 'darwin':
            timeout_path = DEFAULT_TIMEOUT_PATH_PREFIX + '_osx.native'
        else:
            print('Unsupported system: {}'.format(sys.platform))
            exit(-1)
    else:
        timeout_path = os.path.abspath(args['--timeout-path'])

    all_instances = [os.path.abspath(os.path.join(specs_dir, f)) for f in os.listdir(specs_dir)]
    
    os.makedirs(out_dir, exist_ok=True)

    for i, instances in enumerate(shuffle_split(all_instances, num_tests, test_perc)):
        test_dir = os.path.join(out_dir, 'run{}'.format(i))

        os.makedirs(test_dir, exist_ok=True)
        for f in RESOURCES:
            shutil.copy(f, test_dir)

        train, test = instances
        write_instances(train, os.path.join(test_dir, 'train-instances.txt'))
        write_instances(test, os.path.join(test_dir, 'test-instances.txt'))

        with open(os.path.join(test_dir, 'scenario.txt'), 'w') as f:
            kwargs = {
                'algo': relpath('l2_wrapper.py'),
                'l2_path': l2_path,
                'timeout_path': timeout_path,
                'cutoff_time': CUTOFF_TIME
            }
            f.write(SCENARIO.format(**kwargs))

def cost_of_params(kv):
    return {
        "num": kv['num'],
        "bool": kv['bool'],
        "hole": kv['hole'],
        "lambda": kv['lambda'],
        "let": kv['let'],
        "list": kv['list'],
        "tree": kv['tree'],
        "var": kv['var_'],
        "call": {
            "+": kv['add'],
            "-": kv['sub'],
            "*": kv['mult'],
            "/": kv['div'],
            "%": kv['mod'],
            "=": kv['eq'],
            "!=": kv['neq'],
            "<": kv['lt'],
            "<=": kv['le'],
            ">": kv['gt'],
            ">=": kv['ge'],
            "&": kv['and'],
            "|": kv['or'],
            "~": kv['not'],
            "if": kv['if'],
            "rcons": kv['rcons'],
            "cons": kv['cons'],
            "car": kv['car'],
            "cdr": kv['cdr'],
            "tree": kv['tree_op'],
            "children": kv['children'],
            "value": kv['value'],
            "foldr": kv["foldr"],
            "foldl": kv["foldl"],
            "map": kv["map"],
            "filter": kv["filter"],
            "mapt": kv["mapt"],
            "foldt": kv["foldt"],
            "merge": kv["merge"],
            "take": kv["take"],
            "zip": kv["zip"],
            "intersperse": kv["intersperse"],
            "append": kv["append"],
            "reverse": kv["reverse"],
            "concat": kv["concat"],
            "drop": kv["drop"],
            "sort": kv["sort"],
            "dedup": kv["dedup"],
        },
        "call_default": 1,
    }
            
def write_costs(args):
    out_dir = os.path.abspath(args['OUT_DIR'])
    traj_reg = re.compile('^.*-traj_\d+\.csv$')

    for run_dir in [os.path.join(out_dir, d) for d in os.listdir(out_dir)]:
        trajfile = [os.path.join(run_dir, f) for f in os.listdir(run_dir) if traj_reg.match(f)][0]
    
        with open(trajfile, 'r') as f:
            cost_params = f.readlines()[-1].strip().split(', ')[5:]
            costs = {}
            for cp in cost_params:
                parts = cp.split('=')
                name = parts[0]
                cost = int(parts[1].strip("'"))
                costs[name] = cost

            cost_fn = os.path.join(run_dir, 'cost.json')
            with open(cost_fn, 'w') as cost_file:
                json.dump(cost_of_params(costs), cost_file)

def main():
    args = docopt(__doc__)

    if args['setup']:
        setup(args)
    elif args['write-costs']:
        write_costs(args)

if __name__ == '__main__':
    main()
