#!/usr/bin/env python3

'''
usage: l2_wrapper.py <testcase> <args> <cutoff-time> <cutoff-length> <seed> <params>...
'''

import sys
from subprocess import check_output
import json
import tempfile

L2_PATH = '/Users/jack/Documents/l2/repo/l2.native'
TIMEOUT_PATH = '/Users/jack/Documents/l2/repo/timeout_osx.native'
MEMORY_LIMIT = 2000

def cost_of_params(params):
    params = [int(p) for i, p in enumerate(params) if i % 2 == 1]
    return {
        "num": params[0],
        "bool": params[1],
        "hole": params[2],
        "lambda": params[3],
        "let": params[4],
        "list": params[5],
        "tree": params[6],
        "var": params[7],
        "call": {
            "+": params[8],
            "-": params[9],
            "*": params[10],
            "/": params[11],
            "%": params[12],
            "=": params[13],
            "!=": params[14],
            "<": params[15],
            "<=": params[16],
            ">": params[17],
            ">=": params[18],
            "&": params[19],
            "|": params[20],
            "~": params[21],
            "if": params[22],
            "rcons": params[23],
            "cons": params[24],
            "car": params[25],
            "cdr": params[26],
            "tree": params[27],
            "children": params[28],
            "value": params[29]
        },
        "call_default": 1,
    }

if __name__ == '__main__':
    args = sys.argv
    print(list(enumerate(args)))
    testcase = args[1]
    cutoff_time = args[3]
    seed = args[5]
    params = args[6:]

    with tempfile.NamedTemporaryFile() as f:
        cost_str = json.dumps(cost_of_params(params))
        f.write(cost_str.encode())
        f.flush()

        cmd = [
            TIMEOUT_PATH,
            '-m', str(MEMORY_LIMIT),
            '-t', str(int(float(cutoff_time))),
            '--machine-readable',
            '--',
            L2_PATH, 'synth',
            '--cost', f.name,
            '--engine', 'v2',
            testcase
        ]
        out = check_output(cmd)
        out = json.loads(out.decode())

        if out['status'] == 'success':
            print(out)
            print('Result for ParamILS: SAT, {}, -1, -1, {}'.format(out['runtime'], seed))
        else:
            print(out)
            print('Result for ParamILS: TIMEOUT, {}, -1, -1, {}'.format(out['runtime'], seed))

    

    

    
    
