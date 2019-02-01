#!/usr/bin/env python3

'''
usage: l2_wrapper.py <l2-path> <timeout-path> <testcase> <args> <cutoff-time> <cutoff-length> <seed> <params>...
'''

import sys
from subprocess import check_output
import json
import tempfile

MEMORY_LIMIT = 2000

def cost_of_params(params):
    kv = {}
    for i in range(0, len(params), 2):
        kv[params[i][1:]] = int(params[i+1])
        
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

if __name__ == '__main__':
    args = sys.argv
    l2_path = args[1]
    timeout_path = args[2]
    testcase = args[3]
    cutoff_time = args[5]
    seed = args[7]
    params = args[8:]

    with tempfile.NamedTemporaryFile() as f:
        cost_str = json.dumps(cost_of_params(params))
        f.write(cost_str.encode())
        f.flush()

        cmd = [
            timeout_path,
            '-m', str(MEMORY_LIMIT),
            '-t', cutoff_time,
            '--machine-readable',
            '--',
            l2_path, 'synth',
            '--cost', f.name,
            '--engine', 'v2',
            testcase
        ]
        out = check_output(cmd)
        out = json.loads(out.decode())

        if out['status'] == 'success':
            print('Result for ParamILS: SAT, {}, -1, -1, {}'.format(out['runtime'], seed))
        else:
            print(out)
            print('Result for ParamILS: TIMEOUT, {}, -1, -1, {}'.format(out['runtime'], seed))

    

    

    
    
