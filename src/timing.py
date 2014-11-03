#!/usr/bin/env python3

import subprocess
import sys

# MAX_MEMORY = int(4e9) # 4 Gb
TIMEOUT = 10 * 60

testcase_names = [
    "dupli",
    "add",
    "evens",
    "reverse",
    "droplast",
    "last",
    "length",
    "max",
    "multfirst",
    "multlast",
    "append",
    "member",
    "concat",
    "sum",
    "incrs",
    "sums",
    "join",
    "incrt",
    "sumt",
    "leaves",
    "count_leaves",
    "membert",
    "maxt",
    "flatten",
    "height",
    "prependt",
    "appendt",
    "replacet",
    "sumnodes",
    "flattenl",
    "sumtrees",
    "dropmax",
    "shiftl",
    "shiftr",
    "dedup",
    "selectnodes",
    "dropmins",
    "cprod",
]

# def setlimits():
#     resource.setrlimit(resource.RLIMIT_AS, MAX_MEMORY)

def run(testcase, args=[]):
    try:
        output = subprocess.check_output(['./timing.native'] + args + [testcase], timeout=TIMEOUT)
        print(output.decode('utf-8'), end='')
    except subprocess.TimeoutExpired:
        print('Time expired when running {}. (Timeout: {} sec)\n'.format(testcase, TIMEOUT))

if __name__ == '__main__':
    for testcase in testcase_names:
        run(testcase, args=sys.argv[1:])
