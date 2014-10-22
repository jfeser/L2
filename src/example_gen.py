#!/usr/bin/env python3

from collections import OrderedDict
from multiprocessing import Pool
import random
from subprocess import Popen, PIPE, TimeoutExpired
import sys
import time

TIMEOUT = 5 * 60
MAX_NUMBER = 10
MAX_LENGTH = 5
MAX_BRANCH = 3
MAX_DEPTH = 3
NUM_EXAMPLES = 2

def generate_num():
    return random.choice(range(MAX_NUMBER))

def generate_num_list(empty):
    if empty:
        return ([],)
    else:
        return ([generate_num() for i in range(1, random.randint(2, MAX_LENGTH))],)

def generate_num_list_num(empty):
    return (generate_num_list(empty)[0], generate_num())

def generate_num_list_num_list(empty):
    return (generate_num_list(empty)[0], generate_num_list(empty)[0])

def generate_num_list_list(empty):
    if empty:
        return ([],)
    else:
        return ([generate_num_list(empty)[0] for i in range(1, random.randint(2, MAX_LENGTH))],)

def generate_num_tree(empty, depth=MAX_DEPTH):
    if empty:
        return ({},)
    elif depth <= 0:
        return ({'value': generate_num(), 'children': []},)
    else:
        return ({'value': generate_num(), 
                 'children': [generate_num_tree(empty, depth=(depth - 1))[0] for i in \
                              range(1, random.randint(1, MAX_BRANCH))]},)

def generate_num_list_tree(empty, depth=MAX_DEPTH):
    if empty:
        return ({},)
    elif depth <= 0:
        return ({'value': generate_num_list(empty)[0], 'children': []},)
    else:
        return ({'value': generate_num_list(empty)[0],
                 'children': [generate_num_list_tree(empty, depth=(depth - 1))[0] for i in \
                              range(1, random.randint(1, MAX_BRANCH))]},)

def generate_num_tree_num(empty):
    return (generate_num_tree(empty)[0], generate_num())
    
def to_string(x):
    if type(x) is list:
        return '[{}]'.format(' '.join(to_string(e) for e in x))
    if type(x) is dict:
        if x == {}:
            return '{}'
        else:
            value_str = to_string(x['value'])
            if x['children'] == []:
                return '{' + value_str + '}'
            else:
                children_str = ' '.join(to_string(e) for e in x['children'])
                return '{' + value_str + ' ' + children_str + '}'
    elif type(x) is bool:
        return {True: '#t', False: '#f'}[x]
    else:
        return str(x)

def mapt(t, f):
    if t == {}:
        return t
    else:
        return {'value': f(t['value']), 'children': [mapt(x, f) for x in t['children']]}

def foldt(t, f, i):
    if t == {}:
        return i
    else:
        return f([foldt(x, f, i) for x in t['children']], t['value'])

def leaves(t):
    if t == {}:
        return []
    elif t['children'] == []:
        return [t['value']]
    else:
        return sum([leaves(c) for c in t['children']], [])

testcases = {
    'mycar': {
        'impl': lambda l: l[0],
        'input_generator': generate_num_list,
    },

    'mycdr': {
        'impl': lambda l: l[1:],
        'input_generator': generate_num_list,
    },

    'dupli': {
        'impl': lambda l: sum([[x, x] for x in l], []),
        'input_generator': generate_num_list,
    },

    'incr': {
        'impl': lambda l: [x + 1 for x in l],
        'input_generator': generate_num_list,
    },

    'add': {
        'impl': lambda l, y: [x + y for x in l],
        'input_generator': generate_num_list_num,
    },

    'evens': {
        'impl': lambda l: [x for x in l if x % 2 == 0],
        'input_generator': generate_num_list,
    },

    'reverse': {
        'impl': lambda l: list(reversed(l)),
        'input_generator': generate_num_list,
    },

    'last': {
        'impl': lambda l: list(reversed(l))[0],
        'input_generator': generate_num_list,
    },

    'length': {
        'impl': lambda l: len(l),
        'input_generator': generate_num_list,
    },

    'max': {
        'impl': lambda l: max(l),
        'input_generator': generate_num_list,
    },

    'multfirst': {
        'impl': lambda l: [l[0] for x in l],
        'input_generator': generate_num_list,
    },

    'multlast': {
        'impl': lambda l: [l[-1] for x in l],
        'input_generator': generate_num_list,
    },

    'append': {
        'impl': lambda l, x: l + [x],
        'input_generator': generate_num_list_num,
    },

    'member': {
        'impl': lambda l, x: x in l,
        'input_generator': generate_num_list_num,
    },

    'incrs': {
        'impl': lambda l: [[x + 1 for x in y] for y in l],
        'input_generator': generate_num_list_list,
    },

    'zeroes': {
        'impl': lambda l: [x for x in l if x is not 0],
        'input_generator': generate_num_list,
    },

    'concat': {
        'impl': lambda x, y: x + y,
        'input_generator': generate_num_list_num_list,
    },

    'sums': {
        'impl': lambda l: [sum(x) for x in l],
        'input_generator': generate_num_list_list,
    },

    'join': {
        'impl': lambda l: sum(l, []),
        'input_generator': generate_num_list_list,
    },

    'incrt': {
        'impl': lambda t: mapt(t, lambda x: x + 1),
        'input_generator': generate_num_tree,
    },    

    'sumt': {
        'impl': lambda t: foldt(t, lambda xs, x: sum(xs) + x, 0),
        'input_generator': generate_num_tree,
    },    

    'leaves': {
        'requires': ['join'],
        'impl': leaves,
        'input_generator': generate_num_tree,
    },

    'sum': {
        'impl': sum,
        'input_generator': generate_num_list,
    },

    'count_leaves': {
        'requires': ['sum'],
        'impl': lambda t: len(leaves(t)),
        'input_generator': generate_num_tree,
    },

    'membert': {
        'impl': lambda t, x: foldt(t, lambda cs, c: True if c == x else any(cs), False),
        'input_generator': generate_num_tree_num,
    },

    'flatten': {
        'requires': ['join'],
        'impl': lambda t: foldt(t, lambda cs, c: [c] + sum(cs, []), []),
        'input_generator': generate_num_tree,
    },

    'flattenl': {
        'requires': ['join'],
        'impl': lambda t: foldt(t, lambda cs, c: c + sum(cs, []), []),
        'input_generator': generate_num_list_tree,
    },

    'height': {
        'requires': ['max'],
        'impl': lambda t: foldt(t, lambda cs, c: max(cs) + 1 if len(cs) > 0 else 1, 0),
        'input_generator': generate_num_tree,
    },

    'average': {
        'requires': ['sum', 'length'],
        'impl': lambda l: sum(l) // len(l),
        'input_generator': generate_num_list,
    },

    'dropaverage': {
        'requires': ['sum', 'length', 'average'],
        'impl': lambda l: [x for x in l if x >= sum(l) // len(l)],
        'input_generator': generate_num_list,
    },

    'dropmax': {
        'requires': ['max'],
        'impl': lambda l: [x for x in l if x != max(l)],
        'input_generator': generate_num_list,
    },

    'shiftl': {
        'requires': ['append'],
        'impl': lambda l: l[1:] + [l[0]],
        'input_generator': generate_num_list,
    },

    'shiftr': {
        'requires': ['last'],
        'impl': lambda l: [l[-1]] + l[:-1],
        'input_generator': generate_num_list,
    },

    'dedup': {
        'requires': ['member'],
        'impl': lambda l: list(OrderedDict.fromkeys(l)),
        'input_generator': generate_num_list,
    },
}

def generate_examples(name, num_examples):
    testcase = testcases[name]
    examples = []
    inputs = testcase['input_generator'](True)
    try:
        output = testcase['impl'](*inputs)
        examples.append((inputs, output))
    except Exception:
        pass

    while len(examples) < num_examples:
        inputs = testcase['input_generator'](False)
        try:
            output = testcase['impl'](*inputs)
            examples.append((inputs, output))
        except Exception:
            pass

    examples_str = ''
    for example in examples:
        inputs_str = ' '.join([to_string(i) for i in example[0]])
        examples_str += '({} {}) -> {}\n'.format(name, inputs_str, to_string(example[1]))
    return examples_str

def run(name, num_examples=5):
    testcase = testcases[name]

    # Generate examples
    if 'requires' in testcase:
        examples_strs = [generate_examples(n, num_examples) for n in testcase['requires']]
    else:
        examples_strs = []
    examples_strs.append(generate_examples(name, num_examples))
    examples_str = '\n'.join(examples_strs)

    # Synthesize
    # print('Running {} with examples:\n{}'.format(name, examples_str))
    p = Popen(['./timing.native', '-s', '-i'], stdin=PIPE, stdout=PIPE)
    try:
        output = p.communicate(input=examples_str.encode('utf-8'), timeout=TIMEOUT)[0]
        ret = '\n'.join(output.decode('utf-8').split('\n')[1:])
    except TimeoutExpired:
        ret = 'Time expired when running {}. (Timeout: {} sec)\n'.format(testcase, TIMEOUT)
    return ret

def runp(name):
    random.seed()
    return run(name, num_examples=num_examples)

def run_repeated(name, num_trials, num_examples):
    with open('{}-{}-{}.results'.format(name, num_examples, num_trials), 'w') as output:
        with Pool(processes=2) as pool:
            results = pool.map(runp, [name] * num_trials)
        for result in results:
            output.write(result)
            output.write('\n')
    return results

def check_results(results):
    correct = 0
    incorrect = 0
    total = len(results)

    while correct + incorrect < total:
        print(results[0], end='')
        is_correct = input('? ') == 'y'
        if is_correct:
            correct += len([r for r in results if r == results[0]])
            results = [r for r in results if r != results[0]]
        else:
            incorrect += len([r for r in results if r == results[0]])
            results = [r for r in results if r != results[0]]
    return correct / total

if __name__ == '__main__':
    # if len(sys.argv) == 2:
    #     name = sys.argv[1]
    #     print(run(name), end='')

    # elif len(sys.argv) == 4:
    #     name = sys.argv[1]
    #     num_examples = int(sys.argv[2])
    #     num_trials = int(sys.argv[3])
    #     results = run_repeated(name, num_trials, num_examples)
    #     print(check_results(results))
    # else:
    #     for name in testcases:
    #         print(run(name), end='')
    num_trials = int(sys.argv[1])
    max_examples = int(sys.argv[2])
    for name in testcases:
        for num_examples in range(1, max_examples + 1):
            start = time.time()
            run_repeated(name, num_trials, num_examples)
            end = time.time()
            print('Run {} {}-example trials of {} in {}.'.format(num_trials, num_examples, name, end - start))
