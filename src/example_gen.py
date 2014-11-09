#!/usr/bin/env python3

from collections import OrderedDict
from itertools import product
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
NUM_PROCESSES = 1

def generate_num():
    return random.choice(range(MAX_NUMBER))

def generate_num_list():
    return ([generate_num() for i in range(random.randint(0, MAX_LENGTH))],)

def generate_num_list_num():
    return (generate_num_list()[0], generate_num())

def generate_num_list_num_list():
    return (generate_num_list()[0], generate_num_list()[0])

def generate_num_list_list():
    return ([generate_num_list()[0] for i in range(random.randint(0, MAX_LENGTH))],)

def generate_num_tree():
    height = random.randint(0, MAX_DEPTH)
    def gnt(depth):
        if depth <= 0:
            return ({'value': generate_num(), 'children': []},)
        else:
            return ({'value': generate_num(), 
                     'children': [gnt(depth - 1)[0] for i in \
                                  range(1, random.randint(1, MAX_BRANCH))]},)
    if height == 0:
        return ({},)
    else:
        return gnt(height)

def generate_num_tree_list():
    return ([generate_num_tree()[0] for i in range(random.randint(0, MAX_LENGTH))],)
    
def generate_num_list_tree():
    height = random.randint(0, MAX_DEPTH)
    def gt(depth):
        if depth <= 0:
            return ({'value': generate_num_list()[0], 'children': []},)
        else:
            return ({'value': generate_num_list()[0],
                     'children': [gt(depth - 1)[0] for i in \
                                  range(1, random.randint(1, MAX_BRANCH))]},)
    if height == 0:
        return ({},)
    else:
        return gt(height)

def generate_num_list_tree_num():
    return (generate_num_list_tree()[0], generate_num())

def generate_num_list_tree_num_num():
    return (generate_num_list_tree()[0], generate_num(), generate_num())

def generate_num_tree_num():
    return (generate_num_tree()[0], generate_num())
    
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

def foldl(l, f, i):
    if l == []:
        return i
    else:
        return foldl(l[1:], f, f(i, l[0]))

def foldr(l, f, i):
    if l == []:
        return i
    else:
        return f(foldr(l[1:], f, i), l[0])
    
def selectnodes(t):
    join = lambda a: foldl(a, lambda c,b: foldr(c, lambda e,d: [d] + e, b), [])
    sn = lambda t: foldt(t, lambda cs, c: [c] + join(cs) if c % 2 == 0 else join(cs), [])
    return sn(t)

def searchnodes(t, x):
    if t == {}:
        return False
    else:
        if x in t['value']:
            return True
        else:
            return any([searchnodes(c, x) for c in t['children']])

testcases = {
    'dupli': {
        'impl': lambda l: sum([[x, x] for x in l], []),
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

    'droplast': {
        'impl': lambda l: l[:-1],
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

    'concat': {
        'impl': lambda x, y: x + y,
        'input_generator': generate_num_list_num_list,
    },

    'sum': {
        'impl': lambda l: sum(l),
        'input_generator': generate_num_list,
    },

    'incrs': {
        'impl': lambda l: [[x + 1 for x in y] for y in l],
        'input_generator': generate_num_list_list,
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

    'membert': {
        'impl': lambda t, x: foldt(t, lambda cs, c: True if c == x else any(cs), False),
        'input_generator': generate_num_tree_num,
    },

    'maxt': {
        'impl': lambda t: foldt(t, lambda cs, c: max([c] + cs), 0),
        'input_generator': generate_num_tree,
    },

    'prependt': {
        'impl': lambda t, x: mapt(t, lambda y: [x] + y),
        'input_generator': generate_num_list_tree_num,
    },

    'appendt': {
        'impl': lambda t, x: mapt(t, lambda y: y + [x]),
        'input_generator': generate_num_list_tree_num,
    },

    'replacet': {
        'impl': lambda t, x, y: mapt(t, lambda l: [y if z == x else z for z in l]),
        'input_generator': generate_num_list_tree_num_num,
    },

    'sumnodes': {
        'impl': lambda t: mapt(t, lambda l: sum(l)),
        'input_generator': generate_num_list_tree,
    },

    'sumtrees': {
        'impl': lambda l: [foldt(t, lambda cs, c: c + sum(cs), 0) for t in l],
        'input_generator': generate_num_tree_list,
    },

    'cprod': {
        'impl': lambda l: [list(x) for x in product(*l)],
        'input_generator': generate_num_list_list,
    },

    'leaves': {
        'requires': {
            "join": "(lambda (a) (foldl a (lambda (c b) (foldr c (lambda (e d) (cons d e)) b)) []))"
        },
        'impl': leaves,
        'input_generator': generate_num_tree,
    },

    'count_leaves': {
        'requires': {
            "sum": "(lambda (a) (foldl a (lambda (c b) (+ c b)) 0))"
        },
        'impl': lambda t: len(leaves(t)),
        'input_generator': generate_num_tree,
    },

    'flatten': {
        'requires': {
            "join": "(lambda (a) (foldl a (lambda (c b) (foldr c (lambda (e d) (cons d e)) b)) []))"
        },
        'impl': lambda t: foldt(t, lambda cs, c: [c] + sum(cs, []), []),
        'input_generator': generate_num_tree,
    },

    'height': {
        'requires': {
            "max": "(lambda (a) (foldl a (lambda (c b) (if (< c b) b c)) 0))"
        },
        'impl': lambda t: foldt(t, lambda cs, c: max(cs) + 1 if len(cs) > 0 else 1, 0),
        'input_generator': generate_num_tree,
    },
    
    'flattenl': {
        'requires': {
            "join": "(lambda (a) (foldl a (lambda (c b) (foldr c (lambda (e d) (cons d e)) b)) []))"
        },
        'impl': lambda t: foldt(t, lambda cs, c: c + sum(cs, []), []),
        'input_generator': generate_num_list_tree,
    },

    'dropmax': {
        'requires': {
            "max": "(lambda (a) (foldl a (lambda (c b) (if (< c b) b c)) 0))"
        },
        'impl': lambda l: [x for x in l if x != max(l)],
        'input_generator': generate_num_list,
    },

    'shiftl': {
        'requires': {
            "reverse": "(lambda (a) (foldl a (lambda (c b) (cons b c)) []))"
        },
        'impl': lambda l: l[1:] + [l[0]],
        'input_generator': generate_num_list,
    },

    'shiftr': {
        'requires': {
            "reverse": "(lambda (a) (foldl a (lambda (c b) (cons b c)) []))"
        },
        'impl': lambda l: [l[-1]] + l[:-1],
        'input_generator': generate_num_list,
    },

    'dedup': {
        'requires': {
            "member": "(lambda (b a) (foldl b (lambda (d c) (| d (= a c))) #f))"
        },
        'impl': lambda l: list(OrderedDict.fromkeys(l)),
        'input_generator': generate_num_list,
    },

    'selectnodes': {
        'requires': {
            "join": "(lambda (a) (foldl a (lambda (c b) (foldr c (lambda (e d) (cons d e)) b)) []))",
            "pred": "(lambda (a) (= 0 (% a 2)))"
        },
        'impl': selectnodes,
        'input_generator': generate_num_tree,
    },

    'searchnodes': {
        'requires': {
            "member": "(lambda (b a) (foldl b (lambda (d c) (| d (= a c))) #f))"            
        },
        'impl': searchnodes,
        'input_generator': generate_num_list_tree_num,
    },
}

def generate_examples(name, num_examples):
    testcase = testcases[name]
    examples = []
    while len(examples) < num_examples:
        inputs = testcase['input_generator']()
        try:
            output = testcase['impl'](*inputs)
            examples.append((inputs, output))
        except:
            testcase['impl'](*inputs)
            pass

    examples_str = ''
    for example in examples:
        inputs_str = ' '.join([to_string(i) for i in example[0]])
        examples_str += '({} {}) -> {}\n'.format(name, inputs_str, to_string(example[1]))
    return examples_str

def run(name, num_examples=5):
    testcase = testcases[name]

    # Generate examples
    examples_strs = []
    examples_strs.append(generate_examples(name, num_examples))
    examples_str = '\n'.join(examples_strs)

    # Synthesize
    print('Running {} with examples:\n{}'.format(name, examples_str))
    sys.stdout.flush()

    bk_cmd = []
    if 'requires' in testcase:
        for name in testcase['requires']:
            bk_cmd += ['-b', name + ' ' + testcase['requires'][name]]
            
    p = Popen(['../../timeout/timeout', '-t', str(TIMEOUT),
               '-m', '8000000',
               '../src/timing.native'] + bk_cmd + ['-i', '-c', '-s'],
              stdin=PIPE, stdout=PIPE)
    try:
        output = p.communicate(input=examples_str.encode('utf-8'))[0]
        ret = output.decode('utf-8')
    except TimeoutExpired:
        ret = 'Time expired when running {}. (Timeout: {} sec)\n'.format(testcase, TIMEOUT)
    return examples_str + ret

def runp(name):
    random.seed()
    return run(name, num_examples=num_examples)

def run_repeated(name, num_trials, num_examples):
    with open('{}-{}-{}.results'.format(name, num_examples, num_trials), 'w') as output:
        results = []
        for n in [name] * num_trials:
            output.write(runp(n))
            output.write('\n')
            output.flush()
            
        # with Pool(processes=NUM_PROCESSES) as pool:
        #     results = pool.map(runp, [name] * num_trials)

        # for result in results:
        #     output.write(result)
        #     output.write('\n')
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

tests = [
    # ('flattenl', 2, 5),
    # ('leaves', 6, 7),
    # ('selectnodes', 2, 5),
    ('searchnodes', 29),
    # ('maxt', 5, 20),
    # ('cprod', 2, 7),
    # ('droplast', 3, 7),
    # ('dedup', 10, 20),
]

if __name__ == '__main__':
    num_trials = int(sys.argv[1])
    for test in tests:
        name = test[0]

        if len(test) == 3:
            min_examples = test[1]
            max_examples = test[2]
            r = range(min_examples, max_examples + 1)
        elif len(test) == 2:
            ne = test[1]
            r = range(ne, ne + 1)
    
        for num_examples in r:
            start = time.time()
            run_repeated(name, num_trials, num_examples)
            end = time.time()
            print('Run {} {}-example trials of {} in {}.'.\
                  format(num_trials, num_examples, name, end - start))
            sys.stdout.flush()
