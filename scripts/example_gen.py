#!/usr/bin/env python3

from collections import OrderedDict
import csv
from itertools import product
import json
from multiprocessing import Manager, Pool
import pickle
import random
from subprocess import Popen, PIPE, STDOUT, TimeoutExpired
import sys
import time

TIMEOUT = 10 * 60
MAX_NUMBER = 10
MAX_LENGTH = 5
MAX_BRANCH = 3
MAX_DEPTH = 3
NUM_WORKERS = 16

TIMEOUT_PATH = '/home/jkf1/timeout/timeout'
PICKLE_PATH = '/home/jkf1/sygus/results/classifier.pickle'
NUM_TRIALS = 100
MIN_CORRECT = 90

def generate_num():
    return random.choice(range(MAX_NUMBER))

def generate_num_list(empty=False):
    if empty:
        return ([],)
    return ([generate_num() for i in range(random.randint(0, MAX_LENGTH))],)

def generate_num_list_num(empty=False):
    if empty:
        return ([], generate_num())
    return (generate_num_list()[0], generate_num())

def generate_num_list_num_list(empty=False):
    if empty:
        return ([], [])
    return (generate_num_list()[0], generate_num_list()[0])

def generate_num_list_list(empty=False):
    if empty:
        return ([],)
    return ([generate_num_list()[0] for i in range(random.randint(0, MAX_LENGTH))],)

def generate_num_tree(empty=False):
    if empty:
        return ({},)
    
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

def generate_num_tree_list(empty=False):
    if empty:
        return ([],)
    return ([generate_num_tree()[0] for i in range(random.randint(0, MAX_LENGTH))],)
    
def generate_num_list_tree(empty=False):
    if empty:
        return ({},)
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

def generate_num_list_tree_num(empty=False):
    return (generate_num_list_tree(empty)[0], generate_num())

def generate_num_list_tree_num_num(empty=False):
    return (generate_num_list_tree(empty)[0], generate_num(), generate_num())

def generate_num_tree_num(empty=False):
    if empty:
        return ({}, generate_num())
    return (generate_num_tree()[0], generate_num())

def generate_num_tree_num_tree(empty=False):
    if empty:
        return ({}, {})
    return (generate_num_tree()[0], generate_num_tree()[0])

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

def tree(n, cs):
    return {'value':n, 'children': cs}

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

def _filter(l, f):
    if l == []:
        return []
    else:
        if f(l[0]):
            return [l[0]] + _filter(l[1:], f)
        else:
            return _filter(l[1:], f)
    
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

def droplast(l):
    if len(l) > 0:
        return l[:-1]
    else:
        raise IndexError

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
        'impl': droplast,
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
        'impl': lambda b: foldr(b, lambda d,c: d if c in d else [c] + d, []),
        'input_generator': generate_num_list,
    },

    'selectnodes': {
        'requires': {
            "join": "(lambda (a) (foldl a (lambda (c b) (foldr c (lambda (e d) (cons d e)) b)) []))",
            "pred": "(lambda (a) (= 0 (% a 2)))"
        },
        'impl': lambda b: foldt(b, lambda d,c: foldl(d, lambda f,e: _filter(f, lambda g: g % 2 == 0), [c] + sum(d, [])), []),
        'input_generator': generate_num_tree,
    },

    'searchnodes': {
        'requires': {
            "member": "(lambda (b a) (foldl b (lambda (d c) (| d (= a c))) #f))"            
        },
        'impl': searchnodes,
        'input_generator': generate_num_list_tree_num,
    },

    'count_nodes': {
        'impl': lambda t: foldt(t, lambda cs,c: 1 + sum(cs), 0),
        'input_generator': generate_num_tree,
    },

    'dropmins': {
        'impl': lambda ls: [[x for x in l if x != min(l)] if len(l) > 0 else [] for l in ls],
        'input_generator': generate_num_list_list,
    },

    'tconcat': {
        'impl': lambda c, b: foldt(c, lambda e, d: foldl(e, lambda g, f: tree(d, e), tree(d, [b] + e)), c),
        'input_generator': generate_num_tree_num_tree,
    },
}

def generate_examples(name, num_examples):
    testcase = testcases[name]
    examples = []

    inputs = testcase['input_generator'](empty=True)
    try:
        output = testcase['impl'](*inputs)
        examples.append((inputs, output))
    except:
        pass
    
    while len(examples) < num_examples - 1:
        inputs = testcase['input_generator']()
        try:
            output = testcase['impl'](*inputs)
            examples.append((inputs, output))
        except:
            pass

    examples_strs = []
    for example in examples:
        inputs_str = ' '.join([to_string(i) for i in example[0]])
        examples_strs.append('({} {}) -> {}'.format(name, inputs_str, to_string(example[1])))
    return examples_strs

def run(name, num_examples):
    testcase = testcases[name]

    # Generate examples
    examples_strs = generate_examples(name, num_examples)
    examples_str = '\n'.join(examples_strs)

    ret = {
        'name': name,
        'examples': examples_strs,
    }
    
    # Synthesize
    bk_cmd = []
    if 'requires' in testcase:
        for name in testcase['requires']:
            bk_cmd += ['-b', name + ' ' + testcase['requires'][name]]
            
    p = Popen([TIMEOUT_PATH,
               '--no-info-on-success',
               '-t', str(TIMEOUT),
               '-m', '8000000',
               '../src/timing.native'] + bk_cmd + ['-c', '-s', '-i'],
              stdin=PIPE, stdout=PIPE, stderr=STDOUT)
    
    output = p.communicate(input=examples_str.encode('utf-8'))[0].decode('utf-8')
    if 'MAXMEM' in output:
        ret['time'] = 'timeout'
    else:
        ret['time'] = float(output.split(',')[1])
        ret['solution'] = output.split(',')[2].strip()
    return ret

def listener(filename, q):
    '''listens for messages on the q, writes to file. '''
    with open(filename, 'w') as f:
        while 1:
            m = q.get()
            if m == 'kill':
                break
            
            f.write(str(m) + '\n')
            f.flush()

            print('.', end='')
            sys.stdout.flush()

def worker(name, num_examples, q):
    result = run(name, num_examples)
    q.put(json.dumps(result))
    return result
            
def run_repeated(name, num_trials, num_examples, incorrect):
    manager = Manager()
    q = manager.Queue()
    pool = Pool(NUM_WORKERS + 1) # Add one process for the listener

    # Start a listener that writes to the output file.
    filename = '{}-{}-{}.results'.format(name, num_examples, num_trials)
    pool.apply_async(listener, (filename, q))

    # Start worker jobs that run trials.
    jobs = []
    for i in range(num_trials):
        job = pool.apply_async(worker, (name, num_examples, q))
        jobs.append(job)
    
    results = []
    for job in jobs:
        results.append(job.get())

        # Check results for early exit
        num_incorrect = 0
        for result in results:
            if is_incorrect(result, incorrect):
                num_incorrect += 1
        if num_incorrect > NUM_TRIALS - MIN_CORRECT:
            pool.terminate() # Kill the rest of the jobs in the pool.
            break

    q.put('kill') # Tell the listener to stop running.
    pool.close()  
    
    print()
    return results

def is_correct(result, correct):
    return 'solution' in result and result['solution'] in correct[result['name']]

def is_incorrect(result, incorrect):
    return 'solution' not in result or result['solution'] in incorrect[result['name']]

def check_results(results, num_trials, correct):
    num_correct = 0
    for result in results:
        if is_correct(result, correct):
            num_correct += 1

    print('{}/{} are correct.'.format(num_correct, num_trials))
            
    if num_correct < MIN_CORRECT:
        return -1
    elif num_correct == MIN_CORRECT:
        return 0
    else:
        return 1
            
def run_binsearch(name, num_trials, min_examples, max_examples, correct, incorrect):
    orig_max = max_examples
    best = None
    searched = set([])

    def done(num_examples):
        if best is None:
            print('Failure! {} requires more than {} examples.'.format(name, orig_max))
            exit(-1)
        else:
            print('Success! {} requires {} examples.'.format(name, num_examples))
            exit(0)
    
    while True:
        num_examples = (max_examples + min_examples) // 2
        if num_examples in searched:
            done(num_examples)
        
        print('Running {} with {} examples...'.format(name, num_examples))
        results = run_repeated(name, num_trials, num_examples, incorrect)

        k = check_results(results, num_trials, correct)
        if k == 0:
            print('Success! {} requires {} examples.'.format(name, num_examples))
            exit(0)
        elif k > 0:
            if best is None:
                best = num_examples
            else:
                best = min(best, num_examples)
            max_examples = num_examples
        else:
            min_examples = num_examples
            
        if min_examples == max_examples:
            done(num_examples)
                
        searched.add(num_examples)

if __name__ == '__main__':
    # Read command line arguments.
    name = sys.argv[1]
    min_examples = int(sys.argv[2])
    max_examples = int(sys.argv[3])

    # Read pickle.
    with open(PICKLE_PATH, 'rb') as classifier_file:
        classifier = pickle.load(classifier_file)
        correct = classifier[0]
        incorrect = classifier[1]

    if name not in correct:
        print('{} has no correct results defined.'.format(name))
        exit(-1)

    run_binsearch(name, NUM_TRIALS, min_examples, max_examples, correct, incorrect)
