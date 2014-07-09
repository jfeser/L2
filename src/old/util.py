import datetime
import re
import sys
import z3

ALL_OPERATORS = {'bvadd': {'commut': True,  'assoc': True,
                           'arity': 2, 'method': lambda x, y: x + y},
                 'bvsub': {'commut': False, 'assoc': False,
                           'arity': 2, 'method': lambda x, y: x - y},
                 'bvmul': {'commut': True, 'assoc': True,
                           'arity': 2, 'method': lambda x, y: x * y},
                 'bvsdiv': {'commut': False, 'assoc': False,
                            'arity': 2, 'method': lambda x, y: x / y},
                 'bvudiv': {'commut': False, 'assoc': False,
                            'arity': 2, 'method': z3.UDiv},
                 'bvurem': {'commut': False, 'assoc': False,
                            'arity': 2, 'method': z3.URem},
                 'bvsrem': {'commut': False, 'assoc': False,
                            'arity': 2, 'method': z3.SRem},
                 'bvneg': {'commut': False, 'assoc': False,
                           'arity': 1, 'method': lambda x: -x},
                 'bvand': {'commut': True, 'assoc': True,
                           'arity': 2, 'method': lambda x, y: x & y},
                 'bvor': {'commut': True, 'assoc': True,
                          'arity': 2, 'method': lambda x, y: x | y},
                 'bvxor': {'commut': True, 'assoc': True,
                           'arity': 2, 'method': lambda x, y: x ^ y},
                 'bvnot': {'commut': False, 'assoc': False,
                           'arity': 1, 'method': lambda x: ~x},
                 'bvshl': {'commut': False, 'assoc': False,
                           'arity': 2, 'method': lambda x, y: x << y},
                 'bvashr': {'commut': False, 'assoc': False,
                            'arity': 2, 'method': lambda x, y: x >> y},
                 'bvlshr': {'commut': False, 'assoc': False,
                            'arity': 2, 'method': z3.LShR},
                 'bvugt': {'commut': False, 'assoc': False,
                           'arity': 2, 'method': z3.UGT},
                 'bvule': {'commut': False, 'assoc': False,
                           'arity': 2, 'method': z3.ULE}}

def size(expr):
    if type(expr) in (int, str):
        return 1
    else:
        return 1 + sum(size(c) for c in expr[1:])

def partition(number):
    answer = set()
    answer.add((number, ))
    for x in range(1, number):
        for y in partition(number - x):
            answer.add(tuple(sorted((x, ) + y)))
    return answer

def m_partition(n, m):
    return [p for p in partition(n) if len(p) == m]

def model_to_dict(model):
    return {var.name(): model[var].as_long() for var in model}

def model_dict_eval(expr, model_dict):
    pairs = [(z3.BitVec(var, 32), z3.BitVecVal(model_dict[var], 32))\
             for var in model_dict]
    sub = z3.substitute(expr, *pairs)
    val = z3.simplify(sub)
    try:
        return val.as_long()
    except:
        pass

def signature(expr, examples):
    z3_expr = expr_to_z3(expr)
    return tuple(model_dict_eval(z3_expr, ex['model']) for ex in examples)

def expr_to_z3(expr):
    # Treat integers as bitvector literals.
    if type(expr) == int:
        return z3.BitVecVal(expr, 32)
    
    # Treat strings as a variable name.
    if type(expr) == str:
        # Try to parse strings as bitvector literals.
        val = bitvec_to_int(expr)
        if val:
            return z3.BitVecVal(val, 32)
        return z3.BitVec(expr, 32)

    op, *args = expr
    args = [expr_to_z3(a) for a in args]
    assert len(args) == ALL_OPERATORS[op]['arity'],\
        '{} takes {} arguments but {} were given.'\
            .format(op, ALL_OPERATORS[op]['arity'], len(args))
    return ALL_OPERATORS[op]['method'](*args)

def bitvec_to_int(bitvec_str):
    if re.match('#x', bitvec_str) is None:
        return None
    else:
        return int(bitvec_str[2:], base=16)

def try_bitvec(bv_str):
    val = bitvec_to_int(bv_str)
    if val is not None:
        return val
    else:
        return bv_str

def sizeof_build_set(bset):
    size = sys.getsizeof(bset)
    for expr_size in bset:
        size += sys.getsizeof(bset[expr_size])
        for expr in bset[expr_size]:
            size += sys.getsizeof(expr)
    return size

class Oracle(object):
    def __init__(self):
        self._examine_count = 0
        self._times = []
        self._mem = []

    def used_mem(self, num_bytes):
        self._mem.append(num_bytes)

    def examine(self):
        self._examine_count += 1

    def check(self, candidate, master):
        s = z3.Solver()
        s.add(candidate != master)

        start = datetime.datetime.now()
        is_sat = s.check() == z3.sat
        end = datetime.datetime.now()
        self._times.append(end - start)

        if is_sat:
            return False, s.model()
        else:
            return True, None

    def get_stats(self):
        return {
            'avg_time': sum(self._times, datetime.timedelta()) / len(self._times),
            'min_time': min(self._times),
            'max_time': max(self._times),
            'avg_mem': sum(self._mem) / len(self._mem),
            'min_mem': min(self._mem),
            'max_mem': max(self._mem),
            'solve_count': len(self._times),
            'examine_count': self._examine_count,
        }
