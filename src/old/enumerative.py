import collections
from itertools import permutations
import z3

import util

def solve_concrete(initial, operators, examples, oracle):
    goal = tuple(ex['value'] for ex in examples)
    exp_set = collections.defaultdict(set)
    sig_set = set([])

    # Add initial expressions to the exp and sig sets.
    for expr in initial:
        sig = util.signature(expr, examples)
        if sig == goal:
            return expr
        sig_set.add(sig)
        exp_set[1].add(expr)

    i = 2
    while True:
        for op in operators:
            arity = operators[op]['arity']
            for p in util.m_partition(i - 1, arity):
                possible_children = set([]).union(*[exp_set[m] for m in p])
                for children in permutations(possible_children, r=arity):
                    new_expr = (op,) + children
                    oracle.examine()
                    sig = util.signature(new_expr, examples)
                    if sig not in sig_set:
                        sig_set.add(sig)
                        if sig == goal:
                            return new_expr
                        exp_set[sum(p) + 1].add(new_expr)
                        oracle.used_mem(util.sizeof_build_set(exp_set))
        i += 1

def solve(initial, operators, master, oracle):
    # Convert all bitvector literals to integers.
    initial = [util.try_bitvec(v) for v in initial]

    examples = []
    master_z3 = util.expr_to_z3(master)
    while True:
        expr = solve_concrete(initial, operators, examples, oracle)
        expr_z3 = util.expr_to_z3(expr)
        solved, model = oracle.check(expr_z3, master_z3)
        if solved:
            return expr
        else:
            model_dict = util.model_to_dict(model)
            examples.append({'model': model_dict,
                             'value': model.eval(master_z3).as_long()})
