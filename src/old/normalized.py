import collections
from itertools import combinations, permutations
import z3

from rewrite import rewrite, BITVECTOR_PATTERNS
import util

def solve(initial, operators, master, oracle):
    unconverted_initial = initial

    # Convert all bitvector literals to integers.
    initial = [util.try_bitvec(v) for v in initial]

    goal = ()
    examples = []
    expr_set = collections.defaultdict(set)
    master_z3 = util.expr_to_z3(master)
        
    # Add initial expressions to exp_set.
    for expr in initial:
        # Check expression signature before going to the solver.
        sig = util.signature(expr, examples)
        if sig == goal:
            solved, model = oracle.check(util.expr_to_z3(expr), master_z3)
            if solved:
                return expr

            model_dict = util.model_to_dict(model)
            model_val = model.eval(master_z3).as_long()
            goal += (model_val,)
            examples.append({'model': model_dict, 'value': model_val})
        expr_set[1].add(expr)
        
    i = 2
    while True:
        for op in operators:
            arity = operators[op]['arity']
            for p in util.m_partition(i - 1, arity):
                possible_children = set([]).union(*[expr_set[m] for m in p])
                if operators[op]['commut']:
                    children_list = combinations(possible_children, arity)
                else:
                    children_list = permutations(possible_children, arity)

                for children in children_list:
                    expr = expand((op,) + children)
                    compressed_expr = compress(expr)
                    
                    # Do not add new constants to the build set.
                    if type(compressed_expr) is int and \
                       compressed_expr not in initial:
                        continue

                    if compressed_expr not in expr_set[sum(p) + 1]:
                        print(compressed_expr)
                        oracle.examine()
                        # print(compressed_expr)
                        sig = util.signature(expr, examples)
                        if sig == goal:
                            solved, model = oracle.check(util.expr_to_z3(expr), 
                                                         master_z3)
                            if solved:
                                return expr

                            model_dict = util.model_to_dict(model)
                            model_val = model.eval(master_z3).as_long()
                            goal += (model_val,)
                            examples.append({'model': model_dict, 
                                             'value': model_val})
                        expr_set[sum(p) + 1].add(compressed_expr)
                        oracle.used_mem(util.sizeof_build_set(expr_set))
    
        # Eliminate redundant trees from expr_set[i + 1].
        # print('Searched all trees of size <= {}'.format(i + 1))
        # print('Compressing...')
        # for expr in expr_set[i + 1]:
        #     expr = expand(expr)
        #     # smaller_expr = solve(unconverted_initial, operators, expr, oracle)
        #     print('{} -> {}'.format(expr, None))
        i += 1

# def solve(initial, operators, master, oracle):
#     # Convert all bitvector literals to integers.
#     initial = [util.try_bitvec(v) for v in initial]

#     candidates = set(initial)
#     build_set = set(initial)
#     master_z3 = util.expr_to_z3(master)

#     examples = []
#     goal = ()

#     while True:
#         # Check all candidates.
#         for unexpanded_c in candidates:
#             candidate = expand(unexpanded_c)
#             print('E: {}'.format(candidate))
#             oracle.examine()

#             # Check expression signature before going to the solver.
#             sig = util.signature(candidate, examples)
#             if sig != goal:
#                 continue

#             print('C: {}'.format(candidate))

#             solved, model = oracle.check(util.expr_to_z3(candidate), master_z3)
#             if solved:
#                 return candidate
#             else:
#                 model_dict = util.model_to_dict(model)
#                 model_val = model.eval(master_z3).as_long()

#                 goal += (model_val,)
#                 examples.append({'model': model_dict, 'value': model_val})

#         # Generate new candidates.
#         candidates = explore(build_set, operators)
#         build_set |= candidates
        
# def explore(initial, operators):
#     ret = set([])
#     for op in operators:
#         if operators[op]['commut']:
#             children_list = combinations(initial, operators[op]['arity'])
#         else:
#             children_list = permutations(initial, operators[op]['arity'])
#         for children in children_list:
#             expr = (op,) + children
#             ret.add(compress(expand(expr)))
#     return ret

def compress(expr):
    expr = fold_constants(expr)
    expr = rewrite(expr, BITVECTOR_PATTERNS)

    if type(expr) in (str, int):
        return expr
    
    op, *children = expr
    new_children = []

    for child in children:
        if type(child) in (str, int):
            new_children.append(child)
        else:
            child_op, *grandchildren = compress(child)
            if child_op == op and util.ALL_OPERATORS[op]['assoc']:
                new_children += list(grandchildren)
            else:
                new_children.append((child_op,) + tuple(grandchildren))

    if util.ALL_OPERATORS[op]['commut']:
        return (op,) + tuple(sorted(new_children, key=hash))
    else:
        return (op,) + tuple(new_children)

def expand(expr):
    if type(expr) in (str, int):
        return expr

    op, *children = expr
    arity = util.ALL_OPERATORS[op]['arity']
    if len(children) > arity:
        return (op,) + tuple(expand(c) for c in children[:arity - 1]) + \
               (expand((op,) + tuple(children[arity - 1:])),)
    else:
        return (op,) + tuple(expand(c) for c in children)

def fold_constants(expr):
    if type(expr) in (str, int):
        return expr
    
    op, *args = expr
    if all([type(a) == int for a in args]):
        z3_expr = util.expr_to_z3(expr)
        simplified_expr = z3.simplify(z3_expr)
        assert type(simplified_expr) == z3.BitVecNumRef
        return simplified_expr.as_long()
    else:
        return (op,) + tuple(fold_constants(a) for a in args)

