import util

FFFFFFFF = util.bitvec_to_int('#xFFFFFFFF')

def rewrite(expr, patterns):
    # Nothing will match on variables or constants.
    if type(expr) in (str, int):
        return expr
    
    # Attempt to rewrite all children.
    op, *children = (expr[0],) + tuple(rewrite(c, patterns) for c in expr[1:])
    
    # Attempt to rewrite this expression.
    if op in patterns:
        return patterns[op]((op,) + tuple(children))
    else:
        return (op,) + tuple(children)

# (bvadd x 0) -> x
# (bvadd 0 x) -> x
def rewrite_bvadd(expr):
    children = [c for c in expr[1:] if c != 0]
    if len(children) == 1:
        return children[0]
    else:
        return (expr[0],) + tuple(children)

# (bvmul x 1) -> x
# (bvmul 1 x) -> x
# (bvmul x 0) -> 0
# (bvmul 0 x) -> 0
def rewrite_bvmul(expr):
    children = [c for c in expr[1:] if c != 1]
    if 0 in children:
        return 0
    elif len(children) == 1:
        return children[0]
    else:
        return (expr[0],) + tuple(children)

# (bvand x '#x00000000') -> '#x00000000'
# (bvand '#x00000000' x) -> '#x00000000'
# (bvand x '#xFFFFFFFF') -> x
# (bvand '#xFFFFFFFF' x) -> x
def rewrite_bvand(expr):
    op, c1, c2 = expr
    if c1 == FFFFFFFF:
        return c2
    elif c2 == FFFFFFFF:
        return c1
    elif c1 == 0 or c2 == 0:
        return 0
    elif c1 == c2:
        return c1
    else:
        return expr

# (bvor x '#x00000000') -> x
# (bvor '#x00000000' x) -> x
# (bvor x '#xFFFFFFFF') -> '#xFFFFFFFF'
# (bvor '#xFFFFFFFF' x) -> '#xFFFFFFFF'
def rewrite_bvor(expr):
    children = [c for c in expr[1:] if c != 0]
    if FFFFFFFF in children:
        return FFFFFFFF
    elif len(children) == 1:
        return children[0]
    else:
        return (expr[0],) + tuple(children)

# (bvxor x '#x00000000') -> x
# (bvxor '#x00000000' x) -> x
# (bvor x '#xFFFFFFFF') -> '#xFFFFFFFF'
# (bvor '#xFFFFFFFF' x) -> '#xFFFFFFFF'
def rewrite_bvxor(expr):
    op, c1, c2 = expr
    if c1 == 0:
        return c2
    elif c2 == 0:
        return c1
    elif c1 == FFFFFFFF:
        return ('bvnot', c2)
    elif c2 == FFFFFFFF:
        return ('bvnot', c1)
    else:
        return expr

# (bvsub x 0) -> x
# (bvsub 0 x) -> (bvneg x)
def rewrite_bvsub(expr):
    op, c1, c2 = expr
    if c1 == 0:
        return ('bvneg', c2)
    elif c1 == FFFFFFFF:
        return ('bvnot', c2)
    elif c2 == 0:
        return c1
    else:
        return expr

# (bvashr x 0) -> x
def rewrite_bvashr(expr):
    op, c1, c2 = expr
    if c1 == FFFFFFFF:
        return FFFFFFFF
    elif c1 == 0:
        return 0
    elif c2 == 0:
        return c1
    else:
        return expr

# (bvlsh x 0) -> x
# (bvlsh x >=32) -> 0
def rewrite_bvlsh(expr):
    op, c1, c2 = expr
    if c2 == 0:
        return c1
    elif type(c2) is int and c2 >= 32:
        return 0
    else:
        return expr

# Handles both signed and unsigned remainder.
# (bvrem 0 x) -> 0
# (bvrem x 1) -> 0
# (bvrem x x) -> 0
# (bvrem x 0) -> x
def rewrite_bvrem(expr):
    op, c1, c2 = expr
    if c1 == 0 or c2 == 1 or c2 == c1:
        return 0
    elif c2 == 0:
        return c1
    else:
        return expr

# (bvsdiv x 1) -> x
# (bvsdiv x FFFFFFFF) -> (bvneg x)
# (bvsdiv x x) -> 1
# (bvsdiv 0 x) -> 0
def rewrite_bvsdiv(expr):
    op, c1, c2 = expr
    if c2 == 1:
        return c1
    elif c2 == FFFFFFFF:
        return ('bvneg', c1)
    elif c2 == c1:
        return 1
    elif c1 == 0:
        return 0
    else:
        return expr    

# (bvudiv x 1) -> x
# (bvudiv x 0) -> FFFFFFFF
# (bvudiv x x) -> 1
# (bvudiv 0 x) -> 0
def rewrite_bvudiv(expr):
    op, c1, c2 = expr
    if c2 == 1:
        return c1
    elif c2 == 0:
        return FFFFFFFF
    elif c2 == c1:
        return 1
    elif c1 == 0:
        return 0
    else:
        return expr    

# (bvnot (bvnot x)) -> x
def rewrite_bvnot(expr):
    op, c = expr
    if type(c) == tuple:
        sub_op, *sub_c = c
        if sub_op == 'bvnot':
            return sub_c[0]
        else:
            return expr
    else:
        return expr

# (bvneg (bvneg x)) -> x
def rewrite_bvneg(expr):
    op, c = expr
    if type(c) == tuple:
        sub_op, *sub_c = c
        if sub_op == 'bvneg':
            return sub_c[0]
        else:
            return expr
    else:
        return expr

BITVECTOR_PATTERNS = {
    'bvadd': rewrite_bvadd,
    'bvsub': rewrite_bvsub,
    'bvmul': rewrite_bvmul,
    'bvand': rewrite_bvand,
    'bvor': rewrite_bvor,
    'bvxor': rewrite_bvxor,
    'bvshl': rewrite_bvlsh,   # Logical shift left
    'bvlshr': rewrite_bvlsh,  # Logical shift right
    'bvashr': rewrite_bvashr, # Arithmetical shift right
    'bvurem': rewrite_bvrem,
    'bvsrem': rewrite_bvrem,
    'bvudiv': rewrite_bvudiv,
    'bvsdiv': rewrite_bvsdiv,
    'bvnot': rewrite_bvnot,
    'bvneg': rewrite_bvneg,
}
