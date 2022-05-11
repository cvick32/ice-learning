from z3 import *
import inspect

def set_(v, e):
    return lambda post: substitute(post, (v, e)) # set

def seq(s1, s2):
    return lambda post: s1(s2(post)) # se1

def begin(*program_statements):
    def begin_res(post):
        wp = post
        for statement in reversed(program_statements):
            print(f"arg: {inspect.getsource(statement)}")
            wp = statement(wp)
            print(f"new weakest precondition: {wp}")
        return wp
    return begin_res

def if_(cond, t, e):
    return lambda post: Or(Implies(cond, t(post)), And(Not(cond), e(post))) # if

skip = lambda post: post
abort = lambda post: BoolVal(False)

def assert_(prop):
    return lambda post: And(post, prop)

def assume_(prop):
    return lambda post: Implies(prop, post)

def is_var(expr):
    # it's a var if it has no children and is alpha
    return str(expr).isalpha()

def get_vars_help(expr, cur_vars):
    if expr.children():
        for child in expr.children():
            get_vars_help(child, cur_vars)
    else:
        if is_var(expr):
            cur_vars.append(expr)

def get_vars(expr):
    vs = []
    get_vars_help(expr, vs)
    return vs


def while_(cond, inv, *body):
    def while_res(post):
        vs = list(get_vars(post))
        return And(inv, ForAll(vs, And(Implies(And(cond, inv), begin(*body)(inv)),
                                       Implies(And(Not(cond), inv), post))))
    return while_res

def debug(post):
    print(post)
    return post

def verify_fun(pre, post, body):
    final = Implies(pre, body(post))
    print(final)
    prove(final)

I = IntSort()

# example from paper

# i, j, p = Ints('i j p')
# a = Array('a', I, I)
# ice_example = begin(set_(i, IntVal(0)),
#                     set_(j, IntVal(0)),
#                     while_(i < 100, j != j,
#                            if_(Select(a, i) == 1, set_(j, IntVal(1)), set_(j, j)),
#                            set_(i, i + 1)))

# verify_fun(And(p >= 25, p < 75, Select(a, p) == 1), j == 1, ice_example)

# j, k, menor, N = Ints('j k menor N')
# arr = Array('arr', IntSort(), IntSort())
# array_safe = \
#     begin(set_(N, IntVal(1)),
#           set_(j, IntVal(0)),
#           while_(j < N, j == 0,
#                  set_(arr, Store(arr, j, k)),
#                  if_(Select(arr, j) <= menor,
#                      set_(menor, Select(arr, j)),
#                      set_(menor, menor))))

# verify_fun(True, Select(arr, 0) >= menor, array_safe)

# term 2

# x, y, z = Ints('x y z')
# temp = Bool('temp')

# term2 = begin(while_(And(x < 100, z < 100), x == x,
#                      if_(temp, set_(x, x + 1), set_(x, x - 1)),
#                      if_(temp, set_(x, x + 1), set_(z, z - 1))))

# verify_fun(True, Or(x >= 100, z <= 100), term2)


# sn, loop1, n1, x = Ints('sn loop1 n1 x')

# sum3 = begin(set_(sn, IntVal(0)),
#              while_(True


# small example
# i, N, Z = Ints('i N Z')
# a = Array('a', I, I)
# b = Array('b', I, I)
# write_bool = Bool('write_bool')
# test1 = begin(set_(a, K(IntSort(), 0)),
#               set_(b, K(IntSort(), 1)),
#               set_(i, IntVal(0)),
#               while_(i < N, i == i,
#                      if_(write_bool, set_(b, Store(b, Select(a, i), i)), set_(b, b)),
#                      set_(i, i + 1)))

# verify_fun(And(Z >= 0, Z <= N, N > 0), Select(b, Z) <= 1, test1)






# def twosort(a, b):
#     if b < a:
#         temp = a
#         a = b
#         b = temp
#     else:
#         pass
#     return a, b

# a, b, c, d, temp = Ints("a b c d temp")
# prog1 = \
#     if_(b < a,
#         begin(
#             set_(temp, a),
#             set_(a, b),
#             set_(b, temp)),
#         skip)


# prog2 = \
#     begin(
#         set_(c, d - c),
#         set_(d, d - c),
#         set_(c, c + d))


# def square(n):
#     a = 0
#     i = 0
#     while i < n:
#         assert a == n * i
#         i = i + 1
#         a = a + n
#     return a

# i, n = Ints('i n')
# sq = begin(
#     set_(a, IntVal(0)),
#     set_(i, IntVal(0)),
#     while_(i < n, And(i < (n + 1), 0 <= i, a == n * i),
#            set_(i, i + 1),
#            set_(a, a + n)))

# #verify_fun(n >= 0, a == n * n, sq)



# sumn = Function("sumn", IntSort(), IntSort())
# sumndef = ForAll([a], sumn(a) == If(a <= 0, 0, sumn(a - 1) + a))

# sumn_prog = \
#     begin(set_(i, IntVal(0)),
#           while_(i != n + 1, a == sumn(i),
#                  set_(i, i + 1),
#                  set_(a, a + 1)))

# verify_fun(And(sumndef, n >= 0), sumn(n) == a, sumn_prog)
