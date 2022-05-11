from weakest_pre import *

# small example

i, N, Z = Ints('i N Z')
a = Array('a', I, I)
b = Array('b', I, I)
write_bool = Bool('write_bool')
test1 = begin(set_(a, K(IntSort(), 0)),
              set_(b, K(IntSort(), 1)),
              set_(i, IntVal(0)),
              while_(i < N, 0 >= -N + -i,
                     if_(write_bool, set_(b, Store(b, Select(a, i), i)), set_(b, b)),
                     set_(i, i + 1)))

verify_fun(And(Z >= 0, Z <= N, N > 0), Select(b, Z) <= 1, test1)




# int __VERIFIER_nondet_int();

# int main() {
#   int i=0, x=0, y=0;
#   int n=__VERIFIER_nondet_int();
#   __VERIFIER_assume(n>0);
#   for(i=0; 1; i++)
#   {
#     __VERIFIER_assert(x==0);
#   }
#   __VERIFIER_assert(x==0);
# }

