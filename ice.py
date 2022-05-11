from z3 import Bool, Implies, And, Or, Not, Int, Solver, IntNumRef, Array, IntSort
from collections import defaultdict
'''
ICE Learning example:


given a few preconditions, want to try to synthesize an invariant

here are the preconditions  (i guess we can think of this as initial state):

p >= 25
p < 75
a[p] == 1
i = 0
j = 0

post condition:

j == 1

trans relation (loop):
if a[i] == 1 -> j = 1
else i++, a == a, j == j
'''

class Teacher:

    def __init__(self, all_vars, pre_condition, post_condition):
        pass

    def check_invariant(self, inv):
        pass

i, j, p, a = Int('i'), Int('j'), Int('p'), Array('a', IntSort(), IntSort())
Teacher(['i', 'j', 'p', 'a'], [i >= 25, p < 75, a[p] == 1, i == 0, j == 0], j == 1)

class Learner:
    def __init__(self, all_vars, num_disjuncts, num_conjuncts, upper_bound):
        self.all_vars = all_vars
        self.num_vars = len(self.all_vars)
        self.num_to_var_str = self.num_to_var_str_gen()

        self.num_disjuncts = num_disjuncts # i in the paper
        self.num_conjuncts = num_conjuncts # j in the paper
        self.upper_bound = upper_bound

        self.examples = []
        self.counterexamples = []
        self.implication_pairs = []

        self.datapoint_bools = []
        self.solving_for = defaultdict(set)

    def add_example(self, ex):
        self.examples.append(ex)

    def add_counterexample(self, cex):
        self.counterexamples.append(cex)

    def add_implication_pair(self, i1, i2):
        self.implication_pairs.append((i1, i2))

    def run_solver(self):
        form = self.construct_full_smt_formula()
        s = Solver()
        s.add(form)
        if str(s.check()) == 'sat':
            self.cur_model = s.model()
            # d = {}
            # for i in self.cur_model:
            #     d[str(i)] = self.cur_model[i]
            # for i in sorted(d.keys()):
            #     print(f"{i}: {d[i]}")
            return self.get_invariant_structure()
        else:
            # paper says 'dovetail' between the 2 not sure how to do that
            print('have to change c or change disjunct, conjunct structure')

    def get_invariant_structure(self):
        disjuncts = []
        for d in range(self.num_disjuncts):
            conjuncts = []
            for c in range(self.num_conjuncts):
                s = f"d{d}_c{c}"
                var_dict = {}
                for i in self.solving_for[s]:
                    print(i)
                    print(d)
                    v = self.cur_model[i]
                    if 's1' in str(i):
                        var_dict['s1'] = v
                    elif 's2' in str(i):
                        var_dict['s2'] = v
                    elif 'v1' in str(i):
                        var_dict['v1'] = self.num_to_z3_var(v)
                    elif 'v2' in str(i):
                        var_dict['v2'] = self.num_to_z3_var(v)
                    elif 'c_' in str(i):
                        var_dict['c'] = v
                    else:
                        raise ValueError(f'invalid `solving for` key: {i}')
                print(f'here: {var_dict}')
                conjuncts.append((var_dict['s1'] * var_dict['v1']) + (var_dict['s2'] * var_dict['v2']) <= var_dict['c']) # fundamental structure
            disjuncts.append(And(conjuncts))
        return Or(disjuncts)


    def num_to_var_str_gen(self):
        d = {}
        for i, var_str in enumerate(self.all_vars):
            d[i] = var_str
        return d

    def num_to_z3_var(self, num):
        if isinstance(num, IntNumRef):
            num = int(str(num))
        return Int(self.num_to_var_str[num])

    def construct_full_smt_formula(self):
        formula = []
        formula.append(self.conjuncts_for_examples())
        formula.append(self.conjuncts_for_cex())
        formula.append(self.conjuncts_for_implications())
        formula.append(self.conjuncts_for_dps())
        formula.append(self.generate_bij_equality())
        formula.append(self.generate_all_c_in_bounds())
        formula.append(self.generate_multiplication())
        formula.append(self.generate_var_values_with_datapoints())
        formula.append(self.generate_multiplier_values())
        formula.append(self.generate_var_nums())
        formula = And(formula)
        return formula

    def conjuncts_for_examples(self):
        # first on line 1
        ex_bools = []
        for i, dp in enumerate(self.examples):
            var_dict = dp
            ex_bool = Bool(f'example_{i}')
            self.datapoint_bools.append([ex_bool, var_dict])
            ex_bools.append(ex_bool)
        return And(ex_bools)

    def conjuncts_for_cex(self):
        # second on line 1
        cex_bools = []
        for i, dp in enumerate(self.counterexamples):
            var_dict = dp
            cex_bool = Bool(f'cex_{i}')
            cex_bools.append(Not(cex_bool))
            self.datapoint_bools.append([cex_bool, var_dict])
        return And(cex_bools)

    def conjuncts_for_implications(self):
        # third on line 1
        imp_bools = []
        for i, dp in enumerate(self.implication_pairs):
            var_dict_lhs = dp[0]
            var_dict_rhs = dp[1]
            imp_bool_lhs = Bool(f'impl_{i}_lhs')
            imp_bool_rhs = Bool(f'impl_{i}_rhs')
            self.datapoint_bools.append([imp_bool_lhs, var_dict_lhs])
            self.datapoint_bools.append([imp_bool_rhs, var_dict_rhs])
            imp_bool = Implies(imp_bool_lhs, imp_bool_rhs)
            imp_bools.append(imp_bool)
        return And(imp_bools)

    def conjuncts_for_dps(self):
        # last on line 1
        conjuncts = []
        for i, dp in enumerate(self.datapoint_bools):
            disjuncts = []
            for d in range(self.num_disjuncts):
                inner_conjuncts = []
                for c in range(self.num_conjuncts):
                    b = Bool(f"b_p{i}_c{c}_d{d}")
                    inner_conjuncts.append(b)
                disjuncts.append(And(inner_conjuncts))
            conjuncts.append(dp[0] == Or(disjuncts))
        return And(conjuncts)

    def generate_bij_equality(self): # change to include all DPs
        # first on line 2
        equalities = []
        for i, dp in enumerate(self.datapoint_bools):
            for d in range(self.num_disjuncts):
                for conj in range(self.num_conjuncts):
                    b = Bool(f"b_p{i}_d{d}_c{conj}")
                    c = Int(f"c_d{d}_c{conj}")
                    r1 = Int(f"r1_p{i}_d{d}_c{conj}")
                    r2 = Int(f"r2_p{i}_d{d}_c{conj}")
                    equality = b == ((r1 + r2) <= c)
                    equalities.append(equality)
        return And(equalities)

    def generate_all_c_in_bounds(self):
        # middle of line 2
        constraints = []
        for d in range(self.num_disjuncts):
            for nc in range(self.num_conjuncts):
                c = Int(f"c_d{d}_c{nc}")
                b1 = c >= -self.upper_bound # -M
                b2 = c <= self.upper_bound # M
                constraint = And(b1, b2)
                constraints.append(constraint)
                self.solving_for[f"d{d}_c{nc}"].add(c)
        return And(constraints)

    def generate_multiplication(self):
        # last on line 2
        conjuncts = []
        for i, dp in enumerate(self.datapoint_bools):
            for nd in range(self.num_disjuncts):
                for c in range(self.num_conjuncts):
                    for k in range(1, 3):
                        r = Int(f"r{k}_p{i}_d{nd}_c{c}")
                        d = Int(f"d{k}_p{i}_d{nd}_c{c}")
                        s = Int(f"s{k}_d{nd}_c{c}")
                        b1 = Implies(s == 0, r == 0)
                        b2 = Implies(s == 1,  r == d)
                        b3 = Implies(s == -1, r == -d)
                        conjunct = And(b1, b2, b3)     # This might not be correct, the paper doesn't specify which operator to use
                        conjuncts.append(conjunct)
                        self.solving_for[f"d{nd}_c{c}"].add(s)
        return And(conjuncts)


    def generate_var_values_with_datapoints(self):
        # first on line 3
        conjuncts = []
        for i, dp in enumerate(self.datapoint_bools):
            var_dict = dp[1]
            for nd in range(self.num_disjuncts):
                for c in range(self.num_conjuncts):
                    for k in range(1, 3):
                        v = Int(f"v{k}_d{nd}_c{c}")
                        self.solving_for[f"d{nd}_c{c}"].add(v)
                        d = Int(f"d{k}_p{i}_d{nd}_c{c}")
                        for l in range(self.num_vars):
                            conjuncts.append(Implies(v == l, d == var_dict[self.num_to_var_str[l]]))
        return And(conjuncts)

    def generate_multiplier_values(self):
        # second on line 3
        conjuncts = []
        for d in range(self.num_disjuncts):
            for c in range(self.num_conjuncts):
                for k in range(1, 3):
                    s = Int(f"s{k}_d{d}_c{c}")
                    b1 = s >= -1
                    b2 = s <= 1
                    conjunct = And(b1, b2)
                    conjuncts.append(conjunct)
        return And(conjuncts)

    def generate_var_nums(self):
        # third and last on line 3
        conjuncts = []
        for d in range(self.num_disjuncts):
            for c in range(self.num_conjuncts):
                for k in range(1, 3):
                    v = Int(f"v{k}_d{d}_c{c}")
                    b1 = v >= 0
                    b2 = v <= self.num_vars - 1 # n in paper
                    conjunct = And(b1, b2)
                    conjuncts.append(conjunct)
                v1 = Int(f"v1_d{d}_c{c}")
                v2 = Int(f"v2_d{d}_c{c}")
                not_equal = v1 != v2
                conjuncts.append(not_equal)
        return And(conjuncts)


num_disjuncts = 2
num_conjuncts = 1
upper_bound = 5
l = Learner(['i', 'j', 'p'], num_disjuncts, num_conjuncts, upper_bound)

l.add_example({'i': 0, 'j': 0, 'p': 25})
l.add_example({'i': 1, 'j': 0, 'p': 25})
l.add_example({'i': 1, 'j': 1, 'p': 25})
l.add_example({'i': 25, 'j': 25, 'p': 25})
l.add_example({'i': 26, 'j': 1, 'p': 25})
l.add_example({'i': 50, 'j': 51, 'p': 51})
l.add_example({'i': 53, 'j': 1, 'p': 51})
l.add_example({'i': 54, 'j': 1, 'p': 51})
l.add_example({'i': 55, 'j': 1, 'p': 51})

l.add_counterexample({'i': 100, 'j': 0, 'p': 25})
l.add_counterexample({'i': 100, 'j': 2, 'p': 25})
l.add_counterexample({'i': 98, 'j': 5, 'p': 25})
l.add_counterexample({'i': 99, 'j': 0, 'p': 25})
l.add_counterexample({'i': 99, 'j': 2, 'p': 25})


l.add_implication_pair({'i': 50, 'j': 0, 'p': 25}, {'i': 51, 'j': 0, 'p': 25})
l.run_solver()


# lSmall = Learner(['i', 'Z', 'N'], 5, num_conjuncts, upper_bound)
# lSmall.add_example({'i': 0, 'Z': 0, 'N': 1})
# lSmall.add_example({'i': 0, 'Z': 0, 'N': 10})

# lSmall.add_counterexample({'i': 0, 'Z': 0, 'N': 1})
# lSmall.add_counterexample({'i': 0, 'Z': 0, 'N': 1})
# lSmall.run_solver()
