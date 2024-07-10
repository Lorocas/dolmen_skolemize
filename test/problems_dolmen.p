fof(sk_simple_exists, axiom, p(c_1)).
fof(simple_forall, axiom, ! [X] : q(X)).

fof(exists_forall, conjecture, ? [X] : ! [Y] : r(X,Y)).
fof(sk_forall_exists, axiom, ! [X] : s(X,f_1(X))).
fof(sk_nested_quantifiers, axiom, ! [X] : ! [Z] : p(X,f_2(X),Z,f_3(X,Z))).
fof(sk_multiple_exists, axiom, (p(c_2) & q(c_3))).
fof(sk_exists_with_equality, axiom, (c_4 = a)).
fof(forall_with_implication, axiom, ! [X] : (p(X) => q(X))).
fof(sk_exists_in_antecedent, axiom, (p(c_5) => q(a))).
fof(forall_in_consequent, axiom, (p(a) => ! [X] : q(X))).

fof(complex_formula, conjecture, ! [X] : ? [Y] : (p(X,Y) & ! [Z] : (q(Z) => r(X,Y,Z)))).
