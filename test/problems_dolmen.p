fof(simple_exists, axiom, p(c_1)).
fof(simple_forall, axiom, ! [X] : q(X)).

fof(exists_forall, conjecture, ! [Y] : r(c_2,Y)).
fof(sk_forall_exists, axiom, ! [X] : s(X,f_1(X))).
fof(sk_nested_quantifiers, axiom, ! [X] : ! [Z] : p(X,f_2(X),Z,f_3(X,Z))).
fof(multiple_exists, axiom, (p(c_3) & q(c_4))).
fof(exists_with_equality, axiom, (c_5 = a)).
fof(forall_with_implication, axiom, ! [X] : (p(X) => q(X))).
fof(exists_in_antecedent, axiom, (p(c_6) => q(a))).
fof(forall_in_consequent, axiom, (p(a) => ! [X] : q(X))).

fof(complex_formula, conjecture, ! [X] : (p(X,f_4(X)) & ! [Z] : (q(Z) => r(X,f_4(X),Z)))).
