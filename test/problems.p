%----Test file for TPTP skolemization
%----Contains various formulas to test skolemization process

fof(simple_exists, axiom,
    ? [X] : (p(X))).

fof(simple_forall, axiom,
    ! [X] : (q(X))).

fof(exists_forall, conjecture,
    ? [X] : (! [Y] : (r(X, Y)))).

fof(forall_exists, axiom,
    ! [X] : (? [Y] : (s(X, Y)))).

fof(nested_quantifiers, axiom,
    ! [X] : (? [Y] : (! [Z] : (? [W] : p(X, Y, Z, W))))).

fof(multiple_exists, axiom,
    ? [X, Y] : (p(X) & q(Y))).

fof(exists_with_equality, axiom,
    ? [X] : (X = a)).

fof(forall_with_implication, axiom,
    ! [X] : (p(X) => q(X))).

fof(exists_in_antecedent, axiom,
    (? [X] : p(X)) => q(a)).

fof(forall_in_consequent, axiom,
    p(a) => (! [X] : q(X))).

fof(complex_formula, conjecture,
    ! [X] : (? [Y] : (p(X, Y) & (! [Z] : (q(Z) => r(X, Y, Z)))))).