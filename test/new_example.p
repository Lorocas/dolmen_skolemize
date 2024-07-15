% NOTE: the parser doesn't work on this example!
fof(axiom_A, axiom,
    ![X] : (?[Y] : p(X,s(Y)))
).

fof(tran_ax, axiom,
    ![X, Y, Z] : (p(X,Y) => (p(Y,Z) => p(X,Z)))
).

fof(congr_ax, axiom, 
   ![X, Y] : (p(X,Y) => p(s(X),s(Y)))
).

fof(goal_ax, conjecture,
    ?[B] : (p(A, s(s(B))))
).