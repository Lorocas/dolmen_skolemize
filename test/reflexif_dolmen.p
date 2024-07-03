fof(axiome1, axiom, ! [X,Y] : (r(X,Y) => r(Y,X))).
fof(axiome2, axiom, ! [X,Y,Z] : ((r(X,Y) & r(Y,Z)) => r(X,Z))).
fof(sk_axiome3, axiom, ! [X] : r(X,f_1(X))).

fof(reflexivite, conjecture, r(c,c)).
