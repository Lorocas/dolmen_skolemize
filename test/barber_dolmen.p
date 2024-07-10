fof(axiome1, axiom, ! [X,Y] : ~ (r(X,X) => (b(Y) => r(Y,X)))).
fof(axiome2, axiom, ! [X,Y] : (b(X) => (r(X,Y) => ~ r(Y,Y)))).

fof(reflexivite, conjecture, ~ ? [X] : b(X)).
