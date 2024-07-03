% Déclaration des axiomes
% Axiome 1 : Les gens qui ne se rasent pas eux même sont rasés par tous les barbiers
# Pour tout x et y, ¬R(x,x) ⇒ B(y) ⇒ R(y,x)
fof(axiome1, axiom,
    ![X, Y] : ~(r(X,X) => (b(Y) => r(Y,X)))
).

% Axiome 2 : Les barbiers ne rasent que les gens qui ne se rasent pas eux même.
% Pour tout x et y, B(x) ⇒ R(x,y) ⇒ ¬R(y,y)
fof(axiome2, axiom,
    ![X, Y] : (b(X) => (r(X,Y) => (~ r(Y,Y))))
).


% Conjecture : Il n’existe pas de barbier dans ce village
% ¬(∃x, B(x))
fof(reflexivite,conjecture,
    ~ (?[X] : b(X))
).