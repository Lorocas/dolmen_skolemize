% Déclaration des axiomes
% Axiome 1 : Pour tout x et y, R(x,y) => R(y,x)
fof(axiome1, axiom,
    ![X, Y] : (r(X,Y) => r(Y,X))
).

% Axiome 2 : Pour tout x et y et z, ((R(x,y) ^ R(y,z)) => R(x,z))
fof(axiome2, axiom,
    ![X, Y, Z] : ((r(X,Y) & r(Y,Z)) => r(X,Z))
).

% Axiome 3 : pour tout x, il existe y tq R(x,y)
% Note : ajout d'un attribut pour la skolémisation
fof(axiome3, axiom, 
   ![X] : ?[Y] : r(X,Y),
   to_be_skolemized(ax3_sk)
).


% ![X: element] : ?[Y: element] : r(X,Y)
% ![X] : r(X,ax3_sk(X))


% Conjecture : Montrer que pour tout x, R(x,x) (cas particulier : mq R(C,C))
fof(reflexivite,conjecture,
    r(c,c)
).