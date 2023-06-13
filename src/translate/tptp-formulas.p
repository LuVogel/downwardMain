fof(formula1, axiom,handempty(noargs)).
fof(formula2, axiom,![X]:clear(X)).
fof(formula3, axiom,![X]:~holding(X)).
fof(formula4, axiom,![X]: ![Y]:~on(X,Y)).
fof(formula5, axiom,![X]:ontable(X)).
fof(formula0, negated_conjecture,clear(a) & ontable(a) & handempty(noargs)).
