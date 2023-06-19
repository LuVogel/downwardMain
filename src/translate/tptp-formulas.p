fof(formula1, axiom,![X]:clear(X)).
fof(formula2, axiom,![X]: ![Y]:~on(X,Y)).
fof(formula3, axiom,![X]:ontable(X)).
fof(formula4, axiom,handempty(noargs)).
fof(formula5, axiom,![X]:~holding(X)).
fof(formula0, negated_conjecture,clear(a) & ontable(a) & handempty(noargs) & ontable(d)).
