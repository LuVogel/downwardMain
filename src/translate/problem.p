fof(formula1, axiom,handempty(noargs)).
fof(formula2, axiom,![X0]: ontable(X0)).
fof(formula3, axiom,![X0]: ~holding(X0)).
fof(formula4, axiom,![X0]: ![X1]: ~on(X0,X1)).
fof(formula5, axiom,![X0]: clear(X0)).
fof(formula0, negated_conjecture,clear(a) & ontable(a) & handempty(noargs) & clear(d)).






fof(formula0, negated_conjecture,clear(a) & ontable(a) & handempty(noargs) & ontable(d)).