fof(formula1, axiom, ![X0]:  (object(X0) => ( clear(X0) ))).
fof(formula2, axiom, ![X0]:  (object(X0) => ( ontable(X0) ))).
fof(formula3, axiom, ![X0]:  (object(X0) => ( ~holding(X0) ))).
fof(formula4, axiom, ![X0]:  ![X1]:  (object(X1) => ( ~on(X0,X1) ))).
fof(formula5, axiom, ![X0]:  ![X1]:  (object(X0) => ( ~on(X0,X1) ))).
fof(formula0, negated_conjecture, (clear(a) & ontable(a) & handempty(noargs) & ontable(d))).