fof(formula1, axiom,![X]: ![Y]:on(X,Y) | ontable(X) | holding(X)).
fof(formula2, axiom,![X]: ![Y]:on(X,Y) => ~clear(Y)).
fof(formula3, axiom,![X]:~on(X,X)).
fof(formula4, axiom,![X]: ![Y]:ontable(X) => clear(X) | on(Y,X)).
fof(formula0, conjecture,on(a,b) & on(b,c) => clear(a) & ~clear(b)).
