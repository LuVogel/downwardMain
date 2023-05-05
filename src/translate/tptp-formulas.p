fof(init, axiom,clear(b) & ontable(d) & handempty() & clear(c) & ontable(b) & ontable(c) & clear(a) & clear(d) & ontable(a) & =(d,d) & =(b,b) & =(a,a) & =(c,c)).
fof(goal, conjecture,on(d,c) & on(c,b) & on(b,a)).
fof(formula, conjecture,on(x,y) & handempty()).
fof(formula, conjecture,on(a,d) & on(d,c) & on(a,c)).
