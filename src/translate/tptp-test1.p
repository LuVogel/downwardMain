% jeder Block ist entweder auf einem anderen Block, auf dem Tisch oder in der Hand
fof(test_1, axiom, ![X]:
                   ![Y]:
                   on(X,Y) | ontable(X) | holding(X) ).
% jeder Block der nicht frei ist, hat einen Block aus sich drauf
fof(test_2, axiom, ![X]:
                    ?[Y]:
                    on(X,Y) => ~ clear(X) ).
% kein Block kann auf sich selbst sein
fof(test_3, axiom, ![X]: ~ on(X,X) ).

% wenn ein Block on table ist, dann ist er entweder frei oder ein andere block liegt auf ihm
fof(test_4, axiom, ![X]:
                   ![Y]: ontable(X) => clear(X) | on(X, Y) ).

fof(test, conjecture, on(a,b) & on(b,c) => ~ clear(a) & ~ clear(b) ).



fof(formula1, axiom,![X]: ![Y]:on(X,Y) | ontable(X) | holding(X)).
fof(formula2, axiom,![X]: ![Y]:on(X,Y) => ~ clear(X)).
fof(formula3, axiom,![X]:~ on(X,X)).
fof(formula4, axiom,![X]: ![Y]:ontable(X) => clear(X) | on(X,Y)).
fof(formula0, conjecture,on(a,b) & on(b,c) => clear(a) & clear(b)).

% Running in auto input_syntax mode. Trying TPTP
% SZS status CounterSatisfiable for tptp-formulas
% # SZS output start Saturation.
cnf(u31,axiom,
    ~on(sK0,sK1)).

cnf(u43,negated_conjecture,
    ~clear(b)).

cnf(u26,negated_conjecture,
    on(b,c)).

cnf(u25,negated_conjecture,
    on(a,b)).

cnf(u24,axiom,
    ~on(X0,X0)).

% # SZS output end Saturation.
% ------------------------------
% Version: Vampire 4.7 (commit 807e37dd9 on 2022-08-23 09:55:27 +0200)
% Linked with Z3 4.8.13.0 f03d756e086f81f2596157241e0decfb1c982299 z3-4.8.4-5390-gf03d756e0
% Termination reason: Satisfiable

% Memory used [KB]: 4989
% Time elapsed: 0.081 s
% ------------------------------
% ------------------------------


Das folgende geht nicht, da nicht alle Fälle beachtet:
Es gibt ein fall dass clear(a) gilt und es gibt auch ein Fall dass ~clear(a) gilt.
Was vampire aber nicht erkennt: clear(b) ist nicht möglich, da wenn on(a,b) dan musss ~clear(b) sein.
vampire erkennet beide inputs als satisfiable an aber mit CounterSatisfiable


vampire problem.p --statistics full?
vampire --show_options on

fof(formula1, axiom,![X]: ![Y]:on(X,Y) | ontable(X) | holding(X)).
fof(formula2, axiom,![X]: ![Y]:on(X,Y) => ~clear(Y)).
fof(formula3, axiom,![X]:~on(X,X)).
fof(formula4, axiom,![X]: ![Y]:ontable(X) => clear(X) | on(Y,X)).
fof(formula0, conjecture,on(a,b) & on(b,c) => ~clear(a) & clear(b)).

fof(formula1, axiom,![X]: ![Y]:on(X,Y) | ontable(X) | holding(X)).
fof(formula2, axiom,![X]: ![Y]:on(X,Y) => ~clear(Y)).
fof(formula3, axiom,![X]:~on(X,X)).
fof(formula4, axiom,![X]: ![Y]:ontable(X) => clear(X) | on(Y,X)).
fof(formula0, conjecture,on(a,b) & on(b,c) => clear(a) & ~clear(b)).

