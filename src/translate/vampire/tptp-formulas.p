tff(type_dec1, type, object: $tType).
tff(on_decl, type, on: (object * object) > $o).
tff(ontable_decl, type, ontable: object > $o).
tff(clear_decl, type, clear: object > $o).
tff(handempty_decl, type, handempty: $o).
tff(holding_decl, type, holding: object > $o).
tff(equal_decl, type, equal: (object * object) > $o).
tff(formula1, axiom, ![X1:object, X0:object, X2:object]:   (~on(X2,X1) | ~on(X0,X1))).
tff(formula2, axiom, ![X0:object]:   (~holding(X0) | ~ontable(X0))).
tff(formula3, axiom, ![VAR0:object, X0:object]:   (~holding(X0) | ~on(VAR0,X0))).
tff(formula4, axiom, ![X1:object, X0:object, X2:object]:   (~on(X0,X2) | ~on(X0,X1))).
tff(formula5, axiom, ![X0:object]:   (~holding(X0) | ~clear(X0))).
tff(formula6, axiom, ![VAR0:object, X0:object]:   (~holding(X0) | ~on(X0,VAR0))).
tff(formula7, axiom, ![VAR0:object]:   (~on(VAR0,VAR0) | handempty)).
tff(formula8, axiom, ![X0:object]:   (~holding(X0) | ~on(X0,X0))).
tff(formula0, negated_conjecture, ![E:object,J:object,C:object]: (on(E,J) & clear(E) & handempty & on(C,C))).