tff(type_dec1, type, object: $tType).
tff(on_decl, type, on: (object * object) > $o).
tff(ontable_decl, type, ontable: object > $o).
tff(clear_decl, type, clear: object > $o).
tff(handempty_decl, type, handempty: $o).
tff(holding_decl, type, holding: object > $o).
tff(equal_decl, type, equal: (object * object) > $o).
tff(formula1, axiom, ![X0:object]:   (~ontable(X0) | clear(X0))).
tff(formula2, axiom, ![X0:object]:   (ontable(X0) | ~on(X0,X0))).
tff(formula3, axiom, ![X0:object]:   (~on(X0,X0) | clear(X0))).
tff(formula4, axiom, ![X0:object]:   (holding(X0) | clear(X0))).
tff(formula5, axiom, ![VAR0:object, X0:object]:   (~on(X0,VAR0) | clear(X0))).
tff(formula6, axiom, ![VAR0:object, X0:object]:   (~on(X0,VAR0) | ontable(X0))).
tff(formula7, axiom, ![X0:object]:   (~clear(X0) | ~holding(X0))).
tff(formula8, axiom, ![X0:object]:   (ontable(X0) | ~clear(X0))).
tff(formula9, axiom, ![X0:object]:   (~on(X0,X0) | ~holding(X0))).
tff(formula10, axiom, ![VAR0:object, X0:object]:   (~on(X0,VAR0) | ~holding(X0))).
tff(formula11, axiom, ![X0:object]:   (ontable(X0) | holding(X0))).
tff(formula12, axiom, ![VAR0:object]:   (handempty | ~on(VAR0,VAR0))).
tff(formula13, axiom, ![VAR0:object, X0:object]:   (~on(VAR0,X0) | ontable(X0))).
tff(formula14, axiom, ![VAR0:object, X0:object]:   (~on(VAR0,X0) | clear(X0))).
tff(formula15, axiom, ![VAR0:object, X0:object]:   (~on(VAR0,X0) | ~holding(X0))).
tff(formula16, axiom, ![X1:object, X0:object]:   (~on(X0,X1))).
tff(formula17, axiom, ![X0:object]:   (~ontable(X0) | ~holding(X0))).
tff(formula0, negated_conjecture, ![C:object]: (holding(C) & clear(C) & ~ontable(C))).