tff(noargs_type, type, empty: $tType).
tff(type_dec1, type, object: $tType).
tff(on_decl, type, on: (object * object) > $o).
tff(ontable_decl, type, ontable: object > $o).
tff(clear_decl, type, clear: object > $o).
tff(handempty_decl, type, handempty: empty > $o).
tff(holding_decl, type, holding: object > $o).
tff(equal_decl, type, equal: (object * object) > $o).
tff(formula1, axiom, ![VAL1:object, VAL0:object, X0:object]:   clear(X0) | VAL0=VAL1).
tff(formula2, axiom, ![VAL1:object, VAL0:object, X0:object]:   clear(X0) | VAL0=VAL1).
tff(formula3, axiom, ![X0:object]:   clear(X0) | on(X0,X0)).
tff(formula4, axiom, ![X0:object]:   clear(X0) | ~handempty(NOARGS)).
tff(formula5, axiom, ![VAL0:object, X0:object]:   ontable(X0) | on(VAL0,VAL0)).
tff(formula6, axiom, ![VAL1:object, VAL0:object, X0:object]:   ontable(X0) | VAL0=VAL1).
tff(formula7, axiom, ![VAL1:object, VAL0:object, X0:object]:   clear(X0) | VAL0=VAL1).
tff(formula8, axiom, ![VAL1:object, VAL0:object, X0:object]:   ontable(X0) | VAL0=VAL1).
tff(formula9, axiom, ![VAL1:object, VAL0:object, X0:object]:   clear(X0) | VAL0=VAL1).
tff(formula10, axiom, ![X0:object]:   clear(X0) | ontable(X0)).
tff(formula11, axiom, ![VAL0:object, X0:object]:   clear(X0) | on(VAL0,VAL0)).
tff(formula12, axiom, ![VAL0:object, VAL1:object, X0:object]:   clear(X0) | on(VAL0,VAL1)).
tff(formula13, axiom, ![VAL0:object, X0:object]:   ontable(X0) | VAL0=VAL0).
tff(formula14, axiom, ![VAL0:object, X0:object]:   clear(X0) | ontable(VAL0)).
tff(formula15, axiom, ![VAL1:object, VAL0:object, X0:object]:   ontable(X0) | VAL0=VAL1).
tff(formula16, axiom, ![VAL0:object, VAL1:object, X0:object]:   ontable(X0) | on(VAL0,VAL1)).
tff(formula17, axiom, ![VAL1:object, VAL0:object, X0:object]:   ontable(X0) | VAL0=VAL1).
tff(formula18, axiom, ![VAL0:object, X0:object]:   ontable(X0) | ontable(VAL0)).
tff(formula19, axiom, ![VAL0:object, X0:object]:   clear(X0) | on(VAL0,X0)).
tff(formula20, axiom, ![VAL0:object, X0:object]:   clear(X0) | clear(VAL0)).
tff(formula21, axiom, ![VAL0:object, X0:object]:   clear(X0) | VAL0=VAL0).
tff(formula22, axiom, ![VAL0:object, X0:object]:   ontable(X0) | VAL0=VAL0).
tff(formula23, axiom, ![X0:object]:   ~holding(X0)).
tff(formula24, axiom, ![X1:object, X0:object]:   ~on(X0,X1)).
tff(formula25, axiom, ![VAL1:object, VAL0:object, X0:object]:   ontable(X0) | VAL0=VAL1).
tff(formula26, axiom, ![VAL1:object, VAL0:object, X0:object]:   ontable(X0) | VAL0=VAL1).
tff(formula27, axiom, ![VAL0:object, X0:object]:   ontable(X0) | on(X0,VAL0)).
tff(formula28, axiom, ![VAL0:object, X0:object]:   ontable(X0) | on(VAL0,X0)).
tff(formula29, axiom, ![VAL0:object, X0:object]:   clear(X0) | VAL0=VAL0).
tff(formula0, negated_conjecture, ![A:object,NOARGS:empty,D:object]: (clear(A) & ontable(A) & handempty(NOARGS) & on(D,D))).