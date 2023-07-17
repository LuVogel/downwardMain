tff(type_dec1, type, object: $tType).
tff(on_decl, type, on: (object * object) > $o).
tff(ontable_decl, type, ontable: object > $o).
tff(clear_decl, type, clear: object > $o).
tff(handempty_decl, type, handempty: $o).
tff(holding_decl, type, holding: object > $o).
tff(equal_decl, type, equal: (object * object) > $o).
tff(formula1, axiom,   (handempty)).
tff(formula2, axiom, ![X1:object, X2:object, X0:object]:   (~on(X2,X1) | ~on(X0,X1))).
tff(formula3, axiom, ![X1:object, X2:object, X0:object]:   (~on(X0,X2) | ~on(X0,X1))).
tff(formula4, axiom, ![X0:object]:   (~holding(X0))).
tff(formula0, negated_conjecture, ![G:object,H:object,E:object]: (holding(G) & clear(H) & on(E,H))).