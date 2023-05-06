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
