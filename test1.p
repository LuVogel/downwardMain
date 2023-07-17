solution finally found
invariant_candidates found: 
type:  <class 'collections.deque'> , len:  17
INVARIANT CANDIDATE: ¬on(?x0, ?x1) [?x0: object, ?x1: object]
INVARIANT CANDIDATE: ¬on(?x0, ?var0) ∨ clear(?x0) [?x0: object, ?var0: object]
INVARIANT CANDIDATE: clear(?x0) ∨ holding(?x0) [?x0: object]
INVARIANT CANDIDATE: clear(?x0) ∨ ¬ontable(?x0) [?x0: object]
INVARIANT CANDIDATE: ¬on(?x0, ?x0) ∨ clear(?x0) [?x0: object]
INVARIANT CANDIDATE: ¬on(?var0, ?x0) ∨ clear(?x0) [?x0: object, ?var0: object]
INVARIANT CANDIDATE: ¬on(?x0, ?var0) ∨ ontable(?x0) [?x0: object, ?var0: object]
INVARIANT CANDIDATE: ¬on(?x0, ?x0) ∨ ontable(?x0) [?x0: object]
INVARIANT CANDIDATE: ontable(?x0) ∨ ¬clear(?x0) [?x0: object]
INVARIANT CANDIDATE: ¬on(?var0, ?x0) ∨ ontable(?x0) [?x0: object, ?var0: object]
INVARIANT CANDIDATE: ontable(?x0) ∨ holding(?x0) [?x0: object]
INVARIANT CANDIDATE: ¬on(?var0, ?var0) ∨ handempty() [?var0: object]
INVARIANT CANDIDATE: ¬on(?var0, ?x0) ∨ ¬holding(?x0) [?x0: object, ?var0: object]
INVARIANT CANDIDATE: ¬clear(?x0) ∨ ¬holding(?x0) [?x0: object]
INVARIANT CANDIDATE: ¬ontable(?x0) ∨ ¬holding(?x0) [?x0: object]
INVARIANT CANDIDATE: ¬on(?x0, ?x0) ∨ ¬holding(?x0) [?x0: object]
INVARIANT CANDIDATE: ¬on(?x0, ?var0) ∨ ¬holding(?x0) [?x0: object, ?var0: object]

len orig actions:  40 , len reduced actions:  32 for 4 objects
Computing schematic group: [1.260s CPU, 52.963s wall-clock] --> reduced with 4 object
Computing schematic group: [1.530s CPU, 68.603s wall-clock] --> normal with 4 objecs

len orig actions:  60 , len reduced actions:  40 for 5 objects
Computing schematic group: [1.050s CPU, 57.004s wall-clock] --> reduced with 5 objects
Computing schematic group: [1.300s CPU, 70.549s wall-clock] --> normal with 5 objects

len orig actions:  84 , len reduced actions:  48 for 6 objects
Computing schematic group: [1.640s CPU, 85.708s wall-clock] --> reduced with 6 objects
Computing schematic group: [2.360s CPU, 124.239s wall-clock] --> normal with 6 objects


len orig actions:  112 , len reduced actions:  56 for 7 objects
Computing schematic group: [6.050s CPU, 284.387s wall-clock] --> reduced with 7 objects
Computing schematic group: [8.740s CPU, 367.611s wall-clock] --> normal with 7 objects

len orig actions:  144 , len reduced actions:  64 for 8 objects
Computing schematic group: [5.860s CPU, 233.936s wall-clock] --> reduced with 8 objects
Computing schematic group: [12.610s CPU, 525.851s wall-clock] --> normal with 8 objects


len orig actions:  180 , len reduced actions:  72 for 9 objects
Computing schematic group: [8.280s CPU, 326.619s wall-clock] --> reduced with 9 objects
Computing schematic group: [18.350s CPU, 748.328s wall-clock] --> normal with 9 objects

len orig actions:  220 , len reduced actions:  80 for 10 objects
Computing schematic group: [10.400s CPU, 407.085s wall-clock] --> reduced with 10 objects
Computing schematic group: [25.280s CPU, 995.878s wall-clock] --> normal with 10 objects


len orig actions:  264 , len reduced actions:  88 for 11 objects
Computing schematic group: [35.830s CPU, 1372.717s wall-clock] --> normal with 11 objects