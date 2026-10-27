From BusyCoq Require Export Individual.
From BB8 Require Export BB102.

Module Individual102 := Individual BB102.
Export Individual102.

Declare Scope sym_scope.
Bind Scope sym_scope with Sym.
Delimit Scope sym_scope with sym.
Open Scope sym.

Notation "0" := S0 : sym_scope.
Notation "1" := S1 : sym_scope.

(* Make sure that [{{D}}>] still refers to the state, even if we shadowed
   [D] itself with something else. *)
Notation "l '{{A}}>'  r" := (l {{A}}> r) (at level 30).
Notation "l '{{B}}>'  r" := (l {{B}}> r) (at level 30).
Notation "l '{{C}}>'  r" := (l {{C}}> r) (at level 30).
Notation "l '{{D}}>'  r" := (l {{D}}> r) (at level 30).
Notation "l '{{E}}>'  r" := (l {{E}}> r) (at level 30).
Notation "l '{{F}}>'  r" := (l {{F}}> r) (at level 30).
Notation "l '{{G}}>'  r" := (l {{G}}> r) (at level 30).
Notation "l '{{H}}>'  r" := (l {{H}}> r) (at level 30).
Notation "l '{{I}}>'  r" := (l {{I}}> r) (at level 30).

Notation "l '<{{A}}' r" := (l <{{A}} r) (at level 30).
Notation "l '<{{B}}' r" := (l <{{B}} r) (at level 30).
Notation "l '<{{C}}' r" := (l <{{C}} r) (at level 30).
Notation "l '<{{D}}' r" := (l <{{D}} r) (at level 30).
Notation "l '<{{E}}' r" := (l <{{E}} r) (at level 30).
Notation "l '<{{F}}' r" := (l <{{F}} r) (at level 30).
Notation "l '<{{G}}' r" := (l <{{G}} r) (at level 30).
Notation "l '<{{H}}' r" := (l <{{H}} r) (at level 30).
Notation "l '<{{I}}' r" := (l <{{I}} r) (at level 30).
Notation "l '{{J}}>'  r" := (l {{J}}> r) (at level 30).
Notation "l '<{{J}}' r" := (l <{{J}} r) (at level 30).
