From BusyCoq Require Export Individual.
From TM74 Require Export BB74.

Module Individual74 := Individual BB74.
Export Individual74.

Declare Scope sym_scope.
Bind Scope sym_scope with Sym.
Delimit Scope sym_scope with sym.
Open Scope sym.

Notation "0" := S0 : sym_scope.
Notation "1" := S1 : sym_scope.
Notation "2" := S2 : sym_scope.
Notation "3" := S3 : sym_scope.

(* Make sure that [{{A}}>] still refers to the state, even if we shadowed
   [A] itself with something else. *)
Notation "l '{{A}}>'  r" := (l {{A}}> r) (at level 30).
Notation "l '{{B}}>'  r" := (l {{B}}> r) (at level 30).
Notation "l '{{C}}>'  r" := (l {{C}}> r) (at level 30).
Notation "l '{{D}}>'  r" := (l {{D}}> r) (at level 30).
Notation "l '{{E}}>'  r" := (l {{E}}> r) (at level 30).
Notation "l '{{F}}>'  r" := (l {{F}}> r) (at level 30).
Notation "l '{{G}}>'  r" := (l {{G}}> r) (at level 30).
Notation "l '<{{A}}' r" := (l <{{A}} r) (at level 30).
Notation "l '<{{B}}' r" := (l <{{B}} r) (at level 30).
Notation "l '<{{C}}' r" := (l <{{C}} r) (at level 30).
Notation "l '<{{D}}' r" := (l <{{D}} r) (at level 30).
Notation "l '<{{E}}' r" := (l <{{E}} r) (at level 30).
Notation "l '<{{F}}' r" := (l <{{F}} r) (at level 30).
Notation "l '<{{G}}' r" := (l <{{G}} r) (at level 30).
