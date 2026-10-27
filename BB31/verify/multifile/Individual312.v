(** * busycoq Individual utilities for 31-state machines (generated) *)
From BusyCoq Require Export Individual.
From BB8 Require Export BB312.

Module Individual312 := Individual BB312.
Export Individual312.

Declare Scope sym_scope.
Bind Scope sym_scope with Sym.
Delimit Scope sym_scope with sym.
Open Scope sym.

Notation "0" := S0 : sym_scope.
Notation "1" := S1 : sym_scope.

(* Configuration notations l {{qX}}> r  and  l <{{qX}} r for every state (as in BB142);
   busycoq's generic  l {{ q }}> r  /  l <{{ q }} r  also work. *)
Notation "l '{{qA}}>'  r" := (l {{qA}}> r) (at level 30).
Notation "l '<{{qA}}' r" := (l <{{qA}} r) (at level 30).
Notation "l '{{qB}}>'  r" := (l {{qB}}> r) (at level 30).
Notation "l '<{{qB}}' r" := (l <{{qB}} r) (at level 30).
Notation "l '{{qC}}>'  r" := (l {{qC}}> r) (at level 30).
Notation "l '<{{qC}}' r" := (l <{{qC}} r) (at level 30).
Notation "l '{{qD}}>'  r" := (l {{qD}}> r) (at level 30).
Notation "l '<{{qD}}' r" := (l <{{qD}} r) (at level 30).
Notation "l '{{qE}}>'  r" := (l {{qE}}> r) (at level 30).
Notation "l '<{{qE}}' r" := (l <{{qE}} r) (at level 30).
Notation "l '{{qF}}>'  r" := (l {{qF}}> r) (at level 30).
Notation "l '<{{qF}}' r" := (l <{{qF}} r) (at level 30).
Notation "l '{{qG}}>'  r" := (l {{qG}}> r) (at level 30).
Notation "l '<{{qG}}' r" := (l <{{qG}} r) (at level 30).
Notation "l '{{qH}}>'  r" := (l {{qH}}> r) (at level 30).
Notation "l '<{{qH}}' r" := (l <{{qH}} r) (at level 30).
Notation "l '{{qI}}>'  r" := (l {{qI}}> r) (at level 30).
Notation "l '<{{qI}}' r" := (l <{{qI}} r) (at level 30).
Notation "l '{{qJ}}>'  r" := (l {{qJ}}> r) (at level 30).
Notation "l '<{{qJ}}' r" := (l <{{qJ}} r) (at level 30).
Notation "l '{{qK}}>'  r" := (l {{qK}}> r) (at level 30).
Notation "l '<{{qK}}' r" := (l <{{qK}} r) (at level 30).
Notation "l '{{qL}}>'  r" := (l {{qL}}> r) (at level 30).
Notation "l '<{{qL}}' r" := (l <{{qL}} r) (at level 30).
Notation "l '{{qM}}>'  r" := (l {{qM}}> r) (at level 30).
Notation "l '<{{qM}}' r" := (l <{{qM}} r) (at level 30).
Notation "l '{{qN}}>'  r" := (l {{qN}}> r) (at level 30).
Notation "l '<{{qN}}' r" := (l <{{qN}} r) (at level 30).
Notation "l '{{qO}}>'  r" := (l {{qO}}> r) (at level 30).
Notation "l '<{{qO}}' r" := (l <{{qO}} r) (at level 30).
Notation "l '{{qP}}>'  r" := (l {{qP}}> r) (at level 30).
Notation "l '<{{qP}}' r" := (l <{{qP}} r) (at level 30).
Notation "l '{{qQ}}>'  r" := (l {{qQ}}> r) (at level 30).
Notation "l '<{{qQ}}' r" := (l <{{qQ}} r) (at level 30).
Notation "l '{{qR}}>'  r" := (l {{qR}}> r) (at level 30).
Notation "l '<{{qR}}' r" := (l <{{qR}} r) (at level 30).
Notation "l '{{qS}}>'  r" := (l {{qS}}> r) (at level 30).
Notation "l '<{{qS}}' r" := (l <{{qS}} r) (at level 30).
Notation "l '{{qT}}>'  r" := (l {{qT}}> r) (at level 30).
Notation "l '<{{qT}}' r" := (l <{{qT}} r) (at level 30).
Notation "l '{{qU}}>'  r" := (l {{qU}}> r) (at level 30).
Notation "l '<{{qU}}' r" := (l <{{qU}} r) (at level 30).
Notation "l '{{qV}}>'  r" := (l {{qV}}> r) (at level 30).
Notation "l '<{{qV}}' r" := (l <{{qV}} r) (at level 30).
Notation "l '{{qW}}>'  r" := (l {{qW}}> r) (at level 30).
Notation "l '<{{qW}}' r" := (l <{{qW}} r) (at level 30).
Notation "l '{{qX}}>'  r" := (l {{qX}}> r) (at level 30).
Notation "l '<{{qX}}' r" := (l <{{qX}} r) (at level 30).
Notation "l '{{qY}}>'  r" := (l {{qY}}> r) (at level 30).
Notation "l '<{{qY}}' r" := (l <{{qY}} r) (at level 30).
Notation "l '{{qZ}}>'  r" := (l {{qZ}}> r) (at level 30).
Notation "l '<{{qZ}}' r" := (l <{{qZ}} r) (at level 30).
Notation "l '{{qAA}}>'  r" := (l {{qAA}}> r) (at level 30).
Notation "l '<{{qAA}}' r" := (l <{{qAA}} r) (at level 30).
Notation "l '{{qAB}}>'  r" := (l {{qAB}}> r) (at level 30).
Notation "l '<{{qAB}}' r" := (l <{{qAB}} r) (at level 30).
Notation "l '{{qAC}}>'  r" := (l {{qAC}}> r) (at level 30).
Notation "l '<{{qAC}}' r" := (l <{{qAC}} r) (at level 30).
Notation "l '{{qAD}}>'  r" := (l {{qAD}}> r) (at level 30).
Notation "l '<{{qAD}}' r" := (l <{{qAD}} r) (at level 30).
Notation "l '{{qAE}}>'  r" := (l {{qAE}}> r) (at level 30).
Notation "l '<{{qAE}}' r" := (l <{{qAE}} r) (at level 30).
