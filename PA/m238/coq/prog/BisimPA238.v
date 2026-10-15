(** * Frozen PA238 physical/source execution correspondence.

    Both directions use the generic certificate soundness proof. The PA
    certificate is checked against the actual185-node physical decoder and
    the actual191-node source DAG, for every register file. *)

From Coq Require Import Lists.List.
From P238.tm Require Import RM238 Prog238.
From P238.prog Require Import Bisim238 Dag238 Cert238.
Local Unset Implicit Arguments.
Import ListNotations.

Lemma cert238_forward : check (ptree p238) (ptree dag238) cert238 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cert238_backward : check (ptree dag238) (ptree p238) (mirror cert238) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem p238_source_dag238 R :
  rm_halts p238 ([], R) <-> rm_halts dag238 ([], R).
Proof. exact (check_iff p238 dag238 cert238 cert238_forward cert238_backward R). Qed.
