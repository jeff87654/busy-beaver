(** Original actual finite S0 proof transport. The schema suppliers in
    PointedSchemas238 construct finite equality/pointed-R9 proofs without IR.
    This file transports the existing PAinCompact238.finite_set_S0 predicate,
    not a surrogate theory. Raw numeric schema adequacy remains separate. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 PointedSchemas238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 PointedSchemas238.PointedSchemas238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module S0InCompact238.

Theorem S0_axiom_forward phi : finite_set_S0 phi -> derivable pointed_equality_theory phi.
Proof.
  intros [chi Hbase|chi n Hclosed].
  - apply in_app_or in Hbase as [Heq|Hadj].
    + apply derivable_axiom, forward_equality. exact Heq.
    + destruct Hadj as [<-|[]]. exact forward_adjunction.
  - apply forward_forall_times, forward_separation.
Qed.

Theorem S0_to_pointed_equality phi :
  derivable finite_set_S0 phi -> derivable pointed_equality_theory phi.
Proof. apply finite_theory_transport, S0_axiom_forward. Qed.

Theorem S0_to_compact phi : derivable finite_set_S0 phi -> derivable compact_theory phi.
Proof.
  intro H. destruct (S0_to_pointed_equality phi H) as [G [HG Hproof]].
  exists G. split; [|exact Hproof]. intros psi Hpsi. apply pointed_equality_in_compact, HG, Hpsi.
Qed.

Corollary S0_refutation_to_compact :
  derivable finite_set_S0 falsity -> derivable compact_theory falsity.
Proof. apply S0_to_compact. Qed.

Print Assumptions S0_to_pointed_equality.
Print Assumptions S0_to_compact.
Print Assumptions S0_refutation_to_compact.

End S0InCompact238.
