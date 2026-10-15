(** * Complete physical files and the authenticated source permutation.

    The arbitrary tail is retained exactly, including every nonzero old
    spare. These indexed equalities instantiate the source register update
    in the literal file; they impose no outside-register zero condition. *)

From Coq Require Import Lists.List Arith.Arith Lia.
From P238.tm Require Import RM238 Prog238 RegisterTape238.
Local Unset Implicit Arguments.
Import ListNotations.

Definition physical238 (R : regs) := [R 2; R 4; R 3; R 7; R 6; R 8; R 0; R 1; R 5].

Lemma physical238_length R ext : 9 <= length (physical238 R ++ ext).
Proof. rewrite length_app. cbn [physical238 length]. lia. Qed.

Lemma physical238_value R ext r : r < 9 -> nth (slot_of238 r) (physical238 R ++ ext) 0 = R r.
Proof. intros B. do 9 (destruct r as [|r]; [reflexivity|]). lia. Qed.

Lemma physical238_update R ext r f : r < 9 ->
  update_register238 (slot_of238 r) f (physical238 R ++ ext) =
  physical238 (upd R r (f (R r))) ++ ext.
Proof. intros B. do 9 (destruct r as [|r]; [reflexivity|]). lia. Qed.

Lemma physical238_boot : physical238 R_boot238 = [0;2;0;0;0;0;6;0;0].
Proof. reflexivity. Qed.
