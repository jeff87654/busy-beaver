(** * Original indexed PA238 register tape interface.

    Register indices refer to physical unary blocks. Updating a valid index
    changes its value and preserves every other indexed value. The split
    lemmas connect indexed files to the concrete excursions in Box238. *)

From Coq Require Import Lists.List Arith.Arith Lia.
From P238.tm Require Import Box238.
Local Unset Implicit Arguments.
Import ListNotations.

Fixpoint update_register238 (r : nat) (f : nat -> nat) (vs : list nat) {struct vs} : list nat :=
  match vs with
  | [] => []
  | v :: rest =>
      match r with
      | 0 => f v :: rest
      | S r => v :: update_register238 r f rest
      end
  end.

Fixpoint marked_file238 (r : nat) (vs : list nat) {struct vs} : list bool :=
  match vs with
  | [] => []
  | v :: rest =>
      match r with
      | 0 => false :: false :: repeat true v ++ register_file238 rest
      | S r => false :: repeat true (S v) ++ marked_file238 r rest
      end
  end.

Lemma update_register238_length r f vs :
  length (update_register238 r f vs) = length vs.
Proof.
  revert r. induction vs as [|v vs IH]; intro r; [reflexivity|].
  destruct r; cbn [update_register238 length]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma update_register238_values r f vs i :
  r < length vs ->
  nth i (update_register238 r f vs) 0 =
    if Nat.eqb i r then f (nth r vs 0) else nth i vs 0.
Proof.
  revert r i. induction vs as [|v vs IH]; intros r i H; [cbn [length] in H; lia|].
  destruct r as [|r], i as [|i]; cbn [update_register238 nth Nat.eqb];
    try reflexivity. apply IH. cbn [length] in H. lia.
Qed.

Lemma update_register238_split pre v rest f :
  update_register238 (length pre) f (pre ++ v :: rest) = pre ++ f v :: rest.
Proof.
  induction pre as [|u pre IH]; cbn [length app update_register238]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma marked_file238_split pre v rest :
  marked_file238 (length pre) (pre ++ v :: rest) =
    register_file238 pre ++ false :: false :: repeat true v ++ register_file238 rest.
Proof.
  induction pre as [|u pre IH]; [reflexivity|].
  cbn [length app marked_file238]. rewrite IH.
  change (register_file238 (u :: pre)) with
    (false :: repeat true (S u) ++ register_file238 pre).
  cbn [app]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma register238_split (vs : list nat) r : r < length vs ->
  exists pre v rest, vs = pre ++ v :: rest /\ length pre = r.
Proof.
  revert r. induction vs as [|v vs IH]; intros r H; [cbn [length] in H; lia|].
  destruct r as [|r].
  - exists [], v, vs. split; reflexivity.
  - assert (Hr : r < length vs) by (cbn [length] in H; lia).
    destruct (IH r Hr) as [pre [value [rest [E L]]]].
    exists (v :: pre), value, rest. subst vs. split; [reflexivity|]. cbn [length]. congruence.
Qed.

Lemma register238_value_split pre v rest :
  nth (length pre) (pre ++ v :: rest) 0 = v.
Proof. induction pre as [|u pre IH]; cbn [length app nth]; [reflexivity|exact IH]. Qed.
