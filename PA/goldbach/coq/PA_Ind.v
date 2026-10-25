(** * PA_Ind: every instance IND x c a (c <> x, c not in a) from the machine-shaped primitive
    AIND x a = IND x (fcode a) a  (x < fcode a), by renaming the bound successor variable. *)
From Coq Require Import Arith Lia List Bool.
From PAGB Require Import PA_Pair PALogic PA_dB PA_LProp PA_LMeta PA_H.
Import ListNotations.
Unset Implicit Arguments.

Section Ind.
Variable X : wff -> Prop.
Local Notation lprov := (pprov X).
Let LDET := DET X.

Ltac dh := apply dhyp; simpl; tauto.
Ltac dt H := apply dthm; exact H.
Ltac mp a := apply (dmp _ _ a).

Definition sstep (x c : nat) (a : wff) : wff :=
  Wim (Weq (TV c) (TS (TV x))) (Wal x (Wim (Weq (TV x) (TV c)) a)).

Lemma IND_shape x c a :
  IND x c a = Wim (Wal x (Wim (Weq (TV x) TZ) a)) (Wim (Wal x (Wim a (Wal c (sstep x c a)))) (Wal x a)).
Proof. reflexivity. Qed.

(** if x does not occur in a, IND is trivial: the base case at 0, then vacuity *)
Lemma lind_triv x c a : occ x a = false -> lprov (IND x c a).
Proof.
  intro Hx. rewrite IND_shape.
  assert (S0 : lprov (Wim (Wal x (Wim (Weq (TV x) TZ) a)) (Wim (Weq TZ TZ) a))).
  { pose proof (lspec X x TZ (Wim (Weq (TV x) TZ) a) eq_refl) as H.
    cbn [sb sbt] in H. rewrite Nat.eqb_refl in H. rewrite (sb_noocc x TZ a Hx) in H.
    apply H; [cbn; now apply occ_bnd | intros v Hv; discriminate]. }
  apply der_lprov, ded, ded.
  mp a; [dt (lvac X x a Hx)|]. mp (Weq TZ TZ); [| dt (leq_refl X TZ)].
  mp (Wal x (Wim (Weq (TV x) TZ) a)); [dt S0 | dh].
Qed.

Lemma lind x c a : c <> x -> occ c a = false -> lprov (IND x c a).
Proof.
  intros Hcx Hc. destruct (occ x a) eqn:Hxa; [|now apply lind_triv].
  set (c0 := fcode a). assert (Hx0 : x < c0) by now apply fcode_fresh.
  pose proof (AIND X x a Hx0) as H0. fold c0 in H0.
  destruct (Nat.eq_dec c c0) as [->|Hne]; [exact H0|].
  assert (Hc0 : occ c0 a = false) by apply fcode_nocc.
  (* A.c (sstep c) -> A.c0 (sstep c0) *)
  assert (R : lprov (Wim (Wal c (sstep x c a)) (Wal c0 (sstep x c0 a)))).
  { assert (E : sb c (TV c0) (sstep x c a) = sstep x c0 a).
    { unfold sstep. cbn [sb sbt]. rewrite Nat.eqb_refl.
      assert (Exc : Nat.eqb x c = false) by (apply Nat.eqb_neq; congruence).
      rewrite Exc. rewrite (sb_noocc c (TV c0) a Hc). reflexivity. }
    assert (B1 : bnd c (sstep x c a) = false).
    { unfold sstep. cbn [bnd]. rewrite (occ_bnd c a Hc). assert (Exc : Nat.eqb x c = false) by (apply Nat.eqb_neq; congruence). rewrite Exc. reflexivity. }
    assert (B2 : occ c0 (sstep x c a) = false).
    { unfold sstep. cbn [occ tocc]. rewrite Hc0.
      assert (E1 : Nat.eqb c c0 = false) by (apply Nat.eqb_neq; congruence).
      assert (E2 : Nat.eqb x c0 = false) by (apply Nat.eqb_neq; lia).
      rewrite E1, E2. reflexivity. }
    pose proof (lalpha X c c0 (sstep x c a) Hne B1 B2) as L. rewrite E in L. exact L. }
  rewrite IND_shape in H0 |- *.
  apply der_lprov, ded, ded.
  mp (Wal x (Wim a (Wal c0 (sstep x c0 a)))).
  - mp (Wal x (Wim (Weq (TV x) TZ) a)); [dt H0 | dh].
  - mp (Wal x (Wim a (Wal c (sstep x c a)))); [| dh].
    apply dthm, lal. apply der_lprov, ded, ded.
    mp (Wal c (sstep x c a)); [dt R|]. mp a; dh.
Qed.
End Ind.
