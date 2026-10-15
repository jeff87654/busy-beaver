(** Numeric formulas for the pinned PA238 source.

    Original PA additions. The four-residue convention and dual Cantor
    pairing are those of the source. Jeffrey's local m254 proof was consulted
    as a reference; the unresolved permission status is recorded in README.md.
    In particular, the PA rows 3/5/7 below must not be replaced by ZF rows.
    This module makes no semantic identification of code 0 or code 1. *)
From Coq Require Import Arith Lia Bool List.
Import ListNotations.

Fixpoint triangle (n : nat) : nat :=
  match n with 0 => 0 | S k => triangle k + S k end.
Definition P (a b : nat) := triangle (a + b) + b.
Definition next_pair (p : nat * nat) : nat * nat :=
  match p with (0, b) => (S b, 0) | (S a, b) => (a, S b) end.
Fixpoint unP (z : nat) : nat * nat :=
  match z with 0 => (0, 0) | S z => next_pair (unP z) end.

Lemma triangle_mono n m : n <= m -> triangle n <= triangle m.
Proof. intro H; induction H; simpl; lia. Qed.

Lemma P_mono a b c d : a <= c -> b <= d -> P a b <= P c d.
Proof.
  intros Ha Hb; unfold P.
  pose proof (triangle_mono (a + b) (c + d) ltac:(lia)); lia.
Qed.

Lemma P_start_minimum : P 3 (P 1 (P 1 (P 0 0))) = 32.
Proof. reflexivity. Qed.

Lemma pair_band a b :
  triangle (a + b) <= P a b < triangle (S (a + b)).
Proof. unfold P; simpl; lia. Qed.

Lemma P_injective a b c d : P a b = P c d -> a = c /\ b = d.
Proof.
  intro E.
  pose proof (pair_band a b) as Hab.
  pose proof (pair_band c d) as Hcd.
  assert (Hs : a + b = c + d).
  { destruct (Nat.lt_trichotomy (a + b) (c + d)) as [H|[H|H]]; auto.
    - pose proof (triangle_mono (S (a + b)) (c + d) ltac:(lia)); lia.
    - pose proof (triangle_mono (S (c + d)) (a + b) ltac:(lia)); lia. }
  unfold P in E; rewrite Hs in E; lia.
Qed.

Lemma P_next a b :
  P (fst (next_pair (a, b))) (snd (next_pair (a, b))) = S (P a b).
Proof.
  destruct a as [|a]; unfold P; simpl.
  - rewrite !Nat.add_0_r; simpl; lia.
  - replace (a + S b) with (S a + b) by lia; simpl; lia.
Qed.

Lemma P_unP n : P (fst (unP n)) (snd (unP n)) = n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [unP]. destruct (unP n) as [a b] eqn:E.
  rewrite P_next. simpl in IH; lia.
Qed.

Lemma unP_P a b : unP (P a b) = (a, b).
Proof.
  pose proof (P_unP (P a b)) as H.
  destruct (unP (P a b)) as [c d] eqn:E; simpl in H.
  destruct (P_injective c d a b H) as [-> ->]; reflexivity.
Qed.

Lemma triangle_ge n : n <= triangle n.
Proof. induction n; simpl; lia. Qed.
Lemma P_bounds a b : a <= P a b /\ b <= P a b.
Proof. unfold P; pose proof (triangle_ge (a + b)); lia. Qed.
Lemma unP_bounds n : fst (unP n) <= n /\ snd (unP n) <= n.
Proof. pose proof (P_bounds (fst (unP n)) (snd (unP n))); rewrite P_unP in H; exact H. Qed.

Definition wim (a b : nat) := 4 * P a b.
Definition wel (a b : nat) := 4 * P a b + 1.
Definition wal (a b : nat) := 4 * P a b + 2.
Definition weq (a b : nat) := 4 * P a b + 3.
Definition wn (a : nat) := wim a 1.
Definition wa (a b : nat) := wn (wim a (wn b)).
Definition wex (a b : nat) := wn (wal a (wn b)).

Definition rho1 a b := wex a (weq a b).
Definition rho2 a b c := wim (wal a (wim b c)) (wim (wal a b) (wal a c)).
Definition rho3 a b c := wim (wel a b) (wim (weq b c) (wel a c)).
Definition rho4 a b c := wim (wal a (wal b c)) (wal b (wal a c)).
Definition rho5 a b c := wim (weq a b) (wim (wel a c) (wel b c)).
Definition rho6 a b := wim (wex a (wal a b)) b.
Definition rho7 a b c := wim (weq a b) (wim (weq a c) (weq b c)).
Definition rho8 a b c u := wim (wim (wim c u) a) (wim (wim a c) (wim b c)).

(** Here [c] occurs both as a variable label and as a formula code. The
    converse-membership reading is wel(container, member). *)
Definition bundle a b c :=
  wa (wex c
        (wa (wal b (wa (wim (wel a b) (wim c (wel c b)))
                        (wim (wel c b) c)))
            (wim c (wel c b))))
     (wa (wim (weq a b) (wal c (weq a b)))
         (wim (wel a b) (wal c (wel a b)))).
Definition gate a b c :=
  if Nat.eqb c a || Nat.eqb c b then 0 else bundle a b c.

Definition ax_rows a h b c u :=
  [rho1 a b; rho2 a b c; rho3 a b c; rho4 a b c;
   rho5 a b c; rho6 a b; rho7 a b c; rho8 a b c u; wal a h].
Definition ax_stack a h b c u t w := fold_right P w (ax_rows a h b c u ++ [t]).

Lemma wim_not_one a b : wim a b <> 1.
Proof. unfold wim; lia. Qed.
Lemma wal_not_one a b : wal a b <> 1.
Proof. unfold wal; lia. Qed.
Lemma wex_not_one a b : wex a b <> 1.
Proof. apply wim_not_one. Qed.
Lemma bundle_not_one a b c : bundle a b c <> 1.
Proof. apply wim_not_one. Qed.
Lemma rows_not_one a h b c u : Forall (fun n => n <> 1) (ax_rows a h b c u).
Proof.
  unfold ax_rows, rho1, rho2, rho3, rho4, rho5, rho6, rho7, rho8.
  repeat constructor; first [apply wim_not_one | apply wal_not_one].
Qed.
Lemma gate_same a b : gate a b a = 0.
Proof. unfold gate; rewrite Nat.eqb_refl; reflexivity. Qed.
Lemma gate_fresh a b c : c <> a -> c <> b -> gate a b c = bundle a b c.
Proof.
  intros Ha Hb; unfold gate.
  rewrite (proj2 (Nat.eqb_neq c a) Ha), (proj2 (Nat.eqb_neq c b) Hb); reflexivity.
Qed.
Lemma gate_not_one a b c : gate a b c <> 1.
Proof. unfold gate; destruct (_ || _)%bool; [lia|apply bundle_not_one]. Qed.
