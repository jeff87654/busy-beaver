(** * PA_Codes: the numeric coding of the pagb machine (design A, zf/pagb/INTERFACE.md).

    Dual Cantor pairing  P a b = tri (a+b) + b  (as zf/m254/logic/coq/Codes254.v), codes 4 P(x,y) + tag.
      terms    T 0 = 0;  4P(j,k)+0 = S T(j) (n > 0);  +1 = T(j) + T(k);  +2 = T(j) * T(k);  +3 = var j
      formulas D 0 = truth;  4P(x,y)+0 = D x -> D y;  +1 = S T(x) = T(y);  +2 = A. v_x D y;  +3 = T(x) = T(y)
    F = 1 = (S 0 = 0).  The decoders are defined with fuel n+1 (components are < n for n > 0).
    Self-freshness: every variable index in T(n) or D(n) is < n. *)
From Coq Require Import Arith Lia Bool.
From PAGB Require Import PA_Pair PALogic PA_dB.
Unset Implicit Arguments.

(** ** Decomposition of a code: n = 4 P(x,y) + tag *)
Definition dtag (n : nat) : nat := n mod 4.
Definition dx (n : nat) : nat := fst (unP (n / 4)).
Definition dy (n : nat) : nat := snd (unP (n / 4)).

Lemma code_split n : n = 4 * P (dx n) (dy n) + dtag n /\ dtag n < 4.
Proof.
  unfold dx, dy, dtag. rewrite P_unP. split; [|apply Nat.mod_upper_bound; lia].
  pose proof (Nat.div_mod n 4 ltac:(lia)). lia.
Qed.

Lemma dx_lt n : 0 < n -> dx n < n.
Proof.
  intro H. destruct (code_split n) as [E _]. pose proof (P_ge_l (dx n) (dy n)).
  destruct (Nat.eq_dec (P (dx n) (dy n)) 0) as [Z|Z].
  - apply P_0 in Z as [-> _]. exact H.
  - lia.
Qed.

Lemma dy_lt n : 0 < n -> dy n < n.
Proof.
  intro H. destruct (code_split n) as [E _]. pose proof (P_ge_r (dx n) (dy n)).
  destruct (Nat.eq_dec (P (dx n) (dy n)) 0) as [Z|Z].
  - apply P_0 in Z as [_ ->]. exact H.
  - lia.
Qed.

Lemma split_code x y t : t < 4 -> dx (4 * P x y + t) = x /\ dy (4 * P x y + t) = y /\ dtag (4 * P x y + t) = t.
Proof.
  intro Ht.
  assert (Hd : (4 * P x y + t) / 4 = P x y) by (symmetry; apply Nat.div_unique with t; lia).
  assert (Hm : (4 * P x y + t) mod 4 = t) by (symmetry; apply Nat.mod_unique with (P x y); lia).
  unfold dx, dy, dtag. rewrite Hd, Hm, unP_P. auto.
Qed.

(** ** Code constructors *)
Definition tsc (j : nat) : nat := 4 * P j 1.          (* S T(j), canonical junk 1 *)
Definition tpl (j k : nat) : nat := 4 * P j k + 1.
Definition tml (j k : nat) : nat := 4 * P j k + 2.
Definition tvar (i : nat) : nat := 4 * P i 0 + 3.

Definition wim (a b : nat) : nat := 4 * P a b.
Definition wseq (x y : nat) : nat := 4 * P x y + 1.  (* S T(x) = T(y) *)
Definition wal (i a : nat) : nat := 4 * P i a + 2.
Definition weq (x y : nat) : nat := 4 * P x y + 3.
Definition F : nat := 1.
Definition wn (a : nat) : nat := wim a F.

Lemma F_code : wseq 0 0 = F.
Proof. reflexivity. Qed.

(** ** Decoders *)
Fixpoint Tf (fuel n : nat) : tm :=
  match fuel with
  | 0 => TZ
  | S f =>
      match n with
      | 0 => TZ
      | _ => match dtag n with
             | 0 => TS (Tf f (dx n))
             | 1 => TP (Tf f (dx n)) (Tf f (dy n))
             | 2 => TM (Tf f (dx n)) (Tf f (dy n))
             | _ => TV (dx n)
             end
      end
  end.

Definition T (n : nat) : tm := Tf (S n) n.

Definition truth : wff := Weq TZ TZ.

Fixpoint Df (fuel n : nat) : wff :=
  match fuel with
  | 0 => truth
  | S f =>
      match n with
      | 0 => truth
      | _ => match dtag n with
             | 0 => Wim (Df f (dx n)) (Df f (dy n))
             | 1 => Weq (TS (T (dx n))) (T (dy n))
             | 2 => Wal (dx n) (Df f (dy n))
             | _ => Weq (T (dx n)) (T (dy n))
             end
      end
  end.

Definition D (n : nat) : wff := Df (S n) n.

(** fuel independence *)
Lemma Tf_fuel f g n : n < f -> n < g -> Tf f n = Tf g n.
Proof.
  revert g n; induction f as [|f IH]; intros g n Hf Hg; [lia|]. destruct g as [|g]; [lia|].
  cbn. destruct n as [|n']; [reflexivity|].
  pose proof (dx_lt (S n') ltac:(lia)). pose proof (dy_lt (S n') ltac:(lia)).
  destruct (dtag (S n')) as [|[|[|]]]; try rewrite (IH g (dx (S n'))) by lia;
    try rewrite (IH g (dy (S n'))) by lia; reflexivity.
Qed.

Lemma Df_fuel f g n : n < f -> n < g -> Df f n = Df g n.
Proof.
  revert g n; induction f as [|f IH]; intros g n Hf Hg; [lia|]. destruct g as [|g]; [lia|].
  cbn. destruct n as [|n']; [reflexivity|].
  pose proof (dx_lt (S n') ltac:(lia)). pose proof (dy_lt (S n') ltac:(lia)).
  destruct (dtag (S n')) as [|[|[|]]]; try rewrite (IH g (dx (S n'))) by lia;
    try rewrite (IH g (dy (S n'))) by lia; reflexivity.
Qed.

Lemma Tf_S f n : Tf (S f) n =
  match n with
  | 0 => TZ
  | _ => match dtag n with
         | 0 => TS (Tf f (dx n))
         | 1 => TP (Tf f (dx n)) (Tf f (dy n))
         | 2 => TM (Tf f (dx n)) (Tf f (dy n))
         | _ => TV (dx n)
         end
  end.
Proof. reflexivity. Qed.

Lemma Df_S f n : Df (S f) n =
  match n with
  | 0 => truth
  | _ => match dtag n with
         | 0 => Wim (Df f (dx n)) (Df f (dy n))
         | 1 => Weq (TS (T (dx n))) (T (dy n))
         | 2 => Wal (dx n) (Df f (dy n))
         | _ => Weq (T (dx n)) (T (dy n))
         end
  end.
Proof. reflexivity. Qed.

Lemma T_unfold n : 0 < n -> T n =
  match dtag n with
  | 0 => TS (T (dx n))
  | 1 => TP (T (dx n)) (T (dy n))
  | 2 => TM (T (dx n)) (T (dy n))
  | _ => TV (dx n)
  end.
Proof.
  intro H. unfold T at 1. rewrite Tf_S. destruct n as [|n']; [lia|].
  pose proof (dx_lt (S n') H). pose proof (dy_lt (S n') H). unfold T.
  rewrite (Tf_fuel (S n') (S (dx (S n'))) (dx (S n'))) by lia.
  rewrite (Tf_fuel (S n') (S (dy (S n'))) (dy (S n'))) by lia.
  reflexivity.
Qed.

Lemma D_unfold n : 0 < n -> D n =
  match dtag n with
  | 0 => Wim (D (dx n)) (D (dy n))
  | 1 => Weq (TS (T (dx n))) (T (dy n))
  | 2 => Wal (dx n) (D (dy n))
  | _ => Weq (T (dx n)) (T (dy n))
  end.
Proof.
  intro H. unfold D at 1. rewrite Df_S. destruct n as [|n']; [lia|].
  pose proof (dx_lt (S n') H). pose proof (dy_lt (S n') H). unfold D.
  rewrite (Df_fuel (S n') (S (dx (S n'))) (dx (S n'))) by lia.
  rewrite (Df_fuel (S n') (S (dy (S n'))) (dy (S n'))) by lia.
  reflexivity.
Qed.

(** ** Decoding the constructors *)
Lemma P_pos_or a b : 0 < 4 * P a b + 1.
Proof. lia. Qed.

Lemma T_tpl j k : T (tpl j k) = TP (T j) (T k).
Proof.
  unfold tpl. rewrite T_unfold by lia. destruct (split_code j k 1 ltac:(lia)) as (E1 & E2 & E3).
  now rewrite E1, E2, E3.
Qed.

Lemma T_tml j k : T (tml j k) = TM (T j) (T k).
Proof.
  unfold tml. rewrite T_unfold by lia. destruct (split_code j k 2 ltac:(lia)) as (E1 & E2 & E3).
  now rewrite E1, E2, E3.
Qed.

Lemma T_tvar i : T (tvar i) = TV i.
Proof.
  unfold tvar. rewrite T_unfold by lia. destruct (split_code i 0 3 ltac:(lia)) as (E1 & E2 & E3).
  now rewrite E1, E3.
Qed.

Lemma tsc_pos j : 0 < tsc j.
Proof. unfold tsc, P. lia. Qed.

Lemma T_tsc j : T (tsc j) = TS (T j).
Proof.
  rewrite T_unfold by apply tsc_pos. unfold tsc.
  destruct (split_code j 1 0 ltac:(lia)) as (E1 & E2 & E3). rewrite Nat.add_0_r in E1, E2, E3.
  now rewrite E1, E3.
Qed.

Lemma T_0 : T 0 = TZ.
Proof. reflexivity. Qed.

Lemma wim_pos a b : (0 < a \/ 0 < b) -> 0 < wim a b.
Proof.
  intro H. unfold wim. destruct (Nat.eq_dec (P a b) 0) as [Z|Z]; [apply P_0 in Z; lia | lia].
Qed.

Lemma D_wim a b : (0 < a \/ 0 < b) -> D (wim a b) = Wim (D a) (D b).
Proof.
  intro H. rewrite D_unfold by now apply wim_pos. unfold wim.
  destruct (split_code a b 0 ltac:(lia)) as (E1 & E2 & E3). rewrite Nat.add_0_r in E1, E2, E3.
  now rewrite E1, E2, E3.
Qed.

Lemma D_wseq x y : D (wseq x y) = Weq (TS (T x)) (T y).
Proof.
  unfold wseq. rewrite D_unfold by lia. destruct (split_code x y 1 ltac:(lia)) as (E1 & E2 & E3).
  now rewrite E1, E2, E3.
Qed.

Lemma D_wal i a : D (wal i a) = Wal i (D a).
Proof.
  unfold wal. rewrite D_unfold by lia. destruct (split_code i a 2 ltac:(lia)) as (E1 & E2 & E3).
  now rewrite E1, E2, E3.
Qed.

Lemma D_weq x y : D (weq x y) = Weq (T x) (T y).
Proof.
  unfold weq. rewrite D_unfold by lia. destruct (split_code x y 3 ltac:(lia)) as (E1 & E2 & E3).
  now rewrite E1, E2, E3.
Qed.

Lemma D_F : D F = Weq (TS TZ) TZ.
Proof. reflexivity. Qed.

Lemma D_0 : D 0 = truth.
Proof. reflexivity. Qed.

(** ** Self-freshness *)
Lemma T_fresh n v : tocc v (T n) = true -> v < n.
Proof.
  induction n as [n IH] using lt_wf_ind. intro H.
  destruct n as [|n']; [discriminate|]. rewrite T_unfold in H by lia.
  pose proof (dx_lt (S n') ltac:(lia)). pose proof (dy_lt (S n') ltac:(lia)).
  destruct (dtag (S n')) as [|[|[|]]]; cbn in H.
  - specialize (IH _ H0 H). lia.
  - apply orb_true_iff in H as [H|H]; [specialize (IH _ H0 H) | specialize (IH _ H1 H)]; lia.
  - apply orb_true_iff in H as [H|H]; [specialize (IH _ H0 H) | specialize (IH _ H1 H)]; lia.
  - apply Nat.eqb_eq in H. lia.
Qed.

Lemma D_fresh n v : occ v (D n) = true -> v < n.
Proof.
  induction n as [n IH] using lt_wf_ind. intro H.
  destruct n as [|n']; [discriminate|]. rewrite D_unfold in H by lia.
  pose proof (dx_lt (S n') ltac:(lia)). pose proof (dy_lt (S n') ltac:(lia)).
  destruct (dtag (S n')) as [|[|[|]]]; cbn in H.
  - apply orb_true_iff in H as [H|H]; [specialize (IH _ H0 H) | specialize (IH _ H1 H)]; lia.
  - apply orb_true_iff in H as [H|H]; [apply T_fresh in H | apply T_fresh in H]; lia.
  - apply orb_true_iff in H as [H|H]; [apply Nat.eqb_eq in H; lia | specialize (IH _ H1 H); lia].
  - apply orb_true_iff in H as [H|H]; apply T_fresh in H; lia.
Qed.

(** ** Occurs check on term codes (as zf/pagb/machine/spec_pa.py tvars: tag 3 = variable dx,
    tag 0 = σ of dx (dy is junk), tags 1, 2 = both components) *)
Fixpoint toc (fuel v n : nat) : bool :=
  match fuel with
  | 0 => false
  | S f =>
      match n with
      | 0 => false
      | _ => match dtag n with
             | 0 => toc f v (dx n)
             | 1 | 2 => toc f v (dx n) || toc f v (dy n)
             | _ => Nat.eqb (dx n) v
             end
      end
  end.

Definition occT (v n : nat) : bool := toc (S n) v n.

Lemma toc_S f v n : toc (S f) v n =
  match n with
  | 0 => false
  | _ => match dtag n with
         | 0 => toc f v (dx n)
         | 1 | 2 => toc f v (dx n) || toc f v (dy n)
         | _ => Nat.eqb (dx n) v
         end
  end.
Proof. reflexivity. Qed.

Lemma toc_T f v n : n < f -> toc f v n = tocc v (T n).
Proof.
  revert n; induction f as [|f IH]; intros n Hf; [lia|]. rewrite toc_S.
  destruct n as [|n']; [reflexivity|]. rewrite T_unfold by lia.
  pose proof (dx_lt (S n') ltac:(lia)). pose proof (dy_lt (S n') ltac:(lia)).
  destruct (dtag (S n')) as [|[|[|]]]; cbn [tocc];
    rewrite ?(IH (dx (S n'))), ?(IH (dy (S n'))) by lia; reflexivity.
Qed.

Theorem occT_spec v n : occT v n = tocc v (T n).
Proof. apply toc_T. lia. Qed.
