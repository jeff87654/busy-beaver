(** * L1_Arith: Cantor pairing facts and a total decoder [D : nat -> wff]. *)
From Coq Require Import Arith.Arith Lia.
From ZF Require Import Logic.

Lemma tri_S s : tri (S s) = tri s + S s.
Proof.
  unfold tri. replace (S s * (S s + 1)) with (s * (s + 1) + S s * 2) by ring.
  rewrite Nat.div_add by lia. reflexivity.
Qed.

Lemma tri_ge s : s <= tri s.
Proof. induction s; [cbv; lia | rewrite tri_S; lia]. Qed.

Lemma unpair_S z : unpair (S z) = unpair_step (unpair z).
Proof. reflexivity. Qed.

Lemma unpair_diag s : forall x, x <= s -> unpair (x + tri s) = (x, s - x).
Proof.
  induction s as [|s IH]; intros x Hx.
  - assert (x = 0) by lia. subst. reflexivity.
  - induction x as [|x IHx].
    + rewrite Nat.add_0_l, tri_S.
      replace (tri s + S s) with (S (s + tri s)) by lia.
      rewrite unpair_S, IH by lia. rewrite Nat.sub_diag. reflexivity.
    + rewrite Nat.add_succ_l, unpair_S, IHx by lia.
      replace (S s - x) with (S (s - x)) by lia. reflexivity.
Qed.

Lemma unpair_pair x y : unpair (pair x y) = (x, y).
Proof.
  unfold pair. rewrite unpair_diag by lia. f_equal. lia.
Qed.

Lemma pair_unpair z : pair (fst (unpair z)) (snd (unpair z)) = z.
Proof.
  induction z as [|z IH]; [reflexivity|].
  rewrite unpair_S. destruct (unpair z) as [x [|y]]; cbn [fst snd unpair_step] in *.
  - unfold pair in *. rewrite Nat.add_0_r in *. rewrite !Nat.add_0_l, tri_S. lia.
  - unfold pair in *. replace (S x + y) with (x + S y) by lia. lia.
Qed.

Lemma pair_inj x y x' y' : pair x y = pair x' y' -> x = x' /\ y = y'.
Proof.
  intro H. assert (E : unpair (pair x y) = unpair (pair x' y')) by now rewrite H.
  rewrite !unpair_pair in E. now injection E.
Qed.

Lemma pair_ge_r x y : y <= pair x y.
Proof. unfold pair. pose proof (tri_ge (x + y)). lia. Qed.

Lemma pair_ge_l x y : x <= pair x y.
Proof. unfold pair. lia. Qed.

Lemma pair_gt_l x y : 0 < y -> x < pair x y.
Proof. intro. unfold pair. pose proof (tri_ge (x + y)). lia. Qed.

Lemma unpair_le z : fst (unpair z) <= z /\ snd (unpair z) <= z.
Proof.
  rewrite <- (pair_unpair z) at 2 4. split; [apply pair_ge_l | apply pair_ge_r].
Qed.

(** ** Total decoder: invalid tags decode to [Weq 0 0]; garbage is treated as an opaque wff. *)
Definition Dbody (rec : nat -> wff) (z : nat) : wff :=
  let '(p, t) := unpair z in
  match t with
  | 0 => let '(x, y) := unpair p in Weq x y
  | 1 => let '(x, y) := unpair p in Wel x y
  | 2 => let '(a, b) := unpair p in Wim (rec a) (rec b)
  | 3 => Wn (rec p)
  | 4 => let '(x, a) := unpair p in Wal x (rec a)
  | _ => Weq 0 0
  end.

Fixpoint Df (f z : nat) : wff :=
  match f with
  | 0 => Weq 0 0
  | S f => Dbody (Df f) z
  end.

Definition D (z : nat) : wff := Df (S z) z.

Lemma Df_stable f : forall g z, z < f -> z < g -> Df f z = Df g z.
Proof.
  induction f as [|f IH]; intros [|g] z H1 H2; try lia. simpl.
  unfold Dbody. pose proof (pair_unpair z) as Ez.
  destruct (unpair z) as [p t]. simpl in Ez.
  pose proof (pair_unpair p) as Ep. destruct (unpair p) as [a b]. simpl in Ep.
  assert (Ha : a <= p) by (rewrite <- Ep; apply pair_ge_l).
  assert (Hb : b <= p) by (rewrite <- Ep; apply pair_ge_r).
  destruct t as [|[|[|[|[|t]]]]]; try reflexivity.
  - assert (p < z) by (rewrite <- Ez; apply pair_gt_l; lia).
    rewrite (IH g a), (IH g b) by lia. reflexivity.
  - assert (p < z) by (rewrite <- Ez; apply pair_gt_l; lia).
    rewrite (IH g p) by lia. reflexivity.
  - assert (p < z) by (rewrite <- Ez; apply pair_gt_l; lia).
    rewrite (IH g b) by lia. reflexivity.
Qed.

Lemma D_0 : D 0 = Weq 0 0.
Proof. reflexivity. Qed.

Lemma D_weq x y : D (weq x y) = Weq x y.
Proof. unfold D, weq. simpl Df. unfold Dbody. rewrite !unpair_pair. reflexivity. Qed.

Lemma D_wel x y : D (wel x y) = Wel x y.
Proof. unfold D, wel. simpl Df. unfold Dbody. rewrite !unpair_pair. reflexivity. Qed.

Lemma D_wim a b : D (wim a b) = Wim (D a) (D b).
Proof.
  unfold D at 1, wim. simpl Df. unfold Dbody. rewrite !unpair_pair. cbv beta iota.
  assert (pair a b < pair (pair a b) 2) by (apply pair_gt_l; lia).
  pose proof (pair_ge_l a b). pose proof (pair_ge_r a b).
  unfold D. f_equal; apply Df_stable; lia.
Qed.

Lemma D_wn a : D (wn a) = Wn (D a).
Proof.
  unfold D at 1, wn. simpl Df. unfold Dbody. rewrite !unpair_pair. cbv beta iota.
  assert (a < pair a 3) by (apply pair_gt_l; lia).
  unfold D. f_equal; apply Df_stable; lia.
Qed.

Lemma D_wal x a : D (wal x a) = Wal x (D a).
Proof.
  unfold D at 1, wal. simpl Df. unfold Dbody. rewrite !unpair_pair. cbv beta iota.
  assert (pair x a < pair (pair x a) 4) by (apply pair_gt_l; lia).
  pose proof (pair_ge_r x a).
  unfold D. f_equal; apply Df_stable; lia.
Qed.

Lemma D_wex x a : D (wex x a) = Wex x (D a).
Proof. unfold wex. rewrite D_wn, D_wal, D_wn. reflexivity. Qed.

Lemma D_wa a b : D (wa a b) = Wa (D a) (D b).
Proof. unfold wa. rewrite D_wn, D_wim, D_wn. reflexivity. Qed.

Lemma D_code a : D (code a) = a.
Proof.
  induction a; simpl code.
  - apply D_weq.
  - apply D_wel.
  - change (D (wim (code a1) (code a2)) = Wim a1 a2). rewrite D_wim. congruence.
  - change (D (wn (code a)) = Wn a). rewrite D_wn. congruence.
  - change (D (wal x (code a)) = Wal x a). rewrite D_wal. congruence.
Qed.
