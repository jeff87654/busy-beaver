(** Standard fast-growing hierarchy below omega^3 (bb8 conventions).
      f 0 = S,  f (k+1) n = iter n (f k) n                       (f_k)
      f_wa a b = f_(omega*a + b):  f_wa 0 b = f b,  f_wa a (S b) n = iter n (f_wa a b) n,  f_wa (S a) 0 n = f_wa a n n
      f_wsq n = f_(omega^2)(n) = f_wa n 0 n.
    Checked below against BB20_JZ20.v and BB18_R18a.v:  f_wa 1 k = f_wk k  and  f_wa 2 0 = f_w2. *)
From Coq Require Import Lia PeanoNat.
From BB8 Require Import BB21_B21_absdef.
From BB8 Require BB20_JZ20 BB18_R18a.
Set Default Goal Selector "!".

Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | 0 => S
  | S k' => fun n => iter n (f k') n
  end.

Fixpoint f_wa (a : nat) : nat -> nat -> nat :=
  match a with
  | 0 => fun b => f b
  | S a' => fix fb (b : nat) : nat -> nat :=
      match b with
      | 0 => fun n => f_wa a' n n
      | S b' => fun n => iter n (fb b') n
      end
  end.

Definition f_wsq (n : nat) : nat := f_wa n 0 n.

Lemma f_wa_0 : forall b n, f_wa 0 b n = f b n.
Proof. reflexivity. Qed.
Lemma f_wa_S : forall a b n, f_wa a (S b) n = iter n (f_wa a b) n.
Proof. intros [| a] b n; reflexivity. Qed.
Lemma f_wa_lim : forall a n, f_wa (S a) 0 n = f_wa a n n.
Proof. reflexivity. Qed.

(** ** agreement with the earlier files *)
Lemma iter_JZ : forall {X : Type} n (g : X -> X) x, BB20_JZ20.iter n g x = iter n g x.
Proof. induction n; intros; simpl; [reflexivity |]. rewrite IHn. reflexivity. Qed.
Lemma iter_R18 : forall {X : Type} n (g : X -> X) x, BB18_R18a.iter n g x = iter n g x.
Proof. induction n; intros; simpl; [reflexivity |]. rewrite IHn. reflexivity. Qed.



(** pointwise, without function extensionality *)
Lemma iter_ext : forall n (g g' : nat -> nat) x, (forall y, g y = g' y) -> iter n g x = iter n g' x.
Proof. induction n; intros; simpl; [reflexivity |]. rewrite (IHn g g' x H). apply H. Qed.

Lemma f_JZ : forall k n, BB20_JZ20.f k n = f k n.
Proof.
  induction k; intros; simpl; [reflexivity |]. rewrite iter_JZ. apply iter_ext. exact IHk.
Qed.

Lemma f_R18 : forall k n, BB18_R18a.f k n = f k n.
Proof.
  induction k; intros; simpl; [reflexivity |]. rewrite iter_R18. apply iter_ext. exact IHk.
Qed.

Lemma f_wk_JZ : forall k n, BB20_JZ20.f_wk k n = f_wa 1 k n.
Proof.
  induction k; intros.
  - simpl. unfold BB20_JZ20.f_omega. apply f_JZ.
  - simpl BB20_JZ20.f_wk. rewrite f_wa_S, iter_JZ. apply iter_ext. exact IHk.
Qed.

Lemma f_wk_R18 : forall k n, BB18_R18a.f_wk k n = f_wa 1 k n.
Proof.
  induction k; intros.
  - simpl. unfold BB18_R18a.f_omega. apply f_R18.
  - simpl BB18_R18a.f_wk. rewrite f_wa_S, iter_R18. apply iter_ext. exact IHk.
Qed.

Lemma f_w2_JZ : forall n, BB20_JZ20.f_w2 n = f_wa 2 0 n.
Proof. intros. unfold BB20_JZ20.f_w2. rewrite f_wa_lim. apply f_wk_JZ. Qed.

Lemma f_w2_R18 : forall n, BB18_R18a.f_w2 n = f_wa 2 0 n.
Proof. intros. unfold BB18_R18a.f_w2. rewrite f_wa_lim. apply f_wk_R18. Qed.

Lemma f_omega_JZ : forall n, BB20_JZ20.f_omega n = f_wa 1 0 n.
Proof. intros. unfold BB20_JZ20.f_omega. rewrite f_wa_lim, f_wa_0. apply f_JZ. Qed.

(** ** basic properties *)
Definition good (g : nat -> nat) : Prop := (forall x, x <= g x) /\ (forall x y, x <= y -> g x <= g y).

Lemma iter_ge_id : forall g, (forall x, x <= g x) -> forall n x, x <= iter n g x.
Proof. intros g H. induction n; intros; simpl; [lia |]. specialize (IHn x). specialize (H (iter n g x)). lia. Qed.

Lemma iter_mono_arg : forall g, (forall x y, x <= y -> g x <= g y) -> forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g H. induction n; intros; simpl; [lia |]. apply H, IHn. lia. Qed.

Lemma iter_mono_cnt : forall g, (forall x, x <= g x) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g H n m x Hnm. replace m with ((m - n) + n) by lia. rewrite iter_add. apply iter_ge_id. exact H.
Qed.

Lemma good_diag : forall g, good g -> good (fun n => iter n g n).
Proof.
  intros g [H1 H2]. split.
  - intros x. apply iter_ge_id. exact H1.
  - intros x y Hxy. transitivity (iter x g y); [apply iter_mono_arg; assumption | apply iter_mono_cnt; assumption].
Qed.

Lemma good_f : forall k, good (f k).
Proof.
  induction k.
  - split; intros; simpl; lia.
  - apply good_diag. exact IHk.
Qed.

Lemma iter_diag_ge : forall g, good g -> forall y, 1 <= y -> g y <= iter y g y.
Proof.
  intros g [H1 H2] y Hy. destruct y as [| y]; [lia |]. simpl. apply H2. apply iter_ge_id. exact H1.
Qed.

Lemma good_f_wa_b : forall a, (forall b, good (f_wa a b)) -> forall b b' y, b <= b' -> 1 <= y -> f_wa a b y <= f_wa a b' y.
Proof.
  intros a G b b' y Hb Hy. induction Hb; [lia |]. rewrite f_wa_S. pose proof (iter_diag_ge _ (G m) y Hy). lia.
Qed.

Lemma good_f_wa : forall a b, good (f_wa a b).
Proof.
  induction a as [| a IHa].
  - intros b. apply good_f.
  - induction b as [| b IHb].
    + split; intros; rewrite !f_wa_lim.
      * apply (proj1 (IHa x)).
      * transitivity (f_wa a x y); [apply (proj2 (IHa x)); exact H |].
        destruct y as [| y]; [assert (x = 0) by lia; subst; lia |].
        apply (good_f_wa_b a IHa); lia.
    + assert (E : forall n, f_wa (S a) (S b) n = iter n (f_wa (S a) b) n) by (intros; apply f_wa_S).
      destruct (good_diag _ IHb) as [G1 G2]. split; intros; rewrite !E; [apply G1 | apply G2; assumption].
Qed.

Lemma f_wa_b_mono : forall a b b' y, b <= b' -> 1 <= y -> f_wa a b y <= f_wa a b' y.
Proof. intros a. apply good_f_wa_b. intros. apply good_f_wa. Qed.

Lemma f_wa_mono : forall a b x y, x <= y -> f_wa a b x <= f_wa a b y.
Proof. intros. apply (proj2 (good_f_wa a b)). exact H. Qed.

Lemma f_wa_id : forall a b x, x <= f_wa a b x.
Proof. intros. apply (proj1 (good_f_wa a b)). Qed.

(** the limit index is increasing: f_wa a 0 y <= f_wa a' 0 y for a <= a' *)
Lemma f_wa_a_mono : forall a a' y, a <= a' -> 1 <= y -> f_wa a 0 y <= f_wa a' 0 y.
Proof.
  intros a a' y Ha Hy. induction Ha; [lia |]. rewrite f_wa_lim.
  pose proof (f_wa_b_mono m 0 y y ltac:(lia) Hy). lia.
Qed.

Lemma f_wsq_mono : forall x y, x <= y -> f_wsq x <= f_wsq y.
Proof.
  intros x y H. unfold f_wsq. destruct x as [| x]; [destruct y as [| y]; [reflexivity | pose proof (f_wa_id (S y) 0 (S y)); simpl f_wa at 1; lia] |].
  transitivity (f_wa (S x) 0 y); [apply f_wa_mono; exact H | apply f_wa_a_mono; lia].
Qed.
