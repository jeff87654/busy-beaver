(** * Upper bounds for the level maps of Jacobzheng's two-list engine (generic).

    Written by this project for the exact-score comparisons of the J- and R-machines (BB(16) to BB(20)).
    The machines' Coq files define, each with the same text,
      h 0 x = x + 4,  h (m+1) x = iter (x+2) (h m) 2,   hc m 0 x = x,  hc m (n+1) x = hc (m+1) n (h m x)
    and an outer head map G, outer level maps ho 0 = G, ho (m+1) a = iter (a+1) (ho m) r (r a small reset value),
    hoc m 0 a = a, hoc m (n+1) a = hoc (m+1) n (ho m a).  This file proves, for any functions satisfying these
    equations (Section variables and hypotheses, so no machine file is loaded here):
      h_ub    : h m y + 4 <= f (m+1) (y + 4)
      hc_ub   : hc m n x + 4 <= f_omega (m + n + x + 5)
      ho_ub   : ho m a + 20 <= f_wk m (a + 20)                  (given G a + 20 <= f_omega (a + 20) and r <= 19)
      hoc_ub  : hoc m n a + 20 <= f_wk (m + n + 1) (n + a + 20)
    with the standard fast-growing hierarchy, defined here with the same text as in the machine files
    (f 0 = S, f (k+1) n = iter n (f k) n, f_omega n = f n n, f_wk 0 = f_omega, f_wk (k+1) n = iter n (f_wk k) n,
    f_w2 n = f_wk n n).  The comparison files transfer these bounds to each machine's own definitions. *)

From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.

Fixpoint iter {X : Type} (n : nat) (g : X -> X) (x : X) : X :=
  match n with
  | 0 => x
  | S n' => g (iter n' g x)
  end.

Lemma iter_0 : forall {X : Type} (g : X -> X) x, iter 0 g x = x.
Proof. reflexivity. Qed.

Lemma iter_S1 : forall {X : Type} n (g : X -> X) x, iter (S n) g x = g (iter n g x).
Proof. reflexivity. Qed.

Lemma iter_S' : forall {X : Type} n (g : X -> X) x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

Lemma iter_add : forall {X : Type} a b (g : X -> X) x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

Lemma iter_ext : forall {X : Type} (g1 g2 : X -> X), (forall x, g1 x = g2 x) ->
  forall n x, iter n g1 x = iter n g2 x.
Proof. intros X g1 g2 Hg. induction n; intros x; simpl; [reflexivity | rewrite IHn; apply Hg]. Qed.

Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | 0 => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.

Fixpoint f_wk (k : nat) : nat -> nat :=
  match k with
  | 0 => f_omega
  | S k' => fun n => iter n (f_wk k') n
  end.

Definition f_w2 (n : nat) : nat := f_wk n n.

(** ** Generic facts about iteration *)
Lemma iter_mono_x : forall g, (forall a b, a <= b -> g a <= g b) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; auto. Qed.

Lemma iter_ge : forall g, (forall a, a <= g a) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_mono_n : forall g, (forall a, a <= g a) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite iter_add. apply iter_ge. exact Hg.
Qed.

Lemma iter_gt1 : forall g, (forall y, 1 <= y -> y + 1 <= g y) -> forall n x, 1 <= x -> x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros x Hx; simpl. - lia.
  - specialize (IHn x Hx). specialize (Hg (iter n g x) ltac:(lia)). lia.
Qed.

(** An iteration bound transported along a pointwise bound g y + c <= F (y + c). *)
Lemma iter_shift : forall (g F : nat -> nat) c, (forall a b, a <= b -> F a <= F b) ->
  (forall y, g y + c <= F (y + c)) -> forall n y, iter n g y + c <= iter n F (y + c).
Proof.
  intros g F c HF Hg. induction n; intros y; simpl. - lia.
  - specialize (IHn y). specialize (Hg (iter n g y)). specialize (HF _ _ IHn). lia.
Qed.

(** ** The fast-growing hierarchy *)
Lemma f_S : forall k n, f (S k) n = iter n (f k) n.
Proof. reflexivity. Qed.

Lemma f_props : forall k, (forall n, n <= f k n) /\ (forall a b, a <= b -> f k a <= f k b).
Proof.
  induction k as [| k [Hid Hmono]].
  - split; intros; simpl; lia.
  - split.
    + intros n. rewrite f_S. apply iter_ge. exact Hid.
    + intros a b Hab. rewrite !f_S. transitivity (iter a (f k) b).
      * apply iter_mono_x; assumption.
      * apply iter_mono_n; assumption.
Qed.

Lemma f_id : forall k n, n <= f k n.
Proof. intros. apply f_props. Qed.

Lemma f_mono : forall k a b, a <= b -> f k a <= f k b.
Proof. intros. apply f_props. assumption. Qed.

Lemma f_gt : forall k n, 1 <= n -> n < f k n.
Proof.
  induction k; intros n Hn.
  - simpl. lia.
  - rewrite f_S. destruct n as [| n']; [lia |].
    simpl. pose proof (iter_ge (f k) (f_id k) n' (S n')).
    specialize (IHk (iter n' (f k) (S n')) ltac:(lia)). lia.
Qed.

Lemma f_gt1 : forall k n, 1 <= n -> n + 1 <= f k n.
Proof. intros k n Hn. pose proof (f_gt k n Hn). lia. Qed.

Lemma f_level : forall k n, 1 <= n -> f k n <= f (S k) n.
Proof.
  intros k n Hn. rewrite f_S. destruct n as [| n']; [lia |].
  rewrite iter_S'. apply iter_ge. apply f_id.
Qed.

Lemma f_level_mono : forall d k n, 1 <= n -> f k n <= f (d + k) n.
Proof.
  induction d; intros k n Hn. - reflexivity.
  - specialize (IHd k n Hn). pose proof (f_level (d + k) n Hn). change (S d + k) with (S (d + k)). lia.
Qed.

Lemma f_level_le : forall k K n, k <= K -> 1 <= n -> f k n <= f K n.
Proof.
  intros k K n HkK Hn. replace K with ((K - k) + k) by lia. apply f_level_mono; exact Hn.
Qed.

Lemma iter_succ_add : forall n x, iter n S x = n + x.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

Lemma f1 : forall n, f 1 n = 2 * n.
Proof. intros. rewrite f_S. rewrite iter_succ_add. lia. Qed.

Lemma f_dbl : forall k n, 1 <= k -> 2 * n <= f k n.
Proof.
  intros k n Hk. destruct n as [| n']. - lia.
  - rewrite <- f1. replace k with ((k - 1) + 1) by lia. apply f_level_mono. lia.
Qed.

Lemma f_succ_dbl : forall k w, 2 <= k -> 2 * f k w <= f k (S w).
Proof.
  intros k w Hk. destruct k as [| k']; [lia |].
  rewrite !f_S. cbn [iter].
  pose proof (f_dbl k' (iter w (f k') (S w)) ltac:(lia)).
  pose proof (iter_mono_x (f k') (f_mono k') w w (S w) ltac:(lia)). lia.
Qed.

Lemma f_omega_eq : forall n, f_omega n = f n n.  Proof. reflexivity. Qed.
Lemma f_omega_id : forall n, n <= f_omega n.  Proof. intros n. apply f_id. Qed.

Lemma f_omega_ge2 : forall n, 1 <= n -> 2 * n <= f_omega n.
Proof. intros n Hn. rewrite f_omega_eq. apply f_dbl; exact Hn. Qed.

Lemma f_omega_mono : forall a b, a <= b -> f_omega a <= f_omega b.
Proof.
  intros [| a'] b Hab.
  - destruct b as [| b']. + reflexivity.
    + change (f_omega 0) with 1. pose proof (f_omega_id (S b')). lia.
  - rewrite !f_omega_eq.
    pose proof (f_level_mono (b - S a') (S a') (S a') ltac:(lia)) as L1.
    replace (b - S a' + S a') with b in L1 by lia.
    pose proof (f_mono b (S a') b Hab). lia.
Qed.

Lemma f_omega_dbl : forall z, 2 <= z -> 2 * f_omega z <= f_omega (S z).
Proof.
  intros z Hz. rewrite !f_omega_eq.
  pose proof (f_succ_dbl z z Hz). pose proof (f_level z (S z) ltac:(lia)). lia.
Qed.

(** f_k(n) <= f_omega(z) when k <= z and n <= z *)
Lemma f_le_omega : forall k n z, k <= z -> n <= z -> 1 <= z -> f k n <= f_omega z.
Proof.
  intros k n z Hk Hn Hz. rewrite f_omega_eq.
  pose proof (f_mono k n z Hn). pose proof (f_level_le k z z Hk Hz). lia.
Qed.

Lemma f_wk_0 : forall n, f_wk 0 n = f_omega n.  Proof. reflexivity. Qed.
Lemma f_wk_S : forall k n, f_wk (S k) n = iter n (f_wk k) n.  Proof. reflexivity. Qed.

Lemma f_wk_props : forall k, (forall n, n <= f_wk k n) /\ (forall a b, a <= b -> f_wk k a <= f_wk k b).
Proof.
  induction k as [| k [Hid Hmono]].
  - split. + apply f_omega_id. + apply f_omega_mono.
  - split.
    + intros n. rewrite f_wk_S. apply iter_ge. exact Hid.
    + intros a b Hab. rewrite !f_wk_S. transitivity (iter a (f_wk k) b).
      * apply iter_mono_x; assumption.
      * apply iter_mono_n; assumption.
Qed.

Lemma f_wk_id : forall k n, n <= f_wk k n.  Proof. intros. apply f_wk_props. Qed.
Lemma f_wk_mono : forall k a b, a <= b -> f_wk k a <= f_wk k b.  Proof. intros. apply f_wk_props. assumption. Qed.

Lemma f_wk_level : forall k n, 1 <= n -> f_wk k n <= f_wk (S k) n.
Proof.
  intros k n Hn. rewrite f_wk_S. destruct n as [| n']; [lia |].
  rewrite iter_S'. apply iter_ge. apply f_wk_id.
Qed.

Lemma f_wk_level_mono : forall d k n, 1 <= n -> f_wk k n <= f_wk (d + k) n.
Proof.
  induction d; intros k n Hn. - reflexivity.
  - specialize (IHd k n Hn). pose proof (f_wk_level (d + k) n Hn). change (S d + k) with (S (d + k)). lia.
Qed.

Lemma f_wk_level_le : forall k K n, k <= K -> 1 <= n -> f_wk k n <= f_wk K n.
Proof.
  intros k K n HkK Hn. replace K with ((K - k) + k) by lia. apply f_wk_level_mono; exact Hn.
Qed.

Lemma f_wk_ge2 : forall k n, 1 <= n -> 2 * n <= f_wk k n.
Proof.
  intros k n Hn. pose proof (f_omega_ge2 n Hn). pose proof (f_wk_level_le 0 k n ltac:(lia) Hn).
  rewrite f_wk_0 in *. lia.
Qed.

Lemma f_wk_gt : forall k n, 1 <= n -> n + 1 <= f_wk k n.
Proof. intros k n Hn. pose proof (f_wk_ge2 k n Hn). lia. Qed.

(** iter p (f_wk K) x <= f_wk (K+1) z  when p <= z and x <= z *)
Lemma iter_wk_le : forall K p x z, p <= z -> x <= z -> iter p (f_wk K) x <= f_wk (S K) z.
Proof.
  intros K p x z Hp Hx. rewrite f_wk_S.
  pose proof (iter_mono_x (f_wk K) (f_wk_mono K) p x z Hx).
  pose proof (iter_mono_n (f_wk K) (f_wk_id K) p z z Hp). lia.
Qed.

Lemma f_w2_eq : forall n, f_w2 n = f_wk n n.  Proof. reflexivity. Qed.

(** f_wk K z <= f_w2 z  when K <= z *)
Lemma f_wk_le_w2 : forall K z, K <= z -> 1 <= z -> f_wk K z <= f_w2 z.
Proof. intros K z HK Hz. rewrite f_w2_eq. apply f_wk_level_le; assumption. Qed.

Lemma f_w2_mono : forall a b, a <= b -> f_w2 a <= f_w2 b.
Proof.
  intros [| a'] b Hab; rewrite !f_w2_eq.
  - destruct b as [| b']. + reflexivity.
    + pose proof (f_wk_mono 0 0 (S b') ltac:(lia)).
      pose proof (f_wk_level_le 0 (S b') (S b') ltac:(lia) ltac:(lia)). lia.
  - pose proof (f_wk_level_le (S a') b b Hab ltac:(lia)).
    pose proof (f_wk_mono (S a') (S a') b Hab). lia.
Qed.

Lemma f_w2_gt : forall n, 1 <= n -> n + 1 <= f_w2 n.
Proof. intros n Hn. rewrite f_w2_eq. apply f_wk_gt; exact Hn. Qed.

(** ** The inner level maps *)
Section Inner.
Variable h : nat -> nat -> nat.
Hypothesis h_0 : forall x, h 0 x = x + 4.
Hypothesis h_S : forall m x, h (S m) x = iter (x + 2) (h m) 2.
Variable hc : nat -> nat -> nat -> nat.
Hypothesis hc_0 : forall m x, hc m 0 x = x.
Hypothesis hc_S : forall m n x, hc m (S n) x = hc (S m) n (h m x).

Lemma h_ub : forall m y, h m y + 4 <= f (S m) (y + 4).
Proof.
  induction m as [| m IH]; intros y.
  - rewrite h_0, f1. lia.
  - rewrite h_S, (f_S (S m)).
    pose proof (iter_shift (h m) (f (S m)) 4 (f_mono (S m)) IH (y + 2) 2) as H1.
    change (2 + 4) with 6 in H1.
    assert (H6 : 6 <= iter 2 (f (S m)) (y + 4)).
    { pose proof (iter_gt1 (f (S m)) (f_gt1 (S m)) 2 (y + 4) ltac:(lia)). lia. }
    pose proof (iter_mono_x (f (S m)) (f_mono (S m)) (y + 2) 6 _ H6) as H2.
    rewrite <- iter_add in H2. replace (y + 2 + 2) with (y + 4) in H2 by lia. lia.
Qed.

Lemma hc_ub_iter : forall n m x, hc m n x + 4 <= iter n (f (m + n)) (x + 4).
Proof.
  induction n as [| n IH]; intros m x.
  - rewrite hc_0. simpl. lia.
  - rewrite hc_S. specialize (IH (S m) (h m x)). replace (S m + n) with (m + S n) in IH by lia.
    pose proof (h_ub m x) as Hh.
    pose proof (f_level_le (S m) (m + S n) (x + 4) ltac:(lia) ltac:(lia)) as Hl.
    pose proof (iter_mono_x (f (m + S n)) (f_mono (m + S n)) n (h m x + 4) (f (m + S n) (x + 4)) ltac:(lia)) as H2.
    rewrite <- iter_S' in H2. lia.
Qed.

Lemma hc_ub : forall n m x, hc m n x + 4 <= f_omega (m + n + x + 5).
Proof.
  intros n m x. pose proof (hc_ub_iter n m x) as H1.
  set (z := m + n + x + 5).
  pose proof (iter_mono_x (f (m + n)) (f_mono (m + n)) n (x + 4) z ltac:(unfold z; lia)) as H2.
  pose proof (iter_mono_n (f (m + n)) (f_id (m + n)) n z z ltac:(unfold z; lia)) as H3.
  rewrite <- f_S in H3.
  pose proof (f_le_omega (S (m + n)) z z ltac:(unfold z; lia) ltac:(lia) ltac:(unfold z; lia)) as H4.
  lia.
Qed.
End Inner.

(** ** The outer level maps *)
Section Outer.
Variable G : nat -> nat.
Variable r : nat.
Variable ho : nat -> nat -> nat.
Hypothesis G_ub : forall a, G a + 20 <= f_omega (a + 20).
Hypothesis r_le : r <= 19.
Hypothesis ho_0 : forall a, ho 0 a = G a.
Hypothesis ho_S : forall m a, ho (S m) a = iter (a + 1) (ho m) r.
Variable hoc : nat -> nat -> nat -> nat.
Hypothesis hoc_0 : forall m a, hoc m 0 a = a.
Hypothesis hoc_S : forall m n a, hoc m (S n) a = hoc (S m) n (ho m a).

Lemma ho_ub : forall m a, ho m a + 20 <= f_wk m (a + 20).
Proof.
  induction m as [| m IH]; intros a.
  - rewrite ho_0, f_wk_0. apply G_ub.
  - rewrite ho_S, f_wk_S.
    pose proof (iter_shift (ho m) (f_wk m) 20 (f_wk_mono m) IH (a + 1) r) as H1.
    assert (Hr : r + 20 <= iter 19 (f_wk m) (a + 20)).
    { pose proof (iter_gt1 (f_wk m) (f_wk_gt m) 19 (a + 20) ltac:(lia)). lia. }
    pose proof (iter_mono_x (f_wk m) (f_wk_mono m) (a + 1) (r + 20) _ Hr) as H2.
    rewrite <- iter_add in H2. replace (a + 1 + 19) with (a + 20) in H2 by lia. lia.
Qed.

Lemma hoc_ub_iter : forall n m a, hoc m n a + 20 <= iter n (f_wk (m + n)) (a + 20).
Proof.
  induction n as [| n IH]; intros m a.
  - rewrite hoc_0. simpl. lia.
  - rewrite hoc_S. specialize (IH (S m) (ho m a)). replace (S m + n) with (m + S n) in IH by lia.
    pose proof (ho_ub m a) as Hh.
    pose proof (f_wk_level_le m (m + S n) (a + 20) ltac:(lia) ltac:(lia)) as Hl.
    pose proof (iter_mono_x (f_wk (m + S n)) (f_wk_mono (m + S n)) n (ho m a + 20) (f_wk (m + S n) (a + 20)) ltac:(lia)) as H2.
    rewrite <- iter_S' in H2. lia.
Qed.

Lemma hoc_ub : forall n m a, hoc m n a + 20 <= f_wk (S (m + n)) (n + a + 20).
Proof.
  intros n m a. pose proof (hoc_ub_iter n m a) as H1.
  pose proof (iter_wk_le (m + n) n (a + 20) (n + a + 20) ltac:(lia) ltac:(lia)). lia.
Qed.

(** iter p (ho m) a, as one more f_(omega+m+1) step *)
Lemma iter_ho_ub : forall p m a, iter p (ho m) a + 20 <= f_wk (S m) (p + a + 20).
Proof.
  intros p m a.
  pose proof (iter_shift (ho m) (f_wk m) 20 (f_wk_mono m) (ho_ub m) p a) as H1.
  pose proof (iter_wk_le m p (a + 20) (p + a + 20) ltac:(lia) ltac:(lia)). lia.
Qed.
(** the same bounds with the level and the argument of the right-hand side chosen freely (larger) *)
Lemma ho_ub_le : forall m a K z, m <= K -> a + 20 <= z -> ho m a + 20 <= f_wk K z.
Proof.
  intros m a K z HK Hz. pose proof (ho_ub m a). pose proof (f_wk_mono m (a + 20) z Hz).
  pose proof (f_wk_level_le m K z HK ltac:(lia)). lia.
Qed.

Lemma hoc_ub_le : forall n m a K z, S (m + n) <= K -> n + a + 20 <= z -> hoc m n a + 20 <= f_wk K z.
Proof.
  intros n m a K z HK Hz. pose proof (hoc_ub n m a). pose proof (f_wk_mono (S (m + n)) (n + a + 20) z Hz).
  pose proof (f_wk_level_le (S (m + n)) K z HK ltac:(lia)). lia.
Qed.

Lemma iter_ho_ub_le : forall p m a K z, S m <= K -> p + a + 20 <= z -> iter p (ho m) a + 20 <= f_wk K z.
Proof.
  intros p m a K z HK Hz. pose proof (iter_ho_ub p m a). pose proof (f_wk_mono (S m) (p + a + 20) z Hz).
  pose proof (f_wk_level_le (S m) K z HK ltac:(lia)). lia.
Qed.
End Outer.
