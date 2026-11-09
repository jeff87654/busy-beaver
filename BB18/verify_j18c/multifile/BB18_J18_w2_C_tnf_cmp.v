(** Comparisons of J18_w2_C (BB18_J18_w2_C_tnf.v) with the entries it supersedes:
    - R18a   (BB(18), BB18_R18a.v):   sigma_lower_bound  f_w2 (f_omega (f_omega (f 10 2))) < N
    - J16_w2 (BB(16), BB16_J16_w2.v): sigma_lower_bound  f_w2 (f 15 2) < N
    Those files define iter, f, f_omega, f_wk and f_w2 with the same text as BB18_J18_w2_C_tnf.v.
    J18_w2_C's halting tape holds more ones than each of these bounds. *)

From BB8 Require Import Individual182.
From BB8 Require Import BB18_J18_w2_C_tnf.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
(* the main file may make the hierarchy opaque at its end; the generic facts below unfold it (abstract arguments only) *)
Transparent f f_omega f_wk f_w2.

(** Generic facts about the file's own [iter], [f], [f_omega], [f_wk] (standard definitions), proved here from
    the definitions only, so that the comparisons below do not depend on the main proof's lemma names. *)

Lemma cmp_iter_add : forall {X : Type} a b (g : X -> X) x, iter (a + b) g x = iter a g (iter b g x).
Proof. intros X a. induction a as [|a IH]; intros b g x; simpl; [reflexivity | now rewrite IH]. Qed.

Lemma cmp_iter_ge : forall g, (forall a, a <= g a) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg n. induction n as [|n IH]; intros x; simpl; [lia |].
  specialize (IH x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma cmp_iter_mono_x : forall g, (forall a b, a <= b -> g a <= g b) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg n. induction n as [|n IH]; intros x y Hxy; simpl; auto. Qed.

Lemma cmp_iter_mono_n : forall g, (forall a, a <= g a) ->
  forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite cmp_iter_add. apply cmp_iter_ge. exact Hg.
Qed.

Definition cmp_ok (g : nat -> nat) := (forall n, n <= g n) /\ (forall a b, a <= b -> g a <= g b).

Lemma cmp_diag_ok : forall g, cmp_ok g -> cmp_ok (fun n => iter n g n).
Proof.
  intros g [Hid Hmono]. split.
  - intros n. apply cmp_iter_ge. exact Hid.
  - intros a b Hab. eapply Nat.le_trans.
    + apply cmp_iter_mono_x; [exact Hmono | exact Hab].
    + apply cmp_iter_mono_n; [exact Hid | exact Hab].
Qed.

Lemma cmp_diag_step : forall g, cmp_ok g -> forall n, 1 <= n -> g n <= iter n g n.
Proof.
  intros g [Hid Hmono] n Hn. destruct n as [|n]; [lia |]. simpl.
  apply Hmono. apply cmp_iter_ge. exact Hid.
Qed.

(** [iter m g x] with m <= x is at most the next level at x. *)
Lemma cmp_absorb : forall g, cmp_ok g -> forall m x, m <= x -> iter m g x <= iter x g x.
Proof. intros g [Hid _] m x Hm. apply cmp_iter_mono_n; [exact Hid | exact Hm]. Qed.

Lemma cmp_f_ok : forall k, cmp_ok (f k).
Proof.
  induction k as [|k IH].
  - unfold cmp_ok. change (f 0) with S. split; intros; lia.
  - change (cmp_ok (fun n => iter n (f k) n)). apply cmp_diag_ok. exact IH.
Qed.

Lemma cmp_f_level : forall k n, 1 <= n -> f k n <= f (S k) n.
Proof.
  intros k n Hn. change (f (S k) n) with (iter n (f k) n).
  apply cmp_diag_step; [apply cmp_f_ok | exact Hn].
Qed.

Lemma cmp_f_level_mono : forall d k n, 1 <= n -> f k n <= f (d + k) n.
Proof.
  induction d as [|d IH]; intros k n Hn; [simpl; lia |].
  replace (S d + k) with (S (d + k)) by lia.
  eapply Nat.le_trans; [apply IH; exact Hn | apply cmp_f_level; exact Hn].
Qed.

Lemma cmp_iter_S : forall n x, iter n S x = n + x.
Proof. induction n as [|n IH]; intros x; simpl; [reflexivity | now rewrite IH]. Qed.

Lemma cmp_f_omega_ok : cmp_ok f_omega.
Proof.
  split.
  - intros n. unfold f_omega. apply (proj1 (cmp_f_ok n)).
  - intros a b Hab. unfold f_omega. destruct b as [|b].
    + assert (a = 0) by lia. subst. lia.
    + eapply Nat.le_trans; [apply (proj2 (cmp_f_ok a)); exact Hab |].
      pose proof (cmp_f_level_mono (S b - a) a (S b)) as Hl.
      replace (S b - a + a) with (S b) in Hl by lia. apply Hl. lia.
Qed.

Lemma cmp_f_omega_ge2 : forall n, 1 <= n -> 2 * n <= f_omega n.
Proof.
  intros n Hn. unfold f_omega.
  assert (H1 : f 1 n = 2 * n). { change (f 1 n) with (iter n S n). rewrite cmp_iter_S. lia. }
  pose proof (cmp_f_level_mono (n - 1) 1 n Hn) as Hl.
  replace (n - 1 + 1) with n in Hl by lia. lia.
Qed.

Lemma cmp_f_wk_ok : forall k, cmp_ok (f_wk k).
Proof.
  induction k as [|k IH].
  - exact cmp_f_omega_ok.
  - change (cmp_ok (fun n => iter n (f_wk k) n)). apply cmp_diag_ok. exact IH.
Qed.

Lemma cmp_f_wk_id : forall k n, n <= f_wk k n.
Proof. intros k. exact (proj1 (cmp_f_wk_ok k)). Qed.

Lemma cmp_f_wk_mono : forall k a b, a <= b -> f_wk k a <= f_wk k b.
Proof. intros k. exact (proj2 (cmp_f_wk_ok k)). Qed.

Lemma cmp_f_wk_level : forall k n, 1 <= n -> f_wk k n <= f_wk (S k) n.
Proof.
  intros k n Hn. change (f_wk (S k) n) with (iter n (f_wk k) n).
  apply cmp_diag_step; [apply cmp_f_wk_ok | exact Hn].
Qed.

Lemma cmp_f_wk_level_mono : forall d k n, 1 <= n -> f_wk k n <= f_wk (d + k) n.
Proof.
  induction d as [|d IH]; intros k n Hn; [simpl; lia |].
  replace (S d + k) with (S (d + k)) by lia.
  eapply Nat.le_trans; [apply IH; exact Hn | apply cmp_f_wk_level; exact Hn].
Qed.

Lemma cmp_f_wk_ge2 : forall k n, 1 <= n -> 2 * n <= f_wk k n.
Proof.
  intros k n Hn. eapply Nat.le_trans; [apply cmp_f_omega_ge2; exact Hn |].
  pose proof (cmp_f_wk_level_mono k 0 n Hn) as Hl. rewrite Nat.add_0_r in Hl. exact Hl.
Qed.

(** [iter m (f_wk k) x] with m <= x is at most f_(omega+k+1)(x). *)
Lemma cmp_wk_absorb : forall k m x, m <= x -> iter m (f_wk k) x <= f_wk (S k) x.
Proof. intros k m x Hm. change (f_wk (S k) x) with (iter x (f_wk k) x). apply cmp_absorb; [apply cmp_f_wk_ok | exact Hm]. Qed.

(** f_(omega+k)(x) <= f_(omega*2)(y) when k <= y and x <= y. *)
Lemma cmp_wk_le_w2 : forall k x y, k <= y -> x <= y -> 1 <= y -> f_wk k x <= f_wk y y.
Proof.
  intros k x y Hk Hx Hy. eapply Nat.le_trans; [apply cmp_f_wk_mono; exact Hx |].
  pose proof (cmp_f_wk_level_mono (y - k) k y Hy) as Hl. replace (y - k + k) with y in Hl by lia. exact Hl.
Qed.

Lemma cmp_wk_S_eq : forall k n, f_wk (S k) n = iter n (f_wk k) n.
Proof. reflexivity. Qed.

Lemma cmp_f_omega_eq : forall n, f_omega n = f n n.
Proof. reflexivity. Qed.

Lemma cmp_iter_S_r : forall {X : Type} n (g : X -> X) x, iter (S n) g x = iter n g (g x).
Proof. intros X n. induction n as [|n IH]; intros g x; [reflexivity |]. simpl. now rewrite <- IH. Qed.

Lemma cmp_iter_1 : forall {X : Type} (g : X -> X) x, iter 1 g x = g x.
Proof. reflexivity. Qed.

Lemma cmp_iter_2 : forall {X : Type} (g : X -> X) x, iter 2 g x = g (g x).
Proof. reflexivity. Qed.

Lemma cmp_iter_3 : forall {X : Type} (g : X -> X) x, iter 3 g x = g (g (g x)).
Proof. reflexivity. Qed.

Lemma cmp_iter_4 : forall {X : Type} (g : X -> X) x, iter 4 g x = g (g (g (g x))).
Proof. reflexivity. Qed.

Lemma cmp_iter_ext : forall (g h : nat -> nat), (forall y, g y = h y) -> forall n x, iter n g x = iter n h x.
Proof. intros g h E n. induction n as [|n IH]; intros x; simpl; [reflexivity | now rewrite IH, E]. Qed.

Lemma cmp_wk_twice : forall k x, 2 <= x -> f_wk k (f_wk k x) <= f_wk (S k) x.
Proof. intros k x Hx. rewrite <- (cmp_iter_2 (f_wk k) x). apply cmp_wk_absorb. exact Hx. Qed.

Lemma cmp_wk_four : forall k x, 4 <= x -> f_wk k (f_wk k (f_wk k (f_wk k x))) <= f_wk (S k) x.
Proof. intros k x Hx. rewrite <- (cmp_iter_4 (f_wk k) x). apply cmp_wk_absorb. exact Hx. Qed.

(** iter n (f_(omega+k)) (f_(omega+k)(x)) <= f_(omega+k+1)(y) when n + 1 <= y and x <= y. *)
Lemma cmp_wk_shift_absorb : forall k n x y, S n <= y -> x <= y ->
  iter n (f_wk k) (f_wk k x) <= f_wk (S k) y.
Proof.
  intros k n x y Hn Hx. rewrite <- cmp_iter_S_r.
  apply Nat.le_trans with (iter (S n) (f_wk k) y); [apply cmp_iter_mono_x; [apply cmp_f_wk_mono | exact Hx] |].
  apply cmp_wk_absorb. exact Hn.
Qed.

Lemma cmp_f_w2_eq : forall n, f_w2 n = f_wk n n.
Proof. reflexivity. Qed.

Lemma cmp_f_w2_mono : forall a b, a <= b -> f_w2 a <= f_w2 b.
Proof.
  intros a b Hab. rewrite !cmp_f_w2_eq. destruct b as [|b]; [assert (a = 0) by lia; subst; lia |].
  apply cmp_wk_le_w2; lia.
Qed.

Opaque f f_omega f_wk f_w2.

Lemma f_le_fw35 : forall k, k <= 35 -> f k 2 <= f_omega 35.
Proof.
  intros k Hk. rewrite cmp_f_omega_eq.
  apply Nat.le_trans with (f 35 2).
  - pose proof (cmp_f_level_mono (35 - k) k 2 ltac:(lia)) as Hl. replace (35 - k + k) with 35 in Hl by lia. exact Hl.
  - apply (proj2 (cmp_f_ok 35)). lia.
Qed.

Lemma iter19 : f_omega 35 <= iter 9 f_omega 35.
Proof.
  pose proof (cmp_iter_mono_n f_omega (proj1 cmp_f_omega_ok) 1 9 35 ltac:(lia)) as Hi.
  rewrite cmp_iter_1 in Hi. exact Hi.
Qed.

Lemma R18a_arg_le : f_omega (f_omega (f 10 2)) <= 2 * iter 9 f_omega 35.
Proof.
  pose proof (f_le_fw35 10 ltac:(lia)) as H10.
  apply Nat.le_trans with (f_omega (f_omega (f_omega 35))).
  { apply (proj2 cmp_f_omega_ok). apply (proj2 cmp_f_omega_ok). exact H10. }
  rewrite <- (cmp_iter_3 f_omega 35).
  pose proof (cmp_iter_mono_n f_omega (proj1 cmp_f_omega_ok) 3 9 35 ltac:(lia)). lia.
Qed.

Lemma J16_arg_le : f 15 2 <= 2 * iter 9 f_omega 35.
Proof. pose proof (f_le_fw35 15 ltac:(lia)). pose proof iter19. lia. Qed.

Theorem beats_R18a :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_w2 (f_omega (f_omega (f 10 2))) < N.
Proof.
  destruct sigma_lower_bound as (c & N & H1 & H2 & H3 & H4 & H5).
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof (cmp_f_w2_mono _ _ R18a_arg_le). lia.
Qed.

Theorem beats_J16 :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_w2 (f 15 2) < N.
Proof.
  destruct sigma_lower_bound as (c & N & H1 & H2 & H3 & H4 & H5).
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof (cmp_f_w2_mono _ _ J16_arg_le). lia.
Qed.
