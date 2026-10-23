(** * HGoal.v : X3 halts from the blank tape with N ones, f_omega^6 (12 Bx + 26) < N, f_omega^7 12 < N and
    f_omega^2 (12 Bx + 27) < N (BB9/verify_h003).
    HScore.x_goal gives N > f_omega (f_omega a) for every a <= K4 - 1 (the depth of the exit top's clear).  The four
    rebuilding tops add four levels: Ra_i = iter 2 (U (K_i - 1)) 0 is the clear of Top(K_i), and K_(i+1) - 1 >= Ra_i
    (K1 = 12 Rd0 + .., Rd0 >= 2 Ra0 + 1; K2 = 12 Rc1 + .., Rc1 >= 2 Ra1; K3 = 12 Ra2 + ..; K4 = 12 Ra3 + ..), so
    x <= K_i - 1 gives f_omega x + 2 <= Ra_i <= K_(i+1) - 1 (HScore.fw_lt_iter2).  K0 - 1 = 12 Bx + 26. *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XScore Require Import Score.
From XL Require Import Individual112.   (* again: S1 is the symbol *)
From XDev Require Import Base Abs.
From XDev Require HTop HScore Ones.
From XK31 Require K31_Abs.
Opaque U arrow.
Local Open Scope nat_scope.

(** ** f_omega 12 <= Bx (../verify_c7/dev/C7Score5.v) *)
Transparent f f_omega.

Lemma iter_S_add : forall n x, iter n S x = n + x.
Proof. induction n; intros x; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma dbl_iter : forall a b, dbl a b = iter a (fun z => 2 * z + 2) b.
Proof.
  induction a as [| a IH]; intros b; [reflexivity |].
  rewrite iter_S'. cbn [dbl]. apply IH.
Qed.

Lemma fSS_le_U : forall k x, f (S (S k)) x <= U k x.
Proof.
  induction k as [| k IH]; intros n.
  - rewrite f_S, U_0, dbl_iter. set (g := fun z => 2 * z + 2).
    assert (Hg : forall a, a + 1 <= g a) by (intro a; unfold g; lia).
    assert (Hm : forall a b, a <= b -> g a <= g b) by (intros a b H; unfold g; lia).
    assert (H1 : iter n (f 1) n <= iter n g n).
    { apply sc_iter_dom; [| exact Hm]. intro a. rewrite f_S. change (f 0) with S. rewrite iter_S_add. unfold g. lia. }
    assert (H2 : n <= iter (n + 2) g 0) by (pose proof (sc_iter_count g Hg (n + 2) 0); lia).
    assert (H3 : iter n g n <= iter n g (iter (n + 2) g 0)) by (apply sc_iter_mono_x; [exact Hm | exact H2]).
    rewrite <- sc_iter_add in H3. replace (n + (n + 2)) with (2 * n + 2) in H3 by lia. lia.
  - rewrite f_S, U_S.
    assert (Hg : forall a, a + 1 <= U k a) by (intro a; pose proof (sc_U_lin k a); lia).
    assert (H1 : iter n (f (S (S k))) n <= iter n (U k) n) by (apply sc_iter_dom; [exact IH | exact (sc_U_mono k)]).
    assert (H2 : n <= iter (n + 2) (U k) 0) by (pose proof (sc_iter_count (U k) Hg (n + 2) 0); lia).
    assert (H3 : iter n (U k) n <= iter n (U k) (iter (n + 2) (U k) 0))
      by (apply sc_iter_mono_x; [exact (sc_U_mono k) | exact H2]).
    rewrite <- sc_iter_add in H3. replace (n + (n + 2)) with (2 * n + 2) in H3 by lia. lia.
Qed.

Lemma fw12_le_Bx : f_omega 12 <= Bx.
Proof.
  change (f_omega 12) with (f 12 12). pose proof (fSS_le_U 10 12) as H1.
  pose proof (sc_U0_ge 10) as H2. pose proof (sc_U_mono 10 12 (U 10 0) ltac:(lia)) as H3.
  rewrite Bx_def. lia.
Qed.

Opaque f f_omega.

(** ** The top chain *)
Lemma iter_ge_n : forall n j x, n <= iter n (U j) x.
Proof.
  intros n j x. assert (Hg : forall a, a + 1 <= U j a) by (intro a; pose proof (sc_U_lin j a); lia).
  pose proof (sc_iter_count (U j) Hg n x). lia.
Qed.

Lemma Ra_ge : forall K, K + 1 <= iter 2 (U (K - 1)) 0.
Proof.
  intro K. cbn [iter]. pose proof (sc_U0_ge (K - 1)). pose proof (sc_U_lin (K - 1) (U (K - 1) 0)). lia.
Qed.

Lemma chain_facts : HTop.Ra0 <= HTop.K1 - 1 /\ HTop.Ra1 <= HTop.K2 - 1 /\ HTop.Ra2 <= HTop.K3 - 1 /\ HTop.Ra3 <= HTop.K4 - 1.
Proof.
  split; [| split; [| split]].
  - unfold HTop.K1, HTop.Rd0, HTop.Rd4. pose proof (iter_ge_n (2 * HTop.Ra0 + 1) (3 * HTop.k0 + 2) (HTop.Rc4 HTop.k0)). lia.
  - unfold HTop.K2, HTop.Rc1, HTop.Rc3. pose proof (iter_ge_n (2 * HTop.Ra1) (3 * HTop.k1 + 5) (HTop.Rb3 HTop.k1)). lia.
  - unfold HTop.K3; lia.
  - unfold HTop.K4; lia.
Qed.

Lemma chain4 : forall a, a <= 12 * Bx + 26 -> f_omega (f_omega (f_omega (f_omega a))) <= HTop.K4 - 1.
Proof.
  intros a Ha. destruct chain_facts as [B1 [B2 [B3 B4]]].
  assert (L0 : HTop.K0 - 1 = 12 * Bx + 26) by (unfold HTop.K0; lia).
  assert (A1 : f_omega a + 2 <= HTop.Ra0) by (apply HScore.fw_lt_iter2; lia).
  assert (A2 : f_omega (f_omega a) + 2 <= HTop.Ra1) by (apply HScore.fw_lt_iter2; lia).
  assert (A3 : f_omega (f_omega (f_omega a)) + 2 <= HTop.Ra2) by (apply HScore.fw_lt_iter2; lia).
  assert (A4 : f_omega (f_omega (f_omega (f_omega a))) + 2 <= HTop.Ra3) by (apply HScore.fw_lt_iter2; lia).
  lia.
Qed.

Lemma K4_ge : 12 * Bx + 27 <= HTop.K4 - 1.
Proof.
  destruct chain_facts as [B1 [B2 [B3 B4]]].
  pose proof (Ra_ge HTop.K0). pose proof (Ra_ge HTop.K1). pose proof (Ra_ge HTop.K2). pose proof (Ra_ge HTop.K3).
  fold HTop.Ra0 HTop.Ra1 HTop.Ra2 HTop.Ra3 in *. unfold HTop.K0 in *. lia.
Qed.

Lemma count1_same : forall L, K31_Abs.count1 L = Ones.count1 L.
Proof. induction L as [| x L IH]; [reflexivity | cbn; rewrite IH; destruct x; reflexivity]. Qed.

Lemma ones_same : forall c N, K31_Abs.ones c N -> Ones.ones c N.
Proof.
  intros c N [q [L [R [s [E F]]]]]. exists q, L, R, s. split; [exact E |].
  rewrite F, !count1_same. destruct s; reflexivity.
Qed.

Theorem x_goal6 : exists cx N, c0 -->* cx /\ halted tm cx /\ Ones.ones cx N /\
  f_omega (f_omega (f_omega (f_omega (f_omega (f_omega (12 * Bx + 26)))))) < N /\
  f_omega (f_omega (f_omega (f_omega (f_omega (f_omega (f_omega 12)))))) < N /\
  f_omega (f_omega (12 * Bx + 27)) < N.
Proof.
  destruct HScore.x_goal as [c [N [H1 [H2 [H3 HB]]]]].
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact (ones_same c N H3) |].
  pose proof fw12_le_Bx. pose proof (chain4 (12 * Bx + 26) ltac:(lia)) as C1.
  pose proof (chain4 (f_omega 12) ltac:(lia)) as C2.
  split; [exact (HB _ C1) |]. split; [exact (HB _ C2) |].
  apply HB. exact K4_ge.
Qed.

Print Assumptions x_goal6.
