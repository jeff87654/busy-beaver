(** * HFinal.v : the auxiliary machine X3 halts from the blank tape (BB9/verify_h003).
    HTop.reach_D0_top (X3's own top: five rebuilding tops and the exit) gives the cascade start reachF PmH L1H;
    from there C04's cascade and endgame (../verify_f3's Endgame.halts_from_reach, generalized over the parked-count margin
    Pm) and C04's key-31 endgame (K31_End.k31_end) apply, replayed on X3 with raw steps. *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base Abs Lift Step Fin Endgame.
From XDev Require HTop.
From XK31 Require Import K31_End.
Opaque U arrow.

Local Open Scope nat_scope.

Definition L1H : nat := 18 * HTop.hx + 13.
Definition PmH : nat := 12 * HTop.Ra4 + 17 - L1H.

Lemma Ra4_ge : 20 * HTop.hx + 34 <= HTop.Ra4.
Proof.
  destruct HTop.orbit_vals as [_ [_ [_ [_ [E4 _]]]]].
  unfold HTop.Ra4. cbn [iter]. pose proof (U0_ge (HTop.K4 - 1)). pose proof (U_lin (HTop.K4 - 1) (U (HTop.K4 - 1) O)).
  lia.
Qed.

Lemma hx_ge : 1000 <= HTop.hx.
Proof. destruct HTop.orbit_vals as [_ [_ [_ [_ [_ [_ [_ [_ [_ Hh]]]]]]]]]. exact Hh. Qed.

Lemma L1H_props : 60 <= L1H /\ L1H mod 2 = 1 /\ L1H mod 3 = 1.
Proof.
  destruct HTop.orbit_vals as [_ [_ [_ [_ [_ [_ [_ [_ [_ Hh]]]]]]]]].
  unfold L1H. split; [lia |]. split.
  - apply (mod_of _ 2 (9 * HTop.hx + 6)); lia.
  - apply (mod_of _ 3 (6 * HTop.hx + 4)); lia.
Qed.

Lemma PmH_ge : 100 <= PmH.
Proof. pose proof Ra4_ge. unfold PmH, L1H. lia. Qed.

Theorem reach_topH : reachF PmH L1H.
Proof.
  pose proof Ra4_ge.
  exists 19, (12 * HTop.Ra4 + 17), 0, (6 * HTop.hx + 10), (const S0).
  split; [| split; [lia | split; [unfold PmH, L1H; lia | exists (@nil Sym); reflexivity]]].
  unfold L1H. replace (S (18 * HTop.hx + 13)) with (18 * HTop.hx + 14) by lia. exact HTop.reach_D0_top.
Qed.

Theorem x_halts : halts tm c0.
Proof.
  destruct L1H_props as [H60 [H2 H3]].
  eapply (halts_from_reach PmH PmH_ge); [| exact H60 | exact H2 | exact H3 | exact (reachF_P _ _ reach_topH)].
  intros t P s y l HP.
  destruct (k31_end t P s y l HP) as [c [Rl [H1 [H4 _]]]].
  exists c. split; assumption.
Qed.

Print Assumptions x_halts.
