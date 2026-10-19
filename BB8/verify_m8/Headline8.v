(** * Headline8.v : the 8-state M8's score in FGH terms only (compile with fgh/coqc_h8.py = coq_m8's load path).
      m8_fgh3 : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N ->
                f_omega (f_omega (f_omega 12)) < N < f_omega (f_omega (f_omega 13)).
    From Transfer.m8_fgh_bracket (coq_m8, read-only) and Headline.Bx_fw. *)
From M8 Require Import Individual82.
From Coq Require Import Lia PeanoNat.
Set Default Goal Selector "!".
From Dev Require Abs.
From Score Require Score.
From Fgh Require FArith Headline.
From M8 Require Import Tm8.
From M8 Require Transfer.
Local Open Scope nat_scope.
Opaque Abs.U Abs.arrow Abs.Bx Score.f Score.f_omega.

Theorem m8_fgh3 : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N ->
  Score.f_omega (Score.f_omega (Score.f_omega 12)) < N /\ N < Score.f_omega (Score.f_omega (Score.f_omega 13)).
Proof.
  intros c N H1 H2 H3. destruct (Transfer.m8_fgh_bracket c N H1 H2 H3) as [HL HU].
  destruct Headline.Bx_fw as [B1 B2].
  pose proof (FArith.fomega_ge 12) as G0.
  pose proof (FArith.fomega_mono (Score.f_omega 12) (12 * Abs.Bx + 26) ltac:(lia) ltac:(lia)) as G1.
  pose proof (FArith.fomega_ge (Score.f_omega 12)) as G2.
  pose proof (FArith.fomega_mono (Score.f_omega (Score.f_omega 12)) (Score.f_omega (12 * Abs.Bx + 26)) ltac:(lia) G1) as G3.
  pose proof (FArith.fomega_mono (12 * Abs.Bx + 27) (Score.f_omega 13) ltac:(lia) B2) as G4.
  pose proof (FArith.fomega_ge (12 * Abs.Bx + 27)) as G5.
  pose proof (FArith.fomega_mono (Score.f_omega (12 * Abs.Bx + 27)) (Score.f_omega (Score.f_omega 13)) ltac:(lia) G4) as G6.
  split; lia.
Qed.
