(** * Transfer.v : the 8-state machine M8 halts from the blank tape, with the score of the 9-state record C04.

    M8  = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---   (Tm8.tm8, a busycoq machine over the 8-state BB82)
    C04 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF

    Everything about C04 is imported read-only from bb9_c04_coq (dev/Final.v c04_halts, fgh/EndU.v, fgh/Exact.v,
    dev/ScoreEnd.v); Sim.v proves that C04 simulates M8 (one C04 step per M8 step, three for M8's F0) with the same tape,
    and transfers halting and the ones counts.  Statements here use the native 8-state busycoq notions (Individual82:
    halts, c0, -[ ]->*, halted) and [ones] = Tm8.ones (verbatim copy of BB8_champ35_bound.ones).
    Dependencies: only M8 (BB82, Individual82, Tm8, Sim) and modules of the C04 tree BB9/verify_c04 (lib = BB8, Dev, Score,
    Fgh); nothing else from bb8_list/proofs.  [Abs.arrow] is the same Fixpoint as the repo's BB8_champ35_bound.arrow.

    M8 halts reading 1 in state H (H1 undefined), so the standard score (the halting transition writes 1) equals ones.

    Main theorems:
      m8_halts         : halts tm8 c0
      m8_fgh_bracket   : f_w(f_w(12 Bx + 26)) < N < f_w(f_w(12 Bx + 27))  for every halting count N   (2 Bx + 4 = 2 ^13 3)
      m8_fgh_coarse    : f_(w+1)(3) < N < f_(w+1)(4)
      m8_score_exact   : N = sigma_c04 ;  m8_score_reached : the halting tape has exactly sigma_c04 ones
      m8_beats_bb8     : 12 * (2 ^37 3) + 59 < N   (the exact score of the current BB(8) entry, BB8_champ35_exact)
      m8_beats_fw2     : as C04's c04_beats_fw2 (beats the 9-state fw2 machine's count + 1) *)
From M8 Require Import Individual82.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From BB8 Require Individual92 BB9_fw2_1RB0RD BB9_fw2_bound.
From Dev Require Base Abs ScoreEnd.
From K31 Require K31_Abs.
From Score Require Score.
From Fgh Require FArith EndU Exact.
From M8 Require Import Tm8.
From M8 Require Sim.

Module T9 := Individual92.Individual92.Permute.Flip.Compute.TM.

Local Open Scope nat_scope.

Opaque Abs.U Abs.arrow Abs.Bx Score.f Score.f_omega.

(** ** Arithmetic: 12 * (2 ^37 3) + 59 < f_w(f_w(12 Bx + 26)) *)
Lemma f_twice : forall k n, 2 <= n -> Score.f k (Score.f k n) <= Score.f (S k) n.
Proof.
  intros k [| [| n]] Hn; [lia | lia |]. rewrite Score.f_S.
  change (Abs.iter (S (S n)) (Score.f k) (S (S n))) with (Score.f k (Score.f k (Abs.iter n (Score.f k) (S (S n))))).
  apply FArith.f_mono, FArith.f_mono. apply FArith.iter_ge_id, FArith.f_ge.
Qed.

Lemma fomega3_ge : 48 <= Score.f_omega 3.
Proof.
  rewrite FArith.fomega_eq. pose proof (f_twice 2 3 ltac:(lia)) as H.
  rewrite (FArith.f2_eq 3) in H. change (2 ^ 3 * 3) with 24 in H.
  pose proof (FArith.f_lvl 1 24 ltac:(lia)) as H2. rewrite (FArith.f1_eq 24) in H2. lia.
Qed.

Lemma bb8_lt : 12 * Abs.arrow 37 2 3 + 59 < Score.f_omega (Score.f_omega (12 * Abs.Bx + 26)).
Proof.
  pose proof FArith.fomega3_le_Bx as HB. pose proof fomega3_ge as H48.
  pose proof (FArith.arrow_le_f 37 3 ltac:(lia)) as H2.
  pose proof (FArith.f_le_fomega 38 3 ltac:(lia)) as H3. change (38 + 3) with 41 in H3.
  pose proof (FArith.fomega_ge 41) as H41.
  pose proof (FArith.fomega_mono 41 (12 * Abs.Bx + 26) ltac:(lia) ltac:(lia)) as H1.
  rewrite (FArith.fomega_eq (Score.f_omega (12 * Abs.Bx + 26))).
  set (Y := Score.f_omega (12 * Abs.Bx + 26)) in *. set (Z := Score.f_omega 41) in *.
  pose proof (FArith.f_mono2 2 Y Z Y ltac:(lia) ltac:(lia) H1) as H4.
  rewrite (FArith.f2_eq Z) in H4.
  assert (HP : 2 ^ 6 <= 2 ^ Z) by (apply Nat.pow_le_mono_r; lia).
  change (2 ^ 6) with 64 in HP.
  set (A := Abs.arrow 37 2 3) in *. set (F := Score.f 38 3) in *. set (W := Score.f Y Y) in *.
  set (P := 2 ^ Z) in *. clearbody A F W P Y Z.
  nia.
Qed.

(** ** Main theorems *)
Theorem m8_halts : halts tm8 c0.
Proof. exact Sim.m8_halts_sim. Qed.

Theorem m8_fgh_bracket : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N ->
  Score.f_omega (Score.f_omega (12 * Abs.Bx + 26)) < N /\ N < Score.f_omega (Score.f_omega (12 * Abs.Bx + 27)).
Proof.
  intros c N H1 H2 H3. destruct (Sim.m8_to_c04 c N H1 H2 H3) as [c9 [G1 [G2 G3]]].
  exact (EndU.c04_fgh_bracket c9 N G1 G2 G3).
Qed.

Theorem m8_fgh_coarse : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N -> FArith.f_w1 3 < N /\ N < FArith.f_w1 4.
Proof.
  intros c N H1 H2 H3. destruct (Sim.m8_to_c04 c N H1 H2 H3) as [c9 [G1 [G2 G3]]].
  exact (EndU.c04_fgh_coarse c9 N G1 G2 G3).
Qed.

Theorem m8_score_exact : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N -> N = Exact.sigma_c04.
Proof.
  intros c N H1 H2 H3. destruct (Sim.m8_to_c04 c N H1 H2 H3) as [c9 [G1 [G2 G3]]].
  exact (Exact.c04_score_exact c9 N G1 G2 G3).
Qed.

Theorem m8_score_reached : exists c, c0 -[ tm8 ]->* c /\ halted tm8 c /\ ones c Exact.sigma_c04.
Proof.
  destruct Exact.c04_score_reached as [c9 [G1 [G2 G3]]].
  exact (Sim.c04_to_m8 c9 _ G1 G2 G3).
Qed.

Theorem m8_sigma_bracket :
  Score.f_omega (Score.f_omega (12 * Abs.Bx + 26)) < Exact.sigma_c04 /\
  Exact.sigma_c04 < Score.f_omega (Score.f_omega (12 * Abs.Bx + 27)).
Proof. exact Exact.c04_sigma_bracket. Qed.

Theorem m8_beats_bb8 : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N ->
  12 * Abs.arrow 37 2 3 + 59 < N.
Proof.
  intros c N H1 H2 H3. destruct (m8_fgh_bracket c N H1 H2 H3) as [HL _].
  pose proof bb8_lt as H.
  set (A := Abs.arrow 37 2 3) in *. set (Y := Score.f_omega (Score.f_omega (12 * Abs.Bx + 26))) in *.
  clearbody A Y. lia.
Qed.

Theorem m8_beats_fw2 : exists c N, c0 -[ tm8 ]->* c /\ halted tm8 c /\ ones c N /\
  BB9_fw2_bound.f_omega (BB9_fw2_bound.f_omega (465 * 1000 + 9)) < N /\
  exists cf Nf, T9.evstep BB9_fw2_1RB0RD.tm T9.c0 cf /\ T9.halted BB9_fw2_1RB0RD.tm cf /\
    BB9_fw2_bound.ones cf Nf /\ Nf + 1 < N.
Proof.
  destruct ScoreEnd.c04_beats_fw2 as [c9 [N [G1 [G2 [G3 [G4 G5]]]]]].
  destruct (Sim.c04_to_m8 c9 N G1 G2 G3) as [c [H1 [H2 H3]]].
  exists c, N. split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact G4 | exact G5]]]].
Qed.

(** ** The two transfer theorems, restated in native 8-state notation (= Sim.m8_to_c04 / Sim.c04_to_m8) *)
Theorem m8_score_to_c04 : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N ->
  exists c9, T9.evstep Base.tm T9.c0 c9 /\ T9.halted Base.tm c9 /\ K31_Abs.ones c9 N.
Proof. exact Sim.m8_to_c04. Qed.

Theorem m8_score_from_c04 : forall c9 N, T9.evstep Base.tm T9.c0 c9 -> T9.halted Base.tm c9 -> K31_Abs.ones c9 N ->
  exists c, c0 -[ tm8 ]->* c /\ halted tm8 c /\ ones c N.
Proof. exact Sim.c04_to_m8. Qed.