(** * Racheline's 21-state BB(21) champion B21 halts from the blank tape.

    B21 = 0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR

    The machine is Racheline's (bbchallenge wiki BB(21) champion, 2024); the proof is ours (bb8 project, 2026).

    Structure (files):
      BB21_B21_tm.v      TM macro lemmas: level-1 engine (E0/E1/exit), the J-level sweep gadgets, refill, boot.
      BB21_B21_absdef.v  the abstract block machine [astep] (transcription of the measured block rules).
      BB21_B21_sim.v     [astep] is simulated by the TM; [halts_from].
      BB21_B21_grow.v    growth and residues of the engine level maps h (h_mod64: index >= 2 gives 17 mod 64).
      BB21_B21_steps.v   [astep] on states  b0 | E's | frontier | blocks above.
      BB21_B21_inv.v     the dominance invariant (Lemma D) and its preservation by every transition.
      BB21_B21_proc.v    processing of one frontier block (nested induction, reverse-lexicographic order).
      BB21_B21_phase.v   phases: P walks through the 2s; refills.
      BB21_B21_run.v     (B21-specific refill rule refill21) phases 4, 5, 6: the final sweep of phase 6 has J-acc = 2 mod 4: the refill halts.
*)

From BB8 Require Import Individual212.
From BB8 Require BB21_B21_tm BB21_B21_sim BB21_B21_run BB21_B21_score.
Set Default Goal Selector "!".

(* machine: 0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (0, TM.L, I)       | A, 1 => Some (0, TM.L, F)
  | B, 0 => Some (0, TM.R, J)       | B, 1 => Some (1, TM.R, G)
  | C, 0 => Some (0, TM.R, D)       | C, 1 => Some (1, TM.L, C)
  | D, 0 => Some (1, TM.R, H)       | D, 1 => Some (1, TM.R, E)
  | E, 0 => Some (1, TM.L, O)       | E, 1 => Some (0, TM.R, H)
  | F, 0 => Some (1, TM.L, A)       | F, 1 => Some (1, TM.L, F)
  | G, 0 => Some (0, TM.L, C)       | G, 1 => Some (1, TM.L, A)
  | H, 0 => Some (1, TM.R, B)       | H, 1 => Some (1, TM.R, H)
  | I, 0 => Some (1, TM.R, D)       | I, 1 => Some (0, TM.L, F)
  | J, 0 => Some (1, TM.L, P)       | J, 1 => Some (0, TM.R, K)
  | K, 0 => Some (0, TM.L, M)       | K, 1 => Some (1, TM.L, L)
  | L, 0 => Some (0, TM.L, L)       | L, 1 => Some (1, TM.L, M)
  | M, 0 => Some (1, TM.L, E)       | M, 1 => Some (1, TM.L, N)
  | N, 0 => Some (0, TM.R, QQ)      | N, 1 => Some (0, TM.L, M)
  | O, 0 => Some (0, TM.R, P)       | O, 1 => Some (1, TM.L, O)
  | P, 0 => Some (1, TM.L, RR)      | P, 1 => Some (0, TM.R, H)
  | QQ, 0 => Some (1, TM.L, F)      | QQ, 1 => Some (1, TM.R, QQ)
  | RR, 0 => None                   | RR, 1 => Some (0, TM.L, SS)
  | SS, 0 => Some (1, TM.L, H)      | SS, 1 => Some (0, TM.L, TT)
  | TT, 0 => Some (1, TM.L, H)      | TT, 1 => Some (1, TM.L, UU)
  | UU, 0 => Some (0, TM.L, E)      | UU, 1 => Some (1, TM.L, RR)
  end.

Lemma star_conv : forall a b, BB21_B21_proc.star BB21_B21_absdef.refill21 a b -> BB21_B21_sim.star a b.
Proof.
  intros a b H. induction H.
  - apply BB21_B21_sim.star_refl.
  - eapply BB21_B21_sim.star_step; [rewrite BB21_B21_absdef.astep_G; exact H | exact IHstar].
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct BB21_B21_run.abstract_halt as [bs [Hs Hh]].
  rewrite <- BB21_B21_absdef.astep_G in Hh.
  exact (BB21_B21_sim.halts_from bs (star_conv _ _ Hs) Hh).
Qed.

(** ** Score (stage 1).  [onesN c N]: the halting tape holds exactly N ones; the halting transition R0 = 1RZ
    writes one more, so sigma(B21) = N + 1.  [tet n] = 4^^n (tet 0 = 1, tet (S n) = 4 ^ tet n). *)
Theorem sigma_lower_bound :
  exists c N, c0 -[ tm ]->* c /\ halted tm c /\ BB21_B21_score.onesN c N /\ BB21_B21_score.tet 341 < N.
Proof. exact BB21_B21_score.sigma_lower_bound_tet. Qed.
