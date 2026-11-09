(** * W2PR: a 25-state machine built on Racheline's B21 (wiki BB(21) champion) halts from the blank tape.

    W2PR = 0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR

    B21 (Racheline, 2024) with U1 = 1LV and a copy V,W,X,Y of the refill cycle R,S,T,U (V0 = 0LH): the refill
    tests the accumulator mod 8 instead of mod 4, so the machine passes refills #6 and #7 and halts at refill #8,
    after five big omega^2 phases (B21 halts after three).  The omega^2 machinery is Racheline's; the 25-state
    design is ours (bb8 project, w2p-build), and so is the proof.

    Files: BB25_W2PR_tm.v (TM macros, the period-8 refill gadgets), BB25_W2PR_sim.v (refill rule refillW, simulation),
    BB25_W2PR_run.v (phases 4..8, residues mod 256), BB25_W2PR_score.v (halting tape, bound); the engine, sweep and
    dominance-invariant layers are B21's parametric files BB21_B21_{absdef,grow,steps,inv,proc,phase}.v.

    [sigma_lower_bound]: N ones on the halting tape (sigma = N + 1) with
       iter 5 Fh (4^^341) < N,   Fh n = h n 0 = H_(n+2)(0), the level-(n+2) map of the engine
       (h 0 x = x+4, h (S m) x = h m iterated x+3 times from 1;  h n 0 >= 4 h (n-1) 0 + 13). *)

From BB8 Require Import Individual252.
From BB8 Require BB21_B21_grow BB25_W2PR_run BB25_W2PR_score.
Set Default Goal Selector "!".

(* machine: 0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR *)
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
  | UU, 0 => Some (0, TM.L, E)      | UU, 1 => Some (1, TM.L, VV)
  | VV, 0 => Some (0, TM.L, H)      | VV, 1 => Some (0, TM.L, WW)
  | WW, 0 => Some (1, TM.L, H)      | WW, 1 => Some (0, TM.L, XX)
  | XX, 0 => Some (1, TM.L, H)      | XX, 1 => Some (1, TM.L, YY)
  | YY, 0 => Some (0, TM.L, E)      | YY, 1 => Some (1, TM.L, RR)
  end.

Theorem halt : halts tm c0.
Proof. exact BB25_W2PR_score.haltW. Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -[ tm ]->* c /\ halted tm c /\ BB25_W2PR_score.onesN c N /\
    (BB21_B21_absdef.iter 5 BB25_W2PR_run.Fh (BB25_W2PR_run.tet 341) < N)%nat.
Proof. exact BB25_W2PR_score.sigma_lower_boundW. Qed.
