(* machine: 1RB0LK_1RC1RB_1RD1RM_1RE0LH_1LF1RI_0LA1LG_1RL0LF_1LK1LD_1RJ0RB_1RG0LK_1LA1LK_---0LF_0LN1LA_0RE1LN *)
(** * M14_fw3x4 (14 states, Gemini 4 Neon): the entry's statements, for the table named by the machine string

    Neon's proof [BB14_M14_fw3x4.v] (kept byte-identical in this directory) works with the machine in the state
    order of M12's core, started in G ([tm], [c0_core]), and transfers its results to the same machine with the
    states renamed in order of first visit, started in A ([tm_tnf], BusyCoq's [c0]; the renaming is the Coq lemma
    [tm_perm_tnf]).  The renamed table is the one named by the machine string above.  This file states the results
    for that table under the name [tm], with [Theorem halt : halts tm c0], the form this project's check.py reads.
    The table below is written out again; Coq accepts the proofs only because it is the same term as Neon's
    [tm_tnf] (conversion), and probe.v checks it entry by entry against the machine string. *)

From BB8 Require Import Individual142.
From BB8 Require BB14_M14_fw3x4.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.R, B)  | A, 1 => Some (0, TM.L, K)
  | B, 0 => Some (1, TM.R, C)  | B, 1 => Some (1, TM.R, B)
  | C, 0 => Some (1, TM.R, D)  | C, 1 => Some (1, TM.R, M)
  | D, 0 => Some (1, TM.R, E)  | D, 1 => Some (0, TM.L, H)
  | E, 0 => Some (1, TM.L, F)  | E, 1 => Some (1, TM.R, I)
  | F, 0 => Some (0, TM.L, A)  | F, 1 => Some (1, TM.L, G)
  | G, 0 => Some (1, TM.R, L)  | G, 1 => Some (0, TM.L, F)
  | H, 0 => Some (1, TM.L, K)  | H, 1 => Some (1, TM.L, D)
  | I, 0 => Some (1, TM.R, J)  | I, 1 => Some (0, TM.R, B)
  | J, 0 => Some (1, TM.R, G)  | J, 1 => Some (0, TM.L, K)
  | K, 0 => Some (1, TM.L, A)  | K, 1 => Some (1, TM.L, K)
  | L, 0 => None               | L, 1 => Some (0, TM.L, F)
  | M, 0 => Some (0, TM.L, N)  | M, 1 => Some (1, TM.L, A)
  | N, 0 => Some (0, TM.R, E)  | N, 1 => Some (1, TM.L, N)
  end.

(** The machine halts from the blank tape. *)
Theorem halt : halts tm c0.
Proof. exact BB14_M14_fw3x4.halt_tnf. Qed.

(** Its halting tape holds exactly [N_final] = p + a + 7 ones, for the explicit pair (p, a) = [pa_final] of Neon's
    four-loop recursion ([ones] is Neon's: a finite word padded with 0s on both sides holding that many ones).
    L0 is read on a 0; with the halting transition written 1RZ, sigma = N_final + 1. *)
Theorem score_exact :
  exists c, c0 -[ tm ]->* c /\ halted tm c /\ BB14_M14_fw3x4.ones c BB14_M14_fw3x4.N_final.
Proof. exact BB14_M14_fw3x4.score_exact_tnf. Qed.

(** f_(omega+3)^4(f_omega(4)) < N, with the standard fast-growing hierarchy of Neon's file
    (f 0 = S, f (k+1) n = (f k)^n n, f_omega n = f n n, f_omega(k+1) n = f_omega(k)^n n, iter n g = g^n). *)
Theorem sigma_bound :
  exists c n, c0 -[ tm ]->* c /\ halted tm c /\ BB14_M14_fw3x4.ones c n /\
  n > BB14_M14_fw3x4.iter 4 BB14_M14_fw3x4.f_omega3 (BB14_M14_fw3x4.f_omega 4).
Proof. exact BB14_M14_fw3x4.sigma_bound_tnf. Qed.

Print Assumptions halt.
Print Assumptions score_exact.
Print Assumptions sigma_bound.
