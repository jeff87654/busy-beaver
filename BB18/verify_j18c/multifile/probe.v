(** Independent probe for the J18_w2_C (Argon) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB18_J18_w2_C_tnf.tm] is the declared machine
    0LB1LF_0RC1LB_0RD1RM_1LE0RN_1LF1LE_1LG0LE_1RH1RP_1RI1RH_0LJ1RA_1LK1LJ_0LL1LJ_1RM1RC_0RM0RH_1LE1RO_1RZ1RD_0LF0RQ_0LH1RR_0LF1RP
    entry by entry (these 36 checks were generated from the machine string, not from the Coq file; the halting
    transition (1RZ) is None; the 17th and 18th states, letters Q and R, are the constructors QQ and RR), and the start configuration is the blank tape in state A;
    (2) the main theorems have the stated types; (3) they use no axioms.  It also prints the definitions the
    statements use.  The setup names states L and O, so directions are written TM.L / TM.R. *)

From BB8 Require BB18_J18_w2_C_tnf BB18_J18_w2_C_tnf_cmp.
From BB8 Require Import Individual182.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (A, 0) = Some (0, TM.L, B)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (A, 1) = Some (1, TM.L, F)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (B, 0) = Some (0, TM.R, C)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (B, 1) = Some (1, TM.L, B)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (C, 0) = Some (0, TM.R, D)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (C, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (D, 0) = Some (1, TM.L, E)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (D, 1) = Some (0, TM.R, N)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (E, 0) = Some (1, TM.L, F)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (E, 1) = Some (1, TM.L, E)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (F, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (F, 1) = Some (0, TM.L, E)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (G, 0) = Some (1, TM.R, H)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (G, 1) = Some (1, TM.R, P)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (H, 0) = Some (1, TM.R, I)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (H, 1) = Some (1, TM.R, H)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (I, 0) = Some (0, TM.L, J)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (I, 1) = Some (1, TM.R, A)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (J, 0) = Some (1, TM.L, K)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (J, 1) = Some (1, TM.L, J)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (K, 0) = Some (0, TM.L, L)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (K, 1) = Some (1, TM.L, J)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (L, 0) = Some (1, TM.R, M)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (L, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (M, 0) = Some (0, TM.R, M)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (M, 1) = Some (0, TM.R, H)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (N, 0) = Some (1, TM.L, E)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (N, 1) = Some (1, TM.R, O)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (O, 0) = None).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (O, 1) = Some (1, TM.R, D)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (P, 0) = Some (0, TM.L, F)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (P, 1) = Some (0, TM.R, QQ)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (QQ, 0) = Some (0, TM.L, H)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (QQ, 1) = Some (1, TM.R, RR)).
Check (eq_refl : BB18_J18_w2_C_tnf.tm (RR, 0) = Some (0, TM.L, F)).  Check (eq_refl : BB18_J18_w2_C_tnf.tm (RR, 1) = Some (1, TM.R, P)).

Print BB18_J18_w2_C_tnf.iter.
Print BB18_J18_w2_C_tnf.f.
Print BB18_J18_w2_C_tnf.f_omega.
Print BB18_J18_w2_C_tnf.f_wk.
Print BB18_J18_w2_C_tnf.f_w2.
Print BB18_J18_w2_C_tnf.h.
Print BB18_J18_w2_C_tnf.hc.
Print BB18_J18_w2_C_tnf.G0.
Print BB18_J18_w2_C_tnf.Gcy.
Print BB18_J18_w2_C_tnf.G.
Print BB18_J18_w2_C_tnf.ho.
Print BB18_J18_w2_C_tnf.hoc.
Print BB18_J18_w2_C_tnf.sym_val.
Print BB18_J18_w2_C_tnf.count1.
Print BB18_J18_w2_C_tnf.ones.

Check BB18_J18_w2_C_tnf.halt.
Check BB18_J18_w2_C_tnf.score_exact.
Check BB18_J18_w2_C_tnf.sigma_lower_bound.
Check BB18_J18_w2_C_tnf_cmp.beats_R18a.
Check BB18_J18_w2_C_tnf_cmp.beats_J16.

Print Assumptions BB18_J18_w2_C_tnf.halt.
Print Assumptions BB18_J18_w2_C_tnf.score_exact.
Print Assumptions BB18_J18_w2_C_tnf.sigma_lower_bound.
Print Assumptions BB18_J18_w2_C_tnf_cmp.beats_R18a.
Print Assumptions BB18_J18_w2_C_tnf_cmp.beats_J16.
