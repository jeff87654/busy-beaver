(** Independent probe for the M11b proofs (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB11_M11b.tm] is the declared machine
    1RG0LH_1RK1RC_0LD1LA_0RE1LD_0LI1RF_1RZ0RG_1RB1RG_1LA1LH_0LK0LJ_1LH1LI_1LJ1RE
    entry by entry (these 22 lines were generated from the machine string, not from the Coq file; the halting
    transition F0 (1RZ) is None), and the start configuration is the blank tape in state A; (2) the main theorems
    have the stated types; (3) they use no axioms.  It also prints the definitions the statements use. *)

From BB8 Require BB11_M11b BB11_M11b_fgh.
From BB8 Require Import Individual112.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB11_M11b.tm (A, 0) = Some (1, R, G)).  Check (eq_refl : BB11_M11b.tm (A, 1) = Some (0, L, H)).
Check (eq_refl : BB11_M11b.tm (B, 0) = Some (1, R, K)).  Check (eq_refl : BB11_M11b.tm (B, 1) = Some (1, R, C)).
Check (eq_refl : BB11_M11b.tm (C, 0) = Some (0, L, D)).  Check (eq_refl : BB11_M11b.tm (C, 1) = Some (1, L, A)).
Check (eq_refl : BB11_M11b.tm (D, 0) = Some (0, R, E)).  Check (eq_refl : BB11_M11b.tm (D, 1) = Some (1, L, D)).
Check (eq_refl : BB11_M11b.tm (E, 0) = Some (0, L, I)).  Check (eq_refl : BB11_M11b.tm (E, 1) = Some (1, R, F)).
Check (eq_refl : BB11_M11b.tm (F, 0) = None).  Check (eq_refl : BB11_M11b.tm (F, 1) = Some (0, R, G)).
Check (eq_refl : BB11_M11b.tm (G, 0) = Some (1, R, B)).  Check (eq_refl : BB11_M11b.tm (G, 1) = Some (1, R, G)).
Check (eq_refl : BB11_M11b.tm (H, 0) = Some (1, L, A)).  Check (eq_refl : BB11_M11b.tm (H, 1) = Some (1, L, H)).
Check (eq_refl : BB11_M11b.tm (I, 0) = Some (0, L, K)).  Check (eq_refl : BB11_M11b.tm (I, 1) = Some (0, L, J)).
Check (eq_refl : BB11_M11b.tm (J, 0) = Some (1, L, H)).  Check (eq_refl : BB11_M11b.tm (J, 1) = Some (1, L, I)).
Check (eq_refl : BB11_M11b.tm (K, 0) = Some (1, L, J)).  Check (eq_refl : BB11_M11b.tm (K, 1) = Some (1, R, E)).

Print BB11_M11b_fgh.f.
Print BB11_M11b_fgh.f_omega.
Print BB11_M11b_fgh.f_omega1.
Print BB11_M11b.iter.
Print BB11_M11b_fgh.sym_val.
Print BB11_M11b_fgh.count1.
Print BB11_M11b_fgh.ones.

Check BB11_M11b.halt.
Check BB11_M11b_fgh.score_exact.
Check BB11_M11b_fgh.sigma_lower_bound_m11.
Check BB11_M11b_fgh.sigma_lower_bound_64.

Print Assumptions BB11_M11b.halt.
Print Assumptions BB11_M11b_fgh.score_exact.
Print Assumptions BB11_M11b_fgh.sigma_lower_bound_m11.
Print Assumptions BB11_M11b_fgh.sigma_lower_bound_64.
