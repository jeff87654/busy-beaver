(** * ThmTG: the machine's calculus at the level of codes.

    [thm_tg n]: n is derivable from the AX rows and gated bundles by MP and GEN, with the
    truth code 0 as an axiom (stack zeros, failed MP and failed gates produce 0).
    L1 proves  enum_tg_halts <-> thm_tg 1;  the bridge relates thm_tg to the set theory SIR. *)
From Coq Require Import Arith Lia.
From M254TGL Require Import CodesTG.

Inductive thm_tg : nat -> Prop :=
  | T_true : thm_tg 0
  | T_mp t b : thm_tg t -> thm_tg (wim t b) -> thm_tg b
  | T_gen a h : thm_tg h -> thm_tg (wal a h)
  | T_r1 a b : thm_tg (rho1 a b)
  | T_r2 a b c : thm_tg (rho2 a b c)
  | T_r3 a b c : thm_tg (rho3 a b c)
  | T_r4 a b c : thm_tg (rho4 a b c)
  | T_r5 a b c : thm_tg (rho5 a b c)
  | T_r6 a b : thm_tg (rho6 a b)
  | T_r7 a b c : thm_tg (rho7 a b c)
  | T_r8 a b c u : thm_tg (rho8 a b c u)
  | T_bundle a b c : c <> a -> c <> b -> thm_tg (bundle_tg a b c).
