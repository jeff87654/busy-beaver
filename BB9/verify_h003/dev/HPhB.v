(** * HPhB.v (BB9/verify_h003; = ../verify_c7/dev/C7PhB.v on the same generated files: E0-free, so X3 = X' there) : phase B (the frame-1 rebuild, E0-free) in two generated pieces:
    PBab: Kx(1^n ++ [1]; 1; 3R+2; t; e1) -->+ S2n (12R+n-23) t,
          S2n x t = 1001001 (11111001)^t 00 (100)^29 1 (001)^x 110101 B> (nearest-first: the form the run reaches)
    PBc : S2n x t -->+ Kt(1^(x+27) ++ [7]; 1; 2; t), so Kx(1^n ++ [1];1;3R+2;t;e1) -->+ Kt(1^(12R+n+4) ++ [7]; 1; 2; t). *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules Abs KStep.
From XDev Require G_pbab G_pbc.
Opaque U arrow.
Local Open Scope nat_scope.

Definition e11 : side := lft [].
Definition e1 : side := S1 >> const S0.

Definition S2n (x t : nat) : Q * tape :=
  (S1 >> S0 >> S0 >> S1 >> S0 >> S0 >> S1 >> [S1;S1;S1;S1;S1;S0;S0;S1]^^t *> S0 >> S0 >> [S1;S0;S0]^^29 *> S1 >> [S0;S0;S1]^^x *>
   S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> const S0) {{B}}> const S0.

Lemma pbab : forall R n t, 1 <= R -> 11 <= n -> Kx (repeat 1 n ++ [1]) 1 (3 * R + 2) t e1 -->+ S2n (12 * R + n - 23) t.
Proof.
  intros R n t HR Hn. refine (prog_eq _ _ _ _ _ _ (G_pbab.PBab (3 * R - 3) (n - 11) t)).
  - unfold Kx, e1. rewrite lftx_app, lftx_rep. cbn [lftx].
    replace (3 * R + 2) with (5 + (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 5 (3 * R - 3)).
    replace n with (11 + (n - 11)) at 1 by lia. rewrite (pow_add [S1;S0;S1] 11 (n - 11)). reflexivity.
  - unfold S2n. replace (12 * R + n - 23) with ((n - 11) + 4 * (3 * R - 3)) by lia.
    rewrite (pow_add [S0;S0;S1] (n - 11) (4 * (3 * R - 3))), (pow_mul [S0;S0;S1] 4 (3 * R - 3)). reflexivity.
Qed.

Lemma pbc : forall x t, S2n x t -->+ Kx (repeat 1 (x + 27) ++ [7]) 1 2 t e11.
Proof.
  intros x t. refine (prog_eq _ _ _ _ _ _ (G_pbc.PBc t x)).
  - unfold S2n. reflexivity.
  - unfold Kx, e11. rewrite lftx_app, lftx_rep. cbn [lftx lft].
    replace (x + 27) with (27 + x) by lia. rewrite (pow_add [S1;S0;S1] 27 x). reflexivity.
Qed.

Lemma pb : forall R n t, 1 <= R -> 11 <= n ->
  Kx (repeat 1 n ++ [1]) 1 (3 * R + 2) t e1 -->+ Kx (repeat 1 (12 * R + n + 4) ++ [7]) 1 2 t e11.
Proof.
  intros R n t HR Hn. eapply progress_trans; [apply (pbab R n t HR Hn) |].
  replace (12 * R + n + 4) with (12 * R + n - 23 + 27) by lia. apply pbc.
Qed.
