(** * C7Entry.v : the cascade entry of C7 plus its first sub-step (r = 1), from the generated ENTRY1 (generated):
    Kx(1^(5m); 1; 3R+2; t; blank) -->+ D0f (3+t) (9m-7) (12R+4) 0 (3m+3) blank.
    (The first D0 moment is L1 = 3n-4 = 15m-4 = 1 mod 5, P = 12R+8, y = 0; its sub-step gives L2 = (3L1-23)/5.) *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules Abs Lift KStep.
From XDev Require G_ent.
Opaque U arrow.
Local Open Scope nat_scope.

Lemma entry1 : forall R m t, 1 <= R -> 10 <= m ->
  Kx (repeat 1 (5 * m)) 1 (3 * R + 2) t (const S0) -->+ D0f (3 + t) (9 * m - 7) (12 * R + 4) 0 (3 * m + 3) (const S0).
Proof.
  intros R m t HR Hm. refine (prog_eq _ _ _ _ _ _ (G_ent.ENTRY1 (3 * R - 3) (m - 10) t)).
  - unfold Kx. rewrite lftx_rep.
    replace (3 * R + 2) with (5 + (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 5 (3 * R - 3)).
    replace (5 * m) with (50 + 5 * (m - 10)) by lia. rewrite (pow_add [S1;S0;S1] 50), (pow_mul [S1;S0;S1] 5 (m - 10)).
    reflexivity.
  - unfold D0f. rewrite (pow_add [S0;S0;S1;S1;S1;S1;S1;S1] 3 t).
    replace (9 * m - 7) with (9 * (m - 10) + 83) by lia. rewrite (pow_add [S1] (9 * (m - 10)) 83), (pow_mul [S1] 9 (m - 10)).
    replace (12 * R + 4) with (4 * (3 * R - 3) + 16) by lia.
    rewrite (pow_add [S0;S0;S1] (4 * (3 * R - 3)) 16), (pow_mul [S0;S0;S1] 4 (3 * R - 3)).
    replace (3 * m + 3) with (3 * (m - 10) + 33) by lia. rewrite (pow_add [S0;S1] (3 * (m - 10)) 33), (pow_mul [S0;S1] 3 (m - 10)).
    reflexivity.
Qed.
