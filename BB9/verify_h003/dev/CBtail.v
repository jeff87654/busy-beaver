(** CBtail.v : the class-b endgame tail (ESC -> DEC6 -> CDPx -> DEC3 -> CDPx -> HALT), on clean Kx/Kgx forms.
    Independent of the entry prefixes (G_pfx); composed in Endgame.v. *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules G_end Abs Lift Orbit Step.

(** DEC6 restated on a Kx token list: near [S z] zeros, counter 6, then a token x and rest; far side e. *)
Lemma dec6_kx : forall z r t x rest e, 0 < r ->
  Kx (repeat 1%nat (S z) ++ 6 :: x :: rest) 1 r t e -->+
  Kx (repeat 1%nat z ++ (2 * r + 3) :: 3 :: x :: rest) 1 2 t e.
Proof.
  intros z r t x rest e Hr.
  refine (prog_eq _ _ _ _ _ _ (DEC6 r t z ([0;1]^^x *> lftx rest e) Hr)).
  - unfold Kx. rewrite !lftx_app, !lftx_rep. cbn [lftx]. rewrite (pow_S [1;0;1] z). cbn [lpow Str_app]. reflexivity.
  - unfold Kx. rewrite !lftx_app, !lftx_rep. cbn [lftx].
    replace (2 * r + 3) with (3 + 2 * r) by lia.
    rewrite (pow_add [0;1] 3 (2 * r)), (pow_mul [0;1] 2 r). cbn [lpow Str_app]. reflexivity.
Qed.

(** DEC3 restated on a Kx token list (counter 3 -> 0). *)
Lemma dec3_kx : forall z r t x rest e, 0 < r ->
  Kx (repeat 1%nat (S z) ++ 3 :: x :: rest) 1 r t e -->+
  Kx (repeat 1%nat z ++ (2 * r + 3) :: 0%nat :: x :: rest) 1 2 t e.
Proof.
  intros z r t x rest e Hr.
  refine (prog_eq _ _ _ _ _ _ (DEC3 r t z ([0;1]^^x *> lftx rest e) Hr)).
  - unfold Kx. rewrite !lftx_app, !lftx_rep. cbn [lftx]. rewrite (pow_S [1;0;1] z). cbn [lpow Str_app]. reflexivity.
  - unfold Kx. rewrite !lftx_app, !lftx_rep. cbn [lftx].
    replace (2 * r + 3) with (3 + 2 * r) by lia.
    rewrite (pow_add [0;1] 3 (2 * r)), (pow_mul [0;1] 2 r). cbn [lpow Str_app]. reflexivity.
Qed.

(** HALT restated on a Kx token list: counter 0, then far token (S a), rest; far side e. r = 3R+1 form folded into r. *)
Lemma halt_kx : forall z r t a w rest e,
  Kx (repeat 1%nat (S z) ++ 0%nat :: (S a) :: w :: rest) 1 (S r) t e -->+
  ((1 >> [0;1]^^a *> 1 >> [0;1]^^w *> lftx rest e) <{{J}}
   (0 >> 1 >> 1 >> 1 >> 0 >> [1;0;1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >>
    [0;1;1]^^z *> [1;1;0;0;1;0;0;1]^^t *> 0 >> 1 >> const 0)).
Proof.
  intros z r t a w rest e.
  refine (prog_eq _ _ _ _ _ _ (HALT a r t z ([0;1]^^w *> lftx rest e))).
  - unfold Kx. rewrite !lftx_app, !lftx_rep. cbn [lftx].
    rewrite (lpow_snoc [1;0;1] z). cbn [lpow Str_app]. reflexivity.
  - reflexivity.
Qed.

(** A deposited counter token 6R+7 is the residue-1 digit tokd (2R+2); recognise it for CDPx. *)
Lemma kx_deposit_digit : forall K R rest t e,
  Kx (repeat 1%nat K ++ (6 * R + 7) :: rest) 1 2 t e = Kgx (repeat O K ++ [2 * R + 2]) rest O O t e.
Proof.
  intros. unfold Kgx. rewrite map_rep, map_single. unfold tokd.
  replace (3 * (2 * R + 2) + 1) with (6 * R + 7) by lia.
  change (3 * O + 1) with 1%nat. change (3 * O + 2) with 2%nat. rewrite <- app_assoc. reflexivity.
Qed.

Lemma kx_zeros_counter : forall K C rest R t e,
  Kgx (repeat O (S K)) (C :: rest) O R t e = Kx (repeat 1%nat (S K) ++ C :: rest) 1 (3 * R + 2) t e.
Proof. intros. unfold Kgx. rewrite map_rep0. reflexivity. Qed.

(** The class-b endgame tail from the clean pre-ESC form to the halt (ESC + two counter cycles + halt).
    Pre-ESC = Kgx (repeat O K ++ [2]) (6 :: S a :: w :: rest) 0 0 t e : near K zeros, digit-2 (D7), counter 6,
    the key's far token (S a), then w :: rest ; far side e (good).  Reaches an H1 (halted) configuration. *)
Lemma classb_tail : forall K a w rest t e, good e ->
  exists La Ra, Kgx (repeat O K ++ [2]) (6 :: S a :: w :: rest) O O t e -->+ ((1 >> La) <{{J}} Ra).
Proof.
  intros K a w rest t e He.
  set (R1 := iter 2 (U K) O).
  set (R2 := iter (2 * R1 + 2) (U K) O).
  set (R3 := iter (2 * R2 + 2) (U K) O).
  eexists. eexists.
  (* ESC: clear the digit-2 behind K zeros *)
  eapply evstep_progress_trans; [ apply (CDPx K 2 [] (6 :: S a :: w :: rest) O t e He) |].
  fold R1. rewrite app_nil_r, kx_zeros_counter.
  (* dec6: counter 6 -> 3, deposit 6R1+7 *)
  eapply progress_trans; [ apply (dec6_kx K (3 * R1 + 2) t (S a) (w :: rest) e ltac:(lia)) |].
  replace (2 * (3 * R1 + 2) + 3) with (6 * R1 + 7) by lia.
  rewrite kx_deposit_digit.
  (* CDPx clear the deposit -> R2 *)
  eapply evstep_progress_trans; [ apply (CDPx K (2 * R1 + 2) [] (3 :: S a :: w :: rest) O t e He) |].
  fold R2. rewrite app_nil_r, kx_zeros_counter.
  (* dec3: counter 3 -> 0, deposit 6R2+7 *)
  eapply progress_trans; [ apply (dec3_kx K (3 * R2 + 2) t (S a) (w :: rest) e ltac:(lia)) |].
  replace (2 * (3 * R2 + 2) + 3) with (6 * R2 + 7) by lia.
  rewrite kx_deposit_digit.
  (* CDPx clear the deposit -> R3 *)
  eapply evstep_progress_trans; [ apply (CDPx K (2 * R2 + 2) [] (0%nat :: S a :: w :: rest) O t e He) |].
  fold R3. rewrite app_nil_r, kx_zeros_counter.
  (* halt *)
  replace (3 * R3 + 2) with (S (3 * R3 + 1)) by lia.
  apply (halt_kx K (3 * R3 + 1) t a w rest e).
Qed.
