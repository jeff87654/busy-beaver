(** * Bridge.v : Defs.v's definitions are the ones the proofs use, and the helper steps Statement.v needs.

    Every bridge is stated pointwise at variable arguments and proved by reflexivity (the two definitions have the
    same body), so no functional extensionality and no computation on large closed numbers is involved. The helpers
    transport a bound proved with the proofs' constants to the same bound with Defs's constants, again at variable
    arguments (by conversion, which there only unfolds the two copies of the definitions); Statement.v instantiates
    them. *)
From M8 Require Import Individual82.
From Coq Require Import Lia PeanoNat.
From BB8 Require BB9_fw2_1RB0RD BB9_fw2_bound.
From Dev Require Abs.
From Score Require Score.
From Fgh Require FArith.
From M8 Require Import Defs.
Local Open Scope nat_scope.

Lemma iter_eq : forall n g x, iter n g x = Abs.iter n g x.
Proof. intros. reflexivity. Qed.

Lemma arrow_eq : forall k a b, arrow k a b = Abs.arrow k a b.
Proof. intros. reflexivity. Qed.

Lemma f_eq : forall k n, f k n = Score.f k n.
Proof. intros. reflexivity. Qed.

Lemma fomega_eq : forall n, f_omega n = Score.f_omega n.
Proof. intros. reflexivity. Qed.

Lemma fw1_eq : forall n, f_w1 n = FArith.f_w1 n.
Proof. intros. reflexivity. Qed.

(** fw2's own copy of the hierarchy (BB9_fw2_bound.v), used in the comparison with fw2. *)
Lemma fomega_fw2_eq : forall n, f_omega n = BB9_fw2_bound.f_omega n.
Proof. intros. reflexivity. Qed.

(** ** Helpers *)
Lemma fw3_bridge : forall a b N,
  Score.f_omega (Score.f_omega (Score.f_omega a)) < N /\ N < Score.f_omega (Score.f_omega (Score.f_omega b)) ->
  f_omega (f_omega (f_omega a)) < N /\ N < f_omega (f_omega (f_omega b)).
Proof. intros a b N H. exact H. Qed.

Lemma fw2_bridge : forall a b a' b' N, a = a' -> b = b' ->
  Score.f_omega (Score.f_omega a') < N /\ N < Score.f_omega (Score.f_omega b') ->
  f_omega (f_omega a) < N /\ N < f_omega (f_omega b).
Proof. intros a b a' b' N -> -> H. exact H. Qed.

Lemma fw1_bridge : forall a b N, FArith.f_w1 a < N /\ N < FArith.f_w1 b -> f_w1 a < N /\ N < f_w1 b.
Proof. intros a b N H. exact H. Qed.

Lemma fw2_lower_bridge : forall a N, BB9_fw2_bound.f_omega (BB9_fw2_bound.f_omega a) < N -> f_omega (f_omega a) < N.
Proof. intros a N H. exact H. Qed.

(** 12 B + 26 = 6 (2 B + 4) + 2 with 2 B + 4 = arrow 13 2 3 (FArith.Bx_knuth); here x, y, b are variables. *)
Lemma lin_bx : forall x y b, x = y -> 2 * b + 4 = y -> 6 * x + 2 = 12 * b + 26 /\ 6 * x + 3 = 12 * b + 27.
Proof. intros x y b -> H. lia. Qed.

Lemma bx_eq : 6 * arrow 13 2 3 + 2 = 12 * Abs.Bx + 26 /\ 6 * arrow 13 2 3 + 3 = 12 * Abs.Bx + 27.
Proof. exact (lin_bx _ _ _ (arrow_eq 13 2 3) FArith.Bx_knuth). Qed.

Lemma lin_bb8 : forall x y N, x = y -> 12 * y + 59 < N -> 12 * x + 59 < N.
Proof. intros x y N -> H. exact H. Qed.
