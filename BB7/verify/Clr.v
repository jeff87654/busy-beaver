(** * Clearing functions for the champ_231 / champ_232 digit list (machine independent) *)
From BB7 Require Import Defs.
From Coq Require Import Lia PeanoNat List.
Set Default Goal Selector "!".

(** ** Clearing functions *)
Lemma iter_S' : forall n g x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

(** (iter, UW, U, W are defined in Defs.v.)  U j x : the counter after clearing one unit of a digit at depth j (j zero digits nearer the counters),
    starting from counter x.  W j B : the counter after clearing j digits equal to 1 at depths 0..j-1 from B.
      U 0 x = 3x + 9              (R2 sets a = x + 3, then R1 a times: b -> b + 3)
      U (j+1) x = (U j)^(x+2-j) (W j 3)   (R3 writes 1^j, x+2-j with a = 1; R1 gives b = 3; then clear)
      W 0 B = B,  W (j+1) B = U j (W j B). *)
Lemma U_0 : forall x, U 0 x = 3 * x + 9.
Proof. reflexivity. Qed.
Lemma U_S : forall j x, U (S j) x = iter (x + 2 - j) (U j) (W j 3).
Proof. reflexivity. Qed.
Lemma W_0 : forall B, W 0 B = B.
Proof. reflexivity. Qed.
Lemma W_S : forall j B, W (S j) B = U j (W j B).
Proof. reflexivity. Qed.

Opaque U W.

Lemma iter_lin : forall g, (forall a, a + 1 <= g a) -> forall n x, x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma UW_ge : forall j, (forall x, x + 1 <= U j x) /\ (forall B, B + j <= W j B).
Proof.
  induction j as [| j [HU HW]].
  - split; intros; [rewrite U_0 | rewrite W_0]; lia.
  - split; intros.
    + rewrite U_S. pose proof (iter_lin (U j) HU (x + 2 - j) (W j 3)). specialize (HW 3). lia.
    + rewrite W_S. specialize (HW B). specialize (HU (W j B)). lia.
Qed.

Lemma U_ge : forall j x, x + 1 <= U j x.
Proof. intros. apply UW_ge. Qed.
Lemma W_ge : forall j B, B + j <= W j B.
Proof. intros. apply UW_ge. Qed.

Lemma iter_ge : forall j n x, x <= iter n (U j) x.
Proof. intros. pose proof (iter_lin (U j) (U_ge j) n x). lia. Qed.

