(** * C7Halt.v : the r = 2 branch of C7's cascade (step 9) and the halt (BB9/verify_c7).

    D0f (S t) (15u+17) (p+2) 2 (y+5) l  -->+ W1c (p+1) t u y l          (R2A1: 1^L -> (00111) blocks)
    W1c (A+5) t u y l -->+ Vc 0 A (3u+1) (3u+6) t y l                    (PRE: to the first round, X' in J = C7's H0)
    Vc d (A+4) (b+4) c t y l -->+ Vc (S d) A (b+1) (c+3) t y l           (ROUND: one round; [rounds] by induction)
    Vc d A 1 (c+3) t y l -->+ Q3c d A (3c+14) t y l                     (VHq: the end of the last round, 1^(3c+14))
    Q3c d A (5w+4) t y l -->+ Hc d A w t y l (halting: J reading 1)        (VH2b; 3c+14 = 5w+4 when u = 5jj+2)
    Vc d A b c t y l = l 1 (10)^2 1 (10)^(y+5) (1(10)^4)^d 101 (10)^4 0 111 (001)^A <J> 0 1111 0 (01)^b 00 (101)^c
                      (10011100)^(t+1) 100101   (far-first left, head, right). *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules Abs Lift KStep.
From XDev Require G_r2a1 G_r2pre G_r2round G_r2vhq G_r2vh2b.
From XDev Require Ones.
Opaque U arrow.
Local Open Scope nat_scope.

Definition W1c (q t u y : nat) (l : side) : Q * tape :=
  (S1 >> S0 >> S0 >> S1 >> S0 >> S0 >> S1 >> S1 >> S1 >> [S1;S1;S1;S0;S0;S1;S1;S1]^^t *> [S1;S1;S1;S0;S0;S1;S1;S1;S0;S0;S1;S1;S1;S0;S0]^^u *>
   S1 >> S1 >> S1 >> S0 >> S0 >> S1 >> S1 >> S1 >> S0 >> S0 >> S1 >> S1 >> S1 >> S0 >> S0 >> S1 >> S1 >> S1 >> S0 >> S0 >> S1 >> S1 >> S1 >> S1 >> S1 >> S0 >>
   [S1;S0;S0]^^q *> S1 >> S1 >> S1 >> S0 >> [S0;S1]^^y *> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S1 >> l)
  {{B}}> const S0.

Definition Vc (d A b c t y : nat) (l : side) : Q * tape :=
  ([S1;S0;S0]^^A *> S1 >> S1 >> S1 >> S0 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> [S0;S1;S0;S1;S0;S1;S0;S1;S1]^^d *>
   [S0;S1]^^y *> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> S1 >> l) {{J}}>
  (S0 >> S1 >> S1 >> S1 >> S1 >> S0 >> [S0;S1]^^b *> S0 >> S0 >> [S1;S0;S1]^^c *> [S1;S0;S0;S1;S1;S1;S0;S0]^^t *>
   S1 >> S0 >> S0 >> S1 >> S1 >> S1 >> S0 >> S0 >> S1 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0).

Lemma r2a1 : forall p t u y l,
  D0f (S t) (15 * u + 17) (p + 2) 2 (y + 5) l -->+ W1c (S p) t u y l.
Proof.
  intros p t u y l. refine (prog_eq _ _ _ _ _ _ (G_r2a1.R2A1 p t u y l)).
  - unfold D0f. rewrite (pow_add [S1] (15 * u) 17), (pow_mul [S1] 15 u), (pow_add [S0;S0;S1] p 2), (pow_add [S0;S1] y 5).
    reflexivity.
  - unfold W1c. rewrite lpow_snoc. reflexivity.
Qed.

Lemma pre : forall A t u y l, W1c (A + 5) t u y l -->+ Vc 0 A (3 * u + 1) (3 * u + 6) t y l.
Proof.
  intros A t u y l. refine (prog_eq _ _ _ _ _ _ (G_r2pre.PRE A t u y l)).
  - unfold W1c. rewrite (pow_add [S1;S0;S0] A 5). reflexivity.
  - unfold Vc. rewrite (pow_add [S0;S1] (3 * u) 1), (pow_mul [S0;S1] 3 u), (pow_add [S1;S0;S1] (3 * u) 6), (pow_mul [S1;S0;S1] 3 u).
    reflexivity.
Qed.

Lemma rnd : forall d A b c t y l, Vc d (A + 4) (b + 4) c t y l -->+ Vc (S d) A (b + 1) (c + 3) t y l.
Proof.
  intros d A b c t y l. refine (prog_eq _ _ _ _ _ _ (G_r2round.ROUND A b c d t y l)).
  - unfold Vc. rewrite (pow_add [S1;S0;S0] A 4), (pow_add [S0;S1] b 4). reflexivity.
  - unfold Vc. rewrite (pow_S [S0;S1;S0;S1;S0;S1;S0;S1;S1] d), (pow_add [S0;S1] b 1), (pow_add [S1;S0;S1] c 3). reflexivity.
Qed.

Lemma rounds : forall i d A b c t y l,
  Vc d (A + 4 * i) (b + 3 * i + 1) c t y l -->* Vc (d + i) A (b + 1) (c + 3 * i) t y l.
Proof.
  induction i as [| i IH]; intros d A b c t y l.
  - replace (A + 4 * 0) with A by lia. replace (b + 3 * 0 + 1) with (b + 1) by lia.
    replace (d + 0) with d by lia. replace (c + 3 * 0) with c by lia. apply evstep_refl.
  - replace (A + 4 * S i) with ((A + 4 * i) + 4) by lia. replace (b + 3 * S i + 1) with ((b + 3 * i) + 4) by lia.
    eapply evstep_trans; [apply progress_evstep, rnd |].
    replace (b + 3 * i + 1) with (b + 3 * i + 1) by reflexivity.
    replace (d + S i) with (S d + i) by lia. replace (c + 3 * S i) with ((c + 3) + 3 * i) by lia.
    apply IH.
Qed.

(** ** After the last round: VH1 (to the B> moment), VH2a (to the last pass), VH2b (the halt). *)
Definition Q3c (d A X t y : nat) (l : side) : Q * tape :=
  (S1 >> S0 >> S0 >> S1 >> S0 >> S0 >> [S1;S1;S1;S1;S1;S1;S0;S0]^^t *> S1 >> S1 >> S1 >> S1 >> S1 >> S1 >> S0 >> S0 >> S1 >> S1 >> S1 >> S1 >> S1 >> S1 >> S0 >> S0 >>
   [S1]^^X *> S0 >> S1 >> [S0;S1;S1]^^A *> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S1 >>
   [S0;S1;S0;S1;S0;S1;S0;S1;S1]^^d *> [S0;S1]^^y *> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> S1 >> l)
  {{B}}> const S0.

(** The halting configuration: X' in J reading 1 (C7's H1). *)
Definition Hleft (d A y : nat) : list Sym :=
  [S0;S1;S1]^^A ++ [S0;S1;S0;S1;S0;S1;S0;S1;S0;S1;S0;S1;S0;S1;S1] ++ [S0;S1;S0;S1;S0;S1;S0;S1;S1]^^d ++ [S0;S1]^^y ++ [S0;S1;S0;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S0;S1;S1].
Definition Hright (w t : nat) : list Sym :=
  [S1;S1;S1;S1] ++ [S0;S0;S1;S1;S1]^^w ++ [S0;S0;S1;S0;S0;S1;S1;S1]^^t ++ [S0;S0;S1;S0;S0;S1;S1;S1;S0;S0;S1;S0;S0;S1;S1;S1;S0;S0;S1;S0;S0;S1;S0;S1].
Definition Hc (d A w t y : nat) (l : side) : Q * tape := (Hleft d A y *> l) {{J}}> (S1 >> Hright w t *> const S0).

Lemma vh : forall d A c t y l, Vc d A 1 (c + 3) t y l -->+ Q3c d A (3 * c + 14) t y l.
Proof.
  intros d A c t y l. refine (prog_eq _ _ _ _ _ _ (G_r2vhq.VHq A c d t y l)).
  - unfold Vc. rewrite (pow_add [S1;S0;S1] c 3). reflexivity.
  - unfold Q3c. rewrite (pow_add [S1] (3 * c) 14), (pow_mul [S1] 3 c). reflexivity.
Qed.

Lemma vh2 : forall d A w t y l, Q3c d A (5 * w + 4) t y l -->+ Hc d A w t y l.
Proof.
  intros d A w t y l. refine (prog_eq _ _ _ _ _ _ (G_r2vh2b.VH2b A d t w y l)).
  - unfold Q3c. rewrite (pow_add [S1] (5 * w) 4), (pow_mul [S1] 5 w). reflexivity.
  - unfold Hc, Hleft, Hright. rewrite !Str_app_assoc. reflexivity.
Qed.

Lemma Hc_halted : forall d A w t y l, halted tm (Hc d A w t y l).
Proof. intros. unfold Hc. reflexivity. Qed.

Lemma count1_pow : forall xs n, Ones.count1 (xs^^n) = n * Ones.count1 xs.
Proof. intros xs n. induction n as [| n IH]; [reflexivity |]. cbn [lpow]. rewrite Ones.count1_app, IH. lia. Qed.

Lemma Hc_ones : forall d A w t y Ll, exists N, Ones.ones (Hc d A w t y (Ll *> const S0)) N /\ 2 * A <= N.
Proof.
  intros d A w t y Ll. exists (Ones.count1 (Hleft d A y ++ Ll) + 1 + Ones.count1 (Hright w t)). split.
  - exists J, (Hleft d A y ++ Ll), (Hright w t), S1. split; [| reflexivity].
    unfold Hc. rewrite Str_app_assoc. reflexivity.
  - unfold Hleft. rewrite !Ones.count1_app, !count1_pow. cbn [Ones.count1 Ones.sym_val]. lia.
Qed.
