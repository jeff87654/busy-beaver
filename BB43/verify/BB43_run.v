(** * The BB(4,3) champion 1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD halts; exact final tape *)

(** Configurations (Ligocki notation, head on the cell left of "<D"):
      D(a,b,c)  = 0^inf   (11)^a (12)^b 2 2 1 <D (11)^c 0^inf     = [DL (const 0) a b c]
      D1(a,b,c) = 0^inf 1 (11)^a (12)^b 2 2 1 <D (11)^c 0^inf     = [DL (1 >> const 0) a b c]
    Functions:  g b = 2b+5,  f1 b = g^(b+3)(1) = 3*2^(b+4)-5,  G c = f1^(2c+11)(1).
    Rules (BB43_rules.v):
      DL_b  : D(a,b,c)    -->* D(a,0,f1^b c)
      DL_3k : D(3k+a,0,c) -->* D(a,0,G^k c)              (same for D1)
      R25   : D(2,0,c)  -->* D1(2c+8,3,1)
      R26   : D1(1,0,c) -->* D1(2c+7,3,1)
      R27   : D1(0,0,c) -->* D(2c+5,3,1)
      R28   : D(1,0,c)  -->* C0 halting configuration, 1^(4c+17) to the right of the head.
    Run: blank -(80 steps)-> D(2,2,1) -> D(2,0,e1) -> D1(2e1+8,0,v) -> D1(1,0,e2) -> D1(2e2+7,0,v)
         -> D1(0,0,e3) -> D(2e3+5,0,v) -> D(1,0,e4) -> halt,
    with e1 = f1^2(1), v = f1^3(1), and all values = 1 (mod 3). *)

From TM43 Require Import Individual43 BB43_rules.
From Coq Require Import Lia PeanoNat List.
From Coq.micromega Require Import ZifyNat.
Import ListNotations.
Set Default Goal Selector "!".

(** ** Residues mod 3 *)

Lemma g_mod : forall x, x mod 3 = 1%nat -> g x mod 3 = 1%nat.
Proof. intros x H. unfold g. lia. Qed.

Lemma iter_g_mod : forall n x, x mod 3 = 1%nat -> Nat.iter n g x mod 3 = 1%nat.
Proof. induction n; intros x H. - exact H. - simpl. apply g_mod. apply IHn. exact H. Qed.

Lemma f1_mod : forall b, f1 b mod 3 = 1%nat.
Proof. intros. unfold f1. apply iter_g_mod. reflexivity. Qed.

Lemma iter_f1_mod : forall n x, x mod 3 = 1%nat -> Nat.iter n f1 x mod 3 = 1%nat.
Proof. intros [|n] x H. - exact H. - simpl. apply f1_mod. Qed.

Lemma G_mod : forall c, G c mod 3 = 1%nat.
Proof. intros. unfold G. apply iter_f1_mod. reflexivity. Qed.

Lemma iter_G_mod : forall n x, x mod 3 = 1%nat -> Nat.iter n G x mod 3 = 1%nat.
Proof. intros [|n] x H. - exact H. - simpl. apply G_mod. Qed.

(** ** The three G-cascades, over abstract arguments *)

Definition E2 (e1 v : nat) : nat := Nat.iter ((2 * e1 + 7) / 3) G v.
Definition E3 (e1 v : nat) : nat := Nat.iter ((2 * E2 e1 v + 7) / 3) G v.
Definition E4 (e1 v : nat) : nat := Nat.iter ((2 * E3 e1 v + 4) / 3) G v.

Lemma chain : forall e1 v,
  e1 mod 3 = 1%nat -> v mod 3 = 1%nat ->
  (forall t a, DL t a 3 1 -->* DL t a 0 v) ->
  DL (const 0) 2 0 e1 -->* C;; const 0 {{0}} [1;1]^^(2 * E4 e1 v + 8) *> 1 >> const 0.
Proof.
  intros e1 v H1 Hv Hb.
  assert (M2 : E2 e1 v mod 3 = 1%nat) by (apply iter_G_mod; exact Hv).
  assert (M3 : E3 e1 v mod 3 = 1%nat) by (apply iter_G_mod; exact Hv).
  (* D(2,0,e1) -> D1(2e1+8,0,v) -> D1(1,0,e2) *)
  follow (R25 e1). follow (Hb (1 >> const 0) (2 * e1 + 8)).
  assert (K1 : 2 * e1 + 8 = 3 * ((2 * e1 + 7) / 3) + 1%nat) by lia.
  rewrite K1. follow (DL_3k ((2 * e1 + 7) / 3) (1 >> const 0) 1 v).
  fold (E2 e1 v).
  (* D1(1,0,e2) -> D1(2e2+7,0,v) -> D1(0,0,e3) *)
  follow (R26 (E2 e1 v)). follow (Hb (1 >> const 0) (2 * E2 e1 v + 7)).
  assert (K2 : 2 * E2 e1 v + 7 = 3 * ((2 * E2 e1 v + 7) / 3) + 0%nat) by lia.
  rewrite K2. follow (DL_3k ((2 * E2 e1 v + 7) / 3) (1 >> const 0) 0 v).
  fold (E3 e1 v).
  (* D1(0,0,e3) -> D(2e3+5,0,v) -> D(1,0,e4) -> halt *)
  follow (R27 (E3 e1 v)). follow (Hb (const 0) (2 * E3 e1 v + 5)).
  assert (K3 : 2 * E3 e1 v + 5 = 3 * ((2 * E3 e1 v + 4) / 3) + 1%nat) by lia.
  rewrite K3. follow (DL_3k ((2 * E3 e1 v + 4) / 3) (const 0) 1 v).
  fold (E4 e1 v).
  apply R28.
Qed.

(** ** From the blank tape *)

Lemma start : c0 -[ tm ]->* DL (const 0) 2 2 1.
Proof. unfold DL, c0, tape0. simpl. execute. Qed.

Definition e1 : nat := Nat.iter 2 f1 1%nat.
Definition v : nat := Nat.iter 3 f1 1%nat.
(** e4 is sealed, so that no tactic (lia, conversion) ever tries to evaluate it. *)
Lemma e4_sig : {x : nat | x = E4 e1 v}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition e4 : nat := proj1_sig e4_sig.
Lemma e4_eq : e4 = E4 e1 v.
Proof. exact (proj2_sig e4_sig). Qed.

Lemma ones_pairs : forall m (r : Stream sym), [1;1]^^m *> r = [1]^^(2 * m) *> r.
Proof.
  induction m; intros. - reflexivity.
  - replace (2 * S m) with (S (S (2 * m))) by lia. simpl. f_equal. f_equal. apply IHm.
Qed.

Lemma ones_shift : forall n (r : Stream sym), [1]^^n *> 1 >> r = [1]^^(S n) *> r.
Proof. induction n; intros. - reflexivity. - simpl. f_equal. apply IHn. Qed.

(** The halting configuration: state C reading a blank, with exactly 4*e4+17 ones to its right
    and blanks everywhere else.  C0 is the halting transition (1RZ), so the halting write adds one
    more 1: the final tape holds 4*e4+18 nonzero symbols, all of them 1. *)
Definition c_final : Q * tape := C;; const 0 {{0}} [1]^^(4 * e4 + 17) *> const 0.

Theorem reaches_final : c0 -[ tm ]->* c_final.
Proof.
  eapply evstep_trans; [apply start |].
  eapply evstep_trans; [apply (DL_b (const 0) 2 2 1) |].
  assert (Hc : c_final = C;; const 0 {{0}} [1;1]^^(2 * e4 + 8) *> 1 >> const 0).
  { unfold c_final. rewrite ones_pairs, ones_shift.
    replace (S (2 * (2 * e4 + 8))) with (4 * e4 + 17) by lia. reflexivity. }
  rewrite Hc, e4_eq. unfold e1, v. apply chain.
  - apply iter_f1_mod. reflexivity.
  - apply iter_f1_mod. reflexivity.
  - intros t a. apply DL_b.
Qed.

Theorem final_halted : halted tm c_final.
Proof. reflexivity. Qed.

Theorem bb43_halts : halts tm c0.
Proof. eapply halted_evstep_halts; [apply reaches_final | apply final_halted]. Qed.

(** sigma: the number of nonzero cells after the halting transition C0 = 1RZ. *)
Definition sigma : nat := 4 * e4 + 18.
