(** * Rules for the BB(4,3) machine 1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD *)

(** Tape convention (busycoq): [l <{{Q}} r] has the head on [hd l]; [l {{Q}}> r] has the head on [hd r].
    A left stream is listed from the head outwards, so the Ligocki word "X (12)^a 2 1 <D" becomes
    [(1 >> 2 >> [2;1]^^a *> X)].  The halting transition C0 = 1RZ is [None]. *)

From TM43 Require Import Individual43.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, R, D)  | A, 2 => Some (1, L, C)
  | B, 0 => Some (2, L, B)  | B, 1 => Some (1, R, B)  | B, 2 => Some (1, L, C)
  | C, 0 => None            | C, 1 => Some (1, L, A)  | C, 2 => Some (1, L, D)
  | D, 0 => Some (0, R, B)  | D, 1 => Some (2, R, A)  | D, 2 => Some (2, R, D)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma align_lpow : forall (x : sym) xs ys n,
  (x::xs)^^n *> x >> ys = x >> (xs ++ [x])^^n *> ys.
Proof.
  induction n.
  - reflexivity.
  - simpl. repeat rewrite Str_app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma align_lpow_const : forall (x : sym) xs n,
  (x::xs)^^n *> const x = x >> (xs ++ [x])^^n *> const x.
Proof. intros. rewrite const_unfold at 1. apply align_lpow. Qed.

Ltac align_tape := repeat ((rewrite align_lpow || rewrite align_lpow_const); simpl app).
Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
Ltac finish_norm := apply evstep_refl'; norm_nat; align_tape; try reflexivity; lia_refl.
Lemma lpow_add_app : forall (xs : list sym) n m r, xs^^(n + m) *> r = xs^^n *> xs^^m *> r.
Proof. intros. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

(** Rotate the block under the head: [hd ((x::xs)^^n *> x >> ys)] becomes [x]. *)
Ltac align_head1 := match goal with
  | |- context [Streams.hd ?T] =>
    lazymatch T with
    | (?xs ^^ ?n) *> (?xs' ^^ ?m) *> ?ys =>
      let E := fresh "E" in
      assert (E : T = xs ^^ (n + m) *> ys) by (symmetry; apply lpow_add_app);
      rewrite E; clear E
    | ((?x :: ?xs) ^^ ?n) *> ?x' >> ?ys =>
      let E := fresh "E" in
      assert (E : T = x' >> (xs ++ [x]) ^^ n *> ys) by (apply align_lpow);
      rewrite E; clear E; simpl app
    | ((?x :: ?xs) ^^ ?n) *> const ?x' =>
      let E := fresh "E" in
      assert (E : T = x' >> (xs ++ [x]) ^^ n *> const x') by (apply align_lpow_const);
      rewrite E; clear E; simpl app
    end
  end.
Ltac align_head := align_head1; try align_head1.
(** step, re-aligning a stuck head first *)
Ltac go := repeat (try solve [finish]; (step || (align_head; step))).


Lemma c0_split : const 0 = 0 >> 0 >> const 0.
Proof. rewrite const_unfold at 1. rewrite const_unfold at 1. reflexivity. Qed.

(** ** Sweeps *)

Lemma D_22 : forall n l r, l {{D}}> [2]^^n *> r -->* ([2]^^n *> l) {{D}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma D_11 : forall n l r, l {{D}}> [1;1]^^n *> r -->* ([1;2]^^n *> l) {{D}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma A_11 : forall n l r, l {{A}}> [1;1]^^n *> r -->* ([2;1]^^n *> l) {{A}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma B_11 : forall n l r, l {{B}}> [1;1]^^n *> r -->* ([1;1]^^n *> l) {{B}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma C_21 : forall n l r, ([1;2]^^n *> l) <{{C}} r -->* l <{{C}} [1;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma A_12 : forall n l r, ([2;1]^^n *> l) <{{A}} r -->* l <{{A}} [1;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Ltac sweep := first [follow D_11 | follow A_11 | follow B_11 | follow C_21 | follow A_12 | follow D_22].
(** bounded variant: at most n actions *)
Ltac run1 := try (solve [finish_norm] || step || (align_head; step) || sweep).
Tactic Notation "runn" int_or_var(n) := do n run1.
Ltac run := repeat (try solve [finish_norm]; (step || (align_head; step) || sweep)).

(** P6: (12)^a A> 0 0  -->  <A (11)^(a+1) *)
Lemma P6 : forall a l r, l {{A}}> [1;1]^^a *> 0 >> 0 >> r -->* l <{{A}} [1;1]^^(S a) *> r.
Proof.
  intros. follow A_11. do 5 step. follow A_12. finish_norm.
Qed.

(** ** Basic rules (Polygon's numbering on the bbchallenge wiki) *)

(** R10: 2 <D (11)^(a+1) 0 0  -->  <D (11)^(a+2) 2 *)
Lemma R10 : forall a l r,
  (2 >> l) <{{D}} [1;1]^^(S a) *> 0 >> 0 >> r -->* l <{{D}} [1;1]^^(S (S a)) *> 2 >> r.
Proof. intros. run. Qed.


(** R11: 2 <D (11)^a 2 0 0  -->  <D (11)^(a+1) 2 2 *)
Lemma R11 : forall a l r,
  (2 >> l) <{{D}} [1;1]^^a *> 2 >> 0 >> 0 >> r -->* l <{{D}} [1;1]^^(S a) *> 2 >> 2 >> r.
Proof. intros. run. Qed.

(** R12: 1 <A (11)^b 0 0  -->  <A (11)^(b+1) 2 *)
Lemma R12 : forall b l r,
  (1 >> l) <{{A}} [1;1]^^b *> 0 >> 0 >> r -->* l <{{A}} [1;1]^^(S b) *> 2 >> r.
Proof. intros. run. Qed.

(** R13: 1 <A (11)^b 2 0 0  -->  <A (11)^(b+1) 2 2 *)
Lemma R13 : forall b l r,
  (1 >> l) <{{A}} [1;1]^^b *> 2 >> 0 >> 0 >> r -->* l <{{A}} [1;1]^^(S b) *> 2 >> 2 >> r.
Proof. intros. run. Qed.

(** R14: (12) 1 <D (11)^b 0 0  -->  1 <D (11)^(b+2) *)
Lemma R14 : forall b l r,
  (1 >> 2 >> 1 >> l) <{{D}} [1;1]^^b *> 0 >> 0 >> r -->* (1 >> l) <{{D}} [1;1]^^(S (S b)) *> r.
Proof. intros. run. Qed.

(** Versions with a blank right end. *)
Lemma R10c : forall a l,
  (2 >> l) <{{D}} [1;1]^^(S a) *> const 0 -->* l <{{D}} [1;1]^^(S (S a)) *> 2 >> const 0.
Proof. intros. rewrite c0_split at 1. apply R10. Qed.

Lemma R11c : forall a l,
  (2 >> l) <{{D}} [1;1]^^a *> 2 >> const 0 -->* l <{{D}} [1;1]^^(S a) *> 2 >> 2 >> const 0.
Proof. intros. rewrite c0_split at 1. apply R11. Qed.

Lemma R12c : forall b l,
  (1 >> l) <{{A}} [1;1]^^b *> const 0 -->* l <{{A}} [1;1]^^(S b) *> 2 >> const 0.
Proof. intros. rewrite c0_split at 1. apply R12. Qed.

Lemma R13c : forall b l,
  (1 >> l) <{{A}} [1;1]^^b *> 2 >> const 0 -->* l <{{A}} [1;1]^^(S b) *> 2 >> 2 >> const 0.
Proof. intros. rewrite c0_split at 1. apply R13. Qed.

Lemma R14c : forall b l,
  (1 >> 2 >> 1 >> l) <{{D}} [1;1]^^b *> const 0 -->* (1 >> l) <{{D}} [1;1]^^(S (S b)) *> const 0.
Proof. intros. rewrite c0_split at 1. apply R14. Qed.

(** R15: (12)^a 1 <D (11)^b 0^inf  -->  1 <D (11)^(b+2a) 0^inf *)
Lemma R15 : forall a b l,
  (1 >> [2;1]^^a *> l) <{{D}} [1;1]^^b *> const 0 -->* (1 >> l) <{{D}} [1;1]^^(b + 2 * a) *> const 0.
Proof.
  induction a; intros.
  - finish.
  - simpl lpow. simpl Str_app. follow R14c. follow IHa. finish.
Qed.

(** R16: (12) 2 1 <D (11)^b 0^inf  -->  2 (12)^(b+2) 1 <D (11) 0^inf *)
Lemma R16 : forall b l,
  (1 >> 2 >> 2 >> 1 >> l) <{{D}} [1;1]^^b *> const 0 -->*
  (1 >> [2;1]^^(S (S b)) *> 2 >> l) <{{D}} [1;1]^^1 *> const 0.
Proof. intros. run. Qed.

Definition g (b : nat) : nat := 2 * b + 5.

(** R17: (12) 2 1 <D (11)^b 0^inf  -->  2 1 <D (11)^(2b+5) 0^inf *)
Lemma R17 : forall b l,
  (1 >> 2 >> 2 >> 1 >> l) <{{D}} [1;1]^^b *> const 0 -->* (1 >> 2 >> l) <{{D}} [1;1]^^(g b) *> const 0.
Proof. intros. follow R16. follow R15. unfold g. finish. Qed.

Lemma iter_succ_r : forall (f : nat -> nat) n x, Nat.iter (S n) f x = Nat.iter n f (f x).
Proof. induction n; intros. - reflexivity. - simpl in *. rewrite <- IHn. reflexivity. Qed.

(** R18: (12)^a 2 1 <D (11)^b 0^inf  -->  2 1 <D (11)^(g^a b) 0^inf *)
Lemma R18 : forall a b l,
  (1 >> 2 >> [2;1]^^a *> l) <{{D}} [1;1]^^b *> const 0 -->*
  (1 >> 2 >> l) <{{D}} [1;1]^^(Nat.iter a g b) *> const 0.
Proof.
  induction a; intros.
  - finish.
  - rewrite iter_succ_r. simpl lpow. simpl Str_app. follow R17. follow IHa. finish.
Qed.

(** R21a: 2 2 1 <D (11)^b 0^inf  -->  2 <D (11)^(b+2) 0^inf *)
Lemma R21a : forall b l,
  (1 >> 2 >> 2 >> l) <{{D}} [1;1]^^b *> const 0 -->* (2 >> l) <{{D}} [1;1]^^(S (S b)) *> const 0.
Proof. intros. run. Qed.

(** R20: 1 <D (11)^(b+1) 2 0^inf  -->  2 1 <D (11)^(2b+1) 0^inf *)
Lemma R20 : forall b l,
  (1 >> l) <{{D}} [1;1]^^(S b) *> 2 >> const 0 -->* (1 >> 2 >> l) <{{D}} [1;1]^^(1 + 2 * b) *> const 0.
Proof.
  intros. remember (1 + 2 * b) as k.
  do 3 step. follow A_11. step. align_head. step. align_head.
  follow (R15 b 1 (2 >> l)). subst k. finish.
Qed.

(** R22: 1 <D (11)^(b+1) 2 2 0^inf  -->  2 (12)^b 2 1 <D (11) 0^inf *)
Lemma R22 : forall b l,
  (1 >> l) <{{D}} [1;1]^^(S b) *> 2 >> 2 >> const 0 -->*
  (1 >> 2 >> [2;1]^^b *> 2 >> l) <{{D}} [1;1]^^1 *> const 0.
Proof. intros. run. Qed.

(** Y: 1 1 1 <D (11)^b 0^inf  -->  1 <A (11)^(b+2) 0^inf *)
Lemma Y : forall b l,
  (1 >> 1 >> 1 >> l) <{{D}} [1;1]^^b *> const 0 -->* (1 >> l) <{{A}} [1;1]^^(S (S b)) *> const 0.
Proof. intros. run. Qed.

(** R23z: A> 1 (11)^b 2 2 0^inf  -->  (12)^b 2 2 1 <D (11) 0^inf *)
Lemma R23z : forall b l,
  (1 >> l) <{{A}} [1;1]^^b *> 2 >> 2 >> const 0 -->*
  (1 >> 2 >> 2 >> [2;1]^^b *> l) <{{D}} [1;1]^^1 *> const 0.
Proof. intros. run. Qed.

(** ** The f1 level: one (12) of the b-counter *)

Definition f1 (b : nat) : nat := Nat.iter (S (S (S b))) g 1%nat.

(** R21: (12) 2 2 1 <D (11)^b 0^inf  -->  2 2 1 <D (11)^(f1 b) 0^inf *)
Lemma R21 : forall a b l,
  (1 >> 2 >> 2 >> [2;1]^^(S a) *> l) <{{D}} [1;1]^^b *> const 0 -->*
  (1 >> 2 >> 2 >> [2;1]^^a *> l) <{{D}} [1;1]^^(f1 b) *> const 0.
Proof.
  intros. unfold f1. remember (Nat.iter (S (S (S b))) g 1%nat) as k.
  follow (R21a b ([2;1]^^(S a) *> l)).
  follow (R10c (S b) ([2;1]^^(S a) *> l)).
  follow (R11c (S (S (S b))) (1 >> [2;1]^^a *> l)).
  follow (R22 (S (S (S b))) ([2;1]^^a *> l)).
  follow (R18 (S (S (S b))) 1 (2 >> [2;1]^^a *> l)).
  subst k. finish.
Qed.

(** R30: (12)^n 2 2 1 <D (11)^c 0^inf  -->  2 2 1 <D (11)^(f1^n c) 0^inf *)
Lemma R30 : forall n c l,
  (1 >> 2 >> 2 >> [2;1]^^n *> l) <{{D}} [1;1]^^c *> const 0 -->*
  (1 >> 2 >> 2 >> l) <{{D}} [1;1]^^(Nat.iter n f1 c) *> const 0.
Proof.
  induction n; intros.
  - finish.
  - rewrite iter_succ_r. follow (R21 n c l). follow IHn. finish.
Qed.

(** R23: (11)^3 2 2 1 <D (11)^b 0^inf  -->  (12)^(2b+11) 2 2 1 <D (11) 0^inf *)
Lemma R23 : forall b l,
  (1 >> 2 >> 2 >> [1;1]^^3 *> l) <{{D}} [1;1]^^b *> const 0 -->*
  (1 >> 2 >> 2 >> [2;1]^^(2 * b + 11) *> l) <{{D}} [1;1]^^1 *> const 0.
Proof.
  intros. remember (2 * b + 11) as k.
  follow (R21a b ([1;1]^^3 *> l)).
  follow (R10c (S b) ([1;1]^^3 *> l)).
  follow (R20 (S (S b)) (1 >> 1 >> 1 >> 1 >> 1 >> l)).
  follow (R14c (1 + 2 * S (S b)) (1 >> 1 >> 1 >> 1 >> l)).
  follow (Y (S (S (1 + 2 * S (S b)))) (1 >> 1 >> l)).
  follow (R12c (S (S (S (S (1 + 2 * S (S b)))))) (1 >> 1 >> l)).
  follow (R13c (S (S (S (S (S (1 + 2 * S (S b))))))) (1 >> l)).
  follow (R23z (S (S (S (S (S (S (1 + 2 * S (S b)))))))) l).
  subst k. finish.
Qed.

(** ** Configurations *)

(** DL t a b c = t (11)^a (12)^b 2 2 1 <D (11)^c 0^inf ; t = 0^inf (D) or 0^inf 1 (D1). *)
Definition DL (t : Stream Sym) (a b c : nat) : Q * tape :=
  (1 >> 2 >> 2 >> [2;1]^^b *> [1;1]^^a *> t) <{{D}} [1;1]^^c *> const 0.

Definition G (c : nat) : nat := Nat.iter (2 * c + 11) f1 1%nat.

Lemma DL_b : forall t a b c, DL t a b c -->* DL t a 0 (Nat.iter b f1 c).
Proof. intros. unfold DL. follow (R30 b c ([1;1]^^a *> t)). finish. Qed.

Lemma DL_3 : forall t a c, DL t (3 + a) 0 c -->* DL t a 0 (G c).
Proof.
  intros. unfold DL. simpl lpow at 1. simpl Str_app at 1.
  rewrite lpow_add_app.
  follow (R23 c ([1;1]^^a *> t)).
  follow (R30 (2 * c + 11) 1 ([1;1]^^a *> t)).
  unfold G. finish.
Qed.

Lemma DL_3k : forall k t a c, DL t (3 * k + a) 0 c -->* DL t a 0 (Nat.iter k G c).
Proof.
  induction k; intros.
  - finish.
  - replace (3 * S k + a) with (3 + (3 * k + a)) by lia.
    rewrite iter_succ_r. follow (DL_3 t (3 * k + a) c). apply IHk.
Qed.

(** ** Left-edge rules *)

Lemma ones2 : forall c m (r : Stream sym),
  [1;1]^^(2 * c + m) *> r = [1;1]^^c *> [1;1]^^c *> [1;1]^^m *> r.
Proof. intros. replace (2 * c + m) with (c + (c + m)) by lia. rewrite !lpow_add_app. reflexivity. Qed.

(** R25: D(2,0,c) --> D1(2c+8,3,1) *)
Lemma R25 : forall c, DL (const 0) 2 0 c -->* DL (1 >> const 0) (2 * c + 8) 3 1.
Proof.
  intros. unfold DL. rewrite (ones2 c 8). simpl lpow at 1. simpl Str_app at 1.
  follow (R21a c (1 >> 1 >> 1 >> 1 >> const 0)).
  follow (R10c (S c) (1 >> 1 >> 1 >> 1 >> const 0)).
  follow (R20 (S (S c)) (1 >> 1 >> 1 >> const 0)).
  follow (R14c (1 + 2 * S (S c)) (1 >> 1 >> const 0)).
  follow (Y (S (S (1 + 2 * S (S c)))) (const 0)).
  follow (R12c (S (S (S (S (1 + 2 * S (S c)))))) (const 0)).
  runn 100.
Qed.

(** R26: D1(1,0,c) --> D1(2c+7,3,1) *)
Lemma R26 : forall c, DL (1 >> const 0) 1 0 c -->* DL (1 >> const 0) (2 * c + 7) 3 1.
Proof.
  intros. unfold DL. rewrite (ones2 c 7). simpl lpow at 1. simpl Str_app at 1.
  follow (R21a c (1 >> 1 >> 1 >> const 0)).
  follow (R10c (S c) (1 >> 1 >> 1 >> const 0)).
  follow (R20 (S (S c)) (1 >> 1 >> const 0)).
  follow (R14c (1 + 2 * S (S c)) (1 >> const 0)).
  runn 150.
Qed.

(** R27: D1(0,0,c) --> D(2c+5,3,1) *)
Lemma R27 : forall c, DL (1 >> const 0) 0 0 c -->* DL (const 0) (2 * c + 5) 3 1.
Proof.
  intros. unfold DL. rewrite (ones2 c 5). simpl lpow at 1. simpl Str_app at 1.
  follow (R21a c (1 >> const 0)).
  follow (R10c (S c) (1 >> const 0)).
  follow (R20 (S (S c)) (const 0)).
  runn 150.
Qed.

(** R28: D(1,0,c) reaches the halting configuration C0 with 1^(4c+17) to its right. *)
Lemma R28 : forall c, DL (const 0) 1 0 c -->* C;; const 0 {{0}} [1;1]^^(2 * c + 8) *> 1 >> const 0.
Proof.
  intros. unfold DL. rewrite (ones2 c 8). simpl lpow at 1. simpl Str_app at 1.
  follow (R21a c (1 >> 1 >> const 0)).
  follow (R10c (S c) (1 >> 1 >> const 0)).
  follow (R20 (S (S c)) (1 >> const 0)).
  follow (R14c (1 + 2 * S (S c)) (const 0)).
  runn 150.
Qed.
