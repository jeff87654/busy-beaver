(** * BB29: pair alphabet and atomic pair-level rules (BB29/analysis/REPORT.md section 3a). *)

From BB8 Require Import BB29_tm.
From Coq Require Import Lia List.
Import ListNotations.
Set Default Goal Selector "!".

(** Pairs of cells.  [bR p] is the pair in tape order (as on the right of the head);
    [bL p] is the same pair as a left-side stream prefix (nearest cell first). *)
Inductive pr := pO | pC | pX | pZ.

Definition bR (p : pr) : list Sym :=
  match p with pO => [0;1] | pC => [1;1] | pX => [1;0] | pZ => [0;0] end.
Definition bL (p : pr) : list Sym :=
  match p with pO => [1;0] | pC => [1;1] | pX => [0;1] | pZ => [0;0] end.

(** [rs w r]: the word [w] (tape order) followed by [r].
    [ls l w]: [l] followed by the word [w] (tape order), as a left side. *)
Fixpoint rs (w : list pr) (r : side) : side :=
  match w with [] => r | p :: w => bR p *> rs w r end.
Fixpoint ls (l : side) (w : list pr) : side :=
  match w with [] => l | p :: w => ls (bL p *> l) w end.

Lemma rs_app : forall w1 w2 r, rs (w1 ++ w2) r = rs w1 (rs w2 r).
Proof. induction w1; intros; simpl; [reflexivity | rewrite IHw1; reflexivity]. Qed.

Lemma ls_app : forall w1 w2 l, ls l (w1 ++ w2) = ls (ls l w1) w2.
Proof. induction w1; intros; simpl; [reflexivity | rewrite IHw1; reflexivity]. Qed.

Lemma ls_snoc : forall w p l, ls l (w ++ [p]) = bL p *> ls l w.
Proof. intros. rewrite ls_app. reflexivity. Qed.

Lemma rs_Z_const : forall n, rs (repeat pZ n) (const 0) = const 0.
Proof.
  induction n; simpl; [reflexivity|]. rewrite IHn. simpl.
  rewrite <- !const_unfold. reflexivity.
Qed.

Lemma Z_const : bL pZ *> const 0 = const 0.
Proof. simpl. rewrite <- !const_unfold. reflexivity. Qed.

Lemma ls_Z_const : forall n, ls (const 0) (repeat pZ n) = const 0.
Proof. induction n; [reflexivity|]. cbn [repeat ls]. rewrite Z_const. exact IHn. Qed.

(** ** Right-moving states (head on the first cell of the pair) *)

Lemma H_mv : forall p l r, p <> pZ -> l {{qH}}> rs [p] r -->+ ls l [p] {{qH}}> r.
Proof. intros [] l r Hp; [| | | congruence]; simpl; execute. Qed.
Lemma H_Z : forall l r, l {{qH}}> rs [pZ] r -->+ l <{{qY}} rs [pO] r.
Proof. intros; simpl; execute. Qed.

Lemma K_mv : forall p l r, p <> pZ -> l {{qK}}> rs [p] r -->+ ls l [p] {{qK}}> r.
Proof. intros [] l r Hp; [| | | congruence]; simpl; execute. Qed.
Lemma K_Z : forall l r, l {{qK}}> rs [pZ] r -->+ l <{{qAC}} rs [pC] r.
Proof. intros; simpl; execute. Qed.

Lemma N_O : forall l r, l {{qN}}> rs [pO] r -->+ ls l [pO] {{qN}}> r.
Proof. intros; simpl; execute. Qed.
Lemma N_C : forall l r, l {{qN}}> rs [pC] r -->+ ls l [pC] {{qN}}> r.
Proof. intros; simpl; execute. Qed.
Lemma N_Z : forall l r, l {{qN}}> rs [pZ] r -->+ l <{{qAC}} rs [pX] r.
Proof. intros; simpl; execute. Qed.
Lemma N_X : forall l r, l {{qN}}> rs [pX] r -->+ l <{{qR}} rs [pX] r.
Proof. intros; simpl; execute. Qed.

Lemma V_O : forall l r, l {{qV}}> rs [pO] r -->+ ls l [pO] {{qV}}> r.
Proof. intros; simpl; execute. Qed.
Lemma V_C : forall l r, l {{qV}}> rs [pC] r -->+ ls l [pC] {{qV}}> r.
Proof. intros; simpl; execute. Qed.
Lemma V_Z : forall l r, l {{qV}}> rs [pZ] r -->+ ls l [pZ] {{qN}}> r.
Proof. intros; simpl; execute. Qed.
Lemma V_X : forall l r, l {{qV}}> rs [pX] r -->+ l <{{qB}} rs [pZ] r.
Proof. intros; simpl; execute. Qed.

Lemma F_O : forall l r, l {{qF}}> rs [pO] r -->+ ls l [pZ] {{qH}}> r.
Proof. intros; simpl; execute. Qed.
Lemma F_C : forall l r, l {{qF}}> rs [pC] r -->+ ls l [pX] {{qK}}> r.
Proof. intros; simpl; execute. Qed.
Lemma F_X : forall l r, l {{qF}}> rs [pX] r -->+ ls l [pC] {{qN}}> r.
Proof. intros; simpl; execute. Qed.

Lemma LB_O : forall l r, l {{qAA}}> rs [pO] r -->+ ls l [pZ] {{qV}}> r.
Proof. intros; simpl; execute. Qed.
Lemma LB_Z : forall l r, l {{qAA}}> rs [pZ] r -->+ ls l [pZ] {{qV}}> r.
Proof. intros; simpl; execute. Qed.

(** ** Left-moving states (head on the second cell of the pair) *)

Lemma Y_O : forall l r, ls l [pO] <{{qY}} r -->+ l <{{qY}} rs [pO] r.
Proof. intros; simpl; execute. Qed.
Lemma Y_C : forall l r, ls l [pC] <{{qY}} r -->+ l <{{qY}} rs [pC] r.
Proof. intros; simpl; execute. Qed.
Lemma Y_X : forall l r, ls l [pX] <{{qY}} r -->+ l <{{qD}} rs [pX] r.
Proof. intros; simpl; execute. Qed.
Lemma Y_Z : forall l r, ls l [pZ] <{{qY}} r -->+ l <{{qP}} rs [pZ] r.
Proof. intros; simpl; execute. Qed.

Lemma RB_O : forall l r, ls l [pO] <{{qAC}} r -->+ l <{{qY}} rs [pO] r.
Proof. intros; simpl; execute. Qed.
Lemma RB_C : forall l r, ls l [pC] <{{qAC}} r -->+ l <{{qY}} rs [pC] r.
Proof. intros; simpl; execute. Qed.

Lemma D_O : forall l r, ls l [pO] <{{qD}} r -->+ l <{{qD}} rs [pO] r.
Proof. intros; simpl; execute. Qed.
Lemma D_C : forall l r, ls l [pC] <{{qD}} r -->+ l <{{qD}} rs [pC] r.
Proof. intros; simpl; execute. Qed.
Lemma D_Z : forall l r, ls l [pZ] <{{qD}} r -->+ ls l [pO] {{qF}}> r.
Proof. intros; simpl; execute. Qed.
Lemma D_X : forall l r, ls l [pX] <{{qD}} r -->+ ls l [pC] {{qF}}> r.
Proof. intros; simpl; execute. Qed.

Lemma P_O : forall l r, ls l [pO] <{{qP}} r -->+ l <{{qP}} rs [pO] r.
Proof. intros; simpl; execute. Qed.
Lemma P_Z : forall l r, ls l [pZ] <{{qP}} r -->+ ls l [pO] {{qAA}}> r.
Proof. intros; simpl; execute. Qed.

Lemma B_C : forall l r, ls l [pC] <{{qB}} r -->+ l <{{qB}} rs [pZ] r.
Proof. intros; simpl; execute. Qed.
Lemma B_O : forall l r, ls l [pO] <{{qB}} r -->+ l <{{qR}} rs [pX] r.
Proof. intros; simpl; execute. Qed.
Lemma B_Z_halted : forall l r, halted tm (ls l [pZ] <{{qB}} r).
Proof. intros; reflexivity. Qed.

(** Depth scanner: R (depth 0), T (1), \ = qAB (2), S (3). *)
Lemma R_O : forall l r, ls l [pO] <{{qR}} r -->+ ls l [pZ] {{qH}}> r.
Proof. intros; simpl; execute. Qed.
Lemma R_C : forall l r, ls l [pC] <{{qR}} r -->+ l <{{qT}} rs [pC] r.
Proof. intros; simpl; execute. Qed.
Lemma R_Z : forall l r, ls l [pZ] <{{qR}} r -->+ l <{{qP}} rs [pZ] r.
Proof. intros; simpl; execute. Qed.
Lemma T_O : forall l r, ls l [pO] <{{qT}} r -->+ l <{{qR}} rs [pO] r.
Proof. intros; simpl; execute. Qed.
Lemma T_C : forall l r, ls l [pC] <{{qT}} r -->+ l <{{qAB}} rs [pC] r.
Proof. intros; simpl; execute. Qed.
Lemma BS_O : forall l r, ls l [pO] <{{qAB}} r -->+ l <{{qT}} rs [pO] r.
Proof. intros; simpl; execute. Qed.
Lemma BS_C : forall l r, ls l [pC] <{{qAB}} r -->+ l <{{qS}} rs [pC] r.
Proof. intros; simpl; execute. Qed.
Lemma S_O : forall l r, ls l [pO] <{{qS}} r -->+ l <{{qY}} rs [pO] r.
Proof. intros; simpl; execute. Qed.
