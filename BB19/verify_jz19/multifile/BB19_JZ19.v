(** * Jacobzheng's BB(19) champion J19 halts, with sigma > f_(omega+7)^2(5) *)

(** Machine J19 (19 states, A..P, QQ, RR, SS; wiki BB(19) champion, Jacobzheng 2026):
      1RQ1RL_0LI1RC_0LD1LF_0RA1LD_1RB1RE_1LH0LG_1LF1LG_1RE1RM_1LJ1LI_0LK1LI_1RL1RA_0RL0RE_0LN1RM_1LO0LO_1RE1LP_1LN1LN_1LR1RQ_1RZ1LS_0LE0LR

    Anatomy (see investigations/jz19/REPORT.txt).  Lists of 1-blocks separated by single 0s.
    - One sweep engine (states B C D E F G and the A1/L1 split) runs on a list in two modes:
      ENGINE mode (blank left of the list) and MARKER mode (a single 1 left of the list).
      [SW b p W R]: E walks right, head block b, p parked 1-digits, W = what lies left of the two 0s.
    - Engine (level 1):  E0 [x,e,r] -> [x+4,e-1,r],  E1 [x,1^p,e,r] -> [2,1^(p-1),x+3,e-1,r].
    - Outer list (level 2), round boundary [Kbnd]:  R0 [a,e,r] -> [G a, e-1, r] (marker mode, the
      head is expanded into the level-1 list [_,2^k] and run by the engine),
      R1 [a,1^p,e,r] -> [6,1^(p-1),a+1,e-1,r],  EX [a,1^n] -> marker + block a+2n+1.
    - Refill: marker + block M:  M odd -> [2,1^((M+1)/2),2];  M even -> halt with M/2+2 ones.
    - Run: [2,2] -> [12,1] -> M=15 -> [2,1^8,2] ->* [T 8 2, 1^9] -> M = T 8 2 + 19 (even) -> halt.

    Main theorems: [halt], [score_exact], [sigma_lower_bound] (sigma > f_(omega+7)(f_(omega+7) 5)). *)

From BB8 Require Import Individual192.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RQ1RL_0LI1RC_0LD1LF_0RA1LD_1RB1RE_1LH0LG_1LF1LG_1RE1RM_1LJ1LI_0LK1LI_1RL1RA_0RL0RE_0LN1RM_1LO0LO_1RE1LP_1LN1LN_1LR1RQ_1RZ1LS_0LE0LR *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.R, QQ)  | A, 1 => Some (1, TM.R, L)
  | B, 0 => Some (0, TM.L, I)   | B, 1 => Some (1, TM.R, C)
  | C, 0 => Some (0, TM.L, D)   | C, 1 => Some (1, TM.L, F)
  | D, 0 => Some (0, TM.R, A)   | D, 1 => Some (1, TM.L, D)
  | E, 0 => Some (1, TM.R, B)   | E, 1 => Some (1, TM.R, E)
  | F, 0 => Some (1, TM.L, H)   | F, 1 => Some (0, TM.L, G)
  | G, 0 => Some (1, TM.L, F)   | G, 1 => Some (1, TM.L, G)
  | H, 0 => Some (1, TM.R, E)   | H, 1 => Some (1, TM.R, M)
  | I, 0 => Some (1, TM.L, J)   | I, 1 => Some (1, TM.L, I)
  | J, 0 => Some (0, TM.L, K)   | J, 1 => Some (1, TM.L, I)
  | K, 0 => Some (1, TM.R, L)   | K, 1 => Some (1, TM.R, A)
  | L, 0 => Some (0, TM.R, L)   | L, 1 => Some (0, TM.R, E)
  | M, 0 => Some (0, TM.L, N)   | M, 1 => Some (1, TM.R, M)
  | N, 0 => Some (1, TM.L, O)   | N, 1 => Some (0, TM.L, O)
  | O, 0 => Some (1, TM.R, E)   | O, 1 => Some (1, TM.L, P)
  | P, 0 => Some (1, TM.L, N)   | P, 1 => Some (1, TM.L, N)
  | QQ, 0 => Some (1, TM.L, RR) | QQ, 1 => Some (1, TM.R, QQ)
  | RR, 0 => None               | RR, 1 => Some (1, TM.L, SS)
  | SS, 0 => Some (0, TM.L, E)  | SS, 1 => Some (0, TM.L, RR)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** ** Tape algebra *)

Lemma align_lpow : forall (x : Sym) xs ys n,
  (x::xs)^^n *> x >> ys = x >> (xs ++ [x])^^n *> ys.
Proof.
  induction n.
  - reflexivity.
  - simpl. repeat rewrite Str_app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma ones_S_r : forall n (r : side), [1]^^n *> 1 >> r = [1]^^(S n) *> r.
Proof.
  intros n r. change (1 >> r) with ([1] *> r).
  rewrite <- Str_app_assoc, lpow_shift. reflexivity.
Qed.

Lemma ones_S_l : forall n (r : side), 1 >> [1]^^n *> r = [1]^^(S n) *> r.
Proof. reflexivity. Qed.

Lemma ones_add : forall n m (r : side), [1]^^n *> [1]^^m *> r = [1]^^(n + m) *> r.
Proof. intros. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

Ltac norm1 := repeat (rewrite ?ones_S_l, ?ones_S_r, ?ones_add).
Ltac close := apply evstep_refl'; norm1; try reflexivity; lia_refl.

Lemma ones_11 : forall n (r : side), [1; 1]^^n *> r = [1]^^(2 * n) *> r.
Proof.
  induction n; intros r.
  - reflexivity.
  - replace (2 * S n) with (S (S (2 * n))) by lia.
    simpl. rewrite IHn. reflexivity.
Qed.

Lemma ones_111 : forall n (r : side), [1; 1; 1]^^n *> r = [1]^^(3 * n) *> r.
Proof.
  induction n; intros r.
  - reflexivity.
  - replace (3 * S n) with (S (S (S (3 * n)))) by lia.
    simpl. rewrite IHn. reflexivity.
Qed.

Lemma align10 : forall p (Y : side), 1 >> [0; 1]^^p *> Y = [1; 0]^^p *> 1 >> Y.
Proof. intros. symmetry. apply (align_lpow 1 [0] Y p). Qed.

Lemma align01 : forall p (W : side), 0 >> [1; 0]^^p *> 0 >> W = [0; 1]^^p *> 0 >> 0 >> W.
Proof. intros. symmetry. apply (align_lpow 0 [1] (0 >> W) p). Qed.

Lemma pow_cons2 : forall (x y : Sym) n (r : side), [x; y]^^n *> x >> y >> r = x >> y >> [x; y]^^n *> r.
Proof. intros. exact (lpow_shift' _ n [x; y] r). Qed.

Lemma pow_cons3 : forall (x y z : Sym) n (r : side),
  [x; y; z]^^n *> x >> y >> z >> r = x >> y >> z >> [x; y; z]^^n *> r.
Proof. intros. exact (lpow_shift' _ n [x; y; z] r). Qed.

Lemma const0_2 : (const 0 : side) = 0 >> 0 >> const 0.
Proof. rewrite <- !const_unfold. reflexivity. Qed.

(** ** Chains and loops *)

Lemma E_right : forall n l r, l {{E}}> [1]^^n *> r -->* [1]^^n *> l {{E}}> r.
Proof.
  induction n; intros l r.
  - finish.
  - simpl. step. follow IHn. apply evstep_refl'. rewrite ones_S_r. reflexivity.
Qed.

Lemma M_right : forall n l r, l {{M}}> [1]^^n *> r -->* [1]^^n *> l {{M}}> r.
Proof.
  induction n; intros l r.
  - finish.
  - simpl. step. follow IHn. apply evstep_refl'. rewrite ones_S_r. reflexivity.
Qed.

Lemma Q_right : forall n l r, l {{QQ}}> [1]^^n *> r -->* [1]^^n *> l {{QQ}}> r.
Proof.
  induction n; intros l r.
  - finish.
  - simpl. step. follow IHn. apply evstep_refl'. rewrite ones_S_r. reflexivity.
Qed.

Lemma D_left : forall n l r, [1]^^n *> l <{{D}} r -->* l <{{D}} [1]^^n *> r.
Proof.
  induction n; intros l r.
  - finish.
  - simpl. step. follow IHn. apply evstep_refl'. rewrite ones_S_r. reflexivity.
Qed.

Lemma G_left : forall n l r, [1]^^n *> l <{{G}} r -->* l <{{G}} [1]^^n *> r.
Proof.
  induction n; intros l r.
  - finish.
  - simpl. step. follow IHn. apply evstep_refl'. rewrite ones_S_r. reflexivity.
Qed.

Lemma I_left : forall n l r, [1]^^n *> l <{{I}} r -->* l <{{I}} [1]^^n *> r.
Proof.
  induction n; intros l r.
  - finish.
  - simpl. step. follow IHn. apply evstep_refl'. rewrite ones_S_r. reflexivity.
Qed.

(** G0/F1: parked 1-digits move one cell right. *)
Lemma GF_loop : forall n l r, [0; 1]^^n *> l <{{G}} r -->* l <{{G}} [0; 1]^^n *> r.
Proof.
  induction n; intros l r.
  - finish.
  - simpl. step. step. follow IHn. apply evstep_refl'.
    rewrite ?pow_cons2, ?pow_cons3. reflexivity.
Qed.

(** I0/J1: the collapse fills the separators. *)
Lemma IJ_loop : forall n l r, [0; 1]^^n *> l <{{I}} r -->* l <{{I}} [1; 1]^^n *> r.
Proof.
  induction n; intros l r.
  - finish.
  - simpl. step. step. follow IHn. apply evstep_refl'.
    rewrite ?pow_cons2, ?pow_cons3. reflexivity.
Qed.

(** N1/O1/P1: the expansion rewrites 111 as 110 from the right. *)
Lemma NOP_loop : forall n l r, [1; 1; 1]^^n *> l <{{N}} r -->* l <{{N}} [1; 1; 0]^^n *> r.
Proof.
  induction n; intros l r.
  - finish.
  - simpl. step. step. step. follow IHn. apply evstep_refl'.
    rewrite ?pow_cons2, ?pow_cons3. reflexivity.
Qed.

(** R1/S1: the refill keeps every other cell. *)
Lemma RS_loop : forall n l r, [1; 1]^^n *> l <{{RR}} r -->* l <{{RR}} [0; 1]^^n *> r.
Proof.
  induction n; intros l r.
  - finish.
  - simpl. step. step. follow IHn. apply evstep_refl'.
    rewrite ?pow_cons2, ?pow_cons3. reflexivity.
Qed.

(** ** The sweep, generic in the left context W *)

Definition SW (b p : nat) (W : side) (R : side) : Q * tape :=
  ([1]^^b *> 0 >> [1; 0]^^p *> 0 >> W) {{E}}> (0 >> R).

Lemma SW_pass : forall b p W R, SW b p W (1 >> 0 >> R) -->+ SW b (S p) W R.
Proof.
  intros b p W R. unfold SW.
  start_progress.
  follow (D_left b).
  rewrite (ones_S_r b), ones_S_r.
  change ([1]^^(S (S b)) *> 0 >> R) with (1 >> 1 >> [1]^^b *> 0 >> R).
  execute.
  follow (E_right b).
  finish.
Qed.

Lemma SW_dec0 : forall b e W R,
  SW b 0 W ([1]^^(S (S e)) *> 0 >> R) -->+
  W <{{H}} ([1]^^(b + 3) *> 0 >> [1]^^(S e) *> 0 >> R).
Proof.
  intros b e W R. unfold SW.
  start_progress.
  follow (G_left b).
  execute.
  close.
Qed.

Lemma SW_dec1 : forall b p e W R,
  SW b (S p) W ([1]^^(S (S e)) *> 0 >> R) -->+
  W <{{H}} (1 >> 1 >> 0 >> [1; 0]^^p *> [1]^^(b + 2) *> 0 >> [1]^^(S e) *> 0 >> R).
Proof.
  intros b p e W R. unfold SW.
  start_progress.
  follow (G_left b).
  change (0 >> 1 >> 0 >> [1; 0]^^p *> 0 >> W) with (0 >> [1; 0]^^(S p) *> 0 >> W).
  rewrite align01.
  follow (GF_loop (S p)).
  execute.
  apply evstep_refl'. cbn [lpow app Str_app]. rewrite align10. norm1. lia_refl.
Qed.

Lemma SW_end : forall b p W R,
  SW b p W (0 >> R) -->+ W <{{K}} (0 >> [1]^^(b + 2 * p + 2) *> 0 >> R).
Proof.
  intros b p W R. unfold SW.
  start_progress.
  follow (I_left b).
  rewrite align01.
  follow (IJ_loop p).
  execute.
  apply evstep_refl'. rewrite ones_11. norm1. lia_refl.
Qed.

Lemma SW_passes : forall n b p W R,
  SW b p W ([1; 0]^^n *> R) -->* SW b (p + n) W R.
Proof.
  induction n; intros b p W R.
  - rewrite Nat.add_0_r. finish.
  - simpl. eapply evstep_trans; [apply progress_evstep, SW_pass |].
    follow IHn. apply evstep_refl'. f_equal. lia.
Qed.

(** ** Mode boundaries *)

(** Engine mode: H0 restarts the sweep. *)
Lemma H_engine : forall c R,
  const 0 <{{H}} ([1]^^c *> 0 >> R) -->+ SW (S c) 0 (const 0) R.
Proof.
  intros c R. unfold SW.
  start_progress.
  follow (E_right c).
  close.
Qed.

(** Outer round start: K0 writes the marker, L0 L1 split the head. *)
Lemma K_round : forall a R,
  const 0 <{{K}} (0 >> [1]^^(S a) *> 0 >> R) -->+ SW a 0 (1 >> const 0) R.
Proof.
  intros a R. unfold SW.
  start_progress.
  follow (E_right a).
  finish.
Qed.

(** Marker mode: H1 expands the head block (the marker is consumed). *)
Lemma H_marker_aux : forall c R,
  (1 >> const 0) <{{H}} ([1]^^c *> 0 >> R) -->+ ([1]^^(S c) *> const 0) <{{N}} (0 >> R).
Proof.
  intros c R.
  start_progress.
  follow (M_right c).
  execute.
  apply evstep_refl'. rewrite ones_S_r. reflexivity.
Qed.

Lemma EXP0 : forall k R,
  (1 >> const 0) <{{H}} ([1]^^(3 * k + 2) *> 0 >> R) -->+
  SW 4 0 (const 0) ([1; 1; 0]^^k *> 0 >> R).
Proof.
  intros k R.
  eapply progress_evstep_trans; [apply H_marker_aux |].
  replace (S (3 * k + 2)) with (3 * S k) by lia.
  rewrite <- ones_111.
  follow NOP_loop.
  unfold SW. simpl.
  execute.
  all: close.
Qed.

Lemma EXP1 : forall k R,
  (1 >> const 0) <{{H}} ([1]^^(3 * k) *> 0 >> R) -->+
  SW 1 0 (const 0) ([1; 1; 0]^^k *> 0 >> R).
Proof.
  intros k R.
  eapply progress_evstep_trans; [apply H_marker_aux |].
  rewrite <- ones_S_r, <- ones_111.
  follow NOP_loop.
  unfold SW. simpl.
  execute.
  all: close.
Qed.

Lemma EXP2 : forall k R,
  (1 >> const 0) <{{H}} ([1]^^(3 * k + 1) *> 0 >> R) -->+
  SW 4 0 (const 0) ([1; 1; 0]^^k *> 0 >> R).
Proof.
  intros k R.
  eapply progress_evstep_trans; [apply H_marker_aux |].
  replace (S (3 * k + 1)) with (3 * k + 2) by lia.
  rewrite <- ones_add, <- ones_111.
  follow NOP_loop.
  unfold SW. simpl.
  execute.
  all: close.
Qed.

(** Marker mode, K1: the refill. *)
Lemma REFILL_aux : forall M,
  (1 >> const 0) <{{K}} (0 >> [1]^^M *> 0 >> const 0) -->+
  ([1]^^(M + 2) *> const 0) <{{RR}} (1 >> const 0).
Proof.
  intros M.
  start_progress.
  follow (Q_right M).
  execute.
  all: close.
Qed.

Definition c_halt (k : nat) : Q * tape := const 0 <{{RR}} ([0; 1]^^k *> 1 >> const 0).

Lemma REFILL_even : forall k,
  (1 >> const 0) <{{K}} (0 >> [1]^^(2 * k) *> 0 >> const 0) -->+ c_halt (S k).
Proof.
  intros k.
  eapply progress_evstep_trans; [apply REFILL_aux |].
  replace (2 * k + 2) with (2 * S k) by lia.
  rewrite <- ones_11.
  follow RS_loop.
  finish.
Qed.

Lemma REFILL_odd : forall k,
  (1 >> const 0) <{{K}} (0 >> [1]^^(2 * k + 1) *> 0 >> const 0) -->+
  const 0 <{{K}} (0 >> 1 >> 1 >> 0 >> 1 >> [0; 1]^^(S k) *> 1 >> const 0).
Proof.
  intros k.
  eapply progress_evstep_trans; [apply REFILL_aux |].
  replace (2 * k + 1 + 2) with (2 * S k + 1) by lia.
  rewrite <- ones_add, <- ones_11.
  follow RS_loop.
  execute.
Qed.

(** ** Lists on the tape *)

Fixpoint enc (ds : list nat) (Z : side) : side :=
  match ds with
  | [] => 0 >> Z
  | d :: ds' => [1]^^d *> 0 >> enc ds' Z
  end.

Lemma enc_ones : forall p ds Z, enc (repeat 1%nat p ++ ds) Z = [1; 0]^^p *> enc ds Z.
Proof. induction p; intros; simpl. - reflexivity. - rewrite IHp. reflexivity. Qed.

Lemma enc_twos : forall k Z, enc (repeat 2%nat k) Z = [1; 1; 0]^^k *> 0 >> Z.
Proof. induction k; intros; simpl. - reflexivity. - rewrite IHk. reflexivity. Qed.

Lemma repeat_S_r : forall {X} (x : X) n, repeat x (S n) = repeat x n ++ [x].
Proof. induction n; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

Lemma repeat_app_cons : forall {X} (x : X) n l, repeat x n ++ x :: l = x :: repeat x n ++ l.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

(** Engine mode sweep on a level-1 list ds followed by 0 Z. *)
Definition sw (b p : nat) (ds : list nat) (Z : side) : Q * tape := SW b p (const 0) (enc ds Z).

(** Outer round boundary and the marker configuration after exhaustion. *)
Definition Kbnd (ds : list nat) : Q * tape := const 0 <{{K}} (0 >> enc ds (const 0)).
Definition Mk (M : nat) : Q * tape := (1 >> const 0) <{{K}} (0 >> [1]^^M *> 0 >> const 0).

Lemma sw_passes : forall n b p ds Z, sw b p (repeat 1%nat n ++ ds) Z -->* sw b (p + n) ds Z.
Proof. intros. unfold sw. rewrite enc_ones. apply SW_passes. Qed.

Lemma sw_dec0 : forall b e ds Z, sw b 0 (S (S e) :: ds) Z -->+ sw (b + 4) 0 (S e :: ds) Z.
Proof.
  intros. unfold sw. simpl enc.
  eapply progress_trans; [apply SW_dec0 |].
  replace (b + 4)%nat with (S (b + 3)) by lia. apply H_engine.
Qed.

Lemma sw_dec1 : forall b p e ds Z,
  sw b (S p) (S (S e) :: ds) Z -->+ sw 3 0 (repeat 1%nat p ++ S (S b) :: S e :: ds) Z.
Proof.
  intros. unfold sw. simpl enc.
  eapply progress_trans; [apply SW_dec1 |].
  rewrite enc_ones. simpl enc.
  replace (b + 2)%nat with (S (S b)) by lia.
  apply (H_engine 2).
Qed.

Lemma sw_end : forall b p Z,
  sw b p [] Z -->+ const 0 <{{K}} (0 >> [1]^^(b + 2 * p + 2) *> 0 >> Z).
Proof. intros. unfold sw. simpl enc. apply SW_end. Qed.

(** ** Exact hierarchy *)

Local Open Scope nat_scope.

Fixpoint iter {X : Type} (n : nat) (g : X -> X) (x : X) : X :=
  match n with
  | 0 => x
  | S n' => g (iter n' g x)
  end.

Lemma iter_S' : forall {X : Type} n (g : X -> X) x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

Lemma iter_add : forall {X : Type} a b (g : X -> X) x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

(** Engine: clearing a digit at depth p.  U 0 b = b+4, U (p+1) b = U p ^ (b+1) (3). *)
Fixpoint U (p b : nat) : nat :=
  match p with
  | 0 => b + 4
  | S p' => iter (S b) (U p') 3
  end.

Lemma U_0 : forall b, U 0 b = b + 4.
Proof. reflexivity. Qed.
Lemma U_S : forall p b, U (S p) b = iter (S b) (U p) 3.
Proof. reflexivity. Qed.

(** Clearing k leading 2s: Wc k b = U (k-1) (... (U 0 b)). *)
Fixpoint Wc (k b : nat) : nat :=
  match k with
  | 0 => b
  | S k' => U k' (Wc k' b)
  end.

(** G: the outer accumulator after an R0 round (expansion + engine). *)
Definition G (a : nat) : nat :=
  match a mod 3 with
  | 0 => Wc (a / 3) 4 + 2 * (a / 3) + 2
  | 1 => Wc (a / 3 + 1) 1 + 2 * (a / 3 + 1) + 2
  | _ => Wc (a / 3 + 1) 4 + 2 * (a / 3 + 1) + 2
  end.

(** Outer clearing at depth p.  T 0 = G, T (p+1) a = T p ^ a (6). *)
Fixpoint T (p a : nat) : nat :=
  match p with
  | 0 => G a
  | S p' => iter a (T p') 6
  end.

Lemma T_0 : forall a, T 0 a = G a.
Proof. reflexivity. Qed.
Lemma T_S : forall p a, T (S p) a = iter a (T p) 6.
Proof. reflexivity. Qed.

(** ** Engine macro lemmas *)

Lemma eng_clear : forall p e b ds Z,
  sw b 0 (repeat 1 p ++ S e :: ds) Z -->* sw (iter e (U p) b) 0 (repeat 1 p ++ 1 :: ds) Z.
Proof.
  induction p as [| p IHp]; intros e.
  - induction e as [| e IHe]; intros b ds Z.
    + finish.
    + simpl app. eapply evstep_trans; [apply progress_evstep, sw_dec0 |].
      rewrite iter_S'. apply IHe.
  - induction e as [| e IHe]; intros b ds Z.
    + finish.
    + eapply evstep_trans.
      { change (repeat 1 (S p) ++ S (S e) :: ds) with (repeat 1 (S p) ++ S (S e) :: ds).
        apply sw_passes. }
      simpl Nat.add.
      eapply evstep_trans; [apply progress_evstep, sw_dec1 |].
      eapply evstep_trans; [apply (IHp (S b) 3 (S e :: ds) Z) |].
      rewrite <- U_S.
      replace (repeat 1 p ++ 1 :: S e :: ds) with (repeat 1 (S p) ++ S e :: ds).
      2:{ rewrite repeat_app_cons. reflexivity. }
      rewrite iter_S'. apply IHe.
Qed.

Lemma eng_twos : forall k b rest Z,
  sw b 0 (repeat 2 k ++ rest) Z -->* sw (Wc k b) 0 (repeat 1 k ++ rest) Z.
Proof.
  induction k as [| k IHk]; intros b rest Z.
  - finish.
  - rewrite repeat_S_r, <- app_assoc. simpl app.
    eapply evstep_trans; [apply IHk |].
    eapply evstep_trans; [apply (eng_clear k 1) |].
    simpl Wc. simpl iter.
    rewrite repeat_app_cons. finish.
Qed.

Lemma eng_run : forall k b Z,
  sw b 0 (repeat 2 k) Z -->+ (const 0 <{{K}} (0 >> [1]^^(Wc k b + 2 * k + 2) *> 0 >> Z))%sym.
Proof.
  intros k b Z.
  pose proof (eng_twos k b [] Z) as H1. rewrite !app_nil_r in H1.
  eapply evstep_progress_trans; [exact H1 |].
  pose proof (sw_passes k (Wc k b) 0 [] Z) as H2. rewrite app_nil_r in H2.
  eapply evstep_progress_trans; [exact H2 |].
  apply sw_end.
Qed.

(** ** Outer rounds *)

Lemma R0_tail : forall b k R',
  SW b 0 (const 0)%sym ([1; 1; 0]^^k *> 0 >> R')%sym -->+
  (const 0 <{{K}} (0 >> [1]^^(Wc k b + 2 * k + 2) *> 0 >> R'))%sym.
Proof. intros. rewrite <- enc_twos. apply eng_run. Qed.

Lemma K_R0 : forall a e os, Kbnd (S a :: S (S e) :: os) -->+ Kbnd (G (S a) :: S e :: os).
Proof.
  intros a e os. unfold Kbnd. cbn [enc].
  eapply progress_trans; [apply K_round |].
  eapply progress_trans; [apply SW_dec0 |].
  change ([1]^^(S e) *> 0 >> enc os (const 0))%sym with (enc (S e :: os) (const 0)%sym).
  generalize (enc (S e :: os) (const 0)%sym). intros R'.
  assert (Hd : S a = 3 * (S a / 3) + S a mod 3) by (apply Nat.div_mod; lia).
  assert (Hlt : S a mod 3 < 3) by (apply Nat.mod_upper_bound; lia).
  unfold G.
  destruct (S a mod 3) as [| [| [| r]]] eqn:Hm.
  - replace (a + 3) with (3 * (S a / 3) + 2) by lia.
    eapply progress_trans; [apply EXP0 |]. apply R0_tail.
  - replace (a + 3) with (3 * (S a / 3 + 1)) by lia.
    eapply progress_trans; [apply EXP1 |]. apply R0_tail.
  - replace (a + 3) with (3 * (S a / 3 + 1) + 1) by lia.
    eapply progress_trans; [apply EXP2 |]. apply R0_tail.
  - lia.
Qed.

Lemma K_R1 : forall a p e os,
  Kbnd (S a :: repeat 1 (S p) ++ S (S e) :: os) -->+ Kbnd (6 :: repeat 1 p ++ S (S a) :: S e :: os).
Proof.
  intros a p e os. unfold Kbnd. cbn [enc].
  eapply progress_trans; [apply K_round |].
  rewrite enc_ones.
  eapply evstep_progress_trans; [apply SW_passes |].
  simpl Nat.add. cbn [enc].
  eapply progress_trans; [apply SW_dec1 |].
  replace (1 >> 1 >> 0 >> [1; 0]^^p *> [1]^^(a + 2) *> 0 >> [1]^^(S e) *> 0 >> enc os (const 0))%sym
    with ([1]^^(3 * 0 + 2) *> 0 >> enc (repeat 1%nat p ++ S (S a) :: S e :: os) (const 0)%sym)%sym.
  2:{ rewrite enc_ones. cbn [enc]. replace (a + 2) with (S (S a)) by lia. reflexivity. }
  eapply progress_trans; [apply EXP0 |].
  apply (R0_tail 4 0).
Qed.

Lemma K_EX : forall a n, Kbnd (S a :: repeat 1 n) -->+ Mk (a + 2 * n + 2).
Proof.
  intros a n. unfold Kbnd, Mk. cbn [enc].
  eapply progress_trans; [apply K_round |].
  rewrite <- (app_nil_r (repeat 1 n)), enc_ones. cbn [enc].
  eapply evstep_progress_trans; [apply SW_passes |].
  apply SW_end.
Qed.

Lemma Mk_odd : forall k, Mk (2 * k + 1) -->+ Kbnd (2 :: repeat 1 (S k) ++ [2]).
Proof.
  intros k. unfold Mk, Kbnd.
  eapply progress_evstep_trans; [apply REFILL_odd |].
  apply evstep_refl'. cbn [enc]. rewrite enc_ones. cbn [enc lpow app Str_app].
  rewrite align10. cbn [lpow app Str_app]. rewrite <- !const_unfold. reflexivity.
Qed.

Lemma Mk_even : forall k, Mk (2 * k) -->+ c_halt (S k).
Proof. intros k. apply REFILL_even. Qed.

(** ** Positivity, parity *)

Lemma iter_U0 : forall n x, iter n (U 0) x = x + 4 * n.
Proof. induction n; intros; simpl. - lia. - rewrite IHn. lia. Qed.

Lemma U_ge : forall p b, b + 4 <= U p b.
Proof.
  induction p; intros b.
  - simpl. lia.
  - rewrite U_S. assert (forall n x, x + 4 * n <= iter n (U p) x).
    { induction n; intros x; simpl. - lia. - specialize (IHp (iter n (U p) x)). specialize (IHn x). lia. }
    specialize (H (S b) 3). lia.
Qed.

Lemma Wc_ge : forall k b, b + 4 * k <= Wc k b.
Proof. induction k; intros b; simpl. - lia. - specialize (IHk b). pose proof (U_ge k (Wc k b)). lia. Qed.

Lemma U_mod : forall p b, exists j, U (S p) b = 4 * j + 3.
Proof.
  induction p; intros b.
  - rewrite U_S, iter_U0. exists (S b). lia.
  - rewrite U_S. simpl iter. apply IHp.
Qed.

Lemma Wc_mod : forall k b, exists j, Wc (S (S k)) b = 4 * j + 3.
Proof. intros. simpl Wc. apply U_mod. Qed.

Lemma G_ge : forall a, 6 <= G a.
Proof.
  intros a. unfold G.
  destruct (a mod 3) as [| [| r]].
  - pose proof (Wc_ge (a / 3) 4). lia.
  - pose proof (Wc_ge (a / 3 + 1) 1). lia.
  - pose proof (Wc_ge (a / 3 + 1) 4). lia.
Qed.

Lemma G_odd : forall a, 4 <= a -> exists j, G a = 2 * j + 1.
Proof.
  intros a Ha. unfold G.
  assert (Hd : a = 3 * (a / 3) + a mod 3) by (apply Nat.div_mod; lia).
  assert (Hlt : a mod 3 < 3) by (apply Nat.mod_upper_bound; lia).
  destruct (a mod 3) as [| [| [| r]]] eqn:Hm.
  - destruct (a / 3) as [| [| q]] eqn:Hq; [lia | lia |].
    destruct (Wc_mod q 4) as [j Hj]. rewrite Hj. exists (2 * j + q + 4). lia.
  - destruct (a / 3) as [| q] eqn:Hq; [lia |].
    replace (S q + 1) with (S (S q)) by lia. destruct (Wc_mod q 1) as [j Hj]. rewrite Hj.
    exists (2 * j + q + 4). lia.
  - destruct (a / 3) as [| q] eqn:Hq; [lia |].
    replace (S q + 1) with (S (S q)) by lia. destruct (Wc_mod q 4) as [j Hj]. rewrite Hj.
    exists (2 * j + q + 4). lia.
  - lia.
Qed.

Lemma T_pos : forall p a, 1 <= T p a.
Proof.
  induction p; intros a.
  - pose proof (G_ge a). simpl. lia.
  - rewrite T_S. destruct a; simpl. + lia. + apply IHp.
Qed.

Lemma iter_G_ge : forall n, 6 <= iter n G 6.
Proof. induction n; simpl. - lia. - apply G_ge. Qed.

Lemma iter_T_pos : forall p n, 1 <= iter n (T p) 6.
Proof.
  intros p [| n]; [simpl; lia |].
  change (iter (S n) (T p) 6) with (T p (iter n (T p) 6)). apply T_pos.
Qed.

Lemma T_odd : forall p a, 1 <= a -> exists j, T (S p) a = 2 * j + 1.
Proof.
  induction p; intros a Ha; destruct a as [| a]; try lia.
  - rewrite T_S. change (iter (S a) (T 0) 6) with (T 0 (iter a (T 0) 6)). rewrite T_0.
    apply G_odd. eapply Nat.le_trans; [| apply iter_G_ge]. lia.
  - rewrite T_S. change (iter (S a) (T (S p)) 6) with (T (S p) (iter a (T (S p)) 6)).
    apply IHp. apply iter_T_pos.
Qed.

(** ** Outer clearing *)

Lemma outer_clear : forall p e a os, 1 <= a ->
  Kbnd (a :: repeat 1 p ++ S e :: os) -->* Kbnd (iter e (T p) a :: repeat 1 p ++ 1 :: os).
Proof.
  induction p as [| p IHp]; intros e.
  - induction e as [| e IHe]; intros a os Ha.
    + finish.
    + destruct a as [| a]; [lia |]. simpl app.
      eapply evstep_trans; [apply progress_evstep, K_R0 |].
      rewrite iter_S'. apply IHe. apply T_pos.
  - induction e as [| e IHe]; intros a os Ha.
    + finish.
    + destruct a as [| a]; [lia |].
      eapply evstep_trans; [apply progress_evstep, K_R1 |].
      eapply evstep_trans; [apply (IHp (S a) 6 (S e :: os)); lia |].
      rewrite <- T_S.
      replace (repeat 1 p ++ 1 :: S e :: os) with (repeat 1 (S p) ++ S e :: os)
        by (rewrite repeat_app_cons; reflexivity).
      rewrite iter_S'. apply IHe. apply T_pos.
Qed.

(** ** The run from the blank tape *)

Lemma boot : c0 -->* Kbnd [2; 2].
Proof. unfold Kbnd. cbn [enc lpow app Str_app]. execute. Qed.

Lemma G_2 : G 2 = 12.
Proof. reflexivity. Qed.

Definition Mfin : nat := T 8 2 + 19.

Lemma run_to_Mk : c0 -->* Mk (T 8 2 - 1 + 2 * 9 + 2).
Proof.
  eapply evstep_trans; [apply boot |].
  eapply evstep_trans; [apply progress_evstep, (K_R0 1 0 []) |].
  rewrite G_2.
  eapply evstep_trans; [apply progress_evstep, (K_EX 11 1) |].
  change (11 + 2 * 1 + 2) with (2 * 7 + 1).
  eapply evstep_trans; [apply progress_evstep, Mk_odd |].
  eapply evstep_trans; [apply (outer_clear 8 1 2 []); lia |].
  change (iter 1 (T 8) 2) with (T 8 2).
  change (repeat 1 8 ++ [1]) with (repeat 1 9).
  pose proof (T_pos 8 2) as Hp.
  destruct (T 8 2) as [| t] eqn:Ht; [lia |].
  replace (S t - 1) with t by lia.
  apply progress_evstep, K_EX.
Qed.

Lemma run_to_halt : exists k, c0 -->* c_halt (S k) /\ 2 * k = T 8 2 + 19.
Proof.
  destruct (T_odd 7 2 ltac:(lia)) as [j Hj].
  exists (j + 10).
  split; [| lia].
  eapply evstep_trans; [apply run_to_Mk |].
  replace (T 8 2 - 1 + 2 * 9 + 2) with (2 * (j + 10)) by lia.
  apply progress_evstep, Mk_even.
Qed.

Lemma c_halt_halted : forall k, halted tm (c_halt k).
Proof. reflexivity. Qed.

Theorem halt : halts tm c0.
Proof.
  destruct run_to_halt as [k [Hrun _]].
  destruct (with_counter Hrun) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts, c_halt_halted.
Qed.

(** ** Score *)

Definition sym_val (s : Sym) : nat :=
  match s with
  | S0 => 0
  | S1 => 1
  end.

Fixpoint count1 (xs : list Sym) : nat :=
  match xs with
  | [] => 0
  | x :: t => sym_val x + count1 t
  end.

(** [ones c N]: the tape of c is a finite word padded with 0s and holds exactly N ones. *)
Definition ones (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl. - reflexivity. - rewrite IHxs. lia. Qed.

Lemma count1_pow : forall xs n, count1 (xs ^^ n) = n * count1 xs.
Proof. induction n; simpl. - reflexivity. - rewrite count1_app, IHn. lia. Qed.

Lemma ones_c_halt : forall n, ones (c_halt n) (n + 1).
Proof.
  intros n.
  exists RR, (@nil Sym), ([S0; S1]^^n ++ [S1]), S0.
  split.
  - unfold c_halt. rewrite Str_app_assoc. reflexivity.
  - rewrite count1_app, count1_pow. cbn [count1 sym_val]. lia.
Qed.

(** Exact score: sigma = (T 8 2 + 23) / 2, where T 8 2 is odd. *)
Theorem score_exact :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ 2 * N = T 8 2 + 23.
Proof.
  destruct run_to_halt as [k [Hrun Hk]].
  exists (c_halt (S k)), (S k + 1).
  split; [exact Hrun |].
  split; [apply c_halt_halted |].
  split; [apply ones_c_halt |].
  lia.
Qed.

(** ** Fast-growing hierarchy and the lower bound *)

Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | 0 => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.

(** f_(omega+k); the number of omega-layers is data, so it is a recursion on k. *)
Fixpoint f_wk (k : nat) : nat -> nat :=
  match k with
  | 0 => f_omega
  | S k' => fun n => iter n (f_wk k') n
  end.

Lemma f_S : forall k n, f (S k) n = iter n (f k) n.
Proof. reflexivity. Qed.
Lemma f_wk_S : forall k n, f_wk (S k) n = iter n (f_wk k) n.
Proof. reflexivity. Qed.

(** Generic iteration facts. *)
Definition mono (F : nat -> nat) := forall x y, x <= y -> F x <= F y.

Lemma iter_mono_x : forall F, mono F -> forall n x y, x <= y -> iter n F x <= iter n F y.
Proof. intros F HF. induction n; intros x y Hxy; simpl. - exact Hxy. - apply HF, IHn, Hxy. Qed.

Lemma iter_ge : forall F, (forall x, x <= F x) -> forall n x, x <= iter n F x.
Proof.
  intros F HF. induction n; intros x; simpl. - lia.
  - specialize (IHn x). specialize (HF (iter n F x)). lia.
Qed.

Lemma iter_mono_n : forall F, (forall x, x <= F x) -> forall n m x, n <= m -> iter n F x <= iter m F x.
Proof.
  intros F HF n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite iter_add. apply iter_ge, HF.
Qed.

(** Values starting from 1 grow by at least one per step. *)
Lemma iter_from1 : forall F, (forall x, 1 <= x -> x + 1 <= F x) -> forall n, n + 1 <= iter n F 1.
Proof.
  intros F HF. induction n; simpl. - lia. - specialize (HF (iter n F 1) ltac:(lia)). lia.
Qed.

(** Galois form of a conjugation:  d z <= y  ->  d F(z) <= g(y), iterated. *)
Lemma conj_iter : forall d F g, (forall z y, d * z <= y -> d * F z <= g y) ->
  forall n z y, d * z <= y -> d * iter n F z <= iter n g y.
Proof. intros d F g H. induction n; intros z y Hzy; simpl. - exact Hzy. - apply H, IHn, Hzy. Qed.

(** Absorbing the base: F^z(z) <= F^y(1) for y >= 2z. *)
Lemma base_absorb : forall F, mono F -> (forall x, 1 <= x -> x + 1 <= F x) ->
  forall z y, 2 * z <= y -> iter z F z <= iter y F 1.
Proof.
  intros F HF Hg z y Hzy.
  replace y with (z + (y - z)) by lia. rewrite iter_add.
  apply iter_mono_x; [exact HF |].
  pose proof (iter_from1 F Hg (y - z)). lia.
Qed.

(** FGH basics. *)
Lemma f_ge : forall k n, n <= f k n.
Proof.
  induction k; intros n.
  - simpl. lia.
  - rewrite f_S. apply (iter_ge (f k) IHk n n).
Qed.

Lemma f_mono : forall k, mono (f k).
Proof.
  induction k; intros x y Hxy.
  - simpl. lia.
  - rewrite !f_S.
    eapply Nat.le_trans; [apply iter_mono_x; [exact IHk | exact Hxy] |].
    apply iter_mono_n; [apply f_ge | exact Hxy].
Qed.

Lemma f_grow : forall k x, 1 <= x -> x + 1 <= f k x.
Proof.
  induction k; intros x Hx.
  - simpl. lia.
  - rewrite f_S. destruct x as [| x]; [lia |]. simpl iter.
    pose proof (iter_ge (f k) (f_ge k) x (S x)).
    pose proof (IHk (iter x (f k) (S x)) ltac:(lia)). lia.
Qed.

Lemma f_level : forall k x, 1 <= x -> f k x <= f (S k) x.
Proof.
  intros k x Hx. rewrite f_S. destruct x as [| x]; [lia |]. simpl iter.
  apply f_mono. apply iter_ge, f_ge.
Qed.

Lemma f_level_le : forall k j x, k <= j -> 1 <= x -> f k x <= f j x.
Proof.
  intros k j x Hkj Hx. induction Hkj.
  - lia.
  - eapply Nat.le_trans; [exact IHHkj | apply f_level, Hx].
Qed.

Lemma iter_succ : forall m y, iter m S y = y + m.
Proof. induction m; intros; simpl. - lia. - rewrite IHm. lia. Qed.

Lemma f1_dbl : forall k x, 1 <= k -> 2 * x <= f k x.
Proof.
  intros k x Hk. destruct k as [| k]; [lia |].
  induction k.
  - rewrite f_S. simpl f. rewrite iter_succ. lia.
  - destruct x as [| x]; [lia |].
    pose proof (f_level (S k) (S x) ltac:(lia)). lia.
Qed.

Lemma f_double : forall k n, 2 <= k -> 2 * f k n <= f k (S n).
Proof.
  intros k n Hk. destruct k as [| [| k]]; [lia | lia |].
  change (f (S (S k)) n) with (iter n (f (S k)) n).
  change (f (S (S k)) (S n)) with (f (S k) (iter n (f (S k)) (S n))).
  pose proof (f1_dbl (S k) (iter n (f (S k)) (S n)) ltac:(lia)).
  pose proof (iter_mono_x (f (S k)) (f_mono (S k)) n n (S n) ltac:(lia)). lia.
Qed.

Lemma f_omega_mono : mono f_omega.
Proof.
  intros x y Hxy. unfold f_omega.
  destruct x as [| x].
  - destruct y as [| y]; [lia |]. simpl f at 1. pose proof (f_ge (S y) (S y)). lia.
  - eapply Nat.le_trans; [apply f_level_le; [exact Hxy | lia] |]. apply f_mono, Hxy.
Qed.

Lemma f_omega_grow : forall x, x + 1 <= f_omega x.
Proof.
  intros x. unfold f_omega. destruct x as [| x]; [simpl; lia |].
  pose proof (f_level_le 0 (S x) (S x) ltac:(lia) ltac:(lia)) as H. simpl f in H at 1. lia.
Qed.

Lemma f_wk_mono_grow : forall k, mono (f_wk k) /\ (forall x, 1 <= x -> x + 1 <= f_wk k x).
Proof.
  induction k as [| k [IHm IHg]].
  - split; [exact f_omega_mono | intros; apply f_omega_grow].
  - assert (Hge : forall n y, 1 <= y -> y <= iter n (f_wk k) y).
    { induction n; intros y Hy; simpl. - lia.
      - specialize (IHn y Hy). specialize (IHg (iter n (f_wk k) y) ltac:(lia)). lia. }
    split.
    + intros x y Hxy. rewrite !f_wk_S.
      destruct x as [| x]; [simpl; lia |].
      eapply Nat.le_trans; [apply iter_mono_x; [exact IHm | exact Hxy] |].
      assert (E : iter y (f_wk k) y = iter (y - S x) (f_wk k) (iter (S x) (f_wk k) y))
        by (rewrite <- iter_add; f_equal; lia).
      rewrite E. apply Hge. pose proof (Hge (S x) y ltac:(lia)). lia.
    + intros x Hx. rewrite f_wk_S. destruct x as [| x]; [lia |]. simpl iter.
      specialize (Hge x (S x) ltac:(lia)). specialize (IHg (iter x (f_wk k) (S x)) ltac:(lia)). lia.
Qed.

(** Engine:  2 z <= y  ->  2 f_p(z) <= U p y. *)
Lemma U_dom : forall p z y, 2 * z <= y -> 2 * f p z <= U p y.
Proof.
  induction p as [| p IHp]; intros z y Hzy.
  - simpl. lia.
  - rewrite f_S, U_S.
    pose proof (conj_iter 2 (f p) (U p) IHp (S y) 1 3 ltac:(lia)) as H.
    pose proof (base_absorb (f p) (f_mono p) (f_grow p) z (S y) ltac:(lia)). lia.
Qed.

Lemma Wc_dom : forall k b, 1 <= b -> 2 * f k (2 * k) <= Wc (S k) b.
Proof.
  intros k b Hb. simpl Wc. apply U_dom. pose proof (Wc_ge k b). lia.
Qed.

(** One R0 round:  6 z <= y  ->  6 f_omega(z) <= G y. *)
Lemma G_dom : forall z y, 6 * z <= y -> 6 * f_omega z <= G y.
Proof.
  intros z y Hzy.
  destruct z as [| z].
  - unfold f_omega. simpl f. pose proof (G_ge y). lia.
  - assert (Hd : y = 3 * (y / 3) + y mod 3) by (apply Nat.div_mod; lia).
    assert (Hlt : y mod 3 < 3) by (apply Nat.mod_upper_bound; lia).
    assert (HK : exists K b0, 2 * S z <= K /\ 1 <= b0 /\ Wc K b0 + 2 * K + 2 <= G y).
    { unfold G. destruct (y mod 3) as [| [| [| r]]] eqn:Hm.
      - exists (y / 3), 4. lia.
      - exists (y / 3 + 1), 1. lia.
      - exists (y / 3 + 1), 4. lia.
      - lia. }
    destruct HK as [K [b0 [HK [Hb0 HG]]]].
    destruct K as [| K]; [lia |].
    pose proof (Wc_ge (S K) b0) as Hw.
    destruct z as [| z].
    + unfold f_omega. simpl f. lia.
    + pose proof (Wc_dom K b0 Hb0) as Hdom.
      assert (H1 : f (S (S z)) (2 * K) <= f K (2 * K)) by (apply f_level_le; lia).
      assert (H2 : f (S (S z)) (S (S (S (S z)))) <= f (S (S z)) (2 * K)) by (apply f_mono; lia).
      pose proof (f_double (S (S z)) (S (S (S z))) ltac:(lia)) as H3.
      pose proof (f_double (S (S z)) (S (S z)) ltac:(lia)) as H4.
      unfold f_omega. lia.
Qed.

(** Outer clearing:  6 z <= y  ->  6 f_(omega+p)(z) <= T p y. *)
Lemma T_dom : forall p z y, 6 * z <= y -> 6 * f_wk p z <= T p y.
Proof.
  induction p as [| p IHp]; intros z y Hzy.
  - apply G_dom, Hzy.
  - rewrite f_wk_S, T_S.
    destruct (f_wk_mono_grow p) as [Hm Hg].
    pose proof (conj_iter 6 (f_wk p) (T p) IHp y 1 6 ltac:(lia)) as H.
    pose proof (base_absorb (f_wk p) Hm Hg z y ltac:(lia)). lia.
Qed.

Lemma T82_dom : 6 * f_wk 7 (f_wk 7 5) <= T 8 2.
Proof.
  destruct (f_wk_mono_grow 5) as [_ Hg5].
  assert (H6 : 6 * 5 <= T 6 6).
  { rewrite T_S. pose proof (conj_iter 6 (f_wk 5) (T 5) (T_dom 5) 6 1 6 ltac:(lia)) as H.
    pose proof (iter_from1 (f_wk 5) Hg5 6). lia. }
  assert (H7 : 6 * f_wk 7 5 <= T 7 6).
  { rewrite T_S, iter_S', f_wk_S.
    apply (conj_iter 6 (f_wk 6) (T 6) (T_dom 6) 5 5 (T 6 6) H6). }
  rewrite T_S. change (iter 2 (T 7) 6) with (T 7 (T 7 6)).
  apply T_dom, H7.
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_wk 7 (f_wk 7 5) < N.
Proof.
  destruct score_exact as [c [N [Hrun [Hh [Hones HN]]]]].
  exists c, N. split; [exact Hrun |]. split; [exact Hh |]. split; [exact Hones |].
  pose proof T82_dom. lia.
Qed.

Print Assumptions halt.
Print Assumptions score_exact.
Print Assumptions sigma_lower_bound.
