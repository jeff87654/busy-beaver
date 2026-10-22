(** * X base: machine, notations, normalization (bb9_f3_coq; adapted from C04's dev/Base.v).

    X is an auxiliary 11-state machine, C04 with its E0 = 1LH replaced by an inspection of the cell left of H:
      C04 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF
      X   = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LJ0LC_0RG1LD_0LH1LH_1RI---_0RI0RF_0LK---_0RC1RH
    After E0 (E reads 0 at y, writes 1, moves to x = y - 1): C04 is in H at x.  X is in J at x; if x reads 1 X halts
    (as C04 does in H); if x reads 0, J0 = 0LK moves to x - 1, and K1 = 1RH puts X in H at x with the same tape as
    C04 (3 X steps for C04's one E0 step), while K0 = 0RC is the new behaviour (f3_0RC's I0 = 0RC).
    f3_0RC = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF is simulated by X (Sim.v).

    The tactic [step] below is redefined: one [step] is one step of C04, i.e. three X steps for E0 followed by J0
    and K1, so the generated C04 proof scripts ([do n step]) are reused unchanged. *)

From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine X: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LJ0LC_0RG1LD_0LH1LH_1RI---_0RI0RF_0LK---_0RC1RH *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (0, R, A)
  | B, 0 => Some (1, L, C)  | B, 1 => Some (1, L, F)
  | C, 0 => Some (1, R, D)  | C, 1 => Some (0, L, B)
  | D, 0 => Some (1, R, A)  | D, 1 => Some (1, L, E)
  | E, 0 => Some (1, L, J)  | E, 1 => Some (0, L, C)
  | F, 0 => Some (0, R, G)  | F, 1 => Some (1, L, D)
  | G, 0 => Some (0, L, H)  | G, 1 => Some (1, L, H)
  | H, 0 => Some (1, R, I)  | H, 1 => None
  | I, 0 => Some (0, R, I)  | I, 1 => Some (0, R, F)
  | J, 0 => Some (0, L, K)  | J, 1 => None
  | K, 0 => Some (0, R, C)  | K, 1 => Some (1, R, H)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** ** One C04 step *)
Ltac step1 := (eapply evstep_step || eapply progress_step); [prove_step | simpl_tape].
Ltac cur_cfg := lazymatch goal with |- ?c -[ _ ]->* _ => c | |- ?c -[ _ ]->+ _ => c end.
(** the state and the (simplified) symbol under the head *)
Ltac cur_qs := let c := cur_cfg in
  match c with
  | (?q, (?l, ?s, ?r)) => let s' := eval simpl in s in constr:((q, s'))
  | _ => constr:(tt)
  end.
Ltac step :=
  let qs := cur_qs in
  lazymatch qs with
  | (E, S0) => step1;
      let qs' := cur_qs in
      lazymatch qs' with
      | (J, S0) => step1; step1
      | _ => idtac
      end
  | (J, S0) => step1; step1; step
  | _ => step1
  end.

(** ** Tape normalization (as in the hand-written proofs, e.g. BB8_048631_1RB0RG.v) *)

Lemma align_lpow : forall (x : Sym) xs ys n,
  (x::xs)^^n *> x >> ys = x >> (xs ++ [x])^^n *> ys.
Proof.
  induction n.
  - reflexivity.
  - simpl. repeat rewrite Str_app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma align_lpow_const : forall (x : Sym) xs n,
  (x::xs)^^n *> const x = x >> (xs ++ [x])^^n *> const x.
Proof. intros. rewrite const_unfold at 1. apply align_lpow. Qed.

Ltac align_tape := repeat ((rewrite align_lpow || rewrite align_lpow_const); simpl app).
Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
(** Adjacent powers of the same block, in either order (crossing a run pushes its powers in reverse order). *)
Lemma lpow_merge : forall (xs : list Sym) n m Y, xs^^n *> xs^^m *> Y = xs^^(n + m) *> Y.
Proof. intros. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

(** Blank cells in front of the blank tail. *)
Lemma zero_const : (0 >> const 0 : side) = const 0.
Proof. symmetry. apply const_unfold. Qed.

Ltac finish_norm := apply evstep_refl'; norm_nat; align_tape; repeat rewrite lpow_merge; repeat rewrite zero_const;
  try reflexivity; lia_refl.

Lemma lpow_snoc : forall (xs : list Sym) n Y, xs^^(S n) *> Y = xs^^n *> xs *> Y.
Proof. intros. simpl. rewrite <- lpow_shift. apply Str_app_assoc. Qed.
