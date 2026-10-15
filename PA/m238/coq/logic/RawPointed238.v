(** Original ordinary formula readback of the PA238 fixed-point alias.
    The extra outer parameter fixes slot 2 while the member binder varies
    slot 0. Instantiating that parameter and the chosen point at the same
    term produces the exact canonical pointed schema. This is an actual
    finite ND derivation from the displayed raw schema, not a supplier. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238.
Import ListNotations FullSyntax BinSig ZFSignature.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module RawPointed238.
Module C := Compact238.Compact238.
Notation "G ⊢R phi" :=
  (@prv sig_empty ZF_pred_sig falsity_on class G phi) (at level 61).

Definition fixed_member_slots : nat -> C.set_term :=
  $0 .: $3 .: $4 .: (fun k => $(5 + k)).
Definition fixed_point_slots : nat -> C.set_term :=
  $1 .: $2 .: $3 .: (fun k => $(4 + k)).

Definition fixed_point_body (phi : C.set_form) : C.set_form :=
  (∀ ((C.R $3 $0 → (phi[fixed_member_slots] → C.R $1 $0)) ∧
       (C.R $1 $0 → phi[fixed_member_slots]))) ∧
  (phi[fixed_point_slots] → C.R $0 $1).
Definition fixed_point_ax (phi : C.set_form) : C.set_form := ∀ ∀ ∀ ∃ fixed_point_body phi.

Lemma fixed_point_body_at phi u x :
  (fixed_point_body phi)[up (up (up (x..)))][up (up (u..))][up (x..)] =
  (C.pointed_body phi)[up (up (u..))][up (x..)].
Proof.
  destruct u as [iu|[]], x as [ix|[]].
  unfold fixed_point_body, C.pointed_body.
  cbn [subst_form C.R C.terms2 subst_term Vector.map up scons funcomp].
  repeat rewrite subst_comp.
  repeat first
    [ reflexivity
    | match goal with
      | |- ?body[?sigma] = ?body[?tau] =>
          apply subst_ext; intros [|[|[|k]]];
          cbn [fixed_member_slots fixed_point_slots C.member_slots C.point_slots
               up scons funcomp subst_term]; reflexivity
      end
    | f_equal ].
Qed.

Theorem fixed_point_to_pointed G phi :
  G ⊢R fixed_point_ax phi -> G ⊢R C.pointed_ax phi.
Proof.
  intro Hraw; unfold C.pointed_ax.
  apply AllI_named; intro u; apply AllI_named; intro x.
  unfold fixed_point_ax in Hraw.
  pose proof (AllE x (AllE u (AllE x Hraw))) as H.
  change (G ⊢R ∃ ((fixed_point_body phi)
    [up (up (up (x..)))][up (up (u..))][up (x..)])) in H.
  rewrite fixed_point_body_at in H; exact H.
Qed.

Print Assumptions fixed_point_body_at.
Print Assumptions fixed_point_to_pointed.
End RawPointed238.
