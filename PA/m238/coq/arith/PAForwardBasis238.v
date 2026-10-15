(** Original finite source basis for PA term totality.
    Each universally quantified operation supplier is actually derived in
    S0. Its witnesses are instantiated under a single finite context. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  PairGraph238 AddGraph238 MulGraph238 PAForwardTerms238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 PairGraph238.PairGraph238
  AddGraph238.AddGraph238 MulGraph238.MulGraph238
  PAForwardTerms238.PAForwardTerms238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardBasis238.

Definition represented_zero_totality : set_form :=
  ∃ (ordinal_representative $0 ∧ raw_zero $0).
Definition represented_successor_totality : set_form :=
  ∀ (ordinal_representative $0 →
    ∃ (ordinal_representative $0 ∧ raw_successor $1 $0)).
Definition represented_mul_totality : set_form :=
  ∀ ∀ ((ordinal_representative $1 ∧ ordinal_representative $0) →
    ∃ mul_result $2 $1 $0).
Definition term_totality_basis : set_form :=
  (∀ E $0 $0) ∧
    (represented_zero_totality ∧
      (represented_successor_totality ∧ (closed_add_totality ∧ represented_mul_totality))).

Lemma finite_derivable_conjunction T phi psi :
  derivable T phi -> derivable T psi -> derivable T (phi ∧ psi).
Proof.
  intros [G [HG Hphi]] [D [HD Hpsi]]. exists (G ++ D). split.
  - intros chi Hchi. apply in_app_or in Hchi as [Hchi|Hchi]; [now apply HG|now apply HD].
  - apply CI.
    + eapply Weak; [exact Hphi|]. intros chi Hchi. apply in_or_app. now left.
    + eapply Weak; [exact Hpsi|]. intros chi Hchi. apply in_or_app. now right.
Qed.

Lemma S0_represented_zero_totality : derivable finite_set_S0 represented_zero_totality.
Proof. exact (S0_pa_zero_total (fun k => $k)). Qed.
Lemma S0_represented_successor_totality :
  derivable finite_set_S0 represented_successor_totality.
Proof.
  unfold represented_successor_totality. apply S0_generalize.
  exact (S0_ordinal_successor_exists $0).
Qed.
Lemma S0_represented_mul_totality : derivable finite_set_S0 represented_mul_totality.
Proof.
  unfold represented_mul_totality. apply S0_generalize, S0_generalize.
  exact (S0_mul_total $1 $0).
Qed.

Theorem S0_term_totality_basis : derivable finite_set_S0 term_totality_basis.
Proof.
  unfold term_totality_basis. apply finite_derivable_conjunction.
  - exists [∀ E $0 $0]. split.
    + intros psi [<-|[]]. apply S0_base. apply in_or_app. left. now left.
    + apply Ctx. now left.
  - apply finite_derivable_conjunction; [exact S0_represented_zero_totality|].
    apply finite_derivable_conjunction; [exact S0_represented_successor_totality|].
    apply finite_derivable_conjunction; [exact S0_closed_add_totality|].
    exact S0_represented_mul_totality.
Qed.

Lemma term_basis_zero G :
  G ⊢238 term_totality_basis -> G ⊢238 represented_zero_totality.
Proof. intro H. exact (CE1 (CE2 H)). Qed.

Lemma term_basis_successor G x :
  G ⊢238 term_totality_basis -> G ⊢238 ordinal_representative x ->
  G ⊢238 ∃ (ordinal_representative $0 ∧ raw_successor x`[↑] $0).
Proof.
  destruct x as [ix|[]]. intros HB HX.
  pose proof (CE1 (CE2 (CE2 HB))) as HS. unfold represented_successor_totality in HS.
  pose proof (AllE $ix HS) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HX).
Qed.

Lemma term_basis_addition G x y :
  G ⊢238 term_totality_basis -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative y -> G ⊢238 ∃ add_result x`[↑] y`[↑] $0.
Proof.
  intros HB HX HY. apply (closed_add_totality_instance G x y);
    [exact (CE1 (CE2 (CE2 (CE2 HB))))|exact HX|exact HY].
Qed.

Lemma term_basis_multiplication G x y :
  G ⊢238 term_totality_basis -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative y -> G ⊢238 ∃ mul_result x`[↑] y`[↑] $0.
Proof.
  destruct x as [ix|[]], y as [iy|[]]. intros HB HX HY.
  pose proof (CE2 (CE2 (CE2 (CE2 HB)))) as HM. unfold represented_mul_totality in HM.
  pose proof (AllE $iy (AllE $ix HM)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Print Assumptions finite_derivable_conjunction.
Print Assumptions S0_represented_zero_totality.
Print Assumptions S0_represented_successor_totality.
Print Assumptions S0_represented_mul_totality.
Print Assumptions S0_term_totality_basis.
Print Assumptions term_basis_successor.
Print Assumptions term_basis_addition.
Print Assumptions term_basis_multiplication.
End PAForwardBasis238.
