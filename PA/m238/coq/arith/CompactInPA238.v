(* Original compact-in-PA interpretation work. This leaf gives arithmetic
   atom syntax and finite natural-deduction transport. Arithmetic producer
   goals below are definitions of open obligations, not assumed Coq axioms.
   It does not assert the compact-to-ordinary-PA inconsistency implication. *)

From Coq Require Import Arith Lia List Vector.
From Undecidability.Shared Require Import Dec.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
From Undecidability.FOL.Sets Require Import Signatures.
From Undecidability.FOL.Syntax Require Import BinSig.
From P238.arith Require Import PAeq238 Compact238 PAOrder238 PAEqCongruence238.

Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations Vector.VectorNotations FullSyntax PA238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Module CompactInPA238.

(* The Goedel beta remainder relation uses only the existing PA signature.
   No exponentiation symbol is added. *)
Definition beta_modulus (c i : pa_term) : pa_term := σ ((σ i) ⊗ c).
Definition beta (b c i r : pa_term) : pa_form :=
  ∃ ((b`[↑] == ($0 ⊗ beta_modulus c`[↑] i`[↑]) ⊕ r`[↑]) ∧
     (r`[↑] ⧀ beta_modulus c`[↑] i`[↑])).

(* A beta-coded finite sequence starts at 1 and doubles at every position
   below n. Endpoint p represents 2^n. Under the first two binders $0=c,
   $1=b; under the step's final binders $0=s,$1=r,$2=i,$3=c,$4=b. *)
Definition pow2 (n p : pa_term) : pa_form :=
  ∃ ∃
    (beta $1 $0 zero (σ zero) ∧
     (beta $1 $0 n`[↑]`[↑] p`[↑]`[↑] ∧
      ∀ (($0 ⧀ n`[↑]`[↑]`[↑]) →
         ∃ ∃ (beta $4 $3 $2 $1 ∧
               (beta $4 $3 (σ $2) $0 ∧ ($0 == $1 ⊕ $1)))))).

(* The x-th bit of a is one precisely when a=(2*p)*q+p+r, r<p,
   with p=2^x. The later position-bound producer must derive x<a from this
   formula; hereditary descent and IR are not included as defining guards. *)
Definition ackermann_bit (a x : pa_term) : pa_form :=
  ∃ (pow2 x`[↑] $0 ∧
     ∃ ∃ ((a`[↑]`[↑]`[↑] ==
             (($1 ⊗ ($2 ⊕ $2)) ⊕ $2) ⊕ $0) ∧ ($0 ⧀ $2))).
Definition coded_member (a x : pa_term) : pa_form :=
  ackermann_bit a x.

Lemma beta_modulus_subst c i rho :
  (beta_modulus c i)`[rho] = beta_modulus c`[rho] i`[rho].
Proof. unfold beta_modulus. reflexivity. Qed.

Lemma beta_subst b c i r rho :
  (beta b c i r)[rho] = beta b`[rho] c`[rho] i`[rho] r`[rho].
Proof. unfold beta, beta_modulus, PAlt. cbn. now rewrite !up_term. Qed.

Lemma pow2_subst n p rho :
  (pow2 n p)[rho] = pow2 n`[rho] p`[rho].
Proof.
  unfold pow2, beta, beta_modulus, PAlt. cbn. now rewrite !up_term.
Qed.

Lemma ackermann_bit_subst a x rho :
  (ackermann_bit a x)[rho] = ackermann_bit a`[rho] x`[rho].
Proof.
  unfold ackermann_bit, pow2, beta, beta_modulus, PAlt.
  cbn. now rewrite !up_term.
Qed.

Lemma coded_member_subst a x rho :
  (coded_member a x)[rho] = coded_member a`[rho] x`[rho].
Proof.
  unfold coded_member. apply ackermann_bit_subst.
Qed.

(* The compact signature has no functions: all its terms are variables. *)
Definition embed_term (t : Compact238.set_term) : pa_term :=
  match t with
  | var n => var n
  | func f _ => match f with end
  end.
Definition embed_substitution (rho : nat -> Compact238.set_term) : nat -> pa_term :=
  fun n => embed_term (rho n).

Lemma embed_term_subst t rho :
  embed_term t`[rho] = (embed_term t)`[embed_substitution rho].
Proof. destruct t as [n|f v]; [reflexivity|destruct f]. Qed.

Lemma embed_term_shift t : embed_term t`[↑] = (embed_term t)`[↑].
Proof. destruct t as [n|f v]; [reflexivity|destruct f]. Qed.

Lemma embed_substitution_up rho n :
  embed_substitution (up rho) n = up (embed_substitution rho) n.
Proof.
  destruct n; cbn [embed_substitution up scons funcomp];
    [reflexivity|apply embed_term_shift].
Qed.

Definition atom_to_pa (p : ZF_Preds) (v : Vector.t Compact238.set_term 2) : pa_form :=
  match p with
  | elem => coded_member (embed_term (Vector.hd (Vector.tl v)))
                         (embed_term (Vector.hd v))
  | equal => embed_term (Vector.hd v) == embed_term (Vector.hd (Vector.tl v))
  end.

Fixpoint translate_form {ff : falsity_flag}
    (phi : @form BinSig.sig_empty ZFSignature.ZF_pred_sig full_operators ff)
    : pa_form :=
  match phi with
  | falsity => falsity
  | atom p v => atom_to_pa p v
  | bin b psi chi => bin b (translate_form psi) (translate_form chi)
  | quant q psi => quant q (translate_form psi)
  end.

Definition translate (phi : Compact238.set_form) : pa_form := translate_form phi.

Lemma vector2_eta X (v : Vector.t X 2) :
  v = [Vector.hd v; Vector.hd (Vector.tl v)].
Proof.
  rewrite (Vector.eta v) at 1. f_equal.
  apply destruct_vector_single.
Qed.

Lemma atom_to_pa_subst p v rho :
  (atom_to_pa p v)[embed_substitution rho] =
  atom_to_pa p (Vector.map (subst_term rho) v).
Proof.
  rewrite (vector2_eta Compact238.set_term v).
  destruct (Vector.hd v) as [i|f w]; [|destruct f].
  destruct (Vector.hd (Vector.tl v)) as [j|f w]; [|destruct f].
  destruct p.
  - change ((coded_member $j $i)[embed_substitution rho] =
      coded_member (embed_term (rho j)) (embed_term (rho i))).
    rewrite coded_member_subst. reflexivity.
  - change ((($i == $j) : pa_form)[embed_substitution rho] =
      (embed_term (rho i) == embed_term (rho j))).
    reflexivity.
Qed.

Theorem translate_subst phi rho :
  translate phi[rho] = (translate phi)[embed_substitution rho].
Proof.
  revert rho.
  induction phi as [|p v|b phi IHphi psi IHpsi|q phi IHphi]
    using form_ind_falsity; intros rho;
    cbn [translate translate_form subst_form].
  - reflexivity.
  - symmetry. apply atom_to_pa_subst.
  - unfold translate in IHphi, IHpsi.
    now rewrite (IHphi rho), (IHpsi rho).
  - unfold translate in IHphi.
    rewrite (IHphi (up rho)). f_equal.
    apply subst_ext. apply embed_substitution_up.
Qed.

Lemma translate_shift phi : translate phi[↑] = (translate phi)[↑].
Proof.
  rewrite translate_subst. apply subst_ext. intros n. reflexivity.
Qed.

Lemma translate_instance phi t :
  translate phi[t..] = (translate phi)[(embed_term t)..].
Proof.
  rewrite translate_subst. apply subst_ext. intros [|n]; reflexivity.
Qed.

Lemma translate_shift_context A :
  List.map translate (List.map (subst_form ↑) A) =
  List.map (subst_form ↑) (List.map translate A).
Proof.
  rewrite !List.map_map. apply List.map_ext. apply translate_shift.
Qed.

(* All fifteen natural-deduction constructors are translated. The output
   retains an explicit finite context; no arithmetic axiom producer occurs
   among this theorem's assumptions. Peirce's constructor remains classical. *)
Theorem translate_prv :
  forall p A phi,
    @prv BinSig.sig_empty ZFSignature.ZF_pred_sig falsity_on p A phi ->
    @prv PA_funcs_signature PA_preds_signature falsity_on p
      (List.map translate A) (translate phi).
Proof.
  apply (@prv_ind_full BinSig.sig_empty ZFSignature.ZF_pred_sig
    (fun p A phi =>
      @prv PA_funcs_signature PA_preds_signature falsity_on p
        (List.map translate A) (translate phi))).
  - intros p A phi psi H IH. cbn. apply II. exact IH.
  - intros p A phi psi H IH K IK. cbn in IH. eapply IE; eassumption.
  - intros p A phi H IH. cbn. apply AllI.
    rewrite <- translate_shift_context. exact IH.
  - intros p A t phi H IH. rewrite translate_instance.
    apply (AllE (embed_term t)). exact IH.
  - intros p A t phi H IH. cbn. apply (ExI (embed_term t)).
    rewrite <- translate_instance. exact IH.
  - intros p A phi psi H IH K IK. cbn in IH.
    eapply ExE; [exact IH|].
    rewrite <- translate_shift_context, <- translate_shift.
    exact IK.
  - intros p A phi H IH. cbn in IH. now apply Exp.
  - intros p A phi H. apply Ctx. now apply List.in_map.
  - intros p A phi psi H IH K IK. cbn. now apply CI.
  - intros p A phi psi H IH. cbn in IH. now apply (CE1 IH).
  - intros p A phi psi H IH. cbn in IH. now apply (CE2 IH).
  - intros p A phi psi H IH. cbn. now apply DI1.
  - intros p A phi psi H IH. cbn. now apply DI2.
  - intros p A phi psi theta H IH K IK L IL.
    cbn in IH, IK, IL. eapply DE; eassumption.
  - intros A phi psi. cbn. apply Pc.
Qed.

Definition translated_theory (T : Compact238.set_form -> Prop) (psi : pa_form) : Prop :=
  exists phi, T phi /\ translate phi = psi.

Theorem translate_finite_derivation T phi :
  Compact238.derivable T phi -> translated_theory T ⊢TC translate phi.
Proof.
  intros (A & HA & HD). exists (List.map translate A). split.
  - intros psi Hpsi. apply List.in_map_iff in Hpsi.
    destruct Hpsi as (chi & <- & Hchi). exists chi. split;
      [now apply HA|reflexivity].
  - now apply (translate_prv class A phi).
Qed.

Corollary translate_compact_falsity :
  Compact238.derivable Compact238.compact_theory falsity ->
  translated_theory Compact238.compact_theory ⊢TC falsity.
Proof. apply translate_finite_derivation. Qed.

Corollary translate_adj_sep_falsity :
  Compact238.derivable Compact238.adj_sep_theory falsity ->
  translated_theory Compact238.adj_sep_theory ⊢TC falsity.
Proof. apply translate_finite_derivation. Qed.

Lemma translate_R a x :
  translate (Compact238.R a x) = coded_member (embed_term a) (embed_term x).
Proof. reflexivity. Qed.
Lemma translate_E x y :
  translate (Compact238.E x y) = (embed_term x == embed_term y).
Proof. reflexivity. Qed.

(* Equality of all arithmetic subterms is transported through the actual
   bit formula. The only context requirements are the six finite EQ axioms. *)
Lemma coded_member_congruence G a b x y :
  PAEqCongruence238.has_equality G ->
  G ⊢C (a == b) -> G ⊢C (x == y) ->
  G ⊢C (coded_member a x ↔ coded_member b y).
Proof.
  intros HE HA HX.
  assert (HR : forall n, G ⊢C
    ((x .: a .: var) n == (y .: b .: var) n)).
  { intros [|[|n]]; cbn; [exact HX|exact HA|].
    apply PAEqCongruence238.reflexivity_instance, HE. }
  pose proof (PAEqCongruence238.formula_substitution_equivalent
    (coded_member $1 $0) G (x .: a .: var) (y .: b .: var) HE HR) as H.
  rewrite !coded_member_subst in H.
  change (G ⊢C (coded_member a x ↔ coded_member b y)) in H. exact H.
Qed.

Theorem ordinary_membership_congruence :
  paeq_derivable (∀ ∀ ∀ ∀
    ($3 == $1 → $2 == $0 → coded_member $2 $3 → coded_member $0 $1)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize.
  apply paeq_from_upstream. exists EQ. split.
  - exact PAEqCongruence238.equality_context_PAeq.
  - apply II, II, II.
    set (G := List.cons (coded_member $2 $3)
      (List.cons ($2 == $0) (List.cons ($3 == $1) EQ))).
    change (G ⊢C coded_member $0 $1).
    assert (HE : PAEqCongruence238.has_equality G).
    { unfold G. apply PAEqCongruence238.has_equality_cons,
        PAEqCongruence238.has_equality_cons,
        PAEqCongruence238.has_equality_cons.
      intros chi Hchi. exact Hchi. }
    assert (HC : G ⊢C ($2 == $0)).
    { apply Ctx. unfold G. right. now left. }
    assert (HM : G ⊢C ($3 == $1)).
    { apply Ctx. unfold G. right. right. now left. }
    eapply IE with (phi := coded_member $2 $3).
    + exact (CE1 (coded_member_congruence G $2 $0 $3 $1 HE HC HM)).
    + apply Ctx. unfold G. now left.
Qed.

Lemma membership_ir_guard G t :
  G ⊢C (coded_member t t → t ⧀ t) ->
  G ⊢C ¬ (t ⧀ t) -> G ⊢C ¬ coded_member t t.
Proof.
  intros HB H. apply II. eapply IE.
  - eapply Weak; [exact H|]. intros phi Hphi. now right.
  - eapply IE.
    + eapply Weak; [exact HB|]. intros phi Hphi. now right.
    + apply Ctx. now left.
Qed.

Lemma forall_membership_ir G :
  G ⊢C (∀ ∀ (coded_member $1 $0 → $0 ⧀ $1)) ->
  G ⊢C (∀ ¬ ($0 ⧀ $0)) -> G ⊢C (∀ ¬ coded_member $0 $0).
Proof.
  intros HB HO. apply AllI_named. intros t.
  apply membership_ir_guard.
  - change (G ⊢C (coded_member $1 $0 → $0 ⧀ $1)[t .: t .: var]).
    eapply subst_forall_prv with (N := 2); [exact HB|].
    unfold coded_member, ackermann_bit, pow2, beta, beta_modulus, PAlt.
    solve_bounds.
  - exact (AllE t HO).
Qed.

(* Logical tails of finite-support comprehension and literal PAS. These
   construct derivations from displayed local premises; arithmetic coding
   witnesses and their bounds are still separate producer obligations. *)
Lemma forget_finite_bound G B P M :
  G ⊢C (P → B) -> G ⊢C (M ↔ (B ∧ P)) -> G ⊢C (M ↔ P).
Proof.
  intros HS HC. apply CI.
  - apply II. eapply CE2. eapply IE.
    + eapply Weak; [exact (CE1 HC)|]. intros phi Hphi. now right.
    + apply Ctx. now left.
  - apply II. eapply IE.
    + eapply Weak; [exact (CE2 HC)|]. intros phi Hphi. now right.
    + apply CI; [|apply Ctx; now left]. eapply IE.
      * eapply Weak; [exact HS|]. intros phi Hphi. now right.
      * apply Ctx. now left.
Qed.

Lemma forall_forget_finite_bound G B P M :
  G ⊢C (∀ (P → B)) -> G ⊢C (∀ (M ↔ (B ∧ P))) ->
  G ⊢C (∀ (M ↔ P)).
Proof.
  intros HS HC. apply AllI_named. intros t. cbn [subst_form].
  eapply forget_finite_bound; [exact (AllE t HS)|exact (AllE t HC)].
Qed.

Lemma filter_to_literal_pas G B P M :
  G ⊢C (M ↔ (B ∧ P)) -> G ⊢C ((B → P → M) ∧ (M → P)).
Proof.
  intros H. apply CI.
  - apply II, II. eapply IE.
    + eapply Weak; [exact (CE2 H)|]. intros phi Hphi. right. now right.
    + apply CI; apply Ctx; [right; now left|now left].
  - apply II. eapply CE2. eapply IE.
    + eapply Weak; [exact (CE1 H)|]. intros phi Hphi. now right.
    + apply Ctx. now left.
Qed.

Lemma forall_filter_to_literal_pas G B P M :
  G ⊢C (∀ (M ↔ (B ∧ P))) ->
  G ⊢C (∀ ((B → P → M) ∧ (M → P))).
Proof.
  intros H. apply AllI_named. intros t. cbn [subst_form].
  apply filter_to_literal_pas. exact (AllE t H).
Qed.

(* Concrete producer goals. These are pending propositions with no supplied
   proof values. In particular there is no all-axioms adequacy premise used
   to manufacture the open compact-to-PA endpoint. *)
Definition pow2_total_goal : Prop :=
  paeq_derivable (∀ ∃ pow2 $1 $0).
Definition pow2_unique_goal : Prop :=
  paeq_derivable (∀ ∀ ∀ (pow2 $2 $1 → pow2 $2 $0 → $1 == $0)).
Definition pow2_index_bound_goal : Prop :=
  paeq_derivable (∀ ∀ (pow2 $1 $0 → $1 ⧀ $0)).
Definition bit_position_goal : Prop :=
  paeq_derivable (∀ ∀ (coded_member $1 $0 → $0 ⧀ $1)).
Definition equality_producer_goal : Prop :=
  forall phi,
    List.In phi Compact238.equality_base -> paeq_derivable (translate phi).

Theorem equality_producer : equality_producer_goal.
Proof.
  unfold equality_producer_goal, Compact238.equality_base.
  intros phi [<-|[<-|[<-|[<-|[]]]]].
  - change (paeq_derivable ax_refl).
    apply paeq_axiom, PAEqCongruence238.equality_context_PAeq.
    unfold EQ. now left.
  - change (paeq_derivable ax_sym).
    apply paeq_axiom, PAEqCongruence238.equality_context_PAeq.
    unfold EQ. right. now left.
  - change (paeq_derivable ax_trans).
    apply paeq_axiom, PAEqCongruence238.equality_context_PAeq.
    unfold EQ. right. right. now left.
  - change (paeq_derivable (∀ ∀ ∀ ∀
      ($3 == $1 → $2 == $0 → coded_member $2 $3 → coded_member $0 $1))).
    exact ordinary_membership_congruence.
Qed.

(* phi has slot0=member and slot(1+k)=arbitrary arithmetic parameter k.
   Binders introduce a bound, output code, and tested member, respectively. *)
Definition bounded_comprehension (phi : pa_form) : pa_form :=
  ∀ ∃ ∀ (coded_member $1 $0 ↔
    (($0 ⧀ $2) ∧ phi[$0 .: (fun k => $(3 + k))])).
Definition bounded_comprehension_goal : Prop :=
  forall phi : pa_form, paeq_derivable (universal_close (bounded_comprehension phi)).

Definition empty_producer_goal : Prop :=
  paeq_derivable (translate Compact238.empty_ax).
Definition adjunction_producer_goal : Prop :=
  paeq_derivable (translate Compact238.adjunction_ax).
Definition separation_producer_goal : Prop :=
  forall phi n,
    bounded 0 (forall_times n (Compact238.separation_ax phi)) ->
    paeq_derivable (translate (forall_times n (Compact238.separation_ax phi))).
Definition ir_producer_goal : Prop :=
  paeq_derivable (translate Compact238.ir).

(* A finite proof construction of the IR producer from its two local
   arithmetic prerequisites. Neither prerequisite is assumed globally. *)
Lemma ir_from_position_and_order :
  bit_position_goal -> paeq_derivable (∀ ¬ ($0 ⧀ $0)) -> ir_producer_goal.
Proof.
  intros (A & HA & HB) (B & HBctx & HO).
  exists (List.app A B). split.
  - intros phi Hphi. apply List.in_app_iff in Hphi.
    destruct Hphi as [Hphi|Hphi]; [now apply HA|now apply HBctx].
  - apply forall_membership_ir.
    + eapply Weak; [exact HB|]. intros phi Hphi.
      apply List.in_app_iff. now left.
    + eapply Weak; [exact HO|]. intros phi Hphi.
      apply List.in_app_iff. now right.
Qed.

Corollary ir_from_position : bit_position_goal -> ir_producer_goal.
Proof.
  intros HB. apply ir_from_position_and_order; [exact HB|].
  apply PAOrder238.order_irreflexive.
Qed.
Definition pointed_producer_goal : Prop :=
  forall phi n,
    bounded 0 (forall_times n (Compact238.pointed_ax phi)) ->
    paeq_derivable (translate (forall_times n (Compact238.pointed_ax phi))).
Definition collided_producer_goal : Prop :=
  forall phi n,
    bounded 0 (forall_times n (Compact238.collided_ax phi)) ->
    paeq_derivable (translate (forall_times n (Compact238.collided_ax phi))).

Print Assumptions coded_member_subst.
Print Assumptions translate_subst.
Print Assumptions translate_prv.
Print Assumptions translate_finite_derivation.
Print Assumptions translate_compact_falsity.
Print Assumptions translate_adj_sep_falsity.
Print Assumptions coded_member_congruence.
Print Assumptions ordinary_membership_congruence.
Print Assumptions equality_producer.
Print Assumptions membership_ir_guard.
Print Assumptions ir_from_position_and_order.
Print Assumptions ir_from_position.
Print Assumptions forall_forget_finite_bound.
Print Assumptions forall_filter_to_literal_pas.

End CompactInPA238.
