(** Original PA-in-compact work, using finite natural-deduction proofs.

    The eventual target is a constructive transport of finite PAeq
    refutations into [Compact238.derivable finite_set_S0 falsity], where
    [finite_set_S0] below has no global IR axiom.  That transport is not
    asserted here.  This leaf begins the representative
    induction proof: it derives the local minimum-counterexample
    contradiction from the displayed order, trace, and successor data.
    The property is an arbitrary library formula, including every parameter
    and nested quantifier.  No decidability of the property is assumed.

    Remaining work includes the global containing-domain and successor
    closure construction, nonempty-trace/least selection and full induction,
    isomorphism equality, arithmetic graphs and their coherence/totality,
    and recursion on the finite upstream PAeq derivation.  No model-theoretic
    consistency shortcut or endpoint premise occurs in this file. *)

From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238.
Import ListNotations FullSyntax BinSig ZFSignature Compact238.Compact238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAinCompact238.

(** The forward mathematical theory is Adjunction plus full Separation
    with ordinary equality, without global IR.  A theory predicate lists
    allowed first-order axioms; it is not a Coq axiom or an adequacy claim. *)
Inductive finite_set_S0 : set_form -> Prop :=
| S0_base phi : In phi (equality_base ++ [adjunction_ax]) -> finite_set_S0 phi
| S0_separation phi n :
    bounded 0 (forall_times n (separation_ax phi)) ->
    finite_set_S0 (forall_times n (separation_ax phi)).

Definition equality_membership_ax : set_form :=
  ∀ ∀ ∀ ∀ (E $3 $1 → E $2 $0 → R $2 $3 → R $0 $1).
Definition equality_symmetry_ax : set_form := ∀ ∀ (E $1 $0 → E $0 $1).

(** [phi] has member slot $0 and arbitrary parameter slots $(1+k).
    After the member binder, the property can be inserted unchanged.
    A trace is literally the members of s on which phi fails. *)
Definition bad_trace (c s : set_term) (phi : set_form) : set_form :=
  ∀ (R c`[↑] $0 ↔ (R s`[↑] $0 ∧ ¬ phi)).
Definition bad_trace_exists (s : set_term) (phi : set_form) : set_form :=
  ∃ bad_trace $0 s`[↑] (phi[up ↑]).

(** The PA-in-set direction needs no global IR axiom.  Strictness is part
    of its interpreted domain.  The earlier [representative] formula is
    strengthened here, so all members of an interpreted ordinal are
    irreflexive, even in a model where unrelated objects self-belong. *)
Definition member_ir (a : set_term) : set_form :=
  ∀ (R a`[↑] $0 → ¬ R $0 $0).
Definition ordinal_representative (a : set_term) : set_form :=
  representative a ∧ member_ir a.

Lemma weaken_one G psi phi : G ⊢238 phi -> (psi :: G) ⊢238 phi.
Proof.
  intro H. eapply Weak; [exact H|]. intros chi Hchi. now right.
Qed.

Lemma classical_double_negation G phi : G ⊢238 (¬ (¬ phi)) -> G ⊢238 phi.
Proof.
  intro H. eapply IE; [apply Pc|]. apply II, Exp. eapply IE.
  - apply weaken_one. exact H.
  - apply Ctx. now left.
Qed.

Lemma equality_membership_instance G x a y b :
  G ⊢238 equality_membership_ax ->
  G ⊢238 (E x y → E a b → R a x → R b y).
Proof.
  destruct x as [ix|[]], a as [ia|[]], y as [iy|[]], b as [ib|[]].
  intro H. unfold equality_membership_ax in H.
  pose proof (AllE $ib (AllE $iy (AllE $ia (AllE $ix H)))) as H'.
  cbn [E R terms2 subst_form subst_term up scons funcomp] in H'.
  exact H'.
Qed.

Lemma transitive_member G a x y :
  G ⊢238 transitive a -> G ⊢238 R a x -> G ⊢238 R x y -> G ⊢238 R a y.
Proof.
  destruct a as [ia|[]], x as [ix|[]], y as [iy|[]].
  intros HA HX HY. unfold transitive in HA.
  pose proof (AllE $iy (AllE $ix HA)) as H.
  cbn [R terms2 subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma least_member_cases G c b m :
  G ⊢238 least c b -> G ⊢238 R c m -> G ⊢238 (E b m ∨ R m b).
Proof.
  destruct c as [ic|[]], b as [ib|[]], m as [im|[]].
  intros HL HM. unfold least in HL.
  pose proof (AllE $im (CE2 HL)) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE H HM).
Qed.

Lemma greatest_member_cases G b m z :
  G ⊢238 greatest b m -> G ⊢238 R b z -> G ⊢238 (E z m ∨ R m z).
Proof.
  destruct b as [ib|[]], m as [im|[]], z as [iz|[]].
  intros HG HZ. unfold greatest in HG.
  pose proof (AllE $iz (CE2 HG)) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE H HZ).
Qed.

Lemma equality_symmetry_instance G x y :
  G ⊢238 equality_symmetry_ax -> G ⊢238 E x y -> G ⊢238 E y x.
Proof.
  destruct x as [ix|[]], y as [iy|[]]. intros HE Hxy.
  unfold equality_symmetry_ax in HE.
  pose proof (AllE $iy (AllE $ix HE)) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE H Hxy).
Qed.

Lemma equality_member_transport G a x y :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 E x y -> G ⊢238 R a x -> G ⊢238 R a y.
Proof.
  intros HE HQ Hxy HX. eapply IE; [|exact HX].
  eapply IE; [|exact (AllE a HE)]. eapply IE; [|exact Hxy].
  apply equality_membership_instance. exact HQ.
Qed.

Lemma disjunction_swap G phi psi : G ⊢238 phi ∨ psi -> G ⊢238 psi ∨ phi.
Proof.
  intro H. eapply DE; [exact H|apply DI2|apply DI1]; apply Ctx; now left.
Qed.

(** A greatest element of a transitive ordinal gives its actual raw
    predecessor.  Both directions of the successor biconditional have
    finite proofs, and equality transport uses only the ordinary equality
    axioms.  No numerical equality or global IR is used. *)
Lemma greatest_raw_predecessor G b m :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 transitive b ->
  G ⊢238 greatest b m -> G ⊢238 raw_successor m b.
Proof.
  destruct b as [ib|[]], m as [im|[]]. intros HE HQ HS HB HG.
  unfold raw_successor. apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply CI.
  - apply II, disjunction_swap. apply (greatest_member_cases _ $ib $im $iz).
    + apply weaken_one. exact HG.
    + apply Ctx. now left.
  - apply II. eapply DE; [apply Ctx; now left| |].
    + apply (transitive_member _ $ib $im $iz).
      * apply weaken_one, weaken_one. exact HB.
      * apply weaken_one, weaken_one. exact (CE1 HG).
      * apply Ctx. now left.
    + apply (equality_member_transport _ $ib $im $iz).
      * apply weaken_one, weaken_one. exact HE.
      * apply weaken_one, weaken_one. exact HQ.
      * apply (equality_symmetry_instance _ $iz $im).
        -- apply weaken_one, weaken_one. exact HS.
        -- apply Ctx. now left.
      * apply weaken_one, weaken_one. exact (CE1 HG).
Qed.

Lemma trace_member_bad G c s phi t :
  G ⊢238 bad_trace c s phi -> G ⊢238 R c t -> G ⊢238 (¬ phi[t..]).
Proof.
  destruct c as [ic|[]], s as [is|[]], t as [it|[]].
  intros HT HM. unfold bad_trace in HT.
  pose proof (AllE $it HT) as H.
  cbn [R terms2 subst_form subst_term up scons funcomp] in H.
  exact (CE2 (IE (CE1 H) HM)).
Qed.

Lemma trace_bad_member G c s phi t :
  G ⊢238 bad_trace c s phi -> G ⊢238 R s t ->
  G ⊢238 (¬ phi[t..]) -> G ⊢238 R c t.
Proof.
  destruct c as [ic|[]], s as [is|[]], t as [it|[]].
  intros HT HM HB. unfold bad_trace in HT.
  pose proof (AllE $it HT) as H.
  cbn [R terms2 subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact (CE2 H)|]. apply CI; assumption.
Qed.

Lemma trace_nonmember_good G c s phi t :
  G ⊢238 bad_trace c s phi -> G ⊢238 R s t ->
  G ⊢238 (¬ R c t) -> G ⊢238 phi[t..].
Proof.
  intros HT HM HN. apply classical_double_negation, II. eapply IE.
  - apply weaken_one. exact HN.
  - apply (trace_bad_member _ c s phi t).
    + apply weaken_one. exact HT.
    + apply weaken_one. exact HM.
    + apply Ctx. now left.
Qed.

(** Eliminating the Separation input binder shifts only the parameter
    tail of phi.  Its tested-member slot remains $0.  The equality is on
    syntax for arbitrary phi, so nested binders and parameters are covered. *)
Lemma separation_property_subst (phi : set_form) (s : set_term) :
  (phi[separation_slots])[up (up (s..))] = phi[up ↑].
Proof.
  rewrite subst_comp. apply subst_ext. intros [|k];
    cbn [separation_slots up scons funcomp subst_term]; reflexivity.
Qed.

Lemma separation_bad_trace_equation s phi :
  (∃ ∀ (R $1 $0 ↔ (R $2 $0 ∧ (¬ phi)[separation_slots])))[s..] =
  bad_trace_exists s phi.
Proof.
  destruct s as [is|[]].
  change
    ((∃ ∀ (R $1 $0 ↔
      (R $(S (S is)) $0 ∧ ¬ ((phi[separation_slots])[up (up ($is..))])))) =
     (∃ ∀ (R $1 $0 ↔
      (R $(S (S is)) $0 ∧ ¬ phi[up ↑])))).
  rewrite separation_property_subst. reflexivity.
Qed.

Lemma separation_bad_trace G s phi :
  G ⊢238 separation_ax (¬ phi) -> G ⊢238 bad_trace_exists s phi.
Proof.
  intro HS. rewrite <- separation_bad_trace_equation. exact (AllE s HS).
Qed.

Lemma S0_separation_instance n phi :
  bounded (1 + n) phi -> derivable finite_set_S0 (separation_ax phi).
Proof.
  intro Hphi. exists [forall_times n (separation_ax phi)]. split.
  - intros psi [<-|[]]. apply S0_separation.
    now apply separation_instance_closed.
  - assert (HC : [forall_times n (separation_ax phi)] ⊢238
                   forall_times n (separation_ax phi)).
    { apply Ctx. now left. }
    pose proof (subst_forall_prv (phi := separation_ax phi) (N := n)
      (Gamma := [forall_times n (separation_ax phi)]) HC
      (separation_ax_bounded n phi Hphi) var) as H.
    rewrite subst_var in H. exact H.
Qed.

Theorem S0_bad_trace_exists n phi s :
  bounded (1 + n) phi -> derivable finite_set_S0 (bad_trace_exists s phi).
Proof.
  intro Hphi.
  destruct (S0_separation_instance n (¬ phi) ltac:(constructor; [exact Hphi|constructor]))
    as [G [HG HS]].
  exists G. split; [exact HG|]. apply separation_bad_trace. exact HS.
Qed.

Lemma finite_set_S0_closed phi : finite_set_S0 phi -> bounded 0 phi.
Proof.
  intros [psi HP|psi n HP]; [|exact HP].
  apply in_app_or in HP as [HP|HP].
  - now apply equality_base_closed.
  - destruct HP as [<-|[]]. apply adjunction_ax_closed.
Qed.

Lemma S0_generalize phi :
  derivable finite_set_S0 phi -> derivable finite_set_S0 (∀ phi).
Proof. apply derivable_generalize, finite_set_S0_closed. Qed.

Lemma ir_refute G t : G ⊢238 ir -> G ⊢238 R t t -> G ⊢238 falsity.
Proof.
  intros HIR HT. eapply IE; [exact (AllE t HIR)|exact HT].
Qed.

Lemma equal_predecessor_self_member G b m :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 E b m -> G ⊢238 R b m -> G ⊢238 R m m.
Proof.
  intros HE HQ Hbm HM. eapply IE; [|exact HM].
  eapply IE; [|exact Hbm]. eapply IE; [|exact (AllE m HE)].
  apply equality_membership_instance. exact HQ.
Qed.

Lemma member_ir_excludes_self G b t :
  G ⊢238 member_ir b -> G ⊢238 R b t -> G ⊢238 (¬ R t t).
Proof.
  destruct b as [ib|[]], t as [it|[]]. intros HB HT.
  unfold member_ir in HB. pose proof (AllE $it HB) as H.
  cbn [R terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE H HT).
Qed.

Lemma member_ir_refute G b t :
  G ⊢238 member_ir b -> G ⊢238 R b t -> G ⊢238 R t t -> G ⊢238 falsity.
Proof.
  intros HB HM HS. eapply IE; [|exact HS].
  apply (member_ir_excludes_self _ b t); assumption.
Qed.

(** The forward interpretation uses this local strictness version.  Its
    finite proof is independent of the global IR axiom. *)
Lemma strict_least_predecessor_excluded G c b m :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 member_ir b -> G ⊢238 transitive b ->
  G ⊢238 R b m -> G ⊢238 least c b -> G ⊢238 (¬ R c m).
Proof.
  intros HE HQ HI HB HM HL. apply II. eapply DE.
  - apply (least_member_cases _ c b m).
    + apply weaken_one. exact HL.
    + apply Ctx. now left.
  - apply (member_ir_refute _ b m).
    + apply weaken_one, weaken_one. exact HI.
    + apply weaken_one, weaken_one. exact HM.
    + apply (equal_predecessor_self_member _ b m).
      * apply weaken_one, weaken_one. exact HE.
      * apply weaken_one, weaken_one. exact HQ.
      * apply Ctx. now left.
      * apply weaken_one, weaken_one. exact HM.
  - assert (Hbb : (R m b :: R c m :: G) ⊢238 R b b).
    { apply (transitive_member _ b m b).
      - apply weaken_one, weaken_one. exact HB.
      - apply weaken_one, weaken_one. exact HM.
      - apply Ctx. now left. }
    apply (member_ir_refute _ b b); [|exact Hbb|exact Hbb].
    apply weaken_one, weaken_one. exact HI.
Qed.

Theorem strict_minimum_counterexample_contradiction G c s b m phi :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 member_ir b -> G ⊢238 transitive b ->
  G ⊢238 R b m -> G ⊢238 least c b ->
  G ⊢238 bad_trace c s phi -> G ⊢238 R s m ->
  G ⊢238 (phi[m..] → phi[b..]) -> G ⊢238 falsity.
Proof.
  intros HE HQ HI HB HM HL HT Hsm Hstep. eapply IE.
  - apply (trace_member_bad _ c s phi b); [exact HT|exact (CE1 HL)].
  - eapply IE; [exact Hstep|].
    apply (trace_nonmember_good _ c s phi m); [exact HT|exact Hsm|].
    apply (strict_least_predecessor_excluded _ c b m); assumption.
Qed.

(** If b is the least member of c, its strict predecessor m cannot also
    belong to c.  The equality branch would make m self-membered; the
    strict-order branch would make b self-membered by transitivity. *)
Lemma least_predecessor_excluded G c b m :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax -> G ⊢238 ir ->
  G ⊢238 transitive b -> G ⊢238 R b m -> G ⊢238 least c b ->
  G ⊢238 (¬ R c m).
Proof.
  intros HE HQ HIR HB HM HL. apply II. eapply DE.
  - apply (least_member_cases _ c b m).
    + apply weaken_one. exact HL.
    + apply Ctx. now left.
  - apply (ir_refute _ m).
    + apply weaken_one, weaken_one. exact HIR.
    + apply (equal_predecessor_self_member _ b m).
      * apply weaken_one, weaken_one. exact HE.
      * apply weaken_one, weaken_one. exact HQ.
      * apply Ctx. now left.
      * apply weaken_one, weaken_one. exact HM.
  - apply (ir_refute _ b).
    + apply weaken_one, weaken_one. exact HIR.
    + apply (transitive_member _ b m b).
      * apply weaken_one, weaken_one. exact HB.
      * apply weaken_one, weaken_one. exact HM.
      * apply Ctx. now left.
Qed.

(** This is a syntactic proof leaf of minimum-counterexample induction.
    All four object witnesses and all property parameters are retained.
    Witness production is not postulated by this theorem: the hypotheses
    are individual local formulas to be derived from the compact schemas.
    The conclusion is a finite ND derivation of falsity. *)
Theorem minimum_counterexample_contradiction G c s b m phi :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax -> G ⊢238 ir ->
  G ⊢238 transitive b -> G ⊢238 R b m -> G ⊢238 least c b ->
  G ⊢238 bad_trace c s phi -> G ⊢238 R s m ->
  G ⊢238 (phi[m..] → phi[b..]) -> G ⊢238 falsity.
Proof.
  intros HE HQ HIR HB HM HL HT Hsm Hstep.
  eapply IE.
  - apply (trace_member_bad _ c s phi b); [exact HT|exact (CE1 HL)].
  - eapply IE; [exact Hstep|].
    apply (trace_nonmember_good _ c s phi m); [exact HT|exact Hsm|].
    apply (least_predecessor_excluded _ c b m); assumption.
Qed.

Lemma compact_reflexivity : derivable compact_theory (∀ E $0 $0).
Proof.
  apply derivable_axiom, compact_equality. now left.
Qed.

Lemma compact_equality_membership :
  derivable compact_theory equality_membership_ax.
Proof.
  apply derivable_axiom, compact_equality.
  unfold equality_base, equality_membership_ax.
  right. right. right. now left.
Qed.

(** The false property produces an empty object directly from one pointed
    instance.  This is a witness producer, not a premise asserting empty
    set existence.  The two input specializations are arbitrary terms. *)
Lemma pointed_false_empty G : G ⊢238 pointed_ax falsity -> G ⊢238 empty_ax.
Proof.
  intro HP. unfold pointed_ax in HP.
  pose proof (AllE $0 (AllE $0 HP)) as HX.
  eapply ExE_named; [exact HX|]. intro e. destruct e as [ie|[]].
  unfold empty_ax. apply (ExI $ie).
  eapply all_conj_right. eapply CE1, Ctx. now left.
Qed.

Lemma compact_empty : derivable compact_theory empty_ax.
Proof.
  exists [pointed_ax falsity]. split.
  - intros phi [<-|[]].
    change (compact_theory (forall_times 0 (pointed_ax falsity))).
    apply compact_pointed, pointed_instance_closed. constructor.
  - apply pointed_false_empty, Ctx. now left.
Qed.

(** Every empty object is a representative.  Transitivity and linearity
    have impossible member guards.  The extrema clause has an impossible
    nonempty-subset guard.  No quotient extensionality is used. *)
Lemma empty_transitive G a : G ⊢238 raw_zero a -> G ⊢238 transitive a.
Proof.
  destruct a as [ia|[]]. intro HZ. unfold transitive.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp].
  apply II, Exp. eapply IE.
  - apply weaken_one. exact (zero_excludes_member _ $ia $ix HZ).
  - eapply CE1, Ctx. now left.
Qed.

Lemma empty_member_transitive G a :
  G ⊢238 raw_zero a -> G ⊢238 member_transitive a.
Proof.
  destruct a as [ia|[]]. intro HZ. unfold member_transitive.
  apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp].
  apply II, Exp. eapply IE.
  - apply weaken_one. exact (zero_excludes_member _ $ia $ix HZ).
  - apply Ctx. now left.
Qed.

Lemma empty_member_linear G a : G ⊢238 raw_zero a -> G ⊢238 member_linear a.
Proof.
  destruct a as [ia|[]]. intro HZ. unfold member_linear.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  apply II, Exp. eapply IE.
  - apply weaken_one. exact (zero_excludes_member _ $ia $ix HZ).
  - eapply CE1, Ctx. now left.
Qed.

Lemma empty_internal_extrema G a :
  G ⊢238 raw_zero a -> G ⊢238 internal_extrema a.
Proof.
  destruct a as [ia|[]]. intro HZ. unfold internal_extrema.
  apply AllI_named. intro s. destruct s as [is|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  apply II, Exp.
  assert (HS : ((subset $is $ia ∧ nonempty $is) :: G) ⊢238 subset $is $ia).
  { eapply CE1, Ctx. now left. }
  assert (HN : ((subset $is $ia ∧ nonempty $is) :: G) ⊢238 nonempty $is).
  { eapply CE2, Ctx. now left. }
  unfold nonempty in HN. eapply ExE_named; [exact HN|].
  intro t. destruct t as [it|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp].
  eapply IE.
  - apply weaken_one, weaken_one.
    exact (zero_excludes_member _ $ia $it HZ).
  - unfold subset in HS. eapply IE.
    + apply weaken_one. exact (AllE $it HS).
    + apply Ctx. now left.
Qed.

Theorem empty_representative G a :
  G ⊢238 raw_zero a -> G ⊢238 representative a.
Proof.
  intro HZ. unfold representative. apply CI.
  - apply empty_transitive. exact HZ.
  - apply CI.
    + apply empty_member_transitive. exact HZ.
    + apply CI.
      * apply empty_member_linear. exact HZ.
      * apply empty_internal_extrema. exact HZ.
Qed.

Lemma empty_member_ir G a : G ⊢238 raw_zero a -> G ⊢238 member_ir a.
Proof.
  destruct a as [ia|[]]. intro HZ. unfold member_ir.
  apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp].
  apply II, Exp. eapply IE.
  - apply weaken_one. exact (zero_excludes_member _ $ia $ix HZ).
  - apply Ctx. now left.
Qed.

Theorem empty_ordinal_representative G a :
  G ⊢238 raw_zero a -> G ⊢238 ordinal_representative a.
Proof.
  intro HZ. apply CI.
  - apply empty_representative. exact HZ.
  - apply empty_member_ir. exact HZ.
Qed.

(** Actual extremal witnesses are produced from the representative's
    defining internal-subset clause.  The global induction construction must
    prove the Separation-produced bad trace nonempty and inside a containing
    representative before this clause supplies its least element. *)
Lemma ordinal_internal_extrema G a s :
  G ⊢238 ordinal_representative a ->
  G ⊢238 subset s a -> G ⊢238 nonempty s ->
  G ⊢238 ((∃ least s`[↑] $0) ∧ (∃ greatest s`[↑] $0)).
Proof.
  destruct a as [ia|[]], s as [is|[]]. intros HA HS HN.
  pose proof (CE2 (CE2 (CE2 (CE1 HA)))) as HX.
  unfold internal_extrema in HX. pose proof (AllE $is HX) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma ordinal_internal_least G a s :
  G ⊢238 ordinal_representative a ->
  G ⊢238 subset s a -> G ⊢238 nonempty s -> G ⊢238 ∃ least s`[↑] $0.
Proof.
  intros HA HS HN. eapply CE1. apply (ordinal_internal_extrema _ a s); assumption.
Qed.

Lemma ordinal_internal_greatest G a s :
  G ⊢238 ordinal_representative a ->
  G ⊢238 subset s a -> G ⊢238 nonempty s -> G ⊢238 ∃ greatest s`[↑] $0.
Proof.
  intros HA HS HN. eapply CE2. apply (ordinal_internal_extrema _ a s); assumption.
Qed.

Lemma subset_member G a b t :
  G ⊢238 subset a b -> G ⊢238 R a t -> G ⊢238 R b t.
Proof.
  destruct a as [ia|[]], b as [ib|[]], t as [it|[]]. intros HS HT.
  unfold subset in HS. pose proof (AllE $it HS) as H.
  cbn [R terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE H HT).
Qed.

Lemma subset_transitive G a b c :
  G ⊢238 subset a b -> G ⊢238 subset b c -> G ⊢238 subset a c.
Proof.
  destruct a as [ia|[]], b as [ib|[]], c as [ic|[]]. intros HAB HBC.
  unfold subset. apply AllI_named. intro t. destruct t as [it|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp]. apply II.
  apply (subset_member _ $ib $ic $it).
  - apply weaken_one. exact HBC.
  - apply (subset_member _ $ia $ib $it).
    + apply weaken_one. exact HAB.
    + apply Ctx. now left.
Qed.

Lemma member_subset G a b :
  G ⊢238 transitive a -> G ⊢238 R a b -> G ⊢238 subset b a.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HA HB.
  unfold subset. apply AllI_named. intro t. destruct t as [it|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp]. apply II.
  apply (transitive_member _ $ia $ib $it).
  - apply weaken_one. exact HA.
  - apply weaken_one. exact HB.
  - apply Ctx. now left.
Qed.

Lemma member_transitive_member G a b :
  G ⊢238 member_transitive a -> G ⊢238 R a b -> G ⊢238 transitive b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HA HB.
  unfold member_transitive in HA. pose proof (AllE $ib HA) as H.
  cbn [R terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE H HB).
Qed.

Lemma linear_member_cases G a x y :
  G ⊢238 member_linear a -> G ⊢238 R a x -> G ⊢238 R a y ->
  G ⊢238 (E x y ∨ (R y x ∨ R x y)).
Proof.
  destruct a as [ia|[]], x as [ix|[]], y as [iy|[]]. intros HA HX HY.
  unfold member_linear in HA. pose proof (AllE $iy (AllE $ix HA)) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma subset_member_transitive G b a :
  G ⊢238 subset b a -> G ⊢238 member_transitive a -> G ⊢238 member_transitive b.
Proof.
  destruct b as [ib|[]], a as [ia|[]]. intros HS HA.
  unfold member_transitive. apply AllI_named. intro t. destruct t as [it|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp]. apply II.
  apply (member_transitive_member _ $ia $it).
  - apply weaken_one. exact HA.
  - apply (subset_member _ $ib $ia $it).
    + apply weaken_one. exact HS.
    + apply Ctx. now left.
Qed.

Lemma subset_member_linear G b a :
  G ⊢238 subset b a -> G ⊢238 member_linear a -> G ⊢238 member_linear b.
Proof.
  destruct b as [ib|[]], a as [ia|[]]. intros HS HA.
  unfold member_linear. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply II.
  apply (linear_member_cases _ $ia $ix $iy).
  - apply weaken_one. exact HA.
  - apply (subset_member _ $ib $ia $ix).
    + apply weaken_one. exact HS.
    + eapply CE1, Ctx. now left.
  - apply (subset_member _ $ib $ia $iy).
    + apply weaken_one. exact HS.
    + eapply CE2, Ctx. now left.
Qed.

Lemma subset_member_ir G b a :
  G ⊢238 subset b a -> G ⊢238 member_ir a -> G ⊢238 member_ir b.
Proof.
  destruct b as [ib|[]], a as [ia|[]]. intros HS HA.
  unfold member_ir. apply AllI_named. intro t. destruct t as [it|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp]. apply II.
  apply (member_ir_excludes_self _ $ia $it).
  - apply weaken_one. exact HA.
  - apply (subset_member _ $ib $ia $it).
    + apply weaken_one. exact HS.
    + apply Ctx. now left.
Qed.

Lemma internal_extrema_instance G a s :
  G ⊢238 internal_extrema a -> G ⊢238 subset s a -> G ⊢238 nonempty s ->
  G ⊢238 ((∃ least s`[↑] $0) ∧ (∃ greatest s`[↑] $0)).
Proof.
  destruct a as [ia|[]], s as [is|[]]. intros HA HS HN.
  unfold internal_extrema in HA. pose proof (AllE $is HA) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma subset_internal_extrema G b a :
  G ⊢238 subset b a -> G ⊢238 internal_extrema a -> G ⊢238 internal_extrema b.
Proof.
  destruct b as [ib|[]], a as [ia|[]]. intros HS HA.
  unfold internal_extrema. apply AllI_named. intro s. destruct s as [is|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply II.
  apply (internal_extrema_instance _ $ia $is).
  - apply weaken_one. exact HA.
  - apply (subset_transitive _ $is $ib $ia).
    + eapply CE1, Ctx. now left.
    + apply weaken_one. exact HS.
  - eapply CE2, Ctx. now left.
Qed.

(** Members of interpreted ordinals are interpreted ordinals.  The
    internal extrema clause is inherited by composing two subset proofs;
    this does not use an external finiteness argument or Replacement. *)
Theorem ordinal_member_closed G a b :
  G ⊢238 ordinal_representative a -> G ⊢238 R a b ->
  G ⊢238 ordinal_representative b.
Proof.
  intros HA HB.
  assert (HS : G ⊢238 subset b a).
  { apply member_subset; [exact (CE1 (CE1 HA))|exact HB]. }
  unfold ordinal_representative. apply CI.
  - unfold representative. apply CI.
    + apply (member_transitive_member _ a b);
        [exact (CE1 (CE2 (CE1 HA)))|exact HB].
    + apply CI.
      * apply (subset_member_transitive _ b a); [exact HS|].
        exact (CE1 (CE2 (CE1 HA))).
      * apply CI.
        -- apply (subset_member_linear _ b a); [exact HS|].
           exact (CE1 (CE2 (CE2 (CE1 HA)))).
        -- apply (subset_internal_extrema _ b a); [exact HS|].
           exact (CE2 (CE2 (CE2 (CE1 HA)))).
  - apply (subset_member_ir _ b a); [exact HS|exact (CE2 HA)].
Qed.

Definition ordinal_base (phi : set_form) : set_form :=
  ∀ ((ordinal_representative $0 ∧ raw_zero $0) → phi).
Definition ordinal_step (phi : set_form) : set_form :=
  ∀ ∀ ((ordinal_representative $1 ∧
          (ordinal_representative $0 ∧ raw_successor $1 $0)) →
         (phi[predecessor_slots] → phi[successor_slots])).

Lemma predecessor_slots_specialize (phi : set_form) (m b : set_term) :
  (phi[predecessor_slots])[up (m..)][b..] = phi[m..].
Proof.
  destruct m as [im|[]], b as [ib|[]]. rewrite !subst_comp.
  apply subst_ext. intros [|k];
    cbn [predecessor_slots up scons funcomp subst_term]; reflexivity.
Qed.

Lemma successor_slots_specialize (phi : set_form) (m b : set_term) :
  (phi[successor_slots])[up (m..)][b..] = phi[b..].
Proof.
  destruct m as [im|[]], b as [ib|[]]. rewrite !subst_comp.
  apply subst_ext. intros [|k];
    cbn [successor_slots up scons funcomp subst_term]; reflexivity.
Qed.

Lemma ordinal_base_instance G phi b :
  G ⊢238 ordinal_base phi -> G ⊢238 ordinal_representative b ->
  G ⊢238 raw_zero b -> G ⊢238 phi[b..].
Proof.
  destruct b as [ib|[]]. intros HB HR HZ. unfold ordinal_base in HB.
  pose proof (AllE $ib HB) as H.
  cbn [subst_form R E terms2 subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma ordinal_step_instance G phi m b :
  G ⊢238 ordinal_step phi -> G ⊢238 ordinal_representative m ->
  G ⊢238 ordinal_representative b -> G ⊢238 raw_successor m b ->
  G ⊢238 (phi[m..] → phi[b..]).
Proof.
  destruct m as [im|[]], b as [ib|[]]. intros HS HM HB Hsucc.
  unfold ordinal_step in HS. pose proof (AllE $ib (AllE $im HS)) as H.
  cbn [subst_form R E terms2 subst_term] in H.
  rewrite predecessor_slots_specialize, successor_slots_specialize in H.
  eapply IE; [exact H|]. apply CI; [exact HM|]. apply CI; assumption.
Qed.

Lemma bad_representative_not_zero G phi b :
  G ⊢238 ordinal_base phi -> G ⊢238 ordinal_representative b ->
  G ⊢238 (¬ phi[b..]) -> G ⊢238 (¬ raw_zero b).
Proof.
  intros HB HR Hbad. apply II. eapply IE.
  - apply weaken_one. exact Hbad.
  - apply (ordinal_base_instance _ phi b).
    + apply weaken_one. exact HB.
    + apply weaken_one. exact HR.
    + apply Ctx. now left.
Qed.

Lemma not_zero_nonempty G b : G ⊢238 (¬ raw_zero b) -> G ⊢238 nonempty b.
Proof.
  destruct b as [ib|[]]. intro HN. apply classical_double_negation, II.
  assert (HZ : (¬ nonempty $ib :: G) ⊢238 raw_zero $ib).
  { unfold raw_zero. apply AllI_named. intro t. destruct t as [it|[]].
    cbn [R terms2 subst_form subst_term up scons funcomp]. apply II.
    eapply IE.
    - apply weaken_one, Ctx. now left.
    - unfold nonempty. apply (ExI $it).
      cbn [R terms2 subst_form subst_term up scons funcomp].
      apply Ctx. now left. }
  eapply IE; [|exact HZ]. apply weaken_one. exact HN.
Qed.

Lemma subset_reflexivity G b : G ⊢238 subset b b.
Proof.
  destruct b as [ib|[]]. unfold subset.
  apply AllI_named. intro t. destruct t as [it|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp]. apply II, Ctx. now left.
Qed.

(** This completes the local least-bad-element argument using actual
    internal greatest-element witnesses and the parameter-full base/step
    formulas.  There is no hypothesis postulating a predecessor or a good
    predecessor: both are constructed by the finite proofs above.

    The global induction proof still must produce the nonempty bad trace,
    its least representative b, and its containing domain s from an
    arbitrary supposed counterexample. *)
Theorem ordinal_least_bad_contradiction G phi c s b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 ordinal_base phi ->
  G ⊢238 ordinal_step phi -> G ⊢238 ordinal_representative b ->
  G ⊢238 least c b -> G ⊢238 bad_trace c s phi ->
  G ⊢238 subset b s -> G ⊢238 falsity.
Proof.
  destruct b as [ib|[]]. intros HE HQ HEq HB HS HR HL HT Hsub.
  assert (Hbad : G ⊢238 (¬ phi[$ib..])).
  { apply (trace_member_bad _ c s phi $ib); [exact HT|exact (CE1 HL)]. }
  assert (HN : G ⊢238 nonempty $ib).
  { apply not_zero_nonempty. apply (bad_representative_not_zero _ phi $ib); assumption. }
  assert (HX : G ⊢238 ∃ greatest $ib`[↑] $0).
  { apply (ordinal_internal_greatest _ $ib $ib); [exact HR|apply subset_reflexivity|exact HN]. }
  eapply ExE_named; [exact HX|]. intro m. destruct m as [im|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  assert (HG : (greatest $ib $im :: G) ⊢238 greatest $ib $im).
  { apply Ctx. now left. }
  assert (Hm : (greatest $ib $im :: G) ⊢238 ordinal_representative $im).
  { apply (ordinal_member_closed _ $ib $im); [apply weaken_one; exact HR|exact (CE1 HG)]. }
  assert (Hsucc : (greatest $ib $im :: G) ⊢238 raw_successor $im $ib).
  { apply (greatest_raw_predecessor _ $ib $im).
    - apply weaken_one. exact HE.
    - apply weaken_one. exact HQ.
    - apply weaken_one. exact HEq.
    - apply weaken_one. exact (CE1 (CE1 HR)).
    - exact HG. }
  apply (strict_minimum_counterexample_contradiction _ c s $ib $im phi).
  - apply weaken_one. exact HE.
  - apply weaken_one. exact HQ.
  - apply weaken_one. exact (CE2 HR).
  - apply weaken_one. exact (CE1 (CE1 HR)).
  - exact (CE1 HG).
  - apply weaken_one. exact HL.
  - apply weaken_one. exact HT.
  - apply (subset_member _ $ib s $im); [apply weaken_one; exact Hsub|exact (CE1 HG)].
  - apply (ordinal_step_instance _ phi $im $ib).
    + apply weaken_one. exact HS.
    + exact Hm.
    + apply weaken_one. exact HR.
    + exact Hsucc.
Qed.

Lemma separation_false_empty G :
  G ⊢238 separation_ax falsity -> G ⊢238 empty_ax.
Proof.
  intro HS. unfold separation_ax in HS. pose proof (AllE $0 HS) as HX.
  cbn [R terms2 Vector.map subst_form subst_term up scons funcomp] in HX.
  eapply ExE_named; [exact HX|]. intro b. destruct b as [ib|[]].
  cbn [R terms2 Vector.map subst_form subst_term up scons funcomp].
  assert (HC :
    (∀ (R $(S ib) $0 ↔ (R $1 $0 ∧ falsity)) :: G) ⊢238
       ∀ (R $(S ib) $0 ↔ (R $1 $0 ∧ falsity))).
  { apply Ctx. now left. }
  unfold empty_ax. apply (ExI $ib). apply AllI_named.
  intro z. destruct z as [iz|[]].
  pose proof (AllE $iz HC) as Hinst.
  cbn [R terms2 Vector.map subst_form subst_term up scons funcomp] in Hinst.
  cbn [R terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply CE2, IE.
  - apply weaken_one. exact (CE1 Hinst).
  - apply Ctx. now left.
Qed.

Theorem S0_empty : derivable finite_set_S0 empty_ax.
Proof.
  destruct (S0_separation_instance 0 falsity ltac:(constructor)) as [G [HG HS]].
  exists G. split; [exact HG|]. apply separation_false_empty. exact HS.
Qed.

Lemma empty_domain_inhabited G :
  G ⊢238 empty_ax -> G ⊢238 ∃ ordinal_representative $0.
Proof.
  intro HE. unfold empty_ax in HE. eapply ExE_named; [exact HE|].
  intro a. destruct a as [ia|[]]. apply (ExI $ia).
  apply empty_ordinal_representative, Ctx. now left.
Qed.

(** An interpreted number actually exists in S0.  Empty Set itself is
    derived from the false-property Separation instance, so the finite
    context contains no extra Empty Set or IR axiom and no arithmetic
    totality/coherence premise. *)
Theorem S0_ordinal_domain_inhabited :
  derivable finite_set_S0 (∃ ordinal_representative $0).
Proof.
  destruct S0_empty as [G [HG HE]]. exists G. split; [exact HG|].
  apply empty_domain_inhabited. exact HE.
Qed.

(** Adjunction produces an actual raw successor witness for every object.
    Closure of this witness in the interpreted ordinal domain is a separate
    proof obligation; the theorem does not infer it from existence. *)
Lemma adjunction_raw_successor G a :
  G ⊢238 adjunction_ax -> G ⊢238 ∃ raw_successor a`[↑] $0.
Proof.
  destruct a as [ia|[]]. intro HA. unfold adjunction_ax in HA.
  pose proof (AllE $ia (AllE $ia HA)) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H. exact H.
Qed.

Theorem S0_raw_successor_exists a :
  derivable finite_set_S0 (∃ raw_successor a`[↑] $0).
Proof.
  exists [adjunction_ax]. split.
  - intros phi [<-|[]]. apply S0_base. apply in_or_app. right. now left.
  - apply adjunction_raw_successor, Ctx. now left.
Qed.

Lemma raw_successor_member_cases G a b z :
  G ⊢238 raw_successor a b -> G ⊢238 R b z -> G ⊢238 (R a z ∨ E z a).
Proof.
  destruct a as [ia|[]], b as [ib|[]], z as [iz|[]]. intros HS HZ.
  unfold raw_successor in HS. pose proof (AllE $iz HS) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE (CE1 H) HZ).
Qed.

Lemma member_ir_not_self G a : G ⊢238 member_ir a -> G ⊢238 (¬ R a a).
Proof.
  intro HI. apply II. apply (member_ir_refute _ a a).
  - apply weaken_one. exact HI.
  - apply Ctx. now left.
  - apply Ctx. now left.
Qed.

Lemma equality_self_member_transport G z a :
  G ⊢238 equality_membership_ax -> G ⊢238 E z a ->
  G ⊢238 R z z -> G ⊢238 R a a.
Proof.
  intros HQ Hza Hzz. eapply IE; [|exact Hzz].
  eapply IE; [|exact Hza]. eapply IE; [|exact Hza].
  apply equality_membership_instance. exact HQ.
Qed.

(** The strictness component of successor closure is local.  Old members
    inherit strictness from a; a new member equal to a would transport any
    self-membership to a, which the domain predicate already excludes. *)
Lemma raw_successor_member_ir G a b :
  G ⊢238 equality_membership_ax -> G ⊢238 member_ir a ->
  G ⊢238 raw_successor a b -> G ⊢238 member_ir b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HQ HI HS.
  unfold member_ir. apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_successor_member_cases _ $ia $ib $iz).
    + apply weaken_one. exact HS.
    + apply Ctx. now left.
  - apply (member_ir_excludes_self _ $ia $iz).
    + apply weaken_one, weaken_one. exact HI.
    + apply Ctx. now left.
  - apply II. eapply IE.
    + apply weaken_one, weaken_one, weaken_one.
      apply member_ir_not_self. exact HI.
    + apply (equality_self_member_transport _ $iz $ia).
      * apply weaken_one, weaken_one, weaken_one. exact HQ.
      * apply weaken_one, Ctx. now left.
      * apply Ctx. now left.
Qed.

Print Assumptions minimum_counterexample_contradiction.
Print Assumptions strict_minimum_counterexample_contradiction.
Print Assumptions S0_bad_trace_exists.
Print Assumptions compact_empty.
Print Assumptions empty_ordinal_representative.
Print Assumptions greatest_raw_predecessor.
Print Assumptions ordinal_member_closed.
Print Assumptions ordinal_least_bad_contradiction.
Print Assumptions S0_ordinal_domain_inhabited.
Print Assumptions S0_raw_successor_exists.
Print Assumptions raw_successor_member_ir.

End PAinCompact238.
