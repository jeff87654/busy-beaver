(* Original finite ordinary-PA arithmetic for the literal Ackermann bit.
   A full bit period is p+p.  The backward direction removes a successor
   quotient by cancellation and excludes a zero quotient by r<p. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAEqCongruence238 PAOrder238 PAOrderGrowth238 PAOrderBounds238
  PAQuotient238 PARemainderUnique238 CompactInPA238 PAPowerTrace238
  PAPowerBound238 PABitPosition238 PAMultiplicationComm238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAOrder238 PAOrderGrowth238 PAOrderBounds238
  PAQuotient238 PARemainderUnique238 CompactInPA238 PAPowerTrace238
  PAPowerBound238 PABitPosition238 PAMultiplicationComm238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PABitPeriodic238.

Definition periodic_context : list pa_form :=
  List.cons add_commutativity_sentence bit_context.
Definition has_periodic_context (G : list pa_form) : Prop :=
  forall phi, List.In phi periodic_context -> List.In phi G.
Lemma periodic_proof phi : periodic_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := add_commutativity_sentence).
  - apply bit_proof, II. exact HD.
  - exact add_commutative.
Qed.
Lemma periodic_context_self : has_periodic_context periodic_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_periodic_cons G phi : has_periodic_context G ->
  has_periodic_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma periodic_has_bit G : has_periodic_context G -> has_bit_context G.
Proof. intros HG phi Hphi. apply HG. unfold periodic_context. now right. Qed.
Lemma periodic_has_quotient G : has_periodic_context G -> has_quotient_context G.
Proof. intros HG. apply trace_has_quotient, bit_has_trace, periodic_has_bit. exact HG. Qed.
Lemma periodic_equality G : has_periodic_context G -> has_equality G.
Proof. intros HG. apply quotient_has_equality, periodic_has_quotient. exact HG. Qed.
Lemma periodic_reflexivity G a : has_periodic_context G -> G ⊢C (a == a).
Proof. intros HG. apply reflexivity_instance, periodic_equality. exact HG. Qed.
Lemma periodic_symmetry G a b : has_periodic_context G ->
  G ⊢C (a == b) -> G ⊢C (b == a).
Proof. intros HG H. exact (equality_symmetry G a b (periodic_equality G HG) H). Qed.
Lemma periodic_transitivity G a b c : has_periodic_context G ->
  G ⊢C (a == b) -> G ⊢C (b == c) -> G ⊢C (a == c).
Proof. intros HG H K. exact (equality_transitivity G a b c (periodic_equality G HG) H K). Qed.
Lemma periodic_addition G a b c d : has_periodic_context G ->
  G ⊢C (a == b) -> G ⊢C (c == d) -> G ⊢C (a ⊕ c == b ⊕ d).
Proof.
  intros HG H K. exact (IE (IE (addition_instance G a b c d (periodic_equality G HG)) H) K).
Qed.
Lemma periodic_associative G a b c : has_periodic_context G ->
  G ⊢C (a ⊕ (b ⊕ c) == (a ⊕ b) ⊕ c).
Proof.
  intros HG. apply associativity_instance.
  exact (periodic_has_quotient G HG associativity_sentence quotient_associative).
Qed.
Lemma periodic_commutative G a b : has_periodic_context G ->
  G ⊢C (a ⊕ b == b ⊕ a).
Proof.
  intros HG. apply add_commutative_at, HG. unfold periodic_context. now left.
Qed.
Lemma periodic_exchange G a b c : has_periodic_context G ->
  G ⊢C (a ⊕ (b ⊕ c) == b ⊕ (a ⊕ c)).
Proof.
  intros HG.
  pose proof (periodic_associative G a b c HG) as H1.
  pose proof (periodic_addition G (a ⊕ b) (b ⊕ a) c c HG
    (periodic_commutative G a b HG) (periodic_reflexivity G c HG)) as H2.
  pose proof (periodic_symmetry G (b ⊕ (a ⊕ c)) ((b ⊕ a) ⊕ c) HG
    (periodic_associative G b a c HG)) as H3.
  exact (periodic_transitivity G (a ⊕ (b ⊕ c)) ((a ⊕ b) ⊕ c)
    (b ⊕ (a ⊕ c)) HG H1
    (periodic_transitivity G ((a ⊕ b) ⊕ c) ((b ⊕ a) ⊕ c)
      (b ⊕ (a ⊕ c)) HG H2 H3)).
Qed.
Lemma periodic_cancel G m a b : has_periodic_context G ->
  G ⊢C (m ⊕ a == m ⊕ b) -> G ⊢C (a == b).
Proof.
  intros HG H. exact (IE (cancellation_instance G m a b
    (periodic_has_quotient G HG cancellation_sentence quotient_cancellation)) H).
Qed.
Lemma bit_tail_introduce G a p q r :
  G ⊢C bit_pair a p q r -> G ⊢C bit_tail a p.
Proof.
  intros H. unfold bit_tail. apply (ExI q). cbn [subst_form].
  rewrite bit_pair_subst, !up_term, !subst_term_shift.
  apply (ExI r). rewrite bit_pair_subst, !subst_term_shift.
  cbn [up scons subst_term funcomp].
  rewrite !subst_term_shift. exact H.
Qed.
Lemma bit_tail_transport G a b p : has_periodic_context G ->
  G ⊢C (a == b) -> G ⊢C bit_tail a p -> G ⊢C bit_tail b p.
Proof.
  intros HG HE HT.
  pose proof (formula_substitutivity G (bit_tail $0 p`[↑]) a b
    (periodic_equality G HG) HE) as H.
  rewrite !bit_tail_subst, !subst_term_shift in H. exact (IE (CE1 H) HT).
Qed.
Lemma bit_row_flat G q p r : has_periodic_context G ->
  G ⊢C (bit_row q p r == quotient_row q (p ⊕ p) (p ⊕ r)).
Proof.
  intros HG. unfold bit_row, quotient_row.
  exact (periodic_symmetry G ((q ⊗ (p ⊕ p)) ⊕ (p ⊕ r))
    (((q ⊗ (p ⊕ p)) ⊕ p) ⊕ r) HG
    (periodic_associative G (q ⊗ (p ⊕ p)) p r HG)).
Qed.
Lemma bit_row_zero G p r : has_periodic_context G ->
  G ⊢C (bit_row zero p r == p ⊕ r).
Proof.
  intros HG. exact (periodic_transitivity G (bit_row zero p r)
    (quotient_row zero (p ⊕ p) (p ⊕ r)) (p ⊕ r) HG
    (bit_row_flat G zero p r HG) (row_zero G (p ⊕ p) (p ⊕ r)
      (periodic_has_quotient G HG))).
Qed.
Lemma bit_row_successor G q p r : has_periodic_context G ->
  G ⊢C (bit_row (σ q) p r == (p ⊕ p) ⊕ bit_row q p r).
Proof.
  intros HG. pose proof (periodic_has_quotient G HG) as HQ.
  pose proof (bit_row_flat G (σ q) p r HG) as H1.
  pose proof (row_successor G q (p ⊕ p) (p ⊕ r) HQ) as H2.
  pose proof (periodic_symmetry G (bit_row q p r)
    (quotient_row q (p ⊕ p) (p ⊕ r)) HG (bit_row_flat G q p r HG)) as Hflat.
  pose proof (periodic_addition G (p ⊕ p) (p ⊕ p)
    (quotient_row q (p ⊕ p) (p ⊕ r)) (bit_row q p r) HG
    (periodic_reflexivity G (p ⊕ p) HG) Hflat) as H3.
  exact (periodic_transitivity G (bit_row (σ q) p r)
    (quotient_row (σ q) (p ⊕ p) (p ⊕ r)) ((p ⊕ p) ⊕ bit_row q p r) HG H1
    (periodic_transitivity G (quotient_row (σ q) (p ⊕ p) (p ⊕ r))
      ((p ⊕ p) ⊕ quotient_row q (p ⊕ p) (p ⊕ r))
      ((p ⊕ p) ⊕ bit_row q p r) HG H2 H3)).
Qed.
Lemma bit_row_quotient_transport G q t p r : has_periodic_context G ->
  G ⊢C (q == t) -> G ⊢C (bit_row q p r == bit_row t p r).
Proof.
  intros HG Hqt.
  pose proof (row_quotient_congr G q t (p ⊕ p) (p ⊕ r)
    (periodic_has_quotient G HG) Hqt) as H2.
  exact (periodic_transitivity G (bit_row q p r)
    (quotient_row q (p ⊕ p) (p ⊕ r)) (bit_row t p r) HG
    (bit_row_flat G q p r HG)
    (periodic_transitivity G (quotient_row q (p ⊕ p) (p ⊕ r))
      (quotient_row t (p ⊕ p) (p ⊕ r)) (bit_row t p r) HG H2
      (periodic_symmetry G (bit_row t p r)
        (quotient_row t (p ⊕ p) (p ⊕ r)) HG (bit_row_flat G t p r HG)))).
Qed.

Lemma bit_period_forward G a p : has_periodic_context G ->
  G ⊢C bit_tail a p -> G ⊢C bit_tail (a ⊕ (p ⊕ p)) p.
Proof.
  intros HG HT. eapply bit_tail_eliminate; [exact HT|]. intros q r.
  set (D := List.cons (bit_pair a p q r) G).
  change (D ⊢C bit_tail (a ⊕ (p ⊕ p)) p).
  assert (HD : has_periodic_context D).
  { unfold D. apply has_periodic_cons. exact HG. }
  assert (HC : D ⊢C bit_pair a p q r).
  { apply Ctx. unfold D. now left. }
  apply (bit_tail_introduce D (a ⊕ (p ⊕ p)) p (σ q) r).
  unfold bit_pair. apply CI; [|exact (CE2 HC)].
  pose proof (periodic_addition D a (bit_row q p r) (p ⊕ p) (p ⊕ p) HD
    (CE1 HC) (periodic_reflexivity D (p ⊕ p) HD)) as H1.
  pose proof (periodic_commutative D (bit_row q p r) (p ⊕ p) HD) as H2.
  pose proof (periodic_symmetry D (bit_row (σ q) p r)
    ((p ⊕ p) ⊕ bit_row q p r) HD (bit_row_successor D q p r HD)) as H3.
  exact (periodic_transitivity D (a ⊕ (p ⊕ p)) ((bit_row q p r) ⊕ (p ⊕ p))
    (bit_row (σ q) p r) HD H1
    (periodic_transitivity D ((bit_row q p r) ⊕ (p ⊕ p))
      ((p ⊕ p) ⊕ bit_row q p r) (bit_row (σ q) p r) HD H2 H3)).
Qed.
Lemma bit_period_backward G a p : has_periodic_context G ->
  G ⊢C bit_tail (a ⊕ (p ⊕ p)) p -> G ⊢C bit_tail a p.
Proof.
  intros HG HT. eapply bit_tail_eliminate; [exact HT|]. intros q r.
  set (D := List.cons (bit_pair (a ⊕ (p ⊕ p)) p q r) G).
  change (D ⊢C bit_tail a p).
  assert (HD : has_periodic_context D).
  { unfold D. apply has_periodic_cons. exact HG. }
  assert (HC : D ⊢C bit_pair (a ⊕ (p ⊕ p)) p q r).
  { apply Ctx. unfold D. now left. }
  pose proof (predecessor_at D q (periodic_has_quotient D HD)) as Hq.
  eapply DE; [exact Hq| |].
  - set (E := List.cons (q == zero) D).
    change (E ⊢C bit_tail a p). apply Exp.
    assert (HE : has_periodic_context E).
    { unfold E. apply has_periodic_cons. exact HD. }
    assert (Hz : E ⊢C (q == zero)).
    { apply Ctx. unfold E. now left. }
    pose proof (weaken_head D (bit_pair (a ⊕ (p ⊕ p)) p q r) (q == zero) HC) as HCE.
    pose proof (periodic_transitivity E (bit_row q p r) (bit_row zero p r) (p ⊕ r) HE
      (bit_row_quotient_transport E q zero p r HE Hz) (bit_row_zero E p r HE)) as Hrow.
    pose proof (periodic_transitivity E (a ⊕ (p ⊕ p)) (bit_row q p r) (p ⊕ r) HE
      (CE1 HCE) Hrow) as Hbad.
    pose proof (periodic_transitivity E (a ⊕ (p ⊕ p)) ((a ⊕ p) ⊕ p)
      (p ⊕ (a ⊕ p)) HE (periodic_associative E a p p HE)
      (periodic_commutative E (a ⊕ p) p HE)) as Hfront.
    pose proof (periodic_transitivity E (p ⊕ (a ⊕ p)) (a ⊕ (p ⊕ p))
      (p ⊕ r) HE (periodic_symmetry E (a ⊕ (p ⊕ p)) (p ⊕ (a ⊕ p)) HE Hfront)
      Hbad) as Hcancel.
    pose proof (periodic_cancel E p (a ⊕ p) r HE Hcancel) as Hapr.
    pose proof (right_bound_at E a p (periodic_has_bit E HE)) as Hlower.
    pose proof (weak_upper_transport E p (a ⊕ p) r (periodic_has_bit E HE) Hlower Hapr) as Hpr.
    pose proof (IE (IE (strict_weak_at E r p r (periodic_has_quotient E HE)) (CE2 HCE)) Hpr) as Hrr.
    exact (IE (order_ir_at E r (periodic_has_quotient E HE)) Hrr).
  - eapply predecessor_eliminate; [apply Ctx; unfold D; now left|]. intros t.
    set (E := List.cons (q == σ t) (List.cons (∃ (q`[↑] == σ $0)) D)).
    change (E ⊢C bit_tail a p).
    assert (HE : has_periodic_context E).
    { unfold E. apply has_periodic_cons, has_periodic_cons. exact HD. }
    assert (Hqt : E ⊢C (q == σ t)).
    { apply Ctx. unfold E. now left. }
    assert (HCE : E ⊢C bit_pair (a ⊕ (p ⊕ p)) p q r).
    { apply Ctx. unfold E, D. right. right. now left. }
    pose proof (periodic_transitivity E (bit_row q p r) (bit_row (σ t) p r)
      ((p ⊕ p) ⊕ bit_row t p r) HE
      (bit_row_quotient_transport E q (σ t) p r HE Hqt)
      (bit_row_successor E t p r HE)) as Hrow.
    pose proof (periodic_transitivity E (a ⊕ (p ⊕ p)) (bit_row q p r)
      ((p ⊕ p) ⊕ bit_row t p r) HE (CE1 HCE) Hrow) as Hbad.
    pose proof (periodic_transitivity E ((p ⊕ p) ⊕ a) (a ⊕ (p ⊕ p))
      ((p ⊕ p) ⊕ bit_row t p r) HE (periodic_commutative E (p ⊕ p) a HE) Hbad) as Hcancel.
    apply (bit_tail_introduce E a p t r). unfold bit_pair. apply CI.
    + exact (periodic_cancel E (p ⊕ p) a (bit_row t p r) HE Hcancel).
    + exact (CE2 HCE).
Qed.
Theorem bit_full_period : paeq_derivable (∀ ∀
  (bit_tail $0 $1 ↔ bit_tail ($0 ⊕ ($1 ⊕ $1)) $1)).
Proof.
  apply paeq_generalize, paeq_generalize, periodic_proof, CI.
  - apply II. set (G := List.cons (bit_tail $0 $1) periodic_context).
    apply (bit_period_forward G $0 $1).
    + unfold G. apply has_periodic_cons. exact periodic_context_self.
    + apply Ctx. unfold G. now left.
  - apply II. set (G := List.cons (bit_tail ($0 ⊕ ($1 ⊕ $1)) $1) periodic_context).
    apply (bit_period_backward G $0 $1).
    + unfold G. apply has_periodic_cons. exact periodic_context_self.
    + apply Ctx. unfold G. now left.
Qed.

Lemma bit_at_new_position G a p : has_periodic_context G ->
  G ⊢C (a ⧀ p) -> G ⊢C bit_tail (a ⊕ p) p.
Proof.
  intros HG HA. apply (bit_tail_introduce G (a ⊕ p) p zero a).
  unfold bit_pair. apply CI; [|exact HA].
  exact (periodic_transitivity G (a ⊕ p) (p ⊕ a) (bit_row zero p a) HG
    (periodic_commutative G a p HG)
    (periodic_symmetry G (bit_row zero p a) (p ⊕ a) HG (bit_row_zero G p a HG))).
Qed.
Lemma bit_tail_above_code G a p : has_periodic_context G ->
  G ⊢C (a ⧀ p) -> G ⊢C ¬ bit_tail a p.
Proof.
  intros HG HA. apply II.
  set (D := List.cons (bit_tail a p) G).
  assert (HD : has_periodic_context D).
  { unfold D. apply has_periodic_cons. exact HG. }
  assert (HT : D ⊢C bit_tail a p).
  { apply Ctx. unfold D. now left. }
  eapply bit_tail_eliminate; [exact HT|]. intros q r.
  set (E := List.cons (bit_pair a p q r) D).
  change (E ⊢C falsity).
  assert (HE : has_periodic_context E).
  { unfold E. apply has_periodic_cons. exact HD. }
  assert (HC : E ⊢C bit_pair a p q r).
  { apply Ctx. unfold E. now left. }
  pose proof (bit_row_lower E q p r (periodic_has_bit E HE)) as HB.
  pose proof (periodic_symmetry E a (bit_row q p r) HE (CE1 HC)) as Hback.
  pose proof (weak_upper_transport E p (bit_row q p r) a (periodic_has_bit E HE) HB Hback) as Hpa.
  pose proof (weaken_head D (a ⧀ p) (bit_pair a p q r)
    (weaken_head G (a ⧀ p) (bit_tail a p) HA)) as HAE.
  exact (IE (order_ir_at E a (periodic_has_quotient E HE))
    (IE (IE (strict_weak_at E a p a (periodic_has_quotient E HE)) HAE) Hpa)).
Qed.


Lemma bit_tail_equivalence G a b p : has_periodic_context G ->
  G ⊢C (a == b) -> G ⊢C (bit_tail a p ↔ bit_tail b p).
Proof.
  intros HG HE.
  pose proof (formula_substitutivity G (bit_tail $0 p`[↑]) a b
    (periodic_equality G HG) HE) as H.
  rewrite !bit_tail_subst, !subst_term_shift in H. exact H.
Qed.
Lemma periodic_equivalence_transitive (G : list pa_form) (phi psi chi : pa_form) :
  G ⊢C (phi ↔ psi) -> G ⊢C (psi ↔ chi) -> G ⊢C (phi ↔ chi).
Proof.
  intros HP HQ. apply CI.
  - apply II. assert (Hphi : (List.cons phi G) ⊢C phi).
    { apply Ctx. now left. }
    exact (IE (weaken_head G (psi → chi) phi (CE1 HQ))
      (IE (weaken_head G (phi → psi) phi (CE1 HP)) Hphi)).
  - apply II. assert (Hchi : (List.cons chi G) ⊢C chi).
    { apply Ctx. now left. }
    exact (IE (weaken_head G (psi → phi) chi (CE2 HP))
      (IE (weaken_head G (chi → psi) chi (CE2 HQ)) Hchi)).
Qed.

Definition multiple_matrix (h a p : pa_term) : pa_form :=
  bit_tail a p ↔ bit_tail (a ⊕ (h ⊗ (p ⊕ p))) p.
Definition multiple_property (h : pa_term) : pa_form :=
  ∀ ∀ multiple_matrix h`[↑]`[↑] $1 $0.
Lemma multiple_matrix_subst h a p rho :
  (multiple_matrix h a p)[rho] = multiple_matrix h`[rho] a`[rho] p`[rho].
Proof.
  unfold multiple_matrix. cbn [subst_form]. rewrite !bit_tail_subst. reflexivity.
Qed.
Lemma multiple_property_subst h rho :
  (multiple_property h)[rho] = multiple_property h`[rho].
Proof.
  unfold multiple_property. cbn [subst_form]. rewrite multiple_matrix_subst.
  now rewrite !up_term.
Qed.
Lemma multiple_first_instance h a :
  (∀ multiple_matrix h`[↑]`[↑] $1 $0)[a..] =
  ∀ multiple_matrix h`[↑] a`[↑] $0.
Proof.
  cbn [subst_form]. rewrite multiple_matrix_subst, !up_term, !subst_term_shift.
  reflexivity.
Qed.
Lemma multiple_property_introduce G h :
  (forall a p, G ⊢C multiple_matrix h a p) -> G ⊢C multiple_property h.
Proof.
  intros H. unfold multiple_property. apply AllI_named. intros a.
  rewrite multiple_first_instance. apply AllI_named. intros p.
  rewrite multiple_matrix_subst, !subst_term_shift. exact (H a p).
Qed.
Lemma multiple_property_at G h a p :
  G ⊢C multiple_property h -> G ⊢C multiple_matrix h a p.
Proof.
  intros H. pose proof (AllE a H) as H1. rewrite multiple_first_instance in H1.
  pose proof (AllE p H1) as H2.
  rewrite multiple_matrix_subst, !subst_term_shift in H2. exact H2.
Qed.
Lemma bit_period_equivalence G a p : has_periodic_context G ->
  G ⊢C (bit_tail a p ↔ bit_tail (a ⊕ (p ⊕ p)) p).
Proof.
  intros HG. apply CI.
  - apply II. set (D := List.cons (bit_tail a p) G).
    apply (bit_period_forward D a p).
    + unfold D. apply has_periodic_cons. exact HG.
    + apply Ctx. unfold D. now left.
  - apply II. set (D := List.cons (bit_tail (a ⊕ (p ⊕ p)) p) G).
    apply (bit_period_backward D a p).
    + unfold D. apply has_periodic_cons. exact HG.
    + apply Ctx. unfold D. now left.
Qed.
Definition multiple_formula : pa_form := multiple_property $0.
Lemma bit_multiple_base : paeq_derivable multiple_formula[zero..].
Proof.
  unfold multiple_formula. rewrite multiple_property_subst.
  apply periodic_proof, multiple_property_introduce. intros a p.
  unfold multiple_matrix. apply bit_tail_equivalence; [exact periodic_context_self|].
  pose proof (periodic_has_quotient periodic_context periodic_context_self) as HQ.
  pose proof (mult_zero_instance periodic_context (p ⊕ p)
    (HQ ax_mult_zero quotient_mult_zero)) as Hzero.
  pose proof (periodic_addition periodic_context a a (zero ⊗ (p ⊕ p)) zero
    periodic_context_self (periodic_reflexivity periodic_context a periodic_context_self) Hzero) as H1.
  pose proof (PAOrderGrowth238.right_zero_at periodic_context a HQ) as H2.
  apply periodic_symmetry; [exact periodic_context_self|].
  exact (periodic_transitivity periodic_context (a ⊕ (zero ⊗ (p ⊕ p)))
    (a ⊕ zero) a periodic_context_self H1 H2).
Qed.
Lemma bit_multiple_step : paeq_derivable
  (∀ (multiple_formula → multiple_formula[σ $0 .: S >> var])).
Proof.
  unfold multiple_formula. rewrite multiple_property_subst.
  change (paeq_derivable (∀ (multiple_property $0 → multiple_property (σ $0)))).
  apply paeq_generalize, periodic_proof, II, multiple_property_introduce.
  intros a p.
  set (G := List.cons (multiple_property $0) periodic_context).
  change (G ⊢C multiple_matrix (σ $0) a p).
  assert (HG : has_periodic_context G).
  { unfold G. apply has_periodic_cons. exact periodic_context_self. }
  assert (HI : G ⊢C multiple_property $0).
  { apply Ctx. unfold G. now left. }
  pose proof (multiple_property_at G $0 a p HI) as Hind.
  set (m := p ⊕ p). set (o := $0 ⊗ m).
  pose proof (mult_rec_instance G $0 m
    (periodic_has_quotient G HG ax_mult_rec quotient_mult_rec)) as Hrec.
  pose proof (periodic_addition G a a (σ $0 ⊗ m) (m ⊕ o) HG
    (periodic_reflexivity G a HG) Hrec) as H1.
  pose proof (periodic_addition G a a (m ⊕ o) (o ⊕ m) HG
    (periodic_reflexivity G a HG) (periodic_commutative G m o HG)) as H2.
  pose proof (periodic_associative G a o m HG) as H3.
  pose proof (periodic_transitivity G (a ⊕ (σ $0 ⊗ m)) (a ⊕ (m ⊕ o))
    ((a ⊕ o) ⊕ m) HG H1
    (periodic_transitivity G (a ⊕ (m ⊕ o)) (a ⊕ (o ⊕ m)) ((a ⊕ o) ⊕ m) HG H2 H3)) as Hterm.
  pose proof (bit_tail_equivalence G ((a ⊕ o) ⊕ m) (a ⊕ (σ $0 ⊗ m)) p HG
    (periodic_symmetry G (a ⊕ (σ $0 ⊗ m)) ((a ⊕ o) ⊕ m) HG Hterm)) as Hlast.
  pose proof (bit_period_equivalence G (a ⊕ o) p HG) as Hperiod.
  unfold multiple_matrix in Hind |- *.
  exact (periodic_equivalence_transitive G (bit_tail a p) (bit_tail (a ⊕ o) p)
    (bit_tail (a ⊕ (σ $0 ⊗ m)) p) Hind
    (periodic_equivalence_transitive G (bit_tail (a ⊕ o) p)
      (bit_tail ((a ⊕ o) ⊕ m) p) (bit_tail (a ⊕ (σ $0 ⊗ m)) p) Hperiod Hlast)).
Qed.
Theorem bit_multiple_period : paeq_derivable (∀ ∀ ∀
  (bit_tail $1 $0 ↔ bit_tail ($1 ⊕ ($2 ⊗ ($0 ⊕ $0))) $0)).
Proof.
  change (paeq_derivable (∀ multiple_formula)).
  apply (paeq_induction_rule multiple_formula).
  - exact bit_multiple_base.
  - exact bit_multiple_step.
Qed.

End PABitPeriodic238.

Print Assumptions PABitPeriodic238.bit_full_period.
Print Assumptions PABitPeriodic238.bit_at_new_position.
Print Assumptions PABitPeriodic238.bit_tail_above_code.

Print Assumptions PABitPeriodic238.bit_multiple_period.
