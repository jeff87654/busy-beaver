(* Original finite ordinary-PA binary CRT merge certificates.
   The candidate and both quotient witnesses are literal PA terms.
   Every algebraic rearrangement uses finite PA equality derivations. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAAddition238 PAEqCongruence238
  PASemiring238 PAMultiplicationComm238 PAModuliInverse238 CompactInPA238
  PAQuotient238 PAPowerExtension238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PASemiring238
  PAMultiplicationComm238 PAModuliInverse238 CompactInPA238 PAQuotient238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PACRTMerge238.

Lemma merge_add_last_exchange G a b c : has_inverse_context G ->
  G ⊢C ((a ⊕ b) ⊕ c == (a ⊕ c) ⊕ b).
Proof.
  intros HG.
  pose proof (inverse_symmetry G (a ⊕ (b ⊕ c)) ((a ⊕ b) ⊕ c) HG
    (inverse_add_associative G a b c HG)) as Hfirst.
  pose proof (inverse_addition G a a (b ⊕ c) (c ⊕ b) HG
    (inverse_reflexivity G a HG) (inverse_add_commutative G b c HG)) as Hsecond.
  pose proof (inverse_transitivity G ((a ⊕ b) ⊕ c) (a ⊕ (b ⊕ c))
    (a ⊕ (c ⊕ b)) HG Hfirst Hsecond) as Hfront.
  exact (inverse_transitivity G ((a ⊕ b) ⊕ c) (a ⊕ (c ⊕ b)) ((a ⊕ c) ⊕ b)
    HG Hfront (inverse_add_associative G a c b HG)).
Qed.
Lemma merge_mul_last_exchange G a b c : has_inverse_context G ->
  G ⊢C ((a ⊗ b) ⊗ c == (a ⊗ c) ⊗ b).
Proof.
  intros HG.
  pose proof (inverse_mul_associative G a b c HG) as Hfirst.
  pose proof (inverse_multiplication G a a (b ⊗ c) (c ⊗ b) HG
    (inverse_reflexivity G a HG) (inverse_mul_commutative G b c HG)) as Hsecond.
  pose proof (inverse_symmetry G ((a ⊗ c) ⊗ b) (a ⊗ (c ⊗ b)) HG
    (inverse_mul_associative G a c b HG)) as Hthird.
  pose proof (inverse_transitivity G ((a ⊗ b) ⊗ c) (a ⊗ (b ⊗ c))
    (a ⊗ (c ⊗ b)) HG Hfirst Hsecond) as Hfront.
  exact (inverse_transitivity G ((a ⊗ b) ⊗ c) (a ⊗ (c ⊗ b)) ((a ⊗ c) ⊗ b)
    HG Hfront Hthird).
Qed.
Lemma merge_successor_one_sum G a : has_inverse_context G ->
  G ⊢C (σ a == σ zero ⊕ a).
Proof.
  intros HG. pose proof (inverse_has_product G HG) as HP.
  pose proof (PAOrder238.add_rec_instance G zero a (HP ax_add_rec product_add_rec)) as Hfirst.
  pose proof (PAAddition238.add_zero_instance G a (HP ax_add_zero product_add_zero)) as Hzero.
  pose proof (IE (successor_instance G (zero ⊕ a) a (inverse_equality G HG)) Hzero) as Hsecond.
  pose proof (inverse_transitivity G (σ zero ⊕ a) (σ (zero ⊕ a)) (σ a)
    HG Hfirst Hsecond) as Hsum.
  exact (inverse_symmetry G (σ zero ⊕ a) (σ a) HG Hsum).
Qed.

Definition crt_candidate (A x P a v : pa_term) : pa_term :=
  A ⊕ ((x ⊗ P) ⊗ (v ⊕ (a ⊗ A))).
Definition crt_old_offset (A x a v : pa_term) : pa_term := x ⊗ (v ⊕ (a ⊗ A)).
Definition crt_new_quotient (A y a v : pa_term) : pa_term :=
  ((y ⊗ v) ⊕ A) ⊕ ((a ⊗ y) ⊗ A).
Lemma candidate_old_offset G A x P a v : has_inverse_context G ->
  G ⊢C (crt_candidate A x P a v == A ⊕ (crt_old_offset A x a v ⊗ P)).
Proof.
  intros HG. unfold crt_candidate, crt_old_offset.
  exact (inverse_addition G A A ((x ⊗ P) ⊗ (v ⊕ (a ⊗ A)))
    ((x ⊗ (v ⊕ (a ⊗ A))) ⊗ P) HG (inverse_reflexivity G A HG)
    (merge_mul_last_exchange G x P (v ⊕ (a ⊗ A)) HG)).
Qed.

Lemma candidate_new_row G A x P a v y : has_inverse_context G ->
  G ⊢C (x ⊗ P == (y ⊗ σ a) ⊕ σ zero) ->
  G ⊢C (crt_candidate A x P a v == (crt_new_quotient A y a v ⊗ σ a) ⊕ v).
Proof.
  intros HG Hinv. set (M := σ a). set (B := a ⊗ A).
  set (T := v ⊕ B). set (U := (y ⊗ M) ⊗ T).
  pose proof (inverse_multiplication G (x ⊗ P) ((y ⊗ M) ⊕ σ zero) T T HG
    Hinv (inverse_reflexivity G T HG)) as HinvT.
  pose proof (inverse_addition G A A ((x ⊗ P) ⊗ T)
    (((y ⊗ M) ⊕ σ zero) ⊗ T) HG (inverse_reflexivity G A HG) HinvT) as Hfirst.
  pose proof (inverse_left_distribution G (y ⊗ M) (σ zero) T HG) as HDfirst.
  pose proof (inverse_addition G U U (σ zero ⊗ T) T HG
    (inverse_reflexivity G U HG) (inverse_left_one G T HG)) as HDsecond.
  pose proof (inverse_transitivity G (((y ⊗ M) ⊕ σ zero) ⊗ T)
    (U ⊕ (σ zero ⊗ T)) (U ⊕ T) HG HDfirst HDsecond) as HD.
  pose proof (inverse_addition G A A (((y ⊗ M) ⊕ σ zero) ⊗ T)
    (U ⊕ T) HG (inverse_reflexivity G A HG) HD) as Hsecond.
  pose proof (inverse_addition G A A (U ⊕ (v ⊕ B)) (v ⊕ (U ⊕ B)) HG
    (inverse_reflexivity G A HG) (add_exchange G U v B (inverse_has_addition G HG))) as Hthird.
  pose proof (add_exchange G A v (U ⊕ B) (inverse_has_addition G HG)) as Hfourth.
  pose proof (inverse_addition G v v (A ⊕ (U ⊕ B)) (U ⊕ (A ⊕ B)) HG
    (inverse_reflexivity G v HG) (add_exchange G A U B (inverse_has_addition G HG))) as Hfifth.
  pose proof (inverse_left_distribution G (σ zero) a A HG) as HBfirst.
  pose proof (inverse_addition G (σ zero ⊗ A) A B B HG
    (inverse_left_one G A HG) (inverse_reflexivity G B HG)) as HBsecond.
  pose proof (inverse_transitivity G ((σ zero ⊕ a) ⊗ A)
    ((σ zero ⊗ A) ⊕ B) (A ⊕ B) HG HBfirst HBsecond) as HBforward.
  pose proof (inverse_symmetry G ((σ zero ⊕ a) ⊗ A) (A ⊕ B) HG HBforward) as HBback.
  pose proof (inverse_symmetry G M (σ zero ⊕ a) HG
    (merge_successor_one_sum G a HG)) as HMback.
  pose proof (inverse_multiplication G (σ zero ⊕ a) M A A HG HMback
    (inverse_reflexivity G A HG)) as HBthird.
  pose proof (inverse_transitivity G (A ⊕ B) ((σ zero ⊕ a) ⊗ A)
    (M ⊗ A) HG HBback HBthird) as HB.
  pose proof (inverse_mul_associative G y M T HG) as HUfirst.
  pose proof (inverse_mul_exchange G y M T HG) as HUsecond.
  pose proof (inverse_transitivity G U (y ⊗ (M ⊗ T))
    (M ⊗ (y ⊗ T)) HG HUfirst HUsecond) as HU.
  pose proof (inverse_addition G U (M ⊗ (y ⊗ T)) (A ⊕ B) (M ⊗ A) HG HU HB) as Hinside.
  pose proof (inverse_symmetry G (M ⊗ ((y ⊗ T) ⊕ A))
    ((M ⊗ (y ⊗ T)) ⊕ (M ⊗ A)) HG
    (inverse_right_distribution G M (y ⊗ T) A HG)) as Hfactor.
  pose proof (inverse_transitivity G (U ⊕ (A ⊕ B))
    ((M ⊗ (y ⊗ T)) ⊕ (M ⊗ A)) (M ⊗ ((y ⊗ T) ⊕ A)) HG Hinside Hfactor) as Hinner.
  pose proof (inverse_addition G v v (U ⊕ (A ⊕ B)) (M ⊗ ((y ⊗ T) ⊕ A)) HG
    (inverse_reflexivity G v HG) Hinner) as Hsixth.
  pose proof (inverse_addition G v v (M ⊗ ((y ⊗ T) ⊕ A)) (((y ⊗ T) ⊕ A) ⊗ M) HG
    (inverse_reflexivity G v HG) (inverse_mul_commutative G M ((y ⊗ T) ⊕ A) HG)) as Hseventh.
  pose proof (inverse_add_commutative G v (((y ⊗ T) ⊕ A) ⊗ M) HG) as Heighth.
  pose proof (inverse_right_distribution G y v B HG) as HQfirst.
  pose proof (inverse_symmetry G ((y ⊗ a) ⊗ A) (y ⊗ (a ⊗ A)) HG
    (inverse_mul_associative G y a A HG)) as HAfirst.
  pose proof (inverse_multiplication G (y ⊗ a) (a ⊗ y) A A HG
    (inverse_mul_commutative G y a HG) (inverse_reflexivity G A HG)) as HAsecond.
  pose proof (inverse_transitivity G (y ⊗ B) ((y ⊗ a) ⊗ A)
    ((a ⊗ y) ⊗ A) HG HAfirst HAsecond) as HAY.
  pose proof (inverse_addition G (y ⊗ v) (y ⊗ v) (y ⊗ B) ((a ⊗ y) ⊗ A) HG
    (inverse_reflexivity G (y ⊗ v) HG) HAY) as HQsecond.
  pose proof (inverse_transitivity G (y ⊗ T) ((y ⊗ v) ⊕ (y ⊗ B))
    ((y ⊗ v) ⊕ ((a ⊗ y) ⊗ A)) HG HQfirst HQsecond) as HQ.
  pose proof (inverse_addition G (y ⊗ T) ((y ⊗ v) ⊕ ((a ⊗ y) ⊗ A)) A A HG
    HQ (inverse_reflexivity G A HG)) as HQouter.
  pose proof (merge_add_last_exchange G (y ⊗ v) ((a ⊗ y) ⊗ A) A HG) as HQexchange.
  pose proof (inverse_transitivity G ((y ⊗ T) ⊕ A)
    (((y ⊗ v) ⊕ ((a ⊗ y) ⊗ A)) ⊕ A) (crt_new_quotient A y a v)
    HG HQouter HQexchange) as Hquotient.
  pose proof (inverse_multiplication G ((y ⊗ T) ⊕ A) (crt_new_quotient A y a v)
    M M HG Hquotient (inverse_reflexivity G M HG)) as Hquotmul.
  pose proof (inverse_addition G (((y ⊗ T) ⊕ A) ⊗ M) (crt_new_quotient A y a v ⊗ M)
    v v HG Hquotmul (inverse_reflexivity G v HG)) as Hlast.
  pose proof (inverse_transitivity G (crt_candidate A x P a v)
    (A ⊕ (((y ⊗ M) ⊕ σ zero) ⊗ T)) (A ⊕ (U ⊕ T)) HG Hfirst Hsecond) as H12.
  pose proof (inverse_transitivity G (crt_candidate A x P a v)
    (A ⊕ (U ⊕ T)) (A ⊕ (v ⊕ (U ⊕ B))) HG H12 Hthird) as H123.
  pose proof (inverse_transitivity G (crt_candidate A x P a v)
    (A ⊕ (v ⊕ (U ⊕ B))) (v ⊕ (A ⊕ (U ⊕ B))) HG H123 Hfourth) as H1234.
  pose proof (inverse_transitivity G (crt_candidate A x P a v)
    (v ⊕ (A ⊕ (U ⊕ B))) (v ⊕ (U ⊕ (A ⊕ B))) HG H1234 Hfifth) as H12345.
  pose proof (inverse_transitivity G (crt_candidate A x P a v)
    (v ⊕ (U ⊕ (A ⊕ B))) (v ⊕ (M ⊗ ((y ⊗ T) ⊕ A))) HG H12345 Hsixth) as H123456.
  pose proof (inverse_transitivity G (crt_candidate A x P a v)
    (v ⊕ (M ⊗ ((y ⊗ T) ⊕ A))) (v ⊕ (((y ⊗ T) ⊕ A) ⊗ M))
    HG H123456 Hseventh) as H1234567.
  pose proof (inverse_transitivity G (crt_candidate A x P a v)
    (v ⊕ (((y ⊗ T) ⊕ A) ⊗ M)) ((((y ⊗ T) ⊕ A) ⊗ M) ⊕ v)
    HG H1234567 Heighth) as Hwhole.
  exact (inverse_transitivity G (crt_candidate A x P a v)
    ((((y ⊗ T) ⊕ A) ⊗ M) ⊕ v) ((crt_new_quotient A y a v ⊗ M) ⊕ v)
    HG Hwhole Hlast).
Qed.

Theorem binary_crt_new_quotient : paeq_derivable (∀ ∀ ∀ ∀ ∀ ∀
  ($1 ⊗ $2 == ($5 ⊗ σ $3) ⊕ σ zero →
    crt_candidate $0 $1 $2 $3 $4 == (crt_new_quotient $0 $5 $3 $4 ⊗ σ $3) ⊕ $4)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize, inverse_proof, II.
  set (G := List.cons ($1 ⊗ $2 == ($5 ⊗ σ $3) ⊕ σ zero) inverse_context).
  apply (candidate_new_row G $0 $1 $2 $3 $4 $5).
  - unfold G. apply has_inverse_cons. exact inverse_context_self.
  - apply Ctx. unfold G. now left.
Qed.

Lemma old_row_preserved G A z P q m t r h : has_inverse_context G ->
  G ⊢C (z == A ⊕ (q ⊗ P)) -> G ⊢C (A == (h ⊗ m) ⊕ r) ->
  G ⊢C (P == m ⊗ t) -> G ⊢C (z == ((h ⊕ (q ⊗ t)) ⊗ m) ⊕ r).
Proof.
  intros HG Hz HA HP.
  pose proof (inverse_multiplication G q q P (m ⊗ t) HG
    (inverse_reflexivity G q HG) HP) as Hqfirst.
  pose proof (inverse_symmetry G ((q ⊗ m) ⊗ t) (q ⊗ (m ⊗ t)) HG
    (inverse_mul_associative G q m t HG)) as Hqsecond.
  pose proof (merge_mul_last_exchange G q m t HG) as Hqthird.
  pose proof (inverse_transitivity G (q ⊗ P) (q ⊗ (m ⊗ t))
    ((q ⊗ m) ⊗ t) HG Hqfirst Hqsecond) as Hqfront.
  pose proof (inverse_transitivity G (q ⊗ P) ((q ⊗ m) ⊗ t)
    ((q ⊗ t) ⊗ m) HG Hqfront Hqthird) as Hq.
  pose proof (inverse_addition G A ((h ⊗ m) ⊕ r) (q ⊗ P) ((q ⊗ t) ⊗ m)
    HG HA Hq) as Hfirst.
  pose proof (merge_add_last_exchange G (h ⊗ m) r ((q ⊗ t) ⊗ m) HG) as Hsecond.
  pose proof (inverse_symmetry G ((h ⊕ (q ⊗ t)) ⊗ m)
    ((h ⊗ m) ⊕ ((q ⊗ t) ⊗ m)) HG
    (inverse_left_distribution G h (q ⊗ t) m HG)) as Hfactor.
  pose proof (inverse_addition G ((h ⊗ m) ⊕ ((q ⊗ t) ⊗ m))
    ((h ⊕ (q ⊗ t)) ⊗ m) r r HG Hfactor (inverse_reflexivity G r HG)) as Hthird.
  pose proof (inverse_transitivity G z (A ⊕ (q ⊗ P))
    (((h ⊗ m) ⊕ r) ⊕ ((q ⊗ t) ⊗ m)) HG Hz Hfirst) as H01.
  pose proof (inverse_transitivity G z (((h ⊗ m) ⊕ r) ⊕ ((q ⊗ t) ⊗ m))
    (((h ⊗ m) ⊕ ((q ⊗ t) ⊗ m)) ⊕ r) HG H01 Hsecond) as H012.
  exact (inverse_transitivity G z (((h ⊗ m) ⊕ ((q ⊗ t) ⊗ m)) ⊕ r)
    (((h ⊕ (q ⊗ t)) ⊗ m) ⊕ r) HG H012 Hthird).
Qed.

Lemma beta_preserved_by_divisor G A z P q c i r : has_inverse_context G ->
  G ⊢C (z == A ⊕ (q ⊗ P)) -> G ⊢C divides (beta_modulus c i) P ->
  G ⊢C beta A c i r -> G ⊢C beta z c i r.
Proof.
  intros HG Hz Hdiv HB. eapply divides_eliminate; [exact Hdiv|]. intros t.
  set (m := beta_modulus c i).
  set (D := List.cons (P == m ⊗ t) G).
  change (D ⊢C beta z c i r).
  pose proof (weaken_head G (beta A c i r) (P == m ⊗ t) HB) as HBD.
  rewrite PAPowerExtension238.beta_exists_witness in HBD.
  eapply ExE_named; [exact HBD|]. intros h.
  change ((List.cons
    ((PAPowerExtension238.beta_witness A`[↑] c`[↑] i`[↑] r`[↑] $0)[h..]) D) ⊢C beta z c i r).
  rewrite PAPowerExtension238.beta_witness_subst, !subst_term_shift.
  set (E := List.cons (PAPowerExtension238.beta_witness A c i r h) D).
  change (E ⊢C beta z c i r).
  assert (HE : has_inverse_context E).
  { unfold E, D. apply has_inverse_cons, has_inverse_cons. exact HG. }
  assert (Hbody : E ⊢C PAPowerExtension238.beta_witness A c i r h).
  { apply Ctx. unfold E. now left. }
  assert (HA : E ⊢C (A == (h ⊗ m) ⊕ r)) by exact (CE1 Hbody).
  assert (HP : E ⊢C (P == m ⊗ t)).
  { apply Ctx. unfold E, D. right. now left. }
  assert (HzE : E ⊢C (z == A ⊕ (q ⊗ P))).
  { unfold E, D. apply weaken_head, weaken_head. exact Hz. }
  apply (PAPowerExtension238.beta_introduce E z c i r (h ⊕ (q ⊗ t))).
  - exact (old_row_preserved E A z P q m t r h HE HzE HA HP).
  - exact (CE2 Hbody).
Qed.
Theorem beta_divisor_preservation : paeq_derivable (∀ ∀ ∀ ∀ ∀ ∀ ∀
  ($1 == $0 ⊕ ($3 ⊗ $2) → divides (beta_modulus $4 $5) $2 →
    beta $0 $4 $5 $6 → beta $1 $4 $5 $6)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize,
    inverse_proof, II, II, II.
  set (G := List.cons (beta $0 $4 $5 $6)
    (List.cons (divides (beta_modulus $4 $5) $2)
      (List.cons ($1 == $0 ⊕ ($3 ⊗ $2)) inverse_context))).
  apply (beta_preserved_by_divisor G $0 $1 $2 $3 $4 $5 $6).
  - unfold G. apply has_inverse_cons, has_inverse_cons, has_inverse_cons.
    exact inverse_context_self.
  - apply Ctx. unfold G. right. right. now left.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

Lemma candidate_new_beta G A x P c i v y : has_inverse_context G ->
  G ⊢C (x ⊗ P == (y ⊗ beta_modulus c i) ⊕ σ zero) ->
  G ⊢C (v ⧀ beta_modulus c i) ->
  G ⊢C beta (crt_candidate A x P ((σ i) ⊗ c) v) c i v.
Proof.
  intros HG Hinv HB.
  apply (PAPowerExtension238.beta_introduce G
    (crt_candidate A x P ((σ i) ⊗ c) v) c i v
    (crt_new_quotient A y ((σ i) ⊗ c) v)); [|exact HB].
  exact (candidate_new_row G A x P ((σ i) ⊗ c) v y HG Hinv).
Qed.
Theorem binary_crt_beta_endpoint : paeq_derivable (∀ ∀ ∀ ∀ ∀ ∀ ∀
  ($1 ⊗ $2 == ($6 ⊗ beta_modulus $3 $4) ⊕ σ zero →
    $5 ⧀ beta_modulus $3 $4 →
    beta (crt_candidate $0 $1 $2 ((σ $4) ⊗ $3) $5) $3 $4 $5)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize,
    inverse_proof, II, II.
  set (G := List.cons ($5 ⧀ beta_modulus $3 $4)
    (List.cons ($1 ⊗ $2 == ($6 ⊗ beta_modulus $3 $4) ⊕ σ zero) inverse_context)).
  apply (candidate_new_beta G $0 $1 $2 $3 $4 $5 $6).
  - unfold G. apply has_inverse_cons, has_inverse_cons. exact inverse_context_self.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

Definition preservation_row (A z P c i r : pa_term) : pa_form :=
  divides (beta_modulus c i) P → beta A c i r → beta z c i r.
Definition preserved_beta_rows (A z P c : pa_term) : pa_form :=
  ∀ ∀ preservation_row A`[↑]`[↑] z`[↑]`[↑] P`[↑]`[↑] c`[↑]`[↑] $1 $0.
Definition merge_result (A z P c i v : pa_term) : pa_form :=
  beta z c i v ∧ preserved_beta_rows A z P c.
Definition merge_exists (A P c i v : pa_term) : pa_form :=
  ∃ merge_result A`[↑] $0 P`[↑] c`[↑] i`[↑] v`[↑].
Lemma preservation_row_subst A z P c i r rho :
  (preservation_row A z P c i r)[rho] =
  preservation_row A`[rho] z`[rho] P`[rho] c`[rho] i`[rho] r`[rho].
Proof.
  unfold preservation_row. cbn [subst_form].
  rewrite divides_subst, beta_modulus_subst, !beta_subst. reflexivity.
Qed.
Lemma preserved_beta_rows_subst A z P c rho :
  (preserved_beta_rows A z P c)[rho] =
  preserved_beta_rows A`[rho] z`[rho] P`[rho] c`[rho].
Proof.
  unfold preserved_beta_rows. cbn [subst_form]. rewrite preservation_row_subst.
  now rewrite !up_term.
Qed.
Lemma merge_result_subst A z P c i v rho :
  (merge_result A z P c i v)[rho] =
  merge_result A`[rho] z`[rho] P`[rho] c`[rho] i`[rho] v`[rho].
Proof.
  unfold merge_result. cbn [subst_form]. rewrite beta_subst, preserved_beta_rows_subst.
  reflexivity.
Qed.
Lemma preserved_beta_rows_intro G A z P c :
  (forall i r, G ⊢C preservation_row A z P c i r) ->
  G ⊢C preserved_beta_rows A z P c.
Proof.
  intros H. unfold preserved_beta_rows. apply AllI_named. intros i.
  cbn [subst_form]. rewrite preservation_row_subst, !up_term, !subst_term_shift.
  change (G ⊢C ∀ preservation_row A`[↑] z`[↑] P`[↑] c`[↑] i`[↑] $0).
  apply AllI_named. intros r. rewrite preservation_row_subst, !subst_term_shift.
  exact (H i r).
Qed.
Lemma merge_exists_intro G A z P c i v :
  G ⊢C merge_result A z P c i v -> G ⊢C merge_exists A P c i v.
Proof.
  intros H. unfold merge_exists. apply (ExI z).
  rewrite merge_result_subst, !subst_term_shift. exact H.
Qed.
Lemma binary_crt_merge_at G A x P c i v y : has_inverse_context G ->
  G ⊢C (x ⊗ P == (y ⊗ beta_modulus c i) ⊕ σ zero) ->
  G ⊢C (v ⧀ beta_modulus c i) -> G ⊢C merge_exists A P c i v.
Proof.
  intros HG Hinv HB. set (a := (σ i) ⊗ c).
  set (z := crt_candidate A x P a v). set (q := crt_old_offset A x a v).
  apply (merge_exists_intro G A z P c i v). unfold merge_result. apply CI.
  - exact (candidate_new_beta G A x P c i v y HG Hinv HB).
  - apply preserved_beta_rows_intro. intros j r. unfold preservation_row. apply II, II.
    set (D := List.cons (beta A c j r)
      (List.cons (divides (beta_modulus c j) P) G)).
    change (D ⊢C beta z c j r).
    assert (HD : has_inverse_context D).
    { unfold D. apply has_inverse_cons, has_inverse_cons. exact HG. }
    pose proof (candidate_old_offset D A x P a v HD) as Hz.
    assert (Hdiv : D ⊢C divides (beta_modulus c j) P).
    { apply Ctx. unfold D. right. now left. }
    assert (Hold : D ⊢C beta A c j r).
    { apply Ctx. unfold D. now left. }
    exact (beta_preserved_by_divisor D A z P q c j r HD Hz Hdiv Hold).
Qed.
Theorem binary_crt_merge : paeq_derivable (∀ ∀ ∀ ∀ ∀ ∀ ∀
  ($1 ⊗ $2 == ($6 ⊗ beta_modulus $3 $4) ⊕ σ zero →
    $5 ⧀ beta_modulus $3 $4 → merge_exists $0 $2 $3 $4 $5)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize,
    inverse_proof, II, II.
  set (G := List.cons ($5 ⧀ beta_modulus $3 $4)
    (List.cons ($1 ⊗ $2 == ($6 ⊗ beta_modulus $3 $4) ⊕ σ zero) inverse_context)).
  apply (binary_crt_merge_at G $0 $1 $2 $3 $4 $5 $6).
  - unfold G. apply has_inverse_cons, has_inverse_cons. exact inverse_context_self.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

End PACRTMerge238.

Print Assumptions PACRTMerge238.candidate_old_offset.
Print Assumptions PACRTMerge238.binary_crt_new_quotient.
Print Assumptions PACRTMerge238.beta_divisor_preservation.
Print Assumptions PACRTMerge238.binary_crt_beta_endpoint.
Print Assumptions PACRTMerge238.binary_crt_merge.
