(* Original finite ordinary-PA inverse arithmetic for the beta moduli.
   All polynomial rearrangements below are explicit finite equality
   certificates.  The derived arithmetic context is discharged by actual
   PA certificates; no semantic ring theorem or inverse axiom is used. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAAddition238 PAEqCongruence238 PAOrderBounds238
  PAQuotient238 PACancellation238 PASemiring238 PAMultiplicationComm238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAOrderBounds238
  PAQuotient238 PASemiring238 PAMultiplicationComm238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAModuliInverse238.

Definition inverse_context : list pa_form :=
  [mult_associativity_sentence; mult_left_distribution_sentence] ++ commutative_context.
Definition has_inverse_context (G : list pa_form) : Prop :=
  forall phi, List.In phi inverse_context -> List.In phi G.
Lemma inverse_proof phi : inverse_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD.
  eapply paeq_modus_ponens with (phi := mult_associativity_sentence);
    [|exact PASemiring238.mult_associative].
  eapply paeq_modus_ponens with (phi := mult_left_distribution_sentence);
    [|exact PASemiring238.mult_left_distribution].
  apply commutative_proof, II, II. exact HD.
Qed.
Lemma inverse_context_self : has_inverse_context inverse_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_inverse_cons G phi : has_inverse_context G ->
  has_inverse_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma inverse_has_commutative G : has_inverse_context G -> has_commutative_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold inverse_context.
  apply List.in_app_iff. now right.
Qed.
Lemma inverse_has_addition G : has_inverse_context G -> has_addition_context G.
Proof.
  intros HG. apply multiplication_has_addition, commutative_has_multiplication,
    inverse_has_commutative. exact HG.
Qed.
Lemma inverse_has_product G : has_inverse_context G -> has_product_context G.
Proof. intros HG. apply addition_has_product, inverse_has_addition. exact HG. Qed.
Lemma inverse_has_divisor G : has_inverse_context G -> has_divisor_context G.
Proof.
  intros HG phi Hphi. unfold divisor_context, associative_context in Hphi.
  destruct Hphi as [<-|[<-|Hphi]].
  - apply HG. unfold inverse_context. now left.
  - apply HG. unfold inverse_context. right. now left.
  - exact (inverse_has_product G HG phi Hphi).
Qed.
Lemma inverse_equality G : has_inverse_context G -> has_equality G.
Proof. intros HG. apply product_has_equality, inverse_has_product. exact HG. Qed.
Lemma inverse_reflexivity G a : has_inverse_context G -> G ⊢C (a == a).
Proof. intros HG. apply reflexivity_instance, inverse_equality. exact HG. Qed.
Lemma inverse_symmetry G a b : has_inverse_context G ->
  G ⊢C (a == b) -> G ⊢C (b == a).
Proof. intros HG H. exact (equality_symmetry G a b (inverse_equality G HG) H). Qed.
Lemma inverse_transitivity G a b c : has_inverse_context G ->
  G ⊢C (a == b) -> G ⊢C (b == c) -> G ⊢C (a == c).
Proof. intros HG H K. exact (equality_transitivity G a b c (inverse_equality G HG) H K). Qed.
Lemma inverse_addition G a b c d : has_inverse_context G ->
  G ⊢C (a == b) -> G ⊢C (c == d) -> G ⊢C (a ⊕ c == b ⊕ d).
Proof.
  intros HG H K. exact (IE (IE (addition_instance G a b c d (inverse_equality G HG)) H) K).
Qed.
Lemma inverse_multiplication G a b c d : has_inverse_context G ->
  G ⊢C (a == b) -> G ⊢C (c == d) -> G ⊢C (a ⊗ c == b ⊗ d).
Proof.
  intros HG H K. exact (IE (IE (multiplication_instance G a b c d (inverse_equality G HG)) H) K).
Qed.
Lemma inverse_mul_associative G a b c : has_inverse_context G ->
  G ⊢C ((a ⊗ b) ⊗ c == a ⊗ (b ⊗ c)).
Proof. intros HG. apply multiplication_associative_at, inverse_has_divisor. exact HG. Qed.
Lemma inverse_mul_commutative G a b : has_inverse_context G ->
  G ⊢C (a ⊗ b == b ⊗ a).
Proof. intros HG. apply multiplication_commutative_at, inverse_has_commutative. exact HG. Qed.
Lemma inverse_add_associative G a b c : has_inverse_context G ->
  G ⊢C (a ⊕ (b ⊕ c) == (a ⊕ b) ⊕ c).
Proof.
  intros HG. apply associativity_instance.
  exact (inverse_has_product G HG associativity_sentence product_associativity).
Qed.
Lemma inverse_add_commutative G a b : has_inverse_context G ->
  G ⊢C (a ⊕ b == b ⊕ a).
Proof.
  intros HG. apply add_commutative_at.
  exact (inverse_has_addition G HG add_commutativity_sentence addition_commutativity).
Qed.
Lemma inverse_left_distribution G a b c : has_inverse_context G ->
  G ⊢C ((a ⊕ b) ⊗ c == (a ⊗ c) ⊕ (b ⊗ c)).
Proof.
  intros HG. apply left_distribution_at, HG. unfold inverse_context. right. now left.
Qed.
Lemma inverse_right_distribution G a b c : has_inverse_context G ->
  G ⊢C (a ⊗ (b ⊕ c) == (a ⊗ b) ⊕ (a ⊗ c)).
Proof.
  intros HG.
  pose proof (inverse_mul_commutative G a (b ⊕ c) HG) as Hfirst.
  pose proof (inverse_left_distribution G b c a HG) as Hsecond.
  pose proof (inverse_addition G (b ⊗ a) (a ⊗ b) (c ⊗ a) (a ⊗ c) HG
    (inverse_mul_commutative G b a HG) (inverse_mul_commutative G c a HG)) as Hthird.
  pose proof (inverse_transitivity G (a ⊗ (b ⊕ c)) ((b ⊕ c) ⊗ a)
    ((b ⊗ a) ⊕ (c ⊗ a)) HG Hfirst Hsecond) as Hfront.
  exact (inverse_transitivity G (a ⊗ (b ⊕ c)) ((b ⊗ a) ⊕ (c ⊗ a))
    ((a ⊗ b) ⊕ (a ⊗ c)) HG Hfront Hthird).
Qed.
Lemma inverse_right_zero G a : has_inverse_context G -> G ⊢C (a ⊕ zero == a).
Proof.
  intros HG. assert (HH : G ⊢C right_zero_sentence).
  { apply Ctx. exact (inverse_has_product G HG right_zero_sentence bounds_right_zero). }
  pose proof (AllE a HH) as HK. change (G ⊢C (a ⊕ zero == a)) in HK. exact HK.
Qed.
Lemma inverse_left_one G a : has_inverse_context G -> G ⊢C (σ zero ⊗ a == a).
Proof.
  intros HG. pose proof (inverse_has_product G HG) as HP.
  pose proof (mult_rec_instance G zero a (HP ax_mult_rec product_mult_rec)) as Hfirst.
  pose proof (mult_zero_instance G a (HP ax_mult_zero product_mult_zero)) as Hzero.
  pose proof (inverse_addition G a a (zero ⊗ a) zero HG
    (inverse_reflexivity G a HG) Hzero) as Hsecond.
  pose proof (inverse_transitivity G (σ zero ⊗ a) (a ⊕ (zero ⊗ a))
    (a ⊕ zero) HG Hfirst Hsecond) as Hfront.
  exact (inverse_transitivity G (σ zero ⊗ a) (a ⊕ zero) a HG
    Hfront (inverse_right_zero G a HG)).
Qed.
Lemma inverse_right_one G a : has_inverse_context G -> G ⊢C (a ⊗ σ zero == a).
Proof.
  intros HG. exact (inverse_transitivity G (a ⊗ σ zero) (σ zero ⊗ a) a HG
    (inverse_mul_commutative G a (σ zero) HG) (inverse_left_one G a HG)).
Qed.

Lemma inverse_mul_exchange G a b c : has_inverse_context G ->
  G ⊢C (a ⊗ (b ⊗ c) == b ⊗ (a ⊗ c)).
Proof.
  intros HG.
  pose proof (inverse_symmetry G ((a ⊗ b) ⊗ c) (a ⊗ (b ⊗ c)) HG
    (inverse_mul_associative G a b c HG)) as Hfirst.
  pose proof (inverse_multiplication G (a ⊗ b) (b ⊗ a) c c HG
    (inverse_mul_commutative G a b HG) (inverse_reflexivity G c HG)) as Hsecond.
  pose proof (inverse_transitivity G (a ⊗ (b ⊗ c)) ((a ⊗ b) ⊗ c)
    ((b ⊗ a) ⊗ c) HG Hfirst Hsecond) as Hfront.
  exact (inverse_transitivity G (a ⊗ (b ⊗ c)) ((b ⊗ a) ⊗ c)
    (b ⊗ (a ⊗ c)) HG Hfront (inverse_mul_associative G b a c HG)).
Qed.
Lemma inverse_mul_pair_shuffle G a b c d : has_inverse_context G ->
  G ⊢C ((a ⊗ b) ⊗ (c ⊗ d) == (a ⊗ c) ⊗ (b ⊗ d)).
Proof.
  intros HG.
  pose proof (inverse_mul_associative G a b (c ⊗ d) HG) as Hfirst.
  pose proof (inverse_multiplication G a a (b ⊗ (c ⊗ d)) (c ⊗ (b ⊗ d)) HG
    (inverse_reflexivity G a HG) (inverse_mul_exchange G b c d HG)) as Hsecond.
  pose proof (inverse_symmetry G ((a ⊗ c) ⊗ (b ⊗ d)) (a ⊗ (c ⊗ (b ⊗ d))) HG
    (inverse_mul_associative G a c (b ⊗ d) HG)) as Hthird.
  pose proof (inverse_transitivity G ((a ⊗ b) ⊗ (c ⊗ d)) (a ⊗ (b ⊗ (c ⊗ d)))
    (a ⊗ (c ⊗ (b ⊗ d))) HG Hfirst Hsecond) as Hfront.
  exact (inverse_transitivity G ((a ⊗ b) ⊗ (c ⊗ d)) (a ⊗ (c ⊗ (b ⊗ d)))
    ((a ⊗ c) ⊗ (b ⊗ d)) HG Hfront Hthird).
Qed.

Lemma moduli_sum_at G u v C q d p : has_inverse_context G ->
  G ⊢C (v == u ⊕ d) -> G ⊢C (C == q ⊗ d) ->
  G ⊢C ((u ⊗ v) ⊗ q == p ⊕ σ zero) ->
  G ⊢C (((u ⊗ u) ⊗ q) ⊕ (u ⊗ C) == p ⊕ σ zero).
Proof.
  intros HG Hv HC HT.
  set (A := (u ⊗ u) ⊗ q).
  pose proof (inverse_multiplication G u u C (q ⊗ d) HG
    (inverse_reflexivity G u HG) HC) as HB1.
  pose proof (inverse_multiplication G u u (q ⊗ d) (d ⊗ q) HG
    (inverse_reflexivity G u HG) (inverse_mul_commutative G q d HG)) as HB2.
  pose proof (inverse_symmetry G ((u ⊗ d) ⊗ q) (u ⊗ (d ⊗ q)) HG
    (inverse_mul_associative G u d q HG)) as HB3.
  pose proof (inverse_transitivity G (u ⊗ C) (u ⊗ (q ⊗ d))
    (u ⊗ (d ⊗ q)) HG HB1 HB2) as HB12.
  pose proof (inverse_transitivity G (u ⊗ C) (u ⊗ (d ⊗ q))
    ((u ⊗ d) ⊗ q) HG HB12 HB3) as HB.
  pose proof (inverse_addition G A A (u ⊗ C) ((u ⊗ d) ⊗ q) HG
    (inverse_reflexivity G A HG) HB) as Hfirst.
  pose proof (inverse_symmetry G (((u ⊗ u) ⊕ (u ⊗ d)) ⊗ q)
    (((u ⊗ u) ⊗ q) ⊕ ((u ⊗ d) ⊗ q)) HG
    (inverse_left_distribution G (u ⊗ u) (u ⊗ d) q HG)) as Hsecond.
  pose proof (inverse_symmetry G (u ⊗ (u ⊕ d)) ((u ⊗ u) ⊕ (u ⊗ d)) HG
    (inverse_right_distribution G u u d HG)) as Hfactor.
  pose proof (inverse_multiplication G ((u ⊗ u) ⊕ (u ⊗ d)) (u ⊗ (u ⊕ d)) q q HG
    Hfactor (inverse_reflexivity G q HG)) as Hthird.
  pose proof (inverse_multiplication G u u v (u ⊕ d) HG
    (inverse_reflexivity G u HG) Hv) as Huv.
  pose proof (inverse_multiplication G (u ⊗ v) (u ⊗ (u ⊕ d)) q q HG
    Huv (inverse_reflexivity G q HG)) as HTforward.
  pose proof (inverse_symmetry G ((u ⊗ v) ⊗ q) ((u ⊗ (u ⊕ d)) ⊗ q)
    HG HTforward) as Hfourth.
  pose proof (inverse_transitivity G (A ⊕ (u ⊗ C))
    (A ⊕ ((u ⊗ d) ⊗ q)) (((u ⊗ u) ⊕ (u ⊗ d)) ⊗ q)
    HG Hfirst Hsecond) as H12.
  pose proof (inverse_transitivity G (A ⊕ (u ⊗ C))
    (((u ⊗ u) ⊕ (u ⊗ d)) ⊗ q) ((u ⊗ (u ⊕ d)) ⊗ q)
    HG H12 Hthird) as H123.
  pose proof (inverse_transitivity G (A ⊕ (u ⊗ C))
    ((u ⊗ (u ⊕ d)) ⊗ q) ((u ⊗ v) ⊗ q) HG H123 Hfourth) as Hwhole.
  exact (inverse_transitivity G (A ⊕ (u ⊗ C)) ((u ⊗ v) ⊗ q)
    (p ⊕ σ zero) HG Hwhole HT).
Qed.

Lemma moduli_product_shuffle G u v C q : has_inverse_context G ->
  G ⊢C (((u ⊗ u) ⊗ q) ⊗ (v ⊗ C) == ((u ⊗ v) ⊗ q) ⊗ (u ⊗ C)).
Proof.
  intros HG.
  pose proof (inverse_mul_pair_shuffle G (u ⊗ u) q v C HG) as Hfirst.
  pose proof (inverse_mul_associative G u u v HG) as HA.
  pose proof (inverse_mul_commutative G u (u ⊗ v) HG) as HB.
  pose proof (inverse_transitivity G ((u ⊗ u) ⊗ v) (u ⊗ (u ⊗ v))
    ((u ⊗ v) ⊗ u) HG HA HB) as Hfactor.
  pose proof (inverse_multiplication G ((u ⊗ u) ⊗ v) ((u ⊗ v) ⊗ u)
    (q ⊗ C) (q ⊗ C) HG Hfactor (inverse_reflexivity G (q ⊗ C) HG)) as Hsecond.
  pose proof (inverse_symmetry G (((u ⊗ v) ⊗ q) ⊗ (u ⊗ C))
    (((u ⊗ v) ⊗ u) ⊗ (q ⊗ C)) HG
    (inverse_mul_pair_shuffle G (u ⊗ v) q u C HG)) as Hthird.
  pose proof (inverse_transitivity G (((u ⊗ u) ⊗ q) ⊗ (v ⊗ C))
    (((u ⊗ u) ⊗ v) ⊗ (q ⊗ C)) (((u ⊗ v) ⊗ u) ⊗ (q ⊗ C))
    HG Hfirst Hsecond) as Hfront.
  exact (inverse_transitivity G (((u ⊗ u) ⊗ q) ⊗ (v ⊗ C))
    (((u ⊗ v) ⊗ u) ⊗ (q ⊗ C)) (((u ⊗ v) ⊗ q) ⊗ (u ⊗ C))
    HG Hfront Hthird).
Qed.

Lemma special_moduli_inverse_at G u v C q d p : has_inverse_context G ->
  G ⊢C (v == u ⊕ d) -> G ⊢C (C == q ⊗ d) ->
  G ⊢C ((u ⊗ v) ⊗ q == p ⊕ σ zero) ->
  G ⊢C (((u ⊗ u) ⊗ q) ⊗ (σ zero ⊕ (v ⊗ C)) ==
    (p ⊗ (σ zero ⊕ (u ⊗ C))) ⊕ σ zero).
Proof.
  intros HG Hv HC HT.
  set (A := (u ⊗ u) ⊗ q). set (B := u ⊗ C). set (T := (u ⊗ v) ⊗ q).
  pose proof (moduli_sum_at G u v C q d p HG Hv HC HT) as Hsum.
  pose proof (moduli_product_shuffle G u v C q HG) as Hshuffle.
  pose proof (inverse_right_distribution G A (σ zero) (v ⊗ C) HG) as Hfirst.
  pose proof (inverse_addition G (A ⊗ σ zero) A (A ⊗ (v ⊗ C)) (T ⊗ B) HG
    (inverse_right_one G A HG) Hshuffle) as Hsecond.
  pose proof (inverse_multiplication G T (p ⊕ σ zero) B B HG
    HT (inverse_reflexivity G B HG)) as HTB.
  pose proof (inverse_addition G A A (T ⊗ B) ((p ⊕ σ zero) ⊗ B) HG
    (inverse_reflexivity G A HG) HTB) as Hthird.
  pose proof (inverse_left_distribution G p (σ zero) B HG) as HBfirst.
  pose proof (inverse_addition G (p ⊗ B) (p ⊗ B) (σ zero ⊗ B) B HG
    (inverse_reflexivity G (p ⊗ B) HG) (inverse_left_one G B HG)) as HBsecond.
  pose proof (inverse_transitivity G ((p ⊕ σ zero) ⊗ B)
    ((p ⊗ B) ⊕ (σ zero ⊗ B)) ((p ⊗ B) ⊕ B) HG HBfirst HBsecond) as HBwhole.
  pose proof (inverse_addition G A A ((p ⊕ σ zero) ⊗ B) ((p ⊗ B) ⊕ B) HG
    (inverse_reflexivity G A HG) HBwhole) as Hfourth.
  pose proof (add_exchange G A (p ⊗ B) B (inverse_has_addition G HG)) as Hfifth.
  pose proof (inverse_addition G (p ⊗ B) (p ⊗ B) (A ⊕ B) (p ⊕ σ zero) HG
    (inverse_reflexivity G (p ⊗ B) HG) Hsum) as Hsixth.
  pose proof (inverse_add_associative G (p ⊗ B) p (σ zero) HG) as Hseventh.
  pose proof (inverse_addition G ((p ⊗ B) ⊕ p) (p ⊕ (p ⊗ B))
    (σ zero) (σ zero) HG (inverse_add_commutative G (p ⊗ B) p HG)
    (inverse_reflexivity G (σ zero) HG)) as Heighth.
  pose proof (inverse_right_distribution G p (σ zero) B HG) as HPfirst.
  pose proof (inverse_addition G (p ⊗ σ zero) p (p ⊗ B) (p ⊗ B) HG
    (inverse_right_one G p HG) (inverse_reflexivity G (p ⊗ B) HG)) as HPsecond.
  pose proof (inverse_transitivity G (p ⊗ (σ zero ⊕ B))
    ((p ⊗ σ zero) ⊕ (p ⊗ B)) (p ⊕ (p ⊗ B)) HG HPfirst HPsecond) as HPwhole.
  pose proof (inverse_symmetry G (p ⊗ (σ zero ⊕ B)) (p ⊕ (p ⊗ B)) HG HPwhole) as HPback.
  pose proof (inverse_addition G (p ⊕ (p ⊗ B)) (p ⊗ (σ zero ⊕ B))
    (σ zero) (σ zero) HG HPback (inverse_reflexivity G (σ zero) HG)) as Hlast.
  pose proof (inverse_transitivity G (A ⊗ (σ zero ⊕ (v ⊗ C)))
    ((A ⊗ σ zero) ⊕ (A ⊗ (v ⊗ C))) (A ⊕ (T ⊗ B)) HG Hfirst Hsecond) as H12.
  pose proof (inverse_transitivity G (A ⊗ (σ zero ⊕ (v ⊗ C)))
    (A ⊕ (T ⊗ B)) (A ⊕ ((p ⊕ σ zero) ⊗ B)) HG H12 Hthird) as H123.
  pose proof (inverse_transitivity G (A ⊗ (σ zero ⊕ (v ⊗ C)))
    (A ⊕ ((p ⊕ σ zero) ⊗ B)) (A ⊕ ((p ⊗ B) ⊕ B)) HG H123 Hfourth) as H1234.
  pose proof (inverse_transitivity G (A ⊗ (σ zero ⊕ (v ⊗ C)))
    (A ⊕ ((p ⊗ B) ⊕ B)) ((p ⊗ B) ⊕ (A ⊕ B)) HG H1234 Hfifth) as H12345.
  pose proof (inverse_transitivity G (A ⊗ (σ zero ⊕ (v ⊗ C)))
    ((p ⊗ B) ⊕ (A ⊕ B)) ((p ⊗ B) ⊕ (p ⊕ σ zero)) HG H12345 Hsixth) as H123456.
  pose proof (inverse_transitivity G (A ⊗ (σ zero ⊕ (v ⊗ C)))
    ((p ⊗ B) ⊕ (p ⊕ σ zero)) (((p ⊗ B) ⊕ p) ⊕ σ zero)
    HG H123456 Hseventh) as H1234567.
  pose proof (inverse_transitivity G (A ⊗ (σ zero ⊕ (v ⊗ C)))
    (((p ⊗ B) ⊕ p) ⊕ σ zero) ((p ⊕ (p ⊗ B)) ⊕ σ zero)
    HG H1234567 Heighth) as Hwhole.
  exact (inverse_transitivity G (A ⊗ (σ zero ⊕ (v ⊗ C)))
    ((p ⊕ (p ⊗ B)) ⊕ σ zero) ((p ⊗ (σ zero ⊕ B)) ⊕ σ zero)
    HG Hwhole Hlast).
Qed.

Theorem special_moduli_inverse_polynomial : paeq_derivable (∀ ∀ ∀ ∀ ∀ ∀
  ($1 == $0 ⊕ $4 → $2 == $3 ⊗ $4 →
    ($0 ⊗ $1) ⊗ $3 == $5 ⊕ σ zero →
    (($0 ⊗ $0) ⊗ $3) ⊗ (σ zero ⊕ ($1 ⊗ $2)) ==
      ($5 ⊗ (σ zero ⊕ ($0 ⊗ $2))) ⊕ σ zero)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize, inverse_proof, II, II, II.
  set (G := List.cons (($0 ⊗ $1) ⊗ $3 == $5 ⊕ σ zero)
    (List.cons ($2 == $3 ⊗ $4) (List.cons ($1 == $0 ⊕ $4) inverse_context))).
  apply (special_moduli_inverse_at G $0 $1 $2 $3 $4 $5).
  - unfold G. apply has_inverse_cons, has_inverse_cons, has_inverse_cons.
    exact inverse_context_self.
  - apply Ctx. unfold G. right. right. now left.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

Lemma inverse_product_plus_one G a b : has_inverse_context G ->
  G ⊢C ((a ⊕ σ zero) ⊗ (b ⊕ σ zero) ==
    (((a ⊗ b) ⊕ a) ⊕ b) ⊕ σ zero).
Proof.
  intros HG.
  pose proof (inverse_right_distribution G a b (σ zero) HG) as HAfirst.
  pose proof (inverse_addition G (a ⊗ b) (a ⊗ b) (a ⊗ σ zero) a HG
    (inverse_reflexivity G (a ⊗ b) HG) (inverse_right_one G a HG)) as HAsecond.
  pose proof (inverse_transitivity G (a ⊗ (b ⊕ σ zero))
    ((a ⊗ b) ⊕ (a ⊗ σ zero)) ((a ⊗ b) ⊕ a) HG HAfirst HAsecond) as HA.
  pose proof (inverse_left_distribution G a (σ zero) (b ⊕ σ zero) HG) as Hfirst.
  pose proof (inverse_addition G (a ⊗ (b ⊕ σ zero)) ((a ⊗ b) ⊕ a)
    (σ zero ⊗ (b ⊕ σ zero)) (b ⊕ σ zero) HG HA
    (inverse_left_one G (b ⊕ σ zero) HG)) as Hsecond.
  pose proof (inverse_add_associative G ((a ⊗ b) ⊕ a) b (σ zero) HG) as Hthird.
  pose proof (inverse_transitivity G ((a ⊕ σ zero) ⊗ (b ⊕ σ zero))
    ((a ⊗ (b ⊕ σ zero)) ⊕ (σ zero ⊗ (b ⊕ σ zero)))
    (((a ⊗ b) ⊕ a) ⊕ (b ⊕ σ zero)) HG Hfirst Hsecond) as Hfront.
  exact (inverse_transitivity G ((a ⊕ σ zero) ⊗ (b ⊕ σ zero))
    (((a ⊗ b) ⊕ a) ⊕ (b ⊕ σ zero)) ((((a ⊗ b) ⊕ a) ⊕ b) ⊕ σ zero)
    HG Hfront Hthird).
Qed.
Lemma inverse_triple_distribution G a b c m : has_inverse_context G ->
  G ⊢C (((a ⊕ b) ⊕ c) ⊗ m == ((a ⊗ m) ⊕ (b ⊗ m)) ⊕ (c ⊗ m)).
Proof.
  intros HG.
  pose proof (inverse_left_distribution G (a ⊕ b) c m HG) as Hfirst.
  pose proof (inverse_addition G ((a ⊕ b) ⊗ m) ((a ⊗ m) ⊕ (b ⊗ m))
    (c ⊗ m) (c ⊗ m) HG (inverse_left_distribution G a b m HG)
    (inverse_reflexivity G (c ⊗ m) HG)) as Hsecond.
  exact (inverse_transitivity G (((a ⊕ b) ⊕ c) ⊗ m)
    (((a ⊕ b) ⊗ m) ⊕ (c ⊗ m)) (((a ⊗ m) ⊕ (b ⊗ m)) ⊕ (c ⊗ m))
    HG Hfirst Hsecond).
Qed.

Lemma inverse_product_at G x X P Q y Y M : has_inverse_context G ->
  G ⊢C (x ⊗ P == (y ⊗ M) ⊕ σ zero) ->
  G ⊢C (X ⊗ Q == (Y ⊗ M) ⊕ σ zero) ->
  G ⊢C ((x ⊗ X) ⊗ (P ⊗ Q) ==
    (((((y ⊗ Y) ⊗ M) ⊕ y) ⊕ Y) ⊗ M) ⊕ σ zero).
Proof.
  intros HG Hx HX. set (T := (y ⊗ Y) ⊗ M).
  pose proof (inverse_mul_pair_shuffle G x X P Q HG) as Hfirst.
  pose proof (inverse_multiplication G (x ⊗ P) ((y ⊗ M) ⊕ σ zero)
    (X ⊗ Q) ((Y ⊗ M) ⊕ σ zero) HG Hx HX) as Hsecond.
  pose proof (inverse_product_plus_one G (y ⊗ M) (Y ⊗ M) HG) as Hthird.
  pose proof (inverse_mul_pair_shuffle G y M Y M HG) as HTfirst.
  pose proof (inverse_symmetry G (((y ⊗ Y) ⊗ M) ⊗ M)
    ((y ⊗ Y) ⊗ (M ⊗ M)) HG (inverse_mul_associative G (y ⊗ Y) M M HG)) as HTsecond.
  pose proof (inverse_transitivity G ((y ⊗ M) ⊗ (Y ⊗ M))
    ((y ⊗ Y) ⊗ (M ⊗ M)) (T ⊗ M) HG HTfirst HTsecond) as HT.
  pose proof (inverse_addition G ((y ⊗ M) ⊗ (Y ⊗ M)) (T ⊗ M)
    (y ⊗ M) (y ⊗ M) HG HT (inverse_reflexivity G (y ⊗ M) HG)) as Hinner.
  pose proof (inverse_addition G (((y ⊗ M) ⊗ (Y ⊗ M)) ⊕ (y ⊗ M))
    ((T ⊗ M) ⊕ (y ⊗ M)) (Y ⊗ M) (Y ⊗ M) HG Hinner
    (inverse_reflexivity G (Y ⊗ M) HG)) as Hmiddle.
  pose proof (inverse_addition G
    ((((y ⊗ M) ⊗ (Y ⊗ M)) ⊕ (y ⊗ M)) ⊕ (Y ⊗ M))
    (((T ⊗ M) ⊕ (y ⊗ M)) ⊕ (Y ⊗ M)) (σ zero) (σ zero) HG Hmiddle
    (inverse_reflexivity G (σ zero) HG)) as Hfourth.
  pose proof (inverse_triple_distribution G T y Y M HG) as HR.
  pose proof (inverse_addition G (((T ⊕ y) ⊕ Y) ⊗ M)
    (((T ⊗ M) ⊕ (y ⊗ M)) ⊕ (Y ⊗ M)) (σ zero) (σ zero) HG HR
    (inverse_reflexivity G (σ zero) HG)) as Hright.
  pose proof (inverse_symmetry G ((((T ⊕ y) ⊕ Y) ⊗ M) ⊕ σ zero)
    ((((T ⊗ M) ⊕ (y ⊗ M)) ⊕ (Y ⊗ M)) ⊕ σ zero) HG Hright) as Hlast.
  pose proof (inverse_transitivity G ((x ⊗ X) ⊗ (P ⊗ Q))
    ((x ⊗ P) ⊗ (X ⊗ Q)) (((y ⊗ M) ⊕ σ zero) ⊗ ((Y ⊗ M) ⊕ σ zero))
    HG Hfirst Hsecond) as H12.
  pose proof (inverse_transitivity G ((x ⊗ X) ⊗ (P ⊗ Q))
    (((y ⊗ M) ⊕ σ zero) ⊗ ((Y ⊗ M) ⊕ σ zero))
    (((((y ⊗ M) ⊗ (Y ⊗ M)) ⊕ (y ⊗ M)) ⊕ (Y ⊗ M)) ⊕ σ zero)
    HG H12 Hthird) as H123.
  pose proof (inverse_transitivity G ((x ⊗ X) ⊗ (P ⊗ Q))
    (((((y ⊗ M) ⊗ (Y ⊗ M)) ⊕ (y ⊗ M)) ⊕ (Y ⊗ M)) ⊕ σ zero)
    ((((T ⊗ M) ⊕ (y ⊗ M)) ⊕ (Y ⊗ M)) ⊕ σ zero)
    HG H123 Hfourth) as Hwhole.
  exact (inverse_transitivity G ((x ⊗ X) ⊗ (P ⊗ Q))
    ((((T ⊗ M) ⊕ (y ⊗ M)) ⊕ (Y ⊗ M)) ⊕ σ zero)
    ((((T ⊕ y) ⊕ Y) ⊗ M) ⊕ σ zero) HG Hwhole Hlast).
Qed.
Theorem product_inverse_polynomial : paeq_derivable (∀ ∀ ∀ ∀ ∀ ∀ ∀
  ($0 ⊗ $2 == ($4 ⊗ $6) ⊕ σ zero →
    $1 ⊗ $3 == ($5 ⊗ $6) ⊕ σ zero →
    ($0 ⊗ $1) ⊗ ($2 ⊗ $3) ==
      (((((($4 ⊗ $5) ⊗ $6) ⊕ $4) ⊕ $5) ⊗ $6) ⊕ σ zero))).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize,
    inverse_proof, II, II.
  set (G := List.cons ($1 ⊗ $3 == ($5 ⊗ $6) ⊕ σ zero)
    (List.cons ($0 ⊗ $2 == ($4 ⊗ $6) ⊕ σ zero) inverse_context)).
  apply (inverse_product_at G $0 $1 $2 $3 $4 $5 $6).
  - unfold G. apply has_inverse_cons, has_inverse_cons. exact inverse_context_self.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

Lemma inverse_flip_differences G A B x y K xp yp : has_inverse_context G ->
  List.In cancellation_sentence G ->
  G ⊢C (x ⊗ A == (y ⊗ B) ⊕ σ zero) ->
  G ⊢C (K ⊗ A == y ⊕ xp) -> G ⊢C (K ⊗ B == x ⊕ yp) ->
  G ⊢C (xp ⊗ B == (yp ⊗ A) ⊕ σ zero).
Proof.
  intros HG Hcancel Hinv HA HB.
  pose proof (inverse_mul_associative G K A B HG) as HEfirst.
  pose proof (inverse_multiplication G K K (A ⊗ B) (B ⊗ A) HG
    (inverse_reflexivity G K HG) (inverse_mul_commutative G A B HG)) as HEsecond.
  pose proof (inverse_symmetry G ((K ⊗ B) ⊗ A) (K ⊗ (B ⊗ A)) HG
    (inverse_mul_associative G K B A HG)) as HEthird.
  pose proof (inverse_transitivity G ((K ⊗ A) ⊗ B) (K ⊗ (A ⊗ B))
    (K ⊗ (B ⊗ A)) HG HEfirst HEsecond) as HEfront.
  pose proof (inverse_transitivity G ((K ⊗ A) ⊗ B) (K ⊗ (B ⊗ A))
    ((K ⊗ B) ⊗ A) HG HEfront HEthird) as Hcommon.
  pose proof (inverse_multiplication G (K ⊗ A) (y ⊕ xp) B B HG HA
    (inverse_reflexivity G B HG)) as HLfirst.
  pose proof (inverse_left_distribution G y xp B HG) as HLsecond.
  pose proof (inverse_transitivity G ((K ⊗ A) ⊗ B) ((y ⊕ xp) ⊗ B)
    ((y ⊗ B) ⊕ (xp ⊗ B)) HG HLfirst HLsecond) as HL.
  pose proof (inverse_multiplication G (K ⊗ B) (x ⊕ yp) A A HG HB
    (inverse_reflexivity G A HG)) as HRfirst.
  pose proof (inverse_left_distribution G x yp A HG) as HRsecond.
  pose proof (inverse_addition G (x ⊗ A) ((y ⊗ B) ⊕ σ zero)
    (yp ⊗ A) (yp ⊗ A) HG Hinv (inverse_reflexivity G (yp ⊗ A) HG)) as HRthird.
  pose proof (inverse_symmetry G ((y ⊗ B) ⊕ (σ zero ⊕ (yp ⊗ A)))
    (((y ⊗ B) ⊕ σ zero) ⊕ (yp ⊗ A)) HG
    (inverse_add_associative G (y ⊗ B) (σ zero) (yp ⊗ A) HG)) as HRfourth.
  pose proof (inverse_addition G (y ⊗ B) (y ⊗ B)
    (σ zero ⊕ (yp ⊗ A)) ((yp ⊗ A) ⊕ σ zero) HG
    (inverse_reflexivity G (y ⊗ B) HG)
    (inverse_add_commutative G (σ zero) (yp ⊗ A) HG)) as HRfifth.
  pose proof (inverse_transitivity G ((K ⊗ B) ⊗ A) ((x ⊕ yp) ⊗ A)
    ((x ⊗ A) ⊕ (yp ⊗ A)) HG HRfirst HRsecond) as HR12.
  pose proof (inverse_transitivity G ((K ⊗ B) ⊗ A) ((x ⊗ A) ⊕ (yp ⊗ A))
    (((y ⊗ B) ⊕ σ zero) ⊕ (yp ⊗ A)) HG HR12 HRthird) as HR123.
  pose proof (inverse_transitivity G ((K ⊗ B) ⊗ A)
    (((y ⊗ B) ⊕ σ zero) ⊕ (yp ⊗ A)) ((y ⊗ B) ⊕ (σ zero ⊕ (yp ⊗ A)))
    HG HR123 HRfourth) as HR1234.
  pose proof (inverse_transitivity G ((K ⊗ B) ⊗ A)
    ((y ⊗ B) ⊕ (σ zero ⊕ (yp ⊗ A))) ((y ⊗ B) ⊕ ((yp ⊗ A) ⊕ σ zero))
    HG HR1234 HRfifth) as HR.
  pose proof (inverse_symmetry G ((K ⊗ A) ⊗ B) ((y ⊗ B) ⊕ (xp ⊗ B)) HG HL) as HLback.
  pose proof (inverse_transitivity G ((y ⊗ B) ⊕ (xp ⊗ B)) ((K ⊗ A) ⊗ B)
    ((K ⊗ B) ⊗ A) HG HLback Hcommon) as Hjoined.
  pose proof (inverse_transitivity G ((y ⊗ B) ⊕ (xp ⊗ B)) ((K ⊗ B) ⊗ A)
    ((y ⊗ B) ⊕ ((yp ⊗ A) ⊕ σ zero)) HG Hjoined HR) as Hcancelled.
  exact (IE (cancellation_instance G (y ⊗ B) (xp ⊗ B)
    ((yp ⊗ A) ⊕ σ zero) Hcancel) Hcancelled).
Qed.

Definition inverse_pair (A B x y : pa_term) : pa_form := x ⊗ A == (y ⊗ B) ⊕ σ zero.
Definition inverse_exists (A B : pa_term) : pa_form :=
  ∃ ∃ inverse_pair A`[↑]`[↑] B`[↑]`[↑] $1 $0.
Lemma inverse_pair_subst A B x y rho :
  (inverse_pair A B x y)[rho] = inverse_pair A`[rho] B`[rho] x`[rho] y`[rho].
Proof. reflexivity. Qed.
Lemma inverse_exists_intro G A B x y :
  G ⊢C inverse_pair A B x y -> G ⊢C inverse_exists A B.
Proof.
  intros H. unfold inverse_exists. apply (ExI x).
  cbn [subst_form]. rewrite inverse_pair_subst, !up_term, !subst_term_shift.
  change (G ⊢C ∃ inverse_pair A`[↑] B`[↑] x`[↑] $0).
  apply (ExI y). rewrite inverse_pair_subst, !subst_term_shift. exact H.
Qed.
Definition flip_context : list pa_form := List.cons cancellation_sentence inverse_context.
Lemma flip_proof phi : flip_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := cancellation_sentence).
  - apply inverse_proof, II. exact HD.
  - exact PACancellation238.add_cancel_left.
Qed.
Theorem inverse_orientation_from_bounds : paeq_derivable (∀ ∀ ∀ ∀ ∀
  ($2 ⊗ $0 == ($3 ⊗ $1) ⊕ σ zero →
    $3 ⧀= ($4 ⊗ $0) → $2 ⧀= ($4 ⊗ $1) → inverse_exists $1 $0)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, flip_proof, II, II, II.
  set (G := List.cons ($2 ⧀= ($4 ⊗ $1))
    (List.cons ($3 ⧀= ($4 ⊗ $0))
      (List.cons ($2 ⊗ $0 == ($3 ⊗ $1) ⊕ σ zero) flip_context))).
  assert (Hy : G ⊢C ($3 ⧀= ($4 ⊗ $0))).
  { apply Ctx. unfold G. right. now left. }
  unfold PAle in Hy. eapply ExE_named; [exact Hy|]. intros xp.
  change ((List.cons (($4 ⊗ $0)`[↑]`[xp..] == $3`[↑]`[xp..] ⊕ xp) G) ⊢C
    inverse_exists $1 $0).
  rewrite !subst_term_shift.
  set (D := List.cons ($4 ⊗ $0 == $3 ⊕ xp) G).
  assert (Hx : D ⊢C ($2 ⧀= ($4 ⊗ $1))).
  { apply Ctx. unfold D, G. right. now left. }
  unfold PAle in Hx. eapply ExE_named; [exact Hx|]. intros yp.
  change ((List.cons (($4 ⊗ $1)`[↑]`[yp..] == $2`[↑]`[yp..] ⊕ yp) D) ⊢C
    inverse_exists $1 $0).
  rewrite !subst_term_shift.
  set (E := List.cons ($4 ⊗ $1 == $2 ⊕ yp) D).
  assert (HE : has_inverse_context E).
  { intros phi Hphi. unfold E, D, G, flip_context.
    right. right. right. right. right. now right. }
  assert (Hcancel : List.In cancellation_sentence E).
  { unfold E, D, G, flip_context. right. right. right. right. right. now left. }
  assert (Hinv : E ⊢C ($2 ⊗ $0 == ($3 ⊗ $1) ⊕ σ zero)).
  { apply Ctx. unfold E, D, G. right. right. right. right. now left. }
  assert (HA : E ⊢C ($4 ⊗ $0 == $3 ⊕ xp)).
  { apply Ctx. unfold E, D. right. now left. }
  assert (HB : E ⊢C ($4 ⊗ $1 == $2 ⊕ yp)).
  { apply Ctx. unfold E. now left. }
  apply (inverse_exists_intro E $1 $0 xp yp).
  exact (inverse_flip_differences E $0 $1 $2 $3 $4 xp yp HE Hcancel Hinv HA HB).
Qed.

Lemma inverse_complement_bounds G A B x y : has_inverse_context G ->
  G ⊢C (zero ⧀ B) -> G ⊢C (x ⊗ A == (y ⊗ B) ⊕ σ zero) ->
  G ⊢C ((y ⧀= (σ x ⊗ A)) ∧ (x ⧀= (σ x ⊗ B))).
Proof.
  intros HG Hpos Hinv. unfold PAlt in Hpos. eapply ExE_named; [exact Hpos|]. intros k.
  change ((List.cons (B`[↑]`[k..] == σ zero ⊕ k) G) ⊢C
    ((y ⧀= (σ x ⊗ A)) ∧ (x ⧀= (σ x ⊗ B)))).
  rewrite subst_term_shift.
  set (D := List.cons (B == σ zero ⊕ k) G).
  assert (HD : has_inverse_context D).
  { unfold D. apply has_inverse_cons. exact HG. }
  pose proof (inverse_has_product D HD) as HP.
  assert (HBk : D ⊢C (B == σ zero ⊕ k)).
  { apply Ctx. unfold D. now left. }
  pose proof (PAOrder238.add_rec_instance D zero k (HP ax_add_rec product_add_rec)) as HBfirst.
  pose proof (PAAddition238.add_zero_instance D k (HP ax_add_zero product_add_zero)) as HBzero.
  pose proof (IE (successor_instance D (zero ⊕ k) k (inverse_equality D HD)) HBzero) as HBsecond.
  pose proof (inverse_transitivity D B (σ zero ⊕ k) (σ (zero ⊕ k))
    HD HBk HBfirst) as HBfront.
  pose proof (inverse_transitivity D B (σ (zero ⊕ k)) (σ k) HD HBfront HBsecond) as HB.
  assert (Hrs : List.In mult_right_successor_sentence D).
  { apply (commutative_has_multiplication D (inverse_has_commutative D HD)).
    exact multiplication_right_successor. }
  pose proof (inverse_multiplication D y y B (σ k) HD
    (inverse_reflexivity D y HD) HB) as Hyfirst.
  pose proof (mult_right_successor_at D y k Hrs) as Hysecond.
  pose proof (inverse_transitivity D (y ⊗ B) (y ⊗ σ k)
    (y ⊕ (y ⊗ k)) HD Hyfirst Hysecond) as Hy.
  pose proof (inverse_multiplication D x x B (σ k) HD
    (inverse_reflexivity D x HD) HB) as Hxfirst.
  pose proof (mult_right_successor_at D x k Hrs) as Hxsecond.
  pose proof (inverse_transitivity D (x ⊗ B) (x ⊗ σ k)
    (x ⊕ (x ⊗ k)) HD Hxfirst Hxsecond) as Hx.
  pose proof (weaken_head G (x ⊗ A == (y ⊗ B) ⊕ σ zero)
    (B == σ zero ⊕ k) Hinv) as HinvD.
  pose proof (inverse_addition D (y ⊗ B) (y ⊕ (y ⊗ k)) (σ zero) (σ zero) HD
    Hy (inverse_reflexivity D (σ zero) HD)) as Hinvnext.
  pose proof (inverse_transitivity D (x ⊗ A) ((y ⊗ B) ⊕ σ zero)
    ((y ⊕ (y ⊗ k)) ⊕ σ zero) HD HinvD Hinvnext) as Hinvfront.
  pose proof (inverse_symmetry D (y ⊕ ((y ⊗ k) ⊕ σ zero))
    ((y ⊕ (y ⊗ k)) ⊕ σ zero) HD
    (inverse_add_associative D y (y ⊗ k) (σ zero) HD)) as Hinvassoc.
  pose proof (inverse_transitivity D (x ⊗ A) ((y ⊕ (y ⊗ k)) ⊕ σ zero)
    (y ⊕ ((y ⊗ k) ⊕ σ zero)) HD Hinvfront Hinvassoc) as Hinvwhole.
  pose proof (mult_rec_instance D x A (HP ax_mult_rec product_mult_rec)) as HAfirst.
  pose proof (inverse_addition D A A (x ⊗ A) (y ⊕ ((y ⊗ k) ⊕ σ zero)) HD
    (inverse_reflexivity D A HD) Hinvwhole) as HAsecond.
  pose proof (add_exchange D A y ((y ⊗ k) ⊕ σ zero) (inverse_has_addition D HD)) as HAthird.
  pose proof (inverse_transitivity D (σ x ⊗ A) (A ⊕ (x ⊗ A))
    (A ⊕ (y ⊕ ((y ⊗ k) ⊕ σ zero))) HD HAfirst HAsecond) as HAfront.
  pose proof (inverse_transitivity D (σ x ⊗ A) (A ⊕ (y ⊕ ((y ⊗ k) ⊕ σ zero)))
    (y ⊕ (A ⊕ ((y ⊗ k) ⊕ σ zero))) HD HAfront HAthird) as HAwhole.
  pose proof (mult_rec_instance D x B (HP ax_mult_rec product_mult_rec)) as HBmulfirst.
  pose proof (inverse_addition D B B (x ⊗ B) (x ⊕ (x ⊗ k)) HD
    (inverse_reflexivity D B HD) Hx) as HBmulsecond.
  pose proof (add_exchange D B x (x ⊗ k) (inverse_has_addition D HD)) as HBmulthird.
  pose proof (inverse_transitivity D (σ x ⊗ B) (B ⊕ (x ⊗ B))
    (B ⊕ (x ⊕ (x ⊗ k))) HD HBmulfirst HBmulsecond) as HBmulfront.
  pose proof (inverse_transitivity D (σ x ⊗ B) (B ⊕ (x ⊕ (x ⊗ k)))
    (x ⊕ (B ⊕ (x ⊗ k))) HD HBmulfront HBmulthird) as HBmulwhole.
  apply CI.
  - exact (weak_order_witness D y (σ x ⊗ A) (A ⊕ ((y ⊗ k) ⊕ σ zero)) HAwhole).
  - exact (weak_order_witness D x (σ x ⊗ B) (B ⊕ (x ⊗ k)) HBmulwhole).
Qed.

Lemma inverse_exists_subst A B rho :
  (inverse_exists A B)[rho] = inverse_exists A`[rho] B`[rho].
Proof.
  unfold inverse_exists. cbn [subst_form]. rewrite inverse_pair_subst. now rewrite !up_term.
Qed.
Definition inverse_orientation_sentence : pa_form := ∀ ∀ ∀ ∀ ∀
  ($2 ⊗ $0 == ($3 ⊗ $1) ⊕ σ zero →
    $3 ⧀= ($4 ⊗ $0) → $2 ⧀= ($4 ⊗ $1) → inverse_exists $1 $0).
Definition positive_flip_context : list pa_form :=
  List.cons inverse_orientation_sentence inverse_context.
Lemma positive_flip_proof phi : positive_flip_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := inverse_orientation_sentence).
  - apply inverse_proof, II. exact HD.
  - exact inverse_orientation_from_bounds.
Qed.
Lemma inverse_orientation_at G A B x y K : List.In inverse_orientation_sentence G ->
  G ⊢C (x ⊗ A == (y ⊗ B) ⊕ σ zero →
    y ⧀= (K ⊗ A) → x ⧀= (K ⊗ B) → inverse_exists B A).
Proof.
  intros H. assert (HH : G ⊢C inverse_orientation_sentence) by now apply Ctx.
  assert (HB : bounded 5
    ($2 ⊗ $0 == ($3 ⊗ $1) ⊕ σ zero →
      $3 ⧀= ($4 ⊗ $0) → $2 ⧀= ($4 ⊗ $1) → inverse_exists $1 $0)).
  { unfold inverse_exists, inverse_pair, PAle. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := $2 ⊗ $0 == ($3 ⊗ $1) ⊕ σ zero →
      $3 ⧀= ($4 ⊗ $0) → $2 ⧀= ($4 ⊗ $1) → inverse_exists $1 $0)
    (N := 5) HH HB (A .: B .: x .: y .: K .: var)) as HK.
  change (G ⊢C (x ⊗ A == (y ⊗ B) ⊕ σ zero →
    (PAle $3 ($4 ⊗ $0))[A .: B .: x .: y .: K .: var] →
    (PAle $2 ($4 ⊗ $1))[A .: B .: x .: y .: K .: var] →
    (inverse_exists $1 $0)[A .: B .: x .: y .: K .: var])) in HK.
  rewrite !PAle_subst, inverse_exists_subst in HK. exact HK.
Qed.
Theorem inverse_orientation_positive : paeq_derivable (∀ ∀ ∀ ∀
  (zero ⧀ $1 → $2 ⊗ $0 == ($3 ⊗ $1) ⊕ σ zero → inverse_exists $1 $0)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize,
    positive_flip_proof, II, II.
  set (G := List.cons ($2 ⊗ $0 == ($3 ⊗ $1) ⊕ σ zero)
    (List.cons (zero ⧀ $1) positive_flip_context)).
  assert (HG : has_inverse_context G).
  { intros phi Hphi. unfold G, positive_flip_context. right. right. now right. }
  assert (Hpos : G ⊢C (zero ⧀ $1)).
  { apply Ctx. unfold G. right. now left. }
  assert (Hinv : G ⊢C ($2 ⊗ $0 == ($3 ⊗ $1) ⊕ σ zero)).
  { apply Ctx. unfold G. now left. }
  pose proof (inverse_complement_bounds G $0 $1 $2 $3 HG Hpos Hinv) as Hbounds.
  assert (Hrule : List.In inverse_orientation_sentence G).
  { unfold G, positive_flip_context. right. right. now left. }
  exact (IE (IE (IE (inverse_orientation_at G $0 $1 $2 $3 (σ $2) Hrule) Hinv)
    (CE1 Hbounds)) (CE2 Hbounds)).
Qed.

Lemma positive_predecessor_at G t : has_inverse_context G ->
  G ⊢C (zero ⧀ t) -> G ⊢C ∃ (t`[↑] == $0 ⊕ σ zero).
Proof.
  intros HG HP. unfold PAlt in HP. eapply ExE_named; [exact HP|]. intros p.
  change ((List.cons (t`[↑]`[p..] == σ zero ⊕ p) G) ⊢C
    ∃ (t`[↑] == $0 ⊕ σ zero)).
  rewrite subst_term_shift.
  set (D := List.cons (t == σ zero ⊕ p) G).
  assert (HD : has_inverse_context D).
  { unfold D. apply has_inverse_cons. exact HG. }
  assert (HT : D ⊢C (t == σ zero ⊕ p)).
  { apply Ctx. unfold D. now left. }
  pose proof (inverse_transitivity D t (σ zero ⊕ p) (p ⊕ σ zero) HD HT
    (inverse_add_commutative D (σ zero) p HD)) as Hpred.
  apply (ExI p). change (D ⊢C (t`[↑]`[p..] == p ⊕ σ zero)).
  rewrite subst_term_shift. exact Hpred.
Qed.
Theorem positive_predecessor :
  paeq_derivable (∀ (zero ⧀ $0 → ∃ ($1 == $0 ⊕ σ zero))).
Proof.
  apply paeq_generalize, inverse_proof, II.
  set (G := List.cons (zero ⧀ $0) inverse_context).
  apply (positive_predecessor_at G $0).
  - unfold G. apply has_inverse_cons. exact inverse_context_self.
  - apply Ctx. unfold G. now left.
Qed.

Definition factor_context : list pa_form :=
  [predecessor_sentence; order_ir_sentence] ++ inverse_context.
Lemma factor_proof phi : factor_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD.
  eapply paeq_modus_ponens with (phi := predecessor_sentence);
    [|exact PACancellation238.zero_or_successor].
  eapply paeq_modus_ponens with (phi := order_ir_sentence);
    [|exact PAOrder238.order_irreflexive].
  apply inverse_proof, II, II. exact HD.
Qed.
Lemma positive_factor_at G C q d : has_inverse_context G ->
  List.In predecessor_sentence G -> List.In order_ir_sentence G ->
  G ⊢C (zero ⧀ C) -> G ⊢C (C == q ⊗ d) -> G ⊢C (zero ⧀ q).
Proof.
  intros HG Hpred Hir HP HC.
  assert (Hcases : G ⊢C predecessor_sentence) by now apply Ctx.
  pose proof (AllE q Hcases) as HQ.
  change (G ⊢C ((q == zero) ∨ ∃ (q`[↑] == σ $0))) in HQ.
  eapply DE; [exact HQ| |].
  - set (D := List.cons (q == zero) G).
    change (D ⊢C (zero ⧀ q)).
    assert (HD : has_inverse_context D).
    { unfold D. apply has_inverse_cons. exact HG. }
    assert (HZ : D ⊢C (q == zero)).
    { apply Ctx. unfold D. now left. }
    pose proof (inverse_multiplication D q zero d d HD HZ
      (inverse_reflexivity D d HD)) as Hfirst.
    pose proof (mult_zero_instance D d
      (inverse_has_product D HD ax_mult_zero product_mult_zero)) as Hsecond.
    pose proof (inverse_transitivity D (q ⊗ d) (zero ⊗ d) zero HD Hfirst Hsecond) as Hmulzero.
    pose proof (weaken_head G (C == q ⊗ d) (q == zero) HC) as HCD.
    pose proof (inverse_transitivity D C (q ⊗ d) zero HD HCD Hmulzero) as HCzero.
    pose proof (formula_substitutivity D (PAlt zero $0) C zero
      (inverse_equality D HD) HCzero) as Htransfer.
    rewrite !PAlt_subst in Htransfer.
    pose proof (weaken_head G (zero ⧀ C) (q == zero) HP) as HPD.
    pose proof (IE (CE1 Htransfer) HPD) as Hbad.
    assert (HI : D ⊢C order_ir_sentence).
    { apply Ctx. unfold D. now right. }
    pose proof (AllE zero HI) as HIzero.
    change (D ⊢C ¬ ((PAlt $0 $0)[zero..])) in HIzero.
    rewrite PAlt_subst in HIzero. apply Exp. exact (IE HIzero Hbad).
  - set (D := List.cons (∃ (q`[↑] == σ $0)) G).
    change (D ⊢C (zero ⧀ q)).
    assert (HX : D ⊢C ∃ (q`[↑] == σ $0)).
    { apply Ctx. unfold D. now left. }
    eapply ExE_named; [exact HX|]. intros k.
    change ((List.cons (q`[↑]`[k..] == σ k) D) ⊢C (zero ⧀ q)).
    rewrite subst_term_shift.
    set (E := List.cons (q == σ k) D).
    assert (HE : has_inverse_context E).
    { unfold E, D. apply has_inverse_cons, has_inverse_cons. exact HG. }
    assert (Hq : E ⊢C (q == σ k)).
    { apply Ctx. unfold E. now left. }
    pose proof (inverse_symmetry E q (σ k) HE Hq) as Hback.
    pose proof (formula_substitutivity E (PAlt zero $0) (σ k) q
      (inverse_equality E HE) Hback) as Htransfer.
    rewrite !PAlt_subst in Htransfer.
    exact (IE (CE1 Htransfer) (PASemiring238.zero_below_successor E k
      (inverse_has_product E HE))).
Qed.
Theorem positive_quotient_factor : paeq_derivable (∀ ∀ ∀
  (zero ⧀ $0 → $0 == $1 ⊗ $2 → zero ⧀ $1)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, factor_proof, II, II.
  set (G := List.cons ($0 == $1 ⊗ $2) (List.cons (zero ⧀ $0) factor_context)).
  apply (positive_factor_at G $0 $1 $2).
  - intros phi Hphi. unfold G, factor_context. right. right. right. now right.
  - unfold G, factor_context. right. right. now left.
  - unfold G, factor_context. right. right. right. now left.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

Definition positive_orientation_sentence : pa_form := ∀ ∀ ∀ ∀
  (zero ⧀ $1 → $2 ⊗ $0 == ($3 ⊗ $1) ⊕ σ zero → inverse_exists $1 $0).
Definition pairwise_context : list pa_form :=
  List.cons positive_orientation_sentence factor_context.
Definition has_pairwise_context (G : list pa_form) : Prop :=
  forall phi, List.In phi pairwise_context -> List.In phi G.
Lemma pairwise_proof phi : pairwise_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := positive_orientation_sentence).
  - apply factor_proof, II. exact HD.
  - exact inverse_orientation_positive.
Qed.
Lemma pairwise_context_self : has_pairwise_context pairwise_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_pairwise_cons G phi : has_pairwise_context G ->
  has_pairwise_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma pairwise_has_inverse G : has_pairwise_context G -> has_inverse_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold pairwise_context, factor_context.
  right. right. now right.
Qed.
Lemma pairwise_predecessor G : has_pairwise_context G -> List.In predecessor_sentence G.
Proof. intros HG. apply HG. unfold pairwise_context, factor_context. right. now left. Qed.
Lemma pairwise_order_ir G : has_pairwise_context G -> List.In order_ir_sentence G.
Proof. intros HG. apply HG. unfold pairwise_context, factor_context. right. right. now left. Qed.
Lemma positive_orientation_at G A B x y : has_pairwise_context G ->
  G ⊢C (zero ⧀ B → x ⊗ A == (y ⊗ B) ⊕ σ zero → inverse_exists B A).
Proof.
  intros HG. assert (HH : G ⊢C positive_orientation_sentence).
  { apply Ctx, HG. unfold pairwise_context. now left. }
  assert (HB : bounded 4
    (zero ⧀ $1 → $2 ⊗ $0 == ($3 ⊗ $1) ⊕ σ zero → inverse_exists $1 $0)).
  { unfold inverse_exists, inverse_pair, PAlt. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := zero ⧀ $1 → $2 ⊗ $0 == ($3 ⊗ $1) ⊕ σ zero → inverse_exists $1 $0)
    (N := 4) HH HB (A .: B .: x .: y .: var)) as HK.
  change (G ⊢C ((PAlt zero $1)[A .: B .: x .: y .: var] →
    x ⊗ A == (y ⊗ B) ⊕ σ zero →
    (inverse_exists $1 $0)[A .: B .: x .: y .: var])) in HK.
  rewrite PAlt_subst, inverse_exists_subst in HK. exact HK.
Qed.

Lemma one_sum_positive G a : has_inverse_context G -> G ⊢C (zero ⧀ (σ zero ⊕ a)).
Proof.
  intros HG. pose proof (inverse_has_product G HG) as HP.
  pose proof (PAOrder238.add_rec_instance G zero a (HP ax_add_rec product_add_rec)) as Hfirst.
  pose proof (PAAddition238.add_zero_instance G a (HP ax_add_zero product_add_zero)) as Hzero.
  pose proof (IE (successor_instance G (zero ⊕ a) a (inverse_equality G HG)) Hzero) as Hsecond.
  pose proof (inverse_transitivity G (σ zero ⊕ a) (σ (zero ⊕ a)) (σ a)
    HG Hfirst Hsecond) as Hsum.
  pose proof (inverse_symmetry G (σ zero ⊕ a) (σ a) HG Hsum) as Hback.
  pose proof (formula_substitutivity G (PAlt zero $0) (σ a) (σ zero ⊕ a)
    (inverse_equality G HG) Hback) as Htransfer.
  rewrite !PAlt_subst in Htransfer.
  exact (IE (CE1 Htransfer) (PASemiring238.zero_below_successor G a HP)).
Qed.

(* The old divisibility witness supplies q, rather than a division-totality
   theorem. Positivity of C makes q positive. The positive product u*v*q
   then supplies the predecessor p used in the exact polynomial identity. *)
Lemma special_moduli_inverse_exists_at G u v C d : has_pairwise_context G ->
  G ⊢C (zero ⧀ u) -> G ⊢C (zero ⧀ v) -> G ⊢C (zero ⧀ C) ->
  G ⊢C (v == u ⊕ d) -> G ⊢C divides d C ->
  G ⊢C inverse_exists (σ zero ⊕ (u ⊗ C)) (σ zero ⊕ (v ⊗ C)).
Proof.
  intros HG Hu Hv HC Hgap Hdiv. eapply divides_eliminate; [exact Hdiv|]. intros q.
  set (D := List.cons (C == d ⊗ q) G).
  assert (HD : has_pairwise_context D).
  { unfold D. apply has_pairwise_cons. exact HG. }
  pose proof (pairwise_has_inverse D HD) as HI.
  assert (HCd : D ⊢C (C == d ⊗ q)).
  { apply Ctx. unfold D. now left. }
  pose proof (inverse_transitivity D C (d ⊗ q) (q ⊗ d) HI HCd
    (inverse_mul_commutative D d q HI)) as HCq.
  pose proof (weaken_head G (zero ⧀ C) (C == d ⊗ q) HC) as HCD.
  pose proof (positive_factor_at D C q d HI (pairwise_predecessor D HD)
    (pairwise_order_ir D HD) HCD HCq) as Hq.
  pose proof (weaken_head G (zero ⧀ u) (C == d ⊗ q) Hu) as HuD.
  pose proof (weaken_head G (zero ⧀ v) (C == d ⊗ q) Hv) as HvD.
  pose proof (positive_product D u v (inverse_has_product D HI) HuD HvD) as Huv.
  pose proof (positive_product D (u ⊗ v) q (inverse_has_product D HI) Huv Hq) as HT.
  pose proof (positive_predecessor_at D ((u ⊗ v) ⊗ q) HI HT) as HP.
  eapply ExE_named; [exact HP|]. intros p.
  change ((List.cons (((u ⊗ v) ⊗ q)`[↑]`[p..] == p ⊕ σ zero) D) ⊢C
    inverse_exists (σ zero ⊕ (u ⊗ C)) (σ zero ⊕ (v ⊗ C))).
  rewrite subst_term_shift.
  set (E := List.cons ((u ⊗ v) ⊗ q == p ⊕ σ zero) D).
  assert (HE : has_pairwise_context E).
  { unfold E. apply has_pairwise_cons. exact HD. }
  pose proof (pairwise_has_inverse E HE) as HIE.
  assert (HTp : E ⊢C ((u ⊗ v) ⊗ q == p ⊕ σ zero)).
  { apply Ctx. unfold E. now left. }
  assert (HgapE : E ⊢C (v == u ⊕ d)).
  { unfold E, D. apply weaken_head, weaken_head. exact Hgap. }
  pose proof (weaken_head D (C == q ⊗ d) ((u ⊗ v) ⊗ q == p ⊕ σ zero) HCq) as HCqE.
  pose proof (special_moduli_inverse_at E u v C q d p HIE HgapE HCqE HTp) as Hpoly.
  pose proof (one_sum_positive E (u ⊗ C) HIE) as Hmodpos.
  exact (IE (IE (positive_orientation_at E (σ zero ⊕ (v ⊗ C))
    (σ zero ⊕ (u ⊗ C)) ((u ⊗ u) ⊗ q) p HE) Hmodpos) Hpoly).
Qed.
Theorem special_moduli_pairwise_inverse : paeq_derivable (∀ ∀ ∀ ∀
  (zero ⧀ $0 → zero ⧀ $1 → zero ⧀ $2 → $1 == $0 ⊕ $3 → divides $3 $2 →
    inverse_exists (σ zero ⊕ ($0 ⊗ $2)) (σ zero ⊕ ($1 ⊗ $2)))).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize,
    pairwise_proof, II, II, II, II, II.
  set (G := List.cons (divides $3 $2) (List.cons ($1 == $0 ⊕ $3)
    (List.cons (zero ⧀ $2) (List.cons (zero ⧀ $1)
      (List.cons (zero ⧀ $0) pairwise_context))))).
  apply (special_moduli_inverse_exists_at G $0 $1 $2 $3).
  - unfold G. apply has_pairwise_cons, has_pairwise_cons, has_pairwise_cons,
      has_pairwise_cons, has_pairwise_cons. exact pairwise_context_self.
  - apply Ctx. unfold G. right. right. right. right. now left.
  - apply Ctx. unfold G. right. right. right. now left.
  - apply Ctx. unfold G. right. right. now left.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

End PAModuliInverse238.

Print Assumptions PAModuliInverse238.inverse_proof.
Print Assumptions PAModuliInverse238.inverse_right_distribution.
Print Assumptions PAModuliInverse238.inverse_mul_pair_shuffle.
Print Assumptions PAModuliInverse238.special_moduli_inverse_polynomial.
Print Assumptions PAModuliInverse238.product_inverse_polynomial.
Print Assumptions PAModuliInverse238.inverse_orientation_from_bounds.
Print Assumptions PAModuliInverse238.inverse_orientation_positive.
Print Assumptions PAModuliInverse238.positive_predecessor.
Print Assumptions PAModuliInverse238.positive_quotient_factor.
Print Assumptions PAModuliInverse238.special_moduli_pairwise_inverse.
