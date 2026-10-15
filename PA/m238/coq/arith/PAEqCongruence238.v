(* Original finite natural-deduction constructions for equality in PA.
   Every certificate below uses only the six explicit upstream EQ axioms.
   Formula substitutivity is proved by syntax induction, including binders;
   no semantic equality or arithmetic interpretation is assumed. *)
From Coq Require Import List Vector.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
From P238.arith Require Import PAeq238.

Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations Vector.VectorNotations FullSyntax PA238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAEqCongruence238.

Definition has_equality (G : list pa_form) : Prop :=
  forall phi, List.In phi EQ -> List.In phi G.

Lemma has_equality_cons G phi : has_equality G -> has_equality (phi :: G).
Proof. intros H psi Hpsi. right. now apply H. Qed.

Lemma weaken_head G phi psi : G ⊢C phi -> (psi :: G) ⊢C phi.
Proof. intros H. eapply Weak; [exact H|]. intros chi Hchi. now right. Qed.

Lemma reflexivity_instance G a : has_equality G -> G ⊢C (a == a).
Proof.
  intros HE. change (G ⊢C ($0 == $0)[a..]).
  apply (subst_forall_prv (phi := $0 == $0) (N := 1)).
  - change (G ⊢C ax_refl). apply Ctx, HE. unfold EQ. now left.
  - solve_bounds.
Qed.

Lemma symmetry_instance G a b : has_equality G ->
  G ⊢C (a == b → b == a).
Proof.
  intros HE. change (G ⊢C ($1 == $0 → $0 == $1)[b .: a .: var]).
  apply (subst_forall_prv (phi := $1 == $0 → $0 == $1) (N := 2)).
  - change (G ⊢C ax_sym). apply Ctx, HE. unfold EQ. right. now left.
  - solve_bounds.
Qed.

Lemma transitivity_instance G a b c : has_equality G ->
  G ⊢C (a == b → b == c → a == c).
Proof.
  intros HE.
  change (G ⊢C ($2 == $1 → $1 == $0 → $2 == $0)[c .: b .: a .: var]).
  apply (subst_forall_prv (phi := $2 == $1 → $1 == $0 → $2 == $0) (N := 3)).
  - change (G ⊢C ax_trans). apply Ctx, HE. unfold EQ. right. right. now left.
  - solve_bounds.
Qed.

Lemma successor_instance G a b : has_equality G ->
  G ⊢C (a == b → σ a == σ b).
Proof.
  intros HE. change (G ⊢C ($0 == $1 → σ $0 == σ $1)[a .: b .: var]).
  apply (subst_forall_prv (phi := $0 == $1 → σ $0 == σ $1) (N := 2)).
  - change (G ⊢C ax_succ_congr). apply Ctx, HE. unfold EQ. right. right. right. now left.
  - solve_bounds.
Qed.

Lemma addition_instance G a b c d : has_equality G ->
  G ⊢C (a == b → c == d → a ⊕ c == b ⊕ d).
Proof.
  intros HE.
  change (G ⊢C ($0 == $1 → $2 == $3 → $0 ⊕ $2 == $1 ⊕ $3)
    [a .: b .: c .: d .: var]).
  apply (subst_forall_prv
    (phi := $0 == $1 → $2 == $3 → $0 ⊕ $2 == $1 ⊕ $3) (N := 4)).
  - change (G ⊢C ax_add_congr). apply Ctx, HE. unfold EQ. right. right. right. right. now left.
  - solve_bounds.
Qed.

Lemma multiplication_instance G a b c d : has_equality G ->
  G ⊢C (a == b → c == d → a ⊗ c == b ⊗ d).
Proof.
  intros HE.
  change (G ⊢C ($0 == $1 → $2 == $3 → $0 ⊗ $2 == $1 ⊗ $3)
    [a .: b .: c .: d .: var]).
  apply (subst_forall_prv
    (phi := $0 == $1 → $2 == $3 → $0 ⊗ $2 == $1 ⊗ $3) (N := 4)).
  - change (G ⊢C ax_mult_congr). apply Ctx, HE. unfold EQ. right. right. right. right. right. now left.
  - solve_bounds.
Qed.

Lemma equality_symmetry G a b : has_equality G ->
  G ⊢C (a == b) -> G ⊢C (b == a).
Proof. intros HE H. eapply IE; [apply symmetry_instance, HE|exact H]. Qed.

Lemma equality_transitivity G a b c : has_equality G ->
  G ⊢C (a == b) -> G ⊢C (b == c) -> G ⊢C (a == c).
Proof.
  intros HE H K. eapply IE; [|exact K].
  eapply IE; [apply transitivity_instance, HE|exact H].
Qed.

Lemma vector0_eta X (v : Vector.t X 0) : v = [].
Proof. revert v. apply Vector.case0. reflexivity. Qed.

Lemma vector2_eta X (v : Vector.t X 2) :
  v = [Vector.hd v; Vector.hd (Vector.tl v)].
Proof. rewrite (Vector.eta v) at 1. f_equal. apply destruct_vector_single. Qed.

Lemma term_substitution_equal (t : pa_term) :
  forall G rho tau, has_equality G ->
  (forall n, G ⊢C (rho n == tau n)) -> G ⊢C (t`[rho] == t`[tau]).
Proof.
  induction t as [n|f v IH] using term_ind; intros G rho tau HE HR.
  - apply HR.
  - destruct f.
    + rewrite (vector0_eta pa_term v). cbn. apply reflexivity_instance, HE.
    + rewrite (destruct_vector_single v) in *. cbn.
      eapply IE with (phi := (Vector.hd v)`[rho] == (Vector.hd v)`[tau]).
      * exact (successor_instance G (Vector.hd v)`[rho] (Vector.hd v)`[tau] HE).
      * apply IH; [now constructor|exact HE|exact HR].
    + rewrite (vector2_eta pa_term v) in *. cbn.
      eapply IE with
        (phi := (Vector.hd (Vector.tl v))`[rho] == (Vector.hd (Vector.tl v))`[tau]).
      * eapply IE with (phi := (Vector.hd v)`[rho] == (Vector.hd v)`[tau]).
        -- exact (addition_instance G (Vector.hd v)`[rho] (Vector.hd v)`[tau]
             (Vector.hd (Vector.tl v))`[rho] (Vector.hd (Vector.tl v))`[tau] HE).
        -- apply IH; [now constructor|exact HE|exact HR].
      * apply IH; [constructor 2; now constructor|exact HE|exact HR].
    + rewrite (vector2_eta pa_term v) in *. cbn.
      eapply IE with
        (phi := (Vector.hd (Vector.tl v))`[rho] == (Vector.hd (Vector.tl v))`[tau]).
      * eapply IE with (phi := (Vector.hd v)`[rho] == (Vector.hd v)`[tau]).
        -- exact (multiplication_instance G (Vector.hd v)`[rho] (Vector.hd v)`[tau]
             (Vector.hd (Vector.tl v))`[rho] (Vector.hd (Vector.tl v))`[tau] HE).
        -- apply IH; [now constructor|exact HE|exact HR].
      * apply IH; [constructor 2; now constructor|exact HE|exact HR].
Qed.

Lemma equality_atom_equivalent G a b c d : has_equality G ->
  G ⊢C (a == b) -> G ⊢C (c == d) ->
  G ⊢C ((a == c) ↔ (b == d)).
Proof.
  intros HE H K. apply CI.
  - apply II. set (D := List.cons (a == c) G).
    change (D ⊢C (b == d)).
    assert (HE' : has_equality D).
    { unfold D. exact (has_equality_cons G (a == c) HE). }
    assert (HA : D ⊢C (a == b)).
    { unfold D. exact (weaken_head G (a == b) (a == c) H). }
    assert (HK : D ⊢C (c == d)).
    { unfold D. exact (weaken_head G (c == d) (a == c) K). }
    assert (HC : D ⊢C (a == c)).
    { apply Ctx. unfold D. now left. }
    pose proof (equality_symmetry D a b HE' HA) as BA.
    pose proof (equality_transitivity D b a c HE' BA HC) as BC.
    exact (equality_transitivity D b c d HE' BC HK).
  - apply II. set (D := List.cons (b == d) G).
    change (D ⊢C (a == c)).
    assert (HE' : has_equality D).
    { unfold D. exact (has_equality_cons G (b == d) HE). }
    assert (HA : D ⊢C (a == b)).
    { unfold D. exact (weaken_head G (a == b) (b == d) H). }
    assert (HK : D ⊢C (c == d)).
    { unfold D. exact (weaken_head G (c == d) (b == d) K). }
    assert (HD : D ⊢C (b == d)).
    { apply Ctx. unfold D. now left. }
    pose proof (equality_symmetry D c d HE' HK) as DC.
    pose proof (equality_transitivity D a b d HE' HA HD) as AD.
    exact (equality_transitivity D a d c HE' AD DC).
Qed.

Lemma equivalence_reflexivity G phi : G ⊢C (phi ↔ phi).
Proof. apply CI; apply II, Ctx; now left. Qed.

Lemma conjunction_equivalent G phi phi' psi psi' :
  G ⊢C (phi ↔ phi') -> G ⊢C (psi ↔ psi') ->
  G ⊢C ((phi ∧ psi) ↔ (phi' ∧ psi')).
Proof.
  intros H K. apply CI; apply II, CI.
  - eapply IE; [apply weaken_head; exact (CE1 H)|]. eapply CE1. apply Ctx. now left.
  - eapply IE; [apply weaken_head; exact (CE1 K)|]. eapply CE2. apply Ctx. now left.
  - eapply IE; [apply weaken_head; exact (CE2 H)|]. eapply CE1. apply Ctx. now left.
  - eapply IE; [apply weaken_head; exact (CE2 K)|]. eapply CE2. apply Ctx. now left.
Qed.

Lemma disjunction_equivalent G phi phi' psi psi' :
  G ⊢C (phi ↔ phi') -> G ⊢C (psi ↔ psi') ->
  G ⊢C ((phi ∨ psi) ↔ (phi' ∨ psi')).
Proof.
  intros H K. apply CI.
  - apply II. eapply DE; [apply Ctx; now left| |].
    + apply DI1. eapply IE; [apply weaken_head, weaken_head; exact (CE1 H)|].
      apply Ctx. now left.
    + apply DI2. eapply IE; [apply weaken_head, weaken_head; exact (CE1 K)|].
      apply Ctx. now left.
  - apply II. eapply DE; [apply Ctx; now left| |].
    + apply DI1. eapply IE; [apply weaken_head, weaken_head; exact (CE2 H)|].
      apply Ctx. now left.
    + apply DI2. eapply IE; [apply weaken_head, weaken_head; exact (CE2 K)|].
      apply Ctx. now left.
Qed.

Lemma implication_equivalent G phi phi' psi psi' :
  G ⊢C (phi ↔ phi') -> G ⊢C (psi ↔ psi') ->
  G ⊢C ((phi → psi) ↔ (phi' → psi')).
Proof.
  intros H K. apply CI; apply II, II.
  - eapply IE; [apply weaken_head, weaken_head; exact (CE1 K)|].
    eapply IE; [apply Ctx; right; now left|].
    eapply IE; [apply weaken_head, weaken_head; exact (CE2 H)|].
    apply Ctx. now left.
  - eapply IE; [apply weaken_head, weaken_head; exact (CE2 K)|].
    eapply IE; [apply Ctx; right; now left|].
    eapply IE; [apply weaken_head, weaken_head; exact (CE1 H)|].
    apply Ctx. now left.
Qed.

Lemma instantiate_up phi rho t : (phi[up rho])[t..] = phi[t .: rho].
Proof.
  rewrite subst_comp. apply subst_ext. intros [|n]; cbn; [reflexivity|].
  apply subst_term_shift.
Qed.

Lemma substitution_equal_cons G rho tau t : has_equality G ->
  (forall n, G ⊢C (rho n == tau n)) ->
  forall n, G ⊢C ((t .: rho) n == (t .: tau) n).
Proof. intros HE HR [|n]; cbn; [apply reflexivity_instance, HE|apply HR]. Qed.

Lemma formula_substitution_equivalent (phi : pa_form) :
  forall G rho tau, has_equality G ->
  (forall n, G ⊢C (rho n == tau n)) -> G ⊢C (phi[rho] ↔ phi[tau]).
Proof.
  induction phi as [|p v|b phi IHphi psi IHpsi|q phi IHphi] using form_ind_falsity;
    intros G rho tau HE HR; cbn [subst_form].
  - apply equivalence_reflexivity.
  - destruct p. rewrite (vector2_eta pa_term v). cbn.
    apply equality_atom_equivalent.
    + exact HE.
    + apply term_substitution_equal; [exact HE|exact HR].
    + apply term_substitution_equal; [exact HE|exact HR].
  - destruct b.
    + apply conjunction_equivalent; [apply IHphi|apply IHpsi]; assumption.
    + apply disjunction_equivalent; [apply IHphi|apply IHpsi]; assumption.
    + apply implication_equivalent; [apply IHphi|apply IHpsi]; assumption.
  - destruct q.
    + apply CI.
      * apply II, AllI_named. intros t. rewrite (instantiate_up phi tau t).
        assert (HE' : has_equality (List.cons (∀ phi[up rho]) G)).
        { now apply has_equality_cons. }
        assert (HR' : forall n, (List.cons (∀ phi[up rho]) G) ⊢C
          ((t .: rho) n == (t .: tau) n)).
        { apply substitution_equal_cons; [exact HE'|].
          intros n. apply weaken_head, HR. }
        pose proof (IHphi (List.cons (∀ phi[up rho]) G)
          (t .: rho) (t .: tau) HE' HR') as HI.
        eapply IE; [exact (CE1 HI)|].
        rewrite <- (instantiate_up phi rho t). apply (AllE t), Ctx. now left.
      * apply II, AllI_named. intros t. rewrite (instantiate_up phi rho t).
        assert (HE' : has_equality (List.cons (∀ phi[up tau]) G)).
        { now apply has_equality_cons. }
        assert (HR' : forall n, (List.cons (∀ phi[up tau]) G) ⊢C
          ((t .: rho) n == (t .: tau) n)).
        { apply substitution_equal_cons; [exact HE'|].
          intros n. apply weaken_head, HR. }
        pose proof (IHphi (List.cons (∀ phi[up tau]) G)
          (t .: rho) (t .: tau) HE' HR') as HI.
        eapply IE; [exact (CE2 HI)|].
        rewrite <- (instantiate_up phi tau t). apply (AllE t), Ctx. now left.
    + apply CI.
      * apply II. eapply ExE_named; [apply Ctx; now left|]. intros t.
        set (D := List.cons (phi[up rho])[t..] (List.cons (∃ phi[up rho]) G)).
        change (D ⊢C ∃ phi[up tau]).
        apply (ExI t). rewrite (instantiate_up phi tau t).
        assert (HE' : has_equality D).
        { unfold D. apply has_equality_cons. now apply has_equality_cons. }
        assert (HR' : forall n, D ⊢C ((t .: rho) n == (t .: tau) n)).
        { apply substitution_equal_cons; [exact HE'|].
          intros n. unfold D. apply weaken_head, weaken_head, HR. }
        pose proof (IHphi D (t .: rho) (t .: tau) HE' HR') as HI.
        eapply IE; [exact (CE1 HI)|].
        rewrite <- (instantiate_up phi rho t). apply Ctx. unfold D. now left.
      * apply II. eapply ExE_named; [apply Ctx; now left|]. intros t.
        set (D := List.cons (phi[up tau])[t..] (List.cons (∃ phi[up tau]) G)).
        change (D ⊢C ∃ phi[up rho]).
        apply (ExI t). rewrite (instantiate_up phi rho t).
        assert (HE' : has_equality D).
        { unfold D. apply has_equality_cons. now apply has_equality_cons. }
        assert (HR' : forall n, D ⊢C ((t .: rho) n == (t .: tau) n)).
        { apply substitution_equal_cons; [exact HE'|].
          intros n. unfold D. apply weaken_head, weaken_head, HR. }
        pose proof (IHphi D (t .: rho) (t .: tau) HE' HR') as HI.
        eapply IE; [exact (CE2 HI)|].
        rewrite <- (instantiate_up phi tau t). apply Ctx. unfold D. now left.
Qed.

Lemma formula_substitutivity G phi a b : has_equality G ->
  G ⊢C (a == b) -> G ⊢C (phi[a..] ↔ phi[b..]).
Proof.
  intros HE H. apply formula_substitution_equivalent; [exact HE|].
  intros [|n]; cbn; [exact H|apply reflexivity_instance, HE].
Qed.

Lemma equality_context_PAeq phi : List.In phi EQ -> PAeq phi.
Proof.
  intros H. apply PAeq_FA. unfold FAeq. apply List.in_app_iff. now left.
Qed.

Theorem ordinary_formula_substitutivity phi a b :
  paeq_derivable (a == b → phi[a..] → phi[b..]).
Proof.
  apply paeq_from_upstream. exists EQ. split; [exact equality_context_PAeq|].
  apply II, II.
  set (D := List.cons phi[a..] (List.cons (a == b) EQ)).
  change (D ⊢C phi[b..]).
  assert (HE : has_equality D).
  { unfold D. apply has_equality_cons, has_equality_cons.
    intros chi Hchi. exact Hchi. }
  assert (HR : forall n, D ⊢C ((a..) n == (b..) n)).
  { intros [|n]; cbn.
    - apply Ctx. unfold D. right. now left.
    - exact (reflexivity_instance D $n HE). }
  pose proof (formula_substitution_equivalent phi D (a..) (b..) HE HR) as HI.
  eapply IE; [exact (CE1 HI)|]. apply Ctx. unfold D. now left.
Qed.

End PAEqCongruence238.

Print Assumptions PAEqCongruence238.term_substitution_equal.
Print Assumptions PAEqCongruence238.formula_substitution_equivalent.
Print Assumptions PAEqCongruence238.ordinary_formula_substitutivity.
