(** * Spec: Goldbach's conjecture as a sentence of Peano arithmetic, and the target statement.

    Syntax, axioms and deduction are the Coq Library of Undecidability Proofs' (vendored unmodified,
    vendor/README.md):
      - signature: zero, σ, ⊕, ⊗ and the binary predicate == (FOL/Arithmetics/Signature.v);
      - PAeq: the defining equations of + and ×, 0 ≠ S x, injectivity of S, the equality axioms
        (reflexivity, symmetry, transitivity, congruence for σ, ⊕, ⊗) and every instance of the
        induction schema (FOL/Arithmetics/PA.v);
      - ⊢TC: classical natural deduction from finitely many axioms (FOL/Deduction/FullND.v).
    Terms and formulas use de Bruijn indices: $0 is the variable bound by the nearest quantifier.

    Main definitions and results:
      GC_form           the sentence  ∀n. (n even ∧ n ≥ 4) → ∃p ∃q. (Pr p ∧ Pr q) ∧ p + q = n
      Goldbach_nat      the same statement about Coq's nat
      GC_adequate       the standard model satisfies GC_form  <->  Goldbach_nat
      PA_proves_GC      PAeq ⊢TC GC_form                         (the target headline)
      PA_GC_refutation  PAeq ⊢TC GC_form  <->  (extend PAeq ¬GC_form) ⊢TC ⊥ *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import PA.
From Undecidability.FOL.Arithmetics Require Import NatModel.
From Undecidability.FOL Require Import Syntax.Theories.
Import Vector.VectorNotations.

(** ** The sentence *)

(** [leq s t]:  s ≤ t,  i.e.  ∃z. t = s + z *)
Definition leq (s t : term) : form := ∃ (t`[↑] == s`[↑] ⊕ $0).

(** [even t]:  ∃k. t = k + k *)
Definition even (t : term) : form := ∃ (t`[↑] == $0 ⊕ $0).

(** [Pr t]:  t is prime:  2 ≤ t, and whenever t = a × b, then a = 1 or b = 1 *)
Definition Pr (t : term) : form :=
  leq (num 2) t ∧ (∀ ∀ ((t`[↑]`[↑] == $1 ⊗ $0) → (($1 == num 1) ∨ ($0 == num 1)))).

(** Goldbach:  ∀n. (even n ∧ 4 ≤ n) → ∃p ∃q. (Pr p ∧ Pr q) ∧ p + q = n.
    Under ∃p ∃q the indices are q = $0, p = $1, n = $2. *)
Definition GC_form : form :=
  ∀ ((even $0 ∧ leq (num 4) $0) → ∃ ∃ ((Pr $1 ∧ Pr $0) ∧ ($1 ⊕ $0 == $2))).

Definition NG_form : form := ¬ GC_form.

Lemma leq_PAle s t : leq s t = (s ⧀= t).
Proof. reflexivity. Qed.

Lemma GC_closed : closed GC_form.
Proof.
  unfold closed, GC_form, Pr, even, leq. cbn.
  repeat solve_bounds; apply num_bound.
Qed.

(** ** The statement over nat *)

Definition prime_nat (p : nat) : Prop := 2 <= p /\ forall d, Nat.divide d p -> d = 1 \/ d = p.

Definition Goldbach_nat : Prop :=
  forall n, Nat.Even n -> 4 <= n -> exists p q, prime_nat p /\ prime_nat q /\ p + q = n.

(** ** Adequacy in the standard model (interp_nat: FOL/Arithmetics/NatModel.v) *)

Section Adequacy.
  Existing Instance interp_nat.

  Lemma sat_leq rho s t : rho ⊨ leq s t <-> eval rho s <= eval rho t.
  Proof.
    unfold leq. cbn. setoid_rewrite eval_up. split.
    - intros [z ->]. lia.
    - intros H. exists (eval rho t - eval rho s). lia.
  Qed.

  Lemma sat_even rho t : rho ⊨ even t <-> Nat.Even (eval rho t).
  Proof.
    unfold even. cbn. setoid_rewrite eval_up. split.
    - intros [k ->]. exists k. lia.
    - intros [k ->]. exists k. lia.
  Qed.

  Lemma prime_nat_mul p : prime_nat p <-> 2 <= p /\ forall a b, p = a * b -> a = 1 \/ b = 1.
  Proof.
    split.
    - intros [H2 H] ; split; [exact H2|]. intros a b E.
      destruct (H a) as [Ha|Ha]; [exists b; lia | now left |].
      right. subst p. destruct b as [|[|b]]; lia.
    - intros [H2 H]; split; [exact H2|]. intros d [k E].
      destruct (H k d E) as [->| ->]; [right; lia | now left].
  Qed.

  Lemma sat_Pr rho t : rho ⊨ Pr t <-> prime_nat (eval rho t).
  Proof.
    unfold Pr. cbn [sat]. rewrite sat_leq, prime_nat_mul. cbn. setoid_rewrite eval_up. setoid_rewrite eval_up.
    reflexivity.
  Qed.

  Theorem GC_adequate rho : rho ⊨ GC_form <-> Goldbach_nat.
  Proof.
    unfold GC_form, Goldbach_nat. cbn [sat]. setoid_rewrite sat_even. setoid_rewrite sat_leq.
    setoid_rewrite sat_Pr. cbn. split.
    - intros H n Hn H4. destruct (H n (conj Hn H4)) as [p [q [[Hp Hq] E]]]. eauto.
    - intros H n [Hn H4]. destruct (H n Hn H4) as [p [q [Hp [Hq E]]]].
      exists p, q. auto.
  Qed.

  Theorem NG_adequate rho : rho ⊨ NG_form <-> ~ Goldbach_nat.
  Proof. unfold NG_form. cbn. now rewrite GC_adequate. Qed.
End Adequacy.

(** ** The target statement and the refutation form *)

Definition PA_proves_GC : Prop := @tprv _ _ falsity_on class PAeq GC_form.

Definition PA_NG_inconsistent : Prop := @tprv _ _ falsity_on class (extend PAeq NG_form) falsity.

Theorem PA_GC_refutation : PA_proves_GC <-> PA_NG_inconsistent.
Proof. exact (@refutation_prv _ _ PA_funcs_eq PA_preds_eq PAeq GC_form). Qed.

Print Assumptions GC_adequate.
Print Assumptions NG_adequate.
Print Assumptions PA_GC_refutation.
