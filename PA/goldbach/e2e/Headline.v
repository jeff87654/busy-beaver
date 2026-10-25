(** * Headline: the 449-state Turing machine pa_wade.tm halts from the blank tape iff Peano arithmetic
    proves Goldbach's conjecture.  No axioms (see the Print Assumptions at the end).

    - [halts], [c0]: busycoq's TM semantics (third_party/busycoq/verify/TM.v, functor TM instantiated
      as PAGBT.ZFTM.ZFTM with 2 symbols and the 450 states of the machine), blank tape, start state.
    - [tm]: PAGBT.ZFTM.tm.  [PAGBT.ZFTM.tm_table] proves it equal to the literal table [pa_table] of
      tm/coq/TablePA.v, which tm/check_tm.py compares with machine/pa_wade.tm
      (sha256 ed795af79b6752d72c037d7e32eca1d23efaa6a6c0f0d07fc7ba89869f2616a6).
    - [PAeq], [tprv] (written ⊢TC), [sat], [interp_nat]: the Coq Library of Undecidability Proofs
      (vendored unmodified in vendor/): PA with the equality axioms and the full induction schema,
      classical natural deduction, Tarski semantics, the standard model of arithmetic.
    Chain: TM -> register machine (tm/) -> enumerator (prog/) -> code-level calculus -> named Hilbert
    calculus -> library natural deduction (coq/). *)
From Coq Require Import Arith.
From BusyCoq Require TM.
From PAGBT Require ZFTM MainTM.
From PAGBP Require MainPA.
From PAGB Require Spec PA_Logic.
From Undecidability.FOL Require Import PA.
From Undecidability.FOL.Arithmetics Require Import NatModel.

(** ** Goldbach's conjecture as a sentence of PA (de Bruijn indices: $0 = innermost bound variable) *)
Definition leq (s t : term) : form := ∃ (t`[↑] == s`[↑] ⊕ $0).            (* s ≤ t :  ∃z. t = s + z *)
Definition even (t : term) : form := ∃ (t`[↑] == $0 ⊕ $0).               (* ∃k. t = k + k *)
Definition Pr (t : term) : form :=                                        (* t is prime *)
  leq (num 2) t ∧ (∀ ∀ ((t`[↑]`[↑] == $1 ⊗ $0) → (($1 == num 1) ∨ ($0 == num 1)))).
(* ∀n. (n even ∧ 4 ≤ n) → ∃p ∃q. (Pr p ∧ Pr q) ∧ p + q = n   (under ∃p∃q: q = $0, p = $1, n = $2) *)
Definition GC_form : form :=
  ∀ ((even $0 ∧ leq (num 4) $0) → ∃ ∃ ((Pr $1 ∧ Pr $0) ∧ ($1 ⊕ $0 == $2))).

(** ** The same statement about nat *)
Definition prime_nat (p : nat) : Prop := 2 <= p /\ forall d, Nat.divide d p -> d = 1 \/ d = p.
Definition Goldbach_nat : Prop :=
  forall n, Nat.Even n -> 4 <= n -> exists p q, prime_nat p /\ prime_nat q /\ p + q = n.

(** the layer files use exactly these definitions *)
Lemma same_GC : GC_form = Spec.GC_form.  Proof. reflexivity. Qed.
Lemma same_Goldbach : Goldbach_nat = Spec.Goldbach_nat.  Proof. reflexivity. Qed.

(** ** The theorems *)
Theorem pagb_halts_iff_PA_GC :
  PAGBT.ZFTM.ZFTM.halts PAGBT.ZFTM.tm PAGBT.ZFTM.ZFTM.c0 <-> @tprv _ _ falsity_on class PAeq GC_form.
Proof.
  rewrite PAGBT.MainTM.tmpa_rm, PAGBP.MainPA.progpa, same_GC.
  exact PAGB.PA_Logic.enum_halts_iff_PA_GC.
Qed.

Theorem GC_adequate rho : sat interp_nat rho GC_form <-> Goldbach_nat.
Proof. rewrite same_GC, same_Goldbach. exact (PAGB.Spec.GC_adequate rho). Qed.

Print Assumptions pagb_halts_iff_PA_GC.
Print Assumptions GC_adequate.
