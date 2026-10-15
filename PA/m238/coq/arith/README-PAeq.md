# Classical arithmetic endpoint

> These notes describe an earlier development stage. See the
> [PA238 README](../../README.md) for the completed theorem and current build.

`PAeq238.v` uses the Coq Library of Undecidability's pinned arithmetic
signature and `PAeq` axiom predicate. `PA238.ordinary_PAeq` consists of the
universal closure (`close All`) of every upstream axiom. This closes all
induction parameters and retains full induction for every arithmetic formula.
Equality has its explicit reflexivity, symmetry, transitivity, and function
congruence axioms from `FAeq`.

`PA238.paeq_derivable phi` is `ordinary_PAeq ⊢TC phi`: classical natural
deduction from a finite list of closed PA axioms. There is no additional
hypothesis context. `PA238.PAeq_inconsistent` means derivability of `falsity`.

The source includes proof transformations for axiom instantiation,
substitution, generalization, full induction, and transport of finite upstream
proofs to the closed endpoint. `paeq_peirce` explicitly witnesses the classical
rule. `paeq_falsity_iff_old_contradiction` proves syntactic equivalence with
deriving `¬ (∀ ($0 == $0))`, the arithmetic image of the old contradiction
formula. This is an equivalence of finite derivations, not a model-consistency
argument. No machine-to-arithmetic correspondence is asserted here.

From `PA/m238`, run `python3 check_paeq.py --source-only` for hash, dependency,
and unfinished-proof checks. This helper is strictly source-only and does not
launch a compiler. Use the common `PA/m238/check.py` after integration for native
Coq 8.20 checking and eleven closed `Print Assumptions` reports. Native builds
must follow that common checker's bounded execution and existing lock protocol.

Validation: independent source review passed. The root's serialized, bounded
Coq 8.20.1 run compiled `PAeq238.v` and `CheckPAeq238.v` successfully, with all
eleven assumption reports closed under the global context. Static checks also
pass, including the integrated vendor inventory of 39 sources covering this
endpoint's 37-file closure. The complete project build and the arithmetic
interpretation bridges remain separate unfinished obligations.
