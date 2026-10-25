# A verified 449-state Turing machine that halts iff PA proves Goldbach's conjecture

[`machine/pa_wade.tm`](machine/pa_wade.tm) is a 449-state, 2-symbol Turing machine. Started on a blank tape, it
halts **if and only if Peano arithmetic proves Goldbach's conjecture**. This is proved in Coq 8.20, end to end,
and the headline theorems use no axioms:

```
sha256 ed795af79b6752d72c037d7e32eca1d23efaa6a6c0f0d07fc7ba89869f2616a6  machine/pa_wade.tm
```

(LF line endings; 449 states plus `halt`, 897 transitions, start state `0.boot.A`.)

```coq
(* e2e/Headline.v *)
Theorem pagb_halts_iff_PA_GC :
  PAGBT.ZFTM.ZFTM.halts PAGBT.ZFTM.tm PAGBT.ZFTM.ZFTM.c0 <-> @tprv _ _ falsity_on class PAeq GC_form.
Theorem GC_adequate rho : sat interp_nat rho GC_form <-> Goldbach_nat.
(* Print Assumptions: Closed under the global context (both) *)
```

`GC_form` and `Goldbach_nat` are written out in [`e2e/Headline.v`](e2e/Headline.v) (de Bruijn indices: `$0` is
the innermost bound variable):

```coq
Definition leq (s t : term) : form := ∃ (t`[↑] == s`[↑] ⊕ $0).            (* s ≤ t :  ∃z. t = s + z *)
Definition even (t : term) : form := ∃ (t`[↑] == $0 ⊕ $0).               (* ∃k. t = k + k *)
Definition Pr (t : term) : form :=                                        (* t is prime *)
  leq (num 2) t ∧ (∀ ∀ ((t`[↑]`[↑] == $1 ⊗ $0) → (($1 == num 1) ∨ ($0 == num 1)))).
(* ∀n. (n even ∧ 4 ≤ n) → ∃p ∃q. (Pr p ∧ Pr q) ∧ p + q = n   (under ∃p∃q: q = $0, p = $1, n = $2) *)
Definition GC_form : form :=
  ∀ ((even $0 ∧ leq (num 4) $0) → ∃ ∃ ((Pr $1 ∧ Pr $0) ∧ ($1 ⊕ $0 == $2))).

Definition prime_nat (p : nat) : Prop := 2 <= p /\ forall d, Nat.divide d p -> d = 1 \/ d = p.
Definition Goldbach_nat : Prop :=
  forall n, Nat.Even n -> 4 <= n -> exists p q, prime_nat p /\ prime_nat q /\ p + q = n.
```

`GC_adequate` says that `GC_form` means Goldbach's conjecture in the standard model, so the first theorem is about
the conjecture itself and not about some other sentence.

**This is a different statement from [`../m238/`](../m238/)**, whose machine halts iff PA is inconsistent. This
machine halts iff PA + ¬GC is inconsistent (`Spec.PA_GC_refutation`). If PA is inconsistent, PA proves GC and this
machine halts too. It is also not a counterexample search, which would halt iff Goldbach's conjecture is false.

## What has to be trusted

- `halts`, `c0`: busycoq's TM semantics ([`TM.v`](../../ZF/stdzf_r3/vendor/busycoq/TM.v); blank tape, start state
  `0.boot.A`). The functor `TM` is instantiated as `PAGBT.ZFTM.ZFTM`, with 2 symbols and the machine's 450 states
  (449 plus `halt`).
- `tm`: the machine as a busycoq `TM` (`tm/coq/ZFTM.v`). The theorem `ZFTM.tm_table`, also closed, proves that it
  agrees row by row with the literal table `pa_table` of `tm/coq/TablePA.v`. [`tm/check_tm.py`](tm/check_tm.py)
  parses `machine/pa_wade.tm` independently, checks its sha256 and requires `pa_table` to be exactly its table.
- `PAeq`, `tprv` (written `⊢TC`), `sat`, `interp_nat`: the Coq Library of Undecidability Proofs (Kirst, Hermes et
  al.), vendored unmodified in [`vendor/undecidability/`](vendor/undecidability/). `PAeq` is first-order PA over
  `zero`, `σ`, `⊕`, `⊗` and `==`: the defining equations of + and ×, `0 ≠ S x`, injectivity of S, the equality
  axioms and every instance of the induction schema (`FOL/Arithmetics/PA.v`). `tprv` is classical natural
  deduction from finitely many axioms of the theory (`FOL/Deduction/FullND.v`). `sat` is Tarski semantics and
  `interp_nat` the standard model of arithmetic.
- `GC_form`, `Goldbach_nat` (and `leq`, `even`, `Pr`, `prime_nat`), as quoted above. A reader has to check that
  they say what Goldbach's conjecture says.
- The table hash above, and the Coq kernel.

Everything else is internal to the proof: the register machine, the proof enumerator, the machine's own calculus
and the translations between calculi.

## Checking it

```
cd PA/goldbach
python3 check.py          # coqc / coqchk from $COQC / $COQCHK, default `coqc` / `coqchk` on PATH (Coq 8.20.x)
```

It takes about 25 minutes (one coqc at a time, at low priority). It rebuilds everything from source: the 41
library files, the 3 busycoq files and the 42 files of the proof. [`check.py`](check.py):

1. checks the sha256 of the 15 files of the freeze set in `machine/` (the table, its source, the reference
   enumerator `spec_pa.py` and its imports);
2. checks that Andrew Wade's TMBuilder ([`../../ZF/generator/`](../../ZF/generator/), unmodified) compiles
   [`machine/source_pa.py`](machine/source_pa.py) to `pa_wade.tm` ([`machine/build_tm.py`](machine/build_tm.py);
   byte for byte up to line terminators);
3. runs [`coq/check.py`](coq/check.py): no `Admitted`/`admit`/`Axiom`/`Parameter`/`Conjecture` outside comments,
   clean rebuild of the vendored library subset and of `coq/`, the expected statements, every `Print Assumptions`
   closed;
4. runs [`tm/check_tm.py`](tm/check_tm.py): the literal table is `pa_wade.tm`, `tm/tools/gen_coq.py` regenerates
   `DagPA.v`, `TablePA.v`, `NamesPA.v` byte for byte, clean rebuild, `tmpa_rm` and `tm_table` have the expected
   statements and are closed;
5. runs [`prog/check.py`](prog/check.py): the TM layer's `DagPA.v` is the DAG regenerated from the machine, the
   generated regions of `ProgLibPA.v` reproduce, clean rebuild, all assumptions closed;
6. compiles `e2e/Headline.v` (under 100 lines), requires the statements above in its source and both
   `Print Assumptions` closed;
7. runs `coqchk` (an independent kernel re-check) on `PAGBE.Headline` and every library it loads;
8. prints `CHECK PASS` or `CHECK FAIL`.

CI job: `pa-goldbach`.

**Axioms.** `Print Assumptions`, which tracks exactly what a theorem depends on, reports both headline theorems
"Closed under the global context". `coqchk` re-checks the whole environment in the kernel and lists every axiom
declared anywhere in a loaded library. Here that is three: `BusyCoq.LibTactics.inj_pair2`,
`Coq.Logic.ProofIrrelevance.proof_irrelevance` and `Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq`. They come in through
busycoq's `TM.v` imports, which are left unmodified, and the headline theorems use none of them. `check.py` accepts
exactly these three in the coqchk output and fails on any other.

## Proof structure

| Directory | Layer | Main theorem |
|---|---|---|
| [`machine/`](machine/) | the frozen machine (`pa_wade.tm`, `source_pa.py`, `spec_pa.py`; design in [`DESIGN.md`](machine/DESIGN.md)) | — |
| [`tm/`](tm/) | TM ↔ register-machine DAG (certified list-zipper simulation) | `MainTM.tmpa_rm : halts tm c0 <-> rm_halts dagpa ([], regs0)` |
| [`prog/`](prog/) | register-machine DAG ↔ abstract enumerator (structured semantics, occurs-check walk) | `MainPA.progpa : rm_halts dagpa ([], regs0) <-> enum_halts` |
| [`coq/`](coq/) | enumerator ↔ code calculus ↔ named Hilbert calculus ↔ library `PAeq`; `Spec` | `PA_Logic.enum_halts_iff_PA_GC : enum_halts <-> PA_proves_GC` |
| [`e2e/`](e2e/) | composition, under 100 lines | `Headline.pagb_halts_iff_PA_GC` |

The logic layer ([`coq/README.md`](coq/README.md)) has two directions. Soundness (`pprov` → `PAeq`): named
variables to de Bruijn indices, validity of every rule, and parametric induction instances derived from one
parameter-free library instance. Completeness (`PAeq` → `pprov`): library natural deduction is translated into the
named Hilbert calculus `pprov` (`PALogic.v`), and every `PAeq` axiom is derived there. Then each `pprov` rule is
matched with a machine root, and the enumerator's halting is shown equivalent to `pprov (eq NGw) Fw`.

## Design

The machine is a proof enumerator. Its theorems are those of PA plus one extra axiom NG = ¬GC, and it halts when it
derives falsity. So it halts iff PA ⊢ GC. Details are in [`machine/DESIGN.md`](machine/DESIGN.md).

- **Native PA.** The calculus works over 0, S, +, × and = with functional terms. Formula and term codes are
  `4·P(x,y) + tag` with dual Cantor pairing; equality is the only predicate.
- **General vacuity behind an occurs check.** One gated root gives `t = s → ∀z t = s` (Tarski–Megill B6a) for
  all terms t, s and every variable z with z ∉ vars t ∪ vars s. The gate walks the term codes of t and s and opens
  exactly when z does not occur. No vacuity lemmas are derived, and no variables are pinned.
- **The literal Goldbach axiom.** The NG row is the code of `NGw = ¬ tr(GC_form)`, where `tr` is the Coq
  translation of the library formula. The row was parsed from coqc's output (`machine/runs/GCw_coq_print.txt`,
  `machine/ngw.py`), not written by hand.
- **The six Q axioms** (0 ≠ Sx, Sx = Sy → x = y, 0 + x = x, Sx + y = S(x + y), 0 · x = 0, Sx · y = y + x · y,
  in the library's order of arguments) are open rows with free labels.
  Each reaches the literal instance over v0, v1 through its parameters.
- **Substitution-free induction.** `∀x(x=0 → φ) → (∀x(φ → ∀c(c = Sx → ∀x(x = c → φ))) → ∀x φ)`, with c fresh
  for φ by the coding. Substitution is never computed.
- **Route.** The program is Mira-Cult's 254-state ZFC program (see [`../../ZF/m254/`](../../ZF/m254/)) with
  `axioms()` replaced and the freshness gate replaced by the occurs check. Its RM helpers, MP/DROP/NIP, dispatch,
  coding, GEN and self-freshness are unchanged. It is compiled by Wade's TMBuilder, which turns the unchanged
  254-state program into 281 states. The PA program needs 449.

## Files

- `machine/`: the freeze set (`pa_wade.tm`, `source_pa.py`, `spec_pa.py`, `design_choice_A.json`, the spec's imports
  `bignum.py`, `design.py`, `ngw.py`, `pagen.py`, `pavars.py`, `search_a.py`, `search_nest.py`, `search_pa.py`,
  and `runs/GCw_coq_print.txt`, `runs/decode_final.txt`, `runs/push_order.txt`), `build_tm.py` and `DESIGN.md`.
  Five of the frozen Python files have CRLF line endings; their hashes are of the bytes as frozen, and
  `.gitattributes` keeps `machine/` unconverted. The validation and search tools of the development tree are not
  included (see the note at the top of `DESIGN.md`).
- `tools/`: `dag.py` (DAG extraction from a `.tm` file) and `tmsim.py`, copies of [`../../ZF/tools/`](../../ZF/tools/).
- `vendor/undecidability/`: the library subset (41 files, commit `70dfc56`, MPL-2.0).
- busycoq: `TM.v`, `Helper.v`, `LibTactics.v` (commit `bd2e36f`, MIT; LibTactics under its own license) are used
  from [`../../ZF/stdzf_r3/vendor/busycoq/`](../../ZF/stdzf_r3/vendor/busycoq/), as by `PA/m238` and `ZF/tg296`.
  They are the files the proof was developed against (identical up to line endings).
- Comments in the Coq sources use development-tree paths: `zf/pagb/...` is this directory, `zf/m254`, `zf/stdzf`
  and `zf/m254tg` are [`ZF/m254`](../../ZF/m254/), [`ZF/stdzf`](../../ZF/stdzf/) and [`ZF/tg296`](../../ZF/tg296/),
  and `third_party/busycoq/verify` is the busycoq copy above. The sources are otherwise as checked (line endings
  normalized to LF).

## Credits

- The program design is **Mira-Cult's** (mike29936; [github.com/Mira-Cult/turing-machines](https://github.com/Mira-Cult/turing-machines)):
  the 254-state ZFC proof enumerator. Its formula coding, MP/DROP/NIP, GEN, dispatch and freshness discipline are
  used here unchanged. Only the axiom rows and the gate are new.
- The compiler is **Andrew Wade's** TMBuilder ([codeberg.org/ajwade/turing_machine_explorer](https://codeberg.org/ajwade/turing_machine_explorer)),
  vendored in [`../../ZF/generator/`](../../ZF/generator/).
- `PAeq`, natural deduction and the standard model come from the **Coq Library of Undecidability Proofs**
  ([uds-psl/coq-library-undecidability](https://github.com/uds-psl/coq-library-undecidability)).
- The TM semantics is **busycoq**'s ([meithecatte/busycoq](https://github.com/meithecatte/busycoq)).
- The PA program, the machine and the Coq proof are this project's: the repository owner's work with Claude models
  (Anthropic) as agents. The TM-layer simulation and the program-layer method are ported from
  [`../../ZF/tg296/`](../../ZF/tg296/) and [`../../ZF/m254/`](../../ZF/m254/).
