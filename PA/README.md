# PA/: Peano arithmetic

Two machines, for two different statements: one halts iff PA is inconsistent, the other halts iff PA proves
Goldbach's conjecture.

## Consistency of PA: a 238-state machine

[`m238/machine/pa_238.tm`](m238/machine/pa_238.tm) is a 238-state, 2-symbol Turing machine that halts from the blank
tape if and only if ordinary classical Peano arithmetic has a finite refutation:

```coq
blank_halts238 <-> PA238.PAeq_inconsistent        (* P238.e2e.Targets238.pa238_iff_ordinary_proved *)
```

- [`m238/`](m238/README.md): the exact table, the proof sources, vendored dependencies, provenance and Coq 8.20.1
  reproduction instructions. CI job `pa238` (`python3 -I PA/m238/check.py`) rebuilds the dependency closure and
  checks every declared assumption probe.

Contributed by mira-emmy (pull request #18, 2026-10-15). The machine comes from the `mm0-bb` repository (pin and
provenance in [`m238/README.md`](m238/README.md#provenance-and-licenses)).

## PA ⊢ Goldbach: a 449-state machine

[`goldbach/machine/pa_wade.tm`](goldbach/machine/pa_wade.tm) is a 449-state, 2-symbol Turing machine that halts from
the blank tape if and only if PA (the library's `PAeq`) proves Goldbach's conjecture:

```coq
Theorem pagb_halts_iff_PA_GC :
  PAGBT.ZFTM.ZFTM.halts PAGBT.ZFTM.tm PAGBT.ZFTM.ZFTM.c0 <-> @tprv _ _ falsity_on class PAeq GC_form.
Theorem GC_adequate rho : sat interp_nat rho GC_form <-> Goldbach_nat.
```

Both are closed under the global context. Equivalently, it halts iff PA + ¬GC is inconsistent, so it also halts
if PA is inconsistent.

- [`goldbach/`](goldbach/README.md): the table (sha256 `ed795af7…f2616a6`), the Coq proof in four layers, the
  vendored library subset, what has to be trusted, and the design. CI job `pa-goldbach`
  (`python3 check.py` in `PA/goldbach`, about 25 minutes) rebuilds everything from source, re-checks the table and
  its TMBuilder rebuild, and runs coqchk.

This project's work, on Mira-Cult's 254-state program design (new axiom rows and gate) and Andrew Wade's compiler.

No superseded entries in this directory.
