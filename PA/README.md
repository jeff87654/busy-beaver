# PA/: consistency of Peano arithmetic

## Current entry: a 238-state machine

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

No superseded entries in this directory.
