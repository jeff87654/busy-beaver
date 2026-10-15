# PA238: halting and finite PA refutations

This directory proves that the literal [238-state binary machine](machine/pa_238.tm) halts from blank tape iff ordinary classical Peano arithmetic has a finite refutation:

```coq
blank_halts238 <-> PA238.PAeq_inconsistent
```

The theorem is `P238.e2e.Targets238.pa238_iff_ordinary_proved` in [Targets238.v](coq/e2e/Targets238.v). `PA238.PAeq_inconsistent` means classical natural deduction (`TC`, including Peirce) from a finite list of universally closed upstream `PAeq` axioms. Full induction retains arbitrary parameters; see [PAeq238.v](coq/arith/PAeq238.v).

Both directions transport actual finite proofs and executions through the compact calculus, numeric proof commands, candidate enumerator, register program, and literal TM. The exported theorem has no extra model, comprehension, compiler, or simulation premise. Gödel's second incompleteness theorem is cited as standard background in `Targets238.v`.

The blank symbol is `false`, the initial state is 0, working states are 0–237, and halt state is 238. The 476-transition input has SHA256:

```text
ffe370842d70bae96688ad5e290073edffe0bb213cf12fe562a75a74bec966de
```

## Checking

Use Coq 8.20.1 with its matching standard library and Python 3 on a Unix host with `fcntl` and `/bin/ps`. From the repository root, provision absent lock files without changing existing ones, then build:

```sh
python3 - <<'PY'
from pathlib import Path
for name in ('/tmp/mm0-native-mac.lock', '/tmp/mm0_compile.lock'):
    try:
        Path(name).open('xb').close()
    except FileExistsError:
        pass
PY
python3 -I PA/m238/check.py --coqc coqc --wall-seconds 120 --memory-mib 2048
```

The driver acquires those locks in order, rebuilds all 150 PA modules and their 192-source dependency closure, validates the table and vendor manifest, and checks every assumption probe. Each compiler process is limited to 120 seconds and 2048 MiB RSS. A matching optional Nix toolchain is pinned by `6510408d147d8c5e6d76043e899e9251756f6a75#coq_8_20`.

Local checking and full recursive `coqchk` passed. The final endpoint audit reported 383 results closed under the global context. Imported upstream libraries contain unused axioms; the final theorem and these probed results do not depend on them.

Source checks, without kernel compilation:

```sh
python3 -I PA/m238/check.py --source-only
python3 -I PA/m238/tools/gen_table.py --check
```

The build consumes committed Coq certificates and needs no MM0 executable or external generator inputs.

## Provenance and licenses

The machine/source pin is `6f7f0c2f97703839e56a705bbf5da5a0e5c132cf` in the original `mm0-bb` repository; the PA source SHA256 is `b489f6f59dfd6af070db18897ca76b275a931f9958941bceb697c6dd3f4d751a`. Generic proof infrastructure is adapted from Jeffrey's [`ZF/m254`](../../ZF/m254/) development at `c132d7eae8158cd3a9850ea3eb7251158c3dd821`, with attribution retained in the adapted files.

The [Coq Library of Undecidability](vendor/undecidability/README.md) is pinned to `70dfc56f33a6e4835281044e68aa68279989047e` and retains its MPL-2.0 license and source manifest. [BusyCoq](../../ZF/stdzf_r3/vendor/busycoq/README.md) is pinned to `bd2e36f6aa204eb011742d2ca6c8741102b2e59e`; its MIT and MIT-X11 notices remain in that directory. Existing authorship and license notices are preserved; this directory adds no new license grant.
