# hydra34 against hydra33, in Coq

`multifile/` loads the published files of both machines and proves that hydra34 beats the exact score of hydra33
(the BB(33) entry). Logical root `BB8`, busycoq `bd2e36f`, Coq 8.20.1.

- `HydraUpper.v` (machine-independent; uses only `Ord.v`, `Hardy.v`, `HydraOrd.v`): on the hydras of this family a
  chop moves the ordinal x to exactly x[n] or x[n+1] (`chop_exact`), and U(x, n) = H_x(n+2) never increases along a
  round (`HH_up_lim`), so a run from (x, n) halts with N + 2 ≤ H_x(n+2).
- `BB33_upper.v`: for the published hydra33, `upper_bound : forall c N, c0 -->* c -> halted tm c -> ones c N -> N + 2 <= FGH (powtower 5 (ofin 3)) 6`,
  i.e. N + 2 ≤ f_{ω^ω^ω^ω^ω^3}(6) for every halting configuration reached from the blank tape; `halts_with_upper`, and
  `score_window` (the published lower bound and this upper bound together).
- `BB34_vs_BB33.v`: `cmp_33_34` (f_{ω^ω^ω^ω^ω^3}(6) + 3 ≤ f_{ω^ω^ω^ω^ω^4}(5)) and `BB34_beats_BB33` (hydra34 halts with N ones such that N(hydra33) + 3 ≤ N
  for every N(hydra33) with which hydra33 halts).

The files `BB332.v`, `Individual332.v`, `BB33_tm.v`, … `BB33_halt.v` are byte-identical copies of
[`../../BB33/verify/multifile/`](../../BB33/verify/multifile/), and `BB342.v`, … `BB34_bound.v` of
[`../verify/multifile/`](../verify/multifile/); `Ord.v`, `Hardy.v`, `HydraOrd.v` are the shared library. `share_check.sh`
checks all of them byte for byte and runs first in `compile_clean.sh`.

Upper bounds and comparison: written by this project (agent claims-prover), 2026-11-13; packaged and rebuilt from
the repository's files here.

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`probe.v` prints the statements and runs `Print Assumptions` on `HydraUpper.chop_exact`, `BB33_upper.upper_bound`,
`halts_with_upper`, `score_window`, `cmp_33_34` and `BB34_beats_BB33`: all closed under the global context. CI job
`bb13-bb14`.
