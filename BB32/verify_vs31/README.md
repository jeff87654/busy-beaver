# hydra32 against hydra31, in Coq

`multifile/` loads the published files of both machines and proves that hydra32 beats the exact score of hydra31
(the BB(31) entry). Logical root `BB8`, busycoq `bd2e36f`, Coq 8.20.1.

- `HydraUpper.v` (machine-independent; uses only `Ord.v`, `Hardy.v`, `HydraOrd.v`): on the hydras of this family a
  chop moves the ordinal x to exactly x[n] or x[n+1] (`chop_exact`), and U(x, n) = H_x(n+2) never increases along a
  round (`HH_up_lim`), so a run from (x, n) halts with N + 2 ≤ H_x(n+2).
- `BB31_upper.v`: for the published hydra31, `upper_bound : forall c N, c0 -->* c -> halted tm c -> ones c N -> N + 2 <= FGH (powtower 3 (ofin 4)) 6`,
  i.e. N + 2 ≤ f_{ω^ω^ω^4}(6) for every halting configuration reached from the blank tape; `halts_with_upper`, and
  `score_window` (the published lower bound and this upper bound together).
- `BB32_vs_BB31.v`: `cmp_31_32` (f_{ω^ω^ω^4}(6) + 6 ≤ f_{ω^ω^(ω^8·3)}(4)) and `BB32_beats_BB31` (hydra32 halts with N ones such that N(hydra31) + 6 ≤ N
  for every N(hydra31) with which hydra31 halts).

The files `BB312.v`, `Individual312.v`, `BB31_tm.v`, … `BB31_halt.v` are byte-identical copies of
[`../../BB31/verify/multifile/`](../../BB31/verify/multifile/), and `BB322.v`, … `BB32_bound.v` of
[`../verify/multifile/`](../verify/multifile/); `Ord.v`, `Hardy.v`, `HydraOrd.v` are the shared library. `share_check.sh`
checks all of them byte for byte and runs first in `compile_clean.sh`.

Upper bounds and comparison: written by this project (agent claims-prover), 2026-11-13; packaged and rebuilt from
the repository's files here.

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`probe.v` prints the statements and runs `Print Assumptions` on `HydraUpper.chop_exact`, `BB31_upper.upper_bound`,
`halts_with_upper`, `score_window`, `cmp_31_32` and `BB32_beats_BB31`: all closed under the global context. CI job
`bb13-bb14`.
