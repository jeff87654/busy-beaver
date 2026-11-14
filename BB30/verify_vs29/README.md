# hydra30 against hydra29, in Coq

`multifile/` loads the published files of both machines and proves that hydra30 beats the exact score of hydra29 (the
BB(29) entry). Logical root `BB8`, busycoq `bd2e36f`, Coq 8.20.1.

- `BB29_upper.v`: for the published hydra29 (whose own proof gives N = T₄(S)(1) + 1, `score_exact`):
  `halts_with_exact : forall NB, halts_with NB -> NB = T 4 S 1 + 1` (every halting run from the blank tape),
  `T4_upper : T 4 S 1 <= FGH (orep (ofin 3) 7 oz) 26` (T₄(S)(1) ≤ f_{ω^3·7}(26)), `T4_lt_w9 : T 4 S 1 + 25 <= FGH (opow (ofin 9)) 10`
  and `halts_with_upper`.
- `BB30_vs_BB29.v`: `BB30_beats_BB29` (hydra30 halts with N ones such that N(hydra29) + 22 ≤ N for every N(hydra29)
  with which hydra29 halts), from hydra30's `hardy_score`.

The files `BB292.v`, `Individual292.v`, `BB29_tm.v`, … `BB29_bound.v`, `Ufun.v` are byte-identical copies of
[`../../BB29/verify/multifile/`](../../BB29/verify/multifile/), and `BB302.v`, … `BB30_bound.v`, `Hardy.v`, `HydraOrd.v` of
[`../verify/multifile/`](../verify/multifile/); `Ord.v` is the same in both. `share_check.sh` checks all of them byte for byte and
runs first in `compile_clean.sh`.

Upper bound and comparison: written by this project (agent claims-prover), 2026-11-13; packaged and rebuilt from the
repository's files here.

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`probe.v` prints the statements and runs `Print Assumptions` on `T4_upper`, `T4_lt_w9`, `halts_with_exact`,
`halts_with_upper` and `BB30_beats_BB29`: all closed under the global context. CI job `bb13-bb14`.
