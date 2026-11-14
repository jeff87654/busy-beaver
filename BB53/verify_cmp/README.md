# 53-Main's comparisons, in Coq

Two files written here (busycoq `bd2e36f`, Coq 8.20.1), on top of [`../verify/`](../verify/) (Argon's development,
logical root `Local`):

- `BB53_vs_BB43.v` also loads the BB(4,3) entry's development [`../../BB43/verify/`](../../BB43/verify/) (logical
  root `TM43`): `knuth_same` (the two Knuth-arrow definitions agree) and
  `BB53_beats_BB43 : TM43.BB43_run.sigma + 1 < Local.BB53_run.sigma`, from that entry's upper bound
  σ ≤ 4·P(P(P(2^96 + 6))) + 18 (`TM43.BB43_score.sigma_bounds`, P = 2 ↑↑↑ ·) and 53-Main's F(F(7)) < σ.
- `BB53_fgh.v` loads `Ord.v` (a byte-identical copy of [`../../BB31/verify/multifile/Ord.v`](../../BB31/verify/multifile/Ord.v),
  logical root `BB8` here; `share_check.sh`): `fin_fgh_le_knuth` (f_(k+1)(x) ≤ 2 ↑^k (3x) for k ≥ 1, x ≥ 4),
  `FGH_omega_le_home` (f_ω(n) ≤ 2 ↑^n n for n ≥ 4) and
  `sigma_exceeds_FGH : FGH omega (knuth 8 2 3) < sigma /\ FGH omega (FGH omega 7) < sigma`.

Both σ count the nonzero cells after the halting transition (BB(4,3): C0 = `1RZ`; 53-Main: E0 = `1RZ`).
Written by this project (agent claims-prover), 2026-11-13; packaged and rebuilt here.

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

It runs `share_check.sh`, builds `../verify` and `../../BB43/verify` if their `.vo` files are missing, compiles
`Ord.v`, `BB53_vs_BB43.v`, `BB53_fgh.v`, then `probe.v`, which prints the statements and runs `Print Assumptions` on
`knuth_same`, `BB53_beats_BB43`, `fin_fgh_le_knuth`, `FGH_omega_le_home`, `sigma_exceeds_FGH`: all closed under the
global context. CI job `bb53` (after `../verify`).
