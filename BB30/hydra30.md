# hydra30: a 30-state hydra machine above f_{ω^ω}(9)

```
1RC1L[_---0LY_0RD1RW_0RE0RN_0RF0RF_0RG1RX_0RH1RF_0RI1RI_0LJ1RH_1LK1LU_0LL1LP_1LM0RD_0RD1LT_0RO1RV_1LP1RN_0LQ1LQ_0LR1LP_0LS1LA_1RD1LR_0RQ1LZ_0LT1LM_0RN1RN_1RH0R\_0LY1RF_1LU0LB_0LU1LJ_0LA1LA_0R^1R]_0R\1R\_1LJ1R\
```

Found by **Argon** (a Google Gemini model run by the repository owner) on 2026-11-09, by adding one state to the
hydra machines of **mxdys** ([`../BB29/hydra29.md`](../BB29/hydra29.md)); Argon also wrote the Coq proof.
It was re-checked and packaged here on 2026-11-13.

States after Z are the next ASCII characters (`[` `\` `]` `^`). **`Z` is an ordinary
state** (the 26th), not a halt: the only halting transition is B0 = `---`. `_` is also a state, so the string is
read in fixed-width rows of 6 characters (row i = characters 7i..7i+5). In Coq, state character c is the
constructor q + its spreadsheet-column name.

| state | Coq | 0 | 1 |
|---|---|---|---|
| `A` | `qA` | `1RC` | `1L[` |
| `B` | `qB` | `---` | `0LY` |
| `C` | `qC` | `0RD` | `1RW` |
| `D` | `qD` | `0RE` | `0RN` |
| `E` | `qE` | `0RF` | `0RF` |
| `F` | `qF` | `0RG` | `1RX` |
| `G` | `qG` | `0RH` | `1RF` |
| `H` | `qH` | `0RI` | `1RI` |
| `I` | `qI` | `0LJ` | `1RH` |
| `J` | `qJ` | `1LK` | `1LU` |
| `K` | `qK` | `0LL` | `1LP` |
| `L` | `qL` | `1LM` | `0RD` |
| `M` | `qM` | `0RD` | `1LT` |
| `N` | `qN` | `0RO` | `1RV` |
| `O` | `qO` | `1LP` | `1RN` |
| `P` | `qP` | `0LQ` | `1LQ` |
| `Q` | `qQ` | `0LR` | `1LP` |
| `R` | `qR` | `0LS` | `1LA` |
| `S` | `qS` | `1RD` | `1LR` |
| `T` | `qT` | `0RQ` | `1LZ` |
| `U` | `qU` | `0LT` | `1LM` |
| `V` | `qV` | `0RN` | `1RN` |
| `W` | `qW` | `1RH` | `0R\` |
| `X` | `qX` | `0LY` | `1RF` |
| `Y` | `qY` | `1LU` | `0LB` |
| `Z` | `qZ` | `0LU` | `1LJ` |
| `[` | `qAA` | `0LA` | `1LA` |
| `\` | `qAB` | `0R^` | `1R]` |
| `]` | `qAC` | `0R\` | `1R\` |
| `^` | `qAD` | `1LJ` | `1R\` |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB30_halt.halt`. |
| Level | Machine-checked, with the standard fast-growing hierarchy of `Ord.v`: f_{ω^9}(10) ≤ N + 2 (`hardy_score`), hence f_{ω^ω}(9) < N (`sigma_lower_bound_w2_9`). N is the number of ones at the halt; the halt is B reading 0 (B0 = `---`), so σ = N, or N + 1 if the halting transition is taken to write a 1. |
| Exact score | Not computed (no closed form). |
| Steps | Not computed. |
| Compared with BB(29) | Machine-checked: above the exact score of hydra29 (the BB(29) entry) by at least 22, against an upper bound proved on hydra29's published files (`BB29_upper.T4_upper`, `halts_with_exact`, `BB30_beats_BB29`), so above BB(29) + 1. |

## How it works

hydra30 plays the hydra game of mxdys's hydra29 (see [`../BB29/hydra29.md`](../BB29/hydra29.md), section 1, for the
game and the pair encoding of hydras on the tape), with height limit **3**. Its game, scan and round lemmas are
the published BB31 files `BB31_game.v`, `BB31_scan.v`, `BB31_round.v` up to comments and names (Argon generated
them from the same templates); the transition table and the atomic pair rules (`BB30_tm.v`, `BB30_rules.v`)
are specific to this machine.

**Relation to hydra29** (checked here by propagating a state bijection from the halting state B along all
transitions). Up to a renaming of states, hydra30 is hydra29 with one transition
changed and one state added: hydra29's `]0` = `1LH` becomes K0 = `0LL`, into the new state L
(L0 = `1LM`, L1 = `0RD`), and the machine starts in the state that corresponds to hydra29's D
instead of its A. Argon calls the new state a blank-tape pump: the changed opening builds a much larger first hydra
before the game starts. After 2,590 steps
(`init` in `BB30_halt.v`, checked by literal execution in chunks of 250 steps) the machine is in the game
configuration C(7): counter m = 7 and root → X₁ → X₂ with nine leaves on X₂, of ordinal **ω^ω^9** (`x0_eq`:
`olist hs0 = powtower 2 (ofin 9)`).

## Proof

Halting and the bound come from one well-founded argument, exactly as for hydra31 and hydra33: the game is an
instance of the generic Hardy-hierarchy lemma `Hardy.hardy_game` (well-founded induction on the ordinals below
ε₀). Each round takes α = o(hydra) to α − 1 or into [α[m+3], α), with m → m + 1, and the empty hydra halts with
m + 1 ones. From C(7) this gives N + 2 ≥ H_{ω^ω^9}(10) (`hardy_bound`). H_{ω^β} = f_β with β = ω^9 gives `hardy_score`; f_{ω^9}(10) ≥ f_{ω^9}(9) + 9 and ω^ω[9] = ω^9 give f_{ω^ω}(9) < N (`sigma_lower_bound_w2_9`), and `sigma_lower_bound` is the weaker f_{ω^ω}(3) < N.

## Comparison with BB(29)

hydra29 is the BB(29) entry. Its published proof gives its exact count, N = T₄(S)(1) + 1 (`score_exact`), and the
lower bound f_{ω^ω}(3) < N. An **upper** bound is proved in [`verify_vs29/`](verify_vs29/) on the published hydra29
files: every halting run of hydra29 from the blank tape leaves exactly T₄(S)(1) + 1 ones (`halts_with_exact`), and
T₄(S)(1) ≤ f_{ω^3·7}(26) (`T4_upper`), so T₄(S)(1) + 25 ≤ f_{ω^9}(10) (`T4_lt_w9`). With hydra30's
f_{ω^9}(10) ≤ N + 2, `BB30_beats_BB29` proves that hydra30 halts with N ones where N ≥ N(hydra29) + 22. Both machines
halt on B0 = `---`, so the convention for σ is the same, and hydra30 is above BB(29) + 1 in Coq. The machine files in
`verify_vs29/multifile` are byte-identical copies of `verify/multifile` and of the published hydra29 files
(`share_check.sh`).

## Verification

[`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1, built in CI (job `bb13-bb14`). `probe.v` checks the
transition table against the string above entry by entry (generated from the string, fixed-width rows) and
confirms that `halt`, `hardy_bound`, `x0_eq`, `hardy_score`, `sigma_lower_bound_w2_9`, `sigma_lower_bound` are closed under the global context. The proof files are Argon's, unchanged except for
line endings; `Ord.v`, `Hardy.v` and `HydraOrd.v` are byte-identical to BB31's. A from-scratch build here took
455 s at low priority (re-checked by argon-scout-2; then rebuilt from the repository layout).

## Credit

Machine and Coq proof: **Argon** (Google Gemini, run by the repository owner in Google's Antigravity), 2026-11-09,
built on **mxdys**'s hydra machines (BB29, BB31, BB33; mxdys posted them in the bbchallenge Discord, 2026-10-26).
Re-check, probe and packaging: this project, 2026-11-13.
