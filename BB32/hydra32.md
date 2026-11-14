# hydra32: a 32-state hydra machine above f_{ω↑↑4}(8)

```
1RC1LT_---0LZ_0RD1RU_0RE0RW_0RF0RF_0RG1RS_0RH1RF_0RI1RI_0LJ1RH_1LK1L[_0RL1LO_1RM1RL_0RN1RV_1LJ1RM_0LP1LP_0LQ1LO_0LR1LA_1RD1LQ_0LZ1RF_0LA1LA_1RH0RM_0RM1RM_0RX1RY_1LO1RW_0RW1RW_1L[0LB_0L_1L\_0RD1L]_0LJ1L^_0L[1L__0RP1L`_0L]1LJ
```

Found by **Argon** (a Google Gemini model run by the repository owner) on 2026-11-09, by adding one state to the
hydra machines of **mxdys** ([`../BB31/hydra31.md`](../BB31/hydra31.md)); Argon also wrote the Coq proof.
It was re-checked and packaged here on 2026-11-13.

States after Z are the next ASCII characters (`[` `\` `]` `^` `_` `` ` ``). **`Z` is an ordinary
state** (the 26th), not a halt: the only halting transition is B0 = `---`. `_` is also a state, so the string is
read in fixed-width rows of 6 characters (row i = characters 7i..7i+5). In Coq, state character c is the
constructor q + its spreadsheet-column name.

| state | Coq | 0 | 1 |
|---|---|---|---|
| `A` | `qA` | `1RC` | `1LT` |
| `B` | `qB` | `---` | `0LZ` |
| `C` | `qC` | `0RD` | `1RU` |
| `D` | `qD` | `0RE` | `0RW` |
| `E` | `qE` | `0RF` | `0RF` |
| `F` | `qF` | `0RG` | `1RS` |
| `G` | `qG` | `0RH` | `1RF` |
| `H` | `qH` | `0RI` | `1RI` |
| `I` | `qI` | `0LJ` | `1RH` |
| `J` | `qJ` | `1LK` | `1L[` |
| `K` | `qK` | `0RL` | `1LO` |
| `L` | `qL` | `1RM` | `1RL` |
| `M` | `qM` | `0RN` | `1RV` |
| `N` | `qN` | `1LJ` | `1RM` |
| `O` | `qO` | `0LP` | `1LP` |
| `P` | `qP` | `0LQ` | `1LO` |
| `Q` | `qQ` | `0LR` | `1LA` |
| `R` | `qR` | `1RD` | `1LQ` |
| `S` | `qS` | `0LZ` | `1RF` |
| `T` | `qT` | `0LA` | `1LA` |
| `U` | `qU` | `1RH` | `0RM` |
| `V` | `qV` | `0RM` | `1RM` |
| `W` | `qW` | `0RX` | `1RY` |
| `X` | `qX` | `1LO` | `1RW` |
| `Y` | `qY` | `0RW` | `1RW` |
| `Z` | `qZ` | `1L[` | `0LB` |
| `[` | `qAA` | `0L_` | `1L\` |
| `\` | `qAB` | `0RD` | `1L]` |
| `]` | `qAC` | `0LJ` | `1L^` |
| `^` | `qAD` | `0L[` | `1L_` |
| `_` | `qAE` | `0RP` | `` 1L` `` |
| `` ` `` | `qAF` | `0L]` | `1LJ` |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB32_halt.halt`. |
| Level | Machine-checked, with the standard fast-growing hierarchy of `Ord.v`: f_{ω^ω^(ω^8·3)}(4) ≤ N + 2 (`hardy_score`), hence f_{ω↑↑4}(8) < N (`sigma_lower_bound_w4_8`). N is the number of ones at the halt; the halt is B reading 0 (B0 = `---`), so σ = N, or N + 1 if the halting transition is taken to write a 1. |
| Exact score | Not computed (no closed form). |
| Steps | Not computed. |
| Compared with BB(31) | Machine-checked: above the exact score of hydra31 (the BB(31) entry) by at least 6, against an upper bound proved on hydra31's published files (`BB31_upper.upper_bound`, `BB32_beats_BB31`), so above BB(31) + 1. |

## How it works

hydra32 plays the hydra game of mxdys's hydra31 (see [`../BB29/hydra29.md`](../BB29/hydra29.md), section 1, for the
game and the pair encoding of hydras on the tape), with height limit **5**. Its game, scan and round lemmas are
the published BB31 files `BB31_game.v`, `BB31_scan.v`, `BB31_round.v` up to comments and names (Argon generated
them from the same templates); the transition table and the atomic pair rules (`BB32_tm.v`, `BB32_rules.v`)
are specific to this machine.

**Relation to hydra31** (checked here by propagating a state bijection from the halting state B along all
transitions). Up to a renaming of states, hydra32 is hydra31 with one transition
changed and one state added: hydra31's `_0` = `1LH` becomes K0 = `0RL`, into the new state L
(L0 = `1RM`, L1 = `1RL`), and the machine starts in the state that corresponds to hydra31's D
instead of its A. Argon calls the new state a blank-tape pump: the changed opening builds a much larger first hydra
before the game starts. After 4,501 steps
(`init` in `BB32_halt.v`, checked by literal execution in chunks of 250 steps) the machine is in the game
configuration C(1): counter m = 1 and a hydra of height 5, of ordinal **ω^ω^ω^(ω^8·3)** (`x0_eq`:
`olist hs0 = powtower 3 (orep (ofin 8) 3 oz)`).

## Proof

Halting and the bound come from one well-founded argument, exactly as for hydra31 and hydra33: the game is an
instance of the generic Hardy-hierarchy lemma `Hardy.hardy_game` (well-founded induction on the ordinals below
ε₀). Each round takes α = o(hydra) to α − 1 or into [α[m+3], α), with m → m + 1, and the empty hydra halts with
m + 1 ones. From C(1) this gives N + 2 ≥ H_{ω^ω^ω^(ω^8·3)}(4) (`hardy_bound`). H_{ω^β} = f_β with β = a32 = ω^ω^(ω^8·3) gives `hardy_score`; descending a32 at argument 4 (`HydraOrd.desc_between`, `desc_fs_succ`) to (ω^ω^ω^8) + 1 gives f_{ω^ω^ω^8}(8) + 8 ≤ f_{a32}(4), and (ω↑↑4)[8] = ω^ω^ω^8 gives f_{ω↑↑4}(8) < N (`sigma_lower_bound_w4_8`); `sigma_lower_bound_w4` and `sigma_lower_bound` are the weaker f_{ω↑↑4}(4) < N and f_{ω↑↑4}(3) < N.

## Comparison with BB(31)

hydra31 is the BB(31) entry. Its published proof gives the lower bound f_{ω^ω^ω^ω}(4) ≤ N + 2. An **upper** bound for its
score is proved in [`verify_vs31/`](verify_vs31/) (`BB31_upper.upper_bound`): for every halting configuration
reachable from the blank tape, N + 2 ≤ f_{ω^ω^ω^4}(6) (Coq: `FGH (powtower 3 (ofin 4)) 6`). The proof (`HydraUpper.v`) shows that on the
hydras these machines visit, a chop moves the hydra ordinal x exactly to x[n] or x[n+1] (`chop_exact`), and that
H_x(n+2) never increases along a round. With f_{ω^ω^ω^4}(6) + 6 ≤ f_{ω^ω^(ω^8·3)}(4) (`cmp_31_32`), `BB32_beats_BB31` proves that hydra32 halts with N
ones where N ≥ N(hydra31) + 6 for any number N(hydra31) of ones with which hydra31 halts. Both machines halt on
B0 = `---`, so the convention for σ is the same, and hydra32 is above BB(31) + 1 in Coq. The machine files in
`verify_vs31/multifile` are byte-identical copies of `verify/multifile` and of the published hydra31 files
(`share_check.sh`).

## Verification

[`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1, built in CI (job `bb13-bb14`). `probe.v` checks the
transition table against the string above entry by entry (generated from the string, fixed-width rows) and
confirms that `halt`, `hardy_bound`, `x0_eq`, `hardy_score`, `sigma_lower_bound_w4_8`, `sigma_lower_bound_w4`, `sigma_lower_bound` are closed under the global context. The proof files are Argon's, unchanged except for
line endings; `Ord.v`, `Hardy.v` and `HydraOrd.v` are byte-identical to BB31's. A from-scratch build here took
1,948 s (starved at Idle priority; about 8 min of compile time) at low priority (re-checked by argon-scout-2; then rebuilt from the repository layout).

## Credit

Machine and Coq proof: **Argon** (Google Gemini, run by the repository owner in Google's Antigravity), 2026-11-09,
built on **mxdys**'s hydra machines (BB29, BB31, BB33; mxdys posted them in the bbchallenge Discord, 2026-10-26).
Re-check, probe and packaging: this project, 2026-11-13.
