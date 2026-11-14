# hydra34: a 34-state hydra machine above f_{ω↑↑6}(4)

```
1LC1LT_---0LS_1RD1LH_0RE0RC_0RF1RF_0RG1RE_1LA1RF_0LI1LI_0LJ1LH_0LK1LY_1RL1LJ_0RM0RV_0RN0RN_0RO1RR_0RP1RN_0RQ1RQ_0LA1RP_0LS1RN_1LT0LB_0La1LU_0RL1L\_0RX1RW_0RV1RV_1LH1RV_1RZ1L^_0RL1R[_1RP0RF_0LA1L]_0LT1L__0LY1LY_0LU1L`_0L\1La_0RI1Lb_0L_1LA
```

Found by **Argon** (a Google Gemini model run by the repository owner) on 2026-11-09, by adding one state to the
hydra machines of **mxdys** ([`../BB33/hydra33.md`](../BB33/hydra33.md)); Argon also wrote the Coq proof.
It was re-checked and packaged here on 2026-11-13.

States after Z are the next ASCII characters (`[` `\` `]` `^` `_` `` ` `` `a` `b`). **`Z` is an ordinary
state** (the 26th), not a halt: the only halting transition is B0 = `---`. `_` is also a state, so the string is
read in fixed-width rows of 6 characters (row i = characters 7i..7i+5). In Coq, state character c is the
constructor q + its spreadsheet-column name.

| state | Coq | 0 | 1 |
|---|---|---|---|
| `A` | `qA` | `1LC` | `1LT` |
| `B` | `qB` | `---` | `0LS` |
| `C` | `qC` | `1RD` | `1LH` |
| `D` | `qD` | `0RE` | `0RC` |
| `E` | `qE` | `0RF` | `1RF` |
| `F` | `qF` | `0RG` | `1RE` |
| `G` | `qG` | `1LA` | `1RF` |
| `H` | `qH` | `0LI` | `1LI` |
| `I` | `qI` | `0LJ` | `1LH` |
| `J` | `qJ` | `0LK` | `1LY` |
| `K` | `qK` | `1RL` | `1LJ` |
| `L` | `qL` | `0RM` | `0RV` |
| `M` | `qM` | `0RN` | `0RN` |
| `N` | `qN` | `0RO` | `1RR` |
| `O` | `qO` | `0RP` | `1RN` |
| `P` | `qP` | `0RQ` | `1RQ` |
| `Q` | `qQ` | `0LA` | `1RP` |
| `R` | `qR` | `0LS` | `1RN` |
| `S` | `qS` | `1LT` | `0LB` |
| `T` | `qT` | `0La` | `1LU` |
| `U` | `qU` | `0RL` | `1L\` |
| `V` | `qV` | `0RX` | `1RW` |
| `W` | `qW` | `0RV` | `1RV` |
| `X` | `qX` | `1LH` | `1RV` |
| `Y` | `qY` | `1RZ` | `1L^` |
| `Z` | `qZ` | `0RL` | `1R[` |
| `[` | `qAA` | `1RP` | `0RF` |
| `\` | `qAB` | `0LA` | `1L]` |
| `]` | `qAC` | `0LT` | `1L_` |
| `^` | `qAD` | `0LY` | `1LY` |
| `_` | `qAE` | `0LU` | `` 1L` `` |
| `` ` `` | `qAF` | `0L\` | `1La` |
| `a` | `qAG` | `0RI` | `1Lb` |
| `b` | `qAH` | `0L_` | `1LA` |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB34_halt.halt`. |
| Level | Machine-checked, with the standard fast-growing hierarchy of `Ord.v`: f_{ω^ω^ω^ω^ω^4}(5) ≤ N + 2 (`hardy_score`), hence f_{ω↑↑6}(4) < N (`sigma_lower_bound_w6_4`). N is the number of ones at the halt; the halt is B reading 0 (B0 = `---`), so σ = N, or N + 1 if the halting transition is taken to write a 1. |
| Exact score | Not computed (no closed form). |
| Steps | Not computed. |
| Compared with BB(33) | On paper (an argument, not a Coq lemma) above hydra33 (the BB(33) entry), so above BB(33) + 1. In Coq only above hydra33's proved lower bound. |

## How it works

hydra34 plays the hydra game of mxdys's hydra33 (see [`../BB29/hydra29.md`](../BB29/hydra29.md), section 1, for the
game and the pair encoding of hydras on the tape), with height limit **7**. Its game, scan and round lemmas are
the published BB31 files `BB31_game.v`, `BB31_scan.v`, `BB31_round.v` up to comments and names (Argon generated
them from the same templates); the transition table and the atomic pair rules (`BB34_tm.v`, `BB34_rules.v`)
are specific to this machine.

**Relation to hydra33** (checked here by propagating a state bijection from the halting state B along all
transitions). Up to a renaming of states, hydra34 is hydra33 with one transition
changed and one state added: hydra33's `A0` = `1LH` becomes C0 = `1RD`, into the new state D
(D0 = `0RE`, D1 = `0RC`), and the machine starts in the state that corresponds to hydra33's `` ` ``
instead of its A. Argon calls the new state a blank-tape pump: the changed opening builds a much larger first hydra
before the game starts. After 323 steps
(`init` in `BB34_halt.v`, checked by literal execution in chunks of 250 steps) the machine is in the game
configuration C(2): counter m = 2 and a hydra of height 7, of ordinal **ω^ω^ω^ω^ω^ω^4** (`x0_eq`:
`olist hs0 = powtower 6 (ofin 4)`).

## Proof

Halting and the bound come from one well-founded argument, exactly as for hydra31 and hydra33: the game is an
instance of the generic Hardy-hierarchy lemma `Hardy.hardy_game` (well-founded induction on the ordinals below
ε₀). Each round takes α = o(hydra) to α − 1 or into [α[m+3], α), with m → m + 1, and the empty hydra halts with
m + 1 ones. From C(2) this gives N + 2 ≥ H_{ω^ω^ω^ω^ω^ω^4}(5) (`hardy_bound`). H_{ω^β} = f_β with β = ω^ω^ω^ω^ω^4 gives `hardy_score`; (ω↑↑6)[4] = ω^ω^ω^ω^ω^4 and f_x(4) + 4 ≤ f_x(5) give f_{ω↑↑6}(4) < N (`sigma_lower_bound_w6_4`); `sigma_lower_bound_w6` and `sigma_lower_bound` are weaker.

## Comparison with BB(33)

hydra33 is the BB(33) entry; its proved bound is f_{ω^ω^ω^ω^ω^3}(4) ≤ N + 2, so f_{ω↑↑6}(3) < N; no upper bound for it is proved. In Coq, hydra34's bound f_{ω↑↑6}(4) < N is above that proved lower
bound. That hydra34 is above hydra33 itself, and so above BB(33) + 1, is an argument on paper: the initial hydras are ω^ω^ω^ω^ω^ω^4 at Hardy argument 5 (hydra34) and ω^ω^ω^ω^ω^ω^3 at argument 4 (hydra33): the top exponent is 4 instead of 3 and the argument one larger. This is the smallest margin of the three new entries; it holds if hydra33's N lies within the usual slack of H_x0(4) (each round lands in [α[m+3], α)).
A Coq lemma that would close it: an upper bound for hydra33's N (none is proved), for example N(hydra33) + 2 < f_{ω^ω^ω^ω^ω^4}(5).

## Verification

[`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1, built in CI (job `bb13-bb14`). `probe.v` checks the
transition table against the string above entry by entry (generated from the string, fixed-width rows) and
confirms that `halt`, `hardy_bound`, `x0_eq`, `hardy_score`, `sigma_lower_bound_w6_4`, `sigma_lower_bound_w6`, `sigma_lower_bound` are closed under the global context. The proof files are Argon's, unchanged except for
line endings; `Ord.v`, `Hardy.v` and `HydraOrd.v` are byte-identical to BB31's. A from-scratch build here took
397 s at low priority (re-checked by argon-scout-2; then rebuilt from the repository layout).

## Credit

Machine and Coq proof: **Argon** (Google Gemini, run by the repository owner in Google's Antigravity), 2026-11-09,
built on **mxdys**'s hydra machines (BB29, BB31, BB33; mxdys posted them in the bbchallenge Discord, 2026-10-26).
Re-check, probe and packaging: this project, 2026-11-13.
