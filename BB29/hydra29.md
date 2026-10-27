# BB29: a 29-state hydra machine at level f_{ω^ω}

    0LP1LD_---0LC_1LR0LB_1RF1LE_0LD1LD_0R[1RG_1RN0RK_0RI1RJ_1LZ1RH_0RH1RH_0RL1RM_1L\1RK_0RK1RK_0RO1RO_0L\1RN_1R[1LA_0RV0RV_0LT1LS_0R[1LT_0RY1LU_0LR1L\_0RW1RX_0RN1RV_0LC1RV_0LA1LZ_0LY1LY_0RQ0RH_1L]1LR_1LH1LZ

Found by **mxdys**, who posted it, with BB31 ([`../BB31/`](../BB31/)) and BB33 ([`../BB33/`](../BB33/)), in the
bbchallenge Discord (#large-bb-domains) on 2026-10-26 as an unverified AI-generated result, with the claim
BB(29) > f_{ω^ω}(3). The analysis and the Coq proofs were done here (2026-10-27) and confirm the claim.

States after Z are the next ASCII characters (`[ \ ]`), so the string is read in fixed-width rows of 6 characters
(row i = characters 7i..7i+5). In Coq, state character c is the constructor q + its spreadsheet-column name.

| state | Coq | 0 | 1 |
|---|---|---|---|
| `A` | `qA` | `0LP` | `1LD` |
| `B` | `qB` | `---` | `0LC` |
| `C` | `qC` | `1LR` | `0LB` |
| `D` | `qD` | `1RF` | `1LE` |
| `E` | `qE` | `0LD` | `1LD` |
| `F` | `qF` | `0R[` | `1RG` |
| `G` | `qG` | `1RN` | `0RK` |
| `H` | `qH` | `0RI` | `1RJ` |
| `I` | `qI` | `1LZ` | `1RH` |
| `J` | `qJ` | `0RH` | `1RH` |
| `K` | `qK` | `0RL` | `1RM` |
| `L` | `qL` | `1L\` | `1RK` |
| `M` | `qM` | `0RK` | `1RK` |
| `N` | `qN` | `0RO` | `1RO` |
| `O` | `qO` | `0L\` | `1RN` |
| `P` | `qP` | `1R[` | `1LA` |
| `Q` | `qQ` | `0RV` | `0RV` |
| `R` | `qR` | `0LT` | `1LS` |
| `S` | `qS` | `0R[` | `1LT` |
| `T` | `qT` | `0RY` | `1LU` |
| `U` | `qU` | `0LR` | `1L\` |
| `V` | `qV` | `0RW` | `1RX` |
| `W` | `qW` | `0RN` | `1RV` |
| `X` | `qX` | `0LC` | `1RV` |
| `Y` | `qY` | `0LA` | `1LZ` |
| `Z` | `qZ` | `0LY` | `1LY` |
| `[` | `qAA` | `0RQ` | `0RH` |
| `\` | `qAB` | `1L]` | `1LR` |
| `]` | `qAC` | `1LH` | `1LZ` |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB29_halt.halt`. |
| Exact score | Machine-checked: N = T₄(S)(1) + 1 ones at the halt (`score_exact`), with T the recursion of section 3. The halt is B reading 0 (B0 = `---`), so σ = N, or N + 1 if the halting transition is taken to write a 1. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_{ω^ω}(3) < N (`sigma_lower_bound`), the posted claim. Informally σ ≈ f_{ω^ω}(4). |
| Steps | Not computed. |

## 1. How it works: a hydra game

The tape is read in 2-cell pairs: `01` = `(`, `11` = `)`, `10` = a marked `)`, `00` = blank / separator. Between
a unary counter m on the left and the blank on the right, the tape spells a **hydra** (a rooted tree) as a
bracket string. Each round:

- the rightmost head (leaf) is cut off;
- if its parent p is not the root, p (with the head removed) is copied, so that it appears m + 3 times in all;
- the counter m grows by one.

The machine halts when the hydra is empty, with m + 1 ones on the tape. The bracket depth is tracked by a small
left-scanning counter of states (R, T, \ here), which is what limits the hydra's height: height 3 for BB29,
5 for BB31, 7 for BB33. Apart from that counter, the three machines run the same pair-level program up to a
renaming of states.

With o(node) = ω^{o(c₁)} + … + ω^{o(c_k)} (an ordinary sum in tape order), a round takes α = o(hydra) to α − 1
when the cut head hangs from the root, and to an ordinal in [α[m+3], α) otherwise. So the game is a version of
the Hardy hierarchy, and the score is at least H_α(m+3) − 2 for the hydra at counter m.

## 2. The run

From the blank tape, 175 steps reach C(1): counter m = 1 and the hydra root → A → B → 4 leaves, ordinal
ω^(ω^4) (`init` in `BB29_halt.v`). From there the hydra stays sorted and of height ≤ 3.

## 3. Exact score and bound

For BB29 the run has a closed form. Write a height-3 hydra as a list of nodes A, each A being the list of its
children's leaf counts, and set

- T₀(φ)(m) = φ^{m+3}(m+1), T_{k+1}(φ)(m) = (T_k)^{m+3}(φ)(m+1);
- W([]) = S, W(A₀ ++ [k]) = T_k(W(A₀)).

A round-by-round nested induction (on k, then on the number of iterations; no ordinals needed) shows that
C(m, [A₁ … A_r]) reaches C(W(A₁)(…W(A_r)(m)…), []), which halts. From C(1, [[4]]) this gives N = T₄(S)(1) + 1.

For the bound: with U₀(ψ)(n) = ψⁿ(n) and U_{k+1}(ψ)(n) = (U_k)ⁿ(ψ)(n), U_k(S) = f_{ω^k} (`U_is_FGH`, against
the ordinal library `Ord.v`), and T_k φ (x) ≥ U_k ψ (x+1) for ψ ≤ φ monotone and inflationary. So
N − 1 = T₄(S)(1) ≥ U₃(S)(3) = f_{ω³}(3) = f_{ω^ω}(3) (since ω^ω[3] = ω³).

## 4. Verification

[`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1, from-scratch build 41 s, built in CI (job `bb13-bb14`).
`probe.v` checks the transition table against the string above entry by entry and confirms that `halt`,
`score_exact`, `sigma_lower_bound` and `U_is_FGH` are closed under the global context. The ordinals below ε₀,
their standard fundamental sequences and the fast-growing hierarchy are defined in `Ord.v` (shared with BB31 and
BB33; see [`verify/README.md`](verify/README.md)).

## Credit

Machine: **mxdys** (AI-generated, posted to the bbchallenge Discord, 2026-10-26, with the claim
BB(29) > f_{ω^ω}(3)). Analysis (reverse-engineering the hydra game, simulation checks of every rule; see
[`analysis/`](analysis/)) and Coq proofs: this project, 2026-10-27.
