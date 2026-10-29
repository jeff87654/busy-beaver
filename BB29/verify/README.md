# Coq proofs for BB29

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For the machine

    0LP1LD_---0LC_1LR0LB_1RF1LE_0LD1LD_0R[1RG_1RN0RK_0RI1RJ_1LZ1RH_0RH1RH_0RL1RM_1L\1RK_0RK1RK_0RO1RO_0L\1RN_1R[1LA_0RV0RV_0LT1LS_0R[1LT_0RY1LU_0LR1L\_0RW1RX_0RN1RV_0LC1RV_0LA1LZ_0LY1LY_0RQ0RH_1L]1LR_1LH1LZ

(B0 undefined = the halt) it proves:

- `BB29_halt.halt : halts tm c0`: the machine halts from the blank tape;
- `BB29_bound.score_exact`: the halting tape holds exactly `T 4 S 1 + 1` ones (T as in the write-up, section 3);
- `BB29_bound.sigma_lower_bound`: the halting tape holds N ones with `FGH (tower 2) 3 < N`, i.e. f_{ω^ω}(3) < N (`tower 2` = ω^ω);
- `BB29_bound.U_is_FGH`: `U k S n = FGH (opow (ofin k)) n`, the bridge from the recursion used in the proof to the standard f_{ω^k}.

The ordinals below ε₀ and the fast-growing hierarchy are defined in `Ord.v`: hereditary Cantor normal form
(`ord := oz | ow a b`, ω^a + b), the standard fundamental sequences ((β + ω^(γ+1))[n] = β + ω^γ·n,
(β + ω^λ)[n] = β + ω^(λ[n]), ω^ω[n] = ω^n), and f as an inductive relation `fgh` (f_0(n) = n+1,
f_(α+1)(n) = f_α^n(n), f_λ(n) = f_(λ[n])(n)), proved deterministic and total below ε₀, so `FGH` is a function;
`tower k` = ω↑↑k. `ones c N` says the tape of c is a finite word padded with 0s holding N ones. `probe.v` prints
all of these definitions.

## Files

| file | content |
|---|---|
| `BB292.v`, `Individual292.v` | busycoq instantiated for 29 states. State character c is the constructor q + the spreadsheet column of ord(c) − 65: A..Z → qA..qZ, then `[`, `\`, `]`, `^`, `_`, `` ` ``, `a` → qAA..qAG. This avoids clashes with L, R, S, O, I, Q, Z. |
| `BB29_tm.v` | the transition table, with the machine string in its header |
| `BB29_rules.v` | pair alphabet and the atomic pair rules |
| `BB29_scan.v` | scan lemmas and the copy lemma |
| `BB29_round.v` | round lemmas (copy, chop, halt) |
| `BB29_hydra.v` | hydra encoding and the round-by-round processing lemma |
| `BB29_halt.v` | the 175-step opening and `halt` |
| `BB29_bound.v` | exact score, `U_is_FGH`, the bound |
| `Ufun.v` | the recursions T and U, and T ≥ U |
| `Ord.v` | ordinals and the fast-growing hierarchy; byte-identical in BB29/, BB31/ and BB33/ (`Hardy.v` and `HydraOrd.v` are shared by BB31/ and BB33/ only) |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`probe.v` checks the compiled transition table against the machine string entry by entry (lines generated from the
string, not from the Coq file; rows are fixed-width), prints the definitions the statements use, and runs
`Print Assumptions` on the four theorems above: all four are closed under the global context. CI job `bb13-bb14`
runs the same script.
