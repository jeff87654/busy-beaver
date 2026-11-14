# Coq proofs for hydra34 (34 states)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For the machine

```
1LC1LT_---0LS_1RD1LH_0RE0RC_0RF1RF_0RG1RE_1LA1RF_0LI1LI_0LJ1LH_0LK1LY_1RL1LJ_0RM0RV_0RN0RN_0RO1RR_0RP1RN_0RQ1RQ_0LA1RP_0LS1RN_1LT0LB_0La1LU_0RL1L\_0RX1RW_0RV1RV_1LH1RV_1RZ1L^_0RL1R[_1RP0RF_0LA1L]_0LT1L__0LY1LY_0LU1L`_0L\1La_0RI1Lb_0L_1LA
```

(B0 undefined = the halt; `Z` is an ordinary state) it proves:

- `BB34_halt.halt : halts tm c0`: the machine halts from the blank tape;
- `BB34_halt.hardy_bound`: the halting tape holds N ones with `HH (olist hs0) 5 <= N + 2`, and
  `BB34_halt.x0_eq : olist hs0 = powtower 6 (ofin 4)`;
- `BB34_bound.hardy_score`: `FGH (powtower 5 (ofin 4)) 5 <= N + 2`;
- `BB34_bound.sigma_lower_bound_w6_4`: `FGH (tower 6) 4 < N`;
- weaker corollaries: FGH (tower 6) 3 < N (`sigma_lower_bound_w6`), FGH (tower 4) 3 < N.

`Ord.v` (ordinals below ε₀ in Cantor normal form, standard fundamental sequences, the fast-growing hierarchy
`FGH`), `Hardy.v` (the Hardy hierarchy `HH`, `hardy_game`) and `HydraOrd.v` (hydras and their ordinals) are
byte-identical to [`../../BB31/verify/multifile/`](../../BB31/verify/multifile/)'s; see
[`../../BB31/verify/README.md`](../../BB31/verify/README.md) for their content. `tower k` = ω↑↑k, `powtower j y` = ω^…^y
with j omegas. `ones c N` says the tape of c is a finite word padded with 0s holding N ones. `probe.v` prints all
of these definitions.

## Files

| file | content |
|---|---|
| `BB342.v`, `Individual342.v` | busycoq instantiated for 34 states (as BB31's, with 34 state constructors). State character c is the constructor q + the spreadsheet column of ord(c) − 65: A..Z → qA..qZ, then `[`, `\`, `]`, `^`, `_`, `` ` ``, `a`, `b` → qAA..qAH. |
| `BB34_tm.v` | the transition table, with the machine string in a comment |
| `BB34_rules.v` | pair alphabet, state roles, atomic pair rules |
| `BB34_scan.v`, `BB34_round.v`, `BB34_game.v` | scan lemmas, round lemmas, the game as an instance of `hardy_game` (BB31's files up to comments and names) |
| `BB34_halt.v` | the 323-step opening (literal, in chunks of 250 steps), the initial hydra, `hardy_bound`, `halt` |
| `BB34_bound.v` | the FGH statements |
| `Ord.v`, `Hardy.v`, `HydraOrd.v` | shared library (copies of BB31's) |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`probe.v` checks the compiled transition table against the machine string entry by entry (lines generated from
the string, not from the Coq file; rows are fixed-width), prints the definitions the statements use, and runs
`Print Assumptions` on 7 theorems (`halt`, `hardy_bound`, `x0_eq`, `hardy_score`, `sigma_lower_bound_w6_4`, `sigma_lower_bound_w6`, `sigma_lower_bound`): all are closed under the global context. CI job
`bb13-bb14` runs the same script.
