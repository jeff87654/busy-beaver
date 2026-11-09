# Coq proofs for `0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR` (B21, Racheline)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (R0 undefined = the halt, `1RZ` in the string) it proves:

- `BB21_B21.halt : halts tm c0`: the machine halts from the blank tape;
- `BB21_B21.sigma_lower_bound`: the halting tape holds N ones with `tet 341 < N`, that is 4↑↑341 < N;
- `BB21_B21_run.abstract_halt`: the abstract block machine (`astepG refill21`) reaches `Halt` from the phase-3
  start `S3` (the combinatorial core: the invariant, the phases and the residue schedule).

As published:

    Theorem halt : halts tm c0.
    Theorem sigma_lower_bound :
      exists c N, c0 -[ tm ]->* c /\ halted tm c /\ BB21_B21_score.onesN c N /\ BB21_B21_score.tet 341 < N.
    Theorem abstract_halt : exists bs, star refill21 S3 bs /\ astepG refill21 bs = Halt.     (in BB21_B21_run)

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so the score is that N
plus one: the machine halts in state R reading 0, and the halting transition `1RZ` writes a 1, so σ = N + 1.
`tet 0 = 1`, `tet (n+1) = 4 ^ tet n`. `onesN c N` says that `c`'s tape is a finite word padded with 0s on both
sides holding N ones (the same definition as `ones` in the BB(19) and BB(20) files).

**Not proved here:** the wiki's bound f_(ω²)^2(4↑↑341). These files make no fast-growing-hierarchy statement.

## Files (in dependency order)

| file | content |
|---|---|
| `BB212.v`, `Individual212.v` | busycoq instantiated for 21 states (new here; the 20-state files with a 21st constructor). The 17th to 21st states (letters Q to U of the machine string) are the constructors `QQ`, `RR`, `SS`, `TT` and `UU`, because `Q` is busycoq's state type, `R` its direction, `S` is `Datatypes.S` and `T` is a common type variable (`UU` follows the pattern). The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB21_B21_absdef.v` | the abstract block machine `astep` / `astepG`: the block rules of the write-up, with the refill rule as a parameter (B21's is `refill21`) |
| `BB21_B21_tm.v` | TM macro lemmas, all parametric: the level-1 engine (`CA_E0`, `CA_E1`, `LV`, `Chain`, `CA_exit`), the sweep gadgets (`J_E_raw`, `J_dec_raw`, `J_est0_raw`, `J_est1_raw`, `J_P_raw`), the refill (`refill_halt`, `refill_cont`), the return walk (`RW`), the block-level lemmas and the boot (`boot`, 162 steps) |
| `BB21_B21_sim.v` | the machine simulates `astep` (`astep_sim`, `halts_from`) |
| `BB21_B21_grow.v` | growth and residues of the level maps h (`h_mod64`: h_m(x) ≡ 17 mod 64 for m ≥ 2), the gap lemma `GAP` |
| `BB21_B21_steps.v` | `astep` on states of the form b0, E blocks, frontier, blocks above |
| `BB21_B21_inv.v` | the dominance invariant `INV` (Lemma D) and its preservation (`inv_est`, `inv_dec_es`, `inv_dec_b0`, `inv_compl`, `inv_P`, `inv_refill`) |
| `BB21_B21_proc.v` | processing of one frontier block (`proc`; nested induction with the reverse-lexicographic order `RL_wf`) |
| `BB21_B21_phase.v` | phases: P walks through the 2s |
| `BB21_B21_run.v` | the run from phase 3 through phases 4, 5, 6 with the residue bookkeeping (`N4_form`, `abstract_halt`) |
| `BB21_B21_score.v` | the halting tape count (`onesN`), J_3 ≥ 64·4↑↑341 (`J3_tet`), `sigma_lower_bound_tet` |
| `BB21_B21.v` | the table and the two headline theorems |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 2 minutes) and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table of `BB21_B21.tm` against the machine string
entry by entry (42 checks generated from the string, not from the Coq file) and the blank start configuration. It
prints the definitions the statements use and runs `Print Assumptions` on the three theorems above: all three are
closed under the global context. CI job `bb13-bb14` runs the same script.

The proof was also checked with this project's `check.py` (extended to 21 states: the statement `halts tm c0` read
from the file, the table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-08.
