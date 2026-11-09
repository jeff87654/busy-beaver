# Coq proofs for `0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR` (W2PR)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (R0 undefined = the halt, `1RZ` in the string) it proves:

- `BB25_W2PR.halt : halts tm c0`: the machine halts from the blank tape;
- `BB25_W2PR.sigma_lower_bound`: the halting tape holds N ones with `iter 5 Fh (tet 341) < N`, that is
  Fh⁵(4↑↑341) < N;
- `BB25_W2PR_run.abstract_finalW`: the abstract block machine with W2PR's refill rule (`refillW`) reaches, from the
  phase-3 start `S3`, the end of phase 8 with J accumulator 6 mod 8 (the halting class) and
  Fh⁵(4↑↑341) ≤ Fh(number of E blocks + 1).

As published:

    Theorem halt : halts tm c0.
    Theorem sigma_lower_bound :
      exists c N, c0 -[ tm ]->* c /\ halted tm c /\ BB25_W2PR_score.onesN c N /\
        (BB21_B21_absdef.iter 5 BB25_W2PR_run.Fh (BB25_W2PR_run.tet 341) < N)%nat.
    Theorem abstract_finalW : exists s, BB21_B21_proc.star refillW BB21_B21_run.S3 (enc s) /\ PhaseEnd s /\
      jacc s mod 8 = 6 /\ iter 5 Fh (tet 341) <= h (length (es s) + 1) 0.          (in BB25_W2PR_run)

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so the score is that N
plus one: the machine halts in state R reading 0, and the halting transition `1RZ` writes a 1, so σ = N + 1.
`Fh n = h n 0`, with B21's level maps `h 0 x = x + 4`, `h (S m) x = iter (x + 3) (h m) 1` (`BB21_B21_absdef.v`), so Fh
is f_ω-class; `tet 0 = 1`, `tet (n+1) = 4 ^ tet n`. `onesN c N` says that `c`'s tape is a finite word padded with 0s
on both sides holding N ones (as in the BB(19)–BB(21) files).

**Not proved here:** the paper estimate f_(ω²)^5(4↑↑340). These files make no other fast-growing-hierarchy statement.

## Files (in dependency order)

| file | content |
|---|---|
| `BB252.v`, `Individual252.v` | busycoq instantiated for 25 states (new here; the 21-state files with four more constructors). The 17th to 25th states (letters Q to Y of the machine string) are the constructors `QQ`, ..., `YY`. The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB21_B21_absdef.v`, `BB21_B21_grow.v`, `BB21_B21_steps.v`, `BB21_B21_inv.v`, `BB21_B21_proc.v`, `BB21_B21_phase.v`, `BB21_B21_run.v` | **B21's layers, byte-identical** to [`../../BB21/verify/multifile/`](../../BB21/verify/multifile/)'s: the abstract block machine with the refill rule as a parameter, growth and residues, the dominance invariant `INV`, frontier processing, phases (all generic in the refill rule), and B21's run file (its phase-3 start `S3`, `J3`, `N4` and the phase-start invariant are reused). `share_check.sh` checks the identity. |
| `BB25_W2PR_tm.v` | the TM layer for W2PR's table: B21's engine and sweep gadgets retargeted, and the period-8 refill (`zig8`, `refill_halt`, `refill_cont_a`, `refill_cont_b`, `refill_V`), the block-level lemmas and the boot (162 steps) |
| `BB25_W2PR_sim.v` | the refill rule `refillW` (halt iff the J accumulator is 6 mod 8 before the last P; B21's continue at 0 mod 4; the V continue at 2 mod 8) and the simulation of `astepG refillW` by the machine |
| `BB25_W2PR_run.v` | residues mod 256 (`h_mod256`: 81), the V phase start, phases 4 to 8 (J accumulators 4, 0, 2, 2, 6 mod 8 at their ends), the growth bound through `Fh` (`Fh_step`, `step_lb`), `abstract_finalW` |
| `BB25_W2PR_score.v` | the halting tape count (`onesN`), `sigma_lower_boundW`, `haltW` |
| `BB25_W2PR.v` | the table and the two headline theorems |
| `probe.v` | the independent probe (below) |
| `share_check.sh` | checks that the seven B21 layers are byte-identical to `../../BB21/verify/multifile/`'s |
| `compile_clean.sh`, `_CoqProject` | build script (runs `share_check.sh` first when the BB21 tree is present), project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 3 minutes) and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table of `BB25_W2PR.tm` against the machine string
entry by entry (50 checks generated from the string, not from the Coq file) and the blank start configuration. It
prints the definitions the statements use and runs `Print Assumptions` on the three theorems above: all three are
closed under the global context. CI job `bb13-bb14` runs the same script.

The proof was also checked with this project's `check.py` (extended to 25 states: the statement `halts tm c0` read
from the file, the table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-08.
