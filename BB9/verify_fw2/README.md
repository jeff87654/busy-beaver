# Coq proofs for `1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA` (fw2)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (I0 undefined = the halt, `1RZ` in the string) it proves:

- `BB9_fw2_1RB0RD.halt : halts tm c0` -- the machine halts from the blank tape;
- `BB9_fw2_bound.score_exact` -- the halting tape holds exactly `b3 + 3` ones, where `b3` is the explicit value
  computed by the run (see `BB9_fw2_1RB0RD.v`);
- `BB9_fw2_bound.sigma_lower_bound` -- the halting tape holds N ones with `f_omega (f_omega 465009) < N + 1`;
- `BB9_fw2_bound.sigma_lower_bound_strong` -- N ones and a b (= `b2`) with `2 ^ 465010 * f_omega 465009 <= b`,
  `b mod 8 = 7` and `f_omega (3 * (b / 4) + 3) < N + 1`;

and, in `BB9_fw2_vs_records.v`, that both machines halt, with N' and N ones, and N' + 1 < N (or N' + 1 < N + 1),
against:

- `fw2_beats_record` -- `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ`, the earlier BB(9) record
  of this repository (`../verify/`);
- `fw2_beats_redir_0LA` -- `1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LI0LC_1RG1LD_1LC0RH_1RG1LF_---0LA`;
- `fw2_beats_redir_0LA_fh` -- `1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LI0LC_1RG1LD_1LC1RH_0LH0RF_---0LA`;
- `fw2_beats_bb9_champion` -- `1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_1LB0LH` (Jacobzheng 2024);
- `fw2_beats_bb10_champion` -- `1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ` (Racheline
  2024, 10 states).

Each comparison uses the other machine's halting proof and its own Coq score theorem (exact score, or for the BB(10)
champion an upper bound), imported unchanged. The fast-growing hierarchy is the standard one, defined in
`BB9_fw2_bound.v`: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`, `f_omega n = f n n`. `ones c N` says that `c`'s tape is a
finite word padded with 0s on both sides holding N ones. fw2 halts in state I reading 0, and the halting transition
writes 1, so its standard score is N + 1.

## Files

| file | content | source |
|---|---|---|
| `BB9_fw2_1RB0RD.v` | fw2's halting proof: the digit family `Kd`, the rules `KR1`–`KR4Ex`, the clearing functions `U`, `X`, `Tv`, the parities, the 3-list run | Argon, unchanged |
| `BB9_fw2_bound.v` | the exact score and the hierarchy bounds; imports the halting file unchanged | Argon, unchanged |
| `BB9_fw2_vs_records.v` | the five comparisons | Argon, unchanged |
| `BB92.v`, `Individual92.v` | busycoq instantiated for 9 states | identical to `../verify/multifile/` |
| `BB9_record_1RB0RA.v`, `BB9_record_bound.v` | the earlier BB(9) record: halting, exact score | identical to `../verify/multifile/` |
| `BB9_champion_1RB1RA.v`, `BB9_champion_bound.v` | Jacobzheng's BB(9) champion: halting, exact score | identical to `../verify/multifile/` |
| `BB9_record_vs_champion.v` | the record against the champion (needed by `BB10_champion_upper.v`) | identical to `../verify/multifile/` |
| `BB9_redir_0LA.v`, `BB9_redir_0LA_bound.v` | `..._1LC0RH_1RG1LF_---0LA`: halting, exact score | this project, 2026-10-08; first published here |
| `BB9_redir_0LA_fh.v`, `BB9_redir_0LA_fh_bound.v` | `..._1LC1RH_0LH0RF_---0LA`: halting, exact score | this project, 2026-10-08; first published here |
| `BB102.v`, `Individual102.v` | busycoq instantiated for 10 states | identical to `../../BB10/verify/multifile/` |
| `BB10_champion_1RB1RA.v`, `BB10_champion_bound.v` | Racheline's BB(10) champion: halting, exact score | identical to `../../BB10/verify/multifile/` |
| `BB10_champion_upper.v` | an upper bound on that champion's score, in Knuth arrows | this project; first published here |
| `probe.v`, `probe_vs.v` | the independent probes (below) | added here |
| `compile_clean.sh`, `_CoqProject` | build script, project file | added here |
| `compile_clean.log`, `probe.log`, `probe_vs.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files | added here |

"Identical" means byte for byte (git stores one copy). All 19 `.v` files are also identical, up to line endings, to
the copies in the development where Argon's proofs were first checked.

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh          # both stages
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh core     # stage 1 only

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo` and
`Flip.vo` built. COQC may name a specific `coqc`.

- **Stage 1** compiles `BB92`, `Individual92`, `BB9_fw2_1RB0RD`, `BB9_fw2_bound` (38 s in the recorded build)
  and runs `probe.v`, writing `probe.log`.
- **Stage 2** compiles the other 15 files in dependency order and runs `probe_vs.v`, writing `probe_vs.log`
  (1 h 43 min with `PAR=1` in the recorded build; the longest file, `BB9_redir_0LA_fh.v`, took 90 min). Three of the files are large generated halting proofs (`BB9_record_1RB0RA.v`, 0.9 MB;
  `BB9_redir_0LA_fh.v`, 1.0 MB; `BB9_redir_0LA.v`, 0.2 MB). They do not depend on each other, and `PAR=1` compiles
  them in parallel.

The GitHub workflow (`.github/workflows/coq.yml`, job `bb9-fw2`) runs stage 1 (`compile_clean.sh core`) on every
push, and fails unless `probe.log` reports four theorems closed under the global context. Stage 2 takes hours and,
like BB10/ and BB12/, is not run in CI; it was checked locally (section "Verification record").

`probe.v`:
- re-checks by conversion all 18 entries of fw2's transition table against the machine string (the lines are
  generated from the string, not from the Coq file), and the blank start configuration;
- prints the definitions the statements use (`iter`, `f`, `f_omega`, `sym_val`, `count1`, `ones`, and `UX`, `U`,
  `Tpre`, `Tv`, `second`, `b1`, `b2`, `b3`) and the types of the four theorems;
- runs `Print Assumptions` for the four theorems.

`probe_vs.v`:
- re-checks by conversion the 92 entries of the five compared machines' tables against their strings, and the
  10-state start configuration;
- checks by `eq_refl` that the `ones` predicates of the four 9-state comparison files are `BB9_fw2_bound.ones`, and
  prints the 10-state `ones`;
- prints the types of the five comparison theorems and runs `Print Assumptions` for them.

Expected: the last lines of `probe.log` are four lines, and those of `probe_vs.log` five lines,

    Closed under the global context

and neither log contains `Axioms:`. (The compiled files themselves also print `Print Assumptions` results while
compiling; those lines are in `compile_clean.log`.)

## Verification record

`compile_clean.log`, `probe.log` and `probe_vs.log` are from a from-scratch build on 2026-10-16: Coq 8.20.1 (Coq
Platform 2025.01), Windows 11, a shared 16-core laptop, all coqc processes at Idle priority. A fresh directory held
only the 19 `.v` files, the two probes, `compile_clean.sh` and `_CoqProject`, next to busycoq `verify/` exported from
commit `bd2e36f` (`git archive`) with its 7 needed files compiled first. Command:
`BUSYCOQ=../busycoq/verify PAR=1 ./compile_clean.sh` (exit 0). `sha256.txt` has the hashes of the sources.
