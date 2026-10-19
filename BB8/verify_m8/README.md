# Coq proofs for `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---` (M8)

This directory is a Coq layer on top of the C04 development [`../../BB9/verify_c04/`](../../BB9/verify_c04/)
(busycoq commit `bd2e36f`, Coq 8.20.1). For M8 (H1 undefined: the halt) it proves, with no axioms:

- `Transfer.m8_halts : halts tm8 c0`;
- `Headline8.m8_fgh3`: every halted configuration c reached from the blank tape has N ones with
  `f_omega (f_omega (f_omega 12)) < N < f_omega (f_omega (f_omega 13))`;
- `Transfer.m8_fgh_bracket`, more precisely: the same N satisfies
  `f_omega (f_omega (12 * Bx + 26)) < N < f_omega (f_omega (12 * Bx + 27))` (2B + 4 = 2↑^13 3 is C04's
  `FArith.Bx_knuth`);
- `Transfer.m8_fgh_coarse`: the same N satisfies `f_w1 3 < N < f_w1 4` (f_(ω+1)(3) < N < f_(ω+1)(4));
- `Transfer.m8_score_exact`, `Transfer.m8_score_reached`, `Transfer.m8_sigma_bracket`: N = `Exact.sigma_c04`, C04's
  exact symbolic score;
- `Beats8.m8_beats_bb8r` (`12 * arrow 37 2 3 + 59 < N`) and `Beats8.m8_beats_champ35` (the previous BB(8) entry,
  `../verify/`, halts with Nf ones and Nf + 1 < N): M8 beats the previous entry's exact score;
- `Transfer.m8_beats_fw2`, and `Transfer.m8_score_to_c04` / `m8_score_from_c04` (the halting counts of M8 and C04 are
  the same).

The machine and the collapse are described in
[`../1RB0RA_..._0RG0RF_1RG---.md`](../1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---.md).

## Files

| file | content |
|---|---|
| `BB82.v`, `Individual82.v` | busycoq for 8 states, logical path `M8` (the same text as `../verify/`'s, which is under `BB8`; only `Individual82.v`'s `From M8` line differs) |
| `Tm8.v` | `tm8`, `ones` / `count1` / `sym_val` (verbatim copies of `BB8_champ35_bound`'s), `halted_unique8`, multistep facts |
| `Sim.v` | `stmap` (A..F → A..F, G → I, H → H), `symmap`, `Rel` (configurations related through finite tape lists), `sim_step`, `sim_run`, `m8_halts_sim`, `m8_to_c04`, `c04_to_m8` |
| `Transfer.v` | the M8 theorems, from C04's `c04_halts`, `c04_fgh_bracket`, `c04_fgh_coarse`, `c04_score_exact`, `c04_score_reached`, `c04_beats_fw2` |
| `Headline8.v` | `m8_fgh3`, from `Transfer.m8_fgh_bracket` and C04's `fgh/Headline.v` (`Bx_fw`: f_omega 12 < 12 Bx + 26, 12 Bx + 27 ≤ f_omega 13) |
| `Beats8.v` | `arrow_same` (C04's `arrow` and the previous entry's are the same Fixpoint), `m8_beats_bb8r`, `m8_beats_champ35` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh` | build script |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of the from-scratch build, hashes of the source files |

The `.v` files are those of the development where the layer was written (agent m8-coq), unchanged except for line
endings (`BB82.v` had CRLF there). Logical paths: the C04 tree's own (`lib` = `BB8`, `dev` = `Dev`, `k31` = `K31`,
`score` = `Score`, `fgh` = `Fgh`), this directory = `M8`, and, for `Beats8.v` and `probe.v` only, `../verify` = `BB8`
as well. The two `BB8` directories have no file name in common (`BB92`, `Individual92`, `BB9_fw2_*` against `BB82`,
`Individual82`, `BB8_champ35_*`), and this directory's `BB82`/`Individual82` are `M8.BB82`/`M8.Individual82`, so each
name resolves to one file.

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh deps    # ../../BB9/verify_c04, ../verify, then this directory
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh         # this directory only (the other two already compiled)

`C04` and `BB8V` may point to other compiled copies of `../../BB9/verify_c04` and `../verify`; COQC may name a specific
`coqc`. The C04 tree takes about 1 h 40 min on a 4-vCPU GitHub runner (see its README), `../verify` about 10 min, this
directory about a minute, and the probe about 10 minutes there (nearly all of it `Print Assumptions` over C04's
development). The GitHub workflow (job `bb8-m8`) runs `compile_clean.sh deps` whenever these files, `../verify` or
the C04 tree change (and weekly), and fails unless the probe reports eight results closed under the global context.

`probe.v`:
- checks by conversion all 16 entries of `tm8` against lines generated from the machine string, and again against a
  parser of the literal string `"1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---"` (`m8_string_ok`; the slot
  H1 = `---` parses to `None`), and that the start configuration is the blank tape in state A;
- prints the definitions the statements use (`ones`, `count1`, `sym_val`, `f`, `f_omega`, `f_w1`, `Bx`, both
  `arrow`s, `sigma_c04`, `stmap`, `Rel`) and checks the theorem types;
- states the main results as one conjunction `m8_all`, written out with qualified names, and proves it (`m8_all_ok`);
- runs `Print Assumptions` on `m8_all_ok`, `m8_beats_fw2`, `m8_score_to_c04`, `m8_score_from_c04`, `m8_string_ok`,
  `m8_beats_bb8r`, `m8_beats_champ35`, and `m8_headline_ok` (`m8_fgh3` with its type written out).

Expected: `probe.log` contains eight lines `Closed under the global context` and no `Axioms:`.

## Verification record

`compile_clean.log` and `probe.log` are from a build on 2026-10-18: Coq 8.20.1 (Coq Platform 2025.01), Windows 11,
a shared 16-core laptop, every coqc at Idle priority. `../verify` was compiled from scratch in a fresh directory
(`BB8_champ35_1RB0RA.v` 560 s, the whole tree with its probe 11.5 min), and this directory was compiled from scratch on
top of it and of the clean C04 tree recorded in `../../BB9/verify_c04/` (`compile_clean.sh` with `C04` and `BB8V` set
to those copies): the six files took 84 s and the probe 2328 s (the machine was busy), and the probe reported seven
results closed under the global context. `Headline8.v` was added after that: the whole layer was recompiled on the same trees (the seven files about 50 s) and
the extended probe rerun (1245 s), with eight results closed under the global context (`probe.log`; the log of that
run is `../../BB9/verify_c04/compile_headline.log`). `sha256.txt` has the SHA-256 of the `.v` files and
`compile_clean.sh`.
