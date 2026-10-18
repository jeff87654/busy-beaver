# Coq proofs for `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF` (C04)

This directory is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (H1 undefined: the halt) it proves:

- `Final.c04_halts : halts tm c0`: the machine halts from the blank tape;
- `EndU.c04_fgh_bracket`: every halted configuration c reached from the blank tape has N ones with
  `f_omega (f_omega (12 * Bx + 26)) < N < f_omega (f_omega (12 * Bx + 27))`, where `Bx` is B and
  `FArith.Bx_knuth : 2 * Bx + 4 = arrow 13 2 3`, i.e. 2B + 4 = 2↑^13 3 (also `FArith.R2_knuth :
  2 * R2 Bx + 4 = arrow (12 * Bx + 26) 2 4`);
- `EndU.c04_fgh_coarse`: the same N satisfies `f_w1 3 < N < f_w1 4`, where `f_w1 n = iter n f_omega n` is
  f_(ω+1)(n);
- `Exact.c04_score_exact`, `Exact.c04_score_reached`, `Exact.c04_sigma_bracket`: N = `sigma_c04`, an explicit
  symbolic recursion along the cascade (not evaluable in practice), and `sigma_c04` lies in the bracket;
- `ScoreEnd.c04_sigma_lower_bound`: it reaches a halted configuration c whose tape holds N ones with
  `f_omega (f_omega (465 * 1000 + 9)) < N`;
- `ScoreEnd.c04_beats_fw2`: the same, and fw2 (`1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA`, the
  previous BB(9) entry, `../verify_fw2/`) reaches a halted configuration with Nf ones, and `Nf + 1 < N`.

No axioms. `f`, `f_omega` and `ones` are the definitions of fw2's `BB9_fw2_bound.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`; `ones c N` says that c's tape is a finite word padded with 0s on both
sides holding N ones. C04 halts in state H reading 1, so its score is N. fw2 halts in state I reading 0 and its
halting transition writes 1, so its score is Nf + 1. The machine, the run and the proof are described in
[`../1RB0RA_..._1RI---_0RI0RF.md`](../1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF.md).

## Files

Logical paths: `lib/` is `BB8` (historical; the fw2 files use this name), `dev/` is `Dev`, `k31/` is `K31`,
`score/` is `Score`. "Generated" files were written by the development's symbolic executor: one lemma per phase of a
rule, with the run lengths as variables, proved by stepping the machine (busycoq's `execute`, `follow`, `step`) and by
induction for each repeated block.

| file | content |
|---|---|
| `lib/BB92.v`, `lib/Individual92.v` | busycoq instantiated for 9 states (identical to `../verify_fw2/multifile/`) |
| `lib/BB9_fw2_1RB0RD.v`, `lib/BB9_fw2_bound.v` | fw2's halting proof and exact score, Argon's files (identical to `../verify_fw2/multifile/`) |
| `dev/Base.v` | the transition table, notations, tape normalization |
| `dev/Abs.v` | the token family `Kt`/`Kg`, the champion rules on tokens, the clearing `CDP`, `U`, the arrow identities, B (`Bx`, B ≡ 1 mod 5), the first 2369 steps (`init_reach`), `run_to_exhaustion` |
| `dev/G_rules.v` | generated: the machine lemmas of the champion rules |
| `dev/G_reb1.v`, `dev/Chain.v` | generated: exhaustion #1 (the rebuild); `Chain.reach_exh2`: the blank tape reaches the start of exhaustion #2 with R₂ |
| `dev/Lift.v` | the abstract cascade moment `D0f t L P s y l` (run L, parked list P, t tail blocks) |
| `dev/G_top.v` | generated: exhaustion #2 at the far end (the parked list) and its first sub-step |
| `dev/G_sub2.v` … `dev/G_sub5.v` | generated: the sub-steps for L ≡ 1, 2, 3, 4 (mod 5) |
| `dev/G_stop.v`, `dev/G_entry.v` | generated: the stop (L ≡ 0 mod 5), and the entry of the next exhaustion after its clear |
| `dev/Step.v` | the generated lemmas restated on `D0f` (six cases by P mod 6 each), `casc_stepP` (one orbit step), `reach_top` |
| `dev/Orbit.v` | the orbit map `gstep`, parity, ≡ 1 (mod 3), decrease, the key set {31, 37, 43, 49, 55} |
| `dev/Cascade.v` | `cascade_from_start`: the well-founded induction on L down to a key |
| `dev/Fin.v` | the cascade invariant with a finite far side (for the ones count) |
| `dev/G_end.v`, `dev/CBtail.v` | generated: the class-b tail (ESC, the counter 6 → 3 → 0, the halt); `classb_tail` |
| `dev/G_p14_0.v` … `dev/G_p14_5.v`, `dev/G_p20_0.v` … `dev/G_p20_5.v` | generated: the class-b entry prefixes from run 13 and run 19 (sketch values), one file per P mod 6 |
| `dev/Endgame.v` | `casc_key` for keys 37, 43, 49, 55 (key 31 as a section hypothesis), `c04_halts_from_k31` |
| `k31/K_rf.v`, `k31/K_x.v`, `k31/K_e1.v`, `k31/K_e2.v` | generated: the key-31 endgame (champion rules with a free far side; local rules and the halt; the entry; the five post-ESC forms) |
| `k31/K31_Abs.v` | the clearing `CDPf`, the counter `COUNT` (induction), the two-digit clears, `ones` |
| `k31/K31_Mach.v`, `k31/K31_End.v` | the key-31 machine lemmas restated; `k31_end` |
| `dev/Final.v` | `c04_halts` (`c04_halts_from_k31` applied to `k31_end`) |
| `score/Score.v` | f_k ≤ U_k and f_ω(f_ω(465009)) < U_K(0) for K ≥ R₂ |
| `score/Fw2Link.v` | `Score.f_omega` and fw2's `f_omega` are convertible; the bound restated with fw2's constants |
| `score/Fw2Upper.v` | an upper bound on fw2's exact score (b₃ + 5 ≤ U_K(0) for K ≥ R₂) |
| `score/ScoreK.v` | from the endgame data (K ≥ 11R₂) to the three score conclusions |
| `dev/ScoreEnd.v` | `c04_sigma_lower_bound`, `c04_beats_fw2` (the cascade again, with the ones count at the halt) |
| `fgh/FArith.v` | hierarchy arithmetic: f_(k+2)(n) ≤ U_k(n), U_j(x) < f_(j+2)(2x + 4), `Bx_knuth`, `R2_knuth`, the lower and upper chains, the coarse bounds |
| `fgh/Tower.v` | the scale `T P m` of iterates of one U, closed under +, ·, U and iteration at lower levels |
| `fgh/Uniq.v` | the halting configuration is unique; the exact ones count of the final tape |
| `fgh/CascU.v` | the cascade invariant with upper bounds (parked list ≤ 12R₂ + 11, run, tokens and tail bounded) |
| `fgh/EndU.v` | every endgame route ending in an explicit tape; `c04_fgh_bracket`, `c04_fgh_coarse`, `c04_fgh_exists` |
| `fgh/Exact.v` | the recursion `sigma_c04` and `c04_score_exact`, `c04_score_reached`, `c04_sigma_bracket` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `compile_fgh.log`, `probe.log`, `sha256.txt` | logs of the from-scratch build and of `fgh/` on top of it, the probe, hashes of the source files |

The 55 `.v` files are those of the development where the proof was written, unchanged, except that four of them
(`dev/Lift.v`, `score/Fw2Link.v`, `score/Fw2Upper.v`, `score/ScoreK.v`, and `fgh/FArith.v`, `fgh/Uniq.v`, `fgh/EndU.v`,
`fgh/Exact.v`) had CRLF line endings there; here every file has LF endings. `fgh/` adds no machine lemmas: it reuses
the compiled dev, k31 and score files. There the dev and k31 files were compiled with `BB8` = a directory holding only `BB92` and `Individual92`,
and the score files with `BB8` = a directory that also held the fw2 files (byte-identical `BB92.v` and
`Individual92.v`); here `lib/` holds all four. Some comments name the development's generator scripts (`gen/*.py`) and
build wrappers (`coqc_score.py`, …); those are not part of the proof and are not included. Only the 55 files in the
dependency closure of the theorems are included (a few auxiliary files of the development are not).

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh          # everything, then probe.v
    BUSYCOQ=/path/to/busycoq/verify J=8 ./compile_clean.sh      # 8 coqc at a time (default 4)

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo` and
`Flip.vo` built. COQC may name a specific `coqc`. The script knows each file's dependencies (its `Require` lines) and
starts a file as soon as they are compiled, the longest files first; per-file coqc output goes to `_logs/`. Two more
forms are used by CI: `./compile_clean.sh only FILE…` compiles just the listed files (it checks that the `.vo` files
they need exist), and `./compile_clean.sh probe` runs only the probe.

On a GitHub runner the whole build is about 3.2 CPU-hours when each file has a core to itself. 26 generated files that
need only `dev/Base.v` take nearly all of it; the longest are `k31/K_e1.v` (35 min alone), `dev/G_sub2.v` (27 min) and
`k31/K_e2.v` (17 min). With J = 4 on a 4-vCPU runner the files slow each other down and the build takes about
1 h 40 min. At Idle priority on our shared machine everything took about three to four times
as long (section "Verification record"). Memory: under 1 GB per coqc.

The GitHub workflow (`.github/workflows/coq.yml`, job `bb9-c04`) runs `compile_clean.sh` with J = 4 on every push,
and fails unless all 55 `.vo` files are built and `probe.log` reports four results closed under the global context
and no `Axioms:`. It also checks that the four `lib/` files are byte-identical to `../verify_fw2/multifile/`.

`probe.v`:
- checks by conversion all 18 entries of the transition table `Base.tm` against lines generated from the machine
  string (the undefined H1 is `None`), and that the start configuration is the blank tape in state A;
- prints the definitions the statements use (`c0`, `halted`, `sym_val`, `count1`, `ones`, `f`, `f_omega`, and for
  fgh/ `U`, `iter`, `arrow`, `Bx`, `R2`, `f_w1`, `sigma_c04` with all the pieces of its recursion);
- checks that `K31_Abs.ones` and `Score.f_omega` (the names the statements use) are equal, by `reflexivity`, to fw2's
  `BB9_fw2_bound.ones` and `BB9_fw2_bound.f_omega`;
- checks the types of the three theorems, written out in full with qualified names (`Base.tm`, `K31_Abs.ones`,
  `Score.f_omega`, `BB9_fw2_1RB0RD.tm`, …), so that no name in a statement can silently refer to something else;
- states the fgh/ results (`c04_fgh_bracket`, `c04_fgh_coarse`, `c04_score_exact`, `c04_score_reached`,
  `c04_sigma_bracket`, `Bx_knuth`, `R2_knuth`) as one conjunction `c04_fgh_all`, written out with qualified names,
  and proves it from them (`c04_fgh_all_ok`);
- runs `Print Assumptions` on the three main theorems and on `c04_fgh_all_ok`.

Expected: `probe.log` contains four lines (three after the main theorems, one at the end)

    Closed under the global context

and it contains no `Axioms:`. (`Final.v` and `ScoreEnd.v` also print `Print Assumptions` while compiling; those lines
are in `_logs/`.)

## Verification record

`compile_clean.log` is from a from-scratch build of the first 49 files (everything but `fgh/`) on 2026-10-18:
Coq 8.20.1 (Coq Platform 2025.01), Windows 11, a shared 16-core laptop, every coqc at Idle priority. A fresh directory held only the 49 `.v` files,
`probe.v` and `compile_clean.sh`, next to a fresh clone of busycoq at commit `bd2e36f` with its 7 needed files compiled
first. Command: `BUSYCOQ=../busycoq/verify J=4 ./compile_clean.sh`, with `COQC` set to a wrapper that starts coqc at Idle
priority (exit 0). Times: compile 7681 s (2 h 08 min) of wall time, then the probe 560 s; the per-file times add up to
29,017 s (8.1 h; `k31/K_e1.v` 7121 s, `dev/G_sub2.v` 3611 s, `k31/K_e2.v` 2211 s). The probe reported the three
theorems closed under the global context, and `Final.v` and `ScoreEnd.v` printed the same while compiling.

That build used `compile_clean.sh` as it was before two later edits: the header comment, and the check in `only` mode
that the needed `.vo` files exist. Both modes of the final script were then run on the built tree (`only dev/Final`,
178 s, and the error cases).

On GitHub (run 39139815864, the first push of this directory, with the build split over seven jobs) the per-file
times added up to 11,627 s (3.2 h; `k31/K_e1.v` 2074 s, `dev/G_sub2.v` 1606 s, `k31/K_e2.v` 1020 s) and the probe
again reported three closed theorems. With the whole build in one job (J = 4, run 39143800688) the compile took
5517 s and the probe 355 s, again with three closed theorems; `k31/K_e1.v` took 5187 s there, sharing the 4 vCPUs.
(That run's final step failed only because it counted `probe.vo` among the 49 `.vo` files; the count was fixed.)

`fgh/` was added afterwards. `compile_fgh.log` compiles its six files on top of that clean tree (`compile_clean.sh
only fgh/…`, Idle priority) and then runs the extended probe, and `probe.log` is that probe's output (four results
closed under the global context; the fgh files took 367 s, the probe 1462 s on a loaded machine). The first probe
attempt in that log failed on a typo in the new part of `probe.v` (a lost `/\`), which was fixed before the second
attempt. The GitHub job `bb9-c04` builds all 55 files from scratch.

`sha256.txt` has the SHA-256 of the 55 `.v` files, `probe.v`, `compile_clean.sh` and `_CoqProject`, as committed.
