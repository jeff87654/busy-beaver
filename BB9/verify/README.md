# Coq proofs for `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ`

`BB9_record_1RB0RA_selfcontained.v` is ONE Coq file, depending only on the Coq standard library
(Coq 8.20.1, Coq Platform 2025.01), that proves for this machine (I1 undefined = the halt):

- `halt` : the machine halts from the blank tape;
- `score_closed` : the halting tape holds exactly `3 * arrow (12*Bx-9) 2 8 + 108 * (Bx/5) + 70` ones,
  with `2*Bx+4 = arrow 13 2 3` (`Bx_arrow13`); in Knuth arrows, with T = 2↑^13 3:
  sigma = 3·(2↑^(6T−33) 8) + (54T+26)/5;
- `sigma_lower_bound` : more than 2↑^(2↑^13 3) 3 ones (and `sigma_lower_bound_strong`: more than 2↑^(6T−33) 8);
- `Champion9.halt`, `Champion9.score_exact` : Jacobzheng's 2024 champion
  `1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_1LB0LH` halts with exactly `Champion9.b2 + 3` ones;
- `new_champion` : both halt, the champion with Nc ones and ours with No ones, and `Nc + 1 < No`
  (standard scores: the champion's 1RZ writes a 1 on a 0, so its score is Nc + 1; ours reads a 1 at the undefined
  I1, so its score is No);
- `new_champion_margin` : `3 * (Nc + 1) < No`, so no convention about the final write matters.

## Check it

    coqc BB9_record_1RB0RA_selfcontained.v        # about an hour on one core; the machine-level lemmas of the halting proof
    coqc probe_selfcontained.v                    # about 3 minutes, same directory

The first command must end with twelve lines `Closed under the global context` (one per `Print Assumptions`
at the end of the file); the only warnings are deprecation notices, three "notation already used" notices for
the champion module's `-->` notations, and LibTactics' `ltac_Mark` notice.  The probe makes Coq re-check, by
conversion, every entry of both transition tables against the machine strings, the exact types of the main
theorems, and prints the definitions behind the statements (`halts`, `halted`, `step`, `c0`, `ones`, `arrow`,
`Bx`, `bp`, `U`, ...) plus `Print Assumptions` for each theorem.

Note on `grep Axiom`: the file contains exactly one `Axiom` declaration, `inj_pair2` in the inlined busycoq
`LibTactics` (verbatim from TLC's LibTactics; it backs the `inverts` tactic).  None of the twelve theorems depends
on it, which is what the twelve `Closed under the global context` lines certify (`Print Assumptions` lists every
axiom a theorem's proof term uses).  LibTactics also defines a `skip`/`demo` tactic notation on top of `admit`;
a proof using it cannot be closed with `Qed`, and the file has no `Admitted`.

## What is in the file

| part | source |
| --- | --- |
| busycoq core: LibTactics, Helper, TM, Compute, Flip, Permute, Individual | [busycoq](https://github.com/meithecatte/busycoq) `verify/`, commit `bd2e36f`, MIT; each file wrapped in `Module BusyCoq_<File> ... End. Export`, verbatim apart from the hoisted `Require` lines |
| 9-state instantiation | `multifile/BB92.v`, `multifile/Individual92.v` (busycoq's `BB52`/`Individual52` with states `A`..`I`) |
| halting proof | `multifile/BB9_record_1RB0RA.v` |
| exact score | `multifile/BB9_record_bound.v` |
| the 2024 champion: halting + exact score | `multifile/BB9_champion_1RB1RA.v`, `multifile/BB9_champion_bound.v`, inside `Module Champion9` |
| comparison | `multifile/BB9_record_vs_champion.v` |
| final section | `ones_agree` (the two `ones` predicates are convertible copies), `new_champion`, `new_champion_margin`, `Print Assumptions` |

The one textual change relative to the multi-file sources is in BB92: `Inductive state := A | ... | St_H | I.` with
`Notation H := St_H.`, because in a single file the constructor `H` would change the hypothesis names Coq invents
(`H`, `H0`, ...) and collide with explicit patterns in the champion's proofs.  `Print tm` still shows `H`.

## The multi-file development (`multifile/`)

The same theorems as separate files on top of a busycoq checkout, plus the twin machine
`..._0RH0RE_0LH1RZ` (`BB9_record_twin_1RB0RA.v`, same run and score, not included in the self-contained file).
Logical paths: `BusyCoq` for busycoq's `verify/` directory and `BB8` for `multifile/` (the files were developed in
a directory registered as `BB8`; the name is historical).  Compile in this order:

    git clone https://github.com/meithecatte/busycoq && (cd busycoq && git checkout bd2e36f && cd verify && make)
    cd multifile
    for f in BB92 Individual92 BB9_record_1RB0RA BB9_record_bound BB9_champion_1RB1RA BB9_champion_bound \
             BB9_record_vs_champion BB9_record_twin_1RB0RA; do
      coqc -Q /path/to/busycoq/verify BusyCoq -Q . BB8 $f.v
    done

Times on one core: the two halting files about 45 minutes each, `BB9_record_bound.v` about 4 minutes, the rest under
a minute each.

## Verification record

`VERIFICATION.txt` and `sha256.txt` are from the from-scratch compile of this exact file with plain `coqc` (no `-Q`,
no other `.vo` on the load path) in a directory containing nothing else, on 2026-10-06: exit 0, 3673 s, twelve
"Closed under the global context"; probe exit 0, 195 s, eight "Closed under the global context".
