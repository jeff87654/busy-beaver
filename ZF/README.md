# ZF/ — verified Turing machines that halt iff ZF proves a contradiction

Coq proofs that three 2-symbol Turing machines, started on a blank tape, halt **if and only if** a
Hilbert-style formalization of ZF set theory (O'Rear's system `prov`) proves `v_0 e. v_0`:

```coq
Theorem zf_machine : halts tm c0 <-> prov (Wel v0 v0).
(* Print Assumptions zf_machine:  Closed under the global context *)
```

[`stdzf/`](stdzf/) then connects `prov` to the standard formalization of ZF in the Coq Library of
Undecidability Proofs (Kirst & Hermes). For the 354-state machine it proves end to end, in a single
build:

```coq
Theorem zf354_halts_iff_ZF     : halts tm c0 <-> ZFc ⊢TC ⊥          (* ZF, schemas universally closed *)
Theorem zf354_halts_iff_ZF_reg : halts tm c0 <-> (ZFc + Reg) ⊢TC ⊥  (* ZF with regularity *)
(* plus the same for the library's function-symbol signature; all closed, no axioms *)
```

So the 354-state machine halts iff ZF is inconsistent, with or without regularity. No paper argument
remains; see [`stdzf/README.md`](stdzf/README.md).

| machine | states | origin | proof |
|---|---|---|---|
| [`machines/zf2.tm`](machines/zf2.tm) | 393 | Andrew Wade's machine, unchanged | [`verify/393/`](verify/393/) |
| [`machines/A361.tm`](machines/A361.tm) | 361 | Wade's framework; reworked program, same formal system | [`verify/361/`](verify/361/) |
| [`machines/B354.tm`](machines/B354.tm) | **354** | as A361, plus equivalent rewrites of EXT, REP and INF | [`verify/354/`](verify/354/) |

All three machines search the same formal system. `Logic.v` is byte-identical in the three proofs.

## Background

The machine in this lineage has always been O'Rear's proof enumerator:
- the logic is Tarski's system S2 with O'Rear's modifications, plus the ZF axioms EXT, REP, POW, UNI
  and INF;
- wffs and proofs are encoded as Cantor-paired integers;
- the program builds every candidate proof and halts when it derives `v_0 e. v_0`.

Over the years it was compiled to successively smaller Turing machines:
- Yedidia and Aaronson, 7910 states (2016);
- Stefan O'Rear's NQL compiler, 1919 and then 748 states (2016);
- Johannes Riebel, 745 states (2023);
- Rohan Ridenour, 643 and then 636 states (2024);
- Andrew Wade, 588, 549 and 432 states (2025), with the 432-state machine listed on the bbchallenge wiki;
- Wade's current `turing_machine_explorer` repository
  (<https://codeberg.org/ajwade/turing_machine_explorer>, MIT No Attribution), which compiles the
  program to 393 states.

As far as we know, none of these machines had been formally verified before.

- **393:** `machines/zf2.tm` is Wade's `zf2.tm` unchanged. Rebuilding it from his `zf2.py` with the axiom
  order in his README reproduces it byte for byte.
- **361 (A361):** keeps Wade's framework and compiler and changes only the program:
  - the duplicated B6b and B8b clauses are removed;
  - each axiom clause's parameter roles are permuted, with the permutation found by search;
  - DET pops straight into a scratch register;
  - the B6a distinctness test consumes its inputs;
  - wff constructors tag by pairing directly;
  - push and select share one pair/unpair instance;
  - the equality test no longer uses a level-2 break;
  - the dispatch chain is capped at 7.
- **354 (B354):** A361 plus rewrites of the axiom text inside the program. EXT and REP have `/\`, `<->`
  and `=` commuted, and INF has its variables renamed. `verify/354/L1_B354.v` proves in pure
  first-order logic that each rewritten axiom and its original are interderivable. So the machine
  searches a system with exactly the same theorems, and the trusted `Logic.v` is unchanged.

[`generator/`](generator/) rebuilds `A361.tm` and `B354.tm` byte for byte with `python mkcand.py A361.json A361`.
The generator is Wade's `TMBuilder.py`/`zf2.py` (unmodified) plus our program `zfp.py`.

## Checking

Build busycoq (<https://github.com/meithecatte/busycoq>, commit `bd2e36f`, Coq 8.20.1) far enough to have
`TM.vo`, then:

```
cd ZF/verify
BUSYCOQ=/path/to/busycoq/verify python3 check.py 354      # or 361, 393
```

`check.py` does three things:
1. It parses the `.tm` file independently and checks that the literal table `zf2_table` in
   `ZF2Dag.v` is exactly its transition table.
2. It compiles the proof.
3. It checks the statement of `zf_machine` and that `Print Assumptions` reports no axioms.

A full check takes about 5–12 minutes per machine. CI runs all three; see `.github/workflows/coq.yml`.

### What has to be trusted

- **busycoq's `TM.v`:** the definitions of `step`, `halts` and `c0`, the same ones used by the BB(5)
  proof and by `BB8/`–`BB10/` here.
- **The machine:** `ZFTM.v` defines `tm` and proves by computation (`tm_table`) that, for every state
  and symbol, `tm` gives exactly the transition listed in `zf2_table`. That includes the halting
  entries, so `zf2_table` has no extra or missing rows. `check.py` ties `zf2_table` to the `.tm` file.
- **The formal system:** `Logic.v`, about 100 lines. `prov` has the rules DET and GEN, the logical
  axioms B1–B4, B6a–B6c, B7 and B8a–B8c, and EXT, REP (a schema), POW, UNI and INF. Compare them with the
  header of O'Rear's [`zf2.nql`](https://github.com/sorear/metamath-turing-machines/blob/master/machines/2017-zf-sorear-748/zf2.nql).
  `E.` and `/\` are abbreviations.
- **Coq itself:** the Coq 8.20.1 kernel, including the `vm_compute` reduction machine. The table check,
  the boot run, the IP-space prefix and the DAG well-formedness checks are proofs by computation.

### The system versus standard ZF (formalized in `stdzf/`)

On its own, `zf_machine` is about `prov` exactly as defined in `Logic.v`. Earlier machines in this
lineage relied on two paper arguments to read it as "halts iff ZF is inconsistent": that `prov` is no
stronger than ZF, and that it is complete enough to reach ZF − Reg − AC (completeness of O'Rear's
Tarski-S2 variant, fixed-variable axioms, sharp REP). [`stdzf/`](stdzf/) replaces both with Coq
theorems:

- `prov (Wel v0 v0) <-> ZFc ⊢TC ⊥`, where `ZFc` is the minimal-signature ZF of the Coq Library of
  Undecidability Proofs with its separation/replacement instances universally closed. This is the
  library's own semantic axiom set. Its deductive theory leaves the instances open, and treats their
  parameters as constants.
- The same with regularity added (`ZFc + Reg`): the relative consistency of regularity, proved by
  relativizing derivations to the class of well-founded sets.
- The same for the library's function-symbol signature.
- One direction for the library's theories exactly as written: `minZFeq ⊢TC ⊥ -> prov (Wel v0 v0)`.

For the 354-state machine, `stdzf/endtoend/354/` compiles the machine proof and these theorems in one
namespace, so `halts tm c0 <-> ZFc ⊢TC ⊥` holds directly and `Logic.v` is only an internal
intermediate. The trust surface for that statement is described in `stdzf/README.md`. Only the
translation of "ZF is inconsistent" into this particular classical natural-deduction calculus remains
informal; all standard complete calculi agree on it.

### Proof structure (each `verify/N/`)

| layer | files | statement |
|---|---|---|
| TM ↔ register machine | `ZFTM.v`, `Sim*.v` | `halts tm c0 <-> rm_halts zf2 ([], regs0)` |
| path ↔ big-step semantics | `RM.v`, `RMEquiv.v` | `wf p -> rm_halts p ([], R) <-> iter_halts p R` |
| program ↔ abstract enumerator | `ZF2Dag.v`, `ProgLib.v`, `Prog.v` | one run of the root = one `enum_step` |
| enumerator ↔ provability | `Logic.v`, `Enum.v`, `L1*.v` | `enum_halts <-> prov (Wel v0 v0)` |
| assembly | `MainGlue.v`, `Main.v` | `zf_machine` |

Notes on the TM layer:
- The machine runs a boot of about 39,800 steps, then interprets Wade's register machine.
- Each dispatch cycle (select, inc, decnz on nonzero and on zero, break, continue, halt) is proved once,
  over symbolic register files.
- Wade's README warns that his framework never checks that the instruction pointer fits in front of
  the register file. Lemma `ip_space` proves that it always does: the first few hundred
  register-machine steps are computed, and after that, the decrements already executed guarantee
  enough space.

Notes on the logic layer:
- Soundness uses a decoder that is total on all numbers: every number decodes to some wff, and junk
  decodes to `v0 = v0`. This is needed because the machine really does push numbers that are not
  codes of any wff.
- Completeness compiles any derivation into the machine's proof encoding.

[`tools/`](tools/) has an independent Python simulator (`tmsim.py`), a DAG extractor and
register-machine simulator (`dag.py`), the TM-vs-register-machine cross-checker (`crosscheck.py`) and
the generator of `ZF2Dag.v` (`gen_coq_dag.py`).

## Credits

- **Stefan O'Rear:** the formal system, the encodings and the original NQL program.
- **Andrew Wade:** the `TMBuilder` framework and compiler and the 393-state machine. Every machine here
  is built with his compiler.
- **Rohan Ridenour, Johannes Riebel, CatsAreFluffy:** earlier improvements.
- **Maja Kądziołka:** busycoq.
