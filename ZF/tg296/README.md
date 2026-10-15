# A verified 296-state Turing machine that halts iff ZFC + "every set lies in a Grothendieck universe" is inconsistent

[`machine/m254tg_wade.tm`](machine/m254tg_wade.tm) is a 296-state, 2-symbol Turing machine. Started on a
blank tape, it halts **if and only if ZFC + GU is inconsistent**, where GU says that every set lies in
a Grothendieck universe. This is proved in Coq, end to end, with no axioms:

```
sha256 e9b63d8e07bc505326c8e9ec697890b00cc74e675ce12c451369b208826da071  machine/m254tg_wade.tm
```

The dev-tree copy had CRLF line endings, sha256 1b89758c51ed6eaec9c4581e447c5d74fe2b077270d8c555a1b2d94422c1e520;
the table content is identical.

```coq
(* coq/e2e/E2E_TG.v *)
Theorem tg296_halts_iff_ZFGU   : halts tm c0 <-> (ZFc + GU) ⊢TC ⊥.               (* ZF + GU        *)
Theorem tg296_halts_iff_ZFRGU  : halts tm c0 <-> (ZFc + Reg + GU) ⊢TC ⊥.         (* ZF + Reg + GU  *)
Theorem tg296_halts_iff_ZFCGU  : halts tm c0 <-> (ZFc + AC + GU) ⊢TC ⊥.          (* ZFC + GU       *)
Theorem tg296_halts_iff_ZFCRGU : halts tm c0 <-> (ZFc + Reg + AC + GU) ⊢TC ⊥.    (* ZFC + Reg + GU *)
(* Print Assumptions: Closed under the global context (all four) *)
```

As printed by `coqc` (`check.py` requires exactly these, and the fully qualified statements in the source):

```
tg296_halts_iff_ZFGU
     : halts tm c0 <->
       tprv (fun phi : Core.form => Std_iface.ZFc phi \/ phi = SU_gu.GU) bot
tg296_halts_iff_ZFRGU
     : halts tm c0 <->
       tprv
         (fun phi : Core.form =>
          (Std_iface.ZFc phi \/ phi = MinZF.ax_reg') \/ phi = SU_gu.GU) bot
tg296_halts_iff_ZFCGU
     : halts tm c0 <->
       tprv
         (fun phi : Core.form =>
          (Std_iface.ZFc phi \/ phi = Z_wo.ax_ac) \/ phi = SU_gu.GU) bot
tg296_halts_iff_ZFCRGU
     : halts tm c0 <->
       tprv
         (fun phi : Core.form =>
          ((Std_iface.ZFc phi \/ phi = MinZF.ax_reg') \/ phi = Z_wo.ax_ac) \/
          phi = SU_gu.GU) bot
```

In the source the theories are fully qualified (`ZF.Std_iface.ZFc`, `RegCon.MinZF.ax_reg'`, `ZFC.Z_wo.ax_ac`,
`M254TG.SU_gu.GU`), and `tprv` is the library's `FullND.tprv` at the empty function signature, the ∈/≡
predicate signature, with falsity and classical logic; `bot` is `falsity`.

## What has to be trusted

- `halts`, `c0`: busycoq's TM semantics (`TM.v`; blank tape, start state `0.boot.A`).
- `tm`: the machine as a busycoq `TM` (`coq/tm/ZFTM.v`). The theorem `ZFTM.tm_table`, also closed,
  proves that it agrees row by row with the literal table `tg_table` of `coq/tm/TableTG.v`.
  [`check.py`](check.py) parses `machine/m254tg_wade.tm` independently, checks its sha256 and requires
  `tg_table` to be exactly its table (296 states plus `halt`, 591 transitions).
- `⊢TC`: classical natural deduction (`FullND.tprv`) of the Coq Library of Undecidability Proofs
  (Kirst & Hermes).
- `ZFc`: that library's ZF, with separation and replacement instances universally closed, as in
  [`../m254/`](../m254/) and [`../stdzf_r3/`](../stdzf_r3/).
- `ax_reg'` (`RegCon.MinZF`): foundation, `∀x (∃y y∈x → ∃y (y∈x ∧ ∀z (z∈x → ¬ z∈y)))`.
- `ax_ac` (`ZFC.Z_wo`): Zermelo's choice-set form: every set of nonempty, pairwise disjoint sets has
  a set meeting each member in exactly one element.
- `GU` and `Gru` (`coq/settheory/SU_gu.v`). `GU := ∀x ∃u (x ∈ u ∧ Gru u)`, and `Gru` is a clause-by-clause
  transliteration of Metamath set.mm's definition `df-gru`:

  > ⊢ Univ = {u ∣ (Tr u ∧ ∀x ∈ u (𝒫 x ∈ u ∧ ∀y ∈ u {x, y} ∈ u ∧ ∀y ∈ (u ↑m x) ∪ ran y ∈ u))}

  The comment of `SU_gu.v` gives the reading of every clause: `A ∈ u` for a class term A as
  `∃s (s = A ∧ s ∈ u)` (df-clel), `y ∈ (u ↑m x)` as `y : x ⟶ u` (df-map, df-f, df-fn), with Kuratowski
  pairs and the `Fun0`/`Dom0`/`App0` primitives of `ZFC.Z_base`. A reader has to check this
  transliteration and those primitives.
- The Coq kernel.

Everything else (the register machine, the proof enumerator, the machine's own set theory SUIR, the
interpretations between theories) is internal to the proof.

## Checking it

```
cd ZF/tg296
python3 check.py          # coqc from $COQC, default `coqc` (Coq 8.20.x)
```

`check.py`:
- refuses `Admitted`/`admit`/`Axiom`/`Parameter`/`Conjecture` outside comments in `coq/`;
- checks the sha256 of `machine/m254tg_wade.tm` and that `TableTG.v` is exactly its table;
- checks that the generated files reproduce: Wade's TMBuilder ([`../generator/`](../generator/),
  unmodified) compiles [`machine/source_tg.py`](machine/source_tg.py) to `m254tg_wade.tm`
  ([`machine/build_tm.py`](machine/build_tm.py); byte for byte on Linux and macOS, up to line
  terminators on Windows), and [`tools/gen_tm_coq.py`](tools/gen_tm_coq.py) and [`tools/gen_prog.py`](tools/gen_prog.py)
  regenerate `DagTG.v`, `TableTG.v`, `NamesTG.v` and the generated regions of `ProgLibTG.v`;
- compiles the whole dependency closure of `coq/e2e/E2E_TG.v` from source (176 files);
- requires the four statements above, four `Closed under the global context` in `E2E_TG.v`, and the
  statement of `ZFTM.tm_table`, also closed;
- prints `CHECK PASS` or `CHECK FAIL`.

It uses the vendored library and busycoq, `ZF` (`../stdzf/coq`), `RegCon` and `ZFC` (`../stdzf_r3/`), and
two roots of [`../m254/`](../m254/): `M254L` (`../m254/coq/logic`: the formula coding `Codes254`,
`Wff254` and side lemmas of `Bundle254`) and `M254S` (`../m254/coq/settheory`: the nonextensional
toolkit of the 254-state proof). CI job: `zf-tg296`.


## Proof structure

| Layer | Directory | Statement |
|---|---|---|
| TM ↔ register machine | [`coq/tm/`](coq/tm/) | `tmtg_rm : halts tm c0 <-> rm_halts dagtg ([], regs0)` |
| register machine ↔ enumerator | [`coq/prog/`](coq/prog/) | `progtg : rm_halts dagtg ([], regs0) <-> enum_tg_halts` |
| enumerator ↔ the machine's calculus ↔ SUIR | [`coq/logic/`](coq/logic/) | `enum_tg_SUIR : enum_tg_halts <-> SUIR ⊢TC ⊥` |
| SUIR ↔ ZF + GU (and + Reg) | [`coq/settheory/`](coq/settheory/) | `SU_equicons : SUIR ⊢TC ⊥ <-> (ZFc + GU) ⊢TC ⊥` |
| ZF + GU ↔ ZFC + GU (and + Reg) | [`coq/ac/`](coq/ac/) | `ZFCGU_equicons`, `ZFCRGU_equicons` |

- **TM layer.** `dagtg` is the decision DAG of Wade's TMBuilder compile (234 nodes, 9 registers),
  extracted from the `.tm` file. A list-zipper simulation over symbolic tapes shows that the machine runs
  the register machine's path semantics; the boot is checked by computation.
- **Program layer.** Ported from the 254-state proof: one run of `main()` is one step of the abstract
  enumerator `EnumTG.enum_step`, proved symbolically. The symbolic run of `axioms()` concludes with
  `CodesTG.bundle_tg`, so Coq checks that the compiled code builds exactly the new axiom bundle, for
  symbolic parameters.
- **Logic layer.** The 254-state calculus with the new bundle. Soundness: every stack entry is valid in
  SUIR, including every label collision the machine's freshness gate leaves open. Completeness: every
  SUIR axiom instance is produced by the bundle.
- **Set-theory layer.** (ZF + GU → SUIR) the bisimulation-quotient interpretation of the 254-state proof,
  plus a proof that the quotient of a raw UG' container is a weak universe, and that weak universes are
  Grothendieck universes in ZF. (SUIR → ZF + GU) SUIR is relativized to `⋃_α V_α` inside ZF + Reg + GU;
  the container w for a set p is `V_κ`, with κ = U ∩ On for a universe U that contains the rank of p. Reg is then removed by extending
  [`../stdzf_r3/regcon`](../stdzf_r3/regcon)'s well-founded relativization by the axiom GU.
- **AC layer.** ZF + Reg + GU proves (AC + GU)^L, via Gödel's L as in [`../stdzf_r3/zfc`](../stdzf_r3/zfc).
  The new part is (GU)^L: for a universe U, L_κ (κ = U ∩ On) is a universe in L, which needs the
  condensation lemma (Skolem hulls in L_α and the Mostowski collapse), formalized here.

Design notes for each layer are in [`design/`](design/).

## The axiom the machine searches

The machine is Mira-Cult's 254-state program with one change: in its axiom bundle, the container and
collection clauses `C ∧ G'` are replaced by one schema UG'_φ. φ has an input a, an output y, and one
designated inner variable f; all its other parameters are outer.

```
UG'_φ := ∀p ∃w [ p∈w ∧ ∀x∈w ( x⊆w ∧ ∃W∈w ∀z (z⊆x → z∈W) )
           ∧ ∀f ∀B∈w ∃C ( ∀a∈B ∀y (φ(a,y,f) → ∃y' (φ(a,y',f) ∧ y'∈C))      (collection)
                        ∧ ∀y∈C ∃x φ(x,y,f)                                     (C is an image)
                        ∧ ( ∀a∈B ∃y (y∈w ∧ φ(a,y,f)) → ∃U∈w ∀y∈C ∀z∈y z∈U ) ) ]  (union bound)
```

w is transitive and has power containers; collection is relativized to w by the last clause. The
machine's theory SUIR is: the equality axioms, all closed instances of UG'_φ, and irreflexivity `∀x ¬x∈x`
(which, as in the 254-state machine, makes the alias code for falsity sound).

**The relation variable must be bound after w.** The first design had no f: φ and all its parameters
were fixed before `∃w`, and the last clause concluded `C ∈ w`. Every instance of that schema is a
theorem of ZF, by reflection: take w = V_α for a limit α that contains p and the parameters and reflects
φ, `∃y φ(a,y)` and the collection statement; then the collection witness can be taken inside V_α, so
`C ∈ w` is free. The schema would then be equiconsistent with ZF, and the machine would only search for
a ZF contradiction. Binding f after w (∀f inside ∃w) makes the clause speak about relations that w does
not know in advance, which is what forces w to be a universe.

**The union bound.** Binding f after w is not enough with the conclusion `C ∈ w`: transitivity, power
containers and bounded images do not give closure under unions. (In ZFC, let κ be a singular strong
limit, λ = κ⁺, and w = {x ∈ V_λ : every y ∈ TC({x}) has |y| < κ}. Then w is transitive and has power
containers and bounded images, and it contains a cofinal ω-sequence S ⊆ κ, but ∪S = κ ∉ w.) The
conclusion `∃U∈w ⋃C ⊆ U` supplies the union.

The machine-level formula, the order of its conjuncts, and the analysis of every label collision the
freshness gate `c ≠ a, b` allows are in [`design/machine.md`](design/machine.md).

## Provenance

- The program is **Mira-Cult's** (mike29936; [github.com/Mira-Cult/turing-machines](https://github.com/Mira-Cult/turing-machines))
  ZFC254 design: the proof enumerator, the formula coding, the eight logical rows, MP/DROP/NIP and the
  freshness gate are theirs, unchanged. Its verification is in [`../m254/`](../m254/), and most of this
  proof is a port of that one.
- Only the axiom bundle is new. [`machine/source_tg.py`](machine/source_tg.py) is the author's
  `source.py` with the bundle slice of `axioms()` replaced.
- The author's 254 states come from their own backend (a single-marker interpreter with state merges),
  which was not available to us. We compiled with Andrew Wade's TMBuilder
  (codeberg.org/ajwade/turing_machine_explorer), the compiler of [`../generator/`](../generator/).
  Under TMBuilder the unchanged 254-state program compiles to 281 states and the new one to **296**.
  So the new bundle costs about 15 states, and the gap to 254 is the backend.
- The order of the conjuncts and the variable labels were chosen by search over 3,072 orders
  ([`tools/machine/`](tools/machine/): `gen.py`, `search2.py`; `gen.py` needs the author's `source.py`,
  which is not redistributed here). `validate.py` checks the program against the reference enumerator
  `spec.py` on random states, and `collide2.py` enumerates the label collisions.

## Scope

- ZFC + GU is Tarski–Grothendieck set theory in strength: it is equivalent to ZFC + "there is a proper
  class of inaccessible cardinals". Reg and AC do not change the halting condition (the theorems above).
- **Not formalized:** consequences for type theory. Voevodsky's simplicial model, as written up by
  Kapulkin and Lumsdaine ("The simplicial model of univalent foundations (after Voevodsky)", J. Eur.
  Math. Soc. 23 (2021)), and extended to higher inductive types by Lumsdaine and Shulman ("Semantics of
  higher inductive types", Math. Proc. Cambridge Philos. Soc. 169 (2020)), interprets homotopy type
  theory with univalent universes, LEM and AC in ZFC with inaccessibles, and so in ZFC + GU. With the
  theorem above it follows on paper that, if ZFC + GU is consistent, HoTT + LEM + AC cannot prove that
  this machine runs forever. That step rests on those papers; nothing about type theory is checked
  here.
