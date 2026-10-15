# TM layer (coq/tm, root M254TGT)

Proved with no axioms (`Print Assumptions` reports "Closed under the global context"):

```coq
Theorem tmtg_rm  : halts tm c0 <-> rm_halts dagtg ([], regs0).          (* MainTM.v *)
Theorem tm_table : (forall q b, table_lookup tg_table (name q) b = row_of (tm (q, b))) /\ ...
                   /\ name q0 = "0.boot.A" /\ s0 = false
                   /\ length all_states = 297 /\ length tg_table = 591.   (* ZFTM.v *)
```

* `tg_table` (TableTG.v) is the literal transition table of `machine/m254tg_wade.tm` (296 states plus
  `halt`, 591 transitions). `check.py` parses the `.tm` file independently and requires equality.
* `tm` (ZFTM.v) is a busycoq `TM` defined structurally, following `TMBuilder.generate`: the fixed
  framework states (boot, register operations `1.*`, returns `2.*`, `5.root`), the dispatch states
  `4.dispatch.(i+1)`, `6.break.k`, `6.continue.k`, the per-register states `3.<r>.inc/.decnz`, one state
  per decision-DAG node of `dagtg`, and `halt`. `tm_table` checks by `vm_compute` that `tm` and
  `tg_table` agree row by row, and that the naming is injective, so the theorems about `tm` are about
  the file.
* `dagtg` (DagTG.v) is the decision DAG of the Wade compile (234 nodes, 9 registers in declaration
  order), extracted from the `.tm` file by `tools/gen_tm_coq.py` (with `ZF/tools/dag.py`).
* `rm_halts` is the path semantics of Wade's register machine (RM.v, as in `ZF/verify/336`), and
  RMEquiv.v relates it to the structured big-step semantics used by the program layer, under the
  decidable well-formedness `dagtg_wf`.

## Proof (Sim.v and its parts)

The simulation is a list-zipper argument over symbolic tapes, as for the 335-state machine.

* SimBase.v: `zc q l r` / `zl q l r` configurations on busycoq tapes; scanning lemmas.
* SimOps.v, SimRegs.v: the register operations `1.sel / 1.inc / 1.decnz` with the return scans, on
  symbolic register files `sepsR vs` (each register `1^(v+1)` after a single `0`).
* SimIP.v: IP arithmetic: the dispatch scan back to `main().0`, `6.break.k`, `6.continue.k`.
* SimDag.v: static facts about `dagtg` by `vm_compute`, and the bound showing that the IP gap
  (which grows by one per executed decnz) always leaves enough space.
* SimBoot.v: the boot phase, by certified computation.
* Sim.v: dispatch configurations `P 1^j 0^g R-file`; one RM step is simulated by finitely many TM
  steps, a register operation on register r taking r+2 dispatch cycles. Main theorem
  `tm_halts_iff_rm`; MainTM.v restates it as `tmtg_rm`.
