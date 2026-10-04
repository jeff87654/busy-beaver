# Coq proofs for `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_1LC0RH_1RG1LF`

Built on [busycoq](https://github.com/meithecatte/busycoq) at commit `bd2e36f` with Coq 8.20.1
(Coq Platform 2025.01). The files use the logical path `BusyCoq` for busycoq's `verify/` directory
and `BB8` for this directory.

| file | content |
|---|---|
| `BB82.v` | busycoq's `BB52.v` with 8 states `A`..`H`; nothing else changed |
| `Individual82.v` | busycoq's `Individual52.v` with 8 states |
| `BB8_champ35_1RB0RA.v` | the machine `tm` (E0 = `None`, the halt), the digit family `Kc`, rules `R1`-`R4`, the lexicographic termination argument, the literal start-up lemma `init_reach` (6397 steps), and `Theorem halt : halts tm c0` |
| `BB8_champ35_bound.v` | `ones c N` (exactly N ones on the tape of c), Knuth's `arrow k a b`, the exact clearing functions `U j`, `score_exact` (N = 24 bf + 106 with bf = U 34 (U 34 0)), `sigma_lower_bound` (`arrow 11 2 (arrow 11 2 3) < N`), `sigma_lower_bound_strong` (`arrow 35 2 (arrow 35 2 3) < N`), `sigma_gt_arrow36` |
| `BB8_champ35_exact.v` | `U_closed` (2 U j x + 4 = arrow (S j) 2 (2x+4)), `bf_closed` (2 bf + 4 = arrow 37 2 3), `score_closed` (N = 12 * arrow 37 2 3 + 58), `sigma_gt_arrow37` |
| `probe.v` | re-checks every statement above against its literal form and prints the assumptions |

busycoq stops before the halting transition (E0 is `None`), so N counts the ones before the final
write and the standard score is N + 1 = 12 * (2 ↑^37 3) + 59.

## Compiling

    git clone https://github.com/meithecatte/busycoq && (cd busycoq && git checkout bd2e36f && cd verify && make)
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

or by hand, in this directory and in this order:

    coqc -Q /path/to/busycoq/verify BusyCoq -Q . BB8 BB82.v
    coqc -Q /path/to/busycoq/verify BusyCoq -Q . BB8 Individual82.v
    coqc -Q /path/to/busycoq/verify BusyCoq -Q . BB8 BB8_champ35_1RB0RA.v      # about 8 minutes
    coqc -Q /path/to/busycoq/verify BusyCoq -Q . BB8 BB8_champ35_bound.v       # about 20 s
    coqc -Q /path/to/busycoq/verify BusyCoq -Q . BB8 BB8_champ35_exact.v       # about 30 s
    coqc -Q /path/to/busycoq/verify BusyCoq -Q . BB8 probe.v

`probe.v` prints the transition table of `tm`, the definitions of `arrow` and `ones`, the five
statements, and five times `Closed under the global context` (no axioms, no `Admitted`).
`compile_clean.log` is the output of `compile_clean.sh` on the author's machine.

A note for anyone extending these files: `arrow`, `U` and `bf` are declared `Opaque`, but a tactic
that asks the unifier to compare two *different* closed terms such as `arrow 37 2 3` and
`arrow 35 2 (arrow 35 2 4)` still makes Coq evaluate them (it never finishes). Use fully
instantiated rewrites and `generalize` the closed term before calling `lia`, as `BB8_champ35_exact.v` does.
