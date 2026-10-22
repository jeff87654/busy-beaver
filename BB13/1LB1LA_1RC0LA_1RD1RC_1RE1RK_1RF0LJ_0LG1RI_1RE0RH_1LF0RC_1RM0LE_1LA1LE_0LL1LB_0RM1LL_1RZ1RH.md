# M13: a 13-state machine at level f_(ω+2)

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_0LG1RI_1RE0RH_1LF0RC_1RM0LE_1LA1LE_0LL1LB_0RM1LL_1RZ1RH

Below we call this machine **M13**. It halts from the blank tape. Coq proves its exact number of ones at the halt as
an explicit recursion, and proves that its score exceeds f_(ω+2)(f_ω(20)) in the standard fast-growing hierarchy.
The machine keeps four numbers on the tape: a level p, an argument a and two counters c and d. A single rule
computes a fast-growing function W_j whose index j is the level p. Because p grows with each step, this rule is at
level ω. The counter c gives level ω+1 and the counter d gives level ω+2. M13 and both Coq proofs were found and
written by Argon, a Google Gemini model (section 5). Written 2026-10-14.

|   | 0   | 1   |                       |
|---|-----|-----|-----------------------|
| A | 1LB | 1LA |                       |
| B | 1RC | 0LA |                       |
| C | 1RD | 1RC |                       |
| D | 1RE | 1RK |                       |
| E | 1RF | 0LJ |                       |
| F | 0LG | 1RI |                       |
| G | 1RE | 0RH |                       |
| H | 1LF | 0RC |                       |
| I | 1RM | 0LE |                       |
| J | 1LA | 1LE |                       |
| K | 0LL | 1LB |                       |
| L | 0RM | 1LL |                       |
| M | 1RZ | 1RH | M0 is the halt        |

The machine moves left on its first step. The bbchallenge convention has A0 = 1RB. With left and right swapped, the
same machine in that form is
`1RB1RA_1LC0RA_1LD1LC_1LE1LK_1LF0RJ_0RG1LI_1LE0LH_1RF0LC_1LM0RE_1RA1RE_0RL1RB_0LM1RL_1RZ1LH`. The simulator of
section 4.3 checks this form.

**Main facts.** N is the number of 1s on the tape when M reads 0. The halting transition writes a 1 on that 0, so the
standard score is σ = N + 1.

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms). |
| Exact score | Machine-checked formula: N = p₂ + a₂ + 5, where (p₂, a₂) = pa2 is given by the recursion of section 1. So σ = p₂ + a₂ + 6. It is not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+2)(f_ω(20)) < N + 1 = σ. |
| T12a (BB12/) | Beaten, on paper (section 3.3). |
| BB(14)–BB(16) | M13's proved lower bound exceeds the published lower bounds, on paper (section 3.3). |
| Steps | Not computed. |

---

## 1. How it works

### 1.1 Notation

- `0^∞` is the blank part of the tape, and `x^n` is n copies of the word x.
- `C>` means state C with the head on the cell to its right. `<A` means state A with the head on the cell to its
  left.
- In the Coq files, `l {{q}}> r` has the head on the first cell of r, and `l <{{q}} r` has the head on the first cell
  of l. The left side l is listed outward from the head. So `[1]^^b *> [0; 1]^^j *> const 0` on the left of the head
  is the word `0^∞ (10)^j 1^b` read left to right.
- A **block** is the word `10`.

The configurations are the Coq definitions `Ca`, `Ch`, `Ce`, `blk` and `c_end` of
[`BB13_M13.v`](verify/multifile/BB13_M13.v). z is an arbitrary right part.

| Coq | tape |
|---|---|
| `Ca j b z` | `0^∞ (10)^j 1^b C> 0 z` |
| `Ch j b z` | `0^∞ (10)^j <A 1^(b+1) 0 z` |
| `Ce p a c d` | `0^∞ (10)^p 1^(a+2) E> (10)^c 0 1^d 0^∞` |
| `blk a z` | `1^(a+1) 0 z` |
| `c_end p a` | `0^∞ (10)^p 1^(a+5) M> 0^∞` |

In `Ch`, the head reads the last cell of `(10)^j`, a 0. If j = 0, it reads a blank.

"X → Y" below means that the machine goes from X to Y in at least one step (Coq's `-->+`), and "→*" allows zero
steps.

### 1.2 The engine: the functions W_j

W is defined in Coq by

    W_0(b) = b + 3,        W_(j+1)(b) = W_j^(b+1)(2),

where g^n is g applied n times. So W_1(b) = 3b + 5 and W_2(b) = (27·3^b − 5)/2. W_3(0) = 119, and
W_3(1) = W_2(119) = (3^122 − 5)/2 has 58 digits. In `Ca` and `Ch`, the number j of blocks left of the head is the
index, and the run of 1s is the argument. The rules:

| Coq | rule |
|---|---|
| `CA_SH` | `Ca j b (10 z)` → `Ca (j+1) b z` |
| `CA_SH_iter` | `Ca j b ((10)^k z)` →* `Ca (j+k) b z` |
| `CA_CH` | `Ca j b (11 y)` → `Ch j b (1 y)` |
| `CA_EXIT` | `Ca j b (0 z)` → `0^∞ (10)^j 1^(b+2) E> z` |
| `CH_0` | `Ch 0 b z` → `Ca 0 (b+3) z` |
| `CH_S` | `Ch (j+1) b z` → `Ca j 2 (blk (b+1) z)` |
| `BLK_iter_aux` | if the `CH_CA` rule holds at index j: `Ca j b (blk a z)` → `Ca (j+1) (W_j^a(b)) z` |
| `CH_CA` | `Ch j b z` → `Ca j (W_j(b)) z` |

How `CH_CA` works, by induction on j:
- At index 0, `CH_0` adds 3 to the argument.
- At index j + 1, `CH_S` removes one block from the left and resets the argument to 2. The old argument b is left on
  the right as the word `1^(b+2) 0`.
- C then reads that word from the left (`BLK_iter_aux`). Each pair `1 1` in front of it starts one call of `Ch` at
  index j (`CA_CH`), which replaces the argument x by W_j(x) and uses up one 1. There are b + 1 such calls.
- The final `1 0` becomes a block again on the left (`CA_SH`), so the index is back to j + 1.
- The result is W_j^(b+1)(2) = W_(j+1)(b).

Coq also proves W_j(b) ≥ b + 3 (`W_grow`) and W_j(b) ≡ b + 1 (mod 2) (`W_par`). In particular W_j(1) is always even.

### 1.3 The four numbers

In `Ce p a c d`:
- p is the **level**: the number of blocks left of the head;
- a is the **argument**. It is even throughout the run;
- c is the **inner counter**: the number of blocks right of the head;
- d is the **outer counter**: the length of the run of 1s at the right end.

The rules on `Ce`:

| Coq | rule | when |
|---|---|---|
| `CE_EVEN` | `Ce (p'+1) (2k) (c+1) d` → `Ce (p'+k+1) (W_p'(1)) c d` | c > 0 |
| `C_REL` | `Ce (p'+1) (2k) 0 (d+2)` → `Ce p' 2 (k+1) d` | c = 0, d ≥ 2 |
| `D_REL` | `Ce (p'+2) a 0 0` → `Ce p' 2 1 (a+1)` | c = d = 0 |
| `HALT_step` | `Ce p a 0 1` → `c_end p a` | c = 0, d = 1 |

- **`CE_EVEN`** uses up one block of c. E turns the run `1^(2k+2)` into k + 1 blocks on its right and ends in
  `Ch p' 1`. `CH_CA` computes W_p'(1), and the k + 1 new blocks are then absorbed into the level (`CA_SH_iter`).
- **`C_REL`** fires when c is empty. It takes 2 from d, turns the argument into a new inner counter c = a/2 + 1,
  resets a to 2, and lowers the level by 1.
- **`D_REL`** fires when c and d are both empty. It reloads the outer counter with d = a + 1, sets c = 1, resets a to
  2, and lowers the level by 2.
- **`HALT_step`** ends the run. When c is empty and d = 1, the machine reaches `c_end p a`, where M reads 0 and halts
  (`c_end_halted`).

### 1.4 The pair maps

Coq follows (p, a) through four maps (division rounds down):

    Kc(p, a)       = (p + a/2,  W_(p−1)(1))         one CE_EVEN step
    Kd_step(p, a)  = Kc^(a/2+1)(p − 1, 2)           C_REL, then a/2 + 1 Kc steps
    Kd_iter(m, pa) = Kd_step^m(pa)
    D_reload(p, a) = Kc(p − 2, 2)                   D_REL, then one Kc step

and proves the matching runs:

| Coq | run | hypotheses |
|---|---|---|
| `Kc_step` | `Ce p a (c+1) d` → `Ce Kc(p,a) c d` | p ≥ 1, a even |
| `Kc_loop` | `Ce p a c d` →* `Ce Kc^c(p,a) 0 d` | p ≥ 1, a ≥ 2 even |
| `Kd_step_all` | `Ce p a 0 (d+2)` → `Ce Kd_step(p,a) 0 d` | p ≥ 2, a ≥ 2 even |
| `Kd_loop` | `Ce p a 0 (2m+r)` →* `Ce Kd_iter(m,(p,a)) 0 r` | p ≥ 2, a ≥ 2 even |
| `D_reload_all` | `Ce p a 0 0` → `Ce D_reload(p,a) 0 (a+1)` | p ≥ 3, a ≥ 2 even |

`Kc_loop`, `Kd_step_all` and `Kd_loop` also prove that afterwards the level has not fallen, a ≥ 2 and a is even
(a is always 2 or a value W_j(1), which is even). `D_reload_all` lowers the level by 1, and proves p ≥ 2, a ≥ 2 and
a even afterwards, which are the hypotheses of `Kd_loop`. Here `Ce (p, a) c d` stands for `Ce p a c d`.

### 1.5 Why the outer counter is reloaded exactly once

- Every Kd step takes 2 from d.
- If d is even, it reaches 0, and `D_REL` reloads it with d = a + 1. Since a is even, the new d is odd.
- If d is odd, it reaches 1, and `HALT_step` ends the run.
- The run reaches its first `C_REL` with d = 2, which is even. So d is reloaded once, at the end of round 1. Round 2
  then counts the odd d down to 1, and the machine halts.

### 1.6 Where each level comes from

- **Level ω: Kc.** A Kc step sets a to W_(p−1)(1), so the index of W is the current level. It also raises the level
  by a/2, so the next index is set by the last value. Coq: W_(m+3)(1) ≥ 4·f_ω(m+1) + 4 (`W_omega_bound`), and
  two Kc steps take the level p to at least f_ω(p − 3) + 4 (`Kc_dom2`).
- **Level ω+1: Kd_step.** One Kd step makes a/2 + 1 Kc steps, a number set by the current argument.
- **Level ω+2: round 2.** Round 2 makes a₁/2 Kd steps, where a₁ is the argument at the end of round 1.

Section 3.1 gives the exact Coq statements.

---

## 2. The run

| | configuration | how | Coq |
|---|---|---|---|
| 0 | blank tape, state A | | |
| 1 | `Ce 1 2 2 2`, at step 116 | 116 single steps | `init_116` |
| 2 | `Ce 2 4 1 2`, at step 162 | Kc | `CE_EVEN` |
| 3 | `Ce 4 8 0 2`, at step 306 | Kc | `init_306` |
| 4 | `Ce 3 2 5 0`, at step 328 | `C_REL`: round 1 is this one Kd step | `Kd_step_all` |
| 5 | `Ce 4 38 4 0`, at step 1364 | Kc | |
| 6 | `Ce 23 W_3(1) 3 0` | Kc | |
| 7 | `Ce p₃ W_22(1) 2 0`, p₃ = 23 + (3^122 − 5)/4 | Kc | |
| 8 | `Ce pa1 0 0`, pa1 = Kd_step(4, 8) = Kc^5(3, 2) | two more Kc | `run_pa1` |
| 9 | `Ce pa2_0 0 (a₁ + 1)`, pa2_0 = D_reload(pa1) | `D_REL`, then one Kc | `D_reload_all` |
| 10 | `Ce pa2 0 1`, pa2 = Kd_iter(a₁/2, pa2_0) | a₁/2 Kd steps (round 2) | `Kd_loop`, `run_round2` |
| 11 | `c_end pa2`: M reads 0, the halt | `HALT_step` | `run_pa2`, `halt` |

Here pa1 = (p₁, a₁). The step numbers come from the simulator of section 4.3. The 116 steps of `init_116` are also
in the Coq proof, as `do 116 step`. Coq does not compute rows 5–7; they are the values of the recursion. After row 5
the tape is too long to simulate: W_3(1) has 58 digits. The total number of steps has not been computed.

---

## 3. The score

### 3.1 What Coq proves

From [`verify/multifile/BB13_M13_bound.v`](verify/multifile/BB13_M13_bound.v):

- `score_exact`: the halting configuration holds exactly fst pa2 + snd pa2 + 5 ones. It is `c_end pa2`, and its tape
  is `(10)^p₂ 1^(a₂+5)`.
- `sigma_lower_bound_strong`: the halting tape holds N ones with f_(ω+2)(f_ω(20)) < N + 1.
- `sigma_lower_bound`: the same with f_(ω+2)(20) in place of f_(ω+2)(f_ω(20)).

The hierarchy is defined at lines 70–78:
- f_0(n) = n + 1 and f_(k+1)(n) = f_k^n(n);
- f_ω(n) = f_n(n), f_(ω+1)(n) = f_ω^n(n) and f_(ω+2)(n) = f_(ω+1)^n(n).

The proof of the strong bound:
1. **W against f_j.** If 2^(j+1)·n ≤ z, then 2^(j+1)·f_(j+1)(n) ≤ W_(j+1)(z) (`W_bound_all`). It follows that
   4·f_ω(m+1) + 4 ≤ W_(m+3)(1) (`W_omega_bound`).
2. **Kc.** For p ≥ 4 and a ≥ 2, Kc raises p by at least a/2 and makes a ≥ 4·f_ω(p − 3) + 4 (`Kc_dom1`). So two Kc
   steps take p to at least f_ω(p − 3) + 4 (`Kc_dom2`), and after c Kc steps the new p − 3 is at least
   f_ω^⌊c/2⌋(p − 3) (`Kc_dom_any`).
3. **Kd_step.** Let ok_pa(n, (p, a)) mean n ≤ p − 4 and n ≤ a/4. If n ≥ 1 and ok_pa(n, pa), then
   ok_pa(f_(ω+1)(n), Kd_step(pa)) (`Kd_step_dom`). A Kd step makes a/2 + 1 ≥ 2n Kc steps, so it applies f_ω at
   least n times. By induction, m Kd steps give ok_pa(f_(ω+1)^m(n)) (`Kd_iter_dom`).
4. **Round 1.** Kc²(3, 2) = (23, W_3(1)). Three more Kc steps give pa1 with p₁ ≥ f_ω(20) + 5 and
   a₁/2 ≥ f_ω(20) (`pa1_bounds`; 23 = 20 + 3).
5. **Round 2.** `D_reload_dom` gives ok_pa(n, pa2_0) for n = f_ω(20). Then a₁/2 ≥ n Kd steps give
   ok_pa(f_(ω+1)^n(n), pa2) = ok_pa(f_(ω+2)(n), pa2) (`round2_dom`, `pa2_dom_strong`).
6. ok_pa(B, (p₂, a₂)) implies B < p₂ + a₂ + 6 (`ok_pa_score_lt`).

### 3.2 How large

Coq's inputs are loose. The following is on paper, from the same lemmas.
- Row 7 of section 2 has level p₃ = 23 + (3^122 − 5)/4 ≈ 4.0·10^57.
- Applying `Kc_dom1` there, instead of at level 23: the next argument is at least 4·f_ω(p₃ − 3) + 4, so the last Kc
  step raises the level by at least 2·f_ω(p₃ − 3) + 2 and makes a₁ ≥ 4·f_ω(p₃ − 3) + 4. So p₁ ≥ f_ω(p₃ − 3) + 5 and
  a₁/2 ≥ f_ω(p₃ − 3), and steps 5–6 of section 3.1 give σ > f_(ω+2)(f_ω(p₃ − 3)) > f_(ω+2)(f_ω(10^57)).
- The true p₁ and a₁ are larger still. We do not prove an upper bound.
- The outer counter makes only one round (section 1.5). So M13 applies f_(ω+2) once, not iterated.

### 3.3 Comparison with the published champions and with T12a

The bounds are from the bbchallenge wiki "Champions" page, as of 2026-10-11. On that page, a row is blank when a
smaller machine already beats that size. None of these comparisons is machine-checked. They assume the wiki uses the
same standard definitions. Below, m = f_ω(20), so Coq gives σ > f_(ω+2)(m) = f_(ω+1)^m(m).

| n | champion | published lower bound | compared with M13 | status |
|---|---|---|---|---|
| 12 | T12a ([`../BB12/`](../BB12/), this repository) | f_(ω+1)(f_(ω+1)(JJ − 2)) ≤ 6N + 11 (Coq) | M13 is larger | on paper, see below |
| 13 | blank (n1, BB(10)) | | M13 is larger | on paper |
| 14 | Jacobzheng 2026 | f_(ω+1)(f_ω⁴(f_7(3))) | M13's lower bound is larger | on paper |
| 15 | Jacobzheng 2026 | f_(ω+1)²(10^10^57) | M13's lower bound is larger | on paper |
| 16 | Jacobzheng 2026 | f_(ω+1)³(f_ω²(f_6²(3))) | M13's lower bound is larger | on paper |
| 17, 18 | published f_(ω+2)-class champions | | not compared | **no claim** |

The arguments use only monotonicity, f_(k+1)(n) > 2↑^k n for k ≥ 1 and n ≥ 2, and m = f_20(20) ≥ f_7(3).
- **BB(14).** m ≥ 4 and m ≥ f_7(3), so f_(ω+1)(m) = f_ω^m(m) ≥ f_ω⁴(f_7(3)). Then
  f_(ω+1)^m(m) > f_(ω+1)(f_(ω+1)(m)) ≥ f_(ω+1)(f_ω⁴(f_7(3))).
- **BB(15).** m ≥ 2↑^19 20 > 10^10^57, so f_(ω+1)^m(m) > f_(ω+1)³(m) > f_(ω+1)²(10^10^57).
- **BB(16).** f_ω(m) = f_m(m) ≥ f_7(m) ≥ f_6²(m) ≥ f_6²(3), so f_(ω+1)(m) ≥ f_ω⁴(m) ≥ f_ω²(f_6²(3)). Then
  f_(ω+1)^m(m) > f_(ω+1)³(f_(ω+1)(m)) ≥ f_(ω+1)³(f_ω²(f_6²(3))).
- **T12a.** T12a's Coq lower bound starts from JJ − 2 < T = 2↑^37 3 = 2↑^36 4, which is larger than m. But
  f_(ω+1)(m) ≥ f_ω(m) = f_m(m) ≥ f_37(4) > T. So f_(ω+1)^m(m) > f_(ω+1)²(f_(ω+1)(m)) > f_(ω+1)²(JJ − 2), and M13's
  proved lower bound exceeds T12a's.
  - No upper bound on T12a's score is proved, so "M13 beats T12a" is a claim about orders of growth.
  - T12a runs an f_(ω+1)-sized loop twice (on paper, about f_(ω+1)(f_ω(f_(ω+1)(JJ))); see the T12a write-up, section
    3.2). M13 applies f_(ω+1) at least m times.
- **BB(17), BB(18).** These champions are also at level f_(ω+2). We have not compared their exact values with M13,
  and we make no claim about them.

As in the T12a write-up, the BB(14)–BB(16) entries have published lower bounds only. So these comparisons show that
M13's proved lower bound exceeds their published lower bounds, not that M13 outscores those machines. If accepted,
M13 would raise the known lower bounds for BB(13) through BB(16), because BB is increasing.

**M14.** The 14-state machine M14 ([`../BB14/`](../BB14/), same proof architecture, also by Argon) has a larger
proved lower bound. Coq proves f_(ω+2)(f_(ω+2)(f_(ω+2)(15))) < N + 1 for M14: its outer counter is reloaded twice
instead of once. So for BB(14) the relevant entry is M14, not M13.

---

## 4. Verification

### 4.1 What Coq proves

The development is in [`verify/multifile/`](verify/multifile/). It uses Coq 8.20.1 on top of
[busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`). The logical path `BB8` is historical.

| statement | Coq name | file |
|---|---|---|
| M13 halts from the blank tape | `halt` | `BB13_M13.v` |
| the rules and runs of sections 1–2 | `CA_SH` … `CH_CA`, `CE_EVEN`, `C_REL`, `D_REL`, `HALT_step`, `Kc_loop`, `Kd_step_all`, `Kd_loop`, `D_reload_all`, `init_306`, `run_pa1`, `run_round2`, `run_pa2` | `BB13_M13.v` |
| the halting tape holds fst pa2 + snd pa2 + 5 ones | `score_exact` | `BB13_M13_bound.v` |
| f_(ω+2)(f_ω(20)) < N + 1, and f_(ω+2)(20) < N + 1 | `sigma_lower_bound_strong`, `sigma_lower_bound` | `BB13_M13_bound.v` |

| file | content |
|---|---|
| `BB132.v`, `Individual132.v` | busycoq instantiated for 13 states. The state `L` shadows busycoq's direction `L`, so tables write `TM.L` / `TM.R`. |
| `BB13_M13.v` | the halting proof (507 lines) |
| `BB13_M13_bound.v` | the exact ones count and the hierarchy bounds (559 lines). It imports `BB13_M13.v` unchanged and restates the transition table as `tm_table`. |

The four `.v` files are Argon's, unchanged except line 1 of `BB13_M13.v`: Argon's heading comment there stated a
stronger bound than the one proved (f_(ω+2)(f_ω(f_ω(20)))), and it now states the bound that `BB13_M13_bound.v`
proves (see [`verify/README.md`](verify/README.md), Provenance).

`compile_clean.sh` rebuilds the four files from scratch (27 s in the recorded build) and runs `probe.v`. See
[`verify/README.md`](verify/README.md). The probe does three things:

- it checks all 26 entries of the transition table by conversion, against lines generated from the machine string
  (M0 is `None`), and checks that the start configuration is the blank tape in state A;
- it prints the definitions the statements use (`iter`, `f`, `f_omega`, `f_omega1`, `f_omega2`, `ones`, …);
- it runs `Print Assumptions` on `halt`, `score_exact`, `sigma_lower_bound` and `sigma_lower_bound_strong`. All four
  report "Closed under the global context".

The logs of that from-scratch build (2026-10-14, busycoq exported from commit `bd2e36f`) are `compile_clean.log` and
`probe.log`; `sha256.txt` has the hashes of the sources.

**Re-checked here** (2026-10-14), besides that build:
- `check.py`, our mechanical reviewer for busycoq proofs, passes on the halting proof. It compiles the file, checks
  the Coq transition table against the machine string, checks the theorem statement, and requires `Print Assumptions`
  to report no axioms.
- A second compile in a separate copy, with its own probe (all 26 table entries generated from the string, and
  `Print Assumptions` on the four theorems), gave the same result.

### 4.2 Not machine-checked

- **σ = N + 1.** In Coq the halting transition is `None`, and `ones` counts the 1s of the halted configuration. The
  extra 1 written by M0 = 1RZ is the standard convention.
- **The comparisons** of section 3.3, and the size estimates of section 3.2.
- **The step numbers** of section 2, except the 116 of `init_116`. They come from simulation.

### 4.3 Independent checks

[`tools/m13_writeup_chk.py`](tools/m13_writeup_chk.py) is a cell-by-cell simulator written for this write-up. It
shares no code with the Coq files. It builds the configurations of section 1.1 as literal tapes, instantiating z with
15 right parts, and checks each rule of sections 1.2–1.4 on concrete instances. It exits nonzero on any failure.
Result (2026-10-14, about 2 seconds): **ALL PASS**, 3,605 instances, no failures.

| check | instances |
|---|---|
| `CA_SH`, `CA_EXIT`, `CA_CH`, `CH_S` | 525 each |
| `CA_SH_iter` | 375 |
| `CH_0` | 150 |
| `CH_CA`, for j ≤ 1 with b ≤ 7, j = 2 with b ≤ 3 (W_2(3) = 362), and (3, 0) | 168 |
| `BLK_iter_aux` | 64 |
| `CE_EVEN` (Kc, levels 1–3) | 360 |
| `C_REL` | 180 |
| `D_REL` | 72 |
| `HALT_step` | 70 |
| `Kd_step` on (2, 2): `Ce 2 2 0 (d+2)` → `Ce 4 8 0 d` | 6 |
| `D_reload` at levels 3, 4, 5 | 15 |
| small runs to the halt, with N = p + a + 5 exactly | 40 |
| the start-up of section 2 (rows 1–5: steps 116 and 306 exactly; 162, 328 and 1364 printed, and checked to come in this order) | 1 |
| W closed forms and parity; Kc(3, 2) = (4, 38); W_3(1) = (3^122 − 5)/2 | 2 |
| the mirrored 1RB form (entry by entry, and 200,000 steps in lockstep with M13 on a reflected tape), and Argon's core-label string ([`search/README.md`](search/README.md); a renaming of M13's states) | 2 |

All 25 defined transitions are read during these checks. The simulator only checks this description against the
machine. The proof does not depend on it.

---

## 5. Discovery and credit

- **Found** by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity on 2026-10-14.
- **Proved** by Argon: both Coq files, `BB13_M13.v` (`halt`) and `BB13_M13_bound.v` (`score_exact` and the hierarchy
  bounds). Only the heading comment on line 1 of `BB13_M13.v` was corrected here (section 4.1).
- **Re-checked** independently here (section 4):
  - `check.py`;
  - from-scratch compiles, with a probe and `Print Assumptions`;
  - the simulator of section 4.3;
  - re-runs of Argon's search code (section 5.1).

  This write-up was written here.
- **Built on** Jacobzheng's 14-state f_(ω+1) BB(14) champion, whose engine M13 adapts (section 5.1).
- **Related**: M14 ([`../BB14/`](../BB14/)) is a 14-state machine by Argon with the same proof architecture. It
  reaches f_(ω+2)³.

### 5.1 How it was found

This section follows Argon's notes on the search, written 2026-10-14. They are working notes, not a checked record;
statements about searches are Argon's claims unless they say they were re-run here. The search code that survives is in [`search/`](search/),
with a README saying what each program does.

1. **The engine.** Argon started from the engine of Jacobzheng's 14-state f_(ω+1) champion for BB(14).
   - That engine only grows to the left. It keeps `(10)^p 1^A` there and leaves the right part of the tape alone, so
     the right part can hold counters.
   - Jacobzheng's f_(ω+2) machines for BB(17) and BB(18) use the same idea, with separate groups of states for the
     ω+1 and ω+2 layers.
2. **A cheaper ω+1 layer.** Argon then made the ω+1 layer cheaper.
   - In the BB(14) champion, two states build a seed digit before the pair rewriter runs.
   - Argon's change jumps straight into the rewriter (in that machine's labels, I1 = 0LA and L0 = 1LH). The seed then
     forms at the left end, and each counter step finishes the previous step's work.
   - With an outer gadget for reloading and halting, this gave the 14-state machine M14.
3. **13 states on that core.** Argon reports an exhaustive search over the outer transitions of a 9-state version of
   this core (two evaluator states merged) with no halting 13-state machine. That program did not survive.
   - A related surviving search, `search13.cpp`, finds 8 reload gadgets on that kind of core. Each uses every free
     transition, so none has room for a halt. We re-ran it.
4. **A new core.** Argon then fixed a 10-state core in which the scanning state's exit leads straight into the
   dispatcher.
   - This is B0 = 1RA in core labels, which is D0 = 1RE in M13's labels. After C0 = 1RD, it writes the second of two
     1s after the run of 1s, and the head lands in E (rule `CA_EXIT`).
   - When the dispatcher E reads a 1 of the inner counter, E1 = 0LJ erases it and starts the pair rewriter (states E
     and J). The rewriter turns `1^(2k+2)` into k + 1 blocks.
   - Storing the inner counter as blocks `(10)^c` means C_REL needs no conversion step: the rewriter already writes
     the new counter in that form.
   - The argument stays even, because each step calls W with argument 1 and W_j(1) is even (`W_par`).
   - In M13's labels, the core is the ten states A–E, H and J–M. The outer gadget is the states F, G and I, plus the
     core slots E0, H0 and M0. M0 is the halt.
5. **The 13-state search.** `search_core10.cpp` searches the 9 free transitions of a 13-state machine on this core.
   - It keeps the partial machines whose reloads behave like C_REL and D_REL, and whose halt is reached for the right
     parity of d.
   - Argon reports 180 such gadgets. Checking their runs from the blank tape gave halting machines, and Argon chose
     M13 as the cleanest.
   - **Re-run here:** with `main` set to 13 states and Δd = 2, the program finds 111 hits in 4 seconds. M13's full
     string, in Argon's core labels, is among them. We did not reproduce Argon's 180; the limits Argon used were not
     recorded.
6. **12 states on this core.** Argon reports that 12 states (only two outer states, I and J in core labels; 7 free
   transitions) give no halting machine on this core.
   - **Re-run here:** `search_core10.cpp` as shipped runs exactly this case and finds 0 hits for Δd = 1, 2, 3.
   - This is a result for this one architecture. It is not a lower bound on the number of states an f_(ω+2) machine
     needs, and it says nothing about BB(12) in general.

The halting proof and the score bound do not depend on any of this search code.
