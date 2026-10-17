# The BB(4,3) champion, machine-checked

    1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD

This 4-state, 3-symbol machine is the current BB(4,3) champion of the
[bbchallenge wiki](https://wiki.bbchallenge.org/wiki/BB(4,3)). Pavel Kropitz found it in May 2024, and Polygon
analysed it by hand in October 2025 ([machine page](https://wiki.bbchallenge.org/wiki/1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD)).
Here Coq proves, with no axioms, that it halts from the blank tape, that its final tape is a single block of
σ = 4·e₄ + 18 ones, where e₄ is given by an explicit recursion, and that

    2↑↑↑2↑↑↑2↑↑↑(2^96 − 1) < σ.

As far as we know, this is the first machine-checked proof that this machine halts and of its score. The analysis
follows Polygon's: the same configuration family, the same rules (numbered as on the wiki) and the same recursion.
Written 2026-10-17.

|   | 0   | 1   | 2   |                  |
|---|-----|-----|-----|------------------|
| A | 1RB | 1RD | 1LC |                  |
| B | 2LB | 1RB | 1LC |                  |
| C | 1RZ | 1LA | 1LD | C0 is the halt   |
| D | 0RB | 2RA | 2RD |                  |

**Main facts.**

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms). |
| Final tape | Machine-checked: just before the halt, state C reads a 0 with exactly 4·e₄ + 17 ones to its right and blanks everywhere else. C0 = `1RZ` writes one more 1, so the final tape is 1^(4·e₄ + 18). |
| Score | σ = 4·e₄ + 18, all ones and consecutive. e₄ is the recursion of section 3. It is not evaluated as a number. |
| Size | Machine-checked: 2↑↑↑2↑↑↑2↑↑↑(2^96 − 1) < σ (Knuth arrows; 2^96 ≈ 7.92·10²⁸). No upper bound is proved. |
| Steps | Not computed. The first 80 are in the Coq proof. |

---

## 1. Notation

- `0^∞` is the blank part of the tape, and `x^n` is n copies of the word x. Words are written left to right.
- `x <Q` means state Q with the head on the cell x just left of the marker; `Q> x` means state Q with the head on
  the cell x just right of it.
- In the Coq files, `l <{{Q}} r` has the head on the first cell of l, and `l {{Q}}> r` on the first cell of r. The
  left side l is listed outward from the head, so the word `(12)^b 2 2 1 <D` is written `1 >> 2 >> 2 >> [2;1]^^b *> …`.
- A rule written with `L … R` holds for every left context L and right context R: the machine never reads them.
- "X → Y" means that the machine goes from X to Y in zero or more steps (Coq's `-->*`).

The two configuration families are

    D(a, b, c)  = 0^∞   (11)^a (12)^b 2 2 1 <D (11)^c 0^∞
    D1(a, b, c) = 0^∞ 1 (11)^a (12)^b 2 2 1 <D (11)^c 0^∞

D and D1 differ only in a single 1 at the left end. In Coq both are `DL t a b c`, with t = `const 0` (D) or
`1 >> const 0` (D1) (`BB43_rules.v`). Here a counts the pairs 11 on the far left, b the pairs 12, and c the pairs 11 to
the right of the head. The functions are

    g(b)  = 2b + 5
    f1(b) = g^(b+3)(1) = 3·2^(b+4) − 5
    G(c)  = f1^(2c+11)(1)

where h^n is h applied n times. So f1(0) = 43, f1(1) = 91, and f1 is exponential. G is a tower of f1's, so it is
tetration-sized, and iterating G gives pentation.

---

## 2. The rules

All rules below are lemmas of [`verify/BB43_rules.v`](verify/BB43_rules.v), proved for all values of the
parameters.

**Sweeps and small rules.** The sweeps move the head across a block in one direction: `D_22`
(`L D> 2^n R → L 2^n D> R`), `D_11`, `A_11`, `B_11`, `C_21`, `A_12`. Built from them are `P6` and Polygon's rules
R10–R18, R20, R21a, R22, R23z and the rule `Y`:

| Coq | rule |
|---|---|
| `R10` | `L 2 <D (11)^(a+1) 0 0 R` → `L <D (11)^(a+2) 2 R` |
| `R11` | `L 2 <D (11)^a 2 0 0 R` → `L <D (11)^(a+1) 2 2 R` |
| `R12`, `R13` | `L 1 <A (11)^b 0 0 R` → `L <A (11)^(b+1) 2 R`, and the same with a 2 before the 0 0 |
| `R14`, `R15` | `L 1 2 1 <D (11)^b 0 0 R` → `L 1 <D (11)^(b+2) R`; so `L (12)^a 1 <D (11)^b 0^∞` → `L 1 <D (11)^(b+2a) 0^∞` |
| `R16`, `R17` | `L 1 2 2 1 <D (11)^b 0^∞` → `L 2 (12)^(b+2) 1 <D (11) 0^∞` → `L 2 1 <D (11)^(2b+5) 0^∞` |
| `R18` | `L (12)^a 2 1 <D (11)^b 0^∞` → `L 2 1 <D (11)^(g^a(b)) 0^∞` |
| `R20` | `L 1 <D (11)^(b+1) 2 0^∞` → `L 2 1 <D (11)^(2b+1) 0^∞` |
| `R21a` | `L 2 2 1 <D (11)^b 0^∞` → `L 2 <D (11)^(b+2) 0^∞` |
| `R22` | `L 1 <D (11)^(b+1) 2 2 0^∞` → `L 2 (12)^b 2 1 <D (11) 0^∞` |
| `Y` | `L 1 1 1 <D (11)^b 0^∞` → `L 1 <A (11)^(b+2) 0^∞` |
| `R23z` | `L 1 <A (11)^b 2 2 0^∞` → `L (12)^b 2 2 1 <D (11) 0^∞` |

**R21: one pair 12 gives f1.**

    R21:  L (12) 2 2 1 <D (11)^b 0^∞   →   L 2 2 1 <D (11)^(f1(b)) 0^∞

Three trips to the right end (`R21a`, `R10`, `R11`) use up the `2 2 1` next to the head and the 2 of the pair 12,
and leave `L 1 <D (11)^(b+4) 2 2 0^∞`. `R22` turns this into `L 2 (12)^(b+3) 2 1 <D (11) 0^∞`: the right block has
become b + 3 pairs 12 to the left of the head. `R18` consumes them one at a time, and each applies g to the count of
pairs 11 on the right, starting from 1. The result is g^(b+3)(1) = f1(b). Repeating R21 (`R30`) clears the whole block
of pairs 12:

    DL_b:  D(a, b, c) → D(a, 0, f1^b(c)),      and the same for D1.

**R23: three pairs 11 give G.**

    R23:  L (11)^3 2 2 1 <D (11)^b 0^∞   →   L (12)^(2b+11) 2 2 1 <D (11) 0^∞

When there are no pairs 12 left, the head reaches the pairs 11 on the far left. Three of them (with `R21a`, `R10`,
`R20`, `R14`, `Y`, `R12`, `R13`, `R23z`) become 2b + 11 pairs 12, and the right part restarts at one pair 11. Then
`DL_b` clears the 2b + 11 pairs 12 from c = 1, which gives G(b):

    DL_3:   D(a+3, 0, c) → D(a, 0, G(c)),
    DL_3k:  D(3k+a, 0, c) → D(a, 0, G^k(c)),      and the same for D1.

**The edge rules.** When fewer than three pairs 11 are left, what happens depends on how many there are and on the
left end (D or D1):

| Coq | rule |
|---|---|
| `R25` | D(2, 0, c) → D1(2c + 8, 3, 1) |
| `R26` | D1(1, 0, c) → D1(2c + 7, 3, 1) |
| `R27` | D1(0, 0, c) → D(2c + 5, 3, 1) |
| `R28` | D(1, 0, c) → state C reading 0 with 1^(4c+17) to its right and blanks elsewhere: the halt |

In each of R25–R27 the head reaches the left end, the c pairs 11 on the right turn into 2c + 5 to 2c + 8 pairs 11
on the far left, and three pairs 12 are written. No rule covers D(0, 0, c) or D1(2, 0, c); the run never meets
them (section 3).

---

## 3. The run and the exact score

All values below are ≡ 1 (mod 3): f1(b) = 3·2^(b+4) − 5 ≡ 1, so every value of f1 and of G is ≡ 1 (Coq: `f1_mod`,
`G_mod`). If x ≡ 1, then 2x + 8 ≡ 1, 2x + 7 ≡ 0 and 2x + 5 ≡ 1 (mod 3). This fixes the remainder after each `DL_3k`.

| | configuration | how | Coq |
|---|---|---|---|
| 0 | blank tape, state A | | |
| 1 | D(2, 2, 1), at step 80 | 80 single steps | `start` |
| 2 | D(2, 1, 91), at step 11828 | `R21`, f1(1) = 91 | `DL_b` |
| 3 | D(2, 0, e₁), e₁ = f1(91) = 3·2^95 − 5 | `R21` | `DL_b` |
| 4 | D1(2e₁ + 8, 3, 1) → D1(2e₁ + 8, 0, v), v = f1³(1) = f1(e₁) | `R25`, `DL_b` | `chain` |
| 5 | D1(1, 0, e₂), e₂ = G^(k₁)(v), 2e₁ + 8 = 3k₁ + 1 | `DL_3k` | `chain` |
| 6 | D1(2e₂ + 7, 3, 1) → D1(2e₂ + 7, 0, v) → D1(0, 0, e₃), e₃ = G^(k₂)(v), 2e₂ + 7 = 3k₂ | `R26`, `DL_b`, `DL_3k` | `chain` |
| 7 | D(2e₃ + 5, 3, 1) → D(2e₃ + 5, 0, v) → D(1, 0, e₄), e₄ = G^(k₃)(v), 2e₃ + 5 = 3k₃ + 1 | `R27`, `DL_b`, `DL_3k` | `chain` |
| 8 | C reads 0 with 1^(4e₄+17) to its right: the halt | `R28` | `reaches_final`, `final_halted` |

So, exactly (`BB43_run.v`; `probe.v` prints these definitions):

    e₁ = f1²(1) = f1(91) = 3·2^95 − 5
    v  = f1³(1)
    e₂ = E2 = G^((2e₁ + 7)/3)(v),      (2e₁ + 7)/3 = 2^96 − 1
    e₃ = E3 = G^((2e₂ + 7)/3)(v)
    e₄ = E4 = G^((2e₃ + 4)/3)(v)
    σ  = 4·e₄ + 18

The divisions are exact (the residues above). In Coq, e₄ is sealed behind `e4_eq : e4 = E4 e1 v`, so that no tactic
tries to evaluate it.

**Counting convention.** busycoq models the halting transition as `None`, so the Coq run ends in the configuration
`c_final` where C reads a 0, and Coq proves that it is exactly `const 0 {{0}} [1]^^(4 e4 + 17) *> const 0`: blank
on the left, a 0 under the head, 4·e₄ + 17 ones and then blank on the right. The halting entry C0 is `1RZ` (checked in
`probe.v` against the machine string), so the final write turns the 0 under the head into a 1. The halted tape is
then the single block 1^(4·e₄ + 18), and σ counts its nonzero cells: σ = 4·e₄ + 18. Since all of them are 1s, this is
also the number of 1s. Coq defines `sigma := 4 * e4 + 18`; the + 1 for the final write is the standard convention and
is not part of the busycoq semantics.

---

## 4. The bound

[`verify/BB43_bound.v`](verify/BB43_bound.v) defines Knuth's arrows by `knuth 0 a b = a·b` and
`knuth (n+1) a b = (knuth n a)^b(1)`, so `knuth 1 2 b = 2^b`, `knuth 2` is ↑↑ and `knuth 3` is ↑↑↑. It proves

    sigma_lower:  2↑↑↑2↑↑↑2↑↑↑(2^96 − 1) < σ

using only symbolic recursion; no large number is evaluated. The steps:

1. f1(x) + 5 = 6·2^(x+3) (`f1_closed`), so 2^x ≤ f1(x), and 2↑↑n ≤ f1ⁿ(1) (`tower_le_iter_f1`).
2. G(c) = f1^(2c+11)(1) ≥ 2↑↑(c+1) (`G_ge`), and so G^k(x) ≥ 2↑↑↑(k+1) for x ≥ 2 (`iter_G_ge`). With 2↑↑y ≥ 2y
   this gives G^k(x) ≥ 2·(2↑↑↑k) (`cascade`).
3. With k₁ = (2e₁ + 7)/3 = 2^96 − 1 (`k1_value`) and v ≥ 2: e₂ ≥ 2·X with X = 2↑↑↑k₁, so k₂ = (2e₂ + 7)/3 ≥ X;
   e₃ ≥ 2·2↑↑↑k₂ ≥ 2·2↑↑↑X, so k₃ ≥ 2↑↑↑X; and e₄ ≥ 2·2↑↑↑k₃ > 2↑↑↑2↑↑↑X (`E4_lower`). Then σ = 4e₄ + 18 > e₄.

**Comparison with the wiki.** The machine page gives, in Polygon's notation,
f2(a, b) = f1^(2·f2(a−1, b) + 11)(1) with f2(0, b) = b, that is f2(a, b) = G^a(b), and
e₂ = f2((2e₁ + 7)/3, f1²(91)), e₃ = f2((2e₂ + 7)/3, f1²(91)), e₄ = f2((2e₃ + 4)/3, f1²(91)), score 4e₄ + 18. Since
f1(1) = 91, f1²(91) = f1³(1) = v, so this is the recursion of section 3. (In the text we fetched, the fractions are
flattened, as "2e1+73" and "2e3+43"; we read them as (2e₁ + 7)/3 and (2e₃ + 4)/3, which is what the machine does.)
The wiki states

    2↑↑↑2↑↑↑2↑↑↑(7.92×10²⁸) < e₄ < σ < 2↑↑↑2↑↑↑2↑↑↑(7.93×10²⁸).

2^96 = 79,228,162,514,264,337,593,543,950,336 ≈ 7.92×10²⁸. We prove only the lower bound, in the form
2↑↑↑2↑↑↑2↑↑↑(2^96 − 1) < σ. Since 7.92×10²⁸ < 2^96 − 1 and ↑↑↑ is monotone (`knuth_mono`), this implies the wiki's
lower bound for σ; that implication is not stated as a separate Coq theorem. The wiki's upper bound
2↑↑↑2↑↑↑2↑↑↑(7.93×10²⁸) is not checked here.

---

## 5. Verification

### 5.1 What Coq proves

The development is in [`verify/`](verify/), on [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`)
with Coq 8.20.1. The logical root is `TM43`.

| statement | Coq name | file |
|---|---|---|
| the machine halts from the blank tape | `bb43_halts : halts tm c0` | `BB43_run.v` |
| it reaches `c_final`: C reads 0, 1^(4e₄+17) to its right, blank elsewhere | `reaches_final : c0 -->* c_final` | `BB43_run.v` |
| `c_final` is halted (C0 is `None`) | `final_halted : halted tm c_final` | `BB43_run.v` |
| the exact value of e₄ | `e4_eq : e4 = E4 e1 v` | `BB43_run.v` |
| the score | `sigma := 4 * e4 + 18` (definition) | `BB43_run.v` |
| 2↑↑↑2↑↑↑2↑↑↑(2^96 − 1) < σ | `sigma_lower` | `BB43_bound.v` |
| the rules of section 2 | `R10`–`R23`, `R21a`, `R23z`, `Y`, `P6`, `R30`, `DL_b`, `DL_3`, `DL_3k`, `R25`–`R28` | `BB43_rules.v` |
| the residues of section 3 | `f1_mod`, `G_mod`, `iter_G_mod` | `BB43_run.v` |
| the Coq table is the machine string; C0 is `1RZ`; the start is blank in state A; the shape of `c_final`; σ = 4e₄ + 18 | `table_matches_string`, `halt_entry`, `c0_is_blank_A`, `c_final_shape`, `sigma_def` | `probe.v` |

`probe.v` parses the machine string inside Coq and checks all 12 table entries by `vm_compute`. It runs
`Print Assumptions` on `table_matches_string`, `halt_entry`, `c0_is_blank_A`, `c_final_shape`, `bb43_halts`,
`reaches_final`, `final_halted`, `sigma_lower` and `e4_eq`. All nine report "Closed under the global context".

**Build record.** A from-scratch build on 2026-10-17 (Coq 8.20.1, Coq Platform 2025.01, Windows 11, coqc at Idle
priority), in a fresh directory with only the published `verify/` sources next to busycoq `verify/` exported from
commit `bd2e36f` (busycoq's 7 needed files: 47 s): `compile_clean.sh` exit 0 in 111 s, of which `BB43_rules.v` took
73 s. Logs: [`verify/compile_clean.log`](verify/compile_clean.log), [`verify/probe.log`](verify/probe.log); hashes:
[`verify/sha256.txt`](verify/sha256.txt). The GitHub workflow (job `bb43`) runs the same build on every push and fails
unless `probe.log` reports nine closed theorems and no `Axioms:`.

### 5.2 Not machine-checked

- **σ = 4e₄ + 18 counts the final write.** Coq proves the tape of `c_final` exactly; the extra 1 written by
  C0 = `1RZ` is the standard convention (section 3).
- **The step numbers** of section 3, except the 80 of `start`. They come from simulation. The total number of steps
  is not computed.
- **The wiki's upper bound** and the implication to the wiki's lower bound (section 4).

### 5.3 Independent checks

[`tools/bb43_chk.py`](tools/bb43_chk.py) is a cell-by-cell simulator written for this write-up (Python, standard
library only). It shares no code with the Coq files. For a rule with an arbitrary context it fills the context with
an "unknown" symbol and fails if the machine reads it, so a pass covers every context. It exits nonzero on any
failure. Result (2026-10-17, Python 3.11, about 3 seconds): **ALL PASS**, 36 checks.

| check | instances |
|---|---|
| from blank, the first visit to D(2, 2, 1) is at step 80, and to D(2, 1, 91) at step 11828 | 2 |
| the sweeps `D_22`, `D_11`, `A_11`, `B_11`, `C_21`, `A_12`, and `P6` (n, a ≤ 5) | 6 each |
| `R10`–`R14`, `R16`, `R17`, `R20`, `R21a`, `R22`, `Y`, `R23z` (a, b ≤ 5) | 6 each |
| `R15` (a, b ≤ 4), `R18` (a ≤ 4, b ≤ 3) | 25, 20 |
| `R21` (b ≤ 4; b = 4 takes 781,884 steps, to f1(4) = 763) | 5 |
| `R23` (b ≤ 5) | 6 |
| `R25`, `R26`, `R27` (c ≤ 7) | 8 each |
| `R28`: D(1, 0, c) halts; just before, C reads 0 with exactly 1^(4c+17) to its right; the final tape is 1^(4c+18) and nothing else (c ≤ 11) | 12 |
| f1(b) = g^(b+3)(1) = 3·2^(b+4) − 5 and f1(b) ≡ 1 (mod 3) (b < 60); f1(1) = 91; e₁ = 3·2^95 − 5; (2e₁ + 7)/3 = 2^96 − 1; the residues of section 3; 2^96 ≈ 7.92·10²⁸ | 6 |
| every transition, including the halt C0, is read by some check | 1 |

A mutated copy (wrong step count, wrong R21, R23, R25 and R28 right-hand sides) failed exactly those five checks.
The simulator only checks this description against the machine. The proof does not depend on it.

---

## 6. Credit

- **Discovery:** Pavel Kropitz, May 2024, one of seven long-running BB(4,3) machines
  ([bbchallenge Discord](https://discord.com/channels/960643023006490684/1026577255754903572/1243253180297646120)).
- **Analysis:** Polygon, by hand, October 2025
  ([User:Polygon/Page for analyses](https://wiki.bbchallenge.org/wiki/User:Polygon/Page_for_analyses), and the
  [machine page](https://wiki.bbchallenge.org/wiki/1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD)): the configuration
  family D(a, b, c), the rules, the recursion e₁, …, e₄ and the score 4e₄ + 18, all used here.
- **Earlier analysis of the batch:** Racheline analysed four other machines of the same May 2024 batch, which are
  equivalent to each other, in February 2025
  ([bbchallenge Discord](https://discord.com/channels/960643023006490684/1331570843829932063/1337228898068463718)).
  The wiki credits the analysis of this machine to Polygon.
- **Coq proof, simulator and this write-up:** this project, 2026-10-17. The Coq statements follow Polygon's
  rules; the edge rules R25–R28 and the bound are stated and proved here.
