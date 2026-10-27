# BB29 / BB31 / BB33: hydra-game machines

The analysis written before the Coq proofs (2026-10-27): how the machines work, every rule checked by simulation,
and the proof plan. It is the specification the Coq files refer to ("REPORT.md section N"). Scripts are in this
directory; `python check_all.py` reruns every check (5–10 min, results in `check_all.log`, all passing;
`tmcross.py` needs `g++ -O2 -o tmat tmat.cpp` first).

**Status (after the Coq proofs).** Of what §9 lists as open, this is now proved in Coq: the rules, BB29's bound
σ > f_{ω^ω}(3) (BB29's stronger f_{ω^4}(4) − 2 remains informal), and the BB31/BB33 bounds (via the Hardy hierarchy),
including the extra-leading-leaf case. See
[`../hydra29.md`](../hydra29.md), [`../../BB31/hydra31.md`](../../BB31/hydra31.md),
[`../../BB33/hydra33.md`](../../BB33/hydra33.md). Two small corrections found while formalizing: (1) this report
writes left-side pairs in tape order inside `<*`, but busycoq's `l <* xs` puts the first element of xs next to the
head, so the Coq files reverse each pair on the left; (2) in §6, "strictly inflationary" should be "inflationary"
(x ≤ f x). No rule was wrong.

## 0. Summary
- **Mechanism.** All three machines run a Kirby–Paris-style hydra game with a unary counter on the left. The tape,
  read in 2-cell pairs, spells a hydra (rooted tree) as a bracket string. Each round removes the rightmost head (leaf)
  ℓ. If ℓ's parent p is not the root, the grandparent gets copies of p, and the number of copies grows by one each
  round. The machine halts when the hydra is empty.
- **BB29 halts** (given the rules, all validated by simulation). From TM step 175 the configuration is C(1): the hydra
  root → A → B → 4 leaves (ordinal ω^(ω^4)) with counter m = 1. The exact score is σ = T_4(S)(1) + 1 (closed form in
  §5). σ > f_{ω^3}(3) = f_{ω^ω}(3) is proved structurally in §6. Informally, σ ≥ H_{ω^{ω^4}}(4) − 2 = f_{ω^4}(4) − 2 =
  f_{ω^ω}(4) − 2.
- **Height limit.** The machines differ only in a left-scanning bracket-depth counter, which supports hydra height
  E = 3 / 5 / 7 (BB29 / BB31 / BB33). Each +2 states adds two hydra levels.
- **BB31 and BB33 (informal).** BB31's C(1) ordinal is ω^ω^ω^(ω^4), so σ ≳ f_{ω^ω^ω^ω}(4) − 2, just above the posted
  claim f_{ω^ω^ω^ω}(3). BB33's C(1) ordinal is ω^ω^ω^ω^ω^(ω^3), so σ ≳ f_{ω^ω^ω^ω^(ω^3)}(4) − 2 > f_{ω↑↑6}(3), just
  above the posted claim.
- **No sign of a transcription error.** Every transition of all three machines is used by some valid configuration
  (`usage.py`). The BB29 blank-tape run alone uses everything except B0 (the halt) and T0 (used only in later
  successor chops).

## 1. Tape alphabet
BB29 pairs are cells (2i, 2i+1). BB31 and BB33 pairs are shifted by one cell: (2i−1, 2i). In tape order:

| pair | name | meaning |
|---|---|---|
| `01` | **O** | `(` |
| `11` | **C** | `)` |
| `10` | **X** | marked `)`: the close of the marked node M |
| `00` | **Z** | blank / separator / marked `(` |

The first bit of a pair is data; the second bit means "unmarked". Marking maps O ↔ Z and C ↔ X. Right-moving states sit
on the first cell of a pair, left-moving states on the second. Every state has a fixed cell parity, except R, [ and \
in BB29, which also run inside other pair transitions. The pair-level machine (`macro2.py`, `pm_full.py`) is computed
exactly from the TM table by simulating inside each pair; `tmcross.py` independently runs the real TM and compares
whole tapes.

## 2. Configuration family
**Hydra.** A hydra h is the ordered list of children of an implicit root. A node is the list of its children; a leaf
is `()`. The **marked node M** lies on the rightmost path at depth d (d = 0 means M is the root).

**Encoding enc(h,d)** (`hydra.enc`). Write the root's children in preorder with O/C. Write M's closing bracket as X,
and omit the closing brackets of M's ancestors (the tape after X is blank). For d = 0, enc(h,0) = all children ++ X.

**Configuration K(a,b,h,d)**, in BB29 state names, with O = [0;1] and Z = [0;0]:

`const 0 <* O^^a <* Z <* O^^b <{{P}} Z *> enc(h,d) *> const 0`

- The head is on the 2nd cell of the last O of O^b, or of the a/b separator Z if b = 0.
- The counter state is P in BB29, O in BB31, P in BB33.
- A **macro event** is the first entry into the P walk (`family.pm_events`).
- **C(m,h,d) := K(m,0,h,d)** is the configuration just before a chop.

## 3. Rules

### 3a. Pair-level atomic rules (BB29 names; each is a few TM steps)

Right-movers (`l {{q}}> p *> r`):

| state | reads | result |
|---|---|---|
| H | O/C/X | keep, move right |
| H | Z | write O, turn: `l <{{Y}} O*>r` |
| K | O/C/X | keep, move right |
| K | Z | `l <{{]}} C*>r` |
| N | O/C | move right |
| N | Z | `l <{{]}} X*>r` |
| N | X | `l <{{R}} X*>r` |
| V | O/C | move right |
| V | Z | pass: `(l<*Z){{N}}> r` |
| V | X | `l <{{B}} Z*>r` |
| F | O | `(l<*Z){{H}}>r` |
| F | C | `(l<*X){{K}}>r` |
| F | X | `(l<*C){{N}}>r` |
| [ | O or Z | `(l<*Z){{V}}>r` |

Left-movers (`(l<*p) <{{q}} r`):

| state | reads | result |
|---|---|---|
| Y | O/C | move left |
| Y | X | `l <{{D}} X*>r` |
| Y | Z | `l <{{P}} Z*>r` |
| ] | O/C | `l <{{Y}} p*>r` |
| D | O/C | move left |
| D | Z | `(l<*O){{F}}>r` |
| D | X | `(l<*C){{F}}>r` |
| P | O | move left |
| P | Z | `(l<*O){{[}}>r` |
| B | C | `l <{{B}} Z*>r` |
| B | O | `l <{{R}} X*>r` |
| B | Z or X | **halt** (B0 = `---`) |

**Depth scanner.** States R (depth 0), T (1), \ (2). Reading C goes one level deeper (R→T→\→S); reading O goes one
level back (\→T→R).
- R on O means the parent's open bracket was found: `(l<*Z){{H}}>r`.
- R on Z means the scan reached the separator: `l <{{P}} Z*>r`.
- **Escape:** S (depth 3) on O → `l <{{Y}} O*>r`. Y then runs to the separator and enters P, the same outcome as R
  reading Z.
- S on C (depth 4, state U) produces garbage. This is the height limit.

### 3b. Scan lemmas
Induction on the word w, with w in {O,C}* unless noted.

- **S1 H-scan** (w in {O,C,X}*): `l {{H}}> w*>Z*>r ->+ (l<*w) <{{Y}} O*>r`.
- **S2 K-scan** (w in {O,C,X}*): `l {{K}}> w*>Z*>r ->+ (l<*w) <{{]}} C*>r`.
- **S3 N-scan:** `l {{N}}> w*>Z*>r ->+ (l<*w) <{{]}} X*>r` and `l {{N}}> w*>X*>r ->+ (l<*w) <{{R}} X*>r`.
- **S4 V-scan:** `l {{V}}> w*>Z*>r ->+ (l<*w<*Z) {{N}}> r` and `l {{V}}> w*>X*>r ->+ (l<*w) <{{B}} Z*>r`.
- **S5 Y-scan** (also with ] in place of Y when w is nonempty): `(l<*X<*w) <{{Y}} r ->+ l <{{D}} X*>w*>r` and
  `(l<*Z<*w) <{{Y}} r ->+ l <{{P}} Z*>w*>r`.
- **S6 D-scan:** `(l<*Z<*w) <{{D}} r ->+ (l<*O) {{F}}> w*>r` and `(l<*X<*w) <{{D}} r ->+ (l<*C) {{F}}> w*>r`.
- **S7 P-walk + [:** for b ≥ 1, `(l<*Z<*O^^b) <{{P}} r ->+ (l<*O<*Z) {{V}}> O^^(b-1)*>r`; for b = 0,
  `(l<*Z) <{{P}} Z*>r ->+ (l<*O<*Z) {{V}}> r`.
- **S8 B-erase:** `(l<*O<*C^^j) <{{B}} r ->+ l <{{R}} X*>Z^^j*>r`; `(l<*Z<*C^^j) <{{B}} r` halts.
- **S9 depth scan.** Let L = OC (a leaf), t1(k) = O L^k C (height ≤ 1), t2 = O t1* C (height ≤ 2).
  - (a) Non-root parent, s in t1*: `(l<*O<*s) <{{R}} X*>r ->+ (l<*Z) {{H}}> s*>X*>r`.
  - (b) Root, w in t2*: `(l<*Z<*w) <{{R}} X*>r ->+ l <{{P}} Z*>w*>X*>r`. Proof by induction from the right: a last
    tree of height ≤ 1 is scanned normally; otherwise the escape fires and S5 finishes.
- **S10 COPY (core lemma)**, for any s in {O,C}*:
  `(l<*Z) {{H}}> s*>X*>const 0 ->+ (l<*O<*s<*C<*O<*s) <{{]}} X*>const 0`.
  - Loop invariant J(s1,s2) := `(l <* mark(O.s1) <* s2) <{{D}} X*>O*>s1*>const 0`, where `mark` replaces the last pair
    by its marked form (O→Z, C→X).
  - Start: S1 runs to the blank, writes O, then Y reads X; this gives J([], s).
  - Step: J(s1, t::s2) ->+ J(s1++[t], s2). Chain: S6, then F marks t, then H (t = O) or K (t = C) appends t, then
    Y/] scans back (S5).
  - End: J(s, []). D unmarks, F turns X into C, N writes the final X (S3), ending in ]<.

### 3c. Round lemmas (BB29, height(h) ≤ 3)
- **R1 (b-step, d ≥ 1):** `K(a,b+1,h,d) ->+ K(a+1,b,addcopy(h,d),d)`. addcopy inserts a copy of M immediately before
  M. Chain: S7, S4, S3, S9a, S10, S5. enc(h,d) = pre ++ O s X becomes pre ++ O s C O s X = enc(addcopy(h,d), d).
- **R1' (b-step, d = 0):** `K(a,b+1,h,0) ->+ K(a+1,b,h,0)`. Chain: S7, S4, S3, S9b.
- **R2 (chop), h nonempty:** `K(a,0,h,d) ->+ K(0,a+1,h',d')`. The rightmost leaf is removed; its parent p becomes M
  (d' = depth(p)). If p is not the root, one copy of the shortened p is made at once (S10); if p is the root (S9b), no
  copy. Chain: S7(b=0), S4, S8 (enc = pre O C^j X becomes pre X), then S9.
- **R3 (halt):** `K(a,0,(),0)` halts with **a+1 ones** (S7, then V on X, then B on Z).
- **Composite round** C(m) → C(m+1): in the limit case (p not the root) the shortened p ends up as **m+3** nodes in
  total (itself plus m+2 copies); in the successor case (the removed leaf is a child of the root) the leaf is simply
  removed.

**Validation (`rand_family.py`).** Random K(a,b,h,d) are run on the exact pair machine until halt, and every macro
event, including the final ones count, is compared with the model:

| machine | heights tested | agreeing runs | runs that reached HALT |
|---|---|---|---|
| BB29 | ≤ 3 | 1100/1100 | 709 |
| BB31 | ≤ 5 | 500/500 | 252 |
| BB33 | ≤ 7 | 500/500 | 264 |

Negative control: one height above the limit fails, as predicted (BB29 at height 4: 34/300 and 15/150 runs bad; BB31
at height 6: 3/150; BB33 at height 8: 3/100).

## 4. Ordinal interpretation
o(node) = ω^o(c1) + ... + ω^o(ck), an ordinary sum in tape order. A height-h hydra has o < ω↑↑h. Each round on C
configurations does:
- limit: α → α[m+3], m → m+1 (standard fundamental sequences: (β + ω^(γ+1))[n] = β + ω^γ·n,
  (β + ω^λ)[n] = β + ω^(λ[n]));
- successor: α → α − 1, m → m+1;
- α = 0: halt with σ = m + 1.

Checks: `ordinal_check.py` confirms this exactly for every observed round of all three blank-tape runs. BB29's hydra
stays sorted from C(1) on. BB31/BB33 carry an extra leading leaf inside some nodes, which the ordinary sum absorbs. On
random unsorted hydras (`ordinal_rand.py`) the result equalled α[m+3] in 2057 rounds, was larger (by an absorbed term)
in 44, and never smaller.

Hardy form (informal): G(0,n) = n, G(a+1,n) = G(a,n+1), G(λ,n) = G(λ[n],n+1). Then σ = G(α, m+3) − 2. Since
G ≥ H_α (by induction, using that H is monotone in n), σ ≥ H_α(m+3) − 2, and H_(ω^β) = f_β (standard).

## 5. The BB29 run
- **TM step 59:** first clean configuration, K(0,0, root→A→B→[0,{0}], d=4). This is the only time the height exceeds 3
  (ordinary-sum ordinal ω^ω^ω). Its first chop is at depth 4 (p = {0}, height 1) and is handled correctly.
- **TM step 113:** K(0,1).
- **TM step 175:** C(1) = K(1,0, root→A→B→4 leaves, d=3). Literally:
  `const 0 <* [0;1] <* [0;0] <{{P}} [0;0] *> [0;1;0;1] *> [0;1;1;1]^^3 *> [0;1;1;0] *> const 0`
  Ordinal ω^(ω^4), sorted, height 3 from here on.
- **Checks:** all 182 macro events up to 4M pair steps match the model. TM-literal whole-tape checks pass at TM steps
  59, 113, 175, 1,265, 6,343, 1,254,795 and 5,632,383.

**Closed form** (no ordinals needed). Represent a height-3 hydra as a list of A-nodes, each A being the list of its
B-children's leaf counts. Define:
- T_0(φ)(m) = φ^(m+3)(m+1)
- T_(k+1)(φ)(m) = (T_k)^(m+3)(φ)(m+1)   [iterate the functional T_k]
- W([]) = S, W(A0++[k]) = T_k(W(A0))

Then C(m, [A_1..A_r], d) ->* C(W(A_1)(...W(A_r)(m)...), [], 0), which halts with that value + 1. This matches the
model run to halt on 13 small cases (`formula_check.py`). So **σ(BB29) = T_4(S)(1) + 1 = T_3^4(S)(2) + 1**.

## 6. Bound (BB29, rigorous given the rules)
Define the Wainer functions below ω^ω the same way: U_0(ψ)(n) = ψ^n(n), U_(k+1)(ψ)(n) = (U_k)^n(ψ)(n). Then
f_(a+ω^k) = U_k(f_a), so f_(ω^3)(3) = U_3(S)(3) = f_(ω^ω)(3) (since ω^ω[3] = ω^3).

**Lemma** (induction on k). If φ ≥ ψ pointwise and both are monotone and strictly inflationary, then
T_k φ (x) ≥ U_k ψ (x+1); T_k φ and U_k ψ are again monotone and inflationary; and T_k χ ≥ χ.

Hence σ − 1 = T_3(T_3^3 S)(2) ≥ U_3(T_3^3 S)(3) ≥ U_3(S)(3), using U_3 monotone in its function argument and
T_3^3 S ≥ S. So **σ > f_(ω^ω)(3)**.

Established: the macro rules (checked literally on thousands of instances), the closed form and this bound derived
from them. Not established: a proof of the rules for all parameters (the Coq job), and a formal proof of the Hardy
facts behind the stronger f_(ω^4)(4) − 2 claim.

## 7. BB31 / BB33
The pair-level programs are identical up to relabeling (`observed_g.py`, `obs29.txt`, `obs31.txt`, `obs33.txt`):

| role | BB29 | BB31 | BB33 |
|---|---|---|---|
| chop and copy core (B, D, F, H, K) | same | same | same |
| N-scan | N | M | N |
| P-walk | P | O | P |
| V-scan | V | W | Z |
| Y-scan | Y | Z | ] |
| return after K | ] | _ | A |
| [ | [ | \ | _ |
| depths 0..E-1 | R T \ | Q S U ] R | R T V X ` S U |
| escape (depth E) | S | T | W |

| | E | first clean config | C(1) | C(1) ordinal | events matching model |
|---|---|---|---|---|---|
| BB31 | 5 | step 196 | step 360 | ω^ω^ω^(ω^4) | 179 |
| BB33 | 7 | step 140 | step 288 | ω^ω^ω^ω^ω^(ω^3) | 280 |

- The model (with E as the only parameter) matches all random tests up to height E and fails at E+1.
- Both initial hydras have height E+1 and lose the extra level in the first chop, as in BB29.
- The TM-literal cross-checks pass for both.
- Uniform family: BB(29+2j) has E = 3+2j. Each extra depth state is one more hydra level.
- Bounds are informal (Hardy route, plus the observation that an absorbed front leaf only increases α):
  BB31: σ ≳ f_(ω^ω^(ω^4))(4) − 2 = f_(ω^ω^ω^ω)(4) − 2, above even the BB33 claim;
  BB33: σ ≳ f_(ω^ω^ω^ω^(ω^3))(4) − 2 > f_(ω↑↑6)(3).

## 8. Coq plan (BB29)
1. **Encoding.** Hydra as `list (list nat)` (root → A-nodes → leaf counts) plus the marked depth d in {0..3}, with a
   recursive `enc`. Prove enc of copy/chop results by list algebra.
2. **Atomic rules (§3a):** about 30 lemmas, each by `execute`.
3. **Scan lemmas S1–S8:** induction on the word.
4. **S9a/S9b:** induction on the t1/t2 forests.
5. **S10 COPY:** induction on s2 with invariant J. This carries all the copying; prove it first.
6. **Round lemmas R1, R1', R2, R3,** then the three hydra-level round cases, with d quantified (the next chop does
   not depend on it): successor hs++[[]] → hs (d' = 0); A-limit hs++[A0++[0]] → hs++[A0]^(m+3) (d' = 1); B-limit
   hs++[A0++[k+1]] → hs++[A0++[k]^(m+3)] (d' = 2).
7. **Processing lemma.** Good(A) := ∀ hs m d, C(m, hs++[A], d) ->* C(W A m, hs, 0). Good([]) holds.
   P(k) := ∀ A1, Good A1 → Good (A1++[k]), by induction on k. Case k = 0 uses Good A1 (m+3) times. Case k+1 uses P(k)
   iterated (m+3) times, by an inner induction on j for A1++[k]^j. Everything is structural: no ordinals, no
   well-founded recursion.
8. **Initial segment:** `execute` 175 steps from c0 to C(1, [[4]], 3), then halt via R3 with σ = W([4])(1) + 1.
9. **Bound:** the §6 lemma using `Nat.iter` functionals (stdlib only). Target statement:
   `exists c N, c0 -->* c /\ halted c /\ ones c N /\ U 3 S 3 < N`, plus a lemma U k S = f_(ω^k) for the standard
   fundamental sequences (tied to Ord.v in the Coq development).

No global termination measure is needed: the nested structural induction of step 7 (on k, then on iteration counts)
plays the role of the ordinal descent below ω^ω^ω. BB31/BB33 would follow the same plan with one more functional layer
per hydra level (a level-indexed family replacing W/T).

## 9. Open gaps (at the time of writing; see the status note at the top)
- The rules are validated by simulation only (no Coq yet).
- The Hardy-based bounds (BB29's f_(ω^4)(4) − 2 and all BB31/BB33 bounds) are informal.
- For BB31/BB33, the effect of the extra leading leaves is argued, not proved.
- Exact σ is not computed numerically (it is f_(ω^4)-sized); exact step counts were not needed.

## Files (all in this directory)
- Core: `tm.py`, `macro2.py`, `pm_full.py`, `pm.py`, `family.py`, `hydra.py`
- Checks: `blank_family.py`, `rand_family.py`, `tmcross.py` (with `tmat.cpp`/`tmat.exe`), `ordinal_check.py`,
  `ordinal_rand.py`, `formula_check.py`, `usage.py`
- Driver and log: `check_all.py`, `check_all.log`
- Viewers: `view*.py`, `dump.cpp`, `trace.py`, `tree.py`, `observed_g.py`, `obs29/31/33.txt`
