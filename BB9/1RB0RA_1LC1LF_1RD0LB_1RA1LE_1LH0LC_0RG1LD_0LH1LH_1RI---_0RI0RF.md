# C04: a 9-state machine with f_ω(f_ω(f_ω(12))) < σ < f_ω(f_ω(f_ω(13)))

    1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF

> **Now the proof base of the BB(8) entry (2026-10-18).** The 8-state machine M8
> ([`../BB8/1RB0RA_..._0RG0RF_1RG---.md`](../BB8/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---.md)) is
> reduced from C04 by collapsing its F0/G/H0 gadget into one transition; it halts on the same tape with the same score.
> So C04 is not a BB(9) entry (a 9-state record must beat M8). It is kept here as the machine whose Coq proof M8's
> is built on.
> The BB(9) entry is now f3_0RC
> ([`1RB0RA_..._0LI---_0RC1RF.md`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF.md)), whose
> Coq proof also reuses this development (2026-10-21).

Below we call this machine **C04** (its label in the search that found it, section 5). It halts from the blank tape,
and Coq proves, with no axioms and with the standard fast-growing hierarchy, that its score σ satisfies

    f_ω(f_ω(f_ω(12))) < σ < f_ω(f_ω(f_ω(13)))        (c04_fgh3)

More precisely, f_ω(f_ω(12B + 26)) < σ < f_ω(f_ω(12B + 27)) with 2B + 4 = 2↑^13 3 (`c04_fgh_bracket`, `Bx_knuth`;
f_ω(12) < 12B + 26 and 12B + 27 ≤ f_ω(13), `Bx_fw`). As an easier placement, f_(ω+1)(3) < σ < f_(ω+1)(4), where
f_(ω+1)(n) = f_ω^n(n) (`c04_fgh_coarse`). Coq also gives σ exactly, as an explicit symbolic recursion along the run (`c04_score_exact`); its value depends on all base-5
digits of B and cannot be evaluated in practice. σ exceeds the **exact** score of fw2
([`1RB0RD_..._1RZ1RA`](1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA.md)), the previous BB(9) entry of
this folder (`c04_beats_fw2`). It does not beat our 10-state machine n1 ([`../BB10/`](../BB10/)),
which is far up level f_(ω+1). Written 2026-10-18.

C04 runs the BB(7) champion's digit-list counter, like our earlier BB(9) record, and starts exactly as that record does.
It differs only in what happens when the digit list is used up (transition E0). The first time, it rebuilds a list of
12B + 25 digits from the counter B, where 2B + 4 = 2↑^13 3, and clearing that list gives a counter R₂ with
2R₂ + 4 = 2↑^(12B+26) 4 (the first f_ω-sized step). The second time, it parks a list of 12R₂ − 10 digits and starts a
**cascade**: one orbit of the 5-adic map L → (3L + c)/5, which shrinks L by a factor of about 3/5 per step, from
L₀ = 36B + 73. Where the orbit first drops below 60 depends on all base-5 digits of B and cannot be computed. But all
the constants c are even, so L stays odd, and every odd entry point leads to a clear of the parked list (the second
f_ω-sized step) and then to the halt. The even entry points, which would halt before that second step, are never
reached.

|   | 0   | 1   |                         |
|---|-----|-----|-------------------------|
| A | 1RB | 0RA |                         |
| B | 1LC | 1LF |                         |
| C | 1RD | 0LB |                         |
| D | 1RA | 1LE |                         |
| E | 1LH | 0LC |                         |
| F | 0RG | 1LD |                         |
| G | 0LH | 1LH |                         |
| H | 1RI | --- | H1 is undefined: the halt |
| I | 0RI | 0RF |                         |

**Main facts.** N is the number of 1s on the tape when the machine is in state H reading 1. The cell under the head
already holds a 1, so whatever 1 the halting transition is taken to write (the usual convention is 1RZ), the score is
σ = N.

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `c04_halts : halts tm c0`. |
| Score | **f_ω(f_ω(f_ω(12))) < σ < f_ω(f_ω(f_ω(13)))**, machine-checked with the standard fast-growing hierarchy (`c04_fgh3`). |
| More precisely | f_ω(f_ω(12B+26)) < σ < f_ω(f_ω(12B+27)), 2B + 4 = 2↑^13 3, machine-checked (`c04_fgh_bracket`, `Bx_knuth`, `Bx_fw`). |
| Coarse placement | f_(ω+1)(3) < σ < f_(ω+1)(4), f_(ω+1)(n) = f_ω^n(n), machine-checked (`c04_fgh_coarse`). |
| Exact score | Machine-checked: σ = `sigma_c04`, an explicit recursion along the cascade (`c04_score_exact`, `c04_score_reached`). Not evaluated as a number: it depends on where the cascade orbit enters [0, 60), which depends on all base-5 digits of B. |
| Weaker lower bound, used for the comparison | f_ω(f_ω(465009)) < σ (`c04_sigma_lower_bound`). |
| fw2 (the previous BB(9) entry, superseded) | **Beaten**, machine-checked against fw2's Coq-proved exact score: fw2 halts with N_f ones and N_f + 1 < N, and N_f + 1 is fw2's score (`c04_beats_fw2`). |
| The five machines fw2 beats (our earlier BB(9) record, two later 9-state machines of this project, Jacobzheng's 2024 BB(9) champion, Racheline's 2024 BB(10) champion) | Beaten, by combining `c04_beats_fw2` with fw2's five Coq comparisons (`fw2_beats_*`, [`verify_fw2/`](verify_fw2/)). Each step is machine-checked; the combination (one inequality, using that each machine has one halting configuration) is not stated as a Coq theorem. |
| n1 ([`../BB10/`](../BB10/), f_(ω+1)) | **Not** beaten. |
| Steps | Not computed. The first 2369 are in the Coq proof. |

---

## 1. How it works

### 1.1 Notation

- `0^∞` is the blank part of the tape, and `x^n` is n copies of the word x. `B>` is state B with the head on the cell
  to its right.
- D(x) = (10)^x 1 is a token. Tokens x ≡ 1 (mod 3) are **digits**, of value (x − 1)/3. The zero digit is D(1) = 101,
  and `1^k` below means k zero digits.
- The configurations of the counter are

      Kt(d_n … d_1; m; r; t) = 0^∞ 11 D(d_n) … D(d_1) D(m) (10)^r 11 (11111100)^t 1001 B> 0^∞

  with the list d_n … d_1 written far to near (the far `11` is written as the two tokens `0,0`). This is `Kt` in
  `dev/Abs.v`; `Kg ds suf a b t` is the same with digits given by value, m = 3a + 1 and r = 3b + 2.

### 1.2 The counter (shared with the BB(7) champion)

States A–D, E1 and F1 are those of the BB(7) champion `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF` (Kropitz
2025). C04's F0, G and H0 together do what the champion's F0 = 1RG does, in three steps instead of one: F writes 0 and
moves right, G writes back what it reads and moves left, and H, which always reads the 0 that F has just written, writes
1 and moves right. I = 0RI 0RF is the champion's G. So every computation of the champion that does not read E0 is
reproduced step for step, with 2 extra steps per use of F0, and H1 is read only in a situation the champion never
meets.
In particular the champion's rules R1–R3 (count down the near digit, borrow from the next one) and its clearing functions
hold verbatim. Clearing a digit list of depth j with accumulator x gives U_j(x), where

    U_0(x) = 2^(2x+3) − 2,    U_(j+1)(x) = U_j^(2x+2)(0),    2·U_j(x) + 4 = 2↑^(j+1)(2x + 4).

E0 is read exactly when the digit list is used up (an all-zero list), which is where the champion halts. C04 instead
re-encodes the accumulator and the list and keeps going (an **exhaustion**).

### 1.3 Level 0 and the first exhaustion

- From the blank tape the machine reaches Kt(1^10, 7; 1; 2; 0) at step 2369, and the champion's clearing gives
  Kt(1^11; 1; 3B+2; 0) with B = U_10(U_10(0)), 2B + 4 = 2↑^13 3. This is the same B as in our earlier BB(9) record
  (`1RB0RA_..._0LH1RZ`, this folder), which starts the same way. B ≡ 1 (mod 5) and B is even.
- **Exhaustion #1** rebuilds a list from the counter: for every b ≥ 6,
  Kt(1^11; 1; 3b+2; 0) →⁺ Kt(0,0, 7, 1^(12b+24); 1; 2; 3).
- Clearing the digit 7 and the 12B + 24 zeros gives the accumulator R₂ = U_(12B+24)(U_(12B+24)(0)), with
  2R₂ + 4 = 2↑^(12B+26) 4: the first f_ω-sized step.

### 1.4 The second exhaustion and the cascade

An exhaustion of a zero list 1^n turns the list into a run whose length L is 3n − 2 at the far end of the tape (no
tokens to its left) and 3n − 5 otherwise. At the far end (only exhaustion #2) the accumulator R₂ becomes a **parked
list** of 12R₂ − 10 zero digits next to the run. Then, while L ≥ 60, a sub-step looks at r = L mod 5:

| r | new L | written to the left |
|---|---|---|
| 1 | (3L + 32)/5 | separator `4 5` and a token (L − 21)/5 |
| 2 | (3L − 46)/5 | separator `2` and a token (L + 3)/5 |
| 3 | (3L − 64)/5 | separator `6` and a token (L + 7)/5 |
| 4 | (3L − 52)/5 | separator `4` and a token (L + 11)/5 |
| 0 | stop | the run becomes a digit (L + 10)/5 followed by (L − 30)/5 zero digits |

Each sub-step also takes at most 11 zero digits off the parked list and adds 3 tail blocks (11111100). After a stop the
champion's rules clear the new digit list (a new accumulator R_i, which is parked as an inert token 6R_i + 9 or
6R_i + 12, a multiple of 3 and so never a digit). The next exhaustion then starts at L' = (3L − 100)/5. So the whole
cascade, over all its exhaustions, is one orbit of

    g(L) = (3L + c_(L mod 5))/5,    c_1 = 32, c_2 = −46, c_3 = −64, c_4 = −52, c_0 = −100 (stop),

started at L₀ = 36B + 73 (`Orbit.gstep`). Every step shrinks L by a factor of about 3/5, so the cascade has about
log_(5/3)(36B) steps, a tower-sized number, but each takes at most 14 digits off the parked list, which is far longer.
The accumulators of the cascade clears (depth below B) are far smaller than R₂, and they stay on the tape as inert
tokens.

### 1.5 Parity: why the run reaches the second escalation

For L ≥ 60 (`Orbit.v`):

- g(L) ≡ L (mod 2), because every c_r is even (`gstep_mod2`);
- g(L) ≡ 1 (mod 3), because 2c_r ≡ 2 (mod 3) for every r (`gstep_mod3`);
- g(L) < L (`gstep_lt`).

L₀ = 36B + 73 is odd and ≡ 1 (mod 3), and L₀ ≡ 4 (mod 5) because B ≡ 1 (mod 5). So every value of the orbit is odd and
≡ 1 (mod 3), and the first value below 60 (the **key**) is one of 31, 37, 43, 49, 55 (`gstep_key`, a finite check
over L < 135). Which one it is depends on all base-5 digits of B and cannot be computed. An even key would lead to a
halt before the parked list is used (for example 46 → 34 → 10, which halts with a score of about f_ω(12B), below fw2),
but even values never occur. Before this invariant was found, C04 was classified as "Collatz-hard" (section 5).

### 1.6 The endgame

From each key the run uses up its near list and reaches the parked list, leaving a digit 7 (value 2) in front of it.
Clearing that digit across the whole parked list, at depth K ≥ 11R₂, is the **second escalation** (the "ESC" clear):
its accumulator is R_E = U_K(U_K(0)). Then:

- **Keys 37, 43, 49, 55** ("class b"). 37 and 43 go to 13 in one sub-step, 55 stops and its next exhaustion starts at
  13, and 49 goes to 19. From 13 or 19 a fixed sequence (entry, ESC with the tokens `6 7`, a counter 6 → 3 → 0 with two
  more clears of the token T = 6R + 7) ends with E0 read where H then reads a 1: the halt.
- **Key 31.** 31 goes to 25, which is not a stop; the run then reaches the parked list with the tokens `2 7`. After the
  ESC clear one more sub-step runs on the parked list, and the continuation has five forms, one for each residue of K
  mod 5. They are built from counter modes, in which each clear of T = 6R + 7 takes 3 off a counter C (every counter
  produced is ≡ 0 mod 3), two-digit clears (K ≡ 1, 3) and one nested counter (K ≡ 4), and each ends in the halt. Coq
  proves all five, the counters by induction on C (`k31/K31_End.v`).

### 1.7 The score

At the halt the tape still holds a token 6R_last + 7 (or, in one key-31 case, the token 6R_E + 1), where R_last ≥ R_E,
so the tape has at least 6R_E + 2 ones. Here R_E = U_K(U_K(0)) ≥ f_ω(K) and K ≥ R₂ ≥ f_ω(12B + 26), which gives the
lower half of the bracket. For the upper half: the halting configuration is unique, every clear in the run happens at
depth at most 12R₂ + 11, and so every quantity on the halting tape is bounded by iterates of one U at that depth. This
gives σ < f_ω(12R₂ + 45), and 64R₂ < f_ω(12B + 27). The weaker bound f_ω(f_ω(465009)) < σ used for the comparison
with fw2 follows from K ≥ 11R₂ and f_k ≤ U_k.

---

## 2. The run

| stage | configuration reached | Coq |
|---|---|---|
| blank tape, 2369 steps | Kt(1^10, 7; 1; 2; 0) | `Abs.init_reach` |
| champion clearing | Kt(1^11; 1; 3B+2; 0), 2B + 4 = 2↑^13 3 | `Abs.run_to_exhaustion` |
| exhaustion #1 (rebuild) | Kt(0,0, 7, 1^(12B+24); 1; 2; 3) | `Chain.KRebuild` (machine lemmas `G_reb1.v`) |
| clear (first escalation) | Kt(0,0, 1^(12B+25); 1; 3R₂+2; 3) | `Chain.reach_exh2` |
| exhaustion #2: park 1^(12R₂−10), first sub-step from L₀ = 36B + 73 | the cascade moment at L₁ = g(L₀) | `Step.reach_top` (`G_top.v`) |
| the cascade: one orbit step per sub-step or stop | the cascade moment at g(L), parked list ≥ Pm + L | `Step.casc_stepP` (`G_sub2`–`G_sub5`, `G_stop`, `G_entry`), `Cascade.cascade_from_start` |
| the key | 31, 37, 43, 49 or 55 | `Orbit.gstep_key` |
| endgame, keys 37/43/49/55 | ESC, counter 6 → 3 → 0, halt | `Endgame.casc_key`, `CBtail.classb_tail` (`G_end`, `G_p14_*`, `G_p20_*`) |
| endgame, key 31 | ESC, one of five forms by K mod 5, counters, halt | `K31_End.k31_end` (`K_e1`, `K_e2`, `K_x`, `K_rf`) |

---

## 3. The score

### 3.1 What Coq proves

    c04_fgh3              : forall c N, c0 -->* c -> halted tm c -> ones c N ->
                              f_omega (f_omega (f_omega 12)) < N /\ N < f_omega (f_omega (f_omega 13))
    Bx_fw                 : f_omega 12 < 12 * Bx + 26 /\ 12 * Bx + 27 <= f_omega 13
    c04_fgh_bracket       : forall c N, c0 -->* c -> halted tm c -> ones c N ->
                              f_omega (f_omega (12 * Bx + 26)) < N /\ N < f_omega (f_omega (12 * Bx + 27))
    c04_fgh_coarse        : forall c N, c0 -->* c -> halted tm c -> ones c N -> f_w1 3 < N /\ N < f_w1 4
    c04_score_exact       : forall c N, c0 -->* c -> halted tm c -> ones c N -> N = sigma_c04
    c04_score_reached     : exists c, c0 -->* c /\ halted tm c /\ ones c sigma_c04
    c04_sigma_bracket     : f_omega (f_omega (12 * Bx + 26)) < sigma_c04 /\
                              sigma_c04 < f_omega (f_omega (12 * Bx + 27))
    Bx_knuth              : 2 * Bx + 4 = arrow 13 2 3
    R2_knuth              : 2 * R2 Bx + 4 = arrow (12 * Bx + 26) 2 4
    c04_sigma_lower_bound : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
                              f_omega (f_omega (465 * 1000 + 9)) < N
    c04_beats_fw2         : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
                              BB9_fw2_bound.f_omega (BB9_fw2_bound.f_omega (465 * 1000 + 9)) < N /\
                              exists cf Nf, c0 -[ BB9_fw2_1RB0RD.tm ]->* cf /\ halted BB9_fw2_1RB0RD.tm cf /\
                                BB9_fw2_bound.ones cf Nf /\ Nf + 1 < N

`ones c N` says that the tape of c is a finite word padded with 0s on both sides, holding N ones. `f`, `f_omega` and
`ones` are fw2's definitions (`f 0 n = n+1`, `f (k+1) n = (f k)^n n`, `f_omega n = f n n`); the probe checks that the
copies C04's files use are convertible to them. `f_w1 n = iter n f_omega n` is f_(ω+1)(n), and `arrow k a b` is
a ↑^k b (`arrow 0 a b = a·b`). `Bx` is B = U_10(U_10(0)) and `R2 Bx` is R₂. `sigma_c04` runs the cascade recursion
(one orbit step of g at a time, tracking the tail, the run, the parked list and the tokens written) from the top of the
cascade until L < 60, and then applies the formula of the key's route; `c04_score_exact` and `c04_score_reached` say
that this is the number of ones of the (unique) halting configuration. fw2 halts in state I reading 0 and its halting transition writes a 1,
so fw2's score is N_f + 1, and N_f + 1 < N says that C04's score is larger.

The comparison with fw2 uses fw2's own Coq files unchanged (`BB9_fw2_1RB0RD.v`, `BB9_fw2_bound.v`) and an upper bound
on fw2's exact score b₃ + 3 proved here (`score/Fw2Upper.v`: b₃ + 5 ≤ U_K(0) for K ≥ R₂). So C04 beats fw2's exact score,
not only its published lower bound.

### 3.2 How large

The bracket f_ω(f_ω(12B + 26)) < σ < f_ω(f_ω(12B + 27)) is machine-checked (`c04_fgh_bracket`), with
2B + 4 = 2↑^13 3 (`Bx_knuth`), so 12B + 26 = 6·(2↑^13 3) + 2: the inner argument is pinned between two consecutive
integers. In terms of f_(ω+1)(n) = f_ω^n(n), C04 lies between f_(ω+1)(3) and f_(ω+1)(4) (`c04_fgh_coarse`), since
f_ω(3) ≤ 12B + 26 and 12B + 27 ≤ f_ω(f_ω(4)). On paper, a finer analysis of the endgame cases (written before the proof, not
machine-checked) gives σ = f_ω(K + 1 + θ) with 0 < θ < 2, where K, the depth of the ESC clear, lies between
2↑^(12B+26) 4 and 12R₂ − 10.

### 3.3 Comparisons

- **fw2** (`1RB0RD_..._1RZ1RA`, the previous BB(9) entry, f_ω(f_ω(465009)) < σ): beaten, machine-checked against its
  exact score (`c04_beats_fw2`).
- **The five machines fw2 beats** ([fw2's write-up](1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA.md),
  section 3.3): our earlier BB(9) record `1RB0RA_..._0LH1RZ`, the 9-state machines `..._1LC0RH_1RG1LF_---0LA` and
  `..._1LC1RH_0LH0RF_---0LA`, Jacobzheng's BB(9) champion and Racheline's BB(10) champion. Each is beaten by fw2
  in Coq, and fw2 is beaten by C04 in Coq, so C04 beats them. The chaining is on paper.
- **n1** ([`../BB10/`](../BB10/), 10 states, f_(ω+1)(…) < σ): not beaten. f_ω∘f_ω of anything of this size is far
  below n1's score.

---

## 4. Verification

### 4.1 What Coq proves

The development is in [`verify_c04/`](verify_c04/): 56 `.v` files (15.5 MB, 81,000 lines), Coq 8.20.1 on top of
[busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`). No axioms.

| statement | Coq name | file |
|---|---|---|
| C04 halts from the blank tape | `c04_halts : halts tm c0` | `dev/Final.v` |
| the halting tape has N ones, f_ω(f_ω(465009)) < N | `c04_sigma_lower_bound` | `dev/ScoreEnd.v` |
| the same, and fw2 halts with N_f ones, N_f + 1 < N | `c04_beats_fw2` | `dev/ScoreEnd.v` |
| every reachable halting configuration has N ones with f_ω(f_ω(12B+26)) < N < f_ω(f_ω(12B+27)) | `c04_fgh_bracket` (also `c04_fgh_exists`) | `fgh/EndU.v` |
| the same N satisfies f_(ω+1)(3) < N < f_(ω+1)(4) | `c04_fgh_coarse` | `fgh/EndU.v` |
| N = `sigma_c04`, the exact symbolic score, and it is reached | `c04_score_exact`, `c04_score_reached`, `c04_sigma_bracket` | `fgh/Exact.v` |
| 2B + 4 = 2↑^13 3 and 2R₂ + 4 = 2↑^(12B+26) 4 | `Bx_knuth`, `R2_knuth` | `fgh/FArith.v` |
| f_ω(12) < 12B + 26, 12B + 27 ≤ f_ω(13), hence f_ω(f_ω(f_ω(12))) < N < f_ω(f_ω(f_ω(13))) | `Bx_fw`, `c04_fgh3` (also `Bx_fw_tight2`: (12, 13) is the tightest such pair) | `fgh/Headline.v` |

How the proof is put together:

- **Generated machine lemmas** (26 files, 15.2 MB, about 10,000 lemmas, `dev/G_*.v`, `k31/K_*.v`). A symbolic executor
  followed the machine through each phase of the rules above, with the run lengths as variables, and wrote one busycoq
  lemma per phase, proved by stepping the machine (`execute`, `follow`, `step`) and by induction for each repeated block.
  Lemmas whose parked length enters a block encoding come in six versions, one per residue of that length mod 6
  (`G_p14_0` … `G_p14_5`, the `AS*_0` … `AS*_5` cases of `Step.v`).
- **Level 0 and the rebuild** (`Abs.v`, `Chain.v`): the champion's rules and clearing on the token family, `U` and the
  arrow identities, B, B ≡ 1 (mod 5), the first 2369 steps, exhaustion #1 and the clear to R₂.
- **The cascade** (`Lift.v`, `Step.v`, `Orbit.v`, `Cascade.v`, `Fin.v`): the machine lemmas are restated on one abstract
  cascade moment `D0f t L P s y l` (L the run, P the parked list, t the tail blocks); `casc_stepP` is one orbit step
  for the reachability predicate "a cascade moment at orbit value L is reached from the blank tape, with parked list
  ≥ Pm + L", covering the four sub-steps and the stop with its clear and the next entry. `Orbit.v` has the map g and the
  parity and key facts; `Cascade.cascade_from_start` is the well-founded induction on L; `Fin.v` carries a finite far
  side along, so that the halting tape is a finite word.
- **The endgame** (`Endgame.v`, `CBtail.v`; `k31/`): keys 37, 43, 49, 55 through the 12 entry prefixes and the class-b
  tail; key 31 through `K31_End.k31_end` (entry, the ESC clear, the five post-ESC forms, the counter by induction, the
  two-digit clears, the halt).
- **The score** (`score/`, `ScoreEnd.v`): every key ends at the same halting tape with at least 6R_last + 2 ones and
  R_last ≥ U_K(U_K(0)), K ≥ 11R₂ (`ScoreK.K_ge_R2`); `Score.v` proves f_k ≤ U_k and f_ω(f_ω(465009)) < U_K(0);
  `Fw2Link.v` links the hierarchy to fw2's constants; `Fw2Upper.v` bounds fw2's exact score.
- **The bracket and the exact score** (`fgh/`; no new machine lemmas, it reuses the compiled dev, k31 and score files):
  `FArith.v` has the hierarchy arithmetic (f_(k+2)(n) ≤ U_k(n), U_j(x) < f_(j+2)(2x + 4), B and R₂ in Knuth arrows,
  the two chains of inequalities); `Tower.v` the scale of iterates of one U that bounds every tape quantity; `Uniq.v`
  the uniqueness of the halting configuration and the exact ones count of the final tape; `CascU.v` the cascade
  invariant with upper bounds (parked list ≤ 12R₂ + 11, run and tokens bounded); `EndU.v` every endgame route ending
  in an explicit tape, and the bracket; `Exact.v` the recursion `sigma_c04` and its correctness.

`verify_c04/probe.v` checks by conversion all 18 entries of the transition table against lines generated from the
machine string (H1 is `None`) and the blank start configuration, checks the types of all the theorems above written
out with fully qualified names (the fgh ones as one conjunction, `c04_fgh_all_ok`), checks that the `ones` and
`f_omega` used are fw2's, prints the definitions (including `sigma_c04`), and runs `Print Assumptions` on the three
main theorems, on the conjunction, and on the headline conjunction `c04_headline_ok` (`Bx_fw`, `Bx_fw_tight2`,
`c04_fgh3`). All five report "Closed under the global context".

**Build.** `verify_c04/compile_clean.sh` builds everything from scratch in dependency order, J files at a time, and
runs the probe. The whole build is about 3.2 CPU-hours on a GitHub runner (the longest file, `k31/K_e1.v`, takes about
35 min on its own), about 1 h 40 min there with 4 coqc in parallel. The GitHub workflow (job `bb9-c04`) builds all of it from scratch whenever its files change
(and weekly) and fails unless the probe reports five axiom-free results. The recorded local clean build and its times
are in [`verify_c04/README.md`](verify_c04/README.md).

### 4.2 Not machine-checked

- **σ = N.** In Coq the halt is the undefined transition H1 and `ones` counts the 1s of the halted configuration. The
  head reads a 1 there, so the conventional final write does not change the count.
- **The finer estimate** σ = f_ω(K + 1 + θ) of section 3.2, and the comparison with n1.
- **The chaining** of `c04_beats_fw2` with fw2's comparison theorems (section 3.3).
- **The descriptions** of sections 1–2 (the token pictures, the sub-step table, the key-31 forms) summarize what the
  Coq lemmas state; only the lemmas are checked.

### 4.3 Before the proof

C04's rules were found and checked by literal simulation before any Coq was written: the sub-step rule on 62 randomized
contexts and 280 chains, the endgame from every key route in several hundred contexts, and end-to-end runs from
exhaustion #2 to the halt in small worlds (tower-sized quantities replaced by representatives with the right residues).
None of this is needed for the proof.

---

## 5. Discovery and credit

- **Found** in this project's search for 9-state machines of the n1 type: C04 was one of the parked leads of the n1f0
  enumeration (the 9-state tree-normal-form completions of `1RB0RA_1LC1LF_1RD0LB_1RA1LE_---0LC_0RG1LD_------_------_------`,
  394,166 holdouts). Opus agents found the first escalation and the 5-adic cascade map, and classified it as probably
  Collatz-hard.
- **Analysed** by a Fable agent (c04-fable, 2026-10-17), which found the parity invariant, the key set and the endgame,
  and wrote the proof sketch. Agent c04-upper derived the bracket of section 3.2 on paper first.
- **Proved** in Coq by Opus agents, 2026-10-17/18: c04-coq and c04-coq2 (the machine lemmas, the cascade, the class-b
  endgame, the final theorems), c04-k31 (the key-31 endgame), c04-bound (the score arithmetic and the bound on fw2's
  exact score), and agent c04-fgh (`fgh/`: the two-sided bracket, the coarse placement and the exact score). The lead
  re-checked every theorem with `Print Assumptions`, and the development was rebuilt from scratch
  for this folder (section 4.1).
- **Built on** the BB(7) champion of Kropitz (2025; analysed by Ligocki), whose counter C04 runs, and on our earlier
  BB(9) record, whose start-up it shares and whose Coq development supplied the token family and the clearing lemmas.
- **fw2**, the machine C04 is compared with, is Argon's (a Google Gemini model run by the repository owner; see its
  [write-up](1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA.md)). Its Coq files are used unchanged.
