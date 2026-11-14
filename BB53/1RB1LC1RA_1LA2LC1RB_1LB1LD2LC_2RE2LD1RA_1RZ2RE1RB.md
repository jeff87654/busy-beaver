# 53-Main: a BB(5,3) machine above 2 ↑^x x, x = 2 ↑^7 7

```
1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB
```

Found by **Argon** (a Google Gemini model run by the repository owner) on 2026-11-09, with the Coq proof; re-checked
and packaged here on 2026-11-13. "53-Main" is Argon's name for it.

| | 0 | 1 | 2 |
|---|---|---|---|
| A | `1RB` | `1LC` | `1RA` |
| B | `1LA` | `2LC` | `1RB` |
| C | `1LB` | `1LD` | `2LC` |
| D | `2RE` | `2LD` | `1RA` |
| E | `1RZ` | `2RE` | `1RB` |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `bb53_halts`. The halting transition is E0 = `1RZ`. |
| Score | σ = 2·M + 6 nonzero cells after the halting write, for an explicit M (`M53_final`, below; not evaluated). |
| Bounds | Machine-checked, with **F(n) = 2 ↑^n n** (`f_omega` in `BB53_bound.v`, defined there; not the fast-growing hierarchy's f_ω): F(F(7)) < σ and F(2 ↑^8 3) < σ (`sigma_exceeds_f_omega2`); also 2 ↑↑↑ 2 ↑↑↑ 2 ↑↑↑ 2^96 < σ (`sigma_beats_official_bb43`). In arrows: **2 ↑^x x < σ with x = 2 ↑^7 7**. |
| FGH reading (on paper) | F(n) is below the FGH f_ω(n) for n = 2, 3 and above it from n = 4 on, so f_ω(f_ω(7)) < σ for the FGH f_ω. |
| Steps | Not computed. |
| Wiki | The bbchallenge wiki's Champions page (read 2026-11-13) has no BB(5,3) champion (the row is empty). |

## How it works

53-Main is a 3-symbol version of the Ackermann engine of Kropitz's BB(3,4) champion (Ligocki's configurations and
`g` hierarchy). Its configurations are

    B(k, n, m, r) = 0^inf 2^(2m+1) 1^k  B>  1^n r

with g_0(m) = m + 1, g_(k+1)(m) = g_k^(2m+2)(0) and the descent B(k+1, n, m, r) →* B(k+1, 0, g_k^n(m), r)
(`B_rule`); 2 ↑^k-closed forms as for the 4-symbol machines. Further macros (all in `BB53_rules.v`):

    0^inf 2^J 1 B> 0^inf  -->*  0^inf 2^4 1^(J+1) B> 1 1 0^inf                     (lift_from_1)
    0^inf 2^4 1^(j+2) B> 1 1 0^inf  -->*  B(j+2, 0, g_(j+1)(g_j^5(0)), 0^inf)      (even_round)
    B(k+3, 0, m, 0^inf)  -->*  B(k+1, 0, g_k^(2m+4)(0), 0^inf)                     (K_drain_step)
    B(2, 0, m, 0^inf)  -->*  0^inf 2^(2m+5) E> 0^inf                                (halt_from_2)

`K_drain_step` lowers the level by 2, so an odd level drains to 1 and lifts again (`lift_from_1`, which makes the
new level J + 1 from the 2^J block), and an even level drains to 2 and halts. The run:

    0^inf A> 0^inf  -(113 steps)->  0^inf 2^4 1^9 B> 1 1 0^inf                     (start53_to_round2)
        ->  B(9, 0, M2_0)            M2_0 = g_8(g_7^5(0))                           (even_round)
        ->  B(1, 0, M2_4)            four drains, 9 → 7 → 5 → 3 → 1                (K_drain_step)
        ->  0^inf 2^4 1^(2·M2_4+2) B> 1 1 0^inf                                    (lift_from_1, J = 2·M2_4 + 1)
        ->  B(2·M2_4+2, 0, M3_0)     M3_0 = g_(2·M2_4+1)(g_(2·M2_4)^5(0))           (even_round)
        ->  B(2, 0, M)               M = M53_final, drains to level 2               (K_drain_even)
        ->  0^inf 2^(2M+5) E> 0^inf  -(E0 = 1RZ)->  halt                            (halt_from_2)

The tape after the halting write is 2^(2M+5) 1, so σ = 2M + 6. The first round already gives 2·M2_4 ≥ F(7) and
≥ 2 ↑^8 3; the second round runs at level 2·M2_4, so 2·M3_0 + 4 ≥ F(2·M2_4) (`M3_0_ge_fomega`), and M ≥ M3_0.

## Proof

The Coq files are Argon's ([`verify/`](verify/)): `BB53.v`, `Individual53.v` (busycoq instantiated for 5 states and
3 symbols, the same template as the published BB(4,4) and BB(5,4) instantiations), `BB53_rules.v` (sweeps,
`turnaround`, `B_rule`, `lift_from_1`, `even_round`, `K_drain_step`, `K_drain_even`, `halt_from_2`, the 113-step
start), `BB53_run.v` (the sealed constants M2_0 … M2_4, M3_0, M53_final, `reaches_final`, `final_halted`,
`bb53_halts`, the final tape and its count), `BB53_bound.v` (Knuth arrows, F, `sigma_exceeds_f_omega2`,
`sigma_beats_official_bb43`, `bb53_new_champion_main`, everything in one statement).

The name `sigma_beats_official_bb43` is Argon's. Its statement, 2 ↑↑↑ 2 ↑↑↑ 2 ↑↑↑ 2^96 < σ, is the shape of the
*lower* bound of the BB(4,3) entry (Kropitz's machine, σ = 4·e₄ + 18 with
2 ↑↑↑ 2 ↑↑↑ 2 ↑↑↑ (2^96 − 1) < e₄ ≤ 2 ↑↑↑ 2 ↑↑↑ 2 ↑↑↑ (2^96 + 6)), not a comparison with that machine's σ. On paper,
BB(4,3)'s σ ≤ 4·(2 ↑↑↑ 2 ↑↑↑ 2 ↑↑↑ (2^96 + 6)) + 18 is far below F(7) = 2 ↑^7 7, so 53-Main is far above BB(4,3) + 1.

Score convention: σ counts the nonzero cells of the explicit tape after the halting write; `final_cells` is that tape
read off `c_final`, and this reading is not itself a Coq lemma (as in the other multi-symbol entries).

## Verification

- [`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1. `probe.v` checks the 15 transitions against the string above
  (generated from the string, not from the Coq file), prints the definitions (`knuth`, `f_omega`, `sigma`,
  `final_cells`, `c_final`, `Bcfg`, `g`) and runs `Print Assumptions` on 8 theorems: all closed under the global
  context. CI job `bb53`.
- Literal checks (argon-scout-2, outside this repository): the machine reaches the round-2 entry 2^4 1^9 B> 1 1 at
  step 113; `lift_from_1` (J = 0..7), `K_drain_step` and `halt_from_2` (m = 0..4) were checked against the literal
  machine.

## Credit

Machine and Coq proof: **Argon** (Google Gemini, run by the repository owner in Google's Antigravity), 2026-11-09, on
the engine of Pavel Kropitz's BB(3,4) champion as analysed by Shawn Ligocki. Probe, re-check and packaging: this
project, 2026-11-13. Not yet reviewed by the bbchallenge community.
