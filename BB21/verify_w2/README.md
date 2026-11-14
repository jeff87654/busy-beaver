# Coq proofs for B21's ω² bound (`0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR`, Racheline)

`multifile/` extends the halting proof in [`../verify/`](../verify/) with a quantitative layer. On top of busycoq
(commit `bd2e36f`, Coq 8.20.1), for this machine (R0 undefined = the halt, `1RZ` in the string), it proves:

- `BB21_B21_w2.halt : halts tm c0` (the same proof as `../verify/`'s `BB21_B21.halt`);
- `BB21_B21_w2.sigma_lower_bound`: 4↑↑341 < N (as in `../verify/`);
- `BB21_B21_w2.sigma_lower_bound_wsq3`: f_(ω²)(f_(ω²)(f_(ω²)(4↑↑341))) < N;
- `BB21_B21_w2.sigma_lower_bound_wsq`: f_(ω²)(f_(ω²)(4↑↑341)) < N, the bbchallenge wiki's claimed bound in its own form;
- `BB21_B21_w2.beats_J20`: J20's proved BB(20) bound f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N, stated with
  `BB20_JZ20.v`'s own definitions.

Here N is the number of ones on the halting tape, and σ = N + 1. As published:

    Theorem sigma_lower_bound_wsq3 :
      exists c N, c0 -[ tm ]->* c /\ halted tm c /\ BB21_B21_score.onesN c N /\
        BB21_B21_absdef.iter 3 BB_FGH_wa.f_wsq (BB21_B21_score.tet 341) < N.
    Theorem sigma_lower_bound_wsq :
      exists c N, c0 -[ tm ]->* c /\ halted tm c /\ BB21_B21_score.onesN c N /\
        BB_FGH_wa.f_wsq (BB_FGH_wa.f_wsq (BB21_B21_score.tet 341)) < N.
    Theorem beats_J20 :
      exists c N, c0 -[ tm ]->* c /\ halted tm c /\ BB21_B21_score.onesN c N /\
        BB20_JZ20.f_w2 (BB20_JZ20.f_wk 2 (BB20_JZ20.f_wk 2 (BB20_JZ20.f 10 2))) < N.

The fast-growing hierarchy below ω³ is defined in `BB_FGH_wa.v` in the standard way:

    f 0 = S,                  f (k+1) n = iter n (f k) n                         (f_k)
    f_wa 0 b = f b,           f_wa a (b+1) n = iter n (f_wa a b) n,   f_wa (a+1) 0 n = f_wa a n n
                                                                                  (f_wa a b = f_(ω·a+b))
    f_wsq n = f_wa n 0 n                                                          (f_(ω²), with ω²[n] = ω·n)

`BB_FGH_wa.v` also proves that these agree with the definitions in J20's and R18a's files (`f_wk_JZ`, `f_w2_JZ`,
`f_wk_R18`, `f_w2_R18`: f_wa 1 k = f_wk k, f_wa 2 0 = f_w2). That is why it loads those two proofs.
`beats_J20` compares B21 with J20's proved lower bound. Against J20_cube (the current BB(20) entry) the comparison
is with its exact score: `B21_vs_J20cube.v` (written by this project, agent claims-prover, 2026-11-13) loads
J20_cube's proof (`BB20_J20_w2_cube.v`) and the generic upper bounds of `JZ_UB.v`, byte-identical copies of
[`../../BB20/verify_j20cube/multifile/`](../../BB20/verify_j20cube/multifile/)'s, and proves
`B21_beats_J20cube_exact` and `B21_beats_J20cube_score` (NJ + 1 < N: σ(B21) > σ(J20_cube) + 1).

**How the bound is proved** (`BB21_B21_qnt*.v`, `BB21_B21_bound.v`; generic in the refill rule). Every block above the
frontier gets a potential, H-style, at its depth: the depth-j family Mq satisfies f_(ω·j) ≤ Mq_j pointwise (`Mq_fgh`).
The potential never exceeds the future value of B0min (B0's guaranteed length), which never decreases. `proc_q` is
the quantitative form of `../verify/`'s `proc`. A phase that walks the marker P through k lone 2s ends with
f_(ω²)(k) ≤ B0min (`PhiR_fwsq`, `phi_loop_q`, `two_to_phi_q`, `phase_from_work_q`). Phases 4, 5 and 6 each apply
f_(ω²), and the losses at each refill (a factor 4) are absorbed by `fwsq_S` (`chain_step`, `chain_last`,
`abstract_final_q`). `J20_le` puts J20's bound below f_(ω²)(f_(ω²)(T)) for T ≥ 10.

## Files (in dependency order)

| file | content |
|---|---|
| `BB202.v`, `Individual202.v`, `BB20_JZ20.v` | J20's proof, **byte-identical** to [`../../BB20/verify/multifile/`](../../BB20/verify/multifile/)'s |
| `BB182.v`, `Individual182.v`, `BB18_R18a.v` | R18a's proof, **byte-identical** to [`../../BB18/verify_r18a/multifile/`](../../BB18/verify_r18a/multifile/)'s |
| `BB212.v`, `Individual212.v`, `BB21_B21_{absdef,tm,sim,grow,steps,inv,proc,phase,run,score}.v` | B21's halting proof, **byte-identical** to [`../verify/multifile/`](../verify/multifile/)'s (everything except its headline `BB21_B21.v`) |
| `BB_FGH_wa.v`, `BB_FGH_wa2.v` | f_(ω·a+b) and f_(ω²), basic facts, agreement with J20's and R18a's definitions, the growth and chain lemmas, `J20_le` |
| `BB21_B21_qnt.v` to `BB21_B21_qnt4.v` | potentials, B0min bookkeeping, quantitative frontier processing (`proc_q`) and phases (`phase_from_work_q`) |
| `BB21_B21_bound.v` | phases 4 to 6, `sigma_lower_bound_wsq3`, `sigma_lower_bound_wsq`, `beats_J20_bound` |
| `BB21_B21_w2.v` | the table and the five headline theorems |
| `BB20_J20_w2_cube.v`, `JZ_UB.v` | J20_cube's proof and the generic upper bounds, **byte-identical** to [`../../BB20/verify_j20cube/multifile/`](../../BB20/verify_j20cube/multifile/)'s |
| `B21_vs_J20cube.v` | `B21_beats_J20cube_exact`, `B21_beats_J20cube_score` |
| `probe.v` | the independent probe (below) |
| `share_check.sh` | checks that the 20 copied files are byte-identical to the published ones |
| `compile_clean.sh`, `_CoqProject` | build script (runs `share_check.sh` first when the other trees are present), project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 5 minutes) and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table of `BB21_B21_w2.tm` against the machine string
entry by entry (42 checks generated from the string, not from the Coq file) and the blank start configuration. It
prints the definitions the statements use (including `f`, `f_wa`, `f_wsq` and J20's `f_wk`, `f_w2`) and runs
`Print Assumptions` on the five theorems above and on the two comparisons with J20_cube: all seven are closed under the global context. CI job `bb13-bb14` runs
the same script.

The proof was also checked with this project's `check.py` (21 states: the statement `halts tm c0` read from the file,
the table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-08.
