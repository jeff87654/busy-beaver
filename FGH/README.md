# The multi-symbol entries in the fast-growing hierarchy

The multi-symbol entries are proved in Knuth's arrow notation (their own directories). The files here restate their
bounds in the standard fast-growing hierarchy of `Ord.v` (the same definitions as the hydra entries: f_0(n) = n + 1,
f_(k+1)(n) = f_k^n(n), f_ω(n) = f_n(n), f_(ω+1)(n) = f_ω^n(n); in Coq f_k = `FGH (ofin k)` = `fin_fgh k`,
f_ω = `FGH omega`, f_(ω+1) = `FGH (osucc omega)`). Written by this project (agent claims-prover), 2026-11-13.

| entry | theorem | statement (Coq) | loads |
|---|---|---|---|
| BB(4,3), Kropitz | `FGH_BB43.bb43_fgh` | f_4^3(2^94) < σ < f_4^3(2^96 + 6) | [`../BB43/verify/`](../BB43/verify/) (root `TM43`) |
| BB(3,4), Kropitz | `FGH_BB34.bb34_fgh` | f_16(2) < σ < f_16(3) | [`../BB34/verify/`](../BB34/verify/) (root `TM34`) |
| BB(4,4), 44-B | `FGH_BB44.bb44B_fgh` | f_ω(f_2(f_4(f_5(f_4(f_3(64)))))) < σ < f_ω(f_2(f_4(f_5(f_4(f_3(256)))))) | [`../BB44/verify_44b/`](../BB44/verify_44b/) (root `Local`) |
| 44-A | `FGH_BB44.bb44A_fgh` | f_ω(2↑^4 6 − 3) < σ < f_ω(2↑^4 6 − 2) ≤ f_ω(f_5(4)) | same |
| 44-C | `FGH_BB44.bb44C_fgh` | f_ω(65532) < σ < f_ω(65533) | same (byte-identical copies of `verify_44c`) |
| BB(5,4), 54-L | `FGH_BB54.bb54_fgh` | f_(ω+1)(65536) < σ | [`../BB54/verify_54l/`](../BB54/verify_54l/) (root `Local`) |
| BB(5,3), 53-Main | `BB53_fgh.sigma_exceeds_FGH` | f_ω(f_ω(7)) < σ and f_ω(2↑^8 3) < σ | in [`../BB53/verify_cmp/`](../BB53/verify_cmp/) |

`KnuthFGH.v` is the bridge: `kn` is the Knuth arrow (the same text as the `knuth` of every multi-symbol development;
each statement file proves the pointwise equality with its entry's copy), and

- `fin_lower` : 2↑^k x ≤ f_(k+1)(x) for x ≥ 1, and `fin_lower2`;
- `fin_upper` : f_(k+1)(x) ≤ 2↑^k (3x) for k ≥ 1, x ≥ 4;
- `fw_le_F` : f_ω(n) ≤ 2↑^(n+1)(n+3) for n ≥ 4 (the Knuth-arrow "f_omega" of the BB(5,4) files is at least the FGH f_ω);
- `window_kn6` : f_ω(L) < 2↑^L 6 + L < f_ω(L+1) for L ≥ 4, and `window_kn3`, `window_knA`.

`Ord.v` is a byte-identical copy of [`../BB31/verify/multifile/Ord.v`](../BB31/verify/multifile/Ord.v) (`share_check.sh`),
logical root `BB8` here.

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

It runs `share_check.sh`, compiles `Ord.v` and `KnuthFGH.v`, builds each loaded entry directory if its `.vo` files are
missing, compiles the four statement files with that entry's logical root, and then the probes `probe34.v`,
`probe43.v`, `probe44.v`, `probe54.v`, which print the definitions and statements and run `Print Assumptions` on 12
theorems (the four library facts above and `sigma_eq`, `sigma_bounds`, and the six FGH theorems): all closed under
the global context. CI job `fgh`.
