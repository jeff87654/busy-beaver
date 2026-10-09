# The f_(ω+1) candidate screen that found n1

This folder holds the search that found the BB(10) machine

    n1 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_---0LC

(written `..._1RZ0LC` on the [analysis page](../1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC.md);
here an undefined transition is `---`). It contains the tools, the screen's data, and a short test that rebuilds the
tools and reproduces part of the data.

**What is claimed here.** Nothing about n1 rests on this folder. The screen is a heuristic: it follows each candidate
with small stand-in values in place of astronomically large ones, and its verdicts (HALT, LOOP, ...) are guesses about
the real run. The claims about n1 are the Coq theorems in [`../verify/`](../verify/), described on the
[analysis page](../1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC.md). This folder documents how
the machine was found, including one filter that missed it.

Notation as on the analysis page: D(t) = (10)^t 1 is a token, the token 1 (D1) is a zero digit, a configuration is a
list of tokens ending in an a-token and an accumulator r. The *clearing rules* R1–R3 of the BB(7) champion lower the
token next to the accumulator, or borrow from the nearest non-zero token across a run of zeros, and grow the
accumulator at each step; one unit cleared at depth j (j zeros between the token and the accumulator) maps the value
v to 2↑^j v. A clearing stops at an *event*: the borrow meets a blocker (D0, D2, or junk), the a-token bottoms out, or
the borrow runs off the left end of the list.

## 1. The search space

All candidates keep an 8-state *base machine* (states A–H) whose run agrees with the BB(8) record
(`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_1LC0RH_1RG1LF`, [`../../BB8/`](../../BB8/)) up to the point where the
record halts. The record halts when it reads E0 after its digit list is exhausted. Each candidate sends E0 to a new
state I and fills in I and J; the base machine's other transitions are unchanged. The screen in this folder covers
the "GH" base `1RB0RA_1LC1LF_1RD0LB_1RA1LE_---0LC_0RG1LD_1RH1LG_1LC0RG`, whose states A–E are the record's; it is n1's
base machine. `mf35g.py` also knows two sibling bases (H, SIB) and the record itself (REC).

## 2. The pipeline

### 2.1 The start configuration and its residues

Everything starts from the configuration in which the base machine first reads E0, the moment the record would halt.

- For the record, `mf35.xword(b, n)` writes this configuration X(b, n) in closed form: the tape
  `101 (011)^(12b+12) 0 1110101010101010100 (101)^n` with the head on the 0 after the (011) run, in state E. It is
  the record's configuration at the E0 read that follows the exhaustion K(0^n; 0; b) (a list of n zero digits that
  can no longer be cleared; b parametrises the accumulator).
- For the other bases, `mf35g.xstart(family, b)` gets the same moment by literal simulation: it writes K(0^35; 0; b)
  for that base (for GH: `1 (011)^36 (01)^(3b+1) 1010`, head on the blank to its right, state G) and runs the base
  machine until it reads E0.

In the real run b is astronomically large. `numres.py` keeps such numbers as residues modulo
QBIG = 2^10·3^8·5^2·7·11·13·17·19 = 54,305,848,396,800 (QBIG is closed under the Carmichael function, so 2^x mod QBIG
is computable from x mod QBIG once x is large). `numres.tau()` is the common residue of every huge accumulator
produced by the clearing rules. The real b satisfies B = (tau − 2)/3 ≡ 6 (mod 2520).

### 2.2 Completions (`renum.cpp`)

`renum BASE NMAX STARTS BUDGET [REPORT]` enumerates completions of BASE in tree normal form, starting from given
configurations. It simulates each node from every start; at the first start that reads an undefined transition, it
branches that transition over all values (target states up to the first unused one) and keeps the node itself as a
leaf with the transition undefined. So it only ever branches on slots that the run actually reads.

The starts, `data/starts_GH.txt`, are the GH base's E0 configurations for b = 0, ..., 6 and 14 (`make_starts.py`).
With NMAX = 10 and a budget of 200,000 steps per start the tree has 17,917 nodes, of which 12,795 are printed (a
start does not halt, or halts after more than 100,000 steps). `select_set.py` then keeps 11,447 machines: E0 must
point into I or J (12,763), some undefined transition must be reachable in the state graph (1,296 cannot halt at
all), and 20 small halters are dropped (every start halts, the b = 0 start within 100,000 steps).

### 2.3 The mini-follower (`mf35.py`, `mf35g.py`, `mfg_batch.py`)

The mini-follower follows one candidate from the real start, alternating two kinds of stage:

- **Literal stage** (`stage35.cpp` / `stage35g.cpp`, run as a server): the machine is simulated cell by cell until it
  halts (H), exceeds the step or width limit (T, W), or reaches a *K-moment* (the base's canonical state reading 0 at
  the right end of the tape, the tape ending in the family's tail) from which the clearing rules would produce large
  numbers. K-moments whose clearing stays small are simulated literally.
- **Jump** (`follow2.jump`): the clearing rules R1–R3 are run abstractly from the K-moment's token list to the next
  event, with the closed forms of `numres.py` (iterated 2↑^j, residues modulo QBIG for huge values). The event
  configuration is written back to a literal tape, together with any non-token bits beyond the farthest token
  ("far bits"), and the next literal stage starts there.

Every huge value is replaced by a small *representative* of its residue class: run A uses r ≡ R (mod 2520) with
r ≥ 19 and starts from b = 6 (the real class of b mod 2520). `mf35.py` (record family) also makes a second run B with
a different modulus (in the code: r mod 72, r ≥ 40, start b = 30); a jump whose cleared-list length differs between
runs A and B depends on a huge value, so it is counted as a full cycle. `mf35g.py` and the batch screen use run A
only. A run ends with HALT, TIME, WIDE, FAIL (a jump the abstract rules cannot do), LOOP (the last event
configurations repeat in shape with every count changing by a constant amount per period, a heuristic loop test), or
MAXSTAGES.

Each jump appends a history record

    J k=<tokens> far=<clean|junk> ev=<block|a-block|left> zeros=<n> r=<representatives>

where k is the number of list tokens at the K-moment (without the a-token and the accumulator), far says whether far
bits were present, ev is the event, **zeros is the number of zero digits next to the accumulator in the event
configuration, that is, the length of the list the jump has just cleared**, and r lists the representatives of the
new huge values. `mfg_batch.py` writes one line per machine: machine, verdict, number of records, number of jumps
with zeros ≥ 50, and the records joined by ` ; `.

### 2.4 The funnel on the GH tree

`mfg_batch.py GH set.txt mf_GH.tsv 1 12 3000000` (12 stages, 3·10^6 steps per literal stage) gives, for the 11,447
machines ([`data/mf_GH.tsv.gz`](data/mf_GH.tsv.gz)):

| verdict | machines |
|---|---|
| MAXSTAGES | 4,821 |
| TIME | 2,215 |
| HALT | 2,036 |
| WIDE | 1,622 |
| LOOP | 753 |

A selection of 1,005 MAXSTAGES rows was rerun with 80 stages ([`data/mg80_GH.tsv.gz`](data/mg80_GH.tsv.gz): HALT 117,
LOOP 147, MAXSTAGES 551, TIME 156, WIDE 32, FAIL 2). This separates machines whose lists keep growing without a halt
in sight from machines that halt late. Candidate halters from this and the two sibling families (8 GH, 9 H, 103 SIB)
were then put through the size-ordering check of section 4 ([`data/ord_out.tsv`](data/ord_out.tsv)): 89 of the 120
halt under all three policies std, big and shrink, 11 under two, 14 under one, and 6 under none.

## 3. The key lesson: measure growth by the cleared list

An f_(ω+1) machine has to do two things at once: make the list that each clearing crosses longer by an amount that
depends on the latest huge value (each period is then an f_ω-sized step), and count the periods down so that the
machine halts. In the histories the first shows up in `zeros=`, the second as a falling number of non-zero tokens
k − zeros (the counter is a list of tokens parked behind blockers).

The first filters looked at the total token count k instead. That is the wrong quantity:

- **It flags parked lists.** The machine `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_---0LJ_1LD1LC` halts
  in the 12-stage screen with k growing from 85 to 153, while its cleared list stays at 67–71 zeros. The growth is a
  list of parked token pairs, not a longer cleared list. A k-based reading took it for an ω-level-2 machine; it is at
  ω-level 1.
- **It drops n1.** In the 12-stage screen n1 ends MAXSTAGES with k = 117 → 115, flat. In the 80-stage rerun it halts
  after 37 jumps; k rises only from 117 to 330 (6.4 per jump; `ana.py`, the old filter, requires 30 by default), while
  the cleared list grows from 32 to 329 zeros and the non-zero tokens fall from 85 to 1.

[`src/zeros_filter.py`](src/zeros_filter.py) implements the right test. It splits a history into three equal windows
and takes peaks (a period spans several jumps, and the counts oscillate within a period). A machine is selected when
the peak of `zeros=` rises from window to window and ends at least G times higher (`--grow`, default 2), and the peak
of k − zeros falls from window to window. LOOP rows are skipped, and machines with identical histories are grouped.
This filter was written after n1 was found, and its windows-and-peaks criterion was chosen by looking at this data
(a plain first-to-last ratio of `zeros=` ranks n1 15th, because the counts oscillate within a period), so the ranks
below show that the cleared-list measure separates n1 from the k measure, not how a blind filter would have done.
On the screen data:

| file | selected groups | n1 |
|---|---|---|
| `mf_GH.tsv.gz` (12 stages) | 4 | rank 2 (k growth 0.2 per jump: rank 339 of 1,368 under the k measure) |
| `mg80_GH.tsv.gz` (80 stages) | 6 | rank 2; rank 1 with `--kinds HALT` (tied with `..._---0LJ_0LE0LJ`, which has the same history but halts in I0) |

`ana.py` is kept unchanged as the counter-example: on `mf_GH.tsv` it selects 455 rows, and n1 is not among them.
`--compare-k` prints the k-based measure next to the zeros filter.

## 4. The size-ordering trap

A single representative per residue class cannot tell which of two huge values is larger. In the real run each new
accumulator is vastly larger than every value parked earlier; with representatives they are all of the same size, or
in the wrong order. A literal stage whose behaviour depends on that order (for example, unpacking one parked value
into list length while a newer one is consumed) can then take a branch that the real run never takes, and the
verdict is wrong. `ord_run.py` reruns a machine under several representative policies:

- `std`: every huge value gets its representative in [19, 2539), as in the screen;
- `big`: every huge value is lifted by 2520·k;
- `shrink`: the current accumulator lives in the window [19 + 2520k, 19 + 2520(k+1)) and every parked token is
  reduced to [19, 2539), which is the real order (newest largest);
- `floor`, `order`: further variants (see the docstring).

`ord_batch.py` runs std, big and shrink with 80 stages; a machine whose halt survives all three does not depend on the
order of its huge values within the run.

A related trap is the far bits. When a stage is replayed literally to confirm a halt, it must be replayed with the far
bits of the logged event configuration. For n1, the halting stage with its far bits halts in J0 for R = 19 and
R = 2539 (ones = 2R + 735); the same tokens without the far bits run on (`7 1^(n+80)`), because the parked region
takes part in detecting the end of the countdown.

## 5. How n1's candidacy was confirmed

1. **Symbolic follower.** `follow2.py` follows a machine with b kept symbolic: each literal stage is run at several
   values of b in the real residue class and fitted as an affine function, R1–R3 are checked literally in front of
   each tail, and each jump tracks the ω-level of the new values (+1 when a jump clears a list whose length is
   itself huge). For n1 the counter list is D(1)^(12b+7) after the first stage and loses 14 per period; the cleared
   list becomes huge at stage 6 (ω-level 1) and its level rises by one each period (level 2 at stage 9).
2. **Residue class.** The counter loses 14 per period, so the end of the run depends on b mod 14. In the
   mini-follower, b = 6, 20, 34, 48 (b ≡ 6 mod 14) halt in J0, at stages 37, 109, 181 and 253 (12 periods per 14 units
   of b); b = 11, 16, 21 run on past their exhaustion. The real B ≡ 6 (mod 2520), so B ≡ 6 (mod 14): the halting
   class. (The Coq proof states the same fact as T ≡ 2 (mod 7), lemma `T_mod7`.)
3. **Size order.** The big policy (29 stages, until the follower hit Python's recursion limit) and the shrink policy
   (14 stages) reproduce the chain of events of the std run. The parked far bits are identical in the std and big
   runs at every growth stage, so the halting replay with R = 2539 applies to the big run too.
4. **Independent checks and proof.** Independent literal simulators re-checked every rule
   ([`../tools/bb10_n1_writeup_chk.py`](../tools/bb10_n1_writeup_chk.py)), and the halting, exact score and comparison
   with the BB(10) champion were proved in Coq ([`../verify/`](../verify/)).

## 6. Files

`src/` (Python 3.8+, standard library only; C++17):

| file | role |
|---|---|
| `renum.cpp` | TNF completion enumerator from given configurations (section 2.2) |
| `make_starts.py` | the renum starts: a base machine's configuration at its first E0 read after K(0^35; 0; b) |
| `select_set.py` | the screen set from renum output (section 2.2) |
| `stage35.cpp`, `stage35g.cpp` | literal stage servers for the record family and for any family (canonical state, tail, offset) |
| `numres.py` | exact-or-huge numbers with residues modulo QBIG; closed forms of the clearing rules; `tau` |
| `follow2.py` | the symbolic stage follower; `follow2.jump` is the abstract jump used by the mini-follower |
| `hyb10.cpp` | the literal simulator used by `follow2.py`'s literal stages (K-moment detection, rule checks) |
| `tmlit.py` | plain literal TM simulator (used by `mf35g.xstart`) |
| `mf35.py` | mini-follower for the record family, runs A and B |
| `mf35g.py` | mini-follower for the families REC, H, GH, SIB (run A) |
| `mfg_batch.py` | batch screen: `python mfg_batch.py FAMILY SET.txt OUT.tsv WORKERS [STAGES=12] [MAXS=3000000]` |
| `ord_run.py` | one machine under a representative policy, verbose: `--machine M --family F --policy std/big/shrink/floor/order` |
| `ord_batch.py` | the size-ordering check: `python ord_batch.py IN.tsv OUT.tsv WORKERS` (IN: family, machine) |
| `zeros_filter.py` | the cleared-list filter (section 3) |
| `ana.py` | the old k-based filter, kept as the counter-example |

The scripts find the compiled tools next to themselves (`src/`); the environment variables `STAGE35EXE`,
`STAGE35GEXE` and `HYBEXE` override the paths, and `SCREEN_TMP` sets the directory for temporary files. On Windows
the tools run at Idle priority; elsewhere use `nice`. `follow2.py` writes per-stage results to `src/logs/`.

`data/`:

| file | content |
|---|---|
| `starts_GH.txt` | renum starts for the GH base, b = 0–6 and 14 (`make_starts.py GH 0 1 2 3 4 5 6 14`) |
| `mf_GH.tsv.gz` | the 12-stage screen of the 11,447 GH completions (`mfg_batch.py` format) |
| `mg80_GH.tsv.gz` | the 80-stage rerun of 1,005 MAXSTAGES rows |
| `ord_in.tsv`, `ord_out.tsv` | the size-ordering check: 120 machines of the GH, H and SIB families; per policy `policy:verdict:jumps:last line` |

## 7. Build and check

    ./build.sh      # g++ -O2 -std=c++17: renum, stage35, stage35g, hyb10 into src/
    ./check.sh      # about 30 s

`check.sh` builds the tools, runs `zeros_filter.py` on `data/mf_GH.tsv.gz` and checks that n1 is selected (rank 1 or 2)
while its k growth is 0.2 per jump, runs `mf35g.py` on n1 for 12 and 80 stages and checks that both histories equal
the rows in `mf_GH.tsv.gz` and `mg80_GH.tsv.gz` (zeros 32 → 113, and 32 → 329 with the halt in J0), regenerates
`starts_GH.txt` and runs a short renum (b = 0 start, 20,000 steps) that must have n1 as a leaf, and runs the first
stage of `follow2.py` on n1. It was run with g++ 16.1 (MSYS2 UCRT64) and Python 3.11 on Windows.

The full screen can be rerun on one core in under ten minutes:

    cd src
    python make_starts.py GH 0 1 2 3 4 5 6 14 > starts.txt
    ./renum 1RB0RA_1LC1LF_1RD0LB_1RA1LE_---0LC_0RG1LD_1RH1LG_1LC0RG 10 starts.txt 200000 > tree.tsv   # ~2 min
    python select_set.py tree.tsv > set.txt                                                            # 11,447 machines
    python mfg_batch.py GH set.txt mf_GH.tsv 1 12 3000000                                              # ~5 min
    python zeros_filter.py mf_GH.tsv --compare-k

Rerun this way, `tree.tsv`, `set.txt` and `mf_GH.tsv` came out identical to the original files (`mf_GH.tsv` up to line
order). The size-ordering batch takes longer (70 of the 120 rows in ten minutes); those 70 rows were identical to
`data/ord_out.tsv`.

## 8. Credit

The screen was written for this search in October 2026. It builds on the BB(7) champion (Kropitz 2025, analysis by
Ligocki) and the BB(8) record ([`../../BB8/`](../../BB8/)).
