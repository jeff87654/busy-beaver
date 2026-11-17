# The non-obvious pitfalls of this development

## 1. `execute` is cubic in the number of steps

busycoq's `execute` tactic is

    Ltac execute := introv; repeat (try solve [finish]; step).

`step` ends in `simpl_tape`, i.e. `autorewrite with tape_pre; simpl; autorewrite with tape_post`,
and `autorewrite` rewrites **the whole goal** — which, in the middle of an `execute`, contains
the entire proof term accumulated so far, i.e. every intermediate tape.  So one monolithic
`execute` over *n* steps performs O(n²) tape rewrites over tapes of size O(n): it is cubic,
and a 241-step `execute` needed more than 15 GB of RAM and never finished.

The fix is to cut the run into chunks.  `BB35_start.v` states the intermediate configurations
explicitly and proves 25 chunks of 10 steps each:

    Lemma chunk_0 : cfg_0 -->* cfg_10.
    Proof. unfold cfg_0, cfg_10. execute. Qed.

Inside a chunk the accumulated term stays short, so the cost is linear; the whole file
compiles in 15 s and about 300 MB.  The chunks are then joined with `follow`.

Note that `follow` is "peeling": `follow H` on a goal `c1 -->* c3` uses `evstep_trans` and
leaves the goal `c2 -->* c3`, so the last chunk must be closed separately with `finish`.

## 2. `g 15` must never be evaluated

`g` is

    Fixpoint g (k m : nat) : nat :=
      match k with O => S m | S k' => Nat.iter (2 * m + 2) (g k') 0 end.

`g 15 x` iterates `g 14` `2x+2` times, so getting *any* normal form of `g 15 x` requires
normalising `x` as well.  For `x = g 15 (g 15 (g 15 0))` this is astronomically expensive:
a single `whnf` of `Nat.iter 3 (g 15) 0` already runs into the billions of reduction steps.

Concretely, the following all take minutes or exhaust the memory, while the whole proof
otherwise takes 30 s:

- `simpl` on any goal mentioning `g 15` (it normalises the whole tree, exponentially);
- `lia` on a goal mentioning the raw `Nat.iter 3 (g 15) 0` (it partially unfolds the two
  occurrences into *different* terms, so the hypothesis and the goal no longer match and
  `lia` reports "Cannot find witness");
- `apply`/`exact` with a *conversion* between `g15` and the raw `Nat.iter 3 (g 15) 0`
  (unification expands the iter, the comparison of the two 2^16-node trees is quadratic).

**The `sig` alone is not enough.**  In BB34 `g15` was introduced as

    Lemma g15_spec : {x : nat | x = Nat.iter 3 (g 15) 0%nat}. ...
    Definition g15 : nat := proj1_sig g15_spec.

but `g15` is a transparent `Definition`, so `simpl` happily unfolds it to `proj1_sig g15_spec`
and then to `Nat.iter 3 (g 15) 0`.  In this development the seal is therefore made explicit:

    Opaque g15.

placed right after `g15_eq` is proved (before it, the conversion check of `g15_eq` needs the
definition to be transparent).  After that, `simpl` and `lia` treat `g15` as an atomic
natural number and never touch the tower.

Two further precautions make the development robust:

1. **Never compare `g15` with the raw term.**  Every configuration that mentions the score
   mentions it through the *same* term `g15`, so all comparisons are syntactic.  Where the
   raw term is unavoidable — the result of `B_rule` — the result is abstracted away first:

       Theorem B_rule_gen : forall k n m r (x : nat),
         x = Nat.iter n (g k) m -> Bcfg (S k) n m r -->* Bcfg (S k) 0 x r.

   and instantiated with `x := g15`, whose hypothesis `g15_eq` matches syntactically.

2. **Do the arithmetic generically.**  The counting lemmas are stated for an abstract `x`
   and only instantiated afterwards (`cells_count`, `cells_nonblank`), so that no tactic ever
   looks at `g15`.

`knuth 15 2 5` (= 2 ↑^15 5) is not a problem in the same way: `knuth`'s iteration count is a
literal, so unfolding it costs only O(2^14) nodes, and `lia` treats it as an atom.

## 3. `lia` and `Nat.iter 0 f x`

`lia` does **not** reduce `Nat.iter 0 f x` to `x` (its preprocessor abstracts the term as an
atom), so a goal such as `Nat.iter 0 f x <= Nat.iter 0 g x` is unprovable for `lia` even
though it is trivial.  Use `reflexivity` (or `simpl` first) in such places.

## 4. `>=` is not a relation `lia` knows

The notation `x >= y` is `ge` (`Coq.Classes.RelationClasses`), and `lia`'s preprocessor only
knows `le`, `<` and `=`; a goal containing `ge` makes `lia` fail with

    The relation ge is not a declared reflexive relation.

So all comparisons in this development are stated with `<=` and the arguments flipped.

## 5. `simpl` unfolds fixpoints and breaks `rewrite`

`simpl` performs iota-reduction, so `simpl` on a goal containing `aw j (S n) x` rewrites the
*inner* `aw` occurrences as well, and a subsequent `rewrite` with a pattern mentioning
`aw ...` no longer finds its subterm.  The development therefore states the two defining
equations of `aw` explicitly

    Lemma aw_0 : forall j x, aw j 0 x = x.
    Lemma aw_S : forall j n x, aw j (S n) x = knuth j 2 (aw (S j) n x).

and uses `rewrite aw_S` instead of `simpl`.  The same trick is used for `desc` (`desc_S`).

## 6. Side conditions come first

`apply IHn Hn' (g (S (S n)) m)` failed with *"The term ... has type nat while it is expected to
have type 1 <= S n"*: after `induction n`, the side condition `1 <= n` is a *premise* of the
induction hypothesis, so it has to be supplied first.  This is easy to miss because the
original statement of the lemma lists it last.

## 7. Numerals are symbols

`0`–`4` are `sym` notations (`Open Scope sym` in `Individual35.v`), so in `nat` positions they
must be written `0%nat`, `2%nat`, …, and the symbol constants have to be written `S3`, `S4`
explicitly (as in `final_cells`).  Mixing the two scopes in one file is a reliable source of
"has type list nat while it is expected to have type list sym".

## 8. Sandbox notes (only relevant on FUSE/"oss"-style mounts)

1. **`TMPDIR`**: Coq writes `.vo` through the temp directory.  If `/tmp` is not writable,
   `coqc` fails at the very end with `System error: "X.vo: No such file or directory"`.
   Fix: `export TMPDIR=/some/real/dir`.
2. **`.vo` pre-creation**: on such mounts, `Sys.file_exists` could report a stale positive for
   `.vo` files, making Coq's delete-then-recreate fail intermittently.  Fix: `touch X.vo`
   right before `coqc X.v`.
3. **Checking exit codes**: a compile check must not pipe `coqc` into `head`, because then `$?`
   is the exit code of `head` and a timeout looks like a success.  Use
   `coqc ... > log 2>&1; echo EXIT=$?`.
