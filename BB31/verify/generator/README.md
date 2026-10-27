# Generator for the BB31 / BB33 Coq developments

`python gen.py` writes `BB31/verify/multifile/BB31_*.v` and `BB33/verify/multifile/BB33_*.v` from the templates in
`tmpl/`. It only rewrites files whose content changed, so running it on this repository writes nothing: the
published files are exactly its output.

- `tmpl/rules.v`, `scan.v`, `round.v`, `game.v`, `halt.v`: shared templates (`@M@` = machine name; `@ROLES@`,
  `@E@`, `@E1@`, `@SP0@`, `@X0@`, ... = machine data).
- `tmpl/bound_BB31.v`, `tmpl/bound_BB33.v`: per-machine bound statements (a `<stem>_<M>.<ext>` template overrides
  `<stem>.<ext>` for machine M).
- `gen.py`, table `MACHINES`: for each machine, the role → state map and the depth-scanner states; the initial
  hydra, step count and ordinal; and the statements of the main theorems. The role table was checked against the
  exact pair-level tables computed from the machines, and every pair rule is re-proved by busycoq's `execute` in the
  generated `<M>_rules.v`, so a wrong role entry would make the build fail.

The machine-independent lemmas (the Bachmann property, hydra ordinals, `chop_ord`) are in `HydraOrd.v`, and the
Hardy hierarchy and `hardy_game` in `Hardy.v` (both in `../multifile/`, shared with BB33).

The same scheme extends to BB(29+2j) for larger j (hydra height 3+2j): add an entry to `MACHINES` (roles, depth
states, escape state, initial hydra, step count, ordinal), a `tmpl/bound_<M>.v`, and run gen.py.
