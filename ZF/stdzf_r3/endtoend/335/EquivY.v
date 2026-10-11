(** * EquivY: replacing the axioms B2 and B3 of [prov] (zf/axtext/coq/R3/Logic.v) by the single scheme
    BY a b c = a -> ((-. b -> ((b -> c) -> -. a)) -> b)   (Polish: CpCCNqCCqrNpq)
    changes neither the pure-logic theorems ([lprovY a <-> lprov a]) nor the theorems of the full system
    ([provY a <-> prov a]).  Everything proved about [prov]/[lprov] therefore transfers. *)
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta PropBasis.
Import Coq.Lists.List ListNotations.

(** [prov] with B2, B3 replaced by BY *)
Inductive provY : wff -> Prop :=
  | YDET a b : provY (Wim a b) -> provY a -> provY b
  | YGEN x a : provY a -> provY (Wal x a)
  | YB1 a b c : provY (Wim (Wim a b) (Wim (Wim b c) (Wim a c)))
  | YBY a b c : provY (BYf a b c)
  | YB4 x a b : provY (Wim (Wal x (Wim a b)) (Wim (Wal x a) (Wal x b)))
  | YB6a x y z : x <> z -> y <> z ->
      provY (Wa (Wim (Weq x y) (Wal z (Weq x y))) (Wim (Wel x y) (Wal z (Wel x y))))
  | YB6b x y a : provY (Wim (Wal x (Wal y a)) (Wal y (Wal x a)))
  | YB6c x a : provY (Wim (Wex x (Wal x a)) a)
  | YB7 x y : provY (Wex x (Weq x y))
  | YB8a x y z : provY (Wim (Weq x y) (Wim (Weq x z) (Weq y z)))
  | YB8b x y z : provY (Wim (Weq x y) (Wim (Wel x z) (Wel y z)))
  | YB8c x y z : provY (Wim (Weq x y) (Wim (Wel z x) (Wel z y)))
  | YAX_EXT : provY EXT
  | YAX_REP a : provY (REP a)
  | YAX_INF : provY INF.

(** [lprov] with B2, B3 replaced by BY *)
Inductive lprovY : wff -> Prop :=
  | LYDET a b : lprovY (Wim a b) -> lprovY a -> lprovY b
  | LYGEN x a : lprovY a -> lprovY (Wal x a)
  | LYB1 a b c : lprovY (Wim (Wim a b) (Wim (Wim b c) (Wim a c)))
  | LYBY a b c : lprovY (BYf a b c)
  | LYB4 x a b : lprovY (Wim (Wal x (Wim a b)) (Wim (Wal x a) (Wal x b)))
  | LYB6a x y z : x <> z -> y <> z ->
      lprovY (Wa (Wim (Weq x y) (Wal z (Weq x y))) (Wim (Wel x y) (Wal z (Wel x y))))
  | LYB6b x y a : lprovY (Wim (Wal x (Wal y a)) (Wal y (Wal x a)))
  | LYB6c x a : lprovY (Wim (Wex x (Wal x a)) a)
  | LYB7 x y : lprovY (Wex x (Weq x y))
  | LYB8a x y z : lprovY (Wim (Weq x y) (Wim (Weq x z) (Weq y z)))
  | LYB8b x y z : lprovY (Wim (Weq x y) (Wim (Wel x z) (Wel y z)))
  | LYB8c x y z : lprovY (Wim (Weq x y) (Wim (Wel z x) (Wel z y))).

(** BY is a theorem of B1-B3 (natural-deduction style proof through [der]). *)
Lemma lprov_BY a b c : lprov (BYf a b c).
Proof.
  unfold BYf. apply der_lprov, ded, ded.
  (* G = [ -.b -> ((b -> c) -> -.a) ; a ],  goal b, via B2: (-.b -> b) -> b *)
  mp (Wim (Wn b) b); [dt (LB2 b) |]. apply ded.
  (* G = [ -.b ; H ; a ] *)
  mp (Wn a); [mp a; [dt (LB3 a b) | dh] |].
  mp (Wim b c).
  - mp (Wn b); dh.
  - mp (Wn b); [dt (llp362 b c) | dh].
Qed.

Theorem lprovY_lprov a : lprovY a <-> lprov a.
Proof.
  split.
  - induction 1; try (econstructor; eassumption); try (constructor; assumption).
    apply lprov_BY.
  - induction 1; try (econstructor; eassumption); try (constructor; assumption).
    + exact (y_B2 lprovY LYDET LYB1 LYBY a).
    + exact (y_B3 lprovY LYDET LYB1 LYBY a b).
Qed.

Theorem provY_prov a : provY a <-> prov a.
Proof.
  split.
  - induction 1; try (econstructor; eassumption); try (constructor; assumption).
    apply lprov_prov, lprov_BY.
  - induction 1; try (econstructor; eassumption); try (constructor; assumption).
    + exact (y_B2 provY YDET YB1 YBY a).
    + exact (y_B3 provY YDET YB1 YBY a b).
Qed.
