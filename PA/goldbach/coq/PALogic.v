(** * PALogic: a substitution-free Hilbert calculus for Peano arithmetic with named variables
    (Tarski's S2 / Megill style, extended to the terms 0, S, +, × with equality as the only predicate).

    This is the reference calculus of the logic layer: the machine's code-level calculus is mapped
    into it, and it is related to the library's PAeq (soundness: PA_F.v).

    Term existence is primitive in the two forms the machine provides (B7v: E. x x = y, x <> y;
    B7c: E. x x = t with x = S (tcode t)); the general  E. x x = t  (x not in t) is derived (PA_LMeta).
    Side conditions are decidable syntactic checks:  [tocc x t]  (x occurs in the term t)  and
    [occ x a]  (x occurs in the wff a, free or bound).  Substitution is never performed by the
    calculus: the induction schema expresses phi(0) and phi(S x) through equality and a fresh
    variable c. *)
From Coq Require Import Arith Lia List Bool.
From PAGB Require Import PA_Pair.
Import ListNotations.

(** ** Terms and wffs *)
Inductive tm : Type :=
  | TV (n : nat)        (* variable *)
  | TZ                  (* 0 *)
  | TS (t : tm)         (* S t *)
  | TP (t s : tm)       (* t + s *)
  | TM (t s : tm).      (* t × s *)

Inductive wff : Type :=
  | Weq (t s : tm)            (* t = s *)
  | Wim (a b : wff)           (* a -> b *)
  | Wn (a : wff)              (* -. a *)
  | Wal (x : nat) (a : wff).  (* A. x a *)

Definition Wex (x : nat) (a : wff) : wff := Wn (Wal x (Wn a)).
Definition Wa (a b : wff) : wff := Wn (Wim a (Wn b)).
Definition Wo (a b : wff) : wff := Wim (Wn a) b.

Fixpoint tocc (x : nat) (t : tm) : bool :=
  match t with
  | TV n => Nat.eqb n x
  | TZ => false
  | TS t => tocc x t
  | TP t s | TM t s => tocc x t || tocc x s
  end.

(** the machine's code of a term (zf/pagb/INTERFACE.md): it bounds every variable of the term,
    so S (tcode t) is a fresh variable for t *)
Fixpoint tcode (t : tm) : nat :=
  match t with
  | TV i => 4 * P i 0 + 3
  | TZ => 0
  | TS t => 4 * P (tcode t) 1
  | TP t s => 4 * P (tcode t) (tcode s) + 1
  | TM t s => 4 * P (tcode t) (tcode s) + 2
  end.

Fixpoint occ (x : nat) (a : wff) : bool :=
  match a with
  | Weq t s => tocc x t || tocc x s
  | Wim a b => occ x a || occ x b
  | Wn a => occ x a
  | Wal y a => Nat.eqb y x || occ x a
  end.

(** the machine's code of a wff (negation = implication to F = code 1); it bounds every variable,
    so it is a fresh variable for the wff (PA_LMeta.fcode_fresh) *)
Fixpoint fcode (a : wff) : nat :=
  match a with
  | Weq t s => 4 * P (tcode t) (tcode s) + 3
  | Wim a b => 4 * P (fcode a) (fcode b)
  | Wn a => 4 * P (fcode a) 1
  | Wal x a => 4 * P x (fcode a) + 2
  end.

(** ** Arithmetic axioms (open; GEN closes them) *)
Notation v0 := (TV 0).
Notation v1 := (TV 1).

Definition QZS : wff := Wn (Weq TZ (TS v0)).                           (* 0 <> S x *)
Definition QSI : wff := Wim (Weq (TS v0) (TS v1)) (Weq v0 v1).          (* S x = S y -> x = y *)
Definition QA0 : wff := Weq (TP TZ v0) v0.                              (* 0 + x = x *)
Definition QAS : wff := Weq (TP (TS v0) v1) (TS (TP v0 v1)).            (* S x + y = S (x + y) *)
Definition QM0 : wff := Weq (TM TZ v0) TZ.                              (* 0 × x = 0 *)
Definition QMS : wff := Weq (TM (TS v0) v1) (TP v1 (TM v0 v1)).         (* S x × y = y + x × y *)

(** Induction without substitution:
      A.x (x = 0 -> a) -> A.x (a -> A.c (c = S x -> A.x (x = c -> a))) -> A.x a
    with c <> x and c not occurring in a, so that A.x (x = c -> a) says a(c) and
    A.c (c = S x -> a(c)) says a(S x).  Primitive (as in the machine) with c = fcode a, the code
    of a, when x < fcode a; the instances with any other fresh c are derived (PA_Ind.lind). *)
Definition IND (x c : nat) (a : wff) : wff :=
  Wim (Wal x (Wim (Weq (TV x) TZ) a))
      (Wim (Wal x (Wim a (Wal c (Wim (Weq (TV c) (TS (TV x))) (Wal x (Wim (Weq (TV x) (TV c)) a))))))
           (Wal x a)).

(** ** Provability from PA plus extra axioms [X] (for the machine: X = {NG}) *)
Section Prov.
Variable X : wff -> Prop.

Inductive pprov : wff -> Prop :=
  | HYP a : X a -> pprov a
  | DET a b : pprov (Wim a b) -> pprov a -> pprov b
  | GEN x a : pprov a -> pprov (Wal x a)
  (* propositional (Lukasiewicz) *)
  | B1 a b c : pprov (Wim (Wim a b) (Wim (Wim b c) (Wim a c)))
  | B2 a : pprov (Wim (Wim (Wn a) a) a)
  | B3 a b : pprov (Wim a (Wim (Wn a) b))
  (* quantifiers *)
  | B4 x a b : pprov (Wim (Wal x (Wim a b)) (Wim (Wal x a) (Wal x b)))
  | B6a z t s : tocc z t = false -> tocc z s = false -> pprov (Wim (Weq t s) (Wal z (Weq t s)))
  | B6b x y a : pprov (Wim (Wal x (Wal y a)) (Wal y (Wal x a)))
  | B6c x a : pprov (Wim (Wex x (Wal x a)) a)
  | B7v x y : x <> y -> pprov (Wex x (Weq (TV x) (TV y)))
  | B7c t : pprov (Wex (S (tcode t)) (Weq (TV (S (tcode t))) t))
  (* equality *)
  | E8 t s r : pprov (Wim (Weq t s) (Wim (Weq t r) (Weq s r)))
  | ES t s : pprov (Wim (Weq t s) (Weq (TS t) (TS s)))
  | EPl t s r : pprov (Wim (Weq t s) (Weq (TP t r) (TP s r)))
  | EPr t s r : pprov (Wim (Weq t s) (Weq (TP r t) (TP r s)))
  | EMl t s r : pprov (Wim (Weq t s) (Weq (TM t r) (TM s r)))
  | EMr t s r : pprov (Wim (Weq t s) (Weq (TM r t) (TM r s)))
  (* arithmetic *)
  | AZS : pprov QZS
  | ASI : pprov QSI
  | AA0 : pprov QA0
  | AAS : pprov QAS
  | AM0 : pprov QM0
  | AMS : pprov QMS
  | AIND x a : x < fcode a -> pprov (IND x (fcode a) a).
End Prov.
