(** * PA_Enum: the abstract proof enumerator = one run of main() of zf/pagb/machine/source_pa.py,
    exactly zf/pagb/machine/spec_pa.py (frozen, sha256 3cfdafbf...dde4) [enum_step].

    Persistent registers at a command boundary (as zf/m254/logic/coq/Enum254.v):
      pl = prooflist, np = nextproof, tw = topwff, ws = wffstack (stream P top rest; 0 = zeros),
      d = param1, h = param2 (the cache).
    Commands (selector, then fields read from the command list):
      0       MP    x        : d += x; if wim tw d = h then tw := d and push 0, else tw := 0; h := 0
      1       DROP  x        : d += x; push tw; tw := h
      2       NIP   x        : d += x; if h = 1 then HALT else h := pop
      3 + c   AX    x y u    : d += x; a := d; b := h + y; push tw, GEN = wal a h, then the 19 rows
                               (order: design_choice_A.json rorder); tw := bundle a b c; d := 0; h := 0
    The rows and the bundle are the code ASTs of PA_Rows / PA_Thm. *)
From Coq Require Import Arith Lia Bool.
From PAGB Require Import PA_Pair PA_Codes PA_Rows PA_Thm.

Record state : Type := mkState { pl : nat; np : nat; tw : nat; ws : nat; d : nat; h : nat }.

Definition s0 : state := mkState 0 0 0 0 0 0.

(** the AX roots, slots 2 .. 20 (bottom to top); slot 0 = old current, slot 1 = GEN *)
Definition slot2 a b (c u : nat) := cd (r_QAS a b).
Definition slot3 a b (c u : nat) := cd (r_QSI a b).
Definition slot4 a b (c u : nat) := cd (r_B6c a b).
Definition slot5 a b c (u : nat) := cd (r_CM1 a b c).
Definition slot6 (a b c u : nat) := cd r_NG.
Definition slot7 a b (c u : nat) := cd (r_QMS a b).
Definition slot8 (a b : nat) c (u : nat) := cd (r_EX c).
Definition slot9 a b (c u : nat) := cd (r_CS a b).
Definition slot10 a b c (u : nat) := cd (r_CA1 a b c).
Definition slot11 a b c (u : nat) := cd (r_COMM a b c).
Definition slot12 (a b : nat) c (u : nat) := cd (r_QA0 c).
Definition slot13 a b c u := cd (r_L a b c u).
Definition slot14 a b c (u : nat) := cd (r_CM2 a b c).
Definition slot15 a b c (u : nat) := cd (r_EUC a b c).
Definition slot16 a b c (u : nat) := cd (r_CA2 a b c).
Definition slot17 a b c (u : nat) := cd (r_QI a b c).
Definition slot18 a b (c u : nat) := cd (r_R1 a b).
Definition slot19 a (b c u : nat) := cd (r_QM0 a).
Definition slot20 a (b c u : nat) := cd (r_QZS a).

(** the stack after AX: [t] pushed first, then GEN of the cache, then slots 2 .. 20 *)
Definition ax_stack (a hh b c u t w : nat) : nat :=
  P (slot20 a b c u) (P (slot19 a b c u) (P (slot18 a b c u) (P (slot17 a b c u) (P (slot16 a b c u)
  (P (slot15 a b c u) (P (slot14 a b c u) (P (slot13 a b c u) (P (slot12 a b c u) (P (slot11 a b c u)
  (P (slot10 a b c u) (P (slot9 a b c u) (P (slot8 a b c u) (P (slot7 a b c u) (P (slot6 a b c u)
  (P (slot5 a b c u) (P (slot4 a b c u) (P (slot3 a b c u) (P (slot2 a b c u)
  (P (wal a hh) (P t w)))))))))))))))))))).

Definition enum_step (s : state) : option state :=
  let '(pl1, np1) := if Nat.eqb (pl s) 0 then (np s, S (np s)) else (pred (pl s), np s) in
  let '(ac, pl2) := unP pl1 in
  let '(x, pl3) := unP pl2 in
  let d1 := d s + x in
  match ac with
  | 0 => Some (if Nat.eqb (wim (tw s) d1) (h s)
               then mkState pl3 np1 d1 (P 0 (ws s)) d1 0
               else mkState pl3 np1 0 (ws s) d1 0)
  | 1 => Some (mkState pl3 np1 (h s) (P (tw s) (ws s)) d1 (h s))
  | 2 => if Nat.eqb (h s) 1 then None
         else let '(h1, w1) := unP (ws s) in Some (mkState pl3 np1 (tw s) w1 d1 h1)
  | S (S (S c)) =>
      let '(y, pl4) := unP pl3 in
      let '(u, pl5) := unP pl4 in
      let b := h s + y in
      Some (mkState pl5 np1 (bundle d1 b c) (ax_stack d1 (h s) b c u (tw s) (ws s)) 0 0)
  end.

(** [run n s]: n steps from s, [None] if a step halts on the way *)
Fixpoint run (n : nat) (s : state) : option state :=
  match n with
  | 0 => Some s
  | S n => match enum_step s with Some s' => run n s' | None => None end
  end.

(** The enumerator halts iff some reachable state makes a halting step (a NIP with cache F = 1). *)
Definition enum_halts : Prop := exists n s, run n s0 = Some s /\ enum_step s = None.
