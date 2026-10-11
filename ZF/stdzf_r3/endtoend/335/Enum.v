(** * Enum: the abstract proof enumerator, a functional reading of main() in zf2.py,
    instantiated for R3Y1_335 (zf-prune's 335-state machine: R3s336 with B2, B3 replaced by the single scheme
    BY = CpCCNqCCqrNpq (PropBasis.v, EquivY.v); 15 clauses, permuted parameter roles,
    machine texts of EXT, REP (bounded fiber), INF -- see L1_R3s.v; no POW/UNI).

    State: four persistent registers (prooflist, nextproof, topwff, wffstack).  One [enum_step] is
    one iteration of main(); the machine halts at the end of an iteration whose topwff is 1 (the
    code of "v_0 e. v_0").

    Layer L1 proves   enum_halts <-> prov (Wel v0 v0)          (Logic only).
    Layer L2 proves   one big-step run of the DAG root = one enum_step   (program refinement). *)

From Coq Require Import Arith.Arith Lia Lists.List Bool.Bool.
From ZF Require Import Logic.
Import ListNotations.

Definition c0 := 0. Definition c1 := 1. Definition c2 := 2. Definition c3 := 3. Definition c4 := 4.

(* clause wffs of R3Y1_335 (zf-prune's 335-state machine) in clause index order, from
   v335/R3Y1_335.enum.txt; p1..p3 = the three proof-step parameters (the parameter roles are permuted
   per clause, see R3Y1_335.json "perm").  clause_0 (DET) and clause_1 (GEN) are placeholders: their
   effect is defined in [apply_clause]. *)
Definition clause_0 (p1 p2 p3 : nat) : nat := (wim p3 p1).                                            (* DET *)
Definition clause_1 (p1 p2 p3 : nat) : nat := (wal p3 p1).                                            (* GEN *)
Definition clause_2 (p1 p2 p3 : nat) : nat :=
  (wim (wim p3 p2) (wim (wim p2 p1) (wim p3 p1))).   (* B1 *)
Definition clause_3 (p1 p2 p3 : nat) : nat :=
  (wim (wal p3 (wim p2 p1)) (wim (wal p3 p2) (wal p3 p1))).   (* B4 *)
Definition clause_4 (p1 p2 p3 : nat) : nat :=
  (wim (wal p3 (wal p1 p2)) (wal p1 (wal p3 p2))).   (* B6b *)
Definition clause_5 (p1 p2 p3 : nat) : nat :=
  (wim (weq p3 p2) (wim (wel p3 p1) (wel p2 p1))).   (* B8b *)
Definition clause_6 (p1 p2 p3 : nat) : nat :=
  (wa (wim (weq p3 p1) (wal p2 (weq p3 p1))) (wim (wel p3 p1) (wal p2 (wel p3 p1)))).   (* B6a *)
Definition clause_7 (p1 p2 p3 : nat) : nat :=
  (wim (wex p3 (wal p3 p1)) p1).   (* B6c *)
Definition clause_8 (p1 p2 p3 : nat) : nat :=
  (wex p3 (weq p3 p1)).   (* B7 *)
Definition clause_9 (p1 p2 p3 : nat) : nat :=
  (wim (weq p3 p2) (wim (weq p3 p1) (weq p2 p1))).   (* B8a *)
Definition clause_10 (p1 p2 p3 : nat) : nat :=
  (wim (weq p3 p1) (wim (wel p2 p3) (wel p2 p1))).   (* B8c *)
Definition clause_11 (p1 p2 p3 : nat) : nat :=
  (wim (wal c0 (wa (wim (wel c0 c2) (wel c0 c1)) (wim (wel c0 c1) (wel c0 c2)))) (weq c1 c2)).   (* EXT *)
Definition clause_12 (p1 p2 p3 : nat) : nat :=
  (wim (wal c3 (wex c1 (wal c2 (wim (wal c1 p2) (wim (wn (wal c0 (wim (wel c0 c2) (wel c0 c1)))) (wel c2 c1)))))) (wex c1 (wal c2 (wa (wim (wex c3 (wa (wal c1 p2) (wel c3 c0))) (wel c2 c1)) (wim (wel c2 c1) (wex c3 (wa (wal c1 p2) (wel c3 c0)))))))).   (* REPsb0 *)
Definition clause_13 (p1 p2 p3 : nat) : nat :=
  (wex c2 (wa (wal c0 (wim (wel c0 c2) (wex c1 (wa (wal c2 (wa (wim (weq c0 c2) (wel c2 c1)) (wim (wel c2 c1) (weq c0 c2)))) (wel c1 c2))))) (wel c0 c2))).   (* INF *)
Definition clause_14 (p1 p2 p3 : nat) : nat :=
  (wim p3 (wim (wim (wn p2) (wim (wim p2 p1) (wn p3))) p2)).   (* BY = CpCCNqCCqrNpq *)

(* the order in which the clauses appear in main() (R3Y1_335.json "order"):
   position i (1-based) holds clause index [nth (i-1) axiomorder]; codes >= 15 select position 15 *)
Definition axiomorder : list nat := [13; 4; 3; 9; 7; 10; 14; 5; 2; 8; 11; 0; 12; 1; 6].
(* positions: INF B6b B4 B8a B6c B8c BY B8b B1 B7 EXT DET REPsb0 GEN B6a *)

Definition clause (c : nat) : nat -> nat -> nat -> nat :=
  match c with
  | 0 => clause_0 | 1 => clause_1 | 2 => clause_2 | 3 => clause_3 | 4 => clause_4
  | 5 => clause_5 | 6 => clause_6 | 7 => clause_7 | 8 => clause_8 | 9 => clause_9
  | 10 => clause_10 | 11 => clause_11 | 12 => clause_12 | 13 => clause_13
  | _ => clause_14
  end.

(** ** The wff stack: topwff is the top, wffstack the Cantor-encoded rest ((x . rest), 0 = empty). *)
Definition push (x ws : nat) : nat := pair x ws.
Definition pop (ws : nat) : nat * nat := unpair ws.      (* (top, rest); pop 0 = (0, 0) *)

(* Effect of the active clause [c] on (topwff, wffstack), given the three parameters and the stack
   [ws] after main() pushed the previous topwff.  DET pops the minor premise ph (= previous topwff)
   then the major premise and yields p1 iff major = (ph -> p1), else the moot wff 0.
   GEN pops ph and yields A. p3 ph.  B6a (roles x y z = p3 p1 p2) yields the moot wff unless the
   bound variable p2 differs from p3 and p1. *)
Definition apply_clause (c p1 p2 p3 ws : nat) : nat * nat :=
  match c with
  | 0 => let '(ph, ws1) := pop ws in
         let '(maj, ws2) := pop ws1 in
         (if Nat.eqb (wim ph p1) maj then p1 else 0, ws2)
  | 1 => let '(ph, ws1) := pop ws in (wal p3 ph, ws1)
  | 6 => (if Nat.eqb p2 p3 || Nat.eqb p2 p1 then 0 else clause_6 p1 p2 p3, ws)
  | _ => (clause c p1 p2 p3, ws)
  end.

Record state : Type := mkState { pl : nat; np : nat; tw : nat; ws : nat }.

Definition s0 : state := mkState 0 0 0 0.

(* One iteration of main(). *)
Definition enum_step (s : state) : state :=
  let '(pl1, np1) := if Nat.eqb (pl s) 0 then (np s, S (np s)) else (pred (pl s), np s) in
  let '(ac, pl2) := unpair pl1 in
  let '(p1, pl3) := unpair pl2 in
  let '(p2, pl4) := unpair pl3 in
  let '(p3, pl5) := unpair pl4 in
  let ws1 := push (tw s) (ws s) in                       (* v_0(): push previous theorem, topwff := 0 *)
  let '(tw', ws') :=
    if Nat.eqb ac 0 then (0, ws1)                        (* no clause selected: moot wff *)
    else apply_clause (nth (Nat.min ac 15 - 1) axiomorder 14) p1 p2 p3 ws1 in
  mkState pl5 np1 tw' ws'.

(* The machine halts at the end of an iteration leaving topwff = 1 = code (Wel v0 v0). *)
Definition enum_halts : Prop :=
  exists n, tw (Nat.iter (S n) enum_step s0) = 1.
