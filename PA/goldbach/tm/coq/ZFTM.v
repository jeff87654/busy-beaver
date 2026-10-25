(** * ZFTM: the 449-state machine pa_wade.tm (Wade TMBuilder compile of source_pa.py) as a busycoq [TM], built generically from the program.

    The states are defined structurally, following [TMBuilder.generate]:
    - the fixed framework states (boot, register operations 1.*, return 2.*, 5.root);
    - [QDisp i]  = 4.dispatch.(i+1), i < 9 (max run of car edges = 9);
    - [QBrk k]   = 6.break.k (k <= 3),  [QCont k] = 6.continue.k (k <= 4);
    - [QRInc r], [QRDec r] = 3.<register r>.inc / .decnz (9 registers, declaration order);
    - [QNode n]  = decision-DAG node n of [dagpa] (DagPA.v);
    - [QHalt]    = the state "halt" (no transitions).

    The transition function [tm] is defined from [dagpa_nodes]; the theorem [tm_table] checks by
    [vm_compute] that it coincides with the literal table [pa_table] of pa_wade.tm (the trust anchor). *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia Strings.String Ascii Eqdep_dec.
From BusyCoq Require Import TM.
From PAGBT Require Import RM DagPA TablePA NamesPA.
Import ListNotations.
Local Open Scope string_scope.

(** ** Bounded naturals [0..k] (finite payloads, so that the state type is finite). *)
Definition bnat (k : nat) : Type := { n : nat | Nat.leb n k = true }.

Definition bval {k} (x : bnat k) : nat := proj1_sig x.

Definition bmk (k n : nat) : bnat k :=
  match Nat.leb n k as b return Nat.leb n k = b -> bnat k with
  | true => fun H => exist _ n H
  | false => fun _ => exist _ k (Nat.leb_refl k)
  end eq_refl.

Lemma bnat_eq : forall k (x y : bnat k), bval x = bval y -> x = y.
Proof.
  intros k [x Hx] [y Hy]; simpl; intros ->.
  f_equal. apply UIP_dec. exact bool_dec.
Qed.

Lemma bval_bmk : forall k n, n <= k -> bval (bmk k n) = n.
Proof.
  intros k n H. unfold bmk.
  generalize (@eq_refl bool (Nat.leb n k)).
  generalize (Nat.leb n k) at 2 3. intros b E. destruct b; [reflexivity|].
  apply Nat.leb_nle in E. lia.
Qed.

Lemma bmk_bval : forall k (x : bnat k), bmk k (bval x) = x.
Proof.
  intros k x. apply bnat_eq. apply bval_bmk.
  destruct x as [n H]. simpl. apply Nat.leb_le, H.
Qed.

Lemma bval_le : forall k (x : bnat k), bval x <= k.
Proof. intros k [n H]. simpl. apply Nat.leb_le, H. Qed.

Definition bnat_dec {k} (x y : bnat k) : {x = y} + {x <> y}.
Proof.
  destruct (Nat.eq_dec (bval x) (bval y)) as [E|E].
  - left. apply bnat_eq, E.
  - right. intros ->. apply E. reflexivity.
Defined.

Definition ball (k : nat) : list (bnat k) := map (bmk k) (seq 0 (S k)).

Lemma ball_spec : forall k x, In x (ball k).
Proof.
  intros k x. unfold ball. rewrite <- (bmk_bval k x).
  apply in_map, in_seq. pose proof (bval_le k x). lia.
Qed.

(** ** Parameters of the build (TMBuilder.generate for dagpa). *)
Definition max_zeros := 9.      (* dispatch states 4.dispatch.1 .. 4.dispatch.9 *)

(** ** States *)
Inductive state : Type :=
  | QBootA | QBootB | QBootC | QBootD | QBootE
  | QDec | QDecB | QDecC | QDecD | QDecE | QDecG | QDecH | QDecI
  | QInc | QIncB | QIncC | QIncD
  | QSel | QSelB | QSelC | QSelD | QSelE | QSelF
  | QRet1 | QRet1a | QRet1b | QRet2 | QRet2a | QRet2b
  | QRoot
  | QDisp (i : bnat 8)      (* 4.dispatch.(i+1) *)
  | QBrk (k : bnat 3)       (* 6.break.k *)
  | QCont (k : bnat 4)      (* 6.continue.k *)
  | QRInc (r : bnat 8)     (* 3.<reg r>.inc *)
  | QRDec (r : bnat 8)     (* 3.<reg r>.decnz *)
  | QNode (n : bnat 382)    (* DAG node n *)
  | QHalt.

Definition Disp i := QDisp (bmk 8 i).
Definition Brk k := QBrk (bmk 3 k).
Definition Cont k := QCont (bmk 4 k).
Definition RInc r := QRInc (bmk 8 r).
Definition RDec r := QRDec (bmk 8 r).
Definition Node n := QNode (bmk 382 n).

Definition state_eq_dec (a b : state) : {a = b} + {a <> b}.
Proof. decide equality; apply bnat_dec. Defined.

Definition fixed_states : list state :=
  [QBootA; QBootB; QBootC; QBootD; QBootE;
   QDec; QDecB; QDecC; QDecD; QDecE; QDecG; QDecH; QDecI;
   QInc; QIncB; QIncC; QIncD;
   QSel; QSelB; QSelC; QSelD; QSelE; QSelF;
   QRet1; QRet1a; QRet1b; QRet2; QRet2a; QRet2b; QRoot; QHalt].

Definition all_states : list state :=
  fixed_states
  ++ map QDisp (ball 8) ++ map QBrk (ball 3) ++ map QCont (ball 4)
  ++ map QRInc (ball 8) ++ map QRDec (ball 8) ++ map QNode (ball 382).

Lemma all_states_spec : forall a, In a all_states.
Proof.
  intros a. unfold all_states. rewrite !in_app_iff.
  destruct a;
    first [ left; unfold fixed_states; cbn [In]; repeat (first [left; reflexivity | right]); fail
          | do 1 right; left; apply in_map, ball_spec
          | do 2 right; left; apply in_map, ball_spec
          | do 3 right; left; apply in_map, ball_spec
          | do 4 right; left; apply in_map, ball_spec
          | do 5 right; left; apply in_map, ball_spec
          | do 6 right; apply in_map, ball_spec ].
Qed.

Module ZFCtx <: Ctx.
  Definition Q := state.
  Definition Sym := bool.
  Definition q0 := QBootA.
  Definition s0 := false.
  Definition q1 := QBootB.
  Lemma q0_neq_q1 : q0 <> q1. Proof. discriminate. Qed.
  Definition s1 := true.
  Lemma s0_neq_s1 : s0 <> s1. Proof. discriminate. Qed.
  Definition eqb_q := state_eq_dec.
  Definition eqb_sym := bool_dec.
  Definition all_qs := all_states.
  Definition all_qs_spec := all_states_spec.
  Definition all_syms := [false; true].
  Lemma all_syms_spec : forall a, In a all_syms.
  Proof. intros []; simpl; tauto. Qed.
End ZFCtx.

Module ZFTM := TM.TM ZFCtx.
Export ZFTM.

(** ** The transition function, following TMBuilder.generate. *)

(* the transition of a DAG node reading bit [b], whose edge for [b] is [e] *)
Definition edge_trans (e : edge) (b : bool) : option (bool * dir * state) :=
  match e with
  | ENode n => Some (b, R, Node n)
  | EInc r => Some (b, R, RInc r)
  | EDecnz r => Some (b, R, RDec r)
  | EHalt => Some (b, R, QHalt)
  | EBreak k =>
      if b then Some (false, L, Brk k)
      else match k with
           | 0 => Some (true, L, Cont 0)
           | S k' => Some (false, L, Brk k')
           end
  | EContinue k =>
      if b then Some (false, L, Cont (k - 1)) else Some (false, L, Cont k)
  end.

Definition node_edge (n : nat) (b : bool) : edge :=
  if b then snd (dagpa_nodes n) else fst (dagpa_nodes n).

Definition tm : TM := fun '(q, s) =>
  match q, s with
  (* 0. boot *)
  | QBootA, false => Some (true, R, QBootB)
  | QBootA, true => Some (false, L, QBootC)
  | QBootB, false => Some (false, R, QBootC)
  | QBootB, true => Some (false, R, QBootB)
  | QBootC, false => Some (true, L, QBootD)
  | QBootC, true => Some (false, R, QBootE)
  | QBootD, false => Some (false, L, QBootE)
  | QBootD, true => Some (false, L, Cont 4)
  | QBootE, false => Some (true, L, QBootA)
  | QBootE, true => Some (false, L, QBootB)
  (* 1. decnz *)
  | QDec, false => Some (true, R, QDecB)
  | QDec, true => Some (true, L, QDecG)
  | QDecB, false => Some (false, R, QDecB)
  | QDecB, true => Some (false, R, QDecC)
  | QDecC, false => Some (true, R, QDecD)
  | QDecC, true => Some (true, R, QDecC)
  | QDecD, false => Some (false, R, QDecE)
  | QDecD, true => Some (false, R, QDecC)
  | QDecE, false => Some (false, L, QDec)
  | QDecE, true => Some (true, R, QDecE)
  | QDecG, false => Some (false, L, QRet2)
  | QDecG, true => Some (true, R, QDecH)
  | QDecH, false => Some (true, R, QDecI)
  | QDecH, true => Some (false, R, QDecH)
  | QDecI, false => Some (false, L, QSel)
  | QDecI, true => Some (true, R, QDecE)
  (* 1. inc *)
  | QInc, false => Some (true, R, QIncB)
  | QInc, true => None
  | QIncB, false => Some (false, R, QIncB)
  | QIncB, true => Some (true, R, QIncC)
  | QIncC, false => Some (false, R, QIncD)
  | QIncC, true => Some (true, R, QIncC)
  | QIncD, false => Some (true, L, QRet1)
  | QIncD, true => Some (true, R, QIncC)
  (* 1. sel *)
  | QSel, false => Some (true, R, QSelB)
  | QSel, true => Some (false, L, QRet1)
  | QSelB, false => Some (false, R, QSelB)
  | QSelB, true => Some (true, R, QSelC)
  | QSelC, false => Some (false, R, QSelD)
  | QSelC, true => Some (true, R, QSelC)
  | QSelD, false => Some (false, L, QSelE)
  | QSelD, true => Some (true, R, QSelC)
  | QSelE, false => Some (true, L, QSelF)
  | QSelE, true => Some (false, L, QRet1)
  | QSelF, false => Some (false, R, QSelE)
  | QSelF, true => Some (true, L, QSelF)
  (* 2. return *)
  | QRet1, false => Some (false, L, QRet1a)
  | QRet1, true => Some (true, L, QRet1)
  | QRet1a, false => Some (false, L, QRet1b)
  | QRet1a, true => Some (true, L, QRet1)
  | QRet1b, false => Some (false, L, QRet1b)
  | QRet1b, true => Some (false, L, Brk 0)
  | QRet2, false => Some (false, L, QRet2a)
  | QRet2, true => Some (true, L, QRet2)
  | QRet2a, false => Some (false, L, QRet2b)
  | QRet2a, true => Some (true, L, QRet2)
  | QRet2b, false => Some (false, L, QRet2b)
  | QRet2b, true => Some (false, L, Brk 1)
  (* 3. register chains: register r reads r+1 ones before reaching 1.inc / 1.decnz *)
  | QRInc r, false => Some (false, R, QSel)
  | QRInc r, true => Some (true, R, match bval r with 0 => QInc | S r' => RInc r' end)
  | QRDec r, false => Some (false, R, QSel)
  | QRDec r, true => Some (true, R, match bval r with 0 => QDec | S r' => RDec r' end)
  (* 4. dispatch: pass max_zeros + 1 zeros going left, then 5.root *)
  | QDisp i, false =>
      if Nat.ltb (S (bval i)) max_zeros then Some (false, L, Disp (S (bval i)))
      else Some (false, R, QRoot)
  | QDisp i, true => Some (true, L, Cont 0)
  (* 5. root *)
  | QRoot, false => Some (false, R, QRoot)
  | QRoot, true => Some (true, R, Node 0)
  (* 6. break / continue *)
  | QBrk k, false => match bval k with
                     | 0 => Some (true, L, Cont 0)
                     | S k' => Some (false, L, Brk k')
                     end
  | QBrk k, true => Some (false, L, QBrk k)
  | QCont k, false => match bval k with
                      | 0 => Some (false, L, Disp 0)
                      | S _ => Some (false, L, QCont k)
                      end
  | QCont k, true => match bval k with
                     | 0 => Some (true, L, Cont 0)
                     | S k' => Some (false, L, Cont k')
                     end
  (* decision DAG *)
  | QNode n, b => edge_trans (node_edge (bval n) b) b
  | QHalt, _ => None
  end.

(** ** State names (as in pa_wade.tm) *)
Definition digit (n : nat) : string := String (ascii_of_nat (48 + n)) EmptyString.

(* [reg_name], [node_name]: NamesPA.v (generated) *)

Definition name (q : state) : string :=
  match q with
  | QBootA => "0.boot.A" | QBootB => "0.boot.B" | QBootC => "0.boot.C"
  | QBootD => "0.boot.D" | QBootE => "0.boot.E"
  | QDec => "1.decnz" | QDecB => "1.decnz.b" | QDecC => "1.decnz.c" | QDecD => "1.decnz.d"
  | QDecE => "1.decnz.e" | QDecG => "1.decnz.g" | QDecH => "1.decnz.h" | QDecI => "1.decnz.i"
  | QInc => "1.inc" | QIncB => "1.inc.b" | QIncC => "1.inc.c" | QIncD => "1.inc.d"
  | QSel => "1.sel" | QSelB => "1.sel.b" | QSelC => "1.sel.c" | QSelD => "1.sel.d"
  | QSelE => "1.sel.e" | QSelF => "1.sel.f"
  | QRet1 => "2.ret1" | QRet1a => "2.ret1.1" | QRet1b => "2.ret1.2"
  | QRet2 => "2.ret2" | QRet2a => "2.ret2.1" | QRet2b => "2.ret2.2"
  | QRoot => "5.root"
  | QDisp i => "4.dispatch." ++ digit (S (bval i))
  | QBrk k => "6.break." ++ digit (bval k)
  | QCont k => "6.continue." ++ digit (bval k)
  | QRInc r => "3." ++ reg_name (bval r) ++ ".inc"
  | QRDec r => "3." ++ reg_name (bval r) ++ ".decnz"
  | QNode n => node_name (bval n)
  | QHalt => "halt"
  end.

(** ** The literal check against pa_wade.tm *)

(* the row of the table for (state name, symbol read), if any *)
Fixpoint table_lookup (t : list (string * bool * bool * bool * string)) (s : string) (b : bool)
    : option (bool * bool * string) :=
  match t with
  | [] => None
  | (s', b', w, mv, nx) :: t =>
      if andb (String.eqb s s') (Bool.eqb b b') then Some (w, mv, nx) else table_lookup t s b
  end.

Definition dir_is_R (d : dir) : bool := match d with R => true | L => false end.

Definition row_of (o : option (bool * dir * state)) : option (bool * bool * string) :=
  match o with
  | None => None
  | Some (w, d, q') => Some (w, dir_is_R d, name q')
  end.

Definition opt_row_eqb (a b : option (bool * bool * string)) : bool :=
  match a, b with
  | None, None => true
  | Some (w, m, n), Some (w', m', n') => andb (andb (Bool.eqb w w') (Bool.eqb m m')) (String.eqb n n')
  | _, _ => false
  end.

Lemma opt_row_eqb_eq : forall a b, opt_row_eqb a b = true -> a = b.
Proof.
  intros [[[w m] n]|] [[[w' m'] n']|]; simpl; try discriminate; [|reflexivity].
  intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Bool.eqb_prop in H1, H2. apply String.eqb_eq in H3. subst. reflexivity.
Qed.

Fixpoint nodupb (l : list string) : bool :=
  match l with
  | [] => true
  | x :: l => andb (negb (existsb (String.eqb x) l)) (nodupb l)
  end.

Lemma nodupb_spec : forall l, nodupb l = true -> NoDup l.
Proof.
  induction l as [|x l IH]; simpl; intros H; [constructor|].
  apply andb_prop in H as [H1 H2]. constructor; [|auto].
  intros Hin. apply negb_true_iff in H1.
  assert (existsb (String.eqb x) l = true) by (apply existsb_exists; exists x; split;
    [assumption | apply String.eqb_refl]).
  congruence.
Qed.

Definition row_key (r : string * bool * bool * bool * string) : string :=
  let '(s, b, _, _, _) := r in s ++ (if b then " 1" else " 0").

Definition check_rows : bool :=
  forallb (fun q => forallb (fun b => opt_row_eqb (table_lookup pa_table (name q) b) (row_of (tm (q, b))))
                            [false; true]) all_states.

Definition check_no_extra : bool :=
  forallb (fun r => let '(s, _, _, _, _) := r in existsb (fun q => String.eqb s (name q)) all_states)
          pa_table.

Lemma check_rows_ok : check_rows = true. Proof. vm_compute. reflexivity. Qed.
Lemma check_no_extra_ok : check_no_extra = true. Proof. vm_compute. reflexivity. Qed.
Lemma names_nodup_ok : nodupb (map name all_states) = true. Proof. vm_compute. reflexivity. Qed.
Lemma keys_nodup_ok : nodupb (map row_key pa_table) = true. Proof. vm_compute. reflexivity. Qed.

(** The trust anchor: [tm] is exactly the transition table of pa_wade.tm.
    - for every state [q] and symbol [b], the row of pa_wade.tm for (name q, b) is the transition
      [tm (q, b)] (with the target state's name), and there is no row iff [tm] has no transition;
    - every row of pa_wade.tm belongs to a state of [tm]; state names are distinct (so names identify
      states) and rows have distinct keys;
    - the start state is "0.boot.A" (the [#! start] line of pa_wade.tm) and the blank symbol is 0. *)
Theorem tm_table :
  (forall q b, table_lookup pa_table (name q) b = row_of (tm (q, b))) /\
  (forall s b w mv nx, In (s, b, w, mv, nx) pa_table -> exists q, name q = s) /\
  NoDup (map name all_states) /\
  NoDup (map row_key pa_table) /\
  name q0 = "0.boot.A" /\ s0 = false /\
  List.length all_states = 450 /\ List.length pa_table = 897.
Proof.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - intros q b. apply opt_row_eqb_eq.
    pose proof check_rows_ok as H. unfold check_rows in H. rewrite forallb_forall in H.
    specialize (H q (all_states_spec q)). rewrite forallb_forall in H.
    apply H. destruct b; simpl; tauto.
  - intros s b w mv nx Hin. pose proof check_no_extra_ok as H. unfold check_no_extra in H.
    rewrite forallb_forall in H. specialize (H _ Hin).
    change (existsb (fun q => String.eqb s (name q)) all_states = true) in H.
    apply existsb_exists in H as [q [_ Hq]]. apply String.eqb_eq in Hq. exists q. auto.
  - apply nodupb_spec, names_nodup_ok.
  - apply nodupb_spec, keys_nodup_ok.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.
