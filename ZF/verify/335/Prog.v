(** * Prog: the concrete DAG [zf2] (ZF2Dag.v) refines the abstract enumerator step (Enum.v).

    One structured big-step run of the root node from a register file encoding an enumerator
    state [s] is exactly one [enum_step]: it halts iff the new topwff is 1, and otherwise ends in a
    register file encoding [enum_step s].  Loop-head invariant: scratch1..3 = 0 and param1..3 = 0
    (B6a, the last clause, zeroes the params); axiomcode is arbitrary (main() zeroes it).  The lemmas
    (one per subroutine node of the DAG of R3Y1_335) are in ProgLib.v.

    Register files are functions, so "ends in the encoding" is stated pointwise
    ([forall i, R' i = enc .. i]): equality of functions would need functional extensionality. *)

From Coq Require Import Lists.List Arith.Arith Lia Bool.Bool.
From ZF Require Import RM ZF2Dag Logic Enum ProgLib.
Import ListNotations.

(** Registers: 0 prooflist, 1 nextproof, 2 topwff, 3 wffstack, 4 axiomcode, 5..7 param1..3,
    8..10 scratch1..3 (all others 0). *)
Definition enc (s : state) (ac p1 p2 p3 : nat) : regs :=
  fun i => match i with
           | 0 => pl s | 1 => np s | 2 => tw s | 3 => ws s
           | 4 => ac | 5 => p1 | 6 => p2 | 7 => p3 | _ => 0
           end.

Definition st_of (s : state) (ac p1 p2 p3 : nat) : St := mkSt (pl s) (np s) (tw s) (ws s) ac p1 p2 p3 0 0 0.

(* the loop-head register file: params and scratch registers 0 *)
Definition st0 (s : state) (ac : nat) : St := st_of s ac 0 0 0.

Lemma approx_enc R s ac p1 p2 p3 :
  approx R (st_of s ac p1 p2 p3) <-> forall i, R i = enc s ac p1 p2 p3 i.
Proof. split; intros H i; rewrite H; do 11 (destruct i as [|i]; [reflexivity|]); reflexivity. Qed.

Lemma iter00 z : Nat.iter z unpair_step (0, 0) = unpair z.
Proof. reflexivity. Qed.

(** ** The prefix of main(): fetch the next proof and decode axiomcode, param1..3. *)
Lemma prefix_ok pl np t w ac pl1 np1 a pl2 q1 pl3 q2 pl4 q3 pl5 :
  (if Nat.eqb pl 0 then (np, S np) else (pred pl, np)) = (pl1, np1) ->
  unpair pl1 = (a, pl2) -> unpair pl2 = (q1, pl3) -> unpair pl3 = (q2, pl4) -> unpair pl4 = (q3, pl5) ->
  seqx prefix (mkSt pl np t w ac 0 0 0 0 0 0) XNormal (mkSt pl5 np1 t w a q1 q2 q3 0 0 0).
Proof.
  intros Hp E1 E2 E3 E4. unfold prefix.
  destruct pl as [|v]; injection Hp as <- <-; repeat step; apply sx_nil_eq;
    rewrite ?Nat.add_0_l, ?iter00, ?Nat.add_0_r, E1; cbn [fst snd];
    rewrite ?iter00, E2; cbn [fst snd]; rewrite ?iter00, E3; cbn [fst snd];
    rewrite ?iter00, E4; reflexivity.
Qed.

(** ** The 15 clauses: the final topwff/wffstack is the active clause's (Enum.enum_step). *)
Definition clause_result (a q1 q2 q3 w : nat) : nat * nat :=
  if Nat.eqb a 0 then (0, w) else apply_clause (nth (Nat.min a 15 - 1) axiomorder 14) q1 q2 q3 w.

(* B6a's two destructive tests, in program order, versus Enum's side condition *)
Lemma b6a_if a b c X : (if Nat.eqb a b then 0 else if Nat.eqb c b then 0 else X) =
  (if Nat.eqb b c || Nat.eqb b a then 0 else X).
Proof.
  rewrite (Nat.eqb_sym a b), (Nat.eqb_sym c b).
  destruct (Nat.eqb b a), (Nat.eqb b c); reflexivity.
Qed.

Lemma fold_cons_eq c l m m' r : clause_post c m = m' ->
  fold_left (fun m c => clause_post c m) l m' = r -> fold_left (fun m c => clause_post c m) (c :: l) m = r.
Proof. intros <- H; exact H. Qed.

(* evaluate the fold one clause at a time, normalizing the record in between (a lazy evaluation of
   the whole fold would duplicate the unevaluated state exponentially) *)
Ltac fold_eval :=
  repeat (eapply fold_cons_eq;
          [cbn [clause_post get set Nat.pred]; rewrite ?unpair_pair;
           repeat match goal with H : unpair _ = _ |- _ => rewrite H end; cbn [fst snd]; reflexivity|]).

(* closed clauses (EXT, INF) placed after B6a see zeroed params; their wffs do not mention them *)
Ltac closed_fin := cbn [fold_left clause]; unfold clause_11, clause_13; reflexivity.

Lemma fold_clauses pl5 np1 t w a q1 q2 q3 :
  exists a',
    fold_left (fun m c => clause_post c m) axiomorder (mkSt pl5 np1 0 (push t w) a q1 q2 q3 0 0 0) =
    mkSt pl5 np1 (fst (clause_result a q1 q2 q3 (push t w))) (snd (clause_result a q1 q2 q3 (push t w)))
         a' 0 0 0 0 0 0.
Proof.
  unfold clause_result, push, axiomorder, apply_clause, pop.
  do 16 (destruct a as [|a];
    [ cbn [Nat.eqb Nat.min nth Nat.sub apply_clause pop fst snd]; rewrite ?unpair_pair; cbn [fst snd];
      try (destruct (unpair w) eqn:?; cbn [fst snd]); rewrite <- ?b6a_if;
      eexists; fold_eval; closed_fin |]).
  cbn [Nat.eqb Nat.min nth Nat.sub apply_clause pop fst snd]. rewrite <- ?b6a_if.
  eexists; fold_eval; closed_fin.
Qed.

Lemma clauses_lt : Forall (fun c => c < 15) axiomorder.
Proof. repeat constructor. Qed.

(** ** One iteration of main() on abstract register files. *)
Theorem root_sem s ac :
  (tw (enum_step s) = 1 -> exists m', sem (ENode 0) (st0 s ac) XHalt m') /\
  (tw (enum_step s) <> 1 -> exists ac', sem (ENode 0) (st0 s ac) XNormal (st0 (enum_step s) ac')).
Proof.
  destruct s as [pl np t w]. unfold enum_step, st0, st_of. cbn [Enum.pl Enum.np Enum.tw Enum.ws].
  destruct (if Nat.eqb pl 0 then (np, S np) else (pred pl, np)) as [pl1 np1] eqn:Hp.
  destruct (unpair pl1) as [a pl2] eqn:E1. destruct (unpair pl2) as [q1 pl3] eqn:E2.
  destruct (unpair pl3) as [q2 pl4] eqn:E3. destruct (unpair pl4) as [q3 pl5] eqn:E4.
  pose proof (prefix_ok pl np t w ac pl1 np1 a pl2 q1 pl3 q2 pl4 q3 pl5 Hp E1 E2 E3 E4) as Hpre.
  destruct (fold_clauses pl5 np1 t w a q1 q2 q3) as (a' & Hf).
  fold (clause_result a q1 q2 q3 (push t w)).
  destruct (clause_result a q1 q2 q3 (push t w)) as [t' w'] eqn:Ec. cbn [fst snd] in Hf |- *.
  assert (Hbody : seqx (prefix ++ [ENode 197] ++ flat_map CL axiomorder) (mkSt pl np t w ac 0 0 0 0 0 0)
                       XNormal (mkSt pl5 np1 t' w' a' 0 0 0 0 0 0)).
  { eapply seqx_app; [exact Hpre|].
    eapply sx_normal; [apply pushwff197; reflexivity|]. cbn [get set].
    rewrite <- Hf. apply clauses_ok; [exact clauses_lt | reflexivity ..]. }
  assert (Hmain : forall x m', seqx [ENode check_node] (mkSt pl5 np1 t' w' a' 0 0 0 0 0 0) x m' ->
            sem (ENode 0) (mkSt pl np t w ac 0 0 0 0 0 0) x m').
  { intros x m' H. apply seq_node. rewrite main_flat. unfold main_list.
    rewrite app_assoc, app_assoc. eapply seqx_app; [rewrite <- app_assoc; exact Hbody | exact H]. }
  split; intros Ht.
  - destruct (check122_halt (mkSt pl5 np1 t' w' a' 0 0 0 0 0 0) Ht) as [m' Hm].
    exists m'. apply Hmain. apply sx_halt, Hm.
  - exists a'. apply Hmain.
    eapply sx_normal; [apply check122_normal, Ht | constructor].
Qed.

(** ** The theorems on the register machine. *)
Theorem root_step_gen s ac R : (forall i, R i = enc s ac 0 0 0 i) ->
  (tw (enum_step s) = 1 -> exists R', run zf2 (ENode 0) R XHalt R') /\
  (tw (enum_step s) <> 1 -> exists ac' R',
     run zf2 (ENode 0) R XNormal R' /\ forall i, R' i = enc (enum_step s) ac' 0 0 0 i).
Proof.
  intros HR. apply (approx_enc R s ac 0 0 0) in HR. destruct (root_sem s ac) as [Hh Hn]. split; intros Ht.
  - destruct (Hh Ht) as [m' Hm]. destruct (Hm R HR) as (R' & Hr & _). exists R'; exact Hr.
  - destruct (Hn Ht) as (ac' & Hm). destruct (Hm R HR) as (R' & Hr & HR').
    exists ac', R'. split; [exact Hr | apply (approx_enc R' (enum_step s) ac' 0 0 0), HR'].
Qed.

Theorem root_step s ac :
  (tw (enum_step s) = 1 -> exists R', run zf2 (ENode 0) (enc s ac 0 0 0) XHalt R') /\
  (tw (enum_step s) <> 1 -> exists ac' R',
     run zf2 (ENode 0) (enc s ac 0 0 0) XNormal R' /\ forall i, R' i = enc (enum_step s) ac' 0 0 0 i).
Proof. apply (root_step_gen s ac). reflexivity. Qed.

Theorem root_step_det s ac R x R' : (forall i, R i = enc s ac 0 0 0 i) ->
  run zf2 (ENode 0) R x R' ->
  (x = XHalt /\ tw (enum_step s) = 1) \/
  (x = XNormal /\ tw (enum_step s) <> 1 /\ exists ac', forall i, R' i = enc (enum_step s) ac' 0 0 0 i).
Proof.
  intros HR Hr. destruct (root_step_gen s ac R HR) as [Hh Hn].
  destruct (Nat.eq_dec (tw (enum_step s)) 1) as [Ht | Ht].
  - left. destruct (Hh Ht) as [R2 Hr2]. destruct (run_det _ _ _ _ _ Hr _ _ Hr2) as [-> _]. auto.
  - right. destruct (Hn Ht) as (ac' & R2 & Hr2 & HR2).
    destruct (run_det _ _ _ _ _ Hr _ _ Hr2) as [-> ->]. eauto 7.
Qed.

Theorem iter_halts_iff_gen s ac R : (forall i, R i = enc s ac 0 0 0 i) ->
  iter_halts zf2 R <-> exists n, tw (Nat.iter (S n) enum_step s) = 1.
Proof.
  intros HR. split.
  - intros H. revert s ac HR. induction H as [R R' Hr | R R' Hr H IH]; intros s ac HR.
    + destruct (root_step_det s ac R _ R' HR Hr) as [[_ Ht] | [? _]]; [|discriminate].
      exists 0. exact Ht.
    + destruct (root_step_det s ac R _ R' HR Hr) as [[? _] | (_ & _ & ac' & HR')]; [discriminate|].
      destruct (IH _ _ HR') as [n Hn]. exists (S n). rewrite Nat.iter_succ_r. exact Hn.
  - intros [n Hn]. revert s ac R HR Hn. induction n as [|n IH]; intros s ac R HR Hn.
    + destruct (root_step_gen s ac R HR) as [Hh _]. destruct (Hh Hn) as [R' Hr].
      exact (iter_halt zf2 R R' Hr).
    + destruct (root_step_gen s ac R HR) as [Hh Hnn].
      destruct (Nat.eq_dec (tw (enum_step s)) 1) as [Ht | Ht].
      * destruct (Hh Ht) as [R' Hr]. exact (iter_halt zf2 R R' Hr).
      * destruct (Hnn Ht) as (ac' & R' & Hr & HR').
        apply (iter_next zf2 R R' Hr). apply (IH (enum_step s) ac' R' HR').
        rewrite <- Nat.iter_succ_r. exact Hn.
Qed.

Corollary iter_halts_iff s ac :
  iter_halts zf2 (enc s ac 0 0 0) <-> exists n, tw (Nat.iter (S n) enum_step s) = 1.
Proof. apply (iter_halts_iff_gen s ac). reflexivity. Qed.

(* the machine starts with all registers 0 *)
Corollary iter_halts_regs0 : iter_halts zf2 regs0 <-> enum_halts.
Proof.
  unfold enum_halts. apply (iter_halts_iff_gen s0 0).
  intros i. do 11 (destruct i as [|i]; [reflexivity|]); reflexivity.
Qed.

Print Assumptions root_step.
Print Assumptions root_step_det.
Print Assumptions iter_halts_iff.
Print Assumptions iter_halts_regs0.
