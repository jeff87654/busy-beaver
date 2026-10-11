(** * MainGlue: assembles the verified layers, with the two layers still in progress (L2, L3)
    as section hypotheses.  Main.v instantiates them.

      TMH  <->  rm_halts zf2 ([], regs0)                       (L3, hypothesis)
           <->  iter_halts zf2 regs0                           (RMEquiv: rm_halts_iff_iter, zf2_wf)
           <->  iter_halts zf2 (enc_spec s0 0 0 0 0)           (registers equal pointwise)
           <->  exists n, tw (Nat.iter (S n) enum_step s0) = 1  (L2, hypothesis)
           <->  prov (Wel v0 v0)                               (L1: enum_halts_iff) *)

From Coq Require Import Arith.Arith Lia Lists.List.
From ZF Require Import Logic Enum L1 RM ZF2Dag RMEquiv.
Import ListNotations.

(** ** Big-step runs respect pointwise-equal registers (no functional extensionality) *)

Definition req (R R2 : regs) : Prop := forall i, R i = R2 i.

Lemma upd_req R R2 r v : req R R2 -> req (upd R r v) (upd R2 r v).
Proof. intros E i. unfold upd. destruct (Nat.eqb i r); auto. Qed.

Lemma run_req p e R x R' :
  run p e R x R' -> forall Rb, req R Rb -> exists Rb', run p e Rb x Rb' /\ req R' Rb'.
Proof.
  induction 1; intros Rb E.
  - exists (upd Rb r (S (Rb r))). split; [apply run_inc|]. rewrite (E r). apply upd_req, E.
  - exists (upd Rb r v). split; [apply run_decnz_pos; rewrite <- (E r); assumption | apply upd_req, E].
  - exists Rb. split; [apply run_decnz_zero; rewrite <- (E r); assumption | exact E].
  - exists Rb. split; [apply run_break0 | exact E].
  - exists Rb. split; [apply run_breakS | exact E].
  - exists Rb. split; [apply run_continue | exact E].
  - exists Rb. split; [apply run_halt | exact E].
  - destruct (IHrun Rb E) as (Rb' & G1 & E1). exists Rb'. split; [now apply run_node_car_break1 | exact E1].
  - destruct (IHrun Rb E) as (Rb' & G1 & E1). exists Rb'. split; [now apply run_node_car_breakS | exact E1].
  - destruct (IHrun Rb E) as (Rb' & G1 & E1). exists Rb'. split; [now apply run_node_car_continue | exact E1].
  - destruct (IHrun Rb E) as (Rb' & G1 & E1). exists Rb'. split; [now apply run_node_car_halt | exact E1].
  - destruct (IHrun1 Rb E) as (R3 & G1 & E1). destruct (IHrun2 R3 E1) as (R4 & G2 & E2).
    exists R4. split; [eapply run_node_cdr_normal; eauto | exact E2].
  - destruct (IHrun1 Rb E) as (R3 & G1 & E1). destruct (IHrun2 R3 E1) as (R4 & G2 & E2).
    exists R4. split; [eapply run_node_cdr_break; eauto | exact E2].
  - destruct (IHrun1 Rb E) as (R3 & G1 & E1). destruct (IHrun2 R3 E1) as (R4 & G2 & E2).
    destruct (IHrun3 R4 E2) as (R5 & G3 & E3).
    exists R5. split; [eapply run_node_cdr_continue1; eauto | exact E3].
  - destruct (IHrun1 Rb E) as (R3 & G1 & E1). destruct (IHrun2 R3 E1) as (R4 & G2 & E2).
    exists R4. split; [eapply run_node_cdr_continueS; eauto | exact E2].
  - destruct (IHrun1 Rb E) as (R3 & G1 & E1). destruct (IHrun2 R3 E1) as (R4 & G2 & E2).
    exists R4. split; [eapply run_node_cdr_halt; eauto | exact E2].
Qed.

Lemma iter_halts_req p R R2 : req R R2 -> iter_halts p R -> iter_halts p R2.
Proof.
  intros E H. revert R2 E. induction H as [R R' Hr | R R' Hr _ IH]; intros R2 E.
  - destruct (run_req _ _ _ _ _ Hr R2 E) as (R2' & H2 & _). eapply iter_halt; eauto.
  - destruct (run_req _ _ _ _ _ Hr R2 E) as (R2' & H2 & E2).
    eapply iter_next; [exact H2 | exact (IH R2' E2)].
Qed.

Lemma iter_halts_req_iff p R R2 : req R R2 -> (iter_halts p R <-> iter_halts p R2).
Proof.
  intros E. split; apply iter_halts_req; [exact E|]. intro i. symmetry. apply E.
Qed.

(** ** Register encoding of an enumerator state (copy of Prog.v's [enc]) *)

Definition enc_spec (s : Enum.state) (ac p1 p2 p3 : nat) : regs :=
  fun i => match i with
           | 0 => pl s | 1 => np s | 2 => tw s | 3 => ws s
           | 4 => ac | 5 => p1 | 6 => p2 | 7 => p3 | _ => 0
           end.

Lemma enc_spec_s0 : req regs0 (enc_spec s0 0 0 0 0).
Proof. intro i. do 8 (destruct i as [|i]; [reflexivity|]). reflexivity. Qed.

(** ** Glue *)

Section Glue.

Variable TMH : Prop.

(* L3: the Turing machine simulates the path semantics of zf2 from boot *)
Hypothesis tm_halts_iff_rm : TMH <-> rm_halts zf2 ([], regs0).

(* L2: the program implements the abstract enumerator (loop head: param1..3 = 0, see Prog.v) *)
Hypothesis iter_halts_iff : forall s ac,
  iter_halts zf2 (enc_spec s ac 0 0 0) <-> exists n, tw (Nat.iter (S n) enum_step s) = 1.

Theorem glue : TMH <-> prov (Wel v0 v0).
Proof.
  rewrite tm_halts_iff_rm, (rm_halts_iff_iter zf2 zf2_wf regs0).
  rewrite (iter_halts_req_iff zf2 _ _ enc_spec_s0), iter_halts_iff.
  exact enum_halts_iff.
Qed.

End Glue.

Print Assumptions glue.
