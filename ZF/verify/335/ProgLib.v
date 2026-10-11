(** * ProgLib: lemmas for Prog.v (the concrete DAG [zf2] refines the abstract enumerator step).

    Prog.v proves: one structured big-step run of the root node from a register file encoding an enumerator
    state is exactly one [enum_step]: it halts iff the new topwff is 1, and otherwise ends in the
    encoding of the next state (scratch and param registers 0 at every loop head; axiomcode arbitrary).

    Method.  Register files are related pointwise to an 11-field record [St] ([approx]); [sem e m x m']
    says every register file matching [m] runs edge [e] to exit [x] and a file matching [m'].  Nodes that
    are plain sequences are flattened ([expand]) into lists of "atoms" (nodes with their own lemma) by
    computation; atoms with control flow (while_decnz loops, pair, unpair, if_eq, cparam, ...) are proved
    by induction.  The main() body flattens to prefix ++ (clauses in axiomorder) ++ [halt check]; each
    clause is executed symbolically on wff codes (never computing concrete values). *)

From Coq Require Import Lists.List Arith.Arith Lia Bool.Bool.
From ZF Require Import RM ZF2Dag Logic Enum.
Import ListNotations.

(** ** Determinism of the big-step semantics (generic in the program). *)
Lemma run_det p e R x1 R1 :
  run p e R x1 R1 -> forall x2 R2, run p e R x2 R2 -> x1 = x2 /\ R1 = R2.
Proof.
  induction 1; intros x2 Rz H2; inversion H2; subst;
    repeat match goal with
    | IH : forall x R0, run ?p ?e ?R x R0 -> _, H : run ?p ?e ?R _ _ |- _ =>
        let E := fresh "E" in let F := fresh "F" in
        destruct (IH _ _ H) as [E F]; clear H; subst;
        try discriminate E; try (injection E; intros; subst)
    end;
    try congruence; auto.
  rewrite H in H1; injection H1 as ->; auto.
Qed.

(** ** Abstract register files: 11 registers (all others are 0 and never touched). *)
Record St : Type := mkSt {
  r_pl : nat; r_np : nat; r_tw : nat; r_ws : nat; r_ac : nat;
  r_p1 : nat; r_p2 : nat; r_p3 : nat; r_s1 : nat; r_s2 : nat; r_s3 : nat }.

Definition get (m : St) (i : nat) : nat :=
  let 'mkSt a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 := m in
  match i with
  | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => a4 | 5 => a5
  | 6 => a6 | 7 => a7 | 8 => a8 | 9 => a9 | 10 => a10 | _ => 0
  end.

Definition set (m : St) (i v : nat) : St :=
  let 'mkSt a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 := m in
  match i with
  | 0 => mkSt v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  | 1 => mkSt a0 v a2 a3 a4 a5 a6 a7 a8 a9 a10
  | 2 => mkSt a0 a1 v a3 a4 a5 a6 a7 a8 a9 a10
  | 3 => mkSt a0 a1 a2 v a4 a5 a6 a7 a8 a9 a10
  | 4 => mkSt a0 a1 a2 a3 v a5 a6 a7 a8 a9 a10
  | 5 => mkSt a0 a1 a2 a3 a4 v a6 a7 a8 a9 a10
  | 6 => mkSt a0 a1 a2 a3 a4 a5 v a7 a8 a9 a10
  | 7 => mkSt a0 a1 a2 a3 a4 a5 a6 v a8 a9 a10
  | 8 => mkSt a0 a1 a2 a3 a4 a5 a6 a7 v a9 a10
  | 9 => mkSt a0 a1 a2 a3 a4 a5 a6 a7 a8 v a10
  | 10 => mkSt a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 v
  | _ => m
  end.

Definition inc (r : nat) (m : St) : St := set m r (S (get m r)).

Definition clr23 (m : St) : St := set (set m 9 0) 10 0.

(* one step of Wade's unpair walk on registers (o1, o2) *)
Definition ustep (o1 o2 : nat) (m : St) : St :=
  set (set m o1 (fst (unpair_step (get m o1, get m o2)))) o2 (snd (unpair_step (get m o1, get m o2))).

(* result of unpair(o1, o2, i) *)
Definition unpair_post (i o1 o2 : nat) (m : St) : St :=
  set (set (set m i 0) o1 (fst (Nat.iter (get m i) unpair_step (get m o1, get m o2))))
      o2 (snd (Nat.iter (get m i) unpair_step (get m o1, get m o2))).

Lemma get_set m r i v : r <= 10 -> get (set m r v) i = if Nat.eqb i r then v else get m i.
Proof.
  intros Hr; destruct m.
  do 11 (destruct r as [|r]; [do 11 (destruct i as [|i]; [reflexivity|]); reflexivity|]); lia.
Qed.

Definition approx (R : regs) (m : St) : Prop := forall i, R i = get m i.

Lemma approx_upd R m r v : r <= 10 -> approx R m -> approx (upd R r v) (set m r v).
Proof.
  intros Hr H i. unfold upd. rewrite get_set by exact Hr.
  destruct (Nat.eqb i r); auto.
Qed.

(** [sem e m x m']: from any register file matching [m], edge [e] runs to exit [x] and a file
    matching [m']. *)
Definition sem (e : edge) (m : St) (x : exit) (m' : St) : Prop :=
  forall R, approx R m -> exists R', run zf2 e R x R' /\ approx R' m'.

Lemma sem_conseq e m x m1 m2 : sem e m x m1 -> m1 = m2 -> sem e m x m2.
Proof. intros H <-; exact H. Qed.

Lemma sem_inc r m : r <= 10 -> sem (EInc r) m XNormal (inc r m).
Proof.
  intros Hr R HR. exists (upd R r (S (R r))). split; [constructor|].
  unfold inc. rewrite (HR r). apply approx_upd; auto.
Qed.

Lemma sem_decnz_pos r m v : r <= 10 -> get m r = S v -> sem (EDecnz r) m XNormal (set m r v).
Proof.
  intros Hr Hv R HR. exists (upd R r v). split.
  - constructor. rewrite HR; exact Hv.
  - apply approx_upd; auto.
Qed.

Lemma sem_decnz_zero r m : get m r = 0 -> sem (EDecnz r) m (XBreak 1) m.
Proof. intros H0 R HR. exists R. split; auto. constructor. rewrite HR; exact H0. Qed.

Lemma sem_breakS k m : sem (EBreak (S k)) m (XBreak (S k)) m.
Proof. intros R HR. exists R. split; auto. constructor. Qed.

Lemma sem_cont k m : sem (EContinue (S k)) m (XContinue (S k)) m.
Proof. intros R HR. exists R. split; auto. constructor. Qed.

Lemma sem_halt m : sem EHalt m XHalt m.
Proof. intros R HR. exists R. split; auto. constructor. Qed.

Section NodeRules.
Variables (n : nat) (a b : edge).
Hypothesis Hn : zf2_nodes n = (a, b).

Lemma sem_car_break1 m m' : sem a m (XBreak 1) m' -> sem (ENode n) m XNormal m'.
Proof.
  intros H R HR. destruct (H R HR) as (R' & Hr & HR'). exists R'. split; auto.
  apply run_node_car_break1. cbn. rewrite Hn. exact Hr.
Qed.

Lemma sem_car_breakS k m m' : sem a m (XBreak (S (S k))) m' -> sem (ENode n) m (XBreak (S k)) m'.
Proof.
  intros H R HR. destruct (H R HR) as (R' & Hr & HR'). exists R'. split; auto.
  apply run_node_car_breakS. cbn. rewrite Hn. exact Hr.
Qed.

Lemma sem_car_continue k m m' : sem a m (XContinue (S k)) m' -> sem (ENode n) m (XContinue (S k)) m'.
Proof.
  intros H R HR. destruct (H R HR) as (R' & Hr & HR'). exists R'. split; auto.
  apply run_node_car_continue. cbn. rewrite Hn. exact Hr.
Qed.

Lemma sem_car_halt m m' : sem a m XHalt m' -> sem (ENode n) m XHalt m'.
Proof.
  intros H R HR. destruct (H R HR) as (R' & Hr & HR'). exists R'. split; auto.
  apply run_node_car_halt. cbn. rewrite Hn. exact Hr.
Qed.

Lemma sem_cdr_normal m m1 m' : sem a m XNormal m1 -> sem b m1 XNormal m' -> sem (ENode n) m XNormal m'.
Proof.
  intros H1 H2 R HR. destruct (H1 R HR) as (R1 & Hr1 & HR1).
  destruct (H2 R1 HR1) as (R' & Hr & HR'). exists R'. split; auto.
  eapply run_node_cdr_normal; cbn; rewrite Hn; eauto.
Qed.

Lemma sem_cdr_break k m m1 m' : sem a m XNormal m1 -> sem b m1 (XBreak (S k)) m' ->
  sem (ENode n) m (XBreak (S k)) m'.
Proof.
  intros H1 H2 R HR. destruct (H1 R HR) as (R1 & Hr1 & HR1).
  destruct (H2 R1 HR1) as (R' & Hr & HR'). exists R'. split; auto.
  eapply run_node_cdr_break; cbn; rewrite Hn; eauto.
Qed.

Lemma sem_cdr_continue1 m m1 m2 x m' : sem a m XNormal m1 -> sem b m1 (XContinue 1) m2 ->
  sem (ENode n) m2 x m' -> sem (ENode n) m x m'.
Proof.
  intros H1 H2 H3 R HR. destruct (H1 R HR) as (R1 & Hr1 & HR1).
  destruct (H2 R1 HR1) as (R2 & Hr2 & HR2). destruct (H3 R2 HR2) as (R' & Hr & HR').
  exists R'. split; auto.
  eapply run_node_cdr_continue1; [cbn; rewrite Hn; eauto | cbn; rewrite Hn; eauto | exact Hr].
Qed.

Lemma sem_cdr_continueS k m m1 m' : sem a m XNormal m1 -> sem b m1 (XContinue (S (S k))) m' ->
  sem (ENode n) m (XContinue (S k)) m'.
Proof.
  intros H1 H2 R HR. destruct (H1 R HR) as (R1 & Hr1 & HR1).
  destruct (H2 R1 HR1) as (R' & Hr & HR'). exists R'. split; auto.
  eapply run_node_cdr_continueS; cbn; rewrite Hn; eauto.
Qed.

Lemma sem_cdr_halt m m1 m' : sem a m XNormal m1 -> sem b m1 XHalt m' -> sem (ENode n) m XHalt m'.
Proof.
  intros H1 H2 R HR. destruct (H1 R HR) as (R1 & Hr1 & HR1).
  destruct (H2 R1 HR1) as (R' & Hr & HR'). exists R'. split; auto.
  eapply run_node_cdr_halt; cbn; rewrite Hn; eauto.
Qed.

End NodeRules.

(** ** while_decnz(r, body): node [n] = (decnz r, b), [b] exits with continue 1. *)
Lemma sem_while n r b (g P : St -> St) :
  zf2_nodes n = (EDecnz r, b) -> r <= 10 ->
  (forall m, sem b m (XContinue 1) (g m)) ->
  (forall m, get (g m) r = get m r) ->
  (forall m, get m r = 0 -> P m = m) ->
  (forall m v, get m r = S v -> P m = P (g (set m r v))) ->
  forall m, sem (ENode n) m XNormal (P m).
Proof.
  intros Hn Hr Hb Hg HP0 HPS.
  assert (H : forall k m, get m r = k -> sem (ENode n) m XNormal (P m)).
  { induction k as [|k IH]; intros m Hk.
    - rewrite (HP0 m Hk). eapply sem_car_break1; [exact Hn|]. apply sem_decnz_zero; exact Hk.
    - rewrite (HPS m k Hk). eapply sem_cdr_continue1; [exact Hn| | apply Hb |].
      + apply sem_decnz_pos; [exact Hr | exact Hk].
      + apply IH. rewrite Hg, get_set by exact Hr. rewrite Nat.eqb_refl. reflexivity. }
  intros m. apply (H _ m eq_refl).
Qed.

Lemma body_cont1 m : sem (EContinue 1) m (XContinue 1) m.
Proof. apply sem_cont. Qed.

Lemma body_inc n t m : zf2_nodes n = (EInc t, EContinue 2) -> t <= 10 ->
  sem (ENode n) m (XContinue 1) (inc t m).
Proof.
  intros Hn Ht. eapply sem_cdr_continueS with (k := 0); [exact Hn | apply sem_inc, Ht | apply sem_cont].
Qed.

Lemma body_inc2 n n' t1 t2 m : zf2_nodes n = (ENode n', EContinue 2) ->
  zf2_nodes n' = (EInc t1, EInc t2) -> t1 <= 10 -> t2 <= 10 ->
  sem (ENode n) m (XContinue 1) (inc t2 (inc t1 m)).
Proof.
  intros Hn Hn' H1 H2. eapply sem_cdr_continueS with (k := 0); [exact Hn | | apply sem_cont].
  eapply sem_cdr_normal; [exact Hn' | apply sem_inc, H1 | apply sem_inc, H2].
Qed.

(** Closed forms of the loops are checked field by field. *)
Ltac nrm := cbn [get set inc ustep unpair_post clr23] in *.
Ltac fields := intros; repeat match goal with m : St |- _ => destruct m end; nrm; subst;
  try (f_equal; first [reflexivity | lia]).

(* while_decnz(r, ()) : r := 0 *)
Lemma while0 n r : zf2_nodes n = (EDecnz r, EContinue 1) -> r <= 10 ->
  forall m, sem (ENode n) m XNormal (set m r 0).
Proof.
  intros Hn Hr. apply (sem_while n r (EContinue 1) (fun m => m) (fun m => set m r 0)); auto using body_cont1.
  - intros m H0. rewrite <- H0. destruct m. do 11 (destruct r as [|r]; [cbn in *; reflexivity|]); lia.
  - intros m v Hv. destruct m. do 11 (destruct r as [|r]; [cbn in *; reflexivity|]); lia.
Qed.

Ltac body_tac :=
  first [ apply body_cont1
        | apply body_inc; [reflexivity | lia]
        | eapply body_inc2; [reflexivity | reflexivity | lia | lia] ].

Ltac while_tac g P :=
  intros m; eapply (sem_while _ _ _ g P);
  [ reflexivity | lia | intros; body_tac | clear m; intros m; destruct m; reflexivity | fields | fields ].

(** The while_decnz loops of the program (generated by tools/gen_prog.py from ZF2Dag.v):
    while_decnz(r, body) with body = list of increments: r := 0, each target += r. *)
(* BEGIN GENERATED loops *)
(* while_decnz(axiomcode,()).0 *)
Lemma w224 m : sem (ENode 224) m XNormal (set m 4 0).
Proof. revert m; while_tac (fun m : St => m) (fun m : St => set m 4 0). Qed.
(* while_decnz(nextproof,94).0 *)
Lemma w225 m : sem (ENode 225) m XNormal (set (set (set m 8 (get m 8 + get m 1)) 0 (get m 0 + get m 1)) 1 0).
Proof. revert m; while_tac (fun m : St => inc 0 (inc 8 m)) (fun m : St => set (set (set m 8 (get m 8 + get m 1)) 0 (get m 0 + get m 1)) 1 0). Qed.
(* while_decnz(param1,18).0 *)
Lemma w228 m : sem (ENode 228) m XNormal (set (set (set m 2 (get m 2 + get m 5)) 8 (get m 8 + get m 5)) 5 0).
Proof. revert m; while_tac (fun m : St => inc 8 (inc 2 m)) (fun m : St => set (set (set m 2 (get m 2 + get m 5)) 8 (get m 8 + get m 5)) 5 0). Qed.
(* while_decnz(param1,3.scratch2.inc).0 *)
Lemma w229 m : sem (ENode 229) m XNormal (set (set m 9 (get m 9 + get m 5)) 5 0).
Proof. revert m; while_tac (inc 9) (fun m : St => set (set m 9 (get m 9 + get m 5)) 5 0). Qed.
(* while_decnz(param2,()).0 *)
Lemma w230 m : sem (ENode 230) m XNormal (set m 6 0).
Proof. revert m; while_tac (fun m : St => m) (fun m : St => set m 6 0). Qed.
(* while_decnz(param2,18).0 *)
Lemma w231 m : sem (ENode 231) m XNormal (set (set (set m 2 (get m 2 + get m 6)) 8 (get m 8 + get m 6)) 6 0).
Proof. revert m; while_tac (fun m : St => inc 8 (inc 2 m)) (fun m : St => set (set (set m 2 (get m 2 + get m 6)) 8 (get m 8 + get m 6)) 6 0). Qed.
(* while_decnz(param2,77).0 *)
Lemma w232 m : sem (ENode 232) m XNormal (set (set (set m 8 (get m 8 + get m 6)) 10 (get m 10 + get m 6)) 6 0).
Proof. revert m; while_tac (fun m : St => inc 10 (inc 8 m)) (fun m : St => set (set (set m 8 (get m 8 + get m 6)) 10 (get m 10 + get m 6)) 6 0). Qed.
(* while_decnz(param3,18).0 *)
Lemma w235 m : sem (ENode 235) m XNormal (set (set (set m 2 (get m 2 + get m 7)) 8 (get m 8 + get m 7)) 7 0).
Proof. revert m; while_tac (fun m : St => inc 8 (inc 2 m)) (fun m : St => set (set (set m 2 (get m 2 + get m 7)) 8 (get m 8 + get m 7)) 7 0). Qed.
(* while_decnz(param3,3.scratch2.inc).0 *)
Lemma w236 m : sem (ENode 236) m XNormal (set (set m 9 (get m 9 + get m 7)) 7 0).
Proof. revert m; while_tac (inc 9) (fun m : St => set (set m 9 (get m 9 + get m 7)) 7 0). Qed.
(* while_decnz(scratch1,()).0 *)
Lemma w237 m : sem (ENode 237) m XNormal (set m 8 0).
Proof. revert m; while_tac (fun m : St => m) (fun m : St => set m 8 0). Qed.
(* while_decnz(scratch1,3.axiomcode.inc).0 *)
Lemma w238 m : sem (ENode 238) m XNormal (set (set m 4 (get m 4 + get m 8)) 8 0).
Proof. revert m; while_tac (inc 4) (fun m : St => set (set m 4 (get m 4 + get m 8)) 8 0). Qed.
(* while_decnz(scratch1,3.nextproof.inc).0 *)
Lemma w240 m : sem (ENode 240) m XNormal (set (set m 1 (get m 1 + get m 8)) 8 0).
Proof. revert m; while_tac (inc 1) (fun m : St => set (set m 1 (get m 1 + get m 8)) 8 0). Qed.
(* while_decnz(scratch1,3.param1.inc).0 *)
Lemma w242 m : sem (ENode 242) m XNormal (set (set m 5 (get m 5 + get m 8)) 8 0).
Proof. revert m; while_tac (inc 5) (fun m : St => set (set m 5 (get m 5 + get m 8)) 8 0). Qed.
(* while_decnz(scratch1,3.param2.inc).0 *)
Lemma w244 m : sem (ENode 244) m XNormal (set (set m 6 (get m 6 + get m 8)) 8 0).
Proof. revert m; while_tac (inc 6) (fun m : St => set (set m 6 (get m 6 + get m 8)) 8 0). Qed.
(* while_decnz(scratch1,3.param3.inc).0 *)
Lemma w246 m : sem (ENode 246) m XNormal (set (set m 7 (get m 7 + get m 8)) 8 0).
Proof. revert m; while_tac (inc 7) (fun m : St => set (set m 7 (get m 7 + get m 8)) 8 0). Qed.
(* while_decnz(scratch1,3.scratch2.inc).0 *)
Lemma w248 m : sem (ENode 248) m XNormal (set (set m 9 (get m 9 + get m 8)) 8 0).
Proof. revert m; while_tac (inc 9) (fun m : St => set (set m 9 (get m 9 + get m 8)) 8 0). Qed.
(* while_decnz(scratch1,3.scratch3.inc).0 *)
Lemma w249 m : sem (ENode 249) m XNormal (set (set m 10 (get m 10 + get m 8)) 8 0).
Proof. revert m; while_tac (inc 10) (fun m : St => set (set m 10 (get m 10 + get m 8)) 8 0). Qed.
(* while_decnz(scratch1,3.topwff.inc).0 *)
Lemma w251 m : sem (ENode 251) m XNormal (set (set m 2 (get m 2 + get m 8)) 8 0).
Proof. revert m; while_tac (inc 2) (fun m : St => set (set m 2 (get m 2 + get m 8)) 8 0). Qed.
(* while_decnz(scratch1,42).0 *)
Lemma w252 m : sem (ENode 252) m XNormal (set (set (set m 2 (get m 2 + get m 8)) 9 (get m 9 + get m 8)) 8 0).
Proof. revert m; while_tac (fun m : St => inc 9 (inc 2 m)) (fun m : St => set (set (set m 2 (get m 2 + get m 8)) 9 (get m 9 + get m 8)) 8 0). Qed.
(* while_decnz(scratch2,()).0 *)
Lemma w255 m : sem (ENode 255) m XNormal (set m 9 0).
Proof. revert m; while_tac (fun m : St => m) (fun m : St => set m 9 0). Qed.
(* while_decnz(scratch2,3.prooflist.inc).0 *)
Lemma w256 m : sem (ENode 256) m XNormal (set (set m 0 (get m 0 + get m 9)) 9 0).
Proof. revert m; while_tac (inc 0) (fun m : St => set (set m 0 (get m 0 + get m 9)) 9 0). Qed.
(* while_decnz(scratch2,3.topwff.inc).0 *)
Lemma w258 m : sem (ENode 258) m XNormal (set (set m 2 (get m 2 + get m 9)) 9 0).
Proof. revert m; while_tac (inc 2) (fun m : St => set (set m 2 (get m 2 + get m 9)) 9 0). Qed.
(* while_decnz(scratch2,3.wffstack.inc).0 *)
Lemma w259 m : sem (ENode 259) m XNormal (set (set m 3 (get m 3 + get m 9)) 9 0).
Proof. revert m; while_tac (inc 3) (fun m : St => set (set m 3 (get m 3 + get m 9)) 9 0). Qed.
(* while_decnz(scratch3,()).0 *)
Lemma w261 m : sem (ENode 261) m XNormal (set m 10 0).
Proof. revert m; while_tac (fun m : St => m) (fun m : St => set m 10 0). Qed.
(* while_decnz(topwff,()).0 *)
Lemma w262 m : sem (ENode 262) m XNormal (set m 2 0).
Proof. revert m; while_tac (fun m : St => m) (fun m : St => set m 2 0). Qed.
(* while_decnz(topwff,3.scratch1.inc).0 *)
Lemma w263 m : sem (ENode 263) m XNormal (set (set m 8 (get m 8 + get m 2)) 2 0).
Proof. revert m; while_tac (inc 8) (fun m : St => set (set m 8 (get m 8 + get m 2)) 2 0). Qed.
(* while_decnz(topwff,3.scratch2.inc).0 *)
Lemma w265 m : sem (ENode 265) m XNormal (set (set m 9 (get m 9 + get m 2)) 2 0).
Proof. revert m; while_tac (inc 9) (fun m : St => set (set m 9 (get m 9 + get m 2)) 2 0). Qed.
(* while_decnz(wffstack,3.topwff.inc).0 *)
Lemma w266 m : sem (ENode 266) m XNormal (set (set m 2 (get m 2 + get m 3)) 3 0).
Proof. revert m; while_tac (inc 2) (fun m : St => set (set m 2 (get m 2 + get m 3)) 3 0). Qed.
(* END GENERATED loops *)

(** ** Cantor pairing facts. *)
Lemma tri_S n : tri (S n) = tri n + S n.
Proof.
  unfold tri. replace (S n * (S n + 1)) with (n * (n + 1) + S n * 2) by lia.
  rewrite Nat.div_add by lia. reflexivity.
Qed.

Lemma pair_00 : pair 0 0 = 0.
Proof. reflexivity. Qed.

Lemma pair_step a b k : a + b = S k -> pair a b = a + S (pair k 0).
Proof. intros H. unfold pair. rewrite H, tri_S, Nat.add_0_r. lia. Qed.

Lemma unpair_iter_diag a b c : Nat.iter a unpair_step (c, a + b) = (c + a, b).
Proof.
  revert b c. induction a as [|a IH]; intros b c.
  - cbn. f_equal; lia.
  - rewrite Nat.iter_succ. replace (S a + b) with (a + S b) by lia. rewrite IH. cbn. f_equal; lia.
Qed.

Lemma unpair_iter_tri d : Nat.iter (tri d) unpair_step (0, 0) = (0, d).
Proof.
  induction d as [|d IH]; [reflexivity|].
  rewrite tri_S, Nat.add_comm, Nat.iter_add, IH.
  rewrite Nat.iter_succ. replace (0, d) with (0, d + 0) by (f_equal; lia).
  rewrite unpair_iter_diag. cbn. f_equal; lia.
Qed.

Lemma unpair_pair a b : unpair (pair a b) = (a, b).
Proof.
  unfold unpair, pair. rewrite Nat.iter_add, unpair_iter_tri, unpair_iter_diag. reflexivity.
Qed.

(** ** pair(out, in1, in2): out += pair in1 in2; in1, in2 := 0.
    Loop: {while in1 {in1--; in2++; out++}; if in2 {in2--; out++; while in2 {in2--; in1++}; continue}}. *)
Ltac pair_tac W1 W2 :=
  let k := fresh "k" in let IH := fresh "IH" in let m := fresh "m" in let Hk := fresh "Hk" in
  induction k as [|k IH]; intros m Hk;
  [ eapply sem_cdr_normal; [reflexivity | apply W1 |];
    eapply sem_car_break1; [reflexivity|]; eapply sem_conseq; [apply sem_decnz_zero|];
    destruct m; nrm; [lia|];
    repeat match goal with H : ?a + ?b = 0 |- _ =>
      assert (a = 0) by lia; assert (b = 0) by lia; clear H; subst end; reflexivity
  | eapply sem_cdr_continue1; [reflexivity | apply W1 | |];
    [ eapply sem_cdr_continueS with (k := 0); [reflexivity | apply sem_decnz_pos with (v := k); [lia|] | ];
      [ destruct m; nrm; lia
      | eapply sem_cdr_continueS with (k := 1); [reflexivity | | apply sem_cont];
        eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia | apply W2] ]
    | eapply sem_conseq; [apply IH; destruct m; nrm; lia |];
      destruct m; nrm; f_equal; try lia;
      rewrite ?Nat.add_0_l; match goal with |- _ = _ + pair ?a ?b => rewrite (pair_step a b k) by lia end; lia ] ].

(* pair(scratch2, scratch1, topwff): the single pair instance *)
Lemma pair188 m :
  sem (ENode 188) m XNormal (set (set (set m 9 (get m 9 + pair (get m 8) (get m 2))) 8 0) 2 0).
Proof.
  revert m. cut (forall k m, get m 8 + get m 2 = k ->
    sem (ENode 188) m XNormal (set (set (set m 9 (get m 9 + pair (get m 8) (get m 2))) 8 0) 2 0)).
  { intros H m; apply (H _ m eq_refl). }
  pair_tac w252 w263.
Qed.

(* wff codes are astronomically large: never let tactic-level conversion compute a [pair] *)
Opaque pair.

(** ** unpair(out1, out2, in): walk [in] steps of [unpair_step] from (out1, out2); in := 0.
    Loop: {if in {in--; out1++; if out2 {out2--; continue} else {while out1 {out1--; out2++}; continue}}}. *)
Ltac ubody_tac W :=
  intros m; eapply sem_cdr_continueS with (k := 0); [reflexivity | apply sem_inc; lia |];
  destruct (get m 9) as [|v] eqn:Hv;
  [ eapply sem_conseq;
    [ eapply sem_cdr_continueS with (k := 1);
      [ reflexivity
      | eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; destruct m; nrm; exact Hv]
      | eapply sem_cdr_continueS with (k := 2); [reflexivity | apply W | apply sem_cont] ]
    | destruct m; nrm; subst; cbn [unpair_step fst snd]; f_equal; lia ]
  | eapply sem_conseq;
    [ eapply sem_car_continue with (k := 1);
      [ reflexivity
      | eapply sem_cdr_continueS with (k := 1);
        [ reflexivity | apply sem_decnz_pos with (v := v); [lia | destruct m; nrm; exact Hv]
        | apply sem_cont ] ]
    | destruct m; nrm; subst; reflexivity ] ].

Lemma ubody206 m : sem (ENode 206) m (XContinue 1) (ustep 8 9 m).
Proof. revert m; ubody_tac w248. Qed.

Ltac unpair_tac B :=
  intros m; eapply (sem_while _ _ _ _ (unpair_post _ _ _));
  [ reflexivity | lia | apply B | clear m; intros m; destruct m; reflexivity
  | clear m; intros m H0; destruct m; unfold unpair_post; nrm; subst; reflexivity
  | clear m; intros m v Hv; destruct m; unfold unpair_post; nrm; subst;
    rewrite Nat.iter_succ_r, <- surjective_pairing; reflexivity ].

(* unpair(scratch1, scratch2, prooflist) *)
Lemma unpair210 m : sem (ENode 210) m XNormal (unpair_post 0 8 9 m).
Proof. revert m; unpair_tac ubody206. Qed.
(* unpair(scratch1, scratch2, wffstack) *)
Lemma unpair211 m : sem (ENode 211) m XNormal (unpair_post 3 8 9 m).
Proof. revert m; unpair_tac ubody206. Qed.

(** ** Straight-line sequences: a node all of whose cons cells below it (down to "atoms") are run
    car-then-cdr is the sequential composition of its flattening. *)
Inductive seqx : list edge -> St -> exit -> St -> Prop :=
  | sx_nil m : seqx [] m XNormal m
  | sx_normal e l m m1 x m2 : sem e m XNormal m1 -> seqx l m1 x m2 -> seqx (e :: l) m x m2
  | sx_halt e l m m1 : sem e m XHalt m1 -> seqx (e :: l) m XHalt m1.

Lemma sx_nil_eq m m' : m = m' -> seqx [] m XNormal m'.
Proof. intros <-; constructor. Qed.

Lemma seqx_exit l m x m' : seqx l m x m' -> x = XNormal \/ x = XHalt.
Proof. induction 1; auto. Qed.

Lemma seqx_app_inv l1 l2 m x m' : seqx (l1 ++ l2) m x m' ->
  (exists m1, seqx l1 m XNormal m1 /\ seqx l2 m1 x m') \/ (x = XHalt /\ seqx l1 m XHalt m').
Proof.
  revert m. induction l1 as [|e l1 IH]; intros m H; cbn in H.
  - left. exists m. split; [constructor | exact H].
  - inversion H as [|e' l' m0 m1 x' m2 Hs Hl|e' l' m0 m1 Hs]; subst.
    + destruct (IH _ Hl) as [(m3 & Ha & Hb) | (-> & Ha)].
      * left. exists m3. split; [econstructor; eauto | exact Hb].
      * right. split; [reflexivity | econstructor; eauto].
    + right. split; [reflexivity | apply sx_halt; assumption].
Qed.

Lemma seqx_app l1 l2 m m1 x m' : seqx l1 m XNormal m1 -> seqx l2 m1 x m' -> seqx (l1 ++ l2) m x m'.
Proof.
  revert m. induction l1 as [|e l1 IH]; intros m H1 H2; inversion H1; subst; cbn; auto.
  econstructor; eauto.
Qed.

Lemma seqx_single e m x m' : seqx [e] m x m' -> sem e m x m'.
Proof.
  intros H. inversion H as [|e' l' m0 m1 x' m2 Hs Hl|e' l' m0 m1 Hs]; subst; auto.
  inversion Hl; subst; auto.
Qed.

(* nodes with their own lemma: never flattened *)
(* BEGIN GENERATED atoms *)
Definition atoms : list nat := [9; 11; 19; 20; 21; 122; 124; 188; 192; 193; 195; 197; 200; 210; 211; 212; 213; 214; 215; 216; 217; 218; 219; 224; 225; 228; 229; 230; 231; 232; 235; 236; 237; 238; 240; 242; 244; 246; 248; 249; 251; 252; 255; 256; 258; 259; 261; 262; 263; 265; 266; 267; 268].
(* END GENERATED atoms *)

Definition is_atom (n : nat) : bool := existsb (Nat.eqb n) atoms.

Fixpoint expand (fuel : nat) (e : edge) : list edge :=
  match fuel with
  | 0 => [e]
  | S f =>
    match e with
    | ENode n => if is_atom n then [e] else expand f (fst (zf2_nodes n)) ++ expand f (snd (zf2_nodes n))
    | _ => [e]
    end
  end.

Lemma sem_node_seq n m x m' : seqx (expand 200 (fst (zf2_nodes n)) ++ expand 200 (snd (zf2_nodes n))) m x m' ->
  (forall m x m', seqx (expand 200 (fst (zf2_nodes n))) m x m' -> sem (fst (zf2_nodes n)) m x m') ->
  (forall m x m', seqx (expand 200 (snd (zf2_nodes n))) m x m' -> sem (snd (zf2_nodes n)) m x m') ->
  sem (ENode n) m x m'.
Proof.
  intros H Ha Hb. pose proof (surjective_pairing (zf2_nodes n)) as Hn.
  destruct (seqx_app_inv _ _ _ _ _ H) as [(m1 & H1 & H2) | (-> & H1)].
  - destruct (seqx_exit _ _ _ _ H2) as [-> | ->].
    + eapply sem_cdr_normal; [exact Hn | apply Ha, H1 | apply Hb, H2].
    + eapply sem_cdr_halt; [exact Hn | apply Ha, H1 | apply Hb, H2].
  - eapply sem_car_halt; [exact Hn | apply Ha, H1].
Qed.

Lemma expand_sound fuel e m x m' : seqx (expand fuel e) m x m' -> sem e m x m'.
Proof.
  revert e m x m'. induction fuel as [|f IH]; intros e m x m' H; cbn [expand] in H.
  - apply seqx_single, H.
  - destruct e; try (apply seqx_single, H).
    destruct (is_atom n); [apply seqx_single, H|].
    destruct (seqx_app_inv _ _ _ _ _ H) as [(m1 & H1 & H2) | (-> & H1)];
      pose proof (surjective_pairing (zf2_nodes n)) as Hn.
    + destruct (seqx_exit _ _ _ _ H2) as [-> | ->].
      * eapply sem_cdr_normal; [exact Hn | apply IH, H1 | apply IH, H2].
      * eapply sem_cdr_halt; [exact Hn | apply IH, H1 | apply IH, H2].
    + eapply sem_car_halt; [exact Hn | apply IH, H1].
Qed.

Lemma seq_node n m x m' :
  seqx (expand 200 (fst (zf2_nodes n)) ++ expand 200 (snd (zf2_nodes n))) m x m' -> sem (ENode n) m x m'.
Proof.
  intros H. apply (sem_node_seq n m x m' H);
    intros m0 x0 m0' H0; exact (expand_sound 200 _ m0 x0 m0' H0).
Qed.

(** Tactics for symbolic execution of sequences. *)
(* [elem] proves [sem e m XNormal ?m'] for an atom [e] by its lemma; it is extended (::=) as lemmas
   are added. *)
(* BEGIN GENERATED elem_w *)
Ltac elem_w := match goal with
  | |- sem (ENode 224) _ _ _ => apply w224
  | |- sem (ENode 225) _ _ _ => apply w225
  | |- sem (ENode 228) _ _ _ => apply w228
  | |- sem (ENode 229) _ _ _ => apply w229
  | |- sem (ENode 230) _ _ _ => apply w230
  | |- sem (ENode 231) _ _ _ => apply w231
  | |- sem (ENode 232) _ _ _ => apply w232
  | |- sem (ENode 235) _ _ _ => apply w235
  | |- sem (ENode 236) _ _ _ => apply w236
  | |- sem (ENode 237) _ _ _ => apply w237
  | |- sem (ENode 238) _ _ _ => apply w238
  | |- sem (ENode 240) _ _ _ => apply w240
  | |- sem (ENode 242) _ _ _ => apply w242
  | |- sem (ENode 244) _ _ _ => apply w244
  | |- sem (ENode 246) _ _ _ => apply w246
  | |- sem (ENode 248) _ _ _ => apply w248
  | |- sem (ENode 249) _ _ _ => apply w249
  | |- sem (ENode 251) _ _ _ => apply w251
  | |- sem (ENode 252) _ _ _ => apply w252
  | |- sem (ENode 255) _ _ _ => apply w255
  | |- sem (ENode 256) _ _ _ => apply w256
  | |- sem (ENode 258) _ _ _ => apply w258
  | |- sem (ENode 259) _ _ _ => apply w259
  | |- sem (ENode 261) _ _ _ => apply w261
  | |- sem (ENode 262) _ _ _ => apply w262
  | |- sem (ENode 263) _ _ _ => apply w263
  | |- sem (ENode 265) _ _ _ => apply w265
  | |- sem (ENode 266) _ _ _ => apply w266
  end.
(* END GENERATED elem_w *)
Ltac side := first [cbn [get]; reflexivity | lia].
Ltac elem0 :=
  match goal with
  | |- sem (EInc _) _ _ _ => apply sem_inc; lia
  | |- sem (ENode 188) _ _ _ => apply pair188
  | |- sem (ENode 210) _ _ _ => apply unpair210
  | |- sem (ENode 211) _ _ _ => apply unpair211
  | |- _ => elem_w
  end.
Ltac elem := elem0.

Ltac expand_goal :=
  match goal with |- seqx ?l0 _ _ _ =>
    let l := eval vm_compute in l0 in
    let E := fresh "E" in assert (E : l0 = l) by (vm_compute; reflexivity);
    rewrite E; clear E
  end.

Ltac step := eapply sx_normal; [ elem | nrm ].
Ltac run_seq := apply seq_node; expand_goal; repeat step.

Lemma unpair_iter_pair a b : Nat.iter (pair a b) unpair_step (0, 0) = (a, b).
Proof. exact (unpair_pair a b). Qed.

(* close a sequence: compare the final state field by field *)
Ltac fin := apply sx_nil_eq; rewrite ?unpair_iter_pair; cbn [fst snd];
  try reflexivity; f_equal; first [reflexivity | lia].

Ltac start := intros m; destruct m; intros; nrm; subst.


(** ** The stack subroutines (clean registers: scratch1 = scratch2 = scratch3 = 0). *)
(* pushwff() = [s1 := tw; tw := ws; s2 := pair s1 tw; ws := s2]: wffstack := pair topwff wffstack; topwff := 0 *)
Lemma pushwff197 m : get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 197) m XNormal (set (set m 3 (pair (get m 2) (get m 3))) 2 0).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem1 := match goal with |- sem (ENode 197) _ _ _ => eapply pushwff197; side end.
Ltac elem ::= first [elem1 | elem0].

(* v_i(): push; topwff := i *)
Lemma v212 m : get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 212) m XNormal (set (set m 3 (pair (get m 2) (get m 3))) 2 1).
Proof. revert m; start; run_seq; fin. Qed.
Lemma v213 m : get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 213) m XNormal (set (set m 3 (pair (get m 2) (get m 3))) 2 2).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem2 := match goal with
  | |- sem (ENode 212) _ _ _ => eapply v212; side
  | |- sem (ENode 213) _ _ _ => eapply v213; side
  end.
Ltac elem ::= first [elem2 | elem1 | elem0].
Lemma v214 m : get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 214) m XNormal (set (set m 3 (pair (get m 2) (get m 3))) 2 3).
Proof. revert m; start; run_seq; fin. Qed.

(* par_i(): push; topwff := param_i *)
Lemma par192 m : get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 192) m XNormal (set (set m 3 (pair (get m 2) (get m 3))) 2 (get m 5)).
Proof. revert m; start; run_seq; fin. Qed.
Lemma par193 m : get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 193) m XNormal (set (set m 3 (pair (get m 2) (get m 3))) 2 (get m 6)).
Proof. revert m; start; run_seq; fin. Qed.
Lemma par195 m : get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 195) m XNormal (set (set m 3 (pair (get m 2) (get m 3))) 2 (get m 7)).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem3 := match goal with
  | |- sem (ENode 214) _ _ _ => eapply v214; side
  | |- sem (ENode 192) _ _ _ => eapply par192; side
  | |- sem (ENode 193) _ _ _ => eapply par193; side
  | |- sem (ENode 195) _ _ _ => eapply par195; side
  end.
Ltac elem ::= first [elem3 | elem2 | elem1 | elem0].

(* wff constructors: cons = [(s1, s2) := unpair ws; ws := s2; tw := pair s1 tw], then
   tag_k = [s1 := tw; tw := k; tw := pair s1 tw] *)
Lemma weq218 m x r : get m 3 = pair x r -> get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 218) m XNormal (set (set m 2 (weq x (get m 2))) 3 r).
Proof. revert m; start; run_seq; fin. Qed.
Lemma wel217 m x r : get m 3 = pair x r -> get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 217) m XNormal (set (set m 2 (wel x (get m 2))) 3 r).
Proof. revert m; start; run_seq; fin. Qed.
Lemma wim267 m x r : get m 3 = pair x r -> get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 267) m XNormal (set (set m 2 (wim x (get m 2))) 3 r).
Proof. revert m; start; run_seq; fin. Qed.
Lemma wal216 m x r : get m 3 = pair x r -> get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 216) m XNormal (set (set m 2 (wal x (get m 2))) 3 r).
Proof. revert m; start; run_seq; fin. Qed.
Lemma wn268 m : get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 268) m XNormal (set m 2 (wn (get m 2))).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem4 := match goal with
  | |- sem (ENode 218) _ _ _ => eapply weq218; side
  | |- sem (ENode 217) _ _ _ => eapply wel217; side
  | |- sem (ENode 267) _ _ _ => eapply wim267; side
  | |- sem (ENode 216) _ _ _ => eapply wal216; side
  | |- sem (ENode 268) _ _ _ => eapply wn268; side
  end.
Ltac elem ::= first [elem4 | elem3 | elem2 | elem1 | elem0].
Lemma wex219 m x r : get m 3 = pair x r -> get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 219) m XNormal (set (set m 2 (wex x (get m 2))) 3 r).
Proof. revert m; start; run_seq; fin. Qed.
Lemma wa215 m x r : get m 3 = pair x r -> get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 215) m XNormal (set (set m 2 (wa x (get m 2))) 3 r).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem5 := match goal with
  | |- sem (ENode 219) _ _ _ => eapply wex219; side
  | |- sem (ENode 215) _ _ _ => eapply wa215; side
  end.
Ltac elem ::= first [elem5 | elem4 | elem3 | elem2 | elem1 | elem0].

Ltac dec_pos := eapply sem_decnz_pos; [lia | reflexivity].

(** ** select(): if axiomcode {axiomcode--; drop pop} else {topwff := pop}. *)
Lemma select200 m t r : get m 3 = pair t r -> get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 200) m XNormal
    (set (set (set m 2 (match get m 4 with 0 => t | S _ => get m 2 end)) 3 r) 4 (pred (get m 4))).
Proof.
  revert m; start. destruct r_ac0 as [|a].
  - eapply sem_cdr_normal; [reflexivity | eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; reflexivity] |].
    run_seq; fin.
  - eapply sem_car_break1; [reflexivity|].
    eapply sem_cdr_break with (k := 0); [reflexivity | dec_pos |].
    eapply sem_cdr_break with (k := 0); [reflexivity | | apply sem_breakS].
    run_seq; fin.
Qed.
Ltac elem6 := match goal with |- sem (ENode 200) _ _ _ => eapply select200; side end.
Ltac elem ::= first [elem6 | elem5 | elem4 | elem3 | elem2 | elem1 | elem0].

(** ** cparam(p): if axiomcode = 1 then p := pop wffstack (axiomcode restored). *)
(* [unpair(scratch1, scratch2, wffstack); wffstack := scratch2] *)
Lemma n187 m : get m 8 = 0 -> get m 9 = 0 ->
  sem (ENode 187) m XNormal (set (set m 8 (fst (unpair (get m 3)))) 3 (snd (unpair (get m 3)))).
Proof. revert m; start; run_seq; fin. Qed.

Ltac cparam_tac tail :=
  intros m; destruct m; intros; nrm; subst;
  match goal with |- context [ match ?ac with 0 => _ | _ => _ end ] => destruct ac as [|[|?]] end;
  [ (* axiomcode = 0 *)
    eapply sem_car_break1; [reflexivity|];
    eapply sem_cdr_break with (k := 0); [reflexivity | | apply sem_breakS];
    eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; reflexivity]
  | (* axiomcode = 1 *)
    eapply sem_conseq;
    [ eapply sem_cdr_normal; [reflexivity | | tail];
      eapply sem_car_break1; [reflexivity|];
      eapply sem_cdr_break with (k := 0); [reflexivity | dec_pos |];
      eapply sem_cdr_break with (k := 0); [reflexivity | |];
      [ eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; reflexivity]
      | eapply sem_cdr_break with (k := 0); [reflexivity | | apply sem_breakS];
        eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia | apply n187; reflexivity] ]
    | nrm; f_equal; lia ]
  | (* axiomcode >= 2 *)
    eapply sem_conseq;
    [ eapply sem_car_break1; [reflexivity|];
      eapply sem_cdr_break with (k := 0); [reflexivity | | apply sem_breakS];
      eapply sem_cdr_normal; [reflexivity | dec_pos |];
      eapply sem_car_break1; [reflexivity|];
      eapply sem_cdr_break with (k := 0); [reflexivity | dec_pos |];
      eapply sem_cdr_break with (k := 0); [reflexivity | | apply sem_breakS];
      eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia | apply sem_inc; lia]
    | reflexivity ] ].

(* cparam(param2) *)
Lemma cparam9 m : get m 8 = 0 -> get m 9 = 0 -> sem (ENode 9) m XNormal
  (match get m 4 with 1 => set (set m 6 (fst (unpair (get m 3)))) 3 (snd (unpair (get m 3))) | _ => m end).
Proof. revert m; cparam_tac ltac:(eapply sem_cdr_normal; [reflexivity | apply w230 | apply w244]). Qed.

(* cparam(scratch3): no zeroing loop, scratch3 is 0 *)
Lemma cparam11 m : get m 8 = 0 -> get m 9 = 0 -> get m 10 = 0 -> sem (ENode 11) m XNormal
  (match get m 4 with 1 => set (set m 10 (fst (unpair (get m 3)))) 3 (snd (unpair (get m 3))) | _ => m end).
Proof. revert m; cparam_tac ltac:(apply w249). Qed.

Ltac elem7 := match goal with
  | |- sem (ENode 9) _ _ _ => eapply cparam9; side
  | |- sem (ENode 11) _ _ _ => eapply cparam11; side
  end.
Ltac elem ::= first [elem7 | elem6 | elem5 | elem4 | elem3 | elem2 | elem1 | elem0].

(** ** if_eq(scratch2, scratch3, body): runs body iff scratch2 = scratch3; both zeroed.
    Loop: {if s2 {s2--; if s3 {s3--; continue} else {s2 := 0; s3 := 1}}}; then
    {if s3 {s3 := 0; skip body}}. *)
Lemma loop13 x : forall m, get m 9 = x ->
  (x <= get m 10 -> sem (ENode 13) m XNormal (set (set m 9 0) 10 (get m 10 - x))) /\
  (get m 10 < x -> sem (ENode 13) m XNormal (set (set m 9 0) 10 1)).
Proof.
  induction x as [|x IH]; intros m Hx; split; intros Hle.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; exact Hx]|].
    destruct m; nrm; subst; f_equal; lia.
  - lia.
  - destruct (get m 10) as [|y] eqn:Hy; [lia|].
    eapply sem_cdr_continue1; [reflexivity | apply sem_decnz_pos; [lia | exact Hx] | |].
    + eapply sem_car_continue with (k := 0); [reflexivity|].
      eapply sem_cdr_continueS with (k := 0); [reflexivity | | apply sem_cont].
      apply sem_decnz_pos with (v := y); [lia | destruct m; nrm; exact Hy].
    + eapply sem_conseq; [apply (proj1 (IH (set (set m 9 x) 10 y) ltac:(destruct m; reflexivity))); destruct m; nrm; lia|].
      destruct m; nrm; subst; f_equal; lia.
  - destruct (get m 10) as [|y] eqn:Hy.
    + eapply sem_conseq.
      * eapply sem_cdr_normal; [reflexivity | apply sem_decnz_pos; [lia | exact Hx] |].
        eapply sem_cdr_normal; [reflexivity | |].
        -- eapply sem_car_break1; [reflexivity|]. apply sem_decnz_zero. destruct m; nrm; exact Hy.
        -- eapply sem_cdr_normal; [reflexivity | apply w255 | apply sem_inc; lia].
      * destruct m; nrm; subst; reflexivity.
    + eapply sem_cdr_continue1; [reflexivity | apply sem_decnz_pos; [lia | exact Hx] | |].
      * eapply sem_car_continue with (k := 0); [reflexivity|].
        eapply sem_cdr_continueS with (k := 0); [reflexivity | | apply sem_cont].
        apply sem_decnz_pos with (v := y); [lia | destruct m; nrm; exact Hy].
      * eapply sem_conseq; [apply (proj2 (IH (set (set m 9 x) 10 y) ltac:(destruct m; reflexivity))); destruct m; nrm; lia|].
        destruct m; nrm; subst; reflexivity.
Qed.

Lemma if12_eq m : get m 9 = get m 10 -> sem (ENode 12) m XNormal (clr23 m).
Proof.
  intros H. destruct (loop13 (get m 9) m eq_refl) as [H1 _].
  eapply sem_cdr_normal; [reflexivity | apply H1; lia |].
  eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero]|].
  - destruct m; nrm; lia.
  - unfold clr23; destruct m; nrm; f_equal; lia.
Qed.

Lemma if12_neq m : get m 9 <> get m 10 -> sem (ENode 12) m (XBreak 1) (clr23 m).
Proof.
  intros H. destruct (loop13 (get m 9) m eq_refl) as [H1 H2].
  assert (Hl : exists d, sem (ENode 13) m XNormal (set (set m 9 0) 10 (S d))).
  { destruct (Nat.lt_ge_cases (get m 10) (get m 9)) as [Hlt | Hge].
    - exists 0. apply H2, Hlt.
    - exists (get m 10 - get m 9 - 1).
      replace (S (get m 10 - get m 9 - 1)) with (get m 10 - get m 9) by lia.
      apply H1, Hge. }
  destruct Hl as [d Hd].
  eapply sem_cdr_break with (k := 0); [reflexivity | exact Hd |].
  eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos with (v := d);
    [lia | destruct m; reflexivity] |].
  eapply sem_conseq; [eapply sem_cdr_break with (k := 0); [reflexivity | apply w261 | apply sem_breakS]|].
  unfold clr23; destruct m; nrm; reflexivity.
Qed.

(* if_eq(scratch2, scratch3, topwff := 0) *)
Lemma ifeq19 m : sem (ENode 19) m XNormal
  (set (clr23 m) 2 (if Nat.eqb (get m 9) (get m 10) then 0 else get m 2)).
Proof.
  destruct (Nat.eqb_spec (get m 9) (get m 10)) as [H | H].
  - eapply sem_cdr_normal; [reflexivity | apply if12_eq, H |].
    eapply sem_conseq; [apply w262|]. unfold clr23; destruct m; reflexivity.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply if12_neq, H]|].
    unfold clr23; destruct m; reflexivity.
Qed.

(* if_eq(scratch2, scratch3, topwff += param1) *)
Lemma ifeq20 m : get m 8 = 0 -> sem (ENode 20) m XNormal
  (set (clr23 m) 2 (if Nat.eqb (get m 9) (get m 10) then get m 2 + get m 5 else get m 2)).
Proof.
  intros H8. destruct (Nat.eqb_spec (get m 9) (get m 10)) as [H | H].
  - eapply sem_cdr_normal; [reflexivity | apply if12_eq, H |].
    eapply sem_conseq; [eapply sem_cdr_normal; [reflexivity | apply w228 | apply w242]|].
    unfold clr23; destruct m; nrm; subst; f_equal; lia.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply if12_neq, H]|].
    unfold clr23; destruct m; reflexivity.
Qed.

(** ** if_not_decnz(prooflist, {prooflist := nextproof; nextproof++}) *)
Lemma ifnot21 m : get m 8 = 0 -> sem (ENode 21) m XNormal
  (set (set m 0 (match get m 0 with 0 => get m 1 | S v => v end))
       1 (match get m 0 with 0 => S (get m 1) | S _ => get m 1 end)).
Proof.
  intros H8. destruct (get m 0) as [|v] eqn:H0.
  - eapply sem_cdr_normal; [reflexivity | eapply sem_car_break1; [reflexivity | apply sem_decnz_zero, H0] |].
    eapply sem_conseq; [eapply sem_cdr_normal; [reflexivity | apply w225 |
      eapply sem_cdr_normal; [reflexivity | apply w240 | apply sem_inc; lia]]|].
    destruct m; nrm; subst; f_equal; lia.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity|] |].
    + eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos; [lia | exact H0] | apply sem_breakS].
    + destruct m; nrm; subst; reflexivity.
Qed.

Ltac elem8 := match goal with
  | |- sem (ENode 19) _ _ _ => apply ifeq19
  | |- sem (ENode 20) _ _ _ => eapply ifeq20; side
  | |- sem (ENode 21) _ _ _ => eapply ifnot21; side
  end.
Ltac elem ::= first [elem8 | elem7 | elem6 | elem5 | elem4 | elem3 | elem2 | elem1 | elem0].

(** ** the final check: halt iff topwff = 1 (topwff is restored otherwise) *)
Lemma check122_halt m : get m 2 = 1 -> exists m', sem (ENode 122) m XHalt m'.
Proof.
  intros H. eexists.
  eapply sem_cdr_halt; [reflexivity | apply sem_decnz_pos; [lia | exact H] |].
  eapply sem_cdr_halt; [reflexivity | | apply sem_halt].
  eapply sem_car_break1; [reflexivity | apply sem_decnz_zero]. destruct m; nrm; reflexivity.
Qed.

Lemma check122_normal m : get m 2 <> 1 -> sem (ENode 122) m XNormal m.
Proof.
  intros H. destruct (get m 2) as [|[|v]] eqn:H2; [| congruence |].
  - eapply sem_car_break1; [reflexivity | apply sem_decnz_zero, H2].
  - eapply sem_cdr_normal; [reflexivity | apply sem_decnz_pos; [lia | exact H2] |].
    eapply sem_car_break1; [reflexivity|].
    eapply sem_cdr_break with (k := 0); [reflexivity |
      apply sem_decnz_pos with (v := v); [lia | destruct m; nrm; reflexivity] |].
    eapply sem_conseq; [eapply sem_cdr_break with (k := 0); [reflexivity | | apply sem_breakS]|].
    + eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia | apply sem_inc; lia].
    + destruct m; nrm; subst; reflexivity.
Qed.

(** ** The main() body: prefix, the 15 clauses in [axiomorder], the halt check. *)
(* BEGIN GENERATED notations *)
Local Notation E_cparam2 := (ENode 9) (only parsing).
Local Notation E_cparam_s3 := (ENode 11) (only parsing).
Local Notation E_par1 := (ENode 192) (only parsing).
Local Notation E_par2 := (ENode 193) (only parsing).
Local Notation E_par3 := (ENode 195) (only parsing).
Local Notation E_select := (ENode 200) (only parsing).
Local Notation E_v0 := (ENode 197) (only parsing).
Local Notation E_v1 := (ENode 212) (only parsing).
Local Notation E_v2 := (ENode 213) (only parsing).
Local Notation E_v3 := (ENode 214) (only parsing).
Local Notation E_wa := (ENode 215) (only parsing).
Local Notation E_wal := (ENode 216) (only parsing).
Local Notation E_wel := (ENode 217) (only parsing).
Local Notation E_weq := (ENode 218) (only parsing).
Local Notation E_wex := (ENode 219) (only parsing).
Local Notation E_wim := (ENode 267) (only parsing).
Local Notation E_wn := (ENode 268) (only parsing).
(* END GENERATED notations *)

(* clause programs by clause index (generated by tools/gen_prog.py; the flattening equation
   [main_flat] below checks them against the DAG) *)
(* BEGIN GENERATED clauses *)
Definition CL (c : nat) : list edge :=
  match c with
  | 0 => (* DET *) [E_cparam2; E_cparam_s3; E_par2; E_par1; E_wim; ENode 265; ENode 20; E_select]
  | 1 => (* GEN *) [E_cparam2; E_par3; E_par2; E_wal; E_select]
  | 2 => (* B1 *) [E_par3; E_par2; E_wim; E_par2; E_par1; E_wim; E_par3; E_par1; E_wim; E_wim; E_wim; E_select]
  | 3 => (* B4 *) [E_par3; E_par2; E_par1; E_wim; E_wal; E_par3; E_par2; E_wal; E_par3; E_par1; E_wal; E_wim; E_wim; E_select]
  | 4 => (* B6b *) [E_par3; E_par1; E_par2; E_wal; E_wal; E_par1; E_par3; E_par2; E_wal; E_wal; E_wim; E_select]
  | 5 => (* B8b *) [E_par3; E_par2; E_weq; E_par3; E_par1; E_wel; E_par2; E_par1; E_wel; E_wim; E_wim; E_select]
  | 6 => (* B6a *) [E_par3; E_par1; E_weq; E_par2; E_par3; E_par1; E_weq; E_wal; E_wim; E_par3; E_par1; E_wel; E_par2; E_par3; E_par1; E_wel; E_wal; E_wim; E_wa; ENode 232; ENode 236; ENode 19; ENode 249; ENode 229; ENode 19; E_select]
  | 7 => (* B6c *) [E_par3; E_par3; E_par1; E_wal; E_wex; E_par1; E_wim; E_select]
  | 8 => (* B7 *) [E_par3; E_par3; E_par1; E_weq; E_wex; E_select]
  | 9 => (* B8a *) [E_par3; E_par2; E_weq; E_par3; E_par1; E_weq; E_par2; E_par1; E_weq; E_wim; E_wim; E_select]
  | 10 => (* B8c *) [E_par3; E_par1; E_weq; E_par2; E_par3; E_wel; E_par2; E_par1; E_wel; E_wim; E_wim; E_select]
  | 11 => (* EXT *) [E_v0; E_v0; E_v2; E_wel; E_v0; E_v1; E_wel; E_wim; E_v0; E_v1; E_wel; E_v0; E_v2; E_wel; E_wim; E_wa; E_wal; E_v1; E_v2; E_weq; E_wim; E_select]
  | 12 => (* REPsb0 *) [E_v3; E_v1; E_v2; E_v1; E_par2; E_wal; E_v0; E_v0; E_v2; E_wel; E_v0; E_v1; E_wel; E_wim; E_wal; E_wn; E_v2; E_v1; E_wel; E_wim; E_wim; E_wal; E_wex; E_wal; E_v1; E_v2; E_v3; E_v1; E_par2; E_wal; E_v3; E_v0; E_wel; E_wa; E_wex; E_v2; E_v1; E_wel; E_wim; E_v2; E_v1; E_wel; E_v3; E_v1; E_par2; E_wal; E_v3; E_v0; E_wel; E_wa; E_wex; E_wim; E_wa; E_wal; E_wex; E_wim; E_select]
  | 13 => (* INF *) [E_v2; E_v0; E_v0; E_v2; E_wel; E_v1; E_v2; E_v0; E_v2; E_weq; E_v2; E_v1; E_wel; E_wim; E_v2; E_v1; E_wel; E_v0; E_v2; E_weq; E_wim; E_wa; E_wal; E_v1; E_v2; E_wel; E_wa; E_wex; E_wim; E_wal; E_v0; E_v2; E_wel; E_wa; E_wex; E_select]
  | _ => (* Y_CpCCNqCCqrNpq *) [E_par3; E_par2; E_wn; E_par2; E_par1; E_wim; E_par3; E_wn; E_wim; E_wim; E_par2; E_wim; E_wim; E_select]
  end.
Definition prefix : list edge := [ENode 21; ENode 224; ENode 210; ENode 256; ENode 238; ENode 210; ENode 256; ENode 242; ENode 210; ENode 256; ENode 244; ENode 210; ENode 256; ENode 246].
Definition check_node : nat := 122.
(* END GENERATED clauses *)

Definition main_list : list edge := prefix ++ [E_v0] ++ flat_map CL axiomorder ++ [ENode check_node].

Lemma main_flat : expand 200 (fst (zf2_nodes 0)) ++ expand 200 (snd (zf2_nodes 0)) = main_list.
Proof. vm_compute. reflexivity. Qed.

(** Effect of one clause program (ending in select) on a clean register file.  axiomcode = 0: no
    effect (the clause works on a pushed copy and select pops it back), except that B6a's
    destructive distinctness test zeroes param1..3.  axiomcode = 1: the active clause (DET pops its
    minor premise into param2 and its major premise into scratch3; GEN pops its premise into
    param2).  axiomcode >= 2: topwff := the clause's wff, axiomcode--. *)
Definition clause_post (c : nat) (m : St) : St :=
  let p1 := get m 5 in let p2 := get m 6 in let p3 := get m 7 in let w := get m 3 in
  match get m 4 with
  | 0 => match c with 6 => set (set (set m 5 0) 6 0) 7 0 | _ => m end
  | S a =>
    match c, a with
    | 0, 0 =>
      let ph := fst (unpair w) in let w1 := snd (unpair w) in
      let maj := fst (unpair w1) in let w2 := snd (unpair w1) in
      set (set (set (set m 2 (if Nat.eqb (wim ph p1) maj then p1 else 0)) 3 w2) 4 0) 6 ph
    | 0, _ => set (set m 2 (if Nat.eqb (wim p2 p1) 0 then p1 else 0)) 4 a
    | 1, 0 => set (set (set (set m 2 (wal p3 (fst (unpair w)))) 3 (snd (unpair w))) 4 0) 6 (fst (unpair w))
    | 1, _ => set (set m 2 (wal p3 p2)) 4 a
    | 6, _ => set (set (set (set (set m 2 (if Nat.eqb p1 p2 then 0 else if Nat.eqb p3 p2 then 0
                                          else clause_6 p1 p2 p3)) 4 a) 5 0) 6 0) 7 0
    | _, _ => set (set m 2 (clause c p1 p2 p3)) 4 a
    end
  end.

Ltac clause_fin :=
  apply sx_nil_eq; cbn [clause clause_post get set Nat.pred];
  unfold clause_0, clause_1, clause_2, clause_3, clause_4, clause_5, clause_6, clause_7, clause_8,
    clause_9, clause_10, clause_11, clause_12, clause_13, clause_14,
    c0, c1, c2, c3, c4;
  rewrite ?Nat.add_0_l;
  repeat match goal with |- context [Nat.eqb ?x ?y] =>
    lazymatch x with context [Nat.eqb _ _] => fail | _ =>
    destruct (Nat.eqb x y) eqn:? end end;
  try reflexivity.

Lemma clause_ok c m : c < 15 -> get m 8 = 0 -> get m 9 = 0 -> get m 10 = 0 ->
  seqx (CL c) m XNormal (clause_post c m).
Proof.
  intros Hc. destruct m as [a0 a1 a2 a3 [|[|ac]] a5 a6 a7 a8 a9 a10]; intros; nrm; subst;
  do 15 (destruct c as [|c]; [cbn [CL]; repeat step; clause_fin|]); lia.
Qed.

Lemma clause_post_clean c m i : 8 <= i -> get (clause_post c m) i = get m i.
Proof.
  intros Hi. destruct m as [a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10]. unfold clause_post. cbn [get].
  destruct a4 as [|[|a]];
  (do 9 (destruct c as [|c]; [cbn [set]; do 11 (destruct i as [|i]; [lia || reflexivity|]); reflexivity|]));
  cbn [set]; do 11 (destruct i as [|i]; [lia || reflexivity|]); reflexivity.
Qed.

Lemma clauses_ok l m : Forall (fun c => c < 15) l -> get m 8 = 0 -> get m 9 = 0 -> get m 10 = 0 ->
  seqx (flat_map CL l) m XNormal (fold_left (fun m c => clause_post c m) l m).
Proof.
  intros Hl. revert m. induction Hl as [|c l Hc Hl IH]; intros m H8 H9 H10; cbn [flat_map fold_left].
  - constructor.
  - eapply seqx_app; [apply clause_ok; auto|].
    apply IH; rewrite clause_post_clean; auto.
Qed.
