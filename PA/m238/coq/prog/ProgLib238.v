(** Local adaptation of Jeffrey's helper induction proofs in ZF/m254,
    external proof pin c132d7eae8158cd3a9850ea3eb7251158c3dd821.
    The original explanatory header is retained below. PA238 adaptations use
    the frozen Dag238 suffix IDs, Codes238 arithmetic, and a prefix relation
    that permits arbitrary values beyond the nine logical source registers.
    No PA source execution result is assumed. *)

(** * ProgLib254: lemmas for the structured semantics of [dag254] (Dag254.v, the Wade compile of
    zf/m254/inputs/source.py), used by Prog254.v to show that one run of the root is one
    [Enum254.enum_step].

    Method (as zf/v335/coq/ProgLib.v).  Register files are related pointwise to a 9-field record
    [St] ([approx]); [sem e m x m'] says every register file matching [m] runs edge [e] to exit [x]
    and a file matching [m'].  Nodes that are plain sequences are flattened ([expand]) into lists of
    "atoms" (nodes with their own lemma) by computation; atoms with control flow (while_decnz loops,
    pair, unpair, if_eq, if_not_decnz) are proved by induction.  Wff codes are astronomically large:
    [P] is made opaque and codes are only ever manipulated symbolically.

    Registers (declaration order of source.py): 0 nextproof, 1 topwff, 2 wffstack, 3 axiomcode,
    4 param1, 5 param2, 6 scratch1, 7 scratch2, 8 prooflist.  "Clean" = scratch1 = scratch2 = 0. *)

From Coq Require Import Lists.List Arith.Arith Lia Bool.Bool.
From P238.tm Require Import RM238.
From P238.prog Require Import Dag238.
From P238.logic Require Import Codes238.
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

(** ** Abstract source register prefix: nine registers. Outside registers are unrestricted. *)
Record St : Type := mkSt {
  r_np : nat; r_tw : nat; r_ws : nat; r_ac : nat; r_p1 : nat; r_p2 : nat;
  r_s1 : nat; r_s2 : nat; r_pl : nat }.

Definition get (m : St) (i : nat) : nat :=
  let 'mkSt a0 a1 a2 a3 a4 a5 a6 a7 a8 := m in
  match i with
  | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => a4 | 5 => a5 | 6 => a6 | 7 => a7 | 8 => a8
  | _ => 0
  end.

Definition set (m : St) (i v : nat) : St :=
  let 'mkSt a0 a1 a2 a3 a4 a5 a6 a7 a8 := m in
  match i with
  | 0 => mkSt v a1 a2 a3 a4 a5 a6 a7 a8
  | 1 => mkSt a0 v a2 a3 a4 a5 a6 a7 a8
  | 2 => mkSt a0 a1 v a3 a4 a5 a6 a7 a8
  | 3 => mkSt a0 a1 a2 v a4 a5 a6 a7 a8
  | 4 => mkSt a0 a1 a2 a3 v a5 a6 a7 a8
  | 5 => mkSt a0 a1 a2 a3 a4 v a6 a7 a8
  | 6 => mkSt a0 a1 a2 a3 a4 a5 v a7 a8
  | 7 => mkSt a0 a1 a2 a3 a4 a5 a6 v a8
  | 8 => mkSt a0 a1 a2 a3 a4 a5 a6 a7 v
  | _ => m
  end.

Definition inc (r : nat) (m : St) : St := set m r (S (get m r)).

(* one step of the source's unpair walk on registers (o1, o2) *)
Definition ustep (o1 o2 : nat) (m : St) : St :=
  set (set m o1 (fst (next_pair (get m o1, get m o2)))) o2 (snd (next_pair (get m o1, get m o2))).

(* result of unpair(o1, o2, i) *)
Definition unpair_post (i o1 o2 : nat) (m : St) : St :=
  set (set (set m i 0) o1 (fst (Nat.iter (get m i) next_pair (get m o1, get m o2))))
      o2 (snd (Nat.iter (get m i) next_pair (get m o1, get m o2))).

Lemma get_set m r i v : r <= 8 -> get (set m r v) i = if Nat.eqb i r then v else get m i.
Proof.
  intros Hr; destruct m.
  do 9 (destruct r as [|r]; [do 9 (destruct i as [|i]; [reflexivity|]); reflexivity|]); lia.
Qed.

Definition approx (R : regs) (m : St) : Prop := forall i, i <= 8 -> R i = get m i.

Lemma approx_upd R m r v : r <= 8 -> approx R m -> approx (upd R r v) (set m r v).
Proof.
  intros Hr H i Hi. unfold upd. rewrite get_set by exact Hr.
  destruct (Nat.eqb i r); auto.
Qed.

(** [sem e m x m']: from any register file matching [m], edge [e] runs to exit [x] and a file
    matching [m']. *)
Definition sem (e : edge) (m : St) (x : exit) (m' : St) : Prop :=
  forall R, approx R m -> exists R', run dag238 e R x R' /\ approx R' m'.

Lemma sem_conseq e m x m1 m2 : sem e m x m1 -> m1 = m2 -> sem e m x m2.
Proof. intros H <-; exact H. Qed.

Lemma sem_inc r m : r <= 8 -> sem (EInc r) m XNormal (inc r m).
Proof.
  intros Hr R HR. exists (upd R r (S (R r))). split; [constructor|].
  unfold inc. rewrite (HR r Hr). apply approx_upd; auto.
Qed.

Lemma sem_decnz_pos r m v : r <= 8 -> get m r = S v -> sem (EDecnz r) m XNormal (set m r v).
Proof.
  intros Hr Hv R HR. exists (upd R r v). split.
  - constructor. rewrite (HR r Hr); exact Hv.
  - apply approx_upd; auto.
Qed.

Lemma sem_decnz_zero r m : r <= 8 -> get m r = 0 -> sem (EDecnz r) m (XBreak 1) m.
Proof. intros Hr H0 R HR. exists R. split; auto. constructor. rewrite (HR r Hr); exact H0. Qed.

Lemma sem_breakS k m : sem (EBreak (S k)) m (XBreak (S k)) m.
Proof. intros R HR. exists R. split; auto. constructor. Qed.

Lemma sem_cont k m : sem (EContinue (S k)) m (XContinue (S k)) m.
Proof. intros R HR. exists R. split; auto. constructor. Qed.

Lemma sem_halt m : sem EHalt m XHalt m.
Proof. intros R HR. exists R. split; auto. constructor. Qed.

Section NodeRules.
Variables (n : nat) (a b : edge).
Hypothesis Hn : dag_nodes n = (a, b).

Lemma sem_car_break1 m m' : sem a m (XBreak 1) m' -> sem (ENode n) m XNormal m'.
Proof using Hn a b n.
  intros H R HR. destruct (H R HR) as (R' & Hr & HR'). exists R'. split; auto.
  apply run_node_car_break1. cbn. rewrite Hn. exact Hr.
Qed.

Lemma sem_car_breakS k m m' : sem a m (XBreak (S (S k))) m' -> sem (ENode n) m (XBreak (S k)) m'.
Proof using Hn a b n.
  intros H R HR. destruct (H R HR) as (R' & Hr & HR'). exists R'. split; auto.
  apply run_node_car_breakS. cbn. rewrite Hn. exact Hr.
Qed.

Lemma sem_car_continue k m m' : sem a m (XContinue (S k)) m' -> sem (ENode n) m (XContinue (S k)) m'.
Proof using Hn a b n.
  intros H R HR. destruct (H R HR) as (R' & Hr & HR'). exists R'. split; auto.
  apply run_node_car_continue. cbn. rewrite Hn. exact Hr.
Qed.

Lemma sem_car_halt m m' : sem a m XHalt m' -> sem (ENode n) m XHalt m'.
Proof using Hn a b n.
  intros H R HR. destruct (H R HR) as (R' & Hr & HR'). exists R'. split; auto.
  apply run_node_car_halt. cbn. rewrite Hn. exact Hr.
Qed.

Lemma sem_cdr_normal m m1 m' : sem a m XNormal m1 -> sem b m1 XNormal m' -> sem (ENode n) m XNormal m'.
Proof using Hn a b n.
  intros H1 H2 R HR. destruct (H1 R HR) as (R1 & Hr1 & HR1).
  destruct (H2 R1 HR1) as (R' & Hr & HR'). exists R'. split; auto.
  eapply run_node_cdr_normal; cbn; rewrite Hn; eauto.
Qed.

Lemma sem_cdr_break k m m1 m' : sem a m XNormal m1 -> sem b m1 (XBreak (S k)) m' ->
  sem (ENode n) m (XBreak (S k)) m'.
Proof using Hn a b n.
  intros H1 H2 R HR. destruct (H1 R HR) as (R1 & Hr1 & HR1).
  destruct (H2 R1 HR1) as (R' & Hr & HR'). exists R'. split; auto.
  eapply run_node_cdr_break; cbn; rewrite Hn; eauto.
Qed.

Lemma sem_cdr_continue1 m m1 m2 x m' : sem a m XNormal m1 -> sem b m1 (XContinue 1) m2 ->
  sem (ENode n) m2 x m' -> sem (ENode n) m x m'.
Proof using Hn a b n.
  intros H1 H2 H3 R HR. destruct (H1 R HR) as (R1 & Hr1 & HR1).
  destruct (H2 R1 HR1) as (R2 & Hr2 & HR2). destruct (H3 R2 HR2) as (R' & Hr & HR').
  exists R'. split; auto.
  eapply run_node_cdr_continue1; [cbn; rewrite Hn; eauto | cbn; rewrite Hn; eauto | exact Hr].
Qed.

Lemma sem_cdr_continueS k m m1 m' : sem a m XNormal m1 -> sem b m1 (XContinue (S (S k))) m' ->
  sem (ENode n) m (XContinue (S k)) m'.
Proof using Hn a b n.
  intros H1 H2 R HR. destruct (H1 R HR) as (R1 & Hr1 & HR1).
  destruct (H2 R1 HR1) as (R' & Hr & HR'). exists R'. split; auto.
  eapply run_node_cdr_continueS; cbn; rewrite Hn; eauto.
Qed.

Lemma sem_cdr_halt m m1 m' : sem a m XNormal m1 -> sem b m1 XHalt m' -> sem (ENode n) m XHalt m'.
Proof using Hn a b n.
  intros H1 H2 R HR. destruct (H1 R HR) as (R1 & Hr1 & HR1).
  destruct (H2 R1 HR1) as (R' & Hr & HR'). exists R'. split; auto.
  eapply run_node_cdr_halt; cbn; rewrite Hn; eauto.
Qed.

End NodeRules.

(** ** while_decnz(r, body): node [n] = (decnz r, b), [b] exits with continue 1. *)
Lemma sem_while n r b (g P : St -> St) :
  dag_nodes n = (EDecnz r, b) -> r <= 8 ->
  (forall m, sem b m (XContinue 1) (g m)) ->
  (forall m, get (g m) r = get m r) ->
  (forall m, get m r = 0 -> P m = m) ->
  (forall m v, get m r = S v -> P m = P (g (set m r v))) ->
  forall m, sem (ENode n) m XNormal (P m).
Proof.
  intros Hn Hr Hb Hg HP0 HPS.
  assert (H : forall k m, get m r = k -> sem (ENode n) m XNormal (P m)).
  { induction k as [|k IH]; intros m Hk.
    - rewrite (HP0 m Hk). eapply sem_car_break1; [exact Hn|]. apply sem_decnz_zero; [exact Hr|exact Hk].
    - rewrite (HPS m k Hk). eapply sem_cdr_continue1; [exact Hn| | apply Hb |].
      + apply sem_decnz_pos; [exact Hr | exact Hk].
      + apply IH. rewrite Hg, get_set by exact Hr. rewrite Nat.eqb_refl. reflexivity. }
  intros m. apply (H _ m eq_refl).
Qed.

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
Definition atoms : list nat := [87; 88; 89; 91; 93; 95; 102; 103; 104; 105; 113; 130; 132; 134; 138; 140; 142; 143; 146; 147; 148; 149; 150; 152; 153; 154; 155; 164; 165; 166; 169; 170; 171; 172; 173; 175; 177; 179; 180; 181; 183; 184; 186; 187; 188; 189; 190].
(* END GENERATED atoms *)

Definition is_atom (n : nat) : bool := existsb (Nat.eqb n) atoms.

Fixpoint expand (fuel : nat) (e : edge) : list edge :=
  match fuel with
  | 0 => [e]
  | S f =>
    match e with
    | ENode n => if is_atom n then [e] else expand f (fst (dag_nodes n)) ++ expand f (snd (dag_nodes n))
    | _ => [e]
    end
  end.

Lemma expand_sound fuel e m x m' : seqx (expand fuel e) m x m' -> sem e m x m'.
Proof.
  revert e m x m'. induction fuel as [|f IH]; intros e m x m' H; cbn [expand] in H.
  - apply seqx_single, H.
  - destruct e; try (apply seqx_single, H).
    destruct (is_atom n); [apply seqx_single, H|].
    destruct (seqx_app_inv _ _ _ _ _ H) as [(m1 & H1 & H2) | (-> & H1)];
      pose proof (surjective_pairing (dag_nodes n)) as Hn.
    + destruct (seqx_exit _ _ _ _ H2) as [-> | ->].
      * eapply sem_cdr_normal; [exact Hn | apply IH, H1 | apply IH, H2].
      * eapply sem_cdr_halt; [exact Hn | apply IH, H1 | apply IH, H2].
    + eapply sem_car_halt; [exact Hn | apply IH, H1].
Qed.

Lemma seq_node n m x m' :
  seqx (expand 200 (fst (dag_nodes n)) ++ expand 200 (snd (dag_nodes n))) m x m' -> sem (ENode n) m x m'.
Proof.
  intros H. pose proof (surjective_pairing (dag_nodes n)) as Hn.
  destruct (seqx_app_inv _ _ _ _ _ H) as [(m1 & H1 & H2) | (-> & H1)].
  - destruct (seqx_exit _ _ _ _ H2) as [-> | ->].
    + eapply sem_cdr_normal; [exact Hn | apply (expand_sound 200), H1 | apply (expand_sound 200), H2].
    + eapply sem_cdr_halt; [exact Hn | apply (expand_sound 200), H1 | apply (expand_sound 200), H2].
  - eapply sem_car_halt; [exact Hn | apply (expand_sound 200), H1].
Qed.

Ltac nrm := cbn [get set inc ustep unpair_post] in *.

Ltac expand_goal :=
  match goal with |- seqx ?l0 _ _ _ =>
    let l := eval vm_compute in l0 in
    let E := fresh "E" in assert (E : l0 = l) by (vm_compute; reflexivity);
    rewrite E; clear E
  end.

(** ** Loop bodies made of increments only: (incs, continue 2). *)
Lemma body_incs n x m m' : dag_nodes n = (x, EContinue 2) -> seqx (expand 10 x) m XNormal m' ->
  sem (ENode n) m (XContinue 1) m'.
Proof.
  intros Hn H. eapply sem_cdr_continueS with (k := 0); [exact Hn | apply (expand_sound 10), H | apply sem_cont].
Qed.

Ltac body_tac :=
  first [ apply sem_cont
        | intros; eapply body_incs; [reflexivity|]; expand_goal;
          repeat (eapply sx_normal; [apply sem_inc; lia | ]); apply sx_nil_eq; reflexivity ].

(** Closed forms of the loops are checked field by field. *)
Ltac fields := intros; repeat match goal with m : St |- _ => destruct m end; nrm; subst;
  try (f_equal; first [reflexivity | lia]).

Ltac while_tac g P :=
  intros m; eapply (sem_while _ _ _ g P);
  [ reflexivity | lia | intros; body_tac | clear m; intros m; destruct m; reflexivity | fields | fields ].

(** The while_decnz loops with increment-only bodies (generated by tools/gen_prog.py from Dag238.v):
    while_decnz(r, body): r := 0, each target += (multiplicity) * r. *)
(* BEGIN GENERATED loops *)
(* fn_44().0 *)
Lemma w89 m : sem (ENode 89) m XNormal (set (set m 1 (get m 1 + 4 * get m 7)) 7 0).
Proof. revert m; while_tac (fun m : St => inc 1 (inc 1 (inc 1 (inc 1 m)))) (fun m : St => set (set m 1 (get m 1 + 4 * get m 7)) 7 0). Qed.
(* while_decnz(axiomcode,26).0 *)
Lemma w164 m : sem (ENode 164) m XNormal (set (set (set m 6 (get m 6 + get m 3)) 7 (get m 7 + get m 3)) 3 0).
Proof. revert m; while_tac (fun m : St => inc 7 (inc 6 m)) (fun m : St => set (set (set m 6 (get m 6 + get m 3)) 7 (get m 7 + get m 3)) 3 0). Qed.
(* while_decnz(axiomcode,37).0 *)
Lemma w165 m : sem (ENode 165) m XNormal (set (set (set m 1 (get m 1 + get m 3)) 6 (get m 6 + get m 3)) 3 0).
Proof. revert m; while_tac (fun m : St => inc 1 (inc 6 m)) (fun m : St => set (set (set m 1 (get m 1 + get m 3)) 6 (get m 6 + get m 3)) 3 0). Qed.
(* while_decnz(nextproof,0).0 *)
Lemma w166 m : sem (ENode 166) m XNormal (set (set (set m 6 (get m 6 + get m 0)) 8 (get m 8 + get m 0)) 0 0).
Proof. revert m; while_tac (fun m : St => inc 6 (inc 8 m)) (fun m : St => set (set (set m 6 (get m 6 + get m 0)) 8 (get m 8 + get m 0)) 0 0). Qed.
(* while_decnz(param1,3.param2.inc).0 *)
Lemma w169 m : sem (ENode 169) m XNormal (set (set m 5 (get m 5 + get m 4)) 4 0).
Proof. revert m; while_tac (fun m : St => inc 5 m) (fun m : St => set (set m 5 (get m 5 + get m 4)) 4 0). Qed.
(* while_decnz(param1,37).0 *)
Lemma w170 m : sem (ENode 170) m XNormal (set (set (set m 1 (get m 1 + get m 4)) 6 (get m 6 + get m 4)) 4 0).
Proof. revert m; while_tac (fun m : St => inc 1 (inc 6 m)) (fun m : St => set (set (set m 1 (get m 1 + get m 4)) 6 (get m 6 + get m 4)) 4 0). Qed.
(* while_decnz(param2,()).0 *)
Lemma w171 m : sem (ENode 171) m XNormal (set m 5 0).
Proof. revert m; while_tac (fun m : St => m) (fun m : St => set m 5 0). Qed.
(* while_decnz(param2,37).0 *)
Lemma w172 m : sem (ENode 172) m XNormal (set (set (set m 1 (get m 1 + get m 5)) 6 (get m 6 + get m 5)) 5 0).
Proof. revert m; while_tac (fun m : St => inc 1 (inc 6 m)) (fun m : St => set (set (set m 1 (get m 1 + get m 5)) 6 (get m 6 + get m 5)) 5 0). Qed.
(* while_decnz(scratch1,3.axiomcode.inc).0 *)
Lemma w173 m : sem (ENode 173) m XNormal (set (set m 3 (get m 3 + get m 6)) 6 0).
Proof. revert m; while_tac (fun m : St => inc 3 m) (fun m : St => set (set m 3 (get m 3 + get m 6)) 6 0). Qed.
(* while_decnz(scratch1,3.nextproof.inc).0 *)
Lemma w175 m : sem (ENode 175) m XNormal (set (set m 0 (get m 0 + get m 6)) 6 0).
Proof. revert m; while_tac (fun m : St => inc 0 m) (fun m : St => set (set m 0 (get m 0 + get m 6)) 6 0). Qed.
(* while_decnz(scratch1,3.param1.inc).0 *)
Lemma w177 m : sem (ENode 177) m XNormal (set (set m 4 (get m 4 + get m 6)) 6 0).
Proof. revert m; while_tac (fun m : St => inc 4 m) (fun m : St => set (set m 4 (get m 4 + get m 6)) 6 0). Qed.
(* while_decnz(scratch1,3.param2.inc).0 *)
Lemma w179 m : sem (ENode 179) m XNormal (set (set m 5 (get m 5 + get m 6)) 6 0).
Proof. revert m; while_tac (fun m : St => inc 5 m) (fun m : St => set (set m 5 (get m 5 + get m 6)) 6 0). Qed.
(* while_decnz(scratch1,3.topwff.inc).0 *)
Lemma w180 m : sem (ENode 180) m XNormal (set (set m 1 (get m 1 + get m 6)) 6 0).
Proof. revert m; while_tac (fun m : St => inc 1 m) (fun m : St => set (set m 1 (get m 1 + get m 6)) 6 0). Qed.
(* while_decnz(scratch2,3.prooflist.inc).0 *)
Lemma w181 m : sem (ENode 181) m XNormal (set (set m 8 (get m 8 + get m 7)) 7 0).
Proof. revert m; while_tac (fun m : St => inc 8 m) (fun m : St => set (set m 8 (get m 8 + get m 7)) 7 0). Qed.
(* while_decnz(scratch2,3.scratch1.inc).0 *)
Lemma w183 m : sem (ENode 183) m XNormal (set (set m 6 (get m 6 + get m 7)) 7 0).
Proof. revert m; while_tac (fun m : St => inc 6 m) (fun m : St => set (set m 6 (get m 6 + get m 7)) 7 0). Qed.
(* while_decnz(scratch2,3.wffstack.inc).0 *)
Lemma w184 m : sem (ENode 184) m XNormal (set (set m 2 (get m 2 + get m 7)) 7 0).
Proof. revert m; while_tac (fun m : St => inc 2 m) (fun m : St => set (set m 2 (get m 2 + get m 7)) 7 0). Qed.
(* while_decnz(topwff,()).0 *)
Lemma w186 m : sem (ENode 186) m XNormal (set m 1 0).
Proof. revert m; while_tac (fun m : St => m) (fun m : St => set m 1 0). Qed.
(* while_decnz(topwff,26).0 *)
Lemma w187 m : sem (ENode 187) m XNormal (set (set (set m 6 (get m 6 + get m 1)) 7 (get m 7 + get m 1)) 1 0).
Proof. revert m; while_tac (fun m : St => inc 7 (inc 6 m)) (fun m : St => set (set (set m 6 (get m 6 + get m 1)) 7 (get m 7 + get m 1)) 1 0). Qed.
(* while_decnz(topwff,3.scratch1.inc).0 *)
Lemma w188 m : sem (ENode 188) m XNormal (set (set m 6 (get m 6 + get m 1)) 1 0).
Proof. revert m; while_tac (fun m : St => inc 6 m) (fun m : St => set (set m 6 (get m 6 + get m 1)) 1 0). Qed.
(* while_decnz(wffstack,3.topwff.inc).0 *)
Lemma w189 m : sem (ENode 189) m XNormal (set (set m 1 (get m 1 + get m 2)) 2 0).
Proof. revert m; while_tac (fun m : St => inc 1 m) (fun m : St => set (set m 1 (get m 1 + get m 2)) 2 0). Qed.
Ltac elem_w := match goal with
  | |- sem (ENode 89) _ _ _ => apply w89
  | |- sem (ENode 164) _ _ _ => apply w164
  | |- sem (ENode 165) _ _ _ => apply w165
  | |- sem (ENode 166) _ _ _ => apply w166
  | |- sem (ENode 169) _ _ _ => apply w169
  | |- sem (ENode 170) _ _ _ => apply w170
  | |- sem (ENode 171) _ _ _ => apply w171
  | |- sem (ENode 172) _ _ _ => apply w172
  | |- sem (ENode 173) _ _ _ => apply w173
  | |- sem (ENode 175) _ _ _ => apply w175
  | |- sem (ENode 177) _ _ _ => apply w177
  | |- sem (ENode 179) _ _ _ => apply w179
  | |- sem (ENode 180) _ _ _ => apply w180
  | |- sem (ENode 181) _ _ _ => apply w181
  | |- sem (ENode 183) _ _ _ => apply w183
  | |- sem (ENode 184) _ _ _ => apply w184
  | |- sem (ENode 186) _ _ _ => apply w186
  | |- sem (ENode 187) _ _ _ => apply w187
  | |- sem (ENode 188) _ _ _ => apply w188
  | |- sem (ENode 189) _ _ _ => apply w189
  end.
(* END GENERATED loops *)

(** ** pair(scratch2, scratch1, topwff): scratch2 += P scratch1 topwff; scratch1, topwff := 0.
    Loop: {while tw {tw--; s1++; s2++}; if s1 {s1--; s2++; while s1 {s1--; tw++}; continue}}. *)
Lemma pair_step a b k : a + b = S k -> P a b = b + S (P 0 k).
Proof. intros H. unfold P. rewrite H. cbn [Nat.add]. simpl. lia. Qed.

Lemma pair134 m :
  sem (ENode 134) m XNormal (set (set (set m 7 (get m 7 + P (get m 6) (get m 1))) 6 0) 1 0).
Proof.
  revert m. cut (forall k m, get m 6 + get m 1 = k ->
    sem (ENode 134) m XNormal (set (set (set m 7 (get m 7 + P (get m 6) (get m 1))) 6 0) 1 0)).
  { intros H m; apply (H _ m eq_refl). }
  induction k as [|k IH]; intros m Hk.
  - eapply sem_cdr_normal; [reflexivity | apply w187 |].
    eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; [lia|]] |];
      destruct m as [a0 a1 a2 a3 a4 a5 a6 a7 a8]; nrm; [lia|].
    assert (a6 = 0) by lia. assert (a1 = 0) by lia. subst. reflexivity.
  - eapply sem_cdr_continue1; [reflexivity | apply w187 | |].
    + eapply sem_cdr_continueS with (k := 0);
        [reflexivity | apply sem_decnz_pos with (v := k); [lia | destruct m; nrm; lia] |].
      eapply sem_cdr_continueS with (k := 1); [reflexivity | | apply sem_cont].
      eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia | apply w180].
    + eapply sem_conseq; [apply IH; destruct m; nrm; lia |].
      destruct m as [a0 a1 a2 a3 a4 a5 a6 a7 a8]; nrm. f_equal; try lia.
      rewrite (pair_step a6 a1 k) by lia. rewrite ?Nat.add_0_l, ?Nat.add_0_r. lia.
Qed.

(** ** unpair(scratch1, scratch2, in): [in] steps of [next_pair] from (scratch1, scratch2); in := 0.
    Body (node 154): {s2++; if s1 {s1--} else {while s2 {s2--; s1++}}; continue}. *)
Lemma ubody126 m : sem (ENode 126) m (XContinue 1) (ustep 6 7 m).
Proof.
  eapply sem_cdr_continueS with (k := 0); [reflexivity | | apply sem_cont].
  eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia |].
  destruct (get m 6) as [|v] eqn:Hv.
  - eapply sem_cdr_normal; [reflexivity | eapply sem_car_break1; [reflexivity|] | ].
    + apply sem_decnz_zero; [lia|]. destruct m; nrm; exact Hv.
    + eapply sem_conseq; [apply w183|]. destruct m; nrm; subst; cbn [next_pair fst snd]. f_equal; lia.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity|] |].
    + eapply sem_cdr_break with (k := 0); [reflexivity | | apply sem_breakS].
      apply sem_decnz_pos with (v := v); [lia | destruct m; nrm; exact Hv].
    + destruct m; nrm; subst; reflexivity.
Qed.

Ltac unpair_tac :=
  intros m; eapply (sem_while _ _ _ _ (unpair_post _ _ _));
  [ reflexivity | lia | apply ubody126 | clear m; intros m; destruct m; reflexivity
  | clear m; intros m H0; destruct m; unfold unpair_post; nrm; subst; reflexivity
  | clear m; intros m v Hv; destruct m; unfold unpair_post; nrm; subst;
    rewrite Nat.iter_succ_r, <- surjective_pairing; reflexivity ].

(* unpair(scratch1, scratch2, prooflist) *)
Lemma unpair87 m : sem (ENode 87) m XNormal (unpair_post 8 6 7 m).
Proof. revert m; unpair_tac. Qed.
(* unpair(scratch1, scratch2, wffstack) *)
Lemma unpair88 m : sem (ENode 88) m XNormal (unpair_post 2 6 7 m).
Proof. revert m; unpair_tac. Qed.

Lemma iter_unP z : Nat.iter z next_pair (0, 0) = unP z.
Proof. induction z; [reflexivity|]. rewrite Nat.iter_succ, IHz; reflexivity. Qed.

(* wff codes are astronomically large: never let tactic-level conversion compute a [P] *)
Opaque P.

(** Tactics for symbolic execution of sequences.  [elem] proves [sem e m XNormal ?m'] for an atom
    [e] by its lemma; it is extended (::=) as lemmas are added. *)
Ltac side := first [cbn [get]; reflexivity | lia].
Ltac elem0 :=
  match goal with
  | |- sem (EInc _) _ _ _ => apply sem_inc; lia
  | |- sem (ENode 134) _ _ _ => apply pair134
  | |- sem (ENode 87) _ _ _ => apply unpair87
  | |- sem (ENode 88) _ _ _ => apply unpair88
  | |- _ => elem_w
  end.
Ltac elem := elem0.

Ltac step := eapply sx_normal; [ elem | nrm ].
Ltac run_seq := apply seq_node; expand_goal; repeat step.

Ltac codes := unfold wa, wex, wn, wim, wel, wal, weq.

(* close a sequence: compare the final state field by field *)
Ltac fin := apply sx_nil_eq; rewrite ?iter_unP, ?unP_P; cbn [fst snd];
  try reflexivity; f_equal; codes; first [reflexivity | lia].

Ltac start := intros m; destruct m; intros; nrm; subst.

(** ** The stack subroutines (clean registers: scratch1 = scratch2 = 0). *)
(* pushwff(): wffstack := P topwff wffstack; topwff := 0 *)
Lemma pushwff143 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 143) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 0).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem1 := match goal with |- sem (ENode 143) _ _ _ => eapply pushwff143; side end.
Ltac elem ::= first [elem1 | elem0].

(* v_1(): push; topwff := 1 *)
Lemma v149 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 149) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 1).
Proof. revert m; start; run_seq; fin. Qed.
(* par1(), par2(), par3(): push; topwff := param *)
Lemma par138 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 138) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 (get m 4)).
Proof. revert m; start; run_seq; fin. Qed.
Lemma par93 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 93) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 (get m 5)).
Proof. revert m; start; run_seq; fin. Qed.
Lemma par140 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 140) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 (get m 3)).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem2 := match goal with
  | |- sem (ENode 149) _ _ _ => eapply v149; side
  | |- sem (ENode 138) _ _ _ => eapply par138; side
  | |- sem (ENode 93) _ _ _ => eapply par93; side
  | |- sem (ENode 140) _ _ _ => eapply par140; side
  end.
Ltac elem ::= first [elem2 | elem1 | elem0].

(** ** Reading the proof list and popping the stack (clean registers). *)
(* [unpair(scratch1, scratch2, prooflist); while scratch2 {prooflist++}] *)
Lemma n130 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 130) m XNormal (set (set m 6 (fst (unP (get m 8)))) 8 (snd (unP (get m 8)))).
Proof. revert m; start; run_seq; fin. Qed.
(* [unpair(scratch1, scratch2, wffstack); while scratch2 {wffstack++}] *)
Lemma n132 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 132) m XNormal (set (set m 6 (fst (unP (get m 2)))) 2 (snd (unP (get m 2)))).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem3 := match goal with
  | |- sem (ENode 130) _ _ _ => eapply n130; side
  | |- sem (ENode 132) _ _ _ => eapply n132; side
  end.
Ltac elem ::= first [elem3 | elem2 | elem1 | elem0].

(* cons() = wim(): (x, r) := unP wffstack; wffstack := r; topwff := wim x topwff *)
Lemma cons91 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 91) m XNormal (set (set m 1 (wim x (get m 1))) 2 r).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem4 := match goal with |- sem (ENode 91) _ _ _ => eapply cons91; side end.
Ltac elem ::= first [elem4 | elem3 | elem2 | elem1 | elem0].

Lemma wel153 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 153) m XNormal (set (set m 1 (wel x (get m 1))) 2 r).
Proof. revert m; start; run_seq; fin. Qed.
Lemma wal152 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 152) m XNormal (set (set m 1 (wal x (get m 1))) 2 r).
Proof. revert m; start; run_seq; fin. Qed.
Lemma weq154 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 154) m XNormal (set (set m 1 (weq x (get m 1))) 2 r).
Proof. revert m; start; run_seq; fin. Qed.
Lemma wn190 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 190) m XNormal (set m 1 (wn (get m 1))).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem5 := match goal with
  | |- sem (ENode 153) _ _ _ => eapply wel153; side
  | |- sem (ENode 152) _ _ _ => eapply wal152; side
  | |- sem (ENode 154) _ _ _ => eapply weq154; side
  | |- sem (ENode 190) _ _ _ => eapply wn190; side
  end.
Ltac elem ::= first [elem5 | elem4 | elem3 | elem2 | elem1 | elem0].

Lemma wex155 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 155) m XNormal (set (set m 1 (wex x (get m 1))) 2 r).
Proof. revert m; start; run_seq; fin. Qed.
Lemma wa150 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 150) m XNormal (set (set m 1 (wa x (get m 1))) 2 r).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem6 := match goal with
  | |- sem (ENode 155) _ _ _ => eapply wex155; side
  | |- sem (ENode 150) _ _ _ => eapply wa150; side
  end.
Ltac elem ::= first [elem6 | elem5 | elem4 | elem3 | elem2 | elem1 | elem0].


(* read(r): r += fst (unP prooflist); prooflist := snd (unP prooflist) *)
Lemma read146 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 146) m XNormal (set (set m 3 (get m 3 + fst (unP (get m 8)))) 8 (snd (unP (get m 8)))).
Proof. revert m; start; run_seq; fin. Qed.
Lemma read147 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 147) m XNormal (set (set m 4 (get m 4 + fst (unP (get m 8)))) 8 (snd (unP (get m 8)))).
Proof. revert m; start; run_seq; fin. Qed.
Lemma read148 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 148) m XNormal (set (set m 5 (get m 5 + fst (unP (get m 8)))) 8 (snd (unP (get m 8)))).
Proof. revert m; start; run_seq; fin. Qed.
(* pop(param2): param2 += fst (unP wffstack); wffstack := snd (unP wffstack) *)
Lemma pop142 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 142) m XNormal (set (set m 5 (get m 5 + fst (unP (get m 2)))) 2 (snd (unP (get m 2)))).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem7 := match goal with
  | |- sem (ENode 146) _ _ _ => eapply read146; side
  | |- sem (ENode 147) _ _ _ => eapply read147; side
  | |- sem (ENode 148) _ _ _ => eapply read148; side
  | |- sem (ENode 142) _ _ _ => eapply pop142; side
  end.
Ltac elem ::= first [elem7 | elem6 | elem5 | elem4 | elem3 | elem2 | elem1 | elem0].

(** ** if_eq(scratch1, param2, body): runs body iff scratch1 = param2; both are zeroed.
    Loop (node 124): {if s1 {s1--; if p2 {p2--; continue} else {while s1 {s1--; p2++}; p2++}}};
    then (node 128) {if p2 {while p2 {p2--}; skip body}}. *)
Definition clr (m : St) : St := set (set m 6 0) 5 0.

Lemma loop96 x : forall m, get m 6 = x ->
  (x <= get m 5 -> sem (ENode 96) m XNormal (set (set m 6 0) 5 (get m 5 - x))) /\
  (get m 5 < x -> sem (ENode 96) m XNormal (set (set m 6 0) 5 (x - get m 5))).
Proof.
  induction x as [|x IH]; intros m Hx; split; intros Hle.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; [lia|exact Hx]]|].
    destruct m; nrm; subst; f_equal; lia.
  - lia.
  - destruct (get m 5) as [|y] eqn:Hy; [lia|].
    eapply sem_cdr_continue1; [reflexivity | apply sem_decnz_pos; [lia | exact Hx] | |].
    + eapply sem_car_continue with (k := 0); [reflexivity|].
      eapply sem_cdr_continueS with (k := 0); [reflexivity | | apply sem_cont].
      apply sem_decnz_pos with (v := y); [lia | destruct m; nrm; exact Hy].
    + eapply sem_conseq;
        [apply (proj1 (IH (set (set m 6 x) 5 y) ltac:(destruct m; reflexivity))); destruct m; nrm; lia|].
      destruct m; nrm; subst; f_equal; lia.
  - destruct (get m 5) as [|y] eqn:Hy.
    + eapply sem_conseq.
      * eapply sem_cdr_normal; [reflexivity | apply sem_decnz_pos; [lia | exact Hx] |].
        eapply sem_cdr_normal; [reflexivity | |].
        -- eapply sem_car_break1; [reflexivity|]. apply sem_decnz_zero; [lia|]. destruct m; nrm; exact Hy.
        -- eapply sem_cdr_normal; [reflexivity | apply w179 | apply sem_inc; lia].
      * destruct m; nrm; subst; f_equal; lia.
    + eapply sem_cdr_continue1; [reflexivity | apply sem_decnz_pos; [lia | exact Hx] | |].
      * eapply sem_car_continue with (k := 0); [reflexivity|].
        eapply sem_cdr_continueS with (k := 0); [reflexivity | | apply sem_cont].
        apply sem_decnz_pos with (v := y); [lia | destruct m; nrm; exact Hy].
      * eapply sem_conseq;
          [apply (proj2 (IH (set (set m 6 x) 5 y) ltac:(destruct m; reflexivity))); destruct m; nrm; lia|].
        destruct m; nrm; subst; f_equal; lia.
Qed.

Lemma if123_eq m : get m 6 = get m 5 -> sem (ENode 95) m XNormal (clr m).
Proof.
  intros H. destruct (loop96 (get m 6) m eq_refl) as [H1 _].
  eapply sem_cdr_normal; [reflexivity | apply H1; lia |].
  eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; [lia|]]|].
  - destruct m; nrm; lia.
  - unfold clr; destruct m; nrm; f_equal; lia.
Qed.

Lemma if123_neq m : get m 6 <> get m 5 -> sem (ENode 95) m (XBreak 1) (clr m).
Proof.
  intros H. destruct (loop96 (get m 6) m eq_refl) as [H1 H2].
  assert (Hl : exists d, sem (ENode 96) m XNormal (set (set m 6 0) 5 (S d))).
  { destruct (Nat.lt_ge_cases (get m 5) (get m 6)) as [Hlt | Hge].
    - exists (get m 6 - get m 5 - 1).
      replace (S (get m 6 - get m 5 - 1)) with (get m 6 - get m 5) by lia. apply H2, Hlt.
    - exists (get m 5 - get m 6 - 1).
      replace (S (get m 5 - get m 6 - 1)) with (get m 5 - get m 6) by lia. apply H1, Hge. }
  destruct Hl as [d Hd].
  eapply sem_cdr_break with (k := 0); [reflexivity | exact Hd |].
  eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos with (v := d);
    [lia | destruct m; reflexivity] |].
  eapply sem_conseq; [eapply sem_cdr_break with (k := 0); [reflexivity | apply w171 | apply sem_breakS]|].
  unfold clr; destruct m; nrm; reflexivity.
Qed.

(* if_eq(scratch1, param2, par1()) *)
Lemma ifeq102 m : get m 7 = 0 -> sem (ENode 102) m XNormal
  (if Nat.eqb (get m 6) (get m 5)
   then set (set (clr m) 2 (P (get m 1) (get m 2))) 1 (get m 4) else clr m).
Proof.
  intros H7. destruct (Nat.eqb_spec (get m 6) (get m 5)) as [H | H].
  - eapply sem_cdr_normal; [reflexivity | apply if123_eq, H |].
    eapply sem_conseq; [apply par138; destruct m; nrm; auto|]. unfold clr; destruct m; reflexivity.
  - eapply sem_car_break1; [reflexivity | apply if123_neq, H].
Qed.

(* if_eq(scratch1, param2, topwff := 0) *)
Lemma ifeq103 m : sem (ENode 103) m XNormal
  (set (clr m) 1 (if Nat.eqb (get m 6) (get m 5) then 0 else get m 1)).
Proof.
  destruct (Nat.eqb_spec (get m 6) (get m 5)) as [H | H].
  - eapply sem_cdr_normal; [reflexivity | apply if123_eq, H |].
    eapply sem_conseq; [apply w186|]. unfold clr; destruct m; reflexivity.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply if123_neq, H]|].
    unfold clr; destruct m; reflexivity.
Qed.

(* if_eq(scratch1, param2, halt) *)
Lemma ifeq104_halt m : get m 6 = get m 5 -> sem (ENode 104) m XHalt (clr m).
Proof.
  intros H. eapply sem_cdr_halt; [reflexivity | apply if123_eq, H | apply sem_halt].
Qed.

Lemma ifeq104_normal m : get m 6 <> get m 5 -> sem (ENode 104) m XNormal (clr m).
Proof. intros H. eapply sem_car_break1; [reflexivity | apply if123_neq, H]. Qed.

Ltac elem8 := match goal with
  | |- sem (ENode 102) _ _ _ => eapply ifeq102; side
  | |- sem (ENode 103) _ _ _ => apply ifeq103
  end.
Ltac elem ::= first [elem8 | elem7 | elem6 | elem5 | elem4 | elem3 | elem2 | elem1 | elem0].

(** ** if_not_decnz(prooflist, {prooflist := nextproof; nextproof++}) *)
Lemma ifnot105 m : get m 6 = 0 -> sem (ENode 105) m XNormal
  (set (set m 8 (match get m 8 with 0 => get m 0 | S v => v end))
       0 (match get m 8 with 0 => S (get m 0) | S _ => get m 0 end)).
Proof.
  intros H6. destruct (get m 8) as [|v] eqn:H8.
  - eapply sem_cdr_normal; [reflexivity | eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; [lia|exact H8]] |].
    eapply sem_conseq; [eapply sem_cdr_normal; [reflexivity | apply w166 |
      eapply sem_cdr_normal; [reflexivity | apply w175 | apply sem_inc; lia]]|].
    destruct m; nrm; subst; f_equal; lia.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity|] |].
    + eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos; [lia | exact H8] | apply sem_breakS].
    + destruct m; nrm; subst; reflexivity.
Qed.

(** Every primitive in the frozen source graph uses the source prefix.
    This is independent of the initial values of the spare registers. *)
Definition source_edge238 (e : edge) : Prop :=
  match e with EInc r | EDecnz r => r <= 8 | _ => True end.

Lemma dag238_nodes_source n :
  source_edge238 (fst (nodes dag238 n)) /\ source_edge238 (snd (nodes dag238 n)).
Proof.
  unfold dag238; cbn [nodes].
  do 191 (destruct n as [|n]; [vm_compute; split; auto; lia|]).
  vm_compute; split; auto.
Qed.

Lemma run_dag238_preserves_outside e R x R' i :
  9 <= i -> run dag238 e R x R' -> source_edge238 e -> R' i = R i.
Proof.
  intros Hi Hr; induction Hr; intro He; cbn [source_edge238] in He; try reflexivity.
  all: try (unfold upd; destruct (Nat.eqb i r) eqn:E;
            [apply Nat.eqb_eq in E; lia|reflexivity]).
  all: pose proof (dag238_nodes_source n) as [Ha Hb].
  all: repeat match goal with
       | IH : source_edge238 ?e -> ?a = ?b,
         HS : source_edge238 ?e |- _ => specialize (IH HS)
       | IH : source_edge238 (ENode ?n) -> ?a = ?b |- _ => specialize (IH I)
       end.
  all: congruence.
Qed.

Corollary root_dag238_preserves_outside R x R' i :
  9 <= i -> run dag238 (ENode 0) R x R' -> R' i = R i.
Proof. intros Hi Hr; apply (run_dag238_preserves_outside _ _ _ _ i Hi Hr); exact I. Qed.
