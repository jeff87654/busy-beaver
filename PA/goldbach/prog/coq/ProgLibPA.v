(** * ProgLibPA: lemmas for the structured semantics of [dagpa] (DagPA.v, the Wade compile of
    zf/m254tg/machine/source_tg.py), used by L2RootPA.v to show that one run of the root is one
    [EnumTG.enum_step].  Ported from zf/m254/prog/coq/ProgLib254.v by tools/port.py (node renumbering
    only); the GENERATED regions are rewritten by tools/gen_prog.py.

    Method (as zf/v335/coq/ProgLib.v).  Register files are related pointwise to a 9-field record
    [St] ([approx]); [sem e m x m'] says every register file matching [m] runs edge [e] to exit [x]
    and a file matching [m'].  Nodes that are plain sequences are flattened ([expand]) into lists of
    "atoms" (nodes with their own lemma) by computation; atoms with control flow (while_decnz loops,
    pair, unpair, if_eq, if_not_decnz) are proved by induction.  Wff codes are astronomically large:
    [P] is made opaque and codes are only ever manipulated symbolically.

    Registers (declaration order of source_tg.py): 0 nextproof, 1 topwff, 2 wffstack, 3 axiomcode,
    4 param1, 5 param2, 6 scratch1, 7 scratch2, 8 prooflist.  "Clean" = scratch1 = scratch2 = 0. *)

From Coq Require Import Lists.List Arith.Arith Lia Bool.Bool.
From PAGBT Require Import RM DagPA.
From PAGBP Require Import ProgCodesPA.
Unset Implicit Arguments.
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

(** ** Abstract register files: 9 registers (all others are 0 and never touched). *)
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
  set (set m o1 (fst (unP_step (get m o1, get m o2)))) o2 (snd (unP_step (get m o1, get m o2))).

(* result of unpair(o1, o2, i) *)
Definition unpair_post (i o1 o2 : nat) (m : St) : St :=
  set (set (set m i 0) o1 (fst (Nat.iter (get m i) unP_step (get m o1, get m o2))))
      o2 (snd (Nat.iter (get m i) unP_step (get m o1, get m o2))).

Lemma get_set m r i v : r <= 8 -> get (set m r v) i = if Nat.eqb i r then v else get m i.
Proof.
  intros Hr; destruct m.
  do 9 (destruct r as [|r]; [do 9 (destruct i as [|i]; [reflexivity|]); reflexivity|]); lia.
Qed.

Definition approx (R : regs) (m : St) : Prop := forall i, R i = get m i.

Lemma approx_upd R m r v : r <= 8 -> approx R m -> approx (upd R r v) (set m r v).
Proof.
  intros Hr H i. unfold upd. rewrite get_set by exact Hr.
  destruct (Nat.eqb i r); auto.
Qed.

(** [sem e m x m']: from any register file matching [m], edge [e] runs to exit [x] and a file
    matching [m']. *)
Definition sem (e : edge) (m : St) (x : exit) (m' : St) : Prop :=
  forall R, approx R m -> exists R', run dagpa e R x R' /\ approx R' m'.

Lemma sem_conseq e m x m1 m2 : sem e m x m1 -> m1 = m2 -> sem e m x m2.
Proof. intros H <-; exact H. Qed.

Lemma sem_inc r m : r <= 8 -> sem (EInc r) m XNormal (inc r m).
Proof.
  intros Hr R HR. exists (upd R r (S (R r))). split; [constructor|].
  unfold inc. rewrite (HR r). apply approx_upd; auto.
Qed.

Lemma sem_decnz_pos r m v : r <= 8 -> get m r = S v -> sem (EDecnz r) m XNormal (set m r v).
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
Hypothesis Hn : dagpa_nodes n = (a, b).

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
  dagpa_nodes n = (EDecnz r, b) -> r <= 8 ->
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
Definition atoms : list nat := [199; 201; 204; 205; 206; 208; 210; 212; 215; 222; 230; 231; 235; 243; 260; 262; 266; 269; 270; 273; 276; 277; 296; 300; 304; 308; 312; 314; 316; 317; 320; 321; 322; 323; 327; 328; 329; 330; 341; 342; 343; 344; 347; 349; 350; 353; 354; 355; 356; 357; 358; 361; 362; 364; 365; 366; 367; 368; 371; 372; 373; 375; 376; 378; 379; 380; 381; 382].
(* END GENERATED atoms *)

Definition is_atom (n : nat) : bool := existsb (Nat.eqb n) atoms.

Fixpoint expand (fuel : nat) (e : edge) : list edge :=
  match fuel with
  | 0 => [e]
  | S f =>
    match e with
    | ENode n => if is_atom n then [e] else expand f (fst (dagpa_nodes n)) ++ expand f (snd (dagpa_nodes n))
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
      pose proof (surjective_pairing (dagpa_nodes n)) as Hn.
    + destruct (seqx_exit _ _ _ _ H2) as [-> | ->].
      * eapply sem_cdr_normal; [exact Hn | apply IH, H1 | apply IH, H2].
      * eapply sem_cdr_halt; [exact Hn | apply IH, H1 | apply IH, H2].
    + eapply sem_car_halt; [exact Hn | apply IH, H1].
Qed.

Lemma seq_node n m x m' :
  seqx (expand 200 (fst (dagpa_nodes n)) ++ expand 200 (snd (dagpa_nodes n))) m x m' -> sem (ENode n) m x m'.
Proof.
  intros H. pose proof (surjective_pairing (dagpa_nodes n)) as Hn.
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
Lemma body_incs n x m m' : dagpa_nodes n = (x, EContinue 2) -> seqx (expand 10 x) m XNormal m' ->
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

(** The while_decnz loops with increment-only bodies (generated by tools/gen_prog.py from DagPA.v):
    while_decnz(r, body): r := 0, each target += (multiplicity) * r. *)
(* BEGIN GENERATED loops *)
(* fn_44().0 *)
Lemma w206 m : sem (ENode 206) m XNormal (set (set m 1 (get m 1 + 4 * get m 7)) 7 0).
Proof. revert m; while_tac (fun m : St => inc 1 (inc 1 (inc 1 (inc 1 m)))) (fun m : St => set (set m 1 (get m 1 + 4 * get m 7)) 7 0). Qed.
(* while_decnz(axiomcode,()).0 *)
Lemma w341 m : sem (ENode 341) m XNormal (set m 3 0).
Proof. revert m; while_tac (fun m : St => m) (fun m : St => set m 3 0). Qed.
(* while_decnz(axiomcode,26).0 *)
Lemma w342 m : sem (ENode 342) m XNormal (set (set (set m 6 (get m 6 + get m 3)) 7 (get m 7 + get m 3)) 3 0).
Proof. revert m; while_tac (fun m : St => inc 7 (inc 6 m)) (fun m : St => set (set (set m 6 (get m 6 + get m 3)) 7 (get m 7 + get m 3)) 3 0). Qed.
(* while_decnz(axiomcode,37).0 *)
Lemma w343 m : sem (ENode 343) m XNormal (set (set (set m 1 (get m 1 + get m 3)) 6 (get m 6 + get m 3)) 3 0).
Proof. revert m; while_tac (fun m : St => inc 1 (inc 6 m)) (fun m : St => set (set (set m 1 (get m 1 + get m 3)) 6 (get m 6 + get m 3)) 3 0). Qed.
(* while_decnz(nextproof,0).0 *)
Lemma w344 m : sem (ENode 344) m XNormal (set (set (set m 6 (get m 6 + get m 0)) 8 (get m 8 + get m 0)) 0 0).
Proof. revert m; while_tac (fun m : St => inc 6 (inc 8 m)) (fun m : St => set (set (set m 6 (get m 6 + get m 0)) 8 (get m 8 + get m 0)) 0 0). Qed.
(* while_decnz(param1,3.scratch2.inc).0 *)
Lemma w347 m : sem (ENode 347) m XNormal (set (set m 7 (get m 7 + get m 4)) 4 0).
Proof. revert m; while_tac (fun m : St => inc 7 m) (fun m : St => set (set m 7 (get m 7 + get m 4)) 4 0). Qed.
(* while_decnz(param1,37).0 *)
Lemma w349 m : sem (ENode 349) m XNormal (set (set (set m 1 (get m 1 + get m 4)) 6 (get m 6 + get m 4)) 4 0).
Proof. revert m; while_tac (fun m : St => inc 1 (inc 6 m)) (fun m : St => set (set (set m 1 (get m 1 + get m 4)) 6 (get m 6 + get m 4)) 4 0). Qed.
(* while_decnz(param1,97).0 *)
Lemma w350 m : sem (ENode 350) m XNormal (set (set (set m 5 (get m 5 + get m 4)) 6 (get m 6 + get m 4)) 4 0).
Proof. revert m; while_tac (fun m : St => inc 6 (inc 5 m)) (fun m : St => set (set (set m 5 (get m 5 + get m 4)) 6 (get m 6 + get m 4)) 4 0). Qed.
(* while_decnz(param2,()).0 *)
Lemma w353 m : sem (ENode 353) m XNormal (set m 5 0).
Proof. revert m; while_tac (fun m : St => m) (fun m : St => set m 5 0). Qed.
(* while_decnz(param2,3.param1.inc).0 *)
Lemma w354 m : sem (ENode 354) m XNormal (set (set m 4 (get m 4 + get m 5)) 5 0).
Proof. revert m; while_tac (fun m : St => inc 4 m) (fun m : St => set (set m 4 (get m 4 + get m 5)) 5 0). Qed.
(* while_decnz(param2,3.scratch1.inc).0 *)
Lemma w355 m : sem (ENode 355) m XNormal (set (set m 6 (get m 6 + get m 5)) 5 0).
Proof. revert m; while_tac (fun m : St => inc 6 m) (fun m : St => set (set m 6 (get m 6 + get m 5)) 5 0). Qed.
(* while_decnz(param2,37).0 *)
Lemma w356 m : sem (ENode 356) m XNormal (set (set (set m 1 (get m 1 + get m 5)) 6 (get m 6 + get m 5)) 5 0).
Proof. revert m; while_tac (fun m : St => inc 1 (inc 6 m)) (fun m : St => set (set (set m 1 (get m 1 + get m 5)) 6 (get m 6 + get m 5)) 5 0). Qed.
(* while_decnz(scratch1,()).0 *)
Lemma w357 m : sem (ENode 357) m XNormal (set m 6 0).
Proof. revert m; while_tac (fun m : St => m) (fun m : St => set m 6 0). Qed.
(* while_decnz(scratch1,122).0 *)
Lemma w358 m : sem (ENode 358) m XNormal (set (set (set m 4 (get m 4 + get m 6)) 5 (get m 5 + get m 6)) 6 0).
Proof. revert m; while_tac (fun m : St => inc 4 (inc 5 m)) (fun m : St => set (set (set m 4 (get m 4 + get m 6)) 5 (get m 5 + get m 6)) 6 0). Qed.
(* while_decnz(scratch1,3.axiomcode.inc).0 *)
Lemma w361 m : sem (ENode 361) m XNormal (set (set m 3 (get m 3 + get m 6)) 6 0).
Proof. revert m; while_tac (fun m : St => inc 3 m) (fun m : St => set (set m 3 (get m 3 + get m 6)) 6 0). Qed.
(* while_decnz(scratch1,3.nextproof.inc).0 *)
Lemma w362 m : sem (ENode 362) m XNormal (set (set m 0 (get m 0 + get m 6)) 6 0).
Proof. revert m; while_tac (fun m : St => inc 0 m) (fun m : St => set (set m 0 (get m 0 + get m 6)) 6 0). Qed.
(* while_decnz(scratch1,3.param1.inc).0 *)
Lemma w364 m : sem (ENode 364) m XNormal (set (set m 4 (get m 4 + get m 6)) 6 0).
Proof. revert m; while_tac (fun m : St => inc 4 m) (fun m : St => set (set m 4 (get m 4 + get m 6)) 6 0). Qed.
(* while_decnz(scratch1,3.param2.inc).0 *)
Lemma w365 m : sem (ENode 365) m XNormal (set (set m 5 (get m 5 + get m 6)) 6 0).
Proof. revert m; while_tac (fun m : St => inc 5 m) (fun m : St => set (set m 5 (get m 5 + get m 6)) 6 0). Qed.
(* while_decnz(scratch1,3.topwff.inc).0 *)
Lemma w366 m : sem (ENode 366) m XNormal (set (set m 1 (get m 1 + get m 6)) 6 0).
Proof. revert m; while_tac (fun m : St => inc 1 m) (fun m : St => set (set m 1 (get m 1 + get m 6)) 6 0). Qed.
(* while_decnz(scratch2,()).0 *)
Lemma w367 m : sem (ENode 367) m XNormal (set m 7 0).
Proof. revert m; while_tac (fun m : St => m) (fun m : St => set m 7 0). Qed.
(* while_decnz(scratch2,113).0 *)
Lemma w368 m : sem (ENode 368) m XNormal (set (set (set m 4 (get m 4 + get m 7)) 6 (get m 6 + get m 7)) 7 0).
Proof. revert m; while_tac (fun m : St => inc 6 (inc 4 m)) (fun m : St => set (set (set m 4 (get m 4 + get m 7)) 6 (get m 6 + get m 7)) 7 0). Qed.
(* while_decnz(scratch2,3.axiomcode.inc).0 *)
Lemma w371 m : sem (ENode 371) m XNormal (set (set m 3 (get m 3 + get m 7)) 7 0).
Proof. revert m; while_tac (fun m : St => inc 3 m) (fun m : St => set (set m 3 (get m 3 + get m 7)) 7 0). Qed.
(* while_decnz(scratch2,3.param2.inc).0 *)
Lemma w372 m : sem (ENode 372) m XNormal (set (set m 5 (get m 5 + get m 7)) 7 0).
Proof. revert m; while_tac (fun m : St => inc 5 m) (fun m : St => set (set m 5 (get m 5 + get m 7)) 7 0). Qed.
(* while_decnz(scratch2,3.prooflist.inc).0 *)
Lemma w373 m : sem (ENode 373) m XNormal (set (set m 8 (get m 8 + get m 7)) 7 0).
Proof. revert m; while_tac (fun m : St => inc 8 m) (fun m : St => set (set m 8 (get m 8 + get m 7)) 7 0). Qed.
(* while_decnz(scratch2,3.scratch1.inc).0 *)
Lemma w375 m : sem (ENode 375) m XNormal (set (set m 6 (get m 6 + get m 7)) 7 0).
Proof. revert m; while_tac (fun m : St => inc 6 m) (fun m : St => set (set m 6 (get m 6 + get m 7)) 7 0). Qed.
(* while_decnz(scratch2,3.wffstack.inc).0 *)
Lemma w376 m : sem (ENode 376) m XNormal (set (set m 2 (get m 2 + get m 7)) 7 0).
Proof. revert m; while_tac (fun m : St => inc 2 m) (fun m : St => set (set m 2 (get m 2 + get m 7)) 7 0). Qed.
(* while_decnz(topwff,()).0 *)
Lemma w378 m : sem (ENode 378) m XNormal (set m 1 0).
Proof. revert m; while_tac (fun m : St => m) (fun m : St => set m 1 0). Qed.
(* while_decnz(topwff,26).0 *)
Lemma w379 m : sem (ENode 379) m XNormal (set (set (set m 6 (get m 6 + get m 1)) 7 (get m 7 + get m 1)) 1 0).
Proof. revert m; while_tac (fun m : St => inc 7 (inc 6 m)) (fun m : St => set (set (set m 6 (get m 6 + get m 1)) 7 (get m 7 + get m 1)) 1 0). Qed.
(* while_decnz(topwff,3.scratch1.inc).0 *)
Lemma w380 m : sem (ENode 380) m XNormal (set (set m 6 (get m 6 + get m 1)) 1 0).
Proof. revert m; while_tac (fun m : St => inc 6 m) (fun m : St => set (set m 6 (get m 6 + get m 1)) 1 0). Qed.
(* while_decnz(wffstack,3.topwff.inc).0 *)
Lemma w381 m : sem (ENode 381) m XNormal (set (set m 1 (get m 1 + get m 2)) 2 0).
Proof. revert m; while_tac (fun m : St => inc 1 m) (fun m : St => set (set m 1 (get m 1 + get m 2)) 2 0). Qed.
Ltac elem_w := match goal with
  | |- sem (ENode 206) _ _ _ => apply w206
  | |- sem (ENode 341) _ _ _ => apply w341
  | |- sem (ENode 342) _ _ _ => apply w342
  | |- sem (ENode 343) _ _ _ => apply w343
  | |- sem (ENode 344) _ _ _ => apply w344
  | |- sem (ENode 347) _ _ _ => apply w347
  | |- sem (ENode 349) _ _ _ => apply w349
  | |- sem (ENode 350) _ _ _ => apply w350
  | |- sem (ENode 353) _ _ _ => apply w353
  | |- sem (ENode 354) _ _ _ => apply w354
  | |- sem (ENode 355) _ _ _ => apply w355
  | |- sem (ENode 356) _ _ _ => apply w356
  | |- sem (ENode 357) _ _ _ => apply w357
  | |- sem (ENode 358) _ _ _ => apply w358
  | |- sem (ENode 361) _ _ _ => apply w361
  | |- sem (ENode 362) _ _ _ => apply w362
  | |- sem (ENode 364) _ _ _ => apply w364
  | |- sem (ENode 365) _ _ _ => apply w365
  | |- sem (ENode 366) _ _ _ => apply w366
  | |- sem (ENode 367) _ _ _ => apply w367
  | |- sem (ENode 368) _ _ _ => apply w368
  | |- sem (ENode 371) _ _ _ => apply w371
  | |- sem (ENode 372) _ _ _ => apply w372
  | |- sem (ENode 373) _ _ _ => apply w373
  | |- sem (ENode 375) _ _ _ => apply w375
  | |- sem (ENode 376) _ _ _ => apply w376
  | |- sem (ENode 378) _ _ _ => apply w378
  | |- sem (ENode 379) _ _ _ => apply w379
  | |- sem (ENode 380) _ _ _ => apply w380
  | |- sem (ENode 381) _ _ _ => apply w381
  end.
(* END GENERATED loops *)

(** ** pair(scratch2, scratch1, topwff): scratch2 += P scratch1 topwff; scratch1, topwff := 0.
    Loop: {while tw {tw--; s1++; s2++}; if s1 {s1--; s2++; while s1 {s1--; tw++}; continue}}. *)
Lemma pair_step a b k : a + b = S k -> P a b = b + S (P 0 k).
Proof. intros H. unfold P. rewrite H. cbn [Nat.add]. rewrite tri_S. lia. Qed.

Lemma pair308 m :
  sem (ENode 308) m XNormal (set (set (set m 7 (get m 7 + P (get m 6) (get m 1))) 6 0) 1 0).
Proof.
  revert m. cut (forall k m, get m 6 + get m 1 = k ->
    sem (ENode 308) m XNormal (set (set (set m 7 (get m 7 + P (get m 6) (get m 1))) 6 0) 1 0)).
  { intros H m; apply (H _ m eq_refl). }
  induction k as [|k IH]; intros m Hk.
  - eapply sem_cdr_normal; [reflexivity | apply w379 |].
    eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero] |];
      destruct m as [a0 a1 a2 a3 a4 a5 a6 a7 a8]; nrm; [lia|].
    assert (a6 = 0) by lia. assert (a1 = 0) by lia. subst. reflexivity.
  - eapply sem_cdr_continue1; [reflexivity | apply w379 | |].
    + eapply sem_cdr_continueS with (k := 0);
        [reflexivity | apply sem_decnz_pos with (v := k); [lia | destruct m; nrm; lia] |].
      eapply sem_cdr_continueS with (k := 1); [reflexivity | | apply sem_cont].
      eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia | apply w366].
    + eapply sem_conseq; [apply IH; destruct m; nrm; lia |].
      destruct m as [a0 a1 a2 a3 a4 a5 a6 a7 a8]; nrm. f_equal; try lia.
      rewrite (pair_step a6 a1 k) by lia. rewrite ?Nat.add_0_l, ?Nat.add_0_r. lia.
Qed.

(** ** unpair(scratch1, scratch2, in): [in] steps of [unP_step] from (scratch1, scratch2); in := 0.
    Body (node 256): {s2++; if s1 {s1--} else {while s2 {s2--; s1++}}; continue}. *)
Lemma ubody256 m : sem (ENode 256) m (XContinue 1) (ustep 6 7 m).
Proof.
  eapply sem_cdr_continueS with (k := 0); [reflexivity | | apply sem_cont].
  eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia |].
  destruct (get m 6) as [|v] eqn:Hv.
  - eapply sem_cdr_normal; [reflexivity | eapply sem_car_break1; [reflexivity|] | ].
    + apply sem_decnz_zero. destruct m; nrm; exact Hv.
    + eapply sem_conseq; [apply w375|]. destruct m; nrm; subst; cbn [unP_step fst snd]. f_equal; lia.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity|] |].
    + eapply sem_cdr_break with (k := 0); [reflexivity | | apply sem_breakS].
      apply sem_decnz_pos with (v := v); [lia | destruct m; nrm; exact Hv].
    + destruct m; nrm; subst; reflexivity.
Qed.

Ltac unpair_tac :=
  intros m; eapply (sem_while _ _ _ _ (unpair_post _ _ _));
  [ reflexivity | lia | apply ubody256 | clear m; intros m; destruct m; reflexivity
  | clear m; intros m H0; destruct m; unfold unpair_post; nrm; subst; reflexivity
  | clear m; intros m v Hv; destruct m; unfold unpair_post; nrm; subst;
    rewrite Nat.iter_succ_r, <- surjective_pairing; reflexivity ].

(* unpair(scratch1, scratch2, prooflist) *)
Lemma unpair204 m : sem (ENode 204) m XNormal (unpair_post 8 6 7 m).
Proof. revert m; unpair_tac. Qed.
(* unpair(scratch1, scratch2, wffstack) *)
Lemma unpair205 m : sem (ENode 205) m XNormal (unpair_post 2 6 7 m).
Proof. revert m; unpair_tac. Qed.

Lemma iter_unP z : Nat.iter z unP_step (0, 0) = unP z.
Proof. reflexivity. Qed.

(* wff codes are astronomically large: never let tactic-level conversion compute a [P] *)
Opaque P.

(** Tactics for symbolic execution of sequences.  [elem] proves [sem e m XNormal ?m'] for an atom
    [e] by its lemma; it is extended (::=) as lemmas are added. *)
Ltac side := first [cbn [get]; reflexivity | lia].
Ltac elem0 :=
  match goal with
  | |- sem (EInc _) _ _ _ => apply sem_inc; lia
  | |- sem (ENode 308) _ _ _ => apply pair308
  | |- sem (ENode 204) _ _ _ => apply unpair204
  | |- sem (ENode 205) _ _ _ => apply unpair205
  | |- _ => elem_w
  end.
Ltac elem := elem0.

Ltac step := eapply sx_normal; [ elem | nrm ].
Ltac run_seq := apply seq_node; expand_goal; repeat step.

Ltac codes := unfold wa, wex, wn, wim, wel, wal, weq, F.

(* close a sequence: compare the final state field by field *)
Ltac fin := apply sx_nil_eq; rewrite ?iter_unP, ?unP_P; cbn [fst snd];
  try reflexivity; f_equal; codes; first [reflexivity | lia].

Ltac start := intros m; destruct m; intros; nrm; subst.

(** ** The stack subroutines (clean registers: scratch1 = scratch2 = 0). *)
(* pushwff(): wffstack := P topwff wffstack; topwff := 0 *)
Lemma pushwff317 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 317) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 0).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem1 := match goal with |- sem (ENode 317) _ _ _ => eapply pushwff317; side end.
Ltac elem ::= first [elem1 | elem0].

(* v_1(): push; topwff := 1 *)
Lemma v323 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 323) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 1).
Proof. revert m; start; run_seq; fin. Qed.
(* par1(), par2(), par3(): push; topwff := param *)
Lemma par312 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 312) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 (get m 4)).
Proof. revert m; start; run_seq; fin. Qed.
Lemma par210 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 210) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 (get m 5)).
Proof. revert m; start; run_seq; fin. Qed.
Lemma par314 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 314) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 (get m 3)).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem2 := match goal with
  | |- sem (ENode 323) _ _ _ => eapply v323; side
  | |- sem (ENode 312) _ _ _ => eapply par312; side
  | |- sem (ENode 210) _ _ _ => eapply par210; side
  | |- sem (ENode 314) _ _ _ => eapply par314; side
  end.
Ltac elem ::= first [elem2 | elem1 | elem0].

(** ** Reading the proof list and popping the stack (clean registers). *)
(* [unpair(scratch1, scratch2, prooflist); while scratch2 {prooflist++}] *)
Lemma n260 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 260) m XNormal (set (set m 6 (fst (unP (get m 8)))) 8 (snd (unP (get m 8)))).
Proof. revert m; start; run_seq; fin. Qed.
(* [unpair(scratch1, scratch2, wffstack); while scratch2 {wffstack++}] *)
Lemma n262 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 262) m XNormal (set (set m 6 (fst (unP (get m 2)))) 2 (snd (unP (get m 2)))).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem3 := match goal with
  | |- sem (ENode 260) _ _ _ => eapply n260; side
  | |- sem (ENode 262) _ _ _ => eapply n262; side
  end.
Ltac elem ::= first [elem3 | elem2 | elem1 | elem0].

(* cons() = wim(): (x, r) := unP wffstack; wffstack := r; topwff := wim x topwff *)
Lemma cons208 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 208) m XNormal (set (set m 1 (wim x (get m 1))) 2 r).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem4 := match goal with |- sem (ENode 208) _ _ _ => eapply cons208; side end.
Ltac elem ::= first [elem4 | elem3 | elem2 | elem1 | elem0].

Lemma wel328 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 328) m XNormal (set (set m 1 (wel x (get m 1))) 2 r).
Proof. revert m; start; run_seq; fin. Qed.
Lemma wal327 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 327) m XNormal (set (set m 1 (wal x (get m 1))) 2 r).
Proof. revert m; start; run_seq; fin. Qed.
Lemma weq329 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 329) m XNormal (set (set m 1 (weq x (get m 1))) 2 r).
Proof. revert m; start; run_seq; fin. Qed.
Lemma wn382 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 382) m XNormal (set m 1 (wn (get m 1))).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem5 := match goal with
  | |- sem (ENode 328) _ _ _ => eapply wel328; side
  | |- sem (ENode 327) _ _ _ => eapply wal327; side
  | |- sem (ENode 329) _ _ _ => eapply weq329; side
  | |- sem (ENode 382) _ _ _ => eapply wn382; side
  end.
Ltac elem ::= first [elem5 | elem4 | elem3 | elem2 | elem1 | elem0].

Lemma wex330 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 330) m XNormal (set (set m 1 (wex x (get m 1))) 2 r).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem6 := match goal with
  | |- sem (ENode 330) _ _ _ => eapply wex330; side
  end.
Ltac elem ::= first [elem6 | elem5 | elem4 | elem3 | elem2 | elem1 | elem0].


(* read(r): r += fst (unP prooflist); prooflist := snd (unP prooflist) *)
Lemma read320 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 320) m XNormal (set (set m 3 (get m 3 + fst (unP (get m 8)))) 8 (snd (unP (get m 8)))).
Proof. revert m; start; run_seq; fin. Qed.
Lemma read321 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 321) m XNormal (set (set m 4 (get m 4 + fst (unP (get m 8)))) 8 (snd (unP (get m 8)))).
Proof. revert m; start; run_seq; fin. Qed.
Lemma read322 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 322) m XNormal (set (set m 5 (get m 5 + fst (unP (get m 8)))) 8 (snd (unP (get m 8)))).
Proof. revert m; start; run_seq; fin. Qed.
(* pop(param2): param2 += fst (unP wffstack); wffstack := snd (unP wffstack) *)
Lemma pop316 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 316) m XNormal (set (set m 5 (get m 5 + fst (unP (get m 2)))) 2 (snd (unP (get m 2)))).
Proof. revert m; start; run_seq; fin. Qed.
Ltac elem7 := match goal with
  | |- sem (ENode 320) _ _ _ => eapply read320; side
  | |- sem (ENode 321) _ _ _ => eapply read321; side
  | |- sem (ENode 322) _ _ _ => eapply read322; side
  | |- sem (ENode 316) _ _ _ => eapply pop316; side
  end.
Ltac elem ::= first [elem7 | elem6 | elem5 | elem4 | elem3 | elem2 | elem1 | elem0].

(** ** if_eq(scratch1, param2, body): runs body iff scratch1 = param2; both are zeroed.
    Loop (node 216): {if s1 {s1--; if p2 {p2--; continue} else {while s1 {s1--; p2++}; p2++}}};
    then (node 220) {if p2 {while p2 {p2--}; skip body}}. *)
Definition clr (m : St) : St := set (set m 6 0) 5 0.

Lemma loop216 x : forall m, get m 6 = x ->
  (x <= get m 5 -> sem (ENode 216) m XNormal (set (set m 6 0) 5 (get m 5 - x))) /\
  (get m 5 < x -> sem (ENode 216) m XNormal (set (set m 6 0) 5 (x - get m 5))).
Proof.
  induction x as [|x IH]; intros m Hx; split; intros Hle.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; exact Hx]|].
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
        -- eapply sem_car_break1; [reflexivity|]. apply sem_decnz_zero. destruct m; nrm; exact Hy.
        -- eapply sem_cdr_normal; [reflexivity | apply w365 | apply sem_inc; lia].
      * destruct m; nrm; subst; f_equal; lia.
    + eapply sem_cdr_continue1; [reflexivity | apply sem_decnz_pos; [lia | exact Hx] | |].
      * eapply sem_car_continue with (k := 0); [reflexivity|].
        eapply sem_cdr_continueS with (k := 0); [reflexivity | | apply sem_cont].
        apply sem_decnz_pos with (v := y); [lia | destruct m; nrm; exact Hy].
      * eapply sem_conseq;
          [apply (proj2 (IH (set (set m 6 x) 5 y) ltac:(destruct m; reflexivity))); destruct m; nrm; lia|].
        destruct m; nrm; subst; f_equal; lia.
Qed.

Lemma if215_eq m : get m 6 = get m 5 -> sem (ENode 215) m XNormal (clr m).
Proof.
  intros H. destruct (loop216 (get m 6) m eq_refl) as [H1 _].
  eapply sem_cdr_normal; [reflexivity | apply H1; lia |].
  eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero]|].
  - destruct m; nrm; lia.
  - unfold clr; destruct m; nrm; f_equal; lia.
Qed.

Lemma if215_neq m : get m 6 <> get m 5 -> sem (ENode 215) m (XBreak 1) (clr m).
Proof.
  intros H. destruct (loop216 (get m 6) m eq_refl) as [H1 H2].
  assert (Hl : exists d, sem (ENode 216) m XNormal (set (set m 6 0) 5 (S d))).
  { destruct (Nat.lt_ge_cases (get m 5) (get m 6)) as [Hlt | Hge].
    - exists (get m 6 - get m 5 - 1).
      replace (S (get m 6 - get m 5 - 1)) with (get m 6 - get m 5) by lia. apply H2, Hlt.
    - exists (get m 5 - get m 6 - 1).
      replace (S (get m 5 - get m 6 - 1)) with (get m 5 - get m 6) by lia. apply H1, Hge. }
  destruct Hl as [d Hd].
  eapply sem_cdr_break with (k := 0); [reflexivity | exact Hd |].
  eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos with (v := d);
    [lia | destruct m; reflexivity] |].
  eapply sem_conseq; [eapply sem_cdr_break with (k := 0); [reflexivity | apply w353 | apply sem_breakS]|].
  unfold clr; destruct m; nrm; reflexivity.
Qed.

(* if_eq(scratch1, param2, par1()) *)
Lemma ifeq230 m : get m 7 = 0 -> sem (ENode 230) m XNormal
  (if Nat.eqb (get m 6) (get m 5)
   then set (set (clr m) 2 (P (get m 1) (get m 2))) 1 (get m 4) else clr m).
Proof.
  intros H7. destruct (Nat.eqb_spec (get m 6) (get m 5)) as [H | H].
  - eapply sem_cdr_normal; [reflexivity | apply if215_eq, H |].
    eapply sem_conseq; [apply par312; destruct m; nrm; auto|]. unfold clr; destruct m; reflexivity.
  - eapply sem_car_break1; [reflexivity | apply if215_neq, H].
Qed.

(* if_eq(scratch1, param2, halt) *)
Lemma ifeq231_halt m : get m 6 = get m 5 -> sem (ENode 231) m XHalt (clr m).
Proof.
  intros H. eapply sem_cdr_halt; [reflexivity | apply if215_eq, H | apply sem_halt].
Qed.

Lemma ifeq231_normal m : get m 6 <> get m 5 -> sem (ENode 231) m XNormal (clr m).
Proof. intros H. eapply sem_car_break1; [reflexivity | apply if215_neq, H]. Qed.

Ltac elem8 := match goal with
  | |- sem (ENode 230) _ _ _ => eapply ifeq230; side
  end.
Ltac elem ::= first [elem8 | elem7 | elem6 | elem5 | elem4 | elem3 | elem2 | elem1 | elem0].

(** ** if_not_decnz(prooflist, {prooflist := nextproof; nextproof++}) *)
Lemma ifnot235 m : get m 6 = 0 -> sem (ENode 235) m XNormal
  (set (set m 8 (match get m 8 with 0 => get m 0 | S v => v end))
       0 (match get m 8 with 0 => S (get m 0) | S _ => get m 0 end)).
Proof.
  intros H6. destruct (get m 8) as [|v] eqn:H8.
  - eapply sem_cdr_normal; [reflexivity | eapply sem_car_break1; [reflexivity | apply sem_decnz_zero, H8] |].
    eapply sem_conseq; [eapply sem_cdr_normal; [reflexivity | apply w344 |
      eapply sem_cdr_normal; [reflexivity | apply w362 | apply sem_inc; lia]]|].
    destruct m; nrm; subst; f_equal; lia.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity|] |].
    + eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos; [lia | exact H8] | apply sem_breakS].
    + destruct m; nrm; subst; reflexivity.
Qed.
