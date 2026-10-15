(** Local adaptation of Jeffrey's root transport in ZF/m254,
    external proof pin c132d7eae8158cd3a9850ea3eb7251158c3dd821.
    The original explanatory header is retained below. The helper graph is
    the exact PA238 source DAG; AX evaluation below uses the PA rows/bundle.
    The register relation allows arbitrary non-source registers. *)

(** * L2Root254: one structured run of the root of [dag254] (Dag254.v) is one [Enum254.enum_step].

    Boundary register files: scratch1 = scratch2 = axiomcode = 0, the other six registers hold the
    enumerator state ([enc]).  From [enc s] the root halts iff [enum_step s = None], and otherwise
    ends in [enc s'] where [enum_step s = Some s'].  Iterating gives [iter_halts_dag]:
    [iter_halts dag254 (regs of s) <-> some state reachable from s makes a halting step]. *)

From Coq Require Import Lists.List Arith.Arith Lia Bool.Bool.
From P238.tm Require Import RM238.
From P238.prog Require Import Dag238 ProgLib238.
From P238.logic Require Import Codes238 Compiler238 Candidate238 Enum238.
Import ListNotations.

Opaque P.
Ltac nrm ::= cbn [get set inc ustep unpair_post clr] in *.

(** Registers: 0 nextproof, 1 topwff, 2 wffstack, 3 axiomcode, 4 param1, 5 param2, 6 scratch1,
    7 scratch2, 8 prooflist. *)
Definition state := enum_state.
Definition pl := enum_pending.
Definition np := enum_next.
Definition tw (s : state) := let '(t, _, _, _) := enum_registers s in t.
Definition ws (s : state) := let '(_, w, _, _) := enum_registers s in w.
Definition d (s : state) := let '(_, _, d, _) := enum_registers s in d.
Definition h (s : state) := let '(_, _, _, h) := enum_registers s in h.

Definition enc (s : state) : St := mkSt (np s) (tw s) (ws s) 0 (d s) (h s) 0 0 (pl s).

(** ** The four commands (from a clean register file, after the selector has been consumed) *)
(* mp() = [par1; wim; topwff -> scratch1; if_eq(scratch1, param2, par1)] *)
Lemma mp122 m : get m 6 = 0 -> get m 7 = 0 -> sem (ENode 122) m XNormal
  (if Nat.eqb (wim (get m 1) (get m 4)) (get m 5)
   then set (set (set m 1 (get m 4)) 2 (P 0 (get m 2))) 5 0
   else set (set m 1 0) 5 0).
Proof.
  revert m; start; run_seq. apply sx_nil_eq. rewrite Nat.add_0_l.
  destruct (Nat.eqb _ _); reflexivity.
Qed.

(* nip() = [scratch1++; if_eq(scratch1, param2, halt); pop(param2)] *)
Lemma nip124_halt m : get m 6 = 0 -> get m 5 = 1 -> exists m', sem (ENode 124) m XHalt m'.
Proof.
  intros H6 H5. eexists. eapply sem_cdr_halt; [reflexivity | apply sem_inc; lia |].
  eapply sem_car_halt; [reflexivity|]. apply ifeq104_halt. destruct m; nrm; congruence.
Qed.

Lemma nip124 m : get m 6 = 0 -> get m 7 = 0 -> get m 5 <> 1 -> sem (ENode 124) m XNormal
  (set (set m 5 (fst (unP (get m 2)))) 2 (snd (unP (get m 2)))).
Proof.
  intros H6 H7 H5. eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia |].
  eapply sem_cdr_normal; [reflexivity | apply ifeq104_normal; destruct m; nrm; congruence |].
  eapply sem_conseq; [apply pop142; destruct m; nrm; auto|]. destruct m; nrm; subst; reflexivity.
Qed.

(* axioms(): the long straight-line block; the stack after it and the gated bundle *)
Lemma ax1 m y pl4 u pl5 : get m 6 = 0 -> get m 7 = 0 -> unP (get m 8) = (y, pl4) -> unP pl4 = (u, pl5) ->
  sem (ENode 1) m XNormal
    (mkSt (get m 0) (gate (get m 4) (get m 5 + y) (get m 3))
          (ax_stack (get m 4) (get m 5) (get m 5 + y) (get m 3) u (get m 1) (get m 2))
          0 0 0 0 0 pl5).
Proof.
  revert m; start. run_seq.
  apply sx_nil_eq. rewrite ?H1. cbn [fst snd]. rewrite ?H2. cbn [fst snd]. rewrite ?Nat.add_0_l, ?Nat.add_0_r.
  unfold gate. f_equal.
  destruct (Nat.eqb _ (_ + y)), (Nat.eqb _ _); cbn [orb]; reflexivity.
Qed.

(** ** dispatch (node 141): selector 0 MP, 1 DROP, 2 NIP, 3 + c AX (axiomcode = c) *)
Lemma disp_mp m : get m 3 = 0 -> get m 6 = 0 -> get m 7 = 0 -> forall m', sem (ENode 122) m XNormal m' ->
  sem (ENode 113) m XNormal m'.
Proof.
  intros H3 H6 H7 m' H. eapply sem_cdr_normal; [reflexivity | | exact H].
  eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; [lia|exact H3]].
Qed.

(* selector >= 1: decrement, run the rest of the dispatch, break out of the switch *)
Lemma disp_1 m v x m' : get m 3 = S v -> sem (ENode 116) (set m 3 v) x m' ->
  (x = XNormal \/ x = XHalt) -> sem (ENode 113) m x m'.
Proof.
  intros H3 H [-> | ->].
  - eapply sem_car_break1; [reflexivity|].
    eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos; [lia | exact H3] |].
    eapply sem_cdr_break with (k := 0); [reflexivity | exact H | apply sem_breakS].
  - eapply sem_car_halt; [reflexivity|].
    eapply sem_cdr_halt; [reflexivity | apply sem_decnz_pos; [lia | exact H3] |].
    eapply sem_car_halt; [reflexivity | exact H].
Qed.

Lemma disp_drop m : get m 3 = 0 -> forall m', sem (ENode 93) m XNormal m' -> sem (ENode 116) m XNormal m'.
Proof.
  intros H3 m' H. eapply sem_cdr_normal; [reflexivity | | exact H].
  eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; [lia|exact H3]].
Qed.

Lemma disp_2 m v x m' : get m 3 = S v -> sem (ENode 119) (set m 3 v) x m' ->
  (x = XNormal \/ x = XHalt) -> sem (ENode 116) m x m'.
Proof.
  intros H3 H [-> | ->].
  - eapply sem_car_break1; [reflexivity|].
    eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos; [lia | exact H3] |].
    eapply sem_cdr_break with (k := 0); [reflexivity | exact H | apply sem_breakS].
  - eapply sem_car_halt; [reflexivity|].
    eapply sem_cdr_halt; [reflexivity | apply sem_decnz_pos; [lia | exact H3] |].
    eapply sem_car_halt; [reflexivity | exact H].
Qed.

Lemma disp_nip m x m' : get m 3 = 0 -> sem (ENode 124) m x m' -> (x = XNormal \/ x = XHalt) ->
  sem (ENode 119) m x m'.
Proof.
  intros H3 H [-> | ->].
  - eapply sem_cdr_normal; [reflexivity | | exact H].
    eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; [lia|exact H3]].
  - eapply sem_cdr_halt; [reflexivity | | exact H].
    eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; [lia|exact H3]].
Qed.

Lemma disp_ax m v m' : get m 3 = S v -> sem (ENode 1) (set m 3 v) XNormal m' -> sem (ENode 119) m XNormal m'.
Proof.
  intros H3 H. eapply sem_car_break1; [reflexivity|].
  eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos; [lia | exact H3] |].
  eapply sem_cdr_break with (k := 0); [reflexivity | exact H | apply sem_breakS].
Qed.

Ltac elem9 := match goal with |- sem (ENode 105) _ _ _ => eapply ifnot105; side end.
Ltac elem ::= first [elem9 | elem8 | elem7 | elem6 | elem5 | elem4 | elem3 | elem2 | elem1 | elem0].

(** ** The prefix of main(): fetch the next command and read selector and param1. *)
Lemma prefix_ok s pl1 np1 ac pl2 x pl3 :
  (if Nat.eqb (pl s) 0 then (np s, S (np s)) else (pred (pl s), np s)) = (pl1, np1) ->
  unP pl1 = (ac, pl2) -> unP pl2 = (x, pl3) ->
  seqx [ENode 105; ENode 146; ENode 147] (enc s) XNormal (mkSt np1 (tw s) (ws s) ac (d s + x) (h s) 0 0 pl3).
Proof.
  intros Hp E1 E2. destruct s as [pending next [[[t w] offset] cache]]. unfold enc.
  cbn [pl np tw ws d h enum_pending enum_next enum_registers] in *.
  destruct pending as [|v]; injection Hp as <- <-; repeat step; apply sx_nil_eq;
    rewrite ?E1; cbn [fst snd]; rewrite ?E2; cbn [fst snd]; reflexivity.
Qed.

Lemma main_flat : expand 200 (fst (dag_nodes 0)) ++ expand 200 (snd (dag_nodes 0)) =
  [ENode 105; ENode 146; ENode 147; ENode 113].
Proof. vm_compute. reflexivity. Qed.

Lemma root_of m x m' : seqx [ENode 105; ENode 146; ENode 147] m XNormal m' ->
  forall m'', sem (ENode 113) m' x m'' -> (x = XNormal \/ x = XHalt) -> sem (ENode 0) m x m''.
Proof.
  intros H1 m'' H2 Hx. apply seq_node. rewrite main_flat.
  change [ENode 105; ENode 146; ENode 147; ENode 113] with ([ENode 105; ENode 146; ENode 147] ++ [ENode 113]).
  eapply seqx_app; [exact H1|]. destruct Hx as [-> | ->].
  - eapply sx_normal; [exact H2 | constructor].
  - apply sx_halt, H2.
Qed.

(** A raw source-facing normal form of the accepted numeric decoder. The
    extra offset in DROP/NIP is retained. MP/AX absorb their second field
    in their instruction, while the source has already added it to param1. *)
Definition source_enum_step (s : state) : option state :=
  let '(pl1, np1) := if Nat.eqb (pl s) 0
                     then (np s, S (np s)) else (pred (pl s), np s) in
  let '(ac, pl2) := unP pl1 in
  let '(x, pl3) := unP pl2 in
  match ac with
  | 0 => Some (EnumState pl3 np1
      (if Nat.eqb (wim (tw s) (d s + x)) (h s)
       then (d s + x, P 0 (ws s), d s + x, 0)
       else (0, ws s, d s + x, 0)))
  | 1 => Some (EnumState pl3 np1 (h s, P (tw s) (ws s), d s + x, h s))
  | 2 => if Nat.eqb (h s) 1 then None else
      Some (EnumState pl3 np1 (tw s, snd (unP (ws s)), d s + x, fst (unP (ws s))))
  | S (S (S c)) =>
      let '(y, pl4) := unP pl3 in
      let '(u, pl5) := unP pl4 in
      Some (EnumState pl5 np1
        (gate (d s + x) (h s + y) c,
         ax_stack (d s + x) (h s) (h s + y) c u (tw s) (ws s), 0, 0))
  end.

Lemma enum_step_source s : enum_step s = source_enum_step s.
Proof.
  destruct s as [pending next [[[t w] offset] cache]].
  unfold enum_step, source_enum_step, decode_fields;
    cbn [pl np tw ws d h enum_pending enum_next enum_registers].
  destruct pending as [|pending]; cbn [Nat.eqb Nat.pred];
    [destruct (unP next) as [ac pl2]|destruct (unP pending) as [ac pl2]];
    destruct (unP pl2) as [x pl3];
    destruct ac as [|[|[|c]]]; cbn [add_offset command_step];
    rewrite ?Nat.add_0_r; try reflexivity.
  all: try (destruct (Nat.eqb (wim t (offset + x)) cache); reflexivity).
  all: try (destruct (Nat.eqb cache 1); reflexivity).
  all: destruct (unP pl3) as [y pl4]; destruct (unP pl4) as [u pl5];
    cbn [add_offset command_step]; rewrite ?Nat.add_0_r; reflexivity.
Qed.

(** ** One iteration of main() on abstract register files. *)
Theorem root_sem s :
  (enum_step s = None -> exists m', sem (ENode 0) (enc s) XHalt m') /\
  (forall s', enum_step s = Some s' -> sem (ENode 0) (enc s) XNormal (enc s')).
Proof.
  rewrite !enum_step_source; unfold source_enum_step.
  destruct (if Nat.eqb (pl s) 0 then (np s, S (np s)) else (pred (pl s), np s)) as [pl1 np1] eqn:Hp.
  destruct (unP pl1) as [ac pl2] eqn:E1. destruct (unP pl2) as [x pl3] eqn:E2.
  pose proof (prefix_ok s _ _ _ _ _ _ Hp E1 E2) as Hpre.
  set (m := mkSt np1 (tw s) (ws s) ac (d s + x) (h s) 0 0 pl3) in Hpre.
  destruct ac as [|[|[|c]]].
  - (* MP *)
    split; [discriminate|]. intros s' Hs. injection Hs as <-.
    apply (root_of _ _ _ Hpre); [|now left].
    apply disp_mp; [reflexivity .. |].
    eapply sem_conseq; [apply mp122; reflexivity|]. subst m. cbn [get set].
    unfold enc; cbn [pl np tw ws d h enum_pending enum_next enum_registers]. destruct (Nat.eqb (wim (tw s) (d s + x)) (h s)); reflexivity.
  - (* DROP *)
    split; [discriminate|]. intros s' Hs. injection Hs as <-.
    apply (root_of _ _ _ Hpre); [|now left].
    apply (disp_1 _ 0); [reflexivity | | now left].
    apply disp_drop; [reflexivity|].
    eapply sem_conseq; [apply par93; reflexivity|]. reflexivity.
  - (* NIP *)
    split.
    + intros Hn. destruct (Nat.eqb_spec (h s) 1) as [H1 | H1]; [|destruct (unP (ws s)); discriminate].
      destruct (nip124_halt (set (set m 3 1) 3 0) eq_refl H1) as [m' Hm'].
      exists m'. apply (root_of _ _ _ Hpre); [|now right].
      apply (disp_1 _ 1); [reflexivity | | now right].
      apply (disp_2 _ 0); [reflexivity | | now right].
      apply disp_nip; [reflexivity | exact Hm' | now right].
    + intros s' Hs. destruct (Nat.eqb_spec (h s) 1) as [H1 | H1]; [discriminate|].
      destruct (unP (ws s)) as [h1 w1] eqn:Ew. injection Hs as <-.
      apply (root_of _ _ _ Hpre); [|now left].
      apply (disp_1 _ 1); [reflexivity | | now left].
      apply (disp_2 _ 0); [reflexivity | | now left].
      apply disp_nip; [reflexivity | | now left].
      eapply sem_conseq; [apply nip124; [reflexivity | reflexivity | exact H1]|].
      subst m. cbn [get set]. rewrite Ew. reflexivity.
  - (* AX *)
    split; [intros Hn; destruct (unP pl3) as [y pl4]; destruct (unP pl4); discriminate|].
    intros s' Hs. destruct (unP pl3) as [y pl4] eqn:E3. destruct (unP pl4) as [u pl5] eqn:E4.
    injection Hs as <-.
    apply (root_of _ _ _ Hpre); [|now left].
    apply (disp_1 _ (S (S c))); [reflexivity | | now left].
    apply (disp_2 _ (S c)); [reflexivity | | now left].
    apply (disp_ax _ c); [reflexivity|].
    eapply sem_conseq; [apply (ax1 _ y pl4 u pl5); [reflexivity | reflexivity | exact E3 | exact E4]|].
    reflexivity.
Qed.

(** ** The theorems on the register machine. *)
Theorem root_step_gen s R : approx R (enc s) ->
  (enum_step s = None -> exists R', RM238.run dag238 (ENode 0) R XHalt R') /\
  (forall s', enum_step s = Some s' -> exists R', RM238.run dag238 (ENode 0) R XNormal R' /\ approx R' (enc s')).
Proof.
  intros HR. destruct (root_sem s) as [Hh Hn]. split.
  - intros H. destruct (Hh H) as [m' Hm]. destruct (Hm R HR) as (R' & Hr & _). eauto.
  - intros s' H. destruct (Hn s' H R HR) as (R' & Hr & HR'). eauto.
Qed.

Theorem root_step_det s R x R' : approx R (enc s) -> RM238.run dag238 (ENode 0) R x R' ->
  (x = XHalt /\ enum_step s = None) \/
  (exists s', x = XNormal /\ enum_step s = Some s' /\ approx R' (enc s')).
Proof.
  intros HR Hr. destruct (root_step_gen s R HR) as [Hh Hn].
  destruct (enum_step s) as [s'|] eqn:Es.
  - right. destruct (Hn s' eq_refl) as (R2 & Hr2 & HR2).
    destruct (run_det _ _ _ _ _ Hr _ _ Hr2) as [-> ->]. eauto.
  - left. destruct (Hh eq_refl) as [R2 Hr2]. destruct (run_det _ _ _ _ _ Hr _ _ Hr2) as [-> _]. auto.
Qed.

(* some state reachable from [s] makes a halting step *)
Definition halts_from (s : state) : Prop := exists n s', enum_run n s = Some s' /\ enum_step s' = None.

Theorem iter_halts_dag s R : approx R (enc s) -> iter_halts dag238 R <-> halts_from s.
Proof.
  intros HR. split.
  - intros H. revert s HR. induction H as [R R' Hr | R R' Hr H IH]; intros s HR.
    + destruct (root_step_det s R _ R' HR Hr) as [[_ Hs] | (s' & ? & _)]; [|discriminate].
      exists 0, s. auto.
    + destruct (root_step_det s R _ R' HR Hr) as [[? _] | (s' & _ & Es & HR')]; [discriminate|].
      destruct (IH s' HR') as (n & s'' & Hrun & Hs). exists (S n), s''. cbn [enum_run]. rewrite Es. auto.
  - intros (n & s' & Hrun & Hs). revert s R HR Hrun. induction n as [|n IH]; intros s R HR Hrun.
    + injection Hrun as <-. destruct (root_step_gen s R HR) as [Hh _]. destruct (Hh Hs) as [R' Hr].
      exact (iter_halt _ R R' Hr).
    + cbn [enum_run] in Hrun. destruct (enum_step s) as [s1|] eqn:Es; [|discriminate].
      destruct (root_step_gen s R HR) as [_ Hn]. destruct (Hn s1 Es) as (R' & Hr & HR').
      apply (iter_next _ R R' Hr). exact (IH s1 R' HR' Hrun).
Qed.

(** The accepted enumerator endpoint observes [None] at any finite fuel.
    The structured transport above observes the last command boundary.
    This elementary finite-run lemma identifies those observations. *)
Lemma halts_from_enum_run s : halts_from s <-> exists fuel, enum_run fuel s = None.
Proof.
  split.
  - intros (n & s' & Hr & Hs). exists (n + 1).
    rewrite enum_run_append, Hr. cbn [enum_run]. rewrite Hs; reflexivity.
  - intros [fuel Hr]. revert s Hr.
    induction fuel as [|fuel IH]; intros s Hr; [discriminate|].
    cbn [enum_run] in Hr. destruct (enum_step s) as [s'|] eqn:Es.
    + destruct (IH s' Hr) as (n & s'' & Hrun & Hhalt).
      exists (S n), s''; split; [cbn [enum_run]; now rewrite Es|exact Hhalt].
    + exists 0, s; split; [reflexivity|exact Es].
Qed.

Theorem iter_halts_enum s R : approx R (enc s) ->
  iter_halts dag238 R <-> exists fuel, enum_run fuel s = None.
Proof. intro HR; rewrite (iter_halts_dag s R HR); apply halts_from_enum_run. Qed.

(** Source registers at the concrete command checkpoint. Spare registers
    are unrestricted because [approx] only relates indices zero to eight. *)
Definition source_boot238 : St := mkSt 6 0 0 0 2 0 0 0 0.
Lemma enc_enum_boot238 : enc enum_boot = source_boot238.
Proof. reflexivity. Qed.

Corollary iter_halts_dag_boot238 R : approx R source_boot238 ->
  iter_halts dag238 R <-> enum238_boot_halts.
Proof.
  intro HR; change (iter_halts dag238 R <-> exists fuel, enum_run fuel enum_boot = None).
  apply iter_halts_enum. rewrite enc_enum_boot238; exact HR.
Qed.

Print Assumptions root_sem.
Print Assumptions iter_halts_dag.
Print Assumptions iter_halts_dag_boot238.
