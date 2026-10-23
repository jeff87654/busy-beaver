(** * Sim.v : the auxiliary 11-state machine X3 simulates the 9-state machine h003 (BB9/verify_h003; port of ../verify_c7/c7/Sim.v).

    h003 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC        (H3.Defs.tmh, over BB92)
    X3 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LJ0LC_0RG1LD_0LH1LH_1RI---_0RI0RF_0LK---_1RK1RC   (XDev.Base.tm, over BB112)

    State map stmap : A..F -> A..F, G -> I, H -> J, I -> K; symbols S0 -> S0, S1 -> S1.  Every h003 step is matched by
    one X3 step, except h003's F0 = 1RG, which X3 does in three steps (F0 = 0RG, G = 0LH/1LH writes back what it reads,
    H0 = 1RI).  X3 state H is entered only from G and then reads 0, so [Rel] is the direct relation: same finite tape
    lists, state mapped by stmap (unlike f3, no alternative branch and no invariant on I's right neighbour: h003's
    I = 1RI 1RC is X3 K = 1RK 1RC exactly).  h003 halts exactly where X3 does (h003 at H1, X3 at J1).

    Nothing here depends on a proof that X3 halts: the transfer theorems take X3 facts as hypotheses
    (h003_halts_of_x, x_to_h003), or need none at all (h003_to_x, x_halts_of_h003, which run the simulation forward). *)
From BB8 Require Individual92.
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Base Ones.
From H3 Require Defs.

Module T3 := Individual92.Individual92.Permute.Flip.Compute.TM.

Definition stmap (q : BB92.state) : state :=
  match q with
  | BB92.A => A | BB92.B => B | BB92.C => C | BB92.D => D
  | BB92.E => E | BB92.F => F | BB92.G => I | BB92.H => J | BB92.I => K
  end.

Definition symmap (s : BB92.sym) : sym :=
  match s with
  | BB92.S0 => S0
  | BB92.S1 => S1
  end.

Definition cfgh : Type := (BB92.state * (Stream BB92.sym * BB92.sym * Stream BB92.sym))%type.

Definition Rel (c7 : cfgh) (cx : Q * tape) : Prop :=
  exists q (Ll : list BB92.sym) s (Rr : list BB92.sym),
    c7 = (q, (Ll *> const BB92.S0, s, Rr *> const BB92.S0)) /\
    cx = (stmap q, (map symmap Ll *> const S0, symmap s, map symmap Rr *> const S0)).

Ltac reify t :=
  lazymatch t with
  | Streams.Cons ?x ?t' => let L := reify t' in constr:(x :: L)
  | ?L *> const _ => L
  | const _ => constr:(@nil BB92.sym)
  end.

Ltac solve_rel :=
  lazymatch goal with
  | |- Rel (?q, (?l, ?s, ?r)) _ =>
    let Ll := reify l in let Rr := reify r in
    exists q, Ll, s, Rr; split; reflexivity
  end.

Ltac run_steps := repeat (eapply multistep_S; [prove_step |]); apply multistep_0.

Lemma sim_step : forall (c7 c7' : cfgh) cx, T3.step Defs.tmh c7 c7' -> Rel c7 cx ->
  exists k cx', cx -[ Base.tm ]->> S k / cx' /\ Rel c7' cx'.
Proof.
  intros c7 c7' cx Hs [q [Ll [s [Rr [E7 Ex]]]]]. subst c7 cx.
  inversion Hs as [q1 q' s1 s' l r Ht | q1 q' s1 s' l r Ht]; subst; clear Hs;
  destruct q, s; cbn in Ht; inversion Ht; subst; clear Ht;
  (destruct Ll as [| x Ll]; [| destruct x]); (destruct Rr as [| y Rr]; [| destruct y]);
  cbn [T3.move_left T3.move_right Streams.hd Streams.tl Str_app List.map stmap symmap Streams.const];
  first [ exists 0%nat; eexists; split; [run_steps | solve_rel]
        | exists 2%nat; eexists; split; [run_steps | solve_rel] ].
Qed.

(** ** Halting corresponds *)
Lemma halted_rel : forall c7 cx, Rel c7 cx -> (T3.halted Defs.tmh c7 <-> halted Base.tm cx).
Proof.
  intros c7 cx [q [Ll [s [Rr [E7 Ex]]]]]; subst c7 cx.
  destruct q, s; cbn; split; intro Hh; (reflexivity || discriminate).
Qed.

Lemma rel_c0 : Rel T3.c0 c0.
Proof. exists BB92.A, (@nil BB92.sym), BB92.S0, (@nil BB92.sym). split; reflexivity. Qed.

(** ** Determinism on the X3 side *)
Lemma ms_det : forall m c c', c -[ Base.tm ]->> m / c' -> forall n ch, c -[ Base.tm ]->> n / ch -> halted Base.tm ch ->
  m <= n /\ c' -[ Base.tm ]->> (n - m) / ch.
Proof.
  induction 1 as [c | m c c1 c' Hs Hm IH]; intros n ch Hn Hh.
  - split; [lia | rewrite Nat.sub_0_r; exact Hn].
  - inversion Hn as [c2 | n' c2 c3 c4 Hs' Hn']; subst.
    + exfalso. exact (halted_no_step _ _ _ Hh Hs).
    + pose proof (step_deterministic _ _ _ _ Hs Hs') as E. subst c3.
      destruct (IH _ _ Hn' Hh) as [Hle Hr]. split; [lia | exact Hr].
Qed.

Lemma ms_halted : forall n c ch, halted Base.tm c -> c -[ Base.tm ]->> n / ch -> c = ch.
Proof.
  intros n c ch Hh Hn. inversion Hn as [c2 | n' c2 c3 c4 Hs' Hn']; subst; [reflexivity |].
  exfalso. exact (halted_no_step _ _ _ Hh Hs').
Qed.

Lemma ms_evstep : forall n c c', c -[ Base.tm ]->> n / c' -> c -[ Base.tm ]->* c'.
Proof. intros n c c' H. induction H as [c | n c c' c'' Hs _ IH]; [apply evstep_refl | eapply evstep_step; eassumption]. Qed.

Lemma evstep_ms : forall c c', c -[ Base.tm ]->* c' -> exists n, c -[ Base.tm ]->> n / c'.
Proof.
  intros c c' H. induction H as [c | c c' c'' Hs _ [n IH]].
  - exists 0%nat. apply multistep_0.
  - exists (S n). eapply multistep_S; eassumption.
Qed.

(** ** The same two conversions on the h003 side *)
Lemma ms_evstep7 : forall n (c c' : cfgh), T3.multistep Defs.tmh n c c' -> T3.evstep Defs.tmh c c'.
Proof.
  intros n c c' H. induction H as [c | n c c' c'' Hs _ IH]; [apply T3.evstep_refl | eapply T3.evstep_step; eassumption].
Qed.

Lemma evstep_ms7 : forall (c c' : cfgh), T3.evstep Defs.tmh c c' -> exists n, T3.multistep Defs.tmh n c c'.
Proof.
  intros c c' H. induction H as [c | c c' c'' Hs _ [n IH]].
  - exists 0%nat. apply T3.multistep_0.
  - exists (S n). eapply T3.multistep_S; eassumption.
Qed.

(** ** The simulation run, backward: if X3 halts from a related configuration, so does h003, at a related configuration *)
Lemma sim_run : forall n (c7 : cfgh) cx ch, Rel c7 cx -> cx -[ Base.tm ]->> n / ch -> halted Base.tm ch ->
  exists c7h, T3.evstep Defs.tmh c7 c7h /\ T3.halted Defs.tmh c7h /\ Rel c7h ch.
Proof.
  induction n as [n IH] using lt_wf_ind. intros c7 cx ch HR Hn Hh.
  destruct c7 as [q [[l s] r]] eqn:Ec7.
  pose (o := Defs.tmh (q, s)). assert (Et : Defs.tmh (q, s) = o) by reflexivity. clearbody o. destruct o as [t |].
  - rewrite <- Ec7 in HR.
    assert (Hnh : ~ T3.halted Defs.tmh c7) by (subst c7; intro H7; change (Defs.tmh (q, s) = None) in H7; congruence).
    destruct (T3.no_halted_step _ _ Hnh) as [c7' Hs].
    destruct (sim_step c7 c7' cx Hs HR) as [k [cx' [Hk HR']]].
    destruct (ms_det _ _ _ Hk n ch Hn Hh) as [Hle Hrest].
    destruct (IH (n - S k) ltac:(lia) c7' cx' ch HR' Hrest Hh) as [c7h [H1 [H2 H3]]].
    exists c7h. split; [| split; assumption]. rewrite <- Ec7. eapply T3.evstep_step; eassumption.
  - rewrite <- Ec7 in HR |- *.
    assert (H7 : T3.halted Defs.tmh c7) by (subst c7; change (Defs.tmh (q, s) = None); exact Et).
    pose proof (proj1 (halted_rel c7 cx HR) H7) as Hx.
    pose proof (ms_halted n cx ch Hx Hn) as E. subst ch.
    exists c7. split; [apply T3.evstep_refl | split; assumption].
Qed.

(** ** The simulation run, forward: every h003 run is matched by an X3 run between related configurations *)
Lemma sim_ev : forall (c7 c7' : cfgh), T3.evstep Defs.tmh c7 c7' -> forall cx, Rel c7 cx ->
  exists cx', cx -[ Base.tm ]->* cx' /\ Rel c7' cx'.
Proof.
  induction 1 as [c | c c' c'' Hs _ IH]; intros cx HR.
  - exists cx. split; [apply evstep_refl | exact HR].
  - destruct (sim_step c c' cx Hs HR) as [k [cx1 [Hk HR1]]].
    destruct (IH cx1 HR1) as [cx' [H1 H2]].
    exists cx'. split; [eapply evstep_trans; [exact (ms_evstep _ _ _ Hk) | exact H1] | exact H2].
Qed.

(** ** If X3 halts, h003 halts, at a configuration related to X3's halting configuration *)
Theorem h003_reach_of_x : halts Base.tm c0 ->
  exists (c7h : cfgh) ch, T3.evstep Defs.tmh T3.c0 c7h /\ T3.halted Defs.tmh c7h /\ Rel c7h ch /\
  c0 -[ Base.tm ]->* ch /\ halted Base.tm ch.
Proof.
  intros [n [ch [Hn Hh]]].
  destruct (sim_run n T3.c0 c0 ch rel_c0 Hn Hh) as [c7h [H1 [H2 H3]]].
  exists c7h, ch. split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact (ms_evstep _ _ _ Hn) | exact Hh]]]].
Qed.

Theorem h003_halts_of_x : halts Base.tm c0 -> T3.halts Defs.tmh T3.c0.
Proof.
  intro HX. destruct (h003_reach_of_x HX) as [c7h [ch [H1 [H2 _]]]].
  destruct (evstep_ms7 _ _ H1) as [n Hn]. exists n, c7h. split; assumption.
Qed.

Theorem x_halts_of_h003 : T3.halts Defs.tmh T3.c0 -> halts Base.tm c0.
Proof.
  intros [n [c [Hn Hh]]].
  destruct (sim_ev _ _ (ms_evstep7 _ _ _ Hn) c0 rel_c0) as [cx [H1 HR]].
  destruct (evstep_ms _ _ H1) as [m Hm]. exists m, cx. split; [exact Hm | exact (proj1 (halted_rel _ _ HR) Hh)].
Qed.

(** ** Generic facts about 9-state runs *)
Theorem halted_unique7 : forall (tm : T3.TM) c c1 c2, T3.evstep tm c c1 -> T3.evstep tm c c2 ->
  T3.halted tm c1 -> T3.halted tm c2 -> c1 = c2.
Proof.
  intros tm c c1 c2 H1. revert c2. induction H1 as [c | c c' c1 Hs H1 IH]; intros c2 H2 Hh1 Hh2.
  - inversion H2 as [| ? c'' ? Hs' H2']; subst; [reflexivity |].
    exfalso. exact (T3.halted_no_step _ _ _ Hh1 Hs').
  - inversion H2 as [| ? c'' ? Hs' H2']; subst.
    + exfalso. exact (T3.halted_no_step _ _ _ Hh2 Hs).
    + pose proof (T3.step_deterministic _ _ _ _ Hs Hs') as E. subst c''. apply IH; assumption.
Qed.

Lemma zeros_count7 : forall L : list BB92.sym, const BB92.S0 = L *> const BB92.S0 -> Defs.count1 L = 0%nat.
Proof.
  induction L as [| a L IH]; intro H; [reflexivity |].
  cbn [Str_app] in H.
  pose proof (f_equal (@Streams.hd BB92.sym) H) as Ha. pose proof (f_equal (@Streams.tl BB92.sym) H) as Ht.
  cbn in Ha, Ht. subst a.
  cbn [Defs.count1 Defs.sym_val]. apply IH. exact Ht.
Qed.

Lemma side_count7 : forall L1 L2 : list BB92.sym, L1 *> const BB92.S0 = L2 *> const BB92.S0 ->
  Defs.count1 L1 = Defs.count1 L2.
Proof.
  induction L1 as [| a L1 IH]; intros L2 H.
  - symmetry. exact (zeros_count7 L2 H).
  - destruct L2 as [| b L2].
    + symmetry in H. exact (zeros_count7 (a :: L1) H).
    + cbn [Str_app] in H. injection H as Hab Ht. subst b. cbn [Defs.count1]. rewrite (IH L2 Ht). reflexivity.
Qed.

(** ** Ones counts transfer both ways *)
Lemma count_map : forall L, Ones.count1 (map symmap L) = Defs.count1 L.
Proof. induction L as [| a L IH]; [reflexivity |]. destruct a; cbn [map Ones.count1 Defs.count1]; rewrite IH; reflexivity. Qed.

Lemma val_map : forall s, Ones.sym_val (symmap s) = Defs.sym_val s.
Proof. destruct s; reflexivity. Qed.

Lemma zeros_countx : forall L : list Sym, const S0 = L *> const S0 -> Ones.count1 L = 0%nat.
Proof.
  induction L as [| a L IH]; intro H; [reflexivity |].
  cbn [Str_app] in H.
  pose proof (f_equal (@Streams.hd Sym) H) as Ha. pose proof (f_equal (@Streams.tl Sym) H) as Ht. cbn in Ha, Ht. subst a.
  cbn [Ones.count1 Ones.sym_val]. apply IH. exact Ht.
Qed.

Lemma side_countx : forall L1 L2 : list Sym, L1 *> const S0 = L2 *> const S0 -> Ones.count1 L1 = Ones.count1 L2.
Proof.
  induction L1 as [| a L1 IH]; intros L2 H.
  - symmetry. exact (zeros_countx L2 H).
  - destruct L2 as [| b L2].
    + symmetry in H. exact (zeros_countx (a :: L1) H).
    + cbn [Str_app] in H. injection H as Hab Ht. subst b. cbn [Ones.count1]. rewrite (IH L2 Ht). reflexivity.
Qed.

Theorem halted_uniquex : forall c c1 c2, c -[ Base.tm ]->* c1 -> c -[ Base.tm ]->* c2 ->
  halted Base.tm c1 -> halted Base.tm c2 -> c1 = c2.
Proof.
  intros c c1 c2 H1. revert c2. induction H1 as [c | c c' c1 Hs H1 IH]; intros c2 H2 Hh1 Hh2.
  - inversion H2 as [| ? c'' ? Hs' H2']; subst; [reflexivity |].
    exfalso. exact (halted_no_step _ _ _ Hh1 Hs').
  - inversion H2 as [| ? c'' ? Hs' H2']; subst.
    + exfalso. exact (halted_no_step _ _ _ Hh2 Hs).
    + pose proof (step_deterministic _ _ _ _ Hs Hs') as E. subst c''. apply IH; assumption.
Qed.

Lemma rel_ones : forall c7 cx N, Rel c7 cx -> Defs.ones c7 N -> Ones.ones cx N.
Proof.
  intros c7 cx N [q [Ll [s [Rr [E7 Ex]]]]] [q1 [L1 [R1 [s1 [E1 EN]]]]].
  rewrite E7 in E1. injection E1 as Eq EL Es ER. subst q1 s1 cx.
  exists (stmap q), (map symmap Ll), (map symmap Rr), (symmap s). split; [reflexivity |].
  rewrite EN, !count_map, val_map, (side_count7 Ll L1 EL), (side_count7 Rr R1 ER). reflexivity.
Qed.

Lemma ones_rel : forall c7 cx N, Rel c7 cx -> Ones.ones cx N -> Defs.ones c7 N.
Proof.
  intros c7 cx N [q [Ll [s [Rr [E7 Ex]]]]] [q1 [L1 [R1 [s1 [E1 EN]]]]].
  subst c7. exists q, Ll, Rr, s. split; [reflexivity |].
  rewrite Ex in E1; injection E1 as Eq1 EL Es1 ER; subst.
  rewrite <- (side_countx _ _ EL), <- (side_countx _ _ ER), !count_map, val_map. reflexivity.
Qed.

(** ** Every halting count of h003 is a halting count of X3, and conversely (no hypothesis needed) *)
Theorem h003_to_x : forall (c : cfgh) N, T3.evstep Defs.tmh T3.c0 c -> T3.halted Defs.tmh c -> Defs.ones c N ->
  exists cx, c0 -[ Base.tm ]->* cx /\ halted Base.tm cx /\ Ones.ones cx N.
Proof.
  intros c N Hr Hh Ho.
  destruct (sim_ev _ _ Hr c0 rel_c0) as [cx [H1 HR]].
  exists cx. split; [exact H1 | split; [exact (proj1 (halted_rel _ _ HR) Hh) | exact (rel_ones c cx N HR Ho)]].
Qed.

Theorem x_to_h003 : forall cx N, c0 -[ Base.tm ]->* cx -> halted Base.tm cx -> Ones.ones cx N ->
  exists (c : cfgh), T3.evstep Defs.tmh T3.c0 c /\ T3.halted Defs.tmh c /\ Defs.ones c N.
Proof.
  intros cx N Hr Hh Ho.
  destruct (evstep_ms _ _ Hr) as [n Hn].
  destruct (sim_run n T3.c0 c0 cx rel_c0 Hn Hh) as [c7h [H1 [H2 H3]]].
  exists c7h. split; [exact H1 | split; [exact H2 | exact (ones_rel c7h cx N H3 Ho)]].
Qed.

Print Assumptions h003_halts_of_x.
Print Assumptions x_halts_of_h003.
Print Assumptions h003_reach_of_x.
Print Assumptions h003_to_x.
Print Assumptions x_to_h003.
Print Assumptions halted_unique7.
Print Assumptions halted_uniquex.
