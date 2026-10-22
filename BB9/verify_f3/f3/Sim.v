(** * Sim.v : the auxiliary 11-state machine X simulates the 9-state machine f3_0RC (bb9_f3_coq).

    f3 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF          (F3.Defs.tm3, over BB92)
    X  = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LJ0LC_0RG1LD_0LH1LH_1RI---_0RI0RF_0LK---_0RC1RH (Dev.Base.tm, over BB112)

    State map stmap : A..F -> A..F, G -> I, H -> J, I -> K; symbols S0 -> S0, S1 -> S1.  Every f3 step is matched by
    one X step, except f3's F0 = 1RG, which X does in three steps (F0 = 0RG, G = 0LH/1LH back, H0 = 1RI), and f3's
    I1 = 1RF, which X does as K1 = 1RH: X is then in H where f3 is in F, both reading the 0 that f3's H0 (X's J0)
    wrote, and the next step (f3 F0 = 1RG, X H0 = 1RI) brings them back to related states.  [Rel] relates
    configurations through finite tape lists, with that alternative, and with the invariant that f3 in I has a 0
    to its right (I is entered only by H0 = 0LI).  f3 halts exactly where X does (f3 at H1, X at J1). *)
From BB8 Require Individual92.
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Base XFinal.
From XK31 Require K31_Abs.
From F3 Require Defs.

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

Definition cfg3 : Type := (BB92.state * (Stream BB92.sym * BB92.sym * Stream BB92.sym))%type.

Definition hd0 (Rr : list BB92.sym) : Prop :=
  match Rr with
  | [] => True
  | x :: _ => x = BB92.S0
  end.

Definition Rel (c3 : cfg3) (cx : Q * tape) : Prop :=
  exists q (Ll : list BB92.sym) s (Rr : list BB92.sym),
    c3 = (q, (Ll *> const BB92.S0, s, Rr *> const BB92.S0)) /\
    (q = BB92.I -> hd0 Rr) /\
    (cx = (stmap q, (map symmap Ll *> const S0, symmap s, map symmap Rr *> const S0)) \/
     (q = BB92.F /\ s = BB92.S0 /\ cx = (H, (map symmap Ll *> const S0, S0, map symmap Rr *> const S0)))).

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
    exists q, Ll, s, Rr; split; [reflexivity |];
    split; [let HH := fresh in intro HH; first [discriminate HH | exact I | reflexivity] |];
    first [left; reflexivity | right; split; [reflexivity | split; reflexivity]]
  end.

Ltac run_steps := repeat (eapply multistep_S; [prove_step |]); apply multistep_0.

Lemma sim_step : forall (c3 c3' : cfg3) cx, T3.step Defs.tm3 c3 c3' -> Rel c3 cx ->
  exists k cx', cx -[ Base.tm ]->> S k / cx' /\ Rel c3' cx'.
Proof.
  intros c3 c3' cx Hs [q [Ll [s [Rr [E3 [Hi Hx]]]]]]. subst c3.
  inversion Hs as [q1 q' s1 s' l r Ht | q1 q' s1 s' l r Ht]; subst; clear Hs;
  destruct q, s; cbn in Ht; inversion Ht; subst; clear Ht;
  (destruct Ll as [| x Ll]; [| destruct x]); (destruct Rr as [| y Rr]; [| destruct y]);
  (destruct Hx as [Ex | [Eq [Es Ex]]]; [| try discriminate Eq; try discriminate Es]); subst cx;
  try (exfalso; specialize (Hi eq_refl); cbn in Hi; discriminate Hi);
  cbn [T3.move_left T3.move_right Streams.hd Streams.tl Str_app List.map stmap symmap Streams.const];
  first [ exists 0%nat; eexists; split; [run_steps | solve_rel]
        | exists 2%nat; eexists; split; [run_steps | solve_rel] ].
Qed.

(** ** Halting corresponds *)
Lemma halted_rel : forall c3 cx, Rel c3 cx -> (T3.halted Defs.tm3 c3 <-> halted Base.tm cx).
Proof.
  intros c3 cx [q [Ll [s [Rr [E3 [_ [Ex | [Eq [Es Ex]]]]]]]]]; subst c3 cx; [| subst q s];
  [destruct q, s |]; cbn; split; intro Hh; (reflexivity || discriminate).
Qed.

Lemma rel_c0 : Rel T3.c0 c0.
Proof.
  exists BB92.A, (@nil BB92.sym), BB92.S0, (@nil BB92.sym). split; [reflexivity |].
  split; [intro HH; discriminate HH | left; reflexivity].
Qed.

(** ** Determinism on the X side *)
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

(** ** The simulation run: if X halts from a related configuration, so does f3, at a related configuration *)
Lemma sim_run : forall n (c3 : cfg3) cx ch, Rel c3 cx -> cx -[ Base.tm ]->> n / ch -> halted Base.tm ch ->
  exists c3h, T3.evstep Defs.tm3 c3 c3h /\ T3.halted Defs.tm3 c3h /\ Rel c3h ch.
Proof.
  induction n as [n IH] using lt_wf_ind. intros c3 cx ch HR Hn Hh.
  destruct c3 as [q [[l s] r]] eqn:Ec3.
  pose (o := Defs.tm3 (q, s)). assert (Et : Defs.tm3 (q, s) = o) by reflexivity. clearbody o. destruct o as [t |].
  - rewrite <- Ec3 in HR.
    assert (Hnh : ~ T3.halted Defs.tm3 c3) by (subst c3; intro H3; change (Defs.tm3 (q, s) = None) in H3; congruence).
    destruct (T3.no_halted_step _ _ Hnh) as [c3' Hs].
    destruct (sim_step c3 c3' cx Hs HR) as [k [cx' [Hk HR']]].
    destruct (ms_det _ _ _ Hk n ch Hn Hh) as [Hle Hrest].
    destruct (IH (n - S k) ltac:(lia) c3' cx' ch HR' Hrest Hh) as [c3h [H1 [H2 H3]]].
    exists c3h. split; [| split; assumption]. rewrite <- Ec3. eapply T3.evstep_step; eassumption.
  - rewrite <- Ec3 in HR |- *.
    assert (H3 : T3.halted Defs.tm3 c3) by (subst c3; change (Defs.tm3 (q, s) = None); exact Et).
    pose proof (proj1 (halted_rel c3 cx HR) H3) as Hx.
    pose proof (ms_halted n cx ch Hx Hn) as E. subst ch.
    exists c3. split; [apply T3.evstep_refl | split; assumption].
Qed.

(** ** f3 halts, at a configuration related to X's halting configuration *)
Theorem f3_reach : exists (c3h : cfg3) ch, T3.evstep Defs.tm3 T3.c0 c3h /\ T3.halted Defs.tm3 c3h /\ Rel c3h ch /\
  c0 -[ Base.tm ]->* ch /\ halted Base.tm ch.
Proof.
  destruct XFinal.x_halts as [n [ch [Hn Hh]]].
  destruct (sim_run n T3.c0 c0 ch rel_c0 Hn Hh) as [c3h [H1 [H2 H3]]].
  exists c3h, ch. split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact (ms_evstep _ _ _ Hn) | exact Hh]]]].
Qed.

(** ** Generic facts about 9-state runs *)
Theorem halted_unique3 : forall (tm : T3.TM) c c1 c2, T3.evstep tm c c1 -> T3.evstep tm c c2 ->
  T3.halted tm c1 -> T3.halted tm c2 -> c1 = c2.
Proof.
  intros tm c c1 c2 H1. revert c2. induction H1 as [c | c c' c1 Hs H1 IH]; intros c2 H2 Hh1 Hh2.
  - inversion H2 as [| ? c'' ? Hs' H2']; subst; [reflexivity |].
    exfalso. exact (T3.halted_no_step _ _ _ Hh1 Hs').
  - inversion H2 as [| ? c'' ? Hs' H2']; subst.
    + exfalso. exact (T3.halted_no_step _ _ _ Hh2 Hs).
    + pose proof (T3.step_deterministic _ _ _ _ Hs Hs') as E. subst c''. apply IH; assumption.
Qed.

Lemma zeros_count3 : forall L : list BB92.sym, const BB92.S0 = L *> const BB92.S0 -> Defs.count1 L = 0%nat.
Proof.
  induction L as [| a L IH]; intro H; [reflexivity |].
  cbn [Str_app] in H.
  pose proof (f_equal (@Streams.hd BB92.sym) H) as Ha. pose proof (f_equal (@Streams.tl BB92.sym) H) as Ht.
  cbn in Ha, Ht. subst a.
  cbn [Defs.count1 Defs.sym_val]. apply IH. exact Ht.
Qed.

Lemma side_count3 : forall L1 L2 : list BB92.sym, L1 *> const BB92.S0 = L2 *> const BB92.S0 ->
  Defs.count1 L1 = Defs.count1 L2.
Proof.
  induction L1 as [| a L1 IH]; intros L2 H.
  - symmetry. exact (zeros_count3 L2 H).
  - destruct L2 as [| b L2].
    + symmetry in H. exact (zeros_count3 (a :: L1) H).
    + cbn [Str_app] in H. injection H as Hab Ht. subst b. cbn [Defs.count1]. rewrite (IH L2 Ht). reflexivity.
Qed.

Theorem f3_halts_sim : T3.halts Defs.tm3 T3.c0.
Proof.
  destruct f3_reach as [c3h [ch [H1 [H2 _]]]].
  assert (Hm : forall c c', T3.evstep Defs.tm3 c c' -> exists n, T3.multistep Defs.tm3 n c c').
  { intros c c' H. induction H as [c | c c' c'' Hs _ [n IH]].
    - exists 0%nat. apply T3.multistep_0.
    - exists (S n). eapply T3.multistep_S; eassumption. }
  destruct (Hm _ _ H1) as [n Hn]. exists n, c3h. split; assumption.
Qed.

(** ** Ones counts transfer both ways *)
Lemma count_map : forall L, K31_Abs.count1 (map symmap L) = Defs.count1 L.
Proof. induction L as [| a L IH]; [reflexivity |]. destruct a; cbn [map K31_Abs.count1 Defs.count1]; rewrite IH; reflexivity. Qed.

Lemma val_map : forall s, K31_Abs.sym_val (symmap s) = Defs.sym_val s.
Proof. destruct s; reflexivity. Qed.

Lemma zeros_countx : forall L : list Sym, const S0 = L *> const S0 -> K31_Abs.count1 L = 0%nat.
Proof.
  induction L as [| a L IH]; intro H; [reflexivity |].
  cbn [Str_app] in H.
  pose proof (f_equal (@Streams.hd Sym) H) as Ha. pose proof (f_equal (@Streams.tl Sym) H) as Ht. cbn in Ha, Ht. subst a.
  cbn [K31_Abs.count1 K31_Abs.sym_val]. apply IH. exact Ht.
Qed.

Lemma side_countx : forall L1 L2 : list Sym, L1 *> const S0 = L2 *> const S0 -> K31_Abs.count1 L1 = K31_Abs.count1 L2.
Proof.
  induction L1 as [| a L1 IH]; intros L2 H.
  - symmetry. exact (zeros_countx L2 H).
  - destruct L2 as [| b L2].
    + symmetry in H. exact (zeros_countx (a :: L1) H).
    + cbn [Str_app] in H. injection H as Hab Ht. subst b. cbn [K31_Abs.count1]. rewrite (IH L2 Ht). reflexivity.
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

Lemma rel_ones : forall c3 cx N, Rel c3 cx -> Defs.ones c3 N -> K31_Abs.ones cx N.
Proof.
  intros c3 cx N [q [Ll [s [Rr [E3 [_ Hx]]]]]] [q1 [L1 [R1 [s1 [E1 EN]]]]].
  rewrite E3 in E1. injection E1 as Eq EL Es ER. subst q1 s1.
  destruct Hx as [Ex | [Eq [Es Ex]]]; subst cx.
  - exists (stmap q), (map symmap Ll), (map symmap Rr), (symmap s). split; [reflexivity |].
    rewrite EN, !count_map, val_map, (side_count3 Ll L1 EL), (side_count3 Rr R1 ER). reflexivity.
  - subst s. exists H, (map symmap Ll), (map symmap Rr), S0. split; [reflexivity |].
    rewrite EN, !count_map, (side_count3 Ll L1 EL), (side_count3 Rr R1 ER). reflexivity.
Qed.

Lemma ones_rel : forall c3 cx N, Rel c3 cx -> K31_Abs.ones cx N -> Defs.ones c3 N.
Proof.
  intros c3 cx N [q [Ll [s [Rr [E3 [_ Hx]]]]]] [q1 [L1 [R1 [s1 [E1 EN]]]]].
  subst c3. exists q, Ll, Rr, s. split; [reflexivity |].
  destruct Hx as [Ex | [Eq [Es Ex]]]; rewrite Ex in E1; injection E1 as Eq1 EL Es1 ER; subst.
  - rewrite <- (side_countx _ _ EL), <- (side_countx _ _ ER), !count_map, val_map. reflexivity.
  - rewrite <- (side_countx _ _ EL), <- (side_countx _ _ ER), !count_map. reflexivity.
Qed.

(** ** Every halting count of f3 is a halting count of X, and conversely *)
Theorem f3_to_x : forall (c : cfg3) N, T3.evstep Defs.tm3 T3.c0 c -> T3.halted Defs.tm3 c -> Defs.ones c N ->
  exists cx, c0 -[ Base.tm ]->* cx /\ halted Base.tm cx /\ K31_Abs.ones cx N.
Proof.
  intros c N Hr Hh Ho.
  destruct f3_reach as [c3h [ch [H1 [H2 [HR [H3 H4]]]]]].
  pose proof (halted_unique3 _ _ _ _ Hr H1 Hh H2) as E. subst c3h.
  exists ch. split; [exact H3 | split; [exact H4 | exact (rel_ones c ch N HR Ho)]].
Qed.

Theorem x_to_f3 : forall cx N, c0 -[ Base.tm ]->* cx -> halted Base.tm cx -> K31_Abs.ones cx N ->
  exists (c : cfg3), T3.evstep Defs.tm3 T3.c0 c /\ T3.halted Defs.tm3 c /\ Defs.ones c N.
Proof.
  intros cx N Hr Hh Ho.
  destruct f3_reach as [c3h [ch [H1 [H2 [HR [H3 H4]]]]]].
  pose proof (halted_uniquex c0 cx ch Hr H3 Hh H4) as E. subst ch.
  exists c3h. split; [exact H1 | split; [exact H2 | exact (ones_rel c3h cx N HR Ho)]].
Qed.
