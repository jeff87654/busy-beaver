(** * Sim.v : the 9-state record C04 simulates the 8-state machine M8.

    C04 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF   (Dev.Base.tm, over BB92)
    M8  = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---           (M8.Tm8.tm8, over BB82)

    State map stmap : A..F -> A..F, G -> I, H -> H; symbols S0 -> S0, S1 -> S1.  Every M8 step is matched by one C04
    step, except M8's F0 = 1RG, which C04 does in three steps: F0 = 0RG, then G (0LH / 1LH: the cell is left unchanged,
    the head moves back), then H0 = 1RI (H reads the 0 F just wrote).  Configurations are related by [Rel] through
    finite tape lists (so no stream bisimulation is needed).  M8 halts exactly where C04 does (both only at H1).

    Consequences (all from C04's development, read-only): M8 halts from the blank tape (c04_halts + determinism),
    and every count of M8's halting tape is a count of C04's halting tape and vice versa ([m8_to_c04], [c04_to_m8]). *)
From M8 Require Individual82.
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".
From Dev Require Base Final.
From Fgh Require Uniq.
From K31 Require K31_Abs.
From M8 Require Tm8.

Module T8 := Individual82.Individual82.Permute.Flip.Compute.TM.

Definition stmap (q : BB82.state) : BB92.state :=
  match q with
  | BB82.A => BB92.A | BB82.B => BB92.B | BB82.C => BB92.C | BB82.D => BB92.D
  | BB82.E => BB92.E | BB82.F => BB92.F | BB82.G => BB92.I | BB82.H => BB92.H
  end.

Definition symmap (s : BB82.sym) : BB92.sym :=
  match s with
  | BB82.S0 => BB92.S0
  | BB82.S1 => BB92.S1
  end.

Definition cfg8 : Type := (BB82.state * (Stream BB82.sym * BB82.sym * Stream BB82.sym))%type.

Definition Rel (c8 : cfg8) (c9 : Q * tape) : Prop :=
  exists q (Ll : list BB82.sym) s (Rr : list BB82.sym),
    c8 = (q, (Ll *> const BB82.S0, s, Rr *> const BB82.S0)) /\
    c9 = (stmap q, (map symmap Ll *> const BB92.S0, symmap s, map symmap Rr *> const BB92.S0)).

Ltac reify t :=
  lazymatch t with
  | Streams.Cons ?x ?t' => let L := reify t' in constr:(x :: L)
  | ?L *> const _ => L
  | const _ => constr:(@nil BB82.sym)
  end.

Ltac solve_rel :=
  lazymatch goal with
  | |- Rel (?q, (?l, ?s, ?r)) _ =>
    let Ll := reify l in let Rr := reify r in
    exists q, Ll, s, Rr; split; reflexivity
  end.

Ltac run_steps := repeat (eapply multistep_S; [prove_step |]); apply multistep_0.

Lemma sim_step : forall (c8 c8' : cfg8) c9, T8.step Tm8.tm8 c8 c8' -> Rel c8 c9 ->
  exists k c9', c9 -[ Base.tm ]->> S k / c9' /\ Rel c8' c9'.
Proof.
  intros c8 c8' c9 Hs [q [Ll [s [Rr [E8 E9]]]]]. subst c8 c9.
  inversion Hs as [q1 q' s1 s' l r Ht | q1 q' s1 s' l r Ht]; subst; clear Hs;
  destruct q, s; cbn in Ht; inversion Ht; subst; clear Ht;
  (destruct Ll as [| x Ll]; [| destruct x]); (destruct Rr as [| y Rr]; [| destruct y]);
  cbn [T8.move_left T8.move_right Streams.hd Streams.tl Str_app List.map stmap symmap Streams.const];
  first [ exists 0%nat; eexists; split; [run_steps | solve_rel]
        | exists 2%nat; eexists; split; [run_steps | solve_rel] ].
Qed.

(** ** Halting corresponds *)
Lemma halted_rel : forall c8 c9, Rel c8 c9 -> (T8.halted Tm8.tm8 c8 <-> halted Base.tm c9).
Proof.
  intros c8 c9 [q [Ll [s [Rr [E8 E9]]]]]. subst c8 c9.
  destruct q, s; cbn; split; intro Hh; (reflexivity || discriminate).
Qed.

Lemma rel_c0 : Rel T8.c0 c0.
Proof. exists BB82.A, (@nil BB82.sym), BB82.S0, (@nil BB82.sym). split; reflexivity. Qed.

(** ** Determinism on the C04 side *)
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

(** ** The simulation run: if C04 halts from a related configuration, so does M8, at a related configuration *)
Lemma sim_run : forall n (c8 : cfg8) c9 ch, Rel c8 c9 -> c9 -[ Base.tm ]->> n / ch -> halted Base.tm ch ->
  exists c8h, T8.evstep Tm8.tm8 c8 c8h /\ T8.halted Tm8.tm8 c8h /\ Rel c8h ch.
Proof.
  induction n as [n IH] using lt_wf_ind. intros c8 c9 ch HR Hn Hh.
  destruct c8 as [q [[l s] r]] eqn:Ec8.
  pose (o := Tm8.tm8 (q, s)). assert (Et : Tm8.tm8 (q, s) = o) by reflexivity. clearbody o. destruct o as [t |].
  - rewrite <- Ec8 in HR.
    assert (Hnh : ~ T8.halted Tm8.tm8 c8) by (subst c8; intro H8; change (Tm8.tm8 (q, s) = None) in H8; congruence).
    destruct (T8.no_halted_step _ _ Hnh) as [c8' Hs].
    destruct (sim_step c8 c8' c9 Hs HR) as [k [c9' [Hk HR']]].
    destruct (ms_det _ _ _ Hk n ch Hn Hh) as [Hle Hrest].
    destruct (IH (n - S k) ltac:(lia) c8' c9' ch HR' Hrest Hh) as [c8h [H1 [H2 H3]]].
    exists c8h. split; [| split; assumption]. rewrite <- Ec8. eapply T8.evstep_step; eassumption.
  - rewrite <- Ec8 in HR |- *.
    assert (H8 : T8.halted Tm8.tm8 c8) by (subst c8; change (Tm8.tm8 (q, s) = None); exact Et).
    pose proof (proj1 (halted_rel c8 c9 HR) H8) as H9.
    pose proof (ms_halted n c9 ch H9 Hn) as E. subst ch.
    exists c8. split; [apply T8.evstep_refl | split; assumption].
Qed.

(** ** M8 halts, at a configuration related to C04's halting configuration *)
Theorem m8_reach : exists (c8h : cfg8) ch, T8.evstep Tm8.tm8 T8.c0 c8h /\ T8.halted Tm8.tm8 c8h /\ Rel c8h ch /\
  c0 -[ Base.tm ]->* ch /\ halted Base.tm ch.
Proof.
  destruct Final.c04_halts as [n [ch [Hn Hh]]].
  destruct (sim_run n T8.c0 c0 ch rel_c0 Hn Hh) as [c8h [H1 [H2 H3]]].
  exists c8h, ch. split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact (ms_evstep _ _ _ Hn) | exact Hh]]]].
Qed.

Theorem m8_halts_sim : T8.halts Tm8.tm8 T8.c0.
Proof.
  destruct m8_reach as [c8h [ch [H1 [H2 _]]]].
  destruct (Tm8.evstep_multistep8 _ _ _ H1) as [n Hn].
  exists n, c8h. split; assumption.
Qed.

(** ** Ones counts transfer both ways *)
Lemma count_map : forall L, K31_Abs.count1 (map symmap L) = Tm8.count1 L.
Proof. induction L as [| a L IH]; [reflexivity |]. destruct a; cbn [map K31_Abs.count1 Tm8.count1]; rewrite IH; reflexivity. Qed.

Lemma val_map : forall s, K31_Abs.sym_val (symmap s) = Tm8.sym_val s.
Proof. destruct s; reflexivity. Qed.

Theorem m8_to_c04 : forall (c : cfg8) N, T8.evstep Tm8.tm8 T8.c0 c -> T8.halted Tm8.tm8 c -> Tm8.ones c N ->
  exists c9, c0 -[ Base.tm ]->* c9 /\ halted Base.tm c9 /\ K31_Abs.ones c9 N.
Proof.
  intros c N Hr Hh Ho.
  destruct m8_reach as [c8h [ch [H1 [H2 [HR [H3 H4]]]]]].
  pose proof (Tm8.halted_unique8 _ _ _ _ Hr H1 Hh H2) as E. subst c8h.
  exists ch. split; [exact H3 | split; [exact H4 |]].
  destruct HR as [q [Ll [s [Rr [E8 E9]]]]].
  destruct Ho as [q1 [L1 [R1 [s1 [E1 EN]]]]].
  rewrite E8 in E1. injection E1 as Eq EL Es ER. subst q1 s1.
  exists (stmap q), (map symmap Ll), (map symmap Rr), (symmap s). split; [exact E9 |].
  rewrite EN, !count_map, val_map, (Tm8.side_count8 Ll L1 EL), (Tm8.side_count8 Rr R1 ER). reflexivity.
Qed.

Theorem c04_to_m8 : forall c9 N, c0 -[ Base.tm ]->* c9 -> halted Base.tm c9 -> K31_Abs.ones c9 N ->
  exists (c : cfg8), T8.evstep Tm8.tm8 T8.c0 c /\ T8.halted Tm8.tm8 c /\ Tm8.ones c N.
Proof.
  intros c9 N Hr Hh Ho.
  destruct m8_reach as [c8h [ch [H1 [H2 [HR [H3 H4]]]]]].
  pose proof (Uniq.halted_unique c0 c9 ch Hr H3 Hh H4) as E. subst ch.
  exists c8h. split; [exact H1 | split; [exact H2 |]].
  destruct HR as [q [Ll [s [Rr [E8 E9]]]]].
  destruct Ho as [q1 [L1 [R1 [s1 [E1 EN]]]]].
  rewrite E9 in E1. injection E1 as Eq EL Es ER. subst s1.
  exists q, Ll, Rr, s. split; [exact E8 |].
  rewrite EN, <- (Uniq.side_count _ _ EL), <- (Uniq.side_count _ _ ER), !count_map, val_map. reflexivity.
Qed.

(* The full axiom audit (Print Assumptions on every main theorem) is in probe.v. *)
Print Assumptions sim_step.
