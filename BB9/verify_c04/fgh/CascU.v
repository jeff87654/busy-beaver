(** * CascU.v : the cascade invariant with UPPER bounds on everything on the tape.

    Fin.reachF only keeps lower bounds (y >= 1, parked P >= Pm + L) and finiteness of the far side.  For an upper bound
    on the score we carry, along the whole cascade (one orbit of Orbit.gstep from L1 down to a key):
      P <= Ptop = 12 R2 Bx + 11        (the parked count only decreases)
      L <= L1
      mass t s y Ll := t + s + y + count1 Ll  <=  L1 + (L1 - L) * Cst,
    where Ll is the far side as a list (l = Ll *> const 0) and Cst bounds the mass added by one g-step:
    a sub-step adds at most 19 + L, a stop adds 13 + 6 R with R = iter (3+i) (U (3i+2)) 0 <= Rc = iter L1 (U L1) 0.
    The machine steps are exactly Step.AbsSUB2..5 and the stop composite of Step.step_stop, here re-proved with its
    accumulator R explicit (step_stopX; same proof). *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From Dev Require Import Base Abs Lift Orbit Chain Step Fin.
From K31 Require Import K31_Abs.
From Fgh Require Import Tower.
Opaque U arrow.

Definition Ptop : nat := 12 * R2 Bx + 11.
Definition Rc : nat := iter L1 (U L1) O.
Definition Cst : nat := 19 + L1 + 6 * Rc.
Definition mass (t s y : nat) (Ll : list Sym) : nat := t + s + y + count1 Ll.

Definition reachU (L : nat) : Prop :=
  exists t P s y Ll, c0 -->* D0f t (S L) P s y (Ll *> const 0) /\ 1 <= y /\ Pm + L <= P /\ P <= Ptop /\
    L <= L1 /\ mass t s y Ll <= L1 + (L1 - L) * Cst.

Lemma L1_le_Ptop : L1 + 1000 <= Ptop.
Proof.
  destruct L1_val as [b [EB E1]]. pose proof (R2_ge Bx) as HR. pose proof Bx_ge6. unfold Ptop.
  generalize dependent (R2 Bx). intros R HR. lia.
Qed.

Lemma Pm_eq : Pm + L1 = Ptop.
Proof. pose proof L1_le_Ptop. unfold Pm, Ptop in *. lia. Qed.

(** Step.step_stop with the accumulator made explicit (the proof is Step.step_stop's). *)
Lemma step_stopX : forall i P s t y l, 15 <= P -> 1 <= y ->
  D0f t (5 * (3 * i + 2) + 31) P s y l -->+
  D0f (3 + t) (3 * (3 * i + 2) - 1) (P - 3) y (9 + 6 * iter (3 + i) (U (3 * i + 2)) O) ([0;1]^^s *> 1 >> l).
Proof.
  intros i P s t y l HP Hy. set (J := 3 * i + 2).
  set (e := (0 >> 0 >> lftx (2 :: 0 :: repeat 1 (P - 3) ++ [3 + y; s])%nat (1 >> l))).
  eapply progress_evstep_trans; [apply (AbsSTOP J P s t y l ltac:(lia)) |].
  fold e.
  assert (E1 : Kx (repeat 1%nat J ++ [8 + J]) 1 2 (2 + t) e = Kgx (repeat O J ++ [3 + i]) [] O O (2 + t) e).
  { unfold Kgx. rewrite map_rep, app_nil_r.
    replace (map tokd [3 + i]) with [8 + J] by (unfold J, tokd; simpl; f_equal; lia). reflexivity. }
  rewrite E1.
  eapply evstep_trans; [apply (CDPx J (3 + i) [] [] O (2 + t) e) |].
  { right. eexists. reflexivity. }
  rewrite app_nil_r. unfold Kgx. rewrite map_rep0, app_nil_r.
  change (3 * O + 1) with 1%nat.
  replace (S J) with ((J - 1) + 2) by (unfold J; lia).
  assert (E2 : e = 0 >> 0 >> lftx (2 :: 0 :: repeat 1 (P - 3) ++ [4 + (y - 1)])%nat (1 >> ([0;1]^^s *> 1 >> l))).
  { unfold e. f_equal. f_equal. cbn [lftx]. rewrite !lftx_app. cbn [lftx].
    replace (4 + (y - 1)) with (3 + y) by lia. reflexivity. }
  rewrite E2.
  eapply evstep_trans; [apply progress_evstep, (AbsENTRY (J - 1) _ (y - 1) (P - 3) (2 + t) _ ltac:(lia)) |].
  replace (1 + (2 + t)) with (3 + t) by lia.
  replace (3 * (J - 1) + 2) with (3 * J - 1) by (unfold J; lia).
  replace (1 + (y - 1)) with y by lia.
  apply evstep_refl.
Qed.

Lemma mass_step : forall L L' m m' d, L' < L -> L <= L1 -> m <= L1 + (L1 - L) * Cst -> m' <= m + d -> d <= Cst ->
  m' <= L1 + (L1 - L') * Cst.
Proof.
  intros L L' m m' d H1 H2 H3 H4 H5.
  assert (H6 : S (L1 - L) <= L1 - L') by lia.
  pose proof (Nat.mul_le_mono_r _ _ Cst H6) as H7. cbn [Nat.mul] in H7. lia.
Qed.

Ltac mass_simp := unfold mass; rewrite ?count1_app, ?count1_pow; cbn [count1 sym_val].

Theorem casc_stepU : forall L, 60 <= L -> L mod 2 = 1%nat -> L mod 3 = 1%nat -> reachU L -> reachU (gstep L).
Proof.
  intros L HL H2 H3 [t [P [s [y [Ll [HR [Hy [HP [HPt [HL1 HM]]]]]]]]]].
  destruct (split_mod L 3 ltac:(lia)) as [w [r3 [Hr3 HL3]]].
  rewrite (mod_of L 3 w r3 Hr3 HL3) in H3. subst r3. clear H2.
  destruct (split_mod L 5 ltac:(lia)) as [q [r [Hr HL5]]].
  unfold gstep. rewrite (mod_of L 5 q r Hr HL5).
  destruct r as [|[|[|[|[|r]]]]]; [| | | | | lia]; cbv beta iota.
  - (* r = 0: stop.  L = 5 (3 i + 2) + 30 *)
    destruct (split_mod q 3 ltac:(lia)) as [i0 [d [Hd Hq]]].
    assert (d = 2%nat) by lia. subst d.
    set (i := i0 - 2). assert (Li : L = 5 * (3 * i + 2) + 30) by (unfold i; lia).
    replace ((3 * L - 100) / 5) with (3 * (3 * i + 2) - 2).
    2:{ symmetry. apply div5_eq. lia. }
    set (R := iter (3 + i) (U (3 * i + 2)) O).
    assert (HRc : R <= Rc) by (unfold R, Rc; apply iter_U_mono3; lia).
    exists (3 + t), (P - 3), y, (9 + 6 * R), ([0;1]^^s ++ [1] ++ Ll).
    split; [| split; [lia | split; [lia | split; [lia | split; [lia |]]]]].
    + eapply evstep_trans; [exact HR |]. apply progress_evstep.
      replace (S L) with (5 * (3 * i + 2) + 31) by lia.
      replace (S (3 * (3 * i + 2) - 2)) with (3 * (3 * i + 2) - 1) by lia.
      rewrite !Str_app_assoc. apply (step_stopX i P s t y (Ll *> const 0)); lia.
    + apply (mass_step L _ (mass t s y Ll) _ (13 + 6 * R)); [lia | lia | exact HM | mass_simp; lia | unfold Cst; lia].
  - (* r = 1: residue c = 2 *)
    set (J := q - 8).
    replace ((3 * L + 32) / 5) with (3 * J + 31) by (symmetry; apply div5_eq; unfold J; lia).
    exists (3 + t), (P - 11), 5, (4 + J), ([0;1]^^4 ++ [1] ++ [0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
    split; [| split; [lia | split; [unfold J; lia | split; [lia | split; [unfold J; lia |]]]]].
    + eapply evstep_trans; [exact HR |]. apply progress_evstep.
      replace (S L) with (5 * J + 42) by (unfold J; lia).
      replace (S (3 * J + 31)) with (3 * J + 32) by lia.
      rewrite !Str_app_assoc. apply AbsSUB2. lia.
    + apply (mass_step L _ (mass t s y Ll) _ (19 + J)); [unfold J; lia | lia | exact HM | mass_simp; lia |
        unfold Cst, J; lia].
  - (* r = 2: residue c = 3 *)
    set (J := q - 3).
    replace ((3 * L - 46) / 5) with (3 * J + 1) by (symmetry; apply div5_eq; unfold J; lia).
    exists (3 + t), (P - 4), 2, (4 + J), ([0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
    split; [| split; [lia | split; [unfold J; lia | split; [lia | split; [unfold J; lia |]]]]].
    + eapply evstep_trans; [exact HR |]. apply progress_evstep.
      replace (S L) with (5 * J + 18) by (unfold J; lia).
      replace (S (3 * J + 1)) with (3 * J + 2) by lia.
      rewrite !Str_app_assoc. apply AbsSUB3. lia.
    + apply (mass_step L _ (mass t s y Ll) _ (19 + J)); [unfold J; lia | lia | exact HM | mass_simp; lia |
        unfold Cst, J; lia].
  - (* r = 3: residue c = 4 *)
    set (J := q - 4).
    replace ((3 * L - 64) / 5) with (3 * J + 1) by (symmetry; apply div5_eq; unfold J; lia).
    exists (3 + t), (P - 6), 6, (6 + J), ([0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
    split; [| split; [lia | split; [unfold J; lia | split; [lia | split; [unfold J; lia |]]]]].
    + eapply evstep_trans; [exact HR |]. apply progress_evstep.
      replace (S L) with (5 * J + 24) by (unfold J; lia).
      replace (S (3 * J + 1)) with (3 * J + 2) by lia.
      rewrite !Str_app_assoc. apply AbsSUB4. lia.
    + apply (mass_step L _ (mass t s y Ll) _ (19 + J)); [unfold J; lia | lia | exact HM | mass_simp; lia |
        unfold Cst, J; lia].
  - (* r = 4: residue c = 5 *)
    set (J := q - 3).
    replace ((3 * L - 52) / 5) with (3 * J + 1) by (symmetry; apply div5_eq; unfold J; lia).
    exists (3 + t), (P - 6), 4, (6 + J), ([0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
    split; [| split; [lia | split; [unfold J; lia | split; [lia | split; [unfold J; lia |]]]]].
    + eapply evstep_trans; [exact HR |]. apply progress_evstep.
      replace (S L) with (5 * J + 20) by (unfold J; lia).
      replace (S (3 * J + 1)) with (3 * J + 2) by lia.
      rewrite !Str_app_assoc. apply AbsSUB5. lia.
    + apply (mass_step L _ (mass t s y Ll) _ (19 + J)); [unfold J; lia | lia | exact HM | mass_simp; lia |
        unfold Cst, J; lia].
Qed.

Theorem reach_topU : reachU L1.
Proof.
  destruct L1_val as [b [EB E1]].
  pose proof (R2_ge Bx) as HR2. pose proof Pm_eq as HPm. unfold Ptop in HPm.
  exists 7, (7 + 2 * (2 + 6 * R2 Bx)), O, (8 + (36 * b + 16)), (@nil Sym).
  split; [| split; [lia | split; [lia | split; [unfold Ptop; lia | split; [lia |]]]]].
  - eapply evstep_trans; [exact reach_exh2 |].
    unfold Kg. rewrite map_rep0, app_nil_r.
    change (3 * O + 1) with 1%nat.
    replace (S (12 * Bx + 24)) with (5 + (12 * Bx + 20)) by lia.
    replace (3 * R2 Bx + 2) with (2 + 3 * R2 Bx) by lia.
    eapply evstep_trans; [apply progress_evstep, ATE |].
    replace (3 * (12 * Bx + 20) + 14) with (5 * (36 * b + 16) + 30) by lia.
    eapply evstep_trans; [apply progress_evstep, AT1 |].
    replace (3 * (36 * b + 16) + 8) with (S L1) by lia.
    apply evstep_refl.
  - unfold mass. cbn [count1]. lia.
Qed.

Print Assumptions casc_stepU.
Print Assumptions reach_topU.
