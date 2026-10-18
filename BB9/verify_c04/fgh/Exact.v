(** * Exact.v : the exact score of C04 as a symbolic recursion.

    The run from the exhaustion-#2 D0 moment to the halt is a deterministic recursion on the abstract state
      (t, L, P, s, y, m)  =  D0f t (S L) P s y (Ll *> const 0)  with  m = count1 Ll   (the far side's ones),
    one g-step per cascade value L (gnext: the generic sub-steps for L = 1..4 mod 5, the stop for L = 0 mod 5;
    gnext's L is Orbit.gstep L), run until L < 60, i.e. until a key 31/37/43/49/55; then the key's endgame route
    gives the halting tape K31_End.Hc, whose ones count is HN (= Uniq.Hc_N).  So
      sigma_c04 := sig_key (run L1 top)
    with every ingredient an explicit nat expression in U / iter of Bx (uncomputable in practice: the orbit and the
    residues P mod 6, (P - 35) mod 5 depend on the digits of Bx and R2 Bx).  Main result:
      c04_score_exact : forall c N, c0 -->* c -> halted tm c -> ones c N -> N = sigma_c04
      c04_sigma_bracket : f_omega (f_omega (12 Bx + 26)) < sigma_c04 < f_omega (f_omega (12 Bx + 27)). *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List Bool.
Import ListNotations.
Set Default Goal Selector "!".
From Dev Require Import Base Abs Lift Orbit Chain Cascade Step Fin CBtail Endgame.
From K31 Require Import K31_Abs K31_Mach K31_End.
From Dev Require ScoreEnd.
From Score Require Import Score.
From Fgh Require Import FArith Tower Uniq CascU EndU.
Opaque U arrow Bx f f_omega.

(** ** The ones count of the halting tape Hc d s G Ll R n t, with g = count1 (encl G), m = count1 Ll. *)
Definition HN (d s g m R n t : nat) : nat := d + s + g + m + 6 * R + 2 * n + 4 * t + 15.

(** ** Abstract cascade state and one g-step *)
Record cst := mk { ct : nat; cL : nat; cP : nat; cs : nat; cy : nat; cm : nat }.

Definition gnext (x : cst) : cst :=
  match cL x mod 5 with
  | 1%nat => mk (3 + ct x) (3 * (cL x / 5 - 8) + 31) (cP x - 11) 5 (4 + (cL x / 5 - 8)) (cm x + cy x + cs x + 7)
  | 2%nat => mk (3 + ct x) (3 * (cL x / 5 - 3) + 1) (cP x - 4) 2 (4 + (cL x / 5 - 3)) (cm x + cy x + cs x + 2)
  | 3%nat => mk (3 + ct x) (3 * (cL x / 5 - 4) + 1) (cP x - 6) 6 (6 + (cL x / 5 - 4)) (cm x + cy x + cs x + 2)
  | 4%nat => mk (3 + ct x) (3 * (cL x / 5 - 3) + 1) (cP x - 6) 4 (6 + (cL x / 5 - 3)) (cm x + cy x + cs x + 2)
  | _ => mk (3 + ct x) (3 * (3 * ((cL x / 5 - 8) / 3) + 2) - 2) (cP x - 3) (cy x)
            (9 + 6 * iter (3 + (cL x / 5 - 8) / 3) (U (3 * ((cL x / 5 - 8) / 3) + 2)) O) (cm x + cs x + 1)
  end.

Fixpoint run (n : nat) (x : cst) : cst :=
  match n with
  | O => x
  | S n' => if 60 <=? cL x then run n' (gnext x) else x
  end.

(** the state right after exhaustion #2 (TOPENTRY + TOP1): D0f 7 (S L1) (12 R2 + 11) 0 (36 (Bx/5) + 24) (const 0) *)
Definition top : cst := mk 7 L1 (12 * R2 Bx + 11) 0 (36 * (Bx / 5) + 24) 0.

(** ** The endgame routes *)
Definition RE31 (P : nat) : nat := iter 2 (U (P - 21)) O.
Definition sig31 (t P s y m : nat) : nat :=
  match (P - 35) mod 5 with
  | 0%nat => HN 0 2 (13 + y + s) m (iter (2 * RE31 P + (P - 35) / 5 + 7) (U (S (3 * ((P - 35) / 5) + 2))) O)
            (S (3 * ((P - 35) / 5) + 2)) (t + 12)
  | 1%nat => HN 1 5 (7 + y + s) m (iter 1 (U (S (S (3 * ((P - 35) / 5) + 1)))) (K31_End.Rb1 ((P - 35) / 5) (RE31 P)))
            (S (S (3 * ((P - 35) / 5) + 1))) (t + 12)
  | 2%nat => HN (6 * RE31 P) 4 (16 + y + s) m (iter ((P - 35) / 5 + 5) (U (S (3 * ((P - 35) / 5) + 5))) O)
            (S (3 * ((P - 35) / 5) + 5)) (t + 12)
  | 3%nat => HN 1 5 (7 + y + s) m (iter 1 (U (S (S (3 * ((P - 35) / 5) + 3)))) (Ry3 ((P - 35) / 5) (RE31 P)))
            (S (S (3 * ((P - 35) / 5) + 3))) (t + 12)
  | _ => HN 0 2 (13 + y + s) m (iter (2 * Rx3 ((P - 35) / 5) + 2 * RE31 P + 6) (U (S (3 * ((P - 35) / 5) + 2))) O)
            (S (3 * ((P - 35) / 5) + 2)) (t + 12)
  end.
Definition sig37 (t P s y m : nat) : nat := HN 7 2 0 (m + y + s + 2) (ScoreEnd.Rb3 (P - 15)) (S (P - 15)) (t + 7).
Definition sig43 (t P s y m : nat) : nat := HN 9 6 0 (m + y + s + 2) (ScoreEnd.Rb3 (P - 17)) (S (P - 17)) (t + 7).
Definition sig49 (t P s y m : nat) : nat := HN 3 12 5 (m + y + s + 2) (ScoreEnd.Rb3 (P - 18)) (S (P - 18)) (t + 8).
Definition sig55 (t P s y m : nat) : nat :=
  HN (8 + 6 * iter 4 (U 5) O) y 0 (m + s + 1) (ScoreEnd.Rb3 (P - 14)) (S (P - 14)) (t + 7).

Definition sig_key (x : cst) : nat :=
  if cL x =? 31 then sig31 (ct x) (cP x) (cs x) (cy x) (cm x)
  else if cL x =? 37 then sig37 (ct x) (cP x) (cs x) (cy x) (cm x)
  else if cL x =? 43 then sig43 (ct x) (cP x) (cs x) (cy x) (cm x)
  else if cL x =? 49 then sig49 (ct x) (cP x) (cs x) (cy x) (cm x)
  else sig55 (ct x) (cP x) (cs x) (cy x) (cm x).

(** The exact score of C04. *)
Definition sigma_c04 : nat := sig_key (run L1 top).

(** ** Correctness *)
Definition reachE (x : cst) : Prop :=
  exists Ll, c0 -->* D0f (ct x) (S (cL x)) (cP x) (cs x) (cy x) (Ll *> const 0) /\ count1 Ll = cm x /\
    1 <= cy x /\ Pm + cL x <= cP x /\ cL x mod 2 = 1%nat /\ cL x mod 3 = 1%nat.

Lemma div_of : forall n k q r, r < k -> n = k * q + r -> n / k = q.
Proof. intros n k q r Hr Hn. symmetry. apply (Nat.div_unique n k q r Hr Hn). Qed.

Lemma gnext_L : forall x, 60 <= cL x -> cL x mod 3 = 1%nat -> cL (gnext x) = gstep (cL x).
Proof.
  intros [t L P s y m] HL H3. cbn [cL] in *. unfold gnext, gstep. cbn [cL].
  destruct (split_mod L 5 ltac:(lia)) as [q [r [Hr HL5]]].
  rewrite (mod_of L 5 q r Hr HL5), (div_of L 5 q r Hr HL5).
  destruct (split_mod L 3 ltac:(lia)) as [w [r3 [Hr3 HL3]]].
  rewrite (mod_of L 3 w r3 Hr3 HL3) in H3. subst r3.
  destruct r as [|[|[|[|[|r]]]]]; [| | | | | lia]; cbn [cL].
  - destruct (split_mod q 3 ltac:(lia)) as [i0 [d [Hd Hq]]]. assert (d = 2%nat) by lia. subst d.
    rewrite (div_of (q - 8) 3 (i0 - 2) 0) by lia. symmetry. apply div5_eq. lia.
  - symmetry. apply div5_eq. lia.
  - symmetry. apply div5_eq. lia.
  - symmetry. apply div5_eq. lia.
  - symmetry. apply div5_eq. lia.
Qed.

Theorem gnext_ok : forall x, 60 <= cL x -> reachE x -> reachE (gnext x).
Proof.
  intros [t L P s y m] HL [Ll [HR [Hm [Hy [HP [H2 H3]]]]]]. cbn [ct cL cP cs cy cm] in *.
  pose proof (gstep_inv L HL H2 H3) as [G2 G3].
  pose proof (gnext_L (mk t L P s y m) HL H3) as EL. cbn [cL] in EL.
  pose proof (gstep_lt L HL) as Hlt.
  unfold reachE. rewrite EL. clear EL. unfold gnext. cbn [ct cL cP cs cy cm].
  destruct (split_mod L 3 ltac:(lia)) as [w [r3 [Hr3 HL3]]].
  rewrite (mod_of L 3 w r3 Hr3 HL3) in H3. subst r3.
  destruct (split_mod L 5 ltac:(lia)) as [q [r [Hr HL5]]].
  unfold gstep in *. rewrite (mod_of L 5 q r Hr HL5) in *. rewrite (div_of L 5 q r Hr HL5).
  destruct r as [|[|[|[|[|r]]]]]; [| | | | | lia]; cbv beta iota in *; cbn [ct cL cP cs cy cm] in *.
  - (* stop *)
    destruct (split_mod q 3 ltac:(lia)) as [i0 [d [Hd Hq]]]. assert (d = 2%nat) by lia. subst d.
    set (i := i0 - 2). assert (Li : L = 5 * (3 * i + 2) + 30) by (unfold i; lia).
    rewrite (div_of (q - 8) 3 i 0) by (unfold i; lia).
    replace ((3 * L - 100) / 5) with (3 * (3 * i + 2) - 2) in * by (symmetry; apply div5_eq; lia).
    exists ([0;1]^^s ++ [1] ++ Ll). split; [| split; [| split; [lia | split; [lia | split; assumption]]]].
    + eapply evstep_trans; [exact HR |]. apply progress_evstep.
      replace (S L) with (5 * (3 * i + 2) + 31) by lia.
      replace (S (3 * (3 * i + 2) - 2)) with (3 * (3 * i + 2) - 1) by lia.
      rewrite !Str_app_assoc. apply (step_stopX i P s t y (Ll *> const 0)); lia.
    + rewrite !count1_app, count1_pow. cbn [count1 sym_val]. lia.
  - set (J := q - 8).
    replace ((3 * L + 32) / 5) with (3 * J + 31) in * by (symmetry; apply div5_eq; unfold J; lia).
    exists ([0;1]^^4 ++ [1] ++ [0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
    split; [| split; [| split; [lia | split; [unfold J; lia | split; assumption]]]].
    + eapply evstep_trans; [exact HR |]. apply progress_evstep.
      replace (S L) with (5 * J + 42) by (unfold J; lia). replace (S (3 * J + 31)) with (3 * J + 32) by lia.
      rewrite !Str_app_assoc. apply AbsSUB2. lia.
    + rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
  - set (J := q - 3).
    replace ((3 * L - 46) / 5) with (3 * J + 1) in * by (symmetry; apply div5_eq; unfold J; lia).
    exists ([0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
    split; [| split; [| split; [lia | split; [unfold J; lia | split; assumption]]]].
    + eapply evstep_trans; [exact HR |]. apply progress_evstep.
      replace (S L) with (5 * J + 18) by (unfold J; lia). replace (S (3 * J + 1)) with (3 * J + 2) by lia.
      rewrite !Str_app_assoc. apply AbsSUB3. lia.
    + rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
  - set (J := q - 4).
    replace ((3 * L - 64) / 5) with (3 * J + 1) in * by (symmetry; apply div5_eq; unfold J; lia).
    exists ([0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
    split; [| split; [| split; [lia | split; [unfold J; lia | split; assumption]]]].
    + eapply evstep_trans; [exact HR |]. apply progress_evstep.
      replace (S L) with (5 * J + 24) by (unfold J; lia). replace (S (3 * J + 1)) with (3 * J + 2) by lia.
      rewrite !Str_app_assoc. apply AbsSUB4. lia.
    + rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
  - set (J := q - 3).
    replace ((3 * L - 52) / 5) with (3 * J + 1) in * by (symmetry; apply div5_eq; unfold J; lia).
    exists ([0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
    split; [| split; [| split; [lia | split; [unfold J; lia | split; assumption]]]].
    + eapply evstep_trans; [exact HR |]. apply progress_evstep.
      replace (S L) with (5 * J + 20) by (unfold J; lia). replace (S (3 * J + 1)) with (3 * J + 2) by lia.
      rewrite !Str_app_assoc. apply AbsSUB5. lia.
    + rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
Qed.

Lemma run_stop : forall n x, cL x < 60 -> run n x = x.
Proof.
  intros [| n] x H; [reflexivity |]. cbn [run].
  destruct (60 <=? cL x) eqn:E; [apply Nat.leb_le in E; lia | reflexivity].
Qed.

Theorem run_ok : forall n x, reachE x -> 60 <= cL x -> cL x <= n -> reachE (run n x) /\ in_keys (cL (run n x)) = true.
Proof.
  induction n as [| n IH]; intros x HR HL Hn; [lia |].
  cbn [run]. rewrite (proj2 (Nat.leb_le 60 (cL x)) HL).
  pose proof (gnext_ok x HL HR) as HR'.
  destruct HR as [Ll [_ [_ [_ [_ [H2 H3]]]]]].
  pose proof (gnext_L x HL H3) as EL. pose proof (gstep_lt (cL x) HL) as Hlt.
  destruct (Nat.le_gt_cases 60 (cL (gnext x))) as [Hge | Hlt'].
  - apply IH; [exact HR' | exact Hge | lia].
  - rewrite (run_stop n (gnext x) Hlt'). cbv iota. split; [exact HR' |].
    rewrite EL. apply gstep_key; [exact HL | exact H2 | exact H3 | lia].
Qed.

Lemma top_ok : reachE top.
Proof.
  destruct L1_val as [b [EB E1]]. destruct L1_props as [H60 [H2 H3]].
  pose proof (R2_ge Bx) as HR2. pose proof Pm_eq as HPm. unfold Ptop in HPm.
  assert (Eb : Bx / 5 = b) by (apply (div_of Bx 5 b 1); lia).
  exists (@nil Sym). unfold top. cbn [ct cL cP cs cy cm]. rewrite Eb.
  split; [| split; [reflexivity | split; [lia | split; [lia | split; assumption]]]].
  eapply evstep_trans; [exact reach_exh2 |].
  unfold Kg. rewrite map_rep0, app_nil_r.
  change (3 * O + 1) with 1%nat.
  replace (S (12 * Bx + 24)) with (5 + (12 * Bx + 20)) by lia.
  replace (3 * R2 Bx + 2) with (2 + 3 * R2 Bx) by lia.
  eapply evstep_trans; [apply progress_evstep, ATE |].
  replace (3 * (12 * Bx + 20) + 14) with (5 * (36 * b + 16) + 30) by lia.
  eapply evstep_trans; [apply progress_evstep, AT1 |].
  replace (3 * (36 * b + 16) + 8) with (S L1) by lia.
  replace (7 + 2 * (2 + 6 * R2 Bx)) with (12 * R2 Bx + 11) by lia.
  replace (8 + (36 * b + 16)) with (36 * b + 24) by lia.
  apply evstep_refl.
Qed.

(** ** The keys, with the exact count *)
Definition KeyGoal (x : cst) : Prop := exists c, c0 -->* c /\ halted tm c /\ ones c (sig_key x).

Lemma hc_goal : forall c d s G Ll R n t N, c0 -->* Hc d s G (Ll *> const 0) R n t -> Hc_N d s G Ll R n t = N ->
  N = c -> exists c', c0 -->* c' /\ halted tm c' /\ ones c' c.
Proof.
  intros c d s G Ll R n t N H1 H2 H3. subst. exists (Hc d s G (Ll *> const 0) R n t).
  split; [exact H1 | split; [apply Hc_halted | apply Hc_ones_exact]].
Qed.

Ltac cnt := unfold Hc_N, HN; rewrite ?count1_encl_cons, ?count1_app, ?count1_pow; cbn [encl count1 sym_val]; lia.

Lemma key31E : forall t P s y m, reachE (mk t 31 P s y m) -> KeyGoal (mk t 31 P s y m).
Proof.
  intros t P s y m [Ll [HR [Hm [Hy [HP _]]]]]. cbn [ct cL cP cs cy cm] in *. pose proof Pm_ge.
  unfold KeyGoal, sig_key. cbn [ct cL cP cs cy cm]. change (31 =? 31) with true. cbv iota.
  pose proof (k31_esc P s t y (Ll *> const 0) ltac:(lia)) as HE.
  unfold sig31. change (RE P) with (RE31 P) in HE. set (R := RE31 P) in *.
  destruct (split_mod (P - 35) 5 ltac:(lia)) as [w [rho [Hrho Hw]]].
  rewrite (mod_of (P - 35) 5 w rho Hrho Hw), (div_of (P - 35) 5 w rho Hrho Hw).
  destruct rho as [|[|[|[|[|rho]]]]]; [| | | | | lia]; cbv beta iota.
  - replace (P - 20) with (5 * w + 15) in HE by lia.
    eapply hc_goal; [eapply evstep_trans; [exact HR | eapply evstep_trans; [exact HE |
      exact (route0 w R (9 + t) [5;4;y;s]%nat (Ll *> const 0))]] | reflexivity | cnt].
  - replace (P - 20) with (5 * w + 16) in HE by lia.
    eapply hc_goal; [eapply evstep_trans; [exact HR | eapply evstep_trans; [exact HE |
      exact (route1 w R (9 + t) [4;y;s]%nat (Ll *> const 0))]] | reflexivity | cnt].
  - replace (P - 20) with (5 * w + 17) in HE by lia.
    eapply hc_goal; [eapply evstep_trans; [exact HR | eapply evstep_trans; [exact HE |
      exact (route2 w R (9 + t) [5;4;y;s]%nat (Ll *> const 0))]] | reflexivity | cnt].
  - replace (P - 20) with (5 * w + 18) in HE by lia.
    eapply hc_goal; [eapply evstep_trans; [exact HR | eapply evstep_trans; [exact HE |
      exact (route3 w R (9 + t) [4;y;s]%nat (Ll *> const 0))]] | reflexivity | cnt].
  - replace (P - 20) with (5 * w + 19) in HE by lia.
    eapply hc_goal; [eapply evstep_trans; [exact HR | eapply evstep_trans; [exact HE |
      exact (route4 w R (9 + t) [5;4;y;s]%nat (Ll *> const 0))]] | reflexivity | cnt].
Qed.

Lemma key37E : forall t P s y m, reachE (mk t 37 P s y m) -> KeyGoal (mk t 37 P s y m).
Proof.
  intros t P s y m [Ll [HR [Hm [Hy [HP _]]]]]. cbn [ct cL cP cs cy cm] in *. pose proof Pm_ge.
  unfold KeyGoal, sig_key. cbn [ct cL cP cs cy cm]. change (37 =? 31) with false. change (37 =? 37) with true.
  cbv iota. unfold sig37.
  set (Ll' := [0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
  assert (HS : D0f t 38 P s y (Ll *> const 0) -->+ D0f (3 + t) 14 (P - 4) 2 (S 7) (Ll' *> const 0)).
  { unfold Ll'. rewrite !Str_app_assoc. exact (AbsSUB3 4 P s t y (Ll *> const 0) ltac:(lia)). }
  pose proof (D0f14_exact (3 + t) (P - 4) 2 7 (Ll' *> const 0) ltac:(lia)) as HT.
  replace (P - 4 - 11) with (P - 15) in HT by lia. replace (3 + t + 4) with (t + 7) in HT by lia.
  eapply hc_goal; [eapply evstep_trans; [exact HR | apply progress_evstep; eapply progress_trans; [exact HS | exact HT]]
    | reflexivity | unfold Ll'; cnt].
Qed.

Lemma key43E : forall t P s y m, reachE (mk t 43 P s y m) -> KeyGoal (mk t 43 P s y m).
Proof.
  intros t P s y m [Ll [HR [Hm [Hy [HP _]]]]]. cbn [ct cL cP cs cy cm] in *. pose proof Pm_ge.
  unfold KeyGoal, sig_key. cbn [ct cL cP cs cy cm]. change (43 =? 31) with false. change (43 =? 37) with false.
  change (43 =? 43) with true. cbv iota. unfold sig43.
  set (Ll' := [0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
  assert (HS : D0f t 44 P s y (Ll *> const 0) -->+ D0f (3 + t) 14 (P - 6) 6 (S 9) (Ll' *> const 0)).
  { unfold Ll'. rewrite !Str_app_assoc. exact (AbsSUB4 4 P s t y (Ll *> const 0) ltac:(lia)). }
  pose proof (D0f14_exact (3 + t) (P - 6) 6 9 (Ll' *> const 0) ltac:(lia)) as HT.
  replace (P - 6 - 11) with (P - 17) in HT by lia. replace (3 + t + 4) with (t + 7) in HT by lia.
  eapply hc_goal; [eapply evstep_trans; [exact HR | apply progress_evstep; eapply progress_trans; [exact HS | exact HT]]
    | reflexivity | unfold Ll'; cnt].
Qed.

Lemma key49E : forall t P s y m, reachE (mk t 49 P s y m) -> KeyGoal (mk t 49 P s y m).
Proof.
  intros t P s y m [Ll [HR [Hm [Hy [HP _]]]]]. cbn [ct cL cP cs cy cm] in *. pose proof Pm_ge.
  unfold KeyGoal, sig_key. cbn [ct cL cP cs cy cm]. change (49 =? 31) with false. change (49 =? 37) with false.
  change (49 =? 43) with false. change (49 =? 49) with true. cbv iota. unfold sig49.
  set (Ll' := [0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
  assert (HS : D0f t 50 P s y (Ll *> const 0) -->+ D0f (3 + t) 20 (P - 6) 4 12 (Ll' *> const 0)).
  { unfold Ll'. rewrite !Str_app_assoc. exact (AbsSUB5 6 P s t y (Ll *> const 0) ltac:(lia)). }
  pose proof (D0f20_exact (3 + t) (P - 6) 4 12 (Ll' *> const 0) ltac:(lia)) as HT.
  replace (P - 6 - 12) with (P - 18) in HT by lia. replace (3 + t + 5) with (t + 8) in HT by lia.
  eapply hc_goal; [eapply evstep_trans; [exact HR | apply progress_evstep; eapply progress_trans; [exact HS | exact HT]]
    | reflexivity | unfold Ll'; cnt].
Qed.

Lemma key55E : forall t P s y m, reachE (mk t 55 P s y m) -> KeyGoal (mk t 55 P s y m).
Proof.
  intros t P s y m [Ll [HR [Hm [Hy [HP _]]]]]. cbn [ct cL cP cs cy cm] in *. pose proof Pm_ge.
  unfold KeyGoal, sig_key. cbn [ct cL cP cs cy cm]. change (55 =? 31) with false. change (55 =? 37) with false.
  change (55 =? 43) with false. change (55 =? 49) with false. cbv iota. unfold sig55.
  set (Rs := iter 4 (U 5) O).
  set (Ll' := [0;1]^^s ++ [1] ++ Ll).
  assert (HS : D0f t 56 P s y (Ll *> const 0) -->+ D0f (3 + t) 14 (P - 3) y (S (8 + 6 * Rs)) (Ll' *> const 0)).
  { unfold Ll'. rewrite !Str_app_assoc. replace (S (8 + 6 * Rs)) with (9 + 6 * Rs) by lia.
    exact (step_stopX 1 P s t y (Ll *> const 0) ltac:(lia) Hy). }
  pose proof (D0f14_exact (3 + t) (P - 3) y (8 + 6 * Rs) (Ll' *> const 0) ltac:(lia)) as HT.
  replace (P - 3 - 11) with (P - 14) in HT by lia. replace (3 + t + 4) with (t + 7) in HT by lia.
  eapply hc_goal; [eapply evstep_trans; [exact HR | apply progress_evstep; eapply progress_trans; [exact HS | exact HT]]
    | reflexivity | unfold Ll'; cnt].
Qed.

Lemma keyE : forall x, reachE x -> in_keys (cL x) = true -> KeyGoal x.
Proof.
  intros [t L P s y m] HR HK. cbn [cL] in HK. unfold in_keys in HK.
  repeat (apply orb_true_iff in HK; destruct HK as [HK | HK]); apply Nat.eqb_eq in HK; subst L.
  - apply key31E, HR.
  - apply key37E, HR.
  - apply key43E, HR.
  - apply key49E, HR.
  - apply key55E, HR.
Qed.

(** ** Main results *)
Theorem c04_score_reached : exists c, c0 -->* c /\ halted tm c /\ ones c sigma_c04.
Proof.
  destruct L1_props as [H60 _].
  destruct (run_ok L1 top top_ok H60 (le_n _)) as [HR HK].
  exact (keyE _ HR HK).
Qed.

Theorem c04_score_exact : forall c N, c0 -->* c -> halted tm c -> ones c N -> N = sigma_c04.
Proof.
  intros c N H1 H2 H3. destruct c04_score_reached as [c' [H1' [H2' H3']]].
  pose proof (halted_unique c0 c c' H1 H1' H2 H2') as E. subst c'.
  exact (ones_unique c N sigma_c04 H3 H3').
Qed.

Theorem c04_sigma_bracket : f_omega (f_omega (12 * Bx + 26)) < sigma_c04 /\ sigma_c04 < f_omega (f_omega (12 * Bx + 27)).
Proof.
  destruct c04_score_reached as [c [H1 [H2 H3]]]. exact (c04_fgh_bracket c sigma_c04 H1 H2 H3).
Qed.
