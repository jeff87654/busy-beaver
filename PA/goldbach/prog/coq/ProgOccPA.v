(** * ProgOccPA: the occurs-check gate occgate() of the pagb machine (source_pa.py) on [dagpa].

    occgate() walks the term codes a = param1 and b = param2 with a work list in param1 (items
    stored as code + 1, 0 = end of list), decoding each code by repeated decrement (tag = code mod 4,
    quotient in scratch1), pushing the subterms of σ / ⊕ / ⊗ nodes and comparing variable labels
    with c = axiomcode; on a match topwff := 0.  Result ([occgate277]):
      topwff := 0 if c ∈ vars T(a) ∪ vars T(b) (PA_Codes.occT), unchanged otherwise;
      param1 = param2 = axiomcode = 0; scratch1 = scratch2 = 0 preserved. *)
From Coq Require Import Lists.List Arith.Arith Lia Bool.Bool.
From PAGBT Require Import RM DagPA.
From PAGBP Require Import ProgCodesPA ProgLibPA.
From PAGB Require Import PALogic PA_dB.
Import ListNotations.
Unset Implicit Arguments.

Opaque P.

(** ** pair(out, in1, in2): out += P in1 in2; in1, in2 := 0 *)
(* pair(scratch1, param2, param1) *)
Lemma pair304 m :
  sem (ENode 304) m XNormal (set (set (set m 6 (get m 6 + P (get m 5) (get m 4))) 5 0) 4 0).
Proof.
  revert m. cut (forall k m, get m 5 + get m 4 = k ->
    sem (ENode 304) m XNormal (set (set (set m 6 (get m 6 + P (get m 5) (get m 4))) 5 0) 4 0)).
  { intros H m; apply (H _ m eq_refl). }
  induction k as [|k IH]; intros m Hk.
  - eapply sem_cdr_normal; [reflexivity | apply w350 |].
    eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero] |];
      destruct m as [a0 a1 a2 a3 a4 a5 a6 a7 a8]; nrm; [lia|].
    assert (a5 = 0) by lia. assert (a4 = 0) by lia. subst. reflexivity.
  - eapply sem_cdr_continue1; [reflexivity | apply w350 | |].
    + eapply sem_cdr_continueS with (k := 0);
        [reflexivity | apply sem_decnz_pos with (v := k); [lia | destruct m; nrm; lia] |].
      eapply sem_cdr_continueS with (k := 1); [reflexivity | | apply sem_cont].
      eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia | apply w354].
    + eapply sem_conseq; [apply IH; destruct m; nrm; lia |].
      destruct m as [a0 a1 a2 a3 a4 a5 a6 a7 a8]; nrm. f_equal; try lia.
      rewrite (pair_step a5 a4 k) by lia. rewrite ?Nat.add_0_l, ?Nat.add_0_r. lia.
Qed.

(* pair(scratch1, param1, scratch2) *)
Lemma pair300 m :
  sem (ENode 300) m XNormal (set (set (set m 6 (get m 6 + P (get m 4) (get m 7))) 4 0) 7 0).
Proof.
  revert m. cut (forall k m, get m 4 + get m 7 = k ->
    sem (ENode 300) m XNormal (set (set (set m 6 (get m 6 + P (get m 4) (get m 7))) 4 0) 7 0)).
  { intros H m; apply (H _ m eq_refl). }
  induction k as [|k IH]; intros m Hk.
  - eapply sem_cdr_normal; [reflexivity | apply w368 |].
    eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero] |];
      destruct m as [a0 a1 a2 a3 a4 a5 a6 a7 a8]; nrm; [lia|].
    assert (a4 = 0) by lia. assert (a7 = 0) by lia. subst. reflexivity.
  - eapply sem_cdr_continue1; [reflexivity | apply w368 | |].
    + eapply sem_cdr_continueS with (k := 0);
        [reflexivity | apply sem_decnz_pos with (v := k); [lia | destruct m; nrm; lia] |].
      eapply sem_cdr_continueS with (k := 1); [reflexivity | | apply sem_cont].
      eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia | apply w347].
    + eapply sem_conseq; [apply IH; destruct m; nrm; lia |].
      destruct m as [a0 a1 a2 a3 a4 a5 a6 a7 a8]; nrm. f_equal; try lia.
      rewrite (pair_step a4 a7 k) by lia. rewrite ?Nat.add_0_l, ?Nat.add_0_r. lia.
Qed.

(* pair(param1, param2, scratch1) *)
Lemma pair296 m :
  sem (ENode 296) m XNormal (set (set (set m 4 (get m 4 + P (get m 5) (get m 6))) 5 0) 6 0).
Proof.
  revert m. cut (forall k m, get m 5 + get m 6 = k ->
    sem (ENode 296) m XNormal (set (set (set m 4 (get m 4 + P (get m 5) (get m 6))) 5 0) 6 0)).
  { intros H m; apply (H _ m eq_refl). }
  induction k as [|k IH]; intros m Hk.
  - eapply sem_cdr_normal; [reflexivity | apply w358 |].
    eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero] |];
      destruct m as [a0 a1 a2 a3 a4 a5 a6 a7 a8]; nrm; [lia|].
    assert (a5 = 0) by lia. assert (a6 = 0) by lia. subst. reflexivity.
  - eapply sem_cdr_continue1; [reflexivity | apply w358 | |].
    + eapply sem_cdr_continueS with (k := 0);
        [reflexivity | apply sem_decnz_pos with (v := k); [lia | destruct m; nrm; lia] |].
      eapply sem_cdr_continueS with (k := 1); [reflexivity | | apply sem_cont].
      eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia | apply w355].
    + eapply sem_conseq; [apply IH; destruct m; nrm; lia |].
      destruct m as [a0 a1 a2 a3 a4 a5 a6 a7 a8]; nrm. f_equal; try lia.
      rewrite (pair_step a5 a6 k) by lia. rewrite ?Nat.add_0_l, ?Nat.add_0_r. lia.
Qed.

(** ** unpair(out1, out2, in) *)
(* body of unpair(param2, scratch1, param1) *)
Lemma ubody202 m : sem (ENode 202) m (XContinue 1) (ustep 5 6 m).
Proof.
  eapply sem_cdr_continueS with (k := 0); [reflexivity | | apply sem_cont].
  eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia |].
  destruct (get m 5) as [|v] eqn:Hv.
  - eapply sem_cdr_normal; [reflexivity | eapply sem_car_break1; [reflexivity|] | ].
    + apply sem_decnz_zero. destruct m; nrm; exact Hv.
    + eapply sem_conseq; [apply w365|]. destruct m; nrm; subst; cbn [unP_step fst snd]. f_equal; lia.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity|] |].
    + eapply sem_cdr_break with (k := 0); [reflexivity | | apply sem_breakS].
      apply sem_decnz_pos with (v := v); [lia | destruct m; nrm; exact Hv].
    + destruct m; nrm; subst; reflexivity.
Qed.

(* body of unpair(param2, scratch2, scratch1) *)
Lemma ubody213 m : sem (ENode 213) m (XContinue 1) (ustep 5 7 m).
Proof.
  eapply sem_cdr_continueS with (k := 0); [reflexivity | | apply sem_cont].
  eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia |].
  destruct (get m 5) as [|v] eqn:Hv.
  - eapply sem_cdr_normal; [reflexivity | eapply sem_car_break1; [reflexivity|] | ].
    + apply sem_decnz_zero. destruct m; nrm; exact Hv.
    + eapply sem_conseq; [apply w372|]. destruct m; nrm; subst; cbn [unP_step fst snd]. f_equal; lia.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity|] |].
    + eapply sem_cdr_break with (k := 0); [reflexivity | | apply sem_breakS].
      apply sem_decnz_pos with (v := v); [lia | destruct m; nrm; exact Hv].
    + destruct m; nrm; subst; reflexivity.
Qed.

Ltac unpair_tac' B :=
  intros m; eapply (sem_while _ _ _ _ (unpair_post _ _ _));
  [ reflexivity | lia | apply B | clear m; intros m; destruct m; reflexivity
  | clear m; intros m H0; destruct m; unfold unpair_post; nrm; subst; reflexivity
  | clear m; intros m v Hv; destruct m; unfold unpair_post; nrm; subst;
    rewrite Nat.iter_succ_r, <- surjective_pairing; reflexivity ].

(* unpair(param2, scratch1, param1) *)
Lemma unpair201 m : sem (ENode 201) m XNormal (unpair_post 4 5 6 m).
Proof. revert m; unpair_tac' ubody202. Qed.
(* unpair(param2, scratch2, scratch1) *)
Lemma unpair212 m : sem (ENode 212) m XNormal (unpair_post 6 5 7 m).
Proof. revert m; unpair_tac' ubody213. Qed.

(** ** if_eq(param2, scratch1, topwff := 0) *)
Definition clr' (m : St) : St := set (set m 5 0) 6 0.

Lemma loop224 x : forall m, get m 5 = x ->
  (x <= get m 6 -> sem (ENode 224) m XNormal (set (set m 5 0) 6 (get m 6 - x))) /\
  (get m 6 < x -> sem (ENode 224) m XNormal (set (set m 5 0) 6 (x - get m 6))).
Proof.
  induction x as [|x IH]; intros m Hx; split; intros Hle.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; exact Hx]|].
    destruct m; nrm; subst; f_equal; lia.
  - lia.
  - destruct (get m 6) as [|y] eqn:Hy; [lia|].
    eapply sem_cdr_continue1; [reflexivity | apply sem_decnz_pos; [lia | exact Hx] | |].
    + eapply sem_car_continue with (k := 0); [reflexivity|].
      eapply sem_cdr_continueS with (k := 0); [reflexivity | | apply sem_cont].
      apply sem_decnz_pos with (v := y); [lia | destruct m; nrm; exact Hy].
    + eapply sem_conseq;
        [apply (proj1 (IH (set (set m 5 x) 6 y) ltac:(destruct m; reflexivity))); destruct m; nrm; lia|].
      destruct m; nrm; subst; f_equal; lia.
  - destruct (get m 6) as [|y] eqn:Hy.
    + eapply sem_conseq.
      * eapply sem_cdr_normal; [reflexivity | apply sem_decnz_pos; [lia | exact Hx] |].
        eapply sem_cdr_normal; [reflexivity | |].
        -- eapply sem_car_break1; [reflexivity|]. apply sem_decnz_zero. destruct m; nrm; exact Hy.
        -- eapply sem_cdr_normal; [reflexivity | apply w355 | apply sem_inc; lia].
      * destruct m; nrm; subst; f_equal; lia.
    + eapply sem_cdr_continue1; [reflexivity | apply sem_decnz_pos; [lia | exact Hx] | |].
      * eapply sem_car_continue with (k := 0); [reflexivity|].
        eapply sem_cdr_continueS with (k := 0); [reflexivity | | apply sem_cont].
        apply sem_decnz_pos with (v := y); [lia | destruct m; nrm; exact Hy].
      * eapply sem_conseq;
          [apply (proj2 (IH (set (set m 5 x) 6 y) ltac:(destruct m; reflexivity))); destruct m; nrm; lia|].
        destruct m; nrm; subst; f_equal; lia.
Qed.

Lemma if223_eq m : get m 5 = get m 6 -> sem (ENode 223) m XNormal (clr' m).
Proof.
  intros H. destruct (loop224 (get m 5) m eq_refl) as [H1 _].
  eapply sem_cdr_normal; [reflexivity | apply H1; lia |].
  eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero]|].
  - destruct m; nrm; lia.
  - unfold clr'; destruct m; nrm; f_equal; lia.
Qed.

Lemma if223_neq m : get m 5 <> get m 6 -> sem (ENode 223) m (XBreak 1) (clr' m).
Proof.
  intros H. destruct (loop224 (get m 5) m eq_refl) as [H1 H2].
  assert (Hl : exists d, sem (ENode 224) m XNormal (set (set m 5 0) 6 (S d))).
  { destruct (Nat.lt_ge_cases (get m 6) (get m 5)) as [Hlt | Hge].
    - exists (get m 5 - get m 6 - 1).
      replace (S (get m 5 - get m 6 - 1)) with (get m 5 - get m 6) by lia. apply H2, Hlt.
    - exists (get m 6 - get m 5 - 1).
      replace (S (get m 6 - get m 5 - 1)) with (get m 6 - get m 5) by lia. apply H1, Hge. }
  destruct Hl as [d Hd].
  eapply sem_cdr_break with (k := 0); [reflexivity | exact Hd |].
  eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos with (v := d);
    [lia | destruct m; reflexivity] |].
  eapply sem_conseq; [eapply sem_cdr_break with (k := 0); [reflexivity | apply w357 | apply sem_breakS]|].
  unfold clr'; destruct m; nrm; reflexivity.
Qed.

Lemma ifeq222 m : sem (ENode 222) m XNormal
  (set (clr' m) 1 (if Nat.eqb (get m 5) (get m 6) then 0 else get m 1)).
Proof.
  destruct (Nat.eqb_spec (get m 5) (get m 6)) as [H | H].
  - eapply sem_cdr_normal; [reflexivity | apply if223_eq, H |].
    eapply sem_conseq; [apply w378|]. unfold clr'; destruct m; reflexivity.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply if223_neq, H]|].
    unfold clr'; destruct m; reflexivity.
Qed.

Ltac elemO := match goal with
  | |- sem (ENode 304) _ _ _ => apply pair304
  | |- sem (ENode 300) _ _ _ => apply pair300
  | |- sem (ENode 296) _ _ _ => apply pair296
  | |- sem (ENode 201) _ _ _ => apply unpair201
  | |- sem (ENode 212) _ _ _ => apply unpair212
  | |- sem (ENode 222) _ _ _ => apply ifeq222
  end.
Ltac elem ::= first [elemO | elem8 | elem7 | elem6 | elem5 | elem4 | elem3 | elem2 | elem1 | elem0].
Ltac nrm ::= cbn [get set inc ustep unpair_post clr clr'] in *.

(** ** The small subroutines of the walk *)
(* occ_pop(): (param2, rest) := unP param1 *)
Lemma pop276 m : get m 5 = 0 -> get m 6 = 0 ->
  sem (ENode 276) m XNormal (set (set m 5 (fst (unP (get m 4)))) 4 (snd (unP (get m 4)))).
Proof. revert m; start; run_seq; fin. Qed.

(* occ_push_j(): param1 := P (S param2) param1; param2 := 0 *)
Lemma push199 m : get m 6 = 0 ->
  sem (ENode 199) m XNormal (set (set m 4 (P (S (get m 5)) (get m 4))) 5 0).
Proof. revert m; start; run_seq; fin. Qed.

(* occ_init(): param1 := [param2; param1] (as P (S b) (P (S a) 0)); param2 := 0 *)
Lemma init273 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 273) m XNormal (set (set m 4 (P (S (get m 5)) (P (S (get m 4)) 0))) 5 0).
Proof. revert m; start; run_seq; fin. Qed.

(** ** The three handlers (entry: param2 = 0, scratch2 = 0, scratch1 = q = P j k) *)
Definition hsigf (m : St) : St := set (set m 4 (P (S (fst (unP (get m 6)))) (get m 4))) 6 0.
Definition hbinf (m : St) : St :=
  set (set m 4 (P (S (snd (unP (get m 6)))) (P (S (fst (unP (get m 6)))) (get m 4)))) 6 0.
Definition hvarf (m : St) : St :=
  set (set m 1 (if Nat.eqb (fst (unP (get m 6))) (get m 3) then 0 else get m 1)) 6 0.

Ltac elemO2 := match goal with
  | |- sem (ENode 199) _ _ _ => eapply push199; side
  | |- sem (ENode 276) _ _ _ => eapply pop276; side
  | |- sem (ENode 273) _ _ _ => eapply init273; side
  end.
Ltac elem ::= first [elemO2 | elemO | elem8 | elem7 | elem6 | elem5 | elem4 | elem3 | elem2 | elem1 | elem0].

Lemma hsig269 m : get m 5 = 0 -> get m 7 = 0 -> sem (ENode 269) m XNormal (hsigf m).
Proof. unfold hsigf. revert m; start; run_seq; fin. Qed.

Lemma hbin266 m : get m 5 = 0 -> get m 7 = 0 -> sem (ENode 266) m XNormal (hbinf m).
Proof. unfold hbinf. revert m; start; run_seq; fin. Qed.

Lemma hvar270 m : get m 5 = 0 -> get m 7 = 0 -> sem (ENode 270) m XNormal (hvarf m).
Proof. unfold hvarf. revert m; start; run_seq; fin. Qed.

(** ** The decoding loop dm (node 285, inside node 284): param2 = 4 n + r is reduced to 0 by
    repeated decrement, scratch1 counts the quotient; then the handler for the tag r runs. *)
Lemma dm285 n : forall m r, r < 4 -> get m 5 = 4 * n + r -> get m 7 = 0 ->
  let m0 := set (set m 5 0) 6 (get m 6 + n) in
  (r = 0 -> sem (ENode 285) m XNormal m0) /\
  (r = 1 \/ r = 2 -> sem (ENode 285) m (XBreak 1) (hbinf m0)) /\
  (r = 3 -> sem (ENode 285) m (XBreak 1) (hvarf m0)).
Proof.
  induction n as [|n IH]; intros m r Hr Hx H7 m0.
  - rewrite Nat.mul_0_r, Nat.add_0_l in Hx.
    assert (E0 : m0 = set m 5 0) by (unfold m0; destruct m; nrm; subst; f_equal; lia).
    split; [|split].
    + intros ->. rewrite E0. eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; exact Hx]|].
      destruct m; nrm; subst; reflexivity.
    + intros [-> | ->].
      * eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos with (v := 0); [lia | exact Hx] |].
        eapply sem_cdr_break with (k := 0); [reflexivity | |].
        -- eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; destruct m; reflexivity].
        -- eapply sem_cdr_break with (k := 0); [reflexivity | | apply sem_breakS].
           rewrite E0. apply hbin266; destruct m; nrm; auto.
      * eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos with (v := 1); [lia | exact Hx] |].
        eapply sem_car_breakS with (k := 0); [reflexivity|].
        eapply sem_cdr_break with (k := 1); [reflexivity | apply sem_decnz_pos with (v := 0); [lia | destruct m; reflexivity] |].
        eapply sem_cdr_break with (k := 1); [reflexivity | |].
        -- eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; destruct m; reflexivity].
        -- eapply sem_cdr_break with (k := 1); [reflexivity | | apply sem_breakS].
           eapply sem_conseq; [apply hbin266; destruct m; nrm; auto|]. rewrite E0. destruct m; nrm; reflexivity.
    + intros ->.
      eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos with (v := 2); [lia | exact Hx] |].
      eapply sem_car_breakS with (k := 0); [reflexivity|].
      eapply sem_cdr_break with (k := 1); [reflexivity | apply sem_decnz_pos with (v := 1); [lia | destruct m; reflexivity] |].
      eapply sem_car_breakS with (k := 1); [reflexivity|].
      eapply sem_cdr_break with (k := 2); [reflexivity | apply sem_decnz_pos with (v := 0); [lia | destruct m; reflexivity] |].
      eapply sem_cdr_break with (k := 2); [reflexivity | |].
      * eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; destruct m; reflexivity].
      * eapply sem_cdr_break with (k := 2); [reflexivity | | apply sem_breakS].
        eapply sem_conseq; [apply hvar270; destruct m; nrm; auto|]. rewrite E0. destruct m; nrm; reflexivity.
  - set (x := 4 * n + r).
    assert (Hx' : get m 5 = S (S (S (S x)))) by (unfold x; lia).
    set (m4 := set (set m 5 x) 6 (S (get m 6))).
    destruct (IH m4 r Hr ltac:(unfold m4; destruct m; reflexivity) ltac:(unfold m4; destruct m; nrm; exact H7))
      as (I0 & I12 & I3).
    assert (E : set (set m4 5 0) 6 (get m4 6 + n) = m0).
    { unfold m4, m0. destruct m; nrm; f_equal; lia. }
    cbv zeta in I0, I12, I3. rewrite E in I0, I12, I3.
    (* one full iteration, then the restart of node 285 *)
    assert (It : sem (ENode 286) (set m 5 (S (S (S x)))) (XContinue 1) m4).
    { eapply sem_car_continue with (k := 0); [reflexivity|].
      eapply sem_cdr_continueS with (k := 0); [reflexivity | apply sem_decnz_pos with (v := S (S x)); [lia | destruct m; reflexivity] |].
      eapply sem_car_continue with (k := 1); [reflexivity|].
      eapply sem_cdr_continueS with (k := 1); [reflexivity | apply sem_decnz_pos with (v := S x); [lia | destruct m; reflexivity] |].
      eapply sem_car_continue with (k := 2); [reflexivity|].
      eapply sem_cdr_continueS with (k := 2); [reflexivity | apply sem_decnz_pos with (v := x); [lia | destruct m; reflexivity] |].
      eapply sem_conseq; [eapply sem_cdr_continueS with (k := 3); [reflexivity | apply sem_inc; lia | apply sem_cont]|].
      unfold m4. destruct m; nrm; reflexivity. }
    split; [|split].
    + intros Hr0. eapply sem_cdr_continue1; [reflexivity | apply sem_decnz_pos with (v := S (S (S x))); [lia | exact Hx'] | exact It | apply I0, Hr0].
    + intros Hr12. eapply sem_cdr_continue1; [reflexivity | apply sem_decnz_pos with (v := S (S (S x))); [lia | exact Hx'] | exact It | apply I12, Hr12].
    + intros Hr3. eapply sem_cdr_continue1; [reflexivity | apply sem_decnz_pos with (v := S (S (S x))); [lia | exact Hx'] | exact It | apply I3, Hr3].
Qed.

(** ** One item: decode the code t > 0 and run its handler *)
Definition dmres (t : nat) (m : St) : St :=
  let m0 := set (set m 5 0) 6 (t / 4) in
  match dtag t with 0 => hsigf m0 | 1 | 2 => hbinf m0 | _ => hvarf m0 end.

Lemma dm284 t m : 0 < t -> get m 5 = t -> get m 6 = 0 -> get m 7 = 0 -> sem (ENode 284) m XNormal (dmres t m).
Proof.
  intros Ht H5 H6 H7. destruct (code_split t) as [Et Hr]. unfold dmres.
  assert (Hdiv : t / 4 = P (dx t) (dy t)).
  { unfold dx, dy. Transparent P. rewrite P_unP. Opaque P. reflexivity. }
  assert (Hm : t = 4 * (t / 4) + dtag t).
  { unfold dtag. pose proof (Nat.div_mod t 4 ltac:(lia)). lia. }
  destruct (dm285 (t / 4) m (dtag t) Hr ltac:(lia) H7) as (D0 & D12 & D3).
  assert (E : set (set m 5 0) 6 (get m 6 + t / 4) = set (set m 5 0) 6 (t / 4)) by (rewrite H6; reflexivity).
  cbv zeta in D0, D12, D3. rewrite E in D0, D12, D3.
  destruct (dtag t) as [|[|[|[|r]]]] eqn:Ed; try lia.
  - eapply sem_cdr_normal; [reflexivity | apply D0; reflexivity |].
    apply hsig269; destruct m; nrm; auto.
  - eapply sem_car_break1; [reflexivity | apply D12; auto].
  - eapply sem_car_break1; [reflexivity | apply D12; auto].
  - eapply sem_car_break1; [reflexivity | apply D3; auto].
Qed.

(** ** The walk over the work list *)
Fixpoint penc (l : list nat) : nat := match l with [] => 0 | t :: l => P (S t) (penc l) end.
Fixpoint wt (l : list nat) : nat := match l with [] => 0 | t :: l => 2 * t + 1 + wt l end.

Lemma tri_ge n : n <= tri n.
Proof. induction n; cbn; lia. Qed.

Lemma P_ge_sum a b : a + b <= P a b.
Proof. Transparent P. unfold P. pose proof (tri_ge (a + b)). lia. Opaque P. Qed.

Lemma occT_unfold c t : 0 < t -> occT c t =
  match dtag t with
  | 0 => occT c (dx t)
  | 1 | 2 => occT c (dx t) || occT c (dy t)
  | _ => Nat.eqb (dx t) c
  end.
Proof.
  intro Ht. rewrite !occT_spec, T_unfold by exact Ht.
  destruct (dtag t) as [|[|[|]]]; cbn [tocc]; reflexivity.
Qed.

Lemma occT_0 c : occT c 0 = false.
Proof. reflexivity. Qed.

Lemma walk279 k : forall l m, wt l <= k -> get m 4 = penc l -> get m 5 = 0 -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 279) m XNormal (set (set m 4 0) 1 (if existsb (occT (get m 3)) l then 0 else get m 1)).
Proof.
  induction k as [|k IH]; intros l m Hk H4 H5 H6 H7.
  - (* the empty list *)
    destruct l as [|t l]; [|cbn in Hk; lia]. cbn in H4.
    eapply sem_cdr_normal; [reflexivity | apply pop276; auto |].
    eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero]|];
      destruct m; nrm; subst; reflexivity.
  - destruct l as [|t l].
    + cbn in H4. eapply sem_cdr_normal; [reflexivity | apply pop276; auto |].
      eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero]|];
        destruct m; nrm; subst; reflexivity.
    + cbn [penc] in H4. set (c := get m 3).
      set (mp := set (set m 5 (S t)) 4 (penc l)).
      assert (Hpop : sem (ENode 276) m XNormal mp).
      { eapply sem_conseq; [apply pop276; auto|]. unfold mp. rewrite H4. Transparent P. rewrite unP_P. Opaque P. reflexivity. }
      set (mi := set mp 5 t).
      (* the item, run from mi (param2 = t, scratch1 = scratch2 = 0) *)
      assert (Hitem : exists l' m', sem (ENode 282) mi XNormal m' /\ wt l' < wt (t :: l) /\
                get m' 4 = penc l' /\ get m' 5 = 0 /\ get m' 6 = 0 /\ get m' 7 = 0 /\ get m' 3 = c /\
                set (set m' 4 0) 1 (if existsb (occT c) l' then 0 else get m' 1) =
                set (set m 4 0) 1 (if existsb (occT c) (t :: l) then 0 else get m 1)).
      { destruct t as [|t0].
        - exists l, mi. split; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; unfold mi, mp; destruct m; reflexivity]|].
          cbn [wt]. unfold mi, mp, c. destruct m; nrm; subst. repeat split; try lia; try reflexivity.
        - set (t := S t0).
          assert (Hd : sem (ENode 282) mi XNormal (dmres t mi)).
          { eapply sem_cdr_normal; [reflexivity | apply sem_decnz_pos with (v := t0); [lia | unfold mi, mp; destruct m; reflexivity] |].
            eapply sem_cdr_normal; [reflexivity | apply sem_inc; lia |].
            eapply sem_conseq; [apply (dm284 t); [unfold t; lia | | |]; unfold mi, mp; destruct m; nrm; subst; auto|].
            unfold mi, mp, t. destruct m; nrm; reflexivity. }
          assert (Hlt : 0 < t) by (unfold t; lia).
          pose proof (dx_lt t Hlt) as Hdx. pose proof (dy_lt t Hlt) as Hdy.
          destruct (code_split t) as [Et Hr].
          assert (Hdiv : t / 4 = P (dx t) (dy t)).
          { unfold dx, dy. Transparent P. rewrite P_unP. Opaque P. reflexivity. }
          assert (Hsum : dx t + dy t <= t / 4) by (rewrite Hdiv; apply P_ge_sum).
          assert (Hun : unP (t / 4) = (dx t, dy t)) by (unfold dx, dy; apply surjective_pairing).
          pose proof (occT_unfold c t Hlt) as Ho.
          unfold dmres in Hd. destruct (dtag t) as [|[|[|[|r]]]] eqn:Ed; try lia.
          + exists (dx t :: l), (hsigf (set (set mi 5 0) 6 (t / 4))). split; [exact Hd|].
            unfold hsigf, mi, mp, c in *. destruct m; nrm; subst. rewrite Hun. cbn [fst snd wt penc existsb].
            repeat split; try lia; try (rewrite Ho; reflexivity).
          + exists (dy t :: dx t :: l), (hbinf (set (set mi 5 0) 6 (t / 4))). split; [exact Hd|].
            unfold hbinf, mi, mp, c in *. destruct m; nrm; subst. rewrite Hun. cbn [fst snd wt penc existsb].
            repeat split; try lia; try (rewrite Ho; destruct (occT _ (dx t)), (occT _ (dy t)); reflexivity).
          + exists (dy t :: dx t :: l), (hbinf (set (set mi 5 0) 6 (t / 4))). split; [exact Hd|].
            unfold hbinf, mi, mp, c in *. destruct m; nrm; subst. rewrite Hun. cbn [fst snd wt penc existsb].
            repeat split; try lia; try (rewrite Ho; destruct (occT _ (dx t)), (occT _ (dy t)); reflexivity).
          + exists l, (hvarf (set (set mi 5 0) 6 (t / 4))). split; [exact Hd|].
            unfold hvarf, mi, mp, c in *. destruct m; nrm; subst. rewrite Hun. cbn [fst snd wt penc existsb].
            repeat split; try lia; try (rewrite Ho; destruct (Nat.eqb (dx t) _), (existsb _ l); reflexivity). }
      destruct Hitem as (l' & m' & Hi & Hw & H4' & H5' & H6' & H7' & H3' & Eq).
      rewrite <- Eq.
      eapply sem_cdr_continue1; [reflexivity | exact Hpop | |].
      * eapply sem_cdr_continueS with (k := 0);
          [reflexivity | apply sem_decnz_pos with (v := t); [lia | unfold mp; destruct m; reflexivity] |].
        eapply sem_cdr_continueS with (k := 1); [reflexivity | exact Hi | apply sem_cont].
      * rewrite <- H3'. apply (IH l'); auto. cbn [wt] in Hk, Hw. lia.
Qed.

(** ** The gate *)
Lemma occgate277 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 277) m XNormal
    (set (set (set (set m 1 (if occT (get m 3) (get m 5) || occT (get m 3) (get m 4) then 0 else get m 1)) 4 0) 5 0) 3 0).
Proof.
  intros H6 H7. eapply sem_cdr_normal; [reflexivity | apply init273; auto |].
  eapply sem_cdr_normal; [reflexivity | |].
  - apply (walk279 (wt [get m 5; get m 4]) [get m 5; get m 4]); [lia | | | |]; destruct m; nrm; auto.
  - eapply sem_conseq; [apply w341|]. destruct m; nrm. cbn [existsb]. rewrite orb_false_r. reflexivity.
Qed.
