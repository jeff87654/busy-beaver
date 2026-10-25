(** * PA_Rows: the machine's AX roots (design A, zf/pagb/machine/search_a.py) as code ASTs, their
    decoding, and the soundness of every vacuity-independent root in [pprov X].

    [fa]/[ta] are formula/term ASTs whose leaves are parameter codes; [cd] computes the machine code
    (the code functions of zf/pagb/machine/spec_pa.py: ¬A = A -> F, F = 1), [dw] the intended named
    wff.  [D_cd]: the decoder [D] of a code is pprov-equivalent to the intended wff (the only
    discrepancies are Imp(0,0) = 0 = truth and A -> F vs ¬A).
    Rows covered: GEN, L, QI, COMM, B6c, Euclid, Cσ, C⊕1, C⊕2, C⊗1, C⊗2, ρ1, EX, the six Q rows
    (labels x, y arbitrary), NG (= NGw), and IND (gated, c <> a).  Vacuity rows: not here. *)
From Coq Require Import Arith Lia List Bool.
From PAGB Require Import PALogic PA_dB PA_LProp PA_LMeta PA_tr PA_H PA_Ind PA_Codes.
Import ListNotations.
Unset Implicit Arguments.

(** ** ASTs *)
Inductive ta : Type :=
  | AT (n : nat)              (* term parameter: the term code n *)
  | AV (i : nat)              (* v_i *)
  | AZ
  | AS (t : ta)
  | APl (t s : ta)
  | AMl (t s : ta).

Inductive fa : Type :=
  | AF (n : nat)              (* formula parameter: the formula code n *)
  | AImp (a b : fa)
  | ANot (a : fa)             (* a -> F *)
  | AAll (x : nat) (a : fa)
  | AEq (t s : ta)
  | AFalse.                   (* F = code 1 = S0 == 0 *)

Fixpoint cdt (t : ta) : nat :=
  match t with
  | AT n => n
  | AV i => tvar i
  | AZ => 0
  | AS t => tsc (cdt t)
  | APl t s => tpl (cdt t) (cdt s)
  | AMl t s => tml (cdt t) (cdt s)
  end.

Fixpoint cd (a : fa) : nat :=
  match a with
  | AF n => n
  | AImp a b => wim (cd a) (cd b)
  | ANot a => wn (cd a)
  | AAll x a => wal x (cd a)
  | AEq t s => weq (cdt t) (cdt s)
  | AFalse => F
  end.

Fixpoint dwt (t : ta) : tm :=
  match t with
  | AT n => T n
  | AV i => TV i
  | AZ => TZ
  | AS t => TS (dwt t)
  | APl t s => TP (dwt t) (dwt s)
  | AMl t s => TM (dwt t) (dwt s)
  end.

Definition FF : wff := Weq (TS TZ) TZ.

Fixpoint dw (a : fa) : wff :=
  match a with
  | AF n => D n
  | AImp a b => Wim (dw a) (dw b)
  | ANot a => Wn (dw a)
  | AAll x a => Wal x (dw a)
  | AEq t s => Weq (dwt t) (dwt s)
  | AFalse => FF
  end.

Definition AEx (x : nat) (a : fa) : fa := ANot (AAll x (ANot a)).
Definition AAnd (a b : fa) : fa := ANot (AImp a (ANot b)).
Definition AOr (a b : fa) : fa := AImp (ANot a) b.

Lemma T_cdt t : T (cdt t) = dwt t.
Proof.
  induction t; cbn [cdt dwt]; [reflexivity | apply T_tvar | reflexivity | | |].
  - now rewrite T_tsc, IHt.
  - now rewrite T_tpl, IHt1, IHt2.
  - now rewrite T_tml, IHt1, IHt2.
Qed.

Section Dec.
Variable X : wff -> Prop.
Local Notation lprov := (pprov X).
Local Notation leqv := (leqv X).
Let LDET := DET X.

Lemma lnot_FF : lprov (Wn FF).
Proof.
  assert (H : lprov (Wn (Weq TZ (TS TZ)))).
  { refine (LDET _ _ (lspec X 0 TZ QZS eq_refl eq_refl _) (GEN X 0 _ (AZS X))). intros v Hv; discriminate. }
  exact (LDET _ _ (lcontra X _ _ (leq_sym X (TS TZ) TZ)) H).
Qed.

Lemma leqv_imF a : leqv (Wim a FF) (Wn a).
Proof.
  split.
  - apply der_lprov, ded. apply (dmp _ _ (Wn FF)); [| apply dthm, lnot_FF].
    apply (dmp _ _ (Wim a FF)); [apply dthm, lpc_contra | apply dhyp; simpl; auto].
  - apply der_lprov, ded, ded. apply (dmp _ _ a); [| apply dhyp; simpl; auto].
    apply (dmp _ _ (Wn a)); [| apply dhyp; simpl; auto].
    apply dthm. apply (LDET _ _ (lpc_C X _ _ _)). apply B3.
Qed.

Lemma leqv_al x a b : leqv a b -> leqv (Wal x a) (Wal x b).
Proof. intros [H1 H2]. split; apply lal; assumption. Qed.

Lemma leqv_n a b : leqv a b -> leqv (Wn a) (Wn b).
Proof. intros [H1 H2]. split; apply lcontra; assumption. Qed.

Lemma truth_prov : lprov truth.
Proof. apply leq_refl. Qed.

Lemma leqv_both a b : lprov a -> lprov b -> leqv a b.
Proof. intros Ha Hb. split; exact (LDET _ _ (lpc_K X _ _) Hb) || exact (LDET _ _ (lpc_K X _ _) Ha). Qed.

Lemma D_cd a : leqv (D (cd a)) (dw a).
Proof.
  induction a as [n|a IHa b IHb|a IHa|x a IHa|t s|]; cbn [cd dw].
  - apply leqv_refl.
  - destruct (Nat.eq_dec (cd a) 0) as [Ea|Ea]; [destruct (Nat.eq_dec (cd b) 0) as [Eb|Eb]|].
    + rewrite Ea, Eb. cbn. rewrite Ea in IHa. rewrite Eb in IHb.
      apply leqv_both; [apply truth_prov|].
      destruct IHa as [A1 A2]. destruct IHb as [B1' B2'].
      exact (LDET _ _ (lpc_K X _ _) (LDET _ _ B1' truth_prov)).
    + rewrite D_wim by lia. now apply leqv_im.
    + rewrite D_wim by lia. now apply leqv_im.
  - unfold wn. rewrite D_wim by (unfold F; lia). rewrite D_F.
    eapply leqv_trans; [apply leqv_im; [exact IHa | apply leqv_refl] | apply leqv_imF].
  - rewrite D_wal. now apply leqv_al.
  - rewrite D_weq, !T_cdt. apply leqv_refl.
  - rewrite D_F. apply leqv_refl.
Qed.

Lemma prov_cd a : lprov (dw a) -> lprov (D (cd a)).
Proof. intro H. destruct (D_cd a) as [_ E]. exact (LDET _ _ E H). Qed.

Lemma cd_prov a : lprov (D (cd a)) -> lprov (dw a).
Proof. intro H. destruct (D_cd a) as [E _]. exact (LDET _ _ E H). Qed.
End Dec.

(** ** The rows (a, b, c: parameters; u: literal; x, y: labels of the Q rows) *)
Definition r_L (a b c u : nat) : fa :=
  AImp (AImp (AImp (AF c) (AF u)) (AF a)) (AImp (AImp (AF a) (AF c)) (AImp (AF b) (AF c))).
Definition r_QI (a b c : nat) : fa :=
  AImp (AAll a (AImp (AF b) (AF c))) (AImp (AAll a (AF b)) (AAll a (AF c))).
Definition r_COMM (a b c : nat) : fa := AImp (AAll a (AAll b (AF c))) (AAll b (AAll a (AF c))).
Definition r_B6c (a b : nat) : fa := AImp (AEx a (AAll a (AF b))) (AF b).
Definition r_EUC (a b c : nat) : fa :=
  AImp (AEq (AT c) (AT a)) (AImp (AEq (AT c) (AT b)) (AEq (AT a) (AT b))).
Definition r_CS (a b : nat) : fa := AImp (AEq (AT a) (AT b)) (AEq (AS (AT a)) (AS (AT b))).
Definition r_CA1 (a b c : nat) : fa := AImp (AEq (AT a) (AT b)) (AEq (APl (AT a) (AT c)) (APl (AT b) (AT c))).
Definition r_CA2 (a b c : nat) : fa := AImp (AEq (AT a) (AT b)) (AEq (APl (AT c) (AT a)) (APl (AT c) (AT b))).
Definition r_CM1 (a b c : nat) : fa := AImp (AEq (AT a) (AT b)) (AEq (AMl (AT a) (AT c)) (AMl (AT b) (AT c))).
Definition r_CM2 (a b c : nat) : fa := AImp (AEq (AT a) (AT b)) (AEq (AMl (AT c) (AT a)) (AMl (AT c) (AT b))).
Definition r_R1 (a b : nat) : fa := AEx a (AEq (AV a) (AV b)).
Definition r_EX (c : nat) : fa := AEx (S c) (AEq (AV (S c)) (AT c)).

Definition r_QZS (x : nat) : fa := ANot (AEq AZ (AS (AV x))).
Definition r_QSI (x y : nat) : fa := AImp (AEq (AS (AV x)) (AS (AV y))) (AEq (AV x) (AV y)).
Definition r_QA0 (x : nat) : fa := AEq (APl AZ (AV x)) (AV x).
Definition r_QAS (x y : nat) : fa := AEq (APl (AS (AV x)) (AV y)) (AS (APl (AV x) (AV y))).
Definition r_QM0 (x : nat) : fa := AEq (AMl AZ (AV x)) AZ.
Definition r_QMS (x y : nat) : fa := AEq (AMl (AS (AV x)) (AV y)) (APl (AV y) (AMl (AV x) (AV y))).

Definition r_IND (a c : nat) : fa :=
  AImp (AAll a (AImp (AEq (AV a) AZ) (AF c)))
       (AImp (AAll a (AImp (AF c) (AAll c (AImp (AEq (AV c) (AS (AV a))) (AAll a (AImp (AEq (AV a) (AV c)) (AF c)))))))
             (AAll a (AF c))).

(** the named wff as an AST (for NG: the row is the machine code of NGw) *)
Fixpoint enct (t : tm) : ta :=
  match t with TV i => AV i | TZ => AZ | TS t => AS (enct t) | TP t s => APl (enct t) (enct s) | TM t s => AMl (enct t) (enct s) end.
Fixpoint enc (a : wff) : fa :=
  match a with Weq t s => AEq (enct t) (enct s) | Wim a b => AImp (enc a) (enc b) | Wn a => ANot (enc a) | Wal x a => AAll x (enc a) end.

Lemma dwt_enct t : dwt (enct t) = t.
Proof. induction t; cbn; congruence. Qed.
Lemma dw_enc a : dw (enc a) = a.
Proof. induction a; cbn; rewrite ?dwt_enct; congruence. Qed.

From PAGB Require Import PA_Sound.
Definition r_NG : fa := enc NGw.

(** ** Soundness of the rows *)
Section Sound.
Variable X : wff -> Prop.
Local Notation lprov := (pprov X).
Let LDET := DET X.

Ltac dh := apply dhyp; simpl; tauto.
Ltac dt H := apply dthm; exact H.
Ltac mp a := apply (dmp _ _ a).

Lemma s_L a b c u : lprov (dw (r_L a b c u)).
Proof.
  cbn. set (A := D a). set (B := D b). set (C := D c). set (U := D u).
  apply der_lprov, ded, ded, ded.
  (* G = [B; A -> C; (C -> U) -> A] *)
  mp (Wim (Wn C) C); [dt (B2 X C)|]. apply ded.
  (* ¬C: then C -> U holds, so A, so C *)
  mp A; [dh|]. mp (Wim C U); [dh|]. apply ded. mp C; [| dh].
  mp (Wn C); [| dh]. apply dthm. apply (LDET _ _ (lpc_C X _ _ _)). apply B3.
Qed.

Lemma s_QI a b c : lprov (dw (r_QI a b c)).
Proof. apply B4. Qed.
Lemma s_COMM a b c : lprov (dw (r_COMM a b c)).
Proof. apply B6b. Qed.
Lemma s_B6c a b : lprov (dw (r_B6c a b)).
Proof. apply B6c. Qed.
Lemma s_EUC a b c : lprov (dw (r_EUC a b c)).
Proof. apply E8. Qed.
Lemma s_CS a b : lprov (dw (r_CS a b)).
Proof. apply ES. Qed.
Lemma s_CA1 a b c : lprov (dw (r_CA1 a b c)).
Proof. apply EPl. Qed.
Lemma s_CA2 a b c : lprov (dw (r_CA2 a b c)).
Proof. apply EPr. Qed.
Lemma s_CM1 a b c : lprov (dw (r_CM1 a b c)).
Proof. apply EMl. Qed.
Lemma s_CM2 a b c : lprov (dw (r_CM2 a b c)).
Proof. apply EMr. Qed.

Lemma s_R1 a b : lprov (dw (r_R1 a b)).
Proof.
  cbn. destruct (Nat.eq_dec a b) as [<-|Hab].
  - (* E. a (a = a):  A. a -. a = a  gives  -. y = y  for y <> a *)
    set (y := S a).
    assert (H : lprov (Wim (Wal a (Wn (Weq (TV a) (TV a)))) (sb a (TV y) (Wn (Weq (TV a) (TV a)))))).
    { refine (lspec X a (TV y) (Wn (Weq (TV a) (TV a))) _ eq_refl _).
      - change (Nat.eqb y a = false). apply Nat.eqb_neq. unfold y. lia.
      - intros v _. reflexivity. }
    cbn [sb sbt] in H. rewrite Nat.eqb_refl in H.
    apply der_lprov. mp (Wn (Wn (Weq (TV y) (TV y)))).
    + dt (lcontra X _ _ H).
    + dt (LDET _ _ (lpc_nn_intro X _) (leq_refl X (TV y))).
  - exact (B7v X a b Hab).
Qed.

Lemma s_EX c : lprov (dw (r_EX c)).
Proof.
  unfold r_EX, AEx. cbn [dw dwt]. apply lb7. destruct (tocc (S c) (T c)) eqn:E; [|reflexivity].
  apply T_fresh in E. lia.
Qed.

Fixpoint qf (a : wff) : bool :=
  match a with Weq _ _ => true | Wim a b => qf a && qf b | Wn a => qf a | Wal _ _ => false end.

Lemma qf_bnd v a : qf a = true -> bnd v a = false.
Proof.
  induction a; cbn; intro H; try reflexivity; try discriminate.
  - apply andb_true_iff in H as [H1 H2]. now rewrite IHa1, IHa2.
  - now apply IHa.
Qed.

Lemma qf_sb x s a : qf a = true -> qf (sb x s a) = true.
Proof.
  induction a; cbn; intro H; auto; try discriminate.
  apply andb_true_iff in H as [H1 H2]. now rewrite IHa1, IHa2.
Qed.

Lemma p_inst_t x s a : lprov a -> qf a = true -> tocc x s = false -> lprov (sb x s a).
Proof.
  intros H Hq Hx. refine (LDET _ _ (lspec X x s a Hx (qf_bnd _ _ Hq) _) (GEN X x _ H)).
  intros v _. now apply qf_bnd.
Qed.

(** simultaneous substitution on quantifier-free wffs *)
Fixpoint ssb (e : nat -> tm) (a : wff) : wff :=
  match a with
  | Weq t s => Weq (tsub e t) (tsub e s)
  | Wim a b => Wim (ssb e a) (ssb e b)
  | Wn a => Wn (ssb e a)
  | Wal x a => Wal x a
  end.

Definition e01 (x y : nat) : nat -> tm := fun v => if Nat.eqb v 0 then TV x else if Nat.eqb v 1 then TV y else TV v.

Lemma sbt_4 x y t : (forall v, tocc v t = true -> v <= 1) ->
  sbt (3 + x + y) (TV y) (sbt (2 + x + y) (TV x) (sbt 1 (TV (3 + x + y)) (sbt 0 (TV (2 + x + y)) t)))
  = tsub (e01 x y) t.
Proof.
  induction t as [n| |t IH|t IH r IHr|t IH r IHr]; intro H.
  - assert (Hn : n <= 1) by (apply H; cbn; apply Nat.eqb_refl).
    unfold e01. cbn [tsub].
    destruct n as [|[|n]]; [| | lia]; cbn [sbt];
      repeat (match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); try lia end; cbn [sbt]);
      reflexivity.
  - reflexivity.
  - cbn [sbt tsub]. rewrite IH; [reflexivity|]. exact H.
  - cbn [sbt tsub]. rewrite IH, IHr; [reflexivity | |]; intros v Hv; apply H; cbn; now rewrite Hv, ?orb_true_r.
  - cbn [sbt tsub]. rewrite IH, IHr; [reflexivity | |]; intros v Hv; apply H; cbn; now rewrite Hv, ?orb_true_r.
Qed.

Lemma sb_4 x y a : qf a = true -> (forall v, occ v a = true -> v <= 1) ->
  sb (3 + x + y) (TV y) (sb (2 + x + y) (TV x) (sb 1 (TV (3 + x + y)) (sb 0 (TV (2 + x + y)) a)))
  = ssb (e01 x y) a.
Proof.
  induction a; cbn [sb ssb qf]; intros Hq H; try discriminate.
  - rewrite !sbt_4; [reflexivity | |]; intros v Hv; apply H; cbn; now rewrite Hv, ?orb_true_r.
  - apply andb_true_iff in Hq as [H1 H2]. rewrite IHa1, IHa2; [reflexivity | auto | | auto |];
      intros v Hv; apply H; cbn; now rewrite Hv, ?orb_true_r.
  - now rewrite IHa.
Qed.

Lemma q_inst a x y : lprov a -> qf a = true -> (forall v, occ v a = true -> v <= 1) -> lprov (ssb (e01 x y) a).
Proof.
  intros H Hq Hv. rewrite <- sb_4 by assumption.
  apply p_inst_t; [| repeat apply qf_sb; exact Hq | cbn; apply Nat.eqb_neq; lia].
  apply p_inst_t; [| repeat apply qf_sb; exact Hq | cbn; apply Nat.eqb_neq; lia].
  apply p_inst_t; [| apply qf_sb; exact Hq | reflexivity].
  apply p_inst_t; [exact H | exact Hq | reflexivity].
Qed.

Ltac vars01 := intros v Hv; destruct v as [|[|v]]; [lia | lia | cbn in Hv; discriminate].

Lemma s_QZS x : lprov (dw (r_QZS x)).
Proof. exact (q_inst QZS x x (AZS X) eq_refl ltac:(vars01)). Qed.
Lemma s_QSI x y : lprov (dw (r_QSI x y)).
Proof. exact (q_inst QSI x y (ASI X) eq_refl ltac:(vars01)). Qed.
Lemma s_QA0 x : lprov (dw (r_QA0 x)).
Proof. exact (q_inst QA0 x x (AA0 X) eq_refl ltac:(vars01)). Qed.
Lemma s_QAS x y : lprov (dw (r_QAS x y)).
Proof. exact (q_inst QAS x y (AAS X) eq_refl ltac:(vars01)). Qed.
Lemma s_QM0 x : lprov (dw (r_QM0 x)).
Proof. exact (q_inst QM0 x x (AM0 X) eq_refl ltac:(vars01)). Qed.
Lemma s_QMS x y : lprov (dw (r_QMS x y)).
Proof. exact (q_inst QMS x y (AMS X) eq_refl ltac:(vars01)). Qed.

Lemma s_IND a c : c <> a -> lprov (dw (r_IND a c)).
Proof.
  intro H. apply (lind X a c (D c) H). destruct (occ c (D c)) eqn:E; [|reflexivity].
  apply D_fresh in E. lia.
Qed.

Lemma s_NG : X NGw -> lprov (dw r_NG).
Proof. intro H. unfold r_NG. rewrite dw_enc. now apply HYP. Qed.

Lemma s_GEN a h : lprov (D h) -> lprov (D (wal a h)).
Proof. intro H. rewrite D_wal. now apply GEN. Qed.
End Sound.
