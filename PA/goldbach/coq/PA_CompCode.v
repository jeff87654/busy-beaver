(** * PA_CompCode: completeness of the code-level calculus for the reference calculus:
      pprov {NGw} a  ->  thm (fcode a),   hence   PAeq ⊢TC GC_form -> thm F.
    Propositional axioms from the L row by condensed detachment (PA_CD), ex falso from B6c (as m254
    Comp_Prop254.v); B6a and IND are projections of the gated bundle. *)
From Coq Require Import Arith Lia List Bool.
From PAGB Require Import Spec PA_Pair PALogic PA_dB PA_LMeta PA_Codes PA_Rows PA_Sound PA_Comp PA_Thm PA_CD.
Import ListNotations.
Unset Implicit Arguments.

Lemma thm_K (p q : nat) : thm (wim p (wim q p)).
Proof. exact (cd_16 p q). Qed.
Lemma thm_P (p q : nat) : thm (wim (wim (wim p q) p) p).
Proof. exact (cd_25 p q). Qed.
Lemma thm_B (p q r : nat) : thm (wim (wim p q) (wim (wim q r) (wim p r))).
Proof. exact (cd_91 p q r). Qed.
Lemma thm_S (p q r : nat) : thm (wim (wim p (wim q r)) (wim (wim p q) (wim p r))).
Proof. exact (cd_106 p q r). Qed.

Lemma thm_I p : thm (wim p p).
Proof. exact (T_mp _ _ (thm_K p p) (T_mp _ _ (thm_K p (wim p p)) (thm_S p (wim p p) p))). Qed.

(** ** Derivations with hypotheses *)
Inductive derc (G : list nat) : nat -> Prop :=
  | chyp n : In n G -> derc G n
  | cthm n : thm n -> derc G n
  | cmp a b : derc G (wim a b) -> derc G a -> derc G b.

Lemma cded G h a : derc (h :: G) a -> derc G (wim h a).
Proof.
  induction 1 as [n [<-|Hn] | n Hn | a b _ IH1 _ IH2].
  - apply cthm. apply thm_I.
  - apply (cmp _ n); [apply cthm, thm_K | now apply chyp].
  - apply (cmp _ n); [apply cthm, thm_K | now apply cthm].
  - apply (cmp _ (wim h a)); [|exact IH2].
    apply (cmp _ (wim h (wim a b))); [apply cthm, thm_S | exact IH1].
Qed.

Lemma derc_thm a : derc [] a -> thm a.
Proof. induction 1 as [n [] | n Hn | a b _ IH1 _ IH2]; [exact Hn | exact (T_mp _ _ IH2 IH1)]. Qed.

Lemma derc_weak G G' a : derc G a -> incl G G' -> derc G' a.
Proof.
  intros Hd Hi. induction Hd as [n Hn | n Hn | x y _ IH1 _ IH2];
    [apply chyp; auto | now apply cthm | eapply cmp; eauto].
Qed.

Ltac hyp := apply chyp; simpl; tauto.

Definition wa (a b : nat) : nat := wn (wim a (wn b)).

Lemma thm_F a : thm (wim F a).
Proof.
  apply derc_thm. apply cded.
  apply (cmp _ (cd (AEx 0 (AAll 0 (AF a))))); [apply cthm, (T_B6c 0 a)|].
  cbn [cd AEx]. unfold wn. apply (cmp _ F); [apply cthm, thm_K | hyp].
Qed.

Lemma thm_DNE a : thm (wim (wim (wim a F) F) a).
Proof.
  apply derc_thm. apply cded.
  apply (cmp _ (wim (wim a F) a)); [apply cthm, thm_P|].
  apply cded. apply (cmp _ F); [apply cthm, thm_F|].
  apply (cmp _ (wim a F)); hyp.
Qed.

Lemma derc_andl G a b : derc G (wa a b) -> derc G a.
Proof.
  intro H. apply (cmp _ (wim (wim a F) F)); [apply cthm, thm_DNE|].
  apply cded. apply (cmp _ (wim a (wn b))); [apply (derc_weak _ _ _ H); intros ? ?; simpl; tauto|].
  apply cded. apply (cmp _ F); [apply cthm, thm_F|]. apply (cmp _ a); hyp.
Qed.

Lemma derc_andr G a b : derc G (wa a b) -> derc G b.
Proof.
  intro H. apply (cmp _ (wim (wim b F) F)); [apply cthm, thm_DNE|].
  apply cded. apply (cmp _ (wim a (wn b))); [apply (derc_weak _ _ _ H); intros ? ?; simpl; tauto|].
  apply cded. hyp.
Qed.

Lemma thm_B3 a b : thm (wim a (wim (wim a F) b)).
Proof.
  apply derc_thm. do 2 apply cded.
  apply (cmp _ F); [apply cthm, thm_F|]. apply (cmp _ a); hyp.
Qed.

(** ** Codes of named wffs *)
Lemma tcode_cdt t : tcode t = cdt (enct t).
Proof. induction t; cbn [tcode enct cdt]; unfold tvar, tsc, tpl, tml; congruence. Qed.

Lemma fcode_cd a : fcode a = cd (enc a).
Proof. induction a; cbn [fcode enc cd]; unfold wn, wim, weq, wal, F; rewrite ?tcode_cdt; congruence. Qed.

Lemma T_tcode t : T (tcode t) = t.
Proof. rewrite tcode_cdt, T_cdt. apply dwt_enct. Qed.

Lemma occT_tcode z t : occT z (tcode t) = tocc z t.
Proof. now rewrite occT_spec, T_tcode. Qed.

Lemma bundle_open a b c : gate a b c = true -> bundle a b c = wa (cd (r_IND a c)) (cd (r_VAC a b c)).
Proof. intro G. unfold bundle. rewrite G. reflexivity. Qed.

(** ** The translation of pprov derivations.  Codes are written cd (enc a) (never evaluated:
    concrete codes are huge unary numbers). *)
Notation tau a := (cd (enc a)).

Theorem pprov_thm a : pprov (eq NGw) a -> thm (tau a).
Proof.
  induction 1 as [b Hb | a b _ IH1 _ IH2 | x a _ IH | a b c | a | a b | x a b | z t s Ht Hs | x y a | x a
                  | x y Hxy | t | t s r | t s | t s r | t s r | t s r | t s r | | | | | | | x a Hx].
  - subst b. exact T_NG.
  - exact (T_mp _ _ IH2 IH1).
  - exact (T_gen x _ IH).
  - exact (thm_B (tau a) (tau b) (tau c)).
  - exact (thm_P (tau a) F).
  - exact (thm_B3 (tau a) (tau b)).
  - exact (T_QI x (tau a) (tau b)).
  - assert (G : gate (cdt (enct t)) (cdt (enct s)) z = true).
    { unfold gate. rewrite <- !tcode_cdt, !occT_tcode, Ht, Hs. reflexivity. }
    pose proof (T_bundle (cdt (enct t)) (cdt (enct s)) z) as HB. rewrite bundle_open in HB by exact G.
    apply derc_thm. apply (derc_andr _ (cd (r_IND (cdt (enct t)) z))). now apply cthm.
  - exact (T_COMM x y (tau a)).
  - exact (T_B6c x (tau a)).
  - exact (T_R1 x y).
  - pose proof (T_EX (cdt (enct t))) as H. rewrite <- tcode_cdt in H.
    unfold r_EX in H. cbn [enc enct]. rewrite tcode_cdt in H |- *. exact H.
  - exact (T_EUC (cdt (enct s)) (cdt (enct r)) (cdt (enct t))).
  - exact (T_CS (cdt (enct t)) (cdt (enct s))).
  - exact (T_CA1 (cdt (enct t)) (cdt (enct s)) (cdt (enct r))).
  - exact (T_CA2 (cdt (enct t)) (cdt (enct s)) (cdt (enct r))).
  - exact (T_CM1 (cdt (enct t)) (cdt (enct s)) (cdt (enct r))).
  - exact (T_CM2 (cdt (enct t)) (cdt (enct s)) (cdt (enct r))).
  - exact (T_QZS 0).
  - exact (T_QSI 0 1).
  - exact (T_QA0 0).
  - exact (T_QAS 0 1).
  - exact (T_QM0 0).
  - exact (T_QMS 0 1).
  - rewrite fcode_cd in Hx |- *. set (c := tau a) in *.
    assert (G : gate x 0 c = true).
    { unfold gate. rewrite occT_spec. change (occT c 0) with false. rewrite orb_false_r.
      destruct (tocc c (T x)) eqn:E; [|reflexivity].
      apply T_fresh in E. lia. }
    pose proof (T_bundle x 0 c) as HB. rewrite bundle_open in HB by exact G.
    apply derc_thm. apply (derc_andl _ _ (cd (r_VAC x 0 c))). now apply cthm.
Qed.

(** ** The code-level calculus derives F exactly when PAeq proves Goldbach *)
Theorem thm_F_iff : thm F <-> PA_proves_GC.
Proof.
  split; [apply thm_F_GC|].
  intro H. apply pprov_NG_iff_PA_GC, pprov_thm in H.
  change (thm (wim (tau (Weq TZ TZ)) F)) in H.
  exact (T_mp _ _ (pprov_thm _ (leq_refl (eq NGw) TZ)) H).
Qed.

Print Assumptions thm_F_iff.
