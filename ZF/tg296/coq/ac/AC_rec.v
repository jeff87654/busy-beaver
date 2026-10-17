(** * AC_rec: recursion on ω (any ordinal domain) for a closed, total, functional step relation.

    The Z_cl.Scl pattern with [Step] replaced by an arbitrary relation [phG] read through
    [Std_setrec.Rel2] ([Rel2 phG u w] = "w = G(u)", $0 = u, $1 = w in phG).
    [SG phG]: f = $0, ξ = $1, v = $2, a = $3 (the start value): v = a at 0, v = G(f(e)) at e+1,
    v = ∅ at limits. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From ZF Require Std_setrec.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
#[local] Set Default Proof Using "All".

Definition SG (phG : form) : form :=
  (Emp0 $1 → $2 ≡' $3) ∧ (∀ ($0 ∈' $2 → Succ0 $0 $2 → ∃ (App0 $2 $1 $0 ∧ Std_setrec.Rel2 phG $0 $4))) ∧
  (Lim0 $1 → Emp0 $2).

Lemma fb_SG phG : fb 2 phG -> fb 4 (SG phG).
Proof.
  intros _. unfold SG. cbn [fb].
  repeat split; try (apply Std_setrec.fb_Rel2; cbn; lia); try fbcomp; try (cbn; lia).
Qed.

Definition Ax_rec (phG : form) : list form := rec_insts (SG phG).
Lemma Ax_rec_ok phG a : fb 2 phG -> In a (Ax_rec phG) -> ZFR a.
Proof. intros H. apply rec_insts_ok, fb_SG, H. Qed.

(** SR form of SG *)
Definition SGF (phG : form) (f xi v a : term) : form :=
  (Emp0 xi → v ≡' a) ∧
  (∀ ($0 ∈' xi`[↑] → Succ0 $0 xi`[↑] → ∃ (App0 f`[↑]`[↑] $1 $0 ∧ Std_setrec.Rel2 phG $0 v`[↑]`[↑]))) ∧
  (Lim0 xi → Emp0 v).
Lemma SR_SG phG f xi v a : SR (SG phG) f xi v a = SGF phG f xi v a.
Proof. unfold SR, SG, SGF. cbn. autorewrite with fsub. cbn. reflexivity. Qed.

Section Steps.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G).
Context (phG : form).

Lemma SG_loc a : G ⊢C SLoc (SG phG) a.
Proof.
  unfold SLoc. fall f. fall f'. fall xi. fall v. fintro Hf. fintro Hf'. fintro Hxi. fintro Ha. fintro H.
  rewrite SR_SG in H |- *. unfold SGF in H |- *. fdestr H H12 H3. fdestr H12 H1 H2.
  fsplit; [fsplit; [exact H1|]|exact H3].
  fall e. fintro He. fintro Hs. finst H2 e. fmp H2 He. fmp H2 Hs. fex H2 w Hw. fdestr Hw Hw1 Hw2.
  fexists w. fsplit; [|exact Hw2]. unfold Agree in Ha. finst Ha e. fmp Ha He. finst Ha w. exact (iff_l _ _ _ Ha Hw1).
Qed.

Lemma SG_tot a : G ⊢C Std_setrec.GTot phG -> G ⊢C STot (SG phG) a.
Proof.
  intros Ht. unfold STot. fall f. fall xi. fintro Hf. fintro Hxi. fintro Hall.
  fhave Hc : (u_ord_cases HG HR HOm HC xi Hxi). fcases Hc C0 C3; [fcases C0 C1 C2|].
  - fexists a. rewrite SR_SG. unfold SGF. fsplit; [fsplit|].
    + fintro He. feq.
    + fall e. fintro He. fabsurd. exact (emp0_el HG xi e C1 He).
    + fintro Hl. fabsurd. exact (lim_nonemp HG HR HOm HC xi Hl C1).
  - fex C2 b Hb. fdestr Hb Hb1 Hb2. finst Hall b. fmp Hall (succ0_self HG b xi Hb2). fex Hall w Hw.
    fobtain (Std_setrec.gtot_use phG w Ht) as v Hv. fexists v. rewrite SR_SG. unfold SGF. fsplit; [fsplit|].
    + fintro He. fabsurd. exact (succ_nonemp HG HR HOm HC b xi Hb2 He).
    + fall e. fintro He. fintro Hs. fhave E : (succ_inj HG HR HOm HC b e xi Hb2 Hs).
      fexists w. fsplit; [|exact Hv]. frew_in E (App0 f`[↑] $0 w`[↑]) Hw. exact Hw.
    + fintro Hl. fabsurd. exact (succ_nolim HG HR HOm HC b xi Hb2 Hl).
  - fobtain (u_emp0_ex HG HR HOm HC) as v Hv. fexists v. rewrite SR_SG. unfold SGF. fsplit; [fsplit|].
    + fintro He. fabsurd. exact (lim_nonemp HG HR HOm HC xi C3 He).
    + fall e. fintro He. fintro Hs. fabsurd. exact (succ_nolim HG HR HOm HC e xi Hs C3).
    + fintro Hl. exact Hv.
Qed.

Lemma SG_fun a : G ⊢C Std_setrec.GFun phG -> G ⊢C SFun (SG phG) a.
Proof.
  intros Hu. unfold SFun. fall f. fall xi. fall v. fall v'. fintro Hf. fintro Hxi. fintro H. fintro H'.
  rewrite SR_SG in H, H'. unfold SGF in H, H'. fdestr H H12 H3. fdestr H12 H1 H2. fdestr H' H12' H3'. fdestr H12' H1' H2'.
  fhave Hc : (u_ord_cases HG HR HOm HC xi Hxi). fcases Hc C0 C3; [fcases C0 C1 C2|].
  - fmp H1 C1. fmp H1' C1. feq.
  - fex C2 b Hb. fdestr Hb Hb1 Hb2. finst H2 b. fmp H2 (succ0_self HG b xi Hb2). fmp H2 Hb2.
    finst H2' b. fmp H2' (succ0_self HG b xi Hb2). fmp H2' Hb2.
    fex H2 w Hw. fdestr Hw Hw1 Hw2. fex H2' w' Hw'. fdestr Hw' Hw1' Hw2'.
    fhave E : (u_fun0_app HG HR HOm HC f b w w' Hf Hw1 Hw1'). frew_in E (Std_setrec.Rel2 phG $0 v'`[↑]) Hw2'.
    exact (Std_setrec.gfun_use phG w v v' Hu Hw2 Hw2').
  - fmp H3 C3. fmp H3' C3. exact (u_emp0_unique HG HR HOm HC v v' H3 H3').
Qed.
End Steps.

Section Rec.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G).
Context (phG : form) (Hfb : fb 2 phG) (HI : incl (Ax_rec phG) G).

Lemma omrec_ex a d : G ⊢C Std_setrec.GTot phG -> G ⊢C Std_setrec.GFun phG -> G ⊢C Ord0 d ->
  G ⊢C ∃ (Fun0 $0 ∧ Dom0 $0 d`[↑] ∧ RecOK (SG phG) a`[↑] $0).
Proof.
  intros Ht Hu Hd. pose proof (Ax_L_cl _ HL) as HC. pose proof (Ax_cl_ord _ HC) as HO.
  exact (rec_ex HG HR HO (SG phG) (fb_SG phG Hfb) HI a d (SG_loc HG HR HOm HC phG a) (SG_tot HG HR HOm HC phG a Ht)
           (SG_fun HG HR HOm HC phG a Hu) Hd).
Qed.

Lemma omrec_zero a F e u : G ⊢C RecOK (SG phG) a F -> G ⊢C App0 F e u -> G ⊢C Emp0 e -> G ⊢C u ≡' a.
Proof.
  intros H1 H2 H3. pose proof (Ax_L_cl _ HL) as HC. pose proof (Ax_ord_prim _ (Ax_cl_ord _ HC)) as HP.
  pose proof (Z_trec.recok_use HG HP _ _ _ _ _ H1 H2) as H. rewrite SR_SG in H. unfold SGF in H.
  exact (IE (CE1 (CE1 H)) H3).
Qed.

Lemma omrec_succ a F n s u u' : G ⊢C Fun0 F -> G ⊢C RecOK (SG phG) a F ->
  G ⊢C App0 F n u -> G ⊢C Succ0 n s -> G ⊢C App0 F s u' -> G ⊢C Std_setrec.Rel2 phG u u'.
Proof.
  intros Hf H1 Hn Hs Hs'. pose proof (Ax_L_cl _ HL) as HC. pose proof (Ax_ord_prim _ (Ax_cl_ord _ HC)) as HP.
  pose proof (Z_trec.recok_use HG HP _ _ _ _ _ H1 Hs') as H. rewrite SR_SG in H. unfold SGF in H.
  pose proof (CE2 (CE1 H)) as H2. finst H2 n. fmp H2 (succ0_self HG n s Hs). fmp H2 Hs.
  fex H2 w Hw. fdestr Hw Hw1 Hw2.
  fhave E : (u_fun0_app HG HR HOm HC F n w u Hf Hw1 Hn). frew_in E (Std_setrec.Rel2 phG $0 u'`[↑]) Hw2. exact Hw2.
Qed.

End Rec.
