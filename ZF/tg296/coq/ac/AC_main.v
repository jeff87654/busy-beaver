(** * AC_main: relative consistency of AC over ZF + GU.

      acgu_reg_relcon : (ZF + Reg + AC + GU) ⊢TC ⊥  →  (ZF + Reg + GU) ⊢TC ⊥

    Proof: relativize the derivation to L (Z_rel.transfer).  ZF + Reg holds in L (Z_axL.axL_ZFR), AC
    holds in L (Z_ac.acL_ex), GU holds in L ([guL], from ZF + Reg + GU).  With SU_reg.GU_reg_relcon:
    ZF + GU, ZF + AC + GU and ZF + Reg + AC + GU are equiconsistent. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase.
From RegCon Require Import Rel.
From RegCon Require MinZF.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_refl Z_axL Z_wo Z_ac Z_main.
From M254TG Require Import SU_gu SU_reg.
From M254TGA Require Import AC_gu.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ZF theorems from a list of ZF + Reg axioms hold in L, once those axioms do *)
Lemma rel_T' G A T : incl ZF0base G -> In ax_reg' G -> In ax_om' G -> incl Ax_L G ->
  (forall a, In a A -> ZFR a) -> (forall a, In a A -> G ⊢C rel Lform a) -> A ⊢C T -> closedf T ->
  G ⊢C rel Lform T.
Proof.
  intros HG HR HOm HL HAZ HA HT HTc.
  assert (HLe : G ⊢C ∃ Lform) by (eapply L_ex; eassumption). apply (ExE_named HLe). intros t.
  apply (transfer Lform bounded_Lform A T _ t HT HTc).
  - intros a Ha. now apply ZFR_closed, HAZ.
  - intros a Ha. apply weak_cons. now apply HA.
  - apply Ctx. now left.
Qed.

Lemma A_T_ZFR a : In a A_T -> ZFR a.
Proof.
  intros [<- | [<- | Ha]]; [apply ZFR_reg | apply ZFR_om |].
  apply in_app_iff in Ha as [Ha|Ha]; [now apply ZFR_base|].
  apply in_app_iff in Ha as [Ha|Ha]; [now apply Ax_wo_ok | now apply Ax_T_ok].
Qed.

Theorem guL_ex : exists A, (forall b, In b A -> ZFR b) /\
  forall G, incl ZF0base G -> In ax_reg' G -> In ax_om' G -> incl Ax_L G -> In GU G -> incl A G ->
    G ⊢C rel Lform GU.
Proof.
  destruct (MinZF.collect (R := fun L (a : form) => forall G, incl ZF0base G -> In ax_reg' G -> In ax_om' G ->
               incl Ax_L G -> incl L G -> G ⊢C rel Lform a) (Q := ZFR) (A := A0 ++ A_T)) as [L [HL1 HL2]].
  - intros L L' x Hx HL G H1 H2 H3 H4 H5. apply Hx; trivial. intros b Hb. now apply H5, HL.
  - intros a Ha. apply axL_ZFR. apply in_app_iff in Ha as [Ha|Ha]; [now apply A0_ZFR | now apply A_T_ZFR].
  - exists (Ax_wo ++ Ax_gu ++ L). split.
    + intros b Hb. apply in_app_iff in Hb as [Hb|Hb]; [now apply Ax_wo_ok|].
      apply in_app_iff in Hb as [Hb|Hb]; [now apply Ax_gu_ok | now apply HL1].
    + intros G HG HR HOm HL HGU HA.
      assert (HW : incl Ax_wo G) by (intros b Hb; apply HA, in_app_iff; now left).
      assert (HC : incl Ax_gu G) by (intros b Hb; apply HA, in_app_iff; right; apply in_app_iff; now left).
      assert (HLG : incl L G) by (intros b Hb; apply HA, in_app_iff; right; apply in_app_iff; now right).
      assert (HA0 : forall a, In a A0 -> G ⊢C rel Lform a)
        by (intros a Ha; apply HL2; trivial; apply in_app_iff; now left).
      assert (HAT : forall a, In a A_T -> G ⊢C rel Lform a)
        by (intros a Ha; apply HL2; trivial; apply in_app_iff; now right).
      apply guL; trivial.
      * exact (rel_T' G A0 T1 HG HR HOm HL A0_ZFR HA0 T1_prv T1_closed).
      * exact (rel_T' G A_T T_pow HG HR HOm HL A_T_ZFR HAT T_pow_prv T_pow_closed).
      * exact (rel_T' G A_T T_pair HG HR HOm HL A_T_ZFR HAT T_pair_prv T_pair_closed).
      * exact (rel_T' G A_T T_un HG HR HOm HL A_T_ZFR HAT T_un_prv T_un_closed).
Qed.

(** ** The theories *)
Definition T_ACGU (phi : form) : Prop := (ZFc phi \/ phi = ax_ac) \/ phi = GU.
Definition T_ACGUR (phi : form) : Prop := ((ZFc phi \/ phi = ax_reg') \/ phi = ax_ac) \/ phi = GU.

Lemma axL_all a : T_ACGUR a -> exists A, (forall b, In b A -> ZFR b) /\
  forall G, incl ZF0base G -> In ax_reg' G -> In ax_om' G -> incl Ax_L G -> In GU G -> incl A G ->
    G ⊢C rel Lform a.
Proof.
  intros [[H | ->] | ->].
  - destruct (axL_ZFR a H) as [A [HA HG]]. exists A. split; [exact HA|]. intros G H1 H2 H3 H4 _ H5. now apply HG.
  - destruct acL_ex as [A [HA HG]]. exists A. split; [exact HA|]. intros G H1 H2 H3 H4 _ H5. now apply HG.
  - exact guL_ex.
Qed.

Lemma T_ACGUR_closed a : T_ACGUR a -> closedf a.
Proof. intros [[H | ->] | ->]; [now apply ZFR_closed | apply ax_ac_closed | apply GU_closed]. Qed.

Theorem acgu_reg_relcon : T_ACGUR ⊢TC ⊥ -> T_GUR ⊢TC ⊥.
Proof.
  intros [A [HA H]].
  destruct (MinZF.collect (R := fun L (a : form) => forall G, incl ZF0base G -> In ax_reg' G -> In ax_om' G ->
               incl Ax_L G -> In GU G -> incl L G -> G ⊢C rel Lform a) (Q := ZFR) (A := A)) as [L [HL1 HL2]].
  - intros L L' x Hx HL G H1 H2 H3 H4 H5 H6. apply Hx; trivial. intros b Hb. now apply H6, HL.
  - intros a Ha. now apply axL_all, HA.
  - set (G0 := GU :: ax_reg' :: ax_om' :: ZF0base ++ Ax_L ++ L).
    assert (HG0 : incl ZF0base G0) by (intros b Hb; right; right; right; apply in_app_iff; now left).
    assert (HU0 : In GU G0) by now left.
    assert (HR0 : In ax_reg' G0) by (right; now left).
    assert (HO0 : In ax_om' G0) by (right; right; now left).
    assert (HL0 : incl Ax_L G0)
      by (intros b Hb; right; right; right; apply in_app_iff; right; apply in_app_iff; now left).
    assert (HLL : incl L G0)
      by (intros b Hb; right; right; right; apply in_app_iff; right; apply in_app_iff; now right).
    exists G0. split.
    + intros b [ <- | [ <- | [ <- | Hb ] ] ]; [now right | left; now right | left; apply ZFR_om |].
      apply in_app_iff in Hb as [Hb|Hb]; [left; now apply ZFR_base|].
      apply in_app_iff in Hb as [Hb|Hb]; [left; now apply Ax_L_ok | left; now apply HL1].
    + apply (ExE_named (L_ex HG0 HR0 HO0 HL0)). intros t.
      change ⊥ with (rel Lform ⊥).
      apply (transfer Lform bounded_Lform A ⊥ _ t H).
      * cbn. exact I.
      * intros a Ha. now apply T_ACGUR_closed, HA.
      * intros a Ha. apply weak_cons. apply HL2; trivial.
      * apply Ctx. now left.
Qed.

(** ** ZF + GU, ZF + AC + GU and ZF + Reg + AC + GU are equiconsistent *)
Theorem ZFCRGU_equicons : T_ACGUR ⊢TC ⊥ <-> T_GU ⊢TC ⊥.
Proof.
  split; [intros H; exact (GU_reg_relcon (acgu_reg_relcon H))|].
  intros H. apply (Weak_T H). intros phi [Hphi | ->]; [left; left; now left | now right].
Qed.

Theorem ZFCGU_equicons : T_ACGU ⊢TC ⊥ <-> T_GU ⊢TC ⊥.
Proof.
  split.
  - intros H. apply ZFCRGU_equicons. apply (Weak_T H).
    intros phi [[Hphi | ->] | ->]; [left; left; now left | left; now right | now right].
  - intros H. apply (Weak_T H). intros phi [Hphi | ->]; [left; now left | now right].
Qed.
