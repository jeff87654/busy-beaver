(** * SU_reg: regularity is relatively consistent with ZF + GU.

      GU_reg_relcon : T_GUR ⊢TC ⊥ -> T_GU ⊢TC ⊥

    (T_GU = Std_iface.ZFc + GU, T_GUR = T_GU + ax_reg', SU_gu.v; minimal ∈/≡ signature).

    This is ZF/stdzf_r3/regcon's proof (relativize to the class WF of well-founded sets) extended by the
    single axiom GU:
    (1) embed T_GUR into the function-symbol signature (GU is function-free: embed GU);
    (2) relativize the derivation to WF there (Rel.rel_prv), using regcon's Main.rel_axiom for
        the ZF + Reg axioms and [GU_rel_fn] : ZFc_fn + embed GU ⊢ relw (embed GU);
    (3) come back to the minimal signature with rm_const_prv and [rm_const_embed]
        (rm_const_fm (embed φ) is equivalent to φ over minZFeq').
    [GU_rel_fn] is proved in the minimal signature ([MinPart.GU_WF]) and moved over with
    prv_embed (relw ∘ embed = embed ∘ rel WFm, WFm = the ∈-only formula of WF.v's WF).  There:
    for x ∈ WF take a universe U ∋ x (GU) and w := {y ∈ U | WF y}; w ∈ WF, x ∈ w, w is
    transitive, and w is a universe relativized to WF: 𝒫a, {a,b} and ∪ran f from U are in WF
    (closure lemma), and the Δ0 parts (Sub0, Pair0, Fun0, Dom0, App0, Trans0) are absolute for
    the transitive class WF (Z_rel.D0_abs).  The two WF facts used in the minimal signature
    (transitivity, closure lemma) are regcon's WF_el / WF_closure, transferred with (3). *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts.
From Undecidability.FOL.Sets Require Import ZF minZF.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZF PCPb_to_minZF PCPb_to_ZFD.
From Undecidability.FOL.Sets.Models Require Import ZF_conservativity.
From Undecidability Require Import Shared.ListAutomation.
From RegCon Require Rel WF Main MinZF Link.
From ZF Require Std_tr Std_gen Std_iface Std_setnd Std_setbase.
From ZFC Require Z_rel Z_base.
From M254TG Require Import SU_gu.

(** ** Part 1: syntax and the WF facts, function-symbol side *)
Module FN1.
Import ListAutomationNotations ListAutomationHints.
Import Rel WF Main MinZF.
Open Scope syn.
#[local] Hint Constructors prv : core.

(** WF.v's [Mwf] = [WF $0] written in the minimal signature *)
Definition WFm : form' :=
  ∃ (((∀ ($0 ∈' $1 → ∀ ($0 ∈' $1 → $0 ∈' $2))) ∧
      (∀ ((∀ ($0 ∈' $1 → $0 ∈' $2)) → (∃ $0 ∈' $1) → ∃ ($0 ∈' $1 ∧ ∀ ($0 ∈' $1 → ¬ ($0 ∈' $2)))))) ∧ $1 ∈' $0).

Lemma embed_WFm : embed WFm = Mwf.
Proof. reflexivity. Qed.

#[global] Arguments WFm : simpl never.

Lemma rel_embed (M phi : form') : rel (embed M) (embed phi) = embed (rel M phi).
Proof.
  induction phi as [| P v | b a IHa c IHc | q a IHa] using form_ind_falsity; cbn; try reflexivity.
  - now rewrite IHa, IHc.
  - destruct q; cbn; now rewrite IHa.
Qed.

Lemma relw_embed (phi : form') : rel Mwf (embed phi) = embed (rel WFm phi).
Proof. rewrite <- embed_WFm. apply rel_embed. Qed.

(** rm_const_fm (embed φ) and φ are interderivable over minZFeq' *)
Lemma rm_const_embed {p : peirce} (phi : form') : forall A, minZFeq' <<= A ->
  (A ⊢ rm_const_fm (embed phi) <-> A ⊢ phi).
Proof.
  induction phi as [| P v | b a IHa c IHc | q a IHa] using form_ind_subst; intros A HA.
  - cbn. tauto.
  - rewrite (vec_inv2 v). destruct (Vector.hd v) as [i|[]]; destruct (Vector.hd (Vector.tl v)) as [j|[]].
    destruct P; cbn.
    + rewrite <- (prv_ex_eq $i (∃ ($0 ≡' $(S (S j)) ∧ $1 ∈' $0)) HA). cbn.
      rewrite <- (prv_ex_eq $j ($(S i) ∈' $0) HA). cbn. tauto.
    + rewrite <- (prv_ex_eq $i (∃ ($0 ≡' $(S (S j)) ∧ $1 ≡' $0)) HA). cbn.
      rewrite <- (prv_ex_eq $j ($(S i) ≡' $0) HA). cbn. tauto.
  - destruct b; cbn.
    + apply and_equiv; auto.
    + apply or_equiv; intros B HB; [apply IHa | apply IHc]; eapply incl_tran; eassumption.
    + apply impl_equiv; intros B HB; [apply IHa | apply IHc]; eapply incl_tran; eassumption.
  - destruct q; cbn.
    + apply all_equiv. intros t. rewrite rm_const_fm_subst, <- embed_subst. now apply IHa.
    + apply ex_equiv. intros B t HB. rewrite rm_const_fm_subst, <- embed_subst. apply IHa. eapply incl_tran; eassumption.
Qed.

(** the two WF facts, as minimal-signature formulas *)
Definition th1 : form' := Z_rel.TransC WFm.
Definition th2 : form' := ∀ ((∀ ($0 ∈' $1 → WFm)) → WFm).

Lemma th1_fn : ([] : list form) ⊢C embed th1.
Proof.
  unfold th1, Z_rel.TransC. cbn. rewrite embed_WFm.
  apply AllI_named. intros x. rsimp. apply II. apply AllI_named. intros y. rsimp. apply II.
  eapply WF_el; [apply ctx2 | apply ctx1].
Qed.

Lemma th2_fn' T : ZFeq' <<= T -> Wax <<= T -> T ⊢C embed th2.
Proof.
  intros H1 H2. unfold th2. cbn. rewrite embed_WFm.
  apply AllI_named. intros x. rsimp. apply II. apply WF_closure; [auto | auto | apply ctx1].
Qed.

Lemma th2_fn : B0 ⊢C embed th2.
Proof. apply th2_fn'; [apply B0_ZFeq | apply B0_Wax]; apply incl_refl. Qed.

(** from the function-symbol signature to the minimal one, for embedded formulas *)
Lemma fn_to_min (L : list form) (th : form') : (forall b, b el L -> Main.ZFc b) -> L ⊢C embed th ->
  exists L', (forall b, In b L' -> Std_iface.ZFc b) /\ L' ⊢C th.
Proof.
  intros HL H. assert (H' : (L ++ ZFeq') ⊢C embed th) by (apply (Weak H); auto).
  apply rm_const_prv in H'.
  destruct (collect (R := fun L0 (a : form) => L0 ⊢C rm_const_fm a) (Q := ZFcl_min) (A := L)) as [L1 [HL1 HL2]].
  - intros L0 L0' x Hx HL0. apply (Weak Hx HL0).
  - intros a Ha. now apply rm_const_axiom, HL.
  - exists (L1 ++ minZFeq'). split.
    + intros b [Hb|Hb]%in_app_iff; apply Link.std_min; [now apply HL1 | now left].
    + apply rm_const_embed; [auto |]. apply (prv_cut H').
      intros psi [[a [<- Ha]]%in_map_iff | Hb]%in_app_iff.
      * apply (Weak (HL2 a Ha)). auto.
      * apply Ctx. auto.
Qed.

(** from the minimal signature to the function-symbol one *)
Definition TF0 (b : form) : Prop := Main.ZFc b \/ b = embed SU_gu.GU.
Definition TFR (b : form) : Prop := ZFcReg b \/ b = embed SU_gu.GU.

Lemma min_to_fn (L : list form') th : (forall b, In b L -> SU_gu.T_GU b) -> L ⊢C th ->
  exists L', (forall b, b el L' -> TF0 b) /\ L' ⊢C embed th.
Proof.
  intros HL H. apply prv_embed in H.
  destruct (collect (R := fun L0 (a : form') => L0 ⊢C embed a) (Q := TF0) (A := L)) as [L1 [HL1 HL2]].
  - intros L0 L0' x Hx HL0. apply (Weak Hx HL0).
  - intros a Ha. destruct (HL a Ha) as [Ha' | ->].
    + destruct (embed_axiom_ZF (Link.std_all Ha')) as [L0 [H1 H2]].
      exists L0. split; [intros b Hb; left; auto | exact H2].
    + exists [embed SU_gu.GU]. split; [intros b [<-|[]]; now right | apply Ctx; now left].
  - exists L1. split; trivial. apply (prv_cut H). intros psi [a [<- Ha]]%in_map_iff. now apply HL2.
Qed.

Lemma WF_facts : exists L, (forall b, In b L -> Std_iface.ZFc b) /\ L ⊢C th1 /\ L ⊢C th2.
Proof.
  destruct (@fn_to_min nil th1 (fun b (H : b el []) => match H with end) th1_fn) as [L1 [H1 H1']].
  destruct (@fn_to_min B0 th2 B0_ZFc th2_fn) as [L2 [H2 H2']].
  exists (L1 ++ L2). split; [intros b [Hb|Hb]%in_app_iff; auto |].
  split; [apply (Weak H1') | apply (Weak H2')]; auto.
Qed.

End FN1.

(** ** Part 2: GU holds in WF, minimal signature *)
Module MinPart.
Import ListNotations.
Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Rel Z_rel Z_base SU_gu.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Notation WFm := FN1.WFm.

Lemma WFm_bounded : bounded 1 WFm.
Proof. apply fb_bounded. fbcomp. Qed.

Lemma WFm_up sg : WFm[up sg] = WFm.
Proof. exact (M_up' WFm WFm_bounded sg). Qed.

Lemma WFm_cons0 sg : WFm[$0 .: sg] = WFm.
Proof. erewrite (bounded_subst WFm_bounded). apply subst_var. intros [|k] Hk; [reflexivity | lia]. Qed.

Lemma relW_subst (phi : form) sg : (rel WFm phi)[sg] = rel WFm (phi[sg]).
Proof. exact (rel_subst WFm_bounded phi sg). Qed.

#[local] Hint Rewrite WFm_up WFm_cons0 relW_subst : fsub.

(** WF is a transitive class closed under "all elements are WF" *)
Lemma wf_el {G} (H1 : G ⊢C FN1.th1) x y : G ⊢C WFm[x..] -> G ⊢C y ∈' x -> G ⊢C WFm[y..].
Proof. exact (trans_use WFm WFm_bounded G x y H1). Qed.

Lemma wf_cl {G} (H2 : G ⊢C FN1.th2) x : G ⊢C ∀ ($0 ∈' x`[↑] → WFm) -> G ⊢C WFm[x..].
Proof. intros H. unfold FN1.th2 in H2. finst H2 x. exact (IE H2 H). Qed.

Lemma wf_eq {G} (HG : incl ZF0base G) x y : G ⊢C x ≡' y -> G ⊢C WFm[x..] -> G ⊢C WFm[y..].
Proof. exact (leib G WFm x y HG). Qed.

(** Δ0 absoluteness for WF *)
Lemma d0_iff {G} (H1 : G ⊢C FN1.th1) (phi : form) (sg : nat -> term) : D0 phi ->
  (forall k, G ⊢C WFm[(sg k)..]) -> G ⊢C rel WFm (phi[sg]) ↔ phi[sg].
Proof. intros Hd Hs. rewrite <- relW_subst. exact (D0_abs WFm WFm_bounded phi Hd G sg H1 Hs). Qed.

Section D0inst.
Context {G : list form} (H1 : G ⊢C FN1.th1).

Lemma rel_Sub0 z x : G ⊢C WFm[z..] -> G ⊢C WFm[x..] -> G ⊢C rel WFm (Sub0 z x) ↔ Sub0 z x.
Proof.
  intros Hz Hx. pose proof (d0_iff H1 (Sub0 $0 $1) (z .: x .: (fun _ => z))) as H.
  rewrite Sub0_subst in H. apply H; [d0comp | intros [|[|k]]; assumption].
Qed.

Lemma rel_Pair0 x y q : G ⊢C WFm[x..] -> G ⊢C WFm[y..] -> G ⊢C WFm[q..] ->
  G ⊢C rel WFm (Pair0 x y q) ↔ Pair0 x y q.
Proof.
  intros Hx Hy Hq. pose proof (d0_iff H1 (Pair0 $0 $1 $2) (x .: y .: q .: (fun _ => x))) as H.
  rewrite Pair0_subst in H. apply H; [d0comp | intros [|[|[|k]]]; assumption].
Qed.

Lemma rel_Trans0 w : G ⊢C WFm[w..] -> G ⊢C rel WFm (Trans0 w) ↔ Trans0 w.
Proof.
  intros Hw. pose proof (d0_iff H1 (Trans0 $0) (w .: (fun _ => w))) as H.
  rewrite Trans0_subst in H. apply H; [d0comp | intros [|k]; assumption].
Qed.

Lemma rel_Fun0 f : G ⊢C WFm[f..] -> G ⊢C rel WFm (Fun0 f) ↔ Fun0 f.
Proof.
  intros Hf. pose proof (d0_iff H1 (Fun0 $0) (f .: (fun _ => f))) as H.
  rewrite Fun0_subst in H. apply H; [d0comp | intros [|k]; assumption].
Qed.

Lemma rel_Dom0 f x : G ⊢C WFm[f..] -> G ⊢C WFm[x..] -> G ⊢C rel WFm (Dom0 f x) ↔ Dom0 f x.
Proof.
  intros Hf Hx. pose proof (d0_iff H1 (Dom0 $0 $1) (f .: x .: (fun _ => f))) as H.
  rewrite Dom0_subst in H. apply H; [d0comp | intros [|[|k]]; assumption].
Qed.

Lemma rel_App0 f a v : G ⊢C WFm[f..] -> G ⊢C WFm[a..] -> G ⊢C WFm[v..] ->
  G ⊢C rel WFm (App0 f a v) ↔ App0 f a v.
Proof.
  intros Hf Ha Hv. pose proof (d0_iff H1 (App0 $0 $1 $2) (f .: a .: v .: (fun _ => f))) as H.
  rewrite App0_subst in H. apply H; [d0comp | intros [|[|[|k]]]; assumption].
Qed.

End D0inst.

(** both components of a pair (a, v) ∈ f ∈ WF are in WF *)
Lemma app_wf {G} (H1 : G ⊢C FN1.th1) f a v : G ⊢C WFm[f..] -> G ⊢C App0 f a v ->
  G ⊢C WFm[a..] ∧ WFm[v..].
Proof.
  intros Hf H. unfold App0 in H. fex H p Hp. fdestr Hp Hpf Hop.
  pose proof (wf_el H1 _ _ Hf Hpf) as Hpw.
  unfold OP0 in Hop. simp_in Hop. fdestr Hop Hop12 Hop3. fdestr Hop12 Hs Hq.
  fsplit.
  - fex Hs s Hs'. fdestr Hs' Hsp Hsing. unfold Sing0 in Hsing. fdestr Hsing Has Hs2.
    exact (wf_el H1 _ _ (wf_el H1 _ _ Hpw Hsp) Has).
  - fex Hq q Hq'. fdestr Hq' Hqp Hpair. unfold Pair0 in Hpair. fdestr Hpair Hpair1 Hpair2.
    fdestr Hpair1 Haq Hvq. exact (wf_el H1 _ _ (wf_el H1 _ _ Hpw Hqp) Hvq).
Qed.

(** membership in w = {y ∈ U | WF y} *)
Lemma w_out {G} w U y : G ⊢C ∀ ($0 ∈' w`[↑] ↔ $0 ∈' U`[↑] ∧ WFm) -> G ⊢C y ∈' w -> G ⊢C y ∈' U ∧ WFm[y..].
Proof. intros Hw Hy. finst Hw y. exact (iff_l _ _ _ Hw Hy). Qed.

Lemma w_in {G} w U y : G ⊢C ∀ ($0 ∈' w`[↑] ↔ $0 ∈' U`[↑] ∧ WFm) -> G ⊢C y ∈' U -> G ⊢C WFm[y..] -> G ⊢C y ∈' w.
Proof. intros Hw Hy1 Hy2. finst Hw y. apply (iff_r _ _ _ Hw). fsplit; assumption. Qed.

Lemma GU_WF {G} (HG : incl ZF0base G) (HGU : In GU G) (Hsep : In (ax_sep' WFm) G)
  (H1 : G ⊢C FN1.th1) (H2 : G ⊢C FN1.th2) : G ⊢C rel WFm GU.
Proof.
  assert (HU : G ⊢C GU) by (apply Ctx; exact HGU). clear HGU.
  unfold GU. cbn [rel]. fall x. fintro Hx.
  unfold GU in HU. finst HU x. fex HU U HU'. fdestr HU' HxU HGru.
  assert (Hfb : fb 1 WFm) by fbcomp.
  fobtain (sep_use _ 0 WFm var U Hsep Hfb) as w Hw.
  fassert Hww : (WFm[w..]).
  { apply (wf_cl H2). fall y. fintro Hy. exact (CE2 (w_out _ _ _ Hw Hy)). }
  fexists w. fsplit; [exact Hww |]. fsplit; [exact (w_in _ _ _ Hw HxU Hx) |].
  unfold Gru in HGru. fdestr HGru HTU HGU2.
  unfold Gru. simp. fsplit.
  { apply (iff_r _ _ _ (rel_Trans0 H1 w Hww)). unfold Trans0. simp.
    fall y. fintro Hy. fall z. fintro Hz.
    pose proof (w_out _ _ _ Hw Hy) as Hy'. fdestr Hy' HyU HyW.
    apply (w_in _ _ _ Hw); [| exact (wf_el H1 _ _ HyW Hz)].
    unfold Trans0 in HTU. finst HTU y. fmp HTU HyU. finst HTU z. exact (IE HTU Hz). }
  fall a. fintro HaW. fintro Haw.
  pose proof (w_out _ _ _ Hw Haw) as Ha'. fdestr Ha' HaU HaW'.
  finst HGU2 a. fmp HGU2 HaU. fdestr HGU2 HGa12 HGa3. fdestr HGa12 HGa1 HGa2.
  fsplit; [fsplit |].
  { (* power set *)
    fex HGa1 P HP. fdestr HP HPU HPdef.
    fassert HPW : (WFm[P..]).
    { apply (wf_cl H2). fall z. fintro Hz. finst HPdef z. pose proof (iff_l _ _ _ HPdef Hz) as Hzs.
      apply (wf_cl H2). fall t. fintro Ht. apply (wf_el H1 a t HaW).
      unfold Sub0 in Hzs. finst Hzs t. exact (IE Hzs Ht). }
    fexists P. fsplit; [exact HPW |]. fsplit; [exact (w_in _ _ _ Hw HPU HPW) |].
    fall z. fintro HzW. finst HPdef z. pose proof (rel_Sub0 H1 z a HzW HaW) as R. fsplit.
    - fintro Hz. apply (iff_r _ _ _ R). exact (iff_l _ _ _ HPdef Hz).
    - fintro Hz. apply (iff_r _ _ _ HPdef). exact (iff_l _ _ _ R Hz). }
  { (* pairs *)
    fall b. fintro HbW. fintro Hbw. pose proof (w_out _ _ _ Hw Hbw) as Hb'. fdestr Hb' HbU HbW'.
    finst HGa2 b. fmp HGa2 HbU. fex HGa2 q Hq. fdestr Hq HqU Hpq.
    fassert HqW : (WFm[q..]).
    { apply (wf_cl H2). fall z. fintro Hz. pose proof Hpq as Hpq'. unfold Pair0 in Hpq'.
      fdestr Hpq' Hpq1 Hpq2. finst Hpq2 z. fmp Hpq2 Hz. fcases Hpq2 E E.
      - exact (wf_eq HG a z (eq_sym' HG _ _ E) HaW).
      - exact (wf_eq HG b z (eq_sym' HG _ _ E) HbW). }
    fexists q. fsplit; [exact HqW |]. fsplit; [exact (w_in _ _ _ Hw HqU HqW) |].
    apply (iff_r _ _ _ (rel_Pair0 H1 a b q HaW HbW HqW)). exact Hpq. }
  (* unions of ranges *)
  fall f. fintro HfW. fintro Hf. fdestr Hf Hf12 Hf3. fdestr Hf12 HFr HDr.
  pose proof (iff_l _ _ _ (rel_Fun0 H1 f HfW) HFr) as HF.
  pose proof (iff_l _ _ _ (rel_Dom0 H1 f a HfW HaW) HDr) as HD.
  finst HGa3 f.
  fassert Hran : (∀ (∀ (App0 f`[↑]`[↑] $1 $0 → $0 ∈' U`[↑]`[↑]))).
  { fall b. fall v. fintro Hab.
    pose proof (app_wf H1 f b v HfW Hab) as Hbv. fdestr Hbv HbW HvW.
    finst Hf3 b. fmp Hf3 HbW. finst Hf3 v. fmp Hf3 HvW.
    fmp Hf3 (iff_r _ _ _ (rel_App0 H1 f b v HfW HbW HvW) Hab).
    exact (CE1 (w_out _ _ _ Hw Hf3)). }
  fmp HGa3 (CI (CI HF HD) Hran). fex HGa3 Sv HS. fdestr HS HSU HSdef.
  fassert HSW : (WFm[Sv..]).
  { apply (wf_cl H2). fall z. fintro Hz. finst HSdef z. pose proof (iff_l _ _ _ HSdef Hz) as Hz'.
    fex Hz' v Hv. fdestr Hv Hva Hzv. fex Hva b Hb.
    pose proof (app_wf H1 f b v HfW Hb) as Hbv. fdestr Hbv HbW HvW.
    exact (wf_el H1 v z HvW Hzv). }
  fexists Sv. fsplit; [exact HSW |]. fsplit; [exact (w_in _ _ _ Hw HSU HSW) |].
  fall z. fintro HzW. finst HSdef z. fsplit.
  - fintro Hz. pose proof (iff_l _ _ _ HSdef Hz) as Hz'.
    fex Hz' v Hv. fdestr Hv Hva Hzv. fex Hva b Hb.
    pose proof (app_wf H1 f b v HfW Hb) as Hbv. fdestr Hbv HbW HvW.
    fexists v. fsplit; [exact HvW |]. fsplit; [| exact Hzv].
    fexists b. fsplit; [exact HbW |]. exact (iff_r _ _ _ (rel_App0 H1 f b v HfW HbW HvW) Hb).
  - fintro Hz. fex Hz v Hv. fdestr Hv HvW Hv2. fdestr Hv2 Hva Hzv. fex Hva b Hb. fdestr Hb HbW Hbr.
    pose proof (iff_l _ _ _ (rel_App0 H1 f b v HfW HbW HvW) Hbr) as Happ.
    apply (iff_r _ _ _ HSdef). fexists v. fsplit; [fexists b; exact Happ | exact Hzv].
Qed.

(** GU holds in WF, from finitely many axioms of ZF + GU *)
Lemma GU_rel_min : exists L, (forall b, In b L -> T_GU b) /\ L ⊢C rel WFm GU.
Proof.
  destruct FN1.WF_facts as [L0 [HL0 [H1 H2]]].
  assert (Hfb : fb 1 WFm) by fbcomp.
  exists (GU :: ax_sep' WFm :: ZF0base ++ L0). split.
  - intros b [<- | [<- | Hb]]; [now right | |].
    + left. left. exact (ZF0_sep WFm 0 (sep_closed 0 WFm Hfb)).
    + left. apply in_app_iff in Hb as [Hb|Hb]; [left; now apply ZF0_base | now apply HL0].
  - apply GU_WF.
    + intros b Hb. right. right. apply in_app_iff. now left.
    + now left.
    + right. now left.
    + apply (Weak H1). intros b Hb. right. right. apply in_app_iff. now right.
    + apply (Weak H2). intros b Hb. right. right. apply in_app_iff. now right.
Qed.

End MinPart.

(** ** Part 3: relativization in the function-symbol signature, and the way back *)
Module FN2.
Import ListAutomationNotations ListAutomationHints.
Import Rel WF Main MinZF FN1.
Open Scope syn.
#[local] Hint Constructors prv : core.

#[local] Instance ZF_funcs_dec2 : eq_dec ZF_func_sig.
Proof. intros x y. unfold dec. decide equality. Defined.

#[local] Instance ZF_preds_dec2 : eq_dec ZF_pred_sig.
Proof. intros x y. unfold dec. decide equality. Defined.

Lemma GU_bounded_fn : bounded 0 (embed GU).
Proof. apply bounded_comp_eq. compute. repeat split; lia. Qed.

Lemma GU_rel_fn : exists L, (forall b, b el L -> TF0 b) /\ L ⊢C rel Mwf (embed GU).
Proof.
  destruct MinPart.GU_rel_min as [L0 [H1 H2]].
  destruct (min_to_fn H1 H2) as [L [H3 H4]]. exists L. split; [exact H3 |]. now rewrite relw_embed.
Qed.

(** (1) into the function-symbol signature *)
Lemma step1_GU : T_GUR ⊢TC ⊥ -> TFR ⊢TC ⊥.
Proof.
  intros [A [HA H]]. apply prv_embed in H.
  destruct (collect (R := fun L (a : form') => L ⊢C embed a) (Q := TFR) (A := A)) as [L [HL1 HL2]].
  - intros L L' x Hx HL. apply (Weak Hx HL).
  - intros a Ha. destruct (HA a Ha) as [[Ha' | ->] | ->].
    + destruct (embed_axiom (or_introl (Link.std_all Ha'))) as [L0 [H1 H2]].
      exists L0. split; [intros b Hb; left; auto | exact H2].
    + destruct (embed_axiom (or_intror eq_refl)) as [L0 [H1 H2]].
      exists L0. split; [intros b Hb; left; auto | exact H2].
    + exists [embed GU]. split; [intros b [<-|[]]; now right | apply Ctx; now left].
  - exists L. split; trivial. apply (prv_cut H). intros psi [a [<- Ha]]%in_map_iff. now apply HL2.
Qed.

(** (2) relativization to WF *)
Lemma rel_axiom_GU a : TFR a -> exists L, (forall b, b el L -> TF0 b) /\ (forall G, L <<= G -> G ⊢C rel Mwf a).
Proof.
  intros [Ha | ->].
  - destruct (rel_axiom Ha) as [L [H1 H2]]. exists L. split; [intros b Hb; left; auto | exact H2].
  - destruct GU_rel_fn as [L [H1 H2]]. exists L. split; [exact H1 |]. intros G HG. apply (Weak H2 HG).
Qed.

Lemma TFR_closed a : TFR a -> bounded 0 a.
Proof. intros [Ha | ->]; [now apply ZFcReg_closed | exact GU_bounded_fn]. Qed.

Lemma step2_GU : TFR ⊢TC ⊥ -> TF0 ⊢TC ⊥.
Proof.
  intros [A [HA Hprv]].
  destruct (collect (R := fun L a => forall G, L <<= G -> G ⊢C rel Mwf a) (Q := TF0) (A := A)) as [L [HL1 HL2]].
  - intros L L' x Hx HL G HG. apply Hx. intros b Hb. apply HG, HL, Hb.
  - intros a Ha. now apply rel_axiom_GU, HA.
  - exists (B0 ++ L). split.
    + intros b [Hb|Hb]%in_app_iff; [left; now apply B0_ZFc | now apply HL1].
    + assert (H := rel_prv Mwf_bounded (p0 := class) B0_closed Mwf_funcs Hprv (Gamma := B0 ++ L) (sigma := fun _ => ∅)).
      apply H.
      * apply incl_appl, incl_refl.
      * intros k. rewrite Mwf_inst. apply WF_eset; [eapply B0_ZFeq | eapply B0_Wax]; auto.
      * intros a Ha. rewrite (rel_closed Mwf_bounded); [| apply TFR_closed, HA, Ha].
        apply HL2; auto.
Qed.

(** (3) back to the minimal signature *)
Lemma rm_const_axiom_GU a : TF0 a -> exists L, (forall b, In b L -> T_GU b) /\ L ⊢C rm_const_fm a.
Proof.
  intros [Ha | ->].
  - destruct (rm_const_axiom Ha) as [L [H1 H2]].
    exists L. split; [intros b Hb; left; apply Link.std_min; auto | exact H2].
  - exists (GU :: minZFeq'). split.
    + intros b [<-|Hb]; [now right | left; apply Link.std_min; now left].
    + apply rm_const_embed; [auto | apply Ctx; now left].
Qed.

Lemma step3_GU : TF0 ⊢TC ⊥ -> T_GU ⊢TC ⊥.
Proof.
  intros [A [HA H]]. assert (H' : (A ++ ZFeq') ⊢C ⊥) by (apply (Weak H); auto).
  apply rm_const_prv in H'. cbn in H'.
  destruct (collect (R := fun L (a : form) => L ⊢C rm_const_fm a) (Q := T_GU) (A := A)) as [L [HL1 HL2]].
  - intros L L' x Hx HL. apply (Weak Hx HL).
  - intros a Ha. now apply rm_const_axiom_GU, HA.
  - exists (L ++ minZFeq'). split.
    + intros b [Hb|Hb]%in_app_iff; [now apply HL1 | left; apply Link.std_min; now left].
    + apply (prv_cut H'). intros psi [[a [<- Ha]]%in_map_iff | Hb]%in_app_iff.
      * apply (Weak (HL2 a Ha)). auto.
      * apply Ctx. auto.
Qed.

End FN2.

(** ** Main theorem *)
Theorem GU_reg_relcon : T_GUR ⊢TC ⊥ -> T_GU ⊢TC ⊥.
Proof. intros H. exact (FN2.step3_GU (FN2.step2_GU (FN2.step1_GU H))). Qed.
