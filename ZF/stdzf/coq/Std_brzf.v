(** * Std_brzf: every ZF0 axiom, and INF_lib, is derivable from TPset (closures of prov-theorems).
    Main results: [bridge_ZF0_proof : bridge_ZF0], [bridge_INF_proof : bridge_INF]. *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_tr Std_alpha Std_gen Std_F Std_H Std_iface Std_iface2.
From ZF Require Import Std_setnd Std_setbase Std_setinf Std_breq Std_brnd Std_brrep.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** Separation / replacement from facts (instead of context membership) *)
Lemma sep_use' G n (phi : form) (sg : nat -> term) x :
  G ⊢C forall_times n (ax_sep' phi) -> fb (S n) phi ->
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔ $0 ∈' x`[↑]`[↑] ∧ phi[$0 .: (fun k => (sg k)`[↑]`[↑])]).
Proof.
  intros H Hfb.
  apply (closed_inst _ _ _ sg (sep_closed _ _ Hfb)) in H. apply (AllE x) in H. cbn in H.
  replace (phi[$0 .: (fun k => (sg k)`[↑]`[↑])]) with (phi[$0 .: Nat.add 3 >> var][up (up (up sg))][up (up x..)])
    by form_subst_eq.
  exact H.
Qed.

Lemma rep_use' G n (phi : form) (sg : nat -> term) x :
  G ⊢C forall_times n (ax_rep' phi) -> fb (S (S n)) phi ->
  (forall a b b', G ⊢C phi[a .: b .: sg] → phi[a .: b' .: sg] → b ≡' b') ->
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔ ∃ ($0 ∈' x`[↑]`[↑]`[↑] ∧ phi[$0 .: $1 .: (fun k => (sg k)`[↑]`[↑]`[↑])])).
Proof.
  intros H Hfb Hfun.
  apply (closed_inst _ _ _ sg (rep_closed _ _ Hfb)) in H. unfold ax_rep' in H. cbn [subst_form] in H.
  pose proof (IE H (funrel_intro _ _ _ Hfun)) as H'. clear H.
  apply (AllE x) in H'. cbn in H'.
  replace (phi[$0 .: $1 .: (fun k => (sg k)`[↑]`[↑]`[↑])])
    with (phi[$0 .: $1 .: Nat.add 4 >> var][up (up (up (up sg)))][up (up (up x..))]) by form_subst_eq.
  exact H'.
Qed.

(** ** The TPset hypotheses used *)
Definition trW : wff := Wim (Weq 3 1) (Wim (Weq 2 0) (Wim (Weq 3 2) (Weq 1 0))).
Definition phi_p : form := sub' $0 $1.
Definition phi_u : form := ∃ ($0 ∈' $2 ∧ $1 ∈' $0).
Definition phi_r : form := ($0 ≡' $2 ∧ $1 ≡' $3) ∨ ((¬ ($0 ≡' $2)) ∧ $1 ≡' $4).

Lemma refl_Lib : ax_refl' = Lib 1 (Weq 0 0).
Proof. reflexivity. Qed.
Lemma sym_Lib : ax_sym' = Lib 2 (Wim (Weq 1 0) (Weq 0 1)).
Proof. reflexivity. Qed.
Lemma elem_Lib : ax_eq_elem' = Lib 4 (Wim (Weq 3 1) (Wim (Weq 2 0) (Wim (Wel 3 2) (Wel 1 0)))).
Proof. reflexivity. Qed.

Definition TP0 : list form :=
  [ax_refl'; ax_sym'; Lib 4 trW; ax_eq_elem'; Lib 3 EXT; Lib 4 POW; Lib 4 UNI;
   repTP (sep2rep ⊥); repTP (sep2rep phi_p); repTP (sep2rep phi_u); repTP phi_r].

Lemma TP0_TPset psi : In psi TP0 -> TPset psi.
Proof.
  intros H. repeat (destruct H as [<-|H]; [|]); try destruct H.
  - rewrite refl_Lib. apply TPset_Lib; [apply lprov_prov, leq_refl | cbv; lia].
  - rewrite sym_Lib. apply TPset_Lib; [apply lprov_prov, leq_sym | cbv; lia].
  - apply TPset_Lib; [apply lprov_prov, leq_tr_eq | cbv; lia].
  - rewrite elem_Lib. apply TPset_Lib; [apply lprov_prov, leq_tr_el | cbv; lia].
  - apply TPset_Lib; [apply AX_EXT | exact maxfr_EXT].
  - apply TPset_Lib; [apply AX_POW | exact maxfr_POW].
  - apply TPset_Lib; [apply AX_UNI | exact maxfr_UNI].
  - apply repTP_TPset.
  - apply repTP_TPset.
  - apply repTP_TPset.
  - apply repTP_TPset.
Qed.

Lemma trans_from G : G ⊢C ax_refl' -> G ⊢C Lib 4 trW -> G ⊢C ax_trans'.
Proof.
  intros Hr Ht. unfold ax_trans'. fall x. fall y. fall z. fintro H1. fintro H2.
  pose proof (Lib_inst _ 4 trW (fun v => match v with 3 => x | 1 => x | 2 => y | _ => z end) ltac:(cbv; lia) Ht) as H.
  cbn in H. unfold ax_refl' in Hr. finst Hr x. exact (IE (IE (IE H Hr) H2) H1).
Qed.

(** ** The ZF0base axioms *)
Section Base.
Context {G : list form} (HE : incl EqAx G).

Lemma ext_from : G ⊢C Lib 3 EXT -> G ⊢C ax_ext'.
Proof.
  intros HX. unfold ax_ext'. fall x. fall y. fintro H1. fintro H2.
  pose proof (Lib_inst _ 3 EXT (x .: y .: var) maxfr_EXT HX) as H. unfold EXT in H.
  apply (dB_imp _ _ _ H). apply dB_allI. intros z. apply dB_andI; apply dB_impI; ctx_push Hz; simp_in Hz; simp.
  - unfold sub' in H1. finst H1 z. exact (IE H1 Hz).
  - unfold sub' in H2. finst H2 z. exact (IE H2 Hz).
Qed.

Lemma eset_from : G ⊢C forall_times 0 (ax_sep' ⊥) -> G ⊢C ax_eset'.
Proof.
  intros HS. pose proof (sep_use' _ 0 ⊥ var ($0) HS ltac:(cbn; exact I)) as T. simp_in T. fex T e He.
  unfold ax_eset'. fexists e. unfold is_eset. fall z. fintro Hz. finst He z. exact (CE2 (iff_l _ _ _ He Hz)).
Qed.

Lemma power_from : G ⊢C Lib 4 POW -> G ⊢C forall_times 1 (ax_sep' phi_p) -> G ⊢C ax_power'.
Proof.
  intros HP HS. unfold ax_power'. fall x.
  pose proof (Lib_inst _ 4 POW (x .: var) maxfr_POW HP) as H. unfold POW in H.
  apply (dB_exE _ _ _ _ H). intros y. apply II. ctx_push Hy.
  pose proof (sep_use' _ 1 phi_p (x .: var) y HS ltac:(unfold phi_p, sub'; cbn; lia)) as T.
  unfold phi_p in T. simp_in T. fex T P HPc.
  fexists P. unfold is_power. fall z. fsplit.
  - fintro Hz. finst HPc z. exact (CE2 (iff_l _ _ _ HPc Hz)).
  - fintro Hz. finst HPc z. apply (iff_r _ _ _ HPc). fsplit; [|exact Hz].
    pose proof (dB_allE _ _ _ z Hy) as H1. apply (dB_imp _ _ _ H1). apply dB_allI. intros w.
    apply dB_impI. ctx_push Hw. simp_in Hw. simp. unfold sub' in Hz. finst Hz w. exact (IE Hz Hw).
Qed.

Lemma union_from : G ⊢C Lib 4 UNI -> G ⊢C forall_times 1 (ax_sep' phi_u) -> G ⊢C ax_union'.
Proof.
  intros HU HS. unfold ax_union'. fall x.
  pose proof (Lib_inst _ 4 UNI (x .: var) maxfr_UNI HU) as H. unfold UNI in H.
  apply (dB_exE _ _ _ _ H). intros y. apply II. ctx_push Hy.
  pose proof (sep_use' _ 1 phi_u (x .: var) y HS ltac:(unfold phi_u; cbn; lia)) as T.
  unfold phi_u in T. simp_in T. fex T U HUc.
  fexists U. unfold is_union. fall z. fsplit.
  - fintro Hz. finst HUc z. exact (CE2 (iff_l _ _ _ HUc Hz)).
  - fintro Hz. finst HUc z. apply (iff_r _ _ _ HUc). fsplit; [|exact Hz].
    pose proof (dB_allE _ _ _ z Hy) as H1. apply (dB_imp _ _ _ H1).
    fex Hz w Hw. fdestr Hw Hw1 Hw2. apply (dB_exI _ _ _ w). apply dB_andI; simp; assumption.
Qed.

Lemma pair_from : G ⊢C ax_eset' -> G ⊢C ax_power' -> G ⊢C forall_times 3 (ax_rep' phi_r) -> G ⊢C ax_pair'.
Proof.
  intros He Hp Hr. unfold ax_pair'. fall a. fall b.
  unfold ax_eset' in He. fex He e Hee.
  pose proof Hp as T. unfold ax_power' in T. finst T e. fex T p1 Hp1.
  pose proof Hp as T. unfold ax_power' in T. finst T p1. fex T p2 Hp2.
  fassert Hfun : (∀ ∀ ∀ (phi_r[$2 .: $1 .: (fun k => ((e .: a .: b .: var) k)`[↑]`[↑]`[↑])] →
                         phi_r[$2 .: $0 .: (fun k => ((e .: a .: b .: var) k)`[↑]`[↑]`[↑])] → $1 ≡' $0)).
  { fall w. fall y. fall y'. unfold phi_r. simp. fintro H1. fintro H2. fcases H1 H11 H12; fcases H2 H21 H22.
    - fdestr H11 H11a H11b. fdestr H21 H21a H21b. feqE.
    - fdestr H11 H11a H11b. fdestr H22 H22a H22b. fabsurd. exact (IE H22a H11a).
    - fdestr H12 H12a H12b. fdestr H21 H21a H21b. fabsurd. exact (IE H12a H21a).
    - fdestr H12 H12a H12b. fdestr H22 H22a H22b. feqE. }
  assert (Hfun' : forall w y y', Γ ⊢C phi_r[w .: y .: (e .: a .: b .: var)] → phi_r[w .: y' .: (e .: a .: b .: var)] → y ≡' y').
  { intros w y y'. pose proof Hfun as T. finst T w y y'. unfold phi_r in T |- *. simp_in T. simp. exact T. }
  pose proof (rep_use' _ 3 phi_r (e .: a .: b .: var) p2 Hr ltac:(unfold phi_r; cbn; lia) Hfun') as T.
  unfold phi_r in T. simp_in T. fex T Y HY. clear Hfun Hfun'.
  fexists Y. unfold is_pair. fall z. finst HY z. fsplit.
  - fintro Hz. fhave T : (iff_l _ _ _ HY Hz). fex T w Hw. fdestr Hw Hw1 Hw2. fcases Hw2 H1 H2.
    + fleft. exact (CE2 H1).
    + fright. exact (CE2 H2).
  - fintro Hz. apply (iff_r _ _ _ HY). fcases Hz H1 H2.
    + fexists e. fsplit.
      * pose proof Hp2 as T. unfold is_power in T. finst T e. apply (iff_r _ _ _ T). unfold sub'. fall u.
        fintro Hu. fabsurd. unfold is_eset in Hee. finst Hee u. exact (IE Hee Hu).
      * fleft. fsplit; [apply (eqE_refl HE)|exact H1].
    + fexists p1. fsplit.
      * pose proof Hp2 as T. unfold is_power in T. finst T p1. apply (iff_r _ _ _ T). unfold sub'. fall u.
        fintro Hu. exact Hu.
      * fright. fsplit; [|exact H2]. fintro Hpe.
        fassert Hep : (e ∈' p1).
        { pose proof Hp1 as T. unfold is_power in T. finst T e. apply (iff_r _ _ _ T). unfold sub'. fall u.
          fintro Hu. exact Hu. }
        fassert Hee' : (e ∈' e); [fmemE|]. unfold is_eset in Hee. finst Hee e. exact (IE Hee Hee').
Qed.

End Base.

Lemma TP0_incl G : incl TP0 G -> forall psi, In psi TP0 -> G ⊢C psi.
Proof. intros H psi Hp. apply Ctx, H, Hp. Qed.

(** everything in ZF0base, from [ax_trans' :: TP0] *)
Lemma base_from_TP psi : In psi ZF0base -> (ax_trans' :: TP0) ⊢C psi.
Proof.
  assert (HE : incl EqAx (ax_trans' :: TP0)) by (intros x Hx; cbn in *; tauto).
  assert (Hin : forall th, In th TP0 -> (ax_trans' :: TP0) ⊢C th) by (intros th Hth; apply Ctx; now right).
  assert (Hsp : (ax_trans' :: TP0) ⊢C forall_times 1 (ax_sep' phi_p)).
  { apply (sep_from_rep _ 1 phi_p HE ltac:(unfold phi_p, sub'; cbn; lia)).
    apply (rep_from_REP _ 1 _ HE (fb_sep2rep 1 phi_p ltac:(unfold phi_p, sub'; cbn; lia))). apply Hin. cbn; tauto. }
  assert (Hsu : (ax_trans' :: TP0) ⊢C forall_times 1 (ax_sep' phi_u)).
  { apply (sep_from_rep _ 1 phi_u HE ltac:(unfold phi_u; cbn; lia)).
    apply (rep_from_REP _ 1 _ HE (fb_sep2rep 1 phi_u ltac:(unfold phi_u; cbn; lia))). apply Hin. cbn; tauto. }
  assert (Hse : (ax_trans' :: TP0) ⊢C forall_times 0 (ax_sep' ⊥)).
  { apply (sep_from_rep _ 0 ⊥ HE ltac:(cbn; exact I)).
    apply (rep_from_REP _ 0 _ HE (fb_sep2rep 0 ⊥ ltac:(cbn; exact I))). apply Hin. cbn; tauto. }
  assert (Hsr : (ax_trans' :: TP0) ⊢C forall_times 3 (ax_rep' phi_r)).
  { apply (rep_from_REP _ 3 phi_r HE ltac:(unfold phi_r; cbn; lia)). apply Hin. cbn; tauto. }
  assert (Hes : (ax_trans' :: TP0) ⊢C ax_eset') by exact (eset_from HE Hse).
  assert (Hpw : (ax_trans' :: TP0) ⊢C ax_power') by (apply (power_from HE); [apply Hin; cbn; tauto|exact Hsp]).
  intros H. repeat (destruct H as [<-|H]; [|]); try destruct H.
  - apply Ctx. cbn; tauto.
  - apply Ctx. cbn; tauto.
  - apply Ctx. cbn; tauto.
  - apply Ctx. cbn; tauto.
  - apply (ext_from HE). apply Hin. cbn; tauto.
  - exact Hes.
  - exact (pair_from HE Hes Hpw Hsr).
  - apply (union_from HE); [apply Hin; cbn; tauto|exact Hsu].
  - exact Hpw.
Qed.

Lemma cut_trans B psi : incl TP0 B -> (ax_trans' :: TP0) ⊢C psi -> B ⊢C psi.
Proof.
  intros HB H. eapply prv_cut; [exact H|]. intros th [<-|Hth].
  - apply trans_from; apply Ctx, HB; cbn; tauto.
  - apply Ctx, HB, Hth.
Qed.

Lemma cut_trans' B psi : incl TP0 B -> (ax_trans' :: B) ⊢C psi -> B ⊢C psi.
Proof.
  intros HB H. eapply prv_cut; [exact H|]. intros th [<-|Hth].
  - apply trans_from; apply Ctx, HB; cbn; tauto.
  - apply Ctx, Hth.
Qed.

(** ** Recovering free-index bounds of instance formulas *)
Lemma fb_subst_inv (phi : form) : forall N M (sg : nat -> term),
  fb M phi[sg] -> (forall i, idx (sg i) < M -> i < N) -> fb N phi.
Proof.
  induction phi as [|P v|op a IHa b IHb|q a IHa] using form_ind_falsity; intros N M sg Hfb H; cbn in *.
  - exact I.
  - destruct P; cbn in v, Hfb |- *; rewrite (vec2 v) in Hfb |- *; cbn in *;
      destruct (Vector.hd v) as [n|[]]; destruct (Vector.hd (Vector.tl v)) as [m|[]]; cbn in *;
      destruct Hfb; split; apply H; assumption.
  - destruct Hfb. split; [eapply IHa|eapply IHb]; eauto.
  - eapply IHa; [exact Hfb|]. intros [|i] Hi; cbn in Hi; [lia|]. unfold funcomp in Hi.
    destruct (sg i) as [k|[]] eqn:E; cbn in Hi. specialize (H i). rewrite E in H. cbn in H.
    assert (k < M) by lia. specialize (H H0). lia.
Qed.

Lemma fb_sep_inv n phi : closedf (forall_times n (ax_sep' phi)) -> fb (S n) phi.
Proof.
  intros Hc. apply fb_forall_times in Hc. rewrite Nat.add_0_r in Hc. cbn in Hc.
  destruct Hc as [[_ [_ H]] _]. eapply fb_subst_inv; [exact H|]. intros [|i]; cbn; lia.
Qed.

Lemma fb_rep_inv n phi : closedf (forall_times n (ax_rep' phi)) -> fb (S (S n)) phi.
Proof.
  intros Hc. apply fb_forall_times in Hc. rewrite Nat.add_0_r in Hc. cbn in Hc.
  destruct Hc as [[H _] _]. eapply fb_subst_inv; [exact H|]. intros [|[|i]]; cbn; lia.
Qed.

(** ** bridge_ZF0 *)
Theorem bridge_ZF0_proof : bridge_ZF0.
Proof.
  intros psi Hpsi. destruct Hpsi as [psi Hb | phi n Hc | phi n Hc].
  - exists TP0. split; [exact TP0_TPset|]. apply (cut_trans' TP0); [apply incl_refl|].
    eapply Weak; [exact (base_from_TP psi Hb)|]. intros x Hx; exact Hx.
  - exists (repTP (sep2rep phi) :: TP0). split.
    + intros th [<-|Hth]; [apply repTP_TPset|exact (TP0_TPset th Hth)].
    + apply cut_trans'; [intros x Hx; now right|].
      assert (HE : incl EqAx (ax_trans' :: repTP (sep2rep phi) :: TP0)) by (intros x Hx; cbn in *; tauto).
      apply (sep_from_rep _ n phi HE (fb_sep_inv _ _ Hc)).
      apply (rep_from_REP _ n _ HE (fb_sep2rep _ _ (fb_sep_inv _ _ Hc))). apply Ctx. cbn; tauto.
  - exists (repTP phi :: TP0). split.
    + intros th [<-|Hth]; [apply repTP_TPset|exact (TP0_TPset th Hth)].
    + apply cut_trans'; [intros x Hx; now right|].
      assert (HE : incl EqAx (ax_trans' :: repTP phi :: TP0)) by (intros x Hx; cbn in *; tauto).
      apply (rep_from_REP _ n phi HE (fb_rep_inv _ _ Hc)). apply Ctx. cbn; tauto.
Qed.

(** ** bridge_INF *)
Theorem bridge_INF_proof : bridge_INF.
Proof.
  exists [Lib 3 INF]. split.
  - intros th [<-|[]]. apply TPset_Lib; [apply AX_INF|exact maxfr_INF].
  - assert (HI : [Lib 3 INF] ⊢C Lib 3 INF) by (apply Ctx; now left).
    remember [Lib 3 INF] as G0 eqn:EG. clear EG.
    rewrite INF_lib_eq. fall x.
    pose proof (Lib_inst _ 3 INF (fun _ => x) maxfr_INF HI) as H. unfold INF in H.
    apply (dB_exE _ _ _ _ H). intros y. apply II. ctx_push Hy.
    fexists y. fsplit.
    + pose proof (dB_andE1 _ _ _ Hy) as H1. simp_in H1. exact H1.
    + apply dB_andE2 in Hy. unfold SClos. fall u. fintro Hu.
      pose proof (dB_allE _ _ _ u Hy) as H1. pose proof (dB_imp _ _ _ H1 Hu) as H2.
      apply (dB_exE _ _ _ _ H2). intros z. apply II. ctx_push Hz.
      fexists z. fsplit.
      * pose proof (dB_andE1 _ _ _ Hz) as H3. simp_in H3. exact H3.
      * apply dB_andE2 in Hz. unfold Sing. fall w. pose proof (dB_allE _ _ _ w Hz) as H4.
        fsplit.
        -- pose proof (dB_andE1 _ _ _ H4) as H5. simp_in H5. exact H5.
        -- pose proof (dB_andE2 _ _ _ H4) as H5. simp_in H5. exact H5.
Qed.
