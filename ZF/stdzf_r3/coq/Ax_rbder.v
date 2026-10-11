(** * Ax_rbder: the library's replacement, union and power set axioms from the bounded-fiber
    replacement scheme [ax_rb'] (Ax_rb.v).  Proofs written by a Haiku subagent. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_F Std_iface Std_setnd Std_setbase Std_breq Std_brrep Ax_rb.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** Helpers *)

(** equal elements give equal subsets *)
Lemma sub_of_eq (G : list form) x y : incl EqAx G -> G ⊢C x ≡' y -> G ⊢C sub' x y.
Proof.
  intros HE Hxy. unfold sub'. fall v. fintro Hv.
  exact (elemE_cong HE v x v y (eqE_refl HE v) Hxy Hv).
Qed.

(** the fiber hypothesis of rb_hyp, for a functional instance *)
Lemma rb_hyp_fun (G : list form) (phi : form) (sg : nat -> term) : incl EqAx G ->
  G ⊢C (fun_rel' phi)[sg] -> forall w : term,
  G ⊢C ∃ ∀ (phi[w`[↑]`[↑] .: $0 .: (fun k => (sg k)`[↑]`[↑])] → rbC $0 $1).
Proof.
  intros HE Hfr w. unfold rbC.
  apply (XM_rule G (∃ (phi[w`[↑] .: $0 .: (fun k => (sg k)`[↑])]))).
  - apply II. ctx_push Hex. fex Hex z0 Hz0.
    rewrite ?subst_comp in Hz0.
    match type of Hz0 with context [phi[?s]] =>
      replace (phi[s]) with (phi[w .: z0 .: sg]) in Hz0 by form_subst_eq end.
    fexists z0. fall z. fintro Hq. fintro Hn. fabsurd.
    rewrite ?subst_comp in Hq.
    match type of Hq with context [phi[?s]] =>
      replace (phi[s]) with (phi[w .: z .: sg]) in Hq by form_subst_eq end.
    apply (IE Hn). apply (sub_of_eq _ z z0 HE). exact (funrel_inst _ phi sg w z z0 Hfr Hq Hz0).
  - apply II. ctx_push Hn.
    fexists w. fall z. fintro Hq. fabsurd.
    rewrite ?subst_comp in Hq.
    match type of Hq with context [phi[?s]] =>
      replace (phi[s]) with (phi[w .: z .: sg]) in Hq by form_subst_eq end.
    apply (IE Hn). apply (ExI z). rewrite inst_eq. exact Hq.
Qed.

Definition phi_P : form := sub' $1 $2.

Lemma phi_P_sub (s : nat -> term) : phi_P[s] = sub' (s 1) (s 2).
Proof. unfold phi_P. rewrite sub'_subst. reflexivity. Qed.

(** ** Replacement *)
Lemma rep_from_rb G k phi : incl EqAx G -> fb (S (S k)) phi ->
  G ⊢C forall_times k (ax_rb' phi) -> G ⊢C forall_times k (ax_rep' phi).
Proof.
  intros HE Hfb HR. apply ft_intro. intros sg.
  unfold ax_rep'. cbn [subst_form]. apply II. ctx_push Hfr.
  apply AllI_named. intros x.
  pose proof (rb_use _ k phi sg x HR Hfb (rbhyp_intro _ phi sg (rb_hyp_fun _ phi sg HE Hfr))) as H.
  apply (ExE_named H). intros Y. ctx_push HY.
  apply (ExI Y). apply AllI_named. intros z.
  apply (AllE z) in HY. simp_in HY. simp.
  rewrite ?subst_comp.
  match goal with |- context [phi[?s]] =>
    replace (phi[s]) with (phi[$0 .: z`[↑] .: (fun k => (sg k)`[↑])]) by form_subst_eq end.
  rewrite ?subst_comp in HY.
  match type of HY with context [phi[?s]] =>
    replace (phi[s]) with (phi[$0 .: z`[↑] .: (fun k => (sg k)`[↑])]) in HY by form_subst_eq end.
  exact HY.
Qed.

(** ** Union *)
Definition phi_U : form := $1 ∈' $0.

Lemma union_from_rb G : incl EqAx G -> G ⊢C forall_times 0 (ax_rb' phi_U) -> G ⊢C ax_union'.
Proof.
  intros HE HR.
  assert (Hh : forall w : term, G ⊢C ∃ ∀ (phi_U[w`[↑]`[↑] .: $0 .: (fun k => (var k)`[↑]`[↑])] → rbC $0 $1)).
  { intros w. unfold rbC, phi_U. fexists w. fall z. fintro Hz. fintro Hn. exact Hz. }
  pose proof (rbhyp_intro _ phi_U var Hh) as Hh'.
  assert (Hfb : fb (S (S 0)) phi_U) by (unfold phi_U; cbn; repeat first [split | lia | exact I]).
  unfold ax_union', is_union. apply AllI_named. intros x.
  pose proof (rb_use _ 0 phi_U var x HR Hfb Hh') as H.
  apply (ExE_named H). intros Y. ctx_push HY.
  apply (ExI Y). apply AllI_named. intros z.
  apply (AllE z) in HY. simp_in HY. simp.
  exact HY.
Qed.

(** ** Power set *)

Lemma power_from_rb G : incl EqAx G -> G ⊢C (∀ ∃ ($1 ∈' $0)) ->
  G ⊢C forall_times 1 (ax_rb' phi_P) -> G ⊢C ax_power'.
Proof.
  intros HE Hinf HR. unfold ax_power', is_power. apply AllI_named. intros p.
  assert (Hh : forall w : term, G ⊢C ∃ ∀ (phi_P[w`[↑]`[↑] .: $0 .: (fun k => ((p .: var) k)`[↑]`[↑])] → rbC $0 $1)).
  { intros w. unfold rbC. fexists p. fall z. fintro Hq.
    rewrite phi_P_sub in Hq. simp_in Hq. fintro Hn. fabsurd. apply (IE Hn). exact Hq. }
  pose proof (rbhyp_intro _ phi_P (p .: var) Hh) as Hh'.
  assert (Hfb : fb (S (S 1)) phi_P) by (unfold phi_P, sub'; cbn; repeat first [split | lia | exact I]).
  apply (AllE p) in Hinf. fex Hinf Ix HpI.
  pose proof (rb_use _ 1 phi_P (p .: var) Ix HR Hfb Hh') as H.
  apply (ExE_named H). intros Y. ctx_push HY.
  apply (ExI Y). apply AllI_named. intros z.
  apply (AllE z) in HY. simp_in HY. simp.
  rewrite phi_P_sub in HY. simp_in HY. rewrite ?sub'_subst. simp. rewrite ?sub'_subst in HY. simp_in HY.
  fsplit.
  - fintro Hz. pose proof (iff_l _ _ _ HY Hz) as T. fex T w Hw. fdestr Hw Hw1 Hw2. exact Hw2.
  - fintro Hs. apply (iff_r _ _ _ HY). fexists p. fsplit; [exact HpI | exact Hs].
Qed.
