(** * AC_coll: the Mostowski collapse of an extensional set X ⊆ L.

    [Coll X P M]: P is a function with domain X, M = ran P, and P(x) = {P(z) | z ∈ X ∩ x}.
    [ExtX X]: distinct elements of X are told apart by an element of X.
    Construction ([coll_ex]): X ⊆ L_g ([Z_axL.L_bound]); Z_trec recursion on ξ < g with step [Scoll]
    whose value at ξ is P restricted to {x ∈ X | ρ(x) = ξ} (ρ = Z_wo's L-rank [Rho]), computed from the
    values below ξ: P(x) = {f(e)(z) | z ∈ X ∩ x, e < ξ}; elements of x have rank < ρ(x) ([rho_lt]).
    The domains of different stages are disjoint, so P = ⋃ ran f is a function with no agreement
    induction.  Regularity gives injectivity ([coll_inj], with [ExtX]) and that P fixes a transitive
    T ⊆ X pointwise and every y ∈ X with y ⊆ T ([coll_fix], [coll_fix_sub]). *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_wo.
From ZFC Require Z_axL.
From M254TGA Require Import AC_iso.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition Coll (X P M : term) : form :=
  Fun0 P ∧ Dom0 P X ∧ (∀ ($0 ∈' M`[↑] ↔ ∃ App0 P`[↑]`[↑] $0 $1)) ∧
  (∀ (∀ (App0 P`[↑]`[↑] $1 $0 →
     ∀ ($0 ∈' $1 ↔ ∃ ($0 ∈' X`[↑]`[↑]`[↑]`[↑] ∧ ($0 ∈' $3 ∧ App0 P`[↑]`[↑]`[↑]`[↑] $0 $1)))))).
Definition ExtX (X : term) : form :=
  ∀ ($0 ∈' X`[↑] → ∀ ($0 ∈' X`[↑]`[↑] → ¬ ($1 ≡' $0) → ∃ ($0 ∈' X`[↑]`[↑]`[↑] ∧ ¬ ($0 ∈' $2 ↔ $0 ∈' $1)))).
#[global] Arguments Coll : simpl never.
#[global] Arguments ExtX : simpl never.
Lemma Coll_subst X P M sg : (Coll X P M)[sg] = Coll X`[sg] P`[sg] M`[sg].
Proof. psubst Coll. Qed.
Lemma ExtX_subst X sg : (ExtX X)[sg] = ExtX X`[sg].
Proof. psubst ExtX. Qed.
#[global] Hint Rewrite Coll_subst ExtX_subst : fsub.

(** ** The recursion step: the collapse on the elements of X of L-rank exactly ξ *)
(** w ∈ m: ∃ z ∈ p ∩ x, ∃ e ∈ ξ, ∃ g, f(e) = g ∧ g(z) = w *)
Definition Mbody (f xi p x w : term) : form :=
  ∃ ($0 ∈' p`[↑] ∧ ($0 ∈' x`[↑] ∧ ∃ ($0 ∈' xi`[↑]`[↑] ∧
     ∃ (App0 f`[↑]`[↑]`[↑] $1 $0 ∧ App0 $0 $2 w`[↑]`[↑]`[↑])))).
Definition Mch (f xi p x m : term) : form := ∀ ($0 ∈' m`[↑] ↔ Mbody f`[↑] xi`[↑] p`[↑] x`[↑] $0).
(** q = (x, m) with x of rank ξ *)
Definition Vrel (f xi p x q : term) : form :=
  Rho x xi ∧ ∃ (OP0 x`[↑] $0 q`[↑] ∧ Mch f`[↑] xi`[↑] p`[↑] x`[↑] $0).
Definition Vq (f xi p q : term) : form := ∃ ($0 ∈' p`[↑] ∧ Vrel f`[↑] xi`[↑] p`[↑] $0 q`[↑]).
Definition Sc (f xi v p : term) : form := ∀ ($0 ∈' v`[↑] ↔ Vq f`[↑] xi`[↑] p`[↑] $0).
#[global] Arguments Mbody : simpl never.
#[global] Arguments Mch : simpl never.
#[global] Arguments Vrel : simpl never.
#[global] Arguments Vq : simpl never.
#[global] Arguments Sc : simpl never.
Lemma Mbody_subst f xi p x w sg : (Mbody f xi p x w)[sg] = Mbody f`[sg] xi`[sg] p`[sg] x`[sg] w`[sg].
Proof. psubst Mbody. Qed.
#[global] Hint Rewrite Mbody_subst : fsub.
Lemma Mch_subst f xi p x m sg : (Mch f xi p x m)[sg] = Mch f`[sg] xi`[sg] p`[sg] x`[sg] m`[sg].
Proof. psubst Mch. Qed.
#[global] Hint Rewrite Mch_subst : fsub.
Lemma Vrel_subst f xi p x q sg : (Vrel f xi p x q)[sg] = Vrel f`[sg] xi`[sg] p`[sg] x`[sg] q`[sg].
Proof. psubst Vrel. Qed.
#[global] Hint Rewrite Vrel_subst : fsub.
Lemma Vq_subst f xi p q sg : (Vq f xi p q)[sg] = Vq f`[sg] xi`[sg] p`[sg] q`[sg].
Proof. psubst Vq. Qed.
#[global] Hint Rewrite Vq_subst : fsub.
Lemma Sc_subst f xi v p sg : (Sc f xi v p)[sg] = Sc f`[sg] xi`[sg] v`[sg] p`[sg].
Proof. psubst Sc. Qed.
#[global] Hint Rewrite Sc_subst : fsub.

Definition Scoll : form := Sc $0 $1 $2 $3.
Lemma SR_Scoll f xi v p : SR Scoll f xi v p = Sc f xi v p.
Proof. unfold SR, Scoll. simp. reflexivity. Qed.
Lemma fb_Scoll : fb 4 Scoll.
Proof. fbcomp. Qed.
(** rewrite every [SR Scoll ..] by its explicit instance ([rewrite SR_Scoll] would also match an already
    rewritten [Sc ..] up to an expensive conversion through LL) *)
Ltac srs := repeat match goal with |- context [SR Scoll ?a ?b ?c ?d] => rewrite (SR_Scoll a b c d) end.

(** instance formulas *)
Definition mform : form := Mbody $4 $3 $1 $2 $0.
Definition vform : form := Vrel $4 $2 $3 $0 $1.
Definition ranform : form := ∃ (App0 $2 $0 $1).
Definition Bad (X P x : term) : form :=
  ∃ ($0 ∈' X`[↑] ∧ (¬ ($0 ≡' x`[↑])) ∧ ∃ (App0 P`[↑]`[↑] x`[↑]`[↑] $0 ∧ App0 P`[↑]`[↑] $1 $0)).
#[global] Arguments Bad : simpl never.
Lemma Bad_subst X P x sg : (Bad X P x)[sg] = Bad X`[sg] P`[sg] x`[sg].
Proof. psubst Bad. Qed.
#[global] Hint Rewrite Bad_subst : fsub.
Definition injform : form := Bad $1 $2 $0.
Definition fixform : form := ¬ App0 $1 $0 $0.

(** instances (filled by the prover of this file) *)
Definition Ax_coll : list form :=
  Z_axL.powL_insts ++ rec_insts Scoll ++
  [forall_times 4 (ax_sep' mform); forall_times 3 (ax_rep' vform); forall_times 1 (ax_sep' ranform);
   forall_times 2 (ax_sep' injform); forall_times 1 (ax_sep' fixform)].
Lemma Ax_coll_ok a : In a Ax_coll -> ZFR a.
Proof.
  unfold Ax_coll. intros H. apply in_app_iff in H as [H|H]; [|apply in_app_iff in H as [H|H]].
  - apply (oc_insts_ok 0 _ a Z_axL.fb_Qpow H).
  - exact (rec_insts_ok Scoll a fb_Scoll H).
  - destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; first [apply ZFR_sep | apply ZFR_rep]; fbcomp.
Qed.

(** ** Instance membership and context helpers *)
Lemma in_pow {G} (HC : incl Ax_coll G) : incl Z_axL.powL_insts G.
Proof. intros a Ha. apply HC, in_or_app. now left. Qed.
Lemma in_rec {G} (HC : incl Ax_coll G) : incl (rec_insts Scoll) G.
Proof. intros a Ha. apply HC, in_or_app. right. apply in_or_app. now left. Qed.
Lemma in_m {G} (HC : incl Ax_coll G) : In (forall_times 4 (ax_sep' mform)) G.
Proof. apply HC, in_or_app. right. apply in_or_app. right. now left. Qed.
Lemma in_v {G} (HC : incl Ax_coll G) : In (forall_times 3 (ax_rep' vform)) G.
Proof. apply HC, in_or_app. right. apply in_or_app. right. right. now left. Qed.
Lemma in_ran {G} (HC : incl Ax_coll G) : In (forall_times 1 (ax_sep' ranform)) G.
Proof. apply HC, in_or_app. right. apply in_or_app. right. right. right. now left. Qed.
Lemma in_inj {G} (HC : incl Ax_coll G) : In (forall_times 2 (ax_sep' injform)) G.
Proof. apply HC, in_or_app. right. apply in_or_app. right. right. right. right. now left. Qed.
Lemma in_fix {G} (HC : incl Ax_coll G) : In (forall_times 1 (ax_sep' fixform)) G.
Proof. apply HC, in_or_app. right. apply in_or_app. right. right. right. right. right. now left. Qed.

Lemma wox {G} (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G) : WOx G.
Proof. split; [exact HR|split; assumption]. Qed.
Lemma ho_of {G} (HW : incl Ax_wo G) : incl Ax_ord G.
Proof. exact (Ax_cl_ord _ (Ax_L_cl _ (Ax_wo_L _ HW))). Qed.
Lemma hp_of {G} (HW : incl Ax_wo G) : incl Ax_prim G.
Proof. exact (Ax_ord_prim _ (ho_of HW)). Qed.

Lemma op0_ex' {G} (HG : incl ZF0base G) x y : G ⊢C ∃ OP0 x`[↑] y`[↑] $0.
Proof. fobtain (Std_setbase.op_ex HG x y) as q Hq. fexists q. exact (Z_prim.op0_of HG x y q Hq). Qed.

(** the value of a pair in f lies in ⋃⋃f *)
Lemma app_val_in {G} (HG : incl ZF0base G) f u v U1 U2 : G ⊢C is_union f U1 -> G ⊢C is_union U1 U2 ->
  G ⊢C App0 f u v -> G ⊢C v ∈' U2.
Proof.
  intros H1 H2 H. unfold App0 in H. fex H q Hq. fdestr Hq Hq1 Hq2.
  fhave C : (op0_comp_g HG u v q Hq2). fdestr C C1 C2. fex C2 s Hs. fdestr Hs Hs1 Hs2.
  apply (union_in HG U1 U2 s v H2); [exact (union_in HG f U1 q s H1 Hq1 Hs1)|exact Hs2].
Qed.

(** ** The step: existence, locality, functionality *)
Lemma mch_ex {G} (HG : incl ZF0base G) (Hin : In (forall_times 4 (ax_sep' mform)) G) f xi p x :
  G ⊢C ∃ Mch f`[↑] xi`[↑] p`[↑] x`[↑] $0.
Proof.
  fobtain (union_ex HG f) as U1 HU1. fobtain (union_ex HG U1) as U2 HU2.
  fobtain (union_ex HG U2) as U3 HU3. fobtain (union_ex HG U3) as U4 HU4. fobtain (union_ex HG U4) as U5 HU5.
  pose proof (sep_use _ 4 mform (p .: x .: xi .: f .: var) U5 Hin ltac:(fbcomp)) as T.
  unfold mform in T. simp_in T. fex T m Hm. fexists m. unfold Mch. fall w. finst Hm w. fsplit.
  - fintro Hw. exact (CE2 (iff_l _ _ _ Hm Hw)).
  - fintro Hw. apply (iff_r _ _ _ Hm). fsplit; [|exact Hw].
    pose proof Hw as Hw'. unfold Mbody in Hw'. fex Hw' z Hz. fdestr Hz Hz1 Hz23. fdestr Hz23 Hz2 Hz3.
    fex Hz3 e He. fdestr He He1 He2. fex He2 g Hg. fdestr Hg Hg1 Hg2.
    fhave Hg' : (app_val_in HG f e g U1 U2 HU1 HU2 Hg1).
    unfold App0 in Hg2. fex Hg2 q Hq. fdestr Hq Hq1 Hq2.
    fhave Hq3 : (union_in HG U2 U3 g q HU3 Hg' Hq1).
    exact (app_val_in HG U3 z w U4 U5 HU4 HU5 (app0_intro_g U3 z w q Hq2 Hq3)).
Qed.

Lemma vrel_fun {G} (HG : incl ZF0base G) f xi p a b b' :
  G ⊢C Vrel f xi p a b -> G ⊢C Vrel f xi p a b' -> G ⊢C b ≡' b'.
Proof.
  intros H1 H2. unfold Vrel in H1, H2. fdestr H1 H1a H1b. fdestr H2 H2a H2b.
  fex H1b m Hm. fdestr Hm Hm1 Hm2. fex H2b m' Hm'. fdestr Hm' Hm1' Hm2'.
  fassert E : (m ≡' m'). { unfold Mch in Hm2, Hm2'. exact (ext_char HG _ m m' Hm2 Hm2'). }
  frew_in E (OP0 a`[↑] $0 b'`[↑]) Hm1'. exact (op0_unique_g HG a m b b' Hm1 Hm1').
Qed.

Lemma sc_ex {G} (HG : incl ZF0base G) (Hv : In (forall_times 3 (ax_rep' vform)) G) f xi p :
  G ⊢C ∃ Sc f`[↑] xi`[↑] $0 p`[↑].
Proof.
  assert (Hfn : forall a b b', G ⊢C vform[a .: b .: (xi .: p .: f .: var)] →
                                    vform[a .: b' .: (xi .: p .: f .: var)] → b ≡' b').
  { intros a b b'. unfold vform. simp. fintro H1. fintro H2. exact (vrel_fun HG f xi p a b b' H1 H2). }
  pose proof (rep_use G 3 vform (xi .: p .: f .: var) p Hv ltac:(fbcomp) Hfn) as T.
  unfold vform in T. simp_in T. unfold Sc, Vq. simp. exact T.
Qed.

Lemma mbody_agree {G} f f' xi p x w : G ⊢C Agree f f' xi -> G ⊢C Mbody f xi p x w -> G ⊢C Mbody f' xi p x w.
Proof.
  intros HA H. unfold Mbody in H |- *. fex H z Hz. fdestr Hz Hz1 Hz23. fdestr Hz23 Hz2 Hz3.
  fex Hz3 e He. fdestr He He1 He2. fex He2 g Hg. fdestr Hg Hg1 Hg2.
  fexists z. fsplit; [exact Hz1|]. fsplit; [exact Hz2|]. fexists e. fsplit; [exact He1|].
  fexists g. fsplit; [|exact Hg2]. exact (agree_use f f' xi e g HA He1 Hg1).
Qed.
Lemma mbody_agree_r {G} f f' xi p x w : G ⊢C Agree f f' xi -> G ⊢C Mbody f' xi p x w -> G ⊢C Mbody f xi p x w.
Proof.
  intros HA H. unfold Mbody in H |- *. fex H z Hz. fdestr Hz Hz1 Hz23. fdestr Hz23 Hz2 Hz3.
  fex Hz3 e He. fdestr He He1 He2. fex He2 g Hg. fdestr Hg Hg1 Hg2.
  fexists z. fsplit; [exact Hz1|]. fsplit; [exact Hz2|]. fexists e. fsplit; [exact He1|].
  fexists g. fsplit; [|exact Hg2]. exact (agree_use_r f f' xi e g HA He1 Hg1).
Qed.
Lemma mch_agree {G} f f' xi p x m : G ⊢C Agree f f' xi -> G ⊢C Mch f xi p x m -> G ⊢C Mch f' xi p x m.
Proof.
  intros HA H. unfold Mch in H |- *. fall w. finst H w. fsplit.
  - fintro Hw. exact (mbody_agree f f' xi p x w HA (iff_l _ _ _ H Hw)).
  - fintro Hw. apply (iff_r _ _ _ H). exact (mbody_agree_r f f' xi p x w HA Hw).
Qed.
Lemma mch_agree_r {G} f f' xi p x m : G ⊢C Agree f f' xi -> G ⊢C Mch f' xi p x m -> G ⊢C Mch f xi p x m.
Proof.
  intros HA H. unfold Mch in H |- *. fall w. finst H w. fsplit.
  - fintro Hw. exact (mbody_agree_r f f' xi p x w HA (iff_l _ _ _ H Hw)).
  - fintro Hw. apply (iff_r _ _ _ H). exact (mbody_agree f f' xi p x w HA Hw).
Qed.
Lemma vq_agree {G} f f' xi p q : G ⊢C Agree f f' xi -> G ⊢C Vq f xi p q -> G ⊢C Vq f' xi p q.
Proof.
  intros HA H. unfold Vq in H |- *. fex H x Hx. fdestr Hx Hx1 Hx2. unfold Vrel in Hx2. fdestr Hx2 Hx3 Hx4.
  fex Hx4 m Hm. fdestr Hm Hm1 Hm2. fexists x. fsplit; [exact Hx1|]. unfold Vrel. fsplit; [exact Hx3|].
  fexists m. fsplit; [exact Hm1|]. exact (mch_agree f f' xi p x m HA Hm2).
Qed.
Lemma vq_agree_r {G} f f' xi p q : G ⊢C Agree f f' xi -> G ⊢C Vq f' xi p q -> G ⊢C Vq f xi p q.
Proof.
  intros HA H. unfold Vq in H |- *. fex H x Hx. fdestr Hx Hx1 Hx2. unfold Vrel in Hx2. fdestr Hx2 Hx3 Hx4.
  fex Hx4 m Hm. fdestr Hm Hm1 Hm2. fexists x. fsplit; [exact Hx1|]. unfold Vrel. fsplit; [exact Hx3|].
  fexists m. fsplit; [exact Hm1|]. exact (mch_agree_r f f' xi p x m HA Hm2).
Qed.

Lemma Scoll_loc {G} (HG : incl ZF0base G) p : G ⊢C SLoc Scoll p.
Proof.
  unfold SLoc. srs. fall f. fall f'. fall xi. fall v.
  fintro Hf. fintro Hf'. fintro Hxi. fintro HA. fintro H. unfold Sc in H |- *. fall q. finst H q. fsplit.
  - fintro Hq. exact (vq_agree f f' xi p q HA (iff_l _ _ _ H Hq)).
  - fintro Hq. apply (iff_r _ _ _ H). exact (vq_agree_r f f' xi p q HA Hq).
Qed.

Lemma Scoll_tot {G} (HG : incl ZF0base G) (Hv : In (forall_times 3 (ax_rep' vform)) G) p : G ⊢C STot Scoll p.
Proof.
  unfold STot. srs. fall f. fall xi. fintro Hf. fintro Hxi. fintro Hall.
  fobtain (sc_ex HG Hv f xi p) as v Hsv. fexists v. exact Hsv.
Qed.

Lemma Scoll_fun {G} (HG : incl ZF0base G) p : G ⊢C SFun Scoll p.
Proof.
  unfold SFun. srs. fall f. fall xi. fall v. fall v'. fintro Hf. fintro Hxi. fintro H1. fintro H2.
  unfold Sc in H1, H2. exact (ext_char HG _ v v' H1 H2).
Qed.


(** ** The recursion function F and the collapse P = ⋃ ran F *)
Definition Ran (f R : term) : form := ∀ ($0 ∈' R`[↑] ↔ ∃ App0 f`[↑]`[↑] $0 $1).
#[global] Arguments Ran : simpl never.
Lemma Ran_subst f R sg : (Ran f R)[sg] = Ran f`[sg] R`[sg].
Proof. psubst Ran. Qed.
#[global] Hint Rewrite Ran_subst : fsub.

Lemma ran_ex {G} (HG : incl ZF0base G) (Hin : In (forall_times 1 (ax_sep' ranform)) G) f :
  G ⊢C ∃ Ran f`[↑] $0.
Proof.
  fobtain (union_ex HG f) as U1 HU1. fobtain (union_ex HG U1) as U2 HU2.
  pose proof (sep_use _ 1 ranform (f .: var) U2 Hin ltac:(fbcomp)) as T. unfold ranform in T. simp_in T.
  fex T R HRc. fexists R. unfold Ran. fall y. finst HRc y. fsplit.
  - fintro Hy. exact (CE2 (iff_l _ _ _ HRc Hy)).
  - fintro Hy. apply (iff_r _ _ _ HRc). fsplit; [|exact Hy]. fex Hy x Hx. exact (app_val_in HG f x y U1 U2 HU1 HU2 Hx).
Qed.

(** z ∈ x with x of rank ξ: the rank of z is below ξ *)
Lemma rho_lt {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G) xi x z e :
  G ⊢C Ord0 xi -> G ⊢C Rho x xi -> G ⊢C z ∈' x -> G ⊢C Ord0 e -> G ⊢C Rho z e -> G ⊢C e ∈' xi.
Proof.
  intros Oxi Hx Hz Oe He. pose proof (Ax_wo_L _ HW) as HL.
  fobtain (LL_ex_g HG HR HOm HL xi Oxi) as Y HY.
  unfold Rho in Hx. fdestr Hx Hx1 Hx2. unfold InL1 in Hx1. fex Hx1 s Hs. fdestr Hs Hs1 Hs2.
  fex Hs2 Ys HYs. fdestr HYs HYs1 HYs2.
  fhave D : (LL_succ_g HG HR HOm HL xi s Y Ys Oxi Hs1 HY HYs1).
  fhave Sb : (Z_L.w_def_sub HG HR HOm HL Y Ys x D HYs2).
  fhave HzY : (Z_L.sub_use x Y z Sb Hz).
  fobtain (rho_ex HG (wox HR HOm HW) xi Y z Oxi HY HzY) as e' He'. fdestr He' He'1 He'2. fdestr He'2 He'3 He'4.
  fhave E : (rho_unique HG (wox HR HOm HW) z e e' Oe He'1 He He'4). fmem.
Qed.

Lemma appF_inv {G} (HG : incl ZF0base G) (HW : incl Ax_wo G) X F xi v x m :
  G ⊢C RecOK Scoll X F -> G ⊢C App0 F xi v -> G ⊢C App0 v x m ->
  G ⊢C x ∈' X ∧ Rho x xi ∧ Mch F xi X x m.
Proof.
  intros Hrec H1 H2. pose proof (hp_of HW) as HP.
  pose proof (Z_trec.recok_use HG HP Scoll X F xi v Hrec H1) as Hs. rewrite SR_Scoll in Hs.
  unfold App0 in H2. fex H2 q Hq. fdestr Hq Hq1 Hq2.
  unfold Sc in Hs. finst Hs q. fhave T : (iff_l _ _ _ Hs Hq1). unfold Vq in T. fex T x' Hx'. fdestr Hx' Hx'1 Hx'2.
  unfold Vrel in Hx'2. fdestr Hx'2 Hr Hm. fex Hm m' Hm'. fdestr Hm' Hm'1 Hm'2.
  fhave E : (op0_inj_g HG x m x' m' q Hq2 Hm'1). fdestr E E1 E2.
  fsplit; [fsplit|].
  - fmem.
  - frew E1 (Rho $0 xi`[↑]). exact Hr.
  - frew E1 (Mch F`[↑] xi`[↑] X`[↑] $0 m`[↑]). frew E2 (Mch F`[↑] xi`[↑] X`[↑] x'`[↑] $0). exact Hm'2.
Qed.

Lemma appF_intro {G} (HG : incl ZF0base G) (HW : incl Ax_wo G) X F xi v x m :
  G ⊢C RecOK Scoll X F -> G ⊢C App0 F xi v -> G ⊢C x ∈' X -> G ⊢C Rho x xi -> G ⊢C Mch F xi X x m ->
  G ⊢C App0 v x m.
Proof.
  intros Hrec H1 Hx Hr Hm. pose proof (hp_of HW) as HP.
  pose proof (Z_trec.recok_use HG HP Scoll X F xi v Hrec H1) as Hs. rewrite SR_Scoll in Hs.
  fobtain (op0_ex' HG x m) as q Hq. apply (app0_intro_g v x m q Hq).
  unfold Sc in Hs. finst Hs q. apply (iff_r _ _ _ Hs). unfold Vq. fexists x. fsplit; [exact Hx|].
  unfold Vrel. fsplit; [exact Hr|]. fexists m. fsplit; [exact Hq|exact Hm].
Qed.

Lemma appP_el {G} (HG : incl ZF0base G) F R P x m : G ⊢C Ran F R -> G ⊢C is_union R P -> G ⊢C App0 P x m ->
  G ⊢C ∃ (∃ (App0 F`[↑]`[↑] $1 $0 ∧ App0 $0 x`[↑]`[↑] m`[↑]`[↑])).
Proof.
  intros HRan HUP H. unfold App0 in H. fex H q Hq. fdestr Hq Hq1 Hq2.
  fhave T : (union_el HG R P q HUP Hq1). fex T v Hv. fdestr Hv Hv1 Hv2.
  unfold Ran in HRan. finst HRan v. fhave T : (iff_l _ _ _ HRan Hv1). fex T xi Hxi.
  fexists xi. fexists v. fsplit; [exact Hxi|]. exact (app0_intro_g v x m q Hq2 Hv2).
Qed.

Lemma appP_in {G} (HG : incl ZF0base G) F R P xi v x m : G ⊢C Ran F R -> G ⊢C is_union R P ->
  G ⊢C App0 F xi v -> G ⊢C App0 v x m -> G ⊢C App0 P x m.
Proof.
  intros HRan HUP H1 H2. unfold App0 in H2. fex H2 q Hq. fdestr Hq Hq1 Hq2.
  apply (app0_intro_g P x m q Hq2). apply (union_in HG R P v q HUP); [|exact Hq1].
  unfold Ran in HRan. finst HRan v. apply (iff_r _ _ _ HRan). fexists xi. exact H1.
Qed.

Section Build.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G)
  (HC : incl Ax_coll G).
Context (X g Yg F R P : term).
Context (Og : G ⊢C Ord0 g) (HYg : G ⊢C LL g Yg) (HXY : G ⊢C ∀ ($0 ∈' X`[↑] → $0 ∈' Yg`[↑]))
  (HFf : G ⊢C Fun0 F) (Hdom : G ⊢C Dom0 F g) (Hrec : G ⊢C RecOK Scoll X F)
  (HRan : G ⊢C Ran F R) (HUP : G ⊢C is_union R P).

Lemma collP_fun : G ⊢C Fun0 P.
Proof using All.
  pose proof (hp_of HW) as HP. apply (Z_trec.fun0_intro HG HP).
  - apply (Z_trec.isrel0_intro HG HP). fall q. fintro Hq. fhave T : (union_el HG R P q HUP Hq). fex T v Hv. fdestr Hv Hv1 Hv2.
    pose proof HRan as HRa. unfold Ran in HRa. finst HRa v. fhave T : (iff_l _ _ _ HRa Hv1). fex T xi Hxi.
    pose proof (Z_trec.recok_use HG HP Scoll X F xi v Hrec Hxi) as Hs. rewrite SR_Scoll in Hs. unfold Sc in Hs.
    finst Hs q. fhave T : (iff_l _ _ _ Hs Hv2). unfold Vq in T. fex T x Hx. fdestr Hx Hx1 Hx2.
    unfold Vrel in Hx2. fdestr Hx2 Hx3 Hx4. fex Hx4 m Hm. fexists x. fexists m. exact (CE1 Hm).
  - fall x. fall m. fall m'. fintro H1. fintro H2.
    fobtain (appP_el HG F R P x m HRan HUP H1) as xi Hxi. fex Hxi v Hv. fdestr Hv Hv1 Hv2.
    fobtain (appP_el HG F R P x m' HRan HUP H2) as xi' Hxi'. fex Hxi' v' Hv'. fdestr Hv' Hv1' Hv2'.
    fhave A : (appF_inv HG HW X F xi v x m Hrec Hv1 Hv2). fdestr A A12 A3. fdestr A12 A1 A2.
    fhave A' : (appF_inv HG HW X F xi' v' x m' Hrec Hv1' Hv2'). fdestr A' A12' A3'. fdestr A12' A1' A2'.
    fhave Oxi : (ord_el_g g xi Og (dom0_in_g HG F g xi v Hdom Hv1)).
    fhave Oxi' : (ord_el_g g xi' Og (dom0_in_g HG F g xi' v' Hdom Hv1')).
    fhave E : (rho_unique HG (wox HR HOm HW) x xi xi' Oxi Oxi' A2 A2').
    frew_in E (Mch F`[↑] $0 X`[↑] x`[↑] m'`[↑]) A3'.
    unfold Mch in A3, A3'. exact (ext_char HG _ m m' A3 A3').
Qed.

Lemma collP_dom : G ⊢C Dom0 P X.
Proof using All.
  pose proof (hp_of HW) as HP. apply (Z_trec.dom0_intro HG HP).
  - fall x. fintro Hx. pose proof HXY as HXx. finst HXx x. fmp HXx Hx.
    fobtain (rho_ex HG (wox HR HOm HW) g Yg x Og HYg HXx) as xi Hxi. fdestr Hxi Oxi Hxi2. fdestr Hxi2 Hxig Hrho.
    fobtain (dom0_app_g HG F g xi Hdom Hxig) as v Hv.
    fobtain (mch_ex HG (in_m HC) F xi X x) as m Hm.
    fexists m. apply (appP_in HG F R P xi v x m HRan HUP Hv).
    exact (appF_intro HG HW X F xi v x m Hrec Hv Hx Hrho Hm).
  - fall x. fall m. fintro H. fobtain (appP_el HG F R P x m HRan HUP H) as xi Hxi. fex Hxi v Hv. fdestr Hv Hv1 Hv2.
    fhave A : (appF_inv HG HW X F xi v x m Hrec Hv1 Hv2). exact (CE1 (CE1 A)).
Qed.

Lemma collP_eq : G ⊢C ∀ (∀ (App0 P`[↑]`[↑] $1 $0 →
     ∀ ($0 ∈' $1 ↔ ∃ ($0 ∈' X`[↑]`[↑]`[↑]`[↑] ∧ ($0 ∈' $3 ∧ App0 P`[↑]`[↑]`[↑]`[↑] $0 $1))))).
Proof using All.
  fall x. fall m. fintro H. fall w.
  fobtain (appP_el HG F R P x m HRan HUP H) as xi Hxi. fex Hxi v Hv. fdestr Hv Hv1 Hv2.
  fhave A : (appF_inv HG HW X F xi v x m Hrec Hv1 Hv2). fdestr A A12 A3. fdestr A12 A1 A2.
  fhave Oxi : (ord_el_g g xi Og (dom0_in_g HG F g xi v Hdom Hv1)).
  unfold Mch in A3. finst A3 w. fsplit.
  - fintro Hw. fhave T : (iff_l _ _ _ A3 Hw). unfold Mbody in T. fex T z Hz. fdestr Hz Hz1 Hz23. fdestr Hz23 Hz2 Hz3.
    fex Hz3 e He. fdestr He He1 He2. fex He2 h Hh. fdestr Hh Hh1 Hh2.
    fexists z. fsplit; [exact Hz1|]. fsplit; [exact Hz2|]. exact (appP_in HG F R P e h z w HRan HUP Hh1 Hh2).
  - fintro Hw. fex Hw z Hz. fdestr Hz Hz1 Hz23. fdestr Hz23 Hz2 Hz3.
    fobtain (appP_el HG F R P z w HRan HUP Hz3) as e He. fex He h Hh. fdestr Hh Hh1 Hh2.
    fhave B : (appF_inv HG HW X F e h z w Hrec Hh1 Hh2). fdestr B B12 B3. fdestr B12 B1 B2.
    fhave Oe : (ord_el_g g e Og (dom0_in_g HG F g e h Hdom Hh1)).
    fhave Hlt : (rho_lt HG HR HOm HW xi x z e Oxi A2 Hz2 Oe B2).
    apply (iff_r _ _ _ A3). unfold Mbody. fexists z. fsplit; [exact Hz1|]. fsplit; [exact Hz2|].
    fexists e. fsplit; [exact Hlt|]. fexists h. fsplit; [exact Hh1|exact Hh2].
Qed.

End Build.

Lemma coll_ex_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G)
  (HC : incl Ax_coll G) X : G ⊢C ∀ ($0 ∈' X`[↑] → Lform) -> G ⊢C ∃ (∃ Coll X`[↑]`[↑] $1 $0).
Proof.
  intros HXL. pose proof (Ax_wo_L _ HW) as HL. pose proof (ho_of HW) as HO.
  fobtain (Z_axL.L_bound HG HR HOm HL X (in_pow HC)) as g Hg. fex Hg Yg HYg. fdestr HYg H12 H3. fdestr H12 Og HYg'.
  fassert HXY : (∀ ($0 ∈' X`[↑] → $0 ∈' Yg`[↑])).
  { fall x. fintro Hx. finst H3 x. fmp H3 Hx. apply (IE H3). finst HXL x. fmp HXL Hx. exact HXL. }
  fobtain (rec_ex HG HR HO Scoll fb_Scoll (in_rec HC) X g (Scoll_loc HG X) (Scoll_tot HG (in_v HC) X)
             (Scoll_fun HG X) Og) as F HF.
  fdestr HF HF12 Hrec. fdestr HF12 HFf Hdom.
  fobtain (ran_ex HG (in_ran HC) F) as R HRan.
  fobtain (union_ex HG R) as P HUP.
  fobtain (ran_ex HG (in_ran HC) P) as M HM.
  fexists P. fexists M. unfold Coll. fsplit; [fsplit; [fsplit|]|].
  - exact (collP_fun HG HR HOm HW HC X g Yg F R P Og HYg' HXY HFf Hdom Hrec HRan HUP).
  - exact (collP_dom HG HR HOm HW HC X g Yg F R P Og HYg' HXY HFf Hdom Hrec HRan HUP).
  - exact HM.
  - exact (collP_eq HG HR HOm HW HC X g Yg F R P Og HYg' HXY HFf Hdom Hrec HRan HUP).
Qed.


(** ** Properties of a collapse *)
Lemma coll_fun {G} X P M : G ⊢C Coll X P M -> G ⊢C Fun0 P.
Proof. intros H. unfold Coll in H. exact (CE1 (CE1 (CE1 H))). Qed.
Lemma coll_dom {G} X P M : G ⊢C Coll X P M -> G ⊢C Dom0 P X.
Proof. intros H. unfold Coll in H. exact (CE2 (CE1 (CE1 H))). Qed.
Lemma coll_ran {G} X P M : G ⊢C Coll X P M -> G ⊢C Ran P M.
Proof. intros H. unfold Coll in H. unfold Ran. exact (CE2 (CE1 H)). Qed.
Lemma coll_eq_l {G} X P M x m w : G ⊢C Coll X P M -> G ⊢C App0 P x m -> G ⊢C w ∈' m ->
  G ⊢C ∃ ($0 ∈' X`[↑] ∧ ($0 ∈' x`[↑] ∧ App0 P`[↑] $0 w`[↑])).
Proof.
  intros H Hm Hw. unfold Coll in H. pose proof (CE2 H) as H4. finst H4 x m. fmp H4 Hm. finst H4 w.
  exact (iff_l _ _ _ H4 Hw).
Qed.
Lemma coll_eq_r {G} X P M x m z w : G ⊢C Coll X P M -> G ⊢C App0 P x m -> G ⊢C z ∈' X -> G ⊢C z ∈' x ->
  G ⊢C App0 P z w -> G ⊢C w ∈' m.
Proof.
  intros H Hm Hz Hzx Hzw. unfold Coll in H. pose proof (CE2 H) as H4. finst H4 x m. fmp H4 Hm. finst H4 w.
  apply (iff_r _ _ _ H4). fexists z. fsplit; [exact Hz|]. fsplit; [exact Hzx|exact Hzw].
Qed.

(** z ∈ a \ b, P(a) = P(b) = n: some z' ∈ X ∩ b with P(z') = P(z), z' ≢ z *)
Lemma coll_sep_step {G} (HG : incl ZF0base G) X P M a b n z :
  G ⊢C Coll X P M -> G ⊢C App0 P a n -> G ⊢C App0 P b n -> G ⊢C z ∈' X -> G ⊢C z ∈' a -> G ⊢C ¬ (z ∈' b) ->
  G ⊢C ∃ ($0 ∈' X`[↑] ∧ ($0 ∈' b`[↑] ∧ ((¬ ($0 ≡' z`[↑])) ∧
           ∃ (App0 P`[↑]`[↑] z`[↑]`[↑] $0 ∧ App0 P`[↑]`[↑] $1 $0)))).
Proof.
  intros HCl Ha Hb Hz Hza Hzb.
  fobtain (dom0_app_g HG P X z (coll_dom X P M HCl) Hz) as w Hw.
  fhave Hwn : (coll_eq_r X P M a n z w HCl Ha Hz Hza Hw).
  fhave T : (coll_eq_l X P M b n w HCl Hb Hwn). fex T z' Hz'. fdestr Hz' Hz'1 Hz'23. fdestr Hz'23 Hz'2 Hz'3.
  fexists z'. fsplit; [exact Hz'1|]. fsplit; [exact Hz'2|]. fsplit.
  - fintro E. apply (IE Hzb). fmem.
  - fexists w. fsplit; [exact Hw|exact Hz'3].
Qed.

Lemma coll_inj_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (Hin : In (forall_times 2 (ax_sep' injform)) G)
  X P M x x' m : G ⊢C Coll X P M -> G ⊢C ExtX X -> G ⊢C x ∈' X -> G ⊢C x' ∈' X ->
  G ⊢C App0 P x m -> G ⊢C App0 P x' m -> G ⊢C x ≡' x'.
Proof.
  intros HCl HE Hx Hx' H1 H2. fcontra Hne.
  pose proof (sep_use _ 2 injform (X .: P .: var) X Hin ltac:(fbcomp)) as T. unfold injform in T. simp_in T.
  fex T B HB.
  fassert HxB : (x ∈' B).
  { pose proof HB as HBx. finst HBx x. apply (iff_r _ _ _ HBx). fsplit; [exact Hx|]. unfold Bad.
    fexists x'. fsplit; [fsplit; [exact Hx'|]|].
    - fintro E. apply (IE Hne). feq.
    - fexists m. fsplit; [exact H1|exact H2]. }
  fhave T : (reg_use HG HR B x HxB). fex T y Hy. fdestr Hy Hy1 Hy2.
  pose proof HB as HBy. finst HBy y. fhave Hy3 : (iff_l _ _ _ HBy Hy1). clear HBy. fdestr Hy3 HyX HyBad.
  unfold Bad in HyBad. fex HyBad y' Hy'. fdestr Hy' Hy'12 Hy'3. fdestr Hy'12 Hy'X Hne'.
  fex Hy'3 n Hn. fdestr Hn Hn1 Hn2.
  unfold ExtX in HE. finst HE y. fmp HE HyX. finst HE y'. fmp HE Hy'X.
  fassert Hne2 : (¬ (y ≡' y')). { fintro E. apply (IE Hne'). feq. }
  fmp HE Hne2. fex HE z Hz. fdestr Hz HzX Hzd.
  apply (XM_rule _ (z ∈' y)).
  - fintro Hzy.
    fassert Hzy' : (¬ (z ∈' y')). { fintro K. apply (IE Hzd). fsplit; fintro K'; [exact K|exact Hzy]. }
    fhave S : (coll_sep_step HG X P M y y' n z HCl Hn1 Hn2 HzX Hzy Hzy').
    fex S z' Hz'. fdestr Hz' Hz'1 Hz'234. fdestr Hz'234 Hz'2 Hz'34. fdestr Hz'34 Hz'3 Hz'4.
    finst Hy2 z. fmp Hy2 Hzy. apply (IE Hy2). finst HB z. apply (iff_r _ _ _ HB). fsplit; [exact HzX|].
    unfold Bad. fexists z'. fsplit; [fsplit; [exact Hz'1|exact Hz'3]|exact Hz'4].
  - fintro Hzy.
    fassert Hzy' : (z ∈' y').
    { fcontra K. apply (IE Hzd). fsplit; fintro K'; fabsurd; [exact (IE Hzy K')|exact (IE K K')]. }
    fhave S : (coll_sep_step HG X P M y' y n z HCl Hn2 Hn1 HzX Hzy' Hzy).
    fex S z' Hz'. fdestr Hz' Hz'1 Hz'234. fdestr Hz'234 Hz'2 Hz'34. fdestr Hz'34 Hz'3 Hz'4.
    finst Hy2 z'. fmp Hy2 Hz'2. apply (IE Hy2). finst HB z'. apply (iff_r _ _ _ HB). fsplit; [exact Hz'1|].
    unfold Bad. fexists z. fsplit; [fsplit; [exact HzX|]|].
    + fintro E. apply (IE Hz'3). feq.
    + fex Hz'4 w Hw. fdestr Hw Hw1 Hw2. fexists w. fsplit; [exact Hw2|exact Hw1].
Qed.

Lemma coll_iso_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (Hin : In (forall_times 2 (ax_sep' injform)) G)
  X P M : G ⊢C Coll X P M -> G ⊢C ExtX X -> G ⊢C IsoF X P M.
Proof.
  intros HCl HE. unfold IsoF. fsplit; [fsplit|].
  - fall x. fintro Hx. fobtain (dom0_app_g HG P X x (coll_dom X P M HCl) Hx) as m Hm. fexists m. fsplit; [exact Hm|].
    pose proof (coll_ran X P M HCl) as HM. unfold Ran in HM. finst HM m. apply (iff_r _ _ _ HM). fexists x. exact Hm.
  - fall m. fintro Hm. pose proof (coll_ran X P M HCl) as HM. unfold Ran in HM. finst HM m.
    fhave T : (iff_l _ _ _ HM Hm). fex T x Hx. fexists x.
    fsplit; [exact (dom0_in_g HG P X x m (coll_dom X P M HCl) Hx)|exact Hx].
  - fall a. fall b. fall c. fall d. fintro Ha. fintro Hb. fintro Hc. fintro Hd. fsplit.
    + fsplit.
      * fintro Hab. exact (coll_eq_r X P M b d a c HCl Hd Ha Hab Hc).
      * fintro Hcd. fhave T : (coll_eq_l X P M b d c HCl Hd Hcd). fex T z Hz. fdestr Hz Hz1 Hz23.
        fdestr Hz23 Hz2 Hz3.
        fhave E : (coll_inj_g HG HR Hin X P M a z c HCl HE Ha Hz1 Hc Hz3). fmem.
    + fsplit.
      * fintro E. frew_in E (App0 P`[↑] $0 c`[↑]) Hc. exact (fun0_app_g HG P b c d (coll_fun X P M HCl) Hc Hd).
      * fintro E. frew_in E (App0 P`[↑] b`[↑] $0) Hd. exact (coll_inj_g HG HR Hin X P M a b c HCl HE Ha Hb Hc Hd).
Qed.

Lemma coll_trans_g {G} (HG : incl ZF0base G) X P M : G ⊢C Coll X P M -> G ⊢C Trans0 M.
Proof.
  intros HCl. unfold Trans0. fall m. fintro Hm. fall w. fintro Hw.
  pose proof (coll_ran X P M HCl) as HM. unfold Ran in HM. pose proof HM as HM'. finst HM m.
  fhave T : (iff_l _ _ _ HM Hm). fex T x Hx.
  fhave T : (coll_eq_l X P M x m w HCl Hx Hw). fex T z Hz. fdestr Hz Hz1 Hz23. fdestr Hz23 Hz2 Hz3.
  finst HM' w. apply (iff_r _ _ _ HM'). fexists z. exact Hz3.
Qed.

(** P(y) = y when P(z) = z for all z ∈ y (and y ⊆ X) *)
Lemma fix_of {G} (HG : incl ZF0base G) X P M y : G ⊢C Coll X P M -> G ⊢C y ∈' X ->
  G ⊢C ∀ ($0 ∈' y`[↑] → $0 ∈' X`[↑] ∧ App0 P`[↑] $0 $0) -> G ⊢C App0 P y y.
Proof.
  intros HCl Hy Hall. fobtain (dom0_app_g HG P X y (coll_dom X P M HCl) Hy) as m Hm.
  fassert E : (m ≡' y).
  { apply (ext_rule HG); unfold sub'; fall w; fintro Hw.
    - fhave T : (coll_eq_l X P M y m w HCl Hm Hw). fex T z Hz. fdestr Hz Hz1 Hz23. fdestr Hz23 Hz2 Hz3.
      finst Hall z. fmp Hall Hz2. fdestr Hall Hall1 Hall2.
      fhave E : (fun0_app_g HG P z z w (coll_fun X P M HCl) Hall2 Hz3). fmem.
    - finst Hall w. fmp Hall Hw. fdestr Hall Hall1 Hall2. exact (coll_eq_r X P M y m w w HCl Hm Hall1 Hw Hall2). }
  frew_in E (App0 P`[↑] y`[↑] $0) Hm. exact Hm.
Qed.

Lemma coll_fix_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (Hin : In (forall_times 1 (ax_sep' fixform)) G)
  X P M T t : G ⊢C Coll X P M -> G ⊢C Trans0 T -> G ⊢C Sub0 T X -> G ⊢C t ∈' T -> G ⊢C App0 P t t.
Proof.
  intros HCl HT HTX Ht. fcontra Hn.
  pose proof (sep_use _ 1 fixform (P .: var) T Hin ltac:(fbcomp)) as S. unfold fixform in S. simp_in S.
  fex S B HB.
  fassert HtB : (t ∈' B). { pose proof HB as HBt. finst HBt t. apply (iff_r _ _ _ HBt). fsplit; [exact Ht|exact Hn]. }
  fhave R : (reg_use HG HR B t HtB). fex R u Hu. fdestr Hu Hu1 Hu2.
  pose proof HB as HBu. finst HBu u. fhave K : (iff_l _ _ _ HBu Hu1). fdestr K HuT HuN.
  apply (IE HuN). apply (fix_of HG X P M u HCl (Z_L.sub_use T X u HTX HuT)).
  fall z. fintro Hz.
  fhave HzT : (trans_el T u z HT HuT Hz).
  fsplit; [exact (Z_L.sub_use T X z HTX HzT)|].
  fcontra K'. finst Hu2 z. fmp Hu2 Hz. apply (IE Hu2). finst HB z. apply (iff_r _ _ _ HB). fsplit; [exact HzT|exact K'].
Qed.

Lemma coll_fix_sub_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (Hin : In (forall_times 1 (ax_sep' fixform)) G)
  X P M T y : G ⊢C Coll X P M -> G ⊢C Trans0 T -> G ⊢C Sub0 T X -> G ⊢C Sub0 y T ->
  G ⊢C y ∈' X -> G ⊢C App0 P y y.
Proof.
  intros HCl HT HTX HyT Hy. apply (fix_of HG X P M y HCl Hy). fall z. fintro Hz.
  fhave HzT : (Z_L.sub_use y T z HyT Hz).
  fsplit; [exact (Z_L.sub_use T X z HTX HzT)|exact (coll_fix_g HG HR Hin X P M T z HCl HT HTX HzT)].
Qed.


Section Coll.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G)
  (HC : incl Ax_coll G).

Theorem coll_ex X : G ⊢C ∀ ($0 ∈' X`[↑] → Lform) -> G ⊢C ∃ (∃ Coll X`[↑]`[↑] $1 $0).
Proof using HG HR HOm HW HC. exact (coll_ex_g HG HR HOm HW HC X). Qed.

Lemma coll_inj X P M x x' m : G ⊢C Coll X P M -> G ⊢C ExtX X -> G ⊢C x ∈' X -> G ⊢C x' ∈' X ->
  G ⊢C App0 P x m -> G ⊢C App0 P x' m -> G ⊢C x ≡' x'.
Proof using HG HR HOm HW HC. exact (coll_inj_g HG HR (in_inj HC) X P M x x' m). Qed.

Lemma coll_iso X P M : G ⊢C Coll X P M -> G ⊢C ExtX X -> G ⊢C IsoF X P M.
Proof using HG HR HOm HW HC. exact (coll_iso_g HG HR (in_inj HC) X P M). Qed.

Lemma coll_trans X P M : G ⊢C Coll X P M -> G ⊢C Trans0 M.
Proof using HG HR HOm HW HC. exact (coll_trans_g HG X P M). Qed.

Lemma coll_fix X P M T t : G ⊢C Coll X P M -> G ⊢C Trans0 T -> G ⊢C Sub0 T X -> G ⊢C t ∈' T ->
  G ⊢C App0 P t t.
Proof using HG HR HOm HW HC. exact (coll_fix_g HG HR (in_fix HC) X P M T t). Qed.

Lemma coll_fix_sub X P M T y : G ⊢C Coll X P M -> G ⊢C Trans0 T -> G ⊢C Sub0 T X -> G ⊢C Sub0 y T ->
  G ⊢C y ∈' X -> G ⊢C App0 P y y.
Proof using HG HR HOm HW HC. exact (coll_fix_sub_g HG HR (in_fix HC) X P M T y). Qed.

End Coll.


(* Print Assumptions coll_ex. Print Assumptions coll_iso. Print Assumptions coll_fix_sub. *)
