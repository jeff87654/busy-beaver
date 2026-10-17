(** * SU_gru: weak universes (Gru0) are Grothendieck universes (Gru), in ZF.

    Gru0 u is the w-clause of UG' read in ZF with φ(a, y, f) := (a, y) ∈ f:

      Gru0 u := ( Tr u ∧ ∀x∈u ∃W∈u ∀z (z⊆x → z∈W) )
              ∧ ∀f ∀B ( B∈u → ∀a∈B ∃y (y∈u ∧ (a,y)∈f) →
                        ∃C ( ∀a∈B ∀y ((a,y)∈f → ∃y' ((a,y')∈f ∧ y'∈C)) ∧ ∃U (U∈u ∧ ∀y∈C ∀z∈y z∈U) ) )
      GU0 := ∀x ∃u (x∈u ∧ Gru0 u)

    [gru0_gru]: Gru0 u → Gru u (subsets of members are members; 𝒫x ⊆ W_x; {x,y} via the family
    {(∅,{x}), ({∅},{y})} over {∅,{∅}} ∈ u; ∪ran f separated from the bound U).
    [GU_of_GU0]: ZF0 + GU0 ⊢ GU (one separation instance, [Ax_gru]). *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From ZFC Require Import Z_rel Z_base Z_prim.
From M254S Require Import S_gic.
From M254TG Require Import SU_gu SU_V.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition Gru0 (u : term) : form :=
  (Trans0 u ∧ ∀ ($0 ∈' u`[↑] → ∃ ($0 ∈' u`[↑]`[↑] ∧ ∀ (Sub0 $0 $2 → $0 ∈' $1)))) ∧
  ∀ ∀ ($0 ∈' u`[↑]`[↑] → (∀ ($0 ∈' $1 → ∃ ($0 ∈' u`[↑]`[↑]`[↑]`[↑] ∧ App0 $3 $1 $0))) →
       ∃ ((∀ ($0 ∈' $2 → ∀ (App0 $4 $1 $0 → ∃ (App0 $5 $2 $0 ∧ $0 ∈' $3)))) ∧
          ∃ ($0 ∈' u`[↑]`[↑]`[↑]`[↑] ∧ ∀ ($0 ∈' $2 → ∀ ($0 ∈' $1 → $0 ∈' $2))))).
#[global] Arguments Gru0 : simpl never.
Lemma Gru0_subst u sg : (Gru0 u)[sg] = Gru0 u`[sg].
Proof. psubst Gru0. Qed.
#[global] Hint Rewrite Gru0_subst : fsub.

Definition GU0 : form := ∀ ∃ ($1 ∈' $0 ∧ Gru0 $0).
Lemma GU0_closed : closedf GU0.
Proof. unfold GU0, Gru0. fbcomp. Qed.

(** separation for ∪ran f: $0 = z, $1 = f *)
Definition psi_ur : form := ∃ ((∃ App0 $3 $0 $1) ∧ $1 ∈' $0).
Lemma fb_ur : fb 2 psi_ur.
Proof. fbcomp. Qed.
Definition Ax_gru : list form := [forall_times 1 (ax_sep' psi_ur)].
Lemma Ax_gru_ok a : In a Ax_gru -> ZF0 a.
Proof. intros [<-|[]]. apply ZF0_sep, sep_closed, fb_ur. Qed.

Lemma HP0 {G} : incl Ax_prim G.
Proof. intros a []. Qed.

(** ** Accessors *)
Section Acc.
Lemma g0_tr {G} u a b : G ⊢C Gru0 u -> G ⊢C a ∈' u -> G ⊢C b ∈' a -> G ⊢C b ∈' u.
Proof.
  intros H Ha Hb. unfold Gru0 in H. pose proof (CE1 (CE1 H)) as T. unfold Trans0 in T. finst T a.
  fmp T Ha. finst T b. exact (IE T Hb).
Qed.
Lemma g0_cont {G} u x : G ⊢C Gru0 u -> G ⊢C x ∈' u ->
  G ⊢C ∃ ($0 ∈' u`[↑] ∧ ∀ (Sub0 $0 x`[↑]`[↑] → $0 ∈' $1)).
Proof. intros H Hx. unfold Gru0 in H. pose proof (CE2 (CE1 H)) as T. finst T x. exact (IE T Hx). Qed.
Lemma g0_sub {G} u x s : G ⊢C Gru0 u -> G ⊢C x ∈' u -> G ⊢C Sub0 s x -> G ⊢C s ∈' u.
Proof.
  intros H Hx Hs. fobtain (g0_cont u x H Hx) as W HW. fdestr HW HWu HWc. finst HWc s. fmp HWc Hs.
  exact (g0_tr u W s H HWu HWc).
Qed.
Lemma g0_fam {G} u f B : G ⊢C Gru0 u -> G ⊢C B ∈' u ->
  G ⊢C ∀ ($0 ∈' B`[↑] → ∃ ($0 ∈' u`[↑]`[↑] ∧ App0 f`[↑]`[↑] $1 $0)) ->
  G ⊢C ∃ ((∀ ($0 ∈' B`[↑]`[↑] → ∀ (App0 f`[↑]`[↑]`[↑] $1 $0 → ∃ (App0 f`[↑]`[↑]`[↑]`[↑] $2 $0 ∧ $0 ∈' $3)))) ∧
          ∃ ($0 ∈' u`[↑]`[↑] ∧ ∀ ($0 ∈' $2 → ∀ ($0 ∈' $1 → $0 ∈' $2)))).
Proof. intros H HB Ht. unfold Gru0 in H. pose proof (CE2 H) as T. finst T f B. fmp T HB. exact (IE T Ht). Qed.
End Acc.

Lemma sub_self {G} x : G ⊢C Sub0 x x.
Proof. unfold Sub0. fall z. fintro Hz. exact Hz. Qed.

(** a member of a member of C lies in U *)
Local Ltac bound HU y z := let T := fresh in pose proof HU as T; finst T y.

(** ** Gru0 → Gru *)
Lemma gru0_gru {G} (HG : incl ZF0base G) (HA : incl Ax_gru G) u : G ⊢C Gru0 u -> G ⊢C Gru u.
Proof.
  intros H. unfold Gru. fsplit.
  { unfold Gru0 in H. exact (CE1 (CE1 H)). }
  fall x. fintro Hx. fsplit; [fsplit|].
  - (* power set *)
    fobtain (pow_ex HG x) as P HP. fobtain (g0_cont u x H Hx) as W HW. fdestr HW HWu HWc.
    fexists P. fsplit.
    + apply (g0_sub u W P H HWu). unfold Sub0. fall z. fintro Hz. finst HWc z. apply (IE HWc).
      unfold is_power in HP. finst HP z. exact (iff_l _ _ _ HP Hz).
    + unfold is_power in HP. exact HP.
  - (* pairs *)
    fall y. fintro Hy.
    fobtain (emp0_ex HG) as e He.
    fassert Heu : (e ∈' u).
    { apply (g0_sub u x e H Hx). unfold Sub0. fall z. fintro Hz. fabsurd. unfold Emp0 in He. finst He z. exact (IE He Hz). }
    fobtain (pair0_ex HG HP0 e e) as s Hs.
    fassert Hsu : (s ∈' u).
    { fobtain (g0_cont u e H Heu) as W HW. fdestr HW HWu HWc. apply (g0_sub u W s H HWu).
      unfold Sub0. fall z. fintro Hz. unfold Pair0 in Hs. pose proof (CE2 Hs) as T. finst T z. fmp T Hz.
      finst HWc z. apply (IE HWc). fcases T T1 T2; frew T1 (Sub0 $0 e`[↑]) || frew T2 (Sub0 $0 e`[↑]); exact (sub_self e). }
    fobtain (pair0_ex HG HP0 e s) as B HB.
    fassert HBu : (B ∈' u).
    { fobtain (g0_cont u s H Hsu) as W HW. fdestr HW HWu HWc. apply (g0_sub u W B H HWu).
      unfold Sub0. fall z. fintro Hz. unfold Pair0 in HB. pose proof (CE2 HB) as T. finst T z. fmp T Hz.
      finst HWc z. apply (IE HWc). fcases T T1 T2.
      - frew T1 (Sub0 $0 s`[↑]). unfold Sub0. fall w. fintro Hw. fabsurd. unfold Emp0 in He. finst He w. exact (IE He Hw).
      - frew T2 (Sub0 $0 s`[↑]). exact (sub_self s). }
    fassert Hes : (e ≡' s → ⊥).
    { fintro E. unfold Pair0 in Hs. pose proof (CE1 (CE1 Hs)) as T. frew_in E (e`[↑] ∈' $0) T.
      unfold Emp0 in He. finst He e. fapply He. exact T. }
    (* singletons {x}, {y} in u *)
    fobtain (pair0_ex HG HP0 x x) as sx Hsx. fobtain (pair0_ex HG HP0 y y) as sy Hsy.
    fassert Hsxu : (sx ∈' u).
    { fobtain (g0_cont u x H Hx) as W HW. fdestr HW HWu HWc. apply (g0_sub u W sx H HWu).
      unfold Sub0. fall z. fintro Hz. unfold Pair0 in Hsx. pose proof (CE2 Hsx) as T. finst T z. fmp T Hz.
      finst HWc z. apply (IE HWc). fcases T T1 T2; frew T1 (Sub0 $0 x`[↑]) || frew T2 (Sub0 $0 x`[↑]); exact (sub_self x). }
    fassert Hsyu : (sy ∈' u).
    { fobtain (g0_cont u y H Hy) as W HW. fdestr HW HWu HWc. apply (g0_sub u W sy H HWu).
      unfold Sub0. fall z. fintro Hz. unfold Pair0 in Hsy. pose proof (CE2 Hsy) as T. finst T z. fmp T Hz.
      finst HWc z. apply (IE HWc). fcases T T1 T2; frew T1 (Sub0 $0 y`[↑]) || frew T2 (Sub0 $0 y`[↑]); exact (sub_self y). }
    (* f = {(e, {x}), (s, {y})} *)
    fobtain (op0_ex HG HP0 e sx) as c1 Hc1. fobtain (op0_ex HG HP0 s sy) as c2 Hc2.
    fobtain (pair0_ex HG HP0 c1 c2) as f Hf.
    fassert Hfe : (App0 f e sx). { apply (app0_intro_g f e sx c1 Hc1). unfold Pair0 in Hf. exact (CE1 (CE1 Hf)). }
    fassert Hfs : (App0 f s sy). { apply (app0_intro_g f s sy c2 Hc2). unfold Pair0 in Hf. exact (CE2 (CE1 Hf)). }
    (* the only images: (e, v) ∈ f → v = {x};  (s, v) ∈ f → v = {y} *)
    fassert Hfe' : (∀ (App0 f`[↑] e`[↑] $0 → $0 ≡' sx`[↑])).
    { fall v. fintro Hv. unfold App0 in Hv. fex Hv c Hc. fdestr Hc Hcf Hcop. unfold Pair0 in Hf.
      pose proof (CE2 Hf) as T. finst T c. fmp T Hcf. fcases T T1 T2.
      - frew_in T1 (OP0 e`[↑] v`[↑] $0) Hcop. fhave E : (op0_inj_g HG e v e sx c1 Hcop Hc1). exact (CE2 E).
      - frew_in T2 (OP0 e`[↑] v`[↑] $0) Hcop. fhave E : (op0_inj_g HG e v s sy c2 Hcop Hc2). fabsurd.
        apply (IE Hes). exact (CE1 E). }
    fassert Hfs' : (∀ (App0 f`[↑] s`[↑] $0 → $0 ≡' sy`[↑])).
    { fall v. fintro Hv. unfold App0 in Hv. fex Hv c Hc. fdestr Hc Hcf Hcop. unfold Pair0 in Hf.
      pose proof (CE2 Hf) as T. finst T c. fmp T Hcf. fcases T T1 T2.
      - frew_in T1 (OP0 s`[↑] v`[↑] $0) Hcop. fhave E : (op0_inj_g HG s v e sx c1 Hcop Hc1). fabsurd.
        apply (IE Hes). exact (eq_sym' HG _ _ (CE1 E)).
      - frew_in T2 (OP0 s`[↑] v`[↑] $0) Hcop. fhave E : (op0_inj_g HG s v s sy c2 Hcop Hc2). exact (CE2 E). }
    fassert Htot : (∀ ($0 ∈' B`[↑] → ∃ ($0 ∈' u`[↑]`[↑] ∧ App0 f`[↑]`[↑] $1 $0))).
    { fall a. fintro Ha. unfold Pair0 in HB. pose proof (CE2 HB) as T. finst T a. fmp T Ha. fcases T T1 T2.
      - fexists sx. fsplit; [exact Hsxu|]. frew T1 (App0 f`[↑] $0 sx`[↑]). exact Hfe.
      - fexists sy. fsplit; [exact Hsyu|]. frew T2 (App0 f`[↑] $0 sy`[↑]). exact Hfs. }
    fobtain (g0_fam u f B H HBu Htot) as C HC. fdestr HC Hcov HUb. fex HUb U HU. fdestr HU HUu HUc.
    fassert HxU : (x ∈' U).
    { pose proof Hcov as T. finst T e. fmp T (CE1 (CE1 HB)). finst T sx. fmp T Hfe. fex T v Hv.
      fdestr Hv Hv1 Hv2. pose proof Hfe' as E. finst E v. fmp E Hv1.
      fassert HsxC : (sx ∈' C). { exact (elem_l HG v sx C E Hv2). }
      pose proof HUc as T'. finst T' sx. fmp T' HsxC. finst T' x. apply (IE T'). exact (CE1 (CE1 Hsx)). }
    fassert HyU : (y ∈' U).
    { pose proof Hcov as T. finst T s. fmp T (CE2 (CE1 HB)). finst T sy. fmp T Hfs. fex T v Hv.
      fdestr Hv Hv1 Hv2. pose proof Hfs' as E. finst E v. fmp E Hv1.
      fassert HsyC : (sy ∈' C). { exact (elem_l HG v sy C E Hv2). }
      pose proof HUc as T'. finst T' sy. fmp T' HsyC. finst T' y. apply (IE T'). exact (CE1 (CE1 Hsy)). }
    fobtain (pair0_ex HG HP0 x y) as q Hq. fexists q. fsplit; [|exact Hq].
    apply (g0_sub u U q H HUu). unfold Sub0. fall z. fintro Hz. unfold Pair0 in Hq. pose proof (CE2 Hq) as T.
    finst T z. fmp T Hz. fcases T T1 T2.
    + frew T1 ($0 ∈' U`[↑]). exact HxU.
    + frew T2 ($0 ∈' U`[↑]). exact HyU.
  - (* unions of families *)
    fall f. fintro Hfx. fdestr Hfx Hfx12 Hran. fdestr Hfx12 Hff Hfd.
    fassert Htot : (∀ ($0 ∈' x`[↑] → ∃ ($0 ∈' u`[↑]`[↑] ∧ App0 f`[↑]`[↑] $1 $0))).
    { fall a. fintro Ha. fobtain (dom0_app_g HG f x a Hfd Ha) as v Hv. fexists v. fsplit; [|exact Hv].
      finst Hran a v. exact (IE Hran Hv). }
    fobtain (g0_fam u f x H Hx Htot) as C HC. fdestr HC Hcov HUb. fex HUb U HU. fdestr HU HUu HUc.
    pose proof (sep_use _ 1 psi_ur (f .: var) U (HA _ (or_introl eq_refl)) fb_ur) as T.
    unfold psi_ur in T. simp_in T. fex T Wd HWd.
    fexists Wd. fsplit.
    + apply (g0_sub u U Wd H HUu). unfold Sub0. fall z. fintro Hz. finst HWd z. exact (CE1 (iff_l _ _ _ HWd Hz)).
    + fall z. fsplit.
      * fintro Hz. finst HWd z. exact (CE2 (iff_l _ _ _ HWd Hz)).
      * fintro Hz. finst HWd z. apply (iff_r _ _ _ HWd). fsplit; [|exact Hz].
        fex Hz v Hv. fdestr Hv Hv1 Hzv. fex Hv1 a Ha.
        fhave Hax : (dom0_in_g HG f x a v Hfd Ha).
        pose proof Hcov as T. finst T a. fmp T Hax. finst T v. fmp T Ha. fex T v' Hv'. fdestr Hv' Hv'1 Hv'2.
        fhave E : (fun0_app_g HG f a v v' Hff Ha Hv'1).
        pose proof HUc as T'. finst T' v'. fmp T' Hv'2. finst T' z. apply (IE T').
        exact (elem_r HG z v v' E Hzv).
Qed.

Lemma GU_of_GU0 {G} (HG : incl ZF0base G) (HA : incl Ax_gru G) : G ⊢C GU0 -> G ⊢C GU.
Proof.
  intros H. unfold GU. fall x. unfold GU0 in H. finst H x. fex H u Hu. fdestr Hu Hxu Hg.
  fexists u. fsplit; [exact Hxu | exact (gru0_gru HG HA u Hg)].
Qed.
