(** * AC_iso: relativization to sets along an ∈-isomorphism, and absoluteness for transitive sets.

    [IsoF X P M]: P maps X onto M (total on X, onto M), preserving and reflecting ∈ and ≡.
    [iso_relS]: relS X φ[σ] ↔ relS M φ[σ'] when P maps σ k to σ' k (induction on φ).
    [D0_absS], [Sg_upS]: the relS versions of Z_rel.D0_abs and Z_rel.Sg_up for a transitive set Y. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From ZFC Require Import Z_rel Z_base Z_prim.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition IsoF (X P M : term) : form :=
  (∀ ($0 ∈' X`[↑] → ∃ (App0 P`[↑]`[↑] $1 $0 ∧ $0 ∈' M`[↑]`[↑]))) ∧
  (∀ ($0 ∈' M`[↑] → ∃ ($0 ∈' X`[↑]`[↑] ∧ App0 P`[↑]`[↑] $0 $1))) ∧
  (∀ (∀ (∀ (∀ ($3 ∈' X`[↑]`[↑]`[↑]`[↑] → $2 ∈' X`[↑]`[↑]`[↑]`[↑] →
      App0 P`[↑]`[↑]`[↑]`[↑] $3 $1 → App0 P`[↑]`[↑]`[↑]`[↑] $2 $0 →
      ($3 ∈' $2 ↔ $1 ∈' $0) ∧ ($3 ≡' $2 ↔ $1 ≡' $0)))))).
#[global] Arguments IsoF : simpl never.
Lemma IsoF_subst X P M sg : (IsoF X P M)[sg] = IsoF X`[sg] P`[sg] M`[sg].
Proof. psubst IsoF. Qed.
#[global] Hint Rewrite IsoF_subst : fsub.


#[local] Hint Rewrite @relS_subst : fsub.

Lemma trans0_useS {G} x y z : G ⊢C Trans0 x -> G ⊢C y ∈' x -> G ⊢C z ∈' y -> G ⊢C z ∈' x.
Proof.
  intros HT Hy Hz. unfold Trans0 in HT. finst HT y. fmp HT Hy. finst HT z. exact (IE HT Hz).
Qed.

Lemma HsS_cons G (Y : term) sg z : (forall k, G ⊢C sg k ∈' Y) -> G ⊢C z ∈' Y -> forall k, G ⊢C (z .: sg) k ∈' Y.
Proof. intros Hs Hz [|k]; cbn; [exact Hz | apply Hs]. Qed.

Lemma iso_relS (phi : form) : forall G (X P M : term) (sg sg' : nat -> term), incl ZF0base G ->
  G ⊢C IsoF X P M -> (forall k, G ⊢C sg k ∈' X) -> (forall k, G ⊢C App0 P (sg k) (sg' k)) ->
  G ⊢C relS X (phi[sg]) ↔ relS M (phi[sg']).
Proof.
  induction phi as [| Pr v | op a IHa c IHc | q a IHa] using form_ind_falsity;
    intros G X P M sg sg' HG HI Hs Hs'.
  - cbn. apply iff_refl'.
  - unfold IsoF in HI. fdestr HI HI12 HI3.
    destruct Pr; cbn in v |- *; rewrite (vec2 v); cbn;
      destruct (Vector.hd v) as [n|[]]; destruct (Vector.hd (Vector.tl v)) as [m|[]]; cbn.
    + finst HI3 (sg n) (sg m) (sg' n) (sg' m). fmp HI3 (Hs n). fmp HI3 (Hs m). fmp HI3 (Hs' n).
      fmp HI3 (Hs' m). exact (CE1 HI3).
    + finst HI3 (sg n) (sg m) (sg' n) (sg' m). fmp HI3 (Hs n). fmp HI3 (Hs m). fmp HI3 (Hs' n).
      fmp HI3 (Hs' m). exact (CE2 HI3).
  - cbn. apply iff_bin; [eapply IHa|eapply IHc]; eassumption.
  - assert (HI' := HI). unfold IsoF in HI'. fdestr HI' HI12 HI3. fdestr HI12 HA HB.
    destruct q; cbn; fsplit.
    + fintro H. fall m. fintro Hm. finst HB m. fmp HB Hm. fex HB z Hz. fdestr Hz Hz1 Hz2.
      finst H z. fmp H Hz1.
      refine (iff_l _ _ _ (IHa _ X P M (z .: sg) (m .: sg') _ HI _ _) H); [assumption| |].
      * intros [|k]; cbn; [exact Hz1|apply Hs].
      * intros [|k]; cbn; [exact Hz2|apply Hs'].
    + fintro H. fall z. fintro Hz. finst HA z. fmp HA Hz. fex HA m Hm. fdestr Hm Hm1 Hm2.
      finst H m. fmp H Hm2.
      refine (iff_r _ _ _ (IHa _ X P M (z .: sg) (m .: sg') _ HI _ _) H); [assumption| |].
      * intros [|k]; cbn; [exact Hz|apply Hs].
      * intros [|k]; cbn; [exact Hm1|apply Hs'].
    + fintro H. fex H z Hz. fdestr Hz Hz1 Hz2. finst HA z. fmp HA Hz1. fex HA m Hm. fdestr Hm Hm1 Hm2.
      fexists m. fsplit; [exact Hm2|].
      refine (iff_l _ _ _ (IHa _ X P M (z .: sg) (m .: sg') _ HI _ _) Hz2); [assumption| |].
      * intros [|k]; cbn; [exact Hz1|apply Hs].
      * intros [|k]; cbn; [exact Hm1|apply Hs'].
    + fintro H. fex H m Hm. fdestr Hm Hm1 Hm2. finst HB m. fmp HB Hm1. fex HB z Hz. fdestr Hz Hz1 Hz2.
      fexists z. fsplit; [exact Hz1|].
      refine (iff_r _ _ _ (IHa _ X P M (z .: sg) (m .: sg') _ HI _ _) Hm2); [assumption| |].
      * intros [|k]; cbn; [exact Hz1|apply Hs].
      * intros [|k]; cbn; [exact Hz2|apply Hs'].
Qed.

Theorem D0_absS (phi : form) : D0 phi -> forall G (Y : term) (sg : nat -> term), incl ZF0base G ->
  G ⊢C Trans0 Y -> (forall k, G ⊢C sg k ∈' Y) -> G ⊢C relS Y (phi[sg]) ↔ phi[sg].
Proof.
  induction 1 as [| Pr v | b phi psi _ IH1 _ IH2 | k phi _ IH | k phi _ IH]; intros G Y sg HG HT Hs; cbn.
  - apply iff_refl'.
  - apply iff_refl'.
  - apply iff_bin; [apply IH1|apply IH2]; assumption.
  - unfold funcomp. fsplit.
    + fintro H. fall z. fintro Hz. finst H z.
      fhave HzY : (trans0_useS Y (sg k) z HT (Hs k) Hz). fmp H HzY. fmp H Hz.
      exact (iff_l _ _ _ (IH _ Y (z .: sg) HG HT (HsS_cons _ _ _ _ Hs HzY)) H).
    + fintro H. fall z. fintro HzY. fintro Hz. finst H z. fmp H Hz.
      exact (iff_r _ _ _ (IH _ Y (z .: sg) HG HT (HsS_cons _ _ _ _ Hs HzY)) H).
  - unfold funcomp. fsplit.
    + fintro H. fex H z Hz. fdestr Hz HzY Hz0. fdestr Hz0 Hz1 Hz2.
      fexists z. fsplit; [exact Hz1|].
      exact (iff_l _ _ _ (IH _ Y (z .: sg) HG HT (HsS_cons _ _ _ _ Hs HzY)) Hz2).
    + fintro H. fex H z Hz. fdestr Hz Hz1 Hz2.
      fhave HzY : (trans0_useS Y (sg k) z HT (Hs k) Hz1).
      fexists z. fsplit; [exact HzY|]. fsplit; [exact Hz1|].
      exact (iff_r _ _ _ (IH _ Y (z .: sg) HG HT (HsS_cons _ _ _ _ Hs HzY)) Hz2).
Qed.

Theorem Sg_upS (phi : form) : Sg phi -> forall G (Y : term) (sg : nat -> term), incl ZF0base G ->
  G ⊢C Trans0 Y -> (forall k, G ⊢C sg k ∈' Y) -> G ⊢C relS Y (phi[sg]) -> G ⊢C phi[sg].
Proof.
  induction 1 as [phi H0 | phi psi _ IH1 _ IH2 | phi psi _ IH1 _ IH2 | k phi _ IH | phi psi H0 _ IH | phi _ IH];
    intros G Y sg HG HT Hs H; cbn in H |- *.
  - exact (iff_l _ _ _ (D0_absS phi H0 G Y sg HG HT Hs) H).
  - fsplit; [apply (IH1 _ Y)|apply (IH2 _ Y)]; auto; [exact (CE1 H)|exact (CE2 H)].
  - fcases H H1 H2; [fleft; now apply (IH1 _ Y)|fright; now apply (IH2 _ Y)].
  - unfold funcomp in *.
    fall z. fintro Hz. finst H z.
    fhave HzY : (trans0_useS Y (sg k) z HT (Hs k) Hz). fmp H HzY. fmp H Hz.
    exact (IH _ Y (z .: sg) HG HT (HsS_cons _ _ _ _ Hs HzY) H).
  - fintro Hphi. apply (IH _ Y); [exact HG|exact HT|exact Hs|]. fapply H.
    exact (iff_r _ _ _ (D0_absS phi H0 _ Y sg HG HT Hs) Hphi).
  - fex H z Hz. fdestr Hz HzY Hz2.
    fexists z. exact (IH _ Y (z .: sg) HG HT (HsS_cons _ _ _ _ Hs HzY) Hz2).
Qed.
