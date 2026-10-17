(** * SU_gu: Grothendieck universes and the axiom GU, in the library's minimal ∈/≡ signature.

    Source (vetted): Metamath set.mm, df-gru (after SGA4, Exposé I):

      ⊢ Univ = {u ∣ (Tr u ∧ ∀x ∈ u (𝒫 x ∈ u ∧ ∀y ∈ u {x, y} ∈ u ∧ ∀y ∈ (u ↑m x) ∪ ran y ∈ u))}

    Transliteration, clause by clause (primitives from ZF/stdzf_r3/zfc Z_base.v):
      Tr u                     Trans0 u                       ∀a∈u ∀b∈a. b∈u
      ∀x ∈ u ( ...             ∀x (x ∈ u → ...)
      𝒫 x ∈ u                  ∃P (P ∈ u ∧ ∀z (z ∈ P ↔ z ⊆ x))     (df-clel: A ∈ B ↔ ∃s (s = A ∧ s ∈ B))
      ∀y ∈ u {x, y} ∈ u        ∀y (y ∈ u → ∃q (q ∈ u ∧ Pair0 x y q))   (Pair0 x y q: q = {x, y})
      ∀y ∈ (u ↑m x) ...        ∀f ((Fun0 f ∧ Dom0 f x ∧ ∀a ∀v ((a,v) ∈ f → v ∈ u)) → ...)
                               (df-map/df-f/df-fn: f : x ⟶ u  ↔  Fun f ∧ dom f = x ∧ ran f ⊆ u;
                                Fun0 = relation of Kuratowski pairs, single valued; Dom0 f x = dom f = x)
      ∪ ran y ∈ u              ∃U (U ∈ u ∧ ∀z (z ∈ U ↔ ∃v ((∃a (a,v) ∈ f) ∧ z ∈ v)))

    GU := ∀x ∃u (x ∈ u ∧ Gru u)   ("every set lies in a Grothendieck universe"). *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase.
From RegCon Require MinZF.
From ZFC Require Import Z_rel Z_base.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition Gru (u : term) : form :=
  Trans0 u ∧
  ∀ ($0 ∈' u`[↑] →
     (∃ ($0 ∈' u`[↑]`[↑] ∧ ∀ ($0 ∈' $1 ↔ Sub0 $0 $2))) ∧
     (∀ ($0 ∈' u`[↑]`[↑] → ∃ ($0 ∈' u`[↑]`[↑]`[↑] ∧ Pair0 $2 $1 $0))) ∧
     ∀ ((Fun0 $0 ∧ Dom0 $0 $1 ∧ ∀ (∀ (App0 $2 $1 $0 → $0 ∈' u`[↑]`[↑]`[↑]`[↑]))) →
        ∃ ($0 ∈' u`[↑]`[↑]`[↑] ∧ ∀ ($0 ∈' $1 ↔ ∃ ((∃ App0 $4 $0 $1) ∧ $1 ∈' $0))))).
#[global] Arguments Gru : simpl never.
Lemma Gru_subst u sg : (Gru u)[sg] = Gru u`[sg].
Proof. psubst Gru. Qed.
#[global] Hint Rewrite Gru_subst : fsub.

Definition GU : form := ∀ ∃ ($1 ∈' $0 ∧ Gru $0).

Lemma GU_closed : closedf GU.
Proof. unfold GU, Gru. fbcomp. Qed.

(** ZF + GU, and ZF + Reg + GU *)
Definition T_GU (phi : form) : Prop := ZFc phi \/ phi = GU.
Definition T_GUR (phi : form) : Prop := (ZFc phi \/ phi = MinZF.ax_reg') \/ phi = GU.
