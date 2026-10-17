(** * SU_def: the theory SU of the ZF + GU machine (interface with m254tg-machine).

    UG'_φ (φ: $0 = input a, $1 = output y, $2 = f (bound inside, after w), $(k+3) = parameter k):

      ∀p ∃w [ ( p∈w ∧ ∀x∈w ( x⊆w ∧ ∃W∈w ∀z (z⊆x → z∈W) ) )
            ∧ ∀f ∀B ( B∈w → ∃C ( ( ∀a∈B ∀y (φ(a,y,f) → ∃y' (φ(a,y',f) ∧ y'∈C))
                                 ∧ ∀y∈C ∃x φ(x,y,f) )
                               ∧ ( ∀a∈B ∃y (y∈w ∧ φ(a,y,f)) → ∃U (U∈w ∧ ∀y∈C ∀z∈y z∈U) ) ) ) ]

      SU0  = equality axioms + every closed [forall_times n (ug φ)]
      SUIR = SU0 + IR                                  (IR: ∀x ¬ x∈x)

    Conjunctions are parenthesized explicitly (the library's ∧ is left-associative). *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From ZFC Require Z_axL.
From M254S Require Import S_def.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** binders: ∀p ∃w | ∀f ∀B | ∃C | cov: ∀a ∀y ∃y' | nx: ∀y ∃x | tot: ∀a ∃y | bound: ∃U ∀y ∀z *)
Definition ug (phi : form) : form :=
  ∀ ∃ (($1 ∈' $0 ∧
        ∀ ($0 ∈' $1 → (∀ ($0 ∈' $1 → $0 ∈' $2)) ∧
                        ∃ ($0 ∈' $2 ∧ ∀ ((∀ ($0 ∈' $1 → $0 ∈' $3)) → $0 ∈' $1)))) ∧
       ∀ ∀ ($0 ∈' $2 → ∃ (
          ((∀ ($0 ∈' $2 → ∀ (phi[$1 .: $0 .: $4 .: (fun k => $(7 + k))] →
                              ∃ (phi[$2 .: $0 .: $5 .: (fun k => $(8 + k))] ∧ $0 ∈' $3)))) ∧
           (∀ ($0 ∈' $1 → ∃ phi[$0 .: $1 .: $4 .: (fun k => $(7 + k))]))) ∧
          ((∀ ($0 ∈' $2 → ∃ ($0 ∈' $5 ∧ phi[$1 .: $0 .: $4 .: (fun k => $(7 + k))]))) →
           ∃ ($0 ∈' $4 ∧ ∀ ($0 ∈' $2 → ∀ ($0 ∈' $1 → $0 ∈' $2))))))).

Definition SUbase : list form := [ax_refl'; ax_sym'; ax_trans'; ax_eq_elem'].

Inductive SU0 : form -> Prop :=
  | SU0_base phi : In phi SUbase -> SU0 phi
  | SU0_ug phi n : closedf (forall_times n (ug phi)) -> SU0 (forall_times n (ug phi)).

Definition SUIR (phi : form) : Prop := SU0 phi \/ phi = ax_ir.

Lemma SUbase_closed psi : In psi SUbase -> closedf psi.
Proof. intros H. repeat (destruct H as [<-|H]; [cbn; lia|]). destruct H. Qed.

Lemma SU0_closed psi : SU0 psi -> closedf psi.
Proof. intros [phi H | phi n H]; [now apply SUbase_closed | exact H]. Qed.

Lemma SUIR_closed psi : SUIR psi -> closedf psi.
Proof. intros [H | ->]; [now apply SU0_closed | apply ax_ir_closed]. Qed.

Lemma ug_closed n (phi : form) : fb (S (S (S n))) phi -> closedf (forall_times n (ug phi)).
Proof.
  intros H. unfold closedf. apply fb_forall_times_inv. rewrite Nat.add_0_r. cbn.
  repeat split; try lia; (eapply fb_subst; [exact H|]); intros [|[|[|i]]] Hi; cbn; lia.
Qed.

Lemma fb_ug_inv n phi : closedf (forall_times n (ug phi)) -> fb (S (S (S n))) phi.
Proof.
  intros H. apply fb_forall_times in H. rewrite Nat.add_0_r in H. unfold ug in H. cbn in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : fb _ (phi[$0 .: $1 .: $4 .: _]) |- _ => eapply Z_axL.fb_ren_inv; [exact H|] end.
  intros [|[|[|i]]] Hi; cbn in Hi |- *; lia.
Qed.

Lemma SUbase_EqAx : SUbase = EqAx.
Proof. reflexivity. Qed.
