(** * Ax_rb: the bounded-fiber replacement scheme in library syntax, and what it gives.

    [ax_rb' phi] ($0 = domain element w, $1 = image z, $2.. = parameters, as in [ax_rep']):
      (forall w, exists y, forall z, phi(w,z) -> (~ z C_ y -> z in y))
        -> forall x, exists Y, forall z, (z in Y <-> exists w, w in x /\ phi(w,z)).
    It is the library form of the bounded-fiber REP of Logic.v (O'Rear's REP with the fiber
    condition "z = y" replaced by "z C_ y \/ z in y").  Here: closure facts and how to use an
    instance; Ax_rbder.v derives the library's replacement, union and power set axioms from it. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_breq.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition rbC (z y : term) : form := (¬ sub' z y) → z ∈' y.
Definition rb_hyp (phi : form) : form := ∀ ∃ ∀ (phi[$2 .: $0 .: Nat.add 3 >> var] → rbC $0 $1).

Lemma rbC_subst z y (s : nat -> term) : (rbC z y)[s] = rbC z`[s] y`[s].
Proof. unfold rbC. cbn [subst_form]. now rewrite sub'_subst. Qed.
Definition ax_rb' (phi : form) : form :=
  rb_hyp phi → ∀ ∃ ∀ ($0 ∈' $1 ↔ ∃ ($0 ∈' $3 ∧ phi[$0 .: $1 .: Nat.add 4 >> var])).

Lemma rb_closed n (phi : form) : fb (S (S n)) phi -> closedf (forall_times n (ax_rb' phi)).
Proof.
  intros H. unfold closedf. apply fb_forall_times_inv. rewrite Nat.add_0_r.
  unfold ax_rb', rb_hyp, rbC, sub'. cbn.
  repeat first [ split | (eapply fb_subst; [exact H|]; intros [|[|i]] Hi; cbn; lia) | (cbn; lia) ].
Qed.

(** proving the hypothesis of an instance, one domain element at a time *)
Lemma rbhyp_intro G (phi : form) (sg : nat -> term) :
  (forall w, G ⊢C ∃ ∀ (phi[w`[↑]`[↑] .: $0 .: (fun k => (sg k)`[↑]`[↑])] → rbC $0 $1)) ->
  G ⊢C (rb_hyp phi)[sg].
Proof.
  intros H. unfold rb_hyp. cbn [subst_form]. apply AllI_named. intros w. specialize (H w).
  cbn [subst_form]. rewrite !rbC_subst.
  match goal with |- _ ⊢C ∃ ∀ (?A → ?B) =>
    replace A with (phi[w`[↑]`[↑] .: $0 .: (fun k => (sg k)`[↑]`[↑])]) by form_subst_eq;
    replace B with (rbC $0 $1) by reflexivity end.
  exact H.
Qed.

(** using an instance whose hypothesis holds *)
Lemma rb_use G n (phi : form) (sg : nat -> term) x :
  G ⊢C forall_times n (ax_rb' phi) -> fb (S (S n)) phi -> G ⊢C (rb_hyp phi)[sg] ->
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔ ∃ ($0 ∈' x`[↑]`[↑]`[↑] ∧ phi[$0 .: $1 .: (fun k => (sg k)`[↑]`[↑]`[↑])])).
Proof.
  intros H Hfb Hh.
  apply (closed_inst _ _ _ sg (rb_closed _ _ Hfb)) in H. unfold ax_rb' in H. cbn [subst_form] in H.
  pose proof (IE H Hh) as H'. clear H.
  apply (AllE x) in H'. cbn in H'.
  replace (phi[$0 .: $1 .: (fun k => (sg k)`[↑]`[↑]`[↑])])
    with (phi[$0 .: $1 .: Nat.add 4 >> var][up (up (up (up sg)))][up (up (up x..))]) by form_subst_eq.
  exact H'.
Qed.
