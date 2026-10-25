(** * PA_Sound: the reference calculus with the extra axiom NG (= Wn GCw) is sound for PAeq + ¬GC_form.

    GCw is Goldbach's sentence as a named wff (= tr of Spec.GC_form); its de Bruijn image is the
    {→,⊥,∀} translation of Spec.GC_form ([dB_GCw], by computation).  Main results:
      pprov_NG_sound :  pprov {NG} a  ->  PAeq ⋄ ¬GC_form proves dB rho a  (one list for all rho)
      pprov_NG_GC    :  pprov {NG} (0 ≠ 0)  ->  PAeq ⊢TC GC_form *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import PA Syntax.Theories.
From Undecidability.FOL.Arithmetics Require DeductionFacts.
From PAGB Require Import Spec PALogic PA_dB PA_Frag PA_F PA_tr.
Import ListNotations.
Unset Implicit Arguments.

Local Notation "A ⊢C phi" := (@prv _ _ falsity_on class A phi) (at level 55).

(** ** Goldbach's sentence as a named wff: the translation [tr] (PA_tr.v) of Spec.GC_form.
    It is closed; binder names are 2 (innermost) .. 10 (n). *)
Definition GCw : wff := tr (fun _ => TV 1) GC_form.

Definition NGw : wff := Wn GCw.

Lemma dB_GCw rho : dB rho GCw = to_frag GC_form.
Proof. reflexivity. Qed.

(** ** Soundness with NG *)
Definition PA_NG : form -> Prop := extend PAeq NG_form.

Lemma PA_NG_PA psi : PAeq psi -> PA_NG psi.
Proof. intro H. now left. Qed.

Lemma Fvalid_NGw : Fvalid PA_NG NGw.
Proof.
  exists [NG_form]. split; [intros psi [<-|[]]; now right|].
  intro rho. unfold NGw. cbn [dB]. rewrite dB_GCw. apply II.
  eapply IE; [apply Ctx; right; now left|]. apply to_frag_r. apply Ctx. now left.
Qed.

Theorem pprov_NG_sound a : pprov (eq NGw) a ->
  exists A, (forall psi, In psi A -> PA_NG psi) /\ forall rho, A ⊢C dB rho a.
Proof.
  intro H. apply (pprov_Fvalid PA_NG PA_NG_PA (eq NGw)) in H; [exact H|].
  intros b <-. exact Fvalid_NGw.
Qed.

Definition Fw : wff := Wn (Weq TZ TZ).

Theorem pprov_NG_GC : pprov (eq NGw) Fw -> PA_proves_GC.
Proof.
  intro H. apply PA_GC_refutation. apply pprov_NG_sound in H as [A [HA H]].
  exists (A ++ FAeq). split.
  - intros psi [Hp|Hp]%in_app_iff; [now apply HA | now left; apply PAeq_FA].
  - specialize (H var). cbn in H.
    eapply IE; [eapply Weak; [exact H | apply incl_appl, incl_refl]|].
    apply (DeductionFacts.reflexivity class). apply incl_appr, incl_refl.
Qed.

Print Assumptions pprov_NG_GC.
