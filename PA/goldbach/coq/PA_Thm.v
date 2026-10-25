(** * PA_Thm: the machine's calculus at the level of codes (design A, fix (a)), and its soundness:
      thm n  ->  pprov {NGw} (D n),   hence   thm F -> PAeq ⊢TC GC_form.

    [thm]: n is derivable from the AX roots and the gated bundle by MP and GEN, with the truth code
    0 as an axiom (stack zeros, failed MP and a closed gate produce 0).  The Q rows are allowed
    with arbitrary labels (the machine's labels are instances).  Bundle:
      IND(a,c,D c) /\ (T(a) = T(b) -> A. v_c T(a) = T(b)),  emitted iff  c ∉ vars T(a) ∪ vars T(b). *)
From Coq Require Import Arith Lia List Bool.
From PAGB Require Import Spec PALogic PA_dB PA_LProp PA_LMeta PA_tr PA_H PA_Codes PA_Rows PA_Sound PA_Comp.
Import ListNotations.
Unset Implicit Arguments.

Definition r_VAC (a b c : nat) : fa := AImp (AEq (AT a) (AT b)) (AAll c (AEq (AT a) (AT b))).
Definition r_bundle (a b c : nat) : fa := AAnd (r_IND a c) (r_VAC a b c).
Definition gate (a b c : nat) : bool := negb (occT c a || occT c b).
Definition bundle (a b c : nat) : nat := if gate a b c then cd (r_bundle a b c) else 0.

Inductive thm : nat -> Prop :=
  | T_true : thm 0
  | T_mp t b : thm t -> thm (wim t b) -> thm b
  | T_gen a h : thm h -> thm (wal a h)
  | T_L a b c u : thm (cd (r_L a b c u))
  | T_QI a b c : thm (cd (r_QI a b c))
  | T_COMM a b c : thm (cd (r_COMM a b c))
  | T_B6c a b : thm (cd (r_B6c a b))
  | T_EUC a b c : thm (cd (r_EUC a b c))
  | T_CS a b : thm (cd (r_CS a b))
  | T_CA1 a b c : thm (cd (r_CA1 a b c))
  | T_CA2 a b c : thm (cd (r_CA2 a b c))
  | T_CM1 a b c : thm (cd (r_CM1 a b c))
  | T_CM2 a b c : thm (cd (r_CM2 a b c))
  | T_R1 a b : thm (cd (r_R1 a b))
  | T_EX c : thm (cd (r_EX c))
  | T_QZS x : thm (cd (r_QZS x))
  | T_QSI x y : thm (cd (r_QSI x y))
  | T_QA0 x : thm (cd (r_QA0 x))
  | T_QAS x y : thm (cd (r_QAS x y))
  | T_QM0 x : thm (cd (r_QM0 x))
  | T_QMS x y : thm (cd (r_QMS x y))
  | T_NG : thm (cd r_NG)
  | T_bundle a b c : thm (bundle a b c).

(** ** Soundness *)
Section Sound.
Variable X : wff -> Prop.
Hypothesis HNG : X NGw.
Local Notation lprov := (pprov X).
Let LDET := DET X.

Ltac dh := apply dhyp; simpl; tauto.
Ltac dt H := apply dthm; exact H.
Ltac mp a := apply (dmp _ _ a).

Lemma s_IND_any a c : lprov (dw (r_IND a c)).
Proof.
  destruct (Nat.eq_dec c a) as [<-|H]; [|now apply s_IND].
  (* IND(c,c,φ) with c ∉ φ: the base case at 0 gives φ, then vacuity *)
  cbn [dw r_IND dwt]. set (p := D c).
  assert (Hc : occ c p = false).
  { destruct (occ c p) eqn:E; [|reflexivity]. apply D_fresh in E. lia. }
  assert (S0 : lprov (Wim (Wal c (Wim (Weq (TV c) TZ) p)) (Wim (Weq TZ TZ) p))).
  { pose proof (lspec X c TZ (Wim (Weq (TV c) TZ) p) eq_refl) as H.
    cbn [sb sbt] in H. rewrite Nat.eqb_refl in H. rewrite (sb_noocc c TZ p Hc) in H.
    apply H; [cbn; now apply occ_bnd | intros v Hv; discriminate]. }
  apply der_lprov, ded, ded.
  mp p; [dt (lvac X c p Hc)|]. mp (Weq TZ TZ); [| dt (leq_refl X TZ)].
  mp (Wal c (Wim (Weq (TV c) TZ) p)); [dt S0 | dh].
Qed.

Lemma s_VAC a b c : gate a b c = true -> lprov (dw (r_VAC a b c)).
Proof.
  unfold gate. intro G. apply negb_true_iff, orb_false_iff in G as [Ga Gb].
  rewrite !occT_spec in Ga, Gb. cbn [dw r_VAC dwt]. now apply B6a.
Qed.

Lemma s_and a b : lprov (dw a) -> lprov (dw b) -> lprov (dw (AAnd a b)).
Proof. intros Ha Hb. cbn [dw AAnd]. exact (LDET _ _ (LDET _ _ (lpc_andi X _ _) Ha) Hb). Qed.

Theorem thm_sound n : thm n -> lprov (D n).
Proof.
  induction 1.
  - exact (truth_prov X).
  - destruct (Nat.eq_dec t 0) as [->|Ht]; [destruct (Nat.eq_dec b 0) as [->|Hb]|].
    + exact (truth_prov X).
    + rewrite D_wim in IHthm2 by lia. exact (LDET _ _ IHthm2 IHthm1).
    + rewrite D_wim in IHthm2 by lia. exact (LDET _ _ IHthm2 IHthm1).
  - now apply s_GEN.
  - apply prov_cd, s_L.
  - apply prov_cd, s_QI.
  - apply prov_cd, s_COMM.
  - apply prov_cd, s_B6c.
  - apply prov_cd, s_EUC.
  - apply prov_cd, s_CS.
  - apply prov_cd, s_CA1.
  - apply prov_cd, s_CA2.
  - apply prov_cd, s_CM1.
  - apply prov_cd, s_CM2.
  - apply prov_cd, s_R1.
  - apply prov_cd, s_EX.
  - apply prov_cd, s_QZS.
  - apply prov_cd, s_QSI.
  - apply prov_cd, s_QA0.
  - apply prov_cd, s_QAS.
  - apply prov_cd, s_QM0.
  - apply prov_cd, s_QMS.
  - apply prov_cd, s_NG, HNG.
  - unfold bundle. destruct (gate a b c) eqn:G; [|exact (truth_prov X)].
    apply prov_cd, s_and; [apply s_IND_any | now apply s_VAC].
Qed.
End Sound.

Theorem thm_F_GC : thm F -> PA_proves_GC.
Proof.
  intro H. apply pprov_NG_iff_PA_GC. apply (thm_sound (eq NGw) eq_refl) in H. rewrite D_F in H.
  (* S0 = 0 and its refutation give anything *)
  exact (DET _ _ _ (DET _ _ _ (B3 _ FF Fw) H) (lnot_FF _)).
Qed.

Print Assumptions thm_F_GC.
