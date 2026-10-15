(** Original native readback for finite raw PA238 named proofs.
    Binder freshening supplies distinct nested labels. The induction below
    relates actual numeric codes to the native encoding through constructive
    alpha and environment lemmas, without a completeness or IR premise. *)
From Coq Require Import Arith List Bool Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.logic Require Import Codes238 Compiler238 NumericSyntax238
  NumericHilbert238 NumericNamed238 NativeNamed238.
From P238.arith Require Import Compact238.
Import ListNotations FullSyntax BinSig ZFSignature.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module NativeReadback238.
Module C := Compact238.Compact238.
Module N := NumericSyntax238.NumericSyntax238.
Module H := NumericHilbert238.NumericHilbert238.
Module A := NumericNamed238.NumericNamed238.
Module T := NativeNamed238.NativeNamed238.

Definition identity_terms : N.named_env := fun v => $v.
Definition extend_identity (sigma : T.label_env) fresh : T.label_env :=
  fun i => if Nat.eqb i fresh then fresh else sigma i.

Theorem native_interpret_readback_bound k : forall phi,
  T.named_size phi < k -> T.distinct_named_binders phi ->
  forall sigma fresh, 0 < fresh ->
  (forall v, N.names_named v phi = true -> v < fresh) ->
  (forall i, sigma i < fresh) ->
  (forall v, N.names_named v phi = true -> sigma v = v) ->
  Compiler238.derivable (wim (N.encode_named phi)
    (T.native_code (N.interpret_named phi identity_terms) sigma fresh)) /\
  Compiler238.derivable (wim (T.native_code (N.interpret_named phi identity_terms) sigma fresh)
    (N.encode_named phi)).
Proof.
  induction k as [|k IH]; intros phi Hsize Hd sigma fresh Hpos Hb Hr Hi; [lia|].
  destruct phi as [|phi psi|phi|a b|a b|a phi]; cbn [T.named_size] in Hsize.
  - change (Compiler238.derivable (wim 0 (wim 1 1)) /\
      Compiler238.derivable (wim (wim 1 1) 0)); split.
    + exact (Compiler238.derives_mp (wim 1 1) _ (H.numeric_I 1) (H.numeric_K (wim 1 1) 0)).
    + exact (Compiler238.derives_mp 0 _ Compiler238.derives_truth (H.numeric_K 0 (wim 1 1))).
  - destruct Hd as [Hdphi Hdpsi].
    assert (Hbphi : forall v, N.names_named v phi = true -> v < fresh).
    { intros v Hv; apply Hb; cbn [N.names_named]; apply Bool.orb_true_iff; now left. }
    assert (Hbpsi : forall v, N.names_named v psi = true -> v < fresh).
    { intros v Hv; apply Hb; cbn [N.names_named]; apply Bool.orb_true_iff; now right. }
    assert (Hiphi : forall v, N.names_named v phi = true -> sigma v = v).
    { intros v Hv; apply Hi; cbn [N.names_named]; apply Bool.orb_true_iff; now left. }
    assert (Hipsi : forall v, N.names_named v psi = true -> sigma v = v).
    { intros v Hv; apply Hi; cbn [N.names_named]; apply Bool.orb_true_iff; now right. }
    destruct (IH phi ltac:(lia) Hdphi sigma fresh Hpos Hbphi Hr Hiphi) as [Hp Hp'];
      destruct (IH psi ltac:(lia) Hdpsi sigma fresh Hpos Hbpsi Hr Hipsi) as [Hq Hq'].
    cbn [N.encode_named N.interpret_named T.native_code T.native_named]; split;
      apply T.numeric_implication_congruence; assumption.
  - destruct (IH phi ltac:(lia) Hd sigma fresh Hpos Hb Hr Hi) as [Hp Hp'].
    change (Compiler238.derivable
      (wim (wn (N.encode_named phi))
        (wn (T.native_code (N.interpret_named phi identity_terms) sigma fresh))) /\
      Compiler238.derivable
      (wim (wn (T.native_code (N.interpret_named phi identity_terms) sigma fresh))
        (wn (N.encode_named phi)))).
    split; apply H.numeric_contrapose; assumption.
  - assert (Ha : sigma a = a).
    { apply Hi; cbn [N.names_named]; apply Bool.orb_true_iff; left; apply Nat.eqb_refl. }
    assert (Hb' : sigma b = b).
    { apply Hi; cbn [N.names_named]; apply Bool.orb_true_iff; right; apply Nat.eqb_refl. }
    change (Compiler238.derivable (wim (wel a b) (wel (sigma a) (sigma b))) /\
      Compiler238.derivable (wim (wel (sigma a) (sigma b)) (wel a b))).
    rewrite Ha, Hb'; split; apply H.numeric_I.
  - assert (Ha : sigma a = a).
    { apply Hi; cbn [N.names_named]; apply Bool.orb_true_iff; left; apply Nat.eqb_refl. }
    assert (Hb' : sigma b = b).
    { apply Hi; cbn [N.names_named]; apply Bool.orb_true_iff; right; apply Nat.eqb_refl. }
    change (Compiler238.derivable (wim (weq a b) (weq (sigma a) (sigma b))) /\
      Compiler238.derivable (wim (weq (sigma a) (sigma b)) (weq a b))).
    rewrite Ha, Hb'; split; apply H.numeric_I.
  - destruct Hd as [Hinner Hdphi].
    assert (Hal : a < fresh).
    { apply Hb; cbn [N.names_named]; now rewrite Nat.eqb_refl. }
    assert (Hbphi : forall v, N.names_named v phi = true -> v < fresh).
    { intros v Hv; apply Hb; cbn [N.names_named]; apply Bool.orb_true_iff; now right. }
    assert (Hfresh : N.names_named fresh phi = false).
    { destruct (N.names_named fresh phi) eqn:E; [specialize (Hbphi fresh E); lia|reflexivity]. }
    set (psi := A.replace_named a fresh phi).
    set (tau := extend_identity sigma fresh).
    assert (Hsizepsi : T.named_size psi < k).
    { unfold psi; rewrite T.replace_named_size; lia. }
    assert (Hdpsi : T.distinct_named_binders psi).
    { unfold psi; apply T.replace_named_distinct; exact Hdphi. }
    assert (Hbps : forall v, N.names_named v psi = true -> v < S fresh).
    { intros v Hv; unfold psi in Hv; destruct (T.replace_named_name_source a fresh phi v Hv) as [->|Horiginal];
        [lia|specialize (Hbphi v Horiginal); lia]. }
    assert (Hrt : forall i, tau i < S fresh).
    { intro i; unfold tau, extend_identity; destruct (Nat.eqb i fresh); [lia|specialize (Hr i); lia]. }
    assert (Hit : forall v, N.names_named v psi = true -> tau v = v).
    { intros v Hv; unfold psi in Hv; destruct (T.replace_named_name_source a fresh phi v Hv) as [->|Horiginal].
      - unfold tau, extend_identity; now rewrite Nat.eqb_refl.
      - assert (Hvf : v <> fresh) by (specialize (Hbphi v Horiginal); lia).
        unfold tau, extend_identity; rewrite (proj2 (Nat.eqb_neq v fresh) Hvf).
        apply Hi; cbn [N.names_named]; apply Bool.orb_true_iff; now right. }
    destruct (IH psi Hsizepsi Hdpsi tau (S fresh) ltac:(lia) Hbps Hrt Hit) as [Hp Hp'].
    assert (Ebody :
      T.native_named (N.interpret_named phi (N.bind_env identity_terms a))
        (T.push_label sigma fresh) (S fresh) =
      T.native_named (N.interpret_named psi identity_terms) tau (S fresh)).
    { unfold psi; rewrite (T.interpret_named_replace a fresh phi Hinner (A.named_names_binders fresh phi Hfresh)).
      apply T.native_interpret_environment; intros v Hv.
      unfold N.bind_env, N.update_env, identity_terms.
      destruct (Nat.eqb v a) eqn:E.
      - cbn [T.term_label T.push_label]; unfold tau, extend_identity; now rewrite Nat.eqb_refl.
      - cbn [T.term_label T.push_label].
        assert (Hvn : N.names_named v phi = true) by (apply N.free_named_in_names; exact Hv).
        assert (Hvf : v <> fresh) by (specialize (Hbphi v Hvn); lia).
        unfold tau, extend_identity; now rewrite (proj2 (Nat.eqb_neq v fresh) Hvf). }
    destruct (A.named_universal_alpha a fresh phi ltac:(lia) Hinner Hfresh) as [Ha Ha'].
    change (Compiler238.derivable
      (wim (wal a (N.encode_named phi))
        (wal fresh (N.encode_named
          (T.native_named (N.interpret_named phi (N.bind_env identity_terms a))
            (T.push_label sigma fresh) (S fresh))))) /\
      Compiler238.derivable
      (wim (wal fresh (N.encode_named
        (T.native_named (N.interpret_named phi (N.bind_env identity_terms a))
          (T.push_label sigma fresh) (S fresh)))) (wal a (N.encode_named phi)))).
    rewrite Ebody; split.
    + apply H.numeric_implication_compose with (b := wal fresh (N.encode_named psi));
        [exact Ha|apply T.numeric_all_congruence; exact Hp].
    + apply H.numeric_implication_compose with (b := wal fresh (N.encode_named psi));
        [apply T.numeric_all_congruence; exact Hp'|exact Ha'].
Qed.

Theorem native_interpret_readback phi sigma fresh :
  T.distinct_named_binders phi -> 0 < fresh ->
  (forall v, N.names_named v phi = true -> v < fresh) ->
  (forall i, sigma i < fresh) ->
  (forall v, N.names_named v phi = true -> sigma v = v) ->
  Compiler238.derivable (wim (N.encode_named phi)
    (T.native_code (N.interpret_named phi identity_terms) sigma fresh)) /\
  Compiler238.derivable (wim (T.native_code (N.interpret_named phi identity_terms) sigma fresh)
    (N.encode_named phi)).
Proof.
  intros Hd Hpos Hb Hr Hi.
  exact (@native_interpret_readback_bound (S (T.named_size phi)) phi
    ltac:(lia) Hd sigma fresh Hpos Hb Hr Hi).
Qed.

Print Assumptions native_interpret_readback_bound.
Print Assumptions native_interpret_readback.
End NativeReadback238.
