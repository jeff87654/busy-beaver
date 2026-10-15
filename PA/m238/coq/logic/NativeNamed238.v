(** Original native-to-named syntax for the finite PA238 forward proof.
    Terms have the empty function signature, so environments assign names
    to indices. Native bottom is the relative proof-calculus code 1. The
    native decoder and the separate compact IR soundness direction are not
    used here. Quantifiers allocate a fresh label and raise the allocation
    bound for their bodies. *)
From Coq Require Import Arith Bool List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
From P238.logic Require Import Codes238 Compiler238 NumericSyntax238
  NumericHilbert238 NumericNamed238.
From P238.arith Require Import Compact238.
Import ListNotations FullSyntax BinSig ZFSignature.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module NativeNamed238.
Module C := Compact238.Compact238.
Module N := NumericSyntax238.NumericSyntax238.
Module H := NumericHilbert238.NumericHilbert238.
Module A := NumericNamed238.NumericNamed238.

Definition label_env := nat -> nat.
Definition push_label (rho : label_env) (a : nat) : label_env :=
  fun i => match i with 0 => a | S j => rho j end.
Definition term_label (rho : label_env) (t : C.set_term) : nat :=
  match t with
  | var i => rho i
  | func f _ => match f with end
  end.

Fixpoint native_named {ff : falsity_flag}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) (rho : label_env) (fresh : nat) : N.named_formula :=
  match phi with
  | falsity => N.NMem 0 0
  | atom p ts =>
      match p return Vector.t C.set_term (ar_preds p) -> N.named_formula with
      | elem => fun ts => N.NMem (term_label rho (Vector.hd (Vector.tl ts)))
                                (term_label rho (Vector.hd ts))
      | equal => fun ts => N.NEq (term_label rho (Vector.hd ts))
                                (term_label rho (Vector.hd (Vector.tl ts)))
      end ts
  | bin op phi psi =>
      let p := native_named phi rho fresh in
      let q := native_named psi rho fresh in
      match op with
      | Impl => N.NImp p q
      | Conj => N.NNot (N.NImp p (N.NNot q))
      | Disj => N.NImp (N.NNot p) q
      end
  | quant op phi =>
      let p := native_named phi (push_label rho fresh) (S fresh) in
      match op with
      | All => N.NAll fresh p
      | Ex => N.NNot (N.NAll fresh (N.NNot p))
      end
  end.

Definition native_code (phi : C.set_form) rho fresh := N.encode_named (native_named phi rho fresh).

Lemma term_label_ext rho tau t : (forall i, rho i = tau i) ->
  term_label rho t = term_label tau t.
Proof. destruct t as [i|[]]; intro H; apply H. Qed.

Lemma native_named_ext (phi : C.set_form) : forall rho tau fresh,
  (forall i, rho i = tau i) -> native_named phi rho fresh = native_named phi tau fresh.
Proof.
  induction phi as [|p ts|op phi IHphi psi IHpsi|op phi IH] using form_ind_falsity; intros rho tau fresh He.
  - reflexivity.
  - destruct p; cbn [native_named]; f_equal; apply term_label_ext; exact He.
  - destruct op; cbn [native_named]; rewrite (IHphi rho tau fresh He), (IHpsi rho tau fresh He);
      reflexivity.
  - assert (Hp : forall i, push_label rho fresh i = push_label tau fresh i).
    { intros [|i]; cbn [push_label]; [reflexivity|apply He]. }
    destruct op; cbn [native_named]; rewrite (IH _ _ _ Hp); reflexivity.
Qed.

Lemma native_named_binders_below (phi : C.set_form) : forall rho fresh v,
  v < fresh -> N.binders_named v (native_named phi rho fresh) = false.
Proof.
  induction phi as [|p ts|op phi IHphi psi IHpsi|op phi IH] using form_ind_falsity; intros rho fresh v Hlt.
  - reflexivity.
  - destruct p; reflexivity.
  - destruct op; cbn [native_named N.binders_named];
      rewrite (IHphi rho fresh v Hlt), (IHpsi rho fresh v Hlt); reflexivity.
  - assert (Hv : Nat.eqb v fresh = false) by (apply Nat.eqb_neq; lia).
    destruct op; cbn [native_named N.binders_named];
      rewrite Hv, (IH (push_label rho fresh) (S fresh) v ltac:(lia)); reflexivity.
Qed.

Lemma term_label_avoids rho v t : (forall i, rho i <> v) ->
  Nat.eqb v (term_label rho t) = false.
Proof.
  destruct t as [i|[]]; intro H; apply Nat.eqb_neq; change (v <> rho i).
  intro E; apply (H i); symmetry; exact E.
Qed.

Lemma native_named_names_below (phi : C.set_form) : forall rho fresh v,
  0 < v -> v < fresh -> (forall i, rho i <> v) ->
  N.names_named v (native_named phi rho fresh) = false.
Proof.
  induction phi as [|p ts|op phi IHphi psi IHpsi|op phi IH] using form_ind_falsity; intros rho fresh v Hpos Hlt Hr.
  - cbn [native_named N.names_named]; rewrite (proj2 (Nat.eqb_neq v 0) ltac:(lia)); reflexivity.
  - destruct p; cbn [native_named N.names_named]; rewrite !term_label_avoids by exact Hr;
      reflexivity.
  - destruct op; cbn [native_named N.names_named];
      rewrite (IHphi rho fresh v Hpos Hlt Hr), (IHpsi rho fresh v Hpos Hlt Hr); reflexivity.
  - assert (Hv : Nat.eqb v fresh = false) by (apply Nat.eqb_neq; lia).
    assert (Hp : forall i, push_label rho fresh i <> v).
    { intros [|i]; cbn [push_label]; [lia|apply Hr]. }
    destruct op; cbn [native_named N.names_named];
      rewrite Hv, (IH (push_label rho fresh) (S fresh) v Hpos ltac:(lia) Hp); reflexivity.
Qed.

Lemma term_label_substitution rho sigma t :
  term_label rho (t`[sigma]) = term_label (fun i => term_label rho (sigma i)) t.
Proof. destruct t as [i|[]]; reflexivity. Qed.

Lemma native_vector2_eta (ts : Vector.t C.set_term 2) :
  ts = Vector.cons C.set_term (Vector.hd ts) 1
    (Vector.cons C.set_term (Vector.hd (Vector.tl ts)) 0 (Vector.nil C.set_term)).
Proof.
  rewrite (Vector.eta ts) at 1; f_equal; apply destruct_vector_single.
Qed.

Lemma native_named_substitution (phi : C.set_form) : forall rho fresh sigma,
  native_named (phi[sigma]) rho fresh =
  native_named phi (fun i => term_label rho (sigma i)) fresh.
Proof.
  induction phi as [|p ts|op phi IHphi psi IHpsi|op phi IH] using form_ind_falsity; intros rho fresh sigma.
  - reflexivity.
  - destruct p; cbn in ts; rewrite (native_vector2_eta ts).
    + change
        (N.NMem (term_label rho ((Vector.hd (Vector.tl ts))`[sigma]))
                (term_label rho ((Vector.hd ts)`[sigma])) =
         N.NMem (term_label (fun i => term_label rho (sigma i)) (Vector.hd (Vector.tl ts)))
                (term_label (fun i => term_label rho (sigma i)) (Vector.hd ts))).
      f_equal; apply term_label_substitution.
    + change
        (N.NEq (term_label rho ((Vector.hd ts)`[sigma]))
               (term_label rho ((Vector.hd (Vector.tl ts))`[sigma])) =
         N.NEq (term_label (fun i => term_label rho (sigma i)) (Vector.hd ts))
               (term_label (fun i => term_label rho (sigma i)) (Vector.hd (Vector.tl ts)))).
      f_equal; apply term_label_substitution.
  - destruct op; cbn [native_named subst_form]; rewrite IHphi, IHpsi; reflexivity.
  - assert (He : forall i,
      term_label (push_label rho fresh) (up sigma i) =
      push_label (fun j => term_label rho (sigma j)) fresh i).
    { intros [|i]; [reflexivity|].
      change (term_label (push_label rho fresh) ((sigma i)`[↑]) = term_label rho (sigma i)).
      destruct (sigma i) as [j|[]]; reflexivity. }
    destruct op; cbn [native_named subst_form]; rewrite IH;
      rewrite (native_named_ext phi _ _ (S fresh) He); reflexivity.
Qed.

Lemma term_label_replace rho x y t :
  A.rename_label x y (term_label rho t) =
  term_label (fun i => A.rename_label x y (rho i)) t.
Proof. destruct t as [i|[]]; reflexivity. Qed.

Lemma native_named_replace (phi : C.set_form) : forall rho fresh x y,
  0 < x -> x < fresh ->
  A.replace_named x y (native_named phi rho fresh) =
  native_named phi (fun i => A.rename_label x y (rho i)) fresh.
Proof.
  induction phi as [|p ts|op phi IHphi psi IHpsi|op phi IH] using form_ind_falsity; intros rho fresh x y Hpos Hlt.
  - cbn [native_named A.replace_named]; unfold A.rename_label.
    rewrite (proj2 (Nat.eqb_neq 0 x) ltac:(lia)); reflexivity.
  - destruct p; cbn [native_named A.replace_named]; rewrite !term_label_replace; reflexivity.
  - destruct op; cbn [native_named A.replace_named];
      rewrite (IHphi rho fresh x y Hpos Hlt), (IHpsi rho fresh x y Hpos Hlt); reflexivity.
  - assert (He : forall i, A.rename_label x y (push_label rho fresh i) =
      push_label (fun j => A.rename_label x y (rho j)) fresh i).
    { intros [|i]; cbn [push_label]; [|reflexivity].
      unfold A.rename_label; rewrite (proj2 (Nat.eqb_neq fresh x) ltac:(lia)); reflexivity. }
    destruct op; cbn [native_named A.replace_named];
      rewrite (IH (push_label rho fresh) (S fresh) x y Hpos ltac:(lia));
      rewrite (native_named_ext phi _ _ (S fresh) He); reflexivity.
Qed.

Lemma native_named_shift phi rho fresh a :
  native_named (phi[↑]) (push_label rho a) fresh = native_named phi rho fresh.
Proof.
  rewrite native_named_substitution; apply native_named_ext.
  intro i; reflexivity.
Qed.

Lemma numeric_implication_congruence a aa b bb :
  Compiler238.derivable (wim aa a) -> Compiler238.derivable (wim b bb) ->
  Compiler238.derivable (wim (wim a b) (wim aa bb)).
Proof.
  intros Ha Hb; apply H.numeric_context_empty, H.numeric_context_implication_congruence;
    apply H.numeric_theorem; assumption.
Qed.

Lemma numeric_all_congruence x a b : Compiler238.derivable (wim a b) ->
  Compiler238.derivable (wim (wal x a) (wal x b)).
Proof.
  intro Himp; exact (Compiler238.derives_mp (wal x (wim a b))
    (wim (wal x a) (wal x b)) (Compiler238.derives_all x _ Himp)
    (Compiler238.derives_r2 x a b)).
Qed.

Lemma numeric_ex_congruence x a b : Compiler238.derivable (wim a b) ->
  Compiler238.derivable (wim (wex x a) (wex x b)).
Proof.
  intro Himp; unfold wex; apply H.numeric_contrapose, numeric_all_congruence,
    H.numeric_contrapose; exact Himp.
Qed.

(** Changing the allocation bound constructs actual alpha derivations.
    The environment is bounded below the old allocation bound; inner
    binders are moved first, and the outer binder is then renamed fresh. *)
Theorem native_named_reallocate (phi : C.set_form) : forall rho lo hi,
  0 < lo -> lo <= hi -> (forall i, rho i < lo) ->
  Compiler238.derivable (wim (native_code phi rho lo) (native_code phi rho hi)) /\
  Compiler238.derivable (wim (native_code phi rho hi) (native_code phi rho lo)).
Proof.
  induction phi as [|p ts|op phi IHphi psi IHpsi|op phi IH] using form_ind_falsity; intros rho lo hi Hpos Hle Hr.
  - split; apply H.numeric_I.
  - destruct p; split; apply H.numeric_I.
  - destruct (IHphi rho lo hi Hpos Hle Hr) as [Hp Hp'];
      destruct (IHpsi rho lo hi Hpos Hle Hr) as [Hq Hq'].
    unfold native_code in *; destruct op; cbn [native_named N.encode_named]; split.
    + apply H.numeric_contrapose, numeric_implication_congruence;
        [exact Hp|apply H.numeric_contrapose; exact Hq].
    + apply H.numeric_contrapose, numeric_implication_congruence;
        [exact Hp'|apply H.numeric_contrapose; exact Hq'].
    + apply numeric_implication_congruence; [apply H.numeric_contrapose; exact Hp|exact Hq].
    + apply numeric_implication_congruence; [apply H.numeric_contrapose; exact Hp'|exact Hq'].
    + apply numeric_implication_congruence; [exact Hp'|exact Hq].
    + apply numeric_implication_congruence; [exact Hp|exact Hq'].
  - destruct (Nat.eq_dec lo hi) as [->|Hneq]; [split; apply H.numeric_I|].
    assert (Hlt : lo < hi) by lia.
    assert (Hpush : forall i, push_label rho lo i < S lo).
    { intros [|i]; cbn [push_label]; [lia|specialize (Hr i); lia]. }
    destruct (IH (push_label rho lo) (S lo) (S hi) ltac:(lia) ltac:(lia) Hpush) as [Hp Hp'].
    set (q := native_named phi (push_label rho lo) (S hi)).
    assert (Hbind : N.binders_named lo q = false).
    { unfold q; apply native_named_binders_below; lia. }
    assert (Hnames : N.names_named hi q = false).
    { unfold q; apply native_named_names_below; [lia|lia|].
      intros [|i]; cbn [push_label]; [lia|specialize (Hr i); lia]. }
    assert (Erename : A.replace_named lo hi q = native_named phi (push_label rho hi) (S hi)).
    { unfold q; rewrite (native_named_replace phi (push_label rho lo) (S hi) lo hi Hpos ltac:(lia)).
      apply native_named_ext; intros [|i]; cbn [push_label]; unfold A.rename_label.
      - now rewrite Nat.eqb_refl.
      - rewrite (proj2 (Nat.eqb_neq (rho i) lo) ltac:(specialize (Hr i); lia)); reflexivity. }
    destruct op.
    + destruct (A.named_universal_alpha lo hi q ltac:(lia) Hbind Hnames) as [Ha Ha'];
        rewrite Erename in Ha, Ha'.
      unfold native_code; cbn [native_named N.encode_named]; split.
      * apply H.numeric_implication_compose with (b := wal lo (N.encode_named q));
          [apply numeric_all_congruence; exact Hp|exact Ha].
      * apply H.numeric_implication_compose with (b := wal lo (N.encode_named q));
          [exact Ha'|apply numeric_all_congruence; exact Hp'].
    + destruct (A.named_existential_alpha lo hi q ltac:(lia) Hbind Hnames) as [Ha Ha'];
        rewrite Erename in Ha, Ha'.
      change (Compiler238.derivable
        (wim (wex lo (native_code phi (push_label rho lo) (S lo)))
             (wex hi (native_code phi (push_label rho hi) (S hi)))) /\
        Compiler238.derivable
        (wim (wex hi (native_code phi (push_label rho hi) (S hi)))
             (wex lo (native_code phi (push_label rho lo) (S lo))))).
      split.
      * apply H.numeric_implication_compose with (b := wex lo (N.encode_named q));
          [apply numeric_ex_congruence; exact Hp|exact Ha].
      * apply H.numeric_implication_compose with (b := wex lo (N.encode_named q));
          [exact Ha'|apply numeric_ex_congruence; exact Hp'].
Qed.

Lemma term_label_bound rho lo t : (forall i, rho i < lo) -> term_label rho t < lo.
Proof. destruct t as [i|[]]; intro H; apply H. Qed.

Theorem native_vacuity_bound phi rho lo : 0 < lo -> (forall i, rho i < lo) ->
  Compiler238.derivable (wim (native_code phi rho lo) (wal lo (native_code phi rho lo))).
Proof.
  intros Hpos Hr.
  destruct (native_named_reallocate phi rho lo (S lo) Hpos ltac:(lia) Hr) as [Ha Ha'].
  assert (Hv : Compiler238.derivable
    (wim (native_code phi rho (S lo)) (wal lo (native_code phi rho (S lo))))).
  { unfold native_code; apply A.named_vacuity.
    - apply A.named_names_free, native_named_names_below; [exact Hpos|lia|].
      intro i; specialize (Hr i); lia.
    - apply native_named_binders_below; lia. }
  apply H.numeric_implication_compose with (b := native_code phi rho (S lo)); [exact Ha|].
  apply H.numeric_implication_compose with (b := wal lo (native_code phi rho (S lo)));
    [exact Hv|apply numeric_all_congruence; exact Ha'].
Qed.

Theorem native_universal_instance phi rho lo t :
  0 < lo -> (forall i, rho i < lo) ->
  Compiler238.derivable (wim (native_code (∀ phi) rho lo) (native_code (phi[t..]) rho lo)).
Proof.
  intros Hpos Hr; set (q := native_named phi (push_label rho lo) (S lo)).
  set (y := term_label rho t).
  assert (Hyl : y < lo) by (unfold y; apply term_label_bound; exact Hr).
  assert (Hlo : N.binders_named lo q = false).
  { unfold q; apply native_named_binders_below; lia. }
  assert (Hy : N.binders_named y q = false).
  { unfold q; apply native_named_binders_below; lia. }
  assert (Erename : A.replace_named lo y q = native_named (phi[t..]) rho (S lo)).
  { unfold q; rewrite (native_named_replace phi (push_label rho lo) (S lo) lo y Hpos ltac:(lia)).
    rewrite native_named_substitution; apply native_named_ext.
    intros [|i]; cbn [push_label scons term_label]; unfold A.rename_label.
    - now rewrite Nat.eqb_refl.
    - rewrite (proj2 (Nat.eqb_neq (rho i) lo) ltac:(specialize (Hr i); lia)); reflexivity. }
  pose proof (A.named_universal_instance lo y q ltac:(lia) Hlo Hy) as Hinst.
  rewrite Erename in Hinst.
  change (Compiler238.derivable
    (wim (native_code (∀ phi) rho lo) (native_code (phi[t..]) rho (S lo)))) in Hinst.
  destruct (native_named_reallocate (phi[t..]) rho lo (S lo) Hpos ltac:(lia) Hr) as [_ Ha].
  exact (H.numeric_implication_compose _ _ _ Hinst Ha).
Qed.

Theorem native_existential_instance phi rho lo t :
  0 < lo -> (forall i, rho i < lo) ->
  Compiler238.derivable (wim (native_code (phi[t..]) rho lo) (native_code (∃ phi) rho lo)).
Proof.
  intros Hpos Hr; apply H.numeric_context_empty, H.numeric_deduction.
  change (H.numeric_context ([native_code (phi[t..]) rho lo])
    (wn (native_code (∀ (phi → ⊥)) rho lo))).
  unfold wn; apply H.numeric_deduction.
  assert (Hinst : Compiler238.derivable
    (wim (native_code (∀ (phi → ⊥)) rho lo) (wn (native_code (phi[t..]) rho lo)))).
  { exact (native_universal_instance (phi → ⊥) rho lo t Hpos Hr). }
  apply (H.numeric_context_mp
    (native_code (∀ (phi → ⊥)) rho lo :: [native_code (phi[t..]) rho lo])
    (native_code (phi[t..]) rho lo) 1).
  - apply H.numeric_assumption; right; now left.
  - apply (H.numeric_context_mp
      (native_code (∀ (phi → ⊥)) rho lo :: [native_code (phi[t..]) rho lo])
      (native_code (∀ (phi → ⊥)) rho lo) (wn (native_code (phi[t..]) rho lo))).
    + apply H.numeric_assumption; now left.
    + apply H.numeric_theorem; exact Hinst.
Qed.

Theorem native_context_lower prefix G rho lo hi a :
  0 < lo -> lo <= hi -> (forall i, rho i < lo) ->
  H.numeric_context (prefix ++ map (fun phi => native_code phi rho hi) G) a ->
  H.numeric_context (prefix ++ map (fun phi => native_code phi rho lo) G) a.
Proof.
  intros Hpos Hle Hr D; apply (H.numeric_context_cut _ _ _ D).
  intros h Hh; apply in_app_or in Hh as [Hh|Hh].
  - apply H.numeric_assumption, in_or_app; now left.
  - apply in_map_iff in Hh as [phi [<- Hphi]].
    destruct (native_named_reallocate phi rho lo hi Hpos Hle Hr) as [Ha _].
    apply (H.numeric_context_mp
      (prefix ++ map (fun phi => native_code phi rho lo) G)
      (native_code phi rho lo) (native_code phi rho hi)).
    + apply H.numeric_assumption, in_or_app; right.
      exact (@in_map C.set_form nat (fun psi => native_code psi rho lo) G phi Hphi).
    + apply H.numeric_theorem; exact Ha.
Qed.

Fixpoint freshen_named (phi : N.named_formula) (lo : nat) : N.named_formula :=
  match phi with
  | N.NTruth => N.NTruth
  | N.NImp phi psi => N.NImp (freshen_named phi lo) (freshen_named psi lo)
  | N.NNot phi => N.NNot (freshen_named phi lo)
  | N.NMem a b => N.NMem a b
  | N.NEq a b => N.NEq a b
  | N.NAll a phi => N.NAll lo (A.replace_named a lo (freshen_named phi (S lo)))
  end.

Lemma freshen_named_binders_below phi : forall lo v,
  v < lo -> N.binders_named v (freshen_named phi lo) = false.
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH]; intros lo v Hlt;
    cbn [freshen_named N.binders_named].
  - reflexivity.
  - rewrite (IHphi lo v Hlt), (IHpsi lo v Hlt); reflexivity.
  - apply IH; exact Hlt.
  - reflexivity.
  - reflexivity.
  - rewrite A.replace_named_binders,
      (proj2 (Nat.eqb_neq v lo) ltac:(lia)), (IH (S lo) v ltac:(lia)); reflexivity.
Qed.

Lemma freshen_named_free_below phi : forall lo v,
  v < lo -> N.free_named v (freshen_named phi lo) = N.free_named v phi.
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH]; intros lo v Hlt;
    cbn [freshen_named N.free_named].
  - reflexivity.
  - now rewrite (IHphi lo v Hlt), (IHpsi lo v Hlt).
  - apply IH; exact Hlt.
  - reflexivity.
  - reflexivity.
  - rewrite (proj2 (Nat.eqb_neq v lo) ltac:(lia)); cbn.
    destruct (Nat.eq_dec v a) as [->|Hva].
    + rewrite A.replace_named_free by lia; now rewrite Nat.eqb_refl.
    + rewrite A.replace_named_free_outside by lia.
      rewrite (IH (S lo) v ltac:(lia)), (proj2 (Nat.eqb_neq v a) Hva); reflexivity.
Qed.

Lemma freshen_named_names_below phi lo v : v < lo ->
  N.names_named v (freshen_named phi lo) = N.free_named v phi.
Proof.
  intro Hlt; rewrite A.named_names_split, freshen_named_binders_below by exact Hlt.
  rewrite Bool.orb_false_r; apply freshen_named_free_below; exact Hlt.
Qed.

(** Arbitrary raw binder shadowing is removed by a finite numeric proof.
    The original syntax bounds select a label above every old name. Inner
    binders move first, making the actual outer alpha theorem applicable. *)
Theorem named_freshening phi : forall lo,
  (forall v, N.names_named v phi = true -> v < lo) ->
  Compiler238.derivable (wim (N.encode_named phi) (N.encode_named (freshen_named phi lo))) /\
  Compiler238.derivable (wim (N.encode_named (freshen_named phi lo)) (N.encode_named phi)).
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH]; intros lo Hb.
  - split; apply H.numeric_I.
  - assert (Hbphi : forall v, N.names_named v phi = true -> v < lo).
    { intros v Hv; apply Hb; cbn [N.names_named]; apply Bool.orb_true_iff; now left. }
    assert (Hbpsi : forall v, N.names_named v psi = true -> v < lo).
    { intros v Hv; apply Hb; cbn [N.names_named]; apply Bool.orb_true_iff; now right. }
    destruct (IHphi lo Hbphi) as [Hp Hp']; destruct (IHpsi lo Hbpsi) as [Hq Hq'].
    cbn [freshen_named N.encode_named]; split;
      apply numeric_implication_congruence; assumption.
  - destruct (IH lo Hb) as [Hp Hp']; cbn [freshen_named N.encode_named]; split;
      apply H.numeric_contrapose; assumption.
  - split; apply H.numeric_I.
  - split; apply H.numeric_I.
  - assert (Hal : a < lo).
    { apply Hb; cbn [N.names_named]; now rewrite Nat.eqb_refl. }
    assert (Hbphi : forall v, N.names_named v phi = true -> v < S lo).
    { intros v Hv; assert (v < lo).
      { apply Hb; cbn [N.names_named]; apply Bool.orb_true_iff; now right. }
      lia. }
    destruct (IH (S lo) Hbphi) as [Hp Hp']; set (q := freshen_named phi (S lo)).
    assert (Hbind : N.binders_named a q = false).
    { unfold q; apply freshen_named_binders_below; lia. }
    assert (Hname : N.names_named lo q = false).
    { unfold q; rewrite freshen_named_names_below by lia.
      apply A.named_names_free; destruct (N.names_named lo phi) eqn:E; [|reflexivity].
      assert (lo < lo).
      { apply Hb; cbn [N.names_named]; apply Bool.orb_true_iff; now right. }
      lia. }
    destruct (A.named_universal_alpha a lo q ltac:(lia) Hbind Hname) as [Ha Ha'].
    cbn [freshen_named N.encode_named]; split.
    + apply H.numeric_implication_compose with (b := wal a (N.encode_named q));
        [apply numeric_all_congruence; exact Hp|exact Ha].
    + apply H.numeric_implication_compose with (b := wal a (N.encode_named q));
        [exact Ha'|apply numeric_all_congruence; exact Hp'].
Qed.

Corollary encoded_named_freshening phi :
  Compiler238.derivable (wim (N.encode_named phi)
    (N.encode_named (freshen_named phi (S (N.encode_named phi))))) /\
  Compiler238.derivable (wim (N.encode_named (freshen_named phi (S (N.encode_named phi))))
    (N.encode_named phi)).
Proof.
  apply named_freshening; intros v Hv.
  pose proof (N.encode_named_names_bound phi v Hv); lia.
Qed.

Lemma term_label_shift rho fresh t :
  term_label (push_label rho fresh) (t`[↑]) = term_label rho t.
Proof. destruct t as [i|[]]; reflexivity. Qed.

Theorem native_interpret_environment phi : forall env tau rho sigma fresh,
  (forall v, N.free_named v phi = true -> term_label rho (env v) = term_label sigma (tau v)) ->
  native_named (N.interpret_named phi env) rho fresh =
  native_named (N.interpret_named phi tau) sigma fresh.
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    intros env tau rho sigma fresh He.
  - reflexivity.
  - assert (Hephi : forall v, N.free_named v phi = true ->
        term_label rho (env v) = term_label sigma (tau v)).
    { intros v Hv; apply He; cbn [N.free_named]; apply Bool.orb_true_iff; now left. }
    assert (Hepsi : forall v, N.free_named v psi = true ->
        term_label rho (env v) = term_label sigma (tau v)).
    { intros v Hv; apply He; cbn [N.free_named]; apply Bool.orb_true_iff; now right. }
    cbn [N.interpret_named native_named];
      rewrite (IHphi env tau rho sigma fresh Hephi), (IHpsi env tau rho sigma fresh Hepsi); reflexivity.
  - cbn [N.interpret_named native_named]; now rewrite (IH env tau rho sigma fresh He).
  - assert (Ha : term_label rho (env a) = term_label sigma (tau a)).
    { apply He; cbn [N.free_named]; apply Bool.orb_true_iff; left; apply Nat.eqb_refl. }
    assert (Hb : term_label rho (env b) = term_label sigma (tau b)).
    { apply He; cbn [N.free_named]; apply Bool.orb_true_iff; right; apply Nat.eqb_refl. }
    change (N.NMem (term_label rho (env a)) (term_label rho (env b)) =
      N.NMem (term_label sigma (tau a)) (term_label sigma (tau b))).
    now rewrite Ha, Hb.
  - assert (Ha : term_label rho (env a) = term_label sigma (tau a)).
    { apply He; cbn [N.free_named]; apply Bool.orb_true_iff; left; apply Nat.eqb_refl. }
    assert (Hb : term_label rho (env b) = term_label sigma (tau b)).
    { apply He; cbn [N.free_named]; apply Bool.orb_true_iff; right; apply Nat.eqb_refl. }
    change (N.NEq (term_label rho (env a)) (term_label rho (env b)) =
      N.NEq (term_label sigma (tau a)) (term_label sigma (tau b))).
    now rewrite Ha, Hb.
  - cbn [N.interpret_named native_named]; f_equal; apply IH.
    intros v Hv; unfold N.bind_env; destruct (Nat.eqb v a) eqn:E; [reflexivity|].
    rewrite !term_label_shift; apply He; cbn [N.free_named]; rewrite E; cbn; exact Hv.
Qed.

Lemma bind_update_labels env x y a : x <> a -> y <> a -> forall v,
  N.bind_env (N.update_env env x (env y)) a v =
  N.update_env (N.bind_env env a) x (N.bind_env env a y) v.
Proof.
  intros Hxa Hya v; unfold N.bind_env, N.update_env.
  rewrite (proj2 (Nat.eqb_neq y a) Hya).
  destruct (Nat.eqb v a) eqn:Ea; destruct (Nat.eqb v x) eqn:Ex; try reflexivity.
  apply Nat.eqb_eq in Ea; apply Nat.eqb_eq in Ex; congruence.
Qed.

Theorem interpret_named_replace x y phi : N.binders_named x phi = false ->
  N.binders_named y phi = false -> forall env,
  N.interpret_named (A.replace_named x y phi) env =
  N.interpret_named phi (N.update_env env x (env y)).
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH]; intros Hx Hy env.
  - reflexivity.
  - cbn [N.binders_named] in Hx, Hy.
    apply Bool.orb_false_iff in Hx as [Hx1 Hx2]; apply Bool.orb_false_iff in Hy as [Hy1 Hy2].
    cbn [A.replace_named N.interpret_named]; now rewrite (IHphi Hx1 Hy1 env), (IHpsi Hx2 Hy2 env).
  - cbn [A.replace_named N.interpret_named]; now rewrite (IH Hx Hy env).
  - cbn [A.replace_named N.interpret_named]; unfold A.rename_label, N.update_env;
      destruct (Nat.eqb a x), (Nat.eqb b x); reflexivity.
  - cbn [A.replace_named N.interpret_named]; unfold A.rename_label, N.update_env;
      destruct (Nat.eqb a x), (Nat.eqb b x); reflexivity.
  - cbn [N.binders_named] in Hx, Hy.
    apply Bool.orb_false_iff in Hx as [Hxa Hx]; apply Bool.orb_false_iff in Hy as [Hya Hy].
    apply Nat.eqb_neq in Hxa; apply Nat.eqb_neq in Hya.
    cbn [A.replace_named N.interpret_named]; f_equal; rewrite (IH Hx Hy (N.bind_env env a)).
    apply N.interpret_env_ext; intro v; symmetry; apply bind_update_labels; assumption.
Qed.

Fixpoint named_size (phi : N.named_formula) : nat :=
  match phi with
  | N.NTruth | N.NMem _ _ | N.NEq _ _ => 1
  | N.NImp phi psi => S (named_size phi + named_size psi)
  | N.NNot phi | N.NAll _ phi => S (named_size phi)
  end.

Fixpoint distinct_named_binders (phi : N.named_formula) : Prop :=
  match phi with
  | N.NTruth | N.NMem _ _ | N.NEq _ _ => True
  | N.NImp phi psi => distinct_named_binders phi /\ distinct_named_binders psi
  | N.NNot phi => distinct_named_binders phi
  | N.NAll a phi => N.binders_named a phi = false /\ distinct_named_binders phi
  end.

Lemma replace_named_size x y phi : named_size (A.replace_named x y phi) = named_size phi.
Proof.
  induction phi; cbn [A.replace_named named_size]; now rewrite ?IHphi, ?IHphi1, ?IHphi2.
Qed.

Lemma replace_named_distinct x y phi : distinct_named_binders phi ->
  distinct_named_binders (A.replace_named x y phi).
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    cbn [A.replace_named distinct_named_binders]; intros H.
  - exact I.
  - destruct H as [Hphi Hpsi]; split; [now apply IHphi|now apply IHpsi].
  - now apply IH.
  - exact I.
  - exact I.
  - destruct H as [Hb Hphi]; rewrite A.replace_named_binders; split; [exact Hb|now apply IH].
Qed.

Lemma freshen_named_distinct phi : forall lo, distinct_named_binders (freshen_named phi lo).
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    intro lo; cbn [freshen_named distinct_named_binders].
  - exact I.
  - split; [apply IHphi|apply IHpsi].
  - apply IH.
  - exact I.
  - exact I.
  - split.
    + rewrite A.replace_named_binders; apply freshen_named_binders_below; lia.
    + apply replace_named_distinct, IH.
Qed.

Lemma rename_label_name_source x y v a : Nat.eqb v (A.rename_label x y a) = true ->
  v = y \/ Nat.eqb v a = true.
Proof.
  unfold A.rename_label; destruct (Nat.eqb a x); intro H.
  - left; now apply Nat.eqb_eq.
  - now right.
Qed.

Lemma replace_named_name_source x y phi : forall v,
  N.names_named v (A.replace_named x y phi) = true -> v = y \/ N.names_named v phi = true.
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    intros v Hv; cbn [A.replace_named N.names_named] in *.
  - discriminate.
  - apply Bool.orb_true_iff in Hv as [Hv|Hv].
    + destruct (IHphi v Hv) as [Hy|Hphi]; [now left|].
      right; apply Bool.orb_true_iff; now left.
    + destruct (IHpsi v Hv) as [Hy|Hpsi]; [now left|].
      right; apply Bool.orb_true_iff; now right.
  - now apply IH.
  - apply Bool.orb_true_iff in Hv as [Hv|Hv].
    + destruct (rename_label_name_source x y v a Hv) as [Hy|Ha]; [now left|].
      right; apply Bool.orb_true_iff; now left.
    + destruct (rename_label_name_source x y v b Hv) as [Hy|Hb]; [now left|].
      right; apply Bool.orb_true_iff; now right.
  - apply Bool.orb_true_iff in Hv as [Hv|Hv].
    + destruct (rename_label_name_source x y v a Hv) as [Hy|Ha]; [now left|].
      right; apply Bool.orb_true_iff; now left.
    + destruct (rename_label_name_source x y v b Hv) as [Hy|Hb]; [now left|].
      right; apply Bool.orb_true_iff; now right.
  - apply Bool.orb_true_iff in Hv as [Hv|Hv].
    + right; apply Bool.orb_true_iff; now left.
    + destruct (IH v Hv) as [Hy|Hphi]; [now left|].
      right; apply Bool.orb_true_iff; now right.
Qed.

Theorem freshen_named_interpret phi : forall lo,
  (forall v, N.names_named v phi = true -> v < lo) -> forall env,
  N.interpret_named (freshen_named phi lo) env = N.interpret_named phi env.
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH]; intros lo Hb env.
  - reflexivity.
  - assert (Hbphi : forall v, N.names_named v phi = true -> v < lo).
    { intros v Hv; apply Hb; cbn [N.names_named]; apply Bool.orb_true_iff; now left. }
    assert (Hbpsi : forall v, N.names_named v psi = true -> v < lo).
    { intros v Hv; apply Hb; cbn [N.names_named]; apply Bool.orb_true_iff; now right. }
    cbn [freshen_named N.interpret_named]; now rewrite (IHphi lo Hbphi env), (IHpsi lo Hbpsi env).
  - cbn [freshen_named N.interpret_named]; now rewrite (IH lo Hb env).
  - reflexivity.
  - reflexivity.
  - assert (Hal : a < lo).
    { apply Hb; cbn [N.names_named]; now rewrite Nat.eqb_refl. }
    assert (Hbphi : forall v, N.names_named v phi = true -> v < S lo).
    { intros v Hv; assert (v < lo).
      { apply Hb; cbn [N.names_named]; apply Bool.orb_true_iff; now right. }
      lia. }
    assert (Hba : N.binders_named a (freshen_named phi (S lo)) = false).
    { apply freshen_named_binders_below; lia. }
    assert (Hbl : N.binders_named lo (freshen_named phi (S lo)) = false).
    { apply freshen_named_binders_below; lia. }
    cbn [freshen_named N.interpret_named]; f_equal.
    rewrite (interpret_named_replace a lo (freshen_named phi (S lo)) Hba Hbl (N.bind_env env lo)).
    rewrite (IH (S lo) Hbphi (N.update_env (N.bind_env env lo) a (N.bind_env env lo lo))).
    apply N.interpret_env_agree; intros v Hv.
    assert (Hvl : v < lo).
    { apply Hb; cbn [N.names_named]; apply Bool.orb_true_iff; right.
      apply N.free_named_in_names; exact Hv. }
    unfold N.update_env, N.bind_env.
    rewrite Nat.eqb_refl, (proj2 (Nat.eqb_neq v lo) ltac:(lia)).
    destruct (Nat.eqb v a); reflexivity.
Qed.

Fixpoint close_named (n : nat) (phi : N.named_formula) : N.named_formula :=
  match n with 0 => phi | S k => N.NAll k (close_named k phi) end.

Definition close_term_env n (env : N.named_env) v : C.set_term :=
  if Nat.ltb v n then $v else (env v)`[fun i => $(n + i)].

Lemma close_term_env_zero env v : close_term_env 0 env v = env v.
Proof.
  unfold close_term_env; rewrite (proj2 (Nat.ltb_ge v 0) ltac:(lia)).
  destruct (env v) as [i|[]]; cbn [subst_term]; reflexivity.
Qed.

Lemma close_term_env_step n env v :
  close_term_env n (N.bind_env env n) v = close_term_env (S n) env v.
Proof.
  destruct (lt_dec v n) as [Hlt|Hge].
  - unfold close_term_env; rewrite (proj2 (Nat.ltb_lt v n) Hlt),
      (proj2 (Nat.ltb_lt v (S n)) ltac:(lia)); reflexivity.
  - destruct (Nat.eq_dec v n) as [->|Hneq].
    + unfold close_term_env, N.bind_env.
      rewrite Nat.ltb_irrefl, Nat.eqb_refl, (proj2 (Nat.ltb_lt n (S n)) ltac:(lia)).
      cbn [subst_term]; now rewrite Nat.add_0_r.
    + unfold close_term_env, N.bind_env.
      rewrite (proj2 (Nat.ltb_ge v n) ltac:(lia)),
        (proj2 (Nat.ltb_ge v (S n)) ltac:(lia)), (proj2 (Nat.eqb_neq v n) Hneq).
      destruct (env v) as [i|[]]; cbn [subst_term funcomp]; f_equal; lia.
Qed.

Theorem close_named_interpret n phi : forall env,
  N.interpret_named (close_named n phi) env = forall_times n (N.interpret_named phi (close_term_env n env)).
Proof.
  induction n as [|n IH]; intro env.
  - cbn [close_named forall_times]; apply N.interpret_env_ext; intro v; symmetry; apply close_term_env_zero.
  - change ((∀ N.interpret_named (close_named n phi) (N.bind_env env n)) =
      ∀ forall_times n (N.interpret_named phi (close_term_env (S n) env))).
    f_equal; rewrite IH; f_equal.
    apply N.interpret_env_ext; intro v; apply close_term_env_step.
Qed.

Theorem close_named_exact n phi :
  (forall v, N.free_named v phi = true -> v < n) -> forall env,
  N.interpret_named (close_named n phi) env =
  forall_times n (N.interpret_named phi (fun v => $v)).
Proof.
  intros Hb env; rewrite close_named_interpret; f_equal; apply N.interpret_env_agree.
  intros v Hv; unfold close_term_env; rewrite (proj2 (Nat.ltb_lt v n) (Hb v Hv)); reflexivity.
Qed.

Theorem close_named_numeric n phi : Compiler238.derivable (N.encode_named phi) ->
  Compiler238.derivable (N.encode_named (close_named n phi)).
Proof.
  intro D; induction n as [|n IH]; [exact D|].
  exact (Compiler238.derives_all n (N.encode_named (close_named n phi)) IH).
Qed.

(** Closed native formulas are independent of the labels assigned to
    their free de Bruijn slots. Bounds are syntactic, so this relocation
    requires no logical premise or interpretation assumption. *)
Lemma term_label_bounded_agree n t rho tau : bounded_t n t ->
  (forall i, i < n -> rho i = tau i) -> term_label rho t = term_label tau t.
Proof.
  destruct t as [i|[]]; intros Hb He; inversion Hb; subst.
  apply He; assumption.
Qed.

Lemma native_named_bounded_agree {ff} n
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : bounded n phi ->
  forall rho tau fresh, (forall i, i < n -> rho i = tau i) ->
  native_named phi rho fresh = native_named phi tau fresh.
Proof.
  intro Hb; induction Hb as
    [ff n p v H | op ff n phi psi Hb1 IH1 Hb2 IH2 | op ff n phi Hb IH | n];
    intros rho tau fresh He.
  - destruct p; cbn in v.
    + assert (Hhead : bounded_t n (Vector.hd v)).
      { apply H; rewrite (native_vector2_eta v); constructor. }
      assert (Htail : bounded_t n (Vector.hd (Vector.tl v))).
      { apply H; rewrite (native_vector2_eta v); constructor 2; constructor. }
      change (N.NMem (term_label rho (Vector.hd (Vector.tl v))) (term_label rho (Vector.hd v)) =
        N.NMem (term_label tau (Vector.hd (Vector.tl v))) (term_label tau (Vector.hd v))).
      f_equal.
      * exact (term_label_bounded_agree n _ rho tau Htail He).
      * exact (term_label_bounded_agree n _ rho tau Hhead He).
    + assert (Hhead : bounded_t n (Vector.hd v)).
      { apply H; rewrite (native_vector2_eta v); constructor. }
      assert (Htail : bounded_t n (Vector.hd (Vector.tl v))).
      { apply H; rewrite (native_vector2_eta v); constructor 2; constructor. }
      change (N.NEq (term_label rho (Vector.hd v)) (term_label rho (Vector.hd (Vector.tl v))) =
        N.NEq (term_label tau (Vector.hd v)) (term_label tau (Vector.hd (Vector.tl v)))).
      f_equal.
      * exact (term_label_bounded_agree n _ rho tau Hhead He).
      * exact (term_label_bounded_agree n _ rho tau Htail He).
  - destruct op; cbn [native_named];
      rewrite (IH1 rho tau fresh He), (IH2 rho tau fresh He); reflexivity.
  - assert (Hp : forall i, i < S n -> push_label rho fresh i = push_label tau fresh i).
    { intros [|i] Hi; cbn [push_label]; [reflexivity | apply He; lia]. }
    destruct op; cbn [native_named]; rewrite (IH _ _ _ Hp); reflexivity.
  - reflexivity.
Qed.

Lemma native_named_closed_agree (phi : C.set_form) rho tau fresh : bounded 0 phi ->
  native_named phi rho fresh = native_named phi tau fresh.
Proof.
  intro Hb; apply (native_named_bounded_agree 0 phi Hb rho tau fresh).
  intros i Hi; lia.
Qed.

Theorem native_closed_numeric_relocate phi rho lo hi : bounded 0 phi ->
  0 < lo -> 0 < hi -> Compiler238.derivable (native_code phi rho lo) ->
  Compiler238.derivable (native_code phi (fun _ => 0) hi).
Proof.
  intros Hb Hlo Hhi Hd.
  assert (Elo : native_code phi rho lo = native_code phi (fun _ => 0) lo).
  { unfold native_code; now rewrite (native_named_closed_agree phi rho (fun _ => 0) lo Hb). }
  rewrite Elo in Hd.
  destruct (le_dec lo hi) as [Hle | Hgt].
  - destruct (native_named_reallocate phi (fun _ => 0) lo hi Hlo Hle
      ltac:(intro i; exact Hlo)) as [Hforward _].
    exact (Compiler238.derives_mp _ _ Hd Hforward).
  - destruct (native_named_reallocate phi (fun _ => 0) hi lo Hhi ltac:(lia)
      ltac:(intro i; exact Hhi)) as [_ Hback].
    exact (Compiler238.derives_mp _ _ Hd Hback).
Qed.

Lemma native_atom2_terms_bounded n (p : ZF_Preds) x y :
  bounded_t n x -> bounded_t n y -> bounded n (atom p (C.terms2 x y) : C.set_form).
Proof.
  intros Hx Hy; constructor; intros t Ht; unfold C.terms2 in Ht.
  apply vec_cons_inv in Ht as [-> | Ht]; [exact Hx |].
  apply vec_cons_inv in Ht as [-> | Ht]; [exact Hy |].
  inversion Ht.
Qed.

Theorem named_interpret_bounded phi : forall n env,
  (forall v, N.free_named v phi = true -> bounded_t n (env v)) ->
  bounded n (N.interpret_named phi env).
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    intros n env Hb.
  - cbn [N.interpret_named]; constructor; constructor.
  - cbn [N.interpret_named]; constructor.
    + apply IHphi; intros v Hv; apply Hb; cbn [N.free_named].
      apply Bool.orb_true_iff; now left.
    + apply IHpsi; intros v Hv; apply Hb; cbn [N.free_named].
      apply Bool.orb_true_iff; now right.
  - cbn [N.interpret_named]; constructor; [apply IH; exact Hb | constructor].
  - unfold N.interpret_named, C.R; apply native_atom2_terms_bounded;
      apply Hb; cbn [N.free_named]; apply Bool.orb_true_iff;
      [right | left]; apply Nat.eqb_refl.
  - unfold N.interpret_named, C.E; apply native_atom2_terms_bounded;
      apply Hb; cbn [N.free_named]; apply Bool.orb_true_iff;
      [left | right]; apply Nat.eqb_refl.
  - cbn [N.interpret_named]; constructor; apply IH; intros v Hv.
    unfold N.bind_env; destruct (Nat.eqb v a) eqn:E.
    + constructor; lia.
    + eapply (subst_bounded_max_t (ff := falsity_on) (n := n) (m := S n)
        (t := env v) (sigma := ↑)).
      * intros i Hi; constructor; cbn; lia.
      * apply Hb; cbn [N.free_named]; rewrite E; cbn; exact Hv.
Qed.

Lemma named_closed_bound phi :
  bounded 0 (forall_times (S (N.encode_named phi))
    (N.interpret_named phi (fun v => $v))).
Proof.
  apply C.forall_times_closed, named_interpret_bounded; intros v Hv.
  constructor; pose proof (N.encode_named_names_bound phi v (N.free_named_in_names v phi Hv)); lia.
Qed.

Print Assumptions named_interpret_bounded.
Print Assumptions named_closed_bound.
Print Assumptions term_label_bounded_agree.
Print Assumptions native_named_bounded_agree.
Print Assumptions native_named_closed_agree.
Print Assumptions native_closed_numeric_relocate.
Print Assumptions native_named_ext.
Print Assumptions native_named_binders_below.
Print Assumptions native_named_names_below.
Print Assumptions native_named_substitution.
Print Assumptions native_named_replace.
Print Assumptions native_named_reallocate.
Print Assumptions native_vacuity_bound.
Print Assumptions native_universal_instance.
Print Assumptions native_existential_instance.
Print Assumptions named_freshening.
Print Assumptions encoded_named_freshening.
Print Assumptions native_interpret_environment.
Print Assumptions interpret_named_replace.
Print Assumptions freshen_named_distinct.
Print Assumptions freshen_named_interpret.
Print Assumptions close_named_exact.
Print Assumptions close_named_numeric.
End NativeNamed238.
