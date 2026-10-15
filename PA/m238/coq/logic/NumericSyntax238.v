(** Original numeric-to-formula syntax for the pinned PA238 calculus.

    Numeric variable labels are names, not de Bruijn indices. The total
    decoder first builds a named formula, and [interpret_named] interprets
    names through an environment. A wal binder binds its named label and
    shifts every other environment term. Code 0 is a closed truth formula;
    code 1 is converse self-membership. Implication to code 1 is interpreted
    as native negation. IR justifies introducing such implications and
    turns the code-1 alias into a finite compact refutation. No adequacy
    or consistency premise is assumed.

    The local Jeff m254 sources were consulted as mathematical references;
    their unresolved incorporation permission is recorded in README.md.
    This source imports only original PA modules and the licensed library. *)
From Coq Require Import Arith Lia Bool List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.logic Require Import Codes238 Compiler238.
From P238.arith Require Import Compact238 PointedSchemas238.
Import ListNotations FullSyntax BinSig ZFSignature.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module NumericSyntax238.
Module C := Compact238.Compact238.

Inductive named_formula :=
  | NTruth
  | NImp (antecedent consequent : named_formula)
  | NNot (body : named_formula)
  | NMem (container member : nat)
  | NEq (left right : nat)
  | NAll (name : nat) (body : named_formula).

Definition named_env := nat -> C.set_term.
Definition bind_env (rho : named_env) (a : nat) : named_env :=
  fun v => if Nat.eqb v a then $0 else (rho v)`[↑].
Definition update_env (rho : named_env) (a : nat) (t : C.set_term) : named_env :=
  fun v => if Nat.eqb v a then t else rho v.

Fixpoint interpret_named (phi : named_formula) (rho : named_env) : C.set_form :=
  match phi with
  | NTruth => ⊥ → ⊥
  | NImp phi psi => interpret_named phi rho → interpret_named psi rho
  | NNot phi => ¬ interpret_named phi rho
  | NMem a b => C.R (rho a) (rho b)
  | NEq a b => C.E (rho a) (rho b)
  | NAll a phi => ∀ interpret_named phi (bind_env rho a)
  end.

Fixpoint free_named (v : nat) (phi : named_formula) : bool :=
  match phi with
  | NTruth => false
  | NImp phi psi => free_named v phi || free_named v psi
  | NNot phi => free_named v phi
  | NMem a b | NEq a b => Nat.eqb v a || Nat.eqb v b
  | NAll a phi => negb (Nat.eqb v a) && free_named v phi
  end.

Lemma interpret_env_agree phi : forall rho tau,
  (forall v, free_named v phi = true -> rho v = tau v) ->
  interpret_named phi rho = interpret_named phi tau.
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    intros rho tau H; cbn [interpret_named].
  - reflexivity.
  - f_equal.
    + apply IHphi. intros v Hv. apply H. cbn [free_named].
      apply Bool.orb_true_iff; now left.
    + apply IHpsi. intros v Hv. apply H. cbn [free_named].
      apply Bool.orb_true_iff; now right.
  - f_equal. apply IH. exact H.
  - assert (Ha : rho a = tau a).
    { apply H. cbn [free_named]. apply Bool.orb_true_iff; left; apply Nat.eqb_refl. }
    assert (Hb : rho b = tau b).
    { apply H. cbn [free_named]. apply Bool.orb_true_iff; right; apply Nat.eqb_refl. }
    now rewrite Ha, Hb.
  - assert (Ha : rho a = tau a).
    { apply H. cbn [free_named]. apply Bool.orb_true_iff; left; apply Nat.eqb_refl. }
    assert (Hb : rho b = tau b).
    { apply H. cbn [free_named]. apply Bool.orb_true_iff; right; apply Nat.eqb_refl. }
    now rewrite Ha, Hb.
  - f_equal. apply IH. intros v Hv. unfold bind_env.
    destruct (Nat.eqb v a) eqn:E; [reflexivity|].
    rewrite H; [reflexivity|]. cbn [free_named]. rewrite E; cbn; exact Hv.
Qed.

Lemma interpret_env_ext phi rho tau :
  (forall v, rho v = tau v) -> interpret_named phi rho = interpret_named phi tau.
Proof. intro H; apply interpret_env_agree; intros v _; apply H. Qed.

Lemma interpret_fresh phi v rho t : free_named v phi = false ->
  interpret_named phi rho = interpret_named phi (update_env rho v t).
Proof.
  intro Hfresh; apply interpret_env_agree. intros u Hu; unfold update_env.
  destruct (Nat.eqb u v) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E; subst u; rewrite Hfresh in Hu; discriminate.
Qed.

Lemma interpret_substitution phi : forall rho sigma,
  (interpret_named phi rho)[sigma] =
  interpret_named phi (fun v => (rho v)`[sigma]).
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    intros rho sigma; cbn [interpret_named C.R C.E C.terms2 subst_form Vector.map].
  - reflexivity.
  - now rewrite IHphi, IHpsi.
  - now rewrite IH.
  - reflexivity.
  - reflexivity.
  - f_equal. rewrite IH. apply interpret_env_ext. intro v; unfold bind_env.
    destruct (Nat.eqb v a); [reflexivity|apply up_term].
Qed.

Lemma interpret_binder_instance phi rho a t :
  (interpret_named phi (bind_env rho a))[t..] =
  interpret_named phi (update_env rho a t).
Proof.
  rewrite interpret_substitution. apply interpret_env_ext. intro v.
  unfold bind_env, update_env; destruct (Nat.eqb v a); [reflexivity|apply subst_term_shift].
Qed.

Corollary interpret_binder_restore phi rho a :
  (interpret_named phi (bind_env rho a))[(rho a)..] = interpret_named phi rho.
Proof.
  rewrite interpret_binder_instance. apply interpret_env_ext. intro v.
  unfold update_env; destruct (Nat.eqb v a) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E; now subst v.
Qed.

(** Forward syntax uses the existing named tree. Code 1 is the relative
    proof-calculus bottom; its native decoder interpretation is kept separate.
    All labels, including inner binder labels, lie below an encoded formula. *)
Fixpoint encode_named (phi : named_formula) : nat :=
  match phi with
  | NTruth => 0
  | NImp phi psi => wim (encode_named phi) (encode_named psi)
  | NNot phi => wn (encode_named phi)
  | NMem a b => wel a b
  | NEq a b => weq a b
  | NAll a phi => wal a (encode_named phi)
  end.

Fixpoint names_named (v : nat) (phi : named_formula) : bool :=
  match phi with
  | NTruth => false
  | NImp phi psi => names_named v phi || names_named v psi
  | NNot phi => names_named v phi
  | NMem a b | NEq a b => Nat.eqb v a || Nat.eqb v b
  | NAll a phi => Nat.eqb v a || names_named v phi
  end.

Fixpoint binders_named (v : nat) (phi : named_formula) : bool :=
  match phi with
  | NTruth | NMem _ _ | NEq _ _ => false
  | NImp phi psi => binders_named v phi || binders_named v psi
  | NNot phi => binders_named v phi
  | NAll a phi => Nat.eqb v a || binders_named v phi
  end.

Lemma free_named_in_names v phi : free_named v phi = true -> names_named v phi = true.
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    cbn [free_named names_named]; intro H.
  - discriminate.
  - apply Bool.orb_true_iff in H as [H|H]; apply Bool.orb_true_iff;
      [left; now apply IHphi|right; now apply IHpsi].
  - now apply IH.
  - exact H.
  - exact H.
  - apply Bool.andb_true_iff in H as [_ H].
    apply Bool.orb_true_iff; right; now apply IH.
Qed.

Lemma binders_named_in_names v phi : binders_named v phi = true -> names_named v phi = true.
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    cbn [binders_named names_named]; intro H; try discriminate.
  - apply Bool.orb_true_iff in H as [H|H]; apply Bool.orb_true_iff;
      [left; now apply IHphi|right; now apply IHpsi].
  - now apply IH.
  - apply Bool.orb_true_iff in H as [H|H]; apply Bool.orb_true_iff;
      [now left|right; now apply IH].
Qed.

Theorem encode_named_names_bound phi : forall v,
  names_named v phi = true -> v < encode_named phi.
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    intros v Hv; cbn [names_named encode_named] in *.
  - discriminate.
  - pose proof (P_bounds (encode_named phi) (encode_named psi)) as [Ha Hb].
    apply Bool.orb_true_iff in Hv as [Hv|Hv]; unfold wim;
      [specialize (IHphi v Hv)|specialize (IHpsi v Hv)]; lia.
  - pose proof (P_bounds (encode_named phi) 1) as [Ha Hb].
    specialize (IH v Hv); unfold wn, wim; lia.
  - pose proof (P_bounds a b) as [Ha Hb].
    apply Bool.orb_true_iff in Hv as [Hv|Hv]; apply Nat.eqb_eq in Hv; subst v;
      unfold wel; lia.
  - pose proof (P_bounds a b) as [Ha Hb].
    apply Bool.orb_true_iff in Hv as [Hv|Hv]; apply Nat.eqb_eq in Hv; subst v;
      unfold weq; lia.
  - pose proof (P_bounds a (encode_named phi)) as [Ha Hb].
    apply Bool.orb_true_iff in Hv as [Hv|Hv]; unfold wal.
    + apply Nat.eqb_eq in Hv; subst v; lia.
    + specialize (IH v Hv); lia.
Qed.

Theorem encoded_output_names_fresh phi : names_named (encode_named phi) phi = false.
Proof.
  destruct (names_named (encode_named phi) phi) eqn:E; [|reflexivity].
  pose proof (encode_named_names_bound phi (encode_named phi) E); lia.
Qed.

Corollary encoded_output_free_fresh phi : free_named (encode_named phi) phi = false.
Proof.
  destruct (free_named (encode_named phi) phi) eqn:E; [|reflexivity].
  apply free_named_in_names in E; rewrite encoded_output_names_fresh in E; discriminate.
Qed.

Corollary encoded_output_binders_fresh phi : binders_named (encode_named phi) phi = false.
Proof.
  destruct (binders_named (encode_named phi) phi) eqn:E; [|reflexivity].
  apply binders_named_in_names in E; rewrite encoded_output_names_fresh in E; discriminate.
Qed.

Definition decode_node (rec : nat -> named_formula) (n : nat) : named_formula :=
  let '(a, b) := unP (n / 4) in
  match n mod 4 with
  | 0 => if Nat.eqb b 1 then NNot (rec a) else NImp (rec a) (rec b)
  | 1 => NMem a b
  | 2 => NAll a (rec b)
  | _ => NEq a b
  end.

Fixpoint decode_fuel (fuel n : nat) : named_formula :=
  match fuel with
  | 0 => NTruth
  | S fuel => match n with 0 => NTruth | S _ => decode_node (decode_fuel fuel) n end
  end.
Definition decode n := decode_fuel (S n) n.
Definition interpret_code n rho := interpret_named (decode n) rho.

Lemma quotient_smaller n : 0 < n -> n / 4 < n.
Proof. intro H; apply Nat.div_lt; lia. Qed.

Lemma decode_fuel_stable fuel : forall other n,
  n < fuel -> n < other -> decode_fuel fuel n = decode_fuel other n.
Proof.
  induction fuel as [|fuel IH]; intros [|other] n Hfuel Hother; try lia.
  destruct n as [|n]; [reflexivity|]. cbn [decode_fuel]; unfold decode_node.
  pose proof (quotient_smaller (S n) ltac:(lia)) as Hdiv.
  destruct (unP (S n / 4)) as [a b] eqn:E.
  pose proof (unP_bounds (S n / 4)) as Hpair; rewrite E in Hpair; cbn [fst snd] in Hpair.
  pose proof (IH other a ltac:(lia) ltac:(lia)) as Ha.
  pose proof (IH other b ltac:(lia) ltac:(lia)) as Hb.
  destruct (S n mod 4) as [|[|[|tag]]]; try reflexivity.
  - destruct (Nat.eqb b 1); [now rewrite Ha|now rewrite Ha, Hb].
  - now rewrite Hb.
Qed.

Lemma decode_node_agree rec other n : 0 < n ->
  (forall k, k < n -> rec k = other k) -> decode_node rec n = decode_node other n.
Proof.
  intros Hn H; unfold decode_node.
  pose proof (quotient_smaller n Hn) as Hdiv.
  destruct (unP (n / 4)) as [a b] eqn:E.
  pose proof (unP_bounds (n / 4)) as Hpair; rewrite E in Hpair; cbn [fst snd] in Hpair.
  pose proof (H a ltac:(lia)) as Ha; pose proof (H b ltac:(lia)) as Hb.
  destruct (n mod 4) as [|[|[|tag]]]; try reflexivity.
  - destruct (Nat.eqb b 1); [now rewrite Ha|now rewrite Ha, Hb].
  - now rewrite Hb.
Qed.

Lemma decode_unfold n : 0 < n -> decode n = decode_node decode n.
Proof.
  intro Hn; unfold decode at 1; destruct n as [|n]; [lia|].
  change (decode_node (decode_fuel (S n)) (S n) = decode_node decode (S n)).
  apply decode_node_agree; [exact Hn|]. intros k Hk; unfold decode.
  apply decode_fuel_stable; lia.
Qed.

Lemma tagged_fields a b tag : tag < 4 ->
  (4 * P a b + tag) / 4 = P a b /\ (4 * P a b + tag) mod 4 = tag.
Proof.
  intro Htag; split.
  - rewrite Nat.mul_comm, Nat.div_add_l by lia.
    rewrite Nat.div_small by lia; lia.
  - rewrite Nat.mul_comm, Nat.add_comm, Nat.Div0.mod_add.
    apply Nat.mod_small; exact Htag.
Qed.

Lemma decode_zero : decode 0 = NTruth.
Proof. reflexivity. Qed.
Lemma decode_membership a b : decode (wel a b) = NMem a b.
Proof.
  unfold wel; rewrite decode_unfold by lia; unfold decode_node.
  destruct (tagged_fields a b 1 ltac:(lia)) as [Hdiv Hmod].
  rewrite Hdiv, Hmod, unP_P; reflexivity.
Qed.
Lemma decode_equality a b : decode (weq a b) = NEq a b.
Proof.
  unfold weq; rewrite decode_unfold by lia; unfold decode_node.
  destruct (tagged_fields a b 3 ltac:(lia)) as [Hdiv Hmod].
  rewrite Hdiv, Hmod, unP_P; reflexivity.
Qed.
Lemma decode_universal a b : decode (wal a b) = NAll a (decode b).
Proof.
  unfold wal; rewrite decode_unfold by lia; unfold decode_node.
  destruct (tagged_fields a b 2 ltac:(lia)) as [Hdiv Hmod].
  rewrite Hdiv, Hmod, unP_P; reflexivity.
Qed.
Lemma implication_positive a b : a + b > 0 -> wim a b > 0.
Proof. intro H; unfold wim; pose proof (P_bounds a b); lia. Qed.
Lemma decode_implication a b : b <> 1 -> a + b > 0 ->
  decode (wim a b) = NImp (decode a) (decode b).
Proof.
  intros Hneq Hpos; rewrite decode_unfold by (apply implication_positive; exact Hpos).
  unfold decode_node, wim; replace (4 * P a b) with (4 * P a b + 0) by lia.
  destruct (tagged_fields a b 0 ltac:(lia)) as [Hdiv Hmod].
  rewrite Hdiv, Hmod, unP_P, (proj2 (Nat.eqb_neq b 1) Hneq); reflexivity.
Qed.
Lemma decode_negation a : decode (wn a) = NNot (decode a).
Proof.
  unfold wn; rewrite decode_unfold by (apply implication_positive; lia).
  unfold decode_node, wim; replace (4 * P a 1) with (4 * P a 1 + 0) by lia.
  destruct (tagged_fields a 1 0 ltac:(lia)) as [Hdiv Hmod].
  rewrite Hdiv, Hmod, unP_P; reflexivity.
Qed.
Lemma negation_positive a : 0 < wn a.
Proof. unfold wn; apply implication_positive; lia. Qed.
Lemma decode_existential a b :
  decode (wex a b) = NNot (NAll a (NNot (decode b))).
Proof. unfold wex; now rewrite decode_negation, decode_universal, decode_negation. Qed.
Lemma decode_conjunction a b :
  decode (wa a b) = NNot (NImp (decode a) (NNot (decode b))).
Proof.
  unfold wa; rewrite decode_negation, decode_implication, decode_negation.
  - reflexivity.
  - unfold wn; apply wim_not_one.
  - pose proof (negation_positive b); lia.
Qed.

Theorem decode_fuel_free_bound fuel : forall n v,
  free_named v (decode_fuel fuel n) = true -> v < n.
Proof.
  induction fuel as [|fuel IH]; intros n v Hfree; [discriminate|].
  destruct n as [|n]; [discriminate|]. cbn [decode_fuel] in Hfree.
  unfold decode_node in Hfree.
  pose proof (quotient_smaller (S n) ltac:(lia)) as Hdiv.
  destruct (unP (S n / 4)) as [a b] eqn:E.
  pose proof (unP_bounds (S n / 4)) as Hpair; rewrite E in Hpair; cbn [fst snd] in Hpair.
  destruct (S n mod 4) as [|[|[|tag]]]; cbn [free_named] in Hfree.
  - destruct (Nat.eqb b 1); cbn [free_named] in Hfree.
    + pose proof (IH a v Hfree); lia.
    + apply Bool.orb_true_iff in Hfree as [Ha|Hb];
        [pose proof (IH a v Ha)|pose proof (IH b v Hb)]; lia.
  - apply Bool.orb_true_iff in Hfree as [Ha|Hb].
    + apply Nat.eqb_eq in Ha; lia.
    + apply Nat.eqb_eq in Hb; lia.
  - apply Bool.andb_true_iff in Hfree as [_ Hb]; pose proof (IH b v Hb); lia.
  - apply Bool.orb_true_iff in Hfree as [Ha|Hb].
    + apply Nat.eqb_eq in Ha; lia.
    + apply Nat.eqb_eq in Hb; lia.
Qed.

Corollary decode_free_bound n v : free_named v (decode n) = true -> v < n.
Proof. apply decode_fuel_free_bound. Qed.
Theorem decode_self_fresh n : free_named n (decode n) = false.
Proof.
  destruct (free_named n (decode n)) eqn:E; [|reflexivity].
  pose proof (decode_free_bound n n E); lia.
Qed.
Corollary output_name_fresh n rho t :
  interpret_code n rho = interpret_code n (update_env rho n t).
Proof. apply interpret_fresh, decode_self_fresh. Qed.

Lemma interpret_truth rho : interpret_code 0 rho = (⊥ → ⊥).
Proof. reflexivity. Qed.
Lemma interpret_one rho : interpret_code 1 rho = C.R (rho 0) (rho 0).
Proof.
  change (interpret_named (decode (wel 0 0)) rho = C.R (rho 0) (rho 0)).
  rewrite decode_membership; reflexivity.
Qed.
Lemma interpret_implication a b rho : b <> 1 -> a + b > 0 ->
  interpret_code (wim a b) rho = (interpret_code a rho → interpret_code b rho).
Proof. intros Hneq Hpos; unfold interpret_code; rewrite decode_implication by assumption; reflexivity. Qed.
Lemma interpret_negation a rho : interpret_code (wn a) rho = ¬ interpret_code a rho.
Proof. unfold interpret_code; rewrite decode_negation; reflexivity. Qed.
Lemma interpret_universal a b rho :
  interpret_code (wal a b) rho = ∀ interpret_code b (bind_env rho a).
Proof. unfold interpret_code; rewrite decode_universal; reflexivity. Qed.
Lemma interpret_membership a b rho :
  interpret_code (wel a b) rho = C.R (rho a) (rho b).
Proof. unfold interpret_code; rewrite decode_membership; reflexivity. Qed.
Lemma interpret_equality a b rho :
  interpret_code (weq a b) rho = C.E (rho a) (rho b).
Proof. unfold interpret_code; rewrite decode_equality; reflexivity. Qed.
Lemma interpret_existential a b rho :
  interpret_code (wex a b) rho = ¬ ∀ ¬ interpret_code b (bind_env rho a).
Proof. unfold interpret_code; rewrite decode_existential; reflexivity. Qed.
Lemma interpret_conjunction a b rho :
  interpret_code (wa a b) rho = ¬ (interpret_code a rho → ¬ interpret_code b rho).
Proof. unfold interpret_code; rewrite decode_conjunction; reflexivity. Qed.

Lemma compact_truth rho : C.derivable C.compact_theory (interpret_code 0 rho).
Proof.
  rewrite interpret_truth; exists []; split; [intros psi H; inversion H|].
  apply II, Ctx; now left.
Qed.
Lemma compact_not_one rho : C.derivable C.compact_theory (¬ interpret_code 1 rho).
Proof.
  rewrite interpret_one; exists [C.ir]; split.
  - intros psi [<-|[]]; apply C.compact_ir.
  - apply C.ir_guard, Ctx; now left.
Qed.
Lemma compact_explosion phi : C.derivable C.compact_theory ⊥ ->
  C.derivable C.compact_theory phi.
Proof. intros [G [HG Hbot]]; exists G; split; [exact HG|now apply Exp]. Qed.

Theorem numeric_mp_transport a b rho :
  C.derivable C.compact_theory (interpret_code a rho) ->
  C.derivable C.compact_theory (interpret_code (wim a b) rho) ->
  C.derivable C.compact_theory (interpret_code b rho).
Proof.
  intros Ha Hab; destruct (Nat.eq_dec b 1) as [-> | Hneq].
  - change (C.derivable C.compact_theory (interpret_code (wn a) rho)) in Hab.
    rewrite interpret_negation in Hab. apply compact_explosion.
    exact (C.derivable_mp C.compact_theory (interpret_code a rho) ⊥ Hab Ha).
  - destruct (Nat.eq_dec (a + b) 0) as [Hzero | Hpos].
    + assert (b = 0) by lia; subst b; apply compact_truth.
    + rewrite interpret_implication in Hab by lia.
      exact (C.derivable_mp C.compact_theory (interpret_code a rho) (interpret_code b rho) Hab Ha).
Qed.

Theorem numeric_generalize_transport a b :
  (forall rho, C.derivable C.compact_theory (interpret_code b rho)) ->
  forall rho, C.derivable C.compact_theory (interpret_code (wal a b) rho).
Proof.
  intros H rho; rewrite interpret_universal; apply C.compact_generalize, H.
Qed.

Notation "G ⊢N phi" :=
  (@prv sig_empty ZF_pred_sig falsity_on class G phi) (at level 61).

Lemma named_exists_equal G a b rho :
  G ⊢N (∀ C.E $0 $0) -> G ⊢N interpret_code (rho1 a b) rho.
Proof.
  intro HE; unfold rho1; rewrite interpret_existential.
  unfold interpret_code; rewrite decode_equality; apply II.
  assert (Hall : (∀ interpret_named (NNot (NEq a b)) (bind_env rho a)) :: G ⊢N
                 (∀ interpret_named (NNot (NEq a b)) (bind_env rho a))).
  { apply Ctx; now left. }
  pose proof (AllE (rho b) Hall) as Hnot.
  rewrite interpret_binder_instance in Hnot.
  assert (Ha : update_env rho a (rho b) a = rho b).
  { unfold update_env; now rewrite Nat.eqb_refl. }
  assert (Hb : update_env rho a (rho b) b = rho b).
  { unfold update_env; destruct (Nat.eqb b a); reflexivity. }
  cbn [interpret_named] in Hnot; rewrite Ha, Hb in Hnot.
  eapply IE; [exact Hnot|].
  eapply Weak; [exact (AllE (rho b) HE)|]; intros psi Hpsi; now right.
Qed.

Theorem numeric_r1_transport a b rho :
  C.derivable C.compact_theory (interpret_code (rho1 a b) rho).
Proof.
  exists [∀ C.E $0 $0]; split.
  - intros psi [<-|[]]; apply C.compact_equality; now left.
  - apply named_exists_equal, Ctx; now left.
Qed.

(** The reverse gate required by the S0 forward machine path quantifies
    only the actual pointed/equality producer. No IR supplier is available
    in this direction. This finite-context statement remains to be proved. *)
Definition compact_numeric_reverse_transport : Prop :=
  forall G : list C.set_form,
    (forall phi, In phi G ->
      PointedSchemas238.PointedSchemas238.pointed_equality_theory phi) ->
    G ⊢N ⊥ -> Compiler238.derivable 1.

Print Assumptions interpret_substitution.
Print Assumptions decode_self_fresh.
Print Assumptions encode_named_names_bound.
Print Assumptions encoded_output_binders_fresh.
Print Assumptions numeric_mp_transport.
Print Assumptions numeric_generalize_transport.
Print Assumptions numeric_r1_transport.
End NumericSyntax238.
