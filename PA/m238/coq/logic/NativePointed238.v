(** Original finite ordinary-ND readback of the exact PA238 raw R9.
    The member name and the fixed point name occupy distinct slots. The
    only IR premise used while reading a native property is later cut out
    with the actual numeric IR proof; it is never a source-theory axiom. *)
From Coq Require Import Arith List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.logic Require Import Codes238 Compiler238 NumericSyntax238
  NumericHilbert238 NumericNamed238 NumericSound238 NativeNamed238
  NativeND238 NativeReadback238 NativeAxioms238 NativeProperty238 RawInterpret238.
From P238.arith Require Import Compact238 PointedSchemas238 PAinCompact238 S0InCompact238.
Import ListNotations FullSyntax BinSig ZFSignature.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module NativePointed238.
Module C := Compact238.Compact238.
Module N := NumericSyntax238.NumericSyntax238.
Module T := NativeNamed238.NativeNamed238.
Module D := NativeND238.NativeND238.
Module V := NativeAxioms238.NativeAxioms238.
Module P := NativeProperty238.NativeProperty238.
Module R := RawInterpret238.RawInterpret238.
Module S := NumericSound238.NumericSound238.
Module A := NumericNamed238.NumericNamed238.
Notation "G ⊢NPt phi" :=
  (@prv sig_empty ZF_pred_sig falsity_on class G phi) (at level 61).

(** Slot 0 is the varying member, slot 1 the input, and slot 2 the
    fixed point. Truncation affects only slots outside the source bound. *)
Definition pointed_labels n : T.label_env := fun i =>
  if Nat.ltb i n then
    match i with 0 => 3 | 1 => 2 | 2 => 4 | S (S (S k)) => 5 + k end
  else 0.
Definition pointed_property (phi : C.set_form) n := T.native_named phi (pointed_labels n) (n + 5).
Definition pointed_environment (u x : C.set_term) : N.named_env := fun i =>
  match i with 2 => u | 3 => x | 4 => x | S (S (S (S (S k)))) => $k | _ => $0 end.
Definition pointed_named_matrix property :=
  let c := N.encode_named property in
  V.named_and
    (N.NAll 3 (V.named_and
      (N.NImp (N.NMem 2 3) (N.NImp property (N.NMem c 3)))
      (N.NImp (N.NMem c 3) property)))
    (N.NImp property (N.NMem c 3)).

Lemma pointed_labels_range n : forall i, pointed_labels n i < n + 5.
Proof.
  intro i; unfold pointed_labels; destruct (Nat.ltb i n) eqn:E.
  - apply Nat.ltb_lt in E; destruct i as [|[|[|k]]]; cbn; lia.
  - lia.
Qed.

Lemma pointed_environment_slots n u x i : i < n ->
  pointed_environment u x (pointed_labels n i) = (x .: u .: x .: var) i.
Proof.
  intro Hi; unfold pointed_labels; rewrite (proj2 (Nat.ltb_lt i n) Hi).
  destruct i as [|[|[|k]]]; reflexivity.
Qed.

Lemma pointed_member_slots n u x m i : i < n ->
  N.update_env (pointed_environment u x) 3 m (pointed_labels n i) =
  (m .: u .: x .: var) i.
Proof.
  intro Hi; unfold pointed_labels; rewrite (proj2 (Nat.ltb_lt i n) Hi).
  destruct i as [|[|[|k]]]; cbn [N.update_env pointed_environment scons]; reflexivity.
Qed.

Lemma padded_output_fresh property :
  N.free_named (N.encode_named (V.padded_property 2 3 property)) property = false.
Proof.
  set (c := N.encode_named (V.padded_property 2 3 property)).
  set (q := V.property_padding_label 2 3 property).
  assert (Hq : q < c).
  { apply N.encode_named_names_bound; unfold V.padded_property; fold q.
    cbn [N.names_named]; now rewrite Nat.eqb_refl. }
  destruct (N.free_named c property) eqn:E; [|reflexivity].
  pose proof (N.encode_named_names_bound property c (N.free_named_in_names c property E)).
  unfold q, V.property_padding_label in Hq; lia.
Qed.

(** Both directions below are finite derivations. The source formula is
    substituted only on the slots justified by its actual syntax bound. *)
Lemma padded_property_readback G phi n env witness_env sigma :
  bounded n phi -> G ⊢NPt C.ir ->
  (forall v, N.free_named v (pointed_property phi n) = true -> witness_env v = env v) ->
  (forall i, i < n -> env (pointed_labels n i) = sigma i) ->
  G ⊢NPt (N.interpret_named (V.padded_property 2 3 (pointed_property phi n)) witness_env → phi[sigma]) /\
  G ⊢NPt (phi[sigma] → N.interpret_named (V.padded_property 2 3 (pointed_property phi n)) witness_env).
Proof.
  intros Hb HIR He Hslots.
  destruct (V.padded_property_native G 2 3 (pointed_property phi n) witness_env) as [Hpad Hpad'].
  assert (Eproperty : N.interpret_named (pointed_property phi n) witness_env =
    N.interpret_named (pointed_property phi n) env).
  { apply N.interpret_env_agree; exact He. }
  rewrite Eproperty in Hpad, Hpad'.
  destruct (P.native_property_equivalence phi G (pointed_labels n) (n + 5) env
    (fun i => env (pointed_labels n i)) HIR (pointed_labels_range n) ltac:(intro i; reflexivity))
    as [Hsource Hsource'].
  assert (Esource : phi[fun i => env (pointed_labels n i)] = phi[sigma]).
  { eapply bounded_subst; [exact Hb | exact Hslots]. }
  rewrite Esource in Hsource, Hsource'.
  split; eapply P.finite_implication_compose;
    [exact Hpad | exact Hsource | exact Hsource' | exact Hpad'].
Qed.

Definition opened_pointed_body phi (u x w : C.set_term) :=
  (∀ ((C.R u`[↑] $0 → (phi[$0 .: u`[↑] .: x`[↑] .: ↑] → C.R w`[↑] $0)) ∧
      (C.R w`[↑] $0 → phi[$0 .: u`[↑] .: x`[↑] .: ↑]))) ∧
  (phi[x .: u .: x .: var] → C.R w x).

Lemma pointed_body_opened phi u x w :
  ((C.pointed_body phi)[up (up (u..))][up (x..)])[w..] = opened_pointed_body phi u x w.
Proof.
  destruct u as [iu|[]], x as [ix|[]], w as [iw|[]].
  unfold C.pointed_body, opened_pointed_body.
  cbn [subst_form C.R C.terms2 subst_term Vector.map up scons funcomp].
  repeat rewrite subst_comp.
  repeat first
    [ reflexivity
    | match goal with
      | |- ?body[?sigma] = ?body[?tau] => apply subst_ext; intros [|[|[|k]]];
        cbn [C.member_slots C.point_slots up scons funcomp subst_term]; reflexivity
      end
    | f_equal ].
Qed.

Lemma pointed_member_opened phi u x m :
  (phi[$0 .: u`[↑] .: x`[↑] .: ↑])[m..] = phi[m .: u .: x .: var].
Proof.
  rewrite subst_comp; apply subst_ext; intros [|[|[|k]]]; cbn [scons funcomp subst_term];
    try reflexivity; apply subst_term_shift.
Qed.

Lemma fresh_output_agree property env w v :
  N.free_named v property = true ->
  N.update_env env (N.encode_named (V.padded_property 2 3 property)) w v = env v.
Proof.
  intro Hv; unfold N.update_env; destruct (Nat.eqb v
    (N.encode_named (V.padded_property 2 3 property))) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E; subst v; rewrite padded_output_fresh in Hv; discriminate.
Qed.

Lemma fresh_output_member_agree property env w m v :
  N.free_named v property = true ->
  N.update_env (N.update_env env (N.encode_named (V.padded_property 2 3 property)) w) 3 m v =
  N.update_env env 3 m v.
Proof.
  intro Hv.
  change ((if Nat.eqb v 3 then m else
    N.update_env env (N.encode_named (V.padded_property 2 3 property)) w v) =
    (if Nat.eqb v 3 then m else env v)).
  destruct (Nat.eqb v 3); [reflexivity | apply fresh_output_agree; exact Hv].
Qed.

Lemma raw_pointed_witness_readback G phi n u x w : bounded n phi ->
  G ⊢NPt C.ir ->
  G ⊢NPt N.interpret_named
    (pointed_named_matrix (V.padded_property 2 3 (pointed_property phi n)))
    (N.update_env (pointed_environment u x)
      (N.encode_named (V.padded_property 2 3 (pointed_property phi n))) w) ->
  G ⊢NPt opened_pointed_body phi u x w.
Proof.
  intros Hb HIR Hmatrix.
  set (property := pointed_property phi n).
  set (padded := V.padded_property 2 3 property).
  set (c := N.encode_named padded).
  set (env := pointed_environment u x).
  set (out_env := N.update_env env c w).
  destruct (V.padded_property_gate 2 3 property) as [Hc2 Hc3]; fold padded c in Hc2, Hc3.
  change (G ⊢NPt ¬ ((∀ N.interpret_named
    (V.named_and
      (N.NImp (N.NMem 2 3) (N.NImp padded (N.NMem c 3)))
      (N.NImp (N.NMem c 3) padded)) (N.bind_env out_env 3)) →
    ¬ (N.interpret_named padded out_env → C.R (out_env c) (out_env 3)))) in Hmatrix.
  pose proof (R.dual_conjunction_left _ _ _ Hmatrix) as Hall.
  pose proof (R.dual_conjunction_right _ _ _ Hmatrix) as Hpoint.
  assert (Eout : out_env c = w).
  { unfold out_env, N.update_env; now rewrite Nat.eqb_refl. }
  assert (Epoint : out_env 3 = x).
  { unfold out_env, N.update_env; rewrite (proj2 (Nat.eqb_neq 3 c) ltac:(lia)); reflexivity. }
  rewrite Eout, Epoint in Hpoint.
  unfold opened_pointed_body; apply CI.
  - apply AllI_named; intro m.
    cbn [subst_form C.R C.terms2 Vector.map];
      rewrite !subst_term_shift, pointed_member_opened.
    pose proof (AllE m Hall) as Hmember; rewrite N.interpret_binder_instance in Hmember.
    set (member_env := N.update_env out_env 3 m) in *.
    change (G ⊢NPt ¬ ((C.R (member_env 2) (member_env 3) →
      (N.interpret_named padded member_env → C.R (member_env c) (member_env 3))) →
      ¬ (C.R (member_env c) (member_env 3) → N.interpret_named padded member_env))) in Hmember.
    assert (Ein : member_env 2 = u).
    { change ((if Nat.eqb 2 c then w else env 2) = u).
      rewrite (proj2 (Nat.eqb_neq 2 c) ltac:(lia)); reflexivity. }
    assert (Emember : member_env 3 = m).
    { unfold member_env, N.update_env; now rewrite Nat.eqb_refl. }
    assert (Ewitness : member_env c = w).
    { unfold member_env, N.update_env; rewrite (proj2 (Nat.eqb_neq c 3) Hc3); exact Eout. }
    rewrite Ein, Emember, Ewitness in Hmember.
    pose proof (R.dual_conjunction_left _ _ _ Hmember) as Hforward.
    pose proof (R.dual_conjunction_right _ _ _ Hmember) as Hback.
    destruct (padded_property_readback G phi n (N.update_env env 3 m) member_env
      (m .: u .: x .: var) Hb HIR
      ltac:(intros v Hv; apply fresh_output_member_agree; exact Hv)
      ltac:(intros i Hi; apply pointed_member_slots; exact Hi)) as [Hproperty Hproperty'].
    fold property padded in Hproperty, Hproperty'.
    apply CI.
    + apply II, II; eapply IE.
      * eapply IE; [apply P.finite_weaken, P.finite_weaken; exact Hforward|
             apply Ctx; right; now left].
      * eapply IE; [apply P.finite_weaken, P.finite_weaken; exact Hproperty'|
           apply Ctx; now left].
    + apply II; eapply IE; [apply P.finite_weaken; exact Hproperty|].
        eapply IE; [apply P.finite_weaken; exact Hback|apply Ctx; now left].
  - destruct (padded_property_readback G phi n env out_env
      (x .: u .: x .: var) Hb HIR
      ltac:(intros v Hv; apply fresh_output_agree; exact Hv)
      ltac:(intros i Hi; apply pointed_environment_slots; exact Hi)) as [Hproperty Hproperty'].
    fold property padded in Hproperty, Hproperty'.
    apply II; eapply IE; [apply P.finite_weaken; exact Hpoint|].
      eapply IE; [apply P.finite_weaken; exact Hproperty'|apply Ctx; now left].
Qed.

Theorem raw_pointed_readback G phi n u x : bounded n phi -> G ⊢NPt C.ir ->
  G ⊢NPt N.interpret_named
    (V.raw_pointed_named 2 3 (V.padded_property 2 3 (pointed_property phi n)))
    (pointed_environment u x) ->
  G ⊢NPt ∃ ((C.pointed_body phi)[up (up (u..))][up (x..)]).
Proof.
  intros Hb HIR Hraw.
  set (property := V.padded_property 2 3 (pointed_property phi n)).
  set (c := N.encode_named property).
  set (env := pointed_environment u x).
  change (G ⊢NPt ¬ (∀ ¬ N.interpret_named (pointed_named_matrix property)
    (N.bind_env env c))) in Hraw.
  pose proof (R.dual_existential_native _ _ Hraw) as Hex.
  eapply ExE_named; [exact Hex|]; intro w.
  apply (ExI w); rewrite pointed_body_opened.
  apply (raw_pointed_witness_readback
    ((N.interpret_named (pointed_named_matrix property) (N.bind_env env c))[w..] :: G)
    phi n u x w Hb).
  - apply P.finite_weaken; exact HIR.
  - rewrite <- N.interpret_binder_instance; apply Ctx; now left.
Qed.

(** This context contains two formulas, and both have actual closed
    numeric proofs. It is a finite intermediate ND context, not an added
    axiom theory or an assumed source consistency principle. *)
Definition pointed_schema phi n :=
  V.raw_pointed_named 2 3 (V.padded_property 2 3 (pointed_property phi n)).
Definition pointed_readback_context phi n : list C.set_form :=
  [C.ir; V.raw_closed_formula (pointed_schema phi n)].

Lemma pointed_readback_context_closed phi n : forall psi,
  In psi (pointed_readback_context phi n) -> bounded 0 psi.
Proof.
  intros psi [<-|[<-|[]]]; [apply C.ir_closed|apply V.raw_closed_formula_bound].
Qed.

Lemma pointed_schema_instance G phi n env :
  G ⊢NPt V.raw_closed_formula (pointed_schema phi n) ->
  G ⊢NPt N.interpret_named (pointed_schema phi n) env.
Proof.
  intro Hclosed; set (schema := pointed_schema phi n).
  set (k := S (N.encode_named schema)).
  assert (Hb : bounded k (N.interpret_named schema
    NativeReadback238.NativeReadback238.identity_terms)).
  { apply T.named_interpret_bounded; intros v Hv; constructor.
    pose proof (N.encode_named_names_bound schema v (N.free_named_in_names v schema Hv)).
    unfold k; lia. }
  change (G ⊢NPt forall_times k (N.interpret_named schema
    NativeReadback238.NativeReadback238.identity_terms)) in Hclosed.
  pose proof (@subst_forall_prv sig_empty ZF_pred_sig falsity_on class
    (N.interpret_named schema NativeReadback238.NativeReadback238.identity_terms)
    k G Hclosed Hb env) as Hinstance.
  rewrite N.interpret_substitution in Hinstance.
  change (G ⊢NPt N.interpret_named schema env) in Hinstance; exact Hinstance.
Qed.

Theorem finite_pointed_readback phi n : bounded n phi ->
  pointed_readback_context phi n ⊢NPt C.pointed_ax phi.
Proof.
  intro Hb; unfold C.pointed_ax; apply AllI_named; intro u; apply AllI_named; intro x.
  change (pointed_readback_context phi n ⊢NPt
    ∃ ((C.pointed_body phi)[up (up (u..))][up (x..)])).
  apply (raw_pointed_readback (pointed_readback_context phi n) phi n u x Hb).
  - apply Ctx; now left.
  - apply pointed_schema_instance, Ctx; right; now left.
Qed.

Lemma finite_closed_forall_times G phi m :
  (forall psi, In psi G -> bounded 0 psi) -> G ⊢NPt phi ->
  G ⊢NPt forall_times m phi.
Proof.
  intros HG Hphi; induction m as [|m IH]; [exact Hphi|].
  change (G ⊢NPt ∀ forall_times m phi).
  apply AllI; rewrite C.closed_context_shift by exact HG; exact IH.
Qed.

Lemma pointed_readback_context_numeric phi n lo : 0 < lo -> forall psi,
  In psi (pointed_readback_context phi n) ->
  Compiler238.derivable (T.native_code psi (fun _ => 0) lo).
Proof.
  intros Hlo psi [<-|[<-|[]]].
  - apply V.native_ir_numeric; exact Hlo.
  - apply V.raw_closed_native_supplier; [exact Hlo|].
    unfold pointed_schema; apply V.raw_pointed_named_proof;
      destruct (V.padded_property_gate 2 3 (pointed_property phi n)); assumption.
Qed.

(** The IR used in finite_pointed_readback is discharged here with an
    explicit numeric_I/Gen proof. The raw R9 context formula is discharged
    with its actual derives_bundle proof and actual closing Gen steps. *)
Theorem native_pointed_numeric phi m lo : 0 < lo ->
  Compiler238.derivable
    (T.native_code (forall_times m (C.pointed_ax phi)) (fun _ => 0) lo).
Proof.
  intro Hlo; destruct (find_bounded phi) as [n Hb].
  apply (D.native_numeric_closed (pointed_readback_context phi n)
    (forall_times m (C.pointed_ax phi)) (fun _ => 0) lo Hlo ltac:(intro i; exact Hlo)).
  - apply pointed_readback_context_numeric; exact Hlo.
  - apply finite_closed_forall_times; [apply pointed_readback_context_closed|].
    apply finite_pointed_readback; exact Hb.
Qed.

Theorem native_pointed_equality_numeric psi lo :
  PointedSchemas238.PointedSchemas238.pointed_equality_theory psi -> 0 < lo ->
  Compiler238.derivable (T.native_code psi (fun _ => 0) lo).
Proof.
  intros [phi Hphi|phi m Hclosed] Hlo.
  - apply V.native_equality_base; exact Hphi.
  - apply native_pointed_numeric; exact Hlo.
Qed.

(** This inhabits the existing restricted finite proof interface. There
    is no model premise and no compiler supplier in its hypotheses. *)
Theorem compact_numeric_reverse : N.compact_numeric_reverse_transport.
Proof.
  intros G HG Hfalse.
  change (Compiler238.derivable (T.native_code ⊥ (fun _ => 0) 1)).
  assert (Hone : 0 < 1) by exact (Nat.lt_0_succ 0).
  assert (Henv : forall i : nat, (fun _ : nat => 0) i < 1).
  { intro i; exact Hone. }
  apply (D.native_numeric_closed G ⊥ (fun _ : nat => 0) 1 Hone Henv).
  - intros phi Hphi; apply native_pointed_equality_numeric;
      [apply HG; exact Hphi|exact Hone].
  - exact Hfalse.
Qed.

Corollary S0_numeric_refutation :
  C.derivable PAinCompact238.PAinCompact238.finite_set_S0 ⊥ ->
  Compiler238.derivable 1.
Proof.
  intro Hfalse.
  destruct (S0InCompact238.S0InCompact238.S0_to_pointed_equality ⊥ Hfalse)
    as [G [HG Hproof]].
  exact (compact_numeric_reverse G HG Hproof).
Qed.

Print Assumptions S0_numeric_refutation.
Print Assumptions pointed_schema_instance.
Print Assumptions finite_pointed_readback.
Print Assumptions pointed_readback_context_numeric.
Print Assumptions native_pointed_numeric.
Print Assumptions native_pointed_equality_numeric.
Print Assumptions compact_numeric_reverse.
Print Assumptions raw_pointed_witness_readback.
Print Assumptions raw_pointed_readback.
Print Assumptions pointed_labels_range.
Print Assumptions padded_output_fresh.
Print Assumptions padded_property_readback.
Print Assumptions pointed_body_opened.
Print Assumptions pointed_member_opened.
End NativePointed238.
