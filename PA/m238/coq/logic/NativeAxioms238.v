(** Original finite equality readback for the PA238 forward bridge.
    Every closed ordinary equality axiom below has an actual numeric proof
    assembled from the accepted equality rules and actual generalization.
    Pointed schema readback remains a separate constructive obligation. *)
From Coq Require Import Arith List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.logic Require Import Codes238 Compiler238 NumericSyntax238
  NumericHilbert238 NumericNamed238 NumericSound238 NativeNamed238 NativeND238 NativeReadback238.
From P238.arith Require Import Compact238 PointedSchemas238.
Import ListNotations FullSyntax BinSig ZFSignature.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module NativeAxioms238.
Module C := Compact238.Compact238.
Module N := NumericSyntax238.NumericSyntax238.
Module H := NumericHilbert238.NumericHilbert238.
Module T := NativeNamed238.NativeNamed238.
Module D := NativeND238.NativeND238.

Theorem native_equality_base phi rho lo : In phi C.equality_base ->
  Compiler238.derivable (T.native_code phi rho lo).
Proof.
  intros [<-|[<-|[<-|[<-|[]]]]].
  - change (Compiler238.derivable (wal lo (weq lo lo))).
    exact (Compiler238.derives_all lo _ (H.numeric_equality_reflexive lo)).
  - change (Compiler238.derivable
      (wal lo (wal (S lo) (wim (weq lo (S lo)) (weq (S lo) lo))))).
    exact (Compiler238.derives_all lo _
      (Compiler238.derives_all (S lo) _ (H.numeric_equality_symmetry lo (S lo)))).
  - change (Compiler238.derivable
      (wal lo (wal (S lo) (wal (S (S lo))
        (wim (weq lo (S lo)) (wim (weq (S lo) (S (S lo))) (weq lo (S (S lo))))))))).
    exact (Compiler238.derives_all lo _ (Compiler238.derives_all (S lo) _
      (Compiler238.derives_all (S (S lo)) _ (H.numeric_equality_transitive lo (S lo) (S (S lo)))))).
  - change (Compiler238.derivable
      (wal lo (wal (S lo) (wal (S (S lo)) (wal (S (S (S lo)))
        (wim (weq lo (S (S lo))) (wim (weq (S lo) (S (S (S lo))))
          (wim (wel (S lo) lo) (wel (S (S (S lo))) (S (S lo))))))))))).
    apply Compiler238.derives_all, Compiler238.derives_all,
      Compiler238.derives_all, Compiler238.derives_all.
    apply H.numeric_context_empty, H.numeric_deduction,
      H.numeric_deduction, H.numeric_deduction.
    apply H.numeric_context_membership_congruence with (a := S lo) (b := lo).
    + apply H.numeric_assumption; right; now left.
    + apply H.numeric_assumption; right; right; now left.
    + apply H.numeric_assumption; now left.
Qed.

Definition named_and (phi psi : N.named_formula) := N.NNot (N.NImp phi (N.NNot psi)).
Definition named_exists a (phi : N.named_formula) := N.NNot (N.NAll a (N.NNot phi)).

Definition raw_pointed_named a b phi :=
  let c := N.encode_named phi in
  named_exists c
    (named_and
      (N.NAll b
        (named_and
          (N.NImp (N.NMem a b) (N.NImp phi (N.NMem c b)))
          (N.NImp (N.NMem c b) phi)))
      (N.NImp phi (N.NMem c b))).

(** Match the exact raw constructor tree symbolically. Eager arithmetic
    reduction of its nested bundle is unnecessary for this finite proof. *)
Local Opaque P unP triangle wim wal wel weq.
Theorem raw_pointed_named_proof a b phi : N.encode_named phi <> a -> N.encode_named phi <> b ->
  Compiler238.derivable (N.encode_named (raw_pointed_named a b phi)).
Proof.
  intros Hca Hcb; apply H.numeric_context_empty.
  unfold raw_pointed_named, named_exists, named_and.
  cbn [N.encode_named].
  apply H.numeric_conjunction_left with
    (b := wa (wim (weq a b) (wal (N.encode_named phi) (weq a b)))
             (wim (wel a b) (wal (N.encode_named phi) (wel a b)))).
  apply H.numeric_theorem; exact (Compiler238.derives_bundle a b (N.encode_named phi) Hca Hcb).
Qed.
Local Transparent P unP triangle wim wal wel weq.

Theorem raw_pointed_freshened_proof a b phi : N.encode_named phi <> a -> N.encode_named phi <> b ->
  Compiler238.derivable
    (N.encode_named (T.freshen_named (raw_pointed_named a b phi)
      (S (N.encode_named (raw_pointed_named a b phi))))).
Proof.
  intros Hca Hcb.
  destruct (T.encoded_named_freshening (raw_pointed_named a b phi)) as [Halpha _].
  exact (Compiler238.derives_mp (N.encode_named (raw_pointed_named a b phi)) _
    (raw_pointed_named_proof a b phi Hca Hcb) Halpha).
Qed.

Lemma term_label_minimum rho t : (forall i, 2 <= rho i) -> 2 <= T.term_label rho t.
Proof. destruct t as [i|[]]; intro H; apply H. Qed.

(** The raw gate compares constructor codes with 2 and 3. Keep Cantor
    pairing symbolic and use its proved lower bound for the two cases
    whose own residue can equal a gate value at the zero pair. *)
Local Opaque P unP triangle.
Lemma membership_gate_codes a b : wel a b <> 2 /\ wel a b <> 3.
Proof. unfold wel; split; lia. Qed.
Lemma implication_gate_codes a b : wim a b <> 2 /\ wim a b <> 3.
Proof. unfold wim; split; lia. Qed.
Lemma equality_gate_codes a b : 2 <= a -> weq a b <> 2 /\ weq a b <> 3.
Proof.
  intro Hmin; pose proof (P_bounds a b) as [Ha Hb]; unfold weq; split; lia.
Qed.
Lemma universal_gate_codes a b : 0 < a -> wal a b <> 2 /\ wal a b <> 3.
Proof.
  intro Hpos; pose proof (P_bounds a b) as [Ha Hb]; unfold wal; split; lia.
Qed.
Local Transparent P unP triangle.

Theorem native_property_gate phi rho fresh : 0 < fresh -> (forall i, 2 <= rho i) ->
  T.native_code phi rho fresh <> 2 /\ T.native_code phi rho fresh <> 3.
Proof.
  intros Hfresh Hr; induction phi as [|p ts|op phi IHphi psi IHpsi|op phi IH]
    using form_ind_falsity.
  - change (wel 0 0 <> 2 /\ wel 0 0 <> 3); apply membership_gate_codes.
  - destruct p.
    + change (wel (T.term_label rho (Vector.hd (Vector.tl ts)))
        (T.term_label rho (Vector.hd ts)) <> 2 /\
        wel (T.term_label rho (Vector.hd (Vector.tl ts)))
        (T.term_label rho (Vector.hd ts)) <> 3).
      apply membership_gate_codes.
    + change (weq (T.term_label rho (Vector.hd ts))
        (T.term_label rho (Vector.hd (Vector.tl ts))) <> 2 /\
        weq (T.term_label rho (Vector.hd ts))
        (T.term_label rho (Vector.hd (Vector.tl ts))) <> 3).
      apply equality_gate_codes, term_label_minimum; exact Hr.
  - destruct op; cbn [T.native_code T.native_named N.encode_named];
      unfold wn; apply implication_gate_codes.
  - destruct op; cbn [T.native_code T.native_named N.encode_named].
    + apply universal_gate_codes; exact Hfresh.
    + unfold wn; apply implication_gate_codes.
Qed.

Theorem native_raw_pointed_supplier phi rho fresh :
  0 < fresh -> (forall i, 2 <= rho i) ->
  Compiler238.derivable
    (N.encode_named (T.freshen_named
      (raw_pointed_named 2 3 (T.native_named phi rho fresh))
      (S (N.encode_named (raw_pointed_named 2 3 (T.native_named phi rho fresh)))))).
Proof.
  intros Hfresh Hr; apply raw_pointed_freshened_proof;
    destruct (native_property_gate phi rho fresh Hfresh Hr) as [H2 H3]; assumption.
Qed.

Definition property_padding_label a b phi := S (a + b + N.encode_named phi).
Definition padded_property a b phi := N.NAll (property_padding_label a b phi) phi.

Lemma padded_property_gate a b phi :
  N.encode_named (padded_property a b phi) <> a /\
  N.encode_named (padded_property a b phi) <> b.
Proof.
  set (q := property_padding_label a b phi).
  assert (Hq : q < N.encode_named (padded_property a b phi)).
  { apply N.encode_named_names_bound.
    unfold padded_property; fold q; cbn [N.names_named]; now rewrite Nat.eqb_refl. }
  unfold q, property_padding_label in Hq; split; lia.
Qed.

Lemma padding_label_fresh a b phi :
  N.names_named (property_padding_label a b phi) phi = false.
Proof.
  destruct (N.names_named (property_padding_label a b phi) phi) eqn:E; [|reflexivity].
  pose proof (N.encode_named_names_bound phi (property_padding_label a b phi) E).
  unfold property_padding_label in *; lia.
Qed.

Theorem padded_raw_pointed_supplier a b phi :
  Compiler238.derivable
    (N.encode_named (T.freshen_named
      (raw_pointed_named a b (padded_property a b phi))
      (S (N.encode_named (raw_pointed_named a b (padded_property a b phi)))))).
Proof.
  destruct (padded_property_gate a b phi) as [Ha Hb].
  apply raw_pointed_freshened_proof; assumption.
Qed.

Theorem padded_property_equivalent a b phi :
  Compiler238.derivable (wim (N.encode_named phi) (N.encode_named (padded_property a b phi))) /\
  Compiler238.derivable (wim (N.encode_named (padded_property a b phi)) (N.encode_named phi)).
Proof.
  set (q := property_padding_label a b phi).
  assert (Hq : N.names_named q phi = false) by (apply padding_label_fresh).
  assert (Hnext : N.names_named (S q) phi = false).
  { destruct (N.names_named (S q) phi) eqn:E; [|reflexivity].
    pose proof (N.encode_named_names_bound phi (S q) E).
    unfold q, property_padding_label in *; lia. }
  split.
  - apply NumericNamed238.NumericNamed238.named_vacuity.
    + apply NumericNamed238.NumericNamed238.named_names_free; exact Hq.
    + apply NumericNamed238.NumericNamed238.named_names_binders; exact Hq.
  - pose proof (NumericNamed238.NumericNamed238.named_universal_instance q (S q) phi ltac:(lia)
      (NumericNamed238.NumericNamed238.named_names_binders q phi Hq)
      (NumericNamed238.NumericNamed238.named_names_binders (S q) phi Hnext)) as Hinst.
    rewrite NumericNamed238.NumericNamed238.replace_named_unchanged in Hinst by exact Hq.
    exact Hinst.
Qed.

(** Padding is removed by an actual ordinary finite ND proof. This
    step needs no IR: the arithmetic name bound makes its binder vacuous. *)
Theorem padded_property_native G a b phi env :
  @prv sig_empty ZF_pred_sig falsity_on class G
    (N.interpret_named (padded_property a b phi) env → N.interpret_named phi env) /\
  @prv sig_empty ZF_pred_sig falsity_on class G
    (N.interpret_named phi env → N.interpret_named (padded_property a b phi) env).
Proof.
  unfold padded_property; cbn [N.interpret_named].
  rewrite (NumericSound238.NumericSound238.fresh_binder_shift phi env
    (property_padding_label a b phi)).
  - split.
    + apply II.
      assert (Hall : @prv sig_empty ZF_pred_sig falsity_on class
        ((∀ (N.interpret_named phi env)[↑]) :: G) (∀ (N.interpret_named phi env)[↑])).
      { apply Ctx; now left. }
      pose proof (AllE $0 Hall) as Hinst; rewrite subst_shift in Hinst; exact Hinst.
    + apply C.fresh_vacuity.
  - apply NumericNamed238.NumericNamed238.named_names_free, padding_label_fresh.
Qed.

Definition bounded_identity fresh : T.label_env :=
  fun i => if Nat.ltb i fresh then i else 0.

Lemma bounded_identity_range fresh : 0 < fresh -> forall i, bounded_identity fresh i < fresh.
Proof.
  intros Hpos i; unfold bounded_identity; destruct (Nat.ltb i fresh) eqn:E;
    [now apply Nat.ltb_lt|lia].
Qed.

Lemma bounded_identity_names phi fresh :
  (forall v, N.names_named v phi = true -> v < fresh) ->
  forall v, N.names_named v phi = true -> bounded_identity fresh v = v.
Proof.
  intros Hb v Hv; unfold bounded_identity; rewrite (proj2 (Nat.ltb_lt v fresh) (Hb v Hv)); reflexivity.
Qed.

Definition raw_native_budget phi := S (N.encode_named (T.freshen_named phi (S (N.encode_named phi)))).

Theorem raw_named_native_supplier phi : Compiler238.derivable (N.encode_named phi) ->
  Compiler238.derivable
    (T.native_code (N.interpret_named phi NativeReadback238.NativeReadback238.identity_terms)
      (bounded_identity (raw_native_budget phi)) (raw_native_budget phi)).
Proof.
  intro Hraw; set (q := T.freshen_named phi (S (N.encode_named phi))).
  set (fresh := raw_native_budget phi).
  assert (Hpos : 0 < fresh) by (unfold fresh, raw_native_budget; lia).
  assert (Hb : forall v, N.names_named v q = true -> v < fresh).
  { intros v Hv; pose proof (N.encode_named_names_bound q v Hv).
    unfold fresh, raw_native_budget; fold q; lia. }
  destruct (NativeReadback238.NativeReadback238.native_interpret_readback q
    (bounded_identity fresh) fresh (T.freshen_named_distinct phi _)
    Hpos Hb (bounded_identity_range fresh Hpos) (bounded_identity_names q fresh Hb)) as [Hread _].
  destruct (T.encoded_named_freshening phi) as [Halpha _].
  pose proof (Compiler238.derives_mp (N.encode_named phi) (N.encode_named q) Hraw Halpha) as Hq.
  pose proof (Compiler238.derives_mp (N.encode_named q) _ Hq Hread) as Hnative.
  assert (Ephi : N.interpret_named q NativeReadback238.NativeReadback238.identity_terms =
                N.interpret_named phi NativeReadback238.NativeReadback238.identity_terms).
  { unfold q; apply T.freshen_named_interpret.
    intros v Hv; pose proof (N.encode_named_names_bound phi v Hv); lia. }
  rewrite Ephi in Hnative; exact Hnative.
Qed.

Theorem padded_raw_native_supplier a b phi :
  Compiler238.derivable
    (T.native_code
      (N.interpret_named (raw_pointed_named a b (padded_property a b phi))
        NativeReadback238.NativeReadback238.identity_terms)
      (bounded_identity (raw_native_budget (raw_pointed_named a b (padded_property a b phi))))
      (raw_native_budget (raw_pointed_named a b (padded_property a b phi)))).
Proof.
  apply raw_named_native_supplier, raw_pointed_named_proof;
    destruct (padded_property_gate a b phi); assumption.
Qed.

(** This is an actual derived numeric logical supplier. It is never an
    assumption of the pointed/equality producer: R8 identity at code 1
    and actual generalization construct its complete proof. *)
Theorem native_ir_numeric rho lo : 0 < lo ->
  Compiler238.derivable (T.native_code C.ir rho lo).
Proof.
  intro Hpos; set (phi := N.NAll 0 (N.NNot (N.NMem 0 0))).
  assert (Hd : T.distinct_named_binders phi) by (split; [reflexivity|exact I]).
  assert (Hname : forall v, N.names_named v phi = true -> v = 0).
  { intros v Hv; unfold phi in Hv; cbn [N.names_named] in Hv.
    rewrite !Bool.orb_diag in Hv; now apply Nat.eqb_eq. }
  assert (Hb : forall v, N.names_named v phi = true -> v < lo).
  { intros v Hv; rewrite (Hname v Hv); exact Hpos. }
  assert (Hr : forall i, (fun _ : nat => 0) i < lo) by (intro i; exact Hpos).
  assert (Hi : forall v, N.names_named v phi = true -> (fun _ : nat => 0) v = v).
  { intros v Hv; now rewrite (Hname v Hv). }
  destruct (NativeReadback238.NativeReadback238.native_interpret_readback phi
    (fun _ => 0) lo Hd Hpos Hb Hr Hi) as [Hread _].
  assert (Hraw : Compiler238.derivable (N.encode_named phi)).
  { exact (Compiler238.derives_all 0 (wn 1) (H.numeric_I 1)). }
  pose proof (Compiler238.derives_mp (N.encode_named phi) _ Hraw Hread) as Hnative.
  change (Compiler238.derivable (wal lo (wn (wel lo lo)))) in Hnative.
  exact Hnative.
Qed.

(** The raw named theorem is closed by actual numeric Gen constructors.
    Its ordinary universal closure has a syntactic bound and can therefore
    be relocated to the common finite-ND allocation budget. *)
Definition raw_closed_formula phi :=
  forall_times (S (N.encode_named phi))
    (N.interpret_named phi NativeReadback238.NativeReadback238.identity_terms).

Lemma raw_closed_formula_bound phi : bounded 0 (raw_closed_formula phi).
Proof. apply T.named_closed_bound. Qed.

Theorem raw_closed_native_supplier phi lo : 0 < lo ->
  Compiler238.derivable (N.encode_named phi) ->
  Compiler238.derivable (T.native_code (raw_closed_formula phi) (fun _ => 0) lo).
Proof.
  intros Hlo Hraw; set (n := S (N.encode_named phi)).
  pose proof (raw_named_native_supplier (T.close_named n phi)
    (T.close_named_numeric n phi Hraw)) as Hclosed.
  assert (Hfree : forall v, N.free_named v phi = true -> v < n).
  { intros v Hv; pose proof (N.encode_named_names_bound phi v
      (N.free_named_in_names v phi Hv)); unfold n; lia. }
  rewrite (T.close_named_exact n phi Hfree
    NativeReadback238.NativeReadback238.identity_terms) in Hclosed.
  change (Compiler238.derivable (T.native_code (raw_closed_formula phi)
    (bounded_identity (raw_native_budget (T.close_named n phi)))
    (raw_native_budget (T.close_named n phi)))) in Hclosed.
  exact (T.native_closed_numeric_relocate (raw_closed_formula phi)
    (bounded_identity (raw_native_budget (T.close_named n phi)))
    (raw_native_budget (T.close_named n phi)) lo (raw_closed_formula_bound phi)
    ltac:(unfold raw_native_budget; lia) Hlo Hclosed).
Qed.

Print Assumptions raw_closed_formula_bound.
Print Assumptions raw_closed_native_supplier.
Print Assumptions native_equality_base.
Print Assumptions raw_pointed_named_proof.
Print Assumptions raw_pointed_freshened_proof.
Print Assumptions native_property_gate.
Print Assumptions native_raw_pointed_supplier.
Print Assumptions padded_property_gate.
Print Assumptions padded_raw_pointed_supplier.
Print Assumptions padded_property_equivalent.
Print Assumptions padded_property_native.
Print Assumptions raw_named_native_supplier.
Print Assumptions padded_raw_native_supplier.
Print Assumptions native_ir_numeric.
End NativeAxioms238.
