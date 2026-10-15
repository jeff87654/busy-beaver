(* Original finite ordinary-PA prerequisites for forward power traces.
   The zero trace is witnessed by b=c=1 and quotient zero.  Its bounded
   step clause is discharged by the actual zero-minimality certificate.
   No sequence-coding, CRT, or power-totality sentence is assumed. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238
  PAAddition238 PAOrderBounds238 PAQuotient238 PAOrderGrowth238
  PABetaUnique238 CompactInPA238 PAPowerTrace238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAQuotient238
  PAOrderGrowth238 CompactInPA238 PAPowerTrace238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAPowerExtension238.

Definition zero_minimal_sentence : pa_form := ∀ ¬ ($0 ⧀ zero).
Definition extension_context : list pa_form :=
  List.cons zero_minimal_sentence trace_context.
Definition has_extension_context (G : list pa_form) : Prop :=
  forall phi, List.In phi extension_context -> List.In phi G.

Lemma extension_proof phi : extension_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := zero_minimal_sentence).
  - apply trace_proof, II. exact HD.
  - exact PAOrder238.zero_minimal.
Qed.
Lemma extension_context_self : has_extension_context extension_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_extension_cons G phi : has_extension_context G ->
  has_extension_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma extension_has_trace G : has_extension_context G -> has_trace_context G.
Proof. intros HG phi Hphi. apply HG. unfold extension_context. now right. Qed.
Lemma extension_has_quotient G : has_extension_context G -> has_quotient_context G.
Proof. intros HG. apply trace_has_quotient, extension_has_trace. exact HG. Qed.
Lemma extension_has_equality G : has_extension_context G -> has_equality G.
Proof. intros HG. apply quotient_has_equality, extension_has_quotient. exact HG. Qed.

Definition beta_witness (b c i r q : pa_term) : pa_form :=
  (b == quotient_row q (beta_modulus c i) r) ∧ (r ⧀ beta_modulus c i).
Lemma beta_witness_subst b c i r q rho :
  (beta_witness b c i r q)[rho] =
  beta_witness b`[rho] c`[rho] i`[rho] r`[rho] q`[rho].
Proof.
  unfold beta_witness. change
    (((b`[rho] == (quotient_row q (beta_modulus c i) r)`[rho]) ∧
      (PAlt r (beta_modulus c i))[rho]) =
     ((b`[rho] == quotient_row q`[rho]
         (beta_modulus c`[rho] i`[rho]) r`[rho]) ∧
       (r`[rho] ⧀ beta_modulus c`[rho] i`[rho]))).
  rewrite PAlt_subst, quotient_row_subst, beta_modulus_subst. reflexivity.
Qed.
Lemma beta_exists_witness b c i r :
  beta b c i r = ∃ beta_witness b`[↑] c`[↑] i`[↑] r`[↑] $0.
Proof. reflexivity. Qed.

(* A genuine beta introduction rule, with the arithmetic quotient retained. *)
Lemma beta_introduce G b c i r q :
  G ⊢C (b == quotient_row q (beta_modulus c i) r) ->
  G ⊢C (r ⧀ beta_modulus c i) -> G ⊢C beta b c i r.
Proof.
  intros HQ HR. rewrite beta_exists_witness. apply (ExI q).
  rewrite beta_witness_subst, !subst_term_shift.
  change (G ⊢C ((b == quotient_row q (beta_modulus c i) r) ∧
    (r ⧀ beta_modulus c i))).
  apply CI; assumption.
Qed.

Lemma one_product G : has_quotient_context G ->
  G ⊢C (σ zero ⊗ σ zero == σ zero).
Proof.
  intros HG. pose proof (quotient_has_equality G HG) as HE.
  pose proof (mult_rec_instance G zero (σ zero)
    (HG ax_mult_rec quotient_mult_rec)) as HR.
  pose proof (mult_zero_instance G (σ zero)
    (HG ax_mult_zero quotient_mult_zero)) as HZ.
  pose proof (reflexivity_instance G (σ zero) HE) as HO.
  pose proof (IE (IE (addition_instance G (σ zero) (σ zero)
    (zero ⊗ σ zero) zero HE) HO) HZ) as HA.
  pose proof (right_zero_at G (σ zero) HG) as HB.
  pose proof (equality_transitivity G (σ zero ⊗ σ zero)
    (σ zero ⊕ (zero ⊗ σ zero)) (σ zero ⊕ zero) HE HR HA) as HF.
  exact (equality_transitivity G (σ zero ⊗ σ zero)
    (σ zero ⊕ zero) (σ zero) HE HF HB).
Qed.

Lemma beta_one_at_zero G : has_quotient_context G ->
  G ⊢C beta (σ zero) (σ zero) zero (σ zero).
Proof.
  intros HG. pose proof (quotient_has_equality G HG) as HE.
  set (m := beta_modulus (σ zero) zero).
  pose proof (one_product G HG) as HP.
  pose proof (IE (successor_instance G (σ zero ⊗ σ zero) (σ zero) HE) HP) as HM.
  change (G ⊢C (m == σ (σ zero))) in HM.
  pose proof (row_zero G m (σ zero) HG) as HQ.
  pose proof (equality_symmetry G (quotient_row zero m (σ zero)) (σ zero) HE HQ) as HQR.
  pose proof (right_zero_at G (σ (σ zero)) HG) as HZ.
  pose proof (equality_symmetry G (σ (σ zero) ⊕ zero) (σ (σ zero)) HE HZ) as HZR.
  pose proof (equality_transitivity G m (σ (σ zero))
    (σ (σ zero) ⊕ zero) HE HM HZR) as HB.
  apply (beta_introduce G (σ zero) (σ zero) zero (σ zero) zero).
  - exact HQR.
  - apply (PAOrderBounds238.strict_order_witness G (σ zero) m zero). exact HB.
Qed.

Lemma zero_trace_steps G b c : has_extension_context G ->
  G ⊢C trace_steps b c zero.
Proof.
  intros HG. apply trace_steps_introduce. intros i. apply II.
  set (D := List.cons (i ⧀ zero) G).
  change (D ⊢C doubling_step b c i).
  assert (HH : D ⊢C zero_minimal_sentence).
  { apply Ctx. unfold D. right. apply HG. unfold extension_context. now left. }
  pose proof (AllE i HH) as HK.
  change (D ⊢C ¬ ((PAlt $0 zero)[i..])) in HK.
  rewrite PAlt_subst in HK. change (D ⊢C ¬ (i ⧀ zero)) in HK.
  apply Exp. eapply IE; [exact HK|]. apply Ctx. unfold D. now left.
Qed.

Theorem pow2_zero_one : paeq_derivable (pow2 zero (σ zero)).
Proof.
  apply extension_proof.
  apply (pow2_introduce extension_context (σ zero) (σ zero) zero (σ zero)).
  unfold trace_body. apply CI.
  - apply beta_one_at_zero, extension_has_quotient. exact extension_context_self.
  - apply CI.
    + apply beta_one_at_zero, extension_has_quotient. exact extension_context_self.
    + apply zero_trace_steps. exact extension_context_self.
Qed.

Definition append_context : list pa_form :=
  List.cons ax_succ_inj extension_context.
Lemma append_proof phi : append_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := ax_succ_inj).
  - apply extension_proof, II. exact HD.
  - apply paeq_axiom, PAeq_inj.
Qed.
Lemma append_has_extension : has_extension_context append_context.
Proof. intros phi Hphi. unfold append_context. now right. Qed.
Lemma append_has_injective : List.In ax_succ_inj append_context.
Proof. unfold append_context. now left. Qed.

Lemma successor_order_covariance G i n : has_quotient_context G ->
  G ⊢C (i ⧀ n) -> G ⊢C (σ i ⧀ σ n).
Proof.
  intros HG HI. unfold PAlt in HI. eapply ExE_named; [exact HI|]. intros k.
  change ((List.cons (n`[↑]`[k..] == σ i`[↑]`[k..] ⊕ k) G) ⊢C
    (σ i ⧀ σ n)).
  rewrite !subst_term_shift.
  set (D := List.cons (n == σ i ⊕ k) G).
  change (D ⊢C (σ i ⧀ σ n)).
  assert (HD : has_quotient_context D).
  { unfold D. apply has_quotient_cons. exact HG. }
  pose proof (quotient_has_equality D HD) as HE.
  assert (HN : D ⊢C (n == σ i ⊕ k)).
  { apply Ctx. unfold D. now left. }
  pose proof (IE (successor_instance D n (σ i ⊕ k) HE) HN) as HS.
  pose proof (PAOrder238.add_rec_instance D (σ i) k
    (HD ax_add_rec quotient_add_rec)) as HR.
  pose proof (equality_symmetry D (σ (σ i) ⊕ k)
    (σ (σ i ⊕ k)) HE HR) as HB.
  apply (PAOrderBounds238.strict_order_witness D (σ i) (σ n) k).
  exact (equality_transitivity D (σ n) (σ (σ i ⊕ k))
    (σ (σ i) ⊕ k) HE HS HB).
Qed.

(* Split the actual difference witness.  Its zero case is the new last
   position; a successor difference remains in the old strict prefix. *)
Lemma strict_successor_split G i n : has_quotient_context G ->
  List.In ax_succ_inj G -> G ⊢C (i ⧀ σ n) ->
  G ⊢C ((i ⧀ n) ∨ (i == n)).
Proof.
  intros HG Hinj HI. unfold PAlt in HI. eapply ExE_named; [exact HI|]. intros k.
  change ((List.cons ((σ n)`[↑]`[k..] == σ i`[↑]`[k..] ⊕ k) G) ⊢C
    ((i ⧀ n) ∨ (i == n))).
  rewrite !subst_term_shift.
  set (D := List.cons (σ n == σ i ⊕ k) G).
  change (D ⊢C ((i ⧀ n) ∨ (i == n))).
  assert (HD : has_quotient_context D).
  { unfold D. apply has_quotient_cons. exact HG. }
  pose proof (quotient_has_equality D HD) as HE.
  assert (HI' : D ⊢C (σ n == σ i ⊕ k)).
  { apply Ctx. unfold D. now left. }
  pose proof (PAOrder238.add_rec_instance D i k
    (HD ax_add_rec quotient_add_rec)) as HR.
  pose proof (equality_transitivity D (σ n) (σ i ⊕ k)
    (σ (i ⊕ k)) HE HI' HR) as HS.
  assert (Hinj' : List.In ax_succ_inj D) by (unfold D; now right).
  pose proof (IE (PAOrder238.succ_inj_instance D n (i ⊕ k) Hinj') HS) as HN.
  assert (Hpred : D ⊢C predecessor_sentence).
  { apply Ctx, HD. unfold quotient_context. apply List.in_app_iff. left.
    right. right. right. now left. }
  pose proof (AllE k Hpred) as HK.
  change (D ⊢C ((k == zero) ∨ ∃ (k`[↑] == σ $0))) in HK.
  eapply DE; [exact HK| |].
  - set (E := List.cons (k == zero) D).
    change (E ⊢C ((i ⧀ n) ∨ (i == n))). apply DI2.
    assert (HEG : has_quotient_context E).
    { unfold E. apply has_quotient_cons. exact HD. }
    pose proof (quotient_has_equality E HEG) as HEE.
    assert (HZ : E ⊢C (k == zero)).
    { apply Ctx. unfold E. now left. }
    pose proof (reflexivity_instance E i HEE) as HIref.
    pose proof (IE (IE (addition_instance E i i k zero HEE) HIref) HZ) as HA.
    pose proof (right_zero_at E i HEG) as HZr.
    pose proof (equality_transitivity E (i ⊕ k) (i ⊕ zero) i HEE HA HZr) as HB.
    pose proof (weaken_head D (n == i ⊕ k) (k == zero) HN) as HNE.
    pose proof (equality_transitivity E n (i ⊕ k) i HEE HNE HB) as HNI.
    exact (equality_symmetry E n i HEE HNI).
  - set (E := List.cons (∃ (k`[↑] == σ $0)) D).
    change (E ⊢C ((i ⧀ n) ∨ (i == n))).
    assert (HX : E ⊢C ∃ (k`[↑] == σ $0)).
    { apply Ctx. unfold E. now left. }
    eapply ExE_named; [exact HX|]. intros d.
    change ((List.cons (k`[↑]`[d..] == σ d) E) ⊢C ((i ⧀ n) ∨ (i == n))).
    rewrite (@subst_term_shift PA_funcs_signature k d).
    set (F := List.cons (k == σ d) E).
    change (F ⊢C ((i ⧀ n) ∨ (i == n))). apply DI1.
    assert (HF : has_quotient_context F).
    { unfold F, E. apply has_quotient_cons, has_quotient_cons. exact HD. }
    pose proof (quotient_has_equality F HF) as HEF.
    assert (HKd : F ⊢C (k == σ d)).
    { apply Ctx. unfold F. now left. }
    pose proof (reflexivity_instance F i HEF) as HIref.
    pose proof (IE (IE (addition_instance F i i k (σ d) HEF) HIref) HKd) as HA.
    pose proof (PAOrderBounds238.right_successor_instance F i d
      (HF PAOrderBounds238.right_successor_sentence quotient_right_successor)) as Hrs.
    pose proof (PAOrder238.add_rec_instance F i d
      (HF ax_add_rec quotient_add_rec)) as Hls.
    pose proof (equality_symmetry F (σ i ⊕ d) (σ (i ⊕ d)) HEF Hls) as Hback.
    pose proof (equality_transitivity F (i ⊕ k) (i ⊕ σ d)
      (σ (i ⊕ d)) HEF HA Hrs) as Hfront.
    pose proof (equality_transitivity F (i ⊕ k) (σ (i ⊕ d))
      (σ i ⊕ d) HEF Hfront Hback) as Hend.
    assert (HNF : F ⊢C (n == i ⊕ k)).
    { unfold F, E. apply weaken_head, weaken_head. exact HN. }
    apply (PAOrderBounds238.strict_order_witness F i n d).
    exact (equality_transitivity F n (i ⊕ k) (σ i ⊕ d) HEF HNF Hend).
Qed.

Theorem order_successor_split :
  paeq_derivable (∀ ∀ ($0 ⧀ σ $1 → (($0 ⧀ $1) ∨ ($0 == $1)))).
Proof.
  apply paeq_generalize, paeq_generalize, append_proof, II.
  set (G := List.cons ($0 ⧀ σ $1) append_context).
  apply (strict_successor_split G $0 $1).
  - unfold G. apply has_quotient_cons, extension_has_quotient. exact append_has_extension.
  - unfold G. right. exact append_has_injective.
  - apply Ctx. unfold G. now left.
Qed.

Theorem order_successor_covariance :
  paeq_derivable (∀ ∀ ($0 ⧀ $1 → σ $0 ⧀ σ $1)).
Proof.
  apply paeq_generalize, paeq_generalize, append_proof, II.
  set (G := List.cons ($0 ⧀ $1) append_context).
  apply (successor_order_covariance G $0 $1).
  - unfold G. apply has_quotient_cons, extension_has_quotient. exact append_has_extension.
  - apply Ctx. unfold G. now left.
Qed.

Definition beta_row_transfer (b c B C i : pa_term) : pa_form :=
  ∀ (beta b`[↑] c`[↑] i`[↑] $0 → beta B`[↑] C`[↑] i`[↑] $0).
Definition beta_prefix_recode (b c B C n : pa_term) : pa_form :=
  ∀ ($0 ⧀ (σ n)`[↑] → beta_row_transfer b`[↑] c`[↑] B`[↑] C`[↑] $0).
Definition beta_append_witness (b c B C n r : pa_term) : pa_form :=
  beta B C (σ n) r ∧ beta_prefix_recode b c B C n.

Lemma beta_row_transfer_subst b c B C i rho :
  (beta_row_transfer b c B C i)[rho] =
  beta_row_transfer b`[rho] c`[rho] B`[rho] C`[rho] i`[rho].
Proof.
  unfold beta_row_transfer. cbn [subst_form]. rewrite !beta_subst.
  now rewrite !up_term.
Qed.
Lemma beta_prefix_recode_subst b c B C n rho :
  (beta_prefix_recode b c B C n)[rho] =
  beta_prefix_recode b`[rho] c`[rho] B`[rho] C`[rho] n`[rho].
Proof.
  unfold beta_prefix_recode. cbn [subst_form].
  rewrite PAlt_subst, beta_row_transfer_subst. now rewrite !up_term.
Qed.
Lemma beta_append_witness_subst b c B C n r rho :
  (beta_append_witness b c B C n r)[rho] =
  beta_append_witness b`[rho] c`[rho] B`[rho] C`[rho] n`[rho] r`[rho].
Proof.
  unfold beta_append_witness. cbn [subst_form].
  rewrite beta_subst, beta_prefix_recode_subst. reflexivity.
Qed.

Lemma beta_prefix_recode_at G b c B C n i r :
  G ⊢C beta_prefix_recode b c B C n -> G ⊢C (i ⧀ σ n) ->
  G ⊢C beta b c i r -> G ⊢C beta B C i r.
Proof.
  intros HP HI HB. pose proof (AllE i HP) as HH.
  change (G ⊢C (PAlt $0 (σ n)`[↑])[i..] →
    (beta_row_transfer b`[↑] c`[↑] B`[↑] C`[↑] $0)[i..]) in HH.
  assert (Hni : (σ n)`[↑]`[i..] = σ n) by apply subst_term_shift.
  assert (Hbi : b`[↑]`[i..] = b) by apply subst_term_shift.
  assert (Hci : c`[↑]`[i..] = c) by apply subst_term_shift.
  assert (HBi : B`[↑]`[i..] = B) by apply subst_term_shift.
  assert (HCi : C`[↑]`[i..] = C) by apply subst_term_shift.
  rewrite PAlt_subst, beta_row_transfer_subst in HH.
  change (G ⊢C (i ⧀ (σ n)`[↑]`[i..] →
    beta_row_transfer b`[↑]`[i..] c`[↑]`[i..] B`[↑]`[i..] C`[↑]`[i..] i)) in HH.
  rewrite Hni, Hbi, Hci, HBi, HCi in HH.
  pose proof (IE HH HI) as HR. pose proof (AllE r HR) as HK.
  change (G ⊢C (beta b`[↑] c`[↑] i`[↑] $0)[r..] →
    (beta B`[↑] C`[↑] i`[↑] $0)[r..]) in HK.
  assert (Hbr : b`[↑]`[r..] = b) by apply subst_term_shift.
  assert (Hcr : c`[↑]`[r..] = c) by apply subst_term_shift.
  assert (Hir : i`[↑]`[r..] = i) by apply subst_term_shift.
  assert (HBr : B`[↑]`[r..] = B) by apply subst_term_shift.
  assert (HCr : C`[↑]`[r..] = C) by apply subst_term_shift.
  rewrite !beta_subst in HK.
  change (G ⊢C (beta b`[↑]`[r..] c`[↑]`[r..] i`[↑]`[r..] r →
    beta B`[↑]`[r..] C`[↑]`[r..] i`[↑]`[r..] r)) in HK.
  rewrite Hbr, Hcr, Hir, HBr, HCr in HK.
  exact (IE HK HB).
Qed.

Lemma zero_below_successor G n : has_quotient_context G ->
  G ⊢C (zero ⧀ σ n).
Proof.
  intros HG. pose proof (quotient_has_equality G HG) as HE.
  pose proof (PAAddition238.add_zero_instance G n
    (HG ax_add_zero quotient_add_zero)) as HZ.
  pose proof (IE (successor_instance G (zero ⊕ n) n HE) HZ) as HS.
  pose proof (PAOrder238.add_rec_instance G zero n
    (HG ax_add_rec quotient_add_rec)) as HR.
  pose proof (equality_transitivity G (σ zero ⊕ n) (σ (zero ⊕ n))
    (σ n) HE HR HS) as HF.
  apply (PAOrderBounds238.strict_order_witness G zero (σ n) n).
  exact (equality_symmetry G (σ zero ⊕ n) (σ n) HE HF).
Qed.

Lemma doubling_introduce G b c i r s :
  G ⊢C doubling_pair b c i r s -> G ⊢C doubling_step b c i.
Proof.
  intros HP. unfold doubling_step. apply (ExI r).
  cbn [subst_form]. rewrite doubling_pair_subst.
  rewrite !up_term, !subst_term_shift.
  change (G ⊢C ∃ doubling_pair b`[↑] c`[↑] i`[↑] r`[↑] $0).
  apply (ExI s). rewrite doubling_pair_subst, !subst_term_shift. exact HP.
Qed.

Lemma doubling_recode G b c B C n i : has_quotient_context G ->
  G ⊢C beta_prefix_recode b c B C n -> G ⊢C (i ⧀ n) ->
  G ⊢C doubling_step b c i -> G ⊢C doubling_step B C i.
Proof.
  intros HG HP HI HD. eapply doubling_eliminate; [exact HD|]. intros r s.
  set (D := List.cons (doubling_pair b c i r s) G).
  change (D ⊢C doubling_step B C i).
  assert (HDG : has_quotient_context D).
  { unfold D. apply has_quotient_cons. exact HG. }
  pose proof (weaken_head G (beta_prefix_recode b c B C n)
    (doubling_pair b c i r s) HP) as HPD.
  pose proof (weaken_head G (i ⧀ n) (doubling_pair b c i r s) HI) as HID.
  assert (HC : D ⊢C doubling_pair b c i r s).
  { apply Ctx. unfold D. now left. }
  pose proof (strict_upper_successor D i n HDG HID) as Hleft.
  pose proof (successor_order_covariance D i n HDG HID) as Hright.
  apply (doubling_introduce D B C i r s), CI.
  - exact (beta_prefix_recode_at D b c B C n i r HPD Hleft (CE1 HC)).
  - apply CI.
    + exact (beta_prefix_recode_at D b c B C n (σ i) s HPD Hright (CE1 (CE2 HC))).
    + exact (CE2 (CE2 HC)).
Qed.

Lemma trace_recode G b c B C n p : has_quotient_context G ->
  G ⊢C beta_prefix_recode b c B C n ->
  G ⊢C trace_body b c n p -> G ⊢C trace_body B C n p.
Proof.
  intros HG HP HT. unfold trace_body. apply CI.
  - apply (beta_prefix_recode_at G b c B C n zero (σ zero));
      [exact HP|apply zero_below_successor, HG|exact (CE1 HT)].
  - apply CI.
    + apply (beta_prefix_recode_at G b c B C n n p);
        [exact HP|apply successor_self, HG|exact (CE1 (CE2 HT))].
    + apply trace_steps_introduce. intros i. apply II.
      set (D := List.cons (i ⧀ n) G).
      change (D ⊢C doubling_step B C i).
      assert (HD : has_quotient_context D).
      { unfold D. apply has_quotient_cons. exact HG. }
      assert (HI : D ⊢C (i ⧀ n)).
      { apply Ctx. unfold D. now left. }
      pose proof (weaken_head G (beta_prefix_recode b c B C n) (i ⧀ n) HP) as HPD.
      pose proof (weaken_head G (trace_steps b c n) (i ⧀ n) (CE2 (CE2 HT))) as Hsteps.
      exact (doubling_recode D b c B C n i HD HPD HI
        (IE (trace_steps_at D b c n i Hsteps) HI)).
Qed.

Theorem trace_prefix_transport :
  paeq_derivable (∀ ∀ ∀ ∀ ∀ ∀
    (beta_prefix_recode $0 $1 $2 $3 $4 →
      trace_body $0 $1 $4 $5 → trace_body $2 $3 $4 $5)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize, append_proof, II, II.
  set (G := List.cons (trace_body $0 $1 $4 $5)
    (List.cons (beta_prefix_recode $0 $1 $2 $3 $4) append_context)).
  apply (trace_recode G $0 $1 $2 $3 $4 $5).
  - unfold G. apply has_quotient_cons, has_quotient_cons,
      extension_has_quotient. exact append_has_extension.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

Lemma doubling_index_transport G b c i j : has_equality G ->
  G ⊢C (i == j) -> G ⊢C doubling_step b c i -> G ⊢C doubling_step b c j.
Proof.
  intros HE HI HD.
  pose proof (formula_substitutivity G (doubling_step b`[↑] c`[↑] $0)
    i j HE HI) as HH.
  rewrite !doubling_step_subst, !subst_term_shift in HH.
  exact (IE (CE1 HH) HD).
Qed.

Lemma forward_trace G b c B C n p : has_quotient_context G ->
  List.In ax_succ_inj G ->
  G ⊢C beta_append_witness b c B C n (p ⊕ p) ->
  G ⊢C trace_body b c n p -> G ⊢C trace_body B C (σ n) (p ⊕ p).
Proof.
  intros HG Hinj HA HT.
  pose proof (CE2 HA) as HP. pose proof (CE1 HA) as Hend.
  unfold trace_body. apply CI.
  - apply (beta_prefix_recode_at G b c B C n zero (σ zero));
      [exact HP|apply zero_below_successor, HG|exact (CE1 HT)].
  - apply CI; [exact Hend|].
    apply trace_steps_introduce. intros i. apply II.
    set (D := List.cons (i ⧀ σ n) G).
    change (D ⊢C doubling_step B C i).
    assert (HD : has_quotient_context D).
    { unfold D. apply has_quotient_cons. exact HG. }
    assert (HinjD : List.In ax_succ_inj D) by (unfold D; now right).
    assert (HI : D ⊢C (i ⧀ σ n)).
    { apply Ctx. unfold D. now left. }
    pose proof (strict_successor_split D i n HD HinjD HI) as Hsplit.
    pose proof (weaken_head G (beta_prefix_recode b c B C n) (i ⧀ σ n) HP) as HPD.
    pose proof (weaken_head G (trace_body b c n p) (i ⧀ σ n) HT) as HTD.
    pose proof (weaken_head G (beta B C (σ n) (p ⊕ p)) (i ⧀ σ n) Hend) as HendD.
    eapply DE; [exact Hsplit| |].
    + set (E := List.cons (i ⧀ n) D).
      change (E ⊢C doubling_step B C i).
      assert (HE : has_quotient_context E).
      { unfold E. apply has_quotient_cons. exact HD. }
      assert (HIE : E ⊢C (i ⧀ n)).
      { apply Ctx. unfold E. now left. }
      pose proof (weaken_head D (beta_prefix_recode b c B C n) (i ⧀ n) HPD) as HPE.
      pose proof (weaken_head D (trace_steps b c n) (i ⧀ n) (CE2 (CE2 HTD))) as Hsteps.
      exact (doubling_recode E b c B C n i HE HPE HIE
        (IE (trace_steps_at E b c n i Hsteps) HIE)).
    + set (E := List.cons (i == n) D).
      change (E ⊢C doubling_step B C i).
      assert (HE : has_quotient_context E).
      { unfold E. apply has_quotient_cons. exact HD. }
      pose proof (quotient_has_equality E HE) as HEQ.
      assert (HIE : E ⊢C (i == n)).
      { apply Ctx. unfold E. now left. }
      pose proof (equality_symmetry E i n HEQ HIE) as Hni.
      pose proof (weaken_head D (beta_prefix_recode b c B C n) (i == n) HPD) as HPE.
      pose proof (weaken_head D (beta b c n p) (i == n) (CE1 (CE2 HTD))) as Hold.
      pose proof (weaken_head D (beta B C (σ n) (p ⊕ p)) (i == n) HendD) as Hnew.
      pose proof (successor_self E n HE) as Hns.
      pose proof (beta_prefix_recode_at E b c B C n n p HPE Hns Hold) as Hcurrent.
      assert (Hpair : E ⊢C doubling_pair B C n p (p ⊕ p)).
      { unfold doubling_pair. apply CI; [exact Hcurrent|]. apply CI; [exact Hnew|].
        exact (reflexivity_instance E (p ⊕ p) HEQ). }
      exact (doubling_index_transport E B C n i HEQ Hni
        (doubling_introduce E B C n p (p ⊕ p) Hpair)).
Qed.

Theorem trace_append_transport :
  paeq_derivable (∀ ∀ ∀ ∀ ∀ ∀
    (beta_append_witness $0 $1 $2 $3 $4 ($5 ⊕ $5) →
      trace_body $0 $1 $4 $5 → trace_body $2 $3 (σ $4) ($5 ⊕ $5))).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize, append_proof, II, II.
  set (G := List.cons (trace_body $0 $1 $4 $5)
    (List.cons (beta_append_witness $0 $1 $2 $3 $4 ($5 ⊕ $5)) append_context)).
  apply (forward_trace G $0 $1 $2 $3 $4 $5).
  - unfold G. apply has_quotient_cons, has_quotient_cons,
      extension_has_quotient. exact append_has_extension.
  - unfold G. right. right. exact append_has_injective.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

Definition beta_append_exists (b c n r : pa_term) : pa_form :=
  ∃ ∃ beta_append_witness b`[↑]`[↑] c`[↑]`[↑] $1 $0 n`[↑]`[↑] r`[↑]`[↑].
Lemma beta_append_exists_subst b c n r rho :
  (beta_append_exists b c n r)[rho] =
  beta_append_exists b`[rho] c`[rho] n`[rho] r`[rho].
Proof.
  unfold beta_append_exists. cbn [subst_form]. rewrite beta_append_witness_subst.
  now rewrite !up_term.
Qed.
Lemma beta_append_eliminate G b c n r (psi : pa_form) :
  G ⊢C beta_append_exists b c n r ->
  (forall B C, (List.cons (beta_append_witness b c B C n r) G) ⊢C psi) ->
  G ⊢C psi.
Proof.
  intros HX H. unfold beta_append_exists in HX.
  eapply ExE_named; [exact HX|]. intros B.
  cbn [subst_form]. rewrite beta_append_witness_subst.
  rewrite !up_term, !subst_term_shift.
  set (D := List.cons (∃ beta_append_witness b`[↑] c`[↑] B`[↑] $0 n`[↑] r`[↑]) G).
  change (D ⊢C psi).
  assert (HY : D ⊢C ∃ beta_append_witness b`[↑] c`[↑] B`[↑] $0 n`[↑] r`[↑]).
  { apply Ctx. unfold D. now left. }
  eapply ExE_named; [exact HY|]. intros C.
  rewrite beta_append_witness_subst, !subst_term_shift.
  change ((List.cons (beta_append_witness b c B C n r) D) ⊢C psi).
  eapply Weak; [exact (H B C)|]. intros chi Hchi.
  destruct Hchi as [<-|Hchi]; [now left|right; unfold D; now right].
Qed.

(* Exact outstanding arithmetic supplier.  This is a sentence definition,
   not an axiom or a claimed PA proof.  The theorem below requires its
   actual finite ordinary-PA certificate as an explicit input. *)
Definition trace_append_sentence : pa_form :=
  ∀ ∀ ∀ ∀ (trace_body $0 $1 $2 $3 →
    beta_append_exists $0 $1 $2 ($3 ⊕ $3)).
Definition supplier_context : list pa_form :=
  List.cons trace_append_sentence append_context.
Lemma supplier_proof phi : paeq_derivable trace_append_sentence ->
  supplier_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HP HD. eapply paeq_modus_ponens with (phi := trace_append_sentence).
  - apply append_proof, II. exact HD.
  - exact HP.
Qed.
Lemma trace_append_at G b c n p : List.In trace_append_sentence G ->
  G ⊢C (trace_body b c n p → beta_append_exists b c n (p ⊕ p)).
Proof.
  intros H. assert (HH : G ⊢C trace_append_sentence) by now apply Ctx.
  assert (HB : bounded 4
    (trace_body $0 $1 $2 $3 → beta_append_exists $0 $1 $2 ($3 ⊕ $3))).
  { unfold trace_body, trace_steps, doubling_step, doubling_pair,
      beta_append_exists, beta_append_witness, beta_prefix_recode,
      beta_row_transfer, beta, beta_modulus, quotient_row, PAlt. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := trace_body $0 $1 $2 $3 → beta_append_exists $0 $1 $2 ($3 ⊕ $3))
    (N := 4) HH HB (b .: c .: n .: p .: var)) as HK.
  change (G ⊢C (trace_body $0 $1 $2 $3)[b .: c .: n .: p .: var] →
    (beta_append_exists $0 $1 $2 ($3 ⊕ $3))[b .: c .: n .: p .: var]) in HK.
  rewrite trace_body_subst, beta_append_exists_subst in HK.
  change (G ⊢C (trace_body b c n p → beta_append_exists b c n (p ⊕ p))) in HK.
  exact HK.
Qed.

Theorem pow2_successor_from_trace_append :
  paeq_derivable trace_append_sentence ->
  paeq_derivable (∀ ∀ (pow2 $0 $1 → pow2 (σ $0) ($1 ⊕ $1))).
Proof.
  intros HP. apply paeq_generalize, paeq_generalize, (supplier_proof _ HP), II.
  set (G := List.cons (pow2 $0 $1) supplier_context).
  change (G ⊢C pow2 (σ $0) ($1 ⊕ $1)).
  assert (HX : G ⊢C pow2 $0 $1).
  { apply Ctx. unfold G. now left. }
  eapply pow2_eliminate; [exact HX|]. intros b c.
  set (D := List.cons (trace_body b c $0 $1) G).
  change (D ⊢C pow2 (σ $0) ($1 ⊕ $1)).
  assert (HT : D ⊢C trace_body b c $0 $1).
  { apply Ctx. unfold D. now left. }
  assert (Hsup : List.In trace_append_sentence D).
  { unfold D, G, supplier_context. right. right. now left. }
  pose proof (IE (trace_append_at D b c $0 $1 Hsup) HT) as HA.
  eapply beta_append_eliminate; [exact HA|]. intros B C.
  set (E := List.cons (beta_append_witness b c B C $0 ($1 ⊕ $1)) D).
  change (E ⊢C pow2 (σ $0) ($1 ⊕ $1)).
  assert (HE : has_quotient_context E).
  { unfold E, D, G, supplier_context. apply has_quotient_cons,
      has_quotient_cons, has_quotient_cons, has_quotient_cons,
      extension_has_quotient. exact append_has_extension. }
  assert (Hinj : List.In ax_succ_inj E).
  { unfold E, D, G, supplier_context. right. right. right. right.
    exact append_has_injective. }
  assert (HAE : E ⊢C beta_append_witness b c B C $0 ($1 ⊕ $1)).
  { apply Ctx. unfold E. now left. }
  pose proof (weaken_head D (trace_body b c $0 $1)
    (beta_append_witness b c B C $0 ($1 ⊕ $1)) HT) as HTE.
  apply (pow2_introduce E B C (σ $0) ($1 ⊕ $1)).
  exact (forward_trace E b c B C $0 $1 HE Hinj HAE HTE).
Qed.

Definition power_totality_formula : pa_form := ∃ pow2 $1 $0.
Lemma power_totality_base : paeq_derivable power_totality_formula[zero..].
Proof.
  change (paeq_derivable (∃ pow2 zero $0)).
  destruct pow2_zero_one as (A & HA & HD). exists A. split; [exact HA|].
  apply (ExI (σ zero)).
  change (A ⊢C (pow2 zero $0)[(σ zero)..]).
  rewrite pow2_subst. exact HD.
Qed.

Lemma power_totality_step : paeq_derivable trace_append_sentence ->
  paeq_derivable (∀ (power_totality_formula →
    power_totality_formula[σ $0 .: S >> var])).
Proof.
  intros HP. change (paeq_derivable (∀
    ((∃ pow2 $1 $0) → ∃ pow2 (σ $1) $0))).
  apply paeq_generalize.
  destruct (pow2_successor_from_trace_append HP) as (A & HA & HD).
  exists A. split; [exact HA|]. apply II.
  set (G := List.cons (∃ pow2 $1 $0) A).
  change (G ⊢C ∃ pow2 (σ $1) $0).
  assert (HX : G ⊢C ∃ pow2 $1 $0).
  { apply Ctx. unfold G. now left. }
  eapply ExE_named; [exact HX|]. intros p. rewrite pow2_subst.
  set (D := List.cons (pow2 $0 p) G).
  change (D ⊢C ∃ pow2 (σ $1) $0).
  assert (HS : D ⊢C ∀ ∀ (pow2 $0 $1 → pow2 (σ $0) ($1 ⊕ $1))).
  { eapply Weak; [exact HD|]. intros phi Hphi. unfold D, G. right. now right. }
  assert (HB : bounded 2 (pow2 $0 $1 → pow2 (σ $0) ($1 ⊕ $1))).
  { unfold pow2, beta, beta_modulus, PAlt. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := pow2 $0 $1 → pow2 (σ $0) ($1 ⊕ $1))
    (N := 2) HS HB ($0 .: p .: var)) as HK.
  change (D ⊢C (pow2 $0 $1)[$0 .: p .: var] →
    (pow2 (σ $0) ($1 ⊕ $1))[$0 .: p .: var]) in HK.
  rewrite !pow2_subst in HK.
  change (D ⊢C (pow2 $0 p → pow2 (σ $0) (p ⊕ p))) in HK.
  assert (HC : D ⊢C pow2 $0 p).
  { apply Ctx. unfold D. now left. }
  pose proof (IE HK HC) as Hnext.
  apply (ExI (p ⊕ p)).
  change (D ⊢C (pow2 (σ $1) $0)[(p ⊕ p)..]).
  rewrite pow2_subst. exact Hnext.
Qed.

Theorem pow2_total_from_trace_append : paeq_derivable trace_append_sentence ->
  paeq_derivable (∀ ∃ pow2 $1 $0).
Proof.
  intros HP. change (paeq_derivable (∀ power_totality_formula)).
  apply (paeq_induction_rule power_totality_formula).
  - exact power_totality_base.
  - exact (power_totality_step HP).
Qed.

Definition addition_right_bound_sentence : pa_form :=
  ∀ ∀ ($1 ⧀= ($0 ⊕ $1)).
Definition weak_right_extension_sentence : pa_form :=
  ∀ ∀ ∀ ($0 ⧀= $1 → $0 ⧀= ($1 ⊕ $2)).
Definition coding_context : list pa_form :=
  [addition_right_bound_sentence; weak_right_extension_sentence] ++ append_context.
Lemma coding_proof phi : coding_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD.
  eapply paeq_modus_ponens with (phi := addition_right_bound_sentence);
    [|exact PAOrderBounds238.addition_right_bound].
  eapply paeq_modus_ponens with (phi := weak_right_extension_sentence);
    [|exact PAOrderBounds238.weak_order_right_extension].
  apply append_proof, II, II. exact HD.
Qed.
Lemma coding_has_quotient : has_quotient_context coding_context.
Proof.
  intros phi Hphi. unfold coding_context. cbn. right. right.
  exact (extension_has_quotient append_context append_has_extension phi Hphi).
Qed.
Lemma coding_right_bound : List.In addition_right_bound_sentence coding_context.
Proof. unfold coding_context. now left. Qed.
Lemma coding_weak_extension : List.In weak_right_extension_sentence coding_context.
Proof. unfold coding_context. right. now left. Qed.
Lemma addition_right_bound_at G a v : List.In addition_right_bound_sentence G ->
  G ⊢C (v ⧀= (a ⊕ v)).
Proof.
  intros H. change (G ⊢C ($1 ⧀= ($0 ⊕ $1))[a .: v .: var]).
  apply (subst_forall_prv (phi := $1 ⧀= ($0 ⊕ $1)) (N := 2)).
  - change (G ⊢C addition_right_bound_sentence). now apply Ctx.
  - unfold PAle. solve_bounds.
Qed.

Lemma beta_remainder_bound G b c i v : has_quotient_context G ->
  List.In addition_right_bound_sentence G ->
  G ⊢C beta b c i v -> G ⊢C (v ⧀= b).
Proof.
  intros HG HR HB. rewrite beta_exists_witness in HB.
  eapply ExE_named; [exact HB|]. intros q.
  assert (Hb : b`[↑]`[q..] = b) by apply subst_term_shift.
  assert (Hc : c`[↑]`[q..] = c) by apply subst_term_shift.
  assert (Hi : i`[↑]`[q..] = i) by apply subst_term_shift.
  assert (Hv : v`[↑]`[q..] = v) by apply subst_term_shift.
  rewrite beta_witness_subst.
  change ((List.cons (beta_witness b`[↑]`[q..] c`[↑]`[q..]
    i`[↑]`[q..] v`[↑]`[q..] q) G) ⊢C (v ⧀= b)).
  rewrite Hb, Hc, Hi, Hv.
  set (m := beta_modulus c i).
  set (D := List.cons ((b == quotient_row q m v) ∧ (v ⧀ m)) G).
  change (D ⊢C (v ⧀= b)).
  assert (HD : has_quotient_context D).
  { unfold D. apply has_quotient_cons. exact HG. }
  pose proof (quotient_has_equality D HD) as HE.
  assert (Hrow : D ⊢C (b == quotient_row q m v)).
  { eapply CE1. apply Ctx. unfold D. now left. }
  pose proof (equality_symmetry D b (quotient_row q m v) HE Hrow) as Hback.
  assert (HRD : List.In addition_right_bound_sentence D) by (unfold D; now right).
  pose proof (addition_right_bound_at D (q ⊗ m) v HRD) as Hbound.
  pose proof (formula_substitutivity D (PAle v`[↑] $0)
    (quotient_row q m v) b HE Hback) as Htransfer.
  assert (Hvr : v`[↑]`[(quotient_row q m v)..] = v) by apply subst_term_shift.
  assert (Hvb : v`[↑]`[b..] = v) by apply subst_term_shift.
  rewrite !PAle_subst in Htransfer.
  change (D ⊢C (v`[↑]`[(quotient_row q m v)..] ⧀= quotient_row q m v ↔
    v`[↑]`[b..] ⧀= b)) in Htransfer.
  rewrite Hvr, Hvb in Htransfer. exact (IE (CE1 Htransfer) Hbound).
Qed.

Theorem beta_value_bound :
  paeq_derivable (∀ ∀ ∀ ∀ (beta $0 $1 $2 $3 → $3 ⧀= $0)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, coding_proof, II.
  set (G := List.cons (beta $0 $1 $2 $3) coding_context).
  apply (beta_remainder_bound G $0 $1 $2 $3).
  - unfold G. apply has_quotient_cons. exact coding_has_quotient.
  - unfold G. right. exact coding_right_bound.
  - apply Ctx. unfold G. now left.
Qed.

Definition beta_value_exists (b c i : pa_term) : pa_form :=
  ∃ beta b`[↑] c`[↑] i`[↑] $0.
Lemma beta_value_exists_subst b c i rho :
  (beta_value_exists b c i)[rho] = beta_value_exists b`[rho] c`[rho] i`[rho].
Proof.
  unfold beta_value_exists. cbn [subst_form]. rewrite beta_subst. now rewrite !up_term.
Qed.
Lemma beta_value_exists_intro G b c i v :
  G ⊢C beta b c i v -> G ⊢C beta_value_exists b c i.
Proof.
  intros H. unfold beta_value_exists. apply (ExI v).
  rewrite beta_subst, !subst_term_shift. exact H.
Qed.
Lemma beta_index_transport G b c i j v : has_equality G ->
  G ⊢C (i == j) -> G ⊢C beta b c i v -> G ⊢C beta b c j v.
Proof.
  intros HE HI HB.
  pose proof (formula_substitutivity G (beta b`[↑] c`[↑] $0 v`[↑]) i j HE HI) as HH.
  rewrite !beta_subst, !subst_term_shift in HH. exact (IE (CE1 HH) HB).
Qed.

(* The trace itself supplies every value in its inclusive prefix.  Thus
   a trace-conditioned append proof needs no generic division-totality
   certificate merely to obtain the old graph's witnesses. *)
Lemma trace_beta_total G b c n p i : has_quotient_context G ->
  List.In ax_succ_inj G -> G ⊢C trace_body b c n p ->
  G ⊢C (i ⧀ σ n) -> G ⊢C beta_value_exists b c i.
Proof.
  intros HG Hinj HT HI.
  pose proof (strict_successor_split G i n HG Hinj HI) as Hsplit.
  eapply DE; [exact Hsplit| |].
  - set (D := List.cons (i ⧀ n) G).
    change (D ⊢C beta_value_exists b c i).
    assert (HID : D ⊢C (i ⧀ n)).
    { apply Ctx. unfold D. now left. }
    pose proof (weaken_head G (trace_steps b c n) (i ⧀ n) (CE2 (CE2 HT))) as Hsteps.
    pose proof (IE (trace_steps_at D b c n i Hsteps) HID) as Hpair.
    eapply doubling_eliminate; [exact Hpair|]. intros r s.
    set (E := List.cons (doubling_pair b c i r s) D).
    change (E ⊢C beta_value_exists b c i).
    apply (beta_value_exists_intro E b c i r). eapply CE1.
    apply Ctx. unfold E. now left.
  - set (D := List.cons (i == n) G).
    change (D ⊢C beta_value_exists b c i).
    assert (HD : has_quotient_context D).
    { unfold D. apply has_quotient_cons. exact HG. }
    pose proof (quotient_has_equality D HD) as HE.
    assert (HID : D ⊢C (i == n)).
    { apply Ctx. unfold D. now left. }
    pose proof (equality_symmetry D i n HE HID) as Hni.
    pose proof (weaken_head G (beta b c n p) (i == n) (CE1 (CE2 HT))) as Hend.
    apply (beta_value_exists_intro D b c i p).
    exact (beta_index_transport D b c n i p HE Hni Hend).
Qed.

Theorem trace_beta_values_total :
  paeq_derivable (∀ ∀ ∀ ∀ ∀
    (trace_body $0 $1 $2 $3 → $4 ⧀ σ $2 → beta_value_exists $0 $1 $4)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, append_proof, II, II.
  set (G := List.cons ($4 ⧀ σ $2) (List.cons (trace_body $0 $1 $2 $3) append_context)).
  apply (trace_beta_total G $0 $1 $2 $3 $4).
  - unfold G. apply has_quotient_cons, has_quotient_cons,
      extension_has_quotient. exact append_has_extension.
  - unfold G. right. right. exact append_has_injective.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

Definition append_graph (b c n r i v : pa_term) : pa_form :=
  ((i ⧀ σ n) ∧ beta b c i v) ∨ ((i == σ n) ∧ (v == r)).
Lemma weak_right_extension_at G v b r : List.In weak_right_extension_sentence G ->
  G ⊢C (v ⧀= b) -> G ⊢C (v ⧀= (b ⊕ r)).
Proof.
  intros H HB.
  assert (HH : G ⊢C weak_right_extension_sentence) by now apply Ctx.
  assert (Hbounded : bounded 3 ($0 ⧀= $1 → $0 ⧀= ($1 ⊕ $2))).
  { unfold PAle. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := $0 ⧀= $1 → $0 ⧀= ($1 ⊕ $2)) (N := 3)
    HH Hbounded (v .: b .: r .: var)) as HK.
  change (G ⊢C (PAle $0 $1)[v .: b .: r .: var] →
    (PAle $0 ($1 ⊕ $2))[v .: b .: r .: var]) in HK.
  rewrite !PAle_subst in HK.
  change (G ⊢C (v ⧀= b → v ⧀= (b ⊕ r))) in HK. exact (IE HK HB).
Qed.

(* The append graph's uniform arithmetic bound is b+r.  Old values are
   bounded by b through their literal quotient equation; the added value
   r is bounded by b+r through the direct right-addition certificate. *)
Theorem append_graph_bound :
  paeq_derivable (∀ ∀ ∀ ∀ ∀ ∀
    (append_graph $0 $1 $2 $3 $4 $5 → $5 ⧀= ($0 ⊕ $3))).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize, coding_proof, II.
  set (G := List.cons (append_graph $0 $1 $2 $3 $4 $5) coding_context).
  change (G ⊢C ($5 ⧀= ($0 ⊕ $3))).
  assert (HQ : G ⊢C append_graph $0 $1 $2 $3 $4 $5).
  { apply Ctx. unfold G. now left. }
  unfold append_graph in HQ. eapply DE; [exact HQ| |].
  - set (D := List.cons (($4 ⧀ σ $2) ∧ beta $0 $1 $4 $5) G).
    change (D ⊢C ($5 ⧀= ($0 ⊕ $3))).
    assert (HD : has_quotient_context D).
    { unfold D, G. apply has_quotient_cons, has_quotient_cons. exact coding_has_quotient. }
    assert (HR : List.In addition_right_bound_sentence D).
    { unfold D, G. right. right. exact coding_right_bound. }
    assert (HW : List.In weak_right_extension_sentence D).
    { unfold D, G. right. right. exact coding_weak_extension. }
    assert (HB : D ⊢C beta $0 $1 $4 $5).
    { eapply CE2. apply Ctx. unfold D. now left. }
    exact (weak_right_extension_at D $5 $0 $3 HW
      (beta_remainder_bound D $0 $1 $4 $5 HD HR HB)).
  - set (D := List.cons (($4 == σ $2) ∧ ($5 == $3)) G).
    change (D ⊢C ($5 ⧀= ($0 ⊕ $3))).
    assert (HD : has_quotient_context D).
    { unfold D, G. apply has_quotient_cons, has_quotient_cons. exact coding_has_quotient. }
    pose proof (quotient_has_equality D HD) as HE.
    assert (HR : List.In addition_right_bound_sentence D).
    { unfold D, G. right. right. exact coding_right_bound. }
    assert (Hvr : D ⊢C ($5 == $3)).
    { eapply CE2. apply Ctx. unfold D. now left. }
    pose proof (equality_symmetry D $5 $3 HE Hvr) as Hrv.
    pose proof (addition_right_bound_at D $0 $3 HR) as Hbound.
    pose proof (formula_substitutivity D (PAle $0 ($0 ⊕ $3)`[↑])
      $3 $5 HE Hrv) as Htransfer.
    rewrite !PAle_subst, !subst_term_shift in Htransfer.
    exact (IE (CE1 Htransfer) Hbound).
Qed.

End PAPowerExtension238.

Print Assumptions PAPowerExtension238.beta_introduce.
Print Assumptions PAPowerExtension238.beta_one_at_zero.
Print Assumptions PAPowerExtension238.pow2_zero_one.
Print Assumptions PAPowerExtension238.order_successor_split.
Print Assumptions PAPowerExtension238.order_successor_covariance.
Print Assumptions PAPowerExtension238.trace_prefix_transport.
Print Assumptions PAPowerExtension238.trace_append_transport.
Print Assumptions PAPowerExtension238.pow2_successor_from_trace_append.
Print Assumptions PAPowerExtension238.pow2_total_from_trace_append.
Print Assumptions PAPowerExtension238.beta_value_bound.
Print Assumptions PAPowerExtension238.trace_beta_values_total.
Print Assumptions PAPowerExtension238.append_graph_bound.
