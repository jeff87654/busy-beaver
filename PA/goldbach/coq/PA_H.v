(** * PA_H: soundness of the library's classical natural deduction (PA signature) for the named
    calculus: if [A ⊢C phi] then [der (map (tr eta) A) (tr eta phi)] in [pprov X] (pure logic plus
    any X), for every environment [eta] whose terms only use odd variables.
    Ported from zf/stdzf/coq/Std_H.v; quantifier instantiation now uses arbitrary terms (lspec). *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import PA.
From PAGB Require Import PALogic PA_dB PA_LProp PA_LMeta PA_tr.
Import ListNotations.
Unset Implicit Arguments.

Local Notation "A ⊢C phi" := (@prv _ _ falsity_on class A phi) (at level 55).

Section H.
Variable X : wff -> Prop.
Local Notation lprov := (pprov X).
Local Notation der := (der X).
Let LDET := DET X.
Let LGEN := GEN X.
Let LB2 := B2 X.
Let LB3 := B3 X.
Let LB4 := B4 X.
Let LB6c := B6c X.
Let dhyp := dhyp X.
Let dthm := dthm X.
Let dmp := dmp X.
Let ded := ded X.
Let der_lprov := der_lprov X.

Definition leqv (a b : wff) : Prop := lprov (Wim a b) /\ lprov (Wim b a).

(** ** Hypothesis lists and generalization *)
Definition foldi (G : list wff) (a : wff) : wff := fold_left (fun acc h => Wim h acc) G a.

Lemma der_foldi G a : der G a -> lprov (foldi G a).
Proof.
  revert a; induction G as [|h G IH]; intros a H.
  - exact (der_lprov _ H).
  - apply IH. exact (ded _ _ _ H).
Qed.

Lemma foldi_der G a : lprov (foldi G a) -> der G a.
Proof.
  revert a; induction G as [|h G IH]; intros a H.
  - exact (dthm _ _ H).
  - specialize (IH _ H). eapply dmp; [eapply der_weak; [exact IH | intros ? ?; simpl; auto] | apply dhyp; simpl; auto].
Qed.

Lemma foldi_mono G a b : lprov (Wim a b) -> lprov (Wim (foldi G a) (foldi G b)).
Proof.
  revert a b; induction G as [|h G IH]; intros a b H; [exact H|].
  apply IH. apply der_lprov, ded, ded. eapply dmp; [apply dthm, H|]. eapply dmp; apply dhyp; simpl; auto.
Qed.

Lemma all_imp_vac y h c : occ y h = false -> lprov (Wim (Wal y (Wim h c)) (Wim h (Wal y c))).
Proof.
  intro Hy. apply der_lprov, ded, ded.
  eapply dmp; [eapply dmp; [apply dthm, (LB4 y h c) | apply dhyp; simpl; auto]|].
  eapply dmp; [apply dthm, (lvac X y h Hy) | apply dhyp; simpl; auto].
Qed.

Lemma push_all G y c : (forall h, In h G -> occ y h = false) ->
  lprov (Wal y (foldi G c)) -> lprov (foldi G (Wal y c)).
Proof.
  revert c; induction G as [|h G IH]; intros c HG H; [exact H|].
  cbn [foldi fold_left] in *.
  assert (H1 : lprov (foldi G (Wal y (Wim h c)))) by (apply IH; [intros h0 Hh0; apply HG; simpl; auto | exact H]).
  exact (LDET _ _ (foldi_mono G _ _ (all_imp_vac y h c (HG h (or_introl eq_refl)))) H1).
Qed.

Lemma der_gen G y a : (forall h, In h G -> occ y h = false) -> der G a -> der G (Wal y a).
Proof.
  intros HG H. apply foldi_der. apply push_all; [exact HG|]. apply LGEN. now apply der_foldi.
Qed.

(** ** Propositional helpers *)
Lemma l_botw_elim a : lprov (Wim botw a).
Proof.
  unfold botw. apply der_lprov, ded.
  eapply dmp; [eapply dmp; [apply dthm, (LB3 (Weq TZ TZ) a) | apply dthm, leq_refl] | apply dhyp; simpl; auto].
Qed.

Lemma l_not_botw : lprov (Wn botw).
Proof. unfold botw. exact (LDET _ _ (lpc_nn_intro X _) (leq_refl X TZ)). Qed.

Lemma tr_imp_equiv eta (phi psi : form) :
  leqv (tr eta (bin Impl phi psi)) (Wim (tr eta phi) (tr eta psi)).
Proof.
  destruct psi; cbn [tr]; try (split; apply lpc_id).
  set (p := tr eta phi). split; apply der_lprov, ded.
  - apply ded. eapply dmp; [eapply dmp; [apply dthm, (LB3 p botw) | apply dhyp; simpl; auto] | apply dhyp; simpl; auto].
  - eapply dmp; [eapply dmp; [apply dthm, (lpc_contra X p botw) | apply dhyp; simpl; auto] | apply dthm, l_not_botw].
Qed.

Lemma der_leqv G a b : leqv a b -> der G a -> der G b.
Proof. intros [H _] Ha. exact (dmp _ _ _ (dthm _ _ H) Ha). Qed.

Lemma leqv_sym a b : leqv a b -> leqv b a.
Proof. intros [H1 H2]; split; assumption. Qed.

Lemma leqv_im a a' b b' : leqv a a' -> leqv b b' -> leqv (Wim a b) (Wim a' b').
Proof.
  intros [H1 H2] [H3 H4]. split; apply der_lprov, ded, ded.
  - eapply dmp; [apply dthm, H3|]. eapply dmp; [apply dhyp; simpl; auto|]. eapply dmp; [apply dthm, H2 | apply dhyp; simpl; auto].
  - eapply dmp; [apply dthm, H4|]. eapply dmp; [apply dhyp; simpl; auto|]. eapply dmp; [apply dthm, H1 | apply dhyp; simpl; auto].
Qed.

Lemma leqv_refl a : leqv a a.
Proof. split; apply lpc_id. Qed.

Lemma leqv_trans a b c : leqv a b -> leqv b c -> leqv a c.
Proof. intros [H1 H2] [H3 H4]. split; eapply lsyl; eassumption. Qed.

Lemma lprov_leqv a b : leqv a b -> lprov a -> lprov b.
Proof. intros [H _] Ha. exact (LDET _ _ H Ha). Qed.

Lemma l_peirce p q : lprov (Wim (Wim (Wim p q) p) p).
Proof.
  apply der_lprov, ded. eapply dmp; [apply dthm, (LB2 p)|]. apply ded.
  eapply dmp; [apply dhyp; simpl; right; left; reflexivity|].
  apply ded. eapply dmp; [eapply dmp; [apply dthm, (LB3 p q) | apply dhyp; simpl; auto] | apply dhyp; simpl; auto].
Qed.

Lemma l_case a b c : lprov (Wim (Wim (Wn a) b) (Wim (Wim a c) (Wim (Wim b c) c))).
Proof.
  apply der_lprov, ded, ded, ded.
  eapply dmp; [apply dthm, (LB2 c)|]. apply ded.
  eapply dmp; [apply dhyp; simpl; right; left; reflexivity|].
  eapply dmp; [apply dhyp; simpl; right; right; right; left; reflexivity|].
  eapply dmp; [eapply dmp; [apply dthm, (lpc_contra X a c) | apply dhyp; simpl; auto] | apply dhyp; simpl; auto].
Qed.

Lemma l_ex_elim y p c : occ y c = false -> lprov (Wim (Wal y (Wim p c)) (Wim (Wex y p) c)).
Proof.
  intro Hy. apply der_lprov, ded, ded.
  eapply dmp; [apply dthm, (LB6c y c)|].
  eapply dmp; [apply dthm, (lex X y _ _ (lvac X y c Hy))|].
  eapply dmp; [eapply dmp; [apply dthm, (lall_ex X y p c) | apply dhyp; simpl; auto] | apply dhyp; simpl; auto].
Qed.

(** ** Alphabetic variance *)
Lemma lalpha x y a : x <> y -> bnd x a = false -> occ y a = false ->
  lprov (Wim (Wal x a) (Wal y (sb x (TV y) a))).
Proof.
  intros Hxy Hx Hy.
  assert (Hs : sfree (TV y) a).
  { intros v Hv. cbn in Hv. apply Nat.eqb_eq in Hv as ->. now apply occ_bnd. }
  pose proof (lspec X x (TV y) a ltac:(cbn; apply Nat.eqb_neq; congruence) Hx Hs) as H1.
  refine (lsyl X _ _ _ (lvac X y (Wal x a) _) (lal X y _ _ H1)).
  simpl. rewrite Hy, orb_false_r. apply Nat.eqb_neq. exact Hxy.
Qed.

Lemma lalpha_ex x y a : x <> y -> bnd x a = false -> occ y a = false ->
  lprov (Wim (Wex x a) (Wex y (sb x (TV y) a))).
Proof.
  intros Hxy Hx Hy. unfold Wex.
  assert (Hb : lprov (Wim (Wal y (Wn (sb x (TV y) a))) (Wal x (sb y (TV x) (Wn (sb x (TV y) a)))))).
  { apply lalpha.
    - congruence.
    - cbn. rewrite bnd_sb. now apply occ_bnd.
    - cbn. apply occ_sb_self; [cbn; apply Nat.eqb_neq; congruence | exact Hx]. }
  cbn [sb] in Hb. rewrite sb_back in Hb by exact Hy.
  exact (lcontra X _ _ Hb).
Qed.

End H.
