(** Original PA238 work.  The source relation is converse membership:
    [R A x] means that x belongs to A.  All formulas below use the existing
    Undecidability library syntax, substitution, and natural deduction.

    This file does not claim the arithmetic interpretation or a translation
    of the raw numeric calculus.  It gives concrete schema/representation
    formulas and small finite derivation constructions needed by that work.
    In particular, [representative_induction] below is a formula definition,
    not an assumed theorem asserting that the formula is derivable.

    Source reference (read only): original machine repository
    6f7f0c2f97703839e56a705bbf5da5a0e5c132cf, layout_core/inputs/pa/source.py,
    SHA256 b489f6f59dfd6af070db18897ca76b275a931f9958941bceb697c6dd3f4d751a.
    No Jeff/ZF proof source is imported or adapted here. *)

From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
Import ListNotations FullSyntax BinSig ZFSignature.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module Compact238.

Definition set_term := @Core.term sig_empty.
Definition set_form :=
  @Core.form sig_empty ZF_pred_sig full_operators falsity_on.

Definition terms2 (x y : set_term) : Vector.t set_term 2 :=
  Vector.cons set_term x 1 (Vector.cons set_term y 0 (Vector.nil set_term)).

Definition R (a x : set_term) : set_form := atom elem (terms2 x a).
Definition E (x y : set_term) : set_form := atom equal (terms2 x y).

Notation "G ⊢238 phi" :=
  (@prv sig_empty ZF_pred_sig falsity_on class G phi) (at level 55).

(** An ordinary formula property has slots
    $0 = member, $1 = input object, $2 = freely chosen point,
    $(3+k) = extra parameter k.  The outer universal binders close the
    input and point; the remaining parameters are closed explicitly later.

    Under the member binder the environment is
       member $0, output $1, point $2, input $3, parameters $(4+k).
    Outside that binder it is
       output $0, point $1, input $2, parameters $(3+k).
    The point substitution deliberately places the same term in slots 0
    and 2.  A formula may depend arbitrarily on either slot and on all the
    extra parameters. *)
Definition member_slots : nat -> set_term :=
  $0 .: $3 .: $2 .: (fun k => $(4 + k)).
Definition point_slots : nat -> set_term :=
  $1 .: $2 .: $1 .: (fun k => $(3 + k)).

Definition pointed_body (phi : set_form) : set_form :=
  (∀ ((R $3 $0 → (phi[member_slots] → R $1 $0)) ∧
       (R $1 $0 → phi[member_slots]))) ∧
  (phi[point_slots] → R $0 $1).

Definition pointed_ax (phi : set_form) : set_form := ∀ ∀ ∃ pointed_body phi.

(** The gate c<>u and c<>x does not require u<>x.  For u=x, the member
    binder also binds the input name.  The guard is then R($0,$0), while
    the chosen point remains free in the second conjunct.  Here phi has
    one member slot and arbitrary additional parameter slots. *)
Definition collision_member_slots : nat -> set_term :=
  $0 .: (fun k => $(3 + k)).
Definition collision_point_slots : nat -> set_term :=
  $1 .: (fun k => $(2 + k)).

Definition collided_body (phi : set_form) : set_form :=
  (∀ ((R $0 $0 → (phi[collision_member_slots] → R $1 $0)) ∧
       (R $1 $0 → phi[collision_member_slots]))) ∧
  (phi[collision_point_slots] → R $0 $1).

Definition collided_ax (phi : set_form) : set_form := ∀ ∃ collided_body phi.

Definition singleton_filter_body (phi : set_form) : set_form :=
  (∀ (R $1 $0 → phi[collision_member_slots])) ∧
  (phi[collision_point_slots] → R $0 $1).

Definition ir : set_form := ∀ ¬ R $0 $0.

(** Ordinary nonextensional finite-set schemas, expressed with the same
    relation and equality.  No extensionality or canonical empty/successor
    witness is asserted.  [separation_ax] takes $0 as its tested member
    and $(1+k) as an arbitrary parameter. *)
Definition empty_ax : set_form := ∃ ∀ ¬ R $1 $0.
Definition adjunction_ax : set_form :=
  ∀ ∀ ∃ ∀ (R $1 $0 ↔ (R $3 $0 ∨ E $0 $2)).
Definition separation_slots : nat -> set_term :=
  $0 .: (fun k => $(3 + k)).
Definition separation_ax (phi : set_form) : set_form :=
  ∀ ∃ ∀ (R $1 $0 ↔ (R $2 $0 ∧ phi[separation_slots])).

Definition equality_base : list set_form :=
  [∀ E $0 $0;
   ∀ ∀ (E $1 $0 → E $0 $1);
   ∀ ∀ ∀ (E $2 $1 → E $1 $0 → E $2 $0);
   ∀ ∀ ∀ ∀ (E $3 $1 → E $2 $0 → R $2 $3 → R $0 $1)].

(** All axiom instances in the theory interface are closed.  These are
    theory *definitions*, not Coq axioms or assumed adequacy theorems. *)
Inductive compact_theory : set_form -> Prop :=
| compact_equality phi : In phi equality_base -> compact_theory phi
| compact_ir : compact_theory ir
| compact_pointed phi n :
    bounded 0 (forall_times n (pointed_ax phi)) ->
    compact_theory (forall_times n (pointed_ax phi))
| compact_collided phi n :
    bounded 0 (forall_times n (collided_ax phi)) ->
    compact_theory (forall_times n (collided_ax phi)).

Inductive adj_sep_theory : set_form -> Prop :=
| adj_sep_equality phi : In phi equality_base -> adj_sep_theory phi
| adj_sep_ir : adj_sep_theory ir
| adj_sep_empty : adj_sep_theory empty_ax
| adj_sep_adjunction : adj_sep_theory adjunction_ax
| adj_sep_separation phi n :
    bounded 0 (forall_times n (separation_ax phi)) ->
    adj_sep_theory (forall_times n (separation_ax phi)).

Definition derivable (T : set_form -> Prop) (phi : set_form) : Prop :=
  exists G, (forall psi, In psi G -> T psi) /\ G ⊢238 phi.

(** Elementary syntax bounds.  These use the library's inductive bounded
    predicate directly; they do not decide the truth of a parameter formula. *)
Lemma atom2_bounded n (p : ZF_Preds) i j :
  i < n -> j < n -> bounded n (atom p (terms2 $i $j) : set_form).
Proof.
  intros Hi Hj. constructor. intros t Ht. unfold terms2 in Ht.
  apply vec_cons_inv in Ht as [->|Ht]; [constructor; exact Hi|].
  apply vec_cons_inv in Ht as [->|Ht]; [constructor; exact Hj|].
  inversion Ht.
Qed.

Ltac fixed_bounds :=
  repeat first [apply bounded_quant | apply bounded_bin |
                apply bounded_falsity | apply atom2_bounded; lia].

Lemma pointed_ax_bounded n phi :
  bounded (3 + n) phi -> bounded n (pointed_ax phi).
Proof.
  intro Hphi. unfold pointed_ax, pointed_body, R. fixed_bounds.
  all: eapply subst_bounded_max; [|exact Hphi].
  all: intros [|[|[|k]]] Hk; cbn [member_slots point_slots scons];
       constructor; lia.
Qed.

Lemma collided_ax_bounded n phi :
  bounded (1 + n) phi -> bounded n (collided_ax phi).
Proof.
  intro Hphi. unfold collided_ax, collided_body, R. fixed_bounds.
  all: eapply subst_bounded_max; [|exact Hphi].
  all: intros [|k] Hk; cbn [collision_member_slots collision_point_slots scons];
       constructor; lia.
Qed.

Lemma separation_ax_bounded n phi :
  bounded (1 + n) phi -> bounded n (separation_ax phi).
Proof.
  intro Hphi. unfold separation_ax, R. fixed_bounds.
  all: eapply subst_bounded_max; [|exact Hphi].
  all: intros [|k] Hk; cbn [separation_slots scons]; constructor; lia.
Qed.

Lemma forall_times_closed n phi :
  bounded n phi -> bounded 0 (forall_times n phi).
Proof.
  revert phi. induction n as [|n IH]; intros phi Hphi; cbn.
  - exact Hphi.
  - unfold forall_times in *. rewrite iter_switch.
    apply IH. constructor. exact Hphi.
Qed.

Lemma pointed_instance_closed n phi :
  bounded (3 + n) phi -> bounded 0 (forall_times n (pointed_ax phi)).
Proof. intro H. apply forall_times_closed, pointed_ax_bounded, H. Qed.

Lemma collided_instance_closed n phi :
  bounded (1 + n) phi -> bounded 0 (forall_times n (collided_ax phi)).
Proof. intro H. apply forall_times_closed, collided_ax_bounded, H. Qed.

Lemma separation_instance_closed n phi :
  bounded (1 + n) phi -> bounded 0 (forall_times n (separation_ax phi)).
Proof. intro H. apply forall_times_closed, separation_ax_bounded, H. Qed.

Lemma equality_base_closed phi : In phi equality_base -> bounded 0 phi.
Proof.
  unfold equality_base, E, R. intros [<-|[<-|[<-|[<-|[]]]]];
    fixed_bounds.
Qed.

Lemma ir_closed : bounded 0 ir.
Proof. unfold ir, R. fixed_bounds. Qed.
Lemma empty_ax_closed : bounded 0 empty_ax.
Proof. unfold empty_ax, R. fixed_bounds. Qed.
Lemma adjunction_ax_closed : bounded 0 adjunction_ax.
Proof. unfold adjunction_ax, R, E. fixed_bounds. Qed.

Lemma compact_theory_closed phi : compact_theory phi -> bounded 0 phi.
Proof.
  intros [chi H| |chi n H|chi n H];
    [now apply equality_base_closed|apply ir_closed|exact H|exact H].
Qed.

Lemma adj_sep_theory_closed phi : adj_sep_theory phi -> bounded 0 phi.
Proof.
  intros [chi H| | | |chi n H];
    [now apply equality_base_closed|apply ir_closed|apply empty_ax_closed|
     apply adjunction_ax_closed|exact H].
Qed.

(** Finite proof constructions.  A witness context is retained explicitly,
    so these statements provide derivations rather than only consequences
    about consistency. *)
Lemma closed_context_shift G :
  (forall phi, In phi G -> bounded 0 phi) ->
  map (subst_form ↑) G = G.
Proof.
  intro HG. induction G as [|phi G IH]; cbn; [reflexivity|].
  rewrite bounded_0_subst by (apply HG; now left).
  f_equal. apply IH. intros psi Hpsi. apply HG. now right.
Qed.

Lemma derivable_axiom T phi : T phi -> derivable T phi.
Proof.
  intro H. exists [phi]. split.
  - intros psi [<-|[]]. exact H.
  - apply Ctx. now left.
Qed.

Lemma derivable_mp T phi psi :
  derivable T (phi → psi) -> derivable T phi -> derivable T psi.
Proof.
  intros [G [HG Himp]] [H [HH Hphi]]. exists (G ++ H). split.
  - intros chi Hchi. apply in_app_or in Hchi as [Hchi|Hchi];
      [now apply HG|now apply HH].
  - eapply IE.
    + eapply Weak; [exact Himp|]. intros chi Hchi.
      apply in_or_app. now left.
    + eapply Weak; [exact Hphi|]. intros chi Hchi.
      apply in_or_app. now right.
Qed.

Lemma derivable_generalize T phi :
  (forall psi, T psi -> bounded 0 psi) ->
  derivable T phi -> derivable T (∀ phi).
Proof.
  intros HT [G [HG Hphi]]. exists G. split; [exact HG|].
  apply AllI. rewrite closed_context_shift; [exact Hphi|].
  intros psi Hpsi. apply HT, HG, Hpsi.
Qed.

Lemma compact_generalize phi :
  derivable compact_theory phi -> derivable compact_theory (∀ phi).
Proof. apply derivable_generalize, compact_theory_closed. Qed.

Lemma compact_pointed_instance n phi :
  bounded (3 + n) phi ->
  derivable compact_theory (forall_times n (pointed_ax phi)).
Proof.
  intro H. apply derivable_axiom, compact_pointed.
  now apply pointed_instance_closed.
Qed.

(** Atomic vacuity in a fresh binder is a constructed pure-logic proof.
    Freshness is represented by shifting all free indices past the binder. *)
Lemma fresh_vacuity G phi : G ⊢238 (phi → ∀ phi[↑]).
Proof. apply II, AllI, Ctx. cbn. now left. Qed.

Lemma all_conj_right G phi psi :
  G ⊢238 ∀ (phi ∧ psi) -> G ⊢238 ∀ psi.
Proof.
  intro H. apply AllI_named. intro t. exact (CE2 (AllE t H)).
Qed.

Lemma collided_to_singleton G phi :
  G ⊢238 collided_body phi -> G ⊢238 singleton_filter_body phi.
Proof.
  intro H. apply CI.
  - eapply all_conj_right. exact (CE1 H).
  - exact (CE2 H).
Qed.

Lemma ir_guard G t phi :
  G ⊢238 ir -> G ⊢238 (R t t → phi).
Proof.
  intro H. apply II, Exp. eapply IE.
  - eapply Weak; [exact (AllE t H)|]. intros psi Hpsi. now right.
  - apply Ctx. now left.
Qed.

Lemma singleton_to_collided G phi :
  G ⊢238 ir -> G ⊢238 singleton_filter_body phi ->
  G ⊢238 collided_body phi.
Proof.
  intros HIR HS. apply CI.
  - apply AllI_named. intro t. apply CI.
    + apply ir_guard. exact HIR.
    + exact (AllE t (CE1 HS)).
  - exact (CE2 HS).
Qed.

Lemma collided_body_equiv G phi : G ⊢238 ir ->
  (G ⊢238 collided_body phi <-> G ⊢238 singleton_filter_body phi).
Proof.
  intro HIR. split; [apply collided_to_singleton|apply singleton_to_collided, HIR].
Qed.

(** Concrete arithmetic representative formulas.  A representative is a
    transitive set whose members are transitive, linearly ordered by
    membership, and whose nonempty internal subsets have least and greatest
    elements.  Equality here is raw first-order equality; numerical equality
    will require order-isomorphism graphs, not raw extensionality.

    [raw_successor a b] and [raw_zero a] are relations, not functions. *)
Definition raw_zero (a : set_term) : set_form := ∀ ¬ R a`[↑] $0.
Definition raw_successor (a b : set_term) : set_form :=
  ∀ (R b`[↑] $0 ↔ (R a`[↑] $0 ∨ E $0 a`[↑])).
Definition subset (a b : set_term) : set_form :=
  ∀ (R a`[↑] $0 → R b`[↑] $0).
Definition transitive (a : set_term) : set_form :=
  ∀ ∀ ((R a`[↑]`[↑] $1 ∧ R $1 $0) → R a`[↑]`[↑] $0).
Definition member_transitive (a : set_term) : set_form :=
  ∀ (R a`[↑] $0 → transitive $0).
Definition member_linear (a : set_term) : set_form :=
  ∀ ∀ ((R a`[↑]`[↑] $1 ∧ R a`[↑]`[↑] $0) →
       (E $1 $0 ∨ (R $0 $1 ∨ R $1 $0))).
Definition nonempty (a : set_term) : set_form := ∃ R a`[↑] $0.
Definition least (s m : set_term) : set_form :=
  R s m ∧ ∀ (R s`[↑] $0 → (E m`[↑] $0 ∨ R $0 m`[↑])).
Definition greatest (s m : set_term) : set_form :=
  R s m ∧ ∀ (R s`[↑] $0 → (E $0 m`[↑] ∨ R m`[↑] $0)).
Definition internal_extrema (a : set_term) : set_form :=
  ∀ ((subset $0 a`[↑] ∧ nonempty $0) →
       (∃ least $1 $0) ∧ (∃ greatest $1 $0)).
Definition representative (a : set_term) : set_form :=
  transitive a ∧
  (member_transitive a ∧ (member_linear a ∧ internal_extrema a)).

(** An ambient induction instance, retaining an arbitrary property and its
    full parameter tail.  Property slots are $0 = representative and
    $(1+k) = extra parameter k.  The successor clause uses
    predecessor $1, successor $0, parameters $(2+k). *)
Definition predecessor_slots : nat -> set_term :=
  $1 .: (fun k => $(2 + k)).
Definition successor_slots : nat -> set_term :=
  $0 .: (fun k => $(2 + k)).
Definition representative_induction (phi : set_form) : set_form :=
  ((∀ ((representative $0 ∧ raw_zero $0) → phi)) ∧
   (∀ ∀ ((representative $1 ∧
            (representative $0 ∧ raw_successor $1 $0)) →
           (phi[predecessor_slots] → phi[successor_slots])))) →
  ∀ (representative $0 → phi).

Lemma representative_bounded : bounded 1 (representative $0).
Proof.
  unfold representative, transitive, member_transitive, member_linear,
    internal_extrema, subset, nonempty, least, greatest, R, E.
  cbn. fixed_bounds.
Qed.

Lemma representative_subst t sigma :
  (representative t)[sigma] = representative t`[sigma].
Proof.
  unfold representative, transitive, member_transitive, member_linear,
    internal_extrema, subset, nonempty, least, greatest, R, E.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma raw_successor_subst a b sigma :
  (raw_successor a b)[sigma] = raw_successor a`[sigma] b`[sigma].
Proof.
  unfold raw_successor, R, E. cbn. now rewrite !up_term.
Qed.

(** A first arithmetic axiom derivation.  Every raw successor contains its
    predecessor, so it cannot be a raw zero.  This uses reflexivity and the
    displayed successor/zero formulas; it needs no extensionality and no
    choice of a unique successor witness. *)
Lemma successor_contains_predecessor G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 raw_successor a b -> G ⊢238 R b a.
Proof.
  intros HE HS. unfold raw_successor in HS.
  pose proof (AllE a HS) as H.
  cbn [subst_form R E terms2 Vector.map] in H.
  rewrite !subst_term_shift in H.
  eapply IE; [exact (CE2 H)|].
  apply DI2. exact (AllE a HE).
Qed.

Lemma zero_excludes_member G b t :
  G ⊢238 raw_zero b -> G ⊢238 ¬ R b t.
Proof.
  intro H. unfold raw_zero in H. pose proof (AllE t H) as Ht.
  cbn [subst_form R terms2 Vector.map] in Ht.
  rewrite subst_term_shift in Ht. exact Ht.
Qed.

Lemma successor_not_zero G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 (raw_successor a b → ¬ raw_zero b).
Proof.
  intro HE. apply II, II. eapply IE.
  - apply zero_excludes_member. apply Ctx. now left.
  - apply successor_contains_predecessor.
    + eapply Weak; [exact HE|]. intros phi Hphi. right. now right.
    + apply Ctx. right. now left.
Qed.

Lemma compact_successor_not_zero a b :
  derivable compact_theory (raw_successor a b → ¬ raw_zero b).
Proof.
  exists [∀ E $0 $0]. split.
  - intros phi [<-|[]]. apply compact_equality. now left.
  - apply successor_not_zero, Ctx. now left.
Qed.

Lemma representative_at t : (representative $0)[t..] = representative t.
Proof. rewrite representative_subst. reflexivity. Qed.

Lemma representative_term_bounded n t :
  bounded_t n t -> bounded n (representative t).
Proof.
  intro Ht. rewrite <- representative_at.
  eapply subst_bounded_max; [|exact representative_bounded].
  intros i Hi. assert (i = 0) by lia. subst i. exact Ht.
Qed.

Lemma representative_induction_bounded n phi :
  bounded (1 + n) phi -> bounded n (representative_induction phi).
Proof.
  intro Hphi. unfold representative_induction, representative,
    raw_zero, raw_successor, transitive, member_transitive, member_linear,
    internal_extrema, subset, nonempty, least, greatest, R, E.
  cbn. fixed_bounds.
  all: first [exact Hphi |
              eapply subst_bounded_max; [|exact Hphi]].
  all: intros [|k] Hk; cbn [predecessor_slots successor_slots scons];
       constructor; lia.
Qed.

Lemma representative_induction_closed n phi :
  bounded (1 + n) phi ->
  bounded 0 (forall_times n (representative_induction phi)).
Proof.
  intro Hphi. apply forall_times_closed, representative_induction_bounded, Hphi.
Qed.

Print Assumptions collided_body_equiv.
Print Assumptions compact_generalize.
Print Assumptions compact_successor_not_zero.
Print Assumptions representative_induction_closed.

End Compact238.
