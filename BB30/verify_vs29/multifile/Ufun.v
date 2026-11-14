(** * Ordinal-free functionals U_k and their link to the fast-growing hierarchy

      U 0 psi n = psi^n(n),     U (k+1) psi n = ((U k)^n psi)(n).
    For psi = f_b (with b + omega^k in normal form), U k psi = f_(b + omega^k); in particular
      U_FGH : U k S n = f_(omega^k)(n),     U_w_w : U n S n = f_(omega^omega)(n)  (e.g. U 3 S 3).
    Function-level facts (no ordinals): U k preserves "monotone and inflationary" ([goodf]),
    U k psi x >= psi x for x >= 1, and U k is monotone in psi ([U_fun_mono]). *)

From Coq Require Import Arith Lia.
From BB8 Require Import Ord.
Set Default Goal Selector "!".

Fixpoint U (k : nat) (psi : nat -> nat) (n : nat) : nat :=
  match k with
  | O => Nat.iter n psi n
  | S k' => Nat.iter n (U k') psi n
  end.

Lemma U_0 : forall psi n, U 0 psi n = Nat.iter n psi n.
Proof. reflexivity. Qed.

Lemma U_S : forall k psi n, U (S k) psi n = Nat.iter n (U k) psi n.
Proof. reflexivity. Qed.

(** ** Extensionality (no functional extensionality axiom needed) *)

Lemma U_ext : forall k phi psi, (forall x, phi x = psi x) -> forall n, U k phi n = U k psi n.
Proof.
  induction k as [|k IH]; intros phi psi H n; [apply iter_ext; exact H|].
  rewrite !U_S.
  assert (E : forall j x, Nat.iter j (U k) phi x = Nat.iter j (U k) psi x).
  { induction j as [|j IHj]; intro x; [apply H|]. simpl. apply IH. exact IHj. }
  apply E.
Qed.

(** ** The bridge to FGH *)

Lemma all_ge_app : forall y x z, all_ge y (oapp x z) <-> all_ge y x /\ all_ge y z.
Proof.
  intros y x z. induction x as [|a _ b IHb]; simpl; [tauto|]. rewrite IHb. tauto.
Qed.

Lemma all_ge_pow_weaken : forall c c' x, all_ge (opow c) x -> ole c' c -> all_ge (opow c') x.
Proof.
  intros c c' x. induction x as [|a _ b IHb]; simpl; [tauto|].
  intros [H1 H2] Hc. split; [eapply ole_trans; eauto | apply IHb; assumption].
Qed.

Lemma all_ge_orep : forall c j x, all_ge (opow c) x -> all_ge (orep c j oz) x.
Proof.
  intros c j x. induction x as [|a _ b IHb]; simpl; [tauto|].
  intros [H1 H2]. split; [destruct j; simpl; [exact I | exact H1] | apply IHb; exact H2].
Qed.

Lemma all_ge_orep_self : forall c j, all_ge (opow c) (orep c j oz).
Proof. intros c j. induction j as [|j IH]; simpl; [exact I | split; [apply ole_refl | exact IH]]. Qed.

Lemma olt_ofin_S : forall k, olt (ofin k) (ofin (S k)).
Proof.
  unfold ofin. induction k as [|k IH]; [apply olt_z|].
  change (olt (ow oz (orep oz k oz)) (ow oz (orep oz (S k) oz))). apply olt_tail. exact IH.
Qed.

Lemma goodf_FGH : forall b, nf b ->
  (forall x y, x <= y -> FGH b x <= FGH b y) /\ (forall x, x <= FGH b x).
Proof. intros b Hb. split; intros; [apply FGH_mono | apply FGH_ge]; assumption. Qed.

(** U k f_b = f_(b + omega^k) *)
Theorem U_FGH_gen : forall k b psi n, nf b -> all_ge (opow (ofin k)) b ->
  (forall x, psi x = FGH b x) -> U k psi n = FGH (oapp b (opow (ofin k))) n.
Proof.
  induction k as [|k IH]; intros b psi n Hb Hg Hpsi.
  - rewrite U_0, (iter_ext psi (FGH b)) by exact Hpsi.
    change (oapp b (opow (ofin 0))) with (osucc b). rewrite FGH_osucc by exact Hb. reflexivity.
  - rewrite U_S.
    assert (Hgk : all_ge (opow (ofin k)) b)
      by (eapply all_ge_pow_weaken; [exact Hg | right; apply olt_ofin_S]).
    assert (It : forall j x, Nat.iter j (U k) psi x = FGH (oapp b (orep (ofin k) j oz)) x).
    { induction j as [|j IHj]; intro x; [simpl; rewrite oapp_oz_r; apply Hpsi|].
      change (Nat.iter (S j) (U k) psi x) with (U k (Nat.iter j (U k) psi) x).
      rewrite (IH (oapp b (orep (ofin k) j oz))).
      - rewrite oapp_assoc, <- orep_S_app. reflexivity.
      - apply nf_oapp; [exact Hb | apply nf_orep0; apply nf_ofin | apply all_ge_orep; exact Hgk].
      - apply all_ge_app. split; [exact Hgk | apply all_ge_orep_self].
      - exact IHj. }
    rewrite It. rewrite (ofin_S k). rewrite FGH_app_succ_exp; [reflexivity|].
    rewrite <- ofin_S. apply nf_oapp; [exact Hb | apply nf_opow; apply nf_ofin | exact Hg].
Qed.

(** U k S = f_(omega^k) *)
Theorem U_FGH : forall k n, U k S n = FGH (opow (ofin k)) n.
Proof.
  intros k n. apply (U_FGH_gen k oz S n nf_z I). intro x. symmetry. apply FGH_zero.
Qed.

(** f_(omega^omega)(n) = U n S n;  e.g. f_(omega^omega)(3) = U 3 S 3 *)
Theorem U_w_w : forall n, FGH (tower 2) n = U n S n.
Proof. intro n. rewrite FGH_w_w, U_FGH. reflexivity. Qed.

Example U_w_w_3 : FGH (tower 2) 3 = U 3 S 3.
Proof. apply U_w_w. Qed.

(** ** Function-level properties *)

Definition goodf (g : nat -> nat) : Prop :=
  (forall a b, a <= b -> g a <= g b) /\ (forall a, a <= g a).

Lemma goodf_S : goodf S.
Proof. split; intros; lia. Qed.

Lemma goodf_FGH' : forall b, nf b -> goodf (FGH b).
Proof. intros b Hb. apply goodf_FGH. exact Hb. Qed.

Lemma U_props : forall k,
  (forall psi, goodf psi -> goodf (U k psi)) /\
  (forall psi x, goodf psi -> 1 <= x -> psi x <= U k psi x).
Proof.
  induction k as [|k [G H]].
  - split.
    + intros psi [Hm Hi]. split; intros; rewrite ?U_0; [apply iter_mono; assumption | apply iter_ge; exact Hi].
    + intros psi x [Hm Hi] Hx. rewrite U_0. apply iter_succ_ge; assumption.
  - assert (IG : forall j psi, goodf psi -> goodf (Nat.iter j (U k) psi)).
    { induction j as [|j IHj]; intros psi Hp; [exact Hp | apply G; apply IHj; exact Hp]. }
    assert (IW : forall j psi x, goodf psi -> 1 <= x -> psi x <= Nat.iter j (U k) psi x).
    { induction j as [|j IHj]; intros psi x Hp Hx; [simpl; lia|].
      eapply Nat.le_trans; [apply IHj; assumption|]. apply H; [apply IG; exact Hp | exact Hx]. }
    assert (IC : forall j j' psi x, goodf psi -> 1 <= x -> j <= j' ->
                 Nat.iter j (U k) psi x <= Nat.iter j' (U k) psi x).
    { intros j j' psi x Hp Hx Hj. replace j' with ((j' - j) + j) by lia. rewrite Nat.iter_add.
      apply IW; [apply IG; exact Hp | exact Hx]. }
    split.
    + intros psi Hp. split.
      * intros a b Hab. rewrite !U_S.
        eapply Nat.le_trans; [apply (proj1 (IG a psi Hp)); exact Hab|].
        destruct b as [|b]; [assert (a = 0) by lia; subst; lia|]. apply IC; [exact Hp | lia | exact Hab].
      * intro a. rewrite U_S. apply (proj2 (IG a psi Hp)).
    + intros psi x Hp Hx. rewrite U_S. apply IW; assumption.
Qed.

Theorem U_good : forall k psi, goodf psi -> goodf (U k psi).
Proof. intro k. apply (U_props k). Qed.

Theorem U_ge_fun : forall k psi x, goodf psi -> 1 <= x -> psi x <= U k psi x.
Proof. intro k. apply (U_props k). Qed.

Lemma iter_le_fun : forall (psi phi : nat -> nat), (forall a b, a <= b -> psi a <= psi b) ->
  (forall x, psi x <= phi x) -> forall j x, Nat.iter j psi x <= Nat.iter j phi x.
Proof.
  intros psi phi Hm H j x. induction j as [|j IH]; simpl; [lia|].
  eapply Nat.le_trans; [apply Hm; exact IH | apply H].
Qed.

(** U k is monotone in its function argument *)
Theorem U_fun_mono : forall k psi phi, goodf psi -> (forall x, psi x <= phi x) ->
  forall n, U k psi n <= U k phi n.
Proof.
  induction k as [|k IH]; intros psi phi Hp H n.
  - rewrite !U_0. apply iter_le_fun; [apply Hp | exact H].
  - rewrite !U_S.
    assert (E : forall j x, Nat.iter j (U k) psi x <= Nat.iter j (U k) phi x).
    { induction j as [|j IHj]; intro x; [apply H|]. simpl. apply IH; [| exact IHj].
      clear IHj x. induction j as [|j IHj]; [exact Hp | apply U_good; exact IHj]. }
    apply E.
Qed.

Theorem U_mono : forall k psi n n', goodf psi -> n <= n' -> U k psi n <= U k psi n'.
Proof. intros k psi n n' Hp. apply (U_good k psi Hp). Qed.

(** ** The BB29 closed-form functionals T (from the analysis, BB29/analysis/REPORT.md)

      T 0 phi m = phi^(m+3)(m+1),     T (k+1) phi m = ((T k)^(m+3) phi)(m+1).
    BB29's score is sigma = T 4 S 1 + 1.  Main facts: T k preserves [goodf], T k phi >= phi,
    [T_ge_U]: U k psi (x+1) <= T k phi x whenever psi <= phi (both goodf), and
    [T4_ge_f_w_w]: f_(omega^omega)(3) <= T 4 S 1. *)

Fixpoint T (k : nat) (phi : nat -> nat) (m : nat) : nat :=
  match k with
  | O => Nat.iter (m + 3) phi (m + 1)
  | S k' => Nat.iter (m + 3) (T k') phi (m + 1)
  end.

Lemma T_0 : forall phi m, T 0 phi m = Nat.iter (m + 3) phi (m + 1).
Proof. reflexivity. Qed.

Lemma T_S : forall k phi m, T (S k) phi m = Nat.iter (m + 3) (T k) phi (m + 1).
Proof. reflexivity. Qed.

Lemma T_props : forall k,
  (forall chi, goodf chi -> goodf (T k chi)) /\
  (forall chi y, goodf chi -> chi y <= T k chi y).
Proof.
  induction k as [|k [G H]].
  - split.
    + intros chi [Hm Hi]. split.
      * intros a b Hab. rewrite !T_0. apply iter_mono; [exact Hm | exact Hi | lia | lia].
      * intro a. rewrite T_0. eapply Nat.le_trans; [| apply iter_ge; exact Hi]. lia.
    + intros chi y [Hm Hi]. rewrite T_0.
      eapply Nat.le_trans; [apply Hm; apply (Nat.le_succ_diag_r y)|].
      replace (y + 1) with (S y) by lia. apply iter_succ_ge; [exact Hi | lia].
  - assert (IG : forall j chi, goodf chi -> goodf (Nat.iter j (T k) chi)).
    { induction j as [|j IHj]; intros chi Hc; [exact Hc | apply G; apply IHj; exact Hc]. }
    assert (IW : forall j chi y, goodf chi -> chi y <= Nat.iter j (T k) chi y).
    { induction j as [|j IHj]; intros chi y Hc; [simpl; lia|].
      eapply Nat.le_trans; [apply IHj; exact Hc|]. apply H. apply IG. exact Hc. }
    assert (IC : forall j j' chi y, goodf chi -> j <= j' ->
                 Nat.iter j (T k) chi y <= Nat.iter j' (T k) chi y).
    { intros j j' chi y Hc Hj. replace j' with ((j' - j) + j) by lia. rewrite Nat.iter_add.
      apply IW. apply IG. exact Hc. }
    split.
    + intros chi Hc. split.
      * intros a b Hab. rewrite !T_S.
        eapply Nat.le_trans; [apply (proj1 (IG (a + 3) chi Hc) (a + 1) (b + 1)); lia|].
        apply IC; [exact Hc | lia].
      * intro a. rewrite T_S. eapply Nat.le_trans; [| apply (proj2 (IG (a + 3) chi Hc))]. lia.
    + intros chi y Hc. rewrite T_S.
      eapply Nat.le_trans; [apply (proj1 Hc); apply (Nat.le_succ_diag_r y)|].
      replace (y + 1) with (S y) by lia. apply IW. exact Hc.
Qed.

Theorem T_good : forall k chi, goodf chi -> goodf (T k chi).
Proof. intro k. apply (T_props k). Qed.

Theorem T_ge_fun : forall k chi y, goodf chi -> chi y <= T k chi y.
Proof. intro k. apply (T_props k). Qed.

Lemma iter_T_good : forall k j chi, goodf chi -> goodf (Nat.iter j (T k) chi).
Proof. intros k j. induction j as [|j IH]; intros chi Hc; [exact Hc | apply T_good; apply IH; exact Hc]. Qed.

Lemma iter_U_good : forall k j chi, goodf chi -> goodf (Nat.iter j (U k) chi).
Proof. intros k j. induction j as [|j IH]; intros chi Hc; [exact Hc | apply U_good; apply IH; exact Hc]. Qed.

Lemma iter_T_ge : forall k j chi y, goodf chi -> chi y <= Nat.iter j (T k) chi y.
Proof.
  intros k j. induction j as [|j IH]; intros chi y Hc; [simpl; lia|].
  eapply Nat.le_trans; [apply IH; exact Hc|].
  apply (T_ge_fun k (Nat.iter j (T k) chi) y). apply iter_T_good. exact Hc.
Qed.

(** T k phi x >= U k psi (x+1) *)
Theorem T_ge_U : forall k phi psi, goodf phi -> goodf psi -> (forall x, psi x <= phi x) ->
  forall x, U k psi (x + 1) <= T k phi x.
Proof.
  induction k as [|k IH]; intros phi psi Hphi Hpsi H x.
  - rewrite U_0, T_0. eapply Nat.le_trans; [apply iter_le_fun; [apply Hpsi | exact H]|].
    apply iter_mono; [apply Hphi | apply Hphi | lia | lia].
  - rewrite U_S, T_S.
    assert (E : forall j y, Nat.iter j (U k) psi y <= Nat.iter j (T k) phi y).
    { induction j as [|j IHj]; intro y; [apply H|]. simpl.
      eapply Nat.le_trans; [apply (U_mono k _ y (y + 1)); [apply iter_U_good; exact Hpsi | lia]|].
      apply IH; [apply iter_T_good; exact Hphi | apply iter_U_good; exact Hpsi | exact IHj]. }
    eapply Nat.le_trans; [apply E|].
    replace (x + 3) with (2 + (x + 1)) by lia. rewrite (Nat.iter_add 2 (x + 1)).
    assert (W : forall j chi y, goodf chi -> chi y <= Nat.iter j (T k) chi y).
    { induction j as [|j IHj]; intros chi y Hc; [simpl; lia|].
      eapply Nat.le_trans; [apply IHj; exact Hc|]. apply T_ge_fun. apply iter_T_good. exact Hc. }
    apply (W 2 (Nat.iter (x + 1) (T k) phi) (x + 1)). apply iter_T_good. exact Hphi.
Qed.

Corollary T_ge_FGH : forall k x, FGH (opow (ofin k)) (x + 1) <= T k S x.
Proof. intros k x. rewrite <- U_FGH. apply T_ge_U; [apply goodf_S | apply goodf_S | lia]. Qed.

(** BB29: sigma - 1 = T 4 S 1 >= f_(omega^omega)(3) *)
Theorem T4_ge_f_w_w : FGH (tower 2) 3 <= T 4 S 1.
Proof.
  (* unfold one level by rewriting only: never let conversion evaluate T 4 S 1 *)
  rewrite U_w_w, (T_S 3 S 1). change (1 + 3) with 4. change (1 + 1) with 2.
  rewrite (Nat.iter_succ 3 (nat -> nat) (T 3) S).
  assert (Hg : goodf (Nat.iter 3 (T 3) S)) by (apply iter_T_good; apply goodf_S).
  eapply Nat.le_trans; [| apply (T_ge_U 3 _ _ Hg Hg (fun x => le_n _) 2)].
  apply U_fun_mono; [apply goodf_S|]. intro x.
  apply (iter_T_ge 3 3 S x). apply goodf_S.
Qed.
