(** * BB29: exact score and the lower bound sigma > f_(omega^omega)(3)  (BB29/analysis/REPORT.md sections 5-6).

    The halting configuration [c_end (W [4] 1)] carries exactly W([4])(1) + 1 = T_4(S)(1) + 1 ones
    (the head reads 0 in state B; B0 is undefined).  Under the convention "the halting transition
    writes a 1" the score is one more; the bound below holds for either convention. *)

From BB8 Require Import BB29_tm BB29_rules BB29_scan BB29_round BB29_hydra BB29_halt Ord.
From Coq Require Import Lia List PeanoNat.
Import ListNotations.
Set Default Goal Selector "!".

(** ** Ones on the tape (as in bb8_list/proofs/BB11_M11_fgh.v) *)

Definition sym_val (s : Sym) : nat := match s with S0 => 0 | S1 => 1 end.

Fixpoint count1 (xs : list Sym) : nat :=
  match xs with [] => 0 | x :: t => sym_val x + count1 t end.

(** [ones c N]: the tape of [c] is a finite word padded with 0s on both sides, with N ones. *)
Definition ones (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl; [reflexivity | rewrite IHxs; lia]. Qed.

Lemma count1_pow : forall xs n, count1 (xs ^^ n) = n * count1 xs.
Proof. induction n; simpl; [reflexivity | rewrite count1_app, IHn; lia]. Qed.

Lemma ls_repeatO : forall n l, ls l (repeat pO n) = [1; 0]^^n *> l.
Proof.
  induction n as [|n IH]; intros l; [reflexivity|].
  cbn [repeat ls]. rewrite IH. change (bL pO) with [1; 0 : Sym].
  rewrite <- Str_app_assoc, lpow_shift. reflexivity.
Qed.

Lemma ones_c_end : forall a, ones (c_end a) (S a).
Proof.
  intros a. exists qB, (0 :: [1; 0]^^(S a)), [0; 0], 0. split.
  - unfold c_end. rewrite ls_snoc, ls_repeatO. reflexivity.
  - cbn [count1 sym_val]. rewrite count1_pow. cbn [count1 sym_val]. lia.
Qed.

(** From here on numerals are natural numbers. *)
Local Open Scope nat_scope.

(** ** Exact score *)

Lemma W_4 : W [4] = T 4 S.
Proof. change [4] with ([] ++ [4]). rewrite W_snoc, W_nil. reflexivity. Qed.

(** sigma (ones at halt) = T_4(S)(1) + 1 = T_3(T_3^3(S))(2) + 1. *)
Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (T 4 S 1 + 1).
Proof.
  exists (c_end (W [4] 1)). split; [apply reach_end|]. split; [apply c_end_halted|].
  rewrite Nat.add_1_r, <- W_4. apply ones_c_end.
Qed.

Lemma T4_unfold : T 4 S 1 = T 3 (Nat.iter 3 (T 3) S) 2.
Proof. rewrite TS_eq. reflexivity. Qed.

(** ** Monotone, inflationary functions *)

Definition mono (f : nat -> nat) : Prop := forall x y, x <= y -> f x <= f y.
Definition infl (f : nat -> nat) : Prop := forall x, x <= f x.
Definition G (f : nat -> nat) : Prop := mono f /\ infl f.

Lemma G_S : G S.
Proof. split; [intros x y H; lia | intros x; lia]. Qed.

Lemma iter_G : forall f n, G f -> G (Nat.iter n f).
Proof.
  intros f n [Hm Hi]. split.
  - intros x y Hxy. apply iter_mono_arg; assumption.
  - intros x. apply iter_ge; assumption.
Qed.

Lemma iter_le_fun : forall f g, mono g -> (forall x, f x <= g x) -> forall n x, Nat.iter n f x <= Nat.iter n g x.
Proof.
  intros f g Hg Hfg n. induction n as [|n IH]; intros x; simpl; [lia|].
  eapply Nat.le_trans; [apply Hfg | apply Hg, IH].
Qed.

(** ** The Wainer-style functionals below omega^omega:
    U_0(psi)(n) = psi^n(n),  U_(k+1)(psi)(n) = (U_k)^n(psi)(n). *)
Fixpoint U (k : nat) (psi : nat -> nat) : nat -> nat :=
  match k with
  | O => fun n => Nat.iter n psi n
  | S k' => fun n => Nat.iter n (U k') psi n
  end.

Lemma U0_eq : forall psi n, U 0 psi n = Nat.iter n psi n.
Proof. reflexivity. Qed.
Lemma US_eq : forall k psi n, U (S k) psi n = Nat.iter n (U k) psi n.
Proof. reflexivity. Qed.

Lemma U_ext : forall k f g, (forall x, f x = g x) -> forall x, U k f x = U k g x.
Proof.
  induction k as [|k IH]; intros f g Hfg x.
  - rewrite !U0_eq. apply iter_ext. exact Hfg.
  - rewrite !US_eq.
    assert (Hj : forall j y, Nat.iter j (U k) f y = Nat.iter j (U k) g y).
    { induction j as [|j IHj]; intros y; [apply Hfg|]. simpl. apply IH. exact IHj. }
    apply Hj.
Qed.

(** U_k preserves G, and U_k psi >= psi on arguments >= 1. *)
Lemma U_props : forall k psi, G psi -> G (U k psi) /\ (forall x, 1 <= x -> psi x <= U k psi x).
Proof.
  induction k as [|k IH]; intros psi [Hm Hi].
  - split; [split|].
    + intros x y Hxy. rewrite !U0_eq. apply iter_mono; assumption.
    + intros x. rewrite U0_eq. apply iter_ge. exact Hi.
    + intros x Hx. rewrite U0_eq. apply iter_succ_ge; assumption.
  - set (P j := Nat.iter j (U k) psi).
    assert (HG : forall j, G (P j)).
    { induction j as [|j IHj]; [split; assumption | apply (IH (P j) IHj)]. }
    assert (Hch : forall j j' x, j <= j' -> 1 <= x -> P j x <= P j' x).
    { intros j j' x Hjj' Hx. induction Hjj' as [|j' Hjj' IHj]; [lia|].
      eapply Nat.le_trans; [exact IHj|]. apply (IH (P j') (HG j')). exact Hx. }
    split; [split|].
    + intros x y Hxy. rewrite !US_eq. fold (P x) (P y).
      destruct x as [|x].
      * destruct y as [|y]; [lia|]. change (P 0 0) with (psi 0).
        eapply Nat.le_trans; [apply (Hm 0 (S y)); lia|]. change (psi (S y)) with (P 0 (S y)).
        apply Hch; lia.
      * eapply Nat.le_trans; [apply (proj1 (HG (S x))); exact Hxy|]. apply Hch; lia.
    + intros x. rewrite US_eq. fold (P x). apply (proj2 (HG x)).
    + intros x Hx. rewrite US_eq. fold (P x). change (psi x) with (P 0 x). apply Hch; lia.
Qed.

Lemma U_G : forall k psi, G psi -> G (U k psi).
Proof. intros. apply U_props. assumption. Qed.

(** T_k preserves G, and T_k chi >= chi everywhere. *)
Lemma T_props : forall k phi, G phi -> G (T k phi) /\ (forall x, phi x <= T k phi x).
Proof.
  induction k as [|k IH]; intros phi [Hm Hi].
  - split; [split|].
    + intros x y Hxy. rewrite !T0_eq. apply iter_mono; [assumption | assumption | lia | lia].
    + intros x. rewrite T0_eq. eapply Nat.le_trans; [| apply iter_ge; exact Hi]. lia.
    + intros x. rewrite T0_eq. eapply Nat.le_trans; [apply (Hm x (S x)); lia|].
      apply iter_succ_ge; [exact Hi | lia].
  - set (P j := Nat.iter j (T k) phi).
    assert (HG : forall j, G (P j)).
    { induction j as [|j IHj]; [split; assumption | apply (IH (P j) IHj)]. }
    assert (Hch : forall j j' x, j <= j' -> P j x <= P j' x).
    { intros j j' x Hjj'. induction Hjj' as [|j' Hjj' IHj]; [lia|].
      eapply Nat.le_trans; [exact IHj|]. apply (IH (P j') (HG j')). }
    split; [split|].
    + intros x y Hxy. rewrite !TS_eq. fold (P (S (S (S x)))) (P (S (S (S y)))).
      eapply Nat.le_trans; [apply (proj1 (HG (S (S (S x))))); apply (le_n_S x y Hxy)|].
      apply Hch; lia.
    + intros x. rewrite TS_eq. fold (P (S (S (S x)))). eapply Nat.le_trans; [| apply (proj2 (HG _))]. lia.
    + intros x. rewrite TS_eq. fold (P (S (S (S x)))).
      eapply Nat.le_trans; [apply (Hm x (S x)); lia|]. change (phi (S x)) with (P 0 (S x)). apply Hch; lia.
Qed.

Lemma T_G : forall k phi, G phi -> G (T k phi).
Proof. intros. apply T_props. assumption. Qed.

Lemma T_ge : forall k phi, G phi -> forall x, phi x <= T k phi x.
Proof. intros. apply T_props. assumption. Qed.

Lemma iterT_G : forall k j phi, G phi -> G (Nat.iter j (T k) phi).
Proof. intros k j phi H. induction j as [|j IH]; [exact H | apply T_G, IH]. Qed.

Lemma iterT_ge : forall k j phi, G phi -> forall x, phi x <= Nat.iter j (T k) phi x.
Proof.
  intros k j phi H. induction j as [|j IH]; intros x; [apply le_n|].
  eapply Nat.le_trans; [apply IH | apply T_ge, iterT_G, H].
Qed.

(** ** The comparison lemma (BB29/analysis/REPORT.md section 6):
    if psi <= phi pointwise (both monotone and inflationary), then U_k psi (x+1) <= T_k phi x. *)
Lemma compare : forall k phi psi, G phi -> G psi -> (forall x, psi x <= phi x) ->
  forall x, U k psi (S x) <= T k phi x.
Proof.
  induction k as [|k IH]; intros phi psi Hphi Hpsi Hle x.
  - rewrite U0_eq, T0_eq.
    eapply Nat.le_trans; [apply iter_le_fun; [apply Hphi | exact Hle]|].
    apply iter_mono; [apply Hphi | apply Hphi | lia | lia].
  - rewrite US_eq, TS_eq.
    set (phi' := Nat.iter 2 (T k) phi).
    replace (Nat.iter (S (S (S x))) (T k) phi) with (Nat.iter (S x) (T k) phi')
      by (unfold phi'; rewrite <- Nat.iter_add; f_equal; lia).
    assert (Hphi' : G phi') by (apply iterT_G, Hphi).
    assert (Hle' : forall y, psi y <= phi' y).
    { intros y. eapply Nat.le_trans; [apply Hle | apply iterT_ge, Hphi]. }
    assert (Hj : forall j y, Nat.iter j (U k) psi y <= Nat.iter j (T k) phi' y /\
                             G (Nat.iter j (U k) psi) /\ G (Nat.iter j (T k) phi')).
    { induction j as [|j IHj].
      - intros y. split; [apply Hle' | split; assumption].
      - intros y. destruct (IHj 0) as [_ [HGu HGt]].
        split; [| split; [apply U_G, HGu | apply T_G, HGt]].
        simpl. eapply Nat.le_trans; [apply (proj1 (U_G k _ HGu)); apply (Nat.le_succ_diag_r y)|].
        apply IH; [exact HGt | exact HGu | intros z; apply IHj]. }
    apply Hj.
Qed.

(** sigma - 1 = T_3(T_3^3 S)(2) >= U_3(S)(3). *)
Lemma W4_ge_U3 : U 3 S 3 <= T 4 S 1.
Proof.
  rewrite T4_unfold. apply (compare 3 (Nat.iter 3 (T 3) S) S).
  - apply iterT_G, G_S.
  - apply G_S.
  - intros x. apply (iterT_ge 3 3 S G_S x).
Qed.

(** ** Bridge to the standard fast-growing hierarchy of Ord.v *)

Lemma olt_ofin_S : forall k, olt (ofin k) (ofin (S k)).
Proof.
  induction k as [|k IH]; [apply olt_z|].
  change (ofin (S k)) with (ow oz (ofin k)). change (ofin (S (S k))) with (ow oz (ofin (S k))).
  apply olt_tail. exact IH.
Qed.

Lemma all_ge_mono : forall b c c', ole c' c -> all_ge (opow c) b -> all_ge (opow c') b.
Proof.
  induction b as [|a _ b IH]; intros c c' Hc H; [exact I|].
  destruct H as [Ha Hb]. split; [| eapply IH; eassumption].
  simpl in *. eapply ole_trans; eassumption.
Qed.

Lemma all_ge_oapp : forall y x z, all_ge y x -> all_ge y z -> all_ge y (oapp x z).
Proof. intros y x. induction x as [|a _ b IH]; intros z Hx Hz; [exact Hz|]. destruct Hx. split; auto. Qed.

Lemma all_ge_orep : forall c j, all_ge (opow c) (orep c j oz).
Proof. intros c j. induction j as [|j IH]; [exact I|]. split; [apply ole_refl | exact IH]. Qed.

Lemma all_ge_orep_l : forall c j b, all_ge (opow c) b -> all_ge (orep c j oz) b.
Proof.
  intros c j b. induction b as [|a _ b IH]; intros H; [exact I|].
  destruct H as [Ha Hb]. split; [| apply IH, Hb].
  destruct j; [exact I | exact Ha].
Qed.

(** f_(b + omega^k) = U_k (f_b), for b whose exponents are all >= k. *)
Lemma bridge : forall k b, nf b -> all_ge (opow (ofin k)) b ->
  forall n, FGH (oapp b (opow (ofin k))) n = U k (FGH b) n.
Proof.
  induction k as [|k IH]; intros b Hb Hg n.
  - change (oapp b (opow (ofin 0))) with (osucc b). rewrite FGH_osucc by exact Hb. reflexivity.
  - assert (Hk : all_ge (opow (ofin k)) b)
      by (eapply all_ge_mono; [right; apply olt_ofin_S | exact Hg]).
    assert (Hnf : nf (oapp b (opow (osucc (ofin k))))).
    { rewrite <- ofin_S. apply nf_oapp; [exact Hb | apply nf_opow, nf_ofin | exact Hg]. }
    rewrite ofin_S, FGH_app_succ_exp by exact Hnf. rewrite US_eq.
    assert (Hj : forall j x, FGH (oapp b (orep (ofin k) j oz)) x = Nat.iter j (U k) (FGH b) x).
    { induction j as [|j IHj]; intros x.
      - change (orep (ofin k) 0 oz) with oz. rewrite oapp_oz_r. reflexivity.
      - rewrite orep_S_app, <- oapp_assoc.
        assert (Hb' : nf (oapp b (orep (ofin k) j oz))).
        { apply nf_oapp; [exact Hb | apply nf_orep0, nf_ofin | apply all_ge_orep_l, Hk]. }
        rewrite IH; [| exact Hb' | apply all_ge_oapp; [exact Hk | apply all_ge_orep]].
        simpl. apply U_ext. exact IHj. }
    apply Hj.
Qed.

(** U_k S = f_(omega^k), the standard hierarchy of Ord.v. *)
Theorem U_is_FGH : forall k n, U k S n = FGH (opow (ofin k)) n.
Proof.
  intros k n. symmetry.
  change (opow (ofin k)) with (oapp oz (opow (ofin k))).
  rewrite bridge; [| apply nf_z | exact I].
  apply U_ext. apply FGH_zero.
Qed.

(** f_(omega^omega)(3) = f_(omega^3)(3) = U_3(S)(3). *)
Lemma FGH_w_w_3_U : FGH (tower 2) 3 = U 3 S 3.
Proof. rewrite FGH_w_w, U_is_FGH. reflexivity. Qed.

Global Opaque U.

(** ** Main results *)

(** The halting configuration has N = T_4(S)(1) + 1 ones, and f_(omega^omega)(3) < N.
    (Under the "halting transition writes a 1" convention sigma = N + 1 > N.) *)
Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ FGH (tower 2) 3 < N.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (T 4 S 1 + 1). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  rewrite FGH_w_w_3_U, Nat.add_1_r. apply Nat.lt_succ_r. apply W4_ge_U3.
Qed.

Print Assumptions score_exact.
Print Assumptions sigma_lower_bound.
Print Assumptions U_is_FGH.

(** ** Agreement with Ufun.v (the shared definitions of T and U) *)

From BB8 Require Ufun.

(** Our [T] (BB29_hydra.v) equals [Ufun.T] pointwise (also under pointwise-equal arguments). *)
Lemma T_eq_Ufun_ext : forall k f g, (forall x, f x = g x) -> forall m, T k f m = Ufun.T k g m.
Proof.
  induction k as [|k IH]; intros f g Hfg m.
  - rewrite T0_eq, Ufun.T_0. replace (m + 3) with (S (S (S m))) by lia.
    replace (m + 1) with (S m) by lia. apply iter_ext. exact Hfg.
  - rewrite TS_eq, Ufun.T_S. replace (m + 3) with (S (S (S m))) by lia. replace (m + 1) with (S m) by lia.
    assert (Hj : forall j x, Nat.iter j (T k) f x = Nat.iter j (Ufun.T k) g x).
    { induction j as [|j IHj]; intros x; [apply Hfg|]. simpl. apply IH. exact IHj. }
    apply Hj.
Qed.

Lemma T_eq_Ufun : forall k phi m, T k phi m = Ufun.T k phi m.
Proof. intros. apply T_eq_Ufun_ext. reflexivity. Qed.

Theorem score_exact_Ufun : exists c, c0 -->* c /\ halted tm c /\ ones c (Ufun.T 4 S 1 + 1).
Proof. rewrite <- T_eq_Ufun. exact score_exact. Qed.

(** Same bound, closed through Ufun.T4_ge_f_w_w instead of [compare]/[bridge] above. *)
Theorem sigma_lower_bound_Ufun :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ FGH (tower 2) 3 < N.
Proof.
  destruct score_exact_Ufun as [c [H1 [H2 H3]]].
  exists c, (Ufun.T 4 S 1 + 1). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  rewrite Nat.add_1_r. apply Nat.lt_succ_r. apply Ufun.T4_ge_f_w_w.
Qed.

Print Assumptions sigma_lower_bound_Ufun.
