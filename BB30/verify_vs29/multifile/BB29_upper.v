(** * BB29_upper: an UPPER bound for the exact score of the published BB(29) hydra machine (mxdys).

    Published files used unchanged (busy-beaver BB29/verify/multifile): BB292, Individual292, BB29_tm, BB29_rules,
    BB29_scan, BB29_round, BB29_hydra, BB29_halt, Ord, Ufun, BB29_bound.

    BB29_bound.score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (T 4 S 1 + 1),  with the functional
    T of BB29_hydra.v:  T_0(phi)(m) = phi^(m+3)(m+1),  T_(k+1)(phi)(m) = (T_k)^(m+3)(phi)(m+1).
    This file proves, in the fast-growing hierarchy FGH of Ord.v:

      Theorem T4_upper : T 4 S 1 <= FGH (orep (ofin 3) 7 oz) 26          (f_(omega^3 * 7)(26))
      Theorem halts_with_exact : halts_with NB -> NB = T 4 S 1 + 1     (determinism: every halting run)
      Theorem halts_with_upper : halts_with NB -> NB + 24 <= FGH (opow (ofin 9)) 10.

    Method.  (1) T_k phi <= V_k G whenever phi <= G pointwise and G is monotone and inflationary, where
    V_0 G n = G^(n+3)(n+3), V_(k+1) G n = (V_k)^(n+3) G (n+3) (T with the argument raised to the count).
    (2) V_k only evaluates its base at arguments >= 3, where the shifts are absorbed:
        V_0 (f_b) = f_(b+1)(. + 3),   V_1 (f_b) n <= f_(b+omega)(2n+6),
        V_k (f_b) n <= f_(b+omega^k)(2n+6k)   (1 <= k <= 3 here; absorb_k needs k <= 20),
    with f = FGH and b + omega^k in Cantor normal form.  (3) A descent omega^9 ->_10 omega^3*7 + 1. *)

From BB8 Require Import BB29_tm BB29_rules BB29_scan BB29_round BB29_hydra BB29_halt Ord BB29_bound.
From Coq Require Import Lia List PeanoNat Streams.
Import ListNotations.
Set Default Goal Selector "!".
Local Open Scope nat_scope.

(** ** Part 1: T <= V *)

Definition gd (f : nat -> nat) : Prop := (forall x y, x <= y -> f x <= f y) /\ (forall x, x <= f x).

Fixpoint Vf (k : nat) (G : nat -> nat) : nat -> nat :=
  match k with
  | O => fun n => Nat.iter (n + 3) G (n + 3)
  | S k' => fun n => Nat.iter (n + 3) (Vf k') G (n + 3)
  end.

Lemma Vf0 : forall G n, Vf 0 G n = Nat.iter (n + 3) G (n + 3).
Proof. reflexivity. Qed.

Lemma VfS : forall k G n, Vf (S k) G n = Nat.iter (n + 3) (Vf k) G (n + 3).
Proof. reflexivity. Qed.

Lemma it_mono_x : forall f, (forall x y, x <= y -> f x <= f y) ->
  forall n x y, x <= y -> Nat.iter n f x <= Nat.iter n f y.
Proof. intros f Hf n. induction n as [|n IH]; intros x y H; [exact H|]. rewrite !Nat.iter_succ. apply Hf, IH, H. Qed.

Lemma it_infl : forall f, (forall x, x <= f x) -> forall n x, x <= Nat.iter n f x.
Proof.
  intros f Hf n. induction n as [|n IH]; intros x; [simpl; lia|].
  rewrite Nat.iter_succ. eapply Nat.le_trans; [apply IH | apply Hf].
Qed.

Lemma it_mono_n : forall f, (forall x, x <= f x) -> forall n n' x, n <= n' -> Nat.iter n f x <= Nat.iter n' f x.
Proof.
  intros f Hf n n' x H. induction H as [|n' H IH]; [lia|].
  rewrite Nat.iter_succ. eapply Nat.le_trans; [exact IH | apply Hf].
Qed.

Lemma it_le_fun : forall f g, (forall x y, x <= y -> g x <= g y) -> (forall x, f x <= g x) ->
  forall n x, Nat.iter n f x <= Nat.iter n g x.
Proof.
  intros f g Hg Hfg n. induction n as [|n IH]; intros x; [simpl; lia|].
  rewrite !Nat.iter_succ. eapply Nat.le_trans; [apply Hfg | apply Hg, IH].
Qed.

Lemma gd_iter : forall f n, gd f -> gd (Nat.iter n f).
Proof.
  intros f n [Hm Hi]. split; [intros x y H; apply it_mono_x; assumption | intros x; apply it_infl; exact Hi].
Qed.

Lemma it_first : forall f n x, gd f -> f x <= Nat.iter (S n) f x.
Proof.
  intros f n x [Hm Hi]. rewrite Nat.iter_succ. apply Hm. apply it_infl. exact Hi.
Qed.

Lemma Vf_props : forall k G, gd G -> gd (Vf k G) /\ (forall z, G z <= Vf k G z).
Proof.
  induction k as [|k IH]; intros G HG.
  - pose proof HG as [Hm Hi].
    assert (Hge : forall z, G z <= Vf 0 G z).
    { intros z. rewrite Vf0. apply Nat.le_trans with (m := G (z + 3)); [apply Hm; lia|].
      replace (z + 3) with (S (z + 2)) by lia. apply it_first. exact HG. }
    split; [split|].
    + intros x y H. rewrite !Vf0.
      apply Nat.le_trans with (m := Nat.iter (x + 3) G (y + 3)); [apply it_mono_x; [exact Hm | lia]|].
      apply it_mono_n; [exact Hi | lia].
    + intros x. eapply Nat.le_trans; [apply Hi | apply Hge].
    + exact Hge.
  - assert (HP : forall j, gd (Nat.iter j (Vf k) G)).
    { induction j as [|j IHj]; [exact HG | exact (proj1 (IH _ IHj))]. }
    assert (Hch : forall j j' z, j <= j' -> Nat.iter j (Vf k) G z <= Nat.iter j' (Vf k) G z).
    { intros j j' z H. induction H as [|j' H IHj]; [lia|].
      eapply Nat.le_trans; [exact IHj | exact (proj2 (IH _ (HP j')) z)]. }
    assert (Hge : forall z, G z <= Vf (S k) G z).
    { intros z. rewrite VfS.
      apply Nat.le_trans with (m := Nat.iter 0 (Vf k) G (z + 3)); [simpl; apply (proj1 HG); lia|].
      apply Hch. lia. }
    split; [split|].
    + intros x y H. rewrite !VfS.
      apply Nat.le_trans with (m := Nat.iter (x + 3) (Vf k) G (y + 3)); [apply (proj1 (HP (x + 3))); lia|].
      apply Hch. lia.
    + intros x. eapply Nat.le_trans; [apply (proj2 HG) | apply Hge].
    + exact Hge.
Qed.

Lemma Vf_gd : forall k G, gd G -> gd (Vf k G).
Proof. intros. apply Vf_props. assumption. Qed.

Lemma gd_iterV : forall k G j, gd G -> gd (Nat.iter j (Vf k) G).
Proof. intros k G j HG. induction j as [|j IH]; [exact HG | exact (Vf_gd k _ IH)]. Qed.

Lemma T_le_V : forall k phi G, gd G -> (forall y, phi y <= G y) -> forall m, T k phi m <= Vf k G m.
Proof.
  induction k as [|k IH]; intros phi G HG Hle m.
  - rewrite T0_eq, Vf0. replace (m + 3) with (S (S (S m))) by lia.
    eapply Nat.le_trans; [apply it_le_fun; [apply HG | exact Hle]|].
    apply it_mono_x; [apply HG | lia].
  - rewrite TS_eq, VfS. replace (m + 3) with (S (S (S m))) by lia.
    assert (HI : forall j y, Nat.iter j (T k) phi y <= Nat.iter j (Vf k) G y).
    { induction j as [|j IHj]; intros y; [apply Hle|].
      rewrite !Nat.iter_succ. apply IH; [apply gd_iterV; exact HG | exact IHj]. }
    eapply Nat.le_trans; [apply HI|].
    apply (proj1 (gd_iterV k G (S (S (S m))) HG)). lia.
Qed.

(** V only looks at its base on arguments >= 3. *)
Lemma Vf_mono_base : forall k G G', gd G -> gd G' -> (forall z, 3 <= z -> G z <= G' z) ->
  forall n, Vf k G n <= Vf k G' n.
Proof.
  induction k as [|k IH]; intros G G' HG HG' Hle n.
  - rewrite !Vf0.
    assert (H : forall j x, 3 <= x -> Nat.iter j G x <= Nat.iter j G' x).
    { induction j as [|j IHj]; intros x Hx; [simpl; lia|]. rewrite !Nat.iter_succ.
      eapply Nat.le_trans; [apply Hle; pose proof (it_infl G (proj2 HG) j x); lia|].
      apply (proj1 HG'). apply IHj. exact Hx. }
    apply H. lia.
  - rewrite !VfS.
    assert (H : forall j z, 3 <= z -> Nat.iter j (Vf k) G z <= Nat.iter j (Vf k) G' z).
    { induction j as [|j IHj]; intros z Hz; [exact (Hle z Hz)|].
      rewrite !Nat.iter_succ. apply IH; [apply gd_iterV; exact HG | apply gd_iterV; exact HG' | exact IHj]. }
    apply H. lia.
Qed.

(** ** Part 2: the fast-growing hierarchy (Ord.FGH) *)

Lemma F_gd : forall c, nf c -> gd (FGH c).
Proof. intros c Hc. split; [intros x y H; apply FGH_mono; assumption | intros x; apply FGH_ge; exact Hc]. Qed.

Lemma it_add_ge : forall f, (forall z, 1 <= z -> S z <= f z) -> forall n x, 1 <= x -> n + x <= Nat.iter n f x.
Proof.
  intros f Hf n. induction n as [|n IH]; intros x Hx; [simpl; lia|]. rewrite Nat.iter_succ.
  pose proof (IH x Hx). pose proof (Hf (Nat.iter n f x) ltac:(lia)). lia.
Qed.

Lemma fs_ne_oz' : forall z k, z <> oz -> z <> one -> 1 <= k -> fs z k <> oz.
Proof.
  intros [|a b] k H1 H2 Hk; [congruence|].
  destruct b as [|c d].
  - destruct a as [|a1 a2]; [exfalso; apply H2; reflexivity|].
    destruct (opred (ow a1 a2)) as [a'|] eqn:E.
    + rewrite (fs_pow_succ _ _ _ E). destruct k; [lia|]. discriminate.
    + rewrite (fs_pow_lim (ow a1 a2) k ltac:(discriminate) E). discriminate.
  - rewrite fs_cons by discriminate. discriminate.
Qed.

Lemma F_double : forall c, nf c -> c <> oz -> forall y, 2 * y <= FGH c y.
Proof.
  intros c. induction c as [c IH] using (well_founded_ind wf_ltn). intros Hc Hne y.
  destruct y as [|y']; [lia|].
  destruct (okind c) as [|b|] eqn:K.
  - apply okind_zero in K. contradiction.
  - rewrite (FGH_succ c b _ Hc K).
    assert (Hb : nf b) by (apply okind_succ in K; exact (proj1 (opred_spec c b Hc K))).
    pose proof (it_add_ge (FGH b) (fun z Hz => FGH_gt b z Hb Hz) (S y') (S y') ltac:(lia)). lia.
  - rewrite (FGH_lim c _ Hc K).
    assert (Hl : ltn (fs c (S y')) c) by (apply fs_ltn; assumption).
    apply IH; [exact Hl | exact (proj1 Hl) |].
    apply fs_ne_oz'; [exact Hne | intro E; rewrite E in K; discriminate K | lia].
Qed.

(** f_(x+1)(z) >= f_x(2z-1)  and the shift absorption f_x(z+3) <= f_(x+1)(z) for z >= 3. *)
Lemma F_succ_ge : forall x z, nf x -> 1 <= z -> FGH x (2 * z - 1) <= FGH (osucc x) z.
Proof.
  intros x z Hx Hz. rewrite FGH_osucc by exact Hx. destruct z as [|z']; [lia|].
  rewrite Nat.iter_succ. apply FGH_mono; [exact Hx|].
  pose proof (it_add_ge (FGH x) (fun w Hw => FGH_gt x w Hx Hw) z' (S z') ltac:(lia)). lia.
Qed.

Lemma absorb0 : forall c z, nf c -> c <> oz -> 3 <= z -> FGH c (z + 3) <= FGH (osucc c) z.
Proof.
  intros c z Hc Hne Hz. rewrite FGH_osucc by exact Hc.
  destruct z as [|[|z']]; [lia | lia |]. rewrite !Nat.iter_succ. apply FGH_mono; [exact Hc|].
  pose proof (F_double c Hc Hne (Nat.iter z' (FGH c) (S (S z')))).
  pose proof (it_infl (FGH c) (fun w => FGH_ge c w Hc) z' (S (S z'))). lia.
Qed.

(** Ordinals b + j (finite tail) *)
Definition addf (b : ord) (j : nat) : ord := oapp b (ofin j).

Lemma all_ge_ofin : forall j b, all_ge (ofin j) b.
Proof.
  intros j b. induction b as [|a _ b IH]; [exact I|]. split; [| exact IH].
  destruct j; [exact I | apply ole_oz].
Qed.

Lemma nf_addf : forall b j, nf b -> nf (addf b j).
Proof. intros b j Hb. apply nf_oapp; [exact Hb | apply nf_ofin | apply all_ge_ofin]. Qed.

Lemma addf_S : forall b j, osucc (addf b j) = addf b (S j).
Proof. intros. unfold addf. rewrite ofin_S. unfold osucc. apply oapp_assoc. Qed.

Lemma addf_ne : forall b j, addf b (S j) <> oz.
Proof. intros. apply oapp_ne. discriminate. Qed.

Lemma F_addf_mono : forall b i j m, nf b -> i <= j -> 1 <= m -> FGH (addf b i) m <= FGH (addf b j) m.
Proof.
  intros b i j m Hb H Hm. induction H as [|j H IH]; [lia|].
  eapply Nat.le_trans; [exact IH|]. rewrite <- addf_S. apply FGH_le_osucc; [apply nf_addf, Hb | exact Hm].
Qed.

(** f_(b+3)(z) >= f_b(8z-7) *)
Lemma F_plus3 : forall b z, nf b -> 1 <= z -> FGH b (8 * z - 7) <= FGH (addf b 3) z.
Proof.
  intros b z Hb Hz.
  rewrite <- addf_S. eapply Nat.le_trans; [| apply F_succ_ge; [apply nf_addf, Hb | exact Hz]].
  rewrite <- addf_S. eapply Nat.le_trans; [| apply F_succ_ge; [apply nf_addf, Hb | lia]].
  rewrite <- addf_S. eapply Nat.le_trans; [| apply F_succ_ge; [apply nf_addf, Hb | lia]].
  unfold addf at 1. change (ofin 0) with oz. rewrite oapp_oz_r.
  apply FGH_mono; [exact Hb | lia].
Qed.

(** b + omega *)
Lemma F_omega_tail : forall b N, nf (oapp b omega) -> FGH (oapp b omega) N = FGH (addf b N) N.
Proof.
  intros b N H. rewrite FGH_lim; [| exact H | apply okind_app_pow; discriminate].
  unfold omega. rewrite fs_app by discriminate. reflexivity.
Qed.

Lemma nf_app_l : forall x y, nf (oapp x y) -> nf x.
Proof.
  induction x as [|a _ b IH]; intros y H; [apply nf_z|]. cbn [oapp] in H.
  apply nf_ow; [eapply nf_head; exact H | eapply IH; eapply nf_tail; exact H|].
  pose proof (nf_head_le _ _ H) as Hh. destruct b as [|c d]; [exact I|]. exact Hh.
Qed.

(** absorption at level 1:  f_c(2z+6) <= f_(c+omega)(z), z >= 3 *)
Lemma absorb1 : forall c z, nf (oapp c omega) -> 3 <= z -> FGH c (2 * z + 6) <= FGH (oapp c omega) z.
Proof.
  intros c z H Hz. assert (Hc : nf c) by (eapply nf_app_l; exact H).
  rewrite F_omega_tail by exact H.
  eapply Nat.le_trans; [| apply F_addf_mono; [exact Hc | exact Hz | lia]].
  eapply Nat.le_trans; [| apply F_plus3; [exact Hc | lia]].
  apply FGH_mono; [exact Hc | lia].
Qed.

Lemma Vf0_F : forall c y, nf c -> Vf 0 (FGH c) y = FGH (osucc c) (y + 3).
Proof. intros. rewrite Vf0, FGH_osucc by assumption. reflexivity. Qed.

(** level 0, iterated:  V_0^j (f_b) <= f_(b + 2j - 1)(. + 3) *)
Lemma inner0 : forall b j y, nf b -> 1 <= j -> Nat.iter j (Vf 0) (FGH b) y <= FGH (addf b (2 * j - 1)) (y + 3).
Proof.
  intros b j y Hb Hj. revert y. induction Hj as [|j Hj IH]; intros y.
  - rewrite Nat.iter_succ. simpl (Nat.iter 0 _ _). rewrite Vf0_F by exact Hb. apply Nat.eq_le_incl. reflexivity.
  - rewrite Nat.iter_succ.
    eapply Nat.le_trans; [apply (Vf_mono_base 0 _ (FGH (addf b (2 * j))))|].
    + apply gd_iterV, F_gd, Hb.
    + apply F_gd, nf_addf, Hb.
    + intros z Hz. eapply Nat.le_trans; [apply IH|].
      assert (E : addf b (2 * j) = osucc (addf b (2 * j - 1))) by (rewrite addf_S; f_equal; lia).
      rewrite E. apply absorb0; [apply nf_addf, Hb | | exact Hz].
      assert (E2 : 2 * j - 1 = S (2 * j - 2)) by lia. rewrite E2. apply addf_ne.
    + rewrite Vf0_F by (apply nf_addf, Hb). rewrite addf_S.
      replace (S (2 * j)) with (2 * S j - 1) by lia. lia.
Qed.

(** Claim at level k: V_k (f_b) n <= f_(b + omega^k)(2n + 6k) *)
Definition ClaimK (k : nat) : Prop := forall b n, nf b -> all_ge (opow (ofin k)) b ->
  Vf k (FGH b) n <= FGH (oapp b (opow (ofin k))) (2 * n + 6 * k).

Definition InnerK (k : nat) : Prop := forall b j y, nf b -> all_ge (opow (ofin k)) b -> 1 <= j ->
  Nat.iter j (Vf k) (FGH b) y <= FGH (oapp b (orep (ofin k) (2 * j - 1) oz)) (2 * y + 6 * k).

Lemma nf_brep : forall b k j, nf b -> all_ge (opow (ofin k)) b -> nf (oapp b (orep (ofin k) j oz)).
Proof. intros. apply nf_oapp; [assumption | apply nf_orep0, nf_ofin | apply all_ge_orep_l; assumption]. Qed.

Lemma all_ge_brep : forall b k j, all_ge (opow (ofin k)) b -> all_ge (opow (ofin k)) (oapp b (orep (ofin k) j oz)).
Proof. intros. apply all_ge_oapp; [assumption | apply all_ge_orep]. Qed.

Lemma orep_split : forall a i j, orep a (i + j) oz = oapp (orep a i oz) (orep a j oz).
Proof. intros a i j. induction i as [|i IH]; [reflexivity|]. cbn [orep Nat.add oapp]. rewrite IH. reflexivity. Qed.

Lemma claim1 : ClaimK 1.
Proof.
  intros b n Hb Hall. change (opow (ofin 1)) with omega in *.
  assert (Hn : nf (oapp b omega)) by (apply nf_oapp; [exact Hb | apply nf_omega | exact Hall]).
  change (Vf 1 (FGH b) n) with (Nat.iter (n + 3) (Vf 0) (FGH b) (n + 3)).
  eapply Nat.le_trans; [apply inner0; [exact Hb | lia]|].
  rewrite F_omega_tail by exact Hn.
  apply Nat.le_trans with (m := FGH (addf b (2 * (n + 3) - 1)) (2 * n + 6 * 1));
    [apply FGH_mono; [apply nf_addf, Hb | lia] | apply F_addf_mono; [exact Hb | lia | lia]].
Qed.

(** omega^(j+1) descends to omega^j (index k >= 1) *)
Lemma desc_pow_down : forall k j, 1 <= k -> desc k (opow (ofin (S j))) (opow (ofin j)).
Proof.
  intros k j Hk. apply desc_step; [discriminate|]. unfold opow at 1. rewrite ofin_S, (fs_pow_succ _ (ofin j) k) by apply opred_osucc.
  destruct k as [|k]; [lia|]. cbn [orep].
  change (ow (ofin j) (orep (ofin j) k oz)) with (oapp (opow (ofin j)) (orep (ofin j) k oz)).
  apply desc_app_drop. apply nf_orep0, nf_ofin.
Qed.

Lemma ole_ofin : forall i j, i <= j -> ole (ofin i) (ofin j).
Proof.
  intros i j H. induction H as [|j H IH]; [left; reflexivity|].
  eapply ole_trans; [exact IH | right; apply olt_ofin_S].
Qed.

Lemma absorbK : forall k c z, 1 <= k <= 4 -> nf c -> all_ge (opow (ofin k)) c -> 3 <= z ->
  FGH c (2 * z + 6 * k) <= FGH (oapp c (opow (ofin k))) z.
Proof.
  intros k c z Hk Hc Hall Hz.
  assert (Hw : all_ge omega c) by (apply (all_ge_mono c (ofin k) (ofin 1)); [apply ole_ofin; lia | exact Hall]).
  assert (Hcw : nf (oapp c omega)) by (apply nf_oapp; [exact Hc | apply nf_omega | exact Hw]).
  destruct k as [|[|k]]; [lia | |].
  { eapply Nat.le_trans; [| apply absorb1; assumption]. apply FGH_mono; [exact Hc | lia]. }
  assert (Hcww : nf (oapp (oapp c omega) omega)).
  { apply nf_oapp; [exact Hcw | apply nf_omega | apply all_ge_oapp; [exact Hw | split; [left; reflexivity | exact I]]]. }
  assert (Hck : nf (oapp c (opow (ofin (S (S k)))))) by (apply nf_oapp; [exact Hc | apply nf_opow, nf_ofin | exact Hall]).
  assert (Hall2 : all_ge (opow (ofin 2)) c) by (apply (all_ge_mono c (ofin (S (S k))) (ofin 2)); [apply ole_ofin; lia | exact Hall]).
  assert (D : desc 1 (opow (ofin (S (S k)))) (opow (ofin 2))).
  { clear. induction k as [|k IH]; [apply desc_refl|].
    eapply desc_trans; [apply desc_pow_down; lia | exact IH]. }
  (* step 1: omega^(k+2) descends to omega^2 *)
  eapply Nat.le_trans; [| apply (FGH_desc_le 1 _ (oapp c (opow (ofin 2)))); [exact Hck | apply desc_app, D | lia | lia]].
  (* step 2: c + omega^2 at z is c + omega * z, at least c + omega * 2 *)
  assert (E2 : FGH (oapp c (opow (ofin 2))) z = FGH (oapp c (orep (ofin 1) z oz)) z).
  { change (opow (ofin 2)) with (opow (osucc (ofin 1))). apply FGH_app_succ_exp.
    change (osucc (ofin 1)) with (ofin 2). apply nf_oapp; [exact Hc | apply nf_opow, nf_ofin | exact Hall2]. }
  rewrite E2.
  assert (E3 : oapp c (orep (ofin 1) z oz) = oapp (oapp (oapp c omega) omega) (orep (ofin 1) (z - 2) oz)).
  { assert (Ez : z = 2 + (z - 2)) by lia. rewrite Ez at 1. rewrite orep_split, !oapp_assoc. reflexivity. }
  assert (Hn3 : nf (oapp (oapp (oapp c omega) omega) (orep (ofin 1) (z - 2) oz))).
  { rewrite <- E3. apply nf_brep; [exact Hc | exact Hw]. }
  rewrite E3.
  eapply Nat.le_trans; [| apply FGH_app_ge; [exact Hn3 | lia]].
  (* step 3: two level-1 absorptions *)
  eapply Nat.le_trans; [| apply absorb1; [exact Hcww | exact Hz]].
  eapply Nat.le_trans; [| apply absorb1; [exact Hcw | lia]].
  apply FGH_mono; [exact Hc | lia].
Qed.

Lemma inner_of_claim : forall k, 1 <= k <= 4 -> ClaimK k -> InnerK k.
Proof.
  intros k Hk HC b j y Hb Hall Hj. revert y. induction Hj as [|j Hj IH]; intros y.
  - rewrite Nat.iter_succ. simpl (Nat.iter 0 _ _). change (orep (ofin k) (2 * 1 - 1) oz) with (opow (ofin k)). apply HC; assumption.
  - rewrite Nat.iter_succ.
    assert (E12 : oapp (oapp b (orep (ofin k) (2 * j - 1) oz)) (opow (ofin k)) = oapp b (orep (ofin k) (2 * j) oz)).
    { rewrite oapp_assoc. set (p := 2 * j - 1). assert (Ej : 2 * j = S p) by (unfold p; lia).
      rewrite Ej, orep_S_app. reflexivity. }
    assert (Hc2 : nf (oapp b (orep (ofin k) (2 * j) oz))) by (apply nf_brep; assumption).
    eapply Nat.le_trans; [apply (Vf_mono_base k _ (FGH (oapp b (orep (ofin k) (2 * j) oz))))|].
    + apply gd_iterV, F_gd, Hb.
    + apply F_gd, Hc2.
    + intros z Hz. eapply Nat.le_trans; [apply IH|]. rewrite <- E12.
      apply absorbK; [exact Hk | apply nf_brep; assumption | apply all_ge_brep; assumption | exact Hz].
    + eapply Nat.le_trans; [apply HC; [exact Hc2 | apply all_ge_brep; assumption]|].
      assert (E23 : oapp (oapp b (orep (ofin k) (2 * j) oz)) (opow (ofin k)) = oapp b (orep (ofin k) (2 * S j - 1) oz)).
      { rewrite oapp_assoc. replace (2 * S j - 1) with (S (2 * j)) by lia. rewrite orep_S_app. reflexivity. }
      rewrite E23. lia.
Qed.

Lemma claim_succ : forall k, 1 <= k <= 4 -> InnerK k -> ClaimK (S k).
Proof.
  intros k Hk HI b n Hb Hall.
  assert (Hallk : all_ge (opow (ofin k)) b) by (apply (all_ge_mono b (ofin (S k)) (ofin k)); [apply ole_ofin; lia | exact Hall]).
  assert (Hn : nf (oapp b (opow (osucc (ofin k))))).
  { rewrite <- ofin_S. apply nf_oapp; [exact Hb | apply nf_opow, nf_ofin | exact Hall]. }
  rewrite VfS. eapply Nat.le_trans; [apply HI; [exact Hb | exact Hallk | lia]|].
  rewrite ofin_S, FGH_app_succ_exp by exact Hn.
  replace (2 * (n + 3) + 6 * k) with (2 * n + 6 * S k) by lia.
  assert (Es : orep (ofin k) (2 * n + 6 * S k) oz
             = oapp (orep (ofin k) (2 * (n + 3) - 1) oz) (orep (ofin k) (2 * n + 6 * S k - (2 * (n + 3) - 1)) oz)).
  { rewrite <- orep_split. f_equal. lia. }
  rewrite Es, <- oapp_assoc. apply FGH_app_ge; [| lia].
  rewrite oapp_assoc, <- orep_split. apply nf_brep; assumption.
Qed.

Lemma claim2 : ClaimK 2. Proof. apply claim_succ; [lia|]. apply inner_of_claim; [lia | exact claim1]. Qed.
Lemma claim3 : ClaimK 3. Proof. apply claim_succ; [lia|]. apply inner_of_claim; [lia | exact claim2]. Qed.
Lemma inner3 : InnerK 3. Proof. apply inner_of_claim; [lia | exact claim3]. Qed.

(** ** Part 3: the exact score *)

Theorem T4_upper : T 4 S 1 <= FGH (orep (ofin 3) 7 oz) 26.
Proof.
  eapply Nat.le_trans; [apply (T_le_V 4 S (FGH oz)); [apply F_gd, nf_z | intros y; rewrite FGH_zero; lia]|].
  rewrite VfS.
  replace 26 with (2 * (1 + 3) + 6 * 3) by reflexivity.
  replace (orep (ofin 3) 7 oz) with (oapp oz (orep (ofin 3) (2 * (1 + 3) - 1) oz)) by reflexivity.
  apply inner3; [apply nf_z | exact I | lia].
Qed.

Lemma desc_9_to_7 : desc 10 (opow (ofin 9)) (osucc (orep (ofin 3) 7 oz)).
Proof.
  eapply desc_trans; [apply desc_pow_down; lia|].
  eapply desc_trans; [apply desc_pow_down; lia|].
  eapply desc_trans; [apply desc_pow_down; lia|].
  eapply desc_trans; [apply desc_pow_down; lia|].
  eapply desc_trans; [apply desc_pow_down; lia|].
  (* omega^4 -> omega^3 * 10 -> omega^3 * 8 -> omega^3 * 7 + 1 *)
  apply desc_step; [discriminate|].
  replace (fs (opow (ofin 4)) 10) with (oapp (orep (ofin 3) 8 oz) (orep (ofin 3) 2 oz)) by reflexivity.
  eapply desc_trans; [apply desc_app_drop, nf_orep0, nf_ofin|].
  replace (orep (ofin 3) 8 oz) with (oapp (orep (ofin 3) 7 oz) (opow (ofin 3))) by reflexivity.
  apply desc_app.
  eapply desc_trans; [apply desc_pow_down; lia|].
  eapply desc_trans; [apply desc_pow_down; lia|].
  apply (desc_pow_down 10 0). lia.
Qed.

Theorem T4_lt_w9 : T 4 S 1 + 25 <= FGH (opow (ofin 9)) 10.
Proof.
  pose proof T4_upper as H1.
  assert (Hx : nf (orep (ofin 3) 7 oz)) by (apply nf_orep0, nf_ofin).
  pose proof (FGH_desc_le 10 _ _ 10 (nf_opow _ (nf_ofin 9)) desc_9_to_7 ltac:(lia) ltac:(lia)) as H2.
  rewrite FGH_osucc in H2 by exact Hx.
  set (f := FGH (orep (ofin 3) 7 oz)) in *.
  change (Nat.iter 10 f 10) with (f (f (Nat.iter 8 f 10))) in H2.
  assert (Hd : forall y, 2 * y <= f y) by (intro y; apply F_double; [exact Hx | discriminate]).
  assert (Hm : forall a b, a <= b -> f a <= f b) by (intros; apply FGH_mono; assumption).
  assert (H3 : 26 <= Nat.iter 8 f 10).
  { apply Nat.le_trans with (m := Nat.iter 2 f 10).
    - change (Nat.iter 2 f 10) with (f (f 10)). pose proof (Hd 10). pose proof (Hd (f 10)). lia.
    - apply it_mono_n; [intro w; apply FGH_ge, Hx | lia]. }
  pose proof (Hm _ _ H3) as H4. pose proof (Hd (Nat.iter 8 f 10)) as H5. pose proof (Hd 26) as H6.
  pose proof (Hd (f (Nat.iter 8 f 10))) as H7.
  lia.
Qed.

(** ** Part 4: every halting run of BB29 leaves T 4 S 1 + 1 ones *)

Lemma det_halt : forall a b h, a -->* b -> a -->* h -> halted tm h -> b -->* h.
Proof.
  intros a b h Hab Hah Hh.
  apply with_counter in Hab as [n Hn]. apply with_counter in Hah as [k Hk].
  destruct (Nat.le_gt_cases n k) as [Hle|Hgt].
  - destruct (rewind_split' n (k - n) tm k a h Hk ltac:(lia)) as (c' & H1 & H2).
    pose proof (multistep_deterministic tm n a b c' Hn H1) as E. subst c'.
    eapply without_counter. exact H2.
  - destruct (rewind_split' k (n - k) tm n a b Hn ltac:(lia)) as (c' & H1 & H2).
    pose proof (multistep_deterministic tm k a h c' Hk H1) as E. subst c'.
    exfalso. exact (halted_no_multistep tm h b (n - k) ltac:(lia) Hh H2).
Qed.

Lemma halted_evstep_eq : forall h c, halted tm h -> h -->* c -> c = h.
Proof.
  intros h c Hh H. inversion H; subst; [reflexivity|].
  exfalso. eapply halted_no_step; eassumption.
Qed.

Lemma str_count0 : forall L : list Sym, const S0 = L *> const S0 -> count1 L = 0.
Proof.
  induction L as [|b L IH]; intros H; [reflexivity|].
  assert (Hb : S0 = b) by exact (f_equal (@Streams.hd Sym) H).
  assert (Ht : const S0 = L *> const S0) by exact (f_equal (@Streams.tl Sym) H).
  subst b. simpl. apply IH. exact Ht.
Qed.

Lemma str_count : forall L1 L2 : list Sym, L1 *> const S0 = L2 *> const S0 -> count1 L1 = count1 L2.
Proof.
  induction L1 as [|a L1 IH]; intros L2 H.
  - symmetry. apply str_count0. exact H.
  - destruct L2 as [|b L2].
    + apply str_count0. symmetry. exact H.
    + assert (Hb : a = b) by exact (f_equal (@Streams.hd Sym) H).
      assert (Ht : L1 *> const S0 = L2 *> const S0) by exact (f_equal (@Streams.tl Sym) H).
      subst b. cbn [count1]. rewrite (IH L2 Ht). reflexivity.
Qed.

Lemma ones_unique : forall c N N', ones c N -> ones c N' -> N = N'.
Proof.
  intros c N N' (q & L & R & s & E & HN) (q' & L' & R' & s' & E' & HN').
  rewrite E in E'. injection E' as E1 E2 E3 E4. subst.
  rewrite (str_count _ _ E2), (str_count _ _ E4). reflexivity.
Qed.

(** [halts_with NB]: hydra29 halts from the blank tape with NB ones on the tape. *)
Definition halts_with (NB : nat) : Prop := exists c, c0 -->* c /\ halted tm c /\ ones c NB.

Theorem halts_with_exact : forall NB, halts_with NB -> NB = T 4 S 1 + 1.
Proof.
  intros NB (c & H1 & H2 & H3).
  destruct score_exact as (c' & H1' & H2' & H3').
  pose proof (det_halt _ _ _ H1' H1 H2) as H. apply halted_evstep_eq in H; [| exact H2']. subst c.
  exact (ones_unique _ _ _ H3 H3').
Qed.

Theorem halts_with_upper : forall NB, halts_with NB -> NB + 24 <= FGH (opow (ofin 9)) 10.
Proof. intros NB H. apply halts_with_exact in H. pose proof T4_lt_w9. lia. Qed.

Print Assumptions T4_upper.
Print Assumptions T4_lt_w9.
Print Assumptions halts_with_exact.
Print Assumptions halts_with_upper.
