(** B21 / W2PR quantitative layer, part 4: phase-level growth of B0min (parametric in the refill rule).
    A phase over r P-blocks starting at depth j multiplies B0min through PhiR r j, and
    PhiR r j b >= f_wa (j + r) 0 (b + r - 1) >= f_wsq r. *)
From Coq Require Import Lia PeanoNat List Bool.
From BB8 Require Import BB21_B21_absdef BB21_B21_grow BB21_B21_steps BB21_B21_inv BB21_B21_proc BB21_B21_phase
  BB_FGH_wa BB21_B21_qnt BB21_B21_qnt2 BB21_B21_qnt3.
Import ListNotations.
Set Default Goal Selector "!".

Fixpoint PhiR (r j b : nat) : nat :=
  match r with
  | 0 => b
  | S r' => PhiR r' (S j) (Mq Gm (S j) b)
  end.

Lemma PhiR_mono : forall r j x y, x <= y -> PhiR r j x <= PhiR r j y.
Proof. induction r; intros j x y H; cbn [PhiR]; [exact H |]. apply IHr. apply (proj2 (good_g (S j))). exact H. Qed.

Lemma Mq_S : forall j x, S x <= Mq Gm j x.
Proof.
  induction j; intros x; [apply Gm_S |]. simpl. destruct x as [| x].
  - simpl. apply IHj.
  - transitivity (Lev (Mq Gm j) 0 (S x)); [simpl; apply IHj |].
    apply Lev_index; [apply good_g | lia | lia].
Qed.

Lemma PhiR_lb : forall r j b, 1 <= r -> Mq Gm (j + r) (b + r - 1) <= PhiR r j b.
Proof.
  induction r as [| r IH]; intros j b Hr; [lia |]. cbn [PhiR].
  destruct r as [| r].
  - cbn [PhiR]. replace (j + 1) with (S j) by lia. replace (b + 1 - 1) with b by lia. lia.
  - pose proof (IH (S j) (Mq Gm (S j) b) ltac:(lia)) as H.
    replace (j + S (S r)) with (S j + S r) by lia.
    etransitivity; [| exact H]. apply (proj2 (good_g _)). pose proof (Mq_S (S j) b). lia.
Qed.

Lemma PhiR_fwsq : forall r j b, 1 <= r -> 1 <= b -> f_wsq r <= PhiR r j b.
Proof.
  intros r j b Hr Hb. etransitivity; [| apply (PhiR_lb r j b Hr)].
  etransitivity; [| apply (Mq_fgh Gm good_Gm Gm_S)]. unfold f_wsq.
  etransitivity; [apply (f_wa_a_mono r (j + r) r ltac:(lia) Hr) |]. apply f_wa_mono. lia.
Qed.

Lemma PhiR_ge : forall r j b, b <= PhiR r j b.
Proof. induction r; intros j b; cbn [PhiR]; [lia |]. pose proof (Mq_S (S j) b). pose proof (IHr (S j) (Mq Gm (S j) b)). lia. Qed.

(** recover the decomposition after processing: the finished block joins es *)
Lemma post_shape : forall s' es' w F U, INV s' -> 2 <= w -> esok es' -> isE F = false ->
  enc s' = b0 s' :: rev (map ones es') ++ ones w :: F :: U -> es s' = w :: es' /\ fr s' = F /\ up s' = U.
Proof.
  intros s' es' w F U I Hw Hok HF He. apply (enc_inj s' (w :: es') F U I); [constructor; [exact Hw | exact Hok] | exact HF |].
  rewrite He. f_equal. rewrite rev_ones_cons, <- app_assoc. reflexivity.
Qed.

Lemma deep_not_pure : forall s, INV s -> deep (b0 s) -> ~ pure (b0 s).
Proof. intros s I Hd. apply all1_pure; [exact I | apply all1_deep; exact Hd]. Qed.

Section Generic.
Variable refill : nat -> list nat -> res.

Lemma phi_loop_q : forall r s, INV s -> fr s = [1] -> up s = repeat [2] r -> deep (b0 s) ->
  exists s', star refill (enc s) (enc s') /\ PhaseEnd s' /\ length (es s') = length (es s) + r /\
    PhiR r (length (es s)) (B0min s) <= B0min s'.
Proof.
  induction r as [| r IH]; intros s I Hf Hu Hd.
  - exists s. split; [constructor |]. split; [split; [exact I | split; [exact Hf | split; [exact Hu | exact Hd]]] | cbn [PhiR]; lia].
  - set (k := (jacc s - 2) / 2).
    set (s1 := mk (ones (length (b0 s) - 1)) (map pred (es s)) (Xl k) ([1] :: repeat [2] r)).
    assert (St : astepG refill (enc s) = Next (enc s1)).
    { apply (step_P refill s (repeat [2] r) (b0ok_of s I) (i_es s I) Hf Hu (jacc_even s I)). pose proof (jacc_ge s I). lia. }
    assert (I1 : INV s1) by (apply (inv_P s _ I Hf Hu)).
    pose proof (jacc_big s I (i_FP s I Hf)) as J16.
    assert (Hk : 7 <= k) by (unfold k; pose proof (half2_ge (jacc s)); lia).
    assert (Hw : work (Xl k)) by (split; [exact (i_frE s1 I1) | rewrite Xl_len; lia]).
    assert (HB1 : B0min s1 = B0min s) by (apply (B0min_P s _ I Hf Hu)).
    destruct (proc_q refill (length (es s1)) s1 I1 eq_refl Hw) as [s' [Hst [I' [Hdp [HPsi [es' [He' [Hl Hok]]]]]]]].
    unfold s1 in He'. cbn [fr up] in He'. rewrite Xl_len in He'.
    destruct (post_shape s' es' (S k) [1] (repeat [2] r) I' ltac:(lia) Hok eq_refl He') as [Es' [Fs' Us']].
    destruct (IH s' I' Fs' Us' Hdp) as [s'' [Hst' [Hend [Hl' HPhi]]]].
    exists s''. split; [| split; [exact Hend | split]].
    + econstructor; [exact St |]. eapply (star_trans refill); [exact Hst | exact Hst'].
    + rewrite Hl', Es'. simpl. rewrite Hl. unfold s1. simpl. rewrite map_length. lia.
    + (* the growth: Mq (S j) B0min <= Psi <= B0min s' *)
      rewrite Es' in HPhi. simpl length in HPhi. rewrite Hl in HPhi. unfold s1 in HPhi. cbn [es] in HPhi.
      rewrite map_length in HPhi. simpl PhiR. etransitivity; [| exact HPhi]. apply PhiR_mono.
      etransitivity; [| exact HPsi]. unfold Psi. change (b0 s1) with (ones (length (b0 s) - 1)).
      change (fr s1) with (Xl k). rewrite all1_ones. rewrite HB1. change (es s1) with (map pred (es s)). rewrite map_length.
      pose proof (i_min s I) as Hmin.
      destruct (jacc_ge_B0min s I (deep_not_pure s I Hd)) as [_ Hj2].
      assert (Hbk : B0min s <= k) by (unfold k; pose proof (Nat.div_le_mono (jacc s - 4) (jacc s - 2) 2 ltac:(lia) ltac:(lia)); lia).
      destruct k as [| k'] eqn:Ek; [lia |].
      simpl Mq. transitivity (Lev (Mq Gm (length (es s))) (S k') (B0min s)).
      * apply Lev_index; [apply good_g | lia | lia].
      * apply B_fresh; [apply good_g | lia].
Qed.

Lemma two_to_phi_q : forall r s, INV s -> fr s = [2] -> up s = repeat [2] r ->
  exists s', star refill (enc s) (enc s') /\ INV s' /\ fr s' = [1] /\ up s' = repeat [2] r /\ deep (b0 s') /\
    length (es s') = length (es s) /\ B0min s <= B0min s'.
Proof.
  intros r s I Hf Hu. pose proof (i_F2 s I ltac:(rewrite Hf; reflexivity)) as Hbig.
  destruct (es s) as [| e es'] eqn:Ees.
  - assert (St : astepG refill (enc s) = Next (b0m s :: [1] :: up s)).
    { unfold b0m. apply (step_dec_0 refill s 0 [] (b0ok_of s I) Ees Hf (jacc_even s I) (jacc_ge s I)). }
    pose proof (inv_dec_b0 s 0 [] I Ees Hf eq_refl) as I1.
    exists (mk (b0m s) [] [1] (up s)). split; [econstructor; [exact St | constructor] |].
    split; [exact I1 | split; [reflexivity | split; [exact Hu | split; [| split; [reflexivity |]]]]].
    + apply (b0m_deep s I Ees). apply big_not_pure. exact Hbig.
    + exact (proj1 (B0min_dec0 s 0 [] I Ees Hf)).
  - set (W := ones (pred e) ++ Xl ((jacc s - 4) / 2)).
    set (s1 := mk (ones (length (b0 s) - 1)) (map pred es') W ([1] :: up s)).
    assert (St : astepG refill (enc s) = Next (enc s1)).
    { apply (step_dec_es refill s 0 [] e es' (b0ok_of s I) (i_es s I) Hf Ees (jacc_even s I) (jacc_ge s I)). }
    assert (I1 : INV s1) by (apply (inv_dec_es s 0 [] e es' I Hf Ees)).
    assert (HB1 : B0min s1 = B0min s) by (apply (B0min_dec_es s 0 [] e es' I Hf Ees)).
    assert (Hw : work W).
    { destruct (W_props (pred e) ((jacc s - 4) / 2)) as (WL & _ & WE & _). split; [exact WE |].
      fold W in WL. rewrite WL. pose proof (i_es s I) as He'. rewrite Ees in He'. inversion He'; subst. lia. }
    destruct (proc_q refill (length (es s1)) s1 I1 eq_refl Hw) as [s' [Hst [I' [Hdp [HPsi [es'' [He' [Hl Hok]]]]]]]].
    unfold s1 in He'. cbn [fr up] in He'.
    destruct (post_shape s' es'' (length W) [1] (up s) I' (proj2 Hw) Hok eq_refl He') as [Es' [Fs' Us']].
    exists s'. split; [econstructor; [exact St | exact Hst] |].
    split; [exact I' | split; [exact Fs' | split; [rewrite Us'; exact Hu | split; [exact Hdp | split]]]].
    + rewrite Es'. simpl. rewrite Hl. unfold s1. simpl. rewrite map_length. reflexivity.
    + rewrite <- HB1. etransitivity; [| exact HPsi]. unfold Psi. apply evalP_ge, good_g.
Qed.

Lemma phase_from_work_q : forall k s, INV s -> work (fr s) -> up s = repeat [2] (S k) ->
  exists s', star refill (enc s) (enc s') /\ PhaseEnd s' /\ length (es s') = length (es s) + 1 + k /\
    PhiR k (S (length (es s))) (B0min s) <= B0min s'.
Proof.
  intros k s I Hw Hu.
  destruct (proc_q refill (length (es s)) s I eq_refl Hw) as [s1 [Hst [I1 [Hdp [HPsi [es1 [He1 [Hl Hok]]]]]]]].
  rewrite Hu in He1. simpl repeat in He1.
  destruct (post_shape s1 es1 (length (fr s)) [2] (repeat [2] k) I1 (proj2 Hw) Hok eq_refl He1) as [Es1 [Fs1 Us1]].
  destruct (two_to_phi_q k s1 I1 Fs1 Us1) as [s2 [Hst2 [I2 [Hf2 [Hu2 [Hd2 [Hl2 HB2]]]]]]].
  destruct (phi_loop_q k s2 I2 Hf2 Hu2 Hd2) as [s3 [Hst3 [Hend [Hl3 HB3]]]].
  assert (L2 : length (es s2) = S (length (es s))) by (rewrite Hl2, Es1; simpl; lia).
  exists s3. split; [| split; [exact Hend | split]].
  - eapply (star_trans refill); [exact Hst |]. eapply (star_trans refill); [exact Hst2 | exact Hst3].
  - rewrite Hl3, L2. lia.
  - rewrite L2 in HB3. etransitivity; [| exact HB3]. apply PhiR_mono.
    etransitivity; [| exact HB2]. etransitivity; [| exact HPsi]. unfold Psi. apply evalP_ge, good_g.
Qed.

End Generic.
