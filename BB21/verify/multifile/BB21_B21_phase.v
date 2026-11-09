(** B21: phases (P walks through the 2s), phase starts, refills. *)
From Coq Require Import Lia PeanoNat List Bool.
From BB8 Require Import BB21_B21_absdef BB21_B21_grow BB21_B21_steps BB21_B21_inv BB21_B21_proc.
Import ListNotations.
Set Default Goal Selector "!".

Section Generic.
Variable refill : nat -> list nat -> res.

Definition PhaseEnd (s : st) : Prop := INV s /\ fr s = [1] /\ up s = [] /\ deep (b0 s).

(** after Proc, the next frontier is known: re-decompose *)
Lemma redecomp : forall b0' es' w F U, esok es' -> 2 <= w -> isE F = false ->
  INVL (b0' :: rev (map ones es') ++ ones w :: F :: U) ->
  INV (mk b0' (w :: es') F U).
Proof.
  intros b0' es' w F U Hes Hw HF [s2 [He2 I2]].
  assert (Hs2 : enc s2 = b0 s2 :: rev (map ones (w :: es')) ++ F :: U).
  { rewrite He2. assert (b0 s2 = b0') by (unfold enc in He2; injection He2 as ->; reflexivity).
    rewrite H. rewrite rev_ones_cons, <- app_assoc. reflexivity. }
  destruct (enc_inj s2 (w :: es') F U I2 ltac:(constructor; assumption) HF Hs2) as [E1 [E2 E3]].
  assert (b0 s2 = b0') by (unfold enc in He2; injection He2 as ->; reflexivity).
  destruct s2 as [b s e f u]. simpl in *. subst. exact I2.
Qed.

Lemma enc_redecomp : forall b0' es' w F U,
  b0' :: rev (map ones es') ++ ones w :: F :: U = enc (mk b0' (w :: es') F U).
Proof. intros. rewrite enc_mk, rev_ones_cons, <- app_assoc. reflexivity. Qed.

Lemma jacc_big : forall s, INV s -> big (b0 s) -> 16 <= jacc s.
Proof. intros s I Hb. unfold jacc. rewrite eng_eq. pose proof (eng_ge13 _ (or_intror Hb)). lia. Qed.

Lemma phi_loop : forall r s, INV s -> fr s = [1] -> up s = repeat [2] r -> deep (b0 s) ->
  exists s', star refill (enc s) (enc s') /\ PhaseEnd s' /\ length (es s') = length (es s) + r.
Proof.
  induction r as [| r IH]; intros s I Hf Hu Hd.
  - exists s. split; [constructor |]. split; [split; [exact I | split; [exact Hf | split; [exact Hu | exact Hd]]] | lia].
  - set (k := (jacc s - 2) / 2).
    set (s1 := mk (ones (length (b0 s) - 1)) (map pred (es s)) (Xl k) ([1] :: repeat [2] r)).
    assert (St : astepG refill (enc s) = Next (enc s1)).
    { apply (step_P refill s (repeat [2] r) (b0ok_of s I) (i_es s I) Hf Hu (jacc_even s I)). pose proof (jacc_ge s I). lia. }
    assert (I1 : INV s1) by (apply (inv_P s _ I Hf Hu)).
    pose proof (jacc_big s I (i_FP s I Hf)) as J16.
    assert (Hk : 7 <= k) by (unfold k; pose proof (half2_ge (jacc s)); lia).
    assert (Hw : work (Xl k)) by (split; [exact (i_frE s1 I1) | rewrite Xl_len; lia]).
    destruct (proc refill (length (es s1)) s1 I1 eq_refl Hw) as [b0' [es' [Hst [Hl [Hok [Hdp Hinv]]]]]].
    simpl fr in Hst, Hinv. simpl up in Hst, Hinv. rewrite Xl_len in Hst, Hinv.
    pose proof (redecomp b0' es' (S k) [1] (repeat [2] r) Hok ltac:(lia) eq_refl Hinv) as I2.
    destruct (IH _ I2 eq_refl eq_refl Hdp) as [s' [Hst' [Hend Hl']]].
    exists s'. split; [| split; [exact Hend |]].
    + econstructor; [exact St |]. eapply (star_trans refill); [exact Hst |]. rewrite enc_redecomp. exact Hst'.
    + rewrite Hl'. simpl. rewrite Hl. simpl. rewrite map_length. lia.
Qed.

Lemma two_to_phi : forall r s, INV s -> fr s = [2] -> up s = repeat [2] r ->
  exists s', star refill (enc s) (enc s') /\ INV s' /\ fr s' = [1] /\ up s' = repeat [2] r /\ deep (b0 s') /\
    length (es s') = length (es s).
Proof.
  intros r s I Hf Hu. pose proof (i_F2 s I ltac:(rewrite Hf; reflexivity)) as Hbig.
  destruct (es s) as [| e es'] eqn:Ees.
  - assert (St : astepG refill (enc s) = Next (b0m s :: [1] :: up s)).
    { unfold b0m. apply (step_dec_0 refill s 0 [] (b0ok_of s I) Ees Hf (jacc_even s I) (jacc_ge s I)). }
    pose proof (inv_dec_b0 s 0 [] I Ees Hf eq_refl) as I1.
    exists (mk (b0m s) [] [1] (up s)). split; [econstructor; [exact St | constructor] |].
    split; [exact I1 | split; [reflexivity | split; [exact Hu | split; [| reflexivity]]]].
    apply (b0m_deep s I Ees). apply big_not_pure. exact Hbig.
  - set (W := ones (pred e) ++ Xl ((jacc s - 4) / 2)).
    set (s1 := mk (ones (length (b0 s) - 1)) (map pred es') W ([1] :: up s)).
    assert (St : astepG refill (enc s) = Next (enc s1)).
    { apply (step_dec_es refill s 0 [] e es' (b0ok_of s I) (i_es s I) Hf Ees (jacc_even s I) (jacc_ge s I)). }
    assert (I1 : INV s1) by (apply (inv_dec_es s 0 [] e es' I Hf Ees)).
    assert (Hw : work W).
    { destruct (W_props (pred e) ((jacc s - 4) / 2)) as (WL & _ & WE & _). split; [exact WE |].
      fold W in WL. rewrite WL. pose proof (i_es s I) as He'. rewrite Ees in He'. inversion He'; subst. lia. }
    destruct (proc refill (length (es s1)) s1 I1 eq_refl Hw) as [b0' [es'' [Hst [Hl [Hok [Hdp Hinv]]]]]].
    simpl fr in Hst, Hinv. simpl up in Hst, Hinv.
    pose proof (redecomp b0' es'' (length W) [1] (up s) Hok (proj2 Hw) eq_refl Hinv) as I2.
    exists (mk b0' (length W :: es'') [1] (up s)). split.
    + econstructor; [exact St |]. rewrite <- enc_redecomp. exact Hst.
    + split; [exact I2 | split; [reflexivity | split; [exact Hu | split; [exact Hdp |]]]].
      simpl. rewrite Hl. simpl. rewrite map_length. reflexivity.
Qed.

Lemma phase_from_work : forall k s, INV s -> work (fr s) -> up s = repeat [2] (S k) ->
  exists s', star refill (enc s) (enc s') /\ PhaseEnd s' /\ length (es s') = length (es s) + 1 + k.
Proof.
  intros k s I Hw Hu.
  destruct (proc refill (length (es s)) s I eq_refl Hw) as [b0' [es' [Hst [Hl [Hok [Hdp Hinv]]]]]].
  rewrite Hu in Hst, Hinv. simpl repeat in Hst, Hinv.
  pose proof (redecomp b0' es' (length (fr s)) [2] (repeat [2] k) Hok (proj2 Hw) eq_refl Hinv) as I1.
  destruct (two_to_phi k _ I1 eq_refl eq_refl) as [s2 [Hst2 [I2 [Hf2 [Hu2 [Hd2 Hl2]]]]]].
  destruct (phi_loop k s2 I2 Hf2 Hu2 Hd2) as [s3 [Hst3 [Hend Hl3]]].
  exists s3. split; [| split; [exact Hend |]].
  - eapply (star_trans refill); [exact Hst |]. rewrite enc_redecomp. eapply (star_trans refill); [exact Hst2 | exact Hst3].
  - rewrite Hl3, Hl2. simpl. lia.
Qed.

End Generic.
