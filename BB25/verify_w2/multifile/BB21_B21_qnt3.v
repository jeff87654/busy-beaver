(** B21 / W2PR quantitative layer, part 3: the quantitative frontier-processing lemma (parametric in the refill). *)
From Coq Require Import Lia PeanoNat List Bool Wellfounded.
From BB8 Require Import BB21_B21_absdef BB21_B21_grow BB21_B21_steps BB21_B21_inv BB21_B21_proc
  BB_FGH_wa BB21_B21_qnt BB21_B21_qnt2.
Import ListNotations.
Set Default Goal Selector "!".

Lemma all1_app_false : forall a b, all1 b = false -> all1 (a ++ b) = false.
Proof. induction a; intros b H; simpl; [exact H | rewrite IHa by exact H; apply andb_false_r]. Qed.

Lemma all1_Xl : forall k, all1 (Xl k) = false.
Proof. intros [| k]; reflexivity. Qed.

Lemma all1_b0m : forall s, all1 (b0m s) = false.
Proof. intros. unfold b0m. apply all1_app_false, all1_Xl. Qed.

Lemma all1_deep : forall b, deep b -> all1 b = false.
Proof. intros b [m [k [-> _]]]. apply all1_app_false. reflexivity. Qed.

Lemma all1_pure : forall s, INV s -> all1 (b0 s) = false -> ~ pure (b0 s).
Proof. intros s I H [m Hm]. rewrite Hm in H. rewrite all1_ones in H. discriminate. Qed.

Lemma pure_all1 : forall s, INV s -> all1 (b0 s) = true -> pure (b0 s).
Proof.
  intros s I H. destruct (i_b0 s I) as [Hp | [[m Hm] | [m [[k [Hm _]] | Hm]]]]; [exact Hp | | |]; exfalso; rewrite Hm in H.
  - rewrite all1_app_false in H by reflexivity. discriminate.
  - rewrite all1_app_false in H by reflexivity. discriminate.
  - rewrite all1_app_false in H by reflexivity. discriminate.
Qed.

Section Generic.
Variable refill : nat -> list nat -> res.

Definition Psi (j : nat) (s : st) : nat :=
  evalP (Mq Gm j) 0 (if all1 (b0 s) then pre (fr s) else fr s) (B0min s).

Definition PostQ (s : st) (j : nat) : Prop :=
  exists s', star refill (enc s) (enc s') /\ INV s' /\ deep (b0 s') /\ Psi j s <= B0min s' /\
    exists es', enc s' = b0 s' :: rev (map ones es') ++ ones (length (fr s)) :: up s /\ length es' = j /\ esok es'.

Lemma enc_final : forall s' b es', enc s' = b :: rev (map ones es') ++ ones (length (fr s')) :: up s' -> b0 s' = b.
Proof. intros s' b es' H. unfold enc in H. injection H as H1 _. exact H1. Qed.


Lemma good_g : forall j, good (Mq Gm j).
Proof. apply good_Mq, good_Gm. Qed.

(** in-block step: potential is kept *)
Lemma Psi_est : forall j s T p e r, INV s -> fr s = 1 :: T -> lsplit T = (p, S (S e) :: r) ->
  Psi j s <= Psi j (mk (ones (length (b0 s) - 1)) (map pred (es s)) (repeat 1 p ++ (jacc s + 3) :: S e :: r) (up s)).
Proof.
  intros j s T p e r I Hf El. unfold Psi. cbn [b0 fr]. rewrite all1_ones.
  rewrite (B0min_est s T p e r I Hf El). rewrite Hf. rewrite (lsplit_spec _ _ _ El).
  destruct (all1 (b0 s)) eqn:Ea.
  - apply T_small, good_g.
  - apply T_deep; [apply good_g |]. pose proof (jacc_ge_B0min s I (all1_pure s I Ea)). lia.
Qed.

Lemma proc_q : forall j s, INV s -> length (es s) = j -> work (fr s) -> PostQ s j.
Proof.
  induction j as [| j IHj]; intros s0 I0 Hj0 Hw0;
  remember (fr s0) as f eqn:Ef; revert s0 Ef I0 Hj0 Hw0;
  induction f as [f IHf] using (well_founded_induction RL_wf); intros s Ef I Hj Hw;
  pose proof (b0ok_of s I) as Hb; pose proof (i_es s I) as Hes.
  (* ---- frontier next to b0 ---- *)
  - destruct (es s) as [| e es'] eqn:Ees; [| simpl in Hj; discriminate]. clear Hj.
    destruct f as [| a T]; [destruct Hw; simpl in *; lia |].
    destruct a as [| [| d]].
    + exfalso. pose proof (i_nz s I) as Nz. rewrite <- Ef in Nz.
      apply Forall_cons_iff in Nz as [Nz _]. unfold nzd in Nz. apply Forall_cons_iff in Nz as [Nz _]. lia.
    + (* estep *)
      destruct (lsplit T) as [p r] eqn:El.
      destruct r as [| x r].
      { exfalso. apply lsplit_spec in El. rewrite app_nil_r in El. destruct Hw as [HwE Hwl].
        rewrite El in HwE. assert (isE (ones (S p)) = true) by (apply isE_ones; rewrite El in Hwl; simpl in Hwl; rewrite repeat_length in Hwl; lia).
        unfold ones in H. simpl in H. congruence. }
      destruct x as [| [| e]].
      { exfalso. apply lsplit_spec in El. pose proof (i_nz s I) as Nz. rewrite <- Ef in Nz.
        apply Forall_cons_iff in Nz as [Nz _]. unfold nzd in Nz. apply Forall_cons_iff in Nz as [_ Nz].
        rewrite El in Nz. apply Forall_app in Nz as [_ Nz]. apply Forall_cons_iff in Nz as [Nz _]. lia. }
      { exfalso. apply (lsplit_hd _ _ _ El). reflexivity. }
      set (s1 := mk (ones (length (b0 s) - 1)) (map pred (es s)) (repeat 1 p ++ (jacc s + 3) :: S e :: r) (up s)).
      assert (St : astepG refill (enc s) = Next (enc s1)) by (apply (step_est refill s T p e r Hb (i_es s I) (eq_sym Ef) El)).
      assert (I1 : INV s1) by (apply (inv_est s T p e r I (eq_sym Ef) El)).
      assert (HP : Psi 0 s <= Psi 0 s1) by (apply (Psi_est 0 s T p e r I (eq_sym Ef) El)).
      assert (HR : RL (fr s1) (1 :: T)) by (rewrite (lsplit_spec _ _ _ El); apply RL_est).
      assert (Hl1 : length (fr s1) = length (fr s)).
      { destruct HR as [HR _]. rewrite !rev_length in HR. rewrite <- Ef. exact HR. }
      assert (Hw1 : work (fr s1)) by (split; [exact (i_frE s1 I1) | rewrite Hl1, <- Ef; exact (proj2 Hw)]).
      assert (Hj1 : length (es s1) = 0) by (simpl; rewrite Ees; reflexivity).
      destruct (IHf (fr s1) HR s1 eq_refl I1 Hj1 Hw1) as [s' [Hst [I' [Hd' [HP' Hf']]]]].
      exists s'. rewrite <- Hl1. split; [econstructor; [exact St | exact Hst] |].
      split; [exact I' | split; [exact Hd' | split; [lia | exact Hf']]].
    + (* decrement into b0 *)
      assert (St : astepG refill (enc s) = Next (b0m s :: (S d :: T) :: up s)).
      { unfold b0m. apply (step_dec_0 refill s d T Hb Ees (eq_sym Ef) (jacc_even s I) (jacc_ge s I)). }
      destruct (B0min_dec0 s d T I Ees (eq_sym Ef)) as [Bsm Bbig].
      destruct (isE (S d :: T)) eqn:EE.
      * (* the frontier block is completed *)
        destruct (isE_true_ones _ EE) as [Eo Elen].
        destruct d as [| d]; [| unfold ones in Eo; simpl in Eo; discriminate].
        assert (HT : all1 T = true) by (unfold isE in EE; simpl in EE; apply andb_true_iff in EE as [EE _]; exact EE).
        assert (HTn : T <> []) by (intros ->; simpl in Elen; lia).
        destruct (inv_compl s T I Ees (eq_sym Ef) HT HTn) as [Es [fr2 [up2 [Hu I2]]]].
        pose proof (i_F2 s I ltac:(rewrite <- Ef; reflexivity)) as Hbig.
        assert (Henc : b0m s :: (1 :: T) :: up s = enc (mk (b0m s) (rev Es ++ [length (fr s)]) fr2 up2)).
        { rewrite enc_mk. rewrite map_app, rev_app_distr, map_rev, rev_involutive. simpl.
          rewrite Hu. rewrite <- Ef. simpl length. rewrite Eo. reflexivity. }
        exists (mk (b0m s) (rev Es ++ [length (fr s)]) fr2 up2).
        split; [| split; [exact I2 | split; [| split]]].
        -- econstructor; [exact St |]. rewrite Henc. constructor.
        -- apply (b0m_deep s I Ees). apply big_not_pure. exact Hbig.
        -- unfold Psi. replace (all1 (b0 s)) with false
             by (symmetry; destruct (all1 (b0 s)) eqn:Ea; [exfalso; exact (big_not_pure _ Hbig (pure_all1 s I Ea)) | reflexivity]).
           assert (E : evalP (Mq Gm 0) 0 (fr s) (B0min s) = Gm (B0min s))
             by (rewrite <- Ef; cbn [evalP]; rewrite evalP_allones by exact HT; reflexivity).
           rewrite E. exact (B0min_compl s T Es fr2 up2 I Ees (eq_sym Ef)).
        -- exists []. split; [| split; [reflexivity | constructor]].
           rewrite <- Henc. cbn [b0]. simpl. rewrite <- Ef. simpl length. rewrite Eo. reflexivity.
      * set (s1 := mk (b0m s) [] (S d :: T) (up s)).
        assert (I1 : INV s1) by (apply (inv_dec_b0 s d T I Ees (eq_sym Ef) EE)).
        assert (HP : Psi 0 s <= Psi 0 s1).
        { unfold Psi, s1. cbn [b0 fr]. rewrite all1_b0m. rewrite <- Ef.
          destruct (all1 (b0 s)) eqn:Ea.
          - apply T_dec_small; [apply good_g | exact Bsm].
          - apply T_dec; [apply good_g |]. apply Bbig. apply all1_pure; assumption. }
        assert (HR : RL (S d :: T) (S (S d) :: T)) by apply RL_dec.
        assert (Hw1 : work (S d :: T)) by (split; [exact EE | destruct Hw as [_ Hw]; simpl in *; lia]).
        destruct (IHf (S d :: T) HR s1 eq_refl I1 eq_refl Hw1) as [s' [Hst [I' [Hd' [HP' Hf']]]]].
        exists s'. split; [econstructor; [exact St | exact Hst] |].
        split; [exact I' | split; [exact Hd' | split; [lia |]]].
        rewrite <- Ef. exact Hf'.
  (* ---- deeper frontier ---- *)
  - destruct f as [| a T]; [destruct Hw; simpl in *; lia |].
    destruct a as [| [| d]].
    + exfalso. pose proof (i_nz s I) as Nz. rewrite <- Ef in Nz.
      apply Forall_cons_iff in Nz as [Nz _]. unfold nzd in Nz. apply Forall_cons_iff in Nz as [Nz _]. lia.
    + (* estep *)
      destruct (lsplit T) as [p r] eqn:El.
      destruct r as [| x r].
      { exfalso. apply lsplit_spec in El. rewrite app_nil_r in El. destruct Hw as [HwE Hwl].
        rewrite El in HwE. assert (isE (ones (S p)) = true) by (apply isE_ones; rewrite El in Hwl; simpl in Hwl; rewrite repeat_length in Hwl; lia).
        unfold ones in H. simpl in H. congruence. }
      destruct x as [| [| e]].
      { exfalso. apply lsplit_spec in El. pose proof (i_nz s I) as Nz. rewrite <- Ef in Nz.
        apply Forall_cons_iff in Nz as [Nz _]. unfold nzd in Nz. apply Forall_cons_iff in Nz as [_ Nz].
        rewrite El in Nz. apply Forall_app in Nz as [_ Nz]. apply Forall_cons_iff in Nz as [Nz _]. lia. }
      { exfalso. apply (lsplit_hd _ _ _ El). reflexivity. }
      set (s1 := mk (ones (length (b0 s) - 1)) (map pred (es s)) (repeat 1 p ++ (jacc s + 3) :: S e :: r) (up s)).
      assert (St : astepG refill (enc s) = Next (enc s1)) by (apply (step_est refill s T p e r Hb (i_es s I) (eq_sym Ef) El)).
      assert (I1 : INV s1) by (apply (inv_est s T p e r I (eq_sym Ef) El)).
      assert (HP : Psi (S j) s <= Psi (S j) s1) by (apply (Psi_est (S j) s T p e r I (eq_sym Ef) El)).
      assert (HR : RL (fr s1) (1 :: T)) by (rewrite (lsplit_spec _ _ _ El); apply RL_est).
      assert (Hl1 : length (fr s1) = length (fr s)).
      { destruct HR as [HR _]. rewrite !rev_length in HR. rewrite <- Ef. exact HR. }
      assert (Hw1 : work (fr s1)) by (split; [exact (i_frE s1 I1) | rewrite Hl1, <- Ef; exact (proj2 Hw)]).
      assert (Hj1 : length (es s1) = S j) by (simpl; rewrite map_length; exact Hj).
      destruct (IHf (fr s1) HR s1 eq_refl I1 Hj1 Hw1) as [s' [Hst [I' [Hd' [HP' Hf']]]]].
      exists s'. rewrite <- Hl1. split; [econstructor; [exact St | exact Hst] |].
      split; [exact I' | split; [exact Hd' | split; [lia | exact Hf']]].
    + (* decrement into the nearest E *)
      destruct (es s) as [| e es'] eqn:Ees; [simpl in Hj; discriminate |]. simpl in Hj. injection Hj as Hj.
      set (W := ones (pred e) ++ Xl ((jacc s - 4) / 2)).
      set (s1 := mk (ones (length (b0 s) - 1)) (map pred es') W ((S d :: T) :: up s)).
      assert (St : astepG refill (enc s) = Next (enc s1)).
      { apply (step_dec_es refill s d T e es' Hb (i_es s I) (eq_sym Ef) Ees (jacc_even s I) (jacc_ge s I)). }
      assert (I1 : INV s1) by (apply (inv_dec_es s d T e es' I (eq_sym Ef) Ees)).
      assert (B1 : B0min s1 = B0min s) by (apply (B0min_dec_es s d T e es' I (eq_sym Ef) Ees)).
      assert (He2 : 2 <= e) by (pose proof (i_es s I) as He'; rewrite Ees in He'; inversion He'; assumption).
      assert (Hw1 : work W).
      { destruct (W_props (pred e) ((jacc s - 4) / 2)) as (WL & _ & WE & _). split; [exact WE |].
        fold W in WL. rewrite WL. lia. }
      assert (Hj1 : length (es s1) = j) by (simpl; rewrite map_length; exact Hj).
      destruct (IHj s1 I1 Hj1 Hw1) as [s2 [Hst1 [I2 [Hd2 [HP2 [es1 [He2' [Hl1 Hok1]]]]]]]].
      cbn [fr up] in He2'.
      assert (Pw : Psi j s1 = evalP (Mq Gm j) 0 (pre W) (B0min s)).
      { unfold Psi. rewrite B1. unfold s1. cbn [b0 fr]. rewrite all1_ones. reflexivity. }
      assert (HPs : Psi (S j) s <= evalP (Mq Gm (S j)) 0 (S d :: T) (B0min s2)).
      { unfold Psi at 1. rewrite <- Ef.
        destruct (all1 (b0 s)) eqn:Ea.
        - apply T_dec_small; [apply good_g |]. pose proof (evalP_ge _ (good_g j) (pre W) 0 (B0min s)). lia.
        - apply T_dec; [apply good_g |]. pose proof (jacc_ge_B0min s I (all1_pure s I Ea)) as [_ Hk].
          pose proof (i_min s I) as Hm.
          assert (Hge : Mq Gm (S j) (B0min s) <= evalP (Mq Gm j) 0 (pre W) (B0min s)).
          { unfold W. destruct ((jacc s - 4) / 2) as [| k] eqn:Ek; [lia |].
            destruct e as [| [| a]]; [lia | lia |].
            pose proof (B_merged (Mq Gm j) (good_g j) a k (B0min s) ltac:(lia)) as BM.
            change (pred (S (S a))) with (S a).
            assert (Lev (Mq Gm j) (B0min s) (B0min s) <= Lev (Mq Gm j) (S k) (B0min s))
              by (apply Lev_index; [apply good_g | lia | lia]).
            change (Mq Gm (S j) (B0min s)) with (Lev (Mq Gm j) (B0min s) (B0min s)). unfold ones. lia. }
          lia. }
      destruct (isE (S d :: T)) eqn:EE.
      * (* the frontier block is completed by this decrement *)
        destruct (isE_true_ones _ EE) as [Eo Elen].
        exists s2. split; [econstructor; [exact St | exact Hst1] |].
        split; [exact I2 | split; [exact Hd2 | split]].
        -- rewrite evalP_allones in HPs; [exact HPs |]. unfold isE in EE. apply andb_true_iff in EE as [EE _]. exact EE.
        -- exists (length W :: es1). split; [| split; [simpl; rewrite Hl1; reflexivity | constructor; [exact (proj2 Hw1) | exact Hok1]]].
           rewrite He2'. rewrite rev_ones_cons, <- app_assoc. simpl app.
           rewrite <- Ef. change (length (S (S d) :: T)) with (length (S d :: T)). rewrite <- Eo. reflexivity.
      * assert (Hs2 : enc s2 = b0 s2 :: rev (map ones (length W :: es1)) ++ (S d :: T) :: up s).
        { rewrite He2'. rewrite rev_ones_cons, <- app_assoc. reflexivity. }
        assert (Hesok : esok (length W :: es1)) by (constructor; [exact (proj2 Hw1) | exact Hok1]).
        destruct (enc_inj s2 _ _ _ I2 Hesok EE Hs2) as [Hes2 [Hfr2 Hup2]].
        assert (HR : RL (S d :: T) (S (S d) :: T)) by apply RL_dec.
        assert (Hw2 : work (S d :: T)) by (split; [exact EE | destruct Hw as [_ Hw]; simpl in *; lia]).
        assert (Hj2 : length (es s2) = S j) by (rewrite Hes2; simpl; rewrite Hl1; reflexivity).
        destruct (IHf (S d :: T) HR s2 (eq_sym Hfr2) I2 Hj2 Hw2) as [s' [Hst [I' [Hd' [HP' Hf']]]]].
        assert (HP2' : Psi (S j) s2 = evalP (Mq Gm (S j)) 0 (S d :: T) (B0min s2)).
        { unfold Psi. rewrite (all1_deep _ Hd2), Hfr2. reflexivity. }
        exists s'. split; [econstructor; [exact St |]; eapply star_trans; [exact Hst1 | exact Hst] |].
        split; [exact I' | split; [exact Hd' | split; [lia |]]].
        rewrite Hfr2, Hup2 in Hf'. rewrite <- Ef. simpl length in *. exact Hf'.
Qed.

End Generic.
