(** B21: processing of a frontier block (nested induction), on top of the invariant. *)
From Coq Require Import Lia PeanoNat List Bool Wellfounded Wf_nat.
From BB8 Require Import BB21_B21_absdef BB21_B21_grow BB21_B21_steps BB21_B21_inv.
Import ListNotations.
Set Default Goal Selector "!".

Section Generic.
Variable refill : nat -> list nat -> res.

(** abstract reachability for the machine with refill rule [refill] *)
Inductive star : list (list nat) -> list (list nat) -> Prop :=
  | star_refl : forall b, star b b
  | star_step : forall b b' b'', astepG refill b = Next b' -> star b' b'' -> star b b''.

Lemma star_trans : forall a b c, star a b -> star b c -> star a c.
Proof. intros a b c H1 H2. induction H1; [exact H2 | econstructor; [exact H | apply IHstar; exact H2]]. Qed.

(** reverse-lexicographic order on blocks of equal length *)
Fixpoint lexlt (l1 l2 : list nat) : Prop :=
  match l1, l2 with
  | a :: t1, b :: t2 => a < b \/ (a = b /\ lexlt t1 t2)
  | _, _ => False
  end.

Definition LR (a b : list nat) : Prop := length a = length b /\ lexlt a b.

Lemma LR_acc : forall n l, length l = n -> Acc LR l.
Proof.
  induction n as [| n IH]; intros l Hl.
  - constructor. intros y [Hy Hlt]. destruct l; [| discriminate]. destruct y; simpl in Hlt; contradiction.
  - destruct l as [| a m]; [discriminate |]. simpl in Hl. injection Hl as Hm.
    assert (Am : Acc LR m) by (apply IH; exact Hm).
    revert m Hm Am. induction a as [a IHa] using (well_founded_induction lt_wf).
    intros m Hm Am. induction Am as [m _ IHm].
    constructor. intros y [Hy Hlt]. destruct y as [| b m']; [simpl in Hlt; contradiction |].
    simpl in Hy. injection Hy as Hy. simpl in Hlt. destruct Hlt as [Hlt | [-> Hlt]].
    + apply IHa; [exact Hlt | lia | apply IH; lia].
    + apply IHm; [split; [lia | exact Hlt] | lia].
Qed.

Definition RL (a b : list nat) : Prop := LR (rev a) (rev b).

Lemma RL_wf : well_founded RL.
Proof. unfold RL. apply (wf_inverse_image _ _ LR (@rev nat)). intros l. apply (LR_acc (length l)). reflexivity. Qed.

Lemma lexlt_app : forall P a b, lexlt a b -> lexlt (P ++ a) (P ++ b).
Proof. induction P as [| p P IH]; intros a b H; simpl; [exact H | right; split; [reflexivity | apply IH; exact H]]. Qed.

Lemma RL_dec : forall d T, RL (S d :: T) (S (S d) :: T).
Proof.
  intros. unfold RL, LR. simpl. rewrite !app_length. split; [reflexivity |].
  apply lexlt_app. simpl. left. lia.
Qed.

Lemma RL_est : forall p e T y, RL (repeat 1 p ++ y :: S e :: T) (1 :: repeat 1 p ++ S (S e) :: T).
Proof.
  intros. unfold RL, LR. split.
  - rewrite !rev_length. simpl. rewrite !app_length. simpl. lia.
  - change (1 :: repeat 1 p ++ S (S e) :: T) with ([1] ++ repeat 1 p ++ [S (S e)] ++ T).
    replace (repeat 1 p ++ y :: S e :: T) with ((repeat 1 p ++ [y]) ++ [S e] ++ T) by (rewrite <- app_assoc; reflexivity).
    rewrite !rev_app_distr. rewrite <- !app_assoc. apply lexlt_app. simpl. left. lia.
Qed.

(** list-level invariant *)
Definition INVL (L : list (list nat)) : Prop := exists s, enc s = L /\ INV s.

Lemma split_unique : forall A B f f' u u', Forall (fun e => 2 <= e) A -> Forall (fun e => 2 <= e) B ->
  isE f = false -> isE f' = false -> map ones A ++ f :: u = map ones B ++ f' :: u' -> A = B /\ f = f' /\ u = u'.
Proof.
  induction A as [| a A IH]; intros B f f' u u' HA HB Hf Hf' Hs; destruct B as [| b B]; simpl in Hs.
  - injection Hs as -> ->. auto.
  - injection Hs as E1 E2. subst f. inversion HB; subst. rewrite isE_ones in Hf by lia. discriminate.
  - injection Hs as E1 E2. subst f'. inversion HA; subst. rewrite isE_ones in Hf' by lia. discriminate.
  - injection Hs as E1 E2. inversion HA; inversion HB; subst.
    assert (a = b) by (apply (f_equal (@length nat)) in E1; unfold ones in E1; rewrite !repeat_length in E1; exact E1). subst b.
    destruct (IH B f f' u u' H2 H6 Hf Hf' E2) as [-> [-> ->]]. auto.
Qed.

Lemma enc_inj : forall s es' fr' up', INV s -> esok es' -> isE fr' = false ->
  enc s = b0 s :: rev (map ones es') ++ fr' :: up' -> es s = es' /\ fr s = fr' /\ up s = up'.
Proof.
  intros s es' fr' up' I He HE Hs. unfold enc in Hs. apply (f_equal (@tl (list nat))) in Hs. simpl in Hs.
  rewrite <- !map_rev in Hs.
  destruct (split_unique _ _ _ _ _ _ (Forall_rev (i_es s I)) (Forall_rev He) (i_frE s I) HE Hs) as [HA [Hf Hu]].
  split; [| split; assumption]. rewrite <- (rev_involutive (es s)), HA, rev_involutive. reflexivity.
Qed.

Definition work (b : list nat) := isE b = false /\ 2 <= length b.

Definition ProcPost (s : st) (j : nat) : Prop :=
  exists b0' es', star (enc s) (b0' :: rev (map ones es') ++ ones (length (fr s)) :: up s) /\
    length es' = j /\ esok es' /\ deep b0' /\ INVL (b0' :: rev (map ones es') ++ ones (length (fr s)) :: up s).

Lemma lsplit_hd : forall l p r, lsplit l = (p, r) -> hd 0 r <> 1.
Proof.
  induction l as [| d l IH]; intros p r H; simpl in H.
  - inversion H; subst. simpl. lia.
  - destruct d as [| [| d]].
    + inversion H; subst. simpl. lia.
    + destruct (lsplit l) as [p' r'] eqn:E. inversion H; subst. apply (IH p' r eq_refl).
    + inversion H; subst. simpl. lia.
Qed.

Lemma isE_cons1 : forall tl, isE (1 :: tl) = isE (1 :: tl).
Proof. reflexivity. Qed.

Lemma isE_true_ones : forall b, isE b = true -> b = ones (length b) /\ 2 <= length b.
Proof.
  intros b H. unfold isE in H. apply andb_true_iff in H as [H1 H2]. apply Nat.leb_le in H2.
  split; [apply all1_ones_eq; exact H1 | exact H2].
Qed.

Lemma b0ok_of : forall s, INV s -> b0ok (b0 s).
Proof.
  intros s I. pose proof (i_chain s I) as Ch. pose proof (chain_lower _ _ _ Ch) as [_ Hn].
  destruct (i_b0 s I) as [[m Hm] | [[m Hm] | [m [[k [Hm _]] | Hm]]]]; rewrite Hm.
  - unfold ones. exists 1, 1, (repeat 1 m). split; [reflexivity |]. unfold nzd. constructor; [lia |].
    apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
  - destruct m; simpl.
    + exists 1, 5, []. split; [reflexivity | unfold nzd; repeat constructor; lia].
    + exists 1, 1, (repeat 1 m ++ [5]). split; [reflexivity |]. unfold nzd. constructor; [lia |].
      apply Forall_app. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia | repeat constructor; lia].
  - destruct m; simpl.
    + exists 1, 4, (repeat 1 k ++ [2]). split; [reflexivity |]. unfold nzd. constructor; [lia |].
      apply Forall_app. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia | repeat constructor; lia].
    + exists 1, 1, (repeat 1 m ++ Xs k). split; [reflexivity |]. unfold nzd. constructor; [lia |].
      apply Forall_app. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia |].
      unfold Xs. constructor; [lia |]. apply Forall_app. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia | repeat constructor; lia].
  - destruct m; simpl.
    + exists 1, 4, [1]. split; [reflexivity | unfold nzd; repeat constructor; lia].
    + exists 1, 1, (repeat 1 m ++ [4; 1]). split; [reflexivity |]. unfold nzd. constructor; [lia |].
      apply Forall_app. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia | repeat constructor; lia].
Qed.

Lemma enc_mk : forall b es fr up, enc (mk b es fr up) = b :: rev (map ones es) ++ fr :: up.
Proof. reflexivity. Qed.

Lemma rev_ones_cons : forall w es, rev (map ones (w :: es)) = rev (map ones es) ++ [ones w].
Proof. reflexivity. Qed.

Lemma proc : forall j s, INV s -> length (es s) = j -> work (fr s) -> ProcPost s j.
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
      assert (HR : RL (fr s1) (1 :: T)) by (rewrite (lsplit_spec _ _ _ El); apply RL_est).
      assert (Hl1 : length (fr s1) = length (fr s)).
      { destruct HR as [HR _]. rewrite !rev_length in HR. rewrite <- Ef. exact HR. }
      assert (Hw1 : work (fr s1)) by (split; [exact (i_frE s1 I1) | rewrite Hl1, <- Ef; exact (proj2 Hw)]).
      assert (Hj1 : length (es s1) = 0) by (simpl; rewrite Ees; reflexivity).
      destruct (IHf (fr s1) HR s1 eq_refl I1 Hj1 Hw1) as [b0' [es'' [Hst [Hl [Hok [Hbg Hinv]]]]]].
      exists b0', es''. rewrite <- Hl1. split; [| split; [exact Hl | split; [exact Hok | split; [exact Hbg | exact Hinv]]]].
      econstructor; [exact St | exact Hst].
    + (* decrement into b0 *)
      assert (St : astepG refill (enc s) = Next (b0m s :: (S d :: T) :: up s)).
      { unfold b0m. apply (step_dec_0 refill s d T Hb Ees (eq_sym Ef) (jacc_even s I) (jacc_ge s I)). }
      destruct (isE (S d :: T)) eqn:EE.
      * (* the frontier block is completed *)
        destruct (isE_true_ones _ EE) as [Eo Elen].
        destruct d as [| d]; [| unfold ones in Eo; simpl in Eo; discriminate].
        assert (HT : all1 T = true) by (unfold isE in EE; simpl in EE; apply andb_true_iff in EE as [EE _]; exact EE).
        assert (HTn : T <> []) by (intros ->; simpl in Elen; lia).
        destruct (inv_compl s T I Ees (eq_sym Ef) HT HTn) as [Es [fr2 [up2 [Hu I2]]]].
        exists (b0m s), []. split; [| split; [reflexivity | split; [constructor | split]]].
        -- econstructor; [exact St |]. simpl. rewrite <- Ef. simpl length. rewrite Eo. simpl length. constructor.
        -- apply (b0m_deep s I Ees). apply big_not_pure. apply (i_F2 s I). rewrite <- Ef. reflexivity.
        -- exists (mk (b0m s) (rev Es ++ [length (fr s)]) fr2 up2). split; [| exact I2].
           rewrite enc_mk. rewrite map_app, rev_app_distr, map_rev, rev_involutive. simpl.
           rewrite Hu. reflexivity.
      * set (s1 := mk (b0m s) [] (S d :: T) (up s)).
        assert (I1 : INV s1) by (apply (inv_dec_b0 s d T I Ees (eq_sym Ef) EE)).
        assert (HR : RL (S d :: T) (S (S d) :: T)) by apply RL_dec.
        assert (Hw1 : work (S d :: T)) by (split; [exact EE | destruct Hw as [_ Hw]; simpl in *; lia]).
        destruct (IHf (S d :: T) HR s1 eq_refl I1 eq_refl Hw1) as [b0' [es'' [Hst [Hl [Hok [Hbg Hinv]]]]]].
        exists b0', es''. split; [| split; [exact Hl | split; [exact Hok | split; [exact Hbg |]]]].
        -- econstructor; [exact St |]. rewrite <- Ef. exact Hst.
        -- rewrite <- Ef. exact Hinv.
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
      assert (HR : RL (fr s1) (1 :: T)) by (rewrite (lsplit_spec _ _ _ El); apply RL_est).
      assert (Hl1 : length (fr s1) = length (fr s)).
      { destruct HR as [HR _]. rewrite !rev_length in HR. rewrite <- Ef. exact HR. }
      assert (Hw1 : work (fr s1)) by (split; [exact (i_frE s1 I1) | rewrite Hl1, <- Ef; exact (proj2 Hw)]).
      assert (Hj1 : length (es s1) = S j) by (simpl; rewrite map_length; exact Hj).
      destruct (IHf (fr s1) HR s1 eq_refl I1 Hj1 Hw1) as [b0' [es'' [Hst [Hl [Hok [Hbg Hinv]]]]]].
      exists b0', es''. rewrite <- Hl1. split; [| split; [exact Hl | split; [exact Hok | split; [exact Hbg | exact Hinv]]]].
      econstructor; [exact St | exact Hst].
    + (* decrement into the nearest E *)
      destruct (es s) as [| e es'] eqn:Ees; [simpl in Hj; discriminate |]. simpl in Hj. injection Hj as Hj.
      set (W := ones (pred e) ++ Xl ((jacc s - 4) / 2)).
      set (s1 := mk (ones (length (b0 s) - 1)) (map pred es') W ((S d :: T) :: up s)).
      assert (St : astepG refill (enc s) = Next (enc s1)).
      { apply (step_dec_es refill s d T e es' Hb (i_es s I) (eq_sym Ef) Ees (jacc_even s I) (jacc_ge s I)). }
      assert (I1 : INV s1) by (apply (inv_dec_es s d T e es' I (eq_sym Ef) Ees)).
      assert (Hw1 : work W).
      { destruct (W_props (pred e) ((jacc s - 4) / 2)) as (WL & _ & WE & _). split; [exact WE |].
        fold W in WL. rewrite WL. pose proof (i_es s I) as He'. rewrite Ees in He'. inversion He'; subst. lia. }
      assert (Hj1 : length (es s1) = j) by (simpl; rewrite map_length; exact Hj).
      destruct (IHj s1 I1 Hj1 Hw1) as [b1 [es1 [Hst1 [Hl1 [Hok1 [Hbg1 Hinv1]]]]]].
      simpl fr in Hst1, Hinv1. simpl up in Hst1, Hinv1.
      destruct (isE (S d :: T)) eqn:EE.
      * (* the frontier block is completed by this decrement *)
        destruct (isE_true_ones _ EE) as [Eo Elen].
        exists b1, (length W :: es1). split; [| split; [simpl; rewrite Hl1; reflexivity | split; [constructor; [exact (proj2 Hw1) | exact Hok1] | split; [exact Hbg1 |]]]].
        -- econstructor; [exact St |]. rewrite rev_ones_cons, <- app_assoc. simpl app.
           rewrite <- Ef. change (length (S (S d) :: T)) with (length (S d :: T)). rewrite <- Eo. exact Hst1.
        -- rewrite rev_ones_cons, <- app_assoc. simpl app. rewrite <- Ef.
           change (length (S (S d) :: T)) with (length (S d :: T)). rewrite <- Eo. exact Hinv1.
      * destruct Hinv1 as [s2 [He2 I2]].
        assert (Hs2 : enc s2 = b0 s2 :: rev (map ones (length W :: es1)) ++ (S d :: T) :: up s).
        { rewrite He2. assert (b0 s2 = b1) by (unfold enc in He2; injection He2 as ->; reflexivity).
          rewrite H. rewrite rev_ones_cons, <- app_assoc. reflexivity. }
        assert (Hesok : esok (length W :: es1)) by (constructor; [exact (proj2 Hw1) | exact Hok1]).
        destruct (enc_inj s2 _ _ _ I2 Hesok EE Hs2) as [Hes2 [Hfr2 Hup2]].
        assert (HR : RL (S d :: T) (S (S d) :: T)) by apply RL_dec.
        assert (Hw2 : work (S d :: T)) by (split; [exact EE | destruct Hw as [_ Hw]; simpl in *; lia]).
        assert (Hj2 : length (es s2) = S j) by (rewrite Hes2; simpl; rewrite Hl1; reflexivity).
        destruct (IHf (S d :: T) HR s2 (eq_sym Hfr2) I2 Hj2 Hw2) as [b0' [es'' [Hst [Hl [Hok [Hbg Hinv]]]]]].
        exists b0', es''. rewrite Hfr2, Hup2 in Hst, Hinv. rewrite <- Ef. simpl length in *.
        split; [| split; [exact Hl | split; [exact Hok | split; [exact Hbg | exact Hinv]]]].
        econstructor; [exact St |]. eapply star_trans; [exact Hst1 |].
        rewrite <- He2. exact Hst.
Qed.

End Generic.
