(** * BB29: scan lemmas S1-S10 (BB29/analysis/REPORT.md section 3b), including the COPY lemma. *)

From BB8 Require Import BB29_tm BB29_rules.
From Coq Require Import Lia List.
Import ListNotations.
Set Default Goal Selector "!".

(** ** Word predicates and hydra words *)

Definition isOC (p : pr) : Prop := p = pO \/ p = pC.
Definition OC (w : list pr) : Prop := Forall isOC w.
Definition OCX (w : list pr) : Prop := Forall (fun p => p <> pZ) w.

Definition leaf : list pr := [pO; pC].
Definition Bk (k : nat) : list pr := [pO] ++ leaf^^k ++ [pC].   (* B node with k leaves *)
Definition BB (A : list nat) : list pr := flat_map Bk A.          (* the B-children of an A node *)
Definition encA (A : list nat) : list pr := [pO] ++ BB A ++ [pC].
Definition encH (hs : list (list nat)) : list pr := flat_map encA hs.

Ltac ocb := unfold OC, isOC; repeat (apply Forall_cons || apply Forall_nil || (left; reflexivity) || (right; reflexivity)).

Lemma isOC_O : isOC pO. Proof. left; reflexivity. Qed.
Lemma isOC_C : isOC pC. Proof. right; reflexivity. Qed.
Lemma OC_nil : OC []. Proof. constructor. Qed.
Lemma OC_cons : forall p w, isOC p -> OC w -> OC (p :: w). Proof. intros; constructor; assumption. Qed.
Lemma OC_app : forall a b, OC a -> OC b -> OC (a ++ b). Proof. intros; apply Forall_app; split; assumption. Qed.
Lemma OC_app_l : forall a b, OC (a ++ b) -> OC a. Proof. intros a b H; apply Forall_app in H; apply H. Qed.
Lemma OC_app_r : forall a b, OC (a ++ b) -> OC b. Proof. intros a b H; apply Forall_app in H; apply H. Qed.
Lemma OC_lpow : forall w k, OC w -> OC (w ^^ k).
Proof. induction k; intros; simpl; [apply OC_nil | apply OC_app; auto]. Qed.
Lemma OC_repeatO : forall b, OC (repeat pO b).
Proof. induction b; simpl; [apply OC_nil | apply OC_cons; [apply isOC_O | assumption]]. Qed.
Lemma OC_leaf : OC leaf. Proof. ocb. Qed.
Lemma OC_Bk : forall k, OC (Bk k).
Proof. intro k. unfold Bk. apply OC_app; [ocb | apply OC_app; [apply OC_lpow, OC_leaf | ocb]]. Qed.
Lemma OC_BB : forall A, OC (BB A).
Proof. induction A; [apply OC_nil | cbn [BB flat_map]; fold (BB A); apply OC_app; [apply OC_Bk | assumption]]. Qed.
Lemma OC_encA : forall A, OC (encA A).
Proof. intro A. unfold encA. apply OC_app; [ocb | apply OC_app; [apply OC_BB | ocb]]. Qed.
Lemma OC_encH : forall hs, OC (encH hs).
Proof. induction hs; [apply OC_nil | cbn [encH flat_map]; fold (encH hs); apply OC_app; [apply OC_encA | assumption]]. Qed.
Lemma OCX_OC : forall w, OC w -> OCX w.
Proof. intros w H. eapply Forall_impl; [| exact H]. intros p [-> | ->]; discriminate. Qed.
Lemma OCX_app : forall a b, OCX a -> OCX b -> OCX (a ++ b). Proof. intros; apply Forall_app; split; assumption. Qed.
Lemma OCX_X : forall w, OCX w -> OCX (pX :: w). Proof. intros; constructor; [discriminate | assumption]. Qed.
Lemma OCX_nil : OCX []. Proof. constructor. Qed.

#[export] Hint Resolve isOC_O isOC_C OC_nil OC_cons OC_app OC_lpow OC_repeatO OC_leaf OC_Bk OC_BB
  OC_encA OC_encH OCX_OC OCX_app OCX_X OCX_nil : ocdb.
Ltac oc := solve [eauto 20 with ocdb].

Lemma rs_Z0 : rs [pZ] (const 0) = const 0.
Proof. simpl. rewrite <- !const_unfold. reflexivity. Qed.

Lemma repeat_snoc : forall {A} (x : A) n, repeat x (S n) = repeat x n ++ [x].
Proof. induction n; simpl; [reflexivity | rewrite <- IHn; reflexivity]. Qed.

(** Marking: O <-> Z, C <-> X. *)
Definition mk (p : pr) : pr := match p with pO => pZ | pC => pX | q => q end.

(** ** Composition tactics *)

Ltac go H :=
  lazymatch goal with
  | |- _ -[ _ ]->+ _ =>
      first [ eapply progress_evstep_trans; [ apply H; try oc | ]
            | eapply evstep_progress_trans; [ apply H; try oc | ] ]
  | |- _ -[ _ ]->* _ =>
      first [ eapply evstep_trans; [ apply progress_evstep; apply H; try oc | ]
            | eapply evstep_trans; [ apply H; try oc | ] ]
  end.

Ltac last H := first [apply H | apply progress_evstep; apply H].

Ltac lnorm := repeat (rewrite <- ls_app || rewrite <- rs_app); repeat rewrite <- app_assoc; repeat rewrite app_nil_r; cbn [app mk].
Ltac fin := apply evstep_refl'; lnorm; reflexivity.

(** ** S1-S4: right scans *)

Lemma Hscan : forall w l r, OCX w -> l {{qH}}> rs w (rs [pZ] r) -->+ ls l w <{{qY}} rs [pO] r.
Proof.
  induction w as [|p w IH]; intros l r Hw; [apply H_Z|].
  inversion Hw; subst. eapply progress_trans; [apply H_mv; assumption | apply IH; assumption].
Qed.

Lemma Hscan0 : forall w l, OCX w -> l {{qH}}> rs w (const 0) -->+ ls l w <{{qY}} rs [pO] (const 0).
Proof. intros w l Hw. pose proof (Hscan w l (const 0) Hw) as H. rewrite rs_Z0 in H. exact H. Qed.

Lemma Kscan : forall w l r, OCX w -> l {{qK}}> rs w (rs [pZ] r) -->+ ls l w <{{qAC}} rs [pC] r.
Proof.
  induction w as [|p w IH]; intros l r Hw; [apply K_Z|].
  inversion Hw; subst. eapply progress_trans; [apply K_mv; assumption | apply IH; assumption].
Qed.

Lemma Kscan0 : forall w l, OCX w -> l {{qK}}> rs w (const 0) -->+ ls l w <{{qAC}} rs [pC] (const 0).
Proof. intros w l Hw. pose proof (Kscan w l (const 0) Hw) as H. rewrite rs_Z0 in H. exact H. Qed.

Lemma Nscan_mv : forall w l r, OC w -> l {{qN}}> rs w r -->* ls l w {{qN}}> r.
Proof.
  induction w as [|p w IH]; intros l r Hw; [apply evstep_refl|].
  inversion Hw as [|? ? Hp Hw']; subst.
  destruct Hp as [-> | ->]; (eapply evstep_trans; [apply progress_evstep; (apply N_O || apply N_C) | apply IH; assumption]).
Qed.

Lemma NscanZ : forall w l r, OC w -> l {{qN}}> rs w (rs [pZ] r) -->+ ls l w <{{qAC}} rs [pX] r.
Proof. intros. go Nscan_mv. apply N_Z. Qed.

Lemma Nscan0 : forall w l, OC w -> l {{qN}}> rs w (const 0) -->+ ls l w <{{qAC}} rs [pX] (const 0).
Proof. intros w l Hw. pose proof (NscanZ w l (const 0) Hw) as H. rewrite rs_Z0 in H. exact H. Qed.

Lemma NscanX : forall w l r, OC w -> l {{qN}}> rs w (rs [pX] r) -->+ ls l w <{{qR}} rs [pX] r.
Proof. intros. go Nscan_mv. apply N_X. Qed.

Lemma Vscan_mv : forall w l r, OC w -> l {{qV}}> rs w r -->* ls l w {{qV}}> r.
Proof.
  induction w as [|p w IH]; intros l r Hw; [apply evstep_refl|].
  inversion Hw as [|? ? Hp Hw']; subst.
  destruct Hp as [-> | ->]; (eapply evstep_trans; [apply progress_evstep; (apply V_O || apply V_C) | apply IH; assumption]).
Qed.

Lemma VscanZ : forall w l r, OC w -> l {{qV}}> rs w (rs [pZ] r) -->+ ls l (w ++ [pZ]) {{qN}}> r.
Proof. intros. go Vscan_mv. rewrite ls_snoc. apply V_Z. Qed.

Lemma VscanX : forall w l r, OC w -> l {{qV}}> rs w (rs [pX] r) -->+ ls l w <{{qB}} rs [pZ] r.
Proof. intros. go Vscan_mv. apply V_X. Qed.

(** ** S5-S8: left scans *)

Lemma Yscan_mv : forall w l r, OC w -> ls l w <{{qY}} r -->* l <{{qY}} rs w r.
Proof.
  induction w as [|p w IH] using rev_ind; intros l r Hw; [apply evstep_refl|].
  apply Forall_app in Hw as [Hw Hp]. inversion Hp as [|? ? Hp' _]; subst.
  rewrite ls_snoc, rs_app.
  destruct Hp' as [-> | ->]; (eapply evstep_trans; [apply progress_evstep; (apply Y_O || apply Y_C) | apply IH; assumption]).
Qed.

Lemma YscanX : forall w l r, OC w -> ls (ls l [pX]) w <{{qY}} r -->+ l <{{qD}} rs [pX] (rs w r).
Proof. intros. go Yscan_mv. apply Y_X. Qed.

Lemma YscanZ : forall w l r, OC w -> ls (ls l [pZ]) w <{{qY}} r -->+ l <{{qP}} rs [pZ] (rs w r).
Proof. intros. go Yscan_mv. apply Y_Z. Qed.

(** The ] variants (] reads O/C like Y, then continues as Y). *)
Lemma RBscan : forall w l r, OC w -> w <> [] -> ls l w <{{qAC}} r -->+ l <{{qY}} rs w r.
Proof.
  intros w l r Hw Hne. destruct w as [|p w _] using rev_ind; [congruence|].
  apply Forall_app in Hw as [Hw Hp]. inversion Hp as [|? ? Hp' _]; subst.
  rewrite ls_snoc, rs_app.
  destruct Hp' as [-> | ->]; (eapply progress_evstep_trans; [(apply RB_O || apply RB_C) | apply Yscan_mv; assumption]).
Qed.

Lemma RBscanX : forall w l r, OC w -> w <> [] -> ls (ls l [pX]) w <{{qAC}} r -->+ l <{{qD}} rs [pX] (rs w r).
Proof. intros. go RBscan. last Y_X. Qed.

Lemma RBscanZ : forall w l r, OC w -> w <> [] -> ls (ls l [pZ]) w <{{qAC}} r -->+ l <{{qP}} rs [pZ] (rs w r).
Proof. intros. go RBscan. last Y_Z. Qed.

Lemma Dscan_mv : forall w l r, OC w -> ls l w <{{qD}} r -->* l <{{qD}} rs w r.
Proof.
  induction w as [|p w IH] using rev_ind; intros l r Hw; [apply evstep_refl|].
  apply Forall_app in Hw as [Hw Hp]. inversion Hp as [|? ? Hp' _]; subst.
  rewrite ls_snoc, rs_app.
  destruct Hp' as [-> | ->]; (eapply evstep_trans; [apply progress_evstep; (apply D_O || apply D_C) | apply IH; assumption]).
Qed.


Lemma Dscan : forall w l p r, isOC p -> OC w -> ls (ls l [mk p]) w <{{qD}} r -->+ ls l [p] {{qF}}> rs w r.
Proof. intros w l p r [-> | ->] Hw; go Dscan_mv; [last D_Z | last D_X]. Qed.

Lemma Pwalk : forall b l r, ls l (repeat pO b) <{{qP}} r -->* l <{{qP}} rs (repeat pO b) r.
Proof.
  induction b as [|b IH]; intros l r; [apply evstep_refl|].
  rewrite repeat_snoc, ls_snoc, rs_app.
  eapply evstep_trans; [apply progress_evstep, P_O | apply IH].
Qed.

Lemma Berase : forall j l r, ls (ls l [pO]) (repeat pC j) <{{qB}} r -->+ l <{{qR}} rs [pX] (rs (repeat pZ j) r).
Proof.
  induction j as [|j IH]; intros l r; [apply B_O|].
  rewrite repeat_snoc, ls_snoc, (repeat_snoc pZ), rs_app.
  eapply progress_trans; [apply B_C | apply IH].
Qed.

(** ** S9: depth scans *)

Lemma leaf_T : forall l r, ls l leaf <{{qT}} r -->+ l <{{qT}} rs leaf r.
Proof. intros. eapply progress_trans; [apply T_C | apply BS_O]. Qed.

Lemma leaves_T : forall k l r, ls l (leaf^^k) <{{qT}} r -->* l <{{qT}} rs (leaf^^k) r.
Proof.
  induction k as [|k IH]; intros l r; [apply evstep_refl|].
  cbn [lpow]. rewrite ls_app, rs_app.
  eapply evstep_trans; [apply IH | apply progress_evstep, leaf_T].
Qed.

Lemma Bk_R : forall k l r, ls l (Bk k) <{{qR}} r -->+ l <{{qR}} rs (Bk k) r.
Proof.
  intros. unfold Bk. rewrite !ls_app, !rs_app.
  eapply progress_trans; [apply R_C|]. go leaves_T. last T_O.
Qed.

Lemma BB_R : forall A l r, ls l (BB A) <{{qR}} r -->* l <{{qR}} rs (BB A) r.
Proof.
  induction A as [|k A IH]; intros l r; [apply evstep_refl|].
  cbn [BB flat_map]. fold (BB A). rewrite ls_app, rs_app.
  eapply evstep_trans; [apply IH | apply progress_evstep, Bk_R].
Qed.

(** S9a: the parent's open bracket is found (non-root parent; children of height <= 1). *)
Lemma S9a : forall A l r, ls (ls l [pO]) (BB A) <{{qR}} rs [pX] r -->+ ls l [pZ] {{qH}}> rs (BB A) (rs [pX] r).
Proof. intros. go BB_R. last R_O. Qed.

(** Depth-1 scan over the B-children of an A node: either it returns to depth 1, or the
    escape fires (some B has a leaf) and Y is left on an O/C prefix. *)
Lemma Bs_T : forall A l r,
  (ls l (BB A) <{{qT}} r -->* l <{{qT}} rs (BB A) r) \/
  (exists u v, BB A = u ++ v /\ OC u /\ ls l (BB A) <{{qT}} r -->+ ls l u <{{qY}} rs v r).
Proof.
  induction A as [|k A IH]; intros l r; [left; apply evstep_refl|].
  cbn [BB flat_map]. fold (BB A).
  destruct (IH (ls l (Bk k)) r) as [Hf | [u [v [Huv [Hu Hesc]]]]].
  - destruct k as [|k].
    + left. rewrite ls_app, rs_app. eapply evstep_trans; [apply Hf|]. apply progress_evstep, leaf_T.
    + right. exists ([pO] ++ leaf^^k), ([pO; pC; pC] ++ BB A). split; [|split].
      * unfold Bk. cbn [lpow]. rewrite <- lpow_shift. unfold leaf. rewrite <- !app_assoc. reflexivity.
      * oc.
      * rewrite ls_app. go Hf.
        unfold Bk. cbn [lpow]. rewrite <- lpow_shift.
        rewrite <- !app_assoc. rewrite !ls_app.
        eapply progress_evstep_trans; [apply T_C|].
        change (ls ?L leaf) with (ls (ls L [pO]) [pC]).
        eapply evstep_trans; [apply progress_evstep, BS_C|].
        eapply evstep_trans; [apply progress_evstep, S_O|].
        fin.
  - right. exists (Bk k ++ u), v. split; [|split].
    + rewrite Huv. apply app_assoc.
    + oc.
    + rewrite ls_app. eapply progress_evstep_trans; [apply Hesc|]. fin.
Qed.

Lemma encA_R : forall A l r,
  (ls l (encA A) <{{qR}} r -->+ l <{{qR}} rs (encA A) r) \/
  (exists u v, encA A = u ++ v /\ OC u /\ ls l (encA A) <{{qR}} r -->+ ls l u <{{qY}} rs v r).
Proof.
  intros A l r. unfold encA.
  destruct (Bs_T A (ls l [pO]) (rs [pC] r)) as [Hf | [u [v [Huv [Hu Hesc]]]]].
  - left. rewrite !ls_app, !rs_app. eapply progress_trans; [apply R_C|]. go Hf. last T_O.
  - right. exists ([pO] ++ u), (v ++ [pC]). split; [|split].
    + rewrite Huv. rewrite <- !app_assoc. reflexivity.
    + oc.
    + rewrite !ls_app. eapply progress_trans; [apply R_C|]. eapply progress_evstep_trans; [apply Hesc|]. fin.
Qed.

(** S9b: scanning back over the whole hydra to the separator (root parent). *)
Lemma S9b : forall hs l r, ls (ls l [pZ]) (encH hs) <{{qR}} r -->+ l <{{qP}} rs [pZ] (rs (encH hs) r).
Proof.
  induction hs as [|A hs IH] using rev_ind; intros l r; [apply R_Z|].
  unfold encH. rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r. fold (encH hs).
  rewrite ls_app, rs_app.
  destruct (encA_R A (ls (ls l [pZ]) (encH hs)) r) as [Hf | [u [v [Huv [Hu Hesc]]]]].
  - eapply progress_trans; [apply Hf | apply IH].
  - eapply progress_trans; [apply Hesc|]. rewrite <- ls_app.
    eapply progress_evstep_trans; [apply YscanZ; oc|]. rewrite Huv. fin.
Qed.

(** ** S10: COPY *)

Lemma copy_step : forall l u p t s2 c, isOC p -> isOC t -> OC s2 -> OC c -> c <> [] ->
  ls l (u ++ [mk p] ++ t :: s2) <{{qD}} rs [pX] (rs c (const 0)) -->+
  ls l ((u ++ [p]) ++ [mk t] ++ s2) <{{qD}} rs [pX] (rs (c ++ [t]) (const 0)).
Proof.
  intros l u p t s2 c Hp Ht Hs2 Hc Hne.
  rewrite !ls_app. eapply progress_evstep_trans; [apply Dscan; oc|].
  change (rs (t :: s2) ?x) with (rs [t] (rs s2 x)).
  destruct Ht as [-> | ->].
  - eapply evstep_trans; [apply progress_evstep, F_O|].
    rewrite <- !rs_app. eapply evstep_trans; [apply progress_evstep, Hscan0; oc|].
    rewrite !ls_app. eapply evstep_trans; [apply progress_evstep, YscanX; assumption|].
    fin.
  - eapply evstep_trans; [apply progress_evstep, F_C|].
    rewrite <- !rs_app. eapply evstep_trans; [apply progress_evstep, Kscan0; oc|].
    rewrite !ls_app. eapply evstep_trans; [apply progress_evstep, RBscanX; assumption|].
    fin.
Qed.

Lemma copy_loop : forall s2 l u p c, isOC p -> OC s2 -> OC c -> c <> [] ->
  ls l (u ++ [mk p] ++ s2) <{{qD}} rs [pX] (rs c (const 0)) -->+
  ls l (u ++ [p] ++ s2 ++ [pC] ++ c ++ s2) <{{qAC}} rs [pX] (const 0).
Proof.
  induction s2 as [|t s2 IH]; intros l u p c Hp Hs2 Hc Hne.
  - rewrite app_nil_r, ls_app. destruct Hp as [-> | ->].
    + eapply progress_evstep_trans; [apply D_Z|].
      eapply evstep_trans; [apply progress_evstep, F_X|].
      eapply evstep_trans; [apply progress_evstep, Nscan0; assumption|]. fin.
    + eapply progress_evstep_trans; [apply D_X|].
      eapply evstep_trans; [apply progress_evstep, F_X|].
      eapply evstep_trans; [apply progress_evstep, Nscan0; assumption|]. fin.
  - inversion Hs2 as [|? ? Ht Hs2']; subst.
    eapply progress_trans; [apply copy_step; assumption|].
    eapply progress_evstep_trans; [apply IH; [assumption | assumption | oc | destruct c; simpl; congruence]|].
    fin.
Qed.

Lemma COPY : forall s l, OC s ->
  ls l [pZ] {{qH}}> rs s (rs [pX] (const 0)) -->+ ls l ([pO] ++ s ++ [pC; pO] ++ s) <{{qAC}} rs [pX] (const 0).
Proof.
  intros s l Hs. rewrite <- rs_app.
  eapply progress_trans; [apply Hscan0; oc|].
  rewrite ls_app. eapply progress_trans; [apply Y_X|].
  eapply progress_evstep_trans; [apply (copy_loop s l [] pO [pO]); [oc | assumption | oc | discriminate]|].
  fin.
Qed.
