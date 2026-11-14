(** * Generic ordinal and hydra lemmas for the hydra-game machines (BB31, BB33)

    Used by BB31 and BB33.  Axiom-free.  Contents:
    - [bachmann]: the Bachmann property of the fundamental sequences of Ord.v:
        x[n] < y < x  ->  x[n] <= y[1].
    - [desc_between]: every y with x[n] <= y < x descends to x[n] by [1]-steps.  With
      [Hardy.hardy_game] this means a hydra round only has to land in [x[n], x).
    - [desc_fs_succ], [FGH_lim_step]: f_x(n) + n <= f_x(n+1) for limit x and n >= 1.
    - [ocons]: x |-> omega^a + x as an ordinary (absorbing) ordinal sum, on Cantor normal forms.
    - Hydras: [tree], the ordinal [otree]/[olist] (ordinary sum of omega^(children) in tape
      order), the spine representation [plug], the height bound [hb], and [chop_ord]: one hydra
      round (remove the rightmost head, n copies of its shortened parent) moves the ordinal x of
      the hydra into [x[n], x). *)

From BB8 Require Import Ord Hardy.
From Coq Require Import Arith Lia List.
Import ListNotations.
Set Default Goal Selector "!".

(** ** Order helpers *)

Lemma olt_osucc : forall a, olt a (osucc a).
Proof.
  unfold osucc. induction a as [|c _ d IH]; simpl; [apply olt_z | apply olt_tail; exact IH].
Qed.

Lemma olt_osucc_le : forall a g, olt g (osucc a) -> ole g a.
Proof.
  unfold osucc. induction a as [|c _ d IH]; intros g H; simpl in H.
  - inversion H as [| ? ? ? ? Hh | ? ? ? Ht]; subst.
    + apply ole_refl.
    + inversion Hh.
    + inversion Ht.
  - inversion H as [| ? ? ? ? Hh | ? ? ? Ht]; subst.
    + apply ole_oz.
    + right. apply olt_head. exact Hh.
    + destruct (IH _ Ht) as [<-|H']; [apply ole_refl | right; apply olt_tail; exact H'].
Qed.

Lemma olt_head_inv : forall a b c d, olt (ow a b) (ow c d) -> ole a c.
Proof.
  intros a b c d H. inversion H as [| ? ? ? ? Hh | ? ? ? Ht]; subst; [right; exact Hh | left; reflexivity].
Qed.

Lemma ole_cons : forall a x y, ole x y -> ole (ow a x) (ow a y).
Proof. intros a x y [<-|H]; [left; reflexivity | right; apply olt_tail; exact H]. Qed.

Lemma ole_pow : forall a b, ole a b -> ole (ow a oz) (ow b oz).
Proof. intros a b [<-|H]; [left; reflexivity | right; apply olt_head; exact H]. Qed.

Lemma ocmp_cases : forall a b,
  (ocmp a b = Eq /\ a = b) \/ (ocmp a b = Lt /\ olt a b) \/ (ocmp a b = Gt /\ olt b a).
Proof.
  intros a b. destruct (ocmp a b) eqn:E.
  - left. split; [reflexivity | apply ocmp_Eq; exact E].
  - right; left. split; [reflexivity | apply ocmp_Lt; exact E].
  - right; right. split; [reflexivity | apply ocmp_Gt; exact E].
Qed.

Lemma ocmp_refl : forall x, ocmp x x = Eq.
Proof.
  intro x. destruct (ocmp_cases x x) as [[E _]|[[_ H]|[_ H]]]; [exact E | exfalso; exact (olt_irrefl _ H)..].
Qed.

Lemma olt_ole_contra : forall x y, olt x y -> ole y x -> False.
Proof.
  intros x y H [<-|H']; [exact (olt_irrefl _ H) | exact (olt_irrefl _ (olt_trans _ _ _ H H'))].
Qed.

Definition oz_dec (x : ord) : {x = oz} + {x <> oz}.
Proof. destruct x; [left; reflexivity | right; discriminate]. Defined.

(** ** The Bachmann property *)

Lemma bach_succ : forall a' n y, nf y -> olt (orep a' n oz) y -> olt y (opow (osucc a')) ->
  ole (orep a' n oz) (fs y 1).
Proof.
  intros a' n. induction n as [|n IH]; intros y Hy H1 H2; [apply ole_oz|].
  destruct y as [|g r]; [inversion H1|].
  cbn [orep] in H1.
  assert (Hg : ole g a').
  { unfold opow in H2. inversion H2 as [| ? ? ? ? Hh | ? ? ? Ht]; subst.
    - apply olt_osucc_le. exact Hh.
    - inversion Ht. }
  assert (Hr : g = a' /\ olt (orep a' n oz) r).
  { inversion H1 as [| ? ? ? ? Hh | ? ? ? Ht]; subst.
    - exfalso. exact (olt_ole_contra _ _ Hh Hg).
    - split; [reflexivity | exact Ht]. }
  destruct Hr as [-> Hr].
  assert (Hne : r <> oz) by (intro; subst; inversion Hr).
  rewrite fs_cons by exact Hne. cbn [orep]. apply ole_cons.
  apply IH; [eapply nf_tail; eassumption | exact Hr |].
  destruct r as [|h t]; [apply olt_z|]. unfold opow. apply olt_head.
  apply nf_head_le in Hy. simpl in Hy. eapply ole_olt_trans; [exact Hy | apply olt_osucc].
Qed.

(** x[n] < y < x  ->  x[n] <= y[1]  (all terms normal). *)
Theorem bachmann : forall x n y, nf x -> nf y -> olt (fs x n) y -> olt y x -> ole (fs x n) (fs y 1).
Proof.
  induction x as [|a IHa b IHb]; intros n y Hx Hy H1 H2; [inversion H2|].
  destruct b as [|c d].
  - destruct a as [|a1 a2].
    + (* x = 1 *) exfalso. inversion H2 as [| ? ? ? ? Hh | ? ? ? Ht]; subst.
      * inversion H1.
      * inversion Hh.
      * inversion Ht.
    + destruct (opred (ow a1 a2)) as [a'|] eqn:E.
      * (* x = omega^(a'+1) *)
        rewrite (fs_pow_succ _ _ _ E) in *. apply opred_inv in E. rewrite E in H2.
        apply bach_succ; assumption.
      * (* x = omega^l, l limit *)
        rewrite (fs_pow_lim (ow a1 a2) n ltac:(discriminate) E) in *.
        set (a := ow a1 a2) in *.
        destruct y as [|g r]; [inversion H1|].
        assert (Hga : olt g a).
        { inversion H2 as [| ? ? ? ? Hh | ? ? ? Ht]; subst; [exact Hh | inversion Ht]. }
        destruct (oz_dec r) as [->|Hr].
        -- assert (Hlt : olt (fs a n) g).
           { inversion H1 as [| ? ? ? ? Hh | ? ? ? Ht]; subst; [exact Hh | inversion Ht]. }
           destruct g as [|g1 g2]; [inversion Hlt|].
           destruct (opred (ow g1 g2)) as [g'|] eqn:Eg.
           ++ rewrite (fs_pow_succ _ _ _ Eg). cbn [orep]. apply ole_pow.
              apply opred_inv in Eg. rewrite Eg in Hlt. apply olt_osucc_le. exact Hlt.
           ++ rewrite (fs_pow_lim (ow g1 g2) 1 ltac:(discriminate) Eg). apply ole_pow.
              apply IHa; [eapply nf_head; eassumption | eapply nf_head; eassumption | exact Hlt | exact Hga].
        -- rewrite (fs_cons g r 1 Hr).
           inversion H1 as [| ? ? ? ? Hh | ? ? ? Ht]; subst.
           ++ right. apply olt_head. exact Hh.
           ++ apply ole_cons. apply ole_oz.
  - (* x = omega^a + (c,d) *)
    rewrite fs_cons in * by discriminate.
    destruct y as [|g r]; [inversion H1|].
    assert (E : g = a /\ olt (fs (ow c d) n) r /\ olt r (ow c d)).
    { inversion H1 as [| ? ? ? ? Hh | ? ? ? Ht]; subst.
      - exfalso. inversion H2 as [| ? ? ? ? Hh' | ? ? ? Ht']; subst.
        + exact (olt_irrefl _ (olt_trans _ _ _ Hh Hh')).
        + exact (olt_irrefl _ Hh).
      - inversion H2 as [| ? ? ? ? Hh' | ? ? ? Ht']; subst.
        + exfalso. exact (olt_irrefl _ Hh').
        + split; [reflexivity | split; assumption]. }
    destruct E as [-> [Hr1 Hr2]].
    assert (Hr : r <> oz) by (intro; subst; inversion Hr1).
    rewrite (fs_cons a r 1 Hr). apply ole_cons.
    apply IHb; [eapply nf_tail; eassumption | eapply nf_tail; eassumption | exact Hr1 | exact Hr2].
Qed.

(** ** Descent *)

(** Every y in [x[n], x) descends to x[n] by [1]-steps. *)
Theorem desc_between : forall y, nf y -> forall x n, nf x -> ole (fs x n) y -> olt y x -> desc 1 y (fs x n).
Proof.
  intros y. induction y as [y IH] using (well_founded_ind wf_ltn).
  intros Hy x n Hx [E|Hlt] Hyx.
  - rewrite E. apply desc_refl.
  - assert (Hne : y <> oz) by (intro; subst; inversion Hlt).
    apply desc_step; [exact Hne|].
    destruct (fs_nf_lt y 1 Hy Hne) as [Hy1 Hy1lt].
    apply IH; [repeat split; assumption | exact Hy1 | exact Hx | | eapply olt_trans; eassumption].
    apply bachmann; assumption.
Qed.

Lemma fs_ne_oz : forall z k, z <> oz -> z <> one -> 1 <= k -> fs z k <> oz.
Proof.
  intros [|a b] k H1 H2 Hk; [congruence|].
  destruct b as [|c d].
  - destruct a as [|a1 a2]; [exfalso; apply H2; reflexivity|].
    destruct (opred (ow a1 a2)) as [a'|] eqn:E.
    + rewrite (fs_pow_succ _ _ _ E). destruct k; [lia|]. discriminate.
    + rewrite (fs_pow_lim (ow a1 a2) k ltac:(discriminate) E). discriminate.
  - rewrite fs_cons by discriminate. discriminate.
Qed.

Lemma desc_one : forall k z, 1 <= k -> nf z -> z <> oz -> desc k z one.
Proof.
  intros k z Hk. induction z as [z IH] using (well_founded_ind wf_ltn). intros Hz Hne.
  destruct (ocmp_cases z one) as [[_ ->]|[[_ H]|[_ H]]].
  - apply desc_refl.
  - exfalso. inversion H as [| ? ? ? ? Hh | ? ? ? Ht]; subst; [congruence | inversion Hh | inversion Ht].
  - assert (H1 : z <> one) by (intro; subst; exact (olt_irrefl _ H)).
    apply desc_step; [exact Hne|].
    destruct (fs_nf_lt z k Hz Hne) as [Hf Hlt].
    apply IH; [repeat split; assumption | exact Hf | apply fs_ne_oz; assumption].
Qed.

(** For a limit x and k >= 2, x[n+1] descends to x[n] + 1 by [k]-steps. *)
Lemma desc_fs_succ : forall x k n, nf x -> okind x = KLim -> 2 <= k -> desc k (fs x (S n)) (osucc (fs x n)).
Proof.
  induction x as [|a IHa b IHb]; intros k n Hx Hl Hk; [discriminate|].
  destruct b as [|c d].
  - destruct a as [|a1 a2]; [discriminate|].
    destruct (opred (ow a1 a2)) as [a'|] eqn:E.
    + rewrite !(fs_pow_succ _ _ _ E). rewrite orep_S_app. unfold osucc.
      apply desc_app. apply desc_one; [lia | | discriminate].
      apply nf_opow. apply (opred_spec (ow a1 a2)); [eapply nf_head; eassumption | exact E].
    + rewrite !(fs_pow_lim (ow a1 a2) _ ltac:(discriminate) E).
      assert (Ha : nf (ow a1 a2)) by (eapply nf_head; eassumption).
      assert (HaL : okind (ow a1 a2) = KLim) by (apply okind_lim; split; [discriminate | exact E]).
      destruct (fs_nf_lt (ow a1 a2) n Ha ltac:(discriminate)) as [Hg _].
      destruct (fs_nf_lt (ow a1 a2) (S n) Ha ltac:(discriminate)) as [Hg' _].
      set (g := fs (ow a1 a2) n) in *.
      eapply desc_trans; [apply (desc_pow k); [lia | exact Hg' | apply IHa; assumption]|].
      unfold opow. apply desc_step; [discriminate|].
      fold g. rewrite (fs_pow_succ _ g k (opred_osucc g)).
      destruct k as [|[|k]]; [lia | lia|]. cbn [orep].
      change (osucc (ow g oz)) with (ow g one). apply desc_cons.
      apply desc_one; [lia | | discriminate].
      change (nf (orep g (S k) oz)). apply nf_orep0. exact Hg.
  - assert (Hb : ow c d <> oz) by discriminate.
    rewrite !(fs_cons a (ow c d) _ Hb).
    change (osucc (ow a ?t)) with (ow a (osucc t)). apply desc_cons.
    apply IHb; [eapply nf_tail; eassumption | eapply okind_cons_lim; eassumption | exact Hk].
Qed.

Lemma iter_ge_shift : forall (g : nat -> nat), (forall z, 1 <= z -> z < g z) ->
  forall j y, 1 <= y -> g y + j <= Nat.iter (S j) g y.
Proof.
  intros g Hg j. induction j as [|j IH]; intros y Hy; [simpl; lia|].
  specialize (IH y Hy). rewrite Nat.iter_succ.
  assert (Hpos : 1 <= Nat.iter (S j) g y) by (pose proof (Hg y Hy); lia).
  pose proof (Hg _ Hpos). lia.
Qed.

(** f_x(n) + n <= f_x(n+1) for a limit x and n >= 1. *)
Theorem FGH_lim_step : forall x n, nf x -> okind x = KLim -> 1 <= n -> FGH x n + n <= FGH x (S n).
Proof.
  intros x n Hx Hl Hn.
  assert (Hxz : x <> oz) by (intro; subst; discriminate).
  destruct (fs_nf_lt x n Hx Hxz) as [Hfn _].
  destruct (fs_nf_lt x (S n) Hx Hxz) as [Hfn' _].
  rewrite (FGH_lim x n Hx Hl), (FGH_lim x (S n) Hx Hl).
  eapply Nat.le_trans;
    [| apply (FGH_desc_le 2 (fs x (S n)) (osucc (fs x n)) (S n)); [exact Hfn' | apply desc_fs_succ; auto | lia | lia]].
  rewrite FGH_osucc by exact Hfn.
  eapply Nat.le_trans; [| apply iter_ge_shift; [intros z Hz; apply FGH_gt; assumption | lia]].
  pose proof (FGH_mono (fs x n) n (S n) Hfn ltac:(lia)). lia.
Qed.

(** ** Ordinary sum: [ocons a x] = omega^a + x (x in Cantor normal form) *)

Definition ocons (a x : ord) : ord :=
  match x with
  | oz => ow a oz
  | ow b _ => match ocmp a b with Lt => x | _ => ow a x end
  end.

Lemma ocons_ne : forall a x, ocons a x <> oz.
Proof. intros a [|b t]; simpl; [discriminate|]. destruct (ocmp a b); discriminate. Qed.

Lemma nf_ocons : forall a x, nf a -> nf x -> nf (ocons a x).
Proof.
  intros a [|b t] Ha Hx; simpl; [apply nf_one; exact Ha|].
  destruct (ocmp_cases a b) as [[E ->]|[[E _]|[E H]]]; rewrite E.
  - apply nf_cons; [exact Ha | exact Hx | apply ole_refl].
  - exact Hx.
  - apply nf_cons; [exact Ha | exact Hx | right; exact H].
Qed.

Lemma ocons_lt : forall a x1 x2, olt x1 x2 -> olt (ocons a x1) (ocons a x2).
Proof.
  intros a x1 x2 H. destruct x2 as [|b2 t2]; [inversion H|].
  destruct x1 as [|b1 t1].
  - unfold ocons. destruct (ocmp_cases a b2) as [[E _]|[[E Hl]|[E _]]]; rewrite E.
    + apply olt_tail, olt_z.
    + apply olt_head; exact Hl.
    + apply olt_tail, olt_z.
  - assert (Hb : ole b1 b2) by (eapply olt_head_inv; exact H).
    unfold ocons.
    destruct (ocmp_cases a b1) as [[E1 H1]|[[E1 H1]|[E1 H1]]]; rewrite E1;
    destruct (ocmp_cases a b2) as [[E2 H2]|[[E2 H2]|[E2 H2]]]; rewrite E2;
    try (apply olt_tail; exact H); try (apply olt_head; exact H2); try exact H; exfalso;
    first [ rewrite <- H1 in Hb; exact (olt_ole_contra _ _ H2 Hb)
          | rewrite <- H2 in Hb; exact (olt_ole_contra _ _ H1 Hb)
          | exact (olt_ole_contra _ _ (olt_trans _ _ _ H2 H1) Hb) ].
Qed.

Lemma ocons_le : forall a x1 x2, ole x1 x2 -> ole (ocons a x1) (ocons a x2).
Proof. intros a x1 x2 [<-|H]; [left; reflexivity | right; apply ocons_lt; exact H]. Qed.

Lemma olt_self_cons : forall t a, nf (ow a t) -> olt t (ow a t).
Proof.
  induction t as [|c _ s IH]; intros a H; [apply olt_z|].
  pose proof (nf_head_le _ _ H) as Hc. simpl in Hc.
  destruct Hc as [->|Hc]; [| apply olt_head; exact Hc].
  apply olt_tail. apply IH. eapply nf_tail; eassumption.
Qed.

Lemma ole_ocons : forall a y, nf a -> nf y -> ole y (ocons a y).
Proof.
  intros a [|b t] Ha Hy; simpl; [right; apply olt_z|].
  destruct (ocmp_cases a b) as [[E ->]|[[E _]|[E H]]]; rewrite E.
  - right. apply olt_self_cons. apply nf_cons; [exact Ha | exact Hy | apply ole_refl].
  - left; reflexivity.
  - right. apply olt_head. exact H.
Qed.

Lemma ocons_big : forall a y, head_le y a -> ocons a y = ow a y.
Proof.
  intros a [|h t] H; [reflexivity|]. simpl in H. simpl.
  destruct (ocmp_cases a h) as [[E _]|[[E Hl]|[E _]]]; rewrite E; [reflexivity | | reflexivity].
  exfalso. exact (olt_ole_contra _ _ Hl H).
Qed.

Lemma head_le_fs : forall b t n, nf (ow b t) -> head_le (fs (ow b t) n) b.
Proof.
  intros b t n H. destruct (fs_nf_lt (ow b t) n H ltac:(discriminate)) as [_ Hlt].
  destruct (fs (ow b t) n) as [|b' t'] eqn:E; [exact I|]. simpl. eapply olt_head_inv; exact Hlt.
Qed.

Lemma ocons_fs : forall a x n, nf a -> nf x -> x <> oz -> ole (fs (ocons a x) n) (ocons a (fs x n)).
Proof.
  intros a [|b t] n Ha Hx Hne; [congruence|].
  destruct (fs_nf_lt (ow b t) n Hx Hne) as [Hf _].
  pose proof (head_le_fs b t n Hx) as Hh.
  unfold ocons at 1. destruct (ocmp_cases a b) as [[E E']|[[E H]|[E H]]]; rewrite E.
  - subst. rewrite (fs_cons b (ow b t) n Hne), ocons_big by exact Hh. apply ole_refl.
  - apply ole_ocons; assumption.
  - rewrite (fs_cons a (ow b t) n Hne), ocons_big; [apply ole_refl|].
    eapply head_le_mono; [exact Hh | right; exact H].
Qed.

Lemma ocons_lim : forall a x, okind x = KLim -> okind (ocons a x) = KLim.
Proof.
  intros a [|b t] H; [discriminate|]. unfold ocons.
  destruct (ocmp a b); try exact H;
  (apply okind_lim; split; [discriminate|]; rewrite opred_cons by discriminate;
   apply okind_lim in H as [_ H]; rewrite H; reflexivity).
Qed.

Lemma ocons_succ : forall a x, ocons a (osucc x) = osucc (ocons a x).
Proof.
  intros a [|b t].
  - simpl. destruct a; reflexivity.
  - unfold osucc. simpl. destruct (ocmp a b); reflexivity.
Qed.

Lemma ocons_orep : forall g j, ocons g (orep g j oz) = orep g (S j) oz.
Proof. intros g [|j]; [reflexivity|]. simpl. rewrite ocmp_refl. reflexivity. Qed.

(** ** Hydras *)

(** A node is the list of its children (tape order); a hydra is the list of the root's children. *)
Inductive tree : Set := node : list tree -> tree.
Definition leaf : tree := node [].

Section TreeInd.
  Variable P : tree -> Prop.
  Hypothesis Hn : forall cs, Forall P cs -> P (node cs).
  Fixpoint tree_ind' (t : tree) : P t :=
    match t with
    | node cs => Hn cs ((fix go (cs : list tree) : Forall P cs :=
                          match cs with
                          | [] => Forall_nil P
                          | c :: cs' => Forall_cons c (tree_ind' c) (go cs')
                          end) cs)
    end.
End TreeInd.

(** Ordinal of a node: the ordinary sum omega^o(c1) + ... + omega^o(ck) in tape order. *)
Fixpoint otree (t : tree) : ord :=
  match t with node cs => fold_right (fun c acc => ocons (otree c) acc) oz cs end.

Definition Phi (L : list tree) (z : ord) : ord := fold_right (fun c acc => ocons (otree c) acc) z L.
Definition olist (L : list tree) : ord := Phi L oz.

Lemma otree_node : forall cs, otree (node cs) = olist cs.
Proof. reflexivity. Qed.

Lemma Phi_cons : forall c L z, Phi (c :: L) z = ocons (otree c) (Phi L z).
Proof. reflexivity. Qed.

Lemma Phi_app : forall L1 L2 z, Phi (L1 ++ L2) z = Phi L1 (Phi L2 z).
Proof. intros. unfold Phi. apply fold_right_app. Qed.

Lemma olist_app : forall L1 L2, olist (L1 ++ L2) = Phi L1 (olist L2).
Proof. intros. apply Phi_app. Qed.

Lemma olist_single : forall cs, olist [node cs] = opow (olist cs).
Proof. reflexivity. Qed.

Lemma nf_Phi_gen : forall L z, Forall (fun c => nf (otree c)) L -> nf z -> nf (Phi L z).
Proof.
  induction L as [|c L IH]; intros z HL Hz; [exact Hz|]. inversion HL; subst.
  rewrite Phi_cons. apply nf_ocons; [assumption | apply IH; assumption].
Qed.

Lemma nf_otree : forall t, nf (otree t).
Proof.
  apply tree_ind'. intros cs H. rewrite otree_node. apply nf_Phi_gen; [exact H | apply nf_z].
Qed.

Lemma nf_Phi : forall L z, nf z -> nf (Phi L z).
Proof. intros L z Hz. apply nf_Phi_gen; [apply Forall_forall; intros; apply nf_otree | exact Hz]. Qed.

Lemma nf_olist : forall L, nf (olist L).
Proof. intros. apply nf_Phi, nf_z. Qed.

Lemma Phi_lt : forall L z1 z2, olt z1 z2 -> olt (Phi L z1) (Phi L z2).
Proof. induction L as [|c L IH]; intros; [assumption | rewrite !Phi_cons; apply ocons_lt; auto]. Qed.

Lemma Phi_le : forall L z1 z2, ole z1 z2 -> ole (Phi L z1) (Phi L z2).
Proof. intros L z1 z2 [<-|H]; [left; reflexivity | right; apply Phi_lt; exact H]. Qed.

Lemma Phi_ne : forall L z, z <> oz -> Phi L z <> oz.
Proof. intros [|c L] z H; [exact H | apply ocons_ne]. Qed.

Lemma Phi_fs : forall L z n, nf z -> okind z = KLim ->
  ole (fs (Phi L z) n) (Phi L (fs z n)) /\ okind (Phi L z) = KLim.
Proof.
  induction L as [|c L IH]; intros z n Hz Hl; [split; [apply ole_refl | exact Hl]|].
  assert (Hzne : z <> oz) by (intro; subst; discriminate).
  destruct (IH z n Hz Hl) as [H1 H2]. rewrite !Phi_cons. split; [| apply ocons_lim; exact H2].
  eapply ole_trans; [apply ocons_fs; [apply nf_otree | apply nf_Phi; exact Hz | apply Phi_ne; exact Hzne]|].
  apply ocons_le. exact H1.
Qed.

Lemma Phi_succ : forall L z, Phi L (osucc z) = osucc (Phi L z).
Proof. induction L as [|c L IH]; intros; [reflexivity | rewrite !Phi_cons, IH; apply ocons_succ]. Qed.

Lemma olist_leaf_snoc : forall L, olist (L ++ [leaf]) = osucc (olist L).
Proof. intros. rewrite olist_app. change (olist [leaf]) with (osucc oz). apply Phi_succ. Qed.

Lemma olist_repeat : forall t n, olist (repeat t n) = orep (otree t) n oz.
Proof.
  intros t n. induction n as [|n IH]; [reflexivity|].
  cbn [repeat]. unfold olist. rewrite Phi_cons. fold (olist (repeat t n)). rewrite IH. apply ocons_orep.
Qed.

(** ** Spines: the rightmost path *)

(** [plug [L0; ...; Lk-1] X]: the root has children L0 ++ [N1], N_i has children L_i ++ [N_(i+1)],
    and the deepest node N_k of the path has children X.  A nonempty hydra is [plug sp []] for a
    nonempty spine sp (its rightmost head is N_k = leaf). *)
Fixpoint plug (sp : list (list tree)) (X : list tree) : list tree :=
  match sp with [] => X | L :: sp' => L ++ [node (plug sp' X)] end.

Lemma plug_app : forall sp1 sp2 X, plug (sp1 ++ sp2) X = plug sp1 (plug sp2 X).
Proof. induction sp1 as [|L sp1 IH]; intros; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Fixpoint Psi (sp : list (list tree)) (z : ord) : ord :=
  match sp with [] => z | L :: sp' => Phi L (opow (Psi sp' z)) end.

Lemma olist_plug : forall sp X, olist (plug sp X) = Psi sp (olist X).
Proof.
  induction sp as [|L sp IH]; intros X; [reflexivity|]. simpl plug.
  rewrite olist_app, olist_single, IH. reflexivity.
Qed.

Lemma olist_plug_ne : forall sp X, sp <> [] -> olist (plug sp X) <> oz.
Proof.
  intros [|L sp] X H; [congruence|]. simpl plug. rewrite olist_app, olist_single.
  apply Phi_ne. discriminate.
Qed.

Lemma spine_snoc : forall t L, exists sp, sp <> [] /\ L ++ [t] = plug sp [].
Proof.
  apply (tree_ind' (fun t => forall L, exists sp, sp <> [] /\ L ++ [t] = plug sp [])).
  intros ds H L. destruct ds as [|t' ds' _] using rev_ind.
  - exists [L]. split; [discriminate | reflexivity].
  - apply Forall_app in H as [_ H]. inversion H as [|? ? Ht _]; subst.
    destruct (Ht ds') as [sp' [_ E]].
    exists (L :: sp'). split; [discriminate|]. simpl. rewrite <- E. reflexivity.
Qed.

Lemma spine_exists : forall hs, hs <> [] -> exists sp, sp <> [] /\ hs = plug sp [].
Proof.
  intros hs H. destruct hs as [|t L _] using rev_ind; [congruence|]. apply spine_snoc.
Qed.

(** ** One round moves the ordinal into [x[n], x) *)

Definition gstep (n : nat) (x y : ord) : Prop := olt y x /\ ole (fs x n) y.

Lemma gstep_Phi : forall L n z1 z2, nf z1 -> okind z1 = KLim -> gstep n z1 z2 ->
  gstep n (Phi L z1) (Phi L z2) /\ okind (Phi L z1) = KLim.
Proof.
  intros L n z1 z2 Hz Hl [H1 H2]. destruct (Phi_fs L z1 n Hz Hl) as [H3 H4].
  split; [split|]; [apply Phi_lt; exact H1 | | exact H4].
  eapply ole_trans; [exact H3 | apply Phi_le; exact H2].
Qed.

Lemma gstep_pow : forall n z1 z2, okind z1 = KLim -> gstep n z1 z2 ->
  gstep n (opow z1) (opow z2) /\ okind (opow z1) = KLim.
Proof.
  intros n z1 z2 Hl [H1 H2]. apply okind_lim in Hl as [Hne Hp].
  split; [split|].
  - apply olt_head. exact H1.
  - unfold opow. rewrite (fs_pow_lim z1 n Hne Hp). apply ole_pow. exact H2.
  - apply okind_pow_lim. exact Hne.
Qed.

Lemma nf_Psi : forall sp z, nf z -> nf (Psi sp z).
Proof. induction sp as [|L sp IH]; intros z Hz; [exact Hz | simpl; apply nf_Phi, nf_opow, IH, Hz]. Qed.

Lemma gstep_Psi : forall sp n z1 z2, nf z1 -> okind z1 = KLim -> gstep n z1 z2 ->
  gstep n (Psi sp z1) (Psi sp z2) /\ okind (Psi sp z1) = KLim.
Proof.
  induction sp as [|L sp IH]; intros n z1 z2 Hz Hl Hg; [split; assumption|].
  destruct (IH n z1 z2 Hz Hl Hg) as [Hg1 Hl1].
  destruct (gstep_pow n _ _ Hl1 Hg1) as [Hg2 Hl2].
  simpl. apply gstep_Phi; [apply nf_opow, nf_Psi, Hz | exact Hl2 | exact Hg2].
Qed.

(** The rightmost head (a child of p = node (L' ++ [leaf])) is removed and p's parent gets n
    copies of the shortened p in place of p. *)
Theorem chop_ord : forall sp0 L L' n,
  okind (olist (plug sp0 (L ++ [node (L' ++ [leaf])]))) = KLim /\
  gstep n (olist (plug sp0 (L ++ [node (L' ++ [leaf])]))) (olist (plug sp0 (L ++ repeat (node L') n))).
Proof.
  intros sp0 L L' n. rewrite !olist_plug, !olist_app, olist_single, olist_leaf_snoc, olist_repeat, otree_node.
  set (g := olist L').
  assert (Hg : nf g) by apply nf_olist.
  assert (Hb : gstep n (opow (osucc g)) (orep g n oz) /\ okind (opow (osucc g)) = KLim).
  { split; [split|].
    - destruct n as [|n]; [apply olt_z | apply olt_head, olt_osucc].
    - unfold opow. rewrite (fs_pow_succ _ g n (opred_osucc g)). apply ole_refl.
    - apply okind_pow_lim. unfold osucc. apply oapp_ne. discriminate. }
  destruct Hb as [Hb1 Hb2].
  destruct (gstep_Phi L n _ _ (nf_opow _ (nf_osucc _ Hg)) Hb2 Hb1) as [H1 H2].
  destruct (gstep_Psi sp0 n _ _ (nf_Phi _ _ (nf_opow _ (nf_osucc _ Hg))) H2 H1) as [H3 H4].
  split; assumption.
Qed.

(** ** Height bound: [hb h t] iff t has height < h (a leaf has height 0) *)

Fixpoint hb (h : nat) (t : tree) : Prop :=
  match h with 0 => False | S h' => match t with node cs => Forall (hb h') cs end end.

Lemma hb_mono : forall h t, hb h t -> forall h', h <= h' -> hb h' t.
Proof.
  induction h as [|h IH]; intros [cs] H h' Hle; [destruct H|].
  destruct h' as [|h']; [lia|]. simpl in *.
  eapply Forall_impl; [| exact H]. intros c Hc. apply (IH c Hc). lia.
Qed.

Lemma hb_plug : forall sp h X, Forall (hb h) (plug sp X) -> Forall (hb h) X.
Proof.
  induction sp as [|L sp IH]; intros h X H; [exact H|]. simpl in H.
  apply Forall_app in H as [_ H]. inversion H as [|? ? Hn _]; subst.
  destruct h as [|h]; [destruct Hn|]. simpl in Hn. apply IH in Hn.
  eapply Forall_impl; [| exact Hn]. intros c Hc. apply (hb_mono h); [exact Hc | lia].
Qed.

Lemma hb_plug_repl : forall sp h X Y, (forall h', Forall (hb h') X -> Forall (hb h') Y) ->
  Forall (hb h) (plug sp X) -> Forall (hb h) (plug sp Y).
Proof.
  induction sp as [|L sp IH]; intros h X Y HXY H; [apply HXY; exact H|]. simpl in *.
  apply Forall_app in H as [HL H]. inversion H as [|? ? Hn _]; subst.
  apply Forall_app. split; [exact HL|]. constructor; [|constructor].
  destruct h as [|h]; [destruct Hn|]. simpl in *. eapply IH; eassumption.
Qed.

Lemma Forall_repeat : forall {A} (P : A -> Prop) x n, P x -> Forall P (repeat x n).
Proof. intros A P x n H. induction n; constructor; assumption. Qed.

Lemma hb_chop : forall h L L' n, Forall (hb h) (L ++ [node (L' ++ [leaf])]) -> Forall (hb h) (L ++ repeat (node L') n).
Proof.
  intros h L L' n H. apply Forall_app in H as [HL H]. inversion H as [|? ? Hn _]; subst.
  apply Forall_app. split; [exact HL|]. apply Forall_repeat.
  destruct h as [|h]; [destruct Hn|]. simpl in *. apply Forall_app in Hn as [Hn _]. exact Hn.
Qed.

Lemma hb_parent : forall sp0 h L L', Forall (hb (S h)) (plug sp0 (L ++ [node (L' ++ [leaf])])) -> Forall (hb h) L'.
Proof.
  intros sp0 h L L' H. apply hb_plug in H. apply Forall_app in H as [_ H].
  inversion H as [|? ? Hn _]; subst. simpl in Hn. apply Forall_app in Hn as [Hn _]. exact Hn.
Qed.
