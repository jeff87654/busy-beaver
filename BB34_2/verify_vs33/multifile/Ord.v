(** * Ordinals below epsilon_0 and the fast-growing hierarchy (BB29 / BB31 / BB33 hydra machines)

    Ordinal notation: hereditary Cantor normal form with unit coefficients,
      [ow a b]  =  omega^a + b,        [oz] = 0,
    so  omega^a1 + omega^a2 + ... + omega^ak  is  [ow a1 (ow a2 (... (ow ak oz)))],
    normal ([nf]) when a1 >= a2 >= ... >= ak and every ai is normal.  On normal terms the
    lexicographic order [olt] is the ordinal order, and it is well founded ([wf_ltn]).

    Fundamental sequences [fs x n] (standard Wainer/Cantor-normal-form convention):
      (b + omega^(g+1))[n] = b + omega^g * n,   (b + omega^l)[n] = b + omega^(l[n])  (l limit),
      and, for convenience, (b + 1)[n] = b  (successors), 0[n] = 0.
    Fast-growing hierarchy, as a relation [fgh x n m]  ("f_x(n) = m"):
      f_0(n) = n+1,   f_(b+1)(n) = f_b^n(n),   f_l(n) = f_(l[n])(n)  (l limit).
    It is deterministic ([fgh_det]) and total on normal terms ([fgh_total]); [FGH x n] is the
    resulting function (meaningful for [nf x]; 0 otherwise).  Everything is axiom-free. *)

From Coq Require Import Arith Lia.
Set Default Goal Selector "!".

(** ** Terms, order, normal form *)

Inductive ord : Set :=
| oz : ord
| ow : ord -> ord -> ord.

Inductive olt : ord -> ord -> Prop :=
| olt_z : forall a b, olt oz (ow a b)
| olt_head : forall a b c d, olt a c -> olt (ow a b) (ow c d)
| olt_tail : forall a b d, olt b d -> olt (ow a b) (ow a d).

Definition ole (x y : ord) : Prop := x = y \/ olt x y.

Inductive nf : ord -> Prop :=
| nf_z : nf oz
| nf_one : forall a, nf a -> nf (ow a oz)
| nf_cons : forall a c d, nf a -> nf (ow c d) -> ole c a -> nf (ow a (ow c d)).

#[export] Hint Constructors olt nf : ord.

Lemma olt_irrefl : forall x, ~ olt x x.
Proof.
  induction x as [|a IHa b IHb]; intro H; inversion H; subst; auto.
Qed.

Lemma olt_trans : forall x y z, olt x y -> olt y z -> olt x z.
Proof.
  induction x as [|a IHa b IHb]; intros y z H1 H2.
  - inversion H2; subst; [inversion H1 | |]; apply olt_z.
  - inversion H1; subst; inversion H2; subst.
    + apply olt_head; eauto.
    + apply olt_head; assumption.
    + apply olt_head; assumption.
    + apply olt_tail; eauto.
Qed.

Lemma olt_asym : forall x y, olt x y -> ~ olt y x.
Proof. intros x y H1 H2. exact (olt_irrefl x (olt_trans _ _ _ H1 H2)). Qed.

Lemma olt_oz : forall x, ~ olt x oz.
Proof. intros x H. inversion H. Qed.

Lemma ole_refl : forall x, ole x x.
Proof. left. reflexivity. Qed.

Lemma ole_oz : forall x, ole oz x.
Proof. destruct x; [left; reflexivity | right; apply olt_z]. Qed.

Lemma ole_trans : forall x y z, ole x y -> ole y z -> ole x z.
Proof. unfold ole. intros x y z [<-|H1] [<-|H2]; auto. right. eapply olt_trans; eauto. Qed.

Lemma olt_ole_trans : forall x y z, olt x y -> ole y z -> olt x z.
Proof. intros x y z H [<-|H']; [assumption | eapply olt_trans; eauto]. Qed.

Lemma ole_olt_trans : forall x y z, ole x y -> olt y z -> olt x z.
Proof. intros x y z [<-|H] H'; [assumption | eapply olt_trans; eauto]. Qed.

Lemma olt_ole : forall x y, olt x y -> ole x y.
Proof. right. assumption. Qed.

Lemma ole_antisym : forall x y, ole x y -> ole y x -> x = y.
Proof.
  intros x y H1 H2. destruct H1 as [E|H1]; [exact E|]. destruct H2 as [E|H2]; [symmetry; exact E|].
  exfalso. exact (olt_asym _ _ H1 H2).
Qed.

Lemma nf_head : forall a b, nf (ow a b) -> nf a.
Proof. intros a b H. inversion H; assumption. Qed.

Lemma nf_tail : forall a b, nf (ow a b) -> nf b.
Proof. intros a b H. inversion H; subst; auto with ord. Qed.

(** [head_le x a]: the leading exponent of [x] is at most [a] (so [ow a x] is normal when both are). *)
Definition head_le (x a : ord) : Prop :=
  match x with oz => True | ow h _ => ole h a end.

Lemma nf_head_le : forall a b, nf (ow a b) -> head_le b a.
Proof. intros a b H. inversion H; subst; simpl; auto. Qed.

Lemma nf_ow : forall a x, nf a -> nf x -> head_le x a -> nf (ow a x).
Proof. intros a [|c d] Ha Hx Hle; simpl in Hle; auto with ord. Qed.

Lemma head_le_lt : forall z c d a, olt z (ow c d) -> ole c a -> head_le z a.
Proof.
  intros z c d a H Hca. inversion H; subst; simpl; auto.
  apply olt_ole. eapply olt_ole_trans; eauto.
Qed.

Lemma head_le_mono : forall x a b, head_le x a -> ole a b -> head_le x b.
Proof. intros [|h t] a b H Hab; simpl in *; [exact I | eapply ole_trans; eauto]. Qed.

Lemma head_le_oz : forall a, head_le oz a.
Proof. intros. exact I. Qed.

(** ** Well-foundedness of [<] on normal terms *)

Definition ltn (x y : ord) : Prop := nf x /\ nf y /\ olt x y.

Lemma acc_oz : Acc ltn oz.
Proof. constructor. intros y (_ & _ & H). inversion H. Qed.

Lemma acc_below : forall a, Acc ltn a -> nf a ->
  forall x, nf x -> head_le x a -> Acc ltn x.
Proof.
  intros a Ha. induction Ha as [a _ IHa]. intros Hna.
  assert (Hcons : forall t, Acc ltn t -> nf (ow a t) -> Acc ltn (ow a t)).
  { intros t Ht. induction Ht as [t _ IHt]. intros Hnt.
    constructor. intros z (Hnz & _ & Hlt).
    inversion Hlt; subst.
    - apply acc_oz.
    - eapply IHa; [| eapply nf_head; eauto | exact Hnz | simpl; apply ole_refl].
      split; [eapply nf_head; eauto | split; assumption].
    - apply IHt; [| assumption].
      split; [eapply nf_tail; eauto | split; [eapply nf_tail; eauto | assumption]]. }
  intro x. induction x as [|h _ t IHt]; intros Hx Hle.
  - apply acc_oz.
  - simpl in Hle. destruct Hle as [-> | Hlt].
    + apply Hcons; [| exact Hx].
      apply IHt; [eapply nf_tail; eauto | apply nf_head_le; exact Hx].
    + eapply IHa; [| eapply nf_head; eauto | exact Hx | simpl; apply ole_refl].
      split; [eapply nf_head; eauto | split; assumption].
Qed.

Theorem nf_acc : forall x, nf x -> Acc ltn x.
Proof.
  intros [|a b] Hx; [apply acc_oz|].
  revert b Hx. induction a as [|a1 IHa1 a2 IHa2]; intros b Hx.
  - eapply acc_below; [apply acc_oz | apply nf_z | exact Hx | simpl; apply ole_refl].
  - eapply acc_below; [| eapply nf_head; eauto | exact Hx | simpl; apply ole_refl].
    apply IHa1. eapply nf_head; eauto.
Qed.

Theorem wf_ltn : well_founded ltn.
Proof. intro x. constructor. intros y (Hy & _). apply nf_acc. exact Hy. Qed.

(** ** Decidable comparison and normality *)

Fixpoint ocmp (x y : ord) : comparison :=
  match x, y with
  | oz, oz => Eq
  | oz, ow _ _ => Lt
  | ow _ _, oz => Gt
  | ow a b, ow c d => match ocmp a c with Eq => ocmp b d | r => r end
  end.

Lemma ocmp_spec : forall x y, CompareSpec (x = y) (olt x y) (olt y x) (ocmp x y).
Proof.
  induction x as [|a IHa b IHb]; destruct y as [|c d]; simpl; try (constructor; auto with ord; fail).
  destruct (IHa c) as [<-|H|H].
  - destruct (IHb d) as [<-|H'|H']; constructor; auto with ord.
  - constructor. auto with ord.
  - constructor. auto with ord.
Qed.

Lemma ocmp_Eq : forall x y, ocmp x y = Eq -> x = y.
Proof. intros x y H. pose proof (ocmp_spec x y) as S. rewrite H in S. inversion S. assumption. Qed.

Lemma ocmp_Lt : forall x y, ocmp x y = Lt -> olt x y.
Proof. intros x y H. pose proof (ocmp_spec x y) as S. rewrite H in S. inversion S. assumption. Qed.

Lemma ocmp_Gt : forall x y, ocmp x y = Gt -> olt y x.
Proof. intros x y H. pose proof (ocmp_spec x y) as S. rewrite H in S. inversion S. assumption. Qed.

Lemma ole_ocmp : forall x y, ole x y -> ocmp x y <> Gt.
Proof.
  intros x y Hle H. apply ocmp_Gt in H. destruct Hle as [<-|H'].
  - exact (olt_irrefl _ H).
  - exact (olt_asym _ _ H H').
Qed.

Lemma olt_dec : forall x y, {olt x y} + {~ olt x y}.
Proof.
  intros x y. destruct (ocmp x y) eqn:E.
  - right. apply ocmp_Eq in E. subst. apply olt_irrefl.
  - left. apply ocmp_Lt. exact E.
  - right. apply ocmp_Gt in E. intro H. exact (olt_asym _ _ H E).
Defined.

Fixpoint nfb (x : ord) : bool :=
  match x with
  | oz => true
  | ow a b =>
      nfb a && nfb b &&
      match b with
      | oz => true
      | ow c _ => match ocmp c a with Gt => false | _ => true end
      end
  end.

Lemma nfb_nf : forall x, nfb x = true <-> nf x.
Proof.
  induction x as [|a IHa b IHb]; simpl.
  - split; auto with ord.
  - split.
    + intro H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
      destruct b as [|c d].
      * apply nf_one. apply IHa. exact H1.
      * apply nf_cons; [apply IHa; exact H1 | apply IHb; exact H2 |].
        destruct (ocmp c a) eqn:E; try discriminate.
        -- left. apply ocmp_Eq. exact E.
        -- right. apply ocmp_Lt. exact E.
    + intro H. inversion H; subst.
      * rewrite (proj2 IHa H1). reflexivity.
      * rewrite (proj2 IHa H2), (proj2 IHb H3). simpl.
        destruct (ocmp c a) eqn:E; auto. exfalso. exact (ole_ocmp _ _ H4 E).
Qed.

Lemma nf_by_nfb : forall x, nfb x = true -> nf x.
Proof. intros. apply nfb_nf. assumption. Qed.

(** Prove [nf t] for a closed term [t] by computation. *)
Ltac prove_nf := apply nf_by_nfb; vm_compute; reflexivity.

Definition nf_dec (x : ord) : {nf x} + {~ nf x}.
Proof.
  destruct (nfb x) eqn:E.
  - left. apply nfb_nf. exact E.
  - right. intro H. apply nfb_nf in H. congruence.
Defined.

(** ** Arithmetic building blocks *)

(** [oapp x y]: concatenation of the term lists, i.e. the ordinal sum [x + y] when the last
    exponent of [x] is >= the leading exponent of [y] (always the case in our uses). *)
Fixpoint oapp (x y : ord) : ord :=
  match x with oz => y | ow a b => ow a (oapp b y) end.

Definition one : ord := ow oz oz.                     (* 1 = omega^0 *)
Definition opow (a : ord) : ord := ow a oz.           (* omega^a *)
Fixpoint orep (a : ord) (k : nat) (y : ord) : ord :=  (* omega^a * k + y *)
  match k with O => y | S k' => ow a (orep a k' y) end.
Definition ofin (k : nat) : ord := orep oz k oz.      (* the finite ordinal k *)
Definition omega : ord := opow one.
Definition osucc (x : ord) : ord := oapp x one.       (* x + 1 *)
Fixpoint tower (k : nat) : ord :=                     (* omega^^k: tower 0 = 1, tower 1 = omega, ... *)
  match k with O => one | S k' => opow (tower k') end.
Fixpoint powtower (j : nat) (y : ord) : ord :=        (* omega^(omega^(...^y)), j omegas *)
  match j with O => y | S j' => opow (powtower j' y) end.

Lemma ofin_1 : ofin 1 = one.
Proof. reflexivity. Qed.

Lemma tower_1 : tower 1 = omega.
Proof. reflexivity. Qed.

Lemma oapp_oz_r : forall x, oapp x oz = x.
Proof. induction x as [|a _ b IHb]; simpl; [reflexivity | rewrite IHb; reflexivity]. Qed.

Lemma oapp_assoc : forall x y z, oapp (oapp x y) z = oapp x (oapp y z).
Proof. induction x as [|a _ b IHb]; intros; simpl; [reflexivity | rewrite IHb; reflexivity]. Qed.

Lemma oapp_ne : forall x y, y <> oz -> oapp x y <> oz.
Proof. intros [|a b] y H; simpl; [exact H | discriminate]. Qed.

Lemma orep_S_app : forall a n, orep a (S n) oz = oapp (orep a n oz) (opow a).
Proof. intros a n. induction n as [|n IH]; [reflexivity|]. simpl in *. rewrite <- IH. reflexivity. Qed.

Lemma orep_app : forall a n y, orep a n y = oapp (orep a n oz) y.
Proof. intros a n y. induction n as [|n IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma ofin_S : forall k, ofin (S k) = osucc (ofin k).
Proof. intro k. unfold ofin, osucc. apply orep_S_app. Qed.

Lemma tower_ne : forall k, tower k <> oz.
Proof. destruct k; discriminate. Qed.

Lemma powtower_ofin_1 : forall j, powtower j one = tower j.
Proof. induction j as [|j IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** normality of the building blocks *)

Lemma nf_one' : nf one.
Proof. apply nf_one. apply nf_z. Qed.

Lemma nf_opow : forall a, nf a -> nf (opow a).
Proof. intros. apply nf_one. assumption. Qed.

Lemma head_le_orep : forall a k y, head_le y a -> head_le (orep a k y) a.
Proof. intros a [|k] y H; simpl; [exact H | apply ole_refl]. Qed.

Lemma nf_orep : forall a k y, nf a -> nf y -> head_le y a -> nf (orep a k y).
Proof.
  intros a k y Ha Hy Hle. induction k as [|k IH]; simpl; [exact Hy|].
  apply nf_ow; [exact Ha | exact IH | apply head_le_orep; exact Hle].
Qed.

Lemma nf_orep0 : forall a k, nf a -> nf (orep a k oz).
Proof. intros. apply nf_orep; auto with ord. exact I. Qed.

Lemma nf_ofin : forall k, nf (ofin k).
Proof. intros. apply nf_orep0. apply nf_z. Qed.

Lemma nf_omega : nf omega.
Proof. apply nf_opow. apply nf_one'. Qed.

Lemma nf_tower : forall k, nf (tower k).
Proof. induction k; simpl; [apply nf_one' | apply nf_opow; assumption]. Qed.

Lemma nf_powtower : forall j y, nf y -> nf (powtower j y).
Proof. induction j; simpl; intros; [assumption | apply nf_opow; auto]. Qed.

(** [all_ge y x]: the leading exponent of [y] is <= every exponent of [x]. *)
Fixpoint all_ge (y x : ord) : Prop :=
  match x with oz => True | ow a b => head_le y a /\ all_ge y b end.

Lemma nf_oapp : forall x y, nf x -> nf y -> all_ge y x -> nf (oapp x y).
Proof.
  induction x as [|a _ b IHb]; intros y Hx Hy Hg; simpl in *; [exact Hy|].
  destruct Hg as [Hya Hyb].
  apply nf_ow; [eapply nf_head; eauto | apply IHb; [eapply nf_tail; eauto | exact Hy | exact Hyb] |].
  destruct b as [|c d]; simpl; [exact Hya|]. apply nf_head_le in Hx. exact Hx.
Qed.

Lemma nf_app_r : forall x y, nf (oapp x y) -> nf y.
Proof. induction x as [|a _ b IHb]; intros y H; simpl in *; [exact H | apply IHb; eapply nf_tail; eauto]. Qed.

Lemma all_ge_one : forall x, all_ge one x.
Proof. induction x as [|a _ b IHb]; simpl; [exact I | split; [apply ole_oz | exact IHb]]. Qed.

Lemma nf_osucc : forall x, nf x -> nf (osucc x).
Proof. intros. apply nf_oapp; [assumption | apply nf_one' | apply all_ge_one]. Qed.

(** ** Predecessor, kind, fundamental sequences *)

Fixpoint opred (x : ord) : option ord :=
  match x with
  | oz => None
  | ow a oz => match a with oz => Some oz | ow _ _ => None end
  | ow a b => option_map (ow a) (opred b)
  end.

Inductive kind : Set := KZero | KSucc (b : ord) | KLim.

Definition okind (x : ord) : kind :=
  match x with
  | oz => KZero
  | ow _ _ => match opred x with Some b => KSucc b | None => KLim end
  end.

Fixpoint fs (x : ord) (n : nat) : ord :=
  match x with
  | oz => oz
  | ow a oz =>
      match a with
      | oz => oz                                   (* 1[n] = 0 *)
      | ow _ _ =>
          match opred a with
          | Some a' => orep a' n oz                (* omega^(a'+1)[n] = omega^a' * n *)
          | None => ow (fs a n) oz                 (* omega^l[n] = omega^(l[n]) *)
          end
      end
  | ow a b => ow a (fs b n)                        (* (omega^a + b)[n] = omega^a + b[n] *)
  end.

Lemma opred_cons : forall a b, b <> oz -> opred (ow a b) = option_map (ow a) (opred b).
Proof. intros a [|c d] H; [congruence | reflexivity]. Qed.

Lemma opred_pow : forall a, a <> oz -> opred (ow a oz) = None.
Proof. intros [|c d] H; [congruence | reflexivity]. Qed.

Lemma fs_cons : forall a b n, b <> oz -> fs (ow a b) n = ow a (fs b n).
Proof. intros a [|c d] n H; [congruence | reflexivity]. Qed.

Lemma fs_one : forall n, fs one n = oz.
Proof. reflexivity. Qed.

Lemma fs_pow_succ : forall a a' n, opred a = Some a' -> fs (ow a oz) n = orep a' n oz.
Proof.
  intros [|c d] a' n H; [discriminate|].
  change (fs (ow (ow c d) oz) n) with
    (match opred (ow c d) with Some a' => orep a' n oz | None => ow (fs (ow c d) n) oz end).
  rewrite H. reflexivity.
Qed.

Lemma fs_pow_lim : forall a n, a <> oz -> opred a = None -> fs (ow a oz) n = ow (fs a n) oz.
Proof.
  intros [|c d] n H1 H2; [congruence|].
  change (fs (ow (ow c d) oz) n) with
    (match opred (ow c d) with Some a' => orep a' n oz | None => ow (fs (ow c d) n) oz end).
  rewrite H2. reflexivity.
Qed.

Lemma opred_osucc : forall x, opred (osucc x) = Some x.
Proof.
  unfold osucc. induction x as [|a _ b IHb]; [reflexivity|]. simpl oapp.
  rewrite opred_cons by (apply oapp_ne; discriminate). rewrite IHb. reflexivity.
Qed.

Lemma opred_inv : forall x y, opred x = Some y -> x = osucc y.
Proof.
  unfold osucc. induction x as [|a _ b IHb]; intros y H; [discriminate|].
  destruct b as [|c d].
  - destruct a; [|discriminate]. inversion H. reflexivity.
  - rewrite opred_cons in H by discriminate. destruct (opred (ow c d)) as [p|] eqn:E; [|discriminate].
    inversion H; subst. simpl. rewrite <- (IHb p eq_refl). reflexivity.
Qed.

Lemma fs_succ : forall x y n, opred x = Some y -> fs x n = y.
Proof.
  induction x as [|a _ b IHb]; intros y n H; [discriminate|].
  destruct b as [|c d].
  - destruct a; [|discriminate]. inversion H. reflexivity.
  - rewrite opred_cons in H by discriminate. destruct (opred (ow c d)) as [p|] eqn:E; [|discriminate].
    inversion H; subst. rewrite fs_cons by discriminate. rewrite (IHb p n eq_refl). reflexivity.
Qed.

Lemma fs_osucc : forall x n, fs (osucc x) n = x.
Proof. intros. apply fs_succ. apply opred_osucc. Qed.

Lemma okind_zero : forall x, okind x = KZero -> x = oz.
Proof. intros [|a b] H; [reflexivity|]. unfold okind in H. destruct (opred (ow a b)); discriminate. Qed.

Lemma okind_succ : forall x b, okind x = KSucc b <-> opred x = Some b.
Proof.
  intros [|a c] b; [split; discriminate|]. unfold okind.
  destruct (opred (ow a c)); split; intro H; congruence.
Qed.

Lemma okind_lim : forall x, okind x = KLim <-> x <> oz /\ opred x = None.
Proof.
  intros [|a c]; [split; [discriminate | intros [H _]; congruence]|]. unfold okind.
  destruct (opred (ow a c)); split; intro H; try discriminate; try (destruct H; discriminate); auto.
  split; [discriminate | reflexivity].
Qed.

Lemma okind_osucc : forall x, okind (osucc x) = KSucc x.
Proof. intro. apply okind_succ. apply opred_osucc. Qed.

Lemma okind_cons_lim : forall a b, b <> oz -> okind (ow a b) = KLim -> okind b = KLim.
Proof.
  intros a b Hb H. apply okind_lim in H as [_ H]. rewrite opred_cons in H by exact Hb.
  apply okind_lim. split; [exact Hb|]. destruct (opred b); [discriminate | reflexivity].
Qed.

Lemma okind_pow_lim : forall a, a <> oz -> okind (ow a oz) = KLim.
Proof. intros a H. apply okind_lim. split; [discriminate | apply opred_pow; exact H]. Qed.

(** Fundamental sequences decrease and preserve normality. *)
Lemma fs_nf_lt : forall x n, nf x -> x <> oz -> nf (fs x n) /\ olt (fs x n) x.
Proof.
  induction x as [|a IHa b IHb]; intros n Hx Hne; [congruence|].
  destruct b as [|c d].
  - destruct a as [|a1 a2].
    + simpl. split; [apply nf_z | apply olt_z].
    + destruct (opred (ow a1 a2)) as [a'|] eqn:E.
      * rewrite (fs_pow_succ _ _ _ E).
        assert (Ha : nf (ow a1 a2)) by (eapply nf_head; eauto).
        destruct (IHa 0 Ha ltac:(discriminate)) as [Ha' Hlt]. rewrite (fs_succ _ _ 0 E) in Ha', Hlt.
        split; [apply nf_orep0; exact Ha'|].
        destruct n; simpl; [apply olt_z | apply olt_head; exact Hlt].
      * rewrite (fs_pow_lim (ow a1 a2) n ltac:(discriminate) E).
        destruct (IHa n (nf_head _ _ Hx) ltac:(discriminate)) as [Ha' Hlt].
        split; [apply nf_one; exact Ha' | apply olt_head; exact Hlt].
  - rewrite fs_cons by discriminate.
    destruct (IHb n (nf_tail _ _ Hx) ltac:(discriminate)) as [Hb' Hlt].
    split; [| apply olt_tail; exact Hlt].
    apply nf_ow; [eapply nf_head; eauto | exact Hb' |].
    eapply head_le_lt; [exact Hlt | exact (nf_head_le _ _ Hx)].
Qed.

Lemma opred_spec : forall x y, nf x -> opred x = Some y -> nf y /\ olt y x.
Proof.
  intros x y Hx H. rewrite <- (fs_succ x y 0 H). apply fs_nf_lt; [exact Hx|].
  intro E. subst. discriminate.
Qed.

Lemma fs_ltn : forall x n, nf x -> x <> oz -> ltn (fs x n) x.
Proof. intros x n Hx Hne. destruct (fs_nf_lt x n Hx Hne). repeat split; assumption. Qed.

(** Fundamental sequences of sums, in textbook form. *)
Lemma fs_app : forall b y n, y <> oz -> fs (oapp b y) n = oapp b (fs y n).
Proof.
  induction b as [|a _ b IHb]; intros y n H; [reflexivity|].
  change (oapp (ow a b) ?z) with (ow a (oapp b z)).
  rewrite fs_cons by (apply oapp_ne; exact H). rewrite IHb by exact H. reflexivity.
Qed.

Lemma opred_app : forall b y, y <> oz -> opred (oapp b y) = option_map (oapp b) (opred y).
Proof.
  induction b as [|a _ b IHb]; intros y H.
  - change (oapp oz y) with y. destruct (opred y); reflexivity.
  - change (oapp (ow a b) ?z) with (ow a (oapp b z)). rewrite opred_cons by (apply oapp_ne; exact H). rewrite IHb by exact H.
    destruct (opred y); reflexivity.
Qed.

Lemma fs_app_succ_exp : forall b g n, fs (oapp b (opow (osucc g))) n = oapp b (orep g n oz).
Proof.
  intros. rewrite fs_app by discriminate. unfold opow. rewrite (fs_pow_succ _ g n (opred_osucc g)).
  reflexivity.
Qed.

Lemma fs_app_lim_exp : forall b g n, okind g = KLim -> fs (oapp b (opow g)) n = oapp b (opow (fs g n)).
Proof.
  intros b g n H. apply okind_lim in H as [H1 H2].
  rewrite fs_app by discriminate. unfold opow. rewrite fs_pow_lim by assumption. reflexivity.
Qed.

Lemma okind_app_pow : forall b g, g <> oz -> okind (oapp b (opow g)) = KLim.
Proof.
  intros b g H. apply okind_lim. split; [apply oapp_ne; discriminate|].
  rewrite opred_app by discriminate. unfold opow. rewrite opred_pow by exact H. reflexivity.
Qed.

Lemma fs_omega : forall n, fs omega n = ofin n.
Proof. reflexivity. Qed.

Lemma opred_tower_S : forall j, opred (tower (S j)) = None.
Proof. intros [|j]; reflexivity. Qed.

Lemma okind_tower_S : forall j, okind (tower (S j)) = KLim.
Proof. intro j. apply okind_lim. split; [discriminate | apply opred_tower_S]. Qed.

Lemma fs_tower_SS : forall j n, fs (tower (S (S j))) n = opow (fs (tower (S j)) n).
Proof.
  intros j n. change (tower (S (S j))) with (ow (tower (S j)) oz).
  rewrite fs_pow_lim; [reflexivity | discriminate | apply opred_tower_S].
Qed.

(** omega^^(j+1) [n] = omega^(omega^(...^n)) with j omegas: e.g. (omega^omega)[n] = omega^n. *)
Lemma fs_tower : forall j n, fs (tower (S j)) n = powtower j (ofin n).
Proof.
  induction j as [|j IH]; intro n; [reflexivity|].
  rewrite fs_tower_SS, IH. reflexivity.
Qed.

(** ** Descent along fundamental sequences with a fixed index k *)

Inductive desc (k : nat) : ord -> ord -> Prop :=
| desc_refl : forall x, desc k x x
| desc_step : forall x y, x <> oz -> desc k (fs x k) y -> desc k x y.

Lemma desc_trans : forall k x y z, desc k x y -> desc k y z -> desc k x z.
Proof. intros k x y z H. induction H; intros; [assumption | apply desc_step; auto]. Qed.

Lemma desc_nf : forall k x y, desc k x y -> nf x -> nf y /\ ole y x.
Proof.
  intros k x y H. induction H as [x|x y Hne _ IH]; intros Hx; [split; [exact Hx | apply ole_refl]|].
  destruct (fs_nf_lt x k Hx Hne) as [H1 H2]. destruct (IH H1) as [H3 H4].
  split; [exact H3 | right; eapply ole_olt_trans; eauto].
Qed.

Lemma desc_cons : forall k a x y, desc k x y -> desc k (ow a x) (ow a y).
Proof.
  intros k a x y H. induction H as [x|x y Hne _ IH]; [apply desc_refl|].
  apply desc_step; [discriminate|]. rewrite fs_cons by exact Hne. exact IH.
Qed.

Lemma desc_app : forall k b x y, desc k x y -> desc k (oapp b x) (oapp b y).
Proof. induction b as [|a _ b IHb]; intros; simpl; [assumption | apply desc_cons; auto]. Qed.

Lemma desc_zero : forall k x, nf x -> desc k x oz.
Proof.
  intros k x. induction x as [x IH] using (well_founded_ind wf_ltn). intros Hx.
  destruct x as [|a b]; [apply desc_refl|].
  apply desc_step; [discriminate|]. apply IH; [apply fs_ltn; [exact Hx | discriminate]|].
  apply fs_nf_lt; [exact Hx | discriminate].
Qed.

(** [b + y] descends to [b]. *)
Lemma desc_app_drop : forall k b y, nf y -> desc k (oapp b y) b.
Proof. intros k b y Hy. rewrite <- (oapp_oz_r b) at 2. apply desc_app. apply desc_zero. exact Hy. Qed.

Lemma desc_pow : forall k x y, 1 <= k -> nf x -> desc k x y -> desc k (opow x) (opow y).
Proof.
  intros k x y Hk Hx H. induction H as [x|x y Hne D IH]; [apply desc_refl|].
  destruct (fs_nf_lt x k Hx Hne) as [Hfs _].
  apply desc_trans with (y := opow (fs x k)); [| apply IH; exact Hfs].
  apply desc_step; [discriminate|]. unfold opow.
  destruct (opred x) as [x'|] eqn:E.
  - rewrite (fs_pow_succ _ _ _ E), (fs_succ _ _ _ E).
    destruct k as [|k]; [lia|]. simpl orep.
    change (ow x' (orep x' k oz)) with (oapp (opow x') (orep x' k oz)).
    apply desc_app_drop. apply nf_orep0. rewrite (fs_succ _ _ _ E) in Hfs. exact Hfs.
  - rewrite (fs_pow_lim _ _ Hne E). apply desc_refl.
Qed.

(** The key "Bachmann" property: for a limit x and k >= 1, x[n+1] descends to x[n] by [k]-steps. *)
Lemma fs_chain1 : forall x k n, nf x -> okind x = KLim -> 1 <= k -> desc k (fs x (S n)) (fs x n).
Proof.
  induction x as [|a IHa b IHb]; intros k n Hx K Hk; [discriminate|].
  destruct b as [|c d].
  - destruct a as [|a1 a2]; [discriminate|].
    destruct (opred (ow a1 a2)) as [a'|] eqn:E.
    + rewrite !(fs_pow_succ _ _ _ E). rewrite orep_S_app. apply desc_app_drop.
      apply nf_opow. apply (opred_spec _ _ (nf_head _ _ Hx) E).
    + rewrite !(fun n => fs_pow_lim (ow a1 a2) n ltac:(discriminate) E). apply desc_pow; [exact Hk | |].
      * apply fs_nf_lt; [eapply nf_head; eauto | discriminate].
      * apply IHa; [eapply nf_head; eauto | apply okind_lim; split; [discriminate | exact E] | exact Hk].
  - rewrite !fs_cons by discriminate. apply desc_cons.
    apply IHb; [eapply nf_tail; eauto | eapply okind_cons_lim; [discriminate | exact K] | exact Hk].
Qed.

Lemma fs_chain : forall x k j m, nf x -> okind x = KLim -> 1 <= k -> j <= m -> desc k (fs x m) (fs x j).
Proof.
  intros x k j m Hx K Hk Hjm. induction m as [|m IH].
  - assert (j = 0) by lia. subst. apply desc_refl.
  - destruct (Nat.eq_dec j (S m)) as [->|Hne]; [apply desc_refl|].
    eapply desc_trans; [apply fs_chain1; assumption | apply IH; lia].
Qed.

(** ** The fast-growing hierarchy as a relation *)

(** [fgh x n m]: f_x(n) = m.  [fghi b k y m]: (f_b)^k(y) = m. *)
Inductive fgh : ord -> nat -> nat -> Prop :=
| fgh_zero : forall n, fgh oz n (S n)
| fgh_succ : forall x b n m, okind x = KSucc b -> fghi b n n m -> fgh x n m
| fgh_lim : forall x n m, okind x = KLim -> fgh (fs x n) n m -> fgh x n m
with fghi : ord -> nat -> nat -> nat -> Prop :=
| fghi_O : forall b y, fghi b 0 y y
| fghi_S : forall b k y y1 m, fgh b y y1 -> fghi b k y1 m -> fghi b (S k) y m.

Scheme fgh_mut := Induction for fgh Sort Prop
  with fghi_mut := Induction for fghi Sort Prop.
Combined Scheme fgh_fghi_mut from fgh_mut, fghi_mut.

Lemma fgh_fghi_det :
  (forall x n m, fgh x n m -> forall m', fgh x n m' -> m = m') /\
  (forall b k y m, fghi b k y m -> forall m', fghi b k y m' -> m = m').
Proof.
  apply fgh_fghi_mut.
  - intros n m' H. inversion H; subst; [reflexivity | discriminate | discriminate].
  - intros x b n m K Hi IH m' H. inversion H; subst.
    + discriminate.
    + rewrite K in H0. inversion H0; subst. apply IH. assumption.
    + congruence.
  - intros x n m K Hf IH m' H. inversion H; subst.
    + discriminate.
    + congruence.
    + apply IH. assumption.
  - intros b y m' H. inversion H. reflexivity.
  - intros b k y y1 m Hf IHf Hi IHi m' H. inversion H; subst.
    match goal with Hf' : fgh b y ?z |- _ => apply IHf in Hf'; subst end.
    apply IHi. assumption.
Qed.

Theorem fgh_det : forall x n m m', fgh x n m -> fgh x n m' -> m = m'.
Proof. intros. eapply (proj1 fgh_fghi_det); eauto. Qed.

Theorem fgh_total : forall x, nf x -> forall n, {m | fgh x n m}.
Proof.
  refine (well_founded_induction_type wf_ltn (fun x => nf x -> forall n, {m | fgh x n m}) _).
  intros x IH Hx n.
  destruct (okind x) as [|b|] eqn:K.
  - exists (S n). rewrite (okind_zero x K). apply fgh_zero.
  - assert (Hb : ltn b x).
    { apply okind_succ in K. destruct (opred_spec x b Hx K). repeat split; assumption. }
    assert (It : forall k y, {m | fghi b k y m}).
    { induction k as [|k IHk]; intro y.
      - exists y. apply fghi_O.
      - destruct (IH b Hb (proj1 Hb) y) as [y1 H1]. destruct (IHk y1) as [m Hm].
        exists m. eapply fghi_S; eassumption. }
    destruct (It n n) as [m Hm]. exists m. eapply fgh_succ; eassumption.
  - assert (Hl : ltn (fs x n) x).
    { apply fs_ltn; [exact Hx | apply okind_lim in K; apply K]. }
    destruct (IH _ Hl (proj1 Hl) n) as [m Hm]. exists m. apply fgh_lim; assumption.
Defined.

(** [FGH x n] = f_x(n) for normal [x] (and 0 for non-normal terms, which are never used). *)
Definition FGH (x : ord) (n : nat) : nat :=
  match nf_dec x with
  | left H => proj1_sig (fgh_total x H n)
  | right _ => 0
  end.

Lemma FGH_spec : forall x n, nf x -> fgh x n (FGH x n).
Proof. intros x n Hx. unfold FGH. destruct (nf_dec x) as [H|H]; [apply proj2_sig | contradiction]. Qed.

Lemma FGH_unique : forall x n m, nf x -> fgh x n m -> FGH x n = m.
Proof. intros. eapply fgh_det; [apply FGH_spec |]; eassumption. Qed.

Global Opaque FGH.

Lemma iter_ext : forall (f g : nat -> nat) k y, (forall z, f z = g z) -> Nat.iter k f y = Nat.iter k g y.
Proof. intros f g k y H. induction k as [|k IH]; simpl; [reflexivity | rewrite IH; apply H]. Qed.

Lemma fghi_iter : forall b k y, nf b -> fghi b k y (Nat.iter k (FGH b) y).
Proof.
  intros b k. induction k as [|k IH]; intros y Hb; [apply fghi_O|].
  rewrite Nat.iter_succ_r. eapply fghi_S; [apply FGH_spec; exact Hb | apply IH; exact Hb].
Qed.

(** ** Defining equations of [FGH] *)

Lemma FGH_zero : forall n, FGH oz n = S n.
Proof. intros. apply FGH_unique; [apply nf_z | apply fgh_zero]. Qed.

Lemma FGH_succ : forall x b n, nf x -> okind x = KSucc b -> FGH x n = Nat.iter n (FGH b) n.
Proof.
  intros x b n Hx K. assert (Hb : nf b) by (apply okind_succ in K; apply (opred_spec x b Hx K)).
  apply FGH_unique; [exact Hx|]. eapply fgh_succ; [exact K | apply fghi_iter; exact Hb].
Qed.

Lemma FGH_lim : forall x n, nf x -> okind x = KLim -> FGH x n = FGH (fs x n) n.
Proof.
  intros x n Hx K. apply FGH_unique; [exact Hx|]. apply fgh_lim; [exact K|].
  apply FGH_spec. apply fs_nf_lt; [exact Hx | apply okind_lim in K; apply K].
Qed.

(** f_(b+1)(n) = f_b^n(n) *)
Lemma FGH_osucc : forall b n, nf b -> FGH (osucc b) n = Nat.iter n (FGH b) n.
Proof. intros. apply FGH_succ; [apply nf_osucc; assumption | apply okind_osucc]. Qed.

(** f_(b + omega^(g+1))(n) = f_(b + omega^g * n)(n) *)
Lemma FGH_app_succ_exp : forall b g n, nf (oapp b (opow (osucc g))) ->
  FGH (oapp b (opow (osucc g))) n = FGH (oapp b (orep g n oz)) n.
Proof.
  intros b g n H. rewrite FGH_lim by (assumption || (apply okind_app_pow; apply oapp_ne; discriminate)).
  rewrite fs_app_succ_exp. reflexivity.
Qed.

(** f_(b + omega^l)(n) = f_(b + omega^(l[n]))(n) for limit l *)
Lemma FGH_app_lim_exp : forall b g n, nf (oapp b (opow g)) -> okind g = KLim ->
  FGH (oapp b (opow g)) n = FGH (oapp b (opow (fs g n))) n.
Proof.
  intros b g n H K. assert (g <> oz) by (apply okind_lim in K; apply K).
  rewrite FGH_lim by (assumption || (apply okind_app_pow; assumption)).
  rewrite fs_app_lim_exp by exact K. reflexivity.
Qed.

(** ** Growth properties: inflation, monotonicity, descent *)

Lemma iter_ge : forall (g : nat -> nat), (forall n, n <= g n) -> forall k x, x <= Nat.iter k g x.
Proof. intros g H k x. induction k as [|k IH]; simpl; [lia | specialize (H (Nat.iter k g x)); lia]. Qed.

Lemma iter_mono_arg : forall (g : nat -> nat), (forall a b, a <= b -> g a <= g b) ->
  forall k x x', x <= x' -> Nat.iter k g x <= Nat.iter k g x'.
Proof. intros g H k. induction k as [|k IH]; intros x x' Hx; simpl; [exact Hx | apply H; auto]. Qed.

Lemma iter_mono : forall (g : nat -> nat), (forall a b, a <= b -> g a <= g b) -> (forall a, a <= g a) ->
  forall k k' x x', k <= k' -> x <= x' -> Nat.iter k g x <= Nat.iter k' g x'.
Proof.
  intros g Hm Hg k k' x x' Hk Hx.
  replace k' with (k + (k' - k)) by lia. rewrite Nat.iter_add.
  apply iter_mono_arg; [exact Hm|]. eapply Nat.le_trans; [exact Hx | apply iter_ge; exact Hg].
Qed.

Lemma iter_succ_ge : forall (g : nat -> nat), (forall n, n <= g n) -> forall k x, 1 <= k -> g x <= Nat.iter k g x.
Proof.
  intros g H [|k] x Hk; [lia|]. rewrite Nat.iter_succ_r. apply iter_ge. exact H.
Qed.

Definition goodF (x : ord) : Prop :=
  (forall n, n <= FGH x n) /\
  (forall n, 1 <= n -> n < FGH x n) /\
  (forall n n', n <= n' -> FGH x n <= FGH x n') /\
  (forall k m, 1 <= m -> k <= m -> FGH (fs x k) m <= FGH x m).

Theorem FGH_good : forall x, nf x -> goodF x.
Proof.
  intro x. induction x as [x IH] using (well_founded_ind wf_ltn). intros Hx.
  assert (Chain : forall y z m, desc 1 y z -> nf y -> olt y x -> 1 <= m -> FGH z m <= FGH y m).
  { intros y z m D. induction D as [y|y z Hne D IHD]; intros Hy Hyx Hm; [lia|].
    destruct (fs_nf_lt y 1 Hy Hne) as [Hn Hl].
    destruct (IH y (conj Hy (conj Hx Hyx)) Hy) as (_ & _ & _ & G).
    specialize (G 1 m Hm Hm). specialize (IHD Hn (olt_trans _ _ _ Hl Hyx) Hm). lia. }
  destruct (okind x) as [|b|] eqn:K.
  - apply okind_zero in K. subst x.
    repeat split; intros; cbn [fs]; rewrite ?FGH_zero; lia.
  - assert (Hp := K). apply okind_succ in Hp. destruct (opred_spec x b Hx Hp) as [Hb Hbx].
    destruct (IH b (conj Hb (conj Hx Hbx)) Hb) as (G1 & G2 & G3 & G4).
    assert (E : forall n, FGH x n = Nat.iter n (FGH b) n) by (intro; apply FGH_succ; assumption).
    repeat split.
    + intro n. rewrite E. apply iter_ge. exact G1.
    + intros n Hn. rewrite E. eapply Nat.lt_le_trans; [apply G2; exact Hn | apply iter_succ_ge; assumption].
    + intros n n' Hnn. rewrite !E. apply iter_mono; assumption.
    + intros k m Hm Hk. rewrite (fs_succ _ _ _ Hp), E. apply iter_succ_ge; assumption.
  - assert (Hne : x <> oz) by (apply okind_lim in K; apply K).
    assert (S1 : forall n, nf (fs x n) /\ olt (fs x n) x) by (intro; apply fs_nf_lt; assumption).
    assert (Gn : forall n, goodF (fs x n)).
    { intro n. destruct (S1 n) as [H1 H2]. apply IH; [repeat split; assumption | exact H1]. }
    assert (E : forall n, FGH x n = FGH (fs x n) n) by (intro; apply FGH_lim; assumption).
    assert (G4 : forall k m, 1 <= m -> k <= m -> FGH (fs x k) m <= FGH x m).
    { intros k m Hm Hk. rewrite E. apply Chain; [apply fs_chain; auto | apply S1 | apply S1 | exact Hm]. }
    repeat split.
    + intro n. rewrite E. apply (Gn n).
    + intros n Hn. rewrite E. apply (Gn n). exact Hn.
    + assert (Step : forall n, FGH x n <= FGH x (S n)).
      { intro n. rewrite (E n). destruct (Gn n) as (_ & _ & M & _).
        eapply Nat.le_trans; [apply (M n (S n)); lia|].
        apply G4; lia. }
      intros n n' Hnn. induction Hnn as [|n' _ IHn]; [lia | eapply Nat.le_trans; [exact IHn | apply Step]].
    + exact G4.
Qed.

(** f_x(n) >= n *)
Theorem FGH_ge : forall x n, nf x -> n <= FGH x n.
Proof. intros x n Hx. apply (FGH_good x Hx). Qed.

(** f_x(n) >= n + 1 for n >= 1 (note f_(b+1)(0) = 0, so n >= 1 is needed) *)
Theorem FGH_gt : forall x n, nf x -> 1 <= n -> n < FGH x n.
Proof. intros x n Hx. apply (FGH_good x Hx). Qed.

(** monotonicity in n *)
Theorem FGH_mono : forall x n n', nf x -> n <= n' -> FGH x n <= FGH x n'.
Proof. intros x n n' Hx. apply (FGH_good x Hx). Qed.

(** one fundamental-sequence step does not increase f at arguments m >= max(1, k) *)
Theorem FGH_fs_le : forall x k m, nf x -> 1 <= m -> k <= m -> FGH (fs x k) m <= FGH x m.
Proof. intros x k m Hx. apply (FGH_good x Hx). Qed.

(** if y is reached from x by [k]-steps of fundamental sequences, f_y(m) <= f_x(m) for m >= max(1, k) *)
Theorem FGH_desc_le : forall k x y m, nf x -> desc k x y -> 1 <= m -> k <= m -> FGH y m <= FGH x m.
Proof.
  intros k x y m Hx D. induction D as [x|x y Hne _ IH]; intros Hm Hk; [lia|].
  destruct (fs_nf_lt x k Hx Hne) as [H1 _].
  eapply Nat.le_trans; [apply IH; assumption | apply FGH_fs_le; assumption].
Qed.

(** f_b(m) <= f_(b + y)(m) for m >= 1 *)
Theorem FGH_app_ge : forall b y m, nf (oapp b y) -> 1 <= m -> FGH b m <= FGH (oapp b y) m.
Proof.
  intros b y m H Hm. apply (FGH_desc_le 0); [exact H | apply desc_app_drop; eapply nf_app_r; eauto | exact Hm | lia].
Qed.

(** f_b(m) <= f_(b+1)(m) for m >= 1 *)
Theorem FGH_le_osucc : forall b m, nf b -> 1 <= m -> FGH b m <= FGH (osucc b) m.
Proof. intros. apply FGH_app_ge; [apply nf_osucc |]; assumption. Qed.

(** f_(x[k])(m) <= f_(x[j])(m) for a limit x, k <= j, m >= 1 *)
Theorem FGH_fs_mono : forall x j k m, nf x -> okind x = KLim -> k <= j -> 1 <= m ->
  FGH (fs x k) m <= FGH (fs x j) m.
Proof.
  intros x j k m Hx K Hkj Hm. apply (FGH_desc_le 1); [| apply fs_chain; auto | exact Hm | exact Hm].
  apply fs_nf_lt; [exact Hx | apply okind_lim in K; apply K].
Qed.

(** ** Finite levels and the first limits *)

(** the plain iterative definition (identical to [fgh] in bb8_list/proofs/BB10_n1_fgh.v) *)
Fixpoint fin_fgh (k n : nat) : nat :=
  match k with
  | O => S n
  | S k' => Nat.iter n (fin_fgh k') n
  end.

Theorem FGH_fin : forall k n, FGH (ofin k) n = fin_fgh k n.
Proof.
  induction k as [|k IH]; intro n; [apply FGH_zero|].
  rewrite ofin_S, FGH_osucc by apply nf_ofin. simpl. apply iter_ext. exact IH.
Qed.

(** f_omega(n) = f_n(n) *)
Theorem FGH_omega : forall n, FGH omega n = fin_fgh n n.
Proof.
  intro n. rewrite FGH_lim; [| apply nf_omega | reflexivity]. rewrite fs_omega. apply FGH_fin.
Qed.

(** f_(omega^^(j+1))(n) = f_(omega^(omega^(...^n)))(n)  (j omegas) *)
Theorem FGH_tower : forall j n, FGH (tower (S j)) n = FGH (powtower j (ofin n)) n.
Proof. intros j n. rewrite FGH_lim; [| apply nf_tower | apply okind_tower_S]. rewrite fs_tower. reflexivity. Qed.

(** f_(omega^omega)(n) = f_(omega^n)(n);  f_(omega^omega^omega)(n) = f_(omega^omega^n)(n); ... *)
Corollary FGH_w_w : forall n, FGH (tower 2) n = FGH (opow (ofin n)) n.
Proof. intro. apply FGH_tower. Qed.

Corollary FGH_w_w_w : forall n, FGH (tower 3) n = FGH (opow (opow (ofin n))) n.
Proof. intro. apply FGH_tower. Qed.

Corollary FGH_w_w_w_w : forall n, FGH (tower 4) n = FGH (opow (opow (opow (ofin n)))) n.
Proof. intro. apply FGH_tower. Qed.

Example FGH_w_w_3 : FGH (tower 2) 3 = FGH (opow (ofin 3)) 3.
Proof. apply FGH_w_w. Qed.

(** sanity checks *)
Example FGH_1_5 : FGH (ofin 1) 5 = 10.
Proof. rewrite FGH_fin. reflexivity. Qed.

Example FGH_2_3 : FGH (ofin 2) 3 = 24.
Proof. rewrite FGH_fin. reflexivity. Qed.

Example FGH_omega_2 : FGH omega 2 = 8.
Proof. rewrite FGH_omega. reflexivity. Qed.

Example FGH_w_w_1 : FGH (tower 2) 1 = 2.
Proof. rewrite FGH_w_w. change (opow (ofin 1)) with omega. rewrite FGH_omega. reflexivity. Qed.

Example FGH_tower4_1 : FGH (tower 4) 1 = 2.
Proof.
  rewrite FGH_tower, ofin_1, powtower_ofin_1.   (* = f_(omega^^3)(1) *)
  rewrite FGH_tower, ofin_1, powtower_ofin_1.   (* = f_(omega^^2)(1) *)
  exact FGH_w_w_1.
Qed.
