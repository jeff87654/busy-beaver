(** * AC_tup: from one tagged witness-closure to Tarski–Vaught pieces.

    A piece (K, b) of Z_refl ([pcs]) has $0 = the witness and $1..$K = the context.  We code a context
    tau 0, ..., tau (K-1) as the nested ordered pair q = (tau 0, (tau 1, ... (tau (K-1), ∅))) ([TupF], the
    shape of Z_cl's EnvF with OP0 instead of Ext0), and the i-th piece of a list ps by the numeral tag i:
    [cps ps] ($0 = witness v, $1 = parameter q) is the disjunction over i of
        ∃p ∃t (t = i ∧ q = (t, p) ∧ [dec K b](v, p)),
    where [dec K b](v, p) decodes p as a K-tuple and evaluates b.

    [ps_PH]: if X is closed under ordered pairs, contains ∅ and the numerals < |ps|, and is witness-closed
    for [cps ps] ([WClos]), then every piece of ps is witness-closed in X in Z_refl's sense ([PH]). *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From ZF Require Std_setrec.
From RegCon Require Import Rel.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_refl.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** q = (sg 0, (sg 1, ... (sg (n-1), ∅))) *)
Fixpoint TupF (n : nat) (sg : nat -> term) (q : term) : form :=
  match n with
  | 0 => Emp0 q
  | S n => ∃ (TupF n (fun k => (sg (S k))`[↑]) $0 ∧ OP0 (sg 0)`[↑] $0 q`[↑])
  end.

Fixpoint exK (K : nat) (phi : form) : form :=
  match K with
  | 0 => phi
  | S K => ∃ (exK K phi)
  end.

(** decoded piece: $0 = witness v, $1 = coded context p *)
Definition dec (K : nat) (b : form) : form :=
  exK K (TupF K (fun k => $k) $(S K) ∧ b[$K .: (fun k => $k)]).

(** the i-th tagged piece: $0 = v, $1 = q *)
Definition pc (i K : nat) (b : form) : form :=
  ∃ (∃ (NumF i $0 ∧ OP0 $0 $1 $3 ∧ (dec K b)[$2 .: $1 .: (fun k => $(k + 4))])).

Fixpoint cps_from (i : nat) (ps : list (nat * form)) : form :=
  match ps with
  | [] => ⊥
  | (K, b) :: ps' => pc i K b ∨ cps_from (S i) ps'
  end.
Definition cps (ps : list (nat * form)) : form := cps_from 0 ps.

(** X is witness-closed for c ($0 = witness, $1 = parameter) *)
Definition WClos (c : form) (X : term) : form :=
  ∀ ($0 ∈' X`[↑] → (∃ (Lform ∧ Std_setrec.Rel2 c $0 $1)) → ∃ ($0 ∈' X`[↑]`[↑] ∧ Std_setrec.Rel2 c $0 $1)).
(** X is closed under ordered pairs *)
Definition OPClos (X : term) : form :=
  ∀ ($0 ∈' X`[↑] → ∀ ($0 ∈' X`[↑]`[↑] → ∀ (OP0 $2 $1 $0 → $0 ∈' X`[↑]`[↑]`[↑]))).
#[global] Arguments WClos : simpl never.
#[global] Arguments OPClos : simpl never.

#[local] Arguments Lform : simpl never.
#[local] Arguments TupF : simpl never.
#[local] Arguments dec : simpl never.
#[local] Arguments pc : simpl never.
#[local] Arguments cps_from : simpl never.
#[local] Hint Rewrite Lform_up : fsub.
#[local] Hint Rewrite NumF_subst : fsub.

Lemma WClos_subst c X sg : (WClos c X)[sg] = WClos c X`[sg].
Proof. psubst WClos. Qed.
Lemma OPClos_subst X sg : (OPClos X)[sg] = OPClos X`[sg].
Proof. psubst OPClos. Qed.
#[global] Hint Rewrite WClos_subst OPClos_subst : fsub.

(** ** Tuples *)
Lemma TupF_0 sg q : TupF 0 sg q = Emp0 q. Proof. reflexivity. Qed.
Lemma TupF_S n sg q : TupF (S n) sg q = ∃ (TupF n (fun k => (sg (S k))`[↑]) $0 ∧ OP0 (sg 0)`[↑] $0 q`[↑]).
Proof. reflexivity. Qed.

Lemma TupF_ext n : forall sg sg' q, (forall k, k < n -> sg k = sg' k) -> TupF n sg q = TupF n sg' q.
Proof.
  induction n as [|n IH]; intros sg sg' q H; [reflexivity|]. rewrite !TupF_S, (H 0) by lia.
  rewrite (IH (fun k => (sg (S k))`[↑]) (fun k => (sg' (S k))`[↑]) $0); [reflexivity|].
  intros k Hk. cbn. rewrite (H (S k)) by lia. reflexivity.
Qed.

Lemma TupF_subst n : forall sg q tau, (TupF n sg q)[tau] = TupF n (fun k => (sg k)`[tau]) q`[tau].
Proof.
  induction n as [|n IH]; intros sg q tau; [apply Emp0_subst|]. rewrite !TupF_S.
  change ((∃ (TupF n (fun k => (sg (S k))`[↑]) $0 ∧ OP0 (sg 0)`[↑] $0 q`[↑]))[tau])
    with (∃ ((TupF n (fun k => (sg (S k))`[↑]) $0)[up tau] ∧ (OP0 (sg 0)`[↑] $0 q`[↑])[up tau])).
  rewrite IH, OP0_subst. rewrite !up_term.
  rewrite (TupF_ext n (fun k => (sg (S k))`[↑]`[up tau]) (fun k => (sg (S k))`[tau]`[↑]))
    by (intros k _; apply up_term).
  reflexivity.
Qed.

Lemma tup_inst K tau q X :
  (TupF K (fun k => (tau k)`[↑]) $0 ∧ $0 ∈' X`[↑])[q..] = (TupF K tau q ∧ q ∈' X).
Proof.
  cbn. rewrite TupF_subst, subst_term_shift. cbn.
  rewrite (TupF_ext K _ tau) by (intros k _; apply subst_term_shift). reflexivity.
Qed.

Lemma tup_E G n sg z psi : G ⊢C TupF (S n) sg z ->
  (forall e, ((TupF n (fun k => sg (S k)) e ∧ OP0 (sg 0) e z) :: G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros H K. rewrite TupF_S in H. apply (ExE_named H). intros e.
  assert (E : (TupF n (fun k => (sg (S k))`[↑]) $0 ∧ OP0 (sg 0)`[↑] $0 z`[↑])[e..] =
              (TupF n (fun k => sg (S k)) e ∧ OP0 (sg 0) e z)).
  { change ((TupF n (fun k => (sg (S k))`[↑]) $0 ∧ OP0 (sg 0)`[↑] $0 z`[↑])[e..]) with
      ((TupF n (fun k => (sg (S k))`[↑]) $0)[e..] ∧ (OP0 (sg 0)`[↑] $0 z`[↑])[e..]).
    rewrite TupF_subst, OP0_subst, !subst_term_shift.
    rewrite (TupF_ext n _ (fun k => sg (S k))) by (intros k _; apply subst_term_shift). reflexivity. }
  rewrite E. apply K.
Qed.
Lemma tup_I G n sg e z : G ⊢C TupF n (fun k => sg (S k)) e -> G ⊢C OP0 (sg 0) e z -> G ⊢C TupF (S n) sg z.
Proof.
  intros H1 H2. rewrite TupF_S. apply (ExI e).
  change ((TupF n (fun k => (sg (S k))`[↑]) $0 ∧ OP0 (sg 0)`[↑] $0 z`[↑])[e..]) with
      ((TupF n (fun k => (sg (S k))`[↑]) $0)[e..] ∧ (OP0 (sg 0)`[↑] $0 z`[↑])[e..]).
  rewrite TupF_subst, OP0_subst, !subst_term_shift.
  rewrite (TupF_ext n _ (fun k => sg (S k))) by (intros k _; apply subst_term_shift). apply CI; assumption.
Qed.

Lemma tup_ex K : forall G X tau, incl ZF0base G -> G ⊢C OPClos X -> G ⊢C ∀ (Emp0 $0 → $0 ∈' X`[↑]) ->
  (forall k, k < K -> G ⊢C tau k ∈' X) -> G ⊢C ∃ (TupF K (fun k => (tau k)`[↑]) $0 ∧ $0 ∈' X`[↑]).
Proof.
  induction K as [|K IH]; intros G X tau HG HOP HE Ht.
  - clear Ht. fobtain (emp0_ex HG) as e He. apply (ExI e). rewrite tup_inst, TupF_0.
    fsplit; [exact He|]. finst HE e. exact (IE HE He).
  - pose proof (IH G X (fun k => tau (S k)) HG HOP HE (fun k Hk => Ht (S k) ltac:(lia))) as T.
    pose proof (Ht 0 ltac:(lia)) as Ht0. clear Ht IH.
    apply (ExE_named T). intros e. rewrite tup_inst. ctx_push He. fdestr He He1 He2.
    fobtain (op0_ex HG (incl_nil_l _) (tau 0) e) as q Hq.
    apply (ExI q). rewrite tup_inst. fsplit.
    + exact (tup_I _ K tau e q He1 Hq).
    + unfold OPClos in HOP. finst HOP (tau 0). fmp HOP Ht0. finst HOP e. fmp HOP He2. finst HOP q.
      exact (IE HOP Hq).
Qed.

Lemma tup_inj K : forall G sg sg' q q', incl ZF0base G -> G ⊢C TupF K sg q -> G ⊢C TupF K sg' q' ->
  G ⊢C q ≡' q' -> forall k, k < K -> G ⊢C sg k ≡' sg' k.
Proof.
  induction K as [|K IH]; intros G sg sg' q q' HG H H' E k Hk; [lia|].
  apply (tup_E _ _ _ _ _ H). intros e. ctx_push He. fdestr He He1 He2.
  apply (tup_E _ _ _ _ _ H'). intros e'. ctx_push He'. fdestr He' He1' He2'.
  frew_in E (OP0 (sg' 0)`[↑] e'`[↑] $0) He2'.
  pose proof (op0_inj_g HG _ _ _ _ _ He2 He2') as Hi. fdestr Hi Hi1 Hi2.
  destruct k as [|k]; [exact Hi1|].
  exact (IH _ _ _ _ _ HG He1 He1' Hi2 k ltac:(lia)).
Qed.

(** ** K existentials *)
Lemma exK_S K phi : exK (S K) phi = ∃ (exK K phi). Proof. reflexivity. Qed.

Lemma exK_subst K : forall phi sg, (exK K phi)[sg] = exK K (phi[upn K sg]).
Proof.
  induction K as [|K IH]; intros phi sg.
  - cbn. symmetry. apply subst_ext. intros k. unfold upn. cbn. rewrite Nat.sub_0_r. apply subst_term_var.
  - rewrite exK_S. cbn. rewrite IH. rewrite (subst_ext phi (upn_S K sg)). reflexivity.
Qed.

Lemma exK_I K : forall G phi sg, G ⊢C phi[ext K sg] -> G ⊢C exK K phi.
Proof.
  induction K as [|K IH]; intros G phi sg H.
  - cbn. rewrite subst_id in H; [exact H|]. intros k. unfold ext. cbn. f_equal. lia.
  - rewrite exK_S. apply (ExI (sg K)). rewrite exK_subst. apply (IH _ _ sg).
    rewrite subst_comp. erewrite subst_ext; [exact H|]. intros k. cbn. apply upn_ext; [reflexivity|].
    intros j _. reflexivity.
Qed.

Lemma exK_E K : forall G phi psi, G ⊢C exK K phi ->
  (forall G' sg, incl G G' -> G' ⊢C phi[ext K sg] -> G' ⊢C psi) -> G ⊢C psi.
Proof.
  induction K as [|K IH]; intros G phi psi H Hk.
  - apply (Hk G var (incl_refl G)). rewrite subst_id; [exact H|]. intros k. unfold ext. cbn. f_equal. lia.
  - rewrite exK_S in H. apply (ExE_named H). intros x. rewrite exK_subst.
    assert (H0 : (exK K (phi[upn K (x..)]) :: G) ⊢C exK K (phi[upn K (x..)])) by (apply Ctx; now left).
    apply (IH _ _ _ H0).
    intros G' sg HG' H'. apply (Hk G' (fun k => if k =? K then x else sg k)).
    + intros a Ha. apply HG'. now right.
    + rewrite subst_comp in H'. erewrite subst_ext; [exact H'|]. intros k. cbn. symmetry. apply upn_ext.
      * now rewrite Nat.eqb_refl.
      * intros j Hj. destruct (Nat.eqb_spec j K); [lia|reflexivity].
Qed.

Lemma upn_ext_appf K s sg k : (upn K s k)`[ext K sg] = appf K sg s k.
Proof.
  unfold upn, appf. destruct (Nat.ltb_spec k K).
  - cbn. rewrite ext_lt by lia. reflexivity.
  - rewrite subst_term_comp. apply subst_term_id. intros j. cbn. rewrite ext_ge by lia. f_equal. lia.
Qed.

(** ** Decoded pieces *)
Lemma dec_body K b v p rho sg : fb (S K) b ->
  (TupF K (fun k => $k) $(S K) ∧ b[$K .: (fun k => $k)])[upn K (v .: p .: rho)][ext K sg] =
  (TupF K sg p ∧ b[v .: sg]).
Proof.
  intros Hb. rewrite subst_comp. cbn. f_equal.
  - rewrite TupF_subst. cbn. unfold funcomp. rewrite upn_ext_appf.
    unfold appf at 1. destruct (Nat.ltb_spec (S K) K); [lia|]. replace (S K - K) with 1 by lia. cbn.
    apply TupF_ext. intros k Hk. rewrite upn_ext_appf. apply appf_lt. exact Hk.
  - rewrite subst_comp. apply (subst_ext_fb _ (S K) _ _ Hb). intros [|j] Hj; cbn; unfold funcomp;
      rewrite upn_ext_appf.
    + unfold appf. destruct (Nat.ltb_spec K K); [lia|]. now rewrite Nat.sub_diag.
    + apply appf_lt. lia.
Qed.

Lemma dec_I G K b v p rho sg : fb (S K) b -> G ⊢C TupF K sg p -> G ⊢C b[v .: sg] ->
  G ⊢C (dec K b)[v .: p .: rho].
Proof.
  intros Hb H1 H2. unfold dec. rewrite exK_subst. apply (exK_I K G _ sg).
  rewrite (dec_body K b v p rho sg Hb). apply CI; assumption.
Qed.

Lemma dec_E G K b v p rho psi : fb (S K) b -> G ⊢C (dec K b)[v .: p .: rho] ->
  (forall G' sg, incl G G' -> G' ⊢C TupF K sg p -> G' ⊢C b[v .: sg] -> G' ⊢C psi) -> G ⊢C psi.
Proof.
  intros Hb H Hk. unfold dec in H. rewrite exK_subst in H. apply (exK_E K G _ psi H).
  intros G' sg HG' H'. rewrite (dec_body K b v p rho sg Hb) in H'.
  exact (Hk G' sg HG' (CE1 H') (CE2 H')).
Qed.

(** ** Tagged pieces *)
Definition pcB (i K : nat) (b : form) : form :=
  NumF i $0 ∧ OP0 $0 $1 $3 ∧ (dec K b)[$2 .: $1 .: (fun k => $(k + 4))].
Lemma pc_subst_eq i K b s : (pc i K b)[s] = ∃ (∃ (pcB i K b)[up (up s)]).
Proof. reflexivity. Qed.

Lemma pc_body i K b v q rho t p :
  (pcB i K b)[up (up (v .: q .: rho))][up (p..)][t..] = (NumF i t ∧ OP0 t p q ∧ (dec K b)[v .: p .: rho]).
Proof.
  unfold pcB. rewrite !subst_comp. cbn. rewrite NumF_subst, OP0_subst. cbn. f_equal; [f_equal|].
  - f_equal; [rewrite subst_term_shift; reflexivity|].
    rewrite !subst_term_comp. apply subst_term_id. intros j. reflexivity.
  - rewrite subst_comp. apply subst_ext. intros [|[|k]]; cbn;
      try replace (k + 4) with (S (S (S (S k)))) by lia; cbn; unfold funcomp; cbn;
      rewrite ?subst_term_comp; first [reflexivity | apply subst_term_id; intros; reflexivity].
Qed.

Lemma pc_I G i K b v q rho t p : G ⊢C NumF i t -> G ⊢C OP0 t p q -> G ⊢C (dec K b)[v .: p .: rho] ->
  G ⊢C (pc i K b)[v .: q .: rho].
Proof.
  intros H1 H2 H3. rewrite pc_subst_eq. apply (ExI p).
  change ((∃ (pcB i K b)[up (up (v .: q .: rho))])[p..])
    with (∃ (pcB i K b)[up (up (v .: q .: rho))][up (p..)]).
  apply (ExI t). rewrite pc_body. apply CI; [apply CI|]; assumption.
Qed.

Lemma pc_E G i K b v q rho psi : G ⊢C (pc i K b)[v .: q .: rho] ->
  (forall G' t p, incl G G' -> G' ⊢C NumF i t -> G' ⊢C OP0 t p q -> G' ⊢C (dec K b)[v .: p .: rho] ->
     G' ⊢C psi) -> G ⊢C psi.
Proof.
  intros H Hk. rewrite pc_subst_eq in H. apply (ExE_named H). intros p.
  assert (H1 : (((∃ (pcB i K b)[up (up (v .: q .: rho))])[p..]) :: G) ⊢C
                 ∃ ((pcB i K b)[up (up (v .: q .: rho))][up (p..)])) by (apply Ctx; now left).
  apply (ExE_named H1). intros t. rewrite pc_body.
  assert (H2 : ((NumF i t ∧ OP0 t p q ∧ (dec K b)[v .: p .: rho]) ::
                ((∃ (pcB i K b)[up (up (v .: q .: rho))])[p..]) :: G) ⊢C
                 (NumF i t ∧ OP0 t p q ∧ (dec K b)[v .: p .: rho])) by (apply Ctx; now left).
  apply (Hk _ t p).
  - intros a Ha. now right; right.
  - exact (CE1 (CE1 H2)).
  - exact (CE2 (CE1 H2)).
  - exact (CE2 H2).
Qed.

Lemma cps_from_cons i K b ps : cps_from i ((K, b) :: ps) = pc i K b ∨ cps_from (S i) ps.
Proof. reflexivity. Qed.

Lemma cpsf_I ps : forall i0 n K b G s, nth_error ps n = Some (K, b) ->
  G ⊢C (pc (i0 + n) K b)[s] -> G ⊢C (cps_from i0 ps)[s].
Proof.
  induction ps as [|[K' b'] ps IH]; intros i0 n K b G s Hn H; [destruct n; discriminate|].
  rewrite cps_from_cons. destruct n as [|n].
  - cbn in Hn. inversion Hn; subst. apply DI1. rewrite Nat.add_0_r in H. exact H.
  - apply DI2. apply (IH (S i0) n K b G s Hn). replace (S i0 + n) with (i0 + S n) by lia. exact H.
Qed.

(** what a disjunct of [cps_from i0 ps] says when the tag of the parameter is m *)
Definition decat (ps : list (nat * form)) (i0 m : nat) (v p : term) (rho : nat -> term) : form :=
  if m <? i0 then ⊥ else
  match nth_error ps (m - i0) with Some (K, b) => (dec K b)[v .: p .: rho] | None => ⊥ end.

Lemma cpsf_E ps : forall i0 G m t p0 q v rho, incl ZF0base G -> In ax_reg' G -> In ax_om' G -> incl Ax_cl G ->
  G ⊢C NumF m t -> G ⊢C OP0 t p0 q -> G ⊢C (cps_from i0 ps)[v .: q .: rho] -> G ⊢C decat ps i0 m v p0 rho.
Proof.
  induction ps as [|[K' b'] ps IH]; intros i0 G m t p0 q v rho HG HR HOm HC Ht Hq H.
  - apply Exp. exact H.
  - rewrite cps_from_cons in H. apply (DE H).
    + assert (H1 : ((pc i0 K' b')[v .: q .: rho] :: G) ⊢C (pc i0 K' b')[v .: q .: rho]) by (apply Ctx; now left).
      apply (pc_E _ i0 K' b' v q rho _ H1).
      intros G' t' p HG' Ht' Hq' Hd.
      assert (HGG : incl G G') by (intros a Ha; apply HG'; now right).
      pose proof (incl_tran HG HGG) as HG2. pose proof (HGG _ HR) as HR2. pose proof (HGG _ HOm) as HOm2.
      pose proof (incl_tran HC HGG) as HC2. pose proof (Weak Ht HGG) as Ht2. pose proof (Weak Hq HGG) as Hq2.
      pose proof (op0_inj_g HG2 _ _ _ _ _ Hq' Hq2) as Hi. pose proof (CE1 Hi) as Hi1. pose proof (CE2 Hi) as Hi2.
      destruct (Nat.eq_dec m i0) as [->|Hne].
      * unfold decat. rewrite Nat.ltb_irrefl, Nat.sub_diag. cbn.
        refine (leib_gen _ G' (v .: p .: rho) (v .: p0 .: rho) HG2 _ Hd).
        intros [|[|k]]; cbn; [apply eq_refl'; exact HG2|exact Hi2|apply eq_refl'; exact HG2].
      * apply Exp. exact (num_neq HG2 HR2 HOm2 HC2 i0 m t' t ltac:(lia) Ht' Ht2 Hi1).
    + assert (H2 : ((cps_from (S i0) ps)[v .: q .: rho] :: G) ⊢C (cps_from (S i0) ps)[v .: q .: rho])
        by (apply Ctx; now left).
      pose proof (IH (S i0) _ m t p0 q v rho (incl_cons_r _ _ _ HG) (in_cons_r _ _ _ HR) (in_cons_r _ _ _ HOm)
                    (incl_cons_r _ _ _ HC) (weak_cons _ _ _ Ht) (weak_cons _ _ _ Hq) H2) as D.
      revert D. unfold decat. destruct (Nat.ltb_spec m (S i0)).
      * intros D. apply Exp. exact D.
      * destruct (Nat.ltb_spec m i0); [lia|]. replace (m - i0) with (S (m - S i0)) by lia. cbn [nth_error].
        intros D. exact D.
Qed.

Lemma fb_TupF n : forall sg q N, (forall k, k < n -> idx (sg k) < N) -> idx q < N -> fb N (TupF n sg q).
Proof.
  induction n as [|n IH]; intros sg q N Hs Hq.
  - rewrite TupF_0. replace (Emp0 q) with ((Emp0 $0)[fun _ => q]) by (rewrite Emp0_subst; reflexivity).
    apply fb_inst. intros _. exact Hq.
  - rewrite TupF_S. cbn. split.
    + apply IH; [|cbn; lia]. intros k Hk. rewrite idx_up. specialize (Hs (S k) ltac:(lia)). lia.
    + replace (OP0 (sg 0)`[↑] $0 q`[↑]) with ((OP0 $0 $1 $2)[(sg 0)`[↑] .: $0 .: q`[↑] .: (fun _ => $0)])
        by (rewrite OP0_subst; reflexivity).
      apply fb_inst. intros [|[|[|k]]]; cbn; rewrite ?idx_up; try lia. specialize (Hs 0 ltac:(lia)). lia.
Qed.

Lemma fb_exK K : forall phi N, fb (K + N) phi -> fb N (exK K phi).
Proof.
  induction K as [|K IH]; intros phi N H; [exact H|]. rewrite exK_S. cbn. apply IH.
  replace (K + S N) with (S K + N) by lia. exact H.
Qed.

Lemma fb_dec K b : fb (S K) b -> fb 2 (dec K b).
Proof.
  intros Hb. unfold dec. apply fb_exK. cbn. split.
  - apply fb_TupF; cbn; intros; lia.
  - apply (fb_subst _ (S K)); [exact Hb|]. intros [|k] Hk; cbn; lia.
Qed.

Lemma fb_cps_from ps : (forall K b, In (K, b) ps -> fb (S K) b) -> forall i, fb 2 (cps_from i ps).
Proof.
  induction ps as [|[K b] ps IH]; intros Hps i; [exact I|].
  rewrite cps_from_cons. cbn. split; [|apply IH; intros K' b' Hin; apply Hps; now right].
  unfold pc. cbn. split; [split|].
  - replace (NumF i $0) with ((NumF i $0)[fun _ => $0]) by (rewrite NumF_subst; reflexivity).
    apply fb_inst. intros _. cbn. lia.
  - replace (OP0 $0 $1 $3) with ((OP0 $0 $1 $2)[$0 .: $1 .: $3 .: (fun _ => $3)])
      by (rewrite OP0_subst; reflexivity).
    apply fb_inst. intros [|[|[|k]]]; cbn; lia.
  - apply (fb_subst _ 2); [apply fb_dec; apply Hps; now left|]. intros [|[|k]] Hk; cbn; lia.
Qed.

Lemma fb_cps ps : (forall K b, In (K, b) ps -> fb (S K) b) -> fb 2 (cps ps).
Proof. intros H. exact (fb_cps_from ps H 0). Qed.

(** ** The main lemma *)
Lemma ps_PH {G0 : list form} ps X : (forall K b, In (K, b) ps -> fb (S K) b) ->
  incl ZF0base G0 -> In ax_reg' G0 -> In ax_om' G0 -> incl Ax_L G0 ->
  G0 ⊢C OPClos X -> G0 ⊢C ∀ (Emp0 $0 → $0 ∈' X`[↑]) ->
  (forall i, i < length ps -> G0 ⊢C ∀ (NumF i $0 → $0 ∈' X`[↑])) ->
  G0 ⊢C WClos (cps ps) X ->
  forall K b, In (K, b) ps -> PH G0 X K b.
Proof.
  intros Hfb HG HR HOm HL HOP HE HN HW K b Hin.
  destruct (In_nth_error ps (K, b) Hin) as [i Hi].
  assert (Hil : i < length ps) by (apply nth_error_Some; congruence).
  pose proof (Hfb K b Hin) as Hb. clear Hfb Hin.
  intros G' tau HGG' Htau. unfold Ew.
  pose proof (incl_tran HG HGG') as HG'. pose proof (HGG' _ HR) as HR'. pose proof (HGG' _ HOm) as HOm'.
  pose proof (Ax_L_cl _ (incl_tran HL HGG')) as HC'.
  pose proof (Weak HOP HGG') as HOP'. pose proof (Weak HE HGG') as HE'.
  pose proof (Weak (HN i Hil) HGG') as HN'. pose proof (Weak HW HGG') as HW'.
  clear HG HR HOm HL HOP HE HN HW HGG'.
  pose proof (tup_ex K G' X tau HG' HOP' HE' Htau) as T. clear Htau HE'.
  apply (ExE_named T). intros q0. rewrite tup_inst. ctx_push Hq0. fdestr Hq0 Hq0T Hq0X.
  fobtain (num_ex i HG' HR' HOm' HC') as t Ht.
  finst HN' t. fmp HN' Ht.
  fobtain (op0_ex HG' (incl_nil_l _) t q0) as q Hq.
  fassert HqX : (q ∈' X).
  { pose proof HOP' as O. unfold OPClos in O. finst O t. fmp O HN'. finst O q0. fmp O Hq0X. finst O q.
    exact (IE O Hq). }
  fintro Hw. fex Hw v Hv. fdestr Hv HvL Hvb.
  fassert Hrel : (Std_setrec.Rel2 (cps ps) v q).
  { unfold Std_setrec.Rel2, cps. apply (cpsf_I ps 0 i K b _ _ Hi). cbn [Nat.add].
    apply (pc_I _ _ _ _ _ _ _ t q0 Ht Hq). exact (dec_I _ K b v q0 _ tau Hb Hq0T Hvb). }
  unfold WClos in HW'. finst HW' q. fmp HW' HqX.
  fassert Hex : (∃ (Lform ∧ Std_setrec.Rel2 (cps ps) $0 q`[↑])).
  { fexists v. fsplit; [exact HvL|exact Hrel]. }
  fmp HW' Hex. fex HW' v' Hv'. fdestr Hv' Hv'X Hv'R.
  unfold Std_setrec.Rel2, cps in Hv'R.
  pose proof (cpsf_E ps 0 _ i t q0 q v' (fun _ => v') HG' HR' HOm' HC' Ht Hq Hv'R) as D.
  unfold decat in D. cbn in D. rewrite Nat.sub_0_r, Hi in D.
  apply (dec_E _ K b v' q0 _ _ Hb D). intros G2 sg HG2 HT Hb'.
  pose proof (incl_tran HG' HG2) as HG2'.
  pose proof (tup_inj K G2 sg tau q0 q0 HG2' HT (Weak Hq0T HG2) (eq_refl' HG2' q0)) as Heq.
  fexists v'. fsplit; [exact (Weak Hv'X HG2)|].
  set (sg' := fun k => if k <? K then sg k else tau k).
  rewrite (subst_ext_fb b (S K) (v' .: sg) (v' .: sg') Hb) in Hb'.
  2:{ intros [|k] Hk; [reflexivity|]. cbn. unfold sg'. destruct (Nat.ltb_spec k K); [reflexivity|lia]. }
  refine (leib_gen _ G2 (v' .: sg') (v' .: tau) HG2' _ Hb').
  intros [|k]; cbn; [apply eq_refl'; exact HG2'|]. unfold sg'. destruct (Nat.ltb_spec k K).
  - exact (Heq k ltac:(lia)).
  - apply eq_refl'; exact HG2'.
Qed.
