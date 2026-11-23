(** * New BB(14) Champion M14_fw3x4 achieves > f_(omega+3)^4(f_omega(4)) >> sigma(M14_fw3) and halts *)

From BB8 Require Import Individual142.
From Coq Require Import Lia PeanoNat List Wf_nat String Ascii.
Import ListNotations.
Set Default Goal Selector "!".

(** ** Machine definitions and explicit string pinning (eq_refl) *)

(* M12-core G-started machine string:
   1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LL1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_0LG1LN_1RN0LH_1RK0LL *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.R, B)  | A, 1 => Some (1, TM.R, A)
  | B, 0 => Some (1, TM.R, I)  | B, 1 => Some (1, TM.R, C)
  | C, 0 => Some (0, TM.L, D)  | C, 1 => Some (1, TM.L, G)
  | D, 0 => Some (0, TM.R, E)  | D, 1 => Some (1, TM.L, D)
  | E, 0 => Some (1, TM.L, L)  | E, 1 => Some (1, TM.R, F)
  | F, 0 => Some (1, TM.R, M)  | F, 1 => Some (0, TM.R, A)
  | G, 0 => Some (1, TM.R, A)  | G, 1 => Some (0, TM.L, H)
  | H, 0 => Some (1, TM.L, G)  | H, 1 => Some (1, TM.L, H)
  | I, 0 => Some (1, TM.R, E)  | I, 1 => Some (0, TM.L, J)
  | J, 0 => Some (1, TM.L, H)  | J, 1 => Some (1, TM.L, I)
  | K, 0 => None               | K, 1 => Some (0, TM.L, L)
  | L, 0 => Some (0, TM.L, G)  | L, 1 => Some (1, TM.L, N)
  | M, 0 => Some (1, TM.R, N)  | M, 1 => Some (0, TM.L, H)
  | N, 0 => Some (1, TM.R, K)  | N, 1 => Some (0, TM.L, L)
  end.

(* Strict first-visit canonical TNF (start A, all 14/14 states visited by step 129, flipped = false):
   1RB0LK_1RC1RB_1RD1RM_1RE0LH_1LF1RI_0LA1LG_1RL0LF_1LK1LD_1RJ0RB_1RG0LK_1LA1LK_---0LF_0LN1LA_0RE1LN *)
Definition tm_tnf : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.R, B)  | A, 1 => Some (0, TM.L, K)
  | B, 0 => Some (1, TM.R, C)  | B, 1 => Some (1, TM.R, B)
  | C, 0 => Some (1, TM.R, D)  | C, 1 => Some (1, TM.R, M)
  | D, 0 => Some (1, TM.R, E)  | D, 1 => Some (0, TM.L, H)
  | E, 0 => Some (1, TM.L, F)  | E, 1 => Some (1, TM.R, I)
  | F, 0 => Some (0, TM.L, A)  | F, 1 => Some (1, TM.L, G)
  | G, 0 => Some (1, TM.R, L)  | G, 1 => Some (0, TM.L, F)
  | H, 0 => Some (1, TM.L, K)  | H, 1 => Some (1, TM.L, D)
  | I, 0 => Some (1, TM.R, J)  | I, 1 => Some (0, TM.R, B)
  | J, 0 => Some (1, TM.R, G)  | J, 1 => Some (0, TM.L, K)
  | K, 0 => Some (1, TM.L, A)  | K, 1 => Some (1, TM.L, K)
  | L, 0 => None               | L, 1 => Some (0, TM.L, F)
  | M, 0 => Some (0, TM.L, N)  | M, 1 => Some (1, TM.L, A)
  | N, 0 => Some (0, TM.R, E)  | N, 1 => Some (1, TM.L, N)
  end.

(* Previous BB(14) champion M14_fw3 (M12-core A-started & strict TNF A-started) *)
Definition tm_M14_fw3 : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.R, B)  | A, 1 => Some (1, TM.R, A)
  | B, 0 => Some (1, TM.R, I)  | B, 1 => Some (1, TM.R, C)
  | C, 0 => Some (0, TM.L, D)  | C, 1 => Some (1, TM.L, G)
  | D, 0 => Some (0, TM.R, E)  | D, 1 => Some (1, TM.L, D)
  | E, 0 => Some (0, TM.L, K)  | E, 1 => Some (1, TM.R, F)
  | F, 0 => Some (1, TM.R, M)  | F, 1 => Some (0, TM.R, A)
  | G, 0 => Some (1, TM.R, A)  | G, 1 => Some (0, TM.L, H)
  | H, 0 => Some (1, TM.L, G)  | H, 1 => Some (1, TM.L, H)
  | I, 0 => Some (1, TM.R, E)  | I, 1 => Some (0, TM.L, J)
  | J, 0 => Some (1, TM.L, H)  | J, 1 => Some (1, TM.L, I)
  | K, 0 => None               | K, 1 => Some (0, TM.L, L)
  | L, 0 => Some (1, TM.L, N)  | L, 1 => Some (1, TM.L, K)
  | M, 0 => Some (1, TM.R, K)  | M, 1 => Some (0, TM.L, H)
  | N, 0 => Some (1, TM.L, D)  | N, 1 => Some (0, TM.R, K)
  end.

Definition tm_M14_fw3_tnf : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.R, B)  | A, 1 => Some (1, TM.R, A)
  | B, 0 => Some (1, TM.R, C)  | B, 1 => Some (1, TM.R, J)
  | C, 0 => Some (1, TM.R, D)  | C, 1 => Some (0, TM.L, K)
  | D, 0 => Some (0, TM.L, E)  | D, 1 => Some (1, TM.R, I)
  | E, 0 => None               | E, 1 => Some (0, TM.L, F)
  | F, 0 => Some (1, TM.L, G)  | F, 1 => Some (1, TM.L, E)
  | G, 0 => Some (1, TM.L, H)  | G, 1 => Some (0, TM.R, E)
  | H, 0 => Some (0, TM.R, D)  | H, 1 => Some (1, TM.L, H)
  | I, 0 => Some (1, TM.R, L)  | I, 1 => Some (0, TM.R, A)
  | J, 0 => Some (0, TM.L, H)  | J, 1 => Some (1, TM.L, N)
  | K, 0 => Some (1, TM.L, M)  | K, 1 => Some (1, TM.L, C)
  | L, 0 => Some (1, TM.R, E)  | L, 1 => Some (0, TM.L, M)
  | M, 0 => Some (1, TM.L, N)  | M, 1 => Some (1, TM.L, M)
  | N, 0 => Some (1, TM.R, A)  | N, 1 => Some (0, TM.L, M)
  end.

(* Explicit standard-format serializer + parser + injectivity *)
Definition sym_ch (s : Sym) : ascii :=
  match s with S0 => "0"%char | S1 => "1"%char end.

Definition dir_ch (d : TM.dir) : ascii :=
  match d with TM.L => "L"%char | TM.R => "R"%char end.

Definition state_ch (q : Q) : ascii :=
  match q with
  | A => "A"%char | B => "B"%char | C => "C"%char | D => "D"%char
  | E => "E"%char | F => "F"%char | G => "G"%char | H => "H"%char
  | I => "I"%char | J => "J"%char | K => "K"%char | L => "L"%char
  | M => "M"%char | N => "N"%char
  end.

Definition render_tr (o : option (Sym * TM.dir * Q)) : string :=
  match o with
  | None => "---"%string
  | Some (s, d, q) => String (sym_ch s) (String (dir_ch d) (String (state_ch q) EmptyString))
  end.

Definition render_row (t : TM) (q : Q) : string :=
  (render_tr (t (q, S0)) ++ render_tr (t (q, S1)))%string.

Definition render_tm (t : TM) : string :=
  (render_row t A ++ "_" ++ render_row t B ++ "_" ++ render_row t C ++ "_" ++
   render_row t D ++ "_" ++ render_row t E ++ "_" ++ render_row t F ++ "_" ++
   render_row t G ++ "_" ++ render_row t H ++ "_" ++ render_row t I ++ "_" ++
   render_row t J ++ "_" ++ render_row t K ++ "_" ++ render_row t L ++ "_" ++
   render_row t M ++ "_" ++ render_row t N)%string.

Lemma render_tr_inj : forall o1 o2, render_tr o1 = render_tr o2 -> o1 = o2.
Proof.
  intros [[[s1 d1] q1]|] [[[s2 d2] q2]|] H.
  - cbn in H. injection H as Hs Hd Hq.
    assert (s1 = s2) by (destruct s1, s2; try reflexivity; discriminate).
    assert (d1 = d2) by (destruct d1, d2; try reflexivity; discriminate).
    assert (q1 = q2) by (destruct q1, q2; try reflexivity; discriminate).
    subst; reflexivity.
  - destruct s1; discriminate.
  - destruct s2; discriminate.
  - reflexivity.
Qed.

Lemma str_app3_inj : forall c1 c2 c3 s1 c1' c2' c3' s2,
  (String c1 (String c2 (String c3 EmptyString)) ++ s1)%string =
  (String c1' (String c2' (String c3' EmptyString)) ++ s2)%string ->
  String c1 (String c2 (String c3 EmptyString)) = String c1' (String c2' (String c3' EmptyString)) /\
  s1 = s2.
Proof. intros c1 c2 c3 s1 c1' c2' c3' s2 H. cbn in H. inversion H; subst; auto. Qed.

Lemma render_tr_len3 : forall o,
  exists c1 c2 c3, render_tr o = String c1 (String c2 (String c3 EmptyString)).
Proof. intros [[[s d] q]|]; repeat eexists. Qed.

Lemma str_app_assoc : forall s1 s2 s3,
  ((s1 ++ s2) ++ s3)%string = (s1 ++ (s2 ++ s3))%string.
Proof.
  intros s1 s2 s3. induction s1 as [| c s1' IH]; cbn [String.append].
  - reflexivity.
  - f_equal. exact IH.
Qed.

Ltac peel_row Hstep H :=
  apply Hstep in H; let H0 := fresh "H0" in destruct H as [H0 H];
  apply Hstep in H; let H1 := fresh "H1" in destruct H as [H1 H];
  cbn [String.append] in H; injection H as H.

Lemma render_tm_inj : forall t1 t2,
  render_tm t1 = render_tm t2 -> forall q s, t1 (q, s) = t2 (q, s).
Proof.
  intros t1 t2 H.
  unfold render_tm, render_row in H.
  assert (Hstep : forall o1 o2 r1 r2,
    (render_tr o1 ++ r1)%string = (render_tr o2 ++ r2)%string -> o1 = o2 /\ r1 = r2).
  { intros o1 o2 r1 r2 E.
    destruct (render_tr_len3 o1) as [a1 [a2 [a3 E1]]].
    destruct (render_tr_len3 o2) as [b1 [b2 [b3 E2]]].
    rewrite E1, E2 in E.
    apply str_app3_inj in E as [Ec Er].
    split; [apply render_tr_inj; rewrite E1, E2; exact Ec | exact Er]. }
  repeat rewrite str_app_assoc in H.
  peel_row Hstep H; peel_row Hstep H; peel_row Hstep H; peel_row Hstep H;
  peel_row Hstep H; peel_row Hstep H; peel_row Hstep H; peel_row Hstep H;
  peel_row Hstep H; peel_row Hstep H; peel_row Hstep H; peel_row Hstep H;
  peel_row Hstep H.
  apply Hstep in H; destruct H as [HN0 H].
  apply render_tr_inj in H.
  intros [] []; assumption.
Qed.

Lemma tm_str_pin :
  render_tm tm =
  "1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LL1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_0LG1LN_1RN0LH_1RK0LL"%string.
Proof. reflexivity. Qed.

Lemma tm_tnf_str_pin :
  render_tm tm_tnf =
  "1RB0LK_1RC1RB_1RD1RM_1RE0LH_1LF1RI_0LA1LG_1RL0LF_1LK1LD_1RJ0RB_1RG0LK_1LA1LK_---0LF_0LN1LA_0RE1LN"%string.
Proof. reflexivity. Qed.

Lemma tm_M14_fw3_str_pin :
  render_tm tm_M14_fw3 =
  "1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_1LN1LK_1RK0LH_1LD0RK"%string.
Proof. reflexivity. Qed.

Lemma tm_M14_fw3_tnf_str_pin :
  render_tm tm_M14_fw3_tnf =
  "1RB1RA_1RC1RJ_1RD0LK_0LE1RI_---0LF_1LG1LE_1LH0RE_0RD1LH_1RL0RA_0LH1LN_1LM1LC_1RE0LM_1LN1LM_1RA0LM"%string.
Proof. reflexivity. Qed.

(** ** Tape alignment tactics and shared M12 cascade rules for tm (M14_fw3x4) *)

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition c0_core : Q * tape := G;; tape0.

Lemma align_lpow : forall (x : Sym) xs ys n,
  (x::xs)^^n *> x >> ys = x >> (xs ++ [x])^^n *> ys.
Proof.
  induction n.
  - reflexivity.
  - simpl. repeat rewrite Str_app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma align_lpow_const : forall (x : Sym) xs n,
  (x::xs)^^n *> const x = x >> (xs ++ [x])^^n *> const x.
Proof. intros. rewrite const_unfold at 1. apply align_lpow. Qed.

Ltac align_tape := repeat ((rewrite align_lpow || rewrite align_lpow_const); simpl app).
Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
Ltac finish_norm := apply evstep_refl'; norm_nat; align_tape; try reflexivity; lia_refl.

Lemma lpow_double : forall {T} (xs : list T) m, xs^^(2 * m) = (xs ++ xs)^^m.
Proof.
  induction m. - reflexivity.
  - replace (2 * S m)%nat with (S (S (2 * m))) by lia. cbn [lpow]. rewrite IHm, app_assoc. reflexivity.
Qed.

(** ** Basic shift lemmas for tm *)

Lemma cr_AR_1_1 : forall n l r, l {{A}}> [1]^^n *> r -->* [1]^^n *> l {{A}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_DL_1_1 : forall n l r, [1]^^n *> l <{{D}} r -->* l <{{D}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_HL_1_1 : forall n l r, [1]^^n *> l <{{H}} r -->* l <{{H}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_HL_01_01 : forall n l r, [0; 1]^^n *> l <{{H}} r -->* l <{{H}} [0; 1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_IL_11_10 : forall n l r, [1; 1]^^n *> l <{{I}} r -->* l <{{I}} [1; 0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_LN_11_01 : forall n l r, [1; 1]^^n *> l <{{L}} r -->* l <{{L}} [0; 1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** ** Configurations and inner M12 cascade rules *)

Definition Ca (j b : nat) (z : side) : Q * tape :=
  ([1]^^b *> [0; 1]^^j *> const 0) {{A}}> (0 >> z).

Definition Ch (j b : nat) (z : side) : Q * tape :=
  ([0; 1]^^j *> const 0) <{{H}} (1 >> [1]^^b *> 0 >> z).

Definition Ce_z (p a c d : nat) (z : side) : Q * tape :=
  ([1]^^(a + 2) *> [0; 1]^^p *> const 0) {{I}}> ([1; 0]^^c *> 0 >> [1; 0]^^d *> z).

Definition Cd_z (p b d : nat) (z : side) : Q * tape :=
  ([1]^^(b + 2) *> [0; 1]^^p *> const 0) {{I}}> ([1; 0]^^d *> z).

Definition blk (a : nat) (z : side) : side :=
  1 >> [1]^^a *> 0 >> z.

Lemma CA_SH : forall j b z,
  Ca j b (1 >> 0 >> z) -->+ Ca (S j) b z.
Proof.
  intros j b z. unfold Ca.
  start_progress.
  follow cr_DL_1_1.
  align_tape.
  execute.
  follow cr_AR_1_1.
  finish_norm.
Qed.

Lemma CA_SH_iter : forall k j b z,
  Ca j b ([1; 0]^^k *> z) -->* Ca (j + k) b z.
Proof.
  induction k; intros j b z.
  - replace (j + 0)%nat with j by lia. finish.
  - simpl.
    eapply evstep_trans; [apply progress_evstep, CA_SH |].
    follow (IHk (S j) b z).
    replace (S j + k)%nat with (j + S k)%nat by lia. finish.
Qed.

Lemma CA_EXIT : forall j b z,
  Ca j b (0 >> z) -->+ ([1]^^(b + 2) *> [0; 1]^^j *> const 0) {{I}}> z.
Proof.
  intros j b z. unfold Ca.
  start_progress.
  finish_norm.
Qed.

Lemma CA_CH : forall j b y,
  Ca j b (1 >> 1 >> y) -->+ Ch j b (1 >> y).
Proof.
  intros j b y. unfold Ca, Ch.
  start_progress.
  follow cr_HL_1_1.
  finish_norm.
Qed.

Lemma CH_0 : forall b z,
  Ch 0 b z -->+ Ca 0 (b + 3) z.
Proof.
  intros b z. unfold Ch, Ca. simpl lpow.
  start_progress.
  follow cr_AR_1_1.
  finish_norm.
Qed.

Lemma CH_S_aux : forall j b z,
  Ch (S j) b z -->+ Ca 0 2 ([1; 0]^^j *> blk (S b) z).
Proof.
  intros j b z. unfold Ch, Ca, blk.
  start_progress.
  follow cr_HL_01_01.
  align_tape.
  execute; finish_norm.
Qed.

Lemma CH_S : forall j b z,
  Ch (S j) b z -->+ Ca j 2 (blk (S b) z).
Proof.
  intros j b z.
  eapply progress_evstep_trans; [apply CH_S_aux |].
  follow (CA_SH_iter j 0 2 (blk (S b) z)).
  finish_norm.
Qed.

Lemma E_EVEN : forall p' k r,
  ([1]^^(2 * k + 2) *> [0; 1]^^(S p') *> const 0) {{I}}> (1 >> 0 >> r) -->+
  Ch p' 1 ([1; 0]^^(S k) *> 0 >> r).
Proof.
  intros p' k r. unfold Ch.
  replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_IL_11_10.
  execute; finish_norm.
Qed.

Lemma C_REL_aux : forall p' m d z,
  Cd_z (S p') (2 * m + 1) (S d) z -->+ Ch p' 3 (0 >> [1; 0]^^m *> 0 >> [1; 0]^^d *> z).
Proof.
  intros p' m d z. unfold Cd_z, Ch.
  replace (2 * m + 1 + 2)%nat with (1 + (2 * m + 2))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] m). cbn [app].
  start_progress.
  follow cr_IL_11_10.
  align_tape.
  execute; finish_norm.
Qed.

Lemma D_STEP_aux : forall p a d z,
  Ce_z p a 0 (S (S d)) z -->+ Ch p (a + 4) (0 >> [1; 0]^^d *> z).
Proof.
  intros p a d z. unfold Ce_z, Ch. norm_nat.
  start_progress.
  follow cr_HL_1_1.
  finish_norm.
Qed.

(** ** Outer rules of M14_fw3x4 (L1=1LN, N1=0LL, K0=---, K1=0LL, N0=1RK, M0=1RN, L0=0LG, E0=1LL) *)

Lemma L_bounce_to_Ch_aux : forall p r,
  ([0; 1]^^(S p) *> const 0) <{{L}} r -->+
  ([1]^^4 *> [0; 1]^^p *> const 0) {{I}}> r.
Proof.
  intros p r.
  cbn [lpow Str_app].
  start_progress.
  follow cr_HL_01_01.
  align_tape.
  do 3 step.
  change (([1]^^2 *> const 0) {{A}}> (0 >> [1; 0]^^p *> 0 >> r))
    with (Ca 0 2 ([1; 0]^^p *> 0 >> r)).
  follow (CA_SH_iter p 0 2 (0 >> r)).
  replace (0 + p)%nat with p by lia.
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma L_bounce_to_Ch : forall p q z,
  ([0; 1]^^(S p) *> const 0) <{{L}} ([0; 1]^^(S (S q)) *> z) -->+
  Ch p 6 ([0; 1]^^q *> z).
Proof.
  intros p q z.
  eapply progress_evstep_trans; [apply L_bounce_to_Ch_aux |].
  unfold Ch. cbn [lpow Str_app].
  execute.
Qed.

Lemma Outer_reload_entry : forall p k z,
  Ce_z p (2 * k) 0 0 (1 >> 0 >> 0 >> 1 >> 0 >> z) -->+
  ([0; 1]^^p *> const 0) <{{L}} ([0; 1]^^(k + 3) *> 0 >> 0 >> z).
Proof.
  intros p k z. unfold Ce_z. cbn [lpow Str_app].
  replace (2 * k + 2)%nat with (2 + 2 * k)%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_LN_11_01.
  finish_norm.
Qed.

Lemma Boot_0011_to_Loop1 : forall p k,
  ([1]^^(2 * k + 2) *> [0; 1]^^(S p) *> const 0) {{I}}> (0 >> 0 >> 1 >> 1 >> const 0) -->+
  ([0; 1]^^p *> const 0) <{{L}} (0 >> 1 >> 0 >> 0 >> [1; 0]^^k *> 1 >> 1 >> 1 >> 1 >> const 0).
Proof.
  intros p k.
  replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_LN_11_01.
  align_tape.
  execute; finish_norm.
Qed.

Lemma Trans1_entry : forall p k,
  Ce_z p (2 * k) 0 0 (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> const 0) -->+
  ([0; 1]^^p *> const 0) <{{L}} ([0; 1]^^(k + 3) *> 0 >> 1 >> 1 >> 1 >> const 0).
Proof.
  intros p k. unfold Ce_z. cbn [lpow Str_app].
  replace (2 * k + 2)%nat with (2 + 2 * k)%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_LN_11_01.
  finish_norm.
Qed.

Lemma Trans1_010111_to_Ch : forall p a,
  Ce_z p a 0 0 (1 >> 0 >> 1 >> 1 >> 1 >> const 0) -->+
  Ch p (a + 4) (1 >> 1 >> const 0).
Proof.
  intros p a. unfold Ce_z, Ch. norm_nat.
  start_progress.
  follow cr_HL_1_1.
  finish_norm.
Qed.

Lemma Trans1_empty_even : forall p k,
  ([1]^^(2 * k + 2) *> [0; 1]^^(S p) *> const 0) {{I}}> (const 0) -->+
  ([0; 1]^^p *> const 0) <{{L}} (0 >> 1 >> 0 >> 0 >> [1; 0]^^k *> 1 >> 1 >> const 0).
Proof.
  intros p k.
  do 2 (rewrite const_unfold at 2).
  replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_LN_11_01.
  align_tape.
  execute; finish_norm.
Qed.

Lemma Trans2_E0_to_L : forall p k,
  Ce_z p (2 * k) 0 0 (1 >> 0 >> 0 >> 1 >> 1 >> const 0) -->+
  ([0; 1]^^p *> const 0) <{{L}} ([0; 1]^^(k + 4) *> const 0).
Proof.
  intros p k. unfold Ce_z. cbn [lpow Str_app].
  replace (2 * k + 2)%nat with (2 + 2 * k)%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_LN_11_01.
  finish_norm.
Qed.

Lemma Trans2_empty_odd : forall p m,
  Cd_z p (2 * m + 1) 0 (const 0) -->+
  ([0; 1]^^p *> const 0) <{{L}} ([0; 1]^^(m + 2) *> 1 >> const 0).
Proof.
  intros p m. unfold Cd_z. cbn [lpow Str_app].
  do 2 (rewrite const_unfold at 2).
  replace (2 * m + 1 + 2)%nat with (3 + 2 * m)%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] m). cbn [app].
  start_progress.
  follow cr_LN_11_01.
  finish_norm.
Qed.

Lemma Trans2_011_reload : forall p k,
  Ce_z (S p) (2 * k) 0 0 (1 >> 1 >> const 0) -->+
  ([0; 1]^^p *> const 0) <{{L}} (0 >> 1 >> 0 >> 0 >> [1; 0]^^(k + 2) *> 0 >> 1 >> 1 >> const 0).
Proof.
  intros p k. unfold Ce_z. cbn [lpow Str_app].
  do 4 (rewrite const_unfold at 2).
  replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_LN_11_01.
  align_tape.
  execute; finish_norm.
Qed.

Lemma Trans3_0100011_reload : forall p k,
  Ce_z (S p) (2 * k) 0 0 (1 >> 0 >> 0 >> 0 >> 1 >> 1 >> const 0) -->+
  ([0; 1]^^p *> const 0) <{{L}} (0 >> 1 >> 0 >> 0 >> [1; 0]^^(k + 4) *> const 0).
Proof.
  intros p k. unfold Ce_z. cbn [lpow Str_app].
  replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_LN_11_01.
  align_tape.
  execute.
Qed.

Lemma Trans4_E1_to_L : forall p k,
  Ce_z p (2 * k) 0 0 (1 >> 0 >> 0 >> 1 >> 0 >> const 0) -->+
  ([0; 1]^^p *> const 0) <{{L}} ([0; 1]^^(k + 3) *> const 0).
Proof.
  intros p k.
  eapply progress_evstep_trans; [apply Outer_reload_entry |].
  do 2 rewrite <- const_unfold.
  finish.
Qed.

Definition c_end (p a : nat) : Q * tape :=
  ([1]^^(a + 7) *> [0; 1]^^p *> const 0) {{K}}> const 0.

Lemma Trans4_HALT : forall p a,
  Ce_z p a 0 0 (1 >> const 0) -->+ c_end p a.
Proof.
  intros p a. unfold Ce_z, c_end. norm_nat.
  do 3 (rewrite const_unfold at 2).
  start_progress; try finish_norm.
Qed.

Lemma c_end_halted : forall p a, halted tm (c_end p a).
Proof. intros p a. unfold c_end. reflexivity. Qed.

(** ** Exact hierarchy function W and inner transitions *)

Local Open Scope nat_scope.

Fixpoint iter {X : Type} (n : nat) (g : X -> X) (x : X) : X :=
  match n with
  | O => x
  | S n' => g (iter n' g x)
  end.

Lemma iter_S' : forall {X : Type} n (g : X -> X) x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

Lemma iter_add : forall {X : Type} a b (g : X -> X) x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

Fixpoint W (j : nat) (b : nat) : nat :=
  match j with
  | O => b + 3
  | S j' => iter (S b) (W j') 2
  end.

Lemma W_0 : forall b, W 0 b = b + 3. Proof. reflexivity. Qed.
Lemma W_S : forall j b, W (S j) b = iter (S b) (W j) 2. Proof. reflexivity. Qed.

Lemma BLK_iter_aux : forall j,
  (forall b z, Ch j b z -->+ Ca j (W j b) z) ->
  forall a b z, Ca j b (blk a z) -->+ Ca (S j) (iter a (W j) b) z.
Proof.
  intros j HCh a. induction a as [| a IHa]; intros b z.
  - apply CA_SH.
  - eapply progress_evstep_trans; [apply CA_CH |].
    eapply evstep_trans; [apply progress_evstep, HCh |].
    rewrite iter_S'.
    apply progress_evstep, IHa.
Qed.

Lemma CH_CA : forall j b z,
  Ch j b z -->+ Ca j (W j b) z.
Proof.
  induction j as [| j IHj]; intros b z.
  - apply CH_0.
  - eapply progress_evstep_trans; [apply CH_S |].
    apply progress_evstep.
    apply (BLK_iter_aux j IHj (S b) 2 z).
Qed.

Lemma CE_EVEN : forall p' k c d z,
  Ce_z (S p') (2 * k) (S c) d z -->+ Ce_z (p' + S k) (W p' 1) c d z.
Proof.
  intros p' k c d z. unfold Ce_z.
  cbn [lpow Str_app].
  eapply progress_evstep_trans; [apply E_EVEN |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  follow (CA_SH_iter (S k) p' (W p' 1) (0 >> [1; 0]^^c *> 0 >> [1; 0]^^d *> z)%sym).
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma C_REL : forall p' m d z,
  Cd_z (S p') (2 * m + 1) (S d) z -->+ Ce_z p' (W p' 3) m d z.
Proof.
  intros p' m d z. unfold Ce_z.
  eapply progress_evstep_trans; [apply C_REL_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma D_STEP : forall p a d z,
  Ce_z p a 0 (S (S d)) z -->+ Cd_z p (W p (a + 4)) d z.
Proof.
  intros p a d z. unfold Cd_z.
  eapply progress_evstep_trans; [apply D_STEP_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma L_bounce_exec : forall p q z,
  ([S0; S1]^^(S p) *> const S0) <{{L}} ([S0; S1]^^(S (S (S q))) *> z) -->+
  Cd_z p (W p 6) q (S1 >> z).
Proof.
  intros p q z.
  eapply progress_evstep_trans; [apply (L_bounce_to_Ch p (S q) z) |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  unfold Cd_z. cbn [lpow Str_app].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

(** ** Concrete blank-tape boot (240 literal steps from c0_core = G;; tape0) *)

Lemma Boot_240 :
  c0_core -->* Ch 6 3 (S0 >> S1 >> S0 >> S0 >> S0 >> S1 >> S1 >> const S0).
Proof.
  unfold c0_core, Ch. cbn [lpow Str_app].
  do 240 step; finish_norm.
Qed.

(** ** Growth, parity, and exact mod-12 invariants of W *)

Ltac absmod x k :=
  let q := fresh "q" in let r := fresh "r" in
  let H1 := fresh "Hdm" in let H2 := fresh "Hmb" in
  pose proof (Nat.div_mod_eq x k) as H1;
  assert (H2 : x mod k < k) by (apply Nat.mod_upper_bound; discriminate);
  set (q := x / k) in *; set (r := x mod k) in *; clearbody q r.
Ltac mods :=
  repeat match goal with
  | H : context[?x mod ?k] |- _ => absmod x k
  | |- context[?x mod ?k] => absmod x k
  | H : context[?x / ?k] |- _ => absmod x k
  | |- context[?x / ?k] => absmod x k
  end.

Lemma iter_lin3 : forall g, (forall a, a + 3 <= g a) -> forall n x, x + 3 * n <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl; [lia |].
  specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_par_nat : forall g, (forall y, g y mod 2 = (y + 1) mod 2) ->
  forall n x, iter n g x mod 2 = (x + n) mod 2.
Proof.
  intros g Hg. induction n; intros x; cbn [iter].
  - f_equal; lia.
  - rewrite Hg. pose proof (IHn x). mods; lia.
Qed.

Lemma W_grow : forall j b, b + 3 <= W j b.
Proof.
  induction j as [| j IHj]; intros b.
  - rewrite W_0. lia.
  - rewrite W_S. pose proof (iter_lin3 (W j) IHj (S b) 2). lia.
Qed.

Lemma W_par : forall j b, W j b mod 2 = (b + 1) mod 2.
Proof.
  induction j as [| j IHj]; intros b.
  - rewrite W_0. mods; lia.
  - rewrite W_S. rewrite (iter_par_nat (W j) IHj). mods; lia.
Qed.

Lemma iter_W0 : forall n x, iter n (W 0) x = x + 3 * n.
Proof. induction n; intros x; cbn [iter]; [lia | rewrite W_0, IHn; lia]. Qed.

Lemma W_1 : forall b, W 1 b = 3 * b + 5.
Proof. intros b. rewrite W_S, iter_W0. lia. Qed.

Lemma iter_W1_closed : forall n,
  2 * iter n (W 1) 2 + 5 = 3 ^ (n + 2).
Proof.
  induction n as [| n IHn]; cbn [iter].
  - reflexivity.
  - rewrite W_1.
    change (S n + 2) with (S (n + 2)).
    rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma W2_closed : forall b,
  2 * W 2 b + 5 = 3 ^ (b + 3).
Proof.
  intros b. rewrite W_S.
  replace (b + 3) with (S b + 2) by lia.
  apply iter_W1_closed.
Qed.

Lemma W2_ge : forall y, 9 * y + 11 <= W 2 y.
Proof.
  intros y. rewrite W_S.
  change (iter (S y) (W 1) 2) with (W 1 (iter y (W 1) 2)).
  pose proof (iter_lin3 (W 1) (W_grow 1) y 2).
  rewrite W_1. lia.
Qed.

Lemma W_ge3_S_is_W2 : forall j b,
  exists y, 29 <= y /\ W (S (S (S j))) (S b) = W 2 y.
Proof.
  induction j as [| j IHj]; intros b.
  - change (W 3 (S b)) with (W 2 (iter (S b) (W 2) 2)).
    exists (iter (S b) (W 2) 2). split; [| reflexivity].
    change (iter (S b) (W 2) 2) with (W 2 (iter b (W 2) 2)).
    pose proof (iter_lin3 (W 2) (W_grow 2) b 2) as H0.
    pose proof (W2_ge (iter b (W 2) 2)) as H1. lia.
  - change (W (S (S (S (S j)))) (S b)) with (W (S (S (S j))) (iter (S b) (W (S (S (S j)))) 2)).
    pose proof (iter_lin3 (W (S (S (S j)))) (W_grow (S (S (S j)))) (S b) 2) as H0.
    destruct (iter (S b) (W (S (S (S j)))) 2) as [| z]; [lia |].
    apply IHj.
Qed.

(* Exact mod-12 invariants:
   is_W_even a: a == 2 (mod 12), i.e., a = 2*k with k >= 136 and k == 1 (mod 3) [k + 2 = 3*((k+2)/3)]
   is_W_odd  b: b == 11 (mod 12), i.e., b = 2*m + 1 with m >= 59 and m == 2 (mod 3) [m + 1 = 3*((m+1)/3)] *)
Definition is_W_even (a : nat) : Prop :=
  a = 2 * (a / 2) /\ 136 <= a / 2 /\ a / 2 + 2 = 3 * ((a / 2 + 2) / 3).

Definition is_W_odd (b : nat) : Prop :=
  b = 2 * (b / 2) + 1 /\ 59 <= b / 2 /\ b / 2 + 1 = 3 * ((b / 2 + 1) / 3).

Lemma W_ge3_odd : forall p b,
  3 <= p -> b mod 2 = 1 -> is_W_even (W p b).
Proof.
  intros [| [| [| j]]] [| b'] Hp Hb; try lia.
  - cbn in Hb. discriminate.
  - destruct (W_ge3_S_is_W2 j b') as [y [Hy Hw]].
    pose proof (W_par (S (S (S j))) (S b')) as Hpar.
    rewrite Hw in *.
    pose proof (W2_ge y) as Hge.
    assert (Hev : W 2 y mod 2 = 0) by (mods; lia).
    assert (Hpow : 2 * W 2 y + 5 = 9 * 3 ^ (y + 1)).
    { rewrite W2_closed. replace (y + 3) with (2 + (y + 1)) by lia.
      rewrite Nat.pow_add_r. change (3 ^ 2) with 9. lia. }
    set (a := W 2 y) in *; clearbody a; clear Hw Hpar.
    unfold is_W_even.
    assert (Ha_eq : a = 2 * (a / 2) /\ 136 <= a / 2) by (mods; lia).
    destruct Ha_eq as [H1 H2].
    split; [exact H1 | split; [exact H2 |]].
    set (p3 := 3 ^ (y + 1)) in *; clearbody p3.
    mods; lia.
Qed.

Lemma W_ge3_even : forall p b,
  3 <= p -> 1 <= b -> b mod 2 = 0 -> is_W_odd (W p b).
Proof.
  intros [| [| [| j]]] [| b'] Hp Hb Hev; try lia.
  destruct (W_ge3_S_is_W2 j b') as [y [Hy Hw]].
  pose proof (W_par (S (S (S j))) (S b')) as Hpar.
  rewrite Hw in *.
  pose proof (W2_ge y) as Hge.
  assert (Hodd : W 2 y mod 2 = 1) by (mods; lia).
  assert (Hpow : 2 * W 2 y + 5 = 9 * 3 ^ (y + 1)).
  { rewrite W2_closed. replace (y + 3) with (2 + (y + 1)) by lia.
    rewrite Nat.pow_add_r. change (3 ^ 2) with 9. lia. }
  set (w := W 2 y) in *; clearbody w; clear Hw Hpar.
  unfold is_W_odd.
  assert (Hw_eq : w = 2 * (w / 2) + 1 /\ 59 <= w / 2) by (mods; lia).
  destruct Hw_eq as [H1 H2].
  split; [exact H1 | split; [exact H2 |]].
  set (p3 := 3 ^ (y + 1)) in *; clearbody p3.
  mods; lia.
Qed.

Lemma W2_1_val : W 2 1 = 38. Proof. reflexivity. Qed.
Lemma W2_2_val : W 2 2 = 119.
Proof. pose proof (W2_closed 2) as H. change (3 ^ (2 + 3)) with 243 in H. lia. Qed.
Lemma W1_3_val : W 1 3 = 14. Proof. reflexivity. Qed.
Lemma W1_18_val : W 1 18 = 59. Proof. rewrite W_1. lia. Qed.
Lemma W0_3_val : W 0 3 = 6. Proof. reflexivity. Qed.

Opaque W.
Strategy opaque [W].

(** ** Macro-step functions for M14_fw3x4 *)

Definition Kc (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  (p + a / 2, W (p - 1) 1).

Definition Kc_full (pb : nat * nat) : nat * nat :=
  let '(p, b) := pb in
  iter (b / 2) Kc (p - 1, W (p - 1) 3).

Definition Kd_step (pb : nat * nat) : nat * nat :=
  let '(p', a') := Kc_full pb in
  (p', W p' (a' + 4)).

Definition Kd_iter (m : nat) (pb : nat * nat) : nat * nat :=
  iter m Kd_step pb.

Definition L_bounce_pb (p : nat) : nat * nat :=
  (p - 1, W (p - 1) 6).

(* Universal Outer_step for M14_fw3x4:
   Cd_z p b 2 (0 >> [1;0]^(S E) *> S)
     --Kc_full--> Ce_z p1 a1 0 0 (1 >> 0 >> 0 >> [1;0]^(S E) *> S)
     --O3 + L_bounce--> Cd_z (p1-1) (W (p1-1) 6) (a1/2 + 1) (0 >> [1;0]^E *> S)
     --Kd_iter ((a1/2 - 1)/3)--> Cd_z p2 b2 2 (0 >> [1;0]^E *> S) *)
Definition Outer_step (pb : nat * nat) : nat * nat :=
  let '(p1, a1) := Kc_full pb in
  Kd_iter ((a1 / 2 - 1) / 3) (L_bounce_pb p1).

Lemma Kc_unfold : forall p a, Kc (p, a) = (p + a / 2, W (p - 1) 1). Proof. reflexivity. Qed.
Lemma Kc_full_unfold : forall p b, Kc_full (p, b) = iter (b / 2) Kc (p - 1, W (p - 1) 3). Proof. reflexivity. Qed.
Lemma Kd_step_unfold : forall pb, Kd_step pb = let '(p', a') := Kc_full pb in (p', W p' (a' + 4)). Proof. reflexivity. Qed.
Lemma Kd_iter_unfold : forall m pb, Kd_iter m pb = iter m Kd_step pb. Proof. reflexivity. Qed.
Lemma L_bounce_pb_unfold : forall p, L_bounce_pb p = (p - 1, W (p - 1) 6). Proof. reflexivity. Qed.
Lemma Outer_step_unfold : forall pb,
  Outer_step pb = let '(p1, a1) := Kc_full pb in Kd_iter ((a1 / 2 - 1) / 3) (L_bounce_pb p1).
Proof. reflexivity. Qed.

Lemma Kc_step : forall c d z pa,
  1 <= fst pa -> snd pa = 2 * (snd pa / 2) ->
  Ce_z (fst pa) (snd pa) (S c) d z -->+ Ce_z (fst (Kc pa)) (snd (Kc pa)) c d z.
Proof.
  intros c d z [p a] Hp Ha_eq. cbn [fst snd Kc] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  replace (S p' + a / 2) with (p' + S (a / 2)) by lia.
  rewrite Ha_eq at 1.
  apply CE_EVEN.
Qed.

Lemma Kc_loop : forall c d z pa,
  4 <= fst pa -> is_W_even (snd pa) ->
  Ce_z (fst pa) (snd pa) c d z -->* Ce_z (fst (iter c Kc pa)) (snd (iter c Kc pa)) 0 d z /\
  fst pa + c <= fst (iter c Kc pa) /\
  is_W_even (snd (iter c Kc pa)).
Proof.
  induction c as [| c IHc]; intros d z pa Hp Ha.
  - cbn [iter]. split; [finish | split; [lia | exact Ha]].
  - rewrite iter_S'.
    destruct Ha as [Ha_eq [Ha_ge Ha_div3]].
    assert (Hw1 : is_W_even (snd (Kc pa))).
    { destruct pa as [p a]. cbn [fst snd Kc] in *. apply W_ge3_odd; [lia | reflexivity]. }
    assert (Hp1 : fst pa + 1 <= fst (Kc pa)).
    { destruct pa as [p a]. cbn [fst snd Kc] in *. lia. }
    destruct (IHc d z (Kc pa) ltac:(lia) Hw1) as [Hrun [Hp2 Ha2]].
    split; [| split].
    + eapply evstep_trans; [apply progress_evstep, (Kc_step c d z pa ltac:(lia) Ha_eq) | exact Hrun].
    + lia.
    + exact Ha2.
Qed.

Lemma Kc_full_all : forall d z pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) (S d) z -->+ Ce_z (fst (Kc_full pb)) (snd (Kc_full pb)) 0 d z /\
  fst pb + 58 <= fst (Kc_full pb) /\
  is_W_even (snd (Kc_full pb)).
Proof.
  intros d z [p b] Hp [Hb_eq [Hb_ge Hb_m3]]. cbn [fst snd Kc_full] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  assert (Hw3 : is_W_even (W p' 3)) by (apply W_ge3_odd; [lia | reflexivity]).
  destruct (Kc_loop (b / 2) d z (p', W p' 3) ltac:(cbn; lia) Hw3) as [Hrun [Hp1 Ha1]].
  cbn [fst snd] in *.
  split; [| split].
  - rewrite Hb_eq at 1.
    eapply progress_evstep_trans; [apply C_REL | exact Hrun].
  - lia.
  - exact Ha1.
Qed.

Lemma Kd_step_all : forall d z pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) (S (S (S d))) z -->+ Cd_z (fst (Kd_step pb)) (snd (Kd_step pb)) d z /\
  fst pb + 58 <= fst (Kd_step pb) /\
  is_W_odd (snd (Kd_step pb)).
Proof.
  intros d z pb Hp Hb.
  unfold Kd_step.
  destruct (Kc_full_all (S (S d)) z pb Hp Hb) as [Hkc [Hp1 Ha1]].
  set (pa' := Kc_full pb) in *.
  destruct pa' as [p' a']. cbn [fst snd] in *.
  destruct Ha1 as [Ha_eq _].
  assert (Ha4_ev : (a' + 4) mod 2 = 0).
  { replace (a' + 4) with (0 + (a' / 2 + 2) * 2) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (Hw : is_W_odd (W p' (a' + 4))) by (apply W_ge3_even; [lia | lia | exact Ha4_ev]).
  split; [| split].
  - eapply progress_evstep_trans; [exact Hkc | apply progress_evstep, D_STEP].
  - exact Hp1.
  - exact Hw.
Qed.

Lemma Kd_loop : forall m r z pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) (3 * m + r) z -->* Cd_z (fst (Kd_iter m pb)) (snd (Kd_iter m pb)) r z /\
  fst pb + 58 * m <= fst (Kd_iter m pb) /\
  is_W_odd (snd (Kd_iter m pb)).
Proof.
  unfold Kd_iter.
  induction m as [| m IHm]; intros r z pb Hp Hb.
  - cbn [iter]. replace (3 * 0 + r) with r by lia.
    split; [finish | split; [lia | exact Hb]].
  - rewrite iter_S'.
    replace (3 * S m + r) with (S (S (S (3 * m + r)))) by lia.
    destruct (Kd_step_all (3 * m + r) z pb Hp Hb) as [Hstep [Hp1 Hb1]].
    destruct (IHm r z (Kd_step pb) ltac:(lia) Hb1) as [Hrun [Hp2 Hb2]].
    split; [| split].
    + eapply evstep_trans; [apply progress_evstep, Hstep | exact Hrun].
    + lia.
    + exact Hb2.
Qed.

Lemma L_bounce_pb_props : forall p,
  6 <= p ->
  fst (L_bounce_pb p) = p - 1 /\
  is_W_odd (snd (L_bounce_pb p)).
Proof.
  intros p Hp. unfold L_bounce_pb. cbn [fst snd].
  split; [reflexivity |].
  apply W_ge3_even; [lia | lia | reflexivity].
Qed.

(** ** Universal Loop_init, Outer_step_exec, and Outer_loop (valid for ANY sentinel sent!) *)

Lemma Loop_init : forall p E sent,
  7 <= p ->
  ([S0; S1]^^p *> const S0) <{{L}} (S0 >> S1 >> S0 >> S0 >> [S1; S0]^^(S E) *> sent) -->+
  Cd_z (fst (L_bounce_pb (p - 1))) (snd (L_bounce_pb (p - 1))) 2 (S0 >> [S1; S0]^^E *> sent) /\
  5 <= fst (L_bounce_pb (p - 1)) /\
  is_W_odd (snd (L_bounce_pb (p - 1))).
Proof.
  intros p E sent Hp.
  destruct (L_bounce_pb_props (p - 1) ltac:(lia)) as [Hlb_p Hlb_odd].
  split; [| split; [lia | exact Hlb_odd]].
  replace ([S0; S1]^^p) with ([S0; S1]^^(S (p - 1))) by (f_equal; lia).
  eapply progress_evstep_trans; [apply L_bounce_to_Ch_aux |].
  change (([S1]^^4 *> [S0; S1]^^(p - 1) *> const S0) {{I}}> (S0 >> S1 >> S0 >> S0 >> [S1; S0]^^(S E) *> sent))
    with (Ce_z (p - 1) (2 * 1) 0 0 (S1 >> S0 >> S0 >> S1 >> S0 >> [S1; S0]^^E *> sent)).
  eapply evstep_trans; [apply progress_evstep, Outer_reload_entry |].
  replace ([S0; S1]^^(p - 1)) with ([S0; S1]^^(S (p - 2))) by (f_equal; lia).
  change (1 + 3) with (S (S (S 1))).
  eapply evstep_trans; [apply progress_evstep, L_bounce_exec |].
  unfold L_bounce_pb. cbn [fst snd].
  replace (p - 1 - 1) with (p - 2) by lia.
  unfold Cd_z. cbn [lpow Str_app]. finish.
Qed.

Lemma lpow_push10 : forall d z,
  [S1; S0]^^d *> (S1 >> S0 >> z) = [S1; S0]^^(S d) *> z.
Proof.
  induction d as [| d IHd]; intros z.
  - reflexivity.
  - cbn [lpow]. rewrite !Str_app_assoc. cbn [Str_app]. rewrite IHd. reflexivity.
Qed.

Lemma Cd_z_push10 : forall p b d z,
  Cd_z p b d (S1 >> S0 >> z) = Cd_z p b (S d) z.
Proof. intros p b d z. unfold Cd_z. rewrite lpow_push10. reflexivity. Qed.

Lemma Outer_step_exec : forall E sent pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) 2 (S0 >> [S1; S0]^^(S E) *> sent) -->+
  Cd_z (fst (Outer_step pb)) (snd (Outer_step pb)) 2 (S0 >> [S1; S0]^^E *> sent) /\
  5 <= fst (Outer_step pb) /\
  is_W_odd (snd (Outer_step pb)).
Proof.
  intros E sent pb Hp Hb.
  rewrite Outer_step_unfold.
  destruct (Kc_full_all 0 (S1 >> S0 >> S0 >> [S1; S0]^^(S E) *> sent) pb Hp Hb) as [Hkc [Hp1 Ha1]].
  set (pa1 := Kc_full pb) in *.
  destruct pa1 as [p1 a1]. cbn [fst snd] in *.
  destruct Ha1 as [Ha1_eq [Ha1_ge Ha1_m3]].
  set (M := (a1 / 2 - 1) / 3) in *.
  assert (HM_eq : S (a1 / 2) = 3 * M + 2) by (unfold M; mods; lia).
  destruct (L_bounce_pb_props p1 ltac:(lia)) as [Hlb_p Hlb_odd].
  destruct (Kd_loop M 2 (S0 >> [S1; S0]^^E *> sent) (L_bounce_pb p1) ltac:(lia) Hlb_odd)
    as [Hkd [Hkd_p Hkd_odd]].
  split; [| split; [lia | exact Hkd_odd]].
  change (Cd_z (fst pb) (snd pb) 2 (S0 >> [S1; S0]^^(S E) *> sent))
    with (Cd_z (fst pb) (snd pb) 1 (S1 >> S0 >> S0 >> [S1; S0]^^(S E) *> sent)).
  eapply progress_evstep_trans; [exact Hkc |].
  change (Ce_z p1 a1 0 0 (S1 >> S0 >> S0 >> [S1; S0]^^(S E) *> sent))
    with (Ce_z p1 a1 0 0 (S1 >> S0 >> S0 >> S1 >> S0 >> [S1; S0]^^E *> sent)).
  rewrite Ha1_eq at 1.
  eapply evstep_trans; [apply progress_evstep, Outer_reload_entry |].
  replace ([S0; S1]^^p1) with ([S0; S1]^^(S (p1 - 1))) by (f_equal; lia).
  replace (a1 / 2 + 3) with (S (S (S (a1 / 2)))) by lia.
  eapply evstep_trans; [apply progress_evstep, L_bounce_exec |].
  rewrite Cd_z_push10.
  rewrite HM_eq.
  exact Hkd.
Qed.

Opaque Kc Kc_full Kd_step Kd_iter L_bounce_pb Outer_step.
Strategy opaque [Kc Kc_full Kd_step Kd_iter L_bounce_pb Outer_step].

Lemma Outer_loop : forall E sent pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) 2 (S0 >> [S1; S0]^^E *> sent) -->*
  Cd_z (fst (iter E Outer_step pb)) (snd (iter E Outer_step pb)) 2 (S0 >> sent) /\
  5 <= fst (iter E Outer_step pb) /\
  is_W_odd (snd (iter E Outer_step pb)).
Proof.
  induction E as [| E IHE]; intros sent pb Hp Hb.
  - cbn [iter lpow Str_app]. split; [finish | split; [exact Hp | exact Hb]].
  - rewrite iter_S'.
    destruct (Outer_step_exec E sent pb Hp Hb) as [Hst [Hp1 Hb1]].
    destruct (IHE sent (Outer_step pb) Hp1 Hb1) as [Hrest [Hp2 Hb2]].
    split; [| split; [exact Hp2 | exact Hb2]].
    eapply evstep_trans; [apply progress_evstep, Hst | exact Hrest].
Qed.

(** ** Stage transition functions (abstracted over pb so unification never unfolds iter) *)

Definition Trans1_pa1 (pb : nat * nat) : nat * nat := Kc_full pb.
Definition Trans1_pba (pb : nat * nat) : nat * nat :=
  let '(p1, a1) := Trans1_pa1 pb in Kd_iter ((a1 / 2 - 1) / 3) (L_bounce_pb p1).
Definition Trans1_pa2 (pb : nat * nat) : nat * nat := Kc_full (Trans1_pba pb).
Definition Trans1_b_end (pb : nat * nat) : nat :=
  let '(p2, a2) := Trans1_pa2 pb in W p2 (W p2 (a2 + 4)).
Definition Trans1_E (pb : nat * nat) : nat := Trans1_b_end pb / 2 - 1.
Definition Trans1_pb (pb : nat * nat) : nat * nat := L_bounce_pb (fst (Trans1_pa2 pb) - 1).

Definition Trans2_pa1 (pb : nat * nat) : nat * nat := Kc_full pb.
Definition Trans2_pba (pb : nat * nat) : nat * nat :=
  let '(p1, a1) := Trans2_pa1 pb in Kd_iter ((a1 / 2 + 2) / 3) (L_bounce_pb p1).
Definition Trans2_pbb (pb : nat * nat) : nat * nat :=
  let '(pa, ba) := Trans2_pba pb in Kd_iter ((ba / 2 - 2) / 3) (L_bounce_pb pa).
Definition Trans2_pa2 (pb : nat * nat) : nat * nat := Kc_full (Trans2_pbb pb).
Definition Trans2_E (pb : nat * nat) : nat := snd (Trans2_pa2 pb) / 2 + 1.
Definition Trans2_pb (pb : nat * nat) : nat * nat := L_bounce_pb (fst (Trans2_pa2 pb) - 2).

Definition Trans3_pa1 (pb : nat * nat) : nat * nat := Kc_full pb.
Definition Trans3_E (pb : nat * nat) : nat := snd (Trans3_pa1 pb) / 2 + 3.
Definition Trans3_pb (pb : nat * nat) : nat * nat := L_bounce_pb (fst (Trans3_pa1 pb) - 2).

Definition Trans4_pa1 (pb : nat * nat) : nat * nat := Kc_full pb.
Definition Trans4_pbfin (pb : nat * nat) : nat * nat :=
  let '(p1, a1) := Trans4_pa1 pb in Kd_iter ((a1 / 2 - 1) / 3) (L_bounce_pb p1).
Definition Trans4_pa_final (pb : nat * nat) : nat * nat := Kc_full (Trans4_pbfin pb).

Lemma W6_3_even : is_W_even (W 6 3).
Proof. apply W_ge3_odd; [lia | reflexivity]. Qed.

Lemma W5_1_even : is_W_even (W 5 1).
Proof. apply W_ge3_odd; [lia | reflexivity]. Qed.

Definition E0 : nat := W 5 1 / 2 - 1.
Definition pb_L1_0 : nat * nat := L_bounce_pb (4 + W 6 3 / 2).

Lemma Boot_to_Loop1 :
  c0_core -->* Cd_z (fst pb_L1_0) (snd pb_L1_0) 2 (S0 >> [S1; S0]^^E0 *> S1 >> S1 >> S1 >> S1 >> const S0) /\
  5 <= fst pb_L1_0 /\
  is_W_odd (snd pb_L1_0).
Proof.
  destruct W6_3_even as [Hw6_eq [Hw6_ge _]].
  destruct W5_1_even as [Hw5_eq [Hw5_ge _]].
  assert (HE0_eq : W 5 1 / 2 = S E0) by (clear - Hw5_ge; unfold E0; lia).
  destruct (Loop_init (5 + W 6 3 / 2) E0 (S1 >> S1 >> S1 >> S1 >> const S0) ltac:(clear - Hw6_ge; lia))
    as [Hinit [Hp0 Hb0]].
  replace (5 + W 6 3 / 2 - 1) with (4 + W 6 3 / 2) in Hinit, Hp0, Hb0 by (clear; generalize (W 6 3 / 2); intros; lia).
  fold pb_L1_0 in Hinit, Hp0, Hb0.
  split; [| split; [exact Hp0 | exact Hb0]].
  eapply evstep_trans; [exact Boot_240 |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  rewrite Hw6_eq at 1.
  eapply evstep_trans; [apply progress_evstep, (E_EVEN 5 (W 6 3 / 2) (S0 >> S0 >> S1 >> S1 >> const S0)) |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply (CA_SH_iter (S (W 6 3 / 2)) 5 (W 5 1) (S0 >> S0 >> S0 >> S1 >> S1 >> const S0)) |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  replace (5 + S (W 6 3 / 2)) with (S (5 + W 6 3 / 2)) by (clear; generalize (W 6 3 / 2); intros; lia).
  rewrite Hw5_eq at 1.
  eapply evstep_trans; [apply progress_evstep, Boot_0011_to_Loop1 |].
  rewrite HE0_eq.
  apply progress_evstep, Hinit.
Qed.

Lemma Trans1_exec : forall pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) 2 (S0 >> S1 >> S1 >> S1 >> S1 >> const S0) -->+
  Cd_z (fst (Trans1_pb pb)) (snd (Trans1_pb pb)) 2 (S0 >> [S1; S0]^^(Trans1_E pb) *> S1 >> S1 >> const S0) /\
  5 <= fst (Trans1_pb pb) /\
  is_W_odd (snd (Trans1_pb pb)).
Proof.
  intros pb Hp Hb.
  unfold Trans1_pb, Trans1_E, Trans1_b_end, Trans1_pa2, Trans1_pba, Trans1_pa1.
  destruct (Kc_full_all 0 (S1 >> S0 >> S0 >> S1 >> S1 >> S1 >> S1 >> const S0) pb Hp Hb)
    as [Hkc1 [Hp1 Ha1]].
  set (pa1 := Kc_full pb) in *.
  destruct pa1 as [p1 a1]. cbn [fst snd] in *.
  destruct Ha1 as [Ha1_eq [Ha1_ge Ha1_m3]].
  set (M1 := (a1 / 2 - 1) / 3) in *.
  assert (HM1_eq : S (a1 / 2) = 3 * M1 + 2) by (unfold M1; mods; lia).
  destruct (L_bounce_pb_props p1 ltac:(lia)) as [Hlb1_p Hlb1_odd].
  destruct (Kd_loop M1 2 (S1 >> S1 >> S1 >> const S0) (L_bounce_pb p1) ltac:(lia) Hlb1_odd)
    as [Hkd1 [Hkd1_p Hkd1_odd]].
  set (pba := Kd_iter M1 (L_bounce_pb p1)) in *.
  destruct (Kc_full_all 0 (S1 >> S0 >> S1 >> S1 >> S1 >> const S0) pba ltac:(lia) Hkd1_odd)
    as [Hkc2 [Hp2 Ha2]].
  set (pa2 := Kc_full pba) in *.
  destruct pa2 as [p2 a2]. cbn [fst snd] in *.
  destruct Ha2 as [Ha2_eq [Ha2_ge Ha2_m3]].
  assert (Ha2_4_ev : (a2 + 4) mod 2 = 0).
  { replace (a2 + 4) with (0 + (a2 / 2 + 2) * 2) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (Hw_mid : is_W_odd (W p2 (a2 + 4)))
    by (apply W_ge3_even; [lia | lia | exact Ha2_4_ev]).
  assert (Hw_mid_odd : W p2 (a2 + 4) mod 2 = 1).
  { destruct Hw_mid as [Hmq _]. mods; lia. }
  assert (Hb_t1_ev : is_W_even (W p2 (W p2 (a2 + 4)))).
  { apply W_ge3_odd; [lia | exact Hw_mid_odd]. }
  set (bend := W p2 (W p2 (a2 + 4))) in *.
  destruct Hb_t1_ev as [Hb1_eq [Hb1_ge Hb1_m3]].
  set (E1 := bend / 2 - 1) in *.
  assert (HE1_eq : bend / 2 = S E1) by (unfold E1; lia).
  destruct (Loop_init p2 E1 (S1 >> S1 >> const S0) ltac:(lia))
    as [Hinit [HL2_p HL2_odd]].
  split; [| split; [exact HL2_p | exact HL2_odd]].
  change (Cd_z (fst pb) (snd pb) 2 (S0 >> S1 >> S1 >> S1 >> S1 >> const S0))
    with (Cd_z (fst pb) (snd pb) 1 (S1 >> S0 >> S0 >> S1 >> S1 >> S1 >> S1 >> const S0)).
  eapply progress_evstep_trans; [exact Hkc1 |].
  rewrite Ha1_eq at 1.
  eapply evstep_trans; [apply progress_evstep, Trans1_entry |].
  replace ([S0; S1]^^p1) with ([S0; S1]^^(S (p1 - 1))) by (f_equal; lia).
  replace (a1 / 2 + 3) with (S (S (S (a1 / 2)))) by lia.
  eapply evstep_trans; [apply progress_evstep, L_bounce_exec |].
  rewrite Cd_z_push10.
  rewrite HM1_eq.
  assert (Hlb1_s : W (p1 - 1) 6 = snd (L_bounce_pb p1)) by (rewrite L_bounce_pb_unfold; reflexivity).
  rewrite Hlb1_s.
  rewrite <- Hlb1_p.
  eapply evstep_trans; [exact Hkd1 |].
  change (Cd_z (fst pba) (snd pba) 2 (S1 >> S1 >> S1 >> const S0))
    with (Cd_z (fst pba) (snd pba) 1 (S1 >> S0 >> S1 >> S1 >> S1 >> const S0)).
  eapply evstep_trans; [apply progress_evstep, Hkc2 |].
  eapply evstep_trans; [apply progress_evstep, Trans1_010111_to_Ch |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_CH |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  fold bend.
  rewrite const_unfold at 1.
  eapply evstep_trans; [apply progress_evstep, CA_SH |].
  rewrite const_unfold at 1.
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  rewrite Hb1_eq at 1.
  eapply evstep_trans; [apply progress_evstep, Trans1_empty_even |].
  rewrite HE1_eq.
  apply progress_evstep, Hinit.
Qed.

Lemma Trans2_exec : forall pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) 2 (S0 >> S1 >> S1 >> const S0) -->+
  Cd_z (fst (Trans2_pb pb)) (snd (Trans2_pb pb)) 2 (S0 >> [S1; S0]^^(Trans2_E pb) *> S0 >> S1 >> S1 >> const S0) /\
  5 <= fst (Trans2_pb pb) /\
  is_W_odd (snd (Trans2_pb pb)).
Proof.
  intros pb Hp Hb.
  unfold Trans2_pb, Trans2_E, Trans2_pa2, Trans2_pbb, Trans2_pba, Trans2_pa1.
  destruct (Kc_full_all 0 (S1 >> S0 >> S0 >> S1 >> S1 >> const S0) pb Hp Hb)
    as [Hkc1 [Hp1 Ha1]].
  set (pa1 := Kc_full pb) in *.
  destruct pa1 as [p1 a1]. cbn [fst snd] in *.
  destruct Ha1 as [Ha1_eq [Ha1_ge Ha1_m3]].
  set (M1 := (a1 / 2 + 2) / 3) in *.
  assert (HM1_eq : S (S (a1 / 2)) = 3 * M1 + 0) by (unfold M1; mods; lia).
  destruct (L_bounce_pb_props p1 ltac:(lia)) as [Hlb1_p Hlb1_odd].
  destruct (Kd_loop M1 0 (const S0) (L_bounce_pb p1) ltac:(lia) Hlb1_odd)
    as [Hkd1 [Hkd1_p Hkd1_odd]].
  set (pba := Kd_iter M1 (L_bounce_pb p1)) in *.
  destruct pba as [pa ba]. cbn [fst snd] in *.
  destruct Hkd1_odd as [Hba_eq [Hba_ge Hba_m3]].
  set (M2 := (ba / 2 - 2) / 3) in *.
  assert (HM2_eq : ba / 2 - 1 = 3 * M2 + 1) by (unfold M2; mods; lia).
  destruct (L_bounce_pb_props pa ltac:(lia)) as [Hlb2_p Hlb2_odd].
  destruct (Kd_loop M2 1 (S1 >> S1 >> const S0) (L_bounce_pb pa) ltac:(lia) Hlb2_odd)
    as [Hkd2 [Hkd2_p Hkd2_odd]].
  set (pbb := Kd_iter M2 (L_bounce_pb pa)) in *.
  destruct (Kc_full_all 0 (S1 >> S1 >> const S0) pbb ltac:(lia) Hkd2_odd)
    as [Hkc2 [Hp2 Ha2]].
  set (pa2 := Kc_full pbb) in *.
  destruct pa2 as [p2 a2]. cbn [fst snd] in *.
  destruct Ha2 as [Ha2_eq [Ha2_ge Ha2_m3]].
  set (E2 := a2 / 2 + 1) in *.
  assert (HE2_eq : a2 / 2 + 2 = S E2) by (unfold E2; lia).
  destruct (Loop_init (p2 - 1) E2 (S0 >> S1 >> S1 >> const S0) ltac:(lia))
    as [Hinit [HL3_p HL3_odd]].
  replace (p2 - 1 - 1) with (p2 - 2) in Hinit, HL3_p, HL3_odd by lia.
  split; [| split; [exact HL3_p | exact HL3_odd]].
  change (Cd_z (fst pb) (snd pb) 2 (S0 >> S1 >> S1 >> const S0))
    with (Cd_z (fst pb) (snd pb) 1 (S1 >> S0 >> S0 >> S1 >> S1 >> const S0)).
  eapply progress_evstep_trans; [exact Hkc1 |].
  rewrite Ha1_eq at 1.
  eapply evstep_trans; [apply progress_evstep, Trans2_E0_to_L |].
  replace ([S0; S1]^^p1) with ([S0; S1]^^(S (p1 - 1))) by (f_equal; lia).
  replace (a1 / 2 + 4) with (S (S (S (S (a1 / 2))))) by lia.
  eapply evstep_trans; [apply progress_evstep, L_bounce_exec |].
  rewrite const_unfold at 1.
  rewrite Cd_z_push10.
  rewrite HM1_eq.
  assert (Hlb1_s : W (p1 - 1) 6 = snd (L_bounce_pb p1)) by (rewrite L_bounce_pb_unfold; reflexivity).
  rewrite Hlb1_s.
  rewrite <- Hlb1_p.
  eapply evstep_trans; [exact Hkd1 |].
  rewrite Hba_eq at 1.
  eapply evstep_trans; [apply progress_evstep, Trans2_empty_odd |].
  replace ([S0; S1]^^pa) with ([S0; S1]^^(S (pa - 1))) by (f_equal; lia).
  replace (ba / 2 + 2) with (S (S (S (ba / 2 - 1)))) by lia.
  eapply evstep_trans; [apply progress_evstep, L_bounce_exec |].
  rewrite HM2_eq.
  assert (Hlb2_s : W (pa - 1) 6 = snd (L_bounce_pb pa)) by (rewrite L_bounce_pb_unfold; reflexivity).
  rewrite Hlb2_s.
  rewrite <- Hlb2_p.
  eapply evstep_trans; [exact Hkd2 |].
  eapply evstep_trans; [apply progress_evstep, Hkc2 |].
  replace p2 with (S (p2 - 1)) at 1 by lia.
  rewrite Ha2_eq at 1.
  eapply evstep_trans; [apply progress_evstep, Trans2_011_reload |].
  rewrite HE2_eq.
  apply progress_evstep, Hinit.
Qed.

Lemma Trans3_exec : forall pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) 2 (S0 >> S0 >> S1 >> S1 >> const S0) -->+
  Cd_z (fst (Trans3_pb pb)) (snd (Trans3_pb pb)) 2 (S0 >> [S1; S0]^^(Trans3_E pb) *> const S0) /\
  5 <= fst (Trans3_pb pb) /\
  is_W_odd (snd (Trans3_pb pb)) /\
  1 <= Trans3_E pb.
Proof.
  intros pb Hp Hb.
  unfold Trans3_pb, Trans3_E, Trans3_pa1.
  destruct (Kc_full_all 0 (S1 >> S0 >> S0 >> S0 >> S1 >> S1 >> const S0) pb Hp Hb)
    as [Hkc1 [Hp1 Ha1]].
  set (pa1 := Kc_full pb) in *.
  destruct pa1 as [p1 a1]. cbn [fst snd] in *.
  destruct Ha1 as [Ha1_eq [Ha1_ge Ha1_m3]].
  set (E3 := a1 / 2 + 3) in *.
  assert (HE3_eq : a1 / 2 + 4 = S E3) by (unfold E3; lia).
  destruct (Loop_init (p1 - 1) E3 (const S0) ltac:(lia))
    as [Hinit [HL4_p HL4_odd]].
  replace (p1 - 1 - 1) with (p1 - 2) in Hinit, HL4_p, HL4_odd by lia.
  split; [| split; [exact HL4_p | split; [exact HL4_odd | unfold E3; lia]]].
  change (Cd_z (fst pb) (snd pb) 2 (S0 >> S0 >> S1 >> S1 >> const S0))
    with (Cd_z (fst pb) (snd pb) 1 (S1 >> S0 >> S0 >> S0 >> S1 >> S1 >> const S0)).
  eapply progress_evstep_trans; [exact Hkc1 |].
  replace p1 with (S (p1 - 1)) at 1 by lia.
  rewrite Ha1_eq at 1.
  eapply evstep_trans; [apply progress_evstep, Trans3_0100011_reload |].
  rewrite HE3_eq.
  apply progress_evstep, Hinit.
Qed.

Lemma Trans4_HALT_exec : forall pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) 2 (S0 >> [S1; S0]^^1 *> const S0) -->+
  c_end (fst (Trans4_pa_final pb)) (snd (Trans4_pa_final pb)).
Proof.
  intros pb Hp Hb.
  unfold Trans4_pa_final, Trans4_pbfin, Trans4_pa1.
  destruct (Kc_full_all 0 (S1 >> S0 >> S0 >> S1 >> S0 >> const S0) pb Hp Hb)
    as [Hkc1 [Hp1 Ha1]].
  set (pa1 := Kc_full pb) in *.
  destruct pa1 as [p1 a1]. cbn [fst snd] in *.
  destruct Ha1 as [Ha1_eq [Ha1_ge Ha1_m3]].
  set (M4 := (a1 / 2 - 1) / 3) in *.
  assert (HM4_eq : a1 / 2 = 3 * M4 + 1) by (unfold M4; mods; lia).
  destruct (L_bounce_pb_props p1 ltac:(lia)) as [Hlb4_p Hlb4_odd].
  destruct (Kd_loop M4 1 (S1 >> const S0) (L_bounce_pb p1) ltac:(lia) Hlb4_odd)
    as [Hkd4 [Hkd4_p Hkd4_odd]].
  set (pbfin := Kd_iter M4 (L_bounce_pb p1)) in *.
  destruct (Kc_full_all 0 (S1 >> const S0) pbfin ltac:(lia) Hkd4_odd)
    as [Hkc2 [Hp2 Ha2]].
  change (Cd_z (fst pb) (snd pb) 2 (S0 >> [S1; S0]^^1 *> const S0))
    with (Cd_z (fst pb) (snd pb) 1 (S1 >> S0 >> S0 >> S1 >> S0 >> const S0)).
  eapply progress_evstep_trans; [exact Hkc1 |].
  rewrite Ha1_eq at 1.
  eapply evstep_trans; [apply progress_evstep, Trans4_E1_to_L |].
  replace ([S0; S1]^^p1) with ([S0; S1]^^(S (p1 - 1))) by (f_equal; lia).
  replace (a1 / 2 + 3) with (S (S (S (a1 / 2)))) by lia.
  eapply evstep_trans; [apply progress_evstep, L_bounce_exec |].
  rewrite HM4_eq.
  assert (Hlb4_s : W (p1 - 1) 6 = snd (L_bounce_pb p1)) by (rewrite L_bounce_pb_unfold; reflexivity).
  rewrite Hlb4_s.
  rewrite <- Hlb4_p.
  eapply evstep_trans; [exact Hkd4 |].
  eapply evstep_trans; [apply progress_evstep, Hkc2 |].
  apply progress_evstep, Trans4_HALT.
Qed.

Opaque E0 pb_L1_0 Trans1_pb Trans1_E Trans2_pb Trans2_E Trans3_pb Trans3_E Trans4_pa_final.
Strategy opaque [E0 pb_L1_0 Trans1_pb Trans1_E Trans2_pb Trans2_E Trans3_pb Trans3_E Trans4_pa_final].

Definition pb_L1_end : nat * nat := iter E0 Outer_step pb_L1_0.
Definition E1 : nat := Trans1_E pb_L1_end.
Definition pb_L2_0 : nat * nat := Trans1_pb pb_L1_end.
Definition pb_L2_end : nat * nat := iter E1 Outer_step pb_L2_0.
Definition E2 : nat := Trans2_E pb_L2_end.
Definition pb_L3_0 : nat * nat := Trans2_pb pb_L2_end.
Definition pb_L3_end : nat * nat := iter E2 Outer_step pb_L3_0.
Definition E3 : nat := Trans3_E pb_L3_end.
Definition pb_L4_0 : nat * nat := Trans3_pb pb_L3_end.
Definition pb_L4_end : nat * nat := iter (E3 - 1) Outer_step pb_L4_0.
Definition pa_final : nat * nat := Trans4_pa_final pb_L4_end.
Definition N_final : nat := fst pa_final + snd pa_final + 7.

Lemma run_to_end :
  c0_core -->* c_end (fst pa_final) (snd pa_final).
Proof.
  destruct Boot_to_Loop1 as [Hboot [Hp1 Hb1]].
  destruct (Outer_loop E0 (S1 >> S1 >> S1 >> S1 >> const S0) pb_L1_0 Hp1 Hb1)
    as [HL1 [Hp1e Hb1e]].
  fold pb_L1_end in HL1, Hp1e, Hb1e.
  destruct (Trans1_exec pb_L1_end Hp1e Hb1e) as [HT1 [Hp2 Hb2]].
  fold E1 pb_L2_0 in HT1, Hp2, Hb2.
  destruct (Outer_loop E1 (S1 >> S1 >> const S0) pb_L2_0 Hp2 Hb2)
    as [HL2 [Hp2e Hb2e]].
  fold pb_L2_end in HL2, Hp2e, Hb2e.
  destruct (Trans2_exec pb_L2_end Hp2e Hb2e) as [HT2 [Hp3 Hb3]].
  fold E2 pb_L3_0 in HT2, Hp3, Hb3.
  destruct (Outer_loop E2 (S0 >> S1 >> S1 >> const S0) pb_L3_0 Hp3 Hb3)
    as [HL3 [Hp3e Hb3e]].
  fold pb_L3_end in HL3, Hp3e, Hb3e.
  destruct (Trans3_exec pb_L3_end Hp3e Hb3e) as [HT3 [Hp4 [Hb4 HE3_ge]]].
  fold E3 pb_L4_0 in HT3, Hp4, Hb4, HE3_ge.
  destruct (Outer_loop (E3 - 1) ([S1; S0]^^1 *> const S0) pb_L4_0 Hp4 Hb4)
    as [HL4 [Hp4e Hb4e]].
  fold pb_L4_end in HL4, Hp4e, Hb4e.
  pose proof (Trans4_HALT_exec pb_L4_end Hp4e Hb4e) as HT4.
  fold pa_final in HT4.
  eapply evstep_trans; [exact Hboot |].
  eapply evstep_trans; [exact HL1 |].
  eapply evstep_trans; [apply progress_evstep, HT1 |].
  eapply evstep_trans; [exact HL2 |].
  eapply evstep_trans; [apply progress_evstep, HT2 |].
  eapply evstep_trans; [exact HL3 |].
  eapply evstep_trans; [apply progress_evstep, HT3 |].
  replace E3 with ((E3 - 1) + 1) by (clear - HE3_ge; lia).
  rewrite lpow_add, Str_app_assoc.
  eapply evstep_trans; [exact HL4 |].
  apply progress_evstep, HT4.
Qed.

Theorem halt : halts tm c0_core.
Proof.
  destruct (with_counter run_to_end) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. apply c_end_halted.
Qed.

(** ** Exact 1-count and Strict First-Visit TNF Isomorphism *)

Definition sym_val (s : Sym) : nat :=
  match s with S0 => 0 | S1 => 1 end.

Fixpoint count1 (xs : list Sym) : nat :=
  match xs with [] => 0 | x :: t => sym_val x + count1 t end.

Definition ones (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl; [reflexivity | rewrite IHxs; lia]. Qed.

Lemma count1_pow : forall xs n, count1 (xs ^^ n) = n * count1 xs.
Proof. induction n; simpl; [reflexivity | rewrite count1_app, IHn; lia]. Qed.

Lemma ones_c_end : forall p a, ones (c_end p a) (p + a + 7).
Proof.
  intros p a.
  eexists. exists ([S1]^^(a + 7) ++ [S0; S1]^^p), (@nil Sym), S0.
  split.
  - unfold c_end. rewrite !Str_app_assoc. cbn [Str_app Streams.hd Streams.tl]. reflexivity.
  - rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
Qed.

Theorem score_exact :
  exists c, c0_core -->* c /\ halted tm c /\ ones c N_final.
Proof.
  exists (c_end (fst pa_final) (snd pa_final)).
  split; [exact run_to_end |].
  split; [apply c_end_halted |].
  apply ones_c_end.
Qed.

Definition perm_f (q : Q) : Q :=
  match q with
  | A => B | B => C | C => M | D => N | E => E | F => I | G => A
  | H => K | I => D | J => H | K => L | L => F | M => J | N => G
  end.

Lemma tm_perm_tnf : Perm tm tm_tnf perm_f.
Proof.
  split.
  - intros [] [] H; inversion H; reflexivity.
  - intros [] [] s' d q' H; inversion H; subst; reflexivity.
Qed.

Lemma perm_evstep : forall tm1 tm2 g,
  Perm tm1 tm2 g -> forall c c',
  c -[ tm1 ]->* c' ->
  (g (fst c), snd c) -[ tm2 ]->* (g (fst c'), snd c').
Proof.
  intros tm1 tm2 g HP c c' H.
  induction H as [[q t] | [q t] [q1 t1] [q2 t2] H1 _ IH]; cbn [fst snd] in *.
  - apply evstep_refl.
  - eapply evstep_step; [eapply perm_step; eauto | exact IH].
Qed.

Theorem halt_tnf : halts tm_tnf c0.
Proof.
  change c0 with (perm_f G;; tape0).
  exact (perm_halts tm tm_tnf perm_f G tape0 tm_perm_tnf halt).
Qed.

Theorem score_exact_tnf :
  exists c, c0 -[ tm_tnf ]->* c /\ halted tm_tnf c /\ ones c N_final.
Proof.
  destruct score_exact as [[q t] [Hrun [Hhalt Hones]]].
  exists (perm_f q, t).
  split.
  - exact (perm_evstep tm tm_tnf perm_f tm_perm_tnf c0_core (q, t) Hrun).
  - split.
    + exact (perm_halted tm tm_tnf perm_f q t tm_perm_tnf Hhalt).
    + destruct Hones as [q' [L [R [s [Heq Hn]]]]].
      inversion Heq; subst. exists (perm_f q'), L, R, s. auto.
Qed.


(** ** Standard Wainer Fast-Growing Hierarchy up to omega + 3 and Sigma(14) Lower Bound *)

Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | O => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.
Definition f_omega1 (n : nat) : nat := iter n f_omega n.
Definition f_omega2 (n : nat) : nat := iter n f_omega1 n.
Definition f_omega3 (n : nat) : nat := iter n f_omega2 n.

Lemma iter_mono_x : forall g, (forall a b, a <= b -> g a <= g b) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; auto. Qed.

Lemma iter_ge : forall g, (forall a, a <= g a) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl.
  - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_mono_n : forall g, (forall a, a <= g a) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite iter_add. apply iter_ge. exact Hg.
Qed.

Lemma iter_lin1 : forall g, (forall a, 1 <= a -> a + 1 <= g a) -> forall n x, 1 <= x -> x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros x Hx; simpl.
  - lia.
  - specialize (IHn x Hx). specialize (Hg (iter n g x) ltac:(lia)). lia.
Qed.

Lemma iter_dom : forall K g h, (forall n z, K * n <= z -> K * g n <= h z) ->
  forall m n z, K * n <= z -> K * iter m g n <= iter m h z.
Proof. intros K g h Hd. induction m; intros n z Hz; simpl; auto. Qed.

Lemma f_S : forall k n, f (S k) n = iter n (f k) n.
Proof. reflexivity. Qed.

Lemma f_props : forall k, (forall n, n <= f k n) /\ (forall a b, a <= b -> f k a <= f k b).
Proof.
  induction k as [| k [Hid Hmono]].
  - split; intros; simpl; lia.
  - split.
    + intros n. rewrite f_S. apply iter_ge. exact Hid.
    + intros a b Hab. rewrite !f_S. transitivity (iter a (f k) b).
      * apply iter_mono_x; assumption.
      * apply iter_mono_n; assumption.
Qed.

Lemma f_id : forall k n, n <= f k n.
Proof. intros. apply f_props. Qed.

Lemma f_mono : forall k a b, a <= b -> f k a <= f k b.
Proof. intros. apply f_props. assumption. Qed.

Lemma f_gt : forall k n, 1 <= n -> n < f k n.
Proof.
  induction k; intros n Hn.
  - simpl. lia.
  - rewrite f_S. destruct n as [| n']; [lia |].
    simpl. pose proof (iter_ge (f k) (f_id k) n' (S n')).
    specialize (IHk (iter n' (f k) (S n')) ltac:(lia)). lia.
Qed.

Lemma f_level : forall k n, 1 <= n -> f k n <= f (S k) n.
Proof.
  intros k n Hn. rewrite f_S. destruct n as [| n']; [lia |].
  rewrite iter_S'. apply iter_ge. apply f_id.
Qed.

Lemma f_level_mono : forall d k n, 1 <= n -> f k n <= f (d + k) n.
Proof.
  induction d; intros k n Hn.
  - reflexivity.
  - specialize (IHd k n Hn). pose proof (f_level (d + k) n Hn).
    change (S d + k) with (S (d + k)). lia.
Qed.

Lemma iter_succ_add : forall n x, iter n S x = n + x.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma f1 : forall n, f 1 n = 2 * n.
Proof. intros. rewrite f_S, iter_succ_add. lia. Qed.

Lemma f_dbl : forall k n, 1 <= k -> 2 * n <= f k n.
Proof.
  intros k n Hk. destruct n as [| n'].
  - lia.
  - rewrite <- f1. replace k with ((k - 1) + 1) by lia. apply f_level_mono. lia.
Qed.

Lemma f_omega_id : forall n, n <= f_omega n.
Proof. intros n. unfold f_omega. apply f_id. Qed.

Lemma f_omega_dbl : forall n, 1 <= n -> 2 * n <= f_omega n.
Proof. intros n Hn. unfold f_omega. apply f_dbl. exact Hn. Qed.

Lemma f_omega_mono : forall a b, a <= b -> f_omega a <= f_omega b.
Proof.
  intros [| a'] b Hab.
  - destruct b as [| b'].
    + reflexivity.
    + change (f_omega 0) with 1. pose proof (f_omega_id (S b')). lia.
  - unfold f_omega.
    pose proof (f_level_mono (b - S a') (S a') (S a') ltac:(lia)) as L1.
    replace (b - S a' + S a') with b in L1 by lia.
    pose proof (f_mono b (S a') b Hab). lia.
Qed.

Lemma f_omega1_id : forall n, n <= f_omega1 n.
Proof. intros n. unfold f_omega1. apply iter_ge, f_omega_id. Qed.

Lemma f_omega1_dbl : forall n, 1 <= n -> 2 * n <= f_omega1 n.
Proof.
  intros [| n'] Hn; [lia |].
  unfold f_omega1. cbn [iter].
  pose proof (iter_ge f_omega f_omega_id n' (S n')).
  pose proof (f_omega_dbl (iter n' f_omega (S n')) ltac:(lia)). lia.
Qed.

Lemma f_omega1_ge2 : forall n, 1 <= n -> 2 <= f_omega1 n.
Proof. intros n Hn. pose proof (f_omega1_dbl n Hn). lia. Qed.

Lemma f_omega1_mono : forall a b, a <= b -> f_omega1 a <= f_omega1 b.
Proof.
  intros a b Hab. unfold f_omega1.
  transitivity (iter a f_omega b).
  - apply iter_mono_x; [apply f_omega_mono | exact Hab].
  - apply iter_mono_n; [apply f_omega_id | exact Hab].
Qed.

Lemma f_omega2_id : forall n, n <= f_omega2 n.
Proof. intros n. unfold f_omega2. apply iter_ge, f_omega1_id. Qed.

Lemma f_omega2_mono : forall a b, a <= b -> f_omega2 a <= f_omega2 b.
Proof.
  intros a b Hab. unfold f_omega2.
  transitivity (iter a f_omega1 b).
  - apply iter_mono_x; [apply f_omega1_mono | exact Hab].
  - apply iter_mono_n; [apply f_omega1_id | exact Hab].
Qed.

Lemma f_omega3_id : forall n, n <= f_omega3 n.
Proof. intros n. unfold f_omega3. apply iter_ge, f_omega2_id. Qed.

Lemma f_omega3_mono : forall a b, a <= b -> f_omega3 a <= f_omega3 b.
Proof.
  intros a b Hab. unfold f_omega3.
  transitivity (iter a f_omega2 b).
  - apply iter_mono_x; [apply f_omega2_mono | exact Hab].
  - apply iter_mono_n; [apply f_omega2_id | exact Hab].
Qed.

Lemma W_S' : forall j b, W (S j) b = iter b (W j) (W j 2).
Proof. intros j b. rewrite W_S, iter_S'. reflexivity. Qed.

Lemma W_S_2 : forall j, W (S j) 2 = W j (W j (W j 2)).
Proof. intros j. rewrite W_S. reflexivity. Qed.

Lemma pow2_ge : forall j, j + 2 <= 2 ^ (j + 1).
Proof.
  induction j.
  - simpl. lia.
  - change (S j + 1) with (S (j + 1)). rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma W_bound_all : forall j,
  (forall n z, 2 ^ (j + 1) * n <= z -> 2 ^ (j + 1) * f (S j) n <= W (S j) z) /\
  2 ^ (j + 2) * (j + 1) <= W (S j) 2.
Proof.
  induction j as [| j [Hw Hx]].
  - split.
    + intros n z Hz. rewrite W_1, f1. simpl (2 ^ (0 + 1)) in *. lia.
    + rewrite W_1. simpl. lia.
  - pose proof (pow2_ge j) as HKj.
    set (K := 2 ^ (j + 1)) in *.
    assert (HK1 : 2 ^ (S j + 1) = 2 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    assert (HK2 : 2 ^ (j + 2) = 2 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    assert (HK3 : 2 ^ (S j + 2) = 4 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    rewrite HK2 in Hx.
    assert (HX1 : K * 1 <= W (S j) 2) by nia.
    split.
    + intros n y Hy. rewrite HK1 in *. rewrite W_S', f_S.
      destruct n as [| n']. { cbn [iter]. lia. }
      set (n := S n') in *.
      assert (Hm : 2 * n + 1 <= y) by nia.
      pose proof (iter_dom K (f (S j)) (W (S j)) Hw y 1 (W (S j) 2) HX1) as Hd.
      assert (Hc : 2 * iter n (f (S j)) n <= iter y (f (S j)) 1).
      { transitivity (iter (2 * n + 1) (f (S j)) 1).
        2:{ apply iter_mono_n; [apply f_id | exact Hm]. }
        replace (2 * n + 1) with (1 + (n + n)) by lia. rewrite !iter_add.
        change (iter 1 (f (S j)) ?z) with (f (S j) z).
        pose proof (iter_lin1 (f (S j)) ltac:(intros a Ha; pose proof (f_gt (S j) a Ha); lia) n 1 ltac:(lia)).
        pose proof (iter_mono_x (f (S j)) (f_mono (S j)) n n (iter n (f (S j)) 1) ltac:(lia)).
        pose proof (f_dbl (S j) (iter n (f (S j)) (iter n (f (S j)) 1)) ltac:(lia)).
        lia. }
      nia.
    + rewrite HK3, W_S_2.
      pose proof (Hw (2 * (j + 1)) (W (S j) 2) ltac:(nia)) as H1.
      pose proof (f_dbl (S j) (2 * (j + 1)) ltac:(lia)) as H2.
      pose proof (Hw (4 * (j + 1)) (W (S j) (W (S j) 2)) ltac:(nia)) as H3.
      pose proof (f_dbl (S j) (4 * (j + 1)) ltac:(lia)) as H4.
      nia.
Qed.

Lemma W_omega_bound0 : forall m,
  2 * f_omega (S m) + 3 <= W (S (S m)) 2.
Proof.
  intros m.
  rewrite W_S_2.
  destruct (W_bound_all m) as [Hwb Hx].
  assert (H1 : 2 ^ (m + 1) * (2 * (m + 1)) <= W (S m) 2).
  { replace (m + 2) with (m + 1 + 1) in Hx by lia.
    rewrite Nat.pow_add_r in Hx. simpl (2 ^ 1) in Hx. nia. }
  pose proof (Hwb (2 * (m + 1)) (W (S m) 2) H1) as H2.
  pose proof (W_grow (S m) (W (S m) (W (S m) 2))) as H3.
  assert (H4 : f (S m) (S m) <= f (S m) (2 * (m + 1))) by (apply f_mono; lia).
  assert (H5 : 2 <= 2 ^ (m + 1)) by (pose proof (pow2_ge m); lia).
  unfold f_omega.
  set (P := 2 ^ (m + 1)) in *; set (F1 := f (S m) (S m)) in *;
  set (F2 := f (S m) (2 * (m + 1))) in *; set (Z := W (S m) (W (S m) (W (S m) 2))) in *.
  nia.
Qed.

Lemma W_omega_bound : forall m,
  4 * f_omega (S m) + 4 <= W (S (S (S m))) 1.
Proof.
  intros m.
  rewrite W_S. cbn [iter].
  pose proof (W_omega_bound0 m) as H0.
  set (Z := W (S (S m)) 2) in *; clearbody Z.
  rewrite W_S.
  pose proof (iter_lin3 (W (S m)) (W_grow (S m)) (S Z) 2).
  lia.
Qed.

Opaque f f_omega f_omega1 f_omega2 f_omega3.
Strategy opaque [f f_omega f_omega1 f_omega2 f_omega3].

Lemma W5_1_ge_fw4 : 16 * f_omega 4 <= W 5 1.
Proof.
  destruct (W_bound_all 3) as [Hw4 Hx4].
  simpl (2 ^ (3 + 1)) in Hw4.
  simpl (2 ^ (3 + 2)) in Hx4.
  assert (Harg : 16 * 4 <= W 4 2) by (clear - Hx4; lia).
  pose proof (Hw4 4 (W 4 2) Harg) as Hstep.
  assert (Hw5 : W 5 1 = W 4 (W 4 2)) by (rewrite W_S; reflexivity).
  rewrite <- Hw5 in Hstep.
  Transparent f_omega. unfold f_omega. Opaque f_omega.
  exact Hstep.
Qed.

Lemma E0_ge_fw4 : f_omega 4 <= E0.
Proof.
  Transparent E0. unfold E0. Opaque E0.
  pose proof W5_1_ge_fw4 as Hw5.
  pose proof (f_omega_dbl 4 ltac:(lia)) as Hdbl.
  set (F := f_omega 4) in *; set (X := W 5 1) in *; clearbody F X.
  mods; lia.
Qed.

Lemma W6_3_ge_fw4 : f_omega 4 + 1 <= W 6 3 / 2.
Proof.
  pose proof W5_1_ge_fw4 as Hw5.
  pose proof (f_omega_dbl 4 ltac:(lia)) as Hdbl.
  assert (Hle : W 5 1 <= W 6 3).
  { rewrite (W_S 5 3), iter_S'.
    pose proof (iter_lin3 (W 5) (W_grow 5) 3 (W 5 2)) as H1.
    assert (H52 : W 5 2 = W 4 (W 5 1)) by (rewrite (W_S 4 2), (W_S 4 1); reflexivity).
    pose proof (W_grow 4 (W 5 1)) as H2.
    rewrite <- H52 in H2.
    set (a := W 5 1) in *; set (b := W 5 2) in *; set (c := iter 3 (W 5) b) in *.
    clearbody a b c. lia. }
  set (F := f_omega 4) in *; set (X := W 6 3) in *; set (Y := W 5 1) in *.
  clearbody F X Y.
  mods; lia.
Qed.

(** ** Domination across Kc, Kc_full, Kd_step, Kd_iter, L_bounce, Outer_loop, and 4 Stages *)

Lemma Kc_dom1 : forall pa,
  4 <= fst pa -> 6 <= snd pa ->
  fst pa + 3 <= fst (Kc pa) /\
  fst pa + snd pa / 2 <= fst (Kc pa) /\
  4 * f_omega (fst pa - 3) + 4 <= snd (Kc pa).
Proof.
  intros [p a] Hp Ha. rewrite Kc_unfold. cbn [fst snd] in *.
  destruct p as [| [| [| [| m]]]]; try lia.
  replace (S (S (S (S m))) - 1) with (S (S (S m))) by lia.
  replace (S (S (S (S m))) - 3) with (S m) by lia.
  pose proof (W_omega_bound m) as Hw.
  set (z := f_omega (S m)) in *; set (w := W (S (S (S m))) 1) in *; clearbody z w.
  assert (Hdiv : 3 <= a / 2) by (mods; lia).
  split; [lia | split; lia].
Qed.

Lemma Kc_dom2 : forall pa,
  4 <= fst pa -> 6 <= snd pa ->
  4 <= fst (iter 2 Kc pa) /\
  6 <= snd (iter 2 Kc pa) /\
  f_omega (fst pa - 3) + 4 <= fst (iter 2 Kc pa).
Proof.
  intros pa Hp Ha. cbn [iter].
  destruct (Kc_dom1 pa Hp Ha) as [Hp1 [_ Ha1]].
  pose proof (f_omega_id (fst pa - 3)) as Hid.
  assert (Ha1' : 6 <= snd (Kc pa)) by lia.
  destruct (Kc_dom1 (Kc pa) ltac:(lia) Ha1') as [Hp2 [Hdiv2 Ha2]].
  pose proof (f_omega_id (fst (Kc pa) - 3)) as Hid2.
  assert (Hq : 2 * f_omega (fst pa - 3) + 2 <= snd (Kc pa) / 2)
    by (set (z := f_omega (fst pa - 3)) in *; set (s := snd (Kc pa)) in *; clearbody z s; mods; lia).
  split; [lia | split; [lia | lia]].
Qed.

Lemma Kc_dom_even : forall k pa,
  4 <= fst pa -> 6 <= snd pa ->
  4 <= fst (iter (2 * k) Kc pa) /\
  6 <= snd (iter (2 * k) Kc pa) /\
  iter k f_omega (fst pa - 3) <= fst (iter (2 * k) Kc pa) - 3.
Proof.
  induction k as [| k IHk]; intros pa Hp Ha.
  - change (2 * 0) with 0. cbn [iter]. split; [lia | split; [lia | lia]].
  - replace (2 * S k) with (2 + 2 * k) by lia.
    rewrite iter_add.
    change (iter (S k) f_omega (fst pa - 3)) with (f_omega (iter k f_omega (fst pa - 3))).
    destruct (IHk pa Hp Ha) as [Hp1 [Ha1 Hdom1]].
    destruct (Kc_dom2 (iter (2 * k) Kc pa) Hp1 Ha1) as [Hp2 [Ha2 Hdom2]].
    pose proof (f_omega_mono _ _ Hdom1).
    split; [exact Hp2 | split; [exact Ha2 | lia]].
Qed.

Lemma Kc_dom_any : forall c' pa,
  4 <= fst pa -> 6 <= snd pa ->
  4 <= fst (iter c' Kc pa) /\
  6 <= snd (iter c' Kc pa) /\
  iter (c' / 2) f_omega (fst pa - 3) <= fst (iter c' Kc pa) - 3.
Proof.
  intros c' pa Hp Ha.
  assert (Hc : c' = 2 * (c' / 2) \/ c' = 1 + 2 * (c' / 2)) by (mods; lia).
  set (k := c' / 2) in *.
  destruct Hc as [Hev | Hodd].
  - rewrite Hev. apply Kc_dom_even; assumption.
  - rewrite Hodd. rewrite iter_add. cbn [iter].
    destruct (Kc_dom_even k pa Hp Ha) as [Hp1 [Ha1 Hdom1]].
    destruct (Kc_dom1 (iter (2 * k) Kc pa) Hp1 Ha1) as [Hp2 [_ Ha2]].
    pose proof (f_omega_id (fst (iter (2 * k) Kc pa) - 3)).
    split; [lia | split; [lia | lia]].
Qed.

Definition ok_pb (n : nat) (pb : nat * nat) : Prop :=
  n + 4 <= fst pb /\ 4 * n + 2 <= snd pb.

Definition ok_pa (n : nat) (pa : nat * nat) : Prop :=
  n + 6 <= fst pa /\ 6 * n + 8 <= snd pa.

Lemma ok_pb_mono : forall m n pb,
  m <= n -> ok_pb n pb -> ok_pb m pb.
Proof. intros m n pb Hmn [H1 H2]. split; lia. Qed.

Lemma ok_pa_mono : forall m n pa,
  m <= n -> ok_pa n pa -> ok_pa m pa.
Proof. intros m n pa Hmn [H1 H2]. split; lia. Qed.

Lemma Kc_full_dom : forall n pb,
  1 <= n -> ok_pb n pb -> ok_pa (f_omega1 n) (Kc_full pb).
Proof.
  intros n [p b] Hn [Hp Hb]. unfold ok_pb, ok_pa in *. cbn [fst snd] in *.
  rewrite Kc_full_unfold.
  assert (Hb_ge : 1 <= b / 2) by (mods; lia).
  replace (b / 2) with (S (b / 2 - 1)) by lia.
  cbn [iter].
  pose proof (W_grow (p - 1) 3) as Hwg0.
  destruct (Kc_dom_any (b / 2 - 1) (p - 1, W (p - 1) 3) ltac:(cbn; lia) ltac:(cbn; lia))
    as [Hp1 [Ha1 Hdom1]].
  cbn [fst snd] in Hdom1. replace (p - 1 - 3) with (p - 4) in Hdom1 by lia.
  set (pa' := iter (b / 2 - 1) Kc (p - 1, W (p - 1) 3)) in *.
  destruct (Kc_dom1 pa' Hp1 Ha1) as [Hp2 [_ Ha2]].
  assert (Hdiv : n <= (b / 2 - 1) / 2) by (mods; lia).
  assert (H1 : f_omega1 n <= iter ((b / 2 - 1) / 2) f_omega (p - 4)).
  { Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
    transitivity (iter n f_omega (p - 4)).
    - apply iter_mono_x; [apply f_omega_mono | lia].
    - apply iter_mono_n; [apply f_omega_id | exact Hdiv]. }
  pose proof (f_omega1_ge2 n Hn) as Hge2.
  pose proof (f_omega1_id n) as Hid1.
  pose proof (f_omega_dbl (fst pa' - 3) ltac:(lia)) as Hdbl.
  split; lia.
Qed.

Lemma Kd_step_dom : forall n pb,
  1 <= n -> ok_pb n pb -> ok_pb (f_omega1 n) (Kd_step pb).
Proof.
  intros n pb Hn Hok.
  rewrite Kd_step_unfold.
  destruct (Kc_full_dom n pb Hn Hok) as [Hp' Ha'].
  set (pa' := Kc_full pb) in *.
  destruct pa' as [p' a']. cbn [fst snd] in *.
  pose proof (W_grow p' (a' + 4)) as Hwg.
  unfold ok_pb. cbn [fst snd].
  split; lia.
Qed.

Lemma Kd_iter_dom : forall m n pb,
  1 <= n -> ok_pb n pb -> ok_pb (iter m f_omega1 n) (Kd_iter m pb).
Proof.
  intros m n pb. rewrite Kd_iter_unfold.
  induction m as [| m IHm]; intros Hn Hok.
  - cbn [iter]. exact Hok.
  - cbn [iter]. apply Kd_step_dom.
    + pose proof (iter_ge f_omega1 f_omega1_id m n). lia.
    + apply IHm; assumption.
Qed.

Lemma L_bounce_pb_dom : forall n p,
  1 <= n -> n + 5 <= p -> ok_pb n (L_bounce_pb p).
Proof.
  intros n p Hn Hp.
  rewrite L_bounce_pb_unfold. unfold ok_pb. cbn [fst snd].
  destruct (p - 1) as [| [| [| [| m]]]] eqn:Epm; try lia.
  pose proof (W_omega_bound0 (S m)) as Hw0.
  pose proof (f_omega_dbl (S (S m)) ltac:(lia)) as Hdbl.
  assert (Hw6 : W (S (S (S m))) 2 + 18 <= W (S (S (S (S m)))) 6).
  { rewrite W_S, iter_S'.
    exact (iter_lin3 (W (S (S (S m)))) (W_grow (S (S (S m)))) 6 (W (S (S (S m))) 2)). }
  split; lia.
Qed.

Lemma Outer_step_dom : forall n pb,
  1 <= n -> ok_pb n pb -> ok_pb (f_omega2 n) (Outer_step pb).
Proof.
  intros n pb Hn Hok.
  rewrite Outer_step_unfold.
  destruct (Kc_full_dom n pb Hn Hok) as [Hp1 Ha1].
  destruct (Kc_full pb) as [p1 a1]. cbn [fst snd] in *.
  pose proof (f_omega1_id n) as Hf1_id.
  pose proof (L_bounce_pb_dom n p1 Hn ltac:(lia)) as Hlb.
  assert (Hm : n <= (a1 / 2 - 1) / 3) by (mods; lia).
  pose proof (Kd_iter_dom ((a1 / 2 - 1) / 3) n (L_bounce_pb p1) Hn Hlb) as Hkd.
  eapply ok_pb_mono; [| exact Hkd].
  Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
  apply iter_mono_n; [apply f_omega1_id | exact Hm].
Qed.

Lemma Outer_loop_dom : forall E n pb,
  1 <= n -> ok_pb n pb -> ok_pb (iter E f_omega2 n) (iter E Outer_step pb).
Proof.
  induction E as [| E IHE]; intros n pb Hn Hok.
  - cbn [iter]. exact Hok.
  - cbn [iter].
    pose proof (IHE n pb Hn Hok) as H1.
    pose proof (iter_ge f_omega2 f_omega2_id E n) as Hge.
    exact (Outer_step_dom (iter E f_omega2 n) (iter E Outer_step pb) ltac:(lia) H1).
Qed.

Lemma Outer_loop_fw3 : forall E n pb,
  1 <= n -> n <= E -> ok_pb n pb -> ok_pb (f_omega3 n) (iter E Outer_step pb).
Proof.
  intros E n pb Hn Hle Hok.
  eapply ok_pb_mono; [| exact (Outer_loop_dom E n pb Hn Hok)].
  Transparent f_omega3. unfold f_omega3. Opaque f_omega3.
  apply iter_mono_n; [apply f_omega2_id | exact Hle].
Qed.

Lemma Trans1_dom : forall n pb,
  1 <= n -> ok_pb n pb ->
  n <= Trans1_E pb /\ ok_pb n (Trans1_pb pb).
Proof.
  intros n pb Hn Hok.
  Transparent Trans1_pb Trans1_E.
  unfold Trans1_pb, Trans1_E, Trans1_b_end, Trans1_pa2, Trans1_pba, Trans1_pa1.
  Opaque Trans1_pb Trans1_E.
  destruct (Kc_full_dom n pb Hn Hok) as [Hp1 Ha1].
  destruct (Kc_full pb) as [p1 a1]. cbn [fst snd] in *.
  pose proof (f_omega1_id n) as Hf1.
  pose proof (L_bounce_pb_dom n p1 Hn ltac:(lia)) as Hlb1.
  pose proof (Kd_iter_dom ((a1 / 2 - 1) / 3) n (L_bounce_pb p1) Hn Hlb1) as Hkd1.
  assert (Hpba : ok_pb n (Kd_iter ((a1 / 2 - 1) / 3) (L_bounce_pb p1)))
    by (eapply ok_pb_mono; [apply iter_ge, f_omega1_id | exact Hkd1]).
  destruct (Kc_full_dom n _ Hn Hpba) as [Hp2 Ha2].
  destruct (Kc_full (Kd_iter ((a1 / 2 - 1) / 3) (L_bounce_pb p1))) as [p2 a2].
  cbn [fst snd] in *.
  pose proof (W_grow p2 (a2 + 4)) as Hwg1.
  pose proof (W_grow p2 (W p2 (a2 + 4))) as Hwg2.
  split.
  - set (w := W p2 (W p2 (a2 + 4))) in *; clearbody w. mods; lia.
  - apply L_bounce_pb_dom; [exact Hn | lia].
Qed.

Lemma Trans2_dom : forall n pb,
  1 <= n -> ok_pb n pb ->
  n <= Trans2_E pb /\ ok_pb n (Trans2_pb pb).
Proof.
  intros n pb Hn Hok.
  Transparent Trans2_pb Trans2_E.
  unfold Trans2_pb, Trans2_E, Trans2_pa2, Trans2_pbb, Trans2_pba, Trans2_pa1.
  Opaque Trans2_pb Trans2_E.
  destruct (Kc_full_dom n pb Hn Hok) as [Hp1 Ha1].
  destruct (Kc_full pb) as [p1 a1]. cbn [fst snd] in *.
  pose proof (f_omega1_dbl n Hn) as Hf1_dbl.
  assert (Hf1_pos : 1 <= f_omega1 n) by lia.
  pose proof (L_bounce_pb_dom (f_omega1 n) p1 Hf1_pos ltac:(lia)) as Hlb1.
  pose proof (Kd_iter_dom ((a1 / 2 + 2) / 3) (f_omega1 n) (L_bounce_pb p1) Hf1_pos Hlb1) as Hkd1.
  assert (Hpba : ok_pb (f_omega1 n) (Kd_iter ((a1 / 2 + 2) / 3) (L_bounce_pb p1)))
    by (eapply ok_pb_mono; [apply iter_ge, f_omega1_id | exact Hkd1]).
  destruct (Kd_iter ((a1 / 2 + 2) / 3) (L_bounce_pb p1)) as [pa ba].
  destruct Hpba as [Hpa Hba]. cbn [fst snd] in *.
  pose proof (L_bounce_pb_dom n pa Hn ltac:(lia)) as Hlb2.
  pose proof (Kd_iter_dom ((ba / 2 - 2) / 3) n (L_bounce_pb pa) Hn Hlb2) as Hkd2.
  assert (Hpbb : ok_pb n (Kd_iter ((ba / 2 - 2) / 3) (L_bounce_pb pa)))
    by (eapply ok_pb_mono; [apply iter_ge, f_omega1_id | exact Hkd2]).
  destruct (Kc_full_dom n _ Hn Hpbb) as [Hp2 Ha2].
  destruct (Kc_full (Kd_iter ((ba / 2 - 2) / 3) (L_bounce_pb pa))) as [p2 a2].
  cbn [fst snd] in *.
  split.
  - mods; lia.
  - apply L_bounce_pb_dom; [exact Hn | lia].
Qed.

Lemma Trans3_dom : forall n pb,
  1 <= n -> ok_pb n pb ->
  n <= Trans3_E pb - 1 /\ ok_pb n (Trans3_pb pb).
Proof.
  intros n pb Hn Hok.
  Transparent Trans3_pb Trans3_E.
  unfold Trans3_pb, Trans3_E, Trans3_pa1.
  Opaque Trans3_pb Trans3_E.
  destruct (Kc_full_dom n pb Hn Hok) as [Hp1 Ha1].
  pose proof (f_omega1_dbl n Hn) as Hf1_dbl.
  split.
  - mods; lia.
  - apply L_bounce_pb_dom; [exact Hn | lia].
Qed.

Lemma Trans4_dom : forall n pb,
  1 <= n -> ok_pb n pb ->
  ok_pa n (Trans4_pa_final pb).
Proof.
  intros n pb Hn Hok.
  Transparent Trans4_pa_final.
  unfold Trans4_pa_final, Trans4_pbfin, Trans4_pa1.
  Opaque Trans4_pa_final.
  destruct (Kc_full_dom n pb Hn Hok) as [Hp1 Ha1].
  destruct (Kc_full pb) as [p1 a1]. cbn [fst snd] in *.
  pose proof (f_omega1_id n) as Hf1.
  pose proof (L_bounce_pb_dom n p1 Hn ltac:(lia)) as Hlb.
  pose proof (Kd_iter_dom ((a1 / 2 - 1) / 3) n (L_bounce_pb p1) Hn Hlb) as Hkd.
  assert (Hpbfin : ok_pb n (Kd_iter ((a1 / 2 - 1) / 3) (L_bounce_pb p1)))
    by (eapply ok_pb_mono; [apply iter_ge, f_omega1_id | exact Hkd]).
  eapply ok_pa_mono; [apply f_omega1_id | exact (Kc_full_dom n _ Hn Hpbfin)].
Qed.

Lemma pb_L1_0_dom : ok_pb (f_omega 4) pb_L1_0.
Proof.
  Transparent pb_L1_0. unfold pb_L1_0. Opaque pb_L1_0.
  apply L_bounce_pb_dom.
  - pose proof (f_omega_id 4) as H. clear - H. lia.
  - pose proof W6_3_ge_fw4 as H. clear - H. lia.
Qed.

Lemma pa_final_dom : ok_pa (iter 4 f_omega3 (f_omega 4)) pa_final.
Proof.
  pose proof E0_ge_fw4 as HE0.
  pose proof pb_L1_0_dom as H0.
  pose proof (f_omega_id 4) as Hn0.
  assert (Hn0_pos : 1 <= f_omega 4) by (clear - Hn0; lia).
  pose proof (Outer_loop_fw3 E0 (f_omega 4) pb_L1_0 Hn0_pos HE0 H0) as H1.
  fold pb_L1_end in H1.
  assert (Hn1_pos : 1 <= f_omega3 (f_omega 4))
    by (pose proof (f_omega3_id (f_omega 4)) as H; clear - Hn0_pos H; lia).
  destruct (Trans1_dom _ pb_L1_end Hn1_pos H1) as [HE1 H2_0].
  fold E1 pb_L2_0 in HE1, H2_0.
  pose proof (Outer_loop_fw3 E1 _ pb_L2_0 Hn1_pos HE1 H2_0) as H2.
  fold pb_L2_end in H2.
  assert (Hn2_pos : 1 <= f_omega3 (f_omega3 (f_omega 4)))
    by (pose proof (f_omega3_id (f_omega3 (f_omega 4))) as H; clear - Hn1_pos H; lia).
  destruct (Trans2_dom _ pb_L2_end Hn2_pos H2) as [HE2 H3_0].
  fold E2 pb_L3_0 in HE2, H3_0.
  pose proof (Outer_loop_fw3 E2 _ pb_L3_0 Hn2_pos HE2 H3_0) as H3.
  fold pb_L3_end in H3.
  assert (Hn3_pos : 1 <= f_omega3 (f_omega3 (f_omega3 (f_omega 4))))
    by (pose proof (f_omega3_id (f_omega3 (f_omega3 (f_omega 4)))) as H; clear - Hn2_pos H; lia).
  destruct (Trans3_dom _ pb_L3_end Hn3_pos H3) as [HE3 H4_0].
  fold E3 pb_L4_0 in HE3, H4_0.
  pose proof (Outer_loop_fw3 (E3 - 1) _ pb_L4_0 Hn3_pos HE3 H4_0) as H4.
  fold pb_L4_end in H4.
  assert (Hn4_pos : 1 <= f_omega3 (f_omega3 (f_omega3 (f_omega3 (f_omega 4)))))
    by (pose proof (f_omega3_id (f_omega3 (f_omega3 (f_omega3 (f_omega 4))))) as H; clear - Hn3_pos H; lia).
  exact (Trans4_dom _ pb_L4_end Hn4_pos H4).
Qed.

Opaque pb_L1_end E1 pb_L2_0 pb_L2_end E2 pb_L3_0 pb_L3_end E3 pb_L4_0 pb_L4_end pa_final.
Strategy opaque [pb_L1_end E1 pb_L2_0 pb_L2_end E2 pb_L3_0 pb_L3_end E3 pb_L4_0 pb_L4_end pa_final].

Lemma N_final_gt_fw3x4 : iter 4 f_omega3 (f_omega 4) < N_final.
Proof.
  unfold N_final. destruct pa_final_dom as [Hp Ha]. clear - Hp Ha. lia.
Qed.

Theorem sigma_bound :
  exists c n, c0_core -->* c /\ halted tm c /\ ones c n /\
  n > iter 4 f_omega3 (f_omega 4).
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, N_final.
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof N_final_gt_fw3x4 as Hgt. clear - Hgt. lia.
Qed.

Theorem sigma_bound_tnf :
  exists c n, c0 -[ tm_tnf ]->* c /\ halted tm_tnf c /\ ones c n /\
  n > iter 4 f_omega3 (f_omega 4).
Proof.
  destruct score_exact_tnf as [c [H1 [H2 H3]]].
  exists c, N_final.
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof N_final_gt_fw3x4 as Hgt. clear - Hgt. lia.
Qed.

(** ** Determinism, Uniqueness of Halting 1-Count, and FGH Upper Bounds *)

Lemma step_det : forall t c c1 c2,
  c -[ t ]-> c1 -> c -[ t ]-> c2 -> c1 = c2.
Proof.
  intros t c c1 c2 H1 H2. destruct H1; inversion H2; subst; congruence.
Qed.

Lemma halted_no_step : forall t c c',
  halted t c -> c -[ t ]-> c' -> False.
Proof.
  intros t c c' Hh Hs. destruct Hs; cbn in Hh; congruence.
Qed.

Lemma evstep_halted_unique : forall t c c1 c2,
  c -[ t ]->* c1 -> halted t c1 ->
  c -[ t ]->* c2 -> halted t c2 ->
  c1 = c2.
Proof.
  intros t c c1 c2 H1. revert c2.
  induction H1 as [c | c c' c1 Hs H1 IH]; intros c2 Hh1 H2 Hh2.
  - inversion H2 as [| ? c'' ? Hs2 _]; subst.
    + reflexivity.
    + exfalso. eapply halted_no_step; [exact Hh1 | exact Hs2].
  - inversion H2 as [| ? c'' ? Hs2 H2']; subst.
    + exfalso. eapply halted_no_step; [exact Hh2 | exact Hs].
    + assert (Heq : c' = c'') by (eapply step_det; [exact Hs | exact Hs2]).
      subst c''. exact (IH c2 Hh1 H2' Hh2).
Qed.

Lemma count1_const0 : forall L,
  L *> const S0 = const S0 -> count1 L = 0.
Proof.
  induction L as [| x t IH]; intros H.
  - reflexivity.
  - cbn [Str_app] in H. rewrite const_unfold in H at 2.
    assert (Hhd : Streams.hd (x >> (t *> const S0)) = Streams.hd (S0 >> const S0))
      by (f_equal; exact H).
    assert (Htl : Streams.tl (x >> (t *> const S0)) = Streams.tl (S0 >> const S0))
      by (f_equal; exact H).
    cbn [Streams.hd Streams.tl] in Hhd, Htl.
    subst x. cbn [count1 sym_val]. exact (IH Htl).
Qed.

Lemma count1_stream_unique : forall L1 L2,
  L1 *> const S0 = L2 *> const S0 -> count1 L1 = count1 L2.
Proof.
  induction L1 as [| x1 t1 IH]; intros L2 H.
  - cbn [Str_app] in H. symmetry in H.
    rewrite (count1_const0 L2 H). reflexivity.
  - destruct L2 as [| x2 t2].
    + cbn [Str_app] in H. rewrite (count1_const0 (x1 :: t1) H). reflexivity.
    + cbn [Str_app] in H.
      assert (Hhd : Streams.hd (x1 >> (t1 *> const S0)) = Streams.hd (x2 >> (t2 *> const S0)))
        by (f_equal; exact H).
      assert (Htl : Streams.tl (x1 >> (t1 *> const S0)) = Streams.tl (x2 >> (t2 *> const S0)))
        by (f_equal; exact H).
      cbn [Streams.hd Streams.tl] in Hhd, Htl.
      subst x2. cbn [count1]. rewrite (IH t2 Htl). reflexivity.
Qed.

Lemma ones_unique : forall c n1 n2,
  ones c n1 -> ones c n2 -> n1 = n2.
Proof.
  intros c n1 n2 [q1 [L1 [R1 [s1 [Hc1 Hn1]]]]] [q2 [L2 [R2 [s2 [Hc2 Hn2]]]]].
  rewrite Hc1 in Hc2. inversion Hc2 as [[Hq HL Hs HR]]. subst.
  rewrite (count1_stream_unique L1 L2 HL).
  rewrite (count1_stream_unique R1 R2 HR).
  reflexivity.
Qed.

(** ** General FGH Upper Bounds for W, Kc, Kc_full, Kd_step, Kd_iter *)

Lemma iter_upper_shift : forall c g h,
  (forall x y, x + c <= y -> g x + c <= h y) ->
  forall m x y, x + c <= y -> iter m g x + c <= iter m h y.
Proof.
  intros c g h Hd. induction m; intros x y Hxy; cbn [iter].
  - exact Hxy.
  - apply Hd, IHm, Hxy.
Qed.

Lemma W_upper_10 : forall j b, W j b + 10 <= f (j + 1) (b + 10).
Proof.
  induction j as [| j IHj]; intros b.
  - rewrite W_0. change (0 + 1) with 1. rewrite f1. lia.
  - rewrite W_S.
    assert (Hstep : forall x y, x + 10 <= y -> W j x + 10 <= f (j + 1) y).
    { intros x y Hxy. transitivity (f (j + 1) (x + 10)); [apply IHj | apply f_mono; exact Hxy]. }
    pose proof (iter_upper_shift 10 (W j) (f (j + 1)) Hstep (S b) 2 12 ltac:(lia)) as H1.
    replace (S j + 1) with (S (j + 1)) by lia.
    rewrite f_S.
    replace (b + 10) with (S b + 9) at 1 by lia.
    rewrite iter_add.
    transitivity (iter (S b) (f (j + 1)) 12); [exact H1 |].
    apply iter_mono_x; [apply f_mono |].
    pose proof (iter_ge (f (j + 1)) (f_id (j + 1)) 8 (f (j + 1) (b + 10))) as Hg.
    rewrite <- iter_S' in Hg.
    pose proof (f_dbl (j + 1) (b + 10) ltac:(lia)) as Hdbl.
    lia.
Qed.

Lemma W_upper_omega : forall p b N,
  10 <= N -> p + 1 <= N -> b + 10 <= N ->
  W p b + 10 <= f_omega N.
Proof.
  intros p b N HN Hp Hb.
  transitivity (f (p + 1) (b + 10)); [apply W_upper_10 |].
  Transparent f_omega. unfold f_omega. Opaque f_omega.
  transitivity (f N (b + 10)).
  - replace N with ((N - (p + 1)) + (p + 1)) by lia.
    apply f_level_mono; lia.
  - apply f_mono; exact Hb.
Qed.

Lemma f_omega_le_f_omega1 : forall n, 1 <= n -> f_omega n <= f_omega1 n.
Proof.
  intros [| n'] Hn; [lia |].
  Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
  rewrite iter_S'. apply iter_ge, f_omega_id.
Qed.

Lemma f_omega1_le_f_omega2 : forall n, 1 <= n -> f_omega1 n <= f_omega2 n.
Proof.
  intros [| n'] Hn; [lia |].
  Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
  rewrite iter_S'. apply iter_ge, f_omega1_id.
Qed.

Lemma f_omega2_le_f_omega3 : forall n, 1 <= n -> f_omega2 n <= f_omega3 n.
Proof.
  intros [| n'] Hn; [lia |].
  Transparent f_omega3. unfold f_omega3. Opaque f_omega3.
  rewrite iter_S'. apply iter_ge, f_omega2_id.
Qed.

Lemma f_omega_le_f_omega3 : forall n, 1 <= n -> f_omega n <= f_omega3 n.
Proof.
  intros n Hn.
  pose proof (f_omega_le_f_omega1 n Hn).
  pose proof (f_omega1_le_f_omega2 n Hn).
  pose proof (f_omega2_le_f_omega3 n Hn). lia.
Qed.

Lemma iter2_f_omega_le_f_omega1 : forall n, 2 <= n -> iter 2 f_omega n <= f_omega1 n.
Proof.
  intros n Hn.
  Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
  apply iter_mono_n; [apply f_omega_id | exact Hn].
Qed.

Lemma iter3_f_omega_le_f_omega1 : forall n, 3 <= n -> iter 3 f_omega n <= f_omega1 n.
Proof.
  intros n Hn.
  Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
  apply iter_mono_n; [apply f_omega_id | exact Hn].
Qed.

Definition ub (N : nat) (pa : nat * nat) : Prop :=
  fst pa + 10 <= N /\ snd pa + 10 <= N.

Lemma ub_mono : forall M N pa, M <= N -> ub M pa -> ub N pa.
Proof. intros M N pa Hle [H1 H2]. split; lia. Qed.

Lemma Kc_upper : forall N pa,
  11 <= N -> ub N pa -> ub (f_omega N) (Kc pa).
Proof.
  intros N [p a] HN [Hp Ha]. unfold ub in *. cbn [fst snd] in *.
  rewrite Kc_unfold. cbn [fst snd].
  pose proof (f_omega_dbl N ltac:(lia)) as Hdbl.
  split.
  - assert (Ha2 : a / 2 <= a) by (mods; lia). lia.
  - apply W_upper_omega; lia.
Qed.

Lemma Kc_iter_upper : forall k N pa,
  11 <= N -> ub N pa -> ub (iter k f_omega N) (iter k Kc pa).
Proof.
  induction k as [| k IHk]; intros N pa HN Hub.
  - cbn [iter]. exact Hub.
  - cbn [iter]. apply Kc_upper.
    + pose proof (iter_ge f_omega f_omega_id k N). lia.
    + exact (IHk N pa HN Hub).
Qed.

Lemma Kc_full_upper : forall N pb,
  13 <= N -> ub N pb -> ub (f_omega1 N) (Kc_full pb).
Proof.
  intros N [p b] HN [Hp Hb]. unfold ub in *. cbn [fst snd] in *.
  rewrite Kc_full_unfold.
  assert (Hbase : ub (f_omega N) (p - 1, W (p - 1) 3)).
  { split; cbn [fst snd].
    - pose proof (f_omega_id N). lia.
    - apply W_upper_omega; lia. }
  pose proof (f_omega_id N) as Hfw_id.
  pose proof (Kc_iter_upper (b / 2) (f_omega N) (p - 1, W (p - 1) 3) ltac:(lia) Hbase) as Hiter.
  rewrite <- iter_S' in Hiter.
  eapply ub_mono; [| exact Hiter].
  Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
  apply iter_mono_n; [apply f_omega_id | mods; lia].
Qed.

Lemma Kd_step_upper : forall N pb,
  13 <= N -> ub N pb -> ub (iter 2 f_omega1 N) (Kd_step pb).
Proof.
  intros N pb HN Hub.
  rewrite Kd_step_unfold.
  pose proof (Kc_full_upper N pb HN Hub) as Hkc.
  destruct (Kc_full pb) as [p' a']. destruct Hkc as [Hp' Ha']. cbn [fst snd] in *.
  set (M := f_omega1 N) in *.
  assert (HM_ge : 13 <= M) by (unfold M; pose proof (f_omega1_id N); lia).
  pose proof (f_omega_dbl M ltac:(lia)) as HM_dbl.
  pose proof (f_omega_id M) as HM_id.
  assert (Hw : W p' (a' + 4) + 10 <= f_omega (f_omega M)).
  { apply W_upper_omega; lia. }
  pose proof (iter2_f_omega_le_f_omega1 M ltac:(lia)) as H2.
  cbn [iter] in H2 |- *. fold M.
  pose proof (f_omega1_id M) as HM1_id.
  split; cbn [fst snd]; lia.
Qed.

Lemma Kd_iter_upper : forall m N pb,
  13 <= N -> ub N pb -> ub (iter (2 * m) f_omega1 N) (Kd_iter m pb).
Proof.
  intros m N pb. rewrite Kd_iter_unfold.
  induction m as [| m IHm]; intros HN Hub.
  - change (2 * 0) with 0. cbn [iter]. exact Hub.
  - replace (2 * S m) with (2 + 2 * m) by lia.
    rewrite iter_add. cbn [iter].
    pose proof (IHm HN Hub) as H1.
    pose proof (iter_ge f_omega1 f_omega1_id (2 * m) N) as Hge.
    exact (Kd_step_upper (iter (2 * m) f_omega1 N) (iter m Kd_step pb) ltac:(lia) H1).
Qed.

(** ** Self-Contained Execution and Exact Upper Bound for Previous Champion M14_fw3 *)

Module M14_Old.

  Declare Scope old_tm_scope.
  Delimit Scope old_tm_scope with oldtm.
  Local Open Scope old_tm_scope.
  Local Open Scope sym_scope.

  Local Notation "c --> c'"  := (c -[ tm_M14_fw3 ]-> c')   (at level 40) : old_tm_scope.
  Local Notation "c -->* c'" := (c -[ tm_M14_fw3 ]->* c')  (at level 40) : old_tm_scope.
  Local Notation "c -->+ c'" := (c -[ tm_M14_fw3 ]->+ c')  (at level 40) : old_tm_scope.

  Lemma cr_AR_1_1 : forall n l r, l {{A}}> [1]^^n *> r -->* [1]^^n *> l {{A}}> r.
  Proof. induction n; intros; [finish | execute; follow IHn; finish_norm]. Qed.

  Lemma cr_DL_1_1 : forall n l r, [1]^^n *> l <{{D}} r -->* l <{{D}} [1]^^n *> r.
  Proof. induction n; intros; [finish | execute; follow IHn; finish_norm]. Qed.

  Lemma cr_HL_1_1 : forall n l r, [1]^^n *> l <{{H}} r -->* l <{{H}} [1]^^n *> r.
  Proof. induction n; intros; [finish | execute; follow IHn; finish_norm]. Qed.

  Lemma cr_HL_01_01 : forall n l r, [0; 1]^^n *> l <{{H}} r -->* l <{{H}} [0; 1]^^n *> r.
  Proof. induction n; intros; [finish | execute; follow IHn; finish_norm]. Qed.

  Lemma cr_IL_11_10 : forall n l r, [1; 1]^^n *> l <{{I}} r -->* l <{{I}} [1; 0]^^n *> r.
  Proof. induction n; intros; [finish | execute; follow IHn; finish_norm]. Qed.

  Lemma cr_KL_11_10 : forall n l r, [1; 1]^^n *> l <{{K}} r -->* l <{{K}} [1; 0]^^n *> r.
  Proof. induction n; intros; [finish | execute; follow IHn; finish_norm]. Qed.

  Lemma CA_SH : forall j b z, Ca j b (1 >> 0 >> z) -->+ Ca (S j) b z.
  Proof.
    intros j b z. unfold Ca.
    start_progress. follow cr_DL_1_1. align_tape. execute. follow cr_AR_1_1. finish_norm.
  Qed.

  Lemma CA_SH_iter : forall k j b z, Ca j b ([1; 0]^^k *> z) -->* Ca (j + k) b z.
  Proof.
    induction k; intros j b z.
    - replace (j + 0)%nat with j by lia. finish.
    - simpl. eapply evstep_trans; [apply progress_evstep, CA_SH |].
      follow (IHk (S j) b z). replace (S j + k)%nat with (j + S k)%nat by lia. finish.
  Qed.

  Lemma CA_EXIT : forall j b z,
    Ca j b (0 >> z) -->+ ([1]^^(b + 2) *> [0; 1]^^j *> const 0) {{I}}> z.
  Proof. intros j b z. unfold Ca. start_progress. finish_norm. Qed.

  Lemma CA_CH : forall j b y, Ca j b (1 >> 1 >> y) -->+ Ch j b (1 >> y).
  Proof. intros j b y. unfold Ca, Ch. start_progress. follow cr_HL_1_1. finish_norm. Qed.

  Lemma CH_0 : forall b z, Ch 0 b z -->+ Ca 0 (b + 3) z.
  Proof. intros b z. unfold Ch, Ca. simpl lpow. start_progress. follow cr_AR_1_1. finish_norm. Qed.

  Lemma CH_S_aux : forall j b z, Ch (S j) b z -->+ Ca 0 2 ([1; 0]^^j *> blk (S b) z).
  Proof.
    intros j b z. unfold Ch, Ca, blk.
    start_progress. follow cr_HL_01_01. align_tape. execute; finish_norm.
  Qed.

  Lemma CH_S : forall j b z, Ch (S j) b z -->+ Ca j 2 (blk (S b) z).
  Proof.
    intros j b z. eapply progress_evstep_trans; [apply CH_S_aux |].
    follow (CA_SH_iter j 0 2 (blk (S b) z)). finish_norm.
  Qed.

  Lemma E_EVEN : forall p' k r,
    ([1]^^(2 * k + 2) *> [0; 1]^^(S p') *> const 0) {{I}}> (1 >> 0 >> r) -->+
    Ch p' 1 ([1; 0]^^(S k) *> 0 >> r).
  Proof.
    intros p' k r. unfold Ch.
    replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
    rewrite !lpow_add. cbn [lpow Str_app].
    rewrite (lpow_double [1] k). cbn [app].
    start_progress. follow cr_IL_11_10. execute; finish_norm.
  Qed.

  Lemma C_REL_aux : forall p' m d z,
    Cd_z (S p') (2 * m + 1) (S d) z -->+ Ch p' 3 (0 >> [1; 0]^^m *> 0 >> [1; 0]^^d *> z).
  Proof.
    intros p' m d z. unfold Cd_z, Ch.
    replace (2 * m + 1 + 2)%nat with (1 + (2 * m + 2))%nat by lia.
    rewrite !lpow_add. cbn [lpow Str_app].
    rewrite (lpow_double [1] m). cbn [app].
    start_progress. follow cr_IL_11_10. align_tape. execute; finish_norm.
  Qed.

  Lemma D_STEP_aux : forall p a d z,
    Ce_z p a 0 (S (S d)) z -->+ Ch p (a + 4) (0 >> [1; 0]^^d *> z).
  Proof.
    intros p a d z. unfold Ce_z, Ch. norm_nat.
    start_progress. follow cr_HL_1_1. finish_norm.
  Qed.

  Lemma N_bounce : forall p d z,
    ([0; 1]^^(S (S (S p))) *> const 0) <{{L}} (0 >> [1; 0]^^(S d) *> z) -->+
    Cd_z (S (S p)) 1 (S d) z.
  Proof. intros p d z. unfold Cd_z. cbn [lpow Str_app]. start_progress; finish_norm. Qed.

  Lemma Phase1_reload_aux : forall p' k z,
    Ce_z p' (2 * k) 0 0 (0 >> z) -->+
    ([0; 1]^^p' *> const 0) <{{L}} (0 >> [1; 0]^^(S k) *> (0 >> z)).
  Proof.
    intros p' k z. unfold Ce_z.
    replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
    rewrite !lpow_add. cbn [lpow Str_app].
    rewrite (lpow_double [1] k). cbn [app].
    start_progress. follow cr_KL_11_10. align_tape. execute; finish_norm.
  Qed.

  Lemma Phase1_reload : forall p k z,
    Ce_z (S (S (S p))) (2 * k) 0 0 (0 >> z) -->+
    Cd_z (S (S p)) 1 (S k) (0 >> z).
  Proof.
    intros p k z. eapply progress_evstep_trans; [apply Phase1_reload_aux |].
    apply progress_evstep, N_bounce.
  Qed.

  Lemma Phase2_reload_aux : forall p' k zE,
    Ce_z p' (2 * k) 0 1 (0 >> 1 >> zE) -->+
    ([0; 1]^^p' *> const 0) <{{L}} (0 >> [1; 0]^^(k + 3) *> zE).
  Proof.
    intros p' k zE. unfold Ce_z.
    replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
    rewrite !lpow_add. cbn [lpow Str_app].
    rewrite (lpow_double [1] k). cbn [app].
    start_progress. follow cr_KL_11_10. align_tape. execute; finish_norm.
  Qed.

  Lemma Phase2_reload : forall p k E,
    Ce_z (S (S (S p))) (2 * k) 0 1 (0 >> [1; 0]^^(S E) *> const 0) -->+
    Cd_z (S (S p)) 1 (k + 3) (0 >> [1; 0]^^E *> const 0).
  Proof.
    intros p k E.
    change (0 >> [1; 0]^^(S E) *> const 0)%sym with (0 >> 1 >> (0 >> [1; 0]^^E *> const 0))%sym.
    eapply progress_evstep_trans; [apply Phase2_reload_aux |].
    replace (k + 3)%nat with (S (k + 2))%nat by lia.
    apply progress_evstep, N_bounce.
  Qed.

  Definition c_end_old (p a : nat) : Q * tape :=
    ([1]^^(a + 6) *> [0; 1]^^p *> const 0) {{K}}> const 0.

  Lemma HALT_E0 : forall p a,
    Ce_z p a 0 1 (0 >> const 0) -->+ c_end_old p a.
  Proof.
    intros p a. unfold Ce_z, c_end_old. cbn [lpow Str_app].
    rewrite const_unfold at 2. start_progress; finish_norm.
  Qed.

  Lemma c_end_old_halted : forall p a, halted tm_M14_fw3 (c_end_old p a).
  Proof. intros p a. unfold c_end_old. reflexivity. Qed.

  Local Open Scope nat_scope.

  Lemma BLK_iter_aux : forall j,
    (forall b z, Ch j b z -->+ Ca j (W j b) z) ->
    forall a b z, Ca j b (blk a z) -->+ Ca (S j) (iter a (W j) b) z.
  Proof.
    intros j HCh a. induction a as [| a IHa]; intros b z.
    - apply CA_SH.
    - eapply progress_evstep_trans; [apply CA_CH |].
      eapply evstep_trans; [apply progress_evstep, HCh |].
      rewrite iter_S'. apply progress_evstep, IHa.
  Qed.

  Lemma CH_CA : forall j b z, Ch j b z -->+ Ca j (W j b) z.
  Proof.
    induction j as [| j IHj]; intros b z.
    - rewrite W_0. apply CH_0.
    - rewrite W_S. eapply progress_evstep_trans; [apply CH_S |].
      apply progress_evstep. apply (BLK_iter_aux j IHj (S b) 2 z).
  Qed.

  Lemma CE_EVEN : forall p' k c d z,
    Ce_z (S p') (2 * k) (S c) d z -->+ Ce_z (p' + S k) (W p' 1) c d z.
  Proof.
    intros p' k c d z. unfold Ce_z. cbn [lpow Str_app].
    eapply progress_evstep_trans; [apply E_EVEN |].
    eapply evstep_trans; [apply progress_evstep, CH_CA |].
    follow (CA_SH_iter (S k) p' (W p' 1) (S0 >> [S1; S0]^^c *> S0 >> [S1; S0]^^d *> z)).
    eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
    finish_norm.
  Qed.

  Lemma C_REL : forall p' m d z,
    Cd_z (S p') (2 * m + 1) (S d) z -->+ Ce_z p' (W p' 3) m d z.
  Proof.
    intros p' m d z. unfold Ce_z.
    eapply progress_evstep_trans; [apply C_REL_aux |].
    eapply evstep_trans; [apply progress_evstep, CH_CA |].
    eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
    finish_norm.
  Qed.

  Lemma D_STEP : forall p a d z,
    Ce_z p a 0 (S (S d)) z -->+ Cd_z p (W p (a + 4)) d z.
  Proof.
    intros p a d z. unfold Cd_z.
    eapply progress_evstep_trans; [apply D_STEP_aux |].
    eapply evstep_trans; [apply progress_evstep, CH_CA |].
    eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
    finish_norm.
  Qed.

  Lemma N_bounce_step : forall p d z,
    Cd_z (S p) 1 (S (S (S d))) z -->+ Cd_z p (W p (W p 3 + 4)) d z.
  Proof.
    intros p d z.
    eapply progress_evstep_trans; [apply (C_REL p 0 (S (S d)) z) |].
    apply progress_evstep, D_STEP.
  Qed.

  Lemma Boot_139 : c0 -->* Ch 3 3 (const S0).
  Proof. unfold Ch. cbn [lpow Str_app]. do 139 step; finish_norm. Qed.

  Lemma Boot_bridge_72 : forall z,
    ([S1]^^8 *> const S0) {{I}}> ([S1; S0]^^29 *> z) -->* Cd_z 4 3 28 z.
  Proof. intros z. unfold Cd_z. cbn [lpow Str_app]. do 72 step; finish_norm. Qed.

  Definition N_bounce_pb (p : nat) : nat * nat := (p, W p (W p 3 + 4)).

  Definition Phase1_pa (pa : nat * nat) : nat * nat :=
    let '(p, a) := pa in Kc_full (Kd_iter ((a / 2 + 2) / 3 - 2) (N_bounce_pb (p - 2))).

  Definition Phase2_pa (pa1 : nat * nat) : nat * nat :=
    let '(p1, a1) := pa1 in Kc_full (Kd_iter ((a1 / 2 + 2) / 3 - 1) (N_bounce_pb (p1 - 2))).

  Definition Outer_step_old (pa : nat * nat) : nat * nat := Phase2_pa (Phase1_pa pa).

  Lemma Kc_step : forall c d z pa,
    1 <= fst pa -> snd pa = 2 * (snd pa / 2) ->
    Ce_z (fst pa) (snd pa) (S c) d z -->+ Ce_z (fst (Kc pa)) (snd (Kc pa)) c d z.
  Proof.
    intros c d z [p a] Hp Ha_eq. rewrite Kc_unfold. cbn [fst snd] in *.
    destruct p as [| p']; [lia |].
    replace (S p' - 1) with p' by lia.
    replace (S p' + a / 2) with (p' + S (a / 2)) by lia.
    rewrite Ha_eq at 1. apply CE_EVEN.
  Qed.

  Lemma Kc_loop : forall c d z pa,
    4 <= fst pa -> is_W_even (snd pa) ->
    Ce_z (fst pa) (snd pa) c d z -->* Ce_z (fst (iter c Kc pa)) (snd (iter c Kc pa)) 0 d z /\
    fst pa + c <= fst (iter c Kc pa) /\
    is_W_even (snd (iter c Kc pa)).
  Proof.
    induction c as [| c IHc]; intros d z pa Hp Ha.
    - cbn [iter]. split; [finish | split; [lia | exact Ha]].
    - rewrite iter_S'. destruct Ha as [Ha_eq [Ha_ge Ha_div3]].
      assert (Hw1 : is_W_even (snd (Kc pa))).
      { destruct pa as [p a]. rewrite Kc_unfold. cbn [fst snd] in *.
        apply W_ge3_odd; [lia | reflexivity]. }
      assert (Hp1 : fst pa + 1 <= fst (Kc pa)).
      { destruct pa as [p a]. rewrite Kc_unfold. cbn [fst snd] in *. lia. }
      destruct (IHc d z (Kc pa) ltac:(lia) Hw1) as [Hrun [Hp2 Ha2]].
      split; [| split].
      + eapply evstep_trans; [apply progress_evstep, (Kc_step c d z pa ltac:(lia) Ha_eq) | exact Hrun].
      + lia.
      + exact Ha2.
  Qed.

  Lemma Kc_full_all : forall d z pb,
    5 <= fst pb -> is_W_odd (snd pb) ->
    Cd_z (fst pb) (snd pb) (S d) z -->+ Ce_z (fst (Kc_full pb)) (snd (Kc_full pb)) 0 d z /\
    fst pb + 58 <= fst (Kc_full pb) /\
    is_W_even (snd (Kc_full pb)).
  Proof.
    intros d z [p b] Hp [Hb_eq [Hb_ge _]]. rewrite Kc_full_unfold. cbn [fst snd] in *.
    destruct p as [| p']; [lia |].
    replace (S p' - 1) with p' by lia.
    assert (Hw3 : is_W_even (W p' 3)) by (apply W_ge3_odd; [lia | reflexivity]).
    destruct (Kc_loop (b / 2) d z (p', W p' 3) ltac:(cbn; lia) Hw3) as [Hrun [Hp1 Ha1]].
    cbn [fst snd] in *.
    split; [| split].
    - rewrite Hb_eq at 1. eapply progress_evstep_trans; [apply C_REL | exact Hrun].
    - lia.
    - exact Ha1.
  Qed.

  Lemma Kd_step_all : forall d z pb,
    5 <= fst pb -> is_W_odd (snd pb) ->
    Cd_z (fst pb) (snd pb) (S (S (S d))) z -->+ Cd_z (fst (Kd_step pb)) (snd (Kd_step pb)) d z /\
    fst pb + 58 <= fst (Kd_step pb) /\
    is_W_odd (snd (Kd_step pb)).
  Proof.
    intros d z pb Hp Hb. rewrite Kd_step_unfold.
    destruct (Kc_full_all (S (S d)) z pb Hp Hb) as [Hkc [Hp1 Ha1]].
    set (pa' := Kc_full pb) in *. destruct pa' as [p' a']. cbn [fst snd] in *.
    destruct Ha1 as [Ha_eq _].
    assert (Ha4_ev : (a' + 4) mod 2 = 0).
    { replace (a' + 4) with (0 + (a' / 2 + 2) * 2) by lia.
      rewrite Nat.Div0.mod_add. reflexivity. }
    assert (Hw : is_W_odd (W p' (a' + 4))) by (apply W_ge3_even; [lia | lia | exact Ha4_ev]).
    split; [| split].
    - eapply progress_evstep_trans; [exact Hkc | apply progress_evstep, D_STEP].
    - exact Hp1.
    - exact Hw.
  Qed.

  Lemma Kd_loop : forall m r z pb,
    5 <= fst pb -> is_W_odd (snd pb) ->
    Cd_z (fst pb) (snd pb) (3 * m + r) z -->* Cd_z (fst (Kd_iter m pb)) (snd (Kd_iter m pb)) r z /\
    fst pb + 58 * m <= fst (Kd_iter m pb) /\
    is_W_odd (snd (Kd_iter m pb)).
  Proof.
    intros m r z pb. rewrite Kd_iter_unfold. revert r z pb.
    induction m as [| m IHm]; intros r z pb Hp Hb.
    - cbn [iter]. replace (3 * 0 + r) with r by lia. split; [finish | split; [lia | exact Hb]].
    - rewrite iter_S'. replace (3 * S m + r) with (S (S (S (3 * m + r)))) by lia.
      destruct (Kd_step_all (3 * m + r) z pb Hp Hb) as [Hstep [Hp1 Hb1]].
      destruct (IHm r z (Kd_step pb) ltac:(lia) Hb1) as [Hrun [Hp2 Hb2]].
      split; [| split].
      + eapply evstep_trans; [apply progress_evstep, Hstep | exact Hrun].
      + lia.
      + exact Hb2.
  Qed.

  Lemma N_bounce_pb_props : forall p,
    5 <= p -> fst (N_bounce_pb p) = p /\ is_W_odd (snd (N_bounce_pb p)).
  Proof.
    intros p Hp. unfold N_bounce_pb. cbn [fst snd]. split; [reflexivity |].
    destruct (W_ge3_odd p 3 ltac:(lia) eq_refl) as [Hw_eq _].
    assert (Hev : (W p 3 + 4) mod 2 = 0).
    { replace (W p 3 + 4) with (0 + (W p 3 / 2 + 2) * 2) by lia.
      rewrite Nat.Div0.mod_add. reflexivity. }
    apply W_ge3_even; [lia | lia | exact Hev].
  Qed.

  Lemma Phase1_exec : forall z pa,
    7 <= fst pa -> is_W_even (snd pa) ->
    Ce_z (fst pa) (snd pa) 0 0 (S0 >> z) -->+ Ce_z (fst (Phase1_pa pa)) (snd (Phase1_pa pa)) 0 1 (S0 >> z) /\
    7 <= fst (Phase1_pa pa) /\
    is_W_even (snd (Phase1_pa pa)).
  Proof.
    intros z [p a] Hp [Ha_eq [Ha_ge Ha_div3]]. cbn [fst snd Phase1_pa] in *.
    set (M := (a / 2 + 2) / 3) in *.
    assert (HM_ge : 46 <= M) by (unfold M in *; lia).
    destruct (N_bounce_pb_props (p - 2) ltac:(lia)) as [Hnb_p Hnb_odd].
    destruct (Kd_loop (M - 2) 2 (S0 >> z) (N_bounce_pb (p - 2)) ltac:(lia) Hnb_odd)
      as [Hkd [Hkd_p Hkd_odd]].
    destruct (Kc_full_all 1 (S0 >> z) (Kd_iter (M - 2) (N_bounce_pb (p - 2))) ltac:(lia) Hkd_odd)
      as [Hkc [Hkc_p Hkc_ev]].
    split; [| split; [lia | exact Hkc_ev]].
    replace p with (S (S (S (p - 3)))) at 1 by lia.
    rewrite Ha_eq at 1.
    eapply progress_evstep_trans; [apply Phase1_reload |].
    replace (S (S (p - 3))) with (S (p - 2)) by lia.
    assert (HSa : S (a / 2) = S (S (S (3 * (M - 2) + 2)))) by (unfold M in *; lia).
    rewrite HSa.
    eapply evstep_trans; [apply progress_evstep, N_bounce_step |].
    change (Cd_z (p - 2) (W (p - 2) (W (p - 2) 3 + 4)) (3 * (M - 2) + 2) (S0 >> z))
      with (Cd_z (fst (N_bounce_pb (p - 2))) (snd (N_bounce_pb (p - 2))) (3 * (M - 2) + 2) (S0 >> z)).
    eapply evstep_trans; [exact Hkd |].
    apply progress_evstep, Hkc.
  Qed.

  Lemma Phase2_exec : forall E pa1,
    7 <= fst pa1 -> is_W_even (snd pa1) ->
    Ce_z (fst pa1) (snd pa1) 0 1 (S0 >> [S1; S0]^^(S E) *> const S0) -->+
    Ce_z (fst (Phase2_pa pa1)) (snd (Phase2_pa pa1)) 0 0 (S0 >> [S1; S0]^^E *> const S0) /\
    7 <= fst (Phase2_pa pa1) /\
    is_W_even (snd (Phase2_pa pa1)).
  Proof.
    intros E [p1 a1] Hp1 [Ha1_eq [Ha1_ge Ha1_div3]]. cbn [fst snd Phase2_pa] in *.
    set (M1 := (a1 / 2 + 2) / 3) in *.
    assert (HM1_ge : 46 <= M1) by (unfold M1 in *; lia).
    destruct (N_bounce_pb_props (p1 - 2) ltac:(lia)) as [Hnb_p Hnb_odd].
    destruct (Kd_loop (M1 - 1) 1 (S0 >> [S1; S0]^^E *> const S0) (N_bounce_pb (p1 - 2)) ltac:(lia) Hnb_odd)
      as [Hkd [Hkd_p Hkd_odd]].
    destruct (Kc_full_all 0 (S0 >> [S1; S0]^^E *> const S0) (Kd_iter (M1 - 1) (N_bounce_pb (p1 - 2))) ltac:(lia) Hkd_odd)
      as [Hkc [Hkc_p Hkc_ev]].
    split; [| split; [lia | exact Hkc_ev]].
    replace p1 with (S (S (S (p1 - 3)))) at 1 by lia.
    rewrite Ha1_eq at 1.
    eapply progress_evstep_trans; [apply Phase2_reload |].
    replace (S (S (p1 - 3))) with (S (p1 - 2)) by lia.
    assert (HSa1 : a1 / 2 + 3 = S (S (S (3 * (M1 - 1) + 1)))) by (unfold M1 in *; lia).
    rewrite HSa1.
    eapply evstep_trans; [apply progress_evstep, N_bounce_step |].
    change (Cd_z (p1 - 2) (W (p1 - 2) (W (p1 - 2) 3 + 4)) (3 * (M1 - 1) + 1) (S0 >> [S1; S0]^^E *> const S0))
      with (Cd_z (fst (N_bounce_pb (p1 - 2))) (snd (N_bounce_pb (p1 - 2))) (3 * (M1 - 1) + 1) (S0 >> [S1; S0]^^E *> const S0)).
    eapply evstep_trans; [exact Hkd |].
    apply progress_evstep, Hkc.
  Qed.

  Lemma Outer_step_old_unfold : forall pa, Outer_step_old pa = Phase2_pa (Phase1_pa pa).
  Proof. reflexivity. Qed.

  Opaque N_bounce_pb Phase1_pa Phase2_pa Outer_step_old.
  Strategy opaque [N_bounce_pb Phase1_pa Phase2_pa Outer_step_old].

  Lemma Outer_loop_old : forall E pa,
    7 <= fst pa -> is_W_even (snd pa) ->
    Ce_z (fst pa) (snd pa) 0 0 (S0 >> [S1; S0]^^E *> const S0) -->*
    Ce_z (fst (iter E Outer_step_old pa)) (snd (iter E Outer_step_old pa)) 0 0 (S0 >> const S0) /\
    7 <= fst (iter E Outer_step_old pa) /\
    is_W_even (snd (iter E Outer_step_old pa)).
  Proof.
    induction E as [| E IHE]; intros pa Hp Ha.
    - cbn [iter lpow Str_app]. split; [finish | split; [exact Hp | exact Ha]].
    - rewrite iter_S'.
      destruct (Phase1_exec ([S1; S0]^^(S E) *> const S0) pa Hp Ha) as [Hp1_run [Hp1_ge Hp1_ev]].
      destruct (Phase2_exec E (Phase1_pa pa) Hp1_ge Hp1_ev) as [Hp2_run [Hp2_ge Hp2_ev]].
      rewrite <- Outer_step_old_unfold in *.
      destruct (IHE (Outer_step_old pa) Hp2_ge Hp2_ev) as [Hrest [Hfin_ge Hfin_ev]].
      split; [| split; [exact Hfin_ge | exact Hfin_ev]].
      eapply evstep_trans; [apply progress_evstep, Hp1_run |].
      eapply evstep_trans; [apply progress_evstep, Hp2_run | exact Hrest].
  Qed.

  Definition E0_old : nat := W 3 3 / 2 - 3.
  Definition pb_boot : nat * nat := (3 + W 3 3 / 2, W (3 + W 3 3 / 2) (W 2 1 + 4)).
  Definition pa_init : nat * nat := Kc_full (Kd_iter 8 pb_boot).
  Definition pa_final_old : nat * nat := Phase1_pa (iter E0_old Outer_step_old pa_init).
  Definition N_old : nat := fst pa_final_old + snd pa_final_old + 6.

  Lemma W3_3_even : is_W_even (W 3 3).
  Proof. apply W_ge3_odd; [lia | reflexivity]. Qed.

  Lemma I_const0_to_Ce : forall p a,
    ([S1]^^(a + 2) *> [S0; S1]^^p *> const S0) {{I}}> (const S0) =
    Ce_z p a 0 0 (S0 >> const S0).
  Proof.
    intros p a. unfold Ce_z. cbn [lpow Str_app].
    do 2 f_equal. cbn [Streams.tl]. apply const_unfold.
  Qed.

  Lemma Boot_to_Cd4 :
    c0 -->* Cd_z 4 3 28 (S0 >> [S1; S0]^^E0_old *> const S0).
  Proof.
    destruct W3_3_even as [Hw_eq [Hw_ge _]].
    eapply evstep_trans; [exact Boot_139 |].
    eapply evstep_trans; [apply progress_evstep, CH_CA |].
    rewrite const_unfold at 1.
    eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
    rewrite I_const0_to_Ce.
    rewrite Hw_eq at 1.
    eapply evstep_trans; [apply progress_evstep, (Phase1_reload 0 (W 3 3 / 2) (const S0)) |].
    rewrite <- const_unfold.
    replace (S (W 3 3 / 2)) with (S (S (S (S E0_old)))) by (clear - Hw_ge; unfold E0_old; lia).
    eapply evstep_trans; [apply progress_evstep, (C_REL 1 0 (S (S (S E0_old))) (const S0)) |].
    rewrite W1_3_val.
    eapply evstep_trans; [apply progress_evstep, (D_STEP 1 14 (S E0_old) (const S0)) |].
    change (14 + 4) with 18. rewrite W1_18_val.
    change 59 with (2 * 29 + 1).
    eapply evstep_trans; [apply progress_evstep, (C_REL 0 29 E0_old (const S0)) |].
    rewrite W0_3_val.
    unfold Ce_z. cbn [Nat.add lpow Str_app].
    apply Boot_bridge_72.
  Qed.

  Lemma Boot_to_pa_init :
    c0 -->* Ce_z (fst pa_init) (snd pa_init) 0 0 (S0 >> [S1; S0]^^E0_old *> const S0) /\
    7 <= fst pa_init /\
    is_W_even (snd pa_init).
  Proof.
    destruct W3_3_even as [Hw_eq [Hw_ge _]].
    set (zE := (S0 >> [S1; S0]^^E0_old *> const S0)).
    assert (Hpb_odd : is_W_odd (snd pb_boot)).
    { unfold pb_boot. cbn [snd]. rewrite W2_1_val.
      apply W_ge3_even; [clear - Hw_ge; lia | lia | reflexivity]. }
    assert (Hpb_ge : 5 <= fst pb_boot) by (unfold pb_boot; cbn [fst]; clear - Hw_ge; lia).
    destruct (Kd_loop 8 1 zE pb_boot Hpb_ge Hpb_odd) as [Hkd [Hkd_p Hkd_odd]].
    destruct (Kc_full_all 0 zE (Kd_iter 8 pb_boot) ltac:(clear - Hpb_ge Hkd_p; lia) Hkd_odd)
      as [Hkc [Hkc_p Hkc_ev]].
    unfold pa_init.
    split; [| split; [clear - Hpb_ge Hkd_p Hkc_p; lia | exact Hkc_ev]].
    eapply evstep_trans; [exact Boot_to_Cd4 |].
    fold zE.
    eapply evstep_trans; [apply progress_evstep, (C_REL 3 1 27 zE) |].
    eapply evstep_trans; [apply progress_evstep, (Kc_step 0 27 zE (3, W 3 3) ltac:(cbn; lia) Hw_eq) |].
    rewrite Kc_unfold. cbn [fst snd]. replace (3 - 1) with 2 by lia.
    eapply evstep_trans; [apply progress_evstep, (D_STEP (3 + W 3 3 / 2) (W 2 1) 25 zE) |].
    change (Cd_z (3 + W 3 3 / 2) (W (3 + W 3 3 / 2) (W 2 1 + 4)) 25 zE)
      with (Cd_z (fst pb_boot) (snd pb_boot) (3 * 8 + 1) zE).
    eapply evstep_trans; [exact Hkd |].
    apply progress_evstep, Hkc.
  Qed.

  Lemma run_to_end_old : c0 -->* c_end_old (fst pa_final_old) (snd pa_final_old).
  Proof.
    destruct Boot_to_pa_init as [Hboot [Hp0 Ha0]].
    destruct (Outer_loop_old E0_old pa_init Hp0 Ha0) as [Hloop [HpE HaE]].
    destruct (Phase1_exec (const S0) (iter E0_old Outer_step_old pa_init) HpE HaE) as [Hp1 _].
    unfold pa_final_old.
    eapply evstep_trans; [exact Hboot |].
    eapply evstep_trans; [exact Hloop |].
    eapply evstep_trans; [apply progress_evstep, Hp1 |].
    apply progress_evstep, HALT_E0.
  Qed.

  Lemma ones_c_end_old : forall p a, ones (c_end_old p a) (p + a + 6).
  Proof.
    intros p a.
    eexists. exists ([S1]^^(a + 6) ++ [S0; S1]^^p), (@nil Sym), S0.
    split.
    - unfold c_end_old. rewrite !Str_app_assoc. cbn [Str_app Streams.hd Streams.tl]. reflexivity.
    - rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
  Qed.

  Lemma score_exact_old :
    exists c, c0 -->* c /\ halted tm_M14_fw3 c /\ ones c N_old.
  Proof.
    exists (c_end_old (fst pa_final_old) (snd pa_final_old)).
    split; [exact run_to_end_old |].
    split; [apply c_end_old_halted |].
    apply ones_c_end_old.
  Qed.

  Definition perm_f_old (q : Q) : Q :=
    match q with
    | A => A | B => B | C => J | D => H | E => D | F => I | G => N
    | H => M | I => C | J => K | K => E | L => F | M => L | N => G
    end.

  Lemma tm_old_perm_tnf : Perm tm_M14_fw3 tm_M14_fw3_tnf perm_f_old.
  Proof.
    split.
    - intros [] [] H; inversion H; reflexivity.
    - intros [] [] s' d q' H; inversion H; subst; reflexivity.
  Qed.

  Lemma score_exact_old_tnf :
    exists c, c0 -[ tm_M14_fw3_tnf ]->* c /\ halted tm_M14_fw3_tnf c /\ ones c N_old.
  Proof.
    destruct score_exact_old as [[q t] [Hrun [Hhalt Hones]]].
    exists (perm_f_old q, t).
    split.
    - exact (perm_evstep tm_M14_fw3 tm_M14_fw3_tnf perm_f_old tm_old_perm_tnf c0 (q, t) Hrun).
    - split.
      + exact (perm_halted tm_M14_fw3 tm_M14_fw3_tnf perm_f_old q t tm_old_perm_tnf Hhalt).
      + destruct Hones as [q' [L [R [s [Heq Hn]]]]].
        inversion Heq; subst. exists (perm_f_old q'), L, R, s. auto.
  Qed.

  (** *** Exact Upper Bound: N_old <= f_omega3 (f_omega 13) *)

  Lemma N_bounce_pb_upper : forall N p,
    13 <= N -> p + 10 <= N -> ub (f_omega1 N) (N_bounce_pb (p - 2)).
  Proof.
    intros N p HN Hp.
    Transparent N_bounce_pb. unfold N_bounce_pb. Opaque N_bounce_pb.
    assert (H1 : W (p - 2) 3 + 10 <= f_omega N) by (apply W_upper_omega; lia).
    pose proof (f_omega_dbl N ltac:(lia)) as HN_dbl.
    pose proof (f_omega_id N) as HN_id.
    pose proof (f_omega_dbl (f_omega N) ltac:(lia)) as Hfw_dbl.
    pose proof (f_omega_id (f_omega N)) as Hfw_id.
    assert (H2 : W (p - 2) (W (p - 2) 3 + 4) + 10 <= f_omega (f_omega (f_omega N))).
    { apply W_upper_omega; lia. }
    pose proof (iter3_f_omega_le_f_omega1 N ltac:(lia)) as H3.
    cbn [iter] in H3.
    pose proof (f_omega1_id N) as Hf1_id.
    split; cbn [fst snd]; lia.
  Qed.

  Lemma Phase1_upper : forall N pa,
    13 <= N -> ub N pa -> ub (f_omega2 N) (Phase1_pa pa).
  Proof.
    intros N [p a] HN [Hp Ha]. cbn [fst snd] in *.
    Transparent Phase1_pa. unfold Phase1_pa. Opaque Phase1_pa.
    pose proof (N_bounce_pb_upper N p HN Hp) as Hnb.
    set (m := (a / 2 + 2) / 3 - 2) in *.
    pose proof (f_omega1_id N) as Hf1_id.
    pose proof (Kd_iter_upper m (f_omega1 N) (N_bounce_pb (p - 2)) ltac:(lia) Hnb) as Hkd.
    pose proof (iter_ge f_omega1 f_omega1_id (2 * m) (f_omega1 N)) as Hge.
    pose proof (Kc_full_upper (iter (2 * m) f_omega1 (f_omega1 N)) _ ltac:(lia) Hkd) as Hkc.
    eapply ub_mono; [| exact Hkc].
    rewrite <- iter_S'.
    change (f_omega1 (iter (S (2 * m)) f_omega1 N)) with (iter (S (S (2 * m))) f_omega1 N).
    Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
    apply iter_mono_n; [apply f_omega1_id | unfold m; mods; lia].
  Qed.

  Lemma Phase2_upper : forall N pa,
    13 <= N -> ub N pa -> ub (f_omega2 N) (Phase2_pa pa).
  Proof.
    intros N [p a] HN [Hp Ha]. cbn [fst snd] in *.
    Transparent Phase2_pa. unfold Phase2_pa. Opaque Phase2_pa.
    pose proof (N_bounce_pb_upper N p HN Hp) as Hnb.
    set (m := (a / 2 + 2) / 3 - 1) in *.
    pose proof (f_omega1_id N) as Hf1_id.
    pose proof (Kd_iter_upper m (f_omega1 N) (N_bounce_pb (p - 2)) ltac:(lia) Hnb) as Hkd.
    pose proof (iter_ge f_omega1 f_omega1_id (2 * m) (f_omega1 N)) as Hge.
    pose proof (Kc_full_upper (iter (2 * m) f_omega1 (f_omega1 N)) _ ltac:(lia) Hkd) as Hkc.
    eapply ub_mono; [| exact Hkc].
    rewrite <- iter_S'.
    change (f_omega1 (iter (S (2 * m)) f_omega1 N)) with (iter (S (S (2 * m))) f_omega1 N).
    Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
    apply iter_mono_n; [apply f_omega1_id | unfold m; mods; lia].
  Qed.

  Lemma Outer_step_old_upper : forall N pa,
    13 <= N -> ub N pa -> ub (iter 2 f_omega2 N) (Outer_step_old pa).
  Proof.
    intros N pa HN Hub. rewrite Outer_step_old_unfold. cbn [iter].
    pose proof (Phase1_upper N pa HN Hub) as H1.
    pose proof (f_omega2_id N) as Hf2_id.
    exact (Phase2_upper (f_omega2 N) (Phase1_pa pa) ltac:(lia) H1).
  Qed.

  Lemma Outer_loop_old_upper : forall E N pa,
    13 <= N -> ub N pa -> ub (iter (2 * E) f_omega2 N) (iter E Outer_step_old pa).
  Proof.
    induction E as [| E IHE]; intros N pa HN Hub.
    - change (2 * 0) with 0. cbn [iter]. exact Hub.
    - replace (2 * S E) with (2 + 2 * E) by lia.
      rewrite iter_add. cbn [iter].
      pose proof (IHE N pa HN Hub) as H1.
      pose proof (iter_ge f_omega2 f_omega2_id (2 * E) N) as Hge.
      exact (Outer_step_old_upper (iter (2 * E) f_omega2 N) (iter E Outer_step_old pa) ltac:(lia) H1).
  Qed.

  Lemma W3_3_le_fw13 : W 3 3 + 10 <= f_omega 13.
  Proof.
    pose proof (W_upper_10 3 3) as H1.
    change (3 + 1) with 4 in H1. change (3 + 10) with 13 in H1.
    pose proof (f_level_mono 9 4 13 ltac:(lia)) as H2.
    change (9 + 4) with 13 in H2.
    Transparent f_omega. unfold f_omega. Opaque f_omega.
    set (w := W 3 3) in *; set (a := f 4 13) in *; set (b := f 13 13) in *; clearbody w a b.
    lia.
  Qed.

  Lemma E0_old_le_fw13 : 2 * E0_old + 3 <= f_omega 13.
  Proof.
    unfold E0_old. pose proof W3_3_le_fw13 as Hw.
    set (w := W 3 3) in *; set (M := f_omega 13) in *; clearbody w M.
    mods; lia.
  Qed.

  Lemma pb_boot_upper : ub (f_omega1 (f_omega 13)) pb_boot.
  Proof.
    unfold pb_boot. rewrite W2_1_val. change (38 + 4) with 42.
    pose proof W3_3_le_fw13 as Hw.
    pose proof (f_omega_dbl 13 ltac:(lia)) as HM_ge.
    set (M := f_omega 13) in *.
    pose proof (f_omega_dbl M ltac:(clear - HM_ge; lia)) as HM_dbl.
    pose proof (f_omega_id M) as HM_id.
    pose proof (f_omega_le_f_omega1 M ltac:(clear - HM_ge; lia)) as Hle1.
    pose proof (iter2_f_omega_le_f_omega1 M ltac:(clear - HM_ge; lia)) as H2.
    cbn [iter] in H2.
    assert (Hp_le : 3 + W 3 3 / 2 + 10 <= f_omega M).
    { clear - Hw HM_ge HM_dbl.
      set (w := W 3 3) in *; clearbody w M. mods; lia. }
    assert (Hp1_le : 3 + W 3 3 / 2 + 1 <= f_omega M) by (clear - Hp_le; lia).
    assert (Hs_le : W (3 + W 3 3 / 2) 42 + 10 <= f_omega (f_omega M)).
    { apply W_upper_omega; [clear - HM_ge HM_id; lia | exact Hp1_le | clear - HM_ge HM_dbl; lia]. }
    split; cbn [fst snd].
    - exact (Nat.le_trans _ _ _ Hp_le Hle1).
    - exact (Nat.le_trans _ _ _ Hs_le H2).
  Qed.

  Lemma pa_init_upper : ub (f_omega2 (f_omega 13)) pa_init.
  Proof.
    unfold pa_init.
    set (M := f_omega 13) in *.
    pose proof (f_omega_dbl 13 ltac:(lia)) as HM_ge.
    pose proof (f_omega1_id M) as HM1_id.
    pose proof pb_boot_upper as Hpb. fold M in Hpb.
    pose proof (Kd_iter_upper 8 (f_omega1 M) pb_boot ltac:(clear - HM_ge HM1_id; lia) Hpb) as Hkd.
    pose proof (iter_ge f_omega1 f_omega1_id (2 * 8) (f_omega1 M)) as Hge.
    pose proof (Kc_full_upper (iter (2 * 8) f_omega1 (f_omega1 M)) (Kd_iter 8 pb_boot)
                  ltac:(clear - HM_ge HM1_id Hge; lia) Hkd) as Hkc.
    eapply ub_mono; [| exact Hkc].
    rewrite <- iter_S'.
    change (f_omega1 (iter (S (2 * 8)) f_omega1 M)) with (iter 18 f_omega1 M).
    Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
    apply iter_mono_n; [apply f_omega1_id | clear - HM_ge; lia].
  Qed.

  Lemma N_old_upper : N_old <= f_omega3 (f_omega 13).
  Proof.
    unfold N_old, pa_final_old.
    set (M := f_omega 13) in *.
    pose proof (f_omega_dbl 13 ltac:(lia)) as HM_ge.
    pose proof (f_omega2_id M) as HM2_id.
    pose proof pa_init_upper as Hinit. fold M in Hinit.
    pose proof (Outer_loop_old_upper E0_old (f_omega2 M) pa_init
                  ltac:(clear - HM_ge HM2_id; lia) Hinit) as Hloop.
    pose proof (iter_ge f_omega2 f_omega2_id (2 * E0_old) (f_omega2 M)) as Hge.
    pose proof (Phase1_upper (iter (2 * E0_old) f_omega2 (f_omega2 M)) _
                  ltac:(clear - HM_ge HM2_id Hge; lia) Hloop) as Hfin.
    set (B := f_omega2 (iter (2 * E0_old) f_omega2 (f_omega2 M))) in *.
    destruct Hfin as [Hp Ha].
    assert (HB_ge : 1 <= B) by (unfold B; pose proof (f_omega2_id (iter (2 * E0_old) f_omega2 (f_omega2 M))); clear - HM_ge HM2_id Hge H; lia).
    assert (H2B : 2 * B <= f_omega2 B).
    { pose proof (f_omega_dbl B HB_ge) as H1.
      pose proof (f_omega_le_f_omega1 B HB_ge) as H2.
      pose proof (f_omega1_le_f_omega2 B HB_ge) as H3.
      clear - H1 H2 H3. lia. }
    assert (Hfin_le : fst (Phase1_pa (iter E0_old Outer_step_old pa_init)) +
                      snd (Phase1_pa (iter E0_old Outer_step_old pa_init)) + 6 <= f_omega2 B).
    { clear - Hp Ha H2B. clearbody B. lia. }
    transitivity (f_omega2 B); [exact Hfin_le |].
    unfold B. rewrite <- iter_S'.
    change (f_omega2 (f_omega2 (iter (S (2 * E0_old)) f_omega2 M)))
      with (iter (S (S (S (2 * E0_old)))) f_omega2 M).
    Transparent f_omega3. unfold f_omega3. Opaque f_omega3.
    apply iter_mono_n; [apply f_omega2_id |].
    pose proof E0_old_le_fw13 as HE. fold M in HE.
    clear - HE. lia.
  Qed.

  Opaque E0_old pb_boot pa_init pa_final_old N_old.
  Strategy opaque [E0_old pb_boot pa_init pa_final_old N_old].

End M14_Old.

(** ** Exact Champion Superiority Theorem: sigma(M14_fw3) < sigma(M14_fw3x4) *)

Lemma fw4_ge_13 : 13 <= f_omega 4.
Proof.
  assert (Hf24 : f 2 4 = 64).
  { rewrite f_S. cbn [iter]. rewrite !f1. lia. }
  pose proof (f_level_mono 2 2 4 ltac:(lia)) as Hlv.
  change (2 + 2) with 4 in Hlv.
  Transparent f_omega. unfold f_omega. Opaque f_omega.
  set (a := f 2 4) in *; set (b := f 4 4) in *; clearbody a b.
  lia.
Qed.

Lemma N_old_lt_N_final : M14_Old.N_old < N_final.
Proof.
  pose proof M14_Old.N_old_upper as Hold.
  pose proof N_final_gt_fw3x4 as Hnew.
  pose proof fw4_ge_13 as H13.
  assert (H1 : f_omega 13 <= f_omega3 (f_omega 4)).
  { transitivity (f_omega (f_omega 4)).
    - apply f_omega_mono; exact H13.
    - apply f_omega_le_f_omega3; clear - H13; lia. }
  assert (H2 : f_omega3 (f_omega 13) <= iter 2 f_omega3 (f_omega 4)).
  { cbn [iter]. apply f_omega3_mono; exact H1. }
  assert (H3 : iter 2 f_omega3 (f_omega 4) <= iter 4 f_omega3 (f_omega 4)).
  { apply iter_mono_n; [apply f_omega3_id | lia]. }
  exact (Nat.le_lt_trans _ _ _ Hold (Nat.le_lt_trans _ _ _ H2 (Nat.le_lt_trans _ _ _ H3 Hnew))).
Qed.

Theorem beats_M14_fw3_exact :
  (exists c_old n_old c_new n_new,
     c0 -[ tm_M14_fw3_tnf ]->* c_old /\ halted tm_M14_fw3_tnf c_old /\ ones c_old n_old /\
     c0 -[ tm_tnf ]->* c_new /\ halted tm_tnf c_new /\ ones c_new n_new /\
     n_old < n_new) /\
  (forall c_old n_old,
     c0 -[ tm_M14_fw3_tnf ]->* c_old -> halted tm_M14_fw3_tnf c_old -> ones c_old n_old ->
     n_old < N_final).
Proof.
  destruct M14_Old.score_exact_old_tnf as [c_old0 [Ho_run [Ho_halt Ho_ones]]].
  destruct score_exact_tnf as [c_new0 [Hn_run [Hn_halt Hn_ones]]].
  pose proof N_old_lt_N_final as Hlt.
  split.
  - exists c_old0, M14_Old.N_old, c_new0, N_final.
    repeat split; assumption.
  - intros c_old n_old Hrun Hhalt Hones.
    assert (Hc_eq : c_old = c_old0)
      by exact (evstep_halted_unique tm_M14_fw3_tnf c0 c_old c_old0 Hrun Hhalt Ho_run Ho_halt).
    subst c_old.
    assert (Hn_eq : n_old = M14_Old.N_old)
      by exact (ones_unique c_old0 n_old M14_Old.N_old Hones Ho_ones).
    subst n_old.
    exact Hlt.
Qed.

(** ** Zero-Axiom Audit Checks *)

Print Assumptions tm_str_pin.
Print Assumptions tm_tnf_str_pin.
Print Assumptions tm_M14_fw3_str_pin.
Print Assumptions tm_M14_fw3_tnf_str_pin.
Print Assumptions render_tm_inj.
Print Assumptions halt.
Print Assumptions score_exact.
Print Assumptions sigma_bound.
Print Assumptions halt_tnf.
Print Assumptions score_exact_tnf.
Print Assumptions sigma_bound_tnf.
Print Assumptions beats_M14_fw3_exact.
