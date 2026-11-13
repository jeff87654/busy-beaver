(** * Upper bound for the 11-state machine M11b: sigma < f_(omega+1)(f_omega(f_omega 6)) *)

(** Main results (no axioms):
      Theorem sigma_upper_bound_m11 :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        N + 1 < f_omega1 (f_omega (f_omega 6)).
      Theorem sigma_bracket_m11 :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        f_omega1 (f_omega (f_omega 5)) < N /\ N + 1 < f_omega1 (f_omega (f_omega 6)).
    N is the number of ones at the halt and sigma = N + 1 (the halting transition F0 writes a 1 on a 0).

    Outline:
      W_le        W_j(b) <= f_j(f_j(b + 2)) for every level j.
      j7_upper    the bridge index j7 = 6 + W_4(1)/2 + W_6(1)/2 satisfies j7 + 10 <= f_omega 6.
      bridge_upper, a10_upper
                  the token count c10 and the start pair of phase 2 are at most f_omega (j7 + 8).
      phase2_final
                  with M = max(level, accumulator), one Kc step gives M' <= f_omega(M), so c Kc steps and the
                  halt give N + 1 <= f_omega^(c+1)(M_0) <= f_(omega+1)(X) whenever c + 1 <= X and M_0 <= X.
    Every closed tower stays opaque: the lemmas are proved for variables and only instantiated at the end. *)

From BB8 Require Import Individual112.
From BB8 Require Import BB11_M11b BB11_M11b_fgh.
From Coq Require Import Lia PeanoNat List.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

Opaque W Kc pa1 br1 pa2_0 c2_0 pa_end f f_omega f_omega1.

(** ** Iteration helpers *)

Lemma iter_mul : forall n m (g : nat -> nat) x, iter (n * m) g x = iter n (iter m g) x.
Proof.
  induction n as [| n IH]; intros m g x; [reflexivity |].
  change (S n * m) with (m + n * m). rewrite iter_add, IH. reflexivity.
Qed.

Lemma iter_le_dom : forall (g h : nat -> nat),
  (forall x, 2 <= x -> g x <= h x) ->
  (forall a b, a <= b -> h a <= h b) ->
  (forall x, 2 <= x -> 2 <= g x) ->
  forall n x, 2 <= x -> iter n g x <= iter n h x /\ 2 <= iter n g x.
Proof.
  intros g h Hgh Hh Hg2. induction n as [| n IH]; intros x Hx; cbn [iter].
  - split; lia.
  - destruct (IH x Hx) as [H1 H2]. split.
    + pose proof (Hgh _ H2). pose proof (Hh _ _ H1). lia.
    + apply Hg2. exact H2.
Qed.

Lemma f_0 : forall n, f 0 n = S n.
Proof. Transparent f. intros n. reflexivity. Qed.
Opaque f.

Lemma iter_f_level : forall k L n x, k <= L -> 1 <= x -> iter n (f k) x <= iter n (f L) x.
Proof.
  intros k L n x HkL Hx. induction n as [| n IH]; cbn [iter]; [lia |].
  pose proof (iter_ge (f k) (f_id k) n x) as Hge.
  pose proof (f_level_mono (L - k) k (iter n (f k) x) ltac:(lia)) as H1.
  replace (L - k + k) with L in H1 by lia.
  pose proof (f_mono L _ _ IH). lia.
Qed.

Lemma f_ge_plus2 : forall j x, 1 <= j -> 2 <= x -> x + 2 <= f j x.
Proof. intros j x Hj Hx. pose proof (f_dbl j x Hj). lia. Qed.

Lemma f_omega_unfold : forall n, f_omega n = f n n.
Proof. Transparent f_omega. intros n. reflexivity. Qed.
Opaque f_omega.

Lemma f_omega1_unfold : forall n, f_omega1 n = iter n f_omega n.
Proof. Transparent f_omega1. intros n. reflexivity. Qed.
Opaque f_omega1.

(** f_omega n + 1 <= f_omega (n + 1). *)
Lemma fo_succ : forall n, 1 <= n -> f_omega n + 1 <= f_omega (S n).
Proof.
  intros n Hn. rewrite !f_omega_unfold, f_S.
  pose proof (iter_mono_n (f n) (f_id n) 2 (S n) (S n) ltac:(lia)) as H1.
  change (iter 2 (f n) (S n)) with (f n (f n (S n))) in H1.
  pose proof (f_dbl n (f n (S n)) Hn) as H2.
  pose proof (f_mono n n (S n) ltac:(lia)) as H3.
  pose proof (f_gt n n Hn) as H4.
  lia.
Qed.

Lemma f_omega_4x : forall M, 2 <= M -> 4 * M <= f_omega M.
Proof.
  intros M HM. rewrite f_omega_unfold.
  pose proof (f_level_mono (M - 2) 2 M ltac:(lia)) as H1.
  replace (M - 2 + 2) with M in H1 by lia.
  rewrite f_S in H1.
  pose proof (iter_mono_n (f 1) (f_id 1) 2 M M HM) as H2.
  change (iter 2 (f 1) M) with (f 1 (f 1 M)) in H2. rewrite !f1 in H2.
  lia.
Qed.

(** f_(omega+1) is strictly increasing. *)
Lemma f_omega1_S_lt : forall u, 1 <= u -> f_omega1 u < f_omega1 (S u).
Proof.
  intros u Hu. rewrite !f_omega1_unfold.
  change (iter (S u) f_omega (S u)) with (f_omega (iter u f_omega (S u))).
  pose proof (iter_mono_x f_omega f_omega_mono u u (S u) ltac:(lia)).
  pose proof (iter_ge f_omega f_omega_id u (S u)).
  pose proof (f_omega_dbl (iter u f_omega (S u)) ltac:(lia)).
  lia.
Qed.

Lemma f_omega1_lt : forall x y, 1 <= x -> x < y -> f_omega1 x < f_omega1 y.
Proof.
  intros x y Hx Hxy. pose proof (f_omega1_S_lt x Hx).
  pose proof (f_omega1_mono (S x) y Hxy). lia.
Qed.

(** ** W against the fast-growing hierarchy *)

Lemma W_le : forall j b, W j b <= iter 2 (f j) (b + 2).
Proof.
  induction j as [| j IHj]; intros b.
  - rewrite W_0. change (iter 2 (f 0) (b + 2)) with (f 0 (f 0 (b + 2))).
    pose proof (f_0 (b + 2)) as E1. pose proof (f_0 (f 0 (b + 2))) as E2. lia.
  - destruct j as [| j'].
    + rewrite W1_val. change (iter 2 (f 1) (b + 2)) with (f 1 (f 1 (b + 2))).
      pose proof (f1 (b + 2)) as E1. pose proof (f1 (f 1 (b + 2))) as E2. lia.
    + set (j := S j') in *.
      rewrite W_S.
      (* step A: each W_j application is at most three f_j applications *)
      assert (Hdom : forall x, 2 <= x -> W j x <= iter 3 (f j) x).
      { intros x Hx. pose proof (IHj x) as H1.
        pose proof (f_ge_plus2 j x ltac:(unfold j; lia) Hx) as H2.
        pose proof (iter_mono_x (f j) (f_mono j) 2 (x + 2) (f j x) H2) as H3.
        rewrite (iter_S' 2 (f j) x). lia. }
      destruct (iter_le_dom (W j) (iter 3 (f j)) Hdom
                  (iter_mono_x (f j) (f_mono j) 3)
                  (fun x Hx => ltac:(pose proof (W_grow j x); lia)) (S b) 2 ltac:(lia)) as [HA _].
      rewrite <- iter_mul in HA.
      (* step B: 3 (b + 1) applications of f_j from 2 fit inside f_(j+1) (f_(j+1) (b + 2)) *)
      set (y := f (S j) (b + 2)).
      assert (Hy : 3 * S b <= y /\ 2 <= y).
      { unfold y. rewrite f_S.
        pose proof (iter_mono_n (f j) (f_id j) 2 (b + 2) (b + 2) ltac:(lia)) as H1.
        change (iter 2 (f j) (b + 2)) with (f j (f j (b + 2))) in H1.
        pose proof (f_dbl j (b + 2) ltac:(unfold j; lia)) as H2.
        pose proof (f_dbl j (f j (b + 2)) ltac:(unfold j; lia)) as H3.
        lia. }
      destruct Hy as [Hy1 Hy2].
      pose proof (iter_mono_n (f j) (f_id j) (S b * 3) y 2 ltac:(lia)) as HB1.
      pose proof (iter_mono_x (f j) (f_mono j) y 2 y Hy2) as HB2.
      assert (HB3 : iter y (f j) y = f (S j) y) by (rewrite f_S; reflexivity).
      assert (HB4 : iter 2 (f (S j)) (b + 2) = f (S j) y) by reflexivity.
      rewrite HB4. lia.
Qed.

Lemma W_q1 : forall q, W q 1 <= f (S q) 3.
Proof.
  intros q. pose proof (W_le q 1) as H1. change (1 + 2) with 3 in H1.
  pose proof (iter_mono_n (f q) (f_id q) 2 3 3 ltac:(lia)) as H2.
  rewrite f_S. lia.
Qed.

Lemma W_dom_L : forall j L y, j <= L -> 1 <= L -> 2 <= y -> W j y <= iter 3 (f L) y.
Proof.
  intros j L y HjL HL Hy.
  pose proof (W_le j y) as H1.
  pose proof (iter_f_level j L 2 (y + 2) HjL ltac:(lia)) as H2.
  pose proof (f_ge_plus2 L y HL Hy) as H3.
  pose proof (iter_mono_x (f L) (f_mono L) 2 (y + 2) (f L y) H3) as H4.
  rewrite (iter_S' 2 (f L) y). lia.
Qed.

(** ** Phase 1: the bridge index j7 is below f_omega 6 *)

Lemma W61_le : W 6 1 <= iter 5 (f 5) 4.
Proof.
  rewrite W_S. change (iter 2 (W 5) 2) with (W 5 (W 5 2)).
  pose proof (W_le 5 2) as H1.
  pose proof (W_grow 5 2) as H2.
  pose proof (W_dom_L 5 5 (W 5 2) ltac:(lia) ltac:(lia) ltac:(lia)) as H3.
  pose proof (iter_mono_x (f 5) (f_mono 5) 3 (W 5 2) (iter 2 (f 5) (2 + 2)) H1) as H4.
  rewrite <- (iter_add 3 2 (f 5) (2 + 2)) in H4.
  change (2 + 2) with 4 in H1, H4. change (3 + 2) with 5 in H4.
  lia.
Qed.

Lemma W41_le : W 4 1 <= iter 5 (f 5) 4.
Proof.
  pose proof (W_q1 4) as H1.
  pose proof (f_mono 5 3 4 ltac:(lia)) as H2.
  pose proof (iter_mono_n (f 5) (f_id 5) 1 5 4 ltac:(lia)) as H3.
  change (iter 1 (f 5) 4) with (f 5 4) in H3. lia.
Qed.

Lemma j7_upper : j7_1 + 10 <= f_omega 6.
Proof.
  unfold j7_1, p'1, k1.
  pose proof W61_le as H6. pose proof W41_le as H4.
  set (Z := iter 5 (f 5) 4) in *.
  assert (HZ16 : 16 <= Z).
  { unfold Z. pose proof (iter_mono_n (f 5) (f_id 5) 2 5 4 ltac:(lia)) as H1.
    change (iter 2 (f 5) 4) with (f 5 (f 5 4)) in H1.
    pose proof (f_dbl 5 4 ltac:(lia)). pose proof (f_dbl 5 (f 5 4) ltac:(lia)). lia. }
  assert (HF : 2 * Z <= f_omega 6).
  { rewrite f_omega_unfold, f_S. unfold Z.
    change (iter 6 (f 5) 6) with (f 5 (iter 5 (f 5) 6)).
    pose proof (iter_mono_x (f 5) (f_mono 5) 5 4 6 ltac:(lia)) as H1.
    pose proof (f_dbl 5 (iter 5 (f 5) 6) ltac:(lia)) as H2.
    lia. }
  clearbody Z.
  generalize (W 4 1) (W 6 1) H4 H6. intros w4 w6 Hw4 Hw6.
  clear - Hw4 Hw6 HZ16 HF. generalize (f_omega 6) HF. intros F HF'.
  assert (w4 / 2 <= Z / 2) by (apply Nat.Div0.div_le_mono; lia).
  assert (w6 / 2 <= Z / 2) by (apply Nat.Div0.div_le_mono; lia).
  assert (2 * (Z / 2) <= Z) by (apply Nat.Div0.mul_div_le).
  lia.
Qed.

(** ** The bridge: c10 and the start of phase 2 are at most f_omega (j7 + 8) *)

Lemma bridge_upper : forall p' j7, p' <= j7 -> 6 <= j7 ->
  W (j7 + 7) (W j7 (W j7 (W p' 1))) <= f_omega (j7 + 8).
Proof.
  intros p' j7 Hp Hj.
  set (L := j7 + 7).
  assert (HL : 1 <= L) by (unfold L; lia).
  (* W p' 1 <= f_L^3 (3) *)
  pose proof (W_q1 p') as H1. rewrite f_S in H1.
  pose proof (iter_f_level p' L 3 3 ltac:(unfold L; lia) ltac:(lia)) as H1'.
  set (w1 := W p' 1) in *.
  assert (Hw1 : 2 <= w1) by (unfold w1; pose proof (W_grow p' 1); lia).
  (* W j7 w1 <= f_L^6 (3) *)
  pose proof (W_dom_L j7 L w1 ltac:(unfold L; lia) HL Hw1) as H2.
  pose proof (iter_mono_x (f L) (f_mono L) 3 w1 (iter 3 (f L) 3) ltac:(lia)) as H2'.
  rewrite <- (iter_add 3 3 (f L) 3) in H2'.
  set (w2 := W j7 w1) in *.
  assert (Hw2 : 2 <= w2) by (unfold w2; pose proof (W_grow j7 w1); lia).
  (* W j7 w2 <= f_L^9 (3) *)
  pose proof (W_dom_L j7 L w2 ltac:(unfold L; lia) HL Hw2) as H3.
  pose proof (iter_mono_x (f L) (f_mono L) 3 w2 (iter (3 + 3) (f L) 3) ltac:(lia)) as H3'.
  rewrite <- (iter_add 3 (3 + 3) (f L) 3) in H3'.
  set (w9 := W j7 w2) in *.
  assert (Hw9 : 2 <= w9) by (unfold w9; pose proof (W_grow j7 w2); lia).
  (* W L w9 <= f_L^12 (3) <= f_L^(L+1) (L+1) = f_omega (L+1) *)
  pose proof (W_dom_L L L w9 ltac:(lia) HL Hw9) as H4.
  pose proof (iter_mono_x (f L) (f_mono L) 3 w9 (iter (3 + (3 + 3)) (f L) 3) ltac:(lia)) as H4'.
  rewrite <- (iter_add 3 (3 + (3 + 3)) (f L) 3) in H4'.
  pose proof (iter_mono_n (f L) (f_id L) (3 + (3 + (3 + 3))) (S L) 3 ltac:(unfold L; lia)) as H5.
  pose proof (iter_mono_x (f L) (f_mono L) (S L) 3 (S L) ltac:(lia)) as H6.
  assert (H7 : iter (S L) (f L) (S L) = f_omega (j7 + 8)).
  { rewrite f_omega_unfold. replace (j7 + 8) with (S L) by (unfold L; lia). rewrite f_S. reflexivity. }
  lia.
Qed.

Lemma a10_upper : forall j7, W (j7 + 6) 1 <= f_omega (j7 + 8).
Proof.
  intros j7. pose proof (W_q1 (j7 + 6)) as H1.
  pose proof (f_mono (S (j7 + 6)) 3 (S (j7 + 6)) ltac:(lia)) as H2.
  pose proof (f_omega_unfold (S (j7 + 6))) as H3.
  pose proof (f_omega_mono (S (j7 + 6)) (j7 + 8) ltac:(lia)) as H4.
  lia.
Qed.

(** ** Phase 2: M = max(level, accumulator) grows by at most one f_omega per Kc step *)

Lemma Kc_up : forall p a, 3 <= Nat.max p a ->
  Nat.max (fst (Kc (p, a))) (snd (Kc (p, a))) <= f_omega (Nat.max p a) /\ 4 <= snd (Kc (p, a)).
Proof.
  intros p a HM. rewrite Kc_unfold. cbn [fst snd].
  set (M := Nat.max p a) in *.
  assert (Hp : p <= M) by (unfold M; lia).
  assert (Ha : a <= M) by (unfold M; lia).
  pose proof (f_omega_dbl M ltac:(lia)) as H1.
  pose proof (W_q1 (p - 1)) as H2.
  pose proof (f_mono (S (p - 1)) 3 M ltac:(lia)) as H3.
  pose proof (f_level_mono (M - S (p - 1)) (S (p - 1)) M ltac:(lia)) as H4.
  replace (M - S (p - 1) + S (p - 1)) with M in H4 by lia.
  pose proof (f_omega_unfold M) as H5.
  pose proof (W_grow (p - 1) 1) as H6.
  split; [| lia].
  assert (p + a / 2 <= 2 * M) by (pose proof (Nat.Div0.div_le_upper_bound a 2 a ltac:(lia)); lia).
  lia.
Qed.

Lemma Kc_iter_up : forall c p a, 3 <= Nat.max p a ->
  Nat.max (fst (iter c Kc (p, a))) (snd (iter c Kc (p, a))) <= iter c f_omega (Nat.max p a) /\
  3 <= Nat.max (fst (iter c Kc (p, a))) (snd (iter c Kc (p, a))).
Proof.
  intros c p a HM. induction c as [| c IH]; cbn [iter fst snd]; [split; lia |].
  destruct (iter c Kc (p, a)) as [p1 a1]. cbn [fst snd] in IH.
  destruct IH as [IH1 IH2].
  destruct (Kc_up p1 a1 IH2) as [K1 K2].
  pose proof (f_omega_mono _ _ IH1). split; lia.
Qed.

Lemma phase2_final : forall c p a X, 3 <= Nat.max p a -> S c <= X -> Nat.max p a <= X ->
  fst (iter c Kc (p, a)) + snd (iter c Kc (p, a)) + 5 <= f_omega1 X.
Proof.
  intros c p a X HM Hc HX.
  destruct (Kc_iter_up c p a HM) as [H1 H2].
  set (Mc := Nat.max (fst (iter c Kc (p, a))) (snd (iter c Kc (p, a)))) in *.
  assert (H3 : fst (iter c Kc (p, a)) + snd (iter c Kc (p, a)) + 5 <= 4 * Mc) by (unfold Mc; lia).
  pose proof (f_omega_4x Mc ltac:(lia)) as H4.
  pose proof (f_omega_mono _ _ H1) as H5.
  change (f_omega (iter c f_omega (Nat.max p a))) with (iter (S c) f_omega (Nat.max p a)) in H5.
  pose proof (iter_mono_n f_omega f_omega_id (S c) X (Nat.max p a) Hc) as H6.
  pose proof (iter_mono_x f_omega f_omega_mono X (Nat.max p a) X HX) as H7.
  rewrite f_omega1_unfold. lia.
Qed.

(** ** The run of M11b *)

Lemma j7_ge6 : 6 <= j7_1.
Proof. unfold j7_1, p'1. generalize (W 4 1 / 2) k1. intros. lia. Qed.

Lemma p'1_le_j7 : p'1 <= j7_1.
Proof. unfold j7_1. generalize p'1 k1. intros. lia. Qed.

Lemma N_upper : fst pa_end + snd pa_end + 5 <= f_omega1 (f_omega (j7_1 + 8) + 1).
Proof.
  rewrite pa_end_def, pa2_0_val.
  pose proof (bridge_upper p'1 j7_1 p'1_le_j7 j7_ge6) as Hw10.
  assert (Hc : c2_0 <= f_omega (j7_1 + 8)).
  { rewrite c2_0_val. unfold w10_1, j9_1, w9_1.
    pose proof (W_grow (j7_1 + 7) (W j7_1 (W j7_1 (W p'1 1)))) as Hg.
    generalize (W (j7_1 + 7) (W j7_1 (W j7_1 (W p'1 1)))) Hw10 Hg. intros w H1 H2.
    generalize (f_omega (j7_1 + 8)) H1. intros F HF.
    pose proof (Nat.Div0.mul_div_le w 2). lia. }
  pose proof (a10_upper j7_1) as Ha.
  pose proof (W_grow p10_1 1) as Ha4.
  pose proof (f_omega_id (j7_1 + 8)) as Hid.
  unfold p10_1 in *.
  apply phase2_final; lia.
Qed.

Theorem sigma_upper_bound_m11 :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  N + 1 < f_omega1 (f_omega (f_omega 6)).
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (fst pa_end + snd pa_end + 4).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof N_upper as HN.
  pose proof j7_upper as Hj.
  pose proof (fo_succ (j7_1 + 8) ltac:(lia)) as F1.
  pose proof (fo_succ (j7_1 + 9) ltac:(lia)) as F2.
  pose proof (f_omega_mono (S (j7_1 + 9)) (f_omega 6) ltac:(lia)) as F3.
  replace (S (j7_1 + 8)) with (j7_1 + 9) in F1 by lia.
  pose proof (f_omega1_lt (f_omega (j7_1 + 8) + 1) (f_omega (f_omega 6)) ltac:(lia) ltac:(lia)) as F4.
  lia.
Qed.

Theorem sigma_bracket_m11 :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  f_omega1 (f_omega (f_omega 5)) < N /\ N + 1 < f_omega1 (f_omega (f_omega 6)).
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (fst pa_end + snd pa_end + 4).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof pa_end_bound as HL.
  pose proof N_upper as HN.
  pose proof j7_upper as Hj.
  pose proof (fo_succ (j7_1 + 8) ltac:(lia)) as F1.
  pose proof (fo_succ (j7_1 + 9) ltac:(lia)) as F2.
  pose proof (f_omega_mono (S (j7_1 + 9)) (f_omega 6) ltac:(lia)) as F3.
  replace (S (j7_1 + 8)) with (j7_1 + 9) in F1 by lia.
  pose proof (f_omega1_lt (f_omega (j7_1 + 8) + 1) (f_omega (f_omega 6)) ltac:(lia) ltac:(lia)) as F4.
  lia.
Qed.

Print Assumptions sigma_upper_bound_m11.
Print Assumptions sigma_bracket_m11.
