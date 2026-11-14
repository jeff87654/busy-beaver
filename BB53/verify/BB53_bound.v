(** * Lower-bound proof for the new BB(5,3) TNF f_omega^2 champion:
      1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB

    Main certified theorems (zero axioms):
      1. [sigma_exceeds_f_omega2]:
           f_omega (knuth 8 2 3) < sigma /\ f_omega (f_omega 7) < sigma
         (certifies two nested Ackermann cascades > f_omega(2 ↑^8 3)!)
      2. [sigma_beats_official_bb43]:
           knuth 3 2 (knuth 3 2 (knuth 3 2 (2 ^ 96))) < sigma
         (strictly shatters Kropitz's official BB(4,3) pentation record
          4 * e_4 + 18 < 2 ↑^3 2 ↑^3 2 ↑^3 (2^96)!) *)

From Local Require Import Individual53 BB53_rules BB53_run.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

Fixpoint knuth (n a b : nat) : nat :=
  match n with
  | 0 => a * b
  | S n' => Nat.iter b (knuth n' a) 1
  end.

Definition f_omega (n : nat) : nat := knuth n 2 n.

Lemma iter_add : forall {X : Type} (f : X -> X) a b x,
  Nat.iter (a + b) f x = Nat.iter a f (Nat.iter b f x).
Proof.
  intros X f a. induction a as [|a IH]; intros b x.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma knuth_S : forall n a b, knuth (S n) a (S b) = knuth n a (knuth (S n) a b).
Proof. reflexivity. Qed.

Lemma knuth_S0 : forall k b, knuth (S k) 2 b = Nat.iter b (knuth k 2) 1.
Proof. reflexivity. Qed.

Lemma knuth_1 : forall k, knuth k 2 1 = 2.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - simpl. exact IH.
Qed.

Lemma knuth_2 : forall k, knuth k 2 2 = 4.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - simpl. rewrite knuth_1. exact IH.
Qed.

Lemma iter2_knuth : forall k, Nat.iter 2 (knuth k 2) 1 = 4.
Proof. intros k. simpl. rewrite knuth_1. apply knuth_2. Qed.

Lemma knuth_1_pow : forall b, knuth 1 2 b = 2 ^ b.
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rewrite knuth_S, IH. simpl. lia.
Qed.

Section ClosedForm.
Variable h kh : nat -> nat.
Hypothesis hyp : forall y, 2 * h y + 4 = kh (2 * y + 4).

Lemma iter_closed_helper : forall j x,
  2 * Nat.iter j h x + 4 = Nat.iter j kh (2 * x + 4).
Proof.
  induction j as [|j IH]; intros x.
  - simpl. lia.
  - simpl in *. rewrite hyp. rewrite (IH x). reflexivity.
Qed.
End ClosedForm.

Theorem g_closed : forall k m,
  2 * g (S k) m + 4 = knuth k 2 (2 * m + 4).
Proof.
  induction k as [|k IH]; intros m.
  - assert (E : g 1 m = 2 * m + 2).
    { assert (E2 : g 1 m = Nat.iter (2 * m + 2) (g 0) 0%nat) by reflexivity.
      rewrite E2. rewrite (iter_g0 (2 * m + 2) 0%nat). lia. }
    rewrite E. simpl. lia.
  - assert (E : g (S (S k)) m = Nat.iter (2 * m + 2) (g (S k)) 0) by reflexivity.
    rewrite E.
    rewrite (iter_closed_helper (g (S k)) (knuth k 2) IH (2 * m + 2) 0).
    change (2 * 0 + 4) with 4.
    rewrite (knuth_S0 k (2 * m + 4)).
    replace (2 * m + 4) with (2 * m + 2 + 2) by lia.
    rewrite (iter_add (knuth k 2) (2 * m + 2) 2 1).
    rewrite iter2_knuth.
    reflexivity.
Qed.

Theorem g_iter_closed : forall k n,
  2 * Nat.iter n (g k) 0%nat + 4 = knuth k 2 (n + 2).
Proof.
  intros k n. destruct k as [|k].
  - rewrite iter_g0. simpl. lia.
  - rewrite (iter_closed_helper (g (S k)) (knuth k 2) (g_closed k) n 0).
    change (2 * 0 + 4) with 4.
    rewrite (knuth_S0 k (n + 2)).
    rewrite (iter_add (knuth k 2) n 2 1).
    rewrite iter2_knuth.
    reflexivity.
Qed.

(** ** Growth and monotonicity of [g], [drain_even], [knuth], and [f_omega] *)

Section IterGrowth.
Variable f : nat -> nat.
Hypothesis Hf : forall x, f x >= S x.

Lemma iter_ge_steps : forall j, Nat.iter j f 0 >= j.
Proof.
  induction j as [|j IH].
  - simpl. lia.
  - simpl. pose proof (Hf (Nat.iter j f 0)). lia.
Qed.
End IterGrowth.

Lemma g_ge_succ : forall k x, g k x >= S x.
Proof.
  induction k as [|k IH]; intros x.
  - simpl. lia.
  - change (g (S k) x) with (Nat.iter (2 * x + 2) (g k) 0).
    pose proof (iter_ge_steps (g k) IH (2 * x + 2)).
    lia.
Qed.

Lemma iter_g_ge : forall k j, Nat.iter j (g k) 0 >= j.
Proof. intros k j. apply (iter_ge_steps (g k) (g_ge_succ k)). Qed.

Lemma drain_even_ge : forall q m, drain_even q m >= m.
Proof.
  induction q as [|q IH]; intros m.
  - simpl. lia.
  - change (drain_even (S q) m) with (drain_even q (Nat.iter (2 * m + 4) (g (2 * q + 1)) 0)).
    pose proof (IH (Nat.iter (2 * m + 4) (g (2 * q + 1)) 0)).
    pose proof (iter_g_ge (2 * q + 1) (2 * m + 4)).
    lia.
Qed.

Lemma knuth_ge_2b : forall k b, knuth k 2 b >= 2 * b.
Proof.
  induction k as [|k IHk]; intros b.
  - simpl. lia.
  - induction b as [|b IHb].
    + simpl. lia.
    + destruct b as [|b'].
      * rewrite knuth_1. lia.
      * rewrite knuth_S.
        pose proof (IHk (knuth (S k) 2 (S b'))). lia.
Qed.

Lemma knuth_pos : forall k b, knuth (S k) 2 b >= 1.
Proof.
  intros k [|b]; [simpl; lia |].
  pose proof (knuth_ge_2b (S k) (S b)). lia.
Qed.

Lemma knuth_strict_b : forall k b, knuth (S k) 2 (S b) > knuth (S k) 2 b.
Proof.
  intros k b. rewrite knuth_S.
  pose proof (knuth_ge_2b k (knuth (S k) 2 b)).
  pose proof (knuth_pos k b). lia.
Qed.

Lemma knuth_mono_b : forall k b1 b2, b1 <= b2 -> knuth k 2 b1 <= knuth k 2 b2.
Proof.
  intros [|k] b1 b2 Hle; [simpl; lia |].
  induction b2 as [|b2 IH].
  - assert (b1 = 0) by lia. subst. lia.
  - destruct (Nat.eq_dec b1 (S b2)) as [Heq | Hne]; [subst; lia |].
    assert (b1 <= b2) by lia.
    pose proof (IH H). pose proof (knuth_strict_b k b2). lia.
Qed.

Lemma knuth_step_k : forall k b, b >= 1 -> knuth k 2 b <= knuth (S k) 2 b.
Proof.
  intros k [|[|b']] Hb; [lia | rewrite !knuth_1; lia |].
  rewrite (knuth_S k 2 (S b')).
  apply knuth_mono_b.
  destruct b' as [|b'']; [rewrite knuth_1; lia |].
  pose proof (knuth_ge_2b (S k) (S (S b''))). lia.
Qed.

Lemma knuth_mono_k : forall k1 k2 b, k1 <= k2 -> b >= 1 -> knuth k1 2 b <= knuth k2 2 b.
Proof.
  intros k1 k2 b Hk Hb.
  induction k2 as [|k2 IH]; [assert (k1 = 0) by lia; subst; lia |].
  destruct (Nat.eq_dec k1 (S k2)) as [Heq | Hne]; [subst; lia |].
  assert (k1 <= k2) by lia.
  pose proof (IH H). pose proof (knuth_step_k k2 b Hb). lia.
Qed.

Lemma f_omega_mono : forall a b, 1 <= a -> a <= b -> f_omega a <= f_omega b.
Proof.
  intros a b Ha Hab. unfold f_omega.
  assert (H1 : knuth a 2 a <= knuth b 2 a) by (apply knuth_mono_k; lia).
  assert (H2 : knuth b 2 a <= knuth b 2 b) by (apply knuth_mono_b; lia).
  lia.
Qed.

Lemma knuth_4_gt_k : forall k, knuth k 2 4 >= k + 8.
Proof.
  induction k as [|k IH].
  - simpl. lia.
  - rewrite (knuth_S k 2 3).
    assert (E3 : knuth (S k) 2 3 = knuth k 2 4).
    { rewrite (knuth_S k 2 2), knuth_2. reflexivity. }
    rewrite E3.
    pose proof (knuth_ge_2b k (knuth k 2 4)).
    lia.
Qed.

(** ** Pre-Opaque evaluations on sealed constants (ZERO [lia] before [Opaque]!) *)

Definition N65536 : nat := 2 ^ 16.
Definition N2_96 : nat := 2 ^ 96.
Lemma N2_96_def : N2_96 = 2 ^ 96. Proof. reflexivity. Qed.

Lemma N65536_ge_128 : 128 <= N65536.
Proof.
  unfold N65536. change 128 with (2 ^ 7).
  apply Nat.pow_le_mono_r; lia.
Qed.

Lemma knuth2_4_eq : knuth 2 2 4 = N65536.
Proof.
  unfold N65536.
  rewrite (knuth_S 1 2 3), (knuth_S 1 2 2), knuth_2.
  assert (E4 : knuth 1 2 4 = 16) by reflexivity.
  rewrite E4. apply knuth_1_pow.
Qed.

Lemma N2_96_eq_knuth : N2_96 = knuth 1 2 96.
Proof. unfold N2_96. symmetry. apply knuth_1_pow. Qed.

Lemma f_omega_def : forall n, f_omega n = knuth n 2 n.
Proof. reflexivity. Qed.

Lemma f_omega_ge_2n : forall n, f_omega n >= 2 * n.
Proof. intros n. unfold f_omega. apply knuth_ge_2b. Qed.

Lemma M2_0_closed : 2 * M2_0 + 4 = knuth 7 2 (knuth 7 2 7).
Proof.
  pose proof M2_0_eq as HM.
  apply (f_equal (fun z => 2 * z + 4)) in HM.
  rewrite (g_closed 7 (Nat.iter 5 (g 7) 0%nat)) in HM.
  rewrite (g_iter_closed 7 5) in HM.
  exact HM.
Qed.

Lemma M3_0_closed : 2 * M3_0 + 4 = knuth (2 * M2_4) 2 (knuth (2 * M2_4) 2 7).
Proof.
  pose proof M3_0_eq as HM.
  apply (f_equal (fun z => 2 * z + 4)) in HM.
  rewrite (g_closed (2 * M2_4) (Nat.iter 5 (g (2 * M2_4)) 0%nat)) in HM.
  rewrite (g_iter_closed (2 * M2_4) 5) in HM.
  change (5 + 2) with 7 in HM.
  exact HM.
Qed.

Lemma M53_final_ge_M3_0 : M53_final >= M3_0.
Proof. rewrite M53_final_eq. apply drain_even_ge. Qed.

(** ** Mark ALL fast-growing functions and large constants [Opaque]! *)

Opaque g drain_even knuth f_omega N65536 N2_96 M2_0 M2_1 M2_2 M2_3 M2_4 M3_0 M53_final.

Lemma knuth2_5_eq : knuth 2 2 5 = knuth 1 2 (knuth 2 2 4).
Proof. apply (knuth_S 1 2 4). Qed.

Lemma knuth4_3_eq : knuth 4 2 3 = knuth 3 2 4.
Proof. rewrite (knuth_S 3 2 2), knuth_2. reflexivity. Qed.

Lemma knuth8_3_eq : knuth 8 2 3 = knuth 7 2 4.
Proof. rewrite (knuth_S 7 2 2), knuth_2. reflexivity. Qed.

Lemma N2_96_le_knuth3_5 : N2_96 <= knuth 3 2 5.
Proof.
  rewrite N2_96_eq_knuth.
  pose proof N65536_ge_128 as H128.
  pose proof knuth2_4_eq as H24.
  assert (H96 : 96 <= knuth 2 2 4) by lia.
  assert (H1 : knuth 1 2 96 <= knuth 1 2 (knuth 2 2 4)) by (apply knuth_mono_b; exact H96).
  rewrite <- knuth2_5_eq in H1.
  assert (H2 : knuth 2 2 5 <= knuth 3 2 5) by (apply knuth_mono_k; lia).
  lia.
Qed.

Lemma bb43_tower_le_fomega7 :
  knuth 3 2 (knuth 3 2 (knuth 3 2 N2_96)) <= f_omega 7.
Proof.
  rewrite (f_omega_def 7).
  pose proof N2_96_le_knuth3_5 as H0.
  assert (H43 : 5 <= knuth 4 2 3).
  { rewrite knuth4_3_eq. pose proof (knuth_4_gt_k 3). lia. }
  assert (H44 : N2_96 <= knuth 4 2 4).
  { rewrite (knuth_S 3 2 3).
    assert (Hm : knuth 3 2 5 <= knuth 3 2 (knuth 4 2 3)) by (apply knuth_mono_b; exact H43).
    lia. }
  assert (H45 : knuth 3 2 N2_96 <= knuth 4 2 5).
  { rewrite (knuth_S 3 2 4). apply knuth_mono_b; exact H44. }
  assert (H46 : knuth 3 2 (knuth 3 2 N2_96) <= knuth 4 2 6).
  { rewrite (knuth_S 3 2 5). apply knuth_mono_b; exact H45. }
  assert (H47 : knuth 3 2 (knuth 3 2 (knuth 3 2 N2_96)) <= knuth 4 2 7).
  { rewrite (knuth_S 3 2 6). apply knuth_mono_b; exact H46. }
  assert (H77 : knuth 4 2 7 <= knuth 7 2 7) by (apply knuth_mono_k; lia).
  lia.
Qed.

Lemma two_M2_4_ge : 2 * M2_4 >= knuth 8 2 3 /\ 2 * M2_4 >= f_omega 7.
Proof.
  pose proof (iter_g_ge 6 (2 * M2_0 + 4)) as G1; rewrite <- M2_1_eq in G1.
  pose proof (iter_g_ge 4 (2 * M2_1 + 4)) as G2; rewrite <- M2_2_eq in G2.
  pose proof (iter_g_ge 2 (2 * M2_2 + 4)) as G3; rewrite <- M2_3_eq in G3.
  pose proof (iter_g_ge 0 (2 * M2_3 + 4)) as G4; rewrite <- M2_4_eq in G4.
  assert (Hgrow : 2 * M2_4 >= 2 * M2_0 + 6) by lia.
  pose proof M2_0_closed as HC.
  assert (Hk83 : knuth 8 2 3 <= knuth 7 2 (knuth 7 2 7)).
  { rewrite knuth8_3_eq.
    apply knuth_mono_b.
    pose proof (knuth_ge_2b 7 7). lia. }
  assert (Hfw7 : f_omega 7 <= knuth 7 2 (knuth 7 2 7)).
  { rewrite (f_omega_def 7). pose proof (knuth_ge_2b 7 (knuth 7 2 7)). lia. }
  lia.
Qed.

Lemma M3_0_ge_fomega : 2 * M3_0 + 4 >= f_omega (2 * M2_4).
Proof.
  pose proof M3_0_closed as HM.
  rewrite (f_omega_def (2 * M2_4)).
  assert (Hge : 2 * M2_4 <= knuth (2 * M2_4) 2 7).
  { assert (H47 : knuth (2 * M2_4) 2 4 <= knuth (2 * M2_4) 2 7) by (apply knuth_mono_b; lia).
    pose proof (knuth_4_gt_k (2 * M2_4)). lia. }
  assert (Hm : knuth (2 * M2_4) 2 (2 * M2_4) <= knuth (2 * M2_4) 2 (knuth (2 * M2_4) 2 7)).
  { apply knuth_mono_b; exact Hge. }
  lia.
Qed.

Lemma knuth8_3_ge_7 : knuth 8 2 3 >= 7.
Proof.
  rewrite knuth8_3_eq.
  pose proof (knuth_4_gt_k 7). lia.
Qed.

Theorem sigma_exceeds_f_omega2 :
  f_omega (knuth 8 2 3) < sigma /\ f_omega (f_omega 7) < sigma.
Proof.
  unfold sigma.
  destruct two_M2_4_ge as [HM_k8 HM_fw7].
  pose proof M3_0_ge_fomega as HM3.
  pose proof M53_final_ge_M3_0 as Hfin.
  pose proof knuth8_3_ge_7 as Hk87.
  pose proof (f_omega_ge_2n 7) as Hfw7_ge.
  assert (Hfw_k8 : f_omega (knuth 8 2 3) <= f_omega (2 * M2_4)).
  { apply f_omega_mono; lia. }
  assert (Hfw_fw7 : f_omega (f_omega 7) <= f_omega (2 * M2_4)).
  { apply f_omega_mono; lia. }
  lia.
Qed.

Theorem sigma_beats_official_bb43 :
  knuth 3 2 (knuth 3 2 (knuth 3 2 (2 ^ 96))) < sigma.
Proof.
  rewrite <- N2_96_def.
  pose proof bb43_tower_le_fomega7 as H43.
  destruct sigma_exceeds_f_omega2 as [_ Hfw2].
  pose proof (f_omega_ge_2n (f_omega 7)) as Hge.
  lia.
Qed.

Theorem bb53_new_champion_main :
  halts tm c0 /\
  c0 -[ tm ]->* c_final /\
  halted tm c_final /\
  length final_cells = sigma /\
  (forall y, List.In y final_cells -> y <> S0) /\
  f_omega (knuth 8 2 3) < sigma /\
  f_omega (f_omega 7) < sigma /\
  knuth 3 2 (knuth 3 2 (knuth 3 2 (2 ^ 96))) < sigma.
Proof.
  destruct sigma_exceeds_f_omega2 as [H1 H2].
  split; [exact bb53_halts |].
  split; [exact reaches_final |].
  split; [exact final_halted |].
  split; [exact final_cells_count |].
  split; [exact final_cells_all_nonblank |].
  split; [exact H1 |].
  split; [exact H2 | exact sigma_beats_official_bb43].
Qed.
