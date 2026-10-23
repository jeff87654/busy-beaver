(** * Res.v : every accumulator U j x with j >= 2 has the FIXED residue rho modulo M = 2^5 3^4 5^14.

    2 U j x + 4 = arrow (S j) 2 (2 x + 4) (Abs.U_closed) is a power tower 2^^h of height h >= 20, and every
    tower of height >= 16 is T = 10119057948736 modulo 2M = 2^6 3^4 5^14 (Carmichael chain below), so
    U j x = (T - 4) / 2 = rho (mod M).  Modular powers are computed with the stdlib's verified binary
    exponentiation (Zpow_facts.Zpow_mod, Zpow_mod_correct); no huge power is ever evaluated. *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List ZArith.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules Abs.
Opaque U arrow.
From Coq Require Import Zpow_facts.

(** ** Towers *)
Fixpoint tower (h : nat) : nat :=
  match h with
  | O => 1
  | S h' => 2 ^ tower h'
  end.

Fixpoint tz (h : nat) : Z :=
  match h with
  | O => 1%Z
  | S h' => (2 ^ tz h')%Z
  end.

Lemma tz_S : forall h, tz (S h) = (2 ^ tz h)%Z.
Proof. reflexivity. Qed.

Lemma tower_tz : forall h, Z.of_nat (tower h) = tz h.
Proof.
  induction h as [| h IH]; [reflexivity |].
  change (tower (S h)) with (2 ^ tower h). rewrite tz_S, Nat2Z.inj_pow, IH. reflexivity.
Qed.

Lemma tower_le_S : forall h, tower h <= tower (S h).
Proof.
  intro h. change (tower (S h)) with (2 ^ tower h).
  pose proof (Nat.pow_gt_lin_r 2 (tower h) ltac:(lia)). lia.
Qed.

Lemma tower_mono : forall a b, a <= b -> tower a <= tower b.
Proof.
  intros a b H. induction H as [| b H IH]; [lia |].
  pose proof (tower_le_S b). lia.
Qed.

Lemma tower4_ge : 20 <= tower 4.
Proof.
  change (tower 4) with (2 ^ tower 3).
  assert (E : tower 3 = 16) by reflexivity. rewrite E.
  pose proof (Nat.pow_le_mono_r 2 5 16 ltac:(lia) ltac:(lia)) as H.
  change (2 ^ 5) with 32 in H. lia.
Qed.

(** ** Knuth arrows of 2 are towers *)
Lemma arrow_tower_ge : forall k n, 2 <= k -> exists h, n <= h /\ arrow k 2 n = tower h.
Proof.
  induction k as [| k IHk]; intros n Hk; [lia |].
  destruct (Nat.eq_dec k 1) as [-> | Hk1].
  - induction n as [| n IHn].
    + exists O. split; [lia |]. rewrite arrow_S0. reflexivity.
    + destruct IHn as [h [Hh E]]. exists (S h). split; [lia |].
      rewrite arrow_SS, arrow_1_pow, E. reflexivity.
  - destruct n as [| n].
    + exists O. split; [lia |]. rewrite arrow_S0. reflexivity.
    + rewrite arrow_SS.
      assert (G : S n <= arrow (S k) 2 n).
      { destruct n as [| [| n]].
        - rewrite arrow_S0. lia.
        - rewrite arrow_one. lia.
        - pose proof (arrow_gt_arg (S k) (S (S n)) ltac:(lia) ltac:(lia)). lia. }
      destruct (IHk (arrow (S k) 2 n) ltac:(lia)) as [h [Hh E]].
      exists h. split; [lia | exact E].
Qed.

Lemma arrow_ge4 : forall k m, 1 <= k -> 2 <= m -> 4 <= arrow k 2 m.
Proof. intros k m Hk Hm. apply pow2ge2_ge4, arrow_pow2; assumption. Qed.

Lemma arrow_tower20 : forall k n, 3 <= k -> 4 <= n -> exists h, 20 <= h /\ arrow k 2 n = tower h.
Proof.
  intros k n Hk Hn.
  destruct k as [| k1]; [lia |]. destruct n as [| [| n2]]; [lia | lia |].
  rewrite arrow_SS. rewrite arrow_SS.
  pose proof (arrow_ge4 (S k1) n2 ltac:(lia) ltac:(lia)) as G4.
  destruct (arrow_tower_ge k1 (arrow (S k1) 2 n2) ltac:(lia)) as [h1 [H1 E1]].
  rewrite E1.
  destruct (arrow_tower_ge k1 (tower h1) ltac:(lia)) as [h [H E]].
  exists h. split; [| exact E].
  pose proof (tower_mono 4 h1 ltac:(lia)). pose proof tower4_ge. lia.
Qed.

Local Open Scope Z_scope.

Lemma tz_pos : forall h, 0 < tz h.
Proof.
  induction h as [| h IH]; [simpl; lia |].
  rewrite tz_S. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma tz_le_S : forall h, tz h <= tz (S h).
Proof.
  intro h. rewrite tz_S. pose proof (tz_pos h).
  pose proof (Z.pow_gt_lin_r 2 (tz h) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma tz_big : forall h, (5 <= h)%nat -> 18446744073709551616 <= tz h.
Proof.
  intros h H. induction H as [| h H IH].
  - rewrite tz_S, tz_S. assert (E : tz 3 = 16) by reflexivity. rewrite E.
    change 18446744073709551616 with (2 ^ 64).
    apply Z.pow_le_mono_r; [lia |]. vm_compute. discriminate.
  - pose proof (tz_le_S h). lia.
Qed.

(** ** The generic step: 2^e mod 2^a q only depends on e mod L once e >= a, when 2^L = 1 (mod q) *)
Lemma pow_1mod : forall x q k, 0 < q -> 0 <= k -> x mod q = 1 mod q -> x ^ k mod q = 1 mod q.
Proof.
  intros x q k Hq Hk Hx.
  rewrite Zpower_mod, Hx, <- Zpower_mod, Z.pow_1_l by lia. reflexivity.
Qed.

Lemma step_res : forall a q L m c r e,
  m = 2 ^ a * q -> 0 <= a -> 0 < q -> 0 < L -> 2 ^ L mod q = 1 mod q ->
  a <= c -> c <= e -> e mod L = r -> c mod L = r ->
  2 ^ e mod m = 2 ^ c mod m.
Proof.
  intros a q L m c r e Hm Ha Hq HL HP Hac Hce Her Hcr.
  assert (Hd : (e - c) mod L = 0).
  { rewrite Zminus_mod, Her, Hcr, Z.sub_diag. reflexivity. }
  set (k := (e - c) / L).
  assert (Ek : e = c + L * k).
  { pose proof (Z.div_mod (e - c) L ltac:(lia)) as D. rewrite Hd in D. unfold k. lia. }
  assert (Hk : 0 <= k) by (unfold k; apply Z.div_pos; lia).
  assert (Hx : (2 ^ L) ^ k mod q = 1 mod q) by (apply pow_1mod; lia).
  set (x := (2 ^ L) ^ k) in *.
  pose proof (Z.div_mod x q ltac:(lia)) as Dx.
  pose proof (Z.div_mod 1 q ltac:(lia)) as D1.
  assert (Ex : x = 1 + q * (x / q - 1 / q)) by lia.
  assert (Ee : 2 ^ e = 2 ^ c + m * (2 ^ (c - a) * (x / q - 1 / q))).
  { rewrite Ek, Z.pow_add_r, Z.pow_mul_r by lia. fold x. rewrite Ex at 1.
    replace c with (a + (c - a)) at 1 2 by lia. rewrite Z.pow_add_r by lia. rewrite Hm. ring. }
  rewrite Ee, (Z.mul_comm m), Z.mod_add; [reflexivity |].
  rewrite Hm. pose proof (Z.pow_pos_nonneg 2 a ltac:(lia) Ha). lia.
Qed.

(** ** The modulus chain: m_i = 2^a_i q_i, the next modulus m_(i+1) is a multiple of the order of 2 mod q_i,
    and for h >= 20 - i, tz h = c_i (mod m_i).  Generated by gen_res.py (constants checked in Python). *)

Lemma lvl15 : forall h, (5 <= h)%nat -> tz h mod 1 = 0.
Proof. intros h _. apply Z.mod_1_r. Qed.

Lemma lvl14 : forall h, (6 <= h)%nat -> tz h mod 4 = 0.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 1 1 4 8 0 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl15. lia.
  - reflexivity.
Qed.

Lemma lvl13 : forall h, (7 <= h)%nat -> tz h mod 20 = 16.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 5 4 20 32 0 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl14. lia.
  - reflexivity.
Qed.

Lemma lvl12 : forall h, (8 <= h)%nat -> tz h mod 100 = 36.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 25 20 100 176 16 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl13. lia.
  - reflexivity.
Qed.

Lemma lvl11 : forall h, (9 <= h)%nat -> tz h mod 500 = 236.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 125 100 500 836 36 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl12. lia.
  - reflexivity.
Qed.

Lemma lvl10 : forall h, (10 <= h)%nat -> tz h mod 2500 = 1236.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 625 500 2500 4236 236 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl11. lia.
  - reflexivity.
Qed.

Lemma lvl9 : forall h, (11 <= h)%nat -> tz h mod 12500 = 11236.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 3125 2500 12500 21236 1236 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl10. lia.
  - reflexivity.
Qed.

Lemma lvl8 : forall h, (12 <= h)%nat -> tz h mod 62500 = 11236.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 15625 12500 62500 111236 11236 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl9. lia.
  - reflexivity.
Qed.

Lemma lvl7 : forall h, (13 <= h)%nat -> tz h mod 312500 = 136236.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 78125 62500 312500 511236 11236 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl8. lia.
  - reflexivity.
Qed.

Lemma lvl6 : forall h, (14 <= h)%nat -> tz h mod 1562500 = 136236.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 390625 312500 1562500 2636236 136236 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl7. lia.
  - reflexivity.
Qed.

Lemma lvl5 : forall h, (15 <= h)%nat -> tz h mod 7812500 = 3261236.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 1953125 1562500 7812500 12636236 136236 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl6. lia.
  - reflexivity.
Qed.

Lemma lvl4 : forall h, (16 <= h)%nat -> tz h mod 39062500 = 34511236.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 9765625 7812500 39062500 65761236 3261236 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl5. lia.
  - reflexivity.
Qed.

Lemma lvl3 : forall h, (17 <= h)%nat -> tz h mod 585937500 = 503261236.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 146484375 39062500 585937500 347011236 34511236 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl4. lia.
  - reflexivity.
Qed.

Lemma lvl2 : forall h, (18 <= h)%nat -> tz h mod 8789062500 = 2847011236.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 2197265625 585937500 8789062500 5190761236 503261236 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl3. lia.
  - reflexivity.
Qed.

Lemma lvl1 : forall h, (19 <= h)%nat -> tz h mod 131835937500 = 99526698736.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 2 32958984375 8789062500 131835937500 73159511236 2847011236 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl2. lia.
  - reflexivity.
Qed.

Lemma lvl0 : forall h, (20 <= h)%nat -> tz h mod 31640625000000 = 10119057948736.
Proof.
  intros h Hh. destruct h as [| h]; [lia |]. rewrite tz_S.
  rewrite (step_res 6 494384765625 131835937500 31640625000000 1154214198736 99526698736 (tz h)).
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite <- Zpow_mod_correct by lia. vm_compute. reflexivity.
  - lia.
  - pose proof (tz_big h ltac:(lia)). lia.
  - apply lvl1. lia.
  - reflexivity.
Qed.

(** ** The residues *)
Definition Mres : Z := 15820312500000.
Definition rho  : Z := 5059528974366.

Lemma tower_res : forall h, (20 <= h)%nat -> Z.of_nat (tower h) mod 31640625000000 = 10119057948736.
Proof. intros h H. rewrite tower_tz. apply lvl0. lia. Qed.

Theorem U_res : forall j x, (2 <= j)%nat -> (Z.of_nat (U j x)) mod Mres = rho.
Proof.
  intros j x Hj. pose proof (U_closed j x) as E.
  destruct (arrow_tower20 (S j) (2 * x + 4) ltac:(lia) ltac:(lia)) as [h [Hh Eh]].
  rewrite Eh in E. pose proof (tower_res h Hh) as R.
  apply (f_equal Z.of_nat) in E.
  set (t := Z.of_nat (tower h)) in *. clearbody t.
  set (u := U j x) in *. clearbody u.
  assert (Et : t = 2 * Z.of_nat u + 4) by lia. rewrite Et in R. clear E Et.
  unfold Mres, rho.
  pose proof (Z.div_mod (Z.of_nat u) 15820312500000 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (Z.of_nat u) 15820312500000 ltac:(lia)) as B1.
  pose proof (Z.div_mod (2 * Z.of_nat u + 4) 31640625000000 ltac:(lia)) as D2.
  rewrite R in D2.
  set (q1 := Z.of_nat u / 15820312500000) in *. set (q2 := (2 * Z.of_nat u + 4) / 31640625000000) in *.
  set (r1 := Z.of_nat u mod 15820312500000) in *. clearbody q1 q2 r1. lia.
Qed.

Theorem iter_U_res : forall v j x, (1 <= v)%nat -> (2 <= j)%nat -> (Z.of_nat (iter v (U j) x)) mod Mres = rho.
Proof.
  intros v j x Hv Hj. destruct v as [| v]; [lia |].
  cbn [iter]. apply U_res. exact Hj.
Qed.

Theorem Bx_res : (Z.of_nat Bx) mod Mres = rho.
Proof. rewrite Bx_def. apply U_res. lia. Qed.

Print Assumptions U_res.
Print Assumptions iter_U_res.
Print Assumptions Bx_res.
