(** A1: the level-B cascade orbit map g and its invariants (sketch section A1).
    L is the sketch's L (= my cell-count L minus 1).  r = L mod 5; the sub-step/stop constants are
    c_1=32, c_2=-46, c_3=-64, c_4=-52, c_0=-100 (stop).  All are even, 2 c_r = 2 mod 3, and
    3 L + c_r = 0 mod 5 for L = r mod 5, so g(L) = (3 L + c_r)/5 is exact. *)

From Coq Require Import Lia PeanoNat.

(* integer constants as Z-free naturals: g in terms of (3L + c)/5 with c as a signed add/sub on nat *)
Definition gstep (L : nat) : nat :=
  match L mod 5 with
  | 1 => (3 * L + 32) / 5
  | 2 => (3 * L - 46) / 5
  | 3 => (3 * L - 64) / 5
  | 4 => (3 * L - 52) / 5
  | _ => (3 * L - 100) / 5          (* L = 0 mod 5 : stop *)
  end.

(** Exactness: 5 | 3 L + c_r. *)
Lemma gstep_exact1 : forall L, L mod 5 = 1 -> (3 * L + 32) mod 5 = 0.
Proof. intros L H. rewrite Nat.Div0.add_mod, Nat.Div0.mul_mod, H. reflexivity. Qed.

(* helper: value of g via the quotient relation, for the residue facts *)
Lemma div5_eq : forall a q, a = 5 * q -> a / 5 = q.
Proof. intros a q ->. rewrite Nat.mul_comm, Nat.div_mul; lia. Qed.

(** (i) g(L) = 1 mod 3 for every L (the orbit stays in the 1-mod-3 class). *)
Lemma gstep_mod3 : forall L, 60 <= L -> gstep L mod 3 = 1.
Proof.
  intros L HL. unfold gstep.
  pose proof (Nat.mod_upper_bound L 5 ltac:(lia)) as H5.
  pose proof (Nat.div_mod L 5 ltac:(lia)) as HL5.
  remember (L mod 5) as r eqn:Er. remember (L / 5) as q eqn:Eq.
  (* L = 5 q + r *)
  destruct r as [|[|[|[|[|r]]]]]; try lia; clear Eq Er H5.
  - (* r = 0: (3L-100)/5 = 3q - 20 *)
    rewrite (div5_eq (3 * L - 100) (3 * q - 20)) by lia.
    (* 3q-20 mod 3 = 1 iff q = 0 mod 3? no: 3q-20 = 3(q-7)+1 *)
    replace (3 * q - 20) with (3 * (q - 7) + 1) by lia.
    rewrite Nat.Div0.add_mod, Nat.Div0.mul_mod. reflexivity.
  - rewrite (div5_eq (3 * L + 32) (3 * q + 7)) by lia.
    replace (3 * q + 7) with (3 * (q + 2) + 1) by lia.
    rewrite Nat.Div0.add_mod, Nat.Div0.mul_mod. reflexivity.
  - rewrite (div5_eq (3 * L - 46) (3 * q - 8)) by lia.
    replace (3 * q - 8) with (3 * (q - 3) + 1) by lia.
    rewrite Nat.Div0.add_mod, Nat.Div0.mul_mod. reflexivity.
  - rewrite (div5_eq (3 * L - 64) (3 * q - 11)) by lia.
    replace (3 * q - 11) with (3 * (q - 4) + 1) by lia.
    rewrite Nat.Div0.add_mod, Nat.Div0.mul_mod. reflexivity.
  - rewrite (div5_eq (3 * L - 52) (3 * q - 8)) by lia.
    replace (3 * q - 8) with (3 * (q - 3) + 1) by lia.
    rewrite Nat.Div0.add_mod, Nat.Div0.mul_mod. reflexivity.
Qed.

(** helper: a and b have equal parity when they differ by an even number. *)
Lemma mod2_shift : forall a k, (a + 2 * k) mod 2 = a mod 2.
Proof.
  intros a k. rewrite Nat.Div0.add_mod, (Nat.mul_comm 2 k), Nat.Div0.mod_mul, Nat.add_0_r.
  apply Nat.Div0.mod_mod.
Qed.
Lemma mod2_eq : forall a b, (a <= b /\ (b - a) mod 2 = 0) -> a mod 2 = b mod 2.
Proof.
  intros a b [Hle Hev].
  pose proof (Nat.div_mod (b - a) 2 ltac:(lia)) as H. rewrite Hev, Nat.add_0_r in H.
  replace b with (a + 2 * ((b - a) / 2)) by lia. now rewrite mod2_shift.
Qed.
Ltac par := apply mod2_eq; split; [ lia | ]; (
  rewrite ?Nat.Div0.add_mod; reflexivity ) || (
  match goal with |- (?x) mod 2 = 0 => replace x with (2 * (x / 2)) by lia end;
  rewrite Nat.mul_comm; apply Nat.Div0.mod_mul ).

(** (ii) parity is invariant: g(L) = L mod 2. *)
Lemma gstep_mod2 : forall L, 60 <= L -> gstep L mod 2 = L mod 2.
Proof.
  intros L HL. unfold gstep.
  pose proof (Nat.mod_upper_bound L 5 ltac:(lia)) as H5.
  pose proof (Nat.div_mod L 5 ltac:(lia)) as HL5.
  remember (L mod 5) as r eqn:Er. remember (L / 5) as q eqn:Eq.
  destruct r as [|[|[|[|[|r]]]]]; try lia; clear Eq Er H5.
  - rewrite (div5_eq (3 * L - 100) (3 * q - 20)) by lia.
    apply mod2_eq; split; [lia|]. replace (L - (3 * q - 20)) with (2 * (q + 10)) by lia.
    rewrite Nat.mul_comm; apply Nat.Div0.mod_mul.
  - rewrite (div5_eq (3 * L + 32) (3 * q + 7)) by lia.
    apply mod2_eq; split; [lia|]. replace (L - (3 * q + 7)) with (2 * (q - 3)) by lia.
    rewrite Nat.mul_comm; apply Nat.Div0.mod_mul.
  - rewrite (div5_eq (3 * L - 46) (3 * q - 8)) by lia.
    apply mod2_eq; split; [lia|]. replace (L - (3 * q - 8)) with (2 * (q + 5)) by lia.
    rewrite Nat.mul_comm; apply Nat.Div0.mod_mul.
  - rewrite (div5_eq (3 * L - 64) (3 * q - 11)) by lia.
    apply mod2_eq; split; [lia|]. replace (L - (3 * q - 11)) with (2 * (q + 7)) by lia.
    rewrite Nat.mul_comm; apply Nat.Div0.mod_mul.
  - rewrite (div5_eq (3 * L - 52) (3 * q - 8)) by lia.
    apply mod2_eq; split; [lia|]. replace (L - (3 * q - 8)) with (2 * (q + 6)) by lia.
    rewrite Nat.mul_comm; apply Nat.Div0.mod_mul.
Qed.

(** (iii) strict decrease for L large. *)
Lemma gstep_lt : forall L, 60 <= L -> gstep L < L.
Proof.
  intros L HL. unfold gstep.
  pose proof (Nat.mod_upper_bound L 5 ltac:(lia)) as H5.
  pose proof (Nat.div_mod L 5 ltac:(lia)) as HL5.
  remember (L mod 5) as r eqn:Er. remember (L / 5) as q eqn:Eq.
  destruct r as [|[|[|[|[|r]]]]]; try lia; clear Eq Er H5.
  - rewrite (div5_eq (3 * L - 100) (3 * q - 20)) by lia. lia.
  - rewrite (div5_eq (3 * L + 32) (3 * q + 7)) by lia. lia.
  - rewrite (div5_eq (3 * L - 46) (3 * q - 8)) by lia. lia.
  - rewrite (div5_eq (3 * L - 64) (3 * q - 11)) by lia. lia.
  - rewrite (div5_eq (3 * L - 52) (3 * q - 8)) by lia. lia.
Qed.

(** invariant: odd and = 1 mod 3 is preserved while L >= 60. *)
Lemma gstep_inv : forall L, 60 <= L -> L mod 2 = 1 -> L mod 3 = 1 ->
  gstep L mod 2 = 1 /\ gstep L mod 3 = 1.
Proof.
  intros L HL H2 H3. split.
  - rewrite gstep_mod2 by lia. exact H2.
  - apply gstep_mod3; lia.
Qed.

(** (A1 key set) the first value that drops below 60, from an odd =1-mod-3 argument >= 60,
    is one of 31, 37, 43, 49, 55.  Finite check: such an argument is < 135. *)
From Coq Require Import List Bool. Import ListNotations.
Local Open Scope bool_scope.

Definition in_keys (x : nat) : bool :=
  Nat.eqb x 31 || Nat.eqb x 37 || Nat.eqb x 43 || Nat.eqb x 49 || Nat.eqb x 55.

Definition keycheck : bool :=
  forallb (fun L => if (60 <=? L) && (Nat.eqb (L mod 2) 1) && (Nat.eqb (L mod 3) 1) && (gstep L <? 60)
                    then in_keys (gstep L) else true) (seq 0 135).

Lemma keycheck_ok : keycheck = true.
Proof. vm_compute. reflexivity. Qed.

Lemma gstep_bound : forall L, 60 <= L -> gstep L < 60 -> L < 135.
Proof.
  intros L HL Hlt. unfold gstep in Hlt.
  pose proof (Nat.mod_upper_bound L 5 ltac:(lia)).
  pose proof (Nat.div_mod L 5 ltac:(lia)).
  remember (L mod 5) as r. remember (L / 5) as q.
  destruct r as [|[|[|[|[|r]]]]]; try lia.
  - rewrite (div5_eq (3 * L - 100) (3 * q - 20)) in Hlt by lia. lia.
  - rewrite (div5_eq (3 * L + 32) (3 * q + 7)) in Hlt by lia. lia.
  - rewrite (div5_eq (3 * L - 46) (3 * q - 8)) in Hlt by lia. lia.
  - rewrite (div5_eq (3 * L - 64) (3 * q - 11)) in Hlt by lia. lia.
  - rewrite (div5_eq (3 * L - 52) (3 * q - 8)) in Hlt by lia. lia.
Qed.

Lemma gstep_key : forall L, 60 <= L -> L mod 2 = 1 -> L mod 3 = 1 -> gstep L < 60 ->
  in_keys (gstep L) = true.
Proof.
  intros L HL H2 H3 Hlt.
  pose proof (gstep_bound L HL Hlt) as Hb.
  pose proof keycheck_ok as HC. unfold keycheck in HC.
  rewrite forallb_forall in HC.
  specialize (HC L). rewrite in_seq in HC.
  assert (HL' : 0 <= L < 135) by lia. specialize (HC ltac:(lia)).
  rewrite (proj2 (Nat.leb_le _ _) HL), H2, H3 in HC. simpl in HC.
  rewrite (proj2 (Nat.ltb_lt _ _) Hlt) in HC. simpl in HC. exact HC.
Qed.
