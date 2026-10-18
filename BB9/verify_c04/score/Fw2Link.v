(** Link Score.v's copy of the fast-growing hierarchy to fw2's own constants (bb8_list/proofs/BB9_fw2_bound.v,
    identical to busy-beaver/BB9/verify_fw2/multifile/BB9_fw2_bound.v), and restate beats_fw2 against them.
    Build: python coqc_score.py Fw2Link.v 600 --fw2 *)
From BB8 Require Individual92 BB9_fw2_bound.
From Score Require Score.
From Dev Require Abs Chain.

Lemma f_same : forall k n, Score.f k n = BB9_fw2_bound.f k n.
Proof. reflexivity. Qed.

Lemma f_omega_same : forall n, Score.f_omega n = BB9_fw2_bound.f_omega n.
Proof. reflexivity. Qed.

(** Never let conversion meet the closed term f_omega 465009 under two different heads (the kernel would try to
    reduce it): the two hierarchies are identified at a variable argument first, then instantiated. *)
Lemma ff_same : forall a, BB9_fw2_bound.f_omega (BB9_fw2_bound.f_omega a) = Score.f_omega (Score.f_omega a).
Proof. intro a. reflexivity. Qed.

Theorem beats_fw2_link : forall K x N, 11 * Chain.R2 Abs.Bx <= K -> Abs.U K 0 <= x -> 6 * x <= N ->
  BB9_fw2_bound.f_omega (BB9_fw2_bound.f_omega (465 * 1000 + 9)) < N.
Proof.
  intros K x N HK Hx HN.
  exact (eq_ind_r (fun y => y < N) (Score.beats_fw2 K x N HK Hx HN) (ff_same (465 * 1000 + 9))).
Qed.

Theorem S1_link : forall K, 11 * Chain.R2 Abs.Bx <= K ->
  BB9_fw2_bound.f_omega (BB9_fw2_bound.f_omega (465 * 1000 + 9)) < Abs.U K 0.
Proof.
  intros K HK. exact (eq_ind_r (fun y => y < Abs.U K 0) (Score.S1_11 K HK) (ff_same (465 * 1000 + 9))).
Qed.

(* fw2's published statement, for comparison *)
Check BB9_fw2_bound.sigma_lower_bound.
Print Assumptions f_omega_same.
Print Assumptions beats_fw2_link.
Print Assumptions S1_link.
