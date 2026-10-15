(** Original PA238 numeric candidate decoder and bounded execution.

    The source reads the first command from the candidate itself, and
    decrements a nonzero continuation before reading the next command.
    Its DROP and NIP cases also add their raw second field to param1.
    [fields] canonically writes zero there; arbitrary candidates must retain
    that addition. [decode_fields] records it separately from the compiler's
    canonical instruction.

    These are explicit inverse and execution theorems for the numeric
    semantics below. Source-register, DAG, and literal-TM identification
    remain separate obligations; no source equivalence is assumed here. *)
From Coq Require Import Arith Lia Bool List.
From P238.logic Require Import Codes238 Compiler238 SoundCommands238.
Import ListNotations.

Definition add_offset (x : nat) (q : registers) : registers :=
  let '(t, w, d, h) := q in (t, w, d + x, h).

(** The middle component is a raw offset for DROP/NIP. MP/AX already carry
    their offset as part of the compiler instruction. *)
Definition decode_fields (n : nat) : instruction * nat * nat :=
  let '(op, p1) := unP n in
  let '(x, p2) := unP p1 in
  match op with
  | 0 => (MP x, 0, p2)
  | 1 => (DROP, x, p2)
  | 2 => (NIP, x, p2)
  | S (S (S c)) =>
      let '(y, p3) := unP p2 in
      let '(u, p4) := unP p3 in (AX c x y u, 0, p4)
  end.

Local Opaque P unP wim wel wal weq wn wa wex bundle gate command_step.

Lemma add_offset_zero q : add_offset 0 q = q.
Proof. destruct q as [[[t w] d] h]; unfold add_offset; rewrite Nat.add_0_r; reflexivity. Qed.

Lemma decode_fields_encode k tail :
  decode_fields (encode_fields (fields k) tail) = (k, 0, tail).
Proof.
  destruct k; unfold fields, encode_fields; cbn [fold_right].
  all: unfold decode_fields; rewrite !unP_P; reflexivity.
Qed.

Lemma decode_fields_tail_bound n : snd (decode_fields n) <= n.
Proof.
  unfold decode_fields; destruct (unP n) as [op p1] eqn:E1.
  pose proof (unP_bounds n) as H1; rewrite E1 in H1; cbn in H1.
  destruct (unP p1) as [x p2] eqn:E2.
  pose proof (unP_bounds p1) as H2; rewrite E2 in H2; cbn in H2.
  destruct op as [|[|[|c]]]; cbn; try lia.
  destruct (unP p2) as [y p3] eqn:E3.
  pose proof (unP_bounds p2) as H3; rewrite E3 in H3; cbn in H3.
  destruct (unP p3) as [u p4] eqn:E4.
  pose proof (unP_bounds p3) as H4; rewrite E4 in H4; cbn in H4; cbn; lia.
Qed.

(** Fuel exhaustion and candidate exhaustion are different observations.
    A halt is exactly a halting command, including one inside a candidate. *)
Inductive candidate_result :=
  | candidate_halted
  | candidate_exhausted (q : registers)
  | candidate_suspended (pending : nat) (q : registers).

Fixpoint run_candidate (fuel n : nat) (q : registers) : candidate_result :=
  match fuel with
  | 0 => candidate_suspended n q
  | S fuel =>
      let '(k, x, tail) := decode_fields n in
      match command_step k (add_offset x q) with
      | None => candidate_halted
      | Some q' =>
          match tail with
          | 0 => candidate_exhausted q'
          | S n' => run_candidate fuel n' q'
          end
      end
  end.

Theorem run_candidate_encoded k ks q :
  run_candidate (S (length ks))
    (encode_fields (fields k) (encode_tail ks)) q =
  match execute (k :: ks) q with
  | None => candidate_halted
  | Some q' => candidate_exhausted q'
  end.
Proof.
  revert k q; induction ks as [|j ks IH]; intros k q.
  - cbn [length run_candidate]; rewrite decode_fields_encode.
    cbn [fst snd]; rewrite add_offset_zero; cbn [encode_tail execute].
    destruct (command_step k q); reflexivity.
  - cbn [length run_candidate]; rewrite decode_fields_encode.
    cbn [fst snd]; rewrite add_offset_zero; cbn [encode_tail execute].
    destruct (command_step k q) as [q'|]; [apply IH|reflexivity].
Qed.

Corollary run_candidateN ks q :
  run_candidate (S (length (ks ++ finish))) (candidateN ks) q =
  match execute (start :: ks ++ finish) q with
  | None => candidate_halted
  | Some q' => candidate_exhausted q'
  end.
Proof. unfold candidateN; apply run_candidate_encoded. Qed.

Theorem candidate_compiler_complete : derivable 1 ->
  exists ks, forall q,
    run_candidate (S (length (ks ++ finish))) (candidateN ks) q = candidate_halted.
Proof.
  intro H; destruct (compile 1 H) as [ks Hks]; exists ks; intro q.
  rewrite run_candidateN, (compiled_falsity_halts ks Hks q); reflexivity.
Qed.

(** Every candidate drains in a finite explicit bound, or halts earlier.
    Each later command is read from tail-1; the decoder never increases it. *)
Theorem candidate_drains fuel : forall n q, n < fuel ->
  run_candidate fuel n q = candidate_halted \/
  exists q', run_candidate fuel n q = candidate_exhausted q'.
Proof.
  induction fuel as [|fuel IH]; intros n q Hlt; [lia|].
  cbn [run_candidate]; destruct (decode_fields n) as [[k x] tail] eqn:E.
  pose proof (decode_fields_tail_bound n) as Hbound; rewrite E in Hbound; cbn in Hbound.
  destruct (command_step k (add_offset x q)) as [q'|]; [|now left].
  destruct tail as [|n']; [right; now exists q'|].
  apply IH; lia.
Qed.

Corollary candidate_drains_bound n q :
  run_candidate (S n) n q = candidate_halted \/
  exists q', run_candidate (S n) n q = candidate_exhausted q'.
Proof. apply candidate_drains; lia. Qed.

Lemma retained_add_offset x q : retained q -> retained (add_offset x q).
Proof. destruct q as [[[t w] d] h]; exact (fun H => H). Qed.

Definition candidate_safe (r : candidate_result) : Prop :=
  match r with
  | candidate_halted => derivable 1
  | candidate_exhausted q | candidate_suspended _ q => retained q
  end.

Theorem run_candidate_sound fuel : forall n q, retained q ->
  candidate_safe (run_candidate fuel n q).
Proof.
  induction fuel as [|fuel IH]; intros n q Hq; [exact Hq|].
  cbn [run_candidate]; destruct (decode_fields n) as [[k x] tail].
  pose proof (command_sound k (add_offset x q) (retained_add_offset x q Hq)) as Hk.
  destruct (command_step k (add_offset x q)) as [q'|]; [|exact Hk].
  destruct tail; [exact Hk|apply IH; exact Hk].
Qed.

Corollary candidate_halt_sound fuel n q : retained q ->
  run_candidate fuel n q = candidate_halted -> derivable 1.
Proof.
  intros Hq Hrun; pose proof (run_candidate_sound fuel n q Hq) as H.
  rewrite Hrun in H; exact H.
Qed.

Corollary blank_candidate_halt_sound fuel n :
  run_candidate fuel n (0, 0, 0, 0) = candidate_halted -> derivable 1.
Proof. apply candidate_halt_sound; apply retained_zero. Qed.
