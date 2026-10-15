(** Original PA238 command-boundary proof search.

    This scheduler copies nextproof into an empty prooflist and increments
    nextproof; otherwise it decrements prooflist before decoding. Each step
    performs a genuine numeric command. Candidate drainage below supplies
    the finite steps needed to reach any later candidate index, or a halt
    that occurs earlier. Completeness uses the actual [candidateN] compiler.

    This is a numeric command-boundary interface for the program layer.
    The source-register/DAG/literal-machine bridges and ordinary PAeq
    interpretation are separate obligations. The physical-register adapter
    reads the PA checkpoint as nextproof 6 and param1 2. This module does
    not prove the literal TM reaches that checkpoint. *)
From Coq Require Import Arith Lia Bool List.
From P238.logic Require Import Codes238 Compiler238 SoundCommands238 Candidate238.
Import ListNotations.

Record enum_state := EnumState {
  enum_pending : nat;
  enum_next : nat;
  enum_registers : registers
}.

Definition enum_step (s : enum_state) : option enum_state :=
  let '(n, np) :=
    match enum_pending s with
    | 0 => (enum_next s, S (enum_next s))
    | S n => (n, enum_next s)
    end in
  let '(k, x, tail) := decode_fields n in
  match command_step k (add_offset x (enum_registers s)) with
  | None => None
  | Some q => Some (EnumState tail np q)
  end.

Fixpoint enum_run (fuel : nat) (s : enum_state) : option enum_state :=
  match fuel with
  | 0 => Some s
  | S fuel => match enum_step s with
              | None => None
              | Some s' => enum_run fuel s'
              end
  end.

Definition enum_initial := EnumState 0 0 (0, 0, 0, 0).
(** Physical slots follow replay_bootstrap.py's inspected register names:
    wffstack, param1, axiomcode, scratch2, scratch1, prooflist, nextproof,
    topwff, param2. The omitted command-boundary scratch slots are 2/3/4. *)
Definition enum_from_physical (vs : list nat) : enum_state :=
  EnumState (nth 5 vs 0) (nth 6 vs 0)
    (nth 7 vs 0, nth 0 vs 0, nth 1 vs 0, nth 8 vs 0).
Definition enum_boot := EnumState 0 6 (0, 0, 2, 0).
Lemma enum_boot_aliases :
  enum_from_physical [0; 2; 0; 0; 0; 0; 6; 0; 0] = enum_boot.
Proof. reflexivity. Qed.
Definition enum238_halts := exists fuel, enum_run fuel enum_initial = None.
Definition enum238_boot_halts := exists fuel, enum_run fuel enum_boot = None.

Lemma enum_run_zero s : enum_run 0 s = Some s.
Proof. reflexivity. Qed.
Lemma enum_run_succ fuel s : enum_run (S fuel) s =
  match enum_step s with None => None | Some s' => enum_run fuel s' end.
Proof. reflexivity. Qed.
Lemma enum_step_pending n np q : enum_step (EnumState (S n) np q) =
  let '(k, x, tail) := decode_fields n in
  match command_step k (add_offset x q) with
  | None => None
  | Some q' => Some (EnumState tail np q')
  end.
Proof. reflexivity. Qed.
Lemma enum_start_step n q :
  enum_step (EnumState 0 n q) = enum_step (EnumState (S n) (S n) q).
Proof. reflexivity. Qed.
Lemma enum_start_run fuel n q :
  enum_run (S fuel) (EnumState 0 n q) =
  enum_run (S fuel) (EnumState (S n) (S n) q).
Proof. rewrite !enum_run_succ, enum_start_step; reflexivity. Qed.

Lemma enum_run_append first later s : enum_run (first + later) s =
  match enum_run first s with
  | None => None
  | Some s' => enum_run later s'
  end.
Proof.
  revert s; induction first as [|first IH]; intro s; cbn [enum_run Nat.add].
  - reflexivity.
  - destruct (enum_step s); [apply IH|reflexivity].
Qed.

Local Opaque P unP wim wel wal weq wn wa wex bundle gate command_step.

(** A candidate run stops at its first halt/exhaustion. The corresponding
    scheduler prefix has at most the supplied fuel, so later candidate
    execution is never smuggled into the candidate-drain claim. *)
Theorem candidate_result_reachable fuel : forall n np q,
  match run_candidate fuel n q with
  | candidate_halted => exists used, used <= fuel /\
      enum_run used (EnumState (S n) np q) = None
  | candidate_exhausted q' => exists used, used <= fuel /\
      enum_run used (EnumState (S n) np q) = Some (EnumState 0 np q')
  | candidate_suspended n' q' =>
      enum_run fuel (EnumState (S n) np q) = Some (EnumState (S n') np q')
  end.
Proof.
  induction fuel as [|fuel IH]; intros n np q; [reflexivity|].
  cbn [run_candidate]; destruct (decode_fields n) as [[k x] tail] eqn:Ed.
  destruct (command_step k (add_offset x q)) as [q'|] eqn:Ec.
  - destruct tail as [|n'].
    + exists 1; split; [lia|].
      rewrite enum_run_succ, enum_step_pending, Ed, Ec, enum_run_zero; reflexivity.
    + destruct (run_candidate fuel n' q') as [|q''|n'' q''] eqn:Er;
        pose proof (IH n' np q') as Hr; rewrite Er in Hr; cbn in Hr.
      * destruct Hr as [used [Hbound Hrun]]; exists (S used); split; [lia|].
        rewrite enum_run_succ, enum_step_pending, Ed, Ec; exact Hrun.
      * destruct Hr as [used [Hbound Hrun]]; exists (S used); split; [lia|].
        rewrite enum_run_succ, enum_step_pending, Ed, Ec; exact Hrun.
      * rewrite enum_run_succ, enum_step_pending, Ed, Ec; exact Hr.
  - exists 1; split; [lia|].
    rewrite enum_run_succ, enum_step_pending, Ed, Ec; reflexivity.
Qed.

Theorem enum_candidate_drain n np q : exists used, used <= S n /\
  (enum_run used (EnumState (S n) np q) = None \/
   exists q', enum_run used (EnumState (S n) np q) = Some (EnumState 0 np q')).
Proof.
  pose proof (candidate_result_reachable (S n) n np q) as Hr.
  destruct (candidate_drains_bound n q) as [Hhalt|[q' Hexhaust]].
  - rewrite Hhalt in Hr; destruct Hr as [used [Hbound Hrun]].
    exists used; split; [exact Hbound|now left].
  - rewrite Hexhaust in Hr; destruct Hr as [used [Hbound Hrun]].
    exists used; split; [exact Hbound|right; now exists q'].
Qed.

Theorem enum_boundary_drain n q : exists used,
  enum_run used (EnumState 0 n q) = None \/
  exists q', enum_run used (EnumState 0 n q) = Some (EnumState 0 (S n) q').
Proof.
  destruct (enum_candidate_drain n (S n) q) as [used [Hbound Hrun]].
  destruct used as [|used].
  - rewrite enum_run_zero in Hrun.
    destruct Hrun as [Hhalt|[q' Hstop]]; [discriminate|inversion Hstop].
  - exists (S used); rewrite enum_start_run; exact Hrun.
Qed.

Lemma enum_candidate_halt fuel n q : run_candidate fuel n q = candidate_halted ->
  exists used, enum_run used (EnumState 0 n q) = None.
Proof.
  intro Hhalt; pose proof (candidate_result_reachable fuel n (S n) q) as Hr.
  rewrite Hhalt in Hr; destruct Hr as [used [Hbound Hrun]].
  destruct used as [|used]; [discriminate|].
  exists (S used); rewrite enum_start_run; exact Hrun.
Qed.

(** The induction performs one genuine candidate drain at each successor.
    It constructs a finite scheduler trace reaching next+count unless an
    earlier candidate has already halted. *)
Theorem enum_reach_add count : forall next q,
  (exists fuel, enum_run fuel (EnumState 0 next q) = None) \/
  exists fuel q', enum_run fuel (EnumState 0 next q) =
                   Some (EnumState 0 (next + count) q').
Proof.
  induction count as [|count IH]; intros next q.
  - right; exists 0, q; rewrite Nat.add_0_r; reflexivity.
  - destruct (enum_boundary_drain next q) as [used [Hhalt|[q' Hdone]]].
    + left; now exists used.
    + destruct (IH (S next) q') as [[later Hhalt]|[later [q'' Hnext]]].
      * left; exists (used + later); rewrite enum_run_append, Hdone; exact Hhalt.
      * right; exists (used + later), q''; rewrite enum_run_append, Hdone.
        replace (next + S count) with (S next + count) by lia; exact Hnext.
Qed.

Corollary enum_reach_at target next q : next <= target ->
  (exists fuel, enum_run fuel (EnumState 0 next q) = None) \/
  exists fuel q', enum_run fuel (EnumState 0 next q) = Some (EnumState 0 target q').
Proof.
  intro Hle; pose proof (enum_reach_add (target - next) next q) as H.
  replace (next + (target - next)) with target in H by lia; exact H.
Qed.

Lemma candidateN_lower_bound ks : 32 <= candidateN ks.
Proof.
  unfold candidateN, start, fields, encode_fields; cbn [fold_right Nat.add].
  rewrite <- P_start_minimum.
  apply P_mono; [lia|].
  apply P_mono; [lia|].
  apply P_mono; [lia|].
  apply P_mono; lia.
Qed.

Theorem enum_compiler_complete_from next q : next <= 32 -> derivable 1 ->
  exists fuel, enum_run fuel (EnumState 0 next q) = None.
Proof.
  intros Hnext Hder; destruct (candidate_compiler_complete Hder) as [ks Hcandidate].
  pose proof (candidateN_lower_bound ks) as Hbound.
  destruct (enum_reach_at (candidateN ks) next q ltac:(lia))
    as [Hhalt|[used [q' Hreach]]]; [exact Hhalt|].
  destruct (enum_candidate_halt (S (length (ks ++ finish)))
              (candidateN ks) q' (Hcandidate q')) as [later Hhalt].
  exists (used + later); rewrite enum_run_append, Hreach; exact Hhalt.
Qed.

Corollary enum_compiler_complete : derivable 1 -> enum238_halts.
Proof.
  intro H; apply (enum_compiler_complete_from 0 (0, 0, 0, 0)); [lia|exact H].
Qed.
Corollary enum_boot_compiler_complete : derivable 1 -> enum238_boot_halts.
Proof.
  intro H; apply (enum_compiler_complete_from 6 (0, 0, 2, 0)); [lia|exact H].
Qed.

Definition enum_retained s := retained (enum_registers s).

Theorem enum_step_sound s : enum_retained s ->
  match enum_step s with None => derivable 1 | Some s' => enum_retained s' end.
Proof.
  destruct s as [pending next q]; cbn [enum_retained]; intro Hq.
  unfold enum_step; cbn [enum_pending enum_next enum_registers].
  destruct pending as [|n].
  - destruct (decode_fields next) as [[k x] tail].
    pose proof (command_sound k (add_offset x q) (retained_add_offset x q Hq)) as Hk.
    destruct (command_step k (add_offset x q)); exact Hk.
  - destruct (decode_fields n) as [[k x] tail].
    pose proof (command_sound k (add_offset x q) (retained_add_offset x q Hq)) as Hk.
    destruct (command_step k (add_offset x q)); exact Hk.
Qed.

Theorem enum_run_sound fuel : forall s, enum_retained s ->
  match enum_run fuel s with None => derivable 1 | Some s' => enum_retained s' end.
Proof.
  induction fuel as [|fuel IH]; intros s Hs; cbn [enum_run]; [exact Hs|].
  pose proof (enum_step_sound s Hs) as Hstep.
  destruct (enum_step s) as [s'|]; [apply IH; exact Hstep|exact Hstep].
Qed.

Corollary enum_halt_sound fuel s : enum_retained s -> enum_run fuel s = None -> derivable 1.
Proof.
  intros Hs Hrun; pose proof (enum_run_sound fuel s Hs) as H.
  rewrite Hrun in H; exact H.
Qed.

Theorem enum238_sound : enum238_halts -> derivable 1.
Proof.
  intros [fuel Hrun]; apply (enum_halt_sound fuel enum_initial).
  - change (retained (0, 0, 0, 0)); apply retained_zero.
  - exact Hrun.
Qed.
Theorem enum238_boot_sound : enum238_boot_halts -> derivable 1.
Proof.
  intros [fuel Hrun]; apply (enum_halt_sound fuel enum_boot).
  - change (retained (0, 0, 2, 0)); apply retained_zero.
  - exact Hrun.
Qed.

Corollary enum238_code_endpoint : enum238_halts <-> derivable 1.
Proof. split; [apply enum238_sound|apply enum_compiler_complete]. Qed.
Corollary enum238_boot_code_endpoint : enum238_boot_halts <-> derivable 1.
Proof. split; [apply enum238_boot_sound|apply enum_boot_compiler_complete]. Qed.
