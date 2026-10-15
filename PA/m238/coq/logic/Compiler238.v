(** Explicit PA238 proof programs. Original PA additions; see Codes238.v
    and README.md for source pins and the local m254 reference attribution.

    [derivable] is the code calculus, not ordinary PAeq. [compile] produces
    a finite, concrete command list and [candidateN] its numeric candidate.
    The remaining ordinary-PA bridge and enumerator reach/drain obligations
    are not hidden in this module. No conclusion about the literal TM is
    asserted here. *)
From Coq Require Import Arith Lia Bool List.
From P238.logic Require Import Codes238.
Import ListNotations.

Inductive instruction :=
  | MP (offset : nat) | DROP | NIP | AX (selector x y u : nat).

Definition registers := (nat * nat * nat * nat)%type.
Definition command_step (k : instruction) (q : registers) : option registers :=
  let '(t, w, d, h) := q in
  match k with
  | MP x =>
      let b := d + x in
      if Nat.eqb (wim t b) h then Some (b, P 0 w, b, 0)
      else Some (0, w, b, 0)
  | DROP => Some (h, P t w, d, h)
  | NIP => if Nat.eqb h 1 then None
           else Some (t, snd (unP w), d, fst (unP w))
  | AX c x y u =>
      Some (gate (d + x) (h + y) c,
            ax_stack (d + x) h (h + y) c u t w, 0, 0)
  end.

Fixpoint execute (ks : list instruction) (q : registers) : option registers :=
  match ks with
  | [] => Some q
  | k :: rest => match command_step k q with None => None | Some q' => execute rest q' end
  end.

Lemma execute_append ks ls q :
  execute (ks ++ ls) q =
  match execute ks q with None => None | Some q' => execute ls q' end.
Proof.
  revert q; induction ks as [|k ks IH]; intro q; simpl; auto.
  destruct (command_step k q); auto.
Qed.

Lemma execute_pop t x w d h rest : h <> 1 ->
  execute (NIP :: rest) (t, P x w, d, h) = execute rest (t, w, d, x).
Proof.
  intro H; cbn [execute command_step].
  rewrite (proj2 (Nat.eqb_neq h 1) H), unP_P; reflexivity.
Qed.
Lemma execute_halt t w d rest : execute (NIP :: rest) (t, w, d, 1) = None.
Proof. reflexivity. Qed.
Lemma execute_drop t w d h rest :
  execute (DROP :: rest) (t, w, d, h) = execute rest (h, P t w, d, h).
Proof. reflexivity. Qed.
Lemma execute_ax c x y u t w d h rest :
  execute (AX c x y u :: rest) (t, w, d, h) =
  execute rest (gate (d + x) (h + y) c, ax_stack (d + x) h (h + y) c u t w, 0, 0).
Proof. reflexivity. Qed.
Lemma execute_mp t w d h x rest : wim t (d + x) = h ->
  execute (MP x :: rest) (t, w, d, h) = execute rest (d + x, P 0 w, d + x, 0).
Proof.
  intro H; cbn [execute command_step]; rewrite H, Nat.eqb_refl; reflexivity.
Qed.
Lemma execute_nil q : execute [] q = Some q.
Proof. reflexivity. Qed.

(** A closed AX block contains very large coded numbers. Command proofs use
    the established pairing/pop and residue lemmas, so conversion must not
    expand those numbers while searching for a rewrite. *)
Local Opaque P unP wim wel wal weq wn wa wex bundle gate execute command_step.

Ltac safe_cache := first [apply gate_not_one | apply wim_not_one |
                          apply wal_not_one | apply wex_not_one | lia].
Ltac compute_commands :=
  repeat first [progress rewrite execute_ax | progress rewrite execute_drop |
                progress rewrite execute_pop by safe_cache |
                progress rewrite execute_nil |
                progress cbn [repeat app Nat.sub Nat.add ax_stack ax_rows fold_right] |
                progress rewrite gate_same | progress rewrite ?Nat.add_0_r].

(** Exactly ten pops: the initial zero cache, eight rows, and the generated
    formula are inspected. The old current formula is returned as cache and
    is not inspected by this block. *)
Lemma execute_ten_nips a h b c u t w d current rest :
  execute (repeat NIP 10 ++ rest)
    (current, ax_stack a h b c u t w, d, 0) =
  execute rest (current, w, d, t).
Proof.
  unfold ax_stack, ax_rows; cbn [repeat app fold_right].
  rewrite execute_pop by lia.
  rewrite execute_pop by apply wex_not_one.
  do 7 (rewrite execute_pop by apply wim_not_one).
  rewrite execute_pop by apply wal_not_one.
  reflexivity.
Qed.

(** With initially zero offset and cache, two AX commands clear an arbitrary
    current formula while preserving the incoming numeric stack.
    The second AX resets the cache
    before it is inspected, including when the old current formula is 1. *)
Definition reset : list instruction :=
  [AX 0 0 0 0] ++ repeat NIP 10 ++ [AX 0 0 0 0] ++ repeat NIP 10.
Lemma execute_reset t w : execute reset (t, w, 0, 0) = Some (0, w, 0, 0).
Proof.
  unfold reset; cbn [app]; rewrite execute_ax.
  change (execute (repeat NIP 10 ++ [AX 0 0 0 0] ++ repeat NIP 10)
            (gate 0 0 0, ax_stack 0 0 0 0 0 t w, 0, 0) = Some (0, w, 0, 0)).
  rewrite execute_ten_nips, gate_same.
  cbn [app]; rewrite execute_ax; rewrite !Nat.add_0_r.
  change (execute (repeat NIP 10 ++ [])
            (gate 0 t 0, ax_stack 0 t t 0 0 0 w, 0, 0) = Some (0, w, 0, 0)).
  rewrite execute_ten_nips, gate_same, execute_nil; reflexivity.
Qed.

Definition produces (a : nat) (ks : list instruction) : Prop :=
  forall t w, execute ks (t, w, 0, 0) = None \/
              execute ks (t, w, 0, 0) = Some (a, w, 0, 0).

Definition row_program (j a b c u : nat) : list instruction :=
  reset ++ [AX c a b u] ++ repeat NIP j ++ [DROP] ++ repeat NIP (11 - j).

Ltac prove_row :=
  intros t w; right; unfold row_program;
  rewrite execute_append, execute_reset; compute_commands; reflexivity.

Lemma produces_r1 a b c u : produces (rho1 a b) (row_program 1 a b c u).
Proof. prove_row. Qed.
Lemma produces_r2 a b c u : produces (rho2 a b c) (row_program 2 a b c u).
Proof. prove_row. Qed.
Lemma produces_r3 a b c u : produces (rho3 a b c) (row_program 3 a b c u).
Proof. prove_row. Qed.
Lemma produces_r4 a b c u : produces (rho4 a b c) (row_program 4 a b c u).
Proof. prove_row. Qed.
Lemma produces_r5 a b c u : produces (rho5 a b c) (row_program 5 a b c u).
Proof. prove_row. Qed.
Lemma produces_r6 a b c u : produces (rho6 a b) (row_program 6 a b c u).
Proof. prove_row. Qed.
Lemma produces_r7 a b c u : produces (rho7 a b c) (row_program 7 a b c u).
Proof. prove_row. Qed.
Lemma produces_r8 a b c u : produces (rho8 a b c u) (row_program 8 a b c u).
Proof. prove_row. Qed.

Definition bundle_program a b c := reset ++ [AX c a b 0] ++ repeat NIP 10.
Lemma produces_bundle a b c : c <> a -> c <> b ->
  produces (bundle a b c) (bundle_program a b c).
Proof.
  intros Ha Hb t w; right; unfold bundle_program.
  rewrite execute_append, execute_reset; compute_commands.
  rewrite gate_fresh by assumption; reflexivity.
Qed.
Lemma produces_truth : produces 0 reset.
Proof. intros t w; right; apply execute_reset. Qed.

Definition generalize_program a ks :=
  ks ++ [DROP; NIP; AX a a 0 0] ++ repeat NIP 9 ++ [DROP; NIP; NIP].
Lemma produces_generalize a b ks : produces b ks ->
  produces (wal a b) (generalize_program a ks).
Proof.
  intros H t w; unfold generalize_program; rewrite execute_append.
  destruct (H t w) as [Hrun | Hrun]; rewrite Hrun; [now left|right].
  compute_commands; reflexivity.
Qed.

Definition mp_program b antecedent implication :=
  antecedent ++ [DROP] ++ implication ++
  [NIP; DROP; NIP; MP b; AX b 0 0 0] ++ repeat NIP 10 ++ [DROP; NIP; NIP].
Lemma produces_mp a b ks ls : produces a ks -> produces (wim a b) ls ->
  produces b (mp_program b ks ls).
Proof.
  intros Ha Hb t w; unfold mp_program; rewrite execute_append.
  destruct (Ha t w) as [Hrun | Hrun]; rewrite Hrun; [now left|].
  cbn [app]; rewrite execute_drop, execute_append.
  destruct (Hb 0 (P a w)) as [Hrun' | Hrun']; rewrite Hrun'; [now left|].
  cbn [app repeat]; rewrite execute_pop by lia; rewrite execute_drop.
  destruct (Nat.eq_dec a 1) as [-> | Hne].
  - left; apply execute_halt.
  - rewrite execute_pop by exact Hne.
    rewrite execute_mp by reflexivity.
    compute_commands.
    destruct (Nat.eq_dec b 1) as [-> | Hne']; [left; apply execute_halt|].
    rewrite execute_pop by exact Hne'; compute_commands; right; reflexivity.
Qed.

Inductive derivable : nat -> Prop :=
  | derives_truth : derivable 0
  | derives_mp a b : derivable a -> derivable (wim a b) -> derivable b
  | derives_all a b : derivable b -> derivable (wal a b)
  | derives_r1 a b : derivable (rho1 a b)
  | derives_r2 a b c : derivable (rho2 a b c)
  | derives_r3 a b c : derivable (rho3 a b c)
  | derives_r4 a b c : derivable (rho4 a b c)
  | derives_r5 a b c : derivable (rho5 a b c)
  | derives_r6 a b : derivable (rho6 a b)
  | derives_r7 a b c : derivable (rho7 a b c)
  | derives_r8 a b c u : derivable (rho8 a b c u)
  | derives_bundle a b c : c <> a -> c <> b -> derivable (bundle a b c).

(** This existential is obtained by structural induction on the derivation.
    Every branch supplies the actual instruction list above. *)
Theorem compile x : derivable x -> exists ks, produces x ks.
Proof.
  intro H; induction H as
    [|a b Ha IHa Hab IHab|a b Hb IHb
     |a b|a b c|a b c|a b c|a b c|a b|a b c|a b c u|a b c Hca Hcb].
  - exists reset; apply produces_truth.
  - destruct IHa as [ks Hks]; destruct IHab as [ls Hls].
    exists (mp_program b ks ls); eapply produces_mp; eassumption.
  - destruct IHb as [ks Hks].
    exists (generalize_program a ks); apply produces_generalize; assumption.
  - exists (row_program 1 a b 0 0); apply produces_r1.
  - exists (row_program 2 a b c 0); apply produces_r2.
  - exists (row_program 3 a b c 0); apply produces_r3.
  - exists (row_program 4 a b c 0); apply produces_r4.
  - exists (row_program 5 a b c 0); apply produces_r5.
  - exists (row_program 6 a b 0 0); apply produces_r6.
  - exists (row_program 7 a b c 0); apply produces_r7.
  - exists (row_program 8 a b c u); apply produces_r8.
  - exists (bundle_program a b c); apply produces_bundle; assumption.
Qed.

Definition fields (k : instruction) : list nat :=
  match k with
  | MP x => [0; x] | DROP => [1; 0] | NIP => [2; 0]
  | AX c x y u => [3 + c; x; y; u]
  end.
Definition encode_fields fs tail := fold_right P tail fs.
Fixpoint encode_tail ks :=
  match ks with [] => 0 | k :: rest => S (encode_fields (fields k) (encode_tail rest)) end.
Definition start := AX 0 1 1 0.
Definition finish : list instruction := [DROP; NIP; NIP].
Definition candidateN ks := encode_fields (fields start) (encode_tail (ks ++ finish)).

Lemma compiled_falsity_halts ks : produces 1 ks ->
  forall q, execute (start :: ks ++ finish) q = None.
Proof.
  intros H [[[t w] d] h]; unfold start; rewrite execute_ax, execute_append.
  destruct (H (gate (d + 1) (h + 1) 0)
              (ax_stack (d + 1) h (h + 1) 0 0 t w)) as [Hrun | Hrun]; rewrite Hrun; [reflexivity|].
  unfold finish; rewrite execute_drop, execute_pop by lia; apply execute_halt.
Qed.

Theorem compile_falsity : derivable 1 ->
  exists ks, forall q, execute (start :: ks ++ finish) q = None.
Proof.
  intro H; destruct (compile 1 H) as [ks Hks].
  exists ks; apply compiled_falsity_halts; exact Hks.
Qed.
