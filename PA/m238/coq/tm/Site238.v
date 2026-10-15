(** * Actual positive PA238 instruction round trips.

    The gap parameter adds to the authenticated PA minimum38. Every target
    restores state25, the marker, the complete PC/gap/header, and the complete
    physical file effect. The finite checker executes only proved literal
    boxed rules. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith PArith.BinPos Lia.
From P238.tm Require Import RM238 Prog238 Finite238 Symbolic238 RegisterTape238
  LiteralHalting238 Boxed238 BoxedNormalize238 BoxedExecute238.
From P238.tm Require Export SiteCheck238.
Local Unset Implicit Arguments.
Import ListNotations.

Theorem checked_variant238_round Q e zero br Q' overflow phase gap vs :
  check_variant238 Q e zero = true ->
  site_route238 Q e zero = Some (br, (Q', (overflow, phase))) ->
  branch_valid238 br vs ->
  exists n, exact_steps (S n)
    (boxed_denote238 gap vs (site_start238 Q 0 FilePlain238))
    (boxed_denote238 gap vs (site_start238 Q' (bool_nat238 overflow) phase)).
Proof.
  unfold check_variant238. intros C R V. rewrite R in C.
  destruct (boxed_execute238 768 br
    (boxed_matches238 (site_start238 Q' (bool_nat238 overflow) phase))
    (site_start238 Q 0 FilePlain238) false) as [result|] eqn:E; [|discriminate].
  eapply boxed_execute238_restored; eassumption.
Qed.

Lemma checked_site238_variant Q e zero :
  check_site238 Q e = true -> e <> EHalt -> check_variant238 Q e zero = true.
Proof.
  destruct e; try (intros _ N; exfalso; apply N; reflexivity);
    cbn [check_site238]; intros C N; apply andb_true_iff in C as [A B];
    destruct zero; assumption.
Qed.

Theorem checked_site238_halt Q gap vs :
  check_site238 Q EHalt = true -> 9 <= length vs ->
  literal_halts238 (boxed_denote238 gap vs (site_start238 Q 0 FilePlain238)).
Proof.
  intros C V.
  change ((match boxed_execute238 768 None boxed_terminal238
    (site_start238 Q 0 FilePlain238) false with
    | Some _ => true | None => false
    end) = true) in C.
  destruct (boxed_execute238 768 None boxed_terminal238
    (site_start238 Q 0 FilePlain238) false) as [result|] eqn:E; [|discriminate C].
  eapply boxed_execute238_halts; [exact E|]. split; [exact V|exact I].
Qed.

Theorem inventory_site_checked238 p e :
  In (p,e) path_inventory238 -> check_site238 (path_of238 p) e = true.
Proof.
  intro H. pose proof all_sites_checked238 as C.
  pose proof (proj1 (@List.forallb_forall (positive * edge)
    path_site_check238 path_inventory238) C (p,e) H) as E.
  exact E.
Qed.

Lemma site_branch_valid238 Q e zero br Q' overflow phase vs :
  site_route238 Q e zero = Some (br, (Q', (overflow, phase))) ->
  9 <= length vs ->
  (forall r, e = EDecnz r -> zero = Nat.eqb (nth (slot_of238 r) vs 0) 0) ->
  branch_valid238 br vs.
Proof.
  destruct e as [node|r|r|k|k|]; cbn [site_route238]; intros R V Z; try discriminate;
    try (injection R as <- <- <- <-; split; [exact V|exact I]).
  destruct zero; injection R as <- <- <- <-; split; [exact V| |exact V|].
  - specialize (Z r eq_refl). symmetry in Z.
    apply Nat.eqb_eq in Z. exact Z.
  - specialize (Z r eq_refl). symmetry in Z.
    apply Nat.eqb_neq in Z. exact Z.
Qed.

Lemma segments_map_cells238 gap Q : segments_cells gap (map SCell Q) = Q.
Proof.
  induction Q as [|b Q IH]; [reflexivity|].
  change (b :: segments_cells gap (map SCell Q) = b :: Q).
  rewrite IH. reflexivity.
Qed.

Lemma site_start238_literal Q extra phase gap vs :
  boxed_denote238 gap vs (site_start238 Q extra phase) =
  denote (FC 25 [true]
    (Q ++ repeat false (gap + (38 + extra - length Q)) ++ true :: phase_cells238 phase vs)).
Proof.
  unfold boxed_denote238, site_start238, extend_right238, symbolic_denote.
  cbn [boxed_core238 boxed_phase238 symbolic_control head_left symbolic_left symbolic_right].
  rewrite !segments_cells_append238, segments_map_cells238.
  cbn [segments_cells flat_map segment_cells]. rewrite ?app_nil_r.
  replace (1 * gap + (38 + extra - length Q)) with
    (gap + (38 + extra - length Q)) by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.
