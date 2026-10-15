(** * Complete physical PA238 leaf coverage.

    This equality checks the whole unfolded physical decision tree against
    the authenticated4409-path inventory. Thus successful site checks cover
    every possible decoder walk, not only the listed sample PCs. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith PArith.BinPos Lia.
From P238.tm Require Import RM238 RMEquiv238 Leaves238 Prog238 Site238.
Local Unset Implicit Arguments.
Import ListNotations.

Theorem p238_wf : wf p238.
Proof. apply wf_check_sound. vm_compute. reflexivity. Qed.

Theorem physical238_all_leaves :
  leaves p238 186 0 =
  map (fun pe => (path_of238 (fst pe), snd pe)) path_inventory238.
Proof. vm_compute. reflexivity. Qed.

Definition edge_bound238 e :=
  match e with
  | ENode _ => false
  | EInc r | EDecnz r => Nat.ltb r 9
  | EBreak k | EContinue k => Nat.ltb 0 k
  | EHalt => true
  end.

Theorem complete_leaf238 Q e : In (Q,e) (leaves p238 186 0) ->
  length Q <= 34 /\ check_site238 Q e = true /\ edge_bound238 e = true.
Proof.
  rewrite physical238_all_leaves. intro H. apply in_map_iff in H.
  destruct H as [[p e'] [E H]]. cbn in E. injection E as <- <-.
  pose proof (proj1 (@List.forallb_forall (positive * edge)
    inventory_bound238 path_inventory238) path_inventory238_bounds (p,e') H) as B.
  cbn [inventory_bound238] in B.
  apply andb_true_iff in B as [L R]. apply Nat.leb_le in L.
  split; [exact L|]. split; [apply inventory_site_checked238; exact H|exact R].
Qed.

Theorem walk_complete238 P e d :
  walk p238 186 0 P 0 = Some (e,d) ->
  let Q := firstn d (P ++ repeat false d) in
  length Q <= 34 /\ check_site238 Q e = true /\ edge_bound238 e = true.
Proof. intro W. apply complete_leaf238. apply (leaves_root p238 P e d). exact W. Qed.
