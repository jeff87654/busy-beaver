(** * Closed checks of every actual PA238 instruction site.

    This module isolates the stable executable definitions and exhaustive
    literal round-trip certificate. Site238 supplies the semantic transports
    from this checked certificate to complete literal configurations. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith PArith.BinPos Lia.
From P238.tm Require Import RM238 Prog238 Finite238 Symbolic238 RegisterTape238
  LiteralHalting238 Boxed238 BoxedNormalize238 BoxedExecute238.
Local Unset Implicit Arguments.
Import ListNotations.

Definition site_start238 (Q : list bool) (extra : nat) (phase : file_phase238) :=
  BConfig238 (SC 25 false [SCell true]
    (map SCell Q ++ [SRun false 1 (38 + extra - length Q); SCell true])) phase.

Definition allones238 Q := forallb (fun b : bool => b) Q.
Definition bool_nat238 (b : bool) := if b then 1 else 0.
Definition route238 := (file_branch238 * (list bool * (bool * file_phase238)))%type.

Definition site_route238 (Q : list bool) (e : edge) (zero : bool) : option route238 :=
  match e with
  | EInc r =>
      Some (None, (inc_path Q, (allones238 Q, FileIncremented238 (slot_of238 r))))
  | EDecnz r =>
      if zero then
        Some (Some (slot_of238 r, true),
          (brk 1 Q, (allones238 (strip_path false 1 Q), FilePlain238)))
      else Some (Some (slot_of238 r, false),
          (inc_path Q, (allones238 Q, FileDecremented238 (slot_of238 r))))
  | EBreak k =>
      Some (None, (brk k Q, (allones238 (strip_path false k Q), FilePlain238)))
  | EContinue k => Some (None, (cont k Q, (false, FilePlain238)))
  | _ => None
  end.

Definition check_variant238 Q e zero :=
  match site_route238 Q e zero with
  | None => false
  | Some (br, (Q', (overflow, phase))) =>
      match boxed_execute238 768 br
        (boxed_matches238 (site_start238 Q' (bool_nat238 overflow) phase))
        (site_start238 Q 0 FilePlain238) false with
      | Some _ => true
      | None => false
      end
  end.

Definition check_halt238 Q :=
  match boxed_execute238 768 None boxed_terminal238
    (site_start238 Q 0 FilePlain238) false with
  | Some _ => true
  | None => false
  end.

Definition check_site238 Q e :=
  match e with
  | EHalt => check_halt238 Q
  | _ => andb (check_variant238 Q e false) (check_variant238 Q e true)
  end.

Definition path_site_check238 (pe : positive * edge) :=
  check_site238 (path_of238 (fst pe)) (snd pe).

Theorem all_sites_checked238 : forallb path_site_check238 path_inventory238 = true.
Proof. vm_compute. reflexivity. Qed.
