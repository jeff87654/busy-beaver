(** * Actual source, complete physical file, and literal PA238 machine.

    The source helper proof permits arbitrary registers outside0..8. The
    physical invariant independently retains all old spare blocks and new
    allocations. Both finite execution directions use the checked literal
    site proofs and halt reflection, then the checked PA path-pair certificate. *)

From Coq Require Import Lists.List Arith.Arith Lia.
From P238.tm Require Import RM238 RMEquiv238 Prog238 Finite238 Bootstrap238
  LiteralHalting238 Reflection238 MachineProgram238 TM238.
From P238.prog Require Import Dag238 ProgLib238 L2Root238 BisimPA238.
From P238.logic Require Import Compiler238 Enum238.
Local Unset Implicit Arguments.
Import ListNotations.

Lemma dag238_wf : wf dag238.
Proof. apply wf_check_sound. vm_compute. reflexivity. Qed.

Lemma R_boot238_source : approx R_boot238 source_boot238.
Proof. intros i B. do 9 (destruct i as [|i]; [reflexivity|]). lia. Qed.

Theorem checkpoint238_enum_iff :
  literal_halts238 (denote checkpoint238) <-> enum238_boot_halts.
Proof.
  rewrite checkpoint238_literal_iff_program, p238_source_dag238.
  rewrite (rm_halts_iff_iter dag238 dag238_wf R_boot238).
  apply (iter_halts_dag_boot238 R_boot238 R_boot238_source).
Qed.

Theorem actual_pa238_machine_enum : blank_halts238 <-> enum238_boot_halts.
Proof.
  rewrite actual_pa238_machine_program, p238_source_dag238.
  rewrite (rm_halts_iff_iter dag238 dag238_wf R_boot238).
  apply (iter_halts_dag_boot238 R_boot238 R_boot238_source).
Qed.

Theorem enum_to_complete_file_execution238 fuel : enum_run fuel enum_boot = None ->
  exists steps c, exact_steps steps (denote checkpoint238) c /\ literal_halted238 c.
Proof.
  intro H. apply (proj2 checkpoint238_enum_iff). exists fuel. exact H.
Qed.

Theorem complete_file_execution_to_enum238 steps c :
  exact_steps steps (denote checkpoint238) c -> literal_halted238 c ->
  exists fuel, enum_run fuel enum_boot = None.
Proof.
  intros R H. apply (proj1 checkpoint238_enum_iff). exists steps, c. split; assumption.
Qed.

Theorem actual_pa238_machine_numeric : blank_halts238 <-> derivable 1.
Proof. rewrite actual_pa238_machine_enum. apply enum238_boot_code_endpoint. Qed.
