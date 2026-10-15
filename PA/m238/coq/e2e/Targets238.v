(** Exact external target propositions and their actual finite proof
    and literal execution transports. All contracts are proved below. *)

From P238.tm Require Import TM238.
From P238.arith Require Import PAeq238.

Definition pa238_ordinary_refutation_to_halt : Prop :=
  PA238.PAeq_inconsistent -> blank_halts238.

Definition pa238_halt_to_ordinary_refutation : Prop :=
  blank_halts238 -> PA238.PAeq_inconsistent.

Definition pa238_halts_iff_ordinary_PA : Prop :=
  blank_halts238 <-> PA238.PAeq_inconsistent.

(** The implementation must supply the actual derivation-to-command-list
    compiler, candidate enumeration, register simulation and literal TM
    execution witnesses in the forward direction, and their sound inverse
    correspondences in the reverse direction. *)

From P238.tm Require Import Table238 Finite238 Bootstrap238.
From P238.logic Require Import Compiler238 Enum238.

(** The imported Compiler238/Enum238 modules provide kernel-checked
    finite compilation, candidate drainage/reach, and
    [Enum238.enum238_boot_code_endpoint]. The ordinary PAeq-to-numeric
    and literal-halting transports are proved below in both directions.
    The complete checkpoint execution transports are also proved below.

    Named transport propositions are inhabited below by actual proofs. The literal starting tape is the complete [checkpoint238]:
    all nine active blocks, all 324 spare blocks, and the nonzero spare at
    zero-based index 5. Its physical aliases project to pending 0, nextproof
    6, and retained numeric registers (0,0,2,0). The source helpers' scratch
    registers and spare-block effects must be tracked throughout execution;
    [enum_from_physical] alone supplies no execution correspondence. *)
Definition pa238_enum_to_scratch_and_spare_execution : Prop :=
  forall fuel, enum_run fuel enum_boot = None ->
    exists steps c,
      exact_steps steps (denote checkpoint238) c /\
      (let '(q, (_, b, _)) := c in tmn238 q b = None).

Definition pa238_scratch_and_spare_execution_to_enum : Prop :=
  forall steps c,
    exact_steps steps (denote checkpoint238) c ->
    (let '(q, (_, b, _)) := c in tmn238 q b = None) ->
    exists fuel, enum_run fuel enum_boot = None.

Definition pa238_ordinary_refutation_to_numeric : Prop :=
  PA238.PAeq_inconsistent -> derivable 1.

Definition pa238_numeric_refutation_to_ordinary : Prop :=
  derivable 1 -> PA238.PAeq_inconsistent.

(** Actual complete-file execution transports, closed in both directions. *)
From P238.prog Require Import SourceMachine238.

Theorem pa238_enum_execution_proved :
  pa238_enum_to_scratch_and_spare_execution.
Proof. exact enum_to_complete_file_execution238. Qed.

Theorem pa238_execution_enum_proved :
  pa238_scratch_and_spare_execution_to_enum.
Proof. exact complete_file_execution_to_enum238. Qed.

(** Actual finite ordinary PA proof compilation and literal execution. *)
From P238.arith Require Import PAForward238.
From P238.logic Require Import NativePointed238.

Theorem pa238_ordinary_numeric_proved :
  pa238_ordinary_refutation_to_numeric.
Proof.
  intro H. apply NativePointed238.NativePointed238.S0_numeric_refutation.
  exact (PAForward238.PAForward238.ordinary_PAeq_refutation_to_S0 H).
Qed.

Theorem pa238_ordinary_halt_proved :
  pa238_ordinary_refutation_to_halt.
Proof.
  intro H. apply (proj2 actual_pa238_machine_numeric).
  exact (pa238_ordinary_numeric_proved H).
Qed.

(** Actual finite ordinary PA arithmetic discharges the reverse compiler. *)
From P238.arith Require Import PABoundedComprehension238 PACompactReverse238.

Theorem pa238_numeric_ordinary_proved :
  pa238_numeric_refutation_to_ordinary.
Proof.
  exact (PACompactReverse238.PACompactReverse238.numeric_refutation_to_ordinary_PA
    PABoundedComprehension238.PABoundedComprehension238.actual_bounded_comprehension).
Qed.

Theorem pa238_halt_ordinary_proved :
  pa238_halt_to_ordinary_refutation.
Proof.
  intro H. apply pa238_numeric_ordinary_proved.
  exact (proj1 actual_pa238_machine_numeric H).
Qed.

Theorem pa238_iff_ordinary_proved :
  pa238_halts_iff_ordinary_PA.
Proof.
  split; [exact pa238_halt_ordinary_proved | exact pa238_ordinary_halt_proved].
Qed.

(** Standard metamathematical background: K. Goedel,
    Ueber formal unentscheidbare Saetze der Principia Mathematica und
    verwandter Systeme I, Monatshefte fuer Mathematik und Physik 38
    (1931), 173-198, second incompleteness theorem. The checked result
    above is the finite proof / literal execution equivalence. *)
