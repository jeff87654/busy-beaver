(** Original PA238 blank checkpoint computation target.

    This source must be compiled and independently reviewed before its lemmas
    are reported as accepted kernel evidence. The Python audit is never used
    as a premise. [checkpoint_computation] asks Coq's evaluator to replay the
    literal [tmn238] rows from blank tape afresh. *)

From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.Arith
  PArith.BinPos NArith.Nnat.
From BusyCoq Require Import TM.
From P238.tm Require Import Finite238.
Local Unset Implicit Arguments.
Import ListNotations.

Definition active_boot_registers : list nat := [0; 2; 0; 0; 0; 0; 6; 0; 0].
Definition spare_boot_registers : list nat := repeat 0 5 ++ 1 :: repeat 0 318.
Definition unary_file (registers : list nat) : list bool :=
  flat_map (fun value => false :: repeat true (S value)) registers.

(** Head is origin+1. H=39 measures header-origin; D=38 measures the blank
    cells starting at the head and ending immediately before the header. *)
Definition blank238 : finite_configuration := FC 0 [] [].
Definition checkpoint238 : finite_configuration :=
  FC 25 [true]
     (repeat false 38 ++ true :: unary_file (active_boot_registers ++ spare_boot_registers)).

Fixpoint trim_blanks (cells : list bool) : list bool :=
  match cells with
  | [] => []
  | bit :: cells =>
      match bit, trim_blanks cells with
      | false, [] => []
      | _, suffix => bit :: suffix
      end
  end.

Definition normalize (c : finite_configuration) : finite_configuration :=
  FC (control c) (trim_blanks (left_cells c)) (trim_blanks (right_cells c)).

Lemma trim_preserves_stream cells :
  Str_app (trim_blanks cells) (const false) = Str_app cells (const false).
Proof.
  induction cells as [|bit cells IH]; [reflexivity|].
  cbn [trim_blanks]. destruct (trim_blanks cells) as [|b tail] eqn:E;
    destruct bit; cbn [Str_app] in *; rewrite <- IH; try reflexivity.
  apply const_unfold.
Qed.

Lemma normalize_denote c : denote (normalize c) = denote c.
Proof.
  destruct c as [q l r]. unfold denote, normalize; cbn.
  rewrite !trim_preserves_stream. reflexivity.
Qed.

Definition finite_configuration_dec (c d : finite_configuration) : {c = d} + {c <> d}.
Proof.
  decide equality; first [apply Nat.eq_dec | apply list_eq_dec; apply bool_dec].
Defined.

Definition checkpoint_check : bool :=
  match execute 799504%positive blank238 with
  | None => false
  | Some c => if finite_configuration_dec (normalize c) checkpoint238 then true else false
  end.

Lemma checkpoint_computation : checkpoint_check = true.
Proof. vm_compute. reflexivity. Qed.

(** Prove the count through the injective binary embedding. Reifying the
    computed unary [nat] itself would require a 799504-deep term. *)
Lemma binary_steps_799504 : binary_steps 799504%positive = 799504.
Proof. apply Nat2N.inj. vm_compute. reflexivity. Qed.

Theorem blank_reaches_checkpoint238 :
  exact_steps 799504 (denote blank238) (denote checkpoint238).
Proof.
  pose proof checkpoint_computation as H. unfold checkpoint_check in H.
  destruct (execute 799504%positive blank238) as [c|] eqn:E; [|discriminate].
  destruct (finite_configuration_dec (normalize c) checkpoint238) as [C|]; [|discriminate].
  pose proof (execute_literal _ _ _ E) as S.
  rewrite binary_steps_799504 in S.
  rewrite <- (normalize_denote c), C in S. exact S.
Qed.

Lemma boot_register_counts :
  length active_boot_registers = 9 /\ length spare_boot_registers = 324 /\
  List.nth 5 spare_boot_registers 0 = 1.
Proof. vm_compute. auto. Qed.
