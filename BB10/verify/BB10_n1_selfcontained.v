(** * A Busy Beaver candidate for 10 states and 2 symbols that beats the BB(10) champion:
      a self-contained, machine-checked proof *)

(** Machine n1 (bbchallenge standard format; the undefined transition J0 is the halt):

      1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_---0LC

          0    1
      A  1RB  0RA
      B  1LC  1LF
      C  1RD  0LB
      D  1RA  1LE
      E  1LI  0LC
      F  0RG  1LD
      G  1RH  1LG
      H  1LC  0RG
      I  0LJ  0LI
      J  ---  0LC

    n1 is the G/H-swap sibling of the BB(8) record 1RB0RA_1LC1LF_1RD0LB_1RA1LE_---0LC_0RG1LD_1RH1LG_1LC0RG with
    E0 := 1LI and two new states I = 0LJ0LI, J = ---0LC (bb8 project, Jeff Ketchersid with Claude, 2026-10-08).

    This file proves, with no axioms and no dependency other than the Coq standard library
    (arrow k a b = Knuth's a ^(k arrows) b, with arrow 0 a b = a * b; iter n g x = g^n (x)):

      n1_halts             : n1 halts from the blank tape.
      n1_score_exact       : the halting tape holds exactly 2 w + f + 3 k + 22 ones for some f, k and
                               w >= iter (2 JJ + 1) (fun n => arrow n 2 4) 34,   JJ = (3 T - 13) / 7,  T = arrow 37 2 3.
      n1_sigma_lower_bound : the number of ones exceeds  iter ((6 T - 19) / 7) (fun x => arrow (x + 1) 2 3) 33.
      n1_beats_M3_bound    : it exceeds  arrow (4T+41) 2 (arrow (4T+39) 2 (arrow (4T+35) 2 5))  (the proved lower bound
                             of another 10-state candidate, M3; not a comparison of exact scores).
      n1_beats_champion    : the BB(10) champion 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ
                             (Racheline; Module Champion10: its own halting proof and exact score b2 + 3) halts with
                             Nc ones, n1 halts with No ones, and Nc + 1 < No + 1.
      n1_beats_lead        : the same against the 10-state candidate
                             1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LJ0LC_1RG1LD_0RI0RH_1RG1LF_1RE1RI_---1LC (Module Lead10).
      n1_fgh_level         : in the fast-growing hierarchy, f_(omega+1) ((3T - 13)/7 - 2) < N < f_(omega+1) (6T).
      n1_fgh_lower_64      : f_(omega+1) (64) < N.
      graham_lt_f_omega1_64: Graham's number < f_(omega+1) (64).
      n1_beats_graham      : Graham's number < N.

    Score convention.  busycoq stops BEFORE the undefined transition.  n1 and 0LJ0LC then read a 0 at the
    undefined J0, and the champion reads a 0 at E0 = 1RZ, so in each case the final 1RZ write adds one 1: the
    standard scores are No + 1, Nl + 1 and Nc + 1.  (With a final write of 0 the comparison is Nc < No, the same
    inequality.)

    How to check (Coq 8.20.1):

      coqc BB10_n1_selfcontained.v

    The last lines of the output must be "Closed under the global context", once for each of the twenty-eight
    `Print Assumptions` at the end of this file.  The only warnings are deprecation notices, LibTactics'
    `ltac_Mark` notice and notation re-declarations.

    Conventions.  Configurations, steps and halting are busycoq's (module TM below): a configuration is
    (state, (left stream, head symbol, right stream)); `halted tm c` means that the transition for the current
    (state, symbol) is undefined, and `halts tm c0` that such a configuration is reached from the blank tape
    `c0 = (A, (0^inf, 0, 0^inf))`.  `ones c N` says the tape of c is a finite list L, the head symbol s and a finite
    list R (then 0s) with N ones in L, s and R.

    Structure of this file.
      1. busycoq's core library (meithecatte/busycoq, verify/ directory, commit bd2e36f; MIT licence below),
         inlined verbatim, one module per file:  LibTactics, Helper, TM, Compute, Flip, Permute, Individual.
      2. The 10-state instantiation BB102 / Individual102 (as busycoq's BB52 / Individual52).
      3. Module Champion10: the BB(10) champion halts (digit-list counter, rules R1-R4) and its exact score
         (BB10_champion_1RB1RA.v, BB10_champion_bound.v).
      4. Module Lead10: 0LJ0LC halts, its exact score, and its score exceeds the champion's
         (BB10_lead_1RB0RA.v, BB10_lead_bound.v, BB10_lead_vs_champion.v).
      5. Module N1: n1 halts (BB10_n1.v: 6447 literal steps, then the B-form rules R1, R2 and the clearing CLR
         proved at machine level for all parameters, JJ periods of the PERIOD stage, ENDGAME, HALT) and its score
         and comparisons (BB10_n1_bound.v), the closed form of the score (BB10_n1_exact.v), and its level in the
         fast-growing hierarchy and Graham's number (BB10_n1_fgh.v).
      6. The main theorems.
    The published multi-file set compiles the same eleven files in the order BB102, Individual102, BB10_n1,
    BB10_lead_1RB0RA, BB10_lead_bound, BB10_champion_1RB1RA, BB10_champion_bound, BB10_lead_vs_champion,
    BB10_n1_bound, BB10_n1_exact, BB10_n1_fgh.  Here each machine's files stay together in one module, so the
    modules come in dependency order (Champion10 before Lead10, whose comparison file uses it, and both before N1,
    whose score file uses them); within each module the files keep that order.
    The original multi-file development is in bb8_list/proofs; this file was assembled from it by
    gen_selfcontained_n1.py without changing any proof text: `Require` lines are hoisted or turned into `Import`,
    each inlined file starts in the symbol scope as it originally did, the three developments are wrapped in
    modules and the qualified names BB10_champion_*.x, BB10_lead_*.x are renamed Champion10.x, Lead10.x (in code;
    the comments keep the original file names), and where two original files share a module the later one starts
    with `Transparent` for the constants the earlier one made Opaque (Opaque does not cross a Require).  The only
    other textual changes rename constructors behind abbreviations with their old names: in BB102 the states are
    St_A ... St_J with `Notation A := St_A` ... `Notation J := St_J`, and in busycoq's TM.v the directions are
    St_L, St_R with `Notation L := St_L`, `Notation R := St_R` (see the comment at [state]; this keeps the names
    Coq invents in proofs, e.g. for `intros` on `forall L t ts A, ...`, the same as in the multi-file build).

    busycoq licence (third_party/busycoq/LICENSE):
      Copyright (c) 2023 Maja Kadziolka.  Permission is hereby granted, free of charge, to any person obtaining a
      copy of this software and associated documentation files (the "Software"), to deal in the Software without
      restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute,
      sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do
      so, subject to the following conditions: The above copyright notice and this permission notice shall be
      included in all copies or substantial portions of the Software.  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT
      WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
      FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
      LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
      FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
    LibTactics.v (MIT X11 licence, third_party/busycoq/LICENSE-LibTactics): Copyright (c) 2018 Arthur Chargueraud;
      same permission notice as above, and: except as contained in this notice, the name of the copyright holders
      shall not be used in advertising or otherwise to promote the sale, use or other dealings in this Software
      without prior written authorization from the copyright holders. *)

From Coq Require Import Lia PeanoNat List.
Import ListNotations.
(* every library used by the inlined files; each is imported where the original file imported it *)
Require Coq.Arith.Compare_dec Coq.Arith.Wf_nat Coq.Bool.Bool Coq.Bool.Sumbool Coq.Lists.Streams Coq.Logic.FunctionalExtensionality Coq.Logic.ProofIrrelevance Coq.NArith.BinNat Coq.NArith.Nnat Coq.Numbers.BinNums Coq.PArith.BinPos Coq.PArith.Pnat Coq.Program.Equality Coq.Program.Tactics Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.micromega.ZifyClasses.
(* no global `Set Default Goal Selector "!"` here: LibTactics.v is written without it; every later part
   sets it for itself, as the original files do *)

(* ==================================================================================================== *)
(*              busycoq/verify/LibTactics.v  (commit bd2e36f, MIT licence, see the header)              *)
(* ==================================================================================================== *)

Module BusyCoq_LibTactics.

(** * LibTactics: A Collection of Handy General-Purpose Tactics *)

(** This file has been copied from "Programming Language Foundations", a textbook
    from the "Software Foundations" series. The origin of this file seems to be
    https://github.com/charguer/tlc – with Arthur Charguéraud being the original
    author. See LICENSE-LibTactics. *)

(** Some changes have been introduced for the purposes of BusyCoq:
    - the [>>] notation has been marked [Local]. *)

(** This file contains a set of tactics that extends the set of builtin
    tactics provided with the standard distribution of Coq. It intends
    to overcome a number of limitations of the standard set of tactics,
    and thereby to help user to write shorter and more robust scripts.

    Hopefully, Coq tactics will be improved as time goes by, and this
    file should ultimately be useless. In the meanwhile, serious Coq
    users will probably find it very useful.

    The present file contains the implementation and the detailed
    documentation of those tactics. The SF reader need not read this
    file; instead, he/she is encouraged to read the chapter named
    UseTactics.v, which is gentle introduction to the most useful
    tactics from the LibTactic library.
*)

(** The main features offered are:
       - More convenient syntax for naming hypotheses, with tactics for
         introduction and inversion that take as input only the name of
         hypotheses of type [Prop], rather than the name of all variables.
       - Tactics providing true support for manipulating N-ary conjunctions,
         disjunctions and existentials, hidding the fact that the underlying
         implementation is based on binary propositions.
       - Convenient support for automation: tactics followed with the symbol
         "~" or "*" will call automation on the generated subgoals.
         The symbol "~" stands for [auto] and "*" for [intuition eauto].
         These bindings can be customized.
       - Forward-chaining tactics are provided to instantiate lemmas
         either with variable or hypotheses or a mix of both.
       - A more powerful implementation of [apply] is provided (it is based
         on [refine] and thus behaves better with respect to conversion).
       - An improved inversion tactic which substitutes equalities on variables
         generated by the standard inversion mecanism. Moreover, it supports
    the elimination of dependently typed equalities (requires axiom [K],
         which is a weak form of Proof Irrelevance).
       - Tactics for saving time when writing proofs, with tactics to
         asserts hypotheses or sub-goals, and improved tactics for
         clearing, renaming, and sorting hypotheses. *)

(** External credits:
  - thanks to Xavier Leroy for providing the idea of tactic [forward]
  - thanks to Georges Gonthier for the implementation trick in [rapply]
*)

Set Implicit Arguments.

Import Coq.Lists.List.

Declare Scope ltac_scope.

(* ################################################################# *)
(** * Fixing Stdlib *)

(* Very important to remove hint trans_eq_bool from LibBool,
   otherwise eauto slows down dramatically:
  Lemma test : forall b, b = false.
  time eauto 7. (* takes over 4 seconds to fail! *) *)

#[global]
Remove Hints Bool.trans_eq_bool : core.

(* ################################################################# *)
(** * Tools for Programming with Ltac *)

(* ================================================================= *)
(** ** Identity Continuation *)

Ltac idcont tt :=
  idtac.

(* ================================================================= *)
(** ** Untyped Arguments for Tactics *)

(** Any Coq value can be boxed into the type [Boxer]. This is
    useful to use Coq computations for implementing tactics. *)

Inductive Boxer : Type :=
  | boxer : forall (A:Type), A -> Boxer.

(* ================================================================= *)
(** ** Optional Arguments for Tactics  *)

(** [ltac_no_arg] is a constant that can be used to simulate
    optional arguments in tactic definitions.
    Use [mytactic ltac_no_arg] on the tactic invokation,
    and use [match arg with ltac_no_arg => ..] or
    [match type of arg with ltac_No_arg  => ..] to
    test whether an argument was provided. *)

Inductive ltac_No_arg : Set :=
  | ltac_no_arg : ltac_No_arg.

(* ================================================================= *)
(** ** Wildcard Arguments for Tactics  *)

(** [ltac_wild] is a constant that can be used to simulate
    wildcard arguments in tactic definitions. Notation is [__]. *)

Inductive ltac_Wild : Set :=
  | ltac_wild : ltac_Wild.

Notation "'__'" := ltac_wild : ltac_scope.

(** [ltac_wilds] is another constant that is typically used to
    simulate a sequence of [N] wildcards, with [N] chosen
    appropriately depending on the context. Notation is [___]. *)

Inductive ltac_Wilds : Set :=
  | ltac_wilds : ltac_Wilds.

Notation "'___'" := ltac_wilds : ltac_scope.

Open Scope ltac_scope.

(* ================================================================= *)
(** ** Position Markers *)

(** [ltac_Mark] and [ltac_mark] are dummy definitions used as sentinel
    by tactics, to mark a certain position in the context or in the goal. *)

Inductive ltac_Mark : Type :=
  | ltac_mark : ltac_Mark.

(** [gen_until_mark] repeats [generalize] on hypotheses from the
    context, starting from the bottom and stopping as soon as reaching
    an hypothesis of type [Mark]. If fails if [Mark] does not
    appear in the context. *)

Ltac gen_until_mark :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => generalize H; clear H; gen_until_mark
  end end.

(** [gen_until_mark_with_processing F] is similar to [gen_until_mark]
    except that it calls [F] on each hypothesis immediately before
    generalizing it. This is useful for processing the hypotheses. *)

Ltac gen_until_mark_with_processing cont :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => cont H; generalize H; clear H;
         gen_until_mark_with_processing cont
  end end.

(** [intro_until_mark] repeats [intro] until reaching an hypothesis of
    type [Mark]. It throws away the hypothesis [Mark].
    It fails if [Mark] does not appear as an hypothesis in the
    goal. *)

Ltac intro_until_mark :=
  match goal with
  | |- (ltac_Mark -> _) => intros _
  | _ => intro; intro_until_mark
  end.

(* ================================================================= *)
(** ** List of Arguments for Tactics  *)

(** A datatype of type [list Boxer] is used to manipulate list of
    Coq values in ltac. Notation is [>> v1 v2 ... vN] for building
    a list containing the values [v1] through [vN]. *)
(* Note: could attempt the use of a recursive notation *)

Local Notation "'>>'" :=
  (@nil Boxer)
  (at level 0)
  : ltac_scope.
Local Notation "'>>' v1" :=
  ((boxer v1)::nil)
  (at level 0, v1 at level 0)
  : ltac_scope.
Local Notation "'>>' v1 v2" :=
  ((boxer v1)::(boxer v2)::nil)
  (at level 0, v1 at level 0, v2 at level 0)
  : ltac_scope.
Local Notation "'>>' v1 v2 v3" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0)
  : ltac_scope.
Local Notation "'>>' v1 v2 v3 v4" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0)
  : ltac_scope.
Local Notation "'>>' v1 v2 v3 v4 v5" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0)
  : ltac_scope.
Local Notation "'>>' v1 v2 v3 v4 v5 v6" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0)
  : ltac_scope.
Local Notation "'>>' v1 v2 v3 v4 v5 v6 v7" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0)
  : ltac_scope.
Local Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0)
  : ltac_scope.
Local Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0)
  : ltac_scope.
Local Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0)
  : ltac_scope.
Local Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0)
  : ltac_scope.
Local Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::(boxer v12)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
   v12 at level 0)
  : ltac_scope.
Local Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::(boxer v12)::(boxer v13)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
   v12 at level 0, v13 at level 0)
  : ltac_scope.

(** The tactic [list_boxer_of] inputs a term [E] and returns a term
    of type "list boxer", according to the following rules:
    - if [E] is already of type "list Boxer", then it returns [E];
    - otherwise, it returns the list [(boxer E)::nil]. *)
Ltac list_boxer_of E :=
  match type of E with
  | List.list Boxer => constr:(E)
  | _ => constr:((boxer E)::nil)
  end.

(* ================================================================= *)
(** ** Databases of Lemmas  *)

(** Use the hint facility to implement a database mapping
    terms to terms. To declare a new database, use a definition:
    [Definition mydatabase := True.]

    Then, to map [mykey] to [myvalue], write the hint:
    [Hint Extern 1 (Register mydatabase mykey) => Provide myvalue.]

    Finally, to query the value associated with a key, run the
    tactic [ltac_database_get mydatabase mykey]. This will leave
    at the head of the goal the term [myvalue]. It can then be
    named and exploited using [intro]. *)

Inductive Ltac_database_token : Prop := ltac_database_token.

Definition ltac_database (D:Boxer) (T:Boxer) (A:Boxer) := Ltac_database_token.

Notation "'Register' D T" := (ltac_database (boxer D) (boxer T) _)
  (at level 69, D at level 0, T at level 0).

Lemma ltac_database_provide : forall (A:Boxer) (D:Boxer) (T:Boxer),
  ltac_database D T A.
Proof using. split. Qed.

Ltac Provide T := apply (@ltac_database_provide (boxer T)).

Ltac ltac_database_get D T :=
  let A := fresh "TEMP" in evar (A:Boxer);
  let H := fresh "TEMP" in
  assert (H : ltac_database (boxer D) (boxer T) A);
  [ subst A; auto
  | subst A; match type of H with ltac_database _ _ (boxer ?L) =>
               generalize L end; clear H ].

(* Note for a possible alternative implementation of the ltac_database_token:
   Inductive Ltac_database : Type :=
     | ltac_database : forall A, A -> Ltac_database.
   Implicit Arguments ltac_database [A].
*)

(* ================================================================= *)
(** ** On-the-Fly Removal of Hypotheses *)

(** In a list of arguments [>> H1 H2 .. HN] passed to a tactic
    such as [lets] or [applys] or [forwards] or [specializes],
    the term [rm], an identity function, can be placed in front
    of the name of an hypothesis to be deleted. *)

Definition rm (A:Type) (X:A) := X.

(** [rm_term E] removes one hypothesis that admits the same
    type as [E]. *)

Ltac rm_term E :=
  let T := type of E in
  match goal with H: T |- _ => try clear H end.

(** [rm_inside E] calls [rm_term Ei] for any subterm
    of the form [rm Ei] found in E *)

Ltac rm_inside E :=
  let go E := rm_inside E in
  match E with
  | rm ?X => rm_term X
  | ?X1 ?X2 =>
     go X1; go X2
  | ?X1 ?X2 ?X3 =>
     go X1; go X2; go X3
  | ?X1 ?X2 ?X3 ?X4 =>
     go X1; go X2; go X3; go X4
  | ?X1 ?X2 ?X3 ?X4 ?X5 =>
     go X1; go X2; go X3; go X4; go X5
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 =>
     go X1; go X2; go X3; go X4; go X5; go X6
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 ?X9 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8; go X9
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 ?X9 ?X10 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8; go X9; go X10
  | _ => idtac
  end.

(** For faster performance, one may deactivate [rm_inside] by
    replacing the body of this definition with [idtac]. *)

Ltac fast_rm_inside E :=
  rm_inside E.

(* ================================================================= *)
(** ** Numbers as Arguments *)

(** When tactic takes a natural number as argument, it may be
    parsed either as a natural number or as a relative number.
    In order for tactics to convert their arguments into natural numbers,
    we provide a conversion tactic.

    Note: the tactic [number_to_nat] is extended in [LibInt] to
    take into account the [Z] type. *)



Definition ltac_int_to_nat (x:BinInt.Z) : nat :=
  match x with
  | BinInt.Z0 => 0%nat
  | BinInt.Zpos p => BinPos.nat_of_P p
  | BinInt.Zneg p => 0%nat
  end.

Ltac number_to_nat N :=
  match type of N with
  | nat => constr:(N)
  | BinInt.Z => let N' := constr:(ltac_int_to_nat N) in eval compute in N'
  end.

(** [ltac_pattern E at K] is the same as [pattern E at K] except that
    [K] is a Coq number (nat or Z) rather than a Ltac integer. Syntax
    [ltac_pattern E as K in H] is also available. *)

Tactic Notation "ltac_pattern" constr(E) "at" constr(K) :=
  match number_to_nat K with
  | 1 => pattern E at 1
  | 2 => pattern E at 2
  | 3 => pattern E at 3
  | 4 => pattern E at 4
  | 5 => pattern E at 5
  | 6 => pattern E at 6
  | 7 => pattern E at 7
  | 8 => pattern E at 8
  | _ => fail "ltac_pattern: arity not supported"
  end.

Tactic Notation "ltac_pattern" constr(E) "at" constr(K) "in" hyp(H) :=
  match number_to_nat K with
  | 1 => pattern E at 1 in H
  | 2 => pattern E at 2 in H
  | 3 => pattern E at 3 in H
  | 4 => pattern E at 4 in H
  | 5 => pattern E at 5 in H
  | 6 => pattern E at 6 in H
  | 7 => pattern E at 7 in H
  | 8 => pattern E at 8 in H
  | _ => fail "ltac_pattern: arity not supported"
  end.

(** [ltac_set (x := E) at K] is the same as [set (x := E) at K] except
    that [K] is a Coq number (nat or Z) rather than a Ltac integer. *)

Tactic Notation "ltac_set" "(" ident(X) ":=" constr(E) ")" "at" constr(K) :=
  match number_to_nat K with
  | 1%nat => set (X := E) at 1
  | 2%nat => set (X := E) at 2
  | 3%nat => set (X := E) at 3
  | 4%nat => set (X := E) at 4
  | 5%nat => set (X := E) at 5
  | 6%nat => set (X := E) at 6
  | 7%nat => set (X := E) at 7
  | 8%nat => set (X := E) at 8
  | 9%nat => set (X := E) at 9
  | 10%nat => set (X := E) at 10
  | 11%nat => set (X := E) at 11
  | 12%nat => set (X := E) at 12
  | 13%nat => set (X := E) at 13
  | _ => fail "ltac_set: arity not supported"
  end.

(* ================================================================= *)
(** ** Testing Tactics *)

(** [show tac] executes a tactic [tac] that produces a result,
    and then display its result. *)

Tactic Notation "show" tactic(tac) :=
  let R := tac in pose R.

(** [dup N] produces [N] copies of the current goal. It is useful
    for building examples on which to illustrate behaviour of tactics.
    [dup] is short for [dup 2]. *)

Lemma dup_lemma : forall P, P -> P -> P.
Proof using. auto. Qed.

Ltac dup_tactic N :=
  match number_to_nat N with
  | 0 => idtac
  | S 0 => idtac
  | S ?N' => apply dup_lemma; [ | dup_tactic N' ]
  end.

Tactic Notation "dup" constr(N) :=
  dup_tactic N.
Tactic Notation "dup" :=
  dup 2.

(* ================================================================= *)
(** ** Testing evars and non-evars *)

(** [is_not_evar E] succeeds only if [E] is not an evar;
    it fails otherwise. It thus implements the negation of [is_evar] *)

Ltac is_not_evar E :=
  first [ is_evar E; fail 1
        | idtac ].

(** [is_evar_as_bool E] evaluates to [true] if [E] is an evar
    and to [false] otherwise. *)

Ltac is_evar_as_bool E :=
  constr:(ltac:(first
    [ is_evar E; exact true
    | exact false ])).

(** [has_no_evar E] succeeds if [E] contains no evars. *)

Ltac has_no_evar E :=
  first [ has_evar E; fail 1 | idtac ].

(* ================================================================= *)
(** ** Check No Evar in Goal *)

Ltac check_noevar M :=
  first [ has_evar M; fail 2 | idtac ].

Ltac check_noevar_hyp H :=
  let T := type of H in check_noevar T.

Ltac check_noevar_goal :=
  match goal with |- ?G => check_noevar G end.

(* ================================================================= *)
(** ** Helper Function for Introducing Evars *)

(** [with_evar T (fun M => tac)] creates a new evar that can
    be used in the tactic [tac] under the name [M]. *)

Ltac with_evar_base T cont :=
  let x := fresh "TEMP" in evar (x:T); cont x; subst x.

Tactic Notation "with_evar" constr(T) tactic(cont) :=
  with_evar_base T cont.

(* ================================================================= *)
(** ** Tagging of Hypotheses *)

(** [get_last_hyp tt] is a function that returns the last hypothesis
    at the bottom of the context. It is useful to obtain the default
    name associated with the hypothesis, e.g.
    [intro; let H := get_last_hyp tt in let H' := fresh "P" H in ...] *)

Ltac get_last_hyp tt :=
  match goal with H: _ |- _ => constr:(H) end.

(* ================================================================= *)
(** ** More Tagging of Hypotheses *)

(** [ltac_tag_subst] is a specific marker for hypotheses
    which is used to tag hypotheses that are equalities to
    be substituted. *)

Definition ltac_tag_subst (A:Type) (x:A) := x.

(** [ltac_to_generalize] is a specific marker for hypotheses
    to be generalized. *)

Definition ltac_to_generalize (A:Type) (x:A) := x.

Ltac gen_to_generalize :=
  repeat match goal with
    H: ltac_to_generalize _ |- _ => generalize H; clear H end.

Ltac mark_to_generalize H :=
  let T := type of H in
  change T with (ltac_to_generalize T) in H.

(* ================================================================= *)
(** ** Deconstructing Terms *)

(** [get_head E] is a tactic that returns the head constant of the
    term [E], ie, when applied to a term of the form [P x1 ... xN]
    it returns [P]. If [E] is not an application, it returns [E].
    Warning: the tactic seems to loop in some cases when the goal is
    a product and one uses the result of this function. *)

Ltac get_head E :=
  match E with
  | ?E' ?x => get_head E'
  | _ => constr:(E)
  end.

(** [get_fun_arg E] is a tactic that decomposes an application
  term [E], ie, when applied to a term of the form [X1 ... XN]
  it returns a pair made of [X1 .. X(N-1)] and [XN]. *)

Ltac get_fun_arg E :=
  match E with
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X => constr:((X1 X2 X3 X4 X5 X6 X7,X))
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X => constr:((X1 X2 X3 X4 X5 X6,X))
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X => constr:((X1 X2 X3 X4 X5,X))
  | ?X1 ?X2 ?X3 ?X4 ?X => constr:((X1 X2 X3 X4,X))
  | ?X1 ?X2 ?X3 ?X => constr:((X1 X2 X3,X))
  | ?X1 ?X2 ?X => constr:((X1 X2,X))
  | ?X1 ?X => constr:((X1,X))
  end.

(* ================================================================= *)
(** ** Action at Occurence and Action Not at Occurence *)

(** [ltac_action_at K of E do Tac] isolates the [K]-th occurence of [E] in the
    goal, setting it in the form [P E] for some named pattern [P],
    then calls tactic [Tac], and finally unfolds [P]. Syntax
    [ltac_action_at K of E in H do Tac] is also available. *)

Tactic Notation "ltac_action_at" constr(K) "of" constr(E) "do" tactic(Tac) :=
  let p := fresh "TEMP" in ltac_pattern E at K;
  match goal with |- ?P _ => set (p:=P) end;
  Tac; unfold p; clear p.

Tactic Notation "ltac_action_at" constr(K) "of" constr(E) "in" hyp(H) "do" tactic(Tac) :=
  let p := fresh "TEMP" in ltac_pattern E at K in H;
  match type of H with ?P _ => set (p:=P) in H end;
  Tac; unfold p in H; clear p.

(** [protects E do Tac] temporarily assigns a name to the expression [E]
    so that the execution of tactic [Tac] will not modify [E]. This is
    useful for instance to restrict the action of [simpl]. *)

Tactic Notation "protects" constr(E) "do" tactic(Tac) :=
  (* let x := fresh "TEMP" in sets_eq x: E; T; subst x. *)
  let x := fresh "TEMP" in let H := fresh "TEMP" in
  set (X := E) in *; assert (H : X = E) by reflexivity;
  clearbody X; Tac; subst x.

Tactic Notation "protects" constr(E) "do" tactic(Tac) "/" :=
  protects E do Tac.

(* ================================================================= *)
(** ** An Alias for [eq] *)

(** [eq'] is an alias for [eq] to be used for equalities in
    inductive definitions, so that they don't get mixed with
    equalities generated by [inversion]. *)

Definition eq' := @eq.

#[global]
Hint Unfold eq' : core.

Notation "x '='' y" := (@eq' _ x y)
  (at level 70, y at next level).


(* ################################################################# *)
(** * Check as a tactic instead of a top-level command, with possibility to turn off *)

(** [check E] is like [Check E], but works as a tactic.
    It can be turned off using [Ltac check_enabled ::= constr:(false)]. *)

Ltac check_enabled := constr:(true).

Tactic Notation "check" uconstr(E) :=
  lazymatch check_enabled with
  | false => idtac
  | true =>
	  first [ generalize E; match goal with |- ?T -> _ => idtac E; idtac ":" T end; intros _
	        | idtac E; fail 1 "does not typecheck" ]
 end.

(* ################################################################# *)
(** * Common Tactics for Simplifying Goals Like [intuition] *)

Ltac jauto_set_hyps :=
  repeat match goal with H: ?T |- _ =>
    match T with
    | _ /\ _ => destruct H
    | iff _ _ => destruct H
    | exists a, _ => destruct H
    | _ => generalize H; clear H
    end
  end.

Ltac jauto_set_goal :=
  repeat match goal with
  | |- exists a, _ => esplit
  | |- _ /\ _ => split
  | |- iff _ _ => split
  end.

Ltac jauto_set :=
  intros; jauto_set_hyps;
  intros; jauto_set_goal;
  unfold not in *.


(* ################################################################# *)
(** * Backward and Forward Chaining *)

(* ================================================================= *)
(** ** Application *)

Ltac old_refine f :=
  refine f. (* ; shelve_unifiable. *)

(** [rapply] is a tactic similar to [eapply] except that it is
    based on the [refine] tactics, and thus is strictly more
    powerful (at least in theory :). In short, it is able to perform
    on-the-fly conversions when required for arguments to match,
    and it is able to instantiate existentials when required. *)

Tactic Notation "rapply" constr(t) :=
  first  (* --Note: the @ are not useful *)
  [ eexact (@t)
  | old_refine (@t)
  | old_refine (@t _)
  | old_refine (@t _ _)
  | old_refine (@t _ _ _)
  | old_refine (@t _ _ _ _)
  | old_refine (@t _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  ].

(** No-typeclass refine apply, TEMPORARY for Coq < 8.11. *)

Ltac nrapply H :=
  first
  [ notypeclasses refine (H)
  | notypeclasses refine (H _)
  | notypeclasses refine (H _ _)
  | notypeclasses refine (H _ _ _)
  | notypeclasses refine (H _ _ _ _)
  | notypeclasses refine (H _ _ _ _ _)
  | notypeclasses refine (H _ _ _ _ _ _)
  | notypeclasses refine (H _ _ _ _ _ _ _)
  | notypeclasses refine (H _ _ _ _ _ _ _ _)
  | notypeclasses refine (H _ _ _ _ _ _ _ _ _)
  | notypeclasses refine (H _ _ _ _ _ _ _ _ _ _)
  | notypeclasses refine (H _ _ _ _ _ _ _ _ _ _ _)
  | notypeclasses refine (H _ _ _ _ _ _ _ _ _ _ _ _)
  | notypeclasses refine (H _ _ _ _ _ _ _ _ _ _ _ _ _)
  | notypeclasses refine (H _ _ _ _ _ _ _ _ _ _ _ _ _ _) ].

(** The tactics [applys_N T], where [N] is a natural number,
    provides a more efficient way of using [applys T]. It avoids
    trying out all possible arities, by specifying explicitely
    the arity of function [T]. *)

Tactic Notation "rapply_0" constr(t) :=
  old_refine (@t).
Tactic Notation "rapply_1" constr(t) :=
  old_refine (@t _).
Tactic Notation "rapply_2" constr(t) :=
  old_refine (@t _ _).
Tactic Notation "rapply_3" constr(t) :=
  old_refine (@t _ _ _).
Tactic Notation "rapply_4" constr(t) :=
  old_refine (@t _ _ _ _).
Tactic Notation "rapply_5" constr(t) :=
  old_refine (@t _ _ _ _ _).
Tactic Notation "rapply_6" constr(t) :=
  old_refine (@t _ _ _ _ _ _).
Tactic Notation "rapply_7" constr(t) :=
  old_refine (@t _ _ _ _ _ _ _).
Tactic Notation "rapply_8" constr(t) :=
  old_refine (@t _ _ _ _ _ _ _ _).
Tactic Notation "rapply_9" constr(t) :=
  old_refine (@t _ _ _ _ _ _ _ _ _).
Tactic Notation "rapply_10" constr(t) :=
  old_refine (@t _ _ _ _ _ _ _ _ _ _).

(** [lets_base H E] adds an hypothesis [H : T] to the context, where [T] is
    the type of term [E]. If [H] is an introduction pattern, it will
    destruct [H] according to the pattern. *)

Ltac lets_base I E := generalize E; intros I.

(** [applys_to H E] transform the type of hypothesis [H] by
    replacing it by the result of the application of the term
    [E] to [H]. Intuitively, it is equivalent to [lets H: (E H)]. *)

Tactic Notation "applys_to" hyp(H) constr(E) :=
  let H' := fresh "TEMP" in rename H into H';
  (first [ lets_base H (E H')
         | lets_base H (E _ H')
         | lets_base H (E _ _ H')
         | lets_base H (E _ _ _ H')
         | lets_base H (E _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ _ _ _ _ H') ]
  ); clear H'.

(** [applys_to H1,...,HN E] applys [E] to several hypotheses *)

Tactic Notation "applys_to" hyp(H1) "," hyp(H2) constr(E) :=
  applys_to H1 E; applys_to H2 E.
Tactic Notation "applys_to" hyp(H1) "," hyp(H2) "," hyp(H3) constr(E) :=
  applys_to H1 E; applys_to H2 E; applys_to H3 E.
Tactic Notation "applys_to" hyp(H1) "," hyp(H2) "," hyp(H3) "," hyp(H4) constr(E) :=
  applys_to H1 E; applys_to H2 E; applys_to H3 E; applys_to H4 E.

(** [constructors] calls [constructor] or [econstructor]. *)

Tactic Notation "constructors" :=
  first [ constructor | econstructor ]; unfold eq'.

(* ================================================================= *)
(** ** Assertions *)

(** [asserts H: T] is another syntax for [assert (H : T)], which
    also works with introduction patterns. *)

Tactic Notation "asserts" simple_intropattern(I) ":" constr(T) :=
  let H := fresh "TEMP" in assert (H : T);
  [ | generalize H; clear H; intros I ].

(** [asserts H1 .. HN: T] is a shorthand for
    [asserts \[H1 \[H2 \[.. HN\]\]\]\]: T]. *)

Tactic Notation "asserts" simple_intropattern(I1)
 simple_intropattern(I2) ":" constr(T) :=
  asserts [I1 I2]: T.
Tactic Notation "asserts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) ":" constr(T) :=
  asserts [I1 [I2 I3]]: T.
Tactic Notation "asserts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3)
 simple_intropattern(I4) ":" constr(T) :=
  asserts [I1 [I2 [I3 I4]]]: T.
Tactic Notation "asserts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3)
 simple_intropattern(I4) simple_intropattern(I5) ":" constr(T) :=
  asserts [I1 [I2 [I3 [I4 I5]]]]: T.
Tactic Notation "asserts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3)
 simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) ":" constr(T) :=
  asserts [I1 [I2 [I3 [I4 [I5 I6]]]]]: T.

(** [asserts: T] is [asserts H: T] with [H] being chosen automatically. *)

Tactic Notation "asserts" ":" constr(T) :=
  let H := fresh "TEMP" in asserts H : T.

(** [cuts H: T] is the same as [asserts H: T] except that the two subgoals
    generated are swapped: the subgoal [T] comes second. Note that contrary
    to [cut], it introduces the hypothesis. *)

Tactic Notation "cuts" simple_intropattern(I) ":" constr(T) :=
  cut (T); [ intros I | idtac ].

(** [cuts: T] is [cuts H: T] with [H] being chosen automatically. *)

Tactic Notation "cuts" ":" constr(T) :=
  let H := fresh "TEMP" in cuts H: T.

(** [cuts H1 .. HN: T] is a shorthand for
    [cuts \[H1 \[H2 \[.. HN\]\]\]\]: T]. *)

Tactic Notation "cuts" simple_intropattern(I1)
 simple_intropattern(I2) ":" constr(T) :=
  cuts [I1 I2]: T.
Tactic Notation "cuts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) ":" constr(T) :=
  cuts [I1 [I2 I3]]: T.
Tactic Notation "cuts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3)
 simple_intropattern(I4) ":" constr(T) :=
  cuts [I1 [I2 [I3 I4]]]: T.
Tactic Notation "cuts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3)
 simple_intropattern(I4) simple_intropattern(I5) ":" constr(T) :=
  cuts [I1 [I2 [I3 [I4 I5]]]]: T.
Tactic Notation "cuts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3)
 simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) ":" constr(T) :=
  cuts [I1 [I2 [I3 [I4 [I5 I6]]]]]: T.

(* ================================================================= *)
(** ** Instantiation and Forward-Chaining *)

(** The instantiation tactics are used to instantiate a lemma [E]
    (whose type is a product) on some arguments. The type of [E] is
    made of implications and universal quantifications, e.g.
    [forall x, P x -> forall y z, Q x y z -> R z].

    The first possibility is to provide arguments in order: first [x],
    then a proof of [P x], then [y] etc... In this mode, called "Args",
    all the arguments are to be provided. If a wildcard is provided
    (written [__]), then an existential variable will be introduced in
    place of the argument.

    It is very convenient to give some arguments the lemma should be
    instantiated on, and let the tactic find out automatically where
    underscores should be insterted. Underscore arguments [__] are
    interpret as follows: an underscore means that we want to skip the
    argument that has the same type as the next real argument provided
    (real means not an underscore). If there is no real argument after
    underscore, then the underscore is used for the first possible argument.

    The general syntax is [tactic (>> E1 .. EN)] where [tactic] is
    the name of the tactic (possibly with some arguments) and [Ei]
    are the arguments. Moreover, some tactics accept the syntax
    [tactic E1 .. EN] as short for [tactic (>> E1 .. EN)] for
    values of [N] up to 5.

    Finally, if the argument [EN] given is a triple-underscore [___],
    then it is equivalent to providing a list of wildcards, with
    the appropriate number of wildcards. This means that all
    the remaining arguments of the lemma will be instantiated.
    Definitions in the conclusion are not unfolded in this case. *)

(* Underlying implementation *)

Ltac app_assert t P cont :=
  let H := fresh "TEMP" in
  assert (H : P); [ | cont(t H); clear H ].

Ltac app_evar t A cont :=
  let x := fresh "TEMP" in
  evar (x:A);
  let t' := constr:(t x) in
  let t'' := (eval unfold x in t') in
  subst x; cont t''.

Ltac app_arg t P v cont :=
  let H := fresh "TEMP" in
  assert (H : P); [ apply v | cont(t H); try clear H ].

Ltac build_app_alls t final :=
  let rec go t :=
    match type of t with
    | ?P -> ?Q => app_assert t P go
    | forall _:?A, _ => app_evar t A go
    | _ => final t
    end in
  go t.

Ltac boxerlist_next_type vs :=
  match vs with
  | nil => constr:(ltac_wild)
  | (boxer ltac_wild)::?vs' => boxerlist_next_type vs'
  | (boxer ltac_wilds)::_ => constr:(ltac_wild)
  | (@boxer ?T _)::_ => constr:(T)
  end.

(* Note: refuse to instantiate a dependent hypothesis with a proposition;
    refuse to instantiate an argument of type Type with one that
    does not have the type Type.
*)

Ltac build_app_hnts t vs final :=
  let rec go t vs :=
    match vs with
    | nil => first [ final t | fail 1 ]
    | (boxer ltac_wilds)::_ => first [ build_app_alls t final | fail 1 ]
    | (boxer ?v)::?vs' =>
      let cont t' := go t' vs in
      let cont' t' := go t' vs' in
      let T := type of t in
      let T := eval hnf in T in
      match v with
      | ltac_wild =>
         first [ let U := boxerlist_next_type vs' in
           match U with
           | ltac_wild =>
             match T with
             | ?P -> ?Q => first [ app_assert t P cont' | fail 3 ]
             | forall _:?A, _ => first [ app_evar t A cont' | fail 3 ]
             end
           | _ =>
             match T with  (* should test T for unifiability *)
             | U -> ?Q => first [ app_assert t U cont' | fail 3 ]
             | forall _:U, _ => first [ app_evar t U cont' | fail 3 ]
             | ?P -> ?Q => first [ app_assert t P cont | fail 3 ]
             | forall _:?A, _ => first [ app_evar t A cont | fail 3 ]
             end
           end
         | fail 2 ]
      | _ =>
          match T with
          | ?P -> ?Q => first [ app_arg t P v cont'
                              | app_assert t P cont
                              | fail 3 ]
           | forall _:Type, _ =>
              match type of v with
              | Type => first [ cont' (t v)
                              | app_evar t Type cont
                              | fail 3 ]
              | _ => first [ app_evar t Type cont
                           | fail 3 ]
              end
          | forall _:?A, _ =>
             let V := type of v in
             match type of V with
             | Prop =>  first [ app_evar t A cont
                              | fail 3 ]
             | _ => first [ cont' (t v)
                          | app_evar t A cont
                          | fail 3 ]
             end
          end
      end
    end in
  go t vs.

(** newer version : support for typeclasses *)

Ltac app_typeclass t cont :=
  let t' := constr:(t _) in
  cont t'.

Ltac build_app_alls t final ::=
  let rec go t :=
    match type of t with
    | ?P -> ?Q => app_assert t P go
    | forall _:?A, _ =>
        first [ app_evar t A go
              | app_typeclass t go
              | fail 3 ]
    | _ => final t
    end in
  go t.

Ltac build_app_hnts t vs final ::=
  let rec go t vs :=
    match vs with
    | nil => first [ final t | fail 1 ]
    | (boxer ltac_wilds)::_ => first [ build_app_alls t final | fail 1 ]
    | (boxer ?v)::?vs' =>
      let cont t' := go t' vs in
      let cont' t' := go t' vs' in
      let T := type of t in
      let T := eval hnf in T in
      match v with
      | ltac_wild =>
         first [ let U := boxerlist_next_type vs' in
           match U with
           | ltac_wild =>
             match T with
             | ?P -> ?Q => first [ app_assert t P cont' | fail 3 ]
             | forall _:?A, _ => first [ app_typeclass t cont'
                                       | app_evar t A cont'
                                       | fail 3 ]
             end
           | _ =>
             match T with  (* should test T for unifiability *)
             | U -> ?Q => first [ app_assert t U cont' | fail 3 ]
             | forall _:U, _ => first
                 [ app_typeclass t cont'
                 | app_evar t U cont'
                 | fail 3 ]
             | ?P -> ?Q => first [ app_assert t P cont | fail 3 ]
             | forall _:?A, _ => first
                 [ app_typeclass t cont
                 | app_evar t A cont
                 | fail 3 ]
             end
           end
         | fail 2 ]
      | _ =>
          match T with
          | ?P -> ?Q => first [ app_arg t P v cont'
                              | app_assert t P cont
                              | fail 3 ]
           | forall _:Type, _ =>
              match type of v with
              | Type => first [ cont' (t v)
                              | app_evar t Type cont
                              | fail 3 ]
              | _ => first [ app_evar t Type cont
                           | fail 3 ]
              end
          | forall _:?A, _ =>
             let V := type of v in
             match type of V with
             | Prop => first [ app_typeclass t cont
                              | app_evar t A cont
                              | fail 3 ]
             | _ => first [ cont' (t v)
                          | app_typeclass t cont
                          | app_evar t A cont
                          | fail 3 ]
             end
          end
      end
    end in
  go t vs.
  (* --Note: use local function for first [...] *)

Ltac build_app args final :=
  first [
    match args with (@boxer ?T ?t)::?vs =>
      let t := constr:(t:T) in
      build_app_hnts t vs final;
      fast_rm_inside args
    end
  | fail 1 "Instantiation fails for:" args].

Ltac unfold_head_until_product T :=
  eval hnf in T.

Ltac args_unfold_head_if_not_product args :=
  match args with (@boxer ?T ?t)::?vs =>
    let T' := unfold_head_until_product T in
    constr:((@boxer T' t)::vs)
  end.

Ltac args_unfold_head_if_not_product_but_params args :=
  match args with
  | (boxer ?t)::(boxer ?v)::?vs =>
     args_unfold_head_if_not_product args
  | _ => constr:(args)
  end.

(** [lets H: (>> E0 E1 .. EN)] will instantiate lemma [E0]
    on the arguments [Ei] (which may be wildcards [__]),
    and name [H] the resulting term. [H] may be an introduction
    pattern, or a sequence of introduction patterns [I1 I2 IN],
    or empty.
    Syntax [lets H: E0 E1 .. EN] is also available. If the last
    argument [EN] is [___] (triple-underscore), then all
    arguments of [H] will be instantiated. *)

Ltac lets_build I Ei :=
  let args := list_boxer_of Ei in
  let args := args_unfold_head_if_not_product_but_params args in
(*    let Ei''' := args_unfold_head_if_not_product Ei'' in*)
  build_app args ltac:(fun R => lets_base I R).

Tactic Notation "lets" simple_intropattern(I) ":" constr(E) :=
  lets_build I E.
Tactic Notation "lets" ":" constr(E) :=
  let H := fresh in lets H: E.
Tactic Notation "lets" ":" constr(E0)
 constr(A1) :=
  lets: (>> E0 A1).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) :=
  lets: (>> E0 A1 A2).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets: (>> E0 A1 A2 A3).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets: (>> E0 A1 A2 A3 A4).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets: (>> E0 A1 A2 A3 A4 A5).

(* DEPRECATED syntax [lets I1 I2] *)
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 ":" constr(E) :=
  lets [I1 I2]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) ":" constr(E) :=
  lets [I1 [I2 I3]]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) ":" constr(E) :=
  lets [I1 [I2 [I3 I4]]]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 ":" constr(E) :=
  lets [I1 [I2 [I3 [I4 I5]]]]: E.

Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  lets I: (>> E0 A1).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  lets I: (>> E0 A1 A2).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets I: (>> E0 A1 A2 A3).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets I: (>> E0 A1 A2 A3 A4).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets I: (>> E0 A1 A2 A3 A4 A5).

Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) :=
  lets [I1 I2]: E0 A1.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) :=
  lets [I1 I2]: E0 A1 A2.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets [I1 I2]: E0 A1 A2 A3.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets [I1 I2]: E0 A1 A2 A3 A4.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets [I1 I2]: E0 A1 A2 A3 A4 A5.

(** [forwards H: (>> E0 E1 .. EN)] is short for
    [forwards H: (>> E0 E1 .. EN ___)].
    The arguments [Ei] can be wildcards [__] (except [E0]).
    [H] may be an introduction pattern, or a sequence of
    introduction pattern, or empty.
    Syntax [forwards H: E0 E1 .. EN] is also available. *)

Ltac forwards_build_app_arg Ei :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  let args := args_unfold_head_if_not_product args in
  args.

Ltac forwards_then Ei cont :=
  let args := forwards_build_app_arg Ei in
  let args := args_unfold_head_if_not_product_but_params args in
  build_app args cont.

Tactic Notation "forwards" simple_intropattern(I) ":" constr(Ei) :=
  let args := forwards_build_app_arg Ei in
  lets I: args.

Tactic Notation "forwards" ":" constr(E) :=
  let H := fresh in forwards H: E.
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) :=
  forwards: (>> E0 A1).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards: (>> E0 A1 A2).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards: (>> E0 A1 A2 A3).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards: (>> E0 A1 A2 A3 A4).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards: (>> E0 A1 A2 A3 A4 A5).

(* --DEPRECATED syntax *)
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 ":" constr(E) :=
  forwards [I1 I2]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) ":" constr(E) :=
  forwards [I1 [I2 I3]]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) ":" constr(E) :=
  forwards [I1 [I2 [I3 I4]]]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 ":" constr(E) :=
  forwards [I1 [I2 [I3 [I4 I5]]]]: E.

Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  forwards I: (>> E0 A1).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards I: (>> E0 A1 A2).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards I: (>> E0 A1 A2 A3).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards I: (>> E0 A1 A2 A3 A4).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards I: (>> E0 A1 A2 A3 A4 A5).

(** [forwards_nounfold I: E] is like [forwards I: E] but does not
    unfold the head constant of [E] if there is no visible quantification
    or hypothesis in [E]. It is meant to be used mainly by tactics. *)

Tactic Notation "forwards_nounfold" simple_intropattern(I) ":" constr(Ei) :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  build_app args ltac:(fun R => lets_base I R).

(** [forwards_nounfold_then E ltac:(fun K => ..)]
    is like [forwards: E] but it provides the resulting term
    to a continuation, under the name [K]. *)

Ltac forwards_nounfold_then Ei cont :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  build_app args cont.

(** [applys (>> E0 E1 .. EN)] instantiates lemma [E0]
    on the arguments [Ei] (which may be wildcards [__]),
    and apply the resulting term to the current goal,
    using the tactic [applys] defined earlier on.
    [applys E0 E1 E2 .. EN] is also available. *)

Ltac applys_build Ei :=
  let args := list_boxer_of Ei in
  let args := args_unfold_head_if_not_product_but_params args in
  build_app args ltac:(fun R =>
   first [ apply R | eapply R | rapply R ]).

Ltac applys_base E :=
  match type of E with
  | list Boxer => applys_build E
  | _ => first [ rapply E | applys_build E ]
  end; fast_rm_inside E.

Tactic Notation "applys" constr(E) :=
  applys_base E.
Tactic Notation "applys" constr(E0) constr(A1) :=
  applys (>> E0 A1).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) :=
  applys (>> E0 A1 A2).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) :=
  applys (>> E0 A1 A2 A3).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
  applys (>> E0 A1 A2 A3 A4).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  applys (>> E0 A1 A2 A3 A4 A5).

(** [fapplys (>> E0 E1 .. EN)] instantiates lemma [E0]
    on the arguments [Ei] and on the argument [___] meaning
    that all evars should be explicitly instantiated,
    and apply the resulting term to the current goal.
    [fapplys E0 E1 E2 .. EN] is also available. *)

Ltac fapplys_build Ei :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  let args := args_unfold_head_if_not_product_but_params args in
  build_app args ltac:(fun R => apply R).

Tactic Notation "fapplys" constr(E0) :=
  match type of E0 with
  | list Boxer => fapplys_build E0
  | _ => fapplys_build (>> E0)
  end.
Tactic Notation "fapplys" constr(E0) constr(A1) :=
  fapplys (>> E0 A1).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) :=
  fapplys (>> E0 A1 A2).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) constr(A3) :=
  fapplys (>> E0 A1 A2 A3).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
  fapplys (>> E0 A1 A2 A3 A4).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  fapplys (>> E0 A1 A2 A3 A4 A5).

(** [specializes H (>> E1 E2 .. EN)] will instantiate hypothesis [H]
    on the arguments [Ei] (which may be wildcards [__]). If the last
    argument [EN] is [___] (triple-underscore), then all arguments of
    [H] get instantiated. *)

Ltac specializes_build H Ei :=
  let H' := fresh "TEMP" in rename H into H';
  let args := list_boxer_of Ei in
  let args := constr:((boxer H')::args) in
  let args := args_unfold_head_if_not_product args in
  build_app args ltac:(fun R => lets H: R);
  clear H'.

Ltac specializes_base H Ei :=
  specializes_build H Ei; fast_rm_inside Ei.

Tactic Notation "specializes" hyp(H) :=
  specializes_base H (___).
Tactic Notation "specializes" hyp(H) constr(A) :=
  specializes_base H A.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) :=
  specializes H (>> A1 A2).
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) :=
  specializes H (>> A1 A2 A3).
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) :=
  specializes H (>> A1 A2 A3 A4).
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  specializes H (>> A1 A2 A3 A4 A5).

(** [specializes_vars H] is equivalent to [specializes H __ .. __]
    with as many double underscore as the number of dependent arguments
    visible from the type of [H]. Note that no unfolding is currently
    being performed (this behavior might change in the future).
    The current implementation is restricted to the case where
    [H] is an existing hypothesis -- Note: this could be generalized. *)

Ltac specializes_var_base H :=
  match type of H with
  | ?P -> ?Q => fail 1
  | forall _:_, _ => specializes H __
  end.

Ltac specializes_vars_base H :=
  repeat (specializes_var_base H).

Tactic Notation "specializes_var" hyp(H) :=
  specializes_var_base H.

Tactic Notation "specializes_vars" hyp(H) :=
  specializes_vars_base H.

(* ================================================================= *)
(** ** Experimental Tactics for Application *)

(** [fapply] is a version of [apply] based on [forwards]. *)

Tactic Notation "fapply" constr(E) :=
  let H := fresh "TEMP" in forwards H: E;
  first [ apply H | eapply H | rapply H | hnf; apply H
        | hnf; eapply H | applys H ].
   (* Note: is applys redundant with rapply ? *)

(** [sapply] stands for "super apply". It tries
    [apply], [eapply], [applys] and [fapply],
    and also tries to head-normalize the goal first. *)

Tactic Notation "sapply" constr(H) :=
  first [ apply H | eapply H | rapply H | applys H
        | hnf; apply H | hnf; eapply H | hnf; applys H
        | fapply H ].

(* ================================================================= *)
(** ** Adding Assumptions *)

(** [lets_simpl H: E] is the same as [lets H: E] excepts that it
    calls [simpl] on the hypothesis H.
    [lets_simpl: E] is also provided. *)

Tactic Notation "lets_simpl" ident(H) ":" constr(E) :=
  lets H: E; try simpl in H.

Tactic Notation "lets_simpl" ":" constr(T) :=
  let H := fresh "TEMP" in lets_simpl H: T.

(** [lets_hnf H: E] is the same as [lets H: E] excepts that it
    calls [hnf] to set the definition in head normal form.
    [lets_hnf: E] is also provided. *)

Tactic Notation "lets_hnf" ident(H) ":" constr(E) :=
  lets H: E; hnf in H.

Tactic Notation "lets_hnf" ":" constr(T) :=
  let H := fresh "TEMP" in lets_hnf H: T.

(** [puts X: E] is a synonymous for [pose (X := E)].
    Alternative syntax is [puts: E]. *)

Tactic Notation "puts" ident(X) ":" constr(E) :=
  pose (X := E).
Tactic Notation "puts" ":" constr(E) :=
  let X := fresh "X" in pose (X := E).

(* ================================================================= *)
(** ** Application of Tautologies *)

(** [logic E], where [E] is a fact, is equivalent to
    [assert H:E; [tauto | eapply H; clear H]]. It is useful for instance
    to prove a conjunction [A /\ B] by showing first [A] and then [A -> B],
    through the command [logic (foral A B, A -> (A -> B) -> A /\ B)] *)

Ltac logic_base E cont :=
  assert (H:E); [ cont tt | eapply H; clear H ].

Tactic Notation "logic" constr(E) :=
  logic_base E ltac:(fun _ => tauto).

(* ================================================================= *)
(** ** Application Modulo Equalities *)

(** The tactic [equates] replaces a goal of the form
    [P x y z] with a goal of the form [P x ?a z] and a
    subgoal [?a = y]. The introduction of the evar [?a] makes
    it possible to apply lemmas that would not apply to the
    original goal, for example a lemma of the form
    [forall n m, P n n m], because [x] and [y] might be equal
    but not convertible.

    Usage is [equates i1 ... ik], where the indices are the
    positions of the arguments to be replaced by evars,
    counting from the right-hand side. If [0] is given as
    argument, then the entire goal is replaced by an evar. *)

Section equatesLemma.
Variables (A0 A1 : Type).
Variables (A2 : forall (x1 : A1), Type).
Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).
Variables (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).
Variables (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type).
Variables (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

Lemma equates_0 : forall (P Q:Prop),
  P -> P = Q -> Q.
Proof using. intros. subst. auto. Qed.

Lemma equates_1 :
  forall (P:A0->Prop) x1 y1,
  P y1 -> x1 = y1 -> P x1.
Proof using. intros. subst. auto. Qed.

Lemma equates_2 :
  forall y1 (P:A0->forall(x1:A1),Prop) x1 x2,
  P y1 x2 -> x1 = y1 -> P x1 x2.
Proof using. intros. subst. auto. Qed.

Lemma equates_3 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1),Prop) x1 x2 x3,
  P y1 x2 x3 -> x1 = y1 -> P x1 x2 x3.
Proof using. intros. subst. auto. Qed.

Lemma equates_4 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2),Prop) x1 x2 x3 x4,
  P y1 x2 x3 x4 -> x1 = y1 -> P x1 x2 x3 x4.
Proof using. intros. subst. auto. Qed.

Lemma equates_5 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3),Prop) x1 x2 x3 x4 x5,
  P y1 x2 x3 x4 x5 -> x1 = y1 -> P x1 x2 x3 x4 x5.
Proof using. intros. subst. auto. Qed.

Lemma equates_6 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3)(x5:A5 x4),Prop)
  x1 x2 x3 x4 x5 x6,
  P y1 x2 x3 x4 x5 x6 -> x1 = y1 -> P x1 x2 x3 x4 x5 x6.
Proof using. intros. subst. auto. Qed.

End equatesLemma.

Ltac equates_lemma n :=
  match number_to_nat n with
  | 0 => constr:(equates_0)
  | 1 => constr:(equates_1)
  | 2 => constr:(equates_2)
  | 3 => constr:(equates_3)
  | 4 => constr:(equates_4)
  | 5 => constr:(equates_5)
  | 6 => constr:(equates_6)
  | _ => fail 100 "equates tactic only support up to arity 6"
  end.

Ltac equates_one n :=
  let L := equates_lemma n in
  eapply L.

Ltac equates_several E cont :=
  let all_pos := match type of E with
    | List.list Boxer => constr:(E)
    | _ => constr:((boxer E)::nil)
    end in
  let rec go pos :=
     match pos with
     | nil => cont tt
     | (boxer ?n)::?pos' => equates_one n; [ go pos' | ]
     end in
  go all_pos.

Tactic Notation "equates" constr(E) :=
  equates_several E ltac:(fun _ => idtac).
Tactic Notation "equates" constr(n1) constr(n2) :=
  equates (>> n1 n2).
Tactic Notation "equates" constr(n1) constr(n2) constr(n3) :=
  equates (>> n1 n2 n3).
Tactic Notation "equates" constr(n1) constr(n2) constr(n3) constr(n4) :=
  equates (>> n1 n2 n3 n4).

(** [applys_eq H i1 .. iK] is the same as
    [equates i1 .. iK] followed by [applys H]
    on the first subgoal.

    DEPRECATED: use [applys_eq H] instead. *)

Tactic Notation "applys_eq" constr(H) constr(E) :=
  equates_several E ltac:(fun _ => sapply H).
Tactic Notation "applys_eq" constr(H) constr(n1) constr(n2) :=
  applys_eq H (>> n1 n2).
Tactic Notation "applys_eq" constr(H) constr(n1) constr(n2) constr(n3) :=
  applys_eq H (>> n1 n2 n3).
Tactic Notation "applys_eq" constr(H) constr(n1) constr(n2) constr(n3) constr(n4) :=
  applys_eq H (>> n1 n2 n3 n4).

(** [applys_eq H] helps proving a goal of the form [P x1 .. xN]
    from an hypothesis [H] that concludes [P y1 .. yN], where the
    arguments [xi] and [yi] may or may not be convertible.
    Equalities are produced for all arguments that don't unify.

    The tactic invokes [equates] on all arguments, then calls
    [applys K], and attempts [reflexivity] on the side equalities. *)

Lemma applys_eq_init : forall (P Q:Prop),
  P = Q ->
  Q ->
  P.
Proof using. intros. subst. auto. Qed.

Lemma applys_eq_step_dep : forall B (P Q: (forall A, A->B)) (T:Type),
  P = Q ->
  P T = Q T.
Proof using. intros. subst. auto. Qed.

Lemma applys_eq_step : forall A B (P Q:A->B) x y,
  P = Q ->
  x = y ->
  P x = Q y.
Proof using. intros. subst. auto. Qed.

Ltac applys_eq_loop tt :=
  match goal with
  | |- ?P ?x =>
      first [ eapply applys_eq_step; [ applys_eq_loop tt | ]
            | eapply applys_eq_step_dep; applys_eq_loop tt ]
  | _ => reflexivity
  end.

Ltac applys_eq_core H :=
  eapply applys_eq_init;
  [ applys_eq_loop tt | applys H ];
  try reflexivity.

Tactic Notation "applys_eq" constr(H) :=
  applys_eq_core H.

(* ================================================================= *)
(** ** Absurd Goals *)

(** [false_goal] replaces any goal by the goal [False].
    Contrary to the tactic [false] (below), it does not try to do
    anything else *)

Tactic Notation "false_goal" :=
  exfalso.

(** [false_post] is the underlying tactic used to prove goals
    of the form [False]. In the default implementation, it proves
    the goal if the context contains [False] or an hypothesis of the
    form [C x1 .. xN  =  D y1 .. yM], or if the [congruence] tactic
    finds a proof of [x <> x] for some [x]. *)

Ltac false_post :=
  solve [ assumption | discriminate | congruence ].

(** [false] replaces any goal by the goal [False], and calls [false_post] *)

Tactic Notation "false" :=
  false_goal; try false_post.

(** [tryfalse] tries to solve a goal by contradiction, and leaves
    the goal unchanged if it cannot solve it.
    It is equivalent to [try solve \[ false \]]. *)

Tactic Notation "tryfalse" :=
  try solve [ false ].

(** [false E] tries to exploit lemma [E] to prove the goal false.
    [false E1 .. EN] is equivalent to [false (>> E1 .. EN)],
    which tries to apply [applys (>> E1 .. EN)] and if it
    does not work then tries [forwards H: (>> E1 .. EN)]
    followed with [false] *)

Ltac false_then E cont :=
  false_goal; first
  [ applys E
  | forwards_then E ltac:(fun M =>
      pose M; jauto_set_hyps; intros; false) ];
  cont tt.
  (* Note: is [cont] needed? *)

Tactic Notation "false" constr(E) :=
  false_then E ltac:(fun _ => idtac).
Tactic Notation "false" constr(E) constr(E1) :=
  false (>> E E1).
Tactic Notation "false" constr(E) constr(E1) constr(E2) :=
  false (>> E E1 E2).
Tactic Notation "false" constr(E) constr(E1) constr(E2) constr(E3) :=
  false (>> E E1 E2 E3).
Tactic Notation "false" constr(E) constr(E1) constr(E2) constr(E3) constr(E4) :=
  false (>> E E1 E2 E3 E4).

(** [false_invert H] proves a goal if it absurd after
    calling [inversion H] and [false] *)

Ltac false_invert_for H :=
  let M := fresh "TEMP" in pose (M := H); inversion H; false.

Tactic Notation "false_invert" constr(H) :=
  try solve [ false_invert_for H | false ].

(** [false_invert] proves any goal provided there is at least
    one hypothesis [H] in the context (or as a universally quantified
    hypothesis visible at the head of the goal) that can be proved absurd by calling
    [inversion H]. *)

Ltac false_invert_iter :=
  match goal with H:_ |- _ =>
    solve [ inversion H; false
          | clear H; false_invert_iter
          | fail 2 ] end.

Tactic Notation "false_invert" :=
  intros; solve [ false_invert_iter | false ].

(** [tryfalse_invert H] and [tryfalse_invert] are like the
    above but leave the goal unchanged if they don't solve it. *)

Tactic Notation "tryfalse_invert" constr(H) :=
  try (false_invert H).

Tactic Notation "tryfalse_invert" :=
  try false_invert.

(** [false_neq_self_hyp] proves any goal if the context
    contains an hypothesis of the form [E <> E]. It is
    a restricted and optimized version of [false]. It is
    intended to be used by other tactics only. *)

Ltac false_neq_self_hyp :=
  match goal with H: ?x <> ?x |- _ =>
    false_goal; apply H; reflexivity end.


(* ################################################################# *)
(** * Introduction and Generalization *)

(* ================================================================= *)
(** ** Introduction *)

(** [introv] is used to name only non-dependent hypothesis.
 - If [introv] is called on a goal of the form [forall x, H],
   it should introduce all the variables quantified with a
   [forall] at the head of the goal, but it does not introduce
   hypotheses that preceed an arrow constructor, like in [P -> Q].
 - If [introv] is called on a goal that is not of the form
   [forall x, H] nor [P -> Q], the tactic unfolds definitions
   until the goal takes the form [forall x, H] or [P -> Q].
   If unfolding definitions does not produces a goal of this form,
   then the tactic [introv] does nothing at all. *)

(* [introv_rec] introduces all visible variables.
   It does not try to unfold any definition. *)

Ltac introv_rec :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => intro; introv_rec
  | |- _ => idtac
  end.

(* [introv_noarg] forces the goal to be a [forall] or an [->],
   and then calls [introv_rec] to introduces variables
   (possibly none, in which case [introv] is the same as [hnf]).
   If the goal is not a product, then it does not do anything. *)

Ltac introv_noarg :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => introv_rec
  | |- ?G => hnf;
     match goal with
     | |- ?P -> ?Q => idtac
     | |- forall _, _ => introv_rec
     end
  | |- _ => idtac
  end.

  (* simpler yet perhaps less efficient imlementation *)
  Ltac introv_noarg_not_optimized :=
    intro; match goal with H:_|-_ => revert H end; introv_rec.

(* [introv_arg H] introduces one non-dependent hypothesis
   under the name [H], after introducing the variables
   quantified with a [forall] that preceeds this hypothesis.
   This tactic fails if there does not exist a hypothesis
   to be introduced. *)
(* Note: __ in introv means "intros" *)

Ltac introv_arg H :=
  hnf; match goal with
  | |- ?P -> ?Q => intros H
  | |- forall _, _ => intro; introv_arg H
  end.

(* [introv I1 .. IN] iterates [introv Ik] *)

Tactic Notation "introv" :=
  introv_noarg.
Tactic Notation "introv" simple_intropattern(I1) :=
  introv_arg I1.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) :=
  introv I1; introv I2.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) :=
  introv I1; introv I2 I3.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) :=
  introv I1; introv I2 I3 I4.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  introv I1; introv I2 I3 I4 I5.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  introv I1; introv I2 I3 I4 I5 I6.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  introv I1; introv I2 I3 I4 I5 I6 I7.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9 I10.

(** [intros_all] repeats [intro] as long as possible. Contrary to [intros],
    it unfolds any definition on the way. Remark that it also unfolds the
    definition of negation, so applying [intros_all] to a goal of the form
    [forall x, P x -> ~Q] will introduce [x] and [P x] and [Q], and will
    leave [False] in the goal. *)

Tactic Notation "intros_all" :=
  repeat intro.

(** [intros_hnf] introduces an hypothesis and sets in head normal form *)

Tactic Notation "intro_hnf" :=
  intro; match goal with H: _ |- _ => hnf in H end.

(* ================================================================= *)
(** ** Introduction using [=>] and [=>>] *)

(* [=> I1 .. IN] is the same as [intros I1 .. IN] *)

Ltac ltac_intros_post := idtac.

Tactic Notation "=>" :=
  intros.
Tactic Notation "=>" simple_intropattern(I1) :=
  intros I1.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2) :=
  intros I1 I2.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) :=
  intros I1 I2 I3.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) :=
  intros I1 I2 I3 I4.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  intros I1 I2 I3 I4 I5.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  intros I1 I2 I3 I4 I5 I6.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  intros I1 I2 I3 I4 I5 I6 I7.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  intros I1 I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.

(* [=>>] first introduces all non-dependent variables,
   then behaves as [intros]. It unfolds the head of the goal using [hnf]
   if there are not head visible quantifiers.

   Remark: instances of [Inhab] are treated as non-dependent and
   are introduced automatically. *)

(* NOTE: this tactic is later redefined for supporting Inhab *)
Ltac intro_nondeps_aux_special_intro G :=
  fail.

Ltac intro_nondeps_aux is_already_hnf :=
  match goal with
  | |- (?P -> ?Q) => idtac
  | |- ?G -> _ => intro_nondeps_aux_special_intro G;
                  intro; intro_nondeps_aux true
  | |- (forall _,_) => intros ?; intro_nondeps_aux true
  | |- _ =>
     match is_already_hnf with
     | true => idtac
     | false => hnf; intro_nondeps_aux true
     end
  end.

Ltac intro_nondeps tt := intro_nondeps_aux false.

Tactic Notation "=>>" :=
  intro_nondeps tt.
Tactic Notation "=>>" simple_intropattern(I1) :=
  =>>; intros I1.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2) :=
  =>>; intros I1 I2.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) :=
  =>>; intros I1 I2 I3.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) :=
  =>>; intros I1 I2 I3 I4.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  =>>; intros I1 I2 I3 I4 I5.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  =>>; intros I1 I2 I3 I4 I5 I6.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  =>>; intros I1 I2 I3 I4 I5 I6 I7.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  =>>; intros I1 I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  =>>; intros I1 I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  =>>; intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.

(* ================================================================= *)
(** ** Generalization *)

(** [gen X1 .. XN] is a shorthand for calling [generalize dependent]
    successively on variables [XN]...[X1]. Note that the variables
    are generalized in reverse order, following the convention of
    the [generalize] tactic: it means that [X1] will be the first
    quantified variable in the resulting goal. *)

Tactic Notation "gen" ident(X1) :=
  generalize dependent X1.
Tactic Notation "gen" ident(X1) ident(X2) :=
  gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) :=
  gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4)  :=
  gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) :=
  gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) :=
  gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) ident(X7) :=
  gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) ident(X7) ident(X8) :=
  gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) ident(X7) ident(X8) ident(X9) :=
  gen X9; gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) ident(X7) ident(X8) ident(X9) ident(X10) :=
  gen X10; gen X9; gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.

(** [generalizes X] is a shorthand for calling [generalize X; clear X].
    It is weaker than tactic [gen X] since it does not support
    dependencies. It is mainly intended for writing tactics. *)

Tactic Notation "generalizes" hyp(X) :=
  generalize X; clear X.
Tactic Notation "generalizes" hyp(X1) hyp(X2) :=
  generalizes X1; generalizes X2.
Tactic Notation "generalizes" hyp(X1) hyp(X2) hyp(X3) :=
  generalizes X1 X2; generalizes X3.
Tactic Notation "generalizes" hyp(X1) hyp(X2) hyp(X3) hyp(X4) :=
  generalizes X1 X2 X3; generalizes X4.

(* ================================================================= *)
(** ** Naming *)

(** [sets X: E] is the same as [set (X := E) in *], that is,
    it replaces all occurences of [E] by a fresh meta-variable [X]
    whose definition is [E]. *)

Tactic Notation "sets" ident(X) ":" constr(E) :=
  set (X := E) in *.

(** [def_to_eq E X H] applies when [X := E] is a local
    definition. It adds an assumption [H: X = E]
    and then clears the definition of [X].
    [def_to_eq_sym] is similar except that it generates
    the equality [H: E = X]. *)

Ltac def_to_eq X HX E :=
  assert (HX : X = E) by reflexivity; clearbody X.
Ltac def_to_eq_sym X HX E :=
  assert (HX : E = X) by reflexivity; clearbody X.

(** [set_eq X H: E] generates the equality [H: X = E],
    for a fresh name [X], and replaces [E] by [X] in the
    current goal. Syntaxes [set_eq X: E] and
    [set_eq: E] are also available. Similarly,
    [set_eq <- X H: E] generates the equality [H: E = X].

    [sets_eq X HX: E] does the same but replaces [E] by [X]
    everywhere in the goal. [sets_eq X HX: E in H] replaces in [H].
    [set_eq X HX: E in |-] performs no substitution at all. *)

Tactic Notation "set_eq" ident(X) ident(HX) ":" constr(E) :=
  set (X := E); def_to_eq X HX E.
Tactic Notation "set_eq" ident(X) ":" constr(E) :=
  let HX := fresh "EQ" X in set_eq X HX: E.
Tactic Notation "set_eq" ":" constr(E) :=
  let X := fresh "X" in set_eq X: E.

Tactic Notation "set_eq" "<-" ident(X) ident(HX) ":" constr(E) :=
  set (X := E); def_to_eq_sym X HX E.
Tactic Notation "set_eq" "<-" ident(X) ":" constr(E) :=
  let HX := fresh "EQ" X in set_eq <- X HX: E.
Tactic Notation "set_eq" "<-" ":" constr(E) :=
  let X := fresh "X" in set_eq <- X: E.

Tactic Notation "sets_eq" ident(X) ident(HX) ":" constr(E) :=
  set (X := E) in *; def_to_eq X HX E.
Tactic Notation "sets_eq" ident(X) ":" constr(E) :=
  let HX := fresh "EQ" X in sets_eq X HX: E.
Tactic Notation "sets_eq" ":" constr(E) :=
  let X := fresh "X" in sets_eq X: E.

Tactic Notation "sets_eq" "<-" ident(X) ident(HX) ":" constr(E) :=
  set (X := E) in *; def_to_eq_sym X HX E.
Tactic Notation "sets_eq" "<-" ident(X) ":" constr(E) :=
  let HX := fresh "EQ" X in sets_eq <- X HX: E.
Tactic Notation "sets_eq" "<-" ":" constr(E) :=
  let X := fresh "X" in sets_eq <- X: E.

Tactic Notation "set_eq" ident(X) ident(HX) ":" constr(E) "in" hyp(H) :=
  set (X := E) in H; def_to_eq X HX E.
Tactic Notation "set_eq" ident(X) ":" constr(E) "in" hyp(H) :=
  let HX := fresh "EQ" X in set_eq X HX: E in H.
Tactic Notation "set_eq" ":" constr(E) "in" hyp(H) :=
  let X := fresh "X" in set_eq X: E in H.

Tactic Notation "set_eq" "<-" ident(X) ident(HX) ":" constr(E) "in" hyp(H) :=
  set (X := E) in H; def_to_eq_sym X HX E.
Tactic Notation "set_eq" "<-" ident(X) ":" constr(E) "in" hyp(H) :=
  let HX := fresh "EQ" X in set_eq <- X HX: E in H.
Tactic Notation "set_eq" "<-" ":" constr(E) "in" hyp(H) :=
  let X := fresh "X" in set_eq <- X: E in H.

Tactic Notation "set_eq" ident(X) ident(HX) ":" constr(E) "in" "|-" :=
  set (X := E) in |-; def_to_eq X HX E.
Tactic Notation "set_eq" ident(X) ":" constr(E) "in" "|-" :=
  let HX := fresh "EQ" X in set_eq X HX: E in |-.
Tactic Notation "set_eq" ":" constr(E) "in" "|-" :=
  let X := fresh "X" in set_eq X: E in |-.

Tactic Notation "set_eq" "<-" ident(X) ident(HX) ":" constr(E) "in" "|-" :=
  set (X := E) in |-; def_to_eq_sym X HX E.
Tactic Notation "set_eq" "<-" ident(X) ":" constr(E) "in" "|-" :=
  let HX := fresh "EQ" X in set_eq <- X HX: E in |-.
Tactic Notation "set_eq" "<-" ":" constr(E) "in" "|-" :=
  let X := fresh "X" in set_eq <- X: E in |-.

(** [gen_eq X: E] is a tactic whose purpose is to introduce
    equalities so as to work around the limitation of the [induction]
    tactic which typically loses information. [gen_eq E as X] replaces
    all occurences of term [E] with a fresh variable [X] and the equality
    [X = E] as extra hypothesis to the current conclusion. In other words
    a conclusion [C] will be turned into [(X = E) -> C].
    [gen_eq: E] and [gen_eq: E as X] are also accepted. *)

Tactic Notation "gen_eq" ident(X) ":" constr(E) :=
  let EQ := fresh "EQ" X in sets_eq X EQ: E; revert EQ.
Tactic Notation "gen_eq" ":" constr(E) :=
  let X := fresh "X" in gen_eq X: E.
Tactic Notation "gen_eq" ":" constr(E) "as" ident(X) :=
  gen_eq X: E.
Tactic Notation "gen_eq" ident(X1) ":" constr(E1) ","
  ident(X2) ":" constr(E2) :=
  gen_eq X2: E2; gen_eq X1: E1.
Tactic Notation "gen_eq" ident(X1) ":" constr(E1) ","
  ident(X2) ":" constr(E2) "," ident(X3) ":" constr(E3) :=
  gen_eq X3: E3; gen_eq X2: E2; gen_eq X1: E1.

(** [sets_let X] finds the first let-expression in the goal
    and names its body [X]. [sets_eq_let X] is similar,
    except that it generates an explicit equality.
    Tactics [sets_let X in H] and [sets_eq_let X in H]
    allow specifying a particular hypothesis (by default,
    the first one that contains a [let] is considered).

    Known limitation: it does not seem possible to support
    naming of multiple let-in constructs inside a term, from ltac. *)

Ltac sets_let_base tac :=
  match goal with
  | |- context[let _ := ?E in _] => tac E; cbv zeta
  | H: context[let _ := ?E in _] |- _ => tac E; cbv zeta in H
  end.

Ltac sets_let_in_base H tac :=
  match type of H with context[let _ := ?E in _] =>
    tac E; cbv zeta in H end.

Tactic Notation "sets_let" ident(X) :=
  sets_let_base ltac:(fun E => sets X: E).
Tactic Notation "sets_let" ident(X) "in" hyp(H) :=
  sets_let_in_base H ltac:(fun E => sets X: E).
Tactic Notation "sets_eq_let" ident(X) :=
  sets_let_base ltac:(fun E => sets_eq X: E).
Tactic Notation "sets_eq_let" ident(X) "in" hyp(H) :=
  sets_let_in_base H ltac:(fun E => sets_eq X: E).

(* ################################################################# *)
(** * Rewriting *)

(** [rewrites E] is similar to [rewrite] except that
    it supports the [rm] directives to clear hypotheses
    on the fly, and that it supports a list of arguments in the form
    [rewrites (>> E1 E2 E3)] to indicate that [forwards] should be
    invoked first before [rewrites] is called. *)

Ltac rewrites_base E cont :=
  match type of E with
  | List.list Boxer => forwards_then E cont
  | _ => cont E; fast_rm_inside E
  end.

Tactic Notation "rewrites" constr(E) :=
  rewrites_base E ltac:(fun M => rewrite M ).
Tactic Notation "rewrites" constr(E) "in" hyp(H) :=
  rewrites_base E ltac:(fun M => rewrite M in H).
Tactic Notation "rewrites" constr(E) "in" "*" :=
  rewrites_base E ltac:(fun M => rewrite M in *).
Tactic Notation "rewrites" "<-" constr(E) :=
  rewrites_base E ltac:(fun M => rewrite <- M ).
Tactic Notation "rewrites" "<-" constr(E) "in" hyp(H) :=
  rewrites_base E ltac:(fun M => rewrite <- M in H).
Tactic Notation "rewrites" "<-" constr(E) "in" "*" :=
  rewrites_base E ltac:(fun M => rewrite <- M in *).

(** [erewrites E] is similar to [erewrite] except that
    it supports the [rm] directives to clear hypotheses
    on the fly, and that it supports a list of arguments in the form
    [rewrites (>> E1 E2 E3)] to indicate that [forwards] should be
    invoked first before [rewrites] is called. *)

Tactic Notation "erewrites" constr(E) :=
  rewrites_base E ltac:(fun M => erewrite M ).
Tactic Notation "erewrites" constr(E) "in" hyp(H) :=
  rewrites_base E ltac:(fun M => erewrite M in H).
Tactic Notation "erewrites" constr(E) "in" "*" :=
  rewrites_base E ltac:(fun M => erewrite M in *).
Tactic Notation "erewrites" "<-" constr(E) :=
  rewrites_base E ltac:(fun M => erewrite <- M ).
Tactic Notation "erewrites" "<-" constr(E) "in" hyp(H) :=
  rewrites_base E ltac:(fun M => erewrite <- M in H).
Tactic Notation "erewrites" "<-" constr(E) "in" "*" :=
  rewrites_base E ltac:(fun M => erewrite <- M in *).

(* --Note: should we extend tactics below to use [rewrites]? *)

(** [rewrite_all E] iterates version of [rewrite E] as long as possible.
    Warning: this tactic can easily get into an infinite loop.
    Syntax for rewriting from right to left and/or into an hypothese
    is similar to the one of [rewrite]. *)

Tactic Notation "rewrite_all" constr(E) :=
  repeat rewrite E.
Tactic Notation "rewrite_all" "<-" constr(E) :=
  repeat rewrite <- E.
Tactic Notation "rewrite_all" constr(E) "in" ident(H) :=
  repeat rewrite E in H.
Tactic Notation "rewrite_all" "<-" constr(E) "in" ident(H) :=
  repeat rewrite <- E in H.
Tactic Notation "rewrite_all" constr(E) "in" "*" :=
  repeat rewrite E in *.
Tactic Notation "rewrite_all" "<-" constr(E) "in" "*" :=
  repeat rewrite <- E in *.

(** [asserts_rewrite E] asserts that an equality [E] holds (generating a
    corresponding subgoal) and rewrite it straight away in the current
    goal. It avoids giving a name to the equality and later clearing it.
    Syntax for rewriting from right to left and/or into an hypothese
    is similar to the one of [rewrite]. Note: the tactic [replaces]
    plays a similar role. *)

Ltac asserts_rewrite_tactic E action :=
  let EQ := fresh "TEMP" in (assert (EQ : E);
  [ idtac | action EQ; clear EQ ]).

Tactic Notation "asserts_rewrite" constr(E) :=
  asserts_rewrite_tactic E ltac:(fun EQ => rewrite EQ).
Tactic Notation "asserts_rewrite" "<-" constr(E) :=
  asserts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ).
Tactic Notation "asserts_rewrite" constr(E) "in" hyp(H) :=
  asserts_rewrite_tactic E ltac:(fun EQ => rewrite EQ in H).
Tactic Notation "asserts_rewrite" "<-" constr(E) "in" hyp(H) :=
  asserts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ in H).
Tactic Notation "asserts_rewrite" constr(E) "in" "*" :=
  asserts_rewrite_tactic E ltac:(fun EQ => rewrite EQ in *).
Tactic Notation "asserts_rewrite" "<-" constr(E) "in" "*" :=
  asserts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ in *).

(** [cuts_rewrite E] is the same as [asserts_rewrite E] except
    that subgoals are permuted. *)

Ltac cuts_rewrite_tactic E action :=
  let EQ := fresh "TEMP" in (cuts EQ: E;
  [ action EQ; clear EQ | idtac ]).

Tactic Notation "cuts_rewrite" constr(E) :=
  cuts_rewrite_tactic E ltac:(fun EQ => rewrite EQ).
Tactic Notation "cuts_rewrite" "<-" constr(E) :=
  cuts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ).
Tactic Notation "cuts_rewrite" constr(E) "in" hyp(H) :=
  cuts_rewrite_tactic E ltac:(fun EQ => rewrite EQ in H).
Tactic Notation "cuts_rewrite" "<-" constr(E) "in" hyp(H) :=
  cuts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ in H).

(** [rewrite_except H EQ] rewrites equality [EQ] everywhere
    but in hypothesis [H]. Mainly useful for other tactics. *)

Ltac rewrite_except H EQ :=
  let K := fresh "TEMP" in let T := type of H in
  set (K := T) in H;
  rewrite EQ in *; unfold K in H; clear K.

(** [rewrites E at K] applies when [E] is of the form [T1 = T2]
    rewrites the equality [E] at the [K]-th occurence of [T1]
    in the current goal.
    Syntaxes [rewrites <- E at K] and [rewrites E at K in H]
    are also available. *)

Tactic Notation "rewrites" constr(E) "at" constr(K) :=
  match type of E with ?T1 = ?T2 =>
    ltac_action_at K of T1 do (rewrites E) end.
Tactic Notation "rewrites" "<-" constr(E) "at" constr(K) :=
  match type of E with ?T1 = ?T2 =>
    ltac_action_at K of T2 do (rewrites <- E) end.
Tactic Notation "rewrites" constr(E) "at" constr(K) "in" hyp(H) :=
  match type of E with ?T1 = ?T2 =>
    ltac_action_at K of T1 in H do (rewrites E in H) end.
Tactic Notation "rewrites" "<-" constr(E) "at" constr(K) "in" hyp(H) :=
  match type of E with ?T1 = ?T2 =>
    ltac_action_at K of T2 in H do (rewrites <- E in H) end.

(**  ** Replace *)

(** [replaces E with F] is the same as [replace E with F] except that
    the equality [E = F] is generated as first subgoal. Syntax
    [replaces E with F in H] is also available. Note that contrary to
    [replace], [replaces] does not try to solve the equality
    by [assumption]. Note: [replaces E with F] is similar to
    [asserts_rewrite (E = F)]. *)

Tactic Notation "replaces" constr(E) "with" constr(F) :=
  let T := fresh "TEMP" in assert (T: E = F); [ | replace E with F; clear T ].

Tactic Notation "replaces" constr(E) "with" constr(F) "in" hyp(H) :=
  let T := fresh "TEMP" in assert (T: E = F); [ | replace E with F in H; clear T ].

(** [replaces E at K with F] replaces the [K]-th occurence of [E]
    with [F] in the current goal. Syntax [replaces E at K with F in H]
    is also available. *)

Tactic Notation "replaces" constr(E) "at" constr(K) "with" constr(F) :=
  let T := fresh "TEMP" in assert (T: E = F); [ | rewrites T at K; clear T ].

Tactic Notation "replaces" constr(E) "at" constr(K) "with" constr(F) "in" hyp(H) :=
  let T := fresh "TEMP" in assert (T: E = F); [ | rewrites T at K in H; clear T ].

(**  ** Change *)

(** [changes] is like [change] except that it does not silently
   fail to perform its task. (Note that, [changes] is implemented
   using [rewrite], meaning that it might perform additional
   beta-reductions compared with the original [change] tactic. *)
(* --Note: should we support "changes (E1 = E2)" *)

Tactic Notation "changes" constr(E1) "with" constr(E2) "in" hyp(H) :=
  asserts_rewrite (E1 = E2) in H; [ reflexivity | ].

Tactic Notation "changes" constr(E1) "with" constr(E2) :=
  asserts_rewrite (E1 = E2); [ reflexivity | ].

Tactic Notation "changes" constr(E1) "with" constr(E2) "in" "*" :=
  asserts_rewrite (E1 = E2) in *; [ reflexivity | ].


(* ================================================================= *)
(** ** Renaming *)

(** [renames X1 to Y1, ..., XN to YN] is a shorthand for a sequence of
    renaming operations [rename Xi into Yi]. *)

Tactic Notation "renames" ident(X1) "to" ident(Y1) :=
  rename X1 into Y1.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) :=
  renames X1 to Y1; renames X2 to Y2.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) :=
  renames X1 to Y1; renames X2 to Y2, X3 to Y3.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) ","
 ident(X4) "to" ident(Y4) :=
  renames X1 to Y1; renames X2 to Y2, X3 to Y3, X4 to Y4.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) ","
 ident(X4) "to" ident(Y4) "," ident(X5) "to" ident(Y5) :=
  renames X1 to Y1; renames X2 to Y2, X3 to Y3, X4 to Y4, X5 to Y5.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) ","
 ident(X4) "to" ident(Y4) "," ident(X5) "to" ident(Y5) ","
 ident(X6) "to" ident(Y6) :=
  renames X1 to Y1; renames X2 to Y2, X3 to Y3, X4 to Y4, X5 to Y5, X6 to Y6.

(* ================================================================= *)
(** ** Unfolding *)

(** [unfolds] unfolds the head definition in the goal, i.e. if the
    goal has form [P x1 ... xN] then it calls [unfold P].
    If the goal is an equality, it tries to unfold the head constant
    on the left-hand side, and otherwise tries on the right-hand side.
    If the goal is a product, it calls [intros] first.
    -- warning: this tactic is overriden in LibReflect. *)

Ltac apply_to_head_of E cont :=
  let go E :=
    let P := get_head E in cont P in
  match E with
  | forall _,_ => intros; apply_to_head_of E cont
  | ?A = ?B => first [ go A | go B ]
  | ?A => go A
  end.

Ltac unfolds_base :=
  match goal with |- ?G =>
   apply_to_head_of G ltac:(fun P => unfold P) end.

Tactic Notation "unfolds" :=
  unfolds_base.

(** [unfolds in H] unfolds the head definition of hypothesis [H], i.e. if
    [H] has type [P x1 ... xN] then it calls [unfold P in H]. *)

Ltac unfolds_in_base H :=
  match type of H with ?G =>
   apply_to_head_of G ltac:(fun P => unfold P in H) end.

Tactic Notation "unfolds" "in" hyp(H) :=
  unfolds_in_base H.

(** [unfolds in H1,H2,..,HN] allows unfolding the head constant
    in several hypotheses at once. *)

Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) :=
  unfolds in H1; unfolds in H2.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) :=
  unfolds in H1; unfolds in H2 H3.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) hyp(H4) :=
  unfolds in H1; unfolds in H2 H3 H4.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5) :=
  unfolds in H1; unfolds in H2 H3 H4 H5.

(** [unfolds P1,..,PN] is a shortcut for [unfold P1,..,PN in *]. *)

Tactic Notation "unfolds" constr(F1) :=
  unfold F1 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2) :=
  unfold F1,F2 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) :=
  unfold F1,F2,F3 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) :=
  unfold F1,F2,F3,F4 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5) :=
  unfold F1,F2,F3,F4,F5 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5) "," constr(F6) :=
  unfold F1,F2,F3,F4,F5,F6 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5)
 "," constr(F6) "," constr(F7) :=
  unfold F1,F2,F3,F4,F5,F6,F7 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5)
 "," constr(F6) "," constr(F7) "," constr(F8) :=
  unfold F1,F2,F3,F4,F5,F6,F7,F8 in *.

(** [folds P1,..,PN] is a shortcut for [fold P1 in *; ..; fold PN in *]. *)

Tactic Notation "folds" constr(H) :=
  fold H in *.
Tactic Notation "folds" constr(H1) "," constr(H2) :=
  folds H1; folds H2.
Tactic Notation "folds" constr(H1) "," constr(H2) "," constr(H3) :=
  folds H1; folds H2; folds H3.
Tactic Notation "folds" constr(H1) "," constr(H2) "," constr(H3)
 "," constr(H4) :=
  folds H1; folds H2; folds H3; folds H4.
Tactic Notation "folds" constr(H1) "," constr(H2) "," constr(H3)
 "," constr(H4) "," constr(H5) :=
  folds H1; folds H2; folds H3; folds H4; folds H5.

(* ================================================================= *)
(** ** Simplification *)

(** [simpls] is a shortcut for [simpl in *]. *)

Tactic Notation "simpls" :=
  simpl in *.

(** [simpls P1,..,PN] is a shortcut for
    [simpl P1 in *; ..; simpl PN in *]. *)

Tactic Notation "simpls" constr(F1) :=
  simpl F1 in *.
Tactic Notation "simpls" constr(F1) "," constr(F2) :=
  simpls F1; simpls F2.
Tactic Notation "simpls" constr(F1) "," constr(F2)
 "," constr(F3) :=
  simpls F1; simpls F2; simpls F3.
Tactic Notation "simpls" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) :=
  simpls F1; simpls F2; simpls F3; simpls F4.

(** [unsimpl E] replaces all occurence of [X] by [E], where [X] is
   the result which the tactic [simpl] would give when applied to [E].
   It is useful to undo what [simpl] has simplified too far. *)

Tactic Notation "unsimpl" constr(E) :=
  let F := (eval simpl in E) in change F with E.

(** [unsimpl E in H] is similar to [unsimpl E] but it applies
    inside a particular hypothesis [H]. *)

Tactic Notation "unsimpl" constr(E) "in" hyp(H) :=
  let F := (eval simpl in E) in change F with E in H.

(** [unsimpl E in *] applies [unsimpl E] everywhere possible.
    [unsimpls E] is a synonymous. *)

Tactic Notation "unsimpl" constr(E) "in" "*" :=
  let F := (eval simpl in E) in change F with E in *.
Tactic Notation "unsimpls" constr(E) :=
  unsimpl E in *.

(** [nosimpl t] protects the Coq term[t] against some forms of
    simplification. See Gonthier's work for details on this trick. *)

Notation "'nosimpl' t" := (match tt with tt => t end)
  (at level 10).

(* ================================================================= *)
(** ** Reduction *)

Tactic Notation "hnfs" := hnf in *.

(* ================================================================= *)
(** ** Substitution *)

(** [substs] does the same as [subst], except that it does not fail
    when there are circular equalities in the context. *)

Tactic Notation "substs" :=
  repeat (match goal with H: ?x = ?y |- _ =>
            first [ subst x | subst y ] end).

(** Implementation of [substs below], which allows to call
    [subst] on all the hypotheses that lie beyond a given
    position in the proof context. *)

Ltac substs_below limit :=
  match goal with H: ?T |- _ =>
  match T with
  | limit => idtac
  | ?x = ?y =>
    first [ subst x; substs_below limit
          | subst y; substs_below limit
          | generalizes H; substs_below limit; intro ]
  end end.

(** [substs below body E] applies [subst] on all equalities that appear
    in the context below the first hypothesis whose body is [E].
    If there is no such hypothesis in the context, it is equivalent
    to [subst]. For instance, if [H] is an hypothesis, then
    [substs below H] will substitute equalities below hypothesis [H]. *)

Tactic Notation "substs" "below" "body" constr(M) :=
  substs_below M.

(** [substs below H] applies [subst] on all equalities that appear
    in the context below the hypothesis named [H]. Note that
    the current implementation is technically incorrect since it
    will confuse different hypotheses with the same body. *)

Tactic Notation "substs" "below" hyp(H) :=
  match type of H with ?M => substs below body M end.

(** [subst_hyp H] substitutes the equality contained in the
    first hypothesis from the context. *)

Ltac intro_subst_hyp := fail. (* definition further on *)

(** [subst_hyp H] substitutes the equality contained in [H]. *)

Ltac subst_hyp_base H :=
  match type of H with
  | (_,_,_,_,_) = (_,_,_,_,_) => injection H; clear H; do 4 intro_subst_hyp
  | (_,_,_,_) = (_,_,_,_) => injection H; clear H; do 4 intro_subst_hyp
  | (_,_,_) = (_,_,_) => injection H; clear H; do 3 intro_subst_hyp
  | (_,_) = (_,_) => injection H; clear H; do 2 intro_subst_hyp
  | ?x = ?x => clear H
  | ?x = ?y => first [ subst x | subst y ]
  end.

Tactic Notation "subst_hyp" hyp(H) := subst_hyp_base H.

Ltac intro_subst_hyp ::=
  let H := fresh "TEMP" in intros H; subst_hyp H.

(** [intro_subst] is a shorthand for [intro H; subst_hyp H]:
    it introduces and substitutes the equality at the head
    of the current goal. *)

Tactic Notation "intro_subst" :=
  let H := fresh "TEMP" in intros H; subst_hyp H.

(** [subst_local] substitutes all local definition from the context *)

Ltac subst_local :=
  repeat match goal with H:=_ |- _ => subst H end.

(** [subst_eq E] takes an equality [x = t] and replace [x]
    with [t] everywhere in the goal *)

Ltac subst_eq_base E :=
  let H := fresh "TEMP" in lets H: E; subst_hyp H.

Tactic Notation "subst_eq" constr(E) :=
  subst_eq_base E.

(* ================================================================= *)
(** ** Tactics to Work with Proof Irrelevance *)

Import Coq.Logic.ProofIrrelevance.

(** [pi_rewrite E] replaces [E] of type [Prop] with a fresh
    unification variable, and is thus a practical way to
    exploit proof irrelevance, without writing explicitly
    [rewrite (proof_irrelevance E E')]. Particularly useful
    when [E'] is a big expression. *)

Ltac pi_rewrite_base E rewrite_tac :=
  let E' := fresh "TEMP" in let T := type of E in evar (E':T);
  rewrite_tac (@proof_irrelevance _ E E'); subst E'.

Tactic Notation "pi_rewrite" constr(E) :=
  pi_rewrite_base E ltac:(fun X => rewrite X).
Tactic Notation "pi_rewrite" constr(E) "in" hyp(H) :=
  pi_rewrite_base E ltac:(fun X => rewrite X in H).

(* ================================================================= *)
(** ** Proving Equalities *)

(** The tactic [fequal] enhances Coq's tactic [f_equal], which does not
    simplify equalities between tuples, nor between dependent pairs of
    the form [exist _ _] or [existT _ _]. For support of dependent pairs,
    the file [LibEqual] must be imported.

    Subgoals solvable by [reflexivity] are automatically discharged.
    See also the the variant [fequals], which discharges more subgoals. *)

(** Note: only [args_eq_2] is actually useful for the implementation of
    [fequal], if we rely on Coq's [f_equal] tactic for other arities.
    We provide these lemmas to show the pattern of lemmas to exploit
    for implementing [fequal] independently of [f_equal]. *)

Section FuncEq.
Variables (A1 A2 A3 A4 A5 A6 A7 B : Type).

Lemma args_eq_1 : forall (f:A1->B) x1 y1,
  x1 = y1 ->
  f x1 = f y1.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_2 : forall (f:A1->A2->B) x1 y1 x2 y2,
  x1 = y1 -> x2 = y2 ->
  f x1 x2 = f y1 y2.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_3 : forall (f:A1->A2->A3->B) x1 y1 x2 y2 x3 y3,
  x1 = y1 -> x2 = y2 -> x3 = y3 ->
  f x1 x2 x3 = f y1 y2 y3.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_4 : forall (f:A1->A2->A3->A4->B) x1 y1 x2 y2 x3 y3 x4 y4,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 ->
  f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_5 : forall (f:A1->A2->A3->A4->A5->B) x1 y1 x2 y2 x3 y3 x4 y4 x5 y5,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 ->
  f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_6 : forall (f:A1->A2->A3->A4->A5->A6->B) x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 ->
  f x1 x2 x3 x4 x5 x6 = f y1 y2 y3 y4 y5 y6.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_7 : forall (f:A1->A2->A3->A4->A5->A6->A7->B) x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 x7 y7,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 -> x7 = y7 ->
  f x1 x2 x3 x4 x5 x6 x7 = f y1 y2 y3 y4 y5 y6 y7.
Proof using. intros. subst. auto. Qed.

End FuncEq.

Ltac fequal_post :=
  try solve [ reflexivity ].

(** [fequal_support_for_exist], implemented in [LibEqual], is meant
   to simplify goals of the form [exist _ _ = exist _ _ ] and
   [existT _ _ = existT _ _], by exploiting proof irrelevance. *)

Ltac fequal_support_for_exist tt :=
  fail.

(** For a n-ary tuple, [fequal], unlike [f_equal] enforces a recursive call
    on the (n-1)-ary tuple associated with the right component. *)

Ltac fequal_base :=
  match goal with
  | |- (_,_,_) = (_,_,_) =>  apply args_eq_2; [ fequal_base | ]
  | |- _ => first
            [ fequal_support_for_exist tt
            | apply args_eq_1
            | apply args_eq_2
            | apply args_eq_3
            | apply args_eq_4
            | apply args_eq_5
            | apply args_eq_6
            | apply args_eq_7
            | f_equal (* fallback to Coq [f_equal] *) ]
  end.

Tactic Notation "fequal" :=
  fequal_base; fequal_post.

(** [fequals] is the same as [fequal] except that it tries and solve
    all trivial subgoals, using [reflexivity] and [congruence]
    (as well as the proof-irrelevance principle).
    [fequals] applies to goals of the form [f x1 .. xN = f y1 .. yN]
    and produces some subgoals of the form [xi = yi]). *)

Ltac fequals_post :=
  try solve [ reflexivity | congruence | apply proof_irrelevance ].

Tactic Notation "fequals" :=
  fequal; fequals_post.

(** [fequals_rec] calls [fequals] recursively.
    It is equivalent to [repeat (progress fequals)]. *)

Tactic Notation "fequals_rec" :=
  repeat (progress fequals).


(* ################################################################# *)
(** * Inversion *)

(* ================================================================= *)
(** ** Basic Inversion *)

(** [invert keep H] is same to [inversion H] except that it puts all the
    facts obtained in the goal. The keyword [keep] means that the
    hypothesis [H] should not be removed. *)

Tactic Notation "invert" "keep" hyp(H) :=
  pose ltac_mark; inversion H; gen_until_mark.

(** [invert keep H as X1 .. XN] is the same as [inversion H as ...] except
    that only hypotheses which are not variable need to be named
    explicitely, in a similar fashion as [introv] is used to name
    only hypotheses. *)

Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1) :=
  invert keep H; introv I1.
Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  invert keep H; introv I1 I2.
Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  invert keep H; introv I1 I2 I3.

(** [invert H] is same to [inversion H] except that it puts all the
    facts obtained in the goal and clears hypothesis [H].
    In other words, it is equivalent to [invert keep H; clear H]. *)

Tactic Notation "invert" hyp(H) :=
  invert keep H; clear H.

(** [invert H as X1 .. XN] is the same as [invert keep H as X1 .. XN]
    but it also clears hypothesis [H]. *)

Tactic Notation "invert_tactic" hyp(H) tactic(tac) :=
  let H' := fresh "TEMP" in rename H into H'; tac H'; clear H'.
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1) :=
  invert_tactic H (fun H => invert keep H as I1).
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  invert_tactic H (fun H => invert keep H as I1 I2).
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  invert_tactic H (fun H => invert keep H as I1 I2 I3).

(* ================================================================= *)
(** ** Inversion with Substitution *)

(** Our inversion tactics is able to get rid of dependent equalities
    generated by [inversion], using proof irrelevance. *)

(* --we do not import Eqdep because it imports nasty hints automatically
    From TLC Require Import Eqdep. *)

Axiom inj_pair2 :  (* is in fact derivable from the axioms in LibAxiom.v *)
  forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
  existT P p x = existT P p y -> x = y.
(* Proof using. apply Eqdep.EqdepTheory.inj_pair2. Qed. *)

Ltac inverts_tactic H i1 i2 i3 i4 i5 i6 :=
  let rec go i1 i2 i3 i4 i5 i6 :=
    match goal with
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H;
                           first [ subst x | subst y ];
                           go i1 i2 i3 i4 i5 i6
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh "TEMP" in intro H;
         generalize (@inj_pair2 _ P p x y H);
         clear H; go i1 i2 i3 i4 i5 i6
    | |- (?P -> ?Q) => i1; go i2 i3 i4 i5 i6 ltac:(intro)
    | |- (forall _, _) => intro; go i1 i2 i3 i4 i5 i6
    end in
  generalize ltac_mark; invert keep H; go i1 i2 i3 i4 i5 i6;
  unfold eq' in *.

(** [inverts keep H] is same to [invert keep H] except that it
    applies [subst] to all the equalities generated by the inversion. *)

Tactic Notation "inverts" "keep" hyp(H) :=
  inverts_tactic H ltac:(intro) ltac:(intro) ltac:(intro)
                   ltac:(intro) ltac:(intro) ltac:(intro).

(** [inverts keep H as X1 .. XN] is the same as
    [invert keep H as X1 .. XN] except that it applies [subst] to all the
    equalities generated by the inversion *)

Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1) :=
  inverts_tactic H ltac:(intros I1)
   ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2)
   ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intros I4) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intros I4) ltac:(intros I5) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) simple_intropattern(I6) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intros I4) ltac:(intros I5) ltac:(intros I6).

(** [inverts H] is same to [inverts keep H] except that it
    clears hypothesis [H]. *)

Tactic Notation "inverts" hyp(H) :=
  inverts keep H; try clear H.

(** [inverts H as X1 .. XN] is the same as [inverts keep H as X1 .. XN]
    but it also clears the hypothesis [H]. *)

Tactic Notation "inverts_tactic" hyp(H) tactic(tac) :=
  let H' := fresh "TEMP" in rename H into H'; tac H'; clear H'.
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1) :=
  invert_tactic H (fun H => inverts keep H as I1).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  invert_tactic H (fun H => inverts keep H as I1 I2).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4 I5).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) simple_intropattern(I6) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4 I5 I6).

(** [inverts H as] performs an inversion on hypothesis [H], substitutes
    generated equalities, and put in the goal the other freshly-created
    hypotheses, for the user to name explicitly.
    [inverts keep H as] is the same except that it does not clear [H].
    --Note: maybe reimplement [inverts] above using this one *)

Ltac inverts_as_tactic H :=
  let rec go tt :=
    match goal with
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H;
                           first [ subst x | subst y ];
                           go tt
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh "TEMP" in intro H;
         generalize (@inj_pair2 _ P p x y H);
         clear H; go tt
    | |- (forall _, _) =>
       intro; let H := get_last_hyp tt in mark_to_generalize H; go tt
    end in
  pose ltac_mark; inversion H;
  generalize ltac_mark; gen_until_mark;
  go tt; gen_to_generalize; unfolds ltac_to_generalize;
  unfold eq' in *.

Tactic Notation "inverts" "keep" hyp(H) "as" :=
  inverts_as_tactic H.

Tactic Notation "inverts" hyp(H) "as" :=
  inverts_as_tactic H; clear H.

Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) simple_intropattern(I6) simple_intropattern(I7) :=
  inverts H as; introv I1 I2 I3 I4 I5 I6 I7.
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) simple_intropattern(I6) simple_intropattern(I7)
 simple_intropattern(I8) :=
  inverts H as; introv I1 I2 I3 I4 I5 I6 I7 I8.

(** [lets_inverts E as I1 .. IN] is intuitively equivalent to
    [inverts E], with the difference that it applies to any
    expression and not just to the name of an hypothesis. *)

Ltac lets_inverts_base E cont :=
  let H := fresh "TEMP" in lets H: E; try cont H.

Tactic Notation "lets_inverts" constr(E) :=
  lets_inverts_base E ltac:(fun H => inverts H).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1) :=
  lets_inverts_base E ltac:(fun H => inverts H as I1).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  lets_inverts_base E ltac:(fun H => inverts H as I1 I2).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  lets_inverts_base E ltac:(fun H => inverts H as I1 I2 I3).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
  lets_inverts_base E ltac:(fun H => inverts H as I1 I2 I3 I4).


(* ================================================================= *)
(** ** Injection with Substitution *)

(** Underlying implementation of [injects] *)

Ltac injects_tactic H :=
  let rec go _ :=
    match goal with
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H;
                           first [ subst x | subst y | idtac ];
                           go tt
    end in
  generalize ltac_mark; injection H; go tt.

(** [injects keep H] takes an hypothesis [H] of the form
    [C a1 .. aN = C b1 .. bN] and substitute all equalities
    [ai = bi] that have been generated. *)

Tactic Notation "injects" "keep" hyp(H) :=
  injects_tactic H.

(** [injects H] is similar to [injects keep H] but clears
    the hypothesis [H]. *)

Tactic Notation "injects" hyp(H) :=
  injects_tactic H; clear H.

(** [inject H as X1 .. XN] is the same as [injection]
    followed by [intros X1 .. XN] *)

Tactic Notation "inject" hyp(H) :=
  injection H.
Tactic Notation "inject" hyp(H) "as" ident(X1) :=
  injection H; intros X1.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) :=
  injection H; intros X1 X2.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) ident(X3) :=
  injection H; intros X1 X2 X3.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) ident(X3)
 ident(X4) :=
  injection H; intros X1 X2 X3 X4.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) ident(X3)
 ident(X4) ident(X5) :=
  injection H; intros X1 X2 X3 X4 X5.

(* ================================================================= *)
(** ** Inversion and Injection with Substitution --rough implementation *)

(** The tactics [inversions] and [injections] provided in this section
    are similar to [inverts] and [injects] except that they perform
    substitution on all equalities from the context and not only
    the ones freshly generated. The counterpart is that they have
    simpler implementations.

    DEPRECATED: these tactics should no longer be used. *)

(** [inversions keep H] is the same as [inversions H] but it does
    not clear hypothesis [H]. *)

Tactic Notation "inversions" "keep" hyp(H) :=
  inversion H; subst.

(** [inversions H] is a shortcut for [inversion H] followed by [subst]
    and [clear H].
    It is a rough implementation of [inverts keep H] which behave
    badly when the proof context already contains equalities.
    It is provided in case the better implementation turns out to be
    too slow. *)

Tactic Notation "inversions" hyp(H) :=
  inversion H; subst; try clear H.

(** [injections keep H] is the same as [injection H] followed
    by [intros] and [subst]. It is a rough implementation of
    [injects keep H] which behave
    badly when the proof context already contains equalities,
    or when the goal starts with a forall or an implication. *)

Tactic Notation "injections" "keep" hyp(H) :=
  injection H; intros; subst.

(** [injections H] is the same as [injection H] followed
    by [clear H] and [intros] and [subst]. It is a rough
    implementation of [injects keep H] which behave
    badly when the proof context already contains equalities,
    or when the goal starts with a forall or an implication. *)

Tactic Notation "injections" "keep" hyp(H) :=
  injection H; clear H; intros; subst.

(* ================================================================= *)
(** ** Case Analysis *)

(** [cases] is similar to [case_eq E] except that it generates the
    equality in the context and not in the goal, and generates the
    equality the other way round. The syntax [cases E as H]
    allows specifying the name [H] of that hypothesis. *)

Tactic Notation "cases" constr(E) "as" ident(H) :=
  let X := fresh "TEMP" in
  set (X := E) in *; def_to_eq_sym X H E;
  destruct X.

Tactic Notation "cases" constr(E) :=
  let H := fresh "Eq" in cases E as H.

(** [case_if_post H] is to be defined later as a tactic to clean
    up hypothesis [H] and the goal.
    By defaults, it looks for obvious contradictions.
    Currently, this tactic is extended in LibReflect to clean up
    boolean propositions. *)

Ltac case_if_post H :=
  tryfalse.

(** [case_if] looks for a pattern of the form [if ?B then ?E1 else ?E2]
    in the goal, and perform a case analysis on [B] by calling
    [destruct B]. Subgoals containing a contradiction are discarded.
    [case_if] looks in the goal first, and otherwise in the
    first hypothesis that contains an [if] statement.
    [case_if in H] can be used to specify which hypothesis to consider.
    Syntaxes [case_if as Eq] and [case_if in H as Eq] allows to name
    the hypothesis coming from the case analysis. *)

Ltac case_if_on_tactic_core E Eq :=
  match type of E with
  | {_}+{_} => destruct E as [Eq | Eq]
  | _ => let X := fresh "TEMP" in
         sets_eq <- X Eq: E;
         destruct X
  end.

Ltac case_if_on_tactic E Eq :=
  case_if_on_tactic_core E Eq; case_if_post Eq.

Tactic Notation "case_if_on" constr(E) "as" simple_intropattern(Eq) :=
  case_if_on_tactic E Eq.

Tactic Notation "case_if" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [if ?B then _ else _] => case_if_on B as Eq
  | K: context [if ?B then _ else _] |- _ => case_if_on B as Eq
  end.

Tactic Notation "case_if" "in" hyp(H) "as" simple_intropattern(Eq) :=
  match type of H with context [if ?B then _ else _] =>
    case_if_on B as Eq end.

Tactic Notation "case_if" :=
  let Eq := fresh "C" in case_if as Eq.

Tactic Notation "case_if" "in" hyp(H) :=
  let Eq := fresh "C" in case_if in H as Eq.

(** [cases_if] is similar to [case_if] with two main differences:
    if it creates an equality of the form [x = y] and then
    substitutes it in the goal *)

Ltac cases_if_on_tactic_core E Eq :=
  match type of E with
  | {_}+{_} => destruct E as [Eq|Eq]; try subst_hyp Eq
  | _ => let X := fresh "TEMP" in
         sets_eq <- X Eq: E;
         destruct X
  end.

Ltac cases_if_on_tactic E Eq :=
  cases_if_on_tactic_core E Eq; tryfalse; case_if_post Eq.

Tactic Notation "cases_if_on" constr(E) "as" simple_intropattern(Eq) :=
  cases_if_on_tactic E Eq.

Tactic Notation "cases_if" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [if ?B then _ else _] => cases_if_on B as Eq
  | K: context [if ?B then _ else _] |- _ => cases_if_on B as Eq
  end.

Tactic Notation "cases_if" "in" hyp(H) "as" simple_intropattern(Eq) :=
  match type of H with context [if ?B then _ else _] =>
    cases_if_on B as Eq end.

Tactic Notation "cases_if" :=
  let Eq := fresh "C" in cases_if as Eq.

Tactic Notation "cases_if" "in" hyp(H) :=
  let Eq := fresh "C" in cases_if in H as Eq.

(** [case_ifs] is like [repeat case_if] *)

Ltac case_ifs_core :=
  repeat case_if.

Tactic Notation "case_ifs" :=
  case_ifs_core.

(** [destruct_if] looks for a pattern of the form [if ?B then ?E1 else ?E2]
    in the goal, and perform a case analysis on [B] by calling
    [destruct B]. It looks in the goal first, and otherwise in the
    first hypothesis that contains an [if] statement. *)

Ltac destruct_if_post := tryfalse.

Tactic Notation "destruct_if"
 "as" simple_intropattern(Eq1) simple_intropattern(Eq2) :=
  match goal with
  | |- context [if ?B then _ else _] => destruct B as [Eq1|Eq2]
  | K: context [if ?B then _ else _] |- _ => destruct B as [Eq1|Eq2]
  end;
  destruct_if_post.

Tactic Notation "destruct_if" "in" hyp(H)
 "as" simple_intropattern(Eq1) simple_intropattern(Eq2) :=
  match type of H with context [if ?B then _ else _] =>
    destruct B as [Eq1|Eq2] end;
  destruct_if_post.

Tactic Notation "destruct_if" "as" simple_intropattern(Eq) :=
  destruct_if as Eq Eq.
Tactic Notation "destruct_if" "in" hyp(H) "as" simple_intropattern(Eq) :=
  destruct_if in H as Eq Eq.

Tactic Notation "destruct_if" :=
  let Eq := fresh "C" in destruct_if as Eq Eq.
Tactic Notation "destruct_if" "in" hyp(H) :=
  let Eq := fresh "C" in destruct_if in H as Eq Eq.

(** [cases'] is provided for compatibility with [remember]. *)

(** [cases' E] is similar to [case_eq E] except that it generates the
    equality in the context and not in the goal. The syntax [cases' E as H]
    allows specifying the name [H] of that hypothesis. *)

Tactic Notation "cases'" constr(E) "as" ident(H) :=
  let X := fresh "TEMP" in
  set (X := E) in *; def_to_eq X H E;
  destruct X.

Tactic Notation "cases'" constr(E) :=
  let x := fresh "Eq" in cases' E as H.

(** [cases_if'] is similar to [cases_if] except that it generates
    the symmetric equality. *)

Ltac cases_if_on' E Eq :=
  match type of E with
  | {_}+{_} => destruct E as [Eq|Eq]; try subst_hyp Eq
  | _ => let X := fresh "TEMP" in
         sets_eq X Eq: E;
         destruct X
  end; case_if_post Eq.

Tactic Notation "cases_if'" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [if ?B then _ else _] => cases_if_on' B Eq
  | K: context [if ?B then _ else _] |- _ => cases_if_on' B Eq
  end.

Tactic Notation "cases_if'" :=
  let Eq := fresh "C" in cases_if' as Eq.

(* ################################################################# *)
(** * Induction *)

(** [inductions E] is a shorthand for [dependent induction E].
    [inductions E gen X1 .. XN] is a shorthand for
    [dependent induction E generalizing X1 .. XN]. *)

Import Coq.Program.Equality.

Ltac inductions_post :=
  unfold eq' in *.

Tactic Notation "inductions" ident(E) :=
  dependent induction E; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) :=
  dependent induction E generalizing X1; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2) :=
  dependent induction E generalizing X1 X2; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
 ident(X3) :=
  dependent induction E generalizing X1 X2 X3; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
 ident(X3) ident(X4) :=
  dependent induction E generalizing X1 X2 X3 X4; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
 ident(X3) ident(X4) ident(X5) :=
  dependent induction E generalizing X1 X2 X3 X4 X5; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
 ident(X3) ident(X4) ident(X5) ident(X6) :=
  dependent induction E generalizing X1 X2 X3 X4 X5 X6; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
 ident(X3) ident(X4) ident(X5) ident(X6) ident(X7) :=
  dependent induction E generalizing X1 X2 X3 X4 X5 X6 X7; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
 ident(X3) ident(X4) ident(X5) ident(X6) ident(X7) ident(X8) :=
  dependent induction E generalizing X1 X2 X3 X4 X5 X6 X7 X8; inductions_post.

(** [induction_wf IH: E X] is used to apply the well-founded induction
    principle, for a given well-founded relation. It applies to a goal
    [PX] where [PX] is a proposition on [X]. First, it sets up the
    goal in the form [(fun a => P a) X], using [pattern X], and then
    it applies the well-founded induction principle instantiated on [E].

    Here [E] may be either:
   - a proof of [wf R] for [R] of type [A->A->Prop]
   - a binary relation of type [A->A->Prop]
   - a measure of type [A -> nat] // only when LibWf is used. *)

(* DEPRECATED
Tactic Notation "induction_wf" ident(IH) ":" constr(E) ident(X) :=
  pattern X; apply (well_founded_ind E); clear X; intros X IH.
*)

Ltac induction_wf_process_wf_hyp tt := (* refined in LibWf *)
  idtac.

Ltac induction_wf_process_measure E := (* refined in LibWf *)
  fail.

Ltac induction_wf_core_then E X cont :=
  let clearX tt :=
    first [ clear X | fail 3 "the variable on which the induction is done appears in the hypotheses" ] in
  pattern X;
  first [ eapply (@well_founded_ind _ E)
        | eapply (@well_founded_ind _ (E _))
        | eapply (@well_founded_ind _ (E _ _))
        | eapply (@well_founded_ind _ (E _ _ _))
        | induction_wf_process_measure E
        | applys well_founded_ind E ];
  clearX tt;
  first [ induction_wf_process_wf_hyp tt
        | intros X; cont tt ].

Ltac induction_wf_core IH E X :=
  induction_wf_core_then E X ltac:(fun _ => intros IH).

Tactic Notation "induction_wf" ident(IH) ":" constr(E) ident(X) :=
  induction_wf_core IH E X.

(** Induction on the height of a derivation: the helper tactic
    [induct_height] helps proving the equivalence of the auxiliary
    judgment that includes a counter for the maximal height
    (see LibTacticsDemos for an example) *)

Import Coq.Arith.Compare_dec.
Import Coq.micromega.Lia.

Lemma induct_height_max2 : forall n1 n2 : nat,
  exists n, n1 < n /\ n2 < n.
Proof using.
  intros. destruct (lt_dec n1 n2).
  exists (S n2). lia.
  exists (S n1). lia.
Qed.

Ltac induct_height_step x :=
  match goal with
  | H: exists _, _ |- _ =>
     let n := fresh "n" in let y := fresh "x" in
     destruct H as [n ?];
     forwards (y&?&?): induct_height_max2 n x;
     induct_height_step y
  | _ => exists (S x); eauto
 end.

Ltac induct_height := induct_height_step O.

(* ################################################################# *)
(** * Coinduction *)

(** Tactic [cofixs IH] is like [cofix IH] except that the
    coinduction hypothesis is tagged in the form [IH: COIND P]
    instead of being just [IH: P]. This helps other tactics
    clearing the coinduction hypothesis using [clear_coind] *)

Definition COIND (P:Prop) := P.

Tactic Notation "cofixs" ident(IH) :=
  cofix IH;
  match type of IH with ?P => change P with (COIND P) in IH end.

(** Tactic [clear_coind] clears all the coinduction hypotheses,
    assuming that they have been tagged *)

Ltac clear_coind :=
  repeat match goal with H: COIND _ |- _ => clear H end.

(** Tactic [abstracts tac] is like [abstract tac] except that
    it clears the coinduction hypotheses so that the productivity
    check will be happy. For example, one can use [abstracts lia]
    to obtain the same behavior as [lia] but with an auxiliary
    lemma being generated. *)

Tactic Notation "abstracts" tactic(tac) :=
  clear_coind; tac.


(* ################################################################# *)
(** * Decidable Equality *)

(** [decides_equality] is the same as [decide equality] excepts that it
    is able to unfold definitions at head of the current goal. *)

Ltac decides_equality_tactic :=
  first [ decide equality | progress(unfolds); decides_equality_tactic ].

Tactic Notation "decides_equality" :=
  decides_equality_tactic.

(* ################################################################# *)
(** * Equivalence *)

(** [iff H] can be used to prove an equivalence [P <-> Q] and name [H]
    the hypothesis obtained in each case. The syntaxes [iff] and [iff H1 H2]
    are also available to specify zero or two names. The tactic [iff <- H]
    swaps the two subgoals, i.e. produces (Q -> P) as first subgoal. *)

Lemma iff_intro_swap : forall (P Q : Prop),
  (Q -> P) -> (P -> Q) -> (P <-> Q).
Proof using. intuition. Qed.

Tactic Notation "iff" simple_intropattern(H1) simple_intropattern(H2) :=
  split; [ intros H1 | intros H2 ].
Tactic Notation "iff" simple_intropattern(H) :=
  iff H H.
Tactic Notation "iff" :=
  let H := fresh "H" in iff H.

Tactic Notation "iff" "<-" simple_intropattern(H1) simple_intropattern(H2) :=
  apply iff_intro_swap; [ intros H1 | intros H2 ].
Tactic Notation "iff" "<-" simple_intropattern(H) :=
  iff <- H H.
Tactic Notation "iff" "<-" :=
  let H := fresh "H" in iff <- H.

(* ################################################################# *)
(** * N-ary Conjunctions and Disjunctions *)

(** N-ary Conjunctions Splitting in Goals *)

(** Underlying implementation of [splits]. *)

Ltac splits_tactic N :=
  match N with
  | O => fail
  | S O => idtac
  | S ?N' => split; [| splits_tactic N']
  end.

Ltac unfold_goal_until_conjunction :=
  match goal with
  | |- _ /\ _ => idtac
  | _ => progress(unfolds); unfold_goal_until_conjunction
  end.

Ltac get_term_conjunction_arity T :=
  match T with
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(8)
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(7)
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(6)
  | _ /\ _ /\ _ /\ _ /\ _ => constr:(5)
  | _ /\ _ /\ _ /\ _ => constr:(4)
  | _ /\ _ /\ _ => constr:(3)
  | _ /\ _ => constr:(2)
  | _ -> ?T' => get_term_conjunction_arity T'
  | _ => let P := get_head T in
         let T' := eval unfold P in T in
         match T' with
         | T => fail 1
         | _ => get_term_conjunction_arity T'
         end
         (* --todo: warning this can loop... *)
  end.

Ltac get_goal_conjunction_arity :=
  match goal with |- ?T => get_term_conjunction_arity T end.

(** [splits] applies to a goal of the form [(T1 /\ .. /\ TN)] and
    destruct it into [N] subgoals [T1] .. [TN]. If the goal is not a
    conjunction, then it unfolds the head definition. *)

Tactic Notation "splits" :=
  unfold_goal_until_conjunction;
  let N := get_goal_conjunction_arity in
  splits_tactic N.

(** [splits N] is similar to [splits], except that it will unfold as many
    definitions as necessary to obtain an [N]-ary conjunction. *)

Tactic Notation "splits" constr(N) :=
  let N := number_to_nat N in
  splits_tactic N.

(** N-ary Conjunctions Deconstruction *)

(** Underlying implementation of [destructs]. *)

Ltac destructs_conjunction_tactic N T :=
  match N with
  | 2 => destruct T as [? ?]
  | 3 => destruct T as [? [? ?]]
  | 4 => destruct T as [? [? [? ?]]]
  | 5 => destruct T as [? [? [? [? ?]]]]
  | 6 => destruct T as [? [? [? [? [? ?]]]]]
  | 7 => destruct T as [? [? [? [? [? [? ?]]]]]]
  end.

(** [destructs T] allows destructing a term [T] which is a N-ary
    conjunction. It is equivalent to [destruct T as (H1 .. HN)],
    except that it does not require to manually specify N different
    names. *)

Tactic Notation "destructs" constr(T) :=
  let TT := type of T in
  let N := get_term_conjunction_arity TT in
  destructs_conjunction_tactic N T.

(** [destructs N T] is equivalent to [destruct T as (H1 .. HN)],
    except that it does not require to manually specify N different
    names. Remark that it is not restricted to N-ary conjunctions. *)

Tactic Notation "destructs" constr(N) constr(T) :=
  let N := number_to_nat N in
  destructs_conjunction_tactic N T.

(** Proving Goals that are N-ary Disjunctions *)

(** Underlying implementation of [branch]. *)

Ltac branch_tactic K N :=
  match constr:((K,N)) with
  | (_,0) => fail 1
  | (0,_) => fail 1
  | (1,1) => idtac
  | (1,_) => left
  | (S ?K', S ?N') => right; branch_tactic K' N'
  end.

Ltac unfold_goal_until_disjunction :=
  match goal with
  | |- _ \/ _ => idtac
  | _ => progress(unfolds); unfold_goal_until_disjunction
  end.

Ltac get_term_disjunction_arity T :=
  match T with
  | _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(8)
  | _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(7)
  | _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(6)
  | _ \/ _ \/ _ \/ _ \/ _ => constr:(5)
  | _ \/ _ \/ _ \/ _ => constr:(4)
  | _ \/ _ \/ _ => constr:(3)
  | _ \/ _ => constr:(2)
  | _ -> ?T' => get_term_disjunction_arity T'
  | _ => let P := get_head T in
         let T' := eval unfold P in T in
         match T' with
         | T => fail 1
         | _ => get_term_disjunction_arity T'
         end
  end.

Ltac get_goal_disjunction_arity :=
  match goal with |- ?T => get_term_disjunction_arity T end.

(** [branch N] applies to a goal of the form
    [P1 \/ ... \/ PK \/ ... \/ PN] and leaves the goal [PK].
    It only able to unfold the head definition (if there is one),
    but for more complex unfolding one should use the tactic
    [branch K of N]. *)

Tactic Notation "branch" constr(K) :=
  let K := number_to_nat K in
  unfold_goal_until_disjunction;
  let N := get_goal_disjunction_arity in
  branch_tactic K N.

(** [branch K of N] is similar to [branch K] except that the
    arity of the disjunction [N] is given manually, and so this
    version of the tactic is able to unfold definitions.
    In other words, applies to a goal of the form
    [P1 \/ ... \/ PK \/ ... \/ PN] and leaves the goal [PK]. *)

Tactic Notation "branch" constr(K) "of" constr(N) :=
  let N := number_to_nat N in
  let K := number_to_nat K in
  branch_tactic K N.

(** N-ary Disjunction Deconstruction *)

(** Underlying implementation of [branches]. *)

Ltac destructs_disjunction_tactic N T :=
  match N with
  | 2 => destruct T as [? | ?]
  | 3 => destruct T as [? | [? | ?]]
  | 4 => destruct T as [? | [? | [? | ?]]]
  | 5 => destruct T as [? | [? | [? | [? | ?]]]]
  end.

(** [branches T] allows destructing a term [T] which is a N-ary
    disjunction. It is equivalent to [destruct T as [ H1 | .. | HN ] ],
    and produces [N] subgoals corresponding to the [N] possible cases. *)

Tactic Notation "branches" constr(T) :=
  let TT := type of T in
  let N := get_term_disjunction_arity TT in
  destructs_disjunction_tactic N T.

(** [branches N T] is the same as [branches T] except that the arity is
    forced to [N]. This version is useful to unfold definitions
    on the fly. *)

Tactic Notation "branches" constr(N) constr(T) :=
  let N := number_to_nat N in
  destructs_disjunction_tactic N T.

(** [branches] automatically finds a hypothesis [h] that is a disjunction
    and destructs it. *)

Tactic Notation "branches" :=
  match goal with h: _ \/ _ |- _ => branches h end.

(** N-ary Existentials *)

(** [exists T1 ... TN] is a shorthand for [exists T1; ...; exists TN].
    It is intended to prove goals of the form [exist X1 .. XN, P].
    If an argument provided is [__] (double underscore), then an
    evar is introduced. [exists T1 .. TN ___] is equivalent to
    [exists T1 .. TN __ __ __] with as many [__] as possible. *)

Tactic Notation "exists_original" constr(T1) :=
  exists T1.
Tactic Notation "exists" constr(T1) :=
  match T1 with
  | ltac_wild => esplit
  | ltac_wilds => repeat esplit
  | _ => exists T1
  end.
Tactic Notation "exists" constr(T1) constr(T2) :=
  exists T1; exists T2.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) :=
  exists T1; exists T2; exists T3.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4) :=
  exists T1; exists T2; exists T3; exists T4.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) :=
  exists T1; exists T2; exists T3; exists T4; exists T5.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) constr(T6) :=
  exists T1; exists T2; exists T3; exists T4; exists T5; exists T6.

(** For compatibility with Coq syntax, [exists T1, .., TN] is also provided. *)

Tactic Notation "exists" constr(T1) "," constr(T2) :=
  exists T1 T2.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) :=
  exists T1 T2 T3.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) "," constr(T4) :=
  exists T1 T2 T3 T4.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) "," constr(T4) ","
 constr(T5) :=
  exists T1 T2 T3 T4 T5.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) "," constr(T4) ","
 constr(T5) "," constr(T6) :=
  exists T1 T2 T3 T4 T5 T6.

(** The tactic [exists], without arguments, repeats [esplit]
    as many times as there are visible existentials at the
    head of the goal. In there are zero existentials visible,
    the tactic [hnf] is called once. If there are still zero
    existentials visible, the tactic fails.

    To obtain a tactic that supports arbitrary number of
    existentials including the possibility of having zero
    existentials, use [try exists]. *)

Ltac exists_noarg_positive tt :=
  match goal with
  | |- exists _, _ => esplit; try exists_noarg_positive tt
  end.

Ltac exists_noarg tt :=
  match goal with
  | |- exists _, _ => exists_noarg_positive tt
  | _ => hnf; exists_noarg_positive tt
  end.

Tactic Notation "exists" :=
  exists_noarg tt.

Definition def_with_exists (n:nat) : Prop :=
  exists x, x = n.

(** The tactic [exists_nounfold] is similar to [exists],
    except that it does nothing if there are no existentials
    visible in the goal. This tactic may be useful for programming
    other tactics in a robust way. *)

Tactic Notation "exists_nounfold" :=
  try exists_noarg_positive tt.

(** Existentials and Conjunctions in Hypotheses *)

(** [unpack] or [unpack H] destructs conjunctions and existentials in
    all or one hypothesis. *)

Ltac unpack_core :=
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  | H: exists (varname: _), _ |- _ =>
      (* kludge to preserve the name of the quantified variable *)
      let name := fresh varname in
      destruct H as [name ?]
  end.

Ltac unpack_hypothesis H :=
  try match type of H with
  | _ /\ _ =>
      let h1 := fresh "TEMP" in
      let h2 := fresh "TEMP" in
      destruct H as [ h1 h2 ];
      unpack_hypothesis h1;
      unpack_hypothesis h2
  | exists (varname: _), _ =>
      (* kludge to preserve the name of the quantified variable *)
      let name := fresh varname in
      let body := fresh "TEMP" in
      destruct H as [name body];
      unpack_hypothesis body
  end.

Tactic Notation "unpack" :=
  unpack_core.
Tactic Notation "unpack" constr(H) :=
  unpack_hypothesis H.

(* ################################################################# *)
(** * Tactics to Prove Typeclass Instances *)

(** [typeclass] is an automation tactic specialized for finding
    typeclass instances. *)

Tactic Notation "typeclass" :=
  let go _ := eauto with typeclass_instances in
  solve [ go tt | constructor; go tt ].

(** [solve_typeclass] is a simpler version of [typeclass], to use
    in hint tactics for resolving instances *)

Tactic Notation "solve_typeclass" :=
  solve [ eauto with typeclass_instances ].

(* ################################################################# *)
(** * Tactics to Invoke Automation *)

(* ================================================================= *)
(** ** Definitions for Parsing Compatibility *)

Tactic Notation "f_equal" :=
  f_equal.
Tactic Notation "constructor" :=
  constructor.
Tactic Notation "simple" :=
  simpl.

Tactic Notation "split" :=
  split.

Tactic Notation "right" :=
  right.
Tactic Notation "left" :=
  left.

(* ================================================================= *)
(** ** [hint] to Add Hints Local to a Lemma *)

(** [hint E] adds [E] as an hypothesis so that automation can use it.
    Syntax [hint E1,..,EN] is available *)

Tactic Notation "hint" constr(E) :=
  let H := fresh "Hint" in lets H: E.
Tactic Notation "hint" constr(E1) "," constr(E2) :=
  hint E1; hint E2.
Tactic Notation "hint" constr(E1) "," constr(E2) "," constr(E3) :=
  hint E1; hint E2; hint(E3).
Tactic Notation "hint" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) :=
  hint E1; hint E2; hint(E3); hint(E4 ).

(* ================================================================= *)
(** ** [jauto], a New Automation Tactic *)

(** [jauto] is better at [intuition eauto] because it can open existentials
    from the context. In the same time, [jauto] can be faster than
    [intuition eauto] because it does not destruct disjunctions from the
    context. The strategy of [jauto] can be summarized as follows:
    - open all the existentials and conjunctions from the context
    - call esplit and split on the existentials and conjunctions in the goal
    - call eauto. *)

Tactic Notation "jauto" :=
  try solve [ jauto_set; eauto ].

Tactic Notation "jauto_fast" :=
  try solve [ auto | eauto | jauto ].

(** [iauto] is a shorthand for [intuition eauto] *)

Tactic Notation "iauto" := try solve [intuition eauto].

(* ================================================================= *)
(** ** Definitions of Automation Tactics *)

(** The two following tactics defined the default behaviour of
    "light automation" and "strong automation". These tactics
    may be redefined at any time using the syntax [Ltac .. ::= ..]. *)

(** [auto_tilde] is the tactic which will be called each time a symbol
    [~] is used after a tactic. *)

Ltac auto_tilde_default := auto.
Ltac auto_tilde := auto_tilde_default.

(** [auto_star] is the tactic which will be called each time a symbol
    [*] is used after a tactic. *)

Ltac auto_star_default := try solve [ auto | eauto | intuition eauto ].
  (* --todo: should be jauto *)
Ltac auto_star := auto_star_default.

(** [autos~] is a notation for tactic [auto_tilde]. It may be followed
    by lemmas (or proofs terms) which auto will be able to use
    for solving the goal.

    [autos] is an alias for [autos~] *)

Tactic Notation "autos" :=
  auto_tilde.
Tactic Notation "autos" "~" :=
  auto_tilde.
Tactic Notation "autos" "~" constr(E1) :=
  lets: E1; auto_tilde.
Tactic Notation "autos" "~" constr(E1) constr(E2) :=
  lets: E1; autos~ E2.
Tactic Notation "autos" "~" constr(E1) constr(E2) constr(E3) :=
  lets: E1; autos~ E2 E3.
Tactic Notation "autos" "~" constr(E1) constr(E2) constr(E3) constr(E4) :=
  lets: E1; autos~ E2 E3 E4.
Tactic Notation "autos" "~" constr(E1) constr(E2) constr(E3) constr(E4)
 constr(E5):=
  lets: E1; autos~ E2 E3 E4 E5.

(* New syntax using coma *)
Tactic Notation "autos" :=
  auto_tilde.
Tactic Notation "autos" "~" :=
  auto_tilde.
Tactic Notation "autos" "~" constr(E1) :=
  lets: E1; auto_tilde.
Tactic Notation "autos" "~" constr(E1) "," constr(E2) :=
  lets: E1; autos~ E2.
Tactic Notation "autos" "~" constr(E1) "," constr(E2) "," constr(E3) :=
  lets: E1; autos~ E2 E3.
Tactic Notation "autos" "~" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) :=
  lets: E1; autos~ E2 E3 E4.
Tactic Notation "autos" "~" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) ","
 constr(E5):=
  lets: E1; autos~ E2 E3 E4 E5.

(** [autos*] is a notation for tactic [auto_star]. It may be followed
    by lemmas (or proofs terms) which auto will be able to use
    for solving the goal. *)

Tactic Notation "autos" "*" :=
  auto_star.
Tactic Notation "autos" "*" constr(E1) :=
  lets: E1; auto_star.
Tactic Notation "autos" "*" constr(E1) constr(E2) :=
  lets: E1; autos* E2.
Tactic Notation "autos" "*" constr(E1) constr(E2) constr(E3) :=
  lets: E1; autos* E2 E3.
Tactic Notation "autos" "*" constr(E1) constr(E2) constr(E3) constr(E4) :=
  lets: E1; autos* E2 E3 E4.
Tactic Notation "autos" "*" constr(E1) constr(E2) constr(E3) constr(E4)
 constr(E5):=
  lets: E1; autos* E2 E3 E4 E5.

(* New syntax using coma *)

Tactic Notation "autos" "*" :=
  auto_star.
Tactic Notation "autos" "*" constr(E1) :=
  lets: E1; auto_star.
Tactic Notation "autos" "*" constr(E1) "," constr(E2) :=
  lets: E1; autos* E2.
Tactic Notation "autos" "*" constr(E1) "," constr(E2) "," constr(E3) :=
  lets: E1; autos* E2 E3.
Tactic Notation "autos" "*" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) :=
  lets: E1; autos* E2 E3 E4.
Tactic Notation "autos" "*" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) ","
 constr(E5):=
  lets: E1; autos* E2 E3 E4 E5.

(** [auto_false] is a version of [auto] able to spot some contradictions.
    There is an ad-hoc support for goals in [<->]: split is called first.
    [auto_false~] and [auto_false*] are also available. *)

Ltac auto_false_base cont :=
  try solve [
    intros_all; try match goal with |- _ <-> _ => split end;
    solve [ cont tt | intros_all; false; cont tt ] ].

Tactic Notation "auto_false" :=
   auto_false_base ltac:(fun tt => auto).
Tactic Notation "auto_false" "~" :=
   auto_false_base ltac:(fun tt => auto_tilde).
Tactic Notation "auto_false" "*" :=
   auto_false_base ltac:(fun tt => auto_star).

Tactic Notation "dauto" :=
  dintuition eauto.

(* ================================================================= *)
(** ** Parsing for Light Automation *)

(** Any tactic followed by the symbol [~] will have [auto_tilde] called
    on all of its subgoals. Three exceptions:
    - [cuts] and [asserts] only call [auto] on their first subgoal,
    - [apply~] relies on [sapply] rather than [apply],
    - [tryfalse~] is defined as [tryfalse by auto_tilde].

   Some builtin tactics are not defined using tactic notations
   and thus cannot be extended, e.g., [simpl] and [unfold].
   For these, notation such as [simpl~] will not be available. *)

Tactic Notation "equates" "~" constr(E) :=
   equates E; auto_tilde.
Tactic Notation "equates" "~" constr(n1) constr(n2) :=
  equates n1 n2; auto_tilde.
Tactic Notation "equates" "~" constr(n1) constr(n2) constr(n3) :=
  equates n1 n2 n3; auto_tilde.
Tactic Notation "equates" "~" constr(n1) constr(n2) constr(n3) constr(n4) :=
  equates n1 n2 n3 n4; auto_tilde.

Tactic Notation "applys_eq" "~" constr(H) :=
  applys_eq H; auto_tilde.
Tactic Notation "applys_eq" "~" constr(H) constr(E) :=
  applys_eq H E; auto_tilde.
Tactic Notation "applys_eq" "~" constr(H) constr(n1) constr(n2) :=
  applys_eq H n1 n2; auto_tilde.
Tactic Notation "applys_eq" "~" constr(H) constr(n1) constr(n2) constr(n3) :=
  applys_eq H n1 n2 n3; auto_tilde.
Tactic Notation "applys_eq" "~" constr(H) constr(n1) constr(n2) constr(n3) constr(n4) :=
  applys_eq H n1 n2 n3 n4; auto_tilde.

Tactic Notation "apply" "~" constr(H) :=
  sapply H; auto_tilde.

Tactic Notation "destruct" "~" constr(H) :=
  destruct H; auto_tilde.
Tactic Notation "destruct" "~" constr(H) "as" simple_intropattern(I) :=
  destruct H as I; auto_tilde.
Tactic Notation "f_equal" "~" :=
  f_equal; auto_tilde.
Tactic Notation "induction" "~" constr(H) :=
  induction H; auto_tilde.
Tactic Notation "inversion" "~" constr(H) :=
  inversion H; auto_tilde.
Tactic Notation "split" "~" :=
  split; auto_tilde.
Tactic Notation "subst" "~" :=
  subst; auto_tilde.
Tactic Notation "right" "~" :=
  right; auto_tilde.
Tactic Notation "left" "~" :=
  left; auto_tilde.
Tactic Notation "constructor" "~" :=
  constructor; auto_tilde.
Tactic Notation "constructors" "~" :=
  constructors; auto_tilde.

Tactic Notation "false" "~" :=
  false; auto_tilde.
Tactic Notation "false" "~" constr(E) :=
  false_then E ltac:(fun _ => auto_tilde).
Tactic Notation "false" "~" constr(E0) constr(E1) :=
  false~ (>> E0 E1).
Tactic Notation "false" "~" constr(E0) constr(E1) constr(E2) :=
  false~ (>> E0 E1 E2).
Tactic Notation "false" "~" constr(E0) constr(E1) constr(E2) constr(E3) :=
  false~ (>> E0 E1 E2 E3).
Tactic Notation "false" "~" constr(E0) constr(E1) constr(E2) constr(E3) constr(E4) :=
  false~ (>> E0 E1 E2 E3 E4).
Tactic Notation "tryfalse" "~" :=
  try solve [ false~ ].

Tactic Notation "asserts" "~" simple_intropattern(H) ":" constr(E) :=
  asserts H: E; [ auto_tilde | idtac ].
Tactic Notation "asserts" "~" ":" constr(E) :=
  let H := fresh "H" in asserts~ H: E.
Tactic Notation "cuts" "~" simple_intropattern(H) ":" constr(E) :=
  cuts H: E; [ auto_tilde | idtac ].
Tactic Notation "cuts" "~" ":" constr(E) :=
  cuts: E; [ auto_tilde | idtac ].

Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E) :=
  lets I: E; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  lets I: E0 A1; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  lets I: E0 A1 A2; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets I: E0 A1 A2 A3; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets I: E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets I: E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "lets" "~" ":" constr(E) :=
  lets: E; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
 constr(A1) :=
  lets: E0 A1; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
 constr(A1) constr(A2) :=
  lets: E0 A1 A2; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets: E0 A1 A2 A3; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets: E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets: E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E) :=
  forwards I: E; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  forwards I: E0 A1; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards I: E0 A1 A2; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards I: E0 A1 A2 A3; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards I: E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards I: E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "forwards" "~" ":" constr(E) :=
  forwards: E; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
 constr(A1) :=
  forwards: E0 A1; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards: E0 A1 A2; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards: E0 A1 A2 A3; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards: E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards: E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "applys" "~" constr(H) :=
  sapply H; auto_tilde. (*todo?*)
Tactic Notation "applys" "~" constr(E0) constr(A1) :=
  applys E0 A1; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) :=
  applys E0 A1; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) constr(A2) :=
  applys E0 A1 A2; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) constr(A2) constr(A3) :=
  applys E0 A1 A2 A3; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
  applys E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  applys E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "specializes" "~" hyp(H) :=
  specializes H; auto_tilde.
Tactic Notation "specializes" "~" hyp(H) constr(A1) :=
  specializes H A1; auto_tilde.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) :=
  specializes H A1 A2; auto_tilde.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) :=
  specializes H A1 A2 A3; auto_tilde.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) :=
  specializes H A1 A2 A3 A4; auto_tilde.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  specializes H A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "fapply" "~" constr(E) :=
  fapply E; auto_tilde.
Tactic Notation "sapply" "~" constr(E) :=
  sapply E; auto_tilde.

Tactic Notation "logic" "~" constr(E) :=
  logic_base E ltac:(fun _ => auto_tilde).

Tactic Notation "intros_all" "~" :=
  intros_all; auto_tilde.

Tactic Notation "unfolds" "~" :=
  unfolds; auto_tilde.
Tactic Notation "unfolds" "~" constr(F1) :=
  unfolds F1; auto_tilde.
Tactic Notation "unfolds" "~" constr(F1) "," constr(F2) :=
  unfolds F1, F2; auto_tilde.
Tactic Notation "unfolds" "~" constr(F1) "," constr(F2) "," constr(F3) :=
  unfolds F1, F2, F3; auto_tilde.
Tactic Notation "unfolds" "~" constr(F1) "," constr(F2) "," constr(F3) ","
 constr(F4) :=
  unfolds F1, F2, F3, F4; auto_tilde.

Tactic Notation "simple" "~" :=
  simpl; auto_tilde.
Tactic Notation "simple" "~" "in" hyp(H) :=
  simpl in H; auto_tilde.
Tactic Notation "simpls" "~" :=
  simpls; auto_tilde.
Tactic Notation "hnfs" "~" :=
  hnfs; auto_tilde.
Tactic Notation "hnfs" "~" "in" hyp(H) :=
  hnf in H; auto_tilde.
Tactic Notation "substs" "~" :=
  substs; auto_tilde.
Tactic Notation "intro_hyp" "~" hyp(H) :=
  subst_hyp H; auto_tilde.
Tactic Notation "intro_subst" "~" :=
  intro_subst; auto_tilde.
Tactic Notation "subst_eq" "~" constr(E) :=
  subst_eq E; auto_tilde.

Tactic Notation "rewrite" "~" constr(E) :=
  rewrite E; auto_tilde.
Tactic Notation "rewrite" "~" "<-" constr(E) :=
  rewrite <- E; auto_tilde.
Tactic Notation "rewrite" "~" constr(E) "in" hyp(H) :=
  rewrite E in H; auto_tilde.
Tactic Notation "rewrite" "~" "<-" constr(E) "in" hyp(H) :=
  rewrite <- E in H; auto_tilde.

Tactic Notation "rewrites" "~" constr(E) :=
  rewrites E; auto_tilde.
Tactic Notation "rewrites" "~" constr(E) "in" hyp(H) :=
  rewrites E in H; auto_tilde.
Tactic Notation "rewrites" "~" constr(E) "in" "*" :=
  rewrites E in *; auto_tilde.
Tactic Notation "rewrites" "~" "<-" constr(E) :=
  rewrites <- E; auto_tilde.
Tactic Notation "rewrites" "~" "<-" constr(E) "in" hyp(H) :=
  rewrites <- E in H; auto_tilde.
Tactic Notation "rewrites" "~" "<-" constr(E) "in" "*" :=
  rewrites <- E in *; auto_tilde.

Tactic Notation "rewrite_all" "~" constr(E) :=
  rewrite_all E; auto_tilde.
Tactic Notation "rewrite_all" "~" "<-" constr(E) :=
  rewrite_all <- E; auto_tilde.
Tactic Notation "rewrite_all" "~" constr(E) "in" ident(H) :=
  rewrite_all E in H; auto_tilde.
Tactic Notation "rewrite_all" "~" "<-" constr(E) "in" ident(H) :=
  rewrite_all <- E in H; auto_tilde.
Tactic Notation "rewrite_all" "~" constr(E) "in" "*" :=
  rewrite_all E in *; auto_tilde.
Tactic Notation "rewrite_all" "~" "<-" constr(E) "in" "*" :=
  rewrite_all <- E in *; auto_tilde.

Tactic Notation "asserts_rewrite" "~" constr(E) :=
  asserts_rewrite E; auto_tilde.
Tactic Notation "asserts_rewrite" "~" "<-" constr(E) :=
  asserts_rewrite <- E; auto_tilde.
Tactic Notation "asserts_rewrite" "~" constr(E) "in" hyp(H) :=
  asserts_rewrite E in H; auto_tilde.
Tactic Notation "asserts_rewrite" "~" "<-" constr(E) "in" hyp(H) :=
  asserts_rewrite <- E in H; auto_tilde.
Tactic Notation "asserts_rewrite" "~" constr(E) "in" "*" :=
  asserts_rewrite E in *; auto_tilde.
Tactic Notation "asserts_rewrite" "~" "<-" constr(E) "in" "*" :=
  asserts_rewrite <- E in *; auto_tilde.

Tactic Notation "cuts_rewrite" "~" constr(E) :=
  cuts_rewrite E; auto_tilde.
Tactic Notation "cuts_rewrite" "~" "<-" constr(E) :=
  cuts_rewrite <- E; auto_tilde.
Tactic Notation "cuts_rewrite" "~" constr(E) "in" hyp(H) :=
  cuts_rewrite E in H; auto_tilde.
Tactic Notation "cuts_rewrite" "~" "<-" constr(E) "in" hyp(H) :=
  cuts_rewrite <- E in H; auto_tilde.

Tactic Notation "erewrite" "~" constr(E) :=
  erewrite E; auto_tilde.
Tactic Notation "erewrites" "~" constr(E) :=
  erewrites E; auto_tilde.

Tactic Notation "fequal" "~" :=
  fequal; auto_tilde.
Tactic Notation "fequals" "~" :=
  fequals; auto_tilde.
Tactic Notation "pi_rewrite" "~" constr(E) :=
  pi_rewrite E; auto_tilde.
Tactic Notation "pi_rewrite" "~" constr(E) "in" hyp(H) :=
  pi_rewrite E in H; auto_tilde.

Tactic Notation "invert" "~" hyp(H) :=
  invert H; auto_tilde.
Tactic Notation "inverts" "~" hyp(H) :=
  inverts H; auto_tilde.
Tactic Notation "inverts" "~" hyp(E) "as" :=
  inverts E as; auto_tilde.
Tactic Notation "injects" "~" hyp(H) :=
  injects H; auto_tilde.
Tactic Notation "inversions" "~" hyp(H) :=
  inversions H; auto_tilde.

Tactic Notation "cases" "~" constr(E) "as" ident(H) :=
  cases E as H; auto_tilde.
Tactic Notation "cases" "~" constr(E) :=
  cases E; auto_tilde.
Tactic Notation "case_if" "~" :=
  case_if; auto_tilde.
Tactic Notation "case_ifs" "~" :=
  case_ifs; auto_tilde.
Tactic Notation "case_if" "~" "in" hyp(H) :=
  case_if in H; auto_tilde.
Tactic Notation "cases_if" "~" :=
  cases_if; auto_tilde.
Tactic Notation "cases_if" "~" "in" hyp(H) :=
  cases_if in H; auto_tilde.
Tactic Notation "destruct_if" "~" :=
  destruct_if; auto_tilde.
Tactic Notation "destruct_if" "~" "in" hyp(H) :=
  destruct_if in H; auto_tilde.

Tactic Notation "cases'" "~" constr(E) "as" ident(H) :=
  cases' E as H; auto_tilde.
Tactic Notation "cases'" "~" constr(E) :=
  cases' E; auto_tilde.
Tactic Notation "cases_if'" "~" "as" ident(H) :=
  cases_if' as H; auto_tilde.
Tactic Notation "cases_if'" "~" :=
  cases_if'; auto_tilde.

Tactic Notation "decides_equality" "~" :=
  decides_equality; auto_tilde.

Tactic Notation "iff" "~" :=
  iff; auto_tilde.
Tactic Notation "iff" "~" simple_intropattern(I) :=
  iff I; auto_tilde.
Tactic Notation "splits" "~" :=
  splits; auto_tilde.
Tactic Notation "splits" "~" constr(N) :=
  splits N; auto_tilde.

Tactic Notation "destructs" "~" constr(T) :=
  destructs T; auto_tilde.
Tactic Notation "destructs" "~" constr(N) constr(T) :=
  destructs N T; auto_tilde.

Tactic Notation "branch" "~" constr(N) :=
  branch N; auto_tilde.
Tactic Notation "branch" "~" constr(K) "of" constr(N) :=
  branch K of N; auto_tilde.

Tactic Notation "branches" "~" :=
  branches; auto_tilde.
Tactic Notation "branches" "~" constr(T) :=
  branches T; auto_tilde.
Tactic Notation "branches" "~" constr(N) constr(T) :=
  branches N T; auto_tilde.

Tactic Notation "exists" "~" :=
  exists; auto_tilde.
Tactic Notation "exists" "~" constr(T1) :=
  exists T1; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) :=
  exists T1 T2; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) constr(T3) :=
  exists T1 T2 T3; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) constr(T3) constr(T4) :=
  exists T1 T2 T3 T4; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) :=
  exists T1 T2 T3 T4 T5; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) constr(T6) :=
  exists T1 T2 T3 T4 T5 T6; auto_tilde.

Tactic Notation "exists" "~" constr(T1) "," constr(T2) :=
  exists T1 T2; auto_tilde.
Tactic Notation "exists" "~" constr(T1) "," constr(T2) "," constr(T3) :=
  exists T1 T2 T3; auto_tilde.
Tactic Notation "exists" "~" constr(T1) "," constr(T2) "," constr(T3) ","
 constr(T4) :=
  exists T1 T2 T3 T4; auto_tilde.
Tactic Notation "exists" "~" constr(T1) "," constr(T2) "," constr(T3) ","
 constr(T4) "," constr(T5) :=
  exists T1 T2 T3 T4 T5; auto_tilde.
Tactic Notation "exists" "~" constr(T1) "," constr(T2) "," constr(T3) ","
 constr(T4) "," constr(T5) "," constr(T6) :=
  exists T1 T2 T3 T4 T5 T6; auto_tilde.

(* ================================================================= *)
(** ** Parsing for Strong Automation *)

(** Any tactic followed by the symbol [*] will have [auto*] called
    on all of its subgoals. The exceptions to these rules are the
    same as for light automation.

    Exception: use [subs*] instead of [subst*] if you
    import the library [Coq.Classes.Equivalence]. *)

Tactic Notation "equates" "*" constr(E) :=
   equates E; auto_star.
Tactic Notation "equates" "*" constr(n1) constr(n2) :=
  equates n1 n2; auto_star.
Tactic Notation "equates" "*" constr(n1) constr(n2) constr(n3) :=
  equates n1 n2 n3; auto_star.
Tactic Notation "equates" "*" constr(n1) constr(n2) constr(n3) constr(n4) :=
  equates n1 n2 n3 n4; auto_star.

Tactic Notation "applys_eq" "*" constr(H) :=
  applys_eq H; auto_star.
Tactic Notation "applys_eq" "*" constr(H) constr(E) :=
  applys_eq H E; auto_star.
Tactic Notation "applys_eq" "*" constr(H) constr(n1) constr(n2) :=
  applys_eq H n1 n2; auto_star.
Tactic Notation "applys_eq" "*" constr(H) constr(n1) constr(n2) constr(n3) :=
  applys_eq H n1 n2 n3; auto_star.
Tactic Notation "applys_eq" "*" constr(H) constr(n1) constr(n2) constr(n3) constr(n4) :=
  applys_eq H n1 n2 n3 n4; auto_star.

Tactic Notation "apply" "*" constr(H) :=
  sapply H; auto_star.

Tactic Notation "destruct" "*" constr(H) :=
  destruct H; auto_star.
Tactic Notation "destruct" "*" constr(H) "as" simple_intropattern(I) :=
  destruct H as I; auto_star.
Tactic Notation "f_equal" "*" :=
  f_equal; auto_star.
Tactic Notation "induction" "*" constr(H) :=
  induction H; auto_star.
Tactic Notation "inversion" "*" constr(H) :=
  inversion H; auto_star.
Tactic Notation "split" "*" :=
  split; auto_star.
Tactic Notation "subs" "*" :=
  subst; auto_star.
Tactic Notation "subst" "*" :=
  subst; auto_star.
Tactic Notation "right" "*" :=
  right; auto_star.
Tactic Notation "left" "*" :=
  left; auto_star.
Tactic Notation "constructor" "*" :=
  constructor; auto_star.
Tactic Notation "constructors" "*" :=
  constructors; auto_star.

Tactic Notation "false" "*" :=
  false; auto_star.
Tactic Notation "false" "*" constr(E) :=
  false_then E ltac:(fun _ => auto_star).
Tactic Notation "false" "*" constr(E0) constr(E1) :=
  false* (>> E0 E1).
Tactic Notation "false" "*" constr(E0) constr(E1) constr(E2) :=
  false* (>> E0 E1 E2).
Tactic Notation "false" "*" constr(E0) constr(E1) constr(E2) constr(E3) :=
  false* (>> E0 E1 E2 E3).
Tactic Notation "false" "*" constr(E0) constr(E1) constr(E2) constr(E3) constr(E4) :=
  false* (>> E0 E1 E2 E3 E4).
Tactic Notation "tryfalse" "*" :=
  try solve [ false* ].

Tactic Notation "asserts" "*" simple_intropattern(H) ":" constr(E) :=
  asserts H: E; [ auto_star | idtac ].
Tactic Notation "asserts" "*" ":" constr(E) :=
  let H := fresh "H" in asserts* H: E.
Tactic Notation "cuts" "*" simple_intropattern(H) ":" constr(E) :=
  cuts H: E; [ auto_star | idtac ].
Tactic Notation "cuts" "*" ":" constr(E) :=
  cuts: E; [ auto_star | idtac ].

Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E) :=
  lets I: E; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  lets I: E0 A1; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  lets I: E0 A1 A2; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets I: E0 A1 A2 A3; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets I: E0 A1 A2 A3 A4; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets I: E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "lets" "*" ":" constr(E) :=
  lets: E; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
 constr(A1) :=
  lets: E0 A1; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
 constr(A1) constr(A2) :=
  lets: E0 A1 A2; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets: E0 A1 A2 A3; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets: E0 A1 A2 A3 A4; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets: E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E) :=
  forwards I: E; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  forwards I: E0 A1; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards I: E0 A1 A2; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards I: E0 A1 A2 A3; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards I: E0 A1 A2 A3 A4; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards I: E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "forwards" "*" ":" constr(E) :=
  forwards: E; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
 constr(A1) :=
  forwards: E0 A1; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards: E0 A1 A2; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards: E0 A1 A2 A3; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards: E0 A1 A2 A3 A4; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards: E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "applys" "*" constr(H) :=
  sapply H; auto_star. (*todo?*)
Tactic Notation "applys" "*" constr(E0) constr(A1) :=
  applys E0 A1; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) :=
  applys E0 A1; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) constr(A2) :=
  applys E0 A1 A2; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) constr(A2) constr(A3) :=
  applys E0 A1 A2 A3; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
  applys E0 A1 A2 A3 A4; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  applys E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "specializes" "*" hyp(H) :=
  specializes H; auto_star.
Tactic Notation "specializes" "~" hyp(H) constr(A1) :=
  specializes H A1; auto_star.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) :=
  specializes H A1 A2; auto_star.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) :=
  specializes H A1 A2 A3; auto_star.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) :=
  specializes H A1 A2 A3 A4; auto_star.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  specializes H A1 A2 A3 A4 A5; auto_star.

Tactic Notation "fapply" "*" constr(E) :=
  fapply E; auto_star.
Tactic Notation "sapply" "*" constr(E) :=
  sapply E; auto_star.

Tactic Notation "logic" constr(E) :=
  logic_base E ltac:(fun _ => auto_star).

Tactic Notation "intros_all" "*" :=
  intros_all; auto_star.

Tactic Notation "unfolds" "*" :=
  unfolds; auto_star.
Tactic Notation "unfolds" "*" constr(F1) :=
  unfolds F1; auto_star.
Tactic Notation "unfolds" "*" constr(F1) "," constr(F2) :=
  unfolds F1, F2; auto_star.
Tactic Notation "unfolds" "*" constr(F1) "," constr(F2) "," constr(F3) :=
  unfolds F1, F2, F3; auto_star.
Tactic Notation "unfolds" "*" constr(F1) "," constr(F2) "," constr(F3) ","
 constr(F4) :=
  unfolds F1, F2, F3, F4; auto_star.

Tactic Notation "simple" "*" :=
  simpl; auto_star.
Tactic Notation "simple" "*" "in" hyp(H) :=
  simpl in H; auto_star.
Tactic Notation "simpls" "*" :=
  simpls; auto_star.
Tactic Notation "hnfs" "*" :=
  hnfs; auto_star.
Tactic Notation "hnfs" "*" "in" hyp(H) :=
  hnf in H; auto_star.
Tactic Notation "substs" "*" :=
  substs; auto_star.
Tactic Notation "intro_hyp" "*" hyp(H) :=
  subst_hyp H; auto_star.
Tactic Notation "intro_subst" "*" :=
  intro_subst; auto_star.
Tactic Notation "subst_eq" "*" constr(E) :=
  subst_eq E; auto_star.

Tactic Notation "rewrite" "*" constr(E) :=
  rewrite E; auto_star.
Tactic Notation "rewrite" "*" "<-" constr(E) :=
  rewrite <- E; auto_star.
Tactic Notation "rewrite" "*" constr(E) "in" hyp(H) :=
  rewrite E in H; auto_star.
Tactic Notation "rewrite" "*" "<-" constr(E) "in" hyp(H) :=
  rewrite <- E in H; auto_star.

Tactic Notation "rewrites" "*" constr(E) :=
  rewrites E; auto_star.
Tactic Notation "rewrites" "*" constr(E) "in" hyp(H):=
  rewrites E in H; auto_star.
Tactic Notation "rewrites" "*" constr(E) "in" "*":=
  rewrites E in *; auto_star.
Tactic Notation "rewrites" "*" "<-" constr(E) :=
  rewrites <- E; auto_star.
Tactic Notation "rewrites" "*" "<-" constr(E) "in" hyp(H):=
  rewrites <- E in H; auto_star.
Tactic Notation "rewrites" "*" "<-" constr(E) "in" "*":=
  rewrites <- E in *; auto_star.

Tactic Notation "rewrite_all" "*" constr(E) :=
  rewrite_all E; auto_star.
Tactic Notation "rewrite_all" "*" "<-" constr(E) :=
  rewrite_all <- E; auto_star.
Tactic Notation "rewrite_all" "*" constr(E) "in" ident(H) :=
  rewrite_all E in H; auto_star.
Tactic Notation "rewrite_all" "*" "<-" constr(E) "in" ident(H) :=
  rewrite_all <- E in H; auto_star.
Tactic Notation "rewrite_all" "*" constr(E) "in" "*" :=
  rewrite_all E in *; auto_star.
Tactic Notation "rewrite_all" "*" "<-" constr(E) "in" "*" :=
  rewrite_all <- E in *; auto_star.

Tactic Notation "asserts_rewrite" "*" constr(E) :=
  asserts_rewrite E; auto_star.
Tactic Notation "asserts_rewrite" "*" "<-" constr(E) :=
  asserts_rewrite <- E; auto_star.
Tactic Notation "asserts_rewrite" "*" constr(E) "in" hyp(H) :=
  asserts_rewrite E; auto_star.
Tactic Notation "asserts_rewrite" "*" "<-" constr(E) "in" hyp(H) :=
  asserts_rewrite <- E; auto_star.
Tactic Notation "asserts_rewrite" "*" constr(E) "in" "*" :=
  asserts_rewrite E in *; auto_tilde.
Tactic Notation "asserts_rewrite" "*" "<-" constr(E) "in" "*" :=
  asserts_rewrite <- E in *; auto_tilde.

Tactic Notation "cuts_rewrite" "*" constr(E) :=
  cuts_rewrite E; auto_star.
Tactic Notation "cuts_rewrite" "*" "<-" constr(E) :=
  cuts_rewrite <- E; auto_star.
Tactic Notation "cuts_rewrite" "*" constr(E) "in" hyp(H) :=
  cuts_rewrite E in H; auto_star.
Tactic Notation "cuts_rewrite" "*" "<-" constr(E) "in" hyp(H) :=
  cuts_rewrite <- E in H; auto_star.

Tactic Notation "erewrite" "*" constr(E) :=
  erewrite E; auto_star.
Tactic Notation "erewrites" "*" constr(E) :=
  erewrites E; auto_star.

Tactic Notation "fequal" "*" :=
  fequal; auto_star.
Tactic Notation "fequals" "*" :=
  fequals; auto_star.
Tactic Notation "pi_rewrite" "*" constr(E) :=
  pi_rewrite E; auto_star.
Tactic Notation "pi_rewrite" "*" constr(E) "in" hyp(H) :=
  pi_rewrite E in H; auto_star.

Tactic Notation "invert" "*" hyp(H) :=
  invert H; auto_star.
Tactic Notation "inverts" "*" hyp(H) :=
  inverts H; auto_star.
Tactic Notation "inverts" "*" hyp(E) "as" :=
  inverts E as; auto_star.
Tactic Notation "injects" "*" hyp(H) :=
  injects H; auto_star.
Tactic Notation "inversions" "*" hyp(H) :=
  inversions H; auto_star.

Tactic Notation "cases" "*" constr(E) "as" ident(H) :=
  cases E as H; auto_star.
Tactic Notation "cases" "*" constr(E) :=
  cases E; auto_star.
Tactic Notation "case_if" "*" :=
  case_if; auto_star.
Tactic Notation "case_ifs" "*" :=
  case_ifs; auto_star.
Tactic Notation "case_if" "*" "in" hyp(H) :=
  case_if in H; auto_star.
Tactic Notation "cases_if" "*" :=
  cases_if; auto_star.
Tactic Notation "cases_if" "*" "in" hyp(H) :=
  cases_if in H; auto_star.
 Tactic Notation "destruct_if" "*" :=
  destruct_if; auto_star.
Tactic Notation "destruct_if" "*" "in" hyp(H) :=
  destruct_if in H; auto_star.

Tactic Notation "cases'" "*" constr(E) "as" ident(H) :=
  cases' E as H; auto_star.
Tactic Notation "cases'" "*" constr(E) :=
  cases' E; auto_star.
Tactic Notation "cases_if'" "*" "as" ident(H) :=
  cases_if' as H; auto_star.
Tactic Notation "cases_if'" "*" :=
  cases_if'; auto_star.

Tactic Notation "decides_equality" "*" :=
  decides_equality; auto_star.

Tactic Notation "iff" "*" :=
  iff; auto_star.
Tactic Notation "iff" "*" simple_intropattern(I) :=
  iff I; auto_star.
Tactic Notation "splits" "*" :=
  splits; auto_star.
Tactic Notation "splits" "*" constr(N) :=
  splits N; auto_star.

Tactic Notation "destructs" "*" constr(T) :=
  destructs T; auto_star.
Tactic Notation "destructs" "*" constr(N) constr(T) :=
  destructs N T; auto_star.

Tactic Notation "branch" "*" constr(N) :=
  branch N; auto_star.
Tactic Notation "branch" "*" constr(K) "of" constr(N) :=
  branch K of N; auto_star.

Tactic Notation "branches" "*" constr(T) :=
  branches T; auto_star.
Tactic Notation "branches" "*" constr(N) constr(T) :=
  branches N T; auto_star.

Tactic Notation "exists" "*" :=
  exists; auto_star.
Tactic Notation "exists" "*" constr(T1) :=
  exists T1; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) :=
  exists T1 T2; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) :=
  exists T1 T2 T3; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) constr(T4) :=
  exists T1 T2 T3 T4; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) :=
  exists T1 T2 T3 T4 T5; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) constr(T6) :=
  exists T1 T2 T3 T4 T5 T6; auto_star.

Tactic Notation "exists" "*" constr(T1) "," constr(T2) :=
  exists T1 T2; auto_star.
Tactic Notation "exists" "*" constr(T1) "," constr(T2) "," constr(T3) :=
  exists T1 T2 T3; auto_star.
Tactic Notation "exists" "*" constr(T1) "," constr(T2) "," constr(T3) ","
  constr(T4) :=
  exists T1 T2 T3 T4; auto_star.
Tactic Notation "exists" "*" constr(T1) "," constr(T2) "," constr(T3) ","
 constr(T4) "," constr(T5) :=
  exists T1 T2 T3 T4 T5; auto_star.
Tactic Notation "exists" "*" constr(T1) "," constr(T2) "," constr(T3) ","
 constr(T4) "," constr(T5) ","  constr(T6) :=
  exists T1 T2 T3 T4 T5 T6; auto_star.

(* ################################################################# *)
(** * Tactics to Sort Out the Proof Context *)

(* ================================================================= *)
(** ** Hiding Hypotheses *)

(* Implementation *)

Definition ltac_something (P:Type) (e:P) := e.

Notation "'Something'" :=
  (@ltac_something _ _).

Lemma ltac_something_eq : forall (e:Type),
  e = (@ltac_something _ e).
Proof using. auto. Qed.

Lemma ltac_something_hide : forall (e:Type),
  e -> (@ltac_something _ e).
Proof using. auto. Qed.

Lemma ltac_something_show : forall (e:Type),
  (@ltac_something _ e) -> e.
Proof using. auto. Qed.

(** [hide_def x] and [show_def x] can be used to hide/show
    the body of the definition [x]. *)

Tactic Notation "hide_def" hyp(x) :=
  let x' := constr:(x) in
  let T := eval unfold x in x' in
  change T with (@ltac_something _ T) in x.

Tactic Notation "show_def" hyp(x) :=
  let x' := constr:(x) in
  let U := eval unfold x in x' in
  match U with @ltac_something _ ?T =>
    change U with T in x end.

(** [show_def] unfolds [Something] in the goal *)

Tactic Notation "show_def" :=
  unfold ltac_something.
Tactic Notation "show_def" "in" hyp(H) :=
  unfold ltac_something in H.
Tactic Notation "show_def" "in" "*" :=
  unfold ltac_something in *.

(** [hide_defs] and [show_defs] applies to all definitions *)

Tactic Notation "hide_defs" :=
  repeat match goal with H := ?T |- _ =>
    match T with
    | @ltac_something _ _ => fail 1
    | _ => change T with (@ltac_something _ T) in H
    end
  end.

Tactic Notation "show_defs" :=
  repeat match goal with H := (@ltac_something _ ?T) |- _ =>
    change (@ltac_something _ T) with T in H end.

(** [hide_hyp H] replaces the type of [H] with the notation [Something]
    and [show_hyp H] reveals the type of the hypothesis. Note that the
    hidden type of [H] remains convertible the real type of [H]. *)

Tactic Notation "show_hyp" hyp(H) :=
  apply ltac_something_show in H.

Tactic Notation "hide_hyp" hyp(H) :=
  apply ltac_something_hide in H.

(** [hide_hyps] and [show_hyps] can be used to hide/show all hypotheses
    of type [Prop]. *)

Tactic Notation "show_hyps" :=
  repeat match goal with
    H: @ltac_something _ _ |- _ => show_hyp H end.

Tactic Notation "hide_hyps" :=
  repeat match goal with H: ?T |- _ =>
    match type of T with
    | Prop =>
      match T with
      | @ltac_something _ _ => fail 2
      | _ => hide_hyp H
      end
    | _ => fail 1
    end
  end.

(** [hide H] and [show H] automatically select between
    [hide_hyp] or [hide_def], and [show_hyp] or [show_def].
    Similarly [hide_all] and [show_all] apply to all. *)

Tactic Notation "hide" hyp(H) :=
  first [hide_def H | hide_hyp H].

Tactic Notation "show" hyp(H) :=
  first [show_def H | show_hyp H].

Tactic Notation "hide_all" :=
  hide_hyps; hide_defs.

Tactic Notation "show_all" :=
  unfold ltac_something in *.

(** [hide_term E] can be used to hide a term from the goal.
    [show_term] or [show_term E] can be used to reveal it.
    [hide_term E in H] can be used to specify an hypothesis. *)

Tactic Notation "hide_term" constr(E) :=
  change E with (@ltac_something _ E).
Tactic Notation "show_term" constr(E) :=
  change (@ltac_something _ E) with E.
Tactic Notation "show_term" :=
  unfold ltac_something.

Tactic Notation "hide_term" constr(E) "in" hyp(H) :=
  change E with (@ltac_something _ E) in H.
Tactic Notation "show_term" constr(E) "in" hyp(H) :=
  change (@ltac_something _ E) with E in H.
Tactic Notation "show_term" "in" hyp(H) :=
  unfold ltac_something in H.

(** [show_unfold R] unfolds the definition of [R] and
    reveals the hidden definition of R. --todo:test,
    and implement using unfold simply *)
    (* --todo: change "unfolds" *)

Tactic Notation "show_unfold" constr(R1) :=
  unfold R1; show_def.
Tactic Notation "show_unfold" constr(R1) "," constr(R2) :=
  unfold R1, R2; show_def.

(* ================================================================= *)
(** ** Sorting Hypotheses *)

(** [sort] sorts out hypotheses from the context by moving all the
    propositions (hypotheses of type Prop) to the bottom of the context. *)

Ltac sort_tactic :=
  try match goal with H: ?T |- _ =>
  match type of T with Prop =>
    generalizes H; (try sort_tactic); intro
  end end.

Tactic Notation "sort" :=
  sort_tactic.

(* ================================================================= *)
(** ** Clearing Hypotheses *)

(** [clears X1 ... XN] is a variation on [clear] which clears
    the variables [X1]..[XN] as well as all the hypotheses which
    depend on them. Contrary to [clear], it never fails. *)

Tactic Notation "clears" ident(X1) :=
  let rec doit _ :=
  match goal with
  | H:context[X1] |- _ => clear H; try (doit tt)
  | _ => clear X1
  end in doit tt.
Tactic Notation "clears" ident(X1) ident(X2) :=
  clears X1; clears X2.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) :=
  clears X1; clears X2; clears X3.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4) :=
  clears X1; clears X2; clears X3; clears X4.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4)
 ident(X5) :=
  clears X1; clears X2; clears X3; clears X4; clears X5.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4)
 ident(X5) ident(X6) :=
  clears X1; clears X2; clears X3; clears X4; clears X5; clears X6.

(** [clears] (without any argument) clears all the unused variables
    from the context. In other words, it removes any variable
    which is not a proposition (i.e. not of type Prop) and which
    does not appear in another hypothesis nor in the goal. *)
  (* --todo: rename to clears_var ? *)

Ltac clears_tactic :=
  match goal with H: ?T |- _ =>
  match type of T with
  | Prop => generalizes H; (try clears_tactic); intro
  | ?TT => clear H; (try clears_tactic)
  | ?TT => generalizes H; (try clears_tactic); intro
  end end.

Tactic Notation "clears" :=
  clears_tactic.

(** [clears_all] clears all the hypotheses from the context
    that can be cleared. It leaves only the hypotheses that
    are mentioned in the goal. *)

Ltac clears_or_generalizes_all_core :=
  repeat match goal with H: _ |- _ =>
           first [ clear H | generalizes H] end.

Tactic Notation "clears_all" :=
  generalize ltac_mark;
  clears_or_generalizes_all_core;
  intro_until_mark.

(** [clears_but H1 H2 .. HN] clears all hypotheses except the
    one that are mentioned and those that cannot be cleared. *)

Ltac clears_but_core cont :=
  generalize ltac_mark;
  cont tt;
  clears_or_generalizes_all_core;
  intro_until_mark.

Tactic Notation "clears_but" :=
  clears_but_core ltac:(fun _ => idtac).
Tactic Notation "clears_but" ident(H1) :=
  clears_but_core ltac:(fun _ => gen H1).
Tactic Notation "clears_but" ident(H1) ident(H2) :=
  clears_but_core ltac:(fun _ => gen H1 H2).
Tactic Notation "clears_but" ident(H1) ident(H2) ident(H3) :=
  clears_but_core ltac:(fun _ => gen H1 H2 H3).
Tactic Notation "clears_but" ident(H1) ident(H2) ident(H3) ident(H4) :=
  clears_but_core ltac:(fun _ => gen H1 H2 H3 H4).
Tactic Notation "clears_but" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5) :=
  clears_but_core ltac:(fun _ => gen H1 H2 H3 H4 H5).

Lemma demo_clears_all_and_clears_but :
  forall x y:nat, y < 2 -> x = x -> x >= 2 -> x < 3 -> True.
Proof using.
  introv M1 M2 M3. dup 6.
  (* [clears_all] clears all hypotheses. *)
  clears_all. auto.
  (* [clears_but H] clears all but [H] *)
  clears_but M3. auto.
  clears_but y. auto.
  clears_but x. auto.
  clears_but M2 M3. auto.
  clears_but x y. auto.
Qed.

(** [clears_last] clears the last hypothesis in the context.
    [clears_last N] clears the last [N] hypotheses in the context. *)

Tactic Notation "clears_last" :=
  match goal with H: ?T |- _ => clear H end.

Ltac clears_last_base N :=
  match number_to_nat N with
  | 0 => idtac
  | S ?p => clears_last; clears_last_base p
  end.

Tactic Notation "clears_last" constr(N) :=
  clears_last_base N.

(* ################################################################# *)
(** * Tactics for Development Purposes *)

(* ================================================================= *)
(** ** Skipping Subgoals *)

Tactic Notation "skip" :=
  admit.

(** [demo] is like [admit] but it documents the fact that admit is intended *)

Tactic Notation "demo" :=
  skip.

(** [admits H: T] adds an assumption named [H] of type [T] to the
    current context, blindly assuming that it is true.
    [admit: T] is another possible syntax.
    Note that H may be an intro pattern. *)

Tactic Notation "admits" simple_intropattern(I) ":" constr(T) :=
  asserts I: T; [ skip | ].
Tactic Notation "admits" ":" constr(T) :=
  let H := fresh "TEMP" in admits H: T.
Tactic Notation "admits" "~" ":" constr(T) :=
  admits: T; auto_tilde.
Tactic Notation "admits" "*" ":" constr(T) :=
  admits: T; auto_star.

(** [admit_cuts T] simply replaces the current goal with [T]. *)

Tactic Notation "admit_cuts" constr(T) :=
  cuts: T; [ skip | ].

(** [admit_goal H] applies to any goal. It simply assumes
    the current goal to be true. The assumption is named "H".
    It is useful to set up proof by induction or coinduction.
    Syntax [admit_goal] is also accepted.*)

Tactic Notation "admit_goal" ident(H) :=
  match goal with |- ?G => admits H: G end.

Tactic Notation "admit_goal" :=
  let IH := fresh "IH" in admit_goal IH.

(** [admit_rewrite T] can be applied when [T] is an equality.
    It blindly assumes this equality to be true, and rewrite it in
    the goal. *)

Tactic Notation "admit_rewrite" constr(T) :=
  let M := fresh "TEMP" in admits M: T; rewrite M; clear M.

(** [admit_rewrite T in H] is similar as [admit_rewrite], except that
    it rewrites in hypothesis [H]. *)

Tactic Notation "admit_rewrite" constr(T) "in" hyp(H) :=
  let M := fresh "TEMP" in admits M: T; rewrite M in H; clear M.

(** [admit_rewrites_all T] is similar as [admit_rewrite], except that
    it rewrites everywhere (goal and all hypotheses). *)

Tactic Notation "admit_rewrite_all" constr(T) :=
  let M := fresh "TEMP" in admits M: T; rewrite_all M; clear M.

(** [forwards_nounfold_admit_sides_then E ltac:(fun K => ..)]
    is like [forwards: E] but it provides the resulting term
    to a continuation, under the name [K], and it admits
    any side-condition produced by the instantiation of [E],
    using the [skip] tactic. *)

Inductive ltac_goal_to_discard := ltac_goal_to_discard_intro.

Ltac forwards_nounfold_admit_sides_then S cont :=
  let MARK := fresh "TEMP" in
  generalize ltac_goal_to_discard_intro;
  intro MARK;
  forwards_nounfold_then S ltac:(fun K =>
    clear MARK;
    cont K);
  match goal with
  | MARK: ltac_goal_to_discard |- _ => skip
  | _ => idtac
  end.


(* ################################################################# *)
(** * Compatibility with standard library *)

(** The module [Program] contains definitions that conflict with the
    current module. If you import [Program], either directly or indirectly
    (e.g. through [Setoid] or [ZArith]), you will need to import the
    compability definitions through the top-level command:
    [Import LibTacticsCompatibility]. *)

Module LibTacticsCompatibility.
  Tactic Notation "apply" "*" constr(H) :=
    sapply H; auto_star.
  Tactic Notation "subst" "*" :=
    subst; auto_star.
End LibTacticsCompatibility.

Open Scope nat_scope.


(* 2023-07-06 15:50 *)

End BusyCoq_LibTactics.
Export BusyCoq_LibTactics.
(* LibTactics.v sets Implicit Arguments for its own definitions only. *)
Unset Implicit Arguments.

(* ==================================================================================================== *)
(*                busycoq/verify/Helper.v  (commit bd2e36f, MIT licence, see the header)                *)
(* ==================================================================================================== *)

Module BusyCoq_Helper.

(** * Various generic lemmas that aren't present in the standard library *)

Import Coq.Bool.Bool.
Import Coq.Lists.List. Import ListNotations.
Import Coq.Lists.Streams.
Import Coq.micromega.Lia.
Import Coq.micromega.ZifyClasses.
Import Coq.PArith.BinPos Coq.PArith.Pnat.
Import Coq.NArith.BinNat Coq.NArith.Nnat.
Import Coq.ZArith.ZArith. Import Nat.
Export BusyCoq_LibTactics.
Set Default Goal Selector "!".

(* We are currently in a deprecation cycle where this gets changed
   from [auto with *] to [auto]. Opt in to silence the warning. *)
Ltac Tauto.intuition_solver ::= auto.

(* sig *)
Notation "[: x :]" := (exist _ x _).

(* sumbool *)
Notation Yes := (left _ _).
Notation No := (right _ _).
Notation Reduce x := (if x then Yes else No).
Notation "a && b" := (if a then b else No).

(* sumor *)
Notation "!!" := (inright _).
Notation "[|| x ||]" := (inleft [: x :]).
Notation "'bind' x <- a ; b" := (match a with | [|| x ||] => b | !! => No end)
  (right associativity, at level 60, x pattern).
Notation "'bind' x <-- a ; b" := (match a with | [|| x ||] => b | !! => !! end)
  (right associativity, at level 60, x pattern).

Lemma Cons_unfold : forall A (xs : Stream A),
  xs = Cons (hd xs) (tl xs).
Proof.
  introv. destruct xs. reflexivity.
Qed.

Lemma const_unfold : forall T (x : T),
  const x = Cons x (const x).
Proof.
  introv.
  rewrite Cons_unfold at 1.
  reflexivity.
Qed.

Fixpoint lpow {A} (l : list A) (n : nat) : list A :=
  match n with
  | O => []
  | S n => l ++ lpow l n
  end.

Notation "l ^^ n" := (lpow l n) (at level 20).

Lemma lpow_shift : forall {A} (xs : list A) n,
  xs^^n ++ xs = xs ++ xs^^n.
Proof.
  induction n.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite <- app_assoc, IHn.
    reflexivity.
Qed.

Lemma lpow_add : forall A n m (xs : list A),
  xs^^(n + m) = xs^^n ++ xs^^m.
Proof.
  induction n; introv.
  - reflexivity.
  - simpl. rewrite IHn.
    rewrite app_assoc. reflexivity.
Qed.

Lemma app_cons_r : forall {A} xs (x : A) ys,
  xs ++ x :: ys = (xs ++ [x]) ++ ys.
Proof.
  induction xs.
  - reflexivity.
  - introv. simpl.
    rewrite <- IHxs. reflexivity.
Qed.

Lemma skipn_add : forall {A} n m (xs : list A),
  skipn (n + m) xs = skipn m (skipn n xs).
Proof.
  induction n.
  - reflexivity.
  - destruct xs.
    + repeat rewrite skipn_nil. reflexivity.
    + apply IHn.
Qed.

#[export] Hint Rewrite firstn_nil skipn_nil skipn_all firstn_all
  firstn_app_2 : list.

(** We define our own [reflect] in [Prop] instead of [Set],
    as we don't want it to occur in the extracted programs. *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

#[global]
Hint Constructors reflect : core.

Lemma reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  introv H. destruct H; intuition discriminate.
Qed.

Lemma iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  destr_bool; constructor; intuition discriminate.
Qed.

Lemma reflect_sym : forall A (x y : A) b,
  reflect (x = y) b -> reflect (y = x) b.
Proof.
  introv H. destruct H; intuition.
Qed.

Lemma reflect_andb : forall P Q p q,
  reflect P p ->
  reflect Q q ->
  reflect (P /\ Q) (p && q).
Proof.
  introv H1 H2. destruct H1, H2; constructor; intuition.
Qed.

Fixpoint Str_app {A} (xs : list A) (ys : Stream A) : Stream A :=
  match xs with
  | [] => ys
  | x :: xs => Cons x (Str_app xs ys)
  end.

(** Notation for tapes *)
Notation "s >> r" := (Cons s r) (at level 25, right associativity).
Notation "l << s" := (Cons s l) (at level 24, left associativity, only parsing).

Notation "s :> r" := (s :: r) (at level 25, right associativity, only parsing).
Notation "l <: s" := (s :: l) (at level 24, left associativity, only parsing).

Notation "xs +> r" := (xs ++ r) (at level 25, right associativity, only parsing).
Notation "l <+ xs" := (xs ++ l) (at level 24, left associativity, only parsing).

Notation "xs *> r" := (Str_app xs r) (at level 25, right associativity).
Notation "l <* xs" := (Str_app xs l) (at level 24, left associativity, only parsing).

Notation "< [ ]" := nil (only parsing).
Notation "< [ x ; .. ; y ]" := (cons y .. (cons x []) ..) (only parsing).

Lemma Str_app_assoc {A} (xs ys : list A) (zs : Stream A) :
  (xs ++ ys) *> zs = xs *> ys *> zs.
Proof.
  induction xs.
  - reflexivity.
  - simpl. rewrite IHxs. reflexivity.
Qed.

(** Strong induction principles, because the stdlib ones are incomplete
    and I can't get them to work. *)
Lemma strong_induction : forall (P : nat -> Prop),
  (forall n, (forall k, k < n -> P k) -> P n) ->
  forall n, P n.
Proof.
  introv H. introv.
  enough (H' : forall k, k <= n -> P k).
  { apply H'. constructor. }
  induction n; introv G.
  - inverts G. apply H. introv G. inverts G.
  - inverts G.
    + apply H. introv G. apply IHn. lia.
    + auto.
Qed.

Lemma N_strong_induction : forall (P : N -> Prop),
  (forall n, (forall k, (k < n)%N -> P k) -> P n) ->
  forall n, P n.
Proof.
  introv H.
  assert (G: forall n : nat, P (N.of_nat n)).
  { induction n using strong_induction.
    apply H. introv G.
    replace k with (N.of_nat (N.to_nat k))
      by apply N2Nat.id.
    apply H0. lia. }
  introv.
  replace n with (N.of_nat (N.to_nat n))
    by apply N2Nat.id.
  apply G.
Qed.

Lemma positive_strong_induction : forall (P : positive -> Prop),
  (forall n, (forall k, (k < n)%positive -> P k) -> P n) ->
  forall n, P n.
Proof.
  intros P H n.
  replace n with (N.succ_pos (Pos.pred_N n)) by lia.
  apply N_strong_induction with (P := fun n => P (N.succ_pos n)).
  clear n. intros n IH.
  apply H. intros k H'. specialize (IH (Pos.pred_N k)).
  replace (N.succ_pos (Pos.pred_N k)) with k in IH by lia.
  apply IH. lia.
Qed.

(* Heterogenous addition *)
Definition het_add (a : N) (b : positive) : positive :=
  match a with
  | N0 => b
  | Npos a => a + b
  end.

Notation "a :+ b" := (het_add a b)  (at level 50, left associativity).

Lemma het_add_Z : forall a b, Z.pos (a :+ b) = (Z.of_N a + Z.pos b)%Z.
Proof.
  introv. destruct a; unfold ":+"; lia.
Qed.

#[global] Instance Op_het_add : BinOp het_add :=
  { TBOp := Z.add; TBOpInj := het_add_Z }.
Add Zify BinOp Op_het_add.

Lemma het_add_succ_l : forall a b, N.succ a :+ b = Pos.succ (a :+ b).
Proof. lia. Qed.

(* Powers of 2%positive with a nice computational behavior *)
Fixpoint pow2' (k : nat) : positive :=
  match k with
  | O => 1
  | S k => (pow2' k)~0
  end.

Definition pow2 (k : nat) : N := Npos (pow2' k).

Arguments pow2 _ : simpl never.

Lemma pow2_S : forall k,
  pow2 (S k) = N.double (pow2 k).
Proof. introv. unfold pow2. simpl. lia. Qed.

Lemma pow2_gt0 : forall k, (pow2 k > 0)%N.
Proof. unfold pow2. lia. Qed.

Lemma pow2_add : forall n m,
  (pow2' (n + m) = pow2' n * pow2' m)%positive.
Proof.
  introv. induction n; simpl pow2' in *; lia.
Qed.

(** Make [lia] understand [div2] *)
Lemma div2_zify : forall x,
  x = 2 * (div2 x) \/ x = 2 * (div2 x) + 1.
Proof.
  intros.
  repeat rewrite <- double_twice.
  destruct (Even_or_Odd x) as [H | H].
  - apply Even_double in H. lia.
  - apply Odd_double in H. lia.
Qed.

#[global] Instance Op_nat_div2 : UnOp div2 :=
  { TUOp x := (x / 2)%Z;
    TUOpInj x := ltac:(now rewrite div2_div, Nat2Z.inj_div) }.
Add Zify UnOp Op_nat_div2.

(* Make [lia]/[nia] more powerful *)
Lemma length_gt0_if_not_nil : forall A (xs : list A),
  [] <> xs -> length xs <> 0.
Proof. introv H Hlen. apply length_zero_iff_nil in Hlen. auto. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_pre_hook ::=
  unfold pow2 in *; repeat rewrite pow2_add in *; simpl pow2' in *;
  lazymatch goal with
  | H: [] <> _ |- _ => apply length_gt0_if_not_nil in H
  | H: [] = _ -> False |- _ => apply length_gt0_if_not_nil in H
  | _ => idtac
  end.

Section StripPrefix.
  Variable A : Type.
  Variable eqb : forall (a b : A), {a = b} + {a <> b}.

Program Fixpoint strip_prefix (xs ys : list A) : {zs | ys = xs ++ zs} + {True} :=
  match xs, ys with
  | [], ys => [|| ys ||]
  | _, [] => !!
  | x :: xs, y :: ys =>
    if eqb x y then
      match strip_prefix xs ys with
      | [|| zs ||] => [|| zs ||]
      | !! => !!
      end
    else
      !!
  end.
End StripPrefix.

Arguments strip_prefix {A} eqb !xs !ys.

End BusyCoq_Helper.
Export BusyCoq_Helper.

(* ==================================================================================================== *)
(*                  busycoq/verify/TM.v  (commit bd2e36f, MIT licence, see the header)                  *)
(* ==================================================================================================== *)

Module BusyCoq_TM.

(** * TM: Definition of Turing Machines *)

Import Coq.Bool.Sumbool.
Import Coq.Lists.List. Export ListNotations.
Import Coq.Lists.Streams.
Import Coq.Arith.PeanoNat.
Import Coq.micromega.Lia.
Export BusyCoq_Helper.
Set Default Goal Selector "!".

(** The direction a Turing machine can step in. *)
(* Textual change in this inlined file: the constructors are named St_L, St_R behind the abbreviations L, R, for
   the reason given at [state] below (the original proofs rely on `intros` naming a binder L or R as L or R). *)
Inductive dir : Type := St_L | St_R.
Notation L := St_L.
Notation R := St_R.

(** We parametrize over... *)
Module Type Ctx.
  (** the type of states [Q]; *)
  Parameter Q : Type.
  (** the type of tape symbols [Sym]; *)
  Parameter Sym : Type.
  (** the starting state [q0]; *)
  Parameter q0 : Q.
  (** and the blank symbol [s0]. *)
  Parameter s0 : Sym.

  (** during enumeration, we also want: *)
  (** distinguished non-starting state *)
  Parameter q1 : Q.
  Parameter q0_neq_q1 : q0 <> q1.

  (** distinguished non-blank symbol *)
  Parameter s1 : Sym.
  Parameter s0_neq_s1 : s0 <> s1.

  (** Moreover we want decidable equality for [Q] and [Sym]. *)
  Parameter eqb_q : forall (a b : Q), {a = b} + {a <> b}.
  Parameter eqb_sym : forall (a b : Sym), {a = b} + {a <> b}.

  (** It is also useful, in some situations, to be able to enumerate
      all the symbols and states. *)
  Parameter all_qs : list Q.
  Parameter all_qs_spec : forall a, In a all_qs.
  Parameter all_syms : list Sym.
  Parameter all_syms_spec : forall a, In a all_syms.
End Ctx.

Module TM (Ctx : Ctx).
  Export Ctx.

#[export] Hint Resolve all_qs_spec all_syms_spec : core.

(** A Turing machine is a function mapping each [(state, symbol)] pair
    to one of

    - [None], in which case the machine halts;
    - [Some (s, d, q)], in which case the machine writes [s] on the tape,
      moves in the direction specified by [d], and transitions to state [q].

*)
Definition TM : Type := Q * Sym -> option (Sym * dir * Q).

Notation side := (Stream Sym).

(** The state of the tape is represented abstractly as a tuple [(l, s, r)],
    where [v] is the symbol under the head, while [l] and [r] are infinite
    streams of symbols on the left and right side of the head, respectively. *)
Notation tape := (side * Sym * side)%type.

(** We define a notation for tapes, evocative of a turing machine's head
    hovering over a particular symbol. **)
Notation "l {{ s }} r" := (l, s, r)
  (at level 30, s at next level, only parsing).

Local Example tape_ex (a b c d e : Sym) : tape :=
  const s0 << a << b {{c}} d >> e >> const s0.

(** Helper functions for moving the tape head: *)
Definition move_left (t : tape) : tape :=
  match t with
  | l {{s}} r => tl l {{hd l}} s >> r
  end.

Definition move_right (t : tape) : tape :=
  match t with
  | l {{s}} r => l << s {{hd r}} tl r
  end.

(** Notation for the configuration of a machine. Note that the position
    of the head within the tape is implicit, since the tape is centered
    at the head. *)
Notation "q ;; t" := (q, t) (at level 35, only parsing).

(** For the directed head formulation, we use the following: *)
Notation "l <{{ q }} r" := (q;; tl l {{hd l}} r)  (at level 30, q at next level).
Notation "l {{ q }}> r" := (q;; l {{hd r}} tl r)  (at level 30, q at next level).

(** The small-step semantics of Turing machines: *)
Reserved Notation "c -[ tm ]-> c'" (at level 40).

Inductive step (tm : TM) : Q * tape -> Q * tape -> Prop :=
  | step_left q q' s s' l r :
    tm (q, s) = Some (s', L, q') ->
    q;; l {{s}} r -[ tm ]-> q';; (move_left (l {{s'}} r))
  | step_right q q' s s' l r :
    tm (q, s) = Some (s', R, q') ->
    q;; l {{s}} r -[ tm ]-> q';; (move_right (l {{s'}} r))

  where "c -[ tm ]-> c'" := (step tm c c').

Arguments step_left {tm q q' s s' l r}.
Arguments step_right {tm q q' s s' l r}.

#[export] Hint Constructors step : core.

(** If we have an assumption of the form [tm (q, s) = Some (s', d, q')],
   perform case analysis on [d]. *)
Ltac destruct_dir tm q s :=
  lazymatch goal with
  | H: tm (q, s) = Some (?s', ?d, ?q') |- _ =>
    lazymatch d with
    | L => fail
    | R => fail
    | _ => destruct d
    end
  end.

Local Hint Extern 1 =>
  match goal with
  | |- context [?q;; _ {{?s}} _ -[ ?tm ]-> _] => destruct_dir tm q s
  end : core.

(** Executing a specified number of steps: *)
Reserved Notation "c -[ tm ]->> n / c'" (at level 40, n at next level).

Inductive multistep (tm : TM) : nat -> Q * tape -> Q * tape -> Prop :=
  | multistep_0 c : c -[ tm ]->> 0 / c
  | multistep_S n c c' c'' :
    c  -[ tm ]->  c' ->
    c' -[ tm ]->> n / c'' ->
    c  -[ tm ]->> S n / c''

  where "c -[ tm ]->> n / c'" := (multistep tm n c c').

#[export] Hint Constructors multistep : core.

Local Hint Extern 1 =>
  lazymatch goal with
  | H: _ -[ _ ]->> S _ / _ |- _ => inverts H
  | H: _ -[ _ ]->> O / _ |- _ => inverts H
  end : core.

(** Executing an unspecified number of steps (the "eventually
    reaches" relation): *)
Reserved Notation "c -[ tm ]->* c'" (at level 40).

Inductive evstep (tm : TM) : Q * tape -> Q * tape -> Prop :=
  | evstep_refl c : c -[ tm ]->* c
  | evstep_step c c' c'' :
    c  -[ tm ]->  c'  ->
    c' -[ tm ]->* c'' ->
    c  -[ tm ]->* c''

  where "c -[ tm ]->* c'" := (evstep tm c c').

#[export] Hint Constructors evstep : core.

(** Executing an unspecified, but non-zero number of steps: *)
Reserved Notation "c -[ tm ]->+ c'" (at level 40).

Inductive progress (tm : TM) : Q * tape -> Q * tape -> Prop :=
  | progress_base c c' :
    c -[ tm ]->  c' ->
    c -[ tm ]->+ c'
  | progress_step c c' c'' :
    c  -[ tm ]->  c'  ->
    c' -[ tm ]->+ c'' ->
    c  -[ tm ]->+ c''

  where "c -[ tm ]->+ c'" := (progress tm c c').

Arguments progress_base {tm c c'}.
Arguments progress_step {tm c c' c''}.

#[export] Hint Constructors progress : core.

(* alternative definition for [progress] *)
Lemma progress_intro : forall tm c c' c'',
  c  -[ tm ]->  c'  ->
  c' -[ tm ]->* c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2. generalize dependent c. induction H2; eauto.
Qed.

(** The Turing machine has halted if [tm (q, s)] returns [None]. *)
Definition halted (tm : TM) (c : Q * tape) : Prop :=
  match c with
  | (q, l {{s}} r) => tm (q, s) = None
  end.

(** The initial configuration of the machine *)
Definition tape0 : tape := const s0 {{s0}} const s0.
Definition c0 : Q * tape := q0;; tape0.

(** A Turing machine halts if it eventually reaches a halting configuration. *)
Definition halts_in (tm : TM) (c : Q * tape) (n : nat) :=
  exists ch, c -[ tm ]->> n / ch /\ halted tm ch.

Definition halts (tm : TM) (c0 : Q * tape) :=
  exists n, halts_in tm c0 n.

#[export] Hint Unfold halts halts_in : core.

Lemma move_left_tape0 :
  move_left tape0 = tape0.
Proof.
  unfold tape0, move_left.
  rewrite <- const_unfold.
  reflexivity.
Qed.

Lemma move_right_tape0 :
  move_right tape0 = tape0.
Proof.
  unfold tape0, move_right.
  rewrite <- const_unfold.
  reflexivity.
Qed.

#[export] Hint Rewrite move_left_tape0 move_right_tape0 : tape.

(** We prove that the "syntactic" notion of [halted] corresponds
    to the behavior of [step]. *)
Lemma halted_no_step : forall tm c c',
  halted tm c ->
  ~ c -[ tm ]-> c'.
Proof.
  introv Hhalted Hstep.
  inverts Hstep; congruence.
Qed.

Lemma no_halted_step : forall tm c,
  ~ halted tm c ->
  exists c',
  c -[ tm ]-> c'.
Proof.
  introv Hhalted.
  destruct c as [q [[l s] r]].
  destruct (tm (q, s)) as [[[s' d] q'] |] eqn:E.
  - (* tm (q, s) = Some (s', d, q') *)
    eauto 6.
  - (* tm (q, s) = None *)
    congruence.
Qed.

(** Other useful lemmas: *)
Lemma step_deterministic : forall tm c c' c'',
  c -[ tm ]-> c'  ->
  c -[ tm ]-> c'' ->
  c' = c''.
Proof.
  introv H1 H2.
  inverts H1; inverts H2; congruence.
Qed.

Ltac step_deterministic :=
  lazymatch goal with
  | H1: ?c -[ ?tm ]-> ?c',
    H2: ?c -[ ?tm ]-> ?c''
    |- _ =>
    pose proof (step_deterministic tm c c' c'' H1 H2); subst c''; clear H2
  end.

Local Hint Extern 1 => step_deterministic : core.

Lemma multistep_trans : forall tm n m c c' c'',
  c  -[ tm ]->> n / c' ->
  c' -[ tm ]->> m / c'' ->
  c  -[ tm ]->> (n + m) / c''.
Proof.
  introv H1 H2.
  induction H1; simpl; eauto.
Qed.

Lemma multistep_deterministic : forall tm n c c' c'',
  c -[ tm ]->> n / c'  ->
  c -[ tm ]->> n / c'' ->
  c' = c''.
Proof.
  introv H1 H2.
  induction H1; inverts H2; auto.
Qed.

Ltac multistep_deterministic :=
  lazymatch goal with
  | H1: ?c -[ ?tm ]->> ?n / ?c',
    H2: ?c -[ ?tm ]->> ?n / ?c''
    |- _ =>
    pose proof (multistep_deterministic tm n c c' c'' H1 H2); subst c''; clear H2
  end.

Local Hint Extern 1 => multistep_deterministic : core.

Ltac deterministic := repeat (step_deterministic || multistep_deterministic).

Lemma multistep_last : forall tm n c c'',
  c -[ tm ]->> S n / c'' ->
  exists c', c -[ tm ]->> n / c' /\ c' -[ tm ]-> c''.
Proof.
  induction n; introv H; inverts H as H1 H2.
  - eauto.
  - apply IHn in H2. destruct H2 as [cmid [H2 H3]].
    eauto.
Qed.

Lemma evstep_one : forall {tm c c'},
  c -[ tm ]->  c' ->
  c -[ tm ]->* c'.
Proof. eauto. Qed.

Lemma evstep_trans : forall tm c c' c'',
  c  -[ tm ]->* c'  ->
  c' -[ tm ]->* c'' ->
  c  -[ tm ]->* c''.
Proof.
  introv H1 H2. induction H1; eauto.
Qed.

Lemma halts_in_S : forall tm c c' n,
  halts_in tm c' n ->
  c -[ tm ]-> c' ->
  halts_in tm c (S n).
Proof.
  introv Hhalts Hstep.
  destruct Hhalts as [ch [Hrun Hhalted]].
  eauto.
Qed.

#[export] Hint Resolve halts_in_S : core.

Lemma halts_step : forall tm c c',
  halts tm c' ->
  c -[ tm ]-> c' ->
  halts tm c.
Proof.
  introv H Hstep. destruct H. eauto.
Qed.

#[export] Hint Resolve halts_step : core.

Lemma halts_multistep : forall tm c c' n,
  halts tm c' ->
  c -[ tm ]->> n / c' ->
  halts tm c.
Proof.
  introv Hhalts Hsteps.
  induction Hsteps; eauto.
Qed.

#[export] Hint Resolve halts_multistep : core.

Lemma halted_halts :
  forall tm c,
  halted tm c ->
  halts tm c.
Proof. eauto 6. Qed.

#[export] Hint Immediate halted_halts : core.

Lemma progress_trans :
  forall tm c c' c'',
  c  -[ tm ]->+ c'  ->
  c' -[ tm ]->+ c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2. induction H1; eauto.
Qed.

Lemma multistep_progress :
  forall tm n c c',
  c -[ tm ]->> S n / c' ->
  c -[ tm ]->+ c'.
Proof.
  induction n; introv H; inverts H; eauto.
Qed.

#[export] Hint Resolve multistep_progress : core.

Lemma progress_multistep :
  forall tm c c',
  c -[ tm ]->+ c' ->
  exists n,
  c -[ tm ]->> S n / c'.
Proof.
  introv H. induction H.
  - eauto.
  - destruct IHprogress as [n IH].
    eauto.
Qed.

Lemma without_counter :
  forall tm n c c',
  c -[ tm ]->> n / c' ->
  c -[ tm ]->* c'.
Proof.
  introv H. induction H; eauto.
Qed.

Lemma with_counter :
  forall {tm c c'},
  c -[ tm ]->* c' ->
  exists n, c -[ tm ]->> n / c'.
Proof.
  introv H. induction H.
  - eauto.
  - destruct IHevstep as [n IH].
    eauto.
Qed.

Lemma evstep_progress :
  forall tm c c',
  c -[ tm ]->* c' ->
  c <> c' ->
  c -[ tm ]->+ c'.
Proof.
  introv Hrun Hneq.
  apply with_counter in Hrun.
  destruct Hrun as [[| n] Hrun].
  - inverts Hrun. contradiction.
  - eauto.
Qed.

Lemma progress_evstep :
  forall tm c c',
  c -[ tm ]->+ c' ->
  c -[ tm ]->* c'.
Proof.
  introv H.
  apply progress_multistep in H. destruct H.
  eauto using without_counter.
Qed.

Lemma evstep_progress_trans :
  forall tm c c' c'',
  c  -[ tm ]->* c'  ->
  c' -[ tm ]->+ c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2. induction H1; eauto.
Qed.

Lemma progress_evstep_trans :
  forall tm c c' c'',
  c  -[ tm ]->+ c'  ->
  c' -[ tm ]->* c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2. induction H1.
  - apply with_counter in H2.
    destruct H2 as [[| n] H2]; eauto.
  - eauto.
Qed.

Lemma rewind_split:
  forall tm n k c c'',
  c -[ tm ]->> (n + k) / c'' ->
  exists c', c -[ tm ]->> n / c' /\ c' -[ tm ]->> k / c''.
Proof.
  intros tm n k.
  induction n; intros c c'' H.
  - eauto.
  - inverts H as Hstep Hrest.
    apply IHn in Hrest. clear IHn.
    destruct Hrest as [cn [Hn Hk]].
    eauto.
Qed.

(** When using [rewind_split], it is often more convenient to have the arithmetic
    show up as a separate goal, to be easily discharged with [lia]. *)
Lemma rewind_split':
  forall k1 k2 tm n c c'',
  c -[ tm ]->> n / c'' ->
  n = k1 + k2 ->
  exists c', c -[ tm ]->> k1 / c' /\ c' -[ tm ]->> k2 / c''.
Proof.
  introv H E. subst n. apply rewind_split; assumption.
Qed.

Lemma halted_no_multistep:
  forall tm c c' n,
  n > 0 ->
  halted tm c ->
  ~ c -[ tm ]->> n / c'.
Proof.
  introv Hgt0 Hhalted Hrun.
  inverts Hrun as Hstep Hrest.
  - inverts Hgt0.
  - eapply halted_no_step in Hhalted. eauto.
Qed.

Lemma exceeds_halt : forall tm c c' n k,
  halts_in tm c k ->
  n > k ->
  c -[ tm ]->> n / c' ->
  False.
Proof.
  introv [ch [Hch Hhalted]] Hnk Hexec.
  eapply (rewind_split' k (n - k)) in Hexec; try lia.
  destruct Hexec as [ch' [H1 H2]].
  deterministic.
  eapply halted_no_multistep in Hhalted.
  - eauto.
  - lia.
Qed.

Corollary within_halt : forall tm c c' k n,
  halts_in tm c n ->
  c -[ tm ]->> k / c' ->
  k <= n.
Proof.
  introv Hhalts Hrun.
  destruct (Nat.leb_spec k n); try assumption.
  exfalso. eauto using exceeds_halt.
Qed.

Lemma preceeds_halt : forall {tm c c' n k},
  halts_in tm c k ->
  c -[ tm ]->> n / c' ->
  halts_in tm c' (k - n) /\ n <= k.
Proof.
  introv Hhalt Hexec.
  assert (Hle : n <= k) by eauto using within_halt.
  destruct Hhalt as [ch [Hrunch Hhalted]].
  apply (rewind_split' n (k - n)) in Hrunch; try lia.
  destruct Hrunch as [cm [H1 H2]].
  deterministic.
  eauto.
Qed.

Corollary preceeds_halt' : forall tm c c' n k,
  halts_in tm c k ->
  c -[ tm ]->> n / c' ->
  halts_in tm c' (k - n).
Proof.
  introv Hhalt Hexec.
  now destruct (preceeds_halt Hhalt Hexec).
Qed.

Lemma skip_halts: forall tm c c' n,
  c -[ tm ]->> n / c' ->
  ~ halts tm c' ->
  ~ halts tm c.
Proof.
  introv Hexec Hnonhalt [k Hhalt].
  eauto using preceeds_halt'.
Qed.

Corollary multistep_nonhalt : forall tm c c',
  c -[ tm ]->* c' ->
  ~ halts tm c' ->
  ~ halts tm c.
Proof.
  introv Hexec Hnonhalt.
  destruct (with_counter Hexec) as [n Hexec'].
  eauto using skip_halts.
Qed.

Lemma progress_nonhalt' : forall tm (P : Q * tape -> Prop),
  (forall c, P c -> exists c', P c' /\ c -[ tm ]->+ c') ->
  forall k c, P c -> ~ halts_in tm c k.
Proof.
  introv Hstep.
  induction k as [k IH] using strong_induction.
  introv H0 Hhalts.
  apply Hstep in H0. destruct H0 as [c' [HP Hrun]].
  apply progress_multistep in Hrun. destruct Hrun as [n Hrun].
  destruct (preceeds_halt Hhalts Hrun) as [Hhalts' Hle].
  enough (Hnhalts : ~ halts_in tm c' (k - S n)) by contradiction.
  apply IH; intuition lia.
Qed.

Lemma progress_nonhalt : forall tm (P : Q * tape -> Prop) c,
  (forall c, P c -> exists c', P c' /\ c -[ tm ]->+ c') ->
  P c ->
  ~ halts tm c.
Proof.
  introv Hstep H0 Hhalts.
  destruct Hhalts as [k Hhalts].
  enough (Hnhalts : ~ halts_in tm c k) by contradiction.
  eauto using progress_nonhalt'.
Qed.

Corollary progress_nonhalt_simple : forall tm (A : Type) (C : A -> Q * tape) i0,
  (forall i, exists i', C i -[ tm ]->+ C i') ->
  ~ halts tm (C i0).
Proof with eauto.
  introv Hstep.
  apply progress_nonhalt with (P := fun c => exists i, c = C i)...
  - introv [i Hi]. subst c.
    destruct (Hstep i) as [i' Hi']...
Qed.

Corollary progress_nonhalt_cond : forall tm (A : Type) (i0 : A)
  (C : A -> Q * tape) (P : A -> Prop),
  (forall i, P i -> exists i', C i -[ tm ]->+ C i' /\ P i') ->
  P i0 ->
  ~ halts tm (C i0).
Proof with eauto.
  introv Hstep Hi0.
  apply progress_nonhalt with (P := fun c => exists i, c = C i /\ P i)...
  - introv [i [E HP]]. subst c.
    destruct (Hstep i HP) as [i' [Hi' HP']]...
Qed.

(* Constructively extracting useful information from the fact that a particular
   Turing machine has halted. *)
Lemma progress_halts : forall tm (P : Q * tape -> Prop) (Z : Q * tape -> Prop) c1,
  (forall c, P c -> Z c \/ exists c', P c' /\ c -[ tm ]->+ c') ->
  P c1 ->
  halts tm c1 ->
  exists c2, P c2 /\ Z c2.
Proof.
  (* proof by induction on the number of steps the TM takes to halt *)
  introv Hstep HP Hhalt.
  destruct Hhalt as [n Hhalt].
  generalize dependent c1.
  induction n as [n IH] using strong_induction.
  introv HP Hhalts.
  destruct (Hstep c1 HP) as [HZ | (c' & HP' & Hsteps)].
  - eauto.
  - apply progress_multistep in Hsteps. destruct Hsteps as [k Hsteps].
    destruct (preceeds_halt Hhalts Hsteps) as [Hhalts' Hle].
    apply IH with (n - S k) c'; [lia|eauto..].
Qed.

Lemma progress_halts_cond :
  forall tm (A : Type) (C : A -> Q * tape) (P : A -> Prop) (Z : A -> Prop) i0,
  (forall i, P i -> Z i \/ exists i', C i -[ tm ]->+ C i' /\ P i') ->
  P i0 ->
  halts tm (C i0) ->
  exists i, P i /\ Z i.
Proof with eauto.
  introv Hstep HP Hhalt.
  enough (H: exists c2, (exists i, c2 = C i /\ P i)
        /\ (exists i, c2 = C i /\ P i /\ Z i)) by jauto.
  apply progress_halts with tm (C i0); eauto.
  introv (i1 & -> & HPi1).
  destruct (Hstep i1 HPi1) as [| (i' & Hexec & HPi')]; eauto 6.
Qed.

Lemma halts_evstep : forall tm c c',
  halts tm c' ->
  c -[ tm ]->* c' ->
  halts tm c.
Proof.
  introv Hhalts Hsteps.
  apply with_counter in Hsteps. destruct Hsteps. eauto.
Qed.

Lemma halts_evstep' : forall tm c c',
  halts tm c ->
  c -[ tm ]->* c' ->
  halts tm c'.
Proof.
  introv Hhalts Hsteps.
  apply with_counter in Hsteps. destruct Hsteps as [k Hsteps].
  destruct Hhalts as [n Hhalts].
  eauto using preceeds_halt'.
Qed.

Lemma halted_evstep_halts : forall tm c c',
  c -[ tm ]->* c' ->
  halted tm c' ->
  halts tm c.
Proof.
  eauto using halts_evstep.
Qed.

End TM.

End BusyCoq_TM.
Export BusyCoq_TM.

(* ==================================================================================================== *)
(*               busycoq/verify/Compute.v  (commit bd2e36f, MIT licence, see the header)                *)
(* ==================================================================================================== *)

Module BusyCoq_Compute.

(** * Compute: executable Turing machine model *)

(** The model in [TM] uses coinductive, infinite streams, for which
    equality is undecidable, and a step relation, which isn't
    explicitly computable. This is nice for abstract reasoning,
    but not directly usable for deciding Turing machines.
    Here, we'll introduce a computable model, and prove
    that corresponds to the abstract one. *)

Import Coq.Bool.Bool.
Import Coq.Program.Tactics.
Import Coq.Lists.List. Import ListNotations.
Import Coq.Lists.Streams.
Import Coq.micromega.Lia.
Export BusyCoq_TM.
Set Default Goal Selector "!".

Module Compute (Ctx : Ctx).
  Module TM := TM Ctx. Export TM.

(** During computation, a tape is represented similarly to [tape], but
    with finite lists at each side, implicitly completed with [s0]. *)
Definition ctape : Type := list Sym * Sym * list Sym.

(** Lifting [ctape] into the corresponding [tape]. *)
Fixpoint lift_side (xs : list Sym) : Stream Sym :=
  match xs with
  | [] => const s0
  | x :: xs => Cons x (lift_side xs)
  end.

Definition lift_tape (t : ctape) : tape :=
  match t with (l, s, r) => (lift_side l, s, lift_side r) end.

Definition lift (c : Q * ctape) : Q * tape :=
  match c with (q, t) => (q, lift_tape t) end.

Local Obligation Tactic := intros; subst;
  simpl; rewrite const_unfold; congruence.

(** Deciding whether two [ctape]s correspond to the same [tape]. *)
Program Fixpoint empty_side (xs : list Sym)
    : {lift_side xs = const s0} + {lift_side xs <> const s0} :=
  match xs with
  | x :: xs => eqb_sym x s0 && Reduce (empty_side xs)
  | [] => Yes
  end.

Local Obligation Tactic := intros; subst; simpl in *; try congruence.

Program Fixpoint eqb_side (xs ys : list Sym)
    : {lift_side xs = lift_side ys} + {lift_side xs <> lift_side ys} :=
  match xs with
  | x :: xs' =>
    match ys with
    | y :: ys' => eqb_sym x y && Reduce (eqb_side xs' ys')
    | [] => Reduce (empty_side xs)
    end
  | [] => Reduce (empty_side ys)
  end.

Program Definition eqb_tape (t t' : ctape)
    : {lift_tape t = lift_tape t'} + {lift_tape t <> lift_tape t'} :=
  match t, t' with
  | (l, s, r), (l', s', r') =>
    eqb_side l l' && (eqb_sym s s' && Reduce (eqb_side r r'))
  end.

Program Definition eqb (c c' : Q * ctape)
    : {lift c = lift c'} + {lift c <> lift c'} :=
  match c, c' with
  | q;; t, q';; t' => eqb_q q q' && Reduce (eqb_tape t t')
  end.

(** Movement on [ctape]s. *)
Definition left (t : ctape) : ctape :=
  match t with
  | ([], s, r) => ([], s0, s :: r)
  | (s' :: l, s, r) => (l, s', s :: r)
  end.

Definition right (t : ctape) : ctape :=
  match t with
  | (l, s, []) => (s :: l, s0, [])
  | (l, s, s' :: r) => (s :: l, s', r)
  end.

Arguments left : simpl never.
Arguments right : simpl never.

Lemma lift_left : forall t, lift_tape (left t) = move_left (lift_tape t).
Proof.
  intros [[[| s' l] s] r]; reflexivity.
Qed.

Lemma lift_right : forall t, lift_tape (right t) = move_right (lift_tape t).
Proof.
  intros [[l s] [| s' r]]; reflexivity.
Qed.

#[export] Hint Rewrite lift_left lift_right : core.

Local Obligation Tactic := program_simplify; autorewrite with core; try (apply step_left || apply step_right); eauto.

(** Computable semantics of Turing machines. *)
Program Definition cstep (tm : TM) (c : Q * ctape)
    : {c' | lift c -[ tm ]-> lift c'} + {halted tm (lift c)} :=
  match c with
  | q;; l {{s}} r =>
    match tm (q, s) with
    | None => inright _
    | Some (s', L, q') => [|| q';; left  (l {{s'}} r) ||]
    | Some (s', R, q') => [|| q';; right (l {{s'}} r) ||]
    end
  end.

Program Fixpoint cmultistep (tm : TM) (n : nat) (c : Q * ctape)
    : {c' | lift c -[ tm ]->> n / lift c'} + {halts tm (lift c)} :=
  match n with
  | 0 => [|| c ||]
  | S n' =>
    bind c' <-- cstep tm c;
    bind c'' <-- cmultistep tm n' c';
    [|| c'' ||]
  end.

(** The starting configuration. *)
Definition starting : Q * ctape := q0;; [] {{s0}} [].

Lemma lift_starting : lift starting = c0.
Proof. reflexivity. Qed.

End Compute.

End BusyCoq_Compute.
Export BusyCoq_Compute.

(* ==================================================================================================== *)
(*                 busycoq/verify/Flip.v  (commit bd2e36f, MIT licence, see the header)                 *)
(* ==================================================================================================== *)

Module BusyCoq_Flip.

(** * Flip: swapping left and right *)

Import Coq.Logic.FunctionalExtensionality.
Import Coq.Bool.Bool.
Import Coq.Lists.List. Import ListNotations.
Import Coq.micromega.Lia.
Export BusyCoq_Compute.
Set Default Goal Selector "!".

Module Flip (Ctx : Ctx).
  Module Compute := Compute Ctx. Export Compute.

Definition flip_dir (d : dir) :=
  match d with
  | L => R
  | R => L
  end.

Definition flip_tape (t : tape) :=
  match t with
  | l {{s}} r => r {{s}} l
  end.

Definition flip (tm : TM) : TM := fun qs =>
  match tm qs with
  | Some (s, d, q) => Some (s, flip_dir d, q)
  | None => None
  end.

Lemma flip_involutive : forall tm,
  flip (flip tm) = tm.
Proof.
  intros tm. apply functional_extensionality.
  intros [q s]. unfold flip.
  destruct (tm (q, s)) as [[[s' []] q'] |]; reflexivity.
Qed.

Definition flip_conf (c : Q * tape) : Q * tape :=
  match c with
  | q;; t => q;; flip_tape t
  end.

Lemma flip_conf_involutive : forall c,
  flip_conf (flip_conf c) = c.
Proof.
  intros [q [[l s] r]]. reflexivity.
Qed.

Lemma flip_some : forall tm q s s' d q',
  tm (q, s) = Some (s', flip_dir d, q') ->
  flip tm (q, s) = Some (s', d, q').
Proof.
  introv H. unfold flip. rewrite H. destruct d; reflexivity.
Qed.

#[export] Hint Resolve flip_some : core.

Lemma flip_step : forall tm c c',
  c -[ tm ]-> c' ->
  flip_conf c -[ flip tm ]-> flip_conf c'.
Proof.
  introv H.
  inverts H as E; [apply step_right | apply step_left]; auto.
Qed.

#[export] Hint Resolve flip_step : core.

Lemma flip_multistep : forall tm n c c',
  c -[ tm ]->> n / c' ->
  flip_conf c -[ flip tm ]->> n / flip_conf c'.
Proof.
  induction n; introv H; inverts H as Hstep Hrest; eauto.
Qed.

#[export] Hint Resolve flip_multistep : core.

Lemma flip_evstep : forall tm c c',
  c -[ tm ]->* c' ->
  flip_conf c -[ flip tm ]->* flip_conf c'.
Proof. introv H. induction H; eauto. Qed.

Lemma unflip_evstep : forall tm c c',
  c -[ flip tm ]->* c' ->
  flip_conf c -[ tm ]->* flip_conf c'.
Proof.
  introv H. apply flip_evstep in H.
  rewrite flip_involutive in H. exact H.
Qed.

Lemma flip_progress : forall tm c c',
  c -[ tm ]->+ c' ->
  flip_conf c -[ flip tm ]->+ flip_conf c'.
Proof. introv H. induction H; eauto. Qed.

Lemma unflip_progress : forall tm c c',
  c -[ flip tm ]->+ c' ->
  flip_conf c -[ tm ]->+ flip_conf c'.
Proof.
  introv H. apply flip_progress in H.
  rewrite flip_involutive in H. exact H.
Qed.

Lemma flip_halted : forall tm c,
  halted tm c -> halted (flip tm) (flip_conf c).
Proof.
  intros tm [q [[l s] r]].
  unfold halted, flip. simpl.
  intros H. rewrite H.
  reflexivity.
Qed.

#[export] Hint Resolve flip_halted : core.

Lemma flip_halts_in : forall tm c n,
  halts_in tm c n -> halts_in (flip tm) (flip_conf c) n.
Proof.
  introv H.
  destruct H as [ch [Hexec Hhalted]].
  eauto 6.
Qed.

#[export] Hint Resolve flip_halts_in : core.

Lemma flip_halts : forall tm c,
  halts tm c -> halts (flip tm) (flip_conf c).
Proof.
  introv H. destruct H as [n H]. eauto.
Qed.

Lemma flip_halts_iff : forall tm c,
  halts tm c <-> halts (flip tm) (flip_conf c).
Proof.
  introv. split.
  - apply flip_halts.
  - intros H. apply flip_halts in H.
    rewrite flip_involutive, flip_conf_involutive in H.
    exact H.
Qed.

Lemma flip_halts_c0 : forall tm,
  ~ halts (flip tm) c0 -> ~ halts tm c0.
Proof. introv H. rewrite flip_halts_iff. exact H. Qed.

#[export] Hint Immediate flip_halts_c0 : core.

End Flip.

End BusyCoq_Flip.
Export BusyCoq_Flip.

(* ==================================================================================================== *)
(*               busycoq/verify/Permute.v  (commit bd2e36f, MIT licence, see the header)                *)
(* ==================================================================================================== *)

Module BusyCoq_Permute.

(** * Permute: renaming the states *)

Export BusyCoq_Flip.
Set Default Goal Selector "!".

Module Permute (Ctx : Ctx).
  Module Flip := Flip Ctx. Export Flip.

(* [f q = q'], where [q] is a state in [tm] and [q'] is the equivalent state
   in [tm']. *)
(* Note that this definition also admits mapping two equivalent states in [tm]
   to the same state in [tm']. This is intentional, though the name isn't
   perfect. *)
Definition Perm (tm tm' : TM) (f : Q -> Q) :=
  (forall q s,
    tm (q, s) = None ->
    tm' (f q, s) = None) /\
  (forall q s s' d q',
    tm (q, s) = Some (s', d, q') ->
    tm' (f q, s) = Some (s', d, f q')).

Lemma perm_halted : forall tm tm' f q t,
  Perm tm tm' f ->
  halted tm (q;; t) ->
  halted tm' (f q;; t).
Proof.
  introv [Hnone Hsome] H.
  destruct t as [[l s] r].
  apply Hnone, H.
Qed.

Lemma perm_halted' : forall tm tm' f q t,
  Perm tm tm' f ->
  halted tm' (f q;; t) ->
  halted tm (q;; t).
Proof.
  introv [Hnone Hsome] H.
  destruct t as [[l s] r].
  unfold halted in *.
  destruct (tm (q, s)) as [[[s' d] q'] |] eqn:E.
  - apply Hsome in E. congruence.
  - congruence.
Qed.

Local Hint Resolve perm_halted perm_halted' : core.

Lemma perm_step : forall tm tm' f q t q' t',
  Perm tm tm' f ->
  q;; t -[ tm ]-> q';; t' ->
  f q;; t -[ tm' ]-> f q';; t'.
Proof.
  introv [Hnone Hsome] Hstep.
  inverts Hstep as Hstep; constructor; auto.
Qed.

Local Hint Resolve perm_step : core.

Lemma perm_step' : forall tm tm' f q t q' t',
  Perm tm tm' f ->
  f q;; t -[ tm' ]-> q';; t' ->
  exists q'', q;; t -[ tm ]-> q'';; t' /\ f q'' = q'.
Proof.
  introv HP Hstep'.
  assert (H1: ~ halted tm' (f q;; t)).
  { introv Hhalt. eapply halted_no_step in Hhalt. eauto. }
  assert (H2: ~ halted tm (q;; t)) by eauto.
  apply no_halted_step in H2. destruct H2 as [[q'' t''] Hstep].
  exists q''.
  assert (f q;; t -[ tm' ]-> f q'';; t'') by eauto.
  assert (f q'';; t'' = q';; t') by eauto using step_deterministic.
  assert (t' = t'') by congruence. subst t''.
  intuition congruence.
Qed.

Lemma perm_multistep : forall tm tm' f,
  Perm tm tm' f -> forall n q t q' t',
  q;; t -[ tm ]->> n / q';; t' ->
  f q;; t -[ tm' ]->> n / f q';; t'.
Proof.
  introv HP.
  induction n; introv Hsteps; inverts Hsteps.
  - auto.
  - destruct c' as [qq tt]. eauto.
Qed.

Local Hint Resolve perm_multistep : core.

Lemma perm_multistep' : forall tm tm' f,
  Perm tm tm' f -> forall n q t q' t',
  f q;; t -[ tm' ]->> n / q';; t' ->
  exists q'', q;; t -[ tm ]->> n / q'';; t' /\ f q'' = q'.
Proof.
  introv HP.
  induction n; introv Hsteps; inverts Hsteps as H1 H2.
  - eauto.
  - destruct c' as [qq tt].
    eapply perm_step' in H1; try eassumption.
    destruct H1 as [qq' [H1 E1]]. subst qq.
    apply IHn in H2.
    jauto.
Qed.

Lemma perm_halts_in : forall tm tm' f q t n,
  Perm tm tm' f ->
  halts_in tm (q;; t) n ->
  halts_in tm' (f q;; t) n.
Proof.
  introv HP Hhalt.
  unfold halts_in in *.
  destruct Hhalt as [[q' t'] [Hstep Hhalt]]. eauto.
Qed.

Lemma perm_halts_in' : forall tm tm' f q t n,
  Perm tm tm' f ->
  halts_in tm' (f q;; t) n ->
  halts_in tm (q;; t) n.
Proof.
  introv HP Hhalt.
  unfold halts_in in *.
  destruct Hhalt as [[q' t'] [Hstep Hhalt]].
  eapply perm_multistep' in Hstep; try eassumption.
  destruct Hstep as [q'' [H E]]. subst q'. eauto.
Qed.

#[export] Hint Resolve perm_halts_in perm_halts_in' : core.

Lemma perm_halts : forall tm tm' f q t,
  Perm tm tm' f ->
  halts tm (q;; t) ->
  halts tm' (f q;; t).
Proof.
  introv HP Hhalts.
  unfold halts in *.
  destruct Hhalts as [n Hhalts]. eauto.
Qed.

Lemma perm_halts' : forall tm tm' f q t,
  Perm tm tm' f ->
  halts tm' (f q;; t) ->
  halts tm (q;; t).
Proof.
  introv HP Hhalts.
  unfold halts in *.
  destruct Hhalts as [n Hhalts]. eauto.
Qed.

Lemma perm_nonhalt : forall tm tm' f q t,
  Perm tm tm' f ->
  ~ halts tm' (f q;; t) ->
  ~ halts tm (q;; t).
Proof.
  introv HP H' H.
  eauto using perm_halts.
Qed.

Lemma perm_nonhalt' : forall tm tm' f q t,
  Perm tm tm' f ->
  ~ halts tm (q;; t) ->
  ~ halts tm' (f q;; t).
Proof.
  introv HP H' H.
  eauto using perm_halts'.
Qed.

End Permute.

End BusyCoq_Permute.
Export BusyCoq_Permute.

(* ==================================================================================================== *)
(*              busycoq/verify/Individual.v  (commit bd2e36f, MIT licence, see the header)              *)
(* ==================================================================================================== *)

Module BusyCoq_Individual.

(** * Utilities for proving individual machines *)

Export Coq.Lists.Streams.
Import Coq.micromega.Lia.
Export BusyCoq_Permute.
Set Default Goal Selector "!".

Module Individual (Ctx : Ctx).
  Module Permute := Permute Ctx. Export Permute.

(** Trivial lemmas, but [simpl] in these situations leaves a mess. *)
Lemma move_left_const : forall s0 s r,
  move_left (const s0 {{s}} r) = const s0 {{s0}} s >> r.
Proof. reflexivity. Qed.

Lemma move_right_const : forall l s s0,
  move_right (l {{s}} const s0) = l << s {{s0}} const s0.
Proof. reflexivity. Qed.

Lemma tl_const : forall A (x : A), tl (const x) = const x.
Proof. reflexivity. Qed.

#[export] Hint Rewrite move_left_const move_right_const tl_const : tape_pre.
#[export] Hint Rewrite <- const_unfold : tape_post.

Lemma lpow_shift' : forall A n (xs : list A) ys,
  xs^^n *> xs *> ys = xs *> xs^^n *> ys.
Proof.
  introv.
  rewrite <- Str_app_assoc.
  rewrite lpow_shift.
  rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma lpow_S : forall {A} n (xs : list A),
  xs^^(S n) = xs +> xs^^n.
Proof. reflexivity. Qed.

#[export] Hint Rewrite lpow_shift' lpow_add : tape_post.
#[export] Hint Rewrite @Str_app_assoc : tape_post.

(** The direct formulation isn't as useful when the proof that the two
    configurations are the same is non-trivial. *)
Lemma evstep_refl' : forall tm c c',
  c = c' ->
  c -[ tm ]->* c'.
Proof. intros. subst c'. auto. Qed.

(** Solve an equality goal where some subexpressions are equal by [lia],
    in an otherwise [reflexivity]-compatible spine. *)
Ltac lia_refl := solve [repeat (lia || f_equal)].

(** [prove_step] proves a goal of the form [c -[ tm ]-> ?c'], where the value
    returned by [tm] in this situation can be calculated by reflexivity. *)
Ltac prove_step_left := apply @step_left; reflexivity.
Ltac prove_step_right := apply @step_right; reflexivity.
Ltac prove_step := prove_step_left || prove_step_right.

(** Simplify a tape expression, removing [move_left] and [move_right] leftover
    after [prove_step], without needlessly expanding the [cofix] in [const s0]. *)
Ltac simpl_tape :=
  autorewrite with tape_pre;
  simpl;
  autorewrite with tape_post.

(** Prove a goal of the form [c -->+ c'] that consists of a single TM step. *)
Ltac finish_progress := apply progress_base; prove_step.

(** Prove a goal of the form [c -->* c'] that consists of zero TM steps. *)
Ltac finish_evstep := apply evstep_refl'; try (reflexivity || lia_refl).
Ltac finish := finish_evstep || finish_progress.

(** Advance the configuration on the left-hand side of a [-->+] or [-->*]
    by one TM step. *)
Ltac step := (eapply evstep_step || eapply progress_step); [prove_step | simpl_tape].

(** Run [step] until we reach the state that is being asked for, or until the
    TM gets stuck (because the symbolic state doesn't make it clear what symbol
    is under the tape). *)
Ltac execute := introv; repeat (try solve [finish]; step).

(** For a goal of the form [c -->+ c'], take steps until the TM gets stuck,
    taking at least one step. Transforms the goal into [c'' -->* c'] as a result. *)
Ltac start_progress := eapply progress_intro; [prove_step | simpl_tape]; execute.

(** [follow H], on a goal of the form [H: c1 -->* c2  |-  c1' -->* c3], will
    transform it into [|-  c2 -->* c3].  [adjust] is used to make it work when
    the equality [c1 = c1'] isn't as clear.

    [follow], without an argument, will try using the assumptions
    in the context. *)
Ltac do_adjust H ty :=
  lazymatch ty with
  | _ -> ?ty => do_adjust H ty
  | ?c1 -[ _ ]->* _ =>
    lazymatch goal with
    | |- ?c2 -[ _ ]->* _ =>
      replace c2 with c1; [apply H | reflexivity || lia_refl]
    end
  end.

Ltac adjust H := let ty := type of H in do_adjust H ty.
Ltac adjusted H := apply H || adjust H.
Ltac follow_trans :=
  lazymatch goal with
  | |- _ -[ _ ]->* _ => eapply evstep_trans
  | |- _ -[ _ ]->+ _ => eapply evstep_progress_trans
  end.

Ltac follow_hyp H := follow_trans; [adjusted H; eauto |].
Ltac follow_assm :=
  match goal with
  | H: _ |- _ => follow_hyp H
  end.

Tactic Notation "follow" := follow_assm.
Tactic Notation "follow" constr(H) := follow_hyp H.

(** For trivial [-->*] goals, provable by stepping and applying assumptions. *)
Ltac triv := intros; repeat (try solve [finish]; (step || follow)).

End Individual.

End BusyCoq_Individual.
Export BusyCoq_Individual.

(* ==================================================================================================== *)
(*      bb8_list/proofs/BB102.v and Individual102.v: busycoq instantiated to 10 states, 2 symbols       *)
(* ==================================================================================================== *)

(** * Instantiating busycoq to machines with 10 states and 2 symbols (bb8 project, for the BB(10) champion; mirrors BB92.v) *)

Import Coq.Lists.List. Import ListNotations.
Export BusyCoq_Flip.
Set Default Goal Selector "!".

(* Textual change (with the same one for busycoq's [dir] in TM above; besides these, only the renaming of
   qualified names described in the header).  The constructors of [state] are named St_A ... St_J here, with the
   abbreviations A ... J, so that A ... J are not global constants of THIS library: when Coq invents a name
   (anonymous `pose proof`, bare `intros` on `forall L t ts A, ...`) it skips the names of globals defined in the
   current library, and the original proofs, where the constructors came from another compiled file, rely on the
   invented names (H, H0, ...; the binder names A, L themselves).  A renamed constructor behind an abbreviation is
   not a global for that check; patterns, notations and printing are unaffected: `tm (H, 0)`, `| A, 0 => ...` and
   `{{H}}>` mean exactly what they meant. *)
Inductive state := St_A | St_B | St_C | St_D | St_E | St_F | St_G | St_H | St_I | St_J.
Notation A := St_A.  Notation B := St_B.  Notation C := St_C.  Notation D := St_D.  Notation E := St_E.
Notation F := St_F.  Notation G := St_G.  Notation H := St_H.  Notation I := St_I.  Notation J := St_J.
Inductive sym := S0 | S1.

Module BB102 <: Ctx.
  Definition Q := state.
  Definition Sym := sym.
  Definition q0 := A.
  Definition q1 := B.
  Definition s0 := S0.
  Definition s1 := S1.

  Lemma q0_neq_q1 : q0 <> q1.
  Proof. discriminate. Qed.

  Lemma s0_neq_s1 : s0 <> s1.
  Proof. discriminate. Qed.

  Definition eqb_q (a b : Q): {a = b} + {a <> b}.
    decide equality.
  Defined.

  Definition eqb_sym (a b : Sym): {a = b} + {a <> b}.
    decide equality.
  Defined.

  Definition all_qs := [A; B; C; D; E; F; G; H; I; J].

  Lemma all_qs_spec : forall a, In a all_qs.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.

  Definition all_syms := [S0; S1].

  Lemma all_syms_spec : forall a, In a all_syms.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.
End BB102.

Export BusyCoq_Individual.


Module Individual102 := Individual BB102.
Export Individual102.

Declare Scope sym_scope.
Bind Scope sym_scope with Sym.
Delimit Scope sym_scope with sym.
Open Scope sym.

Notation "0" := S0 : sym_scope.
Notation "1" := S1 : sym_scope.

(* Make sure that [{{D}}>] still refers to the state, even if we shadowed
   [D] itself with something else. *)
Notation "l '{{A}}>'  r" := (l {{A}}> r) (at level 30).
Notation "l '{{B}}>'  r" := (l {{B}}> r) (at level 30).
Notation "l '{{C}}>'  r" := (l {{C}}> r) (at level 30).
Notation "l '{{D}}>'  r" := (l {{D}}> r) (at level 30).
Notation "l '{{E}}>'  r" := (l {{E}}> r) (at level 30).
Notation "l '{{F}}>'  r" := (l {{F}}> r) (at level 30).
Notation "l '{{G}}>'  r" := (l {{G}}> r) (at level 30).
Notation "l '{{H}}>'  r" := (l {{H}}> r) (at level 30).
Notation "l '{{I}}>'  r" := (l {{I}}> r) (at level 30).

Notation "l '<{{A}}' r" := (l <{{A}} r) (at level 30).
Notation "l '<{{B}}' r" := (l <{{B}} r) (at level 30).
Notation "l '<{{C}}' r" := (l <{{C}} r) (at level 30).
Notation "l '<{{D}}' r" := (l <{{D}} r) (at level 30).
Notation "l '<{{E}}' r" := (l <{{E}} r) (at level 30).
Notation "l '<{{F}}' r" := (l <{{F}} r) (at level 30).
Notation "l '<{{G}}' r" := (l <{{G}} r) (at level 30).
Notation "l '<{{H}}' r" := (l <{{H}} r) (at level 30).
Notation "l '<{{I}}' r" := (l <{{I}} r) (at level 30).
Notation "l '{{J}}>'  r" := (l {{J}}> r) (at level 30).
Notation "l '<{{J}}' r" := (l <{{J}} r) (at level 30).

(* ==================================================================================================== *)
(*                          Module Champion10: the BB(10) champion (Racheline)                          *)
(* ==================================================================================================== *)

Module Champion10.

(* ==================================================================================================== *)
(*                  bb8_list/proofs/BB10_champion_1RB1RA.v: the BB(10) champion halts                   *)
(* ==================================================================================================== *)

(* Each original file started with the symbol scope on top (from Individual102's `Open Scope sym`);
   restore that here, since the previous part may have ended in nat_scope. *)
Local Open Scope sym_scope.

(** * The BB(10) champion 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ halts *)

(** Machine-checked halting proof of the 10-state, 2-symbol champion found by Racheline (wiki "Champions" table,
    claimed bound > f_omega^2(25)).  Written for bb8_list/investigations/bb10_champion_1RB1RA_0LF0LJ.md; generated by
    bb8_list/investigations/bb10_champion_1RB1RA_0LF0LJ/coq/gen_halt.py from the BB(9)-champion proofs
    (BB9_champion_1RB1RA.v, BB9_champion_bound.v): rows A-H of the two machines are identical and the rules R1-R3
    never visit H, I or J, so their proofs are reused verbatim (re-checked here against this machine's table).

    Configuration family (head D on the blank left of the word; the word is read towards the right):
      Kd ds a b = 0^inf <D 1^(b+1) 0 1^a 0 1^d_1 0 1^d_2 0 ... 1^d_n 0^inf        ds = [d_1; ...; d_n], top digit first
    Rules, proved for all parameters:
      R1 : Kd ds (S a) b                               -->+ Kd ds a (b + 3)
      R2 : Kd (S y :: t) 0 b                           -->+ Kd (y :: t) (b + 2) 1
      R3 : Kd (0^(m+1) ++ S y :: t) 0 (2(m+1) + s)     -->+ Kd (2^m ++ (s+2) :: y :: t) 2 1
      R4 (new, uses I and J):  Kd (0^k) 0 (4m)   -->+ Kd (1 :: trip m) 0 0,   trip m = (0,0,3)^m (0,0,2)
                               Kd (0^k) 0 (4m+2) -->+ Kd (3 :: trip m) 0 0
                               Kd (0^k) 0 (2m+1) halts (E0 = 1RZ), as for the BB(9) champion
    Exact clearing (CDPx_all, as in BB9_champion_bound.v): a digit v at depth j maps b to (U j)^v b when 2j <= b, with
      U 0 x = 3x+7, U (j+1) x = (U j)^(x-2j) (X j), X 0 = 7, X (j+1) = U j (U j (X j)).
    New arithmetic fact (U_mod8): for j >= 2 and x >= 2j, U j x = 7 (mod 8) if x is even and 0 (mod 8) if x is odd.
    The run: the blank tape reaches Kd [2] 0 0 in 12 steps; clearing [2] gives b = 28 = 4*7; rebuild 1 gives
    Kd (1 :: trip 7) 0 0; its clearing gives b1 = Tv 7 1 7 = 0 (mod 8) (the counter before the last digit is even);
    rebuild 2 has m1 = b1/4 even; its clearing gives b2 = Tv m1 1 7, which is odd (7 + 3 m1 + 2 units flip the parity
    of 0); R4 halts. *)


Import Coq.micromega.Lia Coq.Arith.PeanoNat Coq.Lists.List Coq.Arith.Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, R, A)
  | B, 0 => Some (0, L, C)  | B, 1 => Some (0, L, F)
  | C, 0 => Some (0, R, D)  | C, 1 => Some (1, L, C)
  | D, 0 => Some (1, R, A)  | D, 1 => Some (1, R, G)
  | E, 0 => None            | E, 1 => Some (0, R, A)
  | F, 0 => Some (1, L, B)  | F, 1 => Some (1, L, F)
  | G, 0 => Some (1, L, H)  | G, 1 => Some (1, R, E)
  | H, 0 => Some (0, L, I)  | H, 1 => Some (1, L, H)
  | I, 0 => Some (0, L, F)  | I, 1 => Some (0, L, J)
  | J, 0 => Some (1, L, H)  | J, 1 => Some (0, L, J)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma align_lpow : forall (x : Sym) xs ys n,
  (x::xs)^^n *> x >> ys = x >> (xs ++ [x])^^n *> ys.
Proof.
  induction n.
  - reflexivity.
  - simpl. repeat rewrite Str_app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma align_lpow_const : forall (x : Sym) xs n,
  (x::xs)^^n *> const x = x >> (xs ++ [x])^^n *> const x.
Proof. intros. rewrite const_unfold at 1. apply align_lpow. Qed.

Ltac align_tape := repeat ((rewrite align_lpow || rewrite align_lpow_const); simpl app).
Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
Ltac finish_norm := apply evstep_refl'; norm_nat; align_tape; try reflexivity; lia_refl.

Lemma cr_AR_1_1 : forall n l r, l {{A}}> [1]^^n *> r -->* [1]^^n *> l {{A}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_FL_1_1 : forall n l r, [1]^^n *> l <{{F}} r -->* l <{{F}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_CL_1_1 : forall n l r, [1]^^n *> l <{{C}} r -->* l <{{C}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_FL_011_101 : forall n l r, [0;1;1]^^n *> l <{{F}} r -->* l <{{F}} [1;0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.


(** The rebuild pass (new): from state I, every two (110)-blocks become 100011, read as a digit 3 behind two zero
    digits.  I1 = 0LJ, J1 = 0LJ, J0 = 1LH, H1 = 1LH, H1, H0 = 0LI. *)
Lemma cr_IL_110110 : forall n l r, [1;1;0;1;1;0]^^n *> l <{{I}} r -->* l <{{I}} [0;1;1;1;0;0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma R4E4 : forall m, ([0;1;1;0;1;1]^^m *> 0 >> 1 >> 1 >> const 0) {{A}}> const 0 -->+
  const 0 <{{D}} (1 >> 0 >> 0 >> 1 >> [0;0;0;1;1;1]^^m *> 0 >> 0 >> 0 >> 1 >> 1 >> const 0).
Proof.
  intros.
  rewrite (align_lpow 0 [1;1;0;1;1] _ _). simpl app.
  start_progress.
  follow cr_IL_110110.
  do 8 step. finish_norm.
Qed.

Lemma R4E6 : forall m, ([0;1;1;0;1;1]^^(S m) *> const 0) {{A}}> const 0 -->+
  const 0 <{{D}} (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> [0;0;0;1;1;1]^^m *> 0 >> 0 >> 0 >> 1 >> 1 >> const 0).
Proof.
  intros.
  rewrite (align_lpow_const 0 [1;1;0;1;1] _). simpl app.
  start_progress.
  follow cr_IL_110110.
  do 4 step. finish_norm.
Qed.

Lemma R1 : forall b a l, const 0 <{{D}} (1 >> [1]^^b *> 0 >> 1 >> [1]^^a *> l) -->+ const 0 <{{D}} (1 >> 1 >> 1 >> 1 >> [1]^^b *> 0 >> [1]^^a *> l).
Proof.
  intros.
  start_progress.
  follow cr_AR_1_1.
  execute.
  follow cr_FL_1_1.
  do 5 step. finish_norm.
Qed.

Lemma R2 : forall b y t, const 0 <{{D}} (1 >> [1]^^b *> 0 >> 0 >> 1 >> [1]^^y *> t) -->+ const 0 <{{D}} (1 >> 1 >> 0 >> 1 >> 1 >> [1]^^b *> 0 >> [1]^^y *> t).
Proof.
  intros.
  start_progress.
  follow cr_AR_1_1.
  execute.
  follow cr_CL_1_1.
  execute.
  rewrite (align_lpow 1 [] _ _). simpl app.
  execute.
  follow cr_AR_1_1.
  execute.
  follow cr_FL_1_1.
  do 6 step. finish_norm.
Qed.

Lemma ENTRY : forall b w, const 0 <{{D}} (1 >> [1]^^b *> 0 >> w) -->+ ([1]^^b *> 1 >> 1 >> const 0) {{A}}> (0 >> w).
Proof.
  intros.
  start_progress.
  follow cr_AR_1_1.
  do 0 step. finish_norm.
Qed.

Lemma LOOP : forall r Y z, (1 >> 1 >> [1]^^r *> 0 >> Y) {{A}}> (0 >> 0 >> z) -->+ ([1]^^r *> 0 >> 1 >> 1 >> 0 >> Y) {{A}}> (0 >> z).
Proof.
  intros.
  start_progress.
  follow cr_CL_1_1.
  execute.
  rewrite (align_lpow 1 [] _ _). simpl app.
  execute.
  rewrite (align_lpow 1 [] _ _). simpl app.
  execute.
  rewrite (align_lpow 1 [] _ _). simpl app.
  execute.
  follow cr_AR_1_1.
  do 0 step. finish_norm.
Qed.

Lemma FINAL : forall s m y t, ([1]^^s *> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^m *> const 0) {{A}}> (0 >> 1 >> [1]^^y *> t) -->+ const 0 <{{D}} (1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1]^^s *> 1 >> 0 >> [1]^^y *> t).
Proof.
  intros.
  start_progress.
  follow cr_FL_1_1.
  execute.
  follow cr_FL_011_101.
  do 3 step. finish_norm.
Qed.

(** ** The digit family *)

Fixpoint lft (ds : list nat) : side :=
  match ds with
  | [] => const 0
  | d :: t => 0 >> [1]^^d *> lft t
  end.

(** Kd ds a b = 0^inf <D (1^(b+1) 0 1^a 0 1^d_1 0 1^d_2 ...) : the head is on the blank left of the word *)
Definition Kd (ds : list nat) (a b : nat) : Q * tape :=
  const 0 <{{D}} (1 >> [1]^^b *> 0 >> [1]^^a *> lft ds).

Lemma zeros_shift : forall j l, [0]^^j *> 0 >> l = 0 >> [0]^^j *> l.
Proof. induction j; intros. - reflexivity. - simpl. rewrite IHj. reflexivity. Qed.

Lemma zeros_const : forall j, [0]^^j *> const 0 = const 0.
Proof. induction j. - reflexivity. - simpl. rewrite IHj. symmetry. apply const_unfold. Qed.

Lemma lft_zeros : forall k t, lft (repeat 0%nat k ++ t) = [0]^^k *> lft t.
Proof. induction k; intros. - reflexivity. - simpl. rewrite IHk. reflexivity. Qed.

Lemma lft_blank : forall k, lft (repeat 0%nat k) = const 0.
Proof. intros. rewrite <- (app_nil_r (repeat 0%nat k)), lft_zeros. apply zeros_const. Qed.

Lemma lft_twos : forall k t, lft (repeat 2%nat k ++ t) = [0;1;1]^^k *> lft t.
Proof. induction k; intros. - reflexivity. - simpl. rewrite IHk. reflexivity. Qed.

Lemma repeat_snoc : forall (x : nat) n U, repeat x n ++ x :: U = repeat x (S n) ++ U.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

(** ** The four rules *)

Lemma KR1 : forall ds a b, Kd ds (S a) b -->+ Kd ds a (b + 3).
Proof.
  intros. unfold Kd. replace (b + 3) with (3 + b) by lia.
  apply R1.
Qed.

Lemma KR2 : forall y t b, Kd (S y :: t) 0 b -->+ Kd (y :: t) (b + 2) 1.
Proof.
  intros. unfold Kd. replace (b + 2) with (2 + b) by lia.
  apply R2.
Qed.

Lemma const0 : 0 >> const 0 = const 0.
Proof. symmetry. apply const_unfold. Qed.

Lemma lpow_ones_two : forall n X, [1]^^n *> 1 >> 1 >> X = [1]^^(n + 2) *> X.
Proof. induction n; intros. - reflexivity. - simpl. rewrite IHn. reflexivity. Qed.

Lemma blocks_snoc : forall i Y, [0;1;1]^^i *> 0 >> 1 >> 1 >> 0 >> Y = [0;1;1]^^(S i) *> 0 >> Y.
Proof. intros. change (0 >> 1 >> 1 >> 0 >> Y) with ([0;1;1] *> 0 >> Y). rewrite lpow_shift'. reflexivity. Qed.

Lemma ones_back : forall s X, [1]^^s *> 1 >> X = 1 >> [1]^^s *> X.
Proof. intros. change (1 >> X) with ([1] *> X). rewrite lpow_shift'. reflexivity. Qed.

(** The cycle LOOP, i times. *)
Lemma LOOPS : forall i s Y z,
  ([1]^^(2 * i + s) *> 0 >> Y) {{A}}> ([0]^^i *> 0 >> z) -->*
  ([1]^^s *> [0;1;1]^^i *> 0 >> Y) {{A}}> (0 >> z).
Proof.
  induction i; intros.
  - finish.
  - replace (2 * S i + s) with (S (S (2 * i + s))) by lia.
    change ([1]^^(S (S (2 * i + s))) *> 0 >> Y) with (1 >> 1 >> [1]^^(2 * i + s) *> 0 >> Y).
    change ([0]^^(S i) *> 0 >> z) with (0 >> [0]^^i *> 0 >> z).
    rewrite zeros_shift.
    eapply evstep_trans; [apply progress_evstep, LOOP |].
    rewrite <- zeros_shift.
    follow (IHi s (1 >> 1 >> 0 >> Y) z).
    apply evstep_refl'. rewrite blocks_snoc. reflexivity.
Qed.

Lemma EQ3 : forall m s y t,
  1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1]^^s *> 1 >> 0 >> [1]^^y *> t =
  1 >> [1]^^1 *> 0 >> [1]^^2 *> ([0;1;1]^^m *> 0 >> [1]^^(S (S s)) *> 0 >> [1]^^y *> t).
Proof.
  intros.
  rewrite (align_lpow 1 [0;1] _ m). simpl app.
  change (0 >> 1 >> 1 >> 0 >> 1 >> [1]^^s *> 1 >> 0 >> [1]^^y *> t)
    with ([0;1;1] *> (0 >> 1 >> [1]^^s *> 1 >> 0 >> [1]^^y *> t)).
  rewrite lpow_shift'.
  rewrite ones_back.
  change (1 >> 1 >> [1]^^s *> 0 >> [1]^^y *> t) with ([1]^^(S (S s)) *> 0 >> [1]^^y *> t).
  change (1 >> [1]^^1 *> 0 >> [1]^^2 *> ([0;1;1]^^m *> 0 >> [1]^^(S (S s)) *> 0 >> [1]^^y *> t))
    with (1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^m *> 0 >> [1]^^(S (S s)) *> 0 >> [1]^^y *> t).
  change (0 >> 1 >> 1 >> [0;1;1]^^m *> 0 >> [1]^^(S (S s)) *> 0 >> [1]^^y *> t)
    with ([0;1;1] *> [0;1;1]^^m *> 0 >> [1]^^(S (S s)) *> 0 >> [1]^^y *> t).
  reflexivity.
Qed.

Lemma KR3 : forall m s y t,
  Kd (repeat 0%nat (S m) ++ S y :: t) 0 (2 * S m + s) -->+ Kd (repeat 2%nat m ++ S (S s) :: y :: t) 2 1.
Proof.
  intros m s y t. unfold Kd. rewrite lft_zeros.
  change ([1]^^0 *> [0]^^(S m) *> lft (S y :: t)) with ([0]^^(S m) *> 0 >> 1 >> [1]^^y *> lft t).
  eapply progress_evstep_trans; [apply ENTRY |].
  replace ([1]^^(2 * S m + s) *> 1 >> 1 >> const 0) with ([1]^^(2 * S (S m) + s) *> 0 >> const 0).
  2:{ rewrite lpow_ones_two, const0. replace (2 * S (S m) + s) with (2 * S m + s + 2) by lia. reflexivity. }
  change (0 >> [0]^^(S m) *> 0 >> 1 >> [1]^^y *> lft t) with ([0]^^(S (S m)) *> 0 >> 1 >> [1]^^y *> lft t).
  follow (LOOPS (S (S m)) s (const 0) (1 >> [1]^^y *> lft t)).
  simpl lpow. rewrite const0.
  apply progress_evstep.
  eapply progress_evstep_trans; [apply FINAL |].
  apply evstep_refl'. unfold Kd. rewrite lft_twos. simpl lft.
  rewrite EQ3. reflexivity.
Qed.

Lemma LOOPS_blank : forall i s,
  ([1]^^(2 * i + s) *> const 0) {{A}}> const 0 -->*
  ([1]^^s *> [0;1;1]^^i *> const 0) {{A}}> const 0.
Proof.
  intros. pose proof (LOOPS i s (const 0) (const 0)) as H.
  rewrite zeros_shift, zeros_const, const0 in H. exact H.
Qed.


(** ** The rebuild R4 (new) *)

Lemma lpow_double : forall {T} (xs : list T) m, xs^^(2 * m) = (xs ++ xs)^^m.
Proof.
  induction m. - reflexivity.
  - replace (2 * S m) with (S (S (2 * m))) by lia. cbn [lpow]. rewrite IHm, app_assoc. reflexivity.
Qed.

Lemma blocks_odd : forall m, [0;1;1]^^(S (2 * m)) *> const 0 = [0;1;1;0;1;1]^^m *> 0 >> 1 >> 1 >> const 0.
Proof.
  intros. cbn [lpow]. rewrite <- lpow_shift, Str_app_assoc, lpow_double. reflexivity.
Qed.

Lemma blocks_even : forall m, [0;1;1]^^(2 * m) *> const 0 = [0;1;1;0;1;1]^^m *> const 0.
Proof. intros. rewrite lpow_double. reflexivity. Qed.

(** trip m = (0,0,3)^m (0,0,2), top digit first *)
Fixpoint trip (m : nat) : list nat :=
  match m with
  | O => [0%nat; 0%nat; 2%nat]
  | S m' => 0%nat :: 0%nat :: 3%nat :: trip m'
  end.

Lemma lft_trip : forall m, lft (trip m) = [0;0;0;1;1;1]^^m *> 0 >> 0 >> 0 >> 1 >> 1 >> const 0.
Proof. induction m. - reflexivity. - simpl. simpl in IHm. rewrite IHm. reflexivity. Qed.

Lemma KR4E4 : forall k m, Kd (repeat 0%nat k) 0 (4 * m) -->+ Kd (1%nat :: trip m) 0 0.
Proof.
  intros k m. unfold Kd. rewrite lft_blank.
  change ([1]^^0 *> const 0) with (const 0).
  eapply progress_evstep_trans; [apply ENTRY |].
  rewrite lpow_ones_two, const0.
  replace (4 * m + 2) with (2 * S (2 * m) + 0) by lia.
  follow (LOOPS_blank (S (2 * m)) 0).
  change ([1]^^0 *> [0;1;1]^^(S (2 * m)) *> const 0) with ([0;1;1]^^(S (2 * m)) *> const 0).
  rewrite blocks_odd.
  apply progress_evstep.
  eapply progress_evstep_trans; [apply (R4E4 m) |].
  apply evstep_refl'. unfold Kd. simpl lft. rewrite lft_trip. reflexivity.
Qed.

Lemma KR4E6 : forall k m, Kd (repeat 0%nat k) 0 (4 * m + 2) -->+ Kd (3%nat :: trip m) 0 0.
Proof.
  intros k m. unfold Kd. rewrite lft_blank.
  change ([1]^^0 *> const 0) with (const 0).
  eapply progress_evstep_trans; [apply ENTRY |].
  rewrite lpow_ones_two, const0.
  replace (4 * m + 2 + 2) with (2 * S (S (2 * m)) + 0) by lia.
  follow (LOOPS_blank (S (S (2 * m))) 0).
  change ([1]^^0 *> [0;1;1]^^(S (S (2 * m))) *> const 0) with ([0;1;1]^^(S (S (2 * m))) *> const 0).
  replace (S (S (2 * m))) with (2 * S m) by lia.
  rewrite blocks_even.
  apply progress_evstep.
  eapply progress_evstep_trans; [apply (R4E6 m) |].
  apply evstep_refl'. unfold Kd. simpl lft. rewrite lft_trip. reflexivity.
Qed.

(** Odd b: the machine halts (same transitions as for the BB(9) champion). *)
Definition c_end (m : nat) : state * tape :=
  (1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^m *> const 0) {{E}}> const 0.

Lemma HALT7x : forall m,
  (1 >> 0 >> 1 >> 1 >> [0;1;1]^^m *> const 0) {{A}}> const 0 -->* c_end m.
Proof. intros. unfold c_end. do 7 step. apply evstep_refl. Qed.

Lemma c_end_halted : forall m, halted tm (c_end m).
Proof. intros. unfold c_end. simpl. reflexivity. Qed.

Lemma KR4Ox : forall k m, Kd (repeat 0%nat k) 0 (2 * m + 1) -->* c_end m.
Proof.
  intros k m. unfold Kd. rewrite lft_blank.
  change ([1]^^0 *> const 0) with (const 0).
  apply progress_evstep.
  eapply progress_evstep_trans; [apply ENTRY |].
  rewrite lpow_ones_two, const0.
  replace (2 * m + 1 + 2) with (2 * S m + 1) by lia.
  follow (LOOPS_blank (S m) 1).
  simpl lpow.
  apply HALT7x.
Qed.

Lemma init_reach : c0 -->* Kd [2%nat] 0 0.
Proof. unfold Kd. simpl. do 12 step. finish. Qed.

Local Open Scope nat_scope.

Ltac absmod x k :=
  let q := fresh "q" in let r := fresh "r" in
  let H1 := fresh "Hdm" in let H2 := fresh "Hmb" in
  pose proof (Nat.div_mod_eq x k) as H1;
  assert (H2 : x mod k < k) by (apply Nat.mod_upper_bound; discriminate);
  set (q := x / k) in *; set (r := x mod k) in *; clearbody q r.
(** lia in this Coq build does not understand mod: abstract each x mod k with its division facts first. *)
Ltac mods :=
  repeat match goal with
  | H : context[?x mod ?k] |- _ => absmod x k
  | |- context[?x mod ?k] => absmod x k
  end.

Lemma R1iter : forall a ds b, Kd ds a b -->* Kd ds 0 (b + 3 * a).
Proof.
  induction a; intros.
  - replace (b + 3 * 0) with b by lia. finish.
  - eapply evstep_trans; [apply progress_evstep, KR1 |].
    follow (IHa ds (b + 3)).
    replace (b + 3 * S a) with (b + 3 + 3 * a) by lia. finish.
Qed.


Fixpoint iter (n : nat) (g : nat -> nat) (x : nat) : nat :=
  match n with
  | O => x
  | S n' => g (iter n' g x)
  end.

(** ** Iteration *)

Lemma iter_S' : forall n g x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

Lemma iter_add : forall a b g x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

Lemma iter_mono_x : forall g, (forall a b, a <= b -> g a <= g b) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; auto. Qed.

Lemma iter_ge : forall g, (forall a, a <= g a) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_mono_n : forall g, (forall a, a <= g a) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite iter_add. apply iter_ge. exact Hg.
Qed.

Lemma iter_lin : forall g, (forall a, a + 1 <= g a) -> forall n x, x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_lin1 : forall g, (forall a, 1 <= a -> a + 1 <= g a) -> forall n x, 1 <= x -> x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros x Hx; simpl. - lia.
  - specialize (IHn x Hx). specialize (Hg (iter n g x) ltac:(lia)). lia.
Qed.

Lemma iter_par : forall g T, (forall y, T <= y -> T <= g y /\ g y mod 2 = (y + 1) mod 2) ->
  forall n x, T <= x -> T <= iter n g x /\ iter n g x mod 2 = (x + n) mod 2.
Proof.
  intros g T Hg. induction n; intros x Hx; cbn [iter].
  - split; [lia | f_equal; lia].
  - destruct (IHn x Hx) as [H1 H2]. destruct (Hg _ H1) as [H3 H4]. split; [exact H3 |].
    rewrite H4. mods; lia.
Qed.

(** ** The exact clearing functions *)

(** U j x : the value of b after clearing ONE unit of a digit at depth j (j zero digits above it) from b = x.
    X j   : the value of b after clearing j twos at depths 0 .. j-1, starting from b = 7.
      U 0 x = 3x + 7,  U (j+1) x = (U j)^(x - 2j) (X j),  X 0 = 7,  X (j+1) = U j (U j (X j)).
    (R2 + R1^(b+2) gives 3b+7; R3 at depth j+1 writes j twos above the refilled digit x - 2j, then b = 7.) *)
Fixpoint UX (j : nat) : (nat -> nat) * nat :=
  match j with
  | O => (fun x => 3 * x + 7, 7)
  | S i => (fun x => iter (x - 2 * i) (fst (UX i)) (snd (UX i)),
            fst (UX i) (fst (UX i) (snd (UX i))))
  end.

Definition U (j : nat) : nat -> nat := fst (UX j).
Definition X (j : nat) : nat := snd (UX j).

Lemma U_0 : forall x, U 0 x = 3 * x + 7.
Proof. reflexivity. Qed.

Lemma U_S : forall j x, U (S j) x = iter (x - 2 * j) (U j) (X j).
Proof. reflexivity. Qed.

Lemma X_0 : X 0 = 7.
Proof. reflexivity. Qed.

Lemma X_S : forall j, X (S j) = U j (U j (X j)).
Proof. reflexivity. Qed.


(** Never let a tactic compute these numbers. *)
Opaque U X.

Lemma growth : forall j, (forall x, x + 2 * j + 5 <= U j x) /\ 4 * j + 7 <= X j.
Proof.
  induction j as [| j [Hu Hx]].
  - split; [intros; rewrite U_0; lia | rewrite X_0; lia].
  - split.
    + intros x. rewrite U_S.
      pose proof (iter_lin (U j) ltac:(intros a; specialize (Hu a); lia) (x - 2 * j) (X j)). lia.
    + rewrite X_S. pose proof (Hu (X j)). pose proof (Hu (U j (X j))). lia.
Qed.

Lemma Ugrow : forall j x, x + 2 * j + 5 <= U j x.
Proof. intros. apply growth. Qed.

Lemma Xgrow : forall j, 4 * j + 7 <= X j.
Proof. intros. apply growth. Qed.

Lemma U_ge_X : forall i z, X i <= U (S i) z.
Proof.
  intros. rewrite U_S. apply iter_ge. intros a. pose proof (Ugrow i a). lia.
Qed.

(** Parity: one unit at depth j flips the parity of b (for 2j <= b). *)
Lemma parity : forall j, (forall x, 2 * j <= x -> U j x mod 2 = (x + 1) mod 2) /\ X j mod 2 = 1.
Proof.
  induction j as [| j [Hu Hx]].
  - split; [intros; rewrite U_0; mods; lia | rewrite X_0; reflexivity].
  - assert (Hg : forall y, 2 * j <= y -> 2 * j <= U j y /\ U j y mod 2 = (y + 1) mod 2).
    { intros y Hy. split; [pose proof (Ugrow j y); lia | auto]. }
    split.
    + intros x Hx'. rewrite U_S. pose proof (Xgrow j).
      destruct (iter_par (U j) (2 * j) Hg (x - 2 * j) (X j) ltac:(lia)) as [_ Hp].
      rewrite Hp. mods; lia.
    + rewrite X_S. pose proof (Xgrow j).
      destruct (Hg (X j)) as [H1 H2]; [lia |]. destruct (Hg (U j (X j)) H1) as [_ H3].
      rewrite H3. mods; lia.
Qed.

Lemma Upar : forall j x, 2 * j <= x -> U j x mod 2 = (x + 1) mod 2.
Proof. intros. apply parity. assumption. Qed.

Lemma Ustep : forall j y, 2 * j <= y -> 2 * j <= U j y /\ U j y mod 2 = (y + 1) mod 2.
Proof. intros. split; [pose proof (Ugrow j y); lia | apply Upar; assumption]. Qed.

(** ** Clearing at the machine level, with exact values *)

Lemma CHx : forall v Us B, Kd (v :: Us) 0 B -->* Kd (0 :: Us) 0 (iter v (U 0) B).
Proof.
  induction v; intros Us B.
  - apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, KR2 |].
    follow (R1iter (B + 2) (v :: Us) 1).
    rewrite iter_S', U_0. replace (3 * B + 7) with (1 + 3 * (B + 2)) by lia.
    apply IHv.
Qed.

Definition CDPx (j : nat) : Prop := forall v Us B, 2 * j <= B ->
  Kd (repeat 0 j ++ v :: Us) 0 B -->* Kd (repeat 0 (S j) ++ Us) 0 (iter v (U j) B).

(** n twos cleared at depths t .. t+n-1 *)
Fixpoint Yb (t n x : nat) : nat :=
  match n with
  | O => x
  | S n' => U (t + n') (U (t + n') (Yb t n' x))
  end.

Lemma Yb_X : forall j, Yb 0 j 7 = X j.
Proof. induction j. - reflexivity. - simpl Yb. rewrite IHj, X_S. reflexivity. Qed.

Lemma Yb_ge : forall t n x, 2 * t <= x -> 2 * (t + n) <= Yb t n x.
Proof.
  intros t n x Hx. destruct n as [| n']. - simpl. lia.
  - simpl Yb. pose proof (Ugrow (t + n') (U (t + n') (Yb t n' x))). lia.
Qed.

Lemma BLKx : forall D, (forall j', j' < D -> CDPx j') ->
  forall n t V x, t + n <= D -> 2 * t <= x ->
  Kd (repeat 0 t ++ repeat 2 n ++ V) 0 x -->* Kd (repeat 0 (t + n) ++ V) 0 (Yb t n x).
Proof.
  intros D HD. induction n as [| n IHn]; intros t V x Hd Hx.
  - replace (t + 0) with t by lia. apply evstep_refl.
  - rewrite <- repeat_snoc.
    follow (IHn t (2 :: V) x ltac:(lia) Hx).
    follow (HD (t + n) ltac:(lia) 2 V (Yb t n x) (Yb_ge t n x Hx)).
    replace (t + S n) with (S (t + n)) by lia. apply evstep_refl.
Qed.

Lemma CDPx_all : forall j, CDPx j.
Proof.
  intro j. induction j as [j IH] using lt_wf_ind.
  destruct j as [| n].
  - intros v Us B _. simpl. apply CHx.
  - intro v. induction v as [| w IHw]; intros Us B HB.
    + rewrite repeat_snoc. apply evstep_refl.
    + remember (B - 2 * S n) as s eqn:Hs.
      assert (HB' : B = 2 * S n + s) by lia.
      assert (Hr : Kd (repeat 0 (S n) ++ S w :: Us) 0 B -->*
                   Kd (repeat 2 n ++ S (S s) :: w :: Us) 0 7).
      { rewrite HB'. eapply evstep_trans; [apply progress_evstep, KR3 |].
        follow (R1iter 2 (repeat 2 n ++ S (S s) :: w :: Us) 1). finish. }
      follow Hr.
      follow (BLKx (S n) IH n 0 (S (S s) :: w :: Us) 7 ltac:(lia) ltac:(lia)).
      rewrite Yb_X.
      follow (IH n ltac:(lia) (S (S s)) (w :: Us) (X n) ltac:(pose proof (Xgrow n); lia)).
      replace (iter (S (S s)) (U n) (X n)) with (U (S n) B)
        by (rewrite U_S; f_equal; lia).
      follow (IHw Us (U (S n) B) ltac:(pose proof (Ugrow (S n) B); lia)).
      rewrite iter_S'. apply evstep_refl.
Qed.


(** ** Residues mod 8 (new): from depth 2 on, one unit sends even b to 7 and odd b to 0 (mod 8) *)

Lemma U1_mod8 : forall n,
  (n mod 4 = 0 -> iter n (U 0) 7 mod 8 = 7) /\ (n mod 4 = 1 -> iter n (U 0) 7 mod 8 = 4) /\
  (n mod 4 = 2 -> iter n (U 0) 7 mod 8 = 3) /\ (n mod 4 = 3 -> iter n (U 0) 7 mod 8 = 0).
Proof.
  induction n.
  - cbn [iter]. repeat split; intros; mods; lia.
  - cbn [iter]. rewrite U_0. destruct IHn as [H0 [H1 [H2 H3]]].
    repeat split; intros; mods; lia.
Qed.

Lemma U1_x : forall x, U 1 x = iter x (U 0) 7.
Proof. intros. rewrite U_S, X_0. f_equal. lia. Qed.

Lemma U1_0 : forall y, y mod 4 = 0 -> U 1 y mod 8 = 7.
Proof. intros y Hy. rewrite U1_x. apply (U1_mod8 y). exact Hy. Qed.

Lemma U1_3 : forall y, y mod 4 = 3 -> U 1 y mod 8 = 0.
Proof. intros y Hy. rewrite U1_x. apply (U1_mod8 y). exact Hy. Qed.

Lemma X1_val : X 1 = 91.
Proof. rewrite X_S, X_0, !U_0. reflexivity. Qed.

Lemma m8_4_0 : forall y, y mod 8 = 0 -> y mod 4 = 0.
Proof. intros; mods; lia. Qed.

Lemma m8_4_3 : forall y, y mod 8 = 7 -> y mod 4 = 3.
Proof. intros; mods; lia. Qed.

(** iterating U 1 from 91 (= 3 mod 4): 0, 7, 0, 7, ... (mod 8) *)
Lemma U2_orbit : forall n, (n mod 2 = 1 -> iter n (U 1) 91 mod 8 = 0) /\
  (1 <= n -> n mod 2 = 0 -> iter n (U 1) 91 mod 8 = 7).
Proof.
  induction n as [| n [H1 H2]].
  - split; intros; mods; lia.
  - cbn [iter]. split.
    + intros Hn. destruct n as [| n'].
      * cbn [iter]. apply U1_3. reflexivity.
      * apply U1_3, m8_4_3. apply H2; [lia | mods; lia].
    + intros _ Hn. apply U1_0, m8_4_0. apply H1. mods; lia.
Qed.

Definition Pm8 (j : nat) : Prop :=
  (forall x, 2 * j <= x -> (x mod 2 = 0 -> U j x mod 8 = 7) /\ (x mod 2 = 1 -> U j x mod 8 = 0)) /\ X j mod 8 = 7.

Lemma Pm8_2 : Pm8 2.
Proof.
  split.
  - intros x Hx. rewrite U_S, X1_val.
    destruct (U2_orbit (x - 2 * 1)) as [H1 H2].
    split; intros Hp; [apply H2 | apply H1]; mods; lia.
  - rewrite X_S, X1_val. apply U1_0, m8_4_0. apply (proj1 (U2_orbit 1)). reflexivity.
Qed.

Lemma iter_m8 : forall j, (forall x, 2 * j <= x -> (x mod 2 = 0 -> U j x mod 8 = 7) /\ (x mod 2 = 1 -> U j x mod 8 = 0)) ->
  forall n x, 2 * j <= x -> x mod 8 = 7 ->
    2 * j <= iter n (U j) x /\ (n mod 2 = 0 -> iter n (U j) x mod 8 = 7) /\ (n mod 2 = 1 -> iter n (U j) x mod 8 = 0).
Proof.
  intros j Hj. induction n as [| n IH]; intros x Hx H7.
  - cbn [iter]. repeat split; intros; [lia | assumption | mods; lia].
  - destruct (IH x Hx H7) as [G1 [G2 G3]]. cbn [iter].
    pose proof (Ugrow j (iter n (U j) x)). destruct (Hj _ G1) as [K0 K1].
    repeat split; [lia | |]; intros Hn.
    + apply K0. assert (Hn' : n mod 2 = 1) by (mods; lia). specialize (G3 Hn'). mods; lia.
    + apply K1. assert (Hn' : n mod 2 = 0) by (mods; lia). specialize (G2 Hn'). mods; lia.
Qed.

Lemma Pm8_S : forall j, 2 <= j -> Pm8 j -> Pm8 (S j).
Proof.
  intros j Hj [Hu Hx]. pose proof (Xgrow j) as HXg.
  split.
  - intros x Hx'. rewrite U_S.
    destruct (iter_m8 j Hu (x - 2 * j) (X j) ltac:(lia) Hx) as [_ [H0 H1]].
    split; intros Hp; [apply H0 | apply H1]; mods; lia.
  - rewrite X_S.
    destruct (iter_m8 j Hu 2 (X j) ltac:(lia) Hx) as [_ [H0 _]]. apply H0. reflexivity.
Qed.

Lemma Pm8_all : forall j, 2 <= j -> Pm8 j.
Proof.
  intros j Hj. induction j as [| j IH]; [lia |].
  destruct (Nat.eq_dec j 1) as [-> | Hne]; [exact Pm8_2 |].
  apply Pm8_S; [lia | apply IH; lia].
Qed.

Lemma U_mod8 : forall j x, 2 <= j -> 2 * j <= x ->
  (x mod 2 = 0 -> U j x mod 8 = 7) /\ (x mod 2 = 1 -> U j x mod 8 = 0).
Proof. intros j x Hj Hx. apply (proj1 (Pm8_all j Hj)). exact Hx. Qed.

(** ** Clearing the rebuilt lists *)

(** clearing the m (0,0,3) triples of trip m from depth j *)
Fixpoint Tpre (m j B : nat) : nat :=
  match m with
  | O => B
  | S m' => Tpre m' (j + 3) (iter 3 (U (j + 2)) B)
  end.

Definition Tv (m j B : nat) : nat := U (j + 3 * m + 2) (U (j + 3 * m + 2) (Tpre m j B)).

Lemma Tpre_par : forall m j B, 2 * (j + 2) <= B ->
  2 * (j + 3 * m + 2) <= Tpre m j B /\ Tpre m j B mod 2 = (B + 3 * m) mod 2.
Proof.
  induction m; intros j B HB.
  - cbn [Tpre]. split; [lia | f_equal; lia].
  - cbn [Tpre].
    destruct (iter_par (U (j + 2)) (2 * (j + 2)) (Ustep (j + 2)) 3 B HB) as [H1 H2].
    assert (Hg : B + 2 * (j + 2) + 5 <= iter 3 (U (j + 2)) B).
    { cbn [iter]. pose proof (Ugrow (j + 2) B). pose proof (Ugrow (j + 2) (U (j + 2) B)).
      pose proof (Ugrow (j + 2) (U (j + 2) (U (j + 2) B))). lia. }
    destruct (IHm (j + 3) (iter 3 (U (j + 2)) B) ltac:(lia)) as [H3 H4].
    split; [lia |]. rewrite H4. mods; lia.
Qed.

Lemma TRIPS : forall m j B, 2 * (j + 2) <= B ->
  Kd (repeat 0 j ++ trip m) 0 B -->* Kd (repeat 0 (j + 3 * m) ++ [0; 0; 2]) 0 (Tpre m j B).
Proof.
  induction m; intros j B HB.
  - replace (j + 3 * 0) with j by lia. apply evstep_refl.
  - cbn [trip Tpre]. rewrite (repeat_snoc 0 j), (repeat_snoc 0 (S j)).
    follow (CDPx_all (S (S j)) 3 (trip m) B ltac:(lia)).
    assert (Hg : B + 2 * (j + 2) + 5 <= iter 3 (U (j + 2)) B).
    { cbn [iter]. pose proof (Ugrow (j + 2) B). pose proof (Ugrow (j + 2) (U (j + 2) B)).
      pose proof (Ugrow (j + 2) (U (j + 2) (U (j + 2) B))). lia. }
    replace (S (S (S j))) with (j + 3) by lia. replace (S (S j)) with (j + 2) by lia.
    follow (IHm (j + 3) (iter 3 (U (j + 2)) B) ltac:(lia)).
    replace (j + 3 + 3 * m) with (j + 3 * S m) by lia. apply evstep_refl.
Qed.

Lemma TRIP_ALL : forall m j B, 2 * (j + 2) <= B ->
  Kd (repeat 0 j ++ trip m) 0 B -->* Kd (repeat 0 (j + 3 * m + 3)) 0 (Tv m j B).
Proof.
  intros m j B HB.
  follow (TRIPS m j B HB).
  destruct (Tpre_par m j B HB) as [H1 _].
  rewrite (repeat_snoc 0 (j + 3 * m)), (repeat_snoc 0 (S (j + 3 * m))).
  follow (CDPx_all (S (S (j + 3 * m))) 2 [] (Tpre m j B) ltac:(lia)).
  rewrite app_nil_r. unfold Tv. cbn [iter].
  replace (S (S (S (j + 3 * m)))) with (j + 3 * m + 3) by lia.
  replace (S (S (j + 3 * m))) with (j + 3 * m + 2) by lia. apply evstep_refl.
Qed.

Lemma Tv_par : forall m j B, 2 * (j + 2) <= B -> Tv m j B mod 2 = (B + 3 * m) mod 2.
Proof.
  intros m j B HB. destruct (Tpre_par m j B HB) as [H1 H2]. unfold Tv.
  set (D := j + 3 * m + 2) in *. set (z := Tpre m j B) in *.
  pose proof (Ugrow D z).
  pose proof (Upar D z ltac:(lia)) as P1. pose proof (Upar D (U D z) ltac:(lia)) as P2.
  mods; lia.
Qed.

Lemma Tv_big : forall m j B, 2 * (j + 2) <= B -> 2 * (j + 3 * m + 2) <= Tpre m j B /\ 2 * (j + 3 * m + 3) <= Tv m j B.
Proof.
  intros m j B HB. destruct (Tpre_par m j B HB) as [H1 _]. split; [exact H1 |]. unfold Tv.
  pose proof (Ugrow (j + 3 * m + 2) (Tpre m j B)). pose proof (Ugrow (j + 3 * m + 2) (U (j + 3 * m + 2) (Tpre m j B))). lia.
Qed.

(** b mod 8 after the last digit (a 2 at depth >= 2): 0 if the counter before it was even *)
Lemma Tv_mod8 : forall m j B, 2 * (j + 2) <= B -> (B + 3 * m) mod 2 = 0 -> Tv m j B mod 8 = 0.
Proof.
  intros m j B HB Hp. destruct (Tpre_par m j B HB) as [H1 H2]. unfold Tv.
  set (D := j + 3 * m + 2) in *. set (z := Tpre m j B) in *.
  assert (Hz : z mod 2 = 0) by (rewrite H2; exact Hp).
  pose proof (Ugrow D z).
  destruct (U_mod8 D z ltac:(lia) ltac:(lia)) as [Z0 _]. specialize (Z0 Hz).
  destruct (U_mod8 D (U D z) ltac:(lia) ltac:(lia)) as [_ Z1]. apply Z1. mods; lia.
Qed.

(** ** The run *)

Definition b1 : nat := Tv 7 1 7.
Definition second (b : nat) : nat := Tv (b / 4) 1 7.
Definition b2 : nat := second b1.

Lemma b1_def : b1 = Tv 7 1 7.
Proof. reflexivity. Qed.

Lemma b2_def : b2 = second b1.
Proof. reflexivity. Qed.

Opaque b1 b2 Tv.

Lemma b1_mod8 : b1 mod 8 = 0.
Proof. rewrite b1_def. apply Tv_mod8; [lia | reflexivity]. Qed.

Lemma div8 : forall x, x mod 8 = 0 -> x = 4 * (x / 4) /\ (x / 4) mod 2 = 0.
Proof. intros x Hx. pose proof (Nat.div_mod_eq x 4). mods; lia. Qed.

Lemma second_odd : forall b, b mod 8 = 0 -> second b mod 2 = 1.
Proof.
  intros b Hb. unfold second. destruct (div8 b Hb) as [_ Hq].
  rewrite Tv_par; [| lia]. set (q := b / 4) in *. mods; lia.
Qed.

Lemma b2_odd : b2 mod 2 = 1.
Proof. rewrite b2_def. apply second_odd, b1_mod8. Qed.

Lemma odd_half : forall x, x mod 2 = 1 -> x = 2 * (x / 2) + 1.
Proof. intros; mods; lia. Qed.

(** clearing a rebuilt list (1 :: trip m) from Kd _ 0 0 *)
Lemma clear_rebuilt : forall m, Kd (1%nat :: trip m) 0 0 -->* Kd (repeat 0 (1 + 3 * m + 3)) 0 (Tv m 1 7).
Proof.
  intros m.
  change (Kd (1%nat :: trip m) 0 0) with (Kd (repeat 0 0 ++ 1%nat :: trip m) 0 0).
  follow (CDPx_all 0 1 (trip m) 0 ltac:(lia)).
  change (iter 1 (U 0) 0) with (U 0 0). rewrite U_0. change (3 * 0 + 7) with 7.
  apply (TRIP_ALL m 1 7 ltac:(lia)).
Qed.

Lemma run1 : c0 -->* Kd (repeat 0 (1 + 3 * 7 + 3)) 0 b1.
Proof.
  follow init_reach.
  change (Kd [2%nat] 0 0) with (Kd (repeat 0 0 ++ [2%nat]) 0 0).
  follow (CDPx_all 0 2 [] 0 ltac:(lia)).
  change (iter 2 (U 0) 0) with (U 0 (U 0 0)). rewrite !U_0. rewrite app_nil_r.
  change (3 * (3 * 0 + 7) + 7) with (4 * 7).
  eapply evstep_trans; [apply progress_evstep, (KR4E4 1 7) |].
  follow (clear_rebuilt 7). rewrite b1_def. apply evstep_refl.
Qed.

Lemma run2_gen : forall k b, b mod 8 = 0 -> Kd (repeat 0 k) 0 b -->* c_end (second b / 2).
Proof.
  intros k b Hb.
  destruct (div8 b Hb) as [Hq _].
  rewrite Hq at 1.
  eapply evstep_trans; [apply progress_evstep, (KR4E4 k (b / 4)) |].
  follow (clear_rebuilt (b / 4)).
  rewrite (odd_half (Tv (b / 4) 1 7)) by (apply (second_odd b Hb)).
  apply KR4Ox.
Qed.

Lemma run2 : c0 -->* c_end (b2 / 2).
Proof. follow run1. rewrite b2_def. apply run2_gen, b1_mod8. Qed.

Theorem halt : halts tm c0.
Proof.
  destruct (with_counter run2) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. apply c_end_halted.
Qed.

(* ==================================================================================================== *)
(*                        bb8_list/proofs/BB10_champion_bound.v: its exact score                        *)
(* ==================================================================================================== *)

(* The earlier file(s) of this module made these constants Opaque; in the multi-file build
   this file started with them transparent (Opaque is not carried over by Require). *)
Transparent U X b1 b2 Tv.

(* Each original file started with the symbol scope on top (from Individual102's `Open Scope sym`);
   restore that here, since the previous part may have ended in nat_scope. *)
Local Open Scope sym_scope.

(** * A machine-checked score for the BB(10) champion *)

(** Machine (Racheline 2024, wiki "Champions" table, listed as sigma > f_omega^2(25) = f_omega(f_omega(25))):
      1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ
    The machine table [tm], the digit family [Kd], the rules and the run are imported unchanged from
    BB10_champion_1RB1RA.v (which proves [halt : halts tm c0] and passes check.py).  Generated by
    bb8_list/investigations/bb10_champion_1RB1RA_0LF0LJ/coq/gen_bound.py; the fast-growing-hierarchy lemmas are those
    of BB9_champion_bound.v (same clearing functions U, X).

    Main results (no axioms):
      Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (b2 + 3).
      Theorem sigma_lower_bound :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega (f_omega 25) < N + 1.
      Theorem sigma_lower_bound_strong : exists c N b, c0 -->* c /\ halted tm c /\ ones c N /\
        2 ^ 25 * f 25 (f 25 2) <= b /\ b mod 8 = 0 /\ f_omega (3 * (b / 4) + 3) < N + 1.     (b = b1)

    Definitions as in BB9_champion_bound.v: f 0 n = n + 1, f (k+1) n = (f k)^n (n), f_omega n = f n n;
    [ones c N]: the tape of c holds exactly N ones.  busycoq stops before the halting transition E0 = 1RZ, which
    writes one more 1 (the head reads 0 in [c_end]), so the standard score is N + 1 = b2 + 4.

    Exact values:  b1 = Tv 7 1 7,  b2 = Tv (b1/4) 1 7,  Tv m j B = U (j+3m+2) (U (j+3m+2) (Tpre m j B)),
    Tpre clears the m (0,0,3) triples of trip m from depth j (digit 3 at depths j+2, j+5, ..., j+3m-1). *)



Import Coq.micromega.Lia Coq.Arith.PeanoNat Coq.Lists.List Coq.Arith.Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

(** The imported [tm] is the declared machine (BB10_champion_1RB1RA.v passes check.py, which checks this). *)
(* machine: 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ *)
Lemma tm_table :
  tm (A, 0) = Some (1, R, B) /\ tm (A, 1) = Some (1, R, A) /\
  tm (B, 0) = Some (0, L, C) /\ tm (B, 1) = Some (0, L, F) /\
  tm (C, 0) = Some (0, R, D) /\ tm (C, 1) = Some (1, L, C) /\
  tm (D, 0) = Some (1, R, A) /\ tm (D, 1) = Some (1, R, G) /\
  tm (E, 0) = None           /\ tm (E, 1) = Some (0, R, A) /\
  tm (F, 0) = Some (1, L, B) /\ tm (F, 1) = Some (1, L, F) /\
  tm (G, 0) = Some (1, L, H) /\ tm (G, 1) = Some (1, R, E) /\
  tm (H, 0) = Some (0, L, I) /\ tm (H, 1) = Some (1, L, H) /\
  tm (I, 0) = Some (0, L, F) /\ tm (I, 1) = Some (0, L, J) /\
  tm (J, 0) = Some (1, L, H) /\ tm (J, 1) = Some (0, L, J).
Proof. repeat split. Qed.

Local Open Scope nat_scope.

(** Never let a tactic compute these numbers (Opaque declarations are not exported by the imported file). *)
Opaque U X Tv b1 b2.

(** ** Definitions used in the statement *)

(** The fast-growing hierarchy: f 0 n = n + 1, f (k+1) n = (f k)^n (n), f_omega n = f n n.
    ([iter n g x] = g^n(x) is defined in BB10_champion_1RB1RA.v: iter 0 g x = x, iter (S n) g x = g (iter n g x).) *)
Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | O => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.

Definition sym_val (s : Sym) : nat :=
  match s with
  | S0 => 0
  | S1 => 1
  end.

Fixpoint count1 (xs : list Sym) : nat :=
  match xs with
  | [] => 0
  | x :: t => sym_val x + count1 t
  end.

(** [ones c N]: the tape of c is  L (reversed, left of the head), s (head cell), R (right of the head),
    with 0s beyond both lists, and N = number of 1s in L, s, R. *)
Definition ones (c : state * tape) (N : nat) : Prop :=
  exists (q : state) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

Lemma count1_blocks : forall m, count1 ([S0; S1; S1]^^m) = 2 * m.
Proof. induction m. - reflexivity. - simpl. rewrite IHm. lia. Qed.

Lemma ones_c_end : forall m, ones (c_end m) (2 * m + 4).
Proof.
  intros m. exists E, ([S1; S1; S0; S1; S1] ++ [S0; S1; S1]^^m), (@nil Sym), S0. split.
  - reflexivity.
  - simpl. rewrite count1_blocks. lia.
Qed.

(** Domination of iterates through the scaling z >= K n. *)
Lemma iter_dom : forall K g h, (forall n z, K * n <= z -> K * g n <= h z) ->
  forall m n z, K * n <= z -> K * iter m g n <= iter m h z.
Proof. intros K g h Hd. induction m; intros n z Hz; simpl; auto. Qed.

(** ** The fast-growing hierarchy: basic facts *)

Lemma f_S : forall k n, f (S k) n = iter n (f k) n.
Proof. reflexivity. Qed.

Lemma f_props : forall k, (forall n, n <= f k n) /\ (forall a b, a <= b -> f k a <= f k b).
Proof.
  induction k as [| k [Hid Hmono]].
  - split; intros; simpl; lia.
  - split.
    + intros n. rewrite f_S. apply iter_ge. exact Hid.
    + intros a b Hab. rewrite !f_S. transitivity (iter a (f k) b).
      * apply iter_mono_x; assumption.
      * apply iter_mono_n; assumption.
Qed.

Lemma f_id : forall k n, n <= f k n.
Proof. intros. apply f_props. Qed.

Lemma f_mono : forall k a b, a <= b -> f k a <= f k b.
Proof. intros. apply f_props. assumption. Qed.

Lemma f_gt : forall k n, 1 <= n -> n < f k n.
Proof.
  induction k; intros n Hn.
  - simpl. lia.
  - rewrite f_S. destruct n as [| n']; [lia |].
    simpl. pose proof (iter_ge (f k) (f_id k) n' (S n')).
    specialize (IHk (iter n' (f k) (S n')) ltac:(lia)). lia.
Qed.

Lemma f_level : forall k n, 1 <= n -> f k n <= f (S k) n.
Proof.
  intros k n Hn. rewrite f_S. destruct n as [| n']; [lia |].
  rewrite iter_S'. apply iter_ge. apply f_id.
Qed.

Lemma f_level_mono : forall d k n, 1 <= n -> f k n <= f (d + k) n.
Proof.
  induction d; intros k n Hn. - reflexivity.
  - specialize (IHd k n Hn). pose proof (f_level (d + k) n Hn). change (S d + k) with (S (d + k)). lia.
Qed.

Lemma iter_succ_add : forall n x, iter n S x = n + x.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

Lemma f1 : forall n, f 1 n = 2 * n.
Proof. intros. rewrite f_S. rewrite iter_succ_add. lia. Qed.

Lemma f_dbl : forall k n, 1 <= k -> 2 * n <= f k n.
Proof.
  intros k n Hk. destruct n as [| n']. - lia.
  - rewrite <- f1. replace k with ((k - 1) + 1) by lia. apply f_level_mono. lia.
Qed.

(** ** The lower bound for U: level j+1 of the fast-growing hierarchy, with scaling 2^(j+1) *)

Lemma pow2_ge : forall j, j + 2 <= 2 ^ (j + 1).
Proof. induction j. - simpl. lia. - change (S j + 1) with (S (j + 1)). rewrite Nat.pow_succ_r'. lia. Qed.

Lemma bound : forall j,
  (forall n z, 2 ^ (j + 1) * n <= z -> 2 ^ (j + 1) * f (S j) n <= U j z) /\
  2 ^ (j + 2) * (j + 1) <= X j.
Proof.
  induction j as [| j [Hu Hx]].
  - split.
    + intros n z Hz. rewrite U_0, f1. simpl (2 ^ (0 + 1)) in *. lia.
    + rewrite X_0. simpl. lia.
  - pose proof (pow2_ge j) as HKj.
    set (K := 2 ^ (j + 1)) in *.
    assert (HK1 : 2 ^ (S j + 1) = 2 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    assert (HK2 : 2 ^ (j + 2) = 2 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    assert (HK3 : 2 ^ (S j + 2) = 4 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    rewrite HK2 in Hx.
    assert (HX1 : K * 1 <= X j) by nia.
    split.
    + intros n y Hy. rewrite HK1 in *. rewrite U_S, f_S.
      destruct n as [| n']. { simpl. lia. }
      set (n := S n') in *.
      assert (Hm : 2 * n + 1 <= y - 2 * j) by nia.
      pose proof (iter_dom K (f (S j)) (U j) Hu (y - 2 * j) 1 (X j) HX1) as Hd.
      assert (Hc : 2 * iter n (f (S j)) n <= iter (y - 2 * j) (f (S j)) 1).
      { transitivity (iter (2 * n + 1) (f (S j)) 1).
        2:{ apply iter_mono_n; [apply f_id | exact Hm]. }
        replace (2 * n + 1) with (1 + (n + n)) by lia. rewrite !iter_add.
        change (iter 1 (f (S j)) ?z) with (f (S j) z).
        pose proof (iter_lin1 (f (S j)) ltac:(intros a Ha; pose proof (f_gt (S j) a Ha); lia) n 1 ltac:(lia)).
        pose proof (iter_mono_x (f (S j)) (f_mono (S j)) n n (iter n (f (S j)) 1) ltac:(lia)).
        pose proof (f_dbl (S j) (iter n (f (S j)) (iter n (f (S j)) 1)) ltac:(lia)).
        lia. }
      nia.
    + rewrite HK3, X_S.
      pose proof (Hu (2 * (j + 1)) (X j) ltac:(nia)) as H1.
      pose proof (f_dbl (S j) (2 * (j + 1)) ltac:(lia)) as H2.
      pose proof (Hu (4 * (j + 1)) (U j (X j)) ltac:(nia)) as H3.
      pose proof (f_dbl (S j) (4 * (j + 1)) ltac:(lia)) as H4.
      nia.
Qed.

Lemma Ubound : forall j n z, 2 ^ (j + 1) * n <= z -> 2 ^ (j + 1) * f (S j) n <= U j z.
Proof. intro j. apply (proj1 (bound j)). Qed.

Lemma Xbound : forall j, 2 ^ (j + 2) * (j + 1) <= X j.
Proof. intro j. apply (proj2 (bound j)). Qed.


(** ** The run's two clearings, from below *)

Lemma Tpre_last : forall m j B, Tpre (S m) j B = iter 3 (U (j + 3 * m + 2)) (Tpre m j B).
Proof.
  induction m; intros j B.
  - cbn [Tpre]. replace (j + 3 * 0 + 2) with (j + 2) by lia. reflexivity.
  - change (Tpre (S (S m)) j B) with (Tpre (S m) (j + 3) (iter 3 (U (j + 2)) B)).
    rewrite IHm. cbn [Tpre]. replace (j + 3 + 3 * m + 2) with (j + 3 * S m + 2) by lia. reflexivity.
Qed.

Lemma Tv_unfold : forall m j B, Tv m j B = U (j + 3 * m + 2) (U (j + 3 * m + 2) (Tpre m j B)).
Proof. Transparent Tv. reflexivity. Qed.
Opaque Tv.

Lemma f3_2 : f 3 2 = 2048.
Proof. reflexivity. Qed.

Opaque f.

(** b1 >= 2^25 * f_25(f_25(2)) *)
Lemma b1_big : 2 ^ 25 * f 25 (f 25 2) <= b1.
Proof.
  rewrite b1_def, Tv_unfold. change (1 + 3 * 7 + 2) with 24.
  rewrite (Tpre_last 6 1 7). change (1 + 3 * 6 + 2) with 21.
  set (T6 := Tpre 6 1 7). cbn [iter].
  pose proof (U_ge_X 20 (U 21 (U 21 T6))) as Hz. change (S 20) with 21 in Hz.
  pose proof (Xbound 20) as HX. change (2 ^ (20 + 2)) with (2 ^ 22) in HX.
  assert (Hn : 2 ^ (21 + 1) * 21 <= U 21 (U 21 T6)).
  { change (2 ^ (21 + 1)) with (2 ^ 22). pose proof (U_ge_X 20 (U 21 T6)) as Hz'. change (S 20) with 21 in Hz'. nia. }
  pose proof (Ubound 21 21 _ Hn) as H7. change (S 21) with 22 in H7. change (2 ^ (21 + 1)) with (2 ^ 22) in H7.
  pose proof (f_dbl 22 21 ltac:(lia)) as Hd.
  assert (H2 : 2 ^ (24 + 1) * 2 <= U 21 (U 21 (U 21 T6))).
  { replace (24 + 1) with (22 + 3) by lia. rewrite Nat.pow_add_r. change (2 ^ 3) with 8.
    set (P := 2 ^ 22) in *. set (Z := U 21 (U 21 (U 21 T6))) in *. nia. }
  pose proof (Ubound 24 2 _ H2) as H8. change (S 24) with 25 in H8.
  pose proof (Ubound 24 (f 25 2) _ H8) as H9. change (S 24) with 25 in H9. change (2 ^ (24 + 1)) with (2 ^ 25) in H9.
  exact H9.
Qed.

Lemma f25_2 : 25 <= f 25 2.
Proof.
  pose proof (f_level_mono 22 3 2 ltac:(lia)) as H. change (22 + 3) with 25 in H. rewrite f3_2 in H. lia.
Qed.

Lemma quarter_aux : forall b y z P, P * y <= b -> z <= y -> 4 <= P -> z <= b / 4.
Proof. intros b y z P H1 H2 H3. apply Nat.div_le_lower_bound; [lia | nia]. Qed.

Lemma b1_quarter : f 25 25 <= b1 / 4.
Proof.
  assert (Hp : 2 ^ 2 <= 2 ^ 25) by (apply Nat.pow_le_mono_r; lia). change (2 ^ 2) with 4 in Hp.
  exact (quarter_aux b1 _ _ _ b1_big (f_mono 25 25 (f 25 2) f25_2) Hp).
Qed.

(** b2 = Tv m 1 7 >= f_omega (3m + 3): the deepest digit of the second list sits at depth 3m + 3 *)
Lemma second_big : forall m, f_omega (3 * m + 3) <= Tv m 1 7.
Proof.
  intros m. rewrite Tv_unfold. replace (1 + 3 * m + 2) with (S (3 * m + 2)) by lia.
  set (J := S (3 * m + 2)). set (w := Tpre m 1 7).
  pose proof (U_ge_X (3 * m + 2) w) as Hw. fold J in Hw.
  pose proof (Xbound (3 * m + 2)) as HX.
  replace (3 * m + 2 + 2) with (J + 1) in HX by (unfold J; lia).
  replace (3 * m + 2 + 1) with J in HX by (unfold J; lia).
  assert (Hn : 2 ^ (J + 1) * J <= U J w) by lia.
  pose proof (Ubound J J _ Hn) as Hb.
  assert (L1 : f J J <= f (S J) J) by (apply f_level; unfold J; lia).
  assert (L2 : 1 <= 2 ^ (J + 1)) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  unfold f_omega. replace (3 * m + 3) with J by (unfold J; lia).
  set (P := 2 ^ (J + 1)) in *. set (y := f (S J) J) in *. set (Z := U J (U J w)) in *. nia.
Qed.

Lemma f_omega_mono : forall a b, 1 <= a -> a <= b -> f_omega a <= f_omega b.
Proof.
  intros a b Ha Hab. unfold f_omega.
  pose proof (f_level_mono (b - a) a a Ha) as L1. replace (b - a + a) with b in L1 by lia.
  pose proof (f_mono b a b Hab). lia.
Qed.

(** ** Main theorems *)

Lemma ones_odd : forall b, b mod 2 = 1 -> ones (c_end (b / 2)) (b + 3).
Proof.
  intros b Hb. pose proof (odd_half b Hb) as Hb'.
  replace (b + 3) with (2 * (b / 2) + 4) by lia. apply ones_c_end.
Qed.

Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (b2 + 3).
Proof.
  exists (c_end (b2 / 2)). split; [exact run2 |]. split; [apply c_end_halted |].
  apply ones_odd, b2_odd.
Qed.

Lemma b2_big : f_omega (3 * (b1 / 4) + 3) <= b2.
Proof. rewrite b2_def. unfold second. apply second_big. Qed.

Theorem sigma_lower_bound_strong : exists c N b, c0 -->* c /\ halted tm c /\ ones c N /\
  2 ^ 25 * f 25 (f 25 2) <= b /\ b mod 8 = 0 /\ f_omega (3 * (b / 4) + 3) < N + 1.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (b2 + 3), b1.
  (* explicit splits: [repeat split] would try eq_refl on [b1 mod 8 = 0] and evaluate b1 *)
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  split; [exact b1_big |]. split; [exact b1_mod8 |].
  pose proof b2_big as Hb. set (t := f_omega (3 * (b1 / 4) + 3)) in *. lia.
Qed.

Lemma final_arith : forall q v, f 25 25 <= q -> f_omega (3 * q + 3) <= v -> f_omega (f_omega 25) < v + 3 + 1.
Proof.
  intros q v Hq Hv.
  assert (Hpos : 1 <= f_omega 25) by (unfold f_omega; pose proof (f_id 25 25); lia).
  assert (Hle : f_omega 25 <= 3 * q + 3) by (unfold f_omega; lia).
  pose proof (f_omega_mono _ _ Hpos Hle). lia.
Qed.

Theorem sigma_lower_bound : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega (f_omega 25) < N + 1.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (b2 + 3).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  exact (final_arith (b1 / 4) b2 b1_quarter b2_big).
Qed.

End Champion10.

(* ==================================================================================================== *)
(*                             Module Lead10: the 10-state candidate 0LJ0LC                             *)
(* ==================================================================================================== *)

Module Lead10.

(* ==================================================================================================== *)
(*                    bb8_list/proofs/BB10_lead_1RB0RA.v: the candidate 0LJ0LC halts                    *)
(* ==================================================================================================== *)

(* Each original file started with the symbol scope on top (from Individual102's `Open Scope sym`);
   restore that here, since the previous part may have ended in nat_scope. *)
Local Open Scope sym_scope.

(** * BB(10) candidate 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LJ0LC_1RG1LD_0RI0RH_1RG1LF_1RE1RI_---1LC halts *)

(** Generated by bb8_list/autoproof (engine.py: symbolic execution with automatic loop lemmas; coqgen.py). *)

(** Machine-checked halting proof (bb8_list/investigations/bb10_lead_0LJ0LC.md).  Generated by
    bb8_list/investigations/bb10_lead_0LJ0LC/coq/gen_final.py: the machine-level lemmas of Part 1 come from the
    symbolic explorer (mexp.py, autoproof engine; waypoints in parts2.py), Parts 2-3 (glue.v.in) are hand-written.

    Family (head in G on the blank right of the word; the word read from the left):
      N a k g l = 0^inf .. l .. (10)^g 1 ((10) 1)^k (10)^a 1 G> 0^inf
    i.e. an accumulator of a units (a = 2b+1 for the counter b), k zero digits ((10) 1, one unit), then a group of
    g units (a digit d has g = 2d+1; the top entry of a rebuilt list has an even number of units), then the rest.
    Rules (all parameters):
      NR1   : N a 0 (n+2) l                  -->* N (a+4) 0 n l                               (b -> b+2)
      NR23  : N a (k+1) (n+3) (1 l)          -->* N 1 k (a+4) ((10)^(n+1) 1 l)              (borrow, b -> 0)
      NR23z : N a (k+1) 2 (1 0^inf)          -->* N 1 k (a+4) (1 1 0^inf)                   (top entry 2 -> 0)
      REBUILD: all M+2 digits zero           -->* N 1 (2a+M+6) 6 (1 0^inf)                   (top entry 6)
      HALTN : N a (L+2) 0 (1 0^inf)          -->* cH a (L+1), J reads 0 (J0 undefined)
    Clearing: F 0 b = b+2, F (k+1) b = (F k)^(b+2) (0); a digit with u units at depth k maps b to (F k)^u b.
    Run: blank -> N 1 26 5 (step 3890) -> exhausted list of 27 zero digits with b_f = (F 26)^2 0
         -> rebuilt list: top entry 6 over L = 4 b_f + 33 zero digits -> b_2 = (F L)^3 0 -> halt. *)


Import Coq.micromega.Lia Coq.Arith.PeanoNat Coq.Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LJ0LC_1RG1LD_0RI0RH_1RG1LF_1RE1RI_---1LC *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (0, R, A)
  | B, 0 => Some (1, L, C)  | B, 1 => Some (1, L, F)
  | C, 0 => Some (1, R, D)  | C, 1 => Some (0, L, B)
  | D, 0 => Some (1, R, A)  | D, 1 => Some (1, L, E)
  | E, 0 => Some (0, L, J)  | E, 1 => Some (0, L, C)
  | F, 0 => Some (1, R, G)  | F, 1 => Some (1, L, D)
  | G, 0 => Some (0, R, I)  | G, 1 => Some (0, R, H)
  | H, 0 => Some (1, R, G)  | H, 1 => Some (1, L, F)
  | I, 0 => Some (1, R, E)  | I, 1 => Some (1, R, I)
  | J, 0 => None            | J, 1 => Some (1, L, C)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** ** Tape normalization (as in the hand-written proofs, e.g. BB8_048631_1RB0RG.v) *)

Lemma align_lpow : forall (x : Sym) xs ys n,
  (x::xs)^^n *> x >> ys = x >> (xs ++ [x])^^n *> ys.
Proof.
  induction n.
  - reflexivity.
  - simpl. repeat rewrite Str_app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma align_lpow_const : forall (x : Sym) xs n,
  (x::xs)^^n *> const x = x >> (xs ++ [x])^^n *> const x.
Proof. intros. rewrite const_unfold at 1. apply align_lpow. Qed.

Ltac align_tape := repeat ((rewrite align_lpow || rewrite align_lpow_const); simpl app).
Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
(** Adjacent powers of the same block, in either order (crossing a run pushes its powers in reverse order). *)
Lemma lpow_merge : forall (xs : list Sym) n m Y, xs^^n *> xs^^m *> Y = xs^^(n + m) *> Y.
Proof. intros. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

(** Blank cells in front of the blank tail. *)
Lemma zero_const : (0 >> const 0 : side) = const 0.
Proof. symmetry. apply const_unfold. Qed.

Ltac finish_norm := apply evstep_refl'; norm_nat; align_tape; repeat rewrite lpow_merge; repeat rewrite zero_const;
  try reflexivity; lia_refl.

Lemma lpow_snoc : forall (xs : list Sym) n Y, xs^^(S n) *> Y = xs^^n *> xs *> Y.
Proof. intros. simpl. rewrite <- lpow_shift. apply Str_app_assoc. Qed.

Lemma cr_BL_01_01 : forall n l r, [0;1]^^n *> l <{{B}} r -->* l <{{B}} [0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_HR_01_01 : forall n l r, l {{H}}> [0;1]^^n *> r -->* [0;1]^^n *> l {{H}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.


Lemma R1_st1 : forall a n l, (1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> l) {{G}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1]^^n *> l) {{G}}> (const 0).
Proof.
  intros. do 8 step. follow cr_BL_01_01. do 3 step. follow cr_HR_01_01. do 9 step.
  follow cr_BL_01_01. do 7 step. follow cr_HR_01_01. do 5 step. finish_norm.
Qed.

Lemma R2_st1 : forall a n l, (1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{G}}> (const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> ([1;0]^^a *> const 0).
Proof.
  intros. do 8 step. follow cr_BL_01_01. do 3 step. follow cr_HR_01_01. do 9 step.
  follow cr_BL_01_01. do 13 step. repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow_const 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma R2_st3 : forall i2 n n3 l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i2 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> (1 >> 0 >> [1;0]^^n3 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i2 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> ([1;0]^^n3 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma R2_round2 : forall n3 i2 n l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i2 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> (1 >> 0 >> [1;0]^^n3 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i2 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> ([1;0]^^n3 *> const 0).
Proof.
  intros. follow R2_st3. finish_norm.
Qed.

Lemma R2_loop4 : forall n1 i2 n l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i2 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> ([1;0]^^n1 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i2 *> [0;1]^^n1 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> (const 0).
Proof.
  induction n1; intros.
  - finish_norm.
  - follow (R2_round2 n1 i2 n l).
    follow (IHn1 (S i2) n l).
    finish_norm.
Qed.

Lemma R2_loop4_z : forall a n l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> ([1;0]^^a *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> (const 0).
Proof.
  intros. follow (R2_loop4 a 0 n l). finish_norm.
Qed.

Lemma R2_st5 : forall a n l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> (const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 0 >> 1 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{G}}> (const 0).
Proof.
  intros. do 13 step. follow cr_BL_01_01. do 3 step. follow cr_HR_01_01. do 16 step. finish_norm.
Qed.

Lemma R2z_st1 : forall a, (1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> const 0) {{G}}> (const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^a *> const 0).
Proof.
  intros. do 8 step. follow cr_BL_01_01. do 3 step. follow cr_HR_01_01. do 9 step.
  follow cr_BL_01_01. do 13 step. repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow_const 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma R2z_st3 : forall i6 n7, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i6 *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n7 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i6 *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n7 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma R2z_round2 : forall n7 i6, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i6 *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n7 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i6 *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n7 *> const 0).
Proof.
  intros. follow R2z_st3. finish_norm.
Qed.

Lemma R2z_loop4 : forall n5 i6, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i6 *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n5 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i6 *> [0;1]^^n5 *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> (const 0).
Proof.
  induction n5; intros.
  - finish_norm.
  - follow (R2z_round2 n5 i6).
    follow (IHn5 (S i6)).
    finish_norm.
Qed.

Lemma R2z_loop4_z : forall a, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^a *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> (const 0).
Proof.
  intros. follow (R2z_loop4 a 0). finish_norm.
Qed.

Lemma R2z_st5 : forall a, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> (const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 0 >> 1 >> 1 >> 1 >> const 0) {{G}}> (const 0).
Proof.
  intros. do 13 step. follow cr_BL_01_01. do 3 step. follow cr_HR_01_01. do 16 step. finish_norm.
Qed.

Lemma PRE_st1 : forall a k P, (1 >> [0;1]^^a *> [1;0;1]^^k *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> P) {{G}}> (const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^k *> P) {{B}}> ([1;0]^^a *> const 0).
Proof.
  intros. do 8 step. follow cr_BL_01_01. repeat rewrite (align_lpow 1 [0;1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 0 [1;1]). simpl app. do 2 step. follow cr_HR_01_01. do 9 step.
  follow cr_BL_01_01. do 2 step. repeat rewrite (align_lpow 1 [1;0]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0;1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 0 [1;1]). simpl app. do 9 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow_const 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma PRE_st3 : forall i10 k n11 P, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i10 *> 1 >> 1 >> [0;1;1]^^k *> P) {{B}}> (1 >> 0 >> [1;0]^^n11 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i10 *> 1 >> 1 >> [0;1;1]^^k *> P) {{B}}> ([1;0]^^n11 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma PRE_round2 : forall n11 i10 k P, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i10 *> 1 >> 1 >> [0;1;1]^^k *> P) {{B}}> (1 >> 0 >> [1;0]^^n11 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i10 *> 1 >> 1 >> [0;1;1]^^k *> P) {{B}}> ([1;0]^^n11 *> const 0).
Proof.
  intros. follow PRE_st3. finish_norm.
Qed.

Lemma PRE_loop4 : forall n9 i10 k P, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i10 *> 1 >> 1 >> [0;1;1]^^k *> P) {{B}}> ([1;0]^^n9 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i10 *> [0;1]^^n9 *> 1 >> 1 >> [0;1;1]^^k *> P) {{B}}> (const 0).
Proof.
  induction n9; intros.
  - finish_norm.
  - follow (PRE_round2 n9 i10 k P).
    follow (IHn9 (S i10) k P).
    finish_norm.
Qed.

Lemma PRE_loop4_z : forall a k P, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^k *> P) {{B}}> ([1;0]^^a *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [0;1;1]^^k *> P) {{B}}> (const 0).
Proof.
  intros. follow (PRE_loop4 a 0 k P). finish_norm.
Qed.

Lemma PRE_st5 : forall a k P, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [0;1;1]^^k *> P) {{B}}> (const 0) -->* (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [0;1;1]^^k *> P) <{{E}} (1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 5 step. finish_norm.
Qed.

Lemma WALK_st1 : forall a i j P, (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^j *> P) {{E}}> (1 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^j *> P) {{B}}> ([1;0]^^a *> 0 >> [1;0;1]^^i *> const 0).
Proof.
  intros. do 8 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma WALK_st3 : forall i i14 j n15 P, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i14 *> 1 >> 1 >> [0;1;1]^^j *> P) {{B}}> (1 >> 0 >> [1;0]^^n15 *> 0 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i14 *> 1 >> 1 >> [0;1;1]^^j *> P) {{B}}> ([1;0]^^n15 *> 0 >> [1;0;1]^^i *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma WALK_round2 : forall n15 i14 i j P, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i14 *> 1 >> 1 >> [0;1;1]^^j *> P) {{B}}> (1 >> 0 >> [1;0]^^n15 *> 0 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i14 *> 1 >> 1 >> [0;1;1]^^j *> P) {{B}}> ([1;0]^^n15 *> 0 >> [1;0;1]^^i *> const 0).
Proof.
  intros. follow WALK_st3. finish_norm.
Qed.

Lemma WALK_loop4 : forall n13 i14 i j P, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i14 *> 1 >> 1 >> [0;1;1]^^j *> P) {{B}}> ([1;0]^^n13 *> 0 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i14 *> [0;1]^^n13 *> 1 >> 1 >> [0;1;1]^^j *> P) {{B}}> (0 >> [1;0;1]^^i *> const 0).
Proof.
  induction n13; intros.
  - finish_norm.
  - follow (WALK_round2 n13 i14 i j P).
    follow (IHn13 (S i14) i j P).
    finish_norm.
Qed.

Lemma WALK_loop4_z : forall a i j P, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^j *> P) {{B}}> ([1;0]^^a *> 0 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [0;1;1]^^j *> P) {{B}}> (0 >> [1;0;1]^^i *> const 0).
Proof.
  intros. follow (WALK_loop4 a 0 i j P). finish_norm.
Qed.

Lemma WALK_st5 : forall a i j P, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [0;1;1]^^j *> P) {{B}}> (0 >> [1;0;1]^^i *> const 0) -->* (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [0;1;1]^^j *> P) <{{E}} (1 >> 0 >> 1 >> [1;0;1]^^i *> const 0).
Proof.
  intros. do 5 step. finish_norm.
Qed.

Lemma BOR_st1 : forall a k n l, (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{E}}> (1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. do 8 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma BOR_st3 : forall i18 k n n19 l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i18 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> (1 >> 0 >> [1;0]^^n19 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i18 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> ([1;0]^^n19 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma BOR_round2 : forall n19 i18 k n l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i18 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> (1 >> 0 >> [1;0]^^n19 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i18 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> ([1;0]^^n19 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. follow BOR_st3. finish_norm.
Qed.

Lemma BOR_loop4 : forall n17 i18 k n l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i18 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> ([1;0]^^n17 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i18 *> [0;1]^^n17 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  induction n17; intros.
  - finish_norm.
  - follow (BOR_round2 n17 i18 k n l).
    follow (IHn17 (S i18) k n l).
    finish_norm.
Qed.

Lemma BOR_loop4_z : forall a k n l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. follow (BOR_loop4 a 0 k n l). finish_norm.
Qed.

Lemma BOR_st5 : forall a k n l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 0 >> 1 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{G}}> (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. do 13 step. follow cr_BL_01_01. do 3 step. follow cr_HR_01_01. do 14 step. finish_norm.
Qed.

Lemma BORz_st1 : forall a k, (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> const 0) {{E}}> (1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. do 8 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma BORz_st3 : forall i22 k n23, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i22 *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n23 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i22 *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n23 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma BORz_round2 : forall n23 i22 k, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i22 *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n23 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i22 *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n23 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. follow BORz_st3. finish_norm.
Qed.

Lemma BORz_loop4 : forall n21 i22 k, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i22 *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n21 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i22 *> [0;1]^^n21 *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  induction n21; intros.
  - finish_norm.
  - follow (BORz_round2 n21 i22 k).
    follow (IHn21 (S i22) k).
    finish_norm.
Qed.

Lemma BORz_loop4_z : forall a k, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. follow (BORz_loop4 a 0 k). finish_norm.
Qed.

Lemma BORz_st5 : forall a k, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 0 >> 1 >> 1 >> 1 >> const 0) {{G}}> (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. do 13 step. follow cr_BL_01_01. do 3 step. follow cr_HR_01_01. do 14 step. finish_norm.
Qed.

Lemma BORn_st1 : forall a k, (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{E}}> (1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. do 8 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma BORn_st3 : forall i26 k n27, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i26 *> 1 >> 0 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n27 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i26 *> 1 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n27 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma BORn_round2 : forall n27 i26 k, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i26 *> 1 >> 0 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n27 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i26 *> 1 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n27 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. follow BORn_st3. finish_norm.
Qed.

Lemma BORn_loop4 : forall n25 i26 k, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i26 *> 1 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n25 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i26 *> [0;1]^^n25 *> 1 >> 0 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  induction n25; intros.
  - finish_norm.
  - follow (BORn_round2 n25 i26 k).
    follow (IHn25 (S i26) k).
    finish_norm.
Qed.

Lemma BORn_loop4_z : forall a k, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. follow (BORn_loop4 a 0 k). finish_norm.
Qed.

Lemma BORn_st5 : forall a k, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 0 >> 1 >> 1 >> const 0) {{G}}> (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. do 13 step. follow cr_BL_01_01. do 3 step. follow cr_HR_01_01. do 14 step. finish_norm.
Qed.

Lemma RET_st1 : forall i j T, (1 >> 1 >> [0;1;1]^^i *> T) {{G}}> (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^j *> const 0) -->* (1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i *> T) {{G}}> (1 >> 0 >> 0 >> [1;0;1]^^j *> const 0).
Proof.
  intros. do 9 step. finish_norm.
Qed.

Lemma END_st1 : forall a k T, (1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^k *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> T) {{G}}> (1 >> 0 >> 0 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^k *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> T) {{G}}> (const 0).
Proof.
  intros. do 2 step. finish_norm.
Qed.

Lemma LASTW_st1 : forall a i, (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> const 0) {{E}}> (1 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> [1;0;1]^^i *> const 0).
Proof.
  intros. do 8 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma LASTW_st3 : forall i i30 n31, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i30 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n31 *> 0 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i30 *> const 0) {{B}}> ([1;0]^^n31 *> 0 >> [1;0;1]^^i *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma LASTW_round2 : forall n31 i30 i, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i30 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n31 *> 0 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i30 *> const 0) {{B}}> ([1;0]^^n31 *> 0 >> [1;0;1]^^i *> const 0).
Proof.
  intros. follow LASTW_st3. finish_norm.
Qed.

Lemma LASTW_loop4 : forall n29 i30 i, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i30 *> const 0) {{B}}> ([1;0]^^n29 *> 0 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i30 *> [0;1]^^n29 *> const 0) {{B}}> (0 >> [1;0;1]^^i *> const 0).
Proof.
  induction n29; intros.
  - finish_norm.
  - follow (LASTW_round2 n29 i30 i).
    follow (IHn29 (S i30) i).
    finish_norm.
Qed.

Lemma LASTW_loop4_z : forall a i, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> const 0) {{B}}> (0 >> [1;0;1]^^i *> const 0).
Proof.
  intros. follow (LASTW_loop4 a 0 i). finish_norm.
Qed.

Lemma LASTW_st5 : forall a i, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> const 0) {{B}}> (0 >> [1;0;1]^^i *> const 0) -->* (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> const 0) <{{E}} (1 >> 0 >> 1 >> [1;0;1]^^i *> const 0).
Proof.
  intros. do 5 step. finish_norm.
Qed.

Lemma YC_st1 : forall i u, (1 >> 0 >> 1 >> [0;1]^^u *> const 0) {{E}}> (1 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^u *> 0 >> [1;0;1]^^i *> const 0).
Proof.
  intros. do 4 step. follow cr_BL_01_01. do 7 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma YC_st3 : forall i i34 n35, (1 >> 0 >> 0 >> 1 >> [0;1]^^i34 *> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n35 *> 0 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i34 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n35 *> 0 >> [1;0;1]^^i *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma YC_round2 : forall n35 i34 i, (1 >> 0 >> 0 >> 1 >> [0;1]^^i34 *> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n35 *> 0 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i34 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n35 *> 0 >> [1;0;1]^^i *> const 0).
Proof.
  intros. follow YC_st3. finish_norm.
Qed.

Lemma YC_loop4 : forall n33 i34 i, (1 >> 0 >> 0 >> 1 >> [0;1]^^i34 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n33 *> 0 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i34 *> [0;1]^^n33 *> 1 >> 1 >> const 0) {{B}}> (0 >> [1;0;1]^^i *> const 0).
Proof.
  induction n33; intros.
  - finish_norm.
  - follow (YC_round2 n33 i34 i).
    follow (IHn33 (S i34) i).
    finish_norm.
Qed.

Lemma YC_loop4_z : forall i u, (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^u *> 0 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^u *> 1 >> 1 >> const 0) {{B}}> (0 >> [1;0;1]^^i *> const 0).
Proof.
  intros. follow (YC_loop4 u 0 i). finish_norm.
Qed.

Lemma YC_st5 : forall i u, (1 >> 0 >> 0 >> 1 >> [0;1]^^u *> 1 >> 1 >> const 0) {{B}}> (0 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^u *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. finish_norm.
Qed.

Lemma YC_st7 : forall i i38 n39, (1 >> 0 >> 0 >> 1 >> [0;1]^^i38 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n39 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i38 *> const 0) {{B}}> ([1;0]^^n39 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma YC_round6 : forall n39 i38 i, (1 >> 0 >> 0 >> 1 >> [0;1]^^i38 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n39 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i38 *> const 0) {{B}}> ([1;0]^^n39 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0).
Proof.
  intros. follow YC_st7. finish_norm.
Qed.

Lemma YC_loop8 : forall n37 i38 i, (1 >> 0 >> 0 >> 1 >> [0;1]^^i38 *> const 0) {{B}}> ([1;0]^^n37 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i38 *> [0;1]^^n37 *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0).
Proof.
  induction n37; intros.
  - finish_norm.
  - follow (YC_round6 n37 i38 i).
    follow (IHn37 (S i38) i).
    finish_norm.
Qed.

Lemma YC_loop8_z : forall i u, (1 >> 0 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^u *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^u *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0).
Proof.
  intros. follow (YC_loop8 u 0 i). finish_norm.
Qed.

Lemma YC_st9 : forall i u, (1 >> 0 >> 0 >> 1 >> [0;1]^^u *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0) -->* (1 >> 1 >> [0;1]^^u *> const 0) <{{E}} (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0).
Proof.
  intros. do 5 step. finish_norm.
Qed.

Lemma YEND_st1 : forall i, (1 >> const 0) {{E}}> (1 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{H}}> ([1;0;1]^^i *> const 0).
Proof.
  intros. do 26 step. finish_norm.
Qed.

Lemma YEND_st3 : forall i42 n43, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> 0 >> 1 >> const 0) {{H}}> (1 >> 0 >> 1 >> [1;0;1]^^n43 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> 0 >> 1 >> const 0) {{H}}> ([1;0;1]^^n43 *> const 0).
Proof.
  intros. do 5 step. finish_norm.
Qed.

Lemma YEND_round2 : forall n43 i42, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> 0 >> 1 >> const 0) {{H}}> (1 >> 0 >> 1 >> [1;0;1]^^n43 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> 0 >> 1 >> const 0) {{H}}> ([1;0;1]^^n43 *> const 0).
Proof.
  intros. follow YEND_st3. finish_norm.
Qed.

Lemma YEND_loop4 : forall n41 i42, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> 0 >> 1 >> const 0) {{H}}> ([1;0;1]^^n41 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> [1;0;1]^^n41 *> 0 >> 1 >> const 0) {{H}}> (const 0).
Proof.
  induction n41; intros.
  - finish_norm.
  - follow (YEND_round2 n41 i42).
    follow (IHn41 (S i42)).
    finish_norm.
Qed.

Lemma YEND_loop4_z : forall i, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{H}}> ([1;0;1]^^i *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> 0 >> 1 >> const 0) {{H}}> (const 0).
Proof.
  intros. follow (YEND_loop4 i 0). finish_norm.
Qed.

Lemma YEND_st5 : forall i, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> 0 >> 1 >> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> 0 >> 1 >> const 0) {{G}}> (const 0).
Proof.
  intros. do 1 step. finish_norm.
Qed.

Lemma HEND_st1 : forall a i, (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> const 0) {{E}}> (1 >> [1;0;1]^^i *> const 0) -->* (const 0) <{{J}} (0 >> 1 >> 1 >> 1 >> [0;1]^^a *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> [1;0;1]^^i *> const 0).
Proof.
  intros. do 8 step. follow cr_BL_01_01. do 4 step. finish_norm.
Qed.

Lemma R1 : forall a n l, (1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> l) {{G}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^n *> l) {{G}}> (const 0).
Proof.
  intros.
  follow R1_st1.
  finish_norm.
Qed.

Lemma R2 : forall a n l (Hpos_a : 0 < a), (1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{G}}> (const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{G}}> (const 0).
Proof.
  intros.
  follow R2_st1.
  follow R2_loop4_z.
  follow R2_st5.
  finish_norm.
Qed.

Lemma R2z : forall a (Hpos_a : 0 < a), (1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> const 0) {{G}}> (const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> const 0) {{G}}> (const 0).
Proof.
  intros.
  follow R2z_st1.
  follow R2z_loop4_z.
  follow R2z_st5.
  finish_norm.
Qed.

Lemma PRE : forall a k P (Hpos_a : 0 < a), (1 >> [0;1]^^a *> [1;0;1]^^k *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> P) {{G}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [0;1;1]^^k *> P) {{E}}> (1 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros.
  follow PRE_st1.
  follow PRE_loop4_z.
  follow PRE_st5.
  finish_norm.
Qed.

Lemma WALK : forall a i j P (Hpos_a : 0 < a), (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^j *> P) {{E}}> (1 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [0;1;1]^^j *> P) {{E}}> (1 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0).
Proof.
  intros.
  follow WALK_st1.
  follow WALK_loop4_z.
  follow WALK_st5.
  finish_norm.
Qed.

Lemma BOR : forall a k n l (Hpos_a : 0 < a), (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{E}}> (1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> [0;1]^^n *> 1 >> l) {{G}}> (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros.
  follow BOR_st1.
  follow BOR_loop4_z.
  follow BOR_st5.
  finish_norm.
Qed.

Lemma BORz : forall a k (Hpos_a : 0 < a), (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> const 0) {{E}}> (1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> const 0) {{G}}> (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros.
  follow BORz_st1.
  follow BORz_loop4_z.
  follow BORz_st5.
  finish_norm.
Qed.

Lemma BORn : forall a k (Hpos_a : 0 < a), (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{E}}> (1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> const 0) {{G}}> (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros.
  follow BORn_st1.
  follow BORn_loop4_z.
  follow BORn_st5.
  finish_norm.
Qed.

Lemma RET : forall i j T, (1 >> 1 >> [0;1;1]^^i *> T) {{G}}> (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^j *> const 0) -->* (1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i *> T) {{G}}> (1 >> 0 >> 0 >> [1;0;1]^^j *> const 0).
Proof.
  intros.
  follow RET_st1.
  finish_norm.
Qed.

Lemma END : forall a k T, (1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^k *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> T) {{G}}> (1 >> 0 >> 0 >> const 0) -->* (1 >> 0 >> 1 >> [1;0;1]^^k *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> T) {{G}}> (const 0).
Proof.
  intros.
  follow END_st1.
  finish_norm.
Qed.

Lemma LASTW : forall a i (Hpos_a : 0 < a), (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> const 0) {{E}}> (1 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> const 0) {{E}}> (1 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0).
Proof.
  intros.
  follow LASTW_st1.
  follow LASTW_loop4_z.
  follow LASTW_st5.
  finish_norm.
Qed.

Lemma YC : forall i u, (1 >> 0 >> 1 >> [0;1]^^u *> const 0) {{E}}> (1 >> [1;0;1]^^i *> const 0) -->* (1 >> [0;1]^^u *> const 0) {{E}}> (1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0).
Proof.
  intros.
  follow YC_st1.
  follow YC_loop4_z.
  follow YC_st5.
  follow YC_loop8_z.
  follow YC_st9.
  finish_norm.
Qed.

Lemma YEND : forall i, (1 >> const 0) {{E}}> (1 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i *> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> (const 0).
Proof.
  intros.
  follow YEND_st1.
  follow YEND_loop4_z.
  follow YEND_st5.
  finish_norm.
Qed.

Lemma HEND : forall a i (Hpos_a : 0 < a), exists c, (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> const 0) {{E}}> (1 >> [1;0;1]^^i *> const 0) -->* c /\ halted tm c.
Proof.
  intros. eexists. split.
  - apply HEND_st1.
  - simpl. reflexivity.
Qed.




(** * Part 2: the n-list family and its rules (hand-written glue over the generated lemmas above) *)

Lemma pow_S : forall (xs : list Sym) n Y, xs^^(S n) *> Y = xs *> xs^^n *> Y.
Proof. intros. simpl. apply Str_app_assoc. Qed.

Lemma zeros_snoc : forall k X, [1;0;1]^^(S k) *> X = [1;0;1]^^k *> 1 >> 0 >> 1 >> X.
Proof. intros. rewrite lpow_snoc. reflexivity. Qed.

Lemma zeros_snoc2 : forall k X, [1;0;1]^^(S (S k)) *> X = [1;0;1]^^k *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> X.
Proof. intros. rewrite !lpow_snoc. reflexivity. Qed.

(** One group (10)^n 1 of the word, read from the head side: 1 (01)^n. *)
Definition grp (n : nat) (l : side) : side := 1 >> [0;1]^^n *> l.

(** N a k g l = 0^inf .. l .. (10)^g 1 ((10) 1)^k (10)^a 1 G> 0^inf : accumulator with a units, k zero digits
    (one unit each), then a group with g units, then the rest l of the word (read from the head side). *)
Definition N (a k g : nat) (l : side) : Q * tape := (grp a ([1;0;1]^^k *> grp g l)) {{G}}> const 0.

(** Walk / return / left-end shapes of the generated lemmas. *)
Definition Wc (a j i : nat) (P : side) : Q * tape :=
  (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [0;1;1]^^j *> P) {{E}}> (1 >> [1;0;1]^^i *> const 0).
Definition Rc (i j : nat) (T : side) : Q * tape :=
  (1 >> 1 >> [0;1;1]^^i *> T) {{G}}> (1 >> 0 >> 0 >> [1;0;1]^^j *> const 0).
Definition Yc (u i : nat) : Q * tape := (1 >> [0;1]^^u *> const 0) {{E}}> (1 >> [1;0;1]^^i *> const 0).

Lemma WALKS : forall j a i P, 0 < a -> Wc a j i P -->* Wc a 0 (j + i) P.
Proof.
  induction j; intros a i P Ha.
  - apply evstep_refl.
  - eapply evstep_trans; [exact (WALK a i j P Ha) |].
    replace (S j + i) with (j + S i) by lia. exact (IHj a (S i) P Ha).
Qed.

Lemma RETS : forall j i T, Rc i j T -->* Rc (i + j) 0 T.
Proof.
  induction j; intros i T.
  - rewrite Nat.add_0_r. apply evstep_refl.
  - eapply evstep_trans; [exact (RET i j T) |].
    replace (i + S j) with (S i + j) by lia. exact (IHj (S i) T).
Qed.

Lemma YCS : forall u i, Yc u i -->* Yc 0 (i + 2 * u).
Proof.
  induction u; intros i.
  - rewrite Nat.add_0_r. apply evstep_refl.
  - eapply evstep_trans; [exact (YC i u) |].
    replace (i + 2 * S u) with (S (S i) + 2 * u) by lia. exact (IHu (S (S i))).
Qed.

(** The common part of a borrow over k+2 zero digits: PRE, the walk, and (after the borrow lemma) the return. *)
Lemma R3_walk : forall a k P, 0 < a ->
  (grp a ([1;0;1]^^(S (S k)) *> 1 >> P)) {{G}}> const 0 -->* Wc a 0 (S k) P.
Proof.
  intros a k P Ha. unfold grp. rewrite zeros_snoc2.
  eapply evstep_trans; [exact (PRE a k P Ha) |].
  replace (S k) with (k + 1) by lia. exact (WALKS k a 1 P Ha).
Qed.

Lemma R3_ret : forall a k T,
  Rc 0 (S k) (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> T) -->*
  (grp 1 ([1;0;1]^^(S k) *> grp (S (S (S (S a)))) (1 >> T))) {{G}}> const 0.
Proof.
  intros a k T.
  eapply evstep_trans; [exact (RETS (S k) 0 _) |].
  unfold grp. rewrite zeros_snoc. exact (END a k T).
Qed.

(** ** The rules on the family (every one checked against the literal machine in verify_rules.py) *)

Lemma NR1 : forall a n l, N a 0 (S (S n)) l -->* N (S (S (S (S a)))) 0 n l.
Proof. intros. exact (R1 a n l). Qed.

Lemma NR23 : forall a k n l, 0 < a ->
  N a (S k) (S (S (S n))) (1 >> l) -->* N 1 k (S (S (S (S a)))) (grp (S n) (1 >> l)).
Proof.
  intros a k n l Ha. destruct k as [| k].
  - exact (R2 a n l Ha).
  - unfold N.
    eapply evstep_trans; [exact (R3_walk a k ([0;1]^^(S (S (S n))) *> 1 >> l) Ha) |].
    eapply evstep_trans; [exact (BOR a k n l Ha) |].
    exact (R3_ret a k (0 >> 1 >> [0;1]^^n *> 1 >> l)).
Qed.

Lemma NR23z : forall a k, 0 < a ->
  N a (S k) 2 (1 >> const 0) -->* N 1 k (S (S (S (S a)))) (grp 0 (1 >> const 0)).
Proof.
  intros a k Ha. destruct k as [| k].
  - exact (R2z a Ha).
  - unfold N.
    eapply evstep_trans; [exact (R3_walk a k (0 >> 1 >> 0 >> 1 >> 1 >> const 0) Ha) |].
    eapply evstep_trans; [exact (BORz a k Ha) |].
    exact (R3_ret a k (1 >> const 0)).
Qed.

(** The rebuild: all M >= 2 digits zero (the top digit is a zero digit too) -> top entry 6, 2a+M+4 zero digits. *)
Definition Ex (a M : nat) : Q * tape := (grp a ([1;0;1]^^M *> 1 >> const 0)) {{G}}> const 0.

Lemma REBUILD : forall a M, 0 < a -> Ex a (S (S M)) -->* N 1 (2 * a + M + 6) 6 (1 >> const 0).
Proof.
  intros a M Ha. unfold Ex.
  eapply evstep_trans; [exact (R3_walk a M (const 0) Ha) |].
  eapply evstep_trans; [exact (LASTW a (S M) Ha) |].
  eapply evstep_trans; [exact (YCS (S (S (S a))) (S (S M))) |].
  replace (S (S M) + 2 * S (S (S a))) with (S (2 * a + M + 7)) by lia.
  eapply evstep_trans; [exact (YEND (2 * a + M + 7)) |].
  replace (2 * a + M + 7) with (S (S (2 * a + M + 5))) by lia.
  rewrite zeros_snoc2.
  eapply evstep_trans; [exact (PRE 2 (2 * a + M + 5) (0 >> 1 >> 0 >> 1 >> const 0) ltac:(lia)) |].
  eapply evstep_trans; [exact (WALKS (2 * a + M + 5) 2 1 _ ltac:(lia)) |].
  replace (2 * a + M + 5 + 1) with (S (2 * a + M + 5)) by lia.
  eapply evstep_trans; [exact (BORn 2 (2 * a + M + 5) ltac:(lia)) |].
  replace (2 * a + M + 6) with (S (2 * a + M + 5)) by lia.
  exact (R3_ret 2 (2 * a + M + 5) (const 0)).
Qed.

(** The halt: top entry 0 (the word starts 11), L >= 2 zero digits.  cH is the halting configuration (state J
    reads a 0: J0 is undefined). *)
Definition cH (a i : nat) : Q * tape :=
  (const 0) <{{J}} (0 >> 1 >> 1 >> 1 >> [0;1]^^a *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> [1;0;1]^^i *> const 0).

Lemma cH_halted : forall a i, halted tm (cH a i).
Proof. intros. unfold cH. simpl. reflexivity. Qed.

Lemma HALTN : forall a L, 0 < a -> N a (S (S L)) 0 (1 >> const 0) -->* cH a (S L).
Proof.
  intros a L Ha. unfold N.
  eapply evstep_trans; [exact (R3_walk a L (1 >> const 0) Ha) |].
  exact (HEND_st1 a (S L)).
Qed.

Lemma Neq : forall x j u l, N x j 1 (grp u l) = N x (S j) u l.
Proof. intros. unfold N, grp. rewrite (zeros_snoc j). reflexivity. Qed.

(** * Part 3: the abstract run *)

Fixpoint iter (n : nat) (g : nat -> nat) (x : nat) : nat :=
  match n with
  | O => x
  | S n' => g (iter n' g x)
  end.

Lemma iter_S' : forall n g x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

(** F k b: the accumulator b' after clearing ONE unit of a digit at depth k (k zero digits between it and the
    accumulator), starting from accumulator b (accumulator b = 2b+1 units).  F 0 b = b + 2 (rule R1);
    F (k+1) b = (F k)^(b+2) (0) (rule R23 writes the digit b+2 at depth k and resets the accumulator to 0). *)
Fixpoint F (k : nat) : nat -> nat :=
  match k with
  | O => fun b => b + 2
  | S j => fun b => iter (b + 2) (F j) 0
  end.

Lemma F_S : forall j b, F (S j) b = iter (b + 2) (F j) 0.
Proof. reflexivity. Qed.

(** Clearing a digit with u units (2u+1 cells) at depth k. *)
Lemma CLR : forall k u b l, N (2 * b + 1) k (2 * u + 1) (1 >> l) -->* N (2 * iter u (F k) b + 1) k 1 (1 >> l).
Proof.
  induction k as [| j IHj]; intros u; induction u as [| u IHu]; intros b l.
  - apply evstep_refl.
  - replace (2 * S u + 1) with (S (S (2 * u + 1))) by lia.
    eapply evstep_trans; [exact (NR1 (2 * b + 1) (2 * u + 1) (1 >> l)) |].
    replace (S (S (S (S (2 * b + 1))))) with (2 * (b + 2) + 1) by lia.
    rewrite iter_S'. exact (IHu (b + 2) l).
  - apply evstep_refl.
  - replace (2 * S u + 1) with (S (S (S (2 * u)))) by lia.
    eapply evstep_trans; [exact (NR23 (2 * b + 1) j (2 * u) l ltac:(lia)) |].
    replace (S (S (S (S (2 * b + 1))))) with (2 * (b + 2) + 1) by lia.
    change (N 1 j (2 * (b + 2) + 1) (grp (S (2 * u)) (1 >> l)))
      with (N (2 * 0 + 1) j (2 * (b + 2) + 1) (1 >> [0;1]^^(S (2 * u)) *> 1 >> l)).
    eapply evstep_trans; [exact (IHj (b + 2) 0%nat ([0;1]^^(S (2 * u)) *> 1 >> l)) |].
    change (1 >> [0;1]^^(S (2 * u)) *> 1 >> l) with (grp (S (2 * u)) (1 >> l)).
    rewrite Neq. replace (S (2 * u)) with (2 * u + 1) by lia.
    rewrite iter_S'. change (iter (b + 2) (F j) 0) with (F (S j) b).
    exact (IHu (F (S j) b) l).
Qed.

(** Clearing the top entry of a rebuilt list: 2u cells, its zero is 0 cells (the word then starts 11). *)
Lemma CLRtop : forall k u b, N (2 * b + 1) (S k) (2 * u) (1 >> const 0) -->*
  N (2 * iter u (F (S k)) b + 1) (S k) 0 (1 >> const 0).
Proof.
  intros k u. induction u as [| u IHu]; intros b.
  - apply evstep_refl.
  - destruct u as [| u].
    + change (2 * 1) with 2.
      eapply evstep_trans; [exact (NR23z (2 * b + 1) k ltac:(lia)) |].
      replace (S (S (S (S (2 * b + 1))))) with (2 * (b + 2) + 1) by lia.
      change (N 1 k (2 * (b + 2) + 1) (grp 0 (1 >> const 0)))
        with (N (2 * 0 + 1) k (2 * (b + 2) + 1) (1 >> [0;1]^^0 *> 1 >> const 0)).
      eapply evstep_trans; [exact (CLR k (b + 2) 0%nat ([0;1]^^0 *> 1 >> const 0)) |].
      change (1 >> [0;1]^^0 *> 1 >> const 0) with (grp 0 (1 >> const 0)).
      rewrite Neq. apply evstep_refl.
    + replace (2 * S (S u)) with (S (S (S (2 * u + 1)))) by lia.
      eapply evstep_trans; [exact (NR23 (2 * b + 1) k (2 * u + 1) (const 0) ltac:(lia)) |].
      replace (S (S (S (S (2 * b + 1))))) with (2 * (b + 2) + 1) by lia.
      change (N 1 k (2 * (b + 2) + 1) (grp (S (2 * u + 1)) (1 >> const 0)))
        with (N (2 * 0 + 1) k (2 * (b + 2) + 1) (1 >> [0;1]^^(S (2 * u + 1)) *> 1 >> const 0)).
      eapply evstep_trans; [exact (CLR k (b + 2) 0%nat ([0;1]^^(S (2 * u + 1)) *> 1 >> const 0)) |].
      change (1 >> [0;1]^^(S (2 * u + 1)) *> 1 >> const 0) with (grp (S (2 * u + 1)) (1 >> const 0)).
      rewrite Neq. replace (S (2 * u + 1)) with (2 * S u) by lia.
      rewrite iter_S'. change (iter (b + 2) (F k) 0) with (F (S k) b).
      exact (IHu (F (S k) b)).
Qed.

(** ** The run from the blank tape *)

Lemma init_reach : c0 -->* N 1 26 5 (1 >> const 0).
Proof.
  unfold c0, N, grp.
  do 3890 step.
  apply evstep_refl'. reflexivity.
Qed.

(** b_f: the accumulator at the first exhaustion; b_2: the final accumulator.  Both are sealed (Qed'd sigma
    types) so that no tactic can ever try to compute them. *)
Lemma bf_sig : { x : nat | x = iter 2 (F 26) 0 }.
Proof. exists (iter 2 (F 26) 0). reflexivity. Qed.
Definition bf : nat := proj1_sig bf_sig.
Lemma bf_eq : bf = iter 2 (F 26) 0.
Proof. exact (proj2_sig bf_sig). Qed.

Lemma b2_sig : { x : nat | x = iter 3 (F (4 * bf + 33)) 0 }.
Proof. exists (iter 3 (F (4 * bf + 33)) 0). reflexivity. Qed.
Definition b2 : nat := proj1_sig b2_sig.
Lemma b2_eq : b2 = iter 3 (F (4 * bf + 33)) 0.
Proof. exact (proj2_sig b2_sig). Qed.

Lemma first_clear : N 1 26 5 (1 >> const 0) -->* Ex (2 * bf + 1) 27.
Proof.
  change (N 1 26 5 (1 >> const 0)) with (N (2 * 0 + 1) 26 (2 * 2 + 1) (1 >> const 0)).
  eapply evstep_trans; [exact (CLR 26 2 0 (const 0)) |].
  rewrite <- bf_eq. unfold N, Ex, grp. rewrite (zeros_snoc 26). apply evstep_refl.
Qed.

Lemma rebuild_run : Ex (2 * bf + 1) 27 -->* N 1 (4 * bf + 33) 6 (1 >> const 0).
Proof.
  replace (4 * bf + 33) with (2 * (2 * bf + 1) + 25 + 6) by lia.
  exact (REBUILD (2 * bf + 1) 25 ltac:(lia)).
Qed.

Lemma second_clear : N 1 (4 * bf + 33) 6 (1 >> const 0) -->* N (2 * b2 + 1) (4 * bf + 33) 0 (1 >> const 0).
Proof.
  rewrite b2_eq.
  replace (4 * bf + 33) with (S (4 * bf + 32)) by lia.
  change (N 1 (S (4 * bf + 32)) 6 (1 >> const 0)) with (N (2 * 0 + 1) (S (4 * bf + 32)) (2 * 3) (1 >> const 0)).
  exact (CLRtop (4 * bf + 32) 3 0).
Qed.

Theorem run_to_halt : c0 -->* cH (2 * b2 + 1) (4 * bf + 32).
Proof.
  eapply evstep_trans; [exact init_reach |].
  eapply evstep_trans; [exact first_clear |].
  eapply evstep_trans; [exact rebuild_run |].
  eapply evstep_trans; [exact second_clear |].
  replace (4 * bf + 33) with (S (S (4 * bf + 31))) by lia.
  replace (4 * bf + 32) with (S (4 * bf + 31)) by lia.
  exact (HALTN (2 * b2 + 1) (4 * bf + 31) ltac:(lia)).
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct (with_counter run_to_halt) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. apply cH_halted.
Qed.

(* ==================================================================================================== *)
(*                          bb8_list/proofs/BB10_lead_bound.v: its exact score                          *)
(* ==================================================================================================== *)

(* Each original file started with the symbol scope on top (from Individual102's `Open Scope sym`);
   restore that here, since the previous part may have ended in nat_scope. *)
Local Open Scope sym_scope.

(** * Exact score of the BB(10) candidate 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LJ0LC_1RG1LD_0RI0RH_1RG1LF_1RE1RI_---1LC *)

(** Imports the halting proof BB10_lead_1RB0RA.v (Theorem halt; run_to_halt : c0 -->* cH (2 b2 + 1) (4 bf + 32)).
    Main results (no axioms):
      Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (2 * b2 + 2 * (4 * bf + 33) + 5).
      Lemma bf_closed : bf + 4 = arrow 27 2 3.
      Lemma b2_closed : b2 + 4 = arrow (4 * bf + 33) 2 5.
      Theorem score_closed : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
                             N + 1 = 2 * arrow (4 * bf + 33) 2 5 + 2 * (4 * bf + 33) - 2.
    [ones c N]: the tape of c holds exactly N ones; busycoq stops before the halting transition J0 (undefined, the
    head reads a 0), which writes one more 1 in the standard convention, so sigma = N + 1
      = 2 * (2 ^(L arrows) 5) + 2 L - 2,  L = 4 * (2 ^(27 arrows) 3) + 17.
    arrow k a b = a ^(k arrows) b with 0 arrows = multiplication (as in BB8_champ35_bound.v). *)



Import Coq.micromega.Lia Coq.Arith.PeanoNat Coq.Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

(** ** Counting ones *)

Definition sym_val (s : Sym) : nat :=
  match s with
  | S0 => 0
  | S1 => 1
  end.

Fixpoint count1 (xs : list Sym) : nat :=
  match xs with
  | [] => 0
  | x :: t => sym_val x + count1 t
  end.

(** [ones c n]: the tape of c is L (reversed, left of the head), s (head cell), R (right of the head), with 0s
    beyond both lists, and n = number of 1s in L, s, R. *)
Definition ones (c : state * tape) (n : nat) : Prop :=
  exists (q : state) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ n = count1 L + sym_val s + count1 R.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl; [reflexivity | rewrite IHxs; lia]. Qed.

Lemma count1_pow : forall xs m, count1 (xs^^m) = m * count1 xs.
Proof. intros xs m. induction m; simpl; [reflexivity | rewrite count1_app, IHm; lia]. Qed.

Lemma ones_cH : forall a i, ones (cH a i) (a + 2 * i + 6).
Proof.
  intros a i.
  exists J, (@nil Sym), ([S0; S1; S1; S1] ++ [S0; S1]^^a ++ [S0; S1; S0; S1; S0; S1; S0; S0] ++ [S1; S0; S1]^^i), S0.
  split.
  - unfold cH. rewrite !Str_app_assoc. reflexivity.
  - rewrite !count1_app, !count1_pow. simpl. lia.
Qed.

Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (2 * b2 + 2 * (4 * bf + 33) + 5).
Proof.
  exists (cH (2 * b2 + 1) (4 * bf + 32)). split; [exact run_to_halt |]. split; [apply cH_halted |].
  replace (2 * b2 + 2 * (4 * bf + 33) + 5) with ((2 * b2 + 1) + 2 * (4 * bf + 32) + 6) by lia.
  apply ones_cH.
Qed.

(** ** Knuth's up-arrows (as in BB8_champ35_bound.v) *)

Fixpoint arrow (k a b : nat) : nat :=
  match k with
  | O => a * b
  | S k' => Nat.iter b (arrow k' a) 1
  end.

Lemma arrow_S0 : forall k a, arrow (S k) a 0 = 1.
Proof. reflexivity. Qed.

Lemma arrow_SS : forall k a b, arrow (S k) a (S b) = arrow k a (arrow (S k) a b).
Proof. reflexivity. Qed.

Lemma arrow_0 : forall a b, arrow 0 a b = a * b.
Proof. reflexivity. Qed.

Lemma arrow_S_iter : forall k a b, arrow (S k) a b = iter b (arrow k a) 1.
Proof. induction b. - reflexivity. - rewrite arrow_SS, IHb. reflexivity. Qed.

Lemma arrow_one : forall k, arrow k 2 1 = 2.
Proof.
  induction k. - reflexivity.
  - change 1 with (S 0) at 2. rewrite arrow_SS, arrow_S0. exact IHk.
Qed.

Lemma arrow_two : forall k, arrow k 2 2 = 4.
Proof.
  induction k. - reflexivity.
  - change 2 with (S 1) at 2. rewrite arrow_SS, arrow_one. exact IHk.
Qed.

Opaque arrow.

Lemma iter_add : forall a b g x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

(** ** Closed forms of the clearing functions:  F (k+1) x + 4 = 2 ^(k arrows) (x + 4) *)

Lemma iter_F0 : forall n x, iter n (F 0) x = x + 2 * n.
Proof. induction n; intros; simpl. - lia. - rewrite IHn. lia. Qed.

Lemma F_closed : forall k x, F (S k) x + 4 = arrow k 2 (x + 4).
Proof.
  induction k as [| k IH]; intros x.
  - rewrite F_S, iter_F0, (arrow_0 2 (x + 4)). lia.
  - assert (Hit : forall n, iter n (F (S k)) 0 + 4 = iter n (arrow k 2) 4).
    { induction n as [| n IHn]. - reflexivity.
      - change (iter (S n) (F (S k)) 0) with (F (S k) (iter n (F (S k)) 0)).
        change (iter (S n) (arrow k 2) 4) with (arrow k 2 (iter n (arrow k 2) 4)).
        rewrite IH, IHn. reflexivity. }
    rewrite F_S, Hit, (arrow_S_iter k 2 (x + 4)).
    replace (x + 4) with ((x + 2) + 2) by lia. rewrite (iter_add (x + 2) 2 (arrow k 2) 1).
    change (iter 2 (arrow k 2) 1) with (arrow k 2 (arrow k 2 1)).
    rewrite (arrow_one k), (arrow_two k). reflexivity.
Qed.

Lemma iter3 : forall k, iter 3 (F (S k)) 0 + 4 = arrow (S k) 2 5.
Proof.
  intros k.
  change (iter 3 (F (S k)) 0) with (F (S k) (F (S k) (F (S k) 0))).
  rewrite (F_closed k (F (S k) (F (S k) 0))), (F_closed k (F (S k) 0)), (F_closed k 0).
  change (0 + 4) with 4.
  rewrite (arrow_S_iter k 2 5).
  change (iter 5 (arrow k 2) 1) with (arrow k 2 (arrow k 2 (arrow k 2 (arrow k 2 (arrow k 2 1))))).
  rewrite (arrow_one k), (arrow_two k). reflexivity.
Qed.

Lemma bf_closed : bf + 4 = arrow 27 2 3.
Proof.
  rewrite bf_eq.
  change (iter 2 (F 26) 0) with (F 26 (F 26 0)).
  rewrite (F_closed 25 (F 26 0)), (F_closed 25 0).
  change (0 + 4) with 4.
  (* 2 ^27 3 = 2 ^26 (2 ^27 2) = 2 ^26 4 = 2 ^25 (2 ^26 3) = 2 ^25 (2 ^25 (2 ^26 2)) = 2 ^25 (2 ^25 4) *)
  change 3 with (S 2) at 1. rewrite (arrow_SS 26 2 2), (arrow_two 27).
  change 4 with (S 3) at 3. rewrite (arrow_SS 25 2 3).
  change 3 with (S 2) at 2. rewrite (arrow_SS 25 2 2), (arrow_two 26).
  reflexivity.
Qed.

Lemma b2_closed : b2 + 4 = arrow (4 * bf + 33) 2 5.
Proof.
  rewrite b2_eq. replace (4 * bf + 33) with (S (4 * bf + 32)) by lia. apply iter3.
Qed.

Theorem score_closed : exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
  n + 1 = 2 * arrow (4 * bf + 33) 2 5 + 2 * (4 * bf + 33) - 2.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (2 * b2 + 2 * (4 * bf + 33) + 5).
  split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  pose proof b2_closed as E. generalize dependent (arrow (4 * bf + 33) 2 5). intros A E. lia.
Qed.

(* ==================================================================================================== *)
(*              bb8_list/proofs/BB10_lead_vs_champion.v: its score exceeds the champion's               *)
(* ==================================================================================================== *)

(* The earlier file(s) of this module made these constants Opaque; in the multi-file build
   this file started with them transparent (Opaque is not carried over by Require). *)
Transparent arrow.

(* Each original file started with the symbol scope on top (from Individual102's `Open Scope sym`);
   restore that here, since the previous part may have ended in nat_scope. *)
Local Open Scope sym_scope.

(** * The BB(10) candidate beats the BB(10) champion: the two exact scores compared *)

(** Candidate: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LJ0LC_1RG1LD_0RI0RH_1RG1LF_1RE1RI_---1LC
      (BB10_lead_1RB0RA.v: halts; BB10_lead_bound.v: ones at the halt = 2 b2 + 2 (4 bf + 33) + 5, with
       bf = (F 26)^2 0, b2 = (F (4 bf + 33))^3 0, F 0 b = b + 2, F (k+1) b = (F k)^(b+2) 0).
    Champion (Racheline 2024): 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ
      (BB10_champion_bound.v: ones at the halt = b2c + 3, head on a 0, halting transition 1RZ, so its standard
       score is b2c + 4; b1c = Tv 7 1 7, b2c = Tv (b1c/4) 1 7, Tv m j B = U (j+3m+2) (U (j+3m+2) (Tpre m j B))).

    Main results (no axioms):
      Theorem candidate_beats_champion :
        exists cc nc co no, c0 -[ champion tm ]->* cc /\ halted (champion tm) cc /\ champion ones cc nc /\
          c0 -->* co /\ halted tm co /\ ones co no /\ nc + 1 < no + 1.
      Theorem sigma_gt_f_omega2_25 :
        exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ f_omega (f_omega 25) < n + 1.
    Both machines halt by an undefined transition while reading a 0, so the standard scores are nc + 1 and no + 1.

    The argument:
      1. Domination: U j x <= F (j+1) (F (j+1) x) and X j <= (F (j+1))^(4j+2) 0 (Dom), by induction on j.
      2. Hence Tpre m 1 7 <= (F (3m+1))^(6m) 7 and Tv m 1 7 <= F (3m+5) (6m+6) (Tv_le).
      3. b1c = Tv 7 1 7 <= F 26 48 <= F 26 (F 26 0) = bf.
      4. b2c = Tv (b1c/4) 1 7 <= F (3m+5) (6m+6) <= F L (F L 0) <= F L (F L (F L 0)) = b2, with m = b1c/4 <= bf
         and L = 4 bf + 33 (so 3m+5 <= L and 6m+6 <= 4L <= F L 0). *)




Import Coq.micromega.Lia Coq.Arith.PeanoNat Coq.Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

Notation Uc := Champion10.U.
Notation Xc := Champion10.X.
Notation iterc := Champion10.iter.
Notation Tprec := Champion10.Tpre.
Notation Tvc := Champion10.Tv.
Notation b1c := Champion10.b1.
Notation b2c := Champion10.b2.

Opaque Champion10.U Champion10.X Champion10.Tv
  Champion10.b1 Champion10.b2.

(** ** Iteration *)

Lemma iterc_eq : forall n g x, iterc n g x = iter n g x.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma iter_ge2 : forall g, (forall y, y + 2 <= g y) -> forall n x, x + 2 * n <= iter n g x.
Proof.
  intros g Hg. induction n; intros x; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_mono_x : forall g, (forall y z, y <= z -> g y <= g z) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; auto. Qed.

Lemma iter_ge : forall g, (forall y, y <= g y) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_mono_n : forall g, (forall y, y <= g y) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite iter_add. apply iter_ge. exact Hg.
Qed.

Lemma iter_le_fun : forall f g, (forall y, f y <= g y) -> (forall y z, y <= z -> g y <= g z) ->
  forall n x, iter n f x <= iter n g x.
Proof.
  intros f g Hfg Hg. induction n; intros x; simpl. - lia.
  - specialize (IHn x). specialize (Hfg (iter n f x)). specialize (Hg _ _ IHn). lia.
Qed.

Lemma iter_twice : forall g n x, iter n (fun y => g (g y)) x = iter (2 * n) g x.
Proof.
  intros g. induction n; intros x. - reflexivity.
  - replace (2 * S n) with (S (S (2 * n))) by lia. simpl. rewrite IHn. reflexivity.
Qed.

(** ** The clearing functions F of the candidate *)

Lemma F_ge : forall k y, y + 2 <= F k y.
Proof.
  induction k as [| k IH]; intros y.
  - simpl. lia.
  - rewrite F_S. pose proof (iter_ge2 (F k) IH (y + 2) 0). lia.
Qed.

Lemma F_infl : forall k y, y <= F k y.
Proof. intros. pose proof (F_ge k y). lia. Qed.

Lemma F_mono : forall k y z, y <= z -> F k y <= F k z.
Proof.
  destruct k as [| k]; intros y z Hyz.
  - simpl. lia.
  - rewrite !F_S. apply iter_mono_n; [apply F_infl | lia].
Qed.

Lemma F_lvl : forall k y, F k y <= F (S k) y.
Proof.
  intros k y. rewrite F_S. replace (y + 2) with (S (y + 1)) by lia.
  change (iter (S (y + 1)) (F k) 0) with (F k (iter (y + 1) (F k) 0)).
  apply F_mono. pose proof (iter_ge2 (F k) (F_ge k) (y + 1) 0). lia.
Qed.

Lemma F_lvl_mono : forall d k y, F k y <= F (d + k) y.
Proof.
  induction d; intros k y. - reflexivity.
  - specialize (IHd k y). pose proof (F_lvl (d + k) y). change (S d + k) with (S (d + k)). lia.
Qed.

Lemma F_lvl_le : forall k K y, k <= K -> F k y <= F K y.
Proof. intros k K y H. replace K with ((K - k) + k) by lia. apply F_lvl_mono. Qed.

Lemma F1_eq : forall y, F 1 y = 2 * y + 4.
Proof.
  intros y. rewrite F_S.
  assert (E : forall n x, iter n (F 0) x = x + 2 * n).
  { induction n; intros x; simpl. - lia. - rewrite IHn. lia. }
  rewrite E. lia.
Qed.

Lemma F_dbl : forall k y, 1 <= k -> 2 * y + 4 <= F k y.
Proof. intros k y Hk. rewrite <- F1_eq. apply F_lvl_le. exact Hk. Qed.

Lemma F0_big : forall j, 4 * j + 8 <= F (S (S j)) 0.
Proof.
  induction j as [| j IH].
  - change (F 2 0) with (F 1 (F 1 0)). rewrite !F1_eq. lia.
  - change (F (S (S (S j))) 0) with (F (S (S j)) (F (S (S j)) 0)).
    pose proof (F_dbl (S (S j)) (F (S (S j)) 0) ltac:(lia)). lia.
Qed.

Opaque F.

(** ** Domination of the champion's clearing functions *)

Lemma Dom : forall j, (forall x, Uc j x <= F (S j) (F (S j) x)) /\ Xc j <= iter (4 * j + 2) (F (S j)) 0.
Proof.
  induction j as [| j [HU HX]].
  - split.
    + intros x. rewrite Champion10.U_0, !F1_eq. lia.
    + rewrite Champion10.X_0. change (iter (4 * 0 + 2) (F 1) 0) with (F 1 (F 1 0)).
      rewrite !F1_eq. lia.
  - assert (Hc : forall y z, y <= z -> F (S j) (F (S j) y) <= F (S j) (F (S j) z)).
    { intros y z H. apply F_mono, F_mono, H. }
    assert (HX' : Xc (S j) <= iter (4 * S j + 2) (F (S (S j))) 0).
    { rewrite Champion10.X_S.
      transitivity (iter 4 (F (S j)) (Xc j)).
      - change (iter 4 (F (S j)) (Xc j)) with (F (S j) (F (S j) (F (S j) (F (S j) (Xc j))))).
        pose proof (HU (Xc j)) as H1. pose proof (HU (Uc j (Xc j))) as H2.
        pose proof (Hc _ _ H1) as H3. lia.
      - transitivity (iter 4 (F (S j)) (iter (4 * j + 2) (F (S j)) 0)).
        + apply iter_mono_x; [apply F_mono | exact HX].
        + rewrite <- iter_add. replace (4 + (4 * j + 2)) with (4 * S j + 2) by lia.
          apply iter_le_fun; [apply F_lvl | apply F_mono]. }
    split; [| exact HX'].
    intros x. rewrite Champion10.U_S, iterc_eq.
    transitivity (iter (x - 2 * j) (fun y => F (S j) (F (S j) y)) (Xc j)).
    { apply iter_le_fun; [exact HU | exact Hc]. }
    rewrite iter_twice.
    transitivity (iter (2 * (x - 2 * j)) (F (S j)) (iter (4 * j + 2) (F (S j)) 0)).
    { apply iter_mono_x; [apply F_mono | exact HX]. }
    rewrite <- iter_add.
    rewrite (F_S (S j) (F (S (S j)) x)).
    apply iter_mono_n; [apply F_infl |].
    pose proof (F_dbl (S (S j)) x ltac:(lia)) as D1.
    pose proof (F0_big j) as D2. pose proof (F_mono (S (S j)) 0 x ltac:(lia)) as D3. lia.
Qed.

Lemma UD : forall j K y, j < K -> Uc j y <= F K (F K y).
Proof.
  intros j K y H. destruct (Dom j) as [HU _].
  transitivity (F (S j) (F (S j) y)); [apply HU |].
  transitivity (F K (F (S j) y)); [apply F_lvl_le; lia |].
  apply F_mono, F_lvl_le. lia.
Qed.

(** ** The champion's clearing values *)

Lemma Tpre_S : forall m j B, Tprec (S m) j B = Tprec m (j + 3) (iterc 3 (Uc (j + 2)) B).
Proof. reflexivity. Qed.

Lemma Tpre_le : forall m j B, Tprec m j B <= iter (6 * m) (F (j + 3 * m)) B.
Proof.
  induction m as [| m IH]; intros j B.
  - simpl. lia.
  - rewrite Tpre_S, iterc_eq.
    transitivity (iter (6 * m) (F (j + 3 + 3 * m)) (iter 3 (Uc (j + 2)) B)); [apply IH |].
    replace (j + 3 + 3 * m) with (j + 3 * S m) by lia.
    transitivity (iter (6 * m) (F (j + 3 * S m)) (iter 6 (F (j + 3 * S m)) B)).
    + apply iter_mono_x; [apply F_mono |].
      change 6 with (2 * 3). rewrite <- iter_twice.
      apply iter_le_fun; [| intros y z H; apply F_mono, F_mono, H].
      intros y. apply UD. lia.
    + rewrite <- iter_add. replace (6 * m + 6) with (6 * S m) by lia. apply Nat.le_refl.
Qed.

Lemma Tv_le : forall m, Tvc m 1 7 <= F (3 * m + 5) (6 * m + 6).
Proof.
  intros m. rewrite Champion10.Tv_unfold.
  replace (1 + 3 * m + 2) with (3 * m + 3) by lia.
  set (K := 3 * m + 4).
  transitivity (iter 4 (F K) (Tprec m 1 7)).
  { change (iter 4 (F K) (Tprec m 1 7)) with (F K (F K (F K (F K (Tprec m 1 7))))).
    pose proof (UD (3 * m + 3) K (Tprec m 1 7) ltac:(unfold K; lia)) as H1.
    pose proof (UD (3 * m + 3) K (Uc (3 * m + 3) (Tprec m 1 7)) ltac:(unfold K; lia)) as H2.
    pose proof (F_mono K _ _ (F_mono K _ _ H1)) as H3. lia. }
  transitivity (iter 4 (F K) (iter (6 * m) (F K) 7)).
  { apply iter_mono_x; [apply F_mono |].
    transitivity (iter (6 * m) (F (1 + 3 * m)) 7); [apply Tpre_le |].
    apply iter_le_fun; [intros y; apply F_lvl_le; unfold K; lia | apply F_mono]. }
  rewrite <- iter_add.
  transitivity (iter (4 + 6 * m) (F K) (iter 4 (F K) 0)).
  { apply iter_mono_x; [apply F_mono |]. pose proof (iter_ge2 (F K) (F_ge K) 4 0). lia. }
  rewrite <- iter_add.
  replace (3 * m + 5) with (S K) by (unfold K; lia).
  rewrite (F_S K (6 * m + 6)). replace (6 * m + 6 + 2) with (4 + 6 * m + 4) by lia. apply Nat.le_refl.
Qed.

Lemma b1c_le : b1c <= bf.
Proof.
  (* no lia on closed F terms: only transitivity steps *)
  rewrite Champion10.b1_def, bf_eq.
  pose proof (Tv_le 7) as H. change (3 * 7 + 5) with 26 in H. change (6 * 7 + 6) with 48 in H.
  change (iter 2 (F 26) 0) with (F 26 (F 26 0)).
  apply (Nat.le_trans _ _ _ H). apply F_mono.
  apply (Nat.le_trans _ (4 * 24 + 8)); [lia | exact (F0_big 24)].
Qed.

Lemma b2c_le : b2c <= b2.
Proof.
  rewrite Champion10.b2_def. unfold Champion10.second.
  pose proof b1c_le as Hb.
  assert (Hm : b1c / 4 <= bf) by (pose proof (Nat.div_le_upper_bound b1c 4 b1c ltac:(lia) ltac:(lia)); lia).
  pose proof (Tv_le (b1c / 4)) as H1.
  pose proof (F_lvl_le (3 * (b1c / 4) + 5) (4 * bf + 33) (6 * (b1c / 4) + 6) ltac:(lia)) as H2.
  pose proof (F0_big (4 * bf + 31)) as H3. replace (S (S (4 * bf + 31))) with (4 * bf + 33) in H3 by lia.
  pose proof (F_mono (4 * bf + 33) (6 * (b1c / 4) + 6) (F (4 * bf + 33) 0) ltac:(lia)) as H4.
  pose proof (F_mono (4 * bf + 33) (F (4 * bf + 33) 0) (F (4 * bf + 33) (F (4 * bf + 33) 0))
                (F_infl (4 * bf + 33) (F (4 * bf + 33) 0))) as H5.
  rewrite b2_eq. change (iter 3 (F (4 * bf + 33)) 0)
    with (F (4 * bf + 33) (F (4 * bf + 33) (F (4 * bf + 33) 0))).
  lia.
Qed.

(** ** The main theorems *)

Theorem candidate_beats_champion :
  exists cc nc co no,
    c0 -[ Champion10.tm ]->* cc /\ halted Champion10.tm cc /\ Champion10.ones cc nc /\
    c0 -->* co /\ halted tm co /\ ones co no /\ nc + 1 < no + 1.
Proof.
  destruct Champion10.score_exact as [cc [H1 [H2 H3]]].
  destruct score_exact as [co [H4 [H5 H6]]].
  exists cc, (b2c + 3), co, (2 * b2 + 2 * (4 * bf + 33) + 5).
  split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact H4 | split; [exact H5 | split; [exact H6 |]]]]]].
  pose proof b2c_le. lia.
Qed.

(** The bound of the wiki's Champions table for the BB(10) champion, f_omega (f_omega 25), is exceeded too
    (f and f_omega are those of BB10_champion_bound.v: f 0 n = n + 1, f (k+1) n = (f k)^n n, f_omega n = f n n). *)
Theorem sigma_gt_f_omega2_25 :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
    Champion10.f_omega (Champion10.f_omega 25) < n + 1.
Proof.
  destruct score_exact as [co [H4 [H5 H6]]].
  exists co, (2 * b2 + 2 * (4 * bf + 33) + 5).
  split; [exact H4 | split; [exact H5 | split; [exact H6 |]]].
  pose proof (Champion10.final_arith (b1c / 4) b2c Champion10.b1_quarter
                Champion10.b2_big) as Hf.
  pose proof b2c_le as Hle. revert Hf.
  generalize (Champion10.f_omega (Champion10.f_omega 25)). intros w Hf. lia.
Qed.

End Lead10.

(* ==================================================================================================== *)
(*                                     Module N1: the candidate n1                                      *)
(* ==================================================================================================== *)

Module N1.

(* ==================================================================================================== *)
(*                                 bb8_list/proofs/BB10_n1.v: n1 halts                                  *)
(* ==================================================================================================== *)

(* Each original file started with the symbol scope on top (from Individual102's `Open Scope sym`);
   restore that here, since the previous part may have ended in nat_scope. *)
Local Open Scope sym_scope.

(** * BB(10) candidate n1 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_---0LC halts *)

(** Generated by bb8_list/investigations/bb10_n1_coq (gen_final.py). The machine is the G/H-swap sibling of the
    BB(8) record, 1RB0RA_1LC1LF_1RD0LB_1RA1LE_---0LC_0RG1LD_1RH1LG_1LC0RG, with E0 := 1LI and two new states
    I = 0LJ0LI, J = ---0LC (J0 is the halt).  Machine-level lemmas are generated by mexp.py (symbolic execution with
    transfer loops, specs in evs.py / gen_base.py); the abstract part is abstract.v.in, abstract2.v.in, arith.v.in,
    main.v.in.

    B-form (head in H on the blank right of the word; D(m) = (10)^m 1; tokens nearest-first):
      Bf L ts A = L D(t_1) .. D(t_n) D(0) D(A) H> 0^inf      (ts = [t_n; ..; t_1]).
    Champion rules: R1 [L,t+3|A] -> [L,t|2A+8]; R2 [..,t+3,1^(k+1)|A] -> [..,t,A+3,1^k|4]; clearing CLR with
    U 0 A = 2A+8, U (j+1) A = (U j)^(A/3+1) (4), and U j (3a+1) + 8 = 3 * 2 ^(j arrows) (a+3).
    Run from the blank tape (T = 2 ^(37 arrows) 3, sealed; F n = 2 ^(n arrows) 4):
      c0 -->* [7, 1^35 | 4] (6447 steps) -->* [1^36 | 3T-8] -->* (H, S0, CLR(9), P4 with Q = 0, CLR)
         -->* Per 1 (6T-19) 34 a,          Per k m n a = [2^k, 5, 1^m, 0, 0, 2, 1^n | a];
      PERIOD (P1, R2+CLR(9), P2, CLR, P3, R2+CLR(9), P4, CLR): Per k (m+14) n a -->* Per (k+4) m n' a', n' >= F (F n);
      6T-19 = 14 JJ + 7 since T = 2 mod 7 (T is a power tower of 2s), JJ = (3T-13)/7 periods;
      ENDGAME (P1, R2+CLR(9), E, CLR): Per (k+4) 7 n a -->* FarE k + [0, 1^w | f], w >= F n;
      HALT: FarE k + [0, 1^w | f] -->* J reading 0. *)



Import Coq.micromega.Lia Coq.Arith.PeanoNat Coq.Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_---0LC *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (0, R, A)
  | B, 0 => Some (1, L, C)  | B, 1 => Some (1, L, F)
  | C, 0 => Some (1, R, D)  | C, 1 => Some (0, L, B)
  | D, 0 => Some (1, R, A)  | D, 1 => Some (1, L, E)
  | E, 0 => Some (1, L, I)  | E, 1 => Some (0, L, C)
  | F, 0 => Some (0, R, G)  | F, 1 => Some (1, L, D)
  | G, 0 => Some (1, R, H)  | G, 1 => Some (1, L, G)
  | H, 0 => Some (1, L, C)  | H, 1 => Some (0, R, G)
  | I, 0 => Some (0, L, J)  | I, 1 => Some (0, L, I)
  | J, 0 => None            | J, 1 => Some (0, L, C)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** ** Tape normalization (as in the hand-written proofs, e.g. BB8_048631_1RB0RG.v) *)

Lemma align_lpow : forall (x : Sym) xs ys n,
  (x::xs)^^n *> x >> ys = x >> (xs ++ [x])^^n *> ys.
Proof.
  induction n.
  - reflexivity.
  - simpl. repeat rewrite Str_app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma align_lpow_const : forall (x : Sym) xs n,
  (x::xs)^^n *> const x = x >> (xs ++ [x])^^n *> const x.
Proof. intros. rewrite const_unfold at 1. apply align_lpow. Qed.

Ltac align_tape := repeat ((rewrite align_lpow || rewrite align_lpow_const); simpl app).
Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
(** Adjacent powers of the same block, in either order (crossing a run pushes its powers in reverse order). *)
Lemma lpow_merge : forall (xs : list Sym) n m Y, xs^^n *> xs^^m *> Y = xs^^(n + m) *> Y.
Proof. intros. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

(** Blank cells in front of the blank tail. *)
Lemma zero_const : (0 >> const 0 : side) = const 0.
Proof. symmetry. apply const_unfold. Qed.

Ltac finish_norm := apply evstep_refl'; norm_nat; align_tape; repeat rewrite lpow_merge; repeat rewrite zero_const;
  try reflexivity; lia_refl.

Lemma lpow_snoc : forall (xs : list Sym) n Y, xs^^(S n) *> Y = xs^^n *> xs *> Y.
Proof. intros. simpl. rewrite <- lpow_shift. apply Str_app_assoc. Qed.


(** ** Crossing lemmas (generated) *)

Lemma cr_AR_101_001 : forall n l r, l {{A}}> [1;0;1]^^n *> r -->* [0;0;1]^^n *> l {{A}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_AR_111011_000100 : forall n l r, l {{A}}> [1;1;1;0;1;1]^^n *> r -->* [0;0;0;1;0;0]^^n *> l {{A}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_AR_111101_001000 : forall n l r, l {{A}}> [1;1;1;1;0;1]^^n *> r -->* [0;0;1;0;0;0]^^n *> l {{A}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_BL_001_001 : forall n l r, [0;0;1]^^n *> l <{{B}} r -->* l <{{B}} [0;0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_BL_01_01 : forall n l r, [0;1]^^n *> l <{{B}} r -->* l <{{B}} [0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_CL_10_10 : forall n l r, [1;0]^^n *> l <{{C}} r -->* l <{{C}} [1;0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_EL_010101_111011 : forall n l r, [0;1;0;1;0;1]^^n *> l <{{E}} r -->* l <{{E}} [1;1;1;0;1;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_GR_011_011 : forall n l r, l {{G}}> [0;1;1]^^n *> r -->* [0;1;1]^^n *> l {{G}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_GR_01_01 : forall n l r, l {{G}}> [0;1]^^n *> r -->* [0;1]^^n *> l {{G}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_HR_10_10 : forall n l r, l {{H}}> [1;0]^^n *> r -->* [1;0]^^n *> l {{H}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_HR_110110_101101 : forall n l r, l {{H}}> [1;1;0;1;1;0]^^n *> r -->* [1;0;1;1;0;1]^^n *> l {{H}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.


(** ** Machine-level lemmas (generated by mexp.py) *)

Lemma PASS_st1 : forall c j l, (1 >> [0;1]^^j *> 1 >> 0 >> 1 >> [0;1]^^c *> l) {{H}}> (const 0) -->+ (1 >> 0 >> 1 >> [0;1]^^j *> 0 >> 1 >> 1 >> [0;1]^^c *> l) {{H}}> (const 0).
Proof.
  intros. eapply progress_intro; [prove_step | simpl_tape]. do 1 step. follow cr_BL_01_01.
  do 5 step. follow cr_GR_01_01. do 3 step. finish_norm.
Qed.

Lemma PASS : forall c j l, (1 >> [0;1]^^j *> 1 >> 0 >> 1 >> [0;1]^^c *> l) {{H}}> (const 0) -->+ (1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^j *> 1 >> [0;1]^^c *> l) {{H}}> (const 0).
Proof.
  intros.
  eapply progress_evstep_trans; [apply PASS_st1 |].
  finish_norm.
Qed.

Lemma PRO_st1 : forall a t l, (1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{H}}> (const 0) -->+ (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^a *> const 0).
Proof.
  intros. eapply progress_intro; [prove_step | simpl_tape]. do 1 step. follow cr_BL_01_01.
  do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow_const 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma PRO_st3 : forall i2 n3 t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i2 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (1 >> 0 >> [1;0]^^n3 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i2 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^n3 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma PRO_round2 : forall n3 i2 t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i2 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (1 >> 0 >> [1;0]^^n3 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i2 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^n3 *> const 0).
Proof.
  intros. follow PRO_st3. finish_norm.
Qed.

Lemma PRO_loop4 : forall n1 i2 t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i2 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^n1 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i2 *> [0;1]^^n1 *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (const 0).
Proof.
  induction n1; intros.
  - finish_norm.
  - follow (PRO_round2 n1 i2 t l).
    follow (IHn1 (S i2) t l).
    finish_norm.
Qed.

Lemma PRO_loop4_z : forall a t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^a *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (const 0).
Proof.
  intros. follow (PRO_loop4 a 0 t l). finish_norm.
Qed.

Lemma PRO_st5 : forall a t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [0;1]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1]^^t *> l) {{H}}> (const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 5 step. follow cr_GR_01_01. do 7 step.
  follow cr_BL_01_01. do 9 step. follow cr_GR_01_01. do 10 step. finish_norm.
Qed.

Lemma PRO : forall a t l, (1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{H}}> (const 0) -->+ (1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^t *> l) {{H}}> (const 0).
Proof.
  intros.
  eapply progress_evstep_trans; [apply PRO_st1 |].
  follow PRO_loop4_z.
  follow PRO_st5.
  finish_norm.
Qed.

Lemma R2M_st1 : forall a k t l, (1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{H}}> (const 0) -->+ (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^a *> const 0).
Proof.
  intros. eapply progress_intro; [prove_step | simpl_tape]. do 1 step. follow cr_BL_01_01.
  do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow_const 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma R2M_st3 : forall i6 k n7 t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i6 *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (1 >> 0 >> [1;0]^^n7 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i6 *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^n7 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma R2M_round2 : forall n7 i6 k t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i6 *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (1 >> 0 >> [1;0]^^n7 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i6 *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^n7 *> const 0).
Proof.
  intros. follow R2M_st3. finish_norm.
Qed.

Lemma R2M_loop4 : forall n5 i6 k t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i6 *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^n5 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i6 *> [0;1]^^n5 *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (const 0).
Proof.
  induction n5; intros.
  - finish_norm.
  - follow (R2M_round2 n5 i6 k t l).
    follow (IHn5 (S i6) k t l).
    finish_norm.
Qed.

Lemma R2M_loop4_z : forall a k t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^a *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (const 0).
Proof.
  intros. follow (R2M_loop4 a 0 k t l). finish_norm.
Qed.

Lemma R2M_st5 : forall a k t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma R2M_st7 : forall i10 k n11 t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i10 *> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (1 >> 0 >> [1;0]^^n11 *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i10 *> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^n11 *> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma R2M_round6 : forall n11 i10 k t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i10 *> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (1 >> 0 >> [1;0]^^n11 *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i10 *> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^n11 *> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. follow R2M_st7. finish_norm.
Qed.

Lemma R2M_loop8 : forall n9 i10 k t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i10 *> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^n9 *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i10 *> [0;1]^^n9 *> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  induction n9; intros.
  - finish_norm.
  - follow (R2M_round6 n9 i10 k t l).
    follow (IHn9 (S i10) k t l).
    finish_norm.
Qed.

Lemma R2M_loop8_z : forall a k t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. follow (R2M_loop8 a 0 k t l). finish_norm.
Qed.

Lemma R2M_st9 : forall a k t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (0 >> 1 >> 0 >> 1 >> const 0) -->* ([1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 1 step. finish_norm.
Qed.

Lemma R2M_st11 : forall a i20 n21 t l, (1 >> 0 >> 1 >> [1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0).
Proof.
  intros. do 11 step. finish_norm.
Qed.

Lemma R2M_st13 : forall i20 i24 n21 n25 t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i24 *> 1 >> [1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (1 >> 0 >> [1;0]^^n25 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i24 *> 1 >> [1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^n25 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma R2M_round12 : forall n25 i24 i20 n21 t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i24 *> 1 >> [1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (1 >> 0 >> [1;0]^^n25 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i24 *> 1 >> [1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^n25 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0).
Proof.
  intros. follow R2M_st13. finish_norm.
Qed.

Lemma R2M_loop14 : forall n23 i24 i20 n21 t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i24 *> 1 >> [1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^n23 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i24 *> [0;1]^^n23 *> 1 >> [1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0).
Proof.
  induction n23; intros.
  - finish_norm.
  - follow (R2M_round12 n23 i24 i20 n21 t l).
    follow (IHn23 (S i24) i20 n21 t l).
    finish_norm.
Qed.

Lemma R2M_loop14_z : forall a i20 n21 t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0).
Proof.
  intros. follow (R2M_loop14 a 0 i20 n21 t l). finish_norm.
Qed.

Lemma R2M_st15 : forall a i20 n21 t l, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0) -->* ([1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) <{{F}} (1 >> [0;1]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 1 step. finish_norm.
Qed.

Lemma R2M_round10 : forall n21 i20 a t l, (1 >> 0 >> 1 >> [1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0) -->* ([1;0;1]^^n21 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0).
Proof.
  intros. follow R2M_st11. follow R2M_loop14_z. follow R2M_st15. finish_norm.
Qed.

Lemma R2M_loop16 : forall n19 i20 a t l, ([1;0;1]^^n19 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i20 *> [1;0;1]^^n19 *> const 0).
Proof.
  induction n19; intros.
  - finish_norm.
  - follow (R2M_round10 n19 i20 a t l).
    follow (IHn19 (S i20) a t l).
    finish_norm.
Qed.

Lemma R2M_loop16_z : forall a k t l, ([1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> const 0) -->* (0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0).
Proof.
  intros. follow (R2M_loop16 k 0 a t l). finish_norm.
Qed.

Lemma R2M_st17 : forall a k t l, (0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^t *> l) {{G}}> ([1;0;1]^^k *> const 0).
Proof.
  intros. do 7 step. follow cr_HR_10_10. do 1 step. follow cr_CL_10_10. do 15 step.
  follow cr_HR_10_10. do 11 step. finish_norm.
Qed.

Lemma R2M_st19 : forall a i28 n29 t l, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i28 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^t *> l) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n29 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i28 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^t *> l) {{G}}> ([1;0;1]^^n29 *> const 0).
Proof.
  intros. do 5 step. finish_norm.
Qed.

Lemma R2M_round18 : forall n29 i28 a t l, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i28 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^t *> l) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n29 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i28 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^t *> l) {{G}}> ([1;0;1]^^n29 *> const 0).
Proof.
  intros. follow R2M_st19. finish_norm.
Qed.

Lemma R2M_loop20 : forall n27 i28 a t l, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i28 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^t *> l) {{G}}> ([1;0;1]^^n27 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i28 *> [1;0;1]^^n27 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^t *> l) {{G}}> (const 0).
Proof.
  induction n27; intros.
  - finish_norm.
  - follow (R2M_round18 n27 i28 a t l).
    follow (IHn27 (S i28) a t l).
    finish_norm.
Qed.

Lemma R2M_loop20_z : forall a k t l, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^t *> l) {{G}}> ([1;0;1]^^k *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^t *> l) {{G}}> (const 0).
Proof.
  intros. follow (R2M_loop20 k 0 a t l). finish_norm.
Qed.

Lemma R2M_st21 : forall a k t l, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^t *> l) {{G}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^t *> l) {{H}}> (const 0).
Proof.
  intros. do 19 step. finish_norm.
Qed.

Lemma R2M : forall a k t l, (1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^k *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^t *> l) {{H}}> (const 0) -->+ (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^k *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [0;1]^^t *> l) {{H}}> (const 0).
Proof.
  intros.
  eapply progress_evstep_trans; [apply R2M_st1 |].
  follow R2M_loop4_z.
  follow R2M_st5.
  follow R2M_loop8_z.
  follow R2M_st9.
  follow R2M_loop16_z.
  follow R2M_st17.
  follow R2M_loop20_z.
  follow R2M_st21.
  finish_norm.
Qed.

Lemma XH_st1 : forall a n, (1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n *> const 0) {{B}}> ([1;0]^^a *> const 0).
Proof.
  intros. do 2 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow_const 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XH_st3 : forall i32 n n33, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i32 *> 1 >> [1;0;1]^^n *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n33 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i32 *> 1 >> [1;0;1]^^n *> const 0) {{B}}> ([1;0]^^n33 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XH_round2 : forall n33 i32 n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i32 *> 1 >> [1;0;1]^^n *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n33 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i32 *> 1 >> [1;0;1]^^n *> const 0) {{B}}> ([1;0]^^n33 *> const 0).
Proof.
  intros. follow XH_st3. finish_norm.
Qed.

Lemma XH_loop4 : forall n31 i32 n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i32 *> 1 >> [1;0;1]^^n *> const 0) {{B}}> ([1;0]^^n31 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i32 *> [0;1]^^n31 *> 1 >> [1;0;1]^^n *> const 0) {{B}}> (const 0).
Proof.
  induction n31; intros.
  - finish_norm.
  - follow (XH_round2 n31 i32 n).
    follow (IHn31 (S i32) n).
    finish_norm.
Qed.

Lemma XH_loop4_z : forall a n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n *> const 0) {{B}}> ([1;0]^^a *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^n *> const 0) {{B}}> (const 0).
Proof.
  intros. follow (XH_loop4 a 0 n). finish_norm.
Qed.

Lemma XH_st5 : forall a n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^n *> const 0) {{B}}> (const 0) -->* ([1;0;1]^^n *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 1 step. finish_norm.
Qed.

Lemma XH_st7 : forall a i42 n43, (1 >> 0 >> 1 >> [1;0;1]^^n43 *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n43 *> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0).
Proof.
  intros. do 11 step. finish_norm.
Qed.

Lemma XH_st9 : forall i42 i46 n43 n47, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i46 *> 1 >> [1;0;1]^^n43 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n47 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i46 *> 1 >> [1;0;1]^^n43 *> const 0) {{B}}> ([1;0]^^n47 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XH_round8 : forall n47 i46 i42 n43, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i46 *> 1 >> [1;0;1]^^n43 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n47 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i46 *> 1 >> [1;0;1]^^n43 *> const 0) {{B}}> ([1;0]^^n47 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0).
Proof.
  intros. follow XH_st9. finish_norm.
Qed.

Lemma XH_loop10 : forall n45 i46 i42 n43, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i46 *> 1 >> [1;0;1]^^n43 *> const 0) {{B}}> ([1;0]^^n45 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i46 *> [0;1]^^n45 *> 1 >> [1;0;1]^^n43 *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0).
Proof.
  induction n45; intros.
  - finish_norm.
  - follow (XH_round8 n45 i46 i42 n43).
    follow (IHn45 (S i46) i42 n43).
    finish_norm.
Qed.

Lemma XH_loop10_z : forall a i42 n43, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n43 *> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^n43 *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0).
Proof.
  intros. follow (XH_loop10 a 0 i42 n43). finish_norm.
Qed.

Lemma XH_st11 : forall a i42 n43, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^n43 *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0) -->* ([1;0;1]^^n43 *> const 0) <{{F}} (1 >> [0;1]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 1 step. finish_norm.
Qed.

Lemma XH_round6 : forall n43 i42 a, (1 >> 0 >> 1 >> [1;0;1]^^n43 *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0) -->* ([1;0;1]^^n43 *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0).
Proof.
  intros. follow XH_st7. follow XH_loop10_z. follow XH_st11. finish_norm.
Qed.

Lemma XH_loop12 : forall n41 i42 a, ([1;0;1]^^n41 *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> const 0) -->* (const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i42 *> [1;0;1]^^n41 *> const 0).
Proof.
  induction n41; intros.
  - finish_norm.
  - follow (XH_round6 n41 i42 a).
    follow (IHn41 (S i42) a).
    finish_norm.
Qed.

Lemma XH_loop12_z : forall a n, ([1;0;1]^^n *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. follow (XH_loop12 n 0 a). finish_norm.
Qed.

Lemma XH_st13 : forall a n, (const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> const 0) {{A}}> ([0;1]^^a *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. do 7 step. follow cr_HR_10_10. do 1 step. follow cr_CL_10_10. do 25 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step. finish_norm.
Qed.

Lemma XH_st15 : forall i50 n n51, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i50 *> 1 >> 1 >> const 0) {{A}}> (0 >> 1 >> [0;1]^^n51 *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i50 *> 1 >> 1 >> const 0) {{A}}> ([0;1]^^n51 *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XH_round14 : forall n51 i50 n, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i50 *> 1 >> 1 >> const 0) {{A}}> (0 >> 1 >> [0;1]^^n51 *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i50 *> 1 >> 1 >> const 0) {{A}}> ([0;1]^^n51 *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. follow XH_st15. finish_norm.
Qed.

Lemma XH_loop16 : forall n49 i50 n, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i50 *> 1 >> 1 >> const 0) {{A}}> ([0;1]^^n49 *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i50 *> [0;1]^^n49 *> 1 >> 1 >> const 0) {{A}}> (1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  induction n49; intros.
  - finish_norm.
  - follow (XH_round14 n49 i50 n).
    follow (IHn49 (S i50) n).
    finish_norm.
Qed.

Lemma XH_loop16_z : forall a n, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> const 0) {{A}}> ([0;1]^^a *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> const 0) {{A}}> (1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. follow (XH_loop16 a 0 n). finish_norm.
Qed.

Lemma XH_st17 : forall a n, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> const 0) {{A}}> (1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 7 step. follow cr_AR_101_001. do 3 step. follow cr_BL_001_001. do 14 step.
  follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XH_st19 : forall i54 n n55, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i54 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n55 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i54 *> const 0) {{B}}> ([1;0]^^n55 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XH_round18 : forall n55 i54 n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i54 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n55 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i54 *> const 0) {{B}}> ([1;0]^^n55 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow XH_st19. finish_norm.
Qed.

Lemma XH_loop20 : forall n53 i54 n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i54 *> const 0) {{B}}> ([1;0]^^n53 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i54 *> [0;1]^^n53 *> const 0) {{B}}> (0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  induction n53; intros.
  - finish_norm.
  - follow (XH_round18 n53 i54 n).
    follow (IHn53 (S i54) n).
    finish_norm.
Qed.

Lemma XH_loop20_z : forall a n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> const 0) {{B}}> (0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow (XH_loop20 a 0 n). finish_norm.
Qed.

Lemma XH_st21 : forall a n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> const 0) {{B}}> (0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 11 step. follow cr_BL_01_01. do 7 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XH_st23 : forall i58 n n59, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i58 *> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n59 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i58 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n59 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XH_round22 : forall n59 i58 n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i58 *> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n59 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i58 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n59 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow XH_st23. finish_norm.
Qed.

Lemma XH_loop24 : forall n57 i58 n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i58 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n57 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i58 *> [0;1]^^n57 *> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  induction n57; intros.
  - finish_norm.
  - follow (XH_round22 n57 i58 n).
    follow (IHn57 (S i58) n).
    finish_norm.
Qed.

Lemma XH_loop24_z : forall a n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow (XH_loop24 a 0 n). finish_norm.
Qed.

Lemma XH_st25 : forall a n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XH_st27 : forall i62 n n63, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i62 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n63 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i62 *> const 0) {{B}}> ([1;0]^^n63 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XH_round26 : forall n63 i62 n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i62 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n63 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i62 *> const 0) {{B}}> ([1;0]^^n63 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow XH_st27. finish_norm.
Qed.

Lemma XH_loop28 : forall n61 i62 n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i62 *> const 0) {{B}}> ([1;0]^^n61 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i62 *> [0;1]^^n61 *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  induction n61; intros.
  - finish_norm.
  - follow (XH_round26 n61 i62 n).
    follow (IHn61 (S i62) n).
    finish_norm.
Qed.

Lemma XH_loop28_z : forall a n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow (XH_loop28 a 0 n). finish_norm.
Qed.

Lemma XH_st29 : forall a n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 7 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XH_st31 : forall i66 n n67, (1 >> 0 >> 0 >> 1 >> [0;1]^^i66 *> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n67 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i66 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n67 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XH_round30 : forall n67 i66 n, (1 >> 0 >> 0 >> 1 >> [0;1]^^i66 *> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n67 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i66 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n67 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow XH_st31. finish_norm.
Qed.

Lemma XH_loop32 : forall n65 i66 n, (1 >> 0 >> 0 >> 1 >> [0;1]^^i66 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n65 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i66 *> [0;1]^^n65 *> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  induction n65; intros.
  - finish_norm.
  - follow (XH_round30 n65 i66 n).
    follow (IHn65 (S i66) n).
    finish_norm.
Qed.

Lemma XH_loop32_z : forall a n, (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow (XH_loop32 a 0 n). finish_norm.
Qed.

Lemma XH_st33 : forall a n, (1 >> 0 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. finish_norm.
Qed.

Lemma XH_st35 : forall i70 n n71, (1 >> 0 >> 0 >> 1 >> [0;1]^^i70 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n71 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i70 *> const 0) {{B}}> ([1;0]^^n71 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XH_round34 : forall n71 i70 n, (1 >> 0 >> 0 >> 1 >> [0;1]^^i70 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n71 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i70 *> const 0) {{B}}> ([1;0]^^n71 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow XH_st35. finish_norm.
Qed.

Lemma XH_loop36 : forall n69 i70 n, (1 >> 0 >> 0 >> 1 >> [0;1]^^i70 *> const 0) {{B}}> ([1;0]^^n69 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i70 *> [0;1]^^n69 *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  induction n69; intros.
  - finish_norm.
  - follow (XH_round34 n69 i70 n).
    follow (IHn69 (S i70) n).
    finish_norm.
Qed.

Lemma XH_loop36_z : forall a n, (1 >> 0 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^a *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow (XH_loop36 a 0 n). finish_norm.
Qed.

Lemma XH_st37 : forall a n, (1 >> 0 >> 0 >> 1 >> [0;1]^^a *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. do 7 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. finish_norm.
Qed.

Lemma XH_st39 : forall i74 n n75, (1 >> 0 >> [0;1]^^i74 *> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n75 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i74 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n75 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XH_round38 : forall n75 i74 n, (1 >> 0 >> [0;1]^^i74 *> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n75 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i74 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n75 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow XH_st39. finish_norm.
Qed.

Lemma XH_loop40 : forall n73 i74 n, (1 >> 0 >> [0;1]^^i74 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n73 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> [0;1]^^i74 *> [0;1]^^n73 *> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  induction n73; intros.
  - finish_norm.
  - follow (XH_round38 n73 i74 n).
    follow (IHn73 (S i74) n).
    finish_norm.
Qed.

Lemma XH_loop40_z : forall a n, (1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> [0;1]^^a *> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow (XH_loop40 a 0 n). finish_norm.
Qed.

Lemma XH_st41 : forall a n, (1 >> 0 >> [0;1]^^a *> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* ([0;1]^^a *> 1 >> 1 >> const 0) <{{C}} (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 3 step. finish_norm.
Qed.

Lemma XH_st43 : forall i88 n n89, (0 >> 1 >> [0;1]^^n89 *> 1 >> 1 >> const 0) <{{C}} (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n89 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 4 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. finish_norm.
Qed.

Lemma XH_st45 : forall i88 i92 n n93, (1 >> 0 >> 0 >> 1 >> [0;1]^^i92 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n93 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i92 *> const 0) {{B}}> ([1;0]^^n93 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XH_round44 : forall n93 i92 i88 n, (1 >> 0 >> 0 >> 1 >> [0;1]^^i92 *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n93 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i92 *> const 0) {{B}}> ([1;0]^^n93 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow XH_st45. finish_norm.
Qed.

Lemma XH_loop46 : forall n91 i92 i88 n, (1 >> 0 >> 0 >> 1 >> [0;1]^^i92 *> const 0) {{B}}> ([1;0]^^n91 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i92 *> [0;1]^^n91 *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  induction n91; intros.
  - finish_norm.
  - follow (XH_round44 n91 i92 i88 n).
    follow (IHn91 (S i92) i88 n).
    finish_norm.
Qed.

Lemma XH_loop46_z : forall i88 n n89, (1 >> 0 >> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n89 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^n89 *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow (XH_loop46 n89 0 i88 n). finish_norm.
Qed.

Lemma XH_st47 : forall i88 n n89, (1 >> 0 >> 0 >> 1 >> [0;1]^^n89 *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n89 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. do 7 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. finish_norm.
Qed.

Lemma XH_st49 : forall i88 i96 n n97, (1 >> 0 >> [0;1]^^i96 *> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n97 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i96 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n97 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XH_round48 : forall n97 i96 i88 n, (1 >> 0 >> [0;1]^^i96 *> 1 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n97 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i96 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n97 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow XH_st49. finish_norm.
Qed.

Lemma XH_loop50 : forall n95 i96 i88 n, (1 >> 0 >> [0;1]^^i96 *> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n95 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> [0;1]^^i96 *> [0;1]^^n95 *> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  induction n95; intros.
  - finish_norm.
  - follow (XH_round48 n95 i96 i88 n).
    follow (IHn95 (S i96) i88 n).
    finish_norm.
Qed.

Lemma XH_loop50_z : forall i88 n n89, (1 >> 0 >> 1 >> 1 >> const 0) {{B}}> ([1;0]^^n89 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> [0;1]^^n89 *> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow (XH_loop50 n89 0 i88 n). finish_norm.
Qed.

Lemma XH_st51 : forall i88 n n89, (1 >> 0 >> [0;1]^^n89 *> 1 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* ([0;1]^^n89 *> 1 >> 1 >> const 0) <{{C}} (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 3 step. finish_norm.
Qed.

Lemma XH_round42 : forall n89 i88 n, (0 >> 1 >> [0;1]^^n89 *> 1 >> 1 >> const 0) <{{C}} (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* ([0;1]^^n89 *> 1 >> 1 >> const 0) <{{C}} (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow XH_st43. follow XH_loop46_z. follow XH_st47. follow XH_loop50_z. follow XH_st51.
  finish_norm.
Qed.

Lemma XH_loop52 : forall n87 i88 n, ([0;1]^^n87 *> 1 >> 1 >> const 0) <{{C}} (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 1 >> const 0) <{{C}} (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^i88 *> [1;1;0;1;1;0]^^n87 *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  induction n87; intros.
  - finish_norm.
  - follow (XH_round42 n87 i88 n).
    follow (IHn87 (S i88) n).
    finish_norm.
Qed.

Lemma XH_loop52_z : forall a n, ([0;1]^^a *> 1 >> 1 >> const 0) <{{C}} (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 1 >> const 0) <{{C}} (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^a *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow (XH_loop52 a 0 n). finish_norm.
Qed.

Lemma XH_st53 : forall a n, (1 >> 1 >> const 0) <{{C}} (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> [1;1;0;1;1;0]^^a *> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^a *> 0 >> 1 >> const 0) {{H}}> ([0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 39 step. follow cr_HR_110110_101101. do 1 step.
  repeat rewrite (align_lpow 1 [0;1;1;0;1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 0 [1;1;0;1;1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [1;0;1;1;0]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0;1;1;0;1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 0 [1;1;0;1;1]). simpl app. do 12 step. finish_norm.
Qed.

Lemma XH_st55 : forall a i100 n101, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i100 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^a *> 0 >> 1 >> const 0) {{H}}> (0 >> 1 >> 0 >> [0;1;0]^^n101 *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i100 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^a *> 0 >> 1 >> const 0) {{H}}> ([0;1;0]^^n101 *> 1 >> const 0).
Proof.
  intros. do 17 step. finish_norm.
Qed.

Lemma XH_round54 : forall n101 i100 a, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i100 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^a *> 0 >> 1 >> const 0) {{H}}> (0 >> 1 >> 0 >> [0;1;0]^^n101 *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i100 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^a *> 0 >> 1 >> const 0) {{H}}> ([0;1;0]^^n101 *> 1 >> const 0).
Proof.
  intros. follow XH_st55. finish_norm.
Qed.

Lemma XH_loop56 : forall n99 i100 a, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i100 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^a *> 0 >> 1 >> const 0) {{H}}> ([0;1;0]^^n99 *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i100 *> [0;1;1]^^n99 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^a *> 0 >> 1 >> const 0) {{H}}> (1 >> const 0).
Proof.
  induction n99; intros.
  - finish_norm.
  - follow (XH_round54 n99 i100 a).
    follow (IHn99 (S i100) a).
    finish_norm.
Qed.

Lemma XH_loop56_z : forall a n, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^a *> 0 >> 1 >> const 0) {{H}}> ([0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^a *> 0 >> 1 >> const 0) {{H}}> (1 >> const 0).
Proof.
  intros. follow (XH_loop56 n 0 a). finish_norm.
Qed.

Lemma XH_st57 : forall a n, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^a *> 0 >> 1 >> const 0) {{H}}> (1 >> const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^a *> 0 >> 1 >> const 0) {{H}}> (const 0).
Proof.
  intros. do 46 step. finish_norm.
Qed.

Lemma EV_H : forall a n, (1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n *> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^a *> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{H}}> (const 0).
Proof.
  intros.
  follow XH_st1.
  follow XH_loop4_z.
  follow XH_st5.
  follow XH_loop12_z.
  follow XH_st13.
  follow XH_loop16_z.
  follow XH_st17.
  follow XH_loop20_z.
  follow XH_st21.
  follow XH_loop24_z.
  follow XH_st25.
  follow XH_loop28_z.
  follow XH_st29.
  follow XH_loop32_z.
  follow XH_st33.
  follow XH_loop36_z.
  follow XH_st37.
  follow XH_loop40_z.
  follow XH_st41.
  follow XH_loop52_z.
  follow XH_st53.
  follow XH_loop56_z.
  follow XH_st57.
  finish_norm.
Qed.

Lemma XS0_st1 : forall M a n, (1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> const 0).
Proof.
  intros. do 2 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow_const 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XS0_st3 : forall M i104 n n105, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i104 *> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n105 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i104 *> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n105 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XS0_round2 : forall n105 i104 M n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i104 *> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n105 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i104 *> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n105 *> const 0).
Proof.
  intros. follow XS0_st3. finish_norm.
Qed.

Lemma XS0_loop4 : forall n103 i104 M n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i104 *> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n103 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i104 *> [0;1]^^n103 *> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (const 0).
Proof.
  induction n103; intros.
  - finish_norm.
  - follow (XS0_round2 n103 i104 M n).
    follow (IHn103 (S i104) M n).
    finish_norm.
Qed.

Lemma XS0_loop4_z : forall M a n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (const 0).
Proof.
  intros. follow (XS0_loop4 a 0 M n). finish_norm.
Qed.

Lemma XS0_st5 : forall M a n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XS0_st7 : forall M i108 n n109, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i108 *> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n109 *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i108 *> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n109 *> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XS0_round6 : forall n109 i108 M n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i108 *> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n109 *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i108 *> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n109 *> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. follow XS0_st7. finish_norm.
Qed.

Lemma XS0_loop8 : forall n107 i108 M n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i108 *> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n107 *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i108 *> [0;1]^^n107 *> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  induction n107; intros.
  - finish_norm.
  - follow (XS0_round6 n107 i108 M n).
    follow (IHn107 (S i108) M n).
    finish_norm.
Qed.

Lemma XS0_loop8_z : forall M a n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. follow (XS0_loop8 a 0 M n). finish_norm.
Qed.

Lemma XS0_st9 : forall M a n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> const 0) -->* ([0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 2 step. finish_norm.
Qed.

Lemma XS0_st11 : forall M a i118 n119, (0 >> 1 >> 1 >> [0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0).
Proof.
  intros. do 10 step. finish_norm.
Qed.

Lemma XS0_st13 : forall M i118 i122 n119 n123, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i122 *> 1 >> 1 >> [0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n123 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i122 *> 1 >> 1 >> [0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n123 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XS0_round12 : forall n123 i122 M i118 n119, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i122 *> 1 >> 1 >> [0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (1 >> 0 >> [1;0]^^n123 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i122 *> 1 >> 1 >> [0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n123 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0).
Proof.
  intros. follow XS0_st13. finish_norm.
Qed.

Lemma XS0_loop14 : forall n121 i122 M i118 n119, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i122 *> 1 >> 1 >> [0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^n121 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i122 *> [0;1]^^n121 *> 1 >> 1 >> [0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0).
Proof.
  induction n121; intros.
  - finish_norm.
  - follow (XS0_round12 n121 i122 M i118 n119).
    follow (IHn121 (S i122) M i118 n119).
    finish_norm.
Qed.

Lemma XS0_loop14_z : forall M a i118 n119, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0).
Proof.
  intros. follow (XS0_loop14 a 0 M i118 n119). finish_norm.
Qed.

Lemma XS0_st15 : forall M a i118 n119, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0) -->* ([0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) <{{D}} (1 >> 1 >> [0;1]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 2 step. finish_norm.
Qed.

Lemma XS0_round10 : forall n119 i118 M a, (0 >> 1 >> 1 >> [0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0) -->* ([0;1;1]^^n119 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0).
Proof.
  intros. follow XS0_st11. follow XS0_loop14_z. follow XS0_st15. finish_norm.
Qed.

Lemma XS0_loop16 : forall n117 i118 M a, ([0;1;1]^^n117 *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i118 *> [1;0;1]^^n117 *> const 0).
Proof.
  induction n117; intros.
  - finish_norm.
  - follow (XS0_round10 n117 i118 M a).
    follow (IHn117 (S i118) M a).
    finish_norm.
Qed.

Lemma XS0_loop16_z : forall M a n, ([0;1;1]^^n *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. follow (XS0_loop16 n 0 M a). finish_norm.
Qed.

Lemma XS0_st17 : forall M a n, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* ([1;0;1]^^M *> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. do 98 step. finish_norm.
Qed.

Lemma XS0_st19 : forall a i126 n n127, (1 >> 0 >> 1 >> [1;0;1]^^n127 *> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i126 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* ([1;0;1]^^n127 *> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i126 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. do 37 step. finish_norm.
Qed.

Lemma XS0_round18 : forall n127 i126 a n, (1 >> 0 >> 1 >> [1;0;1]^^n127 *> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i126 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* ([1;0;1]^^n127 *> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i126 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. follow XS0_st19. finish_norm.
Qed.

Lemma XS0_loop20 : forall n125 i126 a n, ([1;0;1]^^n125 *> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i126 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i126 *> [1;0;1]^^n125 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  induction n125; intros.
  - finish_norm.
  - follow (XS0_round18 n125 i126 a n).
    follow (IHn125 (S i126) a n).
    finish_norm.
Qed.

Lemma XS0_loop20_z : forall M a n, ([1;0;1]^^M *> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. follow (XS0_loop20 M 0 a n). finish_norm.
Qed.

Lemma XS0_st21 : forall M a n, (0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> ([1;0;1]^^M *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. do 46 step. finish_norm.
Qed.

Lemma XS0_st23 : forall a i130 n n131, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i130 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n131 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i130 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> ([1;0;1]^^n131 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. do 5 step. finish_norm.
Qed.

Lemma XS0_round22 : forall n131 i130 a n, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i130 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n131 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i130 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> ([1;0;1]^^n131 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. follow XS0_st23. finish_norm.
Qed.

Lemma XS0_loop24 : forall n129 i130 a n, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i130 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> ([1;0;1]^^n129 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i130 *> [1;0;1]^^n129 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  induction n129; intros.
  - finish_norm.
  - follow (XS0_round22 n129 i130 a n).
    follow (IHn129 (S i130) a n).
    finish_norm.
Qed.

Lemma XS0_loop24_z : forall M a n, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> ([1;0;1]^^M *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. follow (XS0_loop24 M 0 a n). finish_norm.
Qed.

Lemma XS0_st25 : forall M a n, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* ([1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. do 14 step. follow cr_HR_10_10. do 1 step. follow cr_CL_10_10. do 30 step. finish_norm.
Qed.

Lemma XS0_st27 : forall a i134 n n135, (1 >> 0 >> 1 >> [1;0;1]^^n135 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;1;1]^^i134 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* ([1;0;1]^^n135 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i134 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. do 37 step. finish_norm.
Qed.

Lemma XS0_round26 : forall n135 i134 a n, (1 >> 0 >> 1 >> [1;0;1]^^n135 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;1;1]^^i134 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* ([1;0;1]^^n135 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i134 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. follow XS0_st27. finish_norm.
Qed.

Lemma XS0_loop28 : forall n133 i134 a n, ([1;0;1]^^n133 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;1;1]^^i134 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;1;1]^^i134 *> [0;1;1]^^n133 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  induction n133; intros.
  - finish_norm.
  - follow (XS0_round26 n133 i134 a n).
    follow (IHn133 (S i134) a n).
    finish_norm.
Qed.

Lemma XS0_loop28_z : forall M a n, ([1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;1;1]^^M *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. follow (XS0_loop28 M 0 a n). finish_norm.
Qed.

Lemma XS0_st29 : forall M a n, (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;1;1]^^M *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> ([1;0;1]^^n *> const 0).
Proof.
  intros. do 39 step. follow cr_GR_011_011. do 1 step.
  repeat rewrite (align_lpow 0 [1;1]). simpl app. do 14 step. follow cr_GR_01_01. do 1 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 9 step. finish_norm.
Qed.

Lemma XS0_st31 : forall M a i138 n139, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i138 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n139 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i138 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> ([1;0;1]^^n139 *> const 0).
Proof.
  intros. do 5 step. finish_norm.
Qed.

Lemma XS0_round30 : forall n139 i138 M a, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i138 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n139 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i138 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> ([1;0;1]^^n139 *> const 0).
Proof.
  intros. follow XS0_st31. finish_norm.
Qed.

Lemma XS0_loop32 : forall n137 i138 M a, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i138 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> ([1;0;1]^^n137 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i138 *> [1;0;1]^^n137 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> (const 0).
Proof.
  induction n137; intros.
  - finish_norm.
  - follow (XS0_round30 n137 i138 M a).
    follow (IHn137 (S i138) M a).
    finish_norm.
Qed.

Lemma XS0_loop32_z : forall M a n, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> ([1;0;1]^^n *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> (const 0).
Proof.
  intros. follow (XS0_loop32 n 0 M a). finish_norm.
Qed.

Lemma XS0_st33 : forall M a n, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{G}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{H}}> (const 0).
Proof.
  intros. do 19 step. finish_norm.
Qed.

Lemma EV_S0 : forall M a n, (1 >> [0;1]^^a *> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^M *> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> [1;0;1]^^M *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) {{H}}> (const 0).
Proof.
  intros.
  follow XS0_st1.
  follow XS0_loop4_z.
  follow XS0_st5.
  follow XS0_loop8_z.
  follow XS0_st9.
  follow XS0_loop16_z.
  follow XS0_st17.
  follow XS0_loop20_z.
  follow XS0_st21.
  follow XS0_loop24_z.
  follow XS0_st25.
  follow XS0_loop28_z.
  follow XS0_st29.
  follow XS0_loop32_z.
  follow XS0_st33.
  finish_norm.
Qed.

Lemma XP1_st1 : forall a k m n, (1 >> [0;1]^^a *> 1 >> [1;0;1]^^n *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^a *> const 0).
Proof.
  intros. do 2 step. follow cr_BL_01_01. do 1 step. repeat rewrite (align_lpow 1 [0;1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 0 [1;1]). simpl app. do 3 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow_const 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XP1_st3 : forall i142 k m n n143, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i142 *> 1 >> [1;0;1]^^n *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n143 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i142 *> 1 >> [1;0;1]^^n *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n143 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP1_round2 : forall n143 i142 k m n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i142 *> 1 >> [1;0;1]^^n *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n143 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i142 *> 1 >> [1;0;1]^^n *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n143 *> const 0).
Proof.
  intros. follow XP1_st3. finish_norm.
Qed.

Lemma XP1_loop4 : forall n141 i142 k m n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i142 *> 1 >> [1;0;1]^^n *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n141 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i142 *> [0;1]^^n141 *> 1 >> [1;0;1]^^n *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0).
Proof.
  induction n141; intros.
  - finish_norm.
  - follow (XP1_round2 n141 i142 k m n).
    follow (IHn141 (S i142) k m n).
    finish_norm.
Qed.

Lemma XP1_loop4_z : forall a k m n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^a *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^n *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0).
Proof.
  intros. follow (XP1_loop4 a 0 k m n). finish_norm.
Qed.

Lemma XP1_st5 : forall a k m n, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^n *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0) -->* ([1;0;1]^^n *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 1 step. finish_norm.
Qed.

Lemma XP1_st7 : forall a i152 k m n153, (1 >> 0 >> 1 >> [1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0).
Proof.
  intros. do 11 step. finish_norm.
Qed.

Lemma XP1_st9 : forall i152 i156 k m n153 n157, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i156 *> 1 >> [1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n157 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i156 *> 1 >> [1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n157 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP1_round8 : forall n157 i156 i152 k m n153, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i156 *> 1 >> [1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n157 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i156 *> 1 >> [1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n157 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0).
Proof.
  intros. follow XP1_st9. finish_norm.
Qed.

Lemma XP1_loop10 : forall n155 i156 i152 k m n153, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i156 *> 1 >> [1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n155 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i156 *> [0;1]^^n155 *> 1 >> [1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0).
Proof.
  induction n155; intros.
  - finish_norm.
  - follow (XP1_round8 n155 i156 i152 k m n153).
    follow (IHn155 (S i156) i152 k m n153).
    finish_norm.
Qed.

Lemma XP1_loop10_z : forall a i152 k m n153, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0).
Proof.
  intros. follow (XP1_loop10 a 0 i152 k m n153). finish_norm.
Qed.

Lemma XP1_st11 : forall a i152 k m n153, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0) -->* ([1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> [0;1]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 1 step. finish_norm.
Qed.

Lemma XP1_round6 : forall n153 i152 a k m, (1 >> 0 >> 1 >> [1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0) -->* ([1;0;1]^^n153 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0).
Proof.
  intros. follow XP1_st7. follow XP1_loop10_z. follow XP1_st11. finish_norm.
Qed.

Lemma XP1_loop12 : forall n151 i152 a k m, ([1;0;1]^^n151 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> const 0) -->* (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i152 *> [1;0;1]^^n151 *> const 0).
Proof.
  induction n151; intros.
  - finish_norm.
  - follow (XP1_round6 n151 i152 a k m).
    follow (IHn151 (S i152) a k m).
    finish_norm.
Qed.

Lemma XP1_loop12_z : forall a k m n, ([1;0;1]^^n *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. follow (XP1_loop12 n 0 a k m). finish_norm.
Qed.

Lemma XP1_st13 : forall a k m n, (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> ([0;1]^^a *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. do 7 step. follow cr_HR_10_10. do 1 step. follow cr_CL_10_10. do 27 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step. finish_norm.
Qed.

Lemma XP1_st15 : forall i160 k m n n161, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i160 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> (0 >> 1 >> [0;1]^^n161 *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i160 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> ([0;1]^^n161 *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP1_round14 : forall n161 i160 k m n, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i160 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> (0 >> 1 >> [0;1]^^n161 *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i160 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> ([0;1]^^n161 *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. follow XP1_st15. finish_norm.
Qed.

Lemma XP1_loop16 : forall n159 i160 k m n, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i160 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> ([0;1]^^n159 *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i160 *> [1;0]^^n159 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> (1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  induction n159; intros.
  - finish_norm.
  - follow (XP1_round14 n159 i160 k m n).
    follow (IHn159 (S i160) k m n).
    finish_norm.
Qed.

Lemma XP1_loop16_z : forall a k m n, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> ([0;1]^^a *> 1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> (1 >> 0 >> 1 >> [1;0;1]^^n *> const 0).
Proof.
  intros. follow (XP1_loop16 a 0 k m n). finish_norm.
Qed.

Lemma XP1_st17 : forall a k m n, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> (1 >> 0 >> 1 >> [1;0;1]^^n *> const 0) -->* ([1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 7 step. follow cr_AR_101_001. do 3 step. follow cr_BL_001_001. do 15 step.
  follow cr_CL_10_10. do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 103 step.
  finish_norm.
Qed.

Lemma XP1_st19 : forall a i164 k n n165, (1 >> 0 >> 1 >> [1;0;1]^^n165 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i164 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* ([1;0;1]^^n165 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i164 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 37 step. finish_norm.
Qed.

Lemma XP1_round18 : forall n165 i164 a k n, (1 >> 0 >> 1 >> [1;0;1]^^n165 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i164 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* ([1;0;1]^^n165 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i164 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow XP1_st19. finish_norm.
Qed.

Lemma XP1_loop20 : forall n163 i164 a k n, ([1;0;1]^^n163 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i164 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i164 *> [1;0;1]^^n163 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  induction n163; intros.
  - finish_norm.
  - follow (XP1_round18 n163 i164 a k n).
    follow (IHn163 (S i164) a k n).
    finish_norm.
Qed.

Lemma XP1_loop20_z : forall a k m n, ([1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow (XP1_loop20 m 0 a k n). finish_norm.
Qed.

Lemma XP1_st21 : forall a k m n, (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^m *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 46 step. finish_norm.
Qed.

Lemma XP1_st23 : forall a i168 k n n169, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i168 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n169 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i168 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n169 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 5 step. finish_norm.
Qed.

Lemma XP1_round22 : forall n169 i168 a k n, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i168 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n169 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i168 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n169 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow XP1_st23. finish_norm.
Qed.

Lemma XP1_loop24 : forall n167 i168 a k n, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i168 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n167 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i168 *> [1;0;1]^^n167 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  induction n167; intros.
  - finish_norm.
  - follow (XP1_round22 n167 i168 a k n).
    follow (IHn167 (S i168) a k n).
    finish_norm.
Qed.

Lemma XP1_loop24_z : forall a k m n, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^m *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow (XP1_loop24 m 0 a k n). finish_norm.
Qed.

Lemma XP1_st25 : forall a k m n, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* ([1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 41 step. finish_norm.
Qed.

Lemma XP1_st27 : forall a i172 k n n173, (1 >> 0 >> 1 >> [1;0;1]^^n173 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;1;1]^^i172 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* ([1;0;1]^^n173 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i172 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 37 step. finish_norm.
Qed.

Lemma XP1_round26 : forall n173 i172 a k n, (1 >> 0 >> 1 >> [1;0;1]^^n173 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;1;1]^^i172 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* ([1;0;1]^^n173 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i172 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow XP1_st27. finish_norm.
Qed.

Lemma XP1_loop28 : forall n171 i172 a k n, ([1;0;1]^^n171 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;1;1]^^i172 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;1;1]^^i172 *> [0;1;1]^^n171 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  induction n171; intros.
  - finish_norm.
  - follow (XP1_round26 n171 i172 a k n).
    follow (IHn171 (S i172) a k n).
    finish_norm.
Qed.

Lemma XP1_loop28_z : forall a k m n, ([1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;1;1]^^m *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. follow (XP1_loop28 m 0 a k n). finish_norm.
Qed.

Lemma XP1_st29 : forall a k m n, (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;1;1]^^m *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> [0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> ([0;1;0]^^n *> 1 >> const 0).
Proof.
  intros. do 39 step. follow cr_GR_011_011. do 1 step.
  repeat rewrite (align_lpow 0 [1;1]). simpl app. do 20 step. follow cr_HR_10_10. do 1 step.
  follow cr_CL_10_10. do 19 step. follow cr_HR_10_10. do 9 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 1 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 12 step. finish_norm.
Qed.

Lemma XP1_st31 : forall a i176 k m n177, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i176 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (0 >> 1 >> 0 >> [0;1;0]^^n177 *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i176 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> ([0;1;0]^^n177 *> 1 >> const 0).
Proof.
  intros. do 17 step. finish_norm.
Qed.

Lemma XP1_round30 : forall n177 i176 a k m, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i176 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (0 >> 1 >> 0 >> [0;1;0]^^n177 *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i176 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> ([0;1;0]^^n177 *> 1 >> const 0).
Proof.
  intros. follow XP1_st31. finish_norm.
Qed.

Lemma XP1_loop32 : forall n175 i176 a k m, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i176 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> ([0;1;0]^^n175 *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i176 *> [1;0;1]^^n175 *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (1 >> const 0).
Proof.
  induction n175; intros.
  - finish_norm.
  - follow (XP1_round30 n175 i176 a k m).
    follow (IHn175 (S i176) a k m).
    finish_norm.
Qed.

Lemma XP1_loop32_z : forall a k m n, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> ([0;1;0]^^n *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (1 >> const 0).
Proof.
  intros. follow (XP1_loop32 n 0 a k m). finish_norm.
Qed.

Lemma XP1_st33 : forall a k m n, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (1 >> const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^n *> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0).
Proof.
  intros. do 46 step. finish_norm.
Qed.

Lemma EV_P1 : forall a k m n, (1 >> [0;1]^^a *> 1 >> [1;0;1]^^n *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0).
Proof.
  intros.
  follow XP1_st1.
  follow XP1_loop4_z.
  follow XP1_st5.
  follow XP1_loop12_z.
  follow XP1_st13.
  follow XP1_loop16_z.
  follow XP1_st17.
  follow XP1_loop20_z.
  follow XP1_st21.
  follow XP1_loop24_z.
  follow XP1_st25.
  follow XP1_loop28_z.
  follow XP1_st29.
  follow XP1_loop32_z.
  follow XP1_st33.
  finish_norm.
Qed.

Lemma XP2_st1 : forall k m p r w, (1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> 1 >> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> const 0).
Proof.
  intros. do 4 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow_const 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XP2_st3 : forall i180 k m n181 p w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i180 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n181 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i180 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n181 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP2_round2 : forall n181 i180 k m p w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i180 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n181 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i180 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n181 *> const 0).
Proof.
  intros. follow XP2_st3. finish_norm.
Qed.

Lemma XP2_loop4 : forall n179 i180 k m p w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i180 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n179 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i180 *> [0;1]^^n179 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0).
Proof.
  induction n179; intros.
  - finish_norm.
  - follow (XP2_round2 n179 i180 k m p w).
    follow (IHn179 (S i180) k m p w).
    finish_norm.
Qed.

Lemma XP2_loop4_z : forall k m p r w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0).
Proof.
  intros. follow (XP2_loop4 r 0 k m p w). finish_norm.
Qed.

Lemma XP2_st5 : forall k m p r w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0) -->* ([0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 11 step. follow cr_BL_01_01. do 2 step. finish_norm.
Qed.

Lemma XP2_st7 : forall i190 k m n191 p r, (0 >> 1 >> 1 >> [0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0).
Proof.
  intros. do 16 step. finish_norm.
Qed.

Lemma XP2_st9 : forall i190 i194 k m n191 n195 p, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i194 *> 1 >> 1 >> [0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n195 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i194 *> 1 >> 1 >> [0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n195 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP2_round8 : forall n195 i194 i190 k m n191 p, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i194 *> 1 >> 1 >> [0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n195 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i194 *> 1 >> 1 >> [0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n195 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0).
Proof.
  intros. follow XP2_st9. finish_norm.
Qed.

Lemma XP2_loop10 : forall n193 i194 i190 k m n191 p, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i194 *> 1 >> 1 >> [0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n193 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i194 *> [0;1]^^n193 *> 1 >> 1 >> [0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0).
Proof.
  induction n193; intros.
  - finish_norm.
  - follow (XP2_round8 n193 i194 i190 k m n191 p).
    follow (IHn193 (S i194) i190 k m n191 p).
    finish_norm.
Qed.

Lemma XP2_loop10_z : forall i190 k m n191 p r, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> [0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0).
Proof.
  intros. follow (XP2_loop10 r 0 i190 k m n191 p). finish_norm.
Qed.

Lemma XP2_st11 : forall i190 k m n191 p r, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> [0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0) -->* ([0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> [0;1]^^r *> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0).
Proof.
  intros. do 11 step. follow cr_BL_01_01. do 2 step. finish_norm.
Qed.

Lemma XP2_round6 : forall n191 i190 k m p r, (0 >> 1 >> 1 >> [0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0) -->* ([0;1;1]^^n191 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0).
Proof.
  intros. follow XP2_st7. follow XP2_loop10_z. follow XP2_st11. finish_norm.
Qed.

Lemma XP2_loop12 : forall n189 i190 k m p r, ([0;1;1]^^n189 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> const 0) -->* (1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i190 *> [1;0;1]^^n189 *> const 0).
Proof.
  induction n189; intros.
  - finish_norm.
  - follow (XP2_round6 n189 i190 k m p r).
    follow (IHn189 (S i190) k m p r).
    finish_norm.
Qed.

Lemma XP2_loop12_z : forall k m p r w, ([0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP2_loop12 w 0 k m p r). finish_norm.
Qed.

Lemma XP2_st13 : forall k m p r w, (1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 3 step. finish_norm.
Qed.

Lemma XP2_st15 : forall i198 k m n199 r w, (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^n199 *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^i198 *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([0;1;0;1;0;1]^^n199 *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^i198 *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 12 step. finish_norm.
Qed.

Lemma XP2_round14 : forall n199 i198 k m r w, (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^n199 *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^i198 *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([0;1;0;1;0;1]^^n199 *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^i198 *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP2_st15. finish_norm.
Qed.

Lemma XP2_loop16 : forall n197 i198 k m r w, ([0;1;0;1;0;1]^^n197 *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^i198 *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^i198 *> [1;1;1;1;0;1]^^n197 *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n197; intros.
  - finish_norm.
  - follow (XP2_round14 n197 i198 k m r w).
    follow (IHn197 (S i198) k m r w).
    finish_norm.
Qed.

Lemma XP2_loop16_z : forall k m p r w, ([0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP2_loop16 p 0 k m r w). finish_norm.
Qed.

Lemma XP2_st17 : forall k m p r w, (1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 141 step. finish_norm.
Qed.

Lemma XP2_st19 : forall i202 k n203 p r w, (1 >> 0 >> 1 >> [1;0;1]^^n203 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i202 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([1;0;1]^^n203 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i202 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 37 step. finish_norm.
Qed.

Lemma XP2_round18 : forall n203 i202 k p r w, (1 >> 0 >> 1 >> [1;0;1]^^n203 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i202 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([1;0;1]^^n203 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i202 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP2_st19. finish_norm.
Qed.

Lemma XP2_loop20 : forall n201 i202 k p r w, ([1;0;1]^^n201 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i202 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i202 *> [1;0;1]^^n201 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n201; intros.
  - finish_norm.
  - follow (XP2_round18 n201 i202 k p r w).
    follow (IHn201 (S i202) k p r w).
    finish_norm.
Qed.

Lemma XP2_loop20_z : forall k m p r w, ([1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP2_loop20 m 0 k p r w). finish_norm.
Qed.

Lemma XP2_st21 : forall k m p r w, (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^m *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 51 step. finish_norm.
Qed.

Lemma XP2_st23 : forall i206 k n207 p r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i206 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n207 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i206 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n207 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 5 step. finish_norm.
Qed.

Lemma XP2_round22 : forall n207 i206 k p r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i206 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n207 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i206 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n207 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP2_st23. finish_norm.
Qed.

Lemma XP2_loop24 : forall n205 i206 k p r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i206 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n205 *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i206 *> [1;0;1]^^n205 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n205; intros.
  - finish_norm.
  - follow (XP2_round22 n205 i206 k p r w).
    follow (IHn205 (S i206) k p r w).
    finish_norm.
Qed.

Lemma XP2_loop24_z : forall k m p r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^m *> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP2_loop24 m 0 k p r w). finish_norm.
Qed.

Lemma XP2_st25 : forall k m p r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 78 step. finish_norm.
Qed.

Lemma XP2_st27 : forall i210 k n211 p r w, (1 >> 0 >> 1 >> [1;0;1]^^n211 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i210 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([1;0;1]^^n211 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i210 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 37 step. finish_norm.
Qed.

Lemma XP2_round26 : forall n211 i210 k p r w, (1 >> 0 >> 1 >> [1;0;1]^^n211 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i210 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([1;0;1]^^n211 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i210 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP2_st27. finish_norm.
Qed.

Lemma XP2_loop28 : forall n209 i210 k p r w, ([1;0;1]^^n209 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i210 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^i210 *> [0;1;1]^^n209 *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n209; intros.
  - finish_norm.
  - follow (XP2_round26 n209 i210 k p r w).
    follow (IHn209 (S i210) k p r w).
    finish_norm.
Qed.

Lemma XP2_loop28_z : forall k m p r w, ([1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^m *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP2_loop28 m 0 k p r w). finish_norm.
Qed.

Lemma XP2_st29 : forall k m p r w, (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^m *> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 44 step. follow cr_GR_011_011. do 1 step.
  repeat rewrite (align_lpow 0 [1;1]). simpl app. do 23 step.
  repeat rewrite (align_lpow 1 [1;0]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0;1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 0 [1;1]). simpl app. do 44 step. follow cr_AR_111101_001000. do 3 step.
  repeat rewrite (align_lpow 0 [0;1;0;0;0]). simpl app. do 4 step. finish_norm.
Qed.

Lemma XP2_st31 : forall i214 k m n215 p w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i214 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n215 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i214 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n215 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP2_round30 : forall n215 i214 k m p w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i214 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n215 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i214 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n215 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP2_st31. finish_norm.
Qed.

Lemma XP2_loop32 : forall n213 i214 k m p w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i214 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n213 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i214 *> [1;0]^^n213 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n213; intros.
  - finish_norm.
  - follow (XP2_round30 n213 i214 k m p w).
    follow (IHn213 (S i214) k m p w).
    finish_norm.
Qed.

Lemma XP2_loop32_z : forall k m p r w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP2_loop32 r 0 k m p w). finish_norm.
Qed.

Lemma XP2_st33 : forall k m p r w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 10 step. follow cr_CL_10_10. do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app.
  do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XP2_st35 : forall i218 k m n219 p w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i218 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n219 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i218 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n219 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP2_round34 : forall n219 i218 k m p w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i218 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n219 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i218 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n219 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP2_st35. finish_norm.
Qed.

Lemma XP2_loop36 : forall n217 i218 k m p w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i218 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n217 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i218 *> [0;1]^^n217 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n217; intros.
  - finish_norm.
  - follow (XP2_round34 n217 i218 k m p w).
    follow (IHn217 (S i218) k m p w).
    finish_norm.
Qed.

Lemma XP2_loop36_z : forall k m p r w, (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP2_loop36 r 0 k m p w). finish_norm.
Qed.

Lemma XP2_st37 : forall k m p r w, (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. finish_norm.
Qed.

Lemma XP2_st39 : forall i222 k m n223 p w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i222 *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n223 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i222 *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n223 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP2_round38 : forall n223 i222 k m p w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i222 *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n223 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i222 *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n223 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP2_st39. finish_norm.
Qed.

Lemma XP2_loop40 : forall n221 i222 k m p w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i222 *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n221 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i222 *> [0;1]^^n221 *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n221; intros.
  - finish_norm.
  - follow (XP2_round38 n221 i222 k m p w).
    follow (IHn221 (S i222) k m p w).
    finish_norm.
Qed.

Lemma XP2_loop40_z : forall k m p r w, (1 >> 0 >> 0 >> 1 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP2_loop40 r 0 k m p w). finish_norm.
Qed.

Lemma XP2_st41 : forall k m p r w, (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. finish_norm.
Qed.

Lemma XP2_st43 : forall i236 k m n237 r w, (0 >> 1 >> 0 >> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 16 step. finish_norm.
Qed.

Lemma XP2_st45 : forall i236 i240 k m n237 n241 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i240 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n241 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i240 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n241 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP2_round44 : forall n241 i240 i236 k m n237 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i240 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n241 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i240 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n241 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP2_st45. finish_norm.
Qed.

Lemma XP2_loop46 : forall n239 i240 i236 k m n237 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i240 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n239 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i240 *> [0;1]^^n239 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0).
Proof.
  induction n239; intros.
  - finish_norm.
  - follow (XP2_round44 n239 i240 i236 k m n237 w).
    follow (IHn239 (S i240) i236 k m n237 w).
    finish_norm.
Qed.

Lemma XP2_loop46_z : forall i236 k m n237 r w, (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP2_loop46 r 0 i236 k m n237 w). finish_norm.
Qed.

Lemma XP2_st47 : forall i236 k m n237 r w, (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. finish_norm.
Qed.

Lemma XP2_st49 : forall i236 i244 k m n237 n245 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i244 *> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n245 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i244 *> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n245 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP2_round48 : forall n245 i244 i236 k m n237 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i244 *> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n245 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i244 *> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n245 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP2_st49. finish_norm.
Qed.

Lemma XP2_loop50 : forall n243 i244 i236 k m n237 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i244 *> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n243 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i244 *> [0;1]^^n243 *> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0).
Proof.
  induction n243; intros.
  - finish_norm.
  - follow (XP2_round48 n243 i244 i236 k m n237 w).
    follow (IHn243 (S i244) i236 k m n237 w).
    finish_norm.
Qed.

Lemma XP2_loop50_z : forall i236 k m n237 r w, (1 >> 0 >> 0 >> 1 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP2_loop50 r 0 i236 k m n237 w). finish_norm.
Qed.

Lemma XP2_st51 : forall i236 k m n237 r w, (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0) -->* ([0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} ([0;1]^^r *> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. finish_norm.
Qed.

Lemma XP2_round42 : forall n237 i236 k m r w, (0 >> 1 >> 0 >> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0) -->* ([0;1;0;0;0;0]^^n237 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP2_st43. follow XP2_loop46_z. follow XP2_st47. follow XP2_loop50_z.
  follow XP2_st51. finish_norm.
Qed.

Lemma XP2_loop52 : forall n235 i236 k m r w, ([0;1;0;0;0;0]^^n235 *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i236 *> [1;0;1;1;0;1]^^n235 *> [1;0;1]^^w *> const 0).
Proof.
  induction n235; intros.
  - finish_norm.
  - follow (XP2_round42 n235 i236 k m r w).
    follow (IHn235 (S i236) k m r w).
    finish_norm.
Qed.

Lemma XP2_loop52_z : forall k m p r w, ([0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^p *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP2_loop52 p 0 k m r w). finish_norm.
Qed.

Lemma XP2_st53 : forall k m p r w, (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^p *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^p *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. follow cr_HR_10_10. do 1 step. follow cr_CL_10_10. do 11 step.
  follow cr_HR_10_10. do 21 step. finish_norm.
Qed.

Lemma XP2_st55 : forall i248 k m n249 r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i248 *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^n249 *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i248 *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^n249 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 10 step. finish_norm.
Qed.

Lemma XP2_round54 : forall n249 i248 k m r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i248 *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^n249 *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i248 *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^n249 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP2_st55. finish_norm.
Qed.

Lemma XP2_loop56 : forall n247 i248 k m r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i248 *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^n247 *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i248 *> [1;0;1;1;0;1]^^n247 *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0).
Proof.
  induction n247; intros.
  - finish_norm.
  - follow (XP2_round54 n247 i248 k m r w).
    follow (IHn247 (S i248) k m r w).
    finish_norm.
Qed.

Lemma XP2_loop56_z : forall k m p r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^p *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^p *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP2_loop56 p 0 k m r w). finish_norm.
Qed.

Lemma XP2_st57 : forall k m p r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^p *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^p *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0).
Proof.
  intros. finish_norm.
Qed.

Lemma XP2_st59 : forall i252 k m n253 p r, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i252 *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n253 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i252 *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n253 *> const 0).
Proof.
  intros. do 5 step. finish_norm.
Qed.

Lemma XP2_round58 : forall n253 i252 k m p r, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i252 *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n253 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i252 *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n253 *> const 0).
Proof.
  intros. follow XP2_st59. finish_norm.
Qed.

Lemma XP2_loop60 : forall n251 i252 k m p r, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i252 *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n251 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i252 *> [1;0;1]^^n251 *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (const 0).
Proof.
  induction n251; intros.
  - finish_norm.
  - follow (XP2_round58 n251 i252 k m p r).
    follow (IHn251 (S i252) k m p r).
    finish_norm.
Qed.

Lemma XP2_loop60_z : forall k m p r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^p *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (const 0).
Proof.
  intros. follow (XP2_loop60 w 0 k m p r). finish_norm.
Qed.

Lemma XP2_st61 : forall k m p r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0).
Proof.
  intros. do 19 step. finish_norm.
Qed.

Lemma EV_P2 : forall k m p r w, (1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> 1 >> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> [1;0;1;1;0;1]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0).
Proof.
  intros.
  follow XP2_st1.
  follow XP2_loop4_z.
  follow XP2_st5.
  follow XP2_loop12_z.
  follow XP2_st13.
  follow XP2_loop16_z.
  follow XP2_st17.
  follow XP2_loop20_z.
  follow XP2_st21.
  follow XP2_loop24_z.
  follow XP2_st25.
  follow XP2_loop28_z.
  follow XP2_st29.
  follow XP2_loop32_z.
  follow XP2_st33.
  follow XP2_loop36_z.
  follow XP2_st37.
  follow XP2_loop40_z.
  follow XP2_st41.
  follow XP2_loop52_z.
  follow XP2_st53.
  follow XP2_loop56_z.
  follow XP2_st57.
  follow XP2_loop60_z.
  follow XP2_st61.
  finish_norm.
Qed.

Lemma XP3_st1 : forall a k m w, (1 >> [0;1]^^a *> 1 >> [1;0;1]^^w *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^w *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^a *> const 0).
Proof.
  intros. do 2 step. follow cr_BL_01_01. do 1 step. repeat rewrite (align_lpow 1 [0;1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 0 [1;1]). simpl app. do 3 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow_const 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XP3_st3 : forall i256 k m n257 w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i256 *> 1 >> [1;0;1]^^w *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n257 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i256 *> 1 >> [1;0;1]^^w *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n257 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP3_round2 : forall n257 i256 k m w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i256 *> 1 >> [1;0;1]^^w *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n257 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i256 *> 1 >> [1;0;1]^^w *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n257 *> const 0).
Proof.
  intros. follow XP3_st3. finish_norm.
Qed.

Lemma XP3_loop4 : forall n255 i256 k m w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i256 *> 1 >> [1;0;1]^^w *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n255 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i256 *> [0;1]^^n255 *> 1 >> [1;0;1]^^w *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0).
Proof.
  induction n255; intros.
  - finish_norm.
  - follow (XP3_round2 n255 i256 k m w).
    follow (IHn255 (S i256) k m w).
    finish_norm.
Qed.

Lemma XP3_loop4_z : forall a k m w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^w *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^a *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^w *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0).
Proof.
  intros. follow (XP3_loop4 a 0 k m w). finish_norm.
Qed.

Lemma XP3_st5 : forall a k m w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^w *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0) -->* ([1;0;1]^^w *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 1 step. finish_norm.
Qed.

Lemma XP3_st7 : forall a i266 k m n267, (1 >> 0 >> 1 >> [1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0).
Proof.
  intros. do 11 step. finish_norm.
Qed.

Lemma XP3_st9 : forall i266 i270 k m n267 n271, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i270 *> 1 >> [1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n271 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i270 *> 1 >> [1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n271 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP3_round8 : forall n271 i270 i266 k m n267, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i270 *> 1 >> [1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n271 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i270 *> 1 >> [1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n271 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0).
Proof.
  intros. follow XP3_st9. finish_norm.
Qed.

Lemma XP3_loop10 : forall n269 i270 i266 k m n267, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i270 *> 1 >> [1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n269 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i270 *> [0;1]^^n269 *> 1 >> [1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0).
Proof.
  induction n269; intros.
  - finish_norm.
  - follow (XP3_round8 n269 i270 i266 k m n267).
    follow (IHn269 (S i270) i266 k m n267).
    finish_norm.
Qed.

Lemma XP3_loop10_z : forall a i266 k m n267, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0).
Proof.
  intros. follow (XP3_loop10 a 0 i266 k m n267). finish_norm.
Qed.

Lemma XP3_st11 : forall a i266 k m n267, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> [1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0) -->* ([1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> [0;1]^^a *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. do 1 step. finish_norm.
Qed.

Lemma XP3_round6 : forall n267 i266 a k m, (1 >> 0 >> 1 >> [1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0) -->* ([1;0;1]^^n267 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0).
Proof.
  intros. follow XP3_st7. follow XP3_loop10_z. follow XP3_st11. finish_norm.
Qed.

Lemma XP3_loop12 : forall n265 i266 a k m, ([1;0;1]^^n265 *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> const 0) -->* (0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i266 *> [1;0;1]^^n265 *> const 0).
Proof.
  induction n265; intros.
  - finish_norm.
  - follow (XP3_round6 n265 i266 a k m).
    follow (IHn265 (S i266) a k m).
    finish_norm.
Qed.

Lemma XP3_loop12_z : forall a k m w, ([1;0;1]^^w *> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP3_loop12 w 0 a k m). finish_norm.
Qed.

Lemma XP3_st13 : forall a k m w, (0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{F}} (1 >> 0 >> 1 >> 0 >> [1;0]^^a *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> ([0;1]^^a *> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 7 step. follow cr_HR_10_10. do 1 step. follow cr_CL_10_10. do 23 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step. finish_norm.
Qed.

Lemma XP3_st15 : forall i274 k m n275 w, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i274 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> (0 >> 1 >> [0;1]^^n275 *> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i274 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> ([0;1]^^n275 *> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP3_round14 : forall n275 i274 k m w, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i274 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> (0 >> 1 >> [0;1]^^n275 *> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i274 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> ([0;1]^^n275 *> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP3_st15. finish_norm.
Qed.

Lemma XP3_loop16 : forall n273 i274 k m w, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i274 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> ([0;1]^^n273 *> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i274 *> [0;1]^^n273 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> (1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n273; intros.
  - finish_norm.
  - follow (XP3_round14 n273 i274 k m w).
    follow (IHn273 (S i274) k m w).
    finish_norm.
Qed.

Lemma XP3_loop16_z : forall a k m w, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> ([0;1]^^a *> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> (1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP3_loop16 a 0 k m w). finish_norm.
Qed.

Lemma XP3_st17 : forall a k m w, (0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{A}}> (1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> ([0;1;0]^^w *> 1 >> const 0).
Proof.
  intros. do 7 step. follow cr_AR_101_001. do 3 step. follow cr_BL_001_001. do 16 step.
  follow cr_BL_01_01. do 5 step. follow cr_GR_01_01. do 15 step. follow cr_BL_01_01. do 9 step.
  follow cr_GR_01_01. do 28 step. repeat rewrite (align_lpow 0 [0;1]). simpl app. do 1 step.
  finish_norm.
Qed.

Lemma XP3_st19 : forall a i278 k m n279, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i278 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (0 >> 1 >> 0 >> [0;1;0]^^n279 *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i278 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> ([0;1;0]^^n279 *> 1 >> const 0).
Proof.
  intros. do 17 step. finish_norm.
Qed.

Lemma XP3_round18 : forall n279 i278 a k m, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i278 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (0 >> 1 >> 0 >> [0;1;0]^^n279 *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i278 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> ([0;1;0]^^n279 *> 1 >> const 0).
Proof.
  intros. follow XP3_st19. finish_norm.
Qed.

Lemma XP3_loop20 : forall n277 i278 a k m, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i278 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> ([0;1;0]^^n277 *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i278 *> [1;0;1]^^n277 *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (1 >> const 0).
Proof.
  induction n277; intros.
  - finish_norm.
  - follow (XP3_round18 n277 i278 a k m).
    follow (IHn277 (S i278) a k m).
    finish_norm.
Qed.

Lemma XP3_loop20_z : forall a k m w, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> ([0;1;0]^^w *> 1 >> const 0) -->* (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (1 >> const 0).
Proof.
  intros. follow (XP3_loop20 w 0 a k m). finish_norm.
Qed.

Lemma XP3_st21 : forall a k m w, (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (1 >> const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0).
Proof.
  intros. do 46 step. finish_norm.
Qed.

Lemma EV_P3 : forall a k m w, (1 >> [0;1]^^a *> 1 >> [1;0;1]^^w *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> [1;0;1]^^w *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^a *> 1 >> 1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0).
Proof.
  intros.
  follow XP3_st1.
  follow XP3_loop4_z.
  follow XP3_st5.
  follow XP3_loop12_z.
  follow XP3_st13.
  follow XP3_loop16_z.
  follow XP3_st17.
  follow XP3_loop20_z.
  follow XP3_st21.
  finish_norm.
Qed.

Lemma XP4_st1 : forall k m q r w, (1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> 1 >> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^w *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> const 0).
Proof.
  intros. do 4 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow_const 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XP4_st3 : forall i282 k m n283 q w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i282 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n283 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i282 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n283 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP4_round2 : forall n283 i282 k m q w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i282 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n283 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i282 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n283 *> const 0).
Proof.
  intros. follow XP4_st3. finish_norm.
Qed.

Lemma XP4_loop4 : forall n281 i282 k m q w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i282 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n281 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i282 *> [0;1]^^n281 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0).
Proof.
  induction n281; intros.
  - finish_norm.
  - follow (XP4_round2 n281 i282 k m q w).
    follow (IHn281 (S i282) k m q w).
    finish_norm.
Qed.

Lemma XP4_loop4_z : forall k m q r w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^w *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> [0;1;1]^^w *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0).
Proof.
  intros. follow (XP4_loop4 r 0 k m q w). finish_norm.
Qed.

Lemma XP4_st5 : forall k m q r w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> [0;1;1]^^w *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0) -->* ([0;1;1]^^w *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 11 step. follow cr_BL_01_01. do 2 step. finish_norm.
Qed.

Lemma XP4_st7 : forall i292 k m n293 q r, (0 >> 1 >> 1 >> [0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0).
Proof.
  intros. do 16 step. finish_norm.
Qed.

Lemma XP4_st9 : forall i292 i296 k m n293 n297 q, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i296 *> 1 >> 1 >> [0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n297 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i296 *> 1 >> 1 >> [0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n297 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP4_round8 : forall n297 i296 i292 k m n293 q, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i296 *> 1 >> 1 >> [0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n297 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i296 *> 1 >> 1 >> [0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n297 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0).
Proof.
  intros. follow XP4_st9. finish_norm.
Qed.

Lemma XP4_loop10 : forall n295 i296 i292 k m n293 q, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i296 *> 1 >> 1 >> [0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n295 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i296 *> [0;1]^^n295 *> 1 >> 1 >> [0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0).
Proof.
  induction n295; intros.
  - finish_norm.
  - follow (XP4_round8 n295 i296 i292 k m n293 q).
    follow (IHn295 (S i296) i292 k m n293 q).
    finish_norm.
Qed.

Lemma XP4_loop10_z : forall i292 k m n293 q r, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> [0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0).
Proof.
  intros. follow (XP4_loop10 r 0 i292 k m n293 q). finish_norm.
Qed.

Lemma XP4_st11 : forall i292 k m n293 q r, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> [0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0) -->* ([0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> [0;1]^^r *> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0).
Proof.
  intros. do 11 step. follow cr_BL_01_01. do 2 step. finish_norm.
Qed.

Lemma XP4_round6 : forall n293 i292 k m q r, (0 >> 1 >> 1 >> [0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0) -->* ([0;1;1]^^n293 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0).
Proof.
  intros. follow XP4_st7. follow XP4_loop10_z. follow XP4_st11. finish_norm.
Qed.

Lemma XP4_loop12 : forall n291 i292 k m q r, ([0;1;1]^^n291 *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> const 0) -->* (1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i292 *> [1;0;1]^^n291 *> const 0).
Proof.
  induction n291; intros.
  - finish_norm.
  - follow (XP4_round6 n291 i292 k m q r).
    follow (IHn291 (S i292) k m q r).
    finish_norm.
Qed.

Lemma XP4_loop12_z : forall k m q r w, ([0;1;1]^^w *> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP4_loop12 w 0 k m q r). finish_norm.
Qed.

Lemma XP4_st13 : forall k m q r w, (1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 1 step. follow cr_EL_010101_111011. do 29 step. follow cr_AR_111011_000100. do 16 step.
  finish_norm.
Qed.

Lemma XP4_st15 : forall i300 k m n301 q w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i300 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n301 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i300 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n301 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP4_round14 : forall n301 i300 k m q w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i300 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n301 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i300 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n301 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP4_st15. finish_norm.
Qed.

Lemma XP4_loop16 : forall n299 i300 k m q w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i300 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n299 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i300 *> [1;0]^^n299 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n299; intros.
  - finish_norm.
  - follow (XP4_round14 n299 i300 k m q w).
    follow (IHn299 (S i300) k m q w).
    finish_norm.
Qed.

Lemma XP4_loop16_z : forall k m q r w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP4_loop16 r 0 k m q w). finish_norm.
Qed.

Lemma XP4_st17 : forall k m q r w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 10 step. follow cr_CL_10_10. do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app.
  do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XP4_st19 : forall i304 k m n305 q w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i304 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n305 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i304 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n305 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP4_round18 : forall n305 i304 k m q w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i304 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n305 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i304 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n305 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP4_st19. finish_norm.
Qed.

Lemma XP4_loop20 : forall n303 i304 k m q w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i304 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n303 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i304 *> [0;1]^^n303 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n303; intros.
  - finish_norm.
  - follow (XP4_round18 n303 i304 k m q w).
    follow (IHn303 (S i304) k m q w).
    finish_norm.
Qed.

Lemma XP4_loop20_z : forall k m q r w, (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP4_loop20 r 0 k m q w). finish_norm.
Qed.

Lemma XP4_st21 : forall k m q r w, (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. finish_norm.
Qed.

Lemma XP4_st23 : forall i308 k m n309 q w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i308 *> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n309 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i308 *> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n309 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP4_round22 : forall n309 i308 k m q w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i308 *> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n309 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i308 *> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n309 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP4_st23. finish_norm.
Qed.

Lemma XP4_loop24 : forall n307 i308 k m q w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i308 *> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n307 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i308 *> [0;1]^^n307 *> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n307; intros.
  - finish_norm.
  - follow (XP4_round22 n307 i308 k m q w).
    follow (IHn307 (S i308) k m q w).
    finish_norm.
Qed.

Lemma XP4_loop24_z : forall k m q r w, (1 >> 0 >> 0 >> 1 >> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP4_loop24 r 0 k m q w). finish_norm.
Qed.

Lemma XP4_st25 : forall k m q r w, (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> [0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. finish_norm.
Qed.

Lemma XP4_st27 : forall i322 k m n323 r w, (0 >> 1 >> 0 >> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 16 step. finish_norm.
Qed.

Lemma XP4_st29 : forall i322 i326 k m n323 n327 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i326 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n327 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i326 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n327 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP4_round28 : forall n327 i326 i322 k m n323 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i326 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n327 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i326 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n327 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP4_st29. finish_norm.
Qed.

Lemma XP4_loop30 : forall n325 i326 i322 k m n323 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i326 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n325 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i326 *> [0;1]^^n325 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0).
Proof.
  induction n325; intros.
  - finish_norm.
  - follow (XP4_round28 n325 i326 i322 k m n323 w).
    follow (IHn325 (S i326) i322 k m n323 w).
    finish_norm.
Qed.

Lemma XP4_loop30_z : forall i322 k m n323 r w, (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP4_loop30 r 0 i322 k m n323 w). finish_norm.
Qed.

Lemma XP4_st31 : forall i322 k m n323 r w, (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. finish_norm.
Qed.

Lemma XP4_st33 : forall i322 i330 k m n323 n331 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i330 *> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n331 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i330 *> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n331 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XP4_round32 : forall n331 i330 i322 k m n323 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i330 *> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n331 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i330 *> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n331 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP4_st33. finish_norm.
Qed.

Lemma XP4_loop34 : forall n329 i330 i322 k m n323 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i330 *> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n329 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i330 *> [0;1]^^n329 *> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0).
Proof.
  induction n329; intros.
  - finish_norm.
  - follow (XP4_round32 n329 i330 i322 k m n323 w).
    follow (IHn329 (S i330) i322 k m n323 w).
    finish_norm.
Qed.

Lemma XP4_loop34_z : forall i322 k m n323 r w, (1 >> 0 >> 0 >> 1 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP4_loop34 r 0 i322 k m n323 w). finish_norm.
Qed.

Lemma XP4_st35 : forall i322 k m n323 r w, (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0) -->* ([0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} ([0;1]^^r *> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. finish_norm.
Qed.

Lemma XP4_round26 : forall n323 i322 k m r w, (0 >> 1 >> 0 >> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0) -->* ([0;1;0;0;0;0]^^n323 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP4_st27. follow XP4_loop30_z. follow XP4_st31. follow XP4_loop34_z.
  follow XP4_st35. finish_norm.
Qed.

Lemma XP4_loop36 : forall n321 i322 k m r w, ([0;1;0;0;0;0]^^n321 *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i322 *> [1;0;1;1;0;1]^^n321 *> [1;0;1]^^w *> const 0).
Proof.
  induction n321; intros.
  - finish_norm.
  - follow (XP4_round26 n321 i322 k m r w).
    follow (IHn321 (S i322) k m r w).
    finish_norm.
Qed.

Lemma XP4_loop36_z : forall k m q r w, ([0;1;0;0;0;0]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^q *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP4_loop36 q 0 k m r w). finish_norm.
Qed.

Lemma XP4_st37 : forall k m q r w, (1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^q *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^q *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. follow cr_HR_10_10. do 1 step. follow cr_CL_10_10. do 11 step.
  follow cr_HR_10_10. do 21 step. finish_norm.
Qed.

Lemma XP4_st39 : forall i334 k m n335 r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i334 *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^n335 *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i334 *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^n335 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 10 step. finish_norm.
Qed.

Lemma XP4_round38 : forall n335 i334 k m r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i334 *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^n335 *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i334 *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^n335 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XP4_st39. finish_norm.
Qed.

Lemma XP4_loop40 : forall n333 i334 k m r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i334 *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^n333 *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i334 *> [1;0;1;1;0;1]^^n333 *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0).
Proof.
  induction n333; intros.
  - finish_norm.
  - follow (XP4_round38 n333 i334 k m r w).
    follow (IHn333 (S i334) k m r w).
    finish_norm.
Qed.

Lemma XP4_loop40_z : forall k m q r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^q *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^q *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0).
Proof.
  intros. follow (XP4_loop40 q 0 k m r w). finish_norm.
Qed.

Lemma XP4_st41 : forall k m q r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^q *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^q *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0).
Proof.
  intros. finish_norm.
Qed.

Lemma XP4_st43 : forall i338 k m n339 q r, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i338 *> [1;0;1;1;0;1]^^q *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n339 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i338 *> [1;0;1;1;0;1]^^q *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n339 *> const 0).
Proof.
  intros. do 5 step. finish_norm.
Qed.

Lemma XP4_round42 : forall n339 i338 k m q r, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i338 *> [1;0;1;1;0;1]^^q *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n339 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i338 *> [1;0;1;1;0;1]^^q *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n339 *> const 0).
Proof.
  intros. follow XP4_st43. finish_norm.
Qed.

Lemma XP4_loop44 : forall n337 i338 k m q r, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i338 *> [1;0;1;1;0;1]^^q *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n337 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i338 *> [1;0;1]^^n337 *> [1;0;1;1;0;1]^^q *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (const 0).
Proof.
  induction n337; intros.
  - finish_norm.
  - follow (XP4_round42 n337 i338 k m q r).
    follow (IHn337 (S i338) k m q r).
    finish_norm.
Qed.

Lemma XP4_loop44_z : forall k m q r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^q *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> [1;0;1;1;0;1]^^q *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (const 0).
Proof.
  intros. follow (XP4_loop44 w 0 k m q r). finish_norm.
Qed.

Lemma XP4_st45 : forall k m q r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> [1;0;1;1;0;1]^^q *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> [1;0;1;1;0;1]^^q *> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0).
Proof.
  intros. do 19 step. finish_norm.
Qed.

Lemma EV_P4 : forall k m q r w, (1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> 1 >> 1 >> [0;1;0;1;0;1]^^q *> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> [1;0;1;1;0;1]^^q *> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0).
Proof.
  intros.
  follow XP4_st1.
  follow XP4_loop4_z.
  follow XP4_st5.
  follow XP4_loop12_z.
  follow XP4_st13.
  follow XP4_loop16_z.
  follow XP4_st17.
  follow XP4_loop20_z.
  follow XP4_st21.
  follow XP4_loop24_z.
  follow XP4_st25.
  follow XP4_loop36_z.
  follow XP4_st37.
  follow XP4_loop40_z.
  follow XP4_st41.
  follow XP4_loop44_z.
  follow XP4_st45.
  finish_norm.
Qed.

Lemma XE_st1 : forall k p r w, (1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> 1 >> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> const 0).
Proof.
  intros. do 4 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow_const 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XE_st3 : forall i342 k n343 p w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i342 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n343 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i342 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n343 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XE_round2 : forall n343 i342 k p w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i342 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n343 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i342 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n343 *> const 0).
Proof.
  intros. follow XE_st3. finish_norm.
Qed.

Lemma XE_loop4 : forall n341 i342 k p w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i342 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n341 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i342 *> [0;1]^^n341 *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0).
Proof.
  induction n341; intros.
  - finish_norm.
  - follow (XE_round2 n341 i342 k p w).
    follow (IHn341 (S i342) k p w).
    finish_norm.
Qed.

Lemma XE_loop4_z : forall k p r w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0).
Proof.
  intros. follow (XE_loop4 r 0 k p w). finish_norm.
Qed.

Lemma XE_st5 : forall k p r w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> [0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0) -->* ([0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 11 step. follow cr_BL_01_01. do 2 step. finish_norm.
Qed.

Lemma XE_st7 : forall i352 k n353 p r, (0 >> 1 >> 1 >> [0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0).
Proof.
  intros. do 16 step. finish_norm.
Qed.

Lemma XE_st9 : forall i352 i356 k n353 n357 p, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i356 *> 1 >> 1 >> [0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n357 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i356 *> 1 >> 1 >> [0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n357 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XE_round8 : forall n357 i356 i352 k n353 p, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i356 *> 1 >> 1 >> [0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n357 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i356 *> 1 >> 1 >> [0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n357 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0).
Proof.
  intros. follow XE_st9. finish_norm.
Qed.

Lemma XE_loop10 : forall n355 i356 i352 k n353 p, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i356 *> 1 >> 1 >> [0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n355 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i356 *> [0;1]^^n355 *> 1 >> 1 >> [0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0).
Proof.
  induction n355; intros.
  - finish_norm.
  - follow (XE_round8 n355 i356 i352 k n353 p).
    follow (IHn355 (S i356) i352 k n353 p).
    finish_norm.
Qed.

Lemma XE_loop10_z : forall i352 k n353 p r, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> [0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0).
Proof.
  intros. follow (XE_loop10 r 0 i352 k n353 p). finish_norm.
Qed.

Lemma XE_st11 : forall i352 k n353 p r, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> [0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0) -->* ([0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> [0;1]^^r *> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0).
Proof.
  intros. do 11 step. follow cr_BL_01_01. do 2 step. finish_norm.
Qed.

Lemma XE_round6 : forall n353 i352 k p r, (0 >> 1 >> 1 >> [0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0) -->* ([0;1;1]^^n353 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0).
Proof.
  intros. follow XE_st7. follow XE_loop10_z. follow XE_st11. finish_norm.
Qed.

Lemma XE_loop12 : forall n351 i352 k p r, ([0;1;1]^^n351 *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> const 0) -->* (1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i352 *> [1;0;1]^^n351 *> const 0).
Proof.
  induction n351; intros.
  - finish_norm.
  - follow (XE_round6 n351 i352 k p r).
    follow (IHn351 (S i352) k p r).
    finish_norm.
Qed.

Lemma XE_loop12_z : forall k p r w, ([0;1;1]^^w *> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XE_loop12 w 0 k p r). finish_norm.
Qed.

Lemma XE_st13 : forall k p r w, (1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{D}} (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 3 step. finish_norm.
Qed.

Lemma XE_st15 : forall i360 k n361 r w, (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^n361 *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^i360 *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([0;1;0;1;0;1]^^n361 *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^i360 *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 12 step. finish_norm.
Qed.

Lemma XE_round14 : forall n361 i360 k r w, (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^n361 *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^i360 *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([0;1;0;1;0;1]^^n361 *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^i360 *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XE_st15. finish_norm.
Qed.

Lemma XE_loop16 : forall n359 i360 k r w, ([0;1;0;1;0;1]^^n359 *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^i360 *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^i360 *> [1;1;1;1;0;1]^^n359 *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n359; intros.
  - finish_norm.
  - follow (XE_round14 n359 i360 k r w).
    follow (IHn359 (S i360) k r w).
    finish_norm.
Qed.

Lemma XE_loop16_z : forall k p r w, ([0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XE_loop16 p 0 k r w). finish_norm.
Qed.

Lemma XE_st17 : forall k p r w, (1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{I}} (0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1;1;1;1;0;1]^^p *> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 648 step. follow cr_AR_111101_001000. do 3 step.
  repeat rewrite (align_lpow 0 [0;1;0;0;0]). simpl app. do 4 step. finish_norm.
Qed.

Lemma XE_st19 : forall i364 k n365 p w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i364 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n365 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i364 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n365 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XE_round18 : forall n365 i364 k p w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i364 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n365 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i364 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n365 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XE_st19. finish_norm.
Qed.

Lemma XE_loop20 : forall n363 i364 k p w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i364 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n363 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^i364 *> [1;0]^^n363 *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n363; intros.
  - finish_norm.
  - follow (XE_round18 n363 i364 k p w).
    follow (IHn363 (S i364) k p w).
    finish_norm.
Qed.

Lemma XE_loop20_z : forall k p r w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XE_loop20 r 0 k p w). finish_norm.
Qed.

Lemma XE_st21 : forall k p r w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 10 step. follow cr_CL_10_10. do 1 step. repeat rewrite (align_lpow 1 [0]). simpl app.
  do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XE_st23 : forall i368 k n369 p w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i368 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n369 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i368 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n369 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XE_round22 : forall n369 i368 k p w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i368 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n369 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i368 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n369 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XE_st23. finish_norm.
Qed.

Lemma XE_loop24 : forall n367 i368 k p w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i368 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n367 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i368 *> [0;1]^^n367 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n367; intros.
  - finish_norm.
  - follow (XE_round22 n367 i368 k p w).
    follow (IHn367 (S i368) k p w).
    finish_norm.
Qed.

Lemma XE_loop24_z : forall k p r w, (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XE_loop24 r 0 k p w). finish_norm.
Qed.

Lemma XE_st25 : forall k p r w, (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. finish_norm.
Qed.

Lemma XE_st27 : forall i372 k n373 p w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i372 *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n373 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i372 *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n373 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XE_round26 : forall n373 i372 k p w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i372 *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n373 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i372 *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n373 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XE_st27. finish_norm.
Qed.

Lemma XE_loop28 : forall n371 i372 k p w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i372 *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n371 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i372 *> [0;1]^^n371 *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  induction n371; intros.
  - finish_norm.
  - follow (XE_round26 n371 i372 k p w).
    follow (IHn371 (S i372) k p w).
    finish_norm.
Qed.

Lemma XE_loop28_z : forall k p r w, (1 >> 0 >> 0 >> 1 >> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XE_loop28 r 0 k p w). finish_norm.
Qed.

Lemma XE_st29 : forall k p r w, (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> [0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* ([0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. finish_norm.
Qed.

Lemma XE_st31 : forall i386 k n387 r w, (0 >> 1 >> 0 >> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 16 step. finish_norm.
Qed.

Lemma XE_st33 : forall i386 i390 k n387 n391 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i390 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n391 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i390 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n391 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XE_round32 : forall n391 i390 i386 k n387 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i390 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n391 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i390 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n391 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XE_st33. finish_norm.
Qed.

Lemma XE_loop34 : forall n389 i390 i386 k n387 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i390 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n389 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i390 *> [0;1]^^n389 *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0).
Proof.
  induction n389; intros.
  - finish_norm.
  - follow (XE_round32 n389 i390 i386 k n387 w).
    follow (IHn389 (S i390) i386 k n387 w).
    finish_norm.
Qed.

Lemma XE_loop34_z : forall i386 k n387 r w, (1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XE_loop34 r 0 i386 k n387 w). finish_norm.
Qed.

Lemma XE_st35 : forall i386 k n387 r w, (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. do 5 step. repeat rewrite (align_lpow 0 [1]). simpl app.
  do 1 step. finish_norm.
Qed.

Lemma XE_st37 : forall i386 i394 k n387 n395 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i394 *> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n395 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i394 *> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n395 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XE_round36 : forall n395 i394 i386 k n387 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i394 *> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n395 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i394 *> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n395 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XE_st37. finish_norm.
Qed.

Lemma XE_loop38 : forall n393 i394 i386 k n387 w, (1 >> 0 >> 0 >> 1 >> [0;1]^^i394 *> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n393 *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^i394 *> [0;1]^^n393 *> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0).
Proof.
  induction n393; intros.
  - finish_norm.
  - follow (XE_round36 n393 i394 i386 k n387 w).
    follow (IHn393 (S i394) i386 k n387 w).
    finish_norm.
Qed.

Lemma XE_loop38_z : forall i386 k n387 r w, (1 >> 0 >> 0 >> 1 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XE_loop38 r 0 i386 k n387 w). finish_norm.
Qed.

Lemma XE_st39 : forall i386 k n387 r w, (1 >> 0 >> 0 >> 1 >> [0;1]^^r *> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0) -->* ([0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} ([0;1]^^r *> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 7 step. follow cr_BL_01_01. finish_norm.
Qed.

Lemma XE_round30 : forall n387 i386 k r w, (0 >> 1 >> 0 >> 0 >> 0 >> 0 >> [0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0) -->* ([0;1;0;0;0;0]^^n387 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XE_st31. follow XE_loop34_z. follow XE_st35. follow XE_loop38_z. follow XE_st39.
  finish_norm.
Qed.

Lemma XE_loop40 : forall n385 i386 k r w, ([0;1;0;0;0;0]^^n385 *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i386 *> [1;0;1;1;0;1]^^n385 *> [1;0;1]^^w *> const 0).
Proof.
  induction n385; intros.
  - finish_norm.
  - follow (XE_round30 n385 i386 k r w).
    follow (IHn385 (S i386) k r w).
    finish_norm.
Qed.

Lemma XE_loop40_z : forall k p r w, ([0;1;0;0;0;0]^^p *> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^p *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XE_loop40 p 0 k r w). finish_norm.
Qed.

Lemma XE_st41 : forall k p r w, (1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^p *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^p *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 6 step. follow cr_HR_10_10. do 1 step. follow cr_CL_10_10. do 11 step.
  follow cr_HR_10_10. do 21 step. finish_norm.
Qed.

Lemma XE_st43 : forall i398 k n399 r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i398 *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^n399 *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i398 *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^n399 *> [1;0;1]^^w *> const 0).
Proof.
  intros. do 10 step. finish_norm.
Qed.

Lemma XE_round42 : forall n399 i398 k r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i398 *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^n399 *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i398 *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^n399 *> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XE_st43. finish_norm.
Qed.

Lemma XE_loop44 : forall n397 i398 k r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i398 *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^n397 *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^i398 *> [1;0;1;1;0;1]^^n397 *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0).
Proof.
  induction n397; intros.
  - finish_norm.
  - follow (XE_round42 n397 i398 k r w).
    follow (IHn397 (S i398) k r w).
    finish_norm.
Qed.

Lemma XE_loop44_z : forall k p r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1;1;0;1]^^p *> [1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^p *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0).
Proof.
  intros. follow (XE_loop44 p 0 k r w). finish_norm.
Qed.

Lemma XE_st45 : forall k p r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^p *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^p *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0).
Proof.
  intros. finish_norm.
Qed.

Lemma XE_st47 : forall i402 k n403 p r, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i402 *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n403 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i402 *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n403 *> const 0).
Proof.
  intros. do 5 step. finish_norm.
Qed.

Lemma XE_round46 : forall n403 i402 k p r, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i402 *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (1 >> 0 >> 1 >> [1;0;1]^^n403 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i402 *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n403 *> const 0).
Proof.
  intros. follow XE_st47. finish_norm.
Qed.

Lemma XE_loop48 : forall n401 i402 k p r, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i402 *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^n401 *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i402 *> [1;0;1]^^n401 *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (const 0).
Proof.
  induction n401; intros.
  - finish_norm.
  - follow (XE_round46 n401 i402 k p r).
    follow (IHn401 (S i402) k p r).
    finish_norm.
Qed.

Lemma XE_loop48_z : forall k p r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;1;0;1]^^p *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> ([1;0;1]^^w *> const 0) -->* (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (const 0).
Proof.
  intros. follow (XE_loop48 w 0 k p r). finish_norm.
Qed.

Lemma XE_st49 : forall k p r w, (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{G}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> [1;0;1;1;0;1]^^p *> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^r *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0).
Proof.
  intros. do 19 step. finish_norm.
Qed.

Lemma EV_E : forall k p r w, (1 >> 0 >> 1 >> [0;1]^^r *> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> 1 >> 1 >> 0 >> 1 >> [0;1;0;1;0;1]^^p *> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> [1;0;1;1;0;1]^^p *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^r *> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0).
Proof.
  intros.
  follow XE_st1.
  follow XE_loop4_z.
  follow XE_st5.
  follow XE_loop12_z.
  follow XE_st13.
  follow XE_loop16_z.
  follow XE_st17.
  follow XE_loop20_z.
  follow XE_st21.
  follow XE_loop24_z.
  follow XE_st25.
  follow XE_loop28_z.
  follow XE_st29.
  follow XE_loop40_z.
  follow XE_st41.
  follow XE_loop44_z.
  follow XE_st45.
  follow XE_loop48_z.
  follow XE_st49.
  finish_norm.
Qed.

Lemma XHALT_st1 : forall f k w, (1 >> [0;1]^^f *> 1 >> [1;0;1]^^w *> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [1;1;0]^^w *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^f *> const 0).
Proof.
  intros. do 2 step. follow cr_BL_01_01. do 1 step. repeat rewrite (align_lpow 1 [0;1]). simpl app.
  do 1 step. repeat rewrite (align_lpow 0 [1;1]). simpl app. do 3 step.
  repeat rewrite (align_lpow 0 [1]). simpl app. do 1 step.
  repeat rewrite (align_lpow 1 [0]). simpl app. do 5 step.
  repeat rewrite (align_lpow_const 0 [1]). simpl app. do 1 step. finish_norm.
Qed.

Lemma XHALT_st3 : forall i406 k n407 w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i406 *> [1;1;0]^^w *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n407 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i406 *> [1;1;0]^^w *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n407 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XHALT_round2 : forall n407 i406 k w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i406 *> [1;1;0]^^w *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n407 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i406 *> [1;1;0]^^w *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n407 *> const 0).
Proof.
  intros. follow XHALT_st3. finish_norm.
Qed.

Lemma XHALT_loop4 : forall n405 i406 k w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i406 *> [1;1;0]^^w *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n405 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i406 *> [0;1]^^n405 *> [1;1;0]^^w *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0).
Proof.
  induction n405; intros.
  - finish_norm.
  - follow (XHALT_round2 n405 i406 k w).
    follow (IHn405 (S i406) k w).
    finish_norm.
Qed.

Lemma XHALT_loop4_z : forall f k w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [1;1;0]^^w *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^f *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^f *> [1;1;0]^^w *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0).
Proof.
  intros. follow (XHALT_loop4 f 0 k w). finish_norm.
Qed.

Lemma XHALT_st5 : forall f k w, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^f *> [1;1;0]^^w *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (const 0) -->* ([1;1;0]^^w *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> 1 >> 0 >> [1;0]^^f *> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. finish_norm.
Qed.

Lemma XHALT_st7 : forall f i416 k n417, (1 >> 1 >> 0 >> [1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> 1 >> 0 >> [1;0]^^f *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^f *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0).
Proof.
  intros. do 12 step. finish_norm.
Qed.

Lemma XHALT_st9 : forall i416 i420 k n417 n421, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i420 *> [1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n421 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i420 *> [1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n421 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0).
Proof.
  intros. do 6 step. finish_norm.
Qed.

Lemma XHALT_round8 : forall n421 i420 i416 k n417, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i420 *> [1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (1 >> 0 >> [1;0]^^n421 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i420 *> [1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n421 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0).
Proof.
  intros. follow XHALT_st9. finish_norm.
Qed.

Lemma XHALT_loop10 : forall n419 i420 i416 k n417, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i420 *> [1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^n419 *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^i420 *> [0;1]^^n419 *> [1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0).
Proof.
  induction n419; intros.
  - finish_norm.
  - follow (XHALT_round8 n419 i420 i416 k n417).
    follow (IHn419 (S i420) i416 k n417).
    finish_norm.
Qed.

Lemma XHALT_loop10_z : forall f i416 k n417, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> ([1;0]^^f *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0) -->* (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^f *> [1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0).
Proof.
  intros. follow (XHALT_loop10 f 0 i416 k n417). finish_norm.
Qed.

Lemma XHALT_st11 : forall f i416 k n417, (1 >> 0 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^f *> [1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{B}}> (0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0) -->* ([1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} ([0;1]^^f *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0).
Proof.
  intros. do 9 step. follow cr_BL_01_01. finish_norm.
Qed.

Lemma XHALT_round6 : forall n417 i416 f k, (1 >> 1 >> 0 >> [1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> 1 >> 0 >> [1;0]^^f *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0) -->* ([1;1;0]^^n417 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> 1 >> 0 >> [1;0]^^f *> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0).
Proof.
  intros. follow XHALT_st7. follow XHALT_loop10_z. follow XHALT_st11. finish_norm.
Qed.

Lemma XHALT_loop12 : forall n415 i416 f k, ([1;1;0]^^n415 *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> 1 >> 0 >> [1;0]^^f *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> const 0) -->* (0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> 1 >> 0 >> [1;0]^^f *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^i416 *> [1;0;1]^^n415 *> const 0).
Proof.
  induction n415; intros.
  - finish_norm.
  - follow (XHALT_round6 n415 i416 f k).
    follow (IHn415 (S i416) f k).
    finish_norm.
Qed.

Lemma XHALT_loop12_z : forall f k w, ([1;1;0]^^w *> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> 1 >> 0 >> [1;0]^^f *> 0 >> 1 >> 0 >> 1 >> const 0) -->* (0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> 1 >> 0 >> [1;0]^^f *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow (XHALT_loop12 w 0 f k). finish_norm.
Qed.

Lemma XHALT_st13 : forall f k w, (0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{B}} (0 >> 1 >> 0 >> [1;0]^^f *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0) -->* (0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{J}} (0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^f *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. do 28 step. finish_norm.
Qed.

Lemma EV_HALT : forall f k w, (1 >> [0;1]^^f *> 1 >> [1;0;1]^^w *> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) {{H}}> (const 0) -->* (0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{J}} (0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^f *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0).
Proof.
  intros. follow XHALT_st1. follow XHALT_loop4_z. follow XHALT_st5. follow XHALT_loop12_z.
  follow XHALT_st13.
  finish_norm.
Qed.

Lemma EV_HALT_halted : forall f k w, halted tm ((0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0) <{{J}} (0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^f *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0)).
Proof. intros. reflexivity. Qed.

(** ** Abstract part (hand-written: bb10_n1_coq/abstract.v.in) *)

(** *** Token lists *)

(** [lfr ts L]: tokens D(d) = (10)^d 1, nearest-first, then the side L. *)
Local Open Scope nat_scope.

Fixpoint lfr (ts : list nat) (L : side) : side :=
  match ts with
  | [] => L
  | d :: t => (1 >> [0;1]^^d *> lfr t L)%sym
  end.

(** B-form [L | A]: far side L, then D(t_1) .. D(t_n) D(0) D(A), head in H on the blank right of it
    (ts is nearest-first: ts = [t_n; ..; t_1]). *)
Definition Bf (L : side) (ts : list nat) (A : nat) : Q * tape := (lfr (A :: 0 :: ts) L) {{H}}> const 0%sym.

Notation Bf0 := (Bf (const 0%sym)).

Lemma lfr_app : forall xs ys L, lfr (xs ++ ys) L = lfr xs (lfr ys L).
Proof. induction xs; intros; simpl; [reflexivity | rewrite IHxs; reflexivity]. Qed.

Lemma lfr_ones : forall n t L, lfr (repeat 1 n ++ t) L = ([1;0;1]^^n *> lfr t L)%sym.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma lfr_twos : forall n t L, lfr (repeat 2 n ++ t) L = ([1;0;1;0;1]^^n *> lfr t L)%sym.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma lfr_ones_nil : forall n L, lfr (repeat 1 n) L = ([1;0;1]^^n *> L)%sym.
Proof. intros. rewrite <- (app_nil_r (repeat 1 n)), lfr_ones. reflexivity. Qed.

Lemma lfr_twos_nil : forall n L, lfr (repeat 2 n) L = ([1;0;1;0;1]^^n *> L)%sym.
Proof. intros. rewrite <- (app_nil_r (repeat 2 n)), lfr_twos. reflexivity. Qed.

Lemma pow_add : forall (xs : list Sym) n m Y, xs^^(n + m) *> Y = xs^^n *> xs^^m *> Y.
Proof. intros. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

Lemma pow_mul : forall (xs : list Sym) k n Y, xs^^(k * n) *> Y = (xs^^k)^^n *> Y.
Proof.
  induction n; intros.
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite Nat.mul_succ_r, Nat.add_comm, pow_add, IHn.
    change ((xs^^k)^^(S n)) with (xs^^k ++ (xs^^k)^^n). rewrite Str_app_assoc. reflexivity.
Qed.

(** a token 1 + 3 p as the explorer writes it *)
Lemma tok3 : forall c p Y, ([0;1]^^(c + 3 * p) *> Y = [0;1]^^c *> [0;1;0;1;0;1]^^p *> Y)%sym.
Proof. intros. rewrite pow_add, pow_mul. reflexivity. Qed.

Lemma ones2 : forall q Y, ([1;0;1]^^(2 * q) *> Y = [1;0;1]^^q *> [1;0;1]^^q *> Y)%sym.
Proof. intros. replace (2 * q) with (q + q) by lia. apply pow_add. Qed.

Lemma repeat_snoc : forall (x : nat) n t, repeat x n ++ x :: t = repeat x (S n) ++ t.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma repeat_add : forall (x : nat) n m t, repeat x (n + m) ++ t = repeat x n ++ repeat x m ++ t.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Ltac bnorm := unfold Bf; repeat progress (cbn [lfr]; rewrite ?lfr_app, ?lfr_ones, ?lfr_twos, ?lfr_ones_nil, ?lfr_twos_nil).

(** *** Champion rules on raw tokens *)

(** D(j) D(c) -> D(j + 2c) D(0): c passes of the doubling round [PASS] *)
Lemma PASSES : forall c j l,
  (1 >> [0;1]^^j *> 1 >> [0;1]^^c *> l)%sym {{H}}> const 0%sym -->* (1 >> [0;1]^^(j + 2 * c) *> 1 >> l)%sym {{H}}> const 0%sym.
Proof.
  induction c; intros.
  - rewrite Nat.mul_0_r, Nat.add_0_r. apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, (PASS c j l) |].
    replace (j + 2 * S c) with (S (S j) + 2 * c) by lia.
    apply (IHc (S (S j)) l).
Qed.

Lemma R1 : forall L t ts A, Bf L ((3 + t) :: ts) A -->* Bf L (t :: ts) (2 * A + 8).
Proof.
  intros. unfold Bf. cbn [lfr].
  eapply evstep_trans; [apply progress_evstep, (PRO A t (lfr ts L)) |].
  replace (2 * A + 8) with (2 + 2 * (3 + A)) by lia.
  apply (PASSES (3 + A) 2 (1 >> [0;1]^^t *> lfr ts L)%sym).
Qed.

Lemma R2 : forall L k t ts A,
  Bf L (repeat 1 (S k) ++ (3 + t) :: ts) A -->* Bf L (repeat 1 k ++ (3 + A) :: t :: ts) 4.
Proof.
  intros. unfold Bf. cbn [lfr]. rewrite !lfr_ones. cbn [lfr].
  apply progress_evstep. apply (R2M A k t (lfr ts L)).
Qed.

(** *** Clearing *)

Fixpoint iter (n : nat) (g : nat -> nat) (x : nat) : nat :=
  match n with
  | O => x
  | S n' => g (iter n' g x)
  end.

Lemma iter_S' : forall n g x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

(** U j A: the accumulator after clearing one unit of a token at depth j (j ones to its right), from A.
    A token 3 + A deposited by R2 has S (A / 3) units when A = 1 mod 3. *)
Fixpoint U (j : nat) : nat -> nat :=
  match j with
  | O => fun A => 2 * A + 8
  | S i => fun A => iter (S (A / 3)) (U i) 4
  end.

Lemma U_0 : forall A, U O A = 2 * A + 8.
Proof. reflexivity. Qed.

Lemma U_S : forall j A, U (S j) A = iter (S (A / 3)) (U j) 4.
Proof. reflexivity. Qed.

Opaque U.

Definition r1 (A : nat) : Prop := exists a, A = 3 * a + 1.

Lemma div3 : forall a, (3 * a + 1) / 3 = a.
Proof. intros. symmetry. apply (Nat.div_unique (3 * a + 1) 3 a 1); lia. Qed.

Lemma r1_U0 : forall A, r1 A -> r1 (U O A).
Proof. intros A [a ->]. rewrite U_0. exists (2 * a + 3). lia. Qed.

Lemma r1_iter : forall g, (forall y, r1 y -> r1 (g y)) -> forall n x, r1 x -> r1 (iter n g x).
Proof. intros g Hg. induction n; intros; simpl; [assumption | apply Hg, IHn; assumption]. Qed.

Lemma r1_U : forall j A, r1 A -> r1 (U j A).
Proof.
  induction j; intros.
  - apply r1_U0. assumption.
  - rewrite U_S. apply r1_iter; [exact IHj | exists 1; reflexivity].
Qed.

Lemma r1_US : forall j A, r1 (U (S j) A).
Proof. intros. rewrite U_S. apply r1_iter; [apply r1_U | exists 1; reflexivity]. Qed.

Lemma r1_4 : r1 4.
Proof. exists 1. reflexivity. Qed.

Lemma CLR : forall n d c ts L A, (n = 0 \/ r1 A) ->
  Bf L (repeat 1 n ++ (c + 3 * d) :: ts) A -->* Bf L (repeat 1 n ++ c :: ts) (iter d (U n) A).
Proof.
  induction n as [| n IHn]; intros d c ts L A HA.
  - cbn [repeat app]. clear HA. revert A. induction d as [| d IHd]; intros A.
    + rewrite Nat.mul_0_r, Nat.add_0_r. apply evstep_refl.
    + replace (c + 3 * S d) with (3 + (c + 3 * d)) by lia.
      follow (R1 L (c + 3 * d) ts A).
      rewrite iter_S', <- U_0. apply IHd.
  - destruct HA as [HA | HA]; [discriminate |].
    revert A HA. induction d as [| d IHd]; intros A HA.
    + rewrite Nat.mul_0_r, Nat.add_0_r. apply evstep_refl.
    + replace (c + 3 * S d) with (3 + (c + 3 * d)) by lia.
      follow (R2 L n (c + 3 * d) ts A).
      destruct HA as [a Ha].
      replace (3 + A) with (1 + 3 * S (A / 3)) by (subst A; rewrite div3; lia).
      follow (IHn (S (A / 3)) 1 ((c + 3 * d) :: ts) L 4 (or_intror r1_4)).
      rewrite repeat_snoc, <- U_S, iter_S'.
      apply IHd. apply r1_US.
Qed.

(** *** The special events, on B-forms (wrappers of the generated EV_* lemmas) *)

(** the far region left by P2: 0 0 D0 D0 D0 D1^m D5 D2^(k+2) *)
Definition FarP (k m : nat) : side := (0 >> 0 >> lfr (0 :: 0 :: 0 :: repeat 1 m ++ 5 :: repeat 2 (2 + k))%nat (const 0))%sym.

(** the far region left by the final P2 (E) *)
Definition FarE (k : nat) : side := (
  0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> 0 >>
  0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >>
  [1;0;1;0;1]^^k *> const 0)%sym.

(** H: list exhaustion [1^(n+1) | a] -> [2, 1^(2a+4), 0, 1^n | 6] *)
Lemma H_B : forall n a, Bf0 (repeat 1 (S n)) a -->* Bf0 (repeat 1 n ++ 0 :: repeat 1 4 ++ repeat 1 (2 * a) ++ [2]) 6.
Proof. intros. bnorm. follow (EV_H a n). rewrite (pow_mul [1;0;1]%sym 2 a). finish_norm. Qed.

(** S0: [2, 1^(M+5), 0, 1^(n+2) | a] -> [2, 5, 1^M, 0, 0, 0, a+3, 1^n | 4] *)
Lemma S0_B : forall M n a, Bf0 (repeat 1 (2 + n) ++ 0 :: repeat 1 (5 + M) ++ [2]) a -->*
  Bf0 (repeat 1 n ++ (3 + a) :: 0 :: 0 :: 0 :: repeat 1 M ++ [5; 2]) 4.
Proof. intros. bnorm. follow (EV_S0 M a n). finish_norm. Qed.

(** P1: [2^k, 5, 1^(m+6), 0, 0, 2, 1^n | a] -> [2^(k+2), 5, 1^m, 0, 0, 0, 1, a+3, 1^n | 6] *)
Lemma P1_B : forall k m n a,
  Bf0 (repeat 1 n ++ 2 :: 0 :: 0 :: repeat 1 (6 + m) ++ 5 :: repeat 2 k) a -->*
  Bf0 (repeat 1 n ++ (3 + a) :: 1 :: 0 :: 0 :: 0 :: repeat 1 m ++ 5 :: repeat 2 (2 + k)) 6.
Proof. intros. bnorm. follow (EV_P1 a k m n). finish_norm. Qed.

(** P2: [2^k, 5, 1^(m+6), 0, 0, 0, 1, 1+3p, 0, 1^(w+1) | r+1] -> FarP k m + [2, r+2, 1^(w+2p+2) | 4] *)
Lemma P2_B : forall k m p r w,
  Bf0 (repeat 1 (1 + w) ++ 0 :: (1 + 3 * p) :: 1 :: 0 :: 0 :: 0 :: repeat 1 (6 + m) ++ 5 :: repeat 2 k) (1 + r) -->*
  Bf (FarP k m) (repeat 1 2 ++ repeat 1 w ++ repeat 1 (2 * p) ++ [2 + r; 2]) 4.
Proof.
  intros. unfold FarP. bnorm. rewrite (tok3 1 p).
  follow (EV_P2 k m p r w). rewrite (pow_mul [1;0;1]%sym 2 p). finish_norm.
Qed.

(** P3: FarP k m + [2, 2, 1^w | a] -> [2^(k+2), 5, 1^m, 0, 0, a+5, 1^w | 6] *)
Lemma P3_B : forall k m w a, Bf (FarP k m) (repeat 1 w ++ [2; 2]) a -->*
  Bf0 (repeat 1 w ++ (5 + a) :: 0 :: 0 :: repeat 1 m ++ 5 :: repeat 2 (2 + k)) 6.
Proof. intros. unfold FarP. bnorm. follow (EV_P3 a (2 + k) m w). finish_norm. Qed.

(** P4: [2^k, 5, 1^(m+2), 0, 0, 3q, 0, 1^(w+1) | r+1] -> [2^k, 5, 1^m, 0, 0, r+2, 1^(w+2q+2) | 4] *)
Lemma P4_B : forall k m q r w,
  Bf0 (repeat 1 (1 + w) ++ 0 :: (3 * q) :: 0 :: 0 :: repeat 1 (2 + m) ++ 5 :: repeat 2 k) (1 + r) -->*
  Bf0 (repeat 1 2 ++ repeat 1 w ++ repeat 1 (2 * q) ++ (2 + r) :: 0 :: 0 :: repeat 1 m ++ 5 :: repeat 2 k) 4.
Proof.
  intros. bnorm. rewrite (pow_mul [0;1]%sym 3 q).
  follow (EV_P4 k m q r w). rewrite (pow_mul [1;0;1]%sym 2 q). finish_norm.
Qed.

(** E (the final P2, m = 1): [2^(k+6), 5, 1, 0, 0, 0, 1, 1+3p, 0, 1^(w+1) | r+1] -> FarE k + [r+3, 1^(w+2p+2) | 4] *)
Lemma E_B : forall k p r w,
  Bf0 (repeat 1 (1 + w) ++ 0 :: (1 + 3 * p) :: 1 :: 0 :: 0 :: 0 :: 1 :: 5 :: repeat 2 (6 + k)) (1 + r) -->*
  Bf (FarE k) (repeat 1 2 ++ repeat 1 w ++ repeat 1 (2 * p) ++ [3 + r]) 4.
Proof.
  intros. unfold FarE. bnorm. rewrite (tok3 1 p).
  follow (EV_E k p r w). rewrite (pow_mul [1;0;1]%sym 2 p). finish_norm.
Qed.

(** the halt: FarE k + [0, 1^w | f] -> J reading 0 *)
Lemma HALT_B : forall k w f, exists c, Bf (FarE k) (repeat 1 w ++ [0]) f -->* c /\ halted tm c.
Proof.
  intros. eexists. split.
  - unfold FarE. bnorm. follow (EV_HALT f k w). finish_norm.
  - apply EV_HALT_halted.
Qed.

(** *** Arithmetic: closed form of U, sizes, and the residue of 2 ^(37 arrows) 3 mod 7 *)

(** Knuth's up-arrows (as in BB8_champ35_bound.v): arrow 0 a b = a * b, arrow (S k) a b = (arrow k a)^b (1). *)
Fixpoint arrow (k a b : nat) : nat :=
  match k with
  | O => a * b
  | S k' => Nat.iter b (arrow k' a) 1%nat
  end.

Lemma arrow_0 : forall a b, arrow 0 a b = a * b.
Proof. reflexivity. Qed.

Lemma arrow_SS : forall k a b, arrow (S k) a (S b) = arrow k a (arrow (S k) a b).
Proof. reflexivity. Qed.

Lemma arrow_S0 : forall k a, arrow (S k) a 0 = 1.
Proof. reflexivity. Qed.

Lemma arrow_S_iter : forall k a b, arrow (S k) a b = iter b (arrow k a) 1.
Proof. induction b. - reflexivity. - rewrite arrow_SS, IHb. reflexivity. Qed.

Lemma arrow_1_pow : forall a b, arrow 1 a b = a ^ b.
Proof. induction b; [reflexivity |]. rewrite arrow_SS, IHb. simpl. lia. Qed.

Lemma arrow_one : forall k, arrow k 2 1 = 2.
Proof. induction k. - reflexivity. - rewrite (arrow_SS k 2 0), arrow_S0. exact IHk. Qed.

Lemma arrow_two : forall k, arrow k 2 2 = 4.
Proof. induction k. - reflexivity. - rewrite (arrow_SS k 2 1), arrow_one. exact IHk. Qed.

Opaque arrow.

Lemma iter_add : forall a b g x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

Lemma iter_ge : forall g, (forall a, a <= g a) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_mono_n : forall g, (forall a, a <= g a) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite iter_add. apply iter_ge. exact Hg.
Qed.

Lemma iter_lin1 : forall g, (forall a, 1 <= a -> a + 1 <= g a) -> forall n x, 1 <= x -> x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros x Hx; simpl. - lia.
  - specialize (IHn x Hx). specialize (Hg (iter n g x) ltac:(lia)). lia.
Qed.

Lemma arrow_props : forall k,
  (forall x y, x <= y -> arrow k 2 x <= arrow k 2 y) /\ (forall x, 1 <= x -> x + 1 <= arrow k 2 x) /\
  (forall x, x <= arrow k 2 x).
Proof.
  induction k as [| k [Hm [Hs Hi]]].
  - Transparent arrow. split; [intros; simpl; lia | split; intros; simpl; lia]. Opaque arrow.
  - assert (Hm' : forall x y, x <= y -> arrow (S k) 2 x <= arrow (S k) 2 y).
    { intros x y Hxy. rewrite !arrow_S_iter. apply iter_mono_n; assumption. }
    assert (Hs' : forall x, 1 <= x -> x + 1 <= arrow (S k) 2 x).
    { intros x Hx. rewrite arrow_S_iter.
      destruct x as [| x']; [lia |].
      simpl iter. pose proof (Hs (iter x' (arrow k 2) 1)).
      pose proof (iter_lin1 (arrow k 2) Hs x' 1 ltac:(lia)). lia. }
    split; [exact Hm' | split; [exact Hs' |]].
    intros x. destruct x as [| x']; [lia |]. pose proof (Hs' (S x') ltac:(lia)). lia.
Qed.

Lemma arrow_mono : forall k x y, x <= y -> arrow k 2 x <= arrow k 2 y.
Proof. intros. apply arrow_props. assumption. Qed.

Lemma arrow_gt : forall k x, 1 <= x -> x + 1 <= arrow k 2 x.
Proof. intros. apply arrow_props. assumption. Qed.

Lemma arrow_ge4 : forall k x, 2 <= x -> 4 <= arrow k 2 x.
Proof. intros. rewrite <- (arrow_two k). apply arrow_mono. assumption. Qed.

(** U j (3 a + 1) + 8 = 3 * (2 ^(j arrows) (a + 3)) *)
Lemma U_closed : forall j a, U j (3 * a + 1) + 8 = 3 * arrow j 2 (a + 3).
Proof.
  induction j as [| i IH]; intros a.
  - rewrite U_0, (arrow_0 2 (a + 3)). lia.
  - assert (Hit : forall c, iter c (U i) 4 + 8 = 3 * arrow (S i) 2 (c + 2)).
    { induction c as [| c IHc].
      - simpl iter. rewrite arrow_two. reflexivity.
      - simpl iter. replace (S c + 2) with (S (c + 2)) by lia. rewrite arrow_SS.
        pose proof (arrow_ge4 (S i) (c + 2) ltac:(lia)) as H4.
        revert IHc H4. generalize (arrow (S i) 2 (c + 2)). intros X IHc H4.
        replace (iter c (U i) 4) with (3 * (X - 3) + 1) by lia.
        rewrite IH. replace (X - 3 + 3) with X by lia. reflexivity. }
    rewrite U_S, div3, Hit. replace (S a + 2) with (a + 3) by lia. reflexivity.
Qed.

Lemma r1_dec : forall y, r1 y -> y = 3 * (y / 3) + 1.
Proof. intros y [a ->]. rewrite div3. reflexivity. Qed.

Lemma U_gt : forall j y, r1 y -> y < U j y.
Proof.
  intros j y Hy. rewrite (r1_dec y Hy). generalize (y / 3). intros a.
  pose proof (U_closed j a). pose proof (arrow_gt j (a + 3) ltac:(lia)). lia.
Qed.

Lemma U_mono : forall j y z, r1 y -> r1 z -> y <= z -> U j y <= U j z.
Proof.
  intros j y z Hy Hz Hyz. rewrite (r1_dec y Hy), (r1_dec z Hz).
  assert (y / 3 <= z / 3) by (apply Nat.div_le_mono; lia).
  revert H. generalize (y / 3) (z / 3). intros a b Hab.
  pose proof (U_closed j a). pose proof (U_closed j b).
  pose proof (arrow_mono j (a + 3) (b + 3) ltac:(lia)). lia.
Qed.

Lemma iter_U_ge : forall j d y, r1 y -> 1 <= d -> U j y <= iter d (U j) y.
Proof.
  intros j d y Hy Hd. destruct d as [| d]; [lia |]. clear Hd.
  rewrite iter_S'. induction d as [| d IH]; simpl iter; [lia |].
  pose proof (U_gt j (iter d (U j) (U j y)) (r1_iter _ (r1_U j) d _ (r1_U j y Hy))). lia.
Qed.

(** the growth function: F n = 2 ^(n arrows) 4 = 2 ^(n+1 arrows) 3 *)
Definition F (n : nat) : nat := arrow n 2 4.

Lemma U4 : forall n, U n 4 + 8 = 3 * F n.
Proof. intros. unfold F. exact (U_closed n 1). Qed.

Lemma arrow_S3 : forall n, arrow (S n) 2 3 = F n.
Proof. intros. unfold F. rewrite (arrow_SS n 2 2), (arrow_two (S n)). reflexivity. Qed.

Lemma F_S : forall n, F (S n) = arrow n 2 (F n).
Proof. intros. unfold F at 1. rewrite (arrow_SS n 2 3), arrow_S3. reflexivity. Qed.

Lemma F_0 : F 0 = 8.
Proof. unfold F. rewrite (arrow_0 2 4). reflexivity. Qed.

Lemma F_step : forall n, F n + 1 <= F (S n).
Proof.
  intros. rewrite F_S. apply arrow_gt.
  induction n; [rewrite F_0; lia |]. rewrite F_S. pose proof (arrow_gt n (F n) IHn). lia.
Qed.

Lemma F_ge : forall n, n + 8 <= F n.
Proof. induction n; [rewrite F_0; lia |]. pose proof (F_step n). lia. Qed.

Lemma F_mono : forall x y, x <= y -> F x <= F y.
Proof. intros x y Hxy. induction Hxy; [lia |]. pose proof (F_step m). lia. Qed.

Lemma iterF_mono : forall j x y, x <= y -> iter j F x <= iter j F y.
Proof. induction j; intros; simpl; [assumption | apply F_mono, IHj; assumption]. Qed.

Lemma iterF_ge : forall j x, x <= iter j F x.
Proof. induction j; intros; simpl; [lia | pose proof (F_ge (iter j F x)); pose proof (IHj x); lia]. Qed.

(** *** 2 ^(37 arrows) 3 = 2 mod 7 *)

Lemma tower : forall k, 2 <= k -> forall n, exists m, n <= m /\ arrow k 2 n = arrow 2 2 m.
Proof.
  intros k Hk. induction k as [| k IH]; [lia |].
  destruct (Nat.eq_dec k 1) as [-> | Hk1].
  - intros n. exists n. split; reflexivity.
  - assert (Hk2 : 2 <= k) by lia. specialize (IH Hk2).
    intros n. destruct n as [| n].
    + exists 0. split; [lia |]. rewrite !arrow_S0. reflexivity.
    + rewrite arrow_SS. destruct (IH (arrow (S k) 2 n)) as [m [Hm Heq]].
      exists m. split; [| exact Heq].
      destruct n as [| n'].
      * rewrite arrow_S0 in Hm. lia.
      * pose proof (arrow_gt (S k) (S n') ltac:(lia)). lia.
Qed.

Lemma arrow2_S : forall m, arrow 2 2 (S m) = 2 ^ (arrow 2 2 m).
Proof. intros. rewrite arrow_SS, arrow_1_pow. reflexivity. Qed.

Lemma arrow2_pos : forall m, 1 <= arrow 2 2 m.
Proof. destruct m. - rewrite arrow_S0. lia. - pose proof (arrow_gt 2 (S m) ltac:(lia)). lia. Qed.

Lemma pow_mod_nat : forall a b n, n <> 0 -> a ^ b mod n = (a mod n) ^ b mod n.
Proof.
  intros a b n Hn. induction b as [| b IH].
  - reflexivity.
  - simpl. rewrite (Nat.mul_mod a (a ^ b)) by exact Hn. rewrite IH.
    rewrite (Nat.mul_mod (a mod n) ((a mod n) ^ b)) by exact Hn. rewrite (Nat.mod_mod a n Hn). reflexivity.
Qed.

(** 2 ^ (2 ^ (2 ^ y)) = 2 mod 7 for y >= 1 *)
Lemma tower_mod7 : forall y, 1 <= y -> 2 ^ (2 ^ (2 ^ y)) mod 7 = 2.
Proof.
  intros y Hy.
  assert (He : exists s, 2 ^ y = 2 * s).
  { exists (2 ^ (y - 1)). replace y with (S (y - 1)) at 1 by lia. rewrite Nat.pow_succ_r'. reflexivity. }
  destruct He as [s Hs]. rewrite Hs.
  assert (H3 : 2 ^ (2 * s) mod 3 = 1).
  { rewrite Nat.pow_mul_r. change (2 ^ 2) with 4. rewrite pow_mod_nat by lia.
    change (4 mod 3) with 1. rewrite Nat.pow_1_l. reflexivity. }
  revert H3. generalize (2 ^ (2 * s)). intros e H3.
  assert (Ht : e = 3 * (e / 3) + 1) by (pose proof (Nat.div_mod_eq e 3); lia).
  rewrite Ht. rewrite Nat.pow_add_r, Nat.pow_mul_r. change (2 ^ 3) with 8. change (2 ^ 1) with 2.
  rewrite Nat.mul_mod, pow_mod_nat by lia. change (8 mod 7) with 1. rewrite Nat.pow_1_l. reflexivity.
Qed.

Lemma arrow37_mod7 : arrow 37 2 3 mod 7 = 2.
Proof.
  rewrite (arrow_SS 36 2 2), (arrow_two 37).
  destruct (tower 36 ltac:(lia) 4) as [m [Hm ->]].
  replace m with (S (S (S (m - 3)))) by lia.
  rewrite !arrow2_S. apply tower_mod7. apply arrow2_pos.
Qed.

Lemma arrow_37_3 : arrow 37 2 3 = arrow 35 2 (arrow 35 2 4).
Proof.
  transitivity (arrow 36 2 (arrow 37 2 2)); [exact (arrow_SS 36 2 2) |].
  rewrite (arrow_two 37).
  transitivity (arrow 35 2 (arrow 36 2 3)); [exact (arrow_SS 35 2 3) |].
  rewrite (arrow_SS 35 2 2), (arrow_two 36).
  reflexivity.
Qed.

(** The BB(8)-record-size constant T = 2 ^(37 arrows) 3, sealed (lia must never see it unfolded). *)
Lemma T_sig : {t : nat | t = arrow 37 2 3}.
Proof. exists (arrow 37 2 3). reflexivity. Qed.

Definition T : nat := proj1_sig T_sig.

Lemma T_def : T = arrow 37 2 3.
Proof. exact (proj2_sig T_sig). Qed.

Lemma T_mod7 : exists s, T = 7 * s + 2.
Proof.
  pose proof arrow37_mod7 as H. rewrite <- T_def in H. revert H. generalize T. intros t H.
  exists (t / 7). pose proof (Nat.div_mod_eq t 7). lia.
Qed.

Lemma T_ge : 44 <= T.
Proof.
  rewrite T_def, arrow_S3. pose proof (F_ge 36). revert H. generalize (F 36). intros. lia.
Qed.

Lemma U2_closed : forall j c, U j (U j (3 * c + 1)) + 8 = 3 * arrow j 2 (arrow j 2 (c + 3)).
Proof.
  intros j c. pose proof (U_closed j c) as H1. pose proof (arrow_ge4 j (c + 3) ltac:(lia)) as H4.
  revert H1 H4. generalize (arrow j 2 (c + 3)). intros X H1 H4.
  replace (U j (3 * c + 1)) with (3 * (X - 3) + 1) by lia.
  rewrite U_closed. replace (X - 3 + 3) with X by lia. reflexivity.
Qed.

(** the accumulator at the first exhaustion: iter 2 (U 35) 4 = 3 T - 8 *)
Lemma Af_closed : iter 2 (U 35) 4 + 8 = 3 * T.
Proof.
  rewrite T_def, arrow_37_3. change (iter 2 (U 35) 4) with (U 35 (U 35 (3 * 1 + 1))).
  exact (U2_closed 35 1).
Qed.

(** *** The period: [2^k, 5, 1^(m+14), 0, 0, 2, 1^n | a] -->* [2^(k+4), 5, 1^m, 0, 0, 2, 1^n' | a'] *)

Definition Per (k m n a : nat) : Q * tape := Bf0 (repeat 1 n ++ 2 :: 0 :: 0 :: repeat 1 m ++ 5 :: repeat 2 k) a.

(** the accumulator invariant: a = 1 mod 3, and a is at least one unit cleared at the current depth n *)
Definition Inv (n a : nat) : Prop := 3 <= n /\ r1 a /\ U n 4 <= a.

Lemma merge3 : forall x y z t, repeat 1 x ++ repeat 1 y ++ repeat 1 z ++ t = repeat 1 (x + y + z) ++ t.
Proof. intros. rewrite !repeat_add. reflexivity. Qed.

Lemma r1_split : forall R, r1 R -> exists x, R = 1 + 3 * x.
Proof. intros R [x ->]. exists x. lia. Qed.

Lemma r1_ge : forall j d, 1 <= d -> exists x, iter d (U j) 4 = 1 + 3 * x /\ 1 <= x /\ U j 4 <= iter d (U j) 4.
Proof.
  intros j d Hd.
  destruct (r1_split _ (r1_iter _ (r1_U j) d 4 r1_4)) as [x Hx].
  pose proof (iter_U_ge j d 4 r1_4 Hd). pose proof (U_gt j 4 r1_4).
  exists x. split; [exact Hx |]. split; lia.
Qed.

(** the growth of a P2 / P4 event: 2 p >= F n - 3 when 3 p + 1 >= U n 4 *)
Lemma growth : forall n p, U n 4 <= 1 + 3 * p -> F n <= 2 * p + 3.
Proof. intros n p H. pose proof (U4 n). revert H H0. generalize (U n 4) (F n). intros. lia. Qed.

(** R2 followed by CLR(9): the accumulator 6 is deposited as a token 9 and cleared to D0 at depth d *)
Lemma DEP9 : forall L d t ts, Bf L (repeat 1 (S d) ++ (3 + t) :: ts) 6 -->* Bf L (repeat 1 d ++ 0 :: t :: ts) (iter 3 (U d) 4).
Proof.
  intros. follow (R2 L d t ts 6).
  replace (3 + 6) with (0 + 3 * 3) by lia.
  apply (CLR d 3 0 _ L 4 (or_intror r1_4)).
Qed.

Lemma PERIOD : forall k m n a, Inv n a ->
  exists n' a', Per k (14 + m) n a -->* Per (4 + k) m n' a' /\ Inv n' a' /\ F (F n) <= n'.
Proof.
  intros k m n a [Hn [Ha Hb]].
  destruct (r1_split a Ha) as [p Hp].
  destruct n as [| n1]; [lia |]. destruct n1 as [| w]; [lia |].
  destruct (r1_ge (S w) 3 ltac:(lia)) as [x [Hx [Hx1 _]]].
  destruct (r1_ge (2 + w + 2 * p) x Hx1) as [y [Hy [_ HA2]]].
  destruct (r1_ge (1 + w + 2 * p) 3 ltac:(lia)) as [x' [Hx' [Hx1' _]]].
  destruct (r1_ge (2 + (w + 2 * p) + 2 * S y) x' Hx1') as [z [Hz [_ HA4]]].
  exists (2 + (w + 2 * p) + 2 * S y), (iter x' (U (2 + (w + 2 * p) + 2 * S y)) 4).
  split; [| split].
  - unfold Per.
    (* P1 *)
    replace (14 + m) with (6 + (8 + m)) by lia.
    follow (P1_B k (8 + m) (S (S w)) a).
    (* R2 + CLR(9) at depth S w *)
    follow (DEP9 (const 0%sym) (S w) a (1 :: 0 :: 0 :: 0 :: repeat 1 (8 + m) ++ 5 :: repeat 2 (2 + k))).
    (* P2 *)
    rewrite Hx, Hp. replace (8 + m) with (6 + (2 + m)) by lia. replace (3 * p + 1) with (1 + 3 * p) by lia.
    follow (P2_B (2 + k) (2 + m) p (3 * x) w). rewrite merge3.
    (* CLR(R+1) at depth 2 + w + 2p *)
    replace (2 + 3 * x) with (2 + 3 * x) by reflexivity.
    follow (CLR (2 + w + 2 * p) x 2 [2] (FarP (2 + k) (2 + m)) 4 (or_intror r1_4)).
    (* P3 *)
    follow (P3_B (2 + k) (2 + m) (2 + w + 2 * p) (iter x (U (2 + w + 2 * p)) 4)).
    rewrite Hy. replace (5 + (1 + 3 * y)) with (3 + (3 + 3 * y)) by lia. replace (2 + (2 + k)) with (4 + k) by lia.
    (* R2 + CLR(9) at depth 1 + w + 2p *)
    follow (DEP9 (const 0%sym) (1 + w + 2 * p) (3 + 3 * y) (0 :: 0 :: repeat 1 (2 + m) ++ 5 :: repeat 2 (4 + k))).
    (* P4 *)
    rewrite Hx'. replace (3 + 3 * y) with (3 * S y) by lia.
    replace (1 + w + 2 * p) with (1 + (w + 2 * p)) by lia.
    follow (P4_B (4 + k) m (S y) (3 * x') (w + 2 * p)). rewrite merge3.
    (* CLR(R'+1) *)
    apply (CLR (2 + (w + 2 * p) + 2 * S y) x' 2 _ (const 0%sym) 4 (or_intror r1_4)).
  - split; [lia | split; [exists z; lia | exact HA4]].
  - rewrite Hp in Hb. pose proof (growth (S (S w)) p ltac:(lia)) as G1.
    rewrite Hy in HA2. pose proof (growth (2 + w + 2 * p) y ltac:(lia)) as G2.
    assert (G3 : F (S (S w)) <= 2 + w + 2 * p) by lia.
    pose proof (F_mono _ _ G3). lia.
Qed.

Lemma PERIODS : forall J k n a, Inv n a ->
  exists n' a', Per k (14 * J + 7) n a -->* Per (4 * J + k) 7 n' a' /\ Inv n' a' /\ iter (2 * J) F n <= n'.
Proof.
  induction J as [| J IH]; intros k n a Hinv.
  - exists n, a. split; [apply evstep_refl | split; [exact Hinv | simpl; lia]].
  - destruct (PERIOD k (14 * J + 7) n a Hinv) as [n1 [a1 [H1 [Hinv1 Hg1]]]].
    destruct (IH (4 + k) n1 a1 Hinv1) as [n2 [a2 [H2 [Hinv2 Hg2]]]].
    exists n2, a2. split; [| split; [exact Hinv2 |]].
    + replace (14 * S J + 7) with (14 + (14 * J + 7)) by lia.
      replace (4 * S J + k) with (4 * J + (4 + k)) by lia.
      follow H1. exact H2.
    + replace (2 * S J) with (2 * J + 2) by lia. rewrite iter_add.
      pose proof (iterF_mono (2 * J) _ _ Hg1). change (iter 2 F n) with (F (F n)). lia.
Qed.

(** *** The end: the last P1, R2 + CLR(9), E (the final P2), CLR(R+2) to D0 *)

Lemma ENDGAME : forall k n a, Inv n a ->
  exists w f, Per (4 + k) 7 n a -->* Bf (FarE k) (repeat 1 w ++ [0]) f /\ F n <= w.
Proof.
  intros k n a [Hn [Ha Hb]].
  destruct (r1_split a Ha) as [p Hp].
  destruct n as [| n1]; [lia |]. destruct n1 as [| w]; [lia |].
  destruct (r1_ge (S w) 3 ltac:(lia)) as [x [Hx [Hx1 _]]].
  exists (2 + w + 2 * p), (iter (S x) (U (2 + w + 2 * p)) 4). split.
  - unfold Per.
    follow (P1_B (4 + k) 1 (S (S w)) a).
    follow (DEP9 (const 0%sym) (S w) a (1 :: 0 :: 0 :: 0 :: repeat 1 1 ++ 5 :: repeat 2 (2 + (4 + k)))).
    rewrite Hx, Hp. replace (3 * p + 1) with (1 + 3 * p) by lia. replace (2 + (4 + k)) with (6 + k) by lia.
    follow (E_B k p (3 * x) w). rewrite merge3.
    replace (3 + 3 * x) with (0 + 3 * S x) by lia.
    rewrite <- (app_nil_r (repeat 1 (2 + w + 2 * p) ++ [0])), <- app_assoc.
    apply (CLR (2 + w + 2 * p) (S x) 0 [] (FarE k) 4 (or_intror r1_4)).
  - rewrite Hp in Hb. pose proof (growth (S (S w)) p ltac:(lia)). lia.
Qed.

(** *** The run from the blank tape *)

Lemma init_reach : c0 -->* Bf0 (repeat 1 35 ++ [7]) 4.
Proof.
  unfold c0, Bf. cbn [lfr].
  do 6447 step.
  apply evstep_refl'. reflexivity.
Qed.

(** the accumulator at the first exhaustion, sealed *)
Lemma Af_sig : {x : nat | x = iter 2 (U 35) 4}.
Proof. exists (iter 2 (U 35) 4). reflexivity. Qed.

Definition Af : nat := proj1_sig Af_sig.

Lemma Af_def : Af = iter 2 (U 35) 4.
Proof. exact (proj2_sig Af_sig). Qed.

(** stage 0: the record's first exhaustion, H, S0, CLR(9) at depth 33, P4 (Q = 0), CLR: the first period start *)
Lemma reach_per : exists a, c0 -->* Per 1 (6 * T - 19) 34 a /\ Inv 34 a.
Proof.
  pose proof Af_closed as HAf. pose proof T_ge as HT. rewrite <- Af_def in HAf.
  destruct (r1_ge 33 3 ltac:(lia)) as [x0 [Hx0 [Hx01 _]]].
  destruct (r1_ge 34 x0 Hx01) as [z [Hz [_ HA1]]].
  exists (iter x0 (U 34) 4). split; [| split; [lia | split; [exists z; lia | exact HA1]]].
  follow init_reach.
  follow (CLR 35 2 1 [] (const 0%sym) 4 (or_intror r1_4)). rewrite <- Af_def.
  rewrite repeat_snoc, app_nil_r.
  follow (H_B 35 Af).
  (* S0 with M = 2 Af - 1 *)
  replace (repeat 1 4 ++ repeat 1 (2 * Af) ++ [2]) with (repeat 1 (5 + (6 * T - 17)) ++ [2])
    by (rewrite <- repeat_add; f_equal; f_equal; revert HAf HT; generalize Af T; intros; lia).
  follow (S0_B (6 * T - 17) 33 6).
  follow (CLR 33 3 0 (0 :: 0 :: 0 :: repeat 1 (6 * T - 17) ++ [5; 2]) (const 0%sym) 4 (or_intror r1_4)).
  rewrite Hx0.
  replace (6 * T - 17) with (2 + (6 * T - 19)) by (revert HT; generalize T; intros; lia).
  follow (P4_B 1 (6 * T - 19) 0 (3 * x0) 32). rewrite merge3.
  apply (CLR (2 + 32 + 2 * 0) x0 2 _ (const 0%sym) 4 (or_intror r1_4)).
Qed.

(** J = (3 T - 13) / 7 periods: 6 T - 19 = 14 J + 7 because T = 2 mod 7 *)
Definition JJ : nat := (3 * T - 13) / 7.

Lemma JJ_eq : 6 * T - 19 = 14 * JJ + 7 /\ 1 <= JJ.
Proof.
  destruct T_mod7 as [s Hs]. pose proof T_ge as HT.
  assert (E : (3 * T - 13) / 7 = 3 * s - 1).
  { rewrite Hs. symmetry. apply Nat.div_unique with (r := 0); lia. }
  unfold JJ. rewrite E. revert Hs HT. generalize T. intros. lia.
Qed.

(** The last B-form before the halt; w is at least F^(2 JJ + 1)(34). *)
Lemma reach_end : exists k w f, c0 -->* Bf (FarE k) (repeat 1 w ++ [0]) f /\ iter (2 * JJ + 1) F 34 <= w.
Proof.
  destruct reach_per as [a [H0 Hinv]].
  destruct JJ_eq as [HJ HJ1].
  rewrite HJ in H0.
  destruct (PERIODS JJ 1 34 a Hinv) as [n [a' [H1 [Hinv' Hg]]]].
  replace (4 * JJ + 1) with (4 + (4 * JJ - 3)) in H1 by lia.
  destruct (ENDGAME (4 * JJ - 3) n a' Hinv') as [w [f [H2 Hw]]].
  exists (4 * JJ - 3), w, f. split.
  - follow H0. follow H1. exact H2.
  - replace (2 * JJ + 1) with (S (2 * JJ)) by lia. change (iter (S (2 * JJ)) F 34) with (F (iter (2 * JJ) F 34)).
    pose proof (F_mono _ _ Hg). lia.
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct reach_end as [k [w [f [H1 _]]]].
  destruct (HALT_B k w f) as [c [H2 H3]].
  assert (Hrun : c0 -->* c) by (follow H1; exact H2).
  destruct (with_counter Hrun) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. exact H3.
Qed.

(* ==================================================================================================== *)
(*            bb8_list/proofs/BB10_n1_bound.v: n1's score; it beats 0LJ0LC and the champion             *)
(* ==================================================================================================== *)

(* The earlier file(s) of this module made these constants Opaque; in the multi-file build
   this file started with them transparent (Opaque is not carried over by Require). *)
Transparent U arrow.

(* Each original file started with the symbol scope on top (from Individual102's `Open Scope sym`);
   restore that here, since the previous part may have ended in nat_scope. *)
Local Open Scope sym_scope.

(** * Score of the BB(10) candidate n1 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_---0LC *)

(** Generated by bb8_list/investigations/bb10_n1_coq (gen_bound.py from bound.v.in).
    Imports the halting proof BB10_n1.v unchanged (tm, c0, the run, the generated lemmas).

    Convention: busycoq stops BEFORE the undefined transition; the halting configuration [c_halt] is in state J
    reading a 0 (J0 undefined), and [ones c N] counts the ones on that tape.  The standard score (the halting
    transition treated as 1RZ, writing a 1 on the 0) is N + 1.

    Notation: T = 2 ^(37 arrows) 3 (= 2 B + 4 for the BB(8) record's final accumulator B), F n = 2 ^(n arrows) 4
    = 2 ^(n+1 arrows) 3, JJ = (3 T - 13) / 7 (the number of full periods).

    Main results (no axioms):
      score_exact       : the halt has 2 w + f + 3 k + 22 ones, for the explicit final w, f, k of the run,
                          with w >= F^(2 JJ + 1) (34);
      sigma_lower_bound : ones > G^((6 T - 19) / 7) (33), G x = 2 ^(x+1 arrows) 3   (the verifier's G^N(33),
                          N = (12 B + 5) / 7 growth events);
      dominates         : ones > (2 ^(K arrows))^x (x) for all K, x <= F (F (F 34))
                          (F (F (F 34)) is far beyond 4 T + 41, the index of M3's proved lower bound);
      beats_M3_bound    : ones > M3's proved lower bound arrow (4T+41) 2 (arrow (4T+39) 2 (arrow (4T+35) 2 5));
      beats_lead        : the 10-state candidate 0LJ0LC (BB10_lead_bound.score_exact) halts with Nl ones and
                          Nl + 1 < N + 1;
      beats_champion    : the BB(10) champion (BB10_champion_bound.score_exact) halts with Nc ones and
                          Nc + 1 < N + 1 (via BB10_lead_vs_champion.b2c_le).
      arrow_agree       : [arrow] here coincides with BB10_lead_bound.arrow. *)




Import Coq.micromega.Lia Coq.Arith.PeanoNat Coq.Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

(** [arrow] of BB10_lead_bound.v is the same Fixpoint as ours (separately defined: needs a proof). *)
Lemma arrow_agree : forall k a b, Lead10.arrow k a b = arrow k a b.
Proof.
  induction k as [| k IH]; intros a b; [reflexivity |].
  simpl. induction b as [| b IHb]; [reflexivity |]. simpl. rewrite IHb, IH. reflexivity.
Qed.

Lemma F_def : forall n, F n = arrow n 2 4.
Proof. reflexivity. Qed.

(** Never let a tactic compute these numbers (Opaque declarations are not exported by the imported file). *)
Opaque U arrow F.

(** ** The halting configuration (the end of the generated lemma EV_HALT) *)

Definition c_halt (f k w : nat) : Q * tape :=
  (0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1;0;1]^^k *> const 0)%sym <{{J}} (0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> [1;0]^^f *> 0 >> 1 >> 0 >> 1 >> [1;0;1]^^w *> const 0)%sym.

Lemma c_halt_halted : forall f k w, halted tm (c_halt f k w).
Proof. intros. reflexivity. Qed.

(** HALT_B of the halting file, with the halting configuration made explicit (same proof). *)
Lemma HALT_exact : forall k w f, Bf (FarE k) (repeat 1 w ++ [0]) f -->* c_halt f k w.
Proof. intros. unfold FarE. bnorm. follow (EV_HALT f k w). unfold c_halt. finish_norm. Qed.

Lemma reach_halt : exists k w f, c0 -->* c_halt f k w /\ iter (2 * JJ + 1) F 34 <= w.
Proof.
  destruct reach_end as [k [w [f [H1 H2]]]].
  exists k, w, f. split; [| exact H2]. follow H1. apply HALT_exact.
Qed.

(** ** Counting ones (the definitions of BB8_champ35_bound.v) *)

Definition sym_val (s : Sym) : nat :=
  match s with
  | S0 => 0
  | S1 => 1
  end.

Fixpoint count1 (xs : list Sym) : nat :=
  match xs with
  | [] => 0
  | x :: t => sym_val x + count1 t
  end.

(** [ones c N]: the tape of c is  L (reversed, left of the head), s (head cell), R (right of the head),
    with 0s beyond both lists, and N = number of 1s in L, s, R. *)
Definition ones (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl. - reflexivity. - rewrite IHxs. lia. Qed.

Lemma count1_pow : forall xs n, count1 (xs ^^ n) = n * count1 xs.
Proof. induction n; simpl. - reflexivity. - rewrite count1_app, IHn. lia. Qed.

Lemma ones_c_halt : forall f k w, ones (c_halt f k w) (2 * w + f + 3 * k + 22).
Proof.
  intros. exists J, ([S0;S0;S0;S1;S0;S0;S1;S0;S1;S0;S1;S0;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1] ++ [S1;S0;S1;S0;S1]^^k), ([S0;S0;S1;S1;S1;S1;S0;S0;S1;S0;S0;S1;S0;S0;S1;S0;S0;S1;S0;S1;S0;S1;S0] ++ [S1;S0]^^f ++ [S0;S1;S0;S1] ++ [S1;S0;S1]^^w), S0.
  split.
  - unfold c_halt. rewrite !Str_app_assoc. reflexivity.
  - rewrite !count1_app, !count1_pow. simpl. lia.
Qed.

(** ** The score *)

Theorem score_exact : exists c f k w, c0 -->* c /\ halted tm c /\ ones c (2 * w + f + 3 * k + 22) /\
  iter (2 * JJ + 1) F 34 <= w.
Proof.
  destruct reach_halt as [k [w [f [H1 H2]]]].
  exists (c_halt f k w), f, k, w.
  split; [exact H1 | split; [apply c_halt_halted | split; [apply ones_c_halt | exact H2]]].
Qed.

Lemma score_ge : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter (2 * JJ + 1) F 34 < N.
Proof.
  destruct score_exact as [c [f [k [w [H1 [H2 [H3 H4]]]]]]].
  exists c, (2 * w + f + 3 * k + 22). split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  revert H4. generalize (iter (2 * JJ + 1) F 34). intros. lia.
Qed.

(** ** Arithmetic on arrows *)

Lemma arrow_S_ge : forall k y, y + 1 <= arrow (S k) 2 y.
Proof. intros k [| y]; [rewrite arrow_S0; lia | apply arrow_gt; lia]. Qed.

Lemma arrow_double : forall k y, 2 * y <= arrow k 2 y.
Proof.
  induction k as [| k IH]; intros y.
  - rewrite (arrow_0 2 y). lia.
  - destruct y as [| y]; [rewrite arrow_S0; lia |].
    rewrite arrow_SS. pose proof (IH (arrow (S k) 2 y)). pose proof (arrow_S_ge k y). lia.
Qed.

Lemma arrow_lvl : forall k x, 2 <= x -> arrow k 2 x <= arrow (S k) 2 x.
Proof.
  intros k x Hx. induction x as [| x IH]; [lia |].
  destruct (Nat.eq_dec x 1) as [-> | Hx1].
  - rewrite (arrow_two k), (arrow_two (S k)). lia.
  - rewrite arrow_SS. specialize (IH ltac:(lia)).
    pose proof (arrow_gt k x ltac:(lia)).
    pose proof (arrow_mono k (S x) (arrow k 2 x) ltac:(lia)).
    pose proof (arrow_mono k (arrow k 2 x) (arrow (S k) 2 x) IH). lia.
Qed.

Lemma arrow_lvl_le : forall k K x, k <= K -> 2 <= x -> arrow k 2 x <= arrow K 2 x.
Proof.
  intros k K x HkK Hx. induction HkK; [lia |].
  pose proof (arrow_lvl m x Hx). lia.
Qed.

Lemma arrow_step2 : forall j x, 2 * arrow (S j) 2 x <= arrow (S j) 2 (S x).
Proof. intros. rewrite arrow_SS. apply arrow_double. Qed.

Lemma F_double : forall n, 2 * F n <= F (S n).
Proof. intros. rewrite F_S. apply arrow_double. Qed.

Lemma F34_big : 4 * F 26 + 19 <= F 34.
Proof.
  pose proof (F_double 26). pose proof (F_double 27). pose proof (F_double 28).
  pose proof (F_mono 29 34 ltac:(lia)). pose proof (F_ge 26).
  revert H H0 H1 H2 H3. generalize (F 26) (F 27) (F 28) (F 29) (F 34). intros. lia.
Qed.

(** iter 3 F 34 = F (F (F 34)) *)
Lemma iter3F : iter 3 F 34 = F (F (F 34)).
Proof. reflexivity. Qed.

Lemma JJ_ge2 : 2 <= JJ.
Proof.
  pose proof JJ_eq as [HJ _]. pose proof T_ge. revert HJ H. generalize T JJ. intros. lia.
Qed.

Lemma iter_big : forall j, 3 <= j -> F (F (F 34)) <= iter j F 34.
Proof.
  intros j Hj. replace j with ((j - 3) + 3) by lia. rewrite iter_add.
  rewrite iter3F. apply iterF_ge.
Qed.

(** ** The verifier's form: sigma > G^N(33), G x = 2 ^(x+1 arrows) 3, N = (12 B + 5) / 7 = (6 T - 19) / 7 *)

Lemma iter_G : forall n x, iter n (fun y => arrow (y + 1) 2 3) x = iter n F x.
Proof.
  induction n; intros; simpl; [reflexivity |].
  rewrite IHn, Nat.add_1_r, arrow_S3. reflexivity.
Qed.

Lemma N_eq : (6 * arrow 37 2 3 - 19) / 7 = 2 * JJ + 1.
Proof.
  rewrite <- T_def. destruct JJ_eq as [HJ _]. rewrite HJ.
  symmetry. apply Nat.div_unique with (r := 0); lia.
Qed.

Theorem sigma_lower_bound : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  iter ((6 * arrow 37 2 3 - 19) / 7) (fun x => arrow (x + 1) 2 3) 33 < N.
Proof.
  destruct score_ge as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  rewrite N_eq, iter_G. pose proof (iterF_mono (2 * JJ + 1) 33 34 ltac:(lia)). lia.
Qed.

(** ** Domination of every arrow-iterate with index and count up to F (F (F 34)) *)

Lemma arrow_add : forall K a b, arrow (S K) 2 (a + b) = iter a (arrow K 2) (arrow (S K) 2 b).
Proof. induction a; intros; simpl; [reflexivity |]. rewrite arrow_SS, IHa. reflexivity. Qed.

Lemma iter_arrow_le : forall K x, iter x (arrow K 2) x <= arrow (S K) 2 (2 * x).
Proof.
  intros. replace (2 * x) with (x + x) by lia. rewrite arrow_add.
  pose proof (arrow_S_ge K x).
  assert (Hm : forall n a b, a <= b -> iter n (arrow K 2) a <= iter n (arrow K 2) b).
  { induction n; intros; simpl; [lia | apply arrow_mono, IHn; lia]. }
  apply Hm. lia.
Qed.

Lemma F_lin : forall n, 4 <= n -> 8 * n + 48 <= F n.
Proof.
  intros n Hn. induction Hn.
  - pose proof (F_double 0). pose proof (F_double 1). pose proof (F_double 2). pose proof (F_double 3).
    rewrite F_0 in *. lia.
  - pose proof (F_double m). lia.
Qed.

Theorem dominates : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  forall K x, K <= F (F (F 34)) -> x <= F (F (F 34)) -> iter x (arrow K 2) x < N.
Proof.
  destruct score_ge as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  intros K x HK Hx.
  pose proof JJ_ge2 as HJ.
  assert (H5 : F (F (F (F (F 34)))) <= iter (2 * JJ + 1) F 34).
  { replace (2 * JJ + 1) with ((2 * JJ - 4) + 5) by lia. rewrite iter_add.
    change (iter 5 F 34) with (F (F (F (F (F 34))))). apply iterF_ge. }
  revert HK Hx H4 H5. generalize (F (F (F 34))). intros M HK Hx H4 H5.
  destruct x as [| x']; [simpl iter; lia |].
  (* F (F M) >= arrow (M + 2) 2 4 = arrow (M + 1) 2 (F (M + 1)) >= arrow (M + 1) 2 (2 x) >= arrow (S K) 2 (2 x) *)
  pose proof (F_ge M) as HFM.
  assert (A1 : arrow (M + 2) 2 4 <= F (F M)).
  { rewrite (F_def (F M)). apply arrow_lvl_le; lia. }
  assert (A2 : arrow (M + 2) 2 4 = arrow (M + 1) 2 (F (M + 1))).
  { replace (M + 2) with (S (M + 1)) by lia. replace 4 with (S 3) by reflexivity. rewrite arrow_SS, arrow_S3. reflexivity. }
  pose proof (F_double M) as HD. replace (S M) with (M + 1) in HD by lia.
  pose proof (arrow_mono (M + 1) (2 * S x') (F (M + 1)) ltac:(lia)) as A3.
  pose proof (arrow_lvl_le (S K) (M + 1) (2 * S x') ltac:(lia) ltac:(lia)) as A4.
  pose proof (iter_arrow_le K (S x')) as A5.
  lia.
Qed.

(** M3's proved lower bound (BB10_fw1_bound.sigma_lower_bound), as a closed expression *)
Theorem beats_M3_bound : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  arrow (4 * arrow 37 2 3 + 41) 2 (arrow (4 * arrow 37 2 3 + 39) 2 (arrow (4 * arrow 37 2 3 + 35) 2 5)) < N.
Proof.
  destruct dominates as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  rewrite <- T_def.
  assert (HM : 4 * T + 41 <= F (F (F 34))).
  { rewrite T_def, arrow_S3.
    pose proof (F_ge 34). pose proof (F_mono 36 (F 34) ltac:(lia)) as E1.
    pose proof (F_ge (F 34)). pose proof (F_lin (F (F 34)) ltac:(lia)) as E2.
    revert E1 E2. generalize (F 36) (F (F 34)) (F (F (F 34))). intros. lia. }
  specialize (H4 (4 * T + 41) 5 HM ltac:(pose proof (F_ge (F (F 34))); lia)).
  revert H4. generalize T. intros t H4.
  set (K := 4 * t + 41) in *.
  assert (P5 : 2 <= arrow K 2 5) by (pose proof (arrow_gt K 5 ltac:(lia)); lia).
  assert (L1 : arrow (4 * t + 35) 2 5 <= arrow K 2 5) by (apply arrow_lvl_le; unfold K; lia).
  assert (L2 : arrow (4 * t + 39) 2 (arrow (4 * t + 35) 2 5) <= arrow K 2 (arrow K 2 5)).
  { apply (Nat.le_trans _ (arrow (4 * t + 39) 2 (arrow K 2 5))); [apply arrow_mono; exact L1 |].
    apply arrow_lvl_le; [unfold K; lia | exact P5]. }
  assert (L3 : arrow K 2 (arrow (4 * t + 39) 2 (arrow (4 * t + 35) 2 5)) <= iter 3 (arrow K 2) 5).
  { change (iter 3 (arrow K 2) 5) with (arrow K 2 (arrow K 2 (arrow K 2 5))). apply arrow_mono. exact L2. }
  assert (L4 : iter 3 (arrow K 2) 5 <= iter 5 (arrow K 2) 5).
  { apply iter_mono_n; [intros; apply arrow_props | lia]. }
  unfold K in *. lia.
Qed.

(** ** The 10-state candidate 0LJ0LC and the BB(10) champion *)

(** a count 2 (Y - 4) + 2 L + 5 with Y = 2 ^(L arrows) 5 is below 2 ^(L+2 arrows) 4 *)
Lemma lead_count_lt : forall L, 1 <= L -> 2 * (arrow L 2 5 - 4) + 2 * L + 5 < arrow (L + 2) 2 4.
Proof.
  intros L HL.
  assert (E1 : arrow (L + 2) 2 4 = arrow (L + 1) 2 (F (L + 1))).
  { replace (L + 2) with (S (L + 1)) by lia. replace 4 with (S 3) by reflexivity. rewrite arrow_SS, arrow_S3. reflexivity. }
  pose proof (F_ge (L + 1)) as E2.
  assert (E3 : arrow (L + 1) 2 6 <= arrow (L + 1) 2 (F (L + 1))) by (apply arrow_mono; lia).
  assert (E4 : 2 * arrow (L + 1) 2 5 <= arrow (L + 1) 2 6) by (replace (L + 1) with (S L) by lia; apply arrow_step2).
  assert (E5 : arrow (L + 1) 2 5 = arrow L 2 (F (L + 1))).
  { replace (L + 1) with (S L) by lia. replace 5 with (S 4) by reflexivity. rewrite arrow_SS, <- F_def. reflexivity. }
  assert (E7 : arrow L 2 6 <= arrow L 2 (F (L + 1))) by (apply arrow_mono; lia).
  assert (E8 : 2 * arrow L 2 5 <= arrow L 2 6).
  { destruct L as [| L']; [lia |]. apply arrow_step2. }
  assert (E10 : L + 8 <= arrow L 2 5).
  { pose proof (arrow_mono L 4 5 ltac:(lia)). rewrite <- F_def in H. pose proof (F_ge L). lia. }
  rewrite E1. lia.
Qed.

(** the 0LJ0LC candidate's exact count (BB10_lead_bound.score_exact) is below F^(2 JJ + 1)(34) *)
Lemma lead_lt : 2 * Lead10.b2 + 2 * (4 * Lead10.bf + 33) + 5 < iter (2 * JJ + 1) F 34.
Proof.
  pose proof Lead10.b2_closed as Hb2. pose proof Lead10.bf_closed as Hbf.
  rewrite arrow_agree in Hb2, Hbf.
  pose proof JJ_ge2 as HJ.
  assert (H3F : F (F (F 34)) <= iter (2 * JJ + 1) F 34) by (apply iter_big; lia).
  revert Hb2 Hbf H3F. generalize Lead10.b2 Lead10.bf. intros b2 bf Hb2 Hbf H3F.
  pose proof (lead_count_lt (4 * bf + 33) ltac:(lia)) as Hl.
  assert (HL : 4 * bf + 35 <= F (F 34)).
  { rewrite arrow_S3 in Hbf. pose proof F34_big. pose proof (F_ge (F 34)). lia. }
  assert (HA : arrow (4 * bf + 33 + 2) 2 4 <= F (F (F 34))).
  { rewrite (F_def (F (F 34))). apply arrow_lvl_le; lia. }
  lia.
Qed.

Theorem beats_lead : exists cl nl co no,
  c0 -[ Lead10.tm ]->* cl /\ halted Lead10.tm cl /\ Lead10.ones cl nl /\
  c0 -->* co /\ halted tm co /\ ones co no /\ nl + 1 < no + 1.
Proof.
  destruct Lead10.score_exact as [cl [H1 [H2 H3]]].
  destruct score_ge as [co [no [H4 [H5 [H6 H7]]]]].
  exists cl, (2 * Lead10.b2 + 2 * (4 * Lead10.bf + 33) + 5), co, no.
  split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact H4 | split; [exact H5 | split; [exact H6 |]]]]]].
  pose proof lead_lt. lia.
Qed.

Theorem beats_champion : exists cc nc co no,
  c0 -[ Champion10.tm ]->* cc /\ halted Champion10.tm cc /\ Champion10.ones cc nc /\
  c0 -->* co /\ halted tm co /\ ones co no /\ nc + 1 < no + 1.
Proof.
  destruct Champion10.score_exact as [cc [H1 [H2 H3]]].
  destruct score_ge as [co [no [H4 [H5 [H6 H7]]]]].
  exists cc, (Champion10.b2 + 3), co, no.
  split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact H4 | split; [exact H5 | split; [exact H6 |]]]]]].
  pose proof Lead10.b2c_le. pose proof lead_lt. lia.
Qed.

(* ==================================================================================================== *)
(*                      bb8_list/proofs/BB10_n1_exact.v: n1's score in closed form                      *)
(* ==================================================================================================== *)

(* The earlier file(s) of this module made these constants Opaque; in the multi-file build
   this file started with them transparent (Opaque is not carried over by Require). *)
Transparent U arrow F.

(* Each original file started with the symbol scope on top (from Individual102's `Open Scope sym`);
   restore that here, since the previous part may have ended in nat_scope. *)
Local Open Scope sym_scope.

(** * Closed-form score of the BB(10) candidate n1 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_---0LC *)

(** Generated by bb8_list/investigations/bb10_n1_coq (exact.v.in). Imports BB10_n1.v and BB10_n1_bound.v unchanged.

    The run passes JJ = (3 T - 13) / 7 periods, T = 2 ^(37 arrows) 3. A period start Per k m n a (n = zero-block
    length, a = accumulator) is tracked by the pair (n, g) with a = 3 g - 8. One period maps (n, g) to [step (n, g)]:
      n2 = n + 2 g - 6                                            (the P2 growth: the parked accumulator is unpacked)
      n4 = n2 + 2 * 2 ^(n2+1 arrows) (2 ^(n arrows) 5 - 1) - 4    (the P4 growth)
      g' = 2 ^(n4+1 arrows) (2 ^(n2 arrows) 5 - 1)                 (the next accumulator)
    The first period starts from (34, 2 ^(35 arrows) (2 ^(34 arrows) 5 - 1)). With (n, g) after JJ periods and
    W = n + 2 g - 6 (the final zero block), the halting tape has exactly
      2 W + 3 * 2 ^(W+1 arrows) (2 ^(n arrows) 5) + 12 JJ + 5
    ones (Theorem score_closed); the standard score is one more.  score_value_gt: the value exceeds F^(2 JJ + 1)(34),
    the lower bound of BB10_n1_bound.v (F n = 2 ^(n arrows) 4). *)



Import Coq.micromega.Lia Coq.Arith.PeanoNat Coq.Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

Opaque U arrow F.

(** ** The closed form of a clearing from 4: (U j)^d (4) = 3 * 2 ^(j+1 arrows) (d + 2) - 8 *)

Lemma iterU : forall j d, iter d (U j) 4 + 8 = 3 * arrow (S j) 2 (d + 2).
Proof.
  intros j. induction d as [| d IH].
  - change (iter 0 (U j) 4) with 4. rewrite arrow_two. reflexivity.
  - change (iter (S d) (U j) 4) with (U j (iter d (U j) 4)).
    replace (S d + 2) with (S (d + 2)) by lia. rewrite arrow_SS.
    pose proof (arrow_ge4 (S j) (d + 2) ltac:(lia)) as H4.
    revert IH H4. generalize (iter d (U j) 4) (arrow (S j) 2 (d + 2)). intros A X IH H4.
    replace A with (3 * (X - 3) + 1) by lia.
    rewrite U_closed. replace (X - 3 + 3) with X by lia. reflexivity.
Qed.

Lemma iterU_eq : forall j d, iter d (U j) 4 = 1 + 3 * (arrow (S j) 2 (d + 2) - 3).
Proof.
  intros. pose proof (iterU j d). pose proof (arrow_ge4 (S j) (d + 2) ltac:(lia)).
  revert H H0. generalize (iter d (U j) 4) (arrow (S j) 2 (d + 2)). intros. lia.
Qed.

Lemma arrow5 : forall n, 6 <= arrow n 2 5.
Proof. intros. pose proof (arrow_gt n 5 ltac:(lia)). lia. Qed.

(** ** One period with every value explicit (the script of PERIOD, without the existentials) *)

Lemma PERIOD_U : forall k m w p x y x',
  iter 3 (U (S w)) 4 = 1 + 3 * x -> iter x (U (2 + w + 2 * p)) 4 = 1 + 3 * y ->
  iter 3 (U (1 + w + 2 * p)) 4 = 1 + 3 * x' ->
  Per k (14 + m) (S (S w)) (1 + 3 * p) -->*
  Per (4 + k) m (2 + (w + 2 * p) + 2 * S y) (iter x' (U (2 + (w + 2 * p) + 2 * S y)) 4).
Proof.
  intros k m w p x y x' Hx Hy Hx'.
  unfold Per.
  replace (14 + m) with (6 + (8 + m)) by lia.
  follow (P1_B k (8 + m) (S (S w)) (1 + 3 * p)).
  follow (DEP9 (const 0%sym) (S w) (1 + 3 * p) (1 :: 0 :: 0 :: 0 :: repeat 1 (8 + m) ++ 5 :: repeat 2 (2 + k))).
  rewrite Hx. replace (8 + m) with (6 + (2 + m)) by lia.
  follow (P2_B (2 + k) (2 + m) p (3 * x) w). rewrite merge3.
  follow (CLR (2 + w + 2 * p) x 2 [2] (FarP (2 + k) (2 + m)) 4 (or_intror r1_4)).
  follow (P3_B (2 + k) (2 + m) (2 + w + 2 * p) (iter x (U (2 + w + 2 * p)) 4)).
  rewrite Hy. replace (5 + (1 + 3 * y)) with (3 + (3 + 3 * y)) by lia. replace (2 + (2 + k)) with (4 + k) by lia.
  follow (DEP9 (const 0%sym) (1 + w + 2 * p) (3 + 3 * y) (0 :: 0 :: repeat 1 (2 + m) ++ 5 :: repeat 2 (4 + k))).
  rewrite Hx'. replace (3 + 3 * y) with (3 * S y) by lia.
  replace (1 + w + 2 * p) with (1 + (w + 2 * p)) by lia.
  follow (P4_B (4 + k) m (S y) (3 * x') (w + 2 * p)). rewrite merge3.
  apply (CLR (2 + (w + 2 * p) + 2 * S y) x' 2 _ (const 0%sym) 4 (or_intror r1_4)).
Qed.

(** ** The period map on (n, g), a = 3 g - 8 *)

Definition step (s : nat * nat) : nat * nat :=
  let n := fst s in
  let g := snd s in
  let n2 := n + 2 * g - 6 in
  let n4 := n2 + 2 * arrow (S n2) 2 (arrow n 2 5 - 1) - 4 in
  (n4, arrow (S n4) 2 (arrow n2 2 5 - 1)).

Fixpoint stepn (j : nat) (s : nat * nat) : nat * nat :=
  match j with
  | O => s
  | S j' => stepn j' (step s)
  end.

Lemma PERIOD_G : forall k m n g, 3 <= n -> 4 <= g ->
  Per k (14 + m) n (3 * g - 8) -->* Per (4 + k) m (fst (step (n, g))) (3 * snd (step (n, g)) - 8).
Proof.
  intros k m n g Hn Hg.
  destruct n as [| n1]; [lia |]. destruct n1 as [| w]; [lia |].
  set (p := g - 3).
  set (x := arrow (S (S w)) 2 5 - 3).
  set (n2 := 2 + w + 2 * p).
  set (y := arrow (S n2) 2 (x + 2) - 3).
  set (x' := arrow n2 2 5 - 3).
  assert (Hx : iter 3 (U (S w)) 4 = 1 + 3 * x) by (unfold x; apply iterU_eq).
  assert (Hy : iter x (U (2 + w + 2 * p)) 4 = 1 + 3 * y) by (unfold y, n2; apply iterU_eq).
  assert (Hx' : iter 3 (U (1 + w + 2 * p)) 4 = 1 + 3 * x').
  { unfold x'. rewrite iterU_eq. unfold n2. replace (S (1 + w + 2 * p)) with (2 + w + 2 * p) by lia. reflexivity. }
  pose proof (PERIOD_U k m w p x y x' Hx Hy Hx') as HP.
  replace (3 * g - 8) with (1 + 3 * p) by (unfold p; lia).
  assert (E1 : fst (step (S (S w), g)) = 2 + (w + 2 * p) + 2 * S y).
  { unfold step. cbn [fst snd]. unfold y, x, n2, p.
    pose proof (arrow5 (S (S w))). pose proof (arrow_ge4 (S (2 + w + 2 * (g - 3))) (arrow (S (S w)) 2 5 - 3 + 2) ltac:(lia)).
    replace (S (S w) + 2 * g - 6) with (2 + w + 2 * (g - 3)) by lia.
    replace (arrow (S (S w)) 2 5 - 1) with (arrow (S (S w)) 2 5 - 3 + 2) by lia.
    revert H0. generalize (arrow (S (2 + w + 2 * (g - 3))) 2 (arrow (S (S w)) 2 5 - 3 + 2)). intros. lia. }
  assert (E2 : 3 * snd (step (S (S w), g)) - 8 = iter x' (U (2 + (w + 2 * p) + 2 * S y)) 4).
  { rewrite iterU_eq. rewrite <- E1. unfold step. cbn [fst snd].
    replace (S (S w) + 2 * g - 6) with n2 by (unfold n2, p; lia).
    unfold x'. pose proof (arrow5 n2).
    replace (arrow n2 2 5 - 1) with (arrow n2 2 5 - 3 + 2) by lia.
    set (N4 := n2 + 2 * arrow (S n2) 2 (arrow (S (S w)) 2 5 - 1) - 4).
    pose proof (arrow_ge4 (S N4) (arrow n2 2 5 - 3 + 2) ltac:(lia)).
    revert H0. generalize (arrow (S N4) 2 (arrow n2 2 5 - 3 + 2)). intros. lia. }
  rewrite E1, E2. exact HP.
Qed.

(** ** Sizes: the invariant g >= F n is kept and n grows by F twice per period *)

Lemma step_props : forall n g, 3 <= n -> F n <= g ->
  3 <= fst (step (n, g)) /\ F (fst (step (n, g))) <= snd (step (n, g)) /\ F (F n) <= fst (step (n, g)).
Proof.
  intros n g Hn Hg. unfold step. cbn [fst snd].
  pose proof (F_ge n) as HF.
  set (n2 := n + 2 * g - 6).
  assert (Hn2 : F n <= n2) by (unfold n2; lia).
  pose proof (arrow5 n) as A5. pose proof (arrow5 n2) as A5'.
  assert (G1 : F n2 <= arrow (S n2) 2 (arrow n 2 5 - 1)).
  { rewrite <- arrow_S3. apply arrow_mono. lia. }
  pose proof (F_ge n2) as HF2.
  set (n4 := n2 + 2 * arrow (S n2) 2 (arrow n 2 5 - 1) - 4).
  assert (Hn4 : F n2 <= n4) by (unfold n4; lia).
  assert (G2 : F n4 <= arrow (S n4) 2 (arrow n2 2 5 - 1)).
  { rewrite <- arrow_S3. apply arrow_mono. lia. }
  pose proof (F_mono _ _ Hn2). pose proof (F_ge n4). lia.
Qed.

Lemma PERIODS_G : forall J k n g, 3 <= n -> F n <= g ->
  Per k (14 * J + 7) n (3 * g - 8) -->* Per (4 * J + k) 7 (fst (stepn J (n, g))) (3 * snd (stepn J (n, g)) - 8) /\
  3 <= fst (stepn J (n, g)) /\ F (fst (stepn J (n, g))) <= snd (stepn J (n, g)) /\ iter (2 * J) F n <= fst (stepn J (n, g)).
Proof.
  induction J as [| J IH]; intros k n g Hn Hg.
  - cbn [stepn fst snd]. replace (14 * 0 + 7) with 7 by reflexivity. replace (4 * 0 + k) with k by reflexivity.
    split; [apply evstep_refl | split; [lia | split; [lia | change (iter (2 * 0) F n) with n; lia]]].
  - pose proof (F_ge n).
    destruct (step_props n g Hn Hg) as [S1 [S2 S3]].
    destruct (step (n, g)) as [n' g'] eqn:Es. cbn [fst snd] in S1, S2, S3.
    destruct (IH (4 + k) n' g' S1 S2) as [H1 [H2 [H3 H4]]].
    change (stepn (S J) (n, g)) with (stepn J (step (n, g))). rewrite Es.
    split; [| split; [exact H2 | split; [exact H3 |]]].
    + replace (14 * S J + 7) with (14 + (14 * J + 7)) by lia.
      replace (4 * S J + k) with (4 * J + (4 + k)) by lia.
      eapply evstep_trans; [| exact H1].
      pose proof (PERIOD_G k (14 * J + 7) n g Hn ltac:(lia)) as HP. rewrite Es in HP. cbn [fst snd] in HP. exact HP.
    + replace (2 * S J) with (2 * J + 2) by lia. rewrite iter_add.
      change (iter 2 F n) with (F (F n)). pose proof (iterF_mono (2 * J) _ _ S3). lia.
Qed.

(** ** The endgame with explicit values *)

Lemma ENDGAME_G : forall k n g, 3 <= n -> 4 <= g ->
  Per (4 + k) 7 n (3 * g - 8) -->*
  Bf (FarE k) (repeat 1 (n + 2 * g - 6) ++ [0]) (3 * arrow (S (n + 2 * g - 6)) 2 (arrow n 2 5) - 8).
Proof.
  intros k n g Hn Hg.
  destruct n as [| n1]; [lia |]. destruct n1 as [| w]; [lia |].
  set (p := g - 3). set (x := arrow (S (S w)) 2 5 - 3).
  assert (Hx : iter 3 (U (S w)) 4 = 1 + 3 * x) by (unfold x; apply iterU_eq).
  replace (3 * g - 8) with (1 + 3 * p) by (unfold p; lia).
  replace (S (S w) + 2 * g - 6) with (2 + w + 2 * p) by (unfold p; lia).
  assert (Ef : 3 * arrow (S (2 + w + 2 * p)) 2 (arrow (S (S w)) 2 5) - 8 = iter (S x) (U (2 + w + 2 * p)) 4).
  { rewrite iterU_eq. unfold x. pose proof (arrow5 (S (S w))).
    replace (S (arrow (S (S w)) 2 5 - 3) + 2) with (arrow (S (S w)) 2 5) by lia.
    pose proof (arrow_ge4 (S (2 + w + 2 * p)) (arrow (S (S w)) 2 5) ltac:(lia)).
    revert H0. generalize (arrow (S (2 + w + 2 * p)) 2 (arrow (S (S w)) 2 5)). intros. lia. }
  rewrite Ef.
  unfold Per.
  follow (P1_B (4 + k) 1 (S (S w)) (1 + 3 * p)).
  follow (DEP9 (const 0%sym) (S w) (1 + 3 * p) (1 :: 0 :: 0 :: 0 :: repeat 1 1 ++ 5 :: repeat 2 (2 + (4 + k)))).
  rewrite Hx. replace (2 + (4 + k)) with (6 + k) by lia.
  follow (E_B k p (3 * x) w). rewrite merge3.
  replace (3 + 3 * x) with (0 + 3 * S x) by lia.
  rewrite <- (app_nil_r (repeat 1 (2 + w + 2 * p) ++ [0])), <- app_assoc.
  apply (CLR (2 + w + 2 * p) (S x) 0 [] (FarE k) 4 (or_intror r1_4)).
Qed.

(** ** The start with an explicit accumulator *)

Definition g0 : nat := arrow 35 2 (arrow 34 2 5 - 1).

Lemma reach_per_exact : c0 -->* Per 1 (6 * T - 19) 34 (3 * g0 - 8).
Proof.
  pose proof Af_closed as HAf. pose proof T_ge as HT. rewrite <- Af_def in HAf.
  remember (arrow 34 2 5 - 3) as x0 eqn:Ex0.
  assert (Hx0 : iter 3 (U 33) 4 = 1 + 3 * x0) by (rewrite Ex0; apply iterU_eq).
  assert (Hg0 : 3 * g0 - 8 = iter x0 (U 34) 4).
  { rewrite iterU_eq. unfold g0. rewrite Ex0. pose proof (arrow5 34).
    replace (arrow 34 2 5 - 3 + 2) with (arrow 34 2 5 - 1) by lia.
    pose proof (arrow_ge4 35 (arrow 34 2 5 - 1) ltac:(lia)).
    revert H0. generalize (arrow 35 2 (arrow 34 2 5 - 1)). intros. lia. }
  rewrite Hg0.
  follow init_reach.
  follow (CLR 35 2 1 [] (const 0%sym) 4 (or_intror r1_4)). rewrite <- Af_def.
  rewrite repeat_snoc, app_nil_r.
  follow (H_B 35 Af).
  replace (repeat 1 4 ++ repeat 1 (2 * Af) ++ [2]) with (repeat 1 (5 + (6 * T - 17)) ++ [2])
    by (rewrite <- repeat_add; f_equal; f_equal; revert HAf HT; generalize Af T; intros; lia).
  follow (S0_B (6 * T - 17) 33 6).
  follow (CLR 33 3 0 (0 :: 0 :: 0 :: repeat 1 (6 * T - 17) ++ [5; 2]) (const 0%sym) 4 (or_intror r1_4)).
  rewrite Hx0.
  replace (6 * T - 17) with (2 + (6 * T - 19)) by (revert HT; generalize T; intros; lia).
  follow (P4_B 1 (6 * T - 19) 0 (3 * x0) 32). rewrite merge3.
  apply (CLR (2 + 32 + 2 * 0) x0 2 _ (const 0%sym) 4 (or_intror r1_4)).
Qed.

Lemma g0_ge : F 34 <= g0.
Proof. unfold g0. rewrite <- arrow_S3. apply arrow_mono. pose proof (arrow5 34). lia. Qed.

(** ** The closed form *)

Definition fin : nat * nat := stepn JJ (34, g0).
Definition Wf : nat := fst fin + 2 * snd fin - 6.

(** the exact number of ones on the halting tape *)
Definition score_value : nat := 2 * Wf + 3 * arrow (S Wf) 2 (arrow (fst fin) 2 5) + 12 * JJ + 5.

Lemma JJ_closed : JJ = (3 * arrow 37 2 3 - 13) / 7.
Proof. unfold JJ. rewrite T_def. reflexivity. Qed.

Lemma fin_props : 3 <= fst fin /\ F (fst fin) <= snd fin /\ iter (2 * JJ) F 34 <= fst fin.
Proof.
  destruct (PERIODS_G JJ 1 34 g0 ltac:(lia) g0_ge) as [_ [H2 [H3 H4]]].
  unfold fin. split; [exact H2 | split; [exact H3 | exact H4]].
Qed.

Theorem score_closed : exists c, c0 -->* c /\ halted tm c /\ ones c score_value.
Proof.
  destruct JJ_eq as [HJ HJ1].
  pose proof g0_ge as Hg0. pose proof (F_ge 34) as HF34.
  destruct (PERIODS_G JJ 1 34 g0 ltac:(lia) Hg0) as [H1 [H2 [H3 H4]]].
  fold fin in H1, H2, H3, H4.
  pose proof (F_ge (fst fin)) as HFf.
  exists (c_halt (3 * arrow (S Wf) 2 (arrow (fst fin) 2 5) - 8) (4 * JJ - 3) Wf).
  split; [| split; [apply c_halt_halted |]].
  - pose proof reach_per_exact as H0. rewrite HJ in H0.
    follow H0.
    replace (4 * JJ + 1) with (4 + (4 * JJ - 3)) in H1 by lia.
    follow H1.
    follow (ENDGAME_G (4 * JJ - 3) (fst fin) (snd fin) H2 ltac:(lia)).
    apply HALT_exact.
  - pose proof (ones_c_halt (3 * arrow (S Wf) 2 (arrow (fst fin) 2 5) - 8) (4 * JJ - 3) Wf) as HO.
    unfold score_value.
    pose proof (arrow_ge4 (S Wf) (arrow (fst fin) 2 5) ltac:(pose proof (arrow5 (fst fin)); lia)) as HA.
    revert HO HA. generalize (arrow (S Wf) 2 (arrow (fst fin) 2 5)). intros A HO HA.
    replace (2 * Wf + 3 * A + 12 * JJ + 5) with (2 * Wf + (3 * A - 8) + 3 * (4 * JJ - 3) + 22) by lia.
    exact HO.
Qed.

(** the closed form exceeds the lower bound of BB10_n1_bound.v *)
Theorem score_value_gt : iter (2 * JJ + 1) F 34 < score_value.
Proof.
  destruct fin_props as [H1 [H2 H3]].
  pose proof (iterF_mono 1 _ _ H3) as H4. rewrite <- iter_add in H4. replace (1 + 2 * JJ) with (2 * JJ + 1) in H4 by lia.
  change (iter 1 F (fst fin)) with (F (fst fin)) in H4.
  unfold score_value, Wf.
  revert H2 H4. generalize (iter (2 * JJ + 1) F 34) (arrow (S (fst fin + 2 * snd fin - 6)) 2 (arrow (fst fin) 2 5)).
  intros. pose proof (F_ge (fst fin)). lia.
Qed.

(** the closed form, with every definition unfolded down to arrow, stepn and T *)
Theorem score_closed_unfolded : exists c, c0 -->* c /\ halted tm c /\
  ones c (let J := (3 * arrow 37 2 3 - 13) / 7 in
          let s := stepn J (34, arrow 35 2 (arrow 34 2 5 - 1)) in
          let W := fst s + 2 * snd s - 6 in
          2 * W + 3 * arrow (S W) 2 (arrow (fst s) 2 5) + 12 * J + 5).
Proof.
  destruct score_closed as [c [H1 [H2 H3]]]. exists c. split; [exact H1 | split; [exact H2 |]].
  rewrite <- JJ_closed. exact H3.
Qed.

(* ==================================================================================================== *)
(*           bb8_list/proofs/BB10_n1_fgh.v: n1 in the fast-growing hierarchy; Graham's number           *)
(* ==================================================================================================== *)

(* The earlier file(s) of this module made these constants Opaque; in the multi-file build
   this file started with them transparent (Opaque is not carried over by Require). *)
Transparent U arrow F.

(* Each original file started with the symbol scope on top (from Individual102's `Open Scope sym`);
   restore that here, since the previous part may have ended in nat_scope. *)
Local Open Scope sym_scope.

(** * n1 in the fast-growing hierarchy, and Graham's number *)

(** Generated by bb8_list/investigations/bb10_n1_coq (fgh.v.in). Imports BB10_n1.v, BB10_n1_bound.v and
    BB10_n1_exact.v unchanged.  Machine: n1 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_---0LC.
    [ones c N]: the halting tape of c holds exactly N ones (the standard score is N + 1: J0 is the undefined halt).

    Standard definitions (Nat.iter n f x = f (f (... (f x)))  with n applications of f):
      fgh 0 n = n + 1,  fgh (k+1) n = (fgh k)^n (n)          f_k of the fast-growing hierarchy
      f_omega n = fgh n n,  f_omega1 n = f_omega^n (n)          f_omega and f_(omega+1)
      up3 0 n = 3 * n,  up3 (k+1) n = (up3 k)^n (1)            up3 k n = 3 ^(k arrows) n  (Knuth)
      graham_g 0 = 4,  graham_g (k+1) = up3 (graham_g k) 3     graham_g 1 = 3^^^^3, ..., Graham = graham_g 64

    Results (no axioms):
      fgh_lower      : the halting tape has N ones with f_omega1 ((3 * 2^(37 arrows) 3 - 13) / 7 - 2) < N
      fgh_lower_64   : ... with f_omega1 64 < N
      graham_lt_f_omega1_64 : Graham < f_omega1 64
      beats_graham   : ... with Graham < N
      fgh_level      : f_omega1 ((3 T - 13)/7 - 2) < N < f_omega1 (6 T), T = 2^(37 arrows) 3, for the exact N  *)



Import Coq.micromega.Lia Coq.Arith.PeanoNat Coq.Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

(** ** Definitions *)

Fixpoint fgh (k n : nat) : nat :=
  match k with
  | O => S n
  | S k' => Nat.iter n (fgh k') n
  end.

Definition f_omega (n : nat) : nat := fgh n n.

Definition f_omega1 (n : nat) : nat := Nat.iter n f_omega n.

Fixpoint up3 (k n : nat) : nat :=
  match k with
  | O => 3 * n
  | S k' => Nat.iter n (up3 k') 1
  end.

Fixpoint graham_g (k : nat) : nat :=
  match k with
  | O => 4
  | S k' => up3 (graham_g k') 3
  end.

Definition Graham : nat := graham_g 64.

(** sanity checks of the definitions on small values *)
Example fgh_1_5 : fgh 1 5 = 10. Proof. reflexivity. Qed.
Example fgh_2_3 : fgh 2 3 = 24. Proof. reflexivity. Qed.
Example up3_1_4 : up3 1 4 = 81. Proof. reflexivity. Qed.
Example up3_2_2 : up3 2 2 = 27. Proof. reflexivity. Qed.

Opaque U arrow F.

(** ** Basic facts *)

Lemma iter_nat : forall n (g : nat -> nat) x, Nat.iter n g x = iter n g x.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma fgh_0 : forall n, fgh 0 n = S n.
Proof. reflexivity. Qed.

Lemma fgh_S : forall k n, fgh (S k) n = iter n (fgh k) n.
Proof. intros. simpl. apply iter_nat. Qed.

Lemma f_omega1_iter : forall n, f_omega1 n = iter n f_omega n.
Proof. intros. unfold f_omega1. apply iter_nat. Qed.

Lemma up3_0 : forall n, up3 0 n = 3 * n.
Proof. reflexivity. Qed.

Lemma up3_S : forall k n, up3 (S k) n = iter n (up3 k) 1.
Proof. intros. simpl. apply iter_nat. Qed.

Opaque fgh up3.

Lemma iter_mono_x : forall g, (forall a b, a <= b -> g a <= g b) -> forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; [assumption | apply Hg, IHn; assumption]. Qed.

Lemma arrow_iter_mono : forall K n x y, x <= y -> iter n (arrow K 2) x <= iter n (arrow K 2) y.
Proof. intros. apply iter_mono_x; [intros; apply arrow_mono; assumption | assumption]. Qed.

Lemma fgh_ge : forall k n, n <= fgh k n.
Proof.
  induction k; intros n; [rewrite fgh_0; lia |].
  rewrite fgh_S. apply iter_ge. exact IHk.
Qed.

Lemma f_omega_ge : forall x, x <= f_omega x.
Proof. intros. apply fgh_ge. Qed.

Lemma iter_fo_ge : forall j x, x <= iter j f_omega x.
Proof. intros. apply iter_ge. exact f_omega_ge. Qed.

(** ** Upper bound of f_k by arrows, hence f_omega x <= F (F x) *)

Lemma arrow2_3x : forall x, 3 <= x -> 3 * x <= arrow 2 2 x.
Proof.
  intros x Hx. induction Hx.
  - rewrite (arrow_SS 1 2 2), (arrow_two 2), arrow_1_pow. simpl. lia.
  - pose proof (arrow_step2 1 m). lia.
Qed.

Lemma arrow_3x : forall k x, 3 <= x -> 3 * x <= arrow (S (S k)) 2 x.
Proof.
  intros. pose proof (arrow2_3x x H). pose proof (arrow_lvl_le 2 (S (S k)) x ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma fgh_le : forall k n, 3 <= n -> fgh k n <= arrow (S (S k)) 2 (3 * n).
Proof.
  induction k as [| k IH]; intros n Hn.
  - rewrite fgh_0. pose proof (arrow_gt 2 (3 * n) ltac:(lia)). lia.
  - rewrite fgh_S.
    assert (Hj : forall j, iter j (fgh k) n <= iter (2 * j) (arrow (S (S k)) 2) n).
    { induction j as [| j IHj]; [simpl; lia |].
      replace (2 * S j) with (S (S (2 * j))) by lia. cbn [iter].
      pose proof (fgh_ge k n). pose proof (iter_ge (fgh k) (fgh_ge k) j n) as Hge.
      set (y := iter j (fgh k) n) in *. set (z := iter (2 * j) (arrow (S (S k)) 2) n) in *.
      pose proof (IH y ltac:(lia)) as H1.
      pose proof (arrow_3x k y ltac:(lia)) as H2.
      pose proof (arrow_mono (S (S k)) _ _ H2) as H3.
      pose proof (arrow_mono (S (S k)) _ _ IHj) as H4. pose proof (arrow_mono (S (S k)) _ _ H4) as H5.
      lia. }
    specialize (Hj n).
    pose proof (arrow_S_ge (S (S k)) n) as H1.
    pose proof (arrow_iter_mono (S (S k)) (2 * n) n (arrow (S (S (S k))) 2 n) ltac:(lia)) as H2.
    rewrite <- arrow_add in H2. replace (2 * n + n) with (3 * n) in H2 by lia. lia.
Qed.

Lemma f_omega_le : forall x, 3 <= x -> f_omega x <= F (F x).
Proof.
  intros x Hx. unfold f_omega.
  pose proof (fgh_le x x Hx) as H1.
  pose proof (F_lin (S (S x)) ltac:(lia)) as H2.
  pose proof (arrow_mono (S (S x)) (3 * x) (F (S (S x))) ltac:(lia)) as H3.
  rewrite <- F_S in H3.
  pose proof (F_ge x) as H4. pose proof (F_mono (S (S (S x))) (F x) ltac:(lia)) as H5.
  lia.
Qed.

Lemma fo_iter_le : forall j m, 3 <= m -> iter j f_omega m <= iter (2 * j) F m.
Proof.
  induction j as [| j IH]; intros m Hm; [simpl; lia |].
  replace (2 * S j) with (S (S (2 * j))) by lia. cbn [iter].
  pose proof (iter_fo_ge j m). pose proof (IH m Hm).
  pose proof (f_omega_le (iter j f_omega m) ltac:(lia)).
  pose proof (F_mono _ _ (F_mono _ _ H0)). lia.
Qed.

(** ** Lower bounds for n1 *)

Lemma JJ_ge : 142 <= JJ.
Proof.
  destruct JJ_eq as [HJ _]. pose proof (F_lin 36 ltac:(lia)) as H.
  rewrite <- arrow_S3, <- T_def in H. revert HJ H. generalize T JJ. intros. lia.
Qed.

Lemma T_le : T <= F (F 34).
Proof. rewrite T_def, arrow_S3. apply F_mono. pose proof (F_lin 34 ltac:(lia)). lia. Qed.

Lemma JJ_le_T : JJ <= T.
Proof. unfold JJ. apply Nat.div_le_upper_bound; lia. Qed.

Theorem fgh_lower : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  f_omega1 ((3 * arrow 37 2 3 - 13) / 7 - 2) < N.
Proof.
  destruct score_ge as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  rewrite <- JJ_closed, f_omega1_iter. pose proof JJ_ge as HJ. pose proof JJ_le_T. pose proof T_le.
  pose proof (fo_iter_le (JJ - 2) (JJ - 2) ltac:(lia)) as A1.
  replace (2 * JJ + 1) with (2 * (JJ - 2) + 5) in H4 by lia. rewrite iter_add in H4.
  pose proof (iter_big 5 ltac:(lia)) as A2. pose proof (F_ge (F (F 34))) as A3.
  pose proof (iterF_mono (2 * (JJ - 2)) (JJ - 2) (iter 5 F 34) ltac:(lia)) as A4.
  lia.
Qed.

Theorem fgh_lower_64 : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega1 64 < N.
Proof.
  destruct score_ge as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  rewrite f_omega1_iter. pose proof JJ_ge as HJ.
  pose proof (fo_iter_le 64 64 ltac:(lia)) as A1.
  replace (2 * JJ + 1) with (2 * 64 + (2 * JJ + 1 - 128)) in H4 by lia. rewrite iter_add in H4.
  replace (2 * JJ + 1 - 128) with (S (2 * JJ - 128)) in H4 by lia.
  pose proof (iterF_ge (2 * JJ - 128) 34) as A2. pose proof (F_mono _ _ A2) as A3.
  pose proof (F_lin 34 ltac:(lia)) as A4. change (iter (S (2 * JJ - 128)) F 34) with (F (iter (2 * JJ - 128) F 34)) in H4.
  pose proof (iterF_mono (2 * 64) 64 (F (iter (2 * JJ - 128) F 34)) ltac:(lia)) as A5.
  lia.
Qed.

(** ** Graham's number *)

Lemma up3_le : forall k n, up3 k n <= arrow k 2 (2 * n).
Proof.
  induction k as [| k IH]; intros n.
  - rewrite up3_0, (arrow_0 2 (2 * n)). lia.
  - rewrite up3_S, arrow_S_iter.
    induction n as [| n IHn]; [simpl; lia |].
    replace (2 * S n) with (S (S (2 * n))) by lia. cbn [iter].
    pose proof (IH (iter n (up3 k) 1)) as H1.
    pose proof (arrow_double k (iter n (up3 k) 1)) as H2.
    pose proof (arrow_mono k _ _ H2) as H3.
    pose proof (arrow_mono k _ _ IHn) as H4. pose proof (arrow_mono k _ _ H4) as H5.
    lia.
Qed.

Lemma fgh1 : forall n, fgh 1 n = 2 * n.
Proof.
  intros. rewrite fgh_S. assert (forall j x, iter j (fgh 0) x = j + x).
  { induction j; intros; simpl; [lia | rewrite IHj, fgh_0; lia]. }
  rewrite H. lia.
Qed.

Lemma fgh_arrow_ge : forall k n, 1 <= n -> arrow k 2 n <= fgh (S k) n.
Proof.
  induction k as [| k IH]; intros n Hn.
  - rewrite fgh1, (arrow_0 2 n). lia.
  - rewrite fgh_S, arrow_S_iter.
    assert (Hj : forall j, iter j (arrow k 2) n <= iter j (fgh (S k)) n).
    { induction j as [| j IHj]; [simpl; lia |]. cbn [iter].
      pose proof (iter_ge (fgh (S k)) (fgh_ge (S k)) j n).
      pose proof (arrow_mono k _ _ IHj). pose proof (IH (iter j (fgh (S k)) n) ltac:(lia)). lia. }
    specialize (Hj n). pose proof (arrow_iter_mono k n 1 n Hn). lia.
Qed.

Lemma arrow_strict : forall k y z, y < z -> arrow k 2 y < arrow k 2 z.
Proof.
  intros k y z Hyz. destruct k as [| k].
  - rewrite (arrow_0 2 y), (arrow_0 2 z). lia.
  - pose proof (arrow_step2 k y) as H1. pose proof (arrow_S_ge k y) as H2.
    pose proof (arrow_mono (S k) (S y) z Hyz). lia.
Qed.

Lemma graham_lt : forall j, graham_g j < iter j f_omega 64.
Proof.
  induction j as [| j IH]; [simpl; lia |].
  change (graham_g (S j)) with (up3 (graham_g j) 3). cbn [iter].
  set (x := iter j f_omega 64) in *.
  pose proof (iter_fo_ge j 64) as Hx. fold x in Hx.
  pose proof (up3_le (graham_g j) 3) as H1. change (2 * 3) with 6 in H1.
  pose proof (arrow_lvl_le (graham_g j) (x - 1) 6 ltac:(lia) ltac:(lia)) as H2.
  pose proof (arrow_strict (x - 1) 6 x ltac:(lia)) as H3.
  pose proof (fgh_arrow_ge (x - 1) x ltac:(lia)) as H4. replace (S (x - 1)) with x in H4 by lia.
  unfold f_omega. lia.
Qed.

Theorem graham_lt_f_omega1_64 : Graham < f_omega1 64.
Proof. unfold Graham. rewrite f_omega1_iter. apply graham_lt. Qed.

Theorem beats_graham : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ Graham < N.
Proof.
  destruct fgh_lower_64 as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  pose proof graham_lt_f_omega1_64. lia.
Qed.

(** ** Upper bound: n1 stays below f_(omega+1)(6 T) *)

Lemma fgh_mono_n : forall k x y, x <= y -> fgh k x <= fgh k y.
Proof.
  induction k as [| k IH]; intros x y Hxy; [rewrite (fgh_0 x), (fgh_0 y); lia |].
  rewrite !fgh_S.
  pose proof (iter_mono_x (fgh k) (IH) x x y Hxy).
  pose proof (iter_mono_n (fgh k) (fgh_ge k) x y y Hxy). lia.
Qed.

Lemma fgh_lvl1 : forall k n, 1 <= n -> fgh k n <= fgh (S k) n.
Proof.
  intros k n Hn. rewrite fgh_S.
  pose proof (iter_mono_n (fgh k) (fgh_ge k) 1 n n Hn). cbn [iter] in H. lia.
Qed.

Lemma fgh_lvl : forall k K n, k <= K -> 1 <= n -> fgh k n <= fgh K n.
Proof. intros k K n HkK Hn. induction HkK; [lia |]. pose proof (fgh_lvl1 m n Hn). lia. Qed.

Lemma fgh2 : forall y, fgh 2 y = 2 ^ y * y.
Proof.
  intros. rewrite fgh_S.
  assert (forall j x, iter j (fgh 1) x = 2 ^ j * x).
  { induction j; intros; cbn [iter]; [simpl; lia | rewrite IHj, fgh1, Nat.pow_succ_r'; lia]. }
  apply H.
Qed.

Lemma fo_mono : forall x y, x <= y -> f_omega x <= f_omega y.
Proof.
  intros x y Hxy. unfold f_omega. destruct y as [| y'].
  - assert (x = 0) by lia. subst. lia.
  - pose proof (fgh_mono_n x x (S y') Hxy). pose proof (fgh_lvl x (S y') (S y') Hxy ltac:(lia)). lia.
Qed.

Lemma fo_4 : forall y, 2 <= y -> 4 * y <= f_omega y.
Proof.
  intros y Hy. unfold f_omega. pose proof (fgh_lvl 2 y y Hy ltac:(lia)). rewrite fgh2 in H.
  assert (4 <= 2 ^ y) by (change 4 with (2 ^ 2); apply Nat.pow_le_mono_r; lia).
  nia.
Qed.

Lemma fo_dbl : forall y, 1 <= y -> 2 * f_omega y <= f_omega (S y).
Proof.
  intros y Hy. unfold f_omega. rewrite fgh_S.
  pose proof (iter_mono_n (fgh y) (fgh_ge y) 2 (S y) (S y) ltac:(lia)) as H1.
  change (iter 2 (fgh y) (S y)) with (fgh y (fgh y (S y))) in H1.
  pose proof (fgh_mono_n y y (S y) ltac:(lia)) as H2.
  pose proof (fgh_ge y (S y)) as H3.
  pose proof (fgh_lvl 1 y (fgh y (S y)) Hy ltac:(lia)) as H4. rewrite fgh1 in H4.
  lia.
Qed.

Lemma fo_ge1 : forall y, 1 <= y -> y <= f_omega y.
Proof. intros. apply f_omega_ge. Qed.

Lemma fo_shift : forall c y, 1 <= y -> f_omega y + c <= f_omega (y + c).
Proof.
  induction c as [| c IH]; intros y Hy; [rewrite !Nat.add_0_r; lia |].
  replace (y + S c) with (S (y + c)) by lia.
  pose proof (IH y Hy). pose proof (fo_dbl (y + c) ltac:(lia)). pose proof (f_omega_ge (y + c)). lia.
Qed.

Lemma arrow_fo : forall k z, 1 <= z -> arrow k 2 z <= f_omega (k + z + 1).
Proof.
  intros k z Hz. unfold f_omega.
  pose proof (fgh_arrow_ge k z Hz).
  pose proof (fgh_lvl (S k) (k + z + 1) z ltac:(lia) Hz).
  pose proof (fgh_mono_n (k + z + 1) z (k + z + 1) ltac:(lia)). lia.
Qed.

Lemma iterfo_mono : forall a b y z, a <= b -> y <= z -> iter a f_omega y <= iter b f_omega z.
Proof.
  intros a b y z Hab Hyz.
  pose proof (iter_mono_x f_omega fo_mono a y z Hyz).
  pose proof (iter_mono_n f_omega f_omega_ge a b z Hab). lia.
Qed.

Lemma iterfo_shift : forall a y c, 1 <= y -> iter a f_omega y + c <= iter a f_omega (y + c).
Proof.
  induction a as [| a IH]; intros y c Hy; [cbn [iter]; lia |].
  cbn [iter]. pose proof (iter_fo_ge a y).
  pose proof (fo_shift c (iter a f_omega y) ltac:(lia)).
  pose proof (fo_mono _ _ (IH y c Hy)). lia.
Qed.

(** one period at most multiplies the size x = 2 (n + g) + 6 into f_omega^8 (x) *)
Lemma step_bound : forall n g, 3 <= n -> 3 <= g ->
  2 * (fst (step (n, g)) + snd (step (n, g))) + 6 <= iter 8 f_omega (2 * (n + g) + 6).
Proof.
  intros n g Hn Hg. unfold step. cbn [fst snd].
  remember (2 * (n + g) + 6) as x eqn:Ex.
  remember (n + 2 * g - 6) as n2 eqn:En2.
  remember (arrow n 2 5) as a1 eqn:Ea1.
  remember (arrow n2 2 5) as a2 eqn:Ea2.
  remember (arrow (S n2) 2 (a1 - 1)) as A eqn:EA.
  remember (arrow (S (n2 + 2 * A - 4)) 2 (a2 - 1)) as G eqn:EG.
  pose proof (arrow5 n) as A5. pose proof (arrow5 n2) as A5'. rewrite <- Ea1 in A5. rewrite <- Ea2 in A5'.
  pose proof (arrow_fo n 5 ltac:(lia)) as Ha1. rewrite <- Ea1 in Ha1.
  pose proof (fo_mono (n + 5 + 1) x ltac:(lia)) as Ha1'.
  pose proof (fo_4 x ltac:(lia)) as Fx. pose proof (fo_dbl x ltac:(lia)) as D1. pose proof (fo_dbl (S x) ltac:(lia)) as D2.
  pose proof (arrow_fo (S n2) (a1 - 1) ltac:(lia)) as HA. rewrite <- EA in HA.
  pose proof (fo_mono (S n2 + (a1 - 1) + 1) (f_omega (S (S x))) ltac:(lia)) as HA'.
  remember (f_omega (f_omega (S (S x)))) as Y eqn:EY.
  pose proof (fo_4 (S (S x)) ltac:(lia)) as Fx2.
  pose proof (fo_ge1 (f_omega (S (S x))) ltac:(lia)) as GY. rewrite <- EY in GY.
  pose proof (arrow_fo n2 5 ltac:(lia)) as Ha2. rewrite <- Ea2 in Ha2.
  pose proof (fo_mono (n2 + 5 + 1) (f_omega (S (S x))) ltac:(lia)) as Ha2'.
  pose proof (arrow_fo (S (n2 + 2 * A - 4)) (a2 - 1) ltac:(lia)) as HG. rewrite <- EG in HG.
  pose proof (fo_4 Y ltac:(lia)) as FY. pose proof (fo_dbl Y ltac:(lia)) as DY.
  pose proof (fo_mono (S (n2 + 2 * A - 4) + (a2 - 1) + 1) (f_omega (S Y)) ltac:(lia)) as HG'.
  remember (f_omega (f_omega (S Y))) as Z eqn:EZ.
  pose proof (fo_ge1 (f_omega (S Y)) ltac:(lia)) as GZ. rewrite <- EZ in GZ. pose proof (fo_4 (S Y) ltac:(lia)) as FSY.
  pose proof (fo_4 Z ltac:(lia)) as FZ. pose proof (fo_dbl Z ltac:(lia)) as DZ. pose proof (fo_dbl (S Z) ltac:(lia)) as DZ2.
  assert (Step1 : 2 * (n2 + 2 * A - 4 + G) + 6 <= f_omega (S (S Z))) by lia.
  assert (C1 : S Y <= f_omega Y) by lia.
  assert (C2 : Z <= iter 3 f_omega Y).
  { rewrite EZ. cbn [iter]. apply fo_mono, fo_mono. exact C1. }
  assert (C3 : S (S Z) <= f_omega Z) by lia.
  assert (C4 : f_omega (S (S Z)) <= iter 5 f_omega Y).
  { pose proof (fo_mono _ _ C3). pose proof (fo_mono _ _ (fo_mono _ _ C2)).
    change (iter 5 f_omega Y) with (f_omega (f_omega (iter 3 f_omega Y))). lia. }
  assert (C5 : iter 5 f_omega Y = iter 7 f_omega (S (S x))) by (rewrite EY; reflexivity).
  assert (C6 : S (S x) <= f_omega x) by lia.
  pose proof (iterfo_mono 7 7 (S (S x)) (f_omega x) (le_n _) C6) as C7.
  change (iter 8 f_omega x) with (iter 7 f_omega (f_omega x)).
  lia.
Qed.

Lemma stepn_bound : forall J n g, 3 <= n -> F n <= g ->
  2 * (fst (stepn J (n, g)) + snd (stepn J (n, g))) + 6 <= iter (8 * J) f_omega (2 * (n + g) + 6).
Proof.
  induction J as [| J IH]; intros n g Hn Hg; [change (8 * 0) with 0; cbn [stepn fst snd iter]; lia |].
  pose proof (F_ge n).
  destruct (step_props n g Hn Hg) as [S1 [S2 _]].
  pose proof (step_bound n g Hn ltac:(lia)) as SB.
  destruct (step (n, g)) as [n' g'] eqn:Es. cbn [fst snd] in S1, S2, SB.
  change (stepn (S J) (n, g)) with (stepn J (step (n, g))). rewrite Es.
  pose proof (IH n' g' S1 S2) as H1.
  pose proof (iterfo_mono (8 * J) (8 * J) _ _ (le_n _) SB) as H2.
  replace (8 * S J) with (8 * J + 8) by lia. rewrite iter_add. lia.
Qed.

Lemma x0_bound : 2 * (34 + g0) + 6 <= iter 2 f_omega 43.
Proof.
  unfold g0. pose proof (arrow5 34) as A.
  pose proof (arrow_fo 34 5 ltac:(lia)) as H1. change (34 + 5 + 1) with 40 in H1.
  pose proof (arrow_fo 35 (arrow 34 2 5 - 1) ltac:(lia)) as H2.
  pose proof (fo_4 40 ltac:(lia)) as F40. pose proof (fo_dbl 40 ltac:(lia)) as D40. pose proof (fo_dbl 41 ltac:(lia)) as D41.
  pose proof (fo_dbl 42 ltac:(lia)) as D42.
  pose proof (fo_mono (35 + (arrow 34 2 5 - 1) + 1) (f_omega 42) ltac:(lia)) as H3.
  pose proof (fo_4 (f_omega 42) ltac:(lia)) as F4.
  pose proof (fo_dbl (f_omega 42) ltac:(lia)) as D4. pose proof (fo_dbl (S (f_omega 42)) ltac:(lia)) as D5.
  pose proof (fo_mono (S (S (f_omega 42))) (f_omega 43) ltac:(lia)) as H4.
  change (iter 2 f_omega 43) with (f_omega (f_omega 43)).
  revert A H1 H2 F40 D40 D41 D42 H3 F4 D4 D5 H4.
  generalize (arrow 34 2 5) (arrow 35 2 (arrow 34 2 5 - 1)) (f_omega 40) (f_omega 41) (f_omega 42) (f_omega 43)
    (f_omega (f_omega 42)) (f_omega (S (f_omega 42))) (f_omega (S (S (f_omega 42)))) (f_omega (f_omega 43)).
  intros. lia.
Qed.

Lemma final_bound : forall n g J x, 3 <= n -> F n <= g -> 142 <= J -> x = 2 * (n + g) + 6 ->
  x <= iter (8 * J) f_omega (iter 2 f_omega 43) ->
  2 * (n + 2 * g - 6) + 3 * arrow (S (n + 2 * g - 6)) 2 (arrow n 2 5) + 12 * J + 5 < iter (12 * J + 48) f_omega (12 * J + 48).
Proof.
  intros n g J x Hn Hg HJ Ex HX.
  pose proof (F_ge n) as Fn.
  remember (x + 12 * J + 5) as u eqn:Eu.
  remember (arrow n 2 5) as a eqn:Ea.
  remember (arrow (S (n + 2 * g - 6)) 2 a) as V eqn:EV.
  pose proof (arrow5 n) as A5. rewrite <- Ea in A5.
  pose proof (arrow_fo n 5 ltac:(lia)) as Ha. rewrite <- Ea in Ha.
  pose proof (fo_mono (n + 5 + 1) x ltac:(lia)) as Ha'.
  pose proof (arrow_fo (S (n + 2 * g - 6)) a ltac:(lia)) as HV. rewrite <- EV in HV.
  pose proof (fo_4 x ltac:(lia)) as Fx. pose proof (fo_dbl x ltac:(lia)) as D1. pose proof (fo_dbl (S x) ltac:(lia)) as D2.
  pose proof (fo_mono (S (S x)) (S (S u)) ltac:(lia)) as M1.
  pose proof (fo_mono (S (n + 2 * g - 6) + a + 1) (f_omega (S (S u))) ltac:(lia)) as HV'.
  remember (f_omega (f_omega (S (S u)))) as Q eqn:EQ.
  pose proof (fo_ge1 (f_omega (S (S u))) ltac:(lia)) as GQ. rewrite <- EQ in GQ. pose proof (fo_4 (S (S u)) ltac:(lia)) as F2u.
  pose proof (fo_4 Q ltac:(lia)) as FQ. pose proof (fo_dbl Q ltac:(lia)) as DQ.
  assert (N1 : 2 * (n + 2 * g - 6) + 3 * V + 12 * J + 5 < f_omega (S Q)) by lia.
  assert (N2 : f_omega (S Q) <= iter 5 f_omega u).
  { pose proof (fo_mono (S Q) (f_omega Q) ltac:(lia)) as K1.
    pose proof (fo_4 u ltac:(lia)) as K2. pose proof (iterfo_mono 4 4 (S (S u)) (f_omega u) (le_n _) ltac:(lia)) as K3.
    change (iter 5 f_omega u) with (iter 4 f_omega (f_omega u)).
    assert (K4 : iter 4 f_omega (S (S u)) = f_omega (f_omega Q)) by (rewrite EQ; reflexivity).
    lia. }
  assert (N3 : u <= iter (8 * J + 2) f_omega (12 * J + 48)).
  { pose proof (iter_fo_ge 2 43) as K0.
    pose proof (iterfo_shift (8 * J) (iter 2 f_omega 43) (12 * J + 5) ltac:(lia)) as S1.
    pose proof (iterfo_shift 2 43 (12 * J + 5) ltac:(lia)) as S2.
    pose proof (iterfo_mono (8 * J) (8 * J) _ _ (le_n _) S2) as S3.
    rewrite iter_add. replace (43 + (12 * J + 5)) with (12 * J + 48) in S3 by lia. lia. }
  pose proof (iterfo_mono 5 5 _ _ (le_n _) N3) as N4. rewrite <- iter_add in N4.
  pose proof (iterfo_mono (5 + (8 * J + 2)) (12 * J + 48) (12 * J + 48) (12 * J + 48) ltac:(lia) (le_n _)) as N5.
  lia.
Qed.

Lemma score_value_lt : score_value < f_omega1 (12 * JJ + 48).
Proof.
  destruct fin_props as [H1 [H2 _]].
  pose proof (stepn_bound JJ 34 g0 ltac:(lia) g0_ge) as SB. fold fin in SB.
  pose proof (iterfo_mono (8 * JJ) (8 * JJ) _ _ (le_n _) x0_bound) as X0.
  pose proof JJ_ge as HJ.
  rewrite f_omega1_iter. unfold score_value, Wf.
  apply (final_bound (fst fin) (snd fin) JJ (2 * (fst fin + snd fin) + 6) H1 H2 HJ eq_refl). lia.
Qed.

Lemma lower_from : forall N, iter (2 * JJ + 1) F 34 < N -> f_omega1 (JJ - 2) < N.
Proof.
  intros N H4. rewrite f_omega1_iter. pose proof JJ_ge as HJ. pose proof JJ_le_T. pose proof T_le.
  pose proof (fo_iter_le (JJ - 2) (JJ - 2) ltac:(lia)) as A1.
  replace (2 * JJ + 1) with (2 * (JJ - 2) + 5) in H4 by lia. rewrite iter_add in H4.
  pose proof (iter_big 5 ltac:(lia)) as A2. pose proof (F_ge (F (F 34))) as A3.
  pose proof (iterF_mono (2 * (JJ - 2)) (JJ - 2) (iter 5 F 34) ltac:(lia)) as A4.
  lia.
Qed.

Lemma f_omega1_mono : forall a b, a <= b -> f_omega1 a <= f_omega1 b.
Proof. intros. rewrite !f_omega1_iter. apply iterfo_mono; assumption. Qed.

(** n1 sits at level omega+1: f_(omega+1)(J - 2) < sigma - 1 < f_(omega+1)(6 T), J = (3T - 13)/7 *)
Theorem fgh_level : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  f_omega1 ((3 * arrow 37 2 3 - 13) / 7 - 2) < N /\ N < f_omega1 (6 * arrow 37 2 3).
Proof.
  destruct score_closed as [c [H1 [H2 H3]]].
  exists c, score_value. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  rewrite <- JJ_closed, <- T_def. split.
  - apply lower_from. exact score_value_gt.
  - pose proof score_value_lt. destruct JJ_eq as [HJ _]. pose proof JJ_ge.
    pose proof (f_omega1_mono (12 * JJ + 48) (6 * T) ltac:(lia)). lia.
Qed.

End N1.

(* ==================================================================================================== *)
(** * Main results, stated with one [ones] predicate for the three machines *)

Set Default Goal Selector "!".
Local Open Scope nat_scope.

(** Knuth's up-arrow and iteration, exactly the definitions of module N1 (abbreviations, not copies):
      arrow 0 a b = a * b,   arrow (S k) a b = (arrow k a)^b (1)   (so arrow 1 2 x = 2^x, arrow k 2 3 = 2 ^(k arrows) 3);
      iter 0 g x = x,        iter (S n) g x = g (iter n g x). *)
Notation arrow := N1.arrow.
Notation iter := N1.iter.

(** [ones c N]: the tape of c is  Ls (reversed, left of the head), s (head cell), Rs (right of the head), with 0s
    beyond both lists, and N = the number of 1s in Ls, s and Rs. *)
Definition sym_val (s : Sym) : nat :=
  match s with
  | S0 => 0
  | S1 => 1
  end.

Fixpoint count1 (xs : list Sym) : nat :=
  match xs with
  | [] => 0
  | x :: t => sym_val x + count1 t
  end.

Definition ones (c : state * tape) (N : nat) : Prop :=
  exists (q : state) (Ls Rs : list Sym) (s : Sym),
    c = (q, (Ls *> const S0, s, Rs *> const S0)) /\ N = count1 Ls + sym_val s + count1 Rs.

(** The [ones] of the three developments (with their [count1], [sym_val]) are copies of it: convertible. *)
Lemma ones_N1 : forall c N, N1.ones c N <-> ones c N.
Proof. intros c N. split; intros Hc; exact Hc. Qed.

Lemma ones_Champion10 : forall c N, Champion10.ones c N <-> ones c N.
Proof. intros c N. split; intros Hc; exact Hc. Qed.

Lemma ones_Lead10 : forall c N, Lead10.ones c N <-> ones c N.
Proof. intros c N. split; intros Hc; exact Hc. Qed.

(** n1 halts from the blank tape. *)
Theorem n1_halts : halts N1.tm c0.
Proof. exact N1.halt. Qed.

(** The exact number of ones at the halt, with the bound on w in closed form
    (N1.JJ = (3 N1.T - 13) / 7, N1.T_def : N1.T = arrow 37 2 3, N1.F n = arrow n 2 4). *)
Theorem n1_score_exact : exists c f k w,
  c0 -[ N1.tm ]->* c /\ halted N1.tm c /\ ones c (2 * w + f + 3 * k + 22) /\
  iter (2 * ((3 * arrow 37 2 3 - 13) / 7) + 1) (fun n => arrow n 2 4) 34 <= w.
Proof.
  destruct N1.score_exact as (c & f & k & w & H1 & H2 & H3 & H4).
  unfold N1.JJ in H4. rewrite N1.T_def in H4.
  replace N1.F with (fun n => arrow n 2 4) in H4 by reflexivity.
  exists c, f, k, w.
  split; [exact H1 | split; [exact H2 | split; [exact (proj1 (ones_N1 _ _) H3) | exact H4]]].
Qed.

(** The verifier's lower bound G^((6T-19)/7) (33), with G x = 2 ^(x+1 arrows) 3 and T = 2 ^(37 arrows) 3. *)
Theorem n1_sigma_lower_bound : exists c N,
  c0 -[ N1.tm ]->* c /\ halted N1.tm c /\ ones c N /\
  iter ((6 * arrow 37 2 3 - 19) / 7) (fun x => arrow (x + 1) 2 3) 33 < N.
Proof.
  destruct N1.sigma_lower_bound as (c & N & H1 & H2 & H3 & H4).
  exists c, N.
  split; [exact H1 | split; [exact H2 | split; [exact (proj1 (ones_N1 _ _) H3) | exact H4]]].
Qed.

(** n1 exceeds the proved lower bound of the 10-state candidate M3 (a lower bound only, not M3's score). *)
Theorem n1_beats_M3_bound : exists c N,
  c0 -[ N1.tm ]->* c /\ halted N1.tm c /\ ones c N /\
  arrow (4 * arrow 37 2 3 + 41) 2 (arrow (4 * arrow 37 2 3 + 39) 2 (arrow (4 * arrow 37 2 3 + 35) 2 5)) < N.
Proof.
  destruct N1.beats_M3_bound as (c & N & H1 & H2 & H3 & H4).
  exists c, N.
  split; [exact H1 | split; [exact H2 | split; [exact (proj1 (ones_N1 _ _) H3) | exact H4]]].
Qed.

(** The BB(10) champion halts with Nc ones (score Nc + 1: E0 = 1RZ writes a 1 on a 0); n1 halts with No ones
    (score No + 1: the undefined J0 is read on a 0); Nc + 1 < No + 1.  Champion10.score_exact gives Nc exactly. *)
Theorem n1_beats_champion : exists cc Nc co No,
  c0 -[ Champion10.tm ]->* cc /\ halted Champion10.tm cc /\ ones cc Nc /\
  c0 -[ N1.tm ]->* co /\ halted N1.tm co /\ ones co No /\
  Nc + 1 < No + 1.
Proof.
  destruct N1.beats_champion as (cc & Nc & co & No & H1 & H2 & H3 & H4 & H5 & H6 & H7).
  exists cc, Nc, co, No.
  split; [exact H1 | split; [exact H2 | split; [exact (proj1 (ones_Champion10 _ _) H3) |]]].
  split; [exact H4 | split; [exact H5 | split; [exact (proj1 (ones_N1 _ _) H6) | exact H7]]].
Qed.

(** The same against the 10-state candidate 0LJ0LC (score Nl + 1: the undefined J0 is read on a 0). *)
Theorem n1_beats_lead : exists cl Nl co No,
  c0 -[ Lead10.tm ]->* cl /\ halted Lead10.tm cl /\ ones cl Nl /\
  c0 -[ N1.tm ]->* co /\ halted N1.tm co /\ ones co No /\
  Nl + 1 < No + 1.
Proof.
  destruct N1.beats_lead as (cl & Nl & co & No & H1 & H2 & H3 & H4 & H5 & H6 & H7).
  exists cl, Nl, co, No.
  split; [exact H1 | split; [exact H2 | split; [exact (proj1 (ones_Lead10 _ _) H3) |]]].
  split; [exact H4 | split; [exact H5 | split; [exact (proj1 (ones_N1 _ _) H6) | exact H7]]].
Qed.

(** The fast-growing hierarchy and Graham's number, exactly the definitions of module N1 (BB10_n1_fgh.v):
      fgh 0 n = n + 1,  fgh (k+1) n = (fgh k)^n (n),  f_omega n = fgh n n,  f_omega1 n = f_omega^n (n);
      up3 0 n = 3 * n,  up3 (k+1) n = (up3 k)^n (1)   (up3 k n = 3 ^(k arrows) n),
      graham_g 0 = 4,  graham_g (k+1) = up3 (graham_g k) 3,  Graham = graham_g 64. *)
Notation f_omega1 := N1.f_omega1.
Notation Graham := N1.Graham.

(** n1 sits at level omega+1 of the fast-growing hierarchy:
    f_(omega+1) ((3T - 13)/7 - 2) < N < f_(omega+1) (6T),  T = 2 ^(37 arrows) 3, for the exact count N. *)
Theorem n1_fgh_level : exists c N,
  c0 -[ N1.tm ]->* c /\ halted N1.tm c /\ ones c N /\
  f_omega1 ((3 * arrow 37 2 3 - 13) / 7 - 2) < N /\ N < f_omega1 (6 * arrow 37 2 3).
Proof.
  destruct N1.fgh_level as (c & N & H1 & H2 & H3 & H4).
  exists c, N.
  split; [exact H1 | split; [exact H2 | split; [exact (proj1 (ones_N1 _ _) H3) | exact H4]]].
Qed.

Theorem n1_fgh_lower_64 : exists c N,
  c0 -[ N1.tm ]->* c /\ halted N1.tm c /\ ones c N /\ f_omega1 64 < N.
Proof.
  destruct N1.fgh_lower_64 as (c & N & H1 & H2 & H3 & H4).
  exists c, N.
  split; [exact H1 | split; [exact H2 | split; [exact (proj1 (ones_N1 _ _) H3) | exact H4]]].
Qed.

Theorem graham_lt_f_omega1_64 : Graham < f_omega1 64.
Proof. exact N1.graham_lt_f_omega1_64. Qed.

(** n1 leaves more than Graham's number of ones. *)
Theorem n1_beats_graham : exists c N,
  c0 -[ N1.tm ]->* c /\ halted N1.tm c /\ ones c N /\ Graham < N.
Proof.
  destruct N1.beats_graham as (c & N & H1 & H2 & H3 & H4).
  exists c, N.
  split; [exact H1 | split; [exact H2 | split; [exact (proj1 (ones_N1 _ _) H3) | exact H4]]].
Qed.

(** ** No axioms *)
Print Assumptions Champion10.halt.
Print Assumptions Champion10.score_exact.
Print Assumptions Lead10.halt.
Print Assumptions Lead10.score_exact.
Print Assumptions Lead10.candidate_beats_champion.
Print Assumptions N1.halt.
Print Assumptions N1.score_exact.
Print Assumptions N1.sigma_lower_bound.
Print Assumptions N1.dominates.
Print Assumptions N1.beats_M3_bound.
Print Assumptions N1.beats_lead.
Print Assumptions N1.beats_champion.
Print Assumptions N1.score_closed_unfolded.
Print Assumptions N1.score_value_gt.
Print Assumptions N1.fgh_level.
Print Assumptions N1.fgh_lower_64.
Print Assumptions N1.graham_lt_f_omega1_64.
Print Assumptions N1.beats_graham.
Print Assumptions n1_halts.
Print Assumptions n1_score_exact.
Print Assumptions n1_sigma_lower_bound.
Print Assumptions n1_beats_M3_bound.
Print Assumptions n1_beats_champion.
Print Assumptions n1_beats_lead.
Print Assumptions n1_fgh_level.
Print Assumptions n1_fgh_lower_64.
Print Assumptions graham_lt_f_omega1_64.
Print Assumptions n1_beats_graham.
