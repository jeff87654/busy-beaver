(** * L1_R3s: the axiom texts built by the zf-axtext R3s336 machine (zf/axtext/search/cand/R3s336.json,
    clause table R3s336.enum.txt) are interderivable with the axioms of this directory's Logic.v
    using pure logic ([lprov], no ZF axioms).  Same method as zf/v354/coq/L1_B354.v.

    R3s336 changes three axiom texts (forms.py flips / vmap):
      EXT  variables v0 -> v2, v2 -> v0 (including the FREE variable v0); final equality v1 = v2;
      REP  inner conjunctions swapped (A. v1 ph /\ v3 e. v0) and the biconditional's halves swapped;
      INF  bound variables v1 <-> v2 renamed, both conjunctions swapped and the singleton's
           biconditional halves swapped (equality v0 = v2, i.e. the original orientation).
    For EXT the free variable changes, so the statements are about the universal closures:
      lprov (A. v0 EXT -> EXT_M)   and   lprov (A. v2 EXT_M -> EXT). *)
From Coq Require Import Arith.Arith Lia Lists.List Bool.Bool.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta.
Import ListNotations.

Definition EXT_M : wff :=
  Wim (Wal v0 (Wa (Wim (Wel v0 v2) (Wel v0 v1)) (Wim (Wel v0 v1) (Wel v0 v2)))) (Weq v1 v2).
Definition REP_M (ph : wff) : wff :=
  Wim (Wal v3 (Wex v1 (Wal v2 (Wim (Wal v1 ph) (Wim (Wn (Wal v0 (Wim (Wel v0 v2) (Wel v0 v1)))) (Wel v2 v1))))))
      (Wex v1 (Wal v2 (Wa (Wim (Wex v3 (Wa (Wal v1 ph) (Wel v3 v0))) (Wel v2 v1))
                          (Wim (Wel v2 v1) (Wex v3 (Wa (Wal v1 ph) (Wel v3 v0))))))).
Definition INF_M : wff :=
  Wex v2 (Wa (Wal v0 (Wim (Wel v0 v2)
                          (Wex v1 (Wa (Wal v2 (Wa (Wim (Weq v0 v2) (Wel v2 v1))
                                                  (Wim (Wel v2 v1) (Weq v0 v2))))
                                      (Wel v1 v2)))))
             (Wel v0 v2)).

(** The numeric clauses of R3s336.enum.txt (copied literally) are the codes of these wffs. *)
Section R3sClauses.
Let c0 := 0. Let c1 := 1. Let c2 := 2. Let c3 := 3.
Definition r3s_clause_13 (p1 p2 p3 : nat) : nat := (wim (wal c0 (wa (wim (wel c0 c2) (wel c0 c1)) (wim (wel c0 c1) (wel c0 c2)))) (weq c1 c2)).
Definition r3s_clause_14 (p1 p2 p3 : nat) : nat := (wim (wal c3 (wex c1 (wal c2 (wim (wal c1 p2) (wim (wn (wal c0 (wim (wel c0 c2) (wel c0 c1)))) (wel c2 c1)))))) (wex c1 (wal c2 (wa (wim (wex c3 (wa (wal c1 p2) (wel c3 c0))) (wel c2 c1)) (wim (wel c2 c1) (wex c3 (wa (wal c1 p2) (wel c3 c0)))))))).
Definition r3s_clause_15 (p1 p2 p3 : nat) : nat := (wex c2 (wa (wal c0 (wim (wel c0 c2) (wex c1 (wa (wal c2 (wa (wim (weq c0 c2) (wel c2 c1)) (wim (wel c2 c1) (weq c0 c2)))) (wel c1 c2))))) (wel c0 c2))).
End R3sClauses.

Section Codes.
Local Opaque pair.
Lemma code_EXT_M p1 p2 p3 : code EXT_M = r3s_clause_13 p1 p2 p3.
Proof. reflexivity. Qed.
Lemma code_REP_M ph p1 p3 : code (REP_M ph) = r3s_clause_14 p1 (code ph) p3.
Proof. reflexivity. Qed.
Lemma code_INF_M p1 p2 p3 : code INF_M = r3s_clause_15 p1 p2 p3.
Proof. reflexivity. Qed.
End Codes.

(** ** Alpha-equivalence search (as in L1_B354.v) *)
Lemma ae_al_alpha x y a c : ae a (ren y x c) -> x <> y -> bnd x (ren y x c) = false ->
  occ y (ren y x c) = false -> ren x y (ren y x c) = c -> ae (Wal x a) (Wal y c).
Proof. intros H1 H2 H3 H4 H5. eapply ae_trans; [apply ae_al, H1 | now apply ae_alpha]. Qed.

Ltac aes :=
  first
  [ apply ae_refl
  | apply ae_eqsym
  | apply ae_andcomm
  | apply ae_im; aes
  | apply ae_n; aes
  | apply ae_al; aes
  | match goal with
    | |- ae (Wal ?x _) (Wal ?y _) =>
        apply (ae_al_alpha x y); [simpl; unfold rv; simpl; aes | cbv [v0 v1 v2 v3]; lia | reflexivity | reflexivity | reflexivity]
    end
  | eapply ae_trans; [apply ae_andcomm | apply ae_n; aes] ].

Lemma ae_REP ph : ae (REP ph) (REP_M ph).
Proof. unfold REP, REP_M. apply ae_im; [apply ae_refl | aes]. Qed.

(* INF with all bound variables renamed apart (v4..v7); v0 stays free *)
Definition INF_c : wff :=
  Wex 4 (Wa (Wel 0 4) (Wal 5 (Wim (Wel 5 4) (Wex 6 (Wa (Wel 6 4)
    (Wal 7 (Wa (Wim (Wel 7 6) (Weq 7 5)) (Wim (Weq 7 5) (Wel 7 6))))))))).

Lemma ae_INF : ae INF INF_M.
Proof.
  apply (ae_trans _ INF_c); [unfold INF, INF_c; aes|].
  apply ae_sym. unfold INF_M, INF_c. aes.
Qed.

(* EXT with its bound variable renamed apart (v4); v0, v1 stay free *)
Definition EXT_c : wff :=
  Wim (Wal 4 (Wa (Wim (Wel 4 0) (Wel 4 1)) (Wim (Wel 4 1) (Wel 4 0)))) (Weq 0 1).

Lemma ae_EXT : ae EXT EXT_c.
Proof. unfold EXT, EXT_c. aes. Qed.

Lemma ae_EXT_M : ae EXT_M (ren 0 2 EXT_c).
Proof. unfold EXT_c. simpl. unfold rv. simpl. unfold EXT_M. aes. Qed.

(** ** Interderivability *)
Theorem R3s_EXT : lprov (Wim (Wal v0 EXT) EXT_M) /\ lprov (Wim (Wal v2 EXT_M) EXT).
Proof.
  destruct (ae_sound _ _ ae_EXT) as [I1 I2]. destruct (ae_sound _ _ ae_EXT_M) as [J1 J2].
  split.
  - refine (lsyl _ _ _ (lal v0 _ _ I1) (lsyl _ _ _ (lspec 0 2 EXT_c ltac:(lia) eq_refl eq_refl) J2)).
  - refine (lsyl _ _ _ (lal v2 _ _ J1) (lsyl _ _ _ (lspec 2 0 (ren 0 2 EXT_c) ltac:(lia) eq_refl eq_refl) _)).
    change (ren 2 0 (ren 0 2 EXT_c)) with EXT_c. exact I2.
Qed.

Theorem R3s_REP ph : lprov (Wim (REP ph) (REP_M ph)) /\ lprov (Wim (REP_M ph) (REP ph)).
Proof. exact (ae_sound _ _ (ae_REP ph)). Qed.

Theorem R3s_INF : lprov (Wim INF INF_M) /\ lprov (Wim INF_M INF).
Proof. exact (ae_sound _ _ ae_INF). Qed.

(** Consequences for [prov]: the machine's axiom texts are theorems, and conversely. *)
Corollary prov_EXT_M : prov EXT_M.
Proof. exact (DET _ _ (lprov_prov _ (proj1 R3s_EXT)) (GEN v0 _ AX_EXT)). Qed.
Corollary prov_REP_M ph : prov (REP_M ph).
Proof. exact (DET _ _ (lprov_prov _ (proj1 (R3s_REP ph))) (AX_REP ph)). Qed.
Corollary prov_INF_M : prov INF_M.
Proof. exact (DET _ _ (lprov_prov _ (proj1 R3s_INF)) AX_INF). Qed.

Print Assumptions R3s_EXT.
Print Assumptions R3s_REP.
Print Assumptions R3s_INF.
