(** * L1_B354: the axiom texts of zf-reduce's B354 candidate (zf/reduce/cand/B354.enum.txt) are
    interderivable with the originals of Logic.v using pure logic ([lprov], no ZF axioms).

    B354 changes three axioms (forms.py flips / vmap):
      EXT  final equality written v1 = v0;
      REP  inner equality written v1 = v2, and the biconditional's two halves swapped;
      INF  variables renamed v0 -> v1, v1 -> v2, v2 -> v0 (including the FREE variable v0), the
           inner conjunction swapped and the equality written v1 = v2.
    For INF the free variable changes, so the statements are about the universal closures:
      lprov (A. v0 INF -> INF_B)   and   lprov (A. v1 INF_B -> INF). *)
From Coq Require Import Arith.Arith Lia Lists.List Bool.Bool.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta.
Import ListNotations.

Definition EXT_B : wff :=
  Wim (Wal v2 (Wa (Wim (Wel v2 v0) (Wel v2 v1)) (Wim (Wel v2 v1) (Wel v2 v0)))) (Weq v1 v0).
Definition REP_B (ph : wff) : wff :=
  Wim (Wal v3 (Wex v1 (Wal v2 (Wim (Wal v1 ph) (Weq v1 v2)))))
      (Wex v1 (Wal v2 (Wa (Wim (Wex v3 (Wa (Wel v3 v0) (Wal v1 ph))) (Wel v2 v1))
                          (Wim (Wel v2 v1) (Wex v3 (Wa (Wel v3 v0) (Wal v1 ph))))))).
Definition INF_B : wff :=
  Wex v2 (Wa (Wel v1 v2)
             (Wal v1 (Wim (Wel v1 v2)
                          (Wex v0 (Wa (Wal v2 (Wa (Wim (Wel v2 v0) (Weq v1 v2))
                                                  (Wim (Weq v1 v2) (Wel v2 v0))))
                                      (Wel v0 v2)))))).

(** The numeric clauses of B354.enum.txt (copied literally) are the codes of these wffs. *)
Section B354Clauses.
Let c0 := 0. Let c1 := 1. Let c2 := 2. Let c3 := 3.
Definition b354_clause_13 (p1 p2 p3 : nat) : nat := (wim (wal c2 (wa (wim (wel c2 c0) (wel c2 c1)) (wim (wel c2 c1) (wel c2 c0)))) (weq c1 c0)).
Definition b354_clause_14 (p1 p2 p3 : nat) : nat := (wim (wal c3 (wex c1 (wal c2 (wim (wal c1 p2) (weq c1 c2))))) (wex c1 (wal c2 (wa (wim (wex c3 (wa (wel c3 c0) (wal c1 p2))) (wel c2 c1)) (wim (wel c2 c1) (wex c3 (wa (wel c3 c0) (wal c1 p2)))))))).
Definition b354_clause_17 (p1 p2 p3 : nat) : nat := (wex c2 (wa (wel c1 c2) (wal c1 (wim (wel c1 c2) (wex c0 (wa (wal c2 (wa (wim (wel c2 c0) (weq c1 c2)) (wim (weq c1 c2) (wel c2 c0)))) (wel c0 c2))))))).
End B354Clauses.

Section Codes.
Local Opaque pair.
Lemma code_EXT_B p1 p2 p3 : code EXT_B = b354_clause_13 p1 p2 p3.
Proof. reflexivity. Qed.
Lemma code_REP_B ph p1 p3 : code (REP_B ph) = b354_clause_14 p1 (code ph) p3.
Proof. reflexivity. Qed.
Lemma code_INF_B p1 p2 p3 : code INF_B = b354_clause_17 p1 p2 p3.
Proof. reflexivity. Qed.
End Codes.

(** ** Alpha-equivalence search *)
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

Lemma ae_EXT : ae EXT EXT_B.
Proof. unfold EXT, EXT_B. aes. Qed.

Lemma ae_REP ph : ae (REP ph) (REP_B ph).
Proof. unfold REP, REP_B. aes. Qed.

(* INF with all bound variables renamed apart (v4..v7); v0 stays free *)
Definition INF_c : wff :=
  Wex 4 (Wa (Wel 0 4) (Wal 5 (Wim (Wel 5 4) (Wex 6 (Wa (Wel 6 4)
    (Wal 7 (Wa (Wim (Wel 7 6) (Weq 7 5)) (Wim (Weq 7 5) (Wel 7 6))))))))).

Lemma ae_INF : ae INF INF_c.
Proof. unfold INF, INF_c. aes. Qed.

Lemma ae_INF_B : ae INF_B (ren 0 1 INF_c).
Proof. unfold INF_c. simpl. unfold rv. simpl. unfold INF_B. aes. Qed.

(** ** Interderivability *)
Theorem B354_EXT : lprov (Wim EXT EXT_B) /\ lprov (Wim EXT_B EXT).
Proof. exact (ae_sound _ _ ae_EXT). Qed.

Theorem B354_REP ph : lprov (Wim (REP ph) (REP_B ph)) /\ lprov (Wim (REP_B ph) (REP ph)).
Proof. exact (ae_sound _ _ (ae_REP ph)). Qed.

Theorem B354_INF : lprov (Wim (Wal v0 INF) INF_B) /\ lprov (Wim (Wal v1 INF_B) INF).
Proof.
  destruct (ae_sound _ _ ae_INF) as [I1 I2]. destruct (ae_sound _ _ ae_INF_B) as [J1 J2].
  split.
  - refine (lsyl _ _ _ (lal v0 _ _ I1) (lsyl _ _ _ (lspec 0 1 INF_c ltac:(lia) eq_refl eq_refl) J2)).
  - refine (lsyl _ _ _ (lal v1 _ _ J1) (lsyl _ _ _ (lspec 1 0 (ren 0 1 INF_c) ltac:(lia) eq_refl eq_refl) _)).
    change (ren 1 0 (ren 0 1 INF_c)) with INF_c. exact I2.
Qed.

(** Consequences for [prov]: the B354 axioms are ZF theorems. *)
Corollary prov_EXT_B : prov EXT_B.
Proof. exact (DET _ _ (lprov_prov _ (proj1 B354_EXT)) AX_EXT). Qed.
Corollary prov_REP_B ph : prov (REP_B ph).
Proof. exact (DET _ _ (lprov_prov _ (proj1 (B354_REP ph))) (AX_REP ph)). Qed.
Corollary prov_INF_B : prov INF_B.
Proof. exact (DET _ _ (lprov_prov _ (proj1 B354_INF)) (GEN v0 _ AX_INF)). Qed.

Print Assumptions B354_INF.
Print Assumptions B354_REP.
Print Assumptions B354_EXT.
