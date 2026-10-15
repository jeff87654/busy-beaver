(** Original finite PA238 Hilbert proof infrastructure.
    These certificates were discovered by an independently authored bounded
    unification search starting only from the displayed numeric R8 row.
    For B/S, mathematical target formulas were read from Jeff's CD254
    at pin c132d7eae8158cd3a9850ea3eb7251158c3dd821; detachment edges
    were independently recomputed, without parsing its Proof bodies or
    incorporating its engine or implementation. Existing notices remain.
    The kernel checks actual derivable constructors; no numeric IR premise
    or external proof/code incorporation is used. *)
From Coq Require Import List Lia.
From P238.logic Require Import Codes238 Compiler238.
Import ListNotations.
Unset Implicit Arguments.

Module NumericHilbert238.
Local Opaque P unP triangle wim wal wel weq.
Local Lemma r8_certificate_0 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) p2) (wim (wim p2 p0) (wim p3 p0))).
Proof.
  exact (Compiler238.derives_r8 p2 p3 p0 p1).
Qed.

Local Lemma r8_certificate_1 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim (wim (wim (wim p0 p1) (wim p2 p1)) (wim p1 p3)) (wim p4 (wim p1 p3))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p1 p3) p0) (wim (wim p0 p1) (wim p2 p1))) (wim (wim (wim (wim p0 p1) (wim p2 p1)) (wim p1 p3)) (wim p4 (wim p1 p3)))
    (r8_certificate_0 p1 p3 p0 p2)
    (r8_certificate_0 (wim p1 p3) p0 (wim (wim p0 p1) (wim p2 p1)) p4)).
Qed.

Local Lemma r8_certificate_2 (p0 p1 p2 p3 p4 p5 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim p1 p2)) (wim (wim p3 p1) (wim p4 p1))) (wim p5 (wim (wim p3 p1) (wim p4 p1)))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim p3 p1) (wim p4 p1)) (wim p1 p2)) (wim p0 (wim p1 p2))) (wim (wim (wim p0 (wim p1 p2)) (wim (wim p3 p1) (wim p4 p1))) (wim p5 (wim (wim p3 p1) (wim p4 p1))))
    (r8_certificate_1 p3 p1 p4 p2 p0)
    (r8_certificate_0 (wim (wim p3 p1) (wim p4 p1)) (wim p1 p2) (wim p0 (wim p1 p2)) p5)).
Qed.

Local Lemma r8_certificate_3 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim p0 (wim (wim p1 p2) (wim p2 (wim p1 p2)))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim 0 p2) (wim p1 p2)) (wim p2 (wim p1 p2))) (wim (wim p1 p2) (wim p2 (wim p1 p2)))) (wim p0 (wim (wim p1 p2) (wim p2 (wim p1 p2))))
    (r8_certificate_1 0 p2 p1 (wim p1 p2) (wim p1 p2))
    (r8_certificate_1 (wim 0 p2) (wim p1 p2) p2 (wim p2 (wim p1 p2)) p0)).
Qed.

Local Lemma r8_certificate_4 (p0 p1 : nat) :
  Compiler238.derivable (wim (wim p0 p1) (wim p1 (wim p0 p1))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) (wim (wim p0 p1) (wim p1 (wim p0 p1)))
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_3 (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) p0 p1)).
Qed.

Local Lemma r8_certificate_5 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim (wim p0 p1) (wim p1 (wim p0 p1))) p2) (wim p3 p2)).
Proof.
  exact (Compiler238.derives_mp (wim (wim p2 0) (wim (wim p0 p1) (wim p1 (wim p0 p1)))) (wim (wim (wim (wim p0 p1) (wim p1 (wim p0 p1))) p2) (wim p3 p2))
    (r8_certificate_3 (wim p2 0) p0 p1)
    (r8_certificate_0 p2 0 (wim (wim p0 p1) (wim p1 (wim p0 p1))) p3)).
Qed.

Local Lemma r8_certificate_7 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim p1 p0)) p1) (wim p2 p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim p1 p0) (wim p0 (wim p1 p0))) (wim (wim (wim p0 (wim p1 p0)) p1) (wim p2 p1))
    (r8_certificate_4 p1 p0)
    (r8_certificate_0 p1 p0 (wim p0 (wim p1 p0)) p2)).
Qed.

Local Lemma r8_certificate_12 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim p0 (wim (wim p1 p2) (wim p2 p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim 0 (wim (wim p2 p2) 0)) (wim p2 p2)) (wim (wim p1 p2) (wim p2 p2))) (wim p0 (wim (wim p1 p2) (wim p2 p2)))
    (r8_certificate_7 0 (wim p2 p2) (wim p1 p2))
    (r8_certificate_2 (wim 0 (wim (wim p2 p2) 0)) p2 p2 p1 p2 p0)).
Qed.

Local Lemma r8_certificate_14 (p0 p1 : nat) :
  Compiler238.derivable (wim (wim p0 p1) (wim p1 p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) (wim (wim p0 p1) (wim p1 p1))
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_12 (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) p0 p1)).
Qed.

Local Lemma r8_certificate_18 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p0) p1) (wim p2 p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim p1 p0) (wim p0 p0)) (wim (wim (wim p0 p0) p1) (wim p2 p1))
    (r8_certificate_14 p1 p0)
    (r8_certificate_0 p1 p0 (wim p0 p0) p2)).
Qed.

Local Lemma r8_certificate_20 (p0 p1 : nat) :
  Compiler238.derivable (wim (wim p0 p1) (wim p0 p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim 0 0) (wim 0 (wim 0 0))) p1) (wim p0 p1)) (wim (wim p0 p1) (wim p0 p1))
    (r8_certificate_5 0 0 p1 p0)
    (r8_certificate_14 (wim (wim (wim 0 0) (wim 0 (wim 0 0))) p1) (wim p0 p1))).
Qed.

Local Lemma r8_certificate_22 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) p0) (wim p2 p0)).
Proof.
  exact (Compiler238.derives_mp (wim (wim p0 p1) (wim p0 p1)) (wim (wim (wim p0 p1) p0) (wim p2 p0))
    (r8_certificate_20 p0 p1)
    (r8_certificate_0 p0 p1 (wim p0 p1) p2)).
Qed.

Local Lemma r8_certificate_24 (p0 p1 : nat) :
  Compiler238.derivable (wim p0 (wim p1 p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim p1 p1) (wim p1 p1)) (wim p0 (wim p1 p1))
    (r8_certificate_20 p1 p1)
    (r8_certificate_18 p1 (wim p1 p1) p0)).
Qed.

Local Lemma r8_certificate_25 (p0 : nat) :
  Compiler238.derivable (wim p0 p0).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) (wim p0 p0)
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_24 (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) p0)).
Qed.

Local Lemma r8_certificate_29 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim p0 (wim p1 (wim p2 p1))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p1 p1) (wim p2 p1)) (wim p1 (wim p2 p1))) (wim p0 (wim p1 (wim p2 p1)))
    (r8_certificate_18 p1 (wim p2 p1) p1)
    (r8_certificate_1 p1 p1 p2 (wim p2 p1) p0)).
Qed.

Local Lemma r8_certificate_36 (p0 p1 : nat) :
  Compiler238.derivable (wim p0 (wim p1 p0)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) (wim p0 (wim p1 p0))
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_29 (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) p0 p1)).
Qed.

Local Lemma r8_certificate_37 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim p1 p0)) p2) (wim p3 p2)).
Proof.
  exact (Compiler238.derives_mp (wim (wim p2 0) (wim p0 (wim p1 p0))) (wim (wim (wim p0 (wim p1 p0)) p2) (wim p3 p2))
    (r8_certificate_29 (wim p2 0) p0 p1)
    (r8_certificate_0 p2 0 (wim p0 (wim p1 p0)) p3)).
Qed.

Local Lemma r8_certificate_54 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) (wim p1 p2)) (wim p3 (wim p1 p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p1 p2) p1) (wim p0 p1)) (wim (wim (wim p0 p1) (wim p1 p2)) (wim p3 (wim p1 p2)))
    (r8_certificate_22 p1 p2 p0)
    (r8_certificate_0 (wim p1 p2) p1 (wim p0 p1) p3)).
Qed.

Local Lemma r8_certificate_67 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim p0 (wim (wim (wim p1 (wim p2 p3)) p2) (wim p4 p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p2 p3) (wim p1 (wim p2 p3))) (wim (wim (wim p1 (wim p2 p3)) p2) (wim p4 p2))) (wim p0 (wim (wim (wim p1 (wim p2 p3)) p2) (wim p4 p2)))
    (r8_certificate_0 p2 p3 (wim p1 (wim p2 p3)) p4)
    (r8_certificate_37 (wim p2 p3) p1 (wim (wim (wim p1 (wim p2 p3)) p2) (wim p4 p2)) p0)).
Qed.

Local Lemma r8_certificate_82 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim p1 p2)) (wim p3 p1)) (wim p4 (wim p3 p1))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p3 p1) (wim p1 p2)) (wim p0 (wim p1 p2))) (wim (wim (wim p0 (wim p1 p2)) (wim p3 p1)) (wim p4 (wim p3 p1)))
    (r8_certificate_54 p3 p1 p2 p0)
    (r8_certificate_0 (wim p3 p1) (wim p1 p2) (wim p0 (wim p1 p2)) p4)).
Qed.

Local Lemma r8_certificate_88 (p0 p1 p2 p3 p4 p5 : nat) :
  Compiler238.derivable (wim (wim (wim (wim (wim p0 (wim p1 p2)) p1) (wim p3 p1)) p4) (wim p5 p4)).
Proof.
  exact (Compiler238.derives_mp (wim (wim p4 0) (wim (wim (wim p0 (wim p1 p2)) p1) (wim p3 p1))) (wim (wim (wim (wim (wim p0 (wim p1 p2)) p1) (wim p3 p1)) p4) (wim p5 p4))
    (r8_certificate_67 (wim p4 0) p0 p1 p2 p3)
    (r8_certificate_0 p4 0 (wim (wim (wim p0 (wim p1 p2)) p1) (wim p3 p1)) p5)).
Qed.

Local Lemma r8_certificate_116 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim p0 (wim (wim (wim (wim p1 p2) p3) p2) (wim p1 p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p2 0) (wim (wim p1 p2) p3)) (wim (wim (wim (wim p1 p2) p3) p2) (wim p1 p2))) (wim p0 (wim (wim (wim (wim p1 p2) p3) p2) (wim p1 p2)))
    (r8_certificate_0 p2 0 (wim (wim p1 p2) p3) p1)
    (r8_certificate_82 (wim p2 0) (wim p1 p2) p3 (wim (wim (wim p1 p2) p3) p2) p0)).
Qed.

Local Lemma r8_certificate_120 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim (wim (wim p0 p1) p2) p1) (wim p0 p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) (wim (wim (wim (wim p0 p1) p2) p1) (wim p0 p1))
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_116 (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) p0 p1 p2)).
Qed.

Local Lemma r8_certificate_122 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) (wim (wim p0 p1) p2)) (wim p3 (wim (wim p0 p1) p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim p0 p1) p2) p1) (wim p0 p1)) (wim (wim (wim p0 p1) (wim (wim p0 p1) p2)) (wim p3 (wim (wim p0 p1) p2)))
    (r8_certificate_120 p0 p1 p2)
    (r8_certificate_0 (wim (wim p0 p1) p2) p1 (wim p0 p1) p3)).
Qed.

Local Lemma r8_certificate_168 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim p0 (wim p1 (wim (wim (wim p2 (wim p3 p4)) p3) p3))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim p2 (wim p3 p4)) p3) (wim (wim (wim p2 (wim p3 p4)) p3) p3)) (wim p1 (wim (wim (wim p2 (wim p3 p4)) p3) p3))) (wim p0 (wim p1 (wim (wim (wim p2 (wim p3 p4)) p3) p3)))
    (r8_certificate_122 (wim p2 (wim p3 p4)) p3 p3 p1)
    (r8_certificate_88 p2 p3 p4 (wim (wim p2 (wim p3 p4)) p3) (wim p1 (wim (wim (wim p2 (wim p3 p4)) p3) p3)) p0)).
Qed.

Local Lemma r8_certificate_170 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim p0 (wim (wim (wim p1 (wim p2 p3)) p2) p2)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) (wim p0 (wim (wim (wim p1 (wim p2 p3)) p2) p2))
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_168 (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) p0 p1 p2 p3)).
Qed.

Local Lemma r8_certificate_174 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim p1 p2)) p1) p1).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) (wim (wim (wim p0 (wim p1 p2)) p1) p1)
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_170 (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) p0 p1 p2)).
Qed.

Local Lemma r8_certificate_176 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim p0 (wim p1 (wim p0 p2))) (wim p3 (wim p1 (wim p0 p2)))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p1 (wim p0 p2)) p0) p0) (wim (wim p0 (wim p1 (wim p0 p2))) (wim p3 (wim p1 (wim p0 p2))))
    (r8_certificate_174 p1 p0 p2)
    (r8_certificate_0 (wim p1 (wim p0 p2)) p0 p0 p3)).
Qed.

Local Lemma r8_certificate_183 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim p0 (wim (wim p1 p2) (wim (wim (wim p2 p3) p1) p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p2 p3) p1) (wim (wim p1 p2) (wim (wim (wim p2 p3) p1) p2))) (wim p0 (wim (wim p1 p2) (wim (wim (wim p2 p3) p1) p2)))
    (r8_certificate_0 p2 p3 p1 (wim (wim p2 p3) p1))
    (r8_certificate_176 (wim (wim p2 p3) p1) (wim p1 p2) p2 p0)).
Qed.

Local Lemma r8_certificate_188 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim p0 p1) (wim (wim (wim p1 p2) p0) p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) (wim (wim p0 p1) (wim (wim (wim p1 p2) p0) p1))
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_183 (wim (wim (wim 0 0) 0) (wim (wim 0 0) (wim 0 0))) p0 p1 p2)).
Qed.

Local Lemma r8_certificate_196 (p0 p1 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) p0) p0).
Proof.
  exact (Compiler238.derives_mp (wim p0 p0) (wim (wim (wim p0 p1) p0) p0)
    (r8_certificate_25 p0)
    (r8_certificate_188 p0 p0 p1)).
Qed.

Local Lemma r8_certificate_4463 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim p1 p2)) p1) (wim p3 p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim p1 p2) (wim p0 (wim p1 p2))) (wim (wim (wim p0 (wim p1 p2)) p1) (wim p3 p1))
    (r8_certificate_36 (wim p1 p2) p0)
    (r8_certificate_0 p1 p2 (wim p0 (wim p1 p2)) p3)).
Qed.

Local Lemma r8_certificate_4464 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) (wim p2 (wim p1 p3))) (wim p4 (wim p2 (wim p1 p3)))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p2 (wim p1 p3)) p1) (wim p0 p1)) (wim (wim (wim p0 p1) (wim p2 (wim p1 p3))) (wim p4 (wim p2 (wim p1 p3))))
    (r8_certificate_4463 p2 p1 p3 p0)
    (r8_certificate_0 (wim p2 (wim p1 p3)) p1 (wim p0 p1) p4)).
Qed.

Local Lemma r8_certificate_4467 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim p0 (wim p0 p1)) (wim p2 (wim p0 p1))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 p1) p0) p0) (wim (wim p0 (wim p0 p1)) (wim p2 (wim p0 p1)))
    (r8_certificate_196 p0 p1)
    (r8_certificate_0 (wim p0 p1) p0 p0 p2)).
Qed.

Local Lemma r8_certificate_4468 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim p0 (wim (wim p1 (wim p1 p2)) (wim p1 p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim p1 (wim p1 p2)) (wim (wim p1 (wim p1 p2)) (wim p1 p2))) (wim p0 (wim (wim p1 (wim p1 p2)) (wim p1 p2)))
    (r8_certificate_4467 p1 p2 (wim p1 (wim p1 p2)))
    (r8_certificate_122 p1 (wim p1 p2) (wim p1 p2) p0)).
Qed.

Local Lemma r8_certificate_4469 (p0 p1 : nat) :
  Compiler238.derivable (wim (wim p0 (wim p0 p1)) (wim p0 p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim 0 (wim (wim (wim p0 (wim p0 p1)) (wim p0 p1)) 0)) (wim (wim p0 (wim p0 p1)) (wim p0 p1))) (wim (wim p0 (wim p0 p1)) (wim p0 p1))
    (r8_certificate_4468 (wim 0 (wim (wim (wim p0 (wim p0 p1)) (wim p0 p1)) 0)) p0 p1)
    (r8_certificate_174 0 (wim (wim p0 (wim p0 p1)) (wim p0 p1)) 0)).
Qed.

Local Lemma r8_certificate_4470 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) (wim p1 p2)) (wim p1 p2)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 p1) (wim p1 p2)) (wim (wim (wim p0 p1) (wim p1 p2)) (wim p1 p2))) (wim (wim (wim p0 p1) (wim p1 p2)) (wim p1 p2))
    (r8_certificate_54 p0 p1 p2 (wim (wim p0 p1) (wim p1 p2)))
    (r8_certificate_4469 (wim (wim p0 p1) (wim p1 p2)) (wim p1 p2))).
Qed.

Local Lemma r8_certificate_4471 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) (wim p2 p0)) (wim p3 (wim p2 p0))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p2 p0) (wim p0 p1)) (wim p0 p1)) (wim (wim (wim p0 p1) (wim p2 p0)) (wim p3 (wim p2 p0)))
    (r8_certificate_4470 p2 p0 p1)
    (r8_certificate_0 (wim p2 p0) (wim p0 p1) (wim p0 p1) p3)).
Qed.

Local Lemma r8_certificate_4472 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim p0 (wim p1 (wim p2 p0))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 (wim p1 (wim p2 p0))) (wim p2 p0)) (wim p1 (wim p2 p0))) (wim p0 (wim p1 (wim p2 p0)))
    (r8_certificate_4471 p0 (wim p1 (wim p2 p0)) p2 p1)
    (r8_certificate_120 p0 (wim p1 (wim p2 p0)) (wim p2 p0))).
Qed.

Local Lemma r8_certificate_4473 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim p1 (wim p2 p3))) p2) (wim p4 p2)).
Proof.
  exact (Compiler238.derives_mp (wim (wim p2 (wim p1 (wim p2 p3))) (wim p0 (wim p1 (wim p2 p3)))) (wim (wim (wim p0 (wim p1 (wim p2 p3))) p2) (wim p4 p2))
    (r8_certificate_176 p2 p1 p3 p0)
    (r8_certificate_0 p2 (wim p1 (wim p2 p3)) (wim p0 (wim p1 (wim p2 p3))) p4)).
Qed.

Local Lemma r8_certificate_4474 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim p1 (wim p2 p3))) p2) p2).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 (wim p1 (wim p2 p3))) p2) (wim (wim (wim p0 (wim p1 (wim p2 p3))) p2) p2)) (wim (wim (wim p0 (wim p1 (wim p2 p3))) p2) p2)
    (r8_certificate_4473 p0 p1 p2 p3 (wim (wim p0 (wim p1 (wim p2 p3))) p2))
    (r8_certificate_4469 (wim (wim p0 (wim p1 (wim p2 p3))) p2) p2)).
Qed.

Local Lemma r8_certificate_4475 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim (wim p0 (wim p1 (wim p2 (wim p0 p3)))) (wim p4 (wim p1 (wim p2 (wim p0 p3))))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p1 (wim p2 (wim p0 p3))) p0) p0) (wim (wim p0 (wim p1 (wim p2 (wim p0 p3)))) (wim p4 (wim p1 (wim p2 (wim p0 p3)))))
    (r8_certificate_4474 p1 p2 p0 p3)
    (r8_certificate_0 (wim p1 (wim p2 (wim p0 p3))) p0 p0 p4)).
Qed.

Local Lemma r8_certificate_4476 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim p0 (wim p1 (wim p2 (wim p0 p3)))) (wim p1 (wim p2 (wim p0 p3)))).
Proof.
  exact (Compiler238.derives_mp (wim (wim p0 (wim p1 (wim p2 (wim p0 p3)))) (wim (wim p0 (wim p1 (wim p2 (wim p0 p3)))) (wim p1 (wim p2 (wim p0 p3))))) (wim (wim p0 (wim p1 (wim p2 (wim p0 p3)))) (wim p1 (wim p2 (wim p0 p3))))
    (r8_certificate_4475 p0 p1 p2 p3 (wim p0 (wim p1 (wim p2 (wim p0 p3)))))
    (r8_certificate_4469 (wim p0 (wim p1 (wim p2 (wim p0 p3)))) (wim p1 (wim p2 (wim p0 p3))))).
Qed.

Local Lemma r8_certificate_4477 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim p0 (wim p1 (wim p0 p2))) (wim p1 (wim p0 p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim p0 (wim p1 (wim p0 p2))) (wim (wim p0 (wim p1 (wim p0 p2))) (wim p1 (wim p0 p2)))) (wim (wim p0 (wim p1 (wim p0 p2))) (wim p1 (wim p0 p2)))
    (r8_certificate_176 p0 p1 p2 (wim p0 (wim p1 (wim p0 p2))))
    (r8_certificate_4469 (wim p0 (wim p1 (wim p0 p2))) (wim p1 (wim p0 p2)))).
Qed.

Local Lemma r8_certificate_4478 (p0 p1 p2 p3 p4 p5 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim p1 p2)) (wim p3 (wim p2 p4))) (wim p5 (wim p3 (wim p2 p4)))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p3 (wim p2 p4)) (wim p1 p2)) (wim p0 (wim p1 p2))) (wim (wim (wim p0 (wim p1 p2)) (wim p3 (wim p2 p4))) (wim p5 (wim p3 (wim p2 p4))))
    (r8_certificate_82 p3 p2 p4 p1 p0)
    (r8_certificate_0 (wim p3 (wim p2 p4)) (wim p1 p2) (wim p0 (wim p1 p2)) p5)).
Qed.

Local Lemma r8_certificate_4479 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim p0 (wim (wim (wim p1 p2) p3) (wim p2 p3))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p3 0) (wim p1 p2)) (wim (wim (wim p1 p2) p3) (wim p2 p3))) (wim p0 (wim (wim (wim p1 p2) p3) (wim p2 p3)))
    (r8_certificate_0 p3 0 (wim p1 p2) p2)
    (r8_certificate_4478 (wim p3 0) p1 p2 (wim (wim p1 p2) p3) p3 p0)).
Qed.

Local Lemma r8_certificate_4480 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) p2) (wim p1 p2)).
Proof.
  exact (Compiler238.derives_mp (wim (wim 0 (wim (wim (wim (wim p0 p1) p2) (wim p1 p2)) 0)) (wim (wim (wim p0 p1) p2) (wim p1 p2))) (wim (wim (wim p0 p1) p2) (wim p1 p2))
    (r8_certificate_4479 (wim 0 (wim (wim (wim (wim p0 p1) p2) (wim p1 p2)) 0)) p0 p1 p2)
    (r8_certificate_174 0 (wim (wim (wim p0 p1) p2) (wim p1 p2)) 0)).
Qed.

Local Lemma r8_certificate_4481 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim p0 (wim (wim p0 p1) (wim p2 p1))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p1 0) p0) (wim (wim p0 p1) (wim p2 p1))) (wim p0 (wim (wim p0 p1) (wim p2 p1)))
    (r8_certificate_0 p1 0 p0 p2)
    (r8_certificate_4480 (wim p1 0) p0 (wim (wim p0 p1) (wim p2 p1)))).
Qed.

Local Lemma r8_certificate_4482 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim (wim (wim p0 p1) (wim p2 p1)) p3) p0) (wim (wim p0 p1) (wim p2 p1))).
Proof.
  exact (Compiler238.derives_mp (wim p0 (wim (wim p0 p1) (wim p2 p1))) (wim (wim (wim (wim (wim p0 p1) (wim p2 p1)) p3) p0) (wim (wim p0 p1) (wim p2 p1)))
    (r8_certificate_4481 p0 p1 p2)
    (r8_certificate_188 p0 (wim (wim p0 p1) (wim p2 p1)) p3)).
Qed.

Local Lemma r8_certificate_4483 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim (wim p0 p1) p2) (wim (wim p1 p3) p1)) (wim p0 p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p1 p3) p1) (wim p0 p1)) (wim (wim (wim (wim p0 p1) p2) (wim (wim p1 p3) p1)) (wim p0 p1))
    (r8_certificate_22 p1 p3 p0)
    (r8_certificate_188 (wim (wim p1 p3) p1) (wim p0 p1) p2)).
Qed.

Local Lemma r8_certificate_4484 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim (wim (wim (wim p0 p1) p2) (wim (wim p3 (wim p1 p4)) p1)) (wim p0 p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p3 (wim p1 p4)) p1) (wim p0 p1)) (wim (wim (wim (wim p0 p1) p2) (wim (wim p3 (wim p1 p4)) p1)) (wim p0 p1))
    (r8_certificate_4463 p3 p1 p4 p0)
    (r8_certificate_188 (wim (wim p3 (wim p1 p4)) p1) (wim p0 p1) p2)).
Qed.

Local Lemma r8_certificate_4485 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim (wim (wim (wim (wim p0 p1) p2) (wim p3 p2)) p0) (wim p4 p0)).
Proof.
  exact (Compiler238.derives_mp (wim (wim p0 p1) (wim (wim (wim p0 p1) p2) (wim p3 p2))) (wim (wim (wim (wim (wim p0 p1) p2) (wim p3 p2)) p0) (wim p4 p0))
    (r8_certificate_4481 (wim p0 p1) p2 p3)
    (r8_certificate_0 p0 p1 (wim (wim (wim p0 p1) p2) (wim p3 p2)) p4)).
Qed.

Local Lemma r8_certificate_4486 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim (wim (wim p0 p1) p2) (wim p3 p2)) p0) p0).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim (wim p0 p1) p2) (wim p3 p2)) p0) (wim (wim (wim (wim (wim p0 p1) p2) (wim p3 p2)) p0) p0)) (wim (wim (wim (wim (wim p0 p1) p2) (wim p3 p2)) p0) p0)
    (r8_certificate_4485 p0 p1 p2 p3 (wim (wim (wim (wim p0 p1) p2) (wim p3 p2)) p0))
    (r8_certificate_4469 (wim (wim (wim (wim p0 p1) p2) (wim p3 p2)) p0) p0)).
Qed.

Local Lemma r8_certificate_4487 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim (wim (wim (wim (wim p0 (wim (wim p1 p2) p3)) (wim p1 p2)) p4) p2) (wim p1 p2)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim (wim (wim (wim p0 (wim (wim p1 p2) p3)) (wim p1 p2)) p4) p2) (wim p1 p2)) (wim (wim p0 (wim (wim p1 p2) p3)) (wim p1 p2))) (wim (wim p0 (wim (wim p1 p2) p3)) (wim p1 p2))) (wim (wim (wim (wim (wim p0 (wim (wim p1 p2) p3)) (wim p1 p2)) p4) p2) (wim p1 p2))
    (r8_certificate_4486 (wim (wim p0 (wim (wim p1 p2) p3)) (wim p1 p2)) p4 p2 p1)
    (r8_certificate_4484 (wim (wim (wim (wim p0 (wim (wim p1 p2) p3)) (wim p1 p2)) p4) p2) (wim p1 p2) (wim (wim p0 (wim (wim p1 p2) p3)) (wim p1 p2)) p0 p3)).
Qed.

Local Lemma r8_certificate_4488 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim (wim (wim p1 p2) p1) p3)) (wim (wim p1 p2) p1)) p1).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim (wim p0 (wim (wim (wim p1 p2) p1) p3)) (wim (wim p1 p2) p1)) p1) p1) (wim (wim p1 p2) p1)) (wim (wim (wim p0 (wim (wim (wim p1 p2) p1) p3)) (wim (wim p1 p2) p1)) p1)
    (r8_certificate_4487 p0 (wim p1 p2) p1 p3 p1)
    (r8_certificate_4483 (wim (wim p0 (wim (wim (wim p1 p2) p1) p3)) (wim (wim p1 p2) p1)) p1 p1 p2)).
Qed.

Local Lemma r8_certificate_4489 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim p0 p1) (wim (wim (wim p0 p2) p0) p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim p0 p1) (wim (wim (wim p0 p2) p0) p1)) (wim (wim p0 p2) p0)) p0) (wim (wim p0 p1) (wim (wim (wim p0 p2) p0) p1))
    (r8_certificate_4488 (wim p0 p1) p0 p2 p1)
    (r8_certificate_4482 p0 p1 (wim (wim p0 p2) p0) (wim (wim p0 p2) p0))).
Qed.

Local Lemma r8_certificate_4490 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim (wim p0 (wim p1 p2)) p3) (wim p1 (wim p1 p2))) (wim p0 (wim p1 p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim p1 (wim p1 p2)) (wim p0 (wim p1 p2))) (wim (wim (wim (wim p0 (wim p1 p2)) p3) (wim p1 (wim p1 p2))) (wim p0 (wim p1 p2)))
    (r8_certificate_4467 p1 p2 p0)
    (r8_certificate_188 (wim p1 (wim p1 p2)) (wim p0 (wim p1 p2)) p3)).
Qed.

Local Lemma r8_certificate_4491 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) p0) (wim (wim p0 p2) (wim p3 p2))).
Proof.
  exact (Compiler238.derives_mp (wim p0 (wim (wim p0 p2) (wim p3 p2))) (wim (wim (wim p0 p1) p0) (wim (wim p0 p2) (wim p3 p2)))
    (r8_certificate_4481 p0 p2 p3)
    (r8_certificate_4489 p0 (wim (wim p0 p2) (wim p3 p2)) p1)).
Qed.

Local Lemma r8_certificate_4492 (p0 p1 : nat) :
  Compiler238.derivable (wim p0 (wim (wim p0 p1) p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 (wim (wim p0 p1) p1)) p0) (wim (wim p0 p1) (wim (wim p0 p1) p1))) (wim p0 (wim (wim p0 p1) p1))
    (r8_certificate_4491 p0 (wim (wim p0 p1) p1) p1 (wim p0 p1))
    (r8_certificate_4490 p0 (wim p0 p1) p1 p0)).
Qed.

Local Lemma r8_certificate_4493 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) p0) (wim (wim p0 p2) p2)).
Proof.
  exact (Compiler238.derives_mp (wim p0 (wim (wim p0 p2) p2)) (wim (wim (wim p0 p1) p0) (wim (wim p0 p2) p2))
    (r8_certificate_4492 p0 p2)
    (r8_certificate_4489 p0 (wim (wim p0 p2) p2) p1)).
Qed.

Local Lemma r8_certificate_4494 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim (wim p0 p1) p1) (wim p0 p2)) (wim p3 (wim p0 p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 p2) p0) (wim (wim p0 p1) p1)) (wim (wim (wim (wim p0 p1) p1) (wim p0 p2)) (wim p3 (wim p0 p2)))
    (r8_certificate_4493 p0 p2 p1)
    (r8_certificate_0 (wim p0 p2) p0 (wim (wim p0 p1) p1) p3)).
Qed.

Local Lemma r8_certificate_4495 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim (wim (wim p0 p1) p1) (wim p0 p2)) (wim p0 p2)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim p0 p1) p1) (wim p0 p2)) (wim (wim (wim (wim p0 p1) p1) (wim p0 p2)) (wim p0 p2))) (wim (wim (wim (wim p0 p1) p1) (wim p0 p2)) (wim p0 p2))
    (r8_certificate_4494 p0 p1 p2 (wim (wim (wim p0 p1) p1) (wim p0 p2)))
    (r8_certificate_4469 (wim (wim (wim p0 p1) p1) (wim p0 p2)) (wim p0 p2))).
Qed.

Local Lemma r8_certificate_4496 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim (wim p0 (wim p1 p2)) p3) p2) (wim p0 (wim p1 p2))).
Proof.
  exact (Compiler238.derives_mp (wim p2 (wim p0 (wim p1 p2))) (wim (wim (wim (wim p0 (wim p1 p2)) p3) p2) (wim p0 (wim p1 p2)))
    (r8_certificate_4472 p2 p0 p1)
    (r8_certificate_188 p2 (wim p0 (wim p1 p2)) p3)).
Qed.

Local Lemma r8_certificate_4497 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim p0 (wim p1 (wim (wim p0 p2) (wim p3 p2)))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 (wim p1 (wim (wim p0 p2) (wim p3 p2)))) p0) (wim (wim p0 p2) (wim p3 p2))) (wim p0 (wim p1 (wim (wim p0 p2) (wim p3 p2))))
    (r8_certificate_4491 p0 (wim p1 (wim (wim p0 p2) (wim p3 p2))) p2 p3)
    (r8_certificate_4496 p0 p1 (wim (wim p0 p2) (wim p3 p2)) p0)).
Qed.

Local Lemma r8_certificate_4498 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim p0 (wim (wim (wim (wim p0 p1) p1) p2) (wim p3 p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 p1) p1) (wim p0 (wim (wim (wim (wim p0 p1) p1) p2) (wim p3 p2)))) (wim p0 (wim (wim (wim (wim p0 p1) p1) p2) (wim p3 p2)))
    (r8_certificate_4497 (wim (wim p0 p1) p1) p0 p2 p3)
    (r8_certificate_4495 p0 p1 (wim (wim (wim (wim p0 p1) p1) p2) (wim p3 p2)))).
Qed.

Local Lemma r8_certificate_4499 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim (wim (wim p0 p1) p1) p2) (wim p0 p2)).
Proof.
  exact (Compiler238.derives_mp (wim p0 (wim (wim (wim (wim p0 p1) p1) p2) (wim p0 p2))) (wim (wim (wim (wim p0 p1) p1) p2) (wim p0 p2))
    (r8_certificate_4498 p0 p1 p2 p0)
    (r8_certificate_4477 p0 (wim (wim (wim p0 p1) p1) p2) p2)).
Qed.

Local Lemma r8_certificate_4500 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) (wim p2 (wim p1 p3))) (wim p2 (wim p1 p3))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 p1) (wim p2 (wim p1 p3))) (wim (wim (wim p0 p1) (wim p2 (wim p1 p3))) (wim p2 (wim p1 p3)))) (wim (wim (wim p0 p1) (wim p2 (wim p1 p3))) (wim p2 (wim p1 p3)))
    (r8_certificate_4464 p0 p1 p2 p3 (wim (wim p0 p1) (wim p2 (wim p1 p3))))
    (r8_certificate_4469 (wim (wim p0 p1) (wim p2 (wim p1 p3))) (wim p2 (wim p1 p3)))).
Qed.

Local Lemma r8_certificate_4501 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim p0 (wim p1 (wim (wim (wim p2 p0) p3) (wim p4 p3)))).
Proof.
  exact (Compiler238.derives_mp (wim (wim p2 p0) (wim p1 (wim (wim (wim p2 p0) p3) (wim p4 p3)))) (wim p0 (wim p1 (wim (wim (wim p2 p0) p3) (wim p4 p3))))
    (r8_certificate_4497 (wim p2 p0) p1 p3 p4)
    (r8_certificate_4480 p2 p0 (wim p1 (wim (wim (wim p2 p0) p3) (wim p4 p3))))).
Qed.

Local Lemma r8_certificate_4502 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim p0 (wim (wim (wim p1 (wim (wim p0 p2) p2)) p3) (wim p4 p3))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 p2) p2) (wim p0 (wim (wim (wim p1 (wim (wim p0 p2) p2)) p3) (wim p4 p3)))) (wim p0 (wim (wim (wim p1 (wim (wim p0 p2) p2)) p3) (wim p4 p3)))
    (r8_certificate_4501 (wim (wim p0 p2) p2) p0 p1 p3 p4)
    (r8_certificate_4495 p0 p2 (wim (wim (wim p1 (wim (wim p0 p2) p2)) p3) (wim p4 p3)))).
Qed.

Local Lemma r8_certificate_4503 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim (wim (wim p1 p2) p3) p3)) p4) (wim p2 p4)).
Proof.
  exact (Compiler238.derives_mp (wim (wim p1 p2) (wim (wim (wim p0 (wim (wim (wim p1 p2) p3) p3)) p4) (wim p2 p4))) (wim (wim (wim p0 (wim (wim (wim p1 p2) p3) p3)) p4) (wim p2 p4))
    (r8_certificate_4502 (wim p1 p2) p0 p3 p4 p2)
    (r8_certificate_4500 p1 p2 (wim (wim p0 (wim (wim (wim p1 p2) p3) p3)) p4) p4)).
Qed.

Local Lemma r8_certificate_4504 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) p2) (wim (wim (wim p3 p0) p2) p2)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim (wim p0 p1) p2) (wim (wim (wim p3 p0) p2) p2)) p1) (wim p0 p1)) (wim (wim (wim p0 p1) p2) (wim (wim (wim p3 p0) p2) p2))
    (r8_certificate_4503 (wim (wim p0 p1) p2) p3 p0 p2 p1)
    (r8_certificate_4482 (wim p0 p1) p2 (wim (wim p3 p0) p2) p1)).
Qed.

Local Lemma r8_certificate_4505 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim (wim (wim (wim p0 p1) p1) p2) p0) (wim (wim p0 p1) p1)).
Proof.
  exact (Compiler238.derives_mp (wim p0 (wim (wim p0 p1) p1)) (wim (wim (wim (wim (wim p0 p1) p1) p2) p0) (wim (wim p0 p1) p1))
    (r8_certificate_4492 p0 p1)
    (r8_certificate_188 p0 (wim (wim p0 p1) p1) p2)).
Qed.

Local Lemma r8_certificate_4506 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim (wim p0 p1) (wim p2 p0)) (wim p2 p0)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 p1) (wim p2 p0)) (wim (wim (wim p0 p1) (wim p2 p0)) (wim p2 p0))) (wim (wim (wim p0 p1) (wim p2 p0)) (wim p2 p0))
    (r8_certificate_4471 p0 p1 p2 (wim (wim p0 p1) (wim p2 p0)))
    (r8_certificate_4469 (wim (wim p0 p1) (wim p2 p0)) (wim p2 p0))).
Qed.

Local Lemma r8_certificate_4507 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim p0 (wim p1 (wim (wim p0 p2) p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 p2) p2) (wim p0 (wim p1 (wim (wim p0 p2) p2)))) (wim p0 (wim p1 (wim (wim p0 p2) p2)))
    (r8_certificate_4472 (wim (wim p0 p2) p2) p0 p1)
    (r8_certificate_4495 p0 p2 (wim p1 (wim (wim p0 p2) p2)))).
Qed.

Local Lemma r8_certificate_4508 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim p0 (wim p1 (wim (wim (wim p2 p0) p3) p3))).
Proof.
  exact (Compiler238.derives_mp (wim (wim p2 p0) (wim p1 (wim (wim (wim p2 p0) p3) p3))) (wim p0 (wim p1 (wim (wim (wim p2 p0) p3) p3)))
    (r8_certificate_4507 (wim p2 p0) p1 p3)
    (r8_certificate_4480 p2 p0 (wim p1 (wim (wim (wim p2 p0) p3) p3)))).
Qed.

Local Lemma r8_certificate_4509 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim p0 (wim (wim (wim p1 (wim (wim p0 p2) p2)) p3) p3)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 p2) p2) (wim p0 (wim (wim (wim p1 (wim (wim p0 p2) p2)) p3) p3))) (wim p0 (wim (wim (wim p1 (wim (wim p0 p2) p2)) p3) p3))
    (r8_certificate_4508 (wim (wim p0 p2) p2) p0 p1 p3)
    (r8_certificate_4495 p0 p2 (wim (wim (wim p1 (wim (wim p0 p2) p2)) p3) p3))).
Qed.

Local Lemma r8_certificate_4510 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim (wim (wim p1 p2) p3) p3)) p1) p1).
Proof.
  exact (Compiler238.derives_mp (wim (wim p1 p2) (wim (wim (wim p0 (wim (wim (wim p1 p2) p3) p3)) p1) p1)) (wim (wim (wim p0 (wim (wim (wim p1 p2) p3) p3)) p1) p1)
    (r8_certificate_4509 (wim p1 p2) p0 p3 p1)
    (r8_certificate_4506 p1 p2 (wim (wim p0 (wim (wim (wim p1 p2) p3) p3)) p1))).
Qed.

Local Lemma r8_certificate_4511 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim p0 (wim (wim (wim p0 p1) p2) p2)) (wim (wim (wim p0 p1) p2) p2)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim p0 (wim (wim (wim p0 p1) p2) p2)) (wim (wim (wim p0 p1) p2) p2)) p0) p0) (wim (wim p0 (wim (wim (wim p0 p1) p2) p2)) (wim (wim (wim p0 p1) p2) p2))
    (r8_certificate_4510 (wim p0 (wim (wim (wim p0 p1) p2) p2)) p0 p1 p2)
    (r8_certificate_4505 p0 (wim (wim (wim p0 p1) p2) p2) p0)).
Qed.

Local Lemma r8_certificate_4512 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim p1 p2)) (wim p3 p1)) (wim p3 p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 (wim p1 p2)) (wim p3 p1)) (wim (wim (wim p0 (wim p1 p2)) (wim p3 p1)) (wim p3 p1))) (wim (wim (wim p0 (wim p1 p2)) (wim p3 p1)) (wim p3 p1))
    (r8_certificate_82 p0 p1 p2 p3 (wim (wim p0 (wim p1 p2)) (wim p3 p1)))
    (r8_certificate_4469 (wim (wim p0 (wim p1 p2)) (wim p3 p1)) (wim p3 p1))).
Qed.

Local Lemma r8_certificate_4513 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim (wim (wim p1 (wim p2 p3)) p4) p4)) p2) p2).
Proof.
  exact (Compiler238.derives_mp (wim (wim p1 (wim p2 p3)) (wim (wim (wim p0 (wim (wim (wim p1 (wim p2 p3)) p4) p4)) p2) p2)) (wim (wim (wim p0 (wim (wim (wim p1 (wim p2 p3)) p4) p4)) p2) p2)
    (r8_certificate_4509 (wim p1 (wim p2 p3)) p0 p4 p2)
    (r8_certificate_4512 p1 p2 p3 (wim (wim p0 (wim (wim (wim p1 (wim p2 p3)) p4) p4)) p2))).
Qed.

Local Lemma r8_certificate_4514 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim p0 p1) (wim (wim (wim p2 (wim p0 p3)) p1) p1)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim p0 p1) (wim (wim (wim p2 (wim p0 p3)) p1) p1)) p0) p0) (wim (wim p0 p1) (wim (wim (wim p2 (wim p0 p3)) p1) p1))
    (r8_certificate_4513 (wim p0 p1) p2 p0 p3 p1)
    (r8_certificate_4482 p0 p1 (wim (wim p2 (wim p0 p3)) p1) p0)).
Qed.

Local Lemma r8_certificate_4515 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim (wim (wim p0 p1) (wim p0 p2)) p1) p1).
Proof.
  exact (Compiler238.derives_mp (wim (wim p0 p1) (wim (wim (wim (wim p0 p1) (wim p0 p2)) p1) p1)) (wim (wim (wim (wim p0 p1) (wim p0 p2)) p1) p1)
    (r8_certificate_4514 p0 p1 (wim p0 p1) p2)
    (r8_certificate_4511 (wim p0 p1) (wim p0 p2) p1)).
Qed.

Local Lemma r8_certificate_4516 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim (wim p1 p2) (wim p1 p3))) p2) p2).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim p1 p2) (wim p1 p3)) p2) p2) (wim (wim (wim p0 (wim (wim p1 p2) (wim p1 p3))) p2) p2)
    (r8_certificate_4515 p1 p2 p3)
    (r8_certificate_4504 (wim (wim p1 p2) (wim p1 p3)) p2 p2 p0)).
Qed.

Local Lemma r8_certificate_4517 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim p0 (wim p1 p2)) (wim (wim p1 p0) (wim p1 p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim p0 (wim p1 p2)) (wim (wim p1 p0) (wim p1 p2))) p0) p0) (wim (wim p0 (wim p1 p2)) (wim (wim p1 p0) (wim p1 p2)))
    (r8_certificate_4516 (wim p0 (wim p1 p2)) p1 p0 p2)
    (r8_certificate_4482 p0 (wim p1 p2) (wim p1 p0) p0)).
Qed.

Local Lemma r8_certificate_4518 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim p0 p1) (wim p0 (wim (wim p1 p2) (wim p3 p2)))).
Proof.
  exact (Compiler238.derives_mp (wim p1 (wim p0 (wim (wim p1 p2) (wim p3 p2)))) (wim (wim p0 p1) (wim p0 (wim (wim p1 p2) (wim p3 p2))))
    (r8_certificate_4497 p1 p0 p2 p3)
    (r8_certificate_4517 p1 p0 (wim (wim p1 p2) (wim p3 p2)))).
Qed.

Local Lemma r8_certificate_4519 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim p0 (wim (wim p0 p1) (wim (wim p1 p2) (wim p3 p2)))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 p1) p1) (wim (wim p0 p1) (wim (wim p1 p2) (wim p3 p2)))) (wim p0 (wim (wim p0 p1) (wim (wim p1 p2) (wim p3 p2))))
    (r8_certificate_4518 (wim p0 p1) p1 p2 p3)
    (r8_certificate_4499 p0 p1 (wim (wim p0 p1) (wim (wim p1 p2) (wim p3 p2))))).
Qed.

Local Lemma r8_certificate_4520 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim p0 p1) (wim (wim p1 p2) (wim p0 p2))).
Proof.
  exact (Compiler238.derives_mp (wim p0 (wim (wim p0 p1) (wim (wim p1 p2) (wim p0 p2)))) (wim (wim p0 p1) (wim (wim p1 p2) (wim p0 p2)))
    (r8_certificate_4519 p0 p1 p2 p0)
    (r8_certificate_4476 p0 (wim p0 p1) (wim p1 p2) p2)).
Qed.

Local Lemma r8_certificate_4526 (p0 p1 p2 p3 p4 : nat) :
  Compiler238.derivable (wim (wim (wim p0 (wim p1 p2)) p1) (wim (wim p1 p3) (wim p4 p3))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 (wim p1 p2)) p1) p1) (wim (wim (wim p0 (wim p1 p2)) p1) (wim (wim p1 p3) (wim p4 p3)))
    (r8_certificate_174 p0 p1 p2)
    (r8_certificate_4518 (wim (wim p0 (wim p1 p2)) p1) p1 p3 p4)).
Qed.

Local Lemma r8_certificate_4527 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim (wim p0 p1) (wim p2 p1)) p3) (wim p0 p3)).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim (wim (wim p0 p1) (wim p2 p1)) p3) (wim p0 p3)) p0) (wim (wim p0 p1) (wim p2 p1))) (wim (wim (wim (wim p0 p1) (wim p2 p1)) p3) (wim p0 p3))
    (r8_certificate_4526 (wim (wim (wim p0 p1) (wim p2 p1)) p3) p0 p3 p1 p2)
    (r8_certificate_4482 (wim (wim p0 p1) (wim p2 p1)) p3 p0 p0)).
Qed.

Local Lemma r8_certificate_4528 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim p0 p1) (wim p0 (wim p2 p1))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim (wim p0 p1) (wim p2 p1)) (wim p2 p1)) (wim p0 (wim p2 p1))) (wim (wim p0 p1) (wim p0 (wim p2 p1)))
    (r8_certificate_4527 p0 p1 p2 (wim p2 p1))
    (r8_certificate_4499 (wim p0 p1) (wim p2 p1) (wim p0 (wim p2 p1)))).
Qed.

Local Lemma r8_certificate_4529 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim p0 p1) (wim p2 (wim p0 (wim p3 p1)))).
Proof.
  exact (Compiler238.derives_mp (wim (wim p0 p1) (wim p0 (wim p3 p1))) (wim (wim p0 p1) (wim p2 (wim p0 (wim p3 p1))))
    (r8_certificate_4528 p0 p1 p3)
    (r8_certificate_4528 (wim p0 p1) (wim p0 (wim p3 p1)) p2)).
Qed.

Local Lemma r8_certificate_4530 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim p0 (wim p1 p2)) (wim p0 (wim p1 (wim p3 p2)))).
Proof.
  exact (Compiler238.derives_mp (wim (wim p1 p2) (wim p0 (wim p1 (wim p3 p2)))) (wim (wim p0 (wim p1 p2)) (wim p0 (wim p1 (wim p3 p2))))
    (r8_certificate_4529 p1 p2 p0 p3)
    (r8_certificate_4517 (wim p1 p2) p0 (wim p1 (wim p3 p2)))).
Qed.

Local Lemma r8_certificate_4531 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim p0 (wim (wim p0 (wim p1 p2)) (wim p1 (wim p3 p2)))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p0 (wim p1 p2)) (wim p1 p2)) (wim (wim p0 (wim p1 p2)) (wim p1 (wim p3 p2)))) (wim p0 (wim (wim p0 (wim p1 p2)) (wim p1 (wim p3 p2))))
    (r8_certificate_4530 (wim p0 (wim p1 p2)) p1 p2 p3)
    (r8_certificate_4499 p0 (wim p1 p2) (wim (wim p0 (wim p1 p2)) (wim p1 (wim p3 p2))))).
Qed.

Local Lemma r8_certificate_4532 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim p0 (wim p1 p2)) (wim p1 (wim p0 p2))).
Proof.
  exact (Compiler238.derives_mp (wim p0 (wim (wim p0 (wim p1 p2)) (wim p1 (wim p0 p2)))) (wim (wim p0 (wim p1 p2)) (wim p1 (wim p0 p2)))
    (r8_certificate_4531 p0 p1 p2 p0)
    (r8_certificate_4476 p0 (wim p0 (wim p1 p2)) p1 p2)).
Qed.

Local Lemma r8_certificate_4533 (p0 p1 p2 p3 : nat) :
  Compiler238.derivable (wim (wim (wim (wim p0 p1) (wim p2 p1)) p3) (wim (wim p2 p0) p3)).
Proof.
  exact (Compiler238.derives_mp (wim (wim p2 p0) (wim (wim p0 p1) (wim p2 p1))) (wim (wim (wim (wim p0 p1) (wim p2 p1)) p3) (wim (wim p2 p0) p3))
    (r8_certificate_4520 p2 p0 p1)
    (r8_certificate_4520 (wim p2 p0) (wim (wim p0 p1) (wim p2 p1)) p3)).
Qed.

Local Lemma r8_certificate_4534 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim p0 p1) (wim (wim p0 (wim p1 p2)) (wim p0 p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim (wim p1 p2) (wim p0 p2)) (wim (wim p0 (wim p1 p2)) (wim p0 p2))) (wim (wim p0 p1) (wim (wim p0 (wim p1 p2)) (wim p0 p2)))
    (r8_certificate_4517 (wim p1 p2) p0 p2)
    (r8_certificate_4533 p1 p2 p0 (wim (wim p0 (wim p1 p2)) (wim p0 p2)))).
Qed.

Local Lemma r8_certificate_4535 (p0 p1 p2 : nat) :
  Compiler238.derivable (wim (wim p0 (wim p1 p2)) (wim (wim p0 p1) (wim p0 p2))).
Proof.
  exact (Compiler238.derives_mp (wim (wim p0 p1) (wim (wim p0 (wim p1 p2)) (wim p0 p2))) (wim (wim p0 (wim p1 p2)) (wim (wim p0 p1) (wim p0 p2)))
    (r8_certificate_4534 p0 p1 p2)
    (r8_certificate_4532 (wim p0 p1) (wim p0 (wim p1 p2)) (wim p0 p2))).
Qed.

Theorem numeric_I (a : nat) : Compiler238.derivable (wim a a).
Proof. exact (r8_certificate_25 a). Qed.

Theorem numeric_K (a b : nat) : Compiler238.derivable (wim a (wim b a)).
Proof. exact (r8_certificate_36 a b). Qed.

Theorem numeric_P (a b : nat) : Compiler238.derivable (wim (wim (wim a b) a) a).
Proof. exact (r8_certificate_196 a b). Qed.

Theorem numeric_B (a b c : nat) :
  Compiler238.derivable (wim (wim a b) (wim (wim b c) (wim a c))).
Proof. exact (r8_certificate_4520 a b c). Qed.

Theorem numeric_S (a b c : nat) :
  Compiler238.derivable (wim (wim a (wim b c)) (wim (wim a b) (wim a c))).
Proof. exact (r8_certificate_4535 a b c). Qed.

(** Finite hypothesis derivations retain only actual closed numeric theorems
    and numeric MP. This is the intermediate proof object for the forward
    translation, rather than a semantic validity predicate. *)
Inductive numeric_context (G : list nat) : nat -> Prop :=
| numeric_assumption a : In a G -> numeric_context G a
| numeric_theorem a : Compiler238.derivable a -> numeric_context G a
| numeric_context_mp a b : numeric_context G a ->
    numeric_context G (wim a b) -> numeric_context G b.

Lemma numeric_context_weak G H a : numeric_context G a ->
  (forall b, In b G -> In b H) -> numeric_context H a.
Proof.
  intro D; induction D as [a Ha | a Hth | a b Da IHa Dab IHab]; intro Hin.
  - apply numeric_assumption, Hin; exact Ha.
  - apply numeric_theorem; exact Hth.
  - exact (numeric_context_mp H a b (IHa Hin) (IHab Hin)).
Qed.

Lemma numeric_context_cut G H a : numeric_context G a ->
  (forall b, In b G -> numeric_context H b) -> numeric_context H a.
Proof.
  intro D; induction D as [a Ha | a Hth | a b Da IHa Dab IHab]; intro Hin.
  - apply Hin; exact Ha.
  - apply numeric_theorem; exact Hth.
  - exact (numeric_context_mp H a b (IHa Hin) (IHab Hin)).
Qed.

Lemma numeric_context_closed G a : numeric_context G a ->
  (forall b, In b G -> Compiler238.derivable b) -> Compiler238.derivable a.
Proof.
  intro D; induction D as [a Ha | a Hth | a b Da IHa Dab IHab]; intro Hin.
  - apply Hin; exact Ha.
  - exact Hth.
  - exact (Compiler238.derives_mp a b (IHa Hin) (IHab Hin)).
Qed.

Lemma numeric_context_empty a : numeric_context [] a -> Compiler238.derivable a.
Proof. intro H; apply (numeric_context_closed [] a H); intros b Hb; inversion Hb. Qed.

Lemma numeric_context_lift G a h : numeric_context G a ->
  numeric_context G (wim h a).
Proof.
  intro Ha; apply (numeric_context_mp G a (wim h a) Ha).
  apply numeric_theorem, numeric_K.
Qed.

(** Actual finite deduction. The MP branch consumes the independently
    derived S certificate, without a semantic completeness premise. *)
Theorem numeric_deduction G h a : numeric_context (h :: G) a ->
  numeric_context G (wim h a).
Proof.
  intro D; induction D as [a Ha | a Hth | a b Da IHa Dab IHab].
  - destruct Ha as [<-|Ha].
    + apply numeric_theorem, numeric_I.
    + apply numeric_context_lift, numeric_assumption; exact Ha.
  - apply numeric_context_lift, numeric_theorem; exact Hth.
  - assert (HS : numeric_context G
      (wim (wim h (wim a b)) (wim (wim h a) (wim h b)))).
    { apply numeric_theorem, numeric_S. }
    pose proof (numeric_context_mp G (wim h (wim a b))
      (wim (wim h a) (wim h b)) IHab HS) as Hstep.
    exact (numeric_context_mp G (wim h a) (wim h b) IHa Hstep).
Qed.

(** Code 1 admits actual syntactic explosion from R6 and weakening.
    This direction needs no numeric IR or code interpretation. *)
Lemma numeric_context_explosion G a : numeric_context G 1 -> numeric_context G a.
Proof.
  intro HF.
  assert (HK : numeric_context G (wim 1 (wex 0 (wal 0 a)))).
  { unfold wex, wn; apply numeric_theorem.
    exact (numeric_K 1 (wal 0 (wn (wal 0 a)))). }
  pose proof (numeric_context_mp G 1 (wex 0 (wal 0 a)) HF HK) as HE.
  apply (numeric_context_mp G (wex 0 (wal 0 a)) a HE).
  apply numeric_theorem; exact (Compiler238.derives_r6 0 a).
Qed.

Theorem numeric_F a : Compiler238.derivable (wim 1 a).
Proof.
  apply numeric_context_empty, numeric_deduction, numeric_context_explosion.
  apply numeric_assumption; now left.
Qed.

Theorem numeric_DNE a : Compiler238.derivable (wim (wn (wn a)) a).
Proof.
  apply numeric_context_empty, numeric_deduction.
  apply (numeric_context_mp [wn (wn a)] (wim (wn a) a) a).
  - apply numeric_deduction, numeric_context_explosion.
    apply (numeric_context_mp (wn a :: [wn (wn a)]) (wn a) 1).
    + apply numeric_assumption; now left.
    + apply numeric_assumption; right; now left.
  - apply numeric_theorem; exact (numeric_P a 1).
Qed.

Lemma numeric_context_DNE G a : numeric_context G (wn (wn a)) -> numeric_context G a.
Proof.
  intro H; apply (numeric_context_mp G (wn (wn a)) a H).
  apply numeric_theorem, numeric_DNE.
Qed.

Lemma numeric_under_head G h a : numeric_context G a -> numeric_context (h :: G) a.
Proof.
  intro H; apply (numeric_context_weak G (h :: G) a H).
  intros b Hb; now right.
Qed.

Lemma numeric_context_apply G a b : numeric_context (a :: G) b ->
  numeric_context G a -> numeric_context G b.
Proof.
  intros D Ha; apply (numeric_context_cut (a :: G) G b D).
  intros c [<-|Hc]; [exact Ha|apply numeric_assumption; exact Hc].
Qed.

Lemma numeric_conjunction_intro G a b : numeric_context G a -> numeric_context G b ->
  numeric_context G (wa a b).
Proof.
  intros Ha Hb; unfold wa; apply numeric_deduction.
  apply (numeric_context_mp ((wim a (wn b)) :: G) b 1).
  - apply numeric_under_head; exact Hb.
  - apply (numeric_context_mp ((wim a (wn b)) :: G) a (wn b)).
    + apply numeric_under_head; exact Ha.
    + apply numeric_assumption; now left.
Qed.

Lemma numeric_conjunction_left G a b : numeric_context G (wa a b) -> numeric_context G a.
Proof.
  intro H; apply numeric_context_DNE, numeric_deduction.
  apply (numeric_context_mp ((wn a) :: G) (wim a (wn b)) 1).
  - apply numeric_deduction, numeric_context_explosion.
    apply (numeric_context_mp (a :: (wn a) :: G) a 1).
    + apply numeric_assumption; now left.
    + apply numeric_assumption; right; now left.
  - apply numeric_under_head; exact H.
Qed.

Lemma numeric_conjunction_right G a b : numeric_context G (wa a b) -> numeric_context G b.
Proof.
  intro H; apply numeric_context_DNE, numeric_deduction.
  apply (numeric_context_mp ((wn b) :: G) (wim a (wn b)) 1).
  - apply numeric_context_lift, numeric_assumption; now left.
  - apply numeric_under_head; exact H.
Qed.

Definition disjunction_code a b := wim (wn a) b.

Lemma numeric_disjunction_left G a b : numeric_context G a ->
  numeric_context G (disjunction_code a b).
Proof.
  intro Ha; unfold disjunction_code; apply numeric_deduction, numeric_context_explosion.
  apply (numeric_context_mp ((wn a) :: G) a 1).
  - apply numeric_under_head; exact Ha.
  - apply numeric_assumption; now left.
Qed.

Lemma numeric_disjunction_right G a b : numeric_context G b ->
  numeric_context G (disjunction_code a b).
Proof. intro Hb; unfold disjunction_code; apply numeric_context_lift; exact Hb. Qed.

Lemma numeric_disjunction_elimination G a b c :
  numeric_context G (disjunction_code a b) ->
  numeric_context (a :: G) c -> numeric_context (b :: G) c -> numeric_context G c.
Proof.
  intros Hsum Ha Hb; apply numeric_context_DNE, numeric_deduction.
  pose proof (numeric_deduction G a c Ha) as Hac.
  pose proof (numeric_deduction G b c Hb) as Hbc.
  assert (Hnota : numeric_context ((wn c) :: G) (wn a)).
  { apply numeric_deduction.
    apply (numeric_context_mp (a :: (wn c) :: G) c 1).
    - apply (numeric_context_mp (a :: (wn c) :: G) a c).
      + apply numeric_assumption; now left.
      + apply numeric_under_head, numeric_under_head; exact Hac.
    - apply numeric_assumption; right; now left. }
  assert (Hbody : numeric_context ((wn c) :: G) b).
  { apply (numeric_context_mp ((wn c) :: G) (wn a) b Hnota).
    apply numeric_under_head; exact Hsum. }
  apply (numeric_context_mp ((wn c) :: G) c 1).
  - apply (numeric_context_mp ((wn c) :: G) b c Hbody).
    apply numeric_under_head; exact Hbc.
  - apply numeric_assumption; now left.
Qed.

(** Both source vacuity conjuncts are projected from an actual gated bundle
    proof. The exact gate is name freshness; the first two names may collide. *)
Theorem numeric_equality_vacuity_code a b c : c <> a -> c <> b ->
  Compiler238.derivable (wim (weq a b) (wal c (weq a b))).
Proof.
  intros Hca Hcb; apply numeric_context_empty.
  apply numeric_conjunction_left with
    (b := wim (wel a b) (wal c (wel a b))).
  eapply numeric_conjunction_right.
  apply numeric_theorem; exact (Compiler238.derives_bundle a b c Hca Hcb).
Qed.

Theorem numeric_membership_vacuity_code a b c : c <> a -> c <> b ->
  Compiler238.derivable (wim (wel a b) (wal c (wel a b))).
Proof.
  intros Hca Hcb; apply numeric_context_empty.
  apply numeric_conjunction_right with
    (a := wim (weq a b) (wal c (weq a b))).
  eapply numeric_conjunction_right.
  apply numeric_theorem; exact (Compiler238.derives_bundle a b c Hca Hcb).
Qed.

(** A quantified MP step is the actual R2 row, with its two actual premise
    proofs. This finite generalization rule requires constructed vacuity
    derivations for hypotheses rather than any semantic side condition. *)
Lemma numeric_forall_mp G x a b : numeric_context G (wal x a) ->
  numeric_context G (wal x (wim a b)) -> numeric_context G (wal x b).
Proof.
  intros Ha Hab.
  assert (HR : numeric_context G
    (wim (wal x (wim a b)) (wim (wal x a) (wal x b)))).
  { apply numeric_theorem; exact (Compiler238.derives_r2 x a b). }
  pose proof (numeric_context_mp G (wal x (wim a b))
    (wim (wal x a) (wal x b)) Hab HR) as Hstep.
  exact (numeric_context_mp G (wal x a) (wal x b) Ha Hstep).
Qed.

Theorem numeric_context_generalize G x a :
  (forall h, In h G -> Compiler238.derivable (wim h (wal x h))) ->
  numeric_context G a -> numeric_context G (wal x a).
Proof.
  intros Hv D; induction D as [a Ha | a Hth | a b Da IHa Dab IHab].
  - apply (numeric_context_mp G a (wal x a)).
    + apply numeric_assumption; exact Ha.
    + apply numeric_theorem, Hv; exact Ha.
  - apply numeric_theorem; exact (Compiler238.derives_all x a Hth).
  - exact (numeric_forall_mp G x a b IHa IHab).
Qed.

Lemma numeric_context_contrapose G a b : numeric_context G (wim a b) ->
  numeric_context G (wim (wn b) (wn a)).
Proof.
  intro H; apply numeric_deduction, numeric_deduction.
  apply (numeric_context_mp (a :: (wn b) :: G) b 1).
  - apply (numeric_context_mp (a :: (wn b) :: G) a b).
    + apply numeric_assumption; now left.
    + apply numeric_under_head, numeric_under_head; exact H.
  - apply numeric_assumption; right; now left.
Qed.

Lemma numeric_contrapose a b : Compiler238.derivable (wim a b) ->
  Compiler238.derivable (wim (wn b) (wn a)).
Proof.
  intro H; apply numeric_context_empty, numeric_context_contrapose,
    numeric_theorem; exact H.
Qed.

Lemma numeric_implication_compose a b c : Compiler238.derivable (wim a b) ->
  Compiler238.derivable (wim b c) -> Compiler238.derivable (wim a c).
Proof.
  intros Hab Hbc.
  pose proof (Compiler238.derives_mp (wim a b)
    (wim (wim b c) (wim a c)) Hab (numeric_B a b c)) as Hstep.
  exact (Compiler238.derives_mp (wim b c) (wim a c) Hbc Hstep).
Qed.

(** Negation preserves a constructed vacuity proof. R6 supplies the first
    modal implication; R2 lifts the contraposition of the input proof. *)
Theorem numeric_negation_vacuity x a :
  Compiler238.derivable (wim a (wal x a)) ->
  Compiler238.derivable (wim (wn a) (wal x (wn a))).
Proof.
  intro Hv.
  pose proof (numeric_contrapose a (wal x a) Hv) as Hcontra.
  pose proof (Compiler238.derives_all x (wim (wn (wal x a)) (wn a)) Hcontra) as Hgen.
  pose proof (Compiler238.derives_mp (wal x (wim (wn (wal x a)) (wn a)))
    (wim (wal x (wn (wal x a))) (wal x (wn a))) Hgen
    (Compiler238.derives_r2 x (wn (wal x a)) (wn a))) as Hlift.
  pose proof (numeric_contrapose (wex x (wal x a)) a
    (Compiler238.derives_r6 x a)) as Hr6.
  change (Compiler238.derivable
    (wim (wn a) (wn (wn (wal x (wn (wal x a))))))) in Hr6.
  pose proof (numeric_implication_compose (wn a)
    (wn (wn (wal x (wn (wal x a))))) (wal x (wn (wal x a)))
    Hr6 (numeric_DNE (wal x (wn (wal x a))))) as Hfirst.
  exact (numeric_implication_compose (wn a) (wal x (wn (wal x a)))
    (wal x (wn a)) Hfirst Hlift).
Qed.

Theorem numeric_implication_vacuity x a b :
  Compiler238.derivable (wim a (wal x a)) ->
  Compiler238.derivable (wim b (wal x b)) ->
  Compiler238.derivable (wim (wim a b) (wal x (wim a b))).
Proof.
  intros Ha Hb.
  assert (HB : Compiler238.derivable (wim b (wal x (wim a b)))).
  { pose proof (Compiler238.derives_all x (wim b (wim a b)) (numeric_K b a)) as Hgen.
    pose proof (Compiler238.derives_mp (wal x (wim b (wim a b)))
      (wim (wal x b) (wal x (wim a b))) Hgen
      (Compiler238.derives_r2 x b (wim a b))) as Hlift.
    exact (numeric_implication_compose b (wal x b) (wal x (wim a b)) Hb Hlift). }
  assert (Hnot : Compiler238.derivable (wim (wn a) (wim a b))).
  { apply numeric_context_empty, numeric_deduction, numeric_deduction,
      numeric_context_explosion.
    apply (numeric_context_mp (a :: [wn a]) a 1).
    - apply numeric_assumption; now left.
    - apply numeric_assumption; right; now left. }
  assert (HA : Compiler238.derivable (wim (wn a) (wal x (wim a b)))).
  { pose proof (Compiler238.derives_all x (wim (wn a) (wim a b)) Hnot) as Hgen.
    pose proof (Compiler238.derives_mp (wal x (wim (wn a) (wim a b)))
      (wim (wal x (wn a)) (wal x (wim a b))) Hgen
      (Compiler238.derives_r2 x (wn a) (wim a b))) as Hlift.
    exact (numeric_implication_compose (wn a) (wal x (wn a))
      (wal x (wim a b)) (numeric_negation_vacuity x a Ha) Hlift). }
  apply numeric_context_empty, numeric_deduction.
  assert (Hsum : numeric_context [wim a b] (disjunction_code (wn a) b)).
  { unfold disjunction_code; apply numeric_deduction.
    apply (numeric_context_mp (wn (wn a) :: [wim a b]) a b).
    - apply numeric_context_DNE, numeric_assumption; now left.
    - apply numeric_assumption; right; now left. }
  apply (numeric_disjunction_elimination [wim a b] (wn a) b
    (wal x (wim a b)) Hsum).
  - apply (numeric_context_mp ((wn a) :: [wim a b]) (wn a) (wal x (wim a b))).
    + apply numeric_assumption; now left.
    + apply numeric_theorem; exact HA.
  - apply (numeric_context_mp (b :: [wim a b]) b (wal x (wim a b))).
    + apply numeric_assumption; now left.
    + apply numeric_theorem; exact HB.
Qed.

Theorem numeric_universal_vacuity x y a :
  Compiler238.derivable (wim a (wal x a)) ->
  Compiler238.derivable (wim (wal y a) (wal x (wal y a))).
Proof.
  intro Hv.
  pose proof (Compiler238.derives_all y (wim a (wal x a)) Hv) as Hgen.
  pose proof (Compiler238.derives_mp (wal y (wim a (wal x a)))
    (wim (wal y a) (wal y (wal x a))) Hgen
    (Compiler238.derives_r2 y a (wal x a))) as Hstep.
  exact (numeric_implication_compose (wal y a) (wal y (wal x a))
    (wal x (wal y a)) Hstep (Compiler238.derives_r4 y x a)).
Qed.

Lemma numeric_contraposition_formula a b :
  Compiler238.derivable (wim (wim a b) (wim (wn b) (wn a))).
Proof.
  apply numeric_context_empty, numeric_deduction, numeric_context_contrapose.
  apply numeric_assumption; now left.
Qed.

(** Actual existential elimination under a constructed conclusion-vacuity
    proof. Only the closed contraposition theorem is generalized. *)
Theorem numeric_existential_elimination G x a b :
  Compiler238.derivable (wim b (wal x b)) ->
  numeric_context G (wal x (wim a b)) ->
  numeric_context G (wex x a) -> numeric_context G b.
Proof.
  intros Hv Himp Hex; apply numeric_context_DNE, numeric_deduction.
  assert (Hall : numeric_context ((wn b) :: G) (wal x (wn a))).
  { apply (numeric_forall_mp ((wn b) :: G) x (wn b) (wn a)).
    - apply (numeric_context_mp ((wn b) :: G) (wn b) (wal x (wn b))).
      + apply numeric_assumption; now left.
      + apply numeric_theorem, numeric_negation_vacuity; exact Hv.
    - apply (numeric_forall_mp ((wn b) :: G) x (wim a b) (wim (wn b) (wn a))).
      + apply numeric_under_head; exact Himp.
      + apply numeric_theorem.
        exact (Compiler238.derives_all x
          (wim (wim a b) (wim (wn b) (wn a))) (numeric_contraposition_formula a b)). }
  apply (numeric_context_mp ((wn b) :: G) (wal x (wn a)) 1 Hall).
  apply numeric_under_head; exact Hex.
Qed.

Theorem numeric_equality_reflexive a : Compiler238.derivable (weq a a).
Proof.
  set (x := S a).
  assert (Hxa : x <> a).
  { unfold x; lia. }
  assert (Hv : Compiler238.derivable (wim (weq a a) (wal x (weq a a)))).
  { apply numeric_equality_vacuity_code; exact Hxa. }
  assert (Hdup : Compiler238.derivable (wim (weq x a) (weq a a))).
  { apply numeric_context_empty, numeric_deduction.
    assert (HE : numeric_context [weq x a] (weq x a)).
    { apply numeric_assumption; now left. }
    pose proof (numeric_context_mp [weq x a] (weq x a)
      (wim (weq x a) (weq a a)) HE
      (numeric_theorem [weq x a] _ (Compiler238.derives_r7 x a a))) as Hstep.
    exact (numeric_context_mp [weq x a] (weq x a) (weq a a) HE Hstep). }
  apply numeric_context_empty.
  apply (numeric_existential_elimination [] x (weq x a) (weq a a) Hv).
  - apply numeric_theorem; exact (Compiler238.derives_all x _ Hdup).
  - apply numeric_theorem; exact (Compiler238.derives_r1 x a).
Qed.

Theorem numeric_equality_symmetry a b :
  Compiler238.derivable (wim (weq a b) (weq b a)).
Proof.
  apply numeric_context_empty, numeric_deduction.
  assert (Hstep : numeric_context [weq a b] (wim (weq a a) (weq b a))).
  { apply (numeric_context_mp [weq a b] (weq a b) (wim (weq a a) (weq b a))).
    - apply numeric_assumption; now left.
    - apply numeric_theorem; exact (Compiler238.derives_r7 a b a). }
  apply (numeric_context_mp [weq a b] (weq a a) (weq b a)).
  - apply numeric_theorem, numeric_equality_reflexive.
  - exact Hstep.
Qed.

Theorem numeric_equality_transitive a b c :
  Compiler238.derivable (wim (weq a b) (wim (weq b c) (weq a c))).
Proof.
  apply numeric_context_empty, numeric_deduction, numeric_deduction.
  assert (Hba : numeric_context (weq b c :: [weq a b]) (weq b a)).
  { apply (numeric_context_mp (weq b c :: [weq a b]) (weq a b) (weq b a)).
    - apply numeric_assumption; right; now left.
    - apply numeric_theorem, numeric_equality_symmetry. }
  pose proof (numeric_context_mp (weq b c :: [weq a b]) (weq b a)
    (wim (weq b c) (weq a c)) Hba
    (numeric_theorem (weq b c :: [weq a b]) _ (Compiler238.derives_r7 b a c))) as Hstep.
  apply (numeric_context_mp (weq b c :: [weq a b]) (weq b c) (weq a c)).
  - apply numeric_assumption; now left.
  - exact Hstep.
Qed.

Lemma numeric_context_equality_symmetry G a b : numeric_context G (weq a b) ->
  numeric_context G (weq b a).
Proof.
  intro H; apply (numeric_context_mp G (weq a b) (weq b a) H).
  apply numeric_theorem, numeric_equality_symmetry.
Qed.

Lemma numeric_context_equality_transitive G a b c : numeric_context G (weq a b) ->
  numeric_context G (weq b c) -> numeric_context G (weq a c).
Proof.
  intros Hab Hbc.
  pose proof (numeric_context_mp G (weq a b) (wim (weq b c) (weq a c)) Hab
    (numeric_theorem G _ (numeric_equality_transitive a b c))) as Hstep.
  exact (numeric_context_mp G (weq b c) (weq a c) Hbc Hstep).
Qed.

Lemma numeric_context_equality_congruence G a b c d :
  numeric_context G (weq a c) -> numeric_context G (weq b d) ->
  numeric_context G (weq a b) -> numeric_context G (weq c d).
Proof.
  intros Hac Hbd Hab.
  apply (numeric_context_equality_transitive G c b d); [|exact Hbd].
  apply (numeric_context_equality_transitive G c a b); [|exact Hab].
  apply numeric_context_equality_symmetry; exact Hac.
Qed.

Lemma numeric_context_membership_congruence G a b c d :
  numeric_context G (weq a c) -> numeric_context G (weq b d) ->
  numeric_context G (wel a b) -> numeric_context G (wel c d).
Proof.
  intros Hac Hbd Hab.
  pose proof (numeric_context_mp G (weq a c) (wim (wel a b) (wel c b)) Hac
    (numeric_theorem G _ (Compiler238.derives_r5 a c b))) as Hfirst.
  pose proof (numeric_context_mp G (wel a b) (wel c b) Hab Hfirst) as Hcb.
  pose proof (numeric_context_mp G (wel c b) (wim (weq b d) (wel c d)) Hcb
    (numeric_theorem G _ (Compiler238.derives_r3 c b d))) as Hsecond.
  exact (numeric_context_mp G (weq b d) (wel c d) Hbd Hsecond).
Qed.

Lemma numeric_context_implication_congruence G a aa b bb :
  numeric_context G (wim aa a) -> numeric_context G (wim b bb) ->
  numeric_context G (wim (wim a b) (wim aa bb)).
Proof.
  intros Haa Hbb; apply numeric_deduction, numeric_deduction.
  apply (numeric_context_mp (aa :: (wim a b) :: G) b bb).
  - apply (numeric_context_mp (aa :: (wim a b) :: G) a b).
    + apply (numeric_context_mp (aa :: (wim a b) :: G) aa a).
      * apply numeric_assumption; now left.
      * apply numeric_under_head, numeric_under_head; exact Haa.
    + apply numeric_assumption; right; now left.
  - apply numeric_under_head, numeric_under_head; exact Hbb.
Qed.

Lemma numeric_conditional_contrapose e a b :
  Compiler238.derivable (wim e (wim a b)) ->
  Compiler238.derivable (wim e (wim (wn b) (wn a))).
Proof.
  intro H; apply numeric_context_empty, numeric_deduction, numeric_context_contrapose.
  apply (numeric_context_mp [e] e (wim a b)).
  - apply numeric_assumption; now left.
  - apply numeric_theorem; exact H.
Qed.

Lemma numeric_conditional_implication_congruence e a aa b bb :
  Compiler238.derivable (wim e (wim aa a)) ->
  Compiler238.derivable (wim e (wim b bb)) ->
  Compiler238.derivable (wim e (wim (wim a b) (wim aa bb))).
Proof.
  intros Ha Hb; apply numeric_context_empty, numeric_deduction,
    numeric_context_implication_congruence.
  - apply (numeric_context_mp [e] e (wim aa a)).
    + apply numeric_assumption; now left.
    + apply numeric_theorem; exact Ha.
  - apply (numeric_context_mp [e] e (wim b bb)).
    + apply numeric_assumption; now left.
    + apply numeric_theorem; exact Hb.
Qed.

Lemma numeric_conditional_universal e x a b :
  Compiler238.derivable (wim e (wal x e)) ->
  Compiler238.derivable (wim e (wim a b)) ->
  Compiler238.derivable (wim e (wim (wal x a) (wal x b))).
Proof.
  intros Hv Himp; apply numeric_context_empty, numeric_deduction, numeric_deduction.
  apply (numeric_forall_mp (wal x a :: [e]) x a b).
  - apply numeric_assumption; now left.
  - apply (numeric_forall_mp (wal x a :: [e]) x e (wim a b)).
    + apply (numeric_context_mp (wal x a :: [e]) e (wal x e)).
      * apply numeric_assumption; right; now left.
      * apply numeric_theorem; exact Hv.
    + apply numeric_theorem; exact (Compiler238.derives_all x _ Himp).
Qed.

(** Optional syntactic contradiction encoding. This is a raw proof-code
    construction, not a claim of decoder-level falsity without target IR.
    The main forward translation may use code 1 as relative bottom because
    the actual R6/K explosion rule above has already been constructed. *)
Definition logical_bottom_code := wn (wim 1 1).

Lemma numeric_context_bottom G : numeric_context G logical_bottom_code ->
  numeric_context G 1.
Proof.
  intro HF; apply (numeric_context_mp G (wim 1 1) 1).
  - apply numeric_theorem, numeric_I.
  - exact HF.
Qed.

Lemma numeric_context_bottom_explosion G a :
  numeric_context G logical_bottom_code -> numeric_context G a.
Proof. intro H; apply numeric_context_explosion, numeric_context_bottom, H. Qed.

Lemma numeric_context_peirce G a b :
  numeric_context G (wim (wim (wim a b) a) a).
Proof. apply numeric_theorem, numeric_P. Qed.

Print Assumptions numeric_I.
Print Assumptions numeric_K.
Print Assumptions numeric_P.
Print Assumptions numeric_B.
Print Assumptions numeric_deduction.
Print Assumptions numeric_F.
Print Assumptions numeric_DNE.
Print Assumptions numeric_conjunction_intro.
Print Assumptions numeric_disjunction_elimination.
Print Assumptions numeric_equality_vacuity_code.
Print Assumptions numeric_membership_vacuity_code.
Print Assumptions numeric_context_generalize.
Print Assumptions numeric_negation_vacuity.
Print Assumptions numeric_implication_vacuity.
Print Assumptions numeric_universal_vacuity.
Print Assumptions numeric_existential_elimination.
Print Assumptions numeric_equality_reflexive.
Print Assumptions numeric_equality_symmetry.
Print Assumptions numeric_equality_transitive.
Print Assumptions numeric_conditional_universal.
Print Assumptions numeric_S.
Print Assumptions numeric_context_explosion.
Print Assumptions numeric_context_bottom_explosion.
End NumericHilbert238.
