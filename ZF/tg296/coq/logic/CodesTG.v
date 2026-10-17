(** * CodesTG: the formula coding of the m254tg source program (machine/source_tg.py =
    zfc_254 with the AX bundle replaced by UG').  Everything except the bundle is the zfc_254 coding,
    re-exported from ZF/m254/coq/logic/Codes254.v (read-only): P, unP, wim, wel, wal, weq, F, wn, wa,
    wex, the rows rho1..rho8 and their lemmas.  (Codes254's own [bundle] is the OLD zfc_254 bundle and
    is not used here; the m254tg bundle is [bundle_tg].) *)
From Coq Require Import Arith Lia.
From M254L Require Export Codes254.

(** ** The gated bundle (m254tg): the universe-collection schema UG'_phi, phi = code c, plus atomic
    vacuity.  Labels: w = S c (= c+1, the source's par3 followed by topwff.inc), f = 0,
    x = B = U = b, C = W = c, input a, output b.  Decoded (design/machine.md section 1):
      UG' = Ed [ A0 Ab ( b:d -> ( Y /\ (T /\ Q) ) ) /\ c:d ]
      Y   = Ec [ ( cl2 /\ (H -> Ub) ) /\ cl1 ]
      cl2 = Ab (b:c -> Ea phi)            H  = Aa (a:b -> Eb (b:d /\ phi))
      Ub  = Eb [ b:d /\ Ad (d:c -> Ac (c:d -> c:b)) ]
      cl1 = Aa (a:b -> Ab (phi -> Eb (b:c /\ phi)))
      T   = Ac (c:b -> c:d)              Q  = Ec [ Ad (Ac (c:d -> c:b) -> d:c) /\ c:d ] *)
Definition ugU (a b c : nat) : nat :=
  wex b (wa (wel b (S c)) (wal (S c) (wim (wel (S c) c) (wal c (wim (wel c (S c)) (wel c b)))))).
Definition ugH (a b c : nat) : nat := wal a (wim (wel a b) (wex b (wa (wel b (S c)) c))).
Definition ugcl1 (a b c : nat) : nat := wal a (wim (wel a b) (wal b (wim c (wex b (wa (wel b c) c))))).
Definition ugcl2 (a b c : nat) : nat := wal b (wim (wel b c) (wex a c)).
Definition ugY (a b c : nat) : nat :=
  wex c (wa (wa (ugcl2 a b c) (wim (ugH a b c) (ugU a b c))) (ugcl1 a b c)).
Definition ugT (b c : nat) : nat := wal c (wim (wel c b) (wel c (S c))).
Definition ugQ (b c : nat) : nat :=
  wex c (wa (wal (S c) (wim (wal c (wim (wel c (S c)) (wel c b))) (wel (S c) c))) (wel c (S c))).
Definition ugB (a b c : nat) : nat :=
  wex (S c) (wa (wal 0 (wal b (wim (wel b (S c)) (wa (ugY a b c) (wa (ugT b c) (ugQ b c))))))
                (wel c (S c))).
Definition bundle_tg (a b c : nat) : nat :=
  wa (ugB a b c) (wa (wim (weq a b) (wal c (weq a b))) (wim (wel a b) (wal c (wel a b)))).

(** the flat term generated from the validated RPN AST (tools/machine/gen.py, variant tg) *)
Lemma bundle_tg_flat a b c : bundle_tg a b c =
  wa (wex (S c) (wa (wal 0 (wal b (wim (wel b (S c)) (wa (wex c (wa (wa (wal b (wim (wel b c) (wex a c))) (wim (wal a (wim (wel a b) (wex b (wa (wel b (S c)) c)))) (wex b (wa (wel b (S c)) (wal (S c) (wim (wel (S c) c) (wal c (wim (wel c (S c)) (wel c b))))))))) (wal a (wim (wel a b) (wal b (wim c (wex b (wa (wel b c) c)))))))) (wa (wal c (wim (wel c b) (wel c (S c)))) (wex c (wa (wal (S c) (wim (wal c (wim (wel c (S c)) (wel c b))) (wel (S c) c))) (wel c (S c))))))))) (wel c (S c))))
     (wa (wim (weq a b) (wal c (weq a b))) (wim (wel a b) (wal c (wel a b)))).
Proof. reflexivity. Qed.

Lemma bundle_tg_ne_F a b c : bundle_tg a b c <> F.
Proof. apply wa_ne_F. Qed.
