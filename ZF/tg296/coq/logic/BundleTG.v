(** * BundleTG: the gated m254tg AX bundle as a named wff, and its decoding.

      BW a b c phi = UGW a b c phi /\ (V= /\ V-in)
    UGW is the universe-collection schema UG' with w = S c, f = 0, x = B = U = b, C = W = c,
    matrix phi (input a, output b).  The machine's bundle_tg a b c decodes to BW a b c (D c).
    Side lemmas and tactics are reused from ZF/m254/coq/logic/Bundle254.v (read-only). *)
From Coq Require Import Arith Lia.
From ZF Require Import Logic.
From M254L Require Import Wff254 Bundle254.
From M254TGL Require Import CodesTG.

Definition WU (a b c : nat) : wff :=
  Wex b (Wa (Wel b (S c)) (Wal (S c) (Wim (Wel (S c) c) (Wal c (Wim (Wel c (S c)) (Wel c b)))))).
Definition WH (a b c : nat) (phi : wff) : wff := Wal a (Wim (Wel a b) (Wex b (Wa (Wel b (S c)) phi))).
Definition Wcl1 (a b c : nat) (phi : wff) : wff :=
  Wal a (Wim (Wel a b) (Wal b (Wim phi (Wex b (Wa (Wel b c) phi))))).
Definition Wcl2 (a b c : nat) (phi : wff) : wff := Wal b (Wim (Wel b c) (Wex a phi)).
Definition WY (a b c : nat) (phi : wff) : wff :=
  Wex c (Wa (Wa (Wcl2 a b c phi) (Wim (WH a b c phi) (WU a b c))) (Wcl1 a b c phi)).
Definition WT (b c : nat) : wff := Wal c (Wim (Wel c b) (Wel c (S c))).
Definition WQ (b c : nat) : wff :=
  Wex c (Wa (Wal (S c) (Wim (Wal c (Wim (Wel c (S c)) (Wel c b))) (Wel (S c) c))) (Wel c (S c))).
Definition UGW (a b c : nat) (phi : wff) : wff :=
  Wex (S c) (Wa (Wal 0 (Wal b (Wim (Wel b (S c)) (Wa (WY a b c phi) (Wa (WT b c) (WQ b c))))))
                (Wel c (S c))).
Definition BVt (a b c : nat) : wff :=
  Wa (Wim (Weq a b) (Wal c (Weq a b))) (Wim (Wel a b) (Wal c (Wel a b))).
Definition BW (a b c : nat) (phi : wff) : wff := Wa (UGW a b c phi) (BVt a b c).

Lemma D_bundle_tg a b c : c <> a -> c <> b -> D (bundle_tg a b c) = BW a b c (D c).
Proof.
  intros H1 H2.
  unfold bundle_tg, ugB, ugY, ugH, ugU, ugcl1, ugcl2, ugT, ugQ.
  assert (E1 : wel c b <> 1) by (apply wel_ne1; intro E; injection E as -> ->; now apply H2).
  assert (E2 : wel (S c) c <> 1) by (apply wel_ne1; apply pair_ne00_l; lia).
  assert (E3 : wel c (S c) <> 1) by (apply wel_ne1; apply pair_ne00_r; lia).
  Dsimp. reflexivity.
Qed.
