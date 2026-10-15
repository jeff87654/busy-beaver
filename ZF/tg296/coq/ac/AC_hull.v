(** * AC_hull: an indexed Skolem hull inside L.

    Input: a formula c ($0 = witness, $1 = parameter, read through Std_setrec.Rel2), a base function H0
    whose indices are tagged with the numeral 0 and lie in a set I closed under ordered pairs (with the
    numerals 1, 2 ∈ I), and whose values are in L.
    Output ([hull_ex]): a function H ⊇ H0 with indices in I, whose range X ⊆ L is closed under ordered
    pairs and under canonical witnesses of c ([WClos c X]).

    Construction (ω-recursion AC_rec with the closed step [phH c]): H_0 = H0 and
      H_{n+1} = H_n ∪ {((1,(s,t)), (H_n s, H_n t)) | s, t ∈ dom H_n}
                    ∪ {((2,s), w) | s ∈ dom H_n, w = canonical witness of c(·, H_n s)}  ([NxH]);
    H = ⋃_n H_n.  The tags make H single-valued (induction on n); dom H ⊆ I by induction. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From ZF Require Std_setrec.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_wo.
From M254TGA Require Import AC_rec AC_cwo AC_tup.
From M254TGA Require AC_univ.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** q = ((1, (s, t)), (x, y)) for (s, x), (t, y) ∈ F *)
Definition PairE (F q : term) : form :=
  ∃ (∃ (∃ (∃ (App0 F`[↑]`[↑]`[↑]`[↑] $3 $1 ∧ App0 F`[↑]`[↑]`[↑]`[↑] $2 $0 ∧
     ∃ (∃ (∃ (∃ (NumF 1 $3 ∧ OP0 $7 $6 $2 ∧ OP0 $3 $2 $1 ∧ OP0 $5 $4 $0 ∧
                 OP0 $1 $0 q`[↑]`[↑]`[↑]`[↑]`[↑]`[↑]`[↑]`[↑])))))))).
(** q = ((2, s), w) for (s, x) ∈ F and w the canonical witness of c(·, x) *)
Definition SkE (c : form) (F q : term) : form :=
  ∃ (∃ (App0 F`[↑]`[↑] $1 $0 ∧
     ∃ (CanW c $1 $0 ∧ ∃ (∃ (NumF 2 $1 ∧ OP0 $1 $4 $0 ∧ OP0 $0 $2 q`[↑]`[↑]`[↑]`[↑]`[↑]))))).
(** F' = F ∪ pairs ∪ witnesses *)
Definition NxH (c : form) (F F' : term) : form :=
  ∀ (($0 ∈' F'`[↑]) ↔ (($0 ∈' F`[↑] ∨ PairE F`[↑] $0) ∨ SkE c F`[↑] $0)).
Definition phH (c : form) : form := NxH c $0 $1.

Definition HullP (c : form) (H0 I H X : term) : form :=
  Fun0 H ∧
  (∀ (∀ (App0 H`[↑]`[↑] $1 $0 → $1 ∈' I`[↑]`[↑]))) ∧
  (∀ ($0 ∈' X`[↑] ↔ ∃ App0 H`[↑]`[↑] $0 $1)) ∧
  (∀ (∀ (App0 H0`[↑]`[↑] $1 $0 → App0 H`[↑]`[↑] $1 $0))) ∧
  (∀ ($0 ∈' X`[↑] → Lform)) ∧
  OPClos X ∧
  WClos c X.

#[global] Arguments PairE : simpl never.
#[global] Arguments SkE : simpl never.
#[global] Arguments NxH : simpl never.
#[global] Arguments HullP : simpl never.
#[local] Arguments phH : simpl never.
#[local] Hint Rewrite NumF_subst : fsub.

Lemma PairE_subst F q sg : (PairE F q)[sg] = PairE F`[sg] q`[sg].
Proof. psubst PairE. Qed.
#[global] Hint Rewrite PairE_subst : fsub.
Lemma SkE_subst c F q sg : (SkE c F q)[sg] = SkE c F`[sg] q`[sg].
Proof. psubst SkE. Qed.
#[global] Hint Rewrite SkE_subst : fsub.
Lemma NxH_subst c F F' sg : (NxH c F F')[sg] = NxH c F`[sg] F'`[sg].
Proof. psubst NxH. Qed.
#[global] Hint Rewrite NxH_subst : fsub.
Lemma HullP_subst c H0 I H X sg : (HullP c H0 I H X)[sg] = HullP c H0`[sg] I`[sg] H`[sg] X`[sg].
Proof.
  intros. unfold HullP, WClos.
  repeat progress (cbn; autorewrite with fsub); fix_up; reflexivity.
Qed.
#[global] Hint Rewrite PairE_subst SkE_subst NxH_subst HullP_subst : fsub.

(** ** Helper predicates *)
#[local] Arguments InL : simpl never.
Lemma hl_InL_subst t sg : (InL t)[sg] = InL t`[sg].
Proof. rewrite !InL_eq. repeat progress (cbn; autorewrite with fsub); fix_up; reflexivity. Qed.
#[local] Hint Rewrite hl_InL_subst : fsub.

(** replacement formula for the pair entries: p1 = (s, x), p2 = (t, y), q = ((1, (s, t)), (x, y)) *)
Definition PQ (p1 p2 q : term) : form :=
  ∃ (∃ (∃ (∃ (OP0 $3 $2 p1`[↑]`[↑]`[↑]`[↑] ∧ OP0 $1 $0 p2`[↑]`[↑]`[↑]`[↑] ∧
     ∃ (∃ (∃ (∃ (NumF 1 $3 ∧ OP0 $7 $5 $2 ∧ OP0 $3 $2 $1 ∧ OP0 $6 $4 $0 ∧
                 OP0 $1 $0 q`[↑]`[↑]`[↑]`[↑]`[↑]`[↑]`[↑]`[↑])))))))).
(** z is a pair entry built from p1 and some p2 ∈ Fs *)
Definition PZ (Fs p1 z : term) : form := ∃ ($0 ∈' Fs`[↑] ∧ PQ p1`[↑] $0 z`[↑]).
(** replacement formula for the witness entries: p = (s, x), q = ((2, s), w) *)
Definition SQ (c : form) (p q : term) : form :=
  ∃ (∃ (OP0 $1 $0 p`[↑]`[↑] ∧
     ∃ (CanW c $1 $0 ∧ ∃ (∃ (NumF 2 $1 ∧ OP0 $1 $4 $0 ∧ OP0 $0 $2 q`[↑]`[↑]`[↑]`[↑]`[↑]))))).
(** (i, v) is a pair entry over F *)
Definition HPairT (F i v : term) : form :=
  ∃ (∃ (∃ (∃ (App0 F`[↑]`[↑]`[↑]`[↑] $3 $1 ∧ App0 F`[↑]`[↑]`[↑]`[↑] $2 $0 ∧
     ∃ (∃ (NumF 1 $1 ∧ OP0 $5 $4 $0 ∧ OP0 $1 $0 i`[↑]`[↑]`[↑]`[↑]`[↑]`[↑] ∧
           OP0 $3 $2 v`[↑]`[↑]`[↑]`[↑]`[↑]`[↑])))))).
(** (i, v) is a witness entry over F *)
Definition HSkT (c : form) (F i v : term) : form :=
  ∃ (∃ (App0 F`[↑]`[↑] $1 $0 ∧ CanW c $0 v`[↑]`[↑] ∧ ∃ (NumF 2 $0 ∧ OP0 $0 $2 i`[↑]`[↑]`[↑]))).
(** every entry of F is a base entry, a pair entry over F or a witness entry over F *)
Definition Cls (c : form) (F H0 : term) : form :=
  ∀ (∀ (App0 F`[↑]`[↑] $1 $0 → (App0 H0`[↑]`[↑] $1 $0 ∨ HPairT F`[↑]`[↑] $1 $0) ∨ HSkT c F`[↑]`[↑] $1 $0)).
Definition Inv (c : form) (F H0 I : term) : form :=
  Fun0 F ∧ (∀ (∀ (App0 F`[↑]`[↑] $1 $0 → $1 ∈' I`[↑]`[↑]))) ∧ (∀ (∀ (App0 F`[↑]`[↑] $1 $0 → InL $0))) ∧
  Cls c F H0.
(** induction formula: m ↦ Inv(Fn(m)) and Fn(n) ⊆ Fn(m) for n ∈ m *)
Definition PInd (c : form) (m Fn H0 I : term) : form :=
  ∀ (App0 Fn`[↑] m`[↑] $0 → Inv c $0 H0`[↑] I`[↑] ∧
     ∀ ($0 ∈' m`[↑]`[↑] → ∀ (App0 Fn`[↑]`[↑]`[↑] $1 $0 → Sub0 $0 $2))).
(** separation formula for ran g: $0 = z, $1 = g *)
Definition RanF : form := ∃ App0 $2 $0 $1.

#[local] Arguments PQ : simpl never.
#[local] Arguments PZ : simpl never.
#[local] Arguments SQ : simpl never.
#[local] Arguments HPairT : simpl never.
#[local] Arguments HSkT : simpl never.
#[local] Arguments Cls : simpl never.
#[local] Arguments Inv : simpl never.
#[local] Arguments PInd : simpl never.

Lemma PQ_subst p1 p2 q sg : (PQ p1 p2 q)[sg] = PQ p1`[sg] p2`[sg] q`[sg].
Proof. psubst PQ. Qed.
#[local] Hint Rewrite PQ_subst : fsub.
Lemma PZ_subst Fs p1 z sg : (PZ Fs p1 z)[sg] = PZ Fs`[sg] p1`[sg] z`[sg].
Proof. psubst PZ. Qed.
Lemma SQ_subst c p q sg : (SQ c p q)[sg] = SQ c p`[sg] q`[sg].
Proof. psubst SQ. Qed.
Lemma T1_subst F i v sg : (HPairT F i v)[sg] = HPairT F`[sg] i`[sg] v`[sg].
Proof. psubst HPairT. Qed.
Lemma T2_subst c F i v sg : (HSkT c F i v)[sg] = HSkT c F`[sg] i`[sg] v`[sg].
Proof. psubst HSkT. Qed.
#[local] Hint Rewrite PZ_subst SQ_subst T1_subst T2_subst : fsub.
Lemma Cls_subst c F H0 sg : (Cls c F H0)[sg] = Cls c F`[sg] H0`[sg].
Proof. psubst Cls. Qed.
#[local] Hint Rewrite Cls_subst : fsub.
Lemma Inv_subst c F H0 I sg : (Inv c F H0 I)[sg] = Inv c F`[sg] H0`[sg] I`[sg].
Proof. psubst Inv. Qed.
#[local] Hint Rewrite Inv_subst : fsub.
Lemma PInd_subst c m Fn H0 I sg : (PInd c m Fn H0 I)[sg] = PInd c m`[sg] Fn`[sg] H0`[sg] I`[sg].
Proof. psubst PInd. Qed.
#[local] Hint Rewrite PInd_subst : fsub.

Lemma hl_rel2 c u w : Std_setrec.Rel2 (phH c) u w = NxH c u w.
Proof. unfold Std_setrec.Rel2, phH. rewrite NxH_subst. reflexivity. Qed.

(** ** Free-index bounds *)
Lemma hl_fb_OP0 x y p N : idx x < N -> idx y < N -> idx p < N -> fb N (OP0 x y p).
Proof.
  intros Hx Hy Hp. replace (OP0 x y p) with ((OP0 $0 $1 $2)[x .: y .: p .: var]) by (rewrite OP0_subst; reflexivity).
  apply (fb_subst _ 3); [fbcomp|]. intros [|[|[|i]]] Hi; cbn; lia.
Qed.
Lemma hl_fb_N1 x N : idx x < N -> fb N (NumF 1 x).
Proof.
  intros Hx. replace (NumF 1 x) with ((NumF 1 $0)[x .: var]) by (rewrite NumF_subst; reflexivity).
  apply (fb_subst _ 1); [fbcomp|]. intros [|i] Hi; cbn; lia.
Qed.
Lemma hl_fb_N2 x N : idx x < N -> fb N (NumF 2 x).
Proof.
  intros Hx. replace (NumF 2 x) with ((NumF 2 $0)[x .: var]) by (rewrite NumF_subst; reflexivity).
  apply (fb_subst _ 1); [fbcomp|]. intros [|i] Hi; cbn; lia.
Qed.
Lemma hl_fb_Fun0 x N : idx x < N -> fb N (Fun0 x).
Proof.
  intros Hx. replace (Fun0 x) with ((Fun0 $0)[x .: var]) by (rewrite Fun0_subst; reflexivity).
  apply (fb_subst _ 1); [fbcomp|]. intros [|i] Hi; cbn; lia.
Qed.
Lemma hl_fb_Sub0 x y N : idx x < N -> idx y < N -> fb N (Sub0 x y).
Proof.
  intros Hx Hy. replace (Sub0 x y) with ((Sub0 $0 $1)[x .: y .: var]) by (rewrite Sub0_subst; reflexivity).
  apply (fb_subst _ 2); [fbcomp|]. intros [|[|i]] Hi; cbn; lia.
Qed.
Lemma hl_fb_InL x N : idx x < N -> fb N (InL x).
Proof.
  intros Hx. unfold InL. apply (fb_subst _ 1); [exact fb_Lform|]. intros [|i] Hi; cbn; lia.
Qed.
Lemma hl_fb_T1 F i v N : idx F < N -> idx i < N -> idx v < N -> fb N (HPairT F i v).
Proof.
  intros HaF Hi Hv. replace (HPairT F i v) with ((HPairT $0 $1 $2)[F .: i .: v .: var]) by (rewrite T1_subst; reflexivity).
  apply (fb_subst _ 3); [unfold HPairT; fbcomp|]. intros [|[|[|k]]] Hk; cbn; lia.
Qed.

Local Ltac fbh := repeat match goal with
  | |- _ /\ _ => split
  | |- True => exact I
  | |- fb _ (OP0 _ _ _) => apply hl_fb_OP0; cbn; lia
  | |- fb _ (App0 _ _ _) => apply fb_App0; cbn; lia
  | |- fb _ (NumF 1 _) => apply hl_fb_N1; cbn; lia
  | |- fb _ (NumF 2 _) => apply hl_fb_N2; cbn; lia
  | |- fb _ (Fun0 _) => apply hl_fb_Fun0; cbn; lia
  | |- fb _ (Sub0 _ _) => apply hl_fb_Sub0; cbn; lia
  | |- fb _ (InL _) => apply hl_fb_InL; cbn; lia
  | |- fb _ (HPairT _ _ _) => apply hl_fb_T1; cbn; lia
  | |- fb _ (CanW _ _ _) => apply fb_CanW; [assumption|cbn; lia|cbn; lia]
  | |- fb _ (PairE _ _) => unfold PairE; cbn
  | |- fb _ (SkE _ _ _) => unfold SkE; cbn
  | |- _ < _ => cbn; lia
  end.

Lemma hl_fb_T2 c F i v N : fb 2 c -> idx F < N -> idx i < N -> idx v < N -> fb N (HSkT c F i v).
Proof.
  intros Hc HaF Hi Hv. replace (HSkT c F i v) with ((HSkT c $0 $1 $2)[F .: i .: v .: var]) by (rewrite T2_subst; reflexivity).
  apply (fb_subst _ 3); [unfold HSkT; cbn; fbh|]. intros [|[|[|k]]] Hk; cbn; lia.
Qed.

Lemma fb_phH c : fb 2 c -> fb 2 (phH c).
Proof. intros Hc. unfold phH, NxH. cbn. fbh. Qed.

Lemma hl_fb_SQ c : fb 2 c -> fb 2 (SQ c $0 $1).
Proof. intros Hc. unfold SQ. cbn. fbh. Qed.

Lemma hl_fb_PInd c : fb 2 c -> fb 4 (PInd c $0 $1 $2 $3).
Proof.
  intros Hc. unfold PInd, Inv, Cls. cbn. fbh.
  all: apply hl_fb_T2; [assumption|cbn; lia..].
Qed.

(** instances (extended by the prover of this file) *)
Definition hull_insts (c : form) : list form :=
  [forall_times 1 (ax_rep' (PQ $2 $0 $1)); forall_times 1 (ax_rep' (UF (PZ $2 $1 $0)));
   forall_times 0 (ax_rep' (SQ c $0 $1)); forall_times 1 (ax_sep' RanF);
   forall_times 3 (ax_sep' (PInd c $0 $1 $2 $3))].
Definition Ax_hull (c : form) : list form := Ax_cw c ++ Ax_rec (phH c) ++ hull_insts c.
Lemma Ax_hull_ok c a : fb 2 c -> In a (Ax_hull c) -> ZFR a.
Proof.
  intros Hc H. unfold Ax_hull in H. rewrite !in_app_iff in H. destruct H as [H|[H|H]].
  - exact (Ax_cw_ok c a Hc H).
  - exact (Ax_rec_ok (phH c) a (fb_phH c Hc) H).
  - destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply ZFR_rep. unfold PQ. fbcomp.
    + apply ZFR_rep. unfold UF, PZ, PQ. fbcomp.
    + apply ZFR_rep. exact (hl_fb_SQ c Hc).
    + apply ZFR_sep. unfold RanF. fbcomp.
    + apply ZFR_sep. exact (hl_fb_PInd c Hc).
Qed.

(** ** Proof infrastructure *)
#[local] Ltac weaken_facts a G ::=
  repeat match goal with
  | H : G ⊢C _ |- _ => apply (weak_cons G a) in H
  | H : incl _ G |- _ => apply (incl_cons_r _ G a) in H
  | H : In _ G |- _ => apply (in_cons_r _ a G) in H
  | H : WOx G |- _ => apply (WOx_cons G a) in H
  end.

Lemma hl_cl {G} : WOx G -> incl Ax_cl G.
Proof. intros HX. exact (Ax_L_cl _ (WOx_L _ HX)). Qed.
Lemma hl_P {G} : WOx G -> incl Ax_prim G.
Proof. intros HX. exact (Ax_ord_prim _ (Ax_cl_ord _ (hl_cl HX))). Qed.
Lemma hl_wox_incl {G G'} : incl G G' -> WOx G -> WOx G'.
Proof. intros Hi (H1 & H2 & H3). split; [apply Hi, H1|split; [apply Hi, H2|exact (incl_tran H3 Hi)]]. Qed.

Lemma hl_num_ex k {G} (HG : incl ZF0base G) (HX : WOx G) : G ⊢C ∃ NumF k $0.
Proof. destruct HX as (HR & HOm & HW). exact (num_ex k HG HR HOm (Ax_L_cl _ (Ax_wo_L _ HW))). Qed.
Lemma hl_num_neq {G} (HG : incl ZF0base G) (HX : WOx G) k l x y :
  k <> l -> G ⊢C NumF k x -> G ⊢C NumF l y -> G ⊢C x ≡' y -> G ⊢C ⊥.
Proof. destruct HX as (HR & HOm & HW). exact (num_neq HG HR HOm (Ax_L_cl _ (Ax_wo_L _ HW)) k l x y). Qed.
Lemma hl_num_unique k {G} (HG : incl ZF0base G) (HX : WOx G) x x' :
  G ⊢C NumF k x -> G ⊢C NumF k x' -> G ⊢C x ≡' x'.
Proof. destruct HX as (HR & HOm & HW). exact (num_unique k HG HR HOm (Ax_L_cl _ (Ax_wo_L _ HW)) x x'). Qed.

Lemma hl_app_sub {G} F F' i v : G ⊢C Sub0 F F' -> G ⊢C App0 F i v -> G ⊢C App0 F' i v.
Proof.
  intros Hs H. unfold App0 in H |- *. fex H q Hq. fdestr Hq Hq1 Hq2. fexists q. fsplit; [|exact Hq2].
  unfold Sub0 in Hs. finst Hs q. exact (IE Hs Hq1).
Qed.

(** unpacking tactics *)
Local Ltac pe_unpack H s t x y g r i v Hsx Hty Hg Hr Hi Hv Hq :=
  unfold PairE in H;
  let A1 := fresh "A" in fex H s A1; let A2 := fresh "A" in fex A1 t A2;
  let A3 := fresh "A" in fex A2 x A3; let A4 := fresh "A" in fex A3 y A4;
  let B1 := fresh "B" in let B2 := fresh "C" in fdestr A4 B1 B2; fdestr B1 Hsx Hty;
  let C1 := fresh "A" in fex B2 g C1; let C2 := fresh "A" in fex C1 r C2;
  let C3 := fresh "A" in fex C2 i C3; let C4 := fresh "A" in fex C3 v C4;
  let D1 := fresh "B" in fdestr C4 D1 Hq; let D2 := fresh "B" in fdestr D1 D2 Hv;
  let D3 := fresh "B" in fdestr D2 D3 Hi; fdestr D3 Hg Hr.
Local Ltac pq_unpack H s x t y g r i v Hsx Hty Hg Hr Hi Hv Hq :=
  unfold PQ in H;
  let A1 := fresh "A" in fex H s A1; let A2 := fresh "A" in fex A1 x A2;
  let A3 := fresh "A" in fex A2 t A3; let A4 := fresh "A" in fex A3 y A4;
  let B1 := fresh "B" in let B2 := fresh "C" in fdestr A4 B1 B2; fdestr B1 Hsx Hty;
  let C1 := fresh "A" in fex B2 g C1; let C2 := fresh "A" in fex C1 r C2;
  let C3 := fresh "A" in fex C2 i C3; let C4 := fresh "A" in fex C3 v C4;
  let D1 := fresh "B" in fdestr C4 D1 Hq; let D2 := fresh "B" in fdestr D1 D2 Hv;
  let D3 := fresh "B" in fdestr D2 D3 Hi; fdestr D3 Hg Hr.
Local Ltac sk_unpack H s x w g i Hsx Hw Hg Hi Hq :=
  unfold SkE in H;
  let A1 := fresh "A" in fex H s A1; let A2 := fresh "A" in fex A1 x A2;
  let B1 := fresh "B" in fdestr A2 Hsx B1; let A3 := fresh "A" in fex B1 w A3;
  let B2 := fresh "B" in fdestr A3 Hw B2; let A4 := fresh "A" in fex B2 g A4;
  let A5 := fresh "A" in fex A4 i A5;
  let B3 := fresh "B" in fdestr A5 B3 Hq; fdestr B3 Hg Hi.
Local Ltac sq_unpack H s x w g i Hsx Hw Hg Hi Hq :=
  unfold SQ in H;
  let A1 := fresh "A" in fex H s A1; let A2 := fresh "A" in fex A1 x A2;
  let B1 := fresh "B" in fdestr A2 Hsx B1; let A3 := fresh "A" in fex B1 w A3;
  let B2 := fresh "B" in fdestr A3 Hw B2; let A4 := fresh "A" in fex B2 g A4;
  let A5 := fresh "A" in fex A4 i A5;
  let B3 := fresh "B" in fdestr A5 B3 Hq; fdestr B3 Hg Hi.
Local Ltac t1_unpack H s t x y g r Hsx Hty Hg Hr Hi Hv :=
  unfold HPairT in H;
  let A1 := fresh "A" in fex H s A1; let A2 := fresh "A" in fex A1 t A2;
  let A3 := fresh "A" in fex A2 x A3; let A4 := fresh "A" in fex A3 y A4;
  let B1 := fresh "B" in let B2 := fresh "C" in fdestr A4 B1 B2; fdestr B1 Hsx Hty;
  let C1 := fresh "A" in fex B2 g C1; let C2 := fresh "A" in fex C1 r C2;
  let D1 := fresh "B" in fdestr C2 D1 Hv; let D2 := fresh "B" in fdestr D1 D2 Hi; fdestr D2 Hg Hr.
Local Ltac t2_unpack H s x g Hsx Hw Hg Hi :=
  unfold HSkT in H;
  let A1 := fresh "A" in fex H s A1; let A2 := fresh "A" in fex A1 x A2;
  let B1 := fresh "B" in let B2 := fresh "C" in fdestr A2 B1 B2; fdestr B1 Hsx Hw;
  let A3 := fresh "A" in fex B2 g A3; fdestr A3 Hg Hi.
Local Ltac inv_unpack H Hf Hidx Hval Hcls :=
  unfold Inv in H; let A1 := fresh "A" in let A2 := fresh "C" in
  fdestr H A1 Hcls; fdestr A1 A2 Hval; fdestr A2 Hf Hidx.

(** introduction rules *)
Lemma hl_t1_intro {G} F i v s t x y g r : G ⊢C App0 F s x -> G ⊢C App0 F t y -> G ⊢C NumF 1 g ->
  G ⊢C OP0 s t r -> G ⊢C OP0 g r i -> G ⊢C OP0 x y v -> G ⊢C HPairT F i v.
Proof.
  intros H1 H2 H3 H4 H5 H6. unfold HPairT. fexists s. fexists t. fexists x. fexists y.
  fsplit; [fsplit; assumption|]. fexists g. fexists r. fsplit; [fsplit; [fsplit|]|]; assumption.
Qed.
Lemma hl_t2_intro {G} c F i v s x g : G ⊢C App0 F s x -> G ⊢C CanW c x v -> G ⊢C NumF 2 g -> G ⊢C OP0 g s i ->
  G ⊢C HSkT c F i v.
Proof.
  intros H1 H2 H3 H4. unfold HSkT. fexists s. fexists x. fsplit; [fsplit; assumption|].
  fexists g. fsplit; assumption.
Qed.
Lemma hl_pe_intro {G} F q s t x y g r i v : G ⊢C App0 F s x -> G ⊢C App0 F t y -> G ⊢C NumF 1 g ->
  G ⊢C OP0 s t r -> G ⊢C OP0 g r i -> G ⊢C OP0 x y v -> G ⊢C OP0 i v q -> G ⊢C PairE F q.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7. unfold PairE. fexists s. fexists t. fexists x. fexists y.
  fsplit; [fsplit; assumption|]. fexists g. fexists r. fexists i. fexists v.
  fsplit; [fsplit; [fsplit; [fsplit|]|]|]; assumption.
Qed.
Lemma hl_pq_intro {G} p1 p2 q s t x y g r i v : G ⊢C OP0 s x p1 -> G ⊢C OP0 t y p2 -> G ⊢C NumF 1 g ->
  G ⊢C OP0 s t r -> G ⊢C OP0 g r i -> G ⊢C OP0 x y v -> G ⊢C OP0 i v q -> G ⊢C PQ p1 p2 q.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7. unfold PQ. fexists s. fexists x. fexists t. fexists y.
  fsplit; [fsplit; assumption|]. fexists g. fexists r. fexists i. fexists v.
  fsplit; [fsplit; [fsplit; [fsplit|]|]|]; assumption.
Qed.
Lemma hl_sk_intro {G} c F q s x w g i : G ⊢C App0 F s x -> G ⊢C CanW c x w -> G ⊢C NumF 2 g ->
  G ⊢C OP0 g s i -> G ⊢C OP0 i w q -> G ⊢C SkE c F q.
Proof.
  intros H1 H2 H3 H4 H5. unfold SkE. fexists s. fexists x. fsplit; [exact H1|]. fexists w. fsplit; [exact H2|].
  fexists g. fexists i. fsplit; [fsplit|]; assumption.
Qed.
Lemma hl_sq_intro {G} c p q s x w g i : G ⊢C OP0 s x p -> G ⊢C CanW c x w -> G ⊢C NumF 2 g ->
  G ⊢C OP0 g s i -> G ⊢C OP0 i w q -> G ⊢C SQ c p q.
Proof.
  intros H1 H2 H3 H4 H5. unfold SQ. fexists s. fexists x. fsplit; [exact H1|]. fexists w. fsplit; [exact H2|].
  fexists g. fexists i. fsplit; [fsplit|]; assumption.
Qed.

Lemma hl_t1_sub {G} F F' i v : G ⊢C Sub0 F F' -> G ⊢C HPairT F i v -> G ⊢C HPairT F' i v.
Proof.
  intros Hs H. t1_unpack H s t x y g r Hsx Hty Hg Hr Hi Hv.
  exact (hl_t1_intro F' i v s t x y g r (hl_app_sub F F' s x Hs Hsx) (hl_app_sub F F' t y Hs Hty) Hg Hr Hi Hv).
Qed.
Lemma hl_t2_sub {G} c F F' i v : G ⊢C Sub0 F F' -> G ⊢C HSkT c F i v -> G ⊢C HSkT c F' i v.
Proof.
  intros Hs H. t2_unpack H s x g Hsx Hw Hg Hi.
  exact (hl_t2_intro c F' i v s x g (hl_app_sub F F' s x Hs Hsx) Hw Hg Hi).
Qed.

(** ** The step NxH *)
Lemma hl_nxh_iff {G} c F F' q : G ⊢C NxH c F F' -> G ⊢C q ∈' F' ↔ (q ∈' F ∨ PairE F q) ∨ SkE c F q.
Proof. intros H. unfold NxH in H. finst H q. exact H. Qed.
Lemma hl_nxh_in {G} c F F' q : G ⊢C NxH c F F' -> G ⊢C q ∈' F -> G ⊢C q ∈' F'.
Proof. intros H Hq. apply (iff_r _ _ _ (hl_nxh_iff c F F' q H)). fleft. fleft. exact Hq. Qed.
Lemma hl_nxh_pe {G} c F F' q : G ⊢C NxH c F F' -> G ⊢C PairE F q -> G ⊢C q ∈' F'.
Proof. intros H Hq. apply (iff_r _ _ _ (hl_nxh_iff c F F' q H)). fleft. fright. exact Hq. Qed.
Lemma hl_nxh_sk {G} c F F' q : G ⊢C NxH c F F' -> G ⊢C SkE c F q -> G ⊢C q ∈' F'.
Proof. intros H Hq. apply (iff_r _ _ _ (hl_nxh_iff c F F' q H)). fright. exact Hq. Qed.
Lemma hl_nxh_el {G} c F F' q : G ⊢C NxH c F F' -> G ⊢C q ∈' F' -> G ⊢C (q ∈' F ∨ PairE F q) ∨ SkE c F q.
Proof. intros H Hq. exact (iff_l _ _ _ (hl_nxh_iff c F F' q H) Hq). Qed.
Lemma hl_nxh_sub {G} c F F' : G ⊢C NxH c F F' -> G ⊢C Sub0 F F'.
Proof. intros H. unfold Sub0. fall q. fintro Hq. exact (hl_nxh_in c F F' q H Hq). Qed.

Lemma hl_nxh_app {G} (HG : incl ZF0base G) (HX : WOx G) c F F' i v :
  G ⊢C NxH c F F' -> G ⊢C App0 F' i v -> G ⊢C (App0 F i v ∨ HPairT F i v) ∨ HSkT c F i v.
Proof.
  intros H Ha. unfold App0 in Ha. fex Ha q Hq. fdestr Hq Hq1 Hq2.
  pose proof (hl_nxh_el c F F' q H Hq1) as C. fcases C C1 C2; [fcases C1 C3 C4|].
  - fleft. fleft. exact (app0_intro_g F i v q Hq2 C3).
  - pe_unpack C4 s t x y g r i' v' Hsx Hty Hg Hr Hi Hv Hq'.
    pose proof (Z_wo.w_op0_inj HG HX i v i' v' q Hq2 Hq') as E. fdestr E E1 E2.
    frew_in E1 (OP0 g`[↑] r`[↑] $0) Hi. frew_in E2 (OP0 x`[↑] y`[↑] $0) Hv.
    fleft. fright. exact (hl_t1_intro F i v s t x y g r Hsx Hty Hg Hr Hi Hv).
  - sk_unpack C2 s x w g i' Hsx Hw Hg Hi Hq'.
    pose proof (Z_wo.w_op0_inj HG HX i v i' w q Hq2 Hq') as E. fdestr E E1 E2.
    frew_in E1 (OP0 g`[↑] s`[↑] $0) Hi. frew_in E2 (CanW c x`[↑] $0) Hw.
    fright. exact (hl_t2_intro c F i v s x g Hsx Hw Hg Hi).
Qed.

Lemma hl_app_t1 {G} (HG : incl ZF0base G) (HX : WOx G) c F F' i v :
  G ⊢C NxH c F F' -> G ⊢C HPairT F i v -> G ⊢C App0 F' i v.
Proof.
  intros H H1. t1_unpack H1 s t x y g r Hsx Hty Hg Hr Hi Hv.
  fobtain (Z_wo.w_op0_ex HG HX i v) as q Hq.
  apply (app0_intro_g F' i v q Hq). apply (hl_nxh_pe c F F' q H).
  exact (hl_pe_intro F q s t x y g r i v Hsx Hty Hg Hr Hi Hv Hq).
Qed.
Lemma hl_app_t2 {G} (HG : incl ZF0base G) (HX : WOx G) c F F' i v :
  G ⊢C NxH c F F' -> G ⊢C HSkT c F i v -> G ⊢C App0 F' i v.
Proof.
  intros H H1. t2_unpack H1 s x g Hsx Hw Hg Hi.
  fobtain (Z_wo.w_op0_ex HG HX i v) as q Hq.
  apply (app0_intro_g F' i v q Hq). apply (hl_nxh_sk c F F' q H).
  exact (hl_sk_intro c F q s x v g i Hsx Hw Hg Hi Hq).
Qed.

(** ** Tags and single-valuedness *)
Lemma hl_tag {G} (HG : incl ZF0base G) (HX : WOx G) k l g r g' r' i :
  k <> l -> G ⊢C NumF k g -> G ⊢C OP0 g r i -> G ⊢C NumF l g' -> G ⊢C OP0 g' r' i -> G ⊢C ⊥.
Proof.
  intros Hkl H1 H2 H3 H4. pose proof (Z_wo.w_op0_inj HG HX g r g' r' i H2 H4) as E.
  exact (hl_num_neq HG HX k l g g' Hkl H1 H3 (CE1 E)).
Qed.


Lemma hl_t1t1 {G} (HG : incl ZF0base G) (HX : WOx G) F i v v' : G ⊢C Fun0 F -> G ⊢C HPairT F i v -> G ⊢C HPairT F i v' -> G ⊢C v ≡' v'.
Proof.
  intros Hf H1 H2. t1_unpack H1 s t x y g r Hsx Hty Hg Hr Hi Hv.
  t1_unpack H2 s' t' x' y' g' r' Hsx' Hty' Hg' Hr' Hi' Hv'.
  pose proof (Z_wo.w_op0_inj HG HX g r g' r' i Hi Hi') as E. fdestr E E1 E2.
  frew_in E2 (OP0 s'`[↑] t'`[↑] $0) Hr'.
  pose proof (Z_wo.w_op0_inj HG HX s t s' t' r Hr Hr') as E'. fdestr E' E3 E4.
  frew_in E3 (App0 F`[↑] $0 x'`[↑]) Hsx'. frew_in E4 (App0 F`[↑] $0 y'`[↑]) Hty'.
  pose proof (Z_wo.w_fun0_app HG HX F s x x' Hf Hsx Hsx') as Exx.
  pose proof (Z_wo.w_fun0_app HG HX F t y y' Hf Hty Hty') as Eyy.
  frew_in Exx (OP0 $0 y'`[↑] v'`[↑]) Hv'. frew_in Eyy (OP0 x`[↑] $0 v'`[↑]) Hv'.
  exact (Z_wo.w_op0_unique HG HX x y v v' Hv Hv').
Qed.

Lemma hl_t2t2 {G} (HG : incl ZF0base G) (HX : WOx G) c F i v v' : G ⊢C Fun0 F -> G ⊢C HSkT c F i v -> G ⊢C HSkT c F i v' -> G ⊢C v ≡' v'.
Proof.
  intros Hf H1 H2. t2_unpack H1 s x g Hsx Hw Hg Hi. t2_unpack H2 s' x' g' Hsx' Hw' Hg' Hi'.
  pose proof (Z_wo.w_op0_inj HG HX g s g' s' i Hi Hi') as E. fdestr E E1 E2.
  frew_in E2 (App0 F`[↑] $0 x'`[↑]) Hsx'.
  pose proof (Z_wo.w_fun0_app HG HX F s x x' Hf Hsx Hsx') as Exx.
  frew_in Exx (CanW c $0 v'`[↑]) Hw'.
  exact (canw_unique_g HG HX c x v v' Hw Hw').
Qed.

Lemma hl_t1t2 {G} (HG : incl ZF0base G) (HX : WOx G) c F i v v' : G ⊢C HPairT F i v -> G ⊢C HSkT c F i v' -> G ⊢C ⊥.
Proof.
  intros H1 H2. t1_unpack H1 s t x y g r Hsx Hty Hg Hr Hi Hv. t2_unpack H2 s' x' g' Hsx' Hw' Hg' Hi'.
  exact (hl_tag HG HX 1 2 g r g' s' i ltac:(lia) Hg Hi Hg' Hi').
Qed.

Lemma hl_t0t1 {G} (HG : incl ZF0base G) (HX : WOx G) H0 (Ht0 : G ⊢C ∀ (∀ (App0 H0`[↑]`[↑] $1 $0 → ∃ (∃ (NumF 0 $1 ∧ OP0 $1 $0 $3))))) F i v v' : G ⊢C App0 H0 i v -> G ⊢C HPairT F i v' -> G ⊢C ⊥.
Proof.
  intros H1 H2. pose proof Ht0 as K. finst K i v. fmp K H1. fex K z Hz. fex Hz j Hj. fdestr Hj Hz0 Hzj.
  t1_unpack H2 s t x y g r Hsx Hty Hg Hr Hi Hv.
  exact (hl_tag HG HX 0 1 z j g r i ltac:(lia) Hz0 Hzj Hg Hi).
Qed.

Lemma hl_t0t2 {G} (HG : incl ZF0base G) (HX : WOx G) c H0 (Ht0 : G ⊢C ∀ (∀ (App0 H0`[↑]`[↑] $1 $0 → ∃ (∃ (NumF 0 $1 ∧ OP0 $1 $0 $3))))) F i v v' : G ⊢C App0 H0 i v -> G ⊢C HSkT c F i v' -> G ⊢C ⊥.
Proof.
  intros H1 H2. pose proof Ht0 as K. finst K i v. fmp K H1. fex K z Hz. fex Hz j Hj. fdestr Hj Hz0 Hzj.
  t2_unpack H2 s x g Hsx Hw Hg Hi.
  exact (hl_tag HG HX 0 2 z j g s i ltac:(lia) Hz0 Hzj Hg Hi).
Qed.


Lemma hl_cls_use {G} c F H0 i v : G ⊢C Cls c F H0 -> G ⊢C App0 F i v ->
  G ⊢C (App0 H0 i v ∨ HPairT F i v) ∨ HSkT c F i v.
Proof. intros H Ha. unfold Cls in H. finst H i v. exact (IE H Ha). Qed.

Lemma hl_app_t1_eq {G} (HG : incl ZF0base G) (HX : WOx G) c H0 F i v v'
  (Ht0 : G ⊢C ∀ (∀ (App0 H0`[↑]`[↑] $1 $0 → ∃ (∃ (NumF 0 $1 ∧ OP0 $1 $0 $3))))) :
  G ⊢C Fun0 F -> G ⊢C Cls c F H0 -> G ⊢C App0 F i v -> G ⊢C HPairT F i v' -> G ⊢C v ≡' v'.
Proof.
  intros Hf Hc Ha H1. pose proof (hl_cls_use c F H0 i v Hc Ha) as C. fcases C C1 C2; [fcases C1 C3 C4|].
  - fabsurd. exact (hl_t0t1 HG HX H0 Ht0 F i v v' C3 H1).
  - exact (hl_t1t1 HG HX F i v v' Hf C4 H1).
  - fabsurd. exact (hl_t1t2 HG HX c F i v' v H1 C2).
Qed.

Lemma hl_app_t2_eq {G} (HG : incl ZF0base G) (HX : WOx G) c H0 F i v v'
  (Ht0 : G ⊢C ∀ (∀ (App0 H0`[↑]`[↑] $1 $0 → ∃ (∃ (NumF 0 $1 ∧ OP0 $1 $0 $3))))) :
  G ⊢C Fun0 F -> G ⊢C Cls c F H0 -> G ⊢C App0 F i v -> G ⊢C HSkT c F i v' -> G ⊢C v ≡' v'.
Proof.
  intros Hf Hc Ha H1. pose proof (hl_cls_use c F H0 i v Hc Ha) as C. fcases C C1 C2; [fcases C1 C3 C4|].
  - fabsurd. exact (hl_t0t2 HG HX c H0 Ht0 F i v v' C3 H1).
  - fabsurd. exact (hl_t1t2 HG HX c F i v v' C4 H1).
  - exact (hl_t2t2 HG HX c F i v v' Hf C2 H1).
Qed.

(** ordered pairs of elements of L are in L *)
Lemma hl_op_L {G} (HG : incl ZF0base G) (HX : WOx G) x y p :
  G ⊢C InL x -> G ⊢C InL y -> G ⊢C OP0 x y p -> G ⊢C InL p.
Proof.
  intros Hx Hy Hp. pose proof (WOx_L _ HX) as HL. pose proof (hl_cl HX) as HCl.
  destruct HX as (HR & HOm & HW).
  rewrite InL_eq in Hx. fex Hx a Ha. fex Ha Ya HYa. fdestr HYa HY1 HxY. fdestr HY1 Oa HLa.
  pose proof (L_above_g HG HR HOm HL y a Hy Oa) as T. fex T e He. fex He Ye HYe.
  fdestr HYe HY2 HyY. fdestr HY2 HY3 HLe. fdestr HY3 Oe Hae.
  pose proof (LL_sub_g HG HR HOm HL e a Ye Ya Oe Oa Hae HLe HLa) as Hsub.
  pose proof (Z_L.sub_use Ya Ye x Hsub HxY) as HxYe.
  pose proof (Z_L.w_succ0_ex HG HR HOm HL e) as T. fex T s Hs.
  pose proof (Z_L.w_ord_succ HG HR HOm HL e s Oe Hs) as Os.
  pose proof (LL_ex_g HG HR HOm HL s Os) as T. fex T Ys HYs.
  pose proof (LL_succ_g HG HR HOm HL e s Ye Ys Oe Hs HLe HYs) as HD1.
  pose proof (Z_L.w_succ0_ex HG HR HOm HL s) as T. fex T s2 Hs2.
  pose proof (Z_L.w_ord_succ HG HR HOm HL s s2 Os Hs2) as Os2.
  pose proof (LL_ex_g HG HR HOm HL s2 Os2) as T. fex T Ys2 HYs2.
  pose proof (LL_succ_g HG HR HOm HL s s2 Ys Ys2 Os Hs2 HYs HYs2) as HD2.
  pose proof (AC_univ.pair_def HG HR HOm HCl Ye Ys x x HD1 HxYe HxYe) as T. fex T Xa HXa. fdestr HXa HXa1 HXa2.
  pose proof (AC_univ.pair_def HG HR HOm HCl Ye Ys x y HD1 HxYe HyY) as T. fex T Xb HXb. fdestr HXb HXb1 HXb2.
  pose proof (AC_univ.pair_def HG HR HOm HCl Ys Ys2 Xa Xb HD2 HXa1 HXb1) as T. fex T Xp HXp. fdestr HXp HXp1 HXp2.
  fassert HSa : (Sing0 x Xa).
  { unfold Pair0 in HXa2. fdestr HXa2 H12 H3. fdestr H12 H1 H2. unfold Sing0. fsplit; [exact H1|].
    fall z. fintro Hz. finst H3 z. fmp H3 Hz. fcases H3 C1 C2; [exact C1|exact C2]. }
  fassert Hop : (OP0 x y Xp).
  { pose proof HXp2 as T. unfold Pair0 in T. fdestr T T12 T3. fdestr T12 U1 U2.
    unfold OP0. fsplit; [fsplit|].
    - fexists Xa. fsplit; [exact U1|exact HSa].
    - fexists Xb. fsplit; [exact U2|exact HXb2].
    - fall z. fintro Hz. finst T3 z. fmp T3 Hz. fcases T3 C1 C2.
      + fleft. frew C1 (Sing0 x`[↑] $0). exact HSa.
      + fright. frew C2 (Pair0 x`[↑] y`[↑] $0). exact HXb2. }
  pose proof (u_op0_unique HG HR HOm HCl x y p Xp Hp Hop) as E.
  exact (InL_intro s2 Ys2 p Os2 HYs2 (elem_l HG Xp p Ys2 (eq_sym' HG _ _ E) HXp1)).
Qed.

(** ** Set existence of the step *)
Lemma hl_in_cw {G} c : incl (Ax_hull c) G -> incl (Ax_cw c) G.
Proof. intros H a Ha. apply H. unfold Ax_hull. rewrite !in_app_iff. now left. Qed.
Lemma hl_in_rec {G} c : incl (Ax_hull c) G -> incl (Ax_rec (phH c)) G.
Proof. intros H a Ha. apply H. unfold Ax_hull. rewrite !in_app_iff. right. now left. Qed.
Lemma hl_in_hi {G} c a : incl (Ax_hull c) G -> In a (hull_insts c) -> In a G.
Proof. intros H Ha. apply H. unfold Ax_hull. rewrite !in_app_iff. right. now right. Qed.

Lemma hl_pq_fun {G} (HG : incl ZF0base G) (HX : WOx G) p1 p2 q q' :
  G ⊢C PQ p1 p2 q -> G ⊢C PQ p1 p2 q' -> G ⊢C q ≡' q'.
Proof.
  intros H1 H2. pq_unpack H1 s x t y g r i v Hsx Hty Hg Hr Hi Hv Hq.
  pq_unpack H2 s' x' t' y' g' r' i' v' Hsx' Hty' Hg' Hr' Hi' Hv' Hq'.
  pose proof (Z_wo.w_op0_inj HG HX s x s' x' p1 Hsx Hsx') as E1. fdestr E1 Es Exx.
  pose proof (Z_wo.w_op0_inj HG HX t y t' y' p2 Hty Hty') as E2. fdestr E2 Et Eyy.
  pose proof (hl_num_unique 1 HG HX g g' Hg Hg') as Eg.
  frew_in Es (OP0 $0 t'`[↑] r'`[↑]) Hr'. frew_in Et (OP0 s`[↑] $0 r'`[↑]) Hr'.
  pose proof (Z_wo.w_op0_unique HG HX s t r r' Hr Hr') as Er.
  frew_in Eg (OP0 $0 r'`[↑] i'`[↑]) Hi'. frew_in Er (OP0 g`[↑] $0 i'`[↑]) Hi'.
  pose proof (Z_wo.w_op0_unique HG HX g r i i' Hi Hi') as Ei.
  frew_in Exx (OP0 $0 y'`[↑] v'`[↑]) Hv'. frew_in Eyy (OP0 x`[↑] $0 v'`[↑]) Hv'.
  pose proof (Z_wo.w_op0_unique HG HX x y v v' Hv Hv') as Ev.
  frew_in Ei (OP0 $0 v'`[↑] q'`[↑]) Hq'. frew_in Ev (OP0 i`[↑] $0 q'`[↑]) Hq'.
  exact (Z_wo.w_op0_unique HG HX i v q q' Hq Hq').
Qed.

Lemma hl_sq_fun {G} (HG : incl ZF0base G) (HX : WOx G) c p q q' :
  G ⊢C SQ c p q -> G ⊢C SQ c p q' -> G ⊢C q ≡' q'.
Proof.
  intros H1 H2. sq_unpack H1 s x w g i Hsx Hw Hg Hi Hq. sq_unpack H2 s' x' w' g' i' Hsx' Hw' Hg' Hi' Hq'.
  pose proof (Z_wo.w_op0_inj HG HX s x s' x' p Hsx Hsx') as E1. fdestr E1 Es Exx.
  frew_in Exx (CanW c $0 w'`[↑]) Hw'.
  pose proof (canw_unique_g HG HX c x w w' Hw Hw') as Ew.
  pose proof (hl_num_unique 2 HG HX g g' Hg Hg') as Eg.
  frew_in Eg (OP0 $0 s'`[↑] i'`[↑]) Hi'. frew_in Es (OP0 g`[↑] $0 i'`[↑]) Hi'.
  pose proof (Z_wo.w_op0_unique HG HX g s i i' Hi Hi') as Ei.
  frew_in Ei (OP0 $0 w'`[↑] q'`[↑]) Hq'. frew_in Ew (OP0 i`[↑] $0 q'`[↑]) Hq'.
  exact (Z_wo.w_op0_unique HG HX i w q q' Hq Hq').
Qed.

Lemma hl_nxh_ex {G} (HG : incl ZF0base G) (HX : WOx G) c (Hc : fb 2 c) (HC : incl (Ax_hull c) G) F :
  G ⊢C ∃ NxH c F`[↑] $0.
Proof.
  assert (Hi1 : In (forall_times 1 (ax_rep' (PQ $2 $0 $1))) G)
    by (apply (hl_in_hi c _ HC); unfold hull_insts; left; reflexivity).
  assert (Hi2 : In (forall_times 1 (ax_rep' (UF (PZ $2 $1 $0)))) G)
    by (apply (hl_in_hi c _ HC); unfold hull_insts; right; left; reflexivity).
  assert (Hi3 : In (forall_times 0 (ax_rep' (SQ c $0 $1))) G)
    by (apply (hl_in_hi c _ HC); unfold hull_insts; right; right; left; reflexivity).
  assert (Hex : forall G' x, incl G G' ->
    G' ⊢C ∃ ∀ ($0 ∈' $1 ↔ (PZ $2 $1 $0)[$0 .: x`[↑]`[↑] .: (fun k => ((F .: var) k)`[↑]`[↑])])).
  { intros G' x Hinc. pose proof (incl_tran HG Hinc) as HG'. pose proof (hl_wox_incl Hinc HX) as HX'.
    assert (Hfun : forall a b b', G' ⊢C (PQ $2 $0 $1)[a .: b .: (x .: var)] → (PQ $2 $0 $1)[a .: b' .: (x .: var)] → b ≡' b').
    { intros a b b'. simp. fintro H1. fintro H2. exact (hl_pq_fun HG' HX' x a b b' H1 H2). }
    pose proof (rep_use G' 1 (PQ $2 $0 $1) (x .: var) F (Hinc _ Hi1) ltac:(unfold PQ; fbcomp) Hfun) as R.
    simp_in R. simp. unfold PZ. simp. exact R. }
  pose proof (uimg HG 1 (PZ $2 $1 $0) (F .: var) F Hi2 ltac:(unfold PZ, PQ; fbcomp) Hex) as U. simp_in U.
  assert (Hfun3 : forall a b b', G ⊢C (SQ c $0 $1)[a .: b .: var] → (SQ c $0 $1)[a .: b' .: var] → b ≡' b').
  { intros a b b'. simp. fintro H1. fintro H2. exact (hl_sq_fun HG HX c a b b' H1 H2). }
  pose proof (rep_use G 0 (SQ c $0 $1) var F Hi3 (hl_fb_SQ c Hc) Hfun3) as R3. simp_in R3.
  clear Hex Hfun3.
  fex U P HPd. fex R3 Sk HSd.
  fobtain (bun_ex HG F P) as U1 HU1. fobtain (bun_ex HG U1 Sk) as F' HaF'.
  fexists F'. unfold NxH. fall q. fsplit.
  - fintro Hq. pose proof (bun_el HG U1 Sk F' q HaF' Hq) as C. fcases C C1 C2.
    + pose proof (bun_el HG F P U1 q HU1 C1) as C'. fcases C' C3 C4.
      * fleft. fleft. exact C3.
      * fleft. fright. finst HPd q. pose proof (iff_l _ _ _ HPd C4) as T. fex T p1 Hp1. fdestr Hp1 Hp1F Hz.
        unfold PZ in Hz. fex Hz p2 Hp2. fdestr Hp2 Hp2F Hpq.
        pq_unpack Hpq s x t y g r i v Hsx Hty Hg Hr Hi Hv Hq'.
        exact (hl_pe_intro F q s t x y g r i v (app0_intro_g F s x p1 Hsx Hp1F) (app0_intro_g F t y p2 Hty Hp2F)
                 Hg Hr Hi Hv Hq').
    + fright. finst HSd q. pose proof (iff_l _ _ _ HSd C2) as T. fex T p Hp. fdestr Hp HpF Hsq.
      sq_unpack Hsq s x w g i Hsx Hw Hg Hi Hq'.
      exact (hl_sk_intro c F q s x w g i (app0_intro_g F s x p Hsx HpF) Hw Hg Hi Hq').
  - fintro Hq. fcases Hq C1 C2; [fcases C1 C3 C4|].
    + apply (bun_in HG U1 Sk F' q HaF'). fleft. apply (bun_in HG F P U1 q HU1). fleft. exact C3.
    + apply (bun_in HG U1 Sk F' q HaF'). fleft. apply (bun_in HG F P U1 q HU1). fright.
      pe_unpack C4 s t x y g r i v Hsx Hty Hg Hr Hi Hv Hq'.
      unfold App0 in Hsx, Hty. fex Hsx p1 Hp1. fdestr Hp1 Hp1F Hp1o. fex Hty p2 Hp2. fdestr Hp2 Hp2F Hp2o.
      finst HPd q. apply (iff_r _ _ _ HPd). fexists p1. fsplit; [exact Hp1F|].
      unfold PZ. fexists p2. fsplit; [exact Hp2F|].
      exact (hl_pq_intro p1 p2 q s t x y g r i v Hp1o Hp2o Hg Hr Hi Hv Hq').
    + apply (bun_in HG U1 Sk F' q HaF'). fright.
      sk_unpack C2 s x w g i Hsx Hw Hg Hi Hq'.
      unfold App0 in Hsx. fex Hsx p Hp. fdestr Hp HpF Hpo.
      finst HSd q. apply (iff_r _ _ _ HSd). fexists p. fsplit; [exact HpF|].
      exact (hl_sq_intro c p q s x w g i Hpo Hw Hg Hi Hq').
Qed.

Lemma hl_nxh_unique {G} (HG : incl ZF0base G) c F F1 F2 :
  G ⊢C NxH c F F1 -> G ⊢C NxH c F F2 -> G ⊢C F1 ≡' F2.
Proof. intros H1 H2. unfold NxH in H1, H2. exact (ext_char HG _ F1 F2 H1 H2). Qed.

Lemma hl_gtot {G} (HG : incl ZF0base G) (HX : WOx G) c (Hc : fb 2 c) (HC : incl (Ax_hull c) G) :
  G ⊢C Std_setrec.GTot (phH c).
Proof. unfold Std_setrec.GTot. fall F. rewrite hl_rel2. exact (hl_nxh_ex HG HX c Hc HC F). Qed.

Lemma hl_gfun {G} (HG : incl ZF0base G) c : G ⊢C Std_setrec.GFun (phH c).
Proof.
  unfold Std_setrec.GFun. fall F. fall F1. fall F2. rewrite !hl_rel2. fintro H1. fintro H2.
  exact (hl_nxh_unique HG c F F1 F2 H1 H2).
Qed.

(** ** The invariant *)
Lemma hl_inv_base {G} c H0 I : G ⊢C Fun0 H0 -> G ⊢C ∀ (∀ (App0 H0`[↑]`[↑] $1 $0 → $1 ∈' I`[↑]`[↑] ∧ Lform)) ->
  G ⊢C Inv c H0 H0 I.
Proof.
  intros Hf Hb. unfold Inv. fsplit; [fsplit; [fsplit|]|].
  - exact Hf.
  - fall i. fall v. fintro Ha. pose proof Hb as K. finst K i v. exact (CE1 (IE K Ha)).
  - fall i. fall v. fintro Ha. pose proof Hb as K. finst K i v. pose proof (CE2 (IE K Ha)) as HvL.
    rewrite InL_eq. exact HvL.
  - unfold Cls. fall i. fall v. fintro Ha. fleft. fleft. exact Ha.
Qed.

Lemma hl_inv_step {G} (HG : incl ZF0base G) (HX : WOx G) c H0 I F F'
  (Ht0 : G ⊢C ∀ (∀ (App0 H0`[↑]`[↑] $1 $0 → ∃ (∃ (NumF 0 $1 ∧ OP0 $1 $0 $3)))))
  (HIop : G ⊢C ∀ ($0 ∈' I`[↑] → ∀ ($0 ∈' I`[↑]`[↑] → ∀ (OP0 $2 $1 $0 → $0 ∈' I`[↑]`[↑]`[↑]))))
  (HI1 : G ⊢C ∀ (NumF 1 $0 → $0 ∈' I`[↑])) (HI2 : G ⊢C ∀ (NumF 2 $0 → $0 ∈' I`[↑])) :
  G ⊢C Inv c F H0 I -> G ⊢C NxH c F F' -> G ⊢C Inv c F' H0 I.
Proof.
  intros HInv HN. inv_unpack HInv Hf Hidx Hval Hcls.
  pose proof (hl_nxh_sub c F F' HN) as Hsub.
  unfold Inv. fsplit; [fsplit; [fsplit|]|].
  - apply (fun0_intro HG (hl_P HX)).
    + apply (isrel0_intro HG (hl_P HX)). fall q. fintro Hq.
      pose proof (hl_nxh_el c F F' q HN Hq) as C. fcases C C1 C2; [fcases C1 C3 C4|].
      * unfold Fun0 in Hf. exact (Z_wo.w_isrel0_el HG HX F q (CE1 Hf) C3).
      * pe_unpack C4 s t x y g r i v Hsx Hty Hg Hr Hi Hv Hq'. fexists i. fexists v. exact Hq'.
      * sk_unpack C2 s x w g i Hsx Hw Hg Hi Hq'. fexists i. fexists w. exact Hq'.
    + fall i. fall v. fall v'. fintro H1. fintro H2.
      pose proof (hl_nxh_app HG HX c F F' i v HN H1) as C. pose proof (hl_nxh_app HG HX c F F' i v' HN H2) as D.
      fcases C C1 C2; [fcases C1 C3 C4|]; fcases D D1 D2; try fcases D1 D3 D4.
      * exact (Z_wo.w_fun0_app HG HX F i v v' Hf C3 D3).
      * exact (hl_app_t1_eq HG HX c H0 F i v v' Ht0 Hf Hcls C3 D4).
      * exact (hl_app_t2_eq HG HX c H0 F i v v' Ht0 Hf Hcls C3 D2).
      * exact (eq_sym' HG _ _ (hl_app_t1_eq HG HX c H0 F i v' v Ht0 Hf Hcls D3 C4)).
      * exact (hl_t1t1 HG HX F i v v' Hf C4 D4).
      * fabsurd. exact (hl_t1t2 HG HX c F i v v' C4 D2).
      * exact (eq_sym' HG _ _ (hl_app_t2_eq HG HX c H0 F i v' v Ht0 Hf Hcls D3 C2)).
      * fabsurd. exact (hl_t1t2 HG HX c F i v' v D4 C2).
      * exact (hl_t2t2 HG HX c F i v v' Hf C2 D2).
  - fall i. fall v. fintro Ha. pose proof (hl_nxh_app HG HX c F F' i v HN Ha) as C.
    fcases C C1 C2; [fcases C1 C3 C4|].
    + pose proof Hidx as K. finst K i v. exact (IE K C3).
    + t1_unpack C4 s t x y g r Hsx Hty Hg Hr Hi Hv.
      pose proof Hidx as K1. finst K1 s x. fmp K1 Hsx.
      pose proof Hidx as K2. finst K2 t y. fmp K2 Hty.
      pose proof HIop as K3. finst K3 s. fmp K3 K1. finst K3 t. fmp K3 K2. finst K3 r. fmp K3 Hr.
      pose proof HI1 as K4. finst K4 g. fmp K4 Hg.
      pose proof HIop as K5. finst K5 g. fmp K5 K4. finst K5 r. fmp K5 K3. finst K5 i. exact (IE K5 Hi).
    + t2_unpack C2 s x g Hsx Hw Hg Hi.
      pose proof Hidx as K1. finst K1 s x. fmp K1 Hsx.
      pose proof HI2 as K4. finst K4 g. fmp K4 Hg.
      pose proof HIop as K5. finst K5 g. fmp K5 K4. finst K5 s. fmp K5 K1. finst K5 i. exact (IE K5 Hi).
  - fall i. fall v. fintro Ha. pose proof (hl_nxh_app HG HX c F F' i v HN Ha) as C.
    fcases C C1 C2; [fcases C1 C3 C4|].
    + pose proof Hval as K. finst K i v. exact (IE K C3).
    + t1_unpack C4 s t x y g r Hsx Hty Hg Hr Hi Hv.
      pose proof Hval as K1. finst K1 s x. fmp K1 Hsx. pose proof Hval as K2. finst K2 t y. fmp K2 Hty.
      exact (hl_op_L HG HX x y v K1 K2 Hv).
    + t2_unpack C2 s x g Hsx Hw Hg Hi. exact (canw_L_g HG HX c x v Hw).
  - unfold Cls. fall i. fall v. fintro Ha. pose proof (hl_nxh_app HG HX c F F' i v HN Ha) as C.
    fcases C C1 C2; [fcases C1 C3 C4|].
    + pose proof (hl_cls_use c F H0 i v Hcls C3) as D. fcases D D1 D2; [fcases D1 D3 D4|].
      * fleft. fleft. exact D3.
      * fleft. fright. exact (hl_t1_sub F F' i v Hsub D4).
      * fright. exact (hl_t2_sub c F F' i v Hsub D2).
    + fleft. fright. exact (hl_t1_sub F F' i v Hsub C4).
    + fright. exact (hl_t2_sub c F F' i v Hsub C2).
Qed.

(** ** Induction along ω *)
Lemma hl_ind {G} (HG : incl ZF0base G) (HX : WOx G) c (Hc : fb 2 c) (HC : incl (Ax_hull c) G) H0 I Fn w
  (Hf0 : G ⊢C Fun0 H0)
  (Hb0 : G ⊢C ∀ (∀ (App0 H0`[↑]`[↑] $1 $0 → $1 ∈' I`[↑]`[↑] ∧ Lform)))
  (Ht0 : G ⊢C ∀ (∀ (App0 H0`[↑]`[↑] $1 $0 → ∃ (∃ (NumF 0 $1 ∧ OP0 $1 $0 $3)))))
  (HIop : G ⊢C ∀ ($0 ∈' I`[↑] → ∀ ($0 ∈' I`[↑]`[↑] → ∀ (OP0 $2 $1 $0 → $0 ∈' I`[↑]`[↑]`[↑]))))
  (HI1 : G ⊢C ∀ (NumF 1 $0 → $0 ∈' I`[↑])) (HI2 : G ⊢C ∀ (NumF 2 $0 → $0 ∈' I`[↑])) :
  G ⊢C Om0 w -> G ⊢C Fun0 Fn -> G ⊢C Dom0 Fn w -> G ⊢C RecOK (SG (phH c)) H0 Fn ->
  G ⊢C ∀ ($0 ∈' w`[↑] → PInd c $0 Fn`[↑] H0`[↑] I`[↑]).
Proof.
  intros Hw Hfn Hdom Hrec.
  pose proof (WOx_L _ HX) as HL. pose proof HX as (HR & HOm & HW).
  pose proof (hl_in_rec c HC) as HIr.
  assert (Hi5 : In (forall_times 3 (ax_sep' (PInd c $0 $1 $2 $3))) G)
    by (apply (hl_in_hi c _ HC); unfold hull_insts; do 4 right; left; reflexivity).
  pose proof (sep_use _ 3 (PInd c $0 $1 $2 $3) (Fn .: H0 .: I .: var) w Hi5 (hl_fb_PInd c Hc)) as T. simp_in T.
  fex T X HXd.
  fassert Hsub : (Sub0 w X).
  { apply (Z_wo.w_om_ind HG HX w X Hw).
    - fall e. fintro He. pose proof HXd as K. finst K e. apply (iff_r _ _ _ K). clear K.
      fsplit; [exact (Z_wo.w_om_emp HG HX w e Hw He)|].
      unfold PInd. fall F. fintro HaF.
      pose proof (omrec_zero HG HR HOm HL (phH c) (fb_phH c Hc) HIr H0 Fn e F Hrec HaF He) as E.
      fsplit.
      + frew E (Inv c $0 H0`[↑] I`[↑]). exact (hl_inv_base c H0 I Hf0 Hb0).
      + fall n. fintro Hn. fabsurd. exact (Z_L.emp_use e n He Hn).
    - fall m. fintro Hm. fintro HmX. fall s. fintro Hs.
      pose proof HXd as K. finst K m. pose proof (CE2 (iff_l _ _ _ K HmX)) as Hpm. clear K.
      pose proof (Z_wo.w_om_succ HG HX w m s Hw Hm Hs) as Hsw.
      pose proof HXd as K. finst K s. apply (iff_r _ _ _ K). clear K. fsplit; [exact Hsw|].
      unfold PInd. fall F'. fintro HaF'.
      fobtain (Z_wo.w_dom0_app HG HX Fn w m Hdom Hm) as F HaF.
      unfold PInd in Hpm. finst Hpm F. fmp Hpm HaF. fdestr Hpm HinvF Hmono.
      pose proof (omrec_succ HG HR HOm HL (phH c) (fb_phH c Hc) HIr H0 Fn m s F F' Hfn Hrec HaF Hs HaF') as HN.
      rewrite hl_rel2 in HN.
      pose proof (hl_nxh_sub c F F' HN) as HFF.
      fsplit.
      + exact (hl_inv_step HG HX c H0 I F F' Ht0 HIop HI1 HI2 HinvF HN).
      + fall n. fintro Hn. fall u. fintro Hu.
        pose proof (Z_L.succ_el0 m s n Hs Hn) as C. fcases C C1 C2.
        * finst Hmono n. fmp Hmono C1. finst Hmono u. fmp Hmono Hu. exact (Z_L.sub_tr0 u F F' Hmono HFF).
        * frew_in C2 (App0 Fn`[↑] $0 u`[↑]) Hu.
          pose proof (Z_wo.w_fun0_app HG HX Fn m u F Hfn Hu HaF) as E.
          frew E (Sub0 $0 F'`[↑]). exact HFF. }
  fall m. fintro Hm. pose proof HXd as K. finst K m. exact (CE2 (iff_l _ _ _ K (Z_L.sub_use w X m Hsub Hm))).
Qed.

Lemma hl_inv_at {G} c H0 I Fn w n F : G ⊢C ∀ ($0 ∈' w`[↑] → PInd c $0 Fn`[↑] H0`[↑] I`[↑]) ->
  G ⊢C n ∈' w -> G ⊢C App0 Fn n F -> G ⊢C Inv c F H0 I.
Proof.
  intros Hind Hn HaF. pose proof Hind as K. finst K n. fmp K Hn. unfold PInd in K. finst K F. fmp K HaF.
  exact (CE1 K).
Qed.

Lemma hl_mono_at {G} c H0 I Fn w n m u u' : G ⊢C ∀ ($0 ∈' w`[↑] → PInd c $0 Fn`[↑] H0`[↑] I`[↑]) ->
  G ⊢C m ∈' w -> G ⊢C n ∈' m -> G ⊢C App0 Fn n u -> G ⊢C App0 Fn m u' -> G ⊢C Sub0 u u'.
Proof.
  intros Hind Hm Hn Hu Hu'. pose proof Hind as K. finst K m. fmp K Hm. unfold PInd in K. finst K u'. fmp K Hu'.
  pose proof (CE2 K) as K2. finst K2 n. fmp K2 Hn. finst K2 u. exact (IE K2 Hu).
Qed.

Lemma hl_common {G} (HG : incl ZF0base G) (HX : WOx G) c H0 I Fn w n m u u' :
  G ⊢C ∀ ($0 ∈' w`[↑] → PInd c $0 Fn`[↑] H0`[↑] I`[↑]) -> G ⊢C Om0 w -> G ⊢C Fun0 Fn ->
  G ⊢C n ∈' w -> G ⊢C m ∈' w -> G ⊢C App0 Fn n u -> G ⊢C App0 Fn m u' ->
  G ⊢C ∃ (∃ ($1 ∈' w`[↑]`[↑] ∧ App0 Fn`[↑]`[↑] $1 $0 ∧ Sub0 u`[↑]`[↑] $0 ∧ Sub0 u'`[↑]`[↑] $0)).
Proof.
  intros Hind Hw Hfn Hn Hm Hu Hu'. pose proof (Z_wo.w_om_ord HG HX w Hw) as Ow.
  pose proof (Z_wo.w_ord_el HG HX w n Ow Hn) as On. pose proof (Z_wo.w_ord_el HG HX w m Ow Hm) as Om.
  pose proof (Z_wo.w_ord_tri HG HX n m On Om) as C. fcases C C1 C2; [fcases C1 C3 C4|].
  - fexists m. fexists u'. fsplit; [fsplit; [fsplit|]|].
    + exact Hm.
    + exact Hu'.
    + exact (hl_mono_at c H0 I Fn w n m u u' Hind Hm C3 Hu Hu').
    + exact (Z_L.sub_refl0 u').
  - frew_in C4 (App0 Fn`[↑] $0 u`[↑]) Hu. pose proof (Z_wo.w_fun0_app HG HX Fn m u u' Hfn Hu Hu') as E.
    fexists m. fexists u'. fsplit; [fsplit; [fsplit|]|].
    + exact Hm.
    + exact Hu'.
    + frew E (Sub0 $0 u'`[↑]). exact (Z_L.sub_refl0 u').
    + exact (Z_L.sub_refl0 u').
  - fexists n. fexists u. fsplit; [fsplit; [fsplit|]|].
    + exact Hn.
    + exact Hu.
    + exact (Z_L.sub_refl0 u).
    + exact (hl_mono_at c H0 I Fn w m n u' u Hind Hn C2 Hu' Hu).
Qed.

Lemma hl_succ_at {G} (HG : incl ZF0base G) (HX : WOx G) c (Hc : fb 2 c) (HC : incl (Ax_hull c) G) H0 Fn w n F :
  G ⊢C Om0 w -> G ⊢C Fun0 Fn -> G ⊢C Dom0 Fn w -> G ⊢C RecOK (SG (phH c)) H0 Fn ->
  G ⊢C n ∈' w -> G ⊢C App0 Fn n F -> G ⊢C ∃ (∃ (App0 Fn`[↑]`[↑] $1 $0 ∧ NxH c F`[↑]`[↑] $0)).
Proof.
  intros Hw Hfn Hdom Hrec Hn HaF.
  pose proof (WOx_L _ HX) as HL. pose proof HX as (HR & HOm & HW).
  fobtain (Z_wo.w_succ0_ex HG HX n) as s Hs.
  pose proof (Z_wo.w_om_succ HG HX w n s Hw Hn Hs) as Hsw.
  fobtain (Z_wo.w_dom0_app HG HX Fn w s Hdom Hsw) as F' HaF'.
  pose proof (omrec_succ HG HR HOm HL (phH c) (fb_phH c Hc) (hl_in_rec c HC) H0 Fn n s F F' Hfn Hrec HaF Hs HaF') as HN.
  rewrite hl_rel2 in HN. fexists s. fexists F'. fsplit; assumption.
Qed.

(** ** H = ⋃ ran Fn and X = ran H *)
Definition URan (Fn H : term) : form := ∀ ($0 ∈' H`[↑] ↔ ∃ (∃ (App0 Fn`[↑]`[↑]`[↑] $1 $0 ∧ $2 ∈' $0))).
#[local] Arguments URan : simpl never.
Lemma URan_subst Fn H sg : (URan Fn H)[sg] = URan Fn`[sg] H`[sg].
Proof. psubst URan. Qed.
#[local] Hint Rewrite URan_subst : fsub.

Lemma hl_uran_ex {G} (HG : incl ZF0base G) (HX : WOx G) Fn : G ⊢C ∃ URan Fn`[↑] $0.
Proof.
  fobtain (union_ex HG Fn) as u1 Hu1. fobtain (union_ex HG u1) as u2 Hu2. fobtain (union_ex HG u2) as u3 Hu3.
  pose proof (sep_use _ 1 S_ran (fun _ => Fn) u3 (in_S_ran _ (hl_cl HX)) fb_S_ran) as T. unfold S_ran in T. simp_in T.
  fex T C HCC. fexists C. unfold URan. fall z. fsplit.
  - fintro Hz. finst HCC z. exact (CE2 (iff_l _ _ _ HCC Hz)).
  - fintro Hz. finst HCC z. apply (iff_r _ _ _ HCC). fsplit; [|exact Hz].
    fex Hz u Hu. fex Hu t Ht. fdestr Ht Ht1 Ht2.
    unfold App0 in Ht1. fex Ht1 p Hp. fdestr Hp Hp1 Hp2.
    pose proof (op0_c2 HG u t p Hp2) as Hc2. fex Hc2 s Hs. fdestr Hs Hs1 Hs2.
    apply (union_in HG u2 u3 t z Hu3); [|exact Ht2]. apply (union_in HG u1 u2 s t Hu2); [|exact Hs2].
    exact (union_in HG Fn u1 p s Hu1 Hp1 Hs1).
Qed.

Lemma hl_H_app_el {G} (HG : incl ZF0base G) (HX : WOx G) Fn w H i v :
  G ⊢C Dom0 Fn w -> G ⊢C URan Fn H -> G ⊢C App0 H i v ->
  G ⊢C ∃ (∃ ($1 ∈' w`[↑]`[↑] ∧ App0 Fn`[↑]`[↑] $1 $0 ∧ App0 $0 i`[↑]`[↑] v`[↑]`[↑])).
Proof.
  intros Hdom HU Ha. unfold App0 in Ha. fex Ha q Hq. fdestr Hq Hq1 Hq2.
  unfold URan in HU. finst HU q. pose proof (iff_l _ _ _ HU Hq1) as T. fex T n Hn. fex Hn F HaF. fdestr HaF HF1 HF2.
  fexists n. fexists F. fsplit; [fsplit|].
  - exact (Z_wo.w_dom0_in HG HX Fn w n F Hdom HF1).
  - exact HF1.
  - exact (app0_intro_g F i v q Hq2 HF2).
Qed.

Lemma hl_H_app_in {G} Fn H n F i v : G ⊢C URan Fn H -> G ⊢C App0 Fn n F -> G ⊢C App0 F i v -> G ⊢C App0 H i v.
Proof.
  intros HU HaF Ha. unfold App0 in Ha. fex Ha q Hq. fdestr Hq Hq1 Hq2.
  apply (app0_intro_g H i v q Hq2). unfold URan in HU. finst HU q. apply (iff_r _ _ _ HU).
  fexists n. fexists F. fsplit; assumption.
Qed.

Lemma hl_ran_ex {G} (HG : incl ZF0base G) c (HC : incl (Ax_hull c) G) H :
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔ ∃ App0 H`[↑]`[↑]`[↑] $0 $1).
Proof.
  assert (Hi4 : In (forall_times 1 (ax_sep' RanF)) G)
    by (apply (hl_in_hi c _ HC); unfold hull_insts; do 3 right; left; reflexivity).
  fobtain (union_ex HG H) as u1 Hu1. fobtain (union_ex HG u1) as u2 Hu2.
  pose proof (sep_use _ 1 RanF (fun _ => H) u2 Hi4 ltac:(unfold RanF; fbcomp)) as T. unfold RanF in T. simp_in T.
  fex T X HXd. fexists X. fall z. fsplit.
  - fintro Hz. finst HXd z. exact (CE2 (iff_l _ _ _ HXd Hz)).
  - fintro Hz. finst HXd z. apply (iff_r _ _ _ HXd). fsplit; [|exact Hz].
    fex Hz i Hi. unfold App0 in Hi. fex Hi p Hp. fdestr Hp Hp1 Hp2.
    pose proof (op0_c2 HG i z p Hp2) as Hc2. fex Hc2 s Hs. fdestr Hs Hs1 Hs2.
    apply (union_in HG u1 u2 s z Hu2); [|exact Hs2]. exact (union_in HG H u1 p s Hu1 Hp1 Hs1).
Qed.

Section Hull.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G).
Context (c : form) (Hc : fb 2 c) (HC : incl (Ax_hull c) G).

Theorem hull_ex H0 I :
  G ⊢C Fun0 H0 ->
  G ⊢C ∀ (∀ (App0 H0`[↑]`[↑] $1 $0 → $1 ∈' I`[↑]`[↑] ∧ Lform)) ->
  G ⊢C ∀ (∀ (App0 H0`[↑]`[↑] $1 $0 → ∃ (∃ (NumF 0 $1 ∧ OP0 $1 $0 $3)))) ->
  G ⊢C ∀ ($0 ∈' I`[↑] → ∀ ($0 ∈' I`[↑]`[↑] → ∀ (OP0 $2 $1 $0 → $0 ∈' I`[↑]`[↑]`[↑]))) ->
  G ⊢C ∀ (NumF 1 $0 → $0 ∈' I`[↑]) -> G ⊢C ∀ (NumF 2 $0 → $0 ∈' I`[↑]) ->
  G ⊢C ∃ (∃ (HullP c H0`[↑]`[↑] I`[↑]`[↑] $1 $0)).
Proof using HG HR HOm HW c Hc HC.
  intros Hf0 Hb0 Ht0 HIop HI1 HI2.
  pose proof (cw_wox HR HOm HW) as HX. pose proof (WOx_L _ HX) as HL.
  pose proof (hl_in_rec c HC) as HIr. pose proof (hl_in_cw c HC) as HCw.
  fobtain (Z_wo.w_om_ex HG HX) as w Hw.
  pose proof (Z_wo.w_om_ord HG HX w Hw) as Ow.
  pose proof (omrec_ex HG HR HOm HL (phH c) (fb_phH c Hc) HIr H0 w (hl_gtot HG HX c Hc HC) (hl_gfun HG c) Ow) as T.
  fex T Fn HFn. fdestr HFn HFn1 Hrec. fdestr HFn1 Hfn Hdom.
  pose proof (hl_ind HG HX c Hc HC H0 I Fn w Hf0 Hb0 Ht0 HIop HI1 HI2 Hw Hfn Hdom Hrec) as Hind.
  fobtain (hl_uran_ex HG HX Fn) as Hh HU.
  fobtain (hl_ran_ex HG c HC Hh) as X HXd.
  fexists Hh. fexists X. unfold HullP.
  fsplit; [fsplit; [fsplit; [fsplit; [fsplit; [fsplit|]|]|]|]|].
  - (* Fun0 H *)
    apply (fun0_intro HG (hl_P HX)).
    + apply (isrel0_intro HG (hl_P HX)). fall q. fintro Hq.
      pose proof HU as K. unfold URan in K. finst K q. pose proof (iff_l _ _ _ K Hq) as T. clear K.
      fex T n Hn. fex Hn F HaF. fdestr HaF HF1 HF2.
      pose proof (hl_inv_at c H0 I Fn w n F Hind (Z_wo.w_dom0_in HG HX Fn w n F Hdom HF1) HF1) as HI.
      inv_unpack HI Hf Hidx Hval Hcls. unfold Fun0 in Hf. exact (Z_wo.w_isrel0_el HG HX F q (CE1 Hf) HF2).
    + fall i. fall v. fall v'. fintro H1. fintro H2.
      pose proof (hl_H_app_el HG HX Fn w Hh i v Hdom HU H1) as T. fex T n Hn. fex Hn F HaF.
      fdestr HaF HF1 HF2. fdestr HF1 Hnw HnF.
      pose proof (hl_H_app_el HG HX Fn w Hh i v' Hdom HU H2) as T. fex T m Hm. fex Hm F' HaF'.
      fdestr HaF' HF1' HF2'. fdestr HF1' Hmw HmF'.
      pose proof (hl_common HG HX c H0 I Fn w n m F F' Hind Hw Hfn Hnw Hmw HnF HmF') as T.
      fex T k Hk. fex Hk Fk HK. fdestr HK HK1 HK4. fdestr HK1 HK2 HK3. fdestr HK2 Hkw HkK.
      pose proof (hl_inv_at c H0 I Fn w k Fk Hind Hkw HkK) as HI. inv_unpack HI Hf Hidx Hval Hcls.
      exact (Z_wo.w_fun0_app HG HX Fk i v v' Hf (hl_app_sub F Fk i v HK3 HF2) (hl_app_sub F' Fk i v' HK4 HF2')).
  - (* indices in I *)
    fall i. fall v. fintro Ha.
    pose proof (hl_H_app_el HG HX Fn w Hh i v Hdom HU Ha) as T. fex T n Hn. fex Hn F HaF.
    fdestr HaF HF1 HF2. fdestr HF1 Hnw HnF.
    pose proof (hl_inv_at c H0 I Fn w n F Hind Hnw HnF) as HI. inv_unpack HI Hf Hidx Hval Hcls.
    finst Hidx i v. exact (IE Hidx HF2).
  - exact HXd.
  - (* H0 ⊆ H *)
    fall i. fall v. fintro Ha.
    fobtain (Z_wo.w_emp0_ex HG HX) as e He.
    pose proof (Z_wo.w_om_emp HG HX w e Hw He) as Hew.
    fobtain (Z_wo.w_dom0_app HG HX Fn w e Hdom Hew) as F0 HF0.
    pose proof (omrec_zero HG HR HOm HL (phH c) (fb_phH c Hc) HIr H0 Fn e F0 Hrec HF0 He) as E.
    frew_in E (App0 $0 i`[↑] v`[↑]) Ha.
    exact (hl_H_app_in Fn Hh e F0 i v HU HF0 Ha).
  - (* X ⊆ L *)
    fall x. fintro Hx. pose proof HXd as K. finst K x. pose proof (iff_l _ _ _ K Hx) as T. clear K. fex T i Hi.
    pose proof (hl_H_app_el HG HX Fn w Hh i x Hdom HU Hi) as T. fex T n Hn. fex Hn F HaF.
    fdestr HaF HF1 HF2. fdestr HF1 Hnw HnF.
    pose proof (hl_inv_at c H0 I Fn w n F Hind Hnw HnF) as HI. inv_unpack HI Hf Hidx Hval Hcls.
    finst Hval i x. pose proof (IE Hval HF2) as HxL. rewrite InL_eq in HxL. exact HxL.
  - (* closure under ordered pairs *)
    unfold OPClos. fall x. fintro Hx. fall y. fintro Hy. fall p. fintro Hp.
    pose proof HXd as K. finst K x. pose proof (iff_l _ _ _ K Hx) as T. clear K. fex T s Hs.
    pose proof HXd as K. finst K y. pose proof (iff_l _ _ _ K Hy) as T. clear K. fex T t Ht.
    pose proof (hl_H_app_el HG HX Fn w Hh s x Hdom HU Hs) as T. fex T n Hn. fex Hn F HaF.
    fdestr HaF HF1 HF2. fdestr HF1 Hnw HnF.
    pose proof (hl_H_app_el HG HX Fn w Hh t y Hdom HU Ht) as T. fex T m Hm. fex Hm F' HaF'.
    fdestr HaF' HF1' HF2'. fdestr HF1' Hmw HmF'.
    pose proof (hl_common HG HX c H0 I Fn w n m F F' Hind Hw Hfn Hnw Hmw HnF HmF') as T.
    fex T k Hk. fex Hk Fk HK. fdestr HK HK1 HK4. fdestr HK1 HK2 HK3. fdestr HK2 Hkw HkK.
    pose proof (hl_succ_at HG HX c Hc HC H0 Fn w k Fk Hw Hfn Hdom Hrec Hkw HkK) as T.
    fex T k' Hk'. fex Hk' Fk' HK'. fdestr HK' HkK' HN.
    fobtain (hl_num_ex 1 HG HX) as g Hg. fobtain (Z_wo.w_op0_ex HG HX s t) as r Hr.
    fobtain (Z_wo.w_op0_ex HG HX g r) as i Hi.
    pose proof (hl_t1_intro Fk i p s t x y g r (hl_app_sub F Fk s x HK3 HF2) (hl_app_sub F' Fk t y HK4 HF2')
                  Hg Hr Hi Hp) as HT.
    pose proof (hl_app_t1 HG HX c Fk Fk' i p HN HT) as Ha.
    pose proof (hl_H_app_in Fn Hh k' Fk' i p HU HkK' Ha) as Ha'.
    pose proof HXd as K. finst K p. apply (iff_r _ _ _ K). fexists i. exact Ha'.
  - (* closure under canonical witnesses *)
    unfold WClos. fall q. fintro Hq. fintro Hex.
    pose proof (canw_ex_g HG HX c HCw q Hex) as T. fex T w0 Hw0.
    pose proof HXd as K. finst K q. pose proof (iff_l _ _ _ K Hq) as T. clear K. fex T s Hs.
    pose proof (hl_H_app_el HG HX Fn w Hh s q Hdom HU Hs) as T. fex T n Hn. fex Hn F HaF.
    fdestr HaF HF1 HF2. fdestr HF1 Hnw HnF.
    pose proof (hl_succ_at HG HX c Hc HC H0 Fn w n F Hw Hfn Hdom Hrec Hnw HnF) as T.
    fex T n' Hn'. fex Hn' F' HaF'. fdestr HaF' HnF' HN.
    fobtain (hl_num_ex 2 HG HX) as g Hg. fobtain (Z_wo.w_op0_ex HG HX g s) as i Hi.
    pose proof (hl_t2_intro c F i w0 s q g HF2 Hw0 Hg Hi) as HT.
    pose proof (hl_app_t2 HG HX c F F' i w0 HN HT) as Ha.
    pose proof (hl_H_app_in Fn Hh n' F' i w0 HU HnF' Ha) as Ha'.
    fexists w0. fsplit.
    + pose proof HXd as K. finst K w0. apply (iff_r _ _ _ K). fexists i. exact Ha'.
    + exact (canw_sat_g HG c q w0 Hw0).
Qed.

End Hull.
