(** * ZFTM: the 335-state machine R3Y1_335.tm (a reduction of Wade's zf2.tm) as a busycoq [TM], built generically from the program.

    The states are defined structurally, following [TMBuilder.generate]:
    - the fixed framework states (boot, register operations 1.*, return 2.*, 5.root);
    - [QDisp i]  = 4.dispatch.(i+1), i < 7 (max run of car edges = 7);
    - [QBrk k]   = 6.break.k (k <= 1),  [QCont k] = 6.continue.k (k <= 4);
    - [QRInc r], [QRDec r] = 3.<register r>.inc / .decnz (11 registers, declaration order);
    - [QNode n]  = decision-DAG node n of [zf2] (ZF2Dag.v);
    - [QHalt]    = the state "halt" (no transitions).

    The transition function [tm] is defined from [zf2_nodes]; the theorem [tm_table] checks by
    [vm_compute] that it coincides with the literal table [zf2_table] of R3Y1_335.tm (the trust anchor). *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia Strings.String Ascii Eqdep_dec.
From BusyCoq Require Import TM.
From ZF Require Import RM ZF2Dag.
Import ListNotations.
Local Open Scope string_scope.

(** ** Bounded naturals [0..k] (finite payloads, so that the state type is finite). *)
Definition bnat (k : nat) : Type := { n : nat | Nat.leb n k = true }.

Definition bval {k} (x : bnat k) : nat := proj1_sig x.

Definition bmk (k n : nat) : bnat k :=
  match Nat.leb n k as b return Nat.leb n k = b -> bnat k with
  | true => fun H => exist _ n H
  | false => fun _ => exist _ k (Nat.leb_refl k)
  end eq_refl.

Lemma bnat_eq : forall k (x y : bnat k), bval x = bval y -> x = y.
Proof.
  intros k [x Hx] [y Hy]; simpl; intros ->.
  f_equal. apply UIP_dec. exact bool_dec.
Qed.

Lemma bval_bmk : forall k n, n <= k -> bval (bmk k n) = n.
Proof.
  intros k n H. unfold bmk.
  generalize (@eq_refl bool (Nat.leb n k)).
  generalize (Nat.leb n k) at 2 3. intros b E. destruct b; [reflexivity|].
  apply Nat.leb_nle in E. lia.
Qed.

Lemma bmk_bval : forall k (x : bnat k), bmk k (bval x) = x.
Proof.
  intros k x. apply bnat_eq. apply bval_bmk.
  destruct x as [n H]. simpl. apply Nat.leb_le, H.
Qed.

Lemma bval_le : forall k (x : bnat k), bval x <= k.
Proof. intros k [n H]. simpl. apply Nat.leb_le, H. Qed.

Definition bnat_dec {k} (x y : bnat k) : {x = y} + {x <> y}.
Proof.
  destruct (Nat.eq_dec (bval x) (bval y)) as [E|E].
  - left. apply bnat_eq, E.
  - right. intros ->. apply E. reflexivity.
Defined.

Definition ball (k : nat) : list (bnat k) := map (bmk k) (seq 0 (S k)).

Lemma ball_spec : forall k x, In x (ball k).
Proof.
  intros k x. unfold ball. rewrite <- (bmk_bval k x).
  apply in_map, in_seq. pose proof (bval_le k x). lia.
Qed.

(** ** Parameters of the build (TMBuilder.generate for zf2). *)
Definition max_zeros := 7.      (* dispatch states 4.dispatch.1 .. 4.dispatch.7 *)

(** ** States *)
Inductive state : Type :=
  | QBootA | QBootB | QBootC | QBootD | QBootE
  | QDec | QDecB | QDecC | QDecD | QDecE | QDecG | QDecH | QDecI
  | QInc | QIncB | QIncC | QIncD
  | QSel | QSelB | QSelC | QSelD | QSelE | QSelF
  | QRet1 | QRet1a | QRet1b | QRet2 | QRet2a | QRet2b
  | QRoot
  | QDisp (i : bnat 6)      (* 4.dispatch.(i+1) *)
  | QBrk (k : bnat 1)       (* 6.break.k *)
  | QCont (k : bnat 4)      (* 6.continue.k *)
  | QRInc (r : bnat 10)     (* 3.<reg r>.inc *)
  | QRDec (r : bnat 10)     (* 3.<reg r>.decnz *)
  | QNode (n : bnat 268)    (* DAG node n *)
  | QHalt.

Definition Disp i := QDisp (bmk 6 i).
Definition Brk k := QBrk (bmk 1 k).
Definition Cont k := QCont (bmk 4 k).
Definition RInc r := QRInc (bmk 10 r).
Definition RDec r := QRDec (bmk 10 r).
Definition Node n := QNode (bmk 268 n).

Definition state_eq_dec (a b : state) : {a = b} + {a <> b}.
Proof. decide equality; apply bnat_dec. Defined.

Definition fixed_states : list state :=
  [QBootA; QBootB; QBootC; QBootD; QBootE;
   QDec; QDecB; QDecC; QDecD; QDecE; QDecG; QDecH; QDecI;
   QInc; QIncB; QIncC; QIncD;
   QSel; QSelB; QSelC; QSelD; QSelE; QSelF;
   QRet1; QRet1a; QRet1b; QRet2; QRet2a; QRet2b; QRoot; QHalt].

Definition all_states : list state :=
  fixed_states
  ++ map QDisp (ball 6) ++ map QBrk (ball 1) ++ map QCont (ball 4)
  ++ map QRInc (ball 10) ++ map QRDec (ball 10) ++ map QNode (ball 268).

Lemma all_states_spec : forall a, In a all_states.
Proof.
  intros a. unfold all_states. rewrite !in_app_iff.
  destruct a;
    first [ left; unfold fixed_states; cbn [In]; repeat (first [left; reflexivity | right]); fail
          | do 1 right; left; apply in_map, ball_spec
          | do 2 right; left; apply in_map, ball_spec
          | do 3 right; left; apply in_map, ball_spec
          | do 4 right; left; apply in_map, ball_spec
          | do 5 right; left; apply in_map, ball_spec
          | do 6 right; apply in_map, ball_spec ].
Qed.

Module ZFCtx <: Ctx.
  Definition Q := state.
  Definition Sym := bool.
  Definition q0 := QBootA.
  Definition s0 := false.
  Definition q1 := QBootB.
  Lemma q0_neq_q1 : q0 <> q1. Proof. discriminate. Qed.
  Definition s1 := true.
  Lemma s0_neq_s1 : s0 <> s1. Proof. discriminate. Qed.
  Definition eqb_q := state_eq_dec.
  Definition eqb_sym := bool_dec.
  Definition all_qs := all_states.
  Definition all_qs_spec := all_states_spec.
  Definition all_syms := [false; true].
  Lemma all_syms_spec : forall a, In a all_syms.
  Proof. intros []; simpl; tauto. Qed.
End ZFCtx.

Module ZFTM := TM.TM ZFCtx.
Export ZFTM.

(** ** The transition function, following TMBuilder.generate. *)

(* the transition of a DAG node reading bit [b], whose edge for [b] is [e] *)
Definition edge_trans (e : edge) (b : bool) : option (bool * dir * state) :=
  match e with
  | ENode n => Some (b, R, Node n)
  | EInc r => Some (b, R, RInc r)
  | EDecnz r => Some (b, R, RDec r)
  | EHalt => Some (b, R, QHalt)
  | EBreak k =>
      if b then Some (false, L, Brk k)
      else match k with
           | 0 => Some (true, L, Cont 0)
           | S k' => Some (false, L, Brk k')
           end
  | EContinue k =>
      if b then Some (false, L, Cont (k - 1)) else Some (false, L, Cont k)
  end.

Definition node_edge (n : nat) (b : bool) : edge :=
  if b then snd (zf2_nodes n) else fst (zf2_nodes n).

Definition tm : TM := fun '(q, s) =>
  match q, s with
  (* 0. boot *)
  | QBootA, false => Some (true, R, QBootB)
  | QBootA, true => Some (false, L, QBootC)
  | QBootB, false => Some (false, R, QBootC)
  | QBootB, true => Some (false, R, QBootB)
  | QBootC, false => Some (true, L, QBootD)
  | QBootC, true => Some (false, R, QBootE)
  | QBootD, false => Some (false, L, QBootE)
  | QBootD, true => Some (false, L, Cont 4)
  | QBootE, false => Some (true, L, QBootA)
  | QBootE, true => Some (false, L, QBootB)
  (* 1. decnz *)
  | QDec, false => Some (true, R, QDecB)
  | QDec, true => Some (true, L, QDecG)
  | QDecB, false => Some (false, R, QDecB)
  | QDecB, true => Some (false, R, QDecC)
  | QDecC, false => Some (true, R, QDecD)
  | QDecC, true => Some (true, R, QDecC)
  | QDecD, false => Some (false, R, QDecE)
  | QDecD, true => Some (false, R, QDecC)
  | QDecE, false => Some (false, L, QDec)
  | QDecE, true => Some (true, R, QDecE)
  | QDecG, false => Some (false, L, QRet2)
  | QDecG, true => Some (true, R, QDecH)
  | QDecH, false => Some (true, R, QDecI)
  | QDecH, true => Some (false, R, QDecH)
  | QDecI, false => Some (false, L, QSel)
  | QDecI, true => Some (true, R, QDecE)
  (* 1. inc *)
  | QInc, false => Some (true, R, QIncB)
  | QInc, true => None
  | QIncB, false => Some (false, R, QIncB)
  | QIncB, true => Some (true, R, QIncC)
  | QIncC, false => Some (false, R, QIncD)
  | QIncC, true => Some (true, R, QIncC)
  | QIncD, false => Some (true, L, QRet1)
  | QIncD, true => Some (true, R, QIncC)
  (* 1. sel *)
  | QSel, false => Some (true, R, QSelB)
  | QSel, true => Some (false, L, QRet1)
  | QSelB, false => Some (false, R, QSelB)
  | QSelB, true => Some (true, R, QSelC)
  | QSelC, false => Some (false, R, QSelD)
  | QSelC, true => Some (true, R, QSelC)
  | QSelD, false => Some (false, L, QSelE)
  | QSelD, true => Some (true, R, QSelC)
  | QSelE, false => Some (true, L, QSelF)
  | QSelE, true => Some (false, L, QRet1)
  | QSelF, false => Some (false, R, QSelE)
  | QSelF, true => Some (true, L, QSelF)
  (* 2. return *)
  | QRet1, false => Some (false, L, QRet1a)
  | QRet1, true => Some (true, L, QRet1)
  | QRet1a, false => Some (false, L, QRet1b)
  | QRet1a, true => Some (true, L, QRet1)
  | QRet1b, false => Some (false, L, QRet1b)
  | QRet1b, true => Some (false, L, Brk 0)
  | QRet2, false => Some (false, L, QRet2a)
  | QRet2, true => Some (true, L, QRet2)
  | QRet2a, false => Some (false, L, QRet2b)
  | QRet2a, true => Some (true, L, QRet2)
  | QRet2b, false => Some (false, L, QRet2b)
  | QRet2b, true => Some (false, L, Brk 1)
  (* 3. register chains: register r reads r+1 ones before reaching 1.inc / 1.decnz *)
  | QRInc r, false => Some (false, R, QSel)
  | QRInc r, true => Some (true, R, match bval r with 0 => QInc | S r' => RInc r' end)
  | QRDec r, false => Some (false, R, QSel)
  | QRDec r, true => Some (true, R, match bval r with 0 => QDec | S r' => RDec r' end)
  (* 4. dispatch: pass max_zeros + 1 zeros going left, then 5.root *)
  | QDisp i, false =>
      if Nat.ltb (S (bval i)) max_zeros then Some (false, L, Disp (S (bval i)))
      else Some (false, R, QRoot)
  | QDisp i, true => Some (true, L, Cont 0)
  (* 5. root *)
  | QRoot, false => Some (false, R, QRoot)
  | QRoot, true => Some (true, R, Node 0)
  (* 6. break / continue *)
  | QBrk k, false => match bval k with
                     | 0 => Some (true, L, Cont 0)
                     | S k' => Some (false, L, Brk k')
                     end
  | QBrk k, true => Some (false, L, QBrk k)
  | QCont k, false => match bval k with
                      | 0 => Some (false, L, Disp 0)
                      | S _ => Some (false, L, QCont k)
                      end
  | QCont k, true => match bval k with
                     | 0 => Some (true, L, Cont 0)
                     | S k' => Some (false, L, Cont k')
                     end
  (* decision DAG *)
  | QNode n, b => edge_trans (node_edge (bval n) b) b
  | QHalt, _ => None
  end.

(** ** State names (as in zf2.tm) *)
Definition digit (n : nat) : string := String (ascii_of_nat (48 + n)) EmptyString.

Definition reg_name (r : nat) : string :=
  nth r ["prooflist"; "nextproof"; "topwff"; "wffstack"; "axiomcode"; "param1"; "param2";
         "param3"; "scratch1"; "scratch2"; "scratch3"] "?".

(* generated by tools/gen_zftm_names.py from the comments of ZF2Dag.v (checked below) *)
Definition node_name (n : nat) : string :=
  match n with
  | 0 => "main().0"
  | 1 => "cparam().n_033.0"
  | 2 => "cparam().n_033.0.0"
  | 3 => "cparam().n_033.0.1"
  | 4 => "cparam().n_033.0.1.0"
  | 5 => "cparam().n_033.0.1.1"
  | 6 => "cparam().n_033.0.1.1.0"
  | 7 => "cparam().n_033.0.2"
  | 8 => "cparam().n_033.0.2.0"
  | 9 => "cparam(param2).0"
  | 10 => "cparam(param2).1"
  | 11 => "cparam(scratch3).0"
  | 12 => "if_eq().n_066.0"
  | 13 => "if_eq().n_066.0.0"
  | 14 => "if_eq().n_066.0.1"
  | 15 => "if_eq().n_066.0.1.0"
  | 16 => "if_eq().n_066.0.2"
  | 17 => "if_eq().n_066.1"
  | 18 => "if_eq().n_066.2"
  | 19 => "if_eq(scratch2,scratch3,10).0"
  | 20 => "if_eq(scratch2,scratch3,57).0"
  | 21 => "if_not_decnz(prooflist,99).0"
  | 22 => "if_not_decnz(prooflist,99).0.0"
  | 23 => "if_not_decnz(prooflist,99).1"
  | 24 => "if_not_decnz(prooflist,99).2"
  | 25 => "main().1"
  | 26 => "main().10"
  | 27 => "main().11"
  | 28 => "main().12"
  | 29 => "main().13"
  | 30 => "main().14"
  | 31 => "main().15"
  | 32 => "main().16"
  | 33 => "main().17"
  | 34 => "main().18"
  | 35 => "main().19"
  | 36 => "main().2"
  | 37 => "main().20"
  | 38 => "main().21"
  | 39 => "main().22"
  | 40 => "main().23"
  | 41 => "main().24"
  | 42 => "main().25"
  | 43 => "main().26"
  | 44 => "main().27"
  | 45 => "main().28"
  | 46 => "main().29"
  | 47 => "main().3"
  | 48 => "main().30"
  | 49 => "main().31"
  | 50 => "main().32"
  | 51 => "main().33"
  | 52 => "main().34"
  | 53 => "main().35"
  | 54 => "main().36"
  | 55 => "main().37"
  | 56 => "main().38"
  | 57 => "main().39"
  | 58 => "main().4"
  | 59 => "main().40"
  | 60 => "main().41"
  | 61 => "main().42"
  | 62 => "main().43"
  | 63 => "main().44"
  | 64 => "main().45"
  | 65 => "main().46"
  | 66 => "main().47"
  | 67 => "main().48"
  | 68 => "main().49"
  | 69 => "main().5"
  | 70 => "main().50"
  | 71 => "main().51"
  | 72 => "main().52"
  | 73 => "main().53"
  | 74 => "main().54"
  | 75 => "main().55"
  | 76 => "main().56"
  | 77 => "main().57"
  | 78 => "main().58"
  | 79 => "main().59"
  | 80 => "main().6"
  | 81 => "main().60"
  | 82 => "main().61"
  | 83 => "main().62"
  | 84 => "main().63"
  | 85 => "main().64"
  | 86 => "main().65"
  | 87 => "main().66"
  | 88 => "main().67"
  | 89 => "main().68"
  | 90 => "main().69"
  | 91 => "main().7"
  | 92 => "main().70"
  | 93 => "main().71"
  | 94 => "main().72"
  | 95 => "main().73"
  | 96 => "main().74"
  | 97 => "main().75"
  | 98 => "main().76"
  | 99 => "main().77"
  | 100 => "main().78"
  | 101 => "main().79"
  | 102 => "main().8"
  | 103 => "main().80"
  | 104 => "main().81"
  | 105 => "main().82"
  | 106 => "main().83"
  | 107 => "main().84"
  | 108 => "main().85"
  | 109 => "main().86"
  | 110 => "main().87"
  | 111 => "main().88"
  | 112 => "main().89"
  | 113 => "main().9"
  | 114 => "main().90"
  | 115 => "main().91"
  | 116 => "main().92"
  | 117 => "main().93"
  | 118 => "main().94"
  | 119 => "main().95"
  | 120 => "main().96"
  | 121 => "main().97"
  | 122 => "main().98"
  | 123 => "main().99"
  | 124 => "main().99.0"
  | 125 => "main().99.1"
  | 126 => "main().n_107.0"
  | 127 => "main().n_107.1"
  | 128 => "main().n_107.2"
  | 129 => "main().n_107.3"
  | 130 => "main().n_108.0"
  | 131 => "main().n_108.1"
  | 132 => "main().n_108.2"
  | 133 => "main().n_108.3"
  | 134 => "main().n_109.0"
  | 135 => "main().n_109.1"
  | 136 => "main().n_110.0"
  | 137 => "main().n_110.1"
  | 138 => "main().n_111.0"
  | 139 => "main().n_112.0"
  | 140 => "main().n_113.0"
  | 141 => "main().n_113.1"
  | 142 => "main().n_114.0"
  | 143 => "main().n_116.0"
  | 144 => "main().n_117.0"
  | 145 => "main().n_118.0"
  | 146 => "main().n_119.0"
  | 147 => "main().n_121.0"
  | 148 => "main().n_122.0"
  | 149 => "main().n_123.0"
  | 150 => "main().n_123.1"
  | 151 => "main().n_124.0"
  | 152 => "main().n_125.0"
  | 153 => "main().n_126.0"
  | 154 => "main().n_127.0"
  | 155 => "main().n_128.0"
  | 156 => "main().n_130.0"
  | 157 => "main().n_131.0"
  | 158 => "main().n_132.0"
  | 159 => "main().n_133.0"
  | 160 => "main().n_134.0"
  | 161 => "main().n_135.0"
  | 162 => "main().n_136.0"
  | 163 => "main().n_137.0"
  | 164 => "main().n_138.0"
  | 165 => "main().n_139.0"
  | 166 => "main().n_140.0"
  | 167 => "main().n_141.0"
  | 168 => "main().n_142.0"
  | 169 => "main().n_143.0"
  | 170 => "main().n_144.0"
  | 171 => "main().n_149.0"
  | 172 => "main().n_150.0"
  | 173 => "main().n_151.0"
  | 174 => "main().n_152.0"
  | 175 => "main().n_167.0"
  | 176 => "node_057.0"
  | 177 => "node_084.0"
  | 178 => "node_115.0"
  | 179 => "node_120.0"
  | 180 => "node_129.0"
  | 181 => "node_145.0"
  | 182 => "node_145.1"
  | 183 => "node_145.2"
  | 184 => "node_146.0"
  | 185 => "node_147.0"
  | 186 => "node_148.0"
  | 187 => "node_153.0"
  | 188 => "pair(scratch2,scratch1,topwff).0"
  | 189 => "pair(scratch2,scratch1,topwff).1"
  | 190 => "pair(scratch2,scratch1,topwff).2"
  | 191 => "pair(scratch2,scratch1,topwff).2.0"
  | 192 => "par1().0"
  | 193 => "par2().0"
  | 194 => "par2().1"
  | 195 => "par3().0"
  | 196 => "par3().1"
  | 197 => "pushwff().0"
  | 198 => "pushwff().1"
  | 199 => "pushwff().2"
  | 200 => "select().0"
  | 201 => "select().0.0"
  | 202 => "select().0.1"
  | 203 => "select().0.1.0"
  | 204 => "select().1"
  | 205 => "select().2"
  | 206 => "unpair().n_005.0"
  | 207 => "unpair().n_005.1"
  | 208 => "unpair().n_005.1.0"
  | 209 => "unpair().n_005.2"
  | 210 => "unpair(scratch1,scratch2,prooflist).0"
  | 211 => "unpair(scratch1,scratch2,wffstack).0"
  | 212 => "v_1().0"
  | 213 => "v_2().0"
  | 214 => "v_3().0"
  | 215 => "wa().0"
  | 216 => "wal().0"
  | 217 => "wel().0"
  | 218 => "weq().0"
  | 219 => "wex().0"
  | 220 => "while_decnz().n_000.0"
  | 221 => "while_decnz().n_011.0"
  | 222 => "while_decnz().n_019.0"
  | 223 => "while_decnz().n_019.0.0"
  | 224 => "while_decnz(axiomcode,()).0"
  | 225 => "while_decnz(nextproof,94).0"
  | 226 => "while_decnz(nextproof,94).1"
  | 227 => "while_decnz(nextproof,94).1.0"
  | 228 => "while_decnz(param1,18).0"
  | 229 => "while_decnz(param1,3.scratch2.inc).0"
  | 230 => "while_decnz(param2,()).0"
  | 231 => "while_decnz(param2,18).0"
  | 232 => "while_decnz(param2,77).0"
  | 233 => "while_decnz(param2,77).1"
  | 234 => "while_decnz(param2,77).1.0"
  | 235 => "while_decnz(param3,18).0"
  | 236 => "while_decnz(param3,3.scratch2.inc).0"
  | 237 => "while_decnz(scratch1,()).0"
  | 238 => "while_decnz(scratch1,3.axiomcode.inc).0"
  | 239 => "while_decnz(scratch1,3.axiomcode.inc).1"
  | 240 => "while_decnz(scratch1,3.nextproof.inc).0"
  | 241 => "while_decnz(scratch1,3.nextproof.inc).1"
  | 242 => "while_decnz(scratch1,3.param1.inc).0"
  | 243 => "while_decnz(scratch1,3.param1.inc).1"
  | 244 => "while_decnz(scratch1,3.param2.inc).0"
  | 245 => "while_decnz(scratch1,3.param2.inc).1"
  | 246 => "while_decnz(scratch1,3.param3.inc).0"
  | 247 => "while_decnz(scratch1,3.param3.inc).1"
  | 248 => "while_decnz(scratch1,3.scratch2.inc).0"
  | 249 => "while_decnz(scratch1,3.scratch3.inc).0"
  | 250 => "while_decnz(scratch1,3.scratch3.inc).1"
  | 251 => "while_decnz(scratch1,3.topwff.inc).0"
  | 252 => "while_decnz(scratch1,42).0"
  | 253 => "while_decnz(scratch1,42).1"
  | 254 => "while_decnz(scratch1,42).1.0"
  | 255 => "while_decnz(scratch2,()).0"
  | 256 => "while_decnz(scratch2,3.prooflist.inc).0"
  | 257 => "while_decnz(scratch2,3.prooflist.inc).1"
  | 258 => "while_decnz(scratch2,3.topwff.inc).0"
  | 259 => "while_decnz(scratch2,3.wffstack.inc).0"
  | 260 => "while_decnz(scratch2,3.wffstack.inc).1"
  | 261 => "while_decnz(scratch3,()).0"
  | 262 => "while_decnz(topwff,()).0"
  | 263 => "while_decnz(topwff,3.scratch1.inc).0"
  | 264 => "while_decnz(topwff,3.scratch1.inc).1"
  | 265 => "while_decnz(topwff,3.scratch2.inc).0"
  | 266 => "while_decnz(wffstack,3.topwff.inc).0"
  | 267 => "wim().0"
  | 268 => "wn().0"
  | _ => "?"
  end.

Definition name (q : state) : string :=
  match q with
  | QBootA => "0.boot.A" | QBootB => "0.boot.B" | QBootC => "0.boot.C"
  | QBootD => "0.boot.D" | QBootE => "0.boot.E"
  | QDec => "1.decnz" | QDecB => "1.decnz.b" | QDecC => "1.decnz.c" | QDecD => "1.decnz.d"
  | QDecE => "1.decnz.e" | QDecG => "1.decnz.g" | QDecH => "1.decnz.h" | QDecI => "1.decnz.i"
  | QInc => "1.inc" | QIncB => "1.inc.b" | QIncC => "1.inc.c" | QIncD => "1.inc.d"
  | QSel => "1.sel" | QSelB => "1.sel.b" | QSelC => "1.sel.c" | QSelD => "1.sel.d"
  | QSelE => "1.sel.e" | QSelF => "1.sel.f"
  | QRet1 => "2.ret1" | QRet1a => "2.ret1.1" | QRet1b => "2.ret1.2"
  | QRet2 => "2.ret2" | QRet2a => "2.ret2.1" | QRet2b => "2.ret2.2"
  | QRoot => "5.root"
  | QDisp i => "4.dispatch." ++ digit (S (bval i))
  | QBrk k => "6.break." ++ digit (bval k)
  | QCont k => "6.continue." ++ digit (bval k)
  | QRInc r => "3." ++ reg_name (bval r) ++ ".inc"
  | QRDec r => "3." ++ reg_name (bval r) ++ ".decnz"
  | QNode n => node_name (bval n)
  | QHalt => "halt"
  end.

(** ** The literal check against zf2.tm *)

(* the row of the table for (state name, symbol read), if any *)
Fixpoint table_lookup (t : list (string * bool * bool * bool * string)) (s : string) (b : bool)
    : option (bool * bool * string) :=
  match t with
  | [] => None
  | (s', b', w, mv, nx) :: t =>
      if andb (String.eqb s s') (Bool.eqb b b') then Some (w, mv, nx) else table_lookup t s b
  end.

Definition dir_is_R (d : dir) : bool := match d with R => true | L => false end.

Definition row_of (o : option (bool * dir * state)) : option (bool * bool * string) :=
  match o with
  | None => None
  | Some (w, d, q') => Some (w, dir_is_R d, name q')
  end.

Definition opt_row_eqb (a b : option (bool * bool * string)) : bool :=
  match a, b with
  | None, None => true
  | Some (w, m, n), Some (w', m', n') => andb (andb (Bool.eqb w w') (Bool.eqb m m')) (String.eqb n n')
  | _, _ => false
  end.

Lemma opt_row_eqb_eq : forall a b, opt_row_eqb a b = true -> a = b.
Proof.
  intros [[[w m] n]|] [[[w' m'] n']|]; simpl; try discriminate; [|reflexivity].
  intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Bool.eqb_prop in H1, H2. apply String.eqb_eq in H3. subst. reflexivity.
Qed.

Fixpoint nodupb (l : list string) : bool :=
  match l with
  | [] => true
  | x :: l => andb (negb (existsb (String.eqb x) l)) (nodupb l)
  end.

Lemma nodupb_spec : forall l, nodupb l = true -> NoDup l.
Proof.
  induction l as [|x l IH]; simpl; intros H; [constructor|].
  apply andb_prop in H as [H1 H2]. constructor; [|auto].
  intros Hin. apply negb_true_iff in H1.
  assert (existsb (String.eqb x) l = true) by (apply existsb_exists; exists x; split;
    [assumption | apply String.eqb_refl]).
  congruence.
Qed.

Definition row_key (r : string * bool * bool * bool * string) : string :=
  let '(s, b, _, _, _) := r in s ++ (if b then " 1" else " 0").

Definition check_rows : bool :=
  forallb (fun q => forallb (fun b => opt_row_eqb (table_lookup zf2_table (name q) b) (row_of (tm (q, b))))
                            [false; true]) all_states.

Definition check_no_extra : bool :=
  forallb (fun r => let '(s, _, _, _, _) := r in existsb (fun q => String.eqb s (name q)) all_states)
          zf2_table.

Lemma check_rows_ok : check_rows = true. Proof. vm_compute. reflexivity. Qed.
Lemma check_no_extra_ok : check_no_extra = true. Proof. vm_compute. reflexivity. Qed.
Lemma names_nodup_ok : nodupb (map name all_states) = true. Proof. vm_compute. reflexivity. Qed.
Lemma keys_nodup_ok : nodupb (map row_key zf2_table) = true. Proof. vm_compute. reflexivity. Qed.

(** The trust anchor: [tm] is exactly the transition table of zf2.tm.
    - for every state [q] and symbol [b], the row of zf2.tm for (name q, b) is the transition
      [tm (q, b)] (with the target state's name), and there is no row iff [tm] has no transition;
    - every row of zf2.tm belongs to a state of [tm]; state names are distinct (so names identify
      states) and rows have distinct keys;
    - the start state is "0.boot.A" (the [#! start] line of zf2.tm) and the blank symbol is 0. *)
Theorem tm_table :
  (forall q b, table_lookup zf2_table (name q) b = row_of (tm (q, b))) /\
  (forall s b w mv nx, In (s, b, w, mv, nx) zf2_table -> exists q, name q = s) /\
  NoDup (map name all_states) /\
  NoDup (map row_key zf2_table) /\
  name q0 = "0.boot.A" /\ s0 = false /\
  List.length all_states = 336 /\ List.length zf2_table = 669.
Proof.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - intros q b. apply opt_row_eqb_eq.
    pose proof check_rows_ok as H. unfold check_rows in H. rewrite forallb_forall in H.
    specialize (H q (all_states_spec q)). rewrite forallb_forall in H.
    apply H. destruct b; simpl; tauto.
  - intros s b w mv nx Hin. pose proof check_no_extra_ok as H. unfold check_no_extra in H.
    rewrite forallb_forall in H. specialize (H _ Hin).
    change (existsb (fun q => String.eqb s (name q)) all_states = true) in H.
    apply existsb_exists in H as [q [_ Hq]]. apply String.eqb_eq in Hq. exists q. auto.
  - apply nodupb_spec, names_nodup_ok.
  - apply nodupb_spec, keys_nodup_ok.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.
