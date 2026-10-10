(** * ZFTM: Wade's 393-state machine zf2.tm as a busycoq [TM], built generically from the program.

    The states are defined structurally, following [TMBuilder.generate]:
    - the fixed framework states (boot, register operations 1.*, return 2.*, 5.root);
    - [QDisp i]  = 4.dispatch.(i+1), i < 9 (max run of car edges in zf2 = 9);
    - [QBrk k]   = 6.break.k (k <= 2),  [QCont k] = 6.continue.k (k <= 4);
    - [QRInc r], [QRDec r] = 3.<register r>.inc / .decnz (11 registers, declaration order);
    - [QNode n]  = decision-DAG node n of [zf2] (ZF2Dag.v);
    - [QHalt]    = the state "halt" (no transitions).

    The transition function [tm] is defined from [zf2_nodes]; the theorem [tm_table] checks by
    [vm_compute] that it coincides with the literal table [zf2_table] of zf2.tm (the trust anchor). *)

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
Definition max_zeros := 9.      (* dispatch states 4.dispatch.1 .. 4.dispatch.9 *)

(** ** States *)
Inductive state : Type :=
  | QBootA | QBootB | QBootC | QBootD | QBootE
  | QDec | QDecB | QDecC | QDecD | QDecE | QDecG | QDecH | QDecI
  | QInc | QIncB | QIncC | QIncD
  | QSel | QSelB | QSelC | QSelD | QSelE | QSelF
  | QRet1 | QRet1a | QRet1b | QRet2 | QRet2a | QRet2b
  | QRoot
  | QDisp (i : bnat 8)      (* 4.dispatch.(i+1) *)
  | QBrk (k : bnat 2)       (* 6.break.k *)
  | QCont (k : bnat 4)      (* 6.continue.k *)
  | QRInc (r : bnat 10)     (* 3.<reg r>.inc *)
  | QRDec (r : bnat 10)     (* 3.<reg r>.decnz *)
  | QNode (n : bnat 323)    (* DAG node n *)
  | QHalt.

Definition Disp i := QDisp (bmk 8 i).
Definition Brk k := QBrk (bmk 2 k).
Definition Cont k := QCont (bmk 4 k).
Definition RInc r := QRInc (bmk 10 r).
Definition RDec r := QRDec (bmk 10 r).
Definition Node n := QNode (bmk 323 n).

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
  ++ map QDisp (ball 8) ++ map QBrk (ball 2) ++ map QCont (ball 4)
  ++ map QRInc (ball 10) ++ map QRDec (ball 10) ++ map QNode (ball 323).

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
  | 1 => "cons().0"
  | 2 => "cons().1"
  | 3 => "cparam().n_076.0"
  | 4 => "cparam().n_076.0.0"
  | 5 => "cparam().n_076.0.1"
  | 6 => "cparam().n_076.0.1.0"
  | 7 => "cparam().n_076.0.1.1"
  | 8 => "cparam().n_076.0.1.1.0"
  | 9 => "cparam().n_076.0.2"
  | 10 => "cparam().n_076.0.2.0"
  | 11 => "cparam(param2).0"
  | 12 => "cparam(param2).1"
  | 13 => "cparam(param3).0"
  | 14 => "cparam(param3).1"
  | 15 => "if_decnz(axiomcode,64).0"
  | 16 => "if_decnz(axiomcode,64).1"
  | 17 => "if_eq().n_097.0"
  | 18 => "if_eq().n_097.0.0"
  | 19 => "if_eq().n_097.0.1"
  | 20 => "if_eq().n_097.0.1.0"
  | 21 => "if_eq().n_097.0.2"
  | 22 => "if_eq().n_097.1"
  | 23 => "if_eq().n_097.2"
  | 24 => "if_eq(scratch2,scratch3,62).0"
  | 25 => "if_eq(scratch2,scratch3,88).0"
  | 26 => "if_eq(scratch2,scratch3,88).1"
  | 27 => "if_not_decnz(prooflist,110).0"
  | 28 => "if_not_decnz(prooflist,110).0.0"
  | 29 => "if_not_decnz(prooflist,110).1"
  | 30 => "if_not_decnz(prooflist,110).2"
  | 31 => "main().1"
  | 32 => "main().10"
  | 33 => "main().100"
  | 34 => "main().101"
  | 35 => "main().102"
  | 36 => "main().103"
  | 37 => "main().104"
  | 38 => "main().105"
  | 39 => "main().106"
  | 40 => "main().107"
  | 41 => "main().108"
  | 42 => "main().109"
  | 43 => "main().11"
  | 44 => "main().110"
  | 45 => "main().111"
  | 46 => "main().112"
  | 47 => "main().113"
  | 48 => "main().114"
  | 49 => "main().115"
  | 50 => "main().116"
  | 51 => "main().117"
  | 52 => "main().118"
  | 53 => "main().119"
  | 54 => "main().12"
  | 55 => "main().120"
  | 56 => "main().121"
  | 57 => "main().122"
  | 58 => "main().123"
  | 59 => "main().124"
  | 60 => "main().124.0"
  | 61 => "main().124.1"
  | 62 => "main().13"
  | 63 => "main().14"
  | 64 => "main().15"
  | 65 => "main().16"
  | 66 => "main().17"
  | 67 => "main().18"
  | 68 => "main().19"
  | 69 => "main().2"
  | 70 => "main().20"
  | 71 => "main().21"
  | 72 => "main().22"
  | 73 => "main().23"
  | 74 => "main().24"
  | 75 => "main().25"
  | 76 => "main().26"
  | 77 => "main().27"
  | 78 => "main().28"
  | 79 => "main().29"
  | 80 => "main().3"
  | 81 => "main().30"
  | 82 => "main().31"
  | 83 => "main().32"
  | 84 => "main().33"
  | 85 => "main().34"
  | 86 => "main().35"
  | 87 => "main().36"
  | 88 => "main().37"
  | 89 => "main().38"
  | 90 => "main().39"
  | 91 => "main().4"
  | 92 => "main().40"
  | 93 => "main().41"
  | 94 => "main().42"
  | 95 => "main().43"
  | 96 => "main().44"
  | 97 => "main().45"
  | 98 => "main().46"
  | 99 => "main().47"
  | 100 => "main().48"
  | 101 => "main().49"
  | 102 => "main().5"
  | 103 => "main().50"
  | 104 => "main().51"
  | 105 => "main().52"
  | 106 => "main().53"
  | 107 => "main().54"
  | 108 => "main().55"
  | 109 => "main().56"
  | 110 => "main().57"
  | 111 => "main().58"
  | 112 => "main().59"
  | 113 => "main().6"
  | 114 => "main().60"
  | 115 => "main().61"
  | 116 => "main().62"
  | 117 => "main().63"
  | 118 => "main().64"
  | 119 => "main().65"
  | 120 => "main().66"
  | 121 => "main().67"
  | 122 => "main().68"
  | 123 => "main().69"
  | 124 => "main().7"
  | 125 => "main().70"
  | 126 => "main().71"
  | 127 => "main().72"
  | 128 => "main().73"
  | 129 => "main().74"
  | 130 => "main().75"
  | 131 => "main().76"
  | 132 => "main().77"
  | 133 => "main().78"
  | 134 => "main().79"
  | 135 => "main().8"
  | 136 => "main().80"
  | 137 => "main().81"
  | 138 => "main().82"
  | 139 => "main().83"
  | 140 => "main().84"
  | 141 => "main().85"
  | 142 => "main().86"
  | 143 => "main().87"
  | 144 => "main().88"
  | 145 => "main().89"
  | 146 => "main().9"
  | 147 => "main().90"
  | 148 => "main().91"
  | 149 => "main().92"
  | 150 => "main().93"
  | 151 => "main().94"
  | 152 => "main().95"
  | 153 => "main().96"
  | 154 => "main().97"
  | 155 => "main().98"
  | 156 => "main().99"
  | 157 => "main().n_125.0"
  | 158 => "main().n_125.1"
  | 159 => "main().n_125.2"
  | 160 => "main().n_125.3"
  | 161 => "main().n_125.4"
  | 162 => "main().n_126.0"
  | 163 => "main().n_126.1"
  | 164 => "main().n_126.2"
  | 165 => "main().n_126.3"
  | 166 => "main().n_126.4"
  | 167 => "main().n_126.5"
  | 168 => "main().n_126.6"
  | 169 => "main().n_127.0"
  | 170 => "main().n_127.1"
  | 171 => "main().n_127.2"
  | 172 => "main().n_128.0"
  | 173 => "main().n_128.1"
  | 174 => "main().n_129.0"
  | 175 => "main().n_130.0"
  | 176 => "main().n_131.0"
  | 177 => "main().n_132.0"
  | 178 => "main().n_133.0"
  | 179 => "main().n_134.0"
  | 180 => "main().n_135.0"
  | 181 => "main().n_136.0"
  | 182 => "main().n_136.1"
  | 183 => "main().n_136.2"
  | 184 => "main().n_137.0"
  | 185 => "main().n_138.0"
  | 186 => "main().n_139.0"
  | 187 => "main().n_139.1"
  | 188 => "main().n_140.0"
  | 189 => "main().n_140.1"
  | 190 => "main().n_141.0"
  | 191 => "main().n_142.0"
  | 192 => "main().n_143.0"
  | 193 => "main().n_143.1"
  | 194 => "main().n_144.0"
  | 195 => "main().n_145.0"
  | 196 => "main().n_146.0"
  | 197 => "main().n_146.1"
  | 198 => "main().n_147.0"
  | 199 => "main().n_148.0"
  | 200 => "main().n_149.0"
  | 201 => "main().n_150.0"
  | 202 => "main().n_151.0"
  | 203 => "main().n_152.0"
  | 204 => "main().n_153.0"
  | 205 => "main().n_154.0"
  | 206 => "main().n_155.0"
  | 207 => "main().n_156.0"
  | 208 => "main().n_157.0"
  | 209 => "main().n_158.0"
  | 210 => "main().n_159.0"
  | 211 => "main().n_160.0"
  | 212 => "main().n_161.0"
  | 213 => "main().n_162.0"
  | 214 => "main().n_163.0"
  | 215 => "main().n_164.0"
  | 216 => "main().n_165.0"
  | 217 => "main().n_184.0"
  | 218 => "main().n_189.0"
  | 219 => "node_034.0"
  | 220 => "node_166.0"
  | 221 => "pair(scratch1,topwff,wffstack).0"
  | 222 => "pair(scratch1,topwff,wffstack).1"
  | 223 => "pair(scratch1,topwff,wffstack).2"
  | 224 => "pair(scratch1,topwff,wffstack).2.0"
  | 225 => "pair(scratch2,scratch1,topwff).0"
  | 226 => "pair(scratch2,scratch1,topwff).1"
  | 227 => "pair(scratch2,scratch1,topwff).2"
  | 228 => "pair(scratch2,scratch1,topwff).2.0"
  | 229 => "par1().0"
  | 230 => "par1().1"
  | 231 => "par2().0"
  | 232 => "par2().1"
  | 233 => "par3().0"
  | 234 => "par3().1"
  | 235 => "pushwff().0"
  | 236 => "select().0"
  | 237 => "select().1"
  | 238 => "select().2"
  | 239 => "select().3"
  | 240 => "unpair().n_002.0"
  | 241 => "unpair().n_005.0"
  | 242 => "unpair().n_005.1"
  | 243 => "unpair().n_005.2"
  | 244 => "unpair(scratch1,scratch2,prooflist).0"
  | 245 => "unpair(scratch1,scratch2,wffstack).0"
  | 246 => "unpair(topwff,scratch2,wffstack).0"
  | 247 => "unpair(topwff,scratch2,wffstack).1"
  | 248 => "unpair(topwff,scratch2,wffstack).2"
  | 249 => "unpair(topwff,scratch2,wffstack).3"
  | 250 => "v_1().0"
  | 251 => "v_2().0"
  | 252 => "v_3().0"
  | 253 => "v_4().0"
  | 254 => "wa().0"
  | 255 => "wa().1"
  | 256 => "wal().0"
  | 257 => "wal().1"
  | 258 => "wel().0"
  | 259 => "wel().1"
  | 260 => "weq().0"
  | 261 => "weq().1"
  | 262 => "wex().0"
  | 263 => "wex().1"
  | 264 => "while_decnz().n_000.0"
  | 265 => "while_decnz().n_007.0"
  | 266 => "while_decnz().n_018.0"
  | 267 => "while_decnz().n_044.0"
  | 268 => "while_decnz().n_044.0.0"
  | 269 => "while_decnz().n_083.0"
  | 270 => "while_decnz().n_083.0.0"
  | 271 => "while_decnz().n_100.0"
  | 272 => "while_decnz().n_100.0.0"
  | 273 => "while_decnz(axiomcode,()).0"
  | 274 => "while_decnz(nextproof,105).0"
  | 275 => "while_decnz(nextproof,105).1"
  | 276 => "while_decnz(nextproof,105).1.0"
  | 277 => "while_decnz(param1,()).0"
  | 278 => "while_decnz(param1,43).0"
  | 279 => "while_decnz(param1,85).0"
  | 280 => "while_decnz(param1,85).1"
  | 281 => "while_decnz(param1,85).1.0"
  | 282 => "while_decnz(param1,99).0"
  | 283 => "while_decnz(param2,()).0"
  | 284 => "while_decnz(param2,43).0"
  | 285 => "while_decnz(param2,82).0"
  | 286 => "while_decnz(param2,99).0"
  | 287 => "while_decnz(param3,()).0"
  | 288 => "while_decnz(param3,43).0"
  | 289 => "while_decnz(param3,82).0"
  | 290 => "while_decnz(scratch1,()).0"
  | 291 => "while_decnz(scratch1,3.axiomcode.inc).0"
  | 292 => "while_decnz(scratch1,3.axiomcode.inc).1"
  | 293 => "while_decnz(scratch1,3.nextproof.inc).0"
  | 294 => "while_decnz(scratch1,3.nextproof.inc).1"
  | 295 => "while_decnz(scratch1,3.param1.inc).0"
  | 296 => "while_decnz(scratch1,3.param1.inc).1"
  | 297 => "while_decnz(scratch1,3.param2.inc).0"
  | 298 => "while_decnz(scratch1,3.param2.inc).1"
  | 299 => "while_decnz(scratch1,3.param3.inc).0"
  | 300 => "while_decnz(scratch1,3.param3.inc).1"
  | 301 => "while_decnz(scratch1,3.scratch2.inc).0"
  | 302 => "while_decnz(scratch1,3.topwff.inc).0"
  | 303 => "while_decnz(scratch1,3.wffstack.inc).0"
  | 304 => "while_decnz(scratch1,9).0"
  | 305 => "while_decnz(scratch1,9).1"
  | 306 => "while_decnz(scratch1,9).1.0"
  | 307 => "while_decnz(scratch2,()).0"
  | 308 => "while_decnz(scratch2,3.prooflist.inc).0"
  | 309 => "while_decnz(scratch2,3.prooflist.inc).1"
  | 310 => "while_decnz(scratch2,3.topwff.inc).0"
  | 311 => "while_decnz(scratch2,3.wffstack.inc).0"
  | 312 => "while_decnz(scratch3,()).0"
  | 313 => "while_decnz(topwff,()).0"
  | 314 => "while_decnz(topwff,21).0"
  | 315 => "while_decnz(topwff,21).1"
  | 316 => "while_decnz(topwff,21).1.0"
  | 317 => "while_decnz(topwff,3.scratch1.inc).0"
  | 318 => "while_decnz(topwff,3.scratch1.inc).1"
  | 319 => "while_decnz(topwff,3.scratch2.inc).0"
  | 320 => "while_decnz(wffstack,3.topwff.inc).0"
  | 321 => "wim().0"
  | 322 => "wim().1"
  | 323 => "wn().0"
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
  List.length all_states = 394 /\ List.length zf2_table = 785.
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
