(** B21: the abstract block machine (pure definitions, no TM). *)
From Coq Require Import Lia PeanoNat List Bool.
Import ListNotations.
Set Default Goal Selector "!".

Fixpoint iter {X : Type} (n : nat) (g : X -> X) (x : X) : X :=
  match n with
  | 0 => x
  | S n' => g (iter n' g x)
  end.

Lemma iter_S' : forall {X : Type} n (g : X -> X) x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

Lemma iter_add : forall {X : Type} a b (g : X -> X) x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

(** level maps of the level-1 engine: h 0 = H_2 (x -> x+4), h (S m) x = h m iterated x+3 times from 1 *)
Fixpoint h (m x : nat) : nat :=
  match m with
  | 0 => x + 4
  | S m' => iter (x + 3) (h m') 1
  end.

Fixpoint engf (m : nat) (ds : list nat) (x : nat) : nat :=
  match ds with
  | [] => x
  | d :: t => engf (S m) t (iter (d - 1) (h m) x)
  end.

Definition restore (ms : list nat) : list (list nat) := rev (map (fun m => repeat 1 m) ms).

Definition Xl (k : nat) : list nat :=
  match k with
  | 0 => [5]
  | S k' => [4] ++ repeat 1 k' ++ [2]
  end.

Definition all1 (b : list nat) : bool := forallb (fun d => d =? 1) b.

(** split off the leading 1s *)
Fixpoint lsplit (l : list nat) : nat * list nat :=
  match l with
  | 1 :: t => let '(p, r) := lsplit t in (S p, r)
  | _ => (0, l)
  end.

Inductive res := Next (bs : list (list nat)) | Halt | Stuck.

(** the sweep: J-acc x, passed counts ms (nearest first), blocks R to the right *)
Fixpoint sweep (x : nat) (ms : list nat) (R : list (list nat)) : res :=
  match R with
  | [] => Stuck
  | b :: R' =>
    if all1 b && (2 <=? length b) then sweep (x + 2) (pred (length b) :: ms) R' else
    match b with
    | S (S d) :: T =>
        if Nat.even x && (4 <=? x) then
          match ms with
          | S m :: ms' => Next (restore ms' ++ (repeat 1 (S m) ++ Xl ((x - 4) / 2)) :: (S d :: T) :: R')
          | _ => Stuck
          end
        else Stuck
    | [1] =>
        match R' with
        | [] =>
            if (x mod 4 =? 2) then Halt else
            if (x mod 4 =? 0) && (4 <=? x) then
              match ms with
              | S m :: ms' => Next (restore ms' ++ (repeat 1 (S m) ++ [4; 1]) :: repeat [2] (x / 4))
              | _ => Stuck
              end
            else Stuck
        | [2] :: R'' => if Nat.even x && (2 <=? x) then Next (restore ms ++ Xl ((x - 2) / 2) :: [1] :: R'') else Stuck
        | _ => Stuck
        end
    | 1 :: tl =>
        match lsplit tl, ms with
        | (p, S (S e) :: T), S m :: _ =>
            if 1 <=? x then Next (restore ms ++ (repeat 1 p ++ (x + 3) :: S e :: T) :: R') else Stuck
        | _, _ => Stuck
        end
    | _ => Stuck
    end
  end.

Definition astep (bs : list (list nat)) : res :=
  match bs with
  | (x :: d :: ds) :: R =>
      if forallb (fun d => negb (d =? 0)) (d :: ds) then sweep (engf 0 (d :: ds) x + 3) [length (d :: ds)] R
      else Stuck
  | _ => Stuck
  end.


(** ** the same machine, parametric in the refill rule (engine, sweep and Lemma D layers do not depend on it) *)
Section Generic.
Variable refill : nat -> list nat -> res.
(** the sweep: J-acc x, passed counts ms (nearest first), blocks R to the right *)
Fixpoint sweepG (x : nat) (ms : list nat) (R : list (list nat)) : res :=
  match R with
  | [] => Stuck
  | b :: R' =>
    if all1 b && (2 <=? length b) then sweepG (x + 2) (pred (length b) :: ms) R' else
    match b with
    | S (S d) :: T =>
        if Nat.even x && (4 <=? x) then
          match ms with
          | S m :: ms' => Next (restore ms' ++ (repeat 1 (S m) ++ Xl ((x - 4) / 2)) :: (S d :: T) :: R')
          | _ => Stuck
          end
        else Stuck
    | [1] =>
        match R' with
        | [] => refill x ms
        | [2] :: R'' => if Nat.even x && (2 <=? x) then Next (restore ms ++ Xl ((x - 2) / 2) :: [1] :: R'') else Stuck
        | _ => Stuck
        end
    | 1 :: tl =>
        match lsplit tl, ms with
        | (p, S (S e) :: T), S m :: _ =>
            if 1 <=? x then Next (restore ms ++ (repeat 1 p ++ (x + 3) :: S e :: T) :: R') else Stuck
        | _, _ => Stuck
        end
    | _ => Stuck
    end
  end.

Definition astepG (bs : list (list nat)) : res :=
  match bs with
  | (x :: d :: ds) :: R =>
      if forallb (fun d => negb (d =? 0)) (d :: ds) then sweepG (engf 0 (d :: ds) x + 3) [length (d :: ds)] R
      else Stuck
  | _ => Stuck
  end.
End Generic.

(** B21's refill test (J-acc x before the final P is absorbed; halt iff x = 2 mod 4) *)
Definition refill21 (x : nat) (ms : list nat) : res :=
  if (x mod 4 =? 2) then Halt else
  if (x mod 4 =? 0) && (4 <=? x) then
    match ms with
    | S m :: ms' => Next (restore ms' ++ (repeat 1 (S m) ++ [4; 1]) :: repeat [2] (x / 4))
    | _ => Stuck
    end
  else Stuck.

Lemma sweep_G : forall R x ms, sweep x ms R = sweepG refill21 x ms R.
Proof.
  induction R as [| b R IH]; intros x ms; [reflexivity |]. cbn [sweep sweepG].
  destruct (all1 b && (2 <=? length b)); [apply IH | reflexivity].
Qed.

Lemma astep_G : forall bs, astep bs = astepG refill21 bs.
Proof.
  intros bs. unfold astep, astepG. destruct bs as [| [| x [| d ds]] R]; try reflexivity.
  all: destruct (forallb _ _); [apply sweep_G | reflexivity].
Qed.
