Require Import Nat.
Require Import Arith.
Require Import Lia.

(** [min x y] can be written [x - (x - y)] as we compute over natural numbers *)
Lemma min_minus x y: min x y = x - (x - y).
Proof.
lia.
Qed.

Arguments min_minus {x y}.

Lemma lt_min : forall n m m', n < min m m' -> n< m /\ n< m'.
Proof. 
  intros n m m' H.
  split;   rewrite min_minus in H;  lia.
Qed.
Arguments lt_min [ n m m'].
