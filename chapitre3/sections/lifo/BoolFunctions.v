(** * Booleans functions on lists *)
From Stdlib Require Import List.
From Stdlib Require Import Arith.

Set Implicit Arguments.

Definition isNil (A:Type)(l:list A) :=
  match l with 
    |nil => true
    | _  => false 
  end.

Hint Unfold isNil : core.

Lemma isNilTrue : 
  forall (A:Type)(l:list A),
    isNil l = true -> 
    l = nil.
Proof.
  intros A l H.
  destruct l. reflexivity.
  discriminate H.
Qed.
  
Lemma isNilFalse : 
  forall (A:Type)(l:list A),
    isNil l = false ->
    exists a, exists l', l = a::l'.
Proof.
  intros A l H.
  destruct l. 
  discriminate H.
  exists a. exists l. reflexivity.
Qed.

Definition isLengthOf (A:Type) (n:nat) (l:list A)  :=
  Nat.eqb (List.length l) n.

Lemma lengthIsLengthOf (A:Type) (l:list A) :
  isLengthOf (length l) l = true.
Proof.
  induction l; auto.
Qed.
