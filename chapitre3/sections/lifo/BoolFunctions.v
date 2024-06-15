(** * Booleans functions on lists *)
Require Import List.
Require Import Arith.

Set Implicit Arguments.

Definition isNil (A:Type)(l:list A) :=
  match l with 
    |nil => true
    | _  => false 
  end.

Hint Unfold isNil.

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
  beq_nat (List.length l) n.

Lemma lengthIsLengthOf (A:Type) (l:list A) :
  isLengthOf (length l) l = true.
Proof.
  induction l; auto.
Qed.
