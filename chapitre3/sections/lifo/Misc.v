(** Various utilities for manipulating lists.*)

Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import sections.lifo.Length.
Require Import sections.lifo.Firstn_skipn.

Section Misc.
Set Implicit Arguments.

Variable A :Type.

Definition listProj (P:A->Prop) (l:list (sig P)) : list A :=
  map (proj1_sig (P:=P)) l.

  Definition is_nil (l:list A) :=
    match l with 
      |nil => true
      | _  => false 
    end.


  Lemma is_nil_true : 
    forall (l:list A),
      is_nil l = true -> l = nil.
  Proof.
    unfold is_nil.
    intros l H.
    destruct l. reflexivity.
    discriminate H.
  Qed.
  
  Lemma is_nil_false : 
    forall (l:list A),
      is_nil l = false ->exists a, exists l', l = a::l'.
  Proof.
    unfold is_nil.
    intros  l H.
    destruct l. 
    discriminate H.
    exists a. exists l. reflexivity.
  Qed.

End Misc.

Set Implicit Arguments.

(** * Functions on lists **)

(** The function [zip] applies a binary function to two lists, elementwise: 
   [zip f [x1;...;xn] [y1;...;yn] = [f x1 y1; ... ; f xn yn] ]. **) 

Definition zip (A B C : Type) (f: A->B->C) (l1:list A)(l2 : list B) : list C := 
  List.map (fun pair=>f(fst pair)(snd pair)) (List.combine l1 l2).

(** The function [shift] shifts the elements of a list to the right or to the left depending on the sign of the [d] integer. If it is positive the shifting is done to the right, otherwise to the left. The values that are pushed "outside" the list are replaced by values 
indicated by function [f]: at some index [i] the value will be [f(i)]. **)

Definition shift (A:Type)(d:Z)(f:nat->A)(l:list A) : list A := 
  match d with 
    | Z0 => l 
    | Zpos d =>
      let d_nat := Nat.min (nat_of_P d) (List.length l) in 
        List.app
        (List.map f (List.seq 0 d_nat))
        (firstn (minus (List.length l) d_nat) l)
    | Zneg d =>
      let d_nat := Nat.min (nat_of_P d) (List.length l) in 
        List.app
        (skipn d_nat l)
        (List.map f (List.seq (minus (List.length l) d_nat) d_nat))
  end.

Hint Rewrite seq_length map_length firstn_length skipn_length app_length combine_length : length.

Lemma shift_length :
  forall (A:Type)(d:Z)(f:nat->A)(l:list A),
    List.length (shift d f l) = List.length l.
Proof.
Admitted.
  (* intros A d f l; destruct d; simpl.
    trivial.
    autorewrite with length.
      destruct(lt_eq_lt_dec(nat_of_P p) (length l)) as [H | H].
        destruct H as [H | H].
        rewrite Min.min_l; try lia.
        rewrite Min.min_l; try lia.
        rewrite Min.min_l; try lia.
        rewrite Min.min_l; try lia.
        rewrite Min.min_r; try lia.
        rewrite Min.min_l; try lia.
        autorewrite with length;
          destruct(lt_eq_lt_dec(nat_of_P p) (length l)) as [H | H].
            destruct H as [H | H].
            rewrite Min.min_l; try lia.
            rewrite Min.min_l; try lia.
            rewrite Min.min_r; try lia.
Qed. *)

Hint Rewrite shift_length fold_right_length_app : length.


