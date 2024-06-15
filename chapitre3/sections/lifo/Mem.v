Require Import List.
Require Import Classes.EquivDec.

Set Implicit Arguments.

Fixpoint mem (A:Type)(eqA: EqDec A eq)(a:A)(l:list A):bool:=
  match l with 
    | nil => false 
    | cons h t => if (eqA h a) then true else mem eqA a t
  end.

Lemma inMemEq: 
  forall(A:Type)(eqA: EqDec A eq)(l:list A)(a:A),
    In a l <-> mem eqA a l = true.
Proof.
  intros A eqA l a; split; intro H.
  (* -> *)
  induction l as [  | a' l]; simpl in *.
    elim H.
    destruct H.
      rewrite H; case_eq(eqA a a); intros H'; 
        auto; elim H'; apply eq_refl.
      rewrite IHl; case_eq(eqA a' a); auto. 
  (* <- *)
  induction l as [ | a' l]; simpl in *.
    discriminate.
    destruct(eqA a' a); intuition.
Qed.


