Require Import List.

Set Implicit Arguments.

(** If equality is decidable on a type A, then when an element belongs
to a list, it is possible to decompose the list as a list that does
not contain the element, the element, and another list. *)

Lemma In_decomp : forall A (a:A) l (eqDecA:forall (a a':A),{a = a'}+{a<>a'}),  
  In a l -> 
  exists l1, exists l2, 
    ~In a l1/\ l=l1++a::l2.
Proof.
  intros A0 a l eqDecA. induction l.
  intros H. contradiction.
  destruct (eqDecA a a0).
      exists nil; exists l. 
      split;[simpl;auto | rewrite e; reflexivity]. 
      
      intro H; simpl in H;destruct H;[ symmetry in H; contradiction|].                            
      destruct (IHl H) as [l1 [l2 [not_in_l1 l_eq]]].
      exists (a0::l1); exists l2; split.
      simpl.
      intro in_a_l0. destruct in_a_l0;
      [symmetry in H0|]; contradiction.
      rewrite l_eq.
      reflexivity.
 Qed.

(**  There is at least one element in a non-empty list *) 
Lemma InList: 
  forall (A : Type)(l:list A), 
    l <> nil -> 
    exists a:A, In a l.
Proof.
  induction l; intro H.
  - elim H; reflexivity.
  - exists a.
    constructor; reflexivity.
Qed.

Ltac inPresent := 
  match goal with
    | [  |- In ?a ?l ] =>
      assumption
    | [  |- In ?a ?l ] =>
      firstorder
    | [  |- In ?a (?a::?l) ] =>
      apply in_eq
    | [  |- In ?a (?x::?l) ] =>
      simpl; right; inPresent
    | [  |- In ?a (?l1++?a::?l2) ] =>
      apply in_or_app; right; apply in_eq
    | [  |- In ?a (?l1++?x::?l2) ] =>
      apply in_or_app; left; inPresent
    | [  |- In ?a (?l1++?x::?l2) ] =>
      apply in_or_app; right;simpl; right; inPresent
  end.