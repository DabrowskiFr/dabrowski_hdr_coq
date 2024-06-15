Require Import Coq.Lists.List.
Require Import AlgebraClasses.
(* Require Import LIFO.List.Firstn_skipn. *)

(** * Facts about [app] *)

Lemma app_cons: 
  forall (A:Type)(l:list A)(a:A), 
    a::l = (a::nil) ++ l.
Proof.
  intros A l.
  induction l. 
  reflexivity.
  rewrite IHl. reflexivity.
Qed.


(* To be removed, is solve by firstorder *)
Lemma inAppCons:
  forall (A:Type)(l1 l2:list A)(a:A),
    In a (l1++a::l2).
Proof.
  intros A l1 l2 a.
  apply in_app_iff; right; simpl; left; reflexivity.
Qed.


  
Lemma app_l_l'_nil : forall A (l l' : list A), l = l++l' -> l'=nil.
  intros A.
  induction l. intros; simpl in H; symmetry; auto.
  intros.
  simpl in H. injection H. intro H'; rewrite <- H' in *. apply IHl. assumption.
Qed.

Global Instance appAssoc (A:Type) : Associative (eqA:=eq) (@app A).
Proof.
  constructor.
  intros x y z.
  rewrite app_assoc.
  reflexivity.
Qed.

Global Instance appAssocGen (A:Type) R `{ Equivalence (list A) R} : Associative (eqA:=R) (@app A).
Proof.
  constructor.
  intros x y z.
  rewrite app_assoc.
  reflexivity.
Qed.

(** [nil] is neutral for append  *)
Global Program Instance nil_is_app_unit A : Neutral (eqA:=eq) (app (A:=A)) nil.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
(* Solve Obligations using (constructor;  auto using app_nil_r).  *)

(* (* this lemma causes a circular dependency with firstn_skipn *)
 Lemma app_length_eq (A: Type) : 
  forall l1 l2 l1' l2' : list A, length l1 = length l1' -> l1++l2 = l1'++l2' -> l1=l1'/\ l2=l2'.
Proof.
  intros l1 l2 l1' l2' lenEq appEq.
  split.
  replace l1 with (firstn (length l1) (l1++l2)).
  replace l1' with (firstn (length l1) (l1'++l2')).
  rewrite appEq.
  reflexivity.
  rewrite lenEq.
  i
  rewrite  Firstn_skipn.firstn_app_length; reflexivity.
  rewrite  Firstn_skipn.firstn_app_length; reflexivity.
  replace l2 with (skipn (length l1) (l1++l2)).
  replace l2' with (skipn (length l1) (l1'++l2')).
  rewrite appEq.
  reflexivity.
  rewrite lenEq.
  rewrite  Firstn_skipn.skipn_app_length; reflexivity.
  rewrite  Firstn_skipn.skipn_app_length; reflexivity.
Qed.
*)

Hint Rewrite app_length :length.