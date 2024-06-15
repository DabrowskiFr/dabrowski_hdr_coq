Require Import List.
(* Require Import Sorting. *)
Require Import Relation_Definitions.
(* Require Import Permutation. *)
Require Import Setoid.

Set Implicit Arguments.

Section Sort.

Class Sortable A (eqA : A -> A -> Prop) (leA : A -> A -> Prop) 
  (eqA_dec : forall (a b:A), {eqA  a b}+{~ eqA  a b}) (leA_dec : forall (a b:A), {leA  a b}+{leA b a}) :=
{
  Sortable_eq : Equivalence eqA;
  Sortable_reflexive : reflexive A leA;
  Sortable_transitive : transitive A leA;
  Sortable_antisymmetric : forall a b, leA a b -> leA b a -> eqA a b;
  Sortable_eqA_leA : forall a b, eqA a b -> leA a b
}.

 Variable A:Type.
 Variable leA: A -> A -> Prop.
 Variable eqA  : A -> A -> Prop.
 Hypothesis eqA_dec : forall (a b:A), {eqA  a b}+{~ eqA  a b}.
 Hypothesis leA_dec : forall (a b:A), {leA  a b}+{leA b a}.
 Hypothesis sortA : Sortable eqA leA eqA_dec leA_dec.


(** 
  Insertion of an element in a sorted list
*)
 Fixpoint insert (a:A)  (l:list A) {struct l} : (list A) :=
   match l  with
     |  nil => a::nil
     |  cons b l' =>  if (leA_dec a b)
       then (a::l)
       else (b::(insert a l'))
   end.

 Lemma insertIsCons: 
   forall (a:A) (l:list A),
   exists head, exists tail,
     insert a l = head :: tail /\
     (a = head \/ (leA  head a/\In head l)).
 Proof.
   intros a l.
   destruct l ; simpl.
     exists a. exists nil. split. reflexivity. left. reflexivity.
     destruct(leA_dec a a0).
       exists a. exists (a0::l). split. reflexivity. left. reflexivity.
       exists a0. exists (insert a l). split. reflexivity. right.
         split. assumption.
         left. reflexivity. 
 Qed.

 (* Lemma leASort: 
   forall (a:A) (l:list A),
     lelistA leA a l -> sort leA l -> forall e, In e l -> leA  a e.
 Proof.
   intros a l H H0 e H1.
   generalize dependent a.
   induction l.
     contradict H1.
     intros a0 H.
       apply lelistA_inv in H.
       destruct(eqA_dec e a) as [HeqA | HeqA].
       apply sortA with (y:=a). assumption. apply sortA.
        apply sortA. assumption.
       apply IHl.
         apply sort_inv in H0. destruct H0. assumption.
         apply in_inv in H1.  destruct H1 as [Heq | Hin].
           contradict HeqA. apply sortA. rewrite Heq. apply sortA.
           assumption.
           apply sort_inv in H0. destruct H0.
           destruct l. constructor.
           constructor. apply lelistA_inv in H2.
           apply sortA with (y:=a).
           assumption. assumption.
 Qed. *)

(**
 The insertion of an element in a sorted list gives a sorted list
*)
 (* Lemma insertSort: 
   forall (a:A) (l:list A), 
     sort leA l -> sort leA (insert a l).
 Proof.
   intros a.
   apply Sorted_ind.
     constructor. constructor. constructor.
     intros a0 l H H0 H1.
     simpl.
     destruct(leA_dec a a0).
       (* Case true *)
       constructor. constructor. assumption. assumption.
       constructor. assumption.
       (* Case false *)
       constructor.
         assumption.
         destruct (insertIsCons a l) as [head Hinsert].
         destruct Hinsert as [tail Hinsert].
         destruct Hinsert as [Hdecomp Horder].
         rewrite Hdecomp.
         constructor.  destruct Horder as [H2|H2]. rewrite <-H2. assumption.
         destruct H2 as [ _ H2].
         eapply leASort with (l:=l) ; assumption.
 Qed. *)

 (* Lemma permutationInsert:
   forall (a:A) (l:list A),
     Permutation (a::l) (insert a l).
 Proof.
   induction l ; simpl.
   - constructor. constructor.
   - destruct(leA_dec a a0).
     apply Permutation_refl.
     apply perm_trans with ((a0::a::l)).
     apply perm_swap.
     now apply Permutation_cons. 
 Qed. *)

 (* Lemma permutationInsertInside:
   forall (a:A) (l1 l2:list A),
   Permutation l1 l2 ->
   Permutation (insert a l1) (insert a l2).
 Proof.
   induction l1 ; destruct l2 ; simpl.
   constructor. assumption.
   intro H. apply Permutation_nil_cons in H. destruct H. 
   intro H. apply Permutation_sym in H. apply Permutation_nil_cons in H.
   destruct H. 
   destruct(leA_dec a a0); destruct(leA_dec a a1).
   intro H. constructor. assumption.
   intro H. apply Permutation_trans with (a1::a::l2).
   apply Permutation_trans with (a::a1::l2).
   constructor. apply H.
   constructor.
   constructor. apply permutationInsert.
   intro H.
   apply Permutation_trans with (a0::a::l1).
   constructor. apply Permutation_sym. apply permutationInsert.
   apply Permutation_trans with (a::a0::l1). constructor. 
   constructor. apply H.
   intro H.
   apply Permutation_trans with (a0::a::l1).
   constructor. apply Permutation_sym. apply permutationInsert.
   apply Permutation_trans with (a::a0::l1). constructor. 
   apply Permutation_trans with (a::a1::l2). constructor. apply H.
   apply Permutation_trans with (a1::a::l2). constructor. 
   constructor. apply permutationInsert.
 Qed. *)

(**
  Insertion sort
*)
 (* Program Definition insertSorting (l : list A) : 
  {lo : list A | Permutation l lo /\ sort leA lo /\ lo = fold_right insert nil l} :=
   fold_right insert nil l.
 Next Obligation.
  split.
  (* left *)
   induction l.
     constructor.
     simpl.
     apply Permutation_trans with (insert a l). apply permutationInsert.
     apply permutationInsertInside. assumption.
   (* right *)
   split.
   induction l.
     constructor.
     apply insertSort.
     assumption.
    reflexivity.
 Defined. *)

 (* WARNING: Program was not working here *)

(* Definition insertSorting1 (l : list A) : list A :=
   proj1_sig (insertSorting l). *)

(**
  Compatibility of length with insert_sorting
*)

 Lemma insertLength : forall l a, length (insert a l) = S (length l).
 Proof.
  intros l a.
  induction l.
   reflexivity.
   simpl.
   destruct (leA_dec a a0).
    reflexivity.
    simpl. rewrite IHl.
    reflexivity.
 Qed.

 (* Lemma sortLength : forall l, length (insertSorting1 l) = length l.
 Proof.
  intros l.
  unfold insertSorting1.
  simpl.
  induction l.
   reflexivity.
   simpl. rewrite insertLength.
   rewrite IHl.
   reflexivity.
 Qed. *)



End Sort.

Section Example.

Require Import Arith.

Definition le_dec1 : forall n m, {n <= m} + {m <= n}.
Proof.
induction n.
left. intuition.
destruct m. right. intuition.
destruct (IHn m).
left ; intuition.
right ; intuition.
Defined.

Program Instance sortle : Sortable eq le eq_nat_dec le_dec1.
Next Obligation.
  intuition.
Qed.
Next Obligation.
  intros x y z H1 H2. apply le_trans with y ; intuition.
Qed.
Next Obligation.
  intuition.
Qed.
(*
Eval compute in (projT1 (insertSorting sortle  (4::3::5::2::nil))).
*)
End Example.
