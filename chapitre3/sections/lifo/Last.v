Require Import List.

Require Import sections.lifo.Notations. 

Lemma last_last : forall A lst (x:A) d,   last (lst ++ [x]) d =  x.
Proof.
Admitted.
  (* intros A lst x d.
  induction lst.
  reflexivity.
  simpl.
  case_eq (lst ++ [x]).
  intros H. contradict H; firstorder.
  intros a1 l0 H.
  rewrite <- H.
  clear H.

  apply IHlst.
Qed. *)
Arguments last_last [A]. 

Hint Rewrite last_last : last.
Hint Rewrite last_last : list.


Lemma last_indep: 
  forall (A:Type)(xs:list A)(x d1 d2 : A), 
    last (x::xs) d1 = last (x::xs) d2.
Proof.
  induction xs as [ | x' xs' IH]; trivial.
  intros x d1 d2; simpl in *; trivial. 
Qed.
Arguments last_indep [A]. 


Require Import sections.lifo.Option.

(** Last element of a list, using option type for dealing with empty list case *)
Definition last_option (A:Type) (lst : list A) := match lst with [] => None | a::l => Some (List.last lst a ) end.

Arguments last_option [A]. 

(** [last_option] return the  last element of a list when it exists   *)
Lemma last_option_app_r : forall A lst (x:A),   last_option (lst ++ [x]) = Some x.
Proof.
Admitted.
  (* intros A lst x.
  case_eq(lst ++ [x]).
  intros  H.   contradict H; firstorder.
  intros a l H.
  unfold last_option.
  rewrite <- H.
  rewrite last_last.  
  reflexivity.
Qed. *)

Arguments last_option_app_r [A]. 
Hint Rewrite last_option_app_r : last.
Hint Rewrite last_option_app_r : list.

(** [last_option] return the last element of the second list of a list concatenation when its not empty   *)

Lemma last_option_app: 
    forall (A:Type)(l1 l2:list A),
      l2<>nil -> last_option (l1++l2) = last_option l2.
Proof.
    intros A l1 l2 H ; revert l1.
    induction l2.
      elim H; trivial.
      intros l1.
      change (a::l2) with ([a]++l2).
      rewrite app_assoc. 
      destruct l2.       
         simpl. rewrite app_nil_r; rewrite last_option_app_r; reflexivity. 
         assert (H' : a0::l2 <>[]) by discriminate.
         do 2 rewrite (IHl2 H') .  
         reflexivity.
Qed.
  
  (** *** switching between last_option and last.  
     
     when the list is not empty *)
Lemma last_last_option_non_empty: 
  forall (A:Type)(l:list A), 
    l<>nil -> (forall a:A, Some (last l a) = last_option l).
Proof.
  induction l using rev_ind; intros H default.
  elim H; trivial.
  rewrite last_option_app_r; rewrite last_last; trivial.
Qed.

(** in the general case  *)
Lemma last_last_option (A:Type) :
  forall (d:A) l,
    last l d = (fun d  v =>  (match v with None => d | Some a => a end)) d (last_option l).
  intros d l. revert d.
  induction l; try reflexivity.
  simpl.
  intros d.
  rewrite (IHl a).
    destruct l.
  reflexivity.
  rewrite (IHl d).
  simpl.  
  reflexivity.
Qed.  


(** Strong functions  *)

  Program Definition strongLast (A:Type)(l:list A | l<>nil) : 
    { a : A | Some a = last_option (proj1_sig l) } := noSome( last_option (proj1_sig l)).
  Next Obligation.
    simpl; induction l.
      elim H; trivial.
      simpl ; destruct l.
        discriminate.
        discriminate.
  Defined.
  Arguments strongLast [A].

  Definition sLast (A:Type)(l:{l:list A | l<>nil}) : A := proj1_sig (strongLast l).
  Arguments sLast [A].

  Program Definition sLastProp:
    forall (A:Type)(l:list A | l<>nil),
      Some (sLast l) = last_option l.
  Proof.
    intros A l; unfold sLast, strongLast; apply someNoSomeId.
  Qed.

(*  *)