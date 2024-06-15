Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.

Generalizable All Variables.

Fixpoint takeWhile `(p:A->bool)(xs:list A) : list A := 
  match xs with 
    | []    => []
    | x::xs => if (p x) 
               then x::(takeWhile p xs) else []
  end.

Lemma inTakeWhile `(p:A->bool)(xs:list A)(x0:A) : 
  In x0 (takeWhile p xs) ->
  p x0 = true.
Proof.
  induction xs as [|x xs IH]; intro Hin.
  - inversion Hin.
  - simpl in *.
    case_eq(p x); intro Hp; rewrite Hp in Hin. 
    + inversion Hin. 
      * subst. trivial.
      * now apply IH.
    + inversion Hin.
Qed.

Fixpoint dropWhile `(p:A->bool)(xs:list A) : list A := 
  match xs with 
    | []    => []
    | x::xs => if (p x) 
               then (dropWhile p xs) else x::xs
  end.

Lemma takedropWhile `(p:A->bool)(xs:list A) :
  xs = (takeWhile p xs)++(dropWhile p xs).
Proof.
  induction xs.
  + trivial.
  + simpl.
    destruct(p a).
    * rewrite IHxs at 1.
      apply app_comm_cons.
    * trivial.
Qed.

Lemma dropWhileNotNil `(p:A->bool)(xs:list A)(x:A) :
  In x xs -> 
  p x = false -> 
  dropWhile p xs <> [].
Proof.
  induction xs; intros Hin Hp.
  - inversion Hin.
  - destruct Hin; subst.
    + simpl; rewrite Hp.
      intro. discriminate.
    + simpl. destruct(p a).
      * now apply IHxs.
      * intro. discriminate.
Qed.