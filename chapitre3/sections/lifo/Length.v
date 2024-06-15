(** *Facts about [length] and definition of a predicate [Length]  *)
(* Unset Automatic Introduction.    coq 8.3_rc1 *)

(** *Facts about length of lists *)

Require Import List.
Require Import Lia.
Open Scope list_scope.

Require Import sections.lifo.proof_unicity.

Create HintDb length.

(** length of projection of {l : list | P l}
   trivial but useful in the autorewrite Hint
  *)
Lemma lengthSig:
  forall (A:Type)(P:list A->Prop)(l:list A)(Hl:P l),
    length(proj1_sig (exist P l Hl)) = length l.
Proof.
  intros A P l Hl.
  auto.
Qed.    

Hint Rewrite lengthSig: length.


(** if [l] has length [0], then [l=nil] *)
Lemma lengthNil : 
  forall (A:Type)(l : list A), 
    length l=0 -> 
    l=nil.
Proof.
  intros A0 l lenl.
  induction l.
  reflexivity.
  simpl in lenl. 
  absurd  (S (length l) = 0).
  lia; assumption.
  assumption.
Qed.

(** if [l] has length [0] iff [l=nil] *)
Lemma lengthNilEquiv : 
  forall (A:Type)(l : list A), 
    length l=0 <-> 
    l=nil.
Proof.
  intros A0 l; split ; 
    [ apply lengthNil | intro ; subst; reflexivity ].
Qed.

Global Ltac lengthNil :=
  match goal with 
    | [lenl : 0 = length ?l|-_]=>
      symmetry in lenl; rewrite (lengthNil l lenl) in *
    | [lenr : length ?l=0|-_]=>
      rewrite (lengthNil l lenr) in *
  end. 

(** if [l] has length > [0], then [l=a::l1] *)
Lemma lengthPos : 
  forall (A:Type)(l : list A) n , 
    length l=S n -> 
    exists a, exists l1, l=a::l1.
Proof.
  intros A0 l n lenl.
  induction l.
  simpl in lenl; discriminate.
  exists a. exists l. 
  reflexivity.
Qed.

(* TODO: Is it really usefull ? The next lemma seems sufficient. *)
Lemma lengthCons: 
  forall (A B:Type)(a1:A)(l1:list A)(l:list B),
  length(a1::l1)=length l -> 
  exists b:B,exists l2:list B,l=b::l2.
Proof.
  intros A B a1 l1 l H.
  induction l1; destruct l.
  simpl in H ; discriminate H.
  exists b. exists l. reflexivity.
  simpl in H ; discriminate H.
  exists b. exists l. reflexivity.
Qed.

(** If the length of a list is positive, this list has at least one element *)  
Lemma lengthS: forall (A:Type)(l:list A)(n:nat),
  S n =length l -> exists a:A,exists la:list A,l=a::la.
Proof.
  intros A l.
  induction l ; intros n H.
  discriminate H. 
  exists a. exists l. reflexivity.
Qed.

Arguments lengthNil [A].
Arguments lengthPos [A] l [n].


(* Ltac copy := fun h h' =>
    let t:= type of h  in 
      assert (h' :t ) by assumption.
*)


(* Require Import LIFO.Tactics.*)

(*Ltac lengthPos lenl:=
    match type of lenl with             
      |  S ?n = length ?l=>
        let lenl':=fresh lenl in
          copy lenl as lenl';
          symmetry in lenl';
              apply (lengthPos l) in lenl';
                let H':=fresh "H'" in
                let l':=fresh "l'" in
                let a:=fresh "a" in
                destruct lenl' as [a [l' H']];
                  try (rewrite H' in 
                  *)
                  (*  
      | length ?l= S ?n=>
        let lenl':=fresh lenl in
          copy lenl as lenl' ;
          apply (lengthPos l) in lenl';
                let H':=fresh "H'" in
                let l':=fresh "l'" in
                let a:=fresh "a" in
                destruct lenl' as [a [l' H']];
                  try (rewrite H' in * )
      | length ?l > ?n=>
        let lenl':=fresh "lenl" in let H' := fresh "l_decomp" in
        assert(lenl' :n < length l) by omega;
          apply (S_pred  (length l)) in lenl';        
            apply (lengthPos l) in lenl';
                let H':=fresh "H'" in
                let l':=fresh "l'" in
                let a:=fresh "a" in
              destruct lenl' as [a [l' H']];
                try (rewrite H' in 
  end.
  *)

Lemma lengthPosNotNil :forall A (l : list A) (H:length l> 0 ), l <> nil.
  intros A l H.
  destruct l.
  simpl in H.
  exfalso; lia.
  intro.  
  discriminate.
Qed.


Lemma lengthPosNotNil' :forall A (l : list A) n (H:length l> S n ), l <> nil.
  intros A l n H.
  Proof.
  Admitted.

Lemma lengthNotNil : 
  forall (A:Type)(l : list A), 
    length l<>0 -> 
    l<>nil.
Proof.
  intros A0 l Hlen.
  destruct l.
    elim Hlen; reflexivity.
    discriminate.
Qed.

Lemma lengthNotNil' : 
  forall (A:Type)(l : list A), 
    l<>nil->
    length l<>0 
    .
Proof.
  intros A0 l Hlen.
  destruct l.
    elim Hlen; reflexivity.
    discriminate.
Qed.

Lemma lengthNotNil'' : 
  forall (A:Type)(l : list A), 
    l<>nil->
    length l>0 
    .
Proof.
  intros A0 l Hlen.
  destruct l.
    elim Hlen; reflexivity.
    simpl; auto with arith.
Qed.

Lemma lengthNotNil''' : 
  forall (A:Type)(l : list A) , 
    l<>nil->
    length l>= 1.
Proof.
  intros A0 l Hlen.
  destruct l. 
    elim Hlen; reflexivity.
    apply lengthNotNil'' in Hlen;simpl in *.
    auto with arith.
Qed.

Lemma lengthSuccNotNil :forall A (l : list A) n (H:length l = S n ), l <> nil.
  intros A l n H.
Admitted.

Hint Resolve lengthNotNil lengthNotNil' lengthNotNil'' lengthNotNil''' lengthPosNotNil' lengthPosNotNil lengthSuccNotNil: list.

Hint Rewrite app_length rev_length map_length fold_left_length : length.
Hint Rewrite  split_length_l split_length_r combine_length prod_length seq_length  : length.

Lemma fold_right_length_app:
  forall (A:Type)(l:list A)(ll:list(list A)),
    List.length(fold_right (@app A) l ll) = 
    fold_right plus (List.length l) (List.map (@List.length A) ll).
Proof.
  intros A l ll.
  induction ll; trivial; simpl;
    autorewrite with length; intuition.
Qed.

Hint Rewrite fold_right_length_app : length.

(** length does not depend on elements  *)
Lemma lengthValueIndependent: forall (A:Type)(l1 l2:list A)(a b:A),
  List.length (l1++a::l2) = List.length(l1++b::l2).
Proof.
  intros A l1 l2 a b.
  autorewrite with length.
  trivial.
Qed.


(** * [Length] predicate useful as it is proof irrelevant  

   WARNING : PROOF IRRELEVANCE HAS NOT BEEN PROVED YET
  *)
Require Import proof_unicity.

(* Definition Length := has_length. *)


(* Lemma Length_length (A:Type) (l: list A) : Length l (length l). *)
(* Proof. *)
(*   induction l; simpl. *)
(*   constructor;  reflexivity. *)
(*   simpl. *)
(*   constructor. *)
(*   assumption. *)
(* Qed. *)

(* (** If Length l n and Length l n' then n=n'  *) *)
(* Lemma Length_unique : forall (A:Type) (l: list A) n n', Length l n ->Length l n' -> n = n'. *)
(* Proof. *)
(*   induction l. *)
(*   intros n n' H H0.   *)
(*   inversion H. inversion H0. reflexivity. *)
  
(* intros n n' H H0. *)
(* inversion H. inversion H0. *)
(* f_equal. *)
(* apply IHl;  assumption. *)
(* Qed. *)


(*   Scheme Length_ind' := Induction for Length Sort Prop. *)


(* (** If Length l n and Length l n' then n=n'  *) *)
(* Lemma Length_eq :  *)
(*   forall (A:Type)( eq_A_dec : forall x y : A, {x=y}+{x<>y}) *)
(*     (l : list A) n  (len len'  : Length l n) ,   *)
(*     len = len'. *)
(* Proof. *)
(*     induction len using Length_ind'; intro len'.     *)
(*     change (Length_nil ) with *)
(*       (eq_rect (nil,0)  *)
(*         (fun l => Length  (fst l) (snd l)) (Length_nil ) (nil,0)  *)
(*         (refl_equal ((@nil A),0))). *)
(*     generalize (refl_equal (@nil A,0)). *)
(*     pattern (@nil A) at 1 3 4 6, 0 at 1 3 4 6, len'. *)
(*     case len'; intros; subst. *)
(*     rewrite <- eq_rect_eq_dec_set  ; auto using list_eq_dec, eq_nat_dec, eq_pair. *)
(*     discriminate. *)
 
(*     change (Length_cons a l n len ) with *)
(*       (eq_rect  *)
(*         (l,n)  *)
(*         (fun (l :list A* nat) => Length  (a::(fst l)) (S (snd l))) *)
(*         (Length_cons a l n len) (l,n) (refl_equal (l, n))). *)
(*     generalize (refl_equal (l,n)). *)
(*     Admitted. *)
(* (*     pattern  l  at 1 3 7 , len'.  , n   , *) *)
(* (*     case H0; intros; subst. *) *)
(* (*     discriminate. *) *)
(* (*     injection e3; intros; subst. *) *)
(* (*     rewrite <- eq_rect_eq_dec_set; auto. *) *)
(* (*     f_equal; auto. *) *)
(* (*   Qed. *) *)
(* (*   intros A l n. *) *)

(* (* Admitted. *) *)

(* (**Relation between Lengh and length  *) *)
(* Lemma length_Length (A:Type) (l: list A) n :length l = n  <-> Length l n . *)
(* Proof. *)
(*   split. *)
(*   intros. *)
(*   rewrite <- H.   *)
(*   apply Length_length. *)

(*   intros H. *)
(*   apply (Length_unique _ l (length l)). *)
(*   apply Length_length. *)
(*   assumption. *)
(* Qed. *)


(* Lemma Length_of_nil : forall (A:Type) (l:list A) , Length l 0 -> l =nil. *)
(* Proof. *)
(*   intros A l H. *)
(*   destruct l. *)
(*   reflexivity. *)
(*   inversion H.  *)
(* Qed.   *)

Lemma has_length_Sig_length (A:Type) n (l:{l: list A| has_length l n} ) : length (proj1_sig l ) = n.
Proof.
  (* intros A' n' l'.   *)
  destruct l as   [l l_length] . 
  Admitted.
  (* copy l_length as l_length0.
  rewrite  has_length_length in l_length0.
  simpl; rewrite l_length0. 
  reflexivity.
Qed. *)

Hint Rewrite has_length_Sig_length : length.


(* Implicit Arguments Length_length [A]. *)
(* Implicit Arguments Length_unique [A]. *)
(* Implicit Arguments Length_nil [A]. *)
Arguments has_length_Sig_length [A].

