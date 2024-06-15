Require Import Coq.Lists.List Lia.
Require Import Min.
Require Import sections.lifo.BoolFunctions.
Require Import sections.lifo.Misc.
Require Import sections.lifo.Length.
Require Import sections.lifo.Firstn_skipn.
Require Import sections.lifo.Nth.
Require Import sections.lifo.Tactics.

Lemma mapConstant:
  forall (A B: Type)(f:A->B)(l1 l2: list A),
    (List.length l1 = List.length l2) ->
    (forall a b, f a = f b) -> map f l1 = map f l2.
Proof.
  intros A0 B f l1; induction l1; destruct l2; intros H1 H2; 
    [ trivial |
      discriminate H1 |
      discriminate H1 |
      simpl; f_equal; [ apply H2 |
        simpl in H1; inversion H1; apply IHl1; assumption ]].
Qed.

Lemma inMapInjectiveEq: 
  forall A B (f:A->B)(l:list A), 
    (forall x y, f x = f y -> x = y) ->
    forall x, In x l <-> In (f x) (map f l).
Proof.
    induction l; intros Injective x.
      simpl; split; auto.
      simpl; split; intro H; destruct H as [H|H].
        left; rewrite H; auto.
        right; apply in_map; assumption.
        left; apply Injective; assumption.
        right; rewrite IHl; assumption.
Qed.

Lemma inMapSomeEq: 
  forall A (l:list A), 
    forall x, In x l <-> In (Some x) (map (@Some A) l).
Proof.
  intros A l x;
    apply inMapInjectiveEq;
      intros; injection H; intros; auto.
Qed.

(** A proof irrelevant version of [map_ext] *) 

Lemma mapProj1SigExt : 
  forall (A B:Type)(P1 P2 : A->Prop) (l1 : list (sig P1))(l2 : list (sig P2))
    (f1:sig P1 ->B)(f2:sig P2 ->B),
    (forall x1 x2, proj1_sig x1 = proj1_sig x2 -> f1 x1 = f2 x2)->
    listProj l1 = listProj l2 ->
    map f1 l1 = map f2 l2.
Proof.
  intros A B P1 P2 l1 l2 f1 f2 H H0.
  generalize dependent l2.
  induction l1 ; intros l2 H0; destruct l2 ; auto ; try(discriminate).
  inversion H0.
  simpl. rewrite H with (x1:=a)(x2:=s).
  rewrite IHl1 with (l2:=l2). 
  reflexivity.
  assumption.
  assumption.
Qed.

(** [map] applied to an injective  function is injective *)

Lemma mapInjectiveEq: 
  forall A B (l1 l2:list A) (f:A->B), 
    (forall x y, f x = f y -> x = y) ->
    map f l1 = map f l2 -> 
    l1 = l2.
Proof.
  intros A B l1.
  induction l1; 
    intros l2 f Injective MapEq; 
      destruct l2; auto ; try(discriminate MapEq).
  inversion MapEq as [H0] ; apply Injective in H0; rewrite H0 ; rewrite (IHl1 l2 f); auto.
Qed.


(** ** Tools for insert/remove [map] *)
Section map_inversion.
  
  Variables A B: Type.

(** [fold_left] to [map] *)
  Lemma fold_left_f_inv: 
    forall (f:A->B) (g:B->B->B) (l:list A) (i:B),
    fold_left (fun acc x => g acc (f x)) l i = fold_left (fun acc y => g acc y) (map f l) i.
  Proof.
    induction l. reflexivity.
    simpl.
    intro. apply IHl.
  Qed.


(** [fold_right] to [map] *)
  Lemma fold_right_f_inv:
    forall (f:A->B) (g:B->B->B) (l:list A) (i:B),
    fold_right (fun x acc => g (f x) acc) i l = fold_right (fun y acc => g y acc) i (map f l).
  Proof.
    induction l. reflexivity.
    simpl.
    intro. rewrite IHl.
    reflexivity.
  Qed.

(** [map] with function extensional  egality, WARNING a more general version exists in [inits]. WARNING ABOUT THE WARNING: no in [Init_tails], this version is now called. *)
  Lemma map_assumption: 
    forall (l:list A) (f g:A->B),
    (forall x, In x l -> f x = g x) -> map f l = map g l.
  Proof.
    intros.
    induction l. intros. reflexivity.
    simpl.
    f_equal. apply H. simpl. left. reflexivity.
    apply IHl.
    intros. apply H. simpl. right. assumption.
  Qed.

  Lemma map_eq_nth: 
    forall (l l':list A) (f g:A->B) (H : length l = length l'),
    ( forall n  (H1 : n < length l) (H1' : n < length l') , f (nth' n l H1) = g (nth' n l' H1')) -> 
    map f l = map g l'.
  Proof.
    intros.
    pose (n:=length l); assert (H' :  n = length l) by reflexivity; revert H' ; generalize n; clear n; intros. revert dependent l; revert l' .      
    induction n.
    intros l' l H H0 H'.    symmetry in H'.
    rewrite H' in *.
    rewrite (lengthNil  _ H').
    symmetry in H.
    rewrite (lengthNil  _ H).
    reflexivity.
    intros l' l H H0 H'.    
    admit.
    Admitted.
     (* lengthPos H'.
    simpl in H.
    lengthPos H.
    simpl.
    f_equal. 
    assert (len_ok : 0  < length (a :: l'0)) by (simpl ; auto with arith).
    assert (len_ok' : 0  < length (a0 :: l'1)) by (simpl ; auto with arith).
    generalize (H0 0 len_ok len_ok'). unfold nth'. simpl. auto.
    apply IHn.
    simpl in H; auto with arith.
    intros n0 H1 H1'.
    assert (Sn0_ok: (S n0) <  length (a :: l'0)) by (simpl; lia).
    assert (Sn0_ok' : (S n0) <  length (a0 :: l'1)) by (simpl; lia).
    generalize (H0 (S n0) Sn0_ok Sn0_ok').
    unfold nth' at 1. unfold nth' at 1.  simpl.
    rewrite (nth'_nth _  _ a).
    rewrite (nth'_nth _  _ a0).
    auto.
    simpl in H'; auto with arith.
  Qed. *)

  Lemma fold_left_map_app: 
    forall (f:A->B) (l:list (list A)) (i: list A),
    map f (fold_left (fun x y =>   x++y ) l i) 
    = fold_left (fun x y => x++y) (map(map f) l) (map f i).
  Proof.
    intros f l. 
    induction l. simpl. reflexivity.
       simpl. intros i; rewrite IHl. rewrite map_app. reflexivity.
Qed.
(** [map] and [firstn] composition *)
  Lemma map_firstn: forall (f:A->B) (n:nat) (l:list A),
    map f (firstn n l) = firstn n (map f l).
  Proof.
    induction n. intro. simpl. reflexivity.
    intro. destruct l.
    simpl. reflexivity.
    simpl. f_equal. apply IHn.
  Qed.

(** [map] and [skipn] composition *)
  Lemma map_skipn: forall (f:A->B) (n:nat) (l:list A),
    map f (skipn n l) = skipn n (map f l).
  Proof.
    induction n. intro. simpl. reflexivity.
    intro. destruct l.
    simpl. reflexivity.
    simpl. f_equal. apply IHn.
  Qed.

(** [map] of identity is identity*)
Lemma  mapIdentity : forall (A:Type) (l:list A), map (fun z=>z) l =l.
  Proof.
    intros A0 l.
    induction l.
    unfold map ;simpl. reflexivity.
    simpl. rewrite IHl; reflexivity.
  Qed.
  Arguments mapIdentity [A].

Ltac mapId :=
  match goal with 
    [|-context [map (fun z =>z) ?l]
    ]
    =>
    rewrite (mapIdentity l)
  end.


  (** Simplification of [List.map_nth] where [n] is in the list [l] *)
  Lemma map_nth' : forall (f:A->B) l d d' n,
    n<length l-> nth n (map f l) d = f (nth n l d').
  Proof.
    induction l as  [|  a l IHl].
    simpl; intros d d' n H.
    contradict H;lia.
    intros d d' n H.
    simpl in  *. generalize H;clear H.
    induction n as [|n IHn].
    intro; reflexivity.
    intro. 
    apply (IHl d d' (n) ). lia.
  Qed.

  (** [fst] [map]ed on all element of a [combine] give the first list if it is the smallest of the two combined lists    *)
Lemma map_fst_combine : forall L1 L2, forall (l1 : list L1) (l2 : list L2), length l1<= length l2 -> map (@fst L1 L2)  (combine l1 l2) = l1.
Proof.
induction l1.
simpl. reflexivity.
intros; simpl.
destruct l2. contradict H. simpl. auto with arith. simpl. rewrite IHl1. reflexivity.
simpl in H. lia.
Qed.

  (** [snd] [map]ed on all element of a [combine] give the second list if  the two combined lists have the same size    *)
Lemma map_snd_combine : forall L1 L2, forall (l1 : list L1) (l2 : list L2), length l1 = length l2 -> map (@snd L1 L2)  (combine l1 l2) = l2.
Proof.
induction l1.
simpl. 
intros l2 H. symmetry in H.  symmetry. apply (lengthNil _ H).
intros; simpl.
destruct l2. contradict H. simpl. auto with arith. 
simpl. rewrite IHl1. reflexivity.
simpl in H. lia.
Qed.

Lemma mapNil : forall (A B : Type) l (f : A -> B), nil = map f l -> l = nil.
Proof.
destruct l.
 trivial.
 intros f H. inversion H.
Qed.


End map_inversion.
  
Lemma map_inversion :
    forall A B (l:list A) (f f' : A -> B), 
      map f l = map f' l -> 
      forall a, In a l ->
        f a = f' a.
  Proof.  
    intros A0 B l f f' H a H0.
    destruct (inLtLengthNth _ _ H0).
    destruct H1.
    rewrite <-  (H2  a).
    rewrite <- map_nth.
    rewrite <- (map_nth f') .
    rewrite H.
    assert (H' : x < length  (map f' l)) by (autorewrite with length; auto).
    rewrite (nth_indep (map f' l)   (f a) (f' a) H').
    reflexivity.
  Qed.
  Arguments map_inversion [A B l f f'].



Lemma last_map: forall (A B :Type) (a:A) (b:B) (l:list A) (f:A->B), 
  last (map f l) b = 
  if (isNil l) then b else f (last l a).
Proof.
  induction l.
  simpl.
  auto.
  simpl.
  intros f.
  rewrite IHl.
  destruct l; 
    auto.
Qed.

Fixpoint rev_map' A B (f: A -> B) l accu :=
  match l with
    nil => accu
    | h::t => rev_map' A B f t ((f h)::accu)
  end.

Definition rev_map A B f l := rev' (rev_map' A B f l nil).

Lemma combine_map : forall A B C D  l l' (f: A -> C) (f' : B -> D),
  map (fun (x: A*B) => let (a,b):=x in (f a,f' b))  (combine l l')  
  = combine (map f l) (map f' l').
Proof.
  intros A B C D l.
  induction l.
      reflexivity.
  
      simpl.
      destruct l'.
          reflexivity.
          
          intros f f'.
          simpl.
          rewrite IHl.
          reflexivity.
 Qed.      


Arguments map_nth' [A B].
Arguments map_firstn [A B].
Arguments map_skipn [A B].
Arguments fold_left_f_inv [A B].
Arguments rev_map [A B].
Arguments combine_map [A B C D].

Set Implicit Arguments.

(** Simplification of [List.map_nth] where [n] is in the list [l] *)
Lemma nthMapLt: forall (A B: Type) (f:A->B) l d d' n,
  n<length l-> nth n (map f l) d = f (nth n l d').
Proof.
  induction l as  [|  a l IHl].
  simpl; intros d d' n H.
  contradict H;lia.
  intros d d' n H.
  simpl in  *. generalize H;clear H.
  induction n as [|n IHn].
  intro; reflexivity.
  intro. 
  apply (IHl d d' (n) ). lia.
Qed.


Lemma seqMapConstant:
  forall{A:Type}(l a b:nat)(f:nat -> A),
    (forall(n1 n2 :nat), f n1 = f n2) ->
    map f (List.seq a l) = map f (List.seq b l).
Proof.
  induction l.
  - trivial.
  - simpl. intros a b f H.
    f_equal.
    + apply H.
    + now apply IHl.
Qed.
