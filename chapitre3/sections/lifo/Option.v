Require Import List.
Require Import Program.
Require Import sections.lifo.AlgebraClasses.
Require Import sections.lifo.AlgebraInstances.
Require Import Coq.Relations.Relation_Definitions.
Set Implicit Arguments.

(** Removing the Some constructor  *)

(** using default value  *)
Definition no_some_default  (A:Type) (a: option A) (d: A) :=
  match a with 
    None => d
    | Some a => a
  end.


(** using proof that it is different from None  *)
Program Definition 
  noSome(A:Type)(a:option A| a <> None) : { x:A | Some x = a } := 
  match a with 
    | None => _ 
    | Some x => x
  end.


Lemma someNoSomeId: 
  forall(A:Type)(a:option A)(H:a<>None),
    Some(proj1_sig(noSome(exist _ a H))) = a.
Proof.
  intros A a Ha;
    destruct a; simpl; auto; elim Ha; auto.
Qed.

Lemma someInjectiveEq: 
  forall(A:Type)(x y:A), 
    x = y <-> Some x = Some y.
Proof.
  intros A x y; split;intro H; [
    f_equal | inversion H ]; auto.
Qed.

Hint Rewrite someNoSomeId: option.


Definition isSome (A:Type)(x:option A) : bool := 
  match x with 
    | None => false 
    | Some _ => true
  end.

Lemma isSomeTrueNotNone:
  forall (A:Type)(x: option A), 
    isSome x = true -> x<>None.
Proof.
  destruct x; intro H; discriminate.
Qed.

Fixpoint mapFilterSome (A B :Type)(f: A->option B)(l:list A) := 
  match l with
    | nil => nil
    | cons h t => 
      match (f h) with 
	| Some x => x::mapFilterSome f t
        | None => mapFilterSome f t
      end
  end.

Lemma mapFilterSomeProp: 
  forall (A B :Type)(f: A->option B)(l:list A),
    map Some (mapFilterSome f l) = filter (@isSome B) (map f l).
Proof.
  induction l.
  auto.
  case_eq (f a);
    try(intros b Hfa);(try intros Hfa); simpl; rewrite Hfa; simpl; f_equal; assumption.
Qed.

Lemma mapFilterSome_ext :
  forall A B l (f f' : A -> option B), 
    (forall a:A, f a = f' a) ->
    mapFilterSome f l =  mapFilterSome f' l.
Proof.
  intros A0 B l f f'  H.
  induction l.
  reflexivity.        
  simpl.
  rewrite H.
  rewrite IHl.
  reflexivity.
Qed.
Arguments mapFilterSome_ext [A B].

(** ** Combining option  *)

Definition right_option A  (a: option A) (b:option A) := match b with None => a | Some  _ =>  b end.

Global Instance right_option_assoc A : Associative (@right_option A).
Proof.
  constructor. intros x y z.
  destruct x; destruct y; destruct z; reflexivity.
Qed.

Global Instance right_option_neutral A : Neutral (@right_option A) (@None A).
Proof.
  firstorder.
  destruct a; reflexivity.
Qed.


Definition left_option A  (a: option A) (b:option A) := match a with None => b | Some  _ =>  a end.

Global Instance left_option_assoc A : Associative (@left_option A).
Proof.
  constructor. intros x y z.
  destruct x; destruct y; destruct z; reflexivity.
Qed.

Global Instance left_option_neutral A : Neutral (@left_option A) (@None A).
Proof.
  firstorder.
  destruct a; reflexivity.
Qed.

Definition optionify (A B:Type) (op : A -> A ->B) := 
fun a b => 
  match a with
    None => None 
    | Some a' => match b with 
                   None => None
                   | Some b' => Some (op a' b') 
                 end
  end.

Definition optionify_default (A B:Type) (op : A -> A ->B) (d:A) := 
fun a b => 
  match a with
    None => match b with 
                   None => None
                   | Some b' => Some (op d b') 
                 end
    | Some a' => match b with 
                   None => Some (op a' d)
                   | Some b' => Some (op a' b') 
                 end
  end. 

Definition optionify' (A:Type) (op : A -> A -> A) := 
fun a b => 
  match a with
    None => b
    | Some a' => match b with 
                   None => a
                   | Some b' => Some (op a' b') 
                 end
  end.

Definition optionify'_default (A:Type) (op : A -> A -> A) (d:A) := 
fun a b => 
  match a with
    None => match b with 
              None => d
              | Some b' => b'
            end
    | Some a' => match b with 
                   None => a'
                   | Some b' => op a' b'
                 end
  end.
(*  *)


Definition option_eq A R `{Equivalence A R}  : relation (option A):=
  fun  a b => 
    match a,b with
        Some a, Some b => R a b
      | None, None => True
      | _,_ => False
    end.

Global Instance option_equiv  A {R} `{Equivalence A R}  : Equivalence (@option_eq A R _).
Proof.
  constructor;unfold option_eq.
  - unfold Reflexive. 
    intros x. destruct x; [reflexivity|auto].
  - unfold Symmetric. 
    intros x y H0.
    destruct x,y;try reflexivity ; try (symmetry; auto); auto.
  - unfold Transitive.
    intros x y z H0 H1.
    destruct x,y,z;auto.
    + rewrite H0; auto.
    + elim H0.
Qed.


Global Instance  optionify'_assoc A (f :A->A->A) 
          {R} 
          {eqR : Equivalence R}
          {assoc_f :AlgebraClasses.Associative (equ:=eqR) f} :
  AlgebraClasses.Associative   (optionify' f).
Proof.
  constructor.
  intros x y z.
  unfold optionify'.
  destruct x; destruct y; destruct z;
  unfold option_eq;
  repeat rewrite AlgebraClasses.associative; try reflexivity.
Qed.

  Lemma optionify'_some1  :
    forall A f (e : option A) i, 
      optionify' f e (Some i) <> None.
  Proof.
  Admitted.
    (* destruct e; firstorder.
  Qed. *)

  Lemma optionify'_some2  :
    forall A f (e : option A) i, 
      optionify' f (Some i)  e <> None.
  Proof.
  Admitted.
    (* destruct e; firstorder.
  Qed. *)

  Import Morphisms.

  
  Definition optionify_f_proper A Ra {Ra_eq : Equivalence Ra}
             (f : A -> A -> A)  
             (f_proper : Morphisms.Proper (Ra ==> Ra  ==> Ra) f)
  : 
    Proper 
      (@option_eq _ _ Ra_eq ==> 
       @option_eq _ _ Ra_eq ==> 
       @option_eq _ _ Ra_eq) 
      (@optionify' _ f).
    unfold Proper, respectful.
    intros x y H x0 y0 H0.
    case_eq x; case_eq y;case_eq x0; case_eq y0; intros;
    try rewrite H1, H2,H3,H4 in *;
    try  (simpl in *; try rewrite H;try rewrite H0; reflexivity);
    try simpl in *; contradiction.
  Qed.


Global Instance right_option_assoc_option_eq A : Associative (@right_option A).
Proof.
  constructor. intros x y z.
  destruct x; destruct y; destruct z; reflexivity.
Qed.

Global Instance right_option_neutral_option_eq A : Neutral (@right_option A) (@None A).
Proof.
  firstorder;
  destruct a; reflexivity.
Qed.

 
Global Instance left_option_assoc_option_eq A : Associative (@left_option A).
Proof.
  constructor. intros x y z.
  destruct x; destruct y; destruct z; reflexivity.
Qed.

Global Instance left_option_neutral_option_eq A : Neutral (@left_option A) (@None A).
Proof.
  firstorder;
  destruct a; reflexivity.
Qed.
