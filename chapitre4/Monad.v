Require Import Utf8.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import List.
Require Import Morphisms.
Require Import Prelude.

Open Scope program_scope.

Notation "$" := (fun x y => y x) (at level 29).

(** * Monoid *)

Class Monoid (A : Type) :=
  {
    mempty : A;
    mappend : A -> A -> A;
    
    monoid_left_id  : forall a, mappend mempty a = a;
    monoid_right_id : forall a, mappend a mempty = a;
    monoid_assoc    : forall a b c, mappend a (mappend b c) = mappend (mappend a b) c
  }.

(* Class CommutativeMonoid (A : Type) (E : Monoid A) :=
  {
    monoid_commute : ∀ a b, mappend a b = mappend b a
  }. *)

(** * Functor *)

Class Functor (f : Type -> Type) : Type :=
  {
    fmap : forall {a b : Type}, (a -> b) -> f a -> f b;
    fmap_id   : forall a : Type, fmap (@id a) = id;
    fmap_comp : forall (a b c : Type) (f : b -> c) (g : a -> b),
        (fmap f ∘ fmap g) = fmap (f ∘ g)
  }.
  
(*
  Definition pointwise_relation (R : relation B) : relation (A -> B) :=
    fun f g => forall a, R (f a) (g a).
*)
(** * Applicative *)

Class Applicative (f : Type -> Type) `(E : Functor f)  : Type :=
  {
    pure : ∀ {a : Type}, a -> f a;
    ap : ∀ {a b : Type}, f (a -> b) -> f a -> f b;
    applicative_id : ∀ {a : Type} (x : f a), ap (pure id) x = x;
    applicative_comp : ∀ {a b c : Type} (u : f (b -> c)) (v : f (a -> b)) (w : f a) ,
        ap (ap (ap (pure compose) u) v) w = ap u (ap v w);
    applicative_homomorphism :
      ∀ {a b : Type} (f : a -> b) (x : a), ap (pure f) (pure x) = pure (f x);
    applicative_interchange :
      ∀ {a b : Type} (u : f ( a -> b)) ( y : a), ap u (pure y) = ap (pure ($ y)) u;
    applicative_fmap : ∀ {A B : Type} (f : A -> B), fmap f  = ap (pure f)
    
  }.

Inductive Endo_ a := Endo {appEndo : a -> a}.

Inductive Dual_ a := Dual { getDual : a }.

(** * Foldable *)

(* #[export] Instance monoid_dual (A : Type) (E : Monoid A) : Monoid (Dual_ A) :=
  {
    mempty := Dual A mempty;
    mappend x y := match (x,y) with (Dual _ x, Dual _ y) => Dual A (mappend x y) end
  }.
Admitted.

#[export] Instance monoid_endo (A : Type) : Monoid (Endo_ A) :=
  {
    mempty := Endo _ id;
    mappend x y := match (x,y) with (Endo _ f, Endo _ g) => Endo _ (f ∘ g) end
  }.
Admitted. *)

(* Class Foldable (f : Type -> Type) : Type :=
  {
    foldr : ∀ (A B : Type), (A -> B -> B) -> B -> f A -> B;
    foldMap : ∀ (A B : Type) `(E : Monoid B), (A -> B) -> f A -> B :=
      fun _ _ _ f v => foldr _ _ (fun x y => mappend (f x) y) mempty v;
    fold_ : ∀ (A : Type) `(E : Monoid A), f A -> A :=
      fun A _ => foldMap A A _ (fun (x : A) => x);
    foldl : ∀ (A B : Type), (B -> A -> B) -> B -> f A -> B :=
      fun A B f z t => appEndo _ (getDual _ (foldMap _ _ _ (Dual _ ∘ Endo _ ∘ flip f) t)) z;
    to_list : ∀ (A : Type), f A -> list A :=
      fun A v => foldr _ _ (fun x l => List.cons x l) (@List.nil A) v;
    null : ∀ (A : Type), f A -> bool := fun _ v => foldr _ _ (fun _ _ => false) true v;
    length : ∀ (A : Type), f A -> nat := fun A v => foldl _ _ (fun c _ => c+1) 0 v;
  }.

Arguments foldr [f Foldable A B] _ _ _.
Arguments foldMap [f Foldable A B E] _ _.
Arguments fold_ [f Foldable A E] _.
Arguments foldl [f Foldable A B] _ _ _.
Arguments to_list [f Foldable A] _.
Arguments null [f Foldable A] _.
Arguments length [f Foldable A] _. *)

(** * Traversable *)
(* Class Traversable (f : Type -> Type) `(E : Functor f) `(F : Foldable f) : Type :=
  {
    traverse : ∀ (A B : Type) (g : Type -> Type) `(E : Applicative g), (A -> g B) -> f A -> g (f B);
    sequenceA : ∀ (A : Type) (g : Type -> Type) `(E : Applicative g), f (g A) -> g (f A)
  }. *)

(** * Monad *)
Class Monad (f : Type -> Type) `(E : Applicative f)  : Type :=
  {
    bind : ∀ {a b : Type}, f a -> (a -> f b) -> f b 
  }.

Arguments fmap {f _ a b} g x.

Definition liftA (f : Type -> Type) `{E : Applicative f} (A B : Type) (g : A -> B) (a : f A) :=
  @ap f _ _ _ _ (pure g) a.

Definition liftA2 (f : Type -> Type) `{E : Applicative f} (A B C : Type) (g : A -> B -> C)
           (a : f A) (b : f B) : f C :=
  @ap f _ _ _ _ (fmap g a) b.


Infix "<$>" := fmap (at level 28, left associativity, only parsing) : functor_scope.

Infix "<&>" := (flip fmap) (at level 28, left associativity, only parsing) : functor_scope.

Infix "<$" := (fmap ∘ const) (at level 28) : functor_scope.

Infix "($>)" := (flip (fmap ∘ const)) (at level 28) : functor_scope.

Infix "<*>" := ap (at level 28) : functor_scope.

Infix ">>=" := bind (at level 28) : monad_scope.

Infix ">>" := (fun m k => bind m (fun x => k)) (at level 28) : monad_scope. 

Notation "'do' X <- A ; B" := (bind A (fun X => B))
                               (at level 200, X ident, A at level 100, B at level 200).

Notation "'return'" := pure : monad_scope.


#[export, refine]  Instance monoid_option (A : Type) {E : Monoid A} : Monoid (option A) :=
  {
    mempty := Some mempty;
    mappend (v1 v2 : option A) :=
      match (v1, v2) with
        (Some x, Some y) => Some (mappend x y)
      | _ => @None A
      end
  }.
  Proof.
  - destruct a; simpl.
    rewrite monoid_left_id. 
    reflexivity.
    reflexivity.
  - destruct a; simpl.
    rewrite monoid_right_id. 
    reflexivity.
    reflexivity.
  - intros a b c;
    destruct a, b, c; simpl; try reflexivity.
    rewrite monoid_assoc; reflexivity.
  Defined.

Definition option_map (A B : Type) (f : A -> B) (v : option A) : option B :=
  match v with
    None => None
  | Some x => Some (f x)
  end.
             
#[export] Instance functor_option : Functor option.
Proof.
  constructor 1 with (option_map).
- intros a.
  apply functional_extensionality.
  destruct x; reflexivity.
- intros a b c f g.
  apply functional_extensionality.
  intros x.
  unfold compose.
  destruct x; reflexivity.
Defined.

#[export, refine] Instance applicative_option : Applicative option functor_option :=
  {
    pure _  := Some ;
    ap _ _ fo xo :=
      match (fo, xo) with
        (Some f, Some x) => Some (f x)
      | _ => None
      end
  }.
  Proof.
- destruct x; reflexivity.
- intros a b c u v w.
  destruct u, v, w; try reflexivity.
- reflexivity.
- destruct u; reflexivity.
- reflexivity.
Defined.

(* #[export] Instance foldable_option : Foldable option :=
  {
    foldr A B (f : A -> B -> B) (z : B) (o : option A) :=
      match o with
        None => z
      | Some x => f x z 
      end
  }. *)

(* Lemma foldable_fold : ∀ A B (E : Monoid B) (g : A -> B) (x : option A),
    @foldMap option foldable_option A B E g x = (@fold_ option foldable_option B E ∘ fmap g) x.
Proof.
  intros A B E g x.
  unfold fold_, foldMap.
  unfold compose.
  destruct x; simpl.
  - reflexivity.
  - reflexivity.
Qed. *)

(* Lemma foldable_foldmap : ∀ (A B C : Type) f (E : Monoid C) (F : Functor f) (F : Foldable f)
                           (g : B -> C) (h : A -> B),
    (@foldMap option foldable_option B C E g) ∘ (fmap h) = @foldMap option foldable_option A C E (g ∘ h).
Proof.
  intros A B C f E F F0 g h.
  unfold foldMap.
  unfold compose.
  simpl.
  apply functional_extensionality.
  intros x.
  destruct x; reflexivity.
Qed. *)

#[export] Instance monad_option : Monad option applicative_option :=
  {
    bind _ _ x f :=
      match x with
        Some x => f x
      | None => None
      end
  }.

#[export] Instance fmap_pointwise_Proper (f : Type -> Type) (E : Functor f) (A B : Type):
  Proper (@pointwise_relation A B eq  ==> eq) fmap.
Proof.
  intros x y H__pointwise.
  f_equal.
  apply functional_extensionality.
  apply H__pointwise.
Qed.

Lemma fmap_some :
    ∀ (A   B : Type) (o : option A) (x : B) (f : A -> B) (H : fmap f o = Some x), ∃ a, o = Some a /\ x = f a.
  Proof.
    intros A B o x f H.
    destruct o; simpl in H; [inj H; eauto | discriminate].
  Qed.
