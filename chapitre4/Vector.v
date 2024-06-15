Require Import Monad.
Require Import List.
Require Import Utf8.

Open Scope functor_scope.

Module Type Process.
  Parameter p : nat.
  Parameter p_pos : 0 < p.
End Process.

Module Type Vector (Import P : Process).

  (** * Definitions *)
  
  Parameter t : Type -> Type.

  Parameter make : ∀ (A : Type), (nat -> A) -> (t A).
  Arguments make [A] _.

  Parameter vempty : ∀ A : Type, p = 0 -> t A.
  
  Parameter π : ∀ (A : Type), nat -> (t A) -> option A.
  Arguments π [A ] _ _.

  #[export] Declare Instance v_functor : Functor t.
  
  #[export] Declare Instance v_applicative : Applicative t v_functor.
       
  Parameter erase : ∀ (A : Type), t (option A) -> option (t A).
  Arguments erase [_] _.

  (** * Properties *)
  
  Parameter π_prop : ∀ (A : Type) (v : t A) (i : nat),
      (∃ x, π i v = Some x) <-> i < p.
  
  Parameter π_fmap : ∀ (A B : Type) (f : A -> B),
    forall i v, π i (fmap f v) = pure f <*> π i v.
  
  Parameter π_make : ∀ (A : Type) (f : nat -> A),
    forall i, i < p -> π i (make f) = pure (f i).
  
  Parameter π_pure : ∀ (A : Type),
    forall i (x : A), i < p -> π i (pure x) = pure x.
  
  Parameter π_ap : ∀ (A B : Type) (v1 : t (A -> B)) (v2 : t A),
    forall i, π i (v1 <*> v2) = (π i v1) <*> (π i v2).

  Parameter erase_prop :
    ∀ A  (v : t (option A)) (v' : t A),
      erase v = pure v' <-> v = fmap pure v'.
  
  Parameter vect_eq_dec : ∀ (A : Type),
      (∀ (x y:A), x=y \/ x<>y) -> forall (v1 v2 : t A), v1=v2 \/ v1<>v2.
  
  Parameter vect_extensionality : forall (A : Type) (v v' : t A),
      (∀ i, i < p -> π i v = π i v') -> v = v'.
  
  #[export] Hint Resolve π_ap π_fmap π_make π_pure : projection.

  #[export] Hint Rewrite π_ap π_fmap π_make π_pure : projection.
  
End Vector.