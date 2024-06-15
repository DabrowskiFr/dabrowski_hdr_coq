Require Import Vector.
Require Import VectorTheory.
Require Import Monad.
Require Import Utf8.

Local Open Scope monad_scope.

Module PVector (Import P : Process) (Import V : Vector P).

  Module Export VT := VectorTheory P V.

  (** ** Definition of partial vectors *)

  Definition defined {A} (v : t (option A)) i := ∃ X, π i v = Some (Some X).

  Definition empty {A} (v : t (option A)) := ∀ i, i < p -> ¬ defined v i.
  
  Definition full {A} (v : t (option A)) := ∀ i, i < p -> defined v i.

  Definition partial {A} (v : t (option A)) :=
    ~ (empty v \/ full v).

  Definition compatible {A B} (v : t (option A)) (v' : t (option B)) :=
    ∀ i, i< p -> defined v i <-> defined v' i.

  Infix "⋕" := compatible (at level 28).
  
  Definition lift : ∀ (A : Type) (V : V.t A), V.t (option A) :=
    fun A (V : V.t A) => fmap (@Some A) V.
    
  Arguments lift [A].


  (** ** Selection / Merging operations *)

  Definition select {A} (p : nat -> A -> bool) (v : t (option A)) : t (option A) :=
    mapi (λ i x, x >>= (λ x, if p i x then Some x else None)) v.

  Definition oplus {A} (x y : option A) : option (option A) :=
    match (x,y) with
      (None, Some a) => Some (Some a)
    | (Some a, None) => Some (Some a)
    | (None, None) => Some (None)
    | (Some a, Some b) => None
    end.
                             
  Definition merge {A} (v1 v2 : t (option A))  : option (t (option A)) :=
    zip (@oplus A) v1 v2.
  
End PVector.
