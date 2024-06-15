Require Import String.

Inductive result (A: Type) : Type :=
| Ok: A -> result A 
| Error: String.string -> result A.

Arguments Ok [A] _.
Arguments Error [A] _.

Definition bind {A B: Type} (f: result A) (g: A->result B)
: result B :=
  match f with
    | Ok x => g x
    | Error msg => Error msg
  end.
  
Notation "'do' X <- A ; B" := (bind A (fun X => B)) 
                                (at level 200, X ident, A at level 100, B at level 200).

Definition lift {A B : Type} (f: A -> B) (x : result A) : result B := 
  match x with 
    | Ok x => Ok(f x) 
    | Error msg => Error msg
  end.



  
