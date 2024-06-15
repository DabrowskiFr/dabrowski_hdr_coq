Require Import Coq.ZArith.BinInt.
Require Import sections.lifo.Prelude.

(** ** Types *)

Module Type TYPE ( Import Address: DecidableInfiniteSet ).

  Inductive t := 
  | Thread
  | Number
  | Boolean
  | Location.

  Definition U := t.

  Lemma eq_dec : forall (e e' : t), {e = e'}+{e <> e'}.
  Proof.
    decide equality.
  Qed.

  Definition typeEq (t1 t2: t) : bool := 
    match t1, t2 with 
      | Thread, Thread | Number, Number | Boolean, Boolean | Location, Location => true
      | _, _ => false
    end.
  
  Lemma typeEqEq:
    forall (t1 t2: t),
      typeEq t1 t2 = true -> t1 = t2.
  Proof.
    intros t1 t2; destruct t1; destruct t2; 
    intro H; intuition; inversion H.
  Defined.
  
  Open Scope type_scope.
  
  (** *** Translate type into coq type *)
  Definition typeOfType (t : t) : Set :=
    match t with
      | Thread => nat 
      | Number => Z 
      | Boolean => bool
      | Location => Address.t 
    end.
  
End TYPE.

Module Make ( Address: DecidableInfiniteSet ).

  Include TYPE ( Address ).

End Make.