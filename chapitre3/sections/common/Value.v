Require Import ZArith.
Require Import Bool.
Require Import Coq.ZArith.BinInt.
Require Import sections.lifo.Prelude.
Require Import Type_.
Require Import Logic.Eqdep_dec.

Module Type TYPE ( Import Address: DecidableInfiniteSet) 
                 ( Import T : Type_.TYPE ( Address ) ).

  Inductive t :=
  | Value : forall(ty:T.t)(v:T.typeOfType ty), t.
    
  Definition typeOfValue (v : t) : T.t := 
    match v with 
      | Value t _ => t
    end.

  Definition valueOfValue (v : t) : T.typeOfType(typeOfValue v) := 
    match v with 
      | Value _ v => v
    end.

  Module EqDepDec := DecidableEqDepSet T.

  Lemma ValueInj:
    forall (ty: T.t)(v1 v2 : T.typeOfType ty),
      Value ty v1 = Value ty v2 ->
      v1 = v2.
  Proof.
    intros ty v1 v2 H;  apply EqDepDec.inj_pair2; injection H; trivial.
  Qed.
 
  Lemma eq_dec : forall (e e' : t), {e = e'}+{e <> e'}.
  Proof.
    destruct e; destruct e'; destruct ty; destruct ty0; simpl in *; 
                try (right; intro; discriminate).
    case_eq(Peano_dec.eq_nat_dec v v0); intros eq H; [ 
    left; auto |
    right; intro H'; apply ValueInj in H'; intuition ].
    Admitted.
    (* case_eq(Z_eq_dec v v0); intros eq H; [ 
    left; rewrite eq; auto |
    right; intro H'; apply ValueInj in H'; intuition ].
    case_eq(Bool.bool_dec v v0); intros eq H; [ 
    left; rewrite eq; auto |
    right; intro H'; apply ValueInj in H'; intuition ].
    case_eq(Address.eq_dec v v0); intros eq H; [ 
    left; rewrite eq; auto |
    right; intro H'; apply ValueInj in H'; intuition ].
  Qed. *)
    
  Definition intToValue (n : Z) : t := Value T.Number n.
  Definition boolToValue (b : bool) : t := Value T.Boolean b.

  Coercion intToValue: Z >-> t.
  Coercion boolToValue: bool >-> t.

  Definition getLocation (v : t) : option Address.t := 
    match v with 
      | Value Location a => Some a 
      | _ => None
    end.

  Definition getNumber (v : t) : option Z := 
    match v with 
      | Value Number n => Some n 
      | _ => None
    end.

  Definition getThreadId (v : t) : option nat := 
    match v with 
      | Value Thread t => Some t
      | _ => None
    end.

  Definition getBoolean (v : t) : option bool := 
    match v with 
      | Value Boolean b => Some b
      | _ => None
    end.

End TYPE.

Module Make  ( Address: DecidableInfiniteSet) ( T : Type_.TYPE Address ).
  
  Include TYPE Address T.

End Make.