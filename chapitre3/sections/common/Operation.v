Require Import List ZArith String Bool.
Require Import sections.lifo.Prelude Error Value.

Import ListNotations.

Module Signature.

  Module Type T
         (Import Ad : DecidableInfiniteSet)
         (Import Ty : Type_.TYPE Ad).
    
    (** Domain of a predefined operation *)
    Inductive domain : Set := 
    | Total: forall(t:Ty.t), domain
    | Partial : forall(t:Ty.t), domain.
    
    (** Signature of a predefined operation *)
    Definition t := list Ty.t * domain.
    
    Fixpoint typeOfArgsReturn
             (argumentTypes: list Ty.t)(returnType: domain) : Type := 
      match (argumentTypes, returnType) with 
        | ([], Total t) => typeOfType t
        | ([], Partial t) => result (typeOfType t)
        | (t1::ts, _) => typeOfType t1 -> typeOfArgsReturn ts returnType
      end.
    
    Definition typeOf (s : t) := 
      typeOfArgsReturn (fst s) (snd s).
    
  End T.

End Signature.

Module Type T
       (Import Ad: DecidableInfiniteSet)
       (Import Ty : Type_.TYPE Ad)
       (Import Signature : Signature.T Ad Ty).

  Parameter operation : Set.

  Parameter eq_dec : forall (o o' : operation), { o = o' } + { ~ o = o'}.

  Parameter opSignature : operation -> Signature.t.

  Parameter state : Type.

  Parameter opDenote: state -> forall (op:operation),  Signature.typeOf(opSignature op).

End T.

Module Type Simple 
       (Import Ad : DecidableInfiniteSet)
       (Import Ty : Type_.TYPE Ad)
       (Import Signature : Signature.T Ad Ty) 
  <: T Ad Ty Signature.
  
  (**  Predefined operations *)

  Inductive _operation_ : Set := 
  | NumberC : Z -> _operation_
  | BoolC : bool -> _operation_
  | Null 
  | Plus | Times | Minus | Mod | Div
  | Not | And | Or 
  | LowerThan | GreaterThan
  | Equal: forall (t:Ty.t), _operation_.

  Definition operation := _operation_.

  Lemma eq_dec:  forall (o o' : operation), { o = o' } + { ~ o = o'}.
  Proof. 
    repeat decide equality. 
  Qed.
  
  (** Signatures of operations *)
  Definition opSignature (op: operation) : Signature.t :=
    match op with 
      | NumberC _ => ([],Total Number)
      | BoolC _ => ([],Total Boolean)
      | Null => ([],Total Location)
      | Plus | Times | Minus => 
                         ( [ Number; Number ] , Total Number )
      | Div | Mod => 
                ( [ Number; Number ] , Partial Number )
      | Or | And => 
               ( [ Boolean; Boolean ], Total Boolean )
      | Not => 
          ( [ Boolean ], Total Boolean )
      | LowerThan | GreaterThan =>
                      ( [ Number; Number ], Total Boolean )
      | Equal t => 
          ( [ t; t], Total Boolean )
    end.

  Open Scope string_scope.

  Definition state := unit.

  Definition null : Ad.t := (snd(proj1_sig Ad.infinite)) 0.

  (**  translate an operation into its equivalent in coq *)
  Definition opDenote (st:state) (op:operation) : Signature.typeOf(opSignature op) := 
    match op return (Signature.typeOf (opSignature op)) with
      | NumberC n => n
      | BoolC b => b
      | Null => null
      | Plus => Zplus
      | Minus => Zminus
      | Times => Zmult
      | Mod => fun n1 n2 => 
                 match n2 with 
                   | Z0 => Error "Mod: division by 0"
                   (*| S n => Ok (proj1_sig (modulo (S n) (gt_Sn_O n) n1))*)
                   (*| _ => (Ok Coq.ZArith.BinIntDef.Z.modulo n1 n2)*)
                   | _ => Ok (Coq.ZArith.BinIntDef.Z.modulo n1 n2)
                 end
      | Div => fun n1 n2 => 
                 match n2 with 
                   | Z0 => Error "Div: division by 0"
                   (*| S n => Ok (proj1_sig (quotient (S n) (gt_Sn_O n) n1))*)
                   | _ => Ok (Coq.ZArith.BinIntDef.Z.modulo n1 n2)
                 end
      | Or => orb
      | And => andb
      | Not => negb
      | Equal Thread => Nat.eqb
      | Equal Number => fun x y => proj1_sig (Z_eq_bool x y)
      | Equal Boolean => eqb
      | Equal _Allocation => fun x y => if Ad.eq_dec x y then true else false
      | LowerThan => Zlt_bool
      | GreaterThan => Zgt_bool
  end.

  Close Scope string_scope.

End Simple.