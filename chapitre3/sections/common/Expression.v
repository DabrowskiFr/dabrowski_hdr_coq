Require Import String List Arith Bool FMapList Structures.OrderedTypeEx Zdiv Zbool.
Import ListNotations.

Require Import sections.lifo.InSig sections.lifo.Length.

Require Import sections.lifo.Prelude Type_ Value Error Operation Store.

Open Scope type_scope.
Open Scope string_scope.
  
Module Type TYPE 
       (Import Ad : DecidableInfiniteSet)
       (Import Ty : Type_.TYPE Ad)
       (Import Va : Value.TYPE Ad Ty)
       (Import Si : Operation.Signature.T Ad Ty)
       (Import Op : Operation.T Ad Ty Si)
       (S0 : Store.T Natural Ad Ty Va)
       (Import St : Store.P Natural Ad Ty Va S0).

  Definition conversionT1T2 {t1 t2:Ty.t}{ts: list Ty.t}{d: domain}
                            (f: Si.typeOf(t1::ts,d))
                            (H: t1 = t2 ) : Si.typeOf(t2::ts,d).
  Proof.
    rewrite <- H.
    exact f.
  Defined.

  Definition conversionNIL {d: domain}(f: Si.typeOf([],d)) : 
    match d with 
      | Total r => typeOfType r 
      | Partial r => result(typeOfType r)
    end.
  Proof.
    destruct d; compute in *; exact f.
  Defined.
  
  Program Definition opApplyOneArgument {ty: Ty.t}{ts:list Ty.t}{d:domain}
                                        (f: Si.typeOf( (List.cons ty ts) , d ) )
                                        (arg: result Va.t) 
            : result(Si.typeOf(ts,d)) := 
            match arg with
              | Error _ => 
                  Error "Invalid argument"
              | Ok(Value ty' v) => 
                  match typeEq ty ty' with 
                    | true => 
                        Ok((conversionT1T2 f _) v)
                    | false => Error "Argument with invalid type"
                  end
            end.
  Next Obligation.
    apply typeEqEq; auto.
  Defined.

  (**  apply an operator [f] to arguments [args] *)
  Fixpoint opApply 
             {ts: list Ty.t}{d:domain}(f: Si.typeOf (ts,d))
             (args:list(result Va.t)):
    result Va.t :=
    (match args as args', ts as ts', d as d' 
        return Si.typeOf (ts',d')-> 
               result Va.t with 
       | [], [], Total ty => 
           fun f => 
             let v := conversionNIL f in 
               Ok(Value ty v)
       | [], [], Partial ty => 
           fun f => 
             do v <- conversionNIL f; Ok(Value ty v)
       | _::_, [], _ 
       | [], _::_,  _ 
         => fun _ => Error "Invalid number of arguments"
       | e::es, t'::ts', _ =>
           fun f => 
             do f' <- opApplyOneArgument f e;
           opApply f' es
     end) f.
  
  (** ** Expressions *)
  
  (** *** 3 kind of operation 
   - Constant : a value
   - Variable : a natural
   - Operation : an operator and a list of expression as arguments
*)
  Inductive t : Set :=
(*| Const : Va.t -> t *)
  | Var : nat -> t
  | Ope : operation -> list t -> t.

  Lemma expr_ind : 
    forall P : t -> Prop,
(*    (forall (v : Va.t), P (Const v)) -> *)
      (forall (x : nat), P (Var x )) ->
      (forall (op : operation) (l : list t),
         (forall e, In e l-> P e) -> P (Ope op l)) ->
      forall e : t, P e.
  Proof.
  Admitted.
    (* intros P (*H*) H0 H1.
    fix 1.
    destruct e; try solve [ clear expr_ind; auto ].
    apply H1. intros e Hin.
    induction l as [ | e' es' IH] using list_rect.
    - contradiction.
    - simpl in Hin. destruct Hin as [Heq | Hin].
      +  symmetry in Heq; subst. apply expr_ind.
      + apply IH. apply Hin.
  Qed. *)
  
(*Coercion Const: Va.t >-> t.
  Definition intToExp (n : Z) : t :=  n.
  Definition boolToExp (b : bool) : t := b.
  Coercion intToExp: Z >-> t.
  Coercion boolToExp: bool >-> t. *)
  
  (**  Evaluate expresion [e] with the store [sto] *)
  Fixpoint expEval (sto:St.t)(st: state)(e:t): result Va.t :=
    match e with
      | Var id =>
         match get sto id with 
           | Some v => Ok v 
           | None => Error "Variable undefined"  
         end  
      | Ope op exps => 
        let results := List.map (expEval sto st) exps in
        opApply (opDenote st op) results
    end.

  Fixpoint variables (e:t) : list nat := 
    match e with 
      | Var n => [n]
      | Ope _ l => flat_map variables l
    end.
  
  Lemma eq_dec : forall (e e':t), { e = e' } + { ~ e = e' }.
  Proof.
  Admitted.
    (* fix 1. destruct e; intros e'.
(*  - destruct e'; try solve [clear eq_dec0; right; discriminate].
      destruct(Va.eq_dec t0 t1) as [Heq | Hneq].
      + symmetry in Heq; subst; left; reflexivity.
      + right. intro H. inversion H. contradiction. *)
    - destruct e'; try solve [clear eq_dec0; right; discriminate].
      destruct(eq_nat_dec n n0) as [Heq | Hneq].
      + symmetry in Heq; subst; left; reflexivity.
      + right. intro H. inversion H. contradiction.
    - destruct e'; try solve [clear eq_dec0; right; discriminate].
      generalize l0; clear l0; induction l; intro l'.
      + destruct l'. 
        * { destruct(Op.eq_dec o o0) as [Heq | Hneq].
            - left. symmetry in Heq; subst; reflexivity.
            - right. intro H. inversion H. contradiction. }
        * right. intro. discriminate.
      + destruct l'. 
        * right. intro H. discriminate.
        * { case_eq(eq_dec0 a t0); intros H _.
            - case_eq(IHl l'); intros Hl _.
              + symmetry in H, Hl. subst.
                left. inversion Hl; subst; reflexivity.
              + symmetry in H; subst.
                right. intro H. apply Hl. inversion H as [[H1 H0]]. 
                symmetry in H0, H1. subst.
                reflexivity.
            - right. intro H'. inversion H'. contradiction. }
  Qed. *)

(*  
  (** ** Examples *)

  Definition n0:nat := (0:nat).
  Open Local Scope Z_scope.
  Example expressionExample := Ope Plus [ Var n0; Const 10].
  
  
  Example storeExample := Map.add n0 (Value Number 5) (Map.empty V.t).
  
  Eval compute in expEval storeExample expressionExample.
  
  
  Example expressionMod := Ope Mod [ Const 7; Const 3].
  Eval compute in expEval storeExample expressionMod.
  
  Example expressionDiv  := Ope Div [ Const 7; Const 3].
  Eval compute in expEval storeExample expressionDiv.

  Close Local Scope Z_scope.
*)

End TYPE.

Module Make 
       (Import Ad : DecidableInfiniteSet)
       (Import Ty : Type_.TYPE Ad)
       (Import Va : Value.TYPE Ad Ty)
       (Import Si : Operation.Signature.T Ad Ty)
       (Import Op : Operation.T Ad Ty Si)
       (S0 : Store.T Natural Ad Ty Va)
       (Import St : Store.P Natural Ad Ty Va S0).

  Include TYPE Ad Ty Va Si Op S0 St.

End Make.