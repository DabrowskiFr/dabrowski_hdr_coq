
(** * Tactics *)
Ltac inj H := injection H; intros; subst.

Ltac simplify :=
    repeat match goal with
           | [ H : ex _ |- _ ] => destruct H
           end;
    repeat match goal with
           | [H : _ /\ _  |- _ ] => destruct H
           end; subst.

           Lemma some_inj : forall {A : Type},
           forall x y : A, Some x = Some y -> x = y.
         Proof.
           intros A x y H.
           injection H; intros; subst.
           reflexivity.
         Qed.

  Definition option_fold {A B : Set} 
    (f : A -> B) (z : B) (o : option A) : B :=
      match o with 
        | None => z 
        | Some x => f x
      end.
