Set Implicit Arguments.
Generalizable All Variables.

Require Import Structures.Equalities.
Require Import Morphisms.
Require Import SetoidList.

Open Scope signature_scope.

Section TypeWithEquivalence.

  Context `{EquivA: @Equivalence A eqA}.
  Context `{ltAOrder: @StrictOrder A ltA}.
  Context `{eqALtACompatibles : Proper _ (eqA==>eqA==>iff) ltA }.

  Inductive lltA : list A -> list A -> Prop :=
  | lltA_nil: forall x xs, lltA nil (cons x xs)
  | lltA_ltA_cons: 
    forall x xs y ys, 
      ltA x y ->
      lltA (cons x xs) (cons y ys)
  | lltA_lltA_cons: 
    forall x xs y ys, 
      eqA x y ->
      lltA xs ys ->
      lltA (cons x xs) (cons y ys).

  Global Program Instance lltAOrder: StrictOrder lltA.
  Next Obligation.
    unfold Irreflexive, complement, Reflexive.
    intro l; induction l; intro H.
    - inversion H.
    - inversion H as [| x xs y ys HltA| x xs y ys Heq HlltA]; subst.
      + contradict HltA.
        apply StrictOrder_Irreflexive.
      + now apply IHl.
  Qed.
  Next Obligation.
    unfold Transitive.
    intros l1. induction l1; intros l2 l3 H1 H2.
    - inversion H1; subst.
      inversion H2; subst; constructor.
    - inversion H1 as [| x xs y ys HltA| x xs y ys Heq HlltA]; 
      inversion H2 as [| x' xs' y' ys' HltA'| x' xs' y' ys' Heq' HlltA']; 
      subst; try discriminate. 
      + replace x' with y in * by congruence. constructor. now transitivity y. 
      + replace x' with y in * by congruence. constructor. 
        rewrite <- Heq'. trivial.
      + replace x' with y in * by congruence. constructor.
        rewrite Heq. trivial.
      + replace x' with y in * by congruence.
        replace xs' with ys in * by congruence. 
        constructor 3.
        now transitivity y.
        now apply IHl1 with (y:=ys).
  Qed.

End TypeWithEquivalence.
      