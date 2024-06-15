Require Import Eqdep_dec.
Require Import List.
Require Import Nat.


(* Ne pas utiliser l1 et l2 qui ne resterons pas *)
Lemma l1 : forall A (H:forall x y:A, {x=y}+{x<>y}) (a:A) l, 
  List.count_occ H (a::l) a < 2 -> ~ In a l. 
Proof.
Admitted.
  (* intros.
  induction l; intro H1; destruct H1;[subst|].

  simpl in H0.
  destruct (H a a);[|intuition].
  apply (lt_n_O _ (lt_S_n _ _ (lt_S_n _ _ H0))).

  apply IHl;[|assumption].
  simpl in H0 |- *.
  destruct (H a a);[|intuition].
  destruct (H a0 a);
    [ apply (lt_S _ _ (lt_S_n _ _ H0))
      | apply H0 ].

Qed. *)

Lemma l2 : forall A (H:forall x y:A, {x=y}+{x<>y}) (a:A) l, 
  (forall b, List.count_occ H (a::l) b < 2) ->
  (forall b, List.count_occ H l b < 2).
Proof.
Admitted.
  (* intros.
  generalize (H0 b); intro H1.
  simpl in H1.
  destruct (H a b).
  apply (lt_S _ _ (lt_S_n _ _ H1)).
  assumption.
Qed. *)

Section Aux.

  Lemma eq_pair : forall (A B: Set) (H:forall x y:A, {x=y}+{x<>y}) 
    (H0:forall x y:B, {x=y}+{x<>y}), forall x y : A * B, {x=y}+{x<>y}.
  Proof.
    intros.
    destruct x, y.
    destruct (H a a0); destruct (H0 b b0); 
      try (subst; auto); right; injection;auto.
  Qed.
    
  Theorem eq_rect_eq_nat :
    forall (p:nat) (Q:nat->Type) (x:Q p) (h:p=p), x = eq_rect p Q x p h.
  Proof.
  Admitted.
    (* intros.
    apply (K_dec_set eq_nat_dec) with (p:=h).
    reflexivity.
  Qed. *)

  Lemma eq_rect_eq_dec_set : forall (A:Set) (H:forall x y:A, {x=y}+{x<>y})
    (p:A) (Q:(A->Type)) (x:Q p) (h:p=p), x = eq_rect p Q x p h.
  Proof.
    intros.
    apply (K_dec_set H) with (p:=h).
    reflexivity.
  Qed.

  Theorem eq_dec_refl_unicity : 
    forall (A:Set) (eq_A_dec : forall x y:A, {x=y}+{x<>y})
      (x:A) (p q : x = x), p = q.
  Proof.
    intros.
    transitivity (refl_equal x); [symmetry|];
      apply (K_dec_set eq_A_dec); reflexivity.
  Qed.

  Arguments eq_dec_refl_unicity [A].

End Aux.

Section InNoDup.

  Variable A : Set.
  Variable eq_A_dec : forall x y : A, {x=y}+{x<>y}.
  Variable eq_A_dep : forall (x:A) (p q : x = x), p = q.

 Theorem in_uniqueness_proof : forall (x:A) (l:list A) 
    (H:forall b, List.count_occ eq_A_dec l b < 2) (p q : In x l), p = q.
  Proof.
    intros.
    induction l.
    elim p.
    case_eq p; intros.
    case_eq q; intros.
    subst.
    replace e0 with (eq_refl x).
    reflexivity.
    apply eq_A_dep.
    generalize (l1 _ eq_A_dec _ _ (H a)); intro.
    elim H2.
    subst;assumption.
    case_eq q; intros.
    generalize (l1 _ eq_A_dec _ _  (H a)); intro.
    subst.
    elim H2.
    assumption.
    rewrite (IHl (l2 _ eq_A_dec  _ _ H) i i0).
    reflexivity.
  Qed.
 
End InNoDup.

Section ListLength.
  
  Variable A : Set.
  Variable eq_A_dec : forall x y : A, {x=y}+{x<>y}.
  Variable eq_A_dep : forall (x:A) (p q : x = x), p = q.

  Create HintDb myresolve.
  Create HintDb myconstructors.

  Hint Resolve eq_pair eq_dec_refl_unicity list_eq_dec eq_A_dec (*eq_nat_dec*) : myresolve.

  Inductive has_length (A:Type) : list A -> nat -> Prop :=
  | has_length_nil : has_length A nil 0
  | has_length_cons : forall a l n, has_length A l n ->
    forall l' k, l'=a::l -> k=S n -> has_length A (l') (k).

  Hint Constructors has_length : myconstructors.

  Lemma has_length_length : forall A l n,
    has_length A l n <-> List.length l = n.
  Proof.
  Admitted.
    (* split;
      [ induction 1; subst; auto
        | generalize n;
          induction l; intros n0 H;
            [rewrite <- H | destruct n0]; eauto].
  Qed. *)

  Scheme has_length_ind' := Induction for has_length Sort Prop.

  Theorem has_length_uniqueness_proof : forall l n (H H0 : has_length A l n), H = H0.
  Proof.
  Admitted.
(*    induction H using has_length_ind'; intro H0.
    
    change (has_length_nil A) with
      (eq_rect (nil,0) 
        (fun l => has_length A (fst l) (snd l)) (has_length_nil A) (nil,0) 
        (refl_equal (nil,0))).
    generalize (refl_equal (@nil A,0)).
    pattern (@nil A) at 1 3 4 6, 0 at 1 3 4 6, H0.
    case H0; intros; subst.
    rewrite <- eq_rect_eq_dec_set; auto.
    discriminate.
 
    change (has_length_cons A a l n H l' k e e0) with
      (eq_rect (l',k) (fun l => has_length A (fst l) (snd l))
        (has_length_cons A a l n H l' k e e0) (l',k) (refl_equal (l', k))).
    generalize e, e0; generalize (refl_equal (l',k)).
    pattern l' at 1 3  5 8, k at 1 3 5 8 , H0.
    case H0; intros; subst.
    discriminate.
    injection e3; intros; subst.
    rewrite <- eq_rect_eq_dec_set; auto.
    f_equal; auto.
  Qed.
*)
End ListLength.

Arguments has_length [A].
Arguments has_length_cons [A].
Arguments has_length_nil {A}.
Arguments has_length_length [A].
Section Le.

  Scheme le_ind' := Induction for le Sort Prop.
  
  Theorem le_uniqueness_proof : forall (n m : nat) (p q : n <= m), p = q.
  Proof.
  Admitted.
(*    induction p using le_ind'; intro q.
    replace (le_n n) with
      (eq_rect n (fun n0 => n <= n0) (le_n n) n (refl_equal n)).
    2:reflexivity.
    generalize (refl_equal n).
    
    pattern n at 2 4 6 10, q.
    case q; [intro | intros m l e].
    rewrite <- eq_rect_eq_nat; trivial.
    contradiction (le_Sn_n m); rewrite <- e; assumption.
    replace (le_S n m p) with
      (eq_rect _ (fun n0 => n <= n0) (le_S n m p) _ (refl_equal (S m))).
    2:reflexivity.
    generalize (refl_equal (S m)).
    pattern (S m) at 1 3 4 6, q. case q; [intro Heq | intros m0 l HeqS].
    contradiction (le_Sn_n m); rewrite Heq; assumption.
    injection HeqS; intro Heq; generalize l HeqS.
    rewrite <- Heq; intros; rewrite <- eq_rect_eq_nat.
    rewrite (IHp l0); reflexivity.
  Qed. 
  *)

End Le.





 

