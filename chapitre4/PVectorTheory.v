Require Import Vector.
Require Import VectorTheory.
Require Import PVector.
Require Import Monad.
Require Import Utf8.
Require Import Lia.
Require Import Bool.
Require Import Decidable.
Require Import Coq.Classes.RelationClasses.
Require Import FunctionalExtensionality.

Open Scope monad_scope.

Module PVectorTheory (Import P : Process) (Import V : Vector P).

  Module Export PV := PVector P V.

(*  Coercion f : V.t >-> V.t.*)
  
  (** ** Basic results *)

  Definition vlt A (v1 v2 : t (option A)) :=
    ∀ i, defined v1 i -> defined v2 i.
  Arguments vlt [A] _ _.

  #[export] Instance vlt_reflexive (A : Type) : Reflexive (@vlt A).
  Proof.
    unfold vlt; auto.
  Qed.

  #[export] Instance vlt_transitive (A : Type) : Transitive (@vlt A).
  Proof.
    unfold vlt; eauto.
  Qed.

  #[export] Instance vlt_vlt (A : Type) : PreOrder (@vlt A).
  Proof.
    split; unfold vlt; auto.
  Qed.
    
  Definition coherent A (v1 v2 : t (option A)) := vlt v1 v2 /\ vlt v2 v1.
  Arguments coherent [A] _ _.

  #[export] Instance coherent_reflexive (A : Type) : Reflexive (@coherent A).
  Proof.
    unfold coherent, vlt; auto.
  Qed.
  
  #[export] Instance coherent_symmetric (A : Type) : Symmetric (@coherent A).
  Proof.
    unfold coherent, vlt; split; intuition.
  Qed.

  #[export] Instance coherent_transitive (A : Type) : Transitive (@coherent A).
  Proof.
    unfold coherent, vlt; split; intuition.
  Qed.

  #[export] Instance coherent_equivalence (A : Type) : Equivalence (@coherent A).
  Proof.
    split; unfold coherent, vlt; solve [split; intuition | intuition].
  Qed.

  (** ** defined *)
  
  Lemma undefined : forall A (v : V.t (option A)) i,
      i < p -> ~ (defined v i) <-> π i v = Some None.
  Proof.
    intros A v i H.
    assert (exists X, π i v = Some X) as [X HX] by eauto with vector. 
    split; intro H0.
    - case_eq X; intros; subst.
      + elim H0.
        exists a; assumption.
      + assumption.
    - intro.
      destruct H1 as [x Hx].
      congruence.
  Qed.

  Lemma defined_dec :
    ∀ A (v : t (option A)) i, decidable (defined v i).
  Proof.
    intros A v i; unfold decidable, defined.
    case_eq (π i v); [intros x H__Eq | intros H__Eq].
    - destruct x.
      + eauto.
      + right.
        intro; destruct H; discriminate.
    - right.
      intro H; destruct H; discriminate.
  Qed.

  (** ** empty, full *)
  
  Lemma isEmpty_dec : ∀ A (v: t (option A)), decidable (empty v).
  Proof.
    eauto using dec_pointwise_neg, dec_not, defined_dec.
  Qed.

  Lemma isFullDec : forall A (v : V.t (option A) ), decidable (full v).
  Proof.
    eauto using dec_pointwise_forall, dec_not, defined_dec.
  Qed.

  Lemma isEmpty0 :
    ∀ A HEq,
      empty (vempty (option A) HEq).
  Proof.
    unfold empty.
    intros A HEq i H.
    assert (i < 0) by congruence.
    exfalso; lia.
  Qed.
  
  (** *** compatible *)

  #[export] Instance compatible_equivalence (A : Type) : Equivalence (@compatible A A).
  Proof.
    split.
    - unfold compatible; split; tauto.
    - split; destruct (H i H0); tauto.
    - split; unfold compatible in *;
        destruct (H i H1), (H0 i H1); eauto.
  Qed.

  Lemma compatible_none : forall A (v v' : V.t (option A) ),
      v ⋕ v' -> forall i, (π i v = Some None <-> π i v' = Some None).
  Proof.
    unfold compatible.
    intros A v v' H i.
    split; intros H0.
    - assert (i < p) by eauto with vector.
      destruct (H i H1).
      apply undefined in H0.
      apply undefined. 
      assumption.
      tauto.
      assumption.
    - assert (i < p) by eauto with vector.
      destruct (H i H1).
      apply undefined in H0.
      apply undefined.
      assumption.
      tauto.
      assumption.
  Qed.
    
  Lemma compatible_empty : forall A (v v' : V.t (option A)),
      v ⋕ v' -> empty v -> empty v'.
  Proof.
    unfold compatible, empty.
    intros A v v' H H0 i H1.
    intro.
    apply H in H2.
    elim (H0 _ H1).
    assumption.
    assumption.
  Qed.

  Lemma compatible_total : forall A (v v' : V.t (option A)),
      v ⋕ v' -> full v -> full v'.
  Proof.
    intros A v v' H H0.
    unfold compatible, full in *.
    intros i H1.
    destruct (H i H1) as [HA HB].
    unfold defined in H0.
    destruct (H0 i H1) as [x HC].
    apply HA.
    unfold defined.
    eauto.
  Qed.
  
  (** ** select **)

(*
  Check (@fmap  option _ (option A) (option A) (fun (x : option A) => if f i x then x else None) (π i v)).
 *)
  Lemma π_select : ∀ A (v : t (option A)) (f : nat -> A -> bool)  i,
      π i (select f v) =
      fmap (λ x, x >>= (λ x0, if f i x0 then Some x0 else None))
           (π i v).
  Proof.
    intros A0 v0 f0 i0.
    unfold select; rewrite vectmapi_eq; reflexivity.
  Qed.

  Lemma select_none : forall A (v : t (option A)) f i,
      π i v = Some None -> π i (select f v) = Some None .
  Proof.
    intros A0 v0 f0 i0 H.
    rewrite π_select; rewrite H; reflexivity.
  Qed.

  Lemma select_none_rev : forall A (v : V.t (option A)) f i,
      π i (select f v) = Some None  ->
      (∃ x, π i v = Some (Some x) /\ f i x = false) \/ π i v = Some None.
  Proof.
    intros A v f i H.
    unfold select in H.
    destruct (vectmapi_some_rev _ _ _ _ _ _ H) as [x [Ha Hb]]; simpl in Hb.
    destruct x; simpl in *.
    - case_eq (f i a); intros H__Eq; rewrite H__Eq in Hb.
      + discriminate.
      + eauto.
    - tauto.
  Qed.
  (* begin hide *)
  Ltac selecttac :=
    match goal with
      [ |- ∀ x, ?P ] => intro; selecttac
    | [ H : context c [select ?f ?v] |- _ ] => unfold select in H; simpl in H; selecttac  
    | [ |- π ?i (select ?f ?v) = ?X ] => rewrite π_select; simpl; selecttac
    | [ H : π ?i ?v = ?X |- _] => rewrite H in *; clear H; simpl in *; selecttac
    | [ H : ?f ?i ?x = true |- _ ] => rewrite H in *; clear H; simpl in *; selecttac
    | [ H : ?f ?i ?x = false |- _ ] => rewrite H in *; clear H; simpl in *; selecttac
    | [ H : context c [if ?f ?i ?a then ?X else ?Y] |- _ ] =>
      let Ha := fresh in
      case_eq (f i a); intro Ha; rewrite Ha in *; simpl in H; selecttac
    | [H : context c [fmap ?f (π ?i ?v)] |- _] =>
      let Ha := fresh in
      case_eq (π i v); [intros a Ha| intro Ha]; rewrite Ha in *; clear Ha; simpl in *; selecttac
    | [H : context c [option_map ?X ?Y ?f (π ?i ?v)] |- _] =>
      let Ha := fresh in
      case_eq (π i v); [intros a Ha| intro Ha]; rewrite Ha in *; clear Ha; simpl in *; selecttac
    | [H : context c [mapi ?f ?v] |- _] => rewrite vectmapi_eq in H; simpl in H; selecttac
    | [H : Some ?X = Some ?Y |- _ ] =>
      let Ha := fresh in
      injection H; intro Ha; rewrite Ha in *; clear H; selecttac
    | [H : Some ?X = None |- _ ] => discriminate
    | [H : None = Some ?X |- _ ] => discriminate
    | _ => easy
    | _ => idtac
    end.
  (* end hide *)
  
  Lemma select_true : forall A (v : V.t (option A)) i (x : A) f,
      π i v = Some (Some x)->
      f i x = true ->
      π i (select f v) = π i v.
  Proof.
    selecttac.
  Qed.

  Lemma select_true_rev : forall A (v : V.t (option A)) i x f,
      π i (select f v) = Some (Some x) ->
      f i x = true /\ π i v = Some (Some x).
  Proof.
    selecttac.
    destruct a; selecttac.
  Qed.

  Lemma select_false : forall A (v : t (option A)) f i x,
      π i v = Some (Some x) ->
      f i x = false -> π i (select f v) = Some None .
  Proof.
    selecttac.
  Qed.

  Lemma select_false_rev : forall A (Σ : V.t (option A)) i σ f,
      π i Σ = Some (Some σ) ->
      π i (select f Σ)  = Some None ->
      f i σ = false.
  Proof.
    selecttac.
  Qed. 
  (*
  Lemma choice_none_rev : forall A (Σ : V.t (option A)) i f,
      π i (select f Σ) = Some None ->
      (exists sigma_i, π i Σ = Some (Some sigma_i) /\ f i sigma_i = false)
      \/ π i Σ= Some None.
  Proof.
    intros A v i f H.
    rewrite π_select in H.
    case_eq (π i v); [intros a Ha | intros Ha]; rewrite Ha in *; simpl in *; [ | discriminate].
    case_eq a; [intros b Hb | intros Hb]; rewrite Hb in *; simpl in *; [ | right; reflexivity].
    case_eq (f i b); intros H__Eq; rewrite H__Eq in *;  simpl in *; [discriminate | left; eauto].
  Qed.*)
    
  Lemma select_empty_neg : forall A (f : nat -> A -> bool) (v : V.t (option A)),
      empty (select f v) -> select (fun n x => negb (f n x)) v = v.
  Proof.
    intros A f v H.
    apply vect_extensionality.
    intros i H__lt.
    assert (π i (select f v) = Some None).
    {
      unfold empty, defined in H. 
      assert (∃ X, π i (select f v) = Some X) as [X HX] by auto with vector.
      case_eq X; [intros Y HY | intros HY]; subst.
      elim (H _ H__lt); eauto.
      assumption.
    }
    destruct (select_none_rev _ _ _ _ H0) as [[x [Hx Hy]] | ].
    - assert (negb (f i x) = true) by now rewrite Hy.
      now apply select_true with (x:= x).
    - now rewrite select_none by assumption.
  Qed.
  
  Lemma select_empty_neg_neg : forall A (f : nat -> A -> bool) (v : V.t (option A)),
      empty (select (fun i n => negb (f i n)) v) -> select f v = v.
  Proof.
    intros A f v H.
    replace f with (fun i n => negb (negb (f i n))).
    apply select_empty_neg.
    assumption.
    do 2 (apply functional_extensionality; intro).
    apply negb_involutive.
  Qed.

  Lemma select_empty : forall A (vsigma : V.t A) f,
      empty (select f (fmap Some vsigma)) ->
      forall i sigma_i, π i vsigma = Some sigma_i -> f i sigma_i = false.
  Proof.
    intros A vsigma f H i sigma_i H0.
    assert (π i (fmap Some vsigma) = Some (Some sigma_i)) by (rewrite π_fmap; rewrite H0; reflexivity).
    unfold empty in H.
    assert (i < p) as H__lt by eauto with vector.
    case_eq (f i sigma_i); intros.
    - elim (H _ H__lt).
      unfold defined.
      exists sigma_i.
      assert (π i (fmap Some vsigma) = Some (Some sigma_i)) by (rewrite π_fmap; rewrite H0; reflexivity).
      rewrite select_true with (x:=sigma_i) by assumption.
      assumption.
    - reflexivity.
  Qed.
  
  Lemma select_full : forall A f (v : V.t (option A)),
      full (select f v) -> empty (select (fun i x => negb (f i x)) v).
  Proof.
    intros A f v H.
    unfold full, empty in *.
    intros i H0 H__defined.
    assert(defined (select f v) i) as H__defined2 by auto.
    unfold defined in H__defined, H__defined2.
    destruct H__defined as [X HA], H__defined2 as [Y HY].
    destruct (select_true_rev _ _ _ _ _ HA).
    destruct (select_true_rev _ _ _ _ _ HY).
    replace X with Y in * by congruence.
    rewrite H3 in H1.
    discriminate.
  Qed.
    
  Lemma select_full_neg : forall A f (v : V.t (option A) ),
      full (select (fun i n => negb (f i n)) v) -> empty (select f v).
  Proof.
    intros A f v H.
    replace f with (fun i n => negb (negb (f i n))).
    apply select_full.
    assumption.
    do 2 (apply functional_extensionality; intro).
    apply negb_involutive.
  Qed.

  #[export] Hint Resolve select_none select_none_rev : select.
  #[export] Hint Resolve select_true select_true_rev : select.
  #[export] Hint Resolve select_false select_false_rev : select.
  #[export] Hint Resolve select_empty select_empty_neg : select.
  #[export] Hint Resolve select_full select_full_neg : select.
  (** ** merge *)

  Lemma π_merge : ∀ A (v1 v2 : t (option A)) v i,
      merge v1 v2 = Some v -> i < p ->
      Some (π i v) = liftA2 _ _ _ _ (@oplus A) (π i v1) (π i v2).
  Proof.
    intros A v1 v2 v i H H0.
    unfold merge in H.
    generalize zip_prop; intro.
    edestruct H1.
    apply H2 with (i:=i) in H.
    destruct H as [x1 [x2 [y [HA [HB [HC HD]]]]]].
    rewrite HA, HB, HC; simpl.
    f_equal.
    symmetry.
    assumption.
    assumption.
  Qed.
    
  Lemma merge_sym : forall A (v1 v2 : V.t (option A)),
      merge v1 v2 = merge v2 v1.
  Proof.
    intros A v1 v2.
    apply (zip_commute (option A)).
    unfold oplus.
    intros x1 x2.
    destruct x1, x2; reflexivity.
  Qed.

  Lemma defined_lt :
    ∀ A (v : t (option A)) i,
      defined v i -> i < p.
  Proof.
    intros A v i H.
    destruct H as [x Hx].
    eauto with vector.
  Qed.

  #[export] Hint Resolve defined_lt : vector.

  Lemma merge_exclusive : forall A (v1 v2 v : V.t (option A)),
      merge v1 v2 = Some v ->
      ∀ i, defined v1 i -> ¬ defined v2 i.
  Proof.
  Admitted.
  
  Lemma merge_defined : forall A (v1 v2 v : V.t (option A)) i,
      merge v1 v2 = Some v ->
      defined v1 i -> π i v = π i v1.
  Proof.
    intros A v1 v2 v i H H0.
    assert (i < p) by eauto with vector.
    generalize (π_merge _ _ _ _ _ H H1); intro.
    destruct H0 as [x Hx].
    rewrite Hx in *.
    simpl in H2.
    assert (¬ defined v2 i).
    eapply merge_exclusive; eauto.
    unfold defined; eauto.
    assert (∃ y, π i v2 = Some y) as [y Hy] by eauto with vector.
    rewrite Hy in H2.
    case_eq y ;intros; subst.
    elim H0; unfold defined; eauto.
    unfold oplus in H2.
    congruence.
  Qed.
  
  Lemma merge_undefined : forall A (v1 v2 v : V.t (option A)) i,
      merge v1 v2 = Some v ->
      ¬ defined v i -> π i v = π i v2.
  Proof.
  Admitted.

  Lemma merge_allnone :
    ∀ A (v : t (option A)), merge v (make (fun _ => None)) = Some v.
  Proof.
  Admitted.

  
  Lemma merge_empty : forall A (v1 : V.t (option A)),
      empty v1 -> forall v2, merge v1 v2 = Some v2.
  Proof.
    intros v1 H v2.
    unfold empty in H.
    unfold merge.
  Admitted.
  (*apply V.zip_prop2.
    intros i H0.
    destruct (H i H0) as [x [HA HB]].
    subst.
    assert (exists x2, π v2 i = Some x2) as [x2 Hx2] by eauto with vector.
    exists None, x2, x2.
    split.
    assumption.
    split.
    assumption.
    split.
    assumption.
    unfold oplus.
    destruct x2; reflexivity.
  Qed.*)

  Lemma merge0 :
    ∀ (A : Type) (v : t (option A)),
      p = 0 -> merge v v = Some v.
  Proof.
    intros A v H.
    unfold merge, zip.
    rewrite erase_prop.
    apply vect_extensionality.
    intros i H__lt.
    assert (i < 0) by congruence.
    exfalso; lia.
  Qed.

  Lemma oplus_None :
    ∀ (A : Type) (X : option A),
      oplus X None = Some X.
  Proof.
  Admitted.

  Lemma merge_full : forall A (v1 v2 : V.t (option A)),
      full v1 -> merge v1 v2 = Some v1 \/ merge v1 v2 = None.
  Proof.
  Admitted.

  Lemma merge_full2 : forall A (v1 v2 : V.t (option A)),
  full v2 -> merge v1 v2 = Some v2 \/ merge v1 v2 = None.
Proof.
Admitted.


(*
  Lemma merge_total_empty : forall A (v1 v2 v : V.t (option A)),
      merge v1 v2 = Some v -> full v1 -> empty v2.
  Proof.
  Admitted.*)
(*  
  Lemma merge_full__ : forall A (v1 : V.t (option A)),
      full v1 -> forall v2, (exists v, merge v1 v2 = Some v) -> empty v2.
  Proof.
  Admitted.*)
(*
  
    intros n v1 H v2 H0.
    unfold isTotal in H.
    unfold isEmpty.
    intros i H1.
    destruct H0 as [v Hv].
    destruct (H i H1) as [x [HA HB]].
    assert (exists x, π v2 i = Some x) as [y Hy] by eauto with vector.
    apply V.zip_prop1 with (i:=i) in Hv.
    destruct Hv as [x1 [x2 [z [HC [HD [HE HF]]]]]].
    unfold oplus in HF.
    destruct x1; destruct x2.
    - discriminate.
    - eauto.
    - exfalso; congruence.
    - eauto.
    - assumption.
  Qed.
 *)
  
  Lemma merge_coherent : ∀ A (v1 v2 : t (option A)),
      merge v1 v2 <> None -> coherent v1 v2.
  Proof.
  Admitted.
  
  Lemma fork_join : forall A (f : nat -> A -> bool) (v v1 v2 : V.t (option A)),
      (select f v) ⋕ v1 ->
      (select (fun i n => negb (f i n)) v) ⋕ v2 ->
      exists v', merge v1 v2 = Some v' /\ v ⋕ v'.
  Proof.
  Admitted.

   (** ** fmap *)

  Lemma full_inv : forall A (v : V.t (option A)),
      full v -> exists v',  fmap Some v' = v.
  Proof.
    intros A v H.
    unfold full in H.
    apply vectmap_inv.
    intros i H0.
    unfold defined in H.
    auto.
  Qed.
  
  Lemma full_inj : forall A (v : V.t A), full (fmap Some v).
  Proof.
    intros A vsigma.
    unfold full.
    intros i H.
    assert (exists sigma_i, π i vsigma = Some sigma_i) as [sigma_i Hi] by eauto with vector.
    unfold defined.
    exists (sigma_i).
    rewrite π_fmap.
    simpl.
    rewrite Hi.
    reflexivity.
  Qed.
  
  Lemma empty_inj: forall A (v : V.t A), p > 0 -> ~ empty (fmap Some v).
  Proof.
    intros A vsigma H.
    unfold empty.
    intro.
    assert (0 < p) by lia.
    unfold defined in H0.
    elim (H0 _ H1).
    assert (exists x, π 0 vsigma = Some x) as [X HX] by eauto with vector.
    exists X.
    rewrite π_fmap.
    simpl.
    rewrite HX.
    reflexivity.
  Qed.
 
  Lemma select_fmap_true : forall A (Σ : V.t A) i f,
      fmap (f i) (π i Σ) = pure true ->
      π i (select f (fmap pure Σ)) = pure (π i Σ).
  Proof.
    intros A Σ i f H.
    assert (∃ a, π i Σ = pure a) as [a Ha] by (destruct (π i Σ); [eauto | discriminate]).
    assert (π i (fmap pure Σ) = pure (π i Σ)) by (rewrite π_fmap; rewrite Ha; reflexivity).
    assert (f i a = true) by (rewrite Ha in H; simpl in H; congruence).
    rewrite Ha in H0.
    rewrite select_true with (x:=a) by first [assumption | congruence].
    rewrite Ha; assumption.
  Qed.

  Lemma select_fmap_false : forall A (Σ : V.t A) i x f,
      π i Σ = Some x -> f i x = false ->
      π i (select f (fmap Some Σ)) = Some None.
  Proof.
    intros A Σ i x f H H0.
    assert (π i (fmap Some Σ) = Some (Some x)) by (rewrite π_fmap; rewrite H; reflexivity).
    rewrite select_false with (x:=x) by assumption.
    reflexivity.
  Qed.

  Fact empty_compatible:
  ∀ {A} (Σ : t A)(v'' : t (option A)), 
    empty (lift Σ) → (lift Σ) ⋕ v'' → empty v''.
Proof.
  intros A Σ v'' H H0.
  unfold empty, compatible in *.
  intros i H2.
  intro. 
  destruct (H0 i H2).
  elim (H i H2).
  auto.
Qed.

Fact full_compatible:
  ∀ {A} (Σ : t A)(v'' : t (option A)),full (lift Σ) → (lift Σ) ⋕ v'' → full v''.
Proof.
  intros A Σ v'' H H0.
  unfold full, compatible in *.
  intros i H1; destruct (H0 i H1); auto.
Qed.

Lemma fmap_some :
  ∀ A B (f : nat -> A -> B) (Σ : t A) (Σ' : t B),
    fmap (λ i, fmap (λ σ, f i σ)) (make id) <*> lift Σ = lift Σ' ->
    fmap (λ i σ, f i σ) (make id) <*> Σ = Σ'.
Proof.
  intros A B f0 Σ Σ' H.
  apply vect_extensionality.
  intros i H0.
  rewrite π_ap.
  rewrite π_fmap.
  rewrite π_make.
  apply extrev with (i:=i) in H.
  rewrite π_ap in H.
  rewrite π_fmap in H.
  rewrite π_make in H.
  simpl in *.
  case_eq (π i Σ).
  + intros a H1.
    assert (π i (fmap Some Σ) = Some (Some a)).
    rewrite π_fmap.
    rewrite H1.
    reflexivity.
    unfold lift in H.
    rewrite H2 in H; simpl in H.
    case_eq (π i Σ').
    *intros b H3.
    assert (π i (fmap Some Σ') = Some (Some b)).
    rewrite π_fmap.
    rewrite H3.
    reflexivity.
    rewrite H4 in H.
    injection H; intros; subst.
    reflexivity.
    * intros H3.
      assert (π i (fmap Some Σ') = None).
      rewrite π_fmap.
      rewrite H3.
      reflexivity.
      rewrite H4 in H.
      discriminate.
  + intros H1.
    assert (π i (fmap Some Σ) = None). 
    rewrite π_fmap.
    rewrite H1.
    reflexivity.
    unfold lift in H.
    rewrite H2 in H.
    case_eq (π i Σ').
    * intros s H3.
      assert (π i (fmap Some Σ') = Some (Some s)).
      rewrite π_fmap.
      rewrite H3.
      reflexivity.
      exfalso; congruence.
    * trivial.
  + assumption.
  + assumption.
  + assumption.
Qed.

(* plus général, vecmap de fonction injective*)
Lemma lift_inj : forall A  (Σ Σ' : t A), lift Σ = lift Σ' -> Σ = Σ'.
Proof.
  intros A Σ Σ' H_Eq.
  exact (vectmap_some_inj _ _ _ H_Eq).
Qed.

Lemma lift_Some : forall A (Σ : t A) i σ,
  π i Σ = Some σ -> π i (lift Σ) = Some (Some σ).
Proof.
  intros A Σ i σ H_eq.
  unfold lift.
  rewrite π_fmap; simpl.
  rewrite H_eq; reflexivity.
Qed.

Lemma lift_Some' : forall A (Σ : t A) (Ω : t (option A)) i σ,
Ω = lift Σ -> π i Σ = Some σ -> π i Ω = Some (Some σ).
Proof.
  intros A Σ Ω i σ H_lift H_eq.
  unfold lift in H_lift.
rewrite H_lift.
rewrite π_fmap.
rewrite H_eq.
reflexivity.
Qed.


End PVectorTheory.
