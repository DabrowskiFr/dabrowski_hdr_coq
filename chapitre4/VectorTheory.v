Require Import Top.Vector.
Require Import Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.Compare_dec.
Require Import Utf8.
Require Import Decidable.
Require Import Monad.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Le.
Require Import Prelude.
Open Scope program_scope.

Module VectorTheory (Import P : Process) (Import V : Vector P).

  (** ** Basic results *)
  
  Lemma π_prop1 :  ∀ (A : Type) (v : t A) (i : nat) x, π i v = Some x -> i < p.
  Proof.
    intros A v i x H.
    destruct π_prop with (A:=A) (v:=v) (i:=i).
    apply H0.
    exists x.
    assumption.
  Qed.

  Lemma π_prop2 :  ∀ (A : Type) (v : t A) (i : nat),
      i < p -> (∃ x : A, π i v = Some x).
  Proof.
    apply π_prop.
  Qed.

  Lemma vzeq : forall (A : Type) (v v' : V.t A),  p = 0 -> v = v'.
  Proof.
    intros A v v' H__EQ.
    apply vect_extensionality.
    intros i H__lt.
    rewrite H__EQ in H__lt.
    exfalso; lia.
  Qed.
    
  #[export] Hint Resolve π_prop1 π_prop2 vzeq : vector.

  (** ** Construction *)
  Lemma vect_forall :
    ∀ A (P : nat -> A -> Prop), (∀ i, i < p -> ∃ x_i, P i x_i) ->
      ∃ (v : V.t A), ∀ i, i < p -> ∃ x_i, π i v = Some x_i /\ P i x_i.
  Proof.
    intros A P H__all.
    case_eq p; [intros H__Eq | intros n H__Eq].
    - exists (vempty _ H__Eq); intuition lia.
    - assert (∃ (f : nat -> A), ∀ i, i < S n -> P i (f i)) as [f Hf].
      {
        assert (S n <= p) by lia; clear H__Eq.
        induction n.
        - assert (0 < p) as H__lt by lia.
          destruct (H__all 0 H__lt) as [a Ha].
          exists (fun x => a).
          intros i H__lt2.
          now replace i with 0 by lia.
        - assert (S n <= p) as H__le by lia.
          destruct (IHn H__le) as [f Hb].
          assert (S n < p) as H__lt by lia.
          destruct (H__all _ H__lt) as [a Ha].
          exists (fun m => if eq_nat_dec m (S n) then a else f m).
          intros i H__lt2.  
          case_eq (eq_nat_dec i (S n)); intros; subst.
          assumption.
          assert (i < S n) by lia.
          now apply Hb.
      }
      exists (make f).
      intros i H__lt.
      exists (f i).
      rewrite π_make by lia; intuition.
  Qed.

  Lemma vect_forall2 : 
    ∀ (A B : Type) (P : nat → A → B -> Prop),
      (∀ i : nat, i < p → ∃ (x : A) (y : B), P i x y)
      → ∃ (v1 : V.t A) (v2 : V.t B), ∀ i : nat,
          i < p → ∃ (x : A) (y : B), π i v1 = Some x ∧
                                     π i v2 = Some y /\ P i x y.
  Proof.
    intros A B P H__all.
    case_eq p; [intros H__Eq | intros n H__Eq].
    - exists (vempty _ H__Eq), (vempty _ H__Eq) ; intuition lia.
    - assert (∃ (f : nat -> A) (g: nat -> B), ∀ i, i < S n -> P i (f i) (g i)) as [f [g Hf]].
      {
        assert (S n <= p) by lia; clear H__Eq.
        induction n.
        - assert (0 < p) as H__lt by lia.
          destruct (H__all 0 H__lt) as [a [b Ha]].
          exists (fun x => a), (fun x => b).
          intros i H__lt2.
          now replace i with 0 by lia.
        - assert (S n <= p) as H__le by lia.
          destruct (IHn H__le) as [f [g Hb]].
          assert (S n < p) as H__lt by lia.
          destruct (H__all _ H__lt) as [a [b Ha]].
          exists (fun m => if eq_nat_dec m (S n) then a else f m).
          exists (fun m => if eq_nat_dec m (S n) then b else g m).
          intros i H__lt2.
          case_eq (eq_nat_dec i (S n)); intros; subst.
          assumption.
          assert (i < S n) by lia.
          now apply Hb.
      }
      exists (make f), (make g).
      intros i H__lt.
      exists (f i), (g i).
      rewrite π_make by lia.
      simpl.
      intuition.
      apply π_make.
      lia.
  Qed.

  (** ** Decidability *)
  
  Lemma dec_pointwise_forall :
    ∀ A (v : t A) P,
      (∀ i, i < p -> decidable (P v i)) -> decidable (∀ i, i < p -> P v i).
  Proof.
    intros A v P H.
    assert (forall k,
               k <= p ->
               decidable
                 (forall i, i < k -> P v i)).
    {
      intros k H0.
      induction k.
      - left.
        intros i H1.
        exfalso; lia.
      - assert (k <= p).
        lia.
        destruct (IHk H1).
        + assert (exists x,  π k v = Some x) as [x Hx] by eauto with vector.
          assert (k < p) by lia.
          destruct (H _ H3).
          * left.
            intros i H5.
            destruct (eq_nat_dec i k);[subst|].
            -- assumption.
            -- assert (i < k) by lia.
               eauto.
          * right.
            contradict H4.
            assert (k < S k) by lia.
            apply H4.
            assumption.
        + right.
          contradict H2.
          intros i H3.
          apply H2.
          auto.
    }
    apply H0.
    lia.
  Qed.

  Lemma dec_pointwise_exists :
    ∀ A (v : t A) P,
      (∀ i, i < p -> decidable (P v i)) -> decidable (exists i, i < p /\ P v i).
  Proof.
    intros A v P H.
    assert (forall k,
               k <= p ->
               decidable
                 (exists i, i < k /\ P v i)).
    {
      intros k H0.
      induction k.
      - right.
        intro.
        do 2 destruct H1.
        lia.
      - assert (k <= p).
        lia.
        destruct (IHk H1).
        + assert (exists x,  π k v = Some x) as [x Hx] by eauto with vector.
          assert (k < p) by lia.
          destruct (H _ H3).
          * left.
            eauto.
          * do 2 destruct H2.
            left.
            eauto.
        + assert (k < p) by lia.
          destruct (H _ H3).
          left; eauto.
          right.
          contradict H2.
          do 2 destruct H2.
          destruct (Nat.eq_dec x k).
          subst.
          elim H4; assumption.
          assert (x < k) by lia.
          eauto.
    }
    assert (p <= p) by lia.
    apply (H0 _ H1).
  Qed.

  Lemma dec_pointwise_neg :
    ∀ A (v : t A) P,
      (∀ i, i < p -> decidable (¬ (P v i))) ->
      decidable (∀ i, i < p -> ¬ (P v i)).
  Proof.
    intros A v P H.
    set (Q := fun v i => ¬ P v i).
    assert (decidable (∀ i, i < p -> Q v i)) as Ha by now apply dec_pointwise_forall.
    trivial.
  Qed.
  
  Lemma dec_forall :
    forall A (P : A -> Prop),
      (forall x, decidable (P x)) ->
      (forall (v : V.t A),
          decidable (forall i, i < p -> exists x, π i v = Some x /\ P x)).
  Proof.
    intros A P H v.
    set (Q := fun v i => ∃ x, π i v = Some x /\ P x).
    assert (decidable(∀ i, i < p -> Q v i)).
    apply dec_pointwise_forall.
    intros i H0.
    unfold Q.
    case_eq (π i v); intros; subst.
    destruct (H a).
    left.
    eauto.
    right.
    contradict H2.
    do 2 destruct H2.
    injection H2; intros; subst.
    assumption.
    right.
    intro.
    do 2 destruct H2.
    discriminate.
    apply H0.
  Qed.
      
  Lemma dec_exists :
    forall A (P : A -> Prop),
      (forall x, decidable (P x)) ->
      (forall (v : V.t A),
          decidable (exists i x, π i v = Some x /\ P x)).
  Proof.
    intros A P H v.
    assert (forall k, k <= p ->
                      decidable (exists i, i < k /\ exists x, π i v = Some x /\ P x)).
    {
      intros k H0.
      induction k.
      - right.
        intro H1.
        destruct H1 as [i [HA HB]].
        lia.
      - assert (k <= p) by lia.
        destruct (IHk H1).
        + destruct H2 as [i [HA HB]].
          left; eauto.
        + assert (exists x, π k v = Some x) as [x Hx] by eauto with vector.
          destruct (H x).
          * left.
            exists k; eauto.
          * right.
            intro H4.
            destruct H4 as [i [HA HB]].
            destruct (eq_nat_dec i k);[subst|].
            -- contradict H3.
               destruct HB as [y [HC HD]].
               congruence.
            -- contradict H2.
               exists i.
               split.
               lia.
               assumption.
    }
    destruct (H0 p (le_refl p));[left | right].
    - destruct H1 as [i [HA HB]]; eauto.
    - contradict H1.
      destruct H1 as [i [x [HA HB]]].
      exists i.
      split.
      + destruct π_prop with (A:=A) (v:=v) (i:=i).
        apply H1.
        exists x.
        assumption.
      + exists x.
        split; assumption.
  Qed.

  (**  ** fmap *)

  Lemma vectmap_eq : forall A B (v : V.t A) i (f : A -> B),
      π i (fmap f v) = fmap f (π i v).
  Proof.
    intros A B v i f.
    rewrite π_fmap; reflexivity.
  Qed.
  
  Lemma vectmap_some_rev :
    ∀(A B : Type)(Σ : t A)(i : nat) (y : B)(f : A -> B),
      π i (fmap f Σ) = Some y -> ∃ x, π i Σ = Some x /\ f x = y.
  Proof.
    intros A B Σ i x f H.
    autorewrite with projection in H; simpl in H.
    autorewrite with projection in H; simpl in H.
    case_eq (π i Σ); [intros a H__Eq | intros H__Eq] ; rewrite H__Eq in *.
    injection H; intros; subst ; eauto.
    discriminate.
  Qed.
  
  Lemma vectmap_none_rev : ∀(A B : Type)(Σ : t A)(i : nat) (f : A -> B),
      π i (fmap f Σ) = None -> π i Σ = None.
  Proof.
    intros A B Σ i f H.
    autorewrite with projection in H.
    case_eq (π i Σ); [intros a H__Eq | intros H__Eq] ; rewrite H__Eq in *; easy.
  Qed.
  
  #[export] Hint Resolve vectmap_eq vectmap_some_rev vectmap_none_rev.

  Definition mapi (A B : Type) (f : nat -> A -> B) (v : t A) : t B :=
    fmap f (make id) <*> v.
  
  Arguments mapi [A B] _ _.

  Lemma vectmapi_eq : forall A B (v : V.t A) i (f : nat -> A -> B),
      π i (mapi f v) = fmap (f i) (π i v). 
  Proof.
    intros A B v i f.
    unfold mapi.
    rewrite <- vectmap_eq.
    rewrite π_ap.
    rewrite applicative_fmap.
    rewrite applicative_fmap.
    rewrite <- applicative_homomorphism.
    rewrite π_ap.
    rewrite π_ap.
    rewrite π_ap.
    f_equal.
    f_equal.
    destruct (lt_dec i p).
    - rewrite π_make by assumption.
      rewrite π_pure by assumption.
      reflexivity.
    - assert (π i (make id) = None).
      case_eq (π i (make id)); intros.
      assert (i < p) by eauto with vector.
      intuition.
      reflexivity.
      rewrite H.
      assert (π i (pure i) = None).
      case_eq (π i (pure i)); intros.
      assert (i < p) by eauto with vector.
      intuition.
      reflexivity.
      rewrite H0.
      reflexivity.
  Qed.

  Lemma vectmapi_some_rev : forall A B (v : V.t A) i y (f : nat -> A -> B),
      π i (mapi f v) = Some y -> exists x, π i v = Some x /\ y = f i x.
  Proof.
    intros A B v i y f H.
    assert (i < p) by eauto with vector.
    unfold mapi in H.
    rewrite π_ap in H.
    rewrite π_fmap in H.
    simpl in H.
    rewrite π_make in H.
    simpl in H.
    assert (∃ x, π i v = Some x) as [x Hx] by eauto with vector.
    rewrite Hx in H.
    injection H; intros; subst.
    exists x.
    intuition.
    assumption.
  Qed.
  
  Lemma vectmap_extensionality : forall A B (f g : A -> B) (v : V.t A),
      (forall x, f x = g x) -> fmap f v = fmap g v.
  Proof.
    intros A B f g v H.
    replace g with f.
    reflexivity.
    now apply functional_extensionality.
  Qed.

  #[export] Hint Unfold compose.
  
  Lemma vectmap_compose : forall A B C (f : B -> C) (g : A -> B) (v : V.t A),
      fmap f (fmap g v) = fmap (f ∘ g) v.
  Proof.
    intros A B C f g v.
    rewrite <- fmap_comp.
    reflexivity.
  Qed.

  Lemma vectmap_inv : forall A B (v : V.t B) (f : A -> B),
      (forall i, i < p -> exists x, π i v = Some (f x)) ->
      (exists (v' : V.t A), fmap f v' = v).
  Proof.
    intros A B v f H.
    assert (forall k, k <= p ->
                      exists v' : V.t A,
                        forall i, i < k -> π i (fmap f v') = π i v).
    {
      intros k H0.
      induction k.
      - case_eq p; intros.
        + exists (vempty _ H1).
          intros i H__lt.
          exfalso; lia.
        + assert (0 < S n) as HU by intuition.
          rewrite H1 in *.
          destruct (H 0 HU).
          exists (make (fun _ => x)).
          intros i H__lt2.
          exfalso; lia.
      - assert (k <= p) as HV by intuition.
        destruct (IHk HV) as [v' Hv'].
        assert (k < p) by intuition.
        assert (exists y, π k v = Some (f y)) as [y Hy] by eauto.
        exists (mapi (fun i x => if i =? k then y else x) v').
        intros i H2.
        assert (i < p) by lia.
        assert (exists x, π i v' = Some x) as [x Hx] by eauto with vector.
        destruct (lt_dec i k).
        + assert (i <> k) as HW by lia.
          assert (π i (fmap f v') = π i v) by auto.
          assert (π i v = Some (f x)) as HT.
          {
            rewrite <- H4.
            rewrite π_fmap.
            simpl.
            rewrite Hx.
            reflexivity.
          }
          assert (i =? k = false) as HX by now apply Nat.eqb_neq.
          rewrite vectmap_eq.
          rewrite vectmapi_eq.
          rewrite HX.
          simpl.
          unfold option_map.
          rewrite Hx.
          intuition.
        + assert (i = k) as HW  by lia; subst.
          assert (k =? k = true) as HX by now apply Nat.eqb_eq.
          rewrite vectmap_eq.
          rewrite vectmapi_eq.
          rewrite HX.
          simpl.
          unfold option_map.
          rewrite Hx.
          intuition.
    }
    destruct (H0 p (le_refl p)) as [v' Hv'].
    exists v'.
    now apply vect_extensionality.
  Qed.
  
  #[export] Hint Resolve vectmap_some_rev vectmap_none_rev : vectmap.
  
  Lemma vectmap_inj : forall A B (f : A -> B) (x y : V.t A),
      (forall x y, f x = f y -> x = y) -> fmap f x = fmap f y -> x = y.
  Proof.
    intros A B f x y H H0.
    apply vect_extensionality.
    intros i H1.
    assert (π i (fmap f x) = π i (fmap f y)).
    rewrite H0.
    reflexivity.
    do 2 rewrite π_fmap in H2.
    simpl in H2.
    case_eq (π i x); case_eq (π i y); intros; subst.
    - rewrite H3 in H2.
      rewrite H4 in H2.
      injection H2; intros; subst.
      f_equal.
      apply H.
      assumption.
    - rewrite H3 in H2.
      rewrite H4 in H2.
      discriminate.
    - rewrite H3 in H2.
      rewrite H4 in H2.
      discriminate.
    - reflexivity.
  Qed.

  Lemma vectmap_some_inj :
    forall A (x y : V.t A),
      fmap Some x = fmap Some y -> x = y.
  Proof.
    intros A x y H.
    apply vectmap_inj with (B:= option A) (f:= Some); [congruence | assumption].
  Qed.

  #[export] Hint Resolve vectmap_extensionality vectmap_compose : vectmap.

  (** ** zip  *)

  Definition zip (A B C : Type) (op : A -> B -> option C)
             (v1 : t A) (v2 : t B) : (option (t C)) :=
    erase (ap (ap (pure op) v1) v2).
  
  Arguments zip [A B C] _ _ _.
  
  Lemma zip_prop : forall A B C (f : A -> B -> option C) v1 v2 (v : t C),
      zip f v1 v2 = Some v <->
      (forall i, i < p ->
            exists x1 x2 y,
              π i v1 = Some x1 /\
              π i v2 = Some x2 /\
              π i v = Some y /\
              f x1 x2 = Some y).
  Proof.
    intros A B C f v1 v2 v.
    unfold zip.
    split.
    - intros H i H0.
      assert (∃ x1, π i v1 = Some x1) as [x1 Hx1] by eauto with vector.
      assert (∃ x2, π i v2 = Some x2) as [x2 Hx2] by eauto with vector.
      assert (∃ y, π i v = Some y) as [y Hy] by eauto with vector.
      exists x1, x2, y.
      split.
      assumption.
      split.
      assumption.
      split.
      assumption.
      apply erase_prop in H.
      simpl in H.
      assert (π i (pure f) = Some f).
      {
        rewrite π_pure.
        reflexivity.
        assumption.
      }
      assert (π i ((pure f <*> v1) <*> v2) = Some (f x1 x2)).
      {
        do 2 rewrite π_ap.
        simpl.
        rewrite H1.
        rewrite Hx1.
        rewrite Hx2.
        reflexivity.
      }
      assert (π i (fmap Some v) = Some (Some y)).
      {
        rewrite π_fmap; simpl.
        rewrite Hy.
        reflexivity.
      }
      congruence.
    - intros H.
      apply erase_prop.
      apply vect_extensionality.
      intros i H0.
      destruct (H i H0) as [x1 [x2 [y [Ha [Hb [Hc Hd]]]]]].
      assert ((π i (fmap pure v)) = pure Some <*>  π i v).
      {
        apply π_fmap.
      }
      rewrite H1.
      rewrite Hc.
      simpl.
      assert (π i (pure f) = Some f).
      {
        rewrite π_pure.
        reflexivity.
        assumption.
      }
      assert (π i ((pure f <*> v1) <*> v2) = Some (f x1 x2)).
      {
        do 2 rewrite π_ap.
        simpl.
        rewrite H2.
        rewrite Ha.
        rewrite Hb.
        reflexivity.
      }
      rewrite H3.
      f_equal.
      assumption.
  Qed.
  Lemma zip_commute:
    ∀ (A B : Type)(v1 v2 : t A) (f : A -> A -> option B),
      (∀ x1 x2, f x1 x2 = f x2 x1) ->
      zip f v1 v2 = zip f v2 v1.
  Proof.
    intros nprocs v1 v2.
  Admitted.

    Lemma extrev: 
    ∀ A (v v' : t A),
      v = v' -> (∀ i, i < p → π i v = π i v').
  Proof.
  Admitted.

  Lemma fmap_some_inj : 
  forall A (x y : t A),
  fmap Some x = fmap Some y -> x = y.
Proof.
  eauto using vectmap_inj, some_inj.
Qed.

End VectorTheory.
