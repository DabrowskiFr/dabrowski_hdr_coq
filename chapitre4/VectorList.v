Require Import Monad.
Require Import List.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Basics.
Require Import Vector.
Require Import Coq.Classes.EquivDec.
Require Import Utf8.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.
Require Import Nat.

Open Scope functor_scope.

Inductive vect (A : Type) : nat -> Type :=
  nil : vect A 0
 |cons : forall (x : A) (n:nat), vect A n -> vect A (S n).

Definition case0 {A} (P:vect A 0 -> Type) (H:P (nil A))  (v : vect A 0)  : P v :=
match v with
  | nil _ => H
  |_ => fun devil => False_ind (@IDProp) devil
end.

Definition caseS {A} (P : forall {n}, vect A (S n) -> Type)
  (H : forall h {n} t, @P n (cons _ h _ t)) {n} (v: vect A (S n)) : P v :=
match v with
  | cons _ h _ t => H h t
  |_ => fun devil => False_ind (@IDProp) devil
end.

Definition caseS_ {A} (P : forall {n}, vect A (S n) -> Set)
  (H : forall h {n} t, @P n (cons _ h _ t)) {n} (v: vect A (S n)) : P v :=
match v with
  | cons _ h _ t => H h t
  |_ => fun devil => False_ind (@IDProp) devil
end.

Lemma vect0 : ∀ (A : Type) (v : vect A 0), v = nil A.
Proof.
  intros A v.
  pose (P := fun v => v = nil A).
  assert (P (nil A)) by reflexivity.
  now assert (P v) by now apply case0.  
Qed.

Lemma vect__S : ∀ (n : nat) (A : Type) (v : vect A (S n)), ∃ a v', v = cons _ a _ v'.
Proof.
  intros n A v.
  pose (P := fun n v => ∃ (a : A) (v' : vect A n), v = cons A a n v').
  assert (∀ n v, P n v).
  {
    apply caseS.
    intros h n0 t.
    exists h, t; reflexivity.
  }
  apply H.
Qed.

Fixpoint vectmake n A (f : nat -> A) : vect A n :=
  match n with
    0 => nil A
  | S n => cons _ (f 0) _ (vectmake n A (f ∘ (add 1)))
  end.

Fixpoint nth (n : nat) (A : Type) (i : nat) (v : vect A n) : option A :=
  match v with
    nil _ => None
  | cons _ x _ v =>
    match i with
      0 => Some x
    | S i => nth _ _ i v
    end
  end.

Arguments nth [n A] _ _.


Fixpoint vectmap (n : nat) (A B : Type)(f : A -> B) (v : vect A n) : vect B n :=
  match v with
    nil _ => (nil B)
  | cons _ x n0 v' => cons B (f x) n0 (vectmap _ _ _ f v')
  end.

Arguments vectmap [n A B] _ _.

Program Fixpoint vectapply (n : nat) (A B : Type) (vf : vect (A -> B) n) (vx : vect A n) : vect B n :=
  match vf with
    nil _ => nil B
  | cons _ f _ vf =>
    match vx with
      nil _ => nil B
    | cons _ x _ vx => cons _ (f x) _ (vectapply _ _ _ vf vx)
    end                 
  end.

Arguments vectapply [n A B] _ _.

Fixpoint vectFoldR (n : nat) (A B : Type) (op : A -> B -> B) (neutral : B) (v : vect A n) : B :=
  match v with
    nil _ => neutral
  | cons _ x _ v => op x (vectFoldR _ A B op neutral v)
  end.
    
Fixpoint vectFoldMap (n : nat) (A B: Type)  (E : Monoid B) (f : A -> B) (x : vect A n) :=
  match x with
    nil _ => mempty
  | cons _ x _ v => mappend (f x) (vectFoldMap _ _ _ _ f v)
  end.

(** * Properties of nth *)

Lemma nth_elem :
  ∀ n A (v : vect A n) i, 
    (∃ x, nth i v = Some x) <-> i < n .
Proof.
  intros n A.
  split.
  - revert i.
    induction v.
    + destruct 1 as [x Hx].
      destruct i; discriminate.
    + destruct 1 as [y Hy].
      destruct i; [intuition |].
      assert (i < n) by eauto.
      lia.
  - revert i.
    induction v.
    + intros i H.
      exfalso; lia.
    + intros i H.
      destruct i.
      exists x.
      reflexivity.
      assert (i < n) by lia.
      destruct (IHv _ H0).
      eauto.
Qed.

Lemma nth_elem_not :
  ∀ n A (v : vect A n) i, 
    (nth i v = None) <-> ¬ i < n.
Proof.
  intros n A v i.
  destruct (nth_elem n A v i) as [HA HB].
  split.
  - intros H.
    destruct (lt_dec i n) as [HC | HC].
    destruct (HB HC) as [x Hx].
    exfalso; congruence.
    assumption.
  - intros H.
    destruct (nth i v).
    assert (i < n).
    apply HA.
    eauto.
    intuition.
    reflexivity.
Qed.

(** * Properties of make *)

Lemma nth_vectmake :
  ∀ n A i f,
    i < n ->
    nth i (vectmake n A f) = Some (f i).
Proof.
  induction n; intros A i f H.
  - exfalso; lia.
  - destruct i.
    reflexivity.
    simpl.
    rewrite IHn by lia.
    reflexivity.
Qed.

(** * Properties of map *)

Lemma vectmap_prop_id :
  ∀ (n : nat) (A : Type),
    (@vectmap n A A id)  = id.
Proof.
  intros n A.
  apply functional_extensionality.
  induction x.
  - reflexivity.
  - simpl.
    rewrite IHx.
    reflexivity.
Qed.

Lemma vectmap_prop_comp :
  ∀ (n : nat) (A B C : Type) (f : B -> C) (g : A -> B),
    (@vectmap n B C f) ∘ (@vectmap n A B g) = @vectmap n A C (f ∘ g).
Proof.
  intros n A B C f g.
  apply functional_extensionality.
  induction x.
  - reflexivity.
  - simpl; rewrite <- IHx.
    unfold compose.
    reflexivity.
Qed.

Lemma nth_vectmap :
  ∀ n A B (v : vect A n) (f : A -> B) i x,
  nth i v = Some x ->
  nth i (vectmap f v) = Some (f x).
Proof.
  induction v.
  - destruct i; discriminate.
  - destruct i; simpl in *.
    + congruence.
    + now apply IHv.
Qed.

(** * Properties of apply *)

Lemma apply_id :
  ∀ n (A : Type) (x : vect A n), vectapply (vectmake n (A → A) (λ _ : nat, id)) x = x.
Proof.
  induction n.
  - intros A x.
    replace x with (nil A) by (symmetry; apply vect0).
    reflexivity.
  - intros A x.
    destruct (vect__S _ _ x) as [a [y Hy]].
    subst.
    simpl.
    f_equal.
    rewrite IHn.
    reflexivity.
Qed.

Lemma apply_compose :
  ∀ n A B C (u : vect (B -> C) n) (v : vect (A -> B) n) (w : vect A n),
    vectapply (vectapply (vectapply (vectmake n ((B → C) → (A → B) → A → C) (λ _ : nat, compose)) u) v) w =
    vectapply u (vectapply v w).
Proof.
  intros n A B C u v w.
  induction n.
  - replace u with (nil (B -> C)) by (symmetry; apply vect0).
    reflexivity.
  - destruct (vect__S _ _ u) as [f [u' Hu']].
    destruct (vect__S _ _ v) as [g [v' Hv']].
    destruct (vect__S _ _ w) as [x [w' Hw']].
    subst.
    simpl.
    f_equal.
    apply IHn.
Qed.

Lemma apply_make :
  ∀ n A B (f : A -> B) (x : A),
    vectapply (vectmake n (A -> B) (λ _ : nat, f)) (vectmake n A (λ _ : nat, x)) = vectmake n B (λ _ : nat, f x).
Proof.
  induction n.
  - reflexivity.
  - intros A B f x.
    simpl.
    f_equal.
    unfold compose.
    rewrite IHn.
    reflexivity.
Qed.

Lemma apply_interchange :
  ∀ n (A B : Type) (u : vect (A → B) n) (y : A),
    vectapply u (vectmake n A (λ _ : nat, y)) =
    vectapply (vectmake n ((A → B) → B) (λ (_ : nat) (y0 : A → B), y0 y)) u.
Proof.
  induction n.
  - intros.
    replace u with (nil (A -> B)) by (symmetry; apply vect0).
    reflexivity.
  - intros A B u y.
    destruct (vect__S _ _ u) as [f [u' Hu']].
    subst.
    simpl.
    f_equal.
    unfold compose.
    rewrite IHn.
    reflexivity.
Qed.
(*
Lemma nth_vectapply :
  ∀ n A B (vf : vect (A -> B) n) (v : vect A n) i,
    nth i (vectapply vf v) = (nth i vf) <*> (nth i v).
Proof.
  induction vf.
  - intros v i.
    destruct i; reflexivity.
  - intros v i.
    destruct i; simpl.
    + destruct (vect__S _ _ v) as [y [v' Hy]]; subst.
      reflexivity.
    + destruct (vect__S _ _ v) as [y [v' Hy]]; subst.
      simpl.
      apply IHvf.
Qed.
*)

Lemma nth_vectapply :
  ∀ n A B (vf : vect (A -> B) n) (v : vect A n) i f x,
    nth i vf = Some f ->
    nth i v = Some x ->
    nth i (vectapply vf v) = Some (f x).
Proof.
  induction vf.
  - intros v i f x H H0.
    destruct i; discriminate.
  - intros v i f x0 H H0.
    destruct i; simpl in *.
    + destruct (vect__S _ _ v) as [y [v' Hy]]; subst.
      injection H; injection H0; intros; subst; clear H H0.
      reflexivity.
    + destruct (vect__S _ _ v) as [y [v' Hy]]; subst.
      now apply IHvf.
Qed.

Lemma nth_fmap :
  ∀ n (A B : Type) (f : A -> B) (i : nat) (v : vect A n),
    nth i (vectmap f v) = pure f <*> nth i v.
Proof.
  intros n A B f i v.
  destruct (lt_dec i n).
  - assert (∃ x, nth i v = Some x) as [x Hx] by now apply nth_elem.
    rewrite Hx.
    simpl.
    now apply nth_vectmap.
  - replace (nth i (vectmap f v)) with (@None B).
    replace (nth i v) with (@None A).
    reflexivity.
    symmetry; now apply nth_elem_not.
    symmetry; now apply nth_elem_not.
Qed.

Lemma nth_make : 
  ∀ n (A : Type) (f : nat -> A),
    ∀ i, i < n -> nth  i (vectmake n _ f) = pure (f i).
Proof.
  intros n A i f H.
  apply nth_vectmake.
  assumption.
Qed.

Lemma nth_pure :
  ∀ n (A : Type) (x : A),
    ∀ i, i < n ->  nth i (vectmake n _ (fun _ => x)) = pure x.
Proof.
  intros n A x i H.
  apply (nth_make n _).
  assumption.
Qed.

(** * Other properties *)

Lemma extensionality :
  forall n A (v v' : vect A n),
    (forall i, i < n -> nth i v = nth i v') -> v = v'.
Proof.
  intros n A v v' H.
  induction n.
  - replace v with (nil A) by (rewrite vect0; reflexivity).
    replace v' with (nil A) by (rewrite vect0; reflexivity).
    reflexivity.
  - destruct (vect__S _ _ v) as [x [v0 H__EQ1]].
    destruct (vect__S _ _ v') as [y [v0' H__EQ2]].
    subst.
    f_equal.
    + assert (0 < S n) by intuition.
      generalize (H 0 H0); intro.
      injection H1; intros; subst.
      reflexivity.
    + apply IHn.
      intros i H0.
      assert (S i < S n) by intuition.
      apply (H (S i) H1).
Qed.

Definition g A (x y : option A) : option (option A) :=
  match (x,y) with
    (Some x, None) => Some (Some x)
  | (None, Some y) => Some (Some y)
  | (None, None) => Some None
  | (Some x, Some y) => None
  end.

Definition cons_t (A : Type) (t : Type -> Type) (E : Functor t) (F : Applicative t E)
           (x : t A) (n : nat) (v : t (vect A n)) : t (vect A (S n)) :=
  (liftA2 _ _ _ _ (fun a b => cons A a n b)) x v.

Fixpoint erase_t_ n A (t : Type -> Type) (E : Functor t) (F : Applicative t E)
         (v : vect (t A) n) : t (vect A n) :=
  match v with
    nil _ => pure (nil A)
  | cons _ x _ v => cons_t A t E F x _ (erase_t_ _ _ t E F v)
  end.

Definition cons_opt (A : Type)  (x : option A) (n : nat) (v : option (vect A n)) : option (vect A (S n)) :=
  (liftA2 _ _ _ _ (fun a b => cons A a n b)) x v.

Fixpoint erase_ n A (v : vect (option A) n) : option (vect A n) :=
  match v with
    nil _ => Some (nil A)
  | cons _ x _ v => cons_opt A x _ (erase_ _  _ v)
  end.

Lemma vect_EqDec_ : forall (A : Type),
    (forall (x y:A), x = y \/ x<>y) -> forall n (v1 v2 : vect A n), v1=v2 \/ v1 <> v2.
Proof.
  intros A H.
  induction n.
  - intros v1 v2.
    left.
    rewrite (vect0 _ v1).
    rewrite (vect0 _ v2).
    reflexivity.
  - intros v1 v2.
    
    destruct (vect__S n A v1) as [a1 [v1' Ha1]].
    destruct (vect__S n A v2) as [a2 [v2' Ha2]].
    destruct (IHn v1' v2').
    + destruct (H a1 a2).
      * left.
        subst.
        reflexivity.
      * right.
        subst.
        contradict H1.
        injection H1; intros; subst.
        reflexivity.
    + right.
      subst.
      contradict H0.
      injection H0; intros; subst.
      intuition.
Qed.

Lemma erase_prop_ :
  ∀ n A v v',
    erase_ n A v = Some v' <-> v = vectmap Some v'.
Proof.
  intros n A0 v v'.
  split; revert v'.
  - induction v.
    +  intros v' H.
       simpl in *.
       injection H; intros; subst.
       reflexivity.
    + intros v' H.
      simpl in *.
      unfold cons_opt in H.
      simpl in H.
      destruct x.
      -- case_eq (erase_ n A0 v).
         ++ intros v0 Ha.
            rewrite Ha in H.
            injection H; intros; subst.
            simpl.
            rewrite IHv with v0.
            reflexivity.
            assumption.
         ++ intros H0.
            rewrite H0 in H.
            discriminate.
      -- discriminate.
  - induction v.
    + intros v' H.
      simpl in *.
      rewrite (vect0 A0 v').
      reflexivity.
    + intros v' H.
      simpl in *.
      unfold cons_opt.
      simpl.
      destruct (vect__S _ _ v') as [v'0 [HA HB]]; subst.
      simpl in H.
      injection H; intros; subst.
      assert (v = vectmap Some HA) by intuition.
      apply IHv in H1.
      * case_eq (erase_ n A0 v).
        -- intros v0 Ha.
           rewrite H1 in Ha.
           injection Ha; intros; subst.
           reflexivity.
        -- intros Ha.
           exfalso; congruence.
Qed.  

Lemma nth_le :
  ∀ n A (v : vect A n) i,
    nth i v = None <-> i >= n.
Proof.
  intros n A v i.
  split.
  - intros H.
    destruct (le_lt_dec n i).
    assumption.
    edestruct nth_elem.
    destruct (H1 l).
    rewrite H2 in H.
    discriminate.
  - intros H.
    case_eq (nth i v); intros; subst.
    assert (i < n).
    edestruct nth_elem.
    apply H1.
    eauto.
    exfalso; lia.
    reflexivity.
Qed.

Lemma nth_none:
  ∀ n (A B : Type) (f : A → B) (i : nat) (v : vect A n), nth i v = None → nth i (vectmap f v) = None.
Proof.
  intros n A B f i v H.
  assert (i >= n) by (edestruct nth_le; eauto).
  edestruct nth_le; eauto.
Qed.

Lemma vectmap_pure :
  ∀ p (A B : Type)(f : A → B),vectmap f = (λ v : vect A p, vectapply (vectmake p (A → B) (λ _ : nat, f)) v).
Proof.
  intros p A B f.
  apply functional_extensionality.
  intros x.
  apply extensionality.
  intros i H.
  assert (∃ y, nth i x = Some y) as [y Hy].
  apply nth_elem.
  assumption.
  rewrite nth_vectmap with (x:=y).
  erewrite nth_vectapply.
  f_equal.
  rewrite nth_make.
  reflexivity.
  assumption.
  assumption.
  assumption.
Qed.

Module VectorImp (Export P : Process) : Vector P.

  Definition t := fun A => vect A p.

  Definition vempty (A : Type) : p = 0 -> t A := fun H => eq_rect_r _ (nil A) H.

  #[export, refine] Instance v_functor : Functor t :=
    {
      fmap := @vectmap p;
    }.
  Proof.
    apply (vectmap_prop_id p).
    apply (vectmap_prop_comp p).
  Defined.
    
  Definition π : ∀ A, nat -> t A -> option A := @nth p.

  Lemma π_prop :forall (A : Type) (v : t A) (i : nat),
      (exists x, π _ i v = Some x) <-> i < p.
  Proof.
    eauto using nth_elem.
  Qed.

  #[export, refine] Instance v_applicative : Applicative t v_functor :=
    {
      pure A x := vectmake p A (fun  => x);
      ap _ _ f v := vectapply f v
    }.
  Proof.
    - apply apply_id.
    - apply apply_compose.
    - apply apply_make.
    - apply apply_interchange.
    - apply vectmap_pure.
  Defined.

  Definition make := vectmake p.

  Definition erase A (v : t (option A)) : option (t A) := erase_ p A v.
  
  Lemma erase_prop :
    ∀ A  v v',
      erase A v = pure v' <-> v = fmap pure v'.
  Proof.
    apply erase_prop_.
  Qed.
    
  Lemma π_fmap :
    ∀ (A B : Type) (f : A -> B) (i : nat) (v : t A),
      π _ i (fmap f v) = pure f <*> π _ i v.
  Proof.
    intros A B f i v.
    generalize (nth_vectmap p A B v f i); intro.
    case_eq (nth i v); intros; subst.
    - unfold π.
      rewrite H0.
      apply H in H0.
      simpl.
      assumption.
    - unfold π.
      rewrite H0.
      simpl.
      now apply nth_none.
  Qed.
  
  Lemma π_make : 
    ∀ (A : Type) (f : nat -> A),
      ∀ i, i < p -> π _ i (make _ f) = pure (f i).
  Proof.
    apply nth_make.
  Qed.
  
  Lemma π_pure :
    ∀ (A : Type),
      ∀ i (x: A), i < p -> π _ i (pure x) = pure x.
  Proof.
    intros A i x H.
    apply (nth_pure p A x i H).
  Qed.
  
  Lemma π_ap :
    ∀ (A B : Type) (v1 : t (A -> B)) (v2 : t A) (i : nat),
      π _ i (v1 <*> v2) =  (π _ i v1) <*> (π _ i v2).
  Proof.
    intros A B v1 v2 i.
    case_eq (π _ i v1); intros; subst.
    - assert (i < p).
      edestruct π_prop.
      apply H0.
      exists b.
      apply H.
      assert (∃ a, π _ i v2 = Some a) as [a Ha].
      now apply π_prop.
      rewrite Ha.
      simpl.
      now apply nth_vectapply .
    - simpl.
      case_eq (π B i (vectapply v1 v2)); intros; subst.
      assert (i < p).
      edestruct π_prop.
      eauto.
      assert (∃ x, π (A -> B) i v1 = Some x) as [x Hx].
      apply π_prop.
      assumption.
      rewrite H in Hx.
      discriminate.
      reflexivity.
  Qed.

  Lemma vect_extensionality :
    forall A (v v' : t A),
      (forall i, i < p -> π _ i v = π _ i v') -> v = v'.
    apply extensionality.
  Qed.
    
  Lemma vect_eq_dec : forall (A : Type),
      (forall (x y:A), x=y \/ x <> y) -> forall (v1 v2 : t A), v1=v2 \/ v1<>v2.
  Proof.
    intros A H v1 v2.
    exact (vect_EqDec_ _ H p v1 v2).
  Qed.
  
End VectorImp.
