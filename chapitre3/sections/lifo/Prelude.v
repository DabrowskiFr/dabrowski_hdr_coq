Require Import List.
Require Import ListBasics.
Require Import RelationClasses.
Require Import Structures.Equalities.
Require Import Lia.
Require Import Bool ZArith OrderedType OrderedTypeEx FMapInterface FMapList FMapFacts. 
Require Import Coq.Structures.DecidableTypeEx.

Class Inhabited (A:Type) (default:A) := {}.

Module Type InhabitedType (Import T:Typ).
  Parameter default : T.t.
  Declare Instance inhabited : Inhabited T.t default.
End InhabitedType.

(******************************************************)
(******************************************************)

Notation "A == B" := (A = Some B) (at level 40).

(** General tactics *)

Ltac immediate :=
  solve [ assumption | congruence | discriminate].

Ltac have H p :=
  match goal with
      H' : p |- _ => 
      let H0 := fresh in 
      assert p as H0 by apply H; clear H0
    | _ => fail
  end.

Ltac hypothesis H :=
  solve [inversion H; eauto | eapply H; eauto | erewrite H; eauto].

Ltac functionnal_option :=
  match goal with
    | H0 : ?F ?X1 = Some ?Y1, H1 : ?F ?X2 = Some ?Y2 |- ?Y1 = ?Y2 =>
      cut (X1 = X2);
        [ intro;
          match goal with
            | H2 : X1=X2 |- _ =>
              rewrite H2 in *; rewrite H0 in H1; injection H1; auto end | ]
  end.

Ltac unfoldOne := 
  match goal with 
      [ x := _ |- _ ] => unfold x in *; clear x
  end. 

Ltac safe_subst := repeat unfoldOne; subst. 

Ltac inverseOneTuple :=
  match goal with 
    | [ H : ( _ , _ ) = ( _ , _) |- _ ] => 
      inversion H;
        safe_subst;
        clear H
  end.

Ltac inverseTuples := repeat inverseOneTuple.

(******************************************************)
(******************************************************)

(** Logic *)

Lemma neg_exists_forall_neg : 
  forall (A : Type) (P : A -> Prop),
    ~ (exists x, P x) <-> (forall x, ~ P x).
Proof.
  intros A P.
  split.
  - intros h_exists x.
    contradict h_exists; now exists x.
  - intros h_forall [x h_x].
    contradict h_x; trivial.
Qed.

Lemma nforalln_exists : 
  forall (P : nat -> Prop) (h_dec : forall n, {P n} + {~ P n}),
    forall n,
      not (forall x, x < n -> ~ P x) -> 
      exists x, P x.
Proof.
  intros P h_dec n h_nforall.
  induction n; [intuition |].
  Admitted.
(*  destruct (h_dec n).
  - (now exists n). 
  - assert (~ (forall x, x < n -> ~ P x)).
    {
      intro h_n.
      assert (forall x, x < S n -> ~ P x).
      {
        intros x h_lt;
        destruct (Peano_dec.eq_nat_dec x n); [subst|]. 
        - assumption.
        - assert (x < n) by intuition. 
          now apply h_n. 
      }
      now apply h_nforall .
    }
    now apply IHn. 
Qed.*)

(******************************************************)
(******************************************************)

(** Compare *)

Lemma lt_pred : forall x y z, x < y < z -> x < z-1.
Proof.
  intros x y z H; auto with *.
Qed.

Lemma le_neq_lt : forall i j, i <= j -> i <> j -> i < j.
Proof.
  auto with *.
Qed.

Lemma lt_n_m_Sm : forall x y, x < y -> y < S x -> False. 
Proof.
  intros x y lt_x_y lt_y_Sx.
  assert (y < y) by eauto using Nat.le_trans.
  now elim (Nat.lt_irrefl y).
Qed.
  
Lemma lt_predn_m_n : forall x y, pred x < y -> y < x -> False.
Proof.
  intros x y lt_predx_y lt_y_x.
  destruct x; 
    [ now elim (Nat.nlt_0_r y) 
    | now apply lt_n_m_Sm with (x:= x) (y:=y)].
Qed.

Lemma nlt_le : forall n m, ~ n < m -> m <= n.
Proof.
  intros n m nlt_n_m.
  destruct (Nat.le_gt_cases m n);
    [ assumption 
    | exfalso; intuition].
Qed.

Lemma nlt_neq_gt : forall n m, ~ n < m -> n <> m -> n > m.
Proof.
Admitted.
  (* intros n m nlt_n_m neq_n_m.
  destruct (le_lt_or_eq _ _ (nlt_le _ _ nlt_n_m)); 
    [ assumption 
    | exfalso; intuition].
Qed. *)

Hint Immediate nlt_le nlt_neq_gt : arith v62. 

(******************************************************)
(******************************************************)

(** Option monad *)

Declare Scope monad_scope.

Definition bind {A B : Type} : option A -> (A -> option B) -> option B :=
  fun x f => match x with None => None | Some y => f y end.

Notation "'do' X <- A ; B" := 
  (bind A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200)
  : monad_scope.

Open Scope monad_scope.

Definition lift (A B : Type) (f : A -> B) : option A -> option B := 
  (fun (e : option A) => do x <- e; Some (f x)). 

Arguments lift [A B] _ _.

Lemma bind_Some :
  forall {A : Set} (e : option A), (do y <- e; Some y) = e.
Proof.
  intros A e.
  destruct e; reflexivity.
Qed.

Remark bind_inversion :
  forall (A B : Type) (x: option A) (f: A -> option B) (y: B),
    (do z <- x; f z) = Some y ->
  exists z, x = Some z /\ f z = Some y.
Proof.
  intros A B x f y Heq.
  destruct x as [ a | ]; 
    [ (exists a; tauto)
    | discriminate ].
Qed.

Arguments bind_inversion [A B] _ _ _ _.

Lemma lift_inversion :
  forall (A B : Type) (f : A -> B) (x : option A) (y : B),
    lift f x == y -> exists z, x ==  z /\ f z = y.
Proof.
  intros A B f x y H.
  destruct (bind_inversion _ _ _ H); exists x0; intuition congruence.
Qed.

Arguments lift_inversion [A B f x y] _.

Lemma lift_f_defined :
  forall (A B : Type) (f : A -> B) (x : option A),
    (exists y, lift f x == y) <-> (exists y, x == y).
Proof.
  intros A B f x.
  split; intros [y h_y]. 
  - destruct (lift_inversion h_y) as [z [Ha Hb]]; eauto.
  - rewrite h_y; exists (f y); reflexivity.
Qed.

Arguments lift_f_defined {A B f x}.
    
Lemma lift_fst_inv:
  forall A B p x,
    lift (@fst A B) p ==x -> exists y, p == (x, y).
Proof.
  intros A B p x h_eq.
  destruct (lift_inversion h_eq) as [[x' y] [Ha Hb]].
  exists y; subst; reflexivity.
Qed.

Arguments lift_fst_inv [A B p x] _.

Hint Resolve lift_fst_inv : proj.

Lemma lift_snd_inv :
  forall A B p y, 
    lift (@snd A B) p  == y -> exists x, p == (x, y).
Proof.
  intros A B p y h_eq.
  destruct (lift_inversion h_eq) as [[x y'] [Ha Hb]].
  exists x; subst; reflexivity.
Qed.

Arguments lift_snd_inv [A B p y] _.

Hint Resolve lift_snd_inv : proj.

Lemma lift_fst_snd : 
  forall A B p,
    (exists x, lift (@fst A B) p == x) -> (exists y, lift (@snd A B) p == y).
Proof.
  intros A B p [x h_eq].
  destruct (lift_fst_inv h_eq) as [y h_y].
  rewrite h_y; exists y; reflexivity.
Qed.

Arguments lift_fst_snd [A B p] _.

Hint Resolve lift_fst_snd : proj.

Lemma lift_snd_fst :
  forall A B p,
    (exists y, lift (@snd A B) p == y) -> (exists x, lift (@fst A B) p == x).
Proof.
  intros A B p [y h_eq].
  destruct (lift_snd_inv h_eq) as [x h_x].
  rewrite h_x; exists x; reflexivity.
Qed.

Arguments lift_snd_fst [A B p] _.

Hint Resolve lift_snd_fst : proj.

Lemma lift_pair_surjective :
  forall A B p x y,
  lift (@fst A B) p == x ->
  lift (@snd A B) p == y ->
  p == (x, y).
Proof.
  intros A B p x y h_eq_x h_eq_y.
  destruct p; [ | discriminate].
  - injection h_eq_x; injection h_eq_y; intros; subst.
    f_equal; apply surjective_pairing.
Qed.

Hint Resolve lift_pair_surjective : proj.

Lemma lift_nth_error_defined_left : 
  forall (A B : Set) (k : nat) (f : A -> B) (l : list A), 
    (exists y, lift f (nth_error l k) == y) -> k < length l.
Proof.
  intros A B i f l.
  intros [y h_y].
  apply nth_error_defined_lt.
  eapply lift_f_defined; eauto.
Qed.

Lemma lift_nth_error_defined_right : 
  forall (A B : Set) (k : nat) (f : A -> B) (l : list A), 
    k < length l -> (exists y, lift f (nth_error l k) == y).
Proof.
  intros A B i f l.
  intros h_lt.
  eapply lift_f_defined; eauto with nth_error.
Qed.

Lemma lift_nth_error_append : 
  forall (A B : Set) (k : nat) (f : A -> B) (X : B) (l l' : list A),
    lift f (nth_error l k) == X -> lift f (nth_error (l ++ l') k) == X.
Proof.
  intros A B k f X l l' h_eq.
  assert (nth_error (l ++ l') k = nth_error l k).
  apply nth_error_append_left.
  eapply lift_nth_error_defined_left; eauto.
  congruence.
Qed.

(* Create HintDb nth_error. *)

Hint Resolve lift_nth_error_append : nth_error.
Hint Resolve lift_nth_error_defined_left : nth_error.
Hint Resolve lift_nth_error_defined_right : nth_error.


Lemma lift_nth_error_append_cons_nil_neq :
  forall (A B : Type) (f : A -> B) (l : list A) k a a',
    lift f (nth_error (l++a::nil) k) == a'->
    (f a) <> a' ->
    lift f (nth_error l k) == a'.
Proof.
  intros A B f. induction l as [| x xs]; intros k a a' H H0.
  - destruct k; simpl in *.
    + inversion H; contradict H0; trivial.
    + destruct k; simpl in *; discriminate.
  - destruct k; simpl in *.
    + trivial.
    + eapply IHxs; eassumption.
Qed.
    
Hint Resolve lift_nth_error_append_cons_nil_neq : nth_error.

Lemma lift_nth_error_append_left :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A) k,
    k < length l1 -> 
    lift f (nth_error (l1++l2) k) = lift f (nth_error l1 k).
Proof.
  intros A B f; induction l1 as [| x xs IHxs]; intros l2 k H.
  - simpl in *. lia.
  - destruct k; simpl in *.
    + trivial.
    + assert(k < length xs) by auto with *.
      now apply IHxs.
Qed.

Lemma lift_nth_error_append_right : (* énoncé précédent faux *)
  forall (A B : Type) (f : A -> B) (l1 l2 : list A) k,
    ~ (k < length l1) -> 
    lift f (nth_error (l1++l2) k) = lift f (nth_error l2 (k - length l1)).
Proof.
  intros A B f; induction l1 as [|x xs IH]; intros l2 k H.
  - simpl. rewrite Nat.sub_0_r. trivial.
  - destruct k. simpl in *.
    + admit.
    + assert(not(k < length xs)) by (contradict H; simpl; auto with *).
      simpl. rewrite IH; [|assumption].
      trivial.
Admitted.

Ltac nth_error_rewrite Ha :=
  let Hb := fresh in 
  match type of Ha with
      lift ?f (nth_error (?l ++ ?l') ?i) == ?X =>
      match goal with 
          H : ?i < length ?l |- _ =>
          assert (lift f (nth_error l i) == X) 
            as Hb
              by (rewrite lift_nth_error_append_left in Ha; simpl in Ha; try assumption)
        | H : ~ ?i < length ?l |- _ =>
          rewrite lift_nth_error_append_right in Ha; simpl in Ha; try assumption
        | _ => assert True
      end
  end. 

Ltac nth_error_autorewrite :=
  match goal with 
      H : lift ?f (nth_error (?l ++ ?l') ?i) == ?X, H0 : ?i < length ?l |- _ =>
      rewrite lift_nth_error_append_left in H; simpl in H; try assumption; nth_error_autorewrite
    | H : lift ?f (nth_error (?l ++ ?l') ?i) == ?X, H0 : ~ ?i < length ?l |- _ =>
      rewrite lift_nth_error_append_right in H; simpl in H; try assumption; nth_error_autorewrite
    | H : lift ?f (nth_error (?l ++ ?e::nil) ?i) == ?e', H0 : ?e <> ?e' |- _ =>
      rewrite nth_error_append_cons_nil_neq in H; simpl in H; try assumption; nth_error_autorewrite
    | _ => idtac
  end. 

(******************************************************)
(******************************************************)

(** Infinite *)

Definition infinite (A: Type) : Type :=
  { bij: (A->nat)*(nat->A) | forall (n:nat), (fst bij)((snd bij) n) = n }.

Lemma sMaxNotInL: 
  forall(l:list nat), 
    forall(n:nat), In n l -> n <= List.fold_right max 0 l.
Proof.
  induction l; intros n H; simpl; inversion H; subst; 
  eauto using Nat.le_max_l, Nat.le_max_r, Nat.le_trans.
Qed.

Lemma infiniteIsNotFinite:
  forall (A:Type),
    infinite A -> 
    forall (l:list A), exists(a:A), not(In a l).
Proof.
  unfold infinite; intros A H l; destruct H as [bij  H].
  destruct bij as [f g]. simpl in H.
  set(l':=List.map f l).
  set(max:=List.fold_right max 0 l').
  exists(g(1+max)).
  intro H'.
  apply in_map with (f:=f) in H'.
  rewrite H in H'.
  rewrite in_map_iff in H'.
  destruct H' as [ x [H1 H2] ].
  apply in_map with (f:=f) in H2.
  apply sMaxNotInL in H2.
  rewrite H1 in H2.
  unfold max in H2.
  contradict H2.
  firstorder.
  Admitted.

Module Type Infinite (Import T:Typ). 
  Parameter infinite: infinite t.
End Infinite.

Module Type DecidableInfiniteType := MiniDecidableType <+ Infinite.

Module Type MiniDecidableSet.
  Parameter t : Set.
  Parameter eq_dec : forall (x y : t), { x = y }+{ x <> y }.
End MiniDecidableSet.

Module Type DecidableInfiniteSet := MiniDecidableSet <+ Infinite.

Module Natural <: DecidableInfiniteSet.

  Definition t := nat.

  Lemma eq_dec : forall (x y : t), { x = y }+{ x <> y }.
  Proof. decide equality. Qed. 

  Program Definition infinite : infinite nat :=
    ((fun (n:nat)=>n),(fun (n:nat)=>n)).

End Natural.

(******************************************************)
(******************************************************)

(** Map *)

Set Implicit Arguments.

Module Map :=FMapList.Make(OrderedTypeEx.Nat_as_OT).

Module FMap := FMapFacts.WFacts_fun OrderedTypeEx.Nat_as_OT Map.
  
Section memAdd.
  
  Variable A : Type.
  
  Lemma memAdd : forall (i j : nat) m (v:A) ,
                   Map.mem i m = true ->
                   Map.mem i (Map.add j v m) = true.
  Proof.
    intros.
    rewrite FMap.add_b.
    auto with *.
  Qed.
  
End memAdd.

(** Others *)

Lemma value_elim : forall (A:Type) (x y :A), value x = value y -> x = y.
Proof.
  intros A x y H; injection H; auto.
Qed.

Hint Resolve value_elim : myresolve.

(*Lemma inBoundNth : 
  forall (A : Type) (l : list A) (i:nat) (v : A), 
    nth_error l i = Some v -> i < List.length l.
Proof.
  intros until l.
  induction l; intros.
  destruct i;
    discriminate.
  destruct i.
  apply Lt.lt_O_Sn.
  simpl.
  simpl in H.
  apply Lt.lt_n_S.
  eauto.
Qed.

Hint Resolve inBoundNth.*)

(*Definition filterOption (A B : Type) (f : A -> B) (e : option A) : option B :=
  match e with
    | None => None
    | Some x => Some (f x)
  end.*)

(*Implicit Arguments filterOption [A B].*)

(*Definition defined (A B : Type) (f : A -> option B) (x : A) :=
  exists y, f x ==  y. *)

  (* length *)

(*Ltac length_minus_nonEmpty s :=
  destruct s;[
    exfalso; eauto with projection |
    simpl;
      rewrite <- Minus.minus_n_O; intuition].

Hint Extern 2 (length ?s - 1 < length ?s) => length_minus_nonEmpty s.

   
  Implicit Arguments length_se_s [A].*)

(*  Lemma lt_le : forall x y, x < y -> x <= y.


  Lemma length_minus_one : forall (A: Type) (l : list A), length l - 1 <=  length l.


 Hint Resolve lt_le le_neq_lt length_minus_one length_se_s : arith.*)


