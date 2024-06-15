Require Import Lt Peano_dec Compare_dec Relation_Operators.
Require Import List.
Require Import Lia.
Require Import sections.lifo.Length.

(*************************************************************************)
(*************************************************************************)

(** nth_error *)

Fact nth_error_nil_None : 
  forall (A : Type) (k : nat), 
    nth_error nil k = @None A.
Proof.
  destruct k; reflexivity.
Qed.

Arguments nth_error_nil_None [A] _.
Hint Resolve nth_error_nil_None : nth_error.
Hint Rewrite nth_error_nil_None : nth_error.

Fact nth_error_defined_lt :
  forall (A : Type) (l : list A) (k : nat),
    (exists y, nth_error l k = Some y) -> k < length l.
Proof.
  intros A; induction l; intros k H; destruct H as [x Hx].
  - destruct k; discriminate.
  - destruct k; simpl in *.
    + auto with *.
    + assert(k < length l) by (apply IHl; exists x; trivial).
      auto with *.
Qed.

Arguments nth_error_defined_lt [A l k]  _.
Hint Resolve nth_error_defined_lt : nth_error.

Fact nth_error_lt_defined :
  forall (A : Type) (l : list A) (k : nat),
    k < length l -> (exists y, nth_error l k = Some y).
Proof.
  intro A; induction l; intros k H.
  - contradict H. simpl.
    lia.
  - destruct k; simpl in *.
    + exists a. trivial.
    + apply IHl. auto with *.
Qed.
    
Arguments nth_error_lt_defined [A l k] _.
Hint Resolve nth_error_lt_defined : nth_error.

Fact nth_errorGeLength: 
  forall (A:Type) (l:list A)(k : nat),
    k >= length l -> nth_error l k = None.
Proof.
  intros A l k h_ge.
  case_eq (nth_error l k); intros; subst.
  - assert (k < length l) by eauto with nth_error.
    exfalso; lia.
  - reflexivity.
Qed.

Arguments nth_errorGeLength [A l k] _.

Fact nth_error_pointwise_equality :
  forall (A : Type) (l1 l2 : list A),
    (forall k, nth_error l1 k = nth_error l2 k) -> l1 = l2.
Proof.
  induction l1 as [ | a l1 IH].
  - intros l2 h_equality.
    destruct l2 as [ | a l2].
    + reflexivity.
    + exfalso; now assert (error = value a) by apply (h_equality 0).
  - intros l2 h_equality.
    destruct l2 as [ | b l2].
    + exfalso; now assert (value a = error) by apply (h_equality 0).
    + assert (a = b) by now injection (h_equality 0).
      assert (l1 = l2) by (apply IH; intro k; apply (h_equality (S k))).
      congruence.
Qed.

Arguments nth_error_pointwise_equality [A] _ _ _.
Hint Resolve nth_error_pointwise_equality : nth_error.

(*************************************************************************)
(*************************************************************************)

(** append *)

Hint Resolve List.app_assoc List.app_length : append.
Hint Rewrite -> List.app_assoc : append_left.
Hint Rewrite <- List.app_assoc : append_right.
Hint Rewrite -> List.app_length : append_down.
Hint Rewrite <- List.app_length : append_up.

Lemma append_nil_left_neutral :
  forall (A : Type) (l : list A),
    l ++ nil = l.
Proof.
  intros A l.
  induction l.
  - reflexivity.
  - simpl; rewrite IHl; reflexivity.
Qed.

Lemma append_nil_right_neutral :
  forall (A : Type) (l : list A),
    nil ++ l = l.
Proof.
  intros A l.
  reflexivity.
Qed.

Lemma append_nil_neq_cons_left :
  forall (A : Type) (l1 l2 : list A) (a : A),
    nil <> (a::l1) ++ l2.
Proof.
  discriminate.
Qed.

Lemma append_nil_neq_cons_right :
  forall (A : Type) (l1 l2 : list A) (a : A),
    nil <> l1 ++ (a::l2).
Proof.
  intros A l.
  destruct l; discriminate.
Qed.

Lemma nth_error_map :
  forall {A B : Type}(f:A->B)(l:list A)(n:nat)(d:A),
    (forall a b, f a = f b -> a = b) -> 
    nth_error (map f l) n = Some (f d) -> 
    nth_error l n = Some d.
Proof.
  induction l; intros n d Hf H.
  - destruct n; simpl in *; discriminate.
  - destruct n; simpl. simpl in H. inversion H.
    + assert(a = d) as Heq by now apply Hf.
      rewrite Heq. reflexivity.
    + simpl in H. 
      now apply IHl.
Qed.

Arguments append_nil_left_neutral [A] _.
Arguments append_nil_right_neutral [A] _.
Arguments append_nil_neq_cons_left [A] _ _ _ _.
Arguments append_nil_neq_cons_right [A] _ _ _ _.

Hint Rewrite append_nil_left_neutral append_nil_right_neutral : append.
Hint Resolve append_nil_left_neutral append_nil_right_neutral : append.
Hint Resolve append_nil_neq_cons_left append_nil_neq_cons_right : append.

(*************************************************************************)
(*************************************************************************)

(** nth composed with append *)

Lemma nth_error_append_left :
  forall (A : Type) (l1 l2 : list A) k,
    k < length l1 -> 
    nth_error (l1++l2) k = nth_error l1 k.
Proof.
  induction l1 as [ | a l1 IH].
  - intros l2 k h_lt; simpl in h_lt.
    exfalso; lia.
  - intros l2 k h_lt.
    destruct k as [ | k ].
    + reflexivity.
    + assert (k < length l1) by auto with *; now apply IH.
Qed.      

Arguments nth_error_append_left [A] _ _ _ _.

Hint Resolve nth_error_append_left : nth_error.

Lemma nth_error_append_right :
  forall (A : Type) (l1 l2 : list A) k,
    ~ (k < length l1) -> 
    nth_error (l1 ++ l2) k = nth_error l2 (k - (length l1)).
Proof.
  induction l1 as [ | a l1 IH].
  - intros l2 k h_nlt.
    now replace (k - length nil) with k by (destruct k; reflexivity).
  - intros l2 k h_nlt.
    destruct k as [ | k]; simpl in h_nlt.
    + exfalso; auto with *.
    + assert (~ k < length l1).
    contradict h_nlt.
    now apply Nat.succ_lt_mono in h_nlt.
      now apply IH.
Qed.

Arguments nth_error_append_right [A] _ _ _ _.

Hint Resolve nth_error_append_right : nth_error.

(*************************************************************************)
(*************************************************************************)

(** nth_error composed with append with occurences *)

Lemma nth_error_append_cons_eq :
  forall (A : Type) (l1 l2 : list A) (a: A),
    nth_error (l1 ++ a::l2) (length l1) = Some a.
Proof.
  intros A l1 l2 a.
  rewrite nth_error_append_right by lia.
  now replace (length l1 - length l1) with 0 by auto with *.
Qed.

Arguments nth_error_append_cons_eq [A] _ _ _.

Hint Rewrite nth_error_append_cons_eq : nth_error.

Lemma nth_error_append_cons_neq :
  forall (A : Type) (l1 l2 : list A) a k,
    k <> length l1 ->
    forall b, nth_error (l1++a::l2) k = nth_error (l1++b::l2) k.
Proof.
  intros A l1 l2 a k h_lt b.
  destruct (lt_dec k (length l1)).
  - now do 2 rewrite nth_error_append_left by intuition.
  - do 2 rewrite nth_error_append_right by intuition.
    destruct k.
    + elim n; auto with *.
    + admit. 
      (* rewrite <- minus_Sn_m by lia.
      reflexivity. *)
Admitted.

Arguments nth_error_append_cons_neq [A] _ _ _ _ _ _.

Hint Resolve nth_error_append_cons_neq : nth_error.

Lemma nth_error_append_cons_cons_eq1 :
  forall (A : Type) (l1 l2 l3 : list A) a b,
    nth_error (l1 ++ a::l2 ++ b :: l3) (length l1) = Some a.
Proof.
  intros A l1 l2 l3 a b.
  apply nth_error_append_cons_eq.
Qed.

Arguments nth_error_append_cons_cons_eq1 [A ] _ _ _ _ _.

Hint Resolve nth_error_append_cons_cons_eq1 : nth_error.
Hint Rewrite -> nth_error_append_cons_cons_eq1 : nth_error.

Lemma nth_error_append_cons_cons_eq2 :
  forall (A : Type) (l1 l2 l3 : list A) a b,
    nth_error (l1 ++ a::l2 ++ b :: l3) (length l1 + length l2 + 1) = Some b.
Proof.
  intros A l1 l2 l3 a b.
Admitted.
  (* rewrite nth_error_append_right by intuition.
  replace (length l1 + length l2 + 1 - length l1) with (length l2 + 1) by omega.
  replace (a::l2++b::l3) with ((a::l2)++b::l3) by reflexivity.
  rewrite nth_error_append_right by (simpl; omega).
  replace (length l2 + 1 - length (a:: l2)) with 0 by (simpl; omega).
  reflexivity.
Qed. *)

Arguments nth_error_append_cons_cons_eq2 [A] _ _ _ _ _.

Hint Resolve nth_error_append_cons_cons_eq2 : myresolve.
Hint Rewrite -> nth_error_append_cons_cons_eq2 : myrewrite.

Lemma nth_error_append_cons_cons_neq :
  forall (A : Type) (l1 l2 l3 : list A) a b k,
    k <> length l1 ->
    k <> length l1 + length l2 + 1 ->
    forall c d,
      nth_error (l1 ++ a::l2 ++ b :: l3) k = 
      nth_error (l1 ++ c ::l2 ++ d::l3) k.
Proof.
  intros A l1 l2 l3 a b k H H0 c d.
  replace (nth_error (l1 ++ (a::(l2 ++ (b :: l3)))) k)
  with (nth_error (l1 ++ (c::(l2 ++ (b :: l3)))) k)
    by now apply nth_error_append_cons_neq.
  autorewrite with append_right.
  replace (l1++c::l2++b::l3) with ((l1++c::l2)++b::l3) by now autorewrite with append_right.
  replace (l1++c::l2++d::l3) with ((l1++c::l2)++d::l3) by now autorewrite with append_right.
 Admitted. 
  (* replace (length l1 + length l2 + 1) with (length (l1 ++ c::l2)) 
    in H0 by (autorewrite with length; simpl; intuition).
  replace (nth_error ((l1++c::l2)++b::l3) k)
  with (nth_error ((l1++c::l2)++d::l3) k). 
  reflexivity.
  eauto with nth_error.
Qed. *)

Arguments nth_error_append_cons_cons_neq [A] _ _ _ _ _ _ _ _ _ _.

Hint Resolve nth_error_append_cons_cons_neq : nth_error.

Lemma nth_error_append_cons_nil_neq : 
  forall (A : Type) (l : list A) k a a',
    nth_error (l ++ a::nil) k = Some a' ->
    a <> a' ->
    nth_error l k = Some a'.
Proof.
  intro A; induction l as [ | x xs IH ]; intros k a a' Hnth Hdiff.
  - destruct k; simpl in *.
    + inversion Hnth. contradict Hdiff. trivial.
    + destruct k; discriminate.
  - destruct k; simpl in *.
    + trivial.
    + eauto using IH.
Qed.

Hint Resolve nth_error_append_cons_nil_neq : nth_error.

(*************************************************************************)
(*************************************************************************)
(** List decomposition *)

Lemma split_around :
  forall (A : Type) (l : list A) (k : nat),
    k < length l ->
    exists a l1 l2,
      k = length l1 /\ l = l1 ++ a:: l2.
Proof.      
  induction l as [ | a l h_ind].
  - intros k h_lt_k_l.
    exfalso; apply (Nat.nlt_0_r k h_lt_k_l).
  - intros k h_lt_Sk_al.
    destruct k.
    + (exists a, nil, l); intuition.
    + assert (k < length l) as h_lt_k_l by auto with *.
      destruct (h_ind k h_lt_k_l) as [b [l1 [l2 [h_l1 h_l]]]].
      (exists b, (a::l1), l2).
      simpl; intuition congruence.
Qed.

Arguments split_around [A]  _ _ _.

(** split a list around two positions *)

Lemma split_between :
  forall (A : Type) (l : list A) (k1 : nat) (k2 : nat),
    k1 < k2 -> k2 < length l ->
    exists a b l1 l2 l3,
      k1 = length l1 /\
      k2 = length l1 + length l2 + 1 /\
      l = l1 ++ a::l2 ++ b::l3.
Proof.
  intros A l k1 k2 h_lt_k1_k2 h_lt_k2_l.
  destruct (split_around l k2 h_lt_k2_l) as [b [l1 [l2 [h_size1 h_split1]]]].
  assert (k1 < length l1) as h_lt_k1_l1 by congruence.
  destruct (split_around l1 k1 h_lt_k1_l1) as [a [l3 [l4 [h_size3 h_split2]]]].
  exists a, b, l3, l4, l2.
  split; [assumption |split].
  - replace (length l3 + length l4 + 1) with (length l1).
    congruence.
    rewrite h_split2.
    admit.
    (* now replace (length (l3 ++ a :: l4)) with (length l3 + length l4 + 1) 
    by (rewrite app_length; simpl; intuition). *)
  - rewrite h_split1.
    rewrite h_split2.
    now replace ((l3++a::l4)++b::l2) with (l3++a::l4++b::l2) 
      by (rewrite <- app_assoc; reflexivity).
 Admitted.

(* In *)

Lemma in_neq : 
  forall (A : Type) (l:list A) (e e' : A), In e (e'::l) -> e <> e' -> In e l.
Proof.
  intros A l e e' H H0;
    destruct H as [H | H'];
    [ contradict H0 | idtac ]; auto.
Qed.


Arguments in_neq [A l e e'].

(* NoDup *)

Lemma noDupConcat : forall (A:Type) ( l' l : list A),
                      NoDup (l++l') ->
                      NoDup l /\ NoDup l'.
Proof.
  induction l'.
  - intros l H.
    rewrite app_nil_r in H.
    split;auto.
    constructor.  
  - intros l H.
    assert (NoDup l /\ NoDup l')as Hll' by (apply IHl';apply NoDup_remove_1 with (a:=a);auto).
    destruct Hll' as [Hl Hl'].
    split.
    + assumption. 
    + constructor.
      * assert (~In a (l++l')) as Hninll' by (apply NoDup_remove_2;auto).
        rewrite in_app_iff in Hninll'.
        auto.
      * assumption.  
Qed.

Import ListNotations.

Generalizable All Variables.

Fixpoint lastSome `(l:list A) : option A := 
  match l with 
    | []    => None
    | [x]   => Some x 
    | x::xs => lastSome xs
  end.

Lemma lastSomeAppCons:
  forall `(xs:list A)(a:A),
    lastSome(xs++[a]) = Some a.
Proof.
  intros A; induction xs as [|x xs IH]; intros.
  - trivial.
  - simpl; rewrite IH; destruct xs; trivial.
Qed.


Lemma nth_error_app_hd : 
  forall (A : Type) (a : A) (s1 s2 : list A), 
    nth_error (s1 ++ a::s2) (length s1) = Some a.
Proof.
  induction s1; intro s2; simpl; auto.
Qed.

Lemma nth_error_lt : 
forall (A : Type) (s : list A) (i : nat) (x : A),
nth_error s i = Some x -> i < length s.
Proof.
induction s.
- intros i x H_Eq.
  destruct i; simpl in H_Eq; discriminate.
- intros i x H_Eq.
  destruct i; simpl.
  + lia.
  + simpl in H_Eq.
    assert (i < length s) by eauto.
    lia.
Qed.
