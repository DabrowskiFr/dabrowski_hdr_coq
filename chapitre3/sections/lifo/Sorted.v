Require Import Coq.Lists.List.
Require Import Arith.
Require Import Coq.Sorting.PermutEq.
Require Import Coq.Sorting.Sorting.
Require Import Relation_Definitions.
Require Import Coq.Sorting.Permutation.
Require Import Setoid.
Require Import Coq.Sorting.PermutSetoid.
Require Import sections.lifo.InsertSorting.
Require Import sections.lifo.InSig.
Require Import sections.lifo.Nth.
Require Import sections.lifo.SeqNat.
Require Import sections.lifo.Map.
Require Import sections.lifo.BoundedNat.
Require Import sections.lifo.AlgebraClasses.
Require Import sections.lifo.AlgebraInstances.

Set Implicit Arguments.

Section Bijectivity.
Set Asymmetric Patterns.
  
Definition injective (A B: Type) (f:A->B) :=
 forall (x y : A), f x = f y -> x = y.

Definition surjective (A B : Type) (f:A->B) :=
 forall (y:B), exists x:A, f x = y.

Definition bijective (A B: Type) (f:A->B) :=
 injective f /\ surjective f.

(** 
  Every a of A is in l -> the same in (map f l) if f is surjective
*)
Lemma inMapSurj : forall (A : Type) (l : list A) (f:A -> A) (H : surjective f), 
    (forall a, In a l) -> forall a, In a (map f l).
Proof.
intros.
assert (exists x, f x = a). apply H.
destruct H1 as (x, Hx).
assert (In x l). apply H0.
rewrite <- Hx.
apply in_map.
apply H1.
Qed.

(**
  Reverse of the precedent one with injective function
*)
Lemma inMapInj : forall (A B : Type) l (a : A) f (H : @injective A B f), In (f a) (map f l) -> In a l.
Proof.
induction l ; intros.
 destruct H0.
 simpl in *.
 unfold injective in H.
 destruct H0.
 left. apply H. assumption.
 right. apply (IHl a0 f). unfold injective. apply H.
 apply H0.
Qed.


Lemma inSurj : forall (A B : Type)
  (l: list A) (f:A->B) (H : surjective f) (a:A),
    (forall a, In a l) -> forall b, (In b (map f l)).
Proof.
intros.
assert (exists a1, f a1 = b). apply H.
destruct H1 as (a1, H2).
destruct (in_split a1 l (H0 a1)) as [l1 [l2 Hl1l2]].
rewrite Hl1l2. rewrite map_app. simpl.
rewrite H2.
intuition.
Qed.

End Bijectivity.

Section NoDup.

(**
  Injectivity conserves NoDup
*)
Lemma noDupInj : forall (A B : Type) l f (H: @injective A B f), 
 NoDup l -> NoDup (map f l).
Proof.
intros.
assert (length l = length (map f l)). rewrite map_length. reflexivity.
induction l.
 constructor.
 simpl map. inversion H0.
 constructor. intros SH. apply H4. apply inMapInj with B f ; intuition. 
 apply IHl. apply H5. intuition.
Qed.

(**
  Mapped function conserves NoDup
*)
Lemma noDupFun : forall (A B : Type) l (f : A -> B), 
 NoDup (map f l) -> NoDup l.
Proof.
intros.
assert (length l = length (map f l)). rewrite map_length. reflexivity.
induction l.
 constructor.
 simpl map in *. inversion H.
 constructor. intros SH. apply H3. apply in_map. apply SH. 
 apply IHl. apply H4. intuition.
Qed.

(**
  Seq has no duplication
*)
Lemma noDupSeq : forall len start, NoDup (seq start len).
Proof.
induction len.
 constructor.
 constructor. 
 intro H. apply inSeqLe in H. intuition.
 apply IHlen.
Qed.

Lemma inMapNoDupEqual : forall (A B : Type) L (a : A*B) p, fst a = fst p ->
  NoDup (map (@fst A B) (p::L)) -> In a (p::L) -> a = p.
Proof.
induction L ; intros.
 simpl in *. destruct H1 ; intuition.
 apply IHL ; intuition. inversion H0.
 inversion H5. constructor. intuition. intuition.
 inversion H1. subst ; intuition. destruct H2. simpl in * ; subst.
 rewrite H in H0. inversion H0. destruct H4. intuition.
 right. apply H2.
Qed.

Lemma inMapNoDupEqual1 : forall (A B : Type) L (a : A*B) n, In a L -> 
  NoDup (map (@fst A B) L) -> (forall c, fst a = nth n (map (@fst A B) L) (@fst A B c)) -> 
    (forall a0 : A*B, exists b, fst a0 <> @fst A B b) -> (forall c, a = nth n L c).
Proof.
induction L ; intros.
 destruct H.
 destruct n.
  simpl in *.
  destruct H. 
   subst. reflexivity.
   apply inMapNoDupEqual with L. apply H1 ; apply c. simpl ; apply H0. right. apply H.
   simpl in *.
   destruct H. subst.
   destruct (H2 a0) as (b, H7).
   generalize (H1 b). intros. inversion H0 ; subst. destruct H5.
   destruct (nth_in_or_default n (map (@fst A B) L) (fst b)). rewrite H. intuition.
   rewrite <- H in e. destruct H7. apply e.
   apply IHL. apply H.
   inversion H0 ; assumption.
   apply H1.
   apply H2.
Qed.

(**
  NoDup insig l -> NoDup l
*)
Lemma inSigNoDup : forall m (l : list (boundedNat m)),
    NoDup (map (proj1_sig (P:=(fun n=>lt n m))) l) -> NoDup l.
Proof.
  intro m;  induction l as [ | x xs IH]; intro H.
  - constructor.
  - constructor; simpl in *; inversion H; subst.
    + match goal with
          [ H': not _ |- _ ] => 
          contradict H'; destruct x; now apply in_map
      end.
    + now apply IH.
Qed. 

(**
  NoDup l -> NoDup insig l
*)
Lemma noDupInSig : forall (m:nat) l (P:= fun x => x < m) H2,
  NoDup l -> NoDup (inSig P l H2).
Proof.
induction l ; intros.
 constructor.
 simpl. inversion H.
 constructor. intro H6.
 apply H3.
 apply inInSig in H6. simpl in H6. 
 assumption.
 apply IHl.
 apply H4.
Qed.

(**
  NoDup insig seq
*)
Lemma nodupInSigSeq : forall m, 
  NoDup (inSig (fun i : nat => i < m) (seq 0 m) (inSeq0Lt m)).
Proof.
intros. 
apply (noDupInSig (inSeq0Lt m)).
apply noDupSeq.
Qed.


End NoDup.

Section Permutation.

Lemma Permutation_app_inv1 : forall A (a b c : list A), Permutation (a ++ b ++ c) (c ++ b ++ a).
Proof.
  induction a; intros.
  - rewrite app_nil_r. rewrite app_nil_l. apply Permutation_app_comm.
  - simpl; rewrite IHa.
    eapply Permutation_trans with ((a :: a0 ++ b ++ c)).
    now apply Permutation_cons.
    replace (c ++ b ++ a :: a0) with ((c ++ b) ++ a :: a0).
    apply Permutation_cons_app. rewrite <- app_assoc. apply IHa.
    now rewrite app_assoc. 
Qed.


(** 
 Problems of type in rewrite lead to this kind of lemma
*)
Lemma permutationEq : forall (A : Type) (l1 l2 : list A), l1 = l2 -> Permutation l1 l2.
Proof.
intros A0 l1 l2 H.
rewrite H.
apply Permutation_refl.
Qed.

(**
  nth l1 = a -> Permutation l1 l2 -> a in l2
*)
Lemma permutation_nth_in : forall (A:Type) (eqA_dec : forall a b : A, {a=b} + {~a = b}) l1 l2,
  Permutation l1 l2 -> forall n (c : A), l2 <> nil -> n < length l1 -> In (nth n l1 c) l2.
Proof.
induction l1 ; intros.
 destruct H0 ; apply Permutation_nil in H ; intuition.
 destruct l2.
  destruct H0 ; reflexivity.
  apply Permutation_in with (a::l1) ; intuition.
  apply nth_In ; intuition.
Qed.

(**
  Bijectivity with noDup conserve Permutation
*)
Lemma permutationBij : forall (A : Type) (l: list A) (f:A->A) (H : bijective f), NoDup l ->
   (forall a, In a l) -> Permutation l (map f l).
Proof.
intros.
assert (H3 : surjective f). apply H.
generalize (inMapSurj l H3 H1). intros H2. apply NoDup_Permutation.
 apply H0.  destruct H. apply noDupInj ; intuition. intuition.
Qed.


Lemma permutationConsInv : forall (A : Type) l1 l2 (a : A), Permutation (a::l1) (a::l2) -> Permutation l1 l2.
Proof.
intros.
 assert (Permutation (rev (a::l1)) (rev (a::l2))).
 apply Permutation_trans with (a::l1). 
  apply Permutation_sym. apply Permutation_rev.
  apply Permutation_trans with (a::l2).
   assumption.
   apply Permutation_rev.
simpl in H0.
apply Permutation_trans with (rev l1).
 apply Permutation_rev.
 apply Permutation_trans with (rev l2) ; [ | apply Permutation_sym ; apply Permutation_rev].
 replace (rev l1) with ((rev l1) ++ nil) by intuition.
 replace (rev l2) with ((rev l2) ++ nil) by intuition.
 apply Permutation_app_inv with a.
 assumption.
Qed.

(**
  Permutation conserves NoDup
*)
Lemma permutationNoDup : forall (A : Type) (l1 l2 : list A),
  Permutation l1 l2 -> NoDup l1 -> NoDup l2.
Proof.
intros A l1 l2 H1 H2.
induction H1.
 constructor.
 constructor. inversion H2. intro. 
 destruct H3. apply Permutation_in with l'. apply Permutation_sym ; apply H1.
 apply H5.
 inversion H2.
 apply IHPermutation ; intuition.
 constructor. intro H ; inversion H2 ; inversion H4 ; subst.
 destruct H ; intuition.
 apply H3 ; subst ; intuition.
 inversion H2 ; inversion H3 ; subst ; constructor ; intuition.
 apply IHPermutation2. apply IHPermutation1. apply H2.
Qed.


End Permutation.

Section Sorted.

(**
  if x is in (a::l) sorted then a < x 
*)
Lemma sortedCons : forall (A : Type) (leA0 : A -> A -> Prop) (leA0_trans : forall x y z, leA0 x y -> leA0 y z -> leA0 x z)
(eqA0_dec : forall a b : A, {a = b} + {~ a = b}) l x a, 
  Sorted leA0 (a :: l) -> In x l -> leA0 a x.
Proof.
intros.
induction l.
 inversion H0.
 destruct (eqA0_dec x a0).
  rewrite e. inversion H. inversion H4. assumption.
  apply IHl. 
   inversion H. inversion H4. inversion H3.
   constructor.
    assumption.
    destruct l ; constructor. inversion H11. eapply leA0_trans. apply H6. assumption.
  inversion H0. 
  destruct n. symmetry. apply H1.
   assumption.
Qed.

(**
  l and l' sorted with same elements -> l = l'
*)
Lemma sortedPermutationEq: forall (A : Type) (leA0 : A -> A -> Prop)(leA0_trans : forall x y z, leA0 x y -> leA0 y z -> leA0 x z)
(eqA0_dec : forall a b : A, {a = b} + {~ a = b}) (leA_refl : forall a b, leA0 a b -> leA0 b a -> a = b) l1 l2, 
  Sorted leA0 l1 -> Sorted leA0 l2 -> Permutation l1 l2 -> l1 = l2.
Proof.
intros A0 leA0 leA0_trans eqA0_dec leA0_eq_refl l1.
induction l1 ; intros l2 Hsort1 Hsort2 Hperm.
 apply Permutation_nil in Hperm.
 symmetry. apply Hperm.
 destruct l2. 
  apply Permutation_sym in Hperm. apply Permutation_nil in Hperm.
  inversion Hperm.
  inversion Hsort1 ; inversion Hsort2. subst.
  destruct (eqA0_dec a a0).
   rewrite e in *.
   rewrite (IHl1 l2). reflexivity.
    assumption. assumption. apply Permutation_cons_inv with a0.  assumption. 
   assert (H10 : In a (a0 :: l2)). apply Permutation_in with (a::l1) ; intuition.
   assert (H11 : In a l2).
    inversion H10. destruct n ; symmetry ; apply H. intuition.
   assert (H12 : In a0 (a :: l1)). apply Permutation_in with (a0::l2) ; intuition.
   assert (H13 : In a0 l1).
    inversion H12. destruct n ; apply H. intuition.
   assert (leA0 a a0).
    apply sortedCons with A0 l1. apply leA0_trans. apply eqA0_dec. apply Hsort1. apply H13.
   assert (leA0 a0 a).
    apply sortedCons with A0 l2. apply leA0_trans. apply eqA0_dec. apply Hsort2. apply H11.
   destruct n. apply leA0_eq_refl ; assumption.
Qed.

(* Almost the same as Sorted_cons with naturals *)
Lemma sortedInLe : forall l a, Sorted le (a::l) -> (forall b, In b l -> a <= b).
Proof.
intros.
induction l.
 inversion H0.
 destruct (eq_nat_dec a0 b).
  eapply le_trans. inversion H. inversion H4. apply H6. intuition.
  apply IHl. inversion H ; inversion H3 ; inversion H4 ; subst. constructor. assumption.
  destruct l ; constructor ; inversion H8 ; subst ; eapply le_trans with a0 ; intuition.
  inversion H0 ; intuition.
Qed.

(*
HdRel with concatenation
*)
Lemma HdRel_app : forall (A : Type) (leA : A -> A -> Prop) l1 l2 a, HdRel leA a l1 -> 
  HdRel leA a l2 -> HdRel leA a (l1 ++ l2).
Proof.
intros.
induction l1. rewrite app_nil_l. apply H0.
constructor. inversion H. assumption.
Qed.

(*
Sorted with concatenation
*)
Lemma Sorted_app : forall (A : Type) (leA : A -> A -> Prop) l1 l2, 
  Sorted leA l1 -> Sorted leA l2 -> (forall x, In x l1 -> leA x (hd x l2))->Sorted leA (l1 ++ l2).
Proof.
induction l1 ; intros. 
rewrite app_nil_l. assumption.
constructor.
apply IHl1. inversion H. assumption. assumption.
intros. intuition.
inversion H.
apply HdRel_app. intuition. destruct l2. constructor.
constructor. simpl in H1.
generalize (H1 a) ; intros. subst. assert (a = a) by reflexivity. intuition.
Qed.



End Sorted.

Section lenA.
Variable A:Type.

(**
  New order lenA (nat, A).
*)
Definition lenA (m:nat)(e1 e2:((boundedNat m)*A)) :=
 le (proj1_sig(fst e1)) (proj1_sig(fst e2)).

Definition eqnA (m:nat) (e1 e2 : (boundedNat m*A)): Prop :=
  eq (proj1_sig (fst e1)) (proj1_sig (fst e2)).

(** 
 Decidability on le which is computable
*)
Definition le_dec1 : forall n m, {n <= m} + {m <= n}.
Proof.
induction n.
left. intuition.
destruct m. right. intuition.
destruct (IHn m).
left ; intuition.
right ; intuition.
Defined.

Lemma lenADec:
 forall  (m:nat)(a b : boundedNat m*A), {lenA a b} + {lenA b a}.
Proof.
 intros m a b.
 destruct a as [na a].
 destruct b as [nb b].
 set(H:=le_dec1 (proj1_sig na) (proj1_sig nb)).
 unfold lenA; simpl.
 intuition.
Defined.

Lemma eqnADec :
 forall (m:nat)(a b : boundedNat m*A), {eqnA a b} + {~eqnA  a b}.
Proof.
 intros m a b.
 destruct a as [na a].
 destruct b as [nb b].
 set(H:=eq_nat_dec (proj1_sig na) (proj1_sig nb)).
 unfold eqnA; simpl.
 intuition.
Qed.

Program Instance SortNatA (m:nat) :
  Sortable (@eqnA m) (@lenA m) (@eqnADec m) (@lenADec m).
Next Obligation.
  constructor; intuition.
  unfold eqnA, Transitive. intros. eapply eq_trans ; intuition.
Qed.
Next Obligation.
intros x.
constructor.
Qed.
Next Obligation.
unfold transitive.
intros x y z H1 H2.
unfold lenA in *. intuition.
Qed.
Next Obligation.
unfold eqnA, lenA in *.
intuition.
Qed.
Next Obligation.
unfold eqnA, lenA in *.
intuition.
Qed.


Lemma sortedLeLenA : forall l l1 m H, Sorted le l -> 
  Sorted (@lenA m) (@combine (boundedNat m) A (inSig _ l H) l1).
Proof.
induction l ; intros.
 constructor.
 inversion H0 ; subst.
 
 simpl inSig. simpl combine.
 destruct l1. constructor.
  constructor.
  apply IHl.
  apply H3.
  destruct l.
   constructor.
   simpl. destruct l1.
   constructor.
   simpl. constructor.
   unfold lenA. simpl.
   inversion H4. assumption.
Qed.

Lemma sortedLenALe : forall m l, Sorted (@lenA m) l -> Sorted le (map (fun n:boundedNat m * A => proj1_sig (fst n)) l).
Proof.
  induction l.
    simpl in *. constructor.
    simpl. constructor. apply IHl. inversion H. assumption.
    inversion H. destruct H3. simpl. constructor.
    simpl. constructor. apply H3.
Qed.

End lenA.


(*
*** Local Variables:
*** coq-load-path: (("../../LIFO" "LIFO"))
*** End:
*)