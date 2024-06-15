Require Import List.
Require Import Arith.
Require Import sections.lifo.Misc.
Require Import sections.lifo.Length.
Require Import sections.lifo.BoundedNat.
Require Import sections.lifo.ProofEquality.
Require Import Lia.
Set Implicit Arguments.

(** [inSig] builds, from a list of elements with type [A] and a proof
   that each element of the list has a property [P], a list of type
   [{a:A | P a}] *)
Program Fixpoint inSig 
  (A : Type) (P:A->Prop) (l:list A) (H:forall a, In a l -> P a) :
  (list (sig P)) := 
  match l with
    | nil => nil 
    | t :: q => t :: (inSig P q _)
  end.
Next Obligation.
  apply H.
  simpl. left. reflexivity.
Defined.
Next Obligation.
  apply H.
  auto with *.
Defined.

(** [inSig] preserves the length of the list *)
Lemma inSigLength : 
  forall  (A: Type) (P : A -> Prop) l H,  
    length (inSig  P l H) = length l.
Proof.
  induction l.
  reflexivity.
  intros; simpl;
    rewrite IHl.
  reflexivity.
Qed.
Hint Rewrite inSigLength: length.


(** By removing the proofs associated to elements in a list built with
   [inSig], we obtain the original list. *)
Lemma inSigProj :
  forall (A:Type) (P:A->Prop) l H,
    listProj (inSig P l H) = l.
Proof.
  intros A P l H.
  induction l;[idtac | simpl;rewrite IHl]; reflexivity.
Qed.

Lemma inSigMapProj1Sig :
  forall (A:Type) (P:A->Prop) l H,
    List.map (@proj1_sig A P)(inSig P l H) = l.
Proof.
  intros A P l H.
  induction l;[idtac | simpl;rewrite IHl]; reflexivity.
Qed.

(** [inSigInv] builds from a list of type {a:A| P a}, a list together
   with a proof that for each element of the list, the property P
   holds. *)
Program Fixpoint inSigInv (A:Type) (P:A->Prop)(l:list (sig P)):
 {l:list A | forall a:A, In a l -> P a} :=
  match l with
   | nil => nil
   | t :: q => let (a, P) := t in a :: (inSigInv q) 
  end.
Next Obligation.
  destruct H.
Defined.
Next Obligation.
  destruct H as [H|H].
  rewrite <- H. 
  exact P.
  apply p. 
  exact H.
Defined.

Hint Rewrite inSigLength : length.

Lemma inInSig : 
  forall A (l:list A) P H x, 
    In x (inSig P l H) ->
    In (proj1_sig x) l.
Proof.
  intros A l P H x H0.
  apply in_map with (f:=(@proj1_sig A P))(B:=A) in H0.
  rewrite inSigMapProj1Sig with (P:=P) (l:=l) (H:=H) in H0.
  assumption.
Qed.

(* This lemma is the same as the one above but it can be more easy to use 
in some particular cases *)
Lemma inInSig1 : forall (m:nat) l (P:= fun x => x < m) (a : nat) (H : P a) H2,
  In a l -> In (exist (fun x => P x) a H) (inSig P l H2).
Proof.
Admitted.
(* induction l ; intros.
 destruct H0.
 simpl. destruct H0.
 left. apply projT1BoundedNatInjective. intuition.
 right. apply IHl. apply H0.
Qed. *)

Lemma nthInSigPI : forall m l n d x (P:= fun x => x < m) H H1 H2, 
  nth n l d = x -> nth n (inSig P l H) (exist P d H2) = exist P x H1.
Proof.
induction l ; intros.
 simpl in H0. destruct n ; simpl ; unfold P in H1, H2 ; subst ; 
 replace H1 with H2 by (apply ltUniquenessProof ; intuition) ; reflexivity.
 simpl inSig. destruct n.
 simpl. simpl in H0. subst.
 unfold P. replace (H x (or_introl (In x l) (eq_refl x))) with H1.
 intuition. apply ltUniquenessProof.
 simpl. simpl in H0.
 unfold P. 
 rewrite <- (IHl n d x (inSig_obligation_2 P H (eq_refl (a :: l))) H1 H2).
 unfold P. intuition. apply H0.
Qed.

(*
Proof irrelevance for insig and boundednat
*)
Lemma inSigPI : forall m l1 (P := fun x => x < m) H1 H2, inSig P l1 H1 = inSig P l1 H2.
Proof.
Admitted.
(* induction l1 ; intros.
simpl. reflexivity.
simpl. assert (inSig P l1 (inSig_obligation_2 P H1 (@eq_refl _ (a :: l1))) = inSig P l1 (inSig_obligation_2 P H2 (@eq_refl _ (a::l1)))).
apply IHl1. rewrite H. 
replace (H2 a (or_introl (In a l1) (eq_refl a))) with (H1 a (or_introl (In a l1) (eq_refl a)))  by (apply ltUniquenessProof).
reflexivity.
Qed. *)


(*
Concatenation of two boundednat list (with inSig)
*)
Lemma inSig_app : forall m (P := fun x => x < m) l1 l2 H1 H2 H3, inSig P l1 H1 ++ inSig P l2 H2 = inSig P (l1 ++ l2) H3.
Proof.
Admitted.

(* induction l1 ; intros. simpl. simpl in *.
apply inSigPI.
simpl. replace ((H1 a (or_introl (In a l1) (eq_refl a)))) with ((H3 a (or_introl (In a (l1 ++ l2)) (eq_refl a)))). 
2 : apply ltUniquenessProof. assert (H4 :forall a : nat, In a (l1 ++ l2) -> P a). intuition.
apply H3. simpl. right. trivial. 
assert (H5 : forall a : nat, In a l1 -> P a). intuition. 
assert (H6 : forall a : nat, In a l2 -> P a) by intuition.
replace (inSig P l1 (inSig_obligation_2 P H1 (eq_refl (a :: l1)))) with (inSig P l1 H5).
2 : apply inSigPI. rewrite (IHl1 l2 H5 H2 H4).
assert (inSig P (l1 ++ l2) H4 = inSig P (l1 ++ l2) (inSig_obligation_2 P H3 (eq_refl _))).
 apply inSigPI.
rewrite H. reflexivity.
Qed. *)


(*
Equality of two inSig
*)
Lemma inSig_eq : forall m (P := fun x => x < m) l1 l2 H1 H2, 
  l1 = l2 -> inSig P l1 H1 = inSig P l2 H2.
Proof.
intros.
subst.
apply inSigPI.
Qed.


Lemma firstnInSig : forall n m (P := fun x => x < m)  l1  H1 H2, 
  n < length l1-> 
  firstn n (inSig P l1 H1) = inSig P (firstn n l1) H2.
intros n m P l1 H1 H2 H.
elim (Firstn_skipn.firstn_app l1 H).
intros x H0.  destruct H0 as[l2 [l1_dec [lenl H0] ]].
revert H1 H2.
rewrite <- l1_dec.
rewrite Firstn_skipn.firstn_app_length.
intros H1 H2.
assert (H2' : forall  a : nat, In a l2 -> P a).
intros a H3.
apply H1.
apply in_app_iff.
right ; assumption.
rewrite <- (inSig_app  x l2 H2 H2' ).
rewrite Firstn_skipn.firstn_app_length.
f_equal.
autorewrite with length.
symmetry; assumption.
symmetry; assumption.
Qed.

Lemma skipnInSig : forall n m (P := fun x => x < m)  l1  H1 H2, 
  skipn n (inSig P l1 H1) = inSig P (skipn n l1) H2.
intros n m P l1 H1 H2.
destruct ((gt_dec (length l1) n)) as [H | H].

elim (Firstn_skipn.firstn_app l1 H).
intros x H0.  
destruct H0 as[l2 [l1_dec [lenl H0] ]].
revert H1 H2.
rewrite <- l1_dec.
rewrite Firstn_skipn.skipn_app_length.
intros H1 H2.
assert (H2' : forall  a : nat, In a x -> P a).
intros a H3.
apply H1.
apply in_app_iff.
left ; assumption.
rewrite <- (inSig_app  x l2 H2' H2).
rewrite Firstn_skipn.skipn_app_length.
f_equal.
autorewrite with length.
symmetry; assumption.
symmetry; assumption.
assert (length  ( skipn n (inSig P l1 H1) )= 0).
autorewrite with length.
lia.
rewrite (lengthNil); auto.
rewrite (lengthNil _ H0); auto.
autorewrite with length.
lia.
Qed.  
(*  *)