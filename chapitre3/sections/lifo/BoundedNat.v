(** A module of bounded naturals *)
Require Import Arith.
Require Import Mergesort.
Require Import sections.lifo.ProofEquality.

Set Implicit Arguments.

(** * The type of bounded naturals *)

Definition boundedNat (bound:nat):= { n:nat | n<bound }.

Program Definition buildBoundedNat (n bound:nat) (H:n<bound) :(boundedNat bound):= n.


(** projT1 is injective for bounded naturals. *)
(* TODO: Use the class "Injective" *)

(* Lemma projT1BoundedNatInjective:
  forall
   (bound:nat)(bn1 bn2 : boundedNat bound),
    projT1 bn1 = projT1 bn2 ->
    bn1 = bn2.
Proof.
  intros bound bn1 bn2 H.
  destruct bn1 ; destruct bn2 ; simpl in *.
  revert l l0 ; rewrite H ; intros l l0.
  rewrite ltUniquenessProof with (n:=x0)(m:=bound)(H1:=l)(H2:=l0).
  reflexivity.
Qed. *)

(* Lemma projT1BoundedNat : 
  forall (bound : nat) (bn1 bn2 : boundedNat bound), 
    bn1 = bn2 -> projT1 bn1 = projT1 bn2.
Proof.
intros.
rewrite H.
reflexivity.
Qed. *)

Lemma proj1_sigBoundedNatInjective:
  forall
    (bound:nat)(bn1 bn2 : boundedNat bound),
    proj1_sig bn1 = proj1_sig bn2 ->
    bn1 = bn2.
Proof.
  intros bound bn1 bn2 H.
  destruct bn1 ; destruct bn2 ; simpl in *.
  revert l l0 ; rewrite H ; intros l l0.
  rewrite ltUniquenessProof with (n:=x0)(m:=bound)(H1:=l)(H2:=l0).
  reflexivity.
Qed.

Lemma proj1_sigBoundedNat : 
  forall (bound : nat) (bn1 bn2 : boundedNat bound), 
    bn1 = bn2 -> proj1_sig bn1 = proj1_sig bn2.
Proof.
intros.
rewrite H.
reflexivity.
Qed.

(** Application of a function taking a boundedNat to a regular nat, with a default value *)

Program Definition applyUnbounded (A:Type)(m:nat)(default:A)(f: boundedNat m->A)(n:nat) : A := 
  match leb (S n) m with
    | true => f n
    | false => default
  end.
Next Obligation.
  destruct m; [discriminate | apply Nat.lt_succ_r; apply leb_complete; auto].
Qed.

(** Conversion of boundeNat. *)

Program Definition boundedNatConversion
  (b1 b2 : nat)(n1:boundedNat b1)(H:b1=b2) : 
  {n2:boundedNat b2 | proj1_sig n2 = proj1_sig n1} := 
  proj1_sig n1.
Next Obligation.
  destruct n1 ; auto.
Defined.
  
(* TODO: with a coersion ? *)

Lemma boundedNatConversionEq 
  (b1 b2 : nat)(n1:boundedNat b1)(H:b1=b2) : 
  proj1_sig(proj1_sig(boundedNatConversion n1 H)) = proj1_sig n1.
Proof.
  auto.
Qed.


