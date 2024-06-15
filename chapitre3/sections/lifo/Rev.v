Require Import List.
Require Import Nat.

Require Import sections.lifo.Nth.
Require Import sections.lifo.Length.

Generalizable All Variables.

Set Implicit Arguments.
(** nth element of rev l  *)
Lemma rev_nth'   `(lst : list A): 
  forall  n  (nrevlst :n < length (rev lst))  (nlst :(length lst - S n)< length lst), 
    nth' n (rev lst) nrevlst = nth' (length lst  - S n) lst nlst.
Proof.
  induction lst.
  simpl.
  intros n nrevlst nlst. contradict nlst. auto with arith.
  intros.  
  rewrite nth'_nth with (d:=a).
  rewrite nth'_nth with (d:=a).
  apply rev_nth.
  rewrite rev_length in nrevlst.
  assumption.
Qed. 



(** Equivalences rev rev' and tactics to automaticaly replace them each other  *)
Lemma rev'_rev : forall (A:Type)(l:list A), rev' l = rev l.
Proof.
  intros A l.
  unfold rev'; rewrite <- rev_alt; reflexivity.
Qed.


Lemma map_rev'_rev : forall (A:Type)(l:list (list A)), map (@rev' A) l = map (@rev A) l.
Proof.
  intros A l. apply (map_ext (@rev' A) (@rev A) (@rev'_rev A)).
Qed.

Ltac setoid_rev'_to_rev:=
  repeat (setoid_rewrite rev'_rev || setoid_rewrite map_rev'_rev).

Tactic Notation "rev'_to_rev" :=
  repeat (rewrite rev'_rev || rewrite map_rev'_rev). (* ;  repeat (setoid_rewrite rev'_rev || setoid_rewrite map_rev'_rev). *)

Tactic Notation "rev'_to_rev" "in" ident(H) :=
    repeat (rewrite rev'_rev in H || rewrite map_rev'_rev in H). (* ;repeat (setoid_rewrite rev'_rev in H || setoid_rewrite map_rev'_rev in H). *)


Tactic Notation "rev'_to_rev" "in" "*" :=
  match goal with
    | [ H : _ |- _] =>   rev'_to_rev in H
  end;
rev'_to_rev
.

Ltac rev_to_rev' :=
  repeat (rewrite <- rev'_rev || rewrite <- map_rev'_rev).

Ltac setoid_rev_to_rev' :=
  repeat (setoid_rewrite <- rev'_rev || setoid_rewrite <- map_rev'_rev)
.
Tactic Notation " rev_to_rev'" "in" ident(H) :=
  repeat (rewrite <- rev'_rev in H || rewrite <-  map_rev'_rev in H).
  (* repeat (setoid_rewrite <- rev'_rev in H || setoid_rewrite <-  map_rev'_rev in H). *)
    
Tactic Notation " rev_to_rev'" "in" "*":=
match goal with
    | [ H : _ |- _] => rev_to_rev' in H
end;
rev_to_rev'.
