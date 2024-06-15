Require Import List. 
Require Import sections.lifo.Length.
Require Import sections.lifo.App. 
Require Import sections.lifo.ListBasics.
Require Import sections.lifo.Prelude.

(************************************************************)
(************************************************************)

(** Events *)

Module Type EventType.
  Parameter t : Set.
  Parameter eq_dec : forall x y : t, {x=y}+{x<>y}.
End EventType.

(************************************************************)
(************************************************************)

(** Traces *)
 
Module Trace (E : EventType).

  (** Definitions *)
  
  Notation "A • B" := (A++B::nil) (at level 40).

  Notation Tr := (list E.t).
  
  (*Definition Tr : Set  := (list E.t).*)
  
  Notation pi i s := (nth_error s i).

  (** Induction principles *)

  Lemma tr_ind : 
    forall (P : Tr -> Prop),
      (P nil) ->
      (forall (e : E.t) (s : Tr), P s -> P (s • e)) ->
      forall s : Tr, P s.
  Proof.
    apply rev_ind.
  Defined.

  Lemma tr_ind_length  : 
    forall P : Tr -> Prop,
      (forall s, (forall s', length s' < length s -> P s') -> P s) ->
      forall s : Tr, P s.
  Proof.
    set(R:= fun (l1 l2:Tr)=>lt(length l1)(length l2)).
    intros P H s.
    apply Fix with (R:=R).
    - apply Wf_nat.well_founded_lt_compat with (f:=@length E.t).
      intros x y H'; trivial.
    - assumption.
  Qed.
  
  Lemma tr_case : 
    forall (s : Tr), s = nil \/ exists (s' : Tr) (e : E.t), s = s' • e.
  Proof.
    induction s using tr_ind; eauto.
  Qed.
  
  Ltac tr_case s :=
    let s' := fresh "s" in 
      let e := fresh "e" in 
        let Ha := fresh in 
          let Hb := fresh in
            (destruct (tr_case s) as [ Ha | [ s' [e Hb]]]; 
             [rewrite Ha in * ; clear Ha | rewrite Hb in *; clear Hb]).

  (** Projection defined *)

  Hint Resolve lift_fst_inv lift_snd_inv lift_fst_snd lift_snd_fst lift_pair_surjective : proj.

  (** Injection *)

  Lemma dotInjective: 
    forall{A:Type}{l1 l2:list A}{a1 a2: A}, 
      l1 • a1 = l2 • a2 -> 
      l1 = l2 /\ a1 = a2.
  Proof.
    intros A l1; induction l1; intros l2 a1 a2 Heq.
    - destruct l2 as [ | x2 xs2].
      + repeat rewrite app_nil_l in Heq; inversion Heq; split; trivial.
      + rewrite app_nil_l,  <- app_comm_cons in Heq. 
        inversion Heq. apply app_cons_not_nil in H1. elim H1.
    - destruct l2 as [ | x2 xs2].
      + inversion Heq.
        symmetry in H1.
        apply app_cons_not_nil in H1.
        elim H1.
      + repeat rewrite <- app_comm_cons in Heq.
        inversion Heq.
        specialize (IHl1 xs2 a1 a2 H1). destruct IHl1.
        split; f_equal; trivial.
  Qed.


  Global Ltac inverseDot :=
    match goal with 
      | [ H : ?s • ?e = ?s' • ?e' |- _ ] => 
          apply dotInjective in H; 
          let H1 := fresh H in
            let H2 := fresh H in
              destruct H as [ H1 H2 ]; safe_subst
      | [ H : ?s • ?e = ?e' :: nil |- _ ] =>
          replace (e'::nil) with (nil • e') in H by trivial;
          inverseDot  
      | [ H : ?e' :: nil = ?s • ?e |- _ ] =>
          symmetry in H; inverseDot
    end.

    Lemma pi_length_cons : forall (s : Tr) a,
      pi (length s) (s • a)  = Some a. (* s ++ a::nil *)
    Proof.
      intros s a.
      rewrite nth_error_append_cons_eq.
      reflexivity.
    Qed.


End Trace.
