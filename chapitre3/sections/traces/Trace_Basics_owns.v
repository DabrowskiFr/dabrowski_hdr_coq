Require Import List Arith.
Require Import sections.lifo.ListBasics.

Require Import sections.lifo.Prelude.
Require Import sections.common.GenericTrace.
Require Import sections.traces.Trace.
Require Import sections.traces.Trace_Basics_projection.
Require Import sections.traces.Trace_Basics_occurences.

Module Make (Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ) 
            ( Import Tr : Trace.T Perm Address T V)
            ( Import P : Proj Perm Address T V Tr)
            ( Import O : OccurencesT Perm Address T V Tr P).

  Fact owns_functionnal :
    forall s,
      wf_occurences s ->
      forall p t t', 
        owns s p t -> 
        owns s p t' -> 
        t = t'.
  Proof.
    intros s h_wf_occurences_s p t t' h_owns_t h_owns_t'. 
    inversion h_owns_t as [? i ? h_threadId h_action]; subst. 
    inversion h_owns_t' as [? i' ? h_threadId' h_action']; subst.
    assert (i = i') by wellFormed_occurences (Open p). 
    congruence.
  Qed.

  Fact owns_dec : 
    forall s p t, {owns s p t} + {~ owns s p t}.
  Proof.
    intros s p t.
    destruct (nth_error_dec _ Event.eq_dec s (t, Open p)) as [h_a | h_a].
    - left.
      destruct h_a as [i h_i]; constructor 1 with i; rewrite h_i; reflexivity.
    - right.
      destruct 1 as [? i ? ?].
      assert (pi i s == (t0, Open p)) as h_b by (unfold Event.t; auto with proj).
      firstorder.
  Qed.
  
  Fact owns_s_se : 
    forall s p t, owns s p t -> forall e, owns (s • e) p t.
  Proof.
    intros s p t Howns e. 
    inversion Howns; subst.
    assert (pi i s = pi i (s • e)).
    {
      assert (i < length s).
      apply nth_error_defined_lt.
      case_eq (pi i s); intros.
      exists t0; reflexivity.
      rewrite H in HThreadOf.
      discriminate.
      symmetry.
      apply nth_error_append_left.
      assumption.
    }
    apply owns_cons with (i :=i).
    rewrite <- H; assumption.
    rewrite <- H; assumption.
  Qed.
  
  Fact owns_se_s : 
    forall (s : Tr) e p t, owns (s • e) p t -> e <> (t, Open p) -> owns s p t.
  Proof.
    intros s e p t h_owns h_neq.
    inversion h_owns as [? i h_threadId h_action]; subst.
    assert (pi i (s • e) == (t, Open p)) by (unfold Event.t; auto with proj).
    assert (pi i s == (t, Open p)) by eauto with nth_error.
    exists i; congruence.
  Qed.  

  Lemma ownsOpen : 
    forall s, 
      wf_occurences s -> 
      forall i p t,
        action_of (pi i s) == Open p -> owns s p t -> threadId_of (pi i s) == t.
  Proof.
    intros s h_wf_occurences_s i p t h_action h_owns.
    inversion h_owns as [? i' ? h_threadId h_action2]; subst.
    assert (i = i') by wellFormed_occurences (Open p).
    congruence.
  Qed.

(*    Lemma ownerfowns :
    forall s p t,
      Some t = ownerf s p -> 
      owns s p t.
  Proof.
    induction s.
    - intros p t0 H.
      inversion H.
    - intros p t0 H.
      inversion H.
      destruct a.
      destruct a.
*)      
  



End Make.

Module Type OwnsT (Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ) 
            ( Tr : Trace.T Perm Address T V)
            ( P : Proj Perm Address T V Tr)
            ( O : OccurencesT Perm Address T V Tr P).
Include Make Perm Address T V Tr P O.
End OwnsT.
