Require Import List Arith.
Require Import sections.lifo.ListBasics.

Require Import sections.lifo.Prelude.
Require Import sections.common.GenericTrace.
Require Import sections.traces.Trace.
Require Import sections.traces.Trace_Basics_projection.
Require Import sections.traces.Trace_Basics_occurences.

Require Import Lia.

Module Make (Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ) 
            ( Tr : Trace.T Perm Address T V)
            ( P : Proj Perm Address T V Tr)
            ( O : OccurencesT Perm Address T V Tr P).

  Import Tr.
  Import P.

   (** ** Father *)

  Lemma father_functionnal : 
    forall s, wf_occurences s -> 
         forall t t' t'', father s t t' -> father s t t'' -> t' = t''.
  Proof.
    intros s WF_occurences t t' t'' Father_t' Father_t''.
    destruct Father_t' as [i' [Ha Hb]], Father_t'' as [i'' [Hc Hd]].
    assert (i' = i'') by wellFormed_occurences (Fork t).
    congruence.
  Qed.

  Fact father_s_se : 
    forall s t t', father s t t' -> forall e, father (s • e) t t'.
  Proof.
    intros s t0 t' h_father e.
    destruct h_father as [i [h_threadId h_action]].
    exists i; eauto with nth_error.
  Qed.

  Fact father_se_s : 
    forall s e t t',
      father (s • e) t t' -> e <> (t', Fork t) -> father s t t'.
  Proof.
    intros s e t t' h_father h_neq.
    destruct h_father as [i [Ha Hb]].
    assert (pi i (s • e) == (t', Fork t)) by (unfold Event.t in *; auto with proj).
    assert (pi i s == (t', Fork t)) by eauto with nth_error.
    exists i; intuition congruence.
  Qed.

  Fact father_antisym:
    forall s t t', 
      wf_fork s -> father s t t' -> ~father s t' t.
  Proof.
    intros s t0 t' WF H H'.
    destruct H as [i [Hti Hai]].
    destruct H' as [j [Htj Haj]].
    assert(i<j) by (eauto using WF).
    assert(j<i) by (eauto using WF).
    lia.
  Qed.

End Make.

Module Type FatherT (Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ) 
            ( Tr : Trace.T Perm Address T V)
            ( P : Proj Perm Address T V Tr)
            ( O : OccurencesT Perm Address T V Tr P).
Include Make Perm Address T V Tr P O.
End FatherT.
