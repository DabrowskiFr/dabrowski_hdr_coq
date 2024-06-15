Require Import List Arith.
Require Import sections.lifo.ListBasics.
Require Import sections.lifo.Prelude.
Require Import sections.common.GenericTrace.
Require Import sections.traces.Trace.
Require Import sections.traces.Trace_Basics_projection.
Require Import Lia.

Module Make (Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ) 
            ( Import Tr : Trace.T Perm Address T V)
            ( Import P : Proj Perm Address T V Tr).
  
  (** ** see *)
  
  Lemma see_lt_i_j :
    forall s i j, see s i j -> i < j.
  Proof.
    intros s i j h_see.
    induction h_see.
    - inversion H; clear H; subst.
      + assumption.
      + assumption.
      + eauto.
    - now transitivity y.
  Qed.

  Lemma see_lt_length :
    forall s i j, see s i j -> j < length s.
  Proof.
    intros s i j h_see.
    induction h_see.
    - inversion H; clear H; subst.
      + eauto with nth_error.
      + eauto with nth_error.
      + eauto with nth_error.
    - assumption.
  Qed.

 Lemma see_append :
    forall s s' i j,
      see s i j -> see (s++s') i j.
  Proof.
    intros s s' i j H.
    induction H.
    - inversion H; subst; constructor 1.
      + constructor 1 with t0; auto with nth_error.
      + constructor 2 with l n v; auto with nth_error.
      + constructor 3 with t0; auto with nth_error.
    - constructor 2 with y; assumption.
  Qed.


 
  Fact seeImm_se_s : 
    forall s e k k', k' < length s -> seeImm (s • e) k k' -> seeImm s k k'.
  Proof.
    intros s e k k' h_lt h_see_se.
    
    inversion h_see_se as [ ? ? ? t0 hlt_ij h1 h2 | ? ? ? ? ? ? hlt_ij h1 h2  | ? ? ? t0  hlt_ij h1 h2  ];subst;assert (k<length s) as h_lt_k by lia;assert (pi k s  = pi k  (s • e)) by now rewrite nth_error_append_left.
     - rewrite nth_error_append_left in h1,h2.
      now constructor 1 with t0. lia.
      lia.
    -  rewrite nth_error_append_left in h1,h2.
      now constructor 2 with l n v. lia.
      lia.
    -rewrite nth_error_append_left in h1,h2.
      now constructor 3 with t0. lia.
      lia.
  Qed.

  Hint Resolve see_lt_i_j : see.

  Fact see_se_s : 
    forall s e k k', k' < length s -> see (s • e) k k' -> see s k k'.
  Proof.
    intros s e k k' h_lt h_see.
    induction h_see.
    - constructor 1; now apply seeImm_se_s with e.
    - assert (y < length s)
             by (assert (y < z) by eauto with see; auto with *).
      constructor 2 with y; intuition eauto.
  Qed.

End Make.            

Module Type SeeT (Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ) 
            ( Tr : Trace.T Perm Address T V)
            ( P : Proj Perm Address T V Tr).
Include (Make Perm Address T V Tr P).
End SeeT.
