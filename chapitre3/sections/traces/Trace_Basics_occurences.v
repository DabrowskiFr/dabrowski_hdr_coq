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
            ( Tr : Trace.T Perm Address T V)
            ( P : Proj Perm Address T V Tr).

  Import Tr.
  Import P.
  Hint Constructors occursIn occursAfter : myconstructors.
  Hint Constructors singleAction: myconstructors.
  Hint Constructors tribeChildren owns: myconstructors.
  Hint Unfold tribe : myunfold.

  Ltac occurence_single := 
    match goal with
        HWFOcc : wf_occurences ?s,
                 H : action_of (pi ?i ?s) == ?a, 
                     H0 : action_of (pi ?j ?s) == ?a |- ?i = ?j =>
        eapply (HWFOcc a); eauto
    end.
  
  Ltac singleOccurence :=
    match goal with
      | H0 : singleAction ?A |- _ => 
        inversion H0; clear H0; subst; singleOccurence
      | H0 : wf_occurences ?S, 
             H1 : action_of (pi ?I ?S) == ?B |- ?I = ?J =>
        solve [eapply H0 with (a:=B); eauto 2]
      | H0 : wf_occurences ?S,  
             H1 : action_of (pi ?J ?S) == ?B |- ?I = ?J =>
        solve [eapply H0 with (a:=B); eauto 2]                                      
    end. 
  

  Fact nth_error_dec : 
    forall (A : Type) (eq_dec : forall x y:A, {x=y}+{x<>y}) (l : list A) (e : A),
      {exists i, nth_error l i = Some e} + {forall i, nth_error l i <> Some e}.
  Proof.
    intros A eq_dec l e.
    induction l.
    - right; destruct i; discriminate.
    - destruct IHl.
      + left; destruct e0 as [i Hi]; exists (S i); assumption.
      + destruct (eq_dec a e); [subst |].
        * left; exists 0; reflexivity.
        * right; destruct i; simpl.
          --  contradict n0.
              injection n0; intros; subst;reflexivity.
          --  apply n.
  Qed.        

  Fact lift_nth_error_dec :
    forall (A B : Type) (f : A -> B) (eq_dec : forall x y : B, {x = y} + {x <>y}) (l :list A) (e: B),
      {exists i, lift f (nth_error l i) = Some e} + {forall i, lift f (nth_error l i) <> Some e}.
  Proof.
    intros A B f eq_dec l e.
    induction l.
    - right; destruct i; discriminate.
    - destruct IHl.
      + left; destruct e0 as [i Hi]; exists (S i); assumption.
      + destruct (eq_dec (f a) e); [subst |].
        * left; exists 0; reflexivity.
        * right; destruct i; simpl.
          -- congruence. 
          -- auto.
  Qed.

  Lemma eq_option_dec : 
    forall (A : Type) (eq_dec : forall x y : A, {x=y} + {x<>y}),
      forall x y : option A, {x = y} + {x <> y}.
  Proof.
    intros A eq_dec x y.
    destruct x as [x | ]; destruct y as [y | ]; [ destruct (eq_dec x y) | | |]; intuition congruence.
  Qed.

  Arguments eq_option_dec [A] _ _ _.

  Fact occursIn_dec :
    forall (s : Tr) (a : action), {occursIn s a} + {~occursIn s a}.
  Proof.
    intros s a.
    destruct (lift_nth_error_dec _ _ snd eq_action_dec s a).
    - left; destruct e as [i h_i]; exists i; assumption.
    - right.
      intro Ha; inversion Ha; subst. 
      elim (n i); assumption.
  Qed.

  Fact occursIn_s_se : 
  forall s a e, 
    occursIn s a -> 
    occursIn (s • e) a. 
  Proof.
    intros s a e HOccursIn.
    assert (exists i, action_of (pi i s) == a) 
      as [ i Hi ] by (inversion HOccursIn; subst; eauto).
    exists i; eauto with nth_error.
  Qed.

  Fact occursIn_se_s_neq : 
    forall (s : Tr) (t : threadId) (a a' : action), 
      occursIn (s • (t,a)) a' -> 
      a <> a' -> 
      occursIn s a'.
  Proof.
    intros s t a a' HOccursIn HNeq.
    destruct HOccursIn as [i Hi]; eauto with nth_error.
    admit.
    Admitted.
  (* Qed. *)

  Lemma occursAfter_se_s_neq : 
    forall s t a a' a'', 
      occursAfter (s • (t,a)) a' a'' -> 
      a'' <> a -> 
      occursAfter s a' a''.
  Proof.
    intros s t a a' a'' h_occursAfter h_neq.
    destruct h_occursAfter. 
    assert (j < length s) by eauto with nth_error.
    assert (i < length s) by auto with *.
    exists i j; nth_error_autorewrite.
  Qed.

  Lemma occursIn_se_s_snd : 
    forall (tr:Tr) e a,
      occursIn (tr• e) a ->
      occursIn tr a \/ (snd e) = a.
  Proof.
    induction tr as [|e tr IH] using tr_ind ; intros e' a H.
    - inversion H as [ ? ? Ha ]; subst.
      destruct i; simpl in *.
      + right. inversion Ha. trivial.
      + destruct i; discriminate.
    - inversion H as [ ? ? Ha ]; subst.
      destruct (lt_eq_lt_dec i (length (tr • e))) as [[Hlt|Heq]|Hgt].
      + assert(action_of (pi i ((tr • e))) == a) by
            (rewrite nth_error_append_left in Ha; trivial).
        assert(occursIn (tr • e) a) by (econstructor; eassumption).
        intuition.
      + subst. autorewrite with nth_error in Ha.
        inversion Ha.
        intuition.
      + admit.
        (* assert(i>=length((tr•e)•e')) by
            (autorewrite with length in *; simpl in *; intuition).
        rewrite nth_errorGeLength in Ha; trivial.
        discriminate. *)
  Admitted.
  (* Qed. *)

  Hint Resolve occursIn_s_se occursIn_se_s_neq : occurences.

  Section Order.
    
    Variable s : Tr.
    Variable HWFOcc : wf_occurences s.
    Variables (a : action) (Ha : singleAction a).
    Variables (a' : action) (Ha' : singleAction a').
    Variables (a'' : action) (Ha'' : singleAction a').

    Lemma occursAfter_irrefl : ~ occursAfter s a a.
    Proof.
      intro HOccursAfter.
      inversion HOccursAfter as [ i i' ? HLt]; subst.
      replace i' with i in HLt by occurence_single.
      auto with *.
    Qed.    
    
    Lemma occursAfterSingle :
      occursAfter s a a' -> 
      forall i j, 
        action_of (pi i s) == a -> 
        action_of (pi j s ) == a' -> 
        i < j.
    Proof.
      intros HOccursAfter i j Hi Hj.
      inversion HOccursAfter as [ i' j' ? HLt]; subst.
      replace i' with i in HLt by occurence_single.
      replace j' with j in HLt  by occurence_single.
      assumption.
    Qed.
    
    Lemma occursAfter_asym : 
      occursAfter s a a' -> ~ occursAfter s a' a.
    Proof.
      intros HOccursAfter1 HOccursAfter2.
      inversion HOccursAfter1 as [i0 j0 ? HLt0]; 
        inversion HOccursAfter2 as [i1 j1 ? HLt1]; subst.
      replace i1 with j0 in HLt1 by occurence_single.
      replace j1 with i0 in HLt1 by occurence_single.
      assert (i0 < i0) by auto with *.
      auto with *.
    Qed.
    
    Lemma occursAfter_trans : 
      occursAfter s a a' -> 
      occursAfter s a' a'' -> 
      occursAfter s a a''.
    Proof.
      intros HOccursAfterLeft HOccursAfterRight.
      inversion HOccursAfterLeft as [i0 j0 ? HLt0]; 
        inversion HOccursAfterRight as [i1 j1 ? HLt1]; subst.
      replace i1 with j0 in HLt1 by occurence_single.
      assert (i0 < j1) by auto with *.
      now (apply occursAfter_cons with (i := i0) (j := j1)).
    Qed.
    
  End Order.

  Lemma precedes_irrefl : 
    forall s 
      (HWFOcc : wf_occurences s) 
      (HWFOpenClose : wf_open_close s) p, 
      ~ precedes s p p.
  Proof.
    unfold precedes.
    intros; intro HF; inversion HF; subst.
    eapply Nat.lt_asymm; eauto.
    edestruct HWFOpenClose as [i0 [Hlt [Hb Hc]]]; eauto.
    assert (i0 = j) by singleOccurence; subst; assumption.
  Qed.
  
  Lemma precedes_trans : 
    forall s 
      (HWFOcc : wf_occurences s) 
      (HWFOpenClose : wf_open_close s) p p' p'', 
      precedes s p p' -> precedes s p' p'' -> precedes s p p''.
  Proof.
    intros.
    inversion H; inversion H0; subst.
    assert (j < i0).
    {
      edestruct HWFOpenClose as [i1 [Hb [Hc Hd]]]; eauto.
      assert (i1 = j) by singleOccurence; subst; assumption.
    }
    unfold precedes; eauto using Nat.lt_trans.
    Admitted.
  (* Qed. *)
  
  Lemma precedes_antisym : 
    forall s 
      (HWFOcc : wf_occurences s) 
      (HWFOpenClose : wf_open_close s) p p',
      precedes s p p' -> ~ precedes s p' p.
  Proof.
    intros.
    intro.
    apply (precedes_irrefl s HWFOcc HWFOpenClose p).    
    apply (precedes_trans s HWFOcc HWFOpenClose p p' p); assumption.
  Qed.  

  Lemma pi_undefined :
    forall i (s : Tr), ~ i < length s -> pi i s = None.
  Proof.
    intros i s H.
    assert (i>= length s) by lia.
    now apply nth_errorGeLength.
  Qed.
  
  Hint Rewrite pi_undefined : pi.

  Lemma open_close_lt :
    forall s p i j,
      wf_occurences s ->
      wf_open_close s ->
      action_of (pi i s) == Open p ->
      action_of (pi j s) == Close p ->
      i < j.
  Proof.
    intros s p i j Hocc Hop Hi Hj.
    destruct (Hop _ _ Hj) as [j0 [Ha [Hb Hc]]].
    now replace j0 with i in * by wellFormed_occurences (Open p).
  Qed.

  Lemma notOccursIn_s_se :
    forall s e a,
      ~ occursIn s a ->
      snd e <> a ->
      ~ occursIn (s• e) a.
  Proof.
    intros s e a h_n_occurs h_e.
    intro h_occ.
    destruct h_occ as [i a].
    destruct (lt_eq_lt_dec i (length s)) as [[h_lt | heq] | hgt].
    - assert (action_of (pi i s ) == a) as Ha1 by eauto with nth_error.
      contradict h_n_occurs.
      constructor 1 with i;auto.
    - rewrite heq in Ha.
      autorewrite with nth_error in Ha.
      contradict h_e.
      auto.
      admit.
    - assert (i< length  (s • e)) as hlt by eauto with nth_error.
      admit.
Admitted.

  Lemma notOccursIn_se_s :
    forall s e a,
       ~ occursIn (s• e) a ->
       ~ occursIn s a.
  Proof.
    intros s e a h_n_occ_se.
    contradict h_n_occ_se.
    now apply occursIn_s_se.
  Qed.

  Fact occursAtMostOnce_se_s : 
    forall s e a, occursAtMostOnce (s • e) a -> occursAtMostOnce s a.
  Proof.
    unfold occursAtMostOnce; eauto 4 with nth_error.
  Qed.

End Make.

Module Type OccurencesT (Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ) 
            ( Tr : Trace.T Perm Address T V)
            ( P : Proj Perm Address T V Tr).
  Include Make Perm Address T V Tr P.
End OccurencesT.
