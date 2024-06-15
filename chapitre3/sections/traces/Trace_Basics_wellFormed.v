Require Import List Arith.
Require Import sections.lifo.Prelude.
Require Import sections.common.GenericTrace.
Require Import sections.traces.Trace.
Require Import sections.traces.Trace_Basics_projection.
Require Import sections.traces.Trace_Basics_occurences.
Require Import sections.traces.Trace_Basics_range.
Require Import sections.traces.Trace_Basics_father.
Require Import sections.traces.Trace_Basics_owns.
Require Import sections.traces.Trace_Basics_tribe.
Require Import sections.traces.Trace_Basics_see.
Require Import sections.lifo.ListBasics.
 
Require Import Lia.

Module Make (Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ) 
            ( Tr : Trace.T Perm Address T V)
            ( P : Proj Perm Address T V Tr)
            ( O : OccurencesT Perm Address T V Tr P)
            ( F : FatherT Perm Address T V Tr P O) 
            ( OW : OwnsT Perm Address T V Tr P O)
            ( R : RangeT Perm Address T V Tr P O)
            ( Tribe : TribeT Perm Address T V Tr P O F OW R)
            ( See : SeeT Perm Address T V Tr P).

  Import Tr P O F OW R Tribe See.
  
  (*************************)

 Lemma sec_order_se_s_neq :
    forall s t a p p',
      wf_occurences (s • (t,a)) ->
      wf_fork (s • (t,a)) ->
      wf_open_close (s • (t,a)) ->
      sec_order (s • (t,a)) p p' -> a <> Open p' -> a <> Open p -> sec_order s p p'.
  Proof.
    intros s t a p p' h_wf_occ h_wf_fork h_wf_oc h_sec_order h_neq h_neq'.
    destruct h_sec_order.
    - assert (k <  length s).
      {
        admit.
        (* assert (k < length (s • (t,a))) by eauto with nth_error.
        autorewrite with length in H3; simpl in H3.
        assert (k <> length s).
        intro; subst.
        autorewrite with nth_error in H1.
        injection H1; intros; subst.
        exfalso; intuition.
        intuition. *)
      }
      assert (i <  length s) by auto with *.
      case_eq  (pi k (s • (t,a)));
        [ intros [t0 a'] h_eq | intros h_neq2 ]; subst.
      + assert (forall t', (t, a) <> (t', Fork t0)).
        {
          intros.
          intro.
          injection H5; intros; subst.
          assert (pi (length s) (s • (t', Fork t0)) == (t', Fork t0)).
          autorewrite with nth_error; reflexivity.
          assert (length s < k).
          eapply h_wf_fork.
          unfold Event.t in *; rewrite H6; reflexivity.
          unfold Event.t in *; rewrite h_eq; reflexivity.
          auto with *.
        }
        assert (pi k (s • (t,a)) = pi k s) by eauto with nth_error.
        assert (pi i (s • (t,a)) = pi i s) by eauto with nth_error.
        edestruct range_se_s_neq_open.
        apply h_wf_occ.
        apply h_wf_oc.
        apply H.
        assumption.
        * apply sec_order_cons_dir with i j k.
          tauto.
          assumption.
          unfold Event.t in *; rewrite <- H6.
          assumption.
          unfold Event.t in *; rewrite <- H6; rewrite <- H7; assumption.
        * apply sec_order_cons_dir with i (length s - 1) k.
          tauto.
          auto with *.
          unfold Event.t in *; rewrite <- H6.
          assumption.
          unfold Event.t in *; rewrite <- H6; rewrite <- H7; assumption.
      + unfold Event.t in *; rewrite h_neq2 in H1; discriminate.
    - assert (i' <  length s).
      {
        assert (i' < length (s • (t,a))) by eauto with nth_error.
        admit.
        (* autorewrite with length in H3; simpl in H3.
        assert (i' <> length s).
        intro; subst.
        autorewrite with nth_error in H0.
        injection H0; intros; subst.
        exfalso; intuition.
        intuition. *)
      }
      assert (i <  length s).
      {
        assert (i < length (s • (t,a))) by eauto with nth_error.
        admit.
        (* autorewrite with length in H4; simpl in H4. *)
        (* assert (i <> length s).
        intro; subst.
        autorewrite with nth_error in H.
        injection H; intros; subst.
        exfalso; intuition.
        intuition. *)
      }
      assert (forall t', (t, a) <> (t', Fork t0)).
      {
        intros.
        intro.
        injection H5; intros; subst.
        assert (pi (length s) (s • (t', Fork t0)) == (t', Fork t0)).
        autorewrite with nth_error; reflexivity.
        assert (length s < i').
        eapply h_wf_fork.
        unfold Event.t in *; rewrite H6; reflexivity.
        assumption.
        auto with *.
      }
      assert (pi i' (s • (t,a)) = pi i' s) by eauto with nth_error.
      assert (pi i (s • (t,a)) = pi i s) by eauto with nth_error.
      apply sec_order_cons_ind with i i' t0.
      unfold Event.t in *; congruence. 
      unfold Event.t in *; congruence. 
      unfold Event.t in *; congruence. 
      apply tribe_children_se_s_not_fork with (t,a); try assumption.
      Admitted.
(* Qed. *)

  Lemma concurrent_s_se : 
    forall s p p' e,
      wf_occurences (s • e) ->
      wf_fork (s • e) ->
      wf_open_close (s • e) ->
      concurrent s p p' ->
      concurrent (s • e) p p'.
  Proof.

    intros s p p' e h_wf_occ h_wf_fork h_wf_open_close h_conc.
    unfold concurrent in *.
    destruct h_conc as [H1 [H2 [H3 H4]]].
    destruct e as [t a].
    assert (a <> Open p).
    {
      intro; subst.
      inversion H1 as [i ? hi]; subst.
      assert (i < length s) by eauto with nth_error.
      assert (i = length s).
      {
        assert (action_of (pi i (s • (t,Open p))) == Open p) by eauto with nth_error.
        assert (action_of (pi (length s) (s • (t, Open p))) ==  Open p).
        autorewrite with nth_error; reflexivity.
        wellFormed_occurences (Open p).
      }
      exfalso; auto with *.
    }
    assert (a <> Open p').
    {
      intro; subst.
      inversion H2 as [i ? hi]; subst.
      assert (i < length s) by eauto with nth_error.
      assert (i = length s).
      {
        assert (action_of (pi i (s • (t,Open p'))) == Open p') by eauto with nth_error.
        assert (action_of (pi (length s) (s • (t, Open p'))) ==  Open p').
        autorewrite with nth_error; reflexivity.
        wellFormed_occurences (Open p').
      }
      exfalso; auto with *.
    }
    split.
    now apply occursIn_s_se.
    split.
    now apply occursIn_s_se.
    split.
    contradict H3.

    apply sec_order_se_s_neq with t a; try assumption.
    contradict H4.
    apply sec_order_se_s_neq with t a; try assumption.
Qed.


  Fact wf_occurences_se_s : 
    forall s e, wf_occurences (s • e) -> wf_occurences s.
  Proof.
    unfold wf_occurences; eauto 3 using occursAtMostOnce_se_s.
  Qed.
  
  Fact wf_fork_se_s : forall s e, wf_fork (s • e) -> wf_fork s.
  Proof.
    unfold wf_fork; eauto 4 with nth_error.
  Qed.
  
  Fact wf_join_se_s : forall s e, wf_join (s • e) -> wf_join s.
  Proof.
    unfold wf_join; intuition eauto 5 with nth_error.
  Qed.

  Fact wf_open_close_se_s : forall s e, wf_open_close (s • e) -> wf_open_close s.
  Proof.
    intros s e h_wf_open_close i p h_close.
    assert (action_of (pi i (s • e)) == Close p) as Ha by auto with nth_error.
    destruct (h_wf_open_close i p Ha) as [j [h1_j [h2_j h3_j]]].
    assert (i < length s) by eauto with nth_error.
    assert (j < length s) by auto with *.
    assert (threadId_of (pi i s) = threadId_of (pi j s)).
    {
      replace (pi i s) with (pi i (s • e)).
      replace (pi j s) with (pi j (s • e)).
      assumption.
      eauto with nth_error.
      eauto with nth_error.
    }
    exists j; intuition eauto 4 with nth_error.
    replace (pi j s) with (pi j (s • e)).
    assumption.
    eauto with nth_error.
  Qed.

  Lemma wf_seq_order_se_s : 
    forall s e, 
      wf_seq_order (s • e) -> wf_seq_order s.
  Proof.
    intros s e h_wseq.
    unfold wf_seq_order in *.
    intros p i j h_range h_close_p k p' h_in h_tid_eq h_open_p'.
    assert (j < length s) by
        ( inversion h_range; subst; [eauto with nth_error | auto with *]).
    assert (k < length s) by auto with *.
    assert (i < length s) by auto with *.
    assert (pi j (s • e) = pi j s) as h_eq_j by eauto with nth_error.
    assert (pi k (s • e) = pi k s) as h_eq_k by eauto with nth_error.
    assert (pi i (s • e) = pi i s) as h_eq_i by eauto with nth_error.

    inversion h_range; subst.
    - assert (range (s • e) p i j) by
          (constructor 1; inversion h_range; congruence).
      destruct h_wseq with p i j k p' as [i0 [Hd He]]; try congruence.
       assert (pi i0 (s • e) = pi i0 s) as h_eq_i0. 
      {
        assert (i0 < length s) by auto with *.
        eauto with nth_error.
      }
      exists i0; split; congruence.
    - elim HNotClosed.
      exists (length s - 1).
      assumption.
Qed.

  Fact wf_join_see_fork_se_s : forall s e, wf_join_see_fork (s • e) -> wf_join_see_fork s.
  Proof.
     unfold wf_join_see_fork.
     intros s e H t0 k k' H0 H1.
     apply see_se_s with e;eauto with nth_error.
  (* unfold wf_join_see_fork; eauto 6 using see_se_s with nth_error.*)
  Qed.

  Fact wf_join_all_closed_se_s : forall s e, wf_join_all_closed (s • e) -> wf_join_all_closed s.
  Proof.
      intros s e h_wf_join_all_closed p t0 i j k h_range h_owns h_action.
      unfold wf_join_all_closed in *.
      destruct (range_s_se s p i j e h_range) as [ [h1 h2]| h1 ].
      - apply h_wf_join_all_closed with p t0 i;
        eauto using owns_s_se with nth_error.
      - assert (length s < k) as hgt by (apply h_wf_join_all_closed with p t0 i;eauto using owns_s_se with nth_error).
        assert (k<length s) as hlt by eauto with nth_error.
        exfalso; lia.
  Qed.

 Fact wf_mutualExclusion_se_s : 
    forall s e, 
      wf_occurences (s • e) ->
      wf_fork (s • e) ->
      wf_open_close (s • e) ->
      wf_mutualExclusion (s • e) -> 
      wf_mutualExclusion s.
  Proof.
    intros s e h_wf_occurences h_wf_fork h_wf_occ h_wf_mutualExclusion.
    intros p p'  h_conc.
    destruct h_wf_mutualExclusion with p p' as [Hc | Hc]; try assumption.
    - now apply concurrent_s_se.
    - left.
      inversion Hc; subst.
      assert (j < length s). 
      {
        inversion h_conc as [Hu [Hv [Hw Hx]]].
        inversion Hv as  [j' ? Hj']; subst.
        assert (j = j').
        {
          assert (action_of (pi j' (s • e)) == Open p') by eauto with nth_error.
          wellFormed_occurences (Open p').
        }
        subst; eauto with nth_error.
      }
      assert (i < length s) by auto with *.
      constructor 1 with i j; eauto with nth_error.
      replace (pi i s) with (pi i (s •e)).
      assumption.
      eauto with nth_error.
      replace (pi j s) with (pi j (s • e)).
      assumption.
      eauto with nth_error.
    - right.
      inversion Hc; subst.
      assert (j < length s). 
      {
        inversion h_conc as [Hu [Hv [Hw Hx]]].
        inversion Hu as  [j' ? Hj']; subst.
        assert (j = j').
        {
          assert (action_of (pi j' (s• e)) == Open p) by eauto with nth_error.
          wellFormed_occurences (Open p).
        }
        subst; eauto with nth_error.
      }
      assert (i < length s) by auto with *.
      constructor 1 with i j; eauto with nth_error.
      replace (pi i s) with (pi i (s •e)).
      assumption.
      eauto with nth_error.
      replace (pi j s) with (pi j (s • e)).
      assumption.
      eauto with nth_error.
  Qed.

  Lemma wellFormed_se_s : forall s e, wellFormed (s • e) -> wellFormed s.
  Proof.
    intros s e h_wf_se.
    inversion h_wf_se; constructor;
    eauto using 
          wf_occurences_se_s, wf_fork_se_s, wf_seq_order_se_s, wf_join_se_s, wf_open_close_se_s, wf_join_see_fork_se_s,
           wf_join_all_closed_se_s, wf_mutualExclusion_se_s.
  Qed.

  Hint Resolve wellFormed_se_s : myresolve.

End Make.
