Require Import Lt List Lia. 
From sections.lifo Require Import Prelude ListBasics Length.
From sections.common Require Import Insertion.
From sections.traces Require Import Trace_Basics_tribe Synchronisation.
From sections.traces Require Import Trace_Basics_tribe EquivalenceTheory.
From sections.traces Require Import SyncInsertion Atomicity.

Module Make (SN: MiniDecidableSet)
            (Export Ad : DecidableInfiniteSet) 
            (Export Ty : Type_.TYPE Ad )
            (Export Va : Value.TYPE Ad Ty).
   
  Include Atomicity.Make SN Ad Ty Va.

(** The following theorem states that, in atomic traces, non-concurrent sections do not overlap *)

Theorem atomic_no_overlap :
  forall s,
    wellFormed s ->
    atomic s ->
    forall p i j,
      range s p i j ->
      forall k p',
        i < k < j ->
        action_of (pi k s) == Open p' ->
        action_of (pi j s) == Close p ->
        (exists k', k < k' < j /\ action_of (pi k' s) == Close p').
Proof.
  intros s h_wf h_atomic p i j h_range k p' h_in h_open_p' h_close_p.
  inversion h_wf as [_ _ _ _ h_wseq _ _ _].
  case_eq (pi i s) ; intros; subst. (* eq_pi_i_s *)
  - case_eq (pi k s); intros; subst.
    + destruct t0 as [t0 a0].
      destruct t1 as [t1 a1].
      destruct (Peano_dec.eq_nat_dec t0 t1).
      *  assert (threadId_of (pi i s) = threadId_of (pi k s))
          by (subst; rewrite H, H0; reflexivity).
         eapply h_wseq; eauto.
      * assert (forall k n0 j s a,
                  {k < n0 < j /\ action_of (pi n0 s) == a} +
                  {~ (k < n0 < j /\ action_of (pi n0 s) == a)}) as decidable_aux.
        {
          clear.
           intros.
           destruct (Compare_dec.lt_dec k n0).
          - destruct (Compare_dec.lt_dec n0 j).
            + destruct (pi n0 s) as [[n1 b] | ].
              *  {
                  destruct (Event.eq_dec (n1,b) (n1, a)) as [h_eq | h_neq].
                  - injection h_eq; intros; subst; left; tauto. 
                  - right; intro H; destruct H as [H H0].
                    elim h_neq.
                    injection H0; intros; subst; reflexivity.
                }
              * right; intro H; destruct H; discriminate.
            + right; intro H; destruct H; elim n; intuition.
          - right; intro H; destruct H; elim n ;intuition.
        }
        apply nforalln_exists with (S j); [intros n0; apply decidable_aux|].
        intro.
        assert (~ tribe s p' t0).
        {
          intro.
          assert (owns s p' t0).
          {
            apply tribe_after_open with i k; try assumption.
            inversion h_wf; assumption.
            inversion h_wf; assumption.
            auto with *.
            rewrite H; reflexivity.
          }
          inversion H3; subst.
          assert (i0 = k) by wellFormed_occurences (Open p').
          subst.
          rewrite H0 in HThreadOf; simpl in HThreadOf.
          elim n; congruence.
        }
        unfold atomic in h_atomic.
        assert (exists j', j <= j' /\ range s p' k j') as [j' [Ha Hb]].
        {
          destruct (occursIn_dec s (Close p')).
          - inversion o as [j' h_j']; subst.
            destruct (Compare_dec.lt_dec j j').
            + (exists j').
              split; [auto with *| constructor 1; assumption].
            + assert (j' < S j) by auto with *.
              apply H1 in H3.
              elim H3.
              assert (k < j' < j).
              {
                split.
                - inversion h_wf.
                  unfold wf_open_close in WF4.
                  destruct (WF4 _ _ Ha) as [i0 [hlt_0 [h_eqa h_eqb] ]].
                  assert (i0 = k) by wellFormed_occurences (Open p').
                  subst.
                  assumption.
                - assert (j <> j').
                  intro; subst.
                  rewrite Ha in h_close_p.
                  assert (p' = p) by (injection h_close_p; intros; subst; reflexivity).
                  subst.
                  assert (k = i).
                  {
                    assert (action_of (pi i s) == Open p) by
                        (inversion h_range; assumption).
                    wellFormed_occurences (Open p).
                  }
                  subst.
                  exfalso; auto with *.
                  auto with *.
              }
              tauto.
          - (exists (length s - 1)).
            split.
            assert (j < length s). 
            eapply lift_nth_error_defined_left.
            exists (Close p). apply h_close_p.
            auto with *.
            constructor 2; assumption.
        }
        elim H2.
        apply h_atomic with k j' j.
        assumption.
        auto with *.
        inversion h_wf.
        destruct (WF4 _ _ h_close_p) as [i0 [Hu [Hv Hw]]].
        assert (action_of (pi i s) == Open p)  by now inversion h_range.
        assert (i0 = i) by wellFormed_occurences (Open p).
        subst.
        rewrite Hw.
        rewrite H.
        reflexivity.
    + rewrite H0 in h_open_p'. 
      discriminate. 
  - assert (action_of (pi i s) == Open p) by now inversion h_range. 
    rewrite H in H0.
    discriminate.
Qed.


(** Now we prove that any well-synchronized trace is equivalent to an atomic trace. *)
(** - Proposition [outerExclude_insertion_atomic] is a technical result stating that  *)
(** given an atomic trace the insertion of an event in s before the leftmost [Open] of *)
(** a section excluding the event leads to an atomic trace provided the element does not *)
(** synchronize with any event occuring after the [Open] in s *)
(** - Theorem [wsync_atomic] states our main result *)

Proposition outerExclude_insertion_atomic : 
  forall s,
    atomic s ->
    forall p t a i,
      wellFormed (s • (t,a)) ->
      wellSynchronized (s • (t,a)) ->
      outerExclude s p t ->
      action_of (pi i s) == Open p ->
      (forall k : threadId,
                      i <= k < length s -> 
                      ~ synchronizeWith (s • (t, a)) k (length s)) ->
      forall s', 
        insertion i s (t,a) == s' ->
        atomic s'.
Proof.
  intros s h_atomic_s p t a i h_wf_se h_ws_se h_outerExclude h_i h_no_sync s' h_insertion.

  
  assert (forall k, i <= k < length s -> ~ synchronizeWith (s • (t,a)) k (length s))
    by (inversion h_outerExclude; now apply exclude_noSync with p).
    
  assert (pi i s' == (t, a)) as h_i_s' by now apply insertion_eq with s.
  assert (length s = length s' - 1) as h_eq.
  {
    rewrite <- (insertion_length _ _ _ _ _ h_insertion).
    lia.
  }
  assert (i < length s) as h_lt_i_s by eauto with nth_error.
  assert (wellFormed s) as h_wf_s by now apply wellFormed_se_s with (t,a).
  assert (wellFormed s') as h_wf_s'.
  {
    apply compatible_wellFormed with (s • (t,a)).
    assert (exclude s p t) by now inversion h_outerExclude.
    now apply insertion_compatible with i p.
    assumption.
    assumption.
  }
  (*clear h_no_sync. clear H.*)

  assert (conflicts s t) by (inversion h_outerExclude; exists p; assumption).
  
  intros p' i' j' h_range k h_int t' h_thread.

  assert (tribe s p' t'). 
  {
    assert (i' <> i).
    {
      intro; subst.
      assert (a = Open p').
      {
        assert (action_of (pi i s') == Open p') as h_open by now inversion h_range.
        rewrite h_i_s' in h_open; simpl in h_open; congruence.
      }
      eelim wellFormed_open_in; eauto.
    }
    destruct (Peano_dec.eq_nat_dec k i); [subst | eapply atomic_from; eauto].
    assert (t = t'). 
    {
      assert (pi i s' == (t,a)) as h_proj by eauto using insertion_eq.
      rewrite h_proj in h_thread; simpl in h_thread; congruence.
    }
    subst.
    assert (~ tribe s p t')
      by (destruct h_outerExclude as [ []]; assumption).
    destruct (Peano_dec.eq_nat_dec i j').
    - assert (owns s p' t').
      {
        assert (a = Close p').
        {
          assert (j' < length s') by (subst; eauto with nth_error).
          inversion h_range; subst.
          - rewrite h_i_s' in Hj; simpl in Hj; congruence.
          - rewrite h_eq in h_lt_i_s.
          exfalso; auto with *.
        }
        subst.
        assert (action_of (pi (length s) (s •(t', Close p'))) == Close p') as h_close_act. 
        {
          rewrite lift_nth_error_append_right.
          replace (length s - length s) with 0 by auto with *.
          reflexivity.
          auto with *.
        }
        inversion h_wf_se as [ a b c WF2 d e f g  ].
        destruct (WF2 _ _ h_close_act) as [k0 [Ha [Hb Hc]]].
        assert (threadId_of (pi (length s) (s •(t', Close p'))) == t') as h_close_id. 
        {
          rewrite lift_nth_error_append_right.
          replace (length s - length s) with 0 by auto with *.
          reflexivity.
          auto with *.
        }
        rewrite h_close_id in Hc.
        replace (pi k0 (s • (t',Close p'))) with (pi k0 s) in Hb, Hc by (symmetry; eauto with nth_error).
        exists k0.
        destruct (pi k0 s) as [t1 | ]; [ | discriminate].
        destruct t1; injection Hb; injection Hc; intuition.
        assumption.
      }        
      now constructor 1.
    - assert (i < j') by auto with *.
      destruct j'; [exfalso; auto with *|].
      inversion h_range; subst.
      + assert (pi (S j') s' = pi j' s) by
            (apply insertion_ge with i (t',a); auto with *).
        assert (wf_seq_order s) by now inversion h_wf_s.
        assert (action_of (pi j' s) == Close p').
        {
          rewrite <- H4; assumption.
        }
        assert (pi i' s' = pi i' s).
        {
          apply insertion_lt with i (t',a).
          assumption.
          auto with *.
        }
        assert (range s p' i' j').
        {
          constructor 1.
          rewrite <- H7; assumption.
          rewrite <- H4; assumption.
        }
        assert (i' < i < j').
        {
          split.
          auto with *.
          assert (i <> j').
          {
            intro; subst.
            rewrite H6 in h_i.
            discriminate.
          }
          auto with *.
        }
        

        destruct atomic_no_overlap with s p' i' j' i p as [hj [Hu Hv]]; try assumption.
        destruct h_outerExclude.
        destruct H10.
        destruct H10.
        elim H13.
        exists hj.
        assumption.
      + (* contradiction with outerExclude *)
        assert (pi i' s' = pi i' s).
        {
          apply insertion_lt with i (t',a).
          assumption.
          auto with *.
        }
        assert (pending s p').
        {
          assert (~ occursIn s (Close p')).
          {
            contradict HNotClosed.
            assert (occursIn (s • (t',a)) (Close p')).
            now apply occursIn_s_se.
            eapply insertion_occursIn; eauto.
          }
          constructor.
          exists i'.
          constructor 2.
          rewrite <- H4.
          assumption.
          assumption.
          assumption.
        }
        inversion h_wf_s.
        
        destruct (tribe_dec s WF1 WF2 WF4 p' t').
        *assumption.
        *assert (exclude s p' t') by now constructor.
        inversion h_outerExclude.
        apply H10 in H8.
        inversion H8; subst.
        assert (i0 = i) by wellFormed_occurences (Open p).
        assert (j = i'). 
        {
          assert (pi i' s' = pi i' s).
          apply insertion_lt with i (t', a).
          assumption.
          auto with *.
          rewrite H12 in Hi.
          wellFormed_occurences (Open p').
        }
        subst.
        exfalso;  auto with *.
        intro; subst.
        assert (i = i').
        {
          assert (action_of (pi i' s) == Open p').
          rewrite <- H4.
          assumption.
          wellFormed_occurences (Open p').
        }
        subst; exfalso; intuition.
  }
  assert (tribe (s • (t,a)) p' t').
  now apply tribe_s_se.
  
  now apply insertion_tribe with s i t a.
Qed.

Theorem wsync_atomic : 
  forall s,
    wellFormed s -> 
    wellSynchronized s ->
    exists s', compatible s s' /\ atomic s'.
Proof.
  induction s using tr_ind; intros h_wf h_ws.
  - (exists nil); split; [apply compatible_refl | apply nil_atomic].
  - (* From induction hypothesis *)
    assert (exists s', compatible s s' /\ atomic s') as [s' [Ha Hb]].
    {
      assert (wellFormed s) by now apply wellFormed_se_s with e.
      assert (wellSynchronized s). 
      apply wellSynchronized_se_s with e; try now inversion h_wf.
      destruct IHs as [s' [Ha Hb]]; eauto.
    }
    assert (s • e ~= s' • e) by now  apply compatible_S.
    assert (wellFormed (s' • e)) by now apply compatible_wellFormed with  (s • e).
    assert (wellSynchronized (s' • e)) by now apply compatible_wellSynchronized with (s • e).

    
    assert (wellFormed s) by now apply wellFormed_se_s with e.
    assert (wf_occurences (s • e)) by (inversion h_wf;auto).


    destruct e as [t a];
      destruct (exclude_dec s' (wellFormed_se_s s' (t,a) H0) t) 
      as [h_noExclude | h_outerExclude].
    + assert (atomic (s' • (t,a))).
      {
        assert (~ conflicts s' t) by
            (intro h_conflicts; destruct h_conflicts as [p h_p]; now elim (h_noExclude p)).
        now apply noExclude_atomic. (* -> noConflicts_atomic *)
      }
      (exists (s' • (t,a))); tauto.
    + destruct h_outerExclude as [p Hp].
      assert (exists i, action_of (pi i s') == Open p) 
        as [i Hi] by now apply outerExclude_open with t.
      assert (exists s'', insertion i s' (t,a) == s'') as [s'' Hs''].
      {
        assert (i <= length s') 
          as Hv
            by (assert (i < length s') by eauto with nth_error; auto with *).
        destruct (insertion_defined i s' (t,a) Hv) as [s'' Hs''].
        exists s''; assumption.
      }
      assert (forall k : threadId,
                      i <= k < length s' -> 
                      ~ synchronizeWith (s' • (t, a)) k (length s'))
              by (inversion Hp; now apply exclude_noSync with p).
      assert (s • (t,a) ~= s'').
      {
        apply compatible_trans with (s' • (t,a)).
        -  apply compatible_S;auto.
        - assert (forall k : threadId,
                      i <= k < length s' -> 
                      ~ synchronizeWith (s' • (t, a)) k (length s'))
              by (inversion Hp; now apply exclude_noSync with p).
          assert (exclude s' p t) by now inversion Hp.
          now apply insertion_compatible with i p.    
      }
      assert (atomic s'') by now apply outerExclude_insertion_atomic with s' p t a i.
      exists s''; tauto.
Qed.


End Make.
