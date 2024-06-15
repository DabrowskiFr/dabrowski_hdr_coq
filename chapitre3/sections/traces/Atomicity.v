Require Import Lt List Lia. 
From sections.lifo Require Import Prelude ListBasics Length.
From sections.common Require Import Insertion.
From sections.traces Require Import SyncInsertion Synchronisation.
From sections.traces Require Import EquivalenceTheory. 

Module Make (SN: MiniDecidableSet)
            (Export Ad: DecidableInfiniteSet) 
            (Export Ty : Type_.TYPE Ad )
            (Export Va : Value.TYPE Ad Ty).
  
  Include SyncInsertion.Make SN Ad Ty Va.

  (** * Definition of atomicity
       A trace is atomic if for all section [p] only members of the tribe of [p]
       run while [p] is active *)

  Definition atomic (s : Tr) : Prop :=
    forall p i j, 
      range s p i j ->
      forall k, i <= k <= j ->
           forall t, threadId_of (pi k s) == t -> tribe s p t.

  (** * Basic results *)

  Lemma nil_atomic : atomic nil.
  Proof.
    repeat intro; autorewrite with nth_error in *; discriminate.
  Qed.

  (** If a thread [t] is excluded by a section [p] in an atomic trace [s] then 
  for all action [a] it is still excludes in [s • (t,a)] *)
  (** - Proof sketch : obvious, a thread can be a member of a section only it is the
  owner of the section or if it is forked by a member of the tribe. But [a] cannot be 
  [Open p] of [Fork t] because [p] is pending in [s] and [t] cannot be forked by itself *)

Lemma exclude_not_in_tribe :
    forall s,
      atomic s ->
      forall p t a, 
        wellFormed (s • (t,a)) ->
        exclude s p t -> ~ tribe (s • (t,a)) p t.
  Proof.
    intros s h_atomic p t a h_wf h_exclude h_open.
    assert (~ tribe s p t) by apply h_exclude.
    contradict H.
    assert ((t,a) <> (t, Open p)).
    {
      assert (exists i, action_of (pi i s) == Open p) as [i Hi].
      {
        destruct h_exclude as [[Ha _] _]; inversion Ha as [i Hi]; subst.
        exists i; inversion Hi; assumption.
      }
      assert (i < length s) by eauto with nth_error.
      intros Ha; injection Ha; intros; subst; clear Ha.
      assert (i = length s).
      {
        assert (action_of (pi i (s • (t,Open p))) == Open p) by
            eauto with nth_error.
            
        assert (action_of (pi (length s) (s • (t,Open p))) == Open p) by
            (autorewrite with nth_error; reflexivity).
        wellFormed_occurences (Open p).
      }
      auto with *.
    }
    assert (forall t', (t,a) = (t', Fork t) -> ~ tribe s p t').
    {
      intros t' h_eq; injection h_eq; intros; subst; clear h_eq.
      assert (pi (length s) (s • (t', Fork t')) == (t', Fork t')).
      autorewrite with nth_error; reflexivity.
      wellFormed_fork.
    }
    apply tribe_se_s_not_open_fork with (t,a); try (inversion h_wf; assumption).
    intros.
    specialize H0 with t.
    intro.
    injection H1; intros; subst.
    inversion h_wf. 
    unfold wf_fork in WF2.
    assert (length s < length s) by
        (apply WF2 with t'; autorewrite with nth_error; reflexivity).
    auto with *.
  Qed.

  (** I a thread [t] is excluded by a section [p] in an atomic trace [s] opened at position [i]
  then no event occuring after [i] in [s] would synchronize with an event performed by [t] after [s] *)
  (** - Proof Sketch : suppose there exists some [k] such that such a synchronisation exists. By atomicity
        of [s], we know that the thread at [k] is a member of the tribe of [p]. By Lemma [sw_in_tribe] it
        comes that [t] is a member of the tribe of [p] leading to a contradiction *)
  
  Lemma exclude_noSync :
    forall s,
      atomic s ->
      forall p t a i,
        wellFormed (s • (t,a)) ->
        wellSynchronized (s • (t,a)) ->
        exclude s p t ->
        action_of (pi i s) == Open p ->
        (forall k, i <= k < length s -> ~ synchronizeWith (s • (t,a)) k (length s)).
  Proof.
    intros s h_atomic p t a i h_wf h_ws h_exclude h_open k h_int.
    intro.
    assert (exists t', threadId_of (pi k (s • (t,a))) == t') 
      as [t' Ht'] by (assert (k < length (s • (t,a))) by 
        auto with *; eauto with nth_error).
    assert (tribe (s • (t,a)) p t').
    {
      assert (range s p i (length s - 1)).
      {
        assert (pending s p) by apply h_exclude.
        destruct (pending_range_last2 s p H0) as [i' Hi'].
        assert (i = i').
        {
          assert (wellFormed s) by now apply wellFormed_se_s with (t,a).
          assert (action_of (pi i' s) == Open p) by now inversion Hi'.
          wellFormed_occurences (Open p).
        }
        subst; assumption.
      }
      assert (i <= k <= length s -1) by auto with *.
      assert (threadId_of (pi k s) == t').
      {
        assert (pi k s = pi k (s • (t,a))) by
            (assert (k < length s) by intuition; symmetry; eauto with nth_error).
        congruence.
      }
      now (apply tribe_s_se; apply h_atomic with i (length s - 1) k).
    }
    assert (tribe (s • (t, a)) p t).
    {
      assert (range (s • (t, a)) p i (length s)).
      {
        assert (pending s p) as Ha by apply h_exclude.
        destruct (pending_range_last s p (t,a) Ha) as [i' Hi'].
        assert (action_of (pi i (s • (t,a))) == Open p) by eauto with nth_error.
        assert (action_of (pi i' (s • (t,a))) == Open p) by now inversion Hi'.
        assert (i = i') by wellFormed_occurences (Open p).
        subst; assumption.
      }
      assert (i <= k <= length s) by auto with *.
      assert (i <= length s <= length s) by auto with *.
      assert (threadId_of (pi (length s) (s • (t, a))) == t) by
          (autorewrite with nth_error; reflexivity).
      now apply sw_in_tribe with i (length s) k (length s) t'.
    }
    assert (~ tribe (s • (t,a)) p t) as h_ntribe by now apply exclude_not_in_tribe.
    now contradict h_ntribe.
Qed.
  
  (** If a thread [t] does not conflict in an atomic trace [s] then, for all
      action [a], s • (t,a) is atomic *)
  (** - Proof sketch : suppose that there exists some section [p] ranging from i to j in [s • (t,a)]
        and some event at position [k] between [i] and [j] perfomed by thread [t]. We prove that
        [t] belongs to the tribe of [p]. Suppose that [k=length(s)], otherwise the result is
        immediate by atomicity of [s].
        -- If [a = Open p] then the result is immediate
        -- If [a <> Open p] then [p] is pending in [s] thus [t] must belong to the tribe of [p] in [s] 
           otherwise [p] excludes [t] in [s], thus contradicting the hypothesis [~ conflict s t] *)
  
  Lemma noExclude_atomic : 
    forall s (H : atomic s) t a (HWF : wellFormed ( s • (t,a))), 
      ~ conflicts s t -> atomic (s • (t,a)).
  Proof.
    intros s h_atomic t a h_wf h_noExclude.
    assert (wellFormed s) as HWF by now apply wellFormed_se_s with (t,a).
    assert (wf_occurences s) as Hocc by (inversion HWF; trivial).
    assert (wf_fork s) as Hfork by (inversion HWF; trivial).
    assert (wf_open_close s) as Hopenclose by (inversion HWF; trivial).
    unfold atomic.
    intros p i j h_range k h_int t0 h_threadId.
    assert (j <= length s).
    {
      inversion h_range; subst.
      assert (j < length (s • (t,a))).
      eauto with nth_error.
      autorewrite with length in H; simpl in H.
      auto with *.
      autorewrite with length; simpl.
      auto with *.
    }
    destruct (Peano_dec.eq_nat_dec k (length s)); subst.
    - replace t0 with t by (autorewrite with nth_error in *; simpl in *; congruence).
      replace j with (length s) in * by auto with *.
      + destruct (eq_action_dec a (Open p)); [subst|].
        * constructor 1.
          exists (length s); autorewrite with nth_error; reflexivity.
        * assert (pending s p).
          {
            assert (i < length s).
            {
              assert (i <> length s).
              {
                intro; subst.
                inversion h_range; subst. 
                autorewrite with nth_error in Hi; simpl in Hi; congruence.
                rewrite H2 in Hi; autorewrite with nth_error in Hi; simpl in Hi; congruence.
              }
              auto with *.
            }
            apply range_last_se_pending_s with (t,a) i; auto with *.
          }
          destruct (tribe_dec s Hocc Hfork Hopenclose p t); [ now apply tribe_s_se |].
          contradict h_noExclude; (exists p); unfold exclude; tauto.
    - assert (tribe s p t0).
      {
        assert (exists j', range s p i j') as [j' Hb].
        {
          assert (a <> Open p).
          {
            contradict n; subst.
            assert (i = length s).
            {
              assert (action_of( pi i (s • (t, Open p)))==Open p).
              now inversion h_range.
              assert (action_of( pi (length s) (s • (t, Open p)))==Open p).
              autorewrite with nth_error; simpl; reflexivity.
              wellFormed_occurences (Open p).
            }
            subst.
            assert (k <= length s) by auto with *.
            auto with *.
          }
          destruct (range_se_s_neq_open) with s t a p i j; try (inversion h_wf; assumption).
          destruct H1.
          exists j.
          assumption.
          destruct H1.
          exists (length s - 1).
          assumption.
        }
         assert (i <= k <= j') as Ha.
        {
          split.
          apply h_int.
          inversion h_range; subst.
          - destruct (Compare_dec.lt_dec j (length s)).
            assert (action_of (pi j s) == Close p).
            assert (pi j (s • (t,a)) = pi j s) by eauto with nth_error.
            rewrite <- H0.
            assumption.
            assert (i < length s).
            auto with *.
            assert (pi i (s • (t,a)) = pi i s) by eauto with nth_error.
            assert (action_of (pi i s) == Open p).
            rewrite <- H2.
            assumption.
            assert (range s p i j).
            constructor 1; assumption.
            assert (i = i /\ j = j').
            apply range_functionnal with s p.
            assert (wellFormed s).
            apply wellFormed_se_s with (t,a).
            assumption.
            inversion H5.
            assumption.
            assumption.
            assumption.
            destruct H5; subst.
            apply h_int.
            assert (j = length s) by auto with *.
            subst.
            assert (i < length s) by auto with *.
            assert (action_of (pi i s) == Open p).
            assert (pi i (s • (t,a)) = pi i s) by eauto with nth_error.
            rewrite <- H1.
            assumption.
            assert (j' = length s - 1).
            {
              inversion Hb; subst.
              - assert (action_of (pi j' (s • (t,a))) == Close p).
                eauto with nth_error.
                assert (j' = length s).
                wellFormed_occurences (Close p).
                subst.
                assert (length s < length s) by eauto with nth_error.
                exfalso; intuition.
              - reflexivity.
            }
            subst.
            auto with *.
          - assert (~occursIn s (Close p)).
            {
              contradict HNotClosed.
              apply occursIn_s_se.
              assumption.
            }
            assert (j' = length s - 1).
            {
              inversion Hb; subst.
              elim H0.
              exists j'.
              assumption.
              reflexivity.
            }
            subst.
            destruct h_int.
            autorewrite with length in H2; simpl in H2.
            replace (length s + 1 - 1) with (length s) in H2 by lia.
            auto with *.
        }
        assert (threadId_of (pi k s) == t0).
        {
          assert ( k < length s) by auto with *.
          assert (pi k (s • (t,a)) = pi k s) by eauto with nth_error.
          rewrite <- H1.
          assumption.
        }
        now apply h_atomic with i j' k.
      }
      now apply tribe_s_se.
Qed.


  
  Lemma atomic_from : 
  forall s e,
    wellFormed (s • e) ->
    atomic s -> 
    forall m s',
      insertion m s e == s' ->
      forall p i j k t,
        range s' p i j ->
        i <= k <= j ->
        i <> m -> k <> m -> 
        threadId_of (pi k s') == t ->
        tribe s p t.
Proof.
  intros s  e h_wf h_atomic m s' h_insert p i j k t0 h_range h_int h_neq1 h_neq2 h_id.
  destruct (Compare_dec.lt_dec m i).
  - assert (m < k) by auto with *.
    assert (m < j) by auto with *.
    destruct i; [exfalso; auto with * |].
    destruct k; [exfalso; auto with * |].
    destruct j; [exfalso; auto with * |].
    assert (pi (S i) s' = pi i s) by
        (eapply insertion_ge;  [eauto | auto with *]). 
    assert (pi (S j) s' = pi j s) by
        (eapply insertion_ge;  [eauto | auto with *]). 
    assert (pi (S k) s' = pi k s) by
        (eapply insertion_ge;  [eauto | auto with *]). 
    inversion h_range; subst.
    + assert (range s p i j) by (constructor 1; congruence).
      assert (i <= k <= j) by auto with *.
      apply h_atomic with i j k; try assumption.
      rewrite <- H3; assumption.
    + assert (range s p i (length s - 1)).
      {
        constructor 2.
        congruence.
        contradict HNotClosed.
        assert (occursIn (s • e) (Close p)) by now apply occursIn_s_se.
        eapply insertion_occursIn; eauto.
      }
      apply h_atomic with i (length s - 1) k; try assumption.
      split.
      auto with *.
      assert (k < length s).
      {
        destruct (pi (S k) s').
        symmetry in H3.
        eauto with nth_error.
        discriminate.
      }
      auto with *.
      rewrite <- H3.
      assumption.
  - assert (i < m) by auto with *.
    assert (pi i s' = pi i s) by (eapply insertion_lt; eauto).
    destruct (Compare_dec.lt_dec m k).
    + assert (m < j) by auto with *.
      destruct k ; [exfalso; auto with *|].
      destruct j; [exfalso; auto with *|].
      assert (pi (S k) s' = pi k s) by
          (eapply insertion_ge;  [eauto | auto with *]). 
      assert (pi (S j) s' = pi j s) by
          (eapply insertion_ge;  [eauto | auto with *]). 
      inversion h_range; subst.
      * assert (i <= k <= j) by auto with *.
        apply h_atomic with i j k.
        constructor 1.
        rewrite <- H0.
        inversion h_range; assumption.
        rewrite <- H3; assumption.
        assumption.
        rewrite <- H2; assumption.
      * assert (i <= k <= length s - 1). 
        {
          split.
          auto with *.
          destruct (pi (S k) s').
          symmetry in H2.
          assert (k < length s).
          eauto with nth_error.
          auto with *.
          discriminate.
        }
        apply h_atomic with i (length s - 1) k.
        constructor 2.
        rewrite <- H0.
        inversion h_range; assumption.
        contradict HNotClosed.
        assert (occursIn (s • e) (Close p)) by eauto using occursIn_s_se.
        eapply insertion_occursIn; eauto.
        assumption.
        rewrite <- H2; assumption.
    + assert (k < m) by auto with *.
      assert (pi k s' = pi k s) by (eapply insertion_lt; eauto).
      inversion h_range; subst.
      * {
          destruct (Compare_dec.lt_eq_lt_dec m j) as [ [] | ].
          - destruct j; [exfalso; auto with *|].
            assert (pi (S j) s' = pi j s) by
                (eapply insertion_ge;  [eauto | auto with *]). 
            assert (i <= k <= j) by auto with *.
            assert (range s p i j).
            constructor 1.
            rewrite <- H0; inversion h_range; assumption.
            rewrite <- H3; assumption.
            apply h_atomic with i j k; try assumption.
            rewrite <- H2.
            assumption.
          - subst.
            assert (pi j s' == e)
            by now apply insertion_eq with s.
            assert (~ occursIn s (Close p)). 
            {
              intro.
              inversion H4 as [j0 ? Ha]; subst.
              assert (j0 < length s). 
              {
               case_eq (pi j0 s); intros; subst.
               eauto with nth_error.
               rewrite H5 in Ha; discriminate.
              }
              assert (action_of (pi j0 (s • e)) == Close p).
              eauto with nth_error.
              assert (j0 = length s).
              {
                assert (pi (length s) (s • e) == e).
                rewrite  nth_error_append_right.
                replace (length s - length s) with 0 by auto with *.
                reflexivity.
                auto with *.
                rewrite <- H3 in H7.
                rewrite <- H7 in Hj.
                wellFormed_occurences (Close p).
              }
              exfalso; auto with *.
            }
            assert (range s p i (length s - 1)).
            constructor 2.
            rewrite <- H0; assumption.
            assumption.
            assert (i <= k <= length s - 1). 
            {
              split.
              intuition.
              assert (k < length s).
              destruct (pi k s').
              symmetry in H2.
              eauto with nth_error.
              discriminate.
              auto with *.
            }
            apply h_atomic with i (length s - 1) k; try assumption.
            rewrite <- H2; assumption.
          -  assert (pi j s' = pi j s)by
                (eapply insertion_lt;eauto).
             assert (range s p i j).
             constructor 1.
             rewrite <- H0; assumption.
             rewrite <- H3; assumption.
             apply h_atomic with i j k; try assumption.
             rewrite <- H2; assumption.
        }
      * assert (~ occursIn s (Close p)). 
        {
          contradict HNotClosed.
          assert (occursIn (s • e) (Close p)) by now apply occursIn_s_se.
          eapply insertion_occursIn; eauto.
        }
        apply h_atomic with i (length s - 1) k.
        constructor 2.
        rewrite <- H0; assumption.
        assumption.
        split.
        intuition.
        assert (k < length s).
        destruct (pi k s').
        symmetry in H2.
        eauto with nth_error.
        discriminate.
        auto with *.
        rewrite <- H2; assumption.
Qed.
End Make.
