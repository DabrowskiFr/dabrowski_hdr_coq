Require Import Relation_Operators Operators_Properties Wf_nat.
Require Import sections.lifo.Prelude sections.traces.Trace_Theory.
Require Import sections.traces.EquivalenceTheory.
Require Import sections.common.Insertion.
Require Import List sections.lifo.ListBasics.
Require Import sections.lifo.BijRel.
Require Import Lia. 
Require Import sections.lifo.Length.

Module Make (P : MiniDecidableSet)
       ( Export Address: DecidableInfiniteSet) 
       ( Export T : Type_.TYPE Address )
       ( Export V : Value.TYPE Address T).
   
  Include EquivalenceTheory.Make P Address T V.
  
  (** * Properties of insertion *)
  (** ** Preservation of definitions *)

  (** *** Preservation of [occursIn] *)

  Lemma insertion_occursIn :
    forall s a i e s',
      insertion i s e == s' ->
      (occursIn (s • e) a <-> occursIn s' a).
  Proof.
    intros s a i e s' h_insertion.
    assert (i <= length s) by (eapply insertion_defined_rev; eauto).
    destruct insertion_rel_bijective with i (length s) 
      as [ _ _ h_applicative _ h_surjective]; try assumption.
    split.
    - intro h_occursIn.
      destruct h_occursIn as [k0 h_k0].
      assert (exists k1, insertion_rel i (length s) k0 k1) as [k1 h_k1].
      {
        assert (k0 < S (length s)).
        replace (S (length s)) with (length (s • e)).
        eauto with nth_error.
        autorewrite with length; simpl; lia.
        destruct (h_applicative k0); eauto.
      }
      exists k1.
      replace (pi k1 s') with (pi k0 (s • e)).
      assumption.
      now apply insertion_rel_insertion with i.
    - intro h_occursIn.
      destruct h_occursIn as [k1 h_k1].
      assert (exists k0, insertion_rel i (length s) k0 k1) as [k0 h_k0].
      {
        assert (k1 < S (length s)).
        replace (S (length s)) with (length s').
        eauto with nth_error.
        symmetry; eapply insertion_length; eauto.
        destruct (h_surjective k1); eauto.
      }
      exists k0.
      replace (pi k0 (s • e)) with (pi k1 s').
      assumption.
      symmetry; now apply insertion_rel_insertion with i.
  Qed.

  (** *** Preservation of [wf_occurences] *)
  
  Lemma insertion_wf_occurences :
    forall s i e s',
      wf_occurences (s • e) ->
      insertion i s e == s' ->
      wf_occurences s'.
  Proof.
    intros s i e s' h_wf_occ h_insert.
    unfold wf_occurences, occursAtMostOnce.
    intros a h_single i1 j1 h_eq1 h_eq2.
    assert (i <= length s) by (apply insertion_defined_rev with e; eauto).
    destruct insertion_rel_bijective with i (length s) 
      as [_ h_functional _ _ h_surjective]; try assumption.
    assert (exists i0, insertion_rel i (length s) i0 i1) as [i0 h_i0].
    {
      assert (i1 < S (length s)).
      {
        replace (S (length s)) with (length s').
        eauto with nth_error.
        symmetry; eapply insertion_length; eauto.
      }
      destruct (h_surjective i1); eauto.
    }
    assert (exists j0, insertion_rel i (length s) j0 j1) as [j0 h_j0].
    {
      assert (j1 < S (length s)).
      {
        replace (S (length s)) with (length s').
        eauto with nth_error.
        symmetry; eapply insertion_length; eauto.
      }
      destruct (h_surjective j1); eauto.
    }
    assert (action_of (pi i0 (s • e)) == a) as h_eq3.
    {
      assert (pi i0 (s • e) = pi i1 s') by now apply insertion_rel_insertion with i.
      congruence.
    }
    assert (action_of (pi j0 (s • e)) == a) as h_eq4.
    {
      assert (pi j0 (s • e) = pi j1 s') by now apply insertion_rel_insertion with i.
      congruence.
    }
    replace j0 with i0 in * by (eapply h_wf_occ; eauto).
    eapply h_functional; eauto.
  Qed.
  
  (** *** Preservation of  [father] *)

  Lemma insertion_father : 
    forall s e i t t' s',
      father (s • e) t' t ->
      insertion i s e == s' ->
      father s' t' t.
  Proof.
    intros s e i p t0 s' h_father h_insert.
    assert (i <= length s) by (apply insertion_defined_rev with e; eauto).
    destruct (insertion_rel_bijective) with i (length s)
      as [ _ _ h_applicative _ _]; try assumption.
    inversion h_father as [k0 [h_k_a h_k_b]].
    assert (exists k1, insertion_rel i (length s) k0 k1) as [k1 h_k1].
    {
      assert (k0 < S (length s)).
      replace (S (length s)) with (length (s • e)).
      eauto with nth_error.
      autorewrite with length; simpl; lia.
      destruct (h_applicative k0); eauto.
    }
    assert (pi k0 (s • e) = pi k1 s') by now apply insertion_rel_insertion with i.
    exists k1.
    split.
    rewrite <- H0.
    assumption.
    rewrite <- H0.
    assumption.
  Qed.

  Lemma insertion_father_rev : 
    forall s e i t t' s',
      father s' t' t ->
      insertion i s e == s' ->
      father (s•e) t' t.
  Proof.
    intros s e i p t0 s' h_father h_insert.
    assert (i <= length s) by (apply insertion_defined_rev with e; eauto).
    destruct (insertion_rel_bijective) with i (length s)
      as [ _ _ _ _ h_surjective]; try assumption.
    inversion h_father as [k0 [h_k_a h_k_b]].
    assert (exists k1, insertion_rel i (length s) k1 k0) as [k1 h_k1].
    {
      assert (k0 < S (length s)).
      replace (S (length s)) with (length s').
      eauto with nth_error.
      symmetry.
      now apply insertion_length with i e.
      destruct (h_surjective k0); eauto.
    }
    assert (pi k1 (s • e) = pi k0 s') by now apply insertion_rel_insertion with i.
    exists k1.
    split.
    rewrite  H0.
    assumption.
    rewrite  H0.
    assumption.
  Qed.

  (** *** Preservation of  [owns] *)

  Lemma insertion_owns :
    forall s e i p t s',
      owns (s • e) p t ->
      insertion i s e == s' ->
      owns s' p t.
  Proof.
    intros s e i p t0 s' h_owns h_insert.
    assert (i <= length s) by (apply insertion_defined_rev with e; eauto).
    destruct (insertion_rel_bijective) with i (length s)
      as [ _ _ h_applicative _ _]; try assumption.
    inversion h_owns as [? k0 ? h_k0_a h_k0_b]; subst.
    assert (exists k1, insertion_rel i (length s) k0 k1) as [k1 h_k1].
    {
      assert (k0 < S (length s)).
      replace (S (length s)) with (length (s • e)).
      eauto with nth_error.
      autorewrite with length; simpl; lia.
      destruct (h_applicative k0); eauto.
    }
    assert (pi k0 (s • e) = pi k1 s') by now apply insertion_rel_insertion with i.
    exists k1.
    rewrite <- H0.
    assumption.
    rewrite <- H0.
    assumption.
  Qed.

  Lemma insertion_owns_rev :
    forall s e i p t s',
      owns s' p t ->
      insertion i s e == s' ->
      owns (s • e) p t.
  Proof.
    intros s e i p t0 s' h_owns h_insert.
    assert (i <= length s) by (apply insertion_defined_rev with e; eauto).
    destruct (insertion_rel_bijective) with i (length s)
      as [ _ _ _ _ h_surjective]; try assumption.
    inversion h_owns as [? k0 ? h_k0_a h_k0_b]; subst.
    assert (exists k1, insertion_rel i (length s) k1 k0) as [k1 h_k1].
    {
      assert (k0 < S (length s)).
      replace (S (length s)) with (length s').
      eauto with nth_error.
      symmetry.
      now apply insertion_length with i e.
      destruct (h_surjective k0).
      assumption.
      exists x.
      assumption.
    }
    assert (pi k1 (s • e) = pi k0 s') by now apply insertion_rel_insertion with i.
    exists k1.
    rewrite H0.
    assumption.
    rewrite H0.
    assumption.
  Qed.

  (** *** Preservation of [tribeChildren] *)

  Lemma insertion_tribeChildren : 
    forall s i t0 a s',
      wellFormed (s • (t0,a)) ->
      insertion i s (t0,a) == s' ->
      conflicts s t0 ->
      (forall k, i <= k < length s -> ~ synchronizeWith (s • (t0,a)) k (length s)) ->
      forall p t, tribeChildren (s • (t0,a)) p t -> tribeChildren s' p t.
  Proof.
    intros s i t0 a s' H H0 H1 H2 p t1 H3.
    induction H3.
    assert (j < S (length s)) as h_lt_j.
    {
      inversion H3; subst.
      - replace (S (length s)) with (length (s • (t0,a))).
        eauto with nth_error.
        autorewrite with length; simpl; lia.
      - autorewrite with length; simpl; lia.
    }
    assert (exists i1, insertion_rel i (length s) i0 i1) as [i1 h_i1].
    {
      assert (i0 < S (length s)) as h_lt by intuition.
      assert (applicative (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
      {
        assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
        now destruct (insertion_rel_bijective _ _ h_lt2).
      }
      now apply h_app.
    }
    assert (exists k1, insertion_rel i (length s) k k1) as [k1 h_k1].
    {
      assert (k < S (length s)) as h_lt by intuition.
      assert (applicative (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
      {
        assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
        now destruct (insertion_rel_bijective _ _ h_lt2).
      }
      now apply h_app.
    }
    assert (exists j1, insertion_rel i (length s) j j1) as [j1 h_j1].
    {
      assert (k < S (length s)) as h_lt by intuition.
      assert (applicative (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
      {
        assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
        now destruct (insertion_rel_bijective _ _ h_lt2).
      }
      now apply h_app.
    }
    assert (i1 < k1 <= length s' - 1).
    {
      assert (i1 < k1).
      {
        destruct (Peano_dec.eq_nat_dec k (length s)).
        - subst.
          assert (threadId_of (pi i0 (s • (t0, a))) == t1).
          {
            assert (action_of (pi i0 (s • (t0,a))) == Open p) by now (inversion H3). 
            inversion H4; subst.
            assert (i0 = i2) by wellFormed_occurences (Open p).
            subst; assumption.
          }
          subst.
          assert (k1 = i).
          {
            assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
            eapply insertion_rel_fst_last; eauto.
          }
          subst.
          assert (i0 < i).
          {
            assert (synchronizeWith (s • (t0,a)) i0 (length s)).
            {
              constructor 1.
              constructor 1 with t1; intuition. 
            }
            destruct (Compare_dec.lt_dec i0 i); [assumption|].
            elim (H2 i0); intuition. 
          }
          assert (i0 = i1).
          {
            assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
            now apply insertion_rel_fst_left with i (length s).
          }
          congruence.
        - assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
          eapply insertion_order; eauto.
          intuition.
      }
      assert (k1 <= length s' - 1).
      {
        assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
        destruct insertion_rel_lt with i (length s) k k1.
        assumption.
        assumption.
        replace (length s') with (S (length s)).
        intuition.
        eapply insertion_length; eauto.
      }
      intuition.
    }
    assert (owns s' p t1) by (eapply insertion_owns; eauto).
    assert (pi k1 s' == (t1, Fork t')) as h_eq.
    {
      assert (pi k (s • (t0, a)) = pi k1 s').
      eapply insertion_rel_insertion; eauto.
      rewrite <- H10.
      case_eq (pi k (s • (t0, a))); intros; subst.
      destruct p0.
      unfold Event.t in *; rewrite H11 in H6, H7.
      injection H6; injection H7; intros; subst.
      reflexivity.
      unfold Event.t in *; rewrite H11 in H6; discriminate.
    }
    destruct (Peano_dec.eq_nat_dec k (length s)).
    - subst.
      assert (~ occursIn s' (Close p)).
      {
        inversion H3; subst.
        - assert (j = length s).
          {
            assert (j < length (s • (t0,a))) as h_lt by eauto with nth_error.
            autorewrite with length in h_lt; simpl in h_lt.
            intuition.
          }
          subst.
          rewrite H7 in Hj.
          discriminate.
        - contradict HNotClosed.
          eapply insertion_occursIn; eauto.
      }
      assert (range s' p i1 (length s' -1)).
      {
        assert (action_of (pi i1 s') == Open p).
        {
          assert (action_of (pi i0 (s • (t0, a))) == Open p) by now inversion H3.
          assert (pi i0 (s • (t0, a)) = pi i1 s') by (eapply insertion_rel_insertion; eauto).
          congruence.
        }
        now constructor 2.
      }
      constructor 1 with i1 (length s' -1) t1 k1; try assumption.
      unfold Event.t in *; rewrite h_eq; reflexivity.
      unfold Event.t in *; rewrite h_eq; reflexivity.
    - assert (action_of (pi i1 s') == Open p).
      {
        assert (action_of (pi i0 (s • (t0, a))) == Open p) by now inversion H3.
        assert (pi i0 (s • (t0, a)) = pi i1 s') by (eapply insertion_rel_insertion; eauto).
        congruence.
      }
      assert (pi k1 s' == (t1, Fork t')) by assumption.
      destruct (Peano_dec.eq_nat_dec j (length s)).
      + subst.
        assert (j1 = i).
        {
          assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
          eapply insertion_rel_fst_last; eauto.
        }
        inversion H3; subst.
        * assert (k < i).
          {
            assert (synchronizeWith (s • (t0, a)) k (length s)).
            {
              assert (t0 = t1).
              {
                inversion H.
                destruct (WF4 _ _ Hj) as [i2 [Hu [Hv Hw]]].
                assert (i2 = i0) by wellFormed_occurences (Open p).
                subst.
                inversion H4; subst.
                assert (i2 = i0) by wellFormed_occurences (Open p).
                subst.
                autorewrite with nth_error in Hw.
                rewrite HThreadOf in Hw.
                simpl in Hw; congruence.
              }
              subst.
              constructor 1.
              constructor 1 with t1.
              intuition.
              assumption.
              autorewrite with nth_error; reflexivity.
            }
            destruct (Compare_dec.lt_dec k i); [assumption|].
            assert (i <= k < length s) by intuition.
            elim (H2 k); eauto.
          }
          assert (k = k1).
          {
            assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
            now apply insertion_rel_fst_left with i (length s).
          }
          subst.
          assert (i0 = i1).
          {
            assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
            apply insertion_rel_fst_left with i (length s); intuition.
          }
          subst.
          assert (t0 = t1).
          {
            inversion H.
            destruct (WF4 _ _ Hj) as [i2 [Hu [Hv Hw]]].
            assert (i2 = i1) by wellFormed_occurences (Open p).
            subst.
            inversion H4; subst.
            assert (i1 = i0) by wellFormed_occurences (Open p).
            subst.
            autorewrite with nth_error in Hw.
            rewrite HThreadOf in Hw.
            simpl in Hw; congruence.
          }
          subst.
          assert (action_of (pi i s') == Close p).
          {
            assert (pi i s' = pi (length s) (s • (t1, a))).
            symmetry.
            apply insertion_rel_insertion with i.
            assumption.
            constructor 3.
            unfold Event.t in *; rewrite H13.
            assumption.
          }
          constructor 1 with i1 i t1 k1.
          constructor 1.
          assumption.
          assumption.
          eapply insertion_owns; eauto.
          intuition.
          unfold Event.t in *; rewrite H11; reflexivity.
          unfold Event.t in *; rewrite H11; reflexivity.
        * constructor 1 with i1 (length s' - 1) t1 k1.
          constructor 2.
          assumption.
          contradict HNotClosed.
          eapply insertion_occursIn.
          apply H0.
          assumption.
          eapply insertion_owns; eauto.
          assumption.
          unfold Event.t in *; rewrite H11; reflexivity.
          unfold Event.t in *; rewrite H11; reflexivity.
      +   assert (action_of (pi j (s • (t0, a))) == Close p).
          {
            assert (j < length s) by intuition.
            inversion H3; subst.
            assumption.
            autorewrite with length in H12; simpl in H12.
            exfalso; lia.
          }
          assert (pi j (s • (t0, a)) = pi j1 s').
          {
            eapply insertion_rel_insertion; eauto.
          }
          constructor 1 with i1 j1 t1 k1.
          constructor 1.
          assumption.
          unfold Event.t in *; congruence.
          eapply insertion_owns; eauto.
          split.
          intuition.
          assert (k1 < j1).
          {
            destruct (Peano_dec.eq_nat_dec k j).
            {
              subst.
              unfold Event.t in *; rewrite H7 in H12.
              discriminate.
            }
            assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
            apply insertion_order with i (length s) k j.
            assumption.
            assumption.
            assumption.
            intuition.
            assumption.
          }
          intuition.
          unfold Event.t in *; rewrite H11; reflexivity.
          unfold Event.t in *; rewrite H11; reflexivity.
    - constructor 2 with t1.
      assumption.
      now apply insertion_father with s (t0,a) i.
  Qed.

  Lemma insertion_tribeChildren_rev : 
    forall s i t0 a s',
      wellFormed (s • (t0,a)) ->
      insertion i s (t0,a) == s' ->
      conflicts s t0 ->
      (forall k, i <= k < length s -> ~ synchronizeWith (s • (t0,a)) k (length s)) ->
      forall p t, tribeChildren s' p t -> tribeChildren (s • (t0,a)) p t.
  Proof.
    intros s i t0 a s' h_wf h_insert h_conflict h_nosync p t1 h_tc.
    assert (wf_occurences s') 
      as h_wf_occ by
          (eapply insertion_wf_occurences; inversion h_wf; eauto).
    induction h_tc.
    - assert (j < length s').
      {
        inversion H; subst.
        eauto with nth_error.
        destruct s'; [ destruct k; simpl in *; discriminate |].
        intuition.
      }
      assert (S (length s) = length s') by now apply insertion_length with i (t0,a).
      assert (exists i1, insertion_rel i (length s) i1 i0) as [i1 h_i1].
      {
        assert (i0 < length s') as h_lt by intuition.
        assert (surjective (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
        {
          assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
          now destruct (insertion_rel_bijective _ _ h_lt2).
        }
        apply h_app; congruence.
      }
      assert (exists k1, insertion_rel i (length s) k1 k) as [k1 h_k1].
      {
        assert (i0 < length s') as h_lt by intuition.
        assert (surjective (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
        {
          assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
          now destruct (insertion_rel_bijective _ _ h_lt2).
        }
        apply h_app; intuition.
      }
      assert (exists j1, insertion_rel i (length s) j1 j) as [j1 h_j1].
      {
        assert (i0 < length s') as h_lt by intuition.
        assert (surjective (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
        {
          assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
          now destruct (insertion_rel_bijective _ _ h_lt2).
        }
        apply h_app; congruence.
      }
      assert (pi i0 s' == (t1, Open p)) as h_i0.
      {
        assert (action_of (pi i0 s') == Open p) by now inversion H.
        inversion H0; subst.
        assert (i0 = i2) by wellFormed_occurences (Open p); subst.
        case_eq (pi i2 s'); [intros [t a0] h_eq | intros h_none]; subst.
        unfold Event.t in *; rewrite h_eq in HThreadOf, HActionOf.
        simpl in HThreadOf, HActionOf.
        congruence.
        unfold Event.t in *; rewrite h_none in HThreadOf.
        discriminate.
      }
      assert (pi k s' == (t1, Fork t')) as h_k.
      {
        case_eq (pi k s'); [intros [t a0] h_eq | intros h_none]; subst.
        unfold Event.t in *; rewrite h_eq in H2, H3.
        simpl in H2, H3.
        congruence.
        unfold Event.t in *; rewrite h_none in H2.
        discriminate.
      }
      assert (pi i1 (s • (t0,a)) == (t1, Open p)) 
        as h_i1b
          by (rewrite <- h_i0; now apply insertion_rel_insertion with i).
      assert (pi k1 (s • (t0,a))  == (t1, Fork t')) 
        as h_k1b 
          by (rewrite <- h_k; now apply insertion_rel_insertion with i).
      assert (i <= length s) as h_le_i by (eapply insertion_defined_rev; eauto).
      assert (i1 < k1).
      {
        destruct (Compare_dec.lt_dec i1 k1); [assumption|].
        assert (k1 < i1).
        {
          assert (k1 <> i1) by (intro; subst; rewrite h_i1b in h_k1b; discriminate).
          intuition.
        }
        destruct (Peano_dec.eq_nat_dec i1 (length s)).
        - subst.
          assert (i0 = i) by (eapply insertion_rel_fst_last; eauto).
          destruct (Compare_dec.lt_dec k1 i).
          + assert (k1 = k) by now apply insertion_rel_fst_left with i (length s).
            subst; exfalso; intuition.
          + assert (i <= k1 < length s) by intuition.
            assert (synchronizeWith (s • (t0, a)) k1 (length s)).
            {
              constructor 1.
              constructor 1 with t1; [intuition | rewrite h_k1b; reflexivity | rewrite h_i1b; reflexivity].
            }
            now elim (h_nosync k1).
        - assert (k < i0) by now apply insertion_order with i (length s) k1 i1.
          exfalso; intuition.
      }
      
      inversion H; subst.
      + assert (pi j1 (s • (t0,a)) = pi j s')
          by (eapply insertion_rel_insertion; eauto).
        assert (pi j1 (s • (t0,a)) == (t1, Close p)).
        {
          assert (action_of (pi j1 (s • (t0,a))) == Close p).
          rewrite H7.
          unfold Event.t in *; rewrite Hj; reflexivity.
          inversion h_wf.
          destruct (WF4 _ _ H8) as [i2 [Hu [Hv Hw]]].
          assert (i2 = i1).
          {
            assert (action_of (pi i1 (s • (t0,a))) == Open p).
            rewrite h_i1b; reflexivity.
            wellFormed_occurences (Open p).
          }
          subst.
          case_eq (pi j1 (s • (t0,a))); [intros [tm htm] h_eq | intros]; subst.
          unfold Event.t in *; rewrite h_eq in Hw; rewrite h_i1b in Hw; simpl in Hw.
          rewrite h_eq in H8; simpl in H8.
          congruence.
          rewrite H9 in H8; discriminate.
        }
        assert (k1 < j1).
        {
          destruct (Compare_dec.lt_dec k1 j1); [assumption|].
          assert (j1 < k1).
          {
            assert (k1 <> j1).
            intro; subst.
            unfold Event.t in *; rewrite H8 in h_k1b; discriminate.
            intuition.
          }
          destruct (Peano_dec.eq_nat_dec k1 (length s)).
          - subst.
            assert (k = i).
            {
              now apply insertion_rel_fst_last with (length s).
            }
            assert (synchronizeWith (s • (t0,a)) j1 (length s)).
            {
              constructor 1.
              constructor 1 with t1.
              assumption.
              rewrite H8; reflexivity.
              rewrite h_k1b; reflexivity.
            }
            assert (j1 < i).
            {
              destruct (Compare_dec.lt_dec j1 i);[assumption|].
              elim (h_nosync j1); intuition.
            }
            assert (j1 = j).
            now apply insertion_rel_fst_left with i (length s).
            subst.
            exfalso; intuition.
          - assert (j < k).
            now apply insertion_order with i (length s) j1 k1.
            exfalso; intuition.
        }
        constructor 1 with i1 j1 t1 k1.
        constructor 1.
        unfold Event.t in *; rewrite h_i1b; reflexivity.
        unfold Event.t in *; rewrite H8; reflexivity.
        eapply insertion_owns_rev; eauto.
        intuition.
        unfold Event.t in *; rewrite h_k1b; reflexivity.
        unfold Event.t in *; rewrite h_k1b; reflexivity.
      + constructor 1 with i1 (length (s • (t0,a)) - 1) t1 k1.
        constructor 2.
        unfold Event.t in *; rewrite h_i1b; reflexivity.
        contradict HNotClosed.
        eapply insertion_occursIn; eauto.
        eapply insertion_owns_rev; eauto.
        replace (length (s • (t0, a))) with (length s').
        intuition.
        assert (k1 < length (s • (t0,a))) by eauto with nth_error.
        autorewrite with length in H1; simpl in H1.
        intuition.
        symmetry; replace (length (s • (t0,a))) with (S (length s)).
        eapply insertion_length;eauto.
        autorewrite with length; simpl; lia.
        unfold Event.t in *; rewrite h_k1b; reflexivity.
        unfold Event.t in *; rewrite h_k1b; reflexivity.
    - constructor 2 with t1.
      assumption.
      now apply insertion_father_rev with i s'.
  Qed.

  (** *** Preservation of [tribe] *)

  Lemma insertion_tribe : 
    forall s i t0 a s',
      wellFormed (s • (t0,a)) ->
      insertion i s (t0,a) == s' ->
      conflicts s t0 ->
      (forall k, i <= k < length s -> ~ synchronizeWith (s • (t0,a)) k (length s)) ->
      forall p t, tribe (s • (t0,a)) p t -> tribe s' p t.
  Proof.
    intros s i t0 a s' H H0 H1 H2 p t1 H3.
    inversion H3.
    - constructor 1.
      eapply insertion_owns; eauto.
    - constructor 2.
      eapply insertion_tribeChildren; eauto.
  Qed.

  Lemma insertion_tribe_rev : 
    forall s i t0 a s',
      wellFormed (s • (t0,a)) ->
      insertion i s (t0,a) == s' ->
      conflicts s t0 ->
      (forall k, i <= k < length s -> ~ synchronizeWith (s • (t0,a)) k (length s)) ->
      forall p t, tribe s' p t -> tribe (s • (t0,a)) p t.
  Proof.
    intros s i t0 a s' H H0 H1 H2 p t1 H3.
    inversion H3.
    - constructor 1.
      eapply insertion_owns_rev; eauto.
    - constructor 2.
      eapply insertion_tribeChildren_rev; eauto.
  Qed.
  

  (** *** Preservation of [seq_order] *)

  Lemma insertion_sec_order :
    forall s i t a s' p p',
      wellFormed (s • (t,a)) ->
      insertion i s (t,a) == s' ->
      conflicts s t ->
      (forall k, i <= k < length s -> ~ synchronizeWith (s • (t,a)) k (length s)) ->
      (sec_order (s • (t,a)) p p' <-> sec_order s' p p').
 Proof.
   intros s i t0 a s' p p' Hwf Hi Hc Hns.
   assert (wf_occurences s') as Hwf_ocs' by (eapply insertion_wf_occurences;inversion Hwf;eauto).
   split.
   (*   ----------->                                                           *)
   - intros Hso.
     inversion Hso as [p0 i0 j0 k0 p'0 Hr Hleq Hk Heqt | i0 k0 p0 p0' t Hi0 Hk0 Ht Htr];subst.
     + (**  sec_order_cons_dir **) 
       assert (j0 < S (length s)) as h_lt_j.
        {
          inversion Hr; subst.
          - replace (S (length s)) with (length (s • (t0,a))).
            eauto with nth_error.
            autorewrite with length; simpl; lia.
          - autorewrite with length; simpl; lia.
        } 
       assert (exists i1, insertion_rel i (length s) i0 i1) as [i1 h_i1].
        {
          assert (i0 < S (length s)) as h_lt by intuition.
          assert (applicative (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
          {
            assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
            now destruct (insertion_rel_bijective _ _ h_lt2).
          }
          now apply h_app.
        }
        assert (exists k1, insertion_rel i (length s) k0 k1) as [k1 h_k1].
        {
          assert (k0 < S (length s)) as h_lt by intuition.
          assert (applicative (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
          {
            assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
            now destruct (insertion_rel_bijective _ _ h_lt2).
          }
          now apply h_app.
        }
        assert (exists j1, insertion_rel i (length s) j0 j1) as [j1 h_j1].
        {
          assert (k0 < S (length s)) as h_lt by intuition.
          assert (applicative (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
          {
            assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
            now destruct (insertion_rel_bijective _ _ h_lt2).
          }
          now apply h_app.
        }
         assert (action_of (pi i0 (s • (t0, a))) == Open p) as Hi0.
        {
          inversion Hr;auto.
        }
        assert (action_of (pi i1 s') == Open p) as Hi1.
        {
          assert (pi i0 (s • (t0, a)) = pi i1 s') by (eapply insertion_rel_insertion; eauto).
          congruence.
        }
        assert (action_of (pi k1 s') == Open p') as Hk1.
        {
          assert (pi k0 (s • (t0, a)) = pi k1 s') by (eapply insertion_rel_insertion; eauto).
          rewrite <- H. assumption.
        }
        assert (threadId_of (pi i1 s') = threadId_of (pi k1 s')) as Heqt'.
        {
          assert (pi i0 (s • (t0, a)) = pi i1 s') as H1 by (eapply insertion_rel_insertion; eauto).
          assert (pi k0 (s • (t0, a)) = pi k1 s') as H2 by (eapply insertion_rel_insertion; eauto).
          rewrite <- H1. 
          rewrite <- H2.
          assumption.
        }

        assert (i1<=k1) as Hleqi.
        {
          
          destruct (P.eq_dec p p') as [Heqpp' | Hneqpp'].
          - subst.
             
               
               assert (i1 =k1) as Heqi1k1.
               { 
                 wellFormed_occurences (Open p').
               }
               intuition.
            - 
              assert (i1 <> k1) as Hdi1k1. 
              {
                contradict Hneqpp'.
                subst.
                congruence.
              }
              destruct (Peano_dec.eq_nat_dec k0 (length s)).
              + subst.
                assert (threadId_of (pi i0 (s • (t0, a))) == t0).
                { 
                  autorewrite with nth_error in Heqt.
                  simpl in Heqt.
                  assumption.
                }
                subst.
                assert (k1 = i) as Heqk1i.
                {
                  assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
                  eapply insertion_rel_fst_last; eauto.
                }
                subst.
                assert (i0 <> (length s)) as Hdii0lgt. 
                {
                   intro Hn;subst.
                   autorewrite with nth_error in Hk;simpl in Hk;inversion Hk;subst.
                   autorewrite with nth_error in Hi0;simpl in Hi0;inversion Hi0;subst.
                   
                   contradict Hneqpp'.
                   auto.
                }
                assert (i0 < i).
                {
                  assert (synchronizeWith (s • (t0,a)) i0 (length s)).
                  {
                    constructor 1.
                    constructor 1 with t0;intuition. 
                    autorewrite with nth_error;simpl;auto.
                  }
                  destruct (Compare_dec.lt_dec i0 i); [assumption|].
                  elim (Hns i0); intuition. 
                }
                assert (i0 = i1).
                {
                  assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
                  now apply insertion_rel_fst_left with i (length s).
                }
                subst.
                lia.
              +  assert (i0 <> k0) as Hi0k0. {
                   intro Hn;subst.
                   assert (Some (Open p') = Some (Open p)) as Ho.
                   {
                     rewrite <- Hi0;rewrite <- Hk.
                     auto.
                   }
                   inversion Ho.
                   contradict Hneqpp';auto.
                 }
                assert (i1 <k1) as Hi1k1. 
                { apply insertion_order with i (length s) i0 k0;intuition.
                  eapply insertion_defined_rev; eauto.
                }
                lia.
        }
        inversion Hr;subst.
        * 
          assert (k1<=j1) as Hleqj.
          {
         
            destruct (Peano_dec.eq_nat_dec j0 (length s)) as [Hj0l | Hjol].
            + subst.
              assert (j1 = i) as Hj1i.  
              {
                assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
                eapply insertion_rel_fst_last; eauto.
              }
              assert ( threadId_of (pi (length s) (s • (t0, a))) ==t0) as Htlgt.
              {
                autorewrite with nth_error;simpl;auto.
              }
              assert ( threadId_of (pi i0 (s • (t0, a))) ==t0) as Hti0.
              {
                inversion Hwf.
                destruct WF4 with  (length s) p as [x0 [H1 [H2 H3]]];auto.
                assert (x0 = i0) by  wellFormed_occurences (Open p);subst.
                
                autorewrite with nth_error in H3. simpl in H3;auto.
              }
              assert (k0<i) as Hki. 
              {
                assert (k0<> length s) as Hdk0lgt. 
                {
                  intro Hn;subst.
                  autorewrite with nth_error in Hk;simpl in Hk;inversion Hk;subst.
                  autorewrite with nth_error in Hj;simpl in Hj;inversion Hj;subst.
                }
                assert (synchronizeWith (s • (t0,a)) k0 (length s)).
                {
                  constructor 1.
                  constructor 1 with t0; intuition. 
                  rewrite <- Hti0.
                  auto.
                }
                destruct (Compare_dec.lt_dec k0 i); [assumption|].
                elim (Hns k0); intuition.
              }
              assert (k0 =k1) as Heqk. 
              {
                assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
                now apply insertion_rel_fst_left with i (length s).
              }
              subst.
              lia.
            + assert (k1 < j1).
              {
                apply insertion_order with i (length s) k0 j0;intuition.
                eapply insertion_defined_rev; eauto.
                assert (k0 <> j0) as Hneqk0j0.
                {
                  intro Hn;subst.
                  rewrite Hk in Hj. inversion Hj.
                }
                lia.
              }
              lia.
          }
          assert (range s' p i1 j1) as Hr'.
          {
            constructor 1;auto.
            assert (pi j0 (s • (t0, a)) = pi j1 s') by (eapply insertion_rel_insertion; eauto).
            rewrite <- Hj.
            f_equal;auto.
          }
          constructor 1 with i1 j1 k1;auto.
        * assert (range s' p i1 (length s'-1)) as Hr'.
          {
            constructor 2;auto.
            contradict HNotClosed.
            eapply insertion_occursIn; eauto.
          }
          assert (k1 <= (length s'-1)) as Hlgt.
          {
            assert (k1 < length s') by   eauto with nth_error.
            lia.
          }
          constructor 1 with i1 (length s'-1) k1;auto.
     + (** sec_order_cons_ind **)


       assert (exists i1, insertion_rel i (length s) i0 i1) as [i1 h_i1].
        {
          assert (i0 < (length (s • (t0, a)))) as h_lt1 by eauto with nth_error.
          assert (i0 < S (length s)) as h_lt by (autorewrite with length in h_lt1;simpl in h_lt1;lia).
          assert (applicative (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
          {
            assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
            now destruct (insertion_rel_bijective _ _ h_lt2).
          }
          now apply h_app.
        }
        assert (exists k1, insertion_rel i (length s) k0 k1) as [k1 h_k1].
        {

          assert (k0 < length (s • (t0, a))) as h_lt1 by (eauto with nth_error).
          assert (k0 < S (length s)) as h_lt by (autorewrite with length in h_lt1;simpl in h_lt1;lia).

          assert (applicative (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
          {
            assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
            now destruct (insertion_rel_bijective _ _ h_lt2).
          }
          now apply h_app.
        }
        assert (action_of (pi i1 s') == Open p) as Hi1. 
        {
          assert (pi i0 (s • (t0, a)) = pi i1 s') as H by (eapply insertion_rel_insertion; eauto).
          rewrite <- H.
          assumption.
        }
        assert (action_of (pi k1 s') == Open p') as Hk1. 
        {
          assert (pi k0 (s • (t0, a)) = pi k1 s') as H by (eapply insertion_rel_insertion; eauto).
          rewrite <- H.
          assumption.
        }
        assert (threadId_of (pi k1 s') == t) as Hk1t. 
        {
          assert (pi k0 (s • (t0, a)) = pi k1 s') as H by (eapply insertion_rel_insertion; eauto).
          rewrite <- H.
          assumption.
        }
        assert (tribeChildren s' p t) as HtrC. 
        { apply insertion_tribeChildren with s i t0 a;auto.
        }
        constructor 2 with i1 k1 t;auto.



   - (*                      <-------------                     *)
     intros Hso.
     inversion Hso as [p0 i0 j0 k0 p'0 Hr Hleq Hk Heqt | i0 k0 p0 p0' t Hi0 Hk0 Ht Htr] ;subst.
     +  (*sec_order_cons_dir*)
       assert (S (length s) = length s') by now apply insertion_length with i (t0,a).
       assert (action_of (pi i0 s') == Open p) as Hi0.
        {
          inversion Hr;auto.
        }

       assert (exists i1, insertion_rel i (length s) i1 i0) as [i1 h_i1].
       {
         assert (i0 < length s') as h_lt  by eauto with nth_error.
         assert (surjective (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
         {
           assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
          now destruct (insertion_rel_bijective _ _ h_lt2).
         }
         apply h_app; congruence.
       }
      assert (exists k1, insertion_rel i (length s) k1 k0) as [k1 h_k1].
      {
        assert (k0 < length s') as h_lt by eauto with nth_error.
        assert (surjective (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
        {
          assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
          now destruct (insertion_rel_bijective _ _ h_lt2).
        }
        apply h_app; intuition.
      }
     
      assert (exists j1, insertion_rel i (length s) j1 j0) as [j1 h_j1].
      {
        assert (j0 < length s') as h_lt. 
        {
          inversion Hr;eauto with nth_error.
          intuition.
        }
        assert (surjective (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
        {
          assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
          now destruct (insertion_rel_bijective _ _ h_lt2).
        }
        apply h_app; congruence.
      }



        
        assert (action_of (pi i1  (s • (t0, a))) == Open p) as Hi1.
        {
          assert ( pi i1 (s • (t0, a))=(pi i0 s')) as H0 by (eapply insertion_rel_insertion; eauto).
          
          congruence.
        }       
        assert (action_of (pi k1 (s • (t0, a))) == Open p') as Hk1.
        {
          assert (pi k1 (s • (t0, a)) = pi k0 s') as H0 by (eapply insertion_rel_insertion; eauto).
          rewrite  H0. assumption.
        }
        assert (threadId_of (pi i1 (s • (t0, a))) = threadId_of (pi k1 (s • (t0, a)))) as Heqt'.
        {
          assert (pi i1 (s • (t0, a)) = pi i0 s') as H1 by (eapply insertion_rel_insertion; eauto).
          assert (pi k1 (s • (t0, a)) = pi k0 s') as H2 by (eapply insertion_rel_insertion; eauto).
          rewrite  H1. 
          rewrite  H2.
          assumption.
        }
        assert (pi i s' == (t0, a)) as h_i_s' by now apply insertion_eq with s.
      destruct (P.eq_dec p p') as [Heqpp' | Hneqpp'].
      * (*p = p'*)
        subst.
        assert (i <= length s) as h_le_i by (eapply insertion_defined_rev; eauto).
        assert (i0 = k0) as Hi0k0 by wellFormed_occurences (Open p');subst.
        assert (i1 = k1) as Hi1k1 by wellFormed_occurences (Open p');subst.
        assert (k0 <> i) as Hdifii0. 
        {
          intro Hn;subst.
          assert (a = Open p').
          {
            assert (action_of (pi i s') == Open p') as h_open by now inversion Hr.
            rewrite h_i_s' in h_open; simpl in h_open; congruence.
          }
          eelim wellFormed_open_in; eauto.
        }
        inversion Hr;subst.
        {
          assert (k0 <> j0) as Hk0j0. 
          {
            intro Hn;subst.
            assert (Some (Open p') = Some (Close p')) as H1.
            {
            rewrite <- Hk.
            rewrite <- Hj.
            auto.
            }
            inversion H1.
          }

          assert(k1<=j1). 
          {
            destruct (Peano_dec.eq_nat_dec j0 i) as [Hj0i | Hj0i].
            - subst.
              assert (j1 = length s) as Hj1lgt by now apply insertion_rel_snd_middle with i;subst.
              assert (k1 < length (s • (t0, a))) as Hk1l  by eauto with nth_error.
              replace (length (s • (t0, a))) with (S (length s)) in Hk1l by ( autorewrite with length;simpl;lia).
              lia.
              
            -  assert (k1 <j1). 
               apply insertion_order_rev with i (length s) k0 j0 ;auto;lia.
               lia.
          }
          assert (action_of (pi j1 (s • (t0, a))) == Close p') as Hj1. 
          {
            assert (pi j1 (s • (t0, a)) = pi j0 s') as Hpij by (eapply insertion_rel_insertion; eauto).
            rewrite  Hpij;assumption.
          }
          assert (range (s • (t0, a)) p' k1 j1 ) as Hr1.
          {
            constructor 1;auto.
          }
          
          constructor 1 with k1 j1 k1;auto.
        }          
        
        assert (range  (s • (t0, a)) p' k1 (length  (s • (t0, a)) -1)) as Hr'.
          {
            constructor 2;auto.
            contradict HNotClosed.
            eapply insertion_occursIn; eauto.
          }
          assert (k1 <= (length  (s • (t0, a)) -1)) as Hlgt.
          {
            assert (k1 < (length  (s • (t0, a)) )) by   eauto with nth_error.
            lia.
          }
          constructor 1 with k1 (length  (s • (t0, a)) -1) k1;auto.
      * (*i0 <> k0, i1<> k1*)
        assert (i <= length s) as h_le_i by (eapply insertion_defined_rev; eauto).
        assert (i0 <> k0) as hdifi0k0. 
        {
          intro Hn;subst.
          assert (Some (Open p') = Some (Open p)) as Hpp'.
          rewrite <- Hk;rewrite <- Hi0;auto.
          inversion Hpp';contradict Hneqpp';auto.
        }
        assert (i1 <> k1) as hdifi1k1. 
        {
         intro Hn;subst.
         assert (Some (Open p') = Some (Open p)) as Hpp'.
         rewrite <- Hi1;rewrite <- Hk1;auto.
         inversion Hpp';contradict Hneqpp';auto.
        }
        assert (i0 <> i) as Hdifii1. 
        {
          intro Hn;subst.
          assert (a = Open p).
          {
            assert (action_of (pi i s') == Open p) as h_open by now inversion Hr.
            rewrite h_i_s' in h_open; simpl in h_open; congruence.
          }
          eelim wellFormed_open_in; eauto.
        }
        assert (k0 <> i) as Hdifik0. 
        {
          intro Hn;subst.
          assert (a = Open p').
          {
            assert (action_of (pi i s') == Open p') as h_open by now inversion Hr.
            rewrite h_i_s' in h_open; simpl in h_open; congruence.
          }
          eelim wellFormed_open_in; eauto.
        }
        assert (i1 <= k1) as Hleqi1k1.
        {
          destruct (Compare_dec.lt_dec i k0) as [Hik0 | Hik0].
            + assert (i1 <k1) by (apply insertion_order_rev with i (length s) i0 k0 ;auto;lia).
              lia.
            + assert (k0 <i) as Hltk0i by lia.
              assert (i0 < i) as Hlti0i by lia. 
              assert (i1 = i0) as Hi1i0 by now apply insertion_rel_snd_left with i (length s).
              assert (k1 = k0) as Hk1k0  by now apply insertion_rel_snd_left with i (length s).
              lia.
        }
        
        inversion Hr.
        {
          assert (k0 <> j0) as Hk0j0. 
          {
            intro Hn;subst.
            assert (Some (Open p') = Some (Close p)) as H1.
            {
            rewrite <- Hk.
            rewrite <- Hj.
            auto.
            }
            inversion H1.
          }
          assert(k1<=j1). 
          {
            destruct (Peano_dec.eq_nat_dec j0 i) as [Hj0i | Hj0i].
            - subst.
              assert (j1 = length s) as Hj1lgt by now apply insertion_rel_snd_middle with i;subst.
              assert (k1 < length (s • (t0, a))) as Hk1l  by eauto with nth_error.
              replace (length (s • (t0, a))) with (S (length s)) in Hk1l by ( autorewrite with length;simpl;lia).
              lia.
            -  assert (k1 <j1) by (apply insertion_order_rev with i (length s) k0 j0 ;auto;lia).
               lia.
          }
          assert (action_of (pi j1 (s • (t0, a))) == Close p) as Hj1. 
          {
            assert (pi j1 (s • (t0, a)) = pi j0 s') as Hpij by (eapply insertion_rel_insertion; eauto).
            rewrite  Hpij;assumption.
          }
          assert (range (s • (t0, a)) p i1 j1 ) as Hr1.
          {
            constructor 1;auto.
          }
          
          constructor 1 with i1 j1 k1;auto.
        }
        {

          assert (range  (s • (t0, a)) p i1 (length  (s • (t0, a)) -1)) as Hr'.
          {
            constructor 2;auto.
            contradict HNotClosed.
            eapply insertion_occursIn; eauto.
          }
          assert (k1 <= (length  (s • (t0, a)) -1)) as Hlgt.
          {
            assert (k1 < (length  (s • (t0, a)) )) by   eauto with nth_error.
            lia.
          }
          constructor 1 with i1 (length  (s • (t0, a)) -1) k1;auto.
        }
     +  (**  sec_order_cons_ind   **)
       assert (S (length s) = length s') by now apply insertion_length with i (t0,a).
       assert (exists i1, insertion_rel i (length s) i1 i0) as [i1 h_i1].
       {
         assert (i0 < length s') as h_lt by eauto with nth_error.
         assert (surjective (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
         {
           assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
           now destruct (insertion_rel_bijective _ _ h_lt2).
         }
         apply h_app; intuition.
       }
        assert (exists k1, insertion_rel i (length s) k1 k0) as [k1 h_k1].
        {
          assert (k0 < length s') as h_lt by eauto with nth_error.
          assert (surjective (fun k : threadId => k < S (length s)) (insertion_rel i (length s))) as h_app.
         {
           assert (i <= length s) as h_lt2 by (eapply insertion_defined_rev; eauto).
           now destruct (insertion_rel_bijective _ _ h_lt2).
         }
         apply h_app; intuition.
        }
        assert (action_of (pi i1 (s • (t0, a))) == Open p) as Hi1. 
        {
          assert (pi i1 (s • (t0, a)) =pi i0 s') as Heq by (eapply insertion_rel_insertion;eauto).
          rewrite Heq.
          assumption.
        }
        assert (action_of (pi k1 (s • (t0, a))) == Open p') as Hk1. 
        {
          assert (pi k1 (s • (t0, a)) =pi k0 s') as Heq by (eapply insertion_rel_insertion;eauto).
          rewrite Heq.
          assumption.
        }

        assert (threadId_of (pi k1 (s • (t0, a))) == t) as Hk1t. 
        {
          assert (pi k1 (s • (t0, a)) =pi k0 s') as Heq by (eapply insertion_rel_insertion;eauto).
          rewrite Heq.
          assumption.
        }
        assert (tribeChildren (s • (t0, a)) p t) as HtrC. 
        apply insertion_tribeChildren_rev with i s' ;auto.
        constructor 2 with i1 k1 t;auto.
 Qed.

 (** *** Preservation of [concurrent] *)
 
 Lemma insertion_concurrent :
    forall s i t a s' p p',
      wellFormed (s • (t,a)) ->
      insertion i s (t,a) == s' ->
      conflicts s t ->
      (forall k, i <= k < length s -> ~ synchronizeWith (s • (t,a)) k (length s)) ->
      (concurrent (s • (t,a)) p p' <->
      concurrent s' p p').
  Proof.
    intros s i t a s' p p' h_wf h_insert h_no_sync.
    split.
    - intros h_conc.
      unfold concurrent in *.
      destruct h_conc as [H1 [H2 [H3 H4]]].
      split.
      now apply insertion_occursIn with s i (t,a).
      split.
      now apply insertion_occursIn with s i (t,a).
      split.
      contradict H3.
      now apply insertion_sec_order with i s'.
      contradict H4.
      now apply insertion_sec_order with i s'.
    - intros h_conc.
      unfold concurrent in *.
            destruct h_conc as [H1 [H2 [H3 H4]]].
      split.
      eapply insertion_occursIn; eauto.
      split.
      eapply insertion_occursIn; eauto.
      split.
      contradict H3.
      now apply insertion_sec_order with s i t a.
      contradict H4.
      now apply insertion_sec_order with s i t a.
  Qed.

  (** *** preservation of [synchronizeWith] *)

  Lemma insertion_destructs_no_synchronization :
    forall i s t a s',
      wellFormed (s • (t,a)) ->
      (forall k, i <= k < length s -> ~ synchronizeWith (s • (t,a)) k (length s)) ->
      insertion i s (t,a) = Some s' ->
      conflicts s t ->
      forall i1 i2,
        synchronizeWith (s • (t,a)) i1 i2 ->
        forall j1 j2,
          insertion_rel i (length s) i1 j1 ->
          insertion_rel i (length s) i2 j2 ->
          synchronizeWith s' j1 j2.
  Proof.
    intros i s t a s' h_wf h_nosync h_insertion h_conflict i1 i2 h_sync. 
    induction h_sync as [i1 i2 | i1 i0 i2].
    - intros j1 j2 h_j1 j_j2; constructor.
      assert (pi i1 (s • (t,a)) = pi j1 s')
        by now apply insertion_rel_insertion with i.
      assert (pi i2 (s • (t,a)) = pi j2 s') 
        by now apply insertion_rel_insertion with i.
      assert (j1 < j2).
      {
        assert (i <= length s) by (apply insertion_defined_rev with (t,a); eauto).
        assert (i1 < i2) as h_lt_i1_i2.
        {
          assert (synchronizeWith (s • (t,a)) i1 i2) by now constructor.
          apply synchronizeWithOrder with (s • (t,a)).
          assumption.
        }
        assert (i2 <= length s). 
        {
          assert (i2 < length (s • (t,a))).
          apply synchronizeWithIn with i1.
          constructor; assumption.
          intuition.
          autorewrite with length in H3.
          simpl in H3.
          intuition.
        }
        destruct (Peano_dec.eq_nat_dec i2 (length s)).
        - subst.
          replace j2 with i in * by now (symmetry; apply insertion_rel_fst_last with (length s)).
          
          assert (i1 < i).
          {
            destruct (Compare_dec.lt_dec i1 i); [assumption |].
            assert (i <= i1 < length s).
            {
              split.
              intuition.
              apply synchronizeWithOrder with (s• (t,a)).
              constructor; assumption.
            }
            elim (h_nosync i1 H4).
            constructor; assumption.
          }

          now replace j1 with i1 by now apply insertion_rel_fst_left with i (length s).
        - assert (i2 < length s) by intuition.
          
          now apply insertion_order with i (length s) i1 i2.
      }
      inversion H; subst.
      + constructor 1 with t0.
        assumption.
        unfold Event.t in *; rewrite <- H0; assumption.
        unfold Event.t in *; rewrite <- H1; assumption.
      + constructor 2 with t0.
        assumption.
        unfold Event.t in *; rewrite <- H0; assumption.
        unfold Event.t in *; rewrite <- H1; assumption.
      + constructor 3 with t0.
        assumption.
        unfold Event.t in *; rewrite <- H0; assumption.
        unfold Event.t in *; rewrite <- H1; assumption.
      + constructor 4 with p p'.
        assumption.
        eapply insertion_concurrent; eauto.
        unfold Event.t in *; rewrite <- H0; assumption.
        unfold Event.t in *; rewrite <- H1; assumption.
    - intros j1 j2 h_j1 h_j2.
      assert (i <= length s) as h_lt_i_s.
      {
        eapply insertion_defined_rev.
        exists s'.
        apply h_insertion.
      }
      assert (i2 <= length s) as h_lt_i2_s.
        {
          edestruct insertion_rel_lt.
          eauto.
          now apply h_j2.
          assumption.
        }
      assert (exists j0, 
                j1 < j0 < j2 
                /\ insertion_rel i (length s) i0 j0) as [j0 [[Ha Hb] Hc]].
      {
        destruct (insertion_rel_bijective i (length s) h_lt_i_s) as 
            [ _ _ h_applicative _ _].
        assert (i0 < S (length s)) as h_i0. 
        {
          assert (i0 < i2) by 
              now apply synchronizeWithOrder with (s•(t,a)).
          intuition.
        }
        destruct (h_applicative i0 h_i0) as [j0 h_j0].
        exists j0.
        split; [split|].
        - assert (i1 < i0) by now apply synchronizeWithOrder with (s • (t,a)).
          assert (i0 < length s).
          {
            assert (i2 < S (length s)).
              {
                intuition.
              }
            assert (i0 < i2) by now apply synchronizeWithOrder with (s•(t,a)).
            intuition.
          }
          apply insertion_order with i (length s) i1 i0; first [assumption | intuition].
        - destruct (Peano_dec.eq_nat_dec i2 (length s)).
          + subst.
            replace j2 with i in * by now (symmetry; apply insertion_rel_fst_last with (length s)).
            assert (i0 < i).
            {
              destruct (Compare_dec.lt_dec i0 i); [assumption |].
              assert (i <= i0 < length s).
              {
                split.
                intuition.
                apply synchronizeWithOrder with (s•(t,a)).
                assumption.
              }
              elim (h_nosync i0 H).
              assumption.
            }
            now replace j0 with i0 by now apply insertion_rel_fst_left with i (length s).
          + assert (i0 < i2) by now apply synchronizeWithOrder with (s • (t,a)).
            assert (i2 < length s) by intuition.
            now apply insertion_order with i (length s) i0 i2.
        - assumption.
      }
      assert (synchronizeWith s' j1 j0) by now apply IHh_sync1.
      assert (synchronizeWith s' j0 j2) by now apply IHh_sync2.
      constructor 2 with j0; assumption.
  Qed.

  Lemma insertion_introduce_no_sw :
    forall i s t a s',
      wellFormed (s • (t,a)) ->
      (forall k, i <= k < length s -> ~ synchronizeWith (s • (t,a)) k (length s)) ->
      insertion i s (t,a) = Some s' ->
      conflicts s t ->
      forall i1 i2,
        sw s' i1 i2 ->
        forall j1 j2,
          insertion_rel i (length s) j1 i1 ->
          insertion_rel i (length s) j2 i2 ->
          sw (s • (t,a)) j1 j2.
  Proof.
    intros i s t a s' h_Wf h_no_sync h_insert h_conflict i1 i2 h_sync.
    intros j1 j2 h_insert1 h_insert2.
    assert (i1 < i2) by (inversion h_sync; assumption).
    destruct (Peano_dec.eq_nat_dec i1 i).
    - subst.
      assert (j1 = length s).
      {
        apply insertion_rel_snd_middle with i.
        apply insertion_defined_rev with (t,a).
        exists s'; assumption.
        assumption.
      }
      subst.
      exfalso.
      assert (i <= j2 < length s) as h_a. 
      {
        split.
        assert (i2 = S j2).
        apply insertion_rel_snd_right with i (length s).
        apply insertion_defined_rev with (t,a).
        exists s'; assumption.
        assumption.
        assumption.
        subst.
        intuition.
        destruct (Peano_dec.eq_nat_dec j2 (length s)).
      subst.
      assert (i2 = i).
      apply insertion_rel_fst_last with (length s).
      apply insertion_defined_rev with (t,a).
      exists s'; assumption.
      assumption.
      subst; exfalso; intuition.
      assert (i <= length s) by (eapply insertion_defined_rev; eauto).
      assert (j2 <= length s).
      destruct (insertion_rel_lt _ _ H0 _ _ h_insert2).
      assumption.
      intuition.
    }
    generalize (h_no_sync j2 h_a); intro.
    elim H0.
    constructor 1.
    generalize (insertion_rel_insertion _ _ _ _ h_insert _ _ h_insert1); intro.
    generalize (insertion_rel_insertion _ _ _ _ h_insert _ _ h_insert2); intro.
    inversion h_sync; subst.
    + constructor 1 with t0.
      apply h_a.
      unfold Event.t in *; rewrite H2; assumption.
      unfold Event.t in *; rewrite H1; assumption.
    + assert (threadId_of (pi j2 (s • (t,a))) == t0).
      unfold Event.t in *; rewrite H2; assumption.
      assert (action_of (pi (length s) (s • (t,a))) == Fork t0).
      unfold Event.t in *; rewrite H1; assumption.
      assert (length s < j2).
      inversion h_Wf.
      unfold wf_fork in WF2. 
      apply WF2 with t0.
      assumption.
      assumption.
      exfalso; intuition.
    + assert (threadId_of (pi (length s) (s • (t,a))) == t0).
      unfold Event.t in *; rewrite H1; assumption.
      assert (action_of (pi j2 (s • (t,a))) == Join t0).
      unfold Event.t in *; rewrite H2; assumption.
      assert (length s < j2).
      inversion h_Wf.
      unfold wf_join in WF3. 
      apply WF3 with t0.
      left.
      assumption.
      assumption.
      exfalso; intuition.
    + assert (exists k1 t0, 
                j2 < k1 < length s /\ action_of (pi k1 (s •(t,a)))== Open p 
                /\ threadId_of (pi k1 (s•(t,a))) == t0 /\ threadId_of (pi (length s) (s • (t,a))) == t0).
      {
        assert (action_of (pi (length s) (s • (t,a))) == Close p) by (rewrite H1; assumption).
        assert (wf_open_close (s • (t,a))) by now inversion h_Wf.
        unfold wf_open_close in H8.
        destruct (H8 _ _ H7) as [k0 [h_u [h_v h_w]]].
        assert (exists t0, threadId_of (pi k0 (s • (t,a))) == t0) as [t0 h_t0]. 
        {
          assert (exists e', pi k0 (s • (t,a)) == e').
          destruct (nth_error_lt_defined h_u).
          exists x.
          assert (k0 < length s).
          eauto with nth_error.
          rewrite nth_error_append_left; assumption.
          destruct H9.
          destruct x.
          exists t0.
          rewrite H9.
          reflexivity.
        }
        exists k0.
        exists t0.
        split.
        assert (wf_mutualExclusion (s • (t,a))) by now inversion h_Wf.
        unfold wf_mutualExclusion in H9.
        destruct (H9 p p').
        eapply insertion_concurrent; eauto.

        - inversion H10; subst.
          assert (j = j2). 
          {
            assert (action_of (pi j2 (s • (t,a))) == Open p').
            rewrite H2.
            assumption.
            wellFormed_occurences (Open p').
          }

          assert (i0 = length s). 
          {
            wellFormed_occurences (Close p).
          }
          subst.
          exfalso; intuition.
        - inversion H10; subst.
          assert (j2 < i0). 
          {
            destruct (H8 _ _ Ha) as [k1 [h_u1 [h_v1 h_w1]]].
            assert (action_of (pi j2 (s • (t,a))) == Open p').
            {
              rewrite H2.
              assumption.
            }
            assert (k1 = j2).
            wellFormed_occurences (Open p').
            subst.
            assumption.
          }
          assert (k0 = j). 
          {
            wellFormed_occurences (Open p).
          }
          subst.
          split; [|assumption].
          transitivity i0; assumption.
        - split.
          assumption.
          split.
          assumption.
          unfold Event.t in *; rewrite  h_w.
          assumption.
      }
      destruct H7 as [k1 [t0 [h_b [h_c [h_d h_e]]]]].
      assert (i <= k1 < length s) by intuition.
      elim (h_no_sync k1 H7).
      constructor 1.
      constructor 1 with t0.
      apply H7.
      assumption.
      assumption.
  - assert (i1 < i2) by (inversion h_sync; assumption).
    assert (j1 < j2).
    {
      apply insertion_order_rev with i (length s) i1 i2; try assumption.
      apply insertion_defined_rev with (t,a).
      exists s'; assumption.
    }
    generalize (insertion_rel_insertion _ _ _ _ h_insert _ _ h_insert1); intro.
    generalize (insertion_rel_insertion _ _ _ _ h_insert _ _ h_insert2); intro.
    inversion h_sync; subst.
    + constructor 1 with t0.
      assumption.
      unfold Event.t in *; rewrite H2; assumption.
      unfold Event.t in *; rewrite H3; assumption.
    + constructor 2 with t0.
      assumption.
      unfold Event.t in *; rewrite H2; assumption.
      unfold Event.t in *; rewrite H3; assumption.
    + constructor 3 with t0.
      assumption.
      unfold Event.t in *; rewrite H2; assumption.
      unfold Event.t in *; rewrite H3; assumption.
    + constructor 4 with p p'.
      assumption.
      eapply insertion_concurrent; eauto.
      unfold Event.t in *; rewrite H2; assumption.
      unfold Event.t in *; rewrite H3; assumption.
  Qed.

  Lemma insertion_introduce_no_synchronization :
    forall i s t a s',
      wellFormed (s • (t,a)) ->
      wellSynchronized (s • (t,a)) ->
      (forall k, i <= k < length s -> ~ synchronizeWith (s • (t,a)) k (length s)) ->
      insertion i s (t,a) = Some s' ->
      conflicts s t ->
      forall i1 i2,
        synchronizeWith s' i1 i2 ->
        forall j1 j2,
          insertion_rel i (length s) j1 i1 ->
          insertion_rel i (length s) j2 i2 ->
          synchronizeWith (s • (t,a)) j1 j2.
  Proof.
    intros i s t a  s' h_wf h_ws h_no_sync h_insert h_conflict i1 i2 h_sync.
    induction h_sync.
    - intros j1 j2 h_insert1 h_insert2.
      constructor.
      apply insertion_introduce_no_sw with i s' x y; try assumption.
    - intros j1 j2 h_insert1 h_insert2.
      assert (exists j0, insertion_rel i (length s) j0 y) as [j0 h_j0].
      {
        destruct insertion_rel_bijective with i (length s).
        apply insertion_defined_rev with (t,a).
        exists s'; assumption.
        destruct (s0 y).
        destruct (r _ _ h_insert2).
        transitivity  z.
        apply synchronizeWithOrder with s'.
        assumption.
        assumption.
        exists x0.
        assumption.
      }
      constructor 2 with j0.
      now apply IHh_sync1.
      now apply IHh_sync2.
  Qed. 
  
  (** ** Compatibility *)
  (** *** Insertion produces equivalent traces *)

  Lemma insertion_compatible : 
    forall i p s t a s' ,
      wellFormed (s • (t,a)) ->
      wellSynchronized (s • (t,a)) ->
      exclude s p t ->
      (forall k, i <= k < length s -> ~ synchronizeWith (s • (t,a)) k (length s)) ->
      insertion i s (t,a) = Some s' ->
      action_of (pi i s) == Open p ->
      compatible (s • (t,a)) s'.
  Proof.
    intros i p s t a s' h_wf h_ws h_no_sync h_insertion.
    exists (insertion_rel i (length s)).
    split.
    - unfold Event.t in *.
      replace (length (s • (t,a))) with (S (length s)) 
        in *
        by (autorewrite with length in *; simpl in *; intuition).
      replace (length s') with (S (length s) ) 
        in *.
      assert (i <= length s) by eauto using insertion_defined_rev.
      now apply insertion_rel_bijective.
      now apply insertion_length with i (t,a).
    - split.
      + now apply insertion_rel_insertion.
      + intros i0 j i' j' h_insert1 h_insert2.
        split.
        { intro h_sync.
          apply insertion_destructs_no_synchronization with i s t a i0 i'; try auto.
          exists p; assumption.
        }
        { intro h_sync.
          apply insertion_introduce_no_synchronization with i s' j j'; try auto.
          exists p; assumption.
        }
  Qed.

End Make.
