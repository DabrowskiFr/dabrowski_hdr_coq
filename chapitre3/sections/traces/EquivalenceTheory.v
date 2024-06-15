Require Import Lt Peano_dec Compare_dec Relation_Operators List Morphisms Lia.
From sections.lifo Require Import Prelude ListBasics Length BijRel.
From sections.common Require Import GenericTrace.
From sections.traces Require Import Synchronisation Equivalence.
Require Import sections.lifo.Prelude sections.traces.Synchronisation.
 
(* Revoir toutes les propriétés en utilisant directement la bijection
 pour éviter les hypothèses inutiles *)

Module Make (P : MiniDecidableSet)
       ( Export Address: DecidableInfiniteSet) 
       ( Export T : Type_.TYPE Address )
       ( Export V : Value.TYPE Address T ).

  Include Equivalence.Make P Address T V.

  (** ** Preservation of definitions *)
 
  Lemma compatible_length : 
    forall s s', s ~= s' -> length s = length s'. 
  Proof.
    intros s s' h_comp.
    inversion h_comp as [R [h_bijective _]].
    eauto 3 using bijective_lt_eq.
  Qed.

  Lemma compatible_proj : 
    forall s s',
      compatible s s' ->
      forall i, exists i', pi i' s' = pi i s.
  Proof.
    intros s s' h_comp i.
    inversion h_comp as [ R [[_ _ h_applicative _ _][h_eq _]]].
    destruct (lt_dec i (length s)) as [Ha | Ha].
    - destruct (h_applicative i Ha) as [i' Hi'].
      (exists i'); symmetry; now apply h_eq.
    - assert (~ i < length s') by now rewrite <- (compatible_length s s').
      (exists i); now autorewrite with pi.
  Qed.

  Lemma compatible_occursIn : 
    forall s s',
      compatible s s' ->
      forall a, occursIn s a -> occursIn s' a.
  Proof.
    intros s s' h_comp a h_occurs.
    destruct h_occurs as [i].
    destruct (compatible_proj _ _ h_comp i) as [i' Hi'].
    exists i'; congruence.
  Qed.

  Lemma compatible_not_occursIn :
    forall s s',
      compatible s s' ->
      forall a, ~ occursIn s a -> ~ occursIn s' a.
  Proof.
    intros s s' h_comp a h_n_occurs.
    contradict h_n_occurs.
    assert (s' ~=s) as h_comp2 by (symmetry;auto).
    now apply compatible_occursIn with s'.
  Qed.
    

  Lemma compatible_father : 
    forall s s',
      compatible s s' ->
      forall t t', father s t t' -> father s' t t'.
  Proof.
    intros s s' h_comp t t' [i [h_tid h_act]].
    destruct (compatible_proj s s' h_comp i) as [i' Hi'].
    exists i'; split; congruence.
  Qed.



  Lemma compatible_owns : 
    forall s s',
      compatible s s' ->
      forall p t, owns s p t -> owns s' p t.
  Proof.
    intros s s' h_comp p t h_owns.
    inversion h_owns; subst.
    destruct (compatible_proj s s' h_comp i) as [i' Hi'].
    exists i'; congruence.
  Qed.

(*  Instance compatible_owns_proper (p : P.t) (t : threadId) :
    Proper (compatible ==> iff) (fun s => owns s p t).
  Proof.
    intros s s' h_eq.
    assert (s' ~= s) by now symmetry.
    split; now apply compatible_owns.
  Qed.
*)
  Lemma compatible_range_closed :
    forall s s' R,
      wf_occurences s ->
      wf_open_close s ->
      compatible_by R s s' ->
      forall p i j,
        range s p i j -> 
        action_of (pi j s) == Close p ->
        exists i' j', R i i' /\ R j j' /\ range s' p i' j' /\ action_of (pi j' s') == Close p.
  Proof.
    intros s s' R h_occ h_op_cl h_comp p i j h_range h_occursIn.
    inversion h_comp as [[_ _ h_applicative _ _] [Ha Hb]].
    assert (exists i', R i i' /\ pi i s = pi i' s') as [i' [h1_i' h2_i']].
    {
      assert (i < length s) as Hu by now apply range_i_lt_s with p j.
      destruct (h_applicative i Hu) as [i' h_i'].
      exists i'; auto.
    }
    assert (exists j', R j j' /\ pi j s = pi j' s') as [j' [h1_j' h2_j']]. 
    {
      assert (j < length s) as Hu by eauto with nth_error.
      destruct (h_applicative j Hu) as [j' Hj'].
      exists j'; auto.
    }
    inversion h_range; subst.
    + assert (action_of (pi j' s') == Close p) by congruence.
      exists i', j'; intuition (constructor 1; congruence).
    + elim HNotClosed.
      exists (length s - 1); assumption.
  Qed.
  
  Lemma compatible_range_opened :
    forall s s' R,
      wf_occurences s ->
      wf_open_close s ->
      compatible_by R s s' ->
      forall p i,
        range s p i (length s - 1) ->
        ~ occursIn s (Close p) ->
        exists i', 
          R i i' /\ 
            range s' p i' (length s' - 1) /\ 
            ~ (occursIn s' (Close p)).
  Proof.
    intros s s' R h_occ h_op_cl h_comp p i h_range h_occursIn.
    inversion h_comp as [[_ _ h_applicative _ h_surjective] [Ha Hb]].
    assert (exists i', R i i' /\ pi i s = pi i' s') as [i' [h1_i' h2_i']].
    {
      assert (i < length s) as Hu by  now apply range_i_lt_s with p (length s -1).
      destruct (h_applicative i Hu) as [i' h_i'].
      exists i'; auto.
    } 
    assert (~ occursIn s' (Close p)).
    {
      contradict h_occursIn.
      inversion h_occursIn; subst.
      assert (exists i0', R i0' i0 /\ pi i0' s = pi i0 s') as [i0' [h1_i0' h2_i0']]. 
      {
        assert (i0 < length s') as Hu by eauto with nth_error.
        destruct (h_surjective i0 Hu) as [i0' h_i0'].
        exists i0'; auto.
      }
      exists i0'; congruence.
    }
    inversion h_range; subst; [ elim h_occursIn; eauto |].
    - eauto using occursIn.
    - exists i'.
      intuition (constructor 2; congruence).
Qed.


  Lemma compatible_range : 
    forall s s' R,
      wf_occurences s ->
      wf_open_close s ->
      compatible_by R s s' ->
      forall p i j,
        range s p i j ->
        exists i', R i i' /\
                   ((exists j', R j j' /\ range s' p i' j' /\ action_of (pi j' s') == Close p) 
                    \/ (range s' p i' (length s' -1) /\ ~ occursIn s' (Close p))).
  Proof.
    intros s s' R  h_occ h_op_cl h_comp p i j h_range.
    inversion h_comp as [[_ _ h_applicative _ h_surjective] [Ha Hb]].
    inversion h_range; subst.
    - destruct (compatible_range_closed s s' R h_occ h_op_cl h_comp p i j h_range Hj) 
        as [i' [j' [h_i' [h_j' [h_range' h_close']]]]].
      exists i'.
      split.
      assumption.
      assert (action_of (pi j s) == Close p) by eauto.
      left.
      exists j'; intuition.
    - destruct (compatible_range_opened s s' R  h_occ h_op_cl h_comp p i h_range HNotClosed) 
        as [i' [hi' [h_range' h_occursIn']]].
      exists i'.
      split.
      assumption.
      right; tauto.
  Qed.
  
  (* tribeChildren  -> threadId (pi i s) == t' *)
  (* split open_close in two conditions *)
  (* exists open /\ open,close have same thread *)

  Lemma compatible_tribeChildren : 
    forall s s',
      wf_occurences s ->
      wf_open_close s ->
      compatible s s' ->
      forall p t, tribeChildren s p t -> tribeChildren s' p t.
  Proof.
    intros s s' h_wf_occurences h_wf_open_close h_comp p t h_tribeChildren.
    destruct h_comp as [R h_comp].
    induction h_tribeChildren.
    - assert (exists k', R k k' /\ pi k s = pi k' s') as [k' [h1_k' h2_k']].
      {
        inversion h_comp as  [[_ _ h_applicative _ h_surjective] [h_eq h_sync]].
        assert (k < length s) as Ha by eauto with nth_error.
        destruct (h_applicative k Ha) as [k' hk'].
        assert (pi k s = pi k' s') by auto.
        exists k'; split; assumption.
      }
      destruct (compatible_range s s' R  h_wf_occurences h_wf_open_close h_comp p i j H) as [i' [h_i' Ha]].
      assert (i' < k').
      {
        assert (synchronizeWith s' i' k').
        {
          assert (synchronizeWith s i k).
          {
            assert (threadId_of (pi i s) == t0). 
            {
              inversion H0; subst.
              assert (action_of (pi i s) == Open p) by now inversion H; subst.
              assert (i = i0) by wellFormed_occurences (Open p).
              congruence.
            }
            constructor 1; constructor 1 with t0; intuition.
          }
          inversion h_comp as [ _ [Hu Hv ]].
          now apply (Hv _ _ _ _ h_i' h1_k').
        }
        now apply synchronizeWithOrder with s'.
      }
      destruct Ha as [Ha | Ha].
      + destruct Ha as [j' [h_j' [h_range' h_close']]].
        assert (k' <= j'). 
        {
          assert (synchronizeWith s' k' j').
          {
            assert (synchronizeWith s k j).
            {
              assert (threadId_of (pi j s) == t0). 
              {
                inversion h_comp as [ [] [Hu _]].
                assert (pi j s = pi j' s') by eauto.
                rewrite <- H5 in h_close'.
                (*inversion h_wf_s.*)
                destruct (h_wf_open_close j p h_close') as [i1 [Hv [Hw Hz]]].
                rewrite Hz.
                inversion H0; subst.
                assert (i1 = i2) by wellFormed_occurences (Open p).
                subst.
                assumption.
              }
              inversion h_comp as [ [] [Hv _ ]].
              assert (pi j s = pi j' s') by eauto. 
              assert (action_of (pi j s) == Close p) by congruence. 
              assert (j <> k) by (intro; subst; congruence).
              assert (k < j) by auto with *.
              constructor; constructor 1 with t0; intuition.
            }
            inversion h_comp as [ _ [Hu Hv ]].
            now apply (Hv _ _ _ _ h1_k' h_j').
          }
          assert (k' < j') by now apply synchronizeWithOrder with s'.
          auto with *.
        }
        assert (i' < k' <= j') by intuition.
        assert (compatible s s') by (exists R; assumption). 
        constructor 1 with i' j' t0 k'; first [now apply compatible_owns with s | congruence].
      + assert (k' <= length s' - 1).
        {
          assert (k' < length s').
          inversion h_comp as [[h_restricted _ _ _ _ ]].
          destruct (h_restricted k k' h1_k'); assumption.
          auto with *.
        }
        assert (i' < k' <= length s' -1) by intuition.
        constructor 1 with i' (length s' - 1) t0 k'.
        tauto.
        assert (compatible s s') by (exists R; assumption). 
        now apply compatible_owns with s.
        assumption.
        congruence.
        congruence.
    - assert (compatible s s') by (exists R; assumption).
      assert (father s' t' t0) by now apply compatible_father with s.
      now constructor 2 with t0.
  Qed.

(*  Instance tribeChildren_compatible_proper (p : P.t) (t : threadId) :
    Proper (compatible ==> iff) (fun s => tribeChildren s p t).
  Proof.  
    intros s s' h_eq. 
    assert (s' ~= s') by now symmetry.
    split.
    apply compatible_tribeChildren.*)

  Lemma compatible_tribe : 
    forall s s',
      wf_occurences s ->
      wf_open_close s ->
      compatible s s' ->
      forall p t, tribe s p t -> tribe s' p t.
  Proof.
    intros s s' h_wf_occurences h_wf_open_close h_comp p t h_tribe.
    inversion h_tribe.
    - constructor 1.
      now apply compatible_owns with s.
    - constructor 2.
      now apply compatible_tribeChildren with s.
  Qed.



    Lemma compatible_see : 
      forall s s' i j i' j' R,
        wellSynchronized s ->
        see s i j ->
        compatible_by R s s' ->
          R i i' -> 
          R j j' -> 
          see s' i' j'.
    Proof.
      (*intros s s' i j i' j' R h_ws_s Hsee h_comp hii' hjj'.*)
      intros  s s' i j i' j' R h_ws_s Hsee.
      generalize dependent i'.
      generalize dependent j'.
      induction Hsee as [ i j | i z j  ];subst.
      - intros j' i' h_comp hii' hjj'.
        inversion h_comp    as [ [ h1 h_func h_applicative h3 h_surjective] [h_eq h_sync ]]. 
      

        inversion H as [ ? ? ?  t0 Hlt Hi' Hj' | HA HB HC l n v Hltij Hw Hr |? ? ?  t0 Hlt Hi' Hj'];subst.
        + 
          destruct (h_sync i i' j j') as [h_sync1 h_sync2];auto.
          assert (synchronizeWith s i j) as Hsync_ij.    
          {
            constructor 1.
            constructor 1 with t0;auto.
          }
          assert (synchronizeWith s' i' j')  as Hsync_i'j' by now apply h_sync1. 
          assert (i'<j') as Hlti'j' by now apply synchronizeWithOrder with s'.
          
          rewrite (h_eq i i' hii') in Hi' at 1.
          rewrite (h_eq j j' hjj') in Hj' at 1.
          
          constructor 1.
          constructor 1 with t0;auto.

        + (* i = Write, j = Read, in conflict  *)
          (* wellSynchronised, synchronizeWith i j -> i < j *)
          (* Ri i', R j j', synchronizeWith i j -> i' < j'  *)
          (* constructor 2 see                              *)

          assert (conflict  (Write l n v) (Read l n v)) as Hcfl by constructor.
          unfold wellSynchronized in h_ws_s.
          assert (synchronizeWith s i j) as Hsync_ij. apply h_ws_s with  ( Write l n v) (Read l n v);auto.
     
          destruct (h_sync i i' j j') as [h_sync1 h_sync2];auto.
          assert (synchronizeWith s' i' j')  as Hsync_i'j' by now apply h_sync1. 
          assert (i'<j') as Hlti'j' by now apply synchronizeWithOrder with s'.

          rewrite (h_eq i i' hii') in Hw at 1.
          rewrite (h_eq j j' hjj') in Hr at 1.

          constructor;constructor 2 with l n v;auto.
        + (*i = Fork t0, threadOf j = t0 *)
          (* -> synchronizedWith i j (swFork) *)
          (* -> synchronizedWith i' j'  *)
          (* -> i' < j' *)
          (* contructor 3 see*)
          assert (synchronizeWith s i j) as  Hsync_ij by (constructor;constructor 2 with t0;auto).
  
          destruct (h_sync i i' j j') as [h_sync1 h_sync2];auto.
          assert (synchronizeWith s' i' j')  as Hsync_i'j' by now apply h_sync1. 
          assert (i'<j') as Hlti'j' by now apply synchronizeWithOrder with s'.

          rewrite (h_eq i i' hii') in Hi' at 1.
          rewrite (h_eq j j' hjj') in Hj' at 1.
          
          constructor; constructor 3 with t0;auto.
      - intros j' i' h_comp hii' hjj'.
        assert (exists z', R z z') as Hz'.
        {
          inversion h_comp as [ [_ _ h_app _ _] [_ _]].
          apply h_app.
          apply see_lt_length with i.
          assumption.
        }
        destruct Hz' as [z' Hz'].
        assert (see s' i' z') as Hsee_i'z' by now apply IHHsee1.
        assert (see s' z' j') as Hsee_z'j' by now apply IHHsee2.
        
        now constructor 2 with z'.
    Qed.

 Lemma compatible_pending :
    forall s s',
    compatible s s' ->
    forall p, pending s p -> pending s' p.
  Proof.
    intros s s' h_comp p [h_occursIn h_not_occursIn].
    destruct h_occursIn as [i Hi].
    inversion Hi; subst.
    contradict h_not_occursIn.
    exists (length s - 1).
    assumption.
    split.
    assert (exists i', pi i s = pi i' s') as [i' Hi'].
    {
      inversion h_comp.
      inversion H; subst.
      inversion H0.
      inversion H1.
      assert (i < length s) as Ha by eauto with nth_error.
      destruct (H4 i Ha) as [i' Hi'].
      exists i'.
      eauto.
    }
    exists i'.
    constructor 2.
    rewrite <- Hi'; assumption.
    contradict HNotClosed.
    apply compatible_occursIn with s'. 
    apply compatible_sym.
    assumption.
    assumption.
    contradict HNotClosed.
    apply compatible_occursIn with s'.
    apply compatible_sym.
    assumption.
    assumption.
  Qed.

    (** Preservation of well-formedness conditions *)
       
    Lemma compatible_wf_occurences :
      forall s s',
        compatible s s' ->
        wf_occurences s -> wf_occurences s'.
    Proof.
      intros s s' h_comp h_wf_occurences_s.
      unfold wf_occurences, occursAtMostOnce in *.
      intros a h_a i' j' h_i' h_j'.
      inversion h_comp as [R [h_bijective [h_eq h_sync]]].
      inversion h_bijective as [h_restricted h_functional h_applicative h_injective h_surjective].
      assert (exists i, R i i' /\ pi i s = pi i' s') as [i [h1_i h2_i]].
      {
        assert (i' < length s') by eauto with nth_error.
        assert (exists i, R i i') as [i Hi] by now apply h_surjective.
        exists i; split; [assumption | now apply h_eq].
      }
      assert (exists j, R j j' /\ pi j s = pi j' s') as [j [h1_j h2_j]]. 
      {
        assert (j' < length s') by eauto with nth_error.
        assert (exists j, R j j') as [j Hj] by now apply h_surjective.
        exists j; split; [assumption | now apply h_eq].
      }
      replace j with i in h1_j  by now (apply h_wf_occurences_s with a; congruence).
      now apply h_functional with i.
    Qed.
    
  Lemma compatible_wf_fork : 
    forall s s',
      compatible s s' ->
      wf_fork s -> wf_fork s'.
  Proof.
    intros s s' h_comp h_wf_fork_s.
    unfold wf_fork in *.
    intros i' t h_fork j' h_tid.
    inversion h_comp as [R [h_bijective [h_eq h_sync]]].
    inversion h_bijective as [h_restricted h_functional h_applicative h_injective h_surjective].
    assert (exists i, R i i' /\ pi i s = pi i' s') as [i [h1_i h2_i]].
    {
      assert (i' < length s') as Ha by eauto with nth_error.
      destruct (h_surjective i' Ha)  as [i Hi]. 
      exists i; split ; [assumption | now apply h_eq].
    }
    assert (exists j, R j j' /\ pi j s = pi j' s') as [j [h1_j h2_j]]. 
    {
      assert (j' < length s') as Ha by eauto with nth_error.
      destruct (h_surjective j' Ha) as [j Hj].
      exists j; split; [assumption | now apply h_eq].
    }
    assert (synchronizeWith s i j). 
    {
      constructor 1.
      constructor 2 with t.
      apply h_wf_fork_s with t.
      rewrite h2_i.
      assumption.
      rewrite h2_j.
      assumption.
      rewrite h2_i at 1;assumption.
      rewrite h2_j at 1;assumption.
    }
    assert (synchronizeWith s' i' j') by (eapply h_sync; eauto).
    now apply synchronizeWithOrder with s'.
  Qed.
    
  Lemma compatible_wf_join :
    forall s s', 
      compatible s s' ->
      wellSynchronized s ->
      wf_join_see_fork s ->
      wf_join s ->
      wf_join s'.
  Proof.
    intros s s' h_comp h_ws_s h_wf_join_see_fork_s h_wf_join_s.
    unfold wf_join in *.
    intros i' j' t h_or h_join.
    inversion h_comp as [R [h_bijective [h_eq h_sync]]].
    inversion h_bijective as [h_restricted h_functional h_applicative h_injective h_surjective].
    assert (exists i, R i i' /\ pi i s = pi i' s') as [i [h1_i h2_i]].
    {
      destruct h_or as [h_ti | hai];
       assert (i' < length s') as Ha by eauto with nth_error;
        destruct (h_surjective i' Ha) as [i Hi];
        assert (pi i s = pi i' s') by auto;
        exists i; split; assumption.
    }
    assert (exists j, R j j' /\ pi j s = pi j' s') as [j [h1_j h2_j]].
    {
      assert (j' < length s') as Ha by eauto with nth_error.
      destruct (h_surjective j' Ha) as [j Hj].
      assert (pi j s = pi j' s') by auto.
      exists j; split; assumption.
    }
    assert (synchronizeWith s i j).
    {
      destruct h_or.
      - constructor 1; constructor 3 with t.
        + apply h_wf_join_s with t. 
          rewrite h2_i; left; assumption.
          rewrite h2_j; assumption.
        + rewrite <- h2_i in H at 1;assumption.
        + rewrite <- h2_j in h_join at 1;assumption.
      - apply see_synchronizeWith.
        exact h_ws_s.
        unfold wf_join_see_fork in h_wf_join_see_fork_s.
        apply h_wf_join_see_fork_s with t.
        rewrite h2_i.
        assumption.
        rewrite h2_j.
        assumption.
    }
    assert (synchronizeWith s' i' j') by (eapply h_sync; eauto).
    now apply synchronizeWithOrder with s'.
  Qed.
  
  Lemma compatible_wf_open_close : 
    forall s s',
      compatible s s' ->
      wf_open_close s ->
      wf_open_close s'.
  Proof.
    intros s s' h_comp h_wf_open_close_s.
    unfold wf_open_close in *.
    intros i' p h_close.
    inversion h_comp as [R [[_ _ h_applicative _ h_surjective] [h_eq h_sync]]].
    assert (exists i, R i i' /\ pi i s = pi i' s') as [i [h1_i h2_i]].
    {
      assert (i' < length s') as Ha by eauto with nth_error.
      destruct (h_surjective i' Ha) as [i Hi].
      assert (pi i s = pi i' s') by auto.
      exists i; split; assumption.
    }
    assert (exists j, j < i /\ action_of (pi j s) == Open p 
                      /\ threadId_of (pi i s) = threadId_of (pi j s))
      as [j [h1_j [h2_j h3_j]]]. 
    {
      assert (action_of (pi i s) == Close p) by congruence.
      now apply h_wf_open_close_s.
    }
    assert (exists j', R j j' /\ pi j s = pi j' s') as [j' [h1_j' h2_j']]. 
    {
      assert (j < length s) as Ha by eauto with nth_error.
      destruct (h_applicative j Ha) as [j' hj'].
      assert (pi j s = pi j' s') by auto.
      exists j'; split; assumption.
    }
    assert (j' < i').
    {
      assert (synchronizeWith s' j' i').
      {
        assert (synchronizeWith s j i).
        {
          assert (exists t, threadId_of (pi i s) == t) 
            as [t Ht]. 
          {
            rewrite h2_i.
            destruct (pi i' s') as [[t1 a1] | _].
            - exists t1;auto.
            - inversion h_close.
          }
          constructor 1; constructor 1 with t;auto. rewrite <- h3_j at 1; auto.
        }
        eapply h_sync; eauto.
      }
      now apply synchronizeWithOrder with s'.
    }
    exists j'; intuition congruence.
  Qed.    
  
  Lemma compatible_wf_join_see_fork : 
    forall s s',
      compatible s s' ->
      wellSynchronized s ->
      wf_join_see_fork s ->
      wf_join_see_fork s'.
  Proof.
    intros s s' h_comp h_ws_s h_wf_join_see_fork_s.
    unfold wf_join_see_fork in *.
    intros t i' j' h_fork h_join.
    inversion h_comp as [R h_comp1].
    assert (compatible_by R s s') as h_comp_by by assumption.
    inversion h_comp1 as  [h_bijective [h_eq h_sync]].
    inversion h_bijective as [h_restricted h_functional h_applicative h_injective h_surjective].
    assert (exists i, R i i' /\ pi i s = pi i' s') as [i [h1_i' h2_i']].
    {
      assert (i' < length s') as Ha by eauto with nth_error.
      destruct (h_surjective i' Ha)  as [i Hi]. 
      exists i; split ; [assumption | now apply h_eq].
    }
    assert (exists j, R j j' /\ pi j s = pi j' s') as [j [h1_j' h2_j']].

    {
      assert (j' < length s') as Ha by eauto with nth_error.
      destruct (h_surjective j' Ha)  as [j Hj]. 
      exists j; split ; [assumption | now apply h_eq].
    }
    assert (see s i j). 
    { apply h_wf_join_see_fork_s with t.
      rewrite h2_i'.
      assumption.
      rewrite h2_j'.
      assumption.
    }
    now apply compatible_see with s i j R.
  Qed.
  
  Lemma compatible_wf_join_all_closed : 
    forall s s', 
      compatible s s' ->
      wf_occurences s ->
      wf_open_close s ->
      wf_join_all_closed s ->
      wf_join_all_closed s'.
  Proof.
    intros s s' h_comp h_wf_occurences_s h_wf_open_close_s h_wf_join_all_closed_s.
    unfold wf_join_all_closed in *.
    intros  p t i' j' k' h_range h_owns h_join.
    inversion h_comp as [R [[_ _ h_applicative _ h_surjective] [h_eq h_sync]]].
    assert (wf_occurences s') as h_wf_occurences_s' by now apply compatible_wf_occurences with s.
    assert (wf_open_close s') as h_wf_open_close_s' by now apply compatible_wf_open_close with s.
    assert (exists i, R i i' /\ pi i s = pi i' s') as [i [h1_i h2_i]].
    {
      assert (i' < length s') by now apply range_i_lt_s with p j'.
      assert (exists i, R i i') as [i Hi] by now apply h_surjective.
      exists i; eauto.
    }
    assert (exists j, R j j' /\ pi j s = pi j' s') as [j [h1_j h2_j]]. 
    {
      assert (j' < length s') by now apply range_j_lt_s with p i'.
      assert (exists j, R j j') as [j Hj] by now apply h_surjective.
      exists j; eauto.
    }
    assert (exists k, R k k' /\ pi k s = pi k' s') as [k [h1_k h2_k]]. 
    {
      assert (k' < length s') by eauto with nth_error.
      assert (exists k, R k k') as [k Hk] by now apply h_surjective.
      exists k; eauto.
    }
    assert (action_of (pi k s) == Join t) by congruence.
    assert (owns s p t) as h_owns'. 
    {
      apply compatible_owns with s'.   
      symmetry;auto.
      assumption.
    }
    inversion h_range; subst.
    - assert (range s p i j) as h_range' by (constructor 1; congruence).
      assert (j < k) by eauto.
    
      assert (threadId_of (pi j s) == t).
      {
        assert (action_of (pi i s) == Open p) by now inversion h_range'.
        inversion h_owns'; subst.
        assert (i = i0) by wellFormed_occurences  (Open p).
        subst.
        unfold wf_open_close in h_wf_open_close_s.
        assert (action_of (pi j s) == Close p) as Hcl by congruence.
        destruct (h_wf_open_close_s j p Hcl) as [j0 [Hu [Hv Hw]]].
        assert (j0 = i0) by wellFormed_occurences (Open p).
        subst.
        congruence.
      }
      assert (synchronizeWith s j k).
      {
        constructor 1.
        constructor 3 with t; assumption.
      }
      assert (synchronizeWith s' j' k').
      {
        eapply h_sync; eauto.
      }
      now apply synchronizeWithOrder with s'.
    - assert (range s p i (length s - 1)).
      {
        constructor 2.
        rewrite h2_i.
        assumption.
        contradict HNotClosed.
        apply compatible_occursIn with s;auto.
      }
      assert (length s - 1 < k) by eauto.
      assert (k < length s) by eauto with nth_error.
      exfalso; intuition.
  Qed.

   
(*  Lemma compatible_wf_prefixOrder : 
    forall s s',
      compatible s s' ->
      wf_occurences s ->
      wf_open_close s ->
      wf_fork s ->
      wf_prefixOrder s ->
      wf_prefixOrder s'.
  Proof.
    intros s s' h_comp h_wf h_op_cl h_fork h_wf_prefixOrder.
    inversion h_comp as [R [[_ _ h_applicative _ h_surjective] [h_eq h_sync ]]]. 
    unfold wf_prefixOrder in *.
    intros p i p' i' Hi Hi' Hpp'.
    assert (exists i0, R i0 i /\ pi i0 s = pi i s') as [i0 [h1_i0 h2_i0]].
    {
      assert (i < length s') by eauto with nth_error.
      assert (exists k1, R k1 i) as [k1 Hk1] by now apply h_surjective.
      exists k1; eauto.
    } 
    assert (exists i'0, R i'0 i' /\ pi i'0 s = pi i' s') as [i'0 [h1_i'0 h2_i'0]].
    {
      assert (i' < length s') by  eauto with nth_error.
      assert (exists k1, R k1 i') as [k1 Hk1] by now apply h_surjective.
      exists k1; eauto.
    } 
    assert (action_of ( pi i0 s) == Open p) as Hi0 by congruence.
    assert (action_of ( pi i'0 s) == Open p') as Hi'0 by congruence.
    destruct (h_wf_prefixOrder p i0 p' i'0) as [Hlti0i'0 Htrib];auto.
    split.
    - destruct (h_sync i0 i i'0 i') as [h_sync1 h_sync2];auto.
      apply synchronizeWithOrder with s'.
      apply h_sync1.
      now apply aux1' with p p'.
    - intros t0 Ht0.
      assert (owns s' p' t0) as Howns_s'_p' by (constructor 1 with i';auto).
      assert (owns s p' t0) as Howns_s_p'.
      { 
        apply compatible_owns with s';auto.
        symmetry;auto.
      }
      inversion Howns_s_p';subst.
      assert (i1 = i'0) as Heqi.
      unfold wf_occurences in h_wf.
      unfold occursAtMostOnce in h_wf.
      apply h_wf with (Open p');auto.
      subst.
      assert (tribe s p t0 ) as Htrib0. 
      apply (Htrib t0);auto. 
      apply compatible_tribe with s;auto.
  Qed.
*)



  Lemma compatible_seq_order : 
    forall s, 
      wf_occurences s ->
      wf_fork s ->
      wf_open_close s ->
      wf_mutualExclusion s ->
      forall s', s ~= s' -> forall p p', sec_order s p p' -> sec_order s' p p'.
  Proof.
    intros s h_wf_occ h_wf_fork h_wf_oc h_wf_me  s' equiv p p' h_sec_order.
    inversion h_sec_order; subst.
    - inversion equiv as [R HR].
      case_eq (pi i s); [intros [t a0] h_eq | intros h_neq]; subst.
      assert (exists j, R i j /\ pi j s' = pi i s) as [j0 [Ha Hb]].
      {
        destruct HR.
        destruct H3.
        destruct H4.
        assert (i < length s) by now obtain_range_inequalities H.
        edestruct a.
        apply H5.
        exists x.
        split. 
        assumption.
        symmetry.
        now apply H3.
      }
      assert (exists j', R k j' /\ pi j' s' = pi k s) as [j' [Hu Hv]]. 
      {
        destruct HR.
        destruct H3.
        destruct H4.
        assert (k < length s) by eauto with nth_error.
        edestruct a.
        apply H5.
        exists x.
        split. 
        assumption.
        symmetry.
        now apply H3.
      }
      inversion H; subst.
      + assert (exists m, R j m /\ pi m s' = pi j s) as [m [Hx Hy]]. 
        {
          destruct HR.
          destruct H3.
          destruct H4.
          assert (j < length s) by eauto with nth_error.
          edestruct a.
          apply H5.
          exists x.
          split. 
          assumption.
          symmetry.
          now apply H3.
        }
        assert (range s' p j0 m).
        {
          constructor 1.
          congruence.
          congruence.
        }
        apply sec_order_cons_dir with j0 m j'.
        assumption.
        assert (j0 <= j' <= m).
        {
          split.
          - destruct (Peano_dec.eq_nat_dec i k).
            +  subst.
               assert (j0 = j').
               destruct HR.
               destruct H4.
               eapply f.
               apply Ha.
               apply Hu.
               auto with *.
            + assert (synchronizeWith s' j0 j').
              {
                destruct HR.
                destruct H5.
                destruct (H6 i j0 k j'); try assumption.
                apply H7.
                constructor 1.
                constructor 1 with t.
                auto with *.
                unfold Event.t in *; rewrite h_eq; reflexivity.
                unfold Event.t in *; rewrite <- H2.
                unfold Event.t in *; rewrite h_eq; reflexivity.
              }
              assert (j0 < j') by now apply synchronizeWithOrder with s'.
              auto with *.
          - destruct (Peano_dec.eq_nat_dec k j).
            + subst.
              assert (j' = m).
              destruct HR.
              destruct H4.
              eapply f; eauto.
              auto with *.
            + assert (synchronizeWith s' j' m).
              {
                destruct HR.
                destruct H5.
                destruct (H6 k j' j m); try assumption.
                apply H7.
                constructor.
                constructor 1 with t.
                auto with *.
                unfold Event.t in *; rewrite <- H2.
                rewrite h_eq; reflexivity.
                destruct (h_wf_oc _ _ Hj) as [u [Hn [Hm Hp]]].
                assert (u = i) by wellFormed_occurences (Open p).
                subst.
                unfold Event.t in *; rewrite Hp.
                rewrite h_eq; reflexivity.
              }
              assert (j' < m) by now apply synchronizeWithOrder with s'.
              auto with *.
        }
        assumption.
        congruence.
        rewrite Hb.
        rewrite Hv.
        assumption.
      +  assert (range s' p j0 (length s' - 1)).
         {
           constructor 2.
           congruence.
           contradict HNotClosed.
           eapply compatible_occursIn; eauto.
           symmetry; assumption.
         }
         apply sec_order_cons_dir with j0 (length s' - 1) j'.
         assumption.
         assert (j0 <= j').
         {
           destruct (Peano_dec.eq_nat_dec i k).
            +  subst.
               assert (j0 = j').
               destruct HR.
               destruct H4.
               eapply f.
               apply Ha.
               apply Hu.
               auto with *.
            + assert (synchronizeWith s' j0 j').
              {
                destruct HR.
                destruct H5.
                destruct (H6 i j0 k j'); try assumption.
                apply H7.
                constructor 1.
                constructor 1 with t.
                auto with *.
                unfold Event.t in *; rewrite h_eq; reflexivity.
                unfold Event.t in *; rewrite <- H2.
                unfold Event.t in *; rewrite h_eq; reflexivity.
              }
              assert (j0 < j') by now apply synchronizeWithOrder with s'.
              auto with *.
         }
         assert (j' <= length s' - 1).
         {
           rewrite <- Hv in H1.
           assert (j' < length s') by eauto with nth_error.
           intuition.
         }
         intuition.
         congruence.
         congruence.
      + inversion H; subst.
        rewrite h_neq in Hi; discriminate.
        rewrite h_neq in Hi; discriminate.
    - destruct equiv as [R HR]. 
      assert (exists j, R i j /\ pi j s' = pi i s) as [j0 [Ha Hb]].
       {
         destruct HR.
         destruct H3.
         assert (i < length s) by eauto with nth_error.
         edestruct a.
         apply H3.
         exists x.
         split. 
         assumption.
         symmetry.
         destruct H4.
         apply H4.
         assumption.
       }
       assert (exists j', R i' j' /\ pi j' s' = pi i' s) as [j' [Hu Hv]]. 
       {
         destruct HR.
         destruct H3.
         assert (i' < length s) by eauto with nth_error.
         edestruct a.
         apply H3.
         exists x.
         split. 
         assumption.
         symmetry.
         destruct H4; now apply H4.
       }
       constructor 2 with j0 j' t0.
       congruence.
       congruence.
       congruence.
       eapply compatible_tribeChildren; eauto.
       exists R; eauto.
Qed.

  Ltac surjection :=
    match goal with
        H : ?K < length ?S' |- exists k', ?R k' ?k /\ pi k' ?S = pi ?K ?S' =>
        match goal with
            HR : compatible_by ?R ?S ?S' |- _ => 
            let h_surjective := fresh in
            let Hy := fresh in
            let Hz := fresh in 
            let k' := fresh "k" in
            let Hk := fresh "Hk" in
            destruct HR as [[_ _ _ _ h_surjective] [Hy Hz]];
              destruct h_surjective with K as [k' Hk'];
              [assumption | exists k'; split; [assumption | now apply Hy]]
        end
      |  |- _ => fail "not in domain"
    end.

  Ltac surjection_ :=
    match goal with
        H : ?K < ?M, H0 : surjective (fun k => k < ?M) ?R |- exists k', ?R k' ?K =>
        let k' := fresh "k" in
        let h_k' := fresh "h_k" in
        destruct H0 with K as [k' h_k'];
          [exact H | exists k'; exact h_k']
      | H : ?K < ?M, H0 : bijective _ (fun k => k < ?M) ?R |- exists k', ?R k' ?K =>
        assert (exists k', R k' K) by (destruct H0 as [_ _ _ _ h_surjective]; surjection_);
          assumption
    end.
  
  Ltac injection_ := 
    match goal with 
        h_injective : injective ?R, Ha : ?R ?I ?J, Hb : ?R ?I' ?J  |- ?I = ?I' =>
        apply h_injective with J; [exact Ha | exact Hb]
      | h_bijective : bijective _ _ ?R, Ha : ?R ?I ?J, Hb : ?R ?I' ?J  |- ?I = ?I' =>
        let h_injective := fresh in
        assert (I = I') by
             (destruct h_bijective as [_ _ _ h_injective _];
              apply h_injective with J; [exact Ha | exact Hb]); assumption
    end.

 Ltac compsync :=
   match goal with
     | HR : compatible_by ?R ?S ?S', 
            H0 : ?R ?I' ?I, 
                 H1 : ?R ?K' ?K,
                      H2 : synchronizeWith ?S' ?I ?K |- synchronizeWith ?S ?I' ?K' => 
       let Hx := fresh in
       let Hy := fresh in
       let Hz := fresh in
       destruct HR as [Hx [Hy Hz]]; now apply (Hz _ _ _ _ H0 H1)
     | HR : compatible_by ?R ?S ?S', 
            H0 : ?R ?I' ?I, 
                 H1 : ?R ?K' ?K,
                      H2 : synchronizeWith ?S ?I' ?K' |- synchronizeWith ?S' ?I ?K => 
       let Hx := fresh in
       let Hy := fresh in
       let Hz := fresh in
       destruct HR as [Hx [Hy Hz]]; now apply (Hz _ _ _ _ H0 H1)
   end.

 Ltac compeq :=
   match goal with
     | H : compatible_by ?R ?S ?S', H0 : ?R ?I ?I' |- pi ?I ?S = pi ?I' ?S' =>
       let Hx := fresh in let Hy := fresh in let Hz := fresh in
                                             destruct H as [Hx [Hy Hz]]; eauto
     |  H : compatible_by ?R ?S ?S', H0 : ?R ?I ?I' |- pi ?I' ?S' = pi ?I ?S =>
        symmetry; compeq
     | H : compatible_by ?R ?S ?S', H0 : ?R ?I ?I', H1 : pi ?I ?S == ?A |- pi ?I' ?S' == ?A =>
       unfold Event.t in *; rewrite <- H1; compeq 
     | H : compatible_by ?R ?S ?S', H0 : ?R ?I ?I', H1 : pi ?I' ?S' == ?A |- pi ?I ?S == ?A =>
       unfold Event.t in *; rewrite <- H1; compeq 
     |  |- ?F (pi ?I ?S) = ?F (pi ?I' ?S') => f_equal; compeq
   end.

  Ltac compatibility :=
    match goal with
        H : ?K < length ?S, HR : compatible_by ?R ?S' ?S |- exists k', ?R k' ?K /\ pi k' ?S' = pi ?K ?S =>
        let h_bijective := fresh in
        let Hu := fresh in
        let Hv := fresh in
        let k' := fresh "k" in
        let h_k' := fresh "h_k" in
        destruct HR as [h_bijective [Hu Hv]];
          assert (exists k', R k' K) as [k' h_k'] by surjection_;
          exists k'; split; [assumption | exact (Hu _ _ h_k')]
      | |- synchronizeWith _ _ _ => compsync
      | |- pi ?I ?S = pi ?J ?S' => compeq
      | |- pi ?I ?S = pi ?J ?S' => compeq
      | |- ?F (pi ?I ?S) = ?F (?pi ?J ?S') => compeq
    end.
  
(* Lemma wf_open_close_same_thread : 
                forall s, wf_occurences s -> wf_open_close s ->
                          forall p i j,
                            action_of (pi i s) == Open p ->
                            action_of (pi j s) == Close p ->
                            threadId_of (pi j s) = threadId_of (pi i s).
              Proof.
                intros s h_wf_occ h_wf_oc p i j h_i h_j.
                destruct (h_wf_oc  _ _  h_j) as [i0 [hi0a [hi0b hi0c]]]. 
                assert (i = i0) by wf_intuition; congruence.
              Qed.   
*)

  Ltac wf_intuition :=
    match goal with 
      | H : wellFormed ?S |- _ => inversion H; clear H; wf_intuition
      | H : wf_occurences ?S, 
            H0 : action_of (pi ?I ?S) == ?A, HA : action_of (pi ?J ?S) == ?A |- ?I = ?J =>
        wellFormed_occurences A
     (* | H : wf_occurences ?S,
            H0 : wf_open_close ?S, 
                 H1 : range ?S ?P ?I ?J,
                      H2 : action_of (pi ?J ?S) == Close ?P
        |- threadId_of (pi ?J ?S) = threadId_of (pi ?I ?S) =>
        assert (action_of (pi I S) == Open P); 
          [now inversion H1 | now apply wf_open_close_same_thread with P]*)
      | H : wf_occurences ?S,
            H0 : wf_open_close ?S, 
                 H1 : action_of (pi ?I ?S) == Open ?P,
                      H2 : action_of (pi ?J ?S) == Close ?P
        |- threadId_of (pi ?J ?S) = threadId_of (pi ?I ?S) =>
        let i0 := fresh in
        let hi0a := fresh in
        let hi0b := fresh in
        let hi0c := fresh in
        destruct (H0 _ _ H2) as [i0 [hi0a [hi0b hi0c]]];
          assert (I = i0) by wf_intuition; subst;
          first [assumption | congruence]
    end.

  Lemma compatible_neq_seq_order : 
    forall s,
      wf_occurences s ->
      wf_fork s ->
      wf_open_close s ->
      wf_mutualExclusion s ->
      forall s',
        s ~= s' -> forall p p', ~ sec_order s p p' -> ~sec_order s' p p'.
  Proof.
    intros s h_wf_occ h_wf_fork h_wf_oc h_wf_me s' equiv p p' h_sec.
    contradict h_sec.
    assert (wf_occurences s') by (apply compatible_wf_occurences with s; eauto).
    assert (wf_open_close s') as h_wf_s' by (apply compatible_wf_open_close with s; eauto).
    assert (s' ~= s) as equiv' by (eapply compatible_sym; eauto). 
    destruct equiv' as [R' HR'].
    destruct equiv as [R HR].
    destruct h_sec.
    - assert (k < length s') by eauto with nth_error.
      assert (i < length s') by (inversion H0; eauto with nth_error).
      assert (exists k', R k' k /\ pi k' s = pi k s') as [k' [Hu Hv]] by compatibility.
      assert (exists i', R i' i /\ pi i' s = pi i s') as [i' [Ha Hb]] by compatibility.
      assert (i' <= k') as h_lt1.
      {
        destruct (Peano_dec.eq_nat_dec i k).
        - subst; assert (i' = k') by (destruct HR; injection_); intuition.
        - case_eq (pi k s'); 
          [intros [t a] h_eq | intros h_neq;rewrite h_neq in H2; discriminate]; subst.
          assert (synchronizeWith s' i k).
          {
            constructor 1; constructor 1 with t; unfold Event.t in *;
            [intuition | rewrite H3; rewrite h_eq; reflexivity | rewrite h_eq; reflexivity].
          }
          assert (synchronizeWith s i' k') by compatibility.
          assert (i' < k') by now apply synchronizeWithOrder with s.
          intuition.
      }
      assert (compatible_by (inverse R) s' s) as h_comp_inv by now apply symmetric_compatible_R.
      destruct compatible_range with s' s (inverse R) p i j as [i2 [Hx Hy]]; try assumption.   
      unfold inverse in *.
      assert (i2 = i').
      { 
        assert (action_of (pi i' s) == Open p) by
            (inversion H0; subst; unfold Event.t in *; congruence).
        assert (action_of (pi i2 s) == Open p) by
            (assert (pi i2 s = pi i s') by compatibility; congruence).
        wf_intuition.
      }
      subst.
      destruct Hy as [[j' [h_j' [h_range' h_closep]]] | [h_range' hNotOccursIn]].
      * assert (pi j' s = pi j s') by (destruct HR; now apply H7).
        assert (k' <= j') as h_lt2.
        {
          destruct (Peano_dec.eq_nat_dec k j); intros; subst.
          - assert (k' = j') by (subst; destruct HR; injection_). 
            intuition.
          - assert (k' < j').
            {
              assert (synchronizeWith s' k j).
              {
                case_eq (pi k s'); 
                [intros [t a] h_eq | intros h_neq;rewrite h_neq in H2; discriminate]; subst.
                constructor; constructor 1 with t.
                - intuition.
                - unfold Event.t in *; rewrite h_eq; reflexivity.
                - assert (action_of (pi i' s) == Open p) by now inversion h_range'.
                  assert (threadId_of (pi j' s) = threadId_of (pi i' s)) by wf_intuition.
                  assert (threadId_of (pi i s') == t) by now (rewrite h_eq in H3; simpl in H3).
                  unfold Event.t in *; congruence.
              }
              assert (synchronizeWith s k' j') by compatibility.
              now apply synchronizeWithOrder with s.
            }
            intuition.
        }
        apply sec_order_cons_dir with i' j' k'; 
          [assumption | intuition | congruence | congruence].
      * assert (k' <= length s - 1) 
          as h_lt2
            by (assert (k' < length s) by (rewrite <- Hv in H2; eauto with nth_error); intuition).
        apply sec_order_cons_dir with i' (length s - 1) k'; 
          [assumption | intuition | congruence | congruence].
    - assert (i < length s') by eauto with nth_error.
      assert (i' < length s') by eauto with nth_error.
      assert (exists j, R j i /\ pi j s = pi i s') as [j [Hu Hv]] by compatibility.
      assert (exists j', R j' i' /\ pi j' s = pi i' s') as [j' [Ha Hb]] by compatibility.
      apply sec_order_cons_ind with j j' t0.
      congruence.
      congruence.
      congruence.
      apply compatible_tribeChildren with s'; try assumption.
      symmetry; exists R; eauto.
  Qed.
  
  Lemma compatible_concurrent :
    forall s,
      wf_occurences s ->
      wf_fork s ->
      wf_open_close s ->
      wf_mutualExclusion s ->
      forall s',
        s ~= s' -> forall p p', concurrent s p p' -> concurrent s' p p'.
  Proof.
    intros s h_wf_occ h_wf_fork h_wf_oc h_wf_me s' equiv p p' h_conc.
    unfold concurrent.
    destruct h_conc as [h_occ1 [h_occ2 [ hnot_seq1 hnot_seq2]]].
    split.
    eapply compatible_occursIn; eauto.
    split.
    eapply compatible_occursIn; eauto.
    split; eauto using  compatible_neq_seq_order.
  Qed.


 Lemma compatible_concurrent_rev :
    forall s,
      wf_occurences s ->
      wf_fork s ->
      wf_open_close s ->
      wf_mutualExclusion s ->
      forall s',
        s ~= s' -> forall p p', concurrent s' p p' -> concurrent s p p'.
  Proof.
    intros s h_wf_occ h_wf_fork h_wf_oc h_wf_me s' equiv p p' h_conc.
    unfold concurrent.
    destruct h_conc as [h_occ1 [h_occ2 [hnot_seq1 hnot_seq2]]].
    split.
    eapply compatible_occursIn; [symmetry; eauto | assumption].
    split.
    eapply compatible_occursIn; [symmetry; eauto | assumption].
    split; [contradict hnot_seq1 | contradict hnot_seq2]; eauto using compatible_seq_order.
  Qed.
  
  Lemma concurrent_sym : 
    forall s p p', concurrent s p p' -> concurrent s p' p.
  Proof.
    unfold concurrent; tauto.
  Qed.

  Lemma compatible_wf_mutualExclusion : 
    forall s s',
      compatible s s' ->
      wf_occurences s ->
      wf_fork s ->
      wf_open_close s ->
      wf_mutualExclusion s ->
      wf_mutualExclusion s'.
  Proof.
    intros s s' h_comp h_wfocc h_wf_fork h_wf_oc h_me.
    inversion h_comp as [R [[_ _ h_applicative _ h_surjective] [h_eq h_sync ]]]. 
    unfold wf_mutualExclusion in *.
    assert (wf_occurences s') as h_wfoccs' by now apply compatible_wf_occurences with s.
    unfold wf_occurences in *;unfold occursAtMostOnce in *.
    intros p p' h_conc.
    assert (occursIn s  (Open p)) as Hsp.
    {
      destruct h_conc as [Hu [Hv]].
      apply compatible_occursIn with s';auto.
      symmetry; assumption.
    }
    assert (occursIn s  (Open p')) as Hsp'.
    {
      destruct h_conc as [Hu [Hv]].
      apply compatible_occursIn with s';auto.
      symmetry;auto.
    }
    inversion Hsp as [i0 a Ha0];inversion Hsp' as [j0 b Hb0];subst.
    destruct (h_me p p') as [H_pp' | H_p'p];auto.
    now apply compatible_concurrent_rev with s'.
    - unfold precedes in H_pp'.
      inversion H_pp';subst.
      
      assert (j = j0) by now apply h_wfocc with (Open p');subst. 
      assert (exists k, R i k /\ pi i s = pi k s') as [k1 [h1_k1 h2_k1]]. 
      {
        assert (i < length s) by eauto with nth_error.
        assert (exists k1, R i k1) as [k1 Hk1] by now apply h_applicative.
        exists k1; eauto.
      }
      assert (exists k2, R j0 k2 /\ pi j0 s = pi k2 s') as [k2 [h1_k2 h2_k2]]. 
      {
        assert (j0 < length s) by eauto with nth_error.
        assert (exists k2, R j0 k2) as [k2 Hk1] by now apply h_applicative.
        exists k2; eauto.
      }
      subst.
      left.
      unfold precedes.
      constructor 1 with k1 k2;auto.
      + apply synchronizeWithOrder with s'.
        destruct ( h_sync i k1 j0 k2) as [h_sync1 h_sync2];auto.
        apply h_sync1.
        constructor; constructor 4 with p p'; auto.
        now apply compatible_concurrent_rev with s'.
      + rewrite  <- h2_k1 ;auto.
      + congruence.
    - unfold precedes in H_p'p.
      inversion H_p'p;subst.
      assert (j = i0) by now apply h_wfocc with (Open p);subst. 
      assert (exists k, R i k /\ pi i s = pi k s') as [k1 [h1_k1 h2_k1]]. 
      {
        assert (i < length s) by  eauto with nth_error.
        assert (exists k1, R i k1) as [k1 Hk1] by now apply h_applicative.
        exists k1; eauto.
      }
      assert (exists k2, R i0 k2 /\ pi i0 s = pi k2 s') as [k2 [h1_k2 h2_k2]]. 
      {
        assert (i0 < length s) by  eauto with nth_error.
        assert (exists k2, R i0 k2) as [k2 Hk1] by now apply h_applicative.
        exists k2; eauto.
      }
      subst.
      right.
      unfold precedes.
      constructor 1 with k1 k2;auto.
      + apply synchronizeWithOrder with s'.
        destruct ( h_sync  i k1  i0 k2) as [h_sync1 h_sync2];auto.
        apply h_sync1.
        constructor. 
        constructor 4 with p' p;auto. 
        apply concurrent_sym.
        now apply compatible_concurrent_rev with s'.
      + rewrite  <- h2_k1 ;auto.
        + congruence.
  Qed.
  
 (* Lemma compatible_wf_openInSection : 
    forall s s',
      compatible s s' ->

      wf_occurences s ->
      wf_fork s ->
      wf_open_close s ->
      wf_openInSection s ->
      wf_mutualExclusion s ->
      wf_openInSection s'.
  Proof. 
    intros s s' h_comp h_wf_occ h_wf_fork h_wf_op_cl h_wf_openInSection h_wfMut.
    inversion h_comp as [R [[_ _ h_applicative _ h_surjective] [h_eq h_sync ]]].
    unfold wf_openInSection in *.
    intros p i j p' k h_range h_open_p' h_int.
    assert (j < length s') as h_lt_j by (inversion h_range; subst; [eauto with nth_error | intuition]).
    assert (i < length s') as h_lt_i by intuition.
    assert (k < length s') as h_lt_k by intuition.


    assert (exists i', R i' i /\ pi i' s = pi i s') as [i' [h_i' h_eq_i']]. 
    {
      destruct (h_surjective i h_lt_i) as [i' h_i']. 
      exists i'; split; [exact h_i' | now apply h_eq].
    }
    assert (exists k', R k' k /\ pi k' s = pi k s') as [k' [h_k' h_eq_k']]. 
    {
      destruct (h_surjective k h_lt_k) as [k' h_k']. 
      exists k'; split; [exact h_k' | now apply h_eq].
    }

    assert (exists j', R j' j /\ pi j' s = pi j s') as [j' [h_j' h_eq_j']]. 
    {
      destruct (h_surjective j h_lt_j) as [j' h_j']. 
      exists j'; split; [exact h_j' | now apply h_eq].
    }

    assert (synchronizeWith s' i k).
    {
      assert (p <> p').
      {
        assert (action_of (pi i s') == Open p) by now inversion h_range.
        intro; subst.
        assert (wf_occurences s') by now apply compatible_wf_occurences with s.
        assert (k = i) by wellFormed_occurences (Open p').
        subst; exfalso; intuition.
      }
      destruct aux2' with s' i k p p'.    
      now apply compatible_wf_occurences with s.
      now apply compatible_wf_fork with s.
      now apply compatible_wf_open_close with s.
      now apply compatible_wf_mutualExclusion with s.
      assumption.
      inversion h_range; assumption.
      assumption.
      assumption.
      assert (k < i).
      apply synchronizeWithOrder with s'.
      assumption.
      exfalso; intuition.
    }
    inversion h_range; subst.
    - destruct (Compare_dec.lt_eq_lt_dec k' j') as [ [] | ].
      + assert (range s p i' j') by (constructor 1; congruence).
        assert (i' < k' <= j').
        {
          split.
          - assert (synchronizeWith s i' k').
            {
              eapply h_sync; eauto.
            }
            apply synchronizeWithOrder with s.
            assumption.
          - intuition.
        }
        apply h_wf_openInSection with i' j' k'.
        assumption.
        rewrite h_eq_k'.
        assumption.
        assumption.
      + subst.
        rewrite <- h_eq_j' in Hj.
        rewrite <- h_eq_k' in h_open_p'.
        rewrite h_eq_k' in Hj.
        rewrite h_eq_k' in h_open_p'.
        rewrite h_open_p' in Hj.
        discriminate.
      + {
          destruct (P.eq_dec p p').
          - subst.
            assert (i = k).
            {
              assert (wf_occurences s') 
                as HWFOCC
                  by now apply compatible_wf_occurences with s.
              wellFormed_occurences (Open p').
            }
            subst; exfalso; intuition.
          - destruct (P.lt_dec p p');[ assumption|].
            destruct (P.lt_dec p' p).
            + unfold wf_prefixOrder in *.
              assert (wf_prefixOrder s') as HWFPO by 
                  now apply compatible_wf_prefixOrder with s.
              destruct (HWFPO _ _ _ _ h_open_p' Hi).
              assumption.
              exfalso; intuition.
            + assert (p # p') by tauto.
              assert (wf_mutualExclusion s') as HWFMUT by
                  now apply compatible_wf_mutualExclusion with s.
              assert (occursIn s' (Open p)) by eauto.
              assert (occursIn s' (Open p')) by eauto.
              destruct (HWFMUT _ _ H1 H2 H0).
              * unfold precedes in H3.
                inversion H3; subst.
                assert (wf_occurences s').
                now apply compatible_wf_occurences with s.
                assert (i0 = j) by wellFormed_occurences (Close p).
                assert (j0 = k) by wellFormed_occurences (Open p').
                subst.
                exfalso; intuition.
              * unfold precedes in H3.
                inversion H3; subst.
                assert (wf_occurences s').
                now apply compatible_wf_occurences with s.
                assert (j0 = i) by wellFormed_occurences (Open p).
                assert (wf_open_close s') as HWFOP.
                now apply compatible_wf_open_close with s.
                destruct (HWFOP _ _ Ha) as [u0 [Hc [Hd He]]].
                assert (u0 = k) by wellFormed_occurences (Open p').
                subst.
                exfalso; intuition.
        }
    - assert (range s p i' (length s -1)). 
      {
        constructor 2.
        congruence.
        contradict HNotClosed.
        now apply compatible_occursIn with s.
      }
      assert (action_of (pi i' s) == Open p).
      {
        inversion h_range; congruence.
      }
      assert (i' < k' <= length s - 1).
      {
        assert (synchronizeWith s i' k').
        eapply h_sync; eauto.
        split.
        eapply synchronizeWithOrder; eauto.
        assert (k' < length s).
        {
          rewrite <- h_eq_k' in h_open_p'.
          eauto with nth_error.
        }
        intuition.
      }
      apply h_wf_openInSection with i' (length s - 1) k'; try assumption.
      congruence.
Qed.
*)
  

  Lemma compatible_wf_seq_order : 
    forall s s',
      compatible s s' ->
      wellFormed s ->
      wellSynchronized s ->
      wf_seq_order s'.
  Proof.
    unfold wf_seq_order.
    intros s s' h_comp h_wf h_ws p i j h_range h_close_p k p' h_int h_id_eq h_open_p'. 
    inversion h_wf as [ _ _ _ h_wf_open_close h_wseq _ _ _].
    inversion h_comp as [R h_compatible].

    assert (j < length s') as h_lt_j by (inversion h_range; subst; [eauto with nth_error | intuition]).
    assert (k < length s') as h_lt_k by intuition.
    assert (i < length s') as h_lt_i by intuition.

    assert (exists i', R i' i /\ pi i' s = pi i s') as [i' [h_i' h_eq_i']]. 
    {
      inversion h_compatible as [[_ _ _ _ h_surj] [h_eq2 _]]. 
      destruct (h_surj i h_lt_i) as [i' h_i']. 
      exists i'; split; [exact h_i' | now apply h_eq2].
    }
    assert (exists k', R k' k /\ pi k' s = pi k s') as [k' [h_k' h_eq_k']]. 
    {
      inversion h_compatible as [[_ _ _ _ h_surj] [h_eq2 _]]. 
      destruct (h_surj k h_lt_k) as [k' h_k']. 
      exists k'; split; [exact h_k' | now apply h_eq2].
    }

    assert (exists j', R j' j /\ pi j' s = pi j s') as [j' [h_j' h_eq_j']].
    {
      inversion h_compatible as [[_ _ _ _ h_surj] [h_eq2 _]]. 
      destruct (h_surj j h_lt_j) as [j' h_j']. 
      exists j'; split; [exact h_j' | now apply h_eq2].
    }


    assert (action_of (pi i' s) == Open p) as h_i'_open_p by (inversion h_range; subst; congruence).
    assert (action_of (pi j' s) == Close p) as h_j'_close_p by congruence.
    assert (action_of (pi k' s) == Open p') as h_k'_open_p' by congruence.

    assert (range s p i' j') by now constructor 1.

    case_eq (pi i' s); 
      [intros [t a] h_eq; subst | intros h_none; rewrite h_none in h_i'_open_p; discriminate ].
    assert (threadId_of (pi i' s) == t) by (rewrite h_eq; reflexivity).
    assert (threadId_of (pi k' s) == t) by congruence.
    assert (threadId_of (pi j' s) == t).
    {
      destruct (h_wf_open_close _ _ h_j'_close_p) as [j0 [Ha [Hb Hc]]].
      replace i' with j0 in * by wellFormed_occurences (Open p).
      congruence.
    }

    assert (i' < k' < j'). 
    {
      assert (synchronizeWith s' i k).
      {
        constructor 1.
        constructor 1 with t; unfold Event.t in *; 
        [intuition | congruence | congruence].
      }
      assert (synchronizeWith s' k j). 
      {
        constructor 1.
        constructor 1 with t; unfold Event.t in *; 
        [intuition | congruence | congruence].
      }
      inversion h_compatible as [ _ [ _ Hb]].
      assert (synchronizeWith s i' k') by now apply (Hb i' i k' k).
      assert (synchronizeWith s k' j') by now apply (Hb k' k j' j).
      split;eapply synchronizeWithOrder; eauto.
    }

    destruct h_wseq with p i' j' k' p' as [l' [h_int0 h_close_p']]; try congruence.
    
    assert (threadId_of (pi l' s) == t). 
    {
      destruct (h_wf_open_close _ _ h_close_p') as [j0 [Ha [Hb Hc]]].
      replace j0 with k' in * by wellFormed_occurences (Open p').
      congruence.
    }

    assert (exists l, R l' l /\ pi l' s = pi l s') as [l [h_l h_eq_l]].
    {
      assert (l' < length s) as h_lt by eauto with nth_error.
      inversion h_compatible as [[_ _ h_appl _ _] [h_eq2 _ ]].
      destruct (h_appl l' h_lt) as [l h_l]. 
      exists l; split; [assumption | now apply h_eq2].
    }
 
    assert (k < l < j).
    {
      assert (synchronizeWith s k' l').
      {
        constructor 1. 
        constructor 1 with t; unfold Event.t in *;
        [intuition | congruence | congruence].
      }
      assert (synchronizeWith s l' j'). 
      {
        constructor 1. 
        constructor 1 with t; unfold Event.t in *; 
        [intuition | congruence | congruence].
      }
      inversion h_compatible as [ _ [ _ Hb]].
      assert (synchronizeWith s' k l) by now apply (Hb k' k l' l).
      assert (synchronizeWith s' l j) by now apply (Hb l' l j' j).
      split; eapply synchronizeWithOrder; eauto.
    }
    exists l; split; congruence.
Qed.


 Lemma compatible_wellFormed : 
    forall s s', 
      compatible s s' ->
      wellFormed s ->
      wellSynchronized s ->
      wellFormed s'.
  Proof.
    intros s s' h_comp h_wf_s h_ws_s.
    inversion h_wf_s.
    constructor.
    now apply compatible_wf_occurences with s.
    now apply compatible_wf_fork with s.
    now apply compatible_wf_join with s.
    now apply compatible_wf_open_close with s.
    now apply compatible_wf_seq_order with s.
    now apply compatible_wf_join_see_fork with s.
    now apply compatible_wf_join_all_closed with s.
    (*now apply compatible_wf_prefixOrder with s.
    now apply compatible_wf_openInSection with s.*)
    now apply compatible_wf_mutualExclusion with s.
  Qed.
  
  Lemma compatible_exclude : 
    forall s s',
      wf_occurences s ->
      wf_open_close s ->
      compatible s s' -> 
      forall p t, exclude s p t -> exclude s' p t.
  Proof.
    intros s s' h_wf_occurences h_wf_open_close h_comp p t [h_pending h_notInTribe].
    split.
    - now apply compatible_pending with s.
    - assert (wf_occurences s') by (apply compatible_wf_occurences with s;auto).
      assert (wf_open_close s') by (apply compatible_wf_open_close with s;auto).
      contradict h_notInTribe.
      apply compatible_tribe with s';auto.
      symmetry;assumption.
  Qed.

  Lemma compatible_outerExclude : 
    forall s s',
      wf_occurences s ->
      wf_open_close s ->
      wf_fork s ->
      wf_mutualExclusion s ->
      compatible s s' ->
      forall p t, outerExclude s p t -> outerExclude s' p t.
  Proof.
    intros s s' H_occ H_op_cl H_fork H_mut H_comp p t H_outerExclude.
    inversion H_outerExclude as [ Ha  Hb  ].
    constructor.
    - now apply compatible_exclude with s.
    - intros p' H_exclude Hneq.
      assert (exclude s p' t) as Hexl. 
      { assert (wf_occurences s') as H_occ_s' by now apply compatible_wf_occurences with s.
        assert (wf_open_close s') by (apply compatible_wf_open_close with s;auto).
    
        apply compatible_exclude with s';auto.
        symmetry;auto.
      }
      assert (occursAfter s (Open p) (Open p')) as Haft by auto.
      inversion Haft as [ i j a' Hlt Hi Hj];subst. 
      
      inversion H_comp as [R [[h1 h2 h_applicative h3 h_surjective] [h_eq h_sync ]]]. 
      assert ( synchronizeWith s i j \/ synchronizeWith s j i)  as Hsync by now apply aux2' with p p'.
      destruct Hsync as [Hsync1 | Hsync2].
      +  assert (exists i', R i i' /\ pi i s = pi i' s') as [i' [h1_i' h2_i']].
         {
           assert (i < length s) as Hu by eauto with nth_error.
           destruct (h_applicative i Hu) as [i' h_i'].
           exists i'; auto.
         }
          assert (exists j', R j j' /\ pi j s = pi j' s') as [j' [h1_j' h2_j']].
         {
           assert (j < length s) as Hu by eauto with nth_error.
           destruct (h_applicative j Hu) as [j' h_j'].
           exists j'; auto.
         }
         subst.
         destruct (h_sync i i' j j') as [h_sync1 h_sync2];auto.
         assert (synchronizeWith s' i' j') as h_sync_i'j' by now apply h_sync1.
         assert (i'<j') as Hlti'j' by now apply synchronizeWithOrder with s'.
         constructor 1 with i' j';auto.
         rewrite <- h2_i';auto.
         rewrite <- h2_j';auto.
      +  assert (j<i) as Hltji by now apply synchronizeWithOrder with s.
         contradict Hlt; lia.
  Qed.

  Lemma compatible_wellSynchronized : 
    forall s s',
      compatible s s' ->
      wellSynchronized s ->
      wellSynchronized s'.
  Proof.
    intros s s' h_comp  h_wf_sync.
    inversion h_comp as [R [[ _ h_func h_applicative _ h_surjective] [h_eq h_sync ]]]. 
    unfold wellSynchronized in *.
    intros i' j' a a' Hlt_i'j' Hi' Hj' Hcfl.
    assert (exists i, R i i' /\ pi i s = pi i' s') as [i [h1_i h2_i]].
    {
      assert (i' < length s') by  eauto with nth_error.
      assert (exists k1, R k1 i') as [k1 Hk1] by now apply h_surjective.
      exists k1; eauto.
    } 
    assert (exists j, R j j' /\ pi j s = pi j' s') as [j [h1_j h2_j]].
    {
      assert (j' < length s') by  eauto with nth_error.
      assert (exists k1, R k1 j') as [k1 Hk1] by now apply h_surjective.
      exists k1; eauto.
    } 

    assert (action_of  (pi i s) == a ) as Hi by now rewrite <- h2_i in Hi' .
    assert (action_of  (pi j s) == a' ) as Hj by now rewrite <- h2_j in Hj' .

    destruct (Compare_dec.lt_eq_lt_dec i j) as [[Hlt | Heq] | Hgt].
    - destruct (h_sync i i' j j') as [h_sync1 h_sync2];auto.
      assert (synchronizeWith s i j) as Hsync_s by now  apply h_wf_sync with a a'.    
      now apply h_sync1.
    - rewrite <- Heq in h1_j.
      unfold functionnal in h_func.
      assert (i'=j') as Heq' by now apply (h_func i i' j').
      contradict Heq'.
      lia.
    - destruct (h_sync j j' i i') as [h_sync1 h_sync2];auto.
      assert (conflict a' a) as Hcfl'.
      {
        inversion Hcfl.
        - constructor 2.
        - constructor 1.
        - constructor 3.
      }
      assert (synchronizeWith s j i) as Hsync_s.  apply h_wf_sync with a' a;auto.  
      assert ( synchronizeWith s' j' i') as Hsync_j'i' by (apply h_sync1;auto).
      assert (j'<i') as Hlt_j'i' by now apply  synchronizeWithOrder with s'.
      contradict Hlt_j'i'; lia.
  Qed.

 
  (** Additional results *)


 
 Ltac application_ :=
    match goal with
        H : ?K < ?M, H0 : applicative (fun k => k < ?M) ?R |- exists k', ?R ?K k' =>
        let k' := fresh "k" in
        let h_k' := fresh "h_k" in
        destruct H0 with K as [k' h_k'];
          [exact H | exists k'; exact h_k']
      | H : ?K < ?M, H0 : bijective (fun k => k < ?M) _ ?R |- exists k', ?R ?K k' =>
        assert (exists k', R K k') by (destruct H0 as [_ _ h_applicative _ _]; application_);
          assumption
    end.
(*
 Ltac compsync2 :=
   match goal with
     | HR : compatible_by ?R ?S ?S', 
            H0 : ?R ?I ?I', 
                 H1 : ?R ?K ?K',
                      H2 : synchronizeWith ?S' ?I' ?K' |- synchronizeWith ?S ?I ?K => 
       let Hx := fresh in
       let Hy := fresh in
       let Hz := fresh in
       destruct HR as [Hx [Hy Hz]]; now apply (Hz _ _ _ _ H0 H1)
     | HR : compatible_by ?R ?S ?S', 
            H0 : ?R ?I ?I', 
                 H1 : ?R ?K ?K',
                      H2 : synchronizeWith ?S ?I ?K |- synchronizeWith ?S' ?I' ?K' => 
       let Hx := fresh in
       let Hy := fresh in
       let Hz := fresh in
       destruct HR as [Hx [Hy Hz]]; now apply (Hz _ _ _ _ H0 H1)
   end.
*)
  Ltac compatibility2 :=
    match goal with
       | H : ?K < length ?S, HR : compatible_by ?R ?S ?S' |- exists k', ?R ?K k' /\ pi ?K ?S = pi k' ?S' =>
        let h_bijective := fresh in
        let Hu := fresh in
        let Hv := fresh in
        let k' := fresh "k" in
        let h_k' := fresh "h_k" in
        destruct HR as [h_bijective [Hu Hv]];
          assert (exists k', R K k') as [k' h_k'] by application_;
          exists k'; split; [assumption | exact (Hu _ _ h_k')]
    end.

  Ltac functionnal_ := 
    match goal with 
        h_functionnal : functionnal ?R, Ha : ?R ?I ?J, Hb : ?R ?I ?J'  |- ?J = ?J' =>
        apply h_functionnal with I; [exact Ha | exact Hb]
      | h_bijective : bijective _ _ ?R, Ha : ?R ?I ?J, Hb : ?R ?I ?J'  |- ?J = ?J' =>
        let h_functionnal := fresh in
        assert (J = J') by
            (destruct h_bijective as [_ h_functionnal _ _ _];
             apply h_functionnal with I; [exact Ha | exact Hb]); assumption
    end.

Lemma compatible_range_owner :
  forall s s',
    wf_occurences s ->
    wf_open_close s ->
    forall R,
    compatible_by R s s' ->
    forall p i j k,
      range s p i j ->
      i < k <= j ->
      threadId_of (pi i s) = threadId_of (pi k s) ->
      exists i' k' j',
        range s' p i' j' /\
        i' < k' <= j' /\
        pi i' s' = pi i s /\ pi k' s' = pi k s /\ 
        (action_of (pi j' s') == Close p \/ (j' = length s' - 1 /\ ~ occursIn s' (Close p))). 
Proof.
  intros s s' h_wf_occ h_wf_oc R HR p i j k h_range h_int h_tid_eq.
  case_eq (pi i s); [
      intros [t a] h_eq 
    | intros h_neq; inversion h_range as [ ? Ha | ? Ha]; subst; rewrite h_neq in Ha; discriminate]; 
  rewrite h_eq in *; simpl in *.
  assert (k < length s) by eauto with nth_error.
  assert (i < length s) by eauto with nth_error.
  assert (exists i', R i i' /\ pi i s = pi i' s') as [i' [Ha Hb]] by compatibility2.
  assert (exists k', R k k' /\ pi k s = pi k' s') as [k' [Hu Hv]] by compatibility2.  
  assert (i' < k') as h_lt1.
  {
    destruct (Peano_dec.eq_nat_dec i k).
    - assert (i' = k') by (subst; destruct HR; functionnal_).
      intuition.
    - assert (i' < k').
      {
        assert (synchronizeWith s i k).
        {
          constructor 1; constructor 1 with t; unfold Event.t in *;
          [intuition | rewrite h_eq; reflexivity | congruence].
        }
        assert (synchronizeWith s' i' k')  by compatibility.
        now apply synchronizeWithOrder with s'.
      } 
      assumption.
  }
  destruct compatible_range with s s' R p i j as [i2 [Hx [Hy | Hy]]]; try assumption.   
  - assert (i2 = i') by (destruct HR; functionnal_); subst.
    destruct Hy as [j' [h_j' [h_range' h_closep]]].
    assert (k' <= j') as hlt2.
    {
      assert (pi j s = pi j' s') by (destruct HR as [ _ [ ? _ ]]; auto).
      destruct (Peano_dec.eq_nat_dec k j).
      - assert (k' = j') by now (subst; destruct HR; functionnal_).
        intuition.
      - assert (k' < j').
        {
          assert (synchronizeWith s k j).
          {
            constructor 1; constructor 1 with t; unfold Event.t in *.
            - intuition.
            - congruence.
            - assert (action_of (pi i s) == Open p) by now inversion h_range.
              assert (action_of (pi j s) == Close p) by congruence.
              assert (threadId_of (pi j s) = threadId_of (pi i s)) by wf_intuition.
              unfold Event.t in *; rewrite H4; rewrite h_eq; reflexivity.
          }
          assert (synchronizeWith s' k' j') by compatibility.
          now apply synchronizeWithOrder with s'.
        }
        intuition.
    }
    exists i', k', j'; repeat first [congruence | constructor].
  - assert (i2 = i') by (destruct HR; functionnal_); subst.
    destruct Hy as [h_range' h_closep].
    assert (k' <= length s' - 1).
    {
      assert (k' < length s') by (destruct HR as [ [h_r] ]; apply (h_r _ _ Hu)).
      intuition.
    }
    exists i', k', (length s' - 1); repeat first [congruence | constructor 2 | constructor ].
Qed.

Lemma compatible_range_owner_inv :
  forall s s',
    wf_occurences s ->
    wf_open_close s ->
    forall R,
    compatible_by R s s' ->
    forall p i' j' k',
      range s' p i' j' ->
      i' < k' <= j' ->
      threadId_of (pi i' s') = threadId_of (pi k' s') ->
      exists i k j,
        range s p i j /\
        i < k <= j /\
        pi i s = pi i' s' /\ pi k s = pi k' s' /\ 
        (action_of (pi j s) == Close p \/ (j = length s - 1 /\ ~ occursIn s (Close p))). 
Proof.
  intros s s' h_wf_occ h_wf_oc R h_comp p i' j' k' h_range h_int h_tid_eq.
  assert (wf_occurences s') by
      (apply compatible_wf_occurences with s; [exists R; eauto | assumption]).
  assert (wf_open_close s') by
      (apply compatible_wf_open_close with s; [exists R; eauto | assumption]).
  assert (compatible_by (inverse R) s' s) by now apply symmetric_compatible_R.
  edestruct compatible_range_owner; eauto.
Qed.

  Lemma occursIn_s1e_s2e :
    forall s1 s2,
      s1 ~= s2 ->
      forall e a,
        occursIn (s1 • e) a -> occursIn (s2 • e) a.
  Proof.
    intros s1 s2 equiv e a h_occursIn.
    inversion h_occursIn as [i ? Hi]; subst.
    destruct (Compare_dec.lt_dec i (length s1)).
    - assert (pi i (s1 • e) = pi i s1) by eauto with nth_error.
      destruct equiv as [R HR].
      assert (exists i', R i i' /\ pi i' s2 = pi i s1) as [i' [Ha Hb]].
      {
        destruct HR.
        destruct H0.
        edestruct a0; eauto.
        exists x.

        split.
        assumption.
        destruct H1.
        symmetry; apply H1.
        assumption.
      }
      rewrite H in Hi.
      rewrite <- Hb in Hi.
      exists i'.
      eauto with nth_error.
    - assert (i = length s1).
      {
        assert (i < length (s1 • e)) by eauto with nth_error.
        autorewrite with length in H; simpl in H.
        intuition.
      }
      subst.
      autorewrite with nth_error in Hi.
      injection Hi; intros; subst.
      exists (length s2).
      autorewrite with nth_error.
      destruct e; reflexivity.
Qed.


Lemma father_s1e_s2e : 
   forall s1 s2 e,
    wf_occurences (s1 • e) ->
    forall R,
      compatible_by R s1 s2 ->
      forall t t',
        father (s1 • e) t t' -> 
        father (s2 • e) t t'.
Proof.
  intros s1 s2 e h_wf_occ R h_comp t t' h_father.
  inversion h_father as [ i [h_tid h_act]].
  assert (exists i', pi i' (s2 • e) = pi i (s1 • e)) as [i' Ha].
  {
    destruct (Peano_dec.eq_nat_dec i (length s1)); [subst|].
    - (exists (length s2); autorewrite with nth_error; reflexivity).
    - case_eq (pi i (s1 • e)); [
        intros [t0 a0] h_eq; rewrite h_eq in *; 
        injection h_tid; injection h_act; intros; subst
      | intros Ha; rewrite Ha in h_tid; discriminate
      ].
      assert (i < length s1).
      {
        assert (i < length (s1 • e)) as Hb by eauto with nth_error.
        autorewrite with length in Hb; simpl in Hb; intuition.
      }
      assert (exists i', R i i' /\ pi i s1 = pi i' s2) 
        as [i' [Ha Hb]] by compatibility2.
      assert (pi i' s2 == (t', Fork t)) as Hc.
      {
        assert (pi i s1 == (t', Fork t)) by
            (unfold Event.t in*; rewrite <- h_eq;
             symmetry; eauto with nth_error).
        congruence.
      }
      exists i'; unfold Event.t in *; rewrite <- Hc;
      eauto with nth_error.
  }
  constructor 1 with i'; rewrite Ha; tauto.
Qed.

Lemma owns_s1e_s2e : 
   forall s1 s2 e,
    wf_occurences (s1 • e) ->
    forall R,
      compatible_by R s1 s2 ->
      forall p t,
        owns (s1 • e) p t ->
        owns (s2 • e) p t.
Proof.
  intros s1 s2 e h_wf_occ R h_comp p t h_owns.
  inversion h_owns as [? i ? h_tid h_act]; subst.
  assert (exists i', pi i' (s2 • e) = pi i (s1 • e)) as [i' Ha].
  {
    destruct (Peano_dec.eq_nat_dec i (length s1)); [subst|].
    - (exists (length s2); autorewrite with nth_error; reflexivity).
    - case_eq (pi i (s1 • e)); [
        intros [t0 a0] h_eq; rewrite h_eq in *; 
        injection h_tid; injection h_act; intros; subst
      | intros Ha; rewrite Ha in h_tid; discriminate
      ].
      assert (i < length s1).
      {
        assert (i < length (s1 • e)) as Hb by eauto with nth_error.
        autorewrite with length in Hb; simpl in Hb; intuition.
      }
      assert (exists i', R i i' /\ pi i s1 = pi i' s2) 
        as [i' [Ha Hb]] by compatibility2.
      assert (pi i' s2 == (t, Open p)) as Hc.
      {
        assert (pi i s1 == (t, Open p)) by
            (unfold Event.t in*; rewrite <- h_eq;
             symmetry; eauto with nth_error).
        congruence.
      }
      exists i'; unfold Event.t in *; rewrite <- Hc;
      eauto with nth_error.
  }
  constructor 1 with i'; rewrite Ha; tauto.
Qed.

Lemma range_s1e_s2e : 
  forall s1 s2 e,
    wf_occurences (s1 • e) ->
    wf_open_close (s1 • e) ->
    forall R,
      compatible_by R s1 s2 ->
      forall p i k j,
        range (s1 • e) p i j -> 
        i < k <= j ->
        threadId_of (pi i (s1 • e)) = threadId_of (pi k (s1 • e)) ->
        exists i' k' j',
          pi i (s1 • e) = pi i' (s2 • e) /\
          pi k (s1 • e) = pi k' (s2 • e) /\
        (*  (R j j' \/ (j' = length s1 /\ j' = length s2)) /\*)
          range (s2 • e) p i' j' /\
          i' < k' <= j'.
Proof.
  intros s1 s2 e h_wf_occ h_wf_oc R h_comp p i k j h_range h_int h_eq.
  assert (i < length s1) as Ha. 
  {
    assert (j < S(length s1)).
    {
      replace (S (length s1)) with (length (s1 • e)).
      inversion h_range; subst.
      eauto with nth_error.
      autorewrite with length; simpl; intuition.
      autorewrite with length; simpl; intuition.
    }
    intuition.
  }
  assert (action_of (pi i s1) == Open p) as Hu. 
  {
    replace (pi i s1) with (pi i (s1 • e)).
    inversion h_range; assumption.
    eauto with nth_error.
  }
  assert (exists i', R i i' /\ pi i s1 = pi i' s2) as [i' [Hb Hc]]. 
  {
    compatibility2.
  }
  assert (pi i' (s2 • e) = pi i (s1 • e)) as Hv. 
  {
    replace (pi i' (s2 • e)) with (pi i' s2).
    replace (pi i (s1 • e)) with ( pi i s1).
    symmetry; assumption.
    symmetry.
    eauto with nth_error.
    assert (i' < length s2).
    inversion h_comp.
    inversion H.
    eapply H1; eauto.
    symmetry; eauto with nth_error.
  }
  destruct (Peano_dec.eq_nat_dec k (length s1)); [subst|].
  - assert (j = length s1).
    {
      inversion h_range; subst.
      assert (j < S (length s1)).
      case_eq (pi j (s1 • e)); [intros [t0 a0] h_eq2; 
                                 rewrite h_eq2 in Hj; 
                                 injection Hj; intros; subst 
                               | intros h_eq2; rewrite h_eq2 in Hj; 
                                 discriminate ].
      replace (S (length s1)) with (length (s1 • e)).
      eauto with nth_error.
      autorewrite with length; simpl; intuition.
      intuition.
      autorewrite with length; simpl; intuition.
    }
    subst.
    (exists i', (length s2), (length s2)).
    split.
    symmetry; assumption.
    split.
    autorewrite with nth_error; reflexivity.
    split.
    inversion h_range; subst.
    + autorewrite with nth_error in Hj.      
      constructor 1.
      rewrite Hv.
      replace (pi i (s1 • e)) with (pi i s1).
      assumption.
      symmetry.
      eauto with nth_error.
      autorewrite with length; simpl.
      replace (length s2 + 1 - 1) with (length s2) by intuition.
      autorewrite with nth_error.
      assumption.
    + replace (length s2) with (length (s2 • e) - 1).
      constructor 2.
      rewrite Hv.
      replace (pi i (s1 • e)) with (pi i s1). 
      assumption.
      symmetry.
      eauto with nth_error.
      contradict HNotClosed.
      apply occursIn_s1e_s2e with s2.
      symmetry.
      exists R; eauto.
      assumption.
      autorewrite with length; simpl; intuition.
    + split.
      inversion h_comp.
      inversion H; subst.
      destruct H1 with i i'.
      assumption.
      assumption.
      intuition.
  - assert (k < length s1) as Hd. 
    {
      assert (j < S (length s1)).
      {
        replace (S (length s1)) with (length (s1 • e)).
        inversion h_range; subst.
        eauto with nth_error.
        autorewrite with length; simpl; intuition.
        autorewrite with length; simpl; intuition.
      }
      intuition.
    }
    assert (exists k', R k k' /\ pi k s1 = pi k' s2) 
      as [k' [He Hf]] by compatibility2.
    destruct (Peano_dec.eq_nat_dec j (length s1)); [subst|].
    + (exists i', k', (length s2)).
      split.
      symmetry; assumption.
      split.
      replace (pi k (s1 • e)) with (pi k s1).
      replace (pi k' (s2 • e)) with (pi k' s2).
      assumption.
      assert (k' < length s2).
      {
        inversion h_comp.
        inversion H.
        eapply H1; eauto.
      }
      symmetry; eauto with nth_error.
      symmetry; eauto with nth_error.
      split.
      inversion h_range; subst.
      * constructor 1.
        rewrite Hv.
        replace (pi i (s1 • e)) with (pi i s1).
        assumption.
        symmetry; eauto with nth_error.
        autorewrite with nth_error in Hj.
        autorewrite with nth_error.
        assumption.
      * replace (length s2) with (length (s2 • e) - 1).
        constructor 2.
        rewrite Hv.
        replace (pi i (s1 • e)) with (pi i s1).
        assumption.
        symmetry; eauto with nth_error.
        contradict HNotClosed.
        apply occursIn_s1e_s2e with s2.
        symmetry; exists R; eauto.
        assumption.
        autorewrite with length; simpl; intuition.
      * split.
        assert (synchronizeWith s1 i k).
        {
          case_eq (pi i (s1 • e)); [intros [t0 a0] h_eq2| intros h_eq2].
          - constructor 1.
            constructor 1 with t0.
            apply h_int.
            replace(pi i (s1 • e)) with (pi i s1) in h_eq2.
            unfold Event.t in *; rewrite h_eq2; reflexivity.
            symmetry; eauto with nth_error.
            replace (pi k (s1 • e)) with (pi k s1) in h_eq.
            unfold Event.t in *; rewrite <- h_eq.
            rewrite h_eq2; reflexivity.
            symmetry; eauto with nth_error.
          - inversion h_range; subst;
            rewrite h_eq2 in Hi; discriminate.
        }
        assert (synchronizeWith s2 i' k').
        {
          inversion h_comp.
          destruct H1.
          eapply H2; eauto.
        }
        now apply synchronizeWithOrder with s2.
        assert (k' < length s2).
        {
          inversion h_comp.
          inversion H.
          eapply H1; eauto.
        }
        intuition.
    + assert (j < length s1). 
      {
        assert (j < S (length s1)).
        replace (S (length s1)) with (length (s1 • e)).
        inversion h_range; subst.
        eauto with nth_error.
        autorewrite with length; simpl; intuition.
        autorewrite with length; simpl; intuition.
        intuition.
      }
      assert (range s1 p i j). 
      {
        now apply range_se_s_lt with e.
      }
      assert (wf_occurences s1) by now apply wf_occurences_se_s with e.
      assert (wf_open_close s1) by now apply wf_open_close_se_s with e.
      edestruct  compatible_range_owner.
      apply H1.
      assumption.
      eauto.
      apply H0.
      apply h_int.
      replace (pi i (s1 • e)) with (pi i s1) in h_eq.
      replace (pi k (s1 • e)) with (pi k s1) in h_eq.
      assumption.
      symmetry; eauto with nth_error.
      symmetry; eauto with nth_error.
      destruct H3 as [k0 [j0 [h_range0 [h_int0 [h_pi0 [h_pi1 h2]]]]]].
      eapply range_s_se in h_range0 .
     
      destruct h_range0.
      destruct h2.
      exists x, k0,j0.
      split.
      replace (pi i (s1 • e)) with (pi i s1).
      replace (pi x (s2 • e)) with (pi x s2).
      symmetry; assumption.
      assert (x < length s2).
      {
        assert (j0 < length s2) by eauto with nth_error.
        lia.
      }
      symmetry; eauto with nth_error.
      assert (i < length s1) by intuition.
      symmetry; eauto with nth_error.
      split.
      replace (pi k (s1 • e)) with (pi k s1).
      replace (pi k0 (s2 • e)) with (pi k0 s2).
      symmetry; assumption.
      assert (k0 < length s2).
      {
        assert (j0 < length s2) by eauto with nth_error.
        lia.
      }
      symmetry; eauto with nth_error.
      assert (k < length s1) by exact Hd.
      symmetry; eauto with nth_error.
      split.
      apply H3.
      intuition.
      exists x, k0,(length s2 - 1).
      split.
      replace (pi i (s1 • e)) with (pi i s1).
      replace (pi x (s2 • e)) with (pi x s2).
      symmetry; assumption.
      assert (x < length s2).
      { destruct a.
        subst.
        lia.
      }
      symmetry; eauto with nth_error.
      assert (i < length s1) by intuition.
      symmetry; eauto with nth_error.
      split.
      replace (pi k (s1 • e)) with (pi k s1).
      replace (pi k0 (s2 • e)) with (pi k0 s2).
      symmetry; assumption.
      assert (k0 < length s2).
      {
        destruct a; subst; lia.
      }
      symmetry; eauto with nth_error.
      assert (k < length s1) by assumption.
      symmetry; eauto with nth_error.
      split.
      destruct a.
      rewrite <- H4.
      apply H3.
      lia.
      exists x, k0,(length s2).
      split.
      replace (pi i (s1 • e)) with (pi i s1).
      replace (pi x (s2 • e)) with (pi x s2).
      symmetry; assumption.
      assert (x < length s2).
      {
        destruct h2.
        assert (j0 < length s2) by eauto with nth_error.
        lia.
        destruct H4; subst.
        intuition.
      }
      symmetry; eauto with nth_error.
      assert (i < length s1) by intuition.
      symmetry; eauto with nth_error.
      split.
      replace (pi k (s1 • e)) with (pi k s1).
      replace (pi k0 (s2 • e)) with (pi k0 s2).
      symmetry; assumption.
      assert (k0 < length s2).
      {
        destruct h2.
        assert (j0 < length s2) by eauto with nth_error.
        lia.
        destruct H4; subst.
        intuition.
      }
      symmetry; eauto with nth_error.
      assert (k < length s1).
      {
        inversion h_comp.
        inversion H4.
        eapply H6; eauto.
      }
      symmetry; eauto with nth_error.
      split.
      assumption.
      split. 
      intuition.
      destruct h2.
      assert (j0 < length s2) by eauto with nth_error.
      auto with *.
      destruct H4; subst.
      auto with *.
Qed.

Lemma tribeChildren_s1e_s2e :
  forall s1 s2,
    s1 ~= s2 ->
    forall e,
      wf_occurences (s1 • e) ->
      wf_open_close (s1 • e) ->
      forall p t, 
        tribeChildren (s1 • e) p t -> tribeChildren (s2 • e) p t.
Proof.
  intros s1 s2 h_eq e h_wf_occ h_wf_fork p t h_tc.
  inversion h_eq as [R HR].
  induction h_tc 
    as [ ?  ?  ?  ?  ? k t' h_int  h_tid h_act 
       | ].
  - edestruct range_s1e_s2e as [i' [k' [j' [Ha [Hb [Hc [Hd He]]]]]]].
    eauto.
    eauto.
    inversion h_eq.
    apply HR.
    apply H.
    apply h_int.
    rewrite h_tid.
    assert (action_of (pi i (s1 • e)) == Open p) by now inversion H.
    inversion H0; subst.
    assert (i = i0) by wellFormed_occurences (Open p); subst.
    assumption.
    constructor 1 with i' j' t0 k'.
    assumption.
    now apply owns_s1e_s2e with s1 R.
    intuition.
    rewrite <- Hb.
    assumption.
    rewrite <- Hb.
    assumption.
  - constructor 2 with t0.
    assumption.
    now apply father_s1e_s2e with s1 R.
Qed.



  Lemma sec_order_s1e_s2e :  
    forall s1 s2 e,
      wf_occurences (s1 • e) ->
      wf_fork (s1 • e) ->
      wf_open_close (s1•e) ->
      wf_mutualExclusion (s1 • e) ->
      compatible s1 s2 ->
      forall p p',
        sec_order (s1 • e) p p' -> sec_order (s2 • e) p p'.
  Proof.
    intros s1 s2 e wf_occ h_wf_fork wf_oc wf_me h_comp p p' h_sec_order.
    destruct h_comp as [R HR].
    destruct e as [t a].      
    assert (wf_occurences s1) as h_wf_occ_s1 by now apply wf_occurences_se_s with (t,a).
    assert (wf_open_close s1) as h_wf_oc_s1 by now apply wf_open_close_se_s with (t,a).
    assert (wf_fork s1) as h_wf_fork_s1 by now apply wf_fork_se_s with (t,a).
    assert (wf_mutualExclusion s1) as h_wf_me_s1 by now apply wf_mutualExclusion_se_s with (t,a).
    inversion h_sec_order; subst.
    - destruct (eq_action_dec a (Open p')) as [h_eq | h_neq] ; [subst|].
      + assert (k = length s1).
        {
          assert (action_of (pi (length s1) (s1 •(t, Open p'))) == Open p') by
              (autorewrite with nth_error; reflexivity).
          wf_intuition.
        }
        subst.
        assert (length (s2 • (t, Open p')) - 1 = length s2) 
          as h_eq by
              (autorewrite with length; simpl; lia).
        assert (~ occursIn (s2 • (t, Open p')) (Close p)) as h_neq_close_p.
        {
          assert (j = length s1).
          {
            inversion H; subst.
            - assert (j < length (s1 • (t, Open p'))) by eauto with nth_error.
              autorewrite with length in H3; simpl in H3.
              intuition.
            - autorewrite with length; simpl; intuition.
          }
          inversion H; subst.
          autorewrite with nth_error in Hj; discriminate.
          contradict HNotClosed.
          apply occursIn_s_se.
          apply compatible_occursIn with s2.
          symmetry; exists R; eauto.
          now apply occursIn_se_s_neq with t (Open p').
        }
        destruct (Peano_dec.eq_nat_dec i (length s1)) as [ | h_ni]; [subst|].
        * 
          assert (p = p') by
              (inversion H as [ ? Ha | ? Ha] ;subst; 
               autorewrite with nth_error in Ha; simpl in Ha; congruence); subst.       
          apply sec_order_cons_dir with (length s2) (length (s2 • (t,Open p')) - 1) (length s2);
            [constructor 2 | | | ]; autorewrite with nth_error; intuition.
        * assert (i < length s1) as h_lti by intuition.
          assert (exists i', R i i' /\ pi i s1 = pi i' s2) as [i' [Ha Hb]] by compatibility2.
          assert (i' < length s2) by (destruct HR as [ [h_r ] ]; apply (h_r _ _ Ha)).
          assert (pi i (s1 • (t, Open p')) = pi i' (s2 • (t,Open p'))) as h_eq_i_i'. 
          {
            replace (pi i (s1 • (t, Open p'))) with (pi i s1) by (symmetry; eauto with nth_error).
            now replace (pi i' (s2 • (t, Open p'))) with (pi i' s2) by (symmetry; eauto with nth_error).
          }
          apply sec_order_cons_dir with i' (length (s2 • (t,Open p')) - 1) (length s2);
            [ constructor 2; [rewrite <- h_eq_i_i'; inversion H; assumption | assumption] | | |];
            autorewrite with length nth_error in *; simpl in *; unfold Event.t in *;
            first [congruence | intuition].
      + assert (k < length s1). 
        {
          assert (k < length (s1 • (t,a))) by eauto with nth_error.
          autorewrite with length in H3; simpl in H3.
          assert (k <> length s1).
          {
            intro; subst.
            autorewrite with nth_error in H1; simpl in H1.
            congruence.
          }
          intuition.
        }
        assert (i < length s1) by intuition. 
        assert (pi k (s1 • (t,a)) = pi k s1) by eauto with nth_error.
        assert (pi i (s1 • (t,a)) = pi i s1) by eauto with nth_error. 
        destruct (eq_action_dec a (Open p)); [subst|].
        *  assert (exists i', R i i' /\ pi i s1 = pi i' s2) as [i' [Ha Hb]] by compatibility2.
           assert (exists k', R k k' /\ pi k s1 = pi k' s2) as [k' [Hu Hv]] by compatibility2.
           assert (i = length s1); subst.
           {
             assert (action_of (pi (length s1) (s1 • (t, Open p))) == Open p) 
               by now autorewrite with nth_error.
             assert (action_of (pi i (s1 • (t,Open p))) == Open p) by now inversion H.
             wf_intuition.
           }
           exfalso; intuition.
        * assert (sec_order s1 p p') by eauto using sec_order_se_s_neq.
          assert (sec_order s2 p p') by (eapply compatible_seq_order; first [exists R; eauto | eauto]).
          now apply sec_order_s_se.
    - destruct (eq_action_dec a (Open p')); [subst|].
      + assert (i' = length s1). 
        {
          assert (action_of (pi (length s1) (s1 • (t, Open p'))) == Open p') by
              now autorewrite with nth_error.
          wf_intuition.
        }
        subst.
        assert (t0 = t). 
        {
          autorewrite with nth_error in H1; simpl in H1; congruence.
        }
        subst.
        destruct (P.eq_dec p p').
        * subst.
          apply sec_order_cons_ind with (length s2) (length s2) t; 
            try (autorewrite with nth_error; reflexivity).
          apply tribeChildren_s1e_s2e with s1; first [assumption | exists R; eauto].
        * assert (i < length s1). 
          {
            assert (i < length (s1 • (t,Open p'))) by eauto with nth_error.
            autorewrite with length in H3; simpl in H3.
            assert (i <> length s1) by
                (intro; subst; autorewrite with nth_error in H; simpl in H; congruence).
            intuition.
          }
          assert (pi i (s1 • (t, Open p')) = pi i s1) by eauto with nth_error.
          assert (exists j, R i j /\ pi i s1 = pi j s2) as [j [Ha Hb]] by compatibility2.
          assert (j < length s2) by
              (destruct HR as [ [h_r ]]; eapply h_r; eauto).
          assert (pi j (s2 • (t, Open p')) = pi j s2) by eauto with nth_error.
          apply sec_order_cons_ind with j (length s2) t;
            [unfold Event.t in *; congruence |
             autorewrite with nth_error; reflexivity |
             autorewrite with nth_error; reflexivity | ] .
          apply tribeChildren_s1e_s2e with s1; first [assumption | exists R; eauto].
      + destruct (eq_action_dec a (Open p)); [subst|].
        * 

        edestruct (tribeChildren_after_open (s1 • (t, Open p))) as [i0 [Hx Hy]].
        eauto.
        apply H2.
        apply H1.
        assert (i0 = length s1).
        {
          assert (action_of (pi (length s1) (s1 • (t, Open p))) == Open p) 
             by now autorewrite with nth_error.
          wf_intuition.
        }
        subst.
        assert (i' < length s1).
        {
          assert (i' < length (s1 • (t, Open p))) by eauto with nth_error.
          assert (i' <> length s1). 
          {
            intro; subst; exfalso.
            rewrite pi_length_cons in H0; simpl in H0.
            injection H0; intro; subst.
            intuition.
          }
          autorewrite with length in H3; simpl in H3.
          lia.
        }
        exfalso. lia.
      * assert (sec_order s1 p p') by eauto using sec_order_se_s_neq.
        assert (sec_order s2 p p') by (eapply compatible_seq_order; first [exists R; eauto | eauto]).
        now apply sec_order_s_se.
    Qed.

Lemma occurences_s1e_s2e : 
  forall s1 s2 R,
    compatible_by R s1  s2 ->
    forall e i,
      i < length (s1 • e) -> exists i', (R i i' \/ i' = length s2) /\ pi i' (s2 • e) = pi i (s1 • e).
Proof.
  intros s1 s2 R h_comp e i h_lt.
  destruct (Compare_dec.lt_dec i (length s1)).
  - destruct h_comp.
    destruct H.
    edestruct a.
    apply l.
    exists x.
    split.
    left.
    assumption.
    destruct H0.
    symmetry.
    assert (x < length s2).
    {
      apply (r _ _ H).
    }
    assert (pi i (s1 • e) = pi i s1) by eauto with nth_error.
    assert (pi x (s2 • e) = pi x s2)  by eauto with nth_error.
    rewrite H3.
    rewrite H4.
    now apply H0.
  - assert (i = length s1).
    {
      autorewrite with length in h_lt; simpl in h_lt.
      intuition.
    }
    subst.
    exists (length s2).
    split.
    right.
    reflexivity.
    autorewrite with nth_error; reflexivity.
Qed.

Lemma wf_occurences_s1e_s2e : 
  forall s1 s2,
    s1 ~= s2 ->
    forall e,
      wf_occurences (s1 • e) -> wf_occurences (s2 • e).
Proof.
  intros s1 s2 equiv e h_wf_occ.
  unfold wf_occurences, occursAtMostOnce in *.
  intros a h_single i j h_acti h_actj.
  assert (i < length (s2 • e)) by eauto with nth_error.
  assert (j < length (s2 • e)) by eauto with nth_error.
  assert (s2 ~= s1) as Hu by (symmetry; assumption).
  destruct Hu as [R HR].
  destruct occurences_s1e_s2e with s2 s1 R e i as [i'[Ha Hb]]; try assumption.
  destruct occurences_s1e_s2e with s2 s1 R e j as [j'[Hx Hy]]; try assumption.
  destruct Ha. 
  - destruct Hx.
    + assert (i' = j').
      {
        apply h_wf_occ with a; auto.
        congruence.
        congruence.
      }
      subst.
      destruct HR.
      destruct H3.
      unfold injective in i0.
      now apply (i0 j' i j).
    + assert (i' = j').
      {
        apply h_wf_occ with a.
        auto.
        congruence.
        congruence.
      }
      subst.
      destruct HR.
      destruct H2.
      unfold restricted in r.
      destruct (r _ _ H1).
      exfalso; intuition.
  - destruct Hx.
    + assert (i' = j').
      {
        apply h_wf_occ with a.
        auto.
        congruence.
        congruence.
      }
      subst.

      destruct HR.
      destruct H1.
      unfold restricted in r.
      destruct (r _ _ H2).
      exfalso; auto with *.
    + assert (i = length s2).
      {
        destruct (Compare_dec.lt_dec i (length s2)).
        - assert (exists i0, R i i0 /\ pi i0 s1 = pi i s2) as [i0 [Hu Hv]].
          {
            destruct HR.
            destruct H3.
            edestruct a0.
            apply l.
            exists x.
            split.
            assumption.
            destruct H4.
            symmetry; apply H4.
            assumption.
          }
          assert (i0 = i').
          {
            apply h_wf_occ with a.
            auto.
            assert (pi i (s2 • e) = pi i s2) by eauto with nth_error.
            assert (action_of (pi i0 s1) == a) by congruence.
            eauto with nth_error.
            congruence.
          }
          subst.
          destruct HR.
          destruct H1.
          destruct (r _ _ Hu).
          exfalso; intuition.
        -assert (i < length (s2 •e)) by eauto with nth_error.
         autorewrite with length in H3; simpl in H3.
         intuition.
      }
      assert (j = length s2).
      {
        destruct (Compare_dec.lt_dec j (length s2)).
        - assert (exists j0, R j j0 /\ pi j0 s1 = pi j s2) as [j0 [Hu Hv]]. 
          {
            destruct HR.
            destruct H4.
            edestruct a0.
            apply l.
            exists x.
            split.
            assumption.
            destruct H5.
            symmetry; apply H5.
            assumption.
          }
          assert (j0 = j').
          {
            apply h_wf_occ with a.
            auto.
            assert (pi j (s2 • e) = pi j s2) by eauto with nth_error.
            assert (action_of (pi j0 s1) == a) by congruence.
            eauto with nth_error.
            congruence.
          }
          subst.
          destruct HR.
          destruct H1.
          destruct (r _ _ Hu).
          exfalso; intuition.
        - assert (j < length (s2 •e)) by eauto with nth_error.
          autorewrite with length in H4;simpl in H4.
          intuition.
      }
      congruence.
      Qed.


Lemma wf_fork_s1e_s2e : 
  forall s1 s2,
    s1 ~= s2 ->
    forall e,
      wf_fork (s1 • e) -> wf_fork (s2 • e).
Proof.
  intros s1 s2 equiv e h_wf_fork.
  unfold wf_fork in *.
  intros i t h_fork j h_tid.
  assert (i < length (s2 • e)) by eauto with nth_error.
  assert (j < length (s2 • e)) by eauto with nth_error.
  assert (s2 ~= s1) as Hu by (symmetry; assumption).
  destruct Hu as [R HR].
  destruct occurences_s1e_s2e with s2 s1 R e i as [i'[Ha Hb]]; try assumption.
  destruct occurences_s1e_s2e with s2 s1 R e j as [j'[Hx Hy]]; try assumption.
  destruct Ha.
  - assert (i < length s2). 
    {
      destruct HR.
      destruct H2.
      apply (r _ _ H1).
    }
    assert (i' < length s1). 
    {
      destruct HR.
      destruct H3.
      apply (r _ _ H1).
    }
    assert (pi i (s2 • e) = pi i s2) by eauto with nth_error.
    assert (pi i' (s1 • e) = pi i' s1) by eauto with nth_error. 
    destruct Hx.
    + assert (j < length s2). 
      {
        destruct HR.
        destruct H7.
        apply (r _ _ H6).
      }
      assert (pi j (s2 • e) = pi j s2) by eauto with nth_error.
      assert (wf_fork s2) as h_wf_fork_s2.
      {
        assert (wf_fork s1) by now apply wf_fork_se_s with e.
        now apply compatible_wf_fork with s1.
      }
      apply h_wf_fork_s2 with t; congruence.
    + destruct (Compare_dec.lt_dec j (length s2)).
      * assert (pi j (s2 • e) = pi j s2) by eauto with nth_error.
        assert (exists j0, R j j0 /\ pi j0 s1 = pi j s2) as [j0 [Hu Hv]]. 
        {
          destruct HR.
          destruct H8.
          edestruct a.
          apply l.
          exists x.
          split.
          assumption.
          symmetry.
          destruct H9.
          apply H9.
          assumption.
        }
        assert (j0 < length s1). 
        {
          destruct HR.
          destruct H8.
          apply (r _ _ Hu).
        }
        assert (pi j0 (s1 • e) = pi j0 s1) by eauto with nth_error.
        assert (synchronizeWith s2 i j).
        {
          assert (synchronizeWith s1 i' j0).
          {
            constructor 1.
            constructor 2 with t.
            apply h_wf_fork with t.
            congruence.
            congruence.
          unfold Event.t in *; congruence.
          unfold Event.t in *; congruence.
          }
          destruct HR.
          destruct H12.
          eapply H13; eauto.
        }
        apply synchronizeWithOrder with s2.
        assumption.
      * assert (j < length (s2 • e)) by eauto with nth_error.
        autorewrite with length in H7; simpl in H7.
        assert (j = length s2) by intuition.
        intuition.
  - destruct Hx.
    + assert (j < length s2). 
      {
        destruct HR.
        destruct H3.
        apply (r _ _ H2).
      }
      assert (j' < length s1). 
      {
        destruct HR.
        destruct H4.
        apply (r _ _ H2).
      }
      assert (pi j (s2 • e) = pi j s2) by eauto with nth_error.
      assert (pi j' (s1 • e) = pi j' s1) by eauto with nth_error.
      destruct (Compare_dec.lt_dec i (length s2)).
      * assert (pi i (s2 • e) = pi i s2) by eauto with nth_error.
        assert (exists i0, R i i0 /\ pi i0 s1 = pi i s2) as [i0 [Hu Hv]]. 
        {
          destruct HR.
          destruct H8.
          edestruct a.
          apply l.
          exists x.
          split. 
          assumption.
          symmetry.
          destruct H9.
          apply H9.
          assumption.
        }
        assert (i0 < length s1). 
        {
          destruct HR.
          destruct H8.
          apply (r _ _ Hu).
        }
        assert (pi i0 (s1 • e) = pi i0 s1) by eauto with nth_error.
        assert (synchronizeWith s2 i j).
        {
          assert (synchronizeWith s1 i0 j').
          {
            constructor 1.
            constructor 2 with t.
            apply h_wf_fork with t.
            congruence.
            congruence.
            unfold Event.t in *; congruence.
            unfold Event.t in *; congruence.
          }
          destruct HR.
          destruct H12.
          eapply H13; eauto.
        }
        apply synchronizeWithOrder with s2.
        assumption.
      * assert (i < length (s2 • e)) by eauto with nth_error.
        autorewrite with length in H7; simpl in H7.
        assert (i = length s2) by intuition.
        assert (length s1 < j').
        {
          rewrite H8 in h_fork.
          autorewrite with nth_error in h_fork.
          destruct e as [t0 a]; injection h_fork; intros; subst.
          apply h_wf_fork with t.          
          autorewrite with nth_error.
          reflexivity.
          congruence.
        }
        exfalso; intuition.
    + assert (length s1 < length s1).
      {
        subst.
        apply h_wf_fork with t.
        congruence.
        congruence.
      }
      exfalso; intuition.
Qed.

Lemma wf_open_close_s1e_s2e : 
  forall s1 s2,
    s1 ~= s2 ->
    forall e,
      wf_occurences (s1 • e) ->
      wf_open_close (s1 • e) -> wf_open_close (s2 • e).
Proof.
  intros s1 s2 equiv e h_wf_occ h_wf_oc.
  unfold wf_open_close in *.
  intros i p h_close.
  assert (compatible s2 s1) as [R HR] by (symmetry; assumption).
  assert (i < length (s2 • e)) as h_lt_i by eauto with nth_error.
  destruct (occurences_s1e_s2e _ _ _ HR e i h_lt_i) as [i' [Hu Hv]].
  assert (action_of (pi i' (s1 • e)) == Close p) as h_close_i' by congruence.
  destruct (h_wf_oc _ _ h_close_i') as [j' [Ha [Hb Hc]]].
  assert (j' < length s1).
  {
    destruct Hu.
    - assert (i' < length s1).
      {
        destruct HR.
        destruct H0.
        apply (r _ _ H). 
      }
      intuition.
    - congruence.
  }
  assert (exists j, R j j' /\ pi j' s1 = pi j s2) as [j [Hx Hy]].
  {
    destruct HR.
    destruct H0.
    edestruct s; eauto.
    exists x.
    split.
    assumption.
    symmetry.
    destruct H1.
    now apply H1.
  }
  exists j.
  split.
  - destruct Hu.
    + assert (synchronizeWith s1 j' i').
      {
        assert (i' < length s1). 
        {
          destruct HR.
          destruct H1.
          apply (r _ _ H0).
        }
        assert (j' < length s1). 
        {
          destruct HR.
          destruct H2.
          apply (r _ _ Hx).
        }
        replace (pi i' (s1 • e)) with (pi i' s1) 
          in * by (symmetry; eauto with nth_error).
        replace (pi j' (s1 • e)) with (pi j' s1) 
          in * by (symmetry; eauto with nth_error).
        case_eq (pi i' s1); [intros [t a] h_eq  | intros ]; subst.
        rewrite h_eq in *.
        simpl in *.
        constructor 1.
        constructor 1 with t.
        assumption.
        rewrite Hc; reflexivity.
        unfold Event.t in *; rewrite h_eq; reflexivity.
        rewrite H3 in h_close_i'; discriminate.
      }
      assert (synchronizeWith s2 j i).
      {
        destruct HR.
        destruct H3.
        eapply H4; eauto.
      }
      now apply synchronizeWithOrder with s2.
    + assert (i = length s2).
      {
        destruct (Compare_dec.lt_dec i (length s2)).
        - assert (exists i0, R i i0 /\ pi i0 s1 = pi i s2) as [i0 [Hm Hn]].
          {
            destruct HR.
            destruct H1.
            edestruct a; eauto.
            exists x.
            split.
            assumption.
            symmetry.
            destruct H2.
            apply H2.
            assumption.
          }
          assert (action_of (pi i0 (s1 • e)) == Close p).
          {
            destruct HR.
            destruct H2.
            destruct H1.
            assert (i0 < length s1)
            by apply (r _ _ Hm).
            replace (pi i0 (s1 • e)) with (pi i0 s1) by (symmetry; eauto with nth_error).
            replace (pi i (s2 • e)) with (pi i s2) in h_close by (symmetry; eauto with nth_error).
            congruence.
          }
          subst.
          assert (i0 = length s1) by wellFormed_occurences (Close p).
          assert (i0 < length s1).
          {
            destruct HR.
            destruct H2.
            apply (r _ _ Hm).
          }
          exfalso; intuition.
        - assert (i < length (s2 • e)) by eauto with nth_error.
          autorewrite with length in H1; simpl in H1.
          intuition.
      }
      subst.
      destruct HR.
      destruct H0.
      apply (r _ _ Hx).
  - assert (pi j' (s1 • e) = pi j (s2 • e)).
    {
      assert (pi j' (s1 • e) = pi j' s1) by eauto with nth_error.
      rewrite <- H0 in Hy.
      rewrite Hy in Hb.
      assert (pi j (s2 • e) = pi j s2) by eauto with nth_error.
      congruence.
    }
    split; congruence.
 Qed.

Lemma sec_order_s2e_s1e :  
    forall s1 s2 e,
      wf_occurences (s1 • e) ->
      wf_fork (s1 • e) ->
      wf_open_close (s1•e) ->
      wf_mutualExclusion (s1 • e) ->
      compatible s1 s2 ->
      forall p p',
        sec_order (s2 • e) p p' -> sec_order (s1 • e) p p'.
  Proof.
    intros s1 s2 e h_wf_occ h_wf_fork h_wf_oc h_wf_mut h_comp p p' h_sec.
    inversion h_sec; subst; clear h_sec.
    - assert (j < S (length s2)) as h_lt_j.
      {
        inversion H; subst.
        replace (S (length s2)) with (length (s2 • e)).
        eauto with nth_error.
        autorewrite with length; simpl; lia.
        autorewrite with length; simpl; lia.
      }
      destruct (Peano_dec.eq_nat_dec i (length s2)); [subst|].
      + replace j with (length s2) in * by lia.
        replace k with (length s2) in * by intuition.
        autorewrite with nth_error in H1.
        assert (action_of (pi (length s1) (s1 • e)) == Open p).
        {
          inversion H; subst; [exfalso; congruence|].
          replace (length (s2 • e) - 1) with (length s2) in Hi by lia.
          now autorewrite with nth_error in Hi |- *.
        }          
        constructor 1 with (length s1) (length (s1 • e) -1 ) 
                                       (length s1).
        constructor 2; [assumption |].
        inversion H; subst; [
          exfalso; congruence
        | contradict HNotClosed; now apply occursIn_s1e_s2e with s1 ].
        autorewrite with length; simpl; lia.
        now autorewrite with nth_error.
        now autorewrite with nth_error.
      + assert (s2 ~= s1) as [R HR] by (now apply compatible_sym).
        assert (i < length s2) by lia.
        assert (exists i', R i i' /\ pi i s2 = pi i' s1) 
          as [i' [Hu Hv]] by compatibility2.
        assert (i' < length s1).
        {
          inversion HR.
          inversion H4.
          eapply H6; eauto.
        }
        assert (pi i (s2 • e) = (pi i s2)) by eauto with nth_error.
        assert (pi i' (s1 • e) =  (pi i' s1)) by eauto with nth_error.
        assert (action_of (pi i' s1) == Open p)
          by (inversion H; subst; congruence).
        destruct (Peano_dec.eq_nat_dec k (length s2)); [subst|].
        * assert (j = length s2) by lia.
          constructor 1 with i' (length (s1 • e) -1) (length s1).
          inversion H; subst.
          constructor 1; congruence.
          constructor 2.
          congruence.
          contradict HNotClosed.
          now apply occursIn_s1e_s2e with s1.
          autorewrite with length; simpl; lia.
          now autorewrite with nth_error in H1 |- *.
          autorewrite with nth_error in H2 |- *.
          congruence.
        * {
            assert (k < length s2) by lia.
            assert (exists k', R k k' /\ pi k s2 = pi k' s1) 
              as [k' [Hz Hy]].
            {
              compatibility2.
            }
            assert (k' < length s1).
            {
              inversion HR.
              inversion H9.
              eapply H11; eauto.
            }
            assert (pi k (s2 • e) = (pi k s2)) by eauto with nth_error.
            assert (pi k' (s1 • e) =  (pi k' s1)) by eauto with nth_error.
            assert (action_of (pi k' s1) == Open p') by congruence.
            assert (i' <= k').
            {
              destruct (Peano_dec.eq_nat_dec i k); [subst|].
              - assert (i' = k') by
                    (inversion HR as [[ ] _ ]; eauto).
              intuition.
              - assert (synchronizeWith s2 i k).
                  {
                    constructor 1.
                    case_eq (pi k s2); [intros [t0 a0] h_eq | intros h_eq].
                    constructor 1 with t0.
                    intuition.
                    unfold Event.t in *; rewrite <- H5.
                    rewrite H2.
                    rewrite H10.
                    rewrite h_eq.
                    reflexivity.
                    unfold Event.t in *; rewrite h_eq.
                    reflexivity.
                    rewrite Hy in h_eq.
                    rewrite h_eq in H12.
                    discriminate.
                  }
                  assert (synchronizeWith s1 i' k').
                  {
                    inversion HR.
                    eapply H15; eauto.
                  }
                  assert (i' < k').
                  {
                    now apply synchronizeWithOrder with s1.
                  }
                  intuition.
            }
            destruct (Peano_dec.eq_nat_dec j (length s2)); [subst|].
            - constructor 1 with i' (length s1) k'.
              inversion H; subst.
              + constructor 1.
                congruence.
                now autorewrite with nth_error in Hj |- *.
              + replace (length s1) with (length (s1 • e) - 1). 
                constructor 2.
                congruence.
                contradict HNotClosed.
                now apply occursIn_s1e_s2e with s1.
                autorewrite with length; simpl; lia.
              + intuition.
              + congruence.
              + congruence.
            - assert (j < length s2) by lia.
              assert (exists j', R j j' /\ pi j s2 = pi j' s1) 
                as [j' [Hn Hm]] by compatibility2.
              assert (j' < length s1). 
              {
                inversion HR; subst.
                inversion H15.
                eapply H17.
                apply Hn.
              }
              assert (action_of (pi j (s2 • e)) == Close p) as h_close.
              {
                inversion H; subst.
                assumption.
                autorewrite with length in H14; simpl in H14.
                exfalso; lia.
              }
              assert (pi j (s2 • e) = pi j s2) by eauto with nth_error.
              assert (pi j' (s1 • e) = pi j' s1) by eauto with nth_error.
              assert (k' <= j').
              {
                destruct (Peano_dec.eq_nat_dec k j).
                - subst.
                  assert (k' = j').
                  {
                    inversion HR.
                    inversion H18.
                    eapply H21; eauto.
                  }
                  intuition.
                - assert (k < j) by intuition.
                  assert (synchronizeWith s2 k j).
                  {
                    constructor 1.
                    case_eq (pi k s2); [intros [t0 a0] h_eq | intros h_eq].
                    constructor 1 with t0.
                    intuition.
                    unfold Event.t in *; rewrite h_eq; reflexivity.
                    assert (wf_occurences (s2 • e)).
                    now apply wf_occurences_s1e_s2e with s1.
                    assert (wf_open_close (s2 • e)).
                    now apply wf_open_close_s1e_s2e with s1.
                    destruct (H20 _ _ h_close) as [j0 [Ho [Hoo Hooo]]]. 
                    assert (j0 = i).
                    {
                      assert (action_of (pi i (s2 • e)) == Open p).
                      inversion H; subst; assumption.
                      wellFormed_occurences (Open p).
                    }
                    subst.
                    unfold Event.t in *;rewrite <- H16.
                    rewrite Hooo.
                    rewrite H2.
                    rewrite H10.
                    rewrite h_eq; reflexivity.
                    rewrite <- H10 in h_eq.
                    rewrite h_eq in H1.
                    discriminate.
                  }
                  assert (synchronizeWith s1 k' j').
                  {
                    inversion HR.
                    eapply H21; eauto.
                  }
                  assert (k' < j').
                  now apply synchronizeWithOrder with s1.
                  intuition.
              }
              inversion H; subst.
              + constructor 1 with i' j' k'.
                constructor 1.
                congruence.
                congruence.
                intuition.
                congruence.
                congruence.
              + constructor 1 with i' (length s1) k'.
                replace (length s1) with (length (s1 • e) - 1).
                constructor 2.
                congruence.
                contradict HNotClosed.
                now apply occursIn_s1e_s2e with s1.
                autorewrite with length; simpl; lia.
                intuition.
                congruence.
                congruence.
          }
    - assert (exists j j', 
                action_of (pi j (s1 • e)) == Open p /\ 
                pi j' (s1 • e) == (t0, Open p')) 
        as [j [j' [Hu Hv]]].
      {
        assert (i < i').
        {
          edestruct tribeChildren_after_open.
          eapply wf_fork_s1e_s2e.
          apply h_comp.
          apply h_wf_fork.
          apply H2.
          apply H1.
          destruct H3.
          assert (wf_occurences (s2 • e)).
          now apply wf_occurences_s1e_s2e with s1.
          assert (x = i) by wellFormed_occurences (Open p).
          subst.
          assumption.
        }
        assert (i' < S(length s2)).
        {
          replace (S (length s2)) with (length (s2 • e)).
          eauto with nth_error.
          autorewrite with length; simpl; lia.
        }
        assert (i < length s2) by intuition.
        assert (s2 ~= s1) as [R HR].
        now apply compatible_sym.
        assert (exists j, R i j /\ pi i s2 = pi j s1) as [j [Hn Hm]].
        compatibility2.
        assert (j < length s1).
        {
          inversion HR.
          inversion H6.
          eapply H8; eauto.
        }
        destruct (Peano_dec.eq_nat_dec i' (length s2)).
        - exists j, (length s2).
          split.
          replace (pi j (s1 • e)) with (pi j s1).
          rewrite <- Hm.
          replace (pi i s2) with (pi i (s2 • e)).
          assumption.
          eauto with nth_error.
          symmetry; eauto with nth_error.
          subst.
          assert (length s1 = length s2).
          now apply compatible_length.
          rewrite <- H7.
          autorewrite with nth_error in H0, H1 |- *.
          destruct e; simpl in *.
          injection H0; injection H1; intros; subst.
          reflexivity.
        - assert (i' < length s2) by intuition.
          assert (exists j', R i' j' /\ pi i' s2 = pi j' s1) 
            as [j' [Ho Hoo]].
          compatibility2.
          assert (j' < length s1).
          {
            inversion HR.
            inversion H8.
            eapply H10; eauto.
          }
          exists j, j'.
          split.
          replace (pi j (s1 • e)) with (pi j s1).
          rewrite <- Hm.
          replace (pi i s2) with (pi i (s2 • e)).
          assumption.
          eauto with nth_error.
          symmetry; eauto with nth_error.
          replace (pi j' (s1 • e)) with (pi j' s1).
          rewrite <- Hoo.
          replace (pi i' s2) with (pi i' (s2 • e)).
          destruct (pi i' (s2 • e)).
          destruct t1.
          injection H0; injection H1; intros; subst.
          reflexivity.
          discriminate.
          eauto with nth_error.
          symmetry; eauto with nth_error.
      }
      constructor 2 with j j' t0.
      assumption.
      rewrite Hv; reflexivity.          
      rewrite Hv; reflexivity.          
      apply tribeChildren_s1e_s2e with s2.
      now apply compatible_sym.
      now apply wf_occurences_s1e_s2e with s1.
      now apply wf_open_close_s1e_s2e with s1.
      assumption.
  Qed.



Lemma concurrent_s1e_s2e : 
    forall s1 s2 e,
      wf_occurences (s1 • e) ->
      wf_fork (s1 • e) ->
      wf_open_close (s1 • e) ->
      wf_mutualExclusion (s1 • e) ->
      compatible s1 s2 ->
      forall p p', concurrent (s1 • e) p p' -> concurrent (s2 • e) p p'.
  Proof.
    intros s1 s2 e wf_occ wf_fork wf_oc wf_me h_comp p p' h_conc.
    unfold concurrent in *.
    destruct h_conc as [H1 [H3 [H4 H5]]].
    split.
    now apply occursIn_s1e_s2e with s1.
    split.
    now apply occursIn_s1e_s2e with s1.
    split.
    contradict H4.
    apply sec_order_s2e_s1e with s2; try assumption.
    contradict H5.
    apply sec_order_s2e_s1e with s2; try assumption.
Qed.

Lemma concurrent_s2e_s1e : 
    forall s1 s2 e,
      wf_occurences (s1 • e) ->
      wf_fork (s1 • e) ->
      wf_open_close (s1 • e) ->
      wf_mutualExclusion (s1 • e) ->
      compatible s1 s2 ->
      forall p p', concurrent (s2 • e) p p' -> concurrent (s1 • e) p p'.
  Proof.
    intros s1 s2 e wf_occ wf_fork wf_oc wf_me h_comp p p' h_conc.
    unfold concurrent in *.
    destruct h_conc as [H1 [H3 [H4 H5]]].
    split.
    now apply occursIn_s1e_s2e with s2.
    split.
    now apply occursIn_s1e_s2e with s2.
    split.
    contradict H4.
    apply sec_order_s1e_s2e with s1; try assumption.
    contradict H5.
    apply sec_order_s1e_s2e with s1; try assumption.
Qed.



  Lemma sync_e' :
    forall s1 s2 e i j R l1 l2,
      wf_occurences (s1 • e) ->
      wf_fork (s1 • e) ->
      wf_open_close (s1 • e) ->
      wf_mutualExclusion (s1 • e) ->
      compatible_by R s1 s2 ->
      R i j ->
      l1 = length s1 ->
      l2 = length s2 ->
      (synchronizeWith (s1 • e) i l1 ->
      synchronizeWith (s2 • e) j l2).
  Proof.
    intros s1 s2 e i j R l1 l2  h_wf_occ h_wf_fork h_wf_oc h_wf_me h_comp h_r Heq1 Heq2 h_sync1.
    generalize dependent Heq2.
    generalize dependent j.
    induction h_sync1 as [i z |].
    - intros j h_r Heq2. 
      inversion h_comp    as [ [ h1 h_func h_applicative h3 h_surjective] [h_eq h_sync]].
      assert (pi i s1 = pi j s2) as h_pi by now apply h_eq.
      destruct h1 with i j as [hlti hltj];auto.
      assert (pi i (s1 • e) =pi i s1  ) as h_pi_pi_e by eauto with nth_error.
      assert (pi j (s2 • e) =pi j s2  ) as h_pj_pj_e by eauto with nth_error.
      assert (pi i (s1 • e) = pi j (s2 • e)) as h_eq_pi. rewrite h_pi_pi_e; rewrite  h_pj_pj_e;auto.
     inversion H;subst.
      + constructor; constructor 1 with t0;auto.
        rewrite <- h_eq_pi at 1;auto.
        autorewrite with nth_error in *;auto.
      +  constructor . constructor 2 with t0;auto.
         rewrite <- h_eq_pi at 1;auto.
         autorewrite with nth_error in *;auto.
      + constructor . constructor 3 with t0;auto.
         rewrite <- h_eq_pi at 1;auto.
         autorewrite with nth_error in *;auto.
      + constructor. 
        constructor 4 with p p';auto.
        apply concurrent_s1e_s2e with s1; try assumption.
        exists R; assumption.
        rewrite <- h_eq_pi.
        assumption.
        autorewrite with nth_error in *;auto.
    - inversion h_comp    as [ [ h1 h_func h_applicative h3 h_surjective] [h_eq h_sync]].
      assert (y < length s1) as hlt_y. {
        apply synchronizeWithOrder with (s1 • e).
        rewrite Heq1 in h_sync1_2;auto.
      }
      intros j h_r Heq2.
      assert (exists y', R y y') as Hy' by now apply h_applicative.
      destruct Hy' as [y' Hy'].
      constructor 2 with y'.
      apply synchronizeWith_s_se.
      apply wf_occurences_s1e_s2e with s1.
      exists R; eauto.
      assumption.
      apply wf_fork_s1e_s2e with s1.
      exists R; eauto.
      assumption.
      apply wf_open_close_s1e_s2e with s1.
      exists R; eauto.
      assumption.
      assumption.
      assert (synchronizeWith s1 x y) as h_sync_xy by
                                          now apply synchronizeWith_se_s with e.
      destruct (h_sync x j y y') as [h_sync1 h_sync2];auto.
      apply IHh_sync1_2;auto.
  Qed.
  
  Lemma compatible_precedes_concurrent : 
    forall s1 s2,
      s1 ~= s2 ->
      forall p p',
        concurrent s1 p p' -> precedes s1 p p' -> precedes s2 p p'.
  Proof.
    intros s1 s2 equiv p p' h_conc h_pred.
    unfold precedes in *.
    inversion h_pred; subst.
    assert (synchronizeWith s1 i j).
    {
      constructor 1.
      now constructor 4 with p p'.
    }
    assert (j < length s1) by eauto with nth_error.
    assert (i < length s1) by eauto with nth_error.
    destruct equiv as [R HR].
    assert (exists i', R i i' /\ pi i s1 = pi i' s2) as [i' [Hx Hy]].
    {
      destruct HR.
      destruct H2.
      edestruct a.
      eauto.
      exists x.
      split.
      assumption.
      destruct H3; eauto.
    }
    assert (exists j', R j j' /\ pi j s1 = pi j' s2) as [j' [Hu Hv]]. 
    {
      destruct HR.
      destruct H2.
      edestruct a.
      apply H0.
      exists x.
      split.
      assumption.
      destruct H3; eauto.
    }
    assert (i' < j').
    {
      apply synchronizeWithOrder with s2.
      destruct HR.
      destruct H3.
      eapply H4; eauto.
    }
    exists i' j'.
    assumption.
    congruence.
    congruence.
Qed.

  Lemma precedes_s_se : 
    forall s e a a',
      precedes s a a' -> precedes (s • e) a a'. 
  Proof.
    intros s e a a' h_prec.
    unfold precedes  in *.
    inversion h_prec; subst.
    exists i j.
    assumption.
    eauto with nth_error.
    eauto with nth_error.
  Qed.
 
  Lemma precedes_se_s_neq :
    forall s t a p p' ,
      precedes (s • (t, a)) p p' -> a <> Open p' -> precedes s p p'. 
  Proof.
    intros s t a p p' h_prec h_neq.
    unfold precedes in *.
    inversion h_prec; subst.
    assert (j < length s).
    {
      assert (j < length (s • (t,a))) by eauto with nth_error.
      autorewrite with length in H; simpl in H.
      assert (j <> length s).
      {
        intro; subst.
        autorewrite with nth_error in Ha'; injection Ha'; intros; subst.
        exfalso; intuition.
      }
      intuition.
    }
    assert (i < length s) by intuition.
    unfold Event.t in *.
    replace (pi i (s • (t,a))) with (pi i s) in Ha by (symmetry; eauto with nth_error).
    replace (pi j (s • (t,a))) with (pi j s) in Ha' by (symmetry; eauto with nth_error).
    exists i j; assumption.
Qed.

  Lemma concurrent_se_s_neq :
    forall s t a p p',
      concurrent (s • (t, a)) p p' -> a <> Open p -> a <> Open p' -> concurrent s p p'. 
  Proof.
    intros s t a p p' h_conc h_neq_a h_neq_a'.
    unfold concurrent in *.
    destruct h_conc as [H1 [H2 [H3 H4]]].
    split.
    now apply occursIn_se_s_neq with t a.
    split.
    now apply occursIn_se_s_neq with t a.
    split.
    contradict H3.
    now apply sec_order_s_se.
    contradict H4.
    now apply sec_order_s_se.
  Qed.

  Lemma precedes_s1e_s2e : 
    forall s1 s2,
      s1 ~= s2 ->
      forall e p p',
        wf_occurences (s1 • e) -> 
        wf_open_close (s1 • e) ->
        concurrent (s1 • e) p p' -> precedes (s1 • e) p p' -> precedes (s2 • e) p p'.
  Proof.
    intros s1 s2 equiv e p p' h_wf_occ h_wf_oc h_conc h_prec.
    destruct e as [t a].
    destruct (eq_action_dec a (Open p')).
    - subst.
      inversion h_prec ;subst.
      (* destruct h_prec. *)
      assert (i < length s1).
      {
        assert (j < length (s1 • (t, Open p'))) by eauto with nth_error.
        autorewrite with length in H; simpl in H.
        auto with *.
      }
      destruct equiv as [R HR].
      assert (exists i', R i i' /\ pi i' s2 = pi i s1) as [i' [Hu Hv]]. 
      {
        destruct HR.
        destruct H0.
        edestruct a; eauto.
        exists x.
        split.
        assumption.
        destruct H1; symmetry; eauto.
      }
      assert (i' < length s2). 
      {
        destruct HR.
        destruct H0.
        eapply r; eauto.
      }
      exists i' (length s2); unfold Event.t in *.
      assumption.

      replace (pi i' (s2 • (t, Open p'))) with (pi i' s2) by (symmetry; eauto with nth_error).
      rewrite Hv.
      eauto with *.
      rewrite pi_length_cons.
      reflexivity. 
    - assert (precedes s1 p p') by now apply precedes_se_s_neq with t a.
      assert (a <> Open p).
      {
        intro; subst.
        inversion h_prec; subst.
        apply h_wf_oc in Ha.
        destruct Ha as [j0 [H1 [H2 H3]]].
        assert (j0 = length s1).
        {
          assert (action_of (pi (length s1) (s1 • (t,Open p))) == Open p). 
          autorewrite with nth_error; reflexivity.
          wellFormed_occurences (Open p).
        }
        subst.
        assert (j < length (s1 • (t, Open p))) by eauto with nth_error.
        autorewrite with length in H0; simpl in H0.
        auto with *.
      }
      assert (concurrent s1 p p') by now apply concurrent_se_s_neq with t a.
      assert (precedes s2 p p') by now apply compatible_precedes_concurrent with s1.
      now apply precedes_s_se.
    Qed.

  Lemma wf_mutualExclusion_s1e_s2e : 
    forall s1 s2,
      s1 ~= s2 ->
      forall e,
        wf_occurences (s1 • e) ->
        wf_fork (s1 • e) ->
        wf_open_close (s1 • e) ->
        wf_mutualExclusion (s1 • e) ->
        wf_mutualExclusion (s2 • e).
  Proof.
    intros s1 s2 equiv e wf_occ wf_fork wf_oc wf_me.
    unfold wf_mutualExclusion in *.
    intros p p' h_conc.
    assert (concurrent (s1 • e) p p').
    apply concurrent_s2e_s1e with s2; try assumption.
    destruct (wf_me p p' H).
    left.
    now apply precedes_s1e_s2e with s1.
    right.
    apply precedes_s1e_s2e with s1; try auto.
    apply concurrent_sym.
    assumption.
Qed.



  Lemma sync_e :
    forall s1 s2 e i j R,
      wf_occurences (s1 • e) ->
      wf_fork (s1 • e) ->
      wf_open_close (s1 • e) ->
      wf_mutualExclusion (s1 • e) ->
      compatible_by R s1 s2 ->
      R i j ->
      (synchronizeWith (s1 • e) i (length s1) <->
       synchronizeWith (s2 • e) j (length s2)).
  Proof.
    intros s1 s2 e i j R h_wf_occ h_wf_fork h_oc h_wf_me h_comp h_r.
    split.
    - intros h_sync1.
      apply sync_e' with s1 i R (length s1);auto.
    - intros h_sync2.      
      assert( compatible_by (inverse R) s2 s1) as h_comp_2 by now apply symmetric_compatible_R.
      apply sync_e' with s2 j (inverse R) (length s2);auto.
      apply wf_occurences_s1e_s2e with s1.
      exists R; eauto.
      assumption.
      apply wf_fork_s1e_s2e with s1.
      exists R; eauto.
      assumption.
      apply wf_open_close_s1e_s2e with s1.
      exists R; eauto.
      assumption.
      assumption.
      apply wf_mutualExclusion_s1e_s2e with s1.
      exists R; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
  Qed.


 
  Lemma compatible_S : forall (s1 s2 : Tr) e, 
                         wellFormed (s1 • e) ->
                         s1 ~= s2 ->  s1 • e ~= s2 • e.
  Proof.
    intros s1 s2 e h_wf H.
    assert (wf_occurences (s1 • e)) by now inversion h_wf.
    inversion H as [R [h_bijective [h_eq h_sync ]]]; subst.
    exists (fun x y => R x y \/ (x= length s1 /\ y = length s2)).
    split.
    - replace (length (s1 • e)) with (S (length s1)) by (autorewrite with length; simpl; lia).
      replace (length (s2 • e)) with (S (length s2)) by (autorewrite with length; simpl; lia).
      now apply bijective_S.
    - 
      split. 
      + intros i j H2.
        destruct H2.

        destruct h_bijective as [h_rest h_func h_app h_inj h_surj].
        destruct h_rest with i j as [h_lt_i h_lt_j ];auto.

        replace (pi i (s1 • e)) with (pi i s1) by  (rewrite (nth_error_append_left _  (e::nil));auto).  
        replace (pi j (s2 • e)) with (pi j s2)  by  (rewrite (nth_error_append_left _  (e::nil));auto).  
        now apply h_eq.
        destruct H1.
        replace (pi i (s1 • e)) with (Some e) by (subst; autorewrite with nth_error;auto).
        replace (pi j (s2 • e)) with (Some e) by (subst; autorewrite with nth_error;auto).
        reflexivity.
      + intros i j i' j' H2 H3.
        destruct H2; destruct H3; subst.
        {
          assert (synchronizeWith s1 i i' <-> synchronizeWith s2 j j') as h_sync_s by now apply h_sync.
          destruct h_sync_s as [ h_sync_s1  h_sync_s2].
          destruct h_bijective as [h_rest h_func h_app h_inj h_surj].
          destruct h_rest with i' j' as [h_lt_i' h_lt_j' ];auto.
          
          split.
          - intro h_sync_i.
            assert (synchronizeWith s1 i i') as h_sync_s_i . 
            apply synchronizeWith_se_s with e;auto. 
            inversion h_wf; assumption. 
            apply synchronizeWith_s_se.
            inversion h_wf; now apply wf_occurences_s1e_s2e with s1.
            inversion h_wf; now apply wf_fork_s1e_s2e with s1.
            inversion h_wf; now apply wf_open_close_s1e_s2e with s1.

            eauto.
          -intro h_sync_j.
           assert (synchronizeWith s2 j j') as h_sync_s_j . 
           apply synchronizeWith_se_s with e;auto. 
           inversion h_wf.
           apply wf_occurences_s1e_s2e with s1.
           assumption.
           assumption.
           apply wf_open_close_s1e_s2e with s1.
           assumption.
           inversion h_wf; assumption.
           assert (wf_open_close (s1 • e)) by now inversion h_wf.
           assumption.
           assert (synchronizeWith s1 i i') as h_sync_i.
           apply h_sync_s2.
           assumption.
           apply synchronizeWith_s_se.
            inversion h_wf; now apply wf_occurences_s1e_s2e with s1.
            inversion h_wf; now apply wf_fork_s1e_s2e with s1.
            inversion h_wf; now apply wf_open_close_s1e_s2e with s1.
           assumption.
        }
        {
          destruct H2; subst.
          apply sync_e  with R;auto.
          inversion h_wf; assumption.
          inversion h_wf; assumption.
          inversion h_wf; assumption.
          constructor;auto.
        }
        {
          destruct H1; subst.
            split.
          - intro h_sync1.
            assert ((length s1) < i') as h_lt_s1_i'. 
            apply synchronizeWithOrder with (s1 • e);auto.
            assert (i' < length (s1 • e)) as h_lt_i'_s1e.
            apply  synchronizeWithIn  with (length s1);auto.
            contradict h_lt_i'_s1e.
            replace (length (s1 • e)) with (S (length s1)) by (autorewrite with length;simpl;lia;auto).
            lia.
          -intro h_sync2.
           assert ((length s2) < j') as h_lt_s1_j'. 
           apply synchronizeWithOrder with (s2 • e);auto.
           assert (j' < length (s2 • e)) as h_lt_j'_s2e.
           apply  synchronizeWithIn  with (length s2);auto.
           contradict h_lt_j'_s2e.
           replace (length (s2 • e)) with (S (length s2)) by (autorewrite with length;simpl;lia;auto).
           lia.
        }
        {
          destruct H1; destruct H2; subst.
          split.
          - intro h_sync1.
            assert ((length s1) < (length s1)) as h_lt_s1 by now apply synchronizeWithOrder with (s1 • e).
            contradict h_lt_s1;lia.
          - intro h_sync1.
            assert ((length s2) < (length s2)) as h_lt_s1 by now apply synchronizeWithOrder with (s2 • e).
            contradict h_lt_s1;lia.
        }
  Qed.



End Make.
