(** printing Sigma #&Sigma;# *) (** printing pi  #&pi;#*)
(** printing nat #&#8469;#*)
(** printing exists #&exist;# *) (** printing forall #&forall;# *)
(** printing /\ #&and;# *) (** printing \/ #&or;# *)
(** printing -> #&#x02192;# *)
(** printing • #&#8226;# *)

From Stdlib Require Import List Arith.
Require Import sections.lifo.Prelude.
Require Import sections.lifo.ListBasics.
Require Import sections.common.GenericTrace.
Require Import sections.traces.Trace_Basics.
Require Import sections.lifo.Length.
From Stdlib Require Import Lia.
From Stdlib Require Import Logic.Classical_Prop.


(** In this section, we introduce some results about well formed trace.
     First we show that the set of wellformed trace is prefix closed. Then
     we prove that there exists some restrictions on which actions can be performed
     within a section. *)
 
Module Make (SN : MiniDecidableSet)
            (Export Ad: DecidableInfiniteSet) 
            (Export Ty : Type_.TYPE Ad )
            (Export Va : Value.TYPE Ad Ty).

  Include Trace_Basics.Make SN Ad Ty Va.



  Lemma tribe_dec :
    forall s (HWFOcc : wf_occurences s) (HWFFork : wf_fork s) 
           (HWFOpenClose : wf_open_close s) p t, 
      tribe s p t \/ ~ tribe s p t.
  Proof.
    intros.
    apply classic.
  Qed.

  Lemma sec_order_dec : 
    forall s p p',
      wf_occurences s ->
      wf_fork s ->
      wf_open_close s ->
      (sec_order s p p') \/ (~ sec_order s p p').
  Proof.
  intros.
  apply classic.
  Qed.
 
  (** ** Fork / Join of tribe members *)

  Lemma forkInTribe :   
    forall s, 
      wellFormed s ->
      forall p i j,
        range s p i j ->
        forall k t t',
          tribe s p t ->
          i <= k <= j -> 
          threadId_of (pi k s) == t -> 
          action_of (pi k s) == Fork t' ->
          tribe s p t'.
  Proof.
    intros s wellFormed_s p i j range_s_p_i_j k t t' HTribe H1 H2 H3.
    right.
    assert (i < k <= j).
    {
      split.
      - destruct H1 as [Hik _].
        destruct (Nat.eq_dec i k) as [Heq | Hneq].
        + subst.
          assert (action_of (pi k s) == Open p) by
              (inversion range_s_p_i_j; subst; assumption).
          rewrite H3 in H; discriminate.
        + lia.
      - apply H1.
    }
    destruct HTribe;
      [econstructor 1 | econstructor 2]; eauto.
    exists k; auto.
  Qed.
  
  (** All tribe children is forked after the section was opened *)
  
  Lemma tribeChildren_forked_after : 
    forall s,
      wellFormed s ->
      forall p i j,
        range s p i j ->
        forall t,
          tribeChildren s p t ->
          exists k, i < k /\ action_of (pi k s) == Fork t.
  Proof.
    intros s wellFormed_s p i j range_s_p_i_j t tribeChildren_p_t.
    induction tribeChildren_p_t.
    - assert (i = i0).
      { 
        inversion wellFormed_s.
        destruct range_functionnal with (s:=s) (p:=p) (i:=i) (j:=j) (i':=i0) (j':=j0);
          assumption.
      }
      subst.
      exists k; intuition.
    - destruct IHtribeChildren_p_t as [k [lt_i_k Ak]].
      assert (exists k', threadId_of (pi k' s) == t0 /\ action_of (pi k' s) == Fork t') 
        as [k' [Tk' Ak']] by (inversion H; intuition eauto).
      assert (k < k') by
          (inversion wellFormed_s; eauto).
      exists k'; auto with *.
  Qed.
  
  (** A member of a tribe joined within the section was forked in the section *)
  
  Lemma joined_in_tribe_forked_in :
    forall s,
      wellFormed s ->
      forall p i j,
        range s p i j ->
        forall t k,
          tribe s p t -> 
          i <= k <= j ->
          action_of (pi k s) == Join t ->
          exists k3 t3, 
            i < k3 < k 
            /\ threadId_of(pi k3 s) == t3 
            /\ action_of (pi k3 s) == Fork t.
  Proof.
    intros s wellFormed_s p i j range_s_p_i_j t k tribe_p_t int_i_j_k Ak.
    assert (tribeChildren s p t) as Ha.
    {
      inversion tribe_p_t; [|assumption].
      assert (j < k) by (inversion wellFormed_s; eauto).
      exfalso; auto with *.
    }
    assert (exists k, i < k /\ action_of (pi k s) == Fork t) 
      as [k0 [lt_i_k0 Ak0]]
        by eauto using tribeChildren_forked_after.
    assert (k0 < k).
    {
      inversion wellFormed_s; eauto.
    }
    assert (exists t0, threadId_of (pi k0 s) == t0) as [t0 Tk0].
    {
      apply lift_inversion in Ak0.
      destruct Ak0 as [[t0 a0] [Hevent Haction]].
      exists t0. rewrite Hevent. trivial.
    }
    exists k0, t0; intuition.
  Qed.

 
  (** ** Sections opened inside other section *)

  (** A section [p'] opened within a section [p] is dominated by [p] *)

  Lemma wellFormed_prec_tribe :
    forall s,
      wellFormed s ->
      forall p i j,
        range s p i j ->
        forall k p', 
          i <= k <= j ->
          action_of (pi k s) == Open p' ->
          sec_order s p p'.
  Proof.
    intros s h_wf p i j h_range k p' h_int h_open_p'.
    assert (action_of (pi i s) == Open p) by now inversion h_range.
    destruct (Peano_dec.eq_nat_dec k i) as [h_eq | h_neq_k].
    - subst.
      case_eq (pi i s); [intros [t a] h_eq | intros]; subst.
      apply sec_order_cons_dir with i j i.
      assumption.
      assumption.
      assumption.
      reflexivity.
      rewrite H0 in H; discriminate.
    - destruct (sec_order_dec s p p'); inversion h_wf; try assumption.
      assert (wf_mutualExclusion s) as h_wf_me by now inversion h_wf.
      assert (concurrent s p p') as Ha.
      {
        assert (p <> p') by
          (intro; subst; replace i with k in * by wellFormed_occurences (Open p'); intuition).
        assert (~ sec_order s p' p).
        {
          intro.
          assert (k < i ).
          {
            case_eq (pi i s); [intros [t a] h_eq | intro h_none; rewrite h_none in H; discriminate].
            assert (tribe s p' t) as h_tribe.
            {
              inversion H2; subst.
              - constructor 1.
                exists k.
                assert (i = k0) by wellFormed_occurences (Open p); subst.
                assert (i0 = k) by (inversion H3; wellFormed_occurences (Open p')); subst.
                rewrite H6.
                rewrite h_eq; reflexivity.
                assumption.
              - assert (i' = i) by wellFormed_occurences (Open p).
                subst.
                rewrite h_eq in H5; injection H5; intros; subst. 
                constructor 2; assumption.
            }
            inversion h_tribe; subst.
            - assert (tribe s p t).
              {
                assert (owns s p t) 
                  as h_owns by 
                      (exists i; [rewrite h_eq; reflexivity | inversion h_range; assumption]).
                now constructor 1.
              }
              assert (action_of (pi i s) == Open p) as h_open_p by now inversion h_range.
              assert (threadId_of (pi k s) == t) by   
                  (inversion H3; subst; now replace k with i0 by wellFormed_occurences (Open p')).
              assert (sec_order s p p').
              { 
                apply sec_order_cons_dir with i j k.
                assumption.
                assumption.
                assumption.
                rewrite h_eq; simpl.
                congruence.
              }
              intuition.
            - eapply tribeChildren_live_after_open; eauto.
              rewrite h_eq; reflexivity.
          }
          auto with *.
        }
        unfold concurrent; intuition eauto.
        - exists i; assumption.
        - exists k; assumption.
      }
      destruct (h_wf_me _ _ Ha) as [h_precedes_p_p' | h_precedes_p'_p]; subst.
      + assert (j < k).
        {
          inversion h_precedes_p_p' as [j' k' h_lt Hu Hv Hw]; subst.
          assert (k' = k) by wellFormed_occurences (Open p').
          assert (j'= j ).
          {
            inversion h_range; subst.
            - wellFormed_occurences (Close p).
            - exfalso.
              apply HNotClosed.
              exists j'; assumption.
          }
          congruence.
        }
        auto with *.
      + assert (k < i).
        {
          inversion h_precedes_p'_p as [j' i' h_lt Hu Hv Hw]; subst.
          assert (i' = i) by wellFormed_occurences (Open p).
          assert (wf_open_close s) as h_wf_oc by now inversion h_wf.
          destruct (h_wf_oc _ _ Hv) as [k' [Hx [Hy Hz]]].
          assert (k' = k) by wellFormed_occurences (Open p').
          subst; auto with *.
        }
        auto with *.
  Qed.
  
  (** Only tribe members can open sections in sections *)
  
  Lemma open_in_tribe : 
    forall s,
      wellFormed s -> 
      forall p i j,
        range s p i j ->
        forall k t p',
          i <= k <= j ->
          threadId_of (pi k s) == t -> 
          action_of (pi k s) == Open p' -> 
          tribe s p t.
  Proof.
    intros s wellFormed_s p i j range_s_p_i_j k t p' HLt HThreadOf HActionOf.
    inversion wellFormed_s.
    assert (action_of (pi i s) == Open p) as Hi by (inversion range_s_p_i_j; assumption).
    assert (sec_order s p p') as Ha by (eapply  wellFormed_prec_tribe; eauto).
    inversion Ha; subst.
    - assert (k0 = k) by wellFormed_occurences (Open p'); subst.
      assert (i0 = i) by (inversion H; wellFormed_occurences (Open p)); subst.
      constructor 1.
      exists i.
      congruence.
      assumption.
    - replace i' with k in * by wellFormed_occurences (Open p').
      assert (t = t0) by congruence; subst.
      constructor 2; assumption.
  Qed.   


  (** Open action cannot conflit *)

  Lemma wellFormed_open_in :
    forall s t a,
      wellFormed (s • (t,a)) ->
      conflicts s t ->
      forall p', a <> Open p'.
  Proof.
    intros s t a h_wf h_conflict p' h_neq_open; subst.
    destruct h_conflict as [p [ [ [i h_range] h_neq_open]  h_neq_tribe] ].
    assert (i < length s) as Hi_lt.
    {
      inversion h_range as [i0 Hi0 j0 Hj0 | i0 Hi0 HNotClosed]; subst.
      - eapply (lift_nth_error_defined_left (threadId * action) action
                                             i (@snd threadId action) s).
        exists (Open p); exact Hi0.
      - eapply (lift_nth_error_defined_left (threadId * action) action
                                             i (@snd threadId action) s).
        exists (Open p); exact Hi0.
    }
    assert (action_of (pi i (s • (t, Open p'))) == Open p) as Hopen_i_se.
    {
      inversion h_range as [i0 Hi0 j0 Hj0 | i0 Hi0 HNotClosed]; subst;
        unfold lift in Hi0 |- *;
        rewrite nth_error_append_left by exact Hi_lt;
        exact Hi0.
    }
    assert (tribe s p t).
    {
      assert (tribe (s • (t, Open p')) p t).
      { 
          assert (range (s • (t, Open p')) p i (length s)).
          {
            replace (length s) with (length (s • (t, Open p')) - 1)
              by (rewrite length_app; simpl; lia).
          constructor 2.
          exact Hopen_i_se.
          contradict h_neq_open.
          apply occursIn_se_s_neq with t (Open p').
          assumption.
          discriminate.
        }
        apply open_in_tribe with i (length s) (length s) p'.
        - assumption.
        - assumption.
        - lia.
        - unfold lift; rewrite pi_length_cons; reflexivity.
        - unfold lift; rewrite pi_length_cons; reflexivity.
      }
      assert (p <> p') as Hp_ne_p'.
      {
        intro Hp_eq; subst p'.
        assert (i = length s).
        {
          assert (action_of (pi (length s) (s • (t, Open p))) == Open p)
            by apply action_of_last.
          wellFormed_occurences (Open p).
        }
        lia.
      }
      eapply (tribe_se_s_not_open_fork s (t, Open p') p t).
      - inversion h_wf; assumption.
      - inversion h_wf; assumption.
      - inversion h_wf; assumption.
      - exact H.
      - intro Heq.
        inversion Heq; subst.
        congruence.
      - intros t' Heq.
        discriminate.
    }
    now contradict h_neq_tribe.
  Qed.

  

  (** ** Decidability *)

  Lemma exclude_dec : 
    forall (s : Tr)  (HWF : wellFormed s) (t : threadId), 
      (forall p, ~ exclude s p t) \/ (exists p, outerExclude s p t).
  Proof.
    intros s HWF t.
    destruct (outerExcludef s t) as [p|] eqn:Houter.
    - right. exists p. now apply outerExcludefIsOuter.
    - left. now apply outerExcludefNone.
  Qed.

End Make.


Module Type T 
       (SN : MiniDecidableSet)
       (Export Ad: DecidableInfiniteSet) 
       (Export Ty : Type_.TYPE Ad )
       (Export Va : Value.TYPE Ad Ty ).
  Include Make SN Ad Ty Va.
End T.
