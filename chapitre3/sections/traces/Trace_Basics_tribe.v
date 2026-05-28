From Stdlib Require Import List Arith.
Require Import sections.lifo.Prelude.
Require Import sections.common.GenericTrace.
Require Import sections.traces.Trace.
Require Import sections.traces.Trace_Basics_projection.
Require Import sections.traces.Trace_Basics_occurences.
Require Import sections.traces.Trace_Basics_range.
Require Import sections.traces.Trace_Basics_father.
Require Import sections.traces.Trace_Basics_owns.

From Stdlib Require Import Lia. 

Module Make ( Perm : MiniDecidableSet )
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T )
            ( TraceMod : Trace.T Perm Address T V)
            ( P : Proj Perm Address T V TraceMod)
            ( O : OccurencesT Perm Address T V TraceMod P)
            ( F : FatherT Perm Address T V TraceMod P O) 
            ( OW : OwnsT Perm Address T V TraceMod P O)
            ( R : RangeT Perm Address T V TraceMod P O).

  Import TraceMod P O F OW R.
  
   (** ** tribe *)

  Hint Resolve owns_s_se : owns.   
  Hint Resolve owns_se_s : owns.
  Hint Resolve range_s_se : range.
  Hint Resolve father_s_se : father.

  Lemma threadId_of_last :
    forall s t a, threadId_of (pi (length s) (s • (t, a))) == t.
  Proof.
    intros; unfold lift; rewrite pi_length_cons; reflexivity.
  Qed.

  Lemma action_of_last :
    forall s t a, action_of (pi (length s) (s • (t, a))) == a.
  Proof.
    intros; unfold lift; rewrite pi_length_cons; reflexivity.
  Qed.

  Lemma length_dot :
    forall (s : Tr) (e : Event.t), length (s • e) = S (length s).
  Proof.
    intros; rewrite length_app; simpl; lia.
  Qed.

  Lemma last_dot :
    forall (s : Tr) (e : Event.t), length (s • e) - 1 = length s.
  Proof.
    intros; rewrite length_dot; lia.
  Qed.

  (** *** s_se *)

  Fact tribeChildren_s_se : 
    forall s p t e, 
      tribeChildren s p t -> 
      tribeChildren (s • e) p t.
  Proof.
    intros s p t e h_tribeChildren.
    induction h_tribeChildren as
        [i j owner h_range h_owns k child h_interval h_thread h_fork
        | parent child h_tribeChildren IH h_father].
    - assert (k < length s) as h_k_lt.
      {
        apply (@lift_nth_error_defined_left Event.t action k (@snd threadId action) s).
        exists (Fork child); exact h_fork.
      }
      destruct (range_s_se s p i j e h_range) as [[_ h_range_app] | h_range_app].
      + econstructor 1 with (i:=i) (j:=j) (t:=owner) (k:=k).
        * exact h_range_app.
        * apply owns_s_se; exact h_owns.
        * exact h_interval.
        * replace (pi k (s • e)) with (pi k s).
          -- exact h_thread.
          -- symmetry; apply ListBasics.nth_error_append_left; exact h_k_lt.
        * replace (pi k (s • e)) with (pi k s).
          -- exact h_fork.
          -- symmetry; apply ListBasics.nth_error_append_left; exact h_k_lt.
      + econstructor 1 with (i:=i) (j:=length s) (t:=owner) (k:=k).
        * exact h_range_app.
        * apply owns_s_se; exact h_owns.
        * destruct h_interval as [h_i_k _]; lia.
        * replace (pi k (s • e)) with (pi k s).
          -- exact h_thread.
          -- symmetry; apply ListBasics.nth_error_append_left; exact h_k_lt.
        * replace (pi k (s • e)) with (pi k s).
          -- exact h_fork.
          -- symmetry; apply ListBasics.nth_error_append_left; exact h_k_lt.
    - constructor 2 with (t:=parent).
      + exact IH.
      + apply father_s_se; exact h_father.
  Qed.

  Fact tribe_s_se :
    forall s p t, 
      tribe s p t -> 
      forall e, 
        tribe (s •e) p t.
  Proof.
    intros s p t h_tribe e.
    inversion h_tribe.
    - constructor 1; eauto with owns.
    - constructor 2; now apply tribeChildren_s_se.
  Qed.

  Fact tribe_children_se_s_not_fork : 
    forall (s : Tr) e,
      wf_occurences (s • e) ->
      wf_fork (s • e) ->
      wf_open_close (s • e) ->
      forall p t,
      tribeChildren (s • e) p t ->
      (forall t', e <> (t', Fork t)) ->
        tribeChildren s p t.
  Proof.
    intros s e h_wf_occurences h_wf_fork h_wf_open_close p t h_tribeChildren h_neq.
    induction h_tribeChildren as
        [i j owner h_range h_owns k child h_interval h_thread h_fork
        | parent child h_tribeChildren IH h_father].
    - assert (k < length s) as h_k_lt.
      {
        assert (k < length (s • e)) as h_k_lt_app.
        {
          apply (@lift_nth_error_defined_left Event.t action k (@snd threadId action)
                 (s • e)).
          exists (Fork child); exact h_fork.
        }
        destruct (Compare_dec.lt_eq_lt_dec k (length s)) as [[h_k_lt | h_k_eq] | h_k_gt].
        - exact h_k_lt.
        - subst k.
          exfalso.
          apply (h_neq owner).
          destruct e as [last_t last_a].
          rewrite threadId_of_last in h_thread.
          rewrite action_of_last in h_fork.
          injection h_thread; injection h_fork; intros; subst; reflexivity.
        - rewrite length_dot in h_k_lt_app; lia.
      }
      destruct h_interval as [h_i_k h_k_j].
      destruct e as [last_t last_a].
      assert (last_a <> Open p) as h_not_open.
      {
        intro h_last_open.
        assert (i < length s) as h_i_lt by lia.
        assert (action_of (pi i (s • (last_t, last_a))) == Open p) as h_open_i
            by (inversion h_range; subst; assumption).
        assert (action_of (pi (length s) (s • (last_t, last_a))) == Open p) as h_open_last.
        {
          subst last_a; apply action_of_last.
        }
        assert (i = length s) as h_i_eq
            by (apply h_wf_occurences with (a:=Open p);
                [constructor | exact h_open_i | exact h_open_last]).
        lia.
      }
      assert (owns s p owner) as h_owns_s.
      {
        apply owns_se_s with (last_t, last_a).
        - exact h_owns.
        - intro h_eq; inversion h_eq; subst; contradiction.
      }
      assert (threadId_of (pi k s) == owner) as h_thread_s.
      {
        replace (pi k s) with (pi k (s • (last_t, last_a))).
        - exact h_thread.
        - apply ListBasics.nth_error_append_left; exact h_k_lt.
      }
      assert (action_of (pi k s) == Fork child) as h_fork_s.
      {
        replace (pi k s) with (pi k (s • (last_t, last_a))).
        - exact h_fork.
        - apply ListBasics.nth_error_append_left; exact h_k_lt.
      }
      destruct (range_se_s_neq_open s last_t last_a h_wf_occurences h_wf_open_close
                                      p i j h_range h_not_open) as [[_ h_range_s] | [_ h_range_s]].
      + constructor 1 with i j owner k; assumption || split; assumption.
      + constructor 1 with i (length s - 1) owner k; try assumption.
        split; [assumption | lia].
    - assert (father s child parent) as h_father_s.
      {
        apply father_se_s with e.
        - exact h_father.
        - apply h_neq.
      }
      assert (tribeChildren s p parent) as h_tribeChildren_s.
      {
        apply IH.
        intros fork_thread h_eq.
        subst e.
        destruct h_father as [k0 [h_thread_parent h_fork_child]].
        assert (k0 < length s) as h_k0_lt.
        {
          assert (k0 < length (s • (fork_thread, Fork parent))) as h_k0_lt_app.
          {
            apply (@lift_nth_error_defined_left Event.t action k0 (@snd threadId action)
                   (s • (fork_thread, Fork parent))).
            exists (Fork child); exact h_fork_child.
          }
          destruct (Compare_dec.lt_eq_lt_dec k0 (length s)) as [[h_k0_lt | h_k0_eq] | h_k0_gt].
          - exact h_k0_lt.
          - subst k0.
            exfalso.
            rewrite threadId_of_last in h_thread_parent.
            rewrite action_of_last in h_fork_child.
            injection h_thread_parent; injection h_fork_child; intros; subst.
            apply (Nat.lt_irrefl (length s)).
            eapply h_wf_fork.
            + apply action_of_last.
            + apply threadId_of_last.
          - rewrite length_dot in h_k0_lt_app; lia.
        }
        assert (length s < k0) as h_last_lt_k0.
        {
          eapply h_wf_fork.
          - apply action_of_last.
          - exact h_thread_parent.
        }
        lia.
      }
      now constructor 2 with parent.
  Qed.


  Fact tribe_se_s_not_open_fork :
    forall s e p t,
      wf_occurences (s • e) ->
      wf_fork (s • e) ->
      wf_open_close (s • e) ->
      tribe (s • e) p t -> 
      e <> (t, Open p) -> 
      (forall t', e <> (t', Fork t)) -> 
      tribe s p t.
  Proof.
    intros s e p t h_wf_occurences h_wf_fork h_wf_open_close h_tribe h_neq_open h_neq_fork.
    inversion h_tribe.
    - constructor 1.
      now apply owns_se_s with e.
    - constructor 2.
      apply tribe_children_se_s_not_fork with e; try assumption.
  Qed.

  Lemma ancester_l1 : 
    forall s (WF_fork : wf_fork s) t t',
      ancester s t t' -> exists i, threadId_of (pi i s) == t' /\ forall j, j <= i -> threadId_of (pi j s) == t -> False.
  Proof.
    intros s WF_fork t t' HAncester.
    induction HAncester as [ t t' HFather | 
                             t t'' t' Ancester1 IHAncester1 Ancester2  IHAncester2].
    - destruct HFather as [i [Ha Hb]].
      exists i.
      split; [assumption | intros].
      assert (i < j) by eauto. 
      auto with *.
    - destruct IHAncester1 as [i'' [Ha Hb]].
      destruct IHAncester2 as [i' [Hc Hd]].
      exists i'.
      split;[assumption| intros j He Hf].
      assert (j <= i'').
      {
        destruct (Nat.le_gt_cases i' i''); [auto with *|].
        exfalso.
        apply Hd with (j:=i''); auto with *.
      }
      now (apply Hb with (j:=j)).
  Qed.

  Lemma ancester_trans :
    forall s t t' t'', ancester s t t' -> ancester s t' t'' -> ancester s t t''.
  Proof.
    intros.
    constructor 2 with (y:=t'); assumption.
  Qed.

  Lemma ancester_irrefl :
    forall s (WF_fork : wf_fork s) t , ~ancester s t t.
  Proof.
    intros s WF_fork t.
    intro HAncester.
    assert (exists i, threadId_of (pi i s) == t /\ forall j, j <= i -> threadId_of (pi j s) == t -> False)
           as [ i [ Ha Hb ] ] by eauto using ancester_l1.
    now (apply Hb with (j:=i)).
  Qed.

  Lemma ancester_antisym : 
    forall s (WF_fork : wf_fork s) t t', 
      ancester s t t' -> ~ ancester s t' t.
  Proof.
    intros s WF_fork  t t' H H'.
    assert(ancester s t t) by (eauto using ancester_trans).
    eapply ancester_irrefl; eassumption.
  Qed.


  
  Lemma tribeV : 
    forall s p t, tribeChildren s p t -> exists t', ancester s t t' /\ owns s p t'.
  Proof.
    intros s p t0 H.
    induction H.
    - exists t0.
      split.
      constructor 1.
      exists k; auto.
      assumption.
    - destruct IHtribeChildren as [t'' [Ha Hb]].
      exists t''.
      split.
      constructor 2 with (y:=t0).
      constructor 1.
      assumption.
      apply Ha.
      assumption.
  Qed.

  Lemma tribeU : 
    forall s (HWFOcc : wf_occurences s) (WF_fork : wf_fork s)  p t, 
      tribeChildren s p t -> forall t', father s t' t -> ~ owns s p t' .
  Proof.
    intros s HWFOcc WF_fork  p t0 H t' H0 Hc.
    assert (ancester s t' t0) as Hancester by (constructor 1; assumption).
    destruct (tribeV s p t0 H) as [t'' [Ha Hb]].
    assert (t' = t'') by (eauto using owns_functionnal).
    subst.
    contradict Hancester.
    now apply ancester_antisym.
  Qed.

  Lemma tribeExcl : 
    forall s (HWFOcc : wf_occurences s) (WF_fork : wf_fork s)  p t,
      tribeChildren s p t -> owns s p t -> False.
  Proof.
    intros s HWFOcc WF_fork p t0 H H0.
    inversion H as [ ? ? t1 | ? ? t1 ]; subst.
    - replace t0 with t1 in * by (eauto using owns_functionnal).
      elim (Nat.lt_irrefl k); eauto.
    - eapply tribeU; eauto.
  Qed.


  Lemma tribeChildren_notOwner :
    forall s p t',
    wf_occurences s ->
    wf_fork s ->
    tribeChildren s p t' -> 
    forall t,
      owns s p t ->
      t <> t'.
  Proof.
    intros s p t' Hwf h_wf_fork Htc t0 hown.
    intro heq;subst.
    eapply tribeExcl;eauto.
  Qed.
  
  Lemma notInTribe_s_open_not_owner : 
    forall s t p (HWF : wf_occurences (s • (t, Open p))) (HWF2 : wf_fork (s • (t, Open p))) t',  
      t' <> t-> ~ tribe (s • (t, Open p)) p t'.
  Proof.
    intros s t0 p WF1 WF2  t' H.
    intro ht.
    inversion ht as [ ho | htc ] .
    - inversion ho;subst.
      assert (action_of (pi (length s) (s • (t0, Open p))) == Open p) as hlgt by
        apply action_of_last.
      unfold wf_occurences in WF1;unfold occursAtMostOnce in WF1.
      assert (i = (length s)) as heq by now apply WF1 with (Open p).
      rewrite heq in HThreadOf.
      rewrite threadId_of_last in HThreadOf.
      injection HThreadOf; congruence.
    - 
      induction htc as [ i j t1 h_range h_owns |].
      + assert (action_of (pi (length s) (s • (t0, Open p))) == Open p) as h_pi_l by
        apply action_of_last.
        assert (action_of (pi i (s • (t0, Open p))) == Open p) as h_pi_i by (inversion h_range;auto).
        destruct H0 as [h_i_k h_k_j].
        assert (k< length (s • (t0, Open p))) as h_lt_k.
        {
          apply (@lift_nth_error_defined_left Event.t action k (@snd threadId action)
                 (s • (t0, Open p))).
          exists (Fork t'); exact H2.
        }
        rewrite length_dot in h_lt_k.
        change (S k <= S (length s)) in h_lt_k.
        apply le_S_n in h_lt_k.
        assert (i < length s) as h_lt_i.
        {
          unfold lt.
          eapply Nat.le_trans; eauto.
        }

        unfold wf_occurences in WF1.
        unfold occursAtMostOnce in WF1.
        assert (i = length s) as h_eq_i_l by now apply WF1 with (Open p).
        exfalso;lia.
      + destruct (eq_nat_dec t1 t0) as [h_eq_t1t0 | h_neq_t1t0].
        * 
          assert (owns  (s • (t0, Open p)) p t0) as howns
          by (constructor 1 with (length s); [apply threadId_of_last | apply action_of_last]).
          assert (t0<>t1) as hneq by now apply  tribeChildren_notOwner with  (s • (t0, Open p)) p.
         
          intuition auto with *.
        * apply IHhtc; auto.
          constructor 2; assumption.
  Qed.

  Lemma tribeChildren_after_open : 
  forall s,
    wf_fork s ->
    forall p t,
      tribeChildren s p t ->
      forall i,
        threadId_of (pi i s) == t ->
        exists j, j < i /\ action_of (pi j s) == Open p.
Proof.
  intros s h_wf_fork p t h_tribeChildren.
  induction h_tribeChildren 
    as [ i j t h_range h_owns k t' h_int h_id_k h_action_k 
        | t' t h_tribeChildren IH h_father ].
  - intros i0 h_id_t'.
    assert (k < i0) by (eauto using h_wf_fork).
    (exists i); split; [auto with * | inversion h_range; assumption].
  - intros i0 h_id_t. 
    destruct h_father as [k0 [h_id_k0 h_act_k0]].
    assert (k0 < i0) by (eauto using h_wf_fork).
    destruct (IH k0 h_id_k0) as [j [h_lt h_act_j]].
    (exists j); split; auto with *.
Qed.


Lemma tribe_after_open : 
  forall s,
    wf_occurences s ->
    wf_fork s ->
    forall i j p t,
      i <= j ->
      threadId_of (pi i s) == t ->
      action_of (pi j s) == Open p ->
      tribe s p t ->
      owns s p t.
Proof.
  intros s h_wf_occ h_wf_fork i j p t h_lt h_id h_open h_tribe.
  inversion h_tribe; subst.
  - assumption.
  - destruct (tribeChildren_after_open s h_wf_fork p t H i h_id) as [i0 [h_lt' h_open']].
    assert (j = i0 ) by wellFormed_occurences (Open p).
    subst; exfalso; auto with *.
Qed.  

  Lemma tribeChildren_father_tribe : 
    forall s, 
      wf_occurences s ->
      forall p t,
        tribeChildren s p t ->
        forall t', father s t t' -> tribe s p t'. 
  Proof.
    intros s h_wf p t h_tc t' h_father.
    destruct h_father as [i [h_tid h_act]].
    inversion h_tc as [ ? ? ? ? ?  i' ? ? h_tid' ? | ? ? ? h_father' ]; subst. 
    - replace i' with i in * by wellFormed_occurences (Fork t).
      assert (owns s p t') by (rewrite h_tid in h_tid'; injection h_tid'; congruence).
      now constructor 1.
    - destruct h_father' as [i' [h_tid' h_act']].
      replace i' with i in * by wellFormed_occurences (Fork t).
      rewrite h_tid in h_tid'; injection h_tid'; intros; subst.
      now constructor 2.
  Qed.

 Fact tribeChildrenOpen_empty : 
  forall s t p (HWFOcc : wf_occurences (s • (t, Open p))) t',
    tribeChildren (s • (t, Open p)) p t' -> False.
  Proof.
    intros s t p HWFOcc t' Htc.
    induction Htc as [i j owner Hrange Howns k child Hinterval Hthread Hfork
                     | child parent Htc IH Hfather].
    - assert (i = length s); subst.
      {
        assert (action_of (pi i (s • (t, Open p))) == Open p) by (inversion Hrange; assumption).
        assert (action_of (pi (length s) (s • (t, Open p))) == Open p) 
               by apply action_of_last.
        apply HWFOcc with (a:=Open p); auto.
      }
      assert (j < length (s • (t, Open p))) as h_j_lt
          by (eapply range_j_lt_s; eauto).
      rewrite length_dot in h_j_lt.
      apply le_S_n in h_j_lt.
      destruct Hinterval as [h_i_k h_k_j].
      assert (k <= length s) as h_k_le_s
          by (eapply Nat.le_trans; eauto).
      lia.
    - assumption.
  Qed.
  
  Fact tribeOpen_single :
  forall s t p (HWFOcc : wf_occurences (s • (t, Open p))) t',
    tribe (s • (t, Open p)) p t' <-> t = t'.
  Proof.
    intros s t0 p HWFOcc t'.
    assert (threadId_of (pi (length s) (s • (t0, Open p))) == t0) as Ha 
           by apply threadId_of_last.
    assert (action_of (pi (length s) (s • (t0, Open p))) == Open p) as Hb 
           by apply action_of_last.
    split; intros.
    - inversion H as [ Howns1 | ]. unfold wf_occurences, occursAtMostOnce in HWFOcc.
      + assert (owns (s • (t0, Open p)) p t0) as Howns2 by
               now (apply owns_cons with (i:=length s)).
        inversion Howns1 as [ _1 i _2 Hi]; inversion Howns2 as [ _3 i' _4 Hi']; subst.
        assert (i = i') as Heq by firstorder.
        assert (Some t0 = Some t') by (rewrite <- Hi, <- Hi', Heq; trivial).
        now injection H0.
      + exfalso; eapply tribeChildrenOpen_empty; eauto.
    - subst.
      constructor 1.
      assert (threadId_of (pi (length s) (s • (t', Open p))) == t') 
             by apply threadId_of_last.
      assert (action_of (pi (length s) (s • (t', Open p))) == Open p) 
             by apply action_of_last.
      now apply owns_cons with (i := length s).
  Qed.

  Ltac pi_simpl:=
    autorewrite with length in*; simpl in *; try(rewrite Nat.add_comm, Nat.sub_add in *);
    autorewrite with nth_error in *; trivial.

 Lemma wellFormed_close_in_tribe :
    forall s p t,
      wellFormed (s • (t, Close p)) -> tribe s p t.
  Proof.
    intros s p t H.
    constructor 1.
    inversion H as [ ? ? ? WFOpenClose _ _  _ ?].
    assert(action_of (pi (length s) (s • (t, Close p))) == Close p) as H' 
      by (unfold lift; rewrite pi_length_cons; reflexivity).
    specialize(WFOpenClose (length s) p H').
    destruct WFOpenClose as [j [ Hj [ Haction Hthreadid] ] ].
    exists j.
    assert(threadId_of (pi (length s) (s • (t, Close p))) == t) as H'' by 
      (unfold lift; rewrite pi_length_cons; reflexivity).
    rewrite <- H''. rewrite Hthreadid at 1. 
    now rewrite ListBasics.nth_error_append_left. trivial.
    rewrite <- Haction.
    now rewrite ListBasics.nth_error_append_left.
  Qed.

  Lemma wellFormedOpenFirst : 
    forall s t p, wellFormed (s • (t, Open p)) -> ~ occursIn s (Close p).
  Proof.
    intros s t0 p H.
    intro Hocc.
    assert (action_of (pi (length s) (s • (t0, Open p))) == Open p) as Hlast
        by apply action_of_last.
    remember (Close p) as close_action eqn:h_close_action.
    destruct Hocc as [i a Hclose].
    subst a.
    inversion H as [WF_occurences WF_fork WF_join WF_open_close
                    WF_seq_order WF_join_see_fork WF_join_all_closed
                    WF_mutualExclusion].
    assert (i < length s) as h_i_lt.
    {
      apply (@lift_nth_error_defined_left Event.t action i (@snd threadId action) s).
      exists (Close p); exact Hclose.
    }
    assert (action_of (pi i (s • (t0, Open p))) == Close p) as Hclose_app.
    {
      replace (pi i (s • (t0, Open p))) with (pi i s).
      - assumption.
      - symmetry; apply ListBasics.nth_error_append_left; assumption.
    }
    destruct (WF_open_close i p Hclose_app) as [i' [Hb [Hc Hd]]].
    assert (i' = length s) by
        (apply WF_occurences with (a:= Open p); [constructor | exact Hc | exact Hlast]).
    subst.
    lia.
  Qed.

 Fact tribeOpen : 
    forall s p t, tribe s p t -> occursIn s (Open p).
  Proof.
    intros s p t HTribe.
    destruct HTribe as [HOwns | HTribeChildren].
    - assert (exists i, action_of (pi i s) == Open p) as [i] by (inversion HOwns; eauto).
      apply occursIn_cons with (i:=i); assumption.
    - induction HTribeChildren as [ ? ? t0 ? HOwns | ].
      + have HOwns (owns s p t0).
        inversion HOwns as [? i' ? ? Hi'].
        have Hi' (action_of (pi i' s) == Open p).
        apply occursIn_cons with (i:=i'); assumption.
      + assumption.
  Qed.

  Fact tribe_empty :
    forall p t, ~ tribe nil p t.
  Proof. 
    intros p t. 
    intro HTribe.
    destruct HTribe.
    - inversion H.
      destruct i; simpl in *; discriminate.
    - inversion H.
      + inversion H0; subst; destruct i; simpl in *; discriminate.
      + destruct H1 as [i [Ha Hb]].
        destruct i; simpl in *; discriminate.
  Qed.

 Lemma tribeA : 
    forall s p t t' (WF_occurences : wf_occurences (s • (t',Fork t)))
           (WF_open_close : wf_open_close (s • (t', Fork t)))
           (WF_fork : wf_fork (s • (t', Fork t))),
      ~ tribe s p t' -> ~ tribe (s • (t', Fork t)) p t.
  Proof.
    intros s p t t' WF_occurences WF_open_close WF_fork HTribe.
    contradict HTribe.
    assert (t <>t') as HDiff. 
    {
      intro; subst.
      assert (length s < length s).
      {
        apply WF_fork with (t:=t').
        - apply action_of_last.
        - apply threadId_of_last.
      }
      auto with *.
    }
    inversion HTribe; subst.
    - inversion H; subst.
      assert (i < length s) by
             eauto with nth_error.
      assert (length s < i).
      {
        apply WF_fork with (t:=t).
        - apply action_of_last.
        - assumption.
      }
      exfalso; auto with *.  
    - assert(tribe (s • (t', Fork t)) p t') as Htribe.
      {
        assert(threadId_of (pi (length s) (s • (t', Fork t))) == t') by 
          apply threadId_of_last.
        assert(action_of (pi (length s) (s • (t', Fork t))) == Fork t) by 
          apply action_of_last.
        assert (father (s • (t', Fork t)) t t').
        {
          exists (length s); tauto.
        }
        eauto using tribeChildren_father_tribe.
      }
      assert( (t', Fork t) <> (t', Open p) ) by (intro;discriminate).
      inversion Htribe as [ Howns | Htribe'].
      + assert(owns s p t') by (now apply owns_se_s in Howns).
        now constructor 1.
      + assert(forall t'0 : threadId, (t', Fork t) <> (t'0, Fork t')).
        { 
          intros t'0 Heq.
          contradict HDiff.
          inversion Heq.
          trivial.
        }
        assert(tribeChildren s p t') by eauto using tribe_children_se_s_not_fork.
        now constructor 2.
  Qed.

  Lemma tribeB : 
    forall s e (HWFOcc : wf_occurences (s • e))
           (HWFOpenClose : wf_open_close (s • e))
           (HWFFork : wf_fork (s • e)) p t,
      ~ tribe s p t -> (forall t' t'', e <> (t', Fork t'')) -> (forall t' p', e <> (t', Open p')) -> ~ tribe (s • e) p t.
  Proof.
    intros s e HWFOcc HWFOpenClose HWFFork p t0 H H0 H1.
    contradict H.
    apply tribe_se_s_not_open_fork with (e:=e); try auto.
  Qed.

  Lemma tribeC :
    forall s p t t' i,
      owns s p t' -> 
      range (s • (t', Fork t)) p i (length (s • (t', Fork t)) - 1) -> 
      tribe (s • (t', Fork t)) p t.
  Proof.
    intros s p t t' i HOwns HRange.
    constructor 2.
    constructor 1 with (i:=i) (j:=length (s • (t', Fork t)) -1) (t:=t') (k:=length (s •(t',Fork t)) -1).
    - assumption.
    - apply owns_s_se; assumption.
    - split.
      + rewrite last_dot.
        assert (action_of (pi i (s • (t', Fork t))) == Open p) as h_open
            by (inversion HRange; subst; assumption).
        assert (i < length (s • (t', Fork t))) as h_i_lt.
        {
          apply (@lift_nth_error_defined_left Event.t action i (@snd threadId action)
                 (s • (t', Fork t))).
          exists (Open p); exact h_open.
        }
        rewrite length_dot in h_i_lt.
        assert (i <> length s) as h_i_neq.
        {
          intro; subst.
          rewrite action_of_last in h_open.
          discriminate.
        }
        lia.
      + lia.
    - rewrite last_dot; apply threadId_of_last.
    - rewrite last_dot; apply action_of_last.
  Qed.

  Lemma wf1 : 
    forall s t t', wf_fork (s • (t, Fork t')) -> t <> t'.
  Proof.
    intros; intro; subst.
    apply (Nat.lt_irrefl (length s)).
    apply H with (t:=t').
    - unfold lift; rewrite pi_length_cons; reflexivity.
    - unfold lift; rewrite pi_length_cons; reflexivity.
  Qed.

  Lemma tribeD : 
    forall s p t t' (HWFOcc : wf_occurences (s • (t', Fork t)))
           (HWF_fork : wf_fork (s • (t',Fork t))) i j,
      owns s p t' -> range (s • (t', Fork t)) p i j ->
      j < length (s • (t', Fork t)) - 1 ->
      ~ tribe (s • (t', Fork t)) p t.
  Proof.
    intros s p t t' HWFOcc HWF_fork_join i j HOwns HRange HLt.
    intro HTribe.
    assert (t' <> t) by (eapply wf1; eauto).
    inversion HTribe; subst.
    - assert (owns (s • (t', Fork t)) p t') by eauto with owns.
      elim H.
      eauto using owns_functionnal.
    - inversion H0; subst.
      + assert (i0 =i).
        {
          edestruct range_functionnal.
          apply HWFOcc.
          apply HRange.
          apply H1.
          auto.
        }
        subst.
        assert (j0=j).
        {
          edestruct range_functionnal.
          apply HWFOcc.
          apply HRange.
          apply H1.
          auto.
        }
        subst.
        assert (k = length (s • (t', Fork t)) - 1). 
        {
          assert (action_of (pi (length s) (s • (t', Fork t))) == Fork t) 
              by apply action_of_last.
          assert (k = length s) by now (apply HWFOcc with (a:=Fork t)).
          rewrite last_dot.
          assumption.
        }
        subst.
        intuition auto with *.
      + assert (t0=t').
        {
          assert (father (s • (t', Fork t)) t t').
          {
            exists (length s).
            split; [apply threadId_of_last | apply action_of_last].
          }
          eauto using father_functionnal.
        }
        subst.
        assert (owns (s • (t', Fork t)) p t') by auto with owns.
        eapply tribeExcl; eauto.
  Qed.

  Hint Resolve tribe_empty : tribe.




        

      
End Make.

Module Type TribeT (Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ) 
            ( TraceMod : Trace.T Perm Address T V)
            ( P : Proj Perm Address T V TraceMod)
            ( O : OccurencesT Perm Address T V TraceMod P)
            ( F : FatherT Perm Address T V TraceMod P O) 
            ( OW : OwnsT Perm Address T V TraceMod P O)
            ( R : RangeT Perm Address T V TraceMod P O).
  Include (Make Perm Address T V TraceMod P O F OW R).
End TribeT.
