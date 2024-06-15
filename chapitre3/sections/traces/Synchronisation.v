Require Import Relation_Operators Operators_Properties Wf_nat Arith Lia.
From sections.lifo Require Import Prelude ListBasics. 
From sections.traces Require Import Trace_Theory.

(** In this section, we define the notion of well-synchronized trace. After
     we prove a few basic properties over such traces, we prove that while
     a section is opened members of its tribe cannot synchronize with 
     non-member which enforces that no conflict can occur with the latters *)

Module Make ( P : MiniDecidableSet )
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T).
  
  Include Trace_Theory.Make P Address T V.
  
  (* TO MOVE *)

  Lemma sec_order_s_se : 
    forall s p p' e,
      sec_order s p p' -> sec_order (s • e) p p'.
  Proof.
    intros s p p' e h_sec.
    destruct h_sec.
    - case_eq (pi i s); [intros [t a] h_eq | intros h_neq]; subst.
      + edestruct range_s_se.
        apply H.
        * destruct H3.
          apply sec_order_cons_dir with i j k.
          apply H4.
          assumption.
          eauto with nth_error.
          replace (pi i s) with (pi i (s • e)) in H2 by eauto with nth_error.
          replace (pi k s) with (pi k (s • e)) in H2 by eauto with nth_error.
          assumption.
        * apply sec_order_cons_dir with i (length s) k.
          assumption.
          assert (k < length s) by eauto with nth_error.
          auto with *.
          eauto with nth_error.
          replace (pi i s) with (pi i (s • e)) in H2 by eauto with nth_error.
          replace (pi k s) with (pi k (s • e)) in H2 by eauto with nth_error.
          assumption.
      + inversion H; subst.
        * rewrite h_neq in Hi; discriminate.
        * rewrite h_neq in Hi; discriminate.
    - apply sec_order_cons_ind with i i' t0.
      eauto with nth_error.
      eauto with nth_error.
      eauto with nth_error.
      now apply tribeChildren_s_se.
  Qed.

  (** * Definitions *)

  (** Two actions conflict if they are both memory accesses over
       the same location and at least one of them is a write.*)
  
  Inductive conflict : action -> action -> Prop :=
  | conflict_rw : 
    forall l n v v', conflict (Read l n v) (Write l n v')
  | conflict_wr : 
    forall l n v v', conflict (Write l n v) (Read l n v')
  | conflict_ww : 
    forall l n v v', conflict (Write l n v) (Write l n v').
  
  (** We define when two events in a trace synchronize with each other.
       - every event performed by a thread [t] synchronizes with subsequent events performed by [t]
       - a fork of a thread [t] synchronizes with events performed by [t]
       - every event performed by a thread [t] synchronizes with a join over [t]
       - closing a section s
       The [synchronizeWith] relation is defined as the transitive closure of [sw].*)
  
  Inductive sw : Tr -> nat -> nat -> Prop :=
  | swSeq :
    forall s i j t, 
      i < j ->
      threadId_of (pi i s) == t -> 
      threadId_of (pi j s) == t ->
      sw s i j
  | swFork :
    forall s i j t,
      i <  j ->
      action_of (pi i s) == Fork t -> 
      threadId_of (pi j s) == t -> 
      sw s i j
  | swJoin : 
    forall s i j t,
      i < j ->
      threadId_of (pi i s) == t -> 
      action_of (pi j s) == Join t ->
      sw s i j
  | swAtomic :
    forall s i j p p',
      i < j ->
      concurrent s p p' -> 
      action_of (pi i s) ==  Close p -> 
      action_of (pi j s) == Open p' ->
      sw s i j.
  
  Definition synchronizeWith (s : Tr)  := clos_trans _ (sw s).
  
  (** A trace is well-synchronized if every pair of events containing conflicting
       action synchronize *)
  
  Definition wellSynchronized (s : Tr) :=
    forall i j a a', 
      i < j -> 
      action_of (pi i s) == a ->
      action_of (pi j s) == a' ->
      conflict a a' -> 
      synchronizeWith s i j.
  
  (** * Basic results *)

  Lemma synchronizeWith_lt_i :
    forall s i j,
      synchronizeWith s  i j ->
      i < length s.
  Proof.
    intros s i j H_sync.
    induction H_sync as [ i j h_ws | ].
    - inversion h_ws;eauto with nth_error.
    - intuition.
  Qed.
  
  Lemma synchronizeWith_se_s :
    forall s e i j,
      wf_occurences (s • e) ->
      wf_open_close (s • e) ->
      synchronizeWith ( s • e) i j ->
      j < length s ->
      synchronizeWith s  i j.
  Proof.
    intros s e i j h_wf_occ h_wf_oc H .
    induction H as [ i j | ].
    - intro Hlt_ys.
      inversion H as 
          [ a b c t0 Hlt Hti Htj | a b c t0 Hlt Hti Htj |   a b c   t0 Hlt Hti Htj  
            |  a b c p p' t0 Hlt Hti Htj  ];subst.
      + assert (i<length s) as His.
        assert (j<length s) as His by eauto with nth_error.
        lia.      
        assert (pi i (s • e) = pi i s) as Ha by eauto with nth_error.
        assert (pi j (s • e) = pi j s) as Hb by eauto with nth_error.
        assert (threadId_of (pi i (s )) == t0) as Hti_s by now rewrite Ha in Hti at 1.
        assert (threadId_of (pi j (s )) == t0) as Htj_s by now rewrite Hb in Htj at 1.
        constructor; constructor 1 with t0;auto.
      + assert (i<length s) as His.
        assert (j<length s) as His by eauto with nth_error.
        lia. 
        assert (pi i (s • e) = pi i s) as Ha by eauto with nth_error.
        assert (pi j (s • e) = pi j s) as Hb by eauto with nth_error.
        assert (action_of (pi i s ) == Fork t0) as Hi_fork  by  now rewrite Ha in Hti at 1.
        assert (threadId_of (pi j (s )) == t0) as Htj_s by now rewrite Hb in Htj at 1.
        constructor; constructor 2 with t0;auto.
      + assert (i<length s) as His.
      assert (j<length s) as His by eauto with nth_error.
      lia. 
        assert (pi i (s • e) = pi i s) as Ha by eauto with nth_error.
        assert (pi j (s • e) = pi j s) as Hb by eauto with nth_error.
        assert (threadId_of (pi i (s )) == t0) as Hti_s by now rewrite Ha in Hti at 1.
        assert (action_of (pi j s ) == Join t0) as Hj_Join  by  now rewrite Hb in Htj at 1.
        constructor; constructor 3 with t0;auto.
      + assert (i<length s) as His.
      assert (j<length s) as His by eauto with nth_error.
        lia.   
        (* eauto with nth_error. *)
        assert (pi i (s • e) = pi i s) as Ha by eauto with nth_error.
        assert (pi j (s • e) = pi j s) as Hb by eauto with nth_error.
        assert (action_of (pi i s ) == Close p) as Hi_close  by now rewrite Ha in Hti at 1.
        assert (action_of (pi j s ) == Open p') as Hj_open  by  now rewrite Hb in Htj at 1.
        constructor; constructor 4 with p p';auto.
        inversion Hlt; subst.
        destruct H1 as [Hu [Hw Hx]].
        constructor.
        assert (occursIn s (Open p)).
        {
          destruct e as [t a].
          apply occursIn_se_s_neq with t a.
          assumption.
          destruct (h_wf_oc _ _ Hti) as [j0 [Hi [Hj Hk]]].
          intro; subst.
          assert (action_of (pi (length s) (s • (t, Open p))) == Open p).
          now autorewrite with nth_error.
          assert (j0 = length s) by wellFormed_occurences (Open p).
          subst.
          auto with *.
        }
        assumption.
        split.
        exists j.
        assumption.
        split.
        contradict Hw.
        now apply sec_order_s_se.
        contradict Hx.
        now apply sec_order_s_se.
    - intros.
      assert (synchronizeWith s y z) as H_sync_yz by now apply IHclos_trans2.
      assert (y<length s) as Hlt_ys by now apply synchronizeWith_lt_i with z.
      assert (synchronizeWith s x y) as H_sync_xy by now apply IHclos_trans1.
      now constructor 2 with y.
      Qed.
  (* Qed. *)

  Lemma synchronizeWith_s_se :
    forall s e i j,
      wf_occurences (s • e) ->
      wf_fork (s • e) ->
      wf_open_close (s • e) ->
      synchronizeWith s  i j ->
      synchronizeWith  (s • e)  i j.
  Proof.
    intros s e i j wf_occ wf_fork wf_oc H.
    induction H.
    - inversion H;subst;constructor.
      + constructor 1 with t0;auto with nth_error.
      + constructor 2 with t0;auto with nth_error.
      + constructor 3 with t0;auto with nth_error.
      + constructor 4 with p p' ;auto with nth_error.
        apply concurrent_s_se; try assumption.
    - constructor 2 with y;auto.
  Qed.

  Lemma wellSynchronized_se_s :
    forall s e,
      wf_occurences (s • e) ->
      wf_open_close (s • e) ->
      wellSynchronized (s • e) -> wellSynchronized s.
  Proof.
    intros s e wf_occ wf_oc Hws.
    unfold wellSynchronized in *.
    intros i j a a' Hlt_ij Hai Haj' Hcfl.
    assert (synchronizeWith (s • e) i j) as H_sync_e by (apply Hws with a a';eauto with nth_error).
    assert (j<length s) as Hjs by eauto with nth_error.
    now apply synchronizeWith_se_s with e.
  Qed.
    
  Lemma synchronizeWithOrder : 
    forall s i j, synchronizeWith s i j -> i < j.
  Proof.
    intros s i j synchronizeWith_i_j.
    induction synchronizeWith_i_j as [i j sw_i_j | ].
    - inversion sw_i_j; subst; eauto.
    - eauto using Nat.lt_trans.
  Qed.
  
  Lemma synchronizeWithIn : 
    forall s j k, synchronizeWith s j k -> k < length s.
  Proof.
    intros s j k H.
    induction H; inversion H; assert (y < length s) by eauto with nth_error; assumption.
  Qed.

  Lemma synchronizeWithInL : 
    forall s j k, synchronizeWith s j k -> j < length s.
  Proof.
    intros s j k H.
    induction H.
    inversion H; eauto with nth_error.
    intuition.
  Qed.
  
  Lemma synchronizeWith_lt_i_s_minus_1 :
    forall s i j,
      synchronizeWith s  i j ->
      i < (length s -1).
  Proof.
    intros  s i j  H_sync.
    assert (j<length s) as hltj by now apply synchronizeWithIn with i .
    assert (i<j) as hlti by now apply (synchronizeWithOrder s) .
    lia.
  Qed.
      
  (** *** Some event exists at any position involved in a synchronisation *)
  
  Lemma synchronizeWith_exists_event : 
    forall s,
      wellFormed s ->
      wellSynchronized s ->
      forall k k', 
        synchronizeWith s k k' \/ synchronizeWith s k' k -> 
        (exists t, threadId_of (pi k s) == t) /\ (exists a, action_of (pi k s) == a).
  Proof.
    intros s h_wf h_ws k k' [synchronizeWith_k_k' | synchronizeWith_k'_k].
    - induction synchronizeWith_k_k' as [k k' sw_k_k'|].
      + inversion sw_k_k'; subst.
        * assert(k<length s) by (eapply lift_nth_error_defined_left; exists t0; apply H0).
          split;
          eauto with nth_error.
        * assert(k<length s) by (eapply lift_nth_error_defined_left; exists (Fork t0); apply H0).
        split;
        eauto with nth_error.
        * assert(k<length s) by (eapply lift_nth_error_defined_left; exists t0; apply H0).
        split;
        eauto with nth_error.
          (* split; firstorder using nth_error. *)
        * assert(k<length s) by (eapply lift_nth_error_defined_left; exists (Close p); apply H1).
        split;
        eauto with nth_error.
          (* split; firstorder using nth_error. *)
      + assumption.
    - induction synchronizeWith_k'_k as [k' k sw_k'_k|].
      + inversion sw_k'_k; subst.
        * assert(k<length s) by (eapply lift_nth_error_defined_left; exists t0; apply H1).
        split;
        eauto with nth_error.
          (* split; firstorder using nth_error. *)
        * assert(k<length s) by (eapply lift_nth_error_defined_left; exists t0; apply H1).
        split;
        eauto with nth_error.
          (* split; firstorder using nth_error. *)
        * assert(k<length s) by (eapply lift_nth_error_defined_left; exists (Join t0); apply H1).
        split;
        eauto with nth_error.
          (* split; firstorder using nth_error. *)
        * assert(k<length s) by (eapply lift_nth_error_defined_left; exists (Open p'); apply H2).
        split;
        eauto with nth_error.

          (* split; firstorder using nth_error. *)
      + assumption.
      Qed.

  (** ** TribeChildren synchronize with section opening *)
  
  Lemma aux0' : 
    forall s i p, 
      wf_occurences s ->
      wf_fork s ->
      action_of (pi i s) == Open p ->
      forall t, 
        tribeChildren s p t -> 
        forall j, 
          threadId_of (pi j s) == t -> 
          synchronizeWith s i j.
  Proof.
    intros s i p H_occ H_fork HOpen t HTribeChildren.
    
    induction HTribeChildren.
    - intros j0 HThread.
      assert (synchronizeWith s i k). 
      {
        constructor 1.
        assert (i < k).
        { 
          inversion H; subst;
          assert(i = i0) by (now apply (H_occ (Open p)));
          destruct H1;
          subst;
          trivial.
        }
        assert (threadId_of (pi i s) == t0) by now (apply ownsOpen with (p:=p)).
        constructor 1 with (t:=t0); assumption.
      }
      assert (synchronizeWith s k j0).
      {
        constructor 1.
        constructor 2 with (t:=t'). 
        unfold wf_fork in H_fork.
        apply H_fork with t'.
        assumption.
        assumption.
        assumption.
        assumption.
      }
      constructor 2 with (y:=k); assumption.
    - intros j0 HThread.
      destruct H as [k [Ha Hb]].
      assert (synchronizeWith s i k) by
             now(apply IHHTribeChildren).
      
      assert (synchronizeWith s k j0). 
      {
        constructor 1.
        constructor 2 with (t:=t'). 
        apply H_fork with t'.
        assumption.
        assumption.
        assumption.
        assumption.
      }
      constructor 2 with (y:=k); assumption.
  Qed.
  
  (** Opening of ordered sections synchronize *)
  
  Lemma aux1' : 
    forall s i j p p',
      wf_occurences s ->
      wf_fork s ->
      action_of (pi i s) == Open p -> 
      action_of (pi j s) == Open p' -> 
      i < j ->
      sec_order s p p' -> 
      synchronizeWith s i j.
  Proof.
    intros s i j p p'  H_occ H_fork H0 H1 h_lt H2.
    assert (exists t, threadId_of (pi i s) == t) as [t Ht].
    {
     assert(i<length s). 
        eapply lift_nth_error_defined_left. exists (Open p). apply H0.
        eauto with nth_error.
    }
    assert (exists t', threadId_of (pi j s) == t') as [t' Ht'].
    {
        assert(j<length s).
         eapply lift_nth_error_defined_left. exists (Open p'). apply H1.
            eauto with nth_error.
    }
    inversion H2; subst.
    assert (i < j) by assumption.
    assert (tribe s p t').
    {
      inversion H2; subst.
      - constructor 1.
        exists i.
        assert (i = i0) by (inversion H; wellFormed_occurences (Open p)); subst.
        assert (i0 = i1) by (inversion H7; wellFormed_occurences (Open p)); subst.
        assert (k = k0) by (inversion H7; wellFormed_occurences (Open p')); subst.
        assert (k0 = j) by ( wellFormed_occurences (Open p')); subst.
        congruence.
        assumption.
      - assert (i0 = i) by (inversion H; wellFormed_occurences (Open p)); subst.
        assert (i' = j) by wellFormed_occurences (Open p').
        subst.
        assert (t0 = t') by congruence.
        subst.
        constructor 2; assumption.
    }
    inversion H5.
    - assert (t= t').
      {
        assert (i = i0) by (inversion H; wellFormed_occurences (Open p)); subst.
        assert (k = j) by wellFormed_occurences (Open p'); subst.
        congruence.
      }
      subst.
      constructor 1.
      constructor 1 with (t:=t'); assumption.
    - apply aux0' with (p:=p) (t:=t'); try assumption.
      assert (j = i') by (apply H_occ with (a:=Open p'); auto).
      subst.
      congruence.
      Qed.
  (* Qed. *)

  (** Openings of distinct sections synchronize *)

  Lemma aux2' :
    forall s i j p p',
      wf_occurences s ->
      wf_fork s ->
      wf_open_close s ->
      wf_mutualExclusion s ->
      p <> p' ->
      action_of (pi i s) == Open p ->
      action_of (pi j s) == Open p' ->
      synchronizeWith s i j \/ synchronizeWith s j i.
  Proof.
    intros s i j p p' h_wf_occ  h_wf_fork h_wf_op_cl h_wf_mutualExclusion H3 H4 H5.
    destruct (Compare_dec.lt_dec i j).
    - left.
      destruct (sec_order_dec s p p'); try assumption.
      eapply aux1'; eauto.
      destruct (sec_order_dec s p' p) ; try assumption.
      + 
        {
          inversion H0; subst.
          - assert (k = i) by wellFormed_occurences (Open p); subst.
            assert (j = i0) by (inversion H1; wellFormed_occurences (Open p')); subst.
            constructor 1.
            case_eq (pi i s); [intros [t a] h_eq | intros h_neq]; subst.
            constructor 1 with t.
            assumption.
            unfold Event.t in *; rewrite h_eq; reflexivity.
            unfold Event.t in *; rewrite H7.
            unfold Event.t in *; rewrite h_eq; reflexivity.
            rewrite h_neq in H6; discriminate.
          - assert (i' = i) by wellFormed_occurences (Open p); subst.
            clear H1 H2.
            inversion H7; subst.
            * assert (i1 = j) by (inversion H1; wellFormed_occurences (Open p')); subst.
              assert (k < i) by (eapply h_wf_fork; eauto).
              exfalso; auto with *.
            * assert (synchronizeWith s j i). 
              apply aux0' with p' t0; try assumption.
              assert (j < i) by now apply synchronizeWithOrder with s.
              exfalso; auto with *.
        }
      + assert (concurrent s p p').
        unfold concurrent; repeat (split; eauto);
        eauto with *.
        (* (unfold concurrent; repeat (split; eauto); tauto). *)
        apply h_wf_mutualExclusion in H1.
        destruct H1.
        * inversion H1; subst.
          assert (j0 = j) by wellFormed_occurences (Open p').
          subst.
          constructor 2 with i0.
          constructor 1.
          case_eq (pi i0 s); case_eq (pi i s); intros; subst.
          destruct t0 as [t a].
          destruct t1 as [t' a'].
          assert (i < i0 /\ t = t') as [Hu Hv].
          {
            apply h_wf_op_cl in Ha.
            destruct Ha as [j0 [ Hu[Hv Hw]]].
            assert (j0 = i) by wellFormed_occurences (Open p).
            subst.
            rewrite H2 in Hw.
            rewrite H6 in Hw.
            injection Hw; intros; subst.
            tauto.
          }
          subst.
          constructor 1 with t'.
          assumption.
          unfold Event.t in *; rewrite H2; reflexivity.
          unfold Event.t in *; rewrite H6; reflexivity.
          rewrite H2 in H4; discriminate.
          rewrite H6 in Ha; discriminate.
          rewrite H2 in H4; discriminate.
          assert (concurrent s p p').
          {
            unfold concurrent.
            split.
            eauto with *.
            eauto with *.
          }
          constructor 1.
          now constructor 4 with p p'.
        * exfalso.
          inversion H1; subst.
          assert (i = j0) by wellFormed_occurences (Open p).
          subst.
          apply h_wf_op_cl in Ha.
          destruct Ha as [j1 [Hu [Hv Hw]]].
          assert (j1 = j) by wellFormed_occurences (Open p').
          subst.
          auto with *.
    - right.
      assert (j < i).
      {
        assert (j <> i) by
            (intro; subst; replace p with p' in * by congruence; intuition).
        auto with *.
      }
      destruct (sec_order_dec s p' p); try assumption; [eapply aux1'; eauto | ].
      destruct (sec_order_dec s p p'); try assumption.
      + inversion H1; subst.
        * assert (i = i0) by (inversion H2; wellFormed_occurences (Open p)); subst.
          assert (k = j) by wellFormed_occurences (Open p'); subst.
          case_eq (pi j s); [intros [t a] h_eq | intros h_eq]; subst.
          constructor 1; constructor 1 with t.
          assumption.
          unfold Event.t in *; rewrite h_eq; reflexivity.
          unfold Event.t in *; rewrite H8.
          unfold Event.t in *; rewrite h_eq; reflexivity.
          unfold Event.t in *; rewrite h_eq in H5; discriminate.
        * assert (i' = j) by wellFormed_occurences (Open p'); subst.
          assert (synchronizeWith s i j).
          apply aux0' with p t0; try assumption.
          assert (i < j) by now apply synchronizeWithOrder with s.
          exfalso; intuition.
      + assert (concurrent s p' p).
        {
          unfold concurrent.
          split;
          eauto with *.
        }
        apply h_wf_mutualExclusion in H2.
        destruct H2.
        * inversion H2; subst.
          assert (j0 = i) by wellFormed_occurences (Open p).
          subst.
          constructor 2 with i0.
          constructor 1.
          case_eq (pi i0 s); case_eq (pi j s); intros; subst.
          destruct t0 as [t a].
          destruct t1 as [t' a'].
          assert (j < i0 /\ t = t') as [Hu Hv].
          {
            apply h_wf_op_cl in Ha.
            destruct Ha as [j0 [ Hu[Hv Hw]]].
            assert (j0 = j) by wellFormed_occurences (Open p').
            subst.
            rewrite H6 in Hw.
            rewrite H7 in Hw.
            injection Hw; intros; subst.
            tauto.
          }
          subst.
          constructor 1 with t'.
          assumption.
          unfold Event.t in *; rewrite H6; reflexivity.
          unfold Event.t in *; rewrite H7; reflexivity.
          rewrite H6 in H5; discriminate.
          rewrite H7 in Ha; discriminate.
          rewrite H6 in H5; discriminate.
          assert (concurrent s p' p).
          {
            unfold concurrent.
            split;
            eauto with *.
          }
          constructor 1.
          now constructor 4 with p' p.
        * exfalso.
          inversion H2; subst.
          assert (j = j0) by wellFormed_occurences (Open p').
          subst.
          apply h_wf_op_cl in Ha.
          destruct Ha as [j1 [Hu [Hv Hw]]].
          assert (j1 = i) by wellFormed_occurences (Open p).
          subst.
          auto with *.
          Qed.
  (* Qed. *)

  (* end hide *)

  (** * Non-interference *)
  (** ** No synchronisation with non-members *)
  (** We now prove that in well-synchronized traces, actions performed by members of
       a tribe while in the section cannot synchronize with subsequent events performed
       by non members. Consider a both well-formed and well-synchronized trace [s]. *)

  Lemma see_synchronizeWith :
    forall s i1 i2,
      wellSynchronized s ->
      see s i1 i2 ->
      synchronizeWith s i1 i2.
  Proof.
    intros s i1 i2 H_ws H_see.
    induction H_see.
    - inversion H;subst.
      + constructor 1; now constructor 1 with t0.
      + assert (conflict  (Write l n v) (Read l n v)) as Hcfl by constructor.
        unfold wellSynchronized in H_ws.
        now apply H_ws with  (Write l n v)(Read l n v).
      + constructor 1;now constructor 2 with t0.
    - constructor 2 with y;auto.
  Qed.

  (** *** Visibility implies synchronisation. *)
  
  (** *** Join actions are blind.
        If a join performed at position [j] by a thread [t] see some position [i] then
        there exists a position [k < j] such that the action is perfomed by [t] or is a fork
        of [t], moreover either this position is [i] or [i] synchronizes with this position *)
  
  Lemma see_join : 
    forall s i j t t',
      seeImm s i j ->
      threadId_of (pi j s) == t ->
      action_of (pi j s) == Join t' ->
      (threadId_of (pi i s) == t \/ action_of (pi i s) == Fork t).
  Proof.
    intros s i j t t' seeImm_i_j Tj Aj.
    inversion seeImm_i_j; subst.
    - assert(Some t0 = Some t) by (rewrite <- H1, <- Tj; trivial).
      assert(t0 = t) by (auto with *).
      subst.
      left; trivial.
    - assert(Some (Read l n v) = Some (Join t')) by (rewrite <-Aj, <- H1; trivial).
      discriminate.
    - assert(Some t0 = Some t) by (rewrite <- H1, <- Tj; trivial).
      assert(t0 = t) by (auto with *).
      subst.
      right; trivial.
  Qed.

  Lemma see_sw_seeImm : 
    forall s,
      wellSynchronized s ->
      forall i j t t',
      see s i j ->
      threadId_of (pi j s) == t ->
      action_of (pi j s) == Join t' ->
      exists k,
        k <  j
        /\ (i = k \/ synchronizeWith s i k)
        /\ (threadId_of (pi k s) == t \/ action_of (pi k s) == Fork t).
  Proof.
    intros s h_ws i j t t' see_i_j Tj Aj.
    assert (clos_trans_n1 _ (seeImm s) i j) as Ha by auto using clos_trans_tn1.
    inversion Ha as [seeImm_i_j| k ? seeImm_k_j see_i_k]; subst.
    - assert (i < j) by ( eauto using synchronizeWithOrder, see_synchronizeWith).
      exists i; eauto using see_join.
    - assert (synchronizeWith s i k).
      {
        assert (see s i k) by now apply clos_tn1_trans.
        now apply see_synchronizeWith.
      }
      assert (k < j).
      {
        assert (see s k j) by now (apply t_step).
        eauto using synchronizeWithOrder, see_synchronizeWith.
      }
      exists k; eauto using see_join.
  Qed.
  
    (** *** No external synchronisation. *)
    (** While a section is opened, actions of a member of the tribe cannot synchronize
         with subsequent actions of non-members *)

 Lemma sw_in_tribe :
    forall s,
      wellFormed s ->
      wellSynchronized s ->
      forall p i j, 
        range s p i j ->
        forall k k', 
          i <= k <= j -> 
          i <= k' <= j ->                                  
          synchronizeWith s k k' ->
          forall t t',
            threadId_of (pi k s) == t ->
            threadId_of (pi k' s) == t' -> 
            tribe s p t -> tribe s p t'.
  Proof.
    intros s wellFormed_s wellSynchronized_s.
    inversion wellFormed_s.
    intros p i j range_p_i_j k k'; revert k.
    induction k' using lt_wf_ind.
    intros k int_i_j_k int_i_j_k' synchronizeWith_k_k'.
    induction synchronizeWith_k_k' as [k k' sw_k_k'|].
    - intros t t' Tk Tk' tribe_p_t.
      inversion sw_k_k' ; subst.
      + assert(Some t0 = Some t) by (rewrite <- Tk, <- H1; trivial).
        assert(t0 = t) by auto with *. 
        subst.
        assert(Some t' = Some t) by (rewrite <- Tk', <- H2; trivial).
        assert(t' = t) by auto with *. 
        subst.
        assumption.
      + assert(Some t' = Some t0) by (rewrite <- Tk', <- H2; trivial).
        assert(t' = t0) by auto with *. 
        subst.
        now apply forkInTribe with (i:=i) (j:=j) (k:=k) (t:=t).
      + assert(Some t0 = Some t) by (rewrite <- Tk, <- H1; trivial).
        assert(t0 = t) by auto with *. 
        subst.
        assert (tribeChildren s p t).
        { 
          inversion tribe_p_t; [ | assumption].
          exfalso. 
          assert (j < k') by eauto. auto with *. 
        }
        
        assert (exists k0 t0, i < k0 < k' /\ threadId_of (pi k0 s) == t0 /\ action_of (pi k0 s) == Fork t)
          as [k0 [t0 [Ha [Hb Hc]]]] by (eapply joined_in_tribe_forked_in; eauto).
        
        assert (i <= k0 <= j) by auto with *.
        assert (see s k0 k') by (eapply WF6; eauto).
        assert (tribe s p t0).
        {
          assert (father s t t0).
          exists k0; eauto.
          eapply tribeChildren_father_tribe; eauto.
        }
        assert (exists k1, k1 < k' /\ (k0 = k1 \/ synchronizeWith s k0 k1) /\
                           (threadId_of (pi k1 s) == t' \/ action_of (pi k1 s) == Fork t'))
          as [k1 [ lt_k1_k' [k1_hyp1 k1_hyp2]]]
            by eauto using see_sw_seeImm.
        assert (i <= k1 <= j).
        {
          destruct k1_hyp1; subst.
          intuition.
          assert (k0 < k1) by eauto using synchronizeWithOrder.
          auto with *.
        }
        destruct k1_hyp1; destruct k1_hyp2; subst.
        *assert (father s t t').
         exists k1; eauto.
         eapply tribeChildren_father_tribe; eauto.
        * apply forkInTribe with (i:=i) (j:=j) (k:=k1) (t:=t0); auto.
        * apply H with (m:=k1) (k:=k0) (t:=t0); try assumption.
        * assert (exists t1, threadId_of (pi k1 s) == t1) 
            as [t1 Ht1].
            {
              assert(k1<length s).
              eapply lift_nth_error_defined_left. 
              exists (Fork t'). 
              apply H10.
              eauto with *.
            }
          apply forkInTribe with (i:=i) (j:=j) (k:=k1) (t:=t1); eauto.
      + 
        apply open_in_tribe with (i:=i) (j:=j) (k:=k') (p':=p'); auto.
    - intros t t' HTx HTy HTribe.
      assert (exists t0, threadId_of(pi y s) == t0) as [t0 HT0]. 
      {
        eapply synchronizeWith_exists_event with (s:=s); eauto.
      }
      assert (i <= y <= j).
      {
        assert (x < y) by
            (inversion wellFormed_s;
             now apply synchronizeWithOrder with (s:=s)).
        assert (y < z) by
            (inversion wellFormed_s; now apply synchronizeWithOrder with (s:=s)).
        auto with *.
      }
      apply IHsynchronizeWith_k_k'2 with (t:=t0); try assumption.
      apply IHsynchronizeWith_k_k'1 with (t:=t); try assumption.
      intros.
      assert (m < z).
      {
        assert (y < z) by (inversion wellFormed_s; now apply synchronizeWithOrder with (s:=s)).
        auto with *.
      }
      apply H with (m:=m) (k:=k) (t:=t1); try assumption.
  Qed.
(*
  Lemma sw_in_tribe :
    forall s,
      wellFormed s ->
      wellSynchronized s ->
      forall p i j, 
        range s p i j ->
        forall k k', 
          i <= k <= j -> 
          i <= k' <= j ->                                  
          synchronizeWith s k k' ->
          forall t t',
            threadId_of (pi k s) == t ->
            threadId_of (pi k' s) == t' -> 
            tribe s p t -> tribe s p t'.
  Proof.
    intros s wellFormed_s wellSynchronized_s.
    inversion wellFormed_s.
    intros p i j range_p_i_j k k'; revert k.
    induction k' using lt_wf_ind.
    intros k int_i_j_k int_i_j_k' synchronizeWith_k_k'.
    induction synchronizeWith_k_k' as [k k' sw_k_k'|].
    - intros t t' Tk Tk' tribe_p_t.
      inversion sw_k_k' ; subst.
      + assert(Some t0 = Some t) by (rewrite <- Tk, <- H1; trivial).
        assert(t0 = t) by intuition. 
        subst.
        assert(Some t' = Some t) by (rewrite <- Tk', <- H2; trivial).
        assert(t' = t) by intuition. 
        subst.
        assumption.
      + assert(Some t' = Some t0) by (rewrite <- Tk', <- H2; trivial).
        assert(t' = t0) by intuition. 
        subst.
        now apply forkInTribe with (i:=i) (j:=j) (k:=k) (t:=t).
      + assert(Some t0 = Some t) by (rewrite <- Tk, <- H1; trivial).
        assert(t0 = t) by intuition. 
        subst.
        assert (tribeChildren s p t).
        { 
          inversion tribe_p_t; [ | assumption].
          exfalso. 
          assert (j < k') by eauto. intuition. 
        }
        
        assert (exists k0 t0, i < k0 < k' /\ threadId_of (pi k0 s) == t0 /\ action_of (pi k0 s) == Fork t)
          as [k0 [t0 [Ha [Hb Hc]]]] by (eapply joined_in_tribe_forked_in; eauto).
        
        assert (i <= k0 <= j) by intuition.
        assert (see s k0 k') by (eapply WF6; eauto).
        assert (tribe s p t0).
        {
          assert (father s t t0).
          exists k0; eauto.
          eapply tribeChildren_father_tribe; eauto.
        }
        assert (exists k1, k1 < k' /\ (k0 = k1 \/ synchronizeWith s k0 k1) /\
                           (threadId_of (pi k1 s) == t' \/ action_of (pi k1 s) == Fork t'))
          as [k1 [ lt_k1_k' [k1_hyp1 k1_hyp2]]]
            by eauto using see_sw_seeImm.
        assert (i <= k1 <= j).
        {
          destruct k1_hyp1; subst.
          intuition.
          assert (k0 < k1) by eauto using synchronizeWithOrder.
          intuition.
        }
        destruct k1_hyp1; destruct k1_hyp2; subst.
        *assert (father s t t').
         exists k1; eauto.
         eapply tribeChildren_father_tribe; eauto.
        * apply forkInTribe with (i:=i) (j:=j) (k:=k1) (t:=t0); auto.
        * apply H with (m:=k1) (k:=k0) (t:=t0); try assumption.
        * assert (exists t1, threadId_of (pi k1 s) == t1) 
            as [t1 Ht1] by 
                (assert(k1<length s) by (eapply lift_nth_error_defined_left; exists (Fork t'); apply H10);
                 firstorder using nth_error).
          apply forkInTribe with (i:=i) (j:=j) (k:=k1) (t:=t1); eauto.
      + 
        apply open_in_tribe with (i:=i) (j:=j) (k:=k') (p':=p'); auto.
    - intros t t' HTx HTy HTribe.
      assert (exists t0, threadId_of(pi y s) == t0) as [t0 HT0]. 
      {
        eapply synchronizeWith_exists_event with (s:=s); eauto.
      }
      assert (i <= y <= j).
      {
        assert (x < y) by
            (inversion wellFormed_s;
             now apply synchronizeWithOrder with (s:=s)).
        assert (y < z) by
            (inversion wellFormed_s; now apply synchronizeWithOrder with (s:=s)).
        intuition.
      }
      apply IHsynchronizeWith_k_k'2 with (t:=t0); try assumption.
      apply IHsynchronizeWith_k_k'1 with (t:=t); try assumption.
      intros.
      assert (m < z).
      {
        assert (y < z) by (inversion wellFormed_s; now apply synchronizeWithOrder with (s:=s)).
        intuition.
      }
      apply H with (m:=m) (k:=k) (t:=t1); try assumption.
  Qed.
*)
  (** * No conflict *)
  
  (** As a corollary of the previous lemma we can state that while a section is opened
        actions of a member of the tribe cannot conflict with subsequent actions of 
        non-members. *)
  
  Theorem noConflictOutside : (* rightConflict *)
    forall s,
      wellFormed s ->
      wellSynchronized s ->
      forall p i j (Hp : range s p i j)
             k1 (Hk1 : i <= k1 <= j)
             k2 (Hk2 : i <= k2 <= j)
             t1 a1 t2 a2,
        k1 < k2 ->
        threadId_of (pi k1 s) == t1 ->
        threadId_of (pi k2 s) == t2 ->
        action_of (pi k1 s) == a1 ->
        action_of (pi k2 s) == a2 ->
        tribe s p t1 -> 
        conflict a1 a2  ->
        tribe s p t2.
  Proof.
    intros.
    eapply sw_in_tribe with (k := k1) (k':=k2); eauto.
  Qed.
      
  Ltac synchronizeWith_inequalities :=
    match goal with 
        H0 : synchronizeWith ?S ?I ?J |- ?I < length ?S  => 
        now apply synchronizeWithInL with J
      | H0 : synchronizeWith ?S ?I ?J |- ?J < length ?S  => 
        now apply synchronizeWithIn with I
    end.
  
  Hint Extern 4 (?I < ?J) => synchronizeWith_inequalities : myresolve.
 
End Make.
