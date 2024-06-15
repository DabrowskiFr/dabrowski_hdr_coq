Require Import List Arith.
Require Import sections.lifo.Prelude.
Require Import sections.common.GenericTrace.
Require Import sections.traces.Trace.
Require Import sections.traces.Trace_Basics_projection.
Require Import sections.traces.Trace_Basics_occurences.
Require Import sections.traces.Trace_Basics_range.
Require Import sections.traces.Trace_Basics_father.
Require Import sections.traces.Trace_Basics_owns.

Require Import Lia. 

Module Make ( Perm : MiniDecidableSet )
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T )
            ( Tr : Trace.T Perm Address T V)
            ( P : Proj Perm Address T V Tr)
            ( O : OccurencesT Perm Address T V Tr P)
            ( F : FatherT Perm Address T V Tr P O) 
            ( OW : OwnsT Perm Address T V Tr P O)
            ( R : RangeT Perm Address T V Tr P O).

  Import Tr  P O F OW R.
  
   (** ** tribe *)

  Hint Resolve owns_s_se : owns.   
  Hint Resolve owns_se_s : owns.
  Hint Resolve range_s_se : range.
  Hint Resolve father_s_se : father.

  (** *** s_se *)

  Fact tribeChildren_s_se : 
    forall s p t e, 
      tribeChildren s p t -> 
      tribeChildren (s • e) p t.
  Proof.
    intros s p t e h_tribeChildren.
    induction h_tribeChildren.
    - destruct (range_s_se s p i j e H) as [[Ha Hb] | Hc].
      + constructor 1 with i j t0 k; eauto with nth_error owns.
      + assert (k < length s) by eauto with nth_error.
        constructor 1 with i (length s) t0 k; 
          solve [eauto with nth_error owns | auto with *].
    - assert (father (s • e) t' t0) by eauto with father.
      now constructor 2 with (t:=t0).
      Admitted.
  (* Qed. *)

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
    induction h_tribeChildren.
    - assert (k < length s).
      {
        assert (k < length (s • e)) by eauto with nth_error.
        destruct (Compare_dec.lt_eq_lt_dec k (length s)) as [ []|  ]; [assumption | subst |].
        elim (h_neq t0).
        destruct e.
        admit.
        admit.
        (* now autorewrite with nth_error in H2, H3; simpl in H2, H3; injection H2; injection H3; intros; subst. *)
        (* autorewrite with length in *; simpl in *.
        intuition. *)
      }
      destruct e as [t a].
      assert (a <> Open p).
      {
        assert (i < length s) by auto with *.
        contradict H5.
        assert (i = length s).
        {
          assert (action_of (pi i (s • (t,a))) == Open p) by now inversion H.
          assert (action_of (pi (length s) (s • (t,a))) == Open p) by admit.
              (* (subst; now autorewrite with nth_error). *)
          wellFormed_occurences (Open p).
        }
        auto with *.
      }
      assert (owns s p t0) by (apply owns_se_s with (t,a); congruence).
      nth_error_rewrite H2; nth_error_rewrite H3.
      destruct (range_se_s_neq_open s t a h_wf_occurences h_wf_open_close p i j H H5) as [[Hu Hv] | ].
      + now constructor 1 with i j t0 k.
      + constructor 1 with i (length s - 1) t0 k; auto with *.
      admit.
    - assert (father s t' t0) by (apply father_se_s with e; congruence).
      assert (tribeChildren s p t0).
      {
        assert (forall t', e <> (t', Fork t0)).
        {
          intros; intro; subst.
           destruct H as [k0 [Hu Hv]].
           assert (k0 < length s).
           {
            admit.
             (* destruct (Compare_dec.lt_eq_lt_dec k0 (length s)) as [[]|]; [assumption | subst |].
             autorewrite with nth_error in Hu; simpl in Hu; injection Hu; intros; subst.
             eapply h_wf_fork; autorewrite with nth_error; reflexivity.
             assert (k0 < length (s • (t'0, Fork t0))).
             eapply lift_nth_error_defined_left; eauto.
             autorewrite with length in H; simpl in H.
             intuition. *)
           }
           assert (length s < k0).
           {
            admit.
             (* eapply h_wf_fork. *)
             (* autorewrite with nth_error; reflexivity. *)
             (* eauto with nth_error. *)
           }
           auto with *.
        }
        now apply IHh_tribeChildren.
      }
      now constructor 2 with t0.
      Admitted.
  (* Qed. *)


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
        admit.
         (* (autorewrite with nth_error;auto). *)
      unfold wf_occurences in WF1;unfold occursAtMostOnce in WF1.
      assert (i = (length s)) as heq by now apply WF1 with (Open p).
      rewrite heq in HThreadOf.
      admit. 
      (* autorewrite  with nth_error in HThreadOf;auto. *)
    - 
      induction htc as [ i j t1 h_range h_owns |].
      + assert (action_of (pi (length s) (s • (t0, Open p))) == Open p) as h_pi_l by
        admit.
         (* (autorewrite with nth_error;auto). *)
        assert (action_of (pi i (s • (t0, Open p))) == Open p) as h_pi_i by (inversion h_range;auto).
        assert (k< length (s • (t0, Open p))) as h_lt_k by eauto with nth_error.
        replace (length (s • (t0, Open p))) with (S (length s)) in h_lt_k by 
          admit.
          (* (autorewrite with length; simpl;lia). *)
        assert (i < length s) as h_lt_i by lia.

        unfold wf_occurences in WF1.
        unfold occursAtMostOnce in WF1.
        assert (i = length s) as h_eq_i_l by now apply WF1 with (Open p).
        exfalso;lia.
      + destruct (eq_nat_dec t1 t0) as [h_eq_t1t0 | h_neq_t1t0].
        * 
          assert (owns  (s • (t0, Open p)) p t0) as howns
          by admit.
            (* (constructor 1 with (length s);
            autorewrite with nth_error;auto). *)
          assert (t0<>t1) as hneq by now apply  tribeChildren_notOwner with  (s • (t0, Open p)) p.
         
          intuition.
        * apply IHhtc;auto.
        Admitted.
  (* Qed. *)

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
    intros s t p HWFOcc t' H.
    induction H; intros.
    - assert (i = length s); subst.
      {
        assert (action_of (pi i (s • (t, Open p))) == Open p) by (inversion H; assumption).
        assert (action_of (pi (length s) (s • (t, Open p))) == Open p) 
               by admit. 
                (* (autorewrite with nth_error; trivial). *)
        apply HWFOcc with (a:=Open p); auto.
      }
      assert ( k <= length s).
      {
        assert (j < length (s • (t,Open p))) by (eapply range_j_lt_s; eauto).
        assert (j < length s + 1) by 
          admit. 
          (* (autorewrite with length in *; simpl in *; trivial). *)
        auto with *.
      }
      auto with *.
    - assumption.
  Admitted.
    (* Qed. *)
  
  Fact tribeOpen_single :
  forall s t p (HWFOcc : wf_occurences (s • (t, Open p))) t',
    tribe (s • (t, Open p)) p t' <-> t = t'.
  Proof.
    intros s t0 p HWFOcc t'.
    assert (threadId_of (pi (length s) (s • (t0, Open p))) == t0) as Ha 
           by admit. 
            (* now autorewrite with nth_error. *)
    assert (action_of (pi (length s) (s • (t0, Open p))) == Open p) as Hb 
           by admit. 
           (* now autorewrite with nth_error. *)
    split; intros.
    - inversion H as [ Howns1 | ]. unfold wf_occurences, occursAtMostOnce in HWFOcc.
      + assert (owns (s • (t0, Open p)) p t0) as Howns2 by
               now (apply owns_cons with (i:=length s)).
        inversion Howns1 as [ _1 i _2 Hi]; inversion Howns2 as [ _3 i' _4 Hi']; subst.
        assert (i = i') as Heq by firstorder.
        assert (Some t0 = Some t') by (rewrite <- Hi, <- Hi', Heq; trivial).
        auto.
        admit.
      + exfalso; eapply tribeChildrenOpen_empty; eauto.
    - subst.
      constructor 1.
      assert (threadId_of (pi (length s) (s • (t', Open p))) == t') 
             by admit.
             (* (autorewrite with nth_error; trivial). *)
      assert (action_of (pi (length s) (s • (t', Open p))) == Open p) 
             by admit. 
             (* (autorewrite with nth_error; trivial). *)
      now apply owns_cons with (i := length s).
  Admitted.
        (* Qed. *)

  Ltac pi_simpl:=
    autorewrite with length in*; simpl in *; try(rewrite plus_comm, minus_plus in *);
    autorewrite with nth_error in *; trivial.

 Lemma wellFormed_close_in_tribe :
    forall s p t,
      wellFormed (s • (t, Close p)) -> tribe s p t.
  Proof.
    intros s p t H.
    constructor 1.
    inversion H as [ ? ? ? WFOpenClose _ _  _ ?].
    assert(action_of (pi (length s) (s • (t, Close p))) == Close p) as H' 
      by admit.
      (* pi_simpl. *)
    specialize(WFOpenClose (length s) p H').
    destruct WFOpenClose as [j [ Hj [ Haction Hthreadid] ] ].
    exists j.
    assert(threadId_of (pi (length s) (s • (t, Close p))) == t) as H'' by 
      admit. 
      (* pi_simpl. *)
    rewrite <- H''. rewrite Hthreadid at 1. 
    now rewrite ListBasics.nth_error_append_left. trivial.
    rewrite <- Haction.
    now rewrite ListBasics.nth_error_append_left.
    Admitted.
  (* Qed. *)

  Lemma wellFormedOpenFirst : 
    forall s t p, wellFormed (s • (t, Open p)) -> ~ occursIn s (Close p).
  Proof.
    intros s t0 p H.
    intro.
    assert (action_of (pi (length s) (s • (t0, Open p))) == Open p)
           by admit. 
           (* now autorewrite with nth_error. *)
    inversion H0; subst.
    inversion H.
    assert (action_of (pi i (s • (t0, Open p))) == Close p) by auto with nth_error.
    destruct (WF4 i p H2) as [i' [Hb [Hc Hd]]].
    assert (i' = length s) by
           now (apply WF1 with (a:= Open p)).
    subst.
    assert (i < length s) by eauto with nth_error.
    auto with *.
    Admitted.
  (* Qed. *)

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
        admit.
        admit.
        (* autorewrite with nth_error; trivial.
        autorewrite with nth_error; trivial. *)
      }
      auto with *.
    }
    inversion HTribe; subst.
    - inversion H; subst.
      assert (i < length s) by
             eauto with nth_error.
      assert (length s < i).
      {
          admit.
        (* apply WF_fork with (t0:=t).
        autorewrite with nth_error; trivial.
        assumption. *)
      }
      exfalso; auto with *.  
    - assert(tribe (s • (t', Fork t)) p t') as Htribe.
      {
        assert(threadId_of (pi (length s) (s • (t', Fork t))) == t') by 
          admit. 
            (* pi_simpl. *)
        assert(action_of (pi (length s) (s • (t', Fork t))) == Fork t) by 
          admit. 
          (* pi_simpl. *)
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
  (* Qed. *)
  Admitted.

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
    - admit.
      (* split; pi_simpl; try lia.
      assert (action_of(pi i (s • (t', Fork t))) == Open p) by (inversion HRange; eauto).
      destruct (Lt.le_or_lt i (length s)) as [H0|H0].
      + apply Lt.le_lt_or_eq in H0.
        destruct H0 as [H0 | H0].
        * trivial.
        * exfalso.
          assert (action_of (pi (length s) (s • (t', Fork t)))==Fork t) 
                 by (autorewrite with nth_error; trivial).
          subst.
          autorewrite with nth_error in *; simpl in *; discriminate.
       + assert( i >= length (s • (t', Fork t))) by  (autorewrite with length;simpl;omega).
         now rewrite ListBasics.nth_errorGeLength in H. 
    - pi_simpl. 
    - pi_simpl. *)
    Admitted.
  (* Qed. *)

  Lemma wf1 : 
    forall s t t', wf_fork (s • (t, Fork t')) -> t <> t'.
  Proof.
    intros; intro; subst.
    apply (Lt.lt_irrefl (length s)).
    apply H with (t:=t'); admit.
    (* autorewrite with nth_error; trivial. *)
  Admitted.
    (* Qed. *)

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
                 by admit. 
                 (* (autorewrite with nth_error; trivial). *)
          assert (k = length s) by now (apply HWFOcc with (a:=Fork t)).
          (* autorewrite with length. *)
          admit.
            (* simpl. lia. *)
        }
        subst.
        intuition.
      + assert (t0=t').
        {
          assert (father (s • (t', Fork t)) t t').
          {
            exists (length s).
            admit.
            (* autorewrite with nth_error; simpl; auto. *)
          }
          eauto using father_functionnal.
        }
        subst.
        assert (owns (s • (t', Fork t)) p t') by auto with owns.
        eapply tribeExcl; eauto.
        Admitted.
  (* Qed. *)

  Hint Resolve tribe_empty : tribe.




        

      
End Make.

Module Type TribeT (Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ) 
            ( Tr : Trace.T Perm Address T V)
            ( P : Proj Perm Address T V Tr)
            ( O : OccurencesT Perm Address T V Tr P)
            ( F : FatherT Perm Address T V Tr P O) 
            ( OW : OwnsT Perm Address T V Tr P O)
            ( R : RangeT Perm Address T V Tr P O).
  Include (Make Perm Address T V Tr P O F OW R).
End TribeT.
