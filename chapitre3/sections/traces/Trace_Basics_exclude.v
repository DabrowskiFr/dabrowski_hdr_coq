Require Import List Arith.
Require Import sections.lifo.Prelude sections.lifo.Nth sections.lifo.In.
Require Import sections.common.GenericTrace.
Require Import sections.traces.Trace.
Require Import sections.traces.Trace_Basics_projection.
Require Import sections.traces.Trace_Basics_occurences.
Require Import sections.traces.Trace_Basics_range.
Require Import sections.traces.Trace_Basics_father.
Require Import sections.traces.Trace_Basics_owns.
Require Import sections.traces.Trace_Basics_tribe.
Require Import sections.traces.Trace_Basics_wellFormed.
Require Import sections.lifo.Mem.
Require Import sections.lifo.DropTakeWhile.
Require Import sections.lifo.ListBasics.

Require Import sections.lifo.Length.
Require Import sections.lifo.Firstn_skipn.


Require Import Lia.
Module Make ( Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ) 
            ( Tr : Trace.T Perm Address T V)
            (*( TrTH : Trace.Th Perm Address T V)*)
            ( P : Proj Perm Address T V Tr)
            ( O : OccurencesT Perm Address T V Tr P)
            ( F : FatherT Perm Address T V Tr P O) 
            ( OW : OwnsT Perm Address T V Tr P O)
            ( R : RangeT Perm Address T V Tr P O)
            ( Tribe : TribeT Perm Address T V Tr P O F OW R).

  Import Tr P O F OW R Tribe.

  (** pending *)
  
  Lemma pending_se_s : 
    forall s t a,
      wf_occurences (s • (t,a)) ->
      wf_open_close (s • (t,a)) ->
      forall p,
      pending (s • (t,a)) p -> a <> Open p -> pending s p.
  Proof.
    intros s t a h_wf_occurences h_wf_open_close p h_pending h_neq.
    unfold pending.
    destruct h_pending as [[i h_i] h_not_occursIn].

    autorewrite with length in h_i; simpl in h_i.
    replace (length s + 1 - 1) with (length s) in h_i by lia. 
    split.
    - (exists i).
      destruct (range_se_s_neq_open _ _ _ h_wf_occurences h_wf_open_close p i (length s) h_i h_neq).
      + elim h_not_occursIn; exists (length s); destruct H; eauto with nth_error.
      + tauto.
    - contradict h_not_occursIn.
      eauto with occurences.
  Qed.

  (** - a section [p] pending in [s] is also pending in [s • (t,a)] if [a <> Close p] *)
  Lemma pending_s_se : 
    forall s t a,
      wf_occurences (s • (t,a)) ->
      wf_open_close (s • (t,a)) ->
      forall p, pending s p -> a <> Close p -> pending (s • (t,a)) p.
  Proof.
    intros s t a h_wf_occurences h_wf_opend_close p h_pending h_neq.
    destruct h_pending as [[i h_i] h_not_occursIn].
    split.
    - (exists i).
      destruct (range_s_se s p i (length s - 1) (t,a) h_i).
      destruct H.
      contradict h_not_occursIn.
      destruct s; simpl in *.
      + inversion h_i; subst; autorewrite with nth_error in Hi; discriminate.
      + replace (length s - 0) with (length s) in * by lia.
      exists (length s).
      assert (length s  < length (p0::s)) by intuition.
      eauto with nth_error.
      + autorewrite with length; simpl.
      now replace (length s + 1 - 1) with (length s) by lia.
    - contradict h_not_occursIn; eauto with occurences.
    Qed.
  
  (** - a section freshly opened is pending *)
  Lemma pending_open : 
    forall  s t p,
      wf_occurences (s • (t,Open p)) ->
      wf_open_close (s • (t,Open p)) ->
      pending (s • (t, Open p)) p.
  Proof.
    intros s t p h_wf_occurences h_wf_open_close.
    assert (~ occursIn (s • (t,Open p)) (Close p)).
    { 
      intro h_occursIn.
      inversion h_occursIn as [i ? h_i]; subst.
      assert (exists j, j < i /\ action_of (pi j (s • (t, Open p))) == Open p) as [j [h_a h_b]].
      {
        destruct h_wf_open_close with i p as [j [h_a [h_b _]]]; try assumption.
        exists j; tauto.
      }
      assert (action_of (pi (length s) (s • (t,Open p))) == Open p)
        by (autorewrite with nth_error; reflexivity).
      replace j with (length s) in * by wellFormed_occurences (Open p).
        assert (i < length (s • (t,Open p))) by eauto with nth_error.
        autorewrite with length in H0; simpl in H0; auto with *.
    }
    split.
    - (exists (length s)).
      constructor 2; [autorewrite with nth_error; reflexivity | assumption].
    - assumption.
    Qed.

  Lemma range_last_se_pending_s :
    forall s e p i,
      wellFormed (s • e) ->
      range (s • e) p i (length s) -> i <> length s -> pending s p.
  Proof.
    intros s e p i h_wf h_range h_neq.
    assert (i < length (s • e)) as Hi_se.
    {
      inversion h_range; subst;
      eapply lift_nth_error_defined_left;
      exists(Open p); eassumption.
    }
    assert (i < length s) as Hi_s 
           by (autorewrite with length in * ; simpl in *; intuition).
    assert (action_of (pi i (s • e)) == Open p) as Ha_i_se
           by now inversion h_range.
    assert (action_of (pi i s) == Open p) as Ha_i_s
           by (erewrite <- lift_nth_error_append_left; eassumption).
    assert (~ occursIn s (Close p)).
    {
      intro H.
      inversion h_range as [ ? Haction ?| ? H1 H2 H3 H4]; subst.
      - inversion H as [i0 ?]; subst.
        assert(i0 < length s) as Hi0 by eauto with nth_error.
        assert(i0 = length s) as Hi0_eq.
        {
          assert (action_of (pi i0 (s • e)) == Close p)  by eauto with nth_error.
          wellFormed_occurences (Close p).
        }
        rewrite Hi0_eq in Hi0.
        elim (Lt.lt_irrefl (length s) Hi0).
      - elim H2.
        now apply occursIn_s_se.
    }
    split.
    exists i.
    constructor 2; assumption.
    assumption.
  Qed.

  Lemma pending_range_last :
    forall s p e,
      pending s p -> exists i, range (s • e) p i (length s).
  Proof.
    intros s p e H.
    inversion H as [[i Hrange] H2].
    inversion Hrange as [ ? Haction ? | ? Haction Hoccurs]; subst;
    assert(i < length s) as Hi_len by eauto with nth_error.
    - exists i.
      constructor.
      + now rewrite lift_nth_error_append_left.
      + contradict H2.
      eauto with *.
    - exists i.
      assert(exists t', threadId_of(pi i s) == t') as Ht'.
      {
        assert(exists y,pi i s==y) as Hy 
          by (now apply ListBasics.nth_error_lt_defined).
        destruct Hy as [ [t' a'] Ht'a'].
        exists t'.
        rewrite Ht'a'.
        trivial.
      }
      destruct Ht' as [t' Ht'].
      destruct(occursIn_dec (s • e) (Close p)) as [Ho | Ho].
      + inversion Ho as [i0 ? Haction_i0]; subst.
        assert(action_of (pi i (s • e)) == Open p) 
          by (now rewrite lift_nth_error_append_left).
        assert(i0 = length s).
        {
          destruct(lt_eq_lt_dec i0 (length s)) as [[Hi0|Hi0]|Hi0].
          - contradict Hoccurs.
            assert(action_of(pi i0 s)==Close p) by 
                (now rewrite lift_nth_error_append_left in Haction_i0).
            econstructor; eassumption.
          - trivial.
          - assert(i0>=length (s • e)) by 
                (autorewrite with length; simpl; auto with *).
            assert(action_of (pi i0 (s • e)) = None) as Hnone by
                (now rewrite ListBasics.nth_errorGeLength).
            rewrite Hnone in Haction_i0.
            discriminate.
        }
        subst.
        now constructor.
      + assert(action_of (pi i (s • e)) == Open p) 
          by (now rewrite lift_nth_error_append_left).
        assert(length s = length(s • e) - 1) as Hs
          by (autorewrite with length; simpl; auto with *).
        rewrite Hs.
        now constructor 2.
        Qed.
  
  Lemma pending_range_last2 : 
    forall s p, 
      pending s p ->
      exists i, range s p i (length s - 1).
  Proof.
    intros s p H.
    inversion H as [[i Hrange] H2].
    exists i.
    trivial.
  Qed.

  (** exclude *)
  
  Lemma exclude_nil : forall t p, ~ exclude nil p t.
  Proof.
    intros t p h_exclude.  
    destruct h_exclude.
    inversion H.
    inversion H1.
    inversion H3; subst.
    destruct x; discriminate.
    destruct x; discriminate.
  Qed. 
  
  Lemma exclude_se_s_not_open_p : 
    forall s p t (HWF : wellFormed (s • (t,Open p))) p' t',
      exclude (s • (t,Open p)) p' t' -> p <> p' -> exclude s p' t'. 
  Proof.
    intros.
    inversion H.
    constructor.
    inversion HWF.
    apply pending_se_s with (t:=t0) (a:=Open p).
    assumption.
    assumption.
    assumption.
    intro.
    injection H3; intuition.
    intro; elim H2.
    apply tribe_s_se.
    assumption.
  Qed.

  Lemma exclude_se___s_not_open : 
    forall s p t t' a (HWF : wellFormed (s •(t,a))), 
      exclude (s • (t,a)) p t' -> a <> Open p -> exclude s p t'. 
  Proof.
    intros s p t0 t' a HWF H HnotOpen.
    destruct H as [Hpending Htribe].
    split.
    - (* pending *)
      destruct Hpending as [[i Hrange] HnotOccursIn].
      assert(not(occursIn s (Close p))) by (contradict HnotOccursIn; 
                                            now apply occursIn_s_se).
      inversion Hrange as [ ? Haction ? | ? Haction Hoccurs]; subst.
      + contradict HnotOccursIn.
        eauto with *.
      + assert(i < length s).
        {
          destruct(lt_eq_lt_dec i (length s)) as [[Hi|Hi]|Hi].
          - trivial.
          - subst. 
            rewrite ListBasics.nth_error_append_cons_eq in Haction.
            inversion Haction.
            contradict HnotOpen.
            trivial.
          - assert(i>=length (s • (t0, a))) 
              by (autorewrite with length; simpl;auto with *).
            rewrite ListBasics.nth_errorGeLength in Haction; trivial.
            discriminate.
        }
        assert(action_of (pi i s) == Open p) by
            (now rewrite lift_nth_error_append_left in Haction).
        assert(range s p i (length s - 1)) by (now constructor 2).
        constructor; eauto.
    - (* tribe *) 
      contradict Htribe.
      now apply tribe_s_se.
      Qed.

  Lemma exclude_s_open_not_owner :
    forall s p t,
      wellFormed (s • (t,Open p)) ->
      forall t',
        t' <> t -> exclude (s • (t, Open p)) p t'.
  Proof.
    intros s p t h_wf_formed t' h_neq.
    inversion h_wf_formed.
    split; eauto using pending_open, notInTribe_s_open_not_owner.
  Qed.

  Lemma notTribes_s_se_not_open_fork : 
    forall s t t1 a (HWF : wellFormed (s• (t1,a))) p ,
      ~ tribe s p t -> 
      a <> Open p ->
      (forall t', (t1,a) <> (t', Fork t)) ->
      ~ tribe (s • (t1,a)) p t.
  Proof.
    intros s t t1 a HWF p  Hntr Hnop Ht'.
    contradict Hntr.
    inversion HWF.
    eapply tribe_se_s_not_open_fork;eauto.
    contradict Hnop.
    inversion Hnop;auto.
  Qed.

  Lemma outerExclude_s_se_not_open_fork :
    forall s t t1 a (HWF : wellFormed (s• (t1,a))) p ,
      outerExclude s p t -> 
      (forall p', a <> Open p') ->
      a <> Close p ->
      (forall t', (t1,a) <> (t', Fork t)) ->
      outerExclude (s • (t1,a)) p t.
  Proof.
    intros s t0 t1 a HWF p Hout Hnop Hncl Hnfor.
    inversion Hout as [Hexl Hlp].
    destruct Hexl as [Hpend Hntr].
    constructor.
    - unfold exclude in *.
      split.
      + inversion HWF.
        apply pending_s_se;auto. 
      + apply notTribes_s_se_not_open_fork;auto.
    - intros p' Hexcl2 Hnpp'.
      assert (exclude s p' t0) as Hexls by now apply exclude_se___s_not_open with t1 a.
      assert  (occursAfter s (Open p) (Open p')) as Hocaft by now apply (Hlp p').
      inversion Hocaft;subst.
      apply occursAfter_cons with i j;auto with nth_error.
  Qed.

  Lemma outerExclude_s_se_closed :
    forall s p t t1,
      outerExclude s p t ->
      ~ outerExclude (s • (t1,(Close p))) p t.
  Proof.
    intros s p t t1 Hout.
    inversion Hout as [Hexl Hlp].
    destruct Hexl as [Hpend Hntr].
    intro Hout2.
    inversion Hout2 as [Hexl2 Hlp2].
    unfold exclude in Hexl2.
    destruct Hexl2 as [Hpend2 Hntr2].
    unfold pending in Hpend2.
    destruct Hpend2 as [ Hr Hnocc2].
    subst.
    contradict Hnocc2.
    constructor 1 with (length s).
    autorewrite  with nth_error; auto.
  Qed.

  Lemma outerExclude_open : 
    forall s p t,
      outerExclude s p t -> exists i, action_of (pi i s) == Open p.
  Proof.
    intros s p t0 H.
    inversion H as [ Hexclude HoccursAfter ].
    destruct Hexclude as [ Hpend Htribe ].
    inversion Hpend as [ Hrange ].
    destruct Hrange as [i Hi].
    inversion Hi; subst; eauto.
  Qed.

  Fact outerExclude_not_in_tribe : 
    forall s p t,
      outerExclude s p t -> ~ tribe s p t.
  Proof.
    intros s p t0 h_outerExclude. 
    inversion h_outerExclude.
    unfold exclude in H0.
    destruct H0.
    assumption.
  Qed.

  Lemma tribeChildren_live_after_open : 
    forall s, 
      wellFormed s ->
      forall p t,
        tribeChildren s p t ->
        forall i k ,
          action_of (pi i s) == Open p ->
          threadId_of (pi k s) == t ->
          i < k.
  Proof.
    intros s h_wf p t h_tc.
    assert (wf_fork s) as h_wf_fork by now inversion h_wf.
    induction h_tc.
    - intros i0 k0 h_open_p h_k_0_tid.
      assert (i0 = i) by (inversion H; subst; wellFormed_occurences (Open p)).
      assert (k < k0) by (eapply h_wf_fork; eauto).
      auto with *.
    - intros i0 k0 h_open_p h_k_0_tid.
      destruct H as [k [Ha Hb]].
      assert (i0 < k) by eauto.
      assert (k < k0) by (eapply h_wf_fork; eauto).
      auto with *.
  Qed.

  (** * Auxiliary lemma for outer_exclude_dec *)

  Lemma inFind :
    forall (A:Type) (l:list A) a f,
      In a l ->
      f a = true ->
      exists b,
          List.find f l == b /\ f b =true.
  Proof.
    induction l.
    - intros a f H H1.
      inversion H.
    - intros a0 f H H1.
      inversion H.
      + subst.
        exists a0.
        simpl.
        rewrite H1.
        auto.
      + simpl.
        case_eq (f a).
        * intro Hfa.
          exists a.
          auto.
        * intro.
          now apply (IHl a0).
  Qed.

  Lemma findIn :
    forall (A:Type) (l:list A) f a,
       List.find f l == a ->
       In a l.
  Proof.
    induction l.
    - intros f a H.
      inversion H.
    - intros f a0 H.
      inversion H as [H1].
      case_eq (f a).
      + intro fa.
        rewrite fa in H1. inversion H1. subst.
        constructor. auto.
      + intro fa.
        rewrite fa in H1.
        constructor 2.
        now apply IHl with (f:=f)(a:=a0).
  Qed.

  Definition eventOwnerf (s : Tr)(p:Perm.t) : option Event.t := 
    List.find (fun x => let a0 := (snd x) in
                          if (eq_action_dec a0 (Open p))then true else false
              ) s.

  Definition ownerf (s : Tr)(p:Perm.t) : option threadId :=
    match (eventOwnerf s p) with
      | Some (t,a) => Some t
      | None => None
    end.

    Lemma In_nth_error:
    forall (A:Type)(l:list A)(a:A),
      In a l -> exists n, nth_error l n = Some a.
  Proof.
    induction l as [|x xs IH]; intros a Hin.
    - inversion Hin.
    - inversion Hin.
      + subst. exists 0. trivial.
      + specialize (IH _ H). 
        destruct IH as [n Hnth].
        exists(S n).
        trivial.
  Qed.

  Lemma ownsEventOwnerRev :
    forall s t p,
      wellFormed s ->
      owns s p t ->
      eventOwnerf s p == (t,Open p).
  Proof.
    intros s t0 p Hwf H.
    inversion H;subst.
    unfold ownerf.
    set (f:=(fun x:Event.t => let a0 := (snd x) in
                              if (eq_action_dec a0 (Open p))then true else false
        )) .
    assert (exists e, List.find f s == e /\ f e = true) as Hin.
    {
      apply inFind with (l:=s)(f:=f)(a:=(t0,Open p)).
      - assert(pi i s == (t0, Open p)) by 
        (now apply lift_pair_surjective).
        eapply nth_errorIn.
        eassumption.
      - unfold f.
        simpl.
        case_eq (eq_action_dec (Open p) (Open p)). 
        + auto.
        + intros n H0. intuition.
    }
    destruct Hin as [[t1 a] [Hfind Hf]].
    assert (a = Open p) as Hop.
    {
      unfold f in Hf.
      simpl in Hf.
      destruct (eq_action_dec a (Open p)).
      - assumption.
      - contradict Hf;auto.
    }
    subst.
    assert (In (t1,Open p) s) as Hin1 by now apply findIn with f.
    inversion Hwf.
    assert (exists j, pi j s == (t1,Open p)) as [j Hpj] by now apply In_nth_error.
    assert (action_of (pi j s) == Open p) as Hpjop by (rewrite Hpj;auto).
    assert (i =j) as Heqij. wellFormed_occurences (Open p). subst.
    assert (t1 = t0) as Heqt1t0.
    {
      rewrite Hpj in HThreadOf.
      simpl in *.
      inversion HThreadOf.
      auto.
    }
    subst.
    unfold eventOwnerf.
    
    destruct s.
    - auto.
    - auto.
    Qed.
  
   Lemma ownsOwnerRev :
    forall s t p,
      wellFormed s ->
      owns s p t ->
      ownerf s p == t.
   Proof.
     intros s t p H H0.
     unfold ownerf.
     assert (eventOwnerf s p == (t,Open p)) as H1 by now apply ownsEventOwnerRev. 
     rewrite H1.
     auto.
   Qed.

   Import ListNotations.

   Definition getSection (s : Tr) (p : Perm.t) : Tr :=
     let s' := dropWhile (fun x =>  if (eq_action_dec (snd x) (Open p)) then false else true ) s in
       takeWhile (fun x => if (eq_action_dec (snd x) (Close p)) then false else true) s'.
   
   
   Definition getTribeChild (tribe:list threadId)(e:Event.t) : list threadId :=
     match snd e with 
       | Fork t =>List.map (fun _=>t) (List.filter (beq_nat (fst e)) tribe)
       | _ => []
     end.

   Definition getTribeChild' (tribe:list threadId)(e:Event.t) : list threadId :=
     match snd e with 
       | Fork t => if mem Peano_dec.eq_nat_dec (fst e) tribe 
                   then [t]
                   else []
       | _ => []
     end.

   Lemma getTribeChildCons:
     forall tribe tid e, 
       getTribeChild (tid::tribe) e = 
       (getTribeChild [tid] e) ++ (getTribeChild tribe e).
   Proof.
     intros tribe tid e .
     unfold getTribeChild. 
     destruct e as [t a]; destruct a; simpl; trivial.
     destruct(Nat.eqb t tid).
     - rewrite App.app_cons, map_app. trivial.
     - trivial.
   Qed.

   Lemma getTribeChild'Cons:
     forall tribe tid e, 
       NoDup(tid::tribe) -> 
       getTribeChild' (tid::tribe) e = 
       (getTribeChild' [tid] e) ++ (getTribeChild' tribe e).
   Proof.
    intros tribe0 tid e H_nodup.
    destruct e as [t a]; destruct a; simpl; trivial.
    inversion H_nodup; subst; clear H_nodup.
    case_eq (Nat.eqb t tid); intro.
    - unfold getTribeChild'; simpl.
      apply Nat.eqb_eq in H; subst.
      destruct (Nat.eq_dec tid tid).
      + case_eq (mem Nat.eq_dec tid tribe0).
        * intro.
          apply inMemEq in H.
          elim H1.
          assumption.
        * intro.
          rewrite append_nil_left_neutral.
          reflexivity.
      + elim n.
        reflexivity.
    - unfold getTribeChild'; simpl.
      assert (t <> tid).
      {
        intro.
        apply Nat.eqb_eq in H0.
        rewrite H in H0.
        discriminate.
      }
      destruct (Nat.eq_dec tid t).
      + congruence.
      + case_eq (mem Nat.eq_dec t tribe0).
        * intro.
          reflexivity.
        * reflexivity.
Qed.

   Lemma getTribeChildEq: 
     forall tribe e, 
       NoDup tribe -> 
       getTribeChild tribe e = 
       getTribeChild' tribe e.
   Proof.
     intros tribe e H; destruct e as [tid a].
     induction H.
     - unfold getTribeChild, getTribeChild'. 
       destruct a; trivial.
     - assert(NoDup(x::l)) by (now constructor 2).
       rewrite getTribeChildCons.
       rewrite getTribeChild'Cons; trivial.
       f_equal.
       + unfold getTribeChild, getTribeChild'. 
         destruct a; trivial.
         simpl.
         case_eq(eq_nat_dec x tid); intros Heq _.
         * assert(Nat.eqb tid x = true) as Hbeq by (now apply beq_nat_true_iff).
           rewrite Hbeq.
           trivial.
         * assert(Nat.eqb tid x = false) as Hbeq by (apply beq_nat_false_iff; intuition).
           rewrite Hbeq.
           trivial.
       + trivial.
   Qed.
         
   Lemma getTribeChildApp:
     forall tribe1 tribe2 e, 
       getTribeChild (tribe1++tribe2) e = 
       getTribeChild tribe1 e ++ getTribeChild tribe2 e.
   Proof.
     induction tribe1 as [|t tribe1 IH]; intros tribe2 e; destruct e as [tid a].
     - unfold getTribeChild. 
       rewrite app_nil_l; destruct a; simpl; trivial;
       rewrite app_nil_l; trivial.
     - rewrite <- app_comm_cons.
       rewrite getTribeChildCons. rewrite getTribeChildCons with (tribe:=tribe1).
       rewrite IH.
       rewrite app_assoc.
       trivial.
   Qed.
   
   (* Shall we extract a getTribeChildren function? *)
   Definition getTribe  (s:Tr) (p:Perm.t) : list threadId :=
     match ownerf s p with
       | None => []
       | Some t => 
           let sp := getSection s p in
             let directChildren := flat_map (getTribeChild [t]) sp in 
               t::(fold_left (fun trb e =>(getTribeChild trb e)++trb) s directChildren )
     end.

    
   Definition getClose (e : Event.t) : list Perm.t :=
     match snd e with 
       | Close p => [p]
       | _ => []
     end.
   
   Definition getOpen (e : Event.t) : list Perm.t :=
     match snd e with 
       | Open p => [p]
       | _ => []
     end.
   
   Definition closed  (s : Tr) : list Perm.t := 
     fold_left (fun x e => (getClose e)++x) s [].
   
   Definition opened  (s : Tr) : list Perm.t := 
     fold_left (fun x e => (getOpen e)++x) s [].
   
   Definition isPending (s :Tr)(p:Perm.t):bool :=
     let closed := closed s in
       negb (mem Perm.eq_dec p closed).
   
   Definition pendingList (s : Tr ) : list Perm.t :=
     let closed := closed s in
       let opened := opened s in
         filter (isPending s) opened.

   Definition excludeList (s :Tr)(t:threadId) :=
     List.filter (fun p => negb (mem _ t (getTribe s p))) (pendingList s ).

   Definition outerExcludef (s :Tr)(t:threadId) :=
      List.hd_error (excludeList s t).

   
   Require Import Bool.

   Lemma memActionInMap :
     forall a s ,
       (mem eq_action_dec a (map snd s) = true ) <->
       exists i, action_of (pi i s) == a.
   Proof.
     intros a s. split; intro H.
     - apply inMemEq in H.
       apply in_map_iff in H.
       destruct H as [e [Ha He]].
       assert(exists i, nth_error s i  == e) as Hnth by now apply In_nth_error.
       destruct Hnth as [i Hnth].
       exists i.
       rewrite Hnth, <- Ha.
       trivial.
     - apply inMemEq.
       destruct H as [i Hi].
       apply lift_snd_inv in Hi.
       destruct Hi as [tid Htid].
        apply nth_errorIn in Htid.
       replace a with (snd (tid,a)) by auto.
       now apply in_map.
       Qed.

   Lemma fold_left_in_seed :
    forall (A B :Type) (s:list A) (l :list B) (f : A -> list B) (a:B)  ,
      In a l ->
      In a (fold_left (fun l1 e => (f e)++l1) s l).
   Proof.
     induction s.
     - intros l f a H.
       auto.
     - intros l f a0 H.
       simpl.
       apply IHs.
       apply in_or_app;right;assumption.
   Qed.

   Lemma fold_left_in_seed_gen :
    forall (A B :Type) (s:list A) (l :list B) (f : list B -> A -> list B) (a:B)  ,
      In a l ->
      In a (fold_left (fun l1 e => (f l1 e)++l1) s l).
   Proof.
     induction s.
     - intros l f a H.
       auto.
     - intros l f a0 H.
       simpl.
       apply IHs.
       apply in_or_app;right;assumption.
   Qed.

   Lemma fold_left_in_seed_inc :
    forall (A B :Type) (s:list A) (l l':list B) (f : A -> list B) (a:B)  ,
      In a l ->
      incl l l' -> 
      In a (fold_left (fun l1 e => (f e)++l1) s l').
   Proof.
     induction s.
     - intros l l' f a H.
       auto.
     - intros l l' f a0 H Hinc.
       simpl.
       apply IHs with l;auto.
       unfold incl in *.
       intros a1 Hin.
       rewrite in_app_iff.
       right;apply Hinc;auto.
   Qed.

   Lemma incl_app_ll :
     forall (A : Type) (l : list A) m n,
       incl m n ->
       incl (l++m) (l++n).
   Proof.
     intros.
     assert(incl m (l++n)) by now apply incl_appr.
     assert(incl l (l++n)) by (apply incl_appl; apply incl_refl).
     now apply incl_app.
   Qed.

   Lemma fold_left_in_seed_inc2 :
    forall (A B :Type) (s:list A) (l l':list B) (f : A -> list B) (a:B)  ,
      In a (fold_left (fun l1 e => (f e)++l1) s l) ->
      incl l l' -> 
      In a (fold_left (fun l1 e => (f e)++l1) s l').
   Proof.
     induction s.
     - intros l l' f a H Hinc.
       auto.
     - intros l l' f a0 H Hinc.
       simpl in *.
       apply IHs with (f a ++ l);auto.
       now apply incl_app_ll.
   Qed.

   Lemma fold_left_in_seed_inc2_gen :
    forall (A B :Type) (s:list A) (l l':list B) (f :list B-> A -> list B) (a:B)  ,
      (forall a l l', incl l l' -> incl (f l a) (f l' a)) ->
      In a (fold_left (fun l1 e => (f l1 e)++l1) s l) ->
      incl l l' -> 
      In a (fold_left (fun l1 e => (f l1 e)++l1) s l').
   Proof.
     induction s as [| e s IH]; intros l l' f a Hmonotonic H Hinc.
     - auto.
     - simpl in *.
       assert(incl (f l e ++ l) (f l' e ++ l')).
       {
         apply incl_app.
         apply incl_appl.
         now apply Hmonotonic.
         now apply incl_appr.
       }
       eapply IH; eassumption.
   Qed.

   Lemma fold_left_in_fold :
    forall (A B :Type)(s:list A)  (l :list B)(f : A -> list B) (a:B)  ,
      In a (fold_left (fun l1 e => (f e)++l1) s nil) ->
      In a (fold_left (fun l1 e => (f e)++l1) s l).
   Proof.
     induction l.
     - auto.
     - intros f a0 H.
       assert (In a0 (fold_left (fun (l1 : list B) (e : A) => f e ++ l1) s l)) 
              as H0 by (apply IHl;auto).
       assert (incl l (a::l)) as Hincl by (apply incl_tl; apply incl_refl).
       now apply fold_left_in_seed_inc2 with l.
   Qed.
   
  Lemma fold_left_list_in :
    forall (A B :Type)(s:list A) (l :list B) (f : A -> list B) (a:B)  ,
      In a (fold_left (fun l1 e => (f e)++l1) s l) ->
      In a l \/ In a (fold_left (fun l1 e => (f e)++l1) s nil).
  Proof.
    induction s.
    - intros l f a H.
      simpl in H.
      left;assumption.
    - intros l f a1 H.
      simpl in H.
      assert (In a1 (f a ++ l) \/
        In a1 (fold_left (fun (l1 : list B) (e : A) => f e ++ l1) s [])) 
             as [Hinl | Hinf] by now apply IHs.
      + rewrite in_app_iff in Hinl. destruct Hinl as [Hinfa | Hinl].
        * right.
          simpl.
          apply fold_left_in_seed.
          rewrite app_nil_r; assumption.
        * left;auto.
      + right;auto.
        simpl.
        now apply fold_left_in_fold. 
  Qed.

  Lemma fold_left_getTribeChild_seed_nil :
    forall a s,
      ~ In a (fold_left (fun l1 e => (getTribeChild l1 e) ++ l1) s nil).
  Proof.
    intros a s Hin.
    induction s.
    - simpl in Hin. auto.
    - simpl in Hin.

      unfold getTribeChild at 2 in Hin.
      destruct a0 as [t0 a0].
      destruct a0;simpl in Hin;now apply IHs.
  Qed.

  Lemma inOpenedIsOpen :
    forall s p,
      In p (opened s) ->
      exists i, action_of (pi i s ) == Open p.
  Proof.
    induction s.
    - intros p H.
      simpl in *; exfalso;auto.
    - intros p H.
      unfold opened in H.
      simpl in H.
      destruct a as [t a].
      destruct a as [ | | | | | | | p'|p']; 
        try (simpl in H;destruct (IHs p) as [i Hi]; 
             auto;exists (S i);simpl;auto).
      simpl in H.
      assert (In p [p'] \/  In p (opened s)) as H1 by now apply fold_left_list_in.
      destruct H1 as [Hin | Hfold].
      + assert (p = p') as Heqp 
               by (inversion Hin; simpl in H0; auto; exfalso;trivial).
        subst.
        exists 0;auto.
      + destruct (IHs p) as [i Hi];auto.
        exists (S i).
        auto.
  Qed.

  Lemma pendingTailClosed: 
    forall (e:Event.t)(s: Tr)(p:Perm.t), 
      isPending (e::s) p = true -> 
      isPending s p = true.
  Proof.
    intros e s p H.
    unfold isPending, closed in *.
    simpl in *.
    apply eq_true_not_negb. contradict H.
    apply not_true_iff_false.
    apply negb_false_iff.
    apply inMemEq.
    apply inMemEq in H.
    now apply fold_left_in_fold.
  Qed.

  Lemma isPendingNotClosed :
    forall s p,
      isPending s p = true ->
      ~ occursIn s (Close p).
  Proof.
    induction s as [|e s IH].
    - intros p H.
      unfold isPending in H.
      intro H'. inversion H'. destruct i; simpl in Ha; discriminate.
    - intros p H.
      destruct e as [t a].
      destruct(eq_action_dec a (Close p)) as [Hclose | HnotClose ].
      + subst. unfold isPending,closed in H. 
        simpl in H. 
        assert(In p [p]) by auto with *.
        assert(In p (fold_left (fun x e => getClose e ++ x) s [p])) 
              as Hin by now apply fold_left_in_seed.
        eapply inMemEq in Hin.
        rewrite Hin in H.
        discriminate.
      + apply pendingTailClosed in H.
        assert(not(occursIn s (Close p))) as H' by now apply IH.
        contradict H'.
        inversion H' as [i a' Ha Ha'].
        destruct i as [|i].
        * simpl in *. contradict HnotClose. inversion Ha. trivial.
        * simpl in *. econstructor. apply Ha.
  Qed.

  Lemma pendingIs2 :
    forall s p,
      In  p (pendingList s) ->
      pending s p.
  Proof.
    intros s p H.
    unfold pendingList in H.
    assert (In p (opened s) /\  (isPending s p = true)) 
           as H0 by now apply filter_In.
    destruct H0 as [Hin Hispend].
    unfold pending.
    assert ( ~ occursIn s (Close p)) as Hnocc by now apply isPendingNotClosed.
    assert (exists i, action_of (pi i s ) == Open p) 
           as [i Hi] by now apply inOpenedIsOpen.
    split.
    - exists i.
      now constructor 2.
    - assumption.
  Qed.


  Lemma ownerf_owns:
    forall (s:Tr) (p:Perm.t) (t:threadId),
      ownerf s p == t -> owns s p t.
  Proof.
    unfold ownerf, eventOwnerf.
    induction s as [| e s IH]; intros p t H; simpl in *.
    - discriminate.
    - destruct e as [t' a]. simpl in *.
      destruct(eq_action_dec a (Open p)) as [Hopen | HnotOpen].
      + inversion H; subst. clear H.
        now constructor 1 with (i:=0).
      + case_eq(find (fun x => if eq_action_dec (snd x) (Open p) 
                                then true else false) s); 
        [intros e' H'|intros H'].
        * specialize IH with p t.
          rewrite H' in *.
          apply IH in H.
          inversion H.
          now constructor 1 with (i:=S i).
        * rewrite H' in *.
          discriminate.
  Qed.

  Lemma flatMapApp:
    forall (A B:Type)(f: A -> list B)(l1 l2 : list A), 
      flat_map f (l1++l2) = (flat_map f l1)++(flat_map f l2).
  Proof.
    intros A B f. induction l1 as [|a l1 IH]; intro l2.
    - trivial.
    - simpl. rewrite IH. 
      apply app_assoc.
  Qed.

(*
  Lemma flatMapGetTribeChild :
    forall s l t1 t2 i,
      In t2 (flat_map (getTribeChild l) s) ->
      pi i s == (t1, Fork t2) ->
      In t1 l.
  Proof.
  Qed.
*)

  Lemma getTribeChildIncl:
    forall t tribe e, 
      incl (getTribeChild tribe e) (getTribeChild (t::tribe) e).
  Proof.
    intros t tribe e.
    unfold incl, getTribeChild.
    intro t'; destruct e as [t'' a]; destruct a; try apply incl_refl; simpl.
    intro H.
    case_eq(Nat.eqb t'' t); intro Hbeq.
    + rewrite Nat.eqb_eq in Hbeq. subst.
      right. trivial.
    + trivial.
  Qed.

  Lemma incl_map:
    forall(A B:Type)(f:A->B)(l1 l2:list A),
      incl l1 l2 -> incl (map f l1) (map f l2).
  Proof.
    intros A B f l1 l2 H. 
    unfold incl in *; intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as [y [Heq Hiny]].
    rewrite <- Heq.
    apply in_map.
    now apply H.
  Qed.

  Lemma incl_flat_map:
    forall(A B:Type)(f:A->list B)(l1 l2:list A),
      incl l1 l2 -> incl (flat_map f l1) (flat_map f l2).
  Proof.
    intros A B f l1 l2 H. 
    unfold incl in *; intros x Hin.
    apply in_flat_map in Hin.
    destruct Hin as [y [Hiny Hinfy]].
    apply in_flat_map.
    exists y.
    apply H in Hiny.
    auto.
  Qed.

  Lemma incl_filter:
    forall(A:Type)(p:A->bool)(l1 l2:list A),
      incl l1 l2 -> incl (filter p l1) (filter p l2).
  Proof.
    intros A p l1 l2 H. 
    unfold incl in *; intros x Hin.
    apply filter_In in Hin.
    destruct Hin as [Hin Hp].
    apply H in Hin.
    apply filter_In.
    split; trivial.
  Qed.

  Lemma incl_dropWhilePrefix:
    forall(A:Type)(p:A->bool)(l:list A)(a:A),
      incl (dropWhile p l) (dropWhile p (l•a)).
  Proof.
    intros A p; induction l as [|x xs IH]; intro a.
    - simpl. destruct (p a). 
      + apply incl_refl.
      + apply incl_tl.
        apply incl_refl.
    - simpl. destruct(p x).
      + auto.
      + apply incl_appl with (n:=x::xs)(m:=[a]).
        apply incl_refl.
  Qed.

  Lemma incl_takeWhilePrefix:
    forall(A:Type)(p:A->bool)(l:list A)(a:A),
      incl (takeWhile p l) (takeWhile p  (l • a)).
  Proof.
    intros A p; induction l as [|x xs IH]; intro a.
    - simpl. destruct (p a). 
      + apply incl_tl.
        apply incl_refl.
      + apply incl_refl.
    - simpl. destruct(p x).
      + rewrite App.app_cons with (l:=takeWhile p xs).
        rewrite App.app_cons with (l:=takeWhile p (xs • a)).
        now apply incl_app_ll.
      + apply incl_refl.
  Qed.

  Lemma dropWhilePrefix: 
    forall(A:Type)(p:A->bool)(l:list A)(a:A),
    dropWhile p (l•a) = dropWhile p l \/
    dropWhile p (l•a) = (dropWhile p l) • a.
  Proof.
    intros A p. induction l as [| x xs IH]; intro a.
    - simpl. destruct (p a); auto.
    - destruct(IH a) as [Ha|Ha]; simpl;
      destruct(p x); simpl; auto.
  Qed.
      
  Lemma getTribeChildMonotonic:
    forall (e : Event.t) (l l' : list threadId),
      incl l l' -> 
      incl (getTribeChild l e) (getTribeChild l' e).
  Proof.
    intros [t a] l l' H.
    unfold getTribeChild; destruct a; simpl; try apply incl_refl.
    apply incl_map.
    now apply incl_filter.
  Qed.

  Lemma in_getTribe_s_se :
    forall s p t e,
      wellFormed (s • e) ->
      In t (getTribe s p) ->
      In t (getTribe (s • e) p).
  Proof.
    intros s p t e Hwf H. unfold Event.t in *.
    case_eq (ownerf s p) .
    - intros town Hown.
      assert (owns s p town) as Hown2 by now apply ownerf_owns.
      assert (owns (s • e) p town) as Hownse2 by now apply owns_s_se.
      assert (ownerf (s • e) p == town) as Hownse by now apply ownsOwnerRev.
      unfold getTribe in *.
      rewrite Hownse.
      rewrite Hown in H.
      inversion H; subst. 
      + subst.
        now constructor.
      + constructor 2. 
        apply fold_left_in_seed_inc2_gen with (l:= (flat_map (getTribeChild [town]) (getSection s p))).
        * apply getTribeChildMonotonic.
        * rewrite fold_left_app. simpl.
          apply in_or_app.
          auto.
        * apply incl_flat_map.
          unfold getSection.
          set(f:=fun x : threadId * action =>
                                        if eq_action_dec (snd x) (Open p) then false else true). 
          { destruct(dropWhilePrefix _ f s e) as [Hdrop|Hdrop].
            - rewrite Hdrop. apply incl_refl.
            - rewrite Hdrop. apply incl_takeWhilePrefix. }
    - intros H0.
      unfold getTribe in H.
      rewrite H0 in H.
      inversion H.
  Qed.

  Lemma fold_left_fork_occurs :
    forall s t l,
      In t 
         (fold_left
            (fun (trb : list threadId) (e : Event.t) =>
               getTribeChild trb e ++ trb)
            s l) ->
      ~ In t l ->
      occursIn s (Fork t).
  Proof.
    induction s as [|e s IH];intros t l H Hnin.
    - simpl in H.
      contradict H;auto.
    - destruct e as (tid,a); simpl in *.
      case_eq(eq_action_dec a (Fork t)); intros Ha _.
      + subst. now constructor 1 with (i:=0).
      + assert(~(In t (getTribeChild l (tid,a)))).
        {
          unfold getTribeChild. 
          destruct a; simpl; try solve [intro Hfalse; exfalso; trivial].
          intro Hin.
          apply in_map_iff in Hin.
          destruct Hin as [tid' [Heq Htid'In]].
          subst.
          apply Ha.
          trivial.
        }
        assert(~In t (getTribeChild l (tid, a) ++ l)) as Hnotin.
        {
          intro H'.
          apply in_app_iff in H'.
          destruct H' as [H'|H'];
            contradict H'; assumption.
        }
        specialize(IH _ _ H Hnotin).
        destruct IH as [pos a' Hpos].
        constructor 1 with (i:=S pos).
        auto.
  Qed.

  Lemma fold_left_fork_in2 :
    forall s t1 t2 l,
      In t1 l ->
      In t2 
         (fold_left
         (fun (trb : list threadId) (e : Event.t) =>
            getTribeChild trb e ++ trb)
         ((t1, Fork t2)::s) l).
  Proof.
    intros s t1 t2 l H.
    unfold getTribeChild;simpl.
    apply fold_left_in_seed_gen.
    apply in_split in H.
    destruct H as [l1[l2 H]]. subst.
    repeat rewrite filter_app. simpl.
    rewrite Nat.eqb_refl.
    repeat rewrite map_app. simpl. 
    apply in_or_app.
    left.
    apply in_or_app.
    right.
    simpl.
    left.
    reflexivity.
  Qed.

  Lemma filterFalse:
    forall (A : Type) (p : A -> bool) (l : list A),
      (forall a : A, In a l -> p a = false) -> List.filter p l = [].
  Proof.
    intros A p ;induction l as [|x s IH]; intro Hp.
    - trivial.
    - simpl. rewrite Hp; auto with *. 
  Qed.

  Lemma fold_left_fork_in1 :
    forall s t1 t2 l,
      ~ occursIn s (Fork t2) ->
      In t2 
         (fold_left
         (fun (trb : list threadId) (e : Event.t) =>
            getTribeChild trb e ++ trb)
         ((t1, Fork t2)::s) l) ->
      ~ In t2 l ->
      In t1 l.
  Proof.
    intros s t1 t2 l Hnocc H Hnin.
    case_eq(in_dec Peano_dec.eq_nat_dec t1 l); intros Hin _.
    - trivial.
    - unfold getTribeChild in H. simpl in H.
      assert(forall t, In t l -> Nat.eqb t1 t = false).
      {
        intros t0 H0.
        apply Nat.eqb_neq.
        intro Heq.
        subst.
        now contradict Hin.
      }
      rewrite filterFalse in H; auto.
      contradict Hnocc.
      now apply fold_left_fork_occurs with l.
  Qed.

  Lemma occursIn_not_after :
    forall  s1 s2 t1 t2,
      wf_occurences (s1 ++ (t1,Fork t2)::s2) ->
      ~ occursIn s2 (Fork t2).
  Proof.
    intros s1 s2 t1 t2 H.
    intro Hocc.
    inversion Hocc as [i a Ha];subst.
    unfold wf_occurences in H.
    assert ( occursAtMostOnce (s1 ++ (t1, Fork t2) :: s2) (Fork t2)) as Honce by now apply H.
    unfold occursAtMostOnce in Honce.
    assert (action_of (pi  (plus (S(length s1)) i)  (s1 ++ (t1, Fork t2) :: s2)) == Fork t2) as Ha2.
    rewrite nth_error_append_right.
    replace (S (length s1) + i - length s1) with (S i) by lia;auto.
    lia.
    assert (action_of (pi  (length s1)  (s1 ++ (t1, Fork t2) :: s2)) == Fork t2) as Hf.
    rewrite nth_error_append_cons_eq;auto.
    assert ((length s1) =  (plus (S(length s1)) i)) as Heq by now apply Honce.
    contradict Heq.
    lia.
  Qed.

  Lemma occursIn_not_before :
    forall  s1 s2 t1 t2,
      wf_occurences (s1 ++ (t1,Fork t2)::s2) ->
      ~ occursIn s1 (Fork t2).
  Proof.
    intros s1 s2 t1 t2 H.
    intro Hocc.
    inversion Hocc as [i a Ha];subst.
    unfold wf_occurences in H.
    assert ( occursAtMostOnce (s1 ++ (t1, Fork t2) :: s2) (Fork t2)) as Honce by now apply H.
    unfold occursAtMostOnce in Honce.
    assert (i<length s1) as Hltis1 by eauto with nth_error.
    assert (action_of (pi  i  (s1 ++ (t1, Fork t2) :: s2)) == Fork t2) as Ha2 by (rewrite nth_error_append_left;auto).
    assert (action_of (pi  (length s1)  (s1 ++ (t1, Fork t2) :: s2)) == Fork t2) as Hf by (rewrite nth_error_append_cons_eq;auto).
    assert (i =  (length s1)) as Heq by now apply Honce.
    lia.
  Qed.

  (*a deplacer dans ?*)
  Lemma in_exists_nth_error :
    forall (A:Type) (l : list A) (a :A),
      In a l ->
      (exists i, nth_error l i == a).
  Proof.
    intros A l a H.
    apply in_split in H. destruct H as [l1 [l2 Hl]].
    exists (length l1). rewrite Hl.
    apply nth_error_append_cons_eq.
  Qed.    

  Lemma notIn_flatMap :
    forall s t1 t2 l,
      wf_occurences s ->
      In (t1,Fork t2) s ->
      ~ In t1 l ->
      ~ In t2 (flat_map (getTribeChild l) s).
  Proof.
    intros s t1 t2 l Hwfo Hin Hnin Hinflat.
    rewrite in_flat_map in Hinflat. destruct Hinflat as [[t3 a3] [Hina Hint2]].
    unfold getTribeChild in Hint2.
    destruct a3;simpl in Hint2;auto.
    Admitted.
(*  case_eq (mem eq_nat_dec t3 l).
    - intro Hmem. rewrite Hmem in Hint2.
      assert (t2 = n) as Ht2n.
      { inversion Hint2. auto.
        inversion H.
      }
      subst. clear Hint2.
      assert (t1 = t3) as Ht1t3.
      {
        apply in_exists_nth_error in Hina.
        apply in_exists_nth_error in Hin.
        destruct Hina as [i Hi].
        destruct Hin as [j Hj].
        unfold wf_occurences in Hwfo.
        assert (i = j) as Hij.
        { unfold occursAtMostOnce in Hwfo. 
          apply Hwfo with (Fork n);auto.
          rewrite Hi;auto.

          assert ((@nth_error (prod nat action) s j) = (@nth_error Event.t s j)) as H by auto.
          rewrite H in Hj.
          rewrite Hj.
          auto.
        }
        rewrite  Hij in Hi. 
        Set Printing All.
        simpl.
        assert ((@nth_error (prod nat action) s j) = (@nth_error Event.t s j)) as H by auto.
        rewrite H in Hj.
        Unset Printing All.
        simpl.
        admit.
      }
      subst.
      rewrite <- inMemEq in Hmem.
      auto.
    - intro Hmem. rewrite Hmem in Hint2. inversion Hint2.
  Qed. *)

  Lemma notIn_notOccurs_fork_left:
    forall s t l,
      ~ occursIn s (Fork t) ->
      ~ In t l ->
      ~  In t
         (fold_left
            (fun (trb : list threadId) (e : Event.t) =>
               getTribeChild trb e ++ trb) s l).
  Proof.
    induction s.
    - intros t0 l Hnocc Hnin.
      intro Hn.
      simpl in Hn.
      contradict Hnin;auto.
    - intros t0 l H H0.
      simpl.
      apply IHs.
      + contradict H.
        inversion H.
        now constructor 1 with (S i).
      + intro Hin.
        apply in_app_or in Hin.
        destruct Hin as [HinTr | Hin].
        * destruct a as [t1 a].
          destruct a;simpl in HinTr;auto.
          unfold getTribeChild in HinTr.
          simpl in HinTr.
    (*    case_eq (mem eq_nat_dec t1 l).
          {
            intro Hmem.
            rewrite Hmem in HinTr.
            inversion HinTr as [H1 | H1].
            - subst.
              contradict H.
              constructor 1 with 0.
              simpl. auto.
            - inversion H1.
          }
          {
            intro Hmem.
            rewrite Hmem in HinTr.
            inversion HinTr.
          } *)
          admit.
        * contradict H0. assumption.
        Admitted.
  (* Qed. *)

  Lemma inGetTribeForkIn :
    forall s p t t',
      wellFormed s ->
      In t (getTribe s p) ->
      father s t' t ->
      In t'  (getTribe s p).
  Proof.
    intros s p t0 t' Hwf Hin Hfa.
     inversion Hfa as [i [Ht Ha]]. clear Hfa.
      inversion Hwf.
      assert(exists j t1,pi j s == (t1,Fork t0)) as H.
      { admit.
      }
      
      destruct H as [j [t1 Hj]].
      assert (action_of (pi j s) == Fork t0) as Hja by ( rewrite Hj;auto).

      assert(j<i) by (unfold wf_fork in WF2; eapply WF2; eassumption).
      assert(pi i s == (t0,Fork t')) by now apply lift_pair_surjective.
      assert(i < length s) as Hlen by (eapply nth_error_defined_lt; eauto).
      assert(s = firstn i s ++ nth i s ((t0,Fork t')):: skipn (S i) s)
        as Hs by now apply cutInThree.
      assert (j < length (firstn i s)) as Hlenj by (rewrite firstn_length1; lia).
      set (si:=(firstn i s)). 
      assert (firstn i s = firstn j si ++ nth j si ((t0,Fork t')):: skipn (S j) si)  as Hsi by now apply cutInThree.
      assert (j = length (firstn j si)) 
        as Hjlen by (autorewrite with length; rewrite min_l; auto with *).
      rewrite Hjlen in Hj. rewrite Hs in Hj. rewrite Hsi in Hj. 
      repeat rewrite <- app_assoc in Hj.
      rewrite <- app_comm_cons in Hj.
      rewrite nth_error_append_cons_eq in Hj.
      inversion Hj as [Hj' ].

      assert (i = length (firstn i s))
        as Hilen by (autorewrite with length; rewrite min_l; auto with *).
      generalize H0.
      rewrite Hilen.
      set (i':=length (firstn i s)). 
      rewrite Hs . 
      unfold i'.
      rewrite nth_error_append_cons_eq.
      intro Hi.
      inversion Hi as [Hi'  ]. rewrite Hi'.
      rewrite Hsi. rewrite Hj'. rewrite Hi'.

      unfold getTribe.
     
      assert ( exists t2, (  ownerf
         (@app Event.t
            (@app Event.t (@firstn Event.t j si)
               (@cons Event.t (@pair nat action t1 (Fork t0))
                  (@skipn Event.t (S j) si)))
            (@cons Event.t (@pair nat action t0 (Fork t'))
               (@skipn Event.t (S i) s))) p  ) == t2) as Hown by admit.
      destruct Hown as [ t2 Hown].
      autounfold.
      admit.
      Admitted. 
      (* rewrite Hown.

      constructor 2.
    
      rewrite <- app_assoc.
      Set Printing All.
      rewrite fold_left_app.
      
      set (seed:=  (@fold_left (list nat) Event.t
           (fun (trb : list nat) (e : Event.t) =>
            @app nat (getTribeChild trb e) trb) (@firstn Event.t j si)
           (@flat_map Event.t nat (getTribeChild (@cons nat t2 (@nil nat)))
              (@app Event.t (@firstn Event.t j si)
                 (@app Event.t
                    (@cons Event.t (@pair nat action t1 (Fork t0))
                       (@skipn Event.t (S j) si))
                    (@cons Event.t (@pair nat action t0 (Fork t'))
                       (@skipn Event.t (S i) s))))))).
      Unset Printing All.
      set (f:= (fun (trb : list threadId) (e : Event.t) =>
         getTribeChild trb e ++ trb)).
      unfold getTribe in Hin. rewrite Hs in Hin. rewrite Hi' in Hin. rewrite Hsi in Hin. rewrite Hj' in Hin. autounfold in *. rewrite Hown in Hin.
     
      inversion Hin as [Heq | Hin1].
      (*case_eq (Peano_dec.eq_nat_dec t0 t2).*)
      + (*t0 = t2,  owner de p*)
        (*intros Heq H1.*) unfold seed. rewrite Heq in *. (*clear H1.*)
        apply fold_left_in_seed_gen.
        apply fold_left_in_seed_gen.
        
        admit.
    (*    
        (*casse suite a la nouvelle definition de getTribe (tribeChildren correct)*) 

        rewrite flatMapApp.
        apply in_or_app. right.
        rewrite flatMapApp.
        apply in_or_app. right.
        unfold getTribeChild.
        simpl.
        destruct ( eq_nat_dec t0 t0).
        * left. trivial.
        * contradict n. trivial.
        *)
      + case_eq (Peano_dec.eq_nat_dec t1 t2).
        * intros Heq H1.
          unfold seed.
          rewrite Heq in *.
          rewrite fold_left_app.
          apply fold_left_fork_in2.
          apply fold_left_in_seed_gen.
          apply fold_left_in_seed_gen.
          admit.
           (*    
        (*casse suite a la nouvelle definition de getTribe (tribeChildren correct)*) 

          rewrite flatMapApp.
          apply in_or_app.
          right.
          simpl.
          apply in_or_app. left.
          unfold getTribeChild. simpl.
          destruct (eq_nat_dec t2 t2). constructor. auto.
          destruct n;auto.
            *)
        * intros Hneq H1.
          rewrite fold_left_app.
          unfold f.
          apply fold_left_fork_in2.  
          apply fold_left_fork_in2.  
          
        rewrite <- app_assoc in Hin1.
        rewrite fold_left_app in Hin1.
        rewrite <- app_comm_cons in Hin1.
        assert (~ occursIn (skipn (S j) si ++ (t0, Fork t') :: skipn (S i) s) (Fork t0)) as Hnocc.
        {
          
          rewrite Hs in WF1. rewrite Hsi in WF1. rewrite Hj' in WF1. rewrite Hi' in WF1.
          rewrite <-  app_assoc in WF1.  rewrite <- app_comm_cons in WF1. 
          apply occursIn_not_after with (s1:=(firstn j si ))(t1:=t1);auto.
        }
        assert ( ~
                   In t0
                   (fold_left
                      (fun (trb : list threadId) (e : Event.t) =>
                         getTribeChild trb e ++ trb) (firstn j si)
                      (flat_map (getTribeChild [t2])
                                (firstn j si ++
                                        (t1, Fork t0) :: skipn (S j) si ++ (t0, Fork t') :: skipn (S i) s)))) as Hnint0.
        {
          assert (~ occursIn  (firstn j si) (Fork t0)) as Hnocct0. 
          { apply occursIn_not_before with (skipn (S j) si ++ (t0, Fork t') :: skipn (S i) s) t1.
            rewrite Hs in WF1. rewrite Hsi in WF1. rewrite Hj' in WF1. rewrite Hi' in WF1.
            rewrite <-  app_assoc in WF1.  rewrite <- app_comm_cons in WF1. 
            auto.
          }
          assert (~ In t0  (flat_map (getTribeChild [t2])
           (firstn j si ++
            (t1, Fork t0) :: skipn (S j) si ++ (t0, Fork t') :: skipn (S i) s))) as Hnin.
          {
            apply notIn_flatMap with t1.
            - rewrite Hs in WF1. rewrite Hsi in WF1. rewrite Hj' in WF1. rewrite Hi' in WF1.
              rewrite <-  app_assoc in WF1.  rewrite <- app_comm_cons in WF1. 
              auto.
            - apply in_or_app. right. constructor. auto.
            - intro Hint1.
              inversion Hint1 as [H2 | H2].
              + destruct Hneq;auto.
              + inversion H2.            
          }
            now apply notIn_notOccurs_fork_left.
        }
        
        apply fold_left_fork_in1 in Hin1;auto.  
        admit. (*casse suite a la nouvelle definition de getTribe*)
  Qed. *)


  Lemma tribeChildren_getTribe :
    forall s p t,
      wellFormed s ->
      tribeChildren s p t ->
      In t (getTribe s p).
  Proof.
    intros s p t0 Hwf Htc.
    induction Htc; subst.
    - unfold getTribe.
      assert(ownerf s p == t0) as Hown by now apply ownsOwnerRev.
      assert(pi k s == (t0,Fork t')) by now apply lift_pair_surjective.
      assert(k < length s) as Hlen by (eapply nth_error_defined_lt; eauto).
      rewrite Hown.
      constructor 2.
      assert(s = firstn k s ++ nth k s ((t0,Fork t')):: skipn (S k) s)
            as Hs by now apply cutInThree.
      assert(k = length (firstn k s)) 
            as Hklen by (autorewrite with length; rewrite min_l; auto with *).
      revert H2. revert H3.
      rewrite Hklen.
      set(k':=length(firstn k s)).
      rewrite Hs.
      unfold k'.
      intros Ht Ha.
      apply lift_fst_inv in Ha.
      apply lift_snd_inv in Ht.
      destruct Ha as [y Ha].
      destruct Ht as [x Ht].
      rewrite nth_error_append_cons_eq in Ha.
      rewrite nth_error_append_cons_eq in Ht.
      inversion Ht; inversion Ha.
      rewrite H3 in H5. inversion H5.
      rewrite H6 in *. clear x H6.
      rewrite <- H7 in *. clear y H7 H5.
      rewrite H3.
      
      admit.
      (*
        (*casse suite a la nouvelle definition de getTribe*)
      rewrite flatMapApp.
      apply fold_left_in_seed_gen.
      apply in_or_app. right.
      simpl. apply in_or_app. left.
      unfold getTribeChild. simpl.
      destruct(eq_nat_dec t0 t0) as [H'|H'].
      + intuition.
      + contradict H'; trivial.
       *)
    - now apply inGetTribeForkIn with t0 .
    (* découpage en 3 morceaux à i, puis trois morceaux à j *)
    Admitted.
  (* Qed. *)
      
  Lemma tribe_getTribe :
    forall s p t,
      wellFormed s ->
      tribe s p t ->
      In t (getTribe s p).
  Proof.
    intros s p t0 H H0.
    induction H0.
    - unfold getTribe.
      assert(ownerf s p == t0) as Hown by now apply ownsOwnerRev.
      rewrite Hown.
      simpl. left. trivial.
    - now apply tribeChildren_getTribe.
  Qed.


  Lemma excludeIs : 
    forall s t p,
      wellFormed s ->
      In  p (excludeList s t) ->
      exclude s p t.
  Proof.
    intros s t0 p Hwf H.
    unfold excludeList in H.

    set (f0:= (fun p : Perm.t =>
            negb (mem EquivDec.nat_eq_eqdec t0 (getTribe s p)))).

    destruct filter_In with (f:=f0)(x:= p)(l:=(pendingList s)) as [H0 H1]. 
    assert (In p (pendingList s) /\ f0 p = true) as H3 by now apply H0.
    destruct H3 as [hpend hexcl].
    simpl in *.
    assert ((mem EquivDec.nat_eq_eqdec t0 (getTribe s p)) = false) as Hntribe. 
    {
      unfold f0 in hexcl.
      rewrite negb_true_iff in hexcl.
      assumption.
    }
    assert (~ In t0  (getTribe s p)) as Hnintribe. {
      contradict Hntribe.
     
      rewrite not_false_iff_true.
      now apply inMemEq.
      }
    constructor.
    - now apply pendingIs2.
    - contradict Hnintribe.
      now apply tribe_getTribe.
  Qed.


  (*condition a rajouter?*)
  (*Lemma excludeList_s_se :
    forall s a t' p t,
      In p (excludeList s t) ->
      a <> Close p ->
      In p (excludeList (s• (t',a)) t).
  Proof.
    intros s a t' p t Hin Hncl.
  Qed.
  *)

  Lemma excludeExcludeList :
     forall s t p,
      wellFormed s ->
      exclude s p t ->
      In  p (excludeList s t).
  Proof.
    induction s using tr_ind.
    - intros t0 p Hwf Hexcl.
      contradict Hexcl.
      apply exclude_nil.
    - intros t p Hwf Hexcl.
      destruct e as [t' a].
      destruct (open_action_dec a) as [Ha | Ha].
      + destruct Ha as [p' Hop]. subst.
        destruct (Perm.eq_dec p p') as [Hpp' | Hpp'].
        * subst.
          admit. (*p' necesseraiment pending car en derniere position, t<>t' ou pas*)
        * assert (exclude s p t) as Hexcls.
          apply exclude_se_s_not_open_p with p' t';auto.  
          admit. (*?*)
      + assert (exclude s p t) as Hexcls.
        apply exclude_se___s_not_open with t' a;auto.
(*
        assert (wellFormed s) as Hwfs by now apply wellFormed_se_s with (t',a).
        assert (In p (excludeList s t)) as Hin by now apply IHs.
 *)      

        admit.
  (* Qed. *)
  Admitted.

  Lemma nthExcludeList :
    forall s t p i,
       nth_error (excludeList s t) i == p ->
       exists i' , action_of( pi i' s)== (Open p). 
  Proof.
    admit.
Admitted.

(*
  Lemma orderFilter :
    forall (A:Type) (l1 l2 : list A) f a b i j,
      List.filter f l1 = l2 ->
      nth_error l2 i == a ->
      nth_error l2 j == b ->
      i < j ->
      exists i' j', 
        nth_error l1 i' == a /\ nth_error l1 j' == b /\ i'<j'.
  Proof.
    admit.
*)
  Lemma orderExcludeList :
    forall s t p p' i j,
      wellFormed s ->
      nth_error (excludeList s t) i == p ->
      nth_error (excludeList s t) j == p' ->
      i < j ->
      exists i' j', action_of( pi i' s)== (Open p) /\  action_of( pi j' s)== (Open p') /\ i'<j'.
  Proof.
    intros s t0 p p' i j Hwf Hi Hj Hlt.
    destruct (nthExcludeList s t0 p i) as [i' Hi'];auto.
    destruct (nthExcludeList s t0 p' j) as [j' Hj'];auto.
    exists i'. exists  j'.
    split;auto.
    split;auto.
    unfold excludeList in *.
    unfold pendingList in *.
    unfold opened in *.
    admit.
Admitted.


   Lemma  outerExcludefIsOuter :
    forall s p t,
      wellFormed s ->
      outerExcludef s t = Some p ->
      outerExclude s p t.
  Proof.
    intros s p t0 Hwf H.
    unfold outerExcludef in H.
    assert (In p (excludeList s t0)) as Hin. 
    {
      destruct (excludeList s t0);inversion H.
      subst. constructor;auto.
    }
    assert (exclude s p t0) as Hexl by now apply excludeIs.

    constructor;auto.
    intros p' Hexcl Hpp'.
    inversion Hexcl as [Hpend Hnt].
    inversion Hpend as [[i Hr] H1].    
    assert (In p' (excludeList s t0)) as Hexcls' by now apply excludeExcludeList.
    set (l:= (excludeList s t0)).
    assert (nth_error  (excludeList s t0) 0 == p) as Hnth0.
    {
      destruct (excludeList s t0);inversion H.
      eauto with nth_error.
    }
    assert (exists j, nth_error (excludeList s t0) j == p') as [ j Hnthj].
    {
      assert (exists l1 l2, (excludeList s t0) = l1++p'::l2) as [l1 [ l2 Hex]] by now apply in_split.
      exists (length l1).
      rewrite Hex.
      autorewrite with nth_error;auto.
    }
    assert (j<> 0) as Hj0.
    {
      intro Hn.
      subst.
      contradict Hpp'.
      rewrite Hnth0 in Hnthj. inversion Hnthj. auto.
    }
    assert (0<j) as H0j by lia.
    destruct (orderExcludeList  s t0 p p' 0 j) as [i' [j' [Hi' [Hj' Hlti'j']]]];auto.
    constructor 1 with i' j';auto.
  Qed.


  Lemma in_hd_error_not_none :
    forall (A:Type)(l:list A)(a:A),
      In a l ->
      hd_error l <> None.
  Proof.
    induction l.
    - intros a H.
      contradict H; apply in_nil.
    - intros a0 H.
      simpl.
      congruence.
  Qed.

  Lemma  outerExcludefNone :
    forall s  t,
      wellFormed s ->
      outerExcludef s t = None ->
      (forall p : Perm.t, ~ exclude s p t).
  Proof.
    intros s t Hwf H p.
    contradict H.
    assert (In  p (excludeList s t)) as Hinexcl by now apply excludeExcludeList.
    unfold outerExcludef.
    now apply in_hd_error_not_none with p.
  Qed.

End Make.
