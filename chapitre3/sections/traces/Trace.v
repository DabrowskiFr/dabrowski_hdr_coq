Require Import List Arith Relation_Operators.
Require Import sections.lifo.Prelude.
Require Import sections.common.GenericTrace.
Require Import sections.common.Type_. 
Require Import sections.common.Value.

Open Scope type_scope.

Module Make (SN : MiniDecidableSet )
            (Export Ad : DecidableInfiniteSet) 
            (Export Ty : Type_.TYPE Ad)
            (Export Va : Value.TYPE Ad Ty).
 
  (** * Definitions *)
  
  (** ** Traces *)
 
  (** - We define locations, thread ids and values as follows.
           -- [location] : memory locations
           -- [threadId] : threads identifiers
           -- [value] : values
      - The alphabet of actions is given by :  
       -- [Allocate l n] : allocates an array of size [n] at location [n]
       -- [Free l] : deallocates array at location [l]
       -- [Read l v], [Write l v] : reads/write value v from/to location l
       -- [Fork t], [Join t] : fork/join thread [t]
       -- [Open p], [Close p] : open/close a section with name [p]
       -- [Silent] : non observable action 
      - An event [e] is a pair [(t,a)] where [t] is a thread id and [a] is an action. 
      - Finally we consider traces of events where *)
  
  Definition threadId := nat. 

  Hint Unfold threadId : myunfold.
  
  Inductive action : Type :=
  | Silent : action
  | Allocate : Ad.t -> nat -> action 
  | Free : Ad.t -> action
  | Read : Ad.t -> nat -> Va.t -> action 
  | Write : Ad.t -> nat -> Va.t -> action
  | Fork : threadId -> action 
  | Join : threadId -> action
  | Open : SN.t -> action 
  | Close : SN.t -> action.

  Module Event.

  Definition t := threadId * action.
  
  Lemma eq_dec : forall (e e' : t), {e = e'}+{e <> e'}.
  Proof.
    repeat decide equality; 
      try ( apply SN.eq_dec || apply Ad.eq_dec || apply Va.eq_dec).
  Qed.
  
  End Event.  
  
  Module Export Tr := GenericTrace.Trace (Event).
  
  (** ** Basic definitions over traces *)
  (** - We note [threadOf] and [action_of] the first and second projections over events. *)
  (** - The relation [range] captures the range of a section occuring
        in a trace. For well-formed trace, [range] defines a partial function, see below. *)
  
  Notation threadId_of := (lift (@fst threadId action)).
  
  Notation action_of := (lift (@snd threadId action)).

  (** *** Ownership *)
  (** [owns s p t] : [t] owns section [p] in [s] *)

  Inductive owns (s : Tr) : (SN.t -> threadId -> Prop) :=
  | owns_cons : 
    forall t i p 
      (HThreadOf : threadId_of (pi i s) == t) 
      (HActionOf : action_of (pi i s) == Open p),
      owns s p t.


  (** *** father *)
  (** [father s t t'] : [t'] is the father of [t] in [s] *)

  Definition father (s : Tr) (t : threadId) : threadId -> Prop :=
    fun t' => 
      exists i, 
        threadId_of (pi i s) == t' 
        /\ action_of (pi i s) == Fork t.

  Definition ancester (s : Tr) := clos_trans _ (father s).
    
  (** *** Range *)
  (** [section s p i j] : section [p] range from [i] to [j] in [s], i.e *)
  (** [p] is opened at position [i] and *)
  (** - either [p] is close at position [j] *)
  (** - or [p] is never closed and [j] is the last position of [s] *)

  Inductive occursIn (s : Tr) : action -> Prop :=
    occursIn_cons : 
      forall (i : nat) (a : action) 
             (Ha : action_of (pi i s) == a), 
        occursIn s a.

  Inductive occursAfter (s : Tr) (a : action) : action -> Prop :=
  occursAfter_cons : 
    forall (i : nat) (j : nat) (a' : action) 
            (HLt : i < j) 
            (Ha : action_of (pi i s) == a) 
            (Ha' : action_of (pi j s) == a'),
      occursAfter s a a'.
    

  Inductive range (s : Tr) (p : SN.t) :  nat -> nat -> Prop :=
  |  range_closed : 
       forall i (Hi : action_of (pi i s) == Open p) 
              j (Hj : action_of (pi j s) == (Close p)),    
         range s p i j
  |  range_opened : 
       forall i (Hi : action_of (pi i s) == (Open p))
              (HNotClosed : ~ occursIn s (Close p)),
         range s p i (length s - 1).

  Inductive section (s : Tr) (p : SN.t) : Prop := (* TO REMOVE *)
    section_cons : forall i j, range s p i j -> section s p.
  
  Definition precedes (s: Tr) (p p' : SN.t) :=
    occursAfter s (Close p) (Open p').

  (**  *** Tribe
        A tribe is the set of threads that participate to an atomic section. 
        This includes the thread that initiates the section (the owner) and all
        threads resulting from the execution of this section (the childrens).  *)
  
  Inductive tribeChildren (s: Tr) (p : SN.t) : nat -> Prop :=
  | tribeChildren_direct : 
      forall i j t, 
        range s p i j ->
        owns s p t -> 
        forall k t',
          i < k <= j ->
          threadId_of (pi k s) == t -> action_of (pi k s) == Fork t' -> 
          tribeChildren s p t'
  | tribeChildren_indirect : 
      forall t t', tribeChildren s p t -> father s t' t -> tribeChildren s p t'.
  
  Definition tribe (s : Tr) (p : SN.t) : threadId -> Prop :=
    fun t => owns s p t \/ tribeChildren s p t.

  Inductive sec_order (s : Tr) : SN.t -> SN.t -> Prop :=
      sec_order_cons_dir :
        forall p i j k p',
          range s p i j ->
          i <=  k <= j -> 
          action_of (pi k s) == Open p' ->
          threadId_of (pi i s) = threadId_of (pi k s) ->
          sec_order s p p'
    | sec_order_cons_ind : 
        forall i i' p p' t,
          action_of (pi i s) == Open p ->
          action_of (pi i' s) == Open p' ->
          threadId_of (pi i' s) == t ->
          tribeChildren s p t ->
          sec_order s p p'.
  
  Definition concurrent s p p' := 
    occursIn s (Open p) /\
    occursIn s (Open p') /\
    (~ sec_order s p p' /\ ~ sec_order s p' p).
        

    (** Predicate see *)

    Inductive seeImm  : Tr -> nat -> nat -> Prop := (* Synchronisation *)
    | seeSelf :
      forall s i j t, 
        i < j ->
        threadId_of (pi i s) == t ->
        threadId_of(pi j s) == t ->
        seeImm s i j
    | seeWrite :
      forall s i j l n v,
        i < j ->
        action_of(pi i s) == Write l n v ->
        action_of(pi j s) == Read l n v ->
        seeImm s i j
    | SeeFork : 
      forall s i j t,
        i < j -> 
        action_of(pi i s) == Fork t ->
        threadId_of(pi j s) == t ->
        seeImm s i j.
    
    Definition see (s : Tr)  := clos_trans _ (seeImm s).

  (** Auxiliary definitions *)

  Definition pending s p : Prop :=
    (exists i, range s p i  (length s - 1)) /\ ~ occursIn s (Close p).
  
  Definition exclude s p t : Prop := pending s p /\ ~ tribe s p t.
  
  Definition conflicts (s : Tr) (t : threadId) := 
    exists p, exclude s p t.

  Inductive outerExclude s p t : Prop :=
    outerExclude_cons :
      forall (H0 : exclude s p t)
             (H1 : forall p', exclude s p' t -> p <> p' -> occursAfter s (Open p) (Open p')),
        outerExclude s p t.
  
  Definition occursAtMostOnce (s : Tr) (a : action) :=
  forall i j, 
    action_of (pi i s) == a -> 
    action_of (pi j s) == a -> 
    i = j.

  (** *** Occurences *)
  
  Inductive singleAction : action -> Prop :=
    singleAction_fork : forall t, singleAction (Fork t)
  | singleAction_open : forall p, singleAction (Open p)
  | singleAction_close : forall p, singleAction (Close p).

  (** * Well formed traces *)
  (** 
       Obviously, not all traces denote execution of concrete programs. In this section,
       we introduce some definitions and
       restrict our attention to traces satisfying some synchronisation properties.
       
          - _single occurences_ : any [Fork] / [Open] / [Close] action occurs at most once in
            a trace. 

          - _[Fork] / [Join] - [Open]-[Close] coherency_ : a thread can not be forked if it
            has already performed actions, nor it can be joined it it still has actions to perform.
            A [Close] action must match an [Open] action performed by the same thread.

          - _sections_ : we define the notion of section associated with a permission in a trace
            and impose condition on how sections are ordered in a trace.

          - _tribes_  : we define the notion of tribe associated with a section and impose sufficient
            conditions for ensuring that members of a tribe do not interfere with other threads
            while the section is active.
            - join can only occur between members of the same tribe. 
              This condition matches the intuition that a section occurs in zero
              time from an external point of view. Within a section, a thread of 
              the tribe associated with the section may not observe the termination
              of a thread that was not terminated when the section started.
           - section opening *)

  (** **** *)

  (** (WF1) Fork, Open, Close actions occur at most once *)

  Definition wf_occurences (s : Tr) :=
    forall a, singleAction a -> occursAtMostOnce s a.

  (** (WF2) a [Close] action must match an [Open] action performed by the same thread. *)

  Definition wf_open_close (s : Tr) :=
    forall i p, action_of (pi i s) == Close p -> 
           (exists j, j < i /\ action_of (pi j s) == Open p 
                   /\ (threadId_of (pi i s) = threadId_of (pi j s))).

  (** (WF3) *)
      
  Definition wf_seq_order (s : Tr) :=
    forall p i j,
      range s p i j -> 
      action_of (pi j s) == Close p -> 
      forall k p',
        i < k < j ->
        threadId_of (pi i s) = threadId_of (pi k s) ->
        action_of (pi k s) == Open p' ->
        exists j', k < j' < j /\ action_of (pi j' s) == Close p'.

  (** (WF4) a [Fork] action over a thread can not occur if the
         thread has already performed actions  *)

  Definition wf_fork (s : Tr) :=
    forall i t, action_of(pi i s) == Fork t -> 
                forall j, threadId_of(pi j s) == t -> i < j.

  (** (WF5) A join action cannot occur if the thread performs some
   action or is forked latter *)

  Definition wf_join (s : Tr) :=
    forall i j t, 
      (threadId_of (pi i s) == t \/ action_of (pi i s) == Fork t) ->
      action_of (pi j s) == Join t -> i < j.
  
  (** (WF6) It is not possible to join a thread with opened sections *)

   Definition wf_join_all_closed (s : Tr) : Prop := 
    forall p t i j k,
      range s p i j ->
      owns s p t ->
      action_of(pi k s) == Join t ->
      j < k.

  (** (WF7) A join on a thread see the fork of this thread *)

  Definition wf_join_see_fork (s : Tr) := 
    forall t k k',
      action_of(pi k s) == Fork t ->
      action_of(pi k' s) == Join t ->
      see s k k'.

  (** (WF8) concurrent sections *)

  Definition wf_mutualExclusion (s : Tr) : Prop :=
    forall p p', 
      concurrent s p p' -> precedes s p p' \/ precedes s p' p.

  (** well-formed trace *)

  Inductive wellFormed (s : Tr) := 
    wellFormed_cons : 
    forall
      (WF1 : wf_occurences s)
      (WF2 : wf_fork s)
      (WF3 : wf_join s)
      (WF4 : wf_open_close s)
      (WF5 : wf_seq_order s)
      (WF6 : wf_join_see_fork s)
      (WF7 : wf_join_all_closed s)
      (WF10 : wf_mutualExclusion s),
      wellFormed s.

    Ltac wellFormed_occurences X :=
    match goal with
      | H : wellFormed _ |- ?I = ?J => inversion H; clear H; wellFormed_occurences X
      | H : wf_occurences ?S, 
            H0 : action_of (pi ?I ?S) == X,
                 H1 : action_of (pi ?J ?S) == X |- ?I = ?J =>
        apply H with X; [constructor | assumption | assumption]
    end.

    Ltac wellFormed_fork :=
      match goal with
        | H : wellFormed ?S |- _ => inversion H; clear H; wellFormed_fork
        | H : wf_fork ?S, H0 : pi ?I ?S == (?T, Fork ?T) |- _ =>
          exfalso; elim (Nat.lt_irrefl I); apply H with T; rewrite H0; trivial
        | H : wf_fork ?S, H0 : pi ?I ?S == (?T, Fork ?T) |- ?I < ?I =>
          apply H with T; rewrite H0; trivial
      end.

End Make.

Module Type T 
       (SN : MiniDecidableSet)
       (Export Ad: DecidableInfiniteSet) 
       (Export Ty : Type_.TYPE Ad)
       (Export Va : Value.TYPE Ad Ty).
  Include Make SN Ad Ty Va.
End T.
