(** printing Sigma #&Sigma;# *) (** printing pi  #&pi;#*)
(** printing nat #&#8469;#*)
(** printing exists #&exist;# *) (** printing forall #&forall;# *)
(** printing /\ #&and;# *) (** printing \/ #&or;# *)
(** printing -> #&#x02192;# *)
(** printing • #&#8226;# *)

Require Import List Arith.
Require Import sections.lifo.ListBasics.

Require Import sections.lifo.Prelude.
Require Import sections.common.GenericTrace.
Require Import sections.traces.Trace.
Require Import sections.traces.Trace_Basics_projection.
Require Import sections.traces.Trace_Basics_occurences.

Require Import Lia.

Module Make (Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ) 
            ( Import Tr : Trace.T Perm Address T V)
            ( Import P : Proj Perm Address T V Tr)
            ( Import O : OccurencesT Perm Address T V Tr P).

  (** ** Range *)
  

  (** *** Functional *)
  
  Fact range_functionnal : 
    forall s, 
      wf_occurences s -> 
      forall p i j, 
        range s p i j -> 
        forall i' j', 
          range s p i' j' ->
          i = i' /\ j = j'.
  Proof.
    intros s h_wf_occurences p i j h_range i' j' h_range'.
    Admitted.
    (* inversion h_range as [? h_open ? | ? ? h_not_closed]; 
      inversion h_range' as [? h_open' ? | ? ? h_not_closed']; 
      subst; split; 
      solve [ wellFormed_occurences (Open p) 
            | wellFormed_occurences (Close p) | 
            elim h_not_closed;eauto 
            | elim h_not_closed'; eauto 
            | reflexivity].
  Qed.  *)

  Hint Resolve range_functionnal : range.
  
  (** *** inequalities *)
  
  Fact range_j_lt_s : 
    forall s p i j, range s p i j -> j < length s.
  Proof.
    intros s p i j HRange.
    inversion HRange as [ ? h_open ? h_closed | ? h_open h_not_closed]; subst.  
    - eauto with nth_error.
    - destruct s; simpl.
      + autorewrite with nth_error in h_open; discriminate.
      + lia.
  Qed.
  
  Fact range_i_lt_j : 
    forall s, 
      wf_occurences s -> 
      wf_open_close s ->
      forall p i j, range s p i j -> i <= j.
  Proof.
    intros s h_wf_occurence_s h_wf_open_close_s p i j h_range.
    inversion h_range as [ ? h_open ? h_closed | ? h_open h_not_closed]; subst.
    - assert (i < j).
      {
        destruct h_wf_open_close_s with j p as [i' [h_i' [h_open_' _]]]; [ assumption|].
        now replace i with i' by wellFormed_occurences (Open p).
      }
      auto with *.
    - assert (i < length s) by eauto with nth_error.
      auto with *.
  Qed.
  
  Fact range_i_lt_s : 
    forall s,
      wf_occurences s ->
      wf_open_close s ->
      forall p i j, range s p i j -> i < length s.
  Proof.
    intros s h_wf_occurences_s h_wf_open_close_s p i j h_range.
    assert (i <= j) by eauto using range_i_lt_j.
    assert (j < length s) by eauto using range_j_lt_s.
    auto with *.
  Qed.
  
  Ltac obtain_range_inequalities H0 :=
    match type of H0 with
        range ?S ?P ?I ?J =>
        let Ha := fresh "h_lt_j_s" in
        let Hb := fresh "h_le_i_j"in
        let Hc := fresh "h_lt_i_s" in
        match goal with 
          | H1 : wf_occurences ?S, H2 : wf_open_close ?S |- _ => 
            assert (J < length S) as Ha by exact (range_j_lt_s S P I J H0);
              assert (I <= J) as Hb by exact (range_i_lt_j S H1 H2 P I J H0);
              assert (I < length S) as Hc by exact (range_i_lt_s S H1 H2 P I J H0)
        end
    end.

  (** *** s_se *)
  
  Fact range_s_se_lt : 
    forall s p i j, 
      range s p i j -> 
      forall e,  
        j < length s - 1  -> 
        range (s • e) p i j.
  Proof.
    intros s p i j H e H0.
    assert (action_of (pi i (s • e)) == Open p) by 
        (inversion H; auto with nth_error).
    inversion H; subst.
    - assert (action_of (pi j (s • e)) == Close p) by
             auto with nth_error.
      eauto using range_closed.
    - exfalso; auto with *.
  Qed.
  
  Lemma range_s_se : 
    forall s p i j e,
      range s p i j ->
      (action_of (pi j (s • e)) == Close p /\ range (s • e) p i j) 
      \/ range (s • e) p i (length s).
  Proof.
    intros s p i j e h_range.
    inversion h_range; subst.
    - left; split; [eauto with nth_error | constructor 1; eauto with nth_error].
    - assert (action_of (pi i (s • e)) == Open p) by eauto with nth_error.
      right; destruct e as [t a]; destruct (eq_action_dec a (Close p)); [subst |].
      + constructor 1;[ eauto with nth_error | now autorewrite with nth_error].
      + admit.
Admitted.

  Hint Resolve range_s_se_lt range_s_se : range.

  (** *** se_s *)
  
  Fact range_se_s_lt :
    forall s e, 
      wf_occurences (s • e) -> 
      wf_open_close (s • e) ->
      forall p i j,  
        j < length s -> 
        range (s • e) p i j -> 
        range s p i j.
  Proof.
    intros s e h_wf_occurences_s h_wf_open_close_s p i j h_lt h_range.
    assert (action_of (pi i s) == Open p).
    {
      assert (i < length s) by (obtain_range_inequalities h_range; auto with *).
      inversion h_range; subst; now nth_error_rewrite Hi. 
    }
    assert (action_of (pi j s) == Close p).
    {
      inversion h_range; subst.
      - now nth_error_rewrite Hj.
      - exfalso.
      admit. 
      (* autorewrite with length in h_lt; simpl in h_lt; lia. *)
    }
    auto using range_closed.
  (* Qed. *)
Admitted.  
  Fact range_se_s_neq_open : 
    forall s  t a, 
      wf_occurences (s • (t,a)) ->
      wf_open_close (s • (t,a)) ->
      forall p i j,
        range (s • (t,a)) p i j ->
        a <> Open p -> 
        (action_of (pi j s) == Close p /\ range s p i j) 
        \/ (~ occursIn s (Close p) /\ range s p i (length s - 1)).
  Proof.
    intros s t a h_wf_occurences_s_ta h_wf_open_close_ta p i j h_range h_neq.
    assert (action_of (pi i s) == Open p).
    {
      assert (action_of (pi i (s • (t,a))) == Open p) by now inversion h_range.
      assert (i < length s).
      {
        destruct (lt_eq_lt_dec i (length s)) as [ []|  ]; [assumption | subst | ].
        - autorewrite with nth_error in H; injection H; intros; subst; intuition.
        - obtain_range_inequalities h_range.
          admit.
          (* autorewrite with length in h_lt_i_s; simpl in h_lt_i_s; intuition. *)
      }
      eauto 4 with nth_error.
    }
    destruct (occursIn_dec s (Close p)) as [Ha | Ha].
    - left.
      assert (action_of (pi j s) == Close p).
      {
        inversion Ha; subst.
        inversion h_range; subst.
        - assert (action_of (pi i0 (s • (t,a))) == Close p) by eauto with nth_error.
          assert (i0 = j) by wellFormed_occurences (Close p).
          subst; assumption.
        - elim HNotClosed; exists i0; eauto with nth_error.
      }
      split; [assumption|constructor 1; auto using range_closed].
    - right; split; [assumption | constructor 2; auto using range_opened].
  (* Qed. *)
Admitted.
  Hint Resolve range_se_s_lt range_se_s_neq_open : range.
  
  (** *** other properties *)
  
  Lemma owns_range : 
    forall s p t, owns s p t -> exists i j, range s p i j.
  Proof.
    intros s p t h_owns.
    inversion h_owns as [? i ? _ h_action]; subst.
    destruct (occursIn_dec s (Close p)) as [ Ha | Ha].
    - inversion Ha as [j ? h_j]; subst.
      exists i, j; now constructor 1.
    - exists i, (length s - 1); now constructor 2.
  Qed.

  Hint Resolve owns_range : range.

  

     
End Make.

(* begin hide *)
Module Type RangeT (Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ) 
            ( Tr : Trace.T Perm Address T V)
            ( P : Proj Perm Address T V Tr)
            ( O : OccurencesT Perm Address T V Tr P).
  Include Make Perm Address T V Tr P O.
End RangeT.
(* end hide *)
