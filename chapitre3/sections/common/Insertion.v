Require Import List.
Require Import sections.lifo.ListBasics.
Require Import Le Lt Peano_dec Compare_dec.
Require Import sections.lifo.Prelude.
Require Import sections.lifo.BijRel.


Open Scope monad_scope.



(******************************************************)
(*                    insertion                       *)
(******************************************************)

Fixpoint insertion {A : Set} (m : nat) (l : list A) (e : A) : option (list A) :=
  match m with 
    | 0 => Some (e::l)
    | S n => 
      match l with
        | nil => None
        | a::l' => do y <- insertion n l' e; Some (a::y)
      end
  end.

Section InsertionBasics.

  Lemma insertion_S : 
    forall {A : Set} (i : nat) (l : list A) (e e1 e2 : A) (l' : list A),
      (insertion (S i) (e1::l) e == (e2::l')) 
      <-> (e1 = e2 /\ insertion i l e == l').
  Proof.
    intros A i l e e1 e2 l'.
    split.
    - simpl; intro h_insertion.
      destruct (insertion i l e); simpl in h_insertion.
      + injection h_insertion.
        intros; subst; tauto.
      + discriminate.
    - simpl; intros [Ha Hb].
      destruct (insertion i l e); simpl.
      + repeat f_equal; congruence.
      + discriminate.
  Qed.

  Lemma insertion_length : 
    forall (A :Set)(i : nat) (s : list A) e s', 
      insertion i s e == s' -> S (length s) = length s'.
  Proof.
    induction i.
    - intros s e s' H.
      assert (s' = e::s) by now injection H.
      replace s' with (e::s).
      reflexivity.
    - intros s e s' H.
      destruct s as [ | a s]; [ discriminate |]; simpl in H.
      destruct s' as [ | a' s'];[destruct (insertion i s e); discriminate |].
      assert (insertion i s e == s') by (eapply insertion_S; eauto).
      simpl; f_equal.
      now apply IHi with (e:=e).
  Qed.

  Lemma insertion_not_nil :
    forall {A : Set} (m : nat) (l : list A) (e : A),
      insertion m l e == nil -> False.
  Proof.
    intros A m l e H.
    assert (S (length l) = length (@nil A)) by eauto using insertion_length.
    discriminate.
  Qed.
  
  (** Relation between elements *)
  
  Lemma insertion_lt {A : Set} :
    forall (m : nat) (l : list A) (e : A) (k : nat) (l' : list A),
      insertion m l e == l' -> 
      k < m -> 
      nth_error l' k = nth_error l k.
  Proof.
    induction m as [ | m IHm].
    - intros l e k l' insertion_hyp lt_k_m.
      exfalso; auto with *.
    - intros l e k l' insertion_hyp lt_k_m.
      destruct l as [ | a l]; [discriminate|].
      destruct l' as [ | a' l']; [exfalso; eauto using insertion_not_nil | ].
      replace a' with a by (eapply insertion_S; eauto).
      destruct k as [ | k].
      + reflexivity.
      + assert (insertion m l e == l') by (eapply insertion_S; eauto).
        assert (k < m) by auto with *.
        now apply (IHm l e k l').
  Qed.

  Lemma insertion_ge {A : Set} :
    forall (m : nat) (l : list A) (e : A) (k :nat) (l':list A),
      insertion m l e == l'-> 
      ~ k < m -> 
      nth_error l' (S k) = nth_error l k.
  Proof.
    induction m as [ | m IHm].
    - intros l e k l' insertion_hyp ge_k_0.
      injection insertion_hyp; intros; subst.
      reflexivity.
    - intros l e k l' insertion_hyp ge_k_Sm.
      destruct l as [ | a l]; [ discriminate|].
      destruct l' as [ | a' l']; [exfalso; eauto using insertion_not_nil |].
      destruct k; [exfalso; auto with *|].
      simpl.
      apply IHm with (e:=e).
      eapply insertion_S; eauto.
      auto with *.
  Qed.

  Lemma insertion_eq {A : Set} :
    forall (m : nat) (l : list A) (e : A) (l': list A),
      insertion m l e == l' -> nth_error l' m == e.
  Proof.
    induction m as [ | m IHm].
    - intros l e l' insertion_hyp.
      replace l' with (e::l) by now injection insertion_hyp.
      trivial.
    - intros l e l' insertion_hyp.
      destruct l; [discriminate|].
      destruct l'.
      + simpl in insertion_hyp.
        destruct (insertion m l e); discriminate.
      + assert (insertion m l e == l')
          by (rewrite insertion_S in insertion_hyp; tauto).
        simpl.
        now apply IHm with (l:=l).
  Qed.

  Lemma insertion_defined {A : Set} : 
    forall (m : nat) (l : list A) (e : A),
      m <= length l -> exists l', insertion m l e == l'.
  Proof.
    induction m as [ | m IHm].
    - intros l e le_0_l.
      exists (e::l); reflexivity.
    - intros l e le_Sm_l.
      destruct l as [ | a l ]. 
      + exfalso; now apply (Nat.nle_succ_0 m).
      + assert (m <= length l) as le_m_l by auto with *.
        assert (exists l', insertion m l e == l') as [l' HEq] by now apply IHm.
        exists (a::l').
        simpl.
        rewrite HEq; reflexivity.
  Qed.
  
  Lemma insertion_defined_rev {A : Set} :
    forall (m : nat) (l : list A) (e : A),
      (exists l', insertion m l e == l') -> m <= length l.
  Proof.
    induction m.
    - auto using Nat.le_0_l.
    - intros l e Insertion.
      destruct Insertion as [l' Hl'].
      destruct l as [ | e' m']; [discriminate|].
      destruct l' as [ | e'' l'].
      + exfalso; eauto using insertion_not_nil.
      + apply le_n_S.
        apply IHm with (e:=e).
        exists l'.
        eapply insertion_S; eauto.
  Qed.
  
End InsertionBasics.

(** Relation bewteen old and new position *)

Inductive insertion_rel (i : nat) (m : nat) : nat -> nat -> Prop :=
| insertion_left : forall k, k < i -> insertion_rel i m k k
| insertion_right : forall k, i <= k < m -> insertion_rel i m k (S k)
| insertion_middle : insertion_rel i m m i.

Section InsertionRelBasics.

  Variable i : nat.
  Variable m : nat.
  Variable h_le : i <= m.
  
(** The relation (insertion_rel i m) is a bijection between [0..m] and [0..m] *)
  
  Lemma insertion_rel_bijective : 
    bijective (fun k => k < S m) (fun k => k < S m) (insertion_rel i m).
  Proof.
    constructor.
    - intros x y h_R.
      inversion h_R; subst.
      split; auto with *.
      split; auto with *.
      split; auto with *.
    - intros x y z Ha Hb.
      inversion Ha; inversion Hb; subst; 
      first [ auto with * | exfalso; auto with *].
    - intros k Ha.
      destruct (lt_dec k i); [ | destruct (eq_nat_dec k m); [subst|]].
      + (exists k).
        now apply insertion_left.
      + (exists i).
        now apply insertion_middle.
      + (exists (S k)).
        assert (i <= k < m) by auto with *.
        now apply insertion_right.
    - intros x y z Ha Hb.
      inversion Ha; inversion Hb; subst; try first [auto with * | exfalso; auto with *].
    - intros k Ha.
      destruct (lt_dec k i); [ | destruct (eq_nat_dec k i); [subst|]].
      + (exists k).
        now apply insertion_left.
      + (exists m).
        now apply insertion_middle.
      + destruct k; [exfalso; auto with * |].
        (exists k).
        assert (i <= k < m) by auto with *.
        now apply insertion_right.
  Qed.  

  (** The following lemmas describe how positions are related *)

  Lemma insertion_rel_fst_left : 
    forall k1 k2,
      k1 < i -> 
      insertion_rel i m k1 k2 -> 
      k1 = k2.
  Proof.
    intros k1 k2 H.
    assert (insertion_rel i m k1 k1) by now apply insertion_left.
    assert (functionnal (insertion_rel i m))
      as h_functional by now destruct insertion_rel_bijective.
    now apply (h_functional k1).
  Qed.

   Lemma insertion_rel_fst_right : 
     forall k1 k2,
       insertion_rel i m k1 k2 ->
       i <= k1 < m -> 
       k2 = S k1.
   Proof.
     intros k1 k2 H H0.
     inversion H; subst; first [auto with * | exfalso; auto with *].
   Qed.
   
   Lemma insertion_rel_fst_last :
     forall k, 
       insertion_rel i m m k -> 
       k = i.
   Proof.
     intros k H.
     inversion H; subst; first [reflexivity | exfalso; auto with *].
   Qed.
   
   Lemma insertion_rel_snd_left : 
     forall k1 k2,
       k2 < i -> 
       insertion_rel i m k1 k2 -> 
       k1 = k2.
   Proof.
     intros k1 k2 H H0.
     assert (insertion_rel i m k2 k2) by now apply insertion_left.
     assert (injective (insertion_rel i m)) 
       as h_injective by now destruct insertion_rel_bijective.
     now apply (h_injective k2).
   Qed.
   
   Lemma insertion_rel_snd_middle :
     forall k, insertion_rel i m k i -> k = m.
   Proof.
     intros k H.
     inversion H; subst; first [reflexivity | exfalso; auto with *].
   Qed.
   
   Lemma insertion_rel_snd_right : 
     forall k1 k2,
       insertion_rel i m k1 k2 ->
       i < k2 -> 
       k2 = S k1.
   Proof.
     intros k1 k2 H H0.
     inversion H; subst; first [auto with * | exfalso; auto with *].
   Qed.
   
   (** order is preserved over most positions *)
   
   Lemma insertion_order : 
     forall k1 k2 k3 k4,
       insertion_rel i m k1 k2 ->
       insertion_rel i m k3 k4 -> 
       k1 < k3 -> 
       k3 <> m -> 
       k2 < k4.
   Proof.
     intros k1 k2 k3 k4 H H0 H1 H2.
     assert (k3 < m).
     {
       destruct insertion_rel_bijective.
       destruct (r k3 k4 H0); auto with *.
     }
     destruct (lt_dec k1 i).
     - assert (k1 = k2) by now apply insertion_rel_fst_left.
       destruct (lt_dec k3 i).
       + assert (k3 = k4) by now apply insertion_rel_fst_left.
         congruence.
       + assert (i <= k3 < m) by auto with *.
         assert (k4 = S k3) by
             now apply insertion_rel_fst_right.
             auto with *.
     - assert (i <= k1 < m) by auto with *.
       assert (k2 = S k1) by
           now apply insertion_rel_fst_right.
       assert (i <= k3 < m) by auto with *.
       assert (k4 = S k3) by
           now apply insertion_rel_fst_right.
           auto with *.
   Qed.
   
   Lemma insertion_order_rev : 
     forall k1 k2 k3 k4,
       insertion_rel i m k1 k2 ->
       insertion_rel i m k3 k4 -> 
       k2 < k4 -> 
       k2 <> i -> 
       k1 < k3.
   Proof.
     intros k1 k2 k3 k4 h_insert1 h_insert2 h_lt h_neq.
     destruct (lt_eq_lt_dec k2 i) as [[Ha | Ha] | Ha].
     - assert (k1 = k2) by now apply insertion_rel_snd_left.
       destruct (lt_eq_lt_dec k4 i) as [[Hb | Hb] | Hb].
       + assert (k3 = k4) by now apply insertion_rel_snd_left.
         congruence.
       + assert (k3 = m) by (apply insertion_rel_snd_middle; congruence).
         assert (k1 < m) by auto with *.
         congruence.
       + assert (k4 = S k3) by 
             now apply insertion_rel_snd_right.
             auto with *.
     - exfalso; intuition.
     - assert (k2 = S k1) by 
           now apply insertion_rel_snd_right.
       assert (i < k4) by auto with *.
       assert (k4 = S k3) by
           now apply insertion_rel_snd_right.
           auto with *.
   Qed.
   
   Lemma insertion_rel_lt :
     forall k k',
       insertion_rel i m k k' -> k <= m /\ k' <= m.
   Proof.
     intros k k' H.
     destruct insertion_rel_bijective.
     unfold restricted in r.
     apply r in H.
     auto with *.
   Qed.

End InsertionRelBasics.

Section Results.

  (** the relation insertion_rel maps elements between source and target lists of 
      insertion *)
  
  Lemma insertion_rel_insertion {A : Set} :
    forall i (l : list A) e (l' : list A),
      insertion i l e = Some l' ->
      forall k k', 
        insertion_rel i (length l) k k' ->
        nth_error (l ++ e::nil) k = nth_error l' k'.
  Proof.
    intros i s e s' H k k' H0.
    destruct (lt_dec k i); [ | destruct (eq_nat_dec k (length s)); [subst |]].
    - assert (k = k').
      {
        inversion H0; subst.
        - reflexivity.
        - exfalso; auto with *.
        - assert (k' <= length s).
          { 
            apply insertion_defined_rev with e.
            exists s'; assumption.
          }
          exfalso; auto with *.
      }
      subst.
      symmetry.
      replace (nth_error (s ++ e::nil) k') with (nth_error s k').
      now apply insertion_lt with (i) (e).
      assert (i <= length s).
      {
        apply insertion_defined_rev with e.
        exists s'; assumption.
      }
      assert (k' < length s) by auto with *.
      symmetry.
      now apply nth_error_append_left.
    - symmetry.
      assert (k' = i) by  (inversion H0; auto with *); subst.
      replace (nth_error (s ++ e::nil) (length s)) with (Some e) 
        by now (symmetry; apply nth_error_append_cons_eq).
      apply insertion_eq with s.
      assumption.
    - symmetry.
      destruct k'.
      {
        inversion H0; subst.
        intuition.
        intuition.
      }
      {
        inversion H0; subst.
        intuition.
        replace (nth_error (s ++ e::nil) k') with (nth_error s k')
          by now (symmetry; apply nth_error_append_left).
        now apply insertion_ge with i e.
        intuition.
      }
  Qed.
  

  Lemma insertion_ntherror :
    forall {A:Set} (s : list A) (e : A) (i : nat) (s' : list A) (e' : A), 
      insertion i s e == s' -> 
      ((exists k, nth_error s k == e') \/ e' = e) -> 
      exists k', nth_error s' k' == e'.
  Proof.
    intros A s e i s' e' h_insertion hyp. 
    destruct hyp as [[k Hk] | Ha ].
    - assert (k < length s). 
        eauto with nth_error. 
      assert (i <= length s) as Ha by eauto using insertion_defined_rev.
      destruct (insertion_rel_bijective i (length s) Ha) as [ _ _ h_applicative _ _].
      destruct h_applicative with k as [k' Hc]. 
      intuition.
      exists k'.
      rewrite <- Hk.
      replace (nth_error s k) with (nth_error (s++e::nil) k)
        by now apply nth_error_append_left.
      symmetry.
      now apply insertion_rel_insertion with i.
    - subst.
      exists i.
      eauto using insertion_eq.
  Qed.


  Lemma insertion_ntherror_rev :
    forall {A : Set} (s : list A) (e : A) (i : nat) (s' : list A) (e' : A),
      insertion i s e == s' ->
      (exists k', nth_error s' k' == e') -> 
      ((exists k, nth_error s k == e') \/ e' = e).
  Proof.
    intros A s e i s' e' h_insertion hyp.
    destruct hyp as [k' Hk'].
    destruct (eq_nat_dec k' i).
    - right.
      subst.
      apply insertion_eq in h_insertion.
      congruence.
    - left.
      assert (i <= length s) as Ha by eauto using insertion_defined_rev.
      destruct (insertion_rel_bijective i (length s) Ha) as [ _ _ _ _ h_surjective].
      assert (k' < S (length s)).
      {
        rewrite  (insertion_length _ i s e s' h_insertion).
        eauto with nth_error.
      }
      destruct h_surjective with k' as [k Hc].
      assumption.
      exists k.
      rewrite <- Hk'.
      replace (nth_error s k) with (nth_error (s ++ e::nil) k).
      now apply insertion_rel_insertion with i.
      assert (k <> length s).
      {
        intro; subst.
        assert (k' = i).
        now apply insertion_rel_fst_last with (length s).
        intuition.
      }
      assert (k < length s).
      {
        destruct (insertion_rel_bijective i (length s) Ha).
        destruct (r _ _ Hc).
        auto with *.
      }
      now apply nth_error_append_left.
  Qed.

End Results.