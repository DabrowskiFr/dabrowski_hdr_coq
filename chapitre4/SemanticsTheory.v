Require Import Lia Program Vector.
Require Import List.
Require Import Monad.
Require Import VectorTheory.
Require Import Syntax.
Require Import Semantics.
Require Import Coq.Relations.Relation_Operators.
Require Import Utf8.

Module SemanticsTheory (Import P : Process) (Import V : Vector P).

  Module Export S := Semantics P V.

  Lemma a : forall {A B C : Type}
    (f : B -> C) (g : A -> B) x, f (g x) = (f ∘ g) x.
  Admitted.

  Lemma replicate_fmap_snd : 
  forall s Σ, fmap snd ⦉ s, Σ ⦊ = Σ.
  Proof.
  intros s Σ.
  unfold replicate.
  rewrite (a (fmap snd)).
  rewrite fmap_comp.
  rewrite fmap_id.
  reflexivity.
  Qed.

Lemma reachable_trans : forall C C',
  reachable C (inl C') -> forall Γ, reachable C' Γ -> reachable C Γ.
Proof.
  intros C C' Hreachable.
  dependent induction Hreachable.
  - trivial.
  - intros.
    now constructor 3 with (C' := C').
  - intros.
    assert (reachable C'0 Γ) by eauto.
    now constructor 3 with (C' := C'0).
Qed.



  (** * Determinism of the semantics *)

  Lemma red_det :
    forall i c h γ,
      red i c h γ -> 
        forall h' (γ' : kstate), 
          red i c h' γ' -> h=h' /\ γ = γ'.
  Proof.
   intros i c h γ Hstep1.   
    induction Hstep1; intros h' γ' Hstep2;
      inversion Hstep2; intros; subst.
    - intuition.
    - intuition.
    - intuition.
    - destruct (IHHstep1_1 _ _ H4) as [Ha Hb].
      injection Ha; injection Hb; intros; subst.
      destruct (IHHstep1_2 _ _ H5) as [Hc Hd].
      injection Hc; intros; subst.
      intuition.
    - destruct (IHHstep1_1 _ _ H4).
      discriminate.
    - destruct (IHHstep1 _ _ H4).
      discriminate.
    - destruct (IHHstep1 _ _ H4).
      generalize (IHHstep1 _ _ H4); intro.
      injection H; injection H0; intros; subst.
      intuition.
    - destruct (IHHstep1 _ _ H7).
      injection H0; intros; subst.
      intuition.
    - exfalso; congruence.
    - exfalso; congruence.
    - destruct (IHHstep1 _ _ H7).
      injection H0; intros; subst.
      intuition.
    - destruct (IHHstep1 _ _ H6).
      injection H0; intros; subst.
      intuition.
    - exfalso; congruence.
    - exfalso; congruence.
    - intuition.
Qed.

Fact step_det_aux :
  ∀ (C C' : vconfiguration) (Σ : vstore),
  step C (inl C') ->
  step C (inr Σ) ->
  False.
Proof.
  intros C C' Σ Hstep1 Hstep2.
  inversion Hstep1; inversion Hstep2; subst.
  - destruct (H1 0 P.p_pos) as [γ [γ' [h [Ha [Hb Hc]]]]].
    destruct (H4 0 P.p_pos) as [σ [σ'[h2 [Hd [He Hf]]]]].
    rewrite Ha in Hd.
    injection Hd; intros; subst.
    assert (h = h2 /\ inl γ' = inr σ').
    eapply red_det.
    apply Hc.
    apply Hf.
    destruct H. subst.
    discriminate H0.
Qed.

  Lemma step_deterministic :
    ∀ (C : vconfiguration) (Γ Γ' : vkstate),
    step C Γ ->
    step C Γ' ->
    Γ =  Γ'.
  Proof.
    intros C Γ Γ' Hstep1 Hstep2.
    inversion Hstep1; inversion Hstep2; intros; subst.
    - f_equal.
      apply vect_extensionality.
      intros.
      destruct (H i H0) as [c1 [ γ1 [Ha [Hb [Hc Hd]]]]].    
      destruct (H2 i H0) as [c2 [ γ2 [He [Hf [Hg Hh]]]]].
      replace c2 with c1 in * by congruence.
      destruct (red_det _ _ _ _ Hd _ _ Hh).
      injection H3; intros; subst.
      rewrite Hc.
      rewrite Hg.
      reflexivity.
    - elim (step_det_aux _ _ _ Hstep1 Hstep2).
    - elim (step_det_aux _ _ _ Hstep2 Hstep1).
    - f_equal. 
      apply vect_extensionality.
      intros.
      destruct (H i H0) as [c1 [ γ1 [Ha [Hb [Hc Hd]]]]].    
      destruct (H2 i H0) as [c2 [ γ2 [He [Hf [Hg Hh]]]]].
      replace c2 with c1 in * by congruence.
      destruct (red_det _ _ _ _ Hd _ _ Hh).
      injection H3; intros; subst.
      rewrite Hc.
      rewrite Hg.
      reflexivity.
  Qed.

  (** Remove ?? *)
  Lemma step_empty :
    ∀ (v : vconfiguration) (v' : vkstate),
      p = 0 -> step v v'.
  Proof.
    intros v v' H__EQ.
    destruct v'; constructor; intros i H; exfalso; lia.
  Qed.
  
  (** ** Properties of replicate *)

  Lemma replicate_prop1 :
    forall (s s' : stmt) (vsigma : vstore)
           (sigma : store) (i : nat),
      π i ((replicate s) vsigma) = Some (s', sigma) ->
      s = s'.
  Proof.
    intros s s' vsigma sigma i H_get.
    unfold replicate in H_get.
    assert (i < p) by eauto with vector.
    assert (exists sigma', π i vsigma = Some sigma') as [sigma' H_sigma'] by eauto with vector.
    assert (π i (fmap (fun σ => (s,σ)) vsigma) = Some (s, sigma')).
    {
      rewrite π_fmap.
      rewrite H_sigma'.
      reflexivity.
    }
    unfold configuration in H_get.
    congruence.
  Qed.

  Lemma replicate_prop2 :
    forall (s s' : stmt) (vsigma : V.t store)
           (sigma : store) (i : nat),
      π i ((replicate s) vsigma) = Some (s', sigma) ->
      π i vsigma = Some sigma.
  Proof.
    intros s s' vsigma sigma i H_get.
    unfold replicate in H_get.
    assert (i < p) by eauto with vector.
    assert (exists sigma', π i vsigma = Some sigma') as [sigma' H_sigma'] by eauto with vector.
    assert (π i (fmap (fun σ => (s,σ)) vsigma) = Some (s, sigma')).
    {
      rewrite π_fmap.
      rewrite H_sigma'.
      reflexivity.
    }
    unfold configuration in H_get.
    congruence.
  Qed.
  
  Lemma replicate_prop3 :
    forall (s : stmt) (vsigma : V.t store)
           (sigma : store) (i : nat),
      π i vsigma = Some sigma ->
      π i ((replicate s) vsigma) = Some (s, sigma).
  Proof.
    unfold replicate.
    intros s vsigma sigma i H.
    rewrite π_fmap; rewrite H; reflexivity.
  Qed.

  #[export] Hint Resolve replicate_prop1 replicate_prop2 replicate_prop3 : replicate.
  
  Lemma replicate_inj :
    forall (s s' : stmt) (v v' : V.t store),
      0 < p ->
      replicate s v = replicate s' v' -> s' = s /\ v' = v.
  Proof.
    intros s s' v v' HLt HEq.
    split.
    - assert (exists sigma, π 0 v = Some sigma)
        as [sigma H_sigma] by eauto with vector.
      assert (π 0 (replicate s v) = Some (s, sigma)) by eauto with replicate.
      assert (π 0 (replicate s' v') = Some (s, sigma)) by congruence.
      eapply replicate_prop1; eauto.
    - apply vect_extensionality.
      intros i H.
      assert (exists sigma_i, π i v = Some sigma_i)
        as [sigma_i Hsigma_i] by eauto with vector.
      assert (exists sigma_i', π i v' = Some sigma_i')
        as [sigma_i' Hsigma_i'] by eauto with vector.
      assert (π i (replicate s v) = π i (replicate s' v') ) by congruence.
      rewrite replicate_prop3 with (sigma := sigma_i) in H0 by assumption.
      rewrite replicate_prop3 with (sigma := sigma_i') in H0 by assumption.
      injection H0; intros; subst.
      congruence.
  Qed.


  (** *** Properties over paths *)

  Fact topConditions :
    forall pid1 pid2 s sigma1 sigma2 n1 n2 w1 w2 X1 X2,
      red pid1 (s, sigma1) (n1,w1) (inr X1) ->
      red pid2 (s, sigma2) (n2,w2) (inr X2) ->
      n1 = n2.
  Proof.
    induction s; intros ? ? ? ? ? ? ? ? Hred1 Hred2;
      inversion Hred1; inversion Hred2; subst; eauto.
  Qed.
  
  Fact topConditions_lt :
    forall pid1 pid2 s sigma1 sigma2 n1 n2 w1 w2 X1 X2,
      red pid1 (s, sigma1) (n1,w1) (inr X1) ->
      red pid2 (s, sigma2) (n2,w2) (inl X2) ->
      n2 <= n1.
  Proof.
    induction s;
      intros sigma1 sigma2 n1 n2 w1 w2 X1 X2 Hred1 Hred2;
      try solve [inversion Hred1; inversion Hred2; subst; lia].
    - inversion Hred1; inversion Hred2; subst.
      + assert (n5 <= n3) by (eapply IHs2; eauto).
        replace n4 with n0 in * by (eapply topConditions; eauto).
        lia.
      + assert (n2 <= n0) by (eapply IHs1; eauto).
        lia.
  Qed.

  Fact topConditions_null :
    forall pid s sigma w gamma,
      red pid (s, sigma) (0, w) gamma -> w = nil.
  Proof.
    intros p s.
    induction s; intros ? ? ? Hred ;inversion Hred; subst; try trivial.
    - replace n1 with 0 in * by lia.
      replace n2 with 0 in * by lia.
      apply (IHs2 _ _ _ H6).
    - apply (IHs1 _ _ _ H5).
  Qed.
  
  Fact topConditions_nil :
    forall pid1 pid2 s sigma1 sigma2 m n w X1 X2,
      red pid1 (s, sigma1) (m, w) (inr X1) -> 
      red pid2 (s, sigma2) (n, nil) (inl X2) -> False.
  Proof.
    intros pid1 pid2 s.
    induction s; intros ? ? ? ? ? ? ? Hred1 Hred2;
      inversion Hred1; inversion Hred2; subst; eauto.
  Qed. 

(*   Lemma reduceA_continue : 
    forall nprocs s i sigma_i p_i sigma_i',
      reduceA nprocs i (s,sigma_i) p_i (inr sigma_i') ->
      forall j sigma_j p_j sigma_j',
        reduceA nprocs j (s, sigma_j) p_j (inr sigma_j') -> fst p_i = fst p_j.
  Proof.
    intros nprocs s i sigma_i p_i sigma_i' H_reduceA_i.
    dependent induction H_reduceA_i;
      intros j sigma_j p_j sigma_j' H_reduce_j;
      inversion H_reduce_j; subst;
        try reflexivity.
    assert (n1 = n0).
    {
      replace n0 with (fst (n0,w0)) by reflexivity.
      replace n1 with (fst (n1,w1)) by reflexivity.
      apply (IHH_reduceA_i1 _ _ _ (refl_equal _) (refl_equal _) _ _ _ _ H4).
    }
    assert (n2 = n3).
    {
      replace n3 with (fst (n3,w3)) by reflexivity.
      replace n2 with (fst (n2,w2)) by reflexivity.
      apply (IHH_reduceA_i2 _ _ _ (refl_equal _) (refl_equal _) _ _ _ _ H5).
    }
    subst; reflexivity.
  Qed.*)

  Lemma seq1_sameAction :
  ∀ s1 s2 i j (σ__i σj : store) h hi' hj' γi σj' γi' γj,
    red i (Seq s1 s2, σ__i) h (inl γi) ->
    red j (Seq s1 s2, σj) h (inl γj) ->
    red i (s1, σ__i) hi' (inl γi') ->
    red j (s1, σj) hj' (inr σj') -> False.
  Proof.
    intros s1 s2 i j σi σj h hi' hj' γi σj' γi' γj H H0 H1 H2.
    inversion H; subst.
    - destruct (red_det _ _ _ _ H1 _ _ H8); discriminate.
    - destruct (red_det _ _ _ _ H1 _ _ H7).
      injection H4; intros; subst; clear H4 H7.
      inversion H0; subst.
      * assert (n2 = 0).
        {
          assert (n1 + n2 <= n1) by eauto using topConditions_lt.
          lia.
        }
        subst.
        replace ((n1 + 0)%nat) with n1 in * by lia.
        replace w with (@nil (nat * choice)) in * by (symmetry; eauto using topConditions_null).
        eauto using topConditions_nil.
      * destruct (red_det _ _ _ _ H4 _ _ H2); discriminate.
  Qed.
  
  Lemma sameAction :
    forall pid1 s sigma1 p X1,
      red pid1 (s,sigma1) p X1 ->
      forall pid2 sigma2 X2,
        red pid2 (s,sigma2) p X2 ->
        (exists st1 st2, X1 = inl st1 /\ X2 = inl st2) \/
        (exists sigma_1' sigma_2', X1 = inr sigma_1' /\ X2 = inr sigma_2').
  Proof.
    intros pid1 s sigma1 p X1 Ha;
      dependent induction Ha;
      intros pid2 sigma2 X2 Hb;
      try solve [inversion Hb; subst; eauto].
    - inversion Hb; subst.
      + assert (n0 = n1) by (eapply topConditions; eauto).
        replace n3 with n2 in * by lia.
        apply IHHa2 with s2 σ' pid2 σ'0.
        reflexivity.
        apply H6.
      + exfalso.
        assert (n1 + n2 <= n1) by (eapply topConditions_lt; eauto).
        replace n2 with 0 in * by lia.
        replace ((n1 +0)%nat) with n1 in * by lia.
        assert (w2 = (@nil (nat * choice))) as HEq3 by (eapply topConditions_null;eauto).
        rewrite HEq3 in *.
        apply (topConditions_nil _ _ _ _ _ _ _ _ _ _ Ha1 H5).
    - inversion Hb; subst.
      + exfalso.
        assert (n1 + n2 <= n1) by (eapply topConditions_lt; eauto).
        replace n2 with 0 in * by lia.
        replace ((n1 +0)%nat) with n1 in * by lia.
        assert (w = (@nil (nat * choice))) as HEq3 by (eapply topConditions_null;eauto).
        rewrite HEq3 in *.
        apply (topConditions_nil _ _ _ _ _ _ _ _ _ _ H5 Ha).
      + left.
        eauto.
  Qed.

  Lemma sameContinuation :
    forall  pid1 pid2 s sigma1 sigma2 p s1 s2 sigma1' sigma2',
      red pid1 (s,sigma1) p (inl (s1, sigma1')) ->
      red pid2 (s,sigma2) p (inl (s2, sigma2')) ->
      s1 = s2.
  Proof.
    intros pid1 pid2 s sigma1 sigma2 p s1 s2 sigma1' sigma2' Hred1 Hred2.
    revert pid2 sigma2 s2 sigma2' Hred2.
    dependent induction Hred1.
    - (* Hred1 : reduceA_skip *)
      intros pid2 sigma2 s3 sigma2' Hred2.
      now inversion Hred2.
    - (* reduceA_seq1 *)
      intros pid2 sigma2 s3 sigma2' Hred2.
      inversion Hred2; subst.
      +(* Hred2 : reduceA_seq1 *)
        assert (n0 = n1) by (eapply topConditions; eauto).
        replace n3 with n2 in * by lia.
        eapply IHHred1_2.
        reflexivity.
        f_equal.
        reflexivity.
        apply H6.
      + (* Hred2 : reduceA_seq2 *)
        exfalso.
        assert (w2 = (@nil (nat * choice))) as HEq3.
        {
          replace n2 with 0 in * by
              (assert (n1 + n2 <= n1) by eauto using topConditions_lt; lia).
          eauto using topConditions_null.
        }
        subst.
        eapply topConditions_nil; eauto.
    - (* Hred1 : reduceA_seq2 *)
      intros pid2 sigma2 s3 sigma2' Hred2.
      inversion Hred2; subst.
      + (* Hred2 : reduceA_seq1 *)
        exfalso.
        assert (w = (@nil (nat * choice))) as HEq3.
        {
          replace n2 with 0 in * by
            (assert (n1 + n2 <= n1) by eauto using topConditions_lt; lia).
          eauto using topConditions_null.
        }
        subst.
        eauto using topConditions_nil.
      + (* Hred2 : reduceA_seq2 *)
        f_equal.
        eapply IHHred1.
        reflexivity.
        f_equal.
        reflexivity.
        apply H0.
    - (* Hred1 : reduceA_if1 *)
      intros pid2 sigma2 s3 sigma2' Hred2.
      inversion Hred2; subst; eauto.
    - (* Hred1 : reduceA_if2 *)
      intros pid2 sigma2 s3 sigma2' Hred2.
      inversion Hred2; subst; eauto.
    - (* Hred1 : reduceA_while1 *)
      intros pid2 sigma2 s3 sigma2' Hred2.
      inversion Hred2; subst; eauto.
  Qed.

  Lemma same_path_same_shape :
  forall i j s σi σj p γi γj,
    red i (s, σi) p γi  -> 
    red j (s, σj) p γj  ->
    (exists σi σj, γi = inr σi /\ γj = inr σj) \/
    (exists s' σi' σj', γi = inl (s', σi') /\ γj = inl (s', σj')).
  Proof.
    intros.
    destruct (sameAction _ _ _ _ _ H _ _ _ H0) as [Ha | Ha].
    - destruct Ha as [[si' σi'] [[sj' σj'] [Hb Hc]]].
      subst.
      right.
      generalize (sameContinuation _ _ _ _ _ _ _ _ _ _ H H0); intro.
      subst.
      exists sj', σi', σj'.
      split; reflexivity.    
    - destruct Ha as [σi' [σj' [Hb Hc]]].
      subst.
      left.
      eauto. 
  Qed.

  (* Lemma step_inl :
    forall (v : vconfiguration) (v' : vkstate),
      step v v' -> exists st, v = st.
  Proof.
    intros v v' H.
    inversion H; eauto.
  Qed.
   *)
  (* Lemma reachable_inl :
    forall (v : vconfiguration) (v' : vkstate),
        reachable v v' ->
      inl v = v' \/ exists st, v = st.
  Proof.
    intros v v' H.
    induction H.
    - right; destruct x; [eauto| inversion H].
    - left; reflexivity.
    - destruct IHclos_refl_trans1; destruct IHclos_refl_trans2.
      + left; congruence.
      + subst; right; eauto.
      + subst; right; eauto.
      + right.
        assumption.
  Qed. *)

  (* Lemma reachable_inr :
    forall (v : V.t (stmt * store)) vsigma,
      reachable (inl v) (inr vsigma) ->
      exists v', reachable (inl v) (inl v') /\ step (inl v') (inr vsigma).
  Proof.
    intros v vsigma H.
    dependent induction H.
    - exists v.
      split.
      constructor 2.
      assumption.
    - destruct (reachable_inl _ _ H0); subst.
      + destruct (IHclos_refl_trans1 _ _ (refl_equal _) (refl_equal _)).
        exists x.
        assumption.
      + destruct H1; subst.
        destruct (IHclos_refl_trans2 _ _ (refl_equal _) (refl_equal _)).
        exists x0.
        split.
        constructor 3 with (y:= inl x).
        assumption.
        apply H1.
        apply H1.
  Qed. *)

  (* Lemma reachable_inl_x :
    ∀ (Σ : V.t (store)) (x : V.t (stmt * store) + V.t store),  
      reachable (inr Σ) x -> x = inr Σ.
  Proof.
    intros Σ x H.
    dependent induction H.
    - inversion H.
    - reflexivity.
    - eauto.
  Qed. *)

  (** *** Auxiliary results to deal with the sequence at the global level*)
  
  Definition parcomp (f : stmt -> stmt) :
    vconfiguration -> vconfiguration :=
    fmap (fun p => (f (fst p), snd p)).

  Lemma parseq_prop1 : forall (s1 s2 : stmt) (v : V.t store),
      replicate (Seq s1 s2) v = parcomp (fun s0 => Seq s0 s2) (replicate s1 v).
  Proof.
    intros s1 s2 v.
    unfold replicate, parcomp.
    rewrite vectmap_compose.
    unfold merge.
    apply vect_extensionality.
    intros i H.
    do 2 rewrite vectmap_eq; reflexivity.
  Qed.

  Fact step_seq :
    forall (v v' : vconfiguration)  s2,
      step v (inl v') ->
      step ((parcomp (fun s : stmt => Seq s s2) v))
           (inl (parcomp (fun s : stmt => Seq s s2) v')).
  Proof.
    intros v v' s2 H_step.
    inversion H_step; subst.
    constructor 1.
    intros pid H_lt.
    destruct (H1 pid H_lt) as [st_i [st_i' [p [HA [HB HC]]]]]; clear H1.
    destruct st_i as [s_i sigma_i], st_i' as [s_i' sigma_i'].
    exists (Seq s_i s2, sigma_i), (Seq s_i' s2, sigma_i'), p.
    unfold parcomp.
    rewrite vectmap_eq.
    rewrite vectmap_eq.        
    unfold configuration in *.
    rewrite HA.
    rewrite HB.
    split.
    reflexivity.
    split.
    reflexivity.
    destruct p.
    apply red_seq2.
    apply HC.
  Qed.

  Fact reachable_seq :
    ∀ (v v' : vconfiguration),
      reachable v (inl v') ->
      forall s2,
        reachable ((parcomp (fun s => Seq s s2) v))
                  (inl (parcomp (fun s => Seq s s2) v')).
  Proof.
    intros v v' H s2.
    dependent induction H.
    - constructor 1.
    - constructor 2.  
      apply step_seq.
      assumption.
    - assert (@inl vconfiguration vstore v' ~= @inl vconfiguration vstore v') as Ha by reflexivity.
      generalize (IHreachable _ Ha s2); intro.
      constructor 3 with (parcomp (λ s : stmt, s;; s2) C').
      apply step_seq.
      apply H.
      apply H1.
  Qed.

  Lemma step_reduce :
  forall (C : vconfiguration) Σ s Γ,
    step C (inr Σ) ->
    step (replicate s Σ) Γ ->
    step (parcomp (fun s' => Seq s' s) C) Γ.
  Proof.
    intros C Σ s Γ H_step1 H_step2.
    - inversion H_step1; inversion H_step2; clear H_step1; clear H_step2; subst.
      + constructor.
        intros i Hp.
        destruct (H1 i Hp) as [st_i [sigma_i [p_i [HA [HB HC]]]]]; clear H1.
        destruct (H2 i Hp) as [st_i' [st_i'' [p_i' [HD [HE HF]]]]]; clear H2.
        destruct st_i as (s_i2, sigma_i2), st_i' as (s_i2', sigma_i2').
        destruct p_i as [n_i w_i], p_i' as [n_i' w_i'].
        specialize (replicate_prop1 _ _ _ _ _ HD) as HU.
        specialize (replicate_prop2 _ _ _ _ _ HD) as H0.
        rewrite HB in H0.
        injection H0; intros; subst; clear H0.
        exists (Seq s_i2 s_i2', sigma_i2), st_i'', ((n_i + n_i')%nat, w_i').
        split.
        unfold parcomp.
        rewrite vectmap_eq.
        unfold configuration in *.
        rewrite HA.
        reflexivity.
        split.
        assumption.
        apply red_seq1 with (σ' := sigma_i2') (w1 := w_i).
        assumption.
        assumption.
      + constructor.
        intros i Hp.
        destruct (H1 i Hp) as [st_i [sigma_i [p_i [HA [HB HC]]]]]; clear H1.
        destruct (H2 i Hp) as [st_i' [st_i'' [p_i' [HD [HE HF]]]]]; clear H2.
        destruct st_i as (s_i2, sigma_i2), st_i' as (s_i2', sigma_i2').
        destruct p_i as [n_i w_i], p_i' as [n_i' w_i'].
        specialize (replicate_prop1 _ _ _ _ _ HD) as HU.
        specialize (replicate_prop2 _ _ _ _ _ HD) as H0. 
        rewrite HB in H0.
        injection H0; intros; subst; clear H0.
        exists (Seq s_i2 s_i2', sigma_i2), st_i'', ((n_i + n_i')%nat, w_i').
        split.
        unfold parcomp.
        rewrite vectmap_eq.
        unfold configuration in *.
        rewrite HA.
        reflexivity.
        split.
        assumption.
        apply red_seq1 with (σ' := sigma_i2') (w1 := w_i).
        assumption.
        assumption.
  Qed.

  (** *** Deadlock freeness *)

  Lemma deadlock_free_dec : 
    forall s, {deadlock_free s} + {~ deadlock_free s}.
  Admitted.

(*  Definition reachable' := clos_trans _ step. *)

  (* Lemma clos_trans_reachable :
    forall x y,
      clos_trans _ step x y -> reachable x y.
  Proof.
    intros x y H.
    induction H.
    - constructor 1; assumption.
    - constructor 3 with y; assumption.
  Qed. *)

  (* Lemma reachable_clos_trans :
    forall x y,
      reachable x y -> clos_trans _ step x y \/ x = y.
  Proof.
    intros x y H.
    induction H.
    - left.
      constructor 1.
      assumption.
    - right.
      reflexivity.
    - destruct IHclos_refl_trans1, IHclos_refl_trans2; subst.
      + left.
        constructor 2 with y; assumption.
      + left; assumption.
      + left; assumption.
      + right; reflexivity.
  Qed. *)

  (* Lemma step_reachable' :
      forall (C : vconfiguration ) Σ s Γ,
        step C Γ ->
        clos_trans _ step ((replicate s Σ)) Γ ->
        clos_trans _ step ((parcomp (fun s' => Seq s' s) Σ)) Γ.
  Proof.
    intros vst vsigma s2 v H H0.
    dependent induction H0.
    - constructor 1.
      now apply step_reduce with (vsigma := vsigma).
    - constructor 2 with (y:=y).
      apply IHclos_trans1 with (vsigma := vsigma).
      assumption.
      reflexivity.
      assumption.
  Qed.*)
  
  (* Lemma reachable'_inl :
    forall v v',
      clos_trans _ step v v' ->
      exists st, v = inl st.
  Proof.
    intros v v' H.
    induction H.
    - destruct x; [eauto| inversion H].
    - destruct IHclos_trans1; destruct IHclos_trans2.
      eauto.
  Qed.
  *)
  (*
  Fact reachable'_seq :
    forall v v',
      clos_trans _ step (inl v) (inl v') ->
      forall s2,
        clos_trans _ step (inl (parcomp (fun s => Seq s s2) v))
                   (inl (parcomp (fun s => Seq s s2) v')).
  Proof.
    intros v v' H s2.
    dependent induction H.
    - constructor 1.
      apply step_seq.
      assumption.
    - destruct (reachable'_inl _ _ H0) as [st HEq]; subst.
      econstructor 2.
      apply IHclos_trans1.
      reflexivity.
      reflexivity.
      apply IHclos_trans2.
      reflexivity.
      reflexivity.
  Qed.
*)
  (*
  Lemma reachable_seq_seq :
    forall (vst : V.t (stmt * store)) vsigma s2 v,
      reachable (inl vst) (inr vsigma) ->
      clos_trans _ step (inl (replicate s2 vsigma)) v ->
      clos_trans _ step (inl (parcomp (fun s => Seq s s2) vst)) v.
  Proof.
    intros vst vsigma s2 v H H0.
    destruct (reachable_clos_trans _ _ H); clear H.
    dependent induction H1.
    + 
      apply step_reachable' with (vsigma := vsigma).
      assumption.
      assumption.
    + assert (reachable y (inr vsigma)).
      {
        apply clos_trans_reachable.
        assumption.
      }
      destruct (reachable_inl  _ _ H); subst.
      * generalize (IHclos_trans1 _ _ H0 (refl_equal _) (refl_equal _)).
        easy.
      * destruct H1; subst.
        generalize (IHclos_trans2 _ _ H0 (refl_equal _) (refl_equal _)).
        intro.
        constructor 2 with (inl (parcomp (fun s => Seq s s2) x)).
        apply reachable'_seq.
        assumption.
        assumption.
    + discriminate.
  Qed.
*)

(*  
  Lemma reachable'_reachable :
    forall x y,
      reachable' x y -> reachable x y.
  Proof.
    intros x y H.
    induction H.
    - constructor 1; assumption.
    - constructor 3 with y; assumption.
  Qed.

  Lemma reachable_reachable' :
    forall x y,
      reachable x y -> reachable' x y \/ x = y.
  Proof.
    intros x y H.
    induction H.
    - left.
      constructor 1.
      assumption.
    - right.
      reflexivity.
    - destruct IHclos_refl_trans1, IHclos_refl_trans2; subst.
      + left.
        constructor 2 with y; assumption.
      + left; assumption.
      + left; assumption.
      + right; reflexivity.
  Qed.
*)

    (*

*)

  (*
 

  

  

  *)
  (*  Lemma reduceA_seq_seq :
    forall nprocs i s1 s2 s3 v sigma p,
      reduceA nprocs i (Seq (Seq s1 s2) s3, sigma) p v ->
      reduceA nprocs i (Seq s1 (Seq s2 s3), sigma) p v
  .


  Lemma reduceA_det :
    forall nprocs i st p p' v v',
      reduceA nprocs i st p v ->
      reduceA nprocs i st p' v' -> p = p' /\ v = v'.

*)


(*
  Lemma reachable'_inr :
    forall nprocs v vsigma,
      reachable' nprocs (inl v) (inr vsigma) ->
      exists v', reachable' nprocs (inl v) (inl v') /\ step nprocs (inl v') (inr vsigma).
  Proof.
    intros nprocs v vsigma H.
    dependent induction H.
    - exists v.
      split.
      constructor 2.
      assumption.
    - destruct (reachable_inl _ _ _ H0); subst.
      + destruct (IHclos_refl_trans1 _ _ (refl_equal _) (refl_equal _)).
        exists x.
        assumption.
      + destruct H1; subst.
        destruct (IHclos_refl_trans2 _ _ (refl_equal _) (refl_equal _)).
        exists x0.
        split.
        constructor 3 with (y:= inl x).
        assumption.
        apply H1.
        apply H1.
  Qed.
 *)

  (* Require Import Monad.

   *)
  
  



  
  

  (* Lemma reachable_set :
    forall nprocs vsigma x0 e vsigma',
      mapP (fun i sigma => update sigma x0 (eval nprocs i sigma e)) (VT.map Some vsigma)
      = VT.map Some vsigma' ->
      reachable nprocs (inl (replicate (Assign x0 e) vsigma)) (inr vsigma').
  Proof.
  *)
  


  (* Lemma step_deterministic :
    ∀ (X Y Z : V.t (stmt * store) + V.t store),
      step X Y -> step X Z -> Y = Z. 
 easy *)

End SemanticsTheory.
