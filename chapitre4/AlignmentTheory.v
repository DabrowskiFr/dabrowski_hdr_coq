Require Import Vector.
Require Import VectorTheory.
Require Import Syntax.
Require Import Semantics.
Require Import SemanticsTheory.
Require Import Alignment.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Operators.
Require Import Lia.
Require Import Utf8.
Require Import List.
Require Import Monad.

Open Scope program_scope.

Module AlignmentTheory (Import P : Process) (Import V : Vector P).

  Module Export A := Alignment P V.

  #[export] Hint Constructors red : red.

  Open Scope stmt_scope.

  Notation alltrue Σ b :=
    (∀ i σ__i, π i Σ = Some σ__i -> beval b i σ__i = true).

  Notation allfalse Σ b :=
    (∀ i σ__i, π i Σ = Some σ__i -> beval b i σ__i = false).

  (** ** Preservation of textual alignement *)

  Proposition step_preserves_alignement : 
    forall s Σ, aligned_for s Σ -> 
      forall s' Σ',
        step (replicate s Σ) (inl (replicate s' Σ')) -> 
        aligned_for s' Σ'.  
  Proof.
    intros s Σ H_aligned s' Σ' H_step; unfold aligned_for.
    intros C H_reachable.
    assert (⦉ s, Σ ⦊ ⟹ inl C)
      by now constructor 3 with (C' := ⦉ s', Σ' ⦊).
    eauto.
  Qed.

  Proposition reachability_preserves_alignement :
    forall s Σ, aligned_for s Σ  ->
      forall s' Σ',
        reachable (replicate s Σ) (inl (replicate s' Σ')) -> 
        aligned_for s' Σ'.
  Proof.
    intros s Σ H_aligned s' Σ' Hreachable; unfold aligned_for.
    intros C H_reachable'.
    assert (reachable (replicate s Σ) (inl C)) as HE
      by eauto using reachable_trans.
    eauto.
  Qed.

  (** *** Preservation of replication for aligned programs *) 

  Proposition step_preserves_replication :
    forall s Σ, aligned_for s Σ ->
      forall (C : vconfiguration),
        step (replicate s Σ) (inl C) ->
        exists s', C = replicate s' (fmap snd C).
  Proof.
    intros s Σ Haligned C Hstep.
    generalize P.p_pos; intro H0.
    (* pick the statement at process 0 *)
    assert (exists c0, π 0 C = Some c0) as [[s0' σ] HEq]
      by eauto with vector.
    exists s0'.
    (* by extensionality *)
    apply vect_extensionality.
    intros i Hi.
    (* by hypothesis Hstep, processes 0 and i reduces *)
    inversion Hstep as [? ? Hreds | ]; clear Hstep; subst.
    destruct (Hreds 0 H0) as [[s0 σ0] [[s0'' σ0''] [h0 [Ha [Hb Hc]]]]].
    destruct (Hreds i Hi) as [[si σi] [[si' σi'] [hi [Hd [He Hf]]]]].
    clear Hreds.
    rewrite Hb in HEq; injection HEq; clear HEq; intros; subst.
    (* simple rewriting *)
    assert (π i ⦉ s0', fmap snd C ⦊ = Some (s0', σi')) as Hsimp.
    {
      rewrite replicate_prop3 with (sigma := σi').
      reflexivity.
      rewrite vectmap_eq.
      unfold configuration in *.
      rewrite He; reflexivity.
    }
    rewrite Hsimp; clear Hsimp.
    rewrite He.
    do 2 f_equal.
    (* by definition of replicate we have s0 = si = s*)
    replace s0 with s in * by (eapply replicate_prop1; eauto).
    replace si with s in * by (eapply replicate_prop1; eauto).
     (* by alignement we have hi = h0 *)
    assert (hi = h0).
    {
      assert (⦉ s, Σ ⦊ ⟹ inl ⦉ s, Σ ⦊) as Hrefl by constructor 1.
      unfold aligned_for in Haligned.
      now apply 
      (Haligned _ Hrefl i 0 (s,σi) (s,σ0) 
        hi h0 (inl (si',σi')) (inl (s0',σ))).
    }
    subst.
    (* By Lemma sameContinuation it comes si' = s0' *)
    eauto using sameContinuation.
  Qed.

  Proposition reachability_preserves_replication : 
    forall s Σ (vst : vconfiguration), 
      aligned_for s Σ -> 
      reachable (replicate s Σ) (inl vst) -> 
      exists s', vst = replicate s' (fmap snd vst).
  Proof.
    intros s Σ vst H_aligned H_reachable.
    dependent induction H_reachable.
    -   exists s.
        rewrite replicate_fmap_snd.
        reflexivity.
    - eapply step_preserves_replication.
      apply H_aligned.
      apply H.
    - destruct (step_preserves_replication _ _ H_aligned _ H) as [s' Hs'].
      assert (aligned_for s' (fmap snd C')).
      {
        eapply reachability_preserves_alignement.
        apply H_aligned.
        rewrite <- Hs'.
        constructor 2.
        apply H.
      }
      assert (@inl vconfiguration vstore vst ~= @inl vconfiguration vstore vst).
      reflexivity.
      generalize (IHH_reachable _ _ _ H0 Hs' H1);
        intro.
      apply H2.
  Qed.    

(** *** Textual alignement ensures deadlock freenes *)

  Theorem deadlock_free_if_aligned : 
    forall (s : stmt) (Σ : t store) (vst : vconfiguration),
      aligned_for s Σ -> 
      reachable (replicate s Σ) (inl vst) -> 
      ~ deadlock vst.
  Proof.
    intros s Σ vst H_aligned H_reachable H_deadlock.
    assert (exists s', vst = replicate s' (fmap snd vst)) as [s' HEq].
    {
      apply (reachability_preserves_replication _ _ _ H_aligned H_reachable).
    }
    subst.
    destruct H_deadlock as 
      [i [ j [ H_neq [[[si σi] [pi [γ [Hu Hv]]]] 
      [[sj σj] [pj [σ [Hu' Hv']]]]]]]].
    assert (pi = pj).
    {
      unfold aligned_for in H_aligned.
      apply (H_aligned vst H_reachable _ _ _ _ _ _ _ _ Hu Hu' Hv Hv').
    }
    rewrite HEq in Hu.
    rewrite HEq in Hu'.
    generalize (replicate_prop1 _ _ _ _ _ Hu).
    generalize (replicate_prop1 _ _ _ _ _ Hu').
    intros; subst.
    destruct (same_path_same_shape _ _ _ _ _ _ _ _ Hv Hv').
    destruct H as [σi' [σj' [Ha1 Ha2]]].
    discriminate.
    destruct H as [s' [σi' [σj' [Ha1 Ha2]]]].
    discriminate.
  Qed.

(** *** Alignment preserved through steps *)  

(*  Lemma aligned_skip : ∀ Σ, aligned_for SKIP Σ.
  Proof. 
    intros Σ.
    unfold aligned_for.
    intros vst H i j st_i st_j p_i p_j st_i' st_j' H0 H1 H2 H3.
    *)

(*  Lemma aligned_assign : ∀ Σ x e, aligned_for (x::=e) Σ.
  Proof.
    intros Σ.
    unfold aligned_for.
    intros vst H i j st_i st_j p_i p_j st_i' st_j' H0 H1 H2 H3.
    *)

(*  Lemma aligned_sync : ∀ Σ, aligned_for SYNC Σ.
  Proof.
  intros Σ.*)

(*  Lemma aligned_seq1 : forall s1 s2 Σ,
    aligned_for (s1;;s2) Σ -> aligned_for s1 Σ.
  Proof.*)


(*  Lemma aligned_seq2 : forall s1 s2 (Σ Σ' : V.t store),
    aligned_for (s1;;s2) Σ -> ⦉s1, Σ⦊ ⟹ inr Σ' ->
    aligned_for s2 Σ'.*)
  
(*  Lemma aligned_if1 :
    ∀ (Σ : V.t store) b s1 s2,
      alltrue Σ b ->
      aligned_for (If b s1 s2) Σ ->
      aligned_for s1 Σ.
  Proof.*)

(*  Lemma aligned_if2 : 
    ∀ (Σ : V.t store) b s1 s2,
      (∀ i σ_i, π i Σ = Some σ_i -> beval b i σ_i = false) ->
      aligned_for (If b s1 s2) Σ ->
      aligned_for s2 Σ.
  Proof.*)


(*  Lemma aligned_while :
  ∀ (Σ : V.t store) b s,
    aligned_for (While b s) Σ ->
    alltrue Σ b->
    (∀ (i : nat) (σ_i : store), π i Σ = Some σ_i → beval b i σ_i = true) ->
    aligned_for (Seq s (While b s)) Σ.
  Proof.*)

End AlignmentTheory.



 (* Notation alltrue Σ b :=
    (∀ i σ__i, π i Σ = Some σ__i -> beval b i σ__i = true).

  Notation allfalse Σ b :=
    (∀ i σ__i, π i Σ = Some σ__i -> beval b i σ__i = false).

  Lemma alltrue_dec :
    ∀ Σ b, alltrue Σ b \/ ¬ alltrue Σ b.
  Proof.
   easy *)

  (* Lemma allfalse_dec :
    ∀ Σ b, allfalse Σ b \/ ¬ allfalse Σ b.
  Proof.
   (* easy *)

  Lemma select_alltrue :
    ∀ (Σ : V.t store) b,
      alltrue Σ b ->
      select (beval b) (fmap Some Σ) = fmap Some Σ.
   (* easy *)
  
  Lemma select_alltrue_neg :
    ∀ (Σ : V.t store) b,
      alltrue Σ b ->
      select (beval (Not b)) (fmap Some Σ)= make (fun _ =>  None).
  (* easy *)

  Lemma select_allfalse :
    ∀ (Σ : V.t store) b,
      allfalse Σ b ->
      select (beval (Not b)) (fmap Some Σ) = fmap Some Σ.
 (* easy *)

  Lemma select_allfalse_neg :
    ∀ (Σ : V.t store) b,
      allfalse Σ b ->
      select (beval b) (fmap Some Σ) = make (fun _ =>  None).
 (* easy *)

  Lemma selecti_true:
    ∀ (b : bexpr) (Σ : V.t (option store)) (i : nat) (σ_i : store), 
      π i Σ = Some (Some σ_i)
      → beval b i σ_i = true → π i (select (beval b) Σ) = Some (Some σ_i).
  Proof.
    intros b Σ i σ_i H__EQ1 H5.
  (* easy *)

  Lemma selecti_false:
    ∀ (b : bexpr) (Σ : V.t (option store)) (i : nat) (σ_i : store), 
      π i Σ = Some (Some σ_i)
      → beval b i σ_i = false
      → π i (select (beval (Not b)) Σ) = Some (Some σ_i).
  Proof.
    intros b Σ i σ_i H__EQ1 H5.
 (* easy *)

  Lemma selecti_neg_pos:
    ∀ (b : bexpr) (Σ : V.t (option store)) (i : nat) (σ_i : store), 
      π i (select (beval (Not b) )Σ) = Some (Some σ_i)
      → π i (select (beval b) Σ) = Some None.
  Proof.
    intros b Σ i σ_i HE.
 (* easy *)

  Lemma selecti_pos_neg:
    ∀ (b : bexpr) (Σ : V.t (option store)) (i : nat) (σ_i : store), 
      π i (select (beval b) Σ) = Some (Some σ_i)
      → π i (select (beval (Not b)) Σ) = Some None.
  Proof.
    intros b Σ i σ_i HE.
 (* easy *)

  Lemma selecti_none_pos:
    ∀ (b : bexpr) (Σ : V.t (option store)) (i : nat), 
      π i Σ = Some None → π i (select (beval b) Σ) = Some None.
  Proof.
    intros b Σ i HE.
 (* easy *)

  Lemma selecti_none_neg:
    ∀ (b : bexpr) (Σ : V.t (option store)) (i : nat), 
      π i Σ = Some None
      → π i (select (beval (Not b)) Σ) = Some None.
  Proof.
    intros b Σ i HE.
 easy *)
  

  
  
  (* Lemma step_replicate_join_inl :
    ∀ s (Σ : t store) (Γ : t (stmt * store)) ,
      (∀ i, i < p -> ∃ σ γ h,
            π i Σ = Some σ
            /\ π i Γ = Some γ /\
            (red i (s, σ) h (inl γ))) -> (⦉s, Σ⦊) ⟶ (inl Γ).
  Proof.
    intros s Σ Γ H.
    constructor.
    intros i H0.
    destruct (H i H0) as [σ [γ [h [HA [HB HC]]]]].
    exists (s, σ), γ, h; eauto with replicate.
  Qed. *)


(*  Lemma step_replicate_join_inr :
    ∀ s (Σ : V.t store) (Σ' : V.t store) ,
      (∀ i, i < p -> ∃ σ σ' h,
            π i Σ = Some σ
            /\ π i Σ' = Some σ' /\
            red i (s, σ) h (inr σ')) ->
      (⦉s, Σ⦊ ⟶ inr Σ').
  Proof.
    intros s Σ Σ' H.
    constructor.
    intros i H0.
    destruct (H i H0) as [σ [γ [h [HA [HB HC]]]]].
    exists (s, σ), γ, h; eauto with replicate.
  Qed.*)


  (* Lemma step_replicate_skip :
    ∀ (Σ : V.t store),
      (⦉SKIP, Σ⦊ ⟶ inr Σ).
  Proof.
    intros Σ.
    apply step_replicate_join_inr.
    intros i H__lt.
    assert (exists σ, π i Σ = Some σ) as [σ H__Eq] by eauto with vector. 
    eauto 6 with red.
  Qed. *)

  (* Lemma reachable_replicate_skip :
    forall (Σ : t store), ⦉SKIP, Σ⦊ ⟹ inr Σ.
  Proof.
    intros vsigma.
    constructor 2.
    apply step_replicate_skip.
  Qed.

  Lemma aligned_skip : ∀ Σ, aligned_for SKIP Σ.
  Proof. 
    intros Σ.
    unfold aligned_for.
    intros vst H i j st_i st_j p_i p_j st_i' st_j' H0 H1 H2 H3.
   easy *)

  (* Notation updateall Σ x e :=
    (mapi (fun i σ => update σ x (eval e i σ)) Σ). *)
  
  (* Lemma step_replicate_assign : ∀ (Σ : V.t store) x e,
      (⦉ x ::= e, Σ⦊ ⟶ inr (updateall Σ x e)).
  Proof.
    intros Σ x e.
    apply step_replicate_join_inr.
    intros i H__lt.
    assert (exists σ, π i Σ = Some σ) as [σ HA] by eauto with vector.
    rewrite vectmapi_eq by assumption.
    rewrite HA.
    simpl.
    eauto 7 with red.
  Qed. *)

  (* Lemma reachable_replicate_assign : ∀ (Σ : V.t store) x e,
      (⦉ x ::= e, Σ⦊ ⟹ inr (updateall Σ x e)).
  Proof.
    intros Σ x e.
    constructor 2.
    apply step_replicate_assign.
  Qed.


  Lemma aligned_assign : ∀ Σ x e, aligned_for (x::=e) Σ.
  Proof.
    intros Σ.
    unfold aligned_for.
    intros vst H i j st_i st_j p_i p_j st_i' st_j' H0 H1 H2 H3.
 easy *)

  (* Lemma step_replicate_sync : ∀ (Σ : V.t store),
      ⦉SYNC, Σ⦊ ⟶ inl ⦉SKIP, Σ⦊.
  Proof.
    intros Σ.
    apply step_replicate_join_inl.
    intros i H__lt.
    assert (exists σ, π i Σ = Some σ) as [σ HA] by eauto with vector.
    eauto 7 with red replicate.
  Qed. *)

  (* Lemma reachable_replicate_sync :
    forall (Σ : t store), ⦉SYNC, Σ⦊ ⟹ inr Σ.
  Proof.
 *)
    (* intros vsigma.
    apply rt_trans with (y := inl (replicate Skip vsigma)).
    - apply rt_step.
      apply step_interrupt.
      intros i H_lt.
      assert (exists σ__i, π i vsigma = Some σ__i)
        as [σ__i HA] by eauto with vector.
      exists (Sync, σ__i), (Skip, σ__i), (0,nil).
      auto using replicate_prop3, red_sync.
    - apply reachable_replicate_skip.
  Qed. *)

  
  (* Lemma aligned_sync : ∀ Σ, aligned_for SYNC Σ.
  Proof.
    intros Σ.
  to be removed *)


  (* Lemma step_replicate_seq1 :
    ∀ (Σ : V.t store) s1 s2 Σ' s1',
      (⦉s1, Σ⦊ ⟶ inl ⦉s1', Σ'⦊) ->
      (⦉s1;;s2, Σ⦊ ⟶ inl ⦉s1';;s2, Σ'⦊).
  Proof.
    intros Σ s1 s2 Σ' s0 H.
    assert (∀ i, i < p -> ∃ σi σi' p0, π i Σ = Some σi /\ π i Σ' = Some σi' /\
                                      red i (s1, σi) p0 (inl (s0, σi'))).
    {
      inversion H; subst.
      intros i H0.
      destruct (H2 i H0) as [(si, σi) [(si', σi')[p0 [HA [HB HC]]]]].
      replace si with s1 in * by eauto with replicate.
      replace si' with s0 in * by eauto with replicate.
      exists σi, σi', p0.
      eauto with replicate.
    }
    assert (∀ i, i < p -> ∃ σi σi' p0, π i Σ = Some σi /\ π i Σ' = Some σi' /\
                                      red i (Seq s1 s2, σi) p0 (inl (Seq s0 s2, σi'))).
    {
      intros i H1.
      destruct (H0 i H1) as [σi [σi'[(n,l) [HA [HB HC]]]]].
      exists σi, σi',(n,l).
      eauto with red.
    }
    apply step_interrupt.
    intros i H2.
    destruct (H1 i H2) as [σi [σi' [p0 [ HA [HB HC]]]]].
    exists (Seq s1 s2, σi), (Seq s0 s2, σi'), p0.
    eauto with replicate.
  Qed. *)

  (* Lemma reachable_replicate_seq1 :
    ∀ (Σ : V.t store) s1 s2 Σ' s1',
      (⦉s1, Σ⦊ ⟹ inl ⦉s1', Σ'⦊) ->
      (⦉s1;;s2, Σ⦊ ⟹ inl ⦉s1';;s2, Σ'⦊).
  Proof.
easy *)

  (* Lemma step_replicate_seq2 :
    ∀ (Σ : V.t store) s1 s2 Σ' X,
      (⦉s1, Σ⦊ ⟶ inr Σ') ->
      (⦉s2, Σ'⦊ ⟶ X) ->
      (⦉s1;;s2, Σ⦊ ⟶ X).
  Proof.
    intros Σ s1 s2 Σ' Γ H H0.
    destruct Γ as [Σ0 | Σ0].
    - assert (∀ i, i < p -> ∃ n1 l1 n2 l2 σi σi' σ0,
                   π i Σ = Some σi /\ π i Σ' = Some σi' /\
                   π i Σ0 = Some σ0 /\
                   red i (s1, σi) (n1,l1) (inr σi') /\
                   red i (s2, σi') (n2,l2) (inl σ0)).
      {
        intros i H1.
        inversion H; subst.
        destruct (H4 i H1) as [(si,σi) [σi' [(n1, l1) [ HA [HB HC]]]]]. 
        inversion H0; subst.
        destruct (H5 i H1) as [(sj,σj) [σj' [(n2, l2) [ HD [HE HF]]]]].
        replace si with s1 in * by eauto with replicate.
        replace sj with s2 in * by eauto with replicate.
        assert (π i Σ' = Some σj) by eauto with replicate.
        replace σj with σi' in * by congruence.
        exists n1, l1, n2, l2, σi, σi', σj'.
        assert (π i Σ = Some σi) by eauto with replicate. 
        eauto with red.
      }
      assert (∀ i, i < p -> ∃ n1 n2 l σi σ0,
                   π i Σ = Some σi /\ π i Σ0 = Some σ0 /\
                   red i (Seq s1 s2, σi) ((n1 + n2)%nat, l) (inl σ0)).
      {
        intros i H2.
        destruct (H1 i H2) as [n1 [l1 [n2 [l2 [σi [σi' [σ0 [HA [HB [HC [HD HE]]]]]]]]]]].
        exists n1, n2, l2, σi, σ0.
        eauto with red.
      }
      apply step_interrupt.
      intros i H3.
      destruct (H2 i H3) as [n1 [n2 [l [σi [σ0 [HA [HB HC]]]]]]].
      exists (Seq s1 s2, σi), σ0, ((n1 + n2)%nat, l).
      eauto with replicate.
    - assert (∀ i, i < p -> ∃ n1 l1 n2 l2 σi σi' σ0,
                   π i Σ = Some σi /\ π i Σ' = Some σi' /\
                   π i Σ0 = Some σ0 /\
                   red i (s1, σi) (n1,l1) (inr σi') /\
                   red i (s2, σi') (n2,l2) (inr σ0)).
      {
        intros i H1.
        inversion H; subst.
        destruct (H4 i H1) as [(si,σi) [σi' [(n1, l1) [ HA [HB HC]]]]]. 
        inversion H0; subst.
        destruct (H5 i H1) as [(sj,σj) [σj' [(n2, l2) [ HD [HE HF]]]]].
        replace si with s1 in * by eauto with replicate.
        replace sj with s2 in * by eauto with replicate.
        assert (π i Σ' = Some σj) by eauto with replicate.
        replace σj with σi' in * by congruence.
        exists n1, l1, n2, l2, σi, σi', σj'.
        assert (π i Σ = Some σi) by eauto with replicate. 
        eauto with red.
      }
      assert (∀ i, i < p -> ∃ n1 n2 l σi σ0 ,
                   π i Σ = Some σi /\ π i Σ0 = Some σ0 /\
                   red i (Seq s1 s2, σi) ((n1 + n2)%nat, l) (inr σ0)).
      {
        intros i H2.
        destruct (H1 i H2) as [n1 [l1 [n2 [l2 [σi [σi' [σ0 [HA [HB [HC [HD HE]]]]]]]]]]].
        exists n1, n2, l2, σi, σ0.
        eauto with red.
      }
      apply step_continue.
      intros i H3.
      destruct (H2 i H3) as [n1 [n2 [l [σi [σ0 [HA [HB HC]]]]]]].
      exists (Seq s1 s2, σi), σ0, ((n1 + n2)%nat, l).
      eauto with replicate.
  Qed. *)

  (* Lemma reachable_replicate_seq2 : ∀ s1 s2 (Σ Σ' : V.t store) X,
      (⦉s1, Σ⦊ ⟹ inr Σ') -> (⦉s2, Σ'⦊ ⟹ X) ->
      (⦉s1;;s2, Σ⦊ ⟹ X).
  Proof.
    intros s1 s2 Σ Σ' X H H0.
    (* constructor 3 with (C' := inr Σ'). *)
  (* easy *)


  Lemma aligned_seq1 : forall s1 s2 Σ,
      aligned_for (s1;;s2) Σ -> aligned_for s1 Σ.
  Proof.
 *)
(*    intros s1 s2 sigma H.
    unfold aligned_for in *.
    intros vst H0 i j st_i st_j p_i p_j st_i' st_j' H1 H2 H3 H4.
    eapply reachable_seq in H0.
    rewrite <- parseq_prop1 in H0.
    destruct st_i as [s_i sigma_i], st_j as [s_j sigma_j].
    destruct st_i' as [s_i' sigma_i'], st_j' as [s_j' sigma_j'].
    apply (H _ H0 i j (Seq s_i s2, sigma_i) (Seq s_j s2, sigma_j) p_i p_j
             (Seq s_i' s2, sigma_i') (Seq s_j' s2, sigma_j')).
    unfold parcomp.
    rewrite vectmap_eq; rewrite H1; reflexivity.
    unfold parcomp.
    rewrite vectmap_eq; rewrite H2; reflexivity.
    destruct p_i.
    apply red_seq2.
    assumption.
    destruct p_j.
    apply red_seq2.
    assumption.
  Qed.
  *)
  
  (* Lemma aligned_seq2 : forall s1 s2 (Σ Σ' : V.t store),
      aligned_for (s1;;s2) Σ -> ⦉s1, Σ⦊ ⟹ inr Σ' ->
      aligned_for s2 Σ'.
  Proof.
  *)
  (*
    intros s1 s2 vsigma vsigma' H_aligned H_reachable_s1.
    unfold aligned_for.
    intros vst H_reachable_s2 i j [s_i' sigma_i'] [s_j' sigma_j'] [n_i w_i] [n_j w_j]
           [s_i'' sigma_i''] [s_j'' sigma_j''] H_vst_i H_vst_j H_reduce_i H_reduce_j.
    destruct (reachable_clos_trans _ _ H_reachable_s2) as [H_trans| HEq]; clear H_reachable_s2.
    - assert (reachable (inl (replicate (Seq s1 s2) vsigma)) (inl vst)).
      {
        apply clos_trans_reachable.
        rewrite parseq_prop1.
        now apply reachable_seq_seq with (vsigma:=vsigma').
      }
      eauto.
    - replace vst with (replicate s2 vsigma') in * by congruence; clear HEq.
      assert (exists vst0, reachable (inl (replicate s1 vsigma)) (inl vst0) /\
                           step (inl vst0) (inr vsigma')) as [vst0 [HA HB]].
      {
        now apply reachable_inr.
      }
      assert (reachable
                (inl (replicate (Seq s1 s2) vsigma))
                (inl (parcomp (fun s =>  Seq s s2) vst0))) as HC.
      {
        rewrite parseq_prop1.
        now apply reachable_seq.
      }
      assert (exists st_i0 st_j0 p_i0 p_j0,
                 π i vst0 = Some st_i0 /\
                 π j vst0 = Some st_j0 /\
                 red i st_i0 p_i0 (inr sigma_i') /\
                 red j st_j0 p_j0 (inr sigma_j')).
      {
        assert (i < p) as HU by eauto with vector.
        assert (j < p) as HV by eauto with vector.
        inversion HB; subst.
        destruct (H1 i HU) as [st_i0 [sigma_i0 [p_i0 [HA0 [HB0 HC0]]]]].
        destruct (H1 j HV) as [st_j0 [sigma_j0 [p_j0 [HD0 [HE0 HF0]]]]].
        exists st_i0, st_j0, p_i0, p_j0.
        split;[assumption | split; [assumption|]].
        specialize (replicate_prop1 _ _ _ _ _ H_vst_i); intro.
        specialize (replicate_prop2 _ _ _ _ _ H_vst_i);intro.
        specialize (replicate_prop1 _ _ _ _ _ H_vst_j);intro.
        specialize (replicate_prop2 _ _ _ _ _ H_vst_j);intro.
        subst.
        rewrite H0 in HB0.
        rewrite H3 in HE0.
        injection HB0; injection HE0; intros; subst; clear HB0 HE0.
        split; assumption.
      }
      destruct H as [[s_i0 sigma_i0] [[s_j0  sigma_j0] [ [n_i0 w_i0] [[n_j0 w_j0][HD [HE [HF HG]]]]]]].
      assert (red i (Seq s_i0 s2, sigma_i0) ((n_i0 + n_i)%nat, w_i)
                      (inl ((s_i'', sigma_i'')))).
      {
        destruct (replicate_prop1 _ _ _ _ _ H_vst_i); subst.
        eauto using red_seq1.
      }
      assert (red j (Seq s_j0 s2, sigma_j0) ((n_j0 + n_j)%nat, w_j)
                      (inl ((s_j'', sigma_j'')))).
      {
        destruct (replicate_prop1 _ _ _ _ _ H_vst_j); subst.
        eauto using red_seq1.
      }
      assert (aligned_for s1 vsigma) as HH by now apply aligned_seq1 with s2.
      assert ((n_i0 + n_i, w_i)%nat = (n_j0 + n_j, w_j)%nat).
      {
        unfold aligned_for in H_aligned.
        eapply H_aligned.
        apply HC.
        unfold parcomp.
        rewrite vectmap_eq; rewrite HD; reflexivity.
        unfold parcomp.
        rewrite vectmap_eq; rewrite HE; reflexivity.
        apply H.
        apply H0.
      }
      injection H1; intros; subst.
      f_equal.
      assert (n_i0 = n_j0).
      {
        assert (s_i0 = s_j0).
        {
          assert (aligned_for s1 vsigma).
          apply aligned_seq1 with s2.
          assumption.
          destruct (reachable_replicate_aligned _ _ H2 _ HA) as [s0 [v0 HU]].
          subst.
          destruct (replicate_prop1 _ _ _ _ _ HE).
          destruct (replicate_prop1 _ _ _ _ _ HD).
          subst.
          reflexivity.
        }
        subst.
        eapply topConditions.
        apply HF.
        apply HG.
      }
      lia.
      
  Qed.
*)
    (* Lemma step_replicate_if1 :
    ∀ (Σ : V.t store) b s1 s2 X,
      alltrue Σ b ->
      (⦉s1, Σ⦊ ⟶ X) ->
      (⦉IFB b THEN s1 ELSE s2 FI, Σ⦊ ⟶ X).
  Proof.
    intros Σ b s1 s2 X H_alltrue H_step.
    inversion H_step; subst.
    - constructor.
      intros i Hi.
      destruct (H i Hi) as [[s_i σ_i] [σ_i' [[n0 w0] [HB [HC HD]]]]].
      exists (If b s1 s2, σ_i), σ_i', (1, (n0,L)::w0).
      split.
      + eauto with replicate.
      + split.
        * assumption.
        * apply red_if1.
          -- apply H_alltrue.
             apply replicate_prop2 in HB.
             assumption.
          --  eauto with replicate.
              assert (s1 = s_i) by eauto with replicate.
              subst.
              assumption.
    - constructor.
      intros i H1.
      destruct (H i H1) as [[s_i σ_i] [σ_i' [[n0 w0] [HB [HC HD]]]]].
      exists (If b s1 s2, σ_i), σ_i', (1, (n0,L)::w0).
      split.
      +  eauto with replicate.
      + split.
        * assumption.
        * apply red_if1.
          --  apply H_alltrue.
              apply replicate_prop2 in HB.
              assumption.
          --  eauto with replicate.
              assert (s1 = s_i) by eauto with replicate.
              subst.
              assumption.
Qed. *)

(* Lemma reachable_replicate_if1 :
    ∀ (Σ : t store) b s1 s2 Γ,
      alltrue Σ b ->
      (⦉s1,Σ⦊ ⟹ Γ) ->
      (⦉IFB b THEN s1 ELSE s2 FI, Σ⦊ ⟹ Γ) \/ Γ = inl ⦉s1, Σ⦊.
  Proof.
 *)
  (*
  intros Σ b s1 s2 Γ H H0.
  dependent induction H0.
  - right.
    reflexivity.
  - left.
    constructor 2.
    apply step_replicate_if1.
    assumption.
    assumption.
  - apply IHreachable.
    assumption.
    destruct (IHreachable _ _ H (refl_equal _)) as [HA | HA].
  + left.
    now constructor 3 with (y:=y).
  + destruct (IHclos_refl_trans2 _ _ H HA) as [HB | HB].
    * left; assumption.
    * right; assumption.
    intros Σ b s1 s2 Γ H H0.
    dependent induction H0.
    - right.
      reflexivity.
    - left.
      constructor 2.
      apply step_replicate_if1.
      assumption.
      assumption.
    - destruct (IHclos_refl_trans1 _ _ H (refl_equal _)) as [HA | HA].
      + left.
        now constructor 3 with (y:=y).
      + destruct (IHclos_refl_trans2 _ _ H HA) as [HB | HB].
        * left; assumption.
        * right; assumption.
  Qed.
*)
  (* reduceA_if2 *)
  (* Lemma step_replicate_if2 :
    ∀ (Σ : V.t store) b s1 s2 X,
      allfalse Σ b ->
      (⦉s2, Σ⦊ ⟶ X)  ->
      (⦉IFB b THEN s1 ELSE s2 FI, Σ⦊ ⟶ X).
  Proof.
 *)
  (*
    intros Σ b s1 s2 Γ H H0.
    inversion H0; subst.
    constructor.
    intros i H1.
    destruct (H2 i H1) as [[s_i σ_i] [σ_i' [p0 [HB [HC HD]]]]].
    destruct p0 as [n0 w0].
    exists (If b s1 s2, σ_i), σ_i', (1, (n0,R)::w0).
    split.
    eauto with replicate.
    split.
    assumption.
    apply red_if2.
    apply H.
    apply replicate_prop2 in HB.
    assumption.
    eauto with replicate.
    assert (s2 = s_i) by eauto with replicate.
    subst.
    assumption.
     constructor.
    intros i H1.
    destruct (H2 i H1) as [[s_i σ_i] [σ_i' [p0 [HB [HC HD]]]]].
    destruct p0 as [n0 w0].
    exists (If b s1 s2, σ_i), σ_i', (1, (n0,R)::w0).
    split.
    eauto with replicate.
    split.
    assumption.
    apply red_if2.
     apply H.
    apply replicate_prop2 in HB.
    assumption.
    eauto with replicate.
    assert (s2 = s_i) by eauto with replicate.
    subst.
    assumption .
  Qed.
*)


            
 (* Lemma reachable_replicate_if2 :
   ∀ (Σ : t store) b s1 s2 Γ,
     allfalse Σ b ->
     (⦉s2, Σ⦊ ⟹ Γ) ->
     (⦉IFB b THEN s1 ELSE s2 FI, Σ⦊ ⟹ Γ) \/ Γ = inl ⦉s2, Σ⦊.
 Proof.
 *)
 (*
   intros Σ b s1 s2 Γ H H0.
   dependent induction H0.
   - left.
     constructor 1.
     now apply step_replicate_if2.
   - right.
     reflexivity.
   - destruct (IHclos_refl_trans1 _ _ H (refl_equal _)) as [HA | HA].
     + left.
       now constructor 3 with (y:=y).
     + destruct (IHclos_refl_trans2 _ _ H HA) as [HB | HB].
       * left; assumption.
       * right; assumption.
 Qed.
*)
  
  (* Lemma aligned_if1 :
    ∀ (Σ : V.t store) b s1 s2,
      alltrue Σ b ->
      aligned_for (If b s1 s2) Σ ->
      aligned_for s1 Σ.
  Proof.
 *)
  (*
    intros Σ b s1 s2 H H0.
    unfold aligned_for in *.
    intros vst H1 i j st_i st_j p_i p_j st_i' st_j' H2 H3 H4 H5.
    destruct (reachable_replicate_if1 Σ b s1 s2 (inl vst) H H1).
    - exact (H0 _ H6 _ _ _ _ _ _ _ _ H2 H3 H4 H5).
    - assert (reachable (inl (replicate (If b s1 s2) Σ)) (inl (replicate (If b s1 s2) Σ))) by constructor 2.
      replace vst with (replicate s1 Σ) in * by now injection H6.
      destruct st_i as [si σi], st_j as [sj σj].
      replace si with s1 in * by eauto with replicate.
      replace sj with s1 in * by eauto with replicate.
      destruct p_i as [ni li], p_j as [nj lj].
      assert ((1, (ni,L)::li) = (1, (nj,L)::lj)) as HA.
      {
        apply H0 with (vst := replicate (If b s1 s2) Σ) (i:=i) (j:=j) (st_i := (If b s1 s2,σi))
                      (st_j := (If b s1 s2, σj)) (st_i' := st_i') (st_j' := st_j');
          eauto using red_if1 with replicate.
      }
      f_equal; now injection HA.
  Qed.
*)

  (* Lemma aligned_if2 : 
    ∀ (Σ : V.t store) b s1 s2,
      (∀ i σ_i, π i Σ = Some σ_i -> beval b i σ_i = false) ->
      aligned_for (If b s1 s2) Σ ->
      aligned_for s2 Σ.
  Proof.
 *)
  (*
    intros Σ b s1 s2 H H0.
    unfold aligned_for in *.
    intros vst H1 i j st_i st_j p_i p_j st_i' st_j' H2 H3 H4 H5.
    destruct (reachable_replicate_if2 Σ b s1 s2 (inl vst) H H1).
    - exact (H0 _ H6 _ _ _ _ _ _ _ _ H2 H3 H4 H5).
    - assert (reachable (inl (replicate (If b s1 s2) Σ)) (inl (replicate (If b s1 s2) Σ))) by constructor 2.
      replace vst with (replicate s2 Σ) in * by now injection H6.
      destruct st_i as [si σi], st_j as [sj σj].
      replace si with s2 in * by eauto with replicate.
      replace sj with s2 in * by eauto with replicate.
      destruct p_i as [ni li], p_j as [nj lj].
      assert ((1, (ni,R)::li) = (1, (nj,R)::lj)) as HA.
      {
        apply H0 with (vst := replicate (If b s1 s2) Σ) (i:=i) (j:=j) (st_i := (If b s1 s2,σi))
                      (st_j := (If b s1 s2, σj)) (st_i' := st_i') (st_j' := st_j');
          eauto using red_if2 with replicate.
      }
      f_equal; now injection HA.
  Qed.
*)  
  (* Lemma step_replicate_while1 :
    ∀ (Σ : V.t store) b s (Σ' : vstore),
      alltrue Σ b ->
      (⦉s, Σ⦊ ⟶ inr Σ') → 
      ∀ Σ'',(⦉WHILE b DO s END, Σ'⦊ ⟶ inr Σ'') → 
            (⦉WHILE b DO s END, Σ⦊ ⟶ inr Σ'').
  Proof.
   *)
  (*
    intros Σ b s Σ' H H0 Σ'' H1.
    apply step_continue.
    intros i H2.
    inversion H0; inversion H1; subst.
    destruct (H5 i H2) as [[s_i σ_i] [σ_i0 [p_i [HA [HB HC]]]]].
    destruct (H8 i H2) as [[s_i' σ_i'] [σ_i'' [p_i' [HU [HV HW]]]]].
    destruct p_i.
    destruct p_i'.
    exists (While b s, σ_i), σ_i'', (1, ((n + n0)%nat,L)::l0).
    split.
    eauto with replicate.
    split.
    assumption.
    assert (While b s = s_i') by eauto with replicate.
    assert (s = s_i) by eauto with replicate.
    subst.
    apply red_while1.
    apply H.
    eauto with replicate.
    eapply red_seq1.
    apply HC.
    apply replicate_prop2 in HU.
    assert (σ_i0 = σ_i') by congruence.
    subst.
    assumption.
  Qed.*)

  (* reduceA_while2 *)
  (* Lemma step_replicate_while2 :
    ∀ (Σ : V.t store) b s,
      allfalse Σ b ->
      (⦉WHILE b DO s END, Σ⦊ ⟶ inr Σ).
  Proof.
    intros Σ b s H.
    apply step_continue.
    intros i H0.
    assert (exists σ_i, π i Σ = Some σ_i) as [σ_i HA] by eauto with vector.
    specialize (H i σ_i HA).
    exists (While b s, σ_i), σ_i, (1,nil).
    auto using replicate_prop3, red_while2.
  Qed.

  Lemma step_replicate_while :
    ∀ b s s' (Σ Σ' : V.t store),
      step ((replicate (While b s) Σ)) (inl (replicate s' Σ')) ->
      (∀ i : nat, i < p → ∃ σ_i : store, π i Σ = Some σ_i ∧ beval b i σ_i = true) /\
      step ((replicate (Seq s (While b s)) Σ)) (inl (replicate s' Σ')).
  Proof.
   easy *)


  (* Lemma aligned_while :
    ∀ (Σ : V.t store) b s,
      aligned_for (While b s) Σ ->
      alltrue Σ b->
      (∀ (i : nat) (σ_i : store), π i Σ = Some σ_i → beval b i σ_i = true) ->
      aligned_for (Seq s (While b s)) Σ.
  Proof.
easy *)


  
  (* Lemma step_replicate_inr :
    ∀ s Σ Σ', inl ⦉ s, Σ ⦊ ⟶ inr Σ' -> aligned_for s Σ.
  Proof.
 easy *)
 

(*    intros Σ s1 s2 Γ H__aligned H__step.
    case_eq p; [intros H__EQ0 | intros n H__Eq1].
    - right.
      exists (vempty store H__EQ0); auto using step_empty.
    - assert (∀ i, i < p -> ∃ σi sti pi,
                   π i Σ = Some σi /\
                   π i Γ = Some sti /\
                   red i (Seq s1 s2, σi) pi (inl sti))
        as H__allreduce by now apply step_replicate_split_inl.
      assert (∃ σ0 st0 p0,
                 π 0 Σ = Some σ0 /\
                 π 0 Γ = Some st0 /\
                 red 0 (s1;;s2, σ0) p0 (inl st0))
        as [σ [(s,σ') [p0 [H__EQ1 [H__EQ2 H__reduce]]]]].
        {
          apply (H__allreduce 0).
          lia.
        }
      inversion H__reduce as [ | | | ? ? ? sigma0 ? n1 w1 n2 w2 H__reduce1 H__reduce2
                             | ? ? ? n0 w s1' ? H__reduce0| | | | ]; subst.
      + right.
        assert (∀ i, i < p -> ∃ σ__i'' n__i w__i σ__i σi' ni' wi',
                     π i Σ = Some σ__i /\
                     π i Γ = Some (s, σi') /\
                     red i (s1, σ__i) (n__i, w__i) (inr σ__i'') /\
                     red i (s2, σ__i'') (ni', wi') (inl (s, σi')) 
               ) as H__reduceall.
        {
          intros i H__lt.
          destruct (H__allreduce i H__lt) as [σ__i [(s0, σi') [hi [H__EQ3 [H__EQ4 H__reducei]]]]].
          assert (s0 = s).
          {
            destruct (step_replicate_aligned _ _ H__aligned _ H__step) as [s' [Σ' HEQ5]]; rewrite HEQ5 in *.
            assert (s' = s) by eauto with replicate.
            assert (s' = s0) by eauto with replicate.
            subst; reflexivity.            
          }
          inversion H__reducei as [ | | | ? ? ? ? ? ? ? ? ? H__reducei1 H__reducei2
                                  | ? ? ? ? ? ? ? H__reducei1 | | | |]; subst.
            + exists σ'0, n0, w0, σ__i, σi', n3, w3. tauto.
            + exfalso.
            assert ((n0,w) = ((n1 + n2)%nat, w2)).
            {
              
              assert (reachable (inl (replicate (Seq s1 s2) Σ)) (inl (replicate (Seq s1 s2) Σ))) by
                  constructor 2.
              assert (π 0 (replicate (Seq s1 s2) Σ) = Some (Seq s1 s2, σ)) by eauto with replicate.
              assert (π i (replicate (Seq s1 s2) Σ) = Some (Seq s1 s2, σ__i)) by eauto with replicate.
              unfold aligned_for in H__aligned.
              apply (H__aligned _ H _ _ _ _ _ _ _ _ H1 H0 H__reducei H__reduce).
            }
            injection H; intros; subst; clear H.
            eauto using seq1_sameAction.
        }
        apply vect_forall in H__reduceall.
        destruct H__reduceall as [Σ' H__reducevect].
        exists Σ'.
        split.
        * constructor.
          intros i H__lt.
          destruct (H__reducevect i H__lt)
            as [σ'' [H__EQ5 [ni [wi [ σi'' [ni' [wi' [H__EQ6 [H__EQ7 [H__EQ8 [H__reducei1 H__reducei2]]]]]]]]]]].
          exists (s1, σi''), σ'', (ni,wi).
          eauto with replicate.
        * constructor.
          intros i H__lt.
          destruct (H__reducevect i H__lt)
            as [σ'' [H__EQ6 [ni [wi [ σi'' [σi' [ni' [wi' [H__EQ7 [H__EQ8 [H__reducei1 H__reducei2]]]]]]]]]]].
          exists (s2, σ''), (s, σi'), (ni',wi'); eauto with replicate.
      + left.
        assert (∀ i, i < p -> ∃ σ__i' σ__i n__i w__i,
                     π i Σ = Some σ__i /\
                     π i Γ = Some (Seq s1' s2, σ__i') /\
                     red i (s1, σ__i) (n__i, w__i) (inl (s1', σ__i'))) as H__reduceall.
        {
          intros i H__lt.
          (* assert (i < p) as H__lt2 by omega.*)
          destruct (H__allreduce i H__lt) as  [σ__i [(s0, σi') [hi [H__EQ3 [H__EQ4 H__reducei]]]]].
          assert (s0 = Seq s1' s2).
          {
            destruct (step_replicate_aligned _ _ H__aligned _ H__step) as [s' [Σ' HEQ5]]; rewrite HEQ5 in *.
            assert (s' = Seq s1' s2) by eauto with replicate.
            assert (s' = s0) by eauto with replicate.
            subst; reflexivity.            
          }
          inversion H__reducei as [ | | | ? ? ? ? ? ? ? ? ? H__reducei1 H__reducei2
                                  | ? ? ? ? ? ? ? H__reducei1 | | | |]; subst.
          -  exfalso.
             assert ((n0,w) = ((n1 + n2)%nat, w2)).
             {
               
               assert (reachable (inl (replicate (Seq s1 s2) Σ)) (inl (replicate (Seq s1 s2) Σ))) by
                   constructor 2.
               assert (π 0 (replicate (Seq s1 s2) Σ) = Some (Seq s1 s2, σ)) by eauto with replicate.
               assert (π i (replicate (Seq s1 s2) Σ) = Some (Seq s1 s2, σ__i)) by eauto with replicate. 
               symmetry.
               apply (H__aligned _ H _ _ _ _ _ _ _  _ H1 H0 H__reducei H__reduce).
             }
             injection H; intros; subst; clear H.
             eauto using seq1_sameAction.
          - exists σi', σ__i, n1,w0.
            split.
            assumption.
            split.
            assumption.
            injection H4; intros; subst.
            assumption.
        }
        apply vect_forall in H__reduceall.
        destruct H__reduceall as [Σ' H__reducevect].
        exists s1', Σ'.
        split.
        * constructor.
          intros i H__lt.
          destruct (H__reducevect i H__lt)
            as [σi'' [H__EQ5 [σi [ni [wi [ H__EQ6 [H__EQ7 H__reducei1]]]]]]].
          exists (s1, σi), (s1', σi''), (ni,wi).
          split.
          eauto with replicate.
          split.
          eauto with replicate.
          assumption.
        * apply vect_extensionality.
          intros i H__lt.
          destruct (H__reducevect i H__lt)
            as [σi'' [H__EQ5 [σi [ni [wi [ H__EQ6 [H__EQ7 H__reducei1]]]]]]].
          assert (π i (replicate (Seq s1' s2) Σ') = Some (Seq s1' s2, σi''))
            by eauto with replicate.
          rewrite H__EQ7.
          rewrite H.
          reflexivity.
  Qed.
*)

  


   
 (* Subterms alignment *)
  



(*  Lemma  aligned_if1_inv:
    ∀(b : bexpr) (s1 s2 : stmt)(Σ : t store),
      alltrue Σ b ->
      aligned_for (IFB b THEN s1 ELSE s2 FI) Σ ->
      aligned_for s1 Σ.
  Proof.
    intros b s1 s2 Σ H.
 

  
  Lemma  aligned_if2_inv:
    ∀(b : bexpr) (s1 s2 : stmt)(Σ : t store),
      allfalse Σ b ->
      aligned_for (IFB b THEN s1 ELSE s2 FI) Σ ->
      aligned_for s2 Σ.
  Proof.
    intros b s1 s2 Σ H.*)
  




(*  Lemma reachable_replicated_aligned : 
    forall s Σ,
      aligned_for s Σ ->
        forall (C : vconfiguration),
          reachable (replicate s Σ) C ->
          exists s', C = replicate s' (fmap snd C).
  Proof.
    intros s Σ H_aligned C Hreachable.
    dependent induction Hreachable.
    - exists s.
      now rewrite fmap_snd.
    - apply step_preserves_replication with s Σ.
      assumption.
      assumption.
    - destruct (step_preserves_replication s Σ H_aligned C' H) as [s' Ha].
      assert (aligned_for s' (fmap snd C')).
      apply reachability_preserves_alignement with s Σ.
      apply H_aligned.
      rewrite Ha in H.
      constructor 2.
      apply H.
      eapply IHHreachable.
      apply H0.
      apply Ha.
      reflexivity.
Qed.*)

(*  Lemma reachable_replicate_aligned :
    forall s (Σ : V.t store),
      aligned_for s Σ ->
      forall vstate,
        reachable (replicate s Σ) (inl vstate) ->
        exists s' Σ', vstate = replicate s' Σ'.
  Proof.
    intros s vsigma H_aligned T H_reachable.
    dependent induction H_reachable.
    - eauto using step_replicate_aligned.
    - eauto.
    - assert (exists vstate, y = inl vstate) as [vstate HEq]
          by (destruct (reachable_inl _ _ H_reachable2); eauto).
      destruct (IHH_reachable1 vstate _ _ H_aligned (refl_equal _) HEq)
        as [s0 [vsigma0 HEq0]].
      subst.
      assert (aligned_for s0 vsigma0) as H_aligned_0 by
            eauto using reachability_preserves_alignement.
      destruct (IHH_reachable2 _ _ _ H_aligned_0 (refl_equal _) (refl_equal _))
        as [s' [vsigma' HB]].
      eauto.
  Qed.
*)
