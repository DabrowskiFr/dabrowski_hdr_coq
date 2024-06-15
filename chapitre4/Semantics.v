Require Import Bool Nat List.
Require Import Monad.
Require Import Peano_dec.
Require Import Relations.Relation_Operators.
Require Import Vector VectorTheory PVector PVectorTheory Syntax.
Require Import Program.
Require Import Utf8.

Open Scope type_scope.

Module Semantics (Import P : Process) (Import V : Vector P).

  Module Export PVT := PVectorTheory P V.

  Open Scope stmt_scope.
  Notation "'ε'" := (nil) (at level 70).

  (** * Definition of operational semantics *)

  (** ** Domain *)

  (* notations *)
  (* σ store *)
  (* Σ vstore *)
  (* c configuration *)
  (* C vconfiguration *)
  (* γ kstate *)
  (* Γ vkstate *)

  (** *** Store *)

  Definition store : Set := nat -> nat.

  Definition update : nat -> nat -> store -> store :=
    fun x n σ => fun y => if x =? y then n else σ y.

  Definition configuration : Set := stmt * store.
  Definition kstate : Set := configuration + store.
  Definition vstore : Type := V.t store.
  Definition vconfiguration : Type := V.t configuration.
  Definition vkstate : Type := vconfiguration + vstore.

  Notation "⟨ A , B ⟩" := ((A,B):configuration) (at level 9).

  (* Definition g : configuration -> kstate := @inl configuration store. 
  Definition h : store -> kstate := @inr (stmt * store) store.
  Definition i : vconfiguration -> vkstate := @inl vconfiguration vstore.
  Definition j : vstore -> vkstate := @inr vconfiguration vstore.
  Coercion g : configuration >-> kstate. 
  Coercion h : store >-> kstate.
  Coercion i : vconfiguration >-> vkstate.
  Coercion j : vstore >-> vkstate. *)
  
  (** ** Replicated vectors *)

  Definition replicate (s : stmt) : vstore -> vconfiguration :=
    (fmap (fun σ => (s, σ))).

  Notation "⦉ A , B ⦊" := (replicate A B).

  (** *** Paths *)
  
  Inductive choice := L | R.
  
  Definition path : Set := nat * list (nat * choice).

  (** *** Evaluation of expressions *)
  
  Fixpoint eval (e : expr) (i : nat) (σ : store) : nat :=
    match e with
      Var x => σ x
    | Const n => n
    | Pid => i
    | NProcs => p
    | Binop b e1 e2 =>
      match b with
        Add => (eval e1 i σ) + (eval e2 i σ)
      | Sub => (eval e1 i σ) - (eval e2 i σ)
      | Mult => (eval e1 i σ) * (eval e2 i σ)
      end
    end.
  
  Fixpoint beval (b : bexpr) (i : nat) (σ : store) :=
    match b with
      TT => true
    | FF => false
    | Comp c e1 e2 =>
      match c with
        Eq => (eval e1 i σ) =? (eval e2 i σ)
      | Lt => (eval e1 i σ) <=? (eval e2 i σ)
      end
    | And b1 b2 => (beval b1 i σ) && (beval b2 i σ)
    | Or b1 b2 => (beval b1 i σ) || (beval b2 i σ)
    | Not b =>  negb (beval b i σ)
    end.
  
  
  (** ** local step *)

  Inductive red (i : nat) : configuration → path → kstate → Prop :=
    red_skip : forall σ, 
      red i ⟨SKIP, σ⟩ (0, ε) (inr σ)
  | red_assign : forall σ x e n,
      eval e i σ = n →
      red i ⟨x::=e, σ⟩ (0, ε) (inr (update x n σ))
  | red_sync : forall σ, 
    red i ⟨SYNC, σ⟩ (0, ε) (inl ⟨SKIP, σ⟩)
  | red_seq1 : forall s1 s2 σ (σ':store) γ n1 w1 n2 w2,
      red i ⟨s1, σ⟩ (n1, w1) (inr σ') → red i ⟨s2, σ'⟩ (n2, w2) γ →
      red i ⟨s1;; s2, σ⟩ ((n1 + n2)%nat, w2) γ
  | red_seq2 : forall s1 s2 σ n w s1' σ',
      red i ⟨s1, σ⟩ (n, w) (inl ⟨s1', σ'⟩) →
      red i ⟨s1;; s2, σ⟩ (n,w ) (inl ⟨Seq s1' s2, σ'⟩)
  | red_if1 : forall b σ s1 s2 γ n w, 
        beval b i σ = true → red i ⟨s1, σ⟩ (n, w) γ →
        red i ⟨IFB b THEN s1 ELSE s2 FI, σ⟩ (1, (n,L)::w) γ
  | red_if2 : forall b σ s1 s2 γ n w, 
        beval b i σ = false → red i ⟨s2, σ⟩ (n, w) γ →
        red i ⟨IFB b THEN s1 ELSE s2 FI, σ⟩ (1, (n, R)::w) γ
  | red_while1 : forall b σ s γ n w, 
        beval b i σ = true -> red i ⟨s;;WHILE b DO s END, σ⟩ (n, w) γ →
        red i ⟨WHILE b DO s END, σ⟩ (1, (n, L)::w) γ
  | red_while2 : forall b σ s, 
        beval b i σ = false →
        red i ⟨WHILE b DO s END, σ⟩ (1, ε) (inr σ).

  (** ** Supersteps *)
  
  Inductive step : vconfiguration → vkstate -> Prop :=
    step_interrupt : forall (C : vconfiguration) (C' : vconfiguration),
      (forall i,
          i < p ->
          exists ci ci' hi,
            π i C = Some ci /\ π i C' = Some ci' /\
            red i ci hi (inl ci')) ->
      step C (inl C')
  | step_continue : forall (C : vconfiguration) (Σ : vstore),
      (forall i,
          i < p ->
          exists γi σi hi,
            π i C = Some γi /\ π i Σ = Some σi /\
            red i γi hi (inr σi)) ->
      step C (inr Σ).

  Infix "⟶" := step (at level 70, right associativity).

  (** ** Reachable states *)
  
Inductive reachable : vconfiguration -> vkstate -> Prop :=
  | reachable0 : forall C, reachable C (inl C)
  | reachable1 : forall C Γ, 
    step C Γ -> reachable C Γ
  | reachable2 : forall C C' Γ,
    step C (inl C') -> reachable C' Γ -> reachable C Γ.

  Infix "⟹" := reachable (at level 70, right associativity).

  (** ** Deadlock freeness *)
  
  Definition deadlock (C : vconfiguration) :  Prop :=
    exists i j, i <> j /\
           (exists γi hi γ, π i C = Some γi /\ red i γi hi (inl γ)) /\
           (exists γj hj σ, π j C = Some γj /\ red j γj hj (inr σ)).
  
  Definition deadlock_free (s : stmt) :=
    ∀ Σ (C : vconfiguration), (⦉s, Σ⦊ ⟹ inl C) -> ¬ deadlock C.
  
End Semantics.