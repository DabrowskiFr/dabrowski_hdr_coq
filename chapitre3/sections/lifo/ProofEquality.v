Require Import Arith.
Require Import Nat.
Require Import Eqdep_dec.
Require Import Peano_dec.
(** * Axiom K is provable for [nat] *)

Theorem K_nat :
  forall (x:nat) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.
Proof.
  intros; apply K_dec_set with (p := p).
  apply eq_nat_dec.
  assumption.
Qed.

Theorem eq_rect_eq_nat :
  forall (p:nat) (Q:nat->Type) (x:Q p) (h:p=p), x = eq_rect p Q x p h.
Proof.
  intros; apply K_nat with (p := h); reflexivity.
Qed. 

Scheme leInductionPrinciple := Induction for le Sort Prop.
(** * Two proofs of [n<m] are equals *)

Theorem ltUniquenessProof: 
  forall (n m : nat) (H1 H2 : n < m),
    H1 = H2.
Proof. 
  unfold lt; induction H1 using leInductionPrinciple; intro H2.
    replace (le_n (S n)) with
      (eq_rect _ (fun n0 => S n <= n0) (le_n (S n)) _ (refl_equal (S n))).
      generalize (refl_equal(S n)).
      pattern (S n) at 2 4 6 10, H2; case H2; [intro | intros m l e].
      rewrite <- eq_rect_eq_nat; trivial.
      contradiction (Nat.nle_succ_diag_l m); rewrite <- e; assumption.
      reflexivity.
    replace (le_S (S n) m H1) with
      (eq_rect _ (fun n0 => S n <= n0) (le_S (S n) m H1) _ (refl_equal (S m))).
      generalize (refl_equal (S m)).
      pattern (S m) at 1 3 4 6, H2; case H2; [intro Heq | intros m0 l HeqS].
      contradiction (Nat.nle_succ_diag_l m); rewrite Heq; assumption.
      injection HeqS; intro Heq; generalize l HeqS.
      rewrite <- Heq; intros; rewrite <- eq_rect_eq_nat.
      rewrite (IHle l0); reflexivity.
      reflexivity.
Qed.

Theorem leUniquenessProof:
  forall (n m : nat) (H1 H2 : n <= m),
  H1 = H2.
Proof.
  unfold lt; induction H1 using leInductionPrinciple; intro H2.
    replace (le_n (n)) with
      (eq_rect _ (fun n0 => n <= n0) (le_n (n)) _ (refl_equal (n))).
      generalize (refl_equal(n)).
      pattern (n) at 2 4 6 10, H2; case H2; [intro | intros m l e].
      rewrite <- eq_rect_eq_nat; trivial.
      contradiction (Nat.nle_succ_diag_l m); rewrite <- e; assumption.
      reflexivity.
    replace (le_S (n) m H1) with
      (eq_rect _ (fun n0 => n <= n0) (le_S (n) m H1) _ (refl_equal (S m))).
      generalize (refl_equal (S m)).
      pattern (S m) at 1 3 4 6, H2; case H2; [intro Heq | intros m0 l HeqS].
      contradiction (Nat.nle_succ_diag_l m); rewrite Heq; assumption.
      injection HeqS; intro Heq; generalize l HeqS.
      rewrite <- Heq; intros; rewrite <- eq_rect_eq_nat.
      rewrite (IHle l0); reflexivity.
      reflexivity.
Qed.
