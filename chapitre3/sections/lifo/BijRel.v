Require Import Lt.
Require Import Peano_dec.
Require Import Lia.
(******************************************************)
(* caracterisation of relations *)

Definition functionnal {A B : Set} (R : A -> B -> Prop) :=
  forall k0 k1 k2, R k0 k1 -> R k0 k2 -> k1 = k2.

Definition applicative {A B : Set} (P : A -> Prop) (R : A -> B -> Prop) :=
  forall k, P k -> exists k', R k k'.

Definition injective {A B : Set} (R : A -> B -> Prop) :=
  forall k0 k1 k2, R k1 k0 -> R k2 k0 -> k1 = k2.

Definition surjective {A B : Set} (Q : B -> Prop)(R : A -> B -> Prop) :=
  forall k', Q k' -> exists k, R k k'.

Definition restricted {A B : Set} (P : A -> Prop) (Q : B -> Prop) (R : A -> B -> Prop) :=
  forall x y, R x y -> P x /\ Q y.

Inductive bijective {A B : Set} (P : A -> Prop) (Q : B -> Prop) (R : A -> B -> Prop) :=
  bijective_cons :
    restricted P Q R ->
    functionnal R -> 
    applicative P R -> 
    injective R -> 
    surjective Q R -> 
    bijective P Q R.

Definition identity_R {A : Set} (P : A -> Prop) :=
  fun x y => x = y /\ P x.

Lemma identity_R_bijective {A : Set} :
  forall (P : A -> Prop), 
    bijective P P (identity_R P).
Proof.
  intros P.
  constructor.
  - intros x y [? ?].
    subst; tauto.
  - intros x y z [? _] [? _].
    congruence.
  - intros x y.
    exists x; split; intuition.
  - intros x y z [? _] [? _].
    congruence.
  - intros x h.
    exists x; split; intuition.
Qed.

Definition inverse {A B : Set} (R : A -> B -> Prop) : B -> A -> Prop :=
  fun x y => R y x.

Lemma inverse_bijective {A B : Set} :
  forall (R : A -> B -> Prop) (P: A -> Prop) (Q : B -> Prop), 
    bijective P Q R -> bijective Q P (inverse R).
Proof.
  intros R P Q h_bijective.
  destruct h_bijective as [h_restricted h_functional h_applicative h_injective h_surjective].
  constructor.
  - intros x y h_inverse.
    assert (P y /\ Q x) by now apply h_restricted.
    tauto.
  - intros x y z h1 h2.
    now apply (h_injective x y z).
  - now apply h_surjective.
  - apply h_functional.
  - apply h_applicative.
Qed.

Definition composition {A B C} (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) : A -> C -> Prop :=
  fun x z => exists y, R1 x y /\ R2 y z.

Lemma composition_bijective {A B C : Set} :
  forall (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) (P : A -> Prop) (Q : B -> Prop) (R : C -> Prop),
    bijective P Q R1 -> bijective Q R R2 -> bijective P R (composition R1 R2).
Proof.
  intros R1 R2 P Q R h_bijective1 h_bijective2.
  destruct h_bijective1 as [h_restricted1 h_functional1 h_applicative1 h_injective1 h_surjective1].
  destruct h_bijective2 as [h_restricted2 h_functional2 h_applicative2 h_injective2 h_surjective2].
  constructor.
  - intros x z [y [h1 h2]].
    split; [ now apply (h_restricted1 x y) | now apply (h_restricted2 y z)].
  - intros x y z [y1 [h1 h2]] [y2 [h3 h4]].
    replace y2 with y1 in * by now apply (h_functional1  x y1 y2).
    now apply (h_functional2 y1 y z).
  - intros x h1.
    assert (exists y, R1 x y) as [y h_y] by now apply h_applicative1.
    assert (Q y) by now apply (h_restricted1 x).
    assert (exists z, R2 y z) as [z h_z] by now apply h_applicative2.
    exists z; split with y; tauto.
  - intros x y z [y1 [h1 h2]] [y2[h3 h4]].
    replace y2 with y1 in * by now apply (h_injective2 x y1 y2).
    now apply (h_injective1 y1 y z).
  - intros x h_x.
    assert (exists y, R2 y x) as [y h_y] by now apply h_surjective2.
    assert (Q y) by now apply (h_restricted2 y x).
    assert (exists z, R1 z y) as [z Hz] by now apply h_surjective1.
    exists z; split with y; tauto.
Qed.


(** bijective_lt *)

Lemma bijective_S : 
  forall R n m, 
    bijective (fun k => k < n) (fun k => k < m) R ->
    bijective (fun k => k < S n) (fun k => k < S m) (fun x y => R x y \/ (x = n /\ y = m)).
Proof.
  intros R n m h_bijective.
  inversion h_bijective as [h_restricted h_functional h_applicative h_injective h_surjective].
  constructor.
  - intros x y h_R.
    destruct h_R.
    + assert (x < n /\ y < m) by now apply h_restricted.
      intuition.
    + destruct H; subst; intuition.
  - intros x y z H H0.
    destruct H as [Ha | Ha]; destruct H0 as [Hb | [Hb Hc]]; subst.
    + now apply h_functional with x. 
    + destruct (h_restricted n y Ha) as [Hd _].
      elim (Nat.lt_irrefl _ Hd).
    + destruct Ha as [Hc Hd]; subst.
      destruct (h_restricted n z Hb) as [Hd _].
      elim (Nat.lt_irrefl _ Hd).
    + tauto.
  - intros x h_x.
    destruct (eq_nat_dec x n).
    + (exists m).
      right; split; trivial.
    + assert (x < n) by lia.
      destruct h_applicative with x as [y Hy].
      assumption.
      exists y.
      left; assumption.
  - intros x y z H H0.
    destruct H as [Ha | [Ha Hb]]; destruct H0 as [Hc | [Hc Hd]]; subst.
    + now apply h_injective with x.
    + destruct (h_restricted y m Ha) as [ _ He].
      elim (Nat.lt_irrefl m He).
    + destruct (h_restricted z m Hc) as [ _ He].
      elim (Nat.lt_irrefl m He).
    + reflexivity.
  - intros y h_y.
    destruct (eq_nat_dec y m).
    exists n.
    right; tauto.
    assert (y < m) by lia.
    destruct h_surjective with y as [x Hx].
    assumption.
    exists x.
    left; assumption.
Qed.


Lemma bijective_lt_eq : 
  forall n m,
    (exists R, bijective (fun k => k < n) (fun k => k < m) R) ->
    n = m.
Proof.
  induction n; destruct m; intro Hbij; destruct Hbij as [R HR].
  - trivial.
  - inversion HR as [Hr Hf Ha Hi Hs]; subst.
    unfold restricted, functionnal, applicative, injective, surjective in *.
    simpl in *.
    assert(0 < S m) by auto with *.
    assert(exists k, R k 0) as Hk by now apply Hs.
    destruct Hk as [k Hk].
    assert(k < 0) as Hk0 by (destruct (Hr k 0); trivial).
    contradict Hk0.
    lia.
  - inversion HR as [Hr Hf Ha Hi Hs]; subst.
    unfold restricted, functionnal, applicative, injective, surjective in *.
    simpl in *.
    assert(0 < S n) by auto with *.
    assert(exists k, R 0 k) as Hk by now apply Ha.
    destruct Hk as [k Hk].
    assert(k < 0) as Hk0 by (destruct (Hr 0 k); trivial).
    contradict Hk0.
    lia.
  - inversion HR as [Hr Hf Ha Hi Hs]; subst.
    simpl in *.
    assert(n < S n) as HnSn by intuition.
    set(Hn:=Ha). destruct (Hn n HnSn) as [rn Hrn]. clear Hn HnSn.
    assert(m < S m) as HmSm by intuition.
    set(Hm:=Hs). destruct (Hm m HmSm) as [rm Hrm]. clear Hm HmSm.
    assert(rn < m <-> rm < n) as H_rn_rm.
    {
      split; intro H.
      - destruct(eq_nat_dec rm n) as [Heq | Hneq].
        + subst. assert(m = rn) by eauto using Hf.
        lia.
        + assert(rm < S n) by (specialize(Hr _ _ Hrm); destruct Hr; trivial).
          lia.
      - destruct(eq_nat_dec rn m) as [Heq | Hneq].
        + subst. assert(n = rm) by eauto using Hf.
        lia.
        + assert(rn < S m) by (specialize(Hr _ _ Hrn); destruct Hr; trivial).
          lia.
    }
    assert(exists R, bijective (fun k=>k<n) (fun k=>k<m) R).
    {
      exists(fun x => fun y =>
                        ( x < n /\ y < m /\R x y) \/
                        ( rn < m /\ x = rm /\ y = rn ) ).
      split.
      - (* restricted *)
        intros x y  H. 
        lia.
      - (* functionnal *)
        intros k0 k1 k2 H1 H2.
        destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
        + destruct H1 as [ Hx1 [ Hy1 Hxy1 ]].
          destruct H2 as [ Hx2 [ Hy2 Hxy2 ]].
          eauto.
        + destruct H1 as [ Hx1 [ Hy1 Hxy1 ]].
          destruct H2 as [ H1 [H2 H4] ].
          subst. 
          assert(k1 = m) by eauto.
          lia.
        + destruct H2 as [ Hx2 [ Hy2 Hxy2 ]].
          destruct H1 as [ H1 [H2 H3] ].
          subst. 
          assert(k2 = m) by eauto.
          lia.
        + lia.
      - (* applicative *)
        intros k Hk.
        assert(k < S n) as Hk_S by intuition.
        destruct(Ha k Hk_S) as [k' Hk'].
        assert(k' < S m) as Hk'_S by (specialize (Hr k k' Hk'); intuition).
        destruct(eq_nat_dec rn m) as [Heq | Hneq].
        + subst. assert(rm = n) by eauto. subst.
          assert(k' < m). 
          {
            destruct(eq_nat_dec k' m) as [Heq | Hneq].
            - subst. assert(k = n) by eauto. lia.
            - lia.
          }
          exists k'. left. auto.
        + destruct(eq_nat_dec k rm) as [H_eq | H_neq].
          * exists rn. right. lia.
          * assert(k' < m).
            {
              destruct(eq_nat_dec k' m) as [Hm | Hm'].
              - subst. assert(k = rm) by eauto. contradict H_neq. trivial.
              - lia.
            }
            exists k'. left. intuition.
      - (* injective *)
        intros k0 k1 k2 H1 H2.
        destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
        + destruct H1 as [ Hx1 [ Hy1 Hxy1 ]].
          destruct H2 as [ Hx2 [ Hy2 Hxy2 ]].
          eauto.
        + destruct H1 as [ Hx1 [ Hy1 Hxy1 ]].
          destruct H2 as [ H1 [H2 H4] ].
          subst.
          assert(k1 = n) by eauto.
          lia.
        + destruct H2 as [ Hx2 [ Hy2 Hxy2 ]].
          destruct H1 as [ H1 [H2 H3] ].
          subst. 
          assert(k2 = n) by eauto.
          lia.
        + lia.
      - (* surjective *)
        intros k' Hk'.
        assert(k' < S m) as Hk'_S by intuition.
        destruct(Hs k' Hk'_S) as [k Hkk'].
        assert(k < S n) as Hk_S by (specialize (Hr _ _ Hkk'); intuition).
        destruct(eq_nat_dec rn m) as [Heq | Hneq].
        + subst. assert(rm = n) by eauto. subst.
          assert(k < n). 
          {
            destruct(eq_nat_dec k n) as [Heq | Hneq].
            - subst. assert(k' = m) by eauto. lia.
            - lia.
          }
          exists k. left. auto.
        + destruct(eq_nat_dec k' rn) as [H_eq | H_neq].
          * exists rm. right. lia.
          * assert(k < n).
            {
              destruct(eq_nat_dec k n) as [Hm | Hm'].
              - subst. assert(k' = rn) by eauto. contradict H_neq. trivial.
              - lia.
            }
            exists k. left. intuition.
    }
    assert(n = m) by eauto.
    auto.
Qed.
