Require Import Lt Peano_dec Compare_dec Relation_Operators List Morphisms.
From sections.lifo Require Import Prelude BijRel.
From sections.traces Require Import Synchronisation.

Module Make (P : MiniDecidableSet)
       ( Export Address: DecidableInfiniteSet) 
       ( Export T : Type_.TYPE Address )
       ( Export V : Value.TYPE Address T ).

  Include Synchronisation.Make P Address T V.
   
  Definition compatible_by R (s1 s2 : Tr) :=
    bijective (fun k => k < length s1) (fun k => k < length s2) R
    /\ (forall i j, R i j -> pi i s1 = pi j s2)
    /\ (forall i j i' j', 
          R i j -> R i' j' ->  (synchronizeWith s1 i i' <-> synchronizeWith s2 j j')).

  Definition compatible (s1 s2 : Tr) := exists R, compatible_by R s1 s2.

  Infix "~=" :=compatible (at level 70):trace_scope. 

  Open Scope trace_scope.
  
  Lemma compatible_refl : Reflexive compatible.
  Proof.
    intros s.
    exists (identity_R (fun k => k < length s)).
    split.
    - apply identity_R_bijective.
    - split.
      + intros i j h_i_j.
        assert (i = j) by now inversion h_i_j.
        congruence.
      + intros i j i' j' h_i_j h_i'_j'.
        inversion h_i_j; inversion h_i'_j'.
        split; congruence.
  Qed.

  Lemma compatible_sym : Symmetric compatible.
  Proof.
    intros s s' h_compatible.
    destruct h_compatible as [R [h_bijective [h_eq h_sync ]]].
    exists (inverse R).
    split.
    - apply inverse_bijective in h_bijective.
      apply h_bijective.
    - split.
      + intros i j h.
        symmetry.
        now apply h_eq.
      + intros i j i' j' h1 h2.
        split.
        { intro h3.
          now apply (h_sync j i j' i').
          }
          { intro h3.
            now apply (h_sync j i j' i').
          }
Qed.

  Lemma compatible_trans : Transitive compatible. 
  Proof.
    intros s1 s2 s3 h_comp1 h_comp2.
    destruct h_comp1 as [R1 [h_bijective1 [h_eq1 h_sync1]]].
    destruct h_comp2 as [R2 [h_bijective2 [h_eq2 h_sync2 ]]].
    exists (composition R1 R2).
    split.
    - now apply composition_bijective with (fun k => k < length s2).
    - split.
      + intros i j [k [h1 h2]].
        transitivity (pi k s2);[ now apply h_eq1 | now apply h_eq2].
      + intros i j i' j' [k1 [h1 h2]] [k2 [h3 h4]].
          split; intro ha.
        { apply (h_sync2 k1 j k2 j' h2 h4).
          now apply (h_sync1 i k1 i' k2 h1 h3).
        }
        { apply (h_sync1 i k1 i' k2 h1 h3).
          now apply (h_sync2 k1 j k2 j' h2 h4).
        }
Qed.

  Lemma symmetric_compatible_R :
    forall R s1 s2,
      compatible_by R s1 s2 ->
      compatible_by (inverse R) s2 s1.
  Proof.
    intros R s1 s2 h_compatible.
    destruct h_compatible as  [h_bijective [h_eq h_sync ]].
    split.
    - apply inverse_bijective in h_bijective.
      apply h_bijective.
    - split.
      + intros i j h.
        symmetry.
        now apply h_eq.
      + intros i j i' j' h1 h2.
        split.
        { intro h3.
          now apply (h_sync j i j' i').
          }
        { intro h3.
          now apply (h_sync j i j' i').
        }
Qed.

  Instance compatible_equivalence : Equivalence compatible.
  Proof.
    split; [apply compatible_refl | apply compatible_sym | apply compatible_trans].
  Qed.
  
End Make.    
