Require Import Program Vector.
Require Import VectorTheory.
Require Import Syntax.
Require Import Semantics SemanticsTheory.
Require Import Coq.Relations.Operators_Properties.

Module Alignment (Import P : Process) (Import V : Vector P).

  Module Export ST := SemanticsTheory P V.

  (** * Definition of alignment *)

  Definition aligned_for (s : stmt) (vsigma : V.t store) :=
    forall vst,
      reachable ((replicate s vsigma)) (inl vst) ->
      forall i j st_i st_j p_i p_j st_i' st_j',
        π i vst = Some st_i ->
        π j vst = Some st_j ->
        red i st_i p_i st_i' ->
        red j st_j p_j st_j' ->
        p_i = p_j.
  
  Definition aligned (s : stmt) := forall vsigma, aligned_for s vsigma.

End Alignment.
