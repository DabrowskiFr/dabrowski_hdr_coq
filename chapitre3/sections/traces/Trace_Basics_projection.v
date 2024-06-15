Require Import List Arith.
Require Import sections.lifo.Prelude.
Require Import sections.common.GenericTrace.
Require Import sections.traces.Trace.

Module Make (SN : MiniDecidableSet )
            (Export Ad : DecidableInfiniteSet) 
            (Export Ty : Type_.TYPE Ad)
            (Export Va : Value.TYPE Ad Ty)
            (Import Tr : Trace.T SN Ad Ty Va).

  Hint Constructors singleAction.

  Lemma eq_action_dec : 
    forall (a a' : action), {a = a'} + {a <> a'}.
  Proof.  
    repeat decide equality; 
    try ( apply SN.eq_dec || apply Ad.eq_dec || apply Va.eq_dec).
  Qed.
  
  Lemma open_action_dec  : 
    forall (a : action), (exists p, a = Open p) \/ (forall p, a <> Open p).
  Proof.
    destruct a; solve [ left; eauto | right; intuition discriminate].
  Qed.
  
  Lemma singleAction_dec : forall a, {singleAction a} + { ~ singleAction a}.
  Proof.
    destruct a; solve [auto | right; intro Ha; inversion Ha].
  Qed.
    
End Make.

Module Type Proj 
       (SN : MiniDecidableSet )
       (Export Ad : DecidableInfiniteSet) 
       (Export Ty : Type_.TYPE Ad)
       (Export Va : Value.TYPE Ad Ty)
       (Import Tr : Trace.T SN Ad Ty Va).
  Include Make SN Ad Ty Va Tr.
End Proj.
