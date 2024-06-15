(** printing Sigma #&Sigma;# *) (** printing pi  #&pi;#*)
(** printing nat #&#8469;#*)
(** printing exists #&exist;# *) (** printing forall #&forall;# *)
(** printing /\ #&and;# *) (** printing \/ #&or;# *)
(** printing -> #&#x02192;# *)
(** printing • #&#8226;# *)

Require Import List Arith.
Require Import sections.lifo.Prelude.
Require Import sections.common.GenericTrace.
Require Import sections.traces.Trace.
Require Import sections.traces.Trace_Basics_projection.
Require Import sections.traces.Trace_Basics_occurences.
Require Import sections.traces.Trace_Basics_father.
Require Import sections.traces.Trace_Basics_owns.
Require Import sections.traces.Trace_Basics_range.
Require Import sections.traces.Trace_Basics_see.
Require Import sections.traces.Trace_Basics_tribe.
Require Import sections.traces.Trace_Basics_exclude.
Require Import sections.traces.Trace_Basics_wellFormed.

Module Make (Perm : MiniDecidableSet)
            ( Export Address: DecidableInfiniteSet) 
            ( Export T : Type_.TYPE Address )
            ( Export V : Value.TYPE Address T ).
  
  
  Include Trace.Make Perm Address T V.
  Include Trace_Basics_projection.Make Perm Address T V.
  Include Trace_Basics_occurences.Make Perm Address T V.  
  Include Trace_Basics_father.Make Perm Address T V.
  Include Trace_Basics_owns.Make Perm Address T V.
  Include Trace_Basics_range.Make Perm Address T V.
  Include Trace_Basics_see.Make Perm Address T V.
  Include Trace_Basics_tribe.Make Perm Address T V.
  Include Trace_Basics_exclude.Make Perm Address T V.
  Include Trace_Basics_wellFormed.Make Perm Address T V.

End Make.


Module Type TYPE 
       ( Perm : MiniDecidableSet)
       ( Export Address: DecidableInfiniteSet) 
       ( Export T : Type_.TYPE Address )
       ( Export V : Value.TYPE Address T ).
 Include Make Perm Address T V.
End TYPE. 
