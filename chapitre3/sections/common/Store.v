Require Import Program Coq.Classes.Equivalence.

Require Import sections.lifo.Prelude Value.

Module Type T (Id Ad : DecidableInfiniteSet)
       (Ty : Type_.TYPE Ad) (Vl : Value.TYPE Ad Ty).

  Parameter t : Type.

  Parameter empty : t.

  Parameter set : t -> Id.t -> Vl.t -> t.

  Parameter get : t -> Id.t -> option Vl.t.

  Axiom get_empty : 
    forall id, get empty id = None.

  Axiom get_set_same : 
    forall store id val, 
      get (set store id val) id = Some val.

  Axiom get_set_diff : 
    forall store id id' val, 
      ~ id = id' -> 
      get (set store id val) id' =  get store id'.

End T.

(*Module Type M (Id Ad : DecidableInfiniteSet) 
       (Ty : Type_.TYPE Ad) (Vl : Value.TYPE Ad Ty).
  Include T Id Ad Ty Vl.
End M.*)

Module I 
       (Id : DecidableInfiniteSet)
       (Ad : DecidableInfiniteSet)
       (Ty : Type_.TYPE Ad)
       (Vl : Value.TYPE Ad Ty) : T Id Ad Ty Vl.
  
  Definition t := Id.t -> option Vl.t.

  Definition empty : t := fun _ => None.

  Definition get (store : t) (id : Id.t) := store id.

  Definition set (store : t) (id : Id.t) (v : Vl.t) := 
    fun i => if Id.eq_dec i id 
             then Some v
             else store i.

  Lemma get_empty : forall id, get empty id = None.
  Proof. intros; auto. Qed.

  Lemma get_set_same : 
    forall store id val, get (set store id val) id = Some val.
  Proof. 
    intros; unfold get, set.
    case_eq(Id.eq_dec id id); intros H _.
    - trivial.
    - contradict H; trivial.
  Qed.
      
  Lemma get_set_diff : 
    forall store id id' val, 
      ~ id = id' -> get (set store id val) id' =  get store id'.
  Proof.
    intros store id id' val H.
    intros; unfold get, set.
    case_eq(Id.eq_dec id' id); intros H' _.
    - contradict H; auto.
    - trivial.
  Qed.

End I.

Module Type P (Id Ad : DecidableInfiniteSet)
       (Ty : Type_.TYPE Ad)
       (Vl : Value.TYPE Ad Ty)
       (St : T Id Ad Ty Vl) <: T Id Ad Ty Vl.

  Include St.

  Definition eq (s1 s2 : St.t) : Prop := 
    forall id, get s1 id = get s2 id.

  Local Infix "===" := eq.

  Program Instance eq_equiv : Equivalence eq.
  Next Obligation.
    intros s id; trivial.
  Qed.
  Next Obligation.
    intros s s' H id. auto.
  Qed.
  Next Obligation.
    intros s s' s'' H1 H2 id. 
    now rewrite H1, H2.
  Qed.

  Lemma set_comm : 
    forall store id1 id2 v1 v2, 
      ~ id1 = id2 -> 
      set (set store id1 v1) id2 v2 === set (set store id2 v2) id1 v1.
  Proof.
    intros store id1 id2 v1 v2 H id.
    case_eq(Id.eq_dec id id2); intros Heq _; subst.
    - rewrite get_set_same.
      rewrite get_set_diff by auto.
      now rewrite get_set_same.
    - rewrite get_set_diff by auto.
      case_eq(Id.eq_dec id id1); intros Heq' _; subst.
      + now repeat rewrite get_set_same.
      + now repeat rewrite get_set_diff by auto.
  Qed.

End P.