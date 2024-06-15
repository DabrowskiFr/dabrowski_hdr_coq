Require Import sections.lifo.Prelude.

Lemma subst {A B:Type}{x y : A}{f : A -> B}: x = y -> f y = f x.
Proof.
  intro. rewrite H. reflexivity.
Qed.

Definition cast {A B:Prop}(H : A = B) : A -> B.
Proof.
  intros a.
  rewrite <- H.
  exact a.
Defined.

Module Type T (Ad : DecidableInfiniteSet)
       (Sz : MiniDecidableSet).

  Parameter is_valid : Sz.t -> Sz.t -> Prop.
  Parameter is_valid_dec : 
    forall o size, { is_valid o size } + { ~ is_valid o size }.

  Parameter value_t : Type.

  Parameter default : value_t.

  Parameter null : Ad.t.

  Parameter t : Type.

  Parameter empty : t.

  Parameter in_domain : t -> Ad.t -> Prop.
  Parameter in_domain_dec : 
    forall h a, { in_domain h a } + { ~ in_domain h a }.


  Parameter allocate : t -> Sz.t -> Ad.t -> t -> Prop.

  Parameter size_of : forall (heap : t) (a : Ad.t), in_domain heap a -> Sz.t.

  Parameter free : forall (heap : t) (a : Ad.t), in_domain heap a -> t.

  Parameter get : forall (heap : t) (a : Ad.t) (Ha: in_domain heap a)
                         (o : Sz.t), is_valid o (size_of heap a Ha) -> value_t.

  Parameter set : forall (heap : t) (a : Ad.t) (Ha: in_domain heap a)(o : Sz.t), 
                    is_valid o (size_of heap a Ha) -> value_t -> t.

  Axiom is_valid_inj : 
    forall (o n : Sz.t)(H1 H2 : is_valid o n), H1 = H2.
  
  Axiom in_domain_inj : 
    forall heap address (H1 H2 : in_domain heap address), H1 = H2.

  Axiom empty_domain : 
    forall address, ~ (in_domain empty address).

  Axiom null_not_in_domain:
    forall heap, ~(in_domain heap null).
  
  Axiom allocate_in_domain: 
    forall {heap} {size} {address} {heap'}, 
      allocate heap size address heap' -> 
      in_domain heap' address.
  
  Axiom allocate_not_in_domain: 
    forall {heap} {size} {address} {heap'}, 
      allocate heap size address heap' -> 
      ~ in_domain heap address.

  Axiom allocate_size_of: 
    forall {heap} {size} {address} {heap'} (alloc: allocate heap size address heap'),
      size_of heap' address (allocate_in_domain alloc) = size.

  Axiom allocate_get:
    forall (h : t) (s : Sz.t) (a : Ad.t) (h' : t) (alloc : allocate h s a h') 
           (o : Sz.t) (Hoffset : is_valid o s),
      get h' a (allocate_in_domain alloc) o 
         (cast (subst (allocate_size_of alloc)) Hoffset) = default.

  Axiom free_not_in_domain: 
    forall heap address (Ha: in_domain heap address),
      ~ in_domain (free heap address Ha) address.

  Axiom in_domain_set:
    forall {h} {a} {Ha} {o} {Ho} {v} {a'},
      in_domain h a' ->
      in_domain (set h a Ha o Ho v) a'.

  Axiom size_of_set:
    forall {h} {a} {Ha} {o} {Ho} {v} {a'} {Ha'},
      in_domain h a' ->
      size_of (set h a Ha o Ho v) a' (in_domain_set Ha') = size_of h a' Ha'.

  Axiom get_set_same:
    forall (h : t) 
           (a : Ad.t) (Ha : in_domain h a)
           (o : Sz.t) (Ho : is_valid o (size_of h a Ha))
           (v : value_t), 
      get (set h a Ha o Ho v) a (in_domain_set Ha) o 
          (cast (subst (size_of_set Ha)) Ho) = v.

  Axiom get_set_diff:
    forall (h : t) 
           (a : Ad.t) (Ha : in_domain h a)
           (o : Sz.t) (Ho : is_valid o (size_of h a Ha))
           (a' : Ad.t) (Ha' : in_domain h a')
           (o' : Sz.t) (Ho' : is_valid o' (size_of h a' Ha'))
           (v : value_t),
      ~ a = a' \/ ~ o = o' ->  
      get (set h a Ha o Ho v) a' (in_domain_set Ha') o' 
          (cast (subst (size_of_set Ha')) Ho') =
      get h a' Ha' o' Ho'.

End T.

Require Import Type_ Value.

Module Type T_VALUE
       (Ad : DecidableInfiniteSet)
       (Ty : Type_.TYPE Ad)
       (Va : Value.TYPE Ad Ty) := T Ad Natural with Definition value_t := Va.t.
  