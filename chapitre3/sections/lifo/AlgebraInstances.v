Require Import Program.
Require Export Coq.Classes.Init.
Require Import sections.lifo.AlgebraClasses.

Generalizable All Variables.

(** *Type classes  *)
(** Usual Instances for algebra concepts *)

(** flip arguments preserves properties
 (using [flip] function heavily used by Proper, etc.)  
Instance added by hand in the [typeclass_instances] hint instead of using Instance declaration. This is to prevent loop in instance search.
*)


Definition neutral_flip A Ra RaEquiv f e
           `{neutral_f : @Neutral A Ra RaEquiv f e} 
: Neutral (flip f) e.
Proof.
  constructor;
  unfold flip.
  - destruct neutral_f;
    constructor;
    intros; simpl.
    apply right_neutral.
  -constructor ; intros; simpl.
   apply left_neutral.
Qed.

Hint Extern 1 (Neutral (flip _ ) _)=> apply @neutral_flip : typeclass_instances.


Definition commut_flip A Ra RaEquiv f 
           `{assoc_f : @Commutative A Ra RaEquiv f} 
: Commutative (flip f).
Proof.
  constructor.
  unfold flip.
  intros x y.
  rewrite (commutative).
  reflexivity.
Qed.


Hint Extern 1 (Commutative (flip _ ))=> apply @commut_flip : typeclass_instances.

Definition assoc_flip A Ra RaEquiv f 
           `{assoc_f : @Associative A Ra RaEquiv f} 
: Associative (flip f).
Proof.
  constructor.
  unfold flip.
  intros x y z.
  rewrite (associative).
  reflexivity.
Qed.

Hint Extern 1 (Associative (flip _ )) => apply assoc_flip : typeclass_instances.

Definition SemiGroup_flip A Ra RaEquiv f 
           `{semigroup_f : @SemiGroup A Ra RaEquiv f} 
: SemiGroup (flip f).
Proof.
  constructor.  
  destruct semigroup_f.
  typeclasses eauto.
Qed.  
Hint Extern 1 (SemiGroup (flip _ ))=> apply @SemiGroup_flip : typeclass_instances.

Definition QuasiGroup_flip A Ra RaEquiv f 
           `{quasigroup_f : @QuasiGroup A Ra RaEquiv f} 
: QuasiGroup (flip f).
Proof.
  constructor.
  intros a b.
  unfold flip.
  destruct (quasiGroupLaw(op:=f) a b)  as [ y [[x [law x_unicity]] y_unicity]] .
  exists x.
  split. 
  - exists y.
           split.    
           + tauto.
           + intros x' H.
             apply y_unicity.
             exists x.
             split. 
             * tauto.
             * intros x'0 H0. apply x_unicity. tauto.
           - intros x' H.
             apply x_unicity.
             destruct H. destruct H. tauto.
Qed.


Hint Extern 1 (QuasiGroup (flip _ ))=> apply @QuasiGroup_flip : typeclass_instances.

Program Definition Monoid_flip  A Ra RaEquiv f e
        `{monoid_f : @Monoid A Ra RaEquiv f e} 
: Monoid (flip f) e. 
Proof.
  constructor;destruct monoid_f. 
  typeclasses eauto.
  typeclasses eauto.
Qed.    

Hint Extern 1 (Monoid (flip _ ) _)=> apply @Monoid_flip : typeclass_instances.

Program Definition CommutativeMonoid_flip  A Ra RaEquiv f e
        `{commutativemonoid_f : @CommutativeMonoid A Ra RaEquiv f e} 
: CommutativeMonoid (flip f) e. 
Proof.
  (* intros A Ra RaEquiv f e commutativemonoid_f. *)
  constructor; 
  destruct commutativemonoid_f; 
  typeclasses eauto.
Qed.    
Hint Extern 1 (CommutativeMonoid (flip _ ) _)=> apply @CommutativeMonoid_flip : typeclass_instances.

Definition Group_flip  A Ra RaEquiv f e
           `{group_f : @Group A Ra RaEquiv f e} 
: Group (flip f) e. 
Proof.
  constructor; destruct group_f;   
  try typeclasses eauto.   
  intros x.
  simpl. 
  unfold flip.
  destruct (groupInverse x) as [x' Inv].
  exists x'; tauto.
Qed.
Hint Extern 1 (Group (flip _ ) _)=> apply @Group_flip : typeclass_instances.

Definition CommutativeGroup_flip  A Ra RaEquiv f e
           `{commut_group_f : @CommutativeGroup A Ra RaEquiv f e} 
: CommutativeGroup (flip f) e. 
Proof.
  constructor; destruct commut_group_f;   
  try typeclasses eauto.   
Qed. 


Hint Extern 1 (CommutativeGroup (flip _ ) _)=> apply @CommutativeGroup_flip : typeclass_instances.

Program Definition Distributivity_flip_left  A Ra RaEquiv otime oplus
        `{distributivity : @Distributivity A Ra RaEquiv otime oplus} 
: Distributivity (flip otime) oplus. 
Proof.
  intros; unfold flip; constructor; apply distributivity.
Qed.  
(* Solve Obligations using (intros; unfold flip; apply distributivity). *)



Hint Extern 1 (Distributivity (flip _ ) _)=> apply @Distributivity_flip_left : typeclass_instances.

Program Definition Distributivity_flip_right  A Ra RaEquiv otime oplus
        `{distributivity : @Distributivity A Ra RaEquiv otime oplus} 
: Distributivity otime (flip oplus). 
Proof.
  constructor;intros; unfold flip; apply distributivity.
Qed.


Hint Extern 1 (Distributivity _ (flip _ ))=> apply @Distributivity_flip_right : typeclass_instances.

Program Definition SemiRing_flip_right  A Ra RaEquiv otime oplus a b
        `{semiring : @SemiRing A Ra RaEquiv otime oplus a b} 
: SemiRing otime (flip oplus) a b.
Proof.
  constructor;  intros; destruct semiring; try typeclasses eauto .
  unfold flip.
  pose (semiRingNil a0). tauto. 
Qed. 


Hint Extern 1 (SemiRing _ (flip _ ) _ _)=> apply @SemiRing_flip_right : typeclass_instances.

Program Definition SemiRing_flip_left  A Ra RaEquiv otime oplus a b
        `{semiring : @SemiRing A Ra RaEquiv otime oplus a b} 
: SemiRing (flip otime) oplus a b.
Proof. 
  constructor; 
  intros; destruct semiring; try typeclasses eauto.   
  pose (semiRingNil a0). tauto. 
Qed. 



Hint Extern 1 (SemiRing (flip _ ) _ _ _)=> apply @SemiRing_flip_left : typeclass_instances.

Program Definition Ring_flip_right  A Ra RaEquiv otime oplus a b
        `{ring : @Ring A Ra RaEquiv otime oplus a b} 
: Ring otime (flip oplus) a b. 
Proof.
  constructor;
  intros; destruct ring; try typeclasses eauto.
Qed.


Hint Extern 1 (Ring _ (flip _ ) _ _)=> apply @Ring_flip_right : typeclass_instances.

Program Definition Ring_flip_left  A Ra RaEquiv otime oplus a b
        `{ring : @Ring A Ra RaEquiv otime oplus a b} 
: Ring (flip otime) oplus a b. 
Proof. 
  constructor; intros; destruct ring; try typeclasses eauto.   Qed.




Hint Extern 1 (Ring (flip _ ) _ _ _)=> apply @Ring_flip_left : typeclass_instances.

Program Definition CommutativeRing_flip_right  A Ra RaEquiv otime oplus a b
        `{commutativering : @CommutativeRing A Ra RaEquiv otime oplus a b} 
: CommutativeRing otime (flip oplus) a b. 
Proof.  
  constructor ;intros; destruct commutativering; try typeclasses eauto.
Qed.

Hint Extern 1 (CommutativeRing _ (flip _ ) _ _)=> apply @CommutativeRing_flip_right : typeclass_instances.

Program Definition CommutativeRing_flip_left  A Ra RaEquiv otime oplus a b
        `{commutativering : @CommutativeRing A Ra RaEquiv otime oplus a b} 
: CommutativeRing (flip otime) oplus a b. 
Proof. 
  constructor; intros; destruct commutativering; try typeclasses eauto.   
Qed.

Hint Extern 1 (CommutativeRing (flip _ ) _ _ _)=> apply @CommutativeRing_flip_left : typeclass_instances.


(** Nat is a Semi Ring. *)
Require Import Arith.
(**  0 is neutral for addition in nat *)
Program Instance plus_neutral : Neutral plus 0.
(**  addition in nat is commutative *)
Program Instance commutative_plus :  Commutative plus.
Next Obligation. auto with arith. Qed.
(**  addition in nat is associative *)
Program Instance associative_plus :  Associative plus.
Next Obligation. auto with arith. Qed.
(**  nat with addition is a commutative monoid *)
Program Instance commutativeMonoid_plus : CommutativeMonoid plus 0.

Global Program Instance monoid_plus_zero : Monoid plus 0.
(**  multiplication in nat is associative *)
Program Instance associative_mult : Associative mult.
Next Obligation. auto with arith. Qed.
(**  1 is neutral for multiplication in nat *)
Program Instance neutral_mult : Neutral mult 1.
(**  multiplication in nat is associative *)
Program Instance commutative_mult : Commutative mult.
Next Obligation. auto with arith. Qed.
(**  nat with multiplication is a Commutative Monoid *)
Program Instance commutativeMonoid_mult : CommutativeMonoid mult 1.
(**  multiplication is distributive over addition in nat *)
Program Instance distributive_mult_plus : Distributivity mult plus.
Next Obligation.
  repeat rewrite (commutative (op:=mult) x).
  auto with arith.
Qed.
Next Obligation. auto with arith. Qed.
(**  nat with multiplication and addition is a SemiRing *)
Program Instance SemiRing_nat : SemiRing plus mult 0 1.


(** *Z is a ring*)
Require Import ZArith.
Open Scope Z_scope.
(**  0 is neutral for addition in Z *)
Program Instance Zplus_neutral : Neutral (eqA:=eq) Zplus 0.
(**  addition in Z is commutative *)
Program Instance Zplus_commutative :  Commutative (eqA:=eq) Zplus.
Next Obligation.  (intros;auto with zarith). Qed.
(**  addition in Z is associative *)
Program Instance Zplus_associative :  Associative (eqA:=eq) Zplus.
Next Obligation.   (intros;auto with zarith). Qed.
(**  Z with addition is a group *)
Program Instance group_Zplus : Group (eqA:=eq) Zplus 0.
Next Obligation.  exists (-x); auto with zarith. Qed.
(**  Z with addition is a commutative group *)
Program Instance commutativeGroup_Zplus : CommutativeGroup (eqA:=eq) Zplus 0.
(**  multiplication in Z is associative *)
Program Instance associative_zmult : Associative (eqA:=eq) Zmult.
Next Obligation.   (auto with zarith). Qed.
(**  1 is neutral for multiplication in Z *)
Program Instance neutral_zmult : Neutral (eqA:=eq) Zmult 1.
(**  Z with multiplication is a Monoid *)
Program Instance monoid_zmult : Monoid (eqA:=eq) Zmult 1.
(**  multiplication is distributive over addition in Z *)
Program Instance distributive_zmult_zplus : Distributivity (eqA:=eq) Zmult Zplus.
Next Obligation.   (auto with zarith). Qed.
Next Obligation.   (auto with zarith). Qed.
(**  Z with multiplication and addition is a Ring *)
Program Instance Ring_Z : Ring (eqA:=eq) Zplus Zmult 0 1. 
Close Scope Z_scope.

(** Bool is a Semi Ring  *)
Require Import Bool.
Open Scope bool_scope.
Program Instance orb_neutral : Neutral orb false. 
Program Instance orb_commutative :  Commutative orb.
Next Obligation.  (auto with bool). Qed.
Program Instance orb_associative :  Associative  orb.
Next Obligation.  (auto with bool). Qed.
Program Instance commutative_monoid_orb : CommutativeMonoid orb false.
Program Instance andb_neutral : Neutral andb true.
Program Instance andb_commutative :  Commutative andb.
Next Obligation.  (auto with bool). Qed.
Program Instance andb_associative :  Associative  andb.
Next Obligation.  (auto with bool). Qed.
Program Instance commutative_monoid_andb : CommutativeMonoid andb true.
Program Instance distributive_andb_orb : Distributivity andb orb.
Next Obligation. case x; case y ;  case z ; unfold orb; reflexivity. Qed.
Next Obligation. case x; case y ;  case z ; unfold orb; reflexivity. Qed.
Program Instance distributive_orb_andb : Distributivity orb andb.
Next Obligation.  case x; case y ;  case z ; auto with bool. Qed.
Next Obligation.  case x; case y ;  case z ; auto with bool. Qed.
Program Instance SemiRing_bool : SemiRing andb orb true false.
Next Obligation.  auto with bool. Qed.
Close Scope bool_scope.

Module semiRingProp. 
  
  Program Instance or_neutral : Neutral or False. 
  Next Obligation.  constructor; tauto. Qed.
  Next Obligation.  constructor; tauto. Qed.
  
  Program Instance or_commutative :  Commutative or.
  Next Obligation.  tauto. Qed.
  
  Program Instance or_associative :  Associative  or.
  Next Obligation. tauto. Qed.

  Program Instance commutative_monoid_or : CommutativeMonoid or False.
  Next Obligation.  constructor; typeclasses eauto. Qed.

  Program Instance and_neutral : Neutral and True.
  Next Obligation.  (constructor;tauto). Qed.
  Next Obligation.  (constructor;tauto). Qed.

  Program Instance and_commutative :  Commutative and.
  Next Obligation.  (tauto). Qed.

  Program Instance and_associative :  Associative  and.
  Next Obligation.  (tauto). Qed.

  Program Instance commutative_monoid_and : CommutativeMonoid and True.
  Next Obligation.  (constructor; typeclasses eauto). Qed.


  Program Instance distributive_and_or : Distributivity and or.
  Next Obligation.  (tauto). Qed.
  Next Obligation.  (tauto). Qed.

  Program Instance distributive_or_and : Distributivity or and.
  Next Obligation.  (tauto). Qed.
  Next Obligation.  (tauto). Qed.

  Program Instance SemiRing_prop : SemiRing and or True False.
  Next Obligation.  (typeclasses eauto || tauto). Qed.

End semiRingProp.


(* Section FieldQ. *)
Require Import QArith. 
Open Scope Q_scope.

Program Instance Q_neutral : Neutral (eqA:=Qeq) Qplus 0.

Program Instance Qplus_commutative :  Commutative  (eqA:=Qeq) Qplus.
Next Obligation.
  apply Qplus_comm.
Qed.

Program Instance Qplus_associative :  Associative  Qplus.
Next Obligation.  (intros;symmetry;apply Qplus_assoc). Qed.

Program Instance group_Qplus : Group Qplus 0. 
Next Obligation.
  exists (-x). 
  split.
  - apply (Qplus_opp_r x).
  - rewrite commutative. apply (Qplus_opp_r x).
Qed.

Program Instance commutativeGroup_Qplus : CommutativeGroup Qplus 0.

Program Instance Qmult_neutral : Neutral Qmult 1.

Program Instance Qmult_commutative :  Commutative Qmult.
Next Obligation.  (apply Qmult_comm). Qed.

Program Instance Qmult_associative :  Associative  Qmult.
Next Obligation.  (symmetry; apply Qmult_assoc). Qed.

Program Instance multiplicativeGroup_Qmult : MultiplicativeGroup Qmult 1 0.
Next Obligation.
  exists (/x).
  apply Qmult_inv_r.
Qed.


Program Instance distributive_Qmult_Qplus : Distributivity Qmult Qplus.
Next Obligation.
  apply Qmult_plus_distr_r.
Qed.
Next Obligation.
  apply Qmult_plus_distr_l.
Qed.


Program Instance Field_bool : Field Qplus Qmult 0 1.
Close Scope Q_scope.

(*
*** Local Variables:
*** coq-load-path: (("../../LIFO" "LIFO"))
*** End:
*)