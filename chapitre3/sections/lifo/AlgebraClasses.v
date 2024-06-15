Require Import Program.
Require Export Coq.Classes.Init.
Require Export Coq.Classes.RelationClasses.
Require Import Setoid.
Generalizable All Variables.

(** *Type classes for abstract algebra concepts *)

(** Unit  *)
Class Neutral_old `{equ : Equivalence A eqA} (op: A -> A -> A) (e : A) :=
  {
    left_neutral_old  : forall a, eqA (op e a) a;
    right_neutral_old : forall a, eqA (op a e)  a
  }.

(** Unit  *)
Class NeutralLeft {B}  `{equ : Equivalence A eqA} (op: B -> A -> A) (e : B) :=
  {
    left_neutral  : forall a, eqA (op e a) a
  }.

Class NeutralRight {B} `{equ : Equivalence A eqA} (op: A -> B -> A) (e : B) :=
  {
    right_neutral : forall a, eqA (op a e)  a
  }.

Class Neutral `{equ : Equivalence A eqA} (op: A -> A -> A) (e : A) :=
  {
    NEUTRAL_left_neutral  ::  NeutralLeft op e;
    NEUTRAL_right_neutral ::  NeutralRight op e
  }.



(** Commutativity  *)
Class  Commutative `{equ : Equivalence A eqA} (op: A -> A -> A) :={
                                                                    commutative : forall (x y: A), eqA (op  x y) (op y x)
                                                                  }.

(** Associativity  *)
Class  Associative `{equ : Equivalence A eqA} (op: A -> A -> A) :={
                                                                    associative : forall (x y z: A), eqA (op (op x y) z) (op x (op y z))
                                                                  }.

(** Semi-Group *)
Class SemiGroup  `{equ : Equivalence A eqA} (op : A->A->A) :=
  {
    SemiGroup_Associative :: Associative op
  }.

(** Quasi-Group *)
Class QuasiGroup `{equ : Equivalence A eqA} (op : A->A->A) :=
  {
    quasiGroupLaw : forall a b :A, exists  !x, exists !y, eqA (op a x)  b /\ eqA (op y a) b
  }.

(** Monoid definition  *)
Class Monoid   `{equ : Equivalence A eqA} (op : A->A->A) (e : A)  := 
  {
    Monoid_Associative :: Associative op; 
    Monoid_Neutral :: Neutral op e
  }.

(** Commutative Monoid definition  *)
Class CommutativeMonoid `{equ : Equivalence A eqA} (op : A->A->A) (e : A)  := 
  {
    CommutativeMonoid_Commutative :: Commutative op;
    CommutativeMonoid_Monoid ::  Monoid op e
  }.

(** Group definition  *)
Class Group  `{equ : Equivalence A eqA} (op : A->A->A) (e:A):= 
  {
    Group_Associative : Associative op; 
    Group_Neutral : Neutral op e ;
    groupInverse : forall x:A, exists x', (eqA (op x x') e /\ eqA (op x' x) e)
  }.

(** Commutative Group definition  *)
Class CommutativeGroup  `{equ : Equivalence A eqA} (op : A->A->A) (e:A) := 
  {
    CommutativeGroup_Commutative : Commutative op; 
    CommutativeGroup_Group : Group op e
  }.

(** Multiplicative Group definition  *)
Class MultiplicativeGroup  `{equ : Equivalence A eqA} (op : A->A->A) (neutral absorbant:A) := 
  { 
    MultiplicativeGroup_Associative :: Associative op; 
    MultiplicativeGroup_Neutral :: Neutral op neutral ;
    multiplicativeGroupInverse : forall x:A, exists x', ~ eqA x absorbant -> eqA (op x x') neutral
  }.

(**  Distributivity of otime over oplus  *)
Class Distributivity  `{equ : Equivalence A eqA} `(otimes : A->A->A) (oplus  : A->A->A):={
                                                                                           leftDistributivity : forall (x y z : A), 
                                                                                                                  eqA (otimes x (oplus y z))  (oplus (otimes x y) (otimes x z));
                                                                                           rightDistributivity : forall (x y z : A), 
                                                                                                                   eqA (otimes (oplus y z) x)  (oplus (otimes y x) (otimes z x))
                                                                                         }.

(** SemiRing definition *)
Class SemiRing `{equ : Equivalence A eqA} `(oplus : A->A->A) (otimes : A->A->A)  (ep et : A) :=
  {
    SemiRing_Monoid_p : CommutativeMonoid oplus ep;
    SemiRing_Monoid_t : Monoid otimes et;
    SemiRing_Distributivity :: Distributivity otimes oplus;
    semiRingNil : forall a, eqA (otimes ep a) ep /\ eqA (otimes a ep) ep 
  }.

(** Ring definition *)
Class Ring  `{equ : Equivalence A eqA} (oplus : A->A->A) (otimes : A->A->A)  (ep et : A) :=
  {
    Ring_CommutativeGroup_p : CommutativeGroup oplus ep;
    Ring_Monoid_t : Monoid otimes et;
    Ring_Distributivity :: Distributivity otimes oplus
  }.

(** Commutative Ring definition *)
Class CommutativeRing  `{equ : Equivalence A eqA} (oplus : A->A->A) (otimes : A->A->A)  (ep et : A) :=
  {
    CommutativeRing_CommutativeGroup_p : CommutativeGroup oplus ep;
    CommutativeRing_Monoid_t : Monoid otimes et;
    CommutativeRing_Commutative_t :: Commutative otimes;
    CommutativeRing_Distributivity :: Distributivity otimes oplus
  }.

(** Commutative Ring definition *)
Class Field  `{equ : Equivalence A eqA} (oplus : A->A->A) (otimes : A->A->A)  (ep et : A) :=
  {
    Field_CommutativeGroup_p : CommutativeGroup oplus ep;
    Field_Group_t : MultiplicativeGroup otimes et ep;
    Fiel_Distributivity :: Distributivity otimes oplus
  }.

(** Usual Instances *)

(** flip arguments (using flip function heavily used by Proper, etc.) preserves properties  *)


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
  (* intros A Ra RaEquiv f e commutativemonoid_f;  *)
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
  destruct (groupInverse0 x) as [x' Inv].
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
  pose (semiRingNil0 a0). tauto. 
Qed. 


Hint Extern 1 (SemiRing _ (flip _ ) _ _)=> apply @SemiRing_flip_right : typeclass_instances.

Program Definition SemiRing_flip_left  A Ra RaEquiv otime oplus a b
        `{semiring : @SemiRing A Ra RaEquiv otime oplus a b} 
: SemiRing (flip otime) oplus a b.
Proof. 
  constructor; 
  intros; destruct semiring; try typeclasses eauto.   
  pose (semiRingNil0 a0). tauto. 
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
(* Program Definition Field_flip_right  A Ra RaEquiv otime oplus a b *)
(*         `{field : @Field A Ra RaEquiv otime oplus a b}  *)
(* : Field otime (flip oplus) a b.  *)
(* Solve Obligations using (  intros; destruct field; try typeclasses eauto ). *)

(* Program Instance Field_flip_left  A Ra RaEquiv otime oplus a b *)
(*         `{field : @Field A Ra RaEquiv otime oplus a b}  *)
(* : Field (flip otime) oplus a b.  *)
(* Solve Obligations using (  intros; destruct field; try typeclasses eauto ).    *)
(*Hint Extern 1 (Field _)=> apply @Field_flip_right : typeclass_instances. *)




(* Program Instance commutativeMonoid_monoid  `(CommutativeMonoid)  :  *)
(* Monoid op e. *)

(* Program Instance group_is_monoid  `(Group)  : Monoid op groupNeutral. *)

(* Program Instance commutativeRing_is_Ring  `(CommutativeRing)  :  Ring  oplus otimes ep et. *)

(* Section semiRingNat. *)

Require Import Arith.

(**  0 is neutral for addition in nat *)
Program Instance plus_neutral : Neutral plus 0.
Next Obligation.
  constructor; auto.
Qed.
Next Obligation.
  constructor; auto.
Qed.

(**  addition in nat is commutative *)
Program Instance commutative_plus :  Commutative plus.
Next Obligation.
  auto with arith.
Qed.

(**  addition in nat is associative *)
Program Instance associative_plus :  Associative plus.
Next Obligation.
  auto with arith.
Qed.

(**  nat with addition is a commutative monoid *)
Program Instance commutativeMonoid_plus : CommutativeMonoid plus 0.
Next Obligation.
  constructor;typeclasses eauto.
Qed.

(**  multiplication in nat is associative *)
Program Instance associative_mult : Associative mult.
Next Obligation.
  auto with arith.
Qed.

(**  1 is neutral for multiplication in nat *)
Program Instance neutral_mult : Neutral mult 1.
Next Obligation.
  constructor; auto with arith.
Qed.

(**  multiplication in nat is associative *)
Program Instance commutative_mult : Commutative mult.
Next Obligation.
  auto with arith.
Qed.
Next Obligation.
  auto with arith.
  Admitted.
  
(**  nat with multiplication is a Commutative Monoid *)
Program Instance commutativeMonoid_mult : CommutativeMonoid mult 1.
Next Obligation.
  constructor; typeclasses eauto.
Qed.


(**  multiplication is distributive over addition in nat *)
Program Instance distributive_mult_plus : Distributivity mult plus.
Next Obligation.
  auto with arith.
Admitted.
Next Obligation.
  repeat rewrite (commutative (op:=mult) x).
  auto with arith.
Qed.

(**  nat with multiplication and addition is a SemiRing *)
Program Instance SemiRing_nat : SemiRing plus mult 0 1.

(* End semiRingNat. *)



(** *Z is a ring*)
(* Section anneauZ. *)

Require Import ZArith.
Open Scope Z_scope.

(**  0 is neutral for addition in Z *)
Program Instance Zplus_neutral : Neutral (eqA:=eq) Zplus 0.
Next Obligation.
constructor;auto with zarith.
Qed.
Next Obligation.
constructor;auto with zarith.
Qed.

(**  addition in Z is commutative *)
Program Instance Zplus_commutative :  Commutative (eqA:=eq) Zplus.
Next Obligation.
intros;auto with zarith.
Qed.

(**  addition in Z is associative *)
Program Instance Zplus_associative :  Associative (eqA:=eq) Zplus.
Next Obligation.
intros;auto with zarith.
Qed.

(**  Z with addition is a group *)
Program Instance group_Zplus : Group (eqA:=eq) Zplus 0.
Next Obligation.
Admitted.

(* Solve Obligations  using (typeclasses eauto || intro x;exists (-x); auto with zarith ). *)

(**  Z with addition is a commutative group *)
Program Instance commutativeGroup_Zplus : CommutativeGroup (eqA:=eq) Zplus 0.
(* Solve Obligations  using (typeclasses eauto). (*  *) *)

(**  multiplication in Z is associative *)
Program Instance associative_zmult : Associative (eqA:=eq) Zmult.
Next Obligation.
auto with zarith.
Qed.
(**  1 is neutral for multiplication in Z *)
Program Instance neutral_zmult : Neutral (eqA:=eq) Zmult 1.
Next Obligation.
constructor;auto with zarith.
Qed.
Next Obligation.
constructor;auto with zarith.
Qed.


(**  Z with multiplication is a Monoid *)
Program Instance monoid_zmult : Monoid (eqA:=eq) Zmult 1.
(* Solve Obligations  using (typeclasses eauto). *)

(**  multiplication is distributive over addition in Z *)
Program Instance distributive_zmult_zplus : Distributivity (eqA:=eq) Zmult Zplus.
Next Obligation.
auto with zarith.
Qed.
Next Obligation.
auto with zarith.
Qed.

(**  Z with multiplication and addition is a Ring *)
Program Instance Ring_Z : Ring (eqA:=eq) Zplus Zmult 0 1.
(* Solve Obligations  using (typeclasses eauto). *)
Close Scope Z_scope.
(* End anneauZ. *)

(* Section semiAnneauBool. *)
Require Import Bool.
Open Scope bool_scope.

Program Instance orb_neutral : Neutral orb false. 
Next Obligation.
constructor; auto with bool.
Qed.
Next Obligation.
constructor; auto with bool.
Qed.

Program Instance orb_commutative :  Commutative orb.
Next Obligation.
auto with bool.
Qed.

Program Instance orb_associative :  Associative  orb.
Next Obligation.
auto with bool.
Qed.

Program Instance commutative_monoid_orb : CommutativeMonoid orb false.
Next Obligation.
constructor; typeclasses eauto.
Qed.

Program Instance andb_neutral : Neutral andb true.
Next Obligation.
constructor; auto.
Qed.
Next Obligation.
  constructor;
  unfold andb; intros; case a; reflexivity.
Qed.


Program Instance andb_commutative :  Commutative andb.
Next Obligation.
auto with bool.
Qed.


Program Instance andb_associative :  Associative  andb.
Next Obligation.
auto with bool.
Qed.

Program Instance commutative_monoid_andb : CommutativeMonoid andb true.
Next Obligation.
constructor; typeclasses eauto.
Qed.

Program Instance distributive_andb_orb : Distributivity andb orb.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
(* Solve Obligations  using (intros x y z; case x; case y ;  case z ; unfold orb; reflexivity). *)

Program Instance distributive_orb_andb : Distributivity orb andb.

Next Obligation.
Admitted.
Next Obligation.
Admitted.
(* Solve Obligations  using (intros x y z; case x; case y ;  case z ; auto with bool). *)

Program Instance SemiRing_bool : SemiRing andb orb true false.
Next Obligation.
Admitted.
(* Solve Obligations  using (typeclasses eauto || intro a; case a; split; auto). *)

Close Scope bool_scope.
(* End semiAnneauBool. *)

Module semiAnneauProp. 
  
  Program Instance or_neutral : Neutral or False.
  Next Obligation.
Admitted.
Next Obligation.
Admitted.
  (* Solve Obligations  using (constructor; tauto). *)
  
  Program Instance or_commutative :  Commutative or.
  Next Obligation.
Admitted.
  (* Solve Obligations  using (tauto). *)

  Program Instance or_associative :  Associative  or.
  Next Obligation.
Admitted.
  (* Solve Obligations  using (tauto). *)

  Program Instance commutative_monoid_or : CommutativeMonoid or False.
  Next Obligation.
Admitted.
  (* Solve Obligations  using (constructor; typeclasses eauto). *)
  (* Solve Obligations  using (typeclasses eauto). *)

  Program Instance and_neutral : Neutral and True.
  Next Obligation.
Admitted.
Next Obligation.
Admitted.
  (* Solve Obligations  using (constructor;tauto). *)

  Program Instance and_commutative :  Commutative and.
  Next Obligation.
  Admitted.
  (* Solve Obligations  using (tauto). *)

  Program Instance and_associative :  Associative  and.
  Next Obligation.
Admitted.
  (* Solve Obligations  using (tauto). *)

  Program Instance commutative_monoid_and : CommutativeMonoid and True.
  Next Obligation.
Admitted.
  (* Solve Obligations  using (constructor; typeclasses eauto). *)


  Program Instance distributive_and_or : Distributivity and or.
  Next Obligation.
Admitted.
Next Obligation.
Admitted.
  (* Solve Obligations  using (tauto).  *)

  Program Instance distributive_or_and : Distributivity or and.
  Next Obligation.
Admitted.
Next Obligation.
Admitted.
  (* Solve Obligations  using (tauto).  *)

  Program Instance SemiRing_prop : SemiRing and or True False.
  Next Obligation.
  Admitted.
  (* Solve Obligations  using (typeclasses eauto || tauto). *)

End semiAnneauProp.


(* Section FieldQ. *)
Require Import QArith. 
Open Scope Q_scope.

Program Instance Q_neutral : Neutral (eqA:=Qeq) Qplus 0.
Next Obligation.
  constructor; apply Qplus_0_l.
Qed.
Next Obligation.
  constructor; apply Qplus_0_r.
Qed.

Program Instance Qplus_commutative :  Commutative  (eqA:=Qeq) Qplus.
Next Obligation.
  apply Qplus_comm.
Qed.

Program Instance Qplus_associative :  Associative  Qplus.
Next Obligation.
Admitted.
(* Solve Obligations  using (intros;symmetry;apply Qplus_assoc). *)

Program Instance group_Qplus : Group Qplus 0. 
Next Obligation.
  exists (-x). 
  split.
  - apply (Qplus_opp_r x).
  - rewrite commutative. apply (Qplus_opp_r x).
Qed.

Program Instance commutativeGroup_Qplus : CommutativeGroup Qplus 0.
(* Solve Obligations  using (typeclasses eauto || idtac). *)

Program Instance Qmult_neutral : Neutral Qmult 1.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
(* Solve Obligations  using (constructor ; (apply Qmult_1_r||apply Qmult_1_l)). *)

Program Instance Qmult_commutative :  Commutative Qmult.
Next Obligation.
Admitted.
(* Solve Obligations  using (apply Qmult_comm). *)

Program Instance Qmult_associative :  Associative  Qmult.
Next Obligation.
Admitted.
(* Solve Obligations  using (symmetry; apply Qmult_assoc). *)

Program Instance multiplicativeGroup_Qmult : MultiplicativeGroup Qmult 1 0.
Next Obligation.
Admitted.
(* Solve Obligations  using (typeclasses eauto|| idtac). *)
(* Next Obligation.
  exists (/x).
  apply Qmult_inv_r.
Qed. *)

(* Program Instance commutative_group_Qmult : CommutativeGroup Qmult 1. *)
(* Solve Obligations  using (typeclasses eauto|| idtac). *)
(* Next Obligation. *)


Program Instance distributive_Qmult_Qplus : Distributivity Qmult Qplus.
Next Obligation.
  apply Qmult_plus_distr_r.
Qed.
Next Obligation.
  apply Qmult_plus_distr_l.
Qed.


Program Instance Field_bool : Field Qplus Qmult 0 1.

(* Solve Obligations  using (typeclasses eauto || intro a; case a; split; auto). *)
Close Scope Q_scope.

(* End FieldQ. *)

(* (* MAX *) *)

(* Program Instance max_neutral : Neutral max  0. *)
(* Solve  Obligations using  (constructor;kintro b; apply max_comm; unfold max; simpl; reflexivity). *)

(* Program Instance max_commutative :  Commutative  max. *)
(* Solve Obligations  using (intros; apply max_comm). *)

(* Program Instance max_associative :  Associative  max. *)
(* Solve Obligations  using (intros; symmetry; apply max_assoc). *)


(* Program Instance plus_neutral : Neutral plus  0. *)
(* (* Solve Obligations  using (constructor;auto with arith). *) *)

(* Program Instance plus_commutative :  Commutative plus. *)
(* Solve Obligations  using (intros;auto with arith). *)

(* Program Instance plus_associative :  Associative  plus. *)
(* Solve Obligations  using (intros;auto with arith). *)

(* Program Instance distrib_max_plus : Distributivity  plus max. *)
(* Next Obligation. *)
(*    induction x;  induction y; induction z; simpl in *; (reflexivity || auto with arith). *)
(* Qed. *)



(* Program Instance  commutativeMonoid_max_0: CommutativeMonoid max 0. *)
(* Solve Obligations using (typeclasses eauto). *)

(* Program Instance  commutativeMonoid_sum_0: CommutativeMonoid plus 0. *)
(* Solve Obligations using (typeclasses eauto). *)

(* Program Instance semiRing_max_plus: SemiRing max plus 0 0. *)
(* Solve Obligations using (typeclasses eauto ||idtac). *)
(* Next Obligation.  *)
(* split. *)