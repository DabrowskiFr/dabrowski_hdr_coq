Tactic Notation  "copy" hyp(h) "as" ident(h1) :=
    let t:= type of h  in 
      assert (h1 :t ) by assumption.

Tactic Notation  "copy" hyp(h) "into" ident(h1) :=
  let H := fresh h1 in 
    let t:= type of h  in 
      assert (H :t ) by assumption.

Tactic Notation  "duplicate" ident(h) :=
  copy h into h .

  Tactic Notation  "copy_eq" hyp(h) "into" ident(h1) :=
  let H := fresh h1 in 
    let H_eq := fresh "copy" in 
        pose (H :=h ) ;
          assert (H_eq :  H = h) by reflexivity;
            generalize H H_eq; clear H H_eq; intros H H_eq.
  
  Tactic Notation  "duplicate_eq" ident(h) :=
  copy_eq h into h .


Goal forall H:nat, nat.
  intro.
  duplicate H.
  copy H as H1.
  copy H into H1.
  duplicate_eq H.
  auto.
Qed.  

Ltac simplif := 
let if_left:=fresh "if_left" in let if_right:=fresh "if_right" in
  match goal with 
    [|- context ctx [if ?cond then ?brtrue else ?brfalse ] ]=>  destruct cond as [if_left | if_right]
    | [H : context ctx [if ?cond then ?brtrue else ?brfalse ]|-_] => destruct cond as [if_left | if_right]
    | _ => fail "no if"
  end
  ;[ 
    try (contradict if_left;reflexivity); try (destruct if_left;reflexivity)
    | try (contradict if_right;reflexivity);try (destruct if_right;reflexivity)].

Require Import String.
(** memorisation mecanism : enable kind of side effects  in Ltac  *)
Inductive memo (s: String.string) : Prop :=
  mem  :  memo s
.
(** memorizing a string  *)
Tactic Notation "memorize" constr(s) := 
  pose ( mem _ : memo s).

(** locking on a given string, if a lock is already there, fail, else put the lock  *)
Tactic Notation "lock" constr(s) :=
   lazymatch goal with 
     mem : memo s |- _ =>   fail 
 | _ => memorize s
end.

Tactic Notation "lockd" constr(s) :=
   lazymatch goal with 
     mem : memo s |- _ => idtac s; idtac "locked";  fail 
 | _ => memorize s
end.

(** unlocking on a given string, if a lock is already there, remove it, else do nothing  *)
Tactic Notation "unlock" constr(s) :=
   lazymatch goal with 
     mem : memo s |- _ => clear mem
 | _ => idtac
end.

Ltac to_leibniz R := 
  match goal with |- context [R ?l ?r] => 
                  let leib := fresh "leib" in assert (leib : l=r);[|rewrite leib; try reflexivity]
  end.


(* *)



(** Tactic for recursive elimination of existantial quantifier in hypothesis*)
Tactic Notation "elim_ex" constr(e):=
  repeat (
    match (type of e) with 
      | exists x,_ => 
        elim e;clear e; let H:=fresh "x"  in intros H e
      | _ => fail
    end
    ).
(** Tactic for recursive elimination of existantial quantifier in hypothesis limited to depth [n]*)
Tactic Notation "elim_ex" constr(e) integer(n):=
  do n (
    match (type of e) with 
      | exists x,_ => 
        elim e;clear e; let H:=fresh in intros H e
      | _ => fail
    end
    ).

(** Admiting with a warning message  *)
Ltac myadmit s1 s2 :=    
  match goal with 
    [|- ?G ] => 
  idtac "Warning :  admit in file" s1".v, lemma" s2 "goal :" G
  end ; admit.
