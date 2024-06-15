Require Import String List.


(** * Expressions *)

Inductive binop : Set := Add | Sub | Mult.

Inductive comp : Set := Eq | Lt.

Inductive expr : Set :=
  Var : nat -> expr
| Const : nat -> expr
| Binop : binop -> expr -> expr -> expr
| NProcs : expr
| Pid : expr.

Inductive bexpr : Set :=
  TT
| FF
| Comp : comp -> expr -> expr -> bexpr
| Or : bexpr -> bexpr -> bexpr
| And : bexpr -> bexpr -> bexpr
| Not : bexpr -> bexpr.

(** * Statements *)

Inductive stmt :=
  Skip : stmt
| Assign : nat -> expr -> stmt
| Seq : stmt -> stmt -> stmt
| If : bexpr -> stmt -> stmt -> stmt
| While : bexpr -> stmt -> stmt
| Sync : stmt.

(** * Notations *)

Notation "'SKIP'" := Skip : stmt_scope.
Notation "x '::=' a" := (Assign x a) (at level 60) : stmt_scope.
Notation "'SYNC'" := Sync : stmt_scope.
Notation "s1 ;; s2" :=
  (Seq s1 s2) (at level 80, right associativity) : stmt_scope.
Notation "'WHILE' b 'DO' s 'END'" :=
  (While b s) (at level 80, right associativity) : stmt_scope.
Notation "'IFB' b 'THEN' s1 'ELSE' s2 'FI'" :=
  (If b s1 s2) (at level 80, right associativity) : stmt_scope.
Infix "'OR'" := Or (at level 70).
Infix "AND" := Or (at level 70).
Notation "'Not'" := Not.