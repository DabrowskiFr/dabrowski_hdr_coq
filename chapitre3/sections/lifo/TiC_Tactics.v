Tactic Notation "have" constr(Hyp) "as" ident(Name) :=
  match goal with
    | [ H : Hyp |- _ ] =>
      let tmp := fresh Name "__" in
      let ToClear := H in
      assert Hyp as tmp by apply ToClear; clear ToClear;
      assert Hyp as Name by apply tmp; clear tmp
  end.

Tactic Notation "have" constr(H) :=
  let Name := fresh in 
  assert H as Name by assumption;
    clear Name.

Tactic Notation "introduce" constr(H) :=
  match goal with
    | |- forall _:H, _ => intro
  end.

Tactic Notation "introduce" constr(H) "as" ident(Name):=
  match goal with
    | |- forall _:H, _ => intro Name
  end.

Tactic Notation "hi" constr(H) :=
  first [ have H | introduce H ].

Tactic Notation "hi" constr(H) "as" ident(Name):=
  first [ have H as Name | introduce H as Name].

Tactic Notation "assuming" constr(H0) tactic(t)  :=
  hi H0; t.

Tactic Notation "assuming" constr(H0) "as" ident(N0) tactic(t) :=
  hi H0 as N0; t.

Tactic Notation "prove" constr(H) :=
  assert H ; [ | auto ].

Tactic Notation "prove" "goal" := idtac.

Tactic Notation "conclude" "by" tactic(t) :=
  solve [ t; auto; eauto; intuition ].

Tactic Notation "witness" ident(x) "from" hyp(H) :=
  destruct H as [x H].

Tactic Notation "witness" ident(x) ident(x') "from" hyp(H) :=
  destruct H as [x [x' H]].

Tactic Notation "witness" ident(x) ident(x') ident(x'') "from" hyp(H) :=
  destruct H as [x [x' [x'' H]]].