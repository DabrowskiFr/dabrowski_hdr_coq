Require Import List. Import ListNotations.
Require Import ZArith.
Require Import sections.lifo.Prelude.
Require Import Heap.

Module Type T 
       (Import Ad : DecidableInfiniteSet)
       (Import Sz : MiniDecidableSet)
       (Import Ty : Type_.TYPE Ad)
       (Import Va : Value.TYPE Ad Ty)
       (Import He : Heap.T_VALUE Ad Ty Va).

  Inductive List (heap : He.t) : Ad.t -> list (Ad.t * Z * Ad.t) -> Prop := 
  | List_nil : List heap He.null []
  | List_cons : forall l Hl H0 H1 H2 xs la na lxs, 
                  He.get heap l Hl 0%nat H0 = Value Location la ->
                  He.get heap l Hl 1%nat H1 = Value Number na ->
                  He.get heap l Hl 2%nat H2 = Value Location lxs ->
                  List heap lxs xs ->
                  List heap l ((la,na,lxs)::xs).

  Lemma List_inj : 
    forall heap l1 l2 root, 
      List heap root l1 ->
      List heap root l2 ->
      l1 = l2.
  Proof.
    intros heap l1; induction l1; intros l2 root Hl1 Hl2.
    - inversion Hl1; inversion Hl2; subst.
      + trivial.
      + exfalso. now apply (null_not_in_domain heap).
    - inversion Hl1; inversion Hl2; subst.
      + exfalso. now apply (null_not_in_domain heap).
      + assert(Hl0 = Hl3) by (apply in_domain_inj); subst.
        assert(H0 = H9) by (apply is_valid_inj); subst.
        assert(H1 = H10) by (apply is_valid_inj); subst.
        assert(H2 = H11) by (apply is_valid_inj); subst.
        assert(lxs = lxs0) by (rewrite H14 in H7; now apply ValueInj).
        repeat f_equal.
        rewrite H12 in H4. now apply ValueInj.
        rewrite H13 in H5. now apply ValueInj.
        trivial.
        rewrite H in *.        
        eapply IHl1; eassumption.
  Qed.
        
  Definition inDomain (heap : He.t) (a : Ad.t) : option (in_domain heap a).
  Proof.
    case_eq(in_domain_dec heap a); intros H _.
    - exact(Some H).
    - exact None.
  Defined.

  Lemma not_in_domain:
    forall heap root,
    ~ in_domain heap root <-> inDomain heap root = None.
  Proof.
    intros heap root. unfold inDomain.
    split.
    - intro H. pattern(in_domain_dec heap root).
      case_eq(in_domain_dec heap root); intros Hindom _.
      + contradiction.
      + trivial.
    - intro H. case_eq(in_domain_dec heap root); intros Hindom H'.
      + rewrite H' in H. discriminate.
      + trivial.
  Qed.


  Definition isValid (heap : He.t) (a : Ad.t) Ha (o:nat) : 
    option (He.is_valid o (size_of heap a Ha)).
  Proof.
    case_eq(He.is_valid_dec o (size_of heap a Ha)); intros H _.
    - exact(Some H).
    - exact None.
  Defined.

  Lemma not_is_valid:
    forall (heap : He.t) (a : Ad.t) Ha (o:nat),
      ~ is_valid o (size_of heap a Ha) <-> isValid heap a Ha o = None.
  Proof.
    intros heap a Ha o. unfold isValid in *; split; intro H.
    - pattern(is_valid_dec o (size_of heap a Ha)).
      case_eq(is_valid_dec o (size_of heap a Ha)); intros Hv _.
      + contradiction.
      + trivial.
    - case_eq(is_valid_dec o (size_of heap a Ha)); intros Hv H'.
      + rewrite H' in H. discriminate.
      + trivial.
  Qed.
    

  Open Scope monad_scope.

  Fixpoint IsList (heap : He.t) (root: Ad.t) (li : list (Ad.t * Z * Ad.t)) : bool :=
    match li with 
      | [] => if Ad.eq_dec root He.null then true else false
      | (la,na,lxs)::xs => 
        let result := 
            do Hroot <- inDomain heap root;
            do H0 <- isValid heap root Hroot 0%nat;
            do H1 <- isValid heap root Hroot 1%nat;
            do H2 <- isValid heap root Hroot 2%nat;
            do la' <- getLocation(He.get heap root Hroot 0%nat H0);
            do na' <- getNumber(He.get heap root Hroot 1%nat H1);
            do lxs' <- getLocation(He.get heap root Hroot 2%nat H2);
            let checked_la := if Ad.eq_dec la la' then true else false in
            let checked_na := if Z.eq_dec na na' then true else false in
            let checked_lxs := if Ad.eq_dec lxs lxs' then true else false in
            Some (andb(andb(andb (IsList heap lxs xs) checked_la) 
                           checked_na) checked_lxs) in
        match result with Some b => b | None => false end
    end.

  Lemma ListIsList : 
    forall heap li root, List heap root li <-> IsList heap root li = true.
  Proof.
    intro heap; induction li; intro root.
    - split; intro H; simpl in *.
      + inversion H. destruct (Ad.eq_dec null null); intuition.
      + destruct(Ad.eq_dec root null) as [H'|H'].
        * subst. constructor.
        * discriminate.
    - split; intro H.
      + inversion H; simpl in *; subst.
        case_eq(inDomain heap root); [intros Hd HH0 | intro HH0]; simpl;
        try(apply not_in_domain in HH0; contradiction).
        assert(Hd = Hl0) by (apply in_domain_inj); subst.
        case_eq(isValid heap root Hl0 0); [intros Hv0 HH1 | intro HH1]; simpl;
        try(apply not_is_valid in HH1; contradiction).
        case_eq(isValid heap root Hl0 1); [intros Hv1 HH2 | intro HH2]; simpl;
        try(apply not_is_valid in HH2; contradiction).
        case_eq(isValid heap root Hl0 2); [intros Hv2 HH3 | intro HH3]; simpl;
        try(apply not_is_valid in HH3; contradiction).
        assert(H0 = Hv0) by apply is_valid_inj; subst.
        assert(H1 = Hv1) by apply is_valid_inj; subst.
        assert(H2 = Hv2) by apply is_valid_inj; subst.
        unfold getLocation, getNumber, getLocation.
        rewrite H5, H6, H8; simpl.
        destruct(IHli lxs) as [ Hil _ ]. rewrite (Hil H9); simpl.
        destruct(Ad.eq_dec la la) as [Heq | Heq]; 
          try solve [contradict Heq; auto]; clear Heq.
        destruct(Ad.eq_dec lxs lxs) as [ Heq | Heq]; 
          try solve [contradict Heq; auto]; clear Heq.
        destruct(Z.eq_dec na na) as [Heq | Heq]; try solve [contradict Heq; auto].
        trivial.
      + simpl in H. destruct a as [[la na] lxs]. 
        case_eq(inDomain heap root); [intros Hd H0 | intro H0]; 
        rewrite H0 in H; simpl in H; try discriminate.
        case_eq(isValid heap root Hd 0); [intros Hv0 H1 | intro H1]; 
        rewrite H1 in H; simpl in H; try discriminate.
        case_eq(isValid heap root Hd 1); [intros Hv1 H2 | intro H2]; 
        rewrite H2 in H; simpl in H; try discriminate.
        case_eq(isValid heap root Hd 2); [intros Hv2 H3 | intro H3]; 
        rewrite H3 in H; simpl in H; try discriminate.
        case_eq(getLocation (get heap root Hd 0 Hv0)); [intros la' H4 | intro H4]; 
        rewrite H4 in H; simpl in H; try discriminate.
        case_eq(getNumber (get heap root Hd 1 Hv1)); [intros na' H5 | intro H5]; 
        rewrite H5 in H; simpl in H; try discriminate.
        case_eq(getLocation (get heap root Hd 2 Hv2)); [intros lxs' H6 | intro H6]; 
        rewrite H6 in H; simpl in H; try discriminate.
        case_eq(IsList heap lxs li); intros Hil; 
        rewrite Hil in H; simpl in H; try discriminate.
        destruct(Ad.eq_dec la la'); simpl in H; try discriminate.
        destruct(Z.eq_dec na na'); simpl in H; try discriminate.
        destruct(Ad.eq_dec lxs lxs'); simpl in H; try discriminate.
        unfold getLocation, getNumber, getLocation in *.
        case_eq(get heap root Hd 0 Hv0); intros; rewrite H7 in H4;
        destruct ty; simpl in *; try discriminate.
        case_eq(get heap root Hd 1 Hv1); intros; rewrite H8 in H5;
        destruct ty; simpl in *; try discriminate.
        case_eq(get heap root Hd 2 Hv2); intros; rewrite H9 in H6;
        destruct ty; simpl in *; try discriminate;
        inversion H4; inversion H5; inversion H6; subst.
        econstructor; eauto.
        eapply IHli; eauto.
  Qed.

  Definition trd {A B C} : A*B*C -> C := 
    fun p => match p with (a,b,c) => c end.

  Definition fst3 {A B C} : A*B*C -> A := 
    fun p => match p with (a,b,c) => a end.

  Definition nodeList (heap : He.t) (root : Ad.t) (li : list (Ad.t * Z * Ad.t)) :
    option(list Ad.t) :=
    if IsList heap root li 
    then Some (root::(List.map trd li))
    else None.

  Definition infoList (heap : He.t) (root : Ad.t) (li : list (Ad.t * Z * Ad.t)) :
    option(list Ad.t) :=
    if IsList heap root li 
    then Some (List.map fst3 li)
    else None.

  Lemma nodeListIsList :
    forall heap root li l,
      nodeList heap root li = Some l ->
      IsList heap root li = true.
  Proof.
    intros heap root li l H.
    unfold nodeList in *.
    destruct(IsList heap root li).
    - trivial.
    - discriminate.
  Qed.

  Lemma nodeListList :
    forall heap root li l,
      nodeList heap root li = Some l ->
      List heap root li.
  Proof. 
    intros. 
    apply ListIsList. 
    eapply nodeListIsList. 
    eassumption. 
  Qed.
  
  Lemma nodeList_inj1:
    forall heap root li li' l l', 
      nodeList heap root li = Some l ->
      nodeList heap root li' = Some l' ->
      li = li'.
  Proof.
    intros heap root li li' l l' H H0.
    apply nodeListList in H. 
    apply nodeListList in H0. 
    eapply List_inj; eauto.
  Qed.

  Lemma nodeList_inj2:
    forall heap root li li' l l', 
      nodeList heap root li = Some l ->
      nodeList heap root li' = Some l' ->
      l = l'.
  Proof.
    intros heap root li li' l l' H H0.
    assert(li = li') by (eapply nodeList_inj1; eauto); subst.
    rewrite H0 in H.
    inversion H.
    trivial.
  Qed.


  Lemma nodeListNull1:
    forall heap root l,
    nodeList heap root [] == l ->
    root = null.
  Proof.
    intros heap root l H.
    apply nodeListList in H.
    inversion H.
    trivial.
  Qed.

  Lemma nodeListNull2:
    forall heap root l,
    nodeList heap root [] == l ->
    l = [null].
  Proof.
    intros heap root l H.
    unfold nodeList in H; simpl in *.
    destruct(Ad.eq_dec root null); subst.
    - inversion H. trivial.
    - discriminate.
  Qed.

  Lemma nodeListNotNil:
    forall heap li l root,
      nodeList heap root li == l ->
      exists xs, l = root::xs.
  Proof.
    intros heap li l root H.
    unfold nodeList in *; simpl in H.
    case_eq(IsList heap root li); intros H'; rewrite H' in H; simpl in H;
    try discriminate.
    inversion H.
    destruct l; inversion H1; subst.
    eauto.
  Qed.

  Lemma nodeListCons : 
    forall heap li l la na lxs root,
      nodeList heap root ((la, na, lxs) :: li) == (root::l) ->
      nodeList heap lxs li == l.
  Proof.
    intros heap li l la na lxs root H.
    unfold nodeList in *; simpl in H.
    case_eq(inDomain heap root); [intros Hd H0 | intro H0]; 
    rewrite H0 in H; simpl in H; try discriminate.
    case_eq(isValid heap root Hd 0); [intros Hv0 H1 | intro H1]; 
    rewrite H1 in H; simpl in H; try discriminate.
    case_eq(isValid heap root Hd 1); [intros Hv1 H2 | intro H2]; 
    rewrite H2 in H; simpl in H; try discriminate.
    case_eq(isValid heap root Hd 2); [intros Hv2 H3 | intro H3]; 
    rewrite H3 in H; simpl in H; try discriminate.
    case_eq(getLocation (get heap root Hd 0 Hv0)); [intros la' H4 | intro H4]; 
    rewrite H4 in H; simpl in H; try discriminate.
    case_eq(getNumber (get heap root Hd 1 Hv1)); [intros na' H5 | intro H5]; 
    rewrite H5 in H; simpl in H; try discriminate.
    case_eq(getLocation (get heap root Hd 2 Hv2)); [intros lxs' H6 | intro H6]; 
    rewrite H6 in H; simpl in H; try discriminate.
    case_eq(IsList heap lxs li); intros Hil; trivial;
    rewrite Hil in H; simpl in H; try discriminate.
    destruct(Ad.eq_dec la la'); simpl in H; try discriminate.
    destruct(Z.eq_dec na na'); simpl in H; try discriminate.
    destruct(Ad.eq_dec lxs lxs'); simpl in H; try discriminate.
    inversion H. auto.
  Qed.

  Lemma nodeListMap : 
    forall heap li root l, 
      nodeList heap root li == l ->
      l = root::(List.map trd li).
  Proof.
    induction li; intros root l H.
    - simpl. 
      assert(root = null) by (eapply nodeListNull1; eauto). subst.
      eapply nodeListNull2. eauto.
    - set(H'':= nodeListNotNil _ _ _ _ H); destruct H'' as [ l' Hl']; simpl in *.
      destruct l as [ | a'' l'']; simpl; inversion Hl'; subst.
      f_equal.
      apply IHli.
      destruct a as [[la na] lxs].
      eapply nodeListCons.
      eauto.
  Qed.

  Lemma nodeListAppList : 
    forall heap li root l root' l', 
      nodeList heap root li == (l ++ root'::l') ->
      exists l'', List heap root' l'' /\ map trd l'' = l'.
  Proof.
    induction li; intros root l root' l' H.
    - simpl. 
      assert(root = null) by (eapply nodeListNull1; eauto). subst.
      eapply nodeListNull2 in H. 
      exists [].
      destruct l as [ | x xs ]; simpl in *; inversion H; subst.
      + split; auto. constructor.
      + destruct xs; simpl in *; inversion H2.
    - destruct a as [[la na] lxs]. 
      assert(nodeList heap root ((la, na, lxs) :: li) == (l ++ root' :: l')) 
        as Hbackup by auto.
      assert(nodeList heap root ((la, na, lxs) :: li) == (l ++ root' :: l')) 
        as Hbackup' by auto.
      assert(nodeList heap root ((la, na, lxs) :: li) == (l ++ root' :: l')) 
        as Hbackup'' by auto.
      unfold nodeList in H; simpl in H.
      case_eq(inDomain heap root); [intros Hd H0 | intro H0]; 
      rewrite H0 in H; simpl in H; try discriminate.
      case_eq(isValid heap root Hd 0); [intros Hv0 H1 | intro H1]; 
      rewrite H1 in H; simpl in H; try discriminate.
      case_eq(isValid heap root Hd 1); [intros Hv1 H2 | intro H2]; 
      rewrite H2 in H; simpl in H; try discriminate.
      case_eq(isValid heap root Hd 2); [intros Hv2 H3 | intro H3]; 
      rewrite H3 in H; simpl in H; try discriminate.
      case_eq(getLocation (get heap root Hd 0 Hv0)); [intros la' H4 | intro H4]; 
      rewrite H4 in H; simpl in H; try discriminate.
      case_eq(getNumber (get heap root Hd 1 Hv1)); [intros na' H5 | intro H5]; 
      rewrite H5 in H; simpl in H; try discriminate.
      case_eq(getLocation (get heap root Hd 2 Hv2)); [intros lxs' H6 | intro H6]; 
      rewrite H6 in H; simpl in H; try discriminate.
      case_eq(IsList heap lxs li); intros Hil; 
      rewrite Hil in H; simpl in H; try discriminate.
      destruct(Ad.eq_dec la la'); simpl in H; try discriminate.
      destruct(Z.eq_dec na na'); simpl in H; try discriminate.
      destruct(Ad.eq_dec lxs lxs'); simpl in H; try discriminate.
      unfold getLocation, getNumber in *.
      case_eq(get heap root Hd 0 Hv0); intros; rewrite H7 in H4;
      destruct ty; simpl in *; try discriminate.
      case_eq(get heap root Hd 1 Hv1); intros; rewrite H8 in H5;
      destruct ty; simpl in *; try discriminate.
      case_eq(get heap root Hd 2 Hv2); intros; rewrite H9 in H6;
      destruct ty; simpl in *; try discriminate;
      inversion H4; inversion H5; inversion H6; subst.
      destruct l as [ | x xs ]; simpl in H; inversion H; subst; simpl in *.
      + assert(exists l'', List heap lxs' l'' /\ map trd l'' = map trd li) as Hl''.
        {
          eapply (IHli lxs' []).
          eapply nodeListCons.
          apply Hbackup'.
        }
        destruct Hl'' as [l'' [Hl''1 Hl''2]]; subst.
        exists((la', na', lxs') :: l'').
        split. eapply List_cons; eauto.  simpl; now f_equal.
      + apply nodeListNotNil in Hbackup. destruct Hbackup as [l'' Hl''];
                                         inversion Hl'' ; subst. clear Hl''.
        
        apply nodeListMap in Hbackup'. simpl in *. inversion Hbackup'. subst.
        apply nodeListCons in Hbackup''.
        apply (IHli lxs' xs root' l' Hbackup'').
  Qed.

  Lemma noDupNodeList : 
    forall heap li root l, 
      nodeList heap root li = Some l ->
      NoDup l.
  Proof.
    intros heap. induction li; intros root l Hl.
    - assert(List heap root []) as H by (eapply nodeListList;eauto).
      inversion H; subst; unfold nodeList in *; simpl in *.
      destruct(Ad.eq_dec null null).
      + inversion Hl; subst. constructor. 
        * intro. auto.
        * constructor.
      + discriminate.
    - destruct a as [[la na] lxs]. 
      set(H'':= nodeListNotNil _ _ _ _ Hl); destruct H'' as [ l' Hl'].
      destruct l as [ | x xs ].
      + inversion Hl'.
      + constructor.
        * intro H.
          assert(exists l1 l2 : list Ad.t, xs = l1 ++ x :: l2) 
            as H' by now apply in_split.
          destruct H' as [l1 [l2 H']]. subst.
          set(H'':=Hl).
          rewrite app_comm_cons in H''; 
            apply nodeListAppList in H''.
            destruct H'' as [l'' [Hl''1 Hl''2]].
          set(H'':= Hl).
          apply nodeListMap in H''; inversion H''; subst.
          apply nodeListList in Hl.
          assert(l'' = (la,na,lxs)::li) by (eapply List_inj; eauto); subst.
          simpl in *.
          assert(length ( l1 ++ root :: lxs :: map trd li) = 
                 length (lxs :: map trd li)) as Hlen by (rewrite H2; trivial).
          admit.
                 (* autorewrite with length in Hlen; simpl in Hlen. *)
          (* revert Hlen. clear. intro Hlen. *)
          (* induction li; simpl in *; omega. *)
        * inversion Hl'; subst;  apply nodeListCons in Hl.
          eapply IHli; eauto.
  Admitted.

End T.
