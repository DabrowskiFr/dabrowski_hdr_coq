Require Import List Program ZArith. 
Import ListNotations.
Require Import sections.lifo.Prelude sections.lifo.TiC_Tactics.
Require Import sections.lifo.Last.
Require Import Heap.

Generalizable All Variables.

Module Type StateWithHeap
       (Import Ad : DecidableInfiniteSet)
       (Import Sz : MiniDecidableSet)
       (Import He : Heap.T Ad Sz).

  Parameter t: Type.

  Parameter other : Type.

  Parameter split : t -> He.t * other.

  Parameter combine : He.t * other -> t.

  Axiom split_combine :
    forall (heap:He.t)(o:other), split (combine (heap,o)) = (heap, o).

  Axiom combine_split :
    forall (state:t), state = combine (split state).
  
End StateWithHeap. 

Definition last_error {A} := compose (hd_error (A:=A)) (rev (A:=A)).

Definition get_default {A B:Type}(proj:A->B)(v:option A)(default:B) :=
  match v with
    | None => default
    | Some x => proj x
  end.

Definition third {A B C:Type}(x:A*B*C) : C := snd x.

Definition first {A B C:Type}(x:A*B*C) : A :=
  let ( tmp , _ ) := x in fst tmp.

Lemma app_singleton:
  forall (A:Type)(x y:A)(l1 l2:list A),
    [x] = l1++y::l2 ->
    x = y /\ l1 = [] /\ l2 = [].
Proof.
  intros A x y l1 l2.
  assuming ([x] = l1++y::l2) as H prove (x = y /\ l1 = [] /\ l2 = []).
  {
    assert(In y [x]) as Hin by (rewrite H; apply in_app_iff; auto with *).
    assert(x = y) by (now inversion Hin).
    assert(l1 = []) 
      by (destruct l1; trivial; inversion H; destruct l1; discriminate).
    assert(l2 = []) by (subst; now inversion H).
    intuition.
  }
Qed.

Definition shift_left `(xs:list A) :=
  match xs with
    | [] => []
    | x::xs => xs++[x]
  end.

Definition shift_right `(xs:list A) :=
  List.rev(shift_left(List.rev xs)).

Lemma shift_right_last:
  forall `(xs:list A) x, shift_right (xs++[x]) = x::xs.
Proof.
  intros A xs x; unfold shift_right.
  rewrite rev_unit; simpl; rewrite rev_unit.
  now rewrite rev_involutive.
Qed.

Lemma shift_left_In:
  forall A (x:A) xs, In x xs <-> In x (shift_left xs).
Proof.
  intros A x. induction xs as [ | x' xs IH ].
  - intuition.
  - simpl; split; intro H.
    + destruct H; subst; auto with *.
    + apply in_app_iff in H; simpl in H.
      intuition.
Qed.

Lemma shift_right_In:
  forall A (x:A) xs, In x xs <-> In x (shift_right xs).
Proof.
  intros A x xs. unfold shift_right.
  transitivity (In x (shift_left (rev xs))).
  transitivity (In x (rev xs)).
  apply in_rev.
  apply shift_left_In.
      apply in_rev.
Qed.

Hint Unfold compose last_error : myunfold.

Module Type T 
       (Import Ad : DecidableInfiniteSet)
       (Import Sz : MiniDecidableSet)
       (Import He : Heap.T Ad Sz)
       (Import State : StateWithHeap Ad Sz He).

  (* At an address, a ``record'' contains : 
       - the pointer to the previous cell,
       - some values that constitutes the data,
       - the pointer to the next cell. *)
  
  Record CellDescription := mkCD
    {
      (* Obtaining pointers towards the previous cell and the next cell. *)
      o_prev : Sz.t;
      o_next : Sz.t;
      offsets_spec : o_prev <> o_next;
      (* Obtaining an address from values stored in the Heap *)
      to_address : value_t -> option Ad.t;
      of_address : Ad.t -> option value_t;
      (* ABOUT DATA contained in the list *)
      (* For a version that only checks the structure of cyclic double
         linked, it is not really necessary ... *)
      t : Type;
      is_valid : State.t -> t -> Prop; 
      data : State.t -> Ad.t -> option t;
      data_spec_1: forall heap other adr Hadr offset Hoffset value,
          offset = o_prev \/ offset = o_next ->
          data (combine (heap,other)) adr =
          data (combine ((set heap adr Hadr offset Hoffset value),other)) adr;
      data_spec_2: forall heap other adr Hadr adr' offset Hoffset value,
          adr <> adr' ->
          data (combine (heap,other)) adr' =
          data (combine ((set heap adr Hadr offset Hoffset value),other)) adr'
    }.


  Section Cell.

    Variable Cell : CellDescription.

    Definition addr (root:Ad.t)(lefts rights:list (Ad.t*Cell.(t)*Ad.t)) (e:(Ad.t*Cell.(t)*Ad.t)) :=
      match rev lefts with
        | [] => match rights with
                  | [] => root
                  | (prev,_,_)::_ => prev
                end
        | (_,_,next)::_ => next
      end.

    Definition addr_of_last_first_version (xs : list (Ad.t*Cell.(t)*Ad.t)) : Ad.t :=
      match rev xs with
        | [] => He.null
        | [(_,_,next)] => next
        | _::(_,_,next)::_ => next
      end.

    Fixpoint addr_of_last (xs : list (Ad.t*Cell.(t)*Ad.t)) : Ad.t :=
      match xs with
        | [] => He.null
        | [(_,_,next)] => next
        | (_,_,next)::[ _ ] => next
        | _::xs => addr_of_last xs
      end.

    Lemma addr_of_last_prop:
      forall xs p next last,
        addr_of_last (xs++[(p,next)]++[last]) = next.
    Proof.
      induction xs as [ | [ [prev' d'] next'] xs IH] ; intros [prev d] next last.
      - trivial.
      - simpl.
        case_eq( xs ++ [(prev, d, next); last]); [intro Heq | intros x xs' Heq].
        + symmetry in Heq. now apply app_cons_not_nil in Heq.
        + case_eq( xs' ); [intro Heq' | intros x' xs'' Heq'].
          * subst.
            assert(removelast [x] = removelast (xs++[(prev,d,next);last]) ) as Heq'
                by (now rewrite Heq).
            rewrite removelast_app in Heq' by (intro H; discriminate).
            simpl in Heq'. 
            now apply app_cons_not_nil in Heq'.
          * rewrite <- Heq', <- Heq.
            apply IH.
    Qed.
      
    
    Inductive CyclicDoubleTail :
      State.t->Ad.t -> Ad.t -> list (Ad.t * Cell.(t) *Ad.t) -> Prop :=
    | cdt_singleton :
        forall state heap other fop Hfop root prev Hprev Hnext d,
          (heap,other) = State.split state ->
          Cell.(to_address) (He.get heap fop Hfop Cell.(o_prev) Hprev) == prev ->
          Cell.(to_address) (He.get heap fop Hfop Cell.(o_next) Hnext) == root ->
          Cell.(data) state fop == d ->
          Cell.(is_valid) state d ->
          CyclicDoubleTail state root fop [(prev,d,root)]
    | cdt_app :
        forall state heap other root fop fop' Hfop' d prev Hprev Hnext xs ,
          (heap,other) = State.split state ->
          xs <> [] -> (* Dispensable *)
          CyclicDoubleTail state root fop xs ->
          lift first (hd_error xs) == fop'->
          Cell.(to_address) (He.get heap fop' Hfop' Cell.(o_prev) Hprev) == prev ->
          Cell.(to_address) (He.get heap fop' Hfop' Cell.(o_next) Hnext) == fop ->
          Cell.(data) state fop' == d ->
          Cell.(is_valid) state d ->
          CyclicDoubleTail state root fop' ((prev,d,fop)::xs).

    Lemma cyclicdoubletail_last:
      forall xs state root firstpointer default,
        CyclicDoubleTail state root firstpointer xs ->
        third (last xs default) = root.
    Proof.
      induction xs as [ | x xs IH]; intros state root firstpointer default H.
      - inversion H.
      - simpl; destruct xs as [ | x' xs].
        + inversion H; now simpl.
        + inversion H; subst.
          now apply (IH state root fop).
    Qed.
        
    Inductive CyclicDoubleLinked (state:State.t) :
      Ad.t -> list (Ad.t * Cell.(t) *Ad.t) -> Prop :=
    | cdl_nil : CyclicDoubleLinked state He.null []
    | cdl_cons:
        forall root xs,
          lift first (hd_error xs) == addr_of_last xs ->
          CyclicDoubleTail state root root xs ->
          CyclicDoubleLinked state root xs.

    Lemma linksPropertyPartial:
      forall state root fpointer xs,
        CyclicDoubleTail state root fpointer xs ->
        removelast(tl(shift_right (map third xs))) =
        tl(removelast(shift_left (map first xs))).
    Proof.
      intros state root fpointer xs H; induction H.
      - trivial.
      - destruct xs as [ | x xs _] using rev_ind.
        + simpl in *; trivial.
        + repeat rewrite app_comm_cons in *. simpl in *.
          repeat rewrite map_app in *. simpl in *.
          repeat rewrite app_comm_cons in *. 
          rewrite shift_right_last.
          rewrite shift_right_last in IHCyclicDoubleTail.
          simpl in IHCyclicDoubleTail.
          rewrite removelast_app
            by (simpl;intro H';discriminate).
          simpl in *.             rewrite app_nil_r in *.
          

          destruct xs as [ |x' xs].
          * trivial.
          * Opaque removelast. simpl in *. Transparent removelast.
            rewrite removelast_app in *
              by (simpl;intro H';discriminate).
            {
              destruct xs as [ | x'' xs _] using rev_ind.
              - simpl in *; inversion H1; subst.
                simpl in *. now inversion H12.
              - rewrite map_app in *.
                rewrite app_comm_cons in *.
                rewrite removelast_app in *
                  by (simpl;intro H';discriminate).
                simpl in *.
                destruct xs as [ |x''' xs].
                + simpl in *; inversion H1; subst; simpl in *.
                  inversion IHCyclicDoubleTail;
                    inversion H12; now subst.
                + simpl in *.
                  rewrite IHCyclicDoubleTail.
                  f_equal.
                  * inversion H1; inversion H12; now subst.
                  * auto with *.
            }
    Qed.
    
    Lemma linksProperty:
      forall state root xs,
        CyclicDoubleLinked state root xs ->
        shift_right (map third xs) = shift_left (map first xs).
    Proof.
      intros state root xs H. 
      destruct H as [ | root xs Hlink Hcycliclist].
      - trivial.
      - inversion Hcycliclist; subst.
        + simpl in *. now inversion Hlink.
        + inversion Hcycliclist; subst.
          * now contradict H0.
          * apply linksPropertyPartial in Hcycliclist.
            simpl in *.
            { destruct xs0 as [ | x [ | x' xs ] ].
              - now contradict H0.
              - simpl. replace [fop;third x] with ([fop]++[third x]) by trivial.
                rewrite shift_right_last.
                inversion Hlink; subst.
                simpl in *; inversion H13; subst; simpl in *.
                + now inversion H14.
                + inversion H15.
              - simpl.
                rewrite removelast_app in *
                  by (simpl;intro H';discriminate).
                destruct xs as [ | x'' xs _ ] using rev_ind.
                + Opaque addr_of_last. simpl in *. compute.
                  inversion Hcycliclist; inversion H13;
                  inversion H16; inversion H2; inversion Hlink; subst; now simpl.
                + repeat rewrite app_comm_cons in *.
                  repeat rewrite map_app in *.
                  destruct x''; simpl in *.
                  repeat rewrite app_comm_cons in *.
                  rewrite shift_right_last in Hcycliclist.
                  rewrite shift_right_last.
                  destruct xs as [ | x''' xs _] using rev_ind.
                  * inversion Hlink; inversion H14; inversion H13;
                    inversion H17; inversion Hcycliclist;subst; simpl in *.
                    { inversion H34; subst.
                      - trivial.
                      - inversion H26. }
                  * repeat rewrite map_app in *.
                    Opaque removelast. simpl in *. Transparent removelast.
                    repeat rewrite app_comm_cons in *.
                    rewrite removelast_app in Hcycliclist by (intro H';discriminate).
                    simpl in *. repeat rewrite app_nil_r in *.
                    repeat rewrite app_comm_cons.
                    rewrite Hcycliclist.
                    repeat rewrite app_comm_cons.
                    { repeat f_equal.
                      - inversion H2; subst.
                        apply cyclicdoubletail_last with (default:=x''') in H1. 
                        rewrite <- app_assoc in H1.
                        repeat rewrite app_comm_cons in H1.
                        rewrite app_assoc in H1.
                        rewrite Last.last_last in H1.
                        assumption.
                      - rewrite <- app_assoc in Hlink.
                        repeat rewrite app_comm_cons in Hlink.
                        destruct x'''.
                        rewrite addr_of_last_prop in Hlink.
                        inversion Hlink; subst.
                        trivial. }
            }
    Qed.

    Lemma notInFirst:
      forall state root xs pointer,
        CyclicDoubleLinked state root xs ->
        ~(In pointer (map third xs)) ->
        ~(In pointer (map first xs)).
    Proof.
      intros state root xs pointer CDL HnotIn.
      contradict HnotIn.
      apply shift_right_In.
      erewrite linksProperty by eassumption.
      now rewrite <- shift_left_In.
    Qed.

    Lemma cyclicDoubleTailNoDup:
      forall xs state root firstpointer,
        CyclicDoubleTail state root firstpointer xs ->
        NoDup(tl(map first xs)) /\ NoDup (removelast(map third xs)).
    Proof.
      intros xs state root firstpointer H.
      induction H as [H | state' heap' other' root'' firstpointer prev'
                                        Hdom d prev Hv1 Hv2 xs'' Hstate HnotNil Hcyclic'
                                        [IH1 IH2] Hstruct Hprev Hnext Hdata Hvalid ].
      - split; constructor.
      - split.
        + simpl; inversion Hcyclic'; subst; simpl.
          * constructor; auto; constructor.
          * clear IH2. simpl in *; constructor; trivial.
            inversion Hstruct; subst.
            (* En fait il manque des hypothèses dans la definition de
               CyclicDouleTail pour pouvoir conclure. En effet quand
               on rajoute une cellule, il n'y a aucune contrainte sur
               la valeur de son champ prev: or si on remet une adresse
               d'un champ prev d'une cellule existante c'est problématique. *)
    Admitted.
                  
        
  (* Autre solution 
    
    Inductive move_pointers :
      list(Ad.t*Cell.(t)*Ad.t) -> Ad.t -> list(Ad.t*Cell.(t)*Ad.t) -> Prop :=
    | update_nil : forall adr,
        move_pointers [] adr []
    | update_singleton : forall adr adr' d,
        move_pointers [(adr',d,adr')] adr [(adr,d,adr)]
    | update_app: forall adr_prev d adr_next xs adr'_prev d' adr'_next adr,
        move_pointers ([(adr_prev,d,adr_next)]++xs++[(adr'_prev,d',adr'_next)])
                      adr
                      ([(adr,d,adr_next)]++xs++[(adr'_prev,d',adr)]).
  
    Inductive CyclicDoubleLinked :
      State.t->Ad.t->list (Ad.t * Cell.(t) *Ad.t) -> Prop := 
    | cdl_nil : forall state,
        CyclicDoubleLinked state He.null []
    | cdl_singleton : forall state heap other root Hroot Hprev Hnext d,
        (heap,other) = State.split state ->
        Cell.(to_address) (He.get heap root Hroot Cell.(o_prev) Hprev) == root ->
        Cell.(to_address) (He.get heap root Hroot Cell.(o_next) Hnext) == root ->
        Cell.(data) state root == d ->
        Cell.(is_valid) state d ->
        CyclicDoubleLinked state root [(root,d,root)]
    | cdl_app :
        forall state heap heap' other root' Hroot' root Hroot xs xs'
               Hprev Hprev' Hnext previous d next v_root Hprevious Hnext',
          ~ xs = [] ->
          (heap,other) = State.split state ->
          CyclicDoubleLinked state root' xs ->
          Cell.(data) state root == d ->
          Cell.(is_valid) state d ->
          ~ In root (map third xs) ->
          Cell.(to_address) (He.get heap root Hroot Cell.(o_prev) Hprev) == previous ->
          Cell.(to_address) (He.get heap root Hroot Cell.(o_next) Hnext) == next ->
          previous = get_default first (hd_error xs) root ->
          next = get_default third (last_error xs) root ->
          (* next = root' -> : Is it really necessary ? PROBABLY NOT, to be check with a lemma *)
          move_pointers xs root xs' ->
          Cell.(of_address) root == v_root ->
          (* For heaps, = is not so good, an extensional equivalence
          that enforces get equality only on root' and xs is
          NECESSARY: *)
          heap' = He.set (He.set heap root' Hroot' Cell.(o_prev) Hprev' v_root) 
                         previous Hprevious Cell.(o_next) Hnext' v_root ->
          CyclicDoubleLinked (State.combine(heap',other)) root ((previous,d,next)::xs').

  
        
    Lemma linksProperty:
      forall state root xs,
        CyclicDoubleLinked state root xs ->
        shift_right (map third xs) = shift_left (map first xs).
    Proof.
      intros state root xs H. induction H.
      - trivial.
      - trivial.
      - have (xs <> []) as HnotNil.
        have (move_pointers xs root xs') as Hmove.
        induction Hmove.
        + now contradict HnotNil.
        + simpl in *; unfold compose in *; simpl in *; subst.
          replace [adr';adr] with ([adr'] ++ [adr]) by auto.
          now rewrite shift_right_last.
        + simpl in *; unfold compose in *; simpl in *; subst.
          rewrite map_app in *; simpl in *; unfold compose in *; simpl in *.
          repeat rewrite app_comm_cons in *.
          rewrite shift_right_last.
          rewrite shift_right_last in IHCyclicDoubleLinked.
          autounfold; simpl; repeat rewrite <- app_comm_cons; repeat rewrite rev_unit; simpl.
          rewrite IHCyclicDoubleLinked; repeat rewrite map_app.
          trivial.
    Qed.

    Lemma shift_left_In:
      forall A (x:A) xs, In x xs <-> In x (shift_left xs).
    Proof.
      intros A x. induction xs as [ | x' xs IH ].
      - intuition.
      - simpl; split; intro H.
        + destruct H; subst; intuition.
        + apply in_app_iff in H; simpl in H.
          intuition.
    Qed.

    Lemma shift_right_In:
      forall A (x:A) xs, In x xs <-> In x (shift_right xs).
    Proof.
      intros A x xs. unfold shift_right.
      transitivity (In x (shift_left (rev xs))).
      transitivity (In x (rev xs)).
      apply in_rev.
      apply shift_left_In.
      apply in_rev.
    Qed.

    Lemma notInFirst:
      forall state root' xs root,
        CyclicDoubleLinked state root' xs ->
        ~(In root (map third xs)) ->
        ~(In root (map first xs)).
    Proof.
      intros state root' xs root CDL HnotIn.
      contradict HnotIn.
      apply shift_right_In.
      erewrite linksProperty by eassumption.
      now rewrite <- shift_left_In.
    Qed.
      
    Lemma NoDupCyclicDoubleLinked:
      forall state root xs,
        CyclicDoubleLinked state root xs ->
        NoDup (map first xs) /\ NoDup (map third xs). (* En faire un seul + NoDup sur shift et c'est OK *)
    Proof.
      intros state root xs.
      assuming (CyclicDoubleLinked state root xs) as H
      prove ( NoDup (map first xs) /\ NoDup (map third xs) ).
      {
        induction H.
        - split; constructor.
        - split; constructor; intuition.
        - assuming ( NoDup (map first xs) /\ NoDup (map third xs) ) as IH
          assuming ( CyclicDoubleLinked state root' xs ) as Hxs 
          assuming ( move_pointers xs root xs'  ) as Hmove
          assuming ( previous = get_default first (hd_error xs) root ) as get_previous
          assuming ( next = get_default third (last_error xs) root ) as get_next 
          assuming ( ~ In root (map third xs) ) as HnotIn                                             
          prove ( NoDup (map first ((previous, d, next) :: xs')) /\
                  NoDup (map third ((previous, d, next) :: xs')) ).
          {
            assert( NoDup (map first xs') /\ NoDup (map third xs') ) as Hxs'.
            {
              inversion Hmove; subst.
              - split; simpl; constructor.
              - split; constructor; intuition.
              - assert(~ In root
                         (map first
                              ([(adr_prev, d0, adr_next)]
                                 ++ xs0 ++ [(adr'_prev, d', adr'_next)]))) as HnotInFirst
                    by conclude by eapply notInFirst.
                simpl.
                repeat rewrite map_app in *; simpl.
                destruct IH as [IH1 IH2].
                apply ListBasics.noDupConcat in IH1; simpl in IH1.
                rewrite app_assoc in IH2.
                apply ListBasics.noDupConcat in IH2; simpl in IH2.
                destruct IH1 as [IH1 IH3], IH2 as [IH2 IH4].
                assert( NoDup (map first (xs0 ++ [(adr'_prev, d', root)] )) /\
                        NoDup (map third ([(adr_prev, d0, adr_next)] ++ xs0)) )
                  by (rewrite map_app; split; auto).
                split.
                + assert( ~ In root ((map first xs0)++[adr'_prev]) )
                     by now (contradict HnotInFirst; simpl; right).
                  now constructor.
                + apply Sorted.permutationNoDup with (root::adr_next::map third xs0).
                  apply Permutation.Permutation_cons_append.
                  assert( ~ In root (adr_next::map third xs0) )
                    by (contradict HnotIn; rewrite app_assoc; apply in_app_iff; now left).
                  now constructor.
            }
            inversion Hmove; subst.
            - constructor; intuition.
            - simpl in *; split;
              (constructor; [contradict HnotIn;simpl in HnotIn; intuition |
                             constructor; intuition]).
            - assert(~ In root
                         (map first
                              ([(adr_prev, d0, adr_next)]
                                 ++ xs0 ++ [(adr'_prev, d', adr'_next)]))) as HnotInFirst
                by conclude by eapply notInFirst.
              simpl; autounfold; rewrite app_comm_cons, rev_unit; simpl.
              split.
              + apply Sorted.permutationNoDup with (root::adr_prev::map first (xs0++[(adr'_prev,d',root)])).
                constructor.
                constructor.
                * contradict HnotInFirst. simpl in *.
                  rewrite map_app, in_app_iff in *; intuition.
                * repeat rewrite map_app in *; simpl.
                  destruct IH as [IH1 IH2]. now simpl in IH1.
              + eapply Sorted.permutationNoDup with (root::adr'_next::adr_next::map third xs0).
                rewrite map_app; simpl; apply Permutation.Permutation_cons_append.
                constructor.
                * contradict HnotIn. repeat (rewrite map_app; simpl).
                  rewrite in_app_iff; simpl in *.
                  destruct HnotIn as [ H' | [H'|H']]; auto.
                * repeat rewrite map_app in IH.
                  destruct IH as [IH1 IH2]. simpl in IH2. 
                  apply Sorted.permutationNoDup with (adr_next :: map third xs0 ++ [adr'_next]).
                  rewrite app_comm_cons.
                  now apply Permutation.Permutation_sym, Permutation.Permutation_cons_append.
                  assumption.
          }
      }
    Qed.

    Lemma NoDupCyclicDoubleLinkedUpdated:
      forall state root xs root' xs',
        CyclicDoubleLinked state root xs ->
        not(In root' (map third xs)) ->
        move_pointers xs root' xs' ->
        NoDup (map first xs') /\ NoDup (map third xs').
    Proof.
      intros state root xs root' xs' Hcdl HnotIn Hmove.
      assert(~In root' (map first xs)) as HnotInFirst
          by (conclude by eapply notInFirst).
      inversion Hmove; subst.
      - split; simpl; constructor.
      - split; simpl; constructor; intuition.
      - apply NoDupCyclicDoubleLinked in Hcdl.
        repeat rewrite map_app in Hcdl; simpl in Hcdl; destruct Hcdl as [H1 H2].
        split.
        + repeat rewrite map_app; simpl; constructor.
          * contradict HnotInFirst. repeat rewrite map_app; simpl; now right.
          * now inversion H1.
        + repeat rewrite map_app; simpl.
          apply Sorted.permutationNoDup with (root'::adr_next::map third xs0).
          apply Permutation.Permutation_cons_append.
          constructor.
          * contradict HnotIn. repeat rewrite map_app; simpl; rewrite in_app_iff; simpl.
            inversion HnotIn; auto.
          * rewrite app_comm_cons in H2. apply ListBasics.noDupConcat in H2.
            intuition.
    Qed.
      
    Lemma dataInCyclicDoubleLinked:
      forall state root l1 l2 previous d next xs,
        xs = l1++(previous,d,next)::l2 ->
        CyclicDoubleLinked state root xs ->
        data Cell state (addr root l1 l2 (previous, d, next)) == d /\ Cell.(is_valid) state d.
    Proof.
      intros state root l1 l2 previous d next xs.
      assuming ( xs = l1++(previous,d,next)::l2 ) as Hxs 
      assuming (CyclicDoubleLinked state root xs) as H
      prove (data Cell state (addr root l1 l2 (previous, d, next)) == d /\ Cell.(is_valid) state d).
      {
        generalize l1 l2 previous d next Hxs. clear l1 l2 previous d next Hxs.
        induction H; intros l1 l2 previous0 d0 next0.
        - assuming ([] = l1 ++ (previous0, d0, next0) :: l2) as Hnil
          prove ( data Cell state (addr null l1 l2 (previous0, d0, next0)) == d0 /\ Cell.(is_valid) state d0).
          { destruct l1; discriminate. }
        - assuming ([(root, d, root)] = l1 ++ (previous0,d0,next0) :: l2) as Hxs
          prove ( data Cell state (addr root l1 l2 (previous0, d0, next0)) == d0 /\ Cell.(is_valid) state d0).
          {
            assert((root,d,root) = (previous0,d0,next0)) as Hd0 by conclude by apply app_singleton in Hxs.
            assert(l1 = []) by conclude by apply app_singleton in Hxs.
            assert(l2 = []) by conclude by apply app_singleton in Hxs.
            assert(addr root l1 l2 (previous0,d0,next0) = root) as Haddr by (subst; auto).
            conclude by replace ( data Cell state (addr root l1 l2 (previous0, d0, next0)) == d0 /\
                      Cell.(is_valid) state d0 )
                with    ( data Cell state root == d /\ Cell.(is_valid) state d )
                by (rewrite Haddr; now inversion Hd0).
          }
        - assuming ( (previous, d, next) :: xs' = l1 ++ (previous0, d0, next0) :: l2 ) as Hxs 
          assuming ( data Cell state root == d ) as Hd 
          assuming ( is_valid Cell state d ) as Hvalid
          prove ( data Cell (combine (heap', other0)) (addr root l1 l2 (previous0, d0, next0)) == d0 /\
                  is_valid Cell (combine (heap', other0)) d0 ).
          {
            assert(In (previous0, d0, next0)( (previous,d,next)::xs')) as Hin
                by (rewrite Hxs; apply in_app_iff; intuition).
            case Hin.
            - assuming ( (previous, d, next) = (previous0, d0, next0) ) as Heq prove goal.
              {
                assert(l1 = []) by admit.
                simpl.
                {
                  
                  
                  
                }
              }
            (* NoDup needed ! *)
              admit.
            - admit.  
          }
      }
    Admitted.
    
    Lemma CyclicDoubleLinked_In:
      forall state root xs e,
        CyclicDoubleLinked state root xs ->
        In e xs ->
        exists l1 l2,
          xs = l1 ++ e::l2 /\
          CyclicDoubleLinked state (addr root l1 l2 e) (e::l2++l1).
    Proof.
      intros state root xs e.
      introduce (CyclicDoubleLinked state root xs) as CDL.
      introduce (In e xs) as Hin.
      
      assert(exists l1 l2, xs = l1++e::l2) as H by now apply in_split.
      witness l1 l2 from H. have (xs=l1++e::l2) as Hxs.

      assert(CyclicDoubleLinked state (addr root l1 l2 e) (e::l2++l1)).
      {
        generalize l1 l2 e Hxs Hin. clear Hin l1 l2 e Hxs.
        induction CDL; intros l1 l2 e.
        - assuming([] = l1 ++ e :: l2) assuming(In e []) as Hin
          prove (CyclicDoubleLinked state (addr null l1 l2 e) (e :: l2 ++ l1)).
          { inversion Hin. }
        - assuming ([(root, d, root)] = l1 ++ e :: l2) as Hxs
          assuming (In e [(root,d,root)]) as Hin                                                          
          prove (CyclicDoubleLinked state (addr root l1 l2 e) (e :: l2 ++ l1)).
          {
            assert(e = (root,d,root)) by (now inversion Hin).
            assert(l1 = []) by
                  (destruct l1; trivial;
                   inversion Hxs; destruct l1; discriminate).
            assert(l2 = []) by (subst; now inversion Hxs).
            assert(addr root l1 l2 e = root) as Haddr by (subst; auto).
            replace (CyclicDoubleLinked state (addr root l1 l2 e) (e :: l2 ++ l1))
            with    (CyclicDoubleLinked state root [(root,d,root)])
              by (rewrite Haddr; clear Haddr; subst; trivial).
            conclude by eapply cdl_singleton.
          }
        - assuming ( (previous, d, next) :: xs' = l1 ++ e :: l2) as Hxs
          assuming ( In e ((previous, d, next) :: xs') ) as Hin                                                            
          assuming ( move_pointers xs root xs' ) as xs_xs' 
          assuming (CyclicDoubleLinked state root' xs) as CDL 
          assuming ((heap,other0) = split state) as Hstate 
          assuming (to_address Cell (get heap root Hroot (o_prev Cell) Hprev) == previous) as Hprev1
          assuming (previous = get_default first (hd_error xs) root) as Hprev2
          assuming (to_address Cell (get heap root Hroot (o_next Cell) Hnext) == next) as Hnext1 
          assuming (next = get_default third (last_error xs) root) as Hnext2 
          assuming (heap' =
                    set (set heap root' Hroot' (o_prev Cell) Hprev' v_prev) previous
                        Hprevious (o_next Cell) Hnext' v_next) as Hheap' 
          assuming (forall l1 l2 e, xs = l1 ++ e :: l2 -> In e xs -> 
                                    CyclicDoubleLinked state (addr root' l1 l2 e) (e :: l2 ++ l1)) as IH 
          prove(CyclicDoubleLinked (combine (heap', other0)) (addr root l1 l2 e) (e :: l2 ++ l1)).
          {
            assert ( CyclicDoubleLinked (combine (heap',other0)) root ((previous,d,next):: xs') ) by
                (econstructor; eauto).
            
            destruct e as [[previous' d'] next' ].
            admit.
            (* eapply cdl_app; eauto : Many small facts to prove, a lot of them being consequence of the 
               fact we have several CyclicDoubleLinked => lemmas for these facts *)
          }
      }
    Admitted. *)

      
  End Cell.
  
End T.


(*
*** Local Variables:
*** coq-load-path: (("." "Common") ("../LIFO" "LIFO") "../Support")
*** End:
*)