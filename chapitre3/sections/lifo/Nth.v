(** * Facts about the nth element of a list *)
Require Import List.
Require Import Lia.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section ListNth.
  
  Variable A:Type.

  Lemma inLtLengthNth : 
    forall (a:A) (l:list A),
      In a l -> 
      exists n,  n < length l /\ forall b, nth n l b = a.
  Proof.
  Admitted.
    (* induction l; intros Ha.
    inversion Ha.
    destruct Ha as [Hb | Hc].
    exists 0; firstorder using lt_O_Sn.
    destruct (IHl Hc) as [n [Ha Hb]].
    exists (S n); firstorder using lt_n_S.
  Qed. *)


  (** Two lists [l1 l2] with same length are equal if for each [n] lesser than there length, [n]th element of [l1 ] is equal to [n]th  element of [l2] *)
  Lemma nthSameLengthEqual:
    forall (l1 l2:list A) d,
    length l1 = length l2 ->
    (forall n, n < length l1 -> nth n l1 d = nth n l2 d) ->
    l1 = l2.
  Proof.
  Admitted.
    (* induction l1; intros. 
      destruct l2. 
        reflexivity. 
        simpl in H; discriminate.
      destruct l2.
        simpl in H; discriminate.
        replace a with (nth 0 (a::l1) d) by firstorder.
        replace a0 with (nth 0 (a0::l2) d) by firstorder.
        rewrite H0 by (simpl; firstorder).
        simpl; f_equal.
        apply IHl1 with (d:=d).
          (simpl in H; intuition).
          (intros;
            replace (nth n l1 d) with (nth (S n) (a::l1) d) by firstorder;
              replace (nth n l2 d) with (nth (S n) (a0::l2) d) by firstorder;
                apply H0).
            simpl; firstorder.
  Qed. *)

  (** Two lists on a type with at least two different values are equals 
     if for all default value and for all position their [nth] elements 
     are the same. *)
  Lemma nthEqual :
    forall l1 l2,
      (exists a:A, exists b:A, a<>b) ->
      (forall n (d:A), nth n l1 d = nth n l2 d) -> 
      l1 = l2.
  Proof.
    intros l1 l2 Hcouple.
    destruct Hcouple as [d1 Hcouple].
    destruct Hcouple as [d2 Hd1d2 ].
    generalize dependent l2.
    induction l1.
    (* l1 = nil *)
      destruct l2.
      (* l2 = nil *)
        auto.
      (* l2 = cons *)
        intro H.
        set(H1:=H O d1).
        set(H2:=H O d2).
        simpl in *.
        rewrite <- H2 in H1.
        elim Hd1d2. assumption.
    (* l1 = cons *)
      induction l2.
      (* l2 = nil *) 
         intros H.
         set(H1:=H O d1).
         set(H2:=H O d2).
         simpl in *.
         rewrite H1 in H2.
         elim Hd1d2. assumption.
      (* l2 = cons *) 
         intro H.
         set(HaaO:=H 0 d1).
         simpl in HaaO.
         rewrite HaaO in *.
         rewrite (IHl1 l2).
         auto.
         intro n.
         apply (H (S n)).
  Qed. 

   (** 
    nth element of seq is n (with strong hypothesis on n and a random function f)
   *)
   Lemma seqNthMap : forall (A B: Type) (l : list A) (f : nat-> B) (a : B) start n ,
     n < length l -> nth n (map f (seq start (length l))) a = f (start + n).
   Proof.
   Admitted. 
   (* intros A0 B0 l ; induction (length l) ; intros.
   inversion H.
   simpl seq. simpl map.
   generalize (IHn f a (S start) (pred n0)). intros Hind.
   destruct n0.
    simpl. rewrite plus_0_r. reflexivity.
    rewrite <- pred_Sn in *.
    rewrite <- plus_n_Sm. simpl in Hind. rewrite <- Hind.
   reflexivity.
   inversion H ; intuition.
   Qed. *)

  Lemma nth_errorIn:
    forall (l:list A)(pos:nat)(a:A),
      nth_error l pos = Some a ->In a l.
  Proof.
    intros l pos a H; 
      generalize dependent pos ; induction l; destruct pos ; intros H;
      try(solve [ inversion H ]);
        try(solve [simpl in *; inversion H; left ; reflexivity]).
    simpl in *; right ; eauto using IHl.
  Qed.

  (** nth element is in the list *)
  (* Removed: already in the Coq library *)

  (* TODO: To be deprecated by the version with dependent types. *)

  (** if [n] is lesser than [length l], result of [List.nth] is independant of parameter [d] *)
  Definition nth'b: forall (n:nat) (l:list A),
    n < length l -> {a:A | forall d, nth n l d = a}.
  Proof.
  Admitted.
    (* intros.
    destruct l. simpl in H. absurd (n<0). apply lt_n_O. assumption.
    exists (nth n (a::l) a).
    intro.
    apply nth_indep. assumption.
  Defined. *)

  (** [n]th element of the list without default value as [n] is lesser than [length l] *)
  Definition nth' (n:nat) (l:list A) (pre: n<length l) :=
    match nth'b l pre with exist a _ => a end.

  (** [nth'] is equal to [nth] if [n] is lesser than [length l] *)
  Lemma nth'_nth: forall (n:nat) (l:list A) (pre: n<length l)(d:A), 
    nth' l pre = nth n l d.
  Proof.
    intros.
    unfold nth'.
    destruct (nth'b l pre).
    auto.
  Qed.


  (*
  The head of a list is the same as the 0th element
 	*)
	Lemma nth_hd : forall (A : Type) (b : A) l, hd b l = nth 0 l b.
	Proof.
	destruct l ; reflexivity.
	Qed.


(*
This lemma is the combination between app_nth1 and app_nth2
 l++ l1 : if the element of l are the same as the first element of u
and those of l1 are the same of the last of u then the two lists have the same elements
*)
Lemma app_nth : forall (A : Type) (l l1 : list A) u b, (forall n, (n < length l -> nth n l b = nth n u b) 
  /\ (n < length l1 -> nth n l1 b = nth (n + length l) u b))  -> forall n, n < length (l++l1) -> 
  length (l ++ l1) = length u -> nth n (l ++ l1) b = nth n u b.
Proof.
Admitted.
(* intros.

(* destruct (le_lt_dec (length l) n). *)
rewrite app_nth2 ; intuition. destruct (H (n - length l)).
assert (plus_minus : forall a b, a >= b -> a - b + b = a).
intros. lia.
rewrite plus_minus in H3. apply H3.
rewrite app_length in H0. intuition. intuition.
rewrite app_nth1 ; intuition. destruct (H n) ; intuition.
Qed. *)



End ListNth.

Arguments nth' [A].
