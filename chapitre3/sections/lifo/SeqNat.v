Require Import Arith Lia.
Require Import Min.
Require Import Coq.Lists.List.

Require Import sections.lifo.Misc.
Require Import sections.lifo.InSig.
Require Import sections.lifo.Nth.
Require Import sections.lifo.BoundedNat.
Require Import sections.lifo.Firstn_skipn.
Require Import sections.lifo.Length.
Require Import sections.lifo.Map.

Set Implicit Arguments.

(** * Tools for sequences of natural ([seq]) *)

Section SeqTools.

(** seq and append from [s] to [q+r]*)
  Lemma seqAppN: 
    forall (n q r:nat),
      seq n (q+r) = seq n q ++ seq (n+q) r.
  Proof.
    intros s q r.
    eapply nthSameLengthEqual.
    rewrite app_length. repeat (rewrite seq_length). reflexivity.
    instantiate (1:=0).
    intros.
    rewrite seq_length in H.
    rewrite seq_nth.
    assert (n < q \/ q <= n) as Disj.  lia. elim Disj.
    intro. rewrite app_nth1. rewrite seq_nth. reflexivity.
    assumption.
    rewrite seq_length. assumption.
    intro. rewrite app_nth2. rewrite seq_nth. rewrite seq_length. firstorder. 
    admit.
    admit.
    admit.
    admit.
    admit.
    (* rewrite seq_length. lia.
    rewrite seq_length. unfold ge. assumption.
    assumption. *)
Admitted.
    (* Qed. *)

  (** seq and append from [0] to [q+r]*)
  Lemma seqApp0: 
    forall (q r:nat),
      seq 0 (q+r) = seq 0 q ++ seq q r.
  Proof.
    intros.
    change (seq q r) with (seq (0+q) r).
    apply seqAppN.
  Qed.

 Notation "[ x1 ; .. ; xn ] " := (cons x1 (.. (cons xn nil) .. )).
 Notation "[]" := nil(at level 0).

  (** seq and append from [0] to [q+r]*)
  Lemma seqAppMiddle: 
    forall (start m length :nat) (proof1 : start <= m) (proof2 : m < start + length),
      seq start length = (seq start (m-start)) ++ [m] ++ (seq (m+1) (length - (m -start +1))).
  Proof.
    intros start m length proof1 proof2.
    case_eq(m+1);[ intro mp1_0 | intros n mp1_sn].
    contradict mp1_0; rewrite plus_comm; change (m+1) with (S m); simpl; discriminate.
    simpl. 
    set (q:=m-start).
    assert( m_qtart_q : m=start +q)  by (subst q; auto with arith).   
    replace ( m :: seq (S n) (length - ( q+ 1))) with ( seq (m) (S(length - (q+1)))) by (
      simpl; rewrite plus_comm in *; change (1+m) with (S m) in *;  rewrite mp1_sn;   reflexivity).   
    rewrite m_qtart_q.
    rewrite <- seqAppN .
    assert ( H : (q + S (length - (q + 1)))= length) by lia.
    rewrite H; reflexivity.
  Qed.

  (** if [x] is in [seq 0 i] then [x<i] *)
  Lemma inSeq0Lt:
    forall (i x: nat), 
      List.In x (seq 0 i) -> x < i.
  Proof.
    intros ? ? H.
    destruct (@inLtLengthNth _ _ _ H) as [? [Ha Hb]].
    generalize (Hb i); clear Hb; intro Hb.
    rewrite seq_length in Ha.
    rewrite seq_nth in Hb.
    simpl in Hb.
    rewrite <- Hb.
    assumption.
    assumption.
  Qed.

(** if [x] is in [seq i j] then [i<x] *)
  Lemma inSeqGt (i j x: nat): 
    List.In x (seq i j) -> i <= x.
  Proof.
    induction i.
    intros. auto with arith.
    intros.
         induction j. 
               simpl in H. contradict H. 
               replace ( seq (S i) (S j)) with ( seq(S i) j ++ seq ((S i) + j) 1) in H;[|
                     replace (S j ) with (j + 1) by (simpl;rewrite plus_comm; auto with arith);symmetry;apply seqAppN
               ].
               rewrite in_app_iff in H.
               simpl in H.
               elim H.
                    apply IHj.
                    admit.
                    admit.
                    (* intros H0. elim H0.                *)
                    (* intros H1. rewrite <- H1. auto with arith.
                    intros H1. elim H1. *)
  Admitted.
                    (* Qed. *)

  (** if [x] i in [seq start len] then [x<len+start] *)
  Lemma inSeqLt:
    forall (start len x: nat), 
      List.In x (seq start len) -> 
      x < start+len.
  Proof.
    intros start len x H.
    apply inSeq0Lt; rewrite seqApp0; rewrite in_app_iff; right ; assumption.
  Qed.


  (** if [x] i in [seq start len] then [x>=start] *)
  Lemma inSeqLe : forall len n start, In n (seq start len) -> n >= start.
  Proof.
  induction len.
   intuition. (* simpl in H. destruct H. *)
   intros. destruct H.
   intuition.
   assert (n >= S start). apply IHlen. intuition.
   intuition.
  Qed.

  Program Definition strongSeq (start len : nat) : 
    {l : list (boundedNat (start+len)) | listProj l = seq start len } :=
    inSig (fun n=>n<start+len) (seq start len) (inSeqLt start len).
  Next Obligation.
    apply inSigProj.
  Qed.

  (** The list of the [n] first elements of [seq s m] is sequence from
     [s] to [(min m n)] *)
  Lemma firstn_seq:
    forall m n s, 
      firstn n (seq s m) = seq s (min m n).
  Proof.
  Admitted.
    (* intros.
    apply nthSameLengthEqual with (d:=0).
    rewrite firstn_length.
    repeat (rewrite seq_length).
    apply min_comm.
    intros.
    rewrite firstn_length in H. rewrite seq_length in H.
    pattern (min m n).
    destruct (min_dec m n).
    rewrite e.
    apply firstn_nth.
    apply lt_le_trans with (m:=min n m). assumption. auto with arith.
    rewrite e.
    rewrite firstn_nth.
    replace (seq s m) with (seq s n ++ seq (s+n) (m-n)).
    rewrite app_nth1. reflexivity.
    rewrite seq_length. rewrite <- e. rewrite min_comm. assumption.
    rewrite <- seqAppN. f_equal.
    symmetry. apply le_plus_minus.
    rewrite <- e. auto with arith.
    apply lt_le_trans with (m:=min n m). assumption. auto with arith.
  Qed. *)

  (** The list without the first [n] elements of [seq s m] is the
     sequence from [s+n] to [m-n] *)
  Lemma skipn_seq: 
    forall m n s, 
      skipn n (seq s m) = seq (s+n) (m-n).
  Proof.
    intros.
    pose (mn:=le_lt_dec m n).
    destruct mn.
    replace (m-n) with 0 by lia.
    rewrite le_plus_minus with (m:=n) (n:=m).
    rewrite plus_comm.
    rewrite <- skipn_compose.
    replace (skipn m (seq s m)) with (skipn (length (seq s m)) (seq s m)).
    rewrite skipn_length_l.
    simpl. rewrite skipn_nil.
    reflexivity.
    rewrite seq_length; reflexivity. trivial.
    rewrite le_plus_minus with (m:=m) (n:=n).
    rewrite seqAppN.
    rewrite skipn_app2.
    rewrite seq_length.
    rewrite <- minus_n_n. simpl.
    rewrite minus_plus.
    reflexivity.
    rewrite seq_length. auto.
    apply lt_le_weak.
    trivial.
  Qed.

Lemma seqShiftGen:
        forall len start offset : nat, 
          List.map (fun n=>offset+n) (seq start len) = seq (offset+start) len.
      Proof.
        induction len; simpl.
          trivial.
          intros start offset; f_equal; rewrite IHlen; rewrite plus_comm; 
            simpl; rewrite plus_comm; trivial.
      Qed.

  Definition replicate (A:Type) (n:nat) (a:A) :=
    List.map (fun _ => a) (seq 0 n).
  
  Lemma replicateLength:
    forall (A:Type) (n:nat) (a:A),
      length (replicate n a) = n.
  Proof.
    intros.
    unfold replicate.
    rewrite map_length.
    apply seq_length.
  Qed.

  Lemma replicateProperty:
  forall (A:Type)(size:nat)(value:A),
    forall a:A, In a (replicate size value) -> value = a.
  Proof.
    intros A size value a H; induction size as [ _ | size].
      contradict H.
      simpl in H; destruct H as [H | H].
        assumption.
        rewrite mapConstant with (l2:=seq 0 size) in H;
          unfold replicate in *; intuition.
          repeat (rewrite seq_length); trivial.
  Qed.

  Lemma replicateNatProperty:
    forall (size value m :nat), 
      fold_right plus m (replicate size value) = size * value + m.
  Proof.
    intros size value m; induction size.
      trivial.
      simpl; rewrite mapConstant with (l2:= seq 0 size); auto;
        repeat (rewrite seq_length); trivial. unfold replicate in IHsize; 
         rewrite IHsize; lia.
  Qed.

  Require Import NArith.
  Require Import ZArith.

  Open Scope N_scope.

  Lemma replicateNProperty:
    forall (size value m : N), 
      fold_right N.add m (replicate (N.to_nat size) value) = size * value + m.
  Proof.
    intros size value m; induction size using N.peano_ind.
      trivial.
      unfold replicate; rewrite N2Nat.inj_succ; simpl;
        rewrite mapConstant with (l2:= seq 0 (N.to_nat size)); auto;
        repeat (rewrite seq_length); trivial. unfold replicate in IHsize.
         rewrite IHsize, Nmult_Sn_m; apply N.add_assoc.
  Qed.

  Close Scope N_scope.

  Require Import Sorting.Sorting.
  (**
    HdRel definition on seq
  *)
  Lemma seqHdRel : forall n m, HdRel le n (seq (S n) m).
  Proof.
  intros n m.
  destruct n.
   destruct (seq 1 m).
    constructor.
    constructor. intuition.
   destruct m.
    constructor.
    simpl.
    constructor.
    intuition.
  Qed. 

  (**
    Seq is sorted
  *)
  Lemma seqSorted : forall m n, Sorted le (seq n m).
  Proof.
  induction m ; intros n.
   constructor.
   simpl. constructor.
   apply IHm.
   apply seqHdRel.
  Qed.

  (**
    start <= n < start + len -> n in (seq start len)
  *)
  Lemma inSeq : forall len start a, start <= a < start + len -> In a (seq start len).
  Proof.
  induction len ; intros.
   assert (start < start) by intuition.
   simpl. intuition.
   simpl.
   inversion H. inversion H0.
    left ; reflexivity.
    right. apply IHlen.
    intuition.
  Qed.

  (**
    Recursion part of seq
  *)
  Lemma seq_S : forall len start, seq start (S len) = start :: seq (S start) len.
  Proof.
  intuition.
  Qed.

  (*
    Deploying seq from the end of the list instead of doing it from the beginning
  *)
  Lemma seq_S_app : forall len start, seq start (S len) = seq start len ++ ((start + len) :: nil).
  Proof.
  induction len ; intros. simpl. rewrite plus_0_r ; reflexivity.
   rewrite seq_S. rewrite IHlen.
   simpl. rewrite plus_n_Sm. reflexivity.
  Qed.



End SeqTools.

Section InSigTools.

Lemma inSigSeq : forall m start P H,
  map (fun x => projT1 (sigT_of_sig x)) (inSig P (seq start m) H) = (seq start m).
Proof.
induction m ; intros.
 reflexivity.
 simpl. rewrite IHm.
 reflexivity.
Qed.

(*
Lt property : two seq insig list can be concatened
*)
Lemma inSigSeqApp : forall m len start (P := fun x => x < m) H1 H2 H3, 
  (inSig P (seq start (S len)) H1) = (inSig P (seq start len) H2) ++ (inSig P (seq (start + len) 1) H3).
Proof.
intros.
assert (H5 : forall a : nat,
  In a (seq start len ++ seq (start + len) 1) -> (fun x : nat => x < m) a).
intuition. apply H1. rewrite seq_S_app. assumption.
unfold P. rewrite (inSig_app (seq start len) (seq (start + len) 1) H2 H3 H5).
apply inSig_eq.
apply seq_S_app.
Qed.

End InSigTools.

Hint Resolve   seqAppN : seq.
Hint Resolve   seqApp0 : seq.
Hint Resolve   inSeq0Lt: seq.
Hint Resolve    inSeqLt: seq.
Hint Resolve    inSeqLe: seq.
Hint Resolve    firstn_seq : seq.
Hint Resolve    skipn_seq : seq.
Hint Resolve    replicateLength : seq.
Hint Resolve    seqHdRel : seq.
Hint Resolve    seqSorted : seq.
Hint Resolve    inSeq : seq.
Hint Resolve    seq_S :seq.
Hint Resolve   seq_S_app :seq.
Hint Resolve    inSigSeq : seq.
Hint Resolve    inSigSeq : insig.
Hint Resolve    inSigSeqApp : seq.
Hint Resolve    inSigSeqApp : insig.

Hint Rewrite <- seqAppN :seq.
Hint Rewrite <- seqApp0 :seq.
Hint Rewrite    firstn_seq : seq.
Hint Rewrite    skipn_seq : seq.
Hint Rewrite    seq_S  : seq.
Hint Rewrite    seq_S_app : seq.
Hint Rewrite    inSigSeq  : seq.
Hint Rewrite    inSigSeqApp : seq.
Hint Rewrite  replicateLength  : length.


Lemma mapNthEq: forall (A:Type) (l:list A)(default:A), 
  map (fun position=>nth position l default) (seq 0 (List.length l)) = l.
Proof. 
  induction l using rev_ind.
    trivial.
    intros default; autorewrite with length; rewrite plus_comm;
      rewrite seq_S_app, map_app; simpl;
        rewrite map_assumption with 
          (g:=(fun position : nat => nth position l default)).
          rewrite app_nth2; try lia; rewrite minus_diag; simpl; rewrite IHl; trivial.
          intros a H; rewrite app_nth1; auto using inSeq0Lt.
Qed.
