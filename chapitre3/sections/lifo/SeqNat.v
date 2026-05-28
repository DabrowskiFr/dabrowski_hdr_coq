From Stdlib Require Import Arith Lia NArith ZArith Sorting.Sorting.
From Stdlib Require Import Lists.List.

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
    intros n q r.
    apply seq_app.
  Qed.

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
    contradict mp1_0; rewrite Nat.add_comm; change (m+1) with (S m); simpl; discriminate.
    simpl. 
    set (q:=m-start).
    assert( m_qtart_q : m=start +q)  by (subst q; auto with arith).   
    replace ( m :: seq (S n) (length - ( q+ 1))) with ( seq (m) (S(length - (q+1)))) by (
      simpl; rewrite Nat.add_comm in *; change (1+m) with (S m) in *;  rewrite mp1_sn;   reflexivity).   
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
    intros i x H.
    apply in_seq in H.
    lia.
  Qed.

(** if [x] is in [seq i j] then [i<x] *)
  Lemma inSeqGt (i j x: nat): 
    List.In x (seq i j) -> i <= x.
  Proof.
    intro H.
    apply in_seq in H.
    lia.
  Qed.

  (** if [x] i in [seq start len] then [x<len+start] *)
  Lemma inSeqLt:
    forall (start len x: nat), 
      List.In x (seq start len) -> 
      x < start+len.
  Proof.
    intros start len x H.
    apply in_seq in H.
    lia.
  Qed.


  (** if [x] i in [seq start len] then [x>=start] *)
  Lemma inSeqLe : forall len n start, In n (seq start len) -> n >= start.
  Proof.
    induction len as [|len IHlen]; intros n start H.
    - simpl in H; contradiction.
    - simpl in H. destruct H as [H | H].
      + subst; lia.
      + specialize (IHlen n (S start) H); lia.
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
    induction m as [|m IH]; intros n s; destruct n; simpl; auto.
    rewrite IH.
    reflexivity.
  Qed.

  (** The list without the first [n] elements of [seq s m] is the
     sequence from [s+n] to [m-n] *)
  Lemma skipn_seq: 
    forall m n s, 
      skipn n (seq s m) = seq (s+n) (m-n).
  Proof.
    intros m n s.
    apply Stdlib.Lists.List.skipn_seq.
  Qed.

Lemma seqShiftGen:
        forall len start offset : nat, 
          List.map (fun n=>offset+n) (seq start len) = seq (offset+start) len.
      Proof.
        induction len; simpl.
          trivial.
          intros start offset; f_equal; rewrite IHlen; rewrite Nat.add_comm; 
            simpl; rewrite Nat.add_comm; trivial.
      Qed.

  Definition replicate (A:Type) (n:nat) (a:A) :=
    List.map (fun _ => a) (seq 0 n).
  
  Lemma replicateLength:
    forall (A:Type) (n:nat) (a:A),
      length (replicate n a) = n.
  Proof.
    intros.
    unfold replicate.
    rewrite length_map.
    apply length_seq.
  Qed.

  Lemma replicateProperty:
  forall (A:Type)(size:nat)(value:A),
    forall a:A, In a (replicate size value) -> value = a.
  Proof.
    intros A size value a H; induction size as [| size].
      contradict H.
      simpl in H; destruct H as [H | H].
        assumption.
        rewrite mapConstant with (l2:=seq 0 size) in H;
          unfold replicate in *; intuition.
          repeat (rewrite length_seq); trivial.
  Qed.

  Lemma replicateNatProperty:
    forall (size value m :nat), 
      fold_right plus m (replicate size value) = size * value + m.
  Proof.
    intros size value m; induction size.
      trivial.
      simpl; rewrite mapConstant with (l2:= seq 0 size); auto;
        repeat (rewrite length_seq); trivial. unfold replicate in IHsize; 
         rewrite IHsize; lia.
  Qed.

  Open Scope N_scope.

  Lemma replicateNProperty:
    forall (size value m : N), 
      fold_right N.add m (replicate (N.to_nat size) value) = size * value + m.
  Proof.
    intros size value m; induction size using N.peano_ind.
      trivial.
      unfold replicate; rewrite N2Nat.inj_succ; simpl;
        rewrite mapConstant with (l2:= seq 0 (N.to_nat size)); auto;
        repeat (rewrite length_seq); trivial. unfold replicate in IHsize.
         rewrite IHsize, Nmult_Sn_m; apply N.add_assoc.
  Qed.

  Close Scope N_scope.

  (**
    HdRel definition on seq
  *)
  Lemma seqHdRel : forall n m, HdRel le n (seq (S n) m).
  Proof.
  intros n m.
  destruct n.
   destruct (seq 1 m).
    constructor.
    constructor. lia.
   destruct m.
    constructor.
    simpl.
    constructor.
    lia.
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
    induction len as [|len IHlen]; intros start a H.
    - simpl; lia.
    - simpl.
      destruct (Nat.eq_dec a start) as [Heq | Hneq].
      + left; symmetry; exact Heq.
      + right; apply IHlen; lia.
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
  induction len ; intros. simpl. rewrite Nat.add_0_r ; reflexivity.
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
    intros default; autorewrite with length; rewrite Nat.add_comm;
      rewrite seq_S_app, map_app; simpl;
        rewrite map_assumption with 
          (g:=(fun position : nat => nth position l default)).
          rewrite app_nth2; try lia; rewrite Nat.sub_diag; simpl; rewrite IHl; trivial.
          intros a H; rewrite app_nth1; auto using inSeq0Lt.
Qed.
