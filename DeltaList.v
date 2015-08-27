(** * DeltaList : lists of natural numbers with constrained differences *)

Require Import Arith Omega Wf_nat List.
Import ListNotations.
Set Implicit Arguments.

(** * Increasing lists *)

(** [Delta p l] means that consecutives values in the list [l]
    have differences of at least [p]. *)

Inductive Delta (p:nat) : list nat -> Prop :=
  | Dnil : Delta p []
  | Done n : Delta p [n]
  | Dcons n m l : m+p <= n -> Delta p (n::l) -> Delta p (m::n::l).
Hint Constructors Delta.

(** In particular:
    - [Delta 0 l] means that [l] is increasing
    - [Delta 1 l] means that [l] is stricly increasing
    - [Delta 2 l] implies in addition that no consecutive
      numbers can occur in [l].
*)

Lemma Delta_alt p x l :
 Delta p (x::l) <-> Delta p l /\ (forall y, In y l -> x+p <= y).
Proof.
 split.
 - revert x. induction l as [|a l IH].
   + intros x _. split. constructor. inversion 1.
   + intros x. inversion 1; subst. split; trivial.
     intros y [Hy|Hy]. now subst.
     apply (IH a) in Hy; auto. omega.
 - intros (H,H').
   destruct l; constructor; trivial. apply H'. now left.
Qed.

Lemma Delta_inv p x l : Delta p (x::l) -> Delta p l.
Proof.
 rewrite Delta_alt. intuition.
Qed.

Lemma Delta_more l p p' : p <= p' -> Delta p' l -> Delta p l.
Proof.
 induction 2; constructor; auto; omega.
Qed.

Lemma Delta_21 l : Delta 2 l -> Delta 1 l.
Proof.
 apply Delta_more; auto.
Qed.

Lemma Delta_nz p k l : 0<k -> Delta p (k::l) -> ~In 0 (k::l).
Proof.
 intros H H' [X|X]. omega.
 apply Delta_alt in H'. apply H' in X. omega.
Qed.
Hint Resolve Delta_21 Delta_inv Delta_nz.

Lemma Delta_low_hd p k k' l :
 k'<=k -> Delta p (k::l) -> Delta p (k'::l).
Proof.
 intros Hk. rewrite !Delta_alt. intros (H,H').
 split; trivial. intros y Hy. apply H' in Hy. omega.
Qed.

Lemma Delta_21_S x l : Delta 2 (x::l) -> Delta 1 (S x::l).
Proof.
  intros D. apply Delta_alt in D. destruct D as (D,D').
  apply Delta_alt; split; eauto.
  intros y Hy. apply D' in Hy. omega.
Qed.
Hint Resolve Delta_21_S.

Lemma Delta_map p p' f l :
  (forall x y, x+p <= y -> f x + p' <= f y) ->
  Delta p l -> Delta p' (map f l).
Proof.
 induction 2; constructor; auto.
Qed.

Lemma Delta_pred p l :
 ~In 0 l -> Delta p l -> Delta p (map pred l).
Proof.
 induction 2; simpl in *; constructor; intuition.
Qed.

(* begin hide *)
(* In stdlib's List.v since 8.5: *)
Lemma in_seq len start n :
  In n (seq start len) <-> start <= n < start+len.
Proof.
  revert start. induction len; simpl; intros.
  - rewrite <- plus_n_O. split;[easy|].
    intros (H,H'). apply (Lt.lt_irrefl _ (Lt.le_lt_trans _ _ _ H H')).
  - rewrite IHlen, <- plus_n_Sm; simpl; split.
    * intros [H|H]; subst; intuition auto with arith.
    * intros (H,H'). destruct (Lt.le_lt_or_eq _ _ H); intuition.
Qed.
(* end hide *)

Lemma Delta_seq n k : Delta 1 (seq n k).
Proof.
 revert n. induction k.
 - constructor.
 - intros. simpl. apply Delta_alt. split; auto.
   intros y Hy. rewrite in_seq in Hy. omega.
Qed.

Lemma Delta_app p x l l' :
  Delta p l -> Delta p (x::l') ->
  (forall y, In y l -> y <= x) -> Delta p (l++l').
Proof.
 induction l.
 - intros _ Hl' H. simpl. eauto.
 - intros Hl Hl' H. simpl. apply Delta_alt. split.
   + apply IHl; eauto.
     intros y Hy. apply H. now right.
   + intros y Hy. rewrite in_app_iff in Hy.
     destruct Hy as [Hy|Hy].
     * rewrite Delta_alt in Hl. now apply Hl.
     * assert (a <= x) by (apply H; now left).
       apply Delta_alt in Hl'. apply Hl' in Hy. omega.
Qed.

Lemma Delta_app_inv p l l' :
 Delta p (l++l') ->
 Delta p l /\ Delta p l' /\
 forall x x', In x l -> In x' l' -> x+p <= x'.
Proof.
 induction l; simpl.
 - split. constructor. intuition.
 - rewrite !Delta_alt. intuition.
   subst. apply H1. rewrite in_app_iff. now right.
Qed.

(** * Decreasing lists *)

(** [DeltaRev p l] is [Delta p (rev l)] :
    it considers differences in the reversed order,
    leading to decreasing lists *)

Inductive DeltaRev (p:nat) : list nat -> Prop :=
  | DRnil : DeltaRev p []
  | DRone n : DeltaRev p [n]
  | DRcons n m l : n+p <= m -> DeltaRev p (n::l) -> DeltaRev p (m::n::l).
Hint Constructors DeltaRev.

Lemma DeltaRev_alt p x l :
 DeltaRev p (x::l) <-> DeltaRev p l /\ (forall y, In y l -> y+p <= x).
Proof.
 split.
 - revert x. induction l as [|a l IH].
   + intros x _. split. constructor. inversion 1.
   + intros x. inversion 1; subst. split; trivial.
     intros y [Hy|Hy]. now subst.
     apply (IH a) in Hy; auto. omega.
 - intros (H,H').
   destruct l; constructor; trivial. apply H'. now left.
Qed.

Lemma DeltaRev_app p x l l' :
  DeltaRev p l -> DeltaRev p (x::l') ->
  (forall y, In y l -> x <= y) -> DeltaRev p (l++l').
Proof.
 induction l.
 - intros _ Hl' H. simpl. now rewrite DeltaRev_alt in Hl'.
 - intros Hl Hl' H. simpl. apply DeltaRev_alt. split.
   + apply IHl; auto.
     * now rewrite DeltaRev_alt in Hl.
     * intros y Hy. apply H. now right.
   + intros y Hy. rewrite in_app_iff in Hy.
     destruct Hy as [Hy|Hy].
     * rewrite DeltaRev_alt in Hl. now apply Hl.
     * assert (x <= a) by (apply H; now left).
       apply DeltaRev_alt in Hl'. apply Hl' in Hy. omega.
Qed.

Lemma DeltaRev_app_inv p l l' :
 DeltaRev p (l++l') ->
 DeltaRev p l /\ DeltaRev p l' /\
 forall x x', In x l -> In x' l' -> x'+p <= x.
Proof.
 induction l; simpl.
 - split. constructor. intuition.
 - rewrite !DeltaRev_alt. intuition.
   subst. apply H1. rewrite in_app_iff. now right.
Qed.

Lemma Delta_rev p l : Delta p (rev l) <-> DeltaRev p l.
Proof.
 split.
 - rewrite <- (rev_involutive l) at 2.
   set (l':=rev l); clearbody l'. clear l.
   induction 1.
   + constructor.
   + constructor.
   + simpl in *.
     apply DeltaRev_app with n; auto.
     intros y Hy. apply DeltaRev_app_inv in IHDelta.
     destruct IHDelta as (_ & _ & IH).
     specialize (IH y n).
     rewrite in_app_iff in Hy. simpl in *. intuition.
 - induction 1.
   + constructor.
   + constructor.
   + simpl in *.
     apply Delta_app with n; auto.
     intros y Hy. apply Delta_app_inv in IHDeltaRev.
     destruct IHDeltaRev as (_ & _ & IH).
     specialize (IH y n).
     rewrite in_app_iff in Hy. simpl in *. intuition.
Qed.

Lemma DeltaRev_rev p l : DeltaRev p (rev l) <-> Delta p l.
Proof.
 now rewrite <- Delta_rev, rev_involutive.
Qed.
