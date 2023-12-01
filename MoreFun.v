From Coq Require Import Arith Lia.

(** Notation for function iteration *)

Notation "f ^^ n" := (Nat.iter n f) (at level 30, right associativity).

Lemma iter_S (f:nat->nat) n p : (f^^(S n)) p = (f^^n) (f p).
Proof.
 revert p.
 induction n as [|n IH]; intros; trivial. simpl. now rewrite <- IH.
Qed.

(** A few properties of strictly increasing [nat->nat] functions *)

Definition IncrFun f := forall p, f p < f (S p).

Lemma incr_strmono f : IncrFun f -> (forall p q, p < q -> f p < f q).
Proof.
 intros H. induction 1; auto. specialize (H m). lia.
Qed.

Lemma incr_mono f : IncrFun f -> (forall p q, p <= q -> f p <= f q).
Proof.
 intros H. induction 1; auto. specialize (H m). lia.
Qed.

Lemma incr_monoiff f : IncrFun f -> (forall p q, p < q <-> f p < f q).
Proof.
 intros H p q. split. apply (incr_strmono f H).
 destruct (Nat.lt_trichotomy p q) as [LT|[EQ|GT]]; trivial.
 - subst. lia.
 - apply (incr_strmono f H) in GT. lia.
Qed.

Lemma incr_function_bounds f : IncrFun f ->
  forall n, f 0 <= n -> exists p, f p <= n < f (S p).
Proof.
 intros Hf.
 induction n; intros H.
 - exists 0. split; trivial. specialize (Hf 0). lia.
 - destruct (Nat.le_gt_cases (f 0) n).
   + destruct IHn as (p & Hp); trivial.
     destruct (Nat.eq_dec (S n) (f (S p))) as [E|NE].
     * exists (S p). split. lia. rewrite E. apply Hf.
     * exists p. lia.
   + exists 0. split; try lia. replace (S n) with (f 0) by lia. apply Hf.
Qed.

Lemma incr_function_bounds' f : IncrFun f ->
  forall n, f 0 < n -> exists p, f p < n <= f (S p).
Proof.
 intros Hf n H0.
 destruct n. lia.
 destruct (incr_function_bounds f Hf n) as (p,Hp); try lia.
 exists p. lia.
Qed.

(** cumul : the sum of the n first values of a [nat->nat] function *)

Fixpoint cumul f n :=
  match n with
  | 0 => 0
  | S n => f n + cumul f n
  end.

Lemma cumul_ext f g n :
  (forall m, m < n -> f m = g m) ->
  cumul f n = cumul g n.
Proof.
 revert f g. induction n; simpl; auto.
 intros f g E. f_equal; auto.
Qed.

Lemma cumul_0 n : cumul (fun _ => 0) n = 0.
Proof.
 induction n; simpl; auto.
Qed.

Lemma cumul_add f g n :
 cumul (fun m => f m + g m) n = cumul f n + cumul g n.
Proof.
 induction n; simpl; auto. rewrite IHn; lia.
Qed.

Lemma cumul_test a n : a < n ->
 cumul (fun m : nat => if a =? m then 1 else 0) n = 1.
Proof.
 revert a. induction n; intros a Ha.
 - lia.
 - simpl. case Nat.eqb_spec.
   + intros ->. simpl. f_equal. erewrite cumul_ext. apply cumul_0.
     intros; simpl. case Nat.eqb_spec; lia.
   + intros. simpl. apply IHn; lia.
Qed.

Lemma cumul_mono f n m : n <= m -> cumul f n <= cumul f m.
Proof.
 induction 1; trivial. simpl. lia.
Qed.

(** [count f a n] is the number of [a] in [(f 0) .. (f (n-1))]. *)

Fixpoint count (f:nat->nat) a n :=
 match n with
 | 0 => 0
 | S n => count f a n + if f n =? a then 1 else 0
 end.

Lemma count_subid f a n : count f a n <= n.
Proof.
 induction n; simpl; trivial. case Nat.eqb_spec; lia.
Qed.

Lemma count_mono f a n m : n <= m -> count f a n <= count f a m.
Proof.
 induction 1; trivial. simpl. lia.
Qed.

Lemma count_0 f a n :
  count f a n = 0 <-> (forall p, p<n -> f p <> a).
Proof.
 split.
 - induction n; simpl; try lia. intros H p Hp.
   inversion_clear Hp.
   + intros E. rewrite E, Nat.eqb_refl in H. lia.
   + apply IHn; try lia.
 - induction n; simpl; trivial. intros H.
   rewrite IHn by (intros p Hp; apply H; lia).
   case Nat.eqb_spec; try lia. intros E. specialize (H n). lia.
Qed.

Lemma count_all f a n :
  (forall m, m<n -> f m = a) -> count f a n = n.
Proof.
 induction n. trivial. intros H.
 simpl. rewrite IHn by intuition. rewrite (H n), Nat.eqb_refl; lia.
Qed.

Lemma count_flat f a n m :
  n <= m -> count f a n = count f a m ->
  forall p, n<=p<m -> f p <> a.
Proof.
 induction 1. lia.
 simpl. intros E p (Hp,Hp'). apply (count_mono f a) in H.
 inversion_clear Hp'.
 - intros E'. rewrite E', Nat.eqb_refl in E. lia.
 - apply IHle; lia.
Qed.

(** Counting values equal or above [a] in [(f 0) .. (f (n-1))] *)

Fixpoint count_above f a n :=
 match n with
 | 0 => 0
 | S n => count_above f a n + if a <=? f n then 1 else 0
 end.

Lemma count_above_S f p n :
 count_above f p n = count f p n + count_above f (S p) n.
Proof.
 induction n; cbn -[Nat.leb]; auto. rewrite IHn.
 do 2 case Nat.leb_spec; case Nat.eqb_spec; try lia.
Qed.

(** Consider a function [f:nat->A] and value [a:A] taken infinitely
    often by [f]. A position function will enumerate the locations [i]
    where [f i = a]. Hence if [pos] is a position function for [f] and [a],
    then [pos p] will locate the p-th occurrence of [a] in the outputs of [f].
    Note : occurrences are counted from 0, as well as positions. *)

Record IsPosition {A} (f:nat->A)(a:A)(pos:nat->nat) :=
  { PosIncr : IncrFun pos;
    PosCorrect : forall p, f (pos p) = a;
    PosComplete : forall n, f n = a -> exists p, n = pos p }.

Lemma IsPosition_unique {A} f (a:A) pos pos' :
 IsPosition f a pos -> IsPosition f a pos' -> forall p, pos p = pos' p.
Proof.
 intros Hpos Hpos'.
 induction p as [p IH] using lt_wf_ind.
 destruct (Nat.lt_trichotomy (pos p) (pos' p)) as [LT|[E|LT]]; trivial.
 - assert (exists q, pos p = pos' q) by apply Hpos', Hpos.
   destruct H as (q, E). rewrite E in LT.
   apply (incr_monoiff pos') in LT. 2:apply Hpos'.
   rewrite <- (IH _ LT) in E.
   apply (incr_monoiff pos) in LT. 2:apply Hpos. lia.
 - assert (exists q, pos' p = pos q) by apply Hpos, Hpos'.
   destruct H as (q, E). rewrite E in LT.
   apply (incr_monoiff pos) in LT. 2:apply Hpos.
   rewrite (IH _ LT) in E.
   apply (incr_monoiff pos') in LT. 2:apply Hpos'. lia.
Qed.

Lemma IsPosition_count0 f a pos :
  IsPosition f a pos ->
  forall n, n <= pos 0 -> count f a n = 0.
Proof.
 intros (P0,P1,P2) n Hn. apply count_0. intros m Hm E.
 destruct (P2 _ E) as (p,Hp).
 assert (pos p < pos 0) by lia.
 generalize (incr_monoiff pos P0 p 0). lia.
Qed.

Lemma IsPosition_bound_count f a pos :
 IsPosition f a pos ->
 forall n p, pos p < n <= pos (S p) -> count f a n = S p.
Proof.
 intros (P0,P1,P2).
 induction n.
 - lia.
 - intros p Hp. simpl.
   destruct (Nat.eq_dec n (pos p)) as [EQ|NE].
   + rewrite EQ at 2. rewrite P1, Nat.eqb_refl, Nat.add_1_r. f_equal.
     destruct (Nat.eq_dec p 0).
     * subst p.
       apply (IsPosition_count0 f a pos); try lia. split; auto.
     * rewrite (IHn (p-1)); try lia.
       rewrite EQ. replace p with (S (p-1)) at 2 3 by lia.
       split. apply P0. easy.
   + assert (Hp2 : pos p < n <= pos (S p)) by lia.
     rewrite (IHn _ Hp2).
     case Nat.eqb_spec; intros E; try lia.
     exfalso.
     destruct (P2 _ E) as (p',Hp').
     rewrite Hp' in Hp2. destruct Hp2 as (Hp3,Hp4).
     apply (incr_monoiff _ P0) in Hp3.
     rewrite Nat.le_ngt, <- (incr_monoiff _ P0), <- Nat.le_ngt in Hp4.
     replace p' with (S p) in *; lia.
Qed.

Lemma IsPosition_count_anti f f' a a' pos pos' :
  IsPosition f a pos ->
  IsPosition f' a' pos' ->
  (forall p, pos p <= pos' p) ->
  forall n, count f' a' n <= count f a n.
Proof.
 intros (P0,P1,P2) (P0',P1',P2') LE.
 induction n as [n IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases n (pos' 0)) as [H0'|H0'].
 replace (count f' a' n) with 0. lia.
 { symmetry. apply count_0. intros p Hp E. destruct (P2' _ E) as (p',E').
   assert (pos' p' < pos' 0) by lia.
   generalize (incr_monoiff pos' P0' p' 0). lia. }
 assert (H0 : pos 0 < n) by (generalize (LE 0); lia).
 destruct (incr_function_bounds' pos P0 n H0) as (p & Hp).
 destruct (incr_function_bounds' pos' P0' n H0') as (p' & Hp').
 replace (count f a n) with (S p).
 2:{ symmetry. apply (IsPosition_bound_count f a pos); split; auto; lia. }
 replace (count f' a' n) with (S p').
 2:{ symmetry. apply (IsPosition_bound_count f' a' pos'); split; auto; lia. }
 apply -> Nat.succ_le_mono.
 assert (pos p' < n).
 { apply Nat.le_lt_trans with (pos' p'). apply LE. lia. }
 apply Nat.le_ngt. unfold lt. intros Hpp'.
 generalize (incr_mono pos P0 _ _ Hpp'). lia.
Qed.
