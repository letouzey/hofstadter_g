From Coq Require Import Arith Lia.

(** Notation for function iteration *)

Notation "f ^^ n" := (Nat.iter n f) (at level 30, right associativity).

Lemma iter_S {A} (f:A->A) n p : (f^^(S n)) p = (f^^n) (f p).
Proof.
 revert p.
 induction n as [|n IH]; intros; trivial. simpl. now rewrite <- IH.
Qed.

Lemma iter_add {A} (f:A->A) n m p : (f^^(n+m)) p = (f^^n) ((f^^m) p).
Proof.
 induction n as [|n IH]; simpl; intros; now rewrite ?IH.
Qed.

(** A few properties of strictly increasing [nat->nat] functions *)

Definition IncrFun f := forall p, f p < f (S p).

Lemma incr_strmono f : IncrFun f -> forall p q, p < q -> f p < f q.
Proof.
 intros H. induction 1; auto. specialize (H m). lia.
Qed.

Lemma incr_mono f : IncrFun f -> forall p q, p <= q -> f p <= f q.
Proof.
 intros H. induction 1; auto. specialize (H m). lia.
Qed.

Lemma incr_strmono_iff f : IncrFun f -> forall p q, p < q <-> f p < f q.
Proof.
 intros H p q. split. apply (incr_strmono f H).
 destruct (Nat.lt_trichotomy p q) as [LT|[EQ|GT]]; trivial.
 - subst. lia.
 - apply (incr_strmono f H) in GT. lia.
Qed.

Lemma incr_mono_iff f : IncrFun f -> forall p q, p <= q <-> f p <= f q.
Proof.
 intros H p q. split. apply (incr_mono f H).
 destruct (Nat.lt_trichotomy p q) as [LT|[EQ|GT]]; try lia.
 apply (incr_strmono f H) in GT. lia.
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

Lemma cumul_mono f n m : n <= m -> cumul f n <= cumul f m.
Proof.
 induction 1; trivial. simpl. lia.
Qed.

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

Lemma cumul_cst c n : cumul (fun _ => c) n = c*n.
Proof.
 induction n; simpl; rewrite ?IHn; lia.
Qed.

Lemma cumul_add f g n :
 cumul (fun m => f m + g m) n = cumul f n + cumul g n.
Proof.
 induction n; simpl; auto. rewrite IHn; lia.
Qed.

Lemma cumul_eqb a n : a < n ->
 cumul (fun m : nat => if a =? m then 1 else 0) n = 1.
Proof.
 revert a. induction n; intros a Ha.
 - lia.
 - simpl. case Nat.eqb_spec.
   + intros ->. simpl. f_equal. erewrite cumul_ext. apply cumul_0.
     intros; simpl. case Nat.eqb_spec; lia.
   + intros. simpl. apply IHn; lia.
Qed.

Lemma cumul_ltb n p :
  cumul (fun x => if x <? p then 1 else 0) n = Nat.min p n.
Proof.
 induction n; simpl; rewrite ?IHn; try lia. case Nat.ltb_spec; lia.
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
