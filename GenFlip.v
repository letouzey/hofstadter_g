(** * FlipG : Hofstadter's flipped G tree *)

Require Import MoreFun DeltaList GenFib GenG.
Set Implicit Arguments.

(** See first the file [GenG] for the study of:

     - [fk (S n) + fk^k (n) = S n]
     - [fk 0 = 0]

   and the associated tree where nodes are labeled breadth-first
   from left to right.

   Now, question by Hofstadter: what if we still label the nodes
   from right to left, but for the mirror tree ?
   What is the algebraic definition of the "parent" function
   for this flipped tree ?

   References:
    - Hofstadter's book: Goedel, Escher, Bach, page 137.
    - Sequence A123070 on the Online Encyclopedia of Integer Sequences
      #<a href="http://oeis.org/A123070">#http://oeis.org/A123070#</a>#
*)

(*=============================================================*)

(** * The [flip] function *)

(** If we label the node from right to left, the effect
   on node numbers is the [flip] function below.
   The idea is to map a row [ [1+Ak (p-1);...;Ak p] ]
   to the flipped row [ [Ak p;...;1+Ak (p-1)] ].
*)

Definition flip k n :=
  if n <=? 1 then n
  else
    let d := depth k n in
    1 + A k (d-1) + A k d - n.

Section Knonzero.
Variable k:nat.
Hypothesis K:k<>0.

Lemma flip_low n : n <= 1 -> flip k n = n.
Proof.
 unfold flip.
 case Nat.leb_spec; trivial.
 lia.
Qed.

Lemma flip_0 : flip k 0 = 0.
Proof.
 apply flip_low; auto.
Qed.

Lemma flip_1 : flip k 1 = 1.
Proof.
 apply flip_low; auto.
Qed.

Lemma flip_depth n : depth k (flip k n) = depth k n.
Proof.
 unfold flip.
 case Nat.leb_spec; trivial.
 intros.
 assert (depth k n <> 0) by (rewrite depth_is_0; lia).
 apply depth_carac; trivial.
 set (p := depth k n) in *.
 assert (S (A k (p-1)) <= n <= A k p)
  by now apply depth_carac.
 lia.
Qed.

Lemma flip_eqn0 n : depth k n <> 0 ->
 flip k n = 1 + A k (depth k n - 1) + A k (depth k n) - n.
Proof.
 intros.
 rewrite depth_is_0 in *.
 unfold flip.
 case Nat.leb_spec; lia.
Qed.

Lemma flip_unfold n a b : depth k n <> 0 ->
 a + 1 + A k (depth k n - 1) + A k (depth k n) = b + n ->
 a + flip k n = b.
Proof.
 intros N E.
 destruct (@depth_carac k (depth k n) n K N) as (H,_).
 rewrite flip_eqn0; trivial. lia.
Qed.

Lemma flip_eqn p n : p<>0 -> 1 <= n <= A k (p-k) ->
 flip k (A k (p-1) + n) = S (A k p) - n.
Proof.
 intros Hp Hn.
 unfold flip.
 case Nat.leb_spec.
 - generalize (@A_nz k (p-1)); lia.
 - intros H.
   replace (depth k (A k (p-1) + n)) with p.
   + lia.
   + symmetry. apply depth_carac; trivial.
     rewrite (@A_sum k p); lia.
Qed.

(** Two special cases : leftmost and rightmost node at a given depth *)

Lemma flip_SA p : flip k (S (A k p)) = A k (S p).
Proof.
 rewrite <- Nat.add_1_r.
 replace p with (S p - 1) at 1 by lia.
 rewrite (@flip_eqn (S p)); auto using A_nz. lia.
Qed.

Lemma flip_A p : p<>0 -> flip k (A k p) = S (A k (p-1)).
Proof.
 intros Hp.
 assert (E := @A_sum k p K Hp).
 rewrite E.
 rewrite flip_eqn; auto using A_nz. lia.
Qed.

Lemma flip_init n : n <= k+1 -> flip k n = n.
Proof.
 intros Hn.
 destruct n as [|[|n]].
 - apply flip_0.
 - apply flip_1.
 - rewrite <- (@A_base k (S n)) at 1 by lia.
   rewrite flip_A by lia. simpl. rewrite Nat.sub_0_r. f_equal.
   apply A_base. lia.
Qed.

(** flip is involutive (and hence a bijection) *)

Lemma flip_flip n : flip k (flip k n) = n.
Proof.
 unfold flip at 2.
 case Nat.leb_spec.
 - apply flip_low.
 - intros Hn.
   set (p := depth k n).
   assert (p<>0).
   { unfold p. rewrite depth_is_0. lia. }
   assert (Hn' : S (A k (p-1)) <= n <= A k p).
   { apply depth_carac; auto. }
   rewrite (Nat.add_comm 1).
   rewrite <- Nat.add_assoc.
   rewrite <- Nat.add_sub_assoc by lia.
   rewrite flip_eqn; auto. lia.
   split. lia.
   rewrite (@A_sum k p) by trivial. lia.
Qed.

Lemma flip_eq n m : flip k n = flip k m <-> n = m.
Proof.
 split; intros H.
 - rewrite <- (flip_flip n), <- (flip_flip m). now f_equal.
 - now subst.
Qed.

Lemma flip_swap n m : flip k n = m <-> n = flip k m.
Proof.
 rewrite <- (flip_flip m) at 1. now apply flip_eq.
Qed.

Lemma flip_le_1 n : n <= 1 <-> flip k n <= 1.
Proof.
 split; intros.
 - assert (EQ : n = 0 \/ n = 1) by lia.
   destruct EQ as [-> | ->]; compute; auto.
 - assert (EQ : flip k n = 0 \/ flip k n = 1) by lia.
   rewrite !flip_swap in EQ; trivial. compute in EQ. lia.
Qed.

Lemma flip_gt_1 n : 1 < n <-> 1 < flip k n.
Proof.
 generalize (flip_le_1 n). lia.
Qed.

(** flip and neighbors *)

Lemma flip_S n : 1<n -> depth k (S n) = depth k n ->
  flip k (S n) = flip k n - 1.
Proof.
 intros Hn EQ.
 assert (depth k n <> 0) by (rewrite depth_is_0; lia).
 rewrite !flip_eqn0, EQ; lia.
Qed.

Lemma flip_pred n : 1<n -> depth k (n-1) = depth k n ->
  flip k (n-1) = S (flip k n).
Proof.
 intros Hn EQ.
 assert (depth k n <> 0) by (rewrite depth_is_0; lia).
 rewrite !flip_eqn0, EQ; try lia.
 assert (n <= A k (depth k n)) by (apply depth_carac; auto).
 lia.
Qed.


(*=============================================================*)

(** * The [ff] function corresponding to the flipped [f] tree *)

Definition ff n := flip k (f k (flip k n)).
Notation ffs p := (ff ^^p).

(* Compute take 20 (ff 2). *)

Lemma ff_0 : ff 0 = 0.
Proof.
 reflexivity.
Qed.

Lemma ff_1 : ff 1 = 1.
Proof.
 unfold ff. now rewrite flip_1, f_k_1, flip_1.
Qed.

Lemma ff_depth n : depth k (ff n) = depth k n - 1.
Proof.
 unfold ff. now rewrite flip_depth, f_depth, flip_depth.
Qed.

Lemma ff_A p : ff (A k p) = A k (p-1).
Proof.
 destruct p as [|p].
 simpl.
 - unfold ff. rewrite (@flip_low 1), f_k_1; auto.
 - unfold ff.
   rewrite flip_A by auto.
   simpl. rewrite Nat.sub_0_r.
   destruct p as [|p].
   + simpl. rewrite f_init. simpl. apply flip_low; auto. lia.
   + rewrite f_SA; auto. simpl Nat.sub. rewrite Nat.sub_0_r.
     apply flip_SA.
Qed.

Lemma ff_SA p : ff (S (A k (S p))) = S (A k p).
Proof.
 unfold ff.
 rewrite flip_SA.
 rewrite f_A; trivial.
 rewrite flip_A. f_equal. f_equal. lia. lia.
Qed.

Lemma ff_SA' p : p<>0 -> ff (S (A k p)) = S (A k (p-1)).
Proof.
 destruct p.
 - intuition.
 - intros _. rewrite ff_SA. f_equal. f_equal. lia.
Qed.

Lemma ffs_A m p : ffs m (A k p) = A k (p-m).
Proof.
 revert p.
 induction m as [|m IH]; intros p; simpl.
 - now rewrite Nat.sub_0_r.
 - rewrite IH, ff_A. f_equal. lia.
Qed.

Lemma ffs_SA m p : m <= p -> ffs m (S (A k p)) = S (A k (p-m)).
Proof.
 revert p.
 induction m as [|m IH]; intros p H; simpl.
 - now rewrite Nat.sub_0_r.
 - rewrite IH, ff_SA' by lia. f_equal. f_equal. lia.
Qed.

Lemma ff_init p : 2 <= p <= k+2 -> ff p = p-1.
Proof.
 intros (H,H').
 apply Nat.lt_eq_cases in H'. destruct H' as [H'| ->].
 - unfold ff. rewrite (@flip_init p) by lia.
   rewrite f_init by lia.
   apply flip_init. lia.
 - replace (k+2) with (S (S k)) by lia.
   rewrite <- (@A_base k k) at 1 by lia.
   replace k with (S (k-1)) at 2 by lia.
   rewrite ff_SA. rewrite A_base; lia.
Qed.

Lemma ff_step n : ff (S n) = ff n \/ ff (S n) = S (ff n).
Proof.
 destruct (le_lt_dec n 1) as [LE|LT].
 - assert (EQ : n = 0 \/ n = 1) by lia.
   destruct EQ as [-> | ->].
   + rewrite ff_0, ff_1; auto.
   + rewrite ff_init, ff_1; lia.
 - set (p := depth k n).
   assert (p<>0) by (unfold p; rewrite depth_is_0; lia).
   assert (S (A k (p-1)) <= n <= A k p).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (A k p)) as [EQ|NE].
   + rewrite EQ. rewrite ff_SA', ff_A; auto.
   + assert (depth k (S n) = p). { apply depth_carac; lia. }
     assert (depth k (flip k (S n)) = p). { rewrite flip_depth; auto. }
     assert (1 < flip k n). { now apply (flip_gt_1 n). }
     unfold ff.
     rewrite flip_S in *; auto.
     destruct (eq_nat_dec (f k (flip k n - 1)) (f k (flip k n))) as [EQ|NE'].
     * left; f_equal; trivial.
     * right.
       rewrite f_prev in NE' by lia.
       rewrite NE'.
       apply flip_pred.
       { unfold lt.
         change 2 with (3-1).
         rewrite <- (@f_init k 3) by lia.
         apply f_mono.
         assert (flip k n <> 2).
         { intros EQ. rewrite EQ in *.
           simpl in NE'.
           rewrite f_k_1, f_init in NE'; lia. }
         lia. }
       { rewrite <- NE'. rewrite !f_depth by easy. rewrite flip_depth.
         unfold p in *. lia. }
Qed.

Lemma ff_mono_S n : ff n <= ff (S n).
Proof.
 generalize (ff_step n). lia.
Qed.

Lemma ff_mono n m : n<=m -> ff n <= ff m.
Proof.
induction 1.
- trivial.
- transitivity (ff m); auto using ff_mono_S.
Qed.

Lemma ff_lipschitz n m : ff m - ff n <= m - n.
Proof.
destruct (le_ge_dec n m) as [H|H].
- induction H; try generalize (ff_step m); lia.
- generalize (ff_mono H). lia.
Qed.

Lemma ff_nonzero n : 0 < n -> 0 < ff n.
Proof.
 unfold lt. intros. rewrite <- ff_1. now apply ff_mono.
Qed.

Lemma ff_0_inv n : ff n = 0 -> n = 0.
Proof.
destruct n; trivial.
assert (0 < ff (S n)) by (apply ff_nonzero; auto with arith).
lia.
Qed.

Lemma ff_nz n : n <> 0 -> ff n <> 0.
Proof.
intros H. contradict H. now apply ff_0_inv.
Qed.

Lemma ff_fix n : ff n = n <-> n <= 1.
Proof.
 unfold ff.
 now rewrite flip_le_1, <- f_fix, flip_swap.
Qed.

Lemma ff_le n : ff n <= n.
Proof.
 generalize (ff_lipschitz 0 n). rewrite ff_0. lia.
Qed.

Lemma ff_lt n : 1<n -> ff n < n.
Proof.
 generalize (ff_le n) (ff_fix n); lia.
Qed.

Lemma ff_onto a : exists n, ff n = a.
Proof.
 unfold ff. destruct (@f_onto k (flip k a) K) as (x,H).
 exists (flip k x). now rewrite flip_swap, flip_flip.
Qed.

Lemma ff_nonflat n : ff (S n) = ff n -> ff (S (S n)) = S (ff n).
Proof.
 intros H.
 destruct (le_lt_dec n 1) as [Hn|Hn].
 - assert (EQ : n = 0 \/ n = 1) by lia.
   destruct EQ as [-> | ->].
   + rewrite ff_1, ff_0 in *. rewrite ff_init; lia.
   + rewrite ff_1 in *. rewrite !ff_init; lia.
 - destruct (ff_step (S n)) as [H'|H']; [|lia].
   exfalso.
   set (p := depth k n).
   assert (Hp : p<>0) by (unfold p; rewrite depth_is_0; lia).
   assert (Hnp : S (A k (p-1)) <= n <= A k p).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (A k p)) as [EQ|NE].
   + rewrite EQ in H. rewrite ff_A, ff_SA' in H; lia.
   + destruct (eq_nat_dec (S n) (A k p)) as [EQ|NE'].
     * rewrite EQ in H'. rewrite ff_A, ff_SA' in H'; lia.
     * revert H'. rewrite H; clear H. unfold ff. rewrite flip_eq.
       assert (depth k (S n) = p). { apply depth_carac; lia. }
       assert (depth k (flip k (S n)) = p). { rewrite flip_depth; auto. }
       assert (depth k (S (S n)) = p). { apply depth_carac; lia. }
       assert (depth k (flip k (S (S n))) = p). { rewrite flip_depth; auto. }
       rewrite flip_S by lia.
       rewrite flip_S by (unfold p in H; lia).
       assert (HH : forall m, 1<m -> f k (m-1-1) <> f k m).
       { intros.
         generalize (@f_max_two_antecedents k (m-1-1) m).
         lia. }
       apply HH. now rewrite <- flip_gt_1.
Qed.

Lemma ff_max_two_antecedents n m :
 ff n = ff m -> n < m -> m = S n.
Proof.
 intros H LT.
 unfold lt in LT.
 assert (LE := ff_mono LT).
 rewrite <- H in LE.
 destruct (ff_step n) as [EQ|EQ]; [|lia].
 apply ff_nonflat in EQ.
 destruct (le_lt_dec m (S n)) as [LE'|LT']; [lia|].
 unfold lt in LT'. apply ff_mono in LT'. lia.
Qed.

Lemma ff_inv n m : ff n = ff m -> n = m \/ n = S m \/ m = S n.
Proof.
 intros H.
 destruct (lt_eq_lt_dec n m) as [[LT|EQ]|LT]; auto.
 - apply ff_max_two_antecedents in LT; auto.
 - apply ff_max_two_antecedents in LT; auto.
Qed.

Lemma ffs_flip p n :
  ffs p n = flip k (fs k p (flip k n)).
Proof.
 revert n.
 induction p; simpl; intros.
 - symmetry. apply flip_flip.
 - rewrite IHp. unfold ff. now rewrite flip_flip.
Qed.

Lemma ff_eqn n : k+1 < n -> ff n + ffs (k-1) (S (ff (n-1))) = S n.
Proof.
 intros Hn.
 set (p := depth k n).
 assert (k+1<=p).
 { unfold p.
   replace (k+1) with (k+2-1) by lia.
   replace (k+2-1) with (depth k (k+2)).
   apply depth_mono; lia.
   now apply depth_init. }
 assert (LE : S (A k (p-1)) <= n <= A k p).
 { apply depth_carac; lia. }
 destruct (eq_nat_dec (S (A k (p-1))) n) as [EQ|NE].
 - (* n = S (fib (p-1)) *)
   clear LE.
   replace (n-1) with (A k (p-1)) by lia.
   rewrite ff_A.
   rewrite ffs_SA by lia.
   rewrite <- EQ. clear EQ.
   rewrite ff_SA' by lia.
   rewrite Nat.add_succ_r. simpl. f_equal. f_equal.
   rewrite (@A_sum k (p-1)) by lia. f_equal. f_equal. lia.
 - (* n > S (fib (p-1)) *)
   assert (Hp : depth k (n-1) = p).
   { apply depth_carac; lia. }
   assert (Hp' : depth k (ff (n-1)) = p-1).
   { now rewrite ff_depth, Hp. }
   assert (LE' : S (A k (p-1-1)) <= ff (n-1) <= A k (p-1)).
   { apply depth_carac; auto. lia. }
   destruct (eq_nat_dec (ff (n-1)) (A k (p-1))) as [EQ|NE'].
   + (* ffq(n-1) = A k (p-1) *)
     rewrite EQ.
     rewrite ffs_SA by lia.
     assert (EQ' : ff n = A k (p-1)).
     { destruct (ff_step (n-1)) as [EQ'|EQ'];
       replace (S (n-1)) with n in EQ'; try lia.
       rewrite EQ in EQ'.
       assert (H' : depth k (ff n) = p) by (apply depth_carac; lia).
       rewrite ff_depth in H'. unfold p in *. lia. }
     rewrite EQ'.
     rewrite Nat.add_succ_r. rewrite <- A_S.
     f_equal.
     replace (S (p-1)) with p by lia.
     assert (EQ'' : ff (n-1) = ff (A k p)) by now rewrite EQ, ff_A.
     apply ff_max_two_antecedents in EQ''; lia.
   + (* ffq(n-1) <> A k (p-1) *)
     assert (Hp'' : depth k (S (ff (n-1))) = p-1).
     { apply depth_carac; lia. }
     rewrite ffs_flip.
     apply flip_unfold;
      rewrite !fs_depth, !flip_depth, Hp''; try lia.
     assert (LT : 1 < ff (n-1)).
     { unfold lt. change 2 with (3 - 1).
       rewrite <- (@ff_init 3) by lia.
       apply ff_mono. lia. }
     rewrite flip_S by lia.
     unfold ff at 2. rewrite flip_flip.
     rewrite flip_pred; try (unfold p in Hp; lia).
     replace (fs k (k-1) (f k (S (flip k n)) - 1))
       with (flip k n - f k (flip k n))
     by (generalize (@f_alt_eqn k (flip k n) K); lia).
     rewrite Nat.add_sub_assoc by apply f_le.
     symmetry. apply Nat.add_sub_eq_r.
     rewrite <- (flip_flip (f k (flip k n))).
     fold (ff n).
     apply flip_unfold.
     { rewrite ?ff_depth; unfold p in H; lia. }
     rewrite ff_depth.
     change (depth k n) with p.
     replace (S n + flip k n + ff n) with
        (S n + ff n + flip k n) by lia.
     symmetry.
     apply flip_unfold.
     { unfold p in H; lia. }
     change (depth k n) with p.
     clear LT Hp'' NE' LE' Hp Hp'.
     rewrite (@A_sum k p) by lia.
     rewrite (@A_sum k (p-1)) at 1 by lia.
     replace (p-1-(k-1)-1) with (p-1-k) by lia.
     replace (p-1-(k-1)) with (p-k) by lia.
     lia.
Qed.

(** This equation, along with initial values up to [n=k+1],
    characterizes [ff] entirely. It can hence be used to
    give an algebraic recursive definition to [ff], answering
    the Hofstader's question. *)

Lemma ff_eqn_unique h :
  h 0 = 0 ->
  h 1 = 1 ->
  (forall n, 2<= n <= k+1 -> h n = n-1) ->
  (forall n, k+1 < n -> h n + (h^^(k-1)) (S (h (n-1))) = S n) ->
  forall n, h n = ff n.
Proof.
 intros H0 H1 Hbase Heqn.
 induction n as [n IH] using lt_wf_rec.
 destruct (le_lt_dec n (k+1)) as [Hn|Hn].
 - destruct n as [|[|n]].
   + now rewrite ff_0.
   + now rewrite ff_1.
   + rewrite ff_init, Hbase; lia.
 - assert (E := ff_eqn Hn).
   specialize (Heqn n Hn).
   assert (E' : forall p m, m < n -> (h^^p) m = ffs p m).
   { clear - IH K.
     induction p; auto.
     intros.
     rewrite !iter_S.
     rewrite IH; auto.
     apply IHp; auto.
     generalize (ff_le m); lia. }
   assert (E'' : h (n-1) = ff (n-1)) by (apply IH; lia).
   rewrite E'' in *.
   replace ((h ^^ (k-1)) (S (ff (n - 1)))) with
     (ffs (k-1) (S (ff (n - 1)))) in Heqn.
   lia.
   symmetry. apply E'.
   generalize (@ff_lt (n-1)). lia.
Qed.

End Knonzero.
