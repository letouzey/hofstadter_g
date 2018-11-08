(** * FlipG : Hofstadter's flipped G tree *)

Require Import Arith Omega Wf_nat List Program Program.Wf NPeano.
Require Import DeltaList FunG GenFib GenG.
Set Implicit Arguments.

(** See first the file [FunG] for the study of:

     - [fk (S n) + fk^(S k) (n) = S n]
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

Lemma flip_low k n : n <= 1 -> flip k n = n.
Proof.
 unfold flip.
 case Nat.leb_spec; trivial.
 omega.
Qed.

Lemma flip_0 k : flip k 0 = 0.
Proof.
 apply flip_low; auto.
Qed.

Lemma flip_1 k : flip k 1 = 1.
Proof.
 apply flip_low; auto.
Qed.

Lemma flip_depth k n : depth k (flip k n) = depth k n.
Proof.
 unfold flip.
 case Nat.leb_spec; trivial.
 intros.
 assert (depth k n <> 0) by (rewrite depth_is_0; omega).
 apply depth_carac; trivial.
 set (p := depth k n) in *.
 assert (S (A k (p-1)) <= n <= A k p)
  by now apply depth_carac.
 omega.
Qed.

Lemma flip_eqn0 k n : depth k n <> 0 ->
 flip k n = 1 + A k (depth k n - 1) + A k (depth k n) - n.
Proof.
 intros.
 rewrite depth_is_0 in *.
 unfold flip.
 case Nat.leb_spec; omega.
Qed.

Lemma flip_unfold k n a b : depth k n <> 0 ->
 a + 1 + A k (depth k n - 1) + A k (depth k n) = b + n ->
 a + flip k n = b.
Proof.
 intros.
 generalize (@depth_carac k _ n H).
 rewrite depth_is_0 in *.
 unfold flip.
 case Nat.leb_spec; omega.
Qed.

Lemma flip_eqn k p n : p<>0 -> 1 <= n <= A k (p-S k) ->
 flip k (A k (p-1) + n) = S (A k p) - n.
Proof.
 intros Hp Hn.
 unfold flip.
 case Nat.leb_spec.
 - generalize (@A_nz k (p-1)); omega.
 - intros H.
   replace (depth k (A k (p-1) + n)) with p.
   + omega.
   + symmetry. apply depth_carac; auto.
     rewrite (@A_sum k p); omega.
Qed.

(** Two special cases : leftmost and rightmost node at a given depth *)

Lemma flip_SA k p : flip k (S (A k p)) = A k (S p).
Proof.
 rewrite <- Nat.add_1_r.
 replace p with (S p - 1) at 1 by omega.
 rewrite (@flip_eqn k (S p)); auto using A_nz. omega.
Qed.

Lemma flip_A k p : p<>0 -> flip k (A k p) = S (A k (p-1)).
Proof.
 intros Hp.
 assert (E := @A_sum k p Hp).
 rewrite E.
 rewrite flip_eqn; auto using A_nz. omega.
Qed.

Lemma flip_init k n : n <= k+2 -> flip k n = n.
Proof.
 intros Hn.
 destruct n as [|[|n]].
 - apply flip_0.
 - apply flip_1.
 - rewrite <- (@A_base k (S n)) at 1 by omega.
   rewrite flip_A by omega. simpl. rewrite Nat.sub_0_r. f_equal.
   apply A_base. omega.
Qed.

(** flip is involutive (and hence a bijection) *)

Lemma flip_flip k n : flip k (flip k n) = n.
Proof.
 unfold flip at 2.
 case Nat.leb_spec.
 - apply flip_low.
 - intros Hn.
   set (p := depth k n).
   assert (p<>0).
   { unfold p. rewrite depth_is_0. omega. }
   assert (Hn' : S (A k (p-1)) <= n <= A k p).
   { apply depth_carac; auto. }
   rewrite (Nat.add_comm 1).
   rewrite <- Nat.add_assoc.
   rewrite <- Nat.add_sub_assoc by omega.
   rewrite flip_eqn; auto. omega.
   split. omega.
   rewrite (@A_sum k p) by trivial. omega.
Qed.

Lemma flip_eq k n m : flip k n = flip k m <-> n = m.
Proof.
 split; intros H.
 - rewrite <- (flip_flip k n), <- (flip_flip k m). now f_equal.
 - now subst.
Qed.

Lemma flip_swap k n m : flip k n = m <-> n = flip k m.
Proof.
 rewrite <- (flip_flip k m) at 1. apply flip_eq.
Qed.

Lemma flip_le_1 k n : n <= 1 <-> flip k n <= 1.
Proof.
 split; intros.
 - assert (EQ : n = 0 \/ n = 1) by omega.
   destruct EQ as [-> | ->]; compute; auto.
 - assert (EQ : flip k n = 0 \/ flip k n = 1) by omega.
   rewrite !flip_swap in EQ. compute in EQ. omega.
Qed.

Lemma flip_gt_1 k n : 1 < n <-> 1 < flip k n.
Proof.
 generalize (flip_le_1 k n). omega.
Qed.

(** flip and neighbors *)

Lemma flip_S k n : 1<n -> depth k (S n) = depth k n ->
  flip k (S n) = flip k n - 1.
Proof.
 intros Hn EQ.
 assert (depth k n <> 0) by (rewrite depth_is_0; omega).
 rewrite !flip_eqn0, EQ; omega.
Qed.

Lemma flip_pred k n : 1<n -> depth k (n-1) = depth k n ->
  flip k (n-1) = S (flip k n).
Proof.
 intros Hn EQ.
 assert (depth k n <> 0) by (rewrite depth_is_0; omega).
 rewrite !flip_eqn0, EQ; try omega.
 assert (n <= A k (depth k n)) by (apply depth_carac; auto).
 omega.
Qed.


(*=============================================================*)

(** * The [ff] function corresponding to the flipped [f] tree *)

Definition ff k n := flip k (f k (flip k n)).

(* Compute map (ff 2) (seq 0 20). *)

Lemma ff_k_0 k : ff k 0 = 0.
Proof.
 reflexivity.
Qed.

Lemma ff_k_1 k : ff k 1 = 1.
Proof.
 unfold ff. now rewrite flip_1, f_k_1, flip_1.
Qed.

Lemma ff_depth k n : depth k (ff k n) = depth k n - 1.
Proof.
 unfold ff. now rewrite flip_depth, f_depth, flip_depth.
Qed.

Lemma ff_A k p : ff k (A k p) = A k (p-1).
Proof.
 destruct p as [|p].
 simpl.
 - unfold ff. rewrite (@flip_low k 1), f_k_1; auto.
 - unfold ff.
   rewrite flip_A by auto.
   simpl. rewrite Nat.sub_0_r.
   destruct p as [|p].
   + simpl. rewrite f_init. simpl. apply flip_low; auto. omega.
   + rewrite f_SA; auto. simpl Nat.sub. rewrite Nat.sub_0_r.
     apply flip_SA.
Qed.

Lemma ff_SA k p : ff k (S (A k (S p))) = S (A k p).
Proof.
 unfold ff.
 rewrite flip_SA.
 rewrite f_A.
 rewrite flip_A. f_equal. f_equal. omega. omega.
Qed.

Lemma ff_SA' k p : p<>0 -> ff k (S (A k p)) = S (A k (p-1)).
Proof.
 destruct p.
 - intuition.
 - intros _. rewrite ff_SA. f_equal. f_equal. omega.
Qed.

Lemma ffs_A k m p : (ff k^^m) (A k p) = A k (p-m).
Proof.
 revert p.
 induction m as [|m IH]; intros p; simpl.
 - now rewrite Nat.sub_0_r.
 - rewrite IH, ff_A. f_equal. omega.
Qed.

Lemma ffs_SA k m p : m <= p -> (ff k^^m) (S (A k p)) = S (A k (p-m)).
Proof.
 revert p.
 induction m as [|m IH]; intros p H; simpl.
 - now rewrite Nat.sub_0_r.
 - rewrite IH, ff_SA' by omega. f_equal. f_equal. omega.
Qed.

Lemma ff_init k p : 2 <= p <= k+3 -> ff k p = p-1.
Proof.
 intros (H,H').
 apply Nat.lt_eq_cases in H'. destruct H' as [H'| ->].
 - unfold ff. rewrite (@flip_init k p) by omega.
   rewrite f_init by omega.
   apply flip_init. omega.
 - replace (k+3) with (S (S (S k))) by omega.
   rewrite <- (@A_base k (S k)) at 1 by omega.
   rewrite ff_SA. rewrite A_base; omega.
Qed.

Lemma ff_step k n : ff k (S n) = ff k n \/ ff k (S n) = S (ff k n).
Proof.
 destruct (le_lt_dec n 1) as [LE|LT].
 - assert (EQ : n = 0 \/ n = 1) by omega.
   destruct EQ as [-> | ->].
   + rewrite ff_k_0, ff_k_1; auto.
   + rewrite ff_init, ff_k_1; omega.
 - set (p := depth k n).
   assert (p<>0) by (unfold p; rewrite depth_is_0; omega).
   assert (S (A k (p-1)) <= n <= A k p).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (A k p)) as [EQ|NE].
   + rewrite EQ. rewrite ff_SA', ff_A; auto.
   + assert (depth k (S n) = p). { apply depth_carac; omega. }
     assert (depth k (flip k (S n)) = p). { rewrite flip_depth; auto. }
     assert (1 < flip k n). { now apply (flip_gt_1 k n). }
     unfold ff.
     rewrite flip_S in *; auto.
     destruct (eq_nat_dec (f k (flip k n - 1)) (f k (flip k n))) as [EQ|NE'].
     * left; f_equal; trivial.
     * right.
       rewrite f_prev in NE' by omega.
       rewrite NE'.
       apply flip_pred.
       { unfold lt.
         change 2 with (3-1).
         rewrite <- (@f_init k 3) by omega.
         apply f_mono.
         assert (flip k n <> 2).
         { intros EQ. rewrite EQ in *.
           simpl in NE'.
           rewrite f_k_1, f_init in NE'; omega. }
         omega. }
       { rewrite <- NE'. rewrite !f_depth. rewrite flip_depth.
         unfold p in *. omega. }
Qed.

Lemma ff_mono_S k n : ff k n <= ff k (S n).
Proof.
 generalize (ff_step k n). omega.
Qed.

Lemma ff_mono k n m : n<=m -> ff k n <= ff k m.
Proof.
induction 1.
- trivial.
- transitivity (ff k m); auto using ff_mono_S.
Qed.

Lemma ff_lipschitz k n m : ff k m - ff k n <= m - n.
Proof.
destruct (le_ge_dec n m) as [H|H].
- induction H; try generalize (ff_step k m); omega.
- generalize (ff_mono k H). omega.
Qed.

Lemma ff_nonzero k n : 0 < n -> 0 < ff k n.
Proof.
 unfold lt. intros. rewrite <- (ff_k_1 k). now apply ff_mono.
Qed.

Lemma ff_0_inv k n : ff k n = 0 -> n = 0.
Proof.
destruct n; trivial.
assert (0 < ff k (S n)) by (apply ff_nonzero; auto with arith).
omega.
Qed.

Lemma ff_nz k n : n <> 0 -> ff k n <> 0.
Proof.
intros H. contradict H. now apply (ff_0_inv k).
Qed.

Lemma ff_fix k n : ff k n = n <-> n <= 1.
Proof.
 unfold ff.
 now rewrite flip_le_1, <- f_fix, flip_swap.
Qed.

Lemma ff_le k n : ff k n <= n.
Proof.
 generalize (ff_lipschitz k 0 n). rewrite ff_k_0. omega.
Qed.

Lemma ff_lt k n : 1<n -> ff k n < n.
Proof.
intros H.
destruct (le_lt_or_eq _ _ (ff_le k n)); trivial.
rewrite ff_fix in *. omega.
Qed.

Lemma ff_onto k a : exists n, ff k n = a.
Proof.
 unfold ff. destruct (f_onto k (flip k a)) as (x,H).
 exists (flip k x). now rewrite flip_swap, flip_flip.
Qed.

Lemma ff_nonflat k n : ff k (S n) = ff k n -> ff k (S (S n)) = S (ff k n).
Proof.
 intros H.
 destruct (le_lt_dec n 1) as [Hn|Hn].
 - assert (EQ : n = 0 \/ n = 1) by omega.
   destruct EQ as [-> | ->].
   + rewrite ff_k_1, ff_k_0 in *. rewrite ff_init; omega.
   + rewrite ff_k_1 in *. rewrite !ff_init; omega.
 - destruct (ff_step k (S n)) as [H'|H']; [|omega].
   exfalso.
   set (p := depth k n).
   assert (Hp : p<>0) by (unfold p; rewrite depth_is_0; omega).
   assert (Hnp : S (A k (p-1)) <= n <= A k p).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (A k p)) as [EQ|NE].
   + rewrite EQ in H. rewrite ff_A, ff_SA' in H; omega.
   + destruct (eq_nat_dec (S n) (A k p)) as [EQ|NE'].
     * rewrite EQ in H'. rewrite ff_A, ff_SA' in H'; omega.
     * revert H'. rewrite H; clear H. unfold ff. rewrite flip_eq.
       assert (depth k (S n) = p). { apply depth_carac; omega. }
       assert (depth k (flip k (S n)) = p). { rewrite flip_depth; auto. }
       assert (depth k (S (S n)) = p). { apply depth_carac; omega. }
       assert (depth k (flip k (S (S n))) = p). { rewrite flip_depth; auto. }
       rewrite flip_S by omega.
       rewrite flip_S by (unfold p in H; omega).
       assert (HH : forall m, 1<m -> f k (m-1-1) <> f k m).
       { intros.
         generalize (@f_max_two_antecedents k (m-1-1) m).
         omega. }
       apply HH. now apply flip_gt_1.
Qed.

Lemma ff_max_two_antecedents k n m :
 ff k n = ff k m -> n < m -> m = S n.
Proof.
 intros H LT.
 unfold lt in LT.
 assert (LE := ff_mono k LT).
 rewrite <- H in LE.
 destruct (ff_step k n) as [EQ|EQ]; [|omega].
 apply ff_nonflat in EQ.
 destruct (le_lt_dec m (S n)) as [LE'|LT']; [omega|].
 unfold lt in LT'. apply (ff_mono k) in LT'. omega.
Qed.

Lemma ff_inv k n m : ff k n = ff k m -> n = m \/ n = S m \/ m = S n.
Proof.
 intros H.
 destruct (lt_eq_lt_dec n m) as [[LT|EQ]|LT]; auto.
 - apply (ff_max_two_antecedents k) in LT; auto.
 - apply (ff_max_two_antecedents k) in LT; auto.
Qed.

Lemma ffs_flip k p n :
  (ff k ^^p) n = flip k ((f k ^^p) (flip k n)).
Proof.
 revert n.
 induction p; simpl; intros.
 - symmetry. apply flip_flip.
 - rewrite IHp. unfold ff. now rewrite flip_flip.
Qed.

Lemma subsub n m p : p <= m -> n - (m - p) = n + p - m.
Proof.
 omega.
Qed.

Lemma ff_eqn k n : k+2 < n -> ff k n + (ff k^^k) (S (ff k (n-1))) = S n.
Proof.
 intros Hn.
 set (p := depth k n).
 assert (k+2<=p).
 { unfold p.
   replace (k+2) with (k+3-1) by omega.
   replace (k+3-1) with (depth k (k+3)).
   apply depth_mono; omega.
   now apply depth_init. }
 assert (LE : S (A k (p-1)) <= n <= A k p).
 { apply depth_carac. omega. auto. }
 destruct (eq_nat_dec (S (A k (p-1))) n) as [EQ|NE].
 - (* n = S (fib (p-1)) *)
   clear LE.
   replace (n-1) with (A k (p-1)) by omega.
   rewrite ff_A.
   rewrite ffs_SA by omega.
   rewrite <- EQ. clear EQ.
   rewrite ff_SA' by omega.
   rewrite Nat.add_succ_r. simpl. f_equal. f_equal.
   rewrite (@A_sum k (p-1)) by omega. f_equal. f_equal. omega.
 - (* n > S (fib (p-1)) *)
   assert (Hp : depth k (n-1) = p).
   { apply depth_carac; omega. }
   assert (Hp' : depth k (ff k (n-1)) = p-1).
   { now rewrite ff_depth, Hp. }
   assert (LE' : S (A k (p-1-1)) <= ff k (n-1) <= A k (p-1)).
   { apply depth_carac; auto. omega. }
   destruct (eq_nat_dec (ff k (n-1)) (A k (p-1))) as [EQ|NE'].
   + (* ffk(n-1) = A k (p-1) *)
     rewrite EQ.
     rewrite ffs_SA by omega.
     assert (EQ' : ff k n = A k (p-1)).
     { destruct (ff_step k (n-1)) as [EQ'|EQ'];
       replace (S (n-1)) with n in EQ'; try omega.
       rewrite EQ in EQ'.
       assert (H' : depth k (ff k n) = p) by (apply depth_carac; omega).
       rewrite ff_depth in H'. unfold p in *. omega. }
     rewrite EQ'.
     rewrite Nat.add_succ_r. rewrite <- A_S.
     f_equal.
     replace (S (p-1)) with p by omega.
     assert (EQ'' : ff k (n-1) = ff k (A k p)) by now rewrite EQ, ff_A.
     apply ff_max_two_antecedents in EQ''; omega.
   + (* ffk(n-1) <> A k (p-1) *)
     assert (Hp'' : depth k (S (ff k (n-1))) = p-1).
     { apply depth_carac; omega. }
     rewrite ffs_flip.
     apply flip_unfold;
      rewrite !fs_depth, !flip_depth, Hp''; try omega.
     assert (LT : 1 < ff k (n-1)).
     { unfold lt. change 2 with (3 - 1).
       rewrite <- (@ff_init k 3) by omega.
       apply ff_mono. omega. }
     rewrite flip_S by omega.
     unfold ff at 2. rewrite flip_flip.
     rewrite flip_pred; try (unfold p in Hp; omega).
     replace ((f k ^^ k) (f k (S (flip k n)) - 1)) with (flip k n - f k (flip k n))
     by (generalize (f_alt_eqn k (flip k n)); omega).
     rewrite Nat.add_sub_assoc by apply f_le.
     symmetry. apply Nat.add_sub_eq_r.
     rewrite <- (flip_flip k (f k (flip k n))).
     fold (ff k n).
     apply flip_unfold.
     { rewrite ?ff_depth; unfold p in H; omega. }
     rewrite ff_depth.
     change (depth k n) with p.
     replace (S n + flip k n + ff k n) with
        (S n + ff k n + flip k n) by omega.
     symmetry.
     apply flip_unfold.
     { unfold p in H; omega. }
     change (depth k n) with p.
     clear LT Hp'' NE' LE' Hp Hp'.
     rewrite (@A_sum k p) by omega.
     rewrite (@A_sum k (p-1)) at 1 by omega.
     replace (p-1-k-1) with (p-1-S k) by omega.
     replace (p-1-k) with (p-S k) by omega.
     omega.
Qed.

(** This equation, along with initial values up to [n=k+2],
    characterizes [ff] entirely. It can hence be used to
    give an algebraic recursive definition to [ff], answering
    the Hofstader's question. *)

Lemma ff_eqn_unique h k :
  h 0 = 0 ->
  h 1 = 1 ->
  (forall n, 2<= n <= k+2 -> h n = n-1) ->
  (forall n, k+2 < n -> h n + (h^^k) (S (h (n-1))) = S n) ->
  forall n, h n = ff k n.
Proof.
 intros H0 H1 Hbase Heqn.
 induction n as [n IH] using lt_wf_rec.
 destruct (le_lt_dec n (k+2)) as [Hn|Hn].
 - destruct n as [|[|n]].
   + now rewrite ff_k_0.
   + now rewrite ff_k_1.
   + rewrite ff_init, Hbase; omega.
 - assert (E := ff_eqn k Hn).
   specialize (Heqn n Hn).
   assert (E' : forall p m, m < n -> (h^^p) m = (ff k^^p) m).
   { clear - IH.
     induction p; auto.
     intros.
     rewrite !iter_S.
     rewrite IH; auto.
     apply IHp; auto.
     generalize (@ff_le k m); omega. }
   assert (E'' : h (n-1) = ff k (n-1)) by (apply IH; omega).
   rewrite E'' in *.
   replace ((h ^^ k) (S (ff k (n - 1)))) with
     ((ff k ^^ k) (S (ff k (n - 1)))) in Heqn.
   omega.
   symmetry. apply E'.
   generalize (@ff_lt k (n-1)). omega.
Qed.
