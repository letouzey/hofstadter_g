(** * FlipG : Hofstadter's flipped G tree *)

Require Import MoreFun DeltaList GenFib GenG.
Set Implicit Arguments.

(** See first the file [GenG] for the study of:

     - [fq (S n) + fq^(S q) (n) = S n]
     - [fq 0 = 0]

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
   The idea is to map a row [ [1+Aq (p-1);...;Aq p] ]
   to the flipped row [ [Aq p;...;1+Aq (p-1)] ].
*)

Definition flip q n :=
  if n <=? 1 then n
  else
    let d := depth q n in
    1 + A q (d-1) + A q d - n.

Lemma flip_low q n : n <= 1 -> flip q n = n.
Proof.
 unfold flip.
 case Nat.leb_spec; trivial.
 lia.
Qed.

Lemma flip_0 q : flip q 0 = 0.
Proof.
 apply flip_low; auto.
Qed.

Lemma flip_1 q : flip q 1 = 1.
Proof.
 apply flip_low; auto.
Qed.

Lemma flip_depth q n : depth q (flip q n) = depth q n.
Proof.
 unfold flip.
 case Nat.leb_spec; trivial.
 intros.
 assert (depth q n <> 0) by (rewrite depth_is_0; lia).
 apply depth_carac; trivial.
 set (p := depth q n) in *.
 assert (S (A q (p-1)) <= n <= A q p)
  by now apply depth_carac.
 lia.
Qed.

Lemma flip_eqn0 q n : depth q n <> 0 ->
 flip q n = 1 + A q (depth q n - 1) + A q (depth q n) - n.
Proof.
 intros.
 rewrite depth_is_0 in *.
 unfold flip.
 case Nat.leb_spec; lia.
Qed.

Lemma flip_unfold q n a b : depth q n <> 0 ->
 a + 1 + A q (depth q n - 1) + A q (depth q n) = b + n ->
 a + flip q n = b.
Proof.
 intros.
 generalize (@depth_carac q _ n H).
 rewrite depth_is_0 in *.
 unfold flip.
 case Nat.leb_spec; lia.
Qed.

Lemma flip_eqn q p n : p<>0 -> 1 <= n <= A q (p-S q) ->
 flip q (A q (p-1) + n) = S (A q p) - n.
Proof.
 intros Hp Hn.
 unfold flip.
 case Nat.leb_spec.
 - generalize (@A_nz q (p-1)); lia.
 - intros H.
   replace (depth q (A q (p-1) + n)) with p.
   + lia.
   + symmetry. apply depth_carac; auto.
     rewrite (@A_sum q p); lia.
Qed.

(** Two special cases : leftmost and rightmost node at a given depth *)

Lemma flip_SA q p : flip q (S (A q p)) = A q (S p).
Proof.
 rewrite <- Nat.add_1_r.
 replace p with (S p - 1) at 1 by lia.
 rewrite (@flip_eqn q (S p)); auto using A_nz. lia.
Qed.

Lemma flip_A q p : p<>0 -> flip q (A q p) = S (A q (p-1)).
Proof.
 intros Hp.
 assert (E := @A_sum q p Hp).
 rewrite E.
 rewrite flip_eqn; auto using A_nz. lia.
Qed.

Lemma flip_init q n : n <= q+2 -> flip q n = n.
Proof.
 intros Hn.
 destruct n as [|[|n]].
 - apply flip_0.
 - apply flip_1.
 - rewrite <- (@A_base q (S n)) at 1 by lia.
   rewrite flip_A by lia. simpl. rewrite Nat.sub_0_r. f_equal.
   apply A_base. lia.
Qed.

(** flip is involutive (and hence a bijection) *)

Lemma flip_flip q n : flip q (flip q n) = n.
Proof.
 unfold flip at 2.
 case Nat.leb_spec.
 - apply flip_low.
 - intros Hn.
   set (p := depth q n).
   assert (p<>0).
   { unfold p. rewrite depth_is_0. lia. }
   assert (Hn' : S (A q (p-1)) <= n <= A q p).
   { apply depth_carac; auto. }
   rewrite (Nat.add_comm 1).
   rewrite <- Nat.add_assoc.
   rewrite <- Nat.add_sub_assoc by lia.
   rewrite flip_eqn; auto. lia.
   split. lia.
   rewrite (@A_sum q p) by trivial. lia.
Qed.

Lemma flip_eq q n m : flip q n = flip q m <-> n = m.
Proof.
 split; intros H.
 - rewrite <- (flip_flip q n), <- (flip_flip q m). now f_equal.
 - now subst.
Qed.

Lemma flip_swap q n m : flip q n = m <-> n = flip q m.
Proof.
 rewrite <- (flip_flip q m) at 1. apply flip_eq.
Qed.

Lemma flip_le_1 q n : n <= 1 <-> flip q n <= 1.
Proof.
 split; intros.
 - assert (EQ : n = 0 \/ n = 1) by lia.
   destruct EQ as [-> | ->]; compute; auto.
 - assert (EQ : flip q n = 0 \/ flip q n = 1) by lia.
   rewrite !flip_swap in EQ. compute in EQ. lia.
Qed.

Lemma flip_gt_1 q n : 1 < n <-> 1 < flip q n.
Proof.
 generalize (flip_le_1 q n). lia.
Qed.

(** flip and neighbors *)

Lemma flip_S q n : 1<n -> depth q (S n) = depth q n ->
  flip q (S n) = flip q n - 1.
Proof.
 intros Hn EQ.
 assert (depth q n <> 0) by (rewrite depth_is_0; lia).
 rewrite !flip_eqn0, EQ; lia.
Qed.

Lemma flip_pred q n : 1<n -> depth q (n-1) = depth q n ->
  flip q (n-1) = S (flip q n).
Proof.
 intros Hn EQ.
 assert (depth q n <> 0) by (rewrite depth_is_0; lia).
 rewrite !flip_eqn0, EQ; try lia.
 assert (n <= A q (depth q n)) by (apply depth_carac; auto).
 lia.
Qed.


(*=============================================================*)

(** * The [ff] function corresponding to the flipped [f] tree *)

Definition ff q n := flip q (f q (flip q n)).
Notation ffs q p := (ff q ^^p).

(* Compute take 20 (ff 2). *)

Lemma ff_q_0 q : ff q 0 = 0.
Proof.
 reflexivity.
Qed.

Lemma ff_q_1 q : ff q 1 = 1.
Proof.
 reflexivity.
Qed.

Lemma ff_depth q n : depth q (ff q n) = depth q n - 1.
Proof.
 unfold ff. now rewrite flip_depth, f_depth, flip_depth.
Qed.

Lemma ff_A q p : ff q (A q p) = A q (p-1).
Proof.
 destruct p as [|p].
 simpl.
 - unfold ff. rewrite (@flip_low q 1), f_q_1; auto.
 - unfold ff.
   rewrite flip_A by auto.
   simpl. rewrite Nat.sub_0_r.
   destruct p as [|p].
   + simpl. rewrite f_init. simpl. apply flip_low; auto. lia.
   + rewrite f_SA; auto. simpl Nat.sub. rewrite Nat.sub_0_r.
     apply flip_SA.
Qed.

Lemma ff_SA q p : ff q (S (A q (S p))) = S (A q p).
Proof.
 unfold ff.
 rewrite flip_SA.
 rewrite f_A.
 rewrite flip_A. f_equal. f_equal. lia. lia.
Qed.

Lemma ff_SA' q p : p<>0 -> ff q (S (A q p)) = S (A q (p-1)).
Proof.
 destruct p.
 - intuition.
 - intros _. rewrite ff_SA. f_equal. f_equal. lia.
Qed.

Lemma ffs_A q m p : ffs q m (A q p) = A q (p-m).
Proof.
 revert p.
 induction m as [|m IH]; intros p; simpl.
 - now rewrite Nat.sub_0_r.
 - rewrite IH, ff_A. f_equal. lia.
Qed.

Lemma ffs_SA q m p : m <= p -> ffs q m (S (A q p)) = S (A q (p-m)).
Proof.
 revert p.
 induction m as [|m IH]; intros p H; simpl.
 - now rewrite Nat.sub_0_r.
 - rewrite IH, ff_SA' by lia. f_equal. f_equal. lia.
Qed.

Lemma ff_init q p : 2 <= p <= q+3 -> ff q p = p-1.
Proof.
 intros (H,H').
 apply Nat.lt_eq_cases in H'. destruct H' as [H'| ->].
 - unfold ff. rewrite (@flip_init q p) by lia.
   rewrite f_init by lia.
   apply flip_init. lia.
 - replace (q+3) with (S (S (S q))) by lia.
   rewrite <- (@A_base q (S q)) at 1 by lia.
   rewrite ff_SA. rewrite A_base; lia.
Qed.

Lemma ff_step q n : ff q (S n) = ff q n \/ ff q (S n) = S (ff q n).
Proof.
 destruct (le_lt_dec n 1) as [LE|LT].
 - assert (EQ : n = 0 \/ n = 1) by lia.
   destruct EQ as [-> | ->].
   + rewrite ff_q_0, ff_q_1; auto.
   + rewrite ff_init, ff_q_1; lia.
 - set (p := depth q n).
   assert (p<>0) by (unfold p; rewrite depth_is_0; lia).
   assert (S (A q (p-1)) <= n <= A q p).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (A q p)) as [EQ|NE].
   + rewrite EQ. rewrite ff_SA', ff_A; auto.
   + assert (depth q (S n) = p). { apply depth_carac; lia. }
     assert (depth q (flip q (S n)) = p). { rewrite flip_depth; auto. }
     assert (1 < flip q n). { now apply (flip_gt_1 q n). }
     unfold ff.
     rewrite flip_S in *; auto.
     destruct (eq_nat_dec (f q (flip q n - 1)) (f q (flip q n))) as [EQ|NE'].
     * left; f_equal; trivial.
     * right.
       rewrite f_prev in NE' by lia.
       rewrite NE'.
       apply flip_pred.
       { unfold lt.
         change 2 with (3-1).
         rewrite <- (@f_init q 3) by lia.
         apply f_mono.
         assert (flip q n <> 2).
         { intros EQ. rewrite EQ in *.
           simpl in NE'.
           rewrite f_q_1, f_init in NE'; lia. }
         lia. }
       { rewrite <- NE'. rewrite !f_depth. rewrite flip_depth.
         unfold p in *. lia. }
Qed.

Lemma ff_mono_S q n : ff q n <= ff q (S n).
Proof.
 generalize (ff_step q n). lia.
Qed.

Lemma ff_mono q n m : n<=m -> ff q n <= ff q m.
Proof.
induction 1.
- trivial.
- transitivity (ff q m); auto using ff_mono_S.
Qed.

Lemma ff_lipschitz q n m : ff q m - ff q n <= m - n.
Proof.
destruct (le_ge_dec n m) as [H|H].
- induction H; try generalize (ff_step q m); lia.
- generalize (ff_mono q H). lia.
Qed.

Lemma ff_nonzero q n : 0 < n -> 0 < ff q n.
Proof.
 unfold lt. intros. rewrite <- (ff_q_1 q). now apply ff_mono.
Qed.

Lemma ff_0_inv q n : ff q n = 0 -> n = 0.
Proof.
destruct n; trivial.
assert (0 < ff q (S n)) by (apply ff_nonzero; auto with arith).
lia.
Qed.

Lemma ff_nz q n : n <> 0 -> ff q n <> 0.
Proof.
intros H. contradict H. now apply (ff_0_inv q).
Qed.

Lemma ff_fix q n : ff q n = n <-> n <= 1.
Proof.
 unfold ff.
 now rewrite flip_le_1, <- f_fix, flip_swap.
Qed.

Lemma ff_le q n : ff q n <= n.
Proof.
 generalize (ff_lipschitz q 0 n). rewrite ff_q_0. lia.
Qed.

Lemma ff_lt q n : 1<n -> ff q n < n.
Proof.
 generalize (ff_le q n) (ff_fix q n); lia.
Qed.

Lemma ff_onto q a : exists n, ff q n = a.
Proof.
 unfold ff. destruct (f_onto q (flip q a)) as (x,H).
 exists (flip q x). now rewrite flip_swap, flip_flip.
Qed.

Lemma ff_nonflat q n : ff q (S n) = ff q n -> ff q (S (S n)) = S (ff q n).
Proof.
 intros H.
 destruct (le_lt_dec n 1) as [Hn|Hn].
 - assert (EQ : n = 0 \/ n = 1) by lia.
   destruct EQ as [-> | ->].
   + rewrite ff_q_1, ff_q_0 in *. rewrite ff_init; lia.
   + rewrite ff_q_1 in *. rewrite !ff_init; lia.
 - destruct (ff_step q (S n)) as [H'|H']; [|lia].
   exfalso.
   set (p := depth q n).
   assert (Hp : p<>0) by (unfold p; rewrite depth_is_0; lia).
   assert (Hnp : S (A q (p-1)) <= n <= A q p).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (A q p)) as [EQ|NE].
   + rewrite EQ in H. rewrite ff_A, ff_SA' in H; lia.
   + destruct (eq_nat_dec (S n) (A q p)) as [EQ|NE'].
     * rewrite EQ in H'. rewrite ff_A, ff_SA' in H'; lia.
     * revert H'. rewrite H; clear H. unfold ff. rewrite flip_eq.
       assert (depth q (S n) = p). { apply depth_carac; lia. }
       assert (depth q (flip q (S n)) = p). { rewrite flip_depth; auto. }
       assert (depth q (S (S n)) = p). { apply depth_carac; lia. }
       assert (depth q (flip q (S (S n))) = p). { rewrite flip_depth; auto. }
       rewrite flip_S by lia.
       rewrite flip_S by (unfold p in H; lia).
       assert (HH : forall m, 1<m -> f q (m-1-1) <> f q m).
       { intros.
         generalize (@f_max_two_antecedents q (m-1-1) m).
         lia. }
       apply HH. now apply flip_gt_1.
Qed.

Lemma ff_max_two_antecedents q n m :
 ff q n = ff q m -> n < m -> m = S n.
Proof.
 intros H LT.
 unfold lt in LT.
 assert (LE := ff_mono q LT).
 rewrite <- H in LE.
 destruct (ff_step q n) as [EQ|EQ]; [|lia].
 apply ff_nonflat in EQ.
 destruct (le_lt_dec m (S n)) as [LE'|LT']; [lia|].
 unfold lt in LT'. apply (ff_mono q) in LT'. lia.
Qed.

Lemma ff_inv q n m : ff q n = ff q m -> n = m \/ n = S m \/ m = S n.
Proof.
 intros H.
 destruct (lt_eq_lt_dec n m) as [[LT|EQ]|LT]; auto.
 - apply (ff_max_two_antecedents q) in LT; auto.
 - apply (ff_max_two_antecedents q) in LT; auto.
Qed.

Lemma ffs_flip q p n :
  ffs q p n = flip q (fs q p (flip q n)).
Proof.
 revert n.
 induction p; simpl; intros.
 - symmetry. apply flip_flip.
 - rewrite IHp. unfold ff. now rewrite flip_flip.
Qed.

Lemma ff_eqn q n : q+2 < n -> ff q n + ffs q q (S (ff q (n-1))) = S n.
Proof.
 intros Hn.
 set (p := depth q n).
 assert (q+2<=p).
 { unfold p.
   replace (q+2) with (q+3-1) by lia.
   replace (q+3-1) with (depth q (q+3)).
   apply depth_mono; lia.
   now apply depth_init. }
 assert (LE : S (A q (p-1)) <= n <= A q p).
 { apply depth_carac. lia. auto. }
 destruct (eq_nat_dec (S (A q (p-1))) n) as [EQ|NE].
 - (* n = S (fib (p-1)) *)
   clear LE.
   replace (n-1) with (A q (p-1)) by lia.
   rewrite ff_A.
   rewrite ffs_SA by lia.
   rewrite <- EQ. clear EQ.
   rewrite ff_SA' by lia.
   rewrite Nat.add_succ_r. simpl. f_equal. f_equal.
   rewrite (@A_sum q (p-1)) by lia. f_equal. f_equal. lia.
 - (* n > S (fib (p-1)) *)
   assert (Hp : depth q (n-1) = p).
   { apply depth_carac; lia. }
   assert (Hp' : depth q (ff q (n-1)) = p-1).
   { now rewrite ff_depth, Hp. }
   assert (LE' : S (A q (p-1-1)) <= ff q (n-1) <= A q (p-1)).
   { apply depth_carac; auto. lia. }
   destruct (eq_nat_dec (ff q (n-1)) (A q (p-1))) as [EQ|NE'].
   + (* ffq(n-1) = A q (p-1) *)
     rewrite EQ.
     rewrite ffs_SA by lia.
     assert (EQ' : ff q n = A q (p-1)).
     { destruct (ff_step q (n-1)) as [EQ'|EQ'];
       replace (S (n-1)) with n in EQ'; try lia.
       rewrite EQ in EQ'.
       assert (H' : depth q (ff q n) = p) by (apply depth_carac; lia).
       rewrite ff_depth in H'. unfold p in *. lia. }
     rewrite EQ'.
     rewrite Nat.add_succ_r. rewrite <- A_S.
     f_equal.
     replace (S (p-1)) with p by lia.
     assert (EQ'' : ff q (n-1) = ff q (A q p)) by now rewrite EQ, ff_A.
     apply ff_max_two_antecedents in EQ''; lia.
   + (* ffq(n-1) <> A q (p-1) *)
     assert (Hp'' : depth q (S (ff q (n-1))) = p-1).
     { apply depth_carac; lia. }
     rewrite ffs_flip.
     apply flip_unfold;
      rewrite !fs_depth, !flip_depth, Hp''; try lia.
     assert (LT : 1 < ff q (n-1)).
     { unfold lt. change 2 with (3 - 1).
       rewrite <- (@ff_init q 3) by lia.
       apply ff_mono. lia. }
     rewrite flip_S by lia.
     unfold ff at 2. rewrite flip_flip.
     rewrite flip_pred; try (unfold p in Hp; lia).
     replace (fs q q (f q (S (flip q n)) - 1)) with (flip q n - f q (flip q n))
     by (generalize (f_alt_eqn q (flip q n)); lia).
     rewrite Nat.add_sub_assoc by apply f_le.
     symmetry. apply Nat.add_sub_eq_r.
     rewrite <- (flip_flip q (f q (flip q n))).
     fold (ff q n).
     apply flip_unfold.
     { rewrite ?ff_depth; unfold p in H; lia. }
     rewrite ff_depth.
     change (depth q n) with p.
     replace (S n + flip q n + ff q n) with
        (S n + ff q n + flip q n) by lia.
     symmetry.
     apply flip_unfold.
     { unfold p in H; lia. }
     change (depth q n) with p.
     clear LT Hp'' NE' LE' Hp Hp'.
     rewrite (@A_sum q p) by lia.
     rewrite (@A_sum q (p-1)) at 1 by lia.
     replace (p-1-q-1) with (p-1-S q) by lia.
     replace (p-1-q) with (p-S q) by lia.
     lia.
Qed.

(** This equation, along with initial values up to [n=q+2],
    characterizes [ff] entirely. It can hence be used to
    give an algebraic recursive definition to [ff], answering
    the Hofstader's question. *)

Lemma ff_eqn_unique h q :
  h 0 = 0 ->
  h 1 = 1 ->
  (forall n, 2<= n <= q+2 -> h n = n-1) ->
  (forall n, q+2 < n -> h n + (h^^q) (S (h (n-1))) = S n) ->
  forall n, h n = ff q n.
Proof.
 intros H0 H1 Hbase Heqn.
 induction n as [n IH] using lt_wf_rec.
 destruct (le_lt_dec n (q+2)) as [Hn|Hn].
 - destruct n as [|[|n]].
   + now rewrite ff_q_0.
   + now rewrite ff_q_1.
   + rewrite ff_init, Hbase; lia.
 - assert (E := ff_eqn q Hn).
   specialize (Heqn n Hn).
   assert (E' : forall p m, m < n -> (h^^p) m = ffs q p m).
   { clear - IH.
     induction p; auto.
     intros.
     rewrite !iter_S.
     rewrite IH; auto.
     apply IHp; auto.
     generalize (@ff_le q m); lia. }
   assert (E'' : h (n-1) = ff q (n-1)) by (apply IH; lia).
   rewrite E'' in *.
   replace ((h ^^ q) (S (ff q (n - 1)))) with
     (ffs q q (S (ff q (n - 1)))) in Heqn.
   lia.
   symmetry. apply E'.
   generalize (@ff_lt q (n-1)). lia.
Qed.
