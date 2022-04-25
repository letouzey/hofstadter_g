(** * FlipG : Hofstadter's flipped G tree *)

Require Import DeltaList Fib FunG.
Set Implicit Arguments.

(** See first the file [FunG] for the study of:

     - [G (S n) + G (G n) = S n]
     - [G 0 = 0]

   and the associated tree where nodes are labeled breadth-first
   from left to right.

   Now, question by Hofstadter: what if we still label the nodes
   from right to left, but for the mirror tree ?
   What is the algebraic definition of the "parent" function
   for this flipped tree ?

<<
9 10 11 12  13
 \/   |  \ /
  6   7   8
   \   \ /
    4   5
     \ /
      3
      |
      2
      |
      1
>>

   References:
    - Hofstadter's book: Goedel, Escher, Bach, page 137.
    - Sequence A123070 on the Online Encyclopedia of Integer Sequences
      #<a href="http://oeis.org/A123070">#http://oeis.org/A123070#</a>#
*)

(*=============================================================*)

(** * The [flip] function *)

(** If we label the node from right to left, the effect
   on node numbers is the [flip] function below.
   The idea is to map a row [ [1+fib (k+1);...;fib (k+2)] ]
   to the flipped row [ [fib (k+2);...;1+fib (k+1)] ].
*)

Definition flip n :=
  if n <=? 1 then n else S (fib (S (S (S (depth n))))) - n.

Ltac tac_leb := rewrite <- ?Bool.not_true_iff_false, Nat.leb_le.

Lemma flip_depth n : depth (flip n) = depth n.
Proof.
 unfold flip.
 case_eq (n <=? 1); tac_leb; trivial.
 intros.
 assert (depth n <> 0) by (rewrite depth_0; lia).
 apply depth_carac; trivial.
 set (k := depth n) in *.
 assert (S (fib (S k)) <= n <= fib (S (S k)))
  by now apply depth_carac.
 rewrite fib_eqn.
 lia.
Qed.

Lemma flip_eqn0 n : depth n <> 0 ->
 flip n = S (fib (S (S (S (depth n))))) - n.
Proof.
 intros.
 rewrite depth_0 in *.
 unfold flip.
 case_eq (n <=? 1); tac_leb; lia.
Qed.

Lemma flip_eqn k n : 1 <= n <= fib k ->
 flip (fib (S k) + n) = S (fib (S (S k))) - n.
Proof.
 intros Hn.
 unfold flip.
 case_eq (fib (S k) + n <=? 1); tac_leb.
 - generalize (@fib_nz (S k)); lia.
 - intros H.
   replace (depth (fib (S k) + n)) with k.
   + rewrite fib_eqn. lia.
   + assert (k<>0).
     { intros ->. simpl in Hn; lia. }
     symmetry. apply depth_carac; auto.
     rewrite fib_eqn; lia.
Qed.

(** Two special cases : leftmost and rightmost node at a given depth *)

Lemma flip_Sfib k : 1<k -> flip (S (fib k)) = fib (S k).
Proof.
 intros H.
 destruct k.
 - lia.
 - rewrite <- Nat.add_1_r.
   rewrite flip_eqn.
   lia.
   split; trivial. apply fib_nz. lia.
Qed.

Lemma flip_fib k : 1<k -> flip (fib (S k)) = S (fib k).
Proof.
 intros H.
 destruct k.
 - lia.
 - rewrite fib_eqn' by lia.
   rewrite flip_eqn; auto.
   rewrite fib_eqn'; auto. lia.
   replace (S k - 1) with k by lia.
   split; auto. apply fib_nz. lia.
Qed.

(** flip is involutive (and hence a bijection) *)

Lemma flip_flip n : flip (flip n) = n.
Proof.
 unfold flip at 2.
 case_eq (n <=? 1).
 - unfold flip. now intros ->.
 - tac_leb.
   intros Hn.
   set (k := depth n).
   assert (k<>0).
   { contradict Hn. unfold k in *. rewrite depth_0 in Hn. lia. }
   assert (Hn' : S (fib (S k)) <= n <= fib (S (S k))).
   { apply depth_carac; auto. }
   rewrite fib_eqn.
   replace (S (fib (S (S k)) + fib (S k)) - n) with
    (fib (S k) + (S (fib (S (S k))) - n)) by lia.
   rewrite flip_eqn; auto. lia.
   split. lia. rewrite fib_eqn'; auto.
   replace (S k - 1) with k by lia.
   lia.
Qed.

Lemma flip_eq n m : flip n = flip m <-> n = m.
Proof.
 split; intros H.
 - rewrite <- (flip_flip n), <- (flip_flip m). now f_equal.
 - now subst.
Qed.

Lemma flip_swap n m : flip n = m <-> n = flip m.
Proof.
 rewrite <- (flip_flip m) at 1. apply flip_eq.
Qed.

Lemma flip_low n : n <= 1 <-> flip n <= 1.
Proof.
 split; intros.
 - assert (EQ : n = 0 \/ n = 1) by lia.
   destruct EQ as [-> | ->]; compute; auto.
 - assert (EQ : flip n = 0 \/ flip n = 1) by lia.
   rewrite !flip_swap in EQ. compute in EQ. lia.
Qed.

Lemma flip_high n : 1 < n <-> 1 < flip n.
Proof.
 generalize (flip_low n). lia.
Qed.

(** flip and neighbors *)

Lemma flip_S n : 1<n -> depth (S n) = depth n ->
  flip (S n) = flip n - 1.
Proof.
 intros Hn EQ.
 assert (depth n <> 0) by (rewrite depth_0; lia).
 rewrite !flip_eqn0, EQ; lia.
Qed.

Lemma flip_pred n : 1<n -> depth (n-1) = depth n ->
  flip (n-1) = S (flip n).
Proof.
 intros Hn EQ.
 assert (depth n <> 0) by (rewrite depth_0; lia).
 rewrite !flip_eqn0, EQ; try lia.
 assert (n <= fib (S (S (depth n)))) by (apply depth_carac; auto).
 rewrite fib_eqn; lia.
Qed.


(*=============================================================*)

(** * The [fg] function corresponding to the flipped [G] tree *)

Definition fg n := flip (g (flip n)).

(* Compute map fg (seq 0 10). *)

Lemma fg_depth n : depth (fg n) = depth n - 1.
Proof.
 unfold fg. now rewrite flip_depth, g_depth, flip_depth.
Qed.

Lemma fg_fib k : k<>0 -> fg (fib (S k)) = fib k.
Proof.
 destruct k as [|[|[|k]]].
 - lia.
 - reflexivity.
 - reflexivity.
 - intros _.
   unfold fg.
   now rewrite flip_fib, g_Sfib, flip_Sfib by lia.
Qed.

Lemma fg_Sfib k : 1<k -> fg (S (fib (S k))) = S (fib k).
Proof.
 intros Hk.
 unfold fg.
 rewrite flip_Sfib by lia.
 rewrite g_fib by lia.
 rewrite flip_fib; auto.
Qed.

Lemma fg_fib' k : 1<k -> fg (fib k) = fib (k-1).
Proof.
 destruct k.
 - lia.
 - intros. rewrite fg_fib; f_equal; lia.
Qed.

Lemma fg_Sfib' k : 2<k -> fg (S (fib k)) = S (fib (k-1)).
Proof.
 destruct k.
 - inversion 1.
 - intros. rewrite Nat.sub_1_r. apply fg_Sfib. simpl. lia.
Qed.

Lemma fg_step n : fg (S n) = fg n \/ fg (S n) = S (fg n).
Proof.
 destruct (le_lt_dec n 1) as [LE|LT].
 - assert (EQ : n = 0 \/ n = 1) by lia.
   destruct EQ as [-> | ->]; compute; auto.
 - set (k := depth n).
   assert (k<>0) by (unfold k; rewrite depth_0; lia).
   assert (S (fib (S k)) <= n <= fib (S (S k))).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (fib (S (S k)))) as [EQ|NE].
   + rewrite EQ. rewrite fg_Sfib, fg_fib; auto. lia.
   + assert (depth (S n) = k). { apply depth_carac; lia. }
     assert (depth (flip (S n)) = k). { rewrite flip_depth; auto. }
     assert (1 < flip n). { now apply (flip_high n). }
     unfold fg.
     rewrite flip_S in *; auto.
     destruct (eq_nat_dec (g (flip n - 1)) (g (flip n))) as [EQ|NE'].
     * left; f_equal; trivial.
     * right.
       rewrite g_prev in NE' by lia.
       rewrite NE'.
       apply flip_pred.
       { unfold lt. change 2 with (g 3). apply g_mono.
         assert (flip n <> 2).
         { intros EQ. rewrite EQ in *. now compute in NE'. }
         lia. }
       { rewrite <- NE'. rewrite !g_depth. rewrite flip_depth.
         unfold k in *; lia. }
Qed.

Lemma fg_mono_S n : fg n <= fg (S n).
Proof.
 generalize (fg_step n). lia.
Qed.

Lemma fg_mono n m : n<=m -> fg n <= fg m.
Proof.
induction 1.
- trivial.
- transitivity (fg m); auto using fg_mono_S.
Qed.

Lemma fg_lipschitz n m : fg m - fg n <= m - n.
Proof.
destruct (le_ge_dec n m) as [H|H].
- induction H; try generalize (fg_step m); lia.
- generalize (fg_mono H). lia.
Qed.

Lemma fg_nonzero n : 0 < n -> 0 < fg n.
Proof.
 unfold lt. intros. change 1 with (fg 1). now apply fg_mono.
Qed.

Lemma fg_0_inv n : fg n = 0 -> n = 0.
Proof.
destruct n; trivial.
assert (0 < fg (S n)) by (apply fg_nonzero; auto with arith).
lia.
Qed.

Lemma fg_nz n : n <> 0 -> fg n <> 0.
Proof.
intros H. contradict H. now apply fg_0_inv.
Qed.

Lemma fg_fix n : fg n = n <-> n <= 1.
Proof.
 unfold fg.
 now rewrite flip_low, <- g_fix, flip_swap.
Qed.

Lemma fg_le n : fg n <= n.
Proof.
 generalize (fg_lipschitz 0 n). change (fg 0) with 0. lia.
Qed.

Lemma fg_lt n : 1<n -> fg n < n.
Proof.
intros H.
destruct (le_lt_or_eq _ _ (fg_le n)); trivial.
rewrite fg_fix in *. lia.
Qed.

Lemma fg_onto a : exists n, fg n = a.
Proof.
 unfold fg. destruct (g_onto (flip a)) as (x,H).
 exists (flip x). now rewrite flip_swap, flip_flip.
Qed.

Lemma fg_nonflat n : fg (S n) = fg n -> fg (S (S n)) = S (fg n).
Proof.
 intros H.
 destruct (le_lt_dec n 1) as [Hn|Hn].
 - assert (EQ : n = 0 \/ n = 1) by lia.
   destruct EQ as [-> | ->]; reflexivity.
 - destruct (fg_step (S n)) as [H'|H']; [|lia].
   exfalso.
   set (k := depth n).
   assert (Hk : k<>0) by (unfold k; rewrite depth_0; lia).
   assert (Hnk : S (fib (S k)) <= n <= fib (S (S k))).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (fib (S (S k)))) as [EQ|NE].
   + rewrite EQ in H. rewrite fg_fib, fg_Sfib in H; lia.
   + destruct (eq_nat_dec (S n) (fib (S (S k)))) as [EQ|NE'].
     * rewrite EQ in H'. rewrite fg_fib, fg_Sfib in H'; lia.
     * revert H'. rewrite H; clear H. unfold fg. rewrite flip_eq.
       assert (depth (S n) = k). { apply depth_carac; lia. }
       assert (depth (flip (S n)) = k). { rewrite flip_depth; auto. }
       assert (depth (S (S n)) = k). { apply depth_carac; lia. }
       assert (depth (flip (S (S n))) = k). { rewrite flip_depth; auto. }
       rewrite flip_S by lia.
       rewrite flip_S by (unfold k in H; lia).
       assert (HH : forall m, 1<m -> g (m-1-1) <> g m).
       { intros.
         generalize (@g_max_two_antecedents (g m) (m-1-1) m).
         lia. }
       apply HH. apply flip_high in Hn. auto.
Qed.

Lemma fg_max_two_antecedents n m :
 fg n = fg m -> n < m -> m = S n.
Proof.
 intros H LT.
 unfold lt in LT.
 assert (LE := fg_mono LT).
 rewrite <- H in LE.
 destruct (fg_step n) as [EQ|EQ]; [|lia].
 apply fg_nonflat in EQ.
 destruct (le_lt_dec m (S n)) as [LE'|LT']; [lia|].
 unfold lt in LT'. apply fg_mono in LT'. lia.
Qed.

Lemma fg_inv n m : fg n = fg m -> n = m \/ n = S m \/ m = S n.
Proof.
 intros H.
 destruct (lt_eq_lt_dec n m) as [[LT|EQ]|LT]; auto.
 - apply fg_max_two_antecedents in LT; auto.
 - apply fg_max_two_antecedents in LT; auto.
Qed.

Lemma fg_eqn n : 3 < n -> fg n + fg (S (fg (n-1))) = S n.
Proof.
 intros Hn.
 set (k := depth n).
 assert (3<=k).
 { unfold k. change 3 with (depth 4).
   apply depth_mono; auto. }
 assert (LE : S (fib (S k)) <= n <= fib (S (S k))).
 { apply depth_carac. lia. auto. }
 destruct (eq_nat_dec (S (fib (S k))) n) as [EQ|NE].
 - (* n = S (fib (S k)) *)
   replace (n-1) with (fib (S k)) by lia.
   rewrite <- EQ.
   rewrite fg_fib, !fg_Sfib' by lia.
   replace (S k - 1) with k by lia.
   rewrite fib_eqn'; lia.
 - (* n > S (fib (S k)) *)
   assert (Hk : depth (n-1) = k).
   { apply depth_carac; lia. }
   assert (Hk' : depth (fg (n-1)) = k-1).
   { now rewrite fg_depth, Hk. }
   assert (LE' : S (fib k) <= fg (n-1) <= fib (S k)).
   { replace k with (S (k-1)) by lia.
     apply depth_carac; auto. lia. }
   destruct (eq_nat_dec (fg (n-1)) (fib (S k))) as [EQ|NE'].
   + (* fg(n-1) = fib (S k) *)
     rewrite EQ.
     rewrite fg_Sfib' by lia.
     assert (EQ' : fg n = fib (S k)).
     { destruct (fg_step (n-1)) as [EQ'|EQ'];
       replace (S (n-1)) with n in EQ'; try lia.
       rewrite EQ in EQ'.
       assert (H' : depth (fg n) = k) by (apply depth_carac; lia).
       rewrite fg_depth in H'. unfold k in *. lia. }
     rewrite EQ'.
     rewrite Nat.add_succ_r. rewrite <- fib_eqn' by lia.
     f_equal.
     assert (EQ'' : fg (n-1) = fg (fib (S (S k)))) by now rewrite EQ, fg_fib.
     apply fg_max_two_antecedents in EQ''; lia.
   + (* fg(n-1) <> fib (S k) *)
     assert (Hk'' : depth (S (fg (n-1))) = k-1).
     { apply depth_carac. lia.
       replace (S (k-1)) with k by lia.
       lia. }
     unfold fg at 2.
     rewrite flip_eqn0;
     rewrite g_depth, flip_depth, Hk''; [|lia].
     replace (S (S (k-1-1))) with k by lia.
     assert (LT : 1 < fg (n-1)).
     { unfold lt. change 2 with (fg 3). apply fg_mono. lia. }
     rewrite flip_S by lia.
     unfold fg at 2. rewrite flip_flip.
     rewrite flip_pred; try (unfold k in Hk; lia).
     clear LT Hk'' NE' LE' Hk Hk'.
     replace (g (g (S (flip n)) - 1)) with (flip n - g (flip n))
     by (generalize (g_alt_eqn (flip n)); lia).
     rewrite <- (flip_flip (g (flip n))).
     fold (fg n).
     rewrite !flip_eqn0 by (rewrite ?fg_depth; unfold k in H; lia).
     rewrite fg_depth.
     change (depth n) with k.
     replace (S (k-1)) with k by lia.
     rewrite fib_eqn.
     assert (Hnk : depth (fg n) = k-1).
     { rewrite fg_depth. unfold k. lia. }
     apply depth_carac in Hnk; [|lia].
     replace (S (k-1)) with k in Hnk by lia.
     replace (fib k) with (fib (S (S k)) - fib (S k)) in Hnk;
      [|rewrite fib_eqn; lia].
     set (FSSK := fib (S (S k))) in *.
     set (FSK := fib (S k)) in *.
     replace (S (FSSK+FSK) -n - (S FSSK - fg n))
      with (FSK + fg n - n) by lia.
     lia.
Qed.

(** This equation, along with initial values up to [n=3],
    characterizes [fg] entirely. It can hence be used to
    give an algebraic recursive definition to [fg], answering
    the Hofstader's question. *)

Lemma fg_eqn_unique f :
  f 0 = 0 ->
  f 1 = 1 ->
  f 2 = 1 ->
  f 3 = 2 ->
  (forall n, 3<n -> f n + f (S (f (n-1))) = S n) ->
  forall n, f n = fg n.
Proof.
 intros F0 F1 F2 F3 Fn.
 induction n as [n IH] using lt_wf_rec.
 destruct (le_lt_dec n 3) as [Hn|Hn].
 - destruct n as [|[|[|n]]]; try assumption.
   replace n with 0 by lia. assumption.
 - assert (E := fg_eqn Hn).
   specialize (Fn n Hn).
   rewrite (IH (n-1)) in Fn by lia.
   rewrite (IH (S (fg (n-1)))) in Fn.
   + generalize (@fg_lt n). lia.
   + generalize (@fg_lt (n-1)). lia.
Qed.

(*=============================================================*)

(** * [fg] and the shape of its tree

    We already know that [fg] is onto, hence each node has
    at least a child. Moreover, [fg_max_two_antecedents] says
    that we have at most two children per node.
*)

Lemma unary_flip a : Unary fg a <-> Unary g (flip a).
Proof.
 split; intros U n m Hn Hm; apply flip_eq; apply U;
 unfold fg in *; rewrite ?flip_flip; now apply flip_swap.
Qed.

Lemma multary_flip a : Multary fg a <-> Multary g (flip a).
Proof.
 unfold Multary.
 now rewrite unary_flip.
Qed.

Lemma fg_multary_binary a : Multary fg a <-> Binary fg a.
Proof.
 unfold Multary.
 split.
 - intros U.
   assert (Ha : a<>0).
   { contradict U.
     subst.
     intros u v Hu Hv. apply fg_0_inv in Hu. apply fg_0_inv in Hv.
     now subst. }
   destruct (fg_onto a) as (n,Hn).
   assert (Hn' : n<>0).
   { contradict Ha. now subst. }
   destruct (eq_nat_dec (fg (S n)) a);
   destruct (eq_nat_dec (fg (n-1)) a).
   + exfalso.
     generalize (@fg_max_two_antecedents (n-1) (S n)). lia.
   + exists n; exists (S n); repeat split; auto.
     intros k Hk.
     destruct (fg_inv n k) as [H|[H|H]]; try lia.
     subst n. simpl in *. rewrite Nat.sub_0_r in *. lia.
   + exists n; exists (n-1); repeat split; auto; try lia.
     intros k Hk.
     destruct (fg_inv n k) as [H|[H|H]]; try lia.
     subst k. lia.
   + elim U.
     intros u v Hu Hv.
     assert (u = n).
     { destruct (fg_inv n u) as [H|[H|H]]; subst;
       simpl in *; rewrite ?Nat.sub_0_r in *; lia. }
     assert (v = n).
     { destruct (fg_inv n v) as [H'|[H'|H']]; subst;
       simpl in *; rewrite ?Nat.sub_0_r in *; lia. }
     lia.
 - intros (n & m & Hn & Hm & Hnm & H) U.
   apply Hnm. now apply (U n m).
Qed.

Lemma unary_or_multary n : Unary fg n \/ Multary fg n.
Proof.
 rewrite unary_flip, multary_flip.
 apply unary_or_multary.
Qed.

Lemma unary_xor_multary n : Unary fg n -> Multary fg n -> False.
Proof.
 unfold Multary. intuition.
Qed.

(** We could even exhibit at least one child for each node *)

Definition rchild n :=
 if eq_nat_dec n 1 then 2 else n + fg (S n) - 1.
 (** rightmost son, always there *)

Lemma rightmost_child_carac a n : fg n = a ->
 (fg (S n) = S a <-> n = rchild a).
Proof.
 intros Hn.
 destruct (le_lt_dec n 2).
 - rewrite <- Hn.
   destruct n as [|[|n]].
   + compute. auto.
   + compute. auto.
   + replace n with 0 by lia. compute. auto.
 - assert (2 <= a).
   { change 2 with (fg 3). rewrite <- Hn. apply fg_mono. assumption. }
   unfold rchild.
   destruct eq_nat_dec.
   + destruct a as [|[|[|a]]]; trivial; lia.
   + assert (Hn' : 3 < S n) by lia.
     assert (H' := fg_eqn Hn').
     replace (S n - 1) with n in H' by lia.
     rewrite Hn in H'.
     lia.
Qed.

Lemma fg_onto_eqn a : fg (rchild a) = a.
Proof.
destruct (fg_onto a) as (n,Hn).
destruct (fg_step n) as [H|H].
- assert (H' := fg_nonflat _ H).
  rewrite Hn in *.
  rewrite rightmost_child_carac in H'; auto.
  now rewrite <- H'.
- rewrite Hn in *.
  rewrite rightmost_child_carac in H; auto.
  now rewrite <- H.
Qed.

Definition lchild n :=
 if eq_nat_dec n 1 then 1 else flip (FunG.rchild (flip n)).
 (** leftmost son, always there (but might be equal to
     the rightmost son for unary nodes) *)

Lemma lchild'_alt n : n<>1 -> lchild n = flip (flip n + flip (fg n)).
Proof.
 unfold lchild, FunG.rchild, fg.
 destruct eq_nat_dec; [intros; lia|intros].
 f_equal. f_equal.
 symmetry. apply flip_flip.
Qed.

Lemma fg_onto_eqn' n : fg (lchild n) = n.
Proof.
 unfold fg, lchild.
 destruct eq_nat_dec.
 - now subst.
 - rewrite flip_flip, g_onto_eqn.
   apply flip_flip.
Qed.

Lemma lchild_leftmost n : fg (lchild n - 1) = n - 1.
Proof.
 destruct (le_lt_dec n 1).
 - destruct n as [|n].
   + now compute.
   + replace n with 0 by lia; now compute.
 - set (k:=depth n).
   assert (k<>0) by (unfold k; rewrite depth_0; lia).
   assert (S (fib (S k)) <= n <= fib (S (S k))).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (S (fib (S k)))) as [E|N].
   + rewrite E.
     replace (S (fib (S k)) - 1) with (fib (S k)) by lia.
     unfold lchild.
     destruct eq_nat_dec.
     * generalize (@fib_nz k); intros; lia.
     * rewrite flip_Sfib by lia.
       unfold FunG.rchild. rewrite g_fib by lia.
       rewrite <- fib_eqn.
       rewrite flip_fib by lia.
       replace (S (fib (S (S k))) - 1) with (fib (S (S k))) by lia.
       apply fg_fib; lia.
   + unfold fg. apply flip_swap.
     assert (1 < lchild n).
     { generalize (fg_onto_eqn' n).
       generalize (@fg_mono (lchild n) 2). change (fg 2) with 1.
       lia. }
     rewrite !flip_pred; auto.
     * unfold lchild.
       destruct eq_nat_dec; [lia|].
       rewrite flip_flip.
       rewrite FunG.rightmost_child_carac; auto.
       apply g_onto_eqn.
     * change (depth n) with k; apply depth_carac; lia.
     * assert (D : depth (lchild n) = S k).
       { unfold k. rewrite <- (fg_onto_eqn' n) at 2.
         rewrite fg_depth. generalize (depth_0 (lchild n)).
         lia. }
       rewrite D.
       apply depth_carac in D; auto.
       assert (lchild n <> S (fib (S (S k)))).
       { contradict N.
         rewrite <- (fg_onto_eqn' n), N. rewrite fg_Sfib; lia. }
       apply depth_carac; auto. lia.
Qed.

Lemma lchild_leftmost' n a :
  fg n = a -> n = lchild a \/ n = S (lchild a).
Proof.
 intros Hn.
 destruct (fg_inv (lchild a) n) as [H|[H|H]]; try lia.
 - rewrite <- Hn. apply fg_onto_eqn'.
 - exfalso.
   generalize (lchild_leftmost a).
   rewrite H. simpl. rewrite Nat.sub_0_r, Hn.
   intros. replace a with 0 in * by lia.
   discriminate.
Qed.

Lemma rchild_lchild n :
 rchild n = lchild n \/ rchild n = S (lchild n).
Proof.
 apply lchild_leftmost'. apply fg_onto_eqn.
Qed.

Lemma lchild_rchild n : lchild n <= rchild n.
Proof.
 destruct (rchild_lchild n); lia.
Qed.

Lemma fg_children a n :
  fg n = a -> (n = lchild a \/ n = rchild a).
Proof.
 intros H.
 destruct (lchild_leftmost' _ H) as [Hn|Hn]; auto.
 destruct (rchild_lchild a) as [Ha|Ha]; try lia.
 exfalso.
 symmetry in Ha. apply rightmost_child_carac in Ha.
 rewrite <- Hn in Ha. lia.
 apply fg_onto_eqn'.
Qed.

Lemma binary_lchild_is_unary n :
 1<n -> Multary fg n -> Unary fg (lchild n).
Proof.
 rewrite multary_flip, unary_flip.
 unfold lchild.
 destruct eq_nat_dec; try lia.
 rewrite flip_flip.
 intros. now apply binary_rchild_is_unary.
Qed.

Lemma rightmost_son_is_binary n :
  1<n -> Multary fg (rchild n).
Proof.
 intros.
 rewrite multary_flip.
 apply leftmost_son_is_binary with (flip n).
 - apply flip_swap. apply fg_onto_eqn.
 - rewrite <- flip_swap.
   set (k:=depth n).
   assert (k<>0) by (unfold k; rewrite depth_0; lia).
   assert (S (fib (S k)) <= n <= fib (S (S k))).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (fib (S (S k)))) as [E|N].
   + assert (E' : rchild n = fib (S (S (S k)))).
     { symmetry.
       apply rightmost_child_carac.
       - now rewrite fg_fib.
       - rewrite fg_Sfib; lia. }
     rewrite E'.
     rewrite flip_fib by lia.
     replace (S (fib (S (S k))) - 1) with (fib (S (S k))) by lia.
     rewrite g_fib by lia.
     rewrite E, flip_swap, flip_fib; lia.
   + assert (1 < rchild n).
     { generalize (fg_onto_eqn n).
       generalize (@fg_mono (rchild n) 2). change (fg 2) with 1.
       lia. }
     rewrite <- flip_S; auto.
     * change (fg (S (rchild n)) <> n).
       assert (H' := fg_onto_eqn n).
       destruct (fg_step (rchild n)); try lia.
       apply rightmost_child_carac in H'. lia.
     * assert (D : depth (rchild n) = S k).
       { unfold k. rewrite <- (fg_onto_eqn n) at 2.
         rewrite fg_depth. generalize (depth_0 (rchild n)).
         lia. }
       rewrite D.
       apply depth_carac in D; auto.
       assert (rchild n <> fib (S (S (S k)))).
       { contradict N.
         rewrite <- (fg_onto_eqn n), N. now rewrite fg_fib. }
       apply depth_carac; auto. lia.
Qed.

Lemma unary_child_is_binary n :
 n <> 0 -> Unary fg n -> Multary fg (rchild n).
Proof.
 intros Hn H.
 destruct (le_lt_dec n 1).
 - replace n with 1 in * by lia.
   exfalso.
   specialize (H 1 2). compute in H. lia.
 - now apply rightmost_son_is_binary.
Qed.

Lemma binary_rchild_is_binary n :
 1<n -> Multary fg n -> Multary fg (rchild n).
Proof.
 intros. now apply rightmost_son_is_binary.
Qed.

(** Hence the shape of the [fg] tree is a repetition of
    this pattern:
<<
    r
    |
    p   q
     \ /
      n
>>
  where [n] and [q] and [r] are binary nodes and [p] is unary.

  As expected, this is the mirror of the [G] tree.
  We hence retrieve the fractal aspect of [G], flipped.
*)


(*=============================================================*)

(** * Comparison of [fg] and [g] *)

(** First, a few technical lemmas *)

Lemma fg_g_S_inv n : 3<n ->
 fg (S (fg (n-1))) = g (g (n-1)) ->
 fg n = S (g n).
Proof.
 intros Hn H.
 replace (fg n) with (S n - fg (S (fg (n-1))))
   by (rewrite <- fg_eqn; lia).
 replace n with (S (n-1)) at 3 by lia.
 rewrite g_S.
 replace (S (n-1)) with n by lia.
 rewrite H.
 assert (g (g (n-1)) <= n).
 { transitivity (g (n-1)). apply g_le.
   generalize (g_le (n-1)); lia. }
 lia.
Qed.

Lemma fg_g_eq_inv n : 3<n ->
 fg (S (fg (n-1))) = S (g (g (n-1))) ->
 fg n = g n.
Proof.
 intros Hn H.
 replace (fg n) with (S n - fg (S (fg (n-1))))
   by (rewrite <- fg_eqn; lia).
 replace n with (S (n-1)) at 3 by lia.
 rewrite g_S.
 replace (S (n-1)) with n by lia.
 rewrite H. lia.
Qed.

(** Now, the proof that [fg(n)] is either [g(n)] or [g(n)+1].
    This proof is split in many cases according to the shape
    of the Fibonacci decomposition of [n]. *)

Definition IHeq n :=
 forall m, m<n -> ~Fib.ThreeOdd 2 m -> fg m = g m.
Definition IHsucc n :=
 forall m, m<n -> Fib.ThreeOdd 2 m -> fg m = S (g m).

Lemma fg_g_aux0 n : IHeq n -> Fib.ThreeOdd 2 n -> fg n = S (g n).
Proof.
 intros IH TE.
 assert (6 <= n) by now apply ThreeOdd_le.
 apply fg_g_S_inv; try lia.
 rewrite (IH (n-1)), IH; try (generalize (@g_lt (n-1)); lia).
 - rewrite Odd_gP by autoh. apply g_Two, Three_g; autoh.
 - rewrite Odd_gP by autoh.
   now apply ThreeEven_not_ThreeOdd', ThreeOdd_Sg.
 - apply Two_not_ThreeOdd, Odd_pred_Two; autoh.
Qed.

Lemma fg_g_aux1 n : IHeq n -> 3<n -> Fib.Two 2 n -> fg n = g n.
Proof.
 intros IH N FO.
 apply fg_g_eq_inv; auto.
 assert (High 2 (n-1)). { apply Two_pred_High; auto; lia. }
 assert (Even 2 (g n)) by now apply Two_g.
 rewrite (IH (n-1)) by autoh.
 rewrite 2 Even_gP; auto using Two_Even.
 assert (g n <> 0) by (apply g_nz; lia).
 assert (g (g n) <> 0) by now apply g_nz.
 replace (S (g n - 1)) with (g n) by lia.
 rewrite IH; autoh; try apply g_lt; lia.
Qed.

Lemma fg_g_aux2 n :
 IHeq n -> IHsucc n -> 3<n -> Fib.ThreeEven 2 n -> fg n = g n.
Proof.
 intros IH1 IH2 N TO.
 apply fg_g_eq_inv; try lia.
 assert (H' := @g_lt (n-1)).
 rewrite (IH1 (n-1)), IH2; try lia.
 - rewrite Odd_gP by autoh.
   f_equal. apply g_Two. apply Three_g; autoh.
 - rewrite Odd_gP by autoh. now apply ThreeEven_Sg.
 - apply Two_not_ThreeOdd, Three_pred_Two; autoh.
Qed.

Lemma fg_g_aux3 n : IHeq n -> IHsucc n -> 3<n ->
 Fib.High 2 n -> fg n = g n.
Proof.
 intros IH1 IH2 Hn (k & K & L).
 apply fg_g_eq_inv; auto.
 destruct (Nat.Even_or_Odd k) as [(p,Hp)|(p,Hp)]; subst k.
 - (* even *)
   assert (E1 : g (n-1) = g n - 1) by (apply Even_gP; now exists p).
   assert (S (fg (n-1)) < n) by (generalize (@fg_lt (n-1)); lia).
   assert (g n <> 0) by (apply g_nz; lia).
   assert (E2 : S (g n - 1) = g n) by lia.
   destruct p as [|[|[|p]]].
   + lia.
   + lia.
   + (* four *)
     simpl in *.
     assert (T : Three 2 (g n)) by (revert L; apply g_Low; auto).
     rewrite E1, Odd_gP by autoh.
     destruct L as (l & E & D & _).
     destruct l as [|k l]; [simpl in E; lia|].
     destruct (Nat.Even_or_Odd k) as [(p,Hp)|(p,Hp)]; subst k.
     * (* next term after 3 is even *)
       assert (ThreeEven 2 (n-1)).
       { exists p; exists l; auto. subst; split; auto.
         eapply Delta_low_hd with 4; auto. }
       rewrite (IH1 (n-1)) in * by autoh.
       rewrite E1, E2, IH2 in *; auto.
       replace n with (S (n-1)) by lia.
       rewrite g_not_Two. now apply ThreeEven_Sg.
       intro. eapply Two_not_Three; eauto using ThreeEven_Three.
     * (* next term after 4 is odd *)
       assert (ThreeOdd 2 (n-1)).
       { exists p; exists l; auto. subst; split; auto.
         eapply Delta_low_hd with 4; auto. }
       rewrite (IH2 (n-1)) in * by autoh.
       rewrite E1, E2, IH1 in *; auto using Odd_succ_Even with hof.
       apply g_not_Two.
       intro. eapply Even_xor_Odd; eauto using Two_Even with hof.
   + (* high odd *)
     remember (S (S p)) as k eqn:K'.
     assert (1<k) by lia. clear K K'.
     assert (Even 2 n) by now exists (S k).
     assert (~Two 2 n).
     { intro O. generalize (Low_unique L O). lia. }
     assert (~Four 2 n).
     { intro T. generalize (Low_unique L T). lia. }
     assert (ThreeOdd 2 (n-1)) by now apply EvenHigh_pred_ThreeOdd.
     rewrite (IH2 (n-1)) in *; auto; try lia.
     rewrite E1, E2 in *.
     assert (Ev : Odd 2 (g n)) by now apply Even_g.
     rewrite Odd_gP by auto.
     rewrite IH1; auto using Odd_succ_Even with hof.
     apply g_not_Two.
     intro. apply Even_xor_Odd with (g n); eauto using Two_Even with hof.
 - (* odd *)
   assert (High 2 n) by (exists (2*p+1); auto).
   assert (Odd 2 n) by now exists p.
   rewrite (IH1 (n-1));
     [ | lia | now apply Two_not_ThreeOdd, Odd_pred_Two ].
   assert (S (g (n-1)) < n) by (generalize (@g_lt (n-1)); lia).
   rewrite Odd_gP in * by auto.
   rewrite IH1; try lia.
   + apply g_not_Two. now apply High_g.
   + now apply Even_not_ThreeOdd, High_Sg.
Qed.

(** The main result: *)

Lemma fg_g n :
 (Fib.ThreeOdd 2 n -> fg n = S (g n)) /\
 (~Fib.ThreeOdd 2 n -> fg n = g n).
Proof.
 induction n  as [n IH] using lt_wf_rec.
 assert (IH1 := fun m (H:m<n) => proj1 (IH m H)).
 assert (IH2 := fun m (H:m<n) => proj2 (IH m H)).
 clear IH.
 split.
 - now apply fg_g_aux0.
 - intros.
   destruct (le_lt_dec n 3) as [LE|LT].
   + destruct n as [|[|[|n]]]; try reflexivity.
     replace n with 0 by lia. reflexivity.
   + assert (LT' : 2 < n) by lia.
     destruct (decomp_complete' LT') as [X|[X|[X|X]]].
     * now apply fg_g_aux1.
     * now apply fg_g_aux2.
     * intuition.
     * now apply fg_g_aux3.
Qed.

(** Note: the positions where [fg] and [g] differ start at 7
    and then are separated by 5 or 8 (see [Fib.ThreeOdd_next]
    and related lemmas). Moreover these positions are always
    unary nodes in [G] (see [FunG.decomp_unary]).

    In fact, the [g] tree can be turned into the [fg] tree
    by repeating the following transformation whenever [s] below
    is ThreeOdd:
<<
  r   s t             r s   t
   \ /  |             |  \ /
    p   q   becomes   p   q
     \ /               \ /
      n                 n
>>

    In the left pattern above, [s] is ThreeOdd, hence [r] and
    [p] and [n] are Two, [q] is ThreeEven and [t] is High.
*)

(** Some immediate consequences: *)

Lemma fg_g_step n : fg n = g n \/ fg n = S (g n).
Proof.
 destruct (le_lt_dec n 3) as [LE|LT].
 - left.
   destruct n as [|[|[|n]]]; try reflexivity.
   replace n with 0 by lia. reflexivity.
 - assert (LT' : 2 < n) by lia.
   destruct (decomp_complete' LT') as [X|[X|[X|X]]].
   * left. apply fg_g. now apply Two_not_ThreeOdd.
   * left. apply fg_g. now apply ThreeEven_not_ThreeOdd.
   * right. now apply fg_g.
   * left. apply fg_g. now apply High_not_ThreeOdd.
Qed.

Lemma g_le_fg n : g n <= fg n.
Proof.
 destruct (fg_g_step n); lia.
Qed.


(*=============================================================*)

(** * [fg] and "delta" equations *)

(** We can characterize [fg] via its "delta" (a.k.a increments).
   Let [d(n) = fg(n+1)-fg(n)].  For [n>3] :

    - a) if [d(n-1) = 0] then [d(n) = 1]
    - b) if [d(n-1) <> 0] and [d(fg(n)) = 0] then [d(n) = 1]
    - c) if [d(n-1) <> 0] and [d(fg(n)) <> 0] then [d(n) = 0]

   In fact these deltas are always 0 or 1.
*)

(** [FD] is a relational presentation of these "delta" equations. *)

Inductive FD : nat -> nat -> Prop :=
 | FD_0 : FD 0 0
 | FD_1 : FD 1 1
 | FD_2 : FD 2 1
 | FD_3 : FD 3 2
 | FD_4 : FD 4 3
 | FD_a n x : 4<n -> FD (n-2) x -> FD (n-1) x -> FD n (S x)
 | FD_b n x y z : 4<n -> FD (n-2) x -> FD (n-1) y -> x<>y ->
                   FD y z -> FD (S y) z -> FD n (S y)
 | FD_c n x y z t : 4<n -> FD (n-2) x -> FD (n-1) y -> x<>y ->
                     FD y z -> FD (S y) t -> z <> t -> FD n y.
Hint Constructors FD : hof.

Lemma FD_le n k : FD n k -> k <= n.
Proof.
induction 1; auto with arith; lia.
Qed.

Lemma FD_nz n k : FD n k -> 0<n -> 0<k.
Proof.
induction 1; auto with arith; lia.
Qed.

Lemma FD_lt n k : FD n k -> 1<n -> 0<k<n.
Proof.
induction 1; auto with arith; lia.
Qed.

(* begin hide *)
Ltac uniq :=
match goal with
| U:forall k, FD ?x k -> _, V:FD ?x ?y |- _ =>
   apply U in V; try subst y; uniq
| U:?x<>?x |- _ => now elim U
end.
(* end hide *)

Lemma FD_unique n k k' : FD n k -> FD n k' -> k = k'.
Proof.
intros H1.
revert k'.
induction H1; inversion 1; subst; auto; try lia; uniq.
Qed.

Lemma FD_step n k k' : FD n k -> FD (S n) k' -> k'=k \/ k' = S k.
Proof.
inversion 2; subst; intros; simpl in *; rewrite ?Nat.sub_0_r in *.
- replace k with 0 by (apply FD_unique with 0; autoh). auto.
- replace k with 1 by (apply FD_unique with 1; autoh). auto.
- replace k with 1 by (apply FD_unique with 2; autoh). auto.
- replace k with 2 by (apply FD_unique with 3; autoh). auto.
- replace x with k by (apply FD_unique with n; autoh). lia.
- replace y with k by (apply FD_unique with n; autoh). lia.
- replace k' with k by (apply FD_unique with n; autoh). lia.
Qed.

(** [fg] is an implementation of [FD] (hence the only one). *)

Lemma fg_implements_FD n : FD n (fg n).
Proof.
induction n as [n IH] using lt_wf_rec.
destruct (le_lt_dec n 4) as [Hn|Hn].
- destruct n as [|[|[|[|n]]]]; try constructor.
  replace n with 0 by lia. constructor.
- assert (FD (n-2) (fg (n-2))) by (apply IH; lia).
  assert (FD (n-1) (fg (n-1))) by (apply IH; lia).
  destruct (fg_step (n-2)) as [E|N].
  + replace n with (S (S (n-2))) at 2 by lia.
    rewrite (fg_nonflat (n-2)); auto.
    constructor; auto. rewrite <- E.
    replace (S (n-2)) with (n-1) by lia. auto.
  + replace (S (n-2)) with (n-1) in N by lia.
    set (x := fg (n-2)) in *.
    set (y := fg (n-1)) in *.
    assert (FD y (fg y)).
    { apply IH. unfold y. generalize (fg_le (n-1)); lia. }
    assert (FD (S y) (fg (S y))).
    { apply IH. unfold y. generalize (@fg_lt (n-1)); lia. }
    assert (Hn' : 3 < n) by lia.
    assert (Hn'' : 3 < n-1) by lia.
    assert (EQ := fg_eqn Hn').
    assert (EQ' := fg_eqn Hn'').
    change (fg(n-1)) with y in EQ,EQ'.
    replace (n-1-1) with (n-2) in EQ' by lia.
    change (fg(n-2)) with x in EQ'.
    rewrite <- N in EQ'.
    destruct (fg_step y) as [E'|N'].
    * replace (fg n) with (S y) by lia.
      eapply FD_b; eauto. lia. rewrite <- E'; auto.
    * replace (fg n) with y by lia.
      eapply FD_c; eauto. lia. lia.
Qed.

Lemma fg_unique n k : FD n k <-> k = fg n.
Proof.
split.
- intros. eapply FD_unique; eauto. apply fg_implements_FD.
- intros ->. apply fg_implements_FD.
Qed.

(** The three situations a) b) c) expressed in terms of [fg]. *)

Lemma fg_a n : 0<n -> fg (n-2) = fg (n-1) -> fg n = S (fg (n-1)).
Proof.
destruct (le_lt_dec n 4).
- destruct n as [|[|[|[|n]]]].
  + lia.
  + reflexivity.
  + discriminate.
  + reflexivity.
  + replace n with 0 by lia. compute. reflexivity.
- intros.
  symmetry. apply fg_unique.
  apply FD_a; auto using fg_implements_FD.
  now apply fg_unique.
Qed.

Lemma fg_b n y : 4<n ->
 y = fg (n-1) ->
 fg (n-2) <> y ->
 fg (S y) = fg y ->
 fg n = S y.
Proof.
 intros.
 symmetry. apply fg_unique.
 apply (@FD_b n (fg (n-2)) y (fg y));
  auto using fg_implements_FD.
 - subst. apply fg_implements_FD.
 - now apply fg_unique.
Qed.

Lemma fg_c n y : 4<n ->
 y = fg (n-1) ->
 fg (n-2) <> y ->
 fg (S y) <> fg y ->
 fg n = y.
Proof.
 intros.
 symmetry. apply fg_unique.
 apply (@FD_c n (fg (n-2)) y (fg y) (fg (S y)));
  auto using fg_implements_FD.
 subst. apply fg_implements_FD.
Qed.

(** An old auxiliary lemma stating the converse of the c) case *)

Lemma fg_c_inv n :
  2<n -> fg n = fg (n-1) -> fg (S (fg n)) = S (fg (fg n)).
Proof.
 intros Hn Hg.
 symmetry in Hg. apply fg_unique in Hg.
 remember fg as f eqn:Hf.
 inversion Hg; subst.
 - reflexivity.
 - compute in H1. discriminate.
 - lia.
 - compute in H1. discriminate.
 - compute in H1. discriminate.
 - assert (x = fg(n-1)).
   { eapply FD_unique; eauto using fg_implements_FD. }
   lia.
 - assert (y = fg(n-1)).
   { eapply FD_unique; eauto using fg_implements_FD. }
   lia.
 - set (y := fg(n-1)) in *.
   assert (y = fg n).
   { eapply FD_unique with n; eauto using fg_implements_FD. }
   assert (z = fg y).
   { eapply FD_unique; eauto using fg_implements_FD. }
   assert (t = fg (S y)).
   { eapply FD_unique; eauto using fg_implements_FD. }
   destruct (fg_step y); congruence.
Qed.

(** Presentation via a "delta" function *)

Definition d n := fg (S n) - fg n.

Lemma delta_0_1 n : d n = 0 \/ d n = 1.
Proof.
 unfold d. destruct (fg_step n); lia.
Qed.

Lemma delta_a n : n<>0 -> d (n-1) = 0 -> d n = 1.
Proof.
 intro Hn.
 unfold d in *.
 generalize (fg_nonflat (n-1)).
 generalize (fg_mono_S (n-1)).
 replace (S (n-1)) with n by lia.
 lia.
Qed.

Lemma delta_b n : 4<=n ->
 d (n-1) = 1 -> d (fg n) = 0 -> d n = 1.
Proof.
 unfold d.
 intros.
 replace (S (n-1)) with n in * by lia.
 rewrite (@fg_b (S n) (fg n)); try lia.
 f_equal. lia.
 simpl. lia.
 generalize (fg_step (fg n)). lia.
Qed.

Lemma delta_c n : 4<=n ->
 d (n-1) = 1 -> d (fg n) = 1 -> d n = 0.
Proof.
 unfold d.
 intros.
 replace (S (n-1)) with n in * by lia.
 rewrite (@fg_c (S n) (fg n)); try lia.
 f_equal. lia.
 simpl. lia.
Qed.

Lemma delta_bc n : 4<=n -> d (n-1) = 1 -> d n = 1 - d (fg n).
Proof.
 intros.
 destruct (delta_0_1 (fg n)) as [E|E]; rewrite E.
 - now apply delta_b.
 - now apply delta_c.
Qed.

(* A short formula giving delta:
   This could be used to define fg. *)

Lemma delta_eqn n : 4<=n ->
 d n = 1 - d (n-1) * d (fg n).
Proof.
 intros.
 destruct (delta_0_1 (n-1)) as [E|E]; rewrite E.
 - simpl. apply delta_a; auto; lia.
 - rewrite Nat.mul_1_l. now apply delta_bc.
Qed.

(*============================================================*)

(** * An alternative equation for [fg]

   Another short equation for [fg], but this one cannot be used
   for defining [fg] recursively :-(
*)

Lemma fg_alt_eqn n : 3 < n -> fg (fg n) + fg (n-1) = n.
Proof.
 intros.
 set (k := depth n).
 assert (Hk : 3<=k).
 { unfold k. change 3 with (depth 4).
   apply depth_mono; auto. }
 assert (LE : S (fib (S k)) <= n <= fib (S (S k))).
 { apply depth_carac. lia. auto. }
 unfold fg. rewrite flip_flip.
 rewrite flip_eqn0; rewrite !g_depth, flip_depth; [|unfold k in *; lia].
 fold k.
 replace (S (S (k-1-1))) with k by lia.
 destruct (eq_nat_dec n (S (fib (S k)))) as [EQ|NE].
 - rewrite EQ.
   replace (S (fib (S k)) - 1) with (fib (S k)) by lia.
   rewrite flip_Sfib by lia.
   replace k with (S (k-1)) by lia.
   rewrite flip_fib by lia.
   rewrite !g_fib by lia.
   replace (k-1) with (S (k-2)) at 3 by lia.
   rewrite g_Sfib by lia.
   rewrite flip_Sfib by lia.
   replace (S (k-2)) with (k-1) by lia.
   rewrite fib_eqn'; lia.
 - assert (Hk' : depth (n-1) = k).
   { apply depth_carac; lia. }
   rewrite (flip_eqn0 (g _)); rewrite g_depth, flip_depth, Hk';
    [|lia].
   replace (S (k-1)) with k by lia.
   rewrite flip_pred by (unfold k in Hk'; lia).
   rewrite g_S.
   rewrite (flip_eqn0 n) at 2 by (unfold k in Hk; lia).
   fold k.
   assert (Hk'' : depth (g (g (flip n))) = k-2).
   { rewrite !g_depth, flip_depth. unfold k; lia. }
   apply depth_carac in Hk'' ; [|lia].
   rewrite (fib_eqn (S k)).
   replace (S (S (k-2))) with k in * by lia.
   assert (fib k <= fib (S k)).
   { apply fib_mono. lia. }
   lia.
Qed.

(** This last equation f(f(n)) + f(n-1) = n for n > 3
    is nice and short, but unfortunately it doesn't define
    a unique function, even if the first values are fixed to
    0 1 1 2. For instance: *)

Definition oups n :=
 match n with
 | 0 => 0
 | 1 => 1
 | 2 => 1
 | 3 => 2
 | 4 => 3
 | 5 => 3
 | 6 => 5
 | 7 => 3
 | _ => if Nat.even n then n-2 else 4
 end.

Lemma oups_def n : 7<n -> oups n = if Nat.even n then n-2 else 4.
Proof.
 do 8 (destruct n; try lia). reflexivity.
Qed.

Lemma oups_alt_eqn n : 3<n -> oups (oups n) + oups (n-1) = n.
Proof.
intros.
destruct (le_lt_dec n 9).
- do 10 (destruct n; simpl; try lia).
- case_eq (Nat.even n); intros E.
  + rewrite (@oups_def n),E,!oups_def by lia.
    rewrite !Nat.even_sub,E by lia. simpl. lia.
  + rewrite (@oups_def n),E by lia. simpl.
    rewrite oups_def by lia.
    rewrite !Nat.even_sub,E by lia. simpl. lia.
Qed.

(** We will show below that if we require this equation along
    with a monotonicity constraint, then there is a unique
    solution (which is hence [fg]). *)

(** Study of the alternative equation and its consequences. *)

Definition AltSpec (f:nat->nat) :=
  (f 0 = 0 /\ f 1 = 1 /\ f 2 = 1 /\ f 3 = 2) /\
  (forall n, 3<n -> f (f n) + f (n-1) = n).

Lemma alt_spec_fg : AltSpec fg.
Proof.
split. now compute. apply fg_alt_eqn.
Qed.

Lemma alt_spec_oups : AltSpec oups.
Proof.
split. now compute. apply oups_alt_eqn.
Qed.

Lemma alt_bound f : AltSpec f -> forall n, 1<n -> 0 < f n < n.
Proof.
intros ((H0 & H1 & H2 & H3),Hf).
induction n as [n IH] using lt_wf_rec.
intros Hn.
destruct (le_lt_dec n 3) as [Hn'|Hn'].
- destruct n as [|[|[|n]]]; try lia. replace n with 0; lia.
- assert (1 < f (f n) < n).
  { generalize (IH (n-1)) (Hf n). lia. }
  assert (f (f (S n)) + f n = S n).
  { replace n with (S n - 1) at 2 by lia. apply Hf; lia. }
  assert (f n <> 0). { intros E. rewrite E in *. lia. }
  assert (f n <> n). { intros E. rewrite !E in *. lia. }
  assert (f n <> S n).
  { intros E. rewrite E in *. specialize (IH (f (S n))). lia. }
  lia.
Qed.

Lemma alt_bound' f : AltSpec f -> forall n, 0 <= f n <= n.
Proof.
intros Hf [|[|n]].
- replace (f 0) with 0. auto. symmetry. apply Hf.
- replace (f 1) with 1. auto. symmetry. apply Hf.
- generalize (@alt_bound _ Hf (S (S n))). lia.
Qed.

Lemma alt_4 f : AltSpec f -> f 4 = 3.
Proof.
 intros Hf.
 assert (0 < f 4 < 4) by (apply alt_bound; auto).
 assert (f (f 4) + f 3 = 4) by (apply Hf; auto).
 destruct Hf as ((F0 & F1 & F2 & F3),_).
 destruct (f 4) as [|[|[|[|n]]]]; lia.
Qed.

Lemma alt_5 f : AltSpec f -> f 5 = 3.
Proof.
 intros Hf.
 assert (0 < f 5 < 5) by (apply alt_bound; auto).
 assert (f (f 5) + f 4 = 5) by (apply Hf; auto).
 assert (f 4 = 3) by (apply alt_4; auto).
 destruct Hf as ((F0 & F1 & F2 & F3),_).
 destruct (f 5) as [|[|[|[|[|n]]]]]; lia.
Qed.

(** Alas, [f(n)] isn't unique for [n>5] (e.g 4 or 5 for [n=6]) *)

Lemma monotone_equiv f :
 (forall n, f n <= f (S n)) ->
 (forall n m, n <= m -> f n <= f m).
Proof.
intros Mon.
induction 1.
- reflexivity.
- now transitivity (f m).
Qed.

Lemma alt_mono_bound f : AltSpec f ->
  (forall n, f n <= f (S n)) ->
  forall n m, n <= m -> f m - f n <= m-n.
Proof.
intros Hf Mon.
assert (main : forall n m, 3 < n <= m -> f m - f n <= m - n).
{
  intros.
  destruct Hf as (_,Hf).
  generalize (Hf (S n)) (Hf (S m)); simpl; intros.
  rewrite Nat.sub_0_r in *.
  generalize (@monotone_equiv _ Mon (S n) (S m)).
  generalize (@monotone_equiv _ Mon (f (S n)) (f (S m))).
  lia.
}
intros n m. destruct (le_lt_dec n 3); intros.
- destruct (le_lt_dec m 3); intros.
  + destruct Hf as ((F0 & F1 & F2 & F3), _).
    destruct m as [|[|[|[|m]]]], n as [|[|[|[|n]]]]; lia.
  + specialize (main 4 m). rewrite alt_4 in main; auto.
    destruct Hf as ((F0 & F1 & F2 & F3), _).
    destruct n as [|[|[|[|n]]]]; lia.
- apply main; auto.
Qed.

Lemma alt_mono_unique f1 f2 :
  AltSpec f1 -> (forall n, f1 n <= f1 (S n)) ->
  AltSpec f2 -> (forall n, f2 n <= f2 (S n)) ->
  forall n, f1 n = f2 n.
Proof.
intros Hf1 Mon1 Hf2 Mon2.
induction n as [n IH] using lt_wf_rec.
destruct (le_lt_dec n 3).
- destruct Hf1 as ((F10 & F11 & F12 & F13),_),
           Hf2 as ((F20 & F21 & F22 & F23),_).
  destruct n as [|[|[|[|n]]]]; lia.
- assert (f1 (n-1) = f2 (n-1)) by (apply IH; lia).
  assert (f1 (f1 n) = f2 (f2 n)).
  { destruct Hf1 as (_,Hf1), Hf2 as (_,Hf2).
    specialize (Hf1 n). specialize (Hf2 n). lia. }
  set (x1:=f1 n) in *.
  set (x2:=f2 n) in *.
  assert (f1 x1 = f2 x1).
  { apply IH. apply alt_bound; auto. lia. }
  assert (f1 x2 = f2 x2).
  { apply IH. apply alt_bound; auto. lia. }
  assert (f2 (n-1) <= x2 /\ x2-f2(n-1) <= 1).
  { unfold x2; split.
    - generalize (Mon2 (n-1)); replace (S (n-1)) with n; lia.
    - generalize (@alt_mono_bound _ Hf2 Mon2 (n-1) n); lia. }
  assert (f1 (n-1) <= x1 /\ x1-f1(n-1) <= 1).
  { unfold x1; split.
    - generalize (Mon1 (n-1)); replace (S (n-1)) with n; lia.
    - generalize (@alt_mono_bound _ Hf1 Mon1 (n-1) n); lia. }
  destruct (lt_eq_lt_dec x1 x2) as [[LT|EQ]|LT]; trivial; exfalso.
  + (* x1 < x2 *)
    assert (f1 (S x1) <= f1 x2).
    { apply monotone_equiv. apply Mon1. apply LT. }
    assert (f1 (f1 (S n)) = S (f1 x1)).
    { destruct Hf1 as (_,Hf1).
      generalize (Hf1 (S n)) (Hf1 n); simpl.
      rewrite Nat.sub_0_r.
      unfold x1 in *; lia. }
    assert (f1 (f1 (S n)) = f1 (S x1)).
    { f_equal.
      generalize
        (@alt_mono_bound _ Hf1 Mon1 n (S n))
        (@alt_mono_bound _ Hf1 Mon1 x1 (f1 (S n)) (Mon1 n)).
      unfold x1 in *; lia. }
    lia.
  + (* x2 < x1 *)
    assert (f2 (S x2) <= f2 x1).
    { apply monotone_equiv. apply Mon2. apply LT. }
    assert (f2 (f2 (S n)) = S (f2 x2)).
    { destruct Hf2 as (_,Hf2).
      generalize (Hf2 (S n)) (Hf2 n); simpl.
      rewrite Nat.sub_0_r.
      unfold x2 in *; lia. }
    assert (f2 (f2 (S n)) = f2 (S x2)).
    { f_equal.
      generalize
        (@alt_mono_bound _ Hf2 Mon2 n (S n))
        (@alt_mono_bound _ Hf2 Mon2 (f2 n) (f2 (S n)) (Mon2 n)).
      unfold x2 in *; lia. }
    lia.
Qed.

Lemma alt_mono_is_fg f :
  AltSpec f -> (forall n, f n <= f (S n)) ->
  forall n, f n = fg n.
Proof.
 intros Hg Mon. apply alt_mono_unique; auto.
 - split. now compute. apply fg_alt_eqn.
 - apply fg_mono_S.
Qed.
