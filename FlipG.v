(** * FlipG : Hofstadter's flipped G tree *)

Require Import Arith Omega Wf_nat List Program Program.Wf NPeano.
Require Import DeltaList Fib FunG.
Set Implicit Arguments.

(** See first the previous file for the study of:

     - [G (S n) + G (G n) = S n]
     - [G 0 = 0]

   and the associated tree where nodes are labeled breadth-first
   from left to right.

   Source: Hofstadter's book: Goedel, Escher, Bach.

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
*)

(*=============================================================*)

(** * The [flip] function *)

(** If we label the node from right to left, the effect
   on node numbers is the [flip] function below.
   The idea is to map a row [ [(fib k)+1;...;fib (k+1)] ]
   to the flipped row [ [fib (k+1);...;(fib k)+1] ].
*)

Definition flip n :=
  if n <=? 1 then n else S (fib (S (S (depth n)))) - n.

Ltac tac_leb := rewrite <- ?Bool.not_true_iff_false, leb_le.

Lemma flip_depth n : depth (flip n) = depth n.
Proof.
 unfold flip.
 case_eq (n <=? 1); tac_leb; trivial.
 intros.
 assert (depth n <> 0) by (rewrite depth_0; omega).
 apply depth_carac; trivial.
 set (k := depth n) in *.
 assert (S (fib k) <= n <= fib (S k)) by now apply depth_carac.
 rewrite fib_eqn.
 omega.
Qed.

Lemma flip_eqn0 n : depth n <> 0 ->
 flip n = S (fib (S (S (depth n)))) - n.
Proof.
 intros.
 rewrite depth_0 in *.
 unfold flip.
 case_eq (n <=? 1); tac_leb; omega.
Qed.

Lemma flip_eqn k n : k<>0 -> 1 <= n <= fib (k-1) ->
 flip (fib k + n) = S (fib (S k)) - n.
Proof.
 intros Hk Hn.
 unfold flip.
 case_eq (fib k + n <=? 1); tac_leb.
 - generalize (fib_nz k); omega.
 - intros H.
   replace (depth (fib k + n)) with k.
   + rewrite fib_eqn. omega.
   + symmetry. apply depth_carac; auto.
     rewrite fib_eqn'; omega.
Qed.

(** Two special cases : leftmost and rightmost node at a given depth *)

Lemma flip_Sfib k : k<>0 -> flip (S (fib k)) = fib (S k).
Proof.
 intros H.
 rewrite <- Nat.add_1_r.
 rewrite flip_eqn; try omega.
 split; trivial. apply fib_nz.
Qed.

Lemma flip_fib k : k<>0 -> flip (fib (S k)) = S (fib k).
Proof.
 intros H.
 rewrite fib_eqn'; auto.
 rewrite flip_eqn; auto.
 rewrite fib_eqn'; auto. omega.
 split; auto. apply fib_nz.
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
   { contradict Hn. subst. rewrite depth_0 in Hn. omega. }
   assert (Hn' : S (fib k) <= n <= fib (S k)).
   { apply depth_carac; auto. }
   rewrite fib_eqn.
   replace (S (fib (S k) + fib k) - n) with
    (fib k + (S (fib (S k)) - n)) by omega.
   rewrite flip_eqn; auto. omega.
   split. omega. rewrite fib_eqn'; auto. omega.
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
 - assert (EQ : n = 0 \/ n = 1) by omega.
   destruct EQ as [-> | ->]; compute; auto.
 - assert (EQ : flip n = 0 \/ flip n = 1) by omega.
   rewrite !flip_swap in EQ. compute in EQ. omega.
Qed.

Lemma flip_high n : 1 < n <-> 1 < flip n.
Proof.
 generalize (flip_low n). omega.
Qed.

(** flip and neighbors *)

Lemma flip_S n : 1<n -> depth (S n) = depth n ->
  flip (S n) = flip n - 1.
Proof.
 intros Hn EQ.
 assert (depth n <> 0) by (rewrite depth_0; omega).
 rewrite !flip_eqn0, EQ; omega.
Qed.

Lemma flip_pred n : 1<n -> depth (n-1) = depth n ->
  flip (n-1) = S (flip n).
Proof.
 intros Hn EQ.
 assert (depth n <> 0) by (rewrite depth_0; omega).
 rewrite !flip_eqn0, EQ; try omega.
 assert (n <= fib (S (depth n))) by (apply depth_carac; auto).
 rewrite fib_eqn; omega.
Qed.


(*=============================================================*)

(** * The [fg] function corresponding to the flipped [G] tree *)

Definition fg n := flip (g (flip n)).

(* Compute map fg (seq 0 10). *)

Lemma fg_depth n : depth (fg n) = depth n - 1.
Proof.
 unfold fg. now rewrite flip_depth, g_depth, flip_depth.
Qed.

Lemma fg_fib k : fg (fib (S k)) = fib k.
Proof.
 destruct k.
 - now compute.
 - destruct k.
   + now compute.
   + unfold fg.
     rewrite flip_fib; auto.
     rewrite g_Sfib; auto.
     rewrite flip_Sfib; auto.
Qed.

Lemma fg_Sfib k : k<>0 -> fg (S (fib (S k))) = S (fib k).
Proof.
 intros Hk.
 unfold fg.
 rewrite flip_Sfib; auto.
 rewrite g_fib.
 rewrite flip_fib; auto.
Qed.

Lemma fg_fib' k : k<>0 -> fg (fib k) = fib (k-1).
Proof.
 destruct k.
 - now destruct 1.
 - intros. rewrite Nat.sub_1_r. apply fg_fib.
Qed.

Lemma fg_Sfib' k : 1<k -> fg (S (fib k)) = S (fib (k-1)).
Proof.
 destruct k.
 - inversion 1.
 - intros. rewrite Nat.sub_1_r. apply fg_Sfib. simpl. omega.
Qed.

Lemma fg_step n : fg (S n) = fg n \/ fg (S n) = S (fg n).
Proof.
 destruct (le_lt_dec n 1) as [LE|LT].
 - assert (EQ : n = 0 \/ n = 1) by omega.
   destruct EQ as [-> | ->]; compute; auto.
 - set (k := depth n).
   assert (k<>0) by (unfold k; rewrite depth_0; omega).
   assert (S (fib k) <= n <= fib (S k)).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (fib (S k))) as [EQ|NE].
   + rewrite EQ. rewrite fg_Sfib, fg_fib; auto.
   + assert (depth (S n) = k). { apply depth_carac; omega. }
     assert (depth (flip (S n)) = k). { rewrite flip_depth; auto. }
     assert (1 < flip n). { now apply (flip_high n). }
     unfold fg.
     rewrite flip_S in *; auto.
     destruct (eq_nat_dec (g (flip n - 1)) (g (flip n))) as [EQ|NE'].
     * left; f_equal; trivial.
     * right.
       rewrite g_prev in NE' by omega.
       rewrite NE'.
       apply flip_pred.
       { unfold lt. change 2 with (g 3). apply g_mono.
         assert (flip n <> 2).
         { intros EQ. rewrite EQ in *. now compute in NE'. }
         omega. }
       { rewrite <- NE'. rewrite !g_depth. rewrite flip_depth.
         unfold k in *; omega. }
Qed.

Lemma fg_mono_S n : fg n <= fg (S n).
Proof.
 generalize (fg_step n). omega.
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
- induction H; try generalize (fg_step m); omega.
- generalize (fg_mono H). omega.
Qed.

Lemma fg_nonzero n : 0 < n -> 0 < fg n.
Proof.
 unfold lt. intros. change 1 with (fg 1). now apply fg_mono.
Qed.

Lemma fg_0_inv n : fg n = 0 -> n = 0.
Proof.
destruct n; trivial.
assert (0 < fg (S n)) by (apply fg_nonzero; auto with arith).
omega.
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
 generalize (fg_lipschitz 0 n). change (fg 0) with 0. omega.
Qed.

Lemma fg_lt n : 1<n -> fg n < n.
Proof.
intros H.
destruct (le_lt_or_eq _ _ (fg_le n)); trivial.
rewrite fg_fix in *. omega.
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
 - assert (EQ : n = 0 \/ n = 1) by omega.
   destruct EQ as [-> | ->]; reflexivity.
 - destruct (fg_step (S n)) as [H'|H']; [|omega].
   exfalso.
   set (k := depth n).
   assert (Hk : k<>0) by (unfold k; rewrite depth_0; omega).
   assert (Hnk : S (fib k) <= n <= fib (S k)).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (fib (S k))) as [EQ|NE].
   + rewrite EQ in H. rewrite fg_fib, fg_Sfib in H; omega.
   + destruct (eq_nat_dec (S n) (fib (S k))) as [EQ|NE'].
     * rewrite EQ in H'. rewrite fg_fib, fg_Sfib in H'; omega.
     * revert H'. rewrite H; clear H. unfold fg. rewrite flip_eq.
       assert (depth (S n) = k). { apply depth_carac; omega. }
       assert (depth (flip (S n)) = k). { rewrite flip_depth; auto. }
       assert (depth (S (S n)) = k). { apply depth_carac; omega. }
       assert (depth (flip (S (S n))) = k). { rewrite flip_depth; auto. }
       rewrite flip_S by omega.
       rewrite flip_S by (unfold k in H; omega).
       assert (HH : forall m, 1<m -> g (m-1-1) <> g m).
       { intros.
         generalize (@g_max_two_antecedents (g m) (m-1-1) m).
         omega. }
       apply HH. apply flip_high in Hn. auto.
Qed.

Lemma fg_max_two_antecedents n m :
 fg n = fg m -> n < m -> m = S n.
Proof.
 intros H LT.
 unfold lt in LT.
 assert (LE := fg_mono LT).
 rewrite <- H in LE.
 destruct (fg_step n) as [EQ|EQ]; [|omega].
 apply fg_nonflat in EQ.
 destruct (le_lt_dec m (S n)) as [LE'|LT']; [omega|].
 unfold lt in LT'. apply fg_mono in LT'. omega.
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
 assert (LE : S (fib k) <= n <= fib (S k)).
 { apply depth_carac. omega. auto. }
 destruct (eq_nat_dec (S (fib k)) n) as [EQ|NE].
 - (* n = S (fib k) *)
   replace (n-1) with (fib k) by omega.
   rewrite <- EQ.
   rewrite fg_fib', !fg_Sfib' by omega.
   simpl. rewrite Nat.add_succ_r. rewrite <- fib_eqn' by omega.
   do 3 f_equal. omega.
 - (* n > S (fib k) *)
   assert (Hk : depth (n-1) = k).
   { apply depth_carac; omega. }
   assert (Hk' : depth (fg (n-1)) = k-1).
   { now rewrite fg_depth, Hk. }
   assert (LE' : S (fib (k-1)) <= fg (n-1) <= fib k).
   { replace k with (S (k-1)) at 2 by omega.
     apply depth_carac; auto. omega. }
   destruct (eq_nat_dec (fg (n-1)) (fib k)) as [EQ|NE'].
   + (* fg(n-1) = fib k *)
     rewrite EQ.
     rewrite fg_Sfib' by omega.
     assert (EQ' : fg n = fib k).
     { destruct (fg_step (n-1)) as [EQ'|EQ'];
       replace (S (n-1)) with n in EQ'; try omega.
       rewrite EQ in EQ'.
       assert (H' : depth (fg n) = k) by (apply depth_carac; omega).
       rewrite fg_depth in H'. unfold k in *. omega. }
     rewrite EQ'.
     rewrite Nat.add_succ_r. rewrite <- fib_eqn' by omega.
     f_equal.
     assert (EQ'' : fg (n-1) = fg (fib (S k))) by now rewrite EQ, fg_fib.
     apply fg_max_two_antecedents in EQ''; omega.
   + (* fg(n-1) <> fib k *)
     assert (Hk'' : depth (S (fg (n-1))) = k-1).
     { apply depth_carac. omega.
       replace (S (k-1)) with k by omega.
       omega. }
     unfold fg at 2.
     rewrite flip_eqn0;
     rewrite g_depth, flip_depth, Hk''; [|omega].
     replace (S (S (k-1-1))) with k by omega.
     assert (LT : 1 < fg (n-1)).
     { unfold lt. change 2 with (fg 3). apply fg_mono. omega. }
     rewrite flip_S by omega.
     unfold fg at 2. rewrite flip_flip.
     rewrite flip_pred; try (unfold k in Hk; omega).
     clear LT Hk'' NE' LE' Hk Hk'.
     replace (g (g (S (flip n)) - 1)) with (flip n - g (flip n))
     by (generalize (g_alt_eqn (flip n)); omega).
     rewrite <- (flip_flip (g (flip n))).
     fold (fg n).
     rewrite !flip_eqn0 by (rewrite ?fg_depth; unfold k in H; omega).
     rewrite fg_depth.
     change (depth n) with k.
     replace (S (k-1)) with k by omega.
     rewrite fib_eqn.
     assert (Hnk : depth (fg n) = k-1).
     { rewrite fg_depth. unfold k. omega. }
     apply depth_carac in Hnk; [|omega].
     replace (S (k-1)) with k in Hnk by omega.
     replace (fib (k-1)) with (fib (S k) - fib k) in Hnk;
      [|rewrite fib_eqn'; omega].
     set (FSK := fib (S k)) in *.
     set (FK := fib k) in *.
     replace (S (FSK+FK) -n - (S FSK - fg n))
      with (FK + fg n - n) by omega.
     omega.
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
   replace n with 0 by omega. assumption.
 - assert (E := fg_eqn Hn).
   specialize (Fn n Hn).
   rewrite (IH (n-1)) in Fn by omega.
   rewrite (IH (S (fg (n-1)))) in Fn.
   + generalize (@fg_lt n). omega.
   + generalize (@fg_lt (n-1)). omega.
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
     generalize (@fg_max_two_antecedents (n-1) (S n)). omega.
   + exists n; exists (S n); repeat split; auto.
     intros k Hk.
     destruct (fg_inv n k) as [H|[H|H]]; try omega.
     subst n. simpl in *. rewrite Nat.sub_0_r in *. omega.
   + exists n; exists (n-1); repeat split; auto; try omega.
     intros k Hk.
     destruct (fg_inv n k) as [H|[H|H]]; try omega.
     subst k. omega.
   + elim U.
     intros u v Hu Hv.
     assert (u = n).
     { destruct (fg_inv n u) as [H|[H|H]]; subst;
       simpl in *; rewrite ?Nat.sub_0_r in *; omega. }
     assert (v = n).
     { destruct (fg_inv n v) as [H'|[H'|H']]; subst;
       simpl in *; rewrite ?Nat.sub_0_r in *; omega. }
     omega.
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
   + replace n with 0 by omega. compute. auto.
 - assert (2 <= a).
   { change 2 with (fg 3). rewrite <- Hn. apply fg_mono. assumption. }
   unfold rchild.
   destruct eq_nat_dec.
   + destruct a as [|[|[|a]]]; trivial; omega.
   + assert (Hn' : 3 < S n) by omega.
     assert (H' := fg_eqn Hn').
     replace (S n - 1) with n in H' by omega.
     rewrite Hn in H'.
     omega.
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
 destruct eq_nat_dec; [intros; omega|intros].
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
   + replace n with 0 by omega; now compute.
 - set (k:=depth n).
   assert (k<>0) by (unfold k; rewrite depth_0; omega).
   assert (S (fib k) <= n <= fib (S k)).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (S (fib k))) as [E|N].
   + rewrite E.
     replace (S (fib k) - 1) with (fib k) by omega.
     unfold lchild.
     destruct eq_nat_dec.
     * generalize (fib_nz k); intros; omega.
     * rewrite flip_Sfib; auto.
       unfold FunG.rchild. rewrite g_fib.
       rewrite <- fib_eqn.
       rewrite flip_fib; auto.
       replace (S (fib (S k)) - 1) with (fib (S k)) by omega.
       apply fg_fib.
   + unfold fg. apply flip_swap.
     assert (1 < lchild n).
     { generalize (fg_onto_eqn' n).
       generalize (@fg_mono (lchild n) 2). change (fg 2) with 1.
       omega. }
     rewrite !flip_pred; auto.
     * unfold lchild.
       destruct eq_nat_dec; [omega|].
       rewrite flip_flip.
       rewrite FunG.rightmost_child_carac; auto.
       apply g_onto_eqn.
     * change (depth n) with k; apply depth_carac; omega.
     * assert (D : depth (lchild n) = S k).
       { unfold k. rewrite <- (fg_onto_eqn' n) at 2.
         rewrite fg_depth. generalize (depth_0 (lchild n)).
         omega. }
       rewrite D.
       apply depth_carac in D; auto.
       assert (lchild n <> S (fib (S k))).
       { contradict N.
         rewrite <- (fg_onto_eqn' n), N. now rewrite fg_Sfib. }
       apply depth_carac; auto. omega.
Qed.

Lemma lchild_leftmost' n a :
  fg n = a -> n = lchild a \/ n = S (lchild a).
Proof.
 intros Hn.
 destruct (fg_inv (lchild a) n) as [H|[H|H]]; try omega.
 - rewrite <- Hn. apply fg_onto_eqn'.
 - exfalso.
   generalize (lchild_leftmost a).
   rewrite H. simpl. rewrite Nat.sub_0_r, Hn.
   intros. replace a with 0 in * by omega.
   discriminate.
Qed.

Lemma rchild_lchild n :
 rchild n = lchild n \/ rchild n = S (lchild n).
Proof.
 apply lchild_leftmost'. apply fg_onto_eqn.
Qed.

Lemma lchild_rchild n : lchild n <= rchild n.
Proof.
 destruct (rchild_lchild n); omega.
Qed.

Lemma fg_children a n :
  fg n = a -> (n = lchild a \/ n = rchild a).
Proof.
 intros H.
 destruct (lchild_leftmost' _ H) as [Hn|Hn]; auto.
 destruct (rchild_lchild a) as [Ha|Ha]; try omega.
 exfalso.
 symmetry in Ha. apply rightmost_child_carac in Ha.
 rewrite <- Hn in Ha. omega.
 apply fg_onto_eqn'.
Qed.

Lemma binary_lchild_is_unary n :
 1<n -> Multary fg n -> Unary fg (lchild n).
Proof.
 rewrite multary_flip, unary_flip.
 unfold lchild.
 destruct eq_nat_dec; try omega.
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
   assert (k<>0) by (unfold k; rewrite depth_0; omega).
   assert (S (fib k) <= n <= fib (S k)).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (fib (S k))) as [E|N].
   + assert (E' : rchild n = fib (S (S k))).
     { symmetry.
       apply rightmost_child_carac.
       - now rewrite fg_fib.
       - rewrite fg_Sfib; auto. }
     rewrite E'.
     rewrite flip_fib; auto.
     replace (S (fib (S k)) - 1) with (fib (S k)) by omega.
     rewrite g_fib.
     rewrite E, flip_swap, flip_fib; auto.
   + assert (1 < rchild n).
     { generalize (fg_onto_eqn n).
       generalize (@fg_mono (rchild n) 2). change (fg 2) with 1.
       omega. }
     rewrite <- flip_S; auto.
     * change (fg (S (rchild n)) <> n).
       assert (H' := fg_onto_eqn n).
       destruct (fg_step (rchild n)); try omega.
       apply rightmost_child_carac in H'. omega.
     * assert (D : depth (rchild n) = S k).
       { unfold k. rewrite <- (fg_onto_eqn n) at 2.
         rewrite fg_depth. generalize (depth_0 (rchild n)).
         omega. }
       rewrite D.
       apply depth_carac in D; auto.
       assert (rchild n <> fib (S (S k))).
       { contradict N.
         rewrite <- (fg_onto_eqn n), N. now rewrite fg_fib. }
       apply depth_carac; auto. omega.
Qed.

Lemma unary_child_is_binary n :
 n <> 0 -> Unary fg n -> Multary fg (rchild n).
Proof.
 intros Hn H.
 destruct (le_lt_dec n 1).
 - replace n with 1 in * by omega.
   exfalso.
   specialize (H 1 2). compute in H. omega.
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
   by (rewrite <- fg_eqn; omega).
 replace n with (S (n-1)) at 3 by omega.
 rewrite g_S.
 replace (S (n-1)) with n by omega.
 rewrite H.
 assert (g (g (n-1)) <= n).
 { transitivity (g (n-1)). apply g_le.
   generalize (g_le (n-1)); omega. }
 omega.
Qed.

Lemma fg_g_eq_inv n : 3<n ->
 fg (S (fg (n-1))) = S (g (g (n-1))) ->
 fg n = g n.
Proof.
 intros Hn H.
 replace (fg n) with (S n - fg (S (fg (n-1))))
   by (rewrite <- fg_eqn; omega).
 replace n with (S (n-1)) at 3 by omega.
 rewrite g_S.
 replace (S (n-1)) with n by omega.
 rewrite H. omega.
Qed.

Lemma g_One n : Fib.One 2 n -> g (S n) = g n.
Proof.
 intros (l & H & Hl).
 rewrite H.
 change (S (sumfib (1::l))) with (sumfib (2::l)).
 rewrite !g_sumfib'; eauto.
Qed.

(** Now, the proof that [fg(n)] is either [g(n)] or [g(n)+1].
    This proof is split in many cases according to the shape
    of the Fibonacci decomposition of [n]. *)

Definition IHeq n :=
 forall m, m<n -> ~Fib.TwoEven 2 m -> fg m = g m.
Definition IHsucc n :=
 forall m, m<n -> Fib.TwoEven 2 m -> fg m = S (g m).

Lemma fg_g_S n : IHeq n -> Fib.TwoEven 2 n -> fg n = S (g n).
Proof.
 intros IH (p & l & E & D).
 assert (2 <= p).
 { destruct p as [|[|p]]; inversion D; omega. }
 assert (7 <= n).
 { generalize (@fib_mono 4 (2*p)). simpl in *. omega. }
 apply fg_g_S_inv; [omega|].
 assert (Hl : forall x, In x l -> 4<=x).
 { intros x Hx. apply Delta_alt in D. apply D. simpl. now right. }
 assert (~In 0 l) by (intro X; apply Hl in X; omega).
 set (l' := map pred l).
 assert (Hl' : map S l' = l) by (unfold l'; now apply map_S_pred).
 assert (~In 0 l').
 { unfold l'. rewrite in_map_iff. intros (x,(Hx,Hx')).
   apply Hl in Hx'. omega. }
 assert (D1 : Delta 1 (1::2*p::l)).
 { apply Delta_low_hd with 2; auto. }
 assert (D2 : Delta 2 (1::2*p-1::l')).
 { apply Delta_pred in D; [|eauto]. simpl in D.
   rewrite Nat.sub_1_r. eauto. }
 assert (E1 : n - 1 = sumfib (1 :: 2*p :: l)).
 { rewrite E. simpl. omega. }
 assert (E2 : g (n-1) = sumfib (1::2*p-1::l')).
 { rewrite E1, g_sumfib'; eauto. simpl. do 3 f_equal. omega. }
 assert (E3 : S (g (n-1)) = sumfib (2::2*p-1::l')).
 { now rewrite E2. }
 assert (F : One 1 (n-1)). { exists (2*p::l). auto. }
 assert (F' : TwoOdd 1 (S (g (n-1)))).
 { exists (p-1); exists l'.
   replace (2*(p-1)+1) with (2*p-1) by omega. auto. }
 rewrite (IH (n-1)) by (auto;omega).
 rewrite IH by (auto; generalize (@g_lt (n-1)); omega).
 apply g_One; auto.
 exists (2*p-1::l'); auto.
Qed.

Lemma fg_g_eq_1 n : IHeq n -> 3<n -> Fib.One 2 n -> fg n = g n.
Proof.
 intros IH H3n (l & E & D).
 apply fg_g_eq_inv; auto.
 assert (Hl : forall x, In x l -> 3<=x).
 { intros x Hx. apply Delta_alt in D. now apply D. }
 assert (~In 0 l) by (intros X; apply Hl in X; omega).
 set (l' := map pred l).
 assert (Hl' : map S l' = l) by (unfold l'; now apply map_S_pred).
 assert (~In 0 l').
 { unfold l'. rewrite in_map_iff. intros (x,(Hx,Hx')).
   apply Hl in Hx'. omega. }
 assert (D1 : Delta 1 (2::l)) by auto.
 assert (D2 : Delta 1 (1::l')). { apply Delta_pred in D1; eauto. }
 assert (E1 : n-1 = sumfib l). { rewrite E. simpl. omega. }
 assert (E2 : g (n-1) = sumfib l'). { rewrite E1, g_sumfib'; eauto. }
 assert (E3 : S (g (n-1)) = sumfib (1::l')). { rewrite E2; auto. }
 assert (F : High 1 (n-1)).
 { destruct l as [|k l]; [simpl in E; omega|].
   exists k; exists l; repeat split; eauto. inversion D; omega. }
 assert (F' : One 1 (S (g (n-1)))).
 { exists l'; auto. }
 rewrite (IH (n-1)) by (auto;omega).
 rewrite IH by (auto; generalize (@g_lt (n-1)); omega).
 rewrite E3, E2.
 rewrite !g_sumfib'; eauto.
Qed.

Lemma fg_g_eq_2 n :
 IHeq n -> IHsucc n -> 3<n -> Fib.TwoOdd 2 n -> fg n = g n.
Proof.
 intros IH1 IH2 H3n (p & l & E & D).
 assert (1<p).
 { destruct p as [|[|p]]; inversion D; omega. }
 apply fg_g_eq_inv; auto.
 assert (Hl : forall x, In x l -> 4<=x).
 { intros x Hx. apply Delta_alt in D. apply D. now right. }
 assert (~In 0 l) by (intro X; apply Hl in X; omega).
 set (l' := map pred l).
 assert (Hl' : map S l' = l) by (unfold l'; now apply map_S_pred).
 assert (~In 0 l').
 { unfold l'. rewrite in_map_iff. intros (x,(Hx,Hx')).
   apply Hl in Hx'. omega. }
 assert (D1 : Delta 1 (1 :: 2*p+1 :: l)).
 { constructor. omega. eauto. }
 assert (D2 : Delta 2 (1 :: 2*p :: l')).
 { apply Delta_pred in D; eauto. simpl in D.
   rewrite Nat.add_1_r in D. auto. }
 assert (E1 : n-1 = sumfib (1 :: 2*p+1 :: l)). { now rewrite E. }
 assert (E2 : g (n-1) = sumfib (1::2*p::l')).
 { rewrite E1, g_sumfib'; eauto. simpl. do 3 f_equal. omega. }
 assert (E3 : S (g (n-1)) = sumfib (2::2*p::l')). { now rewrite E2. }
 assert (F : One 1 (n-1)). { exists (2*p+1::l); auto. }
 assert (F' : TwoEven 2 (S (g (n-1)))).
 { apply TwoEven_equiv. exists p; exists l'; auto. }
 rewrite (IH1 (n-1)) by (auto;omega).
 rewrite IH2 by (auto; generalize (@g_lt (n-1)); omega).
 f_equal.
 apply g_One.
 exists (2*p::l'); auto.
Qed.

Lemma fg_g_eq_3even n k l : IHeq n -> 3<n ->
 n = sumfib (2*k::l) -> 2<=k -> Delta 2 (2*k::l) ->
 fg n = g n.
Proof.
 intros IH H3n E Hk D.
 apply fg_g_eq_inv; auto.
 assert (Hl : forall x, In x l -> 4<=x).
 { intros x Hx. apply Delta_alt in D. apply D in Hx. omega. }
 assert (~In 0 l) by (intro X; apply Hl in X; omega).
 set (l' := map pred l).
 assert (Hl' : map S l' = l) by (unfold l'; now apply map_S_pred).
 assert (~In 0 l').
 { unfold l'. rewrite in_map_iff. intros (x,(Hx,Hx')).
   apply Hl in Hx'. omega. }
 set (l0 := odds k).
 set (l0' := evens (k-2)).
 assert (~In 0 (l0++l)).
 { rewrite in_app_iff. intros [X|X]; [|intuition].
   unfold l0 in X. apply odds_in in X. omega. }
 assert (Hl0 : sumfib l0 = pred (fib (2*k))).
 { unfold l0. apply sumfib_odds. }
 assert (Hl0' : l0 = 1::map S (evens (k-1))).
 { unfold l0. rewrite <- odds_S. f_equal. omega. }
 assert (D1 : Delta 1 (l0++l)).
 { apply Delta_app with (2*k); unfold l0; auto using Delta_odds.
   intros y Hy. apply odds_in in Hy. omega. }
 set (SS := fun x => S (S x)).
 assert (D2 : Delta 1 (1::3::map SS l0' ++ l')).
 { constructor. omega.
   apply (@Delta_app 1 (2*k) (3::map SS l0')).
   - apply Delta_alt. split.
     + apply Delta_map with 2; [|apply Delta_evens].
       intros; unfold SS; omega.
     + intros y. rewrite in_map_iff. intros (x,(<-,Hx)).
       apply evens_in in Hx. unfold SS; omega.
   - apply (@Delta_pred _ (S (2*k)::l)); auto. simpl; intuition.
   - intros y. simpl. rewrite in_map_iff.
     intros [X|(x,(<-,Hx))]. subst y. omega.
     apply evens_in in Hx. unfold SS; omega. }
 assert (D3 : Delta 1 (1::2::map SS l0' ++ l')).
 { constructor. omega. apply Delta_low_hd with 3; eauto. }
 assert (E1 : n-1 = sumfib (l0 ++ l)).
 { rewrite sumfib_app.
   rewrite E, Hl0. generalize (fib_nz (2*k)). simpl. omega. }
 assert (E2 : g (n-1) = sumfib (1::2::map SS l0' ++ l')).
 { unfold l'. rewrite E1, g_sumfib'; auto. rewrite Hl0'.
   simpl. rewrite map_app, map_map, map_id.
   replace (k-1) with (S (k-2)) by omega.
   rewrite <- S_odds, odds_S. simpl. now rewrite map_map. }
 assert (E3 : S (g(n-1)) = sumfib (1::3::map SS l0' ++ l')).
 { now rewrite E2. }
 assert (F1 : One 1 (n-1)).
 { rewrite E1. rewrite Hl0' in D1 |- *.
   exists (map S (evens (k-1)) ++ l); auto. }
 assert (F2 : One 1 (S (g (n-1)))).
 { exists (3::map SS l0' ++ l'); auto. }
 rewrite (IH (n-1)); auto; try omega.
 rewrite IH by (auto; generalize (@g_lt (n-1)); omega).
 rewrite E3, E2.
 rewrite !g_sumfib'; eauto.
Qed.

Lemma fg_g_eq_33 n l : IHeq n -> IHsucc n -> 3<n ->
 n = sumfib (3::l) -> Delta 2 (3::l) ->
 fg n = g n.
Proof.
 intros IH1 IH2 Hn E D.
 apply fg_g_eq_inv; auto.
 assert (Hl : forall x, In x l -> 4<=x).
 { intros x Hx. apply Delta_alt in D. apply D in Hx. omega. }
 assert (~In 0 l) by (intro X; apply Hl in X; omega).
 assert (E1 : n - 1 = sumfib (2::l)). { now rewrite E. }
 destruct l as [|k l]; [simpl in *; omega|].
 assert (5 <= k) by (inversion D; omega).
 assert (11 <= n).
 { rewrite E. simpl. generalize (@fib_mono 5 k).
   change (fib 5) with 8. omega. }
 destruct (Nat.Even_or_Odd k) as [(p,Hp)|(p,Hp)]; subst k.
 - (* next term is even *)
   assert (D1 : Delta 1 (2::2*p::l)).
   { apply Delta_low_hd with 3; auto. }
   assert (D2 : Delta 1 (3 :: 2*p-1 :: map pred l)).
   { constructor. omega.
     apply Delta_pred in D1; eauto. simpl in D1.
     rewrite Nat.sub_1_r; eauto. }
   assert (D3 : Delta 1 (1 :: 2*p-1 :: map pred l)).
   { apply Delta_low_hd with 3; auto. }
   assert (E2 : g (n-1) = sumfib (1::2*p-1::map pred l)).
   { rewrite E1, g_sumfib'; eauto. simpl. do 3 f_equal. omega. }
   assert (E3 : S (S (g (n-1))) = sumfib (3::2*p-1::map pred l)).
   { now rewrite E2. }
   assert (F1 : TwoEven 2 (n-1)).
   { apply TwoEven_equiv. rewrite E1. exists p; exists l; auto. }
   assert (F2 : High 1 (S (S (g (n-1))))).
   { exists 3; exists (2*p-1 :: map pred l); auto. }
   assert (g (n-1) < n-2).
   { generalize (g_lipschitz 5 (n-1)). change (g 5) with 3. omega. }
   rewrite (IH2 (n-1)) by (auto; omega).
   rewrite IH1 by (auto; omega).
   rewrite E3, E2.
   rewrite !g_sumfib'; eauto.
 - (* next term is odd *)
   assert (D1 : Delta 1 (2::2*p+1::l)).
   { apply Delta_low_hd with 3; auto. }
   assert (D2 : Delta 2 (2 :: 2*p :: map pred l)).
   { constructor. omega.
     apply Delta_pred in D; eauto. simpl in D.
     replace (2*p) with (pred (2*p+1)); eauto. omega. }
   assert (D3 : Delta 2 (1 :: 2*p :: map pred l)).
   { apply Delta_low_hd with 2; auto. }
   assert (E2 : g (n-1) = sumfib (1::2*p::map pred l)).
   { rewrite E1, g_sumfib'; eauto. simpl. do 3 f_equal. omega. }
   assert (E3 : S (g (n-1)) = sumfib (2::2*p::map pred l)).
   { now rewrite E2. }
   assert (F1 : TwoOdd 1 (n-1)).
   { rewrite E. exists p; exists l; auto. }
   assert (F2 : TwoEven 2 (S (g (n-1)))).
   { exists p; exists (map pred l); auto. }
   rewrite (IH1 (n-1)) by (auto; omega).
   rewrite IH2; [|generalize (@g_lt (n-1)); omega|auto].
   f_equal.
   apply g_One.
   exists (2*p::map pred l); auto.
Qed.

Lemma fg_g_eq_3odd n k l : IHeq n -> IHsucc n -> 3<n ->
 n = sumfib (2*k+1::l) -> 2<=k -> Delta 2 (2*k+1::l) ->
 fg n = g n.
Proof.
 intros IH1 IH2 Hn E Hk D.
 apply fg_g_eq_inv; auto.
 assert (Hl : forall x, In x l -> 4<=x).
 { intros x Hx. apply Delta_alt in D. apply D in Hx. omega. }
 assert (~In 0 l) by (intro X; apply Hl in X; omega).
 set (l' := map pred l).
 assert (Hl' : map S l' = l) by (unfold l'; now apply map_S_pred).
 assert (~In 0 l').
 { unfold l'. rewrite in_map_iff. intros (x,(Hx,Hx')).
   apply Hl in Hx'. omega. }
 set (l0 := evens k).
 assert (Hl0 : sumfib l0 = pred (fib (2*k+1))).
 { unfold l0. apply sumfib_evens. }
 assert (D1 : Delta 1 (l0++l)).
 { apply Delta_app with (2*k+1); auto.
   - unfold l0. apply Delta_21, Delta_evens.
   - unfold l0. intros y Hy. apply evens_in in Hy. omega. }
 assert (~In 0 (l0++l)).
 { rewrite in_app_iff. intros [X|X]; [|intuition].
   unfold l0 in X. apply evens_in in X. omega. }
 assert (E1 : n - 1 = sumfib (l0 ++ l)).
 { rewrite sumfib_app.
   rewrite E, Hl0. generalize (fib_nz (2*k+1)). simpl; omega. }
 set (S4 := fun x => 4+x).
 set (S3 := fun x => 3+x).
 set (l0' := evens (k-2)).
 assert (E2 : n - 1 = sumfib (2::4::map S4 l0' ++ l)).
 { rewrite E1; unfold l0, l0'.
   replace k with (S (S (k-2))) at 1 by omega.
   rewrite <- S_odds, odds_S, <- S_odds, odds_S.
   simpl map. simpl app. now rewrite !map_map. }
 assert (D2 : Delta 2 (2 :: 4 :: map S4 l0' ++ l)).
 { constructor. omega.
   apply (@Delta_app 2 (2*k+1) (4::map S4 l0')); auto.
   - apply Delta_alt. split.
     + apply Delta_map with 2; [|apply Delta_evens].
       intros; unfold S4; omega.
     + intros y. rewrite in_map_iff. intros (x,(Hx,Hx')).
       apply evens_in in Hx'. unfold S4 in *; omega.
   - intros y. simpl. rewrite in_map_iff. unfold S4.
     intros [X|(x,(<-,Hx))]; try (apply evens_in in Hx); omega. }
 assert (D3 : Delta 1 (1 :: 4 :: map S3 l0' ++ l')).
 { constructor. omega.
   apply Delta_inv in D2.
   assert (0<4) by omega.
   apply Delta_pred in D2; [|eauto]. simpl in D2.
   rewrite map_app, map_map in D2. simpl map in D2. auto. }
 assert (D4 : Delta 1 (1 :: 3 :: map S3 l0' ++ l')).
 { constructor. omega. apply Delta_low_hd with 4; eauto. }
 assert (E3 : g (n-1) = sumfib (1::3::map S3 l0'++l')).
 { rewrite E2, g_sumfib'; eauto.
   simpl. now rewrite map_app, map_map. }
 assert (E4 : S (S (g (n-1))) = sumfib (1::4::map S3 l0' ++ l')).
 { now rewrite E3. }
 assert (F1 : TwoEven 2 (n-1)).
 { exists 2; exists (map S4 l0' ++ l); auto. }
 assert (F2 : One 1 (S (S (g (n-1))))).
 { exists (4::map S3 l0' ++ l'); auto. }
 assert (g (n-1) < n-2).
 { clear - Hk E.
   assert (8 <= n).
   { rewrite E. generalize (@fib_mono 5 (2*k+1)).
     change (fib 5) with 8. simpl. omega. }
   generalize (g_lipschitz 5 (n-1)). change (g 5) with 3.
   omega. }
 rewrite (IH2 (n-1)) by (auto; omega).
 rewrite IH1 by (auto; try omega).
 rewrite E4, E3.
 rewrite !g_sumfib'; eauto.
Qed.

Lemma fg_g_eq_3 n : IHeq n -> IHsucc n -> 3<n ->
 Fib.High 2 n -> fg n = g n.
Proof.
 intros IH1 IH2 Hn (k & l & E & Hk & D).
 destruct (Nat.Even_or_Odd k) as [(p,Hp)|(p,Hp)]; subst k.
 - apply (@fg_g_eq_3even n p l); auto. omega.
 - destruct p as [|[|p]].
   + simpl in *. omega.
   + apply (@fg_g_eq_33 n l); auto.
   + apply (@fg_g_eq_3odd n (S (S p)) l); auto. omega.
Qed.

(** The main result: *)

Lemma fg_g n :
 (Fib.TwoEven 2 n -> fg n = S (g n)) /\
 (~Fib.TwoEven 2 n -> fg n = g n).
Proof.
 induction n  as [n IH] using lt_wf_rec.
 assert (IH1 := fun m (H:m<n) => proj1 (IH m H)).
 assert (IH2 := fun m (H:m<n) => proj2 (IH m H)).
 clear IH.
 split.
 - now apply fg_g_S.
 - intros.
   destruct (le_lt_dec n 3) as [LE|LT].
   + destruct n as [|[|[|n]]]; try reflexivity.
     replace n with 0 by omega. reflexivity.
   + destruct (decomp_complete LT) as [X|[X|[X|X]]].
     * now apply fg_g_eq_1.
     * intuition.
     * now apply fg_g_eq_2.
     * now apply fg_g_eq_3.
Qed.

(** Note: the positions where [fg] and [g] differ start at 7
    and then are separated by 5 or 8 (see [Fib.TwoEven_next]
    and related lemmas). *)

(** Some immediate consequences: *)

Lemma fg_g_step n : fg n = g n \/ fg n = S (g n).
Proof.
 destruct (le_lt_dec n 3) as [LE|LT].
 - left.
   destruct n as [|[|[|n]]]; try reflexivity.
   replace n with 0 by omega. reflexivity.
 - destruct (decomp_complete LT) as [X|[X|[X|X]]].
   * left. apply fg_g. now apply One_not_TwoEven.
   * right. now apply fg_g.
   * left. apply fg_g. now apply TwoOdd_not_TwoEven.
   * left. apply fg_g. now apply High_not_TwoEven.
Qed.

Lemma g_le_fg n : g n <= fg n.
Proof.
 destruct (fg_g_step n); omega.
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
Hint Constructors FD.

Lemma FD_le n k : FD n k -> k <= n.
Proof.
induction 1; auto with arith; omega.
Qed.

Lemma FD_nz n k : FD n k -> 0<n -> 0<k.
Proof.
induction 1; auto with arith; omega.
Qed.

Lemma FD_lt n k : FD n k -> 1<n -> 0<k<n.
Proof.
induction 1; auto with arith; omega.
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
induction H1; inversion 1; subst; auto; try omega; uniq.
Qed.

Lemma FD_step n k k' : FD n k -> FD (S n) k' -> k'=k \/ k' = S k.
Proof.
inversion 2; subst; intros; simpl in *; rewrite ?Nat.sub_0_r in *.
- replace k with 0 by (apply FD_unique with 0; auto). auto.
- replace k with 1 by (apply FD_unique with 1; auto). auto.
- replace k with 1 by (apply FD_unique with 2; auto). auto.
- replace k with 2 by (apply FD_unique with 3; auto). auto.
- replace x with k by (apply FD_unique with n; auto). omega.
- replace y with k by (apply FD_unique with n; auto). omega.
- replace k' with k by (apply FD_unique with n; auto). omega.
Qed.

(** [fg] is an implementation of [FD] (hence the only one). *)

Lemma fg_implements_FD n : FD n (fg n).
Proof.
induction n as [n IH] using lt_wf_rec.
destruct (le_lt_dec n 4) as [Hn|Hn].
- destruct n as [|[|[|[|n]]]]; try constructor.
  replace n with 0 by omega. constructor.
- assert (FD (n-2) (fg (n-2))) by (apply IH; omega).
  assert (FD (n-1) (fg (n-1))) by (apply IH; omega).
  destruct (fg_step (n-2)) as [E|N].
  + replace n with (S (S (n-2))) at 2 by omega.
    rewrite (fg_nonflat (n-2)); auto.
    constructor; auto. rewrite <- E.
    replace (S (n-2)) with (n-1) by omega. auto.
  + replace (S (n-2)) with (n-1) in N by omega.
    set (x := fg (n-2)) in *.
    set (y := fg (n-1)) in *.
    assert (FD y (fg y)).
    { apply IH. unfold y. generalize (fg_le (n-1)); omega. }
    assert (FD (S y) (fg (S y))).
    { apply IH. unfold y. generalize (@fg_lt (n-1)); omega. }
    assert (Hn' : 3 < n) by omega.
    assert (Hn'' : 3 < n-1) by omega.
    assert (EQ := fg_eqn Hn').
    assert (EQ' := fg_eqn Hn'').
    change (fg(n-1)) with y in EQ,EQ'.
    replace (n-1-1) with (n-2) in EQ' by omega.
    change (fg(n-2)) with x in EQ'.
    rewrite <- N in EQ'.
    destruct (fg_step y) as [E'|N'].
    * replace (fg n) with (S y) by omega.
      eapply FD_b; eauto. omega. rewrite <- E'; auto.
    * replace (fg n) with y by omega.
      eapply FD_c; eauto. omega. omega.
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
  + omega.
  + reflexivity.
  + discriminate.
  + reflexivity.
  + replace n with 0 by omega. compute. reflexivity.
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
 - omega.
 - compute in H1. discriminate.
 - compute in H1. discriminate.
 - assert (x = fg(n-1)).
   { eapply FD_unique; eauto using fg_implements_FD. }
   omega.
 - assert (y = fg(n-1)).
   { eapply FD_unique; eauto using fg_implements_FD. }
   omega.
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
 unfold d. destruct (fg_step n); omega.
Qed.

Lemma delta_a n : n<>0 -> d (n-1) = 0 -> d n = 1.
Proof.
 intro Hn.
 unfold d in *.
 generalize (fg_nonflat (n-1)).
 generalize (fg_mono_S (n-1)).
 replace (S (n-1)) with n by omega.
 omega.
Qed.

Lemma delta_b n : 4<=n ->
 d (n-1) = 1 -> d (fg n) = 0 -> d n = 1.
Proof.
 unfold d.
 intros.
 replace (S (n-1)) with n in * by omega.
 rewrite (@fg_b (S n) (fg n)); try omega.
 f_equal. omega.
 simpl. omega.
 generalize (fg_step (fg n)). omega.
Qed.

Lemma delta_c n : 4<=n ->
 d (n-1) = 1 -> d (fg n) = 1 -> d n = 0.
Proof.
 unfold d.
 intros.
 replace (S (n-1)) with n in * by omega.
 rewrite (@fg_c (S n) (fg n)); try omega.
 f_equal. omega.
 simpl. omega.
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
 - simpl. apply delta_a; auto; omega.
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
 assert (LE : S (fib k) <= n <= fib (S k)).
 { apply depth_carac. omega. auto. }
 unfold fg. rewrite flip_flip.
 rewrite flip_eqn0; rewrite !g_depth, flip_depth; [|unfold k in *; omega].
 fold k.
 replace (S (S (k-1-1))) with k by omega.
 destruct (eq_nat_dec n (S (fib k))) as [EQ|NE].
 - rewrite EQ.
   replace (S (fib k) - 1) with (fib k) by omega.
   rewrite flip_Sfib by omega.
   replace k with (S (k-1)) by omega.
   rewrite flip_fib by omega.
   rewrite !g_fib.
   replace (k-1) with (S (k-2)) at 3 by omega.
   rewrite g_Sfib by omega.
   rewrite flip_Sfib by omega.
   replace (S (k-2)) with (k-1) by omega.
   rewrite fib_eqn'; omega.
 - assert (Hk' : depth (n-1) = k).
   { apply depth_carac; omega. }
   rewrite (flip_eqn0 (g _)); rewrite g_depth, flip_depth, Hk';
    [|omega].
   replace (S (k-1)) with k by omega.
   rewrite flip_pred by (unfold k in Hk'; omega).
   rewrite g_S.
   rewrite (flip_eqn0 n) at 2 by (unfold k in Hk; omega).
   fold k.
   assert (Hk'' : depth (g (g (flip n))) = k-2).
   { rewrite !g_depth, flip_depth. unfold k; omega. }
   apply depth_carac in Hk'' ; [|omega].
   rewrite fib_eqn.
   replace (S (k-2)) with (k-1) in * by omega.
   assert (fib (k-1) <= fib k).
   { apply fib_mono. omega. }
   omega.
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
 | _ => if even n then n-2 else 4
 end.

Lemma oups_def n : 7<n -> oups n = if even n then n-2 else 4.
Proof.
 do 8 (destruct n; try omega). reflexivity.
Qed.

Lemma oups_alt_eqn n : 3<n -> oups (oups n) + oups (n-1) = n.
Proof.
intros.
destruct (le_lt_dec n 9).
- do 10 (destruct n; simpl; try omega).
- case_eq (even n); intros E.
  + rewrite (@oups_def n),E,!oups_def by omega.
    rewrite !Nat.even_sub,E by omega. simpl. omega.
  + rewrite (@oups_def n),E by omega. simpl.
    rewrite oups_def by omega.
    rewrite !Nat.even_sub,E by omega. simpl. omega.
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
- destruct n as [|[|[|n]]]; try omega. replace n with 0; omega.
- assert (1 < f (f n) < n).
  { generalize (IH (n-1)) (Hf n). omega. }
  assert (f (f (S n)) + f n = S n).
  { replace n with (S n - 1) at 2 by omega. apply Hf; omega. }
  assert (f n <> 0). { intros E. rewrite E in *. omega. }
  assert (f n <> n). { intros E. rewrite !E in *. omega. }
  assert (f n <> S n).
  { intros E. rewrite E in *. specialize (IH (f (S n))). omega. }
  omega.
Qed.

Lemma alt_bound' f : AltSpec f -> forall n, 0 <= f n <= n.
Proof.
intros Hf [|[|n]].
- replace (f 0) with 0. auto. symmetry. apply Hf.
- replace (f 1) with 1. auto. symmetry. apply Hf.
- generalize (@alt_bound _ Hf (S (S n))). omega.
Qed.

Lemma alt_4 f : AltSpec f -> f 4 = 3.
Proof.
 intros Hf.
 assert (0 < f 4 < 4) by (apply alt_bound; auto).
 assert (f (f 4) + f 3 = 4) by (apply Hf; auto).
 destruct Hf as ((F0 & F1 & F2 & F3),_).
 destruct (f 4) as [|[|[|[|n]]]]; omega.
Qed.

Lemma alt_5 f : AltSpec f -> f 5 = 3.
Proof.
 intros Hf.
 assert (0 < f 5 < 5) by (apply alt_bound; auto).
 assert (f (f 5) + f 4 = 5) by (apply Hf; auto).
 assert (f 4 = 3) by (apply alt_4; auto).
 destruct Hf as ((F0 & F1 & F2 & F3),_).
 destruct (f 5) as [|[|[|[|[|n]]]]]; omega.
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
  omega.
}
intros n m. destruct (le_lt_dec n 3); intros.
- destruct (le_lt_dec m 3); intros.
  + destruct Hf as ((F0 & F1 & F2 & F3), _).
    destruct m as [|[|[|[|m]]]], n as [|[|[|[|n]]]]; omega.
  + specialize (main 4 m). rewrite alt_4 in main; auto.
    destruct Hf as ((F0 & F1 & F2 & F3), _).
    destruct n as [|[|[|[|n]]]]; omega.
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
  destruct n as [|[|[|[|n]]]]; omega.
- assert (f1 (n-1) = f2 (n-1)) by (apply IH; omega).
  assert (f1 (f1 n) = f2 (f2 n)).
  { destruct Hf1 as (_,Hf1), Hf2 as (_,Hf2).
    specialize (Hf1 n). specialize (Hf2 n). omega. }
  set (x1:=f1 n) in *.
  set (x2:=f2 n) in *.
  assert (f1 x1 = f2 x1).
  { apply IH. apply alt_bound; auto. omega. }
  assert (f1 x2 = f2 x2).
  { apply IH. apply alt_bound; auto. omega. }
  assert (f2 (n-1) <= x2 /\ x2-f2(n-1) <= 1).
  { unfold x2; split.
    - generalize (Mon2 (n-1)); replace (S (n-1)) with n; omega.
    - generalize (@alt_mono_bound _ Hf2 Mon2 (n-1) n); omega. }
  assert (f1 (n-1) <= x1 /\ x1-f1(n-1) <= 1).
  { unfold x1; split.
    - generalize (Mon1 (n-1)); replace (S (n-1)) with n; omega.
    - generalize (@alt_mono_bound _ Hf1 Mon1 (n-1) n); omega. }
  destruct (lt_eq_lt_dec x1 x2) as [[LT|EQ]|LT]; trivial; exfalso.
  + (* x1 < x2 *)
    assert (f1 (S x1) <= f1 x2).
    { apply monotone_equiv. apply Mon1. apply LT. }
    assert (f1 (f1 (S n)) = S (f1 x1)).
    { destruct Hf1 as (_,Hf1).
      generalize (Hf1 (S n)) (Hf1 n); simpl.
      rewrite Nat.sub_0_r.
      unfold x1 in *; omega. }
    assert (f1 (f1 (S n)) = f1 (S x1)).
    { f_equal.
      generalize
        (@alt_mono_bound _ Hf1 Mon1 n (S n))
        (@alt_mono_bound _ Hf1 Mon1 x1 (f1 (S n)) (Mon1 n)).
      unfold x1 in *; omega. }
    omega.
  + (* x2 < x1 *)
    assert (f2 (S x2) <= f2 x1).
    { apply monotone_equiv. apply Mon2. apply LT. }
    assert (f2 (f2 (S n)) = S (f2 x2)).
    { destruct Hf2 as (_,Hf2).
      generalize (Hf2 (S n)) (Hf2 n); simpl.
      rewrite Nat.sub_0_r.
      unfold x2 in *; omega. }
    assert (f2 (f2 (S n)) = f2 (S x2)).
    { f_equal.
      generalize
        (@alt_mono_bound _ Hf2 Mon2 n (S n))
        (@alt_mono_bound _ Hf2 Mon2 (f2 n) (f2 (S n)) (Mon2 n)).
      unfold x2 in *; omega. }
    omega.
Qed.

Lemma alt_mono_is_fg f :
  AltSpec f -> (forall n, f n <= f (S n)) ->
  forall n, f n = fg n.
Proof.
 intros Hg Mon. apply alt_mono_unique; auto.
 - split. now compute. apply fg_alt_eqn.
 - apply fg_mono_S.
Qed.
