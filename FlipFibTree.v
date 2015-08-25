
Require Import Arith Omega Wf_nat List Program Program.Wf NPeano.
Require Import DeltaList Fib FibTree.
Set Implicit Arguments.

(** See first the previous file for the study of:

    G (S n) + G (G n) = S n
    G 0 = 0

   and the associated tree where nodes are labeled breadth-first
   from left to right. *)

(** Source: Hofstadter's book: Goedel, Escher, Bach. *)

(** Now, question by Hofstadter: what if we still label the nodes
    from right to left, but for the mirror tree ?
    What is the algebraic definition of the "parent" function
    for this flipped tree ?

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

*)

(*=============================================================*)

(** flip *)

(** If we label the node from right to left, the effect
   on node numbers is the flip function below: *)

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

(** The flipped g' function, corresponding to the flipped G tree *)

Definition g' n := flip (g (flip n)).

(* Compute map g' (seq 0 10). *)

Lemma g'_depth n : depth (g' n) = depth n - 1.
Proof.
 unfold g'. now rewrite flip_depth, g_depth, flip_depth.
Qed.

Lemma g'_fib k : g' (fib (S k)) = fib k.
Proof.
 destruct k.
 - now compute.
 - destruct k.
   + now compute.
   + unfold g'.
     rewrite flip_fib; auto.
     rewrite g_Sfib; auto.
     rewrite flip_Sfib; auto.
Qed.

Lemma g'_Sfib k : k<>0 -> g' (S (fib (S k))) = S (fib k).
Proof.
 intros Hk.
 unfold g'.
 rewrite flip_Sfib; auto.
 rewrite g_fib.
 rewrite flip_fib; auto.
Qed.

Lemma g'_fib' k : k<>0 -> g' (fib k) = fib (k-1).
Proof.
 destruct k.
 - now destruct 1.
 - intros. rewrite Nat.sub_1_r. apply g'_fib.
Qed.

Lemma g'_Sfib' k : 1<k -> g' (S (fib k)) = S (fib (k-1)).
Proof.
 destruct k.
 - inversion 1.
 - intros. rewrite Nat.sub_1_r. apply g'_Sfib. simpl. omega.
Qed.

Lemma g'_step n : g' (S n) = g' n \/ g' (S n) = S (g' n).
Proof.
 destruct (le_lt_dec n 1) as [LE|LT].
 - assert (EQ : n = 0 \/ n = 1) by omega.
   destruct EQ as [-> | ->]; compute; auto.
 - set (k := depth n).
   assert (k<>0) by (unfold k; rewrite depth_0; omega).
   assert (S (fib k) <= n <= fib (S k)).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (fib (S k))) as [EQ|NE].
   + rewrite EQ. rewrite g'_Sfib, g'_fib; auto.
   + assert (depth (S n) = k). { apply depth_carac; omega. }
     assert (depth (flip (S n)) = k). { rewrite flip_depth; auto. }
     assert (1 < flip n). { now apply (flip_high n). }
     unfold g'.
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

Lemma g'_mono_S n : g' n <= g' (S n).
Proof.
 generalize (g'_step n). omega.
Qed.

Lemma g'_mono n m : n<=m -> g' n <= g' m.
Proof.
induction 1.
- trivial.
- transitivity (g' m); auto using g'_mono_S.
Qed.

Lemma g'_lipschitz n m : g' m - g' n <= m - n.
Proof.
destruct (le_ge_dec n m) as [H|H].
- induction H; try generalize (g'_step m); omega.
- generalize (g'_mono H). omega.
Qed.

Lemma g'_nonzero n : 0 < n -> 0 < g' n.
Proof.
 unfold lt. intros. change 1 with (g' 1). now apply g'_mono.
Qed.

Lemma g'_0_inv n : g' n = 0 -> n = 0.
Proof.
destruct n; trivial.
assert (0 < g' (S n)) by (apply g'_nonzero; auto with arith).
omega.
Qed.

Lemma g'_nz n : n <> 0 -> g' n <> 0.
Proof.
intros H. contradict H. now apply g'_0_inv.
Qed.

Lemma g'_fix n : g' n = n <-> n <= 1.
Proof.
 unfold g'.
 now rewrite flip_low, <- g_fix, flip_swap.
Qed.

Lemma g'_le n : g' n <= n.
Proof.
 generalize (g'_lipschitz 0 n). change (g' 0) with 0. omega.
Qed.

Lemma g'_lt n : 1<n -> g' n < n.
Proof.
intros H.
destruct (le_lt_or_eq _ _ (g'_le n)); trivial.
rewrite g'_fix in *. omega.
Qed.

Lemma g'_onto a : exists n, g' n = a.
Proof.
 unfold g'. destruct (g_onto (flip a)) as (x,H).
 exists (flip x). now rewrite flip_swap, flip_flip.
Qed.

Lemma g'_nonflat n : g' (S n) = g' n -> g' (S (S n)) = S (g' n).
Proof.
 intros H.
 destruct (le_lt_dec n 1) as [Hn|Hn].
 - assert (EQ : n = 0 \/ n = 1) by omega.
   destruct EQ as [-> | ->]; reflexivity.
 - destruct (g'_step (S n)) as [H'|H']; [|omega].
   exfalso.
   set (k := depth n).
   assert (Hk : k<>0) by (unfold k; rewrite depth_0; omega).
   assert (Hnk : S (fib k) <= n <= fib (S k)).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (fib (S k))) as [EQ|NE].
   + rewrite EQ in H. rewrite g'_fib, g'_Sfib in H; omega.
   + destruct (eq_nat_dec (S n) (fib (S k))) as [EQ|NE'].
     * rewrite EQ in H'. rewrite g'_fib, g'_Sfib in H'; omega.
     * revert H'. rewrite H; clear H. unfold g'. rewrite flip_eq.
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

Lemma g'_max_two_antecedents n m :
 g' n = g' m -> n < m -> m = S n.
Proof.
 intros H LT.
 unfold lt in LT.
 assert (LE := g'_mono LT).
 rewrite <- H in LE.
 destruct (g'_step n) as [EQ|EQ]; [|omega].
 apply g'_nonflat in EQ.
 destruct (le_lt_dec m (S n)) as [LE'|LT']; [omega|].
 unfold lt in LT'. apply g'_mono in LT'. omega.
Qed.

Lemma g'_inv n m : g' n = g' m -> n = m \/ n = S m \/ m = S n.
Proof.
 intros H.
 destruct (lt_eq_lt_dec n m) as [[LT|EQ]|LT]; auto.
 - apply g'_max_two_antecedents in LT; auto.
 - apply g'_max_two_antecedents in LT; auto.
Qed.

Lemma g'_eqn n : 3 < n -> g' n + g' (S (g' (n-1))) = S n.
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
   rewrite g'_fib', !g'_Sfib' by omega.
   simpl. rewrite Nat.add_succ_r. rewrite <- fib_eqn' by omega.
   do 3 f_equal. omega.
 - (* n > S (fib k) *)
   assert (Hk : depth (n-1) = k).
   { apply depth_carac; omega. }
   assert (Hk' : depth (g' (n-1)) = k-1).
   { now rewrite g'_depth, Hk. }
   assert (LE' : S (fib (k-1)) <= g' (n-1) <= fib k).
   { replace k with (S (k-1)) at 2 by omega.
     apply depth_carac; auto. omega. }
   destruct (eq_nat_dec (g' (n-1)) (fib k)) as [EQ|NE'].
   + (* g'(n-1) = fib k *)
     rewrite EQ.
     rewrite g'_Sfib' by omega.
     assert (EQ' : g' n = fib k).
     { destruct (g'_step (n-1)) as [EQ'|EQ'];
       replace (S (n-1)) with n in EQ'; try omega.
       rewrite EQ in EQ'.
       assert (H' : depth (g' n) = k) by (apply depth_carac; omega).
       rewrite g'_depth in H'. unfold k in *. omega. }
     rewrite EQ'.
     rewrite Nat.add_succ_r. rewrite <- fib_eqn' by omega.
     f_equal.
     assert (EQ'' : g' (n-1) = g' (fib (S k))) by now rewrite EQ, g'_fib.
     apply g'_max_two_antecedents in EQ''; omega.
   + (* g'(n-1) <> fib k *)
     assert (Hk'' : depth (S (g' (n-1))) = k-1).
     { apply depth_carac. omega.
       replace (S (k-1)) with k by omega.
       omega. }
     unfold g' at 2.
     rewrite flip_eqn0;
     rewrite g_depth, flip_depth, Hk''; [|omega].
     replace (S (S (k-1-1))) with k by omega.
     assert (LT : 1 < g' (n-1)).
     { unfold lt. change 2 with (g' 3). apply g'_mono. omega. }
     rewrite flip_S by omega.
     unfold g' at 2. rewrite flip_flip.
     rewrite flip_pred; try (unfold k in Hk; omega).
     clear LT Hk'' NE' LE' Hk Hk'.
     replace (g (g (S (flip n)) - 1)) with (flip n - g (flip n))
     by (generalize (g_alt_eqn (flip n)); omega).
     rewrite <- (flip_flip (g (flip n))).
     fold (g' n).
     rewrite !flip_eqn0 by (rewrite ?g'_depth; unfold k in H; omega).
     rewrite g'_depth.
     change (depth n) with k.
     replace (S (k-1)) with k by omega.
     rewrite fib_eqn.
     assert (Hnk : depth (g' n) = k-1).
     { rewrite g'_depth. unfold k. omega. }
     apply depth_carac in Hnk; [|omega].
     replace (S (k-1)) with k in Hnk by omega.
     replace (fib (k-1)) with (fib (S k) - fib k) in Hnk;
      [|rewrite fib_eqn'; omega].
     set (FSK := fib (S k)) in *.
     set (FK := fib k) in *.
     replace (S (FSK+FK) -n - (S FSK - g' n))
      with (FK + g' n - n) by omega.
     omega.
Qed.

(** This equation, along with initial values up to n=3,
    characterizes g' entirely. *)

Lemma g'_eqn_unique f :
  f 0 = 0 ->
  f 1 = 1 ->
  f 2 = 1 ->
  f 3 = 2 ->
  (forall n, 3<n -> f n + f (S (f (n-1))) = S n) ->
  forall n, f n = g' n.
Proof.
 intros F0 F1 F2 F3 Fn.
 induction n as [n IH] using lt_wf_rec.
 destruct (le_lt_dec n 3) as [Hn|Hn].
 - destruct n as [|[|[|n]]]; try assumption.
   replace n with 0 by omega. assumption.
 - assert (E := g'_eqn Hn).
   specialize (Fn n Hn).
   rewrite (IH (n-1)) in Fn by omega.
   rewrite (IH (S (g' (n-1)))) in Fn.
   + generalize (@g'_lt n). omega.
   + generalize (@g'_lt (n-1)). omega.
Qed.

(*=============================================================*)

(** g' and the shape of its tree *)

(** - we already know that g' is onto, hence each node has
      at least a child
    - Cf g_max_two_antecedents : at most two children per node. *)

Lemma unary_flip a : Unary g' a <-> Unary g (flip a).
Proof.
 split; intros U n m Hn Hm; apply flip_eq; apply U;
 unfold g' in *; rewrite ?flip_flip; now apply flip_swap.
Qed.

Lemma multary_flip a : Multary g' a <-> Multary g (flip a).
Proof.
 unfold Multary.
 now rewrite unary_flip.
Qed.

Lemma g'_multary_binary a : Multary g' a <-> Binary g' a.
Proof.
 unfold Multary.
 split.
 - intros U.
   assert (Ha : a<>0).
   { contradict U.
     subst.
     intros u v Hu Hv. apply g'_0_inv in Hu. apply g'_0_inv in Hv.
     now subst. }
   destruct (g'_onto a) as (n,Hn).
   assert (Hn' : n<>0).
   { contradict Ha. now subst. }
   destruct (eq_nat_dec (g' (S n)) a);
   destruct (eq_nat_dec (g' (n-1)) a).
   + exfalso.
     generalize (@g'_max_two_antecedents (n-1) (S n)). omega.
   + exists n; exists (S n); repeat split; auto.
     intros k Hk.
     destruct (g'_inv n k) as [H|[H|H]]; try omega.
     subst n. simpl in *. rewrite Nat.sub_0_r in *. omega.
   + exists n; exists (n-1); repeat split; auto; try omega.
     intros k Hk.
     destruct (g'_inv n k) as [H|[H|H]]; try omega.
     subst k. omega.
   + elim U.
     intros u v Hu Hv.
     assert (u = n).
     { destruct (g'_inv n u) as [H|[H|H]]; subst;
       simpl in *; rewrite ?Nat.sub_0_r in *; omega. }
     assert (v = n).
     { destruct (g'_inv n v) as [H'|[H'|H']]; subst;
       simpl in *; rewrite ?Nat.sub_0_r in *; omega. }
     omega.
 - intros (n & m & Hn & Hm & Hnm & H) U.
   apply Hnm. now apply (U n m).
Qed.

Lemma unary_or_multary n : Unary g' n \/ Multary g' n.
Proof.
 rewrite unary_flip, multary_flip.
 apply unary_or_multary.
Qed.

Lemma unary_xor_multary n : Unary g' n -> Multary g' n -> False.
Proof.
 unfold Multary. intuition.
Qed.

(** We could even exhibit at least one child for each node *)

Definition rchild' n :=
 if eq_nat_dec n 1 then 2 else n + g' (S n) - 1.
 (** rightmost son, always there *)

Lemma rightmost_child_carac a n : g' n = a ->
 (g' (S n) = S a <-> n = rchild' a).
Proof.
 intros Hn.
 destruct (le_lt_dec n 2).
 - rewrite <- Hn.
   destruct n as [|[|n]].
   + compute. auto.
   + compute. auto.
   + replace n with 0 by omega. compute. auto.
 - assert (2 <= a).
   { change 2 with (g' 3). rewrite <- Hn. apply g'_mono. assumption. }
   unfold rchild'.
   destruct eq_nat_dec.
   + destruct a as [|[|[|a]]]; trivial; omega.
   + assert (Hn' : 3 < S n) by omega.
     assert (H' := g'_eqn Hn').
     replace (S n - 1) with n in H' by omega.
     rewrite Hn in H'.
     omega.
Qed.

Lemma g'_onto_eqn a : g' (rchild' a) = a.
Proof.
destruct (g'_onto a) as (n,Hn).
destruct (g'_step n) as [H|H].
- assert (H' := g'_nonflat _ H).
  rewrite Hn in *.
  rewrite rightmost_child_carac in H'; auto.
  now rewrite <- H'.
- rewrite Hn in *.
  rewrite rightmost_child_carac in H; auto.
  now rewrite <- H.
Qed.

Definition lchild' n :=
 if eq_nat_dec n 1 then 1 else flip (rchild (flip n)).
 (** leftmost son, always there (but might be equal to
     the rightmost son for unary nodes) *)

Lemma lchild'_alt n : n<>1 -> lchild' n = flip (flip n + flip (g' n)).
Proof.
 unfold lchild', rchild, g'.
 destruct eq_nat_dec; [intros; omega|intros].
 f_equal. f_equal.
 symmetry. apply flip_flip.
Qed.

Lemma g'_onto_eqn' n : g' (lchild' n) = n.
Proof.
 unfold g', lchild'.
 destruct eq_nat_dec.
 - now subst.
 - rewrite flip_flip, g_onto_eqn.
   apply flip_flip.
Qed.

Lemma lchild'_leftmost n : g' (lchild' n - 1) = n - 1.
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
     unfold lchild'.
     destruct eq_nat_dec.
     * generalize (fib_nz k); intros; omega.
     * rewrite flip_Sfib; auto.
       unfold rchild. rewrite g_fib.
       rewrite <- fib_eqn.
       rewrite flip_fib; auto.
       replace (S (fib (S k)) - 1) with (fib (S k)) by omega.
       apply g'_fib.
   + unfold g'. apply flip_swap.
     assert (1 < lchild' n).
     { generalize (g'_onto_eqn' n).
       generalize (@g'_mono (lchild' n) 2). change (g' 2) with 1.
       omega. }
     rewrite !flip_pred; auto.
     * unfold lchild'.
       destruct eq_nat_dec; [omega|].
       rewrite flip_flip.
       rewrite FibTree.rightmost_child_carac; auto.
       apply g_onto_eqn.
     * change (depth n) with k; apply depth_carac; omega.
     * assert (D : depth (lchild' n) = S k).
       { unfold k. rewrite <- (g'_onto_eqn' n) at 2.
         rewrite g'_depth. generalize (depth_0 (lchild' n)).
         omega. }
       rewrite D.
       apply depth_carac in D; auto.
       assert (lchild' n <> S (fib (S k))).
       { contradict N.
         rewrite <- (g'_onto_eqn' n), N. now rewrite g'_Sfib. }
       apply depth_carac; auto. omega.
Qed.

Lemma lchild'_leftmost' n a :
  g' n = a -> n = lchild' a \/ n = S (lchild' a).
Proof.
 intros Hn.
 destruct (g'_inv (lchild' a) n) as [H|[H|H]]; try omega.
 - rewrite <- Hn. apply g'_onto_eqn'.
 - exfalso.
   generalize (lchild'_leftmost a).
   rewrite H. simpl. rewrite Nat.sub_0_r, Hn.
   intros. replace a with 0 in * by omega.
   discriminate.
Qed.

Lemma rchild'_lchild' n :
 rchild' n = lchild' n \/ rchild' n = S (lchild' n).
Proof.
 apply lchild'_leftmost'. apply g'_onto_eqn.
Qed.

Lemma lchild'_rchild' n : lchild' n <= rchild' n.
Proof.
 destruct (rchild'_lchild' n); omega.
Qed.

Lemma g'_children a n :
  g' n = a -> (n = lchild' a \/ n = rchild' a).
Proof.
 intros H.
 destruct (lchild'_leftmost' _ H) as [Hn|Hn]; auto.
 destruct (rchild'_lchild' a) as [Ha|Ha]; try omega.
 exfalso.
 symmetry in Ha. apply rightmost_child_carac in Ha.
 rewrite <- Hn in Ha. omega.
 apply g'_onto_eqn'.
Qed.

Lemma binary_lchild_is_unary n :
 1<n -> Multary g' n -> Unary g' (lchild' n).
Proof.
 rewrite multary_flip, unary_flip.
 unfold lchild'.
 destruct eq_nat_dec; try omega.
 rewrite flip_flip.
 intros. now apply binary_rchild_is_unary.
Qed.

Lemma rightmost_son_is_binary n :
  1<n -> Multary g' (rchild' n).
Proof.
 intros.
 rewrite multary_flip.
 apply leftmost_son_is_binary with (flip n).
 - apply flip_swap. apply g'_onto_eqn.
 - rewrite <- flip_swap.
   set (k:=depth n).
   assert (k<>0) by (unfold k; rewrite depth_0; omega).
   assert (S (fib k) <= n <= fib (S k)).
   { apply depth_carac; auto. }
   destruct (eq_nat_dec n (fib (S k))) as [E|N].
   + assert (E' : rchild' n = fib (S (S k))).
     { symmetry.
       apply rightmost_child_carac.
       - now rewrite g'_fib.
       - rewrite g'_Sfib; auto. }
     rewrite E'.
     rewrite flip_fib; auto.
     replace (S (fib (S k)) - 1) with (fib (S k)) by omega.
     rewrite g_fib.
     rewrite E, flip_swap, flip_fib; auto.
   + assert (1 < rchild' n).
     { generalize (g'_onto_eqn n).
       generalize (@g'_mono (rchild' n) 2). change (g' 2) with 1.
       omega. }
     rewrite <- flip_S; auto.
     * change (g' (S (rchild' n)) <> n).
       assert (H' := g'_onto_eqn n).
       destruct (g'_step (rchild' n)); try omega.
       apply rightmost_child_carac in H'. omega.
     * assert (D : depth (rchild' n) = S k).
       { unfold k. rewrite <- (g'_onto_eqn n) at 2.
         rewrite g'_depth. generalize (depth_0 (rchild' n)).
         omega. }
       rewrite D.
       apply depth_carac in D; auto.
       assert (rchild' n <> fib (S (S k))).
       { contradict N.
         rewrite <- (g'_onto_eqn n), N. now rewrite g'_fib. }
       apply depth_carac; auto. omega.
Qed.

Lemma unary_child_is_binary n :
 n <> 0 -> Unary g' n -> Multary g' (rchild' n).
Proof.
 intros Hn H.
 destruct (le_lt_dec n 1).
 - replace n with 1 in * by omega.
   exfalso.
   specialize (H 1 2). compute in H. omega.
 - now apply rightmost_son_is_binary.
Qed.

Lemma binary_rchild_is_binary n :
 1<n -> Multary g' n -> Multary g' (rchild' n).
Proof.
 intros. now apply rightmost_son_is_binary.
Qed.


(** Hence the shape of the g' tree is a repetition of this pattern:

    q
    |
    p   p'
    |   |
    --n--
      |

  where n,p',q are binary nodes and p is unary.
  And in q and p', there is the whole tree again
  (apart from special nodes 0 1 2).
  As expected, this is the mirror of the G tree.
*)


(*=============================================================*)

(** Comparison between g' and g *)

(** First, a few technical lemmas *)

Lemma g'_g_S_inv n : 3<n ->
 g' (S (g' (n-1))) = g (g (n-1)) ->
 g' n = S (g n).
Proof.
 intros Hn H.
 replace (g' n) with (S n - g' (S (g' (n-1))))
   by (rewrite <- g'_eqn; omega).
 replace n with (S (n-1)) at 3 by omega.
 rewrite g_S.
 replace (S (n-1)) with n by omega.
 rewrite H.
 assert (g (g (n-1)) <= n).
 { transitivity (g (n-1)). apply g_le.
   generalize (g_le (n-1)); omega. }
 omega.
Qed.

Lemma g'_g_eq_inv n : 3<n ->
 g' (S (g' (n-1))) = S (g (g (n-1))) ->
 g' n = g n.
Proof.
 intros Hn H.
 replace (g' n) with (S n - g' (S (g' (n-1))))
   by (rewrite <- g'_eqn; omega).
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
 assert (Delta 1 (2::l)).
 { apply Delta_alt in Hl; apply Delta_alt. split.
   + apply Delta_21. apply Hl.
   + intros y Hy. apply Hl in Hy. auto. }
 rewrite !g_sumfib'; eauto.
Qed.

(** Now, the proof that g' is either g or g+1, separated
    in many cases according to the shape of the Fibonacci
    decomposition. *)

Definition IHeq n :=
 forall m, m<n -> ~Fib.TwoEven 2 m -> g' m = g m.
Definition IHsucc n :=
 forall m, m<n -> Fib.TwoEven 2 m -> g' m = S (g m).

Lemma g'_g_S n : IHeq n -> Fib.TwoEven 2 n -> g' n = S (g n).
Proof.
 intros IH (p & l & E & D).
 assert (2 <= p).
 { destruct p as [|[|p]]; inversion D; omega. }
 assert (7 <= n).
 { generalize (@fib_mono 4 (2*p)). simpl in *. omega. }
 apply g'_g_S_inv; [omega|].
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
 { apply Delta_pred in D; eauto. simpl in D.
   rewrite Nat.sub_1_r. eauto. }
 assert (D3 : Delta 1 (2::2*p-1::l')).
 { constructor. omega. eauto. }
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

Lemma g'_g_eq_1 n : IHeq n -> 3<n -> Fib.One 2 n -> g' n = g n.
Proof.
 intros IH H3n (l & E & D).
 apply g'_g_eq_inv; auto.
 assert (Hl : forall x, In x l -> 3<=x).
 { intros x Hx. apply Delta_alt in D. now apply D. }
 assert (~In 0 l) by (intros X; apply Hl in X; omega).
 set (l' := map pred l).
 assert (Hl' : map S l' = l) by (unfold l'; now apply map_S_pred).
 assert (~In 0 l').
 { unfold l'. rewrite in_map_iff. intros (x,(Hx,Hx')).
   apply Hl in Hx'. omega. }
 assert (D1 : Delta 1 (2::l)). { apply Delta_alt; eauto. }
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

Lemma g'_g_eq_2 n :
 IHeq n -> IHsucc n -> 3<n -> Fib.TwoOdd 2 n -> g' n = g n.
Proof.
 intros IH1 IH2 H3n (p & l & E & D).
 assert (1<p).
 { destruct p as [|[|p]]; inversion D; omega. }
 apply g'_g_eq_inv; auto.
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
 { constructor. omega.
   apply Delta_pred in D; eauto. simpl in D.
   rewrite Nat.add_1_r in D. eauto. }
 assert (D3 : Delta 1 (2 :: 2*p :: l')).
 { constructor. omega. eauto. }
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

Lemma g'_g_eq_3even n k l : IHeq n -> 3<n ->
 n = sumfib (2*k::l) -> 2<=k -> Delta 2 (2*k::l) ->
 g' n = g n.
Proof.
 intros IH H3n E Hk D.
 apply g'_g_eq_inv; auto.
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
   - apply (@Delta_pred _ (S (2*k)::l)).
     + simpl; intuition.
     + apply Delta_alt. apply Delta_alt in D.
       split.  apply Delta_21, D.
       intros y Hy. apply D in Hy. omega.
   - intros y. simpl. rewrite in_map_iff.
     intros [X|(x,(<-,Hx))]. subst y. omega.
     apply evens_in in Hx. unfold SS; omega. }
 assert (D3 : Delta 1 (1::2::map SS l0' ++ l')).
 { constructor. omega.
   apply Delta_alt; split; eauto.
   intros y Hy. apply Delta_inv, Delta_alt in D2.
   apply D2 in Hy. omega. }
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

Lemma g'_g_eq_33 n l : IHeq n -> IHsucc n -> 3<n ->
 n = sumfib (3::l) -> Delta 2 (3::l) ->
 g' n = g n.
Proof.
 intros IH1 IH2 Hn E D.
 apply g'_g_eq_inv; auto.
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
   { constructor. omega. eauto. }
   assert (D2 : Delta 1 (3 :: 2*p-1 :: map pred l)).
   { constructor. omega.
     apply Delta_pred in D1; eauto. simpl in D1.
     rewrite Nat.sub_1_r; eauto. }
   assert (D3 : Delta 1 (1 :: 2*p-1 :: map pred l)).
   { constructor. omega. eauto. }
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
   { constructor. omega. eauto. }
   assert (D2 : Delta 2 (2 :: 2*p :: map pred l)).
   { constructor. omega.
     apply Delta_pred in D; eauto. simpl in D.
     replace (2*p) with (pred (2*p+1)); eauto. omega. }
   assert (D3 : Delta 2 (1 :: 2*p :: map pred l)).
   { constructor. omega. eauto. }
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

Lemma g'_g_eq_3odd n k l : IHeq n -> IHsucc n -> 3<n ->
 n = sumfib (2*k+1::l) -> 2<=k -> Delta 2 (2*k+1::l) ->
 g' n = g n.
Proof.
 intros IH1 IH2 Hn E Hk D.
 apply g'_g_eq_inv; auto.
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
     + apply Delta_map with 2.
       intros; unfold S4; omega.
       apply Delta_evens.
     + intros y. rewrite in_map_iff. intros (x,(Hx,Hx')).
       unfold S4 in Hx.
       apply evens_in in Hx'. omega.
   - intros y. simpl. rewrite in_map_iff. unfold S4.
     intros [X|(x,(<-,Hx))]. omega.
     apply evens_in in Hx. omega. }
 assert (D3 : Delta 1 (1 :: 4 :: map S3 l0' ++ l')).
 { constructor. omega.
   apply Delta_inv in D2.
   assert (0<4) by omega.
   apply Delta_pred in D2; eauto. simpl in D2.
   rewrite map_app, map_map in D2.
   change (fun x => pred (S4 x)) with S3 in *.
   apply Delta_alt in D2. destruct D2 as (D2,D2').
   apply Delta_alt. split; [eauto|].
   intros y Hy. apply D2' in Hy. omega. }
 assert (D4 : Delta 1 (1 :: 3 :: map S3 l0' ++ l')).
 { constructor. omega.
   apply Delta_alt. split; [eauto|].
   apply Delta_inv, Delta_alt in D3.
   intros y Hy. apply D3 in Hy. omega. }
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

Lemma g'_g_eq_3 n : IHeq n -> IHsucc n -> 3<n ->
 Fib.High 2 n -> g' n = g n.
Proof.
 intros IH1 IH2 Hn (k & l & E & Hk & D).
 destruct (Nat.Even_or_Odd k) as [(p,Hp)|(p,Hp)]; subst k.
 - apply (@g'_g_eq_3even n p l); auto. omega.
 - destruct p as [|[|p]].
   + simpl in *. omega.
   + apply (@g'_g_eq_33 n l); auto.
   + apply (@g'_g_eq_3odd n (S (S p)) l); auto. omega.
Qed.

Lemma g'_g n :
 (Fib.TwoEven 2 n -> g' n = S (g n)) /\
 (~Fib.TwoEven 2 n -> g' n = g n).
Proof.
 induction n  as [n IH] using lt_wf_rec.
 assert (IH1 := fun m (H:m<n) => proj1 (IH m H)).
 assert (IH2 := fun m (H:m<n) => proj2 (IH m H)).
 clear IH.
 split.
 - now apply g'_g_S.
 - intros.
   destruct (le_lt_dec n 3) as [LE|LT].
   + destruct n as [|[|[|n]]]; try reflexivity.
     replace n with 0 by omega. reflexivity.
   + destruct (decomp_complete LT) as [X|[X|[X|X]]].
     * now apply g'_g_eq_1.
     * intuition.
     * now apply g'_g_eq_2.
     * now apply g'_g_eq_3.
Qed.

Lemma g'_g_step n : g' n = g n \/ g' n = S (g n).
Proof.
 destruct (le_lt_dec n 3) as [LE|LT].
 - left.
   destruct n as [|[|[|n]]]; try reflexivity.
   replace n with 0 by omega. reflexivity.
 - destruct (decomp_complete LT) as [X|[X|[X|X]]].
   * left. apply g'_g. now apply One_not_TwoEven.
   * right. now apply g'_g.
   * left. apply g'_g. now apply TwoOdd_not_TwoEven.
   * left. apply g'_g. now apply High_not_TwoEven.
Qed.

Lemma g_le_g' n : g n <= g' n.
Proof.
 destruct (g'_g_step n); omega.
Qed.


(*=============================================================*)

(** g' and "delta" equations *)

(** We can characterize g' via its "delta" (a.k.a increments).
   Let d(n) = g'(n+1)-g'(n).  For n>3 :

   a) if d(n-1) = 0 then d(n) = 1
   b) if d(n-1) <> 0 and d(g'(n)) = 0 then d(n) = 1
   c) if d(n-1) <> 0 and d(g'(n)) <> 0 then d(n) = 0

   In fact these deltas are always 0 or 1.
*)

(** GD' is a relational presentation of these equations. *)

Inductive GD' : nat -> nat -> Prop :=
 | GD'_0 : GD' 0 0
 | GD'_1 : GD' 1 1
 | GD'_2 : GD' 2 1
 | GD'_3 : GD' 3 2
 | GD'_4 : GD' 4 3
 | GD'_a n x : 4<n -> GD' (n-2) x -> GD' (n-1) x -> GD' n (S x)
 | GD'_b n x y z : 4<n -> GD' (n-2) x -> GD' (n-1) y -> x<>y ->
                   GD' y z -> GD' (S y) z -> GD' n (S y)
 | GD'_c n x y z t : 4<n -> GD' (n-2) x -> GD' (n-1) y -> x<>y ->
                     GD' y z -> GD' (S y) t -> z <> t -> GD' n y.
Hint Constructors GD'.

Lemma GD'_le n k : GD' n k -> k <= n.
Proof.
induction 1; auto with arith; omega.
Qed.

Lemma GD'_nz n k : GD' n k -> 0<n -> 0<k.
Proof.
induction 1; auto with arith; omega.
Qed.

Lemma GD'_lt n k : GD' n k -> 1<n -> 0<k<n.
Proof.
induction 1; auto with arith; omega.
Qed.

Ltac uniq :=
match goal with
| U:forall k, GD' ?x k -> _, V:GD' ?x ?y |- _ =>
   apply U in V; try subst y; uniq
| U:?x<>?x |- _ => now elim U
end.

Lemma GD'_unique n k k' : GD' n k -> GD' n k' -> k = k'.
Proof.
intros H1.
revert k'.
induction H1; inversion 1; subst; auto; try omega; uniq.
Qed.

Lemma GD'_step n k k' : GD' n k -> GD' (S n) k' -> k'=k \/ k' = S k.
Proof.
inversion 2; subst; intros; simpl in *; rewrite ?Nat.sub_0_r in *.
- replace k with 0 by (apply GD'_unique with 0; auto). auto.
- replace k with 1 by (apply GD'_unique with 1; auto). auto.
- replace k with 1 by (apply GD'_unique with 2; auto). auto.
- replace k with 2 by (apply GD'_unique with 3; auto). auto.
- replace x with k by (apply GD'_unique with n; auto). omega.
- replace y with k by (apply GD'_unique with n; auto). omega.
- replace k' with k by (apply GD'_unique with n; auto). omega.
Qed.

(** g' is an implementation of GD' (hence the only one). *)

Lemma g'_implements_GD' n : GD' n (g' n).
Proof.
induction n as [n IH] using lt_wf_rec.
destruct (le_lt_dec n 4) as [Hn|Hn].
- destruct n as [|[|[|[|n]]]]; try constructor.
  replace n with 0 by omega. constructor.
- assert (GD' (n-2) (g' (n-2))) by (apply IH; omega).
  assert (GD' (n-1) (g' (n-1))) by (apply IH; omega).
  destruct (g'_step (n-2)) as [E|N].
  + replace n with (S (S (n-2))) at 2 by omega.
    rewrite (g'_nonflat (n-2)); auto.
    constructor; auto. rewrite <- E.
    replace (S (n-2)) with (n-1) by omega. auto.
  + replace (S (n-2)) with (n-1) in N by omega.
    set (x := g' (n-2)) in *.
    set (y := g' (n-1)) in *.
    assert (GD' y (g' y)).
    { apply IH. unfold y. generalize (g'_le (n-1)); omega. }
    assert (GD' (S y) (g' (S y))).
    { apply IH. unfold y. generalize (@g'_lt (n-1)); omega. }
    assert (Hn' : 3 < n) by omega.
    assert (Hn'' : 3 < n-1) by omega.
    assert (EQ := g'_eqn Hn').
    assert (EQ' := g'_eqn Hn'').
    change (g'(n-1)) with y in EQ,EQ'.
    replace (n-1-1) with (n-2) in EQ' by omega.
    change (g'(n-2)) with x in EQ'.
    rewrite <- N in EQ'.
    destruct (g'_step y) as [E'|N'].
    * replace (g' n) with (S y) by omega.
      eapply GD'_b; eauto. omega. rewrite <- E'; auto.
    * replace (g' n) with y by omega.
      eapply GD'_c; eauto. omega. omega.
Qed.

Lemma gd'_unique n k : GD' n k <-> k = g' n.
Proof.
split.
- intros. eapply GD'_unique; eauto. apply g'_implements_GD'.
- intros ->. apply g'_implements_GD'.
Qed.

(** The three situations a) b) c) expressed in terms of g'. *)

Lemma g'_a n : 0<n -> g' (n-2) = g' (n-1) -> g' n = S (g' (n-1)).
Proof.
destruct (le_lt_dec n 4).
- destruct n as [|[|[|[|n]]]].
  + omega.
  + reflexivity.
  + discriminate.
  + reflexivity.
  + replace n with 0 by omega. compute. reflexivity.
- intros.
  symmetry. apply gd'_unique.
  apply GD'_a; auto using g'_implements_GD'.
  now apply gd'_unique.
Qed.

Lemma g'_b n y : 4<n ->
 y = g' (n-1) ->
 g' (n-2) <> y ->
 g' (S y) = g' y ->
 g' n = S y.
Proof.
 intros.
 symmetry. apply gd'_unique.
 apply (@GD'_b n (g' (n-2)) y (g' y));
  auto using g'_implements_GD'.
 - subst. apply g'_implements_GD'.
 - now apply gd'_unique.
Qed.

Lemma g'_c n y : 4<n ->
 y = g' (n-1) ->
 g' (n-2) <> y ->
 g' (S y) <> g' y ->
 g' n = y.
Proof.
 intros.
 symmetry. apply gd'_unique.
 apply (@GD'_c n (g' (n-2)) y (g' y) (g' (S y)));
  auto using g'_implements_GD'.
 subst. apply g'_implements_GD'.
Qed.

(** An old auxiliary lemma stating the converse of the c) case *)

Lemma g'_c_inv n :
  2<n -> g' n = g' (n-1) -> g' (S (g' n)) = S (g' (g' n)).
Proof.
 intros Hn Hg.
 symmetry in Hg. apply gd'_unique in Hg.
 remember g' as f eqn:Hf.
 inversion Hg; subst.
 - reflexivity.
 - compute in H1. discriminate.
 - omega.
 - compute in H1. discriminate.
 - compute in H1. discriminate.
 - assert (x = g'(n-1)).
   { eapply GD'_unique; eauto using g'_implements_GD'. }
   omega.
 - assert (y = g'(n-1)).
   { eapply GD'_unique; eauto using g'_implements_GD'. }
   omega.
 - set (y := g'(n-1)) in *.
   assert (y = g' n).
   { eapply GD'_unique with n; eauto using g'_implements_GD'. }
   assert (z = g' y).
   { eapply GD'_unique; eauto using g'_implements_GD'. }
   assert (t = g' (S y)).
   { eapply GD'_unique; eauto using g'_implements_GD'. }
   destruct (g'_step y); congruence.
Qed.

(** Presentation via a "delta" function *)

Definition d n := g' (S n) - g' n.

Lemma delta_0_1 n : d n = 0 \/ d n = 1.
Proof.
 unfold d. destruct (g'_step n); omega.
Qed.

Lemma delta_a n : n<>0 -> d (n-1) = 0 -> d n = 1.
Proof.
 intro Hn.
 unfold d in *.
 generalize (g'_nonflat (n-1)).
 generalize (g'_mono_S (n-1)).
 replace (S (n-1)) with n by omega.
 omega.
Qed.

Lemma delta_b n : 4<=n ->
 d (n-1) = 1 -> d (g' n) = 0 -> d n = 1.
Proof.
 unfold d.
 intros.
 replace (S (n-1)) with n in * by omega.
 rewrite (@g'_b (S n) (g' n)); try omega.
 f_equal. omega.
 simpl. omega.
 generalize (g'_step (g' n)). omega.
Qed.

Lemma delta_c n : 4<=n ->
 d (n-1) = 1 -> d (g' n) = 1 -> d n = 0.
Proof.
 unfold d.
 intros.
 replace (S (n-1)) with n in * by omega.
 rewrite (@g'_c (S n) (g' n)); try omega.
 f_equal. omega.
 simpl. omega.
Qed.

Lemma delta_bc n : 4<=n -> d (n-1) = 1 -> d n = 1 - d (g' n).
Proof.
 intros.
 destruct (delta_0_1 (g' n)) as [E|E]; rewrite E.
 - now apply delta_b.
 - now apply delta_c.
Qed.

(* A short formula giving delta:
   This could be used to define g'. *)

Lemma delta_eqn n : 4<=n ->
 d n = 1 - d (n-1) * d (g' n).
Proof.
 intros.
 destruct (delta_0_1 (n-1)) as [E|E]; rewrite E.
 - simpl. apply delta_a; auto; omega.
 - rewrite Nat.mul_1_l. now apply delta_bc.
Qed.

(*============================================================*)

(** Another short equation for g', but this one cannot be used
    for defining g' recursively :-( *)

Lemma g'_eqn' n : 3 < n -> g' (g' n) + g' (n-1) = n.
Proof.
 intros.
 set (k := depth n).
 assert (Hk : 3<=k).
 { unfold k. change 3 with (depth 4).
   apply depth_mono; auto. }
 assert (LE : S (fib k) <= n <= fib (S k)).
 { apply depth_carac. omega. auto. }
 unfold g'. rewrite flip_flip.
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

Lemma oups_eqn' n : 3<n -> oups (oups n) + oups (n-1) = n.
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
    solution (which is hence g'). *)

(** Study of the alternative equation and its consequences. *)

Definition AltSpec (g:nat->nat) :=
  (g 0 = 0 /\ g 1 = 1 /\ g 2 = 1 /\ g 3 = 2) /\
  (forall n, 3<n -> g (g n) + g (n-1) = n).

Lemma alt_spec_g' : AltSpec g'.
Proof.
split. now compute. apply g'_eqn'.
Qed.

Lemma alt_spec_oups : AltSpec oups.
Proof.
split. now compute. apply oups_eqn'.
Qed.

Lemma alt_bound g : AltSpec g -> forall n, 1<n -> 0 < g n < n.
Proof.
intros ((H0 & H1 & H2 & H3),Hg).
induction n as [n IH] using lt_wf_rec.
intros Hn.
destruct (le_lt_dec n 3) as [Hn'|Hn'].
- destruct n as [|[|[|n]]]; try omega. replace n with 0; omega.
- assert (1 < g (g n) < n).
  { generalize (IH (n-1)) (Hg n). omega. }
  assert (g (g (S n)) + g n = S n).
  { replace n with (S n - 1) at 2 by omega. apply Hg; omega. }
  assert (g n <> 0). { intros E. rewrite E in *. omega. }
  assert (g n <> n). { intros E. rewrite !E in *. omega. }
  assert (g n <> S n).
  { intros E. rewrite E in *. specialize (IH (g (S n))). omega. }
  omega.
Qed.

Lemma alt_bound' g : AltSpec g -> forall n, 0 <= g n <= n.
Proof.
intros Hg [|[|n]].
- replace (g 0) with 0. auto. symmetry. apply Hg.
- replace (g 1) with 1. auto. symmetry. apply Hg.
- generalize (@alt_bound _ Hg (S (S n))). omega.
Qed.

Lemma alt_4 g : AltSpec g -> g 4 = 3.
Proof.
 intros Hg.
 assert (0 < g 4 < 4) by (apply alt_bound; auto).
 assert (g (g 4) + g 3 = 4) by (apply Hg; auto).
 destruct Hg as ((G0 & G1 & G2 & G3),_).
 destruct (g 4) as [|[|[|[|n]]]]; omega.
Qed.

Lemma alt_5 g : AltSpec g -> g 5 = 3.
Proof.
 intros Hg.
 assert (0 < g 5 < 5) by (apply alt_bound; auto).
 assert (g (g 5) + g 4 = 5) by (apply Hg; auto).
 assert (g 4 = 3) by (apply alt_4; auto).
 destruct Hg as ((G0 & G1 & G2 & G3),_).
 destruct (g 5) as [|[|[|[|[|n]]]]]; omega.
Qed.

(** Alas, g(n) isn't unique for n>5 (e.g 4 or 5 for n=6) *)

Lemma monotone_equiv g :
 (forall n, g n <= g (S n)) ->
 (forall n m, n <= m -> g n <= g m).
Proof.
intros Mon.
induction 1.
- reflexivity.
- now transitivity (g m).
Qed.

Lemma alt_mono_bound g : AltSpec g ->
  (forall n, g n <= g (S n)) ->
  forall n m, n <= m -> g m - g n <= m-n.
Proof.
intros Hg Mon.
assert (main : forall n m, 3 < n <= m -> g m - g n <= m - n).
{
  intros.
  destruct Hg as (_,Hg).
  generalize (Hg (S n)) (Hg (S m)); simpl; intros.
  rewrite Nat.sub_0_r in *.
  generalize (@monotone_equiv _ Mon (S n) (S m)).
  generalize (@monotone_equiv _ Mon (g (S n)) (g (S m))).
  omega.
}
intros n m. destruct (le_lt_dec n 3); intros.
- destruct (le_lt_dec m 3); intros.
  + destruct Hg as ((G0 & G1 & G2 & G3), _).
    destruct m as [|[|[|[|m]]]], n as [|[|[|[|n]]]]; omega.
  + specialize (main 4 m). rewrite alt_4 in main; auto.
    destruct Hg as ((G0 & G1 & G2 & G3), _).
    destruct n as [|[|[|[|n]]]]; omega.
- apply main; auto.
Qed.

Lemma alt_mono_unique g1 g2 :
  AltSpec g1 -> (forall n, g1 n <= g1 (S n)) ->
  AltSpec g2 -> (forall n, g2 n <= g2 (S n)) ->
  forall n, g1 n = g2 n.
Proof.
intros Hg1 Mon1 Hg2 Mon2.
induction n as [n IH] using lt_wf_rec.
destruct (le_lt_dec n 3).
- destruct Hg1 as ((G10 & G11 & G12 & G13),_),
           Hg2 as ((G20 & G21 & G22 & G23),_).
  destruct n as [|[|[|[|n]]]]; omega.
- assert (g1 (n-1) = g2 (n-1)) by (apply IH; omega).
  assert (g1 (g1 n) = g2 (g2 n)).
  { destruct Hg1 as (_,Hg1), Hg2 as (_,Hg2).
    specialize (Hg1 n). specialize (Hg2 n). omega. }
  set (x1:=g1 n) in *.
  set (x2:=g2 n) in *.
  assert (g1 x1 = g2 x1).
  { apply IH. apply alt_bound; auto. omega. }
  assert (g1 x2 = g2 x2).
  { apply IH. apply alt_bound; auto. omega. }
  assert (g2 (n-1) <= x2 /\ x2-g2(n-1) <= 1).
  { unfold x2; split.
    - generalize (Mon2 (n-1)); replace (S (n-1)) with n; omega.
    - generalize (@alt_mono_bound _ Hg2 Mon2 (n-1) n); omega. }
  assert (g1 (n-1) <= x1 /\ x1-g1(n-1) <= 1).
  { unfold x1; split.
    - generalize (Mon1 (n-1)); replace (S (n-1)) with n; omega.
    - generalize (@alt_mono_bound _ Hg1 Mon1 (n-1) n); omega. }
  destruct (lt_eq_lt_dec x1 x2) as [[LT|EQ]|LT]; trivial; exfalso.
  + (* x1 < x2 *)
    assert (g1 (S x1) <= g1 x2).
    { apply monotone_equiv. apply Mon1. apply LT. }
    assert (g1 (g1 (S n)) = S (g1 x1)).
    { destruct Hg1 as (_,Hg1).
      generalize (Hg1 (S n)) (Hg1 n); simpl.
      rewrite Nat.sub_0_r.
      unfold x1 in *; omega. }
    assert (g1 (g1 (S n)) = g1 (S x1)).
    { f_equal.
      generalize
        (@alt_mono_bound _ Hg1 Mon1 n (S n))
        (@alt_mono_bound _ Hg1 Mon1 x1 (g1 (S n)) (Mon1 n)).
      unfold x1 in *; omega. }
    omega.
  + (* x2 < x1 *)
    assert (g2 (S x2) <= g2 x1).
    { apply monotone_equiv. apply Mon2. apply LT. }
    assert (g2 (g2 (S n)) = S (g2 x2)).
    { destruct Hg2 as (_,Hg2).
      generalize (Hg2 (S n)) (Hg2 n); simpl.
      rewrite Nat.sub_0_r.
      unfold x2 in *; omega. }
    assert (g2 (g2 (S n)) = g2 (S x2)).
    { f_equal.
      generalize
        (@alt_mono_bound _ Hg2 Mon2 n (S n))
        (@alt_mono_bound _ Hg2 Mon2 (g2 n) (g2 (S n)) (Mon2 n)).
      unfold x2 in *; omega. }
    omega.
Qed.

Lemma alt_mono_is_g' g :
  AltSpec g -> (forall n, g n <= g (S n)) ->
  forall n, g n = g' n.
Proof.
 intros Hg Mon. apply alt_mono_unique; auto.
 - split. now compute. apply g'_eqn'.
 - apply g'_mono_S.
Qed.
