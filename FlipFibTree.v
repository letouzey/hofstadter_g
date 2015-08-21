
Require Import Arith Omega Wf_nat List Program Program.Wf.
Require Import FibTree.
Set Implicit Arguments.

(* Source: Hofstadter's book: Goedel, Escher, Bach. *)

(* See first the previous file for the study of:
    G (S n) + G (G n) = S n
    G 0 = 0
   and the associated tree where nodes are labeled breadth-first
   from left to right. *)

(* Now, question by Hofstadter: what if we keep the same tree,
   but label the nodes from right to left ?

13 12 11 9  8
 \/   |  \ /
  8   7   6
   \ /   /
    5   4
     \ /
      3
      |
      2
      |
      1

What is now the definition of the "parent" function ?

By convention, we'll keep here the tree ordered from left to right
but we'll flip its shape:

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

(* If we label the node from right to left, the effect
   on node numbers is the flip function below: *)

Definition flip n :=
  if n <=? 1 then n else S (fib (S (S (depth n)))) - n.

Lemma flip_depth n : depth (flip n) = depth n.
Proof.
 unfold flip.
 case Nat.leb_spec; trivial.
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
 case Nat.leb_spec; omega.
Qed.

Lemma flip_eqn k n : k<>0 -> 1 <= n <= fib (k-1) ->
 flip (fib k + n) = S (fib (S k)) - n.
Proof.
 intros Hk Hn.
 unfold flip.
 case Nat.leb_spec.
 - generalize (fib_nz k); omega.
 - intros H.
   replace (depth (fib k + n)) with k.
   + rewrite fib_eqn. omega.
   + symmetry. apply depth_carac; auto.
     rewrite fib_eqn'; omega.
Qed.

(* Two special cases : leftmost and rightmost node at a given depth *)

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

(* flip is involutive (and hence a bijection) *)

Lemma flip_flip n : flip (flip n) = n.
Proof.
 unfold flip at 2.
 case Nat.leb_spec; trivial.
 - unfold flip.
   case Nat.leb_spec; trivial. omega.
 - intros Hn.
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

(* flip and neighboors *)

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

(* The flipped g' function, corresponding to the flipped G tree *)

Definition g' n := flip (g (flip n)).

Compute g'(0)::g'(1)::g'(2)::g'(3)::g'(4)::g'(5)::g'(6)::g'(7)::g'(8)::nil.

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
       apply HH. now apply flip_high in Hn.
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

(* This equation, along with initial values up to n=3,
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

(* g' and the shape of its tree *)

(* - we already know that g' is onto, hence each node has
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

(* We could even exhibit at least one child for each node *)

Definition rchild' n := if n =? 1 then 2 else n + g' (S n) - 1.
(* rightmost son, always there *)

Lemma rightmost_child_carac a n : g' n = a ->
 g' (S n) = S a <-> n = rchild' a.
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
   replace (a =? 1) with false
     by (destruct a as [|[|[|a]]]; trivial; omega).
   assert (Hn' : 3 < S n) by omega.
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

Definition lchild' n := if n =? 1 then 1 else flip (rchild (flip n)).
(* leftmost son, always there (but might be equal to
   the rightmost son for unary nodes) *)

Lemma lchild'_alt n : n<>1 -> lchild' n = flip (flip n + flip (g' n)).
Proof.
 unfold lchild', rchild, g'.
 case Nat.eqb_spec; [intros; omega|intros].
 f_equal. f_equal.
 symmetry. apply flip_flip.
Qed.

Lemma g'_onto_eqn' n : g' (lchild' n) = n.
Proof.
 unfold g', lchild'.
 case Nat.eqb_spec; intros.
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
     case Nat.eqb_spec; [generalize (fib_nz k); intros; omega|intros].
     rewrite flip_Sfib; auto.
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
       case Nat.eqb_spec; intros; [omega|].
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
  g' n = a -> n = lchild' a \/ n = rchild' a.
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
 case Nat.eqb_spec; intros; try omega.
 rewrite flip_flip.
 now apply binary_rchild_is_unary.
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


(* Hence the shape of the g' tree is a repetition of this pattern:

    q
    |
    p   p'
    |   |
    --n--
      |

 where n,p',q are binary nodes and p is unary.
 As expected, this is the mirror of the G tree.
*)


(*=============================================================*)

(* comparison between g' and g *)

Inductive Steps (p:nat) : list nat -> Prop :=
    St_nil : Steps p []
  | St_one : forall n : nat, Steps p [n]
  | St_cons : forall (n m : nat) (l : list nat),
               m+p <= n -> Steps p (n :: l) -> Steps p (m :: n :: l).
Hint Constructors Steps.

Lemma Steps_1 l : Steps 1 l <-> Increasing l.
Proof.
 split; induction 1; constructor; auto; omega.
Qed.

Lemma Steps_more l p p' : p <= p' -> Steps p' l -> Steps p l.
Proof.
 induction 2; constructor; auto; omega.
Qed.

Lemma Steps_21 l : Steps 2 l -> Steps 1 l.
Proof.
 apply Steps_more; auto.
Qed.
Hint Resolve Steps_21.

Lemma Steps_alt p x l :
 Steps p (x::l) <-> Steps p l /\ (forall y, In y l -> x+p <= y).
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

Lemma Steps_nz p k l : 0<k -> Steps p (k::l) -> ~In 0 (k::l).
Proof.
 simpl. intros H H' [X|X]. omega.
 apply Steps_alt in H'. apply H' in X. omega.
Qed.

Lemma Steps_map p p' f l :
  (forall x y, x+p <= y -> f x + p' <= f y) ->
  Steps p l -> Steps p' (map f l).
Proof.
 induction 2; constructor; auto.
Qed.

Lemma Steps_pred p l : ~In 0 l -> Steps p l -> Steps p (map pred l).
Proof.
 induction 2; simpl in *; constructor; intuition.
Qed.

Lemma Steps_inv p x l : Steps p (x::l) -> Steps p l.
Proof.
 rewrite Steps_alt. intuition.
Qed.
Hint Resolve Steps_inv Steps_nz.

Lemma Steps_seq n k : Steps 1 (seq n k).
Proof.
 revert n. induction k.
 - constructor.
 - intros. simpl. apply Steps_alt. split; auto.
   intros y Hy. rewrite in_seq in Hy. omega.
Qed.

Lemma Steps_odds k : Steps 2 (odds k).
Proof.
 unfold odds. apply Steps_map with 1.
 intros. omega.
 apply Steps_seq.
Qed.

Lemma Steps_evens k : Steps 2 (evens k).
Proof.
 unfold odds. apply Steps_map with 1.
 intros. omega.
 apply Steps_seq.
Qed.


Definition HdLeEven l l' := match l, l' with
| [], [] => True
| k::_, k'::_ => exists p, k' = k + 2*p
| _, _ => False
end.

Lemma norm_spec l :
 { l' | sumfib l' = sumfib l /\
        (Steps 1 l -> Steps 2 l') /\
        length l' <= length l /\
        HdLeEven l l' }.
Proof.
 remember (length l) as n eqn:Hn. revert l Hn.
 induction n as [n IH] using lt_wf_rec.
 destruct l as [|k l].
 - exists (@nil nat); repeat split; subst; auto.
 - intros Hn. simpl in Hn.
   assert (Hn' : length l < n) by omega.
   destruct (IH (length l) Hn' l) as (l' & Eq & St & Le & Hd);
    trivial.
   destruct l' as [|k' l'].
   + exists [k].
     simpl in *. repeat split; subst; auto with arith.
     exists 0. omega.
   + assert (Steps 1 (k::l) -> k < k').
     { intros Hl.
       destruct l as [|x l0]. elim Hd. simpl in Hd. destruct Hd as (p,Hd).
       apply Steps_alt in Hl.
       assert (k+1 <= x) by (apply Hl; now left).
       omega. }
     destruct (eq_nat_dec (S k) k') as [E|N].
     * assert (Lt : length (S k' :: l') < n).
       { simpl in *; omega. }
       destruct (IH _ Lt (S k' :: l')) as (l'' & Eq' & St' & Le' & Hd');
         trivial; clear IH.
       exists l''; repeat split; auto.
       { rewrite Eq'. simpl. rewrite <- Eq. simpl.
         rewrite <- E. omega. }
       { intros Hl.
         apply St'.
         rewrite Steps_alt in St, Hl.
         apply Steps_alt. split.
         - apply Steps_21, St, Hl.
         - intros y Hy. apply St in Hy; [|apply Hl]. omega. }
       { simpl in *; omega. }
       { subst k'.
         destruct l''; simpl in Hd'. elim Hd'.
         destruct Hd' as (p,Hd'). exists (S p). omega. }
     * exists (k::k'::l'); repeat split; simpl in *; auto.
       { intros Hl.
         assert (k<k') by auto.
         constructor; auto. omega.
         eauto. }
       { omega. }
       { exists 0. omega. }
Qed.

Definition norm l := let (l',_) := norm_spec l in l'.

Lemma norm_ok l : sumfib (norm l) = sumfib l.
Proof.
 unfold norm. destruct norm_spec. intuition.
Qed.

Lemma norm_steps l : Steps 1 l -> Steps 2 (norm l).
Proof.
 unfold norm. destruct norm_spec. intuition.
Qed.

Lemma norm_hd l : HdLeEven l (norm l).
Proof.
 unfold norm. destruct norm_spec. intuition.
Qed.

Lemma norm_le x l : Steps 1 (x::l) ->
  forall y, In y (norm (x::l)) -> x <= y.
Proof.
 intros H y Hy.
 apply norm_steps in H.
 assert (Hd := norm_hd (x::l)).
 destruct (norm (x::l)) as [|k' l'].
 - elim Hd.
 - simpl in Hd.
   destruct Hd as (p,Hd).
   assert (x <= k') by omega.
   simpl in Hy. destruct Hy as [Hy|Hy]; try omega.
   transitivity k'; auto.
   apply Steps_alt in H. apply H in Hy. omega.
Qed.

Lemma Steps_app p x l l' :
  Steps p l -> Steps p (x::l') ->
  (forall y, In y l -> y <= x) -> Steps p (l++l').
Proof.
 induction l.
 - intros _ Hl' H. simpl. now rewrite Steps_alt in Hl'.
 - intros Hl Hl' H. simpl. apply Steps_alt. split.
   + apply IHl; auto.
     * now rewrite Steps_alt in Hl.
     * intros y Hy. apply H. now right.
   + intros y Hy. rewrite in_app_iff in Hy.
     destruct Hy as [Hy|Hy].
     * rewrite Steps_alt in Hl. now apply Hl.
     * assert (a <= x) by (apply H; now left).
       apply Steps_alt in Hl'. apply Hl' in Hy. omega.
Qed.

Lemma Steps_app_inv p l l' :
 Steps p (l++l') ->
 Steps p l /\ Steps p l' /\
 forall x x', In x l -> In x' l' -> x+p <= x'.
Proof.
 induction l; simpl.
 - split. constructor. intuition.
 - rewrite !Steps_alt. intuition.
   subst. apply H1. rewrite in_app_iff. now right.
Qed.

Lemma FibDecomp_alt x l :
  FibDecomp (x::l) <->
  FibDecomp l /\ x<>0 /\ (forall y, In y l -> y+2 <= x).
Proof.
 split.
 - revert x. induction l as [|a l IH].
   + intros x Hx. repeat split.
     constructor. inversion Hx; omega. inversion 1.
   + intros x. inversion 1; subst. repeat split; trivial.
     apply FibDecomp_nz in H. simpl in H. intuition.
     intros y [Hy|Hy]. now subst.
     apply (IH a) in Hy; auto. omega.
 - intros (H & H' & H'').
   destruct l; constructor; trivial. omega. apply H''. now left.
Qed.

Lemma FibDecomp_app x l l' :
  FibDecomp l -> FibDecomp (x::l') ->
  (forall y, In y l -> x <= y) -> FibDecomp (l++l').
Proof.
 induction l.
 - intros _ Hl' H. simpl. now rewrite FibDecomp_alt in Hl'.
 - intros Hl Hl' H. simpl. apply FibDecomp_alt. repeat split.
   + apply IHl; auto.
     * now rewrite FibDecomp_alt in Hl.
     * intros y Hy. apply H. now right.
   + apply FibDecomp_nz in Hl; simpl in Hl. intuition.
   + intros y Hy. rewrite in_app_iff in Hy.
     destruct Hy as [Hy|Hy].
     * rewrite FibDecomp_alt in Hl. now apply Hl.
     * assert (x <= a) by (apply H; now left).
       apply FibDecomp_alt in Hl'. apply Hl' in Hy. omega.
Qed.

Lemma FibDecomp_app_inv l l' :
 FibDecomp (l++l') ->
 FibDecomp l /\ FibDecomp l' /\
 forall x x', In x l -> In x' l' -> x'+2 <= x.
Proof.
 induction l; simpl.
 - split. constructor. intuition.
 - rewrite !FibDecomp_alt. intuition.
   subst. apply H2. rewrite in_app_iff. now right.
Qed.

Lemma FibDecomp_Steps l : FibDecomp l -> Steps 2 (rev l).
Proof.
 induction 1.
 - constructor.
 - constructor.
 - simpl in *.
   apply Steps_app with n; auto.
   intros y Hy. apply Steps_app_inv in IHFibDecomp.
   destruct IHFibDecomp as (_ & _ & Hln).
   specialize (Hln y n).
   rewrite in_app_iff in Hy. simpl in *. intuition.
Qed.

Lemma Steps_FibDecomp l : Steps 2 l -> ~In 0 l -> FibDecomp (rev l).
Proof.
 induction 1.
 - constructor.
 - simpl. intros. constructor. intuition.
 - simpl in *. intros.
   apply FibDecomp_app with n; auto.
   * constructor. omega. constructor. omega.
   * intros y Hy. apply FibDecomp_app_inv in IHSteps; [|intuition].
     destruct IHSteps as (_ & _ & Hln).
     specialize (Hln y n).
     rewrite in_app_iff in Hy. simpl in *. intuition.
Qed.

Lemma Steps_canon l l' :
 ~In 0 l -> ~In 0 l' -> Steps 2 l -> Steps 2 l' ->
 sumfib l = sumfib l' -> l = l'.
Proof.
 intros.
 assert (rev l = rev l').
 { apply decomp_unique.
   apply Steps_FibDecomp; auto.
   apply Steps_FibDecomp; auto.
   now rewrite !sumfib_rev. }
 rewrite <- (rev_involutive l), <- (rev_involutive l').
 now f_equal.
Qed.

Definition DecompTwoEven st n :=
 exists p l, n = sumfib (2::2*p::l) /\ Steps st (2::2*p::l).

Definition DecompTwoOdd st n :=
 exists p l, n = sumfib (2::2*p+1::l) /\ Steps st (2::2*p+1::l).

Definition DecompOne st n :=
 exists l, n = sumfib (1::l) /\ Steps st (1::l).

Definition DecompHigh st n :=
 exists k l, n = sumfib (k::l) /\ 2<k /\ Steps st (k::l).

Lemma Decomp_complete n : 3<n ->
 DecompOne 2 n \/ DecompTwoEven 2 n \/ DecompTwoOdd 2 n \/ DecompHigh 2 n.
Proof.
 intros Hn.
 destruct (decomp_exists n) as (l,(H1,H2)).
 set (l' := rev l).
 assert (H1' : sumfib l' = n).
 { unfold l'. now rewrite sumfib_rev. }
 assert (H2' : Steps 2 l').
 { unfold l'. now apply FibDecomp_Steps. }
 assert (H3' : ~In 0 l').
 { unfold l'. rewrite <- in_rev. now apply FibDecomp_nz. }
 clearbody l'. clear l H1 H2.
 destruct l' as [|k l'].
 - simpl in H1'. intuition.
 - destruct k as [|[|[|k]]].
   + simpl in H3'. intuition.
   + left; now exists l'.
   + destruct l' as [|k' l'].
     * simpl in H1'. omega.
     * destruct (Nat.Even_or_Odd k') as [(p,Hp)|(p,Hp)].
       { right; left. exists p; exists l'. now subst. }
       { right; right; left. exists p; exists l'.
           repeat split; subst k'; auto; omega. }
   + right; right; right. exists (3+k); exists l'. intuition.
Qed.

Lemma DecompHigh_equiv n : DecompHigh 1 n <-> DecompHigh 2 n.
Proof.
 split; intros (k & l & Hn & Hk & Hl).
 - assert (Hla := norm_steps Hl).
   assert (Hlb := norm_hd (k::l)).
   assert (Hlc := norm_le Hl).
   assert (Hld := norm_ok (k::l)).
   set (l0 := norm (k :: l)) in *.
   destruct l0 as [|k0 l0].
   + elim Hlb.
   + simpl in Hlb. destruct Hlb as (p', Hlb).
     exists k0; exists l0; repeat split; auto; omega.
 - exists k; exists l; auto.
Qed.

Lemma DecompTwoEven_equiv n : DecompTwoEven 1 n <-> DecompTwoEven 2 n.
Proof.
 split; intros (p & l & Hn & Hl).
 - assert (2 <= p).
   { destruct p as [|[|p]].
     - simpl in Hl. inversion Hl; omega.
     - simpl in Hl. inversion Hl; omega.
     - omega. }
   assert (Hla : Steps 1 (2*p::l)).
   { apply Steps_alt in Hl. apply Hl. }
   assert (Hlb := norm_steps Hla).
   assert (Hlc := norm_hd (2*p::l)).
   assert (Hld := norm_le Hla).
   assert (Hle := norm_ok (2*p::l)).
   set (l0 := norm (2*p :: l)) in *.
   destruct l0 as [|k0 l0].
   + elim Hlc.
   + simpl in Hlc. destruct Hlc as (p', Hlc).
     replace k0 with (2*(p+p')) in * by omega.
     exists (p+p'); exists l0; split.
     * simpl in *. omega.
     * constructor; auto. omega.
 - exists p; exists l; auto.
Qed.

Lemma DecompTwoOdd_21 n : DecompTwoOdd 2 n -> DecompTwoOdd 1 n.
Proof.
 intros (p & l & Hn & Hl).
 exists p; exists l; auto.
Qed.

Lemma DecompTwoOdd_12 n :
 DecompTwoOdd 1 n -> DecompTwoOdd 2 n \/ DecompHigh 2 n.
Proof.
 intros (p & l & Hn & Hl).
 assert (Hla : Steps 1 (2*p+1::l)).
 { apply Steps_alt in Hl. apply Hl. }
 assert (Hlb := norm_steps Hla).
 assert (Hlc := norm_hd (2*p+1::l)).
 assert (Hld := norm_le Hla).
 assert (Hle := norm_ok (2*p+1::l)).
 set (l0 := norm (2*p+1 :: l)) in *.
 destruct l0 as [|k0 l0].
 - elim Hlc.
 - destruct (eq_nat_dec k0 3) as [E|N].
   + right. apply DecompHigh_equiv.
     subst k0.
     exists 4; exists l0; repeat split; auto.
     { simpl in *. omega. }
     { apply Steps_alt in Hlb.
       apply Steps_alt. split.
       apply Steps_more with 2; auto. apply Hlb.
       intros y Hy. apply Hlb in Hy. omega. }
   + simpl in Hlc. destruct Hlc as (p', Hlc).
     replace k0 with (2*(p+p')+1) in * by omega.
     left. exists (p+p'); exists l0; repeat split.
     { simpl in *. omega. }
     { constructor; auto. inversion Hl; subst. omega. }
Qed.

Lemma DecompOne_21 n : DecompOne 2 n -> DecompOne 1 n.
Proof.
 intros (l & Hn & Hl). exists l; auto.
Qed.

Lemma DecompOne_12 n : DecompOne 1 n -> DecompOne 2 n \/ DecompHigh 2 n.
Proof.
 intros (l & Hn & Hl).
 destruct l as [|k l].
 - left; exists (@nil nat); auto.
 - inversion_clear Hl.
   assert (Hla := norm_steps H0).
   assert (Hlb := norm_hd (k::l)).
   assert (Hlc := norm_le H0).
   assert (Hld := norm_ok (k::l)).
   set (l0 := norm (k :: l)) in *.
   destruct l0 as [|k0 l0].
   + elim Hlb.
   + simpl in Hlb. destruct Hlb as (p,Hlb).
     destruct (eq_nat_dec k0 2) as [E|N].
     * right. apply DecompHigh_equiv.
       rewrite E in *.
       exists 3; exists l0; repeat split; auto.
       { simpl in *. omega. }
       { apply Steps_alt in Hla.
         apply Steps_alt. split.
         apply Steps_21, Hla.
         intros y Hy. apply Hla in Hy. omega. }
     * left. exists (k0::l0); repeat split.
       { simpl in *; omega. }
       { constructor; auto. omega. }
Qed.

Lemma NotDecompTwoEven_3 n : DecompHigh 2 n -> ~DecompTwoEven 2 n.
Proof.
 intros (k & l & Hn & Hk & Hl) (p & l' & Hn' & Hl').
 assert (E : k::l = 2::2*p::l').
 { apply Steps_canon; try eapply Steps_nz; auto; omega. }
 injection E. omega.
Qed.

Lemma NotDecompTwoEven_3b n : DecompHigh 1 n -> ~DecompTwoEven 2 n.
Proof.
 rewrite DecompHigh_equiv. apply NotDecompTwoEven_3.
Qed.

Lemma NotDecompTwoEven_2 n : DecompTwoOdd 2 n -> ~DecompTwoEven 2 n.
Proof.
 intros (p & l & Hn & Hl) (p' & l' & Hn' & Hl').
 assert (E : 2::2*p+1::l = 2::2*p'::l').
 { apply Steps_canon; try eapply Steps_nz; auto; omega. }
 injection E. omega.
Qed.

Lemma NotDecompTwoEven_2b n : DecompTwoOdd 1 n -> ~DecompTwoEven 2 n.
Proof.
 intros H.
 apply DecompTwoOdd_12 in H. destruct H.
 now apply NotDecompTwoEven_2.
 now apply NotDecompTwoEven_3.
Qed.

Lemma NotDecompTwoEven_1 n : DecompOne 2 n -> ~DecompTwoEven 2 n.
Proof.
 intros (l & Hn & Hl) (p & l' & Hn' & Hl').
 assert (E : 1::l = 2::2*p::l').
 { apply Steps_canon; try eapply Steps_nz; auto; omega. }
 discriminate.
Qed.

Lemma NotDecompTwoEven_1b n : DecompOne 1 n -> ~DecompTwoEven 2 n.
Proof.
 intros H.
 apply DecompOne_12 in H. destruct H.
 now apply NotDecompTwoEven_1.
 now apply NotDecompTwoEven_3.
Qed.

Hint Resolve NotDecompTwoEven_1b NotDecompTwoEven_2b NotDecompTwoEven_3b.

Lemma map_S_pred l : ~In 0 l -> l = map S (map pred l).
Proof.
 intros.
 rewrite map_map. rewrite <- (map_id l) at 1.
 apply map_ext_in.
 intros a Ha. assert (a<>0) by congruence. omega.
Qed.

Lemma g_sumfib' l : Steps 1 l -> ~In 0 l ->
 g (sumfib l) = sumfib (map pred l).
Proof.
 intros.
 rewrite (map_S_pred l) at 1; auto.
 apply g_sumfib.
 apply Increasing_pred; auto. now apply Steps_1.
Qed.

Lemma sumfib_eqn' l : ~In 0 l ->
 sumfib (map S l) - sumfib (map pred l) = sumfib l.
Proof.
 intros. rewrite <- sumfib_eqn; auto. apply Nat.add_sub.
Qed.

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
 now rewrite H.
Qed.

Lemma DecompOne_g n : DecompOne 2 n -> g (S n) = g n.
Proof.
 intros (l & H & Hl).
 rewrite H.
 change (S (sumfib (1::l))) with (sumfib (2::l)).
 assert (Steps 1 (2::l)).
 { apply Steps_alt in Hl; apply Steps_alt. split.
   + apply Steps_21. apply Hl.
   + intros y Hy. apply Hl in Hy. auto. }
 rewrite !g_sumfib'; eauto.
Qed.

Definition IHeq n :=
 forall m, m<n -> ~DecompTwoEven 2 m -> g' m = g m.
Definition IHsucc n :=
 forall m, m<n -> DecompTwoEven 2 m -> g' m = S (g m).

Lemma g'_g_S n : IHeq n ->
 DecompTwoEven 2 n -> g' n = S (g n).
Proof.
 intros IH (p & l & Hn & H).
 assert (2 <= p).
 { destruct p as [|[|p]].
   - simpl in H; inversion_clear H. omega.
   - simpl in H; inversion_clear H. omega.
   - omega. }
 assert (7 <= n).
 { rewrite Hn. simpl.
   assert (fib 4 <= fib (p+(p+0))) by (apply fib_mono; omega).
   simpl fib in *.
   omega. }
 apply g'_g_S_inv; [omega|].
 assert (Hl : forall x, In x l -> 4<=x).
 { intros x Hx. apply Steps_alt in H. apply H. simpl. now right. }
 assert (~In 0 l) by (intro X; apply Hl in X; omega).
 set (l' := map pred l).
 assert (Hl' : l = map S l') by (unfold l'; now apply map_S_pred).
 assert (~In 0 l').
 { unfold l'. rewrite in_map_iff. intros (x,(Hx,Hx')).
   apply Hl in Hx'. omega. }
 assert (E : n - 1 = sumfib (1 :: 2*p :: l)).
 { rewrite Hn. simpl. omega. }
 assert (H' : Steps 1 (1::2*p::l)).
 { constructor. omega.
   apply Steps_21. now inversion H. }
 assert (E2 : g (n-1) = sumfib (1::2*p-1::l')).
 { rewrite E.
   rewrite g_sumfib'; [|auto|simpl; intuition].
   simpl. do 3 f_equal. omega. }
 assert (E3 : S (g (n-1)) = sumfib (2::2*p-1::l')).
 { now rewrite E2. }
 assert (H'' : Steps 2 (1::2*p-1::l')).
 { constructor. omega.
   unfold l'.
   rewrite Nat.sub_1_r.
   apply (@Steps_pred _ (2*p::l)); [ simpl; intuition | eauto]. }
 assert (H''' : Steps 1 (2::2*p-1::l')).
 { constructor. omega.
   apply Steps_21. now inversion H''. }
 assert (D : DecompOne 1 (n-1)).
 { exists (2*p::l). split.
   - rewrite Hn. simpl. omega.
   - apply Steps_more with 2; auto.
     constructor. omega. now inversion H. }
 rewrite (IH (n-1)) by (auto;omega).
 assert (D' : DecompTwoOdd 1 (S (g (n-1)))).
 { exists (p-1); exists l'.
   replace (2*(p-1)+1) with (2*p-1) by omega.
   split; auto. }
 rewrite (IH (S (g (n-1))))
   by (auto; generalize (@g_lt (n-1)); omega).
 apply DecompOne_g; auto.
 exists (2*p-1::l'); auto.
Qed.

Lemma g'_g_eq_1 n : IHeq n -> 3<n -> DecompOne 2 n -> g' n = g n.
Proof.
 intros IH H3n (l & Hn & H).
 apply g'_g_eq_inv; auto.
 assert (Hl : forall x, In x l -> 3<=x).
 { intros x Hx. apply Steps_alt in H. now apply H. }
 assert (~In 0 l) by (intros X; apply Hl in X; omega).
 set (l' := map pred l).
 assert (Hl' : l = map S l') by (unfold l'; now apply map_S_pred).
 assert (~In 0 l').
 { unfold l'. rewrite in_map_iff. intros (x,(Hx,Hx')).
   apply Hl in Hx'. omega. }
 assert (E :  n-1 = sumfib l). { rewrite Hn. simpl. omega. }
 assert (Hbis : Steps 1 l) by eauto.
 assert (H' : Steps 1 (1::l')).
 { unfold l'.
   change 1 with (pred 2).
   apply (@Steps_pred 1 (2::l)).
   + simpl. intuition.
   + apply Steps_alt; auto. }
 assert (E2 : g (n-1) = sumfib l').
 { rewrite E, g_sumfib'; auto. }
 assert (E3 : S (g (n-1)) = sumfib (1::l')).
 { rewrite E2; auto. }
 assert (D : DecompHigh 1 (n-1)).
 { destruct l as [|k l].
   - simpl in Hn. omega.
   - exists k; exists l; repeat split; auto.
     inversion H; omega. }
 rewrite (IH (n-1)) by (auto;omega).
 assert (D' : DecompOne 1 (S (g (n-1)))).
 { exists l'; auto. }
 rewrite (IH (S (g (n-1))))
   by (auto; generalize (@g_lt (n-1)); omega).
 rewrite E3, E2.
 rewrite !g_sumfib'; eauto.
Qed.

Lemma g'_g_eq_2 n : IHeq n -> IHsucc n -> 3<n ->
 DecompTwoOdd 2 n -> g' n = g n.
Proof.
 intros IH1 IH2 H3n (p & l & Hn & H).
 assert (1<p).
 { destruct p as [|[|p]].
   - simpl in H. inversion H. omega.
   - simpl in H. inversion H. omega.
   - omega. }
 apply g'_g_eq_inv; auto.
 replace (g' n) with (S n - g' (S (g' (n-1))))
   by (rewrite <- g'_eqn; omega).
 assert (Hl : forall x, In x l -> 4<=x).
 { intros x Hx. apply Steps_alt in H. apply H. now right. }
 assert (~In 0 l) by (intro X; apply Hl in X; omega).
 set (l' := map pred l).
 assert (Hl' : l = map S l') by (unfold l'; now apply map_S_pred).
 assert (~In 0 l').
 { unfold l'. rewrite in_map_iff. intros (x,(Hx,Hx')).
   apply Hl in Hx'. omega. }
 assert (E : n-1 = sumfib (1 :: 2*p+1 :: l)).
 { now rewrite Hn. }
 assert (H' : Steps 1 (1 :: 2*p+1 :: l)).
 { constructor. omega. apply Steps_21. now inversion H. }
 assert (H'' : Steps 2 (1 :: 2*p :: l')).
 { constructor. omega.
   replace (2*p) with (pred (2*p+1)) by omega.
   apply (@Steps_pred _ (2*p+1::l)); [simpl;intuition|eauto]. }
 assert (H''' : Steps 1 (2 :: 2*p :: l')).
 { constructor. omega. eauto. }
 assert (E2 : g (n-1) = sumfib (1::2*p::l')).
 { rewrite E.
   rewrite g_sumfib'; [|auto|simpl; intuition].
   simpl. do 3 f_equal. omega. }
 assert (E3 : S (g (n-1)) = sumfib (2::2*p::l')).
 { now rewrite E2. }
 assert (D : DecompOne 1 (n-1)).
 { exists (2*p+1::l); split; auto. }
 rewrite (IH1 (n-1)) by (auto;omega).
 assert (D' : DecompTwoEven 2 (S (g (n-1)))).
 { apply DecompTwoEven_equiv.
   exists p; exists l'; split; auto. }
 rewrite (IH2 (S (g (n-1))))
   by (auto; generalize (@g_lt (n-1)); omega).
 f_equal.
 apply DecompOne_g.
 exists (2*p::l'); auto.
Qed.

Lemma odds_in k : forall y, In y (odds k) -> 1<=y<2*k.
Proof.
 induction k.
 - simpl; intuition.
 - intros y. rewrite odds_S, <- S_odds.
   rewrite map_map. simpl.
   rewrite in_map_iff.
   intros [H|(x,(Hx,Hx'))]. omega. apply IHk in Hx'. omega.
Qed.

Lemma evens_in k : forall y, In y (evens k) -> 2<=y<=2*k.
Proof.
 intros y. rewrite <- S_odds, in_map_iff.
 intros (x,(<-,Hx)). apply odds_in in Hx. omega.
Qed.

Lemma g'_g_eq_3even n k l : IHeq n -> 3<n ->
 n = sumfib (2*k::l) -> 2<=k -> Steps 2 (2*k::l) ->
 g' n = g n.
Proof.
 intros IH1 H3n Hn Hk H.
 apply g'_g_eq_inv; auto.
 assert (Hl : forall x, In x l -> 4<=x).
 { intros x Hx. apply Steps_alt in H. apply H in Hx. omega. }
 assert (~In 0 l) by (intro X; apply Hl in X; omega).
 set (l' := map pred l).
 assert (Hl' : l = map S l') by (unfold l'; now apply map_S_pred).
 assert (~In 0 l').
 { unfold l'. rewrite in_map_iff. intros (x,(Hx,Hx')).
   apply Hl in Hx'. omega. }
 set (l0 := odds k).
 assert (Hl0 : sumfib l0 = Nat.pred (fib (2*k))).
 { unfold l0. apply sumfib_odds. }
 assert (Steps 1 (l0++l)).
 { apply Steps_app with (2*k); auto.
   - unfold l0. apply Steps_21, Steps_odds.
   - unfold l0. intros y Hy. apply odds_in in Hy. omega. }
 assert (~In 0 (l0++l)).
 { rewrite in_app_iff. intros [X|X]; [|intuition].
   unfold l0 in X. apply odds_in in X. omega. }
 assert (E : n - 1 = sumfib (l0 ++ l)).
 { rewrite sumfib_app.
   rewrite Hn, Hl0. generalize (fib_nz (2*k)). simpl. omega. }
 destruct k as [|k]; [omega|].
 assert (D : DecompOne 1 (n-1)).
 { rewrite E. unfold l0 in *.
   rewrite odds_S in *. simpl.
   exists (map S (evens k) ++ l); auto. }
 rewrite (IH1 (n-1)); auto; try omega.
 assert (E' : g (n-1) = sumfib (map pred l0++l')).
 { unfold l'. rewrite <- map_app, E, g_sumfib'; auto. }
 assert (E2 : g (n-1) = sumfib (1::evens k ++ l')).
 { rewrite E'. unfold l0.
   rewrite odds_S. simpl map. rewrite map_map. simpl map.
   now rewrite map_id. }
 set (SS := fun x => S (S x)).
 assert (E3 : g (n-1) = sumfib (1::2::map SS (evens (k-1)) ++ l')).
 { rewrite E2. f_equal. f_equal.
   replace k with (S (k-1)) at 1 by omega.
   rewrite <- S_odds. rewrite odds_S. simpl.
   now rewrite map_map. }
 assert (E4 : S (g(n-1)) = sumfib (1::3::map SS (evens (k-1))++l')).
 { now rewrite E3. }
 assert (H' : Steps 1 (1::3::map SS (evens (k-1))++l')).
 { constructor. omega.
   apply (@Steps_app 1 (2*(S k)) (3::map SS (evens (k-1)))).
   - apply Steps_alt. split.
     + apply Steps_map with 2.
       intros; unfold SS; omega.
       apply Steps_evens.
     + intros y. rewrite in_map_iff. intros (x,(Hx,Hx')).
       unfold SS in Hx.
       apply evens_in in Hx'. omega.
   - unfold l'. change (2*(S k)) with (pred (S (2*(S k)))).
     apply (@Steps_pred _ (S (2*(S k))::l)).
     + simpl; intuition.
     + apply Steps_alt. apply Steps_alt in H.
       split. apply Steps_21. apply H.
       intros y Hy. apply H in Hy. omega.
   - intros y. simpl. rewrite in_map_iff. unfold SS.
     intros [X|(x,(<-,Hx))]. subst y. omega.
     apply evens_in in Hx. omega. }
 assert (H'' : Steps 1 (1::2::map SS (evens (k-1))++l')).
 { constructor. omega.
   apply Steps_alt; split; eauto.
   apply Steps_inv in H'. apply Steps_alt in H'.
   intros y Hy. apply H' in Hy. omega. }
 assert (D' : DecompOne 1 (S (g (n-1)))).
 { exists (3::map SS (evens (k-1)) ++ l'); auto. }
 rewrite (IH1 (S (g (n-1))))
   by (auto; generalize (@g_lt (n-1)); omega).
 rewrite E4, E3.
 rewrite !g_sumfib'; eauto.
Qed.

Lemma g'_g_eq_33 n l : IHeq n -> IHsucc n -> 3<n ->
 n = sumfib (3::l) -> Steps 2 (3::l) ->
 g' n = g n.
Proof.
 intros IH1 IH2 H3n Hn H.
 apply g'_g_eq_inv; auto.
 assert (Hl : forall x, In x l -> 4<=x).
 { intros x Hx. apply Steps_alt in H. apply H in Hx. omega. }
 assert (~In 0 l) by (intro X; apply Hl in X; omega).
 assert (E : n - 1 = sumfib (2::l)). { now rewrite Hn. }
 destruct l as [|k' l]; [simpl in *; omega|].
 assert (5 <= k') by (inversion H; omega).
 assert (11 <= n).
 { rewrite Hn. simpl. generalize (@fib_mono 5 k').
   change (fib 5) with 8. omega. }
 destruct (Nat.Even_or_Odd k') as [(k3,Hk3)|(k3,Hk3)].
 * (* next term is even *)
   subst k'.
   assert (Steps 1 (2::2*k3::l)).
   { constructor. omega. eauto. }
   assert (D : DecompTwoEven 2 (n-1)).
   { apply DecompTwoEven_equiv.
     rewrite E. exists k3; exists l; auto. }
   rewrite (IH2 (n-1)); auto; try omega.
   assert (E2 : g (n-1) = sumfib (1::2*k3-1::map pred l)).
   { rewrite E.
     rewrite g_sumfib'; eauto.
     simpl. do 3 f_equal. omega. }
   assert (E3 : S (S (g (n-1))) = sumfib (3::2*k3-1::map pred l)).
   { now rewrite E2. }
   assert (Steps 1 (3 :: 2*k3-1 :: map pred l)).
   { constructor. omega.
     rewrite Nat.sub_1_r.
     apply (@Steps_pred _ (2*k3 :: l)); [simpl; intuition|eauto]. }
   assert (Steps 1 (1 :: 2*k3-1 :: map pred l)).
   { constructor. omega. eauto. }
   assert (D' : DecompHigh 1 (S (S (g (n-1))))).
   { exists 3; exists (2*k3-1 :: map pred l); auto. }
   assert (~DecompTwoEven 2 (S (S (g (n-1))))).
   { apply DecompHigh_equiv in D'.
     now apply NotDecompTwoEven_3. }
   assert (g (n-1) < n-2).
   { generalize (g_lipschitz 5 (n-1)). change (g 5) with 3.
     omega. }
   rewrite (IH1 (S (S (g (n-1))))); [|omega|auto].
   rewrite E3, E2.
   rewrite !g_sumfib'; eauto.
 * (* next term is odd *)
   subst k'.
   assert (Steps 1 (2::2*k3+1::l)).
   { constructor. omega. eauto. }
   assert (D : DecompTwoOdd 1 (n-1)).
   { rewrite E. exists k3; exists l; auto. }
   rewrite (IH1 (n-1)); auto; try omega.
   assert (E2 : g (n-1) = sumfib (1::2*k3::map pred l)).
   { rewrite E.
     rewrite g_sumfib'; eauto.
     simpl. do 3 f_equal. omega. }
   assert (E3 : S (g (n-1)) = sumfib (2::2*k3::map pred l)).
   { now rewrite E2. }
   assert (Steps 2 (2 :: 2*k3 :: map pred l)).
   { constructor. omega.
     replace (2*k3) with (pred (2*k3+1)) by omega.
     apply (@Steps_pred _ (2*k3+1 :: l)); [simpl; intuition|eauto]. }
   assert (Steps 2 (1 :: 2*k3 :: map pred l)).
   { constructor. omega. eauto. }
   assert (D' : DecompTwoEven 2 (S (g (n-1)))).
   { exists k3; exists (map pred l); auto. }
   rewrite (IH2 (S (g (n-1))));
     [|generalize (@g_lt (n-1)); omega|auto].
   f_equal.
   apply DecompOne_g.
   exists (2*k3::map pred l); auto.
Qed.

Lemma g'_g_eq_3odd n k l : IHeq n -> IHsucc n -> 3<n ->
 n = sumfib (2*k+1::l) -> 2<=k -> Steps 2 (2*k+1::l) ->
 g' n = g n.
Proof.
 intros IH1 IH2 H3n Hn Hk H.
 apply g'_g_eq_inv; auto.
 assert (Hl : forall x, In x l -> 4<=x).
 { intros x Hx. apply Steps_alt in H. apply H in Hx. omega. }
 assert (~In 0 l) by (intro X; apply Hl in X; omega).
 set (l' := map pred l).
 assert (Hl' : l = map S l') by (unfold l'; now apply map_S_pred).
 assert (~In 0 l').
 { unfold l'. rewrite in_map_iff. intros (x,(Hx,Hx')).
   apply Hl in Hx'. omega. }
 set (l0 := evens k).
 assert (Hl0 : sumfib l0 = Nat.pred (fib (2*k+1))).
 { unfold l0. apply sumfib_evens. }
 assert (Steps 1 (l0++l)).
 { apply Steps_app with (2*k+1); auto.
   - unfold l0. apply Steps_21, Steps_evens.
   - unfold l0. intros y Hy. apply evens_in in Hy. omega. }
 assert (~In 0 (l0++l)).
 { rewrite in_app_iff. intros [X|X]; [|intuition].
   unfold l0 in X. apply evens_in in X. omega. }
 assert (E : n - 1 = sumfib (l0 ++ l)).
 { rewrite sumfib_app.
   rewrite Hn, Hl0. generalize (fib_nz (2*k+1)). simpl; omega. }
 set (S4 := fun x => 4+x).
 set (S3 := fun x => 3+x).
 set (l0' := evens (k-2)).
 assert (E' : n - 1 = sumfib (2::4::map S4 l0' ++ l)).
 { rewrite E; unfold l0, l0'.
   replace k with (S (S (k-2))) at 1 by omega.
   rewrite <- S_odds, odds_S.
   rewrite <- S_odds, odds_S.
   simpl map. simpl app.
   now rewrite !map_map. }
 assert (H' : Steps 2 (2 :: 4 :: map S4 l0' ++ l)).
 { constructor. omega.
   apply (@Steps_app 2 (2*k+1) (4::map S4 l0')); auto.
   - apply Steps_alt. split.
     + apply Steps_map with 2.
       intros; unfold S4; omega.
       apply Steps_evens.
     + intros y. rewrite in_map_iff. intros (x,(Hx,Hx')).
       unfold S4 in Hx.
       apply evens_in in Hx'. omega.
   - intros y. simpl. rewrite in_map_iff. unfold S4.
     intros [X|(x,(<-,Hx))]. omega.
     apply evens_in in Hx. omega. }
 assert (H'' : Steps 1 (1 :: 4 :: map S3 l0' ++ l')).
 { constructor. omega.
   apply Steps_inv in H'.
   assert (0<4) by omega.
   apply Steps_pred in H'; eauto.
   simpl in H'. rewrite map_app, map_map in H'.
   change (fun x => pred (S4 x)) with S3 in *.
   apply Steps_alt in H'. destruct H' as (H',H'').
   apply Steps_alt. split; [eauto|].
   intros y Hy. apply H'' in Hy. omega. }
 assert (Steps 1 (1 :: 3 :: map S3 l0' ++ l')).
 { constructor. omega.
   apply Steps_alt. split; [eauto|].
   apply Steps_inv in H''.
   apply Steps_alt in H''.
   intros y Hy. apply H'' in Hy. omega. }
 assert (D : DecompTwoEven 2 (n-1)).
 { exists 2; exists (map S4 l0' ++ l); auto. }
 rewrite (IH2 (n-1)); auto; try omega.
 assert (E2 : g (n-1) = sumfib (1::3::map S3 l0'++l')).
 { rewrite E'.
   rewrite g_sumfib'; eauto.
   simpl. now rewrite map_app, map_map. }
 assert (E3 : S (S (g (n-1))) = sumfib (1::4::map S3 l0' ++ l')).
 { now rewrite E2. }
 assert (D' : DecompOne 1 (S (S (g (n-1))))).
 { exists (4::map S3 l0' ++ l'); auto. }
 assert (g (n-1) < n-2).
 { clear - Hk Hn.
   assert (8 <= n).
   { rewrite Hn. generalize (@fib_mono 5 (2*k+1)).
     change (fib 5) with 8. simpl. omega. }
   generalize (g_lipschitz 5 (n-1)). change (g 5) with 3.
   omega. }
 rewrite (IH1 (S (S (g (n-1))))); auto; try omega.
 rewrite E3, E2.
 rewrite !g_sumfib'; eauto.
Qed.

Lemma g'_g_eq_3 n : IHeq n -> IHsucc n -> 3<n ->
 DecompHigh 2 n -> g' n = g n.
Proof.
 intros IH1 IH2 H3n (k & l & Hn & Hk & H).
 destruct (Nat.Even_or_Odd k) as [(k2,Hk2)|(k2,Hk2)]; subst k.
 - apply (@g'_g_eq_3even n k2 l); auto. omega.
 - destruct k2 as [|[|k2]].
   + simpl in *. omega.
   + apply (@g'_g_eq_33 n l); auto.
   + apply (@g'_g_eq_3odd n (S (S k2)) l); auto. omega.
Qed.

Lemma g'_g n :
 (DecompTwoEven 2 n -> g' n = S (g n)) /\
 (~DecompTwoEven 2 n -> g' n = g n).
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
   + destruct (Decomp_complete LT) as [X|[X|[X|X]]].
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
 - destruct (Decomp_complete LT) as [X|[X|[X|X]]].
   * left. apply g'_g. now apply NotDecompTwoEven_1.
   * right. now apply g'_g.
   * left. apply g'_g. now apply NotDecompTwoEven_2.
   * left. apply g'_g. now apply NotDecompTwoEven_3.
Qed.

Lemma g_le_g' n : g n <= g' n.
Proof.
 destruct (g'_g_step n); omega.
Qed.


(*=============================================================*)

(* g' and "delta" equations *)

(* We can characterize g' via its "delta" (a.k.a increments).
   Let d(n) = g'(n+1)-g'(n).
   For n>3 :
   a) if d(n-1) = 0 then d(n) = 1
   b) if d(n-1) <> 0 and d(g'(n)) = 0 then d(n) = 1
   c) if d(n-1) <> 0 and d(g'(n)) <> 0 then d(n) = 0

   In fact these deltas are always 0 or 1.
*)

(* H is a relational presentation of these equations. *)

Inductive H : nat -> nat -> Prop :=
 | H_0 : H 0 0
 | H_1 : H 1 1
 | H_2 : H 2 1
 | H_3 : H 3 2
 | H_4 : H 4 3
 | H_a n x : 4<n -> H (n-2) x -> H (n-1) x -> H n (S x)
 | H_b n x y z : 4<n -> H (n-2) x -> H (n-1) y -> x<>y ->
                      H y z -> H (S y) z -> H n (S y)
 | H_c n x y z t : 4<n -> H (n-2) x -> H (n-1) y -> x<>y ->
                      H y z -> H (S y) t -> z <> t -> H n y.
Hint Constructors H.

Lemma H_le n k : H n k -> k <= n.
Proof.
induction 1; auto with arith; omega.
Qed.

Lemma H_nz n k : H n k -> 0<n -> 0<k.
Proof.
induction 1; auto with arith; omega.
Qed.

Lemma H_lt n k : H n k -> 1<n -> 0<k<n.
Proof.
induction 1; auto with arith; omega.
Qed.

Ltac uniq :=
match goal with
| U:forall k, H ?x k -> _, V:H ?x ?y |- _ =>
   apply U in V; try subst y; uniq
| U:?x<>?x |- _ => now elim U
end.

Lemma H_unique n k k' : H n k -> H n k' -> k = k'.
Proof.
intros H1.
revert k'.
induction H1; inversion 1; subst; auto; try omega; uniq.
Qed.

Lemma H_step n k k' : H n k -> H (S n) k' -> k'=k \/ k' = S k.
Proof.
inversion 2; subst; intros; simpl in *; rewrite ?Nat.sub_0_r in *.
- replace k with 0 by (apply H_unique with 0; auto). auto.
- replace k with 1 by (apply H_unique with 1; auto). auto.
- replace k with 1 by (apply H_unique with 2; auto). auto.
- replace k with 2 by (apply H_unique with 3; auto). auto.
- replace x with k by (apply H_unique with n; auto). omega.
- replace y with k by (apply H_unique with n; auto). omega.
- replace k' with k by (apply H_unique with n; auto). omega.
Qed.

(* H can be implemented *)

Definition h_spec n : { k : nat | H n k }.
Proof.
induction n as [n h] using lt_wf_rec.
destruct (le_lt_dec n 4).
- clear h.
  destruct n as [|[|[|[|n]]]].
  { exists 0; auto. }
  { exists 1; auto. }
  { exists 1; auto. }
  { exists 2; auto. }
  { exists 3; assert (n=0) by omega; subst; auto. }
- destruct (h (n-2)) as (x,X); [omega|].
  destruct (h (n-1)) as (y,Y); [omega|].
  destruct (eq_nat_dec x y).
  + exists (S y). subst; auto.
  + destruct (h y) as (z,Z); [apply H_le in Y; omega|].
    destruct (h (S y)) as (t,T); [apply H_lt in Y; omega|].
    destruct (eq_nat_dec z t).
    * exists (S y). subst; eauto.
    * exists y. eauto.
Defined.

Definition h n := let (k,_) := h_spec n in k.

Lemma h_prop n : H n (h n).
Proof.
unfold h; now destruct h_spec.
Qed.

Lemma h_unique n k : H n k <-> k = h n.
Proof.
split.
- intros. eapply H_unique; eauto. apply h_prop.
- intros ->. apply h_prop.
Qed.

Lemma h_step n : h (S n) = h n \/ h (S n) = S (h n).
Proof.
destruct (@H_step n (h n) (h (S n))); auto using h_prop.
Qed.

(* The three situations a) b) c) expressed in terms of h. *)

Lemma h_a n : 0<n -> h (n-2) = h (n-1) -> h n = S (h (n-1)).
Proof.
destruct (le_lt_dec n 4).
- destruct n as [|[|[|[|n]]]].
  + omega.
  + reflexivity.
  + discriminate.
  + reflexivity.
  + replace n with 0 by omega. discriminate.
- intros.
  symmetry. apply h_unique.
  apply H_a; auto using h_prop.
  now apply h_unique.
Qed.

Lemma h_b n y : 4<n ->
 y = h (n-1) ->
 h (n-2) <> y ->
 h (S y) = h y ->
 h n = S y.
Proof.
 intros.
 symmetry. apply h_unique.
 apply (@H_b n (h (n-2)) y (h y));
  auto using h_prop.
 - subst. apply h_prop.
 - now apply h_unique.
Qed.

Lemma h_c n y : 4<n ->
 y = h (n-1) ->
 h (n-2) <> y ->
 h (S y) <> h y ->
 h n = y.
Proof.
 intros.
 symmetry. apply h_unique.
 apply (@H_c n (h (n-2)) y (h y) (h (S y)));
  auto using h_prop.
 subst. apply h_prop.
Qed.

Ltac H2h := match goal with
 | U: H _ _ |- _ => apply h_unique in U; H2h
 | _ => idtac
end.

Lemma h_eqn n : 3 < n -> h n + h (S (h (n-1))) = S n.
Proof.
 induction n as [|n IH].
 - inversion 1.
 - intros Hn.
   simpl. rewrite Nat.sub_0_r.
   assert (Hh := h_prop (S n)); inversion Hh; subst; try omega;
    simpl in *; rewrite ?Nat.sub_0_r in *; H2h.
   + reflexivity.
   + (* case a) *)
     rewrite <- H2, <- H4 in *. omega.
   + (* case b) *)
     assert (y = S x).
     { generalize (h_step (n-1)).
       replace (S (n-1)) with n by omega.
       omega. }
     rewrite <- H2, <- H3, <- H7, <- H6 in *. omega.
   + (* case c) *)
     rewrite <- H1 in *.
     rewrite H2 in *.
     assert (h n = S x).
     { generalize (h_step (n-1)).
       replace (S (n-1)) with n by omega.
       omega. }
     rewrite H7 in *.
     generalize (h_step (S x)). omega.
Qed.

(* This implementation of H is hence g' *)

Lemma h_is_g' : forall n, h n = g' n.
Proof.
 apply g'_eqn_unique; try reflexivity. apply h_eqn.
Qed.

Lemma H_is_g' n k : H n k <-> k = g' n.
Proof.
 now rewrite h_unique, h_is_g'.
Qed.

(* Presentation via a "delta" function *)

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
 rewrite <- !h_is_g' in *.
 rewrite (@h_b (S n) (h n)); try omega.
 f_equal. omega.
 simpl. omega.
 generalize (h_step (h n)). omega.
Qed.

Lemma delta_c n : 4<=n ->
 d (n-1) = 1 -> d (g' n) = 1 -> d n = 0.
Proof.
 unfold d.
 intros.
 replace (S (n-1)) with n in * by omega.
 rewrite <- !h_is_g' in *.
 rewrite (@h_c (S n) (h n)); try omega.
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

(* Another short equation for g', but this one cannot be used
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

(* This last equation f(f(n)) + f(n-1) = n for n > 3
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
 do 8 (destruct n; try omega). reflexivity.
Qed.

Lemma oups_eqn' n : 3<n -> oups (oups n) + oups (n-1) = n.
Proof.
intros.
destruct (le_lt_dec n 9).
- do 10 (destruct n; simpl; try omega).
- case_eq (Nat.even n); intros E.
  + rewrite (@oups_def n),E,!oups_def by omega.
    rewrite !Nat.even_sub,E by omega. simpl. omega.
  + rewrite (@oups_def n),E by omega. simpl.
    rewrite oups_def by omega.
    rewrite !Nat.even_sub,E by omega. simpl. omega.
Qed.

(* We will show later that if we require this equation along
  with a monotonicity constraint, then there is a unique solution
  (which is hence g'). *)

(* Study of the alternative equation and its consequences. *)

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

(* Alas, g(n) isn't unique for n>5 (e.g 4 or 5 for n=6) *)

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

(* A direct proof of the alternative equation for h,
   with first a auxiliary lemma. *)

Lemma h_nostep_inv n :
  2<n -> h n = h (n-1) -> h (S (h n)) = S (h (h n)).
Proof.
 intros Hn Hh.
 symmetry in Hh. apply h_unique in Hh.
 inversion Hh; subst; H2h; try omega.
 set (y := h (n-1)) in *. rewrite <- Hh.
 destruct (h_step y); trivial. congruence.
Qed.

Lemma h_eqn' n : 3<n -> h (h n) + h (n-1) = n.
Proof.
 induction n as [|n IH].
 - inversion 1.
 - intros Hn.
   simpl. rewrite Nat.sub_0_r.
   assert (Hh := h_prop (S n)); inversion Hh; subst; try omega;
    simpl in *; rewrite ?Nat.sub_0_r in *; H2h.
   + reflexivity.
   + (* case a) *)
     generalize (@h_nostep_inv n).
     rewrite <- H2, <- H4 in *. omega.
   + (* case b) *)
     generalize (h_step (n-1)).
     replace (S (n-1)) with n by omega.
     rewrite <- H2, <- H3, <- H5, <- H7 in *. omega.
   + (* case c) *)
     generalize (h_step (n-1)).
     replace (S (n-1)) with n by omega.
     rewrite <- H1, <- H2 in *. omega.
Qed.
