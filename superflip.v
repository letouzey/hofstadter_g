
Require Import Arith Omega Wf_nat List Program Program.Wf.
Require Import superfibo.
Set Implicit Arguments.

(* Source: Hofstadter's book: Goedel, Escher, Bach. *)

(* See first the previous file for the study of:
    G (S n) + G (G n) = S n
    G 0 = 0
   and the associated tree where nodes are labeled breadth-first
   from left to right. *)

(* Now, question by Hofstadter: what if we keep the same tree,
   but label the nodes from right to left ? *)


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
         generalize (@max_two_antecedents (g m) (m-1-1) m).
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

Lemma g'_eqn n : 4 <= n -> g' (S (g' (n-1))) = S n - g' n.
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
   rewrite <- EQ.
   replace (S (fib k) - 1) with (fib k) by omega.
   replace k with (S (k-1)) at 1 3 by omega.
   rewrite g'_fib, g'_Sfib by omega.
   replace (k-1) with (S (k-2)) by omega.
   rewrite g'_Sfib by omega.
   replace k with (S (S (k-2))) at 2 by omega.
   rewrite fib_eqn. omega.
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
     replace k with (S (k-1)) by omega.
     rewrite g'_Sfib by omega.
     assert (EQ' : g' n = fib k).
     { destruct (g'_step (n-1)) as [EQ'|EQ'];
       replace (S (n-1)) with n in EQ'; try omega.
       rewrite EQ in EQ'.
       assert (H' : depth (g' n) = k) by (apply depth_carac; omega).
       rewrite g'_depth in H'. unfold k in *. omega. }
     rewrite EQ'.
     assert (EQ'' : g' (n-1) = g' (fib (S k))) by now rewrite EQ, g'_fib.
     apply g'_max_two_antecedents in EQ''; [|omega].
     replace (S (n-1)) with n in EQ'' by omega.
     rewrite <- EQ''.
     rewrite fib_eqn'; omega.
   + (* g'(n-1) <> fib k *)
     assert (Hk'' : depth (S (g' (n-1))) = k-1).
     { apply depth_carac. omega.
       replace (S (k-1)) with k by omega.
       omega. }
     unfold g' at 1.
     rewrite flip_eqn0;
     rewrite g_depth, flip_depth, Hk''; [|omega].
     replace (S (S (k-1-1))) with k by omega.
     assert (LT : 1 < g' (n-1)).
     { unfold lt. change 2 with (g' 3). apply g'_mono. omega. }
     rewrite flip_S by omega.
     unfold g' at 1. rewrite flip_flip.
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

Lemma g'_eqn' n : 4 <= n -> g' (g' n) + g' (n-1) = n.
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

(* TODO: study unary/binary nodes of g' *)

(* TODO: montrer que g' est caractérisé par:
   a)  g' (S n) = g' n -> g' (n+2) = S (g' (S n))
   b)  g' (S n) = S (g' n) -> g' g' (S n) = g' (S (g' (S n)) ->
       g' (n+2) = S (g' (S n))
   c) sinon (g' (S n) = S (g' n) et g' (S (g' (S n))) = S' (g' g' (S n))
      alors g' (n+2) = g' (S n)
  Cf fichier superfibo2...
*)