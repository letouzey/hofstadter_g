
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
