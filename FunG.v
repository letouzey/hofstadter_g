(** * FunG : Hofstadter's G function and tree *)

Require Import Arith Lia Wf_nat List.
Require Import DeltaList Fib.
Set Implicit Arguments.

(** Study of the functional equation:
     - [G (S n) + G (G n) = S n]
     - [G 0 = 0]

    and its relationship with the Fibonacci sequence.

    References:
     - Hofstadter's book: Goedel, Escher, Bach, page 137.
     - Sequence A005206 on the Online Encyclopedia of Integer Sequences
       #<a href="http://oeis.org/A005206">#http://oeis.org/A005206#</a>#
*)

(** * Statement of the [G] equations as an inductive relation. *)

Inductive G : nat -> nat -> Prop :=
| G0 : G 0 0
| GS n a b c : G n a -> G a b -> S n = c+b -> G (S n) c.
Hint Constructors G.

Lemma G1 : G 1 1.
Proof.
eauto.
Qed.
Hint Resolve G1.

Lemma GS_inv n a : G (S n) a ->
 exists b c, G n b /\ G b c /\ S n = a + c.
Proof.
 inversion_clear 1 as [|? b c ? Hb Hc Hn].
 exists b; exists c. auto.
Qed.

(** A first upper bound on [G].
    It is used for proving that [G] is a total function. *)

Lemma G_le n a : G n a -> a <= n.
Proof.
revert a.
induction n using lt_wf_rec.
destruct n; inversion_clear 1; lia.
Qed.
Hint Resolve G_le.

Lemma G_rec (P:nat->Set) :
P 0 ->
(forall n, P n -> (forall a, G n a -> P a) -> P (S n)) ->
forall n, P n.
Proof.
intros P_0 P_S.
induction n as [[|n] IH] using lt_wf_rec.
- apply P_0.
- apply P_S.
  + apply IH. auto.
  + intros. apply IH. auto with arith.
Defined.

(** The [G] relation is indeed functional: *)

Lemma G_fun n a a' : G n a -> G n a' -> a = a'.
Proof.
revert a a'.
induction n as [|n IH IH'] using G_rec; intros a a' Ha Ha'.
- inversion_clear Ha; inversion_clear Ha'; trivial.
- destruct (GS_inv Ha) as (b & c & Hb & Hc & H).
  destruct (GS_inv Ha') as (b' & c' & Hb' & Hc' & H').
  replace b' with b in * by (apply IH; auto).
  replace c' with c in * by (apply (IH' b); auto).
  lia.
Qed.

(** * The [g] function, implementing the [G] relation. *)

Definition g_spec n : { a : nat | G n a }.
Proof.
induction n as [|n IH IH'] using G_rec.
- now exists 0.
- destruct IH as (a,Ha).
  destruct (IH' a Ha) as (b,Hb).
  assert (a <= n) by now apply G_le.
  assert (b <= a) by now apply G_le.
  exists (S n - b).
  eapply GS; eauto; lia.
Defined.

Definition g n := let (a,_) := (g_spec n) in a.

(*
Extraction Inline G_rec lt_wf_rec induction_ltof2.
Recursive Extraction g. (* TODO: des let-in parasites *)
*)

(* Compute map g (seq 0 10). *)
(*
  = 0 :: 1 :: 1 :: 2 :: 3 :: 3 :: 4 :: 4 :: 5 :: 6 :: nil
     : list nat
*)

Lemma g_correct n : G n (g n).
Proof.
unfold g; now destruct (g_spec n).
Qed.
Hint Resolve g_correct.

Lemma g_complete n p : G n p <-> p = g n.
Proof.
split; intros H.
- apply (G_fun H (g_correct n)).
- subst. apply g_correct.
Qed.

(** The initial equations, formulated for [g] *)

Lemma g_0 : g 0 = 0.
Proof.
reflexivity.
Qed.

Lemma g_eqn n : g (S n) + g (g n) = S n.
Proof.
unfold g.
destruct (g_spec (S n)) as (a,Ha).
destruct (g_spec n) as (b,Hb).
destruct (g_spec b) as (c,Hc).
destruct (GS_inv Ha) as (b' & c' & Hb' & Hc' & H).
rewrite (G_fun Hb Hb') in *.
rewrite (G_fun Hc Hc') in *. lia.
Qed.

(** Same, with subtraction *)

Lemma g_S n : g (S n) = S n - g (g n).
Proof.
 generalize (g_eqn n); lia.
Qed.

(** * Properties of [g] *)

Lemma g_unique f :
  f 0 = 0  ->
  (forall n, S n = f (S n)+f(f n)) ->
  forall n, f n = g n.
Proof.
intros f_0 f_S.
induction n as [|n IH IH'] using G_rec.
- now rewrite f_0, g_0.
- specialize (f_S n).
  rewrite IH in *.
  rewrite (IH' (g n)) in * by auto.
  generalize (g_eqn n). lia.
Qed.

Lemma g_step n : g (S n) = g n \/ g (S n) = S (g n).
Proof.
induction n as [|n IH IH'] using G_rec.
- compute; auto.
- rewrite (g_S n), (g_S (S n)).
  destruct IH as [-> | ->]; [lia|].
  destruct (IH' (g n)) as [-> | ->]; auto; lia.
Qed.

Lemma g_mono_S n : g n <= g (S n).
Proof.
 generalize (g_step n). lia.
Qed.

Lemma g_mono n m : n <= m -> g n <= g m.
Proof.
induction 1.
- trivial.
- transitivity (g m); auto using g_mono_S.
Qed.

Lemma g_le_S n : g (S n) <= S (g n).
Proof.
 generalize (g_step n). lia.
Qed.

Lemma g_le_add n m : g (n+m) <= n + g m.
Proof.
 induction n; trivial.
 - simpl. generalize (g_le_S (n+m)). lia.
Qed.

(** NB : in Coq, for natural numbers, 3-5 = 0 (truncated subtraction) *)

Lemma g_lipschitz n m : g m - g n <= m - n.
Proof.
destruct (le_ge_dec n m) as [H|H].
- induction H; try generalize (g_step m); lia.
- generalize (g_mono H). lia.
Qed.

Lemma g_nonzero n : 0 < n -> 0 < g n.
Proof.
 unfold lt. intros. change 1 with (g 1). now apply g_mono.
Qed.

Lemma g_0_inv n : g n = 0 -> n = 0.
Proof.
destruct n; trivial.
assert (0 < g (S n)) by (apply g_nonzero; auto with arith).
lia.
Qed.

Lemma g_nz n : n <> 0 -> g n <> 0.
Proof.
intros H. contradict H. now apply g_0_inv.
Qed.

Lemma g_fix n : g n = n <-> n <= 1.
Proof.
split.
- destruct n; auto.
  assert (H := g_eqn n).
  intros Eq; rewrite Eq in H; clear Eq.
  assert (H' : g (g n) = 0) by lia.
  do 2 apply g_0_inv in H'. now subst.
- inversion_clear 1 as [|? H0]; auto.
  inversion_clear H0; auto.
Qed.

Lemma g_le n : g n <= n.
Proof.
 apply G_le; auto.
Qed.

Lemma g_lt n : 1<n -> g n < n.
Proof.
intros H.
destruct (le_lt_or_eq _ _ (g_le n)); trivial.
rewrite g_fix in *. lia.
Qed.
Hint Resolve g_lt.

(** Two special formulations for [g_step] *)

Lemma g_next n a : g n = a -> (g (S n) <> a <-> g (S n) = S a).
Proof.
 generalize (g_step n). lia.
Qed.

Lemma g_prev n a : n <> 0 -> g n = a ->
 (g (n-1) <> a <-> g (n-1) = a - 1).
Proof.
 intros H Ha.
 assert (Ha' := g_nz H).
 generalize (g_step (n-1)). replace (S (n-1)) with n by lia.
 lia.
Qed.

(** [g] cannot stay flat very long *)

Lemma g_nonflat n : g (S n) = g n -> g (S (S n)) = S (g n).
Proof.
 intros H. generalize (g_eqn (S n)) (g_eqn n). rewrite H. lia.
Qed.

Lemma g_nonflat' n : g (S n) = g n -> g (n-1) = g n - 1.
Proof.
 destruct n.
 - now compute.
 - replace (S n - 1) with n by lia.
   intros H.
   destruct (g_step n) as [H'|H'].
   + apply g_nonflat in H'. lia.
   + lia.
Qed.

Lemma g_SS n : S (g n) <= g (S (S n)).
Proof.
 destruct (g_step n) as [E|E].
 - generalize (g_nonflat _ E). lia.
 - transitivity (g (S n)). lia. auto using g_mono_S.
Qed.

Lemma g_double_le n : n <= g (2*n).
Proof.
induction n.
- trivial.
- replace (2* S n) with (S (S (2*n))) by lia.
  transitivity (S (g (2*n))). lia. apply g_SS.
Qed.

Lemma g_div2_le n : n/2 <= g n.
Proof.
 rewrite <- Nat.div2_div.
 rewrite (Nat.div2_odd n) at 2.
 transitivity (g (2*Nat.div2 n)).
 apply g_double_le.
 apply g_mono. lia.
Qed.

(* Two consecutive steps are possible, but not three *)

Lemma g_maxsteps n : g (2+n) = 2 + g n -> g (3+n) = 2 + g n.
Proof.
 intros H.
 simpl in *.
 destruct (g_step n) as [H0|H0], (g_step (S n)) as [H1|H1]; try lia.
 assert (H2 := g_eqn n).
 assert (H3 := g_eqn (S n)).
 assert (H4 := g_eqn (S (S n))).
 assert (H5 : g(g(S n)) = g(g n)) by lia.
 rewrite H0 in H5.
 assert (H6 := g_nonflat _ H5).
 rewrite H1 in H4.
 rewrite <- H0 in H6. lia.
Qed.

(** Said otherwise, g(3+n) cannot be 3+g(n) *)

Lemma g_3_2 n : g (3+n) <= 2 + g n.
Proof.
 destruct (g_step n) as [H|H].
 - rewrite <- H. apply (g_le_add 2 (S n)).
 - destruct (g_step (S n)) as [H'|H'].
   + generalize (g_le_S (2+n)). simpl in *. lia.
   + rewrite H in H'. apply g_maxsteps in H'. lia.
Qed.

Lemma g_maxsteps_below n : g (2+n) = 2 + g n -> g (n-1) = g n.
Proof.
 intros H.
 assert (Nz : n<>0). { now intros ->. }
 assert (H' := g_3_2 (n-1)).
 replace (3+(n-1)) with (2+n) in * by lia.
 generalize (@g_mono (n-1) n). lia.
Qed.


(*==============================================================*)

(** * Antecedents by [g]

    Study of the reverse problem [g(x) = a] for some [a]. *)

Lemma g_max_two_antecedents a n m :
  g n = a -> g m = a -> n<m -> m = S n.
Proof.
intros Hn Hm H.
destruct m as [|m]; [inversion H|].
destruct n as [|n].
- compute in Hn; subst. now apply g_0_inv in Hm.
- generalize
   (g_eqn n) (g_eqn m) (g_step n) (g_step m)
   (g_lipschitz (g n) (g m)).
  lia.
Qed.

(** Another formulation of the same fact *)

Lemma g_inv n m :
  g n = g m -> (n = m \/ n = S m \/ m = S n).
Proof.
 intros.
 destruct (lt_eq_lt_dec n m) as [[LT|EQ]|LT]; auto.
 - generalize (@g_max_two_antecedents (g n) n m); auto.
 - generalize (@g_max_two_antecedents (g m) m n); auto.
Qed.

(** [g] is an onto map *)

Lemma g_onto a : exists n, g n = a.
Proof.
induction a.
- exists 0; trivial.
- destruct IHa as (n,Ha).
  destruct (g_step n); [ | exists (S n); lia].
  destruct (g_step (S n)); [ | exists (S (S n)); lia].
  exfalso.
  generalize (@g_max_two_antecedents a n (S (S n))). lia.
Qed.

(** * The [G] tree *)

(** [g] can be related to a infinite tree where:
    - nodes are labeled via a breadth-first traversal
    - from the label of a child node, [g] give the label
      of the father node.

<<
9 10 11 12 13
 \/   |  \ /
  6   7   8
   \ /   /
    4   5
     \ /
      3
      |
      2
      |
      1
>>

 We already proved that g is onto, hence each node has at least
 one child. A node is said to be unary if the node label has
 exactly one antecedent, and the node is said multary otherwise.
 We first prove that a multary node is actually binary.
*)

Definition Unary (g:nat->nat) a :=
 forall n m, g n = a -> g m = a -> n = m.

Definition Multary g a := ~ Unary g a.

Definition Binary (g:nat->nat) a :=
 exists n m,
   g n = a /\ g m = a /\ n <> m /\
   forall k, g k = a -> k = n \/ k = m.

Lemma multary_binary a : Multary g a <-> Binary g a.
Proof.
 unfold Multary.
 split.
 - intros U.
   assert (Ha : a<>0).
   { contradict U.
     subst.
     intros u v Hu Hv. apply g_0_inv in Hu. apply g_0_inv in Hv.
     now subst. }
   destruct (g_onto a) as (n,Hn).
   assert (Hn' : n<>0).
   { contradict Ha. now subst. }
   destruct (eq_nat_dec (g (S n)) a);
   destruct (eq_nat_dec (g (n-1)) a).
   + exfalso.
     generalize (@g_max_two_antecedents a (n-1) (S n)). lia.
   + exists n; exists (S n); repeat split; auto.
     intros k Hk.
     destruct (g_inv n k) as [H|[H|H]]; try lia.
     subst n. simpl in *. rewrite Nat.sub_0_r in *. lia.
   + exists n; exists (n-1); repeat split; auto; try lia.
     intros k Hk.
     destruct (g_inv n k) as [H|[H|H]]; try lia.
     subst k. lia.
   + elim U.
     intros u v Hu Hv.
     assert (u = n).
     { destruct (g_inv n u) as [H|[H|H]]; subst;
       simpl in *; rewrite ?Nat.sub_0_r in *; lia. }
     assert (v = n).
     { destruct (g_inv n v) as [H'|[H'|H']]; subst;
       simpl in *; rewrite ?Nat.sub_0_r in *; lia. }
     lia.
 - intros (n & m & Hn & Hm & Hnm & H) U.
   apply Hnm. now apply (U n m).
Qed.

(** We could even exhibit at least one child for each node *)

Definition rchild n := n + g n. (** rightmost son, always there *)
Definition lchild n := n + g n - 1. (** left son, if there's one *)

Lemma rightmost_child_carac a n : g n = a ->
 (g (S n) = S a <-> n = rchild a).
Proof.
 intros Hn.
 assert (H' := g_eqn n).
 rewrite Hn in H'.
 unfold rchild; lia.
Qed.

Lemma g_onto_eqn a : g (rchild a) = a.
Proof.
destruct (g_onto a) as (n,Hn).
destruct (g_step n) as [H|H].
- unfold rchild.
  rewrite <- Hn. rewrite <- H at 1 3. f_equal. apply g_eqn.
- rewrite Hn in H.
  rewrite rightmost_child_carac in H; trivial. congruence.
Qed.

(** This provides easily a first relationship between g and
    Fibonacci numbers *)

Lemma g_fib n : n <> 0 -> g (fib (S n)) = fib n.
Proof.
induction n.
- now destruct 1.
- destruct n.
  + reflexivity.
  + intros _. rewrite fib_eqn.
    rewrite <- IHn; auto.
    apply g_onto_eqn.
Qed.

Lemma g_fib' n : 1 < n -> g (fib n) = fib (n-1).
Proof.
 destruct n.
 - lia.
 - intros. rewrite g_fib; f_equal; lia.
Qed.

Lemma g_Sfib n : 1 < n -> g (S (fib (S n))) = S (fib n).
Proof.
 intros.
 rewrite <- (@g_fib n) by lia.
 apply rightmost_child_carac; trivial.
 unfold rchild.
 now rewrite g_fib, g_fib', fib_eqn' by lia.
Qed.

Lemma g_Sfib' n : 2 < n -> g (S (fib n)) = S (fib (n-1)).
Proof.
 destruct n.
 - lia.
 - intros. rewrite g_Sfib; do 2 f_equal; lia.
Qed.

(*==============================================================*)

(** * Shape of the [G] tree *)

(** Let's study now the shape of the G tree.
    First, we prove various characterisation of [Unary] and [Binary] *)

Lemma g_children a n : g n = a ->
  n = rchild a \/ n = lchild a.
Proof.
intros Hn.
destruct (g_step n) as [H|H].
- right.
  destruct (g_step (S n)) as [H'|H'].
  + exfalso.
    generalize (@g_max_two_antecedents a n (S (S n))). lia.
  + rewrite rightmost_child_carac in H'; trivial.
    rewrite H, Hn in H'. unfold lchild, rchild in *; lia.
- rewrite <- (@rightmost_child_carac a n); lia.
Qed.

Lemma g_lchild a :
 g (lchild a) = a - 1 \/ g (lchild a) = a.
Proof.
 destruct (le_gt_dec a 0).
  + replace a with 0 by lia. compute. auto.
  + assert (0 < rchild a) by (unfold rchild; generalize (@g_nonzero a); lia).
    destruct (g_step (lchild a)) as [H'|H'];
    replace (S (lchild a)) with (rchild a) in * by
      (unfold lchild, rchild in *; lia);
    rewrite g_onto_eqn in *; lia.
Qed.

Lemma unary_carac1 a :
 Unary g a <-> forall n, g n = a -> n = rchild a.
Proof.
split; intros H.
- intros n Hn. apply H; trivial. apply g_onto_eqn.
- intros n m Hn Hm. apply H in Hn. apply H in Hm. lia.
Qed.

Lemma unary_carac2 a :
 Unary g a <-> g (lchild a) = a - 1.
Proof.
rewrite unary_carac1.
split; intros H.
- destruct (g_lchild a); trivial.
  assert (lchild a = rchild a) by (apply H; lia).
  unfold rchild, lchild in *; lia.
- intros n Hn.
  destruct (g_children _ Hn) as [H'|H']; trivial.
  rewrite <- H' in H.
  replace a with 0 in * by lia. exact H'.
Qed.

Lemma binary_carac1 a :
 Multary g a <-> a <> 0 /\ forall n, (g n = a <-> n = rchild a \/ n = lchild a).
Proof.
unfold Multary; rewrite unary_carac2.
split.
- intros H.
  assert (a<>0). { contradict H; now subst. }
  split; trivial.
  destruct (g_lchild a) as [H'|H']; [intros; lia|].
  clear H.
  split.
  + apply g_children.
  + destruct 1; subst n. apply g_onto_eqn. auto.
- intros (Ha,H) H'.
  assert (g (lchild a) = a). { apply H; now right. }
  lia.
Qed.

Lemma binary_carac2 a :
 Multary g a <-> (a <> 0 /\ g (lchild a) = a).
Proof.
unfold Multary; rewrite unary_carac2.
split.
- intros H.
  assert (a<>0). { contradict H; now subst. }
  split; trivial.
  destruct (g_lchild a); lia.
- lia.
Qed.

Lemma unary_or_multary n : Unary g n \/ Multary g n.
Proof.
 destruct (eq_nat_dec n 0).
 - left. subst. apply unary_carac2. reflexivity.
 - destruct (eq_nat_dec (g (lchild n)) n).
   + right. apply binary_carac2; auto.
   + left. apply unary_carac2. apply g_prev; auto. lia.
     apply g_onto_eqn.
Qed.

Lemma unary_xor_multary n : Unary g n -> Multary g n -> False.
Proof.
 intuition.
Qed.

(** Now we state the arity of node children *)

Lemma leftmost_son_is_binary n p :
  g p = n -> g (p-1) <> n -> Multary g p.
Proof.
 intros Hp Hp'.
 assert (Hp0 : p<>0). { intros Eq. rewrite Eq in *. auto. }
 assert (Hn0 := g_nz Hp0).
 rewrite g_prev in Hp'; auto.
 destruct (g_lchild p) as [Hq1|Hq1]; [|apply binary_carac2; auto].
 assert (Hq := g_onto_eqn p).
 change (lchild p) with (rchild p - 1) in *.
 set (q:=rchild p) in *.
 assert (q<>0) by (unfold q, rchild; lia).
 clearbody q.
 assert (Eq := g_eqn (q-1)).
 replace (S (q-1)) with q in Eq by lia.
 assert (Eq' := g_eqn q).
 rewrite Hq1,Hp' in Eq.
 rewrite Hq,Hp in Eq'.
 assert (Hq' : g (S q) = p) by lia.
 intro U. specialize (U q (S q) Hq Hq'). lia.
Qed.

Lemma unary_rchild_is_binary n : n <> 0 ->
  Unary g n -> Multary g (rchild n).
Proof.
 intros H U. apply (@leftmost_son_is_binary n).
 - apply g_onto_eqn.
 - rewrite unary_carac2 in U. unfold lchild, rchild in *; lia.
Qed.

Lemma binary_lchild_is_binary n :
  Multary g n -> Multary g (lchild n).
Proof.
 rewrite binary_carac2. intros (B0,B1).
 apply (@leftmost_son_is_binary n); trivial.
 intros Eq.
 generalize (@g_max_two_antecedents n _ _ Eq (g_onto_eqn n)).
 assert (H := g_nz B0).
 unfold lchild, rchild in *. lia.
Qed.

Lemma binary_rchild_is_unary n :
  Multary g n -> Unary g (rchild n).
Proof.
 rewrite binary_carac2. intros (B0,B1).
 assert (Hp := g_onto_eqn n).
 assert (Hq := g_onto_eqn (lchild n)).
 set (p:=lchild n) in *.
 assert (g (S (rchild p)) = S p). { apply rightmost_child_carac; auto. }
 apply unary_carac2.
 change (g (lchild (rchild n)) = p).
 unfold lchild. rewrite Hp.
 replace (rchild n) with (S p) by (unfold p, rchild, lchild; lia).
 replace (S p + n -1) with (p + n) by lia.
 rewrite <- B1. apply g_onto_eqn.
Qed.

(** Hence the shape of the [G] tree is a repetition of this pattern:
<<
        r
        |
    p   q
     \ /
      n
>>
  where [n] and [p] and [r=n+q] are binary nodes and
  [q=p+1=n+g(n)] is unary.

  Fractal aspect : each binary nodes (e.g. [n], [p] and [r] above)
  have the same infinite shape of tree above them
  (which is the shape of [G] apart from special initial nodes 1 2):
<<
     A           A
     |           |
     .       A   .
     |        \ /
 G = .     A = .
>>
*)


(*==============================================================*)

(** * Another equation about [g]

    This one will be used later when flipping [G] left/right. *)

Lemma g_alt_eqn n : g n + g (g (S n) - 1) = n.
Proof.
 destruct (eq_nat_dec n 0) as [Hn|Hn].
 - now subst.
 - assert (Hn' := g_nz Hn).
   case (g_step n) as [H|H].
   + (* n left of a binary node *)
     rewrite H.
     generalize (g_eqn (n-1)).
     case (g_step (n - 1));
     replace (S (n - 1)) with n by lia.
     * generalize (@g_max_two_antecedents (g n) (n-1) (S n)). lia.
     * intros. replace (g n - 1) with (g (n-1)) by lia. lia.
   + (* n is rightmost child *)
     generalize (g_eqn n). rewrite H. simpl. rewrite <- minus_n_O.
     lia.
Qed.


(*==============================================================*)

(** * Depth in the [G] tree *)

(** The depth of a node in the [G] tree is the number of
    iteration of [g] needed before reaching node 1 *)

Notation "f ^^ n" := (Nat.iter n f) (at level 30, right associativity).

Lemma iter_S (f:nat->nat) n p : (f^^(S n)) p = (f^^n) (f p).
Proof.
 revert p.
 induction n as [|n IH]; intros; trivial. simpl. now rewrite <- IH.
Qed.

(* Compute (g^^3) 13. *)

Require Import Program Program.Wf.

Program Fixpoint depth (n:nat) { measure n } : nat :=
 match n with
 | 0 => 0
 | 1 => 0
 | _ => S (depth (g n))
 end.
Next Obligation.
 apply g_lt. lia.
Qed.

(* Compute depth 13. *)

Lemma depth_SS n : depth (S (S n)) = S (depth (g (S (S n)))).
Proof.
 now WfExtensionality.unfold_sub depth (depth (S (S n))).
Qed.

Lemma depth_eqn n : 1<n -> depth n = S (depth (g n)).
Proof.
 destruct n as [|[|n]].
 - lia.
 - lia.
 - intros _. apply depth_SS.
Qed.

Lemma g_depth n : depth (g n) = depth n - 1.
Proof.
 destruct (le_lt_dec n 1) as [LE|LT].
 - assert (H : n=0 \/ n=1) by lia.
   destruct H as [-> | ->]; reflexivity.
 - rewrite (depth_eqn LT). lia.
Qed.

Lemma depth_correct n : n <> 0 -> (g^^(depth n)) n = 1.
Proof.
 induction n as [[|[|n]] IH] using lt_wf_rec.
 - lia.
 - reflexivity.
 - intros _. rewrite depth_SS.
   set (n' := S (S n)) in *. rewrite iter_S. apply IH.
   + apply g_lt. unfold n'; lia.
   + apply g_nz. unfold n'; lia.
Qed.

Lemma depth_minimal n : 1<n -> 1 < ((g^^(depth n - 1)) n).
Proof.
 induction n as [[|[|n]] IH] using lt_wf_rec.
 - lia.
 - lia.
 - intros _. rewrite depth_SS.
   simpl. rewrite <- minus_n_O.
   set (n' := S (S n)) in *.
   destruct (eq_nat_dec (g n') 1) as [->|NE].
   + simpl. unfold n'; lia.
   + assert (H : g n' <> 0) by (apply g_nz; unfold n'; lia).
     assert (depth (g n') <> 0).
     { intro EQ. generalize (depth_correct H). now rewrite EQ. }
     replace (depth (g n')) with (S (depth (g n') - 1)) by lia.
     rewrite iter_S.
     apply IH.
     * apply g_lt. unfold n'; lia.
     * lia.
Qed.

Lemma depth_mono n m : n <= m -> depth n <= depth m.
Proof.
 revert m.
 induction n as [[|[|n]] IH] using lt_wf_rec; intros m H.
 - change (depth 0) with 0. auto with arith.
 - change (depth 1) with 0. auto with arith.
 - destruct m as [|[|m]]; try lia.
   rewrite 2 depth_SS.
   apply le_n_S.
   apply IH.
   + apply g_lt. lia.
   + now apply g_mono.
Qed.

Lemma depth_fib k : depth (fib k) = k-2.
Proof.
 induction k as [|[|[|k]] IH].
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - rewrite depth_eqn.
   + rewrite g_fib, IH; auto. lia.
   + unfold lt. change 2 with (fib 3). apply fib_mono. lia.
Qed.

Lemma depth_Sfib k : 1 < k -> depth (S (fib k)) = k-1.
Proof.
 induction k as [|[|[|k]] IH].
 - lia.
 - lia.
 - reflexivity.
 - intros _.
   rewrite depth_eqn.
   + rewrite g_Sfib, IH; lia.
   + unfold lt. apply le_n_S. now apply fib_nz.
Qed.

Lemma depth_0 n : depth n = 0 <-> n <= 1.
Proof.
 destruct n as [|[|n]].
 - compute; auto with arith.
 - compute; auto with arith.
 - rewrite depth_SS. lia.
Qed.

Lemma depth_carac k n : k <> 0 ->
  (depth n = k <-> S (fib (S k)) <= n <= fib (S (S k))).
Proof.
 intros Hk.
 split; intros H.
 - split.
   + destruct (le_lt_dec n (fib (S k))) as [LE|LT]; trivial.
     apply depth_mono in LE. rewrite depth_fib in LE. lia.
   + destruct (le_lt_dec n (fib (S (S k)))) as [LE|LT]; trivial.
     unfold lt in LT. apply depth_mono in LT.
     rewrite depth_Sfib in LT; lia.
 - destruct H as (H1,H2).
   apply depth_mono in H1. apply depth_mono in H2.
   rewrite depth_fib in H2; rewrite depth_Sfib in H1; lia.
Qed.

(** Conclusion: for k>0,
   - [1+fib (k+1)] is the leftmost node at depth [k]
   - [fib (k+2)] is the rightmost node at depth [k]
   - hence we have [fib (k+2) - fib (k+1) = fib k] nodes at depth [k].
*)

(** Alternatively, we could also have considered
     - [U(k)] : number of unary nodes at depth [k]
     - [B(k)] : number binary nodes at depth [k]

    and their recursive equations:
     - [U(k+1) = B(k)]
     - [B(k+1) = U(k)+B(k)]

    These numbers are also Fibonacci numbers (except when [k=0]),
    along with the number of nodes at depth [k] which is
    [U(k)+B(k)].
*)


(*==============================================================*)

(* begin hide *)
(* now in Coq stdlib's List.v in 8.5 *)
Lemma map_ext_in :
  forall (A B : Type)(f g:A->B) l,
    (forall a, In a l -> f a = g a) -> map f l = map g l.
Proof.
  induction l; simpl; auto.
  intros; rewrite H by intuition; rewrite IHl; auto.
Qed.
(* end hide *)

Lemma map_S_pred l : ~In 0 l -> map S (map pred l) = l.
Proof.
 intros.
 rewrite map_map. rewrite <- (map_id l) at 2.
 apply map_ext_in.
 intros a Ha. assert (a<>0) by congruence. lia.
Qed.

(** * [g] and Fibonacci decomposition.

   We now prove that g is simply "shifting" the Fibonacci
   decomposition of a number, i.e. removing 1 at all the ranks
   in this decomposition.

   For proving this result, we need to consider relaxed
   decompositions where consecutive fibonacci terms may occur
   (but still no [fib 0] nor [fib 1] in the decomposition).
   These decompositions aren't unique. We consider here
   these decomposition with the lowest terms first, to ease
   the following proof.
*)

Lemma g_sumfib l :
  Delta 1 (0::l) -> g (sumfib (List.map S l)) = sumfib l.
Proof.
 remember (sumfib (List.map S l)) as n eqn:E.
 revert l E.
 induction n  as [[|n] IH] using lt_wf_rec; intros [|k l].
 - trivial.
 - simpl map. rewrite sumfib_cons. generalize (fib_S_nz k). intros. lia.
 - discriminate.
 - simpl map. rewrite sumfib_cons.
   intros E Hl.
   rewrite g_S.
   inversion_clear Hl.
   case (eq_nat_dec k 1) as [Hk|Hk].
   + (* k = 1 *)
     subst k. simpl sumfib. injection E as E'.
     assert (Nz : ~In 0 l).
     { intro IN. apply Delta_alt in H0. apply H0 in IN. lia. }
     assert (E1 : g n = sumfib l).
     { apply IH; auto. eauto using Delta_low_hd. }
     assert (E2 : g (g n) = sumfib (map pred l)).
     { apply IH; auto.
       - generalize (g_le n); lia.
       - now rewrite map_S_pred.
       - apply Delta_pred in H0; eauto. }
     apply sumfib_eqn in Nz. lia.
   + (* 1 < k *)
     destruct (Nat.Even_or_Odd k) as [(k2,Hk2)|(k2,Hk2)].
     * (* k even *)
       set (l0 := odds (k2-1)).
       assert (Hl0 : sumfib l0 = pred (fib k)).
       { rewrite Hk2. unfold l0. rewrite sumfib_odds.
         do 3 f_equal. lia. }
       assert (Hl0' : sumfib (map S l0) + 2 = fib (S k)).
       { unfold l0.
         rewrite Nat.add_succ_r.
         change (sumfib (2 :: map S (odds (k2-1))) + 1 = fib (S k)).
         rewrite <- evens_S, sumfib_evens.
         replace (2 * S (k2-1)+1) with (S k) by lia.
         generalize (@fib_nz (S k)); lia. }
       assert (Delta 1 ((2::l0)++l)).
       { apply Delta_app with k; auto; unfold l0.
         - apply Delta_S_cons, Delta_odds.
         - simpl. intros y [Hy|Hy]; try apply odds_in in Hy; lia. }
       simpl app in *.
       assert (IN : forall x, In x (l0++l) -> 2<x).
       { apply Delta_alt in H1. intuition. }
       assert (~In 0 (l0++l)).
       { intro I0. apply IN in I0. lia. }
       assert (G : g n = sumfib (1 :: l0 ++ l)).
       { apply IH; auto.
         simpl. rewrite map_app, sumfib_app. lia.
         constructor; eauto using Delta_low_hd. }
       assert (GG : g (g n) = sumfib (map pred (2 :: l0++l))).
       { apply IH.
         - generalize (g_le n); lia.
         - rewrite G. simpl. f_equal. now rewrite map_S_pred.
         - change (Delta 1 (map pred (1::2::l0++l))).
           apply Delta_pred. simpl; intuition.
           constructor; auto. }
       simpl sumfib.
       rewrite GG, E, <- Hl0'. simpl.
       rewrite Nat.add_shuffle0, <- sumfib_app, <- map_app.
       transitivity (S (sumfib (l0++l))).
       rewrite <- sumfib_eqn; auto; lia.
       rewrite sumfib_app. generalize (@fib_nz k); lia.
     * (* k odd *)
       set (l0 := evens k2).
       assert (Hl0 : sumfib l0 = pred (fib k)).
       { rewrite Hk2. unfold l0. apply sumfib_evens. }
       assert (Hl0' : S (sumfib (map S l0)) = fib (S k)).
       { unfold l0.
         rewrite S_evens, sumfib_odds.
         replace (2*(S k2)) with (S k) by lia.
         generalize (@fib_nz (S k)); lia. }
       assert (Delta 1 ((1::l0)++l)).
       { apply Delta_app with k; auto; unfold l0.
         - apply Delta_S_cons, Delta_evens.
         - simpl. intros y [Hy|Hy]; try apply evens_in in Hy; lia. }
       simpl app in *.
       assert (~In 0 (l0++l)).
       { apply Delta_alt in H1. intro I0. apply H1 in I0. lia. }
       assert (G : g n = sumfib (l0 ++ l)).
       { apply IH; eauto using Delta_low_hd.
         rewrite map_app, sumfib_app. lia. }
       assert (GG : g (g n) = sumfib (map pred (l0++l))).
       { apply IH.
         - generalize (g_le n); lia.
         - now rewrite map_S_pred.
         - change (Delta 1 (map pred (1::l0++l))).
           apply Delta_pred; eauto using Delta_low_hd. }
       simpl sumfib.
       rewrite GG, E, <- Hl0'.
       simpl plus.
       rewrite <- sumfib_app, <- map_app.
       transitivity (S (sumfib (l0++l))).
       rewrite <- sumfib_eqn; auto; lia.
       rewrite sumfib_app. generalize (@fib_nz k); lia.
Qed.

Lemma g_sumfib' l : Delta 1 (1::l) ->
 g (sumfib l) = sumfib (map Nat.pred l).
Proof.
 intros.
 assert (~In 0 (1::l)) by eauto.
 assert (~In 0 l) by (simpl in *; intuition).
 rewrite <- (map_S_pred l) at 1; auto.
 apply g_sumfib.
 change (Delta 1 (map pred (1::l))).
 apply Delta_pred; auto.
Qed.

(** same result, for canonical decomposition expressed in rev order *)

Lemma g_sumfib_rev l : ~In 0 l -> ~In 1 l -> DeltaRev 2 l ->
 g (sumfib l) = sumfib (map Nat.pred l).
Proof.
 intros.
 set (l' := map pred (rev l)).
 assert (Hl : l = map S (rev l')).
 { unfold l'. rewrite <- map_rev, rev_involutive.
   now rewrite map_S_pred. }
 rewrite Hl, !map_rev, !sumfib_rev.
 rewrite g_sumfib.
 - f_equal. rewrite map_map. simpl. symmetry. apply map_id.
 - apply Delta_alt; split.
   + apply Delta_S. unfold l'. apply Delta_pred.
     * now rewrite <- in_rev.
     * now apply Delta_rev.
   + intros y. unfold l'. rewrite in_map_iff.
     intros (x & Hx & IN). rewrite <- in_rev in IN.
     destruct x as [|[|x]]; simpl in *; intuition.
Qed.

(** Beware! In the previous statements, [map pred l] might
    not be a canonical decomposition anymore, since 1 could appear.
    In this case, 1 could be turned into a 2 (since [fib 1 = fib 2]),
    and then we should saturate with Fibonacci equations
    ([fib 2 + fib 3 = fib 4], etc) to regain a canonical
    decomposition (with no consecutive fib terms), see [Fib.norm].*)

(** * [g] and classification of Fibonacci decompositions.

    Most of these results will be used in next file about
    the flipped [G] tree. *)

Lemma g_Low n k : 2<k -> Fib.Low 2 n k -> Fib.Low 2 (g n) (k-1).
Proof.
 intros K (l & -> & D & _).
 assert (~In 0 (k::l)) by (eapply Delta_nz; eauto; lia).
 rewrite g_sumfib'; eauto.
 rewrite (Nat.sub_1_r).
 exists (map Nat.pred l). repeat split; auto; try lia.
 apply Delta_pred in D; auto.
Qed.

Lemma g_Low' n k : 2<k -> Fib.Low 1 n k -> Fib.Low 1 (g n) (k-1).
Proof.
 intros K (l & -> & D & _).
 assert (~In 0 (k::l)) by (eapply Delta_nz; eauto; lia).
 rewrite g_sumfib'; auto with arith.
 rewrite (Nat.sub_1_r).
 exists (map Nat.pred l). repeat split; auto; try lia.
 apply Delta_pred in D; auto.
Qed.

Lemma g_Two n : Fib.Two 2 n -> g (S n) = g n.
Proof.
 intros (l & H & Hl & _).
 rewrite H.
 change (S (sumfib (2::l))) with (sumfib (3::l)).
 rewrite !g_sumfib'; eauto.
Qed.

Lemma g_Two_iff n : Fib.Two 2 n <-> g (S n) = g n.
Proof.
 split. apply g_Two.
 destruct (decomp_exists n) as (l & E & D).
 destruct l as [|k l].
 - simpl in E. now subst.
 - destruct k as [|[|[|k]]].
   + inversion_clear D; lia.
   + inversion_clear D; lia.
   + intros _. exists l; repeat split; eauto.
   + intros E'. exfalso.
     subst n.
     change (S (sumfib (S (S (S k)) :: l))) with
     (sumfib (2::S (S (S k))::l)) in E'.
     rewrite !g_sumfib' in *; auto.
     * simpl map in *.
       rewrite sumfib_cons in E'. simpl fib in E'. lia.
     * do 2 (constructor; eauto); lia.
Qed.

Lemma g_not_Two n : ~Fib.Two 2 n -> g (S n) = S (g n).
Proof.
 rewrite g_Two_iff. generalize (g_step n). lia.
Qed.

Lemma Two_g n : Fib.Two 2 n -> Fib.Even 2 (g n).
Proof.
 intros (l & -> & D & _).
 apply Even_12. apply Two_Even.
 exists (map pred l); repeat split; auto.
 rewrite g_sumfib'; eauto.
 apply Delta_S_cons, Delta_pred in D; eauto.
Qed.

Lemma Three_g n : Fib.Three 2 n -> Fib.Two 2 (g n).
Proof.
apply g_Low. auto.
Qed.

Lemma g_Three_iff n : Fib.Three 2 n <-> g(2 + n) = 2 + g n.
Proof.
 split.
 - intros (l & -> & D & _).
   simpl.
   change (g (sumfib (2::4::l)) = 2 + g (sumfib (3::l))).
   rewrite !g_sumfib'; auto.
 - intros E.
   destruct (Nat.eq_dec n 0) as [->|Hn].
   + discriminate.
   + destruct (decomp_complete Hn) as [H|[H|H]]; auto.
     * rewrite g_Two_iff in H.
       generalize (g_step (S n)). simpl in *. lia.
     * apply High_succ_Two in H. destruct H as (H,_).
       rewrite g_Two_iff in H.
       generalize (g_step n). simpl in *. lia.
Qed.

Lemma ThreeOdd_Sg n : Fib.ThreeOdd 2 n -> Fib.ThreeEven 1 (S (g n)).
Proof.
intros (k & l & -> & D).
assert (1<k) by (inversion_clear D; lia).
rewrite g_sumfib'; eauto.
exists k; exists (map pred l); split; auto.
- simpl. do 4 f_equal. lia.
- apply Delta_pred in D; eauto. simpl in D.
  replace (2*k) with (pred (2*k+1)) by lia. auto.
Qed.

Lemma ThreeEven_Sg n : Fib.ThreeEven 2 n -> Fib.ThreeOdd 2 (S (g n)).
Proof.
intros (k & l & -> & D).
apply ThreeOdd_12.
assert (1<k) by (inversion_clear D; lia).
rewrite g_sumfib'; eauto.
exists (k-1); exists (map pred l); split; auto.
- simpl. do 4 f_equal. lia.
- apply Delta_pred in D; eauto. simpl in D.
  replace (2*(k-1)+1) with (pred (2*k)) by lia. auto.
Qed.

Lemma High_g n : Fib.High 2 n -> ~Fib.Two 2 (g n).
Proof.
 intros (k & K & L) L'.
 apply g_Low in L; try lia.
 generalize (Low_unique L L'). lia.
Qed.

Lemma High_Sg n : Fib.High 2 n -> Fib.Even 2 (S (g n)).
Proof.
intros (k & K & l & -> & D & _).
apply Even_12. apply Two_Even.
rewrite g_sumfib'; eauto.
exists (map pred (k::l)). repeat split; simpl; auto.
constructor. lia. change (Delta 1 (map pred (k :: l))).
apply Delta_pred; eauto.
eapply Delta_nz; eauto. lia.
constructor. lia. eauto.
Qed.

Lemma Odd_g n : Fib.Odd 2 n -> Fib.Even 2 (g n).
Proof.
 intros (k & L).
 assert (k<>0) by (apply Low_nz in L; lia).
 apply g_Low in L; try lia.
 exists k. now replace (2*k) with (2*k+1-1) by lia.
Qed.

Lemma Even_g n : Fib.Even 2 n -> ~Fib.Two 2 n -> Fib.Odd 2 (g n).
Proof.
 intros (k & L) L'.
 assert (k<>0) by (intros ->; now destruct L).
 assert (k<>1) by (intros ->; intuition).
 apply g_Low in L; try lia.
 exists (k-1). now replace (2*(k-1)+1) with (2*k-1) by lia.
Qed.

Lemma Odd_gP n : Fib.Odd 2 n -> g (n-1) = g n.
Proof.
 intros DE. apply Odd_pred_Two in DE.
 destruct n; trivial.
 simpl in *. rewrite Nat.sub_0_r in *. symmetry. now apply g_Two.
Qed.

Lemma Even_gP n : Fib.Even 2 n -> g (n-1) = (g n) - 1.
Proof.
 intros DO.
 assert (DE : ~Fib.Odd 2 n).
 { intro. eapply Even_xor_Odd; eauto. }
 rewrite Odd_pred_Two in DE.
 rewrite g_Two_iff in DE.
 destruct n; trivial.
 simpl in *; rewrite Nat.sub_0_r in *.
 destruct (g_step n); lia.
Qed.

Lemma g_pred_fib_odd k : g (pred (fib (2*k+1))) = fib (2*k).
Proof.
 destruct k.
 - reflexivity.
 - rewrite <- Nat.sub_1_r.
   rewrite Odd_gP.
   + rewrite g_fib'. f_equal; lia. lia.
   + exists (S k). exists (@nil nat); repeat split; simpl; auto. lia.
Qed.

Lemma g_pred_fib_even k : g (pred (fib (2*k))) = fib (2*k-1) - 1.
Proof.
 destruct k.
 - reflexivity.
 - rewrite <- Nat.sub_1_r.
   rewrite Even_gP.
   + rewrite g_fib'; auto. lia.
   + exists (S k); exists (@nil nat); repeat split; simpl; auto. lia.
Qed.

Lemma g_pred_pred_fib k : g (fib k - 2) = fib (k-1) - 1.
Proof.
 destruct (le_lt_dec k 2).
 - destruct k as [|[|[|k]]]; try reflexivity. lia.
 - replace (fib k - 2) with (fib k - 1 - 1) by lia.
   destruct (Nat.Even_or_Odd k) as [(k',->)|(k',->)].
   + rewrite Odd_gP.
     * rewrite Nat.sub_1_r. apply g_pred_fib_even.
     * apply EvenHigh_pred_Odd.
       { exists k'; exists (@nil nat).
         repeat split; simpl; auto. lia. }
       { exists (2*k'). split. lia.
         exists (@nil nat); repeat split; simpl; auto; lia. }
   + rewrite Even_gP.
     * f_equal. rewrite Nat.sub_1_r. rewrite g_pred_fib_odd.
       f_equal. lia.
     * apply Two_Even, Odd_pred_Two.
       exists k'; exists (@nil nat).
       simpl; repeat split; auto. lia.
Qed.

(*==============================================================*)

(** * Fibonacci decomposition and [G] node arity *)

Lemma decomp_rchild l : Delta 1 (1::l) ->
  rchild (sumfib l) = sumfib (map S l).
Proof.
 intros.
 unfold rchild.
 rewrite g_sumfib' by trivial.
 apply sumfib_eqn.
 apply Delta_alt in H. intro IN. apply H in IN. lia.
Qed.

Lemma decomp_unary n : Fib.Odd 2 n -> Unary g n.
Proof.
 intros D.
 rewrite unary_carac2.
 unfold lchild.
 rewrite <- (Odd_gP D).
 replace (n + g (n-1) - 1) with (n - 1 + g (n-1)).
 - apply g_onto_eqn.
 - destruct n; trivial; lia.
Qed.

Lemma decomp_binary n : Fib.Even 2 n -> Binary g n.
Proof.
 intros D.
 rewrite <- multary_binary, binary_carac2.
 assert (n<>0).
 { destruct D as (k & l & -> & D & H). rewrite sumfib_0.
   discriminate. eapply Delta_nz; eauto. lia. }
 split; trivial.
 unfold lchild.
 rewrite Nat.add_comm, Nat.add_sub_swap, Nat.add_comm
  by (apply (@g_mono 1 n); lia).
 rewrite <- (Even_gP D).
 replace (n+g(n-1)) with (S (n-1+g(n-1))) by lia.
 replace n with (S (n-1)) at 3 by lia.
 apply rightmost_child_carac; eauto using g_onto_eqn.
Qed.

Lemma decomp_unary_iff n : Fib.Odd 2 n <-> (n<>0 /\ Unary g n).
Proof.
 split.
 - split.
   + destruct H as (k & l & -> & D & H). rewrite sumfib_0.
     discriminate. eapply Delta_nz; eauto. lia.
   + now apply decomp_unary.
 - intros (Hn,H).
   destruct (Fib.Even_or_Odd Hn) as [Ev|Od]; trivial.
   apply decomp_binary in Ev. apply multary_binary in Ev.
   elim (unary_xor_multary H Ev).
Qed.

Lemma decomp_binary_iff n : Fib.Even 2 n <-> Binary g n.
Proof.
 split.
 - apply decomp_binary.
 - rewrite <- multary_binary; intros B.
   assert (Hn : n<>0).
   { intros ->. rewrite binary_carac2 in B. intuition. }
   destruct (Fib.Even_or_Odd Hn) as [Ev|Od]; trivial.
   apply decomp_unary in Od.
   elim (unary_xor_multary Od B).
Qed.


(*==============================================================*)

(** * [g] and "delta" equations *)

(** We can characterize [g] via its "delta" (a.k.a increments).
   Let [d(n) = g(n+1)-g(n)]. For all [n]:

    - a) if [d(n) = 0] then [d(n+1) = 1]
    - b) if [d(n) <> 0] then [d(n+1) = 1 - d(g(n))]

   In fact these deltas are always 0 or 1.
*)

Definition d n := g (S n) - g n.

Lemma delta_0_1 n : d n = 0 \/ d n = 1.
Proof.
 unfold d. destruct (g_step n); lia.
Qed.

Lemma delta_a n : d n = 0 -> d (S n) = 1.
Proof.
 unfold d in *.
 generalize (g_nonflat n) (g_mono_S n). lia.
Qed.

Lemma delta_b n :
 d n = 1 -> d (S n) + d (g n) = 1.
Proof.
 intros Hn.
 assert (Hgn := delta_0_1 (g n)).
 unfold d in *.
 assert (LE := g_mono_S (S n)).
 assert (LE' := g_mono_S (g n)).
 cut (g (S (S n)) + g (S (g n)) = S (g (S n) + g (g n))); [lia|].
 replace (S (g n)) with (g (S n)) by lia.
 now rewrite !g_eqn.
Qed.

(** A short formula giving delta:
    This could be used to define [g]. *)

Lemma delta_eqn n :
 d (S n) = 1 - d n * d (g n).
Proof.
 destruct (delta_0_1 n) as [E|E]; rewrite E.
 - simpl. now apply delta_a.
 - rewrite Nat.mul_1_l. rewrite <- (delta_b n); lia.
Qed.

Lemma g_alt_def n :
 g (S (S n)) = S (g (S n)) - (g (S n) - g n) * (g (S (g n)) - g (g n)).
Proof.
 change (g (S (S n)) = S (g (S n)) - d n * d (g n)).
 assert (0 <= d n * d (g n) <= 1).
 { generalize (delta_0_1 n)(delta_0_1 (g n)).
   intros [-> | ->] [-> | ->]; simpl; auto. }
 generalize (delta_eqn n). unfold d at 1.
 generalize (g_mono_S (S n)). lia.
Qed.

(** [GD] is a relational presentation of [G] via these "delta" equations. *)

Inductive GD : nat -> nat -> Prop :=
 | GD_0 : GD 0 0
 | GD_1 : GD 1 1
 | GD_a n x : GD n x -> GD (S n) x -> GD (2+n) (S x)
 | GD_b n x y z : GD n x -> GD (S n) y -> x <> y ->
                  GD x z -> GD (S x) z -> GD (2+n) (S y)
 | GD_b' n x y z t : GD n x -> GD (S n) y -> x <> y ->
                     GD x z -> GD (S x) t -> z <> t -> GD (2+n) y.
Hint Constructors GD.

(** There is only one implementation of [GD] *)

(* begin hide *)
Ltac uniq :=
match goal with
| U:forall k, GD ?x k -> _, V:GD ?x ?y |- _ =>
   apply U in V; try subst y; uniq
| U:?x<>?x |- _ => now elim U
end.
(* end hide *)

Lemma GD_unique n k k' : GD n k -> GD n k' -> k = k'.
Proof.
intros H1.
revert k'.
induction H1; inversion 1; subst; auto; try lia; uniq.
Qed.

(** [g] is an implementation of [GD] (hence the only one). *)

Lemma g_implements_GD n : GD n (g n).
Proof.
induction n as [n IH] using lt_wf_rec.
destruct n as [|[|n]].
- auto.
- auto.
- assert (GD n (g n)) by (apply IH; lia).
  assert (GD (S n) (g (S n))) by (apply IH; lia).
  set (x := g n) in *.
  destruct (eq_nat_dec x (g (S n))) as [E|N].
  + rewrite (g_nonflat n) by auto. rewrite <-E in *.
    constructor; auto.
  + assert (GD x (g x)).
    { apply IH. unfold x. generalize (g_le n); lia. }
    assert (GD (S x) (g (S x))).
    { apply IH. unfold x. generalize (g_le n); lia. }
    assert (D : g (S n) - g n = 1).
    { generalize (delta_0_1 n) (g_mono_S n); unfold d, x in *.
      lia. }
    assert (D' := delta_b n D). unfold d in D'.
    destruct (eq_nat_dec (g x) (g (S x))).
    * replace (g (S (S n))) with (S (g (S n)))
       by (unfold x in *; lia).
      eapply GD_b; eauto. congruence.
    * assert (g (S x) - g x = 1).
      { generalize (delta_0_1 x) (g_mono_S x); unfold d; lia. }
      replace (g (S (S n))) with (g (S n))
       by (generalize (g_mono_S (S n)); unfold x in *; lia).
      eapply GD_b'; eauto.
Qed.

(*==============================================================*)

(** * Study of [g (n+m) - g n - g m] *)

(** Base cases *)

Lemma g_add_1 n :  g n <= g (1+n) <= 1 + g n.
Proof.
 generalize (g_step n). simpl. lia.
Qed.

Lemma g_add_2 n : 1 + g n <= g (2+n) <= 2 + g n.
Proof.
 split.
 - destruct (g_step n).
   + generalize (g_nonflat n). simpl in *. lia.
   + simpl in *. rewrite <- H. apply g_mono. lia.
 - apply g_le_add.
Qed.

(** Auxiliary stuff for g_add_approx *)

Fixpoint insert x l :=
 match l with
 | [] => [x]
 | y::l' => if x <=? y then x::l else y::insert x l'
 end.

Lemma sumfib_insert x l :
 sumfib (insert x l) = fib x + sumfib l.
Proof.
 induction l; simpl; auto.
 destruct (x <=? a); simpl; rewrite ?IHl; lia.
Qed.

Lemma map_pred_insert x l :
  ~In 0 l ->
  map Nat.pred (insert x l) = insert (Nat.pred x) (map Nat.pred l).
Proof.
 induction l; simpl; auto.
 do 2 case Nat.leb_spec; intros; try lia; simpl; auto.
 f_equal. auto.
Qed.

Lemma map_pred_insert' x l :
  Delta 1 (0::l) ->
  map Nat.pred (insert x l) = insert (Nat.pred x) (map Nat.pred l).
Proof.
 intros D. apply map_pred_insert. eapply Delta_nz'; eauto.
Qed.

Lemma insert_delta x l a :
 Delta 2 (Nat.pred a::l) -> ~In x l -> a < x -> Delta 1 (a::insert x l).
Proof.
 revert a.
 induction l as [|b l IH]; simpl.
 - constructor. lia. constructor.
 - intro a. case Nat.leb_spec; intro.
   + inversion 1; subst. intros.
     constructor. lia. constructor. lia. auto.
   + inversion 1; subst. intros.
     constructor. lia. apply IH; auto.
     apply Delta_low_hd with b. lia. auto.
Qed.

Lemma sub_succ n m :
 S m <= n -> S (n - S m) = n - m.
Proof.
 intros. rewrite <- Nat.sub_succ_l; auto.
Qed.

Ltac simpl_sub :=
  rewrite ?sub_succ, ?Nat.sub_0_r in * by lia.

Definition head_or_0 l := match l with x::_ => x | [] => 0 end.

Definition rank n := head_or_0 (decomp n).

Lemma rank_sumfib l :
  Delta 1 (1::l) -> rank (sumfib l) mod 2 = (head_or_0 l) mod 2.
Proof.
 unfold rank. intros D.
 replace (decomp (sumfib l)) with (norm l).
 2:{ symmetry. apply decomp_spec. apply norm_sum. now apply norm_ok'. }
 assert (HL := norm_hd l).
 destruct (norm l), l; auto. destruct HL. destruct HL.
 destruct HL as (q,->).
 rewrite Nat.mul_comm.
 simpl head_or_0.
 rewrite Nat.mod_add; auto.
Qed.

Lemma rank_fib k : 1<k -> rank (fib k) mod 2 = k mod 2.
Proof.
 intros Hk.
 replace (fib k) with (sumfib [k]) by (simpl; auto).
 apply rank_sumfib; auto.
Qed.

(** General result about [g(n+)-g(n)-g(p)].
    The current proof is rather convoluted.
*)

Lemma g_add_approx n p :
  g n + g p - 1 + (rank p) mod 2 <= g (n+p) <= g n + g p + (rank p) mod 2.
Proof.
revert n.
induction p as [p IH] using lt_wf_ind.
intros n.
unfold rank, decomp.
destruct (decomp_exists p) as (dp & E & D). simpl proj1_sig.
destruct dp as [|a pl].
- simpl in E. subst p. rewrite !Nat.add_0_r. lia.
- simpl head_or_0.
  apply Delta_inv2 in D. destruct D as (Ha,D). simpl in Ha.
  destruct pl as [|b pl].
  + (* [a] *)
    clear D.
    apply Nat.lt_eq_cases in Ha. apply or_comm in Ha. destruct Ha as [<-|Ha].
    { (* a = 2 *)
      clear IH. subst. simpl. rewrite (Nat.add_comm n).
      generalize (g_add_1 n). change (g 1) with 1. lia. }
    apply Nat.lt_eq_cases in Ha. apply or_comm in Ha. destruct Ha as [<-|Ha].
    { (* a = 3 *)
      clear IH. subst. simpl. rewrite (Nat.add_comm n).
      generalize (g_add_2 n). change (g 2) with 1. lia. }
    { (* 3 < a *)
      destruct (decomp_exists n) as (nl & En & Dn).
      destruct (In_dec Nat.eq_dec a nl) as [INa|NIa].
      - assert (NIb' : ~In (a-1) nl).
        { intro. apply (@Delta2_apart nl (a-1)); auto.
          inversion_clear Dn; auto. simpl_sub; auto. }
        set (nl' := insert (a-1) nl).
        assert (LT : fib (a-2) < p).
        { subst p. simpl. rewrite Nat.add_0_r. apply fib_lt; lia. }
        specialize (IH _ LT (sumfib nl')).
        replace (sumfib nl' + fib (a-2)) with (n + p) in IH.
        2:{ unfold nl'. rewrite sumfib_insert.
            subst n. subst p. simpl.
            generalize (fib_eqn (a-2)). simpl_sub. lia. }
        rewrite rank_fib in IH by lia.
        replace a with (a-2+1*2) by lia. rewrite Nat.mod_add; auto.
        assert (g (sumfib nl') + g(fib (a-2)) = g n + g p); [|lia].
        { clear IH.
          subst p. subst n. simpl. rewrite Nat.add_0_r.
          rewrite !g_fib' by lia.
          unfold nl'. rewrite !g_sumfib'; auto.
          - rewrite map_pred_insert', sumfib_insert; auto.
            rewrite <- !Nat.sub_1_r, <- !Nat.sub_add_distr. simpl.
            generalize (fib_eqn (a-3)). simpl_sub. lia.
          - apply insert_delta; auto. lia. }
      - (* NIa : ~In a nl *)
        clear IH.
        subst p. simpl sumfib. rewrite Nat.add_0_r.
        rewrite g_fib' by lia.
        assert (0 < fib (a-1)). { apply fib_nz. lia. }
        assert (a mod 2 < 2). { now apply Nat.mod_upper_bound. }
        assert (g (n + fib a) = g n + fib (a-1)); [|lia].
        { rewrite <- En. rewrite Nat.add_comm. rewrite <- sumfib_insert.
          rewrite !g_sumfib'; auto.
          - rewrite map_pred_insert', sumfib_insert; auto. simpl.
            rewrite Nat.sub_1_r. lia.
          - apply insert_delta; auto. lia. }
    }
  + set (pl' := b::pl) in *.
    apply Delta_inv2 in D. destruct D as (Hb,D).
    destruct (Nat.lt_ge_cases (a+2) b) as [Hb'|Hb'].
    * { (* a+2 < b *)
        destruct (decomp_exists n) as (nl & En & Dn).
        destruct (In_dec Nat.eq_dec b nl) as [INb|NIb].
        - assert (NIb' : ~In (b-1) nl).
          { intro. apply (@Delta2_apart nl (b-1)); auto.
            inversion_clear Dn; auto. simpl_sub; auto. }
          set (nl' := insert (b-1) nl).
          set (pl2 := a::b-2::pl).
          assert (LT : sumfib pl2 < p).
          { subst p. simpl. generalize (@fib_lt (b-2) b). lia. }
          specialize (IH _ LT (sumfib nl')).
          replace (sumfib nl' + sumfib pl2) with (n + p) in IH.
          2:{ unfold pl2, nl'. rewrite sumfib_insert.
              subst n. subst p. unfold pl'. simpl.
              generalize (fib_eqn (b-2)). simpl_sub. lia. }
          rewrite rank_sumfib in IH.
          2:{ unfold pl2. constructor. auto. constructor. lia.
              apply Delta_S. apply Delta_low_hd with b; auto. lia. }
          simpl head_or_0 in IH.
          assert (g (sumfib nl') + g (sumfib pl2) = g n + g p); [|lia].
          { clear IH.
            unfold pl2. subst p. subst n. unfold pl'.
            unfold nl'. rewrite !g_sumfib'; auto.
            - rewrite map_pred_insert', sumfib_insert; auto. simpl.
              rewrite <- !Nat.sub_1_r, <- !Nat.sub_add_distr. simpl.
              generalize (fib_eqn (b-3)). simpl_sub. lia.
            - constructor; auto. constructor. lia.
              apply Delta_S. apply Delta_low_hd with b; auto. lia.
            - apply insert_delta; auto. lia. }
        - (* NIb : ~In b dn *)
          set (nl' := insert b nl).
          set (pl2 := a::pl).
          assert (LT : sumfib pl2 < p).
          { subst p. simpl. generalize (@fib_nz b). lia. }
          specialize (IH _ LT (sumfib nl')).
          replace (sumfib nl' + sumfib pl2) with (n + p) in IH.
          2:{ unfold nl'. rewrite sumfib_insert.
              subst n. subst p. simpl. lia. }
          rewrite rank_sumfib in IH.
          2:{ constructor. lia.
              apply Delta_low_hd with b; auto. lia. }
          simpl head_or_0 in IH.
          assert (g (sumfib nl') + g (sumfib pl2) = g n + g p); [|lia].
          { clear IH.
            unfold pl2. subst p. subst n. unfold pl', nl'.
            rewrite !g_sumfib'; auto.
            - rewrite map_pred_insert', sumfib_insert; auto. simpl. lia.
            - constructor; auto. apply Delta_low_hd with b; auto. lia.
            - apply insert_delta; auto. lia. }
      }
    * assert (Hb2 : b = a + 2) by lia. clear Hb Hb'. rename Hb2 into Hb.
      destruct (decomp_exists n) as (nl & En & Dn).
      destruct (Sumbool.sumbool_not _ _ (In_dec Nat.eq_dec a nl)) as [NIa|INa].
      { (* ~In a nl *)
         set (nl' := insert a nl).
         assert (LT : sumfib pl' < p).
         { subst p. simpl. generalize (@fib_nz a). lia. }
         specialize (IH _ LT (sumfib nl')).
         replace (sumfib nl' + sumfib pl') with (n + p) in IH.
         2:{ unfold nl'. rewrite sumfib_insert.
             subst n. subst p. simpl. lia. }
         rewrite rank_sumfib in IH.
         2:{ unfold pl'. constructor; auto. lia. }
         simpl head_or_0 in IH.
         subst b. change (a+2) with (a+1*2) in IH.
         rewrite Nat.mod_add in IH; auto.
         assert (g (sumfib nl') + g (sumfib pl') = g n + g p); [|lia].
         { clear IH.
           subst p. subst n. unfold pl', nl'. rewrite !g_sumfib'; auto.
           - rewrite map_pred_insert', sumfib_insert; auto. simpl. lia.
           - constructor; auto. lia.
           - apply insert_delta; auto. }
      }
     apply Nat.lt_eq_cases in Ha. destruct Ha as [Ha|<-].
     apply Nat.lt_eq_cases in Ha. destruct Ha as [Ha|<-].
     { (* 3 < a *)
       set (nl' := insert (a-1) nl).
       set (pl2 := a-2::pl').
       assert (LT : sumfib pl2 < p).
       { subst p. unfold pl2. simpl. generalize (@fib_lt (a-2) a). lia. }
       specialize (IH _ LT (sumfib nl')).
       replace (sumfib nl' + sumfib pl2) with (n + p) in IH.
       2:{ unfold nl'. rewrite sumfib_insert.
           subst n. subst p. simpl.
           generalize (fib_eqn (a-2)). simpl_sub. lia. }
       rewrite rank_sumfib in IH.
       2:{ unfold pl2. constructor. lia.
           unfold pl'. constructor; auto. lia. }
       simpl head_or_0 in IH.
       replace a with (a-2+1*2) by lia. rewrite Nat.mod_add; auto.
       assert (g (sumfib nl') + g (sumfib pl2) = g n + g p); [|lia].
       { clear IH.
         subst p. subst n. unfold nl'. rewrite !g_sumfib'; auto.
         - rewrite map_pred_insert', sumfib_insert; auto. simpl.
           rewrite <- !Nat.sub_1_r, <- !Nat.sub_add_distr. simpl.
           generalize (fib_eqn (a-3)). simpl_sub. lia.
         - constructor; auto. lia. constructor; auto. lia.
         - constructor; auto. lia. constructor; auto. lia.
         - apply insert_delta; auto. 2:lia.
           intro. apply (@Delta2_apart nl (a-1)); auto.
           inversion_clear Dn; auto. simpl_sub. auto. }
     }
     { (* a = 3 *)
       assert (LT : sumfib (2::pl') < p).
       { subst p. simpl. lia. }
       specialize (IH _ LT (1+n)).
       replace (1+n + sumfib (2::pl')) with (n + p) in IH.
       2:{ subst p. simpl. lia. }
       rewrite rank_sumfib in IH.
       2:{ constructor. lia. constructor; auto. lia. }
       simpl Nat.modulo in *.
       assert (0 < g p).
       { apply g_nonzero. subst p. simpl. lia. }
       assert (g (1+n) + g (sumfib (2::pl')) = g n + g p + 1); try lia.
       { clear IH.
         subst p. subst n.
         change (1+sumfib nl) with (sumfib (2::nl)).
         rewrite !g_sumfib'; auto.
         - simpl. lia.
         - constructor; auto. constructor; auto. lia.
         - constructor; auto. constructor; auto. lia.
         - constructor; auto.
           destruct nl as [|c nl].
           + inversion INa.
           + apply Delta_inv2 in Dn. destruct Dn as (Hc,Dn).
             replace c with 3 in *; auto.
             simpl in INa. destruct INa as [INa|INa]; auto.
             apply Delta_alt in Dn. destruct Dn as (_,Dn).
             specialize (Dn _ INa). lia. }
     }
     { (* a = 2 *)
       simpl in Hb. subst b.
       assert (LT : sumfib (3::pl) < p).
       { subst p. simpl. lia. }
       specialize (IH _ LT (2+n)).
       replace (2+n + sumfib (3::pl)) with (n + p) in IH.
       2:{ subst p. simpl. lia. }
       rewrite rank_sumfib in IH.
       2:{ constructor; auto.
           apply Delta_S. apply Delta_low_hd with 4; auto. }
       simpl Nat.modulo in *.
       assert (0 < g (2+n)). { apply g_nonzero. lia. }
       assert (g (2+n) + g (sumfib (3::pl)) + 1 = g n + g p); [|lia].
       { clear IH.
         subst p. subst n.
         destruct nl as [|c nl].
         - inversion INa.
         - apply Delta_inv2 in Dn. destruct Dn as (Hc,Dn).
           replace c with 2 in *.
           2:{
             simpl in INa. destruct INa as [INa|INa]; auto.
             apply Delta_alt in Dn. destruct Dn as (_,Dn).
             specialize (Dn _ INa). lia. }
           change (2+sumfib (2::nl)) with (sumfib (2::3::nl)).
           rewrite !g_sumfib'; auto.
           + simpl. lia.
           + constructor; auto. constructor; auto.
           + constructor; auto. apply Delta_low_hd with 4; auto. }
     }
Qed.

(* Some special cases of g_add_approx *)

Lemma g_add_bound n p :
 g n + g p -1 <= g (n+p) <= g n + g p + 1.
Proof.
 assert (H := g_add_approx n p).
 generalize (Nat.mod_upper_bound (rank p) 2).
 lia.
Qed.

Lemma g_add_fib n k :
  fib k + g n - k mod 2 <= g (fib (S k) + n) <= fib k + g n + 1 - k mod 2.
Proof.
 generalize (g_add_approx n (fib (S k))).
 destruct (Nat.eq_dec k 0).
 - subst k. simpl. change (g 1) with 1.
   rewrite (Nat.add_1_r n). lia.
 - rewrite g_fib; auto. rewrite rank_fib by lia.
   assert (S k mod 2 + k mod 2 = 1).
   { rewrite <- !Nat.bit0_mod. simpl.
     rewrite Nat.odd_succ, <- Nat.negb_even. now destruct Nat.even. }
   rewrite (Nat.add_comm n). lia.
Qed.

Lemma g_add_neqparities n p :
 rank n mod 2 <> rank p mod 2 -> g (n+p) = g n + g p.
Proof.
 intros NE.
 assert (H := g_add_approx n p).
 assert (H' := g_add_approx p n).
 rewrite (Nat.add_comm p n) in H'.
 generalize (Nat.mod_upper_bound (rank n) 2).
 generalize (Nat.mod_upper_bound (rank p) 2).
 lia.
Qed.


Lemma g_add_3 n : 1 + g n <= g (3+n) <= 2 + g n.
Proof.
 generalize (g_add_fib n 3). simpl. now rewrite Nat.add_1_r.
Qed.

Lemma g_add_4 n : 2 + g n <= g (4+n) <= 3 + g n.
Proof.
 generalize (g_add_approx n 4). simpl. change (g 4) with 3.
 rewrite (Nat.add_comm n). simpl. lia.
Qed.

Lemma g_add_5 n : 3 + g n <= g (5+n) <= 4 + g n.
Proof.
 generalize (g_add_fib n 4). simpl. now rewrite Nat.add_1_r.
Qed.

Lemma g_add_6 n : 3 + g n <= g (6+n) <= 4 + g n.
Proof.
 generalize (g_add_approx n 6). simpl. change (g 6) with 4.
 rewrite (Nat.add_comm n). simpl. lia.
Qed.

Lemma g_add_7 n : 4 + g n <= g (7+n) <= 5 + g n.
Proof.
 generalize (g_add_approx n 7). simpl. change (g 7) with 4.
 rewrite (Nat.add_comm n). simpl. lia.
Qed.

Lemma g_add_8 n : 4 + g n <= g (8+n) <= 5 + g n.
Proof.
 generalize (g_add_fib n 5). simpl. now rewrite Nat.add_1_r.
Qed.
