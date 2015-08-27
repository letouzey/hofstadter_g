(** * FibTree : Hofstadter's G function and tree *)

Require Import Arith Omega Wf_nat List NPeano.
Require Import DeltaList Fib.
Set Implicit Arguments.

(** Study of the functional equation:
     - [G (S n) + G (G n) = S n]
     - [G 0 = 0]

    and its relationship with the Fibonacci sequence.

    Source: Hofstadter's book: Goedel, Escher, Bach.
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
destruct n; inversion_clear 1; omega.
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
  omega.
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
  eapply GS; eauto; omega.
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
rewrite (G_fun Hc Hc') in *. omega.
Qed.

(** Same, with subtraction *)

Lemma g_S n : g (S n) = S n - g (g n).
Proof.
 generalize (g_eqn n); omega.
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
  generalize (g_eqn n). omega.
Qed.

Lemma g_step n : g (S n) = g n \/ g (S n) = S (g n).
Proof.
induction n as [|n IH IH'] using G_rec.
- compute; auto.
- rewrite (g_S n), (g_S (S n)).
  destruct IH as [-> | ->]; [omega|].
  destruct (IH' (g n)) as [-> | ->]; auto; omega.
Qed.

Lemma g_mono_S n : g n <= g (S n).
Proof.
 generalize (g_step n). omega.
Qed.

Lemma g_mono n m : n <= m -> g n <= g m.
Proof.
induction 1.
- trivial.
- transitivity (g m); auto using g_mono_S.
Qed.

(** NB : in Coq, for natural numbers, 3-5 = 0 (truncated subtraction) *)

Lemma g_lipschitz n m : g m - g n <= m - n.
Proof.
destruct (le_ge_dec n m) as [H|H].
- induction H; try generalize (g_step m); omega.
- generalize (g_mono H). omega.
Qed.

Lemma g_nonzero n : 0 < n -> 0 < g n.
Proof.
 unfold lt. intros. change 1 with (g 1). now apply g_mono.
Qed.

Lemma g_0_inv n : g n = 0 -> n = 0.
Proof.
destruct n; trivial.
assert (0 < g (S n)) by (apply g_nonzero; auto with arith).
omega.
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
  assert (H' : g (g n) = 0) by omega.
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
rewrite g_fix in *. omega.
Qed.
Hint Resolve g_lt.

(** Two special formulations for [g_step] *)

Lemma g_next n a : g n = a -> (g (S n) <> a <-> g (S n) = S a).
Proof.
 generalize (g_step n). omega.
Qed.

Lemma g_prev n a : n <> 0 -> g n = a ->
 (g (n-1) <> a <-> g (n-1) = a - 1).
Proof.
 intros H Ha.
 assert (Ha' := g_nz H).
 generalize (g_step (n-1)). replace (S (n-1)) with n by omega.
 omega.
Qed.

(** [g] cannot stay flat very long *)

Lemma g_nonflat n : g (S n) = g n -> g (S (S n)) = S (g n).
Proof.
 intros H. generalize (g_eqn (S n)) (g_eqn n). rewrite H. omega.
Qed.

Lemma g_nonflat' n : g (S n) = g n -> g (n-1) = g n - 1.
Proof.
 destruct n.
 - now compute.
 - replace (S n - 1) with n by omega.
   intros H.
   destruct (g_step n) as [H'|H'].
   + apply g_nonflat in H'. omega.
   + omega.
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
  omega.
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
  destruct (g_step n); [ | exists (S n); omega].
  destruct (g_step (S n)); [ | exists (S (S n)); omega].
  exfalso.
  generalize (@g_max_two_antecedents a n (S (S n))). omega.
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
     generalize (@g_max_two_antecedents a (n-1) (S n)). omega.
   + exists n; exists (S n); repeat split; auto.
     intros k Hk.
     destruct (g_inv n k) as [H|[H|H]]; try omega.
     subst n. simpl in *. rewrite Nat.sub_0_r in *. omega.
   + exists n; exists (n-1); repeat split; auto; try omega.
     intros k Hk.
     destruct (g_inv n k) as [H|[H|H]]; try omega.
     subst k. omega.
   + elim U.
     intros u v Hu Hv.
     assert (u = n).
     { destruct (g_inv n u) as [H|[H|H]]; subst;
       simpl in *; rewrite ?Nat.sub_0_r in *; omega. }
     assert (v = n).
     { destruct (g_inv n v) as [H'|[H'|H']]; subst;
       simpl in *; rewrite ?Nat.sub_0_r in *; omega. }
     omega.
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
 unfold rchild; omega.
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

Lemma g_fib n : g (fib (S n)) = fib n.
Proof.
induction n.
- reflexivity.
- rewrite fib_eqn.
  rewrite <- IHn.
  apply g_onto_eqn.
Qed.

Lemma g_Sfib n : n <> 0 -> g (S (fib (S n))) = S (fib n).
Proof.
 destruct n.
 - now destruct 1.
 - intros _.
   rewrite <- (g_fib (S n)).
   apply rightmost_child_carac; trivial.
   unfold rchild.
   now rewrite !g_fib.
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
    generalize (@g_max_two_antecedents a n (S (S n))). omega.
  + rewrite rightmost_child_carac in H'; trivial.
    rewrite H, Hn in H'. unfold lchild, rchild in *; omega.
- rewrite <- (@rightmost_child_carac a n); omega.
Qed.

Lemma g_lchild a :
 g (lchild a) = a - 1 \/ g (lchild a) = a.
Proof.
 destruct (le_gt_dec a 0).
  + replace a with 0 by omega. compute. auto.
  + assert (0 < rchild a) by (unfold rchild; generalize (@g_nonzero a); omega).
    destruct (g_step (lchild a)) as [H'|H'];
    replace (S (lchild a)) with (rchild a) in * by
      (unfold lchild, rchild in *; omega);
    rewrite g_onto_eqn in *; omega.
Qed.

Lemma unary_carac1 a :
 Unary g a <-> forall n, g n = a -> n = rchild a.
Proof.
split; intros H.
- intros n Hn. apply H; trivial. apply g_onto_eqn.
- intros n m Hn Hm. apply H in Hn. apply H in Hm. omega.
Qed.

Lemma unary_carac2 a :
 Unary g a <-> g (lchild a) = a - 1.
Proof.
rewrite unary_carac1.
split; intros H.
- destruct (g_lchild a); trivial.
  assert (lchild a = rchild a) by (apply H; omega).
  unfold rchild, lchild in *; omega.
- intros n Hn.
  destruct (g_children _ Hn) as [H'|H']; trivial.
  rewrite <- H' in H.
  replace a with 0 in * by omega. exact H'.
Qed.

Lemma binary_carac1 a :
 Multary g a <-> a <> 0 /\ forall n, (g n = a <-> n = rchild a \/ n = lchild a).
Proof.
unfold Multary; rewrite unary_carac2.
split.
- intros H.
  assert (a<>0). { contradict H; now subst. }
  split; trivial.
  destruct (g_lchild a) as [H'|H']; [intros; omega|].
  clear H.
  split.
  + apply g_children.
  + destruct 1; subst n. apply g_onto_eqn. auto.
- intros (Ha,H) H'.
  assert (g (lchild a) = a). { apply H; now right. }
  omega.
Qed.

Lemma binary_carac2 a :
 Multary g a <-> (a <> 0 /\ g (lchild a) = a).
Proof.
unfold Multary; rewrite unary_carac2.
split.
- intros H.
  assert (a<>0). { contradict H; now subst. }
  split; trivial.
  destruct (g_lchild a); omega.
- omega.
Qed.

Lemma unary_or_multary n : Unary g n \/ Multary g n.
Proof.
 destruct (eq_nat_dec n 0).
 - left. subst. apply unary_carac2. reflexivity.
 - destruct (eq_nat_dec (g (lchild n)) n).
   + right. apply binary_carac2; auto.
   + left. apply unary_carac2. apply g_prev; auto. omega.
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
 assert (q<>0) by (unfold q, rchild; omega).
 clearbody q.
 assert (Eq := g_eqn (q-1)).
 replace (S (q-1)) with q in Eq by omega.
 assert (Eq' := g_eqn q).
 rewrite Hq1,Hp' in Eq.
 rewrite Hq,Hp in Eq'.
 assert (Hq' : g (S q) = p) by omega.
 intro U. specialize (U q (S q) Hq Hq'). omega.
Qed.

Lemma unary_rchild_is_binary n : n <> 0 ->
  Unary g n -> Multary g (rchild n).
Proof.
 intros H U. apply (@leftmost_son_is_binary n).
 - apply g_onto_eqn.
 - rewrite unary_carac2 in U. unfold lchild, rchild in *; omega.
Qed.

Lemma binary_lchild_is_binary n :
  Multary g n -> Multary g (lchild n).
Proof.
 rewrite binary_carac2. intros (B0,B1).
 apply (@leftmost_son_is_binary n); trivial.
 intros Eq.
 generalize (@g_max_two_antecedents n _ _ Eq (g_onto_eqn n)).
 assert (H := g_nz B0).
 unfold lchild, rchild in *. omega.
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
 replace (rchild n) with (S p) by (unfold p, rchild, lchild; omega).
 replace (S p + n -1) with (p + n) by omega.
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
     replace (S (n - 1)) with n by omega.
     * generalize (@g_max_two_antecedents (g n) (n-1) (S n)). omega.
     * intros. replace (g n - 1) with (g (n-1)) by omega. omega.
   + (* n is rightmost child *)
     generalize (g_eqn n). rewrite H. simpl. rewrite <- minus_n_O.
     omega.
Qed.


(*==============================================================*)

(** * Depth in the [G] tree *)

(** The depth of a node in the [G] tree is the number of
    iteration of [g] needed before reaching node 1 *)

Notation "f ^^ n" := (nat_iter n f) (at level 30, right associativity).

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
 apply g_lt. omega.
Qed.

(* Compute depth 13. *)

Lemma depth_SS n : depth (S (S n)) = S (depth (g (S (S n)))).
Proof.
 now WfExtensionality.unfold_sub depth (depth (S (S n))).
Qed.

Lemma depth_eqn n : 1<n -> depth n = S (depth (g n)).
Proof.
 destruct n as [|[|n]].
 - omega.
 - omega.
 - intros _. apply depth_SS.
Qed.

Lemma g_depth n : depth (g n) = depth n - 1.
Proof.
 destruct (le_lt_dec n 1) as [LE|LT].
 - assert (H : n=0 \/ n=1) by omega.
   destruct H as [-> | ->]; reflexivity.
 - rewrite (depth_eqn LT). omega.
Qed.

Lemma depth_correct n : n <> 0 -> (g^^(depth n)) n = 1.
Proof.
 induction n as [[|[|n]] IH] using lt_wf_rec.
 - omega.
 - reflexivity.
 - intros _. rewrite depth_SS.
   set (n' := S (S n)) in *. rewrite iter_S. apply IH.
   + apply g_lt. unfold n'; omega.
   + apply g_nz. unfold n'; omega.
Qed.

Lemma depth_minimal n : 1<n -> 1 < ((g^^(depth n - 1)) n).
Proof.
 induction n as [[|[|n]] IH] using lt_wf_rec.
 - omega.
 - omega.
 - intros _. rewrite depth_SS.
   simpl. rewrite <- minus_n_O.
   set (n' := S (S n)) in *.
   destruct (eq_nat_dec (g n') 1) as [->|NE].
   + simpl. unfold n'; omega.
   + assert (H : g n' <> 0) by (apply g_nz; unfold n'; omega).
     assert (depth (g n') <> 0).
     { intro EQ. generalize (depth_correct H). now rewrite EQ. }
     replace (depth (g n')) with (S (depth (g n') - 1)) by omega.
     rewrite iter_S.
     apply IH.
     * apply g_lt. unfold n'; omega.
     * omega.
Qed.

Lemma depth_mono n m : n <= m -> depth n <= depth m.
Proof.
 revert m.
 induction n as [[|[|n]] IH] using lt_wf_rec; intros m H.
 - change (depth 0) with 0. auto with arith.
 - change (depth 1) with 0. auto with arith.
 - destruct m as [|[|m]]; try omega.
   rewrite 2 depth_SS.
   apply le_n_S.
   apply IH.
   + apply g_lt. omega.
   + now apply g_mono.
Qed.

Lemma depth_fib k : depth (fib k) = k-1.
Proof.
 induction k as [|[|k] IH].
 - reflexivity.
 - reflexivity.
 - rewrite depth_eqn.
   + rewrite g_fib, IH. omega.
   + unfold lt. change 2 with (fib 2). apply fib_mono. omega.
Qed.

Lemma depth_Sfib k : k <> 0 -> depth (S (fib k)) = k.
Proof.
 induction k as [|[|k] IH].
 - now destruct 1.
 - reflexivity.
 - intros _.
   rewrite depth_eqn.
   + rewrite g_Sfib, IH; omega.
   + unfold lt. apply le_n_S. apply fib_nz.
Qed.

Lemma depth_0 n : depth n = 0 <-> n <= 1.
Proof.
 destruct n as [|[|n]].
 - compute; auto with arith.
 - compute; auto with arith.
 - rewrite depth_SS. omega.
Qed.

Lemma depth_carac k n : k <> 0 ->
  (depth n = k <-> S (fib k) <= n <= fib (S k)).
Proof.
 intros Hk.
 split; intros H.
 - split.
   + destruct (le_lt_dec n (fib k)) as [LE|LT]; trivial.
     apply depth_mono in LE. rewrite depth_fib in LE. omega.
   + destruct (le_lt_dec n (fib (S k))) as [LE|LT]; trivial.
     unfold lt in LT. apply depth_mono in LT.
     rewrite depth_Sfib in LT; omega.
 - destruct H as (H1,H2).
   apply depth_mono in H1. apply depth_mono in H2.
   rewrite depth_fib in H2; rewrite depth_Sfib in H1; omega.
Qed.

(** Conclusion:
   - [(fib k)+1] is the leftmost node at depth [k]
   - [fib (k+1)] is the rightmost node at depth [k]
   - hence we have [fib (k+1) - fib k = fib (k-1)] nodes at depth [k].
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
 intros a Ha. assert (a<>0) by congruence. omega.
Qed.

(** * [g] and Fibonacci decomposition.

   We now prove that g is simply "shifting" the Fibonacci
   decomposition of a number, i.e. removing 1 at all the ranks
   in this decomposition.

   For proving this result, we need to consider relaxed
   decompositions where consecutive fibonacci terms may occur
   (but still no (fib 0)). These decompositions aren't unique.
   We also consider these decomposition in the lowest terms first,
   simply for technical reasons.
*)

Lemma g_sumfib l :
  Delta 1 l -> g (sumfib (List.map S l)) = sumfib l.
Proof.
 remember (sumfib (List.map S l)) as n eqn:E.
 revert l E.
 induction n  as [[|n] IH] using lt_wf_rec; intros [|k l].
 - trivial.
 - simpl map. rewrite sumfib_cons.
   generalize (fib_nz (S k)). intros. omega.
 - discriminate.
 - simpl map. rewrite sumfib_cons.
   intros E Hl.
   rewrite g_S.
   case (eq_nat_dec k 0) as [Hk|Hk].
   + (* k = 0 *)
     subst k. simpl sumfib. injection E as E'.
     assert (Nz : ~In 0 l).
     { intro H0. apply Delta_alt in Hl. apply Hl in H0. omega. }
     assert (E1 : g n = sumfib l).
     { apply IH; auto. inversion Hl; auto; constructor. }
     assert (E2 : g (g n) = sumfib (map pred l)).
     { apply IH; auto.
       - generalize (g_le n); omega.
       - now rewrite map_S_pred.
       - apply Delta_pred; eauto. }
     rewrite E' at 1. rewrite <- sumfib_eqn; trivial.
     rewrite <- E2, <- E1. omega.
   + (* k <> 0 *)
     destruct (Nat.Even_or_Odd k) as [(k2,Hk2)|(k2,Hk2)].
     * (* k even *)
       set (l0 := odds k2).
       assert (Hl0 : sumfib l0 = pred (fib k)).
       { rewrite Hk2. unfold l0. apply sumfib_odds. }
       assert (Hl0' : S (sumfib (map S l0)) = fib (S k)).
       { unfold l0. rewrite S_odds, sumfib_evens.
         rewrite Nat.add_1_r, <- Hk2.
         generalize (fib_nz (S k)); omega. }
       assert (Delta 1 (l0++l)).
       { apply Delta_app with k; auto; unfold l0.
         - apply Delta_21, Delta_odds.
         - intros y Hy. apply odds_in in Hy. omega. }
       assert (~In 0 (l0++l)).
       { rewrite in_app_iff. intros [H0|H0].
         - unfold l0, odds in H0.
           rewrite in_map_iff in H0. destruct H0 as (x,(Hx,_)).
           omega.
         - apply Delta_alt in Hl. apply Hl in H0. omega. }
       assert (G : g n = sumfib (l0 ++ l)).
       { apply IH; auto.
         rewrite map_app, sumfib_app. omega. }
       assert (GG : g (g n) = sumfib (map pred (l0++l))).
       { apply IH.
         - generalize (g_le n); omega.
         - now rewrite map_S_pred.
         - apply Delta_pred; auto. }
       simpl sumfib.
       rewrite GG, E, <- Hl0'.
       simpl plus.
       rewrite <- sumfib_app, <- map_app.
       transitivity (S (sumfib (l0++l))).
       rewrite <- sumfib_eqn; auto; omega.
       rewrite sumfib_app. generalize (fib_nz k); omega.
     * (* k odd *)
       set (l0 := evens k2).
       assert (Hl0 : sumfib l0 = pred (fib k)).
       { rewrite Hk2. unfold l0. apply sumfib_evens. }
       assert (Hl0' : sumfib (map S l0) + 2 = fib (S k)).
       { unfold l0.
         rewrite Nat.add_succ_r.
         change (sumfib (1 :: map S (evens k2)) + 1 = fib (S k)).
         rewrite <- odds_S, sumfib_odds.
         replace (2 * S k2) with (S k) by omega.
         generalize (fib_nz (S k)); omega. }
       assert (Delta 1 (l0++l)).
       { apply Delta_app with k; auto; unfold l0.
         - apply Delta_21, Delta_evens.
         - intros y Hy. apply evens_in in Hy. omega. }
       assert (IN : forall x, In x (l0++l) -> 1<x).
       { intros x. rewrite in_app_iff. intros [Hx|Hx].
         - unfold l0 in Hx. apply evens_in in Hx. omega.
         - apply Delta_alt in Hl. apply Hl in Hx. omega. }
       assert (~In 0 (l0++l)).
       { intro H0. apply IN in H0. omega. }
       assert (G : g n = sumfib (0 :: l0 ++ l)).
       { apply IH; auto.
         - simpl. rewrite map_app, sumfib_app. omega.
         - apply Delta_alt. split; auto.
           intros y Hy. apply IN in Hy. omega. }
       assert (GG : g (g n) = sumfib (map pred (0 :: l0++l))).
       { apply IH.
         - generalize (g_le n); omega.
         - rewrite G. simpl. f_equal. now rewrite map_S_pred.
         - simpl. apply Delta_alt. split.
           + now apply Delta_pred.
           + intros y Hy.
             rewrite in_map_iff in Hy. destruct Hy as (y0,(<-,Hy0)).
             generalize (IN y0 Hy0). omega. }
       simpl sumfib.
       rewrite GG, E, <- Hl0'. simpl.
       rewrite Nat.add_shuffle0, <- sumfib_app, <- map_app.
       transitivity (S (sumfib (l0++l))).
       rewrite <- sumfib_eqn; auto; omega.
       rewrite sumfib_app. generalize (fib_nz k); omega.
Qed.

Lemma g_sumfib' l : ~In 0 l -> Delta 1 l ->
 g (sumfib l) = sumfib (map pred l).
Proof.
 intros.
 rewrite <- (map_S_pred l) at 1; auto.
 apply g_sumfib. apply Delta_pred; auto.
Qed.

(** same result, for canonical decomposition expressed in rev order *)

Lemma g_sumfib_rev l : ~In 0 l -> DeltaRev 2 l ->
 g (sumfib l) = sumfib (map pred l).
Proof.
 intros.
 set (l' := map pred (rev l)).
 assert (Hl : l = map S (rev l')).
 { unfold l'. rewrite <- map_rev, rev_involutive.
   now rewrite map_S_pred. }
 rewrite Hl, !map_rev, !sumfib_rev.
 rewrite g_sumfib.
 - f_equal. rewrite map_map. simpl. symmetry. apply map_id.
 - apply Delta_21. unfold l'. apply Delta_pred.
   + now rewrite <- in_rev.
   + now apply Delta_rev.
Qed.

(** Beware! In the previous statement, [map pred l] might
    not be a canonical decomposition anymore, since 0 could appear.
    In this case, 0 could be turned into a 1 (since [fib 0 = fib 1]),
    and then we should saturate with Fibonacci equations
    ([fib 1 + fib 2 = fib 3], etc) to regain a canonical
    decomposition (with no consecutive fib terms), see [Fib.norm].*)


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
 unfold d. destruct (g_step n); omega.
Qed.

Lemma delta_a n : d n = 0 -> d (S n) = 1.
Proof.
 unfold d in *.
 generalize (g_nonflat n) (g_mono_S n). omega.
Qed.

Lemma delta_b n :
 d n = 1 -> d (S n) + d (g n) = 1.
Proof.
 intros Hn.
 assert (Hgn := delta_0_1 (g n)).
 unfold d in *.
 assert (LE := g_mono_S (S n)).
 assert (LE' := g_mono_S (g n)).
 cut (g (S (S n)) + g (S (g n)) = S (g (S n) + g (g n))); [omega|].
 replace (S (g n)) with (g (S n)) by omega.
 now rewrite !g_eqn.
Qed.

(** A short formula giving delta:
    This could be used to define [g]. *)

Lemma delta_eqn n :
 d (S n) = 1 - d n * d (g n).
Proof.
 destruct (delta_0_1 n) as [E|E]; rewrite E.
 - simpl. now apply delta_a.
 - rewrite Nat.mul_1_l. rewrite <- (delta_b n); omega.
Qed.

Lemma g_alt_def n :
 g (S (S n)) = S (g (S n)) - (g (S n) - g n) * (g (S (g n)) - g (g n)).
Proof.
 change (g (S (S n)) = S (g (S n)) - d n * d (g n)).
 assert (0 <= d n * d (g n) <= 1).
 { generalize (delta_0_1 n)(delta_0_1 (g n)).
   intros [-> | ->] [-> | ->]; simpl; auto. }
 generalize (delta_eqn n). unfold d at 1.
 generalize (g_mono_S (S n)). omega.
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
induction H1; inversion 1; subst; auto; try omega; uniq.
Qed.

(** [g] is an implementation of [GD] (hence the only one). *)

Lemma g_implements_GD n : GD n (g n).
Proof.
induction n as [n IH] using lt_wf_rec.
destruct n as [|[|n]].
- auto.
- auto.
- assert (GD n (g n)) by (apply IH; omega).
  assert (GD (S n) (g (S n))) by (apply IH; omega).
  set (x := g n) in *.
  destruct (eq_nat_dec x (g (S n))) as [E|N].
  + rewrite (g_nonflat n) by auto. rewrite <-E in *.
    constructor; auto.
  + assert (GD x (g x)).
    { apply IH. unfold x. generalize (g_le n); omega. }
    assert (GD (S x) (g (S x))).
    { apply IH. unfold x. generalize (g_le n); omega. }
    assert (D : g (S n) - g n = 1).
    { generalize (delta_0_1 n) (g_mono_S n); unfold d, x in *.
      omega. }
    assert (D' := delta_b n D). unfold d in D'.
    destruct (eq_nat_dec (g x) (g (S x))).
    * replace (g (S (S n))) with (S (g (S n)))
       by (unfold x in *; omega).
      eapply GD_b; eauto. congruence.
    * assert (g (S x) - g x = 1).
      { generalize (delta_0_1 x) (g_mono_S x); unfold d; omega. }
      replace (g (S (S n))) with (g (S n))
       by (generalize (g_mono_S (S n)); unfold x in *; omega).
      eapply GD_b'; eauto.
Qed.
