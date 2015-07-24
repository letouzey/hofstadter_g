
Require Import Arith Omega Wf_nat List Program Program.Wf.
Set Implicit Arguments.

(* Study of the functional equation:
   G (S n) + G (G n) = S n
   G 0 = 0
*)
(* Link with Fibonacci. *)
(* Source: Hofstadter's book: Goedel, Escher, Bach. *)

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

Module G_via_Program.

Program Fixpoint g_spec n { measure n } : { r : nat | G n r } :=
 match n with
 | O => O
 | S n => S n - g_spec (g_spec n)
 end.
Next Obligation.
 destruct g_spec; simpl. apply le_n_S. now apply G_le.
Defined.
Next Obligation.
 program_simpl.
 destruct (g_spec n) as (a,Ha).
 program_simpl.
 destruct (g_spec a) as (b,Hb).
 program_simpl.
 eapply GS; eauto. change (S n = S n - b + b).
 generalize (G_le Ha) (G_le Hb). omega.
Defined.

Definition g n := let (a,_) := g_spec n in a.

Eval lazy in g 55. (* Compute is very slow... *)

End G_via_Program.


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

Extraction Inline G_rec lt_wf_rec induction_ltof2.
Recursive Extraction g. (* TODO: des let-in parasites *)
Recursive Extraction G_via_Program.g. (* TODO: idem *)

Compute g(0)::g(1)::g(2)::g(3)::g(4)::g(5)::g(6)::g(7)::g(8)::nil.
(*
  = 0 :: 1 :: 1 :: 2 :: 3 :: 3 :: 4 :: 4 :: 5 :: nil
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

Lemma g_S n : g (S n) = S n - g (g n).
Proof.
 generalize (g_eqn n); omega.
Qed.

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

Lemma g_mono n m : n<=m -> g n <= g m.
Proof.
induction 1.
- trivial.
- transitivity (g m); auto using g_mono_S.
Qed.

(* NB : in Coq, for natural numbers, 3-5 = 0 (truncated subtraction) *)

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

(* Two special formulations for [g_step] *)

Lemma g_next n a : g n = a -> g (S n) <> a <-> g (S n) = S a.
Proof.
 generalize (g_step n). omega.
Qed.

Lemma g_prev n a : n<>0 -> g n = a ->
 g (n-1) <> a <-> g (n-1) = a - 1.
Proof.
 intros H Ha.
 assert (Ha' := g_nz H).
 generalize (g_step (n-1)). replace (S (n-1)) with n by omega.
 omega.
Qed.

(* g cannot stay flat very long *)

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

(* Study of the reverse problem: g(x) = a for some a. *)

Lemma max_two_antecedents a n m :
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

(* G is an onto map *)

Lemma g_onto a : exists n, g n = a.
Proof.
induction a.
- exists 0; trivial.
- destruct IHa as (n,Ha).
  destruct (g_step n); [ | exists (S n); omega].
  destruct (g_step (S n)); [ | exists (S (S n)); omega].
  exfalso.
  generalize (@max_two_antecedents a n (S (S n))). omega.
Qed.

(* g can be related to a infinite tree where
    - nodes are labeled via a breadth-first traversal
    - g give the label of the father node.

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

 In this tree, a node is unary if the node label has exactly
 one antecedent, and the node is binary otherwise.
*)

Definition Unary a := forall n m, g n = a -> g m = a -> n = m.
Definition Binary a := ~ Unary a.

Definition rchild n := n + g n. (* rightmost son, always there *)
Definition lchild n := n + g n - 1. (* left son, if there's one *)

Lemma rightmost_child_carac a n : g n = a ->
 g (S n) = S a <-> n = rchild a.
Proof.
 intros Hn.
 assert (H' := g_eqn n).
 rewrite Hn in H'.
 unfold rchild; omega.
Qed.

(* We could now provide explicitely one child for each node *)

Lemma g_onto_eqn a : g (rchild a) = a.
Proof.
destruct (g_onto a) as (n,Hn).
destruct (g_step n) as [H|H].
- unfold rchild.
  rewrite <- Hn. rewrite <- H at 1 3. f_equal. apply g_eqn.
- rewrite Hn in H.
  rewrite rightmost_child_carac in H; trivial. congruence.
Qed.

(* This provides easily a first relationship between g and
   Fibonacci numbers *)

Fixpoint fib (n:nat) : nat := match n with
  | 0 => 1
  | 1 => 1
  | S ((S n) as p) => fib p + fib n
 end.

Lemma fib_eqn n : fib (S (S n)) = fib (S n) + fib n.
Proof.
 reflexivity.
Qed.

Lemma fib_eqn' n : n<>0 -> fib (S n) = fib n + fib (n-1).
Proof.
 destruct n.
 - now destruct 1.
 - intros _. replace (S n - 1) with n by omega.
   apply fib_eqn.
Qed.

Lemma g_fib n : g (fib (S n)) = fib n.
Proof.
induction n.
- reflexivity.
- rewrite fib_eqn.
  rewrite <- IHn.
  apply g_onto_eqn.
Qed.

Lemma g_Sfib n : n<>0 -> g (S (fib (S n))) = S (fib n).
Proof.
 destruct n.
 - now destruct 1.
 - intros _.
   rewrite <- (g_fib (S n)).
   apply rightmost_child_carac; trivial.
   unfold rchild.
   now rewrite !g_fib.
Qed.

(* Let's study now the shape of the G tree.
   First, we prove various characterisation of Unary/Binary *)

Lemma children a n : g n = a ->
  n = rchild a \/ n = lchild a.
Proof.
intros Hn.
destruct (g_step n) as [H|H].
- right.
  destruct (g_step (S n)) as [H'|H'].
  + exfalso.
    generalize (@max_two_antecedents a n (S (S n))). omega.
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
 Unary a <-> forall n, g n = a -> n = rchild a.
Proof.
split; intros H.
- intros n Hn. apply H; trivial. apply g_onto_eqn.
- intros n m Hn Hm. apply H in Hn. apply H in Hm. omega.
Qed.

Lemma unary_carac2 a :
 Unary a <-> g (lchild a) = a - 1.
Proof.
rewrite unary_carac1.
split; intros H.
- destruct (g_lchild a); trivial.
  assert (lchild a = rchild a) by (apply H; omega).
  unfold rchild, lchild in *; omega.
- intros n Hn.
  destruct (children _ Hn) as [H'|H']; trivial.
  rewrite <- H' in H.
  replace a with 0 in * by omega. exact H'.
Qed.

Lemma binary_carac1 a :
 Binary a <-> a<>0 /\ forall n, (g n = a <-> n = rchild a \/ n = lchild a).
Proof.
unfold Binary; rewrite unary_carac2.
split.
- intros H.
  assert (a<>0). { contradict H; now subst. }
  split; trivial.
  destruct (g_lchild a) as [H'|H']; [intros; omega|].
  clear H.
  split.
  + apply children.
  + destruct 1; subst n. apply g_onto_eqn. auto.
- intros (Ha,H) H'.
  assert (g (lchild a) = a). { apply H; now right. }
  omega.
Qed.

Lemma binary_carac2 a :
 Binary a <-> (a<>0 /\ g (lchild a) = a).
Proof.
unfold Binary; rewrite unary_carac2.
split.
- intros H.
  assert (a<>0). { contradict H; now subst. }
  split; trivial.
  destruct (g_lchild a); omega.
- omega.
Qed.

Lemma unary_or_binary n : Unary n \/ Binary n.
Proof.
 destruct (eq_nat_dec n 0).
 - left. subst. apply unary_carac2. reflexivity.
 - destruct (eq_nat_dec (g (lchild n)) n).
   + right. now apply binary_carac2.
   + left. apply unary_carac2. apply g_prev; auto. omega.
     apply g_onto_eqn.
Qed.

Lemma unary_xor_binary n : Unary n -> Binary n -> False.
Proof.
 intuition.
Qed.

(* Now we state the arity of node children *)

Lemma leftmost_son_is_binary n p :
  g p = n -> g (p-1) <> n -> Binary p.
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

Lemma unary_rchild_is_binary n : n<>0 ->
  Unary n -> Binary (rchild n).
Proof.
 intros H U. apply (@leftmost_son_is_binary n).
 - apply g_onto_eqn.
 - rewrite unary_carac2 in U. unfold lchild, rchild in *; omega.
Qed.

Lemma binary_lchild_is_binary n :
  Binary n -> Binary (lchild n).
Proof.
 rewrite binary_carac2. intros (B0,B1).
 apply (@leftmost_son_is_binary n); trivial.
 intros Eq.
 generalize (@max_two_antecedents n _ _ Eq (g_onto_eqn n)).
 assert (H := g_nz B0).
 unfold lchild, rchild in *. omega.
Qed.

Lemma binary_rchild_is_unary n :
  Binary n -> Unary (rchild n).
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

(* Hence the shape of the G tree is repetition of this pattern:

        q
        |
    p   p'
    |   |
    --n--
      |

 where n,p,q are binary nodes and p'=p+1=n+g(n) is unary.
 Fractal aspect : at p and q, full copies of G-tree occur
 (apart from special initial nodes 1 2 3).
*)

(* Another relation (used when flipping G left<->right) *)

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
     * generalize (@max_two_antecedents (g n) (n-1) (S n)). omega.
     * intros. replace (g n - 1) with (g (n-1)) by omega. omega.
   + (* n is rightmost child *)
     generalize (g_eqn n). rewrite H. simpl. rewrite <- minus_n_O.
     omega.
Qed.

(* Depth in the G-tree *)

Notation "f ^^ n" := (Nat.iter n f) (at level 30, right associativity).

Lemma iter_S (f:nat->nat) n p : (f^^(S n)) p = (f^^n) (f p).
Proof.
 revert p.
 induction n as [|n IH]; intros; trivial. simpl. now rewrite <- IH.
Qed.

Compute (g^^3) 13.

Program Fixpoint depth (n:nat) { measure n } : nat :=
 match n with
 | 0 => 0
 | 1 => 0
 | _ => S (depth (g n))
 end.
Next Obligation.
 apply g_lt. omega.
Qed.

Compute depth 13.

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

Lemma depth_correct n : n<>0 -> (g^^(depth n)) n = 1.
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

Lemma fib_mono_S k : fib k <= fib (S k).
Proof.
 induction k as [[|[|k]] IH] using lt_wf_rec; auto with arith.
 simpl. omega.
Qed.

Lemma fib_mono k k' : k <= k' -> fib k <= fib k'.
Proof.
 induction 1; trivial.
 transitivity (fib m); trivial. apply fib_mono_S.
Qed.

Lemma fib_nz k : 1 <= fib k.
Proof.
 change 1 with (fib 0). apply fib_mono; auto with arith.
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

Lemma depth_Sfib k : k<>0 -> depth (S (fib k)) = k.
Proof.
 induction k as [|[|k] IH].
 - now destruct 1.
 - reflexivity.
 - intros _.
   rewrite depth_eqn.
   + rewrite g_Sfib, IH; omega.
   + unfold lt. apply le_n_S. apply fib_nz.
Qed.

Lemma depth_0 n : depth n = 0 <-> n<=1.
Proof.
 destruct n as [|[|n]].
 - compute; auto with arith.
 - compute; auto with arith.
 - rewrite depth_SS. omega.
Qed.

Lemma depth_carac k n : k<>0 ->
  depth n = k <-> S (fib k) <= n <= fib (S k).
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

(* Conclusion:
   - (fib k)+1 is the leftmost node at depth k
   - fib (k+1) is the rightmost node at depth k
   - hence we have fib (k+1) - fib k = fib (k-1) nodes at depth k.
*)

(* Alternatively, we could also have considered
    U(k) : unary nodes at depth k
    B(k) : binary nodes at depth k
  and their recursive equations:
    U(k+1) = B(k)
    B(k+1) = U(k)+B(k)
  These numbers are also fibonacci numbers (apart from k=0).
  and Nodes(k) = U(k)+B(k).
*)


(* TODO:

- prove the effect of g on Fibonacci decomposition of numbers

- prove that g(n) = ceil((n+1)/phi) = ceil(tau*(n+1))
  where phi = (1+sqrt(5))/2
        tau = 1/phi = phi-1 = (sqrt(5)-1)/2

*)


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

(* The flipped g' function, corresponding to the flipped G tree *)

Definition g' n := flip (g (flip n)).

Compute g'(0)::g'(1)::g'(2)::g'(3)::g'(4)::g'(5)::g'(6)::g'(7)::g'(8)::nil.

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