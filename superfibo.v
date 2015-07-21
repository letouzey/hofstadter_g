
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

6 7  8
 4   5
   3
   2
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

Lemma g_fib n : g (fib (S n)) = fib n.
Proof.
induction n.
- reflexivity.
- change (fib (S (S n))) with (fib (S n) + fib n).
  rewrite <- IHn.
  apply g_onto_eqn.
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
 (apart from special nodes 1 2 3).
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

(* TODO:

- prove the effect of g on Fibonacci decomposition of numbers

- prove that g(n) = ceil((n+1)/phi) = ceil(tau*(n+1))
  where phi = (1+sqrt(5))/2
        tau = 1/phi = phi-1 = (sqrt(5)-1)/2

*)
