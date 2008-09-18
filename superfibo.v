
Require Import Arith.
Require Import Omega.
Require Import Wf_nat.
Require Import List.

(* Study of the functional equation  G (S n) + G (G n) = S n, with G 0 = 0 *)
(* Link with Fibonacci. *)

Inductive G : nat -> nat -> Prop := 
   | G_0 : G 0 0
   | G_n : forall n a b c, G n a -> G a b -> S n = c+b -> G (S n) c.
Hint Constructors G.

Lemma one_gives_1 : G 1 1. 
Proof.
change (G 1 (1-0)).
eapply G_n; eauto.
Qed.
Hint Resolve one_gives_1.

Lemma first_bound : forall n a, G n a -> a <= n.
Proof.
cut (forall N n a, n <= N -> G n a -> a <= n). firstorder.
induction N.
(* N=0 *)
do 2 inversion_clear 1; subst; auto.
(* N>0 *)
inversion_clear 1; subst; auto.
inversion_clear 1; omega.
Qed.
Hint Resolve first_bound.

Definition g_spec : forall n, { a : nat | G n a }.
Proof. 
cut (forall N n, n <= N -> { a : nat | G n a }).
intros H n; apply (H n); trivial. 
induction N.
destruct n.
exists 0; auto.
intros; elimtype False; inversion H.
intros.
destruct (le_lt_eq_dec _ _ H).
apply IHN; auto with arith.
subst; clear H.
destruct (IHN N) as [a Ha]; auto.
destruct (IHN a) as [b Hb]; auto.
exists ((S N) -b); auto.
eapply G_n; eauto.
assert (b <= N) by apply le_trans with a; auto.
omega.
Defined.

Definition g n := let (a,_) := g_spec n in a.

(*
Eval compute in g(0)::g(1)::g(2)::g(3)::g(4)::g(5)::g(6)::g(7)::nil.
  = 0 :: 1 :: 1 :: 2 :: 3 :: 3 :: 4 :: 4 :: nil
     : list nat
*)

Lemma g_correct_0 : forall n, G n (g n).
Proof. 
unfold g; intro n; destruct (g_spec n); auto.
Qed.
Hint Resolve g_correct_0.

Lemma g_correct_1 : g 0 = 0.
Proof.
unfold g; destruct (g_spec 0).
inversion g0; auto.
Qed.

Lemma unicity : forall n a b, G n a -> G n b -> a = b.
Proof. 
cut (forall N n a b, n <= N -> G n a -> G n b -> a = b).
intros H n; intros; eapply (H n); eauto.
induction N.
do 3 inversion_clear 1; auto.
inversion_clear 1; eauto.
do 2 inversion_clear 1.
assert (a0 = a1) by eauto.
subst.
assert (b0 = b1) by eauto.
subst.
omega.
Qed.

Lemma g_correct_2 : forall n,  S n = g (S n) + g (g n).
Proof.
unfold g; intros n.
destruct (g_spec (S n)) as [gSn HgSn].
destruct (g_spec n) as [gn Hgn].
destruct (g_spec gn) as [ggn Hggn]. 
inversion_clear HgSn.
rewrite (unicity _ _ _ Hgn H) in Hggn.
rewrite (unicity _ _ _ Hggn H0); auto.
Qed.

Lemma g_unique : forall f,  f 0=0  -> (forall n, S n = f (S n)+f(f n)) -> 
  forall n, f n = g n.
Proof.
intros f Hf1 Hf2.
cut (forall N n, n<= N -> f n  = g n).
intros H n; apply (H n); auto.
induction N.
inversion_clear 1.
rewrite g_correct_1; auto.
inversion_clear 1; auto.
generalize (g_correct_2 N).
generalize (Hf2 N).
rewrite (IHN N); auto.
rewrite (IHN (g N)); auto.
omega.
Qed.

Lemma second_bound : forall n m a b, n <= m -> G n a -> G m b -> 
   (a <= b /\ b - a <= m - n). 
Proof.
cut (forall M n m a b, m <= M -> n <= m -> G n a -> G m b -> 
   n <= m -> a <= b /\ b - a <= m - n).
intros H n m; intros; apply (H m); auto.
induction M.
(* M=0 *)
do 4 (inversion_clear 1; subst; auto).
(* M>0 *)
inversion_clear 1; subst; auto.
intros _; intros.
inversion_clear H0.
destruct n as [|N].
inversion_clear H; omega.
inversion_clear H.
destruct (IHM N M a1 a0); auto with arith.
destruct (IHM a1 a0 b1 b0); auto with arith.
omega.
Qed.

Lemma third_bound : forall n a, 1<=n ->  G n a -> 1<= a.
Proof. 
 intros; destruct (second_bound 1 n 1 a); auto.
Qed. 

Lemma only_0_gives_0 : forall n, G n 0 -> n = 0.
Proof.
destruct n; auto.
intros; assert (1<=0).
 apply third_bound with (S n); auto with arith.
inversion H0.
Qed.

Lemma only_0_1_are_fixpoints : forall n m, G n m -> n = m -> n <= 1.
Proof.
destruct n; auto.
inversion_clear 1; intros.
assert (b=0) by omega.
subst.
rewrite (only_0_gives_0 a H1) in H0.
rewrite (only_0_gives_0 n H0); auto.
Qed.

Lemma fourth_bound : forall n a, 1<n -> G n a -> a<n.
Proof.
intros.
generalize (first_bound _ _ H0) (only_0_1_are_fixpoints _ _ H0); omega.
Qed.
Hint Resolve fourth_bound.

(* Study of the reverse problem: G(x) = a for some a. *)

Lemma max_two_solutions : forall a n m, n<m -> 
 G n a -> G m a -> m = S n /\ m = a + g a.
Proof.
intros.
destruct m as [|m].
inversion H.
destruct n as [|n]. 
inversion H0; subst.
generalize (only_0_gives_0 _ H1); omega.
inversion H0; inversion H1; subst; auto.
destruct (second_bound n m a0 a1); auto; try omega.
destruct (second_bound n (S n) a0 a); auto; try omega.
destruct (second_bound m (S m) a1 a); auto; try omega.
destruct (second_bound a0 a1 b b0); auto; try omega.
assert (a=a1) by omega.
subst a1.
rewrite (unicity a (g a) b0); auto.
omega.
Qed.

Lemma same_equation_when_one_solution : forall a n, G n a -> 
  (forall m, G m a -> m = n) -> n = a + g a.
Proof.
intros.
generalize (g_correct_0 (S n)).
inversion 1; subst.
rewrite (unicity n a0 a) in H4; auto; clear H3.
rewrite (unicity a b (g a)) in H5; auto; clear H4.
destruct (second_bound n (S n) a (g (S n))); auto; try omega.
assert (g (S n) = a -> S n = n).
 intros A; apply (H0 (S n)); rewrite <- A; auto.
omega.
Qed.


(* G is an onto map *)

Lemma g_onto : forall a, { n : nat | G n a }.
Proof. 
induction a. 
exists 0; auto.
destruct IHa.
destruct (second_bound x (S x) a (g (S x))); auto; try omega.
destruct (eq_nat_dec (S a) (g (S x))).
exists (S x); rewrite e; auto.
assert (g (S x) = a) by omega.
clear n H0 H.
destruct (second_bound (S x) (S (S x)) a (g (S (S x)))); auto; try omega.
rewrite <- H1; auto.
destruct (eq_nat_dec (S a) (g (S (S x)))).
exists (S (S x)); rewrite e; auto.
elimtype False.
assert (g (S (S x)) = a) by omega.
destruct (max_two_solutions a x (S (S x))); auto.
rewrite <- H2; auto.
omega.
Qed.

Lemma another_G_equation: forall a b, G a b -> G (a+b) a.
Proof.
intros.
rewrite (unicity a b (g a)); auto.
destruct (g_onto a).
destruct x.
inversion g0.
subst.
inversion H; auto.
destruct (eq_nat_dec (g (S (S x))) a).
destruct (max_two_solutions a (S x) (S (S x))); auto.
rewrite <- e; auto.
rewrite H1 in e.
pattern a at 3; rewrite <- e; auto.
destruct (eq_nat_dec (g x) a).
destruct (max_two_solutions a x (S x)); auto.
rewrite <- e; auto.
rewrite H1 in g0; auto.
rewrite <- (@same_equation_when_one_solution a (S x)); auto.
intros.
destruct (lt_eq_lt_dec m (S x)) as [[H1|H1]|H1]; auto.
destruct (max_two_solutions a m (S x)); auto.
inversion H2; subst.
rewrite (unicity m a (g m)) in n0; intuition.
destruct (max_two_solutions a (S x) m); auto.
rewrite <- H2 in n.
rewrite (unicity m a (g m)) in n; intuition.
Qed. 

Fixpoint fib (n:nat) : nat := match n with 
  | 0 => 1
  | 1 => 1 
  | S ((S n) as p) => fib p + fib n
 end.

Lemma g_fib : forall n, g (fib (S n)) = fib n.
Proof.
induction n.
simpl; auto.
assert (G (fib (S n) + fib n) (fib (S n))).
 apply another_G_equation.
 rewrite <- IHn; auto.
rewrite (unicity (fib (S n) + fib n) (fib (S n)) (g (fib (S (S n))))); auto.
Qed.

 