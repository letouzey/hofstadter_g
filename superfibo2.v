
Require Import Arith.
Require Import Omega.
Require Import Wf_nat.
Require Import List.

(* G-Flip : cf quizz by Hofstadter: mirror of G tree *)

(* Study of the functional equation
  G (G n) + G (n-1) = n  for n>3
  G 0 = 0
  G 1 = G 2 = 1
  G 3 = 2
*)
(* Link with Fibonacci. *)


(* First, a "positive" version of this equation:
   - if H(n-2)=H(n-1) then H(n)=H(n-1)+1
   - if H(n-2)<>H(n-1) but HH(n-1)=H(H(n-1)+1) then H(n)=H(n)+1
   - otherwise H(n)=H(n-1)
   We'll prove later the equivalence with the previous G. *)

Inductive H : nat -> nat -> Prop :=
   H_0 : H 0 0
 | H_1 : H 1 1
 | H_2 : H 2 1
 | H_3 : H 3 2
 | H_4 : H 4 3
 | H_n1 n a : 5<=n -> H (n-2) a -> H (n-1) a -> H n (S a)
 | H_n2 n a b c : 5<=n -> H (n-2) a -> H (n-1) b -> a<>b ->
                      H b c -> H (S b) c -> H n (S b)
 | H_n3 n a b c d : 5<=n -> H (n-2) a -> H (n-1) b -> a<>b ->
                      H b c -> H (S b) d -> c <> d -> H n b.
Hint Constructors H.

Definition h_aux :
 forall N, forall n, n<N -> { k : nat | H n k /\ k <= n /\ (1<n -> k < n) }.
Proof.
induction N.
intros.
elimtype False; inversion H0.
rename IHN into h.
intros.
destruct (le_lt_dec n 4).
clear h H0 N.
destruct n.
exists 0; repeat split; auto; inversion 1.
destruct n.
exists 1; auto.
destruct n.
exists 1; auto.
destruct n.
exists 2; auto.
destruct n.
exists 3; auto.
elimtype False; omega.
destruct (h (n-2)) as (x,(Hx,(Hx',Hx''))); [omega|].
destruct (h (n-1)) as (y,(Hy,(Hy',Hy''))); [omega|].
destruct (eq_nat_dec x y).
exists (S y).
repeat split.
subst; auto.
omega.
omega.
destruct (h y) as (z,(Hz,(Hz',Hz''))); [omega|].
destruct (h (S y)) as (t,(Ht,(Ht',Ht''))); [omega|].
destruct (eq_nat_dec z t).
exists (S y).
subst.
repeat split; eauto.
omega.
omega.
exists y.
repeat split; eauto.
omega.
omega.
Qed.

Definition h_spec : forall n, { k : nat | H n k }.
Proof.
intros.
destruct (h_aux (S n) n); auto.
exists x; intuition.
Qed.

Definition h n := let (k,_) := h_spec n in k.

Lemma h_prop : forall n, H n (h n).
Proof.
intros; unfold h; destruct (h_spec n); auto.
Qed.

Lemma h_0 : h 0 = 0.
Proof.
generalize (h_prop 0); inversion 1; auto; try omega.
Qed.

Lemma h_1 : h 1 = 1.
Proof.
generalize (h_prop 1); inversion 1; auto; try omega.
Qed.

Lemma h_2 : h 2 = 1.
Proof.
generalize (h_prop 2); inversion 1; auto; try omega.
Qed.

Lemma h_3 : h 3 = 2.
Proof.
generalize (h_prop 3); inversion 1; auto; try omega.
Qed.

Lemma h_4 : h 4 = 3.
Proof.
generalize (h_prop 4); inversion 1; auto; try omega.
Qed.

Lemma h_5 : h 5 = 3.
Proof.
generalize (h_prop 5); inversion 1; auto; try omega; subst; simpl in *.
inversion H3; try omega.
inversion H4; try omega; subst; simpl in *.
inversion H6; inversion H8; try omega.
inversion H3; try omega.
Qed.

Lemma H_step : forall n k, H n k -> k<= n.
Proof.
cut (forall N, forall n k, H n k -> n<N -> k<=n).
intros.
eapply H0; eauto.
induction N.
inversion_clear 2.
intros.
inversion H0; try omega; generalize (IHN _ _ H4); omega.
Qed.

Lemma H_step1 : forall n k, H n k -> 0<n -> 0<k.
Proof.
cut (forall N, forall n k, H n k -> 0<n<N -> 0<k).
intros.
eapply H0; eauto.
induction N.
intros; omega.
intros.
inversion H0; try omega; generalize (IHN _ _ H4); omega.
Qed.

Lemma H_step2 : forall n k, H n k -> 1<n -> 0<k<n.
Proof.
cut (forall N, forall n k, H n k -> 1<n<N -> 0<k<n).
intros.
eapply H0; eauto.
induction N.
intros; omega.
intros.
inversion H0; try omega; generalize (IHN _ _ H4); omega.
Qed.

Lemma H_unique : forall n k k', H n k -> H n k' -> k = k'.
Proof.
cut (forall N, forall n k k', H n k -> H n k' -> n < N -> k = k').
intros.
eapply H0; eauto.
induction N.
inversion_clear 3.
intros.
inversion H0; inversion H1; auto; try omega.
generalize (IHN _ _ _ H4 H9); omega.
generalize (IHN _ _ _ H4 H9) (IHN _ _ _ H5 H10); omega.
generalize (IHN _ _ _ H4 H9) (IHN _ _ _ H5 H10); omega.
generalize (IHN _ _ _ H4 H12) (IHN _ _ _ H5 H13); omega.
generalize (IHN _ _ _ H4 H12) (IHN _ _ _ H5 H13); omega.
generalize (IHN _ _ _ H5 H13); intros.
rewrite H20 in H7; try omega.
rewrite H20 in H8; try omega.
generalize (IHN _ _ _ H7 H15) (IHN _ _ _ H8 H16)(H_step2 _ _ H13); omega.
generalize (IHN _ _ _ H4 H13) (IHN _ _ _ H5 H14); omega.
generalize (IHN _ _ _ H5 H14); intros; subst.
rewrite H20 in H7; try omega.
rewrite H20 in H8; try omega.
generalize (IHN _ _ _ H7 H16) (IHN _ _ _ H8 H17)(H_step2 _ _ H5); omega.
subst.
generalize (IHN _ _ _ H4 H13) (IHN _ _ _ H5 H14); omega.
Qed.

Lemma h_unique : forall n k, H n k -> k = h n.
Proof.
intros.
eapply H_unique; eauto.
apply h_prop.
Qed.

Lemma h_step : forall n, h (S n) = h n \/ h (S n) = S (h n).
Proof.
intros.
unfold h at 1 3.
destruct (h_spec (S n)).
cut (H n x \/ H n (pred x)).
 destruct 1.
 left; apply h_unique; auto.
 generalize (h_unique _ _ H0).
 intros.
 right; rewrite <- H1.
 generalize (H_step1 _ _ H0).
 destruct n.
 inversion_clear h0; omega.
 omega.
 inversion h0; simpl; auto;
 replace (S n - 1) with n in H2; auto; omega.
Qed.

Lemma h_step2 : forall n, h (1+n) = h n -> h (2+n) = 1+h (1+n).
Proof.
simpl.
unfold h.
intros.
destruct (h_spec n).
destruct (h_spec (S n)).
destruct (h_spec (S (S n))).
subst x0.
inversion h2.
subst.
inversion h1; try omega; subst.
inversion h0; omega.
subst.
inversion h0; try omega.
subst.
inversion h0; try omega; subst.
inversion h1; omega.
subst; simpl in *.
rewrite (H_unique _ _ _ h1 H2); auto.
subst; simpl in *.
rewrite (H_unique _ _ _ h1 H2); auto.
subst; simpl in *.
replace (n-0) with n in H1; auto with arith.
rewrite <- (H_unique _ _ _ h0 H1) in H3; auto.
rewrite (H_unique _ _ _ h1 H2) in H3; auto.
elim H3; auto.
Qed.

Lemma h_implem_g_aux : forall N,
       (forall n, 3<n -> n<=N -> h (h n) + h (pred n) = n)
   /\ (N>2 -> h N = h (pred N) -> h (S (h N)) = S (h (h N))).
Proof.
induction N.
intros.
split.
inversion 2; subst; omega.
inversion 1.
split; intros.
destruct (le_lt_dec N 3).
assert (n=4) by omega.
subst.
simpl; rewrite h_4; rewrite h_3; auto.
inversion H1.
simpl.
generalize (h_prop (S N)); inversion 1; try omega.
(* case 1*)
subst.
simpl in *.
replace (N-0) with N in H8; [|omega].
replace (N-1) with (pred N) in H6; [|omega].
destruct IHN.
rewrite (h_unique _ _ H8).
assert (h N = h (pred N)).
 rewrite <- (h_unique _ _ H8).
 apply (h_unique _ _ H6).
rewrite H7; try omega.
generalize (H2 N).
omega.
(* case 2*)
subst.
simpl in *.
replace (N-0) with N in H7; [|omega].
replace (N-1) with (pred N) in H6; [|omega].
destruct IHN.
rewrite <- (h_unique _ _ H11).
rewrite (h_unique _ _ H9).
rewrite (h_unique _ _ H7).
generalize (h_step (pred N)).
replace (S (pred N)) with N; [|omega].
destruct 1.
rewrite (h_unique _ _ H6) in H8.
rewrite (h_unique _ _ H7) in H8.
elim H8; auto.
generalize (H2 N).
omega.
(* case 3 *)
subst.
simpl in *.
replace (N-0) with N in H6; [|omega].
replace (N-1) with (pred N) in H5; [|omega].
destruct IHN.
generalize (h_step (pred N)).
replace (S (pred N)) with N; [|omega].
destruct 1.
rewrite <- (h_unique _ _ H6) in H12.
rewrite <- (h_unique _ _ H5) in H12.
elim H7; auto.
rewrite (h_unique _ _ H6).
rewrite (h_unique _ _ H6) in H9.
rewrite (h_unique _ _ H6) in H8.
generalize (h_step (h N)).
destruct 1.
rewrite <- (h_unique _ _ H8) in H13.
rewrite <- (h_unique _ _ H9) in H13.
elim H10; auto.
generalize (H2 N); omega.

destruct IHN; auto.

(* inv *)
generalize (h_prop (S N)); inversion 1; try omega.
rewrite h_2; apply h_3.
rewrite h_3; apply h_4.
subst; simpl in *.
replace (N-0) with N in H7; [|omega].
rewrite <- (h_unique _ _ H7) in H1.
omega.
subst; simpl in *.
replace (N-0) with N in H6; [|omega].
rewrite (h_unique _ _ H6) in H3.
omega.
subst; simpl in *.
replace (N-0) with N in H5; [|omega].
replace (N-1) with (pred N) in H4; [|omega].
rewrite H1.
rewrite H1 in H7.
rewrite H1 in H8.
rewrite H1 in H6.
generalize (h_step (h N)).
destruct 1; auto.
rewrite <- (h_unique _ _ H7) in H10.
rewrite <- (h_unique _ _ H8) in H10.
elim H9; auto.
Qed.

Lemma h_implem_g : forall n, 3<n -> h (h n) + h (pred n) = n.
Proof.
intros.
destruct (h_implem_g_aux n); auto.
Qed.

Definition G_spec (g:nat->nat) :=
  (g 0 = 0 /\ g 1 = 1 /\ g 2 = 1 /\ g 3 = 2) /\
  (forall n, 3<n -> g (g n) + g (pred n) = n).

Lemma G_ineg : forall g, G_spec g -> forall n, 1<n -> 0<g n<n.
Proof.
intros g Hg.
cut (forall N, forall n, 1<n<N -> 0<g n<n).
eauto.
induction N.
intros; omega.
intros.
destruct Hg.
destruct H0.
inversion H3; [subst|generalize (IHN n); omega].
destruct (le_lt_dec N 3).
do 4 (destruct N; try omega).
clear H0 H3.
generalize (H2 _ l).
assert (3 < S N) by omega.
generalize (H2 _ H0); clear H0.
simpl; intros.
generalize (IHN (pred N)); intros.
assert (1< g (g N) < N) by omega.
destruct (eq_nat_dec (g N) 0).
rewrite e in H5.
destruct H1.
rewrite H1 in H5; omega.
destruct (eq_nat_dec (g N) N).
do 2 rewrite e in H5.
omega.
split; try omega.
destruct (eq_nat_dec (g N) (S N)); try omega.
rewrite e in H3.
generalize (IHN (N - g (pred N))).
replace (N - g (pred N)) with (g (S N)); [|omega].
omega.
Qed.

Lemma G_ineg0 : forall g, G_spec g -> forall n, 0<=g n<=n.
Proof.
intros.
generalize (G_ineg _ H0 n).
destruct H0.
do 2 (destruct n; try omega).
Qed.


(*
Lemma G_ineg2 : forall g, G_spec g -> forall n m, n<=m -> g n <= g m /\ g m-g n<=m-n.

NON!!! une fonction vérifiant G n'est pas forcément monotone.

Par exemple:
g0=0
g1=1
g2=1
g3=2
g4=3
g5=3
g6=5
g7=3
g8=6
g9=4
g10=8
g11=4
g12=10
etc, etc...

Par contre, si l'on suppose en plus g monotone, alors g = h.
*)

Lemma loc_mon_glob_mon : forall g, (forall n, g n <= g (S n)) ->
 (forall n m, n <= m -> g n <= g m).
Proof.
intros g Mon.
cut (forall N n m, N+n=m -> g n <= g m).
intros.
apply (H0 (m-n)); omega.
induction N.
intros; simpl in *; subst; auto.
intros.
apply le_trans with (g (S n)); auto.
apply IHN; omega.
Qed.


Lemma G_ineg2 : forall g, G_spec g ->
  (forall n, g n<=g (S n)) ->
  forall n m, n <= m -> g m-g n<=m-n.
Proof.
intros g Hg Mon.
cut (forall N n m, n<=m<N -> g m-g n<=m-n).
eauto.
induction N.
intros; omega.
elim Hg; intros Hg1 Hg2.
cut (forall n m, 3<n -> n <= m < S N -> g m - g n <= m - n).
intros.
destruct (le_lt_dec n 3).
destruct (le_lt_dec m 3).
 do 4 (destruct n; [ do 4 (destruct m; try omega) |]); omega.
assert (g 4 = 3).
 assert (g (g 4) = 2) by (generalize (Hg2 4); simpl; omega).
 generalize (G_ineg _ Hg 4).
 destruct (g 4); try omega.
 destruct n0; try omega.
 destruct n0; try omega.
assert (g 4 - g n <= 4-n).
 rewrite H2.
 do 4 (destruct n; try omega).
generalize (H0 4 m); omega.
generalize (H0 n m); omega.
intros.
destruct H1.
inversion H2; [subst N | generalize (IHN n m); omega].
generalize (Hg2 (S n)) (Hg2 (S m)); simpl; intros.
generalize (loc_mon_glob_mon _ Mon (S n) (S m)).
generalize (loc_mon_glob_mon _ Mon (g (S n)) (g (S m))).
omega.
Qed.

Lemma G_unique : forall g1 g2, G_spec g1 -> G_spec g2 ->
  (forall n, g1 n <= g1 (S n)) ->
  (forall n, g2 n <= g2 (S n)) ->
  forall n, g1 n = g2 n.
Proof.
intros g1 g2 Hg1 Hg2 Mon1 Mon2.
cut (forall N n, n<N-> g1 n = g2 n).
eauto.
induction N.
inversion 1.
intros.
inversion H0; [subst N | generalize (IHN n); omega].
clear H0.
elim Hg1; intros Hg11 Hg12.
elim Hg2; intros Hg21 Hg22.
destruct (le_lt_dec n 3).
do 4 (destruct n; try omega).
generalize (Hg12 n l) (Hg22 n l).
generalize (IHN (pred n)); intros.
set (x1:=g1 n) in *.
set (x2:=g2 n) in *.
assert (g2 (pred n) <= x2 /\ x2-g2(pred n) <= 1).
 unfold x2; split.
 generalize (Mon2 (pred n)); try omega.
  replace (S (pred n)) with n; omega.
 generalize (G_ineg2 _ Hg2 Mon2 (pred n) n); omega.
assert (g1 (pred n) <= x1 /\ x1-g1(pred n) <= 1).
 unfold x1; split.
 generalize (Mon1 (pred n)); try omega.
  replace (S (pred n)) with n; omega.
 generalize (G_ineg2 _ Hg1 Mon1 (pred n) n); omega.

destruct (lt_eq_lt_dec x1 x2) as [[E|E]|E]; auto; elimtype False.
assert (g1 (pred n) = x1).
 rewrite <- H0 in H3; try omega.
clear H3 H4.
assert (g1 (g1 (S n)) = S (g1 (g1 n))).
 generalize (Hg12 (S n)); simpl.
 unfold x1 in *; omega.
assert (g1 (S n) = S (g1 n)).
 generalize (G_ineg2 _ Hg1 Mon1 (g1 n) (g1 (S n)) (Mon1 n)).
 generalize (G_ineg2 _ Hg1 Mon1 n (S n)).
 omega.
assert (S (g1 n) <= x2).
 unfold x2,x1 in *; omega.
generalize (loc_mon_glob_mon _ Mon1 _ _ H6).
rewrite <- H4.
rewrite H3.
rewrite (IHN x2).
unfold x1, x2 in *.
omega.
unfold x2 in *; generalize (G_ineg _ Hg2 n); omega.

assert (g2 (pred n) = x2).
 rewrite <- H0 in H3; try omega.
clear H3 H4.
assert (g2 (g2 (S n)) = S (g2 (g2 n))).
 generalize (Hg22 (S n)); simpl.
 unfold x2 in *; omega.
assert (g2 (S n) = S (g2 n)).
 generalize (G_ineg2 _ Hg2 Mon2 (g2 n) (g2 (S n)) (Mon2 n)).
 generalize (G_ineg2 _ Hg2 Mon2 n (S n)).
 omega.
assert (S (g2 n) <= x1).
 unfold x2,x1 in *; omega.
generalize (loc_mon_glob_mon _ Mon2 _ _ H6).
rewrite <- H4.
rewrite H3.
rewrite <- (IHN x1).
unfold x1, x2 in *.
omega.
unfold x1 in *; generalize (G_ineg _ Hg1 n); omega.
Qed.

(* another caracterization for h: we transform its algorithm into an equation:

h(0) = 0
h(1) = 1
h(2) = 1
h(3) = 2
h(4) = 3
for n>=4, h(n+1) = h(n) + 1 - (h(n)-h(n-1))*(h(h(n)+1)-h(h(n)))

*)
