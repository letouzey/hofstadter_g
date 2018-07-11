
Require Import Arith Omega Wf_nat List.
Require Import DeltaList Fib FunG.
Require Extraction.
Set Implicit Arguments.

(** Study of the functional equation:
     - [Fk (S n) + Fk^k (n) = S n]
     - [Fk 0 = 0]
*)

(* k : cf au dessus, p.ex. Hoftadter G = F 2, H = F 3
   p : iteration (p+1)-ieme. Donc 0 valeur par défaut
   n : input
   m : output *)

Module V1.

Inductive F : nat -> nat -> nat -> nat -> Prop :=
| Hk0 p n : F 0 p n n
| Hn0 k p : F k p 0 0
| HSp k p a b c : F (S k) p a b -> F (S k) 0 b c -> F (S k) (S p) a c
| HSn k n a b : F (S k) k n a -> S n = a+b -> F (S k) 0 (S n) b.
Hint Constructors F.

Lemma F_1 k p : F k p 1 1.
Proof.
 revert k.
 induction p.
 - intros.
   destruct k.
   + apply Hk0.
   + eapply HSn. apply Hn0. reflexivity.
 - intros.
   destruct k.
   + apply Hk0.
   + eapply HSp.
     apply IHp.
     eapply HSn.
     * apply Hn0.
     * reflexivity.
Qed.

End V1.

Module V2.

Inductive F : nat -> nat -> nat -> Prop :=
| F0 n : F 0 n n
| Fk0 k : F k 0 0
| FS k n a b : Fs (S k) (S k) n a -> S n = a+b -> F (S k) (S n) b

with Fs : nat -> nat -> nat -> nat -> Prop :=
| Fs0 k n : Fs 0 k n n
| FsS p k a b c : Fs p k a b -> F k b c -> Fs (S p) k a c.

Hint Constructors F Fs.

Lemma Fs_0 p k : Fs p k 0 0.
Proof.
 revert k.
 induction p; intros.
 - apply Fs0.
 - eapply FsS. apply IHp. apply Fk0.
Qed.

Lemma F_1 k : F k 1 1.
Proof.
 induction k.
 - apply F0.
 - eapply FS. eapply Fs_0. reflexivity.
Qed.

Lemma Fs_1 p k : Fs p k 1 1.
Proof.
 induction p; intros.
 - apply Fs0.
 - eapply FsS. apply IHp. apply F_1.
Qed.

Lemma F_le k n a : F k n a -> a <= n.
Proof.
 induction 1; omega.
Qed.

Lemma Fs_le p k n a : Fs p k n a -> a <= n.
Proof.
 induction 1.
 - reflexivity.
 - apply F_le in H0. omega.
Qed.
Hint Resolve F_le Fs_le.

Scheme F_ind2 := Induction for F Sort Prop
  with Fs_ind2  := Induction for Fs Sort Prop.

Combined Scheme F_Fs_ind from F_ind2, Fs_ind2.

Lemma F_Fs_fun :
 (forall k n a, F k n a -> forall a', F k n a' -> a = a') /\
 (forall p k n a, Fs p k n a -> forall a', Fs p k n a' -> a = a').
Proof.
apply F_Fs_ind.
- inversion_clear 1; auto.
- inversion_clear 1; auto.
- intros.
  inversion_clear H0; auto.
  apply H in H1. omega.
- inversion_clear 1; auto.
- intros.
  inversion_clear H1; auto.
  apply H in H2. subst b0.
  apply H0 in H3. auto.
Qed.

Lemma F_fun k n a a' : F k n a -> F k n a' -> a = a'.
Proof.
 intro. now apply F_Fs_fun.
Qed.


(* Diverge à Qed, peut importe si induction 1 ou induction 2
Lemma F_fun k n a a' : F k n a -> F k n a' -> a = a'
with Fs_fun p k n a a' : Fs p k n a -> Fs p k n a' -> a = a'.
Proof.
 - induction 2.
   + inversion H; subst; auto.
   + inversion H; subst; auto.
   + inversion H; subst; auto.
     assert (a0 = a1). { eapply Fs_fun; eauto. }
     omega.
 - induction 2.
   + inversion H; subst; auto.
   + inversion H; subst; auto.
     assert (b = b0). { eapply Fs_fun; eauto. }
     subst b0.
     eapply F_fun; eauto.
Qed.
*)

(*
Lemma F_rec k (P:nat->nat->Set) :
P k 0 ->
(forall n, P k n -> (forall a, F k n a -> P k a) -> P k (S n)) ->
forall n, P k n.
Proof.
intros P_0 P_S.
induction n as [[|n] IH] using lt_wf_rec.
- apply P_0.
- apply P_S.
  + apply IH. auto.
  + intros. apply IH. eauto with arith.
Defined.
*)

Definition f_spec k n : { a : nat | F k n a }.
Proof.
induction n as [[|n] IH ] using lt_wf_rec.
- now exists 0.
- destruct k.
  + now exists (S n).
  + assert (forall p m, m <= n -> { a : nat | Fs p (S k) m a }).
    { induction p.
      - intros. now exists m.
      - intros.
        destruct (IHp m H) as (a,Ha).
        destruct (IH a) as (b,Hb).
        apply Fs_le in Ha. omega.
        exists b. eapply FsS; eauto. }
    destruct (H (S k) n) as (a,Ha); auto.
    exists (S n - a).
    eapply FS; eauto.
    apply Fs_le in Ha. omega.
Defined.

Definition f k n := let (a,_) := f_spec k n in a.

Extraction Inline lt_wf_rec induction_ltof2.
Recursive Extraction f.

Definition test := List.seq 0 20.

Compute List.map (f 1) test.
Compute List.map (f 2) test. (* 0 1 1 2 3 3 4 4 5 6 6 7 8 8 *)
Compute List.map (f 3) test. (* 0 1 1 2 3 4 4 5 5 6 7 7 8 9 *)

Lemma f_correct k n : F k n (f k n).
Proof.
unfold f; now destruct (f_spec k n).
Qed.
Hint Resolve f_correct.

Lemma f_complete k n p : F k n p <-> p = f k n.
Proof.
split; intros H.
- apply (F_fun H (f_correct k n)).
- subst. apply f_correct.
Qed.

Lemma f_0_n n : f 0 n = n.
Proof.
symmetry. rewrite <- f_complete. auto.
Qed.

Lemma f_k_0 k : f k 0 = 0.
Proof.
symmetry. rewrite <- f_complete. auto.
Qed.

Lemma f_k_1 k : f k 1 = 1.
Proof.
symmetry. rewrite <- f_complete. apply F_1.
Qed.

Lemma Fs_iter_f p k n : Fs p k n (((f k)^^p) n).
Proof.
induction p.
- simpl. auto.
- eapply FsS; eauto. simpl.
  now rewrite f_complete.
Qed.

Lemma fs_k_0 p k : ((f k)^^p) 0 = 0.
Proof.
 induction p; simpl; auto.
 rewrite IHp. apply f_k_0.
Qed.

Lemma f_eqn k n : k<>0 -> f k (S n) + ((f k)^^k) n = S n.
Proof.
destruct k.
 - now destruct 1.
 - intros _.
   assert (H := f_correct (S k) (S n)).
   inversion_clear H.
   assert (Nat.iter (S k) (f (S k)) n = a).
   { revert H0. apply F_Fs_fun. apply Fs_iter_f. }
   omega.
Qed.

Lemma f_eqn_pred k n : k<>0 -> f k n + ((f k)^^k) (pred n) = n.
Proof.
intros.
destruct n.
- simpl. apply fs_k_0.
- now apply f_eqn.
Qed.

Lemma f_S k n : k<>0 -> f k (S n) = S n - Nat.iter k (f k) n.
Proof.
 intros H. generalize (f_eqn n H). omega.
Qed.

Lemma f_pred k n : k<>0 -> f k n = n - Nat.iter k (f k) (pred n).
Proof.
intros H. generalize (f_eqn_pred n H). omega.
Qed.

(* Particular case *)

Lemma f_g n : f 2 n = g n.
Proof.
revert n.
apply g_unique.
- reflexivity.
- intros n. symmetry. now apply f_eqn.
Qed.

Lemma f_1_half n : f 1 (2*n) = n /\ f 1 (S (2*n)) = S n.
Proof.
induction n.
- now compute.
- assert (f 1 (2*(S n)) = S n).
  { rewrite f_pred; auto.
    simpl Nat.iter.
    replace (n + (S (n+0))) with (S (2*n)); omega. }
  split; auto.
  rewrite f_pred; auto.
  simpl Nat.iter.
  replace (S (n + (S (n+0)))) with (2*(S n)); omega.
Qed.

Lemma f_unique k g : k<>0 ->
  g 0 = 0  ->
  (forall n, S n = g (S n)+ (g^^k) n) ->
  forall n, g n = f k n.
Proof.
intros Hk g_0 g_S.
induction n as [[|n] IH] using lt_wf_ind.
- now rewrite g_0, f_k_0.
- assert (forall p m, m <= n -> (g^^p) m = ((f k)^^p) m).
  { induction p.
    - now simpl.
    - intros. simpl.
      rewrite IHp; auto. apply IH.
      rewrite Nat.lt_succ_r. apply le_trans with m; auto.
      eapply Fs_le. eapply Fs_iter_f. }
  rewrite f_S, <- H; auto. specialize (g_S n). omega.
Qed.

Lemma f_step k n : f k (S n) = f k n \/ f k (S n) = S (f k n).
Proof.
destruct k.
- rewrite !f_0_n. now right.
- induction n as [n IH] using lt_wf_ind.
  destruct n.
  + rewrite f_k_0, f_k_1; now right.
  + rewrite f_S; auto.
    rewrite f_S; auto.
    set (fSk := f (S k)) in *.
    assert (forall p m, m <= n ->
             (fSk^^p) (S m) = (fSk^^p) m \/
             (fSk^^p) (S m) = S ((fSk^^p) m)).
    { induction p.
      - simpl; now right.
      - intros; simpl.
        destruct (IHp m H) as [-> | ->].
        + now left.
        + apply IH.
          rewrite Nat.lt_succ_r. apply le_trans with m; auto.
          eapply Fs_le. eapply Fs_iter_f. }
    specialize (H (S k) n). omega.
Qed.

Lemma f_mono_S k n : f k n <= f k (S n).
Proof.
 generalize (f_step k n). omega.
Qed.

Lemma f_mono k n m : n <= m -> f k n <= f k m.
Proof.
induction 1.
- trivial.
- transitivity (f k m); auto using f_mono_S.
Qed.

(** NB : in Coq, for natural numbers, 3-5 = 0 (truncated subtraction) *)

Lemma f_lipschitz k n m : f k m - f k n <= m - n.
Proof.
destruct (le_ge_dec n m) as [H|H].
- induction H; try generalize (f_step k m); omega.
- generalize (f_mono k H). omega.
Qed.

Lemma f_nonzero k n : 0 < n -> 0 < f k n.
Proof.
 unfold lt. intros. rewrite <- (f_k_1 k). now apply f_mono.
Qed.

Lemma f_0_inv k n : f k n = 0 -> n = 0.
Proof.
destruct n; trivial.
assert (0 < f k (S n)) by (apply f_nonzero; auto with arith).
omega.
Qed.

Lemma fs_0_inv p k n : ((f k)^^p) n = 0 -> n = 0.
Proof.
 induction p.
 - now simpl.
 - simpl.
   intros. apply IHp. eapply f_0_inv; eauto.
Qed.

Lemma f_nz k n : n <> 0 -> f k n <> 0.
Proof.
intros H. contradict H. now apply (f_0_inv k).
Qed.

Lemma f_fix k n : f k n = n <-> k = 0 \/ n <= 1.
Proof.
split.
- destruct n; auto.
  destruct k; auto.
  assert (H := @f_eqn (S k) n).
  intros Eq; rewrite Eq in H; clear Eq.
  right.
  assert (H' : ((f (S k))^^(S k)) n = 0) by omega.
  apply fs_0_inv in H'.
  now subst.
- intros [->| ]. apply f_0_n.
  assert (Hn : n=0 \/ n=1) by omega.
  destruct Hn as [-> | ->]; auto using f_k_0, f_k_1.
Qed.

Lemma f_le k n : f k n <= n.
Proof.
 eapply F_le; eauto.
Qed.

Lemma f_lt k n : k<>0 -> 1<n -> f k n < n.
Proof.
intros Hk H.
destruct (le_lt_or_eq _ _ (f_le k n)); trivial.
rewrite f_fix in *. omega.
Qed.
Hint Resolve f_lt.

Lemma f_nonflat k n : f k (S n) = f k n -> f k (S (S n)) = S (f k n).
Proof.
 destruct k.
 - rewrite !f_0_n. omega.
 - intros H.
   assert (Hk : S k <> 0) by omega.
   generalize (f_eqn (S n) Hk) (f_eqn n Hk).
   rewrite !iter_S. rewrite H. omega.
Qed.

Lemma f_nonflat' k n : f k (S n) = f k n -> f k (n-1) = f k n - 1.
Proof.
 destruct n.
 - now rewrite f_k_0, f_k_1.
 - replace (S n - 1) with n by omega.
   intros H.
   destruct (f_step k n) as [H'|H'].
   + apply f_nonflat in H'. omega.
   + omega.
Qed.

Lemma f_SS k n : S (f k n) <= f k (S (S n)).
Proof.
 destruct (f_step k n) as [E|E].
 - generalize (f_nonflat _ _ E). omega.
 - transitivity (f k (S n)). omega. auto using f_mono_S.
Qed.

Lemma f_double_le k n : n <= f k (2*n).
Proof.
induction n.
- trivial.
- replace (2* S n) with (S (S (2*n))) by omega.
  transitivity (S (f k (2*n))). omega. apply f_SS.
Qed.

Lemma f_div2_le k n : n/2 <= f k n.
Proof.
 rewrite <- Nat.div2_div.
 rewrite (Nat.div2_odd n) at 2.
 transitivity (f k (2*Nat.div2 n)).
 apply f_double_le.
 apply f_mono. omega.
Qed.

Lemma f_monok k n :
 k<>0 ->
 f (S k) (f (S k) n) <= f k n <= f (S k) n.
Proof.
 intros Hk.
 induction n as [[|n] IH] using lt_wf_ind.
 - now rewrite !f_k_0.
 - split.
   + admit.
   + rewrite f_S; auto.
     rewrite f_S; auto.
     simpl Nat.iter.
   



(* Pour F1 = moitié sup : arbre binaire
9 10 11 12 13 14 15 16
 5     6     7     8
    3           4
          2
          |
          1

*)


(* pour F3 :
14 15 16 17 18 19
  \/  |  |   \/
  10 11 12   13
   \/   |    |
    7   8    9
     \ /     |
      5      6
       \   /
         4
         3
         2
         1
*)


(* Limite infinie de Fk(n)/n

D(n) = n - D(n-1)

D(n)/n = 1 - [D(n-1)/(n-1)]*(1-1/n)

alpha = 1 - alpha
alpha = 0.5


G n = n - G (G (n-1))

G(n) = 1 - [G (G (n-1))/(G (n-1))]*[G(n-1)/(n-1)]*(n-1)/n
alpha = 1 - alpha*alpha
alpha = 0.618


H(n) = n - H (H (H (n-1)))
alpha = 1 - alpha^3
alpha = 0.682

Pour F4 : alpha = 1 - alpha^4
          alpha = 0.724

*)

End V2.


