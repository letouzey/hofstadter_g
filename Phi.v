(** * Phi : Hofstadter G function and the golden ratio *)

From Coq Require Import Arith Znat Reals Lra Lia R_Ifp R_sqrt Znumtheory.
Require Import MoreReals Fib FunG.

Local Open Scope Z.
Local Open Scope R.

(** We consider again the function [g] defined by
    [g 0 = 0] and [g (S n) = S n - g (g n)],
    and we prove that it can also be directly defined
    via primitives using reals numbers:

    [g(n) = floor((n+1)/phi) = floor(tau*(n+1))]

    where:
     - [phi = (1+sqrt(5))/2]
     - [tau = 1/phi = phi-1 = (sqrt(5)-1)/2]

    In Coq, we'll use here by default operations on reals numbers,
    and also:
     - [INR] : the injection from [nat] to [R] (made implicit via Coercion)
     - [IZR] : the injection from [Z] to [R] (made implicit via Coercion)
     - [Int_part] : the integer part of a real, used as a [floor]
       function. It produces a [Z] integer. The local definition
       [nat_part] chains this [Int_part] with [Z.to_nat] to obtain a [nat].
     - [frac_part] : the faction part of a real, producing a [R]
*)

Local Coercion IZR : Z >-> R.
Local Coercion INR : nat >-> R.

(** * Phi and tau *)

Definition phi := (sqrt 5 + 1)/2.
Definition tau := (sqrt 5 - 1)/2.

Lemma tau_1 : tau + 1 = phi.
Proof.
 unfold tau, phi. field.
Qed.

Lemma tau_phi : tau * phi = 1.
Proof.
unfold tau, phi.
replace ((sqrt 5 - 1)/2 * ((sqrt 5 + 1)/2))
with ((sqrt 5 * sqrt 5 - 1)/4) by field.
rewrite sqrt_def. field. lra.
Qed.

Lemma tau_tau : tau * tau = 1 - tau.
Proof.
 rewrite <- tau_phi, <- tau_1. ring.
Qed.

Lemma tau_nz : tau <> 0.
Proof.
 intro E. generalize tau_phi. rewrite E. intros. lra.
Qed.

Lemma phi_nz : phi <> 0.
Proof.
 intro E. generalize tau_phi. rewrite E. intros. lra.
Qed.

Lemma tau_inv : tau = 1/phi.
Proof.
 rewrite <- tau_phi. field. apply phi_nz.
Qed.

Lemma tau_bound : 6/10 < tau < 7/10.
Proof.
 unfold tau.
 cut (11/5 < sqrt 5 < 12/5). lra.
 rewrite <- (sqrt_Rsqr (11/5)) by lra.
 rewrite <- (sqrt_Rsqr (12/5)) by lra.
 split; apply sqrt_lt_1; unfold Rsqr; lra.
Qed.

(** * A bit of irrationality theory *)

Lemma prime_5 : prime 5.
Proof.
 constructor.
 - lia.
 - intros n Hn. apply Zgcd_1_rel_prime.
   assert (n=1 \/ n=2 \/ n=3 \/ n=4)%Z by lia.
   intuition; now subst.
Qed.

Lemma prime_irr (r:R) :
 (forall (p q:Z), Z.gcd p q = 1%Z -> r * q <> p) ->
 (forall (p q:Z), r * q = p -> q=0%Z).
Proof.
 intros H p q.
 generalize (Z.ggcd_gcd p q) (Z.ggcd_correct_divisors p q)
 (Z.gcd_nonneg p q).
 destruct (Z.ggcd p q) as (g,(p',q')). simpl.
 intros G (Hp,Hq) NN Eq. rewrite <- G in NN.
 subst p; subst q.
 destruct (Z.eq_dec g 0) as [E|N]; [subst; trivial|exfalso].
 apply (H p' q').
 - rewrite Z.gcd_mul_mono_l_nonneg in G by trivial.
   apply Z.mul_reg_l with g; lia.
 - rewrite !mult_IZR in Eq.
   apply Rmult_eq_reg_l with (IZR g). rewrite <- Eq. ring.
   now apply not_0_IZR.
Qed.

Lemma sqrt5_irr (p q:Z) : sqrt 5 * q = p -> q = 0%Z.
Proof.
 apply prime_irr. clear p q. intros p q Hpq Eq.
 assert (Eq' : (p*p = 5 * q*q)%Z).
 { apply eq_IZR; rewrite !mult_IZR, <-!Eq.
   replace (IZR 5) with 5 by (simpl; Rcompute).
   rewrite <- (sqrt_def 5) at 3. ring. lra. }
 assert (Hpp : (5 | p*p)). { exists (q*q)%Z. rewrite Eq'. ring. }
 assert (Hp : (5 | p)).
 { apply prime_mult in Hpp; intuition. apply prime_5. }
 case Hp. intros p' Hp'.
 assert (Hqq : (5 | q*q)).
 { exists (p'*p')%Z. apply Z.mul_reg_l with 5%Z. lia.
   rewrite Z.mul_assoc, <- Eq', !Hp'. ring. }
 assert (Hq : (5 | q)).
 { apply prime_mult in Hqq; intuition. apply prime_5. }
 assert (H : (5 | 1)).
 { rewrite <- Hpq. apply Z.gcd_greatest; auto. }
 destruct H as (x,Hx). lia.
Qed.

Lemma tau_irr (p q:Z) : tau * q = p -> q = 0%Z.
Proof.
 unfold tau.
 intros Eq.
 apply sqrt5_irr with (2*p+q)%Z.
 rewrite plus_IZR, mult_IZR. simpl (IZR 2).
 rewrite <- Eq. field.
Qed.

(** * The main theorem *)

Lemma g_tau (n:nat) : g n = nat_part (tau * S n).
Proof.
induction n as [n IH] using lt_wf_rec.
destruct (eq_nat_dec n 0) as [Hn|Hn].
- subst. change (g 0) with O. simpl.
  replace (tau*1) with tau by ring.
  rewrite (nat_part_carac tau 0); simpl; trivial.
  destruct tau_bound; lra.
- assert (Hn' : 0 < n). { apply (lt_INR 0). lia. }
  set (k:=nat_part (tau*n)).
  set (d:=frac_part (tau*n)).
  replace n with (S (n-1)) at 1 by lia.
  rewrite g_S.
  replace (S (n-1)) with n by lia.
  assert (E : g (n-1) = k).
  { rewrite IH by lia. now replace (S (n-1)) with n by lia. }
  rewrite E.
  assert (LE : (k <= n-1)%nat) by (rewrite <-E; apply g_le).
  clear E.
  apply Nat.add_sub_eq_l.
  rewrite IH by lia.
  assert (Hd : d <> 0).
  { unfold d. contradict Hn.
    generalize (int_frac (tau*n)). rewrite Hn.
    rewrite INR_IZR_INZ at 1. intros Eq.
    apply Nat2Z.inj. simpl.
    apply tau_irr with (Int_part (tau * n)).
    rewrite Eq. ring. }
  assert (Hd' : 0 < d < 1).
  { unfold d. destruct (base_fp (tau*n)) as (Hd1,Hd2).
    unfold d in *. destruct Hd1; intuition. }
  assert (taub := tau_bound).
  assert (tau1 := tau_1).
  assert (Eq : tau*n - d = k).
  { rewrite (nat_frac (tau*n)). fold k d. ring.
    apply Rmult_le_pos; lra. }
  destruct (Rle_or_lt d (1-tau)) as [[LT|EQ]|LT].
  + rewrite (nat_part_carac (tau*(S k)) (n-k)).
    rewrite (nat_part_carac (tau*(S n)) k).
    lia.
    * rewrite S_INR. rewrite Rmult_plus_distr_l.
      rewrite <- Eq. split; lra.
    * rewrite minus_INR, S_INR, <- Eq by lia.
      replace (_ - _) with (tau-(tau+1)*d) by (ring [tau_tau]).
      rewrite tau_1.
      assert (0 <= phi*d <= tau); [split|intuition lra].
      { apply Rmult_le_pos; lra. }
      { replace tau with (phi*(1-tau)).
        apply Rmult_le_compat_l; lra.
        rewrite <- tau_1. ring [tau_tau]. }
  + exfalso.
    rewrite EQ in Eq.
    assert (Z.of_nat n + 1 = 0)%Z.
    { apply tau_irr with (Z.of_nat k + 1)%Z.
      rewrite !plus_IZR, <- !INR_IZR_INZ.
      rewrite Rmult_plus_distr_l. rewrite <- Eq. ring. }
    lia.
  + rewrite (nat_part_carac (tau*(S k)) (n-k-1)).
    rewrite (nat_part_carac (tau*(S n)) (S k)).
    lia.
    * rewrite !S_INR. rewrite Rmult_plus_distr_l.
      rewrite <- Eq. split; lra.
    * rewrite !minus_INR, S_INR, <- Eq by lia.
      simpl INR.
      replace (_ - _) with ((tau+1)*(1-d)) by (ring [tau_tau]).
      split.
      { apply Rmult_le_pos; lra. }
      { rewrite <- tau_phi at 3. rewrite Rmult_comm, tau_1.
        apply Rmult_lt_compat_r; lra. }
Qed.

Lemma g_phi (n:nat) : g n = nat_part ((S n)/phi).
Proof.
 rewrite g_tau. f_equal. rewrite tau_inv. field.
 apply phi_nz.
Qed.
