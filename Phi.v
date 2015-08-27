(** * Phi : Hofstadter G function and the golden ratio *)

Require Import Arith Fourier R_Ifp R_sqrt Znumtheory.
Require Import Fib FibTree.

Open Scope R.

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
     - [INR] : the injection from [nat] to [R]
     - [IZR] : the injection from [Z] to [R]
     - [Int_part] : the integer part of a real, used as a [floor]
       function. It produces a [Z] integer, that we can convert
       to [nat] via [Z.to_nat] when necessary.
     - [frac_part] : the faction part of a real, producing a [R]
*)

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
rewrite sqrt_def. field. fourier.
Qed.

Lemma tau_tau : tau * tau = 1 - tau.
Proof.
 rewrite <- tau_phi, <- tau_1. ring.
Qed.

Lemma tau_nz : tau <> 0.
Proof.
 intro E. generalize tau_phi. rewrite E. intros. fourier.
Qed.

Lemma phi_nz : phi <> 0.
Proof.
 intro E. generalize tau_phi. rewrite E. intros. fourier.
Qed.

Lemma tau_inv : tau = 1/phi.
Proof.
 rewrite <- tau_phi. field. apply phi_nz.
Qed.

Lemma tau_bound : 6/10 < tau < 7/10.
Proof.
 unfold tau.
 assert (11/5 < sqrt 5).
 { replace (11/5) with (sqrt ((11/5)*(11/5))).
   apply sqrt_lt_1; fourier.
   apply sqrt_Rsqr. fourier. }
 assert (sqrt 5 < 12/5).
 { replace (12/5) with (sqrt ((12/5)*(12/5))).
   apply sqrt_lt_1; fourier.
   apply sqrt_Rsqr. fourier. }
 split.
 - apply Rmult_lt_reg_l with 2. fourier.
   apply Rplus_lt_reg_r with 1.
   field_simplify. fourier.
 - apply Rmult_lt_reg_l with 2. fourier.
   apply Rplus_lt_reg_r with 1.
   field_simplify. fourier.
Qed.

(** * A bit of irrationality theory *)

Lemma prime_5 : prime 5.
Proof.
 constructor.
 - omega.
 - intros n Hn. apply Zgcd_1_rel_prime.
   assert (n=1 \/ n=2 \/ n=3 \/ n=4)%Z by omega.
   intuition; now subst.
Qed.

Lemma prime_irr (r:R) :
 (forall (p q:Z), Z.gcd p q = 1%Z -> r * IZR q <> IZR p) ->
 (forall (p q:Z), r * IZR q = IZR p -> q=0%Z).
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
   apply Z.mul_reg_l with g; omega.
 - rewrite !mult_IZR in Eq.
   apply Rmult_eq_reg_l with (IZR g). rewrite <- Eq. ring.
   now apply not_0_IZR.
Qed.

Lemma sqrt5_irr (p q:Z) : sqrt 5 * IZR q = IZR p -> q = 0%Z.
Proof.
 apply prime_irr. clear p q. intros p q Hpq Eq.
 assert (Eq' : (p*p = 5 * q*q)%Z).
 { apply eq_IZR; rewrite !mult_IZR, <-!Eq.
   replace (IZR 5) with 5 by (simpl; Rcompute).
   rewrite <- (sqrt_def 5) at 3. ring. fourier. }
 assert (Hpp : (5 | p*p)). { exists (q*q)%Z. rewrite Eq'. ring. }
 assert (Hp : (5 | p)).
 { apply prime_mult in Hpp; intuition. apply prime_5. }
 case Hp. intros p' Hp'.
 assert (Hqq : (5 | q*q)).
 { exists (p'*p')%Z. apply Z.mul_reg_l with 5%Z. omega.
   rewrite Z.mul_assoc, <- Eq', !Hp'. ring. }
 assert (Hq : (5 | q)).
 { apply prime_mult in Hqq; intuition. apply prime_5. }
 assert (H : (5 | 1)).
 { rewrite <- Hpq. apply Z.gcd_greatest; auto. }
 destruct H as (x,Hx). omega.
Qed.

Lemma tau_irr (p q:Z) : tau * IZR q = IZR p -> q = 0%Z.
Proof.
 unfold tau.
 intros Eq.
 apply sqrt5_irr with (2*p+q)%Z.
 rewrite plus_IZR, mult_IZR. simpl (IZR 2).
 rewrite <- Eq. field.
Qed.

(** * Some complements about integer part and fractional part *)

Lemma int_part_iff (r:R)(k:Z) :
 0 <= r-IZR k < 1 <-> Int_part r = k.
Proof.
 split.
 - unfold Int_part.
   intros (H1,H2).
   assert (k+1 = up r)%Z; [|omega].
   apply tech_up; rewrite plus_IZR; simpl; fourier.
 - intros <-. destruct (base_Int_part r). split; fourier.
Qed.

Lemma int_part_carac (r:R)(k:Z) :
 0 <= r-IZR k < 1 -> Int_part r = k.
Proof.
 apply int_part_iff.
Qed.

Lemma int_frac r : r = IZR (Int_part r) + frac_part r.
Proof.
 unfold frac_part. ring.
Qed.

Lemma int_part_le (r:R)(k:Z) : IZR k <= r <-> (k <= Int_part r)%Z.
Proof.
 split.
 - intros.
   destruct (base_Int_part r).
   assert (E : IZR k - 1 < IZR (Int_part r)) by fourier.
   change 1 with (IZR 1) in E.
   rewrite <- minus_IZR in E.
   apply lt_IZR in E. omega.
 - destruct (base_Int_part r).
   intros LE. apply IZR_le in LE. fourier.
Qed.

(** * The main theorem *)

Lemma g_tau (n:nat) : g n = Z.to_nat (Int_part (tau * INR (S n))).
Proof.
induction n as [n IH] using lt_wf_rec.
destruct (eq_nat_dec n 0) as [Hn|Hn].
- subst. change (g 0) with O. simpl.
  replace (tau*1) with tau by ring.
  rewrite (int_part_carac tau 0); simpl; trivial.
  destruct tau_bound; split; fourier.
- assert (0 < INR n). { apply (lt_INR 0). omega. }
  assert (0 <= Int_part (tau * INR n))%Z.
  { apply int_part_le. simpl. destruct tau_bound.
    apply Rmult_le_pos; fourier. }
  set (k:=Z.to_nat (Int_part (tau*INR n))).
  set (d:=frac_part (tau*INR n)).
  replace n with (S (n-1)) at 1 by omega.
  rewrite g_S.
  replace (S (n-1)) with n by omega.
  assert (E : g (n-1) = k).
  { rewrite IH by omega. now replace (S (n-1)) with n by omega. }
  rewrite E.
  assert (k <= n-1)%nat by (rewrite <-E; apply g_le).
  assert (g k < n)%nat by (generalize (g_le k); omega).
  symmetry. apply plus_minus.
  rewrite IH by omega.
  assert (Hd : d <> 0).
  { unfold d. contradict Hn.
    generalize (int_frac (tau*INR n)). rewrite Hn.
    rewrite INR_IZR_INZ at 1. intros Eq.
    apply Nat2Z.inj. simpl.
    apply tau_irr with (Int_part (tau * INR n)).
    rewrite Eq. ring. }
  assert (Hd' : 0 < d < 1).
  { unfold d. destruct (base_fp (tau*INR n)) as (Hd1,Hd2).
    unfold d in *. destruct Hd1; intuition. }
  destruct Hd' as (Hd1,Hd2).
  destruct tau_bound.
  generalize tau_1; intro.
  assert (Eq : INR k = tau*INR n - d).
  { unfold d, k. revert H0. generalize (tau * INR n). clear.
    intros r Hr. rewrite INR_IZR_INZ. rewrite Z2Nat.id; auto.
    rewrite (int_frac r) at 2. ring. }
  destruct (Rle_or_lt d (1-tau)) as [[LT|EQ]|LT].
  + rewrite (int_part_carac (tau*INR(S k)) (Z.of_nat (n-k))).
    rewrite (int_part_carac (tau*INR(S n)) (Z.of_nat k)).
    rewrite !Nat2Z.id. omega.
    * rewrite <- INR_IZR_INZ.
      rewrite S_INR. rewrite Rmult_plus_distr_l.
      rewrite Eq. split; fourier.
    * rewrite <- INR_IZR_INZ, minus_INR, S_INR, Eq by omega.
      replace (_ - _) with (tau-(tau+1)*d) by (ring [tau_tau]).
      rewrite tau_1.
      assert (0 <= phi*d <= tau); [split|intuition fourier].
      { apply Rmult_le_pos; fourier. }
      { replace tau with (phi*(1-tau)).
        apply Rmult_le_compat_l; fourier.
        rewrite <- tau_1. ring [tau_tau]. }
  + rewrite EQ in Eq.
    assert (Z.of_nat n + 1 = 0)%Z.
    apply tau_irr with (Z.of_nat k + 1)%Z.
    rewrite !plus_IZR. simpl.
    rewrite <- !INR_IZR_INZ.
    rewrite Rmult_plus_distr_l. rewrite Eq. ring.
    omega.
  + rewrite (int_part_carac (tau*INR(S k)) (Z.of_nat (n-k-1))).
    rewrite (int_part_carac (tau*INR(S n)) (Z.of_nat (S k))).
    rewrite !Nat2Z.id. omega.
    * rewrite <- INR_IZR_INZ.
      rewrite !S_INR. rewrite Rmult_plus_distr_l.
      rewrite Eq. split; fourier.
    * rewrite <- INR_IZR_INZ, !minus_INR, S_INR, Eq by omega.
      simpl INR.
      replace (_ - _) with ((tau+1)*(1-d)) by (ring [tau_tau]).
      split.
      { apply Rmult_le_pos; fourier. }
      { rewrite <- tau_phi at 3. rewrite Rmult_comm, tau_1.
        apply Rmult_lt_compat_r; fourier. }
Qed.

Lemma g_phi (n:nat) : g n = Z.to_nat (Int_part (INR (S n)/phi)).
Proof.
 rewrite g_tau. do 2 f_equal. rewrite tau_inv. field.
 apply phi_nz.
Qed.
