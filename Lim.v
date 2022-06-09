
From Coq Require Import Arith Reals Lra Lia R_Ifp R_sqrt Ranalysis5.
Require Import GenFib GenG Words.

Open Scope Z.
Open Scope R.

(** * Some limits *)

(* Study of X^(k+1)=X^k+1 : one unique positive root mu(k), in ]1..2].
   For instance : mu(0) = 2
                  mu(1) = 1.618033988749895 (Golden ratio)
                  mu(2) = 1.465571231876768
                  mu(3) = 1.380277569097614
                  mu(4) = 1.324717957244746 (plastic number, root of X^3=X+1)
                  mu(5) = 1.285199033245349

   Dual : positive root tau(k) of X^(k+1)+X-1, in [0.5..1[
    i.e. tau(k) = 1/mu(k)
                  tau(0) = 0.5
                  tau(1) = 0.6180339887498948
                  tau(2) = 0.6823278038280193
                  tau(3) = 0.7244919590005157
                  tau(4) = 0.7548776662466925
                  tau(5) = 0.778089598678601

 *)

Definition mu_spec k : { x : R | 1<=x<=2 /\ x^(S k)-x^k-1=0 }.
Proof.
 set (P := fun x => x^(S k)-x^k-1).
 destruct k.
 - exists 2. lra.
 - apply (IVT_interv P 1 2).
   + intros a Ha. apply derivable_continuous_pt.
     repeat apply derivable_pt_minus.
     * apply derivable_pt_pow.
     * apply derivable_pt_pow.
     * apply derivable_pt_const.
   + lra.
   + unfold P. simpl. lra.
   + unfold P. simpl. generalize (pow_R1_Rle 2 k). lra.
Qed.

Definition mu k : R := proj1_sig (mu_spec k).

Lemma mu_itvl k : 1 < mu k <= 2.
Proof.
 unfold mu. destruct (mu_spec k) as (x & H & E). simpl.
 destruct (Req_dec x 1); try lra. subst. simpl in *. lra.
Qed.

Lemma mu_carac k : (mu k)^(S k) = (mu k)^k+1.
Proof.
 unfold mu. destruct (mu_spec k) as (x & H & E). simpl in *. lra.
Qed.

Definition tau k : R := (*1*) / mu k.

Lemma tau_inv k : mu k = (*1*) / tau k.
Proof.
 unfold tau. rewrite Rinv_involutive; auto.
 generalize (mu_itvl k); lra.
Qed.

Lemma tau_itvl k : 1/2 <= tau k < 1.
Proof.
 unfold tau. generalize (mu_itvl k). intros.
 replace (1/2) with (/2) by lra.
 split.
 - apply Rinv_le_contravar; lra.
 - replace 1 with (/1) by lra.
   apply Rinv_1_lt_contravar; lra.
Qed.

Lemma tau_carac k : (tau k)^(S k) + tau k = 1.
Proof.
 unfold tau.
 assert (MU:=mu_itvl k).
 rewrite <- Rinv_pow by lra.
 assert ((mu k)^(S k)<>0). { apply pow_nonzero. lra. }
 apply Rmult_eq_reg_l with ((mu k)^(S k)); auto.
 rewrite Rmult_1_r, Rmult_plus_distr_l, Rinv_r; auto.
 rewrite mu_carac at 2. simpl. rewrite Rinv_r_simpl_m; lra.
Qed.

Lemma tau_incr k : tau k < tau (S k).
Proof.
 destruct (Rlt_or_le (tau k) (tau (S k))); auto. exfalso.
 assert (E := tau_carac k).
 assert (E' := tau_carac (S k)).
 assert (tau (S k) ^ (S (S k)) < tau k ^(S k)); try lra.
 { apply Rle_lt_trans with (tau k ^(S (S k))).
   - apply pow_incr. generalize (tau_itvl (S k)); lra.
   - remember (S k) as k'. simpl.
     rewrite <- (Rmult_1_l (tau k ^k')) at 2.
     apply Rmult_lt_compat_r.
     * apply pow_lt. generalize (tau_itvl k); lra.
     * generalize (tau_itvl k); lra. }
Qed.

Lemma mu_decr k : mu (S k) < mu k.
Proof.
 rewrite !tau_inv. apply Rinv_lt_contravar. 2:apply tau_incr.
 apply Rmult_lt_0_compat; generalize (tau_itvl k)(tau_itvl (S k)); lra.
Qed.

Definition Ptau k x := x^(S k) + x.

Lemma Ptau_incr k x y :
 0<=x<=1 -> 0<=y<=1 -> x<y -> Ptau k x < Ptau k y.
Proof.
 set (P' := fun x => (INR (S k))*x^k+1).
 assert (D : forall x, derivable_pt_lim (Ptau k) x (P' x)).
 { clear. intros x. apply derivable_pt_lim_plus.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_id. }
 set (DP := fun x => exist _ (P' x) (D x) : derivable_pt (Ptau k) x).
 apply derive_increasing_interv with DP. lra.
 intros t Ht. simpl. unfold P'.
 apply Rplus_le_lt_0_compat. 2:lra.
 apply Rmult_le_pos. apply pos_INR. apply pow_le; lra.
Qed.

Lemma tau_unique k x : 0 <= x -> Ptau k x = 1 -> x = tau k.
Proof.
 intros Hx H.
 assert (x < 1).
 { destruct (Rlt_or_le x 1); auto. exfalso.
   generalize (pow_R1_Rle x (S k)). unfold Ptau in H. lra. }
 assert (I := tau_itvl k).
 assert (E := tau_carac k). change (Ptau k (tau k) = 1) in E.
 destruct (Rtotal_order x (tau k)) as [LT|[EQ|GT]]; auto; exfalso.
 - apply (Ptau_incr k) in LT; lra.
 - apply (Ptau_incr k) in GT; lra.
Qed.

Lemma Ptau_lower k x : 0 <= x -> Ptau k x < 1 -> x < tau k.
Proof.
 intros H H'.
 assert (x < 1).
 { destruct (Rlt_or_le x 1); auto. exfalso.
   generalize (pow_R1_Rle x (S k)). unfold Ptau in H'. lra. }
 destruct (Rtotal_order x (tau k)) as [LT|[EQ|GT]]; auto; exfalso.
 - subst x. unfold Ptau in H'. rewrite tau_carac in H'. lra.
 - apply (Ptau_incr k) in GT; try lra.
   unfold Ptau in GT at 1. rewrite tau_carac in GT. lra.
   generalize (tau_itvl k); lra.
Qed.

Lemma Ptau_upper k x : 0 <= x -> 1 < Ptau k x -> tau k < x.
Proof.
 intros H H'.
 destruct (Rtotal_order x (tau k)) as [LT|[EQ|GT]]; auto; exfalso.
 - apply (Ptau_incr k) in LT; try (generalize (tau_itvl k); lra).
   unfold Ptau in LT at 2. rewrite tau_carac in LT. lra.
 - subst x. unfold Ptau in H'. rewrite tau_carac in H'. lra.
Qed.

Lemma tau_0 : tau 0 = 1/2.
Proof.
 symmetry. apply tau_unique. lra. unfold Ptau. simpl. lra.
Qed.

Lemma tau_1 : tau 1 = (sqrt 5 - 1)/2.
Proof.
 symmetry. apply tau_unique.
 - apply Rle_mult_inv_pos; try lra.
   generalize (sqrt_le_1_alt 1 5). rewrite sqrt_1. lra.
 - unfold Ptau.
   simpl. rewrite Rmult_1_r.
   generalize (Rsqr_sqrt 5). unfold Rsqr. lra.
Qed.

Lemma tau_2 : 0.6823 < tau 2 < 0.6824.
Proof.
 split; [ apply Ptau_lower | apply Ptau_upper ]; unfold Ptau; lra.
Qed.

Lemma tau_3 : 0.7244 < tau 3 < 0.7245.
Proof.
 split; [ apply Ptau_lower | apply Ptau_upper ]; unfold Ptau; lra.
Qed.

Lemma tau_4 : 0.7548 < tau 4 < 0.7549.
Proof.
 split; [ apply Ptau_lower | apply Ptau_upper ]; unfold Ptau; lra.
Qed.

Lemma tau_5 : 0.7780 < tau 5 < 0.7781.
Proof.
 split; [ apply Ptau_lower | apply Ptau_upper ]; unfold Ptau; lra.
Qed.

Lemma mu_0 : mu 0 = 2.
Proof.
 rewrite tau_inv. rewrite tau_0. lra.
Qed.

Lemma mu_1 : mu 1 = (1+sqrt 5)/2.
Proof.
 rewrite tau_inv.
 assert (H := tau_itvl 1).
 apply Rmult_eq_reg_l with (tau 1); try lra.
 rewrite Rinv_r by lra.
 rewrite tau_1.
 generalize (Rsqr_sqrt 5). unfold Rsqr. lra.
Qed.

Lemma mu_2 : 1.465 < mu 2 < 1.466.
Proof.
 rewrite tau_inv.
 assert (H := tau_2).
 destruct tau_2 as (H1,H2).
 apply Rinv_lt_contravar in H1.
 apply Rinv_lt_contravar in H2. lra.
 apply Rmult_lt_0_compat; lra.
 apply Rmult_lt_0_compat; lra.
Qed.

Lemma mu_3 : 1.380 < mu 3 < 1.381.
Proof.
 rewrite tau_inv.
 assert (H := tau_3).
 destruct tau_3 as (H1,H2).
 apply Rinv_lt_contravar in H1.
 apply Rinv_lt_contravar in H2. lra.
 apply Rmult_lt_0_compat; lra.
 apply Rmult_lt_0_compat; lra.
Qed.

Lemma mu_4 : 1.324 < mu 4 < 1.325.
Proof.
 rewrite tau_inv.
 assert (H := tau_4).
 destruct tau_4 as (H1,H2).
 apply Rinv_lt_contravar in H1.
 apply Rinv_lt_contravar in H2. lra.
 apply Rmult_lt_0_compat; lra.
 apply Rmult_lt_0_compat; lra.
Qed.

Lemma mu_5 : 1.285 < mu 5 < 1.286.
Proof.
 rewrite tau_inv.
 assert (H := tau_5).
 destruct tau_5 as (H1,H2).
 apply Rinv_lt_contravar in H1.
 apply Rinv_lt_contravar in H2. lra.
 apply Rmult_lt_0_compat; lra.
 apply Rmult_lt_0_compat; lra.
Qed.


(* A k (S n) / A k n ---> mu(k) *)

Definition Limit (s:nat -> R) (l:R) : Prop :=
  forall eps:R,
    eps > 0 ->
    exists N : nat, forall n:nat, (n >= N)%nat -> R_dist (s n) l < eps.

Lemma A_lim k : Limit (fun n => INR (A k (S n)) / INR (A k n)) (mu k).


A (S n)/A n = 1 + A (n-k)/A n


B(n) = A(n)*tau^n
B(S n) = tau*(tau^n*A(n))+tau^(S k)*tau(n-k)*A(n-k)
       = tau*B(n) + tau^(S k)*B(n-k)
       = tau*B(n) + (1-tau)*B(n-k)

(* f k n / n ---> tau(k) *)

(* For complex numbers and matrices :

http://coquelicot.saclay.inria.fr/
https://www.cs.umd.edu/~rrand/vqc/index.html
https://coqinterval.gitlabpages.inria.fr/

*)

