
From Coq Require Import Arith Reals Lra Lia R_Ifp R_sqrt Ranalysis5.
From Coquelicot Require Import Complex.
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

(*
Lemma lowbound_A k n : (mu k)^n <= INR (A k n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases k n).
 - admit.
 - rewrite A_base by lia. rewrite S_INR.
   (* PAS CLAIR *)


 - simpl; lra.
 - simpl. rewrite plus_INR.
*)


Definition Limit (s:nat -> R) (l:R) : Prop :=
  forall eps:R,
    eps > 0 ->
    exists N : nat, forall n:nat, (n >= N)%nat -> R_dist (s n) l < eps.

(* TODO
Lemma A_lim k : Limit (fun n => INR (A k (S n)) / INR (A k n)) (mu k).
Admitted.

A k n * tau^n --> 1

Ce qui donne A k (S ) / A k n --> 1/tau = mu


A (S n)/A n = 1 + A (n-k)/A n


B(n) = A(n)*tau^n
B(S n) = tau*(tau^n*A(n))+tau^(S k)*tau(n-k)*A(n-k)
       = tau*B(n) + tau^(S k)*B(n-k)
       = tau*B(n) + (1-tau)*B(n-k)

Non, rien de direct...
*)

(* f k n / n ---> tau(k) *)

(* POUR k=2, autres racines, et expression de A 2 n *)

Definition mu2 := mu 2.
Definition tau2 := tau 2.

Definition re_alpha := (1 - mu2)/2.
Definition im_alpha := sqrt (tau2 * (3+tau2))/2.

Definition alpha : C := (re_alpha, im_alpha).
Definition alphabar : C := (re_alpha, - im_alpha).

(* Some complements to Coquelicot *)

Global Arguments Re _%C.
Global Arguments Im _%C.

Module ExtraC.

Local Open Scope C.

Fixpoint Cpow (c : C) n : C :=
 match n with
 | O => 1
 | S n => c * Cpow c n
 end.

Global Arguments Cpow _%C _%nat.
Global Infix "^" := Cpow : C_scope.

Lemma Cpow_1_l n : 1^n = 1.
Proof.
 induction n; simpl; auto. rewrite IHn. ring.
Qed.

Lemma Cpow_add c n m : c^(n+m) = c^n*c^m.
Proof.
 induction n; simpl. now rewrite Cmult_1_l. rewrite IHn. ring.
Qed.

Lemma Cpow_mult_l a b n : (a*b)^n = a^n * b^n.
Proof.
 induction n; simpl. ring. rewrite IHn. ring.
Qed.

Lemma Cpow_mult_r c n m : c^(n*m) = (c^n)^m.
Proof.
 induction n; simpl. now rewrite Cpow_1_l.
 now rewrite !Cpow_add, IHn, Cpow_mult_l.
Qed.

Lemma Cmod2_alt (c:C) : ((Cmod c)^2 = (Re c)^2 + (Im c)^2)%R.
Proof.
 unfold Cmod.
 rewrite pow2_sqrt. trivial.
 generalize (pow2_ge_0 (fst c)) (pow2_ge_0 (snd c)); lra.
Qed.

Lemma Cmod2_conj (c:C) : RtoC (Cmod c ^2) = c * Cconj c.
Proof.
 rewrite Cmod2_alt.
 destruct c as (x,y). unfold Cconj, Cmult, RtoC. simpl. f_equal; lra.
Qed.

Lemma re_alt (c:C) : RtoC (Re c) = (c + Cconj c)/2.
Proof.
 destruct c as (x,y).
 unfold Cconj, RtoC, Cplus, Cdiv, Cmult. simpl. f_equal; field.
Qed.

Lemma im_alt (c:C) : RtoC (Im c) = (c - Cconj c)/(2*Ci).
Proof.
 destruct c as (x,y).
 unfold Cconj, RtoC, Ci, Cminus, Cplus, Cdiv, Cmult. simpl. f_equal; field.
Qed.

Lemma re_plus a b : (Re (a+b) = Re a + Re b)%R.
Proof.
 now destruct a as (xa,ya), b as (xb,yb).
Qed.

Lemma im_plus a b : (Im (a+b) = Im a + Im b)%R.
Proof.
 now destruct a as (xa,ya), b as (xb,yb).
Qed.

Lemma re_scal (r:R)(c:C) : (Re (r*c) = r * Re c)%R.
Proof.
 destruct c as (x,y); simpl. lra.
Qed.

Lemma re_scal_r (c:C)(r:R) : (Re (c*r) = Re c * r)%R.
Proof.
 destruct c as (x,y); simpl. lra.
Qed.

Lemma conj_conj (c:C) : Cconj (Cconj c) = c.
Proof.
 unfold Cconj. simpl. destruct c; simpl; f_equal; lra.
Qed.

Lemma plus_conj a b : Cconj (a+b) = Cconj a + Cconj b.
Proof.
 destruct a as (xa,ya), b as (xb,yb). unfold Cplus, Cconj. simpl.
 f_equal. lra.
Qed.

Lemma mult_conj a b : Cconj (a*b) = Cconj a * Cconj b.
Proof.
 destruct a as (xa,ya), b as (xb,yb). unfold Cmult, Cconj. simpl.
 f_equal; lra.
Qed.

Lemma opp_conj a : Cconj (-a) = - Cconj a.
Proof.
 reflexivity.
Qed.

Lemma minus_conj a b : Cconj (a-b) = Cconj a - Cconj b.
Proof.
 apply plus_conj.
Qed.

Lemma inv_conj (a:C) : a<>0 -> Cconj (/a) = /Cconj a.
Proof.
 intros H.
 assert (H' := H). rewrite Cmod_gt_0 in H'.
 rewrite <- sqrt_0 in H'. apply sqrt_lt_0_alt in H'.
 destruct a as (xa,ya). simpl in *. unfold Cinv, Cconj. simpl.
 f_equal; field_simplify; trivial; lra.
Qed.

Lemma div_conj (a b : C) : b<>0 -> Cconj (a/b) = Cconj a / Cconj b.
Proof.
 intros H. unfold Cdiv. now rewrite mult_conj, inv_conj.
Qed.

Lemma pow_conj a n : Cconj (a^n) = (Cconj a)^n.
Proof.
 induction n; simpl. compute; f_equal; lra. rewrite mult_conj. now f_equal.
Qed.

Lemma mod_conj (c:C) : Cmod (Cconj c) = Cmod c.
Proof.
 unfold Cmod. destruct c as (x,y); simpl. f_equal. lra.
Qed.

Lemma RtoC_pow (a:R)(n:nat) : RtoC (a^n) = (RtoC a)^n.
Proof.
 induction n; simpl; auto. rewrite RtoC_mult. now f_equal.
Qed.

End ExtraC.
Import ExtraC.
Global Arguments Cpow _%C _%nat.
Global Infix "^" := Cpow : C_scope.

Lemma re_alpha_alt : re_alpha = - tau2 ^ 2 / 2.
Proof.
 unfold re_alpha. f_equal.
 unfold mu2. rewrite tau_inv. fold tau2.
 assert (tau2 <> 0) by (unfold tau2; generalize tau_2; lra).
 apply Rmult_eq_reg_l with (tau2); trivial.
 field_simplify; trivial.
 generalize (tau_carac 2); fold tau2; lra.
Qed.

Lemma im_alpha_2 : im_alpha ^ 2 = tau2 * (3+tau2) / 4.
Proof.
 unfold im_alpha.
 unfold Rdiv.
 rewrite Rpow_mult_distr, pow2_sqrt; try lra.
 apply Rmult_le_pos; generalize (tau_2); fold tau2; lra.
Qed.

Lemma alphamod : (Cmod alpha)^2 = tau2.
Proof.
 unfold Cmod.
 rewrite pow2_sqrt.
 2: generalize (pow2_ge_0 (fst alpha)) (pow2_ge_0 (snd alpha)); lra.
 unfold alpha; simpl. ring_simplify.
 rewrite im_alpha_2. rewrite re_alpha_alt.
 field_simplify.
 assert ((tau2)^3 = 1 - tau2) by (generalize (tau_carac 2); fold tau2; lra).
 replace ((tau2)^4) with ((tau2)^3 * tau2) by field.
 rewrite H.
 field_simplify. lra.
Qed.

Lemma mu_is_Croot : (mu2 ^3 = mu2 ^2 + 1)%C.
Proof.
 rewrite <- !RtoC_pow, <- RtoC_plus. unfold mu2. now rewrite (mu_carac 2).
Qed.

Lemma alpha_is_root : (alpha^3 = alpha^2 + 1)%C.
Proof.
 simpl. rewrite !Cmult_1_r. unfold alpha. unfold Cmult; simpl.
 unfold Cplus; simpl. f_equal; ring_simplify.
 - apply Rminus_diag_uniq.
   rewrite im_alpha_2, re_alpha_alt.
   unfold Rdiv. rewrite !Rpow_mult_distr.
   field_simplify.
   assert ((tau2)^3 = 1 - tau2) by (generalize (tau_carac 2); fold tau2; lra).
   replace ((tau2)^6) with (((tau2)^3)^2) by field.
   replace ((tau2)^4) with ((tau2)^3 * tau2) by field.
   rewrite H.
   lra.
 - replace (im_alpha ^ 3) with (im_alpha^2 * im_alpha) by ring.
   cut ((3* re_alpha^2 - im_alpha^2)*im_alpha = (2 * re_alpha)*im_alpha);
    try lra.
   f_equal.
   rewrite im_alpha_2. rewrite re_alpha_alt.
   field_simplify.
   assert ((tau2)^3 = 1 - tau2) by (generalize (tau_carac 2); fold tau2; lra).
   replace ((tau2)^4) with ((tau2)^3 * tau2) by field.
   rewrite H.
   lra.
Qed.

Lemma alphabar_is_root : (alphabar^3 = alphabar^2 + 1)%C.
Proof.
 change alphabar with (Cconj alpha).
 rewrite <- !pow_conj. rewrite alpha_is_root.
 rewrite plus_conj. f_equal. compute; f_equal; lra.
Qed.

Lemma re_alpha_nz : re_alpha <> 0.
Proof.
 unfold re_alpha, mu2. generalize mu_2. lra.
Qed.

Lemma im_alpha_nz : im_alpha <> 0.
Proof.
 assert (LT : 0 < im_alpha ^2).
 { rewrite im_alpha_2. unfold Rdiv.
   repeat apply Rmult_lt_0_compat; unfold tau2; generalize tau_2; lra. }
 apply sqrt_lt_R0 in LT. rewrite sqrt_pow2 in LT.
 lra.
 unfold im_alpha. apply Rle_mult_inv_pos; try lra. apply sqrt_pos.
Qed.

Lemma distinct_roots :
  RtoC mu2 <> alpha /\ RtoC mu2 <> alphabar /\ alpha <> alphabar.
Proof.
 unfold alpha, alphabar, RtoC; repeat split.
 - intros [= A B]. now destruct im_alpha_nz.
 - intros [= A B]. generalize im_alpha_nz. lra.
 - intros [= B]. generalize im_alpha_nz. lra.
Qed.

Definition coef_alpha : C :=
 ((3-mu2^2+(alphabar+mu2)*(mu2-2))/(alpha-mu2)/(alpha-alphabar))%C.

Definition coef_mu : R := 1 - 2 * Re coef_alpha.

Lemma coefs_eqn1 : coef_mu + 2 * Re coef_alpha = 1.
Proof.
 unfold coef_mu. lra.
Qed.

Lemma coefs_eqn2 : coef_mu * mu2 + 2 * Re (coef_alpha * alpha) = 2.
Proof.
 unfold coef_mu. unfold Rminus.
 rewrite Rmult_plus_distr_r, Rmult_1_l.
 rewrite <- Ropp_mult_distr_l, Rmult_assoc.
 rewrite !Ropp_mult_distr_r. rewrite <- re_scal_r.
 rewrite Rplus_assoc, <- Rmult_plus_distr_l, <- re_plus.
 rewrite <- Cmult_plus_distr_l.
 rewrite Cplus_comm, RtoC_opp. fold (Cminus alpha mu2).
 unfold coef_alpha.

(*
Re (1/(alpha-alphabar) * (3-mu^2+(alphabar+mu)*(mu-2)))

= Re (1/(2*Ci*Im alpha) * (3-mu^2+mu*(mu-2)+ alphabar*(mu-2)))
= Re (-Ci/(2*Im alpha) * ((3-mu^2+mu*(mu-2) + re_alpha*(mu-2))%R + Ci * im_alpha*(mu-2))
= (mu-2)*im_alpha/(2*im_alpha)
= (mu-2)/2
L'opposé de ce qu'il faut ?!
*)

Admitted.

Lemma coefs_eqn3 : coef_mu * mu2 ^2 + 2 * Re (coef_alpha * alpha ^2)%C = 3.
Proof.
 unfold coef_mu. unfold Rminus.
 rewrite Rmult_plus_distr_r, Rmult_1_l.
 rewrite <- Ropp_mult_distr_l, Rmult_assoc.
 rewrite !Ropp_mult_distr_r. rewrite <- re_scal_r.
 rewrite Rplus_assoc, <- Rmult_plus_distr_l, <- re_plus.
 rewrite <- Cmult_plus_distr_l.
 rewrite Cplus_comm, RtoC_opp, RtoC_pow. fold (Cminus (alpha^2) (mu2^2))%C.
 unfold coef_alpha.

(*
Re ((alpha+mu)/(alpha-alphabar) * (3-mu^2+(alphabar+mu)*(mu-2)))

= Re (1/(2*Ci*Im alpha) * (alpha+mu)*(3-mu^2+(alphabar+mu)*(mu-2)))

= -1/(2*Im alpha) * Im ((alpha+mu)*(3-mu^2+(alphabar+mu)*(mu-2)))
= -1/(2*Im alpha) * [ (mu+re_alpha)*Im (...) + im_alpha* Re (...) ]
= -1/(2*Im alpha) * [ (mu+re_alpha)*im_alpha*(mu-2)
                      + im_alpha* (3-mu^2+(re_alpha+mu)*(mu-2) ]
= -1/2 * [ (mu+re_alpha)*(mu-2) + 3-mu^2 + (mu+re_alpha)*(mu-2) ]

Encore quelques inversions ?!
*)
Admitted.

Lemma A2_eqn n :
 INR (A 2 n) = coef_mu * mu2 ^n + 2 * Re (coef_alpha * alpha^n)%C.
Proof.
 induction n as [n IH] using lt_wf_ind.
 destruct n.
 - simpl A. simpl pow. simpl Cpow. rewrite Cmult_1_r.
   change (INR 1) with 1. generalize coefs_eqn1. lra.
 - simpl A.
   destruct (Nat.le_gt_cases n 1).
   + destruct n.
     * simpl A. change (INR (1+1)) with 2. generalize coefs_eqn2.
       simpl Cpow. rewrite Cmult_1_r. lra.
     * replace n with O by lia. simpl A.
       replace (INR (2+1)) with 3 by (compute; lra).
       generalize coefs_eqn3. lra.
   + replace (S n) with (3+(n-2))%nat by lia.
     rewrite pow_add. unfold mu2. rewrite (mu_carac 2). fold mu2.
     rewrite Cpow_add. rewrite alpha_is_root.
     rewrite plus_INR.
     rewrite (IH n) by lia. rewrite (IH (n-2)%nat) by lia.
     rewrite Cmult_plus_distr_r, Cmult_plus_distr_l, re_plus.
     ring_simplify. rewrite Rmult_assoc, <-pow_add.
     replace (n-2+2)%nat with n by lia.
     rewrite <-Cpow_add.
     replace (2+(n-2))%nat with n by lia.
     rewrite Cmult_1_l. lra.
Qed.


(* Puis limites (A2 n / mu2^n) = coef_mu
             et (A2 (S n) / A2 n) = mu2 *)


(* For complex numbers and matrices :

http://coquelicot.saclay.inria.fr/
https://www.cs.umd.edu/~rrand/vqc/index.html
https://coqinterval.gitlabpages.inria.fr/
https://github.com/coqtail/coqtail
https://github.com/Sobernard/Lindemann

Finalement, dans opam switch default, qui contenait deja un coq 8.14.1 :

opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-coquelicot


Pour k=2, racines secondaires complexes connues:
  alpha,alphabar = (1/2)*(-tau^2 +/- i.sqrt(tau).sqrt(3+tau))
  ce qui redonne |alpha|^2 = tau
  Trois racines distinctes mu, alpha, alphabar pour X^3-X^2-1
  donc factorisation complete donc pas d'autres racines

Pour k=3, racines complexes connues en fonction des racines réelles

Pour k=4, racines complexes : j et bar(j) connus, et ensuite
  alpha et bar(alpha) connus en fonction de tau.



*)

