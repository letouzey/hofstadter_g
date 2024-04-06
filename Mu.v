From Coq Require Import Lia Reals Lra Ranalysis5 QArith Qcanon.
Require Import MoreReals MoreLim.

Local Open Scope R.
Local Coercion INR : nat >-> R.

(** * Real roots of polynom [X^(k+1)-X^k-1] *)

(** Study of [X^(k+1)=X^k+1] : one unique positive root mu(k), in ]1..2].
    For instance :

     - mu(0) = 2
     - mu(1) = 1.618033988749895.. (Golden ratio)
     - mu(2) = 1.465571231876768..
     - mu(3) = 1.380277569097614..
     - mu(4) = 1.324717957244746.. (plastic number, root of X^3=X+1)
     - mu(5) = 1.285199033245349..

    Dual : positive root tau(k) of X^(k+1)+X-1, in [0.5..1[
    i.e. tau(k) = 1/mu(k)

     - tau(0) = 0.5
     - tau(1) = 0.6180339887498948..
     - tau(2) = 0.6823278038280193..
     - tau(3) = 0.7244919590005157..
     - tau(4) = 0.7548776662466925..
     - tau(5) = 0.7780895986786012..
*)

Definition P (k:nat) (x:R) : R := x^(S k)-x^k-1.

Lemma P_root_equiv k x : P k x = 0 <-> x^(S k) = x^k+1.
Proof.
 unfold P. lra.
Qed.

Lemma P_root_equiv' k x : P k x = 0 <-> x^(k+1) = x^k+1.
Proof.
 rewrite Nat.add_1_r. apply P_root_equiv.
Qed.

Definition mu_spec k : { x : R | 1<=x<=2 /\ P k x = 0 }.
Proof.
 destruct k.
 - exists 2. unfold P. lra.
 - apply (IVT_interv (P (S k)) 1 2).
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
 destruct (Req_dec x 1); try lra. subst. unfold P in *. simpl in *; lra.
Qed.

Lemma mu_root k : P k (mu k) = 0.
Proof.
 unfold mu. destruct (mu_spec k) as (x & H & E). simpl in *. lra.
Qed.

Lemma mu_carac k : (mu k)^(S k) = (mu k)^k+1.
Proof.
 rewrite <- P_root_equiv. apply mu_root.
Qed.

Definition tau k : R := (*1*) / mu k.

Lemma tau_inv k : mu k = (*1*) / tau k.
Proof.
 unfold tau. now rewrite Rinv_inv.
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
 rewrite pow_inv.
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
   - remember (S k) as k'. simpl. generalize (tau_itvl k); nra. }
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
 set (P' := fun x => (S k)*x^k+1).
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

Lemma mu_unique k x : 0 <= x -> x^(S k)=x^k+1 -> x = mu k.
Proof.
 intros Hx H.
 assert (x <> 0).
 { destruct k. simpl in *. lra.
   intros ->. rewrite !pow_i in H; lra || lia. }
 assert (E : 1/x = tau k).
 { apply tau_unique.
   - apply Rle_mult_inv_pos; lra.
   - unfold Ptau. unfold Rdiv. rewrite Rmult_1_l, pow_inv.
     assert (0 < x ^ S k) by (apply pow_lt; lra).
     apply Rmult_eq_reg_l with (x^(S k)); try lra.
     field_simplify; try lra.
     rewrite Rdiv_plus_distr. simpl. field_simplify; try lra.
     now rewrite <- H. }
 rewrite tau_inv. rewrite <- E. unfold Rdiv. now rewrite Rmult_1_l, Rinv_inv.
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

Lemma tau_2 : 0.6823278038280 < tau 2 < 0.6823278038281.
Proof.
 split; [ apply Ptau_lower | apply Ptau_upper ]; unfold Ptau; lra.
Qed.

Lemma tau_3 : 0.7244919590005 < tau 3 < 0.7244919590006.
Proof.
 split; [ apply Ptau_lower | apply Ptau_upper ]; unfold Ptau; lra.
Qed.

Lemma tau_4 : 0.7548776662466 < tau 4 < 0.7548776662467.
Proof.
 split; [ apply Ptau_lower | apply Ptau_upper ]; unfold Ptau; lra.
Qed.

Lemma tau_5 : 0.7780895986786 < tau 5 < 0.7780895986787.
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

Lemma mu_2 : 1.465571231876 < mu 2 < 1.465571231877.
Proof.
 rewrite tau_inv.
 assert (H := tau_2).
 destruct tau_2 as (H1,H2). apply Rinv_lt_contravar in H1,H2; lra.
Qed.

Lemma mu_3 : 1.380277569097 < mu 3 < 1.380277569098.
Proof.
 rewrite tau_inv.
 assert (H := tau_3).
 destruct tau_3 as (H1,H2). apply Rinv_lt_contravar in H1,H2; lra.
Qed.

Lemma mu_4 : 1.324717957244 < mu 4 < 1.324717957245.
Proof.
 rewrite tau_inv.
 assert (H := tau_4).
 destruct tau_4 as (H1,H2). apply Rinv_lt_contravar in H1,H2; lra.
Qed.

Lemma mu_5 : 1.285199033245 < mu 5 < 1.286199033246.
Proof.
 rewrite tau_inv.
 assert (H := tau_5).
 destruct tau_5 as (H1,H2). apply Rinv_lt_contravar in H1,H2; lra.
Qed.

(** When k is odd, there is also a real negative root to X^(k+1)-X^k-1.
    nu(1) = -0.618033988749895.. = 1-phi
    nu(3) = -0.8191725133961643..
    nu(5) = -0.8812714616335695..
 *)

Lemma minushalf_no_root k : P k (-0.5) < 0.
Proof.
 unfold P. replace (-0.5) with (-1*/2) by lra. simpl.
 rewrite !Rpow_mult_distr.
 destruct (Nat.Even_Odd_dec k) as [EV|OD].
 - rewrite minusone_pow_even by trivial. field_simplify.
   assert (0<(/2)^k) by ( apply pow_lt; lra). lra.
 - rewrite minusone_pow_odd by trivial. apply Ropp_lt_cancel.
   field_simplify. apply Rlt_mult_inv_pos; try lra.
   assert ((/2)^k <= /2); try lra.
   { rewrite pow_inv.
     apply Rinv_le_contravar. lra.
     destruct OD as (k' & ->). rewrite Nat.add_1_r. simpl.
     generalize (pow_R1_Rle 2 (k'+(k'+0))). lra. }
Qed.

Definition nu_spec k :
  Nat.Odd k -> { x : R | -1<=x<=-0.5 /\ P k x = 0 }.
Proof.
 intros Hk.
 apply (IVT_interv_decr (P k) (-1) (-0.5)).
   + intros a Ha. apply derivable_continuous_pt.
     repeat apply derivable_pt_minus.
     * apply derivable_pt_pow.
     * apply derivable_pt_pow.
     * apply derivable_pt_const.
   + lra.
   + unfold P. simpl. rewrite minusone_pow_odd by trivial. lra.
   + apply minushalf_no_root.
Qed.

Definition nu k : R :=
 match Nat.Even_Odd_dec k with
 | left _ => 0 (* arbitrary value, not a root *)
 | right ODD => proj1_sig (nu_spec k ODD)
 end.

Lemma nu_itvl k : Nat.Odd k -> -1 < nu k < -0.5.
Proof.
 intros ODD. unfold nu. destruct (Nat.Even_Odd_dec k) as [EV|OD].
 - destruct (Nat.Even_Odd_False k EV ODD).
 - destruct (nu_spec k OD) as (x & H & E). simpl.
   destruct (Req_dec x (-1)).
   { subst. unfold P in *; simpl in *.
     rewrite minusone_pow_odd in *; trivial; lra. }
   destruct (Req_dec x (-0.5)).
   { subst. generalize (minushalf_no_root k). lra. }
   lra.
Qed.

Lemma nu_root k : Nat.Odd k -> P k (nu k) = 0.
Proof.
 intros ODD. unfold nu. destruct (Nat.Even_Odd_dec k) as [EV|OD].
 - destruct (Nat.Even_Odd_False k EV ODD).
 - destruct (nu_spec k OD) as (x & H & E). simpl in *. trivial.
Qed.

Lemma nu_carac k : Nat.Odd k -> (nu k)^(S k) = (nu k)^k+1.
Proof.
 intros. rewrite <- P_root_equiv. now apply nu_root.
Qed.

(* Uniqueness of the negative root (if it exists) *)

Lemma P_odd_neg_decr k x y :
 Nat.Odd k -> x<y<=0 -> P k y < P k x.
Proof.
 intros Hk.
 set (P' := fun x => (S k)*x^k-k*x^(pred k)-0).
 assert (D : forall x, derivable_pt_lim (P k) x (P' x)).
 { clear. intros x. repeat apply derivable_pt_lim_minus.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_const. }
 set (DP := fun x => exist _ (P' x) (D x) : derivable_pt (P k) x).
 intros Hxy.
 apply (derive_decreasing_interv x y) with DP; try lra.
 intros t Ht. simpl. unfold P'. ring_simplify.
 replace k with (S (pred k)) at 2 by (destruct Hk as (k',->); lia).
 rewrite <- tech_pow_Rmult.
 apply Ropp_lt_cancel. rewrite Ropp_0.
 replace (-_) with (t^pred k * (S k * (-t) + k)) by lra.
 apply Rmult_lt_0_compat.
 - apply pow_even_pos; try lra.
   destruct Hk as (k', ->). rewrite Nat.add_1_r. now exists k'.
 - apply Rplus_lt_0_compat; try apply Rmult_lt_0_compat; try lra.
   apply RSpos.
   destruct Hk as (k', ->). rewrite Nat.add_1_r. apply RSpos.
Qed.

Lemma P_even_neg_decr k x y :
 Nat.Even k -> x<y<=0 -> P k x < P k y.
Proof.
 intros Hk Hxy.
 destruct (Nat.eq_dec k 0) as [->|NZ]. { unfold P. simpl. lra. }
 set (P' := fun x => (S k)*x^k-k*x^(pred k)-0).
 assert (D : forall x, derivable_pt_lim (P k) x (P' x)).
 { clear. intros x. repeat apply derivable_pt_lim_minus.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_const. }
 set (DP := fun x => exist _ (P' x) (D x) : derivable_pt (P k) x).
 apply (derive_increasing_interv x y) with DP; try lra.
 intros t Ht. simpl. unfold P'. ring_simplify.
 replace k with (S (pred k)) at 2 by lia.
 rewrite <- tech_pow_Rmult.
 replace (_-_) with ((-t^pred k) * (S k * (-t) + k)) by lra.
 apply Rmult_lt_0_compat.
 - apply Ropp_0_gt_lt_contravar.
   apply pow_odd_neg; try lra. apply Nat.Even_succ.
   destruct k; simpl; trivial; lia.
 - apply Rplus_lt_0_compat; try apply Rmult_lt_0_compat; try lra.
   apply RSpos.
   destruct k; try lia; apply RSpos.
Qed.

Lemma nu_unique_odd k x : x <= 0 -> P k x = 0 -> Nat.Odd k /\ x = nu k.
Proof.
 intros Hx E.
 destruct (Nat.eq_dec k 0) as [->|NZ].
 { unfold P in E; simpl in E. lra. }
 destruct (Req_dec x 0).
 { subst x. unfold P in E. rewrite !pow_i in E by lia. lra. }
 destruct (Nat.Even_Odd_dec k) as [EV|OD].
 - generalize (P_even_neg_decr k x 0 EV). rewrite E.
   unfold P. rewrite !pow_i by lia. lra.
 - split; trivial.
   assert (I := nu_itvl k OD).
   assert (R := nu_root k OD).
   destruct (Rtotal_order x (nu k)) as [LT|[EQ|GT]]; auto; exfalso.
   + generalize (P_odd_neg_decr k x (nu k) OD); lra.
   + generalize (P_odd_neg_decr k (nu k) x OD); lra.
Qed.

Lemma nu_unique k x : x <= 0 -> x^(S k)=x^k+1 -> x = nu k.
Proof.
 intros Hx E. rewrite <- P_root_equiv in E. now apply nu_unique_odd.
Qed.

Lemma mu_unique_even k x : Nat.Even k -> P k x = 0 -> x = mu k.
Proof.
 intros Hk E.
 destruct (Rle_or_lt x 0) as [LE|LT].
 - destruct (Nat.Even_Odd_False k); trivial.
   apply (nu_unique_odd _ _ LE E).
 - apply mu_unique. lra. now apply P_root_equiv.
Qed.

Lemma mu_or_nu k x : Nat.Odd k -> P k x = 0 -> x = mu k \/ x = nu k.
Proof.
 intros Hk E. rewrite P_root_equiv in E.
 destruct (Rle_or_lt x 0) as [LE|LT].
 - right. now apply nu_unique.
 - left. apply mu_unique; trivial. lra.
Qed.

Lemma P_neg_upper k x : Nat.Odd k -> P k x < 0 -> nu k < x.
Proof.
 intros Hk Hx.
 destruct (Rtotal_order x (nu k)) as [LT|[EQ|GT]]; trivial; exfalso.
 - generalize (P_odd_neg_decr k x (nu k) Hk).
   generalize (nu_itvl k Hk). rewrite nu_root by trivial. lra.
 - subst x. rewrite nu_root in Hx; trivial. lra.
Qed.

Lemma P_neg_lower k x : Nat.Odd k -> x <= 0 -> 0 < P k x -> x < nu k.
Proof.
 intros Hk Hx Hx'.
 destruct (Rtotal_order x (nu k)) as [LT|[EQ|GT]]; trivial; exfalso.
 - subst x. rewrite nu_root in Hx'; trivial. lra.
 - generalize (P_odd_neg_decr k (nu k) x Hk).
   rewrite nu_root by trivial. lra.
Qed.

Lemma nu_decr k : Nat.Odd k -> nu (S (S k)) < nu k.
Proof.
 intros Hk. apply P_neg_upper. now apply Nat.Odd_succ_succ.
 assert (I := nu_itvl k Hk).
 assert (E := nu_carac k Hk).
 set (x := nu k) in *.
 unfold P. rewrite <- 2 tech_pow_Rmult. rewrite E at 1. simpl.
 ring_simplify. assert (x^2 < 1^2); try lra.
 rewrite <- !Rsqr_pow2. apply neg_pos_Rsqr_lt; lra.
Qed.

Lemma nu_1 : nu 1 = (1-sqrt 5)/2.
Proof.
 symmetry.
 apply nu_unique.
 - apply Ropp_le_cancel. field_simplify.
   apply Rle_mult_inv_pos; try lra.
   assert (1 <= sqrt 5); try lra.
   rewrite <- sqrt_1. apply sqrt_le_1_alt. lra.
 - simpl. field_simplify. rewrite pow2_sqrt by lra. field.
Qed.

Lemma nu_1' : -0.6180339887499 < nu 1 < -0.6180339887498.
Proof.
 assert (H : Nat.Odd 1) by now rewrite <- Nat.odd_spec.
 split; [apply P_neg_lower|apply P_neg_upper];
   trivial; unfold P; simpl; lra.
Qed.

Lemma nu_3 : -0.819172513397 < nu 3 < -0.819172513396.
Proof.
 assert (H : Nat.Odd 3) by now rewrite <- Nat.odd_spec.
 split; [apply P_neg_lower|apply P_neg_upper];
   trivial; unfold P; simpl; lra.
Qed.

Lemma nu_5 : -0.88127146164 < nu 5 < -0.88127146163.
Proof.
 assert (H : Nat.Odd 5) by now rewrite <- Nat.odd_spec.
 split; [apply P_neg_lower|apply P_neg_upper];
   trivial; unfold P; simpl; lra.
Qed.

(* Irrationality of mu, tau, nu.
   This is a specialized version of the rational root theorem *)

Lemma Zdivide_pow_inv (n m : Z) (p:nat) :
  Z.gcd n m = 1%Z -> Z.divide n (m^Z.of_nat p) -> Z.divide n m.
Proof.
 induction p as [|p IH]; intros G D.
 - apply Z.divide_1_r in D. destruct D as [-> | ->].
   apply Z.divide_1_l. apply Z.divide_opp_l, Z.divide_1_l.
 - rewrite Nat2Z.inj_succ, Z.pow_succ_r in D by lia.
   apply Z.gauss in D; auto.
Qed.

Lemma root_irrat k (q:Q) : k<>O -> (Q2R q)^(S k) <> (Q2R q)^k + 1.
Proof.
 intros Hk.
 intro E.
 assert (E1 : (Q2R q)^k * (Q2R q - 1) = 1) by (simpl in E; lra).
 clear E.
 rewrite <- (Qred_correct q) in E1.
 destruct (Qred q) as (a,b) eqn:Q.
 assert (P : (Z.gcd a (Zpos b) = 1)%Z).
 { change (Z.gcd (Qnum (a#b)) (QDen (a#b)) = 1)%Z.
   rewrite <- Qred_iff, <- Q. apply Qred_involutive. }
 clear q Q.
 unfold Q2R in E1. simpl in *.
 rewrite Rpow_mult_distr, pow_inv in E1.
 assert (E2 : IZR a ^k * (IZR a - IZR (Zpos b)) = IZR (Zpos b) ^ (S k)).
 { rewrite <- (Rmult_1_r (_^S k)), <- E1. simpl. field. split.
   - intro H. now apply eq_IZR in H.
   - apply pow_nonzero. intro H. now apply eq_IZR in H. }
 clear E1.
 rewrite !pow_IZR, Z_R_minus, <- mult_IZR in E2. apply eq_IZR in E2.
 assert (D : Z.divide a ((Zpos b)^(Z.of_nat (S k)))).
 { rewrite <- E2.
   replace (Z.of_nat k) with (Z.succ (Z.pred (Z.of_nat k))) at 1 by lia.
   rewrite Z.pow_succ_r, <- Z.mul_assoc by lia.
   now apply Z.divide_mul_l. }
 apply Zdivide_pow_inv in D; trivial.
 destruct (Z.le_gt_cases 0%Z a) as [Ha|Ha].
 - rewrite Z.divide_gcd_iff, P in D; trivial.
   subst a. clear Ha P.
   rewrite Z.pow_1_l in E2 by lia.
   assert (0 < (Zpos b)^(Z.of_nat (S k)))%Z;
    try apply Z.pow_pos_nonneg; lia.
 - rewrite <- Z.divide_opp_l, Z.divide_gcd_iff,Z.gcd_opp_l, P in D by lia.
   replace a with (-1)%Z in * by lia.
   clear Ha P D.
   rewrite Nat2Z.inj_succ, Z.pow_succ_r in E2 by lia.
   assert (D' : Z.divide (Z.pos b) 1%Z).
   { replace 1%Z with ((1+Z.pos b)-Z.pos b)%Z by lia.
     apply Z.divide_sub_r; try apply Z.divide_refl.
     exists ((-1)*(-Z.pos b) ^Z.of_nat k)%Z.
     replace (-Z.pos b)%Z with ((-1)*(Z.pos b))%Z by lia.
     rewrite Z.pow_mul_l, <- !Z.mul_assoc.
     rewrite <- (Z.mul_comm (Z.pos b)), <- E2.
     rewrite (Z.mul_assoc (_^_)), <- Z.pow_mul_l.
     change (-1 * -1)%Z with 1%Z. rewrite Z.pow_1_l; lia. }
   apply Z.divide_1_r in D'. destruct D' as [D' | D']; try easy.
   rewrite D' in *. rewrite Z.pow_1_l, Z.mul_1_l in E2 by lia.
   assert (Z.abs 1 = Z.abs 2); try easy.
   rewrite <- E2, Z.abs_mul, Z.abs_pow. simpl. rewrite Z.pow_1_l; lia.
Qed.

Lemma mu_rat k (q:Q) : mu k = Q2R q <-> k=O /\ q==2.
Proof.
 split.
 - intros E. assert (C := mu_carac k). rewrite E in C.
   destruct (Nat.eq_dec k O).
   + split; trivial. subst k. rewrite pow_1, pow_0_r in C.
     apply Qreals.eqR_Qeq. rewrite C. lra.
   + exfalso. revert C. now apply root_irrat.
 - intros (->,->). rewrite mu_0. lra.
Qed.

Lemma mu_irrat k : k<>O -> forall (q:Q), mu k <> Q2R q.
Proof.
 intros Hk q E. apply mu_rat in E. easy.
Qed.

Lemma nu_rat k (q:Q) : nu k = Q2R q <-> Nat.Even k /\ q==0. (* not a root *)
Proof.
 split.
 - intros E. destruct (Nat.Even_Odd_dec k) as [Hk|Hk] eqn:D.
   + split; trivial. unfold nu in E. rewrite D in E.
     apply Qreals.eqR_Qeq; lra.
   + exfalso.
     assert (C := nu_carac k Hk). rewrite E in C. revert C. apply root_irrat.
     destruct Hk; lia.
 - intros (Hk, E).
   unfold nu. destruct Nat.Even_Odd_dec.
   + rewrite E; lra.
   + now destruct (Nat.Even_Odd_False k).
Qed.

Lemma nu_irrat k : Nat.Odd k -> forall (q:Q), nu k <> Q2R q.
Proof.
 intros Hk q E. apply nu_rat in E. apply (Nat.Even_Odd_False k); tauto.
Qed.

Lemma tau_rat k (q:Q) : tau k = Q2R q <-> k=O /\ q==1#2.
Proof.
 split.
 - intros E.
   assert (E' : mu k = Q2R (/q)%Q).
   { rewrite tau_inv, E. rewrite Qreals.Q2R_inv; trivial.
     intros Hq. generalize (tau_itvl k). rewrite E, Hq. lra. }
   apply mu_rat in E'. destruct E' as (Hk,E'). split; trivial.
   now rewrite <- (Qinv_involutive q), E'.
 - intros (->,->). rewrite tau_0. lra.
Qed.

Lemma tau_irrat k : k<>O -> forall (q:Q), tau k <> Q2R q.
Proof.
 intros Hk q E. apply tau_rat in E. easy.
Qed.

(** The limit of mu(k) and tau(k) is 1 when k tends to +∞ *)

Lemma pow_lower_bound (k:nat)(x:R) : 0<=x -> 1 + k*x <= (1+x)^k.
Proof.
 induction k.
 - simpl. lra.
 - intros Hx. rewrite <- tech_pow_Rmult.
   apply Rle_trans with ((1+x)*(1+k*x)).
   + rewrite S_INR. generalize (pos_INR k). nra.
   + apply Rmult_le_compat_l; lra.
Qed.

Lemma mu_upper_bound_aux (k:nat) : (S k)*(mu k - 1)^2 <= 1.
Proof.
 unfold mu. destruct mu_spec as (mu & M1 & M2). cbn -[pow INR].
 unfold P in M2. rewrite <- tech_pow_Rmult in M2.
 replace (S k*_) with ((mu-1)*(S k*(mu-1))) by lra.
 replace 1 with ((mu-1)*mu^k) at 3 by lra.
 apply Rmult_le_compat_l; try lra.
 replace mu with (1+(mu-1)) at 2 by lra.
 rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l.
 generalize (pow_lower_bound k (mu-1)). lra.
Qed.

Lemma mu_upper_bound (k:nat) : mu k <= 1 + /sqrt (S k).
Proof.
 assert (Hk := RSpos k).
 assert (M1 := mu_itvl k).
 assert (mu k - 1 <= / sqrt (S k)); try lra.
 rewrite inv_sqrt_depr; try lra.
 apply Rsqr_incr_0; try apply sqrt_pos; try lra.
 rewrite Rsqr_sqrt by (generalize (Rinv_0_lt_compat _ Hk); lra).
 rewrite Rsqr_pow2.
 apply Rmult_le_reg_l with (S k); trivial.
 rewrite <- Rinv_r_sym; try lra.
 apply mu_upper_bound_aux.
Qed.

Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

Lemma mu_limit : is_lim_seq mu 1.
Proof.
 apply is_lim_seq_le_le with (fun _ => 1) (fun k => 1 + /sqrt (S k)).
 - split. generalize (mu_itvl n); lra. apply mu_upper_bound; lia.
 - apply is_lim_seq_const.
 - replace (Rbar.Finite 1) with (Rbar.Finite (1+0)) by (f_equal; lra).
   apply is_lim_seq_plus'; try apply is_lim_seq_const.
   change (Rbar.Finite 0) with (Rbar.Rbar_inv Rbar.p_infty).
   apply is_lim_seq_inv; try easy.
   rewrite <- is_lim_seq_incr_1 with (u:=fun n => sqrt n).
   apply is_lim_seq_sqrt.
Qed.

Lemma tau_limit : is_lim_seq tau 1.
Proof.
 unfold tau.
 replace (Rbar.Finite 1) with (Rbar.Rbar_inv 1) by (simpl; f_equal; lra).
 apply is_lim_seq_inv. apply mu_limit. simpl. intros [= E]. lra.
Qed.
