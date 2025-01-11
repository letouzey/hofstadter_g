From Coq Require Import Lia Reals Lra Ranalysis5 QArith Qcanon.
Require Import MoreReals MoreLim.

Local Open Scope R.
Local Coercion INR : nat >-> R.

(** * Real roots of polynom [X^(q+1)-X^q-1] *)

(** Study of [X^(q+1)=X^q+1] : one unique positive root mu(q), in ]1..2].
    For instance :

     - mu(0) = 2
     - mu(1) = 1.618033988749895.. (Golden ratio)
     - mu(2) = 1.465571231876768..
     - mu(3) = 1.380277569097614..
     - mu(4) = 1.324717957244746.. (plastic number, root of X^3=X+1)
     - mu(5) = 1.285199033245349..

    Dual : positive root tau(q) of X^(q+1)+X-1, in [0.5..1[
    i.e. tau(q) = 1/mu(q)

     - tau(0) = 0.5
     - tau(1) = 0.6180339887498948..
     - tau(2) = 0.6823278038280193..
     - tau(3) = 0.7244919590005157..
     - tau(4) = 0.7548776662466925..
     - tau(5) = 0.7780895986786012..
*)

Definition P (q:nat) (x:R) : R := x^(S q)-x^q-1.

Lemma P_root_equiv q x : P q x = 0 <-> x^(S q) = x^q+1.
Proof.
 unfold P. lra.
Qed.

Lemma P_root_equiv' q x : P q x = 0 <-> x^(q+1) = x^q+1.
Proof.
 rewrite Nat.add_1_r. apply P_root_equiv.
Qed.

Definition mu_spec q : { x : R | 1<=x<=2 /\ P q x = 0 }.
Proof.
 destruct q.
 - exists 2. unfold P. lra.
 - apply (IVT_interv (P (S q)) 1 2).
   + intros a Ha. apply derivable_continuous_pt.
     repeat apply derivable_pt_minus.
     * apply derivable_pt_pow.
     * apply derivable_pt_pow.
     * apply derivable_pt_const.
   + lra.
   + unfold P. simpl. lra.
   + unfold P. simpl. generalize (pow_R1_Rle 2 q). lra.
Qed.

Definition mu q : R := proj1_sig (mu_spec q).

Lemma mu_itvl q : 1 < mu q <= 2.
Proof.
 unfold mu. destruct (mu_spec q) as (x & H & E). simpl.
 destruct (Req_dec x 1); try lra. subst. unfold P in *. simpl in *; lra.
Qed.

Lemma mu_root q : P q (mu q) = 0.
Proof.
 unfold mu. destruct (mu_spec q) as (x & H & E). simpl in *. lra.
Qed.

Lemma mu_carac q : (mu q)^(S q) = (mu q)^q+1.
Proof.
 rewrite <- P_root_equiv. apply mu_root.
Qed.

Definition tau q : R := (*1*) / mu q.

Lemma tau_inv q : mu q = (*1*) / tau q.
Proof.
 unfold tau. now rewrite Rinv_inv.
Qed.

Lemma tau_itvl q : 1/2 <= tau q < 1.
Proof.
 unfold tau. generalize (mu_itvl q). intros.
 replace (1/2) with (/2) by lra.
 split.
 - apply Rinv_le_contravar; lra.
 - replace 1 with (/1) by lra.
   apply Rinv_1_lt_contravar; lra.
Qed.

Lemma tau_carac q : (tau q)^(S q) + tau q = 1.
Proof.
 unfold tau.
 assert (MU:=mu_itvl q).
 rewrite pow_inv.
 assert ((mu q)^(S q)<>0). { apply pow_nonzero. lra. }
 apply Rmult_eq_reg_l with ((mu q)^(S q)); auto.
 rewrite Rmult_1_r, Rmult_plus_distr_l, Rinv_r; auto.
 rewrite mu_carac at 2. simpl. rewrite Rinv_r_simpl_m; lra.
Qed.

Lemma tau_incr q : tau q < tau (S q).
Proof.
 destruct (Rlt_or_le (tau q) (tau (S q))); auto. exfalso.
 assert (E := tau_carac q).
 assert (E' := tau_carac (S q)).
 assert (tau (S q) ^ (S (S q)) < tau q ^(S q)); try lra.
 { apply Rle_lt_trans with (tau q ^(S (S q))).
   - apply pow_incr. generalize (tau_itvl (S q)); lra.
   - remember (S q) as q'. simpl. generalize (tau_itvl q); nra. }
Qed.

Lemma tau_incr' q q' : (q <= q')%nat -> tau q <= tau q'.
Proof.
 induction 1; try lra.
 apply Rle_trans with (tau m); trivial. apply Rlt_le, tau_incr.
Qed.

Lemma mu_decr q : mu (S q) < mu q.
Proof.
 rewrite !tau_inv. apply Rinv_lt_contravar. 2:apply tau_incr.
 apply Rmult_lt_0_compat; generalize (tau_itvl q)(tau_itvl (S q)); lra.
Qed.

Definition Ptau q x := x^(S q) + x.

Lemma Ptau_incr q x y :
 0<=x<=1 -> 0<=y<=1 -> x<y -> Ptau q x < Ptau q y.
Proof.
 set (P' := fun x => (S q)*x^q+1).
 assert (D : forall x, derivable_pt_lim (Ptau q) x (P' x)).
 { clear. intros x. apply derivable_pt_lim_plus.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_id. }
 set (DP := fun x => exist _ (P' x) (D x) : derivable_pt (Ptau q) x).
 apply derive_increasing_interv with DP. lra.
 intros t Ht. simpl. unfold P'.
 apply Rplus_le_lt_0_compat. 2:lra.
 apply Rmult_le_pos. apply pos_INR. apply pow_le; lra.
Qed.

Lemma tau_unique q x : 0 <= x -> Ptau q x = 1 -> x = tau q.
Proof.
 intros Hx H.
 assert (x < 1).
 { destruct (Rlt_or_le x 1); auto. exfalso.
   generalize (pow_R1_Rle x (S q)). unfold Ptau in H. lra. }
 assert (I := tau_itvl q).
 assert (E := tau_carac q). change (Ptau q (tau q) = 1) in E.
 destruct (Rtotal_order x (tau q)) as [LT|[EQ|GT]]; auto; exfalso.
 - apply (Ptau_incr q) in LT; lra.
 - apply (Ptau_incr q) in GT; lra.
Qed.

Lemma mu_unique q x : 0 <= x -> x^(S q)=x^q+1 -> x = mu q.
Proof.
 intros Hx H.
 assert (x <> 0).
 { destruct q. simpl in *. lra.
   intros ->. rewrite !pow_i in H; lra || lia. }
 assert (E : 1/x = tau q).
 { apply tau_unique.
   - apply Rle_mult_inv_pos; lra.
   - unfold Ptau. unfold Rdiv. rewrite Rmult_1_l, pow_inv.
     assert (0 < x ^ S q) by (apply pow_lt; lra).
     apply Rmult_eq_reg_l with (x^(S q)); try lra.
     field_simplify; try lra.
     rewrite Rdiv_plus_distr. simpl. field_simplify; try lra.
     now rewrite <- H. }
 rewrite tau_inv. rewrite <- E. unfold Rdiv. now rewrite Rmult_1_l, Rinv_inv.
Qed.

Lemma Ptau_lower q x : 0 <= x -> Ptau q x < 1 -> x < tau q.
Proof.
 intros H H'.
 assert (x < 1).
 { destruct (Rlt_or_le x 1); auto. exfalso.
   generalize (pow_R1_Rle x (S q)). unfold Ptau in H'. lra. }
 destruct (Rtotal_order x (tau q)) as [LT|[EQ|GT]]; auto; exfalso.
 - subst x. unfold Ptau in H'. rewrite tau_carac in H'. lra.
 - apply (Ptau_incr q) in GT; try lra.
   unfold Ptau in GT at 1. rewrite tau_carac in GT. lra.
   generalize (tau_itvl q); lra.
Qed.

Lemma Ptau_upper q x : 0 <= x -> 1 < Ptau q x -> tau q < x.
Proof.
 intros H H'.
 destruct (Rtotal_order x (tau q)) as [LT|[EQ|GT]]; auto; exfalso.
 - apply (Ptau_incr q) in LT; try (generalize (tau_itvl q); lra).
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

(** When q is odd, there is also a real negative root to X^(q+1)-X^q-1.
    nu(1) = -0.618033988749895.. = 1-phi
    nu(3) = -0.8191725133961643..
    nu(5) = -0.8812714616335695..
 *)

Lemma minushalf_no_root q : P q (-0.5) < 0.
Proof.
 unfold P. replace (-0.5) with (-1*/2) by lra. simpl.
 rewrite !Rpow_mult_distr.
 destruct (Nat.Even_Odd_dec q) as [EV|OD].
 - rewrite minusone_pow_even by trivial. field_simplify.
   assert (0<(/2)^q) by ( apply pow_lt; lra). lra.
 - rewrite minusone_pow_odd by trivial. apply Ropp_lt_cancel.
   field_simplify. apply Rlt_mult_inv_pos; try lra.
   assert ((/2)^q <= /2); try lra.
   { rewrite pow_inv.
     apply Rinv_le_contravar. lra.
     destruct OD as (q' & ->). rewrite Nat.add_1_r. simpl.
     generalize (pow_R1_Rle 2 (q'+(q'+0))). lra. }
Qed.

Definition nu_spec q :
  Nat.Odd q -> { x : R | -1<=x<=-0.5 /\ P q x = 0 }.
Proof.
 intros Hq.
 apply (IVT_interv_decr (P q) (-1) (-0.5)).
   + intros a Ha. apply derivable_continuous_pt.
     repeat apply derivable_pt_minus.
     * apply derivable_pt_pow.
     * apply derivable_pt_pow.
     * apply derivable_pt_const.
   + lra.
   + unfold P. simpl. rewrite minusone_pow_odd by trivial. lra.
   + apply minushalf_no_root.
Qed.

Definition nu q : R :=
 match Nat.Even_Odd_dec q with
 | left _ => 0 (* arbitrary value, not a root *)
 | right ODD => proj1_sig (nu_spec q ODD)
 end.

Lemma nu_itvl q : Nat.Odd q -> -1 < nu q < -0.5.
Proof.
 intros ODD. unfold nu. destruct (Nat.Even_Odd_dec q) as [EV|OD].
 - destruct (Nat.Even_Odd_False q EV ODD).
 - destruct (nu_spec q OD) as (x & H & E). simpl.
   destruct (Req_dec x (-1)).
   { subst. unfold P in *; simpl in *.
     rewrite minusone_pow_odd in *; trivial; lra. }
   destruct (Req_dec x (-0.5)).
   { subst. generalize (minushalf_no_root q). lra. }
   lra.
Qed.

Lemma nu_root q : Nat.Odd q -> P q (nu q) = 0.
Proof.
 intros ODD. unfold nu. destruct (Nat.Even_Odd_dec q) as [EV|OD].
 - destruct (Nat.Even_Odd_False q EV ODD).
 - destruct (nu_spec q OD) as (x & H & E). simpl in *. trivial.
Qed.

Lemma nu_carac q : Nat.Odd q -> (nu q)^(S q) = (nu q)^q+1.
Proof.
 intros. rewrite <- P_root_equiv. now apply nu_root.
Qed.

(* Uniqueness of the negative root (if it exists) *)

Lemma P_odd_neg_decr q x y :
 Nat.Odd q -> x<y<=0 -> P q y < P q x.
Proof.
 intros Hq.
 set (P' := fun x => (S q)*x^q-q*x^(pred q)-0).
 assert (D : forall x, derivable_pt_lim (P q) x (P' x)).
 { clear. intros x. repeat apply derivable_pt_lim_minus.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_const. }
 set (DP := fun x => exist _ (P' x) (D x) : derivable_pt (P q) x).
 intros Hxy.
 apply (derive_decreasing_interv x y) with DP; try lra.
 intros t Ht. simpl. unfold P'. ring_simplify.
 replace q with (S (pred q)) at 2 by (destruct Hq as (q',->); lia).
 rewrite <- tech_pow_Rmult.
 apply Ropp_lt_cancel. rewrite Ropp_0.
 replace (-_) with (t^pred q * (S q * (-t) + q)) by lra.
 apply Rmult_lt_0_compat.
 - apply pow_even_pos; try lra.
   destruct Hq as (q', ->). rewrite Nat.add_1_r. now exists q'.
 - apply Rplus_lt_0_compat; try apply Rmult_lt_0_compat; try lra.
   apply RSpos.
   destruct Hq as (q', ->). rewrite Nat.add_1_r. apply RSpos.
Qed.

Lemma P_even_neg_decr q x y :
 Nat.Even q -> x<y<=0 -> P q x < P q y.
Proof.
 intros Hq Hxy.
 destruct (Nat.eq_dec q 0) as [->|NZ]. { unfold P. simpl. lra. }
 set (P' := fun x => (S q)*x^q-q*x^(pred q)-0).
 assert (D : forall x, derivable_pt_lim (P q) x (P' x)).
 { clear. intros x. repeat apply derivable_pt_lim_minus.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_const. }
 set (DP := fun x => exist _ (P' x) (D x) : derivable_pt (P q) x).
 apply (derive_increasing_interv x y) with DP; try lra.
 intros t Ht. simpl. unfold P'. ring_simplify.
 replace q with (S (pred q)) at 2 by lia.
 rewrite <- tech_pow_Rmult.
 replace (_-_) with ((-t^pred q) * (S q * (-t) + q)) by lra.
 apply Rmult_lt_0_compat.
 - apply Ropp_0_gt_lt_contravar.
   apply pow_odd_neg; try lra. apply Nat.Even_succ.
   destruct q; simpl; trivial; lia.
 - apply Rplus_lt_0_compat; try apply Rmult_lt_0_compat; try lra.
   apply RSpos.
   destruct q; try lia; apply RSpos.
Qed.

Lemma nu_unique_odd q x : x <= 0 -> P q x = 0 -> Nat.Odd q /\ x = nu q.
Proof.
 intros Hx E.
 destruct (Nat.eq_dec q 0) as [->|NZ].
 { unfold P in E; simpl in E. lra. }
 destruct (Req_dec x 0).
 { subst x. unfold P in E. rewrite !pow_i in E by lia. lra. }
 destruct (Nat.Even_Odd_dec q) as [EV|OD].
 - generalize (P_even_neg_decr q x 0 EV). rewrite E.
   unfold P. rewrite !pow_i by lia. lra.
 - split; trivial.
   assert (I := nu_itvl q OD).
   assert (R := nu_root q OD).
   destruct (Rtotal_order x (nu q)) as [LT|[EQ|GT]]; auto; exfalso.
   + generalize (P_odd_neg_decr q x (nu q) OD); lra.
   + generalize (P_odd_neg_decr q (nu q) x OD); lra.
Qed.

Lemma nu_unique q x : x <= 0 -> x^(S q)=x^q+1 -> x = nu q.
Proof.
 intros Hx E. rewrite <- P_root_equiv in E. now apply nu_unique_odd.
Qed.

Lemma mu_unique_even q x : Nat.Even q -> P q x = 0 -> x = mu q.
Proof.
 intros Hq E.
 destruct (Rle_or_lt x 0) as [LE|LT].
 - destruct (Nat.Even_Odd_False q); trivial.
   apply (nu_unique_odd _ _ LE E).
 - apply mu_unique. lra. now apply P_root_equiv.
Qed.

Lemma mu_or_nu q x : Nat.Odd q -> P q x = 0 -> x = mu q \/ x = nu q.
Proof.
 intros Hq E. rewrite P_root_equiv in E.
 destruct (Rle_or_lt x 0) as [LE|LT].
 - right. now apply nu_unique.
 - left. apply mu_unique; trivial. lra.
Qed.

Lemma P_neg_upper q x : Nat.Odd q -> P q x < 0 -> nu q < x.
Proof.
 intros Hq Hx.
 destruct (Rtotal_order x (nu q)) as [LT|[EQ|GT]]; trivial; exfalso.
 - generalize (P_odd_neg_decr q x (nu q) Hq).
   generalize (nu_itvl q Hq). rewrite nu_root by trivial. lra.
 - subst x. rewrite nu_root in Hx; trivial. lra.
Qed.

Lemma P_neg_lower q x : Nat.Odd q -> x <= 0 -> 0 < P q x -> x < nu q.
Proof.
 intros Hq Hx Hx'.
 destruct (Rtotal_order x (nu q)) as [LT|[EQ|GT]]; trivial; exfalso.
 - subst x. rewrite nu_root in Hx'; trivial. lra.
 - generalize (P_odd_neg_decr q (nu q) x Hq).
   rewrite nu_root by trivial. lra.
Qed.

Lemma nu_decr q : Nat.Odd q -> nu (S (S q)) < nu q.
Proof.
 intros Hq. apply P_neg_upper. now apply Nat.Odd_succ_succ.
 assert (I := nu_itvl q Hq).
 assert (E := nu_carac q Hq).
 set (x := nu q) in *.
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

Lemma root_irrat q (x:Q) : q<>O -> (Q2R x)^(S q) <> (Q2R x)^q + 1.
Proof.
 intros Hq.
 intro E.
 assert (E1 : (Q2R x)^q * (Q2R x - 1) = 1) by (simpl in E; lra).
 clear E.
 rewrite <- (Qred_correct x) in E1.
 destruct (Qred x) as (a,b) eqn:X.
 assert (P : (Z.gcd a (Zpos b) = 1)%Z).
 { change (Z.gcd (Qnum (a#b)) (QDen (a#b)) = 1)%Z.
   rewrite <- Qred_iff, <- X. apply Qred_involutive. }
 clear x X.
 unfold Q2R in E1. simpl in *.
 rewrite Rpow_mult_distr, pow_inv in E1.
 assert (E2 : IZR a ^q * (IZR a - IZR (Zpos b)) = IZR (Zpos b) ^ (S q)).
 { rewrite <- (Rmult_1_r (_^S q)), <- E1. simpl. field. split.
   - intro H. now apply eq_IZR in H.
   - apply pow_nonzero. intro H. now apply eq_IZR in H. }
 clear E1.
 rewrite !pow_IZR, Z_R_minus, <- mult_IZR in E2. apply eq_IZR in E2.
 assert (D : Z.divide a ((Zpos b)^(Z.of_nat (S q)))).
 { rewrite <- E2.
   replace (Z.of_nat q) with (Z.succ (Z.pred (Z.of_nat q))) at 1 by lia.
   rewrite Z.pow_succ_r, <- Z.mul_assoc by lia.
   now apply Z.divide_mul_l. }
 apply Zdivide_pow_inv in D; trivial.
 destruct (Z.le_gt_cases 0%Z a) as [Ha|Ha].
 - rewrite Z.divide_gcd_iff, P in D; trivial.
   subst a. clear Ha P.
   rewrite Z.pow_1_l in E2 by lia.
   assert (0 < (Zpos b)^(Z.of_nat (S q)))%Z;
    try apply Z.pow_pos_nonneg; lia.
 - rewrite <- Z.divide_opp_l, Z.divide_gcd_iff,Z.gcd_opp_l, P in D by lia.
   replace a with (-1)%Z in * by lia.
   clear Ha P D.
   rewrite Nat2Z.inj_succ, Z.pow_succ_r in E2 by lia.
   assert (D' : Z.divide (Z.pos b) 1%Z).
   { replace 1%Z with ((1+Z.pos b)-Z.pos b)%Z by lia.
     apply Z.divide_sub_r; try apply Z.divide_refl.
     exists ((-1)*(-Z.pos b) ^Z.of_nat q)%Z.
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

Lemma mu_rat q (x:Q) : mu q = Q2R x <-> q=O /\ x==2.
Proof.
 split.
 - intros E. assert (C := mu_carac q). rewrite E in C.
   destruct (Nat.eq_dec q O).
   + split; trivial. subst q. rewrite pow_1, pow_0_r in C.
     apply Qreals.eqR_Qeq. rewrite C. lra.
   + exfalso. revert C. now apply root_irrat.
 - intros (->,->). rewrite mu_0. lra.
Qed.

Lemma mu_irrat q : q<>O -> forall (x:Q), mu q <> Q2R x.
Proof.
 intros Hq x E. apply mu_rat in E. easy.
Qed.

Lemma nu_rat q (x:Q) : nu q = Q2R x <-> Nat.Even q /\ x==0. (* not a root *)
Proof.
 split.
 - intros E. destruct (Nat.Even_Odd_dec q) as [Hq|Hq] eqn:D.
   + split; trivial. unfold nu in E. rewrite D in E.
     apply Qreals.eqR_Qeq; lra.
   + exfalso.
     assert (C := nu_carac q Hq). rewrite E in C. revert C. apply root_irrat.
     destruct Hq; lia.
 - intros (Hq, E).
   unfold nu. destruct Nat.Even_Odd_dec.
   + rewrite E; lra.
   + now destruct (Nat.Even_Odd_False q).
Qed.

Lemma nu_irrat q : Nat.Odd q -> forall (x:Q), nu q <> Q2R x.
Proof.
 intros Hq x E. apply nu_rat in E. apply (Nat.Even_Odd_False q); tauto.
Qed.

Lemma tau_rat q (x:Q) : tau q = Q2R x <-> q=O /\ x==1#2.
Proof.
 split.
 - intros E.
   assert (E' : mu q = Q2R (/x)%Q).
   { rewrite tau_inv, E. rewrite Qreals.Q2R_inv; trivial.
     intros Hq. generalize (tau_itvl q). rewrite E, Hq. lra. }
   apply mu_rat in E'. destruct E' as (Hq,E'). split; trivial.
   now rewrite <- (Qinv_involutive x), E'.
 - intros (->,->). rewrite tau_0. lra.
Qed.

Lemma tau_irrat q : q<>O -> forall (x:Q), tau q <> Q2R x.
Proof.
 intros Hq x E. apply tau_rat in E. easy.
Qed.

(** The limit of mu(q) and tau(q) is 1 when q tends to +∞ *)

Lemma pow_lower_bound (q:nat)(x:R) : 0<=x -> 1 + q*x <= (1+x)^q.
Proof.
 induction q.
 - simpl. lra.
 - intros Hx. rewrite <- tech_pow_Rmult.
   apply Rle_trans with ((1+x)*(1+q*x)).
   + rewrite S_INR. generalize (pos_INR q). nra.
   + apply Rmult_le_compat_l; lra.
Qed.

Lemma mu_upper_bound_aux (q:nat) : (S q)*(mu q - 1)^2 <= 1.
Proof.
 unfold mu. destruct mu_spec as (mu & M1 & M2). cbn -[pow INR].
 unfold P in M2. rewrite <- tech_pow_Rmult in M2.
 replace (S q*_) with ((mu-1)*(S q*(mu-1))) by lra.
 replace 1 with ((mu-1)*mu^q) at 3 by lra.
 apply Rmult_le_compat_l; try lra.
 replace mu with (1+(mu-1)) at 2 by lra.
 rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l.
 generalize (pow_lower_bound q (mu-1)). lra.
Qed.

Lemma mu_upper_bound (q:nat) : mu q <= 1 + /sqrt (S q).
Proof.
 assert (Hq := RSpos q).
 assert (M1 := mu_itvl q).
 assert (mu q - 1 <= / sqrt (S q)); try lra.
 rewrite inv_sqrt_depr; try lra.
 apply Rsqr_incr_0; try apply sqrt_pos; try lra.
 rewrite Rsqr_sqrt by (generalize (Rinv_0_lt_compat _ Hq); lra).
 rewrite Rsqr_pow2.
 apply Rmult_le_reg_l with (S q); trivial.
 rewrite <- Rinv_r_sym; try lra.
 apply mu_upper_bound_aux.
Qed.

Lemma pow_mu_lower_bound (q:nat) : sqrt (S q) <= (mu q)^q.
Proof.
  rewrite <- (sqrt_pow2 (mu q ^q)).
  2:{ apply Rlt_le, pow_lt. generalize (mu_itvl q); lra. }
  apply sqrt_le_1.
  - apply Rlt_le. apply RSpos.
  - rewrite <- Rsqr_pow2. apply Rle_0_sqr.
  - apply Rmult_le_reg_r with ((mu q-1)^2).
    + apply pow_lt. generalize (mu_itvl q); lra.
    + rewrite <- Rpow_mult_distr.
      replace (mu q^q*(mu q -1)) with 1.
      * rewrite pow1. apply mu_upper_bound_aux.
      * field_simplify; try lra.
        rewrite Rmult_comm, tech_pow_Rmult, mu_carac; lra.
Qed.

Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

Lemma mu_limit : is_lim_seq mu 1.
Proof.
 apply is_lim_seq_le_le with (fun _ => 1) (fun q => 1 + /sqrt (S q)).
 - split. generalize (mu_itvl n); lra. apply mu_upper_bound; lia.
 - apply is_lim_seq_const.
 - replace 1 with (1+0) at 1 by lra.
   apply is_lim_seq_plus'; try apply is_lim_seq_const.
   rewrite <- is_lim_seq_incr_1 with (u:=fun n => /sqrt n).
   apply lim_inv_sqrt.
Qed.

Lemma tau_limit : is_lim_seq tau 1.
Proof.
 unfold tau.
 replace (Rbar.Finite 1) with (Rbar.Rbar_inv 1) by (simpl; f_equal; lra).
 apply is_lim_seq_inv. apply mu_limit. simpl. intros [= E]. lra.
Qed.

Lemma opp_pow_upper_bound (q:nat)(x:R) : 0<=x<=1 -> 1-x^q <= q*(1-x).
Proof.
 intros Hx.
 induction q.
 - simpl. lra.
 - rewrite <- tech_pow_Rmult, S_INR.
   assert (x^q*(1-x) <= 1*(1-x)); try lra.
   { apply Rmult_le_compat_r. lra.
     rewrite <- (pow1 q). now apply pow_incr. }
Qed.

Lemma pow_mu_upper_bound q : (mu q)^q <= S q.
Proof.
 assert (H : 0 < tau q < 1) by (generalize (tau_itvl q); lra).
 replace (mu q ^q) with (mu q ^S q - 1)
  by (generalize (mu_carac q); lra).
 apply Rmult_le_reg_r with (1 - tau q); try lra.
 replace ((mu q^S q -1)*(1 - tau q)) with (1 - tau q ^S q).
 2:{ replace (1-tau q) with (tau q^S q)
     by (generalize (tau_carac q); lra).
     rewrite tau_inv, pow_inv. field.
     destruct H as (H,_). apply (pow_lt _ (S q)) in H. lra. }
 apply (opp_pow_upper_bound (S q)). lra.
Qed.

Lemma mu_lower_bound q : 1 + /S q <= mu q.
Proof.
 assert (Hq := RSpos q).
 assert (M1 := mu_itvl q).
 assert (/S q <= mu q - 1); try lra.
 apply Rmult_le_reg_r with (S q * mu q^q).
 - apply Rmult_lt_0_compat. lra. apply pow_lt. lra.
 - rewrite (Rmult_comm (S q)) at 2.
   rewrite <- (Rmult_assoc _ _ (S q)).
   replace ((mu q -1)*mu q^q) with 1; field_simplify; try lra.
   + apply pow_mu_upper_bound.
   + rewrite tech_pow_Rmult, mu_carac; lra.
Qed.

(** A better lower bound for tau. Actually, this lower bound is even
    an equivalent of tau for large q, see file RootEquiv.v *)

Lemma tau_better_lower_bound q : (2<=q)%nat -> 1-ln(q+1)/(q+1) < tau q.
Proof.
 intros Hq.
 apply le_INR in Hq. change (INR 2) with 2 in Hq.
 set (a := 1 - ln(q+1)/(q+1)).
 assert (Ha : 0<a<1).
 { unfold a. split.
   - assert (ln (q+1)/(q+1) < 1); try lra.
     { apply -> Rcomplements.Rdiv_lt_1; try lra.
       rewrite <- (ln_exp (q+1)) at 2. apply ln_increasing. lra.
       generalize (exp_ineq1 (q+1)); lra. }
   - apply tech_Rgt_minus, Rdiv_lt_0_compat; try lra.
     rewrite <- ln_1. apply ln_increasing; lra. }
 set (Q := fun x => x^(S q)+x-1).
 assert (LT : Q a < 0).
 { unfold Q. assert (a ^S q < 1 - a); try lra.
   apply ln_lt_inv; try lra.  apply pow_lt; lra.
   rewrite Rcomplements.ln_pow, S_INR; try lra.
   apply Rle_lt_trans with (-ln (q+1)).
   - rewrite Rmult_comm. apply Rcomplements.Rle_div_r; try lra.
     eapply Rle_trans. apply Rcomplements.ln_le. lra.
     apply exp_ineq1_le. rewrite ln_exp; lra.
   - unfold a. replace (1-(1-_)) with (ln (q+1)/(q+1)) by lra.
     assert (LT : 1 < ln (q+1)).
     { rewrite <- (ln_exp 1) at 1. apply ln_increasing.
       apply exp_pos. generalize exp_1_lt_3; lra. }
     rewrite Rcomplements.ln_div; try lra.
     apply ln_increasing in LT; try lra. rewrite ln_1 in LT. lra. }
 destruct (IVT_interv Q a 1) as (r & (R1,R2) & R3).
 { intros b Hb. apply derivable_continuous_pt.
   apply derivable_pt_minus; try apply derivable_pt_const.
   apply derivable_pt_plus; try apply derivable_pt_id.
   apply derivable_pt_pow. }
 { lra. }
 { trivial. }
 { unfold Q. rewrite pow1. lra. }
 assert (E : r = tau q).
 { apply tau_unique. lra. unfold Ptau, Q in *. lra. }
 apply Rle_lt_or_eq_dec in R1. destruct R1; subst; lra.
Qed.
