From Coq Require Import Lia Znat Reals Lra Ranalysis5 QArith Qcanon.
Close Scope Q. (* Issue with QArith. *)
Require Import MoreTac MoreReals MoreLim.
Local Open Scope Q.
Local Open Scope R.
Local Coercion INR : nat >-> R.

(** * Real roots of polynom [X^k-X^(k-1)-1] *)

(** Study of [X^k=X^(k-1)+1] :
    one unique positive root mu(k), in ]1..2] as soon as k>0.
    For instance :

     - mu(1) = 2
     - mu(2) = 1.618033988749895.. (Golden ratio)
     - mu(3) = 1.465571231876768..
     - mu(4) = 1.380277569097614..
     - mu(5) = 1.324717957244746.. (plastic number, root of X^3=X+1)
     - mu(6) = 1.285199033245349..

    Dual : positive root tau(k) of X^k+X-1, in [0.5..1[ when k>0.
    i.e. tau(k) = 1/mu(k)

     - tau(1) = 0.5
     - tau(2) = 0.6180339887498948..
     - tau(3) = 0.6823278038280193..
     - tau(4) = 0.7244919590005157..
     - tau(5) = 0.7548776662466925..
     - tau(6) = 0.7780895986786012..
*)

Definition P (k:nat) (x:R) : R := x^k-x^(k-1)-1.

Lemma P_root_equiv k x : P k x = 0 <-> x^k = x^(k-1)+1.
Proof.
 unfold P. lra.
Qed.

(** Beware, for k=0, mu is an arbitrary value, not a root (we choose 2) *)

Definition mu_spec k : { x : R | 1<x<=2 /\ (k=O \/ P k x = 0) }.
Proof.
 destruct k as [|[|k]].
 - exists 2. split. lra. now left.
 - exists 2. split. lra. right. unfold P. simpl. lra.
 - destruct (IVT_interv (P (S (S k))) 1 2) as (x & Hx & Hx').
   + intros a Ha. apply derivable_continuous_pt.
     repeat apply derivable_pt_minus.
     * apply derivable_pt_pow.
     * apply derivable_pt_pow.
     * apply derivable_pt_const.
   + lra.
   + unfold P. simpl. lra.
   + unfold P. simpl. ring_simplify. generalize (pow_R1_Rle 2 k). lra.
   + exists x.
     assert (x <> 1). { intros ->. unfold P in Hx'. simpl in Hx'. lra. }
     split. lra. now right.
Defined.

Definition mu k : R := proj1_sig (mu_spec k).

Lemma mu_itvl k : 1 < mu k <= 2.
Proof.
 unfold mu. destruct (mu_spec k) as (x & H & H'). apply H.
Qed.

Lemma mu_pos k : 0 < mu k.
Proof.
 generalize (mu_itvl k). lra.
Qed.

Lemma mu_0 : mu 0 = 2.
Proof.
 reflexivity.
Qed.

Lemma mu_1 : mu 1 = 2.
Proof.
 reflexivity.
Qed.

Lemma mu_root k : k<>O -> P k (mu k) = 0.
Proof.
 intros K.
 unfold mu. destruct (mu_spec k) as (x & H & [K'|E]).
 - now destruct K.
 - apply E.
Qed.

Lemma mu_carac k : k<>O -> (mu k)^k = (mu k)^(k-1)+1.
Proof.
 intros K. rewrite <- P_root_equiv. now apply mu_root.
Qed.

Lemma mu_carac' k : k<>O -> (mu k)^(k-1)*(mu k - 1) = 1.
Proof.
 intros K.
 rewrite Rmult_minus_distr_l, Rmult_comm, tech_pow_Rmult.
 replace (S (k-1)) with k by lia. rewrite mu_carac; trivial; lra.
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

Lemma tau_pos k : 0 < tau k.
Proof.
 generalize (tau_itvl k). lra.
Qed.

Lemma tau_carac k : k<>O -> (tau k)^k + tau k = 1.
Proof.
 intros K.
 unfold tau.
 assert (MU:=mu_itvl k).
 rewrite pow_inv.
 assert ((mu k)^k<>0). { apply pow_nonzero. lra. }
 apply Rmult_eq_reg_l with ((mu k)^k); auto.
 rewrite Rmult_1_r, Rmult_plus_distr_l, Rinv_r; auto.
 rewrite mu_carac at 2; trivial. simpl.
 replace k with (S (k-1)) at 2 by lia. simpl. field. lra.
Qed.

Lemma tau_incr k : k<>O -> tau k < tau (S k).
Proof.
 destruct k as [|k]; try easy. intros _.
 destruct (Rlt_or_le (tau (S k)) (tau (S (S k)))); auto. exfalso.
 assert (E := tau_carac (S k) lia).
 assert (E' := tau_carac (S (S k)) lia).
 assert (tau (S (S k)) ^ (S (S k)) < tau (S k) ^(S k)); try lra.
 { apply Rle_lt_trans with (tau (S k) ^(S (S k))).
   - apply pow_incr. split; trivial. apply Rlt_le, tau_pos.
   - remember (S k) as k'. simpl. generalize (tau_itvl k'); nra. }
Qed.

Lemma tau_incr' k k' : (k <= k')%nat -> tau k <= tau k'.
Proof.
 induction 1; try lra.
 apply Rle_trans with (tau m); trivial.
 destruct m. apply Rle_refl. now apply Rlt_le, tau_incr.
Qed.

Lemma mu_decr k : k<>O -> mu (S k) < mu k.
Proof.
 intros K. rewrite !tau_inv. apply Rinv_lt_contravar. 2:now apply tau_incr.
 apply Rmult_lt_0_compat; apply tau_pos.
Qed.

Definition Ptau k x := x^k + x.

Lemma Ptau_incr k x y :
 0<=x<=1 -> 0<=y<=1 -> x<y -> Ptau k x < Ptau k y.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { unfold Ptau. intros. rewrite !pow_O. lra. }
 set (P' := fun x => k*x^(pred k)+1).
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

Lemma tau_unique k x : k<>O -> 0 <= x -> Ptau k x = 1 -> x = tau k.
Proof.
 intros K Hx H.
 assert (x < 1).
 { destruct (Rlt_or_le x 1); auto. exfalso.
   generalize (pow_R1_Rle x k). unfold Ptau in H. lra. }
 assert (I := tau_itvl k).
 assert (E := tau_carac k K). change (Ptau k (tau k) = 1) in E.
 destruct (Rtotal_order x (tau k)) as [LT|[EQ|GT]]; auto; exfalso.
 - apply (Ptau_incr k) in LT; lra.
 - apply (Ptau_incr k) in GT; lra.
Qed.

Lemma mu_unique k x : 0 <= x -> x^k = x^(k-1)+1 -> x = mu k.
Proof.
 intros Hx H.
 destruct (Nat.eq_dec k 0) as [->|K].
 { rewrite !pow_O in H. lra. }
 assert (x <> 0).
 { destruct k. simpl in *. lra.
   intros ->. simpl in H. generalize (pow_le 0 (k-0)). lra. }
 assert (E : 1/x = tau k).
 { apply tau_unique; trivial.
   - apply Rle_mult_inv_pos; lra.
   - unfold Ptau. unfold Rdiv. rewrite Rmult_1_l, pow_inv.
     assert (0 < x ^ k) by (apply pow_lt; lra).
     apply Rmult_eq_reg_l with (x^k); try lra.
     rewrite Rmult_plus_distr_l. replace k with (S (k-1)) at 3 by lia.
     rewrite H at 3. simpl. field; try lra. }
 rewrite tau_inv. rewrite <- E. unfold Rdiv. now rewrite Rmult_1_l, Rinv_inv.
Qed.

Lemma Ptau_lower k x : k<>O -> 0 <= x -> Ptau k x < 1 -> x < tau k.
Proof.
 intros K H H'.
 assert (x < 1).
 { destruct (Rlt_or_le x 1); auto. exfalso.
   generalize (pow_R1_Rle x k). unfold Ptau in H'. lra. }
 destruct (Rtotal_order x (tau k)) as [LT|[EQ|GT]]; auto; exfalso.
 - subst x. unfold Ptau in H'. rewrite tau_carac in H'; trivial. lra.
 - apply (Ptau_incr k) in GT; try lra.
   unfold Ptau in GT at 1. rewrite tau_carac in GT; trivial. lra.
   generalize (tau_itvl k); lra.
Qed.

Lemma Ptau_upper k x : k<>O -> 0 <= x -> 1 < Ptau k x -> tau k < x.
Proof.
 intros K H H'.
 destruct (Rtotal_order x (tau k)) as [LT|[EQ|GT]]; auto; exfalso.
 - apply (Ptau_incr k) in LT; try (generalize (tau_itvl k); lra).
   unfold Ptau in LT at 2. rewrite tau_carac in LT; trivial. lra.
 - subst x. unfold Ptau in H'. rewrite tau_carac in H'; trivial. lra.
Qed.

Lemma Ptau_lt1_iff k x : k<>O -> 0 <= x -> Ptau k x < 1 <-> x < tau k.
Proof.
 intros K Hx. split.
 - now apply Ptau_lower.
 - destruct (Req_dec (Ptau k x) 1).
   + apply tau_unique in H; trivial. lra.
   + intros LT. apply Rlt_not_le in LT. apply Rnot_le_lt.
     contradict LT. apply Rlt_le. apply Ptau_upper; trivial; lra.
Qed.

Lemma Ptau_gt1_iff k x : k<>O -> 0 <= x -> 1 < Ptau k x <-> tau k < x.
Proof.
 intros K Hx. split.
 - now apply Ptau_upper.
 - destruct (Req_dec (Ptau k x) 1).
   + apply tau_unique in H; trivial. lra.
   + intros LT. apply Rlt_not_le in LT. apply Rnot_le_lt.
     contradict LT. apply Rlt_le. apply Ptau_lower; trivial. lra.
Qed.

Lemma tau_0 : tau 0 = 1/2.
Proof.
 unfold tau. rewrite mu_0; lra.
Qed.

Lemma tau_1 : tau 1 = 1/2.
Proof.
 unfold tau. rewrite mu_1; lra.
Qed.

Lemma tau_2 : tau 2 = (sqrt 5 - 1)/2.
Proof.
 symmetry. apply tau_unique; try lia.
 - apply Rle_mult_inv_pos; try lra.
   generalize (sqrt_le_1_alt 1 5). rewrite sqrt_1. lra.
 - unfold Ptau.
   simpl. rewrite Rmult_1_r.
   generalize (Rsqr_sqrt 5). unfold Rsqr. lra.
Qed.

Lemma tau_3 : 0.6823278038280 < tau 3 < 0.6823278038281.
Proof.
 split; [ apply Ptau_lower | apply Ptau_upper ]; unfold Ptau; lia || lra.
Qed.

Lemma tau_4 : 0.7244919590005 < tau 4 < 0.7244919590006.
Proof.
 split; [ apply Ptau_lower | apply Ptau_upper ]; unfold Ptau; lia || lra.
Qed.

Lemma tau_5 : 0.7548776662466 < tau 5 < 0.7548776662467.
Proof.
 split; [ apply Ptau_lower | apply Ptau_upper ]; unfold Ptau; lia || lra.
Qed.

Lemma tau_6 : 0.7780895986786 < tau 6 < 0.7780895986787.
Proof.
 split; [ apply Ptau_lower | apply Ptau_upper ]; unfold Ptau; lia || lra.
Qed.

Lemma mu_2 : mu 2 = (1+sqrt 5)/2.
Proof.
 rewrite tau_inv.
 assert (H := tau_itvl 2).
 apply Rmult_eq_reg_l with (tau 2); try lra.
 rewrite Rinv_r by lra.
 rewrite tau_2.
 generalize (Rsqr_sqrt 5). unfold Rsqr. lra.
Qed.

Lemma mu_3 : 1.465571231876 < mu 3 < 1.465571231877.
Proof.
 rewrite tau_inv.
 assert (H := tau_3).
 destruct tau_3 as (H1,H2). apply Rinv_lt_contravar in H1,H2; lra.
Qed.

Lemma mu_4 : 1.380277569097 < mu 4 < 1.380277569098.
Proof.
 rewrite tau_inv.
 assert (H := tau_4).
 destruct tau_4 as (H1,H2). apply Rinv_lt_contravar in H1,H2; lra.
Qed.

Lemma mu_5 : 1.324717957244 < mu 5 < 1.324717957245.
Proof.
 rewrite tau_inv.
 assert (H := tau_5).
 destruct tau_5 as (H1,H2). apply Rinv_lt_contravar in H1,H2; lra.
Qed.

Lemma mu_6 : 1.285199033245 < mu 6 < 1.286199033246.
Proof.
 rewrite tau_inv.
 assert (H := tau_6).
 destruct tau_6 as (H1,H2). apply Rinv_lt_contravar in H1,H2; lra.
Qed.

(** When k is even and >0, there is also a real negative root to X^k-X^(k-1)-1.
    nu(2) = -0.618033988749895.. = 1-phi
    nu(4) = -0.8191725133961643..
    nu(6) = -0.8812714616335695..
 *)

Lemma minushalf_no_root k : P k (-0.5) < 0.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { unfold P. rewrite !pow_O. lra. }
 unfold P. replace (-0.5) with (-1*/2) by lra.
 replace k with (S (k-1)) at 1 by lia. simpl.
 rewrite !Rpow_mult_distr.
 destruct (Nat.Even_Odd_dec (k-1)) as [EV|OD].
 - rewrite minusone_pow_even by trivial. field_simplify.
   assert (0<(/2)^(k-1)) by ( apply pow_lt; lra). lra.
 - rewrite minusone_pow_odd by trivial. apply Ropp_lt_cancel.
   field_simplify. apply Rlt_mult_inv_pos; try lra.
   assert ((/2)^(k-1) <= /2); try lra.
   { rewrite pow_inv.
     apply Rinv_le_contravar. lra.
     destruct OD as (k' & ->). rewrite Nat.add_1_r. simpl.
     generalize (pow_R1_Rle 2 (k'+(k'+0))). lra. }
Qed.

Definition nu_spec k :
  k<>O -> Nat.Even k -> { x : R | -1<=x<=-0.5 /\ P k x = 0 }.
Proof.
 intros Hk Hk'.
 apply (IVT_interv_decr (P k) (-1) (-0.5)).
   + intros a Ha. apply derivable_continuous_pt.
     repeat apply derivable_pt_minus.
     * apply derivable_pt_pow.
     * apply derivable_pt_pow.
     * apply derivable_pt_const.
   + lra.
   + unfold P. simpl. replace k with (S (k-1)) at 1 by lia.
     simpl. rewrite (minusone_pow_odd (k-1)). lra.
     rewrite <- Nat.Even_succ. now replace (S (k-1)) with k by lia.
   + apply minushalf_no_root.
Qed.

Definition nu k : R :=
 match k with
 | O => 0 (* arbitrary value, not a root *)
 | S k' => match Nat.Even_Odd_dec (S k') with
        | left EV => proj1_sig (nu_spec _ (Nat.neq_succ_0 k') EV)
        | right _ => 0 (* arbitrary value, not a root *)
        end
 end.

Lemma nu_itvl k : k<>O -> Nat.Even k -> -1 < nu k < -0.5.
Proof.
 intros K EV. unfold nu. destruct k. easy.
 destruct (Nat.Even_Odd_dec (S k)) as [EV'|OD'].
 - destruct nu_spec as (x & H & E). simpl.
   destruct (Req_dec x (-1)).
   { subst. unfold P in *; simpl in *.
     rewrite Nat.sub_0_r in E. rewrite minusone_pow_odd in E. lra.
     now rewrite <- Nat.Even_succ. }
   destruct (Req_dec x (-0.5)).
   { subst. generalize (minushalf_no_root (S k)). lra. }
   lra.
 - destruct (Nat.Even_Odd_False _ EV OD').
Qed.

Lemma nu_root k : k<>O -> Nat.Even k -> P k (nu k) = 0.
Proof.
 intros K EV. unfold nu. destruct k. easy.
 destruct (Nat.Even_Odd_dec (S k)) as [EV'|OD'].
 - now destruct nu_spec as (x & H & E).
 - destruct (Nat.Even_Odd_False _ EV OD').
Qed.

Lemma nu_carac k : k<>O -> Nat.Even k -> (nu k)^k = (nu k)^(k-1)+1.
Proof.
 intros. rewrite <- P_root_equiv. now apply nu_root.
Qed.

Lemma nu_carac' k : k<>O -> Nat.Even k -> (nu k)^(k-1)*(nu k - 1) = 1.
Proof.
 intros. rewrite Rmult_minus_distr_l, Rmult_comm, tech_pow_Rmult.
 replace (S (k-1)) with k by lia. rewrite nu_carac; trivial; lra.
Qed.


(* Uniqueness of the negative root (if it exists) *)

Lemma P_even_neg_decr k x y :
 k<>O -> Nat.Even k -> x<y<=0 -> P k y < P k x.
Proof.
 intros K K'.
 set (P' := fun x => k*x^(pred k)-(k-1)%nat*x^(pred (k-1))-0).
 assert (D : forall x, derivable_pt_lim (P k) x (P' x)).
 { clear. intros x. repeat apply derivable_pt_lim_minus.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_const. }
 set (DP := fun x => exist _ (P' x) (D x) : derivable_pt (P k) x).
 intros Hxy.
 apply (derive_decreasing_interv x y) with DP; try lra.
 intros t Ht. simpl. unfold P'. rewrite minus_INR by lia.
 change (INR 1) with 1.
 assert (2 <= k)%nat. { destruct K' as (k',->); lia. }
 replace (pred k) with (S (k-2)) by lia.
 replace (pred (k-1)) with (k-2)%nat by lia. simpl.
 apply Ropp_lt_cancel. rewrite Ropp_0.
 replace (-_) with ((k*(1-t)-1)*t^(k-2)) by ring.
 apply Rmult_lt_0_compat.
 - apply le_INR in H. change (INR 2) with 2 in H. nra.
 - apply pow_even_pos; try lra.
   rewrite <- Nat.Even_succ_succ. now replace (S _) with k by lia.
Qed.

Lemma P_odd_neg_decr k x y :
 Nat.Odd k -> x<y<=0 -> P k x < P k y.
Proof.
 intros K Hxy.
 destruct (Nat.eq_dec k 1) as [->|NZ]. { unfold P. simpl. lra. }
 set (P' := fun x => k*x^(pred k)-(k-1)%nat*x^(pred (k-1))-0).
 assert (D : forall x, derivable_pt_lim (P k) x (P' x)).
 { clear. intros x. repeat apply derivable_pt_lim_minus.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_pow.
   apply derivable_pt_lim_const. }
 set (DP := fun x => exist _ (P' x) (D x) : derivable_pt (P k) x).
 apply (derive_increasing_interv x y) with DP; try lra.
 intros t Ht. simpl. unfold P'.
 assert (3 <= k)%nat. { destruct K as (k',->); lia. }
 rewrite minus_INR by lia. change (INR 1) with 1.
 replace (pred k) with (S (k-2)) by lia.
 replace (pred (k-1)) with (k-2)%nat by lia. simpl.
 replace (_-0) with ((-t^(k-2)) * (k * (1-t) - 1)) by ring.
 apply Rmult_lt_0_compat.
 - apply Ropp_0_gt_lt_contravar.
   apply pow_odd_neg; try lra. rewrite <- Nat.Odd_succ_succ.
   now replace (S _) with k by lia.
 - apply le_INR in H. rewrite INR_IZR_INZ in H; simpl in H. nra.
Qed.

Lemma nu_unique_even k x :
  x <= 0 -> P k x = 0 -> k<>O /\ Nat.Even k /\ x = nu k.
Proof.
 intros Hx E.
 destruct (Nat.eq_dec k 0) as [->|K0].
 { unfold P in E. rewrite !pow_O in E. lra. }
 destruct (Nat.eq_dec k 1) as [->|K1].
 { unfold P in E; simpl in E. lra. }
 split. trivial.
 destruct (Req_dec x 0).
 { subst x. unfold P in E. rewrite !pow_i in E by lia. lra. }
 destruct (Nat.Even_Odd_dec k) as [EV|OD].
 - split; trivial.
   assert (I := nu_itvl k K0 EV).
   assert (R := nu_root k K0 EV).
   destruct (Rtotal_order x (nu k)) as [LT|[EQ|GT]]; auto; exfalso.
   + generalize (P_even_neg_decr k x (nu k) K0 EV); lra.
   + generalize (P_even_neg_decr k (nu k) x K0 EV); lra.
 - generalize (P_odd_neg_decr k x 0 OD). rewrite E.
   unfold P. rewrite !pow_i by lia. lra.
Qed.

Lemma nu_unique k x : x <= 0 -> x^k = x^(k-1)+1 -> x = nu k.
Proof.
 intros Hx E. rewrite <- P_root_equiv in E. now apply nu_unique_even.
Qed.

Lemma mu_unique_odd k x : Nat.Odd k -> P k x = 0 -> x = mu k.
Proof.
 intros K E.
 destruct (Rle_or_lt x 0) as [LE|LT].
 - destruct (Nat.Even_Odd_False k); trivial.
   apply (nu_unique_even _ _ LE E).
 - apply mu_unique. lra. now apply P_root_equiv.
Qed.

Lemma mu_or_nu q x : Nat.Even q -> P q x = 0 -> x = mu q \/ x = nu q.
Proof.
 intros Hq E. rewrite P_root_equiv in E.
 destruct (Rle_or_lt x 0) as [LE|LT].
 - right. now apply nu_unique.
 - left. apply mu_unique; trivial. lra.
Qed.

Lemma P_neg_upper k x : k<>O -> Nat.Even k -> P k x < 0 -> nu k < x.
Proof.
 intros K K' Hx.
 destruct (Rtotal_order x (nu k)) as [LT|[EQ|GT]]; trivial; exfalso.
 - generalize (P_even_neg_decr k x (nu k) K K').
   generalize (nu_itvl k K K'). rewrite nu_root by trivial. lra.
 - subst x. rewrite nu_root in Hx; trivial. lra.
Qed.

Lemma P_neg_lower k x : k<>O -> Nat.Even k -> x <= 0 -> 0 < P k x -> x < nu k.
Proof.
 intros K K' Hx Hx'.
 destruct (Rtotal_order x (nu k)) as [LT|[EQ|GT]]; trivial; exfalso.
 - subst x. rewrite nu_root in Hx'; trivial. lra.
 - generalize (P_even_neg_decr k (nu k) x K K').
   rewrite nu_root by trivial. lra.
Qed.

Lemma nu_decr k : k<>O -> Nat.Even k -> nu (S (S k)) < nu k.
Proof.
 intros K K'. apply P_neg_upper. easy. now apply Nat.Even_succ_succ.
 assert (I := nu_itvl k K K').
 assert (E := nu_carac k K K').
 set (x := nu k) in *.
 unfold P. simpl. rewrite E at 1.
 replace k with (S (k-1)) at 2 by lia. simpl.
 replace (_-1) with (x^2-1) by ring. nra.
Qed.

Lemma nu_2 : nu 2 = (1-sqrt 5)/2.
Proof.
 symmetry.
 apply nu_unique.
 - apply Ropp_le_cancel. field_simplify.
   apply Rle_mult_inv_pos; try lra.
   assert (1 <= sqrt 5); try lra.
   rewrite <- sqrt_1. apply sqrt_le_1_alt. lra.
 - simpl. field_simplify. rewrite pow2_sqrt by lra. field.
Qed.

Lemma nu_2' : -0.6180339887499 < nu 2 < -0.6180339887498.
Proof.
 assert (H : Nat.Even 2) by now rewrite <- Nat.even_spec.
 split; [apply P_neg_lower|apply P_neg_upper]; try lia; trivial;
   unfold P; simpl; lra.
Qed.

Lemma nu_4 : -0.819172513397 < nu 4 < -0.819172513396.
Proof.
 assert (H : Nat.Even 4) by now rewrite <- Nat.even_spec.
 split; [apply P_neg_lower|apply P_neg_upper]; try lia;
   trivial; unfold P; simpl; lra.
Qed.

Lemma nu_6 : -0.88127146164 < nu 6 < -0.88127146163.
Proof.
 assert (H : Nat.Even 6) by now rewrite <- Nat.even_spec.
 split; [apply P_neg_lower|apply P_neg_upper]; try lia;
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

Lemma root_irrat k (x:Q) : (1<k)%nat -> (Q2R x)^k <> (Q2R x)^(k-1) + 1.
Proof.
 intros K E.
 assert (E1 : (Q2R x)^(k-1) * (Q2R x - 1) = 1).
 { replace k with (S (k-1)) in E at 1 by lia. simpl in E; lra. }
 clear E.
 rewrite <- (Qred_correct x) in E1.
 destruct (Qred x) as (a,b) eqn:X.
 assert (P : (Z.gcd a (Zpos b) = 1)%Z).
 { change (Z.gcd (Qnum (a#b)) (QDen (a#b)) = 1)%Z.
   rewrite <- Qred_iff, <- X. apply Qred_involutive. }
 clear x X.
 unfold Q2R in E1. simpl in *.
 rewrite Rpow_mult_distr, pow_inv in E1.
 assert (E2 : IZR a ^(k-1) * (IZR a - IZR (Zpos b)) = IZR (Zpos b) ^ k).
 { rewrite <- (Rmult_1_r (_^k)), <- E1.
   replace k with (S (k-1)) at 2 by lia. simpl. field. split.
   - intro H. now apply eq_IZR in H.
   - apply pow_nonzero. intro H. now apply eq_IZR in H. }
 clear E1.
 rewrite !pow_IZR, Z_R_minus, <- mult_IZR in E2. apply eq_IZR in E2.
 assert (D : Z.divide a ((Zpos b)^(Z.of_nat k))).
 { rewrite <- E2.
   replace (Z.of_nat (k-1)) with (Z.succ (Z.of_nat (k-2))) by lia.
   rewrite Z.pow_succ_r, <- Z.mul_assoc by lia.
   now apply Z.divide_mul_l. }
 apply Zdivide_pow_inv in D; trivial.
 destruct (Z.le_gt_cases 0%Z a) as [Ha|Ha].
 - rewrite Z.divide_gcd_iff, P in D; trivial.
   subst a. clear Ha P.
   rewrite Z.pow_1_l in E2 by lia.
   assert (0 < (Zpos b)^(Z.of_nat k))%Z;
    try apply Z.pow_pos_nonneg; lia.
 - rewrite <- Z.divide_opp_l, Z.divide_gcd_iff,Z.gcd_opp_l, P in D by lia.
   replace a with (-1)%Z in * by lia.
   clear Ha P D.
   replace k with (S (k-1)) in E2 at 2 by lia.
   rewrite Nat2Z.inj_succ, Z.pow_succ_r in E2 by lia.
   assert (D' : Z.divide (Z.pos b) 1%Z).
   { replace 1%Z with ((1+Z.pos b)-Z.pos b)%Z by lia.
     apply Z.divide_sub_r; try apply Z.divide_refl.
     exists ((-1)*(-Z.pos b) ^Z.of_nat (k-1))%Z.
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

Lemma mu_rat k (x:Q) : mu k = Q2R x <-> (k<=1)%nat /\ x==2.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { rewrite mu_0. split.
   + intros. split. lia. apply Qreals.eqR_Qeq. rewrite <- H. lra.
   + intros (_,->). lra. }
 split.
 - intros E. assert (C := mu_carac k K). rewrite E in C.
   destruct (Nat.eq_dec k 1) as [->|K'].
   + split. trivial. apply Qreals.eqR_Qeq. rewrite <- E, mu_1. lra.
   + exfalso. revert C. apply root_irrat. lia.
 - intros (K',->). replace k with 1%nat by lia. rewrite mu_1. lra.
Qed.

Lemma mu_irrat k : (1<k)%nat -> forall (x:Q), mu k <> Q2R x.
Proof.
 intros K x E. apply mu_rat in E. lia.
Qed.

Lemma nu_rat k (x:Q) :
  nu k = Q2R x <-> (k=O \/ Nat.Odd k) /\ x==0. (* not a root *)
Proof.
 destruct k.
 { unfold nu. split. intros E. split. now left. apply Qreals.eqR_Qeq; lra.
   intros (_,->). lra. }
 split.
 - intros E. destruct (Nat.Even_Odd_dec (S k)) as [K|K] eqn:D.
   + exfalso. assert (C := nu_carac (S k) lia K).
     rewrite E in C. revert C. apply root_irrat. destruct K; lia.
   + split. now right. unfold nu in E. rewrite D in E.
     apply Qreals.eqR_Qeq; lra.
 - intros ([K|K], E). easy. unfold nu. destruct Nat.Even_Odd_dec.
   + now destruct (Nat.Even_Odd_False (S k)).
   + rewrite E; lra.
Qed.

Lemma nu_irrat k : k<>O -> Nat.Even k -> forall (x:Q), nu k <> Q2R x.
Proof.
 intros K K' x E. apply nu_rat in E. apply (Nat.Even_Odd_False k); tauto.
Qed.

Lemma tau_rat k (x:Q) : tau k = Q2R x <-> (k<=1)%nat /\ x==1#2.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { split.
   - intros E. split. lia. apply Qreals.eqR_Qeq. rewrite <- E.
     unfold tau. rewrite mu_0. lra.
   - intros (_,->). unfold tau. rewrite mu_0. lra. }
 split.
 - intros E.
   assert (E' : mu k = Q2R (/x)%Q).
   { rewrite tau_inv, E. rewrite Qreals.Q2R_inv; trivial.
     intros E'. generalize (tau_itvl k). rewrite E, E'. lra. }
   apply mu_rat in E'. destruct E' as (K',E'). split; trivial.
   now rewrite <- (Qinv_involutive x), E'.
 - intros (K',->). replace k with 1%nat by lia. rewrite tau_1. lra.
Qed.

Lemma tau_irrat k : (1<k)%nat -> forall (x:Q), tau k <> Q2R x.
Proof.
 intros K x E. apply tau_rat in E. lia.
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

Lemma mu_upper_bound_aux (k:nat) : k*(mu k - 1)^2 <= 1.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { rewrite Rmult_0_l. lra. }
 unfold mu. destruct mu_spec as (mu & M1 & [->|M2]); try easy.
 cbn -[pow INR].
 unfold P in M2. replace k with (S (k-1)) in M2 at 1 by lia.
 rewrite <- tech_pow_Rmult in M2.
 replace (k*_) with ((mu-1)*(k*(mu-1))) by lra.
 replace 1 with ((mu-1)*mu^(k-1)) at 3 by lra.
 apply Rmult_le_compat_l; try lra.
 replace mu with (1+(mu-1)) at 2 by lra.
 replace k with (S (k-1)) at 1 by lia.
 rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l.
 generalize (pow_lower_bound (k-1) (mu-1)). lra.
Qed.

Lemma mu_upper_bound (k:nat) : k<>O -> mu k <= 1 + /sqrt k.
Proof.
 intros K.
 assert (K' := RSpos (k-1)). replace (S (k-1)) with k in K' by lia.
 assert (M1 := mu_itvl k).
 assert (mu k - 1 <= / sqrt k); try lra.
 rewrite inv_sqrt_depr; try lra.
 apply Rsqr_incr_0; try apply sqrt_pos; try lra.
 rewrite Rsqr_sqrt by (generalize (Rinv_0_lt_compat _ K'); lra).
 rewrite Rsqr_pow2.
 apply Rmult_le_reg_l with k; trivial.
 rewrite <- Rinv_r_sym; try lra.
 apply mu_upper_bound_aux.
Qed.

Lemma pow_mu_lower_bound (k:nat) : sqrt k <= (mu k)^(k-1).
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { simpl. rewrite sqrt_0. lra. }
 rewrite <- (sqrt_pow2 (mu k ^(k-1))).
 2:{ apply Rlt_le, pow_lt. generalize (mu_itvl k); lra. }
 apply sqrt_le_1.
 - apply pos_INR.
 - rewrite <- Rsqr_pow2. apply Rle_0_sqr.
 - apply Rmult_le_reg_r with ((mu k-1)^2).
   + apply pow_lt. generalize (mu_itvl k); lra.
   + rewrite <- Rpow_mult_distr.
     replace (mu k^(k-1)*(mu k -1)) with 1.
     * rewrite pow1. apply mu_upper_bound_aux.
     * generalize (mu_carac k K).
       replace k with (S (k-1)) at 2 by lia. simpl. lra.
Qed.

Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

Lemma mu_limit : is_lim_seq mu 1.
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_le_le with (fun _ => 1) (fun k => 1 + /sqrt (S k)).
 - split. generalize (mu_itvl (S n)); lra. apply mu_upper_bound; lia.
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

Lemma opp_pow_upper_bound (k:nat)(x:R) : 0<=x<=1 -> 1-x^k <= k*(1-x).
Proof.
 intros Hx.
 induction k.
 - simpl. lra.
 - rewrite <- tech_pow_Rmult, S_INR.
   assert (x^k*(1-x) <= 1*(1-x)); try lra.
   { apply Rmult_le_compat_r. lra.
     rewrite <- (pow1 k). now apply pow_incr. }
Qed.

Lemma pow_mu_upper_bound k : k<>O -> (mu k)^(k-1) <= k.
Proof.
 intros K.
 assert (H : 0 < tau k < 1) by (generalize (tau_itvl k); lra).
 replace (mu k ^(k-1)) with (mu k ^k - 1)
  by (generalize (mu_carac k K); lra).
 apply Rmult_le_reg_r with (1 - tau k); try lra.
 replace ((mu k^k -1)*(1 - tau k)) with (1 - tau k ^k).
 2:{ replace (1-tau k) with (tau k^k)
     by (generalize (tau_carac k K); lra).
     rewrite tau_inv, pow_inv. field.
     destruct H as (H,_). apply (pow_lt _ k) in H. lra. }
 apply (opp_pow_upper_bound k). lra.
Qed.

Lemma mu_lower_bound k : k<>O -> 1 + /k <= mu k.
Proof.
 intros K.
 assert (K' := RSpos (k-1)). replace (S (k-1)) with k in K' by lia.
 assert (M1 := mu_itvl k).
 assert (/k <= mu k - 1); try lra.
 apply Rmult_le_reg_r with (k * mu k^(k-1)).
 - apply Rmult_lt_0_compat. lra. apply pow_lt. lra.
 - rewrite (Rmult_comm k) at 2.
   rewrite <- (Rmult_assoc _ _ k).
   replace ((mu k -1)*mu k^(k-1)) with 1; field_simplify; try lra.
   + now apply pow_mu_upper_bound.
   + rewrite tech_pow_Rmult. replace (S (k-1)) with k by lia.
     rewrite mu_carac; trivial. lra.
Qed.

(** A better lower bound for tau. Actually, this lower bound is even
    an equivalent of tau for large k, see file RootEquiv.v *)

Lemma tau_better_lower_bound k : (3<=k)%nat -> 1-ln(k)/k < tau k.
Proof.
 intros K.
 apply le_INR in K. rewrite INR_IZR_INZ in K. simpl in K.
 set (a := 1 - ln(k)/k).
 assert (Ha : 0<a<1).
 { unfold a. split.
   - assert (ln k/k < 1); try lra.
     { apply -> Rcomplements.Rdiv_lt_1; try lra.
       rewrite <- (ln_exp k) at 2. apply ln_increasing. lra.
       generalize (exp_ineq1 k); lra. }
   - apply tech_Rgt_minus, Rdiv_lt_0_compat; try lra.
     rewrite <- ln_1. apply ln_increasing; lra. }
 set (Q := fun x => x^k+x-1).
 assert (LT : Q a < 0).
 { unfold Q. assert (a ^k < 1 - a); try lra.
   apply ln_lt_inv; try lra.  apply pow_lt; lra.
   rewrite Rcomplements.ln_pow; try lra.
   apply Rle_lt_trans with (-ln k).
   - rewrite Rmult_comm. apply Rcomplements.Rle_div_r; try lra.
     eapply Rle_trans. apply Rcomplements.ln_le. lra.
     apply exp_ineq1_le. rewrite ln_exp; lra.
   - unfold a. replace (1-(1-_)) with (ln k/k) by lra.
     assert (LT : 1 < ln k).
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
 assert (E : r = tau k).
 { apply tau_unique. intros ->. simpl in *. lra. lra.
   unfold Ptau, Q in *. lra. }
 apply Rle_lt_or_eq_dec in R1. destruct R1; subst; lra.
Qed.
