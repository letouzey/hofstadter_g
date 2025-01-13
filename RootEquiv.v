From Coq Require Import Lia Reals Lra Ranalysis5 QArith Qcanon.
From Coquelicot Require Import Rcomplements Hierarchy Continuity ElemFct.
From Coquelicot Require Import PSeries.
Require Import MoreFun MoreReals MoreLim Mu.

Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * The positive root of X^n+X-1 is equivalent to 1-ln n/n for large n *)

(** To prove that, we study iterated approximations of this root r,
    based on the fact that r=(1-r)^(1/n). We show below that a2 < r < a3
    when n>=3 and that a2 and a3 provide the desired equivalent.
    Any initial point 0<a0<1 would probably do, but picking a0 = 1-1/e
    leads to some constant cancellations later. *)

Definition a0 := 1 - exp(-1).
Definition a1 (n:nat) := Rpower (1 - a0) (/n).
Definition a2 (n:nat) := Rpower (1 - a1 n) (/n).
Definition a3 (n:nat) := Rpower (1 - a2 n) (/n).

Lemma a1_alt n : a1 n = exp (-/n).
Proof.
 unfold a1, a0, Rpower. f_equal. replace (-/n) with (/n * -1) by lra.
 rewrite <- (ln_exp (-1)) at 2. f_equal. f_equal. lra.
Qed.

(** Instead of a proper Landau o(1) notation, we explicit the residual
    functions and show below that all of them converge to 0 *)

Definition ϵ1 (n:nat) := n * a1 n - n + 1.
Definition ϵ2 (n:nat) := n * a2 n - n + ln n.
Definition ϵ3 (n:nat) := n * a3 n - n + ln n - ln (ln n).

(** The asymptotic expressions of a1 a2 a3 *)

Lemma a1_eqn n : n<>O -> a1 n = 1 - /n + ϵ1(n)/n.
Proof. intros Hn. unfold ϵ1. field. apply not_0_INR; lia. Qed.

Lemma a2_eqn n : n<>O -> a2 n = 1 - ln n / n + ϵ2(n)/n.
Proof. intros Hn. unfold ϵ2. field. apply not_0_INR; lia. Qed.

Lemma a3_eqn n : n<>O -> a3 n = 1 - ln n / n + ln (ln n) / n + ϵ3(n)/n.
Proof. intros Hn. unfold ϵ3. field. apply not_0_INR; lia. Qed.

(** Convergence to 0 *)

Lemma ϵ1_lim : is_lim_seq ϵ1 0.
Proof.
 set (f := fun x => (exp x - 1) / x).
 apply is_lim_seq_ext_loc with (fun n => (-1)*(f (-/n))+1).
 { exists 1%nat. intros n Hn. unfold ϵ1, f. rewrite a1_alt.
   field. apply not_0_INR; lia. }
 replace 0 with ((-1)*1+1) by lra.
 apply is_lim_seq_plus'; try apply is_lim_seq_const.
 apply is_lim_seq_mult'; try apply is_lim_seq_const.
 apply is_lim_comp_seq with (x:=0).
 - apply is_lim_div_expm1_0.
 - exists 1%nat. intros n Hn [= E].
   assert (E' : /n = 0) by lra. revert E'.
   apply Rinv_neq_0_compat, not_0_INR; lia.
 - replace 0 with (-0) by lra. apply is_lim_seq_opp', is_lim_seq_invn.
Qed.

Lemma ϵ2_lim : is_lim_seq ϵ2 0.
Proof.
 set (ϵ1' := fun n => ln (1-ϵ1 n)).
 assert (E1' : is_lim_seq ϵ1' 0).
 { rewrite <- ln_1. apply is_lim_seq_continuous.
   - apply continuous_alt, continuous_ln; lra.
   - replace 1 with (1-0) at 1 by lra.
     apply is_lim_seq_minus'. apply is_lim_seq_const. apply ϵ1_lim. }
 set (b1 := fun (n:nat) => -(ln n / n) + ϵ1' n/n).
 assert (E : forall n, n<>O -> b1 n = ln (1-a1 n)/n).
 { intros n Hn. unfold b1, ϵ1'. rewrite a1_eqn; trivial.
   assert (Hn' : 0 < n) by (apply lt_0_INR; lia).
   apply Rmult_eq_reg_l with (INR n); try lra. field_simplify; try lra.
   rewrite Rplus_comm. fold (ln (1 - ϵ1 n) - ln n).
   rewrite <- ln_div; try lra.
   - f_equal; field; lra.
   - unfold ϵ1. ring_simplify. replace (_+_) with (n*(1-a1 n)) by ring.
     apply Rmult_lt_0_compat; trivial.
     apply Rlt_Rminus. rewrite <- exp_0, a1_alt. apply exp_increasing.
     apply Ropp_lt_gt_0_contravar.
     apply Rinv_0_lt_compat. apply lt_0_INR; lia. }
 assert (B1 : is_lim_seq b1 0).
 { replace 0 with (-0+0*0) by lra.
   apply is_lim_seq_plus'.
   - apply is_lim_seq_opp', lim_ln_div_n.
   - apply is_lim_seq_mult'; trivial. apply is_lim_seq_invn. }
 assert (B1' : eventually (fun n => b1 n <> 0)).
 { apply is_lim_seq_spec in E1'. destruct (E1' posreal_one) as (N,HN).
   exists (N+3)%nat. intros n Hn [=E'].
   assert (Hn' : INR 3 <= n) by (apply le_INR; lia). simpl in Hn'.
   unfold b1 in E'.
   unfold Rdiv in E'. rewrite Ropp_mult_distr_l, <- Rmult_plus_distr_r in E'.
   apply Rmult_integral in E'. destruct E'.
   2:{ generalize (Rinv_0_lt_compat n); lra. }
   specialize (HN n lia). simpl in HN. rewrite Rminus_0_r in HN.
   apply Rabs_def2 in HN.
   assert (1 < ln n); try lra.
   assert (E1 := exp_1_itvl).
   rewrite <- (ln_exp 1). apply ln_increasing; lra. }
 apply is_lim_seq_ext_loc with
  (fun n => (b1 n^2 * n)*((exp (b1 n) - 1 - b1 n)/(b1 n)^2) + ϵ1' n).
 { destruct B1' as (N,HN). exists (S N). intros n Hn.
   unfold ϵ2, a2, Rpower. rewrite (Rmult_comm (/n)).
   change (_ */ _) with (ln (1-a1 n) / n). rewrite <- E by lia.
   unfold b1 at 3. field. split. apply not_0_INR; lia. apply HN; lia. }
 replace 0 with (0 * (1/2) + 0) by lra.
 apply is_lim_seq_plus'; trivial.
 apply is_lim_seq_mult'.
 { apply is_lim_seq_ext_loc with
    (fun (n:nat) => (ln n)^2/n - 2 * (ln n / n) * ϵ1' n + (ϵ1' n)^2/n).
   { exists 1%nat. intros n Hn.
     unfold b1. field. apply not_0_INR; lia. }
   replace 0 with (0-2*0*0+0) by lra.
   apply is_lim_seq_plus'; [ apply is_lim_seq_minus' |].
   - apply lim_ln2_div_n.
   - apply is_lim_seq_mult'; [ apply is_lim_seq_mult'|];
     trivial using is_lim_seq_const, lim_ln_div_n.
   - simpl. replace 0 with (0*(0*1)*0) by lra.
     apply is_lim_seq_mult'. 2:apply is_lim_seq_invn.
     do 2 (apply is_lim_seq_mult'; trivial). apply is_lim_seq_const. }
 { apply (is_lim_comp_seq _  b1 0 (1/2) exp_taylor2); trivial.
   destruct B1' as (N,HN). exists N.
   intros n Hn [=E']. now apply (HN n Hn). }
Qed.

Lemma ϵ3_lim : is_lim_seq ϵ3 0.
Proof.
 set (ϵ2' := fun n => ln (1-ϵ2 n / ln n)).
 assert (E2' : is_lim_seq ϵ2' 0).
 { rewrite <- ln_1. apply is_lim_seq_continuous.
   - apply continuous_alt, continuous_ln; lra.
   - replace 1 with (1-0*0) at 1 by lra.
     apply is_lim_seq_minus'. apply is_lim_seq_const.
     apply is_lim_seq_mult'. apply ϵ2_lim. apply lim_inv_ln. }
 set (b2 := fun (n:nat) => -(ln n / n) + ln (ln n)/n + ϵ2' n/n).
 assert (E : eventually (fun n => b2 n = ln (1-a2 n)/n)).
 { assert (E2:=ϵ2_lim).
   apply is_lim_seq_spec in E2. destruct (E2 posreal_one) as (N,HN).
   exists (N+3)%nat. intros n Hn.
   unfold b2, ϵ2'. rewrite a2_eqn; try lia.
   assert (Hn' : 3 <= n).
   { replace 3 with (INR 3) by (simpl; lra). apply le_INR; lia. }
   apply Rmult_eq_reg_l with n; try lra. field_simplify; try lra.
   replace (1-(1-_+_)) with (ln n/n * (1 - ϵ2 n/ln n)).
   2:{ field. split; try lra. apply ln_neq_0; lra. }
   assert (1 < ln n).
   { rewrite <- (ln_exp 1). apply ln_increasing; generalize exp_1_itvl; lra. }
   rewrite ln_mult, ln_div; try lra.
   - apply Rdiv_lt_0_compat; lra.
   - specialize (HN n lia). simpl in HN. rewrite Rminus_0_r in HN.
     apply Rabs_def2 in HN.
     apply Rlt_Rminus. rewrite <- Rdiv_lt_1; lra. }
 assert (B2 : is_lim_seq b2 0).
 { replace 0 with (-0+0+0*0) by lra.
   apply is_lim_seq_plus'; [apply is_lim_seq_plus'|].
   - apply is_lim_seq_opp', lim_ln_div_n.
   - apply lim_lnln_div_n.
   - apply is_lim_seq_mult'; trivial. apply is_lim_seq_invn. }
 assert (B2s : is_lim_seq (fun n => b2 n * sqrt n) 0).
 { apply is_lim_seq_ext_loc with
    (fun (n:nat) => - (ln n/sqrt n) + ln (ln n) / sqrt n + ϵ2' n / sqrt n).
   { exists 1%nat. intros n Hn.
     symmetry. unfold b2. rewrite <- (pow2_sqrt n) at 2 4 5 by apply pos_INR.
     field. apply le_INR in Hn. change (INR 1) with 1 in Hn.
     generalize (sqrt_lt_R0 n); lra. }
   replace 0 with (-0+0+0*0) by lra.
   apply is_lim_seq_plus'; [ apply is_lim_seq_plus' | apply is_lim_seq_mult'].
   - apply is_lim_seq_opp', lim_ln_div_sqrt.
   - apply lim_lnln_div_sqrt.
   - trivial.
   - apply lim_inv_sqrt. }
 assert (B2' : eventually (fun n => b2 n <> 0)).
 { clear E B2 B2s.
   apply is_lim_seq_spec in E2'. destruct (E2' posreal_one) as (N,HN).
   exists (N+2)%nat. intros n Hn.
   specialize (HN n lia). simpl in HN. rewrite Rminus_0_r in HN.
   apply Rabs_def2 in HN.
   unfold b2. intros E.
   unfold Rdiv in E. rewrite Ropp_mult_distr_l, <- !Rmult_plus_distr_r in E.
   apply Rmult_integral in E. destruct E as [E|E].
   - assert (LE := exp_ineq1_le (ln (ln n))). rewrite exp_ln in LE. lra.
     rewrite <- ln_1. apply ln_increasing; try lra.
     apply (lt_INR 1); lia.
   - revert E. apply Rinv_neq_0_compat. apply not_0_INR. lia. }
 apply is_lim_seq_ext_loc with
  (fun n => (b2 n^2 * n)*((exp (b2 n) - 1 - b2 n)/(b2 n)^2) + ϵ2' n).
 { destruct E as (N,E).
   destruct B2' as (N',HN'). exists (N+N'+2)%nat. intros n Hn.
   unfold ϵ3, a3, Rpower. rewrite (Rmult_comm (/n)).
   change (_ */ _) with (ln (1-a2 n) / n). rewrite <- E by lia.
   unfold b2 at 3. field. split. apply not_0_INR; lia. apply HN'; lia. }
 replace 0 with (0 * (1/2) + 0) by lra.
 apply is_lim_seq_plus'; [apply is_lim_seq_mult'|]; trivial.
 { apply is_lim_seq_ext with (fun n => (b2 n * sqrt n)^2).
   { intros n. ring_simplify. rewrite pow2_sqrt; try easy. apply pos_INR. }
   replace 0 with (0*(0*1)) by lra.
   do 2 (apply is_lim_seq_mult'; trivial using is_lim_seq_const). }
 { apply (is_lim_comp_seq _  b2 0 (1/2) exp_taylor2); trivial.
   destruct B2' as (N,HN). exists N.
   intros n Hn [=E']. now apply (HN n Hn). }
Qed.

(** Now we relate a2 and a3 and the root of X^k+X-1 *)

Section K.
Variable k:nat.
Hypothesis Hk : (3<=k)%nat.
Let root := tau (k-1).

Lemma root_itvl : 0.68 <= root < 1.
Proof.
 split.
 - apply Rle_trans with (tau 2). generalize tau_2; lra.
   apply tau_incr'; lia.
 - apply tau_itvl.
Qed.

Definition F x := Rpower (1-x) (/k).

Lemma F_fixpoint : F root = root.
Proof.
 assert (E := tau_carac (k-1)). fold root in E.
 replace (S (k-1)) with k in E by lia.
 unfold F. replace (1-root) with (root^k) by lra.
 rewrite <- Rpower_pow, Rpower_mult by (generalize root_itvl; lra).
 replace (k*/k) with 1 by (field; apply not_0_INR; lia).
 apply Rpower_1; generalize root_itvl; lra.
Qed.

Lemma F_fixpoint_inv x : 0<x<1 -> F x = x -> x = root.
Proof.
 intros Hx E.
 apply tau_unique; try lra.
 unfold Ptau. replace (S (k-1)) with k by lia. rewrite <- E at 1.
 unfold F.
 rewrite <- Rpower_pow, Rpower_mult by apply exp_pos.
 replace (/k*k) with 1 by (field; apply not_0_INR; lia).
 rewrite Rpower_1; lra.
Qed.

Lemma F_decr x y : x < y < 1 -> F y < F x.
Proof.
 intros LT. unfold F. apply Rlt_Rpower_l; try lra.
 apply Rinv_0_lt_compat. apply lt_0_INR; lia.
Qed.

Lemma F_1 x : 0 < x < 1 -> F x < 1.
Proof.
 intros Hx.
 replace 1 with (Rpower 1 (/k)).
 2:{ unfold Rpower. now rewrite ln_1, Rmult_0_r, exp_0. }
 apply Rlt_Rpower_l; try lra.
 apply Rinv_0_lt_compat. apply lt_0_INR; lia.
Qed.

Lemma F_low x : 0 < x < root -> root < F x < 1.
Proof.
 intros Hx. split; try apply F_1; try (generalize root_itvl; lra).
 rewrite <- F_fixpoint. apply F_decr; generalize root_itvl; lra.
Qed.

Lemma F_high x : root < x < 1 -> 0 < F x < root.
Proof.
 intros Hx. split. apply exp_pos. rewrite <- F_fixpoint. now apply F_decr.
Qed.

Lemma root_bounds : a2 k < root < a3 k.
Proof.
 assert (H : root < a1 k < 1).
 { apply F_low. unfold a0. generalize exp_m1_itvl root_itvl. lra. }
 apply F_high in H. split. apply H. apply F_low in H. apply H.
Qed.

End K.

(** The final asymptotic equivalence : *)

Lemma root_tau_equiv :
 exists ϵ : nat -> R,
   is_lim_seq ϵ 0 /\
   forall k, (1 < k)%nat -> tau (k-1) = 1 - ln k / k * (1 - ϵ k).
Proof.
 set (ϵ := fun k => 1 - (1 - tau (k-1)) * k / ln k).
 exists ϵ. split.
 2:{ intros k Hk. unfold ϵ. field.
     apply lt_INR in Hk. change (INR 1) with 1 in Hk.
     split; try apply ln_neq_0; lra. }
 apply is_lim_seq_le_le_loc with
   (fun n => 1-(1-a2 n)*n/ln n)
   (fun n => 1-(1-a3 n)*n/ln n).
 { exists 3%nat. intros n Hn.
   assert (R := root_bounds n lia).
   unfold ϵ.
   set (t := tau _) in *.
   unfold Rdiv. rewrite !Rmult_assoc.
   set (c := _ */_).
   assert (0 < c).
   { apply Rmult_lt_0_compat. apply lt_0_INR; lia.
     apply Rinv_0_lt_compat. rewrite <- ln_1.
     apply ln_increasing; try lra. apply (lt_INR 1). lia. }
   nra. }
 - apply is_lim_seq_ext_loc with (fun n => ϵ2 n/ln n).
   { exists 2%nat. intros n Hn. rewrite a2_eqn by lia. field.
     split. apply not_0_INR; lia.
     apply ln_neq_0. apply (not_INR _ 1); lia. apply lt_0_INR; lia. }
   apply is_lim_seq_0_abs with (fun n => Rabs (ϵ2 n)).
   2:{ rewrite <- is_lim_seq_abs_0. apply ϵ2_lim. }
   exists 3%nat. intros n Hn. unfold Rdiv. rewrite Rabs_mult.
   set (c := Rabs (ϵ2 _)).
   rewrite <- (Rmult_1_r c) at 2.
   apply Rmult_le_compat_l. apply Rabs_pos.
   rewrite Rabs_inv, Rabs_pos_eq.
   2:{ rewrite <- ln_1. apply Rcomplements.ln_le; try lra.
       apply (le_INR 1); lia. }
   replace 1 with (/1) by lra. apply Rinv_le_contravar; try lra.
   rewrite <- (ln_exp 1). apply Rcomplements.ln_le. apply exp_pos.
   apply Rle_trans with 3. generalize exp_le_3; lra.
   apply le_INR in Hn; simpl in *; lra.
 - apply is_lim_seq_ext_loc with (fun n:nat => ln (ln n)/ln n + ϵ3 n/ln n).
   { exists 2%nat. intros n Hn. rewrite a3_eqn by lia. field.
     split. apply not_0_INR; lia.
     apply ln_neq_0. apply (not_INR _ 1); lia. apply lt_0_INR. lia. }
   replace 0 with (0+0) by lra.
   apply is_lim_seq_plus'.
   + apply is_lim_comp_seq with (f:=fun x => ln x / x) (x:=Rbar.p_infty);
     trivial using is_lim_div_ln_p, lim_ln. now exists O.
   + apply is_lim_seq_0_abs with (fun n => Rabs (ϵ3 n)).
     2:{ rewrite <- is_lim_seq_abs_0. apply ϵ3_lim. }
     exists 3%nat. intros n Hn. unfold Rdiv. rewrite Rabs_mult.
     set (c := Rabs (ϵ3 n)).
     rewrite <- (Rmult_1_r c) at 2.
     apply Rmult_le_compat_l. apply Rabs_pos.
     rewrite Rabs_inv, Rabs_pos_eq.
     2:{ rewrite <- ln_1. apply ln_le; try lra. apply (le_INR 1); lia. }
     replace 1 with (/1) by lra. apply Rinv_le_contravar; try lra.
     rewrite <- (ln_exp 1). apply ln_le. apply exp_pos.
     apply Rle_trans with 3. generalize exp_le_3; lra.
     apply le_INR in Hn; simpl in *; lra.
Qed.

(* Print Assumptions root_tau_equiv. *)

(** This lead to a [1+ln n/n] equivalent for the positive root of
    X^n-X^(n-1)-1. *)

Lemma root_mu_equiv :
 exists ϵ : nat -> R,
   is_lim_seq ϵ 0 /\
   eventually (fun k => mu (k-1) = 1 + ln k / k * (1 + ϵ k)).
Proof.
 destruct root_tau_equiv as (ϵ & Hϵ & E).
 set (u := fun n:nat => ln n/n * (1 - ϵ n)).
 assert (U : is_lim_seq u 0).
 { replace 0 with (0*(1-0)) by lra.
   apply is_lim_seq_mult'; [|apply is_lim_seq_minus'];
    trivial using is_lim_seq_const, lim_ln_div_n. }
 set (ϵ' := fun n => -ϵ n + (1-ϵ n)*u n/(1-u n)).
 exists ϵ'. split.
 - replace 0 with (-0+(1-0)*0/(1-0)) by lra.
   apply is_lim_seq_plus'.
   + now apply is_lim_seq_opp'.
   + apply is_lim_seq_div'; try lra.
     * apply is_lim_seq_mult'; trivial.
       apply is_lim_seq_minus'; trivial using is_lim_seq_const.
     * apply is_lim_seq_minus'; trivial using is_lim_seq_const.
 - rewrite <- is_lim_seq_spec in U. destruct (U posreal_one) as (N,HN).
   exists (N+2)%nat. intros n Hn. specialize (HN n lia). simpl in HN.
   rewrite Rminus_0_r in HN. apply Rabs_def2 in HN.
   assert (E' : tau (n-1) = 1 - u n).
   { unfold u. rewrite E; try lia. field. apply not_0_INR; lia. }
   rewrite tau_inv, E'.
   replace (/(1-u n)) with (1 + u n + (u n)^2/(1-u n)) by (field; lra).
   unfold ϵ', u. field. split. apply not_0_INR; lia.
   replace (n - _) with (n * (1 - u n)).
   2:{ unfold u. field. apply not_0_INR; lia. }
   intros D. apply Rmult_integral in D. destruct D as [D|D]; try lra.
   revert D. apply not_0_INR; lia.
Qed.

(* Print Assumptions root_mu_equiv. *)
