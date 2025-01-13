From Coq Require Import Lia Reals Lra Ranalysis5 QArith Qcanon.
From Coquelicot Require Import Rcomplements Hierarchy Continuity ElemFct.
From Coquelicot Require Import PSeries Derive AutoDerive.
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

(** Bonus : The sequence u_(n+1) = (1-u_n)^(1/k) converges to the
    positive root of X^k+X-1.
    Here we prove that for the initial point u_0=1-1/e used earlier
    and for 3<=k (in order to have u_0 < root).
    These constraints could be improved someday to 1<=k and any 0<u_0<1 *)

Section K.
Variable k:nat.
Hypothesis Hk : (3<=k)%nat.
Let Hk' : 3<=k. Proof. apply le_INR in Hk. simpl in Hk. lra. Qed.
Let root := tau (k-1).

Local Notation F := (F k).

Definition u n := (F^^n) a0.

(** Position of F(F(x)) with respect to x.
    For easier computations, we work on (1-x^k) instead of F.
    NB: This (1-x^k) is not suitable for a approximation sequence
    (root is a repulsive fixpoint while fixpoints 0 and 1 are attractive).
*)

Definition H x := 1-x^k.
Definition H2 x := 1 - (1-x^k)^k.

Lemma H2_alt x : H2 x = H (H x).
Proof. reflexivity. Qed.

Lemma H_F x : 0<x<1 -> H (F x) = x.
Proof.
 intros Hx. unfold F, H.
 rewrite <- Rpower_pow, Rpower_mult by apply exp_pos.
 rewrite Rinv_l by (apply not_0_INR; lia).
 rewrite Rpower_1; lra.
Qed.

Lemma F_H x : 0<x<1 -> F (H x) = x.
Proof.
 intros Hx. unfold F, H.
 replace (1-_) with (x^k) by lra.
 rewrite <- Rpower_pow, Rpower_mult, Rinv_r, Rpower_1; lra.
Qed.

Lemma F_H_lt x y : 0<x<1 -> 0<y<1 -> x < F y <-> y < H x.
Proof.
 intros Hx Hy. unfold F, H. split; intros LT.
 - assert (x^k < 1-y); try lra.
   rewrite <- (Rpower_1 (1-y)) by lra.
   rewrite <- (Rinv_l k) at 2 by lra.
   rewrite <- Rpower_mult, Rpower_pow by lra.
   apply pow_lt_compat_l; try lia. lra.
 - rewrite <- (Rpower_1 x) by lra.
   rewrite <- (Rinv_r k) at 1 by lra.
   rewrite <- Rpower_mult, Rpower_pow by lra.
   apply Rlt_Rpower_l; try split; try lra.
   apply Rinv_0_lt_compat. apply lt_0_INR; lia.
   apply pow_lt; lra.
Qed.

Lemma F_H_lt' x y : 0<x<1 -> 0<y<1 -> F x < y <-> H y < x.
Proof.
 intros Hx Hy. split; intros LT.
 - apply Rlt_not_le in LT. apply Rnot_le_lt. contradict LT.
   apply Rle_lt_or_eq_dec in LT. destruct LT as [LT | ->].
   + apply F_H_lt in LT; trivial. now apply Rlt_le.
   + rewrite F_H; lra.
 - apply Rlt_not_le in LT. apply Rnot_le_lt. contradict LT.
   apply Rle_lt_or_eq_dec in LT. destruct LT as [LT | ->].
   + apply F_H_lt in LT; trivial. now apply Rlt_le.
   + rewrite H_F; lra.
Qed.

Definition dH2 x := k^2*(x*(1-x^k))^(k-1).

Lemma dH2_ok x : 0<=x<=1 -> is_derive H2 x (dH2 x).
Proof.
 intros Hx. unfold H2, dH2. auto_derive; trivial.
 replace (Nat.pred k)%nat with (k-1)%nat by lia.
 rewrite Rpow_mult_distr. now ring_simplify. (* mais pas ring ?! *)
Qed.

Definition d2H2 x := k^2*(k-1)*(1-(k+1)*x^k)*(x*(1-x^k))^(k-2).

Lemma d2H2_ok x : 0<=x<=1 -> is_derive dH2 x (d2H2 x).
Proof.
 intros Hx. unfold dH2, d2H2. auto_derive; trivial.
 replace (Nat.pred k)%nat with (k-1)%nat by lia.
 replace (Nat.pred (k-1))%nat with (k-2)%nat by lia.
 rewrite minus_INR by lia. change (INR 1) with 1.
 rewrite <- !Rmult_assoc. f_equal.
 replace (x^k) with (x*x^(k-1)); try ring.
 { now replace k with (S (k-1)) at 2 by lia. }
Qed.

Lemma H2_compare_id :
  (forall x, 0 < x < root -> H2 x < x) /\
  (forall x, root < x < 1 -> x < H2 x).
Proof.
 assert (Hroot := root_itvl k Hk). fold root in Hroot.
 set (f := fun x => H2(x)-x).
 set (df := fun x => dH2(x)-1).
 assert (E0 : f 0 = 0).
 { unfold f, H2. rewrite pow_i, !Rminus_0_r, pow1 by lia. lra. }
 assert (E1 : f 1 = 0).
 { unfold f, H2. rewrite pow1. replace (1-1) with 0 by lra.
   rewrite pow_i by lia. lra. }
 assert (Er : f root = 0).
 { unfold f,H2.
   assert (E := tau_carac (k-1)). replace (S (k-1)) with k in E by lia.
   fold root in E. replace (1 - root^k) with root; lra. }
 assert (Df : forall x, 0<=x<=1 -> is_derive f x (df x)).
 { intros x Hx. apply (is_derive_plus (V:=R_NM)). apply dH2_ok; lra.
   auto_derive; trivial. }
 assert (D2f : forall x, 0<=x<=1 -> is_derive df x (d2H2 x)).
 { intros y Hy. rewrite <- (Rminus_0_r (d2H2 y)).
   apply (is_derive_plus (V:=R_NM)). apply d2H2_ok; lra.
   auto_derive; trivial. lra. }
 (* Rolle *)
 destruct (Rolle_weak f df 0 root) as (x1 & X1 & X1');
  intros; try apply Df; try lra.
 (* Rolle, bis *)
 destruct (Rolle_weak f df root 1) as (x2 & X2 & X2');
  intros; try apply Df; try lra.
 (* Rolle, ter *)
 destruct (Rolle_weak df d2H2 x1 x2) as (x3 & X3 & X3');
  intros; try apply D2f; try lra.
 assert (E3 : (k+1)*x3^k = 1).
 { unfold d2H2 in X3'.
   apply Rmult_integral in X3'. destruct X3' as [X3'|X3'].
   - apply Rmult_integral in X3'. destruct X3' as [X3'|X3']; try lra.
     apply Rmult_integral in X3'. destruct X3' as [X3'|X3']; try lra.
     generalize (pow_lt k 2); lra.
   - exfalso; revert X3'. apply pow_nonzero. intros X3'.
     apply Rmult_integral in X3'. destruct X3' as [X3'|X3']; try lra.
     assert (LT : x3^k < 1); try lra.
     { rewrite <- (pow1 k). apply pow_lt_compat_l; try lra. lia. } }
 assert (P2 : forall x, 0<x<x3 -> 0 < d2H2 x).
 { intros x Hx. unfold d2H2.
   repeat (apply Rmult_lt_0_compat); try lra.
   - apply Rlt_Rminus. rewrite <- E3 at 2. apply Rmult_lt_compat_l; try lra.
     apply pow_lt_compat_l. lra. lia.
   - apply pow_lt. apply Rmult_lt_0_compat; try lra.
     apply Rlt_Rminus. rewrite <- (pow1 k). apply pow_lt_compat_l. lra. lia. }
 assert (N2 : forall x, x3<x<1 -> d2H2 x < 0).
 { intros x Hx. unfold d2H2.
   rewrite <- (Ropp_involutive (Rmult _ _)). apply Ropp_lt_gt_0_contravar.
   apply Rlt_gt. rewrite Ropp_mult_distr_l, Ropp_mult_distr_r.
   repeat (apply Rmult_lt_0_compat); try lra.
   - assert (1 < (k+1)*x^k); try lra.
     rewrite <- E3 at 1. apply Rmult_lt_compat_l; try lra.
     apply pow_lt_compat_l. lra. lia.
   - apply pow_lt. apply Rmult_lt_0_compat; try lra.
     apply Rlt_Rminus. rewrite <- (pow1 k). apply pow_lt_compat_l. lra. lia. }
 clear X3' E3.
 assert (N1a : forall x, 0<x<x1 -> df x < 0).
 { intros x Hx. rewrite <- X1'.
   apply (incr_function_le df x x1 d2H2); simpl; intros;
     try apply D2f; try apply P2; lra. }
 assert (P1 : forall x, x1<x<x2 -> 0 < df x).
 { intros x Hx.
   destruct (Rle_or_lt x x3) as [Hx'|Hx'].
   + destruct (MVT_weak df d2H2 x1 x) as (c & Hc & Hc'); try lra.
     { intros. apply D2f; lra. }
     rewrite X1', Rminus_0_r in Hc'. rewrite Hc'.
     apply Rmult_lt_0_compat; try lra. apply P2; lra.
   + rewrite <- X2'.
     apply Ropp_lt_cancel.
     apply (incr_function_le (fun x => -df x) x x2 (fun x => -d2H2 x)); simpl;
       intros; try lra.
     * apply (is_derive_opp (V:=R_NM)). apply D2f; lra.
     * rewrite <- Ropp_0. apply Ropp_lt_contravar. apply N2; lra. }
 assert (N1b : forall x, x2<x<1 -> df x < 0).
 { intros x Hx. rewrite <- X2'.
   apply Ropp_lt_cancel.
   apply (incr_function_le (fun x => -df x) x2 x (fun x => -d2H2 x)); simpl;
   intros; try lra.
   - apply (is_derive_opp (V:=R_NM)). apply D2f; lra.
   - rewrite <- Ropp_0. apply Ropp_lt_contravar. apply N2; lra. }
 clear X1' X2' x3 X3 P2 N2.
 split.
 - intros x Hx. clear N1b.
   apply Rminus_lt. change (f x < 0).
   destruct (Rle_or_lt x x1) as [Hx'|Hx'].
   + destruct (MVT_weak f df 0 x) as (c & Hc & Hc'); try lra.
     { intros. apply Df; lra. }
     rewrite E0, !Rminus_0_r in Hc'. rewrite Hc'.
     replace 0 with (0*x) by lra. apply Rmult_lt_compat_r; try lra.
     apply N1a; lra.
   + destruct (MVT_weak f df x root) as (c & Hc & Hc'); try lra.
     { intros. apply Df; lra. }
     rewrite Er in Hc'. apply Rminus_lt_0. rewrite Hc'.
     apply Rmult_lt_0_compat; try apply P1; lra.
 - intros x Hx. clear N1a.
   apply Rminus_lt_0. change (0 < f x).
   destruct (Rle_or_lt x x2) as [Hx'|Hx'].
   + destruct (MVT_weak f df root x) as (c & Hc & Hc'); try lra.
     { intros. apply Df; lra. }
     rewrite Er, !Rminus_0_r in Hc'. rewrite Hc'.
     apply Rmult_lt_0_compat; try apply P1; lra.
   + destruct (MVT_weak f df x 1) as (c & Hc & Hc'); try lra.
     { intros. apply Df; lra. }
     rewrite E1 in Hc'. apply Rminus_lt. rewrite Hc'.
     replace 0 with (0*(1-x)) by lra. apply Rmult_lt_compat_r; try lra.
     apply N1b; lra.
Qed.

Lemma H2_low x : 0 < x < root -> H2 x < x.
Proof. apply H2_compare_id. Qed.

Lemma H2_high x : root < x < 1 -> x < H2 x.
Proof. apply H2_compare_id. Qed.

Lemma FF_low x : 0 < x < root -> x < F (F x).
Proof.
 intros Hx. assert (Hroot := root_itvl k Hk). fold root in Hroot.
 apply F_H_lt; try lra. split. apply exp_pos. apply F_1; trivial. lra.
 apply F_H_lt'; try lra. 2:apply H2_low; lra. split.
 - unfold H. assert (x^k < 1^k). apply pow_lt_compat_l; try lra. lia.
   rewrite pow1 in *. lra.
 - unfold H. assert (0<x^k). apply pow_lt; lra. lra.
Qed.

Lemma FF_high x : root < x < 1 -> F (F x) < x.
Proof.
 intros Hx. assert (Hroot := root_itvl k Hk). fold root in Hroot.
 apply F_H_lt'; try lra.
 split. apply exp_pos. apply F_1; trivial. lra.
 apply F_H_lt; try lra. 2:apply H2_high; lra. split.
 - unfold H. assert (x^k < 1^k). apply pow_lt_compat_l; try lra. lia.
   rewrite pow1 in *. lra.
 - unfold H. assert (0<x^k). apply pow_lt; lra. lra.
Qed.

Lemma FF_fixpoint x : 0<x<1 -> F (F x) = x <-> x = root.
Proof.
 intros Hx. split.
 - intros E. destruct (Rtotal_order x root) as [LT|[EQ|LT]]; trivial.
   + generalize (FF_low x). lra.
   + generalize (FF_high x). lra.
 - intros ->. now rewrite 2 F_fixpoint.
Qed.

Lemma F_continuous x : 0<x<1 -> continuous F x.
Proof.
 intros Hx. unfold F, Rpower.
 apply continuous_comp; [ | apply continuous_exp ].
 apply (continuous_mult (K:=R_AbsRing)); [ apply continuous_const | ].
 apply continuous_comp; [ | apply continuous_ln; lra ].
 apply (continuous_plus (V:=R_NM)); [ apply continuous_const | ].
 apply (continuous_opp (V:=R_NM)), continuous_id.
Qed.

Definition u2 n := u (2*n).

Lemma u2_below_root n : 0 < u2 n < root.
Proof.
 induction n.
 - unfold u2. simpl. unfold a0.
   generalize exp_m1_itvl (root_itvl k Hk). fold root. lra.
 - unfold u2. simpl. replace (n + _)%nat with (S (2*n))%nat by lia.
   now apply F_high, F_low.
Qed.

Lemma u2_incr n : u2 n < u2 (S n).
Proof.
 unfold u2. replace (2*S n)%nat with (S (S (2*n)))%nat by lia.
 apply FF_low. apply u2_below_root.
Qed.

Lemma u2_lim : is_lim_seq u2 root.
Proof.
 assert (X : ex_lim_seq u2).
 { apply ex_lim_seq_incr. intros n. apply Rlt_le, u2_incr. }
 destruct X as (l,Hl).
 assert (Rbar.Rbar_le a0 l).
 { apply is_lim_seq_le with (fun _ => a0) u2;
    trivial using is_lim_seq_const. intros.
   induction n. apply Rle_refl. generalize (u2_incr n); lra. }
 assert (Rbar.Rbar_le l root).
 { apply is_lim_seq_le with u2 (fun _ => root);
    trivial using is_lim_seq_const. intros. apply Rlt_le, u2_below_root. }
 destruct l as [ l | | ]; try easy. simpl in *.
 assert (0 < l < 1).
 { assert (Hroot := root_itvl k Hk). fold root in Hroot. split; try lra.
   unfold a0 in *. generalize exp_m1_itvl. lra. }
 assert (Hl' : is_lim_seq u2 (F (F l))).
 { apply (is_lim_seq_incr_1 u2).
   apply is_lim_seq_ext with (fun n => F (F (u2 n))).
   { intros n. unfold u2.
     replace (2*S n)%nat with (S (S (2*n)))%nat by lia. easy. }
   apply (is_lim_seq_continuous (fun x => F (F x)) u2); trivial.
   apply continuous_alt, continuous_comp; apply F_continuous; try lra.
   split. apply exp_pos. apply F_1; trivial. }
 assert (E : F (F l) = l).
 { apply is_lim_seq_unique in Hl, Hl'. congruence. }
 apply FF_fixpoint in E; subst; trivial.
Qed.

Lemma u2bis_lim : is_lim_seq (fun n => u (S (2*n))) root.
Proof.
 unfold root. rewrite <- F_fixpoint; trivial. fold root.
 apply (is_lim_seq_continuous F u2); try apply u2_lim.
 apply continuous_alt, F_continuous.
 generalize (root_itvl k Hk). fold root. lra.
Qed.

(** We glue everything : u is an alternating sequence converging to root *)

Lemma u_lim : is_lim_seq u root.
Proof.
 assert (U := u2_lim).
 assert (U' := u2bis_lim).
 unfold u2 in *.
 rewrite <- is_lim_seq_spec in *.
 intro eps.
 destruct (U eps) as (N,HN).
 destruct (U' eps) as (N',HN').
 exists (Nat.max (2*N) (2*N'+1)). intros n Hn.
 destruct (Nat.Even_or_Odd n) as [Ev|Od].
 - assert (Hn' : (n = 2 * (Nat.div2 n))%nat).
   { rewrite <- Nat.double_twice. now apply Nat.Even_double. }
   rewrite Hn'. apply HN. apply Nat.mul_le_mono_pos_l with 2%nat; lia.
 - assert (Hn' : (n = S (2 * (Nat.div2 n))%nat)).
   { rewrite <- Nat.double_twice. now apply Nat.Odd_double. }
   rewrite Hn'. apply HN'. apply Nat.mul_le_mono_pos_l with 2%nat; lia.
Qed.

End K.
