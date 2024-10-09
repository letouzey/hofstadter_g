From Coq Require Import Arith Lia QArith Reals Lra Qreals.
From QuantumLib Require Import Complex.
Require Import MoreFun MoreList MoreReals MoreLim MoreComplex.
Require Import DeltaList GenFib GenG GenAdd Words Mu ThePoly Approx.
Local Open Scope Z.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * Studying case k=2

   We focus here on the case k=2, compute the complex roots of [X^3-X^2-1],
   and express (A 2 n) in term of combinations of powers of these roots.
   Then we study the frequencies in [Words.kseq 2], and the behaviour of
   function [h] (i.e. [f 2]).
*)

Definition μ := mu 2.
Definition τ := tau 2.

Definition re_α := (1 - μ)/2.
Definition im_α := sqrt (τ * (3+τ))/2.

Definition α : C := (re_α, im_α).
Definition αbar : C := (re_α, - im_α).

Lemma τ3 : τ^3 = 1 - τ.
Proof.
 generalize (tau_carac 2). fold τ. lra.
Qed.

Lemma τ4 : τ^4 = τ - τ^2.
Proof.
 change (τ^4) with (τ*τ^3). rewrite τ3. ring.
Qed.

Lemma τ234 : τ^2 + τ^3 + τ^4 = 1.
Proof.
 rewrite τ3, τ4; ring.
Qed.

Lemma τ5 : τ^5 = τ + τ^2 - 1.
Proof.
 change (τ^5) with (τ*τ^4). rewrite τ4. ring_simplify.
 rewrite τ3. ring.
Qed.

Lemma τ6 : τ^6 = (1-τ)^2.
Proof.
 rewrite <- τ3. ring.
Qed.

#[local] Instance μ_approx : Approx 1.465571231876 μ 1.465571231877.
Proof.
 red. unfold μ. generalize mu_2. lra.
Qed.

#[local] Instance τ_approx : Approx 0.6823278038280 τ 0.6823278038281.
Proof.
 red. unfold τ. generalize tau_2. lra.
Qed.

#[local] Instance τ2_approx : Approx 0.465570 (τ^2) 0.465572.
Proof. approx. Qed.

Lemma re_α_alt : re_α = - τ^2 / 2.
Proof.
 unfold re_α. f_equal.
 unfold μ. rewrite tau_inv. fold τ.
 assert (τ <> 0) by approx.
 apply Rmult_eq_reg_l with τ; trivial.
 field_simplify; trivial. rewrite τ3. lra.
Qed.

Lemma im_α_2 : im_α ^ 2 = τ * (3+τ) / 4.
Proof.
 unfold im_α.
 unfold Rdiv.
 rewrite Rpow_mult_distr, pow2_sqrt; try lra. approx.
Qed.

Lemma αmod2 : (Cmod α)^2 = τ.
Proof.
 unfold Cmod.
 rewrite pow2_sqrt.
 2: generalize (pow2_ge_0 (fst α)) (pow2_ge_0 (snd α)); lra.
 unfold α; simpl. ring_simplify.
 rewrite im_α_2. rewrite re_α_alt.
 field_simplify. rewrite τ4. field.
Qed.

Lemma τ_as_μ : τ = μ*(μ-1).
Proof.
 change τ with (/μ). apply Rmult_eq_reg_l with μ. 2:approx.
 field_simplify. 2:approx. unfold μ. rewrite mu_carac. ring.
Qed.

#[local] Instance αmod_approx :
  Approx 0.8260313576541 (Cmod α) 0.8260313576543 |20.
Proof.
 apply pow2_approx_inv; try qle; try apply Cmod_ge_0.
 rewrite αmod2. approx.
Qed.

#[local] Instance im_α_approx : Approx 0.79255199 im_α 0.792552.
Proof.
 apply pow2_approx_inv; try qle. rewrite im_α_2. approx.
 unfold im_α. generalize (sqrt_pos (τ*(3+τ))). lra.
Qed.

Lemma μ_is_root : (μ ^3 = μ ^2 + 1)%C.
Proof.
 rewrite !RtoC_pow, <- RtoC_plus. unfold μ. now rewrite (mu_carac 2).
Qed.

Lemma α_is_root : (α^3 = α^2 + 1)%C.
Proof.
 simpl. rewrite !Cmult_1_r. unfold α. unfold Cmult; simpl.
 unfold Cplus; simpl. f_equal; ring_simplify.
 - rewrite im_α_2, re_α_alt.
   field_simplify. rewrite τ6, τ4, τ3. field.
 - change (im_α ^ 3) with (im_α * im_α^2).
   rewrite im_α_2, re_α_alt.
   field_simplify. rewrite τ4. field.
Qed.

Lemma αbar_is_root : (αbar^3 = αbar^2 + 1)%C.
Proof.
 change αbar with (Cconj α).
 rewrite <- !Cpow_conj. rewrite α_is_root.
 rewrite Cconj_plus_distr. f_equal. compute; f_equal; lra.
Qed.

Lemma re_α_nz : re_α <> 0.
Proof.
 unfold re_α. approx.
Qed.

Lemma im_α_pos : 0 < im_α.
Proof.
 unfold im_α. apply Rlt_mult_inv_pos; try lra.
 apply sqrt_lt_R0. approx.
Qed.

Lemma im_α_nz : im_α <> 0.
Proof.
 generalize im_α_pos; lra.
Qed.

Lemma distinct_roots :
  α <> μ /\ αbar <> μ /\ α <> αbar.
Proof.
 unfold α, αbar, RtoC; repeat split.
 - intros [= A B]. now destruct im_α_nz.
 - intros [= A B]. generalize im_α_nz. lra.
 - intros [= B]. generalize im_α_nz. lra.
Qed.

(** Elementary symmetric functions between roots *)

Lemma roots_sum : (μ+α+αbar = 1)%C.
Proof.
 unfold Cplus. simpl. change 1%C with (1,0).
 f_equal; unfold re_α; field.
Qed.

Lemma roots_prod : (μ*α*αbar = 1)%C.
Proof.
 rewrite <- Cmult_assoc, <- Cmod2_conj, αmod2, <- RtoC_mult.
 unfold μ, τ, tau. f_equal. apply Rinv_r. approx.
Qed.

Lemma sigma2_nul : (μ*α + μ*αbar + α*αbar = 0)%C.
Proof.
 rewrite <- Cmod2_conj, αmod2.
 replace (μ * α + μ * αbar)%C with (μ*(α+αbar))%C by ring.
 replace (α+αbar)%C with (1-μ)%C by (rewrite <- roots_sum; ring).
 rewrite <- RtoC_minus, <- RtoC_mult, <- RtoC_plus. f_equal.
 rewrite τ_as_μ. ring.
Qed.

Lemma roots_sum2 : (μ^2 + α^2 + αbar^2 = 1)%C.
Proof.
 replace 1%C with (1^2-2*0)%C by lca.
 rewrite <- roots_sum, <- sigma2_nul. ring.
Qed.

Definition roots2 := [RtoC μ; α; αbar].

Lemma roots2_sorted : SortedRoots 2 roots2.
Proof.
 split.
 - unfold roots2, ThePoly. simpl.
   rewrite !Cmult_1_l, !Cmult_1_r, !Cplus_0_l, !Cplus_0_r.
   replace (- αbar * - α * - μ)%C with (- (μ * α *αbar))%C by lca.
   replace (- αbar + - α + - μ)%C with (- (μ + α + αbar))%C by lca.
   replace (- αbar * - α + _)%C with (μ*α + μ*αbar + α*αbar)%C by lca.
   rewrite roots_sum, roots_prod, sigma2_nul.
   reflexivity.
 - do 2 constructor.
   + repeat constructor.
   + constructor. right. unfold α, αbar. simpl. split; trivial. approx.
   + left. unfold α. simpl. approx.
Qed.


(** More root powers *)

Ltac simpl_root := repeat (autorewrite with root; ring_simplify).
#[local] Hint Rewrite μ_is_root α_is_root αbar_is_root : root.

Lemma μ4 : (μ^4 = 1 + μ + μ^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

Lemma α4 : (α^4 = 1 + α + α^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

Lemma αbar4 : (αbar^4 = 1 + αbar + αbar^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

#[local] Hint Rewrite μ4 α4 αbar4 : root.

Lemma μ5 : (μ^5 = 1 + μ + 2*μ^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

Lemma α5 : (α^5 = 1 + α + 2*α^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

Lemma αbar5 : (αbar^5 = 1 + αbar + 2*αbar^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

#[local] Hint Rewrite μ5 α5 αbar5 : root.

Lemma μ6 : (μ^6 = 2 + μ + 3*μ^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

Lemma α6 : (α^6 = 2 + α + 3*α^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

Lemma αbar6 : (αbar^6 = 2 + αbar + 3*αbar^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

#[local] Hint Rewrite μ6 α6 αbar6 : root.

Lemma α7 : (α^7 = 3 + 2*α + 4*α^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.
#[local] Hint Rewrite α7 : root.

Lemma α8 : (α^8 = 4 + 3*α + 6*α^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.
#[local] Hint Rewrite α8 : root.

(** Explicit decomposition of [A 2 n] into a linear combination
    of root powers.
    This is less useful now that we have general results for any k,
    see ThePoly.coefs_LinCombA and Freq.A_ratio for instance.
    But these general results do not provide expressions for the
    coefficients, unlike [coef_α] and [coef_μ] below.
    For that, we manually invert the Vandermonde(μ,α,αbar) matrix,
    and first compute its determinant. *)

Definition det : C := ((μ-α)*(μ-αbar)*(α-αbar))%C.

Lemma det2 : (det^2 = -31)%C.
Proof.
 unfold det.
 replace ((μ - α) * (μ - αbar))%C with (μ*(3*μ-2))%C.
 2:{ ring_simplify. rewrite <- Cmod2_conj, αmod2.
     replace (_+-1*μ*α+-1*μ*αbar)%C with (μ^2-μ*(1-μ))%C
       by (rewrite <- roots_sum; ring).
     rewrite τ_as_μ. rewrite RtoC_mult, RtoC_minus. ring. }
 rewrite im_alt'. change (Im α) with im_α. unfold im_α.
 rewrite !Cpow_mul_l.
 rewrite <- !RtoC_mult, <- RtoC_minus, !RtoC_pow, <- !RtoC_mult.
 unfold Rdiv. rewrite Rpow_mult_distr, pow2_sqrt by approx.
 rewrite pow_inv.
 replace (2^2) with 4 by lra.
 simpl (Ci^2)%C. rewrite Cmult_1_r, Ci2.
 rewrite <- RtoC_opp, <- !RtoC_mult. f_equal.
 change τ with (/μ). field_simplify. 2:approx.
 unfold μ. rewrite mu_carac. field.
Qed.

Lemma det_eqn : (det = Ci * sqrt 31)%C.
Proof.
 assert (0 <= Im det).
 { unfold det.
   replace (μ-αbar)%C with (Cconj (μ-α))%C.
   2:{ now rewrite Cconj_minus_distr, Cconj_R. }
   rewrite <- Cmod2_conj, im_scal_l, im_alt'.
   replace (2*Ci*Im α)%C with ((2*Im α)*Ci)%C by ring.
   rewrite <- RtoC_mult, im_scal_l. change (Im Ci) with 1.
   rewrite Rmult_1_r. change (Im α) with im_α.
   apply Rmult_le_pos.
   - rewrite <- Rsqr_pow2. apply Rle_0_sqr.
   - generalize im_α_pos. nra. }
 generalize det2.
 destruct det as (x,y). simpl in *. rewrite Cmult_1_r.
 unfold Ci. unfold Cmult; simpl. rewrite !Rmult_0_l, !Rmult_1_l.
 intros [= RE IM].
 ring_simplify in IM. rewrite Rmult_assoc in IM.
 apply Rmult_integral in IM. destruct IM as [IM|IM]; [lra| ].
 apply Rmult_integral in IM. destruct IM; subst; try nra.
 f_equal; try ring. ring_simplify. symmetry. apply sqrt_lem_1; lra.
Qed.

Lemma det_nz : det <> 0.
Proof.
 rewrite det_eqn. rewrite Cmult_integral. intros [[= E] | E]; try lra.
 apply RtoC_inj in E. apply sqrt_eq_0 in E; lra.
Qed.

Definition coef_μ : R := 2 * μ^4 * im_α / sqrt 31.

Definition coef_α : C := α^4 * (αbar - μ) / det.
Definition coef_αbar := Cconj coef_α.

#[local] Instance sqrt_31 : Approx 5.5677 (sqrt 31) 5.5678.
Proof.
 eapply pow2_approx_inv; try lra; try apply sqrt_pos.
 rewrite <-Rsqr_pow2, Rsqr_sqrt; approx.
Qed.

#[local] Instance coef_μ_bound : Approx 1.3134 coef_μ 1.3135.
Proof.
 unfold coef_μ. approx.
Qed.

Lemma coef_μ_alt1 : (RtoC coef_μ = μ^4 * (α-αbar) / det)%C.
Proof.
 unfold coef_μ. rewrite det_eqn. change im_α with (Im α).
 rewrite im_alt'. rewrite RtoC_div, !RtoC_mult, RtoC_pow by approx.
 field. split. negapply RtoC_inj. approx. intros [= E]; lra.
Qed.

Lemma coef_μ_alt2 : coef_μ = μ^3 * sqrt ((3*μ+1)/31).
Proof.
 unfold coef_μ. rewrite sqrt_div_alt by lra.
 unfold Rdiv. rewrite <- Rmult_assoc. f_equal.
 replace (2*μ^4*im_α) with (μ^3*(μ*2*im_α)) by ring. f_equal.
 unfold im_α. field_simplify.
 apply Rsqr_inj; try apply sqrt_pos.
 - apply Rmult_le_pos. approx. apply sqrt_pos.
 - rewrite Rsqr_mult, !Rsqr_sqrt by approx. rewrite Rsqr_pow2.
   unfold τ, tau. fold μ. field. approx.
Qed.

Lemma coef_αbar_alt : (coef_αbar = αbar^4 * (μ-α) / det)%C.
Proof.
 unfold coef_αbar, coef_α.
 rewrite Cdiv_conj by apply det_nz.
 rewrite Cconj_mult_distr, Cpow_conj, Cconj_minus_distr, Cconj_R.
 change (Cconj α) with αbar.
 replace (Cconj αbar) with α.
 2:{ symmetry. change αbar with (Cconj α). apply Cconj_involutive. }
 replace (Cconj det) with (- det)%C.
 2:{ rewrite det_eqn. rewrite Cconj_mult_distr, Cconj_R, Ci_conj. lca. }
 field. apply det_nz.
Qed.

(** Verification of the desired equations about the coefficients *)

Lemma coefs_eqn1 : coef_μ + 2 * Re coef_α = 1.
Proof.
 apply RtoC_inj. rewrite RtoC_plus, RtoC_mult, re_alt.
 fold coef_αbar. rewrite coef_αbar_alt, coef_μ_alt1. unfold coef_α.
 apply Cmult_eq_reg_l with det; try field_simplify; try apply det_nz.
 apply Ceq_minus. unfold det. rewrite μ4, α4, αbar4. ring.
Qed.

Lemma coefs_eqn2 : coef_μ * μ + 2 * Re (coef_α * α) = 2.
Proof.
 apply RtoC_inj. rewrite RtoC_plus, !RtoC_mult, re_alt.
 rewrite Cconj_mult_distr. change (Cconj α) with αbar.
 fold coef_αbar. rewrite coef_αbar_alt, coef_μ_alt1. unfold coef_α.
 apply Cmult_eq_reg_l with det; try field_simplify; try apply det_nz.
 apply Ceq_minus. unfold det. rewrite μ5, α5, αbar5. ring.
Qed.

Lemma coefs_eqn3 : coef_μ * μ^2 + 2 * Re (coef_α * α^2) = 3.
Proof.
 apply RtoC_inj. rewrite RtoC_plus, !RtoC_mult, <- !RtoC_pow, re_alt.
 rewrite Cconj_mult_distr, !Cpow_conj. change (Cconj α) with αbar.
 fold coef_αbar. rewrite coef_αbar_alt, coef_μ_alt1. unfold coef_α.
 apply Cmult_eq_reg_l with det; try field_simplify; try apply det_nz.
 apply Ceq_minus. unfold det. rewrite μ6, α6, αbar6. ring.
Qed.

Lemma A2_eqn n : INR (A 2 n) = coef_μ * μ ^n + 2 * Re (coef_α * α^n).
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
     rewrite pow_add. unfold μ. rewrite (mu_carac 2). fold μ.
     rewrite Cpow_add_r. rewrite α_is_root.
     rewrite plus_INR.
     rewrite (IH n) by lia. rewrite (IH (n-2)%nat) by lia.
     rewrite Cmult_plus_distr_r, Cmult_plus_distr_l, re_plus.
     ring_simplify. rewrite Rmult_assoc, <-pow_add.
     replace (n-2+2)%nat with n by lia.
     rewrite <- Cpow_add_r.
     replace (2+(n-2))%nat with n by lia.
     rewrite Cmult_1_l. lra.
Qed.

Lemma A2_div_μ_n n : A 2 n / μ ^n = coef_μ + 2 * Re (coef_α * (α/μ)^n).
Proof.
 assert (μ <> 0) by approx.
 assert (μ^n <> 0). { now apply pow_nonzero. }
 unfold Cdiv. rewrite Cpow_mul_l, Cpow_inv by (negapply RtoC_inj; auto).
 rewrite Cmult_assoc, RtoC_pow, <- RtoC_inv, re_scal_r by trivial.
 rewrite A2_eqn. field; trivial.
Qed.

Lemma Cmod_α_μ : Cmod (α/μ) < 1.
Proof.
 assert (0 < μ) by approx.
 assert (0 < τ) by approx.
 apply Rlt_pow2_inv; try lra.
 rewrite Cmod_div by (negapply RtoC_inj; lra).
 rewrite Cmod_R, Rabs_right by lra.
 unfold Rdiv. rewrite Rpow_mult_distr. rewrite αmod2. approx.
Qed.

Lemma Lim_A2_div_μ_n : is_lim_seq (fun n => A 2 n / μ ^ n) coef_μ.
Proof.
 apply is_lim_seq_ext with
  (u := fun n => coef_μ + 2 * Re (coef_α * (α/μ)^n)).
 { intros n. now rewrite A2_div_μ_n. }
 replace (Rbar.Finite coef_μ) with (Rbar.Finite (coef_μ + 0))
   by (f_equal; lra).
 apply is_lim_seq_plus'; [apply is_lim_seq_const|].
 apply is_lim_seq_0_abs with
  (v := fun n => 2 * Cmod coef_α * (Cmod (α/μ))^n).
 - intros n.
   rewrite Rabs_mult. rewrite (Rabs_right 2) by lra.
   rewrite Rmult_assoc, <- Cmod_pow, <- Cmod_mult.
   apply Rmult_le_compat_l; try lra.
   apply re_le_Cmod.
 - replace 0 with ((2*Cmod coef_α) * 0) by lra.
   apply is_lim_seq_mult'; [apply is_lim_seq_const|].
   apply is_lim_seq_geom.
   rewrite Rabs_right by (apply Rle_ge, Cmod_ge_0).
   apply Cmod_α_μ.
Qed.

(** See also Freq.A_ratio now: *)

Lemma Lim_A2_ratio : is_lim_seq (fun n => A 2 (S n) / A 2 n) μ.
Proof.
 assert (μ_pos : 0 < μ ) by approx.
 assert (coef_μ <> 0) by approx.
 apply is_lim_seq_ext with
     (u := fun n => μ * ((A 2 (S n) / μ ^ (S n)) / (A 2 n / μ ^ n))).
 - intros n. simpl pow. field; repeat split; try lra.
   + change 0 with (INR 0). negapply INR_eq. generalize (A_nz 2 n). lia.
   + generalize (pow_lt _ n μ_pos). lra.
 - replace (Rbar.Finite μ) with (Rbar.Rbar_mult μ (coef_μ / coef_μ)).
   2:{ simpl. f_equal. field; auto. }
   apply is_lim_seq_scal_l.
   assert (L := Lim_A2_div_μ_n).
   apply is_lim_seq_div'; auto.
   rewrite is_lim_seq_incr_1 in L. apply L.
Qed.

(** Note: the coefficients coef_μ and coef_α and coef_αbar
    are the roots of the polynomial [X^3-X^2-(12/31)*X-1/31].
    For proving that, we need first some more identities about
    these coefficients. *)

Lemma coef_sum : (coef_μ+coef_α+coef_αbar = 1)%C.
Proof.
 rewrite <- coefs_eqn1, RtoC_plus, RtoC_mult, re_alt.
 unfold coef_αbar. field.
Qed.

Lemma coef_prod : (coef_μ * coef_α * coef_αbar = 1/31)%C.
Proof.
 rewrite coef_μ_alt1, coef_αbar_alt. unfold coef_α.
 replace (_*_)%C with (-(μ*α*αbar)^4* det/det^3)%C.
 2:{ unfold det at 1. field. apply det_nz. }
 rewrite roots_prod. field_simplify. rewrite det2. lca. apply det_nz.
Qed.

Lemma coef_μ2 : (31 * coef_μ^2 = 15*μ^2 + 7*μ + 11)%C.
Proof.
 rewrite coef_μ_alt2.
 rewrite RtoC_pow, Rpow_mult_distr, pow2_sqrt by approx.
 rewrite RtoC_mult, RtoC_div, <- !RtoC_pow, RtoC_plus, RtoC_mult by lra.
 field_simplify. rewrite Cpow_S. now simpl_root.
Qed.

Lemma coef_α2 : (31 * coef_α^2 = 15*α^2 + 7*α + 11)%C.
Proof.
 unfold coef_α. rewrite (Cpow_S _ 3). rewrite α_is_root.
 unfold Cdiv.
 assert (α <> 0). { unfold α. intros [= E _]. revert E. approx. }
 rewrite !Cpow_mul_l, Cpow_inv, det2 by apply det_nz.
 replace ((αbar-μ)^2)%C with ((1-α^2)-2*(1/α))%C.
 2:{ rewrite <- roots_sum2 at 1. rewrite <- roots_prod at 1. now field. }
 field_simplify; trivial. simpl_root. field.
Qed.

Lemma coef_αbar2 : (31 * coef_αbar^2 = 15*αbar^2 + 7*αbar + 11)%C.
Proof.
 unfold coef_αbar.
 rewrite <- Cpow_conj. rewrite <- (Cconj_R 31).
 rewrite <- Cconj_mult_distr, coef_α2.
 now rewrite !Cconj_plus_distr, !Cconj_mult_distr, Cpow_conj, !Cconj_R.
Qed.

Lemma coef_squares : (coef_μ^2+coef_α^2+coef_αbar^2 = 55/31)%C.
Proof.
 apply Cmult_eq_reg_l with (RtoC 31); [|negapply RtoC_inj; lra].
 field_simplify.
 rewrite coef_μ2, coef_α2, coef_αbar2.
 replace (RtoC 55) with (15*1+7*1+33)%C by lca.
 rewrite <- roots_sum2 at 1. rewrite <- roots_sum at 1. ring.
Qed.

Lemma coef_sigma2 :
  (coef_μ * coef_α + coef_α * coef_αbar + coef_αbar * coef_μ = -12/31)%C.
Proof.
 replace (_+_)%C with ((1^2-(55/31))/2)%C; try lca.
 rewrite <- coef_sum, <- coef_squares. field.
Qed.

Lemma poly_coefs (X:C) :
  ((X - coef_μ)*(X - coef_α)*(X - coef_αbar) = X^3-X^2-(12/31)*X-1/31)%C.
Proof.
 rewrite <- coef_prod.
 rewrite <- (Cmult_1_l (X^2)), <- coef_sum.
 unfold Cminus at 5.
 replace (-X^2)%C with (- (1*X^2))%C by field.
 replace (-(12/31 * X))%C with ((-12/31) * X)%C by field.
 rewrite <- coef_sigma2.
 field.
Qed.

Lemma coef_μ_poly : coef_μ^3 - coef_μ^2 - (12/31)*coef_μ - 1/31 = 0.
Proof.
 apply RtoC_inj.
 rewrite !RtoC_minus, !RtoC_mult, !RtoC_div, <- !RtoC_pow by lra.
 rewrite <- poly_coefs. ring.
Qed.

Lemma coef_α_poly : (coef_α^3 - coef_α^2 - (12/31)*coef_α - 1/31 = 0)%C.
Proof.
 rewrite <- poly_coefs. ring.
Qed.


(** ** Occurrences of letters in morphic word [Words.kseq 2]

    We will see below how this relates to function [h] (a.k.a [f 2])
    and its iterate [h^^2].

    For a finite word [w], the frequency of letter [a] is
    [nbocc a w / length w]. For infinite words, the frequency
    of a letter (if it exists) is the limit of frequencies for
    ever-growing finite prefixes of the infinite word.

    Here for [Words.kseq 2], the frequencies of letters [0],[1],[2]
    will be respectively [τ^3],[τ^4],[τ^2] (another numbering
    of letters would make that more uniform). For proving that and
    even more, we now consider the following differences :
*)

Definition Diff0 w := τ^3 * length w - nbocc 0 w.
Definition Diff1 w := τ^4 * length w - nbocc 1 w.
Definition Diff2 w := τ^2 * length w - nbocc 2 w.

Definition diff0 n := Diff0 (take n (kseq 2)).
Definition diff1 n := Diff1 (take n (kseq 2)).
Definition diff2 n := Diff2 (take n (kseq 2)).

(** One of these differences can be deduced from the other two.
    We now forget about diff1 and consider only diff0 and diff2
    (that have nice links with [h] and [h^^2]). *)

Lemma Diff012 w :
 List.Forall (fun a => a <= 2)%nat w ->
 Diff0 w + Diff1 w + Diff2 w = 0.
Proof.
 intros H.
 apply nbocc_total_le in H. simpl in H.
 unfold Diff0, Diff1, Diff2.
 rewrite τ3, τ4. ring_simplify.
 rewrite H, !plus_INR. change (INR 0) with 0. ring.
Qed.

Lemma diff012 n : diff0 n + diff1 n + diff2 n = 0.
Proof.
 apply Diff012.
 apply Forall_nth. intros i d. rewrite take_length. intros H.
 rewrite take_nth by trivial. apply kseq_letters.
Qed.

(** Expressing diff0 and diff2 in terms of [h] and [h^^2] *)

Lemma diff0_alt n : diff0 n = h n - τ * n.
Proof.
 unfold diff0, Diff0. rewrite take_length.
 rewrite <- count_nbocc.
 rewrite τ3. rewrite Rmult_minus_distr_r.
 rewrite <- (f_count_0 2 n) at 1 by easy. fold h. rewrite plus_INR. lra.
Qed.

Lemma diff2_alt n : diff2 n = τ^2 * n - (h^^2) n.
Proof.
 unfold diff2, Diff2. rewrite take_length.
 rewrite <- count_nbocc.
 now rewrite fs_count_k.
Qed.

(** Equations giving Diff0 and Diff1 after a substitution [ksubst 2].
    Note : this could be stated via a matrix someday.
*)

Lemma Diff0_ksubst2 w : Diff0 (ksubstw 2 w) = τ * Diff2 w.
Proof.
 unfold Diff0, Diff2.
 rewrite len_ksubst, plus_INR.
 destruct (nbocc_ksubst2 w) as (-> & _ & _).
 ring_simplify. unfold Rminus. rewrite Rplus_assoc. f_equal.
 rewrite τ3. lra.
Qed.

Lemma Diff2_ksubst2 w :
  List.Forall (fun a => a <= 2)%nat w ->
  Diff2 (ksubstw 2 w) = - τ^2 * Diff2 w - Diff0 w.
Proof.
 intros H.
 unfold Diff0, Diff2.
 rewrite len_ksubst.
 destruct (nbocc_ksubst2 w) as (_ & _ & ->).
 rewrite !plus_INR.
 replace (nbocc 1 w + nbocc 2 w) with (length w - nbocc 0 w).
 2:{ apply len_nbocc_012 in H. rewrite H. rewrite !plus_INR. lra. }
 ring_simplify.
 replace (τ^4) with (1-τ^2-τ^3) by (generalize τ234; lra).
 lra.
Qed.

(** For [A 2] numbers, diff0 and diff2 have nice expressions via
    powers of the [α] and [αbar] roots (or some real part of
    a power of [α]). Let's first describe the coefficients used
    in these expressions. *)

Definition coefa2 := ((α*(τ^2-1)-τ^3)/(α-αbar))%C.
Definition coefa0 := (αbar * coefa2)%C.

Lemma re_coefa2 : 2*Re coefa2 = τ^2-1.
Proof.
 unfold coefa2.
 change αbar with (Cconj α). rewrite im_alt'.
 change (Im α) with im_α.
 unfold Cdiv.
 replace (/ (2*Ci*im_α))%C with (/Ci * /(2*im_α))%C.
 2:{ field; repeat split; try cconst.
     negapply RtoC_inj; apply im_α_nz. }
 rewrite Ci_inv.
 replace (-Ci * _)%C with (Ci * -(/(2*im_α)))%C by ring.
 rewrite !Cmult_assoc.
 rewrite <- RtoC_mult, <- RtoC_inv, <- RtoC_opp
  by (generalize im_α_nz; lra).
 rewrite re_scal_r, re_mult_Ci.
 simpl. field. apply im_α_nz.
Qed.

Lemma re_coefa0 : 2*Re coefa0 = τ^3.
Proof.
 unfold coefa0, coefa2. unfold Cdiv.
 rewrite Cmult_assoc.
 replace (αbar * _)%C
  with ((α * αbar) * (τ^2-1) - αbar * τ^3)%C by ring.
 rewrite <- Cmod2_conj, αmod2.
 change αbar with (Cconj α) at 2. rewrite im_alt'.
 change (Im α) with im_α.
 replace (/ (2*Ci*im_α))%C with (/Ci * /(2*im_α))%C.
 2:{ field; repeat split; try cconst.
     negapply RtoC_inj; apply im_α_nz. }
 rewrite Ci_inv.
 replace (-Ci * _)%C with (Ci * -(/(2*im_α)))%C by ring.
 rewrite !Cmult_assoc.
 rewrite <- RtoC_mult, <- RtoC_inv, <- RtoC_opp
  by (generalize im_α_nz; lra).
 rewrite re_scal_r, re_mult_Ci.
 simpl. field. apply im_α_nz.
Qed.

Lemma diff_A n :
 diff0 (A 2 n) = 2 * Re(coefa0 * α^n) /\
 diff2 (A 2 n) = 2 * Re(coefa2 * α^n).
Proof.
 induction n as [|n IH].
 - simpl A. simpl Cpow.
   unfold diff0, diff2. simpl take. change (kseq 2 0) with 2%nat.
   unfold Diff0, Diff2. simpl length. simpl nbocc.
   rewrite !Cmult_1_r. rewrite re_coefa0, re_coefa2. simpl; lra.
 - unfold diff0, diff2.
   rewrite kseq_take_A, kword_S.
   rewrite Diff0_ksubst2, Diff2_ksubst2 by (apply kword_letters).
   rewrite <- kseq_take_A. fold (diff0 (A 2 n)) (diff2 (A 2 n)).
   destruct IH as (-> & ->).
   simpl Cpow.
   split.
   + rewrite Cmult_assoc. rewrite (Cmult_comm coefa0). unfold coefa0.
     rewrite Cmult_assoc. change αbar with (Cconj α).
     rewrite <- Cmod2_conj, αmod2.
     rewrite <- Cmult_assoc, re_scal_l. lra.
   + unfold coefa0.
     rewrite (Cmult_assoc coefa2), (Cmult_comm coefa2 α).
     rewrite <- !Cmult_assoc.
     set (c := (coefa2 * α^n)%C).
     replace (-τ^2*(2*Re c)-2*Re (αbar * c)) with
         (2 * ((-τ^2)*Re c + (-1)*(Re (αbar * c)))) by ring.
     f_equal.
     rewrite <-!re_scal_l, <-re_plus.
     f_equal.
     rewrite Cmult_assoc. rewrite <- Cmult_plus_distr_r. f_equal.
     replace (-τ^2) with (2*re_α) by (rewrite re_α_alt; lra).
     rewrite RtoC_mult.
     change re_α with (Re α).
     rewrite re_alt.
     change (Cconj α) with αbar. field.
Qed.

(** Now, any arbitrary number [n] is a sum of [A 2] numbers by Zeckendorf
    theorem (cf. [GenFib.decomp]). So [diff0 n] will be a sum of powers
    of [α]. *)

Lemma Diff0_app u v : Diff0 (u++v) = Diff0 u + Diff0 v.
Proof.
 unfold Diff0.
 rewrite List.app_length, nbocc_app, !plus_INR. lra.
Qed.

Lemma Diff0_concat l : Diff0 (List.concat l) = Rlistsum (List.map Diff0 l).
Proof.
 induction l; simpl; auto.
 - unfold Diff0. simpl. lra.
 - rewrite Diff0_app. lra.
Qed.

Lemma diff0_decomp_eqn n :
  diff0 n = Rlistsum (List.map (fun n => 2*Re(coefa0 * α^n)) (decomp 2 n)).
Proof.
 unfold diff0.
 rewrite decomp_prefix_kseq. unfold kwords. rewrite flat_map_concat_map.
 rewrite Diff0_concat, List.map_map, List.map_rev, Rlistsum_rev.
 f_equal.
 apply List.map_ext; intros.
 rewrite <- kseq_take_A. apply diff_A.
Qed.

Lemma diff0_decomp_eqn' n :
  diff0 n = 2*Re (coefa0 * Cpoly α (decomp 2 n)).
Proof.
 rewrite diff0_decomp_eqn.
 induction decomp; cbn -[Re].
 - rewrite Cmult_0_r. cconst.
 - rewrite Cmult_plus_distr_l, re_plus, Rmult_plus_distr_l.
   f_equal. apply IHl.
Qed.

(** With the previous expression of [diff0 n], we will progressively bound it
    by some constant independent from [n]. *)

Lemma diff0_decomp_le n :
 Rabs (diff0 n) <=
  2 * Cmod coefa0 * Rlistsum (List.map (pow (Cmod α)) (decomp 2 n)).
Proof.
 rewrite diff0_decomp_eqn.
 induction decomp.
 - simpl. rewrite Rabs_R0. lra.
 - cbn -[Re].
   eapply Rle_trans. apply Rabs_triang.
   rewrite Rmult_plus_distr_l.
   apply Rplus_le_compat; [|apply IHl].
   rewrite Rabs_mult. rewrite Rabs_right by lra.
   rewrite Rmult_assoc.
   apply Rmult_le_compat_l; try lra.
   rewrite <- Cmod_pow, <-Cmod_mult.
   apply re_le_Cmod.
Qed.

Lemma diff0_indep_bound n :
  Rabs (diff0 n) <= 2 * Cmod coefa0 / (1 - Cmod α^3).
Proof.
 eapply Rle_trans. apply diff0_decomp_le.
 unfold Rdiv.
 apply Rmult_le_compat_l.
 - generalize (Cmod_ge_0 coefa0). lra.
 - apply sum_pow; try lia; try apply decomp_delta.
   split; try apply Cmod_ge_0.
   apply Rlt_pow2_inv; try lra. rewrite αmod2. approx.
Qed.

(** Experimentally, this first bound is around 1.112.
    Having this finite bound is enough to prove that the frequency
    of letter 0 is [τ^3] and that [h n / n] converges towards τ.
*)

Lemma lim_diff0_div_n : is_lim_seq (fun n => diff0 n / n) 0.
Proof.
 eapply is_lim_seq_bound. apply diff0_indep_bound.
Qed.

Lemma frequency_0 : is_lim_seq (fun n => count (kseq 2) 0 n / n) (τ^3).
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with (u := fun n => τ^3 - diff0 (S n) / S n).
 - intros n.
   unfold diff0, Diff0. rewrite take_length.
   rewrite <- count_nbocc. field. apply RSnz.
 - replace (Rbar.Finite (τ^3)) with (Rbar.Finite (τ^3 + -0))
    by (f_equal; lra).
   eapply is_lim_seq_plus'. apply is_lim_seq_const.
   change (Rbar.Finite (-0)) with (Rbar.Rbar_opp 0).
   apply -> is_lim_seq_opp.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff0 n / n)).
   apply lim_diff0_div_n.
Qed.

Lemma Lim_h_div_n : is_lim_seq (fun n => h n / n) τ.
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with (u := fun n => τ + diff0 (S n) / S n).
 - intros n. rewrite diff0_alt. field. apply RSnz.
 - replace (Rbar.Finite τ) with (Rbar.Finite (τ + 0)) by (f_equal; lra).
   eapply is_lim_seq_plus'. apply is_lim_seq_const.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff0 n / n)).
   apply lim_diff0_div_n.
Qed.

(** NB : Classical reals are now Dedekind cuts,
    just 4 logical axioms remaining :)
*)

(* Print Assumptions Lim_H_div_n. *)


(** With some more sweat, we prove now a better bound, strictly
    below 1, with nice consequences :

     - [h n = nat_part (τ*n)+{0,1}]
     - [h] is quasi-additive [forall n p, -2 <= h(n+p) - h(n) - h(p) <= 2]
*)

Lemma αmod_lt : 0 < Cmod α < 1.
Proof.
 split.
 - apply Cmod_gt_0. unfold α. injection 1 as H H'. now apply re_α_nz.
 - apply Rlt_pow2_inv; try lra. rewrite αmod2. approx.
Qed.

Lemma αmod9_lt : 0 < Cmod α^9 < 1.
Proof.
 assert (H := αmod_lt).
 split.
 - apply pow_lt; lra.
 - change ((Cmod α)^9) with ((Cmod α)*(Cmod α)^8).
   apply Rle_lt_trans with (Cmod α * 1); try lra.
   apply Rmult_le_compat_l; try lra.
   rewrite <- (pow1 8). apply pow_incr. lra.
Qed.

Lemma re_α2 : Re (α^2) = re_α^2 - im_α^2.
Proof.
 simpl. ring.
Qed.

Lemma re_α2_τ : Re (α^2) = -τ*(1+τ)/2.
Proof.
 rewrite re_α2. rewrite re_α_alt, im_α_2.
 field_simplify.
 rewrite τ4. field.
Qed.

Lemma im_α2 : Im (α^2) = 2*re_α*im_α.
Proof.
 simpl. ring.
Qed.

Module Coefs.
(** Triplets (a,b,c) for "reduced" polynomials a+bα+cα^2 *)
Local Open Scope nat.

Inductive coefs := Coefs (a b c : nat).

Definition zero : coefs := Coefs 0 0 0.

Definition add '(Coefs a b c) '(Coefs a' b' c') :=
 Coefs (a+a') (b+b') (c+c').

Fixpoint of_exp n :=
 match n with
 | 0 => Coefs 1 0 0
 | 1 => Coefs 0 1 0
 | 2 => Coefs 0 0 1
 | S n => add (of_exp n) (of_exp (n-2))
 end.

Definition of_poly l := List.fold_right add zero (map of_exp l).

Definition Ceval x '(Coefs a b c) := (a + b * x + c * x^2)%C.

Lemma of_exp_S n : 2 <= n ->
  of_exp (S n) = add (of_exp n) (of_exp (n-2)).
Proof.
 destruct n as [|[|n ] ]; lia || easy.
Qed.

Lemma Ceval_add x c c' :
  (Ceval x (add c c') = Ceval x c + Ceval x c')%C.
Proof.
 destruct c as [a b c], c' as [a' b' c']. simpl.
 rewrite !plus_INR. lca.
Qed.

Lemma Cpow_α_reduce n : (α^n = Ceval α (of_exp n))%C.
Proof.
 induction n as [n IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases n 2).
 - destruct n as [|[|[|n ] ] ]; lca || lia.
 - destruct n; try lia. rewrite of_exp_S by lia.
   rewrite Ceval_add, <- !IH by lia. clear IH.
   replace (S n) with (3 + (n-2)) by lia.
   rewrite Cpow_add_r, α_is_root.
   replace n with (2 + (n-2)) at 2 by lia.
   rewrite Cpow_add_r. ring.
Qed.

Lemma Cpoly_α_reduce l : (Cpoly α l = Ceval α (of_poly l))%C.
Proof.
 induction l.
 - unfold Cpoly. simpl. lca.
 - cbn. rewrite Ceval_add, Cpow_α_reduce. f_equal. apply IHl.
Qed.

End Coefs.

Lemma cmod2_trinom_α (a b c : R) :
 (Cmod (a + b*α + c*α^2))^2 =
 (1/4)*((2*a - b*τ^2 - c*τ*(1+τ))^2 + τ*(3+τ)*(b-c*τ^2)^2).
Proof.
 rewrite Cmod2_alt.
 rewrite !re_plus, !im_plus, re_RtoC, im_RtoC.
 rewrite !re_scal_l, !im_scal_l, re_α2_τ, im_α2.
 simpl Im. simpl Re.
 replace (0 + _ + _) with (im_α * (b + c * (2*re_α))) by ring.
 rewrite Rpow_mult_distr, im_α_2, re_α_alt. field.
Qed.

Ltac calc_α_poly :=
 rewrite Coefs.Cpoly_α_reduce; cbn -[pow INR]; rewrite cmod2_trinom_α.

Definition max3list := [0;3;7]%nat.
Definition max3pack := Cmod (Cpoly α max3list).

Lemma max3pack_eqn : max3pack^2 = 15 - 11*τ - 10*τ^2.
Proof.
 unfold max3pack, max3list. calc_α_poly.
 rewrite !INR_IZR_INZ. simpl Z.of_nat.
 field_simplify. rewrite ?τ6, ?τ5, ?τ4, ?τ3. field.
Qed.

(* Curious note : all the trinoms we consider lead to N - M*τ - K*τ^2
   except (Cmod (1+α^4+α^8))^2 = 8 + 2*τ - 17*τ^2. *)

Lemma best_3pack_enum l :
  In l (enum_sparse_subsets0 2 9) -> Cmod (Cpoly α l) <= max3pack.
Proof.
 intro H. apply Rle_pow2_inv; [apply Cmod_ge_0|]. rewrite max3pack_eqn.
 revert l H. apply Forall_forall. vm_compute enum_sparse_subsets0.
 repeat (constructor; [ try (calc_α_poly; approx) | ]); [|constructor].
 rewrite <- max3pack_eqn. apply Rle_refl.
Qed.

Lemma best_3pack_below l :
  Delta 3 l -> Below l 9 -> Cmod (Cpoly α l) <= max3pack.
Proof.
 intros D B.
 destruct l as [|a l].
 - cbn -[Cpow]. rewrite Cmod_0. apply Cmod_ge_0.
 - revert l D B. induction a as [|a IH]; intros l D B.
   + apply best_3pack_enum.
     now rewrite enum_sparse_subsets0_ok, enum_sparse_subsets_ok.
   + replace (S a::l)%list with (List.map S (a :: List.map pred l))%list.
     2:{ simpl. f_equal. rewrite List.map_map.
         rewrite <- (List.map_id l) at 2. apply List.map_ext_in.
         intros b Hb.
         assert (b<>O); try lia.
         { intros ->. apply (@Delta_nz' 3 (S a) l); auto; lia. }}
     unfold Cpoly.
     rewrite List.map_map, (Clistsum_pow_factor α 1), Cmod_mult, Cpow_1_r.
     set (l' := List.map pred l).
     eapply Rle_trans. 2:apply (IH l').
     * rewrite <- (Rmult_1_l (Cmod (Cpoly _ _))) at 2.
       apply Rmult_le_compat_r; try apply Cmod_ge_0.
       apply Rle_pow2_inv; try lra. rewrite αmod2. approx.
     * change (Delta 3 (map pred (S a :: l))). clear l'.
       apply Delta_pred; trivial. eapply Delta_nz; eauto; lia.
     * change (Below (map pred (S a :: l)) 9). clear l'.
       unfold Below in *. intros x. rewrite in_map_iff.
       intros (y & <- & Hy). specialize (B y Hy). lia.
Qed.

Lemma best_3pack l :
  Delta 3 l -> Cmod (Cpoly α l) <= max3pack / (1 - Cmod α ^9).
Proof.
 intros D.
 assert (B := maxlist0_above l).
 setoid_rewrite <- Nat.lt_succ_r in B.
 set (N := S (maxlist 0 l)). change (Below l N) in B. clearbody N.
 revert l D B.
 induction N as [N IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases N 9).
 - clear IH. intros l D B.
   eapply Rle_trans. apply best_3pack_below; auto.
   unfold Below in *. intros y Hy. specialize (B y Hy). lia.
   rewrite <- (Rmult_1_r max3pack) at 1. unfold Rdiv.
   apply Rmult_le_compat_l; try apply Cmod_ge_0.
   rewrite <- (Rmult_1_l (/ _)).
   assert (P := Cmod_ge_0 α).
   apply Rcomplements.Rle_div_r; generalize αmod9_lt; lra.
 - intros l D B. destruct (cut_lt_ge 9 l) as (l1,l2) eqn:E.
   assert (D' := D).
   assert (E' := cut_app 9 l). rewrite E in E'. rewrite <- E' in D',B |- *.
   rewrite Delta_app_iff in D'. destruct D' as (D1 & D2 & D3).
   rewrite Cpoly_app.
   eapply Rle_trans. apply Cmod_triangle.
   eapply Rle_trans; [eapply Rplus_le_compat_r|].
   + apply best_3pack_below; auto.
     generalize (cut_fst 9 l). now rewrite E.
   + assert (A : forall n, List.In n l2 -> (9 <= n)%nat).
     { intros n Hn. apply (@cut_snd' 3 9 l); auto. now rewrite E. }
     rewrite (Cpoly_factor_above α 9 l2) by trivial.
     set (l2' := List.map (decr 9) l2).
     rewrite Cmod_mult.
     replace (max3pack / _)
       with (max3pack + Cmod (α^9) * (max3pack / (1 - Cmod α ^9))).
     * apply Rplus_le_compat_l.
       apply Rmult_le_compat_l; try apply Cmod_ge_0.
       apply (IH (N-9)%nat); try lia.
       { apply Delta_map_decr; auto. }
       { unfold l2'. intros x Hx. rewrite List.in_map_iff in Hx.
         destruct Hx as (y & <- & Hy).
         specialize (A y Hy).
         assert (y < N)%nat by (apply B; rewrite List.in_app_iff; now right).
         unfold decr. lia. }
     * rewrite Cmod_pow. field. generalize αmod9_lt; lra.
Qed.

Lemma diff0_better_bound n :
  Rabs (diff0 n) <= 2 * Cmod coefa0 * max3pack / (1 - Cmod α ^9).
Proof.
 rewrite diff0_decomp_eqn'.
 rewrite Rabs_mult. rewrite Rabs_right by lra.
 unfold Rdiv. rewrite !Rmult_assoc. apply Rmult_le_compat_l; try lra.
 eapply Rle_trans; [apply re_le_Cmod|].
 rewrite Cmod_mult. apply Rmult_le_compat_l; try apply Cmod_ge_0.
 apply best_3pack, decomp_delta.
Qed.

Lemma coefa2_inner_mod :
  Cmod (α * (τ ^ 2 - 1) - τ ^ 3) ^ 2 = τ*(1-τ).
Proof.
 rewrite !RtoC_pow, <- RtoC_minus.
 rewrite Cmod2_alt. unfold Cminus.
 rewrite re_plus, im_plus, re_scal_r, im_scal_r.
 rewrite <- !RtoC_opp, re_RtoC, im_RtoC, Rplus_0_r. simpl Re; simpl Im.
 rewrite re_α_alt.
 rewrite Rpow_mult_distr. rewrite im_α_2.
 rewrite τ3. field_simplify.
 replace (τ^8) with ((τ^4)^2) by ring.
 rewrite τ6, τ5, τ4, τ3. field_simplify.
 rewrite τ4, τ3. field.
Qed.

Lemma Cmod2_coefa2 :
  Cmod coefa2 ^2 = (1-τ)/(3+τ).
Proof.
 unfold coefa2, Cdiv.
 rewrite !Cmod_mult, !Rpow_mult_distr, Cmod_inv.
 2:{ apply Cminus_eq_contra. apply distinct_roots. }
 rewrite coefa2_inner_mod.
 rewrite im_alt', !Cmod_mult.
 rewrite !Cmod_R, Rabs_right by lra.
 rewrite Cmod_Ci, Rmult_1_r.
 simpl Im.
 rewrite pow_inv, Rpow_mult_distr.
 rewrite pow2_abs. rewrite im_α_2. field. approx.
Qed.

(** And finally, we obtain that diff0 is always strictly less than 1.
    (experimentally the new bound is around 0.996) *)

Lemma diff0_lt_1 n : Rabs (diff0 n) < 1.
Proof.
 eapply Rle_lt_trans. apply diff0_better_bound.
 assert (A9 := αmod9_lt).
 apply -> Rcomplements.Rdiv_lt_1; try lra.
 apply Rlt_pow2_inv; try lra.
 clear A9.
 rewrite !Rpow_mult_distr.
 rewrite max3pack_eqn.
 replace (Cmod α^9) with (((Cmod α)^2)^4*Cmod α) by ring.
 rewrite αmod2, τ4.
 unfold coefa0. rewrite Cmod_mult, Rpow_mult_distr, Cmod2_coefa2.
 change αbar with (Cconj α). rewrite Cmod_Cconj, αmod2.
 approx.
Qed.

(* Print Assumptions diff0_lt_1. *)

(* Consequences for h : *)

Lemma h_alt n : INR (h n) = τ*n + diff0 n.
Proof.
 rewrite diff0_alt; lra.
Qed.

Lemma h_natpart_or n : h n = nat_part (τ*n) \/ h n = S (nat_part (τ*n)).
Proof.
assert (-1 < τ*n - h n < 1).
{ rewrite h_alt.
  assert (H := diff0_lt_1 n).
  rewrite Rcomplements.Rabs_lt_between in H. lra. }
destruct (Rle_or_lt 0 (τ*n-h n)).
- left. symmetry. apply nat_part_carac; lra.
- right.
  case (Nat.eq_dec n 0); intros Hn.
  + subst n. change (h 0) with O in *. simpl in *. lra.
  + assert (h n <> O). { contradict Hn. eapply f_0_inv; eauto. }
    assert (nat_part (τ*n) = h n -1)%nat; try lia.
    apply nat_part_carac. rewrite minus_INR by lia. simpl. lra.
Qed.

(* NB: both sides are reached, e.g. left for n=0 and right for n=1.
   I've found no easy way to predict on which side will be some (h n). *)

Lemma h_natpart_bound (n:nat) :
 (nat_part (τ*n) <= h n <= 1 + nat_part (τ*n))%nat.
Proof.
 destruct (h_natpart_or n) as [-> | ->]; lia.
Qed.

(* A quasi-additivity result for h = f 2 that I was unable to obtain
   directly on h. *)

Lemma h_quasiadd p n : (h p + h n -2 <= h (p+n) <= h p + h n + 2)%nat.
Proof.
  case (Nat.eq_dec p 0); intros Hp.
  - subst p. simpl. lia.
  - case (Nat.eq_dec n 0); intros Hn.
    + subst n. change (h 0) with 0%nat. rewrite !Nat.add_0_r. lia.
    + split; apply Nat.lt_succ_r; apply INR_lt.
      * rewrite minus_INR, plus_INR. rewrite !S_INR, !h_alt.
        2:{ generalize (@f_nonzero 2 p) (@f_nonzero 2 n). fold h. lia. }
        rewrite plus_INR.
        assert (Dp := diff0_lt_1 p).
        assert (Dn := diff0_lt_1 n).
        assert (Dpn := diff0_lt_1 (p+n)).
        rewrite Rcomplements.Rabs_lt_between in *.
        simpl. lra.
      * rewrite !S_INR, !plus_INR. rewrite !h_alt, plus_INR.
        assert (Dp := diff0_lt_1 p).
        assert (Dn := diff0_lt_1 n).
        assert (Dpn := diff0_lt_1 (p+n)).
        rewrite Rcomplements.Rabs_lt_between in *.
        simpl. lra.
Qed.

(* Print Assumptions h_quasiadd. *)

(** Now, same study for [diff2 n], giving the frequency of letter 2,
    and the limit of [h^^2]. Less interesting, the bound is in [1..2]. *)

Lemma Diff2_app u v : Diff2 (u++v) = Diff2 u + Diff2 v.
Proof.
 unfold Diff2.
 rewrite List.app_length, nbocc_app, !plus_INR. lra.
Qed.

Lemma Diff2_concat l : Diff2 (List.concat l) = Rlistsum (List.map Diff2 l).
Proof.
 induction l; simpl; auto.
 - unfold Diff2. simpl. lra.
 - rewrite Diff2_app. lra.
Qed.

Lemma diff2_decomp_eqn n :
  diff2 n = Rlistsum (List.map (fun n => 2*Re(coefa2 * α^n)) (decomp 2 n)).
Proof.
 unfold diff2.
 rewrite decomp_prefix_kseq. unfold kwords. rewrite flat_map_concat_map.
 rewrite Diff2_concat, List.map_map, List.map_rev, Rlistsum_rev.
 f_equal.
 apply List.map_ext; intros.
 rewrite <- kseq_take_A. apply diff_A.
Qed.

Lemma diff2_decomp_eqn' n :
  diff2 n = 2*Re (coefa2 * Cpoly α (decomp 2 n)).
Proof.
 rewrite diff2_decomp_eqn.
 induction decomp; cbn -[Re].
 - rewrite Cmult_0_r. cconst.
 - rewrite Cmult_plus_distr_l, re_plus, Rmult_plus_distr_l.
   f_equal. apply IHl.
Qed.

(** With the previous expression of [diff2 n], we will progressively bound it
    by some constant independent from [n]. *)

Lemma diff2_decomp_le n :
 Rabs (diff2 n) <=
  2 * Cmod coefa2 * Rlistsum (List.map (pow (Cmod α)) (decomp 2 n)).
Proof.
 rewrite diff2_decomp_eqn.
 induction decomp.
 - simpl. rewrite Rabs_R0. lra.
 - cbn -[Re].
   eapply Rle_trans. apply Rabs_triang.
   rewrite Rmult_plus_distr_l.
   apply Rplus_le_compat; [|apply IHl].
   rewrite Rabs_mult. rewrite Rabs_right by lra.
   rewrite Rmult_assoc.
   apply Rmult_le_compat_l; try lra.
   rewrite <- Cmod_pow, <-Cmod_mult.
   apply re_le_Cmod.
Qed.

Lemma diff2_indep_bound n :
 Rabs (diff2 n) <= 2 * Cmod coefa2 / (1 - Cmod α^3).
Proof.
 eapply Rle_trans. apply diff2_decomp_le.
 unfold Rdiv.
 apply Rmult_le_compat_l.
 - generalize (Cmod_ge_0 coefa2). lra.
 - apply sum_pow; try lia; try apply decomp_delta. approx.
Qed.

Lemma diff2_lt_2 n : Rabs (diff2 n) < 2.
Proof.
 eapply Rle_lt_trans. apply diff2_indep_bound.
 replace 2 with (2*1) at 2 by lra.
 unfold Rdiv. rewrite Rmult_assoc. apply Rmult_lt_compat_l; try lra.
 assert (Cmod α^3 < 1) by approx.
 apply Rcomplements.Rlt_div_l; try lra.
 rewrite Rmult_1_l.
 apply Rlt_pow2_inv; try lra. rewrite Cmod2_coefa2. approx.
Qed.


(** Experimentally, this bound for diff2 is around 1.3462 and cannot be
    improved significantly (unlike the first bound 1.112 for diff0 improved
    to 0.996 later).
    Anyway, having this finite bound is enough to prove that the frequency
    of letter 2 is [τ^2] and that [(h^^2)(n) / n] converges towards [τ^2].
*)

Lemma lim_diff2_div_n : is_lim_seq (fun n => diff2 n / n) 0.
Proof.
 eapply is_lim_seq_bound. apply diff2_indep_bound.
Qed.

Lemma frequency_2 : is_lim_seq (fun n => count (kseq 2) 2 n / n) (τ^2).
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with
  (u := fun n => τ^2 - diff2 (S n) / INR (S n)).
 - intros n.
   unfold diff2, Diff2. rewrite take_length.
   rewrite <- count_nbocc. field. apply RSnz.
 - replace (Rbar.Finite (τ^2)) with (Rbar.Finite (τ^2 + -0))
    by (f_equal; lra).
   eapply is_lim_seq_plus'. apply is_lim_seq_const.
   change (Rbar.Finite (-0)) with (Rbar.Rbar_opp 0).
   apply -> is_lim_seq_opp.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff2 n / n)).
   apply lim_diff2_div_n.
Qed.

Lemma frequency_1 : is_lim_seq (fun n => count (kseq 2) 1 n / n) (τ^4).
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with
  (u := fun n => τ^4 + diff0 (S n) / INR (S n) + diff2 (S n) / INR (S n)).
 - intros n.
   field_simplify; try apply RSnz. f_equal.
   rewrite Rplus_assoc.
   replace (diff0 (S n) + diff2 (S n)) with (-diff1 (S n))
     by (generalize (diff012 (S n)); lra).
   unfold diff1, Diff1. rewrite take_length.
   rewrite <- count_nbocc. field.
 - replace (Rbar.Finite (τ^4)) with (Rbar.Finite (τ^4 + 0 + 0))
    by (f_equal; lra).
   apply is_lim_seq_plus'. apply is_lim_seq_plus'. apply is_lim_seq_const.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff0 n / n)).
   apply lim_diff0_div_n.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff2 n / n)).
   apply lim_diff2_div_n.
Qed.

Lemma Lim_h2_div_n : is_lim_seq (fun n => (h^^2) n / n) (τ^2).
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with
  (u := fun n => τ^2 - diff2 (S n) / INR (S n)).
 - intros n. rewrite diff2_alt. field. rewrite S_INR.
   generalize (pos_INR n). lra.
 - replace (Rbar.Finite (τ^2)) with (Rbar.Finite (τ^2 - 0))
    by (f_equal; lra).
   eapply is_lim_seq_plus'. apply is_lim_seq_const.
   change (Rbar.Finite (-0)) with (Rbar.Rbar_opp 0).
   apply -> is_lim_seq_opp.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff2 n / n)).
   apply lim_diff2_div_n.
Qed.

Lemma h2_alt n : INR ((h^^2) n) = τ^2 * n - diff2 n.
Proof.
 rewrite diff2_alt; lra.
Qed.

(** Alternative bound of diff2 via diff0 : [1+τ] is less precise than
    the previous bound, but easier to obtain and still below 2. *)

Lemma diff2_via_diff0 n : diff2 n = - diff0 (h n) - τ * diff0 n.
Proof.
 rewrite diff2_alt, !diff0_alt. simpl. ring.
Qed.

Lemma diff2_lt_indirect n : Rabs (diff2 n) < 1+τ.
Proof.
 rewrite diff2_via_diff0. unfold Rminus.
 eapply Rle_lt_trans; try apply Rabs_triang; rewrite !Rabs_Ropp, Rabs_mult.
 rewrite (Rabs_pos_eq τ) by approx.
 replace τ with (τ*1) at 2 by lra.
 apply Rplus_lt_compat; try apply Rmult_lt_compat_l; try apply diff0_lt_1.
 approx.
Qed.

(** Distance between [h^^2] and [nat_part (τ^2 * n)].
    This distance may be "+2", for instance for n=1235.
    But the theoretical "-1" does not seem to happen
    (TODO: how to prove it ?) *)

Lemma h2_natpart_bound (n:nat) :
 (nat_part (τ^2 * n) -1 <= (h^^2) n <= 2 + nat_part (τ^2 * n))%nat.
Proof.
 split.
 - assert (nat_part (τ^2 * n) < 2 + (h^^2) n)%nat; try lia.
   { apply nat_part_lt. split.
     - apply Rmult_le_pos. approx. apply pos_INR.
     - rewrite plus_INR. replace (INR 2) with 2 by auto.
       assert (LT := diff2_lt_2 n). apply Rcomplements.Rabs_lt_between in LT.
       generalize (diff2_alt n). lra. }
 - assert ((h^^2) n - 2 <= nat_part (τ^2 * n))%nat; try lia.
   { apply nat_part_le.
     - apply Rmult_le_pos. approx. apply pos_INR.
     - destruct (Nat.le_gt_cases 4 n) as [LE|LT].
       + assert (LE' := fs_mono 2 2 LE).
         rewrite minus_INR by trivial.
         replace (INR 2) with 2 by auto.
         assert (LT := diff2_lt_2 n). apply Rcomplements.Rabs_lt_between in LT.
         generalize (diff2_alt n). lra.
       + destruct n. simpl; lra.
         destruct n. simpl. approx.
         destruct n. simpl. approx.
         destruct n. simpl. approx.
         lia. }
Qed.

(* Next cases:

For k=3, see LimCase3.v
 an extra negative real root. The complex roots can be expressed
 in function of the real roots. Similar convergence and results than for k=2,
 except that (f 3 n) could be further apart from (nat_part (tau 3 * n)).

For k=4, no Coq proofs yet.
 four complex roots : j and (Cconj j) of modulus 1, and
  some α and (Cconj α) of modulus < 1. Note that α can be
  expressed in function of (tau 4). Apparently, no more finite bound to
  (f 4 n - tau 4 * n).

Afterwards, always some complex root of modulus > 1 (but < mu k).
And (f k n - tau k * n) seems to diverge.
*)
