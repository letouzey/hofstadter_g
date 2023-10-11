From Coq Require Import Arith Lia Reals Lra.
From QuantumLib Require Import Complex.
Require Import MoreReals MoreLim MoreComplex.
Require Import DeltaList FunG GenFib GenG GenAdd Words Mu.
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

Definition mu := mu 2.
Definition tau := tau 2.

Definition re_alpha := (1 - mu)/2.
Definition im_alpha := sqrt (tau * (3+tau))/2.

Definition alpha : C := (re_alpha, im_alpha).
Definition alphabar : C := (re_alpha, - im_alpha).

Lemma tau3 : tau^3 = 1 - tau.
Proof.
 generalize (tau_carac 2). fold tau. lra.
Qed.

Lemma tau4 : tau^4 = tau - tau^2.
Proof.
 change (tau^4) with (tau*tau^3). rewrite tau3. ring.
Qed.

Lemma tau234 : tau^2 + tau^3 + tau^4 = 1.
Proof.
 rewrite tau3, tau4; ring.
Qed.

Lemma tau5 : tau^5 = tau + tau^2 - 1.
Proof.
 change (tau^5) with (tau*tau^4). rewrite tau4. ring_simplify.
 rewrite tau3. ring.
Qed.

Lemma tau6 : tau^6 = (1-tau)^2.
Proof.
 rewrite <- tau3. ring.
Qed.

Lemma tau_approx : 0.682327 < tau < 0.682328.
Proof.
 exact tau_2.
Qed.

Lemma tau2_approx : 0.465570 < tau^2 < 0.465572.
Proof.
 destruct tau_approx as (H1,H2).
 simpl. rewrite Rmult_1_r. split.
 - eapply Rlt_trans; [ | eapply Rmult_le_0_lt_compat; eauto]; lra.
 - eapply Rlt_trans; [ eapply Rmult_le_0_lt_compat; eauto | ]; lra.
Qed.

Lemma re_alpha_alt : re_alpha = - tau ^ 2 / 2.
Proof.
 unfold re_alpha. f_equal.
 unfold mu. rewrite tau_inv. fold tau.
 assert (tau <> 0) by (generalize tau_approx; lra).
 apply Rmult_eq_reg_l with tau; trivial.
 field_simplify; trivial. rewrite tau3. lra.
Qed.

Lemma im_alpha_2 : im_alpha ^ 2 = tau * (3+tau) / 4.
Proof.
 unfold im_alpha.
 unfold Rdiv.
 rewrite Rpow_mult_distr, pow2_sqrt; try lra.
 apply Rmult_le_pos; generalize tau_approx; lra.
Qed.

Lemma alphamod2 : (Cmod alpha)^2 = tau.
Proof.
 unfold Cmod.
 rewrite pow2_sqrt.
 2: generalize (pow2_ge_0 (fst alpha)) (pow2_ge_0 (snd alpha)); lra.
 unfold alpha; simpl. ring_simplify.
 rewrite im_alpha_2. rewrite re_alpha_alt.
 field_simplify. rewrite tau4. field.
Qed.

Lemma mu_is_Croot : (mu ^3 = mu ^2 + 1)%C.
Proof.
 rewrite !RtoC_pow, <- RtoC_plus. unfold mu. now rewrite (mu_carac 2).
Qed.

Lemma alpha_is_root : (alpha^3 = alpha^2 + 1)%C.
Proof.
 simpl. rewrite !Cmult_1_r. unfold alpha. unfold Cmult; simpl.
 unfold Cplus; simpl. f_equal; ring_simplify.
 - rewrite im_alpha_2, re_alpha_alt.
   field_simplify. rewrite tau6, tau4, tau3. field.
 - change (im_alpha ^ 3) with (im_alpha * im_alpha^2).
   rewrite im_alpha_2, re_alpha_alt.
   field_simplify. rewrite tau4. field.
Qed.

Lemma alphabar_is_root : (alphabar^3 = alphabar^2 + 1)%C.
Proof.
 change alphabar with (Cconj alpha).
 rewrite <- !Cpow_conj. rewrite alpha_is_root.
 rewrite Cconj_plus_distr. f_equal. compute; f_equal; lra.
Qed.

Lemma re_alpha_nz : re_alpha <> 0.
Proof.
 unfold re_alpha, mu. generalize mu_2. lra.
Qed.

Lemma im_alpha_nz : im_alpha <> 0.
Proof.
 assert (LE : 0 <= im_alpha).
 { unfold im_alpha. apply Rle_mult_inv_pos; try lra. apply sqrt_pos. }
 assert (LT : 0 < im_alpha ^2).
 { rewrite im_alpha_2. unfold Rdiv.
   repeat apply Rmult_lt_0_compat; generalize tau_approx; lra. }
 destruct (Rle_lt_or_eq_dec _ _ LE) as [?|EQ]; try rewrite <- EQ in *; lra.
Qed.

Lemma distinct_roots :
  alpha <> mu /\ alphabar <> mu /\ alpha <> alphabar.
Proof.
 unfold alpha, alphabar, RtoC; repeat split.
 - intros [= A B]. now destruct im_alpha_nz.
 - intros [= A B]. generalize im_alpha_nz. lra.
 - intros [= B]. generalize im_alpha_nz. lra.
Qed.

(** Explicit decomposition of [A 2 n] into a linear combination
    of root powers.
    This is less useful now that we have general results for any k,
    see ThePoly.coefs_LinCombA and Freq.A_ratio for instance.
    But these general results do not provide expressions for the
    coefficients, unlike [coef_alpha] and [coef_mu] below.
*)

Definition coef_alpha : C :=
 ((3-mu^2+(alphabar+mu)*(mu-2))/(alpha-mu)/(alpha-alphabar))%C.

Definition coef_mu : R := 1 - 2 * Re coef_alpha.

Local Hint Rewrite
 Ropp_0 Rplus_0_r Rplus_0_l Rminus_0_r
 Rmult_0_l Rmult_0_r Rmult_1_l Rmult_1_r : rbasic.

Lemma misc_eqn : (re_alpha - mu)^2 + im_alpha^2 = 2*tau + mu^2.
Proof.
 rewrite <- !Rsqr_pow2, Rsqr_minus, !Rsqr_pow2.
 replace (2*tau) with (tau+tau) by lra.
 rewrite <- alphamod2 at 1. rewrite Cmod2_alt. simpl Re. simpl Im.
 rewrite re_alpha_alt at 2.
 simpl (tau^2). change tau with (/ mu) at 1. field.
 unfold mu. generalize mu_2. lra.
Qed.

Lemma re_coef_alpha_alt : Re coef_alpha =
  (-3 + mu^2 + tau^2 * (mu - 2)) / (2*(2*tau+mu^2)).
Proof.
 unfold coef_alpha.
 set (u := Cplus _ _).
 set (v := (u / (alpha-mu))%C).
 change alphabar with (Cconj alpha); rewrite im_alt'.
 simpl Im.
 replace (v / _)%C
   with ((v / Ci)%C * (/ (2*im_alpha))%R)%C.
 2:{ rewrite RtoC_inv, RtoC_mult. 2:generalize im_alpha_nz; lra.
     field; repeat split; try cconst. negapply RtoC_inj; apply im_alpha_nz. }
 rewrite re_scal_r.
 unfold Cdiv. rewrite Ci_inv.
 replace (v * -Ci)%C with (-v * Ci)%C by ring.
 rewrite re_mult_Ci.
 rewrite im_opp, Ropp_involutive.
 unfold v, u; clear u v. cbn -[pow].
 autorewrite with rbasic. fold (mu-2). fold (re_alpha-mu).
 rewrite <- misc_eqn.
 set (mo := (re_alpha-mu)^2+im_alpha^2).
 rewrite re_alpha_alt. field; split; try apply im_alpha_nz.
 unfold mo; clear mo. rewrite <-!Rsqr_pow2, Rplus_comm.
 negapply Rplus_sqr_eq_0_l. apply im_alpha_nz.
Qed.

Lemma re_coef_alpha_bound : -0.16 < Re coef_alpha < -0.15.
Proof.
 generalize tau_approx tau2_approx mu_2. fold mu. intros H H' H''.
 assert (1.465^2 < mu^2 < 1.466^2).
 { split; rewrite <-!Rsqr_pow2; apply Rsqr_incrst_1; lra. }
 rewrite re_coef_alpha_alt.
 rewrite Rcomplements.Rlt_div_l by lra.
 rewrite <- Rcomplements.Rlt_div_r by lra.
 assert (E : tau ^ 2 * mu  = tau).
 { unfold mu, tau, Mu.tau. field. fold mu. lra. }
 split; apply Rminus_gt_0_lt; ring_simplify; lra.
Qed.

Lemma coef_mu_bound : 1.30 < coef_mu < 1.32.
Proof.
 unfold coef_mu. generalize re_coef_alpha_bound. lra.
Qed.

(** These coefficients coef_alpha and coef_mu were found by manually
    inverting the Vandermonde(mu,alpha,alphabar) matrix.
    Let's first verify the corresponding equations: *)

Lemma coefs_eqn1 : coef_mu + 2 * Re coef_alpha = 1.
Proof.
 unfold coef_mu. lra.
Qed.

Lemma coefs_eqn2 : coef_mu * mu + 2 * Re (coef_alpha * alpha) = 2.
Proof.
 unfold coef_mu. unfold Rminus.
 rewrite Rmult_plus_distr_r, Rmult_1_l.
 rewrite <- Ropp_mult_distr_l, Rmult_assoc.
 rewrite !Ropp_mult_distr_r. rewrite <- re_scal_r.
 rewrite Rplus_assoc, <- Rmult_plus_distr_l, <- re_plus.
 rewrite <- Cmult_plus_distr_l.
 rewrite Cplus_comm, RtoC_opp. fold (Cminus alpha mu).
 unfold coef_alpha.
 change alphabar with (Cconj alpha); rewrite im_alt'.
 remember (Cplus _ _) as z eqn:EQ. simpl Im.
 replace (Cmult _ _) with (z/(2*im_alpha)/Ci)%C.
 2:{ field; repeat split; try cconst.
     - destruct distinct_roots as (H & _ & _). now apply Cminus_eq_contra.
     - negapply RtoC_inj. apply im_alpha_nz. }
 unfold Cdiv at 1. rewrite Ci_inv.
 replace (Cmult _ _) with ((-z/(2*im_alpha))*Ci)%C.
 2: { field; repeat split; try cconst.
      negapply RtoC_inj. apply im_alpha_nz. }
 rewrite re_mult_Ci.
 unfold Cdiv. rewrite <- RtoC_mult, <- RtoC_inv.
 2: { generalize im_alpha_nz. lra. }
 rewrite im_scal_r, im_opp.
 rewrite EQ; clear EQ z.
 rewrite im_plus.
 rewrite RtoC_pow, <- RtoC_minus, im_RtoC.
 rewrite <- RtoC_minus, im_scal_r, im_plus, im_RtoC.
 rewrite im_conj. simpl Im.
 field. apply im_alpha_nz.
Qed.

(* TODO : bizarreries avec les scopes et les operateurs infixes. *)

Lemma coefs_eqn3 : coef_mu * mu ^2 + 2 * Re (coef_alpha * alpha^2)%C = 3.
Proof.
 unfold coef_mu. unfold Rminus.
 rewrite Rmult_plus_distr_r, Rmult_1_l.
 rewrite <- Ropp_mult_distr_l, Rmult_assoc.
 rewrite !Ropp_mult_distr_r. rewrite <- re_scal_r.
 rewrite Rplus_assoc, <- Rmult_plus_distr_l, <- re_plus.
 rewrite <- Cmult_plus_distr_l.
 rewrite Cplus_comm, RtoC_opp, <- RtoC_pow. fold (Cminus (alpha^2) (mu^2))%C.
 unfold coef_alpha.
 change alphabar with (Cconj alpha); rewrite im_alt'.
 remember (Cplus _ _) as z eqn:EQ. simpl Im.
 replace (Cmult _ _) with ((z*(alpha+mu))/(2*im_alpha)/Ci)%C.
 2:{ simpl Cpow. field; repeat split; try cconst.
     - destruct distinct_roots as (H & _ & _). now apply Cminus_eq_contra.
     - negapply RtoC_inj. apply im_alpha_nz. }
 unfold Cdiv at 1. rewrite Ci_inv.
 replace (Cmult _ _) with (((-z*(alpha+mu))/(2*im_alpha))*Ci)%C.
 2: { field; repeat split; try cconst.
      negapply RtoC_inj. apply im_alpha_nz. }
 rewrite re_mult_Ci.
 unfold Cdiv. rewrite <- RtoC_mult, <- RtoC_inv.
 2: { generalize im_alpha_nz. lra. }
 rewrite im_scal_r.
 rewrite EQ; clear EQ z.
 rewrite im_mult.
 rewrite !im_plus, !re_plus, !re_RtoC, !im_RtoC. simpl (Im alpha).
 simpl (Re alpha).
 replace (im_alpha + 0) with im_alpha by ring.
 rewrite re_opp, im_opp, re_plus, im_plus.
 rewrite !RtoC_pow, <- !RtoC_minus, re_RtoC, im_RtoC.
 rewrite re_scal_r, im_scal_r, re_plus, im_plus, re_RtoC, im_RtoC.
 rewrite re_conj, im_conj. simpl Re. simpl Im.
 field. apply im_alpha_nz.
Qed.

Lemma A2_eqn n :
 INR (A 2 n) = coef_mu * mu ^n + 2 * Re (coef_alpha * alpha^n)%C.
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
     rewrite pow_add. unfold mu. rewrite (mu_carac 2). fold mu.
     rewrite Cpow_add_r. rewrite alpha_is_root.
     rewrite plus_INR.
     rewrite (IH n) by lia. rewrite (IH (n-2)%nat) by lia.
     rewrite Cmult_plus_distr_r, Cmult_plus_distr_l, re_plus.
     ring_simplify. rewrite Rmult_assoc, <-pow_add.
     replace (n-2+2)%nat with n by lia.
     rewrite <- Cpow_add_r.
     replace (2+(n-2))%nat with n by lia.
     rewrite Cmult_1_l. lra.
Qed.

Lemma A2_div_mu_n n :
 A 2 n / mu ^n = coef_mu + 2 * Re (coef_alpha * (alpha/mu)^n)%C.
Proof.
 assert (mu <> 0). { unfold mu. generalize (mu_itvl 2). lra. }
 assert (mu^n <> 0). { now apply pow_nonzero. }
 unfold Cdiv. rewrite Cpow_mul_l, Cpow_inv by (negapply RtoC_inj; auto).
 rewrite Cmult_assoc, RtoC_pow, <- RtoC_inv, re_scal_r by trivial.
 rewrite A2_eqn. field; trivial.
Qed.

Lemma Cmod_alpha_mu : Cmod (alpha/mu) < 1.
Proof.
 assert (0 < mu). { unfold mu. generalize (mu_itvl 2). lra. }
 assert (0 < tau) by (generalize tau_approx; lra).
 apply Rlt_pow2_inv; try lra.
 rewrite Cmod_div by (negapply RtoC_inj; lra).
 rewrite Cmod_R, Rabs_right by lra.
 unfold Rdiv. rewrite Rpow_mult_distr. rewrite alphamod2.
 unfold mu. rewrite tau_inv, Rinv_inv; fold tau; try lra.
 ring_simplify. rewrite tau3. lra.
Qed.

Lemma Lim_A2_div_mu_n :
 is_lim_seq (fun n => A 2 n / mu ^ n) coef_mu.
Proof.
 apply is_lim_seq_ext with
  (u := fun n => coef_mu + 2 * Re (coef_alpha * (alpha/mu)^n)%C).
 { intros n. now rewrite A2_div_mu_n. }
 replace (Rbar.Finite coef_mu) with (Rbar.Finite (coef_mu + 0))
   by (f_equal; lra).
 apply is_lim_seq_plus'; [apply is_lim_seq_const|].
 apply is_lim_seq_0_abs with
  (v := fun n => 2 * Cmod coef_alpha * (Cmod (alpha/mu))^n).
 - intros n.
   rewrite Rabs_mult. rewrite (Rabs_right 2) by lra.
   rewrite Rmult_assoc, <- Cmod_pow, <- Cmod_mult.
   apply Rmult_le_compat_l; try lra.
   apply re_le_Cmod.
 - replace 0 with ((2*Cmod coef_alpha) * 0) by lra.
   apply is_lim_seq_mult'; [apply is_lim_seq_const|].
   apply is_lim_seq_geom.
   rewrite Rabs_right by (apply Rle_ge, Cmod_ge_0).
   apply Cmod_alpha_mu.
Qed.

(** See also Freq.A_ratio now: *)

Lemma Lim_A2_ratio :
 is_lim_seq (fun n => A 2 (S n) / A 2 n) mu.
Proof.
 assert (mu_pos : 0 < mu ).
 { unfold mu. generalize mu_2. lra. }
 assert (coef_mu <> 0).
 { generalize coef_mu_bound. lra. }
 apply is_lim_seq_ext with
     (u := fun n => mu * ((A 2 (S n) / mu ^ (S n))
                          / (A 2 n / mu ^ n))).
 - intros n. simpl pow. field; repeat split; try lra.
   + change 0 with (INR 0). negapply INR_eq. generalize (A_nz 2 n). lia.
   + generalize (pow_lt _ n mu_pos). lra.
 - replace (Rbar.Finite mu) with (Rbar.Rbar_mult mu (coef_mu / coef_mu)).
   2:{ simpl. f_equal. field; auto. }
   apply is_lim_seq_scal_l.
   assert (L := Lim_A2_div_mu_n).
   apply is_lim_seq_div'; auto.
   rewrite is_lim_seq_incr_1 in L. apply L.
Qed.


(** ** Occurrences of letters in morphic word [Words.kseq 2]

    We will see below how this relates to function [h] (a.k.a [f 2])
    and its iterate [h^^2].

    For a finite word [w], the frequency of letter [a] is
    [nbocc a w / length w]. For infinite words, the frequency
    of a letter (if it exists) is the limit of frequencies for
    ever-growing finite prefixes of the infinite word.

    Here for [Words.kseq 2], the frequencies of letters [0],[1],[2]
    will be respectively [tau^3],[tau^4],[tau^2] (another numbering
    of letters would make that more uniform). For proving that and
    even more, we now consider the following differences :
*)

Definition Diff0 w := tau^3 * length w - nbocc 0 w.
Definition Diff1 w := tau^4 * length w - nbocc 1 w.
Definition Diff2 w := tau^2 * length w - nbocc 2 w.

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
 rewrite tau3, tau4. ring_simplify.
 rewrite H, !plus_INR. change (INR 0) with 0. ring.
Qed.

Lemma diff012 n : diff0 n + diff1 n + diff2 n = 0.
Proof.
 apply Diff012.
 apply Forall_nth. intros i d. rewrite take_length. intros H.
 rewrite take_nth by trivial. apply kseq_letters.
Qed.

(** Expressing diff0 and diff2 in terms of [h] and [h^^2] *)

Lemma diff0_alt n :
  diff0 n = h n - tau * n.
Proof.
 unfold diff0, Diff0. rewrite take_length.
 rewrite <- count_nbocc.
 rewrite tau3. rewrite Rmult_minus_distr_r.
 rewrite <- (f_count_0 2 n) at 1 by easy. fold h. rewrite plus_INR. lra.
Qed.

Lemma diff2_alt n :
  diff2 n = tau^2 * n - (h^^2) n.
Proof.
 unfold diff2, Diff2. rewrite take_length.
 rewrite <- count_nbocc.
 now rewrite fs_count_k.
Qed.

(** Equations giving Diff0 and Diff1 after a substitution [ksubst 2].
    Note : this could be stated via a matrix someday.
*)

Lemma Diff0_ksubst2 w :
  Diff0 (apply (ksubst 2) w) = tau * Diff2 w.
Proof.
 unfold Diff0, Diff2.
 rewrite len_ksubst2, plus_INR.
 destruct (nbocc_ksubst2 w) as (-> & _ & _).
 ring_simplify. unfold Rminus. rewrite Rplus_assoc. f_equal.
 rewrite tau3. lra.
Qed.

Lemma Diff2_ksubst2 w :
  List.Forall (fun a => a <= 2)%nat w ->
  Diff2 (apply (ksubst 2) w) = - tau^2 * Diff2 w - Diff0 w.
Proof.
 intros H.
 unfold Diff0, Diff2.
 rewrite len_ksubst2.
 destruct (nbocc_ksubst2 w) as (_ & _ & ->).
 rewrite !plus_INR.
 replace (nbocc 1 w + nbocc 2 w) with (length w - nbocc 0 w).
 2:{ apply len_nbocc_012 in H. rewrite H. rewrite !plus_INR. lra. }
 ring_simplify.
 replace (tau^4) with (1-tau^2-tau^3) by (generalize tau234; lra).
 unfold letter in *. lra.
Qed.

(** For [A 2] numbers, diff0 and diff2 have nice expressions via
    powers of the [alpha] and [alphabar] roots (or some real part of
    a power of [alpha]). Let's first describe the coefficients used
    in these expressions. *)

Definition coefa2 := ((alpha*(tau^2-1)-tau^3)/(alpha-alphabar))%C.
Definition coefa0 := (alphabar * coefa2)%C.

Lemma re_coefa2 : 2*Re coefa2 = tau^2-1.
Proof.
 unfold coefa2.
 change alphabar with (Cconj alpha). rewrite im_alt'.
 change (Im alpha) with im_alpha.
 unfold Cdiv.
 replace (/ (2*Ci*im_alpha))%C with (/Ci * /(2*im_alpha))%C.
 2:{ field; repeat split; try cconst.
     negapply RtoC_inj; apply im_alpha_nz. }
 rewrite Ci_inv.
 replace (-Ci * _)%C with (Ci * -(/(2*im_alpha)))%C by ring.
 rewrite !Cmult_assoc.
 rewrite <- RtoC_mult, <- RtoC_inv, <- RtoC_opp
  by (generalize im_alpha_nz; lra).
 rewrite re_scal_r, re_mult_Ci.
 simpl. field. apply im_alpha_nz.
Qed.

Lemma re_coefa0 : 2*Re coefa0 = tau^3.
Proof.
 unfold coefa0, coefa2. unfold Cdiv.
 rewrite Cmult_assoc.
 replace (alphabar * _)%C
  with ((alpha * alphabar) * (tau^2-1) - alphabar * tau^3)%C by ring.
 rewrite <- Cmod2_conj, alphamod2.
 change alphabar with (Cconj alpha) at 2. rewrite im_alt'.
 change (Im alpha) with im_alpha.
 replace (/ (2*Ci*im_alpha))%C with (/Ci * /(2*im_alpha))%C.
 2:{ field; repeat split; try cconst.
     negapply RtoC_inj; apply im_alpha_nz. }
 rewrite Ci_inv.
 replace (-Ci * _)%C with (Ci * -(/(2*im_alpha)))%C by ring.
 rewrite !Cmult_assoc.
 rewrite <- RtoC_mult, <- RtoC_inv, <- RtoC_opp
  by (generalize im_alpha_nz; lra).
 rewrite re_scal_r, re_mult_Ci.
 simpl. field. apply im_alpha_nz.
Qed.

Lemma diff_A n :
 diff0 (A 2 n) = 2 * Re(coefa0 * alpha^n)%C /\
 diff2 (A 2 n) = 2 * Re(coefa2 * alpha^n)%C.
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
     rewrite Cmult_assoc. change alphabar with (Cconj alpha).
     rewrite <- Cmod2_conj, alphamod2.
     rewrite <- Cmult_assoc, re_scal_l. lra.
   + unfold coefa0.
     rewrite (Cmult_assoc coefa2), (Cmult_comm coefa2 alpha).
     rewrite <- !Cmult_assoc.
     set (c := (coefa2 * (alpha^n))%C).
     replace (-tau^2*(2*Re c)-2*Re (alphabar * c)) with
         (2 * ((-tau^2)*Re c + (-1)*(Re (alphabar * c)))) by ring.
     f_equal.
     rewrite <-!re_scal_l, <-re_plus.
     f_equal.
     rewrite Cmult_assoc. rewrite <- Cmult_plus_distr_r. f_equal.
     replace (-tau^2) with (2*re_alpha) by (rewrite re_alpha_alt; lra).
     rewrite RtoC_mult.
     change re_alpha with (Re alpha).
     rewrite re_alt.
     change (Cconj alpha) with alphabar. field.
Qed.

(** Now, any arbitrary number [n] is a sum of [A 2] numbers by Zeckendorf
    theorem (cf. [GenFib.decomp]). So [diff0 n] will be a sum of powers
    of [alpha]. *)

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
  diff0 n =
   Rlistsum (List.map (fun n => 2*Re(coefa0 * alpha^n)%C) (decomp 2 n)).
Proof.
 unfold diff0.
 rewrite decomp_prefix_kseq.
 rewrite Diff0_concat, List.map_map, List.map_rev, Rlistsum_rev.
 f_equal.
 apply List.map_ext; intros.
 rewrite <- kseq_take_A. apply diff_A.
Qed.

Lemma diff0_decomp_eqn' n :
  diff0 n =
   2*Re (coefa0 * Clistsum (List.map (Cpow alpha) (decomp 2 n))).
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
  2 * Cmod coefa0 * Rlistsum (List.map (pow (Cmod alpha)) (decomp 2 n)).
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

Lemma sum_pow_cons k l n r :
  O<>k -> 0<=r<1 -> Delta k (n::l) ->
  Rlistsum (List.map (pow r) (n::l)) <= r^n/(1-r^k).
Proof.
 intros Hk Hr.
 assert (H3 : 0 <= r^k < 1).
 { apply pow_lt_1_compat. lra. lia. }
 revert n.
 induction l.
 - intros n _. cbn -[pow].
   rewrite Rplus_0_r.
   apply Rcomplements.Rle_div_r; try lra.
   rewrite <- (Rmult_1_r (r^n)) at 2.
   apply Rmult_le_compat_l; try lra.
   apply pow_le; lra.
 - intros n. inversion_clear 1.
   change (Rlistsum _) with (r^n + Rlistsum (List.map (pow r) (a::l))).
   eapply Rle_trans. eapply Rplus_le_compat_l. apply IHl; eauto.
   apply Rcomplements.Rle_div_r; try lra.
   field_simplify; try lra.
   rewrite <- Ropp_mult_distr_l, <- pow_add.
   assert (r^a <= r^(n+k)). { apply Rle_pow_low; auto. }
   lra.
Qed.

Lemma sum_pow k l r :
  O<>k -> 0<=r<1 -> Delta k l ->
  Rlistsum (List.map (pow r) l) <= /(1-r^k).
Proof.
 intros Hk Hr D.
 assert (H3 : 0 <= r^k < 1).
 { apply pow_lt_1_compat. lra. lia. }
 destruct l as [|n l].
 - cbn -[pow].
   rewrite <- (Rmult_1_l (/ _)).
   apply Rcomplements.Rle_div_r; try lra.
 - eapply Rle_trans. apply (sum_pow_cons k); auto.
   rewrite <- (Rmult_1_l (/ _)).
   apply Rmult_le_compat_r.
   rewrite <- (Rmult_1_l (/ _)).
   apply Rcomplements.Rle_div_r; try lra.
   rewrite <-(pow1 n).
   apply pow_maj_Rabs. rewrite Rabs_right; lra.
Qed.

Lemma diff0_indep_bound n :
 Rabs (diff0 n) <= 2 * Cmod coefa0 / (1 - Cmod alpha^3).
Proof.
 eapply Rle_trans. apply diff0_decomp_le.
 unfold Rdiv.
 apply Rmult_le_compat_l.
 - generalize (Cmod_ge_0 coefa0). lra.
 - apply sum_pow; try lia; try apply decomp_delta.
   split; try apply Cmod_ge_0.
   apply Rlt_pow2_inv; try lra.
   rewrite alphamod2. generalize tau_approx. lra.
Qed.

(** Experimentally, this first bound is around 1.112.
    Having this finite bound is enough to prove that the frequency
    of letter 0 is [tau^3] and that [h n / n] converges towards tau.
*)

Lemma lim_diff0_div_n : is_lim_seq (fun n => diff0 n / n) 0.
Proof.
 eapply is_lim_seq_bound. apply diff0_indep_bound.
Qed.

Lemma frequency_0 :
 is_lim_seq (fun n => count (kseq 2) 0 n / n) (tau^3).
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with (u := fun n => tau^3 - diff0 (S n) / S n).
 - intros n.
   unfold diff0, Diff0. rewrite take_length.
   rewrite <- count_nbocc. field. apply RSnz.
 - replace (Rbar.Finite (tau^3)) with (Rbar.Finite (tau^3 + -0))
    by (f_equal; lra).
   eapply is_lim_seq_plus'. apply is_lim_seq_const.
   change (Rbar.Finite (-0)) with (Rbar.Rbar_opp 0).
   apply -> is_lim_seq_opp.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff0 n / n)).
   apply lim_diff0_div_n.
Qed.

Lemma Lim_h_div_n :
 is_lim_seq (fun n => h n / n) tau.
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with (u := fun n => tau + diff0 (S n) / S n).
 - intros n. rewrite diff0_alt. field. apply RSnz.
 - replace (Rbar.Finite tau) with (Rbar.Finite (tau + 0)) by (f_equal; lra).
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

     - [h n = nat_part (tau*n)+{0,1}]
     - [h] is quasi-additive [forall n p, -2 <= h (n+p) - h n - h p <= 2]
*)

Lemma re_alpha2 : Re (alpha^2) = re_alpha^2 - im_alpha^2.
Proof.
 simpl. ring.
Qed.

Lemma re_alpha2_tau : Re (alpha^2) = -tau*(1+tau)/2.
Proof.
 rewrite re_alpha2. rewrite re_alpha_alt, im_alpha_2.
 field_simplify.
 rewrite tau4. field.
Qed.

Lemma im_alpha2 : Im (alpha^2) = 2*re_alpha*im_alpha.
Proof.
 simpl. ring.
Qed.

Definition alpha3 := alpha_is_root.

Lemma alpha4 : (alpha^4 = 1 + alpha + alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha3. ring_simplify. rewrite alpha3. ring.
Qed.

Lemma alpha5 : (alpha^5 = 1 + alpha + 2*alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha4. ring_simplify. rewrite alpha3. ring.
Qed.

Lemma alpha6 : (alpha^6 = 2 + alpha + 3*alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha5. ring_simplify. rewrite alpha3. ring.
Qed.

Lemma alpha7 : (alpha^7 = 3 + 2*alpha + 4*alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha6. ring_simplify. rewrite alpha3. ring.
Qed.

Lemma alpha8 : (alpha^8 = 4 + 3*alpha + 6*alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha7. ring_simplify. rewrite alpha3. ring.
Qed.

Lemma cmod2_trinom_alpha (a b c : R) :
 (Cmod (a + b*alpha + c*alpha^2)%C)^2 =
 (1/4)*((2*a - b*tau^2 - c*tau*(1+tau))^2 + tau*(3+tau)*(b-c*tau^2)^2).
Proof.
 rewrite Cmod2_alt.
 rewrite !re_plus, !im_plus, re_RtoC, im_RtoC.
 rewrite !re_scal_l, !im_scal_l, re_alpha2_tau, im_alpha2.
 simpl Im. simpl Re.
 replace (0 + _ + _) with (im_alpha * (b + c * (2*re_alpha))) by ring.
 rewrite Rpow_mult_distr, im_alpha_2, re_alpha_alt. field.
Qed.

Ltac solve_trinom a b c :=
  replace ((Cmod _)^2) with (Cmod (a+b*alpha+c*alpha^2)%C^2);
  [ rewrite (cmod2_trinom_alpha a b c);
    field_simplify; rewrite ?tau6, ?tau5, ?tau4, ?tau3; field_simplify
  | f_equal; f_equal;
    rewrite ?alpha3, ?alpha4, ?alpha5, ?alpha6, ?alpha7, ?alpha8; ring ].

Definition max3pack := Cmod (1+alpha^3+alpha^7)%C.

Lemma max3pack_eqn : max3pack^2 = 15 - 11*tau - 10*tau^2.
Proof.
 unfold max3pack. solve_trinom 5 2 5. field.
Qed.

(* Curious note : all the trinoms we consider lead to N - M*tau - K*tau^2
   except (Cmod (1+alpha^4+alpha^8)%C)^2 = 8 + 2*tau - 17*tau^2. *)

(* TODO : how to improve the next lemma ? *)
Ltac finish B n := specialize (B n); simpl in B; lia.
Lemma best_3pack_0 l :
  Delta 3 (O::l) -> Below l 9 ->
  Cmod (Clistsum (List.map (Cpow alpha) (O::l))) <= max3pack.
Proof.
 intros D B.
 apply Rle_pow2_inv; [apply Cmod_ge_0| rewrite max3pack_eqn].
 assert (T := tau_approx).
 assert (T2 := tau2_approx).
 inversion D; subst; cbn -[Cpow pow]; simpl (alpha^0)%C.
 { rewrite Cplus_0_r, Cmod_1. lra. (* 1 *) }
 destruct (Nat.eq_dec n 3) as [->|?].
 { inversion H2; subst; cbn -[Cpow pow].
   { solve_trinom 2 0 1. lra. (* 1 + alpha^3 *) }
   destruct (Nat.eq_dec n 6) as [->|?].
   { inversion H4; subst; cbn -[Cpow pow]; [|finish B n].
     solve_trinom 4 1 4. lra. (* 1 + alpha^3 + alpha^6 *) }
   destruct (Nat.eq_dec n 7) as [->|?].
   { inversion H4; subst; cbn -[Cpow pow]; [|finish B n].
     (* 1 + alpha^3 + alpha^7 *)
     apply Req_le. now rewrite Cplus_0_r, Cplus_assoc, <- max3pack_eqn. }
   destruct (Nat.eq_dec n 8) as [->|?]; [|finish B n].
   { inversion H4; subst; cbn -[Cpow pow]; [|finish B n].
     solve_trinom 6 3 7. lra. (* 1+alpha^3+alpha^8 *) }}
 destruct (Nat.eq_dec n 4) as [->|?].
 { inversion H2; subst; cbn -[Cpow pow].
   { solve_trinom 2 1 1. lra. (* 1+alpha^4*) }
   destruct (Nat.eq_dec n 7) as [->|?].
   { inversion H4; subst; cbn -[Cpow pow]; [|finish B n].
     solve_trinom 5 3 5. lra. (* 1+alpha^4+alpha^7 *) }
   destruct (Nat.eq_dec n 8) as [->|?]; [|finish B n].
   { inversion H4; subst; cbn -[Cpow pow]; [|finish B n].
     solve_trinom 6 4 7. lra. (* 1+alpha^4+alpha^8 *) }}
 destruct (Nat.eq_dec n 5) as [->|?].
 { inversion H2; subst; cbn -[Cpow pow].
   { solve_trinom 2 1 2. lra. (* 1+alpha^5 *) }
   destruct (Nat.eq_dec n 8) as [->|?]; [|finish B n].
   { inversion H4; subst; cbn -[Cpow pow]; [|finish B n].
     solve_trinom 6 4 8. lra. (* 1+alpha^5+alpha^8 *) }}
 destruct (Nat.eq_dec n 6) as [->|?].
 { inversion H2; subst; cbn -[Cpow pow]; [|finish B n].
   solve_trinom 3 1 3. lra. (* 1+alpha^6 *) }
 destruct (Nat.eq_dec n 7) as [->|?].
 { inversion H2; subst; cbn -[Cpow pow]; [|finish B n].
   solve_trinom 4 2 4. lra. (* 1+alpha^7 *) }
 destruct (Nat.eq_dec n 8) as [->|?]; [|finish B n].
 { inversion H2; subst; cbn -[Cpow pow]; [|finish B n].
   solve_trinom 5 3 6. lra. (* 1+alpha^8 *) }
Qed.

Lemma Clistsum_factor p l :
 Clistsum (List.map (fun n => alpha^(p+n))%C l) =
 (alpha^p * Clistsum (List.map (Cpow alpha) l))%C.
Proof.
 induction l; cbn -[Cpow].
 - ring.
 - change (List.fold_right Cplus 0)%C with Clistsum. rewrite IHl.
   rewrite Cpow_add_r. ring.
Qed.

Lemma Clistsum_factor_above p l :
 (forall n, List.In n l -> p <= n)%nat ->
 Clistsum (List.map (Cpow alpha) l) =
 (alpha^p * Clistsum (List.map (Cpow alpha) (List.map (decr p) l)))%C.
Proof.
 induction l as [|a l IH]; cbn -[Cpow]; intros Hl.
 - ring.
 - change (List.fold_right Cplus 0)%C with Clistsum. rewrite IH by intuition.
   replace a with ((a-p)+p)%nat at 1 by (specialize (Hl a); lia).
   rewrite Cpow_add_r. unfold decr at 2. ring.
Qed.

Lemma best_3pack l :
  Delta 3 l -> Below l 9 ->
  Cmod (Clistsum (List.map (Cpow alpha) l)) <= max3pack.
Proof.
 intros D B.
 destruct l as [|a l].
 - cbn -[Cpow]. rewrite Cmod_0. apply Cmod_ge_0.
 - revert l D B. induction a as [|a IH]; intros l D B.
   + apply best_3pack_0; auto. unfold Below in *. simpl in *. intuition.
   + replace (S a::l)%list with (List.map S (a :: List.map pred l))%list.
     2:{ simpl. f_equal. rewrite List.map_map.
         rewrite <- (List.map_id l) at 2. apply List.map_ext_in.
         intros b Hb.
         assert (b<>O); try lia.
         { contradict Hb. subst b.
           apply (@Delta_nz' 3 (S a) l); auto; try lia. }}
     rewrite List.map_map, (Clistsum_factor 1), Cmod_mult, Cpow_1_r.
     set (l' := List.map pred l).
     eapply Rle_trans. 2:apply (IH l').
     * rewrite <- (Rmult_1_l (Cmod (Clistsum _))) at 2.
       apply Rmult_le_compat_r; try apply Cmod_ge_0.
       apply Rle_pow2_inv; try lra.
       rewrite alphamod2. generalize tau_approx; lra.
     * unfold l'. clear l'.
       destruct l as [|b l].
       { simpl; constructor. }
       { inversion_clear D. simpl. constructor. lia.
         apply (@Delta_pred 3 (b::l)); auto.
         apply (@Delta_nz' 3 a (b::l)); try lia.
         constructor; auto; try lia. }
       { unfold Below in *. intros y [->|Hy].
         - specialize (B (S y)). simpl in B; lia.
         - unfold l' in *. clear l'.
           rewrite List.in_map_iff in Hy. destruct Hy as (x & <- & Hx).
           assert (x < 9)%nat by (apply (B x); simpl; intuition).
           lia. }
Qed.

Lemma alphamod_lt : 0 < Cmod alpha < 1.
Proof.
 split.
 - apply Cmod_gt_0. unfold alpha. injection 1 as H H'. now apply re_alpha_nz.
 - apply Rlt_pow2_inv; try lra.
   rewrite alphamod2. generalize tau_approx; lra.
Qed.

Lemma alphamod9_lt : 0 < Cmod alpha^9 < 1.
Proof.
 assert (H := alphamod_lt).
 split.
 - apply pow_lt; lra.
 - change ((Cmod alpha)^9) with ((Cmod alpha)*(Cmod alpha)^8).
   apply Rle_lt_trans with (Cmod alpha * 1); try lra.
   apply Rmult_le_compat_l; try lra.
   rewrite <- (pow1 8). apply pow_incr. lra.
Qed.

Lemma Delta_map_decr p k l :
  (forall n, List.In n l -> k <= n)%nat ->
  Delta p l -> Delta p (List.map (decr k) l).
Proof.
 induction l as [|a l IH]; simpl; auto.
 - intros H. inversion 1; subst; constructor.
   + unfold decr. specialize (H a). lia.
   + apply IH; auto.
Qed.

Lemma Clistsum_delta_below N l :
  Delta 3 l -> Below l N ->
  Cmod (Clistsum (List.map (Cpow alpha) l)) <=
   max3pack / (1 - Cmod alpha ^9).
Proof.
 revert l.
 induction N as [N IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases N 9).
 - clear IH. intros l D B.
   eapply Rle_trans. apply best_3pack; auto.
   unfold Below in *. intros y Hy. specialize (B y Hy). lia.
   rewrite <- (Rmult_1_r max3pack) at 1. unfold Rdiv.
   apply Rmult_le_compat_l; try apply Cmod_ge_0.
   rewrite <- (Rmult_1_l (/ _)).
   assert (P := Cmod_ge_0 alpha).
   apply Rcomplements.Rle_div_r; generalize alphamod9_lt; lra.
 - intros l D B. destruct (cut_lt_ge 9 l) as (l1,l2) eqn:E.
   assert (D' := D).
   assert (E' := cut_app 9 l). rewrite E in E'. rewrite <- E' in D',B |- *.
   rewrite Delta_app_iff in D'. destruct D' as (D1 & D2 & D3).
   rewrite List.map_app, Clistsum_app.
   eapply Rle_trans. apply Cmod_triangle.
   eapply Rle_trans; [eapply Rplus_le_compat_r|].
   + apply best_3pack; auto.
     generalize (cut_fst 9 l). now rewrite E.
   + assert (A : forall n, List.In n l2 -> (9 <= n)%nat).
     { intros n Hn. apply (@cut_snd' 3 9 l); auto. now rewrite E. }
     rewrite (Clistsum_factor_above 9 l2) by trivial.
     set (l2' := List.map (decr 9) l2).
     rewrite Cmod_mult.
     replace (max3pack / _)
       with (max3pack + Cmod (alpha^9) * (max3pack / (1 - Cmod alpha ^9))).
     * apply Rplus_le_compat_l.
       apply Rmult_le_compat_l; try apply Cmod_ge_0.
       apply (IH (N-9)%nat); try lia.
       { apply Delta_map_decr; auto. }
       { unfold l2'. intros x Hx. rewrite List.in_map_iff in Hx.
         destruct Hx as (y & <- & Hy).
         specialize (A y Hy).
         assert (y < N)%nat by (apply B; rewrite List.in_app_iff; now right).
         unfold decr. lia. }
     * rewrite Cmod_pow. field. generalize alphamod9_lt; lra.
Qed.

(** We need below to have an upper bound of the elements of a list *)

Fixpoint listmax l :=
 match l with
 | nil => O
 | n::l' => Nat.max n (listmax l')
 end%list.

Lemma listmax_above l :
 forall n, List.In n l -> (n <= listmax l)%nat.
Proof.
 induction l; inversion 1; simpl; subst. apply Nat.le_max_l.
 transitivity (listmax l); auto. apply Nat.le_max_r.
Qed.

Lemma Clistsum_delta l :
  Delta 3 l ->
  Cmod (Clistsum (List.map (Cpow alpha) l)) <=
   max3pack / (1 - Cmod alpha ^9).
Proof.
 intros D.
 apply (Clistsum_delta_below (S (listmax l))); auto.
 intros x Hx. apply listmax_above in Hx. lia.
Qed.

Lemma diff0_better_bound n :
 Rabs (diff0 n) <= 2 * Cmod coefa0 * max3pack / (1 - Cmod alpha ^9).
Proof.
 rewrite diff0_decomp_eqn'.
 rewrite Rabs_mult. rewrite Rabs_right by lra.
 unfold Rdiv. rewrite !Rmult_assoc. apply Rmult_le_compat_l; try lra.
 eapply Rle_trans; [apply re_le_Cmod|].
 rewrite Cmod_mult. apply Rmult_le_compat_l; try apply Cmod_ge_0.
 apply Clistsum_delta, decomp_delta.
Qed.

(* TODO : toujours quelques %C parasites *)

Lemma coefa2_inner_mod :
  Cmod (alpha * (tau ^ 2 - 1) - tau ^ 3)%C ^ 2 = tau*(1-tau).
Proof.
 rewrite !RtoC_pow, <- RtoC_minus.
 rewrite Cmod2_alt. unfold Cminus.
 rewrite re_plus, im_plus, re_scal_r, im_scal_r.
 rewrite <- !RtoC_opp, re_RtoC, im_RtoC, Rplus_0_r. simpl Re; simpl Im.
 rewrite re_alpha_alt.
 rewrite Rpow_mult_distr. rewrite im_alpha_2.
 rewrite tau3. field_simplify.
 replace (tau^8) with ((tau^4)^2) by ring.
 rewrite tau6, tau5, tau4, tau3. field_simplify.
 rewrite tau4, tau3. field.
Qed.

Lemma Cmod2_coefa2 :
  Cmod coefa2 ^2 = (1-tau)/(3+tau).
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
 rewrite pow2_abs. rewrite im_alpha_2. field. generalize tau_approx; lra.
Qed.

(** And finally, we obtain that diff0 is always strictly less than 1.
    (experimentally the new bound is around 0.996) *)

Lemma diff0_lt_1 n : Rabs (diff0 n) < 1.
Proof.
 eapply Rle_lt_trans. apply diff0_better_bound.
 assert (A9 := alphamod9_lt).
 apply -> Rcomplements.Rdiv_lt_1; try lra.
 apply Rlt_pow2_inv; try lra.
 clear A9.
 rewrite !Rpow_mult_distr.
 rewrite max3pack_eqn.
 replace (Cmod alpha^9) with (((Cmod alpha)^2)^4*Cmod alpha) by ring.
 rewrite alphamod2, tau4.
 unfold coefa0. rewrite Cmod_mult, Rpow_mult_distr, Cmod2_coefa2.
 change alphabar with (Cconj alpha). rewrite Cmod_Cconj, alphamod2.
 assert (H := tau_approx).
 assert (H2 := tau2_approx).
 field_simplify; try lra. rewrite alphamod2, tau4, tau3.
 field_simplify; try lra. apply Rcomplements.Rlt_div_l; try lra.
 field_simplify; try lra. rewrite tau3. field_simplify; try lra.
 assert (LT : Cmod alpha * (-4*tau^2 + 8*tau -2) < 151 * tau^2 - 104*tau + 2).
 { apply Rlt_pow2_inv; try lra.
   rewrite Rpow_mult_distr. rewrite alphamod2. ring_simplify.
   rewrite tau5, tau4, tau3. ring_simplify; lra. }
 ring_simplify in LT. lra.
Qed.

(* Print Assumptions diff0_lt_1. *)

(* Consequences for h : *)

Lemma h_alt n : INR (h n) = tau*n + diff0 n.
Proof.
 rewrite diff0_alt; lra.
Qed.

Lemma h_natpart_or (n:nat) :
 h n = nat_part (tau*n) \/ h n = S (nat_part (tau*n)).
Proof.
assert (-1 < tau*n - h n < 1).
{ rewrite h_alt.
  assert (H := diff0_lt_1 n).
  rewrite Rcomplements.Rabs_lt_between in H. lra. }
destruct (Rle_or_lt 0 (tau*n-h n)).
- left. symmetry. apply nat_part_carac; lra.
- right.
  case (Nat.eq_dec n 0); intros Hn.
  + subst n. change (h 0) with O in *. simpl in *. lra.
  + assert (h n <> O). { contradict Hn. eapply f_0_inv; eauto. }
    assert (nat_part (tau*n) = h n -1)%nat; try lia.
    apply nat_part_carac. rewrite minus_INR by lia. simpl. lra.
Qed.

(* NB: both sides are reached, e.g. left for n=0 and right for n=1.
   I've found no easy way to predict on which side will be some (h n). *)

Lemma h_natpart_bound (n:nat) :
 (nat_part (tau*n) <= h n <= 1 + nat_part (tau*n))%nat.
Proof.
 destruct (h_natpart_or n) as [-> | ->]; lia.
Qed.

(* A quasi-additivity result for h = f 2 that I was unable to obtain
   directly on h. *)

Lemma h_quasiadd p n :
 (h p + h n -2 <= h (p+n) <= h p + h n + 2)%nat.
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
  diff2 n =
   Rlistsum (List.map (fun n => 2*Re(coefa2 * alpha^n)%C) (decomp 2 n)).
Proof.
 unfold diff2.
 rewrite decomp_prefix_kseq.
 rewrite Diff2_concat, List.map_map, List.map_rev, Rlistsum_rev.
 f_equal.
 apply List.map_ext; intros.
 rewrite <- kseq_take_A. apply diff_A.
Qed.

Lemma diff2_decomp_eqn' n :
  diff2 n =
   2*Re (coefa2 * Clistsum (List.map (Cpow alpha) (decomp 2 n))).
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
  2 * Cmod coefa2 * Rlistsum (List.map (pow (Cmod alpha)) (decomp 2 n)).
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
 Rabs (diff2 n) <= 2 * Cmod coefa2 / (1 - Cmod alpha^3).
Proof.
 eapply Rle_trans. apply diff2_decomp_le.
 unfold Rdiv.
 apply Rmult_le_compat_l.
 - generalize (Cmod_ge_0 coefa2). lra.
 - apply sum_pow; try lia; try apply decomp_delta.
   split; try apply Cmod_ge_0.
   apply Rlt_pow2_inv; try lra.
   rewrite alphamod2. generalize tau_approx. lra.
Qed.

Lemma diff2_lt_2 n : Rabs (diff2 n) < 2.
Proof.
 eapply Rle_lt_trans. apply diff2_indep_bound.
 replace 2 with (2*1) at 2 by lra.
 unfold Rdiv. rewrite Rmult_assoc. apply Rmult_lt_compat_l; try lra.
 assert (H := tau_approx).
 assert (H2 := tau2_approx).
 assert (Cmod alpha^3 < 1).
 { apply Rlt_pow2_inv; try lra. ring_simplify.
   change 6%nat with (2*3)%nat. rewrite pow_mult, alphamod2, tau3. lra. }
 apply Rcomplements.Rlt_div_l; try lra.
 rewrite Rmult_1_l.
 apply Rlt_pow2_inv; try lra. rewrite Cmod2_coefa2.
 apply Rcomplements.Rlt_div_l; try lra.
 ring_simplify.
 change 6%nat with (2*3)%nat. rewrite pow_mult, alphamod2, tau3.
 ring_simplify.
 assert (LT : Cmod alpha^3 * (2*tau + 6) < 5 - tau^2).
 { apply Rlt_pow2_inv; try lra.
   rewrite Rpow_mult_distr. ring_simplify.
   change 6%nat with (2*3)%nat. rewrite pow_mult, alphamod2, tau3.
   ring_simplify. rewrite tau3, tau4. ring_simplify. lra. }
 ring_simplify in LT. lra.
Qed.


(** Experimentally, this bound for diff2 is around 1.3462 and cannot be
    improved significantly (unlike the first bound 1.112 for diff0 improved
    to 0.996 later).
    Anyway, having this finite bound is enough to prove that the frequency
    of letter 2 is [tau^2] and that [(h^^2)(n) / n] converges towards [tau^2].
*)

Lemma lim_diff2_div_n : is_lim_seq (fun n => diff2 n / n) 0.
Proof.
 eapply is_lim_seq_bound. apply diff2_indep_bound.
Qed.

Lemma frequency_2 :
 is_lim_seq (fun n => count (kseq 2) 2 n / n) (tau^2).
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with
  (u := fun n => tau^2 - diff2 (S n) / INR (S n)).
 - intros n.
   unfold diff2, Diff2. rewrite take_length.
   rewrite <- count_nbocc. field. apply RSnz.
 - replace (Rbar.Finite (tau^2)) with (Rbar.Finite (tau^2 + -0))
    by (f_equal; lra).
   eapply is_lim_seq_plus'. apply is_lim_seq_const.
   change (Rbar.Finite (-0)) with (Rbar.Rbar_opp 0).
   apply -> is_lim_seq_opp.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff2 n / n)).
   apply lim_diff2_div_n.
Qed.

Lemma frequency_1 :
 is_lim_seq (fun n => count (kseq 2) 1 n / n) (tau^4).
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with
  (u := fun n => tau^4 + diff0 (S n) / INR (S n) + diff2 (S n) / INR (S n)).
 - intros n.
   field_simplify; try apply RSnz. f_equal.
   rewrite Rplus_assoc.
   replace (diff0 (S n) + diff2 (S n)) with (-diff1 (S n))
     by (generalize (diff012 (S n)); lra).
   unfold diff1, Diff1. rewrite take_length.
   rewrite <- count_nbocc. field.
 - replace (Rbar.Finite (tau^4)) with (Rbar.Finite (tau^4 + 0 + 0))
    by (f_equal; lra).
   apply is_lim_seq_plus'. apply is_lim_seq_plus'. apply is_lim_seq_const.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff0 n / n)).
   apply lim_diff0_div_n.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff2 n / n)).
   apply lim_diff2_div_n.
Qed.

Lemma Lim_h2_div_n :
 is_lim_seq (fun n => (h^^2) n / n) (tau^2).
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with
  (u := fun n => tau^2 - diff2 (S n) / INR (S n)).
 - intros n. rewrite diff2_alt. field. rewrite S_INR.
   generalize (pos_INR n). lra.
 - replace (Rbar.Finite (tau^2)) with (Rbar.Finite (tau^2 - 0))
    by (f_equal; lra).
   eapply is_lim_seq_plus'. apply is_lim_seq_const.
   change (Rbar.Finite (-0)) with (Rbar.Rbar_opp 0).
   apply -> is_lim_seq_opp.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff2 n / n)).
   apply lim_diff2_div_n.
Qed.

Lemma h2_alt n : INR ((h^^2) n) = tau^2 * n - diff2 n.
Proof.
 rewrite diff2_alt; lra.
Qed.


(** Distance between [h^^2] and [nat_part (tau^2 * n)].
    This distance may be "+2", for instance for n=1235.
    But the theoretical "-1" does not seem to happen
    (TODO: how to prove it ?) *)

Lemma h2_natpart_bound (n:nat) :
 (nat_part (tau^2 * n) -1 <= (h^^2) n <= 2 + nat_part (tau^2 * n))%nat.
Proof.
 split.
 - assert (nat_part (tau^2 * n) < 2 + (h^^2) n)%nat; try lia.
   { apply nat_part_lt. split.
     - apply Rmult_le_pos. generalize tau2_approx; lra. apply pos_INR.
     - rewrite plus_INR. replace (INR 2) with 2 by auto.
       assert (LT := diff2_lt_2 n). apply Rcomplements.Rabs_lt_between in LT.
       generalize (diff2_alt n). lra. }
 - assert ((h^^2) n - 2 <= nat_part (tau^2 * n))%nat; try lia.
   { apply nat_part_le.
     - apply Rmult_le_pos. generalize tau2_approx; lra. apply pos_INR.
     - destruct (Nat.le_gt_cases 4 n) as [LE|LT].
       + assert (LE' := fs_mono 2 2 LE).
         rewrite minus_INR by trivial.
         replace (INR 2) with 2 by auto.
         assert (LT := diff2_lt_2 n). apply Rcomplements.Rabs_lt_between in LT.
         generalize (diff2_alt n). lra.
       + destruct n. simpl; lra.
         destruct n. simpl. rewrite !Rmult_1_r. generalize tau2_approx. lra.
         destruct n. simpl. rewrite !Rmult_1_r. generalize tau2_approx. lra.
         destruct n. simpl. rewrite !Rmult_1_r. generalize tau2_approx. lra.
         lia. }
Qed.

(* TODO: next cases

For k=3, an extra negative real root. The complex roots can be expressed
 in function of the real roots. Similar convergence and results than for k=2,
 except that (f 3 n) could be further apart from (nat_part (tau 3 * n)).

For k=4, four complex roots : j and (Cconj j) of modulus 1, and
  some alpha and (Cconj alpha) of modulus < 1. Note that alpha can be
  expressed in function of (tau 4). Apparently, no more finite bound to
  (f 4 n - tau 4 * n).

Afterwards, always some complex root of modulus > 1 (but < mu k).
And (f k n - tau k * n) seems to diverge.
*)
