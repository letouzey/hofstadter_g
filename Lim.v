
From Coq Require Import Arith Reals Lra Lia R_Ifp R_sqrt Ranalysis5.
From Coquelicot Require Import Complex Lim_seq.
Require Import FunG GenFib GenG GenAdd Words Phi MoreComplex.

Open Scope Z.
Open Scope R.

Local Coercion INR : nat >-> R.

(* Tactic negapply : With f : C->D ; turn a goal ~C into a subgoal ~D *)
Ltac negapply f :=
 let H := fresh in intro H; apply f in H;
 let c := type of H in revert H; change (not c).

(* Some extra lemmas on Reals. TODO move elsewhere someday *)
Lemma Rle_pow_low r n m : 0<=r<1 -> (n<=m)%nat -> r^m <= r^n.
Proof.
 induction 2; try lra.
 simpl. apply Rle_trans with (1 * r^m); try lra.
 apply Rmult_le_compat_r; try lra. apply pow_le; lra.
Qed.

Lemma Rlt_pow2_inv x y : 0 <= y -> x^2 < y^2 -> x < y.
Proof.
 intros Hy LT.
 destruct (Rle_or_lt 0 x) as [Hx|Hx]; try lra.
 rewrite <- (Rabs_right x), <- (Rabs_right y) by lra.
 apply Rsqr_lt_abs_0. now rewrite !Rsqr_pow2.
Qed.


(** * Studying some limits *)

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

Lemma tau_2 : 0.682327 < tau 2 < 0.682328.
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

(* Sums of (list R) and (list C). *)

Definition Rlistsum l := List.fold_right Rplus 0 l.

Definition Clistsum l := List.fold_right Cplus 0%C l.

Lemma Rlistsum_cons x l : Rlistsum (x::l) = x + Rlistsum l.
Proof.
 reflexivity.
Qed.

Lemma Rlistsum_app l l' : Rlistsum (l++l') = Rlistsum l + Rlistsum l'.
Proof.
 induction l; simpl; rewrite ?IHl; lra.
Qed.

Lemma Rlistsum_rev l : Rlistsum (List.rev l) = Rlistsum l.
Proof.
 induction l; simpl; auto.
 rewrite Rlistsum_app, IHl. simpl; lra.
Qed.

Lemma Clistsum_cons x l : Clistsum (x::l) = (x + Clistsum l)%C.
Proof.
 reflexivity.
Qed.

Lemma Clistsum_app l l' : Clistsum (l++l') = (Clistsum l + Clistsum l')%C.
Proof.
 induction l; simpl; rewrite ?IHl; ring.
Qed.

(* We now focus on the case k=2 : other complex roots, and expressing
   (A 2 n) in term of combinations of root powers. *)

Module K_2.

Definition mu := mu 2.
Definition tau := tau 2.

Definition re_alpha := (1 - mu)/2.
Definition im_alpha := sqrt (tau * (3+tau))/2.

Definition alpha : C := (re_alpha, im_alpha).
Definition alphabar : C := (re_alpha, - im_alpha).

Lemma tau3 : tau^3 = 1 - tau.
Proof.
 assert (E := tau_carac 2). fold tau in E. lra.
Qed.

Lemma tau234 : tau^2 + tau^3 + tau^4 = 1.
Proof.
 assert (E := tau3).
 assert (E' := E). apply (Rmult_eq_compat_l tau) in E'.
 ring_simplify in E'. lra.
Qed.

Lemma tau4 : tau^4 = tau - tau^2.
Proof.
 generalize tau234. rewrite tau3. lra.
Qed.

Lemma tau5 : tau^5 = tau + tau^2 - 1.
Proof.
 change (tau^5) with (tau*tau^4). rewrite tau4. ring_simplify.
 rewrite tau3. ring.
Qed.

Lemma tau6 : tau^6 = (1-tau)^2.
Proof.
 change 6%nat with (3*2)%nat. now rewrite pow_mult, tau3.
Qed.

Lemma tau_approx : 0.682327 < tau < 0.682328.
Proof.
 apply tau_2.
Qed.

Lemma tau2_approx : 0.465570 < tau^2 < 0.465572.
Proof.
 assert (H := tau_approx).
 simpl. rewrite Rmult_1_r. split.
 - apply Rlt_trans with (0.682327*0.682327); try lra.
   apply Rmult_le_0_lt_compat; lra.
 - apply Rlt_trans with (0.682328*0.682328); try lra.
   apply Rmult_le_0_lt_compat; lra.
Qed.

Lemma re_alpha_alt : re_alpha = - tau ^ 2 / 2.
Proof.
 unfold re_alpha. f_equal.
 unfold mu. rewrite tau_inv. fold tau.
 assert (tau <> 0) by (generalize tau_approx; lra).
 apply Rmult_eq_reg_l with (tau); trivial.
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
 rewrite <- !RtoC_pow, <- RtoC_plus. unfold mu. now rewrite (mu_carac 2).
Qed.

Lemma alpha_is_root : (alpha^3 = alpha^2 + 1)%C.
Proof.
 simpl. rewrite !Cmult_1_r. unfold alpha. unfold Cmult; simpl.
 unfold Cplus; simpl. f_equal; ring_simplify.
 - apply Rminus_diag_uniq.
   rewrite im_alpha_2, re_alpha_alt.
   unfold Rdiv. rewrite !Rpow_mult_distr.
   field_simplify.
   rewrite tau6, tau4, tau3. field.
 - replace (im_alpha ^ 3) with (im_alpha^2 * im_alpha) by ring.
   cut ((3* re_alpha^2 - im_alpha^2)*im_alpha = (2 * re_alpha)*im_alpha);
    try lra.
   f_equal.
   rewrite im_alpha_2. rewrite re_alpha_alt.
   field_simplify.
   rewrite tau4. field.
Qed.

Lemma alphabar_is_root : (alphabar^3 = alphabar^2 + 1)%C.
Proof.
 change alphabar with (Cconj alpha).
 rewrite <- !Cpow_conj. rewrite alpha_is_root.
 rewrite Cplus_conj. f_equal. compute; f_equal; lra.
Qed.

Lemma re_alpha_nz : re_alpha <> 0.
Proof.
 unfold re_alpha, mu. generalize mu_2. lra.
Qed.

Lemma im_alpha_nz : im_alpha <> 0.
Proof.
 assert (LT : 0 < im_alpha ^2).
 { rewrite im_alpha_2. unfold Rdiv.
   repeat apply Rmult_lt_0_compat; generalize tau_approx; lra. }
 apply sqrt_lt_R0 in LT. rewrite sqrt_pow2 in LT.
 lra.
 unfold im_alpha. apply Rle_mult_inv_pos; try lra. apply sqrt_pos.
Qed.

Lemma distinct_roots :
  alpha <> mu /\ alphabar <> mu /\ alpha <> alphabar.
Proof.
 unfold alpha, alphabar, RtoC; repeat split.
 - intros [= A B]. now destruct im_alpha_nz.
 - intros [= A B]. generalize im_alpha_nz. lra.
 - intros [= B]. generalize im_alpha_nz. lra.
Qed.

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
 { unfold mu, tau, Lim.tau. field. fold mu. lra. }
 split; apply Rminus_gt_0_lt; ring_simplify; lra.
Qed.

Lemma coef_mu_bound : 1.30 < coef_mu < 1.32.
Proof.
 unfold coef_mu. generalize re_coef_alpha_bound. lra.
Qed.

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
 rewrite <- RtoC_pow, <- RtoC_minus, im_RtoC.
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
 rewrite Cplus_comm, RtoC_opp, RtoC_pow. fold (Cminus (alpha^2) (mu^2))%C.
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
 rewrite <- !RtoC_pow, <- !RtoC_minus, re_RtoC, im_RtoC.
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
 unfold Cdiv. rewrite Cpow_mult_l, Cpow_inv by (negapply RtoC_inj; auto).
 rewrite Cmult_assoc, <- RtoC_pow, <- RtoC_inv, re_scal_r by trivial.
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
 unfold mu. rewrite tau_inv, Rinv_involutive; fold tau; try lra.
 ring_simplify. rewrite tau3. lra.
Qed.

Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

Lemma Lim_A2_div_mu_n :
 is_lim_seq (fun n => A 2 n / mu ^ n) coef_mu.
Proof.
 apply is_lim_seq_ext with
  (u := fun n => coef_mu + 2 * Re (coef_alpha * (alpha/mu)^n)%C).
 { intros n. now rewrite A2_div_mu_n. }
 replace (Rbar.Finite coef_mu) with (Rbar.Finite (coef_mu + 0))
   by (f_equal; lra).
 apply is_lim_seq_plus'; [apply is_lim_seq_const|].
 apply is_lim_seq_abs_0.
 apply is_lim_seq_le_le with
     (u := fun _ => 0)
     (w := fun n => 2 * Cmod coef_alpha * (Cmod (alpha/mu))^n).
 - intros n; split; try apply Rabs_pos.
   rewrite Rabs_mult. rewrite (Rabs_right 2) by lra.
   rewrite Rmult_assoc, <- Cmod_pow, <- Cmod_mult.
   apply Rmult_le_compat_l; try lra.
   apply re_le_Cmod.
 - apply is_lim_seq_const.
 - replace 0 with ((2*Cmod coef_alpha) * 0) by lra.
   apply is_lim_seq_mult'; [apply is_lim_seq_const|].
   apply is_lim_seq_geom.
   rewrite Rabs_right by (apply Rle_ge, Cmod_ge_0).
   apply Cmod_alpha_mu.
Qed.

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


(* Occurrences of letters in (Words.kseq 2)
   and consequences for h = f 2 and h^^2 *)

Definition Delta0 w := tau^3 * length w - nbocc 0 w.
Definition Delta2 w := tau^2 * length w - nbocc 2 w.

Definition delta0 n := Delta0 (take n (kseq 2)).
Definition delta2 n := Delta2 (take n (kseq 2)).

Lemma Delta0_app u v : Delta0 (u++v) = Delta0 u + Delta0 v.
Proof.
 unfold Delta0.
 rewrite List.app_length, nbocc_app, !plus_INR. lra.
Qed.

Lemma Delta0_concat l : Delta0 (List.concat l) = Rlistsum (List.map Delta0 l).
Proof.
 induction l; simpl; auto.
 - unfold Delta0. simpl. lra.
 - rewrite Delta0_app. lra.
Qed.

Lemma Delta0_ksubst2 w :
  Delta0 (apply (ksubst 2) w) = tau * Delta2 w.
Proof.
 unfold Delta0, Delta2.
 rewrite len_ksubst2, plus_INR.
 destruct (nbocc_ksubst2 w) as (-> & _ & _).
 ring_simplify. unfold Rminus. rewrite Rplus_assoc. f_equal.
 rewrite tau3. lra.
Qed.

Lemma Delta2_ksubst2 w :
  List.Forall (fun a => a <= 2)%nat w ->
  Delta2 (apply (ksubst 2) w) = - tau^2 * Delta2 w - Delta0 w.
Proof.
 intros H.
 unfold Delta0, Delta2.
 rewrite len_ksubst2.
 destruct (nbocc_ksubst2 w) as (_ & _ & ->).
 rewrite !plus_INR.
 replace (nbocc 1 w + nbocc 2 w) with (length w - nbocc 0 w).
 2:{ apply len_alt in H. rewrite H. rewrite !plus_INR. lra. }
 ring_simplify.
 replace (tau^4) with (1-tau^2-tau^3) by (generalize tau234; lra).
 unfold letter in *. lra.
Qed.

Lemma delta0_alt n :
  delta0 n = h n - tau * n.
Proof.
 unfold delta0, Delta0. rewrite take_length.
 rewrite <- count_nbocc.
 rewrite tau3. rewrite Rmult_minus_distr_r.
 rewrite <- (f_count_0 2 n) at 1 by easy. fold h. rewrite plus_INR. lra.
Qed.

Lemma delta2_alt n :
  delta2 n = tau^2 * n - (h^^2) n.
Proof.
 unfold delta2, Delta2. rewrite take_length.
 rewrite <- count_nbocc.
 now rewrite fs_count_k.
Qed.

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

Lemma delta_A n :
 delta0 (A 2 n) = 2 * Re(coefa0 * alpha^n)%C /\
 delta2 (A 2 n) = 2 * Re(coefa2 * alpha^n)%C.
Proof.
 induction n as [|n IH].
 - simpl A. simpl Cpow.
   unfold delta0, delta2. simpl take. change (kseq 2 0) with 2%nat.
   unfold Delta0, Delta2. simpl length. simpl nbocc.
   rewrite !Cmult_1_r. rewrite re_coefa0, re_coefa2. simpl; lra.
 - unfold delta0, delta2.
   rewrite kseq_take_A, kword_S.
   rewrite Delta0_ksubst2, Delta2_ksubst2 by (apply kword_letters).
   rewrite <- kseq_take_A. fold (delta0 (A 2 n)) (delta2 (A 2 n)).
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
     change (Cconj alpha) with alphabar.
     change (-1) with (-(1)). rewrite RtoC_opp. field. cconst.
Qed.

Lemma delta0_decomp_eqn n :
  delta0 n =
   Rlistsum (List.map (fun n => 2*Re(coefa0 * alpha^n)%C) (decomp 2 n)).
Proof.
 unfold delta0.
 rewrite decomp_prefix_kseq.
 rewrite Delta0_concat, List.map_map, List.map_rev, Rlistsum_rev.
 f_equal.
 apply List.map_ext; intros.
 rewrite <- kseq_take_A. apply delta_A.
Qed.

Lemma delta0_decomp_eqn' n :
  delta0 n =
   2*Re (coefa0 * Clistsum (List.map (Cpow alpha) (decomp 2 n))).
Proof.
 rewrite delta0_decomp_eqn.
 induction decomp; cbn -[Re].
 - rewrite Cmult_0_r. cconst.
 - rewrite Cmult_plus_distr_l, re_plus, Rmult_plus_distr_l.
   f_equal. apply IHl.
Qed.

Lemma delta0_decomp_bound n :
 Rabs (delta0 n) <=
  2 * Cmod coefa0 * Rlistsum (List.map (pow (Cmod alpha)) (decomp 2 n)).
Proof.
 rewrite delta0_decomp_eqn.
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
  O<>k -> 0<=r<1 -> DeltaList.Delta k (n::l) ->
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
  O<>k -> 0<=r<1 -> DeltaList.Delta k l ->
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

Lemma delta0_indep_bound n :
 Rabs (delta0 n) <= 2 * Cmod coefa0 / (1 - Cmod alpha^3).
Proof.
 eapply Rle_trans. apply delta0_decomp_bound.
 unfold Rdiv.
 apply Rmult_le_compat_l.
 - generalize (Cmod_ge_0 coefa0). lra.
 - apply sum_pow; try lia; try apply decomp_delta.
   split; try apply Cmod_ge_0.
   apply Rlt_pow2_inv; try lra.
   rewrite alphamod2. generalize tau_approx. lra.
Qed.

(* Experimentally, this first bound is around 1.112.
   Having this finite bound is enough to prove that (h n)/n
   converges towards tau.
   We prove below a better bound, strictly below 1.
*)

Lemma Lim_h_div_n :
 is_lim_seq (fun n => h n / n) tau.
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with
  (u := fun n => tau + delta0 (S n) / INR (S n)).
 - intros n. rewrite delta0_alt. field. rewrite S_INR.
   generalize (pos_INR n). lra.
 - replace (Rbar.Finite tau) with (Rbar.Finite (tau + 0)) by (f_equal; lra).
   eapply is_lim_seq_plus'. apply is_lim_seq_const.
   set (K := 2 * Cmod coefa0 / (1 - (Cmod alpha)^3)).
   apply is_lim_seq_le_le with
     (u := fun n => -K / S n)
     (w := fun n => K / S n).
   + intros n.
     assert (LE := delta0_indep_bound (S n)). fold K in LE.
     apply Rcomplements.Rabs_le_between in LE.
     assert (0 <= / S n).
     { rewrite <- (Rmult_1_l (/ _)). apply Rle_mult_inv_pos; try lra.
       rewrite S_INR. generalize (pos_INR n). lra. }
     split; unfold Rdiv; apply Rmult_le_compat_r; lra.
   + apply (is_lim_seq_div _ _ (-K) Rbar.p_infty); try easy.
     * apply is_lim_seq_const.
     * rewrite <- is_lim_seq_incr_1. apply is_lim_seq_INR.
     * red. red. simpl. now rewrite Rmult_0_r.
   + apply (is_lim_seq_div _ _ K Rbar.p_infty); try easy.
     * apply is_lim_seq_const.
     * rewrite <- is_lim_seq_incr_1. apply is_lim_seq_INR.
     * red. red. simpl. now rewrite Rmult_0_r.
Qed.

(* NB : Classical reals are now Dedekind cuts,
   just 4 logical axioms remaining :)
*)

(* Print Assumptions Lim_H_div_n. *)

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

Lemma alpha4 : (alpha^4 = 1 + alpha + alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha_is_root. ring_simplify.
 rewrite alpha_is_root. ring.
Qed.

(* TODO : ring on C cannot handle basic constant simplification like 2+1=3 *)

Lemma alpha5 : (alpha^5 = 1 + alpha + 2*alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha4. ring_simplify.
 rewrite alpha_is_root.
 replace (RtoC 2) with (1+1)%C by cconst. ring.
Qed.

Lemma alpha6 : (alpha^6 = 2 + alpha + 3*alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha5. ring_simplify.
 rewrite alpha_is_root.
 replace (RtoC 3) with (1+2)%C by cconst. ring.
Qed.

Lemma alpha7 : (alpha^7 = 3 + 2*alpha + 4*alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha6. ring_simplify.
 rewrite alpha_is_root.
 replace (RtoC 4) with (1+3)%C by cconst. ring.
Qed.

Lemma alpha8 : (alpha^8 = 4 + 3*alpha + 6*alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha7. ring_simplify.
 rewrite alpha_is_root.
 replace (RtoC 6) with (2+4)%C by cconst. ring.
Qed.

Lemma eqn_03 :
 (Cmod (1+alpha^3)%C)^2 = 4 - 2*tau - tau^2.
Proof.
 transitivity ((Cmod (2+0*alpha+1*alpha^2)%C)^2).
 - f_equal. f_equal. rewrite alpha_is_root.
   replace (RtoC 2) with (1+1)%C by cconst. ring.
 - rewrite cmod2_trinom_alpha.
   field_simplify. rewrite ?tau6, ?tau5, ?tau4, ?tau3. field.
Qed.

Lemma eqn_04 :
 (Cmod (1+alpha^4)%C)^2 = 3 - 3 * tau^2.
Proof.
 transitivity ((Cmod (2+1*alpha+1*alpha^2)%C)^2).
 - f_equal. f_equal. rewrite alpha4.
   replace (RtoC 2) with (1+1)%C by cconst. ring.
 - rewrite cmod2_trinom_alpha.
   field_simplify. rewrite ?tau6, ?tau5, ?tau4, ?tau3. field.
Qed.

Lemma eqn_05 :
 (Cmod (1+alpha^5)%C)^2 = 2 - tau - 2 * tau^2.
Proof.
 transitivity ((Cmod (2+1*alpha+2*alpha^2)%C)^2).
 - f_equal. f_equal. rewrite alpha5.
   replace (RtoC 2) with (1+1)%C at 2 by cconst. ring.
 - rewrite cmod2_trinom_alpha.
   field_simplify. rewrite ?tau6, ?tau5, ?tau4, ?tau3. field.
Qed.

Lemma eqn_06 :
 (Cmod (1+alpha^6)%C)^2 = 6 - 5 * tau - 3 * tau^2.
Proof.
 transitivity ((Cmod (3+1*alpha+3*alpha^2)%C)^2).
 - f_equal. f_equal. rewrite alpha6.
   replace (RtoC 3) with (1+2)%C at 2 by cconst. ring.
 - rewrite cmod2_trinom_alpha.
   field_simplify. rewrite ?tau6, ?tau5, ?tau4, ?tau3. field.
Qed.

Lemma eqn_07 :
 (Cmod (1+alpha^7)%C)^2 = 8 - 4 * tau - 8 * tau^2.
Proof.
 transitivity ((Cmod (4+2*alpha+4*alpha^2)%C)^2).
 - f_equal. f_equal. rewrite alpha7.
   replace (RtoC 4) with (1+3)%C at 2 by cconst. ring.
 - rewrite cmod2_trinom_alpha.
   field_simplify. rewrite ?tau6, ?tau5, ?tau4, ?tau3. field.
Qed.

Lemma eqn_08 :
 (Cmod (1+alpha^8)%C)^2 = 7 - 3 * tau - 9 * tau^2.
Proof.
 transitivity ((Cmod (5+3*alpha+6*alpha^2)%C)^2).
 - f_equal. f_equal. rewrite alpha8.
   replace (RtoC 5) with (1+4)%C by cconst. ring.
 - rewrite cmod2_trinom_alpha.
   field_simplify. rewrite ?tau6, ?tau5, ?tau4, ?tau3. field.
Qed.

Lemma eqn_036 :
 (Cmod (1+alpha^3+alpha^6)%C)^2 = 12 - 11*tau - 4*tau^2.
Proof.
 transitivity ((Cmod (4+1*alpha+4*alpha^2)%C)^2).
 - f_equal. f_equal. rewrite alpha6, alpha_is_root.
   replace (RtoC 4) with (1+1+2)%C at 1 by cconst.
   replace (RtoC 4) with (1+3)%C by cconst. ring.
 - rewrite cmod2_trinom_alpha.
   field_simplify. rewrite ?tau6, ?tau5, ?tau4, ?tau3. field.
Qed.

Lemma eqn_037 :
 (Cmod (1+alpha^3+alpha^7)%C)^2 = 15 - 11*tau - 10*tau^2.
Proof.
 transitivity ((Cmod (5+2*alpha+5*alpha^2)%C)^2).
 - f_equal. f_equal. rewrite alpha7, alpha_is_root.
   replace (RtoC 5) with (1+1+3)%C at 1 by cconst.
   replace (RtoC 5) with (1+4)%C by cconst. ring.
 - rewrite cmod2_trinom_alpha.
   field_simplify.
   rewrite tau6, tau5, tau4, tau3. field.
Qed.

Lemma eqn_038 :
 (Cmod (1+alpha^3+alpha^8)%C)^2 = 15 - 12*tau - 11*tau^2.
Proof.
 transitivity ((Cmod (6+3*alpha+7*alpha^2)%C)^2).
 - f_equal. f_equal. rewrite alpha8, alpha_is_root.
   replace (RtoC 6) with (1+1+4)%C at 2 by cconst.
   replace (RtoC 7) with (1+6)%C by cconst. ring.
 - rewrite cmod2_trinom_alpha.
   field_simplify. rewrite ?tau6, ?tau5, ?tau4, ?tau3. field.
Qed.

Lemma eqn_047 :
 (Cmod (1+alpha^4+alpha^7)%C)^2 = 10 - tau - 15*tau^2.
Proof.
 transitivity ((Cmod (5+3*alpha+5*alpha^2)%C)^2).
 - f_equal. f_equal. rewrite alpha7, alpha4.
   replace (RtoC 5) with (1+1+3)%C at 1 by cconst.
   replace (RtoC 5) with (1+4)%C by cconst.
   replace (RtoC 3) with (1+2)%C at 3 by cconst. ring.
 - rewrite cmod2_trinom_alpha.
   field_simplify. rewrite ?tau6, ?tau5, ?tau4, ?tau3. field.
Qed.

Lemma eqn_048 :
 (Cmod (1+alpha^4+alpha^8)%C)^2 = 8 + 2*tau - 17*tau^2.
Proof.
 transitivity ((Cmod (6+4*alpha+7*alpha^2)%C)^2).
 - f_equal. f_equal. rewrite alpha8, alpha4.
   replace (RtoC 7) with (1+6)%C by cconst.
   replace (RtoC 4) with (1+3)%C by cconst.
   replace (RtoC 6) with (1+1+1+3)%C at 2 by cconst. ring.
 - rewrite cmod2_trinom_alpha.
   field_simplify. rewrite ?tau6, ?tau5, ?tau4, ?tau3. field.
Qed.

Lemma eqn_058 :
 (Cmod (1+alpha^5+alpha^8)%C)^2 = 4 - 8*tau^2.
Proof.
 transitivity ((Cmod (6+4*alpha+8*alpha^2)%C)^2).
 - f_equal. f_equal. rewrite alpha8, alpha5.
   replace (RtoC 8) with (2+6)%C by cconst.
   replace (RtoC 4) with (1+3)%C at 2 by cconst.
   replace (RtoC 6) with (1+1+4)%C at 2 by cconst. ring.
 - rewrite cmod2_trinom_alpha.
   field_simplify. rewrite ?tau6, ?tau5, ?tau4, ?tau3. field.
Qed.

Definition max3pack := Cmod (1+alpha^3+alpha^7)%C.

Lemma max3pack_eqn : max3pack^2 = 15 - 11*tau - 10*tau^2.
Proof.
 apply eqn_037.
Qed.

(* TODO : pretty ugly, but will do for the moment *)
Lemma best_3pack_0 l :
  DeltaList.Delta 3 (O::l) -> Below l 9 ->
  Cmod (Clistsum (List.map (Cpow alpha) (O::l))) <= max3pack.
Proof.
 intros D B.
 apply Rsqr_incr_0_var; try apply Cmod_ge_0; rewrite !Rsqr_pow2.
 destruct l as [|a l]; cbn -[Cpow pow]; simpl (alpha^0)%C.
 - (* 1 *)
   rewrite Cplus_0_r, Cmod_1, max3pack_eqn.
   generalize tau_approx tau2_approx; lra.
 - inversion_clear D.
   case (Nat.eqb_spec a 3); [intros ->| intros].
   { destruct l as [|b l]; cbn -[Cpow pow].
     - (* 1 + alpha^3 *)
       rewrite Cplus_0_r, eqn_03, max3pack_eqn.
       generalize tau_approx tau2_approx; lra.
     - inversion_clear H0.
       case (Nat.eqb_spec b 6); [intros ->| intros].
       { destruct l as [|c l]; cbn -[Cpow pow].
         - (* 1 + alpha^3 + alpha^7 *)
           rewrite Cplus_0_r, Cplus_assoc, eqn_036, max3pack_eqn.
           generalize tau_approx, tau2_approx; lra.
         - inversion_clear H2. specialize (B c). simpl in B. lia. }
       case (Nat.eqb_spec b 7); [intros ->| intros].
       { destruct l as [|c l]; cbn -[Cpow pow].
         - (* 1 + alpha^3 + alpha^7 *)
           rewrite Cplus_0_r, Cplus_assoc. apply Rle_refl.
         - inversion_clear H2. specialize (B c). simpl in B. lia. }
       case (Nat.eqb_spec b 8); [intros ->| intros].
       { destruct l as [|c l]; cbn -[Cpow pow].
         - (* 1+alpha^3+alpha^8 *)
           rewrite Cplus_0_r, Cplus_assoc, eqn_038, max3pack_eqn.
           generalize tau_approx, tau2_approx; lra.
         - inversion_clear H2. specialize (B c). simpl in B. lia. }
       specialize (B b). simpl in B. lia. }
   case (Nat.eqb_spec a 4); [intros ->| intros].
   { destruct l as [|b l]; cbn -[Cpow pow].
     - (* 1+alpha^4*)
       rewrite Cplus_0_r, eqn_04, max3pack_eqn.
       generalize tau_approx, tau2_approx; lra.
     - inversion_clear H0.
       case (Nat.eqb_spec b 7); [intros ->| intros].
       { destruct l as [|c l]; cbn -[Cpow pow].
         - (* 1+alpha^4+alpha^7 *)
           rewrite Cplus_0_r, Cplus_assoc, eqn_047, max3pack_eqn.
           generalize tau_approx, tau2_approx; lra.
         - inversion_clear H2. specialize (B c). simpl in B. lia. }
       case (Nat.eqb_spec b 8); [intros ->| intros].
       { destruct l as [|c l]; cbn -[Cpow pow].
         - (* 1+alpha^4+alpha^8 *)
           rewrite Cplus_0_r, Cplus_assoc, eqn_048, max3pack_eqn.
           generalize tau_approx, tau2_approx; lra.
         - inversion_clear H2. specialize (B c). simpl in B. lia. }
       specialize (B b). simpl in B. lia. }
   case (Nat.eqb_spec a 5); [intros ->| intros].
   { destruct l as [|b l]; cbn -[Cpow pow].
     - (* 1+alpha^5 *)
       rewrite Cplus_0_r, eqn_05, max3pack_eqn.
       generalize tau_approx, tau2_approx; lra.
     - inversion_clear H0.
       case (Nat.eqb_spec b 8); [intros ->| intros].
       { destruct l as [|c l]; cbn -[Cpow pow].
         - (* 1+alpha^5+alpha^8 *)
           rewrite Cplus_0_r, Cplus_assoc, eqn_058, max3pack_eqn.
           generalize tau_approx, tau2_approx; lra.
         - inversion_clear H2. specialize (B c). simpl in B. lia. }
       specialize (B b). simpl in B. lia. }
   case (Nat.eqb_spec a 6); [intros ->| intros].
   { destruct l as [|b l]; cbn -[Cpow pow].
     - (* 1+alpha^6 *)
       rewrite Cplus_0_r, eqn_06, max3pack_eqn.
       generalize tau_approx, tau2_approx; lra.
     - inversion_clear H0.
       specialize (B b). simpl in B. lia. }
   case (Nat.eqb_spec a 7); [intros ->| intros].
   { destruct l as [|b l]; cbn -[Cpow pow].
     - (* 1+alpha^7 *)
       rewrite Cplus_0_r, eqn_07, max3pack_eqn.
       generalize tau_approx, tau2_approx; lra.
     - inversion_clear H0.
       specialize (B b). simpl in B. lia. }
   case (Nat.eqb_spec a 8); [intros ->| intros].
   { destruct l as [|b l]; cbn -[Cpow pow].
     - (* 1+alpha^8 *)
       rewrite Cplus_0_r, eqn_08, max3pack_eqn.
       generalize tau_approx, tau2_approx; lra.
     - inversion_clear H0.
       specialize (B b). simpl in B. lia. }
   specialize (B a). simpl in B. lia.
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
  DeltaList.Delta 3 l -> Below l 9 ->
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
           apply (@DeltaList.Delta_nz' 3 (S a) l); auto; try lia. }}
     rewrite List.map_map, (Clistsum_factor 1), Cmod_mult, Cpow_1_r.
     set (l' := List.map pred l).
     eapply Rle_trans. 2:apply (IH l').
     * set (c := Clistsum _). rewrite <- (Rmult_1_l (Cmod c)) at 2.
       apply Rmult_le_compat_r; try apply Cmod_ge_0.
       apply Rsqr_incr_0_var; try lra; rewrite !Rsqr_pow2.
       rewrite alphamod2. generalize tau_approx; lra.
     * unfold l'. clear l'.
       destruct l as [|b l].
       { simpl; constructor. }
       { inversion_clear D. simpl. constructor. lia.
         apply (@DeltaList.Delta_pred 3 (b::l)); auto.
         apply (@DeltaList.Delta_nz' 3 a (b::l)); try lia.
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
  DeltaList.Delta p l -> DeltaList.Delta p (List.map (decr k) l).
Proof.
 induction l as [|a l IH]; simpl; auto.
 - intros H. inversion 1; subst; constructor.
   + unfold decr. specialize (H a). lia.
   + apply IH; auto.
Qed.

Lemma Clistsum_delta_below N l :
  DeltaList.Delta 3 l -> Below l N ->
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
   rewrite DeltaList.Delta_app_iff in D'. destruct D' as (D1 & D2 & D3).
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
  DeltaList.Delta 3 l ->
  Cmod (Clistsum (List.map (Cpow alpha) l)) <=
   max3pack / (1 - Cmod alpha ^9).
Proof.
 intros D.
 apply (Clistsum_delta_below (S (listmax l))); auto.
 intros x Hx. apply listmax_above in Hx. lia.
Qed.

Lemma delta0_better_bound n :
 Rabs (delta0 n) <= 2 * Cmod coefa0 * max3pack / (1 - Cmod alpha ^9).
Proof.
 rewrite delta0_decomp_eqn'.
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
 rewrite <- !RtoC_pow, <- RtoC_minus.
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

Lemma delta0_lt_1 n : Rabs (delta0 n) < 1.
Proof.
 eapply Rle_lt_trans. apply delta0_better_bound.
 assert (A9 := alphamod9_lt).
 apply -> Rcomplements.Rdiv_lt_1; try lra.
 apply Rlt_pow2_inv; try lra.
 clear A9.
 rewrite !Rpow_mult_distr.
 rewrite max3pack_eqn.
 replace (Cmod alpha^9) with (((Cmod alpha)^2)^4*Cmod alpha) by ring.
 rewrite alphamod2, tau4.
 unfold coefa0, coefa2, Cdiv.
 rewrite !Cmod_mult, !Rpow_mult_distr, Cmod_inv.
 2:{ apply Cminus_eq_contra. apply distinct_roots. }
 rewrite coefa2_inner_mod.
 rewrite im_alt', !Cmod_mult.
 rewrite !Cmod_R, Rabs_right by lra.
 rewrite Cmod_Ci, Rmult_1_r.
 simpl Im.
 rewrite <- Rinv_pow, Rpow_mult_distr.
 2:{ apply Rmult_integral_contrapositive. split; try lra.
     apply Rabs_no_R0, im_alpha_nz. }
 rewrite pow2_abs. rewrite !Rmult_assoc, (Rmult_comm (/ _)), <-!Rmult_assoc.
 apply Rcomplements.Rlt_div_l.
 { rewrite im_alpha_2. field_simplify.
   generalize tau_approx, tau2_approx; lra. }
 rewrite <- Rmult_assoc, (Rmult_comm _ (2^2)), !Rmult_assoc.
 apply Rmult_lt_compat_l; try lra.
 rewrite im_alpha_2.
 change alphabar with (Cconj alpha). rewrite Cmod_conj, alphamod2.
 unfold Rdiv.
 rewrite (Rmult_assoc tau (3+tau)), <- (Rmult_assoc (_^2)).
 rewrite (Rmult_comm (_^2) tau).
 rewrite !Rmult_assoc.
 apply Rmult_lt_compat_l; [generalize tau_approx; lra|].
 field_simplify.
 rewrite !alphamod2, tau5, tau4, tau3; field_simplify.
 rewrite tau3. field_simplify.
 replace (_/4) with
  (Cmod alpha * (tau^2 - 2*tau + 1/2) + (7*tau^2-8*tau+6)/4) by field.
 apply Rcomplements.Rlt_minus_l.
 apply Ropp_lt_cancel.
 rewrite Ropp_mult_distr_r.
 apply Rlt_pow2_inv; [generalize tau_approx, tau2_approx; lra| ].
 rewrite Rpow_mult_distr, alphamod2.
 apply Rminus_gt_0_lt.
 field_simplify.
 rewrite tau5, tau4, tau3. field_simplify.
 generalize tau_approx tau2_approx; lra.
Qed.

(* Print Assumptions delta0_lt_1. *)

(* Consequences for h : *)

Lemma h_alt n : INR (h n) = tau*n + delta0 n.
Proof.
 rewrite delta0_alt; lra.
Qed.

Lemma h_natpart_or (n:nat) :
 h n = nat_part (tau*n) \/ h n = S (nat_part (tau*n)).
Proof.
assert (-1 < tau*n - h n < 1).
{ rewrite h_alt.
  assert (H := delta0_lt_1 n).
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

(* NB: both side are reached, e.g. left for n=0 and right for n=1.
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
        assert (Dp := delta0_lt_1 p).
        assert (Dn := delta0_lt_1 n).
        assert (Dpn := delta0_lt_1 (p+n)).
        rewrite Rcomplements.Rabs_lt_between in *.
        simpl. lra.
      * rewrite !S_INR, !plus_INR. rewrite !h_alt, plus_INR.
        assert (Dp := delta0_lt_1 p).
        assert (Dn := delta0_lt_1 n).
        assert (Dpn := delta0_lt_1 (p+n)).
        rewrite Rcomplements.Rabs_lt_between in *.
        simpl. lra.
Qed.

(* Print Assumptions h_quasiadd. *)

End K_2.

(* TODO: next cases and general case

For k=3, an extra negative real root. The complex roots can be expressed
 in function of the real roots. Similar convergence and results than for k=2,
 except that (f 3 n) could be further apart from (nat_part (tau 3 * n)).

For k=4, four complex roots : j and (Cconj j) of modulus 1, and
  some alpha and (Cconj alpha) of modulus < 1. Note that alpha can be
  expressed in function of (tau 4). Apparently, no more finite bound to
  (f 4 n - tau 4 * n).

Afterwards, always some complex root of modulus > 1 (but < mu k).
And (f k n - tau k * n) seems to diverge.

To prove in general :

  A k n / mu^n ---> Cst for some Cst<>0 (Cf. Saari, non-negative matrices, etc)

  A k (S n) / A k n ---> mu k  (easy consequence of the previous)

  f k n / n ---> tau k    (Cf. Saari, one of the last theorem, simplifiable)

*)
