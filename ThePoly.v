From Coq Require Import Lia Reals Lra Permutation.
From Coquelicot Require Complex.
From QuantumLib Require Import Complex Matrix Eigenvectors VecSet Polynomial.
Require Import MoreList MoreReals MoreLim MoreComplex MorePoly MoreMatrix.
Require Import GenFib Mu.
Local Open Scope C.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

Definition ThePoly (k:nat) : Polynomial :=
 monom C1 (k+1) +, monom (-C1) k +, [-C1].

Lemma ThePoly_root_carac r k : Root r (ThePoly k) <-> r^(S k) = r^k + 1.
Proof.
 unfold ThePoly, Root. rewrite !Pplus_eval, !monom_eval.
 symmetry. rewrite Ceq_minus.
 rewrite Nat.add_1_r, Cmult_1_l. cbn.
 rewrite <- !Copp_mult_distr_l, !Cmult_1_l, Cplus_0_l.
 unfold Cminus. now rewrite Copp_plus_distr, Cplus_assoc.
Qed.

Lemma mu_is_root k : Root (mu k) (ThePoly k).
Proof.
 rewrite ThePoly_root_carac.
 now rewrite !RtoC_pow, mu_carac, !RtoC_plus.
Qed.

Lemma ThePoly_subdeg k : (degree (monom (-C1) k +, [-C1]) <= k)%nat.
Proof.
 etransitivity; [apply Pplus_degree1| ].
 rewrite monom_degree. 2:apply Copp_neq_0_compat, C1_neq_C0.
 generalize (degree_length [-C1]). simpl. lia.
Qed.

Lemma ThePoly_deg k : degree (ThePoly k) = S k.
Proof.
 unfold ThePoly.
 rewrite Pplus_assoc, Pplus_comm.
 rewrite Pplus_degree2.
 rewrite monom_degree. lia. apply C1_neq_C0.
 rewrite monom_degree. 2:apply C1_neq_C0.
 generalize (ThePoly_subdeg k). lia.
Qed.

Lemma ThePoly_monic (k:nat) : monic (ThePoly k).
Proof.
 unfold ThePoly. rewrite Pplus_assoc, Pplus_comm. unfold monic.
 rewrite topcoef_plus_ltdeg. apply topcoef_monom.
 rewrite monom_degree. 2:apply C1_neq_C0.
 generalize (ThePoly_subdeg k). lia.
Qed.

Lemma ThePoly_diff k : k<>O ->
 Pdiff (ThePoly k) ≅ [-k; k+1] *, monom C1 (k-1).
Proof.
 intros Hk.
 unfold ThePoly.
 rewrite !Pdiff_plus, !diff_monom.
 replace (pred (k+1)) with (S (k-1)) by lia.
 replace (pred k) with (k-1)%nat by lia.
 simpl Pdiff. rewrite Pzero_alt, Pplus_0_r.
 rewrite monom_S.
 rewrite (monom_scale (-C1)), <- Pmult_assoc.
 replace ([RtoC k] *, [-C1]) with [-RtoC k].
 2: simpl; f_equal; lca.
 rewrite <- Pmult_X. rewrite <- Pmult_assoc.
 rewrite (Pmult_comm _ _X_), Pmult_X.
 rewrite <- Pmult_plus_distr_r. simpl Pplus.
 apply Peq_iff. f_equal. f_equal. f_equal. lca.
 f_equal. rewrite plus_INR, RtoC_plus. lca.
Qed.

Lemma ThePoly_diff_0 : Pdiff (ThePoly 0) ≅ [C1].
Proof.
 unfold ThePoly. simpl. apply Peq_iff.
 rewrite Cplus_0_r. apply (app_C0_compactify_reduce_1 [C1]).
Qed.

Lemma ThePoly_no_common_root_with_diff k c :
  Root c (ThePoly k) -> ~ Root c (Pdiff (ThePoly k)).
Proof.
 intros Hc.
 destruct (Nat.eq_dec k 0) as [->|Hk].
 - rewrite ThePoly_diff_0. unfold Root. cbn. rewrite Cmult_1_l, Cplus_0_l.
   apply C1_neq_C0.
 - rewrite ThePoly_diff by trivial.
   unfold Root.
   rewrite Pmult_eval, monom_eval. cbn.
   rewrite !Cmult_1_r, Cmult_1_l, Cplus_0_l. intro E.
   apply Cmult_integral in E. destruct E as [E|E].
   + rewrite Cplus_comm in E. apply Ceq_minus in E.
     assert (Hc' : c = (INR k / INR (S k))%C).
     { rewrite <- E. rewrite <- RtoC_plus, <- S_INR. field.
       intros H'. apply RtoC_inj in H'. generalize (RSpos k). lra. }
     rewrite <- RtoC_div in Hc'. 2:generalize (RSpos k); lra.
     revert Hc.
     rewrite ThePoly_root_carac, Ceq_minus. unfold Cminus.
     rewrite Copp_plus_distr, Cplus_assoc.
     change (c^S k - c^k - 1 <> 0)%C.
     replace (c^S k - c^k - 1)%C with (c^S k - (c^k + 1))%C by ring.
     apply Cminus_eq_contra. intro Hc.
     set (r := Rdiv _ _) in *.
     assert (r <= 1).
     { unfold r. apply Rcomplements.Rle_div_l.
       generalize (RSpos k); lra. rewrite S_INR; lra. }
     subst c. rewrite !RtoC_pow, <- RtoC_plus in Hc.
     apply RtoC_inj in Hc.
     apply mu_unique in Hc. generalize (mu_itvl k); lra.
     apply Rcomplements.Rdiv_le_0_compat. apply pos_INR. apply RSpos.
   + revert E.
     apply Cpow_nz.
     contradict Hc. subst c.
     rewrite ThePoly_root_carac.
     destruct k; try lia. simpl.
     rewrite !Cmult_0_l, !Cplus_0_l. auto using C1_neq_C0.
Qed.

Lemma ThePoly_separated_roots k :
  exists l, length l = S k /\ NoDup l /\ ThePoly k ≅ linfactors l.
Proof.
 destruct (separated_roots (ThePoly k)) as (l & D & E).
 - apply ThePoly_monic.
 - apply ThePoly_no_common_root_with_diff.
 - exists l; repeat split; auto.
   rewrite <- linfactors_degree. now rewrite <- E, ThePoly_deg.
Qed.

Lemma ThePoly_separated_roots_mu k :
  exists (l : list C),
   length l = S k /\ NoDup l /\ ThePoly k ≅ linfactors l /\ nth O l C0 = mu k.
Proof.
 destruct (ThePoly_separated_roots k) as (l & L & D & E).
 assert (IN : In (RtoC (mu k)) l).
 { rewrite linfactors_roots. rewrite <- E. apply mu_is_root. }
 apply in_split in IN. destruct IN as (l1 & l2 & E').
 set (l' := RtoC (mu k) :: l1 ++ l2).
 assert (P : Permutation l' l).
 { rewrite E'. apply Permutation_middle. }
 exists l'; repeat split.
 - apply Permutation_length in P. lia.
 - apply Permutation_sym, Permutation_NoDup in P; trivial.
 - apply linfactors_perm in P. now rewrite P.
Qed.

Lemma roots_le_mu k (r:C) :
 Root r (ThePoly k) -> (Cmod r <= mu k)%R.
Proof.
 rewrite ThePoly_root_carac. intros E.
 apply Rnot_lt_le. intros L.
 assert (Iv := mu_itvl k).
 assert (H : mu k -1 < Cmod (r-1)).
 { apply Rlt_le_trans with (Cmod r -1)%R; try lra.
   apply Rle_minus_l.
   replace r with ((r-C1)+C1) at 1 by lca.
   eapply Rle_trans; [apply Cmod_triangle|]. rewrite Cmod_1. lra. }
 assert (H' : (mu k)^k <= Cmod (r^k)).
 { rewrite Cmod_pow. apply pow_incr; lra. }
 assert (LT : (mu k)^k*(mu k -1) < Cmod (r^k*(r-1))).
 { rewrite Cmod_mult. apply Rle_lt_mult_compat; split; try lra.
   apply pow_lt; lra. }
 revert LT. apply Rle_not_lt.
 unfold Rminus, Cminus. rewrite Rmult_plus_distr_l, Cmult_plus_distr_l.
 rewrite Rmult_comm, Cmult_comm. simpl in E. rewrite E.
 assert (E' := mu_carac k). simpl in E'. rewrite E'. ring_simplify.
 replace (_ + _)%C with C1 by ring. rewrite Cmod_1; lra.
Qed.

Lemma other_roots_lt_mu k (r:C) :
 Root r (ThePoly k) -> r <> mu k -> (Cmod r < mu k)%R.
Proof.
 intros R N.
 assert (LE := roots_le_mu k r R).
 apply Rle_lt_or_eq_dec in LE. destruct LE as [LT|E]; trivial.
 destruct N.
 apply ThePoly_root_carac in R.
 assert (E' : (Cmod (r^k * (r - 1)) = mu k^k * (mu k -1))%R).
 { unfold Rminus, Cminus. rewrite Rmult_plus_distr_l, Cmult_plus_distr_l.
   rewrite Rmult_comm, Cmult_comm. simpl in R. rewrite R.
   replace (_ + _)%C with C1 by ring. rewrite Cmod_1.
   generalize (mu_carac k); simpl. intros ->. ring. }
 rewrite Cmod_mult, Cmod_pow, E in E'.
 apply Rmult_eq_reg_l in E'.
 2:{ apply pow_nonzero. generalize (mu_itvl k); lra. }
 rewrite <- E in E'.
 apply Cmod_triangle_exact in E'. congruence.
Qed.

Lemma G_big_mult_0 (l : list C) : G_big_mult l = 0 -> In C0 l.
Proof.
 induction l; simpl. apply C1_neq_C0.
 intros E. apply Cmult_integral in E; intuition.
Qed.

Lemma multdiffs_nodup (l : list C) : NoDup l -> multdiffs l <> 0.
Proof.
 induction 1; simpl.
 - apply C1_neq_C0.
 - intros E. apply Cmult_integral in E. destruct E as [E|E]; try easy.
   apply G_big_mult_0 in E. rewrite in_map_iff in E.
   destruct E as (y & E & IN). apply H. apply Ceq_minus in E. now subst.
Qed.

Definition pows (l:list C) n := map (fun c => c^n) l.

Lemma nth_pows i l p : (i < length l)%nat ->
 nth i (pows l p) 0 = nth i l 0 ^p.
Proof.
 intros H.
 rewrite <- map_nth with (f := fun c => c ^ p).
 apply nth_indep. unfold pows; rewrite map_length; lia.
Qed.

Lemma get_row_mult n m p (A : Matrix n m) (B : Matrix m p) k :
 Mmult (get_row k A) B == get_row k (Mmult A B).
Proof.
 intros i j Hi Hj. unfold get_row, Mmult. case Nat.eqb_spec; auto; lia.
Qed.

Lemma get_row_mult_eq n m p (A : Matrix n m) (B : Matrix m p) k :
 WF_Matrix A -> WF_Matrix B ->
 Mmult (get_row k A) B = get_row k (Mmult A B).
Proof.
 intros. apply mat_equiv_eq; auto using WF_get_row, WF_mult.
 apply get_row_mult.
Qed.

Lemma Re_Σ f n : Re (Σ f n) = big_sum (fun i => Re (f i)) n.
Proof.
 induction n; cbn; trivial. now f_equal.
Qed.

Lemma is_lim_seq_Σ_0 (f:nat -> nat -> R) n :
 (forall i, (i<n)%nat -> is_lim_seq (fun k => f k i) R0) ->
 is_lim_seq (fun k => big_sum (f k) n) R0.
Proof.
 intros H. induction n; simpl.
 - apply is_lim_seq_const.
 - replace R0 with (0+0)%R by lra. apply is_lim_seq_plus'; auto.
Qed.

Section Roots.
Variable k : nat.
Variable allroots : list C.
Hypothesis allroots_len : length allroots = S k.
Hypothesis allroots_nodup : NoDup allroots.
Hypothesis allroots_ok : ThePoly k ≅ linfactors allroots.
Hypothesis allroots_mu : nth O allroots C0 = mu k.

Let vdmroot := Vandermonde (S k) allroots.

Lemma VdmRoots_det_nz : Determinant vdmroot <> 0.
Proof.
 unfold vdmroot.
 rewrite Vandermonde_det by trivial.
 now apply multdiffs_nodup.
Qed.

(** Conjecture (TODO?) : the square of this determinant seems to be
    [+/- ((k+1)^(k+1)+k^k)].
    For instance +5 for k=1, -31 for k=2, -283 for k=3, +3381 for k=4
    See OEIS A056788.
    At least, this square is clearly an integer, since it's a symmetric
    polynomial of the roots (determinant is alternating) with coefficients
    in Z, hence it is a Z polynomial of the elementary symmetric polynomials
    that here are -1 or 0 or 1 (coefficients of ThePoly). *)

Lemma VdmRoots_invertible : invertible vdmroot.
Proof.
 apply lin_indep_invertible. apply WF_Vandermonde.
 apply lin_indep_det_neq_0. apply WF_Vandermonde.
 red. split; auto. apply VdmRoots_det_nz.
Qed.

Lemma coefs_LinComb :
 exists coefs : Vector (S k),
  forall p, (p <= k)%nat ->
    scalprod coefs (mkvect _ (pows allroots p)) = S p.
Proof.
 destruct VdmRoots_invertible as (Vinv & E & _).
 set (vect_1_Sk := mkvect (S k) (map (compose RtoC INR) (seq 1 (S k)))).
 assert (WF_Matrix vect_1_Sk).
 { apply WF_mkvect. now rewrite map_length, seq_length. }
 set (coefs := Mmult Vinv vect_1_Sk).
 exists (make_WF coefs). intros p Hp.
 replace (mkvect _ (pows allroots p)) with (transpose (get_row p vdmroot)).
 2:{ apply mat_equiv_eq.
     - apply WF_transpose, WF_get_row, WF_Vandermonde.
     - apply WF_mkvect. unfold pows. rewrite map_length; lia.
     - intros i j Hi Hj. replace j with O by lia; clear j Hj.
       rewrite mkvect_eqn, nth_pows by lia.
       unfold get_row, vdmroot, Vandermonde. cbn.
       do 2 case Nat.leb_spec; auto; lia. }
 unfold scalprod. rewrite <- Mmult_transpose.
 rewrite get_row_mult_eq. 2:apply WF_Vandermonde. 2:apply WF_make_WF.
 rewrite (eq_make_WF vdmroot). 2:apply WF_Vandermonde.
 rewrite Mmult_make_WF. unfold coefs.
 rewrite <- Mmult_assoc, E, Mmult_1_l; auto.
 rewrite <- eq_make_WF; auto.
 unfold get_row, transpose. cbn -[RtoC INR seq].
 unfold vect_1_Sk, mkvect, list2D_to_matrix.
 rewrite map_map.
 rewrite nth_map_indep with (d':=O) by (rewrite seq_length; lia).
 now rewrite seq_nth by lia.
Qed.

Lemma coefs_LinCombA :
 exists coefs : Vector (S k),
  forall n, scalprod coefs (mkvect _ (pows allroots n)) = A k n.
Proof.
 destruct coefs_LinComb as (coefs & Init). exists coefs.
 induction n as [n IH] using lt_wf_ind.
 destruct (Nat.leb_spec n k).
 - rewrite A_base by lia. now apply Init.
 - destruct n; try lia. simpl A.
   rewrite plus_INR, RtoC_plus, <- !IH by lia.
   replace (mkvect _ (pows allroots (S n))) with
       (mkvect (S k) (pows allroots n) .+ mkvect _ (pows allroots (n-k))).
   + unfold scalprod. now rewrite Mmult_plus_distr_l.
   + apply mat_equiv_eq.
     * apply WF_plus; apply WF_mkvect; unfold pows; rewrite map_length; lia.
     * apply WF_mkvect; unfold pows; rewrite map_length; lia.
     * intros i j Hi Hj. replace j with O by lia.
       unfold Mplus. rewrite !mkvect_eqn, !nth_pows by lia.
       set (r := nth i allroots C0).
       assert (R : Root r (ThePoly k)).
       { rewrite allroots_ok, <- linfactors_roots. apply nth_In; lia. }
       rewrite ThePoly_root_carac in R.
       replace n with (k + (n-k))%nat at 1 3 by lia.
       rewrite <- Nat.add_succ_l, !Cpow_add_r, R. lca.
Qed.

Lemma A_div_pow_mu_limit_aux :
 exists (lim:R), is_lim_seq (fun n => A k n / mu k ^n)%R lim.
Proof.
 destruct coefs_LinCombA as (coefs & E).
 exists (Re (coefs O O)). (* actually (coefs O O) is a real *)
 assert (allroots_mu' : nth 0 allroots C0 = mu k).
 { destruct allroots; simpl in *; auto; try lia. }
 assert (Iv := mu_itvl k).
 assert (mu k <> 0)%R by lra.
 set (rest :=
      (fun n i => Re (coefs (S i) O * (nth (S i) allroots 0)^n) / mu k^n)%R).
 apply is_lim_seq_ext with
   (u := (fun n => Re (coefs O O) + big_sum (rest n) k)%R).
 - intros n.
   rewrite <- (re_RtoC (A k n)). rewrite <- E. clear E.
   rewrite scalprod_alt, <- big_sum_extend_l;
   rewrite mkvect_eqn, nth_pows, allroots_mu' by lia.
   rewrite RtoC_pow, re_plus, re_scal_r, Re_Σ.
   rewrite Rdiv_plus_distr. f_equal; [field; now apply pow_nonzero|].
   unfold Rdiv. rewrite (@big_sum_mult_r _ _ _ _ R_is_ring).
   apply bigsum_ext. intros i Hi. cbn -[Re].
   unfold rest. unfold Rdiv. f_equal. f_equal. f_equal.
   now rewrite mkvect_eqn, nth_pows by lia.
 - clear E. rewrite <- (Rplus_0_r (Re _)) at 1.
   apply is_lim_seq_plus'; [apply is_lim_seq_const|].
   apply is_lim_seq_Σ_0. intros i Hi.
   apply is_lim_seq_0_abs with
     (fun n => Cmod (coefs (S i) O) * (Cmod (nth (S i) allroots 0) / mu k)^n)%R.
   + intros n. unfold rest. clear rest. set (r := nth _ _ _).
     unfold Rdiv. rewrite <- re_scal_r.
     eapply Rle_trans; [apply re_le_Cmod|].
     rewrite <- Cmult_assoc, Cmod_mult.
     apply Rmult_le_compat_l. apply Cmod_ge_0.
     rewrite Cmod_mult.
     rewrite Rpow_mult_distr.
     rewrite <- Cmod_pow.
     apply Rmult_le_compat_l. apply Cmod_ge_0.
     rewrite Cmod_R. rewrite Rabs_right. rewrite pow_inv; lra.
     left. apply Rinv_0_lt_compat. apply pow_lt; lra.
   + clear rest.
     set (c := Cmod _).
     set (r := nth _ _ _).
     replace 0%R with (c * 0)%R at 1 by lra.
     apply is_lim_seq_mult'; [apply is_lim_seq_const|].
     apply is_lim_seq_geom.
     rewrite Rabs_right.
     2:{ apply Rle_ge, Rcomplements.Rdiv_le_0_compat. apply Cmod_ge_0. lra. }
     apply -> Rcomplements.Rdiv_lt_1; try lra.
     apply other_roots_lt_mu.
     rewrite allroots_ok, <- linfactors_roots. apply nth_In; lia.
     destruct allroots as [|m l]; simpl in *; try lia.
     inversion allroots_nodup; subst.
     assert (In r l) by (unfold r; apply nth_In; lia).
     intros ->; intuition.
Qed.

End Roots.

Lemma A_div_pow_mu_limit k :
 exists (lim:R), is_lim_seq (fun n => A k n / mu k ^n)%R lim.
Proof.
 destruct (ThePoly_separated_roots_mu k) as (l & l_len & l_dp & l_ok & l_mu).
 apply A_div_pow_mu_limit_aux with l; auto.
Qed.

(* Print Assumptions A_div_pow_mu_limit. *)
