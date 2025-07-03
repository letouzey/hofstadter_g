From Coq Require Import Lia Reals Lra.
From Coquelicot Require Complex.
From Coquelicot Require Export Lim_seq.
From Coquelicot Require Import Rcomplements Hierarchy Continuity Series PSeries.
From Coquelicot Require Import ElemFct Derive.
Close Scope R. (* Issue with Coquelicot *)
From Hofstadter.HalfQuantum Require Import Complex Polynomial.
Require Import MoreTac MoreList MoreReals MoreComplex MoreSum MorePoly.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

Notation R_NM := R_NormedModule.
Notation R_CNM := R_CompleteNormedModule.
Notation C_NM := Coquelicot.Complex.C_R_NormedModule.
Notation C_CNM := Coquelicot.Complex.C_R_CompleteNormedModule.

(** Complements to Coquelicot.Lim_seq *)

Lemma is_lim_seq_opp' u (l:R) :
 is_lim_seq u l -> is_lim_seq (fun n => -u n) (-l).
Proof.
 intros H. now apply is_lim_seq_opp in H.
Qed.

Lemma is_lim_seq_0_abs u v :
 Hierarchy.eventually (fun n => Rabs (u n) <= v n) ->
 is_lim_seq v 0 -> is_lim_seq u 0.
Proof.
 intros H Hv.
 apply is_lim_seq_le_le_loc with (u := fun n => -v n) (w := v); trivial.
 - destruct H as (N,H). exists N. intros n Hn. apply Rabs_le_between, H, Hn.
 - replace 0 with (-0) by lra. now apply is_lim_seq_opp'.
Qed.

Lemma is_lim_seq_bound u K :
 (forall n, Rabs (u n) <= K) -> is_lim_seq (fun n => u n / n) 0.
Proof.
 intros H.
 apply is_lim_seq_0_abs with (fun n => K / n).
 - exists 1%nat. intros n Hn. specialize (H n). unfold Rdiv.
   rewrite Rabs_mult, Rabs_inv.
   rewrite (Rabs_right n). 2:{ apply Rle_ge, pos_INR. }
   apply Rmult_le_compat_r; trivial.
   apply Rlt_le, Rinv_0_lt_compat, lt_0_INR; lia.
 - apply (is_lim_seq_div _ _ K Rbar.p_infty); try easy.
   + apply is_lim_seq_const.
   + apply is_lim_seq_INR.
   + red. red. simpl. now rewrite Rmult_0_r.
Qed.

Lemma is_lim_seq_invn : is_lim_seq (fun n => /n) 0.
Proof.
 apply is_lim_seq_ext with (fun n => 1/n).
 - intros n. unfold Rdiv. apply Rmult_1_l.
 - apply is_lim_seq_bound with (K:=1). intros. rewrite Rabs_pos_eq; lra.
Qed.

Lemma is_lim_seq_ndivSn :
 is_lim_seq (fun n => n / S n) 1.
Proof.
 replace 1 with (1-0) by lra.
 apply is_lim_seq_ext with (fun n => 1-/(S n)).
 - intros n. rewrite S_INR. field. rewrite <- S_INR.
   generalize (lt_0_INR (S n) lia). lra.
 - apply is_lim_seq_minus'; try apply is_lim_seq_const.
   assert (H := is_lim_seq_invn).
   now apply is_lim_seq_incr_1 in H.
Qed.

Lemma is_lim_seq_sqrt : is_lim_seq (fun n : nat => sqrt n) Rbar.p_infty.
Proof.
 apply (is_lim_comp_seq sqrt INR Rbar.p_infty);
 auto using is_lim_sqrt_p, is_lim_id, is_lim_seq_INR. now exists O.
Qed.

Lemma is_lim_seq_big_sum_0 (f:nat -> nat -> R) n :
 (forall i, (i<n)%nat -> is_lim_seq (fun q => f q i) R0) ->
 is_lim_seq (fun q => big_sum (f q) n) R0.
Proof.
 intros H. induction n; simpl.
 - apply is_lim_seq_const.
 - replace R0 with (0+0)%R by lra. apply is_lim_seq_plus'; auto.
Qed.

(** Results about limits of exp and logarithm *)

Lemma exp_taylor2 : is_lim (fun x => (exp x - 1 - x) / x^2) 0 (1/2).
Proof.
 set (a := fun n => /fact n).
 assert (Ha : forall y, ex_pseries (V:=R_NM) a y).
 { intros y. exists (exp y). apply is_exp_Reals. }
 apply is_lim_ext_loc with (PSeries (PS_decr_1 (PS_decr_1 (V:=R_NM) a))).
 - exists posreal_one. intros y _ Hy'.
   rewrite exp_Reals. fold a.
   rewrite (PSeries_decr_1 a), (PSeries_decr_1 (PS_decr_1 (V:=R_NM) a));
    trivial.
   2:{ apply ex_pseries_decr_1; trivial.
       right. exists (/y). now apply Rinv_l. }
   change (a O) with (/1).
   change (PS_decr_1 (V:=R_NM) a 0) with (/1).
   rewrite Rinv_1. now field.
 - replace (1/2) with ((PS_decr_1 (PS_decr_1 (V:=R_NM) a)) O).
   2:{ unfold a, PS_decr_1. simpl. lra. }
   rewrite <- PSeries_0.
   apply is_lim_continuity, PSeries_continuity.
   rewrite !CV_radius_decr_1.
   replace (CV_radius a) with (Rbar.p_infty); try easy.
   { symmetry. apply CV_radius_infinite_DAlembert.
     - apply exp_cof_no_R0.
     - eapply is_lim_seq_ext.
       { intros n. symmetry. unfold a. unfold Rdiv. now rewrite simpl_fact. }
       rewrite <- is_lim_seq_abs_0.
       rewrite <- (is_lim_seq_incr_1 Rinv).
       apply is_lim_seq_invn. }
Qed.

Lemma exp_above_square_ineg x : 0<x -> x/6 <= exp x / x^2.
Proof.
 intros Hx.
 replace (x/6) with (x^3/6/x^2) by (field; lra).
 apply Rmult_le_compat_r. apply Rlt_le, Rinv_0_lt_compat; nra.
 eapply Rle_trans; [|apply (exp_ge_taylor x 3); lra]. simpl. nra.
Qed.

Lemma exp_above_square :
  is_lim (fun x => exp x / x^2) Rbar.p_infty Rbar.p_infty.
Proof.
 apply is_lim_le_p_loc with (fun x => x/6).
 - exists 0. apply exp_above_square_ineg.
 - replace Rbar.p_infty with (Rbar.Rbar_div Rbar.p_infty 6) at 2.
   2:{ simpl. destruct Rle_dec; try lra.
       destruct Rle_lt_or_eq_dec; trivial; lra. }
   apply is_lim_div. apply is_lim_id. apply is_lim_const.
   intros [=E]; lra. simpl; intros [=E]; lra.
Qed.

Lemma ln2_below_id :
  is_lim (fun x => (ln x)^2 / x) Rbar.p_infty 0.
Proof.
 apply (is_lim_le_le_loc (fun _ => 0) (fun x => 6 / ln x)).
 - exists 1. intros x Hx. split.
   + apply Rdiv_le_0_compat; try lra.
     rewrite <- Rsqr_pow2. apply Rle_0_sqr.
   + assert (Hx' : 0 < ln x).
     { rewrite <- ln_1. apply ln_increasing; lra. }
     assert (LE := exp_above_square_ineg (ln x) Hx').
     rewrite exp_ln in LE by lra.
     rewrite <- Rinv_div, <- (Rinv_div _ 6).
     apply Rinv_le_contravar; lra.
 - apply is_lim_const.
 - replace (Rbar.Finite 0) with (Rbar.Rbar_div 6 Rbar.p_infty).
   2:{ simpl. f_equal. lra. }
   apply is_lim_div; try easy. apply is_lim_const. apply is_lim_ln_p.
Qed.

Lemma lim_ln : is_lim_seq (fun n => ln n) Rbar.p_infty.
Proof.
 apply (is_lim_comp_seq ln INR Rbar.p_infty);
 trivial using is_lim_ln_p, is_lim_seq_INR. now exists O.
Qed.

Lemma lim_ln_div_n : is_lim_seq (fun n => ln n / n) 0.
Proof.
 apply (is_lim_comp_seq (fun x => ln x/x) INR Rbar.p_infty);
 trivial using is_lim_seq_INR, is_lim_div_ln_p. now exists O.
Qed.

Lemma lim_lnln_div_n : is_lim_seq (fun n => ln (ln n) / n) 0.
Proof.
 apply is_lim_seq_le_le_loc with (fun _ => 0) (fun n => ln n/n);
 trivial using is_lim_seq_const, lim_ln_div_n.
 exists 3%nat. intros n Hn. apply le_INR in Hn.
 replace (INR 3) with 3 in Hn by (simpl; lra).
 split.
 - apply Rdiv_le_0_compat; try lra.
   rewrite <- ln_1. apply ln_le; try lra.
   rewrite <- (ln_exp 1). apply ln_le. apply exp_pos.
   generalize exp_1_itvl; lra.
 - apply Rmult_le_compat_r. apply Rlt_le, Rinv_0_lt_compat. lra.
   apply ln_le. rewrite <- ln_1. apply ln_increasing; lra.
   rewrite <- (ln_exp n) at 2. apply ln_le; try lra.
   generalize (exp_ineq1_le n); lra.
Qed.

Lemma lim_ln2_div_n : is_lim_seq (fun n => ln n ^ 2 / n) 0.
Proof.
 apply (is_lim_comp_seq (fun x => (ln x)^2/x) INR Rbar.p_infty).
 apply ln2_below_id. now exists O. apply is_lim_seq_INR.
Qed.

Lemma lim_inv_ln : is_lim_seq (fun n => / ln n) 0.
Proof.
 change (Rbar.Finite 0) with (Rbar.Rbar_inv Rbar.p_infty).
 apply is_lim_seq_inv; try easy.
 apply (is_lim_comp_seq ln INR Rbar.p_infty);
 trivial using is_lim_seq_INR, is_lim_ln_p. now exists O.
Qed.

Lemma lim_inv_sqrt : is_lim_seq (fun n => /sqrt n) 0.
Proof.
 change (Rbar.Finite 0) with (Rbar.Rbar_inv Rbar.p_infty).
 apply is_lim_seq_inv; try easy. apply is_lim_seq_sqrt.
Qed.

Lemma continuous_alt f x : continuous f x <-> continuity_pt f x.
Proof.
 symmetry. apply continuity_pt_filterlim.
Qed.

Lemma lim_ln_div_sqrt : is_lim_seq (fun n => ln n / sqrt n) 0.
Proof.
 apply is_lim_seq_ext_loc with (fun n => sqrt (ln n ^2 / n)).
 { exists 1%nat. intros n Hn.
   rewrite sqrt_div_alt by (apply lt_0_INR; lia).
   rewrite sqrt_pow2; trivial. rewrite <- ln_1. apply ln_le; try lra.
   now apply (le_INR 1). }
 rewrite <- sqrt_0. apply is_lim_seq_continuous. apply continuous_alt.
 - apply continuous_sqrt.
 - apply lim_ln2_div_n.
Qed.

Lemma lim_lnln_div_sqrt : is_lim_seq (fun n => ln (ln n) / sqrt n) 0.
Proof.
 apply is_lim_seq_le_le_loc with (fun _ => 0) (fun n => ln n/sqrt n);
 trivial using is_lim_seq_const, lim_ln_div_sqrt.
 exists 3%nat. intros n Hn. apply le_INR in Hn.
 replace (INR 3) with 3 in Hn by (simpl; lra).
 split.
 - apply Rdiv_le_0_compat. 2:{ apply sqrt_lt_R0; lra. }
   rewrite <- ln_1. apply ln_le; try lra.
   rewrite <- (ln_exp 1). apply ln_le. apply exp_pos.
   generalize exp_1_itvl; lra.
 - apply Rmult_le_compat_r. apply Rlt_le, Rinv_0_lt_compat, sqrt_lt_R0; lra.
   apply ln_le. rewrite <- ln_1. apply ln_increasing; lra.
   rewrite <- (ln_exp n) at 2. apply ln_le; try lra.
   generalize (exp_ineq1_le n); lra.
Qed.

(** sup and limsup *)

Lemma is_sup_seq_const (c : Rbar.Rbar) : is_sup_seq (fun _ => c) c.
Proof.
 destruct c; red.
 - intros eps. split.
   + intros _; simpl. destruct eps. simpl. lra.
   + exists O. simpl. destruct eps. simpl. lra.
 - intros M; now exists O.
 - now intros M.
Qed.

Lemma is_inf_seq_const (c : Rbar.Rbar) : is_inf_seq (fun _ => c) c.
Proof.
 destruct c; red.
 - intros eps. split.
   + intros _; simpl. destruct eps. simpl. lra.
   + exists O. simpl. destruct eps. simpl. lra.
 - now intros M.
 - intros M; now exists O.
Qed.

Lemma LimSup_seq_correct (u : nat -> R) : is_LimSup_seq u (LimSup_seq u).
Proof.
 destruct (ex_LimSup_seq u) as (l, Hl).
 now rewrite (is_LimSup_seq_unique _ _ Hl).
Qed.

Lemma LimInf_seq_correct (u : nat -> R) : is_LimInf_seq u (LimInf_seq u).
Proof.
 destruct (ex_LimInf_seq u) as (l, Hl).
 now rewrite (is_LimInf_seq_unique _ _ Hl).
Qed.

Lemma Lim_LimSup (u : nat -> R) :
  ex_lim_seq u -> Lim_seq u = LimSup_seq u.
Proof.
 intros H. apply ex_lim_LimSup_LimInf_seq in H.
 unfold Lim_seq. rewrite <- H.
 destruct (LimSup_seq u); simpl; trivial. f_equal. lra.
Qed.

Lemma Lim_LimInf (u : nat -> R) :
  ex_lim_seq u -> Lim_seq u = LimInf_seq u.
Proof.
 intros H. apply ex_lim_LimSup_LimInf_seq in H.
 unfold Lim_seq. rewrite -> H.
 destruct (LimInf_seq u); simpl; trivial. f_equal. lra.
Qed.

Lemma finite_max (u:nat->R) N : exists M, forall n, (n<=N)%nat -> u n <= M.
Proof.
 induction N.
 - exists (u O). intros n Hn. inversion Hn. lra.
 - destruct IHN as (M & HM).
   exists (Rmax M (u (S N))).
   intros n Hn. inversion Hn.
   + subst; apply Rmax_r.
   + apply Rle_trans with M; [|apply Rmax_l]. now apply HM.
Qed.

(** A sequence u of values in R (not Rbar !) cannot have -infinity
    as sup. *)

Lemma sup_no_minfty (u:nat -> R) : Sup_seq u <> Rbar.m_infty.
Proof.
 intro E.
 assert (Hu := Sup_seq_correct u). rewrite E in Hu. simpl in *.
 specialize (Hu (u O) O). lra.
Qed.

Lemma inf_no_pinfty (u:nat -> R) : Inf_seq u <> Rbar.p_infty.
Proof.
 intro E.
 assert (Hu := Inf_seq_correct u). rewrite E in Hu. simpl in *.
 specialize (Hu (u O) O). lra.
Qed.

(** For a sequence u of values in R (not Rbar  !),
    having +infinity as sup is the same as having +infinity as limsup *)

Lemma Sup_LimSup_pinfty (u:nat -> R) :
 Sup_seq u = Rbar.p_infty <-> LimSup_seq u = Rbar.p_infty.
Proof.
 split.
 - intros Hu. apply is_LimSup_seq_unique.
   assert (Hu' := Sup_seq_correct u). rewrite Hu in Hu'. simpl in *.
   intros M N.
   destruct (finite_max u (N-1)) as (M' & HM').
   destruct (Hu' (Rmax M (M'+1))) as (n & Hn). exists n. split.
   + destruct (Nat.le_gt_cases N n); trivial. exfalso.
     specialize (HM' n lia). generalize (Rmax_r M (M'+1)). lra.
   + eapply Rle_lt_trans; [ apply Rmax_l | apply Hn ].
 - intros Hu. apply is_sup_seq_unique.
   assert (Hu' := LimSup_seq_correct u). rewrite Hu in Hu'. simpl in *.
   intros M. destruct (Hu' M O) as (n & _ & H). now exists n.
Qed.

Lemma finite_lim_finite_sup (u:nat -> R) :
 ex_finite_lim_seq u -> Rbar.is_finite (Sup_seq u).
Proof.
 intros (l & H).
 destruct (Sup_seq u) eqn:E; try easy.
 - exfalso.
   apply is_lim_LimSup_seq, is_LimSup_seq_unique in H.
   rewrite Sup_LimSup_pinfty in E. now rewrite E in H.
 - exfalso. now apply (sup_no_minfty u).
Qed.

Lemma finite_lim_bounded (u:nat -> R) :
  ex_finite_lim_seq u -> forall n, u n <= Rbar.real (Sup_seq u).
Proof.
 intros H. apply finite_lim_finite_sup in H.
 destruct (Sup_seq u) eqn:E; try easy. intros n. simpl.
 change (Rbar.Rbar_le ((fun n => Rbar.Finite (u n)) n) r).
 apply is_sup_seq_major. rewrite <- E. apply Sup_seq_correct.
Qed.

Lemma is_inf_seq_minor (u : nat -> Rbar.Rbar) (l : Rbar.Rbar) :
  is_inf_seq u l -> forall n, Rbar.Rbar_le l (u n).
Proof.
 intros Hu n.
 rewrite <- is_sup_opp_inf_seq in Hu.
 apply is_sup_seq_major with (n:=n) in Hu.
 now apply Rbar.Rbar_opp_le.
Qed.

Lemma Inf_seq_major_le (u : nat -> Rbar.Rbar) (M : R) (n : nat) :
  Rbar.Rbar_le (u n) M -> Rbar.Rbar_le (Inf_seq u) M.
Proof.
 intros. apply Rbar.Rbar_le_trans with (u n); trivial.
 apply is_inf_seq_minor. apply Inf_seq_correct.
Qed.

Lemma LimSup_le_Sup (u:nat->R) : Rbar.Rbar_le (LimSup_seq u) (Sup_seq u).
Proof.
 destruct (Sup_seq u) as [r | | ] eqn:E.
 - rewrite LimSup_InfSup_seq.
   eapply Inf_seq_major_le with (n:=O).
   rewrite Sup_seq_ext with (v:=u). 2:{ intros n. do 2 f_equal. lia. }
   rewrite E. apply Rbar.Rbar_le_refl.
 - now destruct (LimSup_seq u).
 - now destruct (sup_no_minfty u).
Qed.

Lemma Inf_le_LimInf (u:nat->R) : Rbar.Rbar_le (Inf_seq u) (LimInf_seq u).
Proof.
 destruct (Inf_seq u) as [r | | ] eqn:E; try constructor.
 - rewrite LimInf_SupInf_seq.
   eapply Sup_seq_minor_le with (n:=O).
   rewrite Inf_seq_ext with (v:=u). 2:{ intros n. do 2 f_equal. lia. }
   rewrite E. apply Rbar.Rbar_le_refl.
 - now destruct (inf_no_pinfty u).
Qed.

Lemma Fekete_core (u:nat->R) :
 (forall n m, u (n+m)%nat <= u n + u m) ->
 forall q, q<>O -> Rbar.Rbar_le (LimSup_seq (fun n => u n / n)) (u q / q).
Proof.
 intros U q Q.
 assert (U' : forall a b c, u (a*b+c)%nat <= a * u b + u c).
 { induction a; intros.
   - simpl. lra.
   - replace (S a * b + c)%nat with (b + (a*b+c))%nat by lia.
     eapply Rle_trans. apply U.
     rewrite S_INR, (Rplus_comm a 1), Rmult_plus_distr_r, Rmult_1_l.
     rewrite Rplus_assoc. apply Rplus_le_compat_l. apply IHa. }
 destruct (finite_max u (q-1)) as (M & HM).
 replace (Rbar.Finite (u q/q)) with
     (LimSup_seq (fun n => (n- n mod q)/n * (u q / q) + M / n)).
 { apply LimSup_le. exists 1%nat. intros n Hn.
   assert (Hn' : 0 < /n).
   { apply Rinv_0_lt_compat. destruct n; try lia. apply RSpos. }
   rewrite (Nat.div_mod_eq n q) at 1. rewrite (Nat.mul_comm q).
   eapply Rle_trans;
     [eapply Rmult_le_compat_r;[now apply Rlt_le|apply U']| ].
   rewrite Rmult_plus_distr_r. apply Rplus_le_compat.
   - apply Req_le.
     rewrite <- minus_INR by (apply Nat.mod_le; lia).
     replace (n-n mod q)%nat with (((n/q)*q)%nat).
     2:{ rewrite (Nat.div_mod_eq n q) at 2. lia. }
     rewrite mult_INR. field. split; apply not_0_INR; lia.
   - apply Rmult_le_compat_r;[now apply Rlt_le| ].
     apply HM. generalize (Nat.mod_upper_bound n q); lia. }
 { apply is_LimSup_seq_unique, is_lim_LimSup_seq.
   rewrite <- (Rplus_0_r (u q / q)) at 1.
   apply is_lim_seq_plus'.
   2:{ apply is_lim_seq_bound with (Rabs M); intros; lra. }
   rewrite <- (Rmult_1_l (u q / q)) at 1.
   apply is_lim_seq_mult'; try apply is_lim_seq_const.
   apply is_lim_seq_ext_loc with (u := fun n => 1 - (n mod q)/n).
   { exists 1%nat. intros n Hn. field. apply not_0_INR; lia. }
   replace 1 with (1-0) at 1 by lra.
   apply is_lim_seq_minus'; try apply is_lim_seq_const.
   apply is_lim_seq_bound with q; intros.
   rewrite Rabs_right by (apply Rle_ge; apply pos_INR).
   apply le_INR. generalize (Nat.mod_upper_bound n q); lia. }
Qed.

Lemma Fekete_subadditive_lemma (u:nat->R) :
 (forall n m, u (n+m)%nat <= u n + u m) ->
 let f := fun n => u n / n in
 is_lim_seq f (Inf_seq (fun n => f (S n))).
Proof.
 intros U f.
 assert (U' := Fekete_core u U). fold f in U'.
 assert (LE : Rbar.Rbar_le (LimSup_seq f) (Inf_seq (fun n => f (S n)))).
 { replace (LimSup_seq f) with (Inf_seq (fun n => LimSup_seq f)).
   2:{ apply is_inf_seq_unique, is_inf_seq_const. }
   apply Inf_seq_le. intros n. apply U'. lia. }
 assert (E : LimSup_seq f = LimInf_seq f).
 { apply Rbar.Rbar_le_antisym; try apply LimSup_LimInf_seq_le.
   destruct (LimSup_seq f) eqn:E.
   - replace (Rbar.Finite r) with (LimInf_seq (fun n => r)).
     2:{ apply is_LimInf_seq_unique, is_LimInf_seq_const. }
     apply LimInf_le. exists 1%nat. intros n Hn. apply U'. lia.
   - simpl in U'. now destruct (U' 1%nat).
   - simpl; trivial. }
 assert (LE' := Inf_le_LimInf (fun n => f (S n))). simpl in LE'.
 replace (LimInf_seq (fun x => f (S x))) with (LimInf_seq f) in LE'.
 2:{ symmetry. apply is_LimInf_seq_unique.
     rewrite <- is_LimInf_seq_ind_1. apply LimInf_seq_correct. }
 assert (X : ex_lim_seq f).
 { apply ex_lim_LimSup_LimInf_seq, E. }
 replace (Inf_seq (fun n => f (S n))) with (Lim_seq f).
 now apply Lim_seq_correct.
 apply Rbar.Rbar_le_antisym. now rewrite Lim_LimSup. now rewrite Lim_LimInf.
Qed.

Lemma Fekete_superadditive_lemma (u:nat->R) :
 (forall n m, u (n+m)%nat >= u n + u m) ->
 let f := fun n => u n / n in
 is_lim_seq f (Sup_seq (fun n => f (S n))).
Proof.
 intros U. cbn -[INR].
 rewrite is_lim_seq_opp.
 rewrite Sup_seq_ext with (v:=fun n => Rbar.Rbar_opp (- u(S n)/S n)).
 2:{ intros n. cbn -[INR]. f_equal. field. generalize (RSpos n); lra. }
 rewrite <- Inf_opp_sup.
 apply is_lim_seq_ext_loc with (u:=fun n => - u n/n).
 { exists 1%nat. intros n Hn. field. destruct n; try lia.
   generalize (RSpos n); lra. }
 apply Fekete_subadditive_lemma. intros n m. specialize (U n m). lra.
Qed.

(** More on R series *)

Lemma is_series_alt (a:nat->R) (l:R) :
 is_series a l <-> is_lim_seq (sum_n a) l.
Proof.
 reflexivity.
Qed.

Lemma ex_series_alt (a:nat->R) :
 ex_series a <-> ex_finite_lim_seq (sum_n a).
Proof.
 reflexivity.
Qed.

Lemma is_series_R0 : is_series (fun _ => 0%R) 0%R.
Proof.
 rewrite is_series_alt.
 apply is_lim_seq_ext with (fun _ => 0%R); try apply is_lim_seq_const.
 intros n. symmetry. apply (sum_n_zero (G:=R_AbelianMonoid)).
Qed.

Lemma ex_series_Rlistsum {A} (f : nat -> A -> R) (l : list A) :
 (forall x, In x l -> ex_series (fun n => f n x)) ->
 ex_series (fun n => Rlistsum (map (f n) l)).
Proof.
 induction l.
 - intros. simpl. exists 0%R.
   change (is_lim_seq (sum_n (fun _ => R0)) R0).
   apply is_lim_seq_ext with (u:=fun _ => R0); try apply is_lim_seq_const.
   intros n. symmetry. apply sum_n_R0; trivial.
 - intros Hf. simpl.
   apply (ex_series_plus (V:=R_NM)).
   + apply Hf. now left.
   + apply IHl. intros x Hx. apply Hf. now right.
Qed.

Lemma ex_series_bigsum (f : nat -> nat -> R) m :
 (forall i, (i < m)%nat -> ex_series (fun n => f n i)) ->
 ex_series (fun n => big_sum (f n) m).
Proof.
 induction m; intros Hf; simpl.
 - exists 0%R. apply is_series_R0.
 - apply (ex_series_plus (V:=R_NM)).
   + apply IHm. intros i Hi. apply Hf. lia.
   + apply Hf. lia.
Qed.

Lemma ex_series_le_eventually {K : AbsRing} {V : CompleteNormedModule K}
  (a : nat -> V) (b : nat -> R) :
  Hierarchy.eventually (fun n => norm (a n) <= b n) ->
  ex_series b -> ex_series a.
Proof.
 intros (N,H) (l,X).
 set (b' := fun n => if n <=? N then norm (a n) else b n).
 apply (ex_series_le (K:=K) (V:=V) _ b').
 { intros n. unfold b'. case Nat.leb_spec; try lra. intros. apply H. lia. }
 exists (l + (sum_n (norm∘a) N - sum_n b N))%R.
 change (is_lim_seq (sum_n b') (l + (sum_n (norm ∘ a) N - sum_n b N)))%R.
 rewrite is_lim_seq_incr_n with (N:=N).
 apply is_lim_seq_ext
   with (u := (fun n => sum_n b (n+N) + (sum_n (norm ∘ a) N - sum_n b N))%R).
 - unfold b'. clear.
   induction n.
   + simpl. ring_simplify. apply sum_n_ext_loc. intros n Hn.
     case Nat.leb_spec; lia || easy.
   + simpl. rewrite !sum_Sn. case Nat.leb_spec; try lia. intros.
     rewrite <- IHn. simpl. change plus with Rplus. ring.
 - apply is_lim_seq_plus'. now rewrite <- is_lim_seq_incr_n.
   apply is_lim_seq_const.
Qed.

Lemma ex_series_square (a : nat -> R) :
  ex_series (Rabs∘a) -> ex_series (fun n => a n^2)%R.
Proof.
 intros H.
 apply (ex_series_le_eventually (V:=R_CNM)) with (b := Rabs∘a); trivial.
 assert (H' := ex_series_lim_0 _ H).
 destruct (H' (Rgt 1)) as (N, HP).
 { exists (mkposreal 1 ltac:(lra)). simpl. intros y Y.
   apply Rabs_lt_between in Y.
   change minus with Rminus in Y; lra. }
 exists N. intros n Hn. specialize (HP n Hn).
 change norm with Rabs. rewrite Rabs_right.
 2:{ rewrite <- Rsqr_pow2. apply Rle_ge, Rle_0_sqr. }
 rewrite <- Rsqr_pow2, Rsqr_abs. unfold compose, Rsqr in *.
 rewrite <- (Rmult_1_r (Rabs (a n))) at 3.
 apply Rmult_le_compat_l; try lra. apply Rabs_pos.
Qed.

Lemma Series_rest0 (a : nat -> R) (l : R) :
 is_series a l -> forall n, is_lim_seq (sum_n_m a (S n)) (l-sum_n a n)%R.
Proof.
 intros H n.
 apply (is_lim_seq_ext_loc (fun m => sum_n a m - sum_n a n)%R).
 - exists n. intros m Hm.
   symmetry. now apply (sum_n_m_sum_n (G:=R_AbelianGroup)).
 - apply is_lim_seq_minus'; trivial. apply is_lim_seq_const.
Qed.

Lemma Series_rest (a : nat -> R) :
 ex_series a ->
 forall n, (Series a - sum_n a n = Rbar.real (Lim_seq (sum_n_m a (S n))))%R.
Proof.
 intros (l,H) n.
 rewrite (is_series_unique a l H).
 apply Series_rest0 with (n:=n) in H. apply is_lim_seq_unique in H.
 now rewrite H.
Qed.


(** Limits of C sequences *)

Local Open Scope C.

Lemma C_ball (c c' : C) (eps : R) :
  Cmod (c-c') < eps -> ball c eps c'.
Proof.
 rewrite Cmod_switch. intros H.
 change (Rabs (Re (c' - c)) < eps /\ Rabs (Im (c' - c)) < eps).
 split; apply Rle_lt_trans with (Cmod (c'-c));
  auto using re_le_Cmod, im_le_Cmod.
Qed.

Lemma ball_C (c c' : C) (eps : R) :
  ball c eps c' -> Cmod (c-c') < eps * sqrt 2.
Proof.
 rewrite Cmod_switch. intros (H,H').
 change (Rabs (Re (c' - c)) < eps) in H.
 change (Rabs (Im (c' - c)) < eps) in H'.
 assert (0 <= eps) by (generalize (Rabs_pos (Re (c'-c))); lra).
 rewrite <- (Rabs_right eps) in H,H' by lra.
 apply Rsqr_lt_abs_1 in H, H'.
 apply Rsqr_incrst_0; try apply Cmod_ge_0.
 2:{ apply Rmult_le_pos; trivial; apply sqrt_pos. }
 rewrite Rsqr_mult, Rsqr_sqrt by lra. rewrite !Rsqr_pow2 in *.
 rewrite Cmod2_alt. lra.
Qed.

Definition is_lim_Cseq (f : nat -> C) (c : C) :=
 filterlim f Hierarchy.eventually (locally c).

Lemma is_lim_Cseq_proj (f : nat -> C) (c : C) :
 is_lim_Cseq f c <->
 is_lim_seq (Re ∘ f) (Re c) /\ is_lim_seq (Im ∘ f) (Im c).
Proof.
 split.
 - split.
   + intros P (eps, HP). simpl in HP.
     destruct (H (ball c eps)) as (N, HN); [now exists eps|].
     exists N. intros n Hn. now apply HP, HN.
   + intros P (eps, HP). simpl in HP.
     destruct (H (ball c eps)) as (N, HN); [now exists eps|].
     exists N. intros n Hn. now apply HP, HN.
 - intros (H1,H2) P (eps, HP). simpl in HP.
   destruct (H1 (ball (Re c) eps)) as (N1, HN1); [now exists eps|].
   destruct (H2 (ball (Im c) eps)) as (N2, HN2); [now exists eps|].
   exists (Nat.max N1 N2). intros n Hn. apply HP.
   split; [apply HN1|apply HN2]; lia.
Qed.

Definition ex_lim_Cseq (f : nat -> C) := exists c, is_lim_Cseq f c.

Definition Lim_Cseq (f : nat -> C) : C :=
  (Rbar.real (Lim_seq (Re ∘ f)), Rbar.real (Lim_seq (Im ∘ f))).

Lemma is_lim_Cseq_unique (f : nat -> C) (c : C) :
 is_lim_Cseq f c -> Lim_Cseq f = c.
Proof.
 rewrite is_lim_Cseq_proj. intros (H1,H2). unfold Lim_Cseq.
 apply is_lim_seq_unique in H1, H2. rewrite H1, H2. simpl. now destruct c.
Qed.

Lemma Lim_Cseq_correct (f : nat -> C) :
 ex_lim_Cseq f -> is_lim_Cseq f (Lim_Cseq f).
Proof.
 intros (c & H). now rewrite (is_lim_Cseq_unique _ _ H).
Qed.

Lemma is_lim_Cseq_0_Cmod (f : nat -> C) :
 is_lim_seq (Cmod ∘ f) 0%R -> is_lim_Cseq f 0.
Proof.
 intros H.
 apply is_lim_Cseq_proj. simpl.
 split; apply is_lim_seq_0_abs with (v := Cmod ∘ f); trivial;
 exists O; intros; apply re_le_Cmod || apply im_le_Cmod.
Qed.

Lemma is_lim_Cseq_Cmod (f : nat -> C) (l : C) :
 is_lim_Cseq f l -> is_lim_seq (Cmod ∘ f) (Cmod l).
Proof.
 intros H P (eps,HP). simpl in HP.
 assert (LT : 0 < /2 * eps).
 { apply Rmult_lt_0_compat. lra. apply eps. }
 set (eps' := mkposreal _ LT).
 destruct (H (ball l eps')) as (N, HN); [now exists eps'|].
 exists N. intros n Hn. apply HP.
 change (Rabs (Cmod (f n) - Cmod l) < eps).
 assert (Cmod (f n - l) < eps).
 { apply Rsqr_incrst_0; trivial using Cmod_ge_0.
   2:{ generalize (cond_pos eps); lra. }
   rewrite !Rsqr_pow2, Cmod2_alt.
   destruct (HN n Hn) as (H1,H2).
   change (Rabs (Re (f n - l)) < eps') in H1.
   change (Rabs (Im (f n - l)) < eps') in H2.
   rewrite <- (Rabs_right eps') in H1,H2 by (generalize (cond_pos eps'); lra).
   apply Rsqr_lt_abs_1 in H1,H2. rewrite !Rsqr_pow2 in H1,H2.
   change (pos eps') with (/2 * eps)%R in H1,H2. nra. }
 apply Rabs_lt_between. split.
 - apply Ropp_lt_cancel. rewrite Ropp_involutive, Ropp_minus_distr.
   rewrite <- (Cmod_opp (f n)).
   apply Rle_lt_trans with (Cmod (l - f n)); [apply Cmod_triangle'|].
   now rewrite Cmod_switch.
 - rewrite <- (Cmod_opp l).
   apply Rle_lt_trans with (Cmod (f n - l)); [apply Cmod_triangle'|]. easy.
Qed.

Lemma is_lim_Cseq_ext (f g : nat -> C)(l : C) :
 (forall n, f n = g n) -> is_lim_Cseq f l -> is_lim_Cseq g l.
Proof.
 intros E. rewrite !is_lim_Cseq_proj. intros (Hf,Hg). split.
 - apply is_lim_seq_ext with (u:=Re∘f); trivial.
   intros n. unfold compose. now rewrite E.
 - apply is_lim_seq_ext with (u:=Im∘f); trivial.
   intros n. unfold compose. now rewrite E.
Qed.

Lemma is_lim_Cseq_ext_loc (f g : nat -> C)(l : C) :
 Hierarchy.eventually (fun n => f n = g n) ->
 is_lim_Cseq f l -> is_lim_Cseq g l.
Proof.
 intros (N & HN). rewrite !is_lim_Cseq_proj. intros (Hf,Hg). split.
 - apply is_lim_seq_ext_loc with (u:=Re∘f); trivial.
   exists N. intros n Hn. unfold compose. now rewrite HN.
 - apply is_lim_seq_ext_loc with (u:=Im∘f); trivial.
   exists N. intros n Hn. unfold compose. now rewrite HN.
Qed.

Lemma is_lim_Cseq_Cmod' (a : nat -> C) (b : nat -> R) (la : C) (lb : R) :
  (forall n, Cmod (a n) <= b n) ->
  is_lim_Cseq a la -> is_lim_seq b lb -> Cmod la <= lb.
Proof.
 intros LE Ha Hb.
 assert (Ha' := is_lim_Cseq_Cmod a la Ha).
 now apply (is_lim_seq_le (Cmod∘a) b (Cmod la) lb).
Qed.

Lemma is_lim_Cseq_const (c:C) : is_lim_Cseq (fun _ => c) c.
Proof.
 rewrite is_lim_Cseq_proj. split.
 apply is_lim_seq_ext with (u:= fun _ => Re c). easy. apply is_lim_seq_const.
 apply is_lim_seq_ext with (u:= fun _ => Im c). easy. apply is_lim_seq_const.
Qed.

Lemma Lim_Cseq_const (c:C) : Lim_Cseq (fun _ => c) = c.
Proof.
 apply is_lim_Cseq_unique, is_lim_Cseq_const.
Qed.

Lemma is_lim_Cseq_plus (a b : nat -> C) (la lb : C) :
 is_lim_Cseq a la -> is_lim_Cseq b lb ->
 is_lim_Cseq (fun n => a n + b n) (la + lb).
Proof.
 rewrite !is_lim_Cseq_proj. intros (Ha1,Ha2) (Hb1,Hb2). split.
 - apply is_lim_seq_ext with (fun n => (Re ∘ a) n + (Re ∘ b) n)%R.
   + intros n. apply re_plus.
   + now apply is_lim_seq_plus'.
 - apply is_lim_seq_ext with (fun n => (Im ∘ a) n + (Im ∘ b) n)%R.
   + intros n. apply im_plus.
   + now apply is_lim_seq_plus'.
Qed.

Lemma Lim_Cseq_plus (a b : nat -> C) :
 ex_lim_Cseq a -> ex_lim_Cseq b ->
 Lim_Cseq (fun n => a n + b n) = Lim_Cseq a + Lim_Cseq b.
Proof.
 intros (la,Ha) (lb,Hb). apply is_lim_Cseq_unique.
 apply is_lim_Cseq_plus.
 - apply Lim_Cseq_correct. now exists la.
 - apply Lim_Cseq_correct. now exists lb.
Qed.

Lemma is_lim_Cseq_minus (a b : nat -> C) (la lb : C) :
 is_lim_Cseq a la -> is_lim_Cseq b lb ->
 is_lim_Cseq (fun n => a n - b n) (la - lb).
Proof.
 rewrite !is_lim_Cseq_proj. intros (Ha1,Ha2) (Hb1,Hb2). split.
 - apply is_lim_seq_ext with (fun n => (Re ∘ a) n - (Re ∘ b) n)%R.
   + intros n. unfold compose, Rminus. rewrite <- re_opp. apply re_plus.
   + now apply is_lim_seq_minus'.
 - apply is_lim_seq_ext with (fun n => (Im ∘ a) n - (Im ∘ b) n)%R.
   + intros n. unfold compose, Rminus. rewrite <- im_opp. apply im_plus.
   + now apply is_lim_seq_minus'.
Qed.

Lemma is_lim_Cseq_mult (a b : nat -> C) (la lb : C) :
 is_lim_Cseq a la -> is_lim_Cseq b lb ->
 is_lim_Cseq (fun n => a n * b n) (la * lb).
Proof.
 rewrite !is_lim_Cseq_proj. intros (Ha1,Ha2) (Hb1,Hb2). split.
 - apply is_lim_seq_ext with (fun n => (Re ∘ a) n * (Re ∘ b) n
                                     - (Im ∘ a) n * (Im ∘ b) n)%R.
   + intros n. apply re_mult.
   + apply is_lim_seq_plus'. now apply is_lim_seq_mult'.
     apply is_lim_seq_opp'. now apply is_lim_seq_mult'.
 - apply is_lim_seq_ext with (fun n => (Re ∘ a) n * (Im ∘ b) n
                                     + (Im ∘ a) n * (Re ∘ b) n)%R.
   + intros n. apply im_mult.
   + apply is_lim_seq_plus'; now apply is_lim_seq_mult'.
Qed.

Lemma is_lim_Cseq_incr_n (u : nat -> C) (N : nat) l :
  is_lim_Cseq u l <-> is_lim_Cseq (fun n : nat => u (n + N)%nat) l.
Proof.
 rewrite !is_lim_Cseq_proj.
 rewrite (is_lim_seq_incr_n (Re∘_) N).
 rewrite (is_lim_seq_incr_n (Im∘_) N). easy.
Qed.

Lemma is_lim_Cseq_alt0 a (l:C) :
  is_lim_Cseq a l <-> is_lim_seq (fun n => Cmod (a n - l)) 0%R.
Proof.
 split.
 - intros H.
   rewrite <- Cmod_0.
   apply is_lim_Cseq_Cmod.
   replace 0 with (l-l) by lca. apply is_lim_Cseq_minus; trivial.
   apply is_lim_Cseq_const.
 - intros H.
   apply is_lim_Cseq_0_Cmod in H.
   apply is_lim_Cseq_ext with (fun n => (a n -l)+l); try (intros; ring).
   rewrite <- (Cplus_0_l l) at 1.
   apply is_lim_Cseq_plus; trivial. apply is_lim_Cseq_const.
Qed.

Lemma is_lim_Cseq_alt a (l:C) :
  is_lim_Cseq a l <->
  forall eps : posreal, exists N, forall n, (N<=n)%nat ->
   Cmod (a n - l) < eps.
Proof.
 rewrite is_lim_Cseq_alt0.
 rewrite <- is_lim_seq_spec. unfold is_lim_seq'. simpl.
 split; intros H eps; destruct (H eps) as (N & HN); exists N; intros n Hn;
  specialize (HN n Hn);
  now rewrite Rminus_0_r, Rabs_pos_eq in * by apply Cmod_ge_0.
Qed.

Lemma is_lim_Cseq_Clistsum (f : nat -> C -> C) (g : C -> C) l :
 (forall x, In x l -> is_lim_Cseq (fun n => f n x) (g x)) ->
 is_lim_Cseq (fun n => Clistsum (map (f n) l)) (Clistsum (map g l)).
Proof.
 induction l.
 - simpl. intros _. apply is_lim_Cseq_const.
 - intros H. simpl. apply is_lim_Cseq_plus. apply H; now left.
   apply IHl. intros x Hx. apply H; now right.
Qed.

Lemma is_lim_Cseq_bigsum (f : nat -> nat -> C) (lims : nat -> C) m :
 (forall i, (i < m)%nat -> is_lim_Cseq (fun n => f n i) (lims i)) ->
 is_lim_Cseq (fun n => big_sum (f n) m) (big_sum lims m).
Proof.
 induction m; intros Hf.
 - apply is_lim_Cseq_const.
 - simpl. apply is_lim_Cseq_plus.
   + apply IHm. intros i Hi. apply Hf. lia.
   + apply Hf. lia.
Qed.

Lemma is_lim_Cseq_subseq (u : nat -> C)(l : C)(phi : nat -> nat) :
  Hierarchy.filterlim phi Hierarchy.eventually Hierarchy.eventually ->
  is_lim_Cseq u l -> is_lim_Cseq (fun n : nat => u (phi n)) l.
Proof.
 intros H1 H2. rewrite is_lim_Cseq_proj in *. split; unfold compose.
 - now apply (is_lim_seq_subseq (fun n => Re (u n))).
 - now apply (is_lim_seq_subseq (fun n => Im (u n))).
Qed.

(** Series on C *)

Lemma is_Cseries_alt (a : nat -> C) (l : C) :
 is_series a l <-> is_lim_Cseq (sum_n a) l.
Proof.
 reflexivity.
Qed.

Definition CSeries (a : nat -> C) : C := Lim_Cseq (sum_n a).

Lemma CSeries_unique (a : nat -> C) (l : C) :
  is_series a l -> CSeries a = l.
Proof.
 intros H. apply is_lim_Cseq_unique, is_lim_Cseq_proj. split.
 - red. eapply filterlim_comp with (f := sum_n a) (g:=Re); eauto.
   intros P (eps, H'). exists eps. intros c Hc. apply H', Hc.
 - red. eapply filterlim_comp with (f := sum_n a) (g:=Im); eauto.
   intros P (eps, H'). exists eps. intros c Hc. apply H', Hc.
Qed.

Lemma CSeries_correct (a : nat -> C) :
  ex_series a -> is_series a (CSeries a).
Proof.
 intros (l & H). simpl in l. now rewrite (CSeries_unique a l).
Qed.

Lemma pos_series_pos_sum (a : nat -> R) l :
  is_series a l ->
  (forall n, 0 <= a n) ->
  forall n, sum_n a n <= l.
Proof.
 intros H Ha n. change (is_lim_seq (sum_n a) l) in H.
 apply is_lim_seq_incr_compare; trivial.
 intros m. rewrite sum_Sn. unfold plus. simpl. generalize (Ha (S m)). lra.
Qed.

Lemma pos_series_pos_lim (a : nat -> R) l :
  is_series a l -> (forall n, 0 <= a n) -> 0 <= l.
Proof.
 intros H Ha.
 apply Rle_trans with (sum_n a O).
 rewrite sum_O. apply Ha.
 now apply (pos_series_pos_sum _ _ H).
Qed.

Lemma ex_series_Cmod (a : nat -> C) :
 ex_series (Cmod ∘ a) -> ex_series a.
Proof.
 apply (ex_series_le (V := C_CNM)).
 intros. rewrite <- Complex.Cmod_norm. apply Rle_refl.
Qed.

Lemma is_series_Cmod (a : nat -> C) (l:R) :
 is_series (Cmod ∘ a) l ->
 exists l':C, is_series a l' /\ Cmod l' <= l.
Proof.
 intros H. destruct (ex_series_Cmod a) as (l' & Hl'); [now exists l|].
 simpl in l'. exists l'. split; trivial.
 assert (E := is_lim_Cseq_Cmod (sum_n a) l' Hl').
 apply (is_lim_seq_le (Cmod ∘ (sum_n a)) (sum_n (Cmod ∘ a)) (Cmod l') l);
  trivial. intros. apply sum_n_triangle.
Qed.

Lemma CSeries_Cmod (a : nat -> C) :
  ex_series (Cmod ∘ a) -> Cmod (CSeries a) <= Series (Cmod ∘ a).
Proof.
 intros (l,Hl). destruct (is_series_Cmod a l Hl) as (l' & Hl' & LE).
 erewrite CSeries_unique; eauto. erewrite is_series_unique; eauto.
Qed.

Lemma CSeries_rest0 (a : nat -> C) (l : C) :
 is_series a l -> forall n, is_lim_Cseq (sum_n_m a (S n)) (l-sum_n a n).
Proof.
 intros H n.
 assert (H' : is_lim_Cseq (fun m => sum_n a m - sum_n a n) (l-sum_n a n)).
 { apply is_lim_Cseq_minus; trivial. apply is_lim_Cseq_const. }
 rewrite is_lim_Cseq_proj in *. split.
 - apply (is_lim_seq_ext_loc (Re ∘ (fun m => sum_n a m - sum_n a n)));
    try apply H'.
   exists n. intros m Hm. unfold compose. f_equal.
   symmetry. now apply (sum_n_m_sum_n (G:=Complex.C_AbelianGroup)).
 - apply (is_lim_seq_ext_loc (Im ∘ (fun m => sum_n a m - sum_n a n)));
    try apply H'.
   exists n. intros m Hm. unfold compose. f_equal.
   symmetry. now apply (sum_n_m_sum_n (G:=Complex.C_AbelianGroup)).
Qed.

Lemma CSeries_RtoC_impl (a : nat -> R) (l:C) :
  is_series (RtoC∘a) l -> is_series a (Re l) /\ Im l = 0%R.
Proof.
 intros H.
 change (is_lim_Cseq (sum_n (RtoC∘a)) l) in H.
 rewrite is_lim_Cseq_proj in H. destruct H as (H1,H2).
 apply is_lim_seq_ext with (v:=sum_n a) in H1.
 2:{ intros n. unfold compose. rewrite re_sum_n. now apply sum_n_ext. }
 apply is_lim_seq_ext with (v:=fun _ => 0%R) in H2.
 2:{ intros n. unfold compose. rewrite im_sum_n. apply sum_n_R0. }
 split. apply H1. apply is_lim_seq_unique in H2.
 rewrite Lim_seq_const in H2. now injection H2.
Qed.

Lemma CSeries_RtoC (a : nat -> R) (l:R) :
  is_series (RtoC∘a) (RtoC l) <-> is_series a l.
Proof.
 split.
 - intros H. change l with (Re (RtoC l)). now apply CSeries_RtoC_impl.
 - intros H.
   change (is_lim_Cseq (sum_n (RtoC∘a)) l).
   rewrite is_lim_Cseq_proj; simpl. split.
   + apply is_lim_seq_ext with (u:=sum_n a); try easy.
     intros n. unfold compose. rewrite re_sum_n. now apply sum_n_ext.
   + apply is_lim_seq_ext with (u:=fun _ => 0%R); try apply is_lim_seq_const.
     intros n. unfold compose. rewrite im_sum_n. symmetry.
     now apply sum_n_R0.
Qed.

Lemma ex_series_lim_C0 (a : nat -> C) :
  ex_series a -> is_lim_Cseq a 0.
Proof.
 intros H.
 apply (Cauchy_ex_series (V := C_CNM)) in H. red in H.
 apply is_lim_Cseq_alt. intros eps.
 destruct (H eps) as (N & HN). clear H.
 exists N. intros n Hn.
 replace (a n - 0) with (a n) by lca.
 specialize (HN n n Hn Hn).
 now rewrite sum_n_n, <- Cmod_norm in HN.
Qed.

Local Open Scope R.

(** Extra facts about order on Rbar *)

Lemma Rbar_le_carac_via_lt a b :
  (forall c:R, Rbar.Rbar_lt c a -> Rbar.Rbar_le c b) -> Rbar.Rbar_le a b.
Proof.
 destruct a as [a| | ], b as [b| | ]; simpl; trivial; intros H.
 - destruct (Rle_lt_dec a b) as [LE|LT]; trivial.
   specialize (H ((b+a)/2)). lra.
 - apply (H (a-1)%R). lra.
 - specialize (H (b+1)%R). lra.
 - now apply (H 0).
Qed.

Lemma Rbar_le_mult_div (a : R) (b c : Rbar.Rbar) :
 0 < a ->
 Rbar.Rbar_le (Rbar.Rbar_mult a b) c <->
 Rbar.Rbar_le b (Rbar.Rbar_mult (/a) c).
Proof.
 intros Ha.
 assert (Ha' : 0 < /a) by now apply Rinv_0_lt_compat.
 destruct b as [b| | ], c as [c| | ]; simpl; trivial;
 repeat destruct Rle_dec; try lra;
 repeat destruct Rle_lt_or_eq_dec; simpl; try lra.
 split; intros H.
 - apply Rmult_le_reg_l with a; trivial. field_simplify; try lra.
 - replace c with (a * (c * /a)) by (field; lra).
   apply Rmult_le_compat_l; lra.
Qed.

Lemma Rbar_lt_mult_div (a : R) (b c : Rbar.Rbar) :
 0 < a ->
 Rbar.Rbar_lt (Rbar.Rbar_mult a b) c <->
 Rbar.Rbar_lt b (Rbar.Rbar_mult (/a) c).
Proof.
 intros Ha.
 assert (Ha' : 0 < /a) by now apply Rinv_0_lt_compat.
 destruct b as [b| | ], c as [c| | ]; simpl; trivial;
 repeat destruct Rle_dec; try lra;
 repeat destruct Rle_lt_or_eq_dec; simpl; try lra.
 split; intros H.
 - apply Rmult_lt_reg_l with a; trivial. field_simplify; try lra.
 - replace c with (a * (c * /a)) by (field; lra).
   apply Rmult_lt_compat_l; lra.
Qed.

(** Customized versions of Rolle Lemma and Mean-Value-Theorem.
    - For simplicity, we ask for derivability also on the interval borders
      (instead of just continuity).
    - Unlike many other MVT (e.g. Coquelicot's one) the existing point c
      is strictly inside a b. *)

Lemma MVT_weak (f df : R -> R) (a b : R) :
 (forall x, a <= x <= b -> is_derive f x (df x)) ->
 a < b ->
 exists c, a < c < b /\ f b - f a = df c * (b-a).
Proof.
 intros Df Hab.
 destruct (MVT_cor2 f df a b) as (c & Hc & Hc'); trivial.
 { intros. apply is_derive_Reals. apply Df; lra. }
 now exists c.
Qed.

Lemma Rolle_weak (f df : R -> R) (a b : R) :
  (forall x, a <= x <= b -> is_derive f x (df x)) ->
  a < b ->
  f a = f b ->
  exists c, a < c < b /\ df c = 0.
Proof.
 intros Hf Hab E.
 destruct (MVT_weak f df a b) as (c & Hc & Hc'); trivial.
 exists c; split; trivial. replace (f b - f a) with 0 in Hc' by lra.
 symmetry in Hc'. apply Rmult_integral in Hc'. destruct Hc'; trivial; lra.
Qed.

(** Key properties of Lub_Rbar *)

Lemma Lub_Rbar_ub (E:R->Prop) x : E x -> Rbar.Rbar_le x (Lub.Lub_Rbar E).
Proof.
 intros. now apply Lub.Lub_Rbar_correct.
Qed.

Lemma Lub_Rbar_least (E:R->Prop) l :
 (forall x, E x -> Rbar.Rbar_le x l) -> Rbar.Rbar_le (Lub.Lub_Rbar E) l.
Proof.
 intros H. apply Lub.Lub_Rbar_correct. exact H.
Qed.

(** Power series on R : More on CV_disk and CV_radius *)

Lemma CV_disk_rabs a x : CV_disk a x <-> CV_disk a (Rabs x).
Proof.
 unfold CV_disk.
 split; apply ex_series_ext; intros n;
  now rewrite !Rabs_mult, !RPow_abs, Rabs_Rabsolu.
Qed.

Lemma CV_disk_le_radius (a:nat->R) (x:R) :
 CV_disk a x -> Rbar.Rbar_le x (CV_radius a).
Proof.
 intros. now apply Lub_Rbar_ub.
Qed.

Lemma CV_radius_ge_1 (a : nat -> R) :
  ex_series (Rabs∘a) -> Rbar.Rbar_le 1%R (CV_radius a).
Proof.
 intros H. apply CV_disk_le_radius.
 red. eapply ex_series_ext; eauto. intros n. now rewrite pow1, Rmult_1_r.
Qed.

Lemma CV_radius_le (a b : nat -> R) :
 (forall n, Rabs (a n) <= Rabs (b n)) ->
 Rbar.Rbar_le (CV_radius b) (CV_radius a).
Proof.
 intros H.
 unfold CV_radius, Lub.Lub_Rbar.
 destruct Lub.ex_lub_Rbar as (ubb & Hb & Hb').
 destruct Lub.ex_lub_Rbar as (uba & Ha & Ha'). simpl.
 - red in Hb, Ha. apply Hb'. red. intros x Hx. apply Ha.
   clear - H Hx. unfold CV_disk in *.
   eapply (ex_series_le (V:=R_CNM)); eauto.
   intros n. change norm with Rabs. rewrite Rabs_Rabsolu, !Rabs_mult.
   apply Rmult_le_compat_r; trivial using Rabs_pos.
Qed.

Definition CV_disk' (a : nat -> R) (r : R) :=
 exists r', Rabs r' = r /\ ex_series (fun n => a n * r'^n)%R.

Definition CV_radius' (a : nat -> R) : Rbar.Rbar :=
  Lub.Lub_Rbar (CV_disk' a).

Lemma CV_disk_disk' a r : 0<=r -> CV_disk a r -> CV_disk' a r.
Proof.
 unfold CV_disk, CV_disk'. intros Hr H.
 apply ex_series_Rabs in H. exists r. split; trivial. now apply Rabs_pos_eq.
Qed.

Lemma CV_radius_radius' a : CV_radius a = CV_radius' a.
Proof.
 apply Rbar.Rbar_le_antisym.
 { apply Lub.Lub_Rbar_correct. red.
   intros x Hx. destruct (Rle_lt_dec 0 x).
   - apply Lub_Rbar_ub. now apply CV_disk_disk'.
   - apply Rbar.Rbar_le_trans with (Rbar.Finite 0). simpl; lra.
     apply Lub_Rbar_ub. red. exists 0%R. split. apply Rabs_pos_eq; lra.
     eapply ex_series_ext; [ | exists (a O); apply is_pseries_0 ].
     intros n. simpl. now rewrite Rmult_comm. }
 { apply Lub_Rbar_least.
   intros x (x' & <- & E).
   destruct (Rbar.Rbar_le_lt_dec (Rabs x') (CV_radius a)) as [LE|LT]; trivial.
   exfalso.
   now apply (CV_disk_outside _ _ LT), ex_series_lim_0. }
Qed.

(** Power series on C *)

Local Open Scope C.

Definition is_CPowerSeries (a : nat -> C) (z lim : C) :=
  is_lim_Cseq (sum_n (fun n => a n * z^n)) lim.

Definition ex_CPowerSeries (a : nat -> C) (z : C) :=
  exists lim, is_CPowerSeries a z lim.

Definition CPowerSeries (a : nat -> C) (z : C) : C :=
  CSeries (fun k => a k * z ^ k).

Lemma CPowerSeries_unique (a : nat -> C) (z l : C) :
  is_CPowerSeries a z l -> CPowerSeries a z = l.
Proof.
 apply CSeries_unique.
Qed.

Lemma CPowerSeries_correct (a : nat -> C) z :
  ex_CPowerSeries a z -> is_CPowerSeries a z (CPowerSeries a z).
Proof.
 apply CSeries_correct.
Qed.

Lemma is_CPowerSeries_alt a z l : is_CPowerSeries a z l <-> is_pseries a z l.
Proof.
 unfold is_CPowerSeries, is_lim_Cseq.
 change (filterlim _ _ _) with (is_series (fun n => a n * z^n) l).
 unfold is_pseries.
 assert (E : forall n, a n * z ^ n = scal (pow_n z n) (a n)).
 { intros n. change scal with Cmult. change pow_n with Cpow. ring. }
 split; apply is_series_ext. apply E. intros n; now rewrite E.
Qed.

Lemma ex_CPowerSeries_alt a z : ex_CPowerSeries a z <-> ex_pseries a z.
Proof.
 split; intros (l & L); exists l; revert L; apply (is_CPowerSeries_alt a z l).
Qed.

Lemma ex_CPowerSeries_Cmod a z :
  ex_pseries (Cmod∘a) (Cmod z) -> ex_CPowerSeries a z.
Proof.
 intros H.
 rewrite ex_pseries_R in H.
 eapply ex_series_ext in H.
 2:{ intros n. unfold "∘". now rewrite <- Cmod_pow, <- Cmod_mult. }
 apply ex_series_Cmod in H.
 rewrite ex_CPowerSeries_alt. revert H. apply ex_series_ext.
 intros n. change scal with Cmult; change pow_n with Cpow. lca.
Qed.

Lemma Cmod_prod_aux a b n : Cmod b <= 1 -> Cmod (a * b^n) <= Cmod a.
Proof.
 intros Hb.
 rewrite Cmod_mult, Cmod_pow.
 rewrite <- (Rmult_1_r (Cmod a)) at 2.
 apply Rmult_le_compat_l. apply Cmod_ge_0.
 apply Rpow_le1. split. apply Cmod_ge_0. apply Hb.
Qed.

Lemma CPowerSeries_bound1 (a : nat -> C) l z :
  is_series (Cmod ∘ a) l -> Cmod z <= 1 ->
  forall n, Cmod (sum_n (fun k => a k * z^k) n) <= l.
Proof.
 intros Ha Hz n.
 eapply Rle_trans; [apply sum_n_triangle|].
 apply Rle_trans with (sum_n (Cmod ∘ a) n);
  [apply sum_n_le | apply pos_series_pos_sum; eauto; intros; apply Cmod_ge_0].
 intros m. now apply Cmod_prod_aux.
Qed.

Lemma CPowerSeries_bound2 (a : nat -> C) l z :
  is_series (Cmod ∘ a) l -> Cmod z <= 1 ->
  Cmod (CPowerSeries a z) <= l.
Proof.
 intros H Hz.
 unfold CPowerSeries. rewrite <- (is_series_unique (Cmod∘a) l H).
 eapply Rle_trans.
 - apply CSeries_Cmod.
   unfold compose.
   apply (ex_series_le (V :=R_CNM)) with (b:=Cmod∘a);
    try now exists l.
   intros n. change norm with Rabs.
   rewrite Rabs_right by apply Rle_ge, Cmod_ge_0. now apply Cmod_prod_aux.
 - apply Series_le. 2:now exists l.
   intros n. unfold compose. split; try apply Cmod_ge_0.
   now apply Cmod_prod_aux.
Qed.

Lemma CPowerSeries_bound3 (a : nat -> C) (l:R) z :
 is_series (Cmod ∘ a) l -> Cmod z <= 1 ->
 forall n,
 Cmod (CPowerSeries a z - sum_n (fun k => a k * z^k) n) <=
 l - sum_n (Cmod ∘ a) n.
Proof.
 intros H Hz n.
 assert (H' : ex_series (fun k => a k * z^k)).
 { apply ex_series_Cmod.
   apply (ex_series_le (V :=R_CNM)) with (b:=Cmod∘a);
     try now exists l.
   intros m. change norm with Rabs.
   rewrite Rabs_right by apply Rle_ge, Cmod_ge_0. now apply Cmod_prod_aux. }
 destruct H' as (l',H'). simpl in l'.
 unfold CPowerSeries. rewrite (CSeries_unique _ _ H').
 assert (R := Series_rest0 _ _ H n).
 assert (R' := CSeries_rest0 _ _ H' n).
 eapply is_lim_Cseq_Cmod'; eauto.
 intros m. eapply Rle_trans; [apply sum_n_m_triangle|].
 apply sum_n_m_le. intros k. now apply Cmod_prod_aux.
Qed.

Definition PS_geom r := fun n => r^S n.

Lemma is_powerseries_invlin r x : r<>0 -> Cmod (r*x) < 1 ->
 is_CPowerSeries (PS_geom r) x (/ (/r - x)).
Proof.
 intros Hr Hx. unfold PS_geom.
 apply is_lim_Cseq_ext with (fun n => (1 - (r*x)^S n)/(/r-x)).
 { intros n. rewrite <- (Cmult_1_l (sum_n _ _)).
   rewrite <- (Cinv_l (/r-x)) at 2.
   2:{ intros E. apply Ceq_minus in E.
       rewrite <- E, Cinv_r, Cmod_1 in Hx; trivial. lra. }
   unfold Cdiv. rewrite Cmult_comm, <- Cmult_assoc. f_equal.
   rewrite sum_n_ext with (b:=fun k => r * (r*x)^k).
   2:{ intros k. now rewrite Cpow_S, Cpow_mult_l, Cmult_assoc. }
   rewrite sum_n_Cmult_l, Cmult_assoc.
   replace ((/r-x)*r) with (1-r*x) by now field.
   symmetry. apply sum_n_Cpow. }
 unfold Cdiv. rewrite <- (Cmult_1_l (/(/r-x))) at 1.
 apply is_lim_Cseq_mult; [|apply is_lim_Cseq_const].
 replace 1 with (1-0) at 1 by lca.
 apply is_lim_Cseq_minus. apply is_lim_Cseq_const.
 apply is_lim_Cseq_0_Cmod.
 apply is_lim_seq_ext with (fun n => (Cmod (r*x))^S n)%R.
 - intros n. unfold compose. now rewrite Cmod_pow.
 - rewrite <- is_lim_seq_incr_1. apply is_lim_seq_geom.
   now rewrite Rabs_right by apply Rle_ge, Cmod_ge_0.
Qed.

(** Delaying a sequence with extra initial zeros.
    See also Coquelicot.PSeries.PS_incr_n someday. *)

Definition delay {G:AbelianMonoid} (a:nat->G) p :=
  fun n => if n <? p then zero else a (n-p)%nat.

Lemma sum_n_delay {G:AbelianMonoid} (a:nat->G) p n :
  sum_n (delay a p) (n+p) = sum_n a n.
Proof.
 induction n.
 - rewrite Nat.add_0_l, sum_O.
   destruct p.
   + now rewrite sum_O.
   + rewrite sum_Sn.
     erewrite sum_n_ext_loc, sum_n_zero.
     2:{ intros k K. unfold delay. case Nat.ltb_spec; easy || lia. }
     unfold delay. simpl.
     case Nat.ltb_spec; try lia. intros _.
     replace (p-p)%nat with O by lia. apply plus_zero_l.
 - simpl. rewrite !sum_Sn, IHn. f_equal. unfold delay.
   case Nat.ltb_spec; try lia. intros _. f_equal. lia.
Qed.

Lemma delay_comp {G G':AbelianMonoid} (h:G->G') p (a:nat->G) :
 h zero = zero -> forall n, delay (h∘a) p n = h (delay a p n).
Proof.
 intros H n. unfold delay. now case Nat.ltb.
Qed.

Lemma delay_series_R p (a:nat->R) l :
  is_series a l -> is_series (delay a p) l.
Proof.
 intros H.
 change (is_lim_seq (sum_n (delay a p)) l).
 apply is_lim_seq_incr_n with (N:=p).
 eapply is_lim_seq_ext; [|apply H].
 intros n. symmetry. apply sum_n_delay.
Qed.

Lemma delay_powerseries_R p a x lim :
  is_series (fun n => a n * x^n)%R lim ->
  is_series (fun n => delay a p n * x^n)%R (x^p * lim)%R.
Proof.
 intros H.
 rewrite is_series_alt.
 rewrite is_lim_seq_incr_n with (N:=p).
 apply is_lim_seq_ext with (fun n => x^p * sum_n (fun k => a k * x^k) n)%R.
 { intros n. rewrite <- (sum_n_mult_l (K:=R_AbsRing)).
   rewrite <- sum_n_delay with (p:=p). apply sum_n_ext. clear n.
   intros n. unfold delay. case Nat.ltb_spec; intros.
   - change zero with R0. lra.
   - change mult with Rmult.
     rewrite !(Rmult_comm (a _)), <- Rmult_assoc, <- pow_add.
     f_equal. f_equal. lia. }
 apply is_lim_seq_mult'; trivial using is_lim_seq_const.
Qed.

Lemma delay_powerseries p a z lim :
  is_CPowerSeries a z lim ->
  is_CPowerSeries (delay a p) z (z^p * lim).
Proof.
 unfold is_CPowerSeries. intros H.
 rewrite is_lim_Cseq_incr_n with (N:=p).
 apply is_lim_Cseq_ext with (fun n => z^p * sum_n (fun k => a k * z^k) n).
 { intros n. rewrite <- sum_n_Cmult_l.
   rewrite <- sum_n_delay with (p:=p). apply sum_n_ext. clear n.
   intros n. unfold delay. case Nat.ltb_spec; intros.
   - change zero with 0. lca.
   - rewrite Cmult_assoc, (Cmult_comm (z^p)), <- Cmult_assoc. f_equal.
     rewrite <- Cpow_add. f_equal. lia. }
 apply is_lim_Cseq_mult; trivial using is_lim_Cseq_const.
Qed.

(** Convergence disk and radius for C power series *)

Definition C_CV_disk (a : nat -> C) (r : C) :=
  ex_series (fun n => Cmod (a n * r^n)).

Definition C_CV_radius (a : nat -> C) : Rbar.Rbar :=
  Lub.Lub_Rbar (C_CV_disk a).

Lemma C_CV_disk_alt a r : C_CV_disk a r <-> CV_disk (Cmod∘a) (Cmod r).
Proof.
 unfold C_CV_disk, CV_disk.
 split; apply ex_series_ext;
  intros n; unfold "∘";
   now rewrite <- Cmod_pow, <- Cmod_mult, Rabs_pos_eq by apply Cmod_ge_0.
Qed.

Lemma C_CV_radius_alt a : C_CV_radius a = CV_radius (Cmod∘a).
Proof.
 unfold C_CV_radius, CV_radius. apply Lub.Lub_Rbar_eqset.
 intros x. now rewrite C_CV_disk_alt, Cmod_R, <- CV_disk_rabs.
Qed.

Lemma C_CV_disk_correct (a : nat -> C) (z : C) :
  C_CV_disk a z -> ex_CPowerSeries a z.
Proof.
 rewrite C_CV_disk_alt. intros H. apply ex_CPowerSeries_Cmod.
 now apply CV_disk_correct.
Qed.

Lemma C_CV_radius_inside (a : nat -> C) (z : C) :
  Rbar.Rbar_lt (Cmod z) (C_CV_radius a) -> ex_CPowerSeries a z.
Proof.
 intros H. apply ex_CPowerSeries_Cmod. apply CV_radius_inside.
 now rewrite <- C_CV_radius_alt, Rabs_pos_eq by apply Cmod_ge_0.
Qed.

Lemma C_CV_radius_outside (a : nat -> C) (z : C) :
  Rbar.Rbar_lt (C_CV_radius a) (Cmod z) ->
  ~is_lim_Cseq (fun n => a n * z^n) 0.
Proof.
 intros H. rewrite C_CV_radius_alt in H.
 rewrite <- (Rabs_pos_eq (Cmod z)) in H by apply Cmod_ge_0.
 apply CV_disk_outside in H. contradict H.
 apply is_lim_Cseq_Cmod in H. rewrite Cmod_0 in H.
 eapply is_lim_seq_ext; eauto.
 intros n. unfold "∘". now rewrite <- Cmod_pow, <- Cmod_mult.
Qed.

Definition C_CV_disk' (a : nat -> C) (r : R) :=
 exists z, Cmod z = r /\ ex_CPowerSeries a z.

Definition C_CV_radius' (a : nat -> C) : Rbar.Rbar :=
  Lub.Lub_Rbar (C_CV_disk' a).

Lemma C_CV_radius_radius' a : C_CV_radius a = C_CV_radius' a.
Proof.
 apply Rbar.Rbar_le_antisym.
 { apply Lub.Lub_Rbar_correct.
   intros x Hx. destruct (Rle_lt_dec 0 x).
   - apply Lub_Rbar_ub. exists x. split.
     + now rewrite Cmod_R, Rabs_pos_eq.
     + now apply ex_series_Cmod.
   - apply Rbar.Rbar_le_trans with (Rbar.Finite 0). simpl; lra.
     apply Lub_Rbar_ub. red. exists 0%R. split. apply Cmod_0.
     exists (a O). rewrite is_CPowerSeries_alt. apply (is_pseries_0 a). }
 { apply Lub_Rbar_least.
   intros x (z & <- & E).
   destruct (Rbar.Rbar_le_lt_dec (Cmod z) (C_CV_radius a)) as [LE|LT];
    trivial.
   exfalso.
   rewrite C_CV_radius_alt in LT.
   rewrite <- (Rabs_pos_eq (Cmod z)) in LT by apply Cmod_ge_0.
   apply ex_series_lim_C0 in E.
   apply is_lim_Cseq_Cmod in E. rewrite Cmod_0 in E.
   apply (CV_disk_outside _ _ LT).
   eapply is_lim_seq_ext; eauto.
   intros n. unfold "∘". now rewrite <- Cmod_pow, <- Cmod_mult. }
Qed.

(** C power series projection (when point x is a Real) *)

Lemma is_CPowerSeries_proj (a:nat->C)(x:R) :
  ex_pseries (Cmod∘a) (Rabs x) ->
  is_CPowerSeries a x (PSeries (Re∘a) x, PSeries (Im∘a) x).
Proof.
 intros H.
 unfold is_CPowerSeries. rewrite is_lim_Cseq_proj. simpl. split.
 - eapply is_lim_seq_ext with (u:=sum_n (fun k => (Re∘a) k * x^k)%R).
   { intros n. unfold compose. rewrite re_sum_n. apply sum_n_ext.
     clear n. intros n. unfold compose.
     now rewrite <- re_scal_r, <- RtoC_pow. }
   unfold PSeries, Series. apply Lim_seq_correct'. rewrite <- ex_series_alt.
   eapply (ex_series_le (V:=R_CNM)); eauto.
   { intros n. change norm with Rabs.
     rewrite Rabs_mult. unfold compose. rewrite RPow_abs.
     change scal with Rmult. rewrite Rmult_comm.
     apply Rmult_le_compat_l. apply Rabs_pos. apply re_le_Cmod. }
 - eapply is_lim_seq_ext with (u:=sum_n (fun k => (Im∘a) k * x^k)%R).
   { intros n. unfold compose. rewrite im_sum_n. apply sum_n_ext.
     clear n. intros n. unfold compose.
     now rewrite <- im_scal_r, <- RtoC_pow. }
   unfold PSeries, Series. apply Lim_seq_correct'. rewrite <- ex_series_alt.
   eapply (ex_series_le (V:=R_CNM)); eauto.
   { intros n. change norm with Rabs.
     rewrite Rabs_mult. unfold compose. rewrite RPow_abs.
     change scal with Rmult. rewrite Rmult_comm.
     apply Rmult_le_compat_l. apply Rabs_pos. apply im_le_Cmod. }
Qed.

Lemma CPowerSeries_proj (a:nat->C)(x:R) :
  ex_pseries (Cmod∘a) (Rabs x) ->
  CPowerSeries a x = (PSeries (Re∘a) x, PSeries (Im∘a) x).
Proof.
 intros. now apply CPowerSeries_unique, is_CPowerSeries_proj.
Qed.

(** Unicity of coefficients of C power series *)

Lemma CPowerSeries_coef_ext (a b : nat -> C) :
 Rbar.Rbar_lt R0 (C_CV_radius a) ->
 Rbar.Rbar_lt R0 (C_CV_radius b) ->
 locally R0 (fun x:R => CPowerSeries a x = CPowerSeries b x) ->
 forall n, a n = b n.
Proof.
 intros Ha Hb E n.
 rewrite (surjective_pairing (a n)), (surjective_pairing (b n)).
 assert (L: locally R0 (fun x : R => PSeries (Re ∘ a) x = PSeries (Re ∘ b) x
                                 /\ PSeries (Im ∘ a) x = PSeries (Im ∘ b) x)).
 { destruct E as (eps & E).
   set (ra := match C_CV_radius a with Rbar.Finite r => r | _ => 1%R end).
   assert (Ra : 0 < ra).
   { unfold ra. destruct (C_CV_radius a); try easy. lra. }
   set (rb := match C_CV_radius b with Rbar.Finite r => r | _ => 1%R end).
   assert (Rb : 0 < rb).
   { unfold rb. destruct (C_CV_radius b); try easy. lra. }
   assert (LT : 0 < Rmin eps (Rmin ra rb)).
   { apply Rmin_glb_lt. apply eps. now apply Rmin_glb_lt. }
   set (eps' := mkposreal _ LT).
   exists eps'. intros y Y. change (Rabs (y-0) < eps') in Y.
   assert (Y0 : Rabs (y - 0) < eps).
   { apply Rlt_le_trans with eps'; trivial. apply Rmin_l. }
   specialize (E y Y0). clear Y0.
   rewrite !CPowerSeries_proj in E; trivial; try lra.
   + now injection E.
   + clear E Ha. clearbody ra.
     rewrite Rminus_0_r in Y.
     assert (ex_pseries (Cmod∘b) (Rabs y)).
     { apply CV_radius_inside. rewrite Rabs_Rabsolu.
       rewrite <- C_CV_radius_alt.
       apply Rbar.Rbar_lt_le_trans with eps'; trivial.
       apply Rbar.Rbar_le_trans with (Rmin ra rb); [apply Rmin_r|].
       apply Rbar.Rbar_le_trans with rb; [apply Rmin_r|].
       unfold rb. destruct C_CV_radius; simpl; trivial; lra. }
     red in H. eapply ex_series_ext; eauto.
     intros k. unfold compose. unfold scal. simpl.
     change mult with Rmult.
     rewrite pow_n_pow. ring.
   + clear E Hb. clearbody rb.
     rewrite Rminus_0_r in Y.
     assert (ex_pseries (Cmod∘a) (Rabs y)).
     { apply CV_radius_inside. rewrite Rabs_Rabsolu.
       rewrite <- C_CV_radius_alt.
       apply Rbar.Rbar_lt_le_trans with eps'; trivial.
       apply Rbar.Rbar_le_trans with (Rmin ra rb); [apply Rmin_r|].
       apply Rbar.Rbar_le_trans with ra; [apply Rmin_l|].
       unfold ra. destruct C_CV_radius; simpl; trivial; lra. }
     red in H. eapply ex_series_ext; eauto.
     intros k. unfold compose. unfold scal. simpl.
     change mult with Rmult.
     rewrite pow_n_pow. ring. }
 f_equal.
 - apply (PSeries_ext_recip (Re∘a) (Re∘b) n).
   + apply Rbar.Rbar_lt_le_trans with (C_CV_radius a); auto.
     rewrite C_CV_radius_alt.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply re_le_Cmod.
   + apply Rbar.Rbar_lt_le_trans with (C_CV_radius b); auto.
     rewrite C_CV_radius_alt.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply re_le_Cmod.
   + destruct L as (eps & L). exists eps. apply L.
 - apply (PSeries_ext_recip (Im∘a) (Im∘b) n).
   + apply Rbar.Rbar_lt_le_trans with (C_CV_radius a); auto.
     rewrite C_CV_radius_alt.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply im_le_Cmod.
   + apply Rbar.Rbar_lt_le_trans with (C_CV_radius b); auto.
     rewrite C_CV_radius_alt.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply im_le_Cmod.
   + destruct L as (eps & L). exists eps. apply L.
Qed.

(** Addition and multiplication of C power series *)

Definition CPS_plus : (nat->C) -> (nat->C) -> (nat->C) := PS_plus (V:=C_NM).
Definition CPS_mult (a b : nat->C) (n:nat) : C :=
  sum_n (fun k => a k * b (n - k)%nat) n.

Lemma CPS_mult_eqn a b n :
 CPS_mult a b n = (PS_mult (Re∘a) (Re∘b) n - PS_mult (Im∘a) (Im∘b) n,
                   PS_mult (Re∘a) (Im∘b) n + PS_mult (Im∘a) (Re∘b) n)%R.
Proof.
 unfold CPS_mult, PS_mult.
 rewrite <- !sum_n_Reals.
 rewrite sum_n_proj; f_equal.
 - unfold "∘". simpl. rewrite sum_n_Rminus. now apply sum_n_ext.
 - unfold "∘". simpl. rewrite sum_n_Rplus. now apply sum_n_ext.
Qed.

Lemma CPS_mult_scal (a b : nat -> C) (z : C) n :
  CPS_mult (fun k : nat => scal (pow_n z k) (a k))
           (fun k : nat => scal (pow_n z k) (b k)) n =
  scal (pow_n z n) (CPS_mult a b n).
Proof.
 unfold CPS_mult, PS_mult.
 change pow_n with Cpow. change scal with Cmult.
 rewrite <- sum_n_Cmult_l. apply sum_n_ext_loc.
 intros k Hk. replace n with (k+(n-k))%nat at 3 by lia.
 rewrite Cpow_add_r. fixeq C. ring.
Qed.

Lemma is_CPS_plus (a b : nat->C) (z la lb : C) :
  is_CPowerSeries a z la -> is_CPowerSeries b z lb
    -> is_CPowerSeries (CPS_plus a b) z (la+lb).
Proof.
 rewrite !is_CPowerSeries_alt. apply (is_pseries_plus a b).
Qed.

Lemma ex_CPS_plus (a b : nat->C) (z : C) :
  ex_CPowerSeries a z -> ex_CPowerSeries b z
    -> ex_CPowerSeries (CPS_plus a b) z.
Proof.
 rewrite !ex_CPowerSeries_alt. apply (ex_pseries_plus a b).
Qed.

Lemma CPowerSeries_plus (a b : nat -> C) (z : C) :
  ex_CPowerSeries a z -> ex_CPowerSeries b z ->
  CPowerSeries (CPS_plus a b) z = CPowerSeries a z + CPowerSeries b z.
Proof.
 intros (la,Ha) (lb,Hb).
 rewrite (CPowerSeries_unique _ _ _ Ha), (CPowerSeries_unique _ _ _ Hb).
 now apply CPowerSeries_unique, is_CPS_plus.
Qed.

Lemma C_CV_disk_plus (a b : nat -> C) (z : C) :
 C_CV_disk a z -> C_CV_disk b z -> C_CV_disk (CPS_plus a b) z.
Proof.
 intros Ha Hb.
 rewrite C_CV_disk_alt in *.
 unfold CPS_plus.
 assert (Hc := CV_disk_plus _ _ _ Ha Hb).
 red. red in Hc.
 eapply (ex_series_le (V:=R_CNM)); eauto.
 intros n. change norm with Rabs. simpl. rewrite Rabs_Rabsolu.
 rewrite !Rabs_mult. apply Rmult_le_compat_r. apply Rabs_pos.
 unfold "∘". unfold PS_plus.
 change plus with Cplus at 1. change plus with Rplus at 1.
 rewrite !Rabs_pos_eq. apply Cmod_triangle.
 generalize (Cmod_ge_0 (a n)), (Cmod_ge_0 (b n)); lra.
 apply Cmod_ge_0.
Qed.

Lemma C_CV_radius_plus (a b : nat -> C) :
  Rbar.Rbar_le (Rbar.Rbar_min (C_CV_radius a) (C_CV_radius b))
               (C_CV_radius (CPS_plus a b)).
Proof.
 apply Rbar_le_carac_via_lt.
 intros c Hc.
 assert (Ha : Rbar.Rbar_lt c (C_CV_radius a)).
 { generalize Hc. apply Rbar.Rbar_min_case_strong; trivial.
   intros. eapply Rbar.Rbar_lt_le_trans; eauto. }
 assert (Hb : Rbar.Rbar_lt c (C_CV_radius b)).
 { generalize Hc. apply Rbar.Rbar_min_case_strong; trivial.
   intros. eapply Rbar.Rbar_lt_le_trans; eauto. }
 clear Hc.
 destruct (Rle_lt_dec 0 c).
 - replace c with (Cmod c) in Ha, Hb.
   2:{ rewrite Cmod_R, Rabs_pos_eq; trivial. }
   apply C_CV_radius_inside in Ha,Hb.
   rewrite C_CV_radius_radius'.
   apply Lub_Rbar_ub. exists c.
   split. rewrite Cmod_R, Rabs_pos_eq; trivial.
   now apply ex_CPS_plus.
 - apply Rbar.Rbar_le_trans with 0%R. simpl; lra.
   rewrite C_CV_radius_alt. apply CV_radius_ge_0.
Qed.

Lemma is_pseries_1 (a : nat -> R) (l : R) :
 is_pseries a 1%R l <-> is_series a l.
Proof.
 unfold is_pseries. change pow_n with pow. change scal with Rmult.
 split; apply is_series_ext; intros n; rewrite pow1; lra.
Qed.

(** NB: is_series_mult coud have weaker preconditions, see Mertens thm. *)

Lemma is_series_mult (a b : nat -> C) (la lb : C) :
 Rbar.Rbar_lt 1%R (C_CV_radius a) ->
 Rbar.Rbar_lt 1%R (C_CV_radius b) ->
 is_series a la -> is_series b lb ->
 is_series (CPS_mult a b) (la * lb).
Proof.
 intros Ha0 Hb0 Ha Hb. rewrite is_Cseries_alt, is_lim_Cseq_proj.
 unfold "∘".
 rewrite C_CV_radius_alt, <- (Rabs_pos_eq 1) in Ha0, Hb0 by lra.
 assert (Ra : Rbar.Rbar_lt (Rabs 1) (CV_radius (Re ∘ a))).
 { eapply Rbar.Rbar_lt_le_trans; [ apply Ha0 | ].
   apply CV_radius_le. intros n. unfold "∘". rewrite re_le_Cmod.
   rewrite Rabs_pos_eq by apply Cmod_ge_0. lra. }
 assert (Rb : Rbar.Rbar_lt (Rabs 1) (CV_radius (Re ∘ b))).
 { eapply Rbar.Rbar_lt_le_trans; [ apply Hb0 | ].
   apply CV_radius_le. intros n. unfold "∘". rewrite re_le_Cmod.
   rewrite Rabs_pos_eq by apply Cmod_ge_0. lra. }
 assert (Ia : Rbar.Rbar_lt (Rabs 1) (CV_radius (Im ∘ a))).
 { eapply Rbar.Rbar_lt_le_trans; [ apply Ha0 | ].
   apply CV_radius_le. intros n. unfold "∘". rewrite im_le_Cmod.
   rewrite Rabs_pos_eq by apply Cmod_ge_0. lra. }
 assert (Ib : Rbar.Rbar_lt (Rabs 1) (CV_radius (Im ∘ b))).
 { eapply Rbar.Rbar_lt_le_trans; [ apply Hb0 | ].
   apply CV_radius_le. intros n. unfold "∘". rewrite im_le_Cmod.
   rewrite Rabs_pos_eq by apply Cmod_ge_0. lra. }
 split.
 - eapply is_lim_seq_ext.
   { intros n. symmetry. rewrite re_sum_n. unfold "∘".
     erewrite sum_n_ext.
     2:{ intros k. rewrite CPS_mult_eqn. now simpl. }
     symmetry. apply sum_n_Rminus. }
   simpl Re. apply is_lim_seq_minus'; rewrite <- is_series_alt.
   + rewrite <- is_pseries_1.
     apply is_pseries_mult; try rewrite is_pseries_1; trivial.
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Ha.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Ha.
       apply re_sum_n. }
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Hb.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Hb.
       apply re_sum_n. }
   + rewrite <- is_pseries_1.
     apply is_pseries_mult; try rewrite is_pseries_1; trivial.
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Ha.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Ha.
       apply im_sum_n. }
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Hb.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Hb.
       apply im_sum_n. }
 - eapply is_lim_seq_ext.
   { intros n. symmetry. rewrite im_sum_n. unfold "∘".
     erewrite sum_n_ext.
     2:{ intros k. rewrite CPS_mult_eqn. now simpl. }
     symmetry. apply sum_n_Rplus. }
   simpl Im. apply is_lim_seq_plus'; rewrite <- is_series_alt.
   + rewrite <- is_pseries_1.
     apply is_pseries_mult; try rewrite is_pseries_1; trivial.
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Ha.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Ha.
       apply re_sum_n. }
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Hb.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Hb.
       apply im_sum_n. }
   + rewrite <- is_pseries_1.
     apply is_pseries_mult; try rewrite is_pseries_1; trivial.
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Ha.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Ha.
       apply im_sum_n. }
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Hb.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Hb.
       apply re_sum_n. }
Qed.

Lemma CV_radius_scal (a : nat -> R) (r : R) :
 0 < r ->
 CV_radius (fun n => scal (pow_n r n) (a n)) =
 Rbar.Rbar_mult (/r)%R (CV_radius a).
Proof.
 intros Hr.
 set (b := fun n => _).
 apply Lub.is_lub_Rbar_unique. unfold CV_disk.
 split.
 - intros x Hx.
   apply Rbar_le_mult_div; trivial.
   apply CV_disk_le_radius. red.
   eapply ex_series_ext; eauto.
   intros n. simpl. f_equal. unfold b.
   change scal with Rmult. change pow_n with pow.
   rewrite Rpow_mult_distr. ring.
 - intros l Hl. red in Hl.
   assert (Hr' : 0 < /r) by now apply Rinv_0_lt_compat.
   apply Rbar_le_mult_div; trivial.
   destruct (Lub.Lub_Rbar_correct (CV_disk a)) as (H1,H2).
   fold (CV_radius a) in H1,H2.
   red in H1. unfold CV_disk in H1.
   apply H2. red. intros x Hx. red in Hx.
   rewrite <- Rbar_le_mult_div; trivial.
   apply Hl.
   eapply ex_series_ext; eauto.
   intros n. simpl. f_equal. unfold b.
   change scal with Rmult. change pow_n with pow.
   rewrite Rpow_mult_distr, pow_inv. field. apply pow_nonzero. lra.
Qed.

Lemma CV_radius_scal_lt (a : nat -> R) (r : R) :
 0 < r ->
 Rbar.Rbar_lt r (CV_radius a) ->
 Rbar.Rbar_lt 1%R (CV_radius (fun n => scal (pow_n r n) (a n))).
Proof.
 intros Hr LT.
 rewrite CV_radius_scal; trivial.
 rewrite <- Rbar_lt_mult_div; trivial. simpl Rbar.Rbar_mult.
 rewrite Rmult_1_r; trivial.
Qed.

Lemma is_CPS_mult (a b : nat -> C) (z la lb : C) :
  is_CPowerSeries a z la -> is_CPowerSeries b z lb
  -> Rbar.Rbar_lt (Cmod z) (C_CV_radius a)
  -> Rbar.Rbar_lt (Cmod z) (C_CV_radius b)
  -> is_CPowerSeries (CPS_mult a b) z (la * lb).
Proof.
 intros Ha Hb Ha' Hb'.
 destruct (Ceq_dec z 0) as [->|Hz].
 { replace la with (a O).
   2:{ apply CPowerSeries_unique in Ha. rewrite <- Ha.
       symmetry. apply CPowerSeries_unique.
       rewrite is_CPowerSeries_alt.
       apply (is_pseries_0 a). }
   replace lb with (b O).
   2:{ apply CPowerSeries_unique in Hb. rewrite <- Hb.
       symmetry. apply CPowerSeries_unique.
       rewrite is_CPowerSeries_alt.
       apply (is_pseries_0 b). }
   replace (a O * b O) with (CPS_mult a b 0).
   2:{ unfold CPS_mult, PS_mult. now rewrite sum_O. }
   rewrite is_CPowerSeries_alt.
   apply (is_pseries_0 (CPS_mult a b)). }
 rewrite is_CPowerSeries_alt.
 unfold is_pseries.
 eapply is_series_ext; [ apply CPS_mult_scal | ].
 apply is_series_mult; try now rewrite is_CPowerSeries_alt in *.
 - rewrite C_CV_radius_alt in *.
   erewrite CV_radius_ext.
   apply (CV_radius_scal_lt (Cmod∘a)); eauto.
   now apply Cmod_gt_0.
   intros k. unfold "∘".
   change (Cmod (z^k * a k) = Cmod z^k * Cmod (a k))%R.
   now rewrite <- Cmod_pow, <- Cmod_mult.
 - rewrite C_CV_radius_alt in *.
   erewrite CV_radius_ext.
   apply (CV_radius_scal_lt (Cmod∘b)); eauto.
   now apply Cmod_gt_0.
   intros k. unfold "∘".
   change (Cmod (z^k * b k) = Cmod z^k * Cmod (b k))%R.
   now rewrite <- Cmod_pow, <- Cmod_mult.
Qed.

Lemma ex_CPS_mult (a b : nat -> C) (z : C) :
  Rbar.Rbar_lt (Cmod z) (C_CV_radius a) ->
  Rbar.Rbar_lt (Cmod z) (C_CV_radius b) ->
  ex_CPowerSeries (CPS_mult a b) z.
Proof.
 intros Ha Hb.
 exists ((CPowerSeries a z) * (CPowerSeries b z)).
 apply is_CPS_mult; trivial.
 - apply CPowerSeries_correct. now apply C_CV_radius_inside.
 - apply CPowerSeries_correct. now apply C_CV_radius_inside.
Qed.

Lemma CPowerSeries_mult (a b : nat -> C) (z : C) :
  Rbar.Rbar_lt (Cmod z) (C_CV_radius a) ->
  Rbar.Rbar_lt (Cmod z) (C_CV_radius b) ->
  CPowerSeries (CPS_mult a b) z = CPowerSeries a z * CPowerSeries b z.
Proof.
 intros Ha Hb.
 apply CPowerSeries_unique, is_CPS_mult; trivial.
 - apply CPowerSeries_correct. now apply C_CV_radius_inside.
 - apply CPowerSeries_correct. now apply C_CV_radius_inside.
Qed.

Lemma C_CV_radius_mult (a b : nat -> C) :
  Rbar.Rbar_le (Rbar.Rbar_min (C_CV_radius a) (C_CV_radius b))
               (C_CV_radius (CPS_mult a b)).
Proof.
 apply Rbar_le_carac_via_lt.
 intros c Hc.
 assert (Ha : Rbar.Rbar_lt c (C_CV_radius a)).
 { generalize Hc. apply Rbar.Rbar_min_case_strong; trivial.
   intros. eapply Rbar.Rbar_lt_le_trans; eauto. }
 assert (Hb : Rbar.Rbar_lt c (C_CV_radius b)).
 { generalize Hc. apply Rbar.Rbar_min_case_strong; trivial.
   intros. eapply Rbar.Rbar_lt_le_trans; eauto. }
 clear Hc.
 destruct (Rle_lt_dec 0 c).
 - replace c with (Cmod c) in Ha, Hb.
   2:{ rewrite Cmod_R, Rabs_pos_eq; trivial. }
   rewrite C_CV_radius_radius'.
   apply Lub_Rbar_ub. exists c.
   split. rewrite Cmod_R, Rabs_pos_eq; trivial.
   now apply ex_CPS_mult.
 - apply Rbar.Rbar_le_trans with 0%R. simpl; lra.
   rewrite C_CV_radius_alt. apply CV_radius_ge_0.
Qed.

(** Power series and polynomial *)

Definition PS_poly (P:Polynomial) := fun n => coef n P.

Lemma PS_poly_ok (P:Polynomial) z :
  is_CPowerSeries (PS_poly P) z (Peval P z).
Proof.
 red. apply is_lim_Cseq_ext_loc with (fun _ => Peval P z).
 2:apply is_lim_Cseq_const.
 exists (length P); intros n Hn. unfold PS_poly, coef.
 unfold Peval.
 rewrite <- big_sum_sum_n.
 replace (S n) with (length P + (S n - length P))%nat by lia.
 rewrite big_sum_sum.
 rewrite <- (Cplus_0_r (big_sum _ _)) at 1.
 change Gplus with Cplus. f_equal. symmetry.
 apply (@big_sum_0 C). intros x.
 change Gzero with 0.
 rewrite nth_overflow; try lca. lia.
Qed.

Lemma PS_poly_radius p : C_CV_radius (PS_poly p) = Rbar.p_infty.
Proof.
 assert (H : forall x, Rbar.Rbar_le (Cmod x) (C_CV_radius (PS_poly p))).
 { intros x. rewrite C_CV_radius_radius'. apply Lub_Rbar_ub.
   exists x; split; trivial. eexists. apply PS_poly_ok. }
 destruct (C_CV_radius (PS_poly p)) as [x | | ]; trivial; exfalso.
 - specialize (H (Rabs x + 1)%R). simpl in H.
   rewrite Cmod_R in H.
   destruct (Rle_lt_dec 0 x).
   + rewrite !Rabs_pos_eq in H; try (generalize (Rabs_pos x); lra).
   + generalize (Rabs_pos (Rabs x + 1)); lra.
 - apply (H 0).
Qed.

Definition PS_one n := match n with O => 1 | _ => 0 end.

Lemma PS_one_ok z : is_CPowerSeries PS_one z 1.
Proof.
 red. apply is_lim_Cseq_ext_loc with (fun _ => 1).
 2:apply is_lim_Cseq_const.
 exists 1%nat. intros [|n] Hn; try lia.
 rewrite <- big_sum_sum_n.
 replace (S (S n)) with (1+S n)%nat by lia.
 rewrite big_sum_sum. simpl. ring_simplify.
 rewrite (@big_sum_0 C); intros; lca.
Qed.

Lemma C_CV_radius_one : C_CV_radius PS_one = Rbar.p_infty.
Proof.
 assert (H : forall x, Rbar.Rbar_le (Cmod x) (C_CV_radius PS_one)).
 { intros x. rewrite C_CV_radius_radius'. apply Lub_Rbar_ub.
   exists x; split; trivial. exists 1. apply PS_one_ok. }
 destruct (C_CV_radius PS_one) as [x | | ]; trivial; exfalso.
 - specialize (H (Rabs x + 1)%R). simpl in H.
   rewrite Cmod_R in H.
   destruct (Rle_lt_dec 0 x).
   + rewrite !Rabs_pos_eq in H; try (generalize (Rabs_pos x); lra).
   + generalize (Rabs_pos (Rabs x + 1)); lra.
 - apply (H 0).
Qed.

Definition PS_inv_linfactors (l:list C) :=
  fold_right (fun r => CPS_mult (PS_opp (PS_geom (/r)))) PS_one l.

Lemma C_CV_radius_opp (a : nat -> C) :
  C_CV_radius (PS_opp a) = C_CV_radius a.
Proof.
 rewrite !C_CV_radius_alt. apply CV_radius_ext.
 intros n. apply Cmod_opp.
Qed.

Lemma C_CV_radius_geom (r:C) : r<>0 ->
 C_CV_radius (PS_geom r) = (/Cmod r)%R.
Proof.
 intros Hr.
 rewrite C_CV_radius_alt.
 apply CV_radius_finite_DAlembert.
 - intros n. unfold "∘", PS_geom.
   rewrite Cmod_pow. apply pow_nonzero.
   rewrite (Cmod_gt_0 r) in Hr. lra.
 - now apply Cmod_gt_0.
 - unfold "∘", PS_geom.
   eapply is_lim_seq_ext; try apply is_lim_seq_const.
   intros n; simpl. rewrite Cmod_mult.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_r.
   + now rewrite Rmult_1_r, Rabs_pos_eq by apply Cmod_ge_0.
   + change (Cmod (r^S n) <> 0)%R.
     rewrite Cmod_pow. apply pow_nonzero.
     rewrite (Cmod_gt_0 r) in Hr. lra.
Qed.

Definition Rbar_minlist (l : list Rbar.Rbar) :=
  fold_right Rbar.Rbar_min Rbar.p_infty l.

Definition min_Cmod_list (l : list C) :=
  Rbar_minlist (map (fun r => Rbar.Finite (Cmod r)) l).

Lemma min_Cmod_cons z l :
  min_Cmod_list (z::l) = Rbar.Rbar_min (Cmod z) (min_Cmod_list l).
Proof.
 easy.
Qed.

Lemma min_Cmod_list_spec (x:R) l :
 Rbar.Rbar_lt x (min_Cmod_list l) <-> Forall (fun r => x < Cmod r) l.
Proof.
 induction l.
 - simpl. split; constructor.
 - rewrite min_Cmod_cons. split; intros H.
   + constructor.
     * change (Rbar.Rbar_lt x (Cmod a)).
       eapply Rbar.Rbar_lt_le_trans; eauto. apply Rbar.Rbar_min_l.
     * apply IHl.
       eapply Rbar.Rbar_lt_le_trans; eauto. apply Rbar.Rbar_min_r.
   + inversion_clear H. apply Rbar.Rbar_min_case; trivial.
     now apply IHl.
Qed.

Lemma PS_inv_linfactors_radius (l : list C) :
  ~In 0 l ->
  Rbar.Rbar_le (min_Cmod_list l) (C_CV_radius (PS_inv_linfactors l)).
Proof.
 induction l.
 - intros _; simpl; now rewrite C_CV_radius_one.
 - rewrite min_Cmod_cons.
   cbn -[Rbar.Rbar_min]. intros H.
   eapply Rbar.Rbar_le_trans; [| apply C_CV_radius_mult].
   remember (Rbar.Rbar_min _ _) as x.
   apply Rbar.Rbar_min_case; subst x;
     [ eapply Rbar.Rbar_le_trans; try apply Rbar.Rbar_min_l
     | eapply Rbar.Rbar_le_trans; try apply Rbar.Rbar_min_r ].
   + rewrite C_CV_radius_opp, C_CV_radius_geom.
     * rewrite Cmod_inv, Rinv_inv. apply Rbar.Rbar_le_refl.
     * apply nonzero_div_nonzero. tauto.
   + apply IHl; tauto.
Qed.

Lemma PS_inv_linfactors_ok l z :
  Forall (fun r => Cmod z < Cmod r) l ->
  is_CPowerSeries (PS_inv_linfactors l) z (/ Peval (linfactors l) z).
Proof.
 induction l.
 - intros _. simpl. rewrite Pconst_eval, Cinv_1. apply PS_one_ok.
 - inversion_clear 1. simpl. rewrite Pmult_eval, Cinv_mult.
   assert (Ha : a <> 0).
   { apply Cmod_gt_0. generalize (Cmod_ge_0 z); lra. }
   assert (Ha' : /a <> 0).
   { now apply nonzero_div_nonzero. }
   replace (Peval [-a;1] z) with (z-a).
   2:{ unfold Peval. simpl. ring. }
   rewrite Cmult_comm.
   apply is_CPS_mult; auto.
   + replace (/(z-a)) with (opp (/(a-z))).
     2:{ change opp with Copp. fixeq C. rewrite <- Cinv_Copp. f_equal. ring. }
     rewrite <- (Cinv_inv a) at 2.
     rewrite is_CPowerSeries_alt.
     apply (@is_pseries_opp C_AbsRing).
     rewrite <- is_CPowerSeries_alt.
     apply is_powerseries_invlin; trivial.
     rewrite Cmod_mult, Cmod_inv. apply Cmod_gt_0 in Ha.
     rewrite <- (Rinv_l (Cmod a)) by lra. apply Rmult_lt_compat_l; trivial.
     now apply Rinv_0_lt_compat.
   + rewrite C_CV_radius_opp, C_CV_radius_geom; trivial.
     simpl. now rewrite Cmod_inv, Rinv_inv.
   + eapply Rbar.Rbar_lt_le_trans.
     2:{ apply PS_inv_linfactors_radius.
         intros IN. rewrite Forall_forall in H1. specialize (H1 0 IN).
         rewrite Cmod_0 in H1. generalize (Cmod_ge_0 z); lra. }
     now apply min_Cmod_list_spec.
Qed.
