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

Global Instance is_lim_seq_proper :
  Proper (pointwise_relation _ eq ==> eq ==> iff) is_lim_seq.
Proof.
 intros f f' Hf l l' <-. split; apply is_lim_seq_ext.
 now apply Hf. intro. symmetry. apply Hf.
Qed.

Global Instance ex_lim_seq_proper :
  Proper (pointwise_relation _ eq ==> iff) ex_lim_seq.
Proof.
 intros f f' Hf. split; apply ex_lim_seq_ext.
 now apply Hf. intro. symmetry. apply Hf.
Qed.

Global Instance Lim_seq_proper :
  Proper (pointwise_relation _ eq ==> eq) Lim_seq.
Proof.
 intros f f' Hf. apply Lim_seq_ext. now apply Hf.
Qed.

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
     - unfold a. setoid_rewrite simpl_fact.
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

Global Instance is_series_proper {K} {V : NormedModule K} :
  Proper (pointwise_relation _ eq ==> eq ==> iff) (@is_series K V).
Proof.
 intros f f' Hf l l' <-. split; apply is_series_ext.
 apply Hf. intros n. symmetry. apply Hf.
Qed.

Global Instance ex_series_proper {K} {V : NormedModule K} :
  Proper (pointwise_relation _ eq ==> iff) (@ex_series K V).
Proof.
 intros f f' Hf. split; apply ex_series_ext.
 apply Hf. intros n. symmetry. apply Hf.
Qed.

Global Instance Series_proper :
  Proper (pointwise_relation _ eq ==> eq) Series.
Proof.
 intros f f' Hf. apply Series_ext. apply Hf.
Qed.

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
 - intros. simpl. exists 0%R. apply is_series_R0.
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
 intros E. rewrite !is_lim_Cseq_proj. intros (Hf,Hg).
 split; unfold "∘"; now setoid_rewrite <- E.
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

Lemma ex_lim_Cseq_ext (u v : nat -> C) :
  (forall n : nat, u n = v n) ->
  ex_lim_Cseq u -> ex_lim_Cseq v.
Proof.
 intros E (l & H). exists l. eapply is_lim_Cseq_ext; eauto.
Qed.

Lemma LimSup_ext (u v : nat -> R) :
  Hierarchy.eventually (fun n : nat => u n = v n) ->
  LimSup_seq u = LimSup_seq v.
Proof.
 intros H.
 apply Rbar.Rbar_le_antisym; apply LimSup_le.
 - destruct H as (N & HN). exists N. intros n Hn. now rewrite HN.
 - destruct H as (N & HN). exists N. intros n Hn. now rewrite HN.
Qed.

Lemma LimInf_ext (u v : nat -> R) :
  Hierarchy.eventually (fun n : nat => u n = v n) ->
  LimInf_seq u = LimInf_seq v.
Proof.
 intros H.
 apply Rbar.Rbar_le_antisym; apply LimInf_le.
 - destruct H as (N & HN). exists N. intros n Hn. now rewrite HN.
 - destruct H as (N & HN). exists N. intros n Hn. now rewrite HN.
Qed.

Lemma LimSeq_ext (u v : nat -> R) :
  Hierarchy.eventually (fun n : nat => u n = v n) ->
  Lim_seq u = Lim_seq v.
Proof.
 intros H. unfold Lim_seq.
 now rewrite (LimInf_ext _ _ H), (LimSup_ext _ _ H).
Qed.

Lemma Lim_CSeq_ext (u v : nat -> C) :
  Hierarchy.eventually (fun n : nat => u n = v n) ->
  Lim_Cseq u = Lim_Cseq v.
Proof.
 intros H. unfold Lim_Cseq. f_equal; f_equal; apply LimSeq_ext.
 - destruct H as (N & HN). exists N. intros n Hn. unfold "∘". now rewrite HN.
 - destruct H as (N & HN). exists N. intros n Hn. unfold "∘". now rewrite HN.
Qed.

Global Instance is_lim_Cseq_proper :
  Proper (pointwise_relation _ eq ==> eq ==> iff) is_lim_Cseq.
Proof.
 intros f f' Hf l l' <-. split; apply is_lim_Cseq_ext.
 now apply Hf. intro. symmetry. apply Hf.
Qed.

Global Instance ex_lim_Cseq_proper :
  Proper (pointwise_relation _ eq ==> iff) ex_lim_Cseq.
Proof.
 intros f f' Hf. split; apply ex_lim_Cseq_ext.
 now apply Hf. intro. symmetry. apply Hf.
Qed.

Global Instance Lim_Cseq_proper :
  Proper (pointwise_relation _ eq ==> eq) Lim_Cseq.
Proof.
 intros f f' Hf. apply Lim_CSeq_ext. exists O. intros n _. now apply Hf.
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
 rewrite is_lim_Cseq_proj. split; apply is_lim_seq_const.
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
 - unfold "∘". setoid_rewrite re_plus. now apply is_lim_seq_plus'.
 - unfold "∘". setoid_rewrite im_plus. now apply is_lim_seq_plus'.
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
 rewrite !is_lim_Cseq_proj. intros (Ha1,Ha2) (Hb1,Hb2).
 split; unfold "∘", Cminus.
 - srewrite re_plus re_opp. now apply is_lim_seq_minus'.
 - srewrite im_plus im_opp. now apply is_lim_seq_minus'.
Qed.

Lemma is_lim_Cseq_mult (a b : nat -> C) (la lb : C) :
 is_lim_Cseq a la -> is_lim_Cseq b lb ->
 is_lim_Cseq (fun n => a n * b n) (la * lb).
Proof.
 rewrite !is_lim_Cseq_proj. intros (Ha1,Ha2) (Hb1,Hb2).
 split; unfold "∘".
 - setoid_rewrite re_mult.
   apply is_lim_seq_minus'; now apply is_lim_seq_mult'.
 - setoid_rewrite im_mult.
   apply is_lim_seq_plus'; now apply is_lim_seq_mult'.
Qed.

Lemma is_lim_Cseq_incr_n (u : nat -> C) (N : nat) l :
  is_lim_Cseq u l <-> is_lim_Cseq (fun n : nat => u (n + N)%nat) l.
Proof.
 rewrite !is_lim_Cseq_proj.
 rewrite (is_lim_seq_incr_n (Re∘_) N).
 rewrite (is_lim_seq_incr_n (Im∘_) N). easy.
Qed.

Lemma ex_lim_Cseq_incr_n (u : nat -> C) (N : nat) :
  ex_lim_Cseq u <-> ex_lim_Cseq (fun n : nat => u (n + N)%nat).
Proof.
 split; intros (l & H); exists l; revert H; now apply is_lim_Cseq_incr_n.
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

Lemma ex_Cseries_alt (a : nat -> C) :
  ex_series a <-> ex_lim_Cseq (sum_n a).
Proof.
 split; intros (l & H); exists l; revert H; apply is_Cseries_alt.
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

Lemma CSeries_ext (u v : nat -> C) :
  (forall n, u n = v n) -> CSeries u = CSeries v.
Proof.
 intros H. unfold CSeries. apply Lim_CSeq_ext. exists O.
 intros n _. apply sum_n_ext; trivial.
Qed.

Global Instance CSeries_proper :
  Proper (pointwise_relation _ eq ==> eq) CSeries.
Proof.
 intros f f' Hf. apply CSeries_ext. now apply Hf.
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

Lemma is_series_null (a : nat -> R) :
 is_series a 0%R -> (forall n : nat, 0 <= a n) -> forall n : nat, a n = 0%R.
Proof.
 intros H1 H2.
 assert (H3 := pos_series_pos_sum _ _ H1 H2).
 assert (H4 : forall n, 0 <= sum_n a n).
 { intros n. rewrite <- (sum_n_R0 n). now apply sum_n_le. }
 intros [|n].
 - rewrite <- sum_O. generalize (H3 O) (H4 O); lra.
 - specialize (H3 (S n)). rewrite sum_Sn in H3. change plus with Rplus in H3.
   generalize (H2 (S n)) (H4 n); lra.
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

Lemma is_CSeries_RtoC_impl (a : nat -> R) (l:C) :
  is_series (RtoC∘a) l -> is_series a (Re l) /\ Im l = 0%R.
Proof.
 intros H.
 change (is_lim_Cseq (sum_n (RtoC∘a)) l) in H.
 rewrite is_lim_Cseq_proj in H. destruct H as (H1,H2).
 unfold "∘" in *.
 setoid_rewrite re_sum_n in H1. setoid_rewrite im_sum_n in H2.
 unfold "∘" in *. simpl in H2.
 setoid_rewrite sum_n_R0 in H2.
 split. apply H1.
 apply is_lim_seq_unique in H2. rewrite Lim_seq_const in H2.
 now injection H2.
Qed.

Lemma is_CSeries_RtoC (a : nat -> R) (l:R) :
  is_series (RtoC∘a) (RtoC l) <-> is_series a l.
Proof.
 split.
 - intros H. change l with (Re (RtoC l)). now apply is_CSeries_RtoC_impl.
 - intros H.
   change (is_lim_Cseq (sum_n (RtoC∘a)) l).
   rewrite is_lim_Cseq_proj; simpl. split; unfold "∘".
   + now setoid_rewrite re_sum_n.
   + setoid_rewrite im_sum_n. unfold "∘". simpl.
     setoid_rewrite sum_n_R0. apply is_lim_seq_const.
Qed.

Lemma ex_series_RtoC (a : nat -> R) :
 ex_series (RtoC ∘ a) <-> ex_series a.
Proof.
 split; intros (l & H).
 - rewrite is_Cseries_alt in H. rewrite is_lim_Cseq_proj in H.
   destruct H as (H1 & H2).
   unfold "∘" in *. setoid_rewrite re_sum_n in H1.
   rewrite ex_series_alt. now exists (Re l).
 - exists (RtoC l). now rewrite is_CSeries_RtoC.
Qed.

Lemma CSeries_RtoC (a : nat -> R) :
  ex_series a -> CSeries (RtoC ∘ a) = RtoC (Series a).
Proof.
 intros. now apply CSeries_unique, is_CSeries_RtoC, Series_correct.
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

Lemma is_series_incr_1' (a : nat -> C) l :
  is_series a l <-> is_series (a∘S) (l - a O).
Proof.
 split; intros H.
 - rewrite is_Cseries_alt in *.
   apply (is_lim_Cseq_incr_n _ 1) in H.
   apply is_lim_Cseq_ext with (fun n => sum_n a (n+1) - a O).
   { intros n. rewrite <- !big_sum_sum_n.
     rewrite <- big_sum_extend_l, Nat.add_1_r. change Gplus with Cplus.
     ring_simplify. easy. }
   apply is_lim_Cseq_minus; trivial. apply is_lim_Cseq_const.
 - rewrite is_Cseries_alt in *.
   apply (is_lim_Cseq_incr_n _ 1).
   apply is_lim_Cseq_ext with (fun n => sum_n (a∘S) n + a O).
   { intros n. rewrite <- !big_sum_sum_n.
     symmetry. rewrite <- big_sum_extend_l, Nat.add_1_r.
     change Gplus with Cplus. apply Cplus_comm. }
   replace l with (l - a O + a O) by ring.
   apply is_lim_Cseq_plus; trivial. apply is_lim_Cseq_const.
Qed.

Lemma CSeries_incr_1 (a : nat -> C) :
 ex_series a -> CSeries a = a O + CSeries (a∘S).
Proof.
 intros. apply CSeries_unique. rewrite is_series_incr_1'.
 replace (_+_-_) with (CSeries (a∘S)) by ring.
 apply CSeries_correct. unfold "∘". now rewrite <- ex_series_incr_1.
Qed.

Lemma is_series_incr_n' (a : nat -> C) l (n:nat) :
  is_series a l <-> is_series (fun k => a (n+k)%nat) (l - big_sum a n).
Proof.
 revert a l. induction n.
 - intros a l. simpl. replace (l-0) with l by lca. easy.
 - intros a l. rewrite is_series_incr_1', IHn.
   rewrite <- big_sum_extend_l. change Gplus with Cplus.
   replace (l - (_+_)) with (l - a O - big_sum (fun k => a (S k)) n) by ring.
   easy.
Qed.

Lemma CSeries_incr_n (a : nat -> C) (n:nat) :
 ex_series a -> CSeries a = big_sum a n + CSeries (fun k => a (n+k)%nat).
Proof.
 intros. apply CSeries_unique. rewrite is_series_incr_n' with (n:=n).
 replace (_+_-_) with (CSeries (fun k => a (n+k)%nat)) by ring.
 apply CSeries_correct. now rewrite <- ex_series_incr_n.
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
