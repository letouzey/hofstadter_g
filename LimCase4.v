From Coq Require Import Bool Arith Lia QArith Reals Lra Qreals.
From QuantumLib Require Import Polynomial.
Require Import MoreFun MoreList MoreReals MoreComplex.
Require Import MoreLim MorePoly MoreMatrix.
Require Import DeltaList GenFib GenG GenAdd Words Mu ThePoly Approx.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * Studying case q=4

   We focus here on the case q=4, compute the complex roots of [X^5-X^4-1],
   and express (A 4 n) in term of combinations of powers of these roots.
   Then we show that [Rabs (f 4 n - tau 4 * n)] has infinity as limsup
   (or equivalently as sup, see MoreLim.Sup_LimSup_pinfty).
*)

Definition μ := mu 4.
Definition τ := tau 4.

#[local] Instance : Approx 0.7548776662466 τ 0.7548776662467.
Proof. red. unfold τ. generalize tau_4. lra. Qed.

#[local] Instance : Approx 1.324717957244 μ 1.324717957245.
Proof. red. unfold μ. generalize mu_4. lra. Qed.

Lemma τ_μ : τ = /μ.
Proof.
 reflexivity.
Qed.

(** The complex roots of [X^5-X^4-1] *)

Lemma Poly4_factor : ThePoly 4 = (Pmult [C1;-C1;C1] [-C1;-C1;C0;C1])%C.
Proof.
 unfold ThePoly; simpl. repeat (f_equal; try lca).
Qed.

Definition γ := Cexp (PI/3).
Definition γbar := Cexp (-PI/3).

Lemma γ_conj : γbar = Cconj γ.
Proof.
 unfold γ, γbar. rewrite Cexp_conj_neg. f_equal. lra.
Qed.

Lemma γmod : Cmod γ = 1.
Proof.
 apply Cmod_Cexp.
Qed.

Lemma factor1 : [C1;-C1;C1]%C = linfactors [γ;γbar].
Proof.
 simpl. f_equal;[|f_equal].
 - ring_simplify. unfold γ, γbar. rewrite <- Cexp_add.
   replace (_+_) with 0 by lra. now rewrite Cexp_0.
 - apply Cminus_eq_0. ring_simplify.
   rewrite γ_conj, (Cplus_comm _ γ), re_alt'.
   unfold γ, Cexp, Re. simpl. rewrite cos_PI3. lca.
 - f_equal; lca.
Qed.

Definition re_α := - μ/2.
Definition im_α := sqrt (τ-re_α^2).

Definition α : C := (re_α, im_α).
Definition αbar : C := (re_α, - im_α).

#[local] Instance : Approx (-0.67) re_α (-0.66).
Proof. approx. Qed.

#[local] Instance : Approx 0.56 im_α 0.57.
Proof. approx. Qed.

Lemma α_conj : Cconj α = αbar.
Proof. reflexivity. Qed.

Lemma αmod2 : (Cmod α)^2 = τ.
Proof.
 rewrite Cmod2_alt. unfold α, Re, Im; simpl fst; simpl snd.
 unfold im_α. rewrite <- (Rsqr_pow2 (sqrt _)), Rsqr_sqrt. lra.
 unfold re_α. approx.
Qed.

Lemma μ3 : μ^3 = μ+1.
Proof.
 symmetry. apply Rminus_diag_uniq_sym.
 apply Rmult_eq_reg_l with (μ^2-μ+1); try approx.
 rewrite Rmult_0_r. ring_simplify. unfold μ. rewrite (mu_carac 4). ring.
Qed.

Lemma factor2 : [-C1;-C1;C0;C1]%C = linfactors [RtoC μ;α;αbar].
Proof.
 simpl. f_equal;[|f_equal;[|f_equal] ]; try ring_simplify.
 - apply Cminus_eq_0. ring_simplify.
   rewrite (Cmult_comm αbar), <- Cmod2_conj, αmod2, τ_μ, RtoC_inv.
   field. injection. approx.
 - rewrite Cmult_comm, <- α_conj, <- Cmod2_conj, αmod2.
   rewrite <- Cplus_assoc, <- Cmult_plus_distr_r, (Cplus_comm _ α), re_alt'.
   change (Re α) with re_α. unfold re_α. rewrite τ_μ, RtoC_inv.
   rewrite RtoC_div, RtoC_opp. symmetry. apply Cminus_eq_0.
   field_simplify; try (injection; approx).
   rewrite RtoC_pow, μ3. rewrite RtoC_plus. field. injection; approx.
 - apply Cminus_eq_0. ring_simplify.
   rewrite <- α_conj, (Cplus_comm _ α), re_alt'.
   change (Re α) with re_α. unfold re_α. rewrite <- RtoC_mult, <- RtoC_plus.
   f_equal. field.
 - f_equal. lca.
Qed.

Definition roots := [RtoC μ; γ; γbar; α; αbar].

Lemma roots_sorted : SortedRoots 4 roots.
Proof.
 split.
 - rewrite Poly4_factor, factor1, factor2, <- linfactors_app.
   apply linfactors_perm. unfold roots. simpl.
   apply (Permutation_app_swap_app [γ;γbar] [RtoC μ]).
 - do 3 constructor.
   + do 2 constructor. constructor. constructor. right.
     unfold αbar, α, Re, Im; simpl. split; trivial. approx.
   + constructor. constructor. rewrite γ_conj.
     unfold α. simpl. rewrite cos_PI3. approx.
   + rewrite γ_conj. right. simpl. split; trivial. rewrite sin_PI3.
     field_simplify. apply Rmult_lt_compat_r; try nra.
     generalize (sqrt_lt_R0 3). lra.
   + simpl. rewrite cos_PI3. approx.
Qed.

Local Hint Rewrite RtoC_pow : RtoC.
Local Hint Rewrite <- RtoC_opp RtoC_plus RtoC_mult RtoC_minus RtoC_inv
 RtoC_div : RtoC.

Lemma μ_is_Rroot : μ^5 = μ^4 + 1.
Proof.
 exact (mu_carac 4).
Qed.

Lemma μ_is_Croot : (μ^5 = μ^4 + 1)%C.
Proof.
 autorewrite with RtoC. f_equal. apply μ_is_Rroot.
Qed.

Lemma γ_is_Croot : (γ^5 = γ^4 + 1)%C.
Proof.
 rewrite <- ThePoly_root_carac. destruct roots_sorted as (->,_).
 apply linfactors_roots. simpl. tauto.
Qed.

Lemma α_is_Croot : (α^5 = α^4 + 1)%C.
Proof.
 rewrite <- ThePoly_root_carac. destruct roots_sorted as (->,_).
 apply linfactors_roots. simpl. tauto.
Qed.

Lemma A4_eqn_C :
 let a := coefA 4 μ in
 let b := coefA 4 γ in
 let c := coefA 4 γbar in
 let d := coefA 4 α in
 let e := coefA 4 αbar in
 forall n, RtoC (A 4 n) = (a*μ^n + b*γ^n + c*γbar^n + d*α^n + e*αbar^n)%C.
Proof.
 intros a b c d e n.
 rewrite (Equation_A 4 roots roots_sorted). unfold roots.
 simpl. fold a b c d e. ring.
Qed.

Lemma A4_eqn_R :
 let a := coef_mu 4 in
 let b := coefA 4 γ in
 let d := coefA 4 α in
 forall n, INR (A 4 n) = a*μ^n + 2*Re (b*γ^n) + 2*Re (d*α^n).
Proof.
 intros a b d n.
 apply RtoC_inj. rewrite A4_eqn_C.
 autorewrite with RtoC.
 rewrite <- coef_mu_ok. fold a.
 rewrite γ_conj, coefA_conj.
 change αbar with (Cconj α). rewrite coefA_conj.
 fold b d. rewrite <- !Cpow_conj, <- !Cconj_mult_distr.
 rewrite !RtoC_plus, !RtoC_mult.
 rewrite <- !re_alt'. ring.
Qed.

Definition decomp_u n := map (Nat.mul 6) (seq 0 n).

Definition seq_u n := sumA 4 (decomp_u n).

Definition decomp_u_S n : decomp_u (S n) = decomp_u n ++ [6*n]%nat.
Proof.
 unfold decomp_u. now rewrite seq_S, map_app.
Qed.

Lemma decomp_u_delta n : Delta 6 (decomp_u n).
Proof.
 induction n.
 - constructor.
 - rewrite decomp_u_S. apply Delta_app_iff; repeat split; trivial.
   constructor. intros x x' Hx [<-|[ ] ]. unfold decomp_u in Hx.
   rewrite in_map_iff in Hx. destruct Hx as (y & <- & Hy).
   rewrite in_seq in Hy. lia.
Qed.

Lemma γ6 : (γ^6)%C = 1.
Proof.
 unfold γ. rewrite Cexp_pow, INR_IZR_INZ. simpl.
 replace (PI/3*6) with (2*PI) by field. apply Cexp_2PI.
Qed.

Lemma delta_seq_u_eqn n :
  f 4 (seq_u n) - τ * (seq_u n) =
  2*n*Re (coefdA 4 γ) +
  2*Re (coefdA 4 α * Clistsum (map (Cpow α) (decomp_u n))).
Proof.
 apply RtoC_inj. rewrite (Equation_delta' 4 roots roots_sorted); try lia.
 unfold roots. simpl tl.
 rewrite decomp_carac with (l:=decomp_u n); try easy.
 2:{ apply Delta_S, decomp_u_delta. }
 simpl map.
 rewrite γ_conj, <- α_conj. rewrite !coefdA_conj.
 set (l := decomp_u n).
 set (dγ := coefdA 4 γ).
 set (dα := coefdA 4 α).
 replace (Clistsum (map (Cpow (Cconj γ)) l))
  with (Cconj (Clistsum (map (Cpow γ) l))).
 2:{ rewrite Clistsum_conj, map_map. f_equal. apply map_ext.
     intros a. apply Cpow_conj. }
 set (sum := Clistsum (map (Cpow α) l)).
 replace (Clistsum (map (Cpow (Cconj α)) l)) with (Cconj sum).
 2:{ unfold sum. rewrite Clistsum_conj, map_map. f_equal. apply map_ext.
     intros a. apply Cpow_conj. }
 replace (Clistsum (map (Cpow γ) l)) with (RtoC n).
 2:{ clear. unfold l, decomp_u. rewrite map_map.
     rewrite map_ext with (g := fun _ => C1), Clistsum_const, seq_length. lca.
     intros a. now rewrite Cpow_mult, γ6, Cpow_1_l. }
 rewrite Cconj_R, <- !Cconj_mult_distr.
 simpl Clistsum.
 rewrite (Rmult_comm 2), Rmult_assoc.
 rewrite RtoC_plus, !RtoC_mult, <- !re_alt'. ring.
Qed.

#[local] Instance : Approx 0.0189 (Re (coefdA 4 γ)) 0.0190.
Proof.
 unfold coefdA, coefA. fold τ.
 rewrite !INR_IZR_INZ. simpl IZR.
 unfold Cdiv. replace (/(5*γ-4))%C with ((/21)%R*(5*Cconj γ-4))%C.
 2:{ rewrite Cinv_alt.
     2:{ intros E. apply Cminus_eq_0 in E. injection E as E _.
         rewrite cos_PI3 in E. revert E. lra. }
     unfold Cdiv. rewrite Cmult_comm. f_equal.
     - now rewrite Cconj_minus_distr, Cconj_mult_distr, !Cconj_R.
     - rewrite RtoC_inv. f_equal.
       rewrite Cmod2_alt. f_equal. simpl. rewrite cos_PI3, sin_PI3.
       field_simplify. rewrite pow2_sqrt by lra. field. }
 remember (Re _) as x eqn:Hx.
 simpl in Hx.
 rewrite cos_PI3, sin_PI3 in Hx. field_simplify in Hx.
 2:{ replace (sqrt 3 * sqrt 3) with (Rsqr (sqrt 3)) in Hx by trivial.
     rewrite Rsqr_sqrt in Hx; lra. }
 change (8%nat) with (2*4)%nat in Hx.
 change (6%nat) with (2*3)%nat in Hx.
 change (4%nat) with (2*2)%nat in Hx.
 rewrite !pow_mult, pow2_sqrt in Hx by lra.
 field_simplify in Hx. subst x. approx.
Qed.

Lemma delta_seq_u_bound :
 exists (c c' : posreal),
 forall n, Rabs (f 4 (seq_u n) - τ * seq_u n - c*n) <= c'.
Proof.
 set (c := 2*Re (coefdA 4 γ)).
 assert (Hc : 0 < c) by (unfold c; approx).
 exists (mkposreal c Hc). simpl.
 set (c' := 2*(Cmod (coefdA 4 α)/(1-Cmod α^6))).
 assert (Hc' : 0 < c').
 { unfold c'. repeat apply Rmult_lt_0_compat; try lra.
   - apply Cmod_gt_0. apply coefdA_nz.
     + eapply SortedRoots_roots. apply roots_sorted. unfold roots.
       simpl;tauto.
     + change (Cnth roots 3 <> Cnth roots 0). intros E.
       apply NoDup_nth in E; simpl; try lia.
       eapply SortedRoots_nodup; apply roots_sorted.
   - change 6%nat with (2*3)%nat. rewrite pow_mult, αmod2. approx. }
 exists (mkposreal c' Hc'). simpl.
 intros n.
 rewrite delta_seq_u_eqn. unfold c.
 remember (_+_-_) as x eqn:Hx. ring_simplify in Hx. subst x.
 rewrite Rabs_mult, Rabs_right by lra.
 unfold c'. apply Rmult_le_compat_l; try lra.
 eapply Rle_trans; [apply re_le_Cmod|]. rewrite Cmod_mult.
 unfold Rdiv. apply Rmult_le_compat_l. apply Cmod_ge_0.
 eapply Rle_trans; [apply Clistsum_mod|]. rewrite map_map.
 rewrite map_ext with (g:=pow (Cmod α)).
 2:{ intros. now rewrite Cmod_pow. }
 apply sum_pow; try apply decomp_u_delta. lia. split. apply Cmod_ge_0.
 apply Rsqr_incrst_0; try lra; try apply Cmod_ge_0.
 rewrite Rsqr_pow2, αmod2. approx.
Qed.

Lemma delta_limsup_q4 :
 is_LimSup_seq (fun n => Rabs (f 4 n - τ * n)) Rbar.p_infty.
Proof.
 replace Rbar.p_infty with (LimSup_seq (fun n => Rabs (f 4 n - τ * n))).
 apply LimSup_seq_correct.
 apply Sup_LimSup_pinfty, is_sup_seq_unique.
 intros M.
 destruct delta_seq_u_bound as (c & c' & LE).
 set (m := (S (Z.to_nat (Int_part ((M+c')/c))))).
 assert (Hm : M < c*m-c').
 { apply Rcomplements.Rlt_minus_r.
   rewrite Rmult_comm. apply Rcomplements.Rlt_div_l.
   destruct c; simpl; lra.
   unfold m.
   set (x := (M+c')/c). clearbody x.
   rewrite (int_frac x) at 1.
   rewrite S_INR, INR_IZR_INZ.
   destruct (Int_part x) eqn:E.
   - simpl. apply Rplus_lt_compat_l. apply base_fp.
   - rewrite Z2Nat.id; try lia. apply Rplus_lt_compat_l. apply base_fp.
   - apply Rplus_lt_compat. 2:apply base_fp. simpl. apply IZR_lt. lia. }
 clearbody m. exists (seq_u m). specialize (LE m).
 set (d := f 4 (seq_u m) - τ * seq_u m) in *.
 eapply Rlt_le_trans; [apply Hm|].
 rewrite <- Rabs_Ropp.
 replace (-d) with (-(c*m) - (d-c*m)) by lra.
 eapply Rle_trans; [|apply Rabs_triang_inv].
 rewrite Rabs_Ropp, Rabs_right. lra.
 apply Rle_ge, Rmult_le_pos. destruct c; simpl; lra. apply pos_INR.
Qed.

(* Print Assumptions delta_limsup_q4. *)
