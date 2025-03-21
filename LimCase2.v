From Coq Require Import Arith Lia NArith Reals Lra.
From Hofstadter.HalfQuantum Require Import Complex.
Require Import MoreFun MoreList MoreReals MoreLim MoreComplex MoreSum.
Require Import DeltaList Approx.
Require Import GenFib GenG GenAdd Words Mu ThePoly Freq Discrepancy.
Local Open Scope C.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion RtoC : R >-> C.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * Studying case q=2 i.e. Article's k=3

   We focus here on the case q=2, compute the complex roots of [X^3-X^2-1],
   and express (A 2 n) in term of combinations of powers of these roots.
   Then we study the frequencies in [Words.qseq 2], and the behaviour of
   function [h] (i.e. [f 2] ie Hofstadter's H).
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
 rewrite <- (sqrt_pow2 (Cmod α)), αmod2 by apply Cmod_ge_0. approx.
Qed.

#[local] Instance im_α_approx : Approx 0.79255199 im_α 0.792552.
Proof.
 approx.
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

Lemma distinct_roots :
  α <> μ /\ αbar <> μ /\ α <> αbar.
Proof.
 unfold α, αbar, RtoC; repeat split.
 - intros [= A _]. revert A. approx.
 - intros [= _ A]. revert A. approx.
 - intros [= A]. revert A. approx.
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

Definition roots := [RtoC μ; α; αbar].

Lemma roots_sorted : SortedRoots 2 roots.
Proof.
 split.
 - unfold roots, ThePoly. simpl.
   apply MorePoly.eq_Peq. f_equal;[|f_equal;[|f_equal]].
   + rewrite <- roots_prod at 1. ring.
   + ring_simplify. rewrite <- sigma2_nul. ring.
   + rewrite <- roots_sum at 1. ring.
   + f_equal; lca.
 - do 2 constructor.
   + repeat constructor.
   + constructor. right. unfold α, αbar. simpl. split; trivial. approx.
   + left. unfold α. simpl. approx.
Qed.

(** Explicit decomposition of [A 2 n] into a linear combination
    of root powers. Now just an instance of [ThePoly.Equation_A]. *)

Definition coef_μ : R := coef_mu 2.
Definition coef_α : C := coefA 2 α.
Definition coef_αbar : C := coefA 2 αbar.

#[local] Instance coef_μ_bound : Approx 1.3134 coef_μ 1.3135.
Proof.
 approx.
Qed.

Lemma coef_αbar_conj : coef_αbar = Cconj coef_α.
Proof.
 unfold coef_αbar, coef_α, coefA.
 rewrite Cdiv_conj, !Cpow_conj, Cconj_minus_distr, Cconj_mult_distr.
 now rewrite !Cconj_R.
Qed.

Lemma A2_eqn n : INR (A 2 n) = coef_μ * μ ^n + 2 * Re (coef_α * α^n).
Proof.
 apply RtoC_inj. unfold coef_μ.
 rewrite RtoC_plus, !RtoC_mult, <- !RtoC_pow, re_alt, coef_mu_ok.
 field_simplify. fold μ.
 rewrite Cconj_mult_distr, Cpow_conj. change (Cconj α) with αbar.
 rewrite <- coef_αbar_conj.
 rewrite (ThePoly.Equation_A 2 roots roots_sorted). simpl.
 fold coef_α coef_αbar. ring.
Qed.

Lemma A2_div_μ_n n : A 2 n / μ ^n = coef_μ + 2 * Re (coef_α * (α/μ)^n).
Proof.
 assert (μ <> 0) by approx.
 assert (μ^n <> 0). { now apply pow_nonzero. }
 unfold Cdiv. rewrite Cpow_mul_l, Cpow_inv.
 rewrite Cmult_assoc, RtoC_pow, <- RtoC_inv, re_scal_r.
 rewrite A2_eqn. field; trivial.
Qed.

Lemma Cmod_α_μ : Cmod (α/μ) < 1.
Proof.
 assert (0 < μ) by approx.
 assert (0 < τ) by approx.
 apply Rlt_pow2_inv; try lra.
 rewrite Cmod_div, Cmod_R, Rabs_right by lra.
 unfold Rdiv. rewrite Rpow_mult_distr. rewrite αmod2. approx.
Qed.

Lemma Lim_A2_div_μ_n : is_lim_seq (fun n => A 2 n / μ ^ n) coef_μ.
Proof.
 apply ThePoly.A_div_pow_mu_limit.
Qed.

Lemma Lim_A2_ratio : is_lim_seq (fun n => A 2 (S n) / A 2 n) μ.
Proof.
 apply Freq.A_ratio.
Qed.

(** Equations about the coefficients *)

Lemma coefs_eqn1 : coef_μ + 2 * Re coef_α = 1.
Proof.
 change 1 with (INR (A2 0)). rewrite A2_eqn.
 simpl pow. simpl Cpow. rewrite Cmult_1_r. ring.
Qed.

Lemma coefs_eqn2 : coef_μ * μ + 2 * Re (coef_α * α) = 2.
Proof.
 change 2 with (INR (A2 1)) at 2. rewrite A2_eqn.
 simpl pow. simpl Cpow. rewrite !Cmult_1_r. ring.
Qed.

Lemma coefs_eqn3 : coef_μ * μ^2 + 2 * Re (coef_α * α^2) = 3.
Proof.
 replace 3 with (INR (A2 2)) by (simpl; lra). now rewrite A2_eqn.
Qed.


(** For the coming study of discrepancies, build and check an approx
    of τ up to 10^-100 *)

Definition newton_step x := Qred (x - (x^3+x-1)/(3*x^2+1))%Q.
Definition newton n := N.iter n newton_step 1%Q.

Definition Qround '(Qmake a b) n :=
  let d := (10^n)%positive in
  let z := Z.div (a*Z.pos d) (Z.pos b) in
  (Qmake z d, Qmake (z+1) d).

Definition tau100 : Q*Q := Eval vm_compute in Qround (newton 8) 100.

Lemma tau100_approx : Approx (fst tau100) τ (snd tau100).
Proof.
 split.
 - apply Rlt_le. apply Mu.Ptau_lower; approx.
 - apply Rlt_le. apply Mu.Ptau_upper; approx.
Qed.

(** ** Discrepancies, i.e. differences [h n - τ*n].

    We show that these differences are always in -0.7085..0.8542.
    Differences are all of the form [a-b*τ], let's encode them
    via pairs of N numbers. The key operation is then to compare
    to compare [a1-b1*τ] and [a2-b2*τ]. *)

Module NN.
Local Open Scope N.

Definition t : Type := N*N.

Definition N2R n := IZR (Z.of_N n).
Definition N2Q n := inject_Z (Z.of_N n).

Definition to_R '(a,b) : R := (N2R a - N2R b * τ)%R.

Definition to_QQ '(a,b) : Q*Q :=
  (N2Q a - N2Q b * snd tau100, N2Q a - N2Q b * fst tau100)%Q.

Lemma to_QQ_ok ab :
  Approx (fst (to_QQ ab)) (to_R ab) (snd (to_QQ ab)).
Proof.
 assert (H := tau100_approx).
 destruct ab as (a,b). cbn -[to_QQ].
 unfold to_QQ. unfold fst at 1. unfold snd at 2.
 apply minus_approx. apply IZR_approx.
 apply mult_approx. apply IZR_approx. apply H. red; simpl; lia. easy.
Qed.

Definition ltb '(a1,b1) '(a2,b2) :=
  let r := (Z.of_N a1 - Z.of_N a2)%Z in
  let s := (Z.of_N b1 - Z.of_N b2)%Z in
  (r*(r^2+s^2) <? s^3)%Z.

Lemma ltb_spec ab1 ab2 : ltb ab1 ab2 = true <-> (to_R ab1 < to_R ab2)%R.
Proof.
 destruct ab1 as (a1,b1), ab2 as (a2,b2).
 cbn -[Z.pow]. rewrite Z.ltb_lt.
 set (r := (Z.of_N a1 - Z.of_N a2)%Z) in *.
 set (s := (Z.of_N b1 - Z.of_N b2)%Z) in *.
 rewrite Rminus_lt_0.
 replace (_-_-_)%R with (τ*IZR s - IZR r)%R.
 2:{ unfold r, s, N2R. rewrite !minus_IZR. ring. }
 rewrite <- Rminus_lt_0.
 destruct (Z.compare_spec 0 s) as [<-|POS|NEG].
 - replace (r * _)%Z with (r^3)%Z by ring. change (0^3) with 0.
   rewrite Rmult_0_r. rewrite IZR_lt_iff. lia.
 - destruct (Z.le_gt_cases r 0).
   { split; intros _; try lia.
     apply Rle_lt_trans with 0%R. now apply IZR_le.
     apply Rmult_lt_0_compat. approx. now apply IZR_lt. }
   rewrite <- Rcomplements.Rlt_div_l by now apply IZR_lt.
   unfold τ. rewrite <- Ptau_lt1_iff.
   2:{ apply Rcomplements.Rdiv_le_0_compat. apply IZR_le; lia.
       now apply IZR_lt. }
   unfold Ptau.
   split; intros LT.
   + apply Rmult_lt_reg_r with (IZR s^3)%R.
     { rewrite pow_IZR. apply IZR_lt; lia. }
     field_simplify. 2:{ apply IZR_neq. lia. }
     rewrite !pow_IZR, <- !mult_IZR, <- plus_IZR. apply IZR_lt.
     simpl Z.of_nat. now ring_simplify in LT.
   + apply Rmult_lt_compat_r with (r := (IZR s^3)%R) in LT.
     2:{ rewrite pow_IZR. apply IZR_lt; lia. }
     field_simplify in LT. 2:{ revert LT. apply IZR_neq. lia. }
     rewrite !pow_IZR, <- !mult_IZR, <- plus_IZR in LT. apply lt_IZR in LT.
     simpl Z.of_nat in LT. now ring_simplify.
 - destruct (Z.le_gt_cases 0 r).
   { split; intros H'; try lia. exfalso. apply IZR_lt in NEG.
     apply IZR_le in H. generalize (tau_itvl 2). fold τ. nra. }
   rewrite Rminus_lt_0. replace (_ - _)%R with (IZR (-r) - τ * IZR (-s))%R.
   2:{ rewrite !opp_IZR. lra. }
   rewrite <- Rminus_lt_0.
   rewrite Rcomplements.Rlt_div_r by (apply IZR_lt; lia).
   unfold τ. rewrite <- Ptau_gt1_iff.
   2:{ apply Rcomplements.Rdiv_le_0_compat. apply IZR_le; lia.
       apply IZR_lt; lia. }
   unfold Ptau.
   split; intros LT.
   + apply Rmult_lt_reg_r with (IZR (-s)^3)%R.
     { rewrite pow_IZR. apply IZR_lt; lia. }
     field_simplify. 2:{ apply IZR_neq. lia. }
     rewrite !pow_IZR, <- !mult_IZR, <- plus_IZR. apply IZR_lt.
     simpl Z.of_nat. ring_simplify. apply Z.opp_lt_mono in LT.
     now ring_simplify in LT.
   + apply Rmult_lt_compat_r with (r := (IZR (-s)^3)%R) in LT.
     2:{ rewrite pow_IZR. apply IZR_lt; lia. }
     field_simplify in LT. 2:{ revert LT. apply IZR_neq. lia. }
     rewrite !pow_IZR, <- !mult_IZR, <- plus_IZR in LT. apply lt_IZR in LT.
     simpl Z.of_nat in LT. ring_simplify in LT.
     apply Z.opp_lt_mono. now ring_simplify.
Qed.

Definition max ab cd := if ltb ab cd then cd else ab.
Definition min ab cd := if ltb cd ab then cd else ab.

Definition add '(a,b) '(c,d) := (a+c,b+d).

Lemma add_ok ab cd : to_R (add ab cd) = (to_R ab + to_R cd)%R.
Proof.
 destruct ab as (a,b), cd as (c,d). simpl.
 unfold N2R. rewrite !N2Z.inj_add, !plus_IZR. lra.
Qed.

Lemma max_ok ab cd : to_R (max ab cd) = Rmax (to_R ab) (to_R cd).
Proof.
 unfold max.
 destruct (ltb ab cd) eqn:E.
 - rewrite ltb_spec in E. rewrite Rmax_right; trivial. lra.
 - rewrite <- not_true_iff_false, ltb_spec in E.
   rewrite Rmax_left; trivial. lra.
Qed.

Lemma min_ok ab cd : to_R (min ab cd) = Rmin (to_R ab) (to_R cd).
Proof.
 unfold min.
 destruct (ltb cd ab) eqn:E.
 - rewrite ltb_spec in E. rewrite Rmin_right; trivial. lra.
 - rewrite <- not_true_iff_false, ltb_spec in E.
   rewrite Rmin_left; trivial. lra.
Qed.

(** Simultaneous computations of (diff 2 (A2 n)) and (MaxDeltas 2) *)

Record buffer := Buffer { d0:t; d1:t; d2:t; m0:t; m1:t; m2:t }.

Definition max_init := Buffer (1,1) (1,2) (2,3) (0,0) (1,1) (1,1).
Definition max_next '(Buffer d0 d1 d2 m0 m1 m2) :=
  Buffer d1 d2 (add d0 d2) m1 m2 (max m2 (add m0 d2)).
Definition max_loop (n:N) := N.iter (n-2) max_next max_init.
Definition maxdeltas (n:N) := (max_loop n).(m2).

Definition min_init := Buffer (1,1) (1,2) (2,3) (0,0) (0,0) (1,2).
Definition min_next '(Buffer d0 d1 d2 m0 m1 m2) :=
  Buffer d1 d2 (add d0 d2) m1 m2 (min m2 (add m0 d2)).
Definition min_loop (n:N) := N.iter (n-2) min_next min_init.
Definition mindeltas (n:N) := (min_loop n).(m2).

Lemma max_loop_spec (n:nat) :
  let '(Buffer d0 d1 d2 m0 m1 m2) := max_loop (N.of_nat n + 2) in
  to_R d0 = diff 2 (A2 n) /\
  to_R d1 = diff 2 (A2 (n+1)) /\
  to_R d2 = diff 2 (A2 (n+2)) /\
  to_R m0 = MaxDeltas 2 n /\
  to_R m1 = MaxDeltas 2 (n+1) /\
  to_R m2 = MaxDeltas 2 (n+2).
Proof.
 unfold max_loop.
 rewrite N2Nat.inj_iter.
 replace (N.to_nat (_+2-2)) with n by lia.
 induction n.
 - simpl; unfold diff. fold τ. unfold N2R. simpl.
   rewrite (Rmax_right 0) by approx. repeat split; try lra.
   rewrite Rmax_left by approx. lra.
 - simpl Nat.iter. destruct (Nat.iter _ _ _) as [d1 d2 d3 m1 m2 m3].
   unfold max_next.
   replace (S n + 1)%nat with (n+2)%nat by lia.
   replace (S n)%nat with (n+1)%nat at 1 3 by lia.
   destruct IHn as (IH1 & IH2 & IH3 & IH1' & IH2' & IH3').
   repeat split; trivial.
   + rewrite add_ok, IH1, IH3.
     simpl. rewrite (Nat.add_comm (A2 _)).
     rewrite diff_A_A by lia. f_equal. f_equal. f_equal. lia.
   + rewrite max_ok, add_ok. simpl. f_equal; trivial.
     f_equal; trivial. rewrite IH1'. f_equal. lia.
Qed.

Lemma maxdeltas_spec (n:nat) : (2 <= n)%nat ->
  MaxDeltas 2 n = to_R (maxdeltas (N.of_nat n)).
Proof.
 intros Hn. unfold maxdeltas.
 assert (H := max_loop_spec (n-2)).
 replace (N.of_nat (n-2) + 2)%N with (N.of_nat n) in H by lia.
 destruct (max_loop _); simpl in *.
 replace (n-2+2)%nat with n in H by lia. symmetry. apply H.
Qed.

Definition checkapprox a b '(q1,q2) := Qle_bool a q1 && Qle_bool q2 b.

Lemma checkapprox_ok a b qq :
 checkapprox a b qq = true -> (a <= fst qq)%Q /\ (snd qq <= b)%Q.
Proof.
 unfold checkapprox. destruct qq as (q1,q2).
 now rewrite andb_true_iff, !Qle_bool_iff.
Qed.

Lemma maxdeltas_approx n a b : (2 <= n)%nat ->
 checkapprox a b (to_QQ (maxdeltas (N.of_nat n))) = true
 -> Approx a (MaxDeltas 2 n) b.
Proof.
 intros Hn H. rewrite (maxdeltas_spec n Hn).
 eapply approx_trans; [apply to_QQ_ok| | ]; eapply checkapprox_ok; eauto.
Qed.

Lemma min_loop_spec (n:nat) :
  let '(Buffer d0 d1 d2 m0 m1 m2) := min_loop (N.of_nat n + 2) in
  to_R d0 = diff 2 (A2 n) /\
  to_R d1 = diff 2 (A2 (n+1)) /\
  to_R d2 = diff 2 (A2 (n+2)) /\
  to_R m0 = MinDeltas 2 n /\
  to_R m1 = MinDeltas 2 (n+1) /\
  to_R m2 = MinDeltas 2 (n+2).
Proof.
 unfold min_loop.
 rewrite N2Nat.inj_iter.
 replace (N.to_nat (_+2-2)) with n by lia.
 induction n.
 - simpl; unfold diff. fold τ. unfold N2R. simpl.
   rewrite (Rmin_left 0) by approx. repeat split; try lra.
   rewrite Rmin_right by approx. lra.
 - simpl Nat.iter. destruct (Nat.iter _ _ _) as [d1 d2 d3 m1 m2 m3].
   unfold min_next.
   replace (S n + 1)%nat with (n+2)%nat by lia.
   replace (S n)%nat with (n+1)%nat at 1 3 by lia.
   destruct IHn as (IH1 & IH2 & IH3 & IH1' & IH2' & IH3').
   repeat split; trivial.
   + rewrite add_ok, IH1, IH3.
     simpl. rewrite (Nat.add_comm (A2 _)).
     rewrite diff_A_A by lia. f_equal. f_equal. f_equal. lia.
   + rewrite min_ok, add_ok. simpl. f_equal; trivial.
     f_equal; trivial. rewrite IH1'. f_equal. lia.
Qed.

Lemma mindeltas_spec (n:nat) : (2 <= n)%nat ->
  MinDeltas 2 n = to_R (mindeltas (N.of_nat n)).
Proof.
 intros Hn. unfold mindeltas.
 assert (H := min_loop_spec (n-2)).
 replace (N.of_nat (n-2) + 2)%N with (N.of_nat n) in H by lia.
 destruct (min_loop _); simpl in *.
 replace (n-2+2)%nat with n in H by lia. symmetry. apply H.
Qed.

Lemma mindeltas_approx n a b : (2 <= n)%nat ->
 checkapprox a b (to_QQ (mindeltas (N.of_nat n))) = true
 -> Approx a (MinDeltas 2 n) b.
Proof.
 intros Hn H. rewrite (mindeltas_spec n Hn).
 eapply approx_trans; [apply to_QQ_ok| | ]; eapply checkapprox_ok; eauto.
Qed.

End NN.

(** Taking n=400 is enough to get 30 decimal digits of precision *)

#[local] Instance maxdeltas_400 :
  Approx 0.854187179928304211983581540152665 (MaxDeltas 2 400)
         0.854187179928304211983581540152667.
Proof.
 apply NN.maxdeltas_approx. lia. now vm_compute.
Qed.

Definition precision '(r,s) :=
 let '(Qmake a b) := Qminus s r in
 ((Z.log2 a - Z.log2 (Z.pos b))*100/332)%Z.

(* Compute precision maxdeltas_400_QQ. *)

(** Now we bound (residue 2 roots 400). *)

Definition rest := 2*Cmod (coefdA 2 α)/(1 - Cmod α^3).

Lemma residue2_eqn n :
  residue 2 LimCase2.roots n = rest * Cmod α^n.
Proof.
 unfold residue, roots. cbn -[pow].
 change αbar with (Cconj α). rewrite coefdA_conj, !Cmod_Cconj.
 rewrite Rplus_0_r, <- double.
 unfold rest. field. approx.
Qed.

#[local] Instance : Approx 1.111 rest 1.112.
Proof.
 unfold rest. unfold coefdA, coefA. fold τ.
 rewrite !INR_IZR_INZ. cbn -[pow Cpow].
 replace (_ / _ * _)%C with (α ^ 2 / (3 * α - C2) * (1 - τ * α))%C.
 2:{ unfold Cdiv. rewrite <- (Cinv_l α). ring.
     intros [= E _]. revert E. approx. }
 unfold Cdiv. rewrite !Cmod_mult, Cmod_pow, αmod2, Cmod_inv.
 replace (Cmod α^3) with (τ*Cmod α) by (rewrite <- αmod2; ring).
 approx.
Qed.

Lemma residue2_400_upper : residue 2 LimCase2.roots 400 < / 10^31.
Proof.
 rewrite residue2_eqn.
 change (400)%nat with (2*200)%nat. rewrite pow_mult, αmod2.
 apply Rmult_lt_reg_r with (10^31). apply pow_lt; lra.
 rewrite Rinv_l. 2:{ apply pow_nonzero. lra. }
 replace (10^31) with (Q2R (10^31)).
 2:{ replace 10 with (Q2R 10). now rewrite <- Q2R_pow. apply Q2R_IZR. }
 rewrite (Rmult_comm rest), Rmult_assoc.
 apply Rlt_trans with (0.6824^200 * (rest * Q2R (10 ^ 31))); [|approx].
 apply Rmult_lt_compat_r. approx.
 apply Rpow_lt_compat_r. lia. approx. approx.
Qed.

#[local] Instance sup_deltas_approx :
  Approx 0.8541871799283042119835815401526 (sup_deltas' 2)
         0.8541871799283042119835815401528.
Proof.
 split.
 - eapply Rle_trans;
   [|apply (MaxDeltas_below_lim' 2 lia roots) with (p:=400%nat)].
   approx. apply roots_sorted. unfold roots, Cnth; simpl; approx.
 - eapply Rle_trans;
   [apply (sup_deltas_upper 2 lia roots) with (p:=400%nat)|].
   apply roots_sorted. unfold roots, Cnth; simpl; approx.
   eapply Rle_trans;
   [apply Rplus_le_compat_l; apply Rlt_le; apply residue2_400_upper|].
   approx.
Qed.

(* Print Assumptions sup_deltas_approx. *)

(* Current final precision : slightly below 1O^-30 *)

#[local] Instance mindeltas_400 :
  Approx (-0.708415898743967960305146324178772) (MinDeltas 2 400)
         (-0.708415898743967960305146324178770).
Proof.
 apply NN.mindeltas_approx. lia. now vm_compute.
Qed.

#[local] Instance inf_deltas_approx :
  Approx (-0.7084158987439679603051463241789) (inf_deltas' 2)
         (-0.7084158987439679603051463241787).
Proof.
 split.
 - eapply Rle_trans;
   [|apply (inf_deltas_lower 2 lia roots) with (p:=400%nat)].
   2:apply roots_sorted. 2:unfold roots, Cnth; simpl; approx.
   eapply Rle_trans;
   [|apply Rplus_le_compat_l, Ropp_le_contravar, Rlt_le;
     apply residue2_400_upper].
   approx.
 - eapply Rle_trans;
   [apply (MinDeltas_above_lim' 2 lia roots) with (p:=400%nat)|].
   apply roots_sorted. unfold roots, Cnth; simpl; approx. approx.
Qed.

Lemma diff_bound n :
 -0.7084158987439679603051463241789 <= diff 2 n <= 0.8541871799283042119835815401528.
Proof.
 split.
 - apply Rle_trans with (inf_deltas' 2). approx.
   apply diff_ge_inf' with LimCase2.roots. lia. apply roots_sorted.
   unfold roots, Cnth; simpl; approx.
 - apply Rle_trans with (sup_deltas' 2).
   apply diff_le_sup' with (LimCase2.roots). lia. apply roots_sorted.
   unfold roots, Cnth; simpl; approx. approx.
Qed.

Lemma abs_diff_bound n : Rabs (diff 2 n) <= 0.8541871799283042119835815401528.
Proof.
 apply Rabs_le. generalize (diff_bound n). lra.
Qed.

(** In particular, |diff 2 n| is always strictly less than 1. *)

Lemma diff_lt_1 n : Rabs (diff 2 n) < 1.
Proof.
 eapply Rle_lt_trans. apply abs_diff_bound. lra.
Qed.

(* Print Assumptions diff0_lt_1. *)

(** Even the sup of |diff 2 n| is strictly less than 1. *)

Lemma sup_diff_lt_1 :
 Rbar.Rbar_lt (Sup_seq (fun n => Rabs (diff 2 n))) 1.
Proof.
 apply Rbar.Rbar_le_lt_trans with (Sup_seq (fun _ => 0.9)).
 - apply Sup_seq_le. intros n. simpl.
   eapply Rle_trans. apply abs_diff_bound. lra.
 - replace (Sup_seq _) with (Rbar.Finite 0.9); simpl. approx.
   symmetry. apply is_sup_seq_unique. apply is_sup_seq_const.
Qed.

(** Consequences of the bounded discrepancies *)

Lemma h_alt n : INR (h n) = τ*n + diff 2 n.
Proof.
 unfold diff. fold τ. fold h. lra.
Qed.

Lemma h_natpart_or n : h n = nat_part (τ*n) \/ h n = S (nat_part (τ*n)).
Proof.
assert (-1 < τ*n - h n < 1).
{ rewrite h_alt.
  assert (H := diff_lt_1 n).
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
        assert (Dp := diff_lt_1 p).
        assert (Dn := diff_lt_1 n).
        assert (Dpn := diff_lt_1 (p+n)).
        rewrite Rcomplements.Rabs_lt_between in *.
        simpl. lra.
      * rewrite !S_INR, !plus_INR. rewrite !h_alt, plus_INR.
        assert (Dp := diff_lt_1 p).
        assert (Dn := diff_lt_1 n).
        assert (Dpn := diff_lt_1 (p+n)).
        rewrite Rcomplements.Rabs_lt_between in *.
        simpl. lra.
Qed.

(* Print Assumptions h_quasiadd. *)


(** ** Discrepancies for (h^^2). *)

Definition diffh2 n := (h^^2) n - τ^2 * n.

Lemma diffh2_alt n : diffh2 n = diff 2 (h n) + τ * diff 2 n.
Proof.
 unfold diffh2, diff. simpl. fold h. fold τ. lra.
Qed.

Lemma diffh2_bounds n : -1.1920 <= diffh2 n <= 1.4372.
Proof.
 rewrite diffh2_alt.
 generalize (diff_bound n) (diff_bound (h n)) τ_approx. unfold Approx. nra.
Qed.

(** Distance between [h^^2] and [nat_part (τ^2 * n)].
    This distance may be "+2", for instance for n=1235.
    (TODO: direct estimate for diffh2_bounds (not just through diffh2_alt)
     to show that the lower bound is above -1 and hence
     [nat_part (τ^2 * n) <= (h^^2) n] (e.g. no "-1" below)) *)

Lemma h2_natpart_bound (n:nat) :
 (nat_part (τ^2 * n) -1 <= (h^^2) n <= 2 + nat_part (τ^2 * n))%nat.
Proof.
 split.
 - assert (nat_part (τ^2 * n) < 2 + (h^^2) n)%nat; try lia.
   { apply nat_part_lt. split.
     - apply Rmult_le_pos. approx. apply pos_INR.
     - rewrite plus_INR. replace (INR 2) with 2 by auto.
       generalize (diffh2_bounds n). unfold diffh2. simpl. lra. }
 - assert ((h^^2) n - 2 <= nat_part (τ^2 * n))%nat; try lia.
   { apply nat_part_le.
     - apply Rmult_le_pos. approx. apply pos_INR.
     - destruct (Nat.le_gt_cases 4 n) as [LE|LT].
       + assert (LE' := fs_mono 2 2 LE).
         rewrite minus_INR by trivial.
         replace (INR 2) with 2 by auto.
         generalize (diffh2_bounds n). unfold diffh2. simpl. lra.
       + destruct n. simpl; lra.
         destruct n. simpl. approx.
         destruct n. simpl. approx.
         destruct n. simpl. approx.
         lia. }
Qed.


(** ** Occurrences of letters in morphic word [Words.qseq 2]

    See now the much more general results in Freq.v.

    For a finite word [w], the frequency of letter [a] is
    [nbocc a w / length w]. For infinite words, the frequency
    of a letter (if it exists) is the limit of frequencies for
    ever-growing finite prefixes of the infinite word.

    Here for [Words.qseq 2], the frequencies of letters [0],[1],[2]
    will be respectively [τ^3],[τ^4],[τ^2] (another numbering
    of letters would make that more uniform). For proving that and
    even more, we now consider the following differences :
*)

Definition Diff0 w := τ^3 * length w - nbocc 0 w.
Definition Diff1 w := τ^4 * length w - nbocc 1 w.
Definition Diff2 w := τ^2 * length w - nbocc 2 w.

Definition diff0 n := Diff0 (take n (qseq 2)).
Definition diff1 n := Diff1 (take n (qseq 2)).
Definition diff2 n := Diff2 (take n (qseq 2)).

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
 rewrite take_nth by trivial. apply qseq_letters.
Qed.

(** Expressing diff0 and diff2 in terms of [h] and [h^^2] *)

Lemma diff0_alt n : diff0 n = h n - τ * n.
Proof.
 unfold diff0, Diff0. rewrite take_length.
 rewrite <- count_nbocc.
 rewrite τ3. rewrite Rmult_minus_distr_r.
 rewrite <- (f_count_0 2 n) at 1 by easy. fold h. rewrite plus_INR. lra.
Qed.

Lemma diff0_alt' n : diff0 n = diff 2 n.
Proof.
 apply diff0_alt.
Qed.

Lemma diff2_alt n : diff2 n = τ^2 * n - (h^^2) n.
Proof.
 unfold diff2, Diff2. rewrite take_length.
 rewrite <- count_nbocc.
 now rewrite fs_count_q.
Qed.

Lemma diff2_alt' n : diff2 n = - diffh2 n.
Proof.
 rewrite diff2_alt. unfold diffh2. lra.
Qed.

(** Equations giving Diff0 and Diff1 after a substitution [qsubst 2].
    Note : this could be stated via a matrix someday.
*)

Lemma Diff0_qsubst2 w : Diff0 (qsubstw 2 w) = τ * Diff2 w.
Proof.
 unfold Diff0, Diff2.
 rewrite len_qsubst, plus_INR.
 destruct (nbocc_qsubst2 w) as (-> & _ & _).
 ring_simplify. unfold Rminus. rewrite Rplus_assoc. f_equal.
 rewrite τ3. lra.
Qed.

Lemma Diff2_qsubst2 w :
  List.Forall (fun a => a <= 2)%nat w ->
  Diff2 (qsubstw 2 w) = - τ^2 * Diff2 w - Diff0 w.
Proof.
 intros H.
 unfold Diff0, Diff2.
 rewrite len_qsubst.
 destruct (nbocc_qsubst2 w) as (_ & _ & ->).
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

Lemma diff0_A n : diff0 (A 2 n) = 2 * Re(coefdA 2 α * α^n).
Proof.
 apply RtoC_inj.
 rewrite diff0_alt. unfold h. rewrite f_A.
 rewrite (Equation_dA 2 roots). 2:apply roots_sorted. 2:lia.
 unfold roots. cbn -[Cmult Cpow]. rewrite Cplus_0_r.
 change αbar with (Cconj α).
 rewrite coefdA_conj, <- Cpow_conj, <- Cconj_mult_distr, re_alt'.
 now rewrite RtoC_mult.
Qed.

Lemma diff2_A n : diff2 (A 2 n) = 2 * Re(coefdA 2 α / αbar * α^n).
Proof.
 unfold Cdiv. rewrite <- Cmult_assoc, (Cmult_comm (/_)).
 replace (α^n * _)%C with (α^(n+1) * / τ)%C.
 2:{ rewrite <- αmod2, Cmod2_conj. change (Cconj α) with αbar.
     rewrite Nat.add_1_r, Cpow_S. field. split.
     intros [= H _]. revert H. approx.
     intros [= H _]. revert H. approx. }
 rewrite Cmult_assoc, <-RtoC_inv, re_scal_r.
 rewrite <- Rmult_assoc. rewrite <- diff0_A.
 apply Rmult_eq_reg_r with τ; try approx.
 rewrite Rmult_assoc, Rinv_l, Rmult_1_r by approx.
 rewrite diff2_alt, diff0_alt.
 unfold h. rewrite f_A, fs_A. replace (n+1-1)%nat with n by lia.
 rewrite Nat.add_1_r. simpl. rewrite plus_INR. ring_simplify.
 rewrite τ3. ring.
Qed.

(** NB: I previously used the alternative expression
    (αbar*(α*(τ^2-1)-τ^3)/(α-αbar)) for (coefdA 2 α).
    I did once a tedious proof of equality between these two expressions. *)

Lemma re_coefdA : 2*Re (coefdA 2 α) = 1-τ.
Proof.
 generalize (diff0_A 0). rewrite Cpow_0_r, Cmult_1_r, diff0_alt.
 cbn -[Re]. lra.
Qed.

Lemma lim_diff0_div_n : is_lim_seq (fun n => diff0 n / n) 0.
Proof.
 eapply is_lim_seq_bound. intros n. rewrite diff0_alt'.
 apply Rlt_le. apply diff_lt_1.
Qed.

Lemma frequency_0 : is_lim_seq (fun n => count (qseq 2) 0 n / n) (τ^3).
Proof.
 apply Freq.freq_qseq_0. lia.
Qed.

Lemma Lim_h_div_n : is_lim_seq (fun n => h n / n) τ.
Proof.
 apply Freq.Lim_fq_div_n.
Qed.

(** Bounds for [diff2 n], giving the frequency of letter 2,
    and the limit of [h^^2]. Less interesting, the bound is in [1..2]. *)

Lemma diff2_lt_2 n : Rabs (diff2 n) < 2.
Proof.
 rewrite diff2_alt', Rabs_Ropp. apply Rcomplements.Rabs_lt_between.
 generalize (diffh2_bounds n); lra.
Qed.

(** Having this finite bound is enough to prove that the frequency
    of letter 2 is [τ^2] and that [(h^^2)(n) / n] converges towards [τ^2]. *)

Lemma lim_diff2_div_n : is_lim_seq (fun n => diff2 n / n) 0.
Proof.
 eapply is_lim_seq_bound. intros n. apply Rlt_le. apply diff2_lt_2.
Qed.

Lemma frequency_2 : is_lim_seq (fun n => count (qseq 2) 2 n / n) (τ^2).
Proof.
 apply is_lim_seq_ext_loc with (fun n => τ^2 - diff2 n / n).
 - exists 1%nat. intros n Hn.
   unfold diff2, Diff2. rewrite take_length.
   rewrite <- count_nbocc. field. apply not_0_INR; lia.
 - replace (τ^2) with (τ^2 + -0) at 1 by lra.
   apply is_lim_seq_plus'. apply is_lim_seq_const.
   apply is_lim_seq_opp'. apply lim_diff2_div_n.
Qed.

Lemma frequency_1 : is_lim_seq (fun n => count (qseq 2) 1 n / n) (τ^4).
Proof.
 apply is_lim_seq_ext_loc with (fun n => τ^4 + diff0 n / n + diff2 n / n).
 - exists 1%nat. intros n Hn.
   field_simplify; try (apply not_0_INR; lia). f_equal.
   rewrite Rplus_assoc.
   replace (diff0 n + diff2 n) with (-diff1 n)
     by (generalize (diff012 n); lra).
   unfold diff1, Diff1. rewrite take_length.
   rewrite <- count_nbocc. field.
 - replace (τ^4) with (τ^4 + 0 + 0) at 1 by lra.
   apply is_lim_seq_plus';[ apply is_lim_seq_plus'|];
    trivial using is_lim_seq_const, lim_diff0_div_n, lim_diff2_div_n.
Qed.

Lemma Lim_h2_div_n : is_lim_seq (fun n => (h^^2) n / n) (τ^2).
Proof.
 apply Freq.Lim_fqj_div_n.
Qed.


(** Appendix: the coefficients coef_μ and coef_α and [Cconj coef_α]
    are the roots of the polynomial [X^3-X^2-(12/31)*X-1/31].
    For proving that, we need first some more identities about
    these coefficients. *)

Module Appendix.

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
   apply Rmult_le_pos; approx. }
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
 rewrite det_eqn. rewrite Cmult_integral. intros [[=E]|[=E]]; try lra.
 apply sqrt_eq_0 in E; lra.
Qed.

Lemma coef_μ_eqn : coef_μ = 2 * μ^4 * im_α / sqrt 31.
Proof.
  apply RtoC_inj. unfold coef_μ. rewrite coef_mu_ok.
  unfold coefA. fold μ.
  replace (μ^3)%C with (μ^4 * μ / μ^2)%C.
  2:{ field. injection; approx. }
  assert (NZ : √31 <> 0) by (intro E; apply sqrt_eq_0 in E; lra).
  rewrite !RtoC_div, !RtoC_mult, <- !RtoC_pow.
  rewrite (Cmult_comm 2). unfold Cdiv. rewrite <- !Cmult_assoc. f_equal.
  rewrite !Cmult_assoc.
  change (coefB 2 μ = 2 * im_α / √ 31)%C.
  change (RtoC μ) with (roots @ 0).
  rewrite <- (coefs0_coefB 2 _ roots_sorted).
  apply Cmult_eq_reg_r with (Ci * RtoC (√31))%C.
  2:{ intros E. apply Cmult_integral in E.
      destruct E as [[= E]|[= E]]; [lra|easy]. }
  unfold Cdiv. field_simplify.
  2:{ injection; lra. }
  change im_α with (Im α).
  rewrite <- im_alt'. rewrite <- Cmult_assoc, <- det_eqn.
  unfold det.
  generalize (coefs0_eqn 2 _ roots_sorted 0 lia).
  unfold Cnth. simpl. rewrite Cmult_1_r, !Cmult_assoc. intros ->.
  now rewrite Cmult_1_l.
Qed.

Lemma coef_α_eqn : (coef_α = α^4 * (αbar - μ) / det)%C.
Proof.
  unfold coef_α, coefA.
  replace (α^3)%C with (α^4 * α / α^2)%C.
  2:{ field. intros [= E _]. revert E. approx. }
  unfold Cdiv. rewrite <- !Cmult_assoc. f_equal.
  rewrite !Cmult_assoc.
  change (coefB 2 α = (αbar - μ) * / det)%C.
  change α with (roots @ 1).
  rewrite <- (coefs0_coefB 2 _ roots_sorted).
  apply Cmult_eq_reg_r with det. 2:apply det_nz.
  unfold Cdiv. rewrite <- Cmult_assoc. rewrite Cinv_l. 2:apply det_nz.
  rewrite Cmult_1_r.
  replace det with ((α-μ)*(α-αbar)*(αbar-μ))%C by (unfold det; ring).
  generalize (coefs0_eqn 2 _ roots_sorted 1 lia).
  unfold Cnth. simpl. rewrite Cmult_1_r, !Cmult_assoc. intros ->. ring.
Qed.

Lemma coef_sum : (coef_μ+coef_α+coef_αbar = 1)%C.
Proof.
 rewrite <- coefs_eqn1, RtoC_plus, RtoC_mult, re_alt, coef_αbar_conj.
 field.
Qed.

Lemma coef_prod : (coef_μ * coef_α * coef_αbar = 1/31)%C.
Proof.
 rewrite coef_μ_eqn, coef_αbar_conj, coef_α_eqn.
 rewrite Cdiv_conj, Cconj_mult_distr, Cconj_minus_distr, Cpow_conj
  by apply det_nz. rewrite Cconj_R.
 replace (_*_)%C with (-(μ*α*αbar)^4* det/det^3)%C.
 2:{ unfold det at 1. change im_α with (Im α).
     rewrite RtoC_div, !RtoC_mult, im_alt.
     rewrite <- RtoC_pow.
     replace (Cconj αbar) with α.
     2:{ unfold α, αbar, Cconj. simpl. f_equal. lra. }
     change (Cconj α) with αbar.
     replace (Cconj det) with (-det)%C.
     2:{ rewrite det_eqn. rewrite Cconj_mult_distr, Cconj_R. lca. }
     rewrite det_eqn. field.
     split; injection as E; try apply sqrt_eq_0 in E; lra. }
 rewrite roots_prod. field_simplify. rewrite det2. lca. apply det_nz.
Qed.

Ltac simpl_root := repeat (autorewrite with root; ring_simplify).
#[local] Hint Rewrite μ_is_root α_is_root αbar_is_root : root.

Lemma μ4 : (μ^4 = 1 + μ + μ^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

Lemma α4 : (α^4 = 1 + α + α^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

#[local] Hint Rewrite μ4 α4 : root.

Lemma μ5 : (μ^5 = 1 + μ + 2*μ^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

Lemma α5 : (α^5 = 1 + α + 2*α^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

#[local] Hint Rewrite μ5 α5 : root.

Lemma μ6 : (μ^6 = 2 + μ + 3*μ^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

Lemma α6 : (α^6 = 2 + α + 3*α^2)%C.
Proof. rewrite Cpow_S. now simpl_root. Qed.

#[local] Hint Rewrite μ6 α6 : root.

Lemma coef_μ2 : (31 * coef_μ^2 = 15*μ^2 + 7*μ + 11)%C.
Proof.
 unfold coef_μ, coef_mu. fold μ.
 rewrite RtoC_div. unfold Cdiv. rewrite Cpow_mul_l.
 rewrite <- RtoC_pow, <- Cpow_mult. simpl Nat.mul.
 set (x := RtoC (Rminus _ _)).
 assert (NZ : x <> 0) by (injection; approx).
 rewrite Cpow_inv.
 apply Cmult_eq_reg_r with (x^2)%C; try apply Cpow_nonzero; trivial.
 rewrite <- !Cmult_assoc. rewrite Cinv_l; try apply Cpow_nonzero; trivial.
 unfold x. clear NZ x.
 rewrite RtoC_minus, RtoC_mult.
 change (RtoC (INR 2)) with (RtoC 2).
 replace (RtoC (INR 3)) with (RtoC 3) by lca.
 now simpl_root.
Qed.

Lemma coef_α2 : (31 * coef_α^2 = 15*α^2 + 7*α + 11)%C.
Proof.
 unfold coef_α, coefA.
 unfold Cdiv. rewrite Cpow_mul_l.
 rewrite <- Cpow_mult. simpl Nat.mul.
 set (x := Cminus _ _).
 assert (NZ : x <> 0).
 { intros E. unfold x in E. apply Cminus_eq_0 in E.
   assert (E' : Im (3%nat * α) = 0) by now rewrite E, im_RtoC.
   rewrite im_scal_l in E'. revert E'. approx. }
 rewrite Cpow_inv.
 apply Cmult_eq_reg_r with (x^2)%C; try apply Cpow_nonzero; trivial.
 rewrite <- !Cmult_assoc. rewrite Cinv_l; try apply Cpow_nonzero; trivial.
 unfold x. clear NZ x.
 change (RtoC (INR 2)) with (RtoC 2).
 replace (RtoC (INR 3)) with (RtoC 3) by lca.
 now simpl_root.
Qed.

Lemma coef_αbar2 : (31 * coef_αbar^2 = 15*αbar^2 + 7*αbar + 11)%C.
Proof.
 rewrite coef_αbar_conj.
 rewrite <- Cpow_conj. rewrite <- (Cconj_R 31).
 rewrite <- Cconj_mult_distr, coef_α2.
 now rewrite !Cconj_plus_distr, !Cconj_mult_distr, Cpow_conj, !Cconj_R.
Qed.

Lemma coef_squares : (coef_μ^2+coef_α^2+coef_αbar^2 = 55/31)%C.
Proof.
 apply Cmult_eq_reg_l with (RtoC 31); [|injection; lra].
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
 rewrite !RtoC_minus, !RtoC_mult, !RtoC_div, <- !RtoC_pow.
 rewrite <- poly_coefs. ring.
Qed.

Lemma coef_α_poly : (coef_α^3 - coef_α^2 - (12/31)*coef_α - 1/31 = 0)%C.
Proof.
 rewrite <- poly_coefs. ring.
Qed.

End Appendix.
