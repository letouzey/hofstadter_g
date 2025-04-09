From Coq Require Import Arith Lia NArith Reals Lra.
From Hofstadter.HalfQuantum Require Import Complex.
Require Import MoreTac MoreFun MoreList MoreReals MoreLim MoreComplex MoreSum.
Require Import DeltaList Approx.
Require Import GenFib GenG GenAdd Words Mu ThePoly Freq Discrepancy.
Require WordGrowth.
Local Open Scope C.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * Studying case k=3

   We focus here on the case k=3, compute the complex roots of [X^3-X^2-1],
   and express (A 3 n) in term of combinations of powers of these roots.
   Then we study the frequencies in [Words.kseq 3], and the behaviour of
   function [h] (i.e. [f 3] ie Hofstadter's H).
*)

Definition μ := mu 3.
Definition τ := tau 3.

Definition re_α := (1 - μ)/2.
Definition im_α := sqrt (τ * (3+τ))/2.

Definition α : C := (re_α, im_α).
Definition αbar : C := (re_α, - im_α).

Lemma τ_μ : τ = /μ.
Proof.
 easy.
Qed.

Lemma μ_τ : μ = /τ.
Proof.
 apply tau_inv.
Qed.

Lemma τ3 : τ^3 = 1 - τ.
Proof.
 rewrite <- (tau_carac 3) by easy. fold τ. lra.
Qed.

Lemma τ234 : τ^2 + τ^3 + τ^4 = 1.
Proof.
 ring [τ3].
Qed.

#[local] Instance μ_approx : Approx 1.465571231876 μ 1.465571231877.
Proof.
 red. unfold μ. generalize mu_3. lra.
Qed.

#[local] Instance τ_approx : Approx 0.6823278038280 τ 0.6823278038281.
Proof.
 red. unfold τ. generalize tau_3. lra.
Qed.

#[local] Instance τ2_approx : Approx 0.465570 (τ^2) 0.465572.
Proof. approx. Qed.

Lemma re_α_alt : re_α = - τ^2 / 2.
Proof.
 unfold re_α. rewrite μ_τ. field [τ3]. approx.
Qed.

Lemma im_α_2 : im_α ^ 2 = τ * (3+τ) / 4.
Proof.
 unfold im_α, Rdiv. rewrite Rpow_mult_distr, pow2_sqrt by approx. lra.
Qed.

Lemma αmod2 : (Cmod α)^2 = τ.
Proof.
 unfold Cmod.
 rewrite pow2_sqrt.
 2: generalize (pow2_ge_0 (fst α)) (pow2_ge_0 (snd α)); lra.
 unfold α; simpl. ring_simplify [im_α_2 re_α_alt]. field [τ3].
Qed.

Lemma τ_as_μ : τ = μ*(μ-1).
Proof.
 rewrite μ_τ. field [τ3]. approx.
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
 ctor. unfold μ. now rewrite (mu_carac 3 lia).
Qed.

Lemma α_is_root : (α^3 = α^2 + 1)%C.
Proof.
 simpl. rewrite !Cmult_1_r. unfold α. unfold Cmult; simpl.
 unfold Cplus; simpl. f_equal; ring_simplify.
 - rewrite im_α_2, re_α_alt. field [τ3].
 - change (im_α ^ 3) with (im_α * im_α^2).
   rewrite im_α_2, re_α_alt. field [τ3].
Qed.

Lemma αbar_is_root : (αbar^3 = αbar^2 + 1)%C.
Proof.
 change αbar with (Cconj α).
 rewrite <- !Cpow_conj. rewrite α_is_root. now conj_in.
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
 ctor. f_equal. rewrite τ_as_μ. ring.
Qed.

Lemma roots_sum2 : (μ^2 + α^2 + αbar^2 = 1)%C.
Proof.
 replace 1%C with (1^2-2*0)%C by lca.
 rewrite <- roots_sum, <- sigma2_nul. ring.
Qed.

Definition roots := [RtoC μ; α; αbar].

Lemma roots_sorted : SortedRoots 3 roots.
Proof.
 split.
 - unfold roots, ThePoly. simpl.
   apply MorePoly.eq_Peq. f_equal;[|f_equal;[|f_equal]].
   + replace (-1)%C with (-(1))%C by ring. rewrite <- roots_prod at 1. ring.
   + ring_simplify. rewrite <- sigma2_nul. ring.
   + replace (-1)%C with (-(1))%C by ring. rewrite <- roots_sum at 1. ring.
   + f_equal; lca.
 - do 2 constructor.
   + repeat constructor.
   + constructor. right. unfold α, αbar. simpl. split; trivial. approx.
   + left. unfold α. simpl. approx.
Qed.

(** Explicit decomposition of [A 3 n] into a linear combination
    of root powers. Now just an instance of [ThePoly.Equation_A]. *)

Definition coef_μ : R := coef_mu 3.
Definition coef_α : C := coefA 3 α.
Definition coef_αbar : C := coefA 3 αbar.

#[local] Instance coef_μ_bound : Approx 1.3134 coef_μ 1.3135.
Proof.
 approx.
Qed.

Lemma coef_αbar_conj : coef_αbar = Cconj coef_α.
Proof.
 unfold coef_αbar, coef_α. change αbar with (Cconj α). apply coefA_conj.
Qed.

Lemma A3_eqn n : INR (A 3 n) = coef_μ * μ ^n + 2 * Re (coef_α * α^n).
Proof.
 apply RtoC_inj. unfold coef_μ.
 rtoc. rewrite re_alt, coef_mu_ok.
 field_simplify. fold μ.
 conj_in. change (Cconj α) with αbar.
 rewrite <- coef_αbar_conj.
 rewrite (ThePoly.Equation_A 3 roots roots_sorted). simpl.
 fold coef_α coef_αbar. ring.
Qed.

Lemma A3_div_μ_n n : A 3 n / μ ^n = coef_μ + 2 * Re (coef_α * (α/μ)^n).
Proof.
 assert (μ <> 0) by approx.
 assert (μ^n <> 0). { now apply pow_nonzero. }
 unfold Cdiv. rewrite Cpow_mult_l, Cpow_inv.
 rewrite Cmult_assoc. ctor. rewrite re_scal_r.
 rewrite A3_eqn. field; trivial.
Qed.

Lemma Cmod_α_μ : Cmod (α/μ) < 1.
Proof.
 assert (0 < μ) by approx.
 assert (0 < τ) by approx.
 apply Rlt_pow2_inv; try lra.
 rewrite Cmod_div, Cmod_R, Rabs_right by lra.
 unfold Rdiv. rewrite Rpow_mult_distr. rewrite αmod2. approx.
Qed.

Lemma Lim_A3_div_μ_n : is_lim_seq (fun n => A 3 n / μ ^ n) coef_μ.
Proof.
 apply ThePoly.A_div_pow_mu_limit.
Qed.

Lemma Lim_A3_ratio : is_lim_seq (fun n => A 3 (S n) / A 3 n) μ.
Proof.
 apply Freq.A_ratio.
Qed.

(** Equations about the coefficients *)

Lemma coefs_eqn1 : coef_μ + 2 * Re coef_α = 1.
Proof.
 change 1 with (INR (A3 0)). rewrite A3_eqn.
 simpl pow. simpl Cpow. rewrite Cmult_1_r. ring.
Qed.

Lemma coefs_eqn2 : coef_μ * μ + 2 * Re (coef_α * α) = 2.
Proof.
 change 2 with (INR (A3 1)) at 2. rewrite A3_eqn.
 simpl pow. simpl Cpow. rewrite !Cmult_1_r. ring.
Qed.

Lemma coefs_eqn3 : coef_μ * μ^2 + 2 * Re (coef_α * α^2) = 3.
Proof.
 replace 3 with (INR (A3 2)) by (simpl; lra). now rewrite A3_eqn.
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
 - apply Rlt_le. apply Mu.Ptau_lower; [easy | approx | approx].
 - apply Rlt_le. apply Mu.Ptau_upper; [easy | approx | approx].
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
   unfold τ. rewrite <- Ptau_lt1_iff; try easy.
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
     field_simplify in LT. 2:{ try (*compat*) revert LT. apply IZR_neq. lia. }
     rewrite !pow_IZR, <- !mult_IZR, <- plus_IZR in LT. apply lt_IZR in LT.
     simpl Z.of_nat in LT. now ring_simplify.
 - destruct (Z.le_gt_cases 0 r).
   { split; intros H'; try lia. exfalso. apply IZR_lt in NEG.
     apply IZR_le in H. generalize (tau_itvl 3). fold τ. nra. }
   rewrite Rminus_lt_0. replace (_ - _)%R with (IZR (-r) - τ * IZR (-s))%R.
   2:{ rewrite !opp_IZR. lra. }
   rewrite <- Rminus_lt_0.
   rewrite Rcomplements.Rlt_div_r by (apply IZR_lt; lia).
   unfold τ. rewrite <- Ptau_gt1_iff; try easy.
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
     field_simplify in LT. 2:{ try (*compat*) revert LT. apply IZR_neq. lia. }
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

(** Simultaneous computations of (diff 3 (A3 n)) and (MaxDeltas 3) *)

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
  to_R d0 = diff 3 (A3 n) /\
  to_R d1 = diff 3 (A3 (n+1)) /\
  to_R d2 = diff 3 (A3 (n+2)) /\
  to_R m0 = MaxDeltas 3 n /\
  to_R m1 = MaxDeltas 3 (n+1) /\
  to_R m2 = MaxDeltas 3 (n+2).
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
     simpl. rewrite (Nat.add_comm (A3 _)).
     rewrite diff_A_A by lia. f_equal. f_equal. f_equal. lia.
   + rewrite max_ok, add_ok. simpl. f_equal; trivial.
     f_equal; trivial. rewrite IH1'. f_equal. lia.
Qed.

Lemma maxdeltas_spec (n:nat) : (2 <= n)%nat ->
  MaxDeltas 3 n = to_R (maxdeltas (N.of_nat n)).
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
 -> Approx a (MaxDeltas 3 n) b.
Proof.
 intros Hn H. rewrite (maxdeltas_spec n Hn).
 eapply approx_trans; [apply to_QQ_ok| | ]; eapply checkapprox_ok; eauto.
Qed.

Lemma min_loop_spec (n:nat) :
  let '(Buffer d0 d1 d2 m0 m1 m2) := min_loop (N.of_nat n + 2) in
  to_R d0 = diff 3 (A3 n) /\
  to_R d1 = diff 3 (A3 (n+1)) /\
  to_R d2 = diff 3 (A3 (n+2)) /\
  to_R m0 = MinDeltas 3 n /\
  to_R m1 = MinDeltas 3 (n+1) /\
  to_R m2 = MinDeltas 3 (n+2).
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
     simpl. rewrite (Nat.add_comm (A3 _)).
     rewrite diff_A_A by lia. f_equal. f_equal. f_equal. lia.
   + rewrite min_ok, add_ok. simpl. f_equal; trivial.
     f_equal; trivial. rewrite IH1'. f_equal. lia.
Qed.

Lemma mindeltas_spec (n:nat) : (2 <= n)%nat ->
  MinDeltas 3 n = to_R (mindeltas (N.of_nat n)).
Proof.
 intros Hn. unfold mindeltas.
 assert (H := min_loop_spec (n-2)).
 replace (N.of_nat (n-2) + 2)%N with (N.of_nat n) in H by lia.
 destruct (min_loop _); simpl in *.
 replace (n-2+2)%nat with n in H by lia. symmetry. apply H.
Qed.

Lemma mindeltas_approx n a b : (2 <= n)%nat ->
 checkapprox a b (to_QQ (mindeltas (N.of_nat n))) = true
 -> Approx a (MinDeltas 3 n) b.
Proof.
 intros Hn H. rewrite (mindeltas_spec n Hn).
 eapply approx_trans; [apply to_QQ_ok| | ]; eapply checkapprox_ok; eauto.
Qed.

End NN.

(** Taking n=400 is enough to get 32 decimal digits of precision *)

#[local] Instance maxdeltas_400 :
  Approx 0.854187179928304211983581540152665 (MaxDeltas 3 400)
         0.854187179928304211983581540152667.
Proof.
 apply NN.maxdeltas_approx. lia. now vm_compute.
Qed.

Definition precision '(r,s) :=
 let '(Qmake a b) := Qminus s r in
 ((Z.log2 a - Z.log2 (Z.pos b))*100/332)%Z.

(* Compute precision maxdeltas_400_QQ. *)

(** Now we bound (residue 3 roots 400). *)

Definition rest := 2*Cmod (coefdA 3 α)/(1 - Cmod α^3).

Lemma residue3_eqn n :
  residue 3 roots n = rest * Cmod α^n.
Proof.
 unfold residue, roots. cbn -[pow].
 change αbar with (Cconj α). rewrite coefdA_conj. conj_out.
 rewrite Rplus_0_r, <- double.
 unfold rest. field. approx.
Qed.

#[local] Instance : Approx 1.111 rest 1.112.
Proof.
 unfold rest. unfold coefdA, coefA. fold τ.
 rewrite !INR_IZR_INZ. cbn -[pow Cpow].
 replace (_ / _ * _)%C with (α ^ 2 / (3 * α - 2) * (1 - τ * α))%C.
 2:{ unfold Cdiv. replace (3-1)%C with 2%C by lca.
     rewrite <- (Cinv_l α). ring.
     intros [= E _]. revert E. approx. }
 unfold Cdiv. rewrite !Cmod_mult, Cmod_pow, αmod2, Cmod_inv.
 replace (Cmod α^3) with (τ*Cmod α) by (rewrite <- αmod2; ring).
 approx.
Qed.

Lemma residue3_400_upper : residue 3 roots 400 < / 10^33.
Proof.
 rewrite residue3_eqn.
 change (400)%nat with (2*200)%nat. rewrite pow_mult, αmod2.
 apply Rmult_lt_reg_r with (10^33). apply pow_lt; lra.
 rewrite Rinv_l. 2:{ apply pow_nonzero. lra. }
 replace (10^33) with (Q2R (10^33)).
 2:{ replace 10 with (Q2R 10). now rewrite <- Q2R_pow. apply Q2R_IZR. }
 rewrite (Rmult_comm rest), Rmult_assoc.
 apply Rlt_trans with (0.6824^200 * (rest * Q2R (10 ^ 33))); [|approx].
 apply Rmult_lt_compat_r. approx.
 apply Rpow_lt_compat_r. lia. approx. approx.
Qed.

#[local] Instance sup_deltas_approx :
  Approx 0.854187179928304211983581540152665 (sup_deltas' 3)
         0.854187179928304211983581540152668.
Proof.
 split.
 - eapply Rle_trans;
   [|apply (MaxDeltas_below_lim' 3 lia roots) with (p:=400%nat)].
   approx. apply roots_sorted. unfold roots, Cnth; simpl; approx.
 - eapply Rle_trans;
   [apply (sup_deltas_upper 3 lia roots) with (p:=400%nat)|].
   apply roots_sorted. unfold roots, Cnth; simpl; approx.
   eapply Rle_trans;
   [apply Rplus_le_compat_l; apply Rlt_le; apply residue3_400_upper|].
   approx.
Qed.

(* Print Assumptions sup_deltas_approx. *)

(* Current final precision : slightly below 1O^-32 *)

#[local] Instance mindeltas_400 :
  Approx (-0.708415898743967960305146324178772) (MinDeltas 3 400)
         (-0.708415898743967960305146324178770).
Proof.
 apply NN.mindeltas_approx. lia. now vm_compute.
Qed.

#[local] Instance inf_deltas_approx :
  Approx (-0.708415898743967960305146324178773) (inf_deltas' 3)
         (-0.708415898743967960305146324178770).
Proof.
 split.
 - eapply Rle_trans;
   [|apply (inf_deltas_lower 3 lia roots) with (p:=400%nat)].
   2:apply roots_sorted. 2:unfold roots, Cnth; simpl; approx.
   eapply Rle_trans;
   [|apply Rplus_le_compat_l, Ropp_le_contravar, Rlt_le;
     apply residue3_400_upper].
   approx.
 - eapply Rle_trans;
   [apply (MinDeltas_above_lim' 3 lia roots) with (p:=400%nat)|].
   apply roots_sorted. unfold roots, Cnth; simpl; approx. approx.
Qed.

Lemma diff_bound n :
 -0.708415898743967960305146324178773 <= diff 3 n <=
  0.854187179928304211983581540152668.
Proof.
 split.
 - apply Rle_trans with (inf_deltas' 3). approx.
   apply diff_ge_inf' with roots. lia. apply roots_sorted.
   unfold roots, Cnth; simpl; approx.
 - apply Rle_trans with (sup_deltas' 3).
   apply diff_le_sup' with roots. lia. apply roots_sorted.
   unfold roots, Cnth; simpl; approx. approx.
Qed.

Lemma abs_diff_bound n :
  Rabs (diff 3 n) <= 0.854187179928304211983581540152668.
Proof.
 apply Rabs_le. generalize (diff_bound n). lra.
Qed.

(** In particular, |diff 3 n| is always strictly less than 1. *)

Lemma diff_lt_1 n : Rabs (diff 3 n) < 1.
Proof.
 eapply Rle_lt_trans. apply abs_diff_bound. lra.
Qed.

(* Print Assumptions diff0_lt_1. *)

(** Even the sup of |diff 3 n| is strictly less than 1. *)

Lemma sup_diff_lt_1 :
 Rbar.Rbar_lt (Sup_seq (fun n => Rabs (diff 3 n))) 1.
Proof.
 apply Rbar.Rbar_le_lt_trans with (Sup_seq (fun _ => 0.9)).
 - apply Sup_seq_le. intros n. simpl.
   eapply Rle_trans. apply abs_diff_bound. lra.
 - replace (Sup_seq _) with (Rbar.Finite 0.9); simpl. approx.
   symmetry. apply is_sup_seq_unique. apply is_sup_seq_const.
Qed.

(** Consequences of the bounded discrepancies *)

Lemma h_alt n : INR (h n) = τ*n + diff 3 n.
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
        2:{ generalize (@f_nonzero 3 p) (@f_nonzero 3 n). fold h. lia. }
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

(** If we know whether n has a rank 0 (i.e. it has
    a low 1 in its decomposition), then we can be
    more precise concerning the bounds of [diff 3 n]. *)

Lemma diff_rank n :
  diff 3 n = diff 3 (S n) + match rank 3 n with Some O => τ | _ => τ-1 end.
Proof.
 destruct (@flat_rank_0 3 lia n) as (_,E).
 destruct (@step_rank_nz 3 lia n) as (_,E').
 unfold diff. fold τ. rewrite S_INR.
 destruct (rank 3 n) as [[|r]|].
 - rewrite E by easy. lra.
 - rewrite E' by easy. rewrite S_INR. lra.
 - rewrite E' by easy. rewrite S_INR. lra.
Qed.

Lemma diff_bound_rank0 n : rank 3 n = Some O ->
 -0.026088094915948632935662584467725 <= diff 3 n <=
  0.854187179928304211983581540152668.
Proof.
 intros H.
 split.
 - rewrite diff_rank, H.
   destruct (diff_bound (S n)) as (LE,_).
   destruct tau100_approx as (LE',_). unfold tau100 in *. simpl fst in *. nra.
 - apply diff_bound.
Qed.

Lemma diff_bound_ranknz n : rank 3 n <> Some O ->
 -0.708415898743967960305146324178773 <= diff 3 n <=
  0.536514983756323539353065279863717.
Proof.
 intros H.
 split.
 - apply diff_bound.
 - rewrite diff_rank. destruct (rank 3 n) as [[|r]|]; try easy;
   destruct (diff_bound (S n)) as (_,GE);
   destruct tau100_approx as (_,GE'); unfold tau100 in *; simpl snd in *; nra.
Qed.


(** ** Discrepancies for (h^^2). *)

Definition diffh2 n := (h^^2) n - τ^2 * n.

Lemma diffh2_alt n : diffh2 n = diff 3 (h n) + τ * diff 3 n.
Proof.
 unfold diffh2, diff. simpl. fold h. fold τ. lra.
Qed.

Lemma diffh2_eqn n : diffh2 n = -μ * diff 3 (rchild 3 n).
Proof.
 unfold diffh2, diff. rewrite f_onto_eqn by lia. fold τ.
 unfold rchild, h.
 rewrite plus_INR.
 change (fs 3 (3-1)) with (fs 3 2).
 replace (-μ * _) with ((μ*τ)*fs 3 2 n - μ*τ^3*n) by (rewrite τ3; ring).
 replace (μ*τ^3) with ((μ*τ)*τ^2) by ring.
 change τ with (/μ) at 2 3. rewrite Rinv_r by approx. ring.
Qed.

Lemma diffh2_bounds n : -0.786300925665 <= diffh2 n <= 1.038233961404.
Proof.
 split.
 - rewrite diffh2_eqn.
   assert (H : rank 3 (rchild 3 n) <> Some O).
   { unfold rank. rewrite rchild_decomp, decomp_sum'; try easy.
     now destruct (decomp 3 n) as [|r l].
     eapply Delta_map; eauto using decomp_delta. lia. }
   generalize (diff_bound_ranknz _ H) μ_approx. unfold Approx. nra.
 - rewrite diffh2_eqn.
   generalize (diff_bound (rchild 3 n)) μ_approx. unfold Approx. nra.
Qed.

(** Differences [h^^2] minus [nat_part (τ^2 * n)] are 0, +1 or +2.
    The "+2" difference is rather rare, it corresponds to the bound 1.038...
    being barely above 1. See for instance n=1235.
    The bound -0.78... being above -1 ensures now that a "-1" difference
    is impossible. *)

Lemma h2_natpart_bound (n:nat) :
 (nat_part (τ^2 * n) <= (h^^2) n <= 2 + nat_part (τ^2 * n))%nat.
Proof.
 split.
 - assert (nat_part (τ^2 * n) < 1 + (h^^2) n)%nat; try lia.
   { apply nat_part_lt. split.
     - apply Rmult_le_pos. approx. apply pos_INR.
     - rewrite plus_INR. replace (INR 2) with 2 by auto.
       generalize (diffh2_bounds n). unfold diffh2. simpl. lra. }
 - assert ((h^^2) n - 2 <= nat_part (τ^2 * n))%nat; try lia.
   { apply nat_part_le.
     - apply Rmult_le_pos. approx. apply pos_INR.
     - destruct (Nat.le_gt_cases 4 n) as [LE|LT].
       + assert (LE' := fs_mono 3 2 LE).
         rewrite minus_INR by trivial.
         replace (INR 2) with 2 by auto.
         generalize (diffh2_bounds n). unfold diffh2. simpl. lra.
       + destruct n. simpl; lra.
         destruct n. simpl. approx.
         destruct n. simpl. approx.
         destruct n. simpl. approx.
         lia. }
Qed.


(** ** Occurrences of letters in morphic word [Words.kseq 3]

    See now the much more general results in Freq.v.

    For a finite word [w], the frequency of letter [a] is
    [nbocc a w / length w]. For infinite words, the frequency
    of a letter (if it exists) is the limit of frequencies for
    ever-growing finite prefixes of the infinite word.

    Here for [Words.kseq 3], the frequencies of letters [0],[1],[2]
    will be respectively [τ^3],[τ^4],[τ^2] (another numbering
    of letters would make that more uniform). For proving that and
    even more, we now consider the following differences :
*)

Definition Diff0 w := τ^3 * length w - nbocc 0 w.
Definition Diff1 w := τ^4 * length w - nbocc 1 w.
Definition Diff2 w := τ^2 * length w - nbocc 2 w.

Definition diff0 n := Diff0 (take n (kseq 3)).
Definition diff1 n := Diff1 (take n (kseq 3)).
Definition diff2 n := Diff2 (take n (kseq 3)).

(** One of these differences can be deduced from the other two.
    We now forget about diff1 and consider only diff0 and diff2
    (that have nice links with [h] and [h^^2]). *)

Lemma Diff012 w :
 List.Forall (fun a => a < 3)%nat w ->
 Diff0 w + Diff1 w + Diff2 w = 0.
Proof.
 intros H.
 apply nbocc_total_lt in H. simpl in H.
 unfold Diff0, Diff1, Diff2.
 ring_simplify [τ3]. rewrite H, !plus_INR. simpl. ring.
Qed.

Lemma diff012 n : diff0 n + diff1 n + diff2 n = 0.
Proof.
 apply Diff012.
 apply Forall_nth. intros i d. rewrite take_length. intros H.
 rewrite take_nth by trivial. now apply kseq_letters.
Qed.

(** Expressing diff0 and diff2 in terms of [h] and [h^^2] *)

Lemma diff0_alt n : diff0 n = h n - τ * n.
Proof.
 unfold diff0, Diff0. rewrite take_length.
 rewrite <- count_nbocc.
 rewrite τ3. rewrite Rmult_minus_distr_r.
 rewrite <- (f_count_0 3 n) at 1 by lia. fold h. rewrite plus_INR. lra.
Qed.

Lemma diff0_alt' n : diff0 n = diff 3 n.
Proof.
 apply diff0_alt.
Qed.

Lemma diff2_alt n : diff2 n = τ^2 * n - (h^^2) n.
Proof.
 unfold diff2, Diff2. rewrite take_length.
 rewrite <- count_nbocc.
 now rewrite (fs_count_km1 3).
Qed.

Lemma diff2_alt' n : diff2 n = - diffh2 n.
Proof.
 rewrite diff2_alt. unfold diffh2. lra.
Qed.

(** Equations giving Diff0 and Diff1 after a substitution [ksubst 3].
    Note : this could be stated via a matrix someday.
*)

Lemma Diff0_ksubst3 w : Diff0 (ksubstw 3 w) = τ * Diff2 w.
Proof.
 unfold Diff0, Diff2.
 rewrite len_ksubst, plus_INR.
 destruct (nbocc_ksubst3 w) as (-> & _ & _).
 ring_simplify. unfold Rminus. rewrite Rplus_assoc. f_equal.
 rewrite τ3. simpl. lra.
Qed.

Lemma Diff2_qsubst2 w :
  List.Forall (fun a => a < 3)%nat w ->
  Diff2 (ksubstw 3 w) = - τ^2 * Diff2 w - Diff0 w.
Proof.
 intros H.
 unfold Diff0, Diff2.
 rewrite len_ksubst.
 destruct (nbocc_ksubst3 w) as (_ & _ & ->).
 rewrite !plus_INR.
 replace (nbocc 1 w + nbocc 2 w) with (length w - nbocc 0 w).
 2:{ apply len_nbocc_012 in H. rewrite H. rewrite !plus_INR. lra. }
 ring_simplify.
 replace (τ^4) with (1-τ^2-τ^3) by (generalize τ234; lra).
 simpl. lra.
Qed.

Lemma diff0_diff2_A n : diff0 (A 3 (S n)) = τ * diff2 (A 3 n).
Proof.
 unfold diff0, diff2. rewrite <- Diff0_ksubst3. f_equal.
 rewrite !kprefix_A_kword. apply kword_S.
Qed.

(** See also diffh2_eqn: *)

Lemma diff0_diff2 n : diff0 (rchild 3 n) = τ * diff2 n.
Proof.
 unfold diff0, diff2. rewrite <- Diff0_ksubst3.
 change (ksubstw 3 (kprefix 3 n)) with (WordGrowth.knsub 3 1 (kprefix 3 n)).
 now rewrite WordGrowth.knsub_kprefix, WordGrowth.L_k_1_rchild.
Qed.

(** For [A 3] numbers, diff0 and diff2 have nice expressions via
    powers of the [α] and [αbar] roots (or some real part of
    a power of [α]). Let's first describe the coefficients used
    in these expressions. *)

Lemma diff0_A n : diff0 (A 3 n) = 2 * Re(coefdA 3 α * α^n).
Proof.
 apply RtoC_inj.
 rewrite diff0_alt by easy. unfold h. rewrite f_A by easy.
 rewrite (Equation_dA 3 roots); try easy. 2:apply roots_sorted.
 unfold roots. cbn -[Cmult Cpow]. rewrite Cplus_0_r.
 change αbar with (Cconj α).
 rewrite coefdA_conj. conj_out. rewrite re_alt'. now rtoc.
Qed.

Lemma diff2_A n : diff2 (A 3 n) = 2 * Re(coefdA 3 α / αbar * α^n).
Proof.
 unfold Cdiv. rewrite <- Cmult_assoc, (Cmult_comm (/_)).
 replace (α^n * _)%C with (α^(n+1) * / τ)%C.
 2:{ rewrite <- αmod2, Cmod2_conj. change (Cconj α) with αbar.
     rewrite Nat.add_1_r, Cpow_S. field. split.
     intros [= H _]. revert H. approx.
     intros [= H _]. revert H. approx. }
 rewrite Cmult_assoc. ctor. rewrite re_scal_r.
 rewrite <- Rmult_assoc. rewrite <- diff0_A.
 apply Rmult_eq_reg_r with τ; try approx.
 rewrite Rmult_assoc, Rinv_l, Rmult_1_r by approx.
 rewrite diff2_alt, diff0_alt.
 unfold h. rewrite f_A, fs_A by easy. replace (n+1-1)%nat with n by lia.
 rewrite Nat.add_1_r. simpl. rewrite plus_INR. ring_simplify.
 rewrite τ3. ring.
Qed.

(** NB: I previously used the alternative expression
    (αbar*(α*(τ^2-1)-τ^3)/(α-αbar)) for (coefdA 2 α).
    I did once a tedious proof of equality between these two expressions. *)

Lemma re_coefdA : 2*Re (coefdA 3 α) = 1-τ.
Proof.
 generalize (diff0_A 0). rewrite Cpow_0_r, Cmult_1_r, diff0_alt.
 cbn -[Re]. lra.
Qed.

Lemma lim_diff0_div_n : is_lim_seq (fun n => diff0 n / n) 0.
Proof.
 eapply is_lim_seq_bound. intros n. rewrite diff0_alt'.
 apply Rlt_le. apply diff_lt_1.
Qed.

Lemma frequency_0 : is_lim_seq (fun n => count (kseq 3) 0 n / n) (τ^3).
Proof.
 apply Freq.freq_kseq_0. lia.
Qed.

Lemma Lim_h_div_n : is_lim_seq (fun n => h n / n) τ.
Proof.
 now apply Freq.Lim_fk_div_n.
Qed.

Lemma diff2_lt_2 n : Rabs (diff2 n) < 2.
Proof.
 rewrite diff2_alt', Rabs_Ropp. apply Rcomplements.Rabs_lt_between.
 generalize (diffh2_bounds n); lra.
Qed.

(** Any bound on diff2 is enough to prove that the frequency
    of letter 2 is [τ^2] and that [(h^^2)(n) / n] converges towards [τ^2]. *)

Lemma lim_diff2_div_n : is_lim_seq (fun n => diff2 n / n) 0.
Proof.
 eapply is_lim_seq_bound. intros n. apply Rlt_le. apply diff2_lt_2.
Qed.

Lemma frequency_2 : is_lim_seq (fun n => count (kseq 3) 2 n / n) (τ^2).
Proof.
 apply is_lim_seq_ext_loc with (fun n => τ^2 - diff2 n / n).
 - exists 1%nat. intros n Hn.
   unfold diff2, Diff2. rewrite take_length.
   rewrite <- count_nbocc. field. apply not_0_INR; lia.
 - replace (τ^2) with (τ^2 + -0) at 1 by lra.
   apply is_lim_seq_plus'. apply is_lim_seq_const.
   apply is_lim_seq_opp'. apply lim_diff2_div_n.
Qed.

Lemma frequency_1 : is_lim_seq (fun n => count (kseq 3) 1 n / n) (τ^4).
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
 now apply Freq.Lim_fkj_div_n.
Qed.


(** Appendix: the coefficients coef_μ and coef_α and [Cconj coef_α]
    are the roots of the polynomial [X^3-X^2-(12/31)*X-1/31]. *)

Module Appendix.
Local Open Scope C.

Section AnyRoot.
Variable r:C.
Hypothesis R: In r roots.
Let R3 : r^3 = r^2+1.
Proof.
 apply ThePoly_root_carac.
 now apply (SortedRoots_roots _ _ roots_sorted) in R.
Qed.

Lemma pre_coefA_alt : /(3*r-2) = (9*r^2-3*r-2)/31.
Proof.
 set (d := _-_).
 assert (NZ : d <> 0).
 { intros E. apply Ceq_minus in E.
   assert (E' : r = (3%nat-1)/3%nat).
   { replace (_-_) with 2 by lca. rewrite <- E. lca. }
   apply (SortedRoots_roots _ _ roots_sorted) in R.
   rewrite E' in R. now apply root_non_km1k in R. }
 apply Cmult_eq_reg_r with d; trivial. unfold d at 3. now field [R3].
Qed.

Lemma coefA_alt : coefA 3 r = (13*r^2+6*r+4)/31.
Proof.
 unfold coefA. replace (_-_) with (3*r-2) by lca.
 unfold Cdiv. rewrite pre_coefA_alt, R3. field [R3].
Qed.

Lemma coefA_square : (coefA 3 r)^2 = (15*r^2+7*r+11)/31.
Proof.
 rewrite coefA_alt. field [R3].
Qed.

Lemma coefA_cube : (coefA 3 r)^3 = (621*r^2+289*r+420)/31^2.
Proof.
 rewrite Cpow_S, coefA_square, coefA_alt. field [R3].
Qed.

Lemma coefA_poly :
  let c := coefA 3 r in c^3 - c^2 - (12/31)*c - 1/31 = 0.
Proof.
 cbv zeta. rewrite coefA_cube, coefA_square, coefA_alt by trivial. field.
Qed.

End AnyRoot.

(** Older approach *)

Definition det : C := (μ-α)*(μ-αbar)*(α-αbar).

Lemma μα_eqn : (μ - α)*(μ - αbar) = μ*(3*μ-2).
Proof.
 ring_simplify. rewrite <- Cmod2_conj, αmod2.
 (*compat*) unfold Cminus.
 replace (μ^2+_+_) with (μ^2-μ*(1-μ)) by (rewrite <- roots_sum; ring).
 rewrite τ_as_μ. rtoc. ring.
Qed.

Lemma αμ_eqn : (α - μ)*(α - αbar) = α*(3*α-2).
Proof.
 assert (D := SortedRoots_nodup _ _ roots_sorted).
 assert (E := MorePoly.Peval_Pdiff_linfactors roots 1 D).
 destruct roots_sorted as (E',_).
 rewrite <- E', ThePoly_diff_expr in E by lia.
 change (roots@1) with α in E. simpl in E.
 replace (_-_) with (3*α-2) in E. 2:{ simpl. rtoc. ring. }
 rewrite !Cmult_1_r in E. symmetry. apply E. lia.
Qed.

Lemma det2 : det^2 = -31.
Proof.
 unfold det.
 rewrite μα_eqn, im_alt'. change (Im α) with im_α. unfold im_α.
 rewrite !Cpow_mult_l. ctor.
 unfold Rdiv. rewrite Rpow_mult_distr, pow2_sqrt by approx.
 rewrite pow_inv, Ci2'. ctor. f_equal.
 rewrite μ_τ. field [τ3]. approx.
Qed.

Lemma det_eqn : det = Ci * sqrt 31.
Proof.
 assert (0 <= Im det).
 { unfold det.
   replace (μ-αbar) with (Cconj (μ-α)) by now conj_in.
   rewrite <- Cmod2_conj, im_scal_l, im_alt'.
   replace (2*Ci*Im α) with ((2*Im α)*Ci) by ring.
   ctor. rewrite im_scal_l. change (Im Ci) with 1%R.
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

Lemma coef_μ_eqn : RtoC coef_μ = 2 * μ^4 * im_α / sqrt 31.
Proof.
  unfold coef_μ. rewrite coef_mu_ok.
  unfold coefA. fold μ.
  replace (_-_) with (3*μ-2). 2:{ simpl. rtoc. ring. }
  apply Cmult_eq_reg_l with (det * (3*μ-2)).
  2:{ rewrite Cmult_integral. intros [H|[=H _]]. now apply det_nz.
      revert H. approx. }
  unfold det at 1. rewrite det_eqn.
  rewrite μα_eqn, im_alt'. change (Im α) with im_α. field. simpl.
  split.
  - intros [=E]. apply sqrt_eq_0 in E; lra.
  - intros [=E]. revert E. approx.
Qed.

Lemma coef_α_eqn : coef_α = α^4 * (αbar - μ) / det.
Proof.
  unfold coef_α, coefA.
  replace (_-_) with (3*α-2). 2:{ simpl. rtoc. ring. }
  apply Cmult_eq_reg_l with (det * (3*α-2)).
  2:{ rewrite Cmult_integral. intros [H|[=H _]]. now apply det_nz.
      revert H. approx. }
  replace det with ((α*(3*α-2))*(αbar-μ)) at 1.
  2:{ rewrite <- αμ_eqn. unfold det. ring. }
  field. simpl.
  split; try apply det_nz. intros [=E _]. revert E. approx.
Qed.

Lemma coef_sum : coef_μ+coef_α+coef_αbar = 1.
Proof.
 rewrite <- coefs_eqn1. rtoc. rewrite re_alt, coef_αbar_conj. field.
Qed.

Lemma coef_prod : coef_μ * coef_α * coef_αbar = 1/31.
Proof.
 unfold coef_μ, coef_α, coef_αbar. rewrite coef_mu_ok. fold μ.
 unfold coefA.
 replace (3%nat-1) with 2 by lca. rewrite INR_IZR_INZ. simpl IZR.
 apply Cmult_eq_reg_r with (-31). 2:{ intros [= E]. lra. }
 rewrite <- det2 at 1. replace (-31) with (-(31)) by lca.
 replace (det^2) with
  (-((μ-α)*(μ-αbar))*((α-μ)*(α-αbar))*(Cconj ((α-μ)*(α-αbar)))).
 2:{ conj_in. change (Cconj α) with αbar. replace (Cconj αbar) with α by lca.
     unfold det. ring. }
 rewrite μα_eqn, αμ_eqn. conj_in. change (Cconj α) with αbar.
 replace 1 with ((μ*α*αbar)^4). 2:{ now rewrite roots_prod, Cpow_1_l. }
 field; simpl; repeat split; intros [= E _]; revert E; approx.
Qed.

Lemma coef_squares : coef_μ^2+coef_α^2+coef_αbar^2 = 55/31.
Proof.
 unfold coef_μ, coef_α, coef_αbar. rewrite coef_mu_ok. fold μ.
 rewrite !coefA_square by (unfold roots; simpl; tauto).
 field_simplify. f_equal.
 replace 55 with (15*1+7*1+33) by lca.
 rewrite <- roots_sum2 at 1. rewrite <- roots_sum at 1. ring.
Qed.

Lemma coef_sigma2 :
  coef_μ * coef_α + coef_α * coef_αbar + coef_αbar * coef_μ = -12/31.
Proof.
 replace (_+_) with ((1^2-(55/31))/2); try lca.
 rewrite <- coef_sum, <- coef_squares. field.
Qed.

Lemma poly_coefs (X:C) :
  (X - coef_μ)*(X - coef_α)*(X - coef_αbar) = X^3-X^2-(12/31)*X-1/31.
Proof.
 rewrite <- coef_prod.
 rewrite <- (Cmult_1_l (X^2)), <- coef_sum.
 unfold Cminus at 5.
 replace (-(12/31 * X))%C with ((-12/31) * X)%C by field.
 rewrite <- coef_sigma2. field.
Qed.

Lemma coef_μ_poly : coef_μ^3 - coef_μ^2 - (12/31)*coef_μ - 1/31 = 0.
Proof.
 rewrite <- poly_coefs. ring.
Qed.

Lemma coef_α_poly : coef_α^3 - coef_α^2 - (12/31)*coef_α - 1/31 = 0.
Proof.
 rewrite <- poly_coefs. ring.
Qed.

End Appendix.
