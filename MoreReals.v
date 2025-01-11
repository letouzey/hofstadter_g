From Coq Require Import List Lia Reals Ranalysis5 Lra.
From Coq Require Import Qreals Qminmax Qabs.
From Coquelicot Require Rcomplements.
Require Import MoreList DeltaList.
Import ListNotations.

(** * Complements about Coq reals *)

(* Fix the lack of proper bullets in Coquelicot, inherited from math-comp *)
Global Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z.
Local Open Scope R.
Local Coercion IZR : Z >-> R.
Local Coercion INR : nat >-> R.

Lemma Rdist_pos_pos a b : 0<=a -> 0<=b -> R_dist a b <= Rmax a b.
Proof.
unfold R_dist. intros Ha Hb.
destruct (Rlt_le_dec a b).
- rewrite Rmax_right, Rabs_left; lra.
- rewrite Rmax_left, Rabs_right; lra.
Qed.

Lemma Rdist_impl_pos (a b : R) : R_dist a b < b -> 0 < a.
Proof.
 unfold R_dist. intros H.
 destruct (Rle_or_lt b a).
 - rewrite Rabs_right in H; lra.
 - rewrite Rabs_left in H; lra.
Qed.

Lemma Rabs_left' r : r <= 0 -> Rabs r = - r.
Proof.
 intros LE. rewrite <- Rabs_Ropp, Rabs_right; lra.
Qed.

Lemma max_INR a b : INR (Nat.max a b) = Rmax a b.
Proof.
 apply Nat.max_case_strong; intros; symmetry.
 - apply Rmax_left. now apply le_INR.
 - apply Rmax_right. now apply le_INR.
Qed.

Lemma Rmult_lt_compat a b c d :
 0 <= a < b -> 0 <= c < d -> a*c < b*d.
Proof.
 nra.
Qed.

Lemma Rle_lt_mult_compat (a b c d:R) :
 0 < a <= b -> 0 < c < d -> a*c < b*d.
Proof.
 nra.
Qed.

Lemma Rmult_ge_lowerbound a r b a' r' b' :
 a <= r <= b -> a' <= r' <= b' ->
 a*a' <= r*r' \/ a*b' <= r*r' \/ b*a' <= r*r' \/ b*b' <= r*r'.
Proof.
 intros.
 destruct (Rle_lt_dec 0 a); destruct (Rle_lt_dec 0 a'); try nra.
 destruct (Rle_lt_dec 0 b); destruct (Rle_lt_dec 0 b'); try nra.
 destruct (Rle_lt_dec 0 r); nra.
Qed.

Lemma Rmult_le_upperbound a r b a' r' b' :
 a <= r <= b -> a' <= r' <= b' ->
 r*r' <= a*a' \/ r*r' <= a*b' \/ r*r' <= b*a' \/ r*r' <= b*b'.
Proof.
 intros A A'. assert (B : -b <= -r <= -a) by lra.
 generalize (Rmult_ge_lowerbound _ _ _ _ _ _ B A').
 rewrite <- !Ropp_mult_distr_l. lra.
Qed.

Lemma pow_0_r r : r ^ 0 = 1.
Proof. reflexivity. Qed.

Lemma pow_lt_compat_l x y n :
 0 <= x < y -> n<>O -> x^n < y^n.
Proof.
 induction n; try easy.
 destruct (Nat.eq_dec n O) as [->|N]; try lra.
 intros Hxy _. simpl. apply Rmult_lt_compat; trivial.
 split; auto. now apply pow_le.
Qed.

Lemma Rle_pow_low r n m : 0<=r<1 -> (n<=m)%nat -> r^m <= r^n.
Proof.
 induction 2; try lra.
 simpl. apply Rle_trans with (1 * r^m); try lra.
 apply Rmult_le_compat_r; try lra. apply pow_le; lra.
Qed.

Lemma Rlt_pow2_inv x y : 0 <= y -> x^2 < y^2 -> x < y.
Proof.
 nra.
Qed.

Lemma Rle_pow2_inv x y : 0 <= y -> x^2 <= y^2 -> x <= y.
Proof.
 nra.
Qed.

Lemma RSpos n : 0 < S n.
Proof.
 rewrite S_INR. generalize (pos_INR n). lra.
Qed.

Lemma RSnz n : INR (S n) <> 0.
Proof.
 generalize (RSpos n). lra.
Qed.

Lemma Rplus_reorder a b c d : (a+b)+(c+d) = (a+c)+(b+d).
Proof. lra. Qed.

Lemma minusone_pow_even k : Nat.Even k -> (-1)^k = 1.
Proof.
 intros (m & ->).
 rewrite pow_mult. replace ((-1)^2) with 1 by lra. apply pow1.
Qed.

Lemma minusone_pow_odd k : Nat.Odd k -> (-1)^k = -1.
Proof.
 intros (m & ->).
 rewrite pow_add, pow_mult. replace ((-1)^2) with 1 by lra. rewrite pow1. lra.
Qed.

Lemma pow_even_nonneg k x : Nat.Even k -> 0 <= x^k.
Proof.
 intros (m & ->). rewrite pow_mult. apply pow_le. nra.
Qed.

Lemma pow_even_pos k x : Nat.Even k -> 0 <> x -> 0 < x^k.
Proof.
 intros (m & ->) Hx. rewrite pow_mult. apply pow_lt. nra.
Qed.

Lemma pow_odd_neg k x : Nat.Odd k -> x < 0 -> x^k < 0.
Proof.
 intros (m & ->) Hx.
 rewrite Nat.add_1_r. rewrite <- tech_pow_Rmult, pow_mult.
 apply Ropp_lt_cancel. rewrite Ropp_mult_distr_l, Ropp_0.
 apply Rmult_lt_0_compat; try lra. apply pow_lt. nra.
Qed.

Lemma pow_incr_odd n x y : Nat.Odd n -> x <= y -> x^n <= y^n.
Proof.
 intros Hn LE.
 destruct (Rle_lt_dec 0 x).
 - apply pow_incr; lra.
 - destruct (Rle_lt_dec 0 y).
   + apply Rle_trans with 0.
     * apply Rlt_le. apply pow_odd_neg; auto.
     * now apply pow_le.
   + replace x with (-1*-x) by lra.
     replace y with (-1*-y) by lra.
     rewrite !Rpow_mult_distr.
     rewrite minusone_pow_odd by trivial.
     generalize (pow_incr (-y) (-x) n). lra.
Qed.

Lemma pow_decr_even_neg n x y :
  Nat.Even n -> x <= y <= 0 -> y^n <= x^n.
Proof.
 intros Hn LE.
 replace x with (-1*-x) by lra.
 replace y with (-1*-y) by lra.
 rewrite !Rpow_mult_distr.
 rewrite minusone_pow_even by trivial.
 generalize (pow_incr (-y) (-x) n). lra.
Qed.

(** Link between Q and R *)

Lemma Q2R_pow q n : Q2R (q^Z.of_nat n) = (Q2R q)^n.
Proof.
 induction n.
 - simpl. try lra.
 - rewrite Nat2Z.inj_succ, <-Z.add_1_l.
   rewrite Qpower.Qpower_plus' by lia. now rewrite Q2R_mult, IHn.
Qed.

Lemma Q2R_pow' q z : (0<=z)%Z -> Q2R (q^z) = (Q2R q)^Z.to_nat z.
Proof.
 intros Hz. rewrite <- Q2R_pow. f_equal. f_equal. lia.
Qed.

Lemma Q2R_pow2 q : Q2R (q^2) = (Q2R q)^2.
Proof.
 now apply Q2R_pow'.
Qed.

Lemma Q2R_abs q : Q2R (Qabs q) = Rabs (Q2R q).
Proof.
 apply Qabs_case; intros LE; apply Qle_Rle in LE.
 - rewrite Rabs_right; lra.
 - rewrite <- Rabs_Ropp, Rabs_right, ?Q2R_opp; lra.
Qed.

Lemma Q2R_IZR z : Q2R (inject_Z z) = IZR z.
Proof. unfold Q2R, inject_Z. simpl. lra. Qed.

(** [IVT_interv] and [derive_increasing_interv] but
    for decreasing functions *)

Lemma IVT_interv_decr (f : R -> R) x y :
  (forall a : R, x <= a <= y -> continuity_pt f a) ->
  x < y -> 0 < f x -> f y < 0 -> {z : R | x <= z <= y /\ f z = 0}.
Proof.
 intros Hf Hxy Hx Hy.
 set (g := fun x => - f x).
 destruct (IVT_interv g x y) as (z & Hz & E); unfold g in *; try lra.
 + intros a Ha. now apply continuity_pt_opp, Hf.
 + exists z; split; trivial; lra.
Qed.

Lemma derivable_pt_opp_defined :
  forall (f : R -> R) (x:R), derivable_pt f x -> derivable_pt (- f) x.
Proof.
  intros f x H.
  unfold derivable_pt in H.
  destruct H as [l H]; exists (-l).
  apply derivable_pt_lim_opp; assumption.
Defined.

Lemma derivable_opp_defined :
  forall f, derivable f -> derivable (- f).
Proof.
  unfold derivable; intros f X x.
  apply (derivable_pt_opp_defined _ x (X _)).
Defined.

Lemma derive_decreasing_interv a b (f : R -> R) (pr : derivable f) :
  a < b ->
  (forall t : R, a < t < b -> derive_pt f t (pr t) < 0) ->
  forall x y : R, a <= x <= b -> a <= y <= b -> x < y -> f y < f x.
Proof.
 intros Hab Hf x y Hx Hy Hxy.
 apply Ropp_lt_cancel.
 apply (derive_increasing_interv a b _
          (derivable_opp_defined f pr)); trivial.
 intros t Ht.
 unfold derive_pt, derivable_opp_defined, derivable_pt_opp_defined in *.
 specialize (Hf t Ht). destruct (pr t). simpl in *. lra.
Qed.


(** Integer part and fractional part *)

Definition nat_part r := Z.to_nat (Int_part r).

Lemma int_part_le (r:R)(k:Z) : k <= r <-> (k <= Int_part r)%Z.
Proof.
 split.
 - intros LE.
   destruct (base_Int_part r) as (U,V).
   assert (E : k - 1 < Int_part r) by lra.
   change 1 with (IZR 1) in E.
   rewrite <- minus_IZR in E.
   apply lt_IZR in E. lia.
 - destruct (base_Int_part r).
   intros LE. apply IZR_le in LE. lra.
Qed.

Lemma int_part_iff (r:R)(k:Z) :
 0 <= r-k < 1 <-> Int_part r = k.
Proof.
 split.
 - unfold Int_part.
   intros (H1,H2).
   assert (k+1 = up r)%Z; [|lia].
   apply tech_up; rewrite plus_IZR; simpl; lra.
 - intros <-. destruct (base_Int_part r). split; lra.
Qed.

Lemma int_part_carac (r:R)(k:Z) :
 0 <= r-k < 1 -> Int_part r = k.
Proof.
 apply int_part_iff.
Qed.

Lemma int_frac r : r = Int_part r + frac_part r.
Proof.
 unfold frac_part. ring.
Qed.

Lemma nat_part_carac (r:R)(k:nat) :
 0 <= r-k < 1 -> nat_part r = k.
Proof.
 unfold nat_part. intros H.
 rewrite <- (Nat2Z.id k). f_equal. apply int_part_iff.
 now rewrite <- INR_IZR_INZ.
Qed.

Lemma nat_frac r : 0 <= r -> r = nat_part r + frac_part r.
Proof.
 unfold frac_part, nat_part. intros H.
 rewrite INR_IZR_INZ. rewrite Z2Nat.id. ring.
 rewrite <- int_part_le. auto.
Qed.

Lemma nat_part_INR x : 0 <= x -> x <= nat_part x + 1.
Proof.
 intros Hx.
 rewrite (nat_frac x Hx) at 1. generalize (base_fp x). lra.
Qed.


Lemma nat_part_le n r : 0<=r -> INR n <= r <-> (n <= nat_part r)%nat.
Proof.
 intros Hr.
 rewrite INR_IZR_INZ.
 rewrite int_part_le.
 unfold nat_part.
 rewrite Nat2Z.inj_le.
 rewrite Z2Nat.id; try reflexivity.
 now rewrite <- int_part_le.
Qed.

Lemma nat_part_lt n r : 0 <= r < INR n -> (nat_part r < n)%nat.
Proof.
 intros (Hr,H).
 apply Nat.lt_nge. rewrite <- nat_part_le; lra.
Qed.

Lemma Int_part_mono a b : a <= b -> (Int_part a <= Int_part b)%Z.
Proof.
 intros H.
 apply int_part_le. apply Rle_trans with a; trivial.
 rewrite (int_frac a) at 2. generalize (base_fp a). lra.
Qed.

Lemma nat_part_mono a b : a <= b -> (nat_part a <= nat_part b)%nat.
Proof.
 intros H. unfold nat_part.
 destruct (Z.le_gt_cases 0 (Int_part b)) as [LE|LT].
 - destruct (Z.le_gt_cases 0 (Int_part a)).
   + apply Z2Nat.inj_le; trivial. now apply Int_part_mono.
   + destruct (Int_part a); simpl; try lia.
 - assert (b < 0).
   { rewrite Z.lt_nge in LT. rewrite <- int_part_le in LT. lra. }
   assert (LT' : a < 0) by lra.
   apply Rlt_not_le in LT'. rewrite int_part_le in LT'. lia.
Qed.

(** Ceil function (from R to Z) : [1+Int_part] except on integers *)

Definition ceil (x:R) : Z :=
  Int_part x + if Req_EM_T (frac_part x) 0 then 0 else 1.

Lemma ceil_bound (r : R) : r <= IZR (ceil r) < r + 1.
Proof.
 unfold ceil.
 destruct Req_EM_T as [E|N].
 - rewrite (int_frac r) at 1 4. rewrite plus_IZR, E. lra.
 - rewrite (int_frac r) at 1 4. rewrite plus_IZR.
   generalize (base_fp r); lra.
Qed.

Lemma ceil_iff (r : R) (z : Z) : 0 <= IZR z - r < 1 <-> ceil r = z.
Proof.
 split.
 2:{ intros <-. generalize (ceil_bound r). lra. }
 unfold ceil.
 destruct Req_EM_T as [E|N].
 - rewrite (int_frac r) at 1 2. rewrite E. clear E.
   rewrite Z.add_0_r, Rplus_0_r, Z_R_minus.
   intros (U,V). apply le_IZR in U. apply lt_IZR in V. lia.
 - rewrite (int_frac r) at 1 2.
   assert (Hr := base_fp r).
   intros Hz.
   assert (Hz' : 0 < IZR z - IZR (Int_part r) < 2) by lra. clear N Hr Hz.
   rewrite Z_R_minus in Hz'.
   destruct Hz' as (U,V). apply lt_IZR in U. apply lt_IZR in V. lia.
Qed.

Lemma large_enough_exponent (a b:R) :
  1 < a -> exists n:nat, b < a^n.
Proof.
 intros Ha.
 destruct (Rlt_or_le b 1); [now exists O|].
 assert (0 <= ln b).
 { rewrite <- ln_1. apply Rcomplements.ln_le; lra. }
 assert (0 < ln a).
 { rewrite <- ln_1. apply ln_increasing; lra. }
 exists (S (Z.to_nat (Int_part (ln b / ln a)))).
 apply ln_lt_inv; try apply pow_lt; try lra.
 rewrite ln_pow; try lra.
 replace (ln b) with (ln a * (ln b / ln a)) at 1.
 2:{ field. apply ln_neq_0; lra. }
 rewrite (Rmult_comm _ (ln a)).
 apply Rmult_lt_compat_l; trivial.
 rewrite S_INR, INR_IZR_INZ, Z2Nat.id.
 2:{ apply int_part_le. apply Rcomplements.Rdiv_le_0_compat; lra. }
 rewrite (int_frac (ln b / ln a)) at 1.
 apply Rplus_lt_compat_l. apply base_fp.
Qed.

Lemma large_enough_exponent' (a b:R) :
  0 < a < 1 -> 0 < b -> exists n:nat, a^n < b.
Proof.
 intros Ha Hb.
 destruct (large_enough_exponent (/a) (/b)) as (n,Hn).
 { rewrite <- Rinv_1. apply Rinv_lt_contravar; lra. }
 exists n. rewrite pow_inv in Hn.
 apply Rcomplements.Rinv_lt_cancel; trivial.
Qed.

(** Some trigonometry : [fun n => |cos(a*n+b)|] is apart from 0
    frequently enough when [sin(a)<>0]. *)

Lemma affine_cos_apart_zero (a b : R) : sin a <> 0 ->
 exists c:posreal,
   forall N, exists n, (N<=n)%nat /\ c < Rabs (cos (a * n + b)).
Proof.
intros Ha.
set (f := fun n => Rabs (cos (a*n+b))).
set (ZeroOne := fun x => 0<=x<=1).
assert (CZO : compact ZeroOne) by apply compact_P3.
destruct (Bolzano_Weierstrass f ZeroOne CZO) as (lim,Hlim).
{ unfold ZeroOne, f. intros. split. apply Rabs_pos.
  apply Rabs_le, COS_bound. }
assert (0 <= lim).
{ apply Rnot_lt_le. intros LT.
  destruct (Hlim (fun x => x<0) O) as (p & Hp & LT').
  - assert (LT' : 0 < (-lim/2)) by lra.
    exists (mkposreal (-lim/2) LT').
    intros x X. unfold disc in X. simpl in X.
    apply Rabs_def2 in X. lra.
  - revert LT'. apply Rle_not_lt, Rabs_pos. }
destruct (Req_dec lim 0) as [->|NZ].
- assert (LT : 0 < Rabs (sin a)/2).
  { generalize (Rabs_pos_lt (sin a)). lra. }
  exists (mkposreal (Rabs(sin a)/2) LT). intros N.
  destruct (Req_dec (cos a) 0) as [Ha'|Ha'].
  + destruct (Hlim (fun x => x < 1/2) N) as (n & Hn & LT').
    * assert (LT' : 0 < 1/2) by lra.
      exists (mkposreal (1/2) LT').
      intros x X. unfold disc in X. simpl in X.
      apply Rabs_def2 in X. lra.
    * exists (S n). split. lia. rewrite S_INR. simpl.
      replace (a*(n+1)+b) with (a+(a*n+b)) by lra.
      rewrite cos_plus, Ha', Rmult_0_l, Rabs_minus_sym, Rminus_0_r.
      rewrite Rabs_mult. unfold f in LT'.
      replace (1/2) with (Rabs (1/2)) in LT' by (rewrite Rabs_right; lra).
      apply Rsqr_lt_abs_1 in LT'.
      rewrite cos2 in LT'.
      assert (LT2 : (1/2)² < (sin(a*n+b))²)  by (unfold Rsqr in *; lra).
      apply Rsqr_lt_abs_0 in LT2. rewrite Rabs_right in LT2 by lra. nra.
  + set (c := Rmin (1/2) (Rabs (sin a)/Rabs (cos a)/4)).
    assert (LT' : 0 < c).
    { apply Rmin_glb_lt. lra.
      do 2 (apply Rdiv_lt_0_compat; try lra). now apply Rabs_pos_lt. }
    destruct (Hlim (fun x => x < c) N) as (n & Hn & LTn).
    * exists (mkposreal c LT').
      intros x X. unfold disc in X. simpl in X.
      apply Rabs_def2 in X. lra.
    * exists (S n). split. lia. rewrite S_INR. simpl.
      replace (a*(n+1)+b) with (a+(a*n+b)) by lra.
      rewrite cos_plus, Rabs_minus_sym.
      eapply Rlt_le_trans; [|apply Rabs_triang_inv].
      rewrite !Rabs_mult. fold (f n).
      assert (LT2 : Rabs (sin (a * n + b)) > 3/4).
      { replace (3/4) with (Rabs (3/4)) by (rewrite Rabs_right; lra).
        apply Rsqr_lt_abs_0.
        rewrite sin2.
        assert (LTn' : f n < Rabs (1/2)).
        { rewrite Rabs_right by lra. apply Rlt_le_trans with c; trivial.
          unfold c. apply Rmin_l. }
        apply Rsqr_lt_abs_1 in LTn'. unfold Rsqr in *; lra. }
      assert (Rabs (cos a) * f n < Rabs (sin a)/4).
      { apply Rlt_le_trans with (Rabs (cos a) * c).
        apply Rmult_lt_compat_l; trivial. now apply Rabs_pos_lt.
        apply Rle_trans with
            (Rabs (cos a) * (Rabs (sin a) / Rabs (cos a)/4)).
        apply Rmult_le_compat_l. apply Rabs_pos. apply Rmin_r.
        field_simplify. apply Rle_refl. now apply Rabs_no_R0. }
      nra.
- assert (LT : 0 < lim/2) by lra.
  exists (mkposreal (lim/2) LT).
  intros N. simpl.
  destruct (Hlim (fun x => lim/2 < x) N) as (n & Hn & LT').
  + exists (mkposreal (lim/2) LT).
    intros x X. unfold disc in X. simpl in X.
    apply Rabs_def2 in X. lra.
  + now exists n.
Qed.

(** Strict positivity of 2nd-degree polynomial *)

Lemma discriminant_neg (a b c : R) :
 0 < a ->
 b^2 < 4*a*c ->
 forall x, 0 < a*x^2+b*x+c.
Proof.
 intros A D x.
 assert (0 < c).
 { apply Rmult_lt_reg_l with a; trivial. ring_simplify. nra. }
 apply Rmult_lt_reg_l with (4*c)%R; try lra.
 rewrite Rmult_0_r, !Rmult_plus_distr_l, <- Rmult_assoc.
 destruct (Req_dec x 0) as [->|X].
 - ring_simplify. nra.
 - apply Rle_lt_trans with (b^2*x^2 + 4*c*(b*x)+4*c*c)%R.
   + replace (_+_)%R with ((b*x+2*c)^2)%R by ring. apply pow2_ge_0.
   + do 2 apply Rplus_lt_compat_r.
     apply Rmult_lt_compat_r; trivial; nra.
Qed.

(** More precise interval for exp 1 than exp_le_3 *)

Lemma exp_m1_itvl : 11/30 <= exp(-1) <= 3/8.
Proof.
 set (f := fun i => / INR (fact i)).
 unfold exp; case (exist_exp (-1)) as (x,e); simpl; unfold exp_in in e.
 replace (11/30) with (sum_f_R0 (tg_alt f) 5).
 2:{ unfold tg_alt,f; simpl. field. }
 replace (3/8) with (sum_f_R0 (tg_alt f) 4).
 2:{ unfold tg_alt,f; simpl. field. }
 apply (alternated_series_ineq f x 2).
 - unfold Un_decreasing; intros;
     apply Rmult_le_reg_l with (INR (fact n)).
   { apply INR_fact_lt_0. }
   apply Rmult_le_reg_l with (INR (fact (S n))).
   { apply INR_fact_lt_0. }
   rewrite Rinv_r.
   2:{ apply INR_fact_neq_0. }
   unfold f. rewrite Rmult_1_r; rewrite Rmult_comm; rewrite Rmult_assoc;
     rewrite Rinv_l.
   2:{ apply INR_fact_neq_0. }
   rewrite Rmult_1_r; apply le_INR; apply fact_le; apply Nat.le_succ_diag_r.
 - unfold f. intros eps H1.
   assert (H0 := cv_speed_pow_fact 1); unfold Un_cv; unfold Un_cv in H0;
     intros; elim (H0 _ H1); intros; exists x0; intros;
       unfold R_dist in H2; unfold R_dist;
         replace (/ INR (fact n)) with (1 ^ n / INR (fact n));
         try apply H; trivial.
    unfold Rdiv; rewrite pow1; rewrite Rmult_1_l; reflexivity.
  - unfold f. intros eps H0.
    unfold infinite_sum in e; unfold Un_cv, tg_alt; intros; elim (e _ H0);
      intros; exists x0; intros;
      replace (sum_f_R0 (fun i:nat => (-1) ^ i * / INR (fact i)) n) with
      (sum_f_R0 (fun i:nat => / INR (fact i) * (-1) ^ i) n);auto.
    apply sum_eq; intros; apply Rmult_comm.
Qed.

Lemma exp_1_itvl : 8/3 <= exp 1 <= 30/11.
Proof.
 replace 1 with (-(-1)) by lra. rewrite exp_Ropp.
 replace (8/3) with (/(3/8)) by lra.
 replace (30/11) with (/(11/30)) by lra.
 generalize exp_m1_itvl. split; apply Rinv_le_contravar; try lra.
Qed.

Lemma exp_1_gt_2 : 2 < exp 1.
Proof.
 generalize exp_1_itvl. lra.
Qed.

Lemma exp_1_lt_3 : exp 1 < 3.
Proof.
 generalize exp_1_itvl. lra.
Qed.
