From Coq Require Import List Lia Reals Ranalysis5 Lra.
From Coq Require Import Qreals Qminmax Qabs.
From Coquelicot Require Rcomplements.
Require Import MoreList DeltaList.
Import ListNotations.

Local Open Scope Z.
Local Open Scope R.
Local Coercion IZR : Z >-> R.
Local Coercion INR : nat >-> R.

(** Complements about Coq reals *)

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

(** Sum of [List R]. *)

Definition Rlistsum (l: list R) := List.fold_right Rplus 0 l.

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

Lemma listsum_INR (l:list nat) : INR (list_sum l) = Rlistsum (map INR l).
Proof.
 induction l; simpl; trivial. rewrite plus_INR. now f_equal.
Qed.

Lemma Rlistsum_distr l r : Rlistsum l * r = Rlistsum (map (fun x => x*r) l).
Proof.
 induction l; simpl; lra.
Qed.

Lemma Rdist_listsum {A}(f g:A->R) l :
 R_dist (Rlistsum (map f l)) (Rlistsum (map g l)) <=
 Rlistsum (map (fun x => R_dist (f x) (g x)) l).
Proof.
 induction l; simpl.
 - rewrite R_dist_eq; lra.
 - eapply Rle_trans. apply R_dist_plus.
   apply Rplus_le_compat_l. apply IHl.
Qed.

Lemma Rlistsum_le {A}(f g:A->R) l :
 (forall a, In a l -> f a <= g a) ->
 Rlistsum (map f l) <= Rlistsum (map g l).
Proof.
 induction l; simpl. lra.
 intros H. apply Rplus_le_compat. apply H; intuition.
 apply IHl; intuition.
Qed.

Definition Rpoly x l := Rlistsum (List.map (pow x) l).

Lemma Rpoly_cons x n l : Rpoly x (n::l) = (x^n + Rpoly x l)%R.
Proof.
 easy.
Qed.

Lemma Rpoly_app x l l' : Rpoly x (l++l') = (Rpoly x l + Rpoly x l')%R.
Proof.
 unfold Rpoly. now rewrite map_app, Rlistsum_app.
Qed.

Lemma Rlistsum_pow_factor r p l :
 Rlistsum (List.map (fun n => r^(p+n)) l) = r^p * Rpoly r l.
Proof.
 induction l; cbn -[pow].
 - ring.
 - change (List.fold_right Rplus 0) with Rlistsum. rewrite IHl.
   fold (Rpoly r l). rewrite Rdef_pow_add. ring.
Qed.

Lemma Rpoly_factor_above r p l :
 (forall n, List.In n l -> p <= n)%nat ->
 Rpoly r l = r^p * Rpoly r (List.map (decr p) l).
Proof.
 induction l as [|a l IH]; cbn -[pow]; intros Hl.
 - ring.
 - change (List.fold_right Rplus 0) with Rlistsum.
   fold (Rpoly r l). fold (Rpoly r (map (decr p) l)).
   rewrite IH by intuition.
   replace a with ((a-p)+p)%nat at 1 by (specialize (Hl a); lia).
   rewrite Rdef_pow_add. unfold decr at 2. ring.
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
