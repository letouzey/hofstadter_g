From Coq Require Import List Lia Reals Ranalysis5 Lra.
Require Import MoreList.
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

Lemma max_INR a b : INR (Nat.max a b) = Rmax a b.
Proof.
 apply Nat.max_case_strong; intros; symmetry.
 - apply Rmax_left. now apply le_INR.
 - apply Rmax_right. now apply le_INR.
Qed.
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

Lemma Rle_pow2_inv x y : 0 <= y -> x^2 <= y^2 -> x <= y.
Proof.
 intros Hy LT.
 destruct (Rle_or_lt 0 x) as [Hx|Hx]; try lra.
 rewrite <- (Rabs_right x), <- (Rabs_right y) by lra.
 apply Rsqr_le_abs_0. now rewrite !Rsqr_pow2.
Qed.

Lemma RSpos n : 0 < S n.
Proof.
 rewrite S_INR. generalize (pos_INR n). lra.
Qed.

Lemma RSnz n : INR (S n) <> 0.
Proof.
 generalize (RSpos n). lra.
Qed.

Lemma Rle_lt_mult_compat (a b c d:R) :
 0 < a <= b -> 0 < c < d -> a*c < b*d.
Proof.
 intros. apply Rle_lt_trans with (b*c).
 - apply Rmult_le_compat_r; lra.
 - apply Rmult_lt_compat_l; lra.
Qed.

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

Lemma pow_even_pos k x : Nat.Even k -> 0 <> x -> 0 < x^k.
Proof.
 intros (m & ->) Hx.
 rewrite pow_mult. apply pow_lt. rewrite <- Rsqr_pow2.
 apply Rlt_0_sqr; lra.
Qed.

Lemma pow_odd_neg k x : Nat.Odd k -> x < 0 -> x^k < 0.
Proof.
 intros (m & ->) Hx.
 rewrite Nat.add_1_r. rewrite <- tech_pow_Rmult, pow_mult.
 apply Ropp_lt_cancel. rewrite Ropp_mult_distr_l, Ropp_0.
 apply Rmult_lt_0_compat; try lra.
 apply pow_lt. rewrite <- Rsqr_pow2. apply Rlt_0_sqr; lra.
Qed.

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

Lemma listsum_INR (l:list nat) : INR (listsum l) = Rlistsum (map INR l).
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
