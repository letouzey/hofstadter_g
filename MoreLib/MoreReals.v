From Coq Require Import List Lia Znat Reals Ranalysis5 Lra.
From Coq Require Import QArith Qreals Qminmax Qabs Qcanon.
Close Scope Q. Close Scope Qc. (* Issue with QArith *)
From Coquelicot Require Rcomplements.
From Hofstadter.HalfQuantum Require Import RealAux.
Require Import MoreList DeltaList.
Import ListNotations.

(** * Complements about Coq reals *)

(* Fix the lack of proper bullets in Coquelicot, inherited from math-comp *)
Global Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z.
Local Open Scope R.
Local Coercion IZR : Z >-> R.
Local Coercion INR : nat >-> R.

(** Instances concerning Rlt and Rle *)
#[global] Instance Rlt_strorder : StrictOrder Rlt.
Proof.
 split; repeat red; intros; lra.
Qed.
#[global] Instance Rlt_compat : Proper (Logic.eq==>Logic.eq==>iff) Rlt.
Proof.
 repeat red; intros; lra.
Qed.
#[global] Instance Rle_preorder : PreOrder Rle.
Proof.
 split; red; intros; lra.
Qed.
#[global] Instance Rle_partorder : PartialOrder Logic.eq Rle.
Proof.
 cbn. unfold Basics.flip. intros. lra.
Qed.
#[global] Instance Rle_compat : Proper (Logic.eq==>Logic.eq==>iff) Rle.
Proof.
 repeat red; intros; lra.
Qed.
#[global] Instance Rplus_le_compat : Proper (Rle ==> Rle ==> Rle) Rplus.
Proof.
 intros x x' Hx y y' Hy. lra.
Qed.
#[global] Instance Rplus_lt_compat : Proper (Rlt ==> Rlt ==> Rlt) Rplus.
Proof.
 intros x x' Hx y y' Hy. lra.
Qed.

(** Rabs_right, but with Rle instead of Rge precondition *)
Definition Rabs_right' := Rabs_pos_eq.

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

Lemma pow_inj_l n x y : n<>O -> 0 <= x -> 0 <= y -> x ^ n = y ^ n -> x = y.
Proof.
 intros Hn Hx Hy H.
 apply Rle_antisym.
 - apply Rnot_lt_le. intros LT.
   apply (Rpow_lt_compat_r n) in LT; trivial. lra.
 - apply Rnot_lt_le. intros LT.
   apply (Rpow_lt_compat_r n) in LT; trivial. lra.
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

Lemma nat_part_INR x : 0 <= x -> x < nat_part x + 1.
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

Lemma Int_part_addZ x z : Int_part (x + IZR z) = (Int_part x + z)%Z.
Proof.
 apply int_part_iff.
 rewrite plus_IZR.
 replace (_+_-_) with (x-IZR (Int_part x)) by ring.
 now apply int_part_iff.
Qed.

Lemma frac_part_addZ z x : frac_part (x + IZR z) = frac_part x.
Proof.
 unfold frac_part. rewrite Int_part_addZ, plus_IZR. ring.
Qed.

Lemma Int_part_opp x : frac_part x <> 0 ->
 (Int_part (-x) = - Int_part x -1)%Z.
Proof.
 intros Hx. unfold frac_part in Hx.
 apply int_part_iff. rewrite minus_IZR, opp_IZR.
 generalize (eq_refl (Int_part x)). rewrite <- int_part_iff. lra.
Qed.

Lemma frac_part_opp x : frac_part x <> 0 ->
  frac_part (-x) = 1 - frac_part x.
Proof.
 intros Hx. unfold frac_part.
 rewrite Int_part_opp, minus_IZR, opp_IZR by trivial. lra.
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

(** Dirichlet approximation theorem *)

Lemma dirichlet (a : R)(N : nat) : N<>O ->
  exists (q : nat) (p : Z), (1<=q<=N)%nat /\ Rabs (q*a - p) < 1/N.
Proof.
 intros HN.
 set (l := map (fun (k:nat) => nat_part (N*frac_part (k*a))) (seq O (S N))).
 assert (B : Below l N).
 { unfold l. intros x. rewrite in_map_iff. intros (k & <- & K).
   rewrite in_seq in K. apply nat_part_lt.
   generalize (base_fp (k*a)) (lt_0_INR N ltac:(lia)). nra. }
 assert (L : length l = S N).
 { unfold l. now rewrite map_length, seq_length. }
 destruct (pigeonhole_split N l B ltac:(lia)) as (m & l1 & l2 & l3 & E).
 set (k1 := length l1).
 set (k2 := length l2).
 unfold l in E.
 assert (k1+k2 < N)%nat.
 { apply (f_equal (@length nat)) in E.
   rewrite map_length, seq_length, !app_length in E. simpl in E.
   rewrite app_length in E. simpl in E. lia. }
 replace (S N) with (k1 + S (k2 + S (N-k1-k2-1)))%nat in E by lia.
 rewrite seq_app, map_app in E.
 apply app_inv in E.
 2:{ now rewrite map_length, seq_length. }
 destruct E as (_,E).
 rewrite <- cons_seq in E. simpl in E. injection E as E1 E.
 rewrite seq_app, map_app in E.
 apply app_inv in E.
 2:{ now rewrite map_length, seq_length. }
 destruct E as (_,E).
 rewrite <- cons_seq in E. remember (S k1+k2)%nat as k.
 injection E as E2 _.
 exists (S k2).
 exists (Int_part (k*a) - Int_part (k1*a))%Z.
 split. lia.
 set (u := N * _) in E1.
 set (v := N * _) in E2.
 assert (-1 < u-v < 1).
 { rewrite (nat_frac u), (nat_frac v).
   2:{ unfold v. generalize (base_fp (k*a)) (lt_0_INR N ltac:(lia)). nra. }
   2:{ unfold u. generalize (base_fp (k1*a)) (lt_0_INR N ltac:(lia)). nra. }
   rewrite E1,E2.
   generalize (base_fp u) (base_fp v). lra. }
 unfold u, v in *; clearbody k1 k2; clear l B L u v E1 E2 l1 l2 l3.
 replace (S k2) with (k-k1)%nat by lia.
 rewrite minus_INR, Rmult_minus_distr_r by lia.
 rewrite (int_frac (k*a)) at 1. rewrite (int_frac (k1*a)) at 1.
 rewrite minus_IZR. apply Rabs_def1; ring_simplify.
 - apply Rcomplements.Rlt_div_r. apply lt_0_INR; lia. lra.
 - apply Ropp_lt_cancel. rewrite Ropp_involutive.
   apply Rcomplements.Rlt_div_r. apply lt_0_INR; lia. lra.
Qed.

(** Specialized version of [euclidean_division] on positive reals,
    hence with quotient in nat. *)

Lemma euclidian_division_pos (x y : R) :
 0 <= x -> 0 < y -> exists (q : nat) (r : R), x = q * y + r /\ 0 <= r < y.
Proof.
 intros Hx Hy.
 exists (nat_part (x/y)), (y*frac_part (x/y)); split.
 - replace x with (y * (x/y)) at 1 by (field; lra).
   rewrite (nat_frac (x/y)) at 1. ring.
   apply Rcomplements.Rdiv_le_0_compat; lra.
 - generalize (base_fp (x/y)). nra.
Qed.

(** Kronecker approximation theorem *)

Definition irrat r := forall (q:Q), r <> Q2R q.

Lemma kronecker (a b : R)(eps : posreal) : irrat a ->
 exists (q:nat) (p:Z), Rabs (q*a - p - b) < eps.
Proof.
 intros Ha.
 set (N := S (nat_part (/eps))).
 assert (HN : /eps < N).
 { unfold N. rewrite S_INR. apply nat_part_INR. apply Rlt_le.
   apply Rinv_0_lt_compat, eps. }
 assert (HN' : /N < eps).
 { rewrite <- (Rinv_inv eps).
   apply Rinv_lt_contravar; trivial. apply Rmult_lt_0_compat.
   apply Rinv_0_lt_compat, eps. apply RSpos. }
 destruct (dirichlet a N ltac:(easy)) as (q & p & Hq & LT).
 set (m := frac_part (q*a)).
 assert (Hm : 0 < m < 1).
 { destruct (base_fp (q*a)) as (U,V). unfold m. split; trivial.
   destruct U as [U|U]; trivial. apply fp_nat in U.
   destruct U as (c & U). destruct (Ha (Qmake c (Pos.of_nat q))).
   unfold Q2R. simpl. rewrite <- U. rewrite INR_IZR_INZ.
   replace (Z.pos (Pos.of_nat q)) with (Z.of_nat q).
   - field.
     apply IZR_neq. intro E. change (0%Z) with (Z.of_nat 0) in E.
     apply Nat2Z.inj in E. lia.
   - rewrite <- positive_nat_Z. f_equal. rewrite Nat2Pos.id; lia. }
 destruct (Z.eq_dec (Int_part (q*a)) p) as [EQ|NEQ].
 - assert (Hm' : m < eps).
   { rewrite (int_frac (q*a)), EQ in LT. fold m in LT.
     replace (p+m-p) with m in LT by lra. rewrite Rabs_right in LT; lra. }
   assert (Hb := base_fp b).
   destruct (euclidian_division_pos (frac_part b) m) as (k & r & Hk & Hr);
    try lra.
   exists (k*q)%nat, (Z.of_nat k * Int_part (q*a) - Int_part b)%Z.
   rewrite (int_frac b) at 2. rewrite Hk.
   rewrite mult_INR, minus_IZR, mult_IZR, <- INR_IZR_INZ.
   rewrite Rmult_assoc. rewrite (int_frac (q*a)) at 1. fold m.
   replace (_-_) with (-r) by ring. rewrite Rabs_Ropp, Rabs_right; lra.
 - rewrite (int_frac (q*a)) in LT.
   assert (EQ : Int_part (q*a) = (p-1)%Z).
   { apply Rabs_def2 in LT.
     assert (1/N <= 1).
     { unfold Rdiv. rewrite Rmult_1_l, <- Rinv_1.
       apply Rinv_le_contravar. lra. apply (le_INR 1). unfold N; lia. }
     assert (Int_part (q*a) - p < 1)%Z.
     { apply lt_IZR. rewrite minus_IZR. generalize (base_fp (q*a)). lra. }
     assert (-2 < Int_part (q*a) - p)%Z.
     { apply lt_IZR. rewrite minus_IZR. generalize (base_fp (q*a)). lra. }
     lia. }
   rewrite EQ, minus_IZR in LT. fold m in LT.
   replace (_-p) with (-(1-m)) in LT by lra. rewrite Rabs_Ropp in LT.
   rewrite Rabs_right in LT by lra.
   assert (Hb := base_fp b).
   destruct (euclidian_division_pos (1-frac_part b) (1-m))
     as (k & r & Hk & Hr); try lra.
   exists (k*q)%nat, (Z.of_nat k * (Int_part (q*a)+1) - (1+Int_part b))%Z.
   replace b with (1+Int_part b-(1-frac_part b)) at 2.
   2:{ rewrite (int_frac b) at 3. lra. }
   rewrite Hk, minus_IZR, mult_IZR, !plus_IZR, <- INR_IZR_INZ.
   rewrite mult_INR.
   rewrite Rmult_assoc. rewrite (int_frac (q*a)) at 1. fold m.
   replace (_-_) with r by ring. rewrite Rabs_right; lra.
Qed.

(** Some complements on trigonometry. *)

Lemma cos_periodZ x (p:Z) : cos (x + 2 * p * PI) = cos x.
Proof.
 destruct p.
 - f_equal. lra.
 - replace (IZR (Z.pos p)) with (INR (Z.to_nat (Z.pos p))).
   apply cos_period. rewrite INR_IZR_INZ. f_equal. now apply Z2Nat.id.
 - replace x with (x + 2*Z.neg p*PI + 2*INR (Z.to_nat (Z.pos p))*PI) at 2.
   symmetry; apply cos_period.
   rewrite INR_IZR_INZ, Z2Nat.id by easy.
   change (Z.neg p) with (-Z.pos p)%Z. rewrite opp_IZR. lra.
Qed.

Lemma sin_periodZ x (p:Z) : sin (x + 2 * p * PI) = sin x.
Proof.
 destruct p.
 - f_equal. lra.
 - replace (IZR (Z.pos p)) with (INR (Z.to_nat (Z.pos p))).
   apply sin_period. rewrite INR_IZR_INZ. f_equal. now apply Z2Nat.id.
 - replace x with (x + 2*Z.neg p*PI + 2*INR (Z.to_nat (Z.pos p))*PI) at 2.
   symmetry; apply sin_period.
   rewrite INR_IZR_INZ, Z2Nat.id by easy.
   change (Z.neg p) with (-Z.pos p)%Z. rewrite opp_IZR. lra.
Qed.

Lemma cos_abs x : cos (Rabs x) = cos x.
Proof.
 destruct (Rle_lt_dec 0 x).
 - rewrite Rabs_right; lra.
 - rewrite Rabs_left by lra. apply cos_neg.
Qed.

(** [fun n => cos(a*n+b)] is above 0.5 infinitely often, first when
    [a/(2*PI)] is irrational, then more generally when [sin(a)<>0].
    TODO: It seems overkill to use rationality / irrationality this way
     (and the Excluded Middle to know in which case we are).
     Is there a simpler proof ? *)

Lemma affine_cos_pos_irrat (a b : R) :
  irrat (a / (2*PI)) ->
  forall N, exists n, (N<=n)%nat /\ 1/2 < cos (a * n + b).
Proof.
 intros Ha N.
 assert (Heps : 0 < /6) by lra.
 set (eps := mkposreal _ Heps).
 destruct (kronecker _ (-(N*a+b)/(2*PI)) eps Ha) as (q & p & E).
 exists (N+q)%nat. split. lia. rewrite plus_INR.
 unfold eps in E. simpl in E. clear eps Heps.
 apply Rmult_lt_compat_l with (r:=2*PI) in E. 2:{ apply Rgt_2PI_0. }
 rewrite <- (Rabs_right (2*PI)) in E at 1. 2:{ generalize Rgt_2PI_0; lra. }
 rewrite <- Rabs_mult in E.
 replace (2*PI*_) with ((a*(N+q)+b)-2*p*PI) in E by (field; apply PI_neq0).
 set (c := a*(N+q)+b) in *.
 replace c with (c-2*p*PI+2*p*PI) by lra.
 rewrite cos_periodZ, <- cos_abs.
 rewrite <- cos_PI3. replace (2*PI*/6) with (PI/3) in E by lra.
 apply cos_decreasing_1; trivial using Rabs_pos; generalize PI_RGT_0; lra.
Qed.

Lemma affine_cos_pos (a b : R) :
  sin a <> 0 ->
  forall N, exists n, (N<=n)%nat /\ 1/2 <= cos (a * n + b).
Proof.
 intros Ha N.
 destruct (Classical_Prop.classic (irrat (a/(2*PI)))) as [Ha'|Ha'].
 - destruct (affine_cos_pos_irrat a b Ha' N) as (n & Hn & LT).
   exists n. split; trivial. lra.
 - apply Classical_Pred_Type.not_all_not_ex in Ha'.
   destruct Ha' as (a' & E).
   rewrite (Qeq_eqR a' (Qred a')) in E by (symmetry; apply Qred_correct).
   destruct (Qred a') as (p,q) eqn:Hpq.
   assert (Hpq' : Z.gcd p (Z.pos q) = 1%Z).
   { replace q with (Qden (Qred a')). 2:now rewrite Hpq.
     replace p with (Qnum (Qred a')). 2:now rewrite Hpq.
     apply Qred_identity2, Qred_involutive. }
   assert (P := PI_RGT_0).
   assert (E' : a = 2*p*PI / Z.pos q).
   { apply Rmult_eq_compat_l with (r:=2*PI) in E.
     field_simplify in E; try lra.
     subst a. unfold Q2R. simpl. field. now apply IZR_neq. }
   clear E Hpq a'.
   apply Z.gcd_bezout in Hpq'. destruct Hpq' as (u & v & Hpq).
   apply (f_equal IZR) in Hpq. rewrite plus_IZR, !mult_IZR in Hpq.
   destruct (euclidian_division (-b/(2*PI)+1/6) (/Z.pos q))
     as (k & r & EQ & Hr).
   { now apply Rinv_neq_0_compat, IZR_neq. }
   assert (Hr' : 0 <= r < /3).
   { split. apply Hr. apply Rlt_le_trans with (Rabs (/ Z.pos q)). apply Hr.
     rewrite Rabs_right. 2:{ left. now apply Rinv_0_lt_compat, IZR_lt. }
     apply Rinv_le_contravar; try lra. apply IZR_le.
     assert (q <> 1%positive).
     { intros ->. apply Ha. unfold Rdiv in *. rewrite E', Rinv_1, Rmult_1_r.
       rewrite <- (Rplus_0_l (_*PI)). now rewrite sin_periodZ, sin_0. }
     assert (q <> 2%positive).
     { intros ->. apply Ha. replace a with (p*PI) by lra.
       rewrite (Z.div_mod p 2), Z.add_comm; try lia.
       rewrite plus_IZR, mult_IZR.
       rewrite Rmult_plus_distr_r, sin_periodZ.
       assert (Hp : (p mod 2 = 0 \/ p mod 2 = 1)%Z).
       { generalize (Z.mod_pos_bound p 2); lia. }
       destruct Hp as [-> | ->].
       - now rewrite Rmult_0_l, sin_0.
       - now rewrite Rmult_1_l, sin_PI. }
     lia. }
   clear Hr.
   set (k' := Z.max Z0 (Z.of_nat N - k*u)). (* large over-estimate *)
   set (n := (k * u + k' * Z.pos q)%Z).
   assert (Hn : (Z.of_nat N <= n)%Z).
   { unfold n, k'.
     destruct (Z.max_spec 0 (Z.of_nat N - k*u)) as [(MX,->)|(MX,->)]; [|lia].
     apply Z.le_sub_le_add_l. set (z := (_-_)%Z).
     rewrite <- (Z.mul_1_r z) at 1. apply Z.mul_le_mono_nonneg_l; lia. }
   exists (Z.to_nat n); split.
   + apply Nat2Z.inj_le. rewrite Z2Nat.id; lia.
   + rewrite INR_IZR_INZ, Z2Nat.id by lia. unfold n. clear n Hn. clearbody k'.
     rewrite plus_IZR, !mult_IZR, Rmult_plus_distr_l.
     rewrite Rplus_assoc, (Rplus_comm _ b), <- Rplus_assoc.
     rewrite E'. clear a Ha E'.
     replace (_*(k'*_)) with (2*(p*k')%Z*PI).
     2:{ rewrite mult_IZR. field. now apply IZR_neq. }
     rewrite cos_periodZ.
     replace (_*(k*u)) with ((k/Z.pos q)*(2*PI) + 2*(-v*k)%Z*PI).
     2:{ rewrite mult_IZR, opp_IZR.
         rewrite <- (Rmult_1_l (_*(2*PI))), <- Hpq.
         field. now apply IZR_neq. }
     rewrite Rplus_assoc, (Rplus_comm _ b), <- Rplus_assoc, cos_periodZ.
     replace (_+b) with ((1/6-r)*(2*PI)).
     2:{ apply Rplus_eq_compat_r with (r:=-r) in EQ. ring_simplify in EQ.
         unfold Rdiv at 2. rewrite <- EQ. field. lra. }
     clear p u v Hpq k k' EQ.
     rewrite <- cos_abs, <- cos_PI3.
     assert (Rabs ((1/6 - r) * (2*PI)) <= PI/3).
     { rewrite Rabs_mult.
       rewrite (Rabs_right (2*PI)) by lra.
       replace (PI/3) with (1/6 * (2*PI)) by lra.
       apply Rmult_le_compat_r; try lra. apply Rabs_le. lra. }
     apply cos_decr_1; trivial using Rabs_pos; lra.
Qed.

Lemma affine_cos_neg (a b : R) : sin a <> 0 ->
   forall N, exists n, (N<=n)%nat /\ cos (a * n + b) <= -1/2.
Proof.
 intros Ha N.
 destruct (affine_cos_pos a (b+PI) Ha N) as (n & Hn & LT).
 exists n. split; trivial. rewrite <- Rplus_assoc, neg_cos in LT. lra.
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

Lemma pow_via_exp x n : 0<x -> x^n = exp (n * ln x).
Proof.
 intros Hx.
 induction n.
 - simpl. now rewrite Rmult_0_l, exp_0.
 - rewrite <- Nat.add_1_r at 2. rewrite plus_INR. simpl.
   rewrite IHn. rewrite <- (exp_ln x) at 1 by trivial.
   rewrite <- exp_plus. f_equal. lra.
Qed.

Lemma exp_pow x n : exp x ^ n = exp (x*n).
Proof.
 rewrite pow_via_exp, ln_exp by apply exp_pos. f_equal. ring.
Qed.

Lemma Rpow_lt_reg_r n x y : 0 <= x -> 0 <= y -> x ^ n < y ^ n -> x < y.
Proof.
 intros Hx Hy.
 destruct n as [|n].
 { simpl. lra. }
 destruct (Req_dec x 0) as [Hx'|Hx'], (Req_dec y 0) as [Hy'|Hy'].
 - subst. simpl. lra.
 - lra.
 - subst. apply (pow_le x (S n)) in Hx. rewrite Rpow_0_l by easy. lra.
 - rewrite !pow_via_exp by lra.
   intros H. apply exp_lt_inv in H.
   apply Rmult_lt_reg_l in H; try apply RSpos.
   apply ln_lt_inv; lra.
Qed.

(** Generalized n-th root *)

Definition nthroot (x:R) (n:nat) :=
  if Rle_lt_dec x 0 then 0 else exp (ln x / n).

Lemma nthroot_alt x n : 0 < x -> nthroot x n = exp (ln x / n).
Proof.
 intros. unfold nthroot. destruct Rle_lt_dec; lra.
Qed.

Lemma nthroot_nonpos x n : x <= 0 -> nthroot x n = 0.
Proof.
 intros. unfold nthroot. destruct Rle_lt_dec; lra.
Qed.

Lemma nthroot_pos x n : 0 <= nthroot x n.
Proof.
 unfold nthroot. destruct Rle_lt_dec; try lra. apply Rlt_le, exp_pos.
Qed.

Lemma nthroot_gt_0 x n : 0 < x -> 0 < nthroot x n.
Proof.
 intros Hx.
 unfold nthroot. destruct Rle_lt_dec; try lra. apply exp_pos.
Qed.

(** Beware of the non-conventional nthroot 0 0 = 0 *)

Lemma nthroot_1_r x : 0 < x -> nthroot x 0 = 1.
Proof.
 intros Hx. rewrite nthroot_alt by trivial. simpl.
 unfold Rdiv. now rewrite Rinv_0, Rmult_0_r, exp_0.
Qed.

Lemma nthroot_pow x n : n<>O -> 0 <= x -> (nthroot x n)^n = x.
Proof.
 intros Hn Hx.
 destruct (Req_dec x 0) as [Hx'|Hx'].
 - rewrite Hx', nthroot_nonpos by lra. apply Rpow_0_l. lia.
 - rewrite nthroot_alt, exp_pow by lra.
   rewrite <- (exp_ln x) at 2 by lra. f_equal. field.
   contradict Hn. now apply INR_eq.
Qed.

Lemma nthroot_sqrt x : nthroot x 2 = sqrt x.
Proof.
 destruct (Rle_lt_dec x 0).
 - rewrite nthroot_nonpos by trivial. symmetry. now apply sqrt_neg_0.
 - apply (pow_inj_l 2); try lia; try apply nthroot_pos; try apply sqrt_pos.
   rewrite nthroot_pow by (lia||lra). rewrite pow2_sqrt; lra.
Qed.

Lemma sqrt2_approx : 1.414 < sqrt 2 < 1.415.
Proof.
 split; apply Rsqr_incrst_0; try lra; try apply sqrt_pos;
  rewrite Rsqr_sqrt, Rsqr_pow2; lra.
Qed.
