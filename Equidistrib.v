From Coq Require Import Arith Lia Reals Lra QArith_base.
Require Import MoreTac MoreFun MoreList MoreReals MoreLim MoreSum.
Import Summation.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** Equidistribution Theorem :
    irrational multiples modulo 1 are uniformly distributed. *)

(* https://link.springer.com/article/10.1007/s00283-014-9505-x *)

Definition Rleb (a b : R) := if Rle_lt_dec a b then true else false.
Definition Rltb (a b : R) := negb (Rleb b a).

Lemma Rleb_spec a b : BoolSpec (a <= b) (b < a) (Rleb a b).
Proof.
 unfold Rleb. destruct Rle_lt_dec; now constructor.
Qed.

Lemma Rltb_spec a b : BoolSpec (a < b) (b <= a) (Rltb a b).
Proof.
 unfold Rltb. case Rleb_spec; intros; now constructor.
Qed.

Definition RIn a b r := Rleb a r && Rltb r b.

Lemma RIn_spec a b r : RIn a b r = true <-> a <= r < b.
Proof.
 unfold RIn. case Rleb_spec; case Rltb_spec; simpl; lra.
Qed.

Definition Rcountin (u:nat->R) a b n :=
 length (filter (RIn a b) (map u (seq 0 n))).

Definition EquiDistr01 (u:nat->R) :=
 forall a b,
   0<=a -> a<=b -> b<=1 ->
   is_lim_seq (fun n => Rcountin u a b n / n) (b-a).

Lemma Rcountin_S (u:nat->R) a b n :
 Rcountin u a b (S n) =
 (Rcountin u a b n + if RIn a b (u n) then 1 else 0)%nat.
Proof.
 unfold Rcountin. rewrite seq_S, map_app, filter_app, app_length.
 simpl. f_equal. now destruct (RIn a b (u n)).
Qed.

Lemma Rcountin_split u a b c n : a<=b<=c ->
  (Rcountin u a c n = Rcountin u a b n + Rcountin u b c n)%nat.
Proof.
 intros (AB,BC).
 unfold Rcountin.
 induction (map u _) as [|x l IH]; simpl; trivial.
 unfold RIn at 1 4 7.
 repeat case Rleb_spec; repeat case Rltb_spec; intros; simpl; lra || lia.
Qed.

Lemma Rcountin_via_0 u a b n : 0<=a<=b ->
  (Rcountin u a b n = Rcountin u 0 b n - Rcountin u 0 a n)%nat.
Proof.
 intros H. rewrite (Rcountin_split u 0 a b n H). lia.
Qed.

Lemma Rcountin_noitvl (f:nat->R) a b n : b<a -> Rcountin f a b n = O.
Proof.
 intros Hab.
 unfold Rcountin. rewrite map_filter, map_length.
 rewrite filter_nop; trivial.
 intros x _. apply not_true_iff_false. unfold compose. rewrite RIn_spec; lra.
Qed.

Lemma EquiDistr01_alt1 u :
  EquiDistr01 u <->
  forall b, 0<=b<=1 -> is_lim_seq (fun n => Rcountin u 0 b n / n) b.
Proof.
 split; intros H.
 - intros b Hb. replace b with (b-0) at 1 by lra. apply (H 0 b); lra.
 - intros a b Ha Hab Hb.
   eapply is_lim_seq_ext.
   { symmetry. rewrite Rcountin_via_0 by lra. rewrite minus_INR.
     apply Rdiv_minus_distr.
     rewrite (Rcountin_split u 0 a b n). lia. lra. }
   apply is_lim_seq_minus'; apply H; lra.
Qed.

Definition mean u n := (big_sum u n)/n.
Definition mean_frac u n := mean (frac_part ∘ u) n.

Lemma mean_frac_reduce u n a :
  mean_frac (fun n => u n + a) n = mean_frac (fun n => u n + frac_part a) n.
Proof.
 unfold mean_frac, mean. unfold compose. f_equal.
 apply big_sum_eq_bounded. intros x Hx.
 rewrite (int_frac a) at 1.
 rewrite (Rplus_comm (IZR _)), <- Rplus_assoc.
 apply frac_part_addZ.
Qed.

Lemma mean_frac_reduce' u n a :
  mean_frac (fun n => u n + a) n =
  mean_frac (fun n => u n - frac_part (-a)) n.
Proof.
 unfold mean_frac, mean. unfold compose. f_equal.
 apply big_sum_eq_bounded. intros x Hx.
 rewrite <- (Ropp_involutive a) at 1.
 rewrite (int_frac (-a)) at 1.
 rewrite Ropp_plus_distr, <- opp_IZR, (Rplus_comm (IZR _)).
 now rewrite <- Rplus_assoc, frac_part_addZ.
Qed.

Lemma mean_frac_eqn u n b : n<>O -> 0<=b<=1 ->
  mean_frac (fun m => u m - b) n - mean_frac u n =
  Rcountin (frac_part ∘ u) 0 b n / n - b.
Proof.
 intros Hn Hb.
 unfold mean_frac, mean, compose. rewrite <- Rdiv_minus_distr.
 rewrite !big_sum_Rlistsum, Rlistsum_minus.
 unfold Rcountin.
 rewrite <- map_map with (g := fun x => frac_part (x - b) - frac_part x).
 rewrite <- map_map with (g := fun x => frac_part x).
 set (l := map u _).
 rewrite map_filter, map_length.
 destruct (Req_dec b 1) as [->|Hb1].
 - assert (Hb' : frac_part 1 = 0).
   { assert (E := int_frac 1).
     replace (Int_part 1) with 1%Z in E. lra.
     symmetry. apply int_part_iff. lra. }
   rewrite map_ext with (g:=fun _ => 0).
   2:{ intros x. rewrite Rminus_fp1. rewrite Hb'. lra. rewrite Hb'.
       generalize (base_fp x); lra. }
   rewrite Rlistsum_const, Rmult_0_l.
   rewrite filter_all.
   2:{ intros x Hx. apply RIn_spec. generalize (base_fp x); lra. }
   unfold l; rewrite map_length, seq_length. field.
   contradict Hn. now apply (INR_eq n 0) in Hn.
 - assert (Hb' : frac_part b = b).
   { rewrite (int_frac b) at 2.
     replace (Int_part b) with 0%Z. lra.
     symmetry. apply int_part_iff. rewrite Rminus_0_r. lra. }
   erewrite Rlistsum_perm.
   2:{ apply Permutation_map. symmetry.
       apply (filter_partition (RIn 0 b ∘ frac_part)). }
   rewrite map_app, Rlistsum_app.
   rewrite map_ext_in with (g := fun _ => 1-b).
   2:{ intros x Hx. rewrite filter_In in Hx. destruct Hx as (_,Hx).
       unfold compose in Hx. rewrite RIn_spec in Hx.
       rewrite Rminus_fp2, Hb'. lra. now rewrite Hb'. }
   rewrite Rlistsum_const.
   rewrite map_ext_in with (g:= fun _ => -b).
   2:{ intros x Hx. rewrite filter_In in Hx. destruct Hx as (_,Hx).
       unfold compose in Hx. rewrite negb_true_iff in Hx.
       rewrite <- not_true_iff_false, RIn_spec in Hx.
       rewrite Rminus_fp1, Hb'. lra. rewrite Hb'.
     generalize (base_fp x); lra. }
   rewrite Rlistsum_const.
   set (f := RIn 0 b ∘ frac_part).
   unfold Rminus.
   rewrite Rmult_plus_distr_r, Rplus_assoc, <- Rmult_plus_distr_l.
   rewrite <- plus_INR, filter_partition_length.
   unfold l at 2. rewrite map_length, seq_length. field.
   contradict Hn. now apply (INR_eq n 0) in Hn.
Qed.

Lemma EquiDistr01_alt2 u :
  EquiDistr01 (fun n => frac_part (u n)) <->
  forall a,
    is_lim_seq (fun n => mean_frac u n - mean_frac (fun m => u m + a) n) 0.
Proof.
 rewrite EquiDistr01_alt1. split; intros H.
 - intros a.
   set (b := frac_part (-a)).
   assert (Hb : 0 <= b < 1).
   { unfold b. generalize (base_fp (-a)); lra. }
   specialize (H b ltac:(lra)).
   rewrite is_lim_seq_incr_1 in H.
   rewrite is_lim_seq_incr_1.
   eapply is_lim_seq_ext.
   { intros n. symmetry. rewrite mean_frac_reduce'.
     rewrite <- Ropp_minus_distr.
     rewrite (mean_frac_eqn u (S n) _ lia); fold b; try lra.
     reflexivity. }
   replace 0 with (-(b-b)) at 1 by lra.
   apply is_lim_seq_opp'. apply is_lim_seq_minus'; trivial.
   apply is_lim_seq_const.
 - intros b Hb.
   specialize (H (-b)).
   rewrite is_lim_seq_incr_1 in H.
   rewrite is_lim_seq_incr_1.
   eapply is_lim_seq_ext in H.
   2:{ intros n. rewrite <- Ropp_minus_distr.
       assert (E := mean_frac_eqn u (S n) b lia Hb).
       unfold Rminus in *. rewrite E.
       rewrite Ropp_plus_distr, Ropp_involutive. reflexivity. }
   apply is_lim_seq_ext with
       (u :=fun n => - (- (Rcountin (frac_part ∘ u) 0 b (S n) / S n) + b) + b).
   { intros n. unfold compose. ring. }
   replace b with (-0+b) at 1 by lra.
   apply is_lim_seq_plus'. apply is_lim_seq_opp'; trivial.
   apply is_lim_seq_const.
Qed.

Lemma EquiDistr01_alt2b u :
  EquiDistr01 (fun n => frac_part (u n)) <->
  forall a, 0<a<1 ->
    is_lim_seq (fun n => mean_frac u n - mean_frac (fun m => u m + a) n) 0.
Proof.
 rewrite EquiDistr01_alt2. split.
 - intros H a _. apply (H a).
 - intros H a.
   eapply is_lim_seq_ext.
   { intros n. symmetry. rewrite mean_frac_reduce. reflexivity. }
   destruct (Req_dec (frac_part a) 0) as [->|Ha].
   { apply is_lim_seq_ext with (u:=fun _ => 0). 2:apply is_lim_seq_const.
     intros n. unfold mean_frac, mean. unfold compose.
     symmetry. apply Rminus_diag_eq. f_equal. apply big_sum_eq_bounded.
     intros x _. now rewrite Rplus_0_r. }
   apply H. generalize (base_fp a); lra.
Qed.

Theorem MultIrrat_EquiDistrMod1 t :
  irrat t -> EquiDistr01 (fun n => frac_part (t*n)).
Proof.
 intros Ht.
 apply EquiDistr01_alt2b.
 intros a Ha.
 assert (Ha1 : frac_part a = a).
 { unfold frac_part. replace (Int_part a) with 0%Z. lra.
   symmetry. apply int_part_iff. lra. }
 assert (Ha2 : frac_part (-a) = 1-a). { rewrite frac_part_opp; lra. }
 apply is_lim_seq_spec. intros eps.
 set (eps' := Rmin (eps/2) (Rmin a (1-a))).
 assert (Heps' : 0 < eps' <= eps/2).
 { split; try apply Rmin_l.
   unfold eps'. repeat apply Rmin_glb_lt; try lra.
   destruct eps; simpl; lra. }
 assert (Heps2 : eps' <= a).
 { unfold eps'. now rewrite Rmin_r, Rmin_l. }
 assert (Heps3 : eps' <= 1-a).
 { unfold eps'. now rewrite Rmin_r, Rmin_r. }
 set (eps2 := Rcomplements.pos_div_2 (mkposreal eps' (proj1 Heps'))).
 destruct (kronecker t (a+eps'/2) eps2) as (q1 & p1 & H1); trivial.
 destruct (kronecker t (a-eps'/2) eps2) as (q2 & p2 & H2); trivial.
 assert (H1' : a < frac_part (t*q1) < a + eps').
 { unfold frac_part.
   apply Rcomplements.Rabs_lt_between in H1.
   unfold eps2 in H1. simpl in H1.
   replace (Int_part (t*q1)) with p1. lra.
   symmetry; apply int_part_iff. lra. }
 assert (H2' : a-eps' < frac_part (t*q2) < a).
 { unfold frac_part.
   apply Rcomplements.Rabs_lt_between in H2.
   unfold eps2 in H2. simpl in H2.
   replace (Int_part (t*q2)) with p2. lra.
   symmetry; apply int_part_iff. lra. }
 clearbody eps'. clear p1 p2 H1 H2 eps2.
 exists (Nat.max (Nat.max q1 q2) (S (nat_part (Nat.max q1 q2 / eps')))).
 intros n Hn.
 assert (Hn1 : (q1 <= n)%nat) by lia.
 assert (Hn2 : (q2 <= n)%nat) by lia.
 assert (Hn' : Nat.max q1 q2 < n * eps').
 { apply Rmult_lt_reg_r with (r:=/eps').
   apply Rinv_0_lt_compat; try lra.
   field_simplify; try lra.
   eapply Rlt_le_trans.
   2:{ apply le_INR. eapply Nat.le_trans;[|apply Hn].
       apply Nat.le_max_r. }
   rewrite <- Nat.add_1_r, plus_INR. apply nat_part_INR.
   apply Rle_mult_inv_pos; try lra. apply pos_INR. }
 clear Hn.
 unfold mean_frac, mean. unfold compose. rewrite Rminus_0_r.
 rewrite <- Rdiv_minus_distr.
 apply Rcomplements.Rabs_lt_between, and_comm; split.
 - assert (Q : q1<>O).
   { intros ->. simpl in H1'. rewrite Rmult_0_r, fp_R0 in H1'. lra. }
   apply Rcomplements.Rlt_div_l. apply lt_0_INR; lia.
   assert (Hn1' : q1 < n * eps').
   { eapply Rle_lt_trans; [|apply Hn']. apply le_INR; lia. }
   clear Hn'.
   assert (E : frac_part (t*(-q1)) = 1 - frac_part (t*q1)).
   { rewrite <- Ropp_mult_distr_r, frac_part_opp. lra.
     unfold frac_part. intros E. apply Rminus_diag_uniq_sym in E.
     apply (Ht (Qmake (Int_part (t*q1)) (Pos.of_nat q1))).
     unfold Q2R. simpl. rewrite E.
     replace (Z.pos (Pos.of_nat q1)) with (Z.of_nat q1).
     rewrite <-INR_IZR_INZ. field. apply not_0_INR; lia.
     destruct q1; try lia. }
   assert (LT : forall m, frac_part (t*m) < frac_part (t*(m-q1)+a)+eps').
   { intros m.
     destruct (Rle_lt_dec 1 (frac_part (t*(m-q1))+frac_part (t*q1)))
      as [H|H].
     - assert (H' : frac_part(t*(-q1)) <= frac_part (t*(m-q1))).
       { rewrite E. lra. }
       replace (t*m) with (t*(m-q1) - t*(-q1)) by ring.
       rewrite Rminus_fp1, E by lra.
       apply Rlt_le_trans
         with (frac_part (t*(m - q1)) - frac_part (-a) + eps').
       lra. apply Rplus_le_compat_r.
       replace (_+a) with (t*(m-q1)-(-a)) by lra.
       destruct (Rle_lt_dec (frac_part (-a)) (frac_part (t*(m-q1)))).
       + rewrite Rminus_fp1; lra.
       + rewrite Rminus_fp2; lra.
     - assert (H' : frac_part (t*(m-q1)) < frac_part(t*(-q1))).
       { rewrite E. lra. }
       replace (t*m) with (t*(m-q1) - t*(-q1)) by ring.
       rewrite Rminus_fp2, E by lra. ring_simplify.
       assert (LT' : frac_part (t*(m - q1)) < frac_part (-a)).
       { eapply Rlt_le_trans; [apply H'|]. rewrite E, Ha2. lra. }
       replace (_+a) with (t*(m-q1)--a) by lra.
       rewrite Rminus_fp2 by lra. rewrite Ha2. ring_simplify. lra. }
   clear E.
   replace n with (q1+(n-q1))%nat at 1 by lia.
   rewrite big_sum_sum.
   replace n with ((n-q1)+q1)%nat at 2 by lia.
   rewrite big_sum_sum.
   unfold Rminus.
   rewrite Ropp_plus_distr. simpl. rewrite <- !Rplus_assoc.
   apply RealAux.Rlt_minus_l.
   apply Rlt_le_trans with (eps*n).
   2:{ rewrite <- (Rplus_0_r (eps*n)) at 1. apply Rplus_le_compat_l.
       apply RealAux.Rsum_ge_0. intros i _.
       generalize (base_fp (t*(n-q1+i)%nat+a)); lra. }
   rewrite Rplus_assoc, big_sum_Ropp, <- big_sum_Rplus.
   apply Rle_lt_trans with (q1 + n *eps').
   2:{ apply Rlt_le_trans with (n*eps' + n*eps'); try lra.
       rewrite (Rmult_comm eps). rewrite <- Rmult_plus_distr_l.
       apply Rmult_le_compat_l. apply (le_INR 0); lia. lra. }
   apply Rplus_le_compat.
   + rewrite <- (Rmult_1_l q1), <- big_sum_Rconst.
     apply RealAux.Rsum_le. intros i _.
     generalize (base_fp (t*i)); lra.
   + apply Rle_trans with ((n-q1)%nat*eps').
     2:{ apply Rmult_le_compat_r. lra. apply le_INR; lia. }
     rewrite Rmult_comm, <- big_sum_Rconst.
     apply RealAux.Rsum_le. intros i _.
     specialize (LT (q1+i)%nat). rewrite plus_INR in LT at 2.
     replace (q1+i-q1) with (INR i) in LT; lra.
 - assert (Q : q2<>O).
   { intros ->. simpl in H2'. rewrite Rmult_0_r, fp_R0 in H2'. lra. }
   apply Rcomplements.Rlt_div_r. apply lt_0_INR; lia.
   assert (Hn2' : q2 < n * eps').
   { eapply Rle_lt_trans; [|apply Hn']. apply le_INR; lia. }
   clear Hn'.
   assert (E : frac_part (t*(-q2)) = 1 - frac_part (t*q2)).
   { rewrite <- Ropp_mult_distr_r, frac_part_opp. lra.
     unfold frac_part. intros E. apply Rminus_diag_uniq_sym in E.
     apply (Ht (Qmake (Int_part (t*q2)) (Pos.of_nat q2))).
     unfold Q2R. simpl. rewrite E.
     replace (Z.pos (Pos.of_nat q2)) with (Z.of_nat q2).
     rewrite <-INR_IZR_INZ. field. apply not_0_INR; lia.
     destruct q2; try lia. }
   assert (LT : forall m, frac_part (t*m) > frac_part (t*(m-q2)+a)-eps').
   { intros m.
     destruct (Rle_lt_dec 1 (frac_part (t*(m-q2))+frac_part (t*q2)))
      as [H|H].
     - assert (H' : frac_part(t*(-q2)) <= frac_part (t*(m-q2))).
       { rewrite E. lra. }
       replace (t*m) with (t*(m-q2) - t*(-q2)) by ring.
       rewrite Rminus_fp1, E by lra.
       apply Rle_lt_trans
         with (frac_part (t*(m - q2)) - frac_part (-a) - eps').
       2:lra. apply Rplus_le_compat_r.
       assert (LT' : frac_part (t*(m - q2)) > frac_part (-a)).
       { eapply Rlt_le_trans; [|apply H']. rewrite E, Ha2. lra. }
       replace (_+a) with (t*(m-q2)--a) by lra.
       rewrite Rminus_fp1; lra.
     - assert (H' : frac_part (t*(m-q2)) < frac_part(t*(-q2))).
       { rewrite E. lra. }
       replace (t*m) with (t*(m-q2) - t*(-q2)) by ring.
       rewrite Rminus_fp2, E by lra.
       replace (_+a) with (t*(m-q2)--a) by lra.
       destruct (Rle_lt_dec (frac_part (-a)) (frac_part (t*(m-q2)))).
       + rewrite Rminus_fp1; lra.
       + rewrite Rminus_fp2; lra. }
   clear E.
   replace n with (q2+(n-q2))%nat at 2 by lia.
   rewrite big_sum_sum.
   replace n with ((n-q2)+q2)%nat at 3 by lia.
   rewrite big_sum_sum.
   unfold Rminus.
   rewrite Ropp_plus_distr. simpl. rewrite !Rplus_assoc.
   rewrite <- (Rplus_0_l (-eps*n)).
   apply Rplus_le_lt_compat.
   { apply RealAux.Rsum_ge_0. intros i _.
     generalize (base_fp (t*i)); lra. }
   rewrite <- Rplus_assoc, big_sum_Ropp, <- big_sum_Rplus.
   apply Rlt_le_trans with (- n*eps' - q2).
   { apply Rle_lt_trans with (-n*eps' + -n*eps'); try lra.
     rewrite (Rmult_comm (-eps)). rewrite <- Rmult_plus_distr_l.
     rewrite <- Ropp_mult_distr_l, Ropp_mult_distr_r.
     apply Rmult_le_compat_l. apply (le_INR 0); lia. lra. }
   apply Rplus_le_compat.
   + apply Rle_trans with ((n-q2)%nat*(-eps')).
     { rewrite <- Ropp_mult_distr_r, Ropp_mult_distr_l.
       apply Rmult_le_compat_r. lra. apply Ropp_le_contravar.
       apply le_INR; lia. }
     rewrite Rmult_comm, <- big_sum_Rconst.
     apply RealAux.Rsum_le. intros i _.
     specialize (LT (q2+i)%nat). rewrite plus_INR in LT at 2.
     replace (q2+i-q2) with (INR i) in LT; lra.
   + apply Ropp_le_contravar.
     rewrite <- (Rmult_1_l q2), <- big_sum_Rconst.
     apply RealAux.Rsum_le. intros i _.
     generalize (base_fp (t*(n-q2+i)%nat+a)); lra.
Qed.

Lemma maxseqexists p (u : nat -> nat -> R) (eps:posreal) lim :
 (forall q, (q < p)%nat ->
  exists N, forall n, (N<=n)%nat -> Rabs (u q n - lim) < eps) ->
 exists N, forall n, (N <= n)%nat ->
  forall q, (q<p)%nat -> Rabs ((u q n) - lim) < eps.
Proof.
 induction p; intros H.
 - now exists O.
 - destruct IHp as (N & HN).
   { intros q Hq. apply H. lia. }
   destruct (H p lia) as (N' & HN').
   exists (Nat.max N N'). intros n Hn q Hq.
   inversion_clear Hq.
   + apply HN'. lia.
   + apply HN; lia.
Qed.

Lemma sum_rcountin_bounds (u:nat->R) (p:nat) :
  (p<>0)%nat ->
  (forall n, 0 <= u n < 1) ->
  forall n,
  big_sum (fun q => q/p * Rcountin u (q/p) (S q/p) n) p
  <= big_sum u n <=
  big_sum (fun q => S q/p * Rcountin u (q/p) (S q/p) n) p.
Proof.
 intros Hp Hu.
 induction n.
 - simpl (big_sum u 0).
   rewrite big_sum_eq_bounded with (g := fun _ => 0)
     by (intros; simpl; lra).
   rewrite big_sum_Rconst.
   rewrite big_sum_eq_bounded with (g := fun _ => 0)
     by (intros; simpl; lra).
   rewrite big_sum_Rconst. lra.
 - simpl (big_sum u (S n)).
   set (q0 := nat_part (p * u n)).
   assert (Hq0 : (q0 < p)%nat).
   { apply nat_part_lt. split.
     - apply Rmult_le_pos. apply pos_INR. apply Hu.
     - rewrite <- (Rmult_1_r p) at 2. apply Rmult_lt_compat_l.
       + apply (lt_INR 0). lia.
       + apply Hu. }
   assert (H1 : RIn (q0/p) (S q0/p) (u n) = true).
   { rewrite RIn_spec. split.
     - apply Rmult_le_reg_l with p. apply (lt_INR 0); lia.
       field_simplify. 2:{ apply (not_INR p 0); lia. }
       apply nat_part_le; try easy.
       apply Rmult_le_pos. apply pos_INR. apply Hu.
     - apply Rmult_lt_reg_l with p. apply (lt_INR 0); lia.
       field_simplify. 2:{ apply (not_INR p 0); lia. }
       rewrite S_INR. apply nat_part_INR.
       apply Rmult_le_pos. apply pos_INR. apply Hu. }
   assert (H2 : forall q, q<>q0 -> RIn (q/p) (S q/p) (u n) = false).
   { intros q. rewrite <- not_true_iff_false.
     intros Hq. contradict Hq. rewrite RIn_spec in H1, Hq.
     assert ((q < S q0)%nat).
     { apply INR_lt. apply Rmult_lt_reg_r with (/p); try lra.
       apply Rinv_0_lt_compat, (lt_INR 0); lia. }
     assert ((q0 < S q)%nat).
     { apply INR_lt. apply Rmult_lt_reg_r with (/p); try lra.
       apply Rinv_0_lt_compat, (lt_INR 0); lia. }
     lia. }
   split.
   + erewrite big_sum_eq_bounded.
     2:{ intros q Hq. now rewrite Rcountin_S, plus_INR, Rmult_plus_distr_l. }
     rewrite big_sum_Rplus.
     apply Rplus_le_compat. apply IHn.
     rewrite big_sum_kronecker_R with (m:=q0); trivial.
     * rewrite H1. simpl. apply RIn_spec in H1. lra.
     * intros q Hq Hq'. rewrite H2; trivial. simpl. lra.
   + erewrite big_sum_eq_bounded with (n:=p).
     2:{ intros q Hq. now rewrite Rcountin_S, plus_INR, Rmult_plus_distr_l. }
     rewrite big_sum_Rplus.
     apply Rplus_le_compat. apply IHn.
     rewrite big_sum_kronecker_R with (m:=q0); trivial.
     * rewrite H1. rewrite Rmult_1_r. apply RIn_spec in H1. lra.
     * intros q Hq Hq'. rewrite H2; trivial. apply Rmult_0_r.
Qed.

(** Corollary : the mean of these fractional parts tends to 0.5.
    This is usually a direct consequence of the Riemann integral criterium:
    https://en.wikipedia.org/wiki/Equidistributed_sequence
    We rather formalize here a direct proof. *)

Theorem MultIrrat_mean t :
  irrat t -> is_lim_seq (fun n => mean (fun m => frac_part (t*m)) n) 0.5.
Proof.
 intros Ht.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_spec. intros eps.
 set (p := S (nat_part (/eps))).
 assert (Hp : 0 < p). { apply lt_0_INR. lia. }
 assert (Hp' : 0 < /p). { now apply Rinv_0_lt_compat. }
 assert (Hp_eps : /p < eps).
 { rewrite <- (Rinv_inv eps).
   apply Rinv_lt_contravar.
   - apply Rmult_lt_0_compat; trivial. apply Rinv_0_lt_compat, eps.
   - unfold p. rewrite S_INR.
     apply nat_part_INR. apply Rlt_le, Rinv_0_lt_compat, eps. }
 assert (LT : 0 < /(p*(p+1))).
 { apply Rinv_0_lt_compat, Rmult_lt_0_compat; lra. }
 set (eps' := mkposreal _ LT).
 set (f := fun (m:nat) => frac_part (t*m)).
 destruct (maxseqexists p (fun q n => Rcountin f (q/p) ((S q)/p) (S n) /S n)
            eps' (/p)) as (N & HN).
 { intros q Hq.
   generalize eps'.
   change (is_lim_seq' (fun n => Rcountin f (q/p) (S q/p) (S n) /S n) (/p)).
   apply is_lim_seq_spec.
   replace (/p) with (S q/p - q/p).
   2:{ rewrite S_INR. unfold Rdiv. rewrite Rmult_plus_distr_r. ring. }
   rewrite <- is_lim_seq_incr_1
   with (u := fun n => Rcountin f (q / p) (S q / p) n / n).
   apply (MultIrrat_EquiDistrMod1 t Ht (q/p) (S q/p)).
   { unfold Rdiv. apply Rmult_le_pos. apply pos_INR. lra. }
   { rewrite S_INR. unfold Rdiv. rewrite Rmult_plus_distr_r. lra. }
   { apply Rmult_le_reg_r with (r:=p). trivial. field_simplify; try lra.
     apply le_INR. lia. }}
 exists N. intros n Hn. specialize (HN n Hn).
 assert (Hf : forall n, 0 <= f n < 1).
 { intros m. generalize (base_fp (t*m)); unfold f; lra. }
 destruct (sum_rcountin_bounds f p lia Hf (S n)) as (LE,GE).
 unfold mean. apply Rcomplements.Rabs_lt_between. split.
 - apply RealAux.Rlt_minus_r. rewrite Rplus_comm.
   apply Rmult_lt_reg_r with (S n). apply (lt_INR 0); lia.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_l.
   2:{ apply (not_INR (S n) 0); lia. }
   rewrite Rmult_1_r.
   eapply Rlt_le_trans; [|apply LE]. clear LE GE.
   apply Rmult_lt_reg_r with (/S n).
   { apply Rinv_0_lt_compat, (lt_INR 0); lia. }
   rewrite Rmult_assoc, Rinv_r.
   2:{ apply (not_INR (S n) 0); lia. }
   rewrite Rmult_1_r.
   unfold Rdiv. rewrite big_sum_Rmult_r.
   eapply Rlt_le_trans;
     [|eapply RealAux.Rsum_le with (f:= fun q => q/(p*(p+1)))].
   2:{ intros q Hq.
       unfold Rdiv. rewrite Rinv_mult, <- Rmult_assoc.
       rewrite (Rmult_assoc _ _ (/S n)).
       apply Rmult_le_compat_l.
       { apply Rmult_le_pos. apply pos_INR.
         apply Rlt_le, Rinv_0_lt_compat; trivial. }
       specialize (HN q Hq).
       apply Rcomplements.Rabs_lt_between in HN. destruct HN as (HN,_).
       apply RealAux.Rlt_minus_r in HN.
       eapply Rle_trans; [|apply Rlt_le, HN].
       change (pos eps') with (/(p*(p+1))).
       apply RealAux.Rminus_le_0. field_simplify. unfold Rdiv.
       rewrite Rmult_0_l; lra. nra. }
   unfold Rdiv. rewrite <- big_sum_Rmult_r.
   rewrite big_sum_id.
   replace 0.5 with (/2) by lra.
   apply Rlt_le_trans with (/2 - /p); try lra.
   apply RealAux.Rminus_le_0. field_simplify.
   replace (2/_) with (/(p*(p+1))). apply Rlt_le, LT. field. nra. nra.
 - apply RealAux.Rlt_minus_l.
   apply Rmult_lt_reg_r with (S n). apply (lt_INR 0); lia.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_l.
   2:{ apply (not_INR (S n) 0); lia. }
   rewrite Rmult_1_r.
   eapply Rle_lt_trans; [apply GE|]. clear LE GE.
   apply Rmult_lt_reg_r with (/S n).
   { apply Rinv_0_lt_compat, (lt_INR 0); lia. }
   rewrite Rmult_assoc, Rinv_r.
   2:{ apply (not_INR (S n) 0); lia. }
   rewrite Rmult_1_r.
   unfold Rdiv. rewrite big_sum_Rmult_r.
   eapply Rle_lt_trans;
     [eapply RealAux.Rsum_le with (g:= fun q => S q/p * (p+2)/(p*(p+1)))|].
   { intros q Hq.
     unfold Rdiv.
     rewrite (Rmult_assoc _ _ (/S n)), (Rmult_assoc _ _ (/(p * (p+1)))).
     apply Rmult_le_compat_l.
     { apply Rmult_le_pos. apply pos_INR.
       apply Rlt_le, Rinv_0_lt_compat; trivial. }
     specialize (HN q Hq).
     apply Rcomplements.Rabs_lt_between in HN. destruct HN as (_,HN).
     apply RealAux.Rlt_minus_l in HN.
     eapply Rle_trans; [apply Rlt_le, HN|].
     change (pos eps') with (/(p*(p+1))).
     apply RealAux.Rminus_le_0. field_simplify. unfold Rdiv.
     rewrite Rmult_0_l; lra. nra. }
   unfold Rdiv. rewrite <- 3 big_sum_Rmult_r.
   assert (E := big_sum_shift p INR). change Gplus with Rplus in E.
   rewrite Rplus_0_l in E. rewrite <- E, big_sum_id. rewrite S_INR.
   replace 0.5 with (/2) by lra.
   apply Rle_lt_trans with (/p + /2); try lra.
   apply RealAux.Rminus_le_0. field_simplify; nra.
Qed.

(** A strict version of Rcountin, handy for Ropp *)

Definition RStrIn a b x := Rltb a x && Rltb x b.

Lemma RStrIn_spec a b r : RStrIn a b r = true <-> a < r < b.
Proof.
 unfold RStrIn. repeat case Rltb_spec; simpl; lra.
Qed.

Definition RcountStrIn (u:nat->R) a b n :=
 length (filter (RStrIn a b) (map u (seq 0 n))).

Lemma RcountStrIn_noitvl (f:nat->R) a b n : b<=a -> RcountStrIn f a b n = O.
Proof.
 intros Hab.
 unfold RcountStrIn. rewrite map_filter, map_length.
 rewrite filter_nop; trivial.
 intros x _. apply not_true_iff_false. unfold compose.
 rewrite RStrIn_spec; lra.
Qed.

Lemma RcountStrIn_opp u a b n:
  RcountStrIn (Ropp ∘ u) (-b) (-a) n = RcountStrIn u a b n.
Proof.
 unfold RcountStrIn. rewrite !map_filter, !map_length. unfold compose.
 f_equal. apply filter_ext.
 intros m. apply eq_true_iff_eq. rewrite !RStrIn_spec. lra.
Qed.

(** For injective functions, RcountStrIn and Rcountin differ by at most 1 *)

Lemma Rcountin_strin (u:nat->R) a b n :
 FinFun.Injective u ->
 (RcountStrIn u a b n <= Rcountin u a b n <= S (RcountStrIn u a b n))%nat.
Proof.
 intros Hu.
 destruct (Rlt_le_dec b a).
 { rewrite Rcountin_noitvl, RcountStrIn_noitvl; try lia; try lra. }
 unfold Rcountin, RcountStrIn.
 rewrite !map_filter, !map_length. unfold compose.
 erewrite filter_ext with
  (f:=fun m => RIn _ _ _)
  (g:=fun m => (RStrIn a b (u m)) || (Rltb a b && (Req_EM_T (u m) a ||| false))).
 2:{ intros m. unfold RIn, RStrIn.
     destruct (Req_EM_T (u m) a) as [->|N];
     case Rleb_spec; intros; simpl; try lra;
     repeat (case Rltb_spec; intros; simpl; try lra). }
 rewrite filter_or_disj.
 2:{ intros m _.
     destruct (Req_EM_T (u m) a) as [->|N].
     - unfold RStrIn. case (Rltb_spec a a); intros; simpl; lra.
     - now rewrite !andb_false_r. }
 set (L1 := length _).
 set (L2 := length _).
 assert (H2 : (L2 <= 1)%nat); try lia.
 { apply filter_uniq. 2:apply seq_NoDup.
   intros p q _ _. destruct (Rltb a b); simpl; try easy.
   destruct (Req_EM_T (u p) a) as [E|N]; try easy.
   destruct (Req_EM_T (u q) a) as [E'|N']; try easy.
   intros _ _. apply (Hu p q). lra. }
Qed.

(** The densities are hence unchanged *)

Lemma Rcountin_strin_lim (u:nat->R) a b (lim:R) :
 FinFun.Injective u ->
 is_lim_seq (fun n => Rcountin u a b n/n) lim <->
 is_lim_seq (fun n => RcountStrIn u a b n/n) lim.
Proof.
 intros Hu.
 split; intros LI.
 - eapply is_lim_seq_le_le
     with (u:=fun n => Rcountin u a b n/n-/n)
          (w:=fun n => Rcountin u a b n/n); trivial.
   2:{ replace lim with (lim-0) by lra. apply is_lim_seq_minus'; trivial.
       apply is_lim_seq_invn. }
   intros n.
   destruct (Rcountin_strin u a b n Hu) as (H,H').
   apply le_INR in H, H'. rewrite S_INR in H'.
   assert (Hn : 0 <= /n).
   { destruct n. simpl. rewrite Rinv_0; lra.
     apply Rlt_le, Rinv_0_lt_compat. apply (lt_INR 0); lia. }
   apply Rmult_le_compat_r with (r:=/n) in H, H'; trivial.
   unfold Rdiv; lra.
 - eapply is_lim_seq_le_le
     with (u:=fun n => RcountStrIn u a b n/n)
          (w:=fun n => RcountStrIn u a b n/n+/n); trivial.
   2:{ replace lim with (lim+0) by lra. apply is_lim_seq_plus'; trivial.
       apply is_lim_seq_invn. }
   intros n.
   destruct (Rcountin_strin u a b n Hu) as (H,H').
   apply le_INR in H, H'. rewrite S_INR in H'.
   assert (Hn : 0 <= /n).
   { destruct n. simpl. rewrite Rinv_0; lra.
     apply Rlt_le, Rinv_0_lt_compat. apply (lt_INR 0); lia. }
   apply Rmult_le_compat_r with (r:=/n) in H, H'; trivial.
   unfold Rdiv; lra.
Qed.
