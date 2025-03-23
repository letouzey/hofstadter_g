From Coq Require Import Arith NArith Lia QArith Reals Lra Qreals.
From Hofstadter.HalfQuantum Require Import Complex.
Require Import MoreTac MoreFun MoreList MoreReals MoreLim MoreComplex MoreSum.
Require Import DeltaList GenFib GenG GenAdd Words Mu ThePoly.
Local Open Scope C.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion RtoC : R >-> C.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * Discrepancy

    Differences between the f functions and their linear equivalents.
    [AllDeltas] provides global expressions for sets of discrepancies
    up to some [A] numbers, and [MaxDeltas] and [MinDeltas] their max
    and min. Interestingly, these definitions follow once again
    the same recursive pattern.

    Then we prove that the discrepancies will remain bounded when
    the secondary roots of ThePoly are all of modulus < 1.
    For the unbounded discrepancies, see Freq.v and F5.v.

    Naming convention:
    k is the recursion depth in the definition of functions f
    p is used to enumerate the A numbers
    n is for succesive points (typically here, [n < A k p])
*)

Definition diff k n := f k n - tau k * n.

Fixpoint AllDeltas (k p:nat) :=
 match p with
 | 0 => [0]
 | S p => AllDeltas k p ++ map (Rplus (diff k (A k p))) (AllDeltas k (p-(k-1)))
 end.

Fixpoint MaxDeltas (k p:nat) :=
 match p with
 | 0 => 0
 | S p => Rmax (MaxDeltas k p) (MaxDeltas k (p-(k-1)) + diff k (A k p))
 end.

Fixpoint MinDeltas (k p:nat) :=
 match p with
 | 0 => 0
 | S p => Rmin (MinDeltas k p) (MinDeltas k (p-(k-1)) + diff k (A k p))
 end.

(** Basic properties about diff *)

Lemma diff_app k l l' : k<>O -> Delta k (l++l') ->
 diff k (sumA k (l++l')) = diff k (sumA k l) + diff k (sumA k l').
Proof.
 intros K D.
 assert (D' := D). apply Delta_app_inv in D'. destruct D' as (D1 & D2 & _).
 unfold diff. rewrite !f_sumA by trivial.
 rewrite map_app, !sumA_app, !plus_INR. lra.
Qed.

Lemma diff_app_singl k l p : k<>O -> Delta k (l++[p]) ->
 diff k (sumA k (l++[p])) = diff k (sumA k l) + diff k (A k p).
Proof.
 intros K D. rewrite diff_app; trivial. f_equal; f_equal. simpl. lia.
Qed.

Lemma diff_add k n p : k<>O ->(n < A k (p-(k-1)))%nat ->
  diff k (n + A k p) = diff k n + diff k (A k p).
Proof.
 intros K Hn.
 assert (E : decomp k (n+A k p) = decomp k n++[p]).
 { now apply decomp_plus_A. }
 rewrite <- (decomp_sum k (n+A k p)), E.
 rewrite diff_app_singl, decomp_sum; trivial.
 rewrite <- E. apply decomp_delta.
Qed.

Lemma diff_A_A k p p' : (1<k)%nat -> (p+(k-1) <= p')%nat ->
  diff k (A k p + A k p') = diff k (A k p) + diff k (A k p').
Proof.
 intros K H.
 unfold diff.
 replace (A k p + A k p')%nat with (sumA k [p;p']) by (simpl; lia).
 rewrite f_sumA_lax, !f_A; try lia.
 2:{ repeat constructor. lia. }
 simpl. rewrite <- !Nat.sub_1_r, !plus_INR. simpl. lra.
Qed.

(** Properties of AllDeltas *)

Lemma AllDeltas_len k p : length (AllDeltas k p) = A k p.
Proof.
 induction p as [[|p] IH] using lt_wf_ind; try easy.
 simpl. rewrite app_length, map_length. f_equal; apply IH; lia.
Qed.

Lemma AllDeltas_spec k p n :
  k<>O -> (n < A k p)%nat -> nth n (AllDeltas k p) 0 = diff k n.
Proof.
 intros K. revert n.
 induction p as [[|p] IH] using lt_wf_ind.
 - intros n Hn. unfold diff. simpl in *. replace n with O by lia. simpl. lra.
 - intros n Hn. simpl in *.
   destruct (Nat.ltb_spec n (A k p)).
   + rewrite app_nth1.
     2:{ now rewrite AllDeltas_len. }
     apply IH; trivial; lia.
   + rewrite app_nth2.
     2:{ now rewrite AllDeltas_len. }
     rewrite nth_map_indep with (d':=0).
     2:{ rewrite !AllDeltas_len. simpl in Hn. lia. }
     rewrite AllDeltas_len. simpl in Hn.
     rewrite IH; trivial; try lia. clear IH.
     replace n with ((n-A k p)+A k p)%nat at 2 by lia.
     rewrite diff_add; trivial. lra. lia.
Qed.

Lemma AllDeltas_spec' k p x : k<>O ->
  In x (AllDeltas k p) <-> exists n, (n < A k p)%nat /\ diff k n = x.
Proof.
 intros K. split.
 - intros IN. destruct (In_nth _ _ 0 IN) as (n & Hn & E).
   rewrite AllDeltas_len in Hn.
   exists n. split; trivial. now rewrite AllDeltas_spec in E.
 - intros (n & Hn & <-).
   rewrite <- (AllDeltas_spec k p n) by trivial.
   apply nth_In. now rewrite AllDeltas_len.
Qed.

(** Properties of MaxDeltas *)

Lemma MaxDeltas_spec k p n :
  k<>O -> (n < A k p)%nat -> diff k n <= MaxDeltas k p.
Proof.
 intros K Hn. rewrite <- (AllDeltas_spec k p n K Hn).
 revert n Hn.
 induction p as [[|p] IH] using lt_wf_ind.
 - intros n Hn. simpl in *. replace n with O by lia. lra.
 - intros n Hn. simpl in *.
   destruct (Nat.ltb_spec n (A k p)).
   + rewrite app_nth1.
     2:{ now rewrite AllDeltas_len. }
     eapply Rle_trans; [apply IH|]; trivial; try lia. apply Rmax_l.
   + rewrite app_nth2.
     2:{ now rewrite AllDeltas_len. }
     rewrite nth_map_indep with (d':=0).
     2:{ rewrite !AllDeltas_len. simpl in Hn. lia. }
     rewrite AllDeltas_len. simpl in Hn.
     rewrite Rplus_comm.
     eapply Rle_trans; [|apply Rmax_r].
     apply Rplus_le_compat_r, IH; lia.
Qed.

Lemma MaxDeltas_reached k p :
  k<>O -> exists n, (n < A k p)%nat /\ MaxDeltas k p = diff k n.
Proof.
 intros K. induction p as [[|p] IH] using lt_wf_ind.
 - exists 0%nat. split; simpl. lia. unfold diff; simpl; lra.
 - simpl.
   destruct (IH p lia) as (n1 & Hn1 & E1).
   destruct (IH (p-(k-1))%nat lia) as (n2 & Hn2 & E2).
   destruct (Rle_lt_dec (diff k n2 + diff k (A k p)) (diff k n1)).
   + exists n1. split. lia. rewrite E1, E2, Rmax_left; lra.
   + exists (n2+A k p)%nat. split. lia. rewrite E1, E2, Rmax_right by lra.
     symmetry. now apply diff_add.
Qed.

Lemma MaxDeltas_incr k p : MaxDeltas k p <= MaxDeltas k (S p).
Proof.
 apply Rmax_l.
Qed.

Lemma MaxDeltas_mono k p p' :
  (p <= p')%nat -> MaxDeltas k p <= MaxDeltas k p'.
Proof.
 induction 1. lra. eapply Rle_trans; [apply IHle|]. apply MaxDeltas_incr.
Qed.

Lemma MaxDeltas_pos k p : 0 <= MaxDeltas k p.
Proof.
 apply (MaxDeltas_mono k 0). lia.
Qed.

Lemma MaxDeltas_has_lim k : ex_lim_seq (MaxDeltas k).
Proof.
 eapply ex_lim_seq_incr. apply MaxDeltas_incr.
Qed.

Definition sup_deltas k : Rbar.Rbar := Lim_seq (MaxDeltas k).

(** This sup_deltas will be finite exactly when k <= 4 *)

Lemma MaxDeltas_lim k : is_lim_seq (MaxDeltas k) (sup_deltas k).
Proof.
 apply Lim_seq_correct. apply MaxDeltas_has_lim.
Qed.

Lemma MaxDeltas_below_lim k p : Rbar.Rbar_le (MaxDeltas k p) (sup_deltas k).
Proof.
 unfold sup_deltas.
 rewrite <- (Lim_seq_const (MaxDeltas k p)).
 apply Lim_seq_le_loc.
 exists p. apply MaxDeltas_mono.
Qed.

Lemma diff_le_sup k n : k<>O -> Rbar.Rbar_le (diff k n) (sup_deltas k).
Proof.
 intros K. destruct (invA_spec k n) as (_,LT).
 set (p := (S (invA k n))) in *.
 apply Rbar.Rbar_le_trans with (MaxDeltas k p).
 + apply MaxDeltas_spec; trivial. lia.
 + apply MaxDeltas_below_lim.
Qed.

Lemma diff_sup k : k<>O -> Sup_seq (diff k) = sup_deltas k.
Proof.
 intros K. apply is_sup_seq_unique. red.
 destruct sup_deltas as [l| | ] eqn:E.
 - intros eps. split.
   + intros n. simpl.
     apply Rle_lt_trans with l. 2:{ destruct eps. simpl. lra. }
     generalize (diff_le_sup k n K). now rewrite E.
   + assert (L := MaxDeltas_lim k). rewrite E in L.
     apply is_lim_seq_spec in L.
     destruct (L eps) as (N & HN).
     specialize (HN N lia).
     destruct (MaxDeltas_reached k N K) as (n & _ & E').
     exists n. simpl. rewrite <- E'.
     apply Rcomplements.Rabs_lt_between in HN. lra.
 - intros M.
   assert (L := MaxDeltas_lim k). rewrite E in L.
   apply is_lim_seq_spec in L.
   destruct (L M) as (N & HN). specialize (HN N lia).
   destruct (MaxDeltas_reached k N K) as (n & _ & E').
   exists n. simpl. now rewrite <- E'.
 - generalize (MaxDeltas_below_lim k 0). rewrite E. simpl. easy.
Qed.

(** Properties of MinDeltas *)

Lemma MinDeltas_spec k p n :
  k<>O -> (n < A k p)%nat -> MinDeltas k p <= diff k n.
Proof.
 intros K Hn. rewrite <- (AllDeltas_spec k p n K Hn).
 revert n Hn.
 induction p as [[|p] IH] using lt_wf_ind.
 - intros n Hn. simpl in *. replace n with O by lia. lra.
 - intros n Hn. simpl in *.
   destruct (Nat.ltb_spec n (A k p)).
   + rewrite app_nth1.
     2:{ now rewrite AllDeltas_len. }
     eapply Rle_trans; [|apply IH]; trivial; try lia. apply Rmin_l.
   + rewrite app_nth2.
     2:{ now rewrite AllDeltas_len. }
     rewrite nth_map_indep with (d':=0).
     2:{ rewrite !AllDeltas_len. simpl in Hn. lia. }
     rewrite AllDeltas_len. simpl in Hn.
     rewrite Rplus_comm.
     eapply Rle_trans; [apply Rmin_r|].
     apply Rplus_le_compat_l, IH; lia.
Qed.

Lemma MinDeltas_reached k p :
  k<>O -> exists n, (n < A k p)%nat /\ MinDeltas k p = diff k n.
Proof.
 intros K. induction p as [[|p] IH] using lt_wf_ind.
 - exists 0%nat. split; simpl. lia. unfold diff; simpl; lra.
 - simpl.
   destruct (IH p lia) as (n1 & Hn1 & E1).
   destruct (IH (p-(k-1))%nat lia) as (n2 & Hn2 & E2).
   destruct (Rle_lt_dec (diff k n1) (diff k n2 + diff k (A k p))).
   + exists n1. split. lia. rewrite E1, E2, Rmin_left; lra.
   + exists (n2+A k p)%nat. split. lia. rewrite E1, E2, Rmin_right by lra.
     symmetry. now apply diff_add.
Qed.

Lemma MinDeltas_decr k p : MinDeltas k (S p) <= MinDeltas k p.
Proof.
 simpl. apply Rmin_l.
Qed.

Lemma MinDeltas_mono k p p' :
  (p <= p')%nat -> MinDeltas k p' <= MinDeltas k p.
Proof.
 induction 1. lra. eapply Rle_trans; [|apply IHle]. apply MinDeltas_decr.
Qed.

Lemma MinDeltas_neg k p : MinDeltas k p <= 0.
Proof.
 apply (MinDeltas_mono k 0). lia.
Qed.

Lemma MinDeltas_has_lim k : ex_lim_seq (MinDeltas k).
Proof.
 eapply ex_lim_seq_decr. apply MinDeltas_decr.
Qed.

Definition inf_deltas k : Rbar.Rbar := Lim_seq (MinDeltas k).

(** This limit is finite exactly when k <= 4 *)

Lemma MinDeltas_lim k : is_lim_seq (MinDeltas k) (inf_deltas k).
Proof.
 apply Lim_seq_correct. apply MinDeltas_has_lim.
Qed.

Lemma MinDeltas_above_lim k p : Rbar.Rbar_le (inf_deltas k) (MinDeltas k p).
Proof.
 unfold inf_deltas.
 rewrite <- (Lim_seq_const (MinDeltas k p)).
 apply Lim_seq_le_loc.
 exists p. apply MinDeltas_mono.
Qed.

Lemma diff_ge_inf k n : k<>O -> Rbar.Rbar_le (inf_deltas k) (diff k n).
Proof.
 intros K. destruct (invA_spec k n) as (_,LT).
 set (p := (S (invA k n))) in *.
 apply Rbar.Rbar_le_trans with (MinDeltas k p).
 + apply MinDeltas_above_lim.
 + apply MinDeltas_spec; lia.
Qed.

Lemma diff_inf k : k<>O -> Inf_seq (diff k) = (inf_deltas k).
Proof.
 intros K. apply is_inf_seq_unique. red.
 destruct inf_deltas as [l| | ] eqn:E.
 - intros eps. split.
   + intros n. simpl.
     apply Rlt_le_trans with l. { destruct eps. simpl. lra. }
     generalize (diff_ge_inf k n K). now rewrite E.
   + assert (L := MinDeltas_lim k). rewrite E in L.
     apply is_lim_seq_spec in L.
     destruct (L eps) as (N & HN).
     specialize (HN N lia).
     destruct (MinDeltas_reached k N K) as (n & _ & E').
     exists n. simpl. rewrite <- E'.
     apply Rcomplements.Rabs_lt_between in HN. lra.
 - generalize (MinDeltas_above_lim k 0). rewrite E. simpl. easy.
 - intros M.
   assert (L := MinDeltas_lim k). rewrite E in L.
   apply is_lim_seq_spec in L.
   destruct (L M) as (N & HN). specialize (HN N lia).
   destruct (MinDeltas_reached k N K) as (n & _ & E').
   exists n. simpl. now rewrite <- E'.
Qed.

(** Generic proof that the discrepancies are bounded when
    the secondary roots of ThePoly are of modulus < 1. *)

Section LowSecondRoots.
Variable k : nat.
Hypothesis K : (1 < k)%nat.
Variable roots : list C.
Hypothesis roots_ok : SortedRoots k roots.
Hypothesis LowSecond : Cmod (roots@1) < 1.

Lemma tl_roots_nonnil : tl roots <> [].
Proof.
 apply SortedRoots_length in roots_ok.
 destruct roots; simpl in *; try easy. subst; lia.
 intros ->. simpl in *. lia.
Qed.

Lemma coefdA_pos z : In z (tl roots) -> 0 < Cmod (coefdA k z).
Proof.
 intros Hz.
 apply Cmod_gt_0, coefdA_nz.
 - apply (SortedRoots_roots k roots roots_ok).
   destruct roots; simpl in *; tauto.
 - rewrite <- (SortedRoots_mu k roots roots_ok). intros ->.
   apply SortedRoots_nodup in roots_ok.
   destruct roots; unfold Cnth in *; simpl in *; try easy.
   now inversion_clear roots_ok.
Qed.

Lemma low_secondary_roots z : In z (tl roots) -> 0 < Cmod z < 1.
Proof.
 intros Hz. split.
 - apply Cmod_gt_0. intros ->.
   apply (root_nz k). apply (SortedRoots_roots k _ roots_ok).
   destruct roots; simpl in *; tauto.
 - apply (SortedRoots_Cmod_sorted k) in roots_ok.
   rewrite StronglySorted_nth in roots_ok.
   destruct (In_nth _ _ 0%C Hz) as (p & Hp & E).
   destruct roots as [|mu rt]; try easy. simpl in *.
   destruct p as [|p]. rewrite <- E; apply LowSecond.
   specialize (roots_ok 1%nat (S (S p)) lia).
   unfold Cnth in *; simpl in *. rewrite E in *. lra.
Qed.

Definition residue p :=
  Rlistsum
    (map (fun z => Cmod (coefdA k z) * Cmod z^p / (1 - Cmod z^k))
         (tl roots)).

Lemma residue_decr p p' : (p <= p')%nat -> residue p' <= residue p.
Proof.
 intros H. apply Rlistsum_le.
 intros z Hz. unfold Rdiv.
 apply Rmult_le_compat_r.
 { apply Rlt_le, Rinv_0_lt_compat. rewrite <- Rminus_lt_0.
   apply pow_lt_1_compat; try lia. split. apply Cmod_ge_0.
   now apply low_secondary_roots. }
 apply Rmult_le_compat_l. apply Cmod_ge_0.
 apply Rle_pow_le1; trivial. generalize (low_secondary_roots z Hz). lra.
Qed.

Lemma residue_pos p : 0 < residue p.
Proof.
  rewrite <- (Rlistsum_0 (tl roots)).
  apply Rlistsum_lt. apply tl_roots_nonnil.
  intros z Hz. unfold Rdiv.
  repeat apply Rmult_lt_0_compat.
  - now apply coefdA_pos.
  - apply pow_lt. now apply low_secondary_roots.
  - apply Rinv_0_lt_compat. rewrite <- Rminus_lt_0.
    apply pow_lt_1_compat; try lia. split. apply Cmod_ge_0.
    now apply low_secondary_roots.
Qed.

Lemma diff_rank_bound n r :
  rank k n = Some r -> Rabs (diff k n) < residue r.
Proof.
 intros Hr.
 unfold diff.
 rewrite <- Cmod_R, Equation_delta' with (roots:=roots) by (trivial; lia).
 eapply Rle_lt_trans; [apply Clistsum_mod|rewrite map_map].
 apply Rlistsum_lt;[apply tl_roots_nonnil|].
 intros z Hz.
 rewrite Cmod_mult. unfold Rdiv. rewrite Rmult_assoc.
 apply Rmult_lt_compat_l. now apply coefdA_pos.
 eapply Rle_lt_trans; [apply Clistsum_mod|rewrite map_map].
 erewrite map_ext by apply Cmod_pow.
 unfold rank in Hr.
 assert (D := decomp_delta k n).
 destruct (decomp k n) as [|r' l]; try easy. injection Hr as ->.
 apply sum_pow_cons; trivial; try lia. now apply low_secondary_roots.
Qed.

Lemma diff_residue0 n : Rabs (diff k n) < residue 0.
Proof.
 destruct (rank k n) as [r|] eqn:E.
 - apply Rlt_le_trans with (residue r). now apply diff_rank_bound.
   apply residue_decr. lia.
 - rewrite rank_none in E. subst n. unfold diff. simpl.
   replace (_-_) with 0 by lra. rewrite Rabs_pos_eq. apply residue_pos. lra.
Qed.

Lemma MaxDeltas_bounded p : MaxDeltas k p < residue 0.
Proof.
 destruct (MaxDeltas_reached k p lia) as (n & Hn & ->).
 eapply Rle_lt_trans; [apply Rle_abs|]. apply diff_residue0.
Qed.

Lemma MaxDeltas_has_finite_lim : ex_finite_lim_seq (MaxDeltas k).
Proof.
 eapply ex_finite_lim_seq_incr.
 - apply MaxDeltas_incr.
 - intros p. apply Rlt_le. apply MaxDeltas_bounded.
Qed.

Lemma sup_deltas_finite : Rbar.is_finite (sup_deltas k).
Proof.
 destruct MaxDeltas_has_finite_lim as (l & L).
 replace (sup_deltas k) with (Rbar.Finite l); try easy.
 symmetry; now apply is_lim_seq_unique.
Qed.

Definition sup_deltas' : R := Rbar.real (sup_deltas k).

Lemma MaxDeltas_lim' : is_lim_seq (MaxDeltas k) sup_deltas'.
Proof.
 unfold sup_deltas'. rewrite sup_deltas_finite. apply MaxDeltas_lim.
Qed.

Lemma MaxDeltas_below_lim' p : MaxDeltas k p <= sup_deltas'.
Proof.
 generalize (MaxDeltas_below_lim k p). now rewrite <- sup_deltas_finite.
Qed.

Lemma diff_le_sup' n : diff k n <= sup_deltas'.
Proof.
 generalize (diff_le_sup k n lia). now rewrite <- sup_deltas_finite.
Qed.

Lemma diff_sup' : Sup_seq (diff k) = sup_deltas'.
Proof.
 rewrite diff_sup by lia. symmetry. apply sup_deltas_finite.
Qed.

Lemma MaxDeltas_rest p n : diff k n < MaxDeltas k p + residue p.
Proof.
 rewrite <- (decomp_sum k n).
 assert (D := decomp_delta k n).
 assert (E := cut_app p (decomp k n)).
 assert (H1 := cut_fst p (decomp k n)).
 assert (H2 := cut_snd' p D).
 destruct (cut_lt_ge p (decomp k n)) as (l1,l2). simpl in *.
 rewrite <- E.
 rewrite diff_app; try lia. 2:{ now rewrite E. }
 apply Rplus_le_lt_compat.
 - apply MaxDeltas_spec; try lia. apply decomp_max'; trivial; try lia.
   rewrite <- E in D. apply Delta_app_inv in D. apply D.
 - destruct l2 as [|r l2].
   + unfold diff. simpl. replace (_-_) with 0 by lra. apply residue_pos.
   + apply Rlt_le_trans with (residue r).
     * eapply Rle_lt_trans;[apply Rle_abs|]. apply diff_rank_bound.
       unfold rank. rewrite decomp_sum'; trivial; try lia. rewrite <- E in D.
       apply Delta_app_inv in D. apply D.
     * apply residue_decr. apply H2. now left.
Qed.

Lemma sup_deltas_upper p :
 sup_deltas' <= MaxDeltas k p + residue p.
Proof.
 set (c := _+_).
 change (Rbar.Rbar_le sup_deltas' c).
 rewrite <- diff_sup'.
 replace (Rbar.Finite c) with (Sup_seq (fun _ => c)).
 2:{ apply is_sup_seq_unique, is_sup_seq_const. }
 apply Sup_seq_le. simpl. intros n. apply Rlt_le. apply MaxDeltas_rest.
Qed.

Lemma MinDeltas_bounded p : - residue 0 < MinDeltas k p.
Proof.
 destruct (MinDeltas_reached k p lia) as (n & Hn & ->).
 apply Ropp_lt_cancel; rewrite Ropp_involutive.
 eapply Rle_lt_trans; [apply Rcomplements.Rabs_maj2|]. apply diff_residue0.
Qed.

Lemma MinDeltas_has_finite_lim : ex_finite_lim_seq (MinDeltas k).
Proof.
 eapply ex_finite_lim_seq_decr.
 - apply MinDeltas_decr.
 - intros p. apply Rlt_le. apply MinDeltas_bounded.
Qed.

Lemma inf_deltas_finite : Rbar.is_finite (inf_deltas k).
Proof.
 destruct MinDeltas_has_finite_lim as (l & L).
 replace (inf_deltas k) with (Rbar.Finite l); try easy.
 symmetry; now apply is_lim_seq_unique.
Qed.

Definition inf_deltas' : R := Rbar.real (inf_deltas k).

Lemma MinDeltas_lim' : is_lim_seq (MinDeltas k) inf_deltas'.
Proof.
 unfold inf_deltas'. rewrite inf_deltas_finite. apply MinDeltas_lim.
Qed.

Lemma MinDeltas_above_lim' p : inf_deltas' <= MinDeltas k p.
Proof.
 generalize (MinDeltas_above_lim k p). now rewrite <- inf_deltas_finite.
Qed.

Lemma diff_ge_inf' n : inf_deltas' <= diff k n.
Proof.
 generalize (diff_ge_inf k n lia). now rewrite <- inf_deltas_finite.
Qed.

Lemma diff_inf' : Inf_seq (diff k) = inf_deltas'.
Proof.
 rewrite diff_inf by lia. symmetry. apply inf_deltas_finite.
Qed.

Lemma MinDeltas_rest p n : MinDeltas k p - residue p < diff k n.
Proof.
 rewrite <- (decomp_sum k n).
 assert (D := decomp_delta k n).
 assert (E := cut_app p (decomp k n)).
 assert (H1 := cut_fst p (decomp k n)).
 assert (H2 := cut_snd' p D).
 destruct (cut_lt_ge p (decomp k n)) as (l1,l2). simpl in *.
 rewrite <- E.
 rewrite diff_app; try lia. 2:{ now rewrite E. }
 apply Rplus_le_lt_compat.
 - apply MinDeltas_spec; try lia. apply decomp_max'; trivial; try lia.
   rewrite <- E in D. apply Delta_app_inv in D. apply D.
 - apply Ropp_lt_cancel. rewrite Ropp_involutive.
   destruct l2 as [|r l2].
   + unfold diff. simpl. replace (-_) with 0 by lra. apply residue_pos.
   + apply Rlt_le_trans with (residue r).
     * eapply Rle_lt_trans;[apply Rcomplements.Rabs_maj2|].
       apply diff_rank_bound.
       unfold rank. rewrite decomp_sum'; trivial; try lia. rewrite <- E in D.
       apply Delta_app_inv in D. apply D.
     * apply residue_decr. apply H2. now left.
Qed.

Lemma inf_deltas_lower p : MinDeltas k p - residue p <= inf_deltas'.
Proof.
 set (c := _-_).
 change (Rbar.Rbar_le c inf_deltas').
 rewrite <- diff_inf'.
 replace (Rbar.Finite c) with (Inf_seq (fun _ => c)).
 2:{ apply is_inf_seq_unique, is_inf_seq_const. }
 apply Inf_seq_le. simpl. intros n. apply Rlt_le. apply MinDeltas_rest.
Qed.

End LowSecondRoots.
