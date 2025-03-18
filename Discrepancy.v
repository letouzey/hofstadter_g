From Coq Require Import Arith NArith Lia QArith Reals Lra Qreals.
From Hofstadter.HalfQuantum Require Import Complex.
Require Import MoreFun MoreList MoreReals MoreLim MoreComplex MoreSum.
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
    For the unbounded discrepancies, see Freq.v and LimCase4.v.

    Naming convention:
    q is the recursion depth -1 in the definition of functions f
      (i.e. k-1 where k is used in the articles)
    p is used to enumerate the A numbers
    n is for succesive points (typically here, [n < A q p])
*)

Definition diff q n := f q n - tau q * n.

Fixpoint AllDeltas (q p:nat) :=
 match p with
 | 0 => [0]
 | S p => AllDeltas q p ++ map (Rplus (diff q (A q p))) (AllDeltas q (p-q))
 end.

Fixpoint MaxDeltas (q p:nat) :=
 match p with
 | 0 => 0
 | S p => Rmax (MaxDeltas q p) (MaxDeltas q (p-q) + diff q (A q p))
 end.

Fixpoint MinDeltas (q p:nat) :=
 match p with
 | 0 => 0
 | S p => Rmin (MinDeltas q p) (MinDeltas q (p-q) + diff q (A q p))
 end.

(** Basic properties about diff *)

Lemma diff_app q l l' : Delta (S q) (l++l') ->
 diff q (sumA q (l++l')) = diff q (sumA q l) + diff q (sumA q l').
Proof.
 intros D.
 assert (D' := D). apply Delta_app_inv in D'. destruct D' as (D1 & D2 & _).
 unfold diff. rewrite !f_sumA by trivial.
 rewrite map_app, !sumA_app, !plus_INR. lra.
Qed.

Lemma diff_app_singl q l p : Delta (S q) (l++[p]) ->
 diff q (sumA q (l++[p])) = diff q (sumA q l) + diff q (A q p).
Proof.
 intros D. rewrite diff_app; trivial. f_equal; f_equal. simpl. lia.
Qed.

Lemma diff_add q n p : (n < A q (p-q))%nat ->
  diff q (n + A q p) = diff q n + diff q (A q p).
Proof.
 intros Hn.
 assert (E : decomp q (n+A q p) = decomp q n++[p]).
 { now apply decomp_plus_A. }
 rewrite <- (decomp_sum q (n+A q p)), E.
 rewrite diff_app_singl, decomp_sum; trivial.
 rewrite <- E. apply decomp_delta.
Qed.

(** Properties of AllDeltas *)

Lemma AllDeltas_len q p : length (AllDeltas q p) = A q p.
Proof.
 induction p as [[|p] IH] using lt_wf_ind; try easy.
 simpl. rewrite app_length, map_length. f_equal; apply IH; lia.
Qed.

Lemma AllDeltas_spec q p n :
  (n < A q p)%nat -> nth n (AllDeltas q p) 0 = diff q n.
Proof.
 revert n.
 induction p as [[|p] IH] using lt_wf_ind.
 - intros n Hn. unfold diff. simpl in *. replace n with O by lia. simpl. lra.
 - intros n Hn. simpl in *.
   destruct (Nat.ltb_spec n (A q p)).
   + rewrite app_nth1.
     2:{ now rewrite AllDeltas_len. }
     apply IH; trivial; lia.
   + rewrite app_nth2.
     2:{ now rewrite AllDeltas_len. }
     rewrite nth_map_indep with (d':=0).
     2:{ rewrite !AllDeltas_len. simpl in Hn. lia. }
     rewrite AllDeltas_len. simpl in Hn.
     rewrite IH; trivial; try lia. clear IH.
     replace n with ((n-A q p)+A q p)%nat at 2 by lia.
     rewrite diff_add. lra. lia.
Qed.

Lemma AllDeltas_spec' q p x :
  In x (AllDeltas q p) <-> exists n, (n < A q p)%nat /\ diff q n = x.
Proof.
 split.
 - intros IN. destruct (In_nth _ _ 0 IN) as (n & Hn & E).
   rewrite AllDeltas_len in Hn.
   exists n. split; trivial. now rewrite AllDeltas_spec in E.
 - intros (n & Hn & <-).
   rewrite <- (AllDeltas_spec q p n) by trivial.
   apply nth_In. now rewrite AllDeltas_len.
Qed.

(** Properties of MaxDeltas *)

Lemma MaxDeltas_spec q p n : (n < A q p)%nat -> diff q n <= MaxDeltas q p.
Proof.
 intros Hn. rewrite <- (AllDeltas_spec q p n Hn).
 revert n Hn.
 induction p as [[|p] IH] using lt_wf_ind.
 - intros n Hn. simpl in *. replace n with O by lia. lra.
 - intros n Hn. simpl in *.
   destruct (Nat.ltb_spec n (A q p)).
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

Lemma MaxDeltas_reached q p :
  exists n, (n < A q p)%nat /\ MaxDeltas q p = diff q n.
Proof.
 induction p as [[|p] IH] using lt_wf_ind.
 - exists 0%nat. split; simpl. lia. unfold diff; simpl; lra.
 - simpl.
   destruct (IH p lia) as (n1 & Hn1 & E1).
   destruct (IH (p-q)%nat lia) as (n2 & Hn2 & E2).
   destruct (Rle_lt_dec (diff q n2 + diff q (A q p)) (diff q n1)).
   + exists n1. split. lia. rewrite E1, E2, Rmax_left; lra.
   + exists (n2+A q p)%nat. split. lia. rewrite E1, E2, Rmax_right by lra.
     symmetry. now apply diff_add.
Qed.

Lemma MaxDeltas_incr q p : MaxDeltas q p <= MaxDeltas q (S p).
Proof.
 apply Rmax_l.
Qed.

Lemma MaxDeltas_mono q p p' :
  (p <= p')%nat -> MaxDeltas q p <= MaxDeltas q p'.
Proof.
 induction 1. lra. eapply Rle_trans; [apply IHle|]. apply MaxDeltas_incr.
Qed.

Lemma MaxDeltas_pos q p : 0 <= MaxDeltas q p.
Proof.
 apply (MaxDeltas_mono q 0). lia.
Qed.

Lemma MaxDeltas_has_lim q : ex_lim_seq (MaxDeltas q).
Proof.
 eapply ex_lim_seq_incr. apply MaxDeltas_incr.
Qed.

Definition sup_deltas q : Rbar.Rbar := Lim_seq (MaxDeltas q).

(** This sup_deltas will be finite exactly when q <= 3 (i.e. k <= 4) *)

Lemma MaxDeltas_lim q : is_lim_seq (MaxDeltas q) (sup_deltas q).
Proof.
 apply Lim_seq_correct. apply MaxDeltas_has_lim.
Qed.

Lemma MaxDeltas_below_lim q p : Rbar.Rbar_le (MaxDeltas q p) (sup_deltas q).
Proof.
 unfold sup_deltas.
 rewrite <- (Lim_seq_const (MaxDeltas q p)).
 apply Lim_seq_le_loc.
 exists p. apply MaxDeltas_mono.
Qed.

Lemma diff_le_sup q n : Rbar.Rbar_le (diff q n) (sup_deltas q).
Proof.
 destruct (invA_spec q n) as (_,LT).
 set (p := (S (invA q n))) in *.
 apply Rbar.Rbar_le_trans with (MaxDeltas q p).
 + apply MaxDeltas_spec. lia.
 + apply MaxDeltas_below_lim.
Qed.

Lemma diff_sup q : Sup_seq (diff q) = sup_deltas q.
Proof.
 apply is_sup_seq_unique. red.
 destruct sup_deltas as [l| | ] eqn:E.
 - intros eps. split.
   + intros n. simpl.
     apply Rle_lt_trans with l. 2:{ destruct eps. simpl. lra. }
     generalize (diff_le_sup q n). now rewrite E.
   + assert (L := MaxDeltas_lim q). rewrite E in L.
     apply is_lim_seq_spec in L.
     destruct (L eps) as (N & HN).
     specialize (HN N lia).
     destruct (MaxDeltas_reached q N) as (n & _ & E').
     exists n. simpl. rewrite <- E'.
     apply Rcomplements.Rabs_lt_between in HN. lra.
 - intros M.
   assert (L := MaxDeltas_lim q). rewrite E in L.
   apply is_lim_seq_spec in L.
   destruct (L M) as (N & HN). specialize (HN N lia).
   destruct (MaxDeltas_reached q N) as (n & _ & E').
   exists n. simpl. now rewrite <- E'.
 - generalize (MaxDeltas_below_lim q 0). rewrite E. simpl. easy.
Qed.

(** Properties of MinDeltas *)

Lemma MinDeltas_spec q p n : (n < A q p)%nat -> MinDeltas q p <= diff q n.
Proof.
 intros Hn. rewrite <- (AllDeltas_spec q p n Hn).
 revert n Hn.
 induction p as [[|p] IH] using lt_wf_ind.
 - intros n Hn. simpl in *. replace n with O by lia. lra.
 - intros n Hn. simpl in *.
   destruct (Nat.ltb_spec n (A q p)).
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

Lemma MinDeltas_reached q p :
  exists n, (n < A q p)%nat /\ MinDeltas q p = diff q n.
Proof.
 induction p as [[|p] IH] using lt_wf_ind.
 - exists 0%nat. split; simpl. lia. unfold diff; simpl; lra.
 - simpl.
   destruct (IH p lia) as (n1 & Hn1 & E1).
   destruct (IH (p-q)%nat lia) as (n2 & Hn2 & E2).
   destruct (Rle_lt_dec (diff q n1) (diff q n2 + diff q (A q p))).
   + exists n1. split. lia. rewrite E1, E2, Rmin_left; lra.
   + exists (n2+A q p)%nat. split. lia. rewrite E1, E2, Rmin_right by lra.
     symmetry. now apply diff_add.
Qed.

Lemma MinDeltas_decr q p : MinDeltas q (S p) <= MinDeltas q p.
Proof.
 simpl. apply Rmin_l.
Qed.

Lemma MinDeltas_mono q p p' :
  (p <= p')%nat -> MinDeltas q p' <= MinDeltas q p.
Proof.
 induction 1. lra. eapply Rle_trans; [|apply IHle]. apply MinDeltas_decr.
Qed.

Lemma MinDeltas_neg q p : MinDeltas q p <= 0.
Proof.
 apply (MinDeltas_mono q 0). lia.
Qed.

Lemma MinDeltas_has_lim q : ex_lim_seq (MinDeltas q).
Proof.
 eapply ex_lim_seq_decr. apply MinDeltas_decr.
Qed.

Definition inf_deltas q : Rbar.Rbar := Lim_seq (MinDeltas q).

(** This limit is finite exactly when q <= 3 (i.e. k <= 4) *)

Lemma MinDeltas_lim q : is_lim_seq (MinDeltas q) (inf_deltas q).
Proof.
 apply Lim_seq_correct. apply MinDeltas_has_lim.
Qed.

Lemma MinDeltas_above_lim q p : Rbar.Rbar_le (inf_deltas q) (MinDeltas q p).
Proof.
 unfold inf_deltas.
 rewrite <- (Lim_seq_const (MinDeltas q p)).
 apply Lim_seq_le_loc.
 exists p. apply MinDeltas_mono.
Qed.

Lemma diff_ge_inf q n : Rbar.Rbar_le (inf_deltas q) (diff q n).
Proof.
 destruct (invA_spec q n) as (_,LT).
 set (p := (S (invA q n))) in *.
 apply Rbar.Rbar_le_trans with (MinDeltas q p).
 + apply MinDeltas_above_lim.
 + apply MinDeltas_spec. lia.
Qed.

Lemma diff_inf q : Inf_seq (diff q) = (inf_deltas q).
Proof.
 apply is_inf_seq_unique. red.
 destruct inf_deltas as [l| | ] eqn:E.
 - intros eps. split.
   + intros n. simpl.
     apply Rlt_le_trans with l. { destruct eps. simpl. lra. }
     generalize (diff_ge_inf q n). now rewrite E.
   + assert (L := MinDeltas_lim q). rewrite E in L.
     apply is_lim_seq_spec in L.
     destruct (L eps) as (N & HN).
     specialize (HN N lia).
     destruct (MinDeltas_reached q N) as (n & _ & E').
     exists n. simpl. rewrite <- E'.
     apply Rcomplements.Rabs_lt_between in HN. lra.
 - generalize (MinDeltas_above_lim q 0). rewrite E. simpl. easy.
 - intros M.
   assert (L := MinDeltas_lim q). rewrite E in L.
   apply is_lim_seq_spec in L.
   destruct (L M) as (N & HN). specialize (HN N lia).
   destruct (MinDeltas_reached q N) as (n & _ & E').
   exists n. simpl. now rewrite <- E'.
Qed.

(** Generic proof that the discrepancies are bounded when
    the secondary roots of ThePoly are of modulus < 1. *)

Section LowSecondRoots.
Variable q : nat.
Hypothesis Hq : q <> O.
Variable roots : list C.
Hypothesis roots_ok : SortedRoots q roots.
Hypothesis LowSecond : Cmod (roots@1) < 1.

Lemma tl_roots_nonnil : tl roots <> [].
Proof.
 apply SortedRoots_length in roots_ok.
 destruct roots; simpl in *; try easy.
 contradict Hq; subst; simpl in *; lia.
Qed.

Lemma coefdA_pos z : In z (tl roots) -> 0 < Cmod (coefdA q z).
Proof.
 intros Hz.
 apply Cmod_gt_0, coefdA_nz.
 - apply (SortedRoots_roots q roots roots_ok).
   destruct roots; simpl in *; tauto.
 - rewrite <- (SortedRoots_mu q roots roots_ok). intros ->.
   apply SortedRoots_nodup in roots_ok.
   destruct roots; unfold Cnth in *; simpl in *; try easy.
   now inversion_clear roots_ok.
Qed.

Lemma low_secondary_roots z : In z (tl roots) -> 0 < Cmod z < 1.
Proof.
 intros Hz. split.
 - apply Cmod_gt_0. intros ->.
   apply (root_nz q). apply (SortedRoots_roots q _ roots_ok).
   destruct roots; simpl in *; tauto.
 - apply (SortedRoots_Cmod_sorted q) in roots_ok.
   rewrite StronglySorted_nth in roots_ok.
   destruct (In_nth _ _ 0%C Hz) as (p & Hp & E).
   destruct roots as [|mu rt]; try easy. simpl in *.
   destruct p as [|p]. rewrite <- E; apply LowSecond.
   specialize (roots_ok 1%nat (S (S p)) lia).
   unfold Cnth in *; simpl in *. rewrite E in *. lra.
Qed.

Definition residue p :=
  Rlistsum
    (map (fun z => Cmod (coefdA q z) * Cmod z^p / (1 - Cmod z^(S q)))
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
  rank q n = Some r -> Rabs (diff q n) < residue r.
Proof.
 intros Hr.
 unfold diff.
 rewrite <- Cmod_R, Equation_delta' with (roots:=roots) by trivial.
 eapply Rle_lt_trans; [apply Clistsum_mod|rewrite map_map].
 apply Rlistsum_lt;[apply tl_roots_nonnil|].
 intros z Hz.
 rewrite Cmod_mult. unfold Rdiv. rewrite Rmult_assoc.
 apply Rmult_lt_compat_l. now apply coefdA_pos.
 eapply Rle_lt_trans; [apply Clistsum_mod|rewrite map_map].
 erewrite map_ext by apply Cmod_pow.
 unfold rank in Hr.
 assert (D := decomp_delta q n).
 destruct (decomp q n) as [|r' l]; try easy. injection Hr as ->.
 apply sum_pow_cons; trivial. now apply low_secondary_roots.
Qed.

Lemma diff_residue0 n : Rabs (diff q n) < residue 0.
Proof.
 destruct (rank q n) as [r|] eqn:E.
 - apply Rlt_le_trans with (residue r). now apply diff_rank_bound.
   apply residue_decr. lia.
 - rewrite rank_none in E. subst n. unfold diff. simpl.
   replace (_-_) with 0 by lra. rewrite Rabs_pos_eq. apply residue_pos. lra.
Qed.

Lemma MaxDeltas_bounded p : MaxDeltas q p < residue 0.
Proof.
 destruct (MaxDeltas_reached q p) as (n & Hn & ->).
 eapply Rle_lt_trans; [apply Rle_abs|]. apply diff_residue0.
Qed.

Lemma MaxDeltas_has_finite_lim : ex_finite_lim_seq (MaxDeltas q).
Proof.
 eapply ex_finite_lim_seq_incr.
 - apply MaxDeltas_incr.
 - intros p. apply Rlt_le. apply MaxDeltas_bounded.
Qed.

Lemma sup_deltas_finite : Rbar.is_finite (sup_deltas q).
Proof.
 destruct MaxDeltas_has_finite_lim as (l & L).
 replace (sup_deltas q) with (Rbar.Finite l); try easy.
 symmetry; now apply is_lim_seq_unique.
Qed.

Definition sup_deltas' : R := Rbar.real (sup_deltas q).

Lemma MaxDeltas_lim' : is_lim_seq (MaxDeltas q) sup_deltas'.
Proof.
 unfold sup_deltas'. rewrite sup_deltas_finite. apply MaxDeltas_lim.
Qed.

Lemma MaxDeltas_below_lim' p : MaxDeltas q p <= sup_deltas'.
Proof.
 generalize (MaxDeltas_below_lim q p). now rewrite <- sup_deltas_finite.
Qed.

Lemma diff_le_sup' n : diff q n <= sup_deltas'.
Proof.
 generalize (diff_le_sup q n). now rewrite <- sup_deltas_finite.
Qed.

Lemma diff_sup' : Sup_seq (diff q) = sup_deltas'.
Proof.
 rewrite diff_sup. symmetry. apply sup_deltas_finite.
Qed.

Lemma MaxDeltas_rest p n : diff q n < MaxDeltas q p + residue p.
Proof.
 rewrite <- (decomp_sum q n).
 assert (D := decomp_delta q n).
 assert (E := cut_app p (decomp q n)).
 assert (H1 := cut_fst p (decomp q n)).
 assert (H2 := cut_snd' p D).
 destruct (cut_lt_ge p (decomp q n)) as (l1,l2). simpl in *.
 rewrite <- E.
 rewrite diff_app. 2:{ now rewrite E. }
 apply Rplus_le_lt_compat.
 - apply MaxDeltas_spec. apply decomp_max'; trivial.
   rewrite <- E in D. apply Delta_app_inv in D. apply D.
 - destruct l2 as [|r l2].
   + unfold diff. simpl. replace (_-_) with 0 by lra. apply residue_pos.
   + apply Rlt_le_trans with (residue r).
     * eapply Rle_lt_trans;[apply Rle_abs|]. apply diff_rank_bound.
       unfold rank. rewrite decomp_sum'; trivial. rewrite <- E in D.
       apply Delta_app_inv in D. apply D.
     * apply residue_decr. apply H2. now left.
Qed.

Lemma sup_deltas_upper p :
 sup_deltas' <= MaxDeltas q p + residue p.
Proof.
 set (c := _+_).
 change (Rbar.Rbar_le sup_deltas' c).
 rewrite <- diff_sup'.
 replace (Rbar.Finite c) with (Sup_seq (fun _ => c)).
 2:{ apply is_sup_seq_unique, is_sup_seq_const. }
 apply Sup_seq_le. simpl. intros n. apply Rlt_le. apply MaxDeltas_rest.
Qed.

Lemma MinDeltas_bounded p : - residue 0 < MinDeltas q p.
Proof.
 destruct (MinDeltas_reached q p) as (n & Hn & ->).
 apply Ropp_lt_cancel; rewrite Ropp_involutive.
 eapply Rle_lt_trans; [apply Rcomplements.Rabs_maj2|]. apply diff_residue0.
Qed.

Lemma MinDeltas_has_finite_lim : ex_finite_lim_seq (MinDeltas q).
Proof.
 eapply ex_finite_lim_seq_decr.
 - apply MinDeltas_decr.
 - intros p. apply Rlt_le. apply MinDeltas_bounded.
Qed.

Lemma inf_deltas_finite : Rbar.is_finite (inf_deltas q).
Proof.
 destruct MinDeltas_has_finite_lim as (l & L).
 replace (inf_deltas q) with (Rbar.Finite l); try easy.
 symmetry; now apply is_lim_seq_unique.
Qed.

Definition inf_deltas' : R := Rbar.real (inf_deltas q).

Lemma MinDeltas_lim' : is_lim_seq (MinDeltas q) inf_deltas'.
Proof.
 unfold inf_deltas'. rewrite inf_deltas_finite. apply MinDeltas_lim.
Qed.

Lemma MinDeltas_above_lim' p : inf_deltas' <= MinDeltas q p.
Proof.
 generalize (MinDeltas_above_lim q p). now rewrite <- inf_deltas_finite.
Qed.

Lemma diff_ge_inf' n : inf_deltas' <= diff q n.
Proof.
 generalize (diff_ge_inf q n). now rewrite <- inf_deltas_finite.
Qed.

Lemma diff_inf' : Inf_seq (diff q) = inf_deltas'.
Proof.
 rewrite diff_inf. symmetry. apply inf_deltas_finite.
Qed.

Lemma MinDeltas_rest p n : MinDeltas q p - residue p < diff q n.
Proof.
 rewrite <- (decomp_sum q n).
 assert (D := decomp_delta q n).
 assert (E := cut_app p (decomp q n)).
 assert (H1 := cut_fst p (decomp q n)).
 assert (H2 := cut_snd' p D).
 destruct (cut_lt_ge p (decomp q n)) as (l1,l2). simpl in *.
 rewrite <- E.
 rewrite diff_app. 2:{ now rewrite E. }
 apply Rplus_le_lt_compat.
 - apply MinDeltas_spec. apply decomp_max'; trivial.
   rewrite <- E in D. apply Delta_app_inv in D. apply D.
 - apply Ropp_lt_cancel. rewrite Ropp_involutive.
   destruct l2 as [|r l2].
   + unfold diff. simpl. replace (-_) with 0 by lra. apply residue_pos.
   + apply Rlt_le_trans with (residue r).
     * eapply Rle_lt_trans;[apply Rcomplements.Rabs_maj2|].
       apply diff_rank_bound.
       unfold rank. rewrite decomp_sum'; trivial. rewrite <- E in D.
       apply Delta_app_inv in D. apply D.
     * apply residue_decr. apply H2. now left.
Qed.

Lemma inf_deltas_lower p : MinDeltas q p - residue p <= inf_deltas'.
Proof.
 set (c := _-_).
 change (Rbar.Rbar_le c inf_deltas').
 rewrite <- diff_inf'.
 replace (Rbar.Finite c) with (Inf_seq (fun _ => c)).
 2:{ apply is_inf_seq_unique, is_inf_seq_const. }
 apply Inf_seq_le. simpl. intros n. apply Rlt_le. apply MinDeltas_rest.
Qed.

End LowSecondRoots.
