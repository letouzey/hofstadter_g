From Coq Require Import List Arith Lia Reals Lra.
Require Import MoreFun MoreList MoreReals MoreLim.
Require Import GenFib GenG Words Mu ThePoly.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** Frequency of letter [0] in the infinite words [qseq].
    Consequences: [f q n / n] tends to [tau q],
    hence [f (q+1)] is eventually strictly above [f q]. *)

Lemma A_pos q n : 1 <= A q n.
Proof.
  apply (le_INR 1). apply A_nz.
Qed.

(** Via some matrix manipulations, we proved that the Fibonacci-like
   numbers [A q n] are a C linear combination [Σ α_i * r_i ^n] where
   the [r_i] are the (complex) roots of [X^(S q)-X^q-1].
   In particular, for q=1, this gives a variant of the Binet formula.
   The roots are (mu q) and q other roots of strictly lower modulus.
   Hence [A q n / mu q ^ n] has a finite limit, and this limit can be
   proved to be a real number. More details in [ThePoly.v] *)

Definition A_div_pow_mu_limit q :
 is_lim_seq (fun n => A q n / mu q ^n) (ThePoly.coef_mu q).
Proof.
 apply ThePoly.A_div_pow_mu_limit.
Qed.

(* Let's now prove this limit to be >= 1 *)

Lemma mu_ineq q n : (n <= q)%nat -> mu q ^ n * (mu q - 1) <= 1.
Proof.
 intros H.
 apply Rmult_le_reg_l with (mu q ^ (q-n)).
 { apply pow_lt. generalize (mu_itvl q). lra. }
 rewrite <- Rmult_assoc, <- pow_add.
 replace (q-n+n)%nat with q by lia.
 ring_simplify. rewrite Rmult_comm, tech_pow_Rmult, mu_carac.
 ring_simplify. apply pow_R1_Rle. generalize (mu_itvl q). lra.
Qed.

Lemma A_ge_mu_pow q n : mu q ^ n <= A q n.
Proof.
 induction n as [[|n] IH] using lt_wf_ind; simpl; try lra.
 destruct (Nat.le_gt_cases n q).
 - (* n <= q *)
   replace (n-q)%nat with O by lia. simpl.
   apply Rle_trans with (mu q ^ n + 1).
   + rewrite Rplus_comm; apply Rcomplements.Rle_minus_l.
     eapply Rle_trans; [|apply (mu_ineq q n H); trivial].
     ring_simplify. lra.
   + rewrite Nat.add_1_r, S_INR. generalize (IH n (Nat.le_refl _)). lra.
 - (* q < n *)
   change (mu q * mu q ^ n) with (mu q ^S n).
   replace (S n) with (n-q + S q)%nat by lia.
   rewrite pow_add, mu_carac, Rmult_plus_distr_l, Rmult_1_r, <- pow_add.
   replace (n-q+q)%nat with n by lia.
   rewrite plus_INR. apply Rplus_le_compat; apply IH; lia.
Qed.

Lemma coef_mu_ge1 q : 1 <= coef_mu q.
Proof.
 change (Rbar.Rbar_le 1 (coef_mu q)).
 apply is_lim_seq_le with (u:=fun _ => 1) (v:=fun n => A q n/mu q^n);
  try apply is_lim_seq_const; try apply A_div_pow_mu_limit.
 intros. apply Rcomplements.Rle_div_r.
 - apply pow_lt. generalize (mu_itvl q). lra.
 - rewrite Rmult_1_l. apply A_ge_mu_pow.
Qed.

(* Now let's prove that [A q (S n)/A q n] tends to [mu q] *)

Lemma A_ratio q : is_lim_seq (fun n => A q (S n) / A q n) (mu q).
Proof.
 apply is_lim_seq_ext with
  (fun n => mu q * ((A q (S n) / mu q^(S n)) / (A q n / mu q^n))).
 { intros n. simpl pow. field; repeat split.
   - generalize (A_pos q n). lra.
   - generalize (pow_lt (mu q) n) (mu_itvl q). lra.
   - generalize (mu_itvl q). lra. }
 set (lim := coef_mu q).
 assert (Hlim : lim <> 0). { unfold lim. generalize (coef_mu_ge1 q); lra. }
 replace (mu q) with (mu q * (lim / lim)) at 1 by now field.
 change (Rbar.Finite (mu q * (lim / lim))) with
  (Rbar.Rbar_mult (mu q) (lim/lim)).
 assert (H := A_div_pow_mu_limit q). fold lim in H.
 apply is_lim_seq_scal_l.
 apply is_lim_seq_div'; trivial. now apply is_lim_seq_incr_1 in H.
Qed.

Lemma ratio_iter f (r:R) :
  (forall x, 0 < f x) ->
  is_lim_seq (fun n => f (S n) / f n) r ->
  forall p, is_lim_seq (fun n => f (n+p)%nat / f n) (r^p).
Proof.
 intros Hf Hr.
 induction p.
 - rewrite pow_O.
   apply is_lim_seq_ext with (fun n => 1).
   + intros. rewrite Nat.add_0_r. field. generalize (Hf n); lra.
   + apply is_lim_seq_const.
 - simpl.
   apply is_lim_seq_ext with
       (fun n => (f (S (n + p)) / f (n + p)%nat) * (f (n + p)%nat / f n)).
   + intros. rewrite Nat.add_succ_r. field; split.
     generalize (Hf n); lra. generalize (Hf (n+p)%nat); lra.
   + apply is_lim_seq_mult'; trivial.
     apply (is_lim_seq_incr_n (fun n => f (S n)/f n) p); trivial.
Qed.

Lemma A_ratio_q q p : is_lim_seq (fun n => A q (n+p)/A q n) (mu q^p).
Proof.
 apply (ratio_iter (A q)); try apply A_ratio.
 intros x. generalize (A_pos q x); lra.
Qed.

Lemma A_ratio_Sq q :
 is_lim_seq (fun n => A q (S n) / A q (n-q)) (mu q ^ S q).
Proof.
 apply is_lim_seq_incr_n with q.
 apply is_lim_seq_ext with (fun n => A q (n+S q)/A q n).
 intros. repeat f_equal; lia.
 apply A_ratio_q.
Qed.

Lemma A_ratio_inv q : is_lim_seq (fun n => A q n / A q (S n)) (tau q).
Proof.
 unfold tau.
 apply is_lim_seq_ext with (fun n => / (A q (S n) / A q n)).
 intros. field. generalize (A_pos q n); generalize (A_pos q (S n)); lra.
 change (Rbar.Finite (/ mu q)) with (Rbar.Rbar_inv (mu q)).
 apply is_lim_seq_inv. apply A_ratio.
 intros [= E]. destruct (mu_itvl q). lra.
Qed.

Lemma A_ratio_invSq q :
 is_lim_seq (fun n => A q (n-q) / A q (S n)) (tau q ^ S q).
Proof.
 unfold tau.
 apply is_lim_seq_ext with (fun n => / (A q (S n) / A q (n-q))).
 intros. field. generalize (A_pos q (S n)); generalize (A_pos q (n-q)); lra.
 rewrite pow_inv.
 change (Rbar.Finite (/ mu q ^ S q)) with (Rbar.Rbar_inv (mu q ^ S q)).
 apply is_lim_seq_inv. apply A_ratio_Sq.
 intros [= E].
 assert (0 < mu q ^S q).
 { apply pow_lt. generalize (mu_itvl q); lra. }
 simpl in *; rewrite E in *; lra.
Qed.

Lemma nbocc_all q l : (nbocc q l <= length l)%nat.
Proof.
 induction l; simpl; try lia. case Nat.eqb; lia.
Qed.

Lemma freq_qseq_0 q :
 q<>O -> is_lim_seq (fun n => count (qseq q) 0 n / n) (tau q ^ S q).
Proof.
 intros Hq.
 apply is_lim_seq_incr_1.
 assert (T : tau q = 1 - (tau q)^(S q)) by (generalize (tau_carac q); lra).
 set (lim := tau q ^ S q).
 assert (Hlim: 0 < lim < 1).
 { generalize (tau_itvl q). rewrite T. unfold lim. lra. }
 apply is_lim_seq_Reals. red. intros eps Heps.
 assert (L := A_ratio_invSq q).
 rewrite is_lim_seq_Reals in L. red in L. fold lim in L.
 assert (Heps' : eps/2 > 0) by lra. destruct (L _ Heps') as (G,HG). clear L.
 set (N := S (nat_part (2 * A q (q+S G) / eps))).
 exists N. intros n Hn.
 destruct (A_inv q n) as (p & Hp).
 rewrite (count_qseq q (S n) (S p)) by lia.
 set (w := firstn _ _).
 assert (Hw : length w = S n).
 { unfold w. rewrite firstn_length, qword_len. lia. }
 destruct (Saari_lemma4_qsubst q (S p) w (S G)) as (l & z & E & F & Hz);
  try lia.
 unfold w. apply firstn_Prefix.
 assert (0 < S n) by (apply (lt_INR 0); lia).
 apply Rmult_lt_reg_l with (S n); trivial.
 rewrite <- (Rabs_right (S n)) at 1 by lra.
 rewrite <- R_dist_mult_l.
 unfold Rdiv. rewrite <- Rmult_assoc, Rinv_r_simpl_m by lra.
 rewrite E, flat_map_concat_map.
 rewrite nbocc_app, nbocc_concat, map_map. rewrite plus_INR.
 rewrite <- Hw, E, app_length at 1. rewrite plus_INR, Rmult_plus_distr_r.
 rewrite flat_map_concat_map, length_concat, map_map.
 eapply Rle_lt_trans. apply R_dist_plus.
 replace eps with (eps/2 + eps/2) by field.
 rewrite Rmult_plus_distr_l.
 apply Rplus_le_lt_compat.
 - rewrite !listsum_INR, Rlistsum_distr, !map_map.
   eapply Rle_trans. apply Rdist_listsum. simpl R_dist.
   eapply Rle_trans.
   apply Rlistsum_le with (g := fun x => A q x * (eps/2)).
   intros a Ha.
   assert (Ha' : (S G <= a)%nat).
   { rewrite Forall_forall in F. now apply F. }
   assert (Ha2 : (G <= a-1)%nat) by lia.
   specialize (HG (a-1)%nat Ha2).
   rewrite qword_len. replace a with (S (a-1))%nat at 1 by lia.
   rewrite nbocc_0_qword; try lia.
   replace (S (a-1))%nat with a in HG by lia.
   assert (HAa := A_pos q a).
   assert (HAa' : 0 < / A q a). { apply Rinv_0_lt_compat; lra. }
   apply Rmult_le_reg_l with (/ A q a); trivial.
   rewrite <- (Rabs_right (/ A q a)) at 1; try lra.
   rewrite <- R_dist_mult_l.
   replace (/ A q a * (A q a * lim)) with lim by (field; lra).
   replace (/ A q a * (A q a * (eps /2))) with (eps / 2) by (field; lra).
   rewrite Rmult_comm.
   apply Rlt_le. apply HG.
   rewrite <- Hw, E, app_length, plus_INR, Rmult_plus_distr_r.
   rewrite flat_map_concat_map, length_concat, map_map.
   rewrite listsum_INR, Rlistsum_distr, !map_map.
   rewrite (map_ext (fun x => length _ * (eps/2))
                    (fun x => A q x * (eps/2))).
   2:{ intros a. now rewrite qword_len. }
   assert (0 <= length z * (eps/2)); try lra.
   apply Rmult_le_pos. apply pos_INR. lra.
 - apply Rle_lt_trans with (length z).
   + eapply Rle_trans. eapply Rdist_pos_pos.
     apply (le_INR 0); lia.
     apply Rmult_le_pos; try lra. apply (le_INR 0); lia.
     apply Rmax_lub. apply le_INR, nbocc_all.
     assert (Hz' := pos_INR (length z)).
     rewrite <- (Rmult_1_r (length z)) at 2.
     apply Rmult_le_compat_l; lra.
   + apply Rle_lt_trans with (A q (q+S G)).
     now apply le_INR.
     apply Rmult_lt_reg_l with (2/eps).
     apply Rmult_lt_0_compat; try lra.
     apply Rinv_0_lt_compat; lra. field_simplify; try lra.
     apply Rle_lt_trans with N. 2:apply lt_INR; lia.
     unfold N. set (x := _ / _). rewrite S_INR.
     apply nat_part_INR. unfold x.
     apply Rmult_le_pos.
     change 2 with (INR 2). rewrite <- mult_INR. apply pos_INR.
     generalize (Rinv_0_lt_compat eps); lra.
Qed.

(** Consequence : [f q n / n] tends to [tau q] *)

Lemma Lim_fq_div_n_nz q : q<>O -> is_lim_seq (fun n => f q n / n) (tau q).
Proof.
 intros Hq.
 rewrite is_lim_seq_incr_1.
 apply is_lim_seq_ext with (u := fun n => 1 - count (qseq q) 0 (S n) / S n).
 { intros n.
   assert (0 < INR (S n)) by apply RSpos.
   replace 1 with (S n / S n) by (field; lra).
   rewrite <- (f_count_0 q (S n) Hq) at 1.
   rewrite plus_INR. lra. }
 assert (T : tau q = 1 - (tau q)^(S q)) by (generalize (tau_carac q); lra).
 rewrite T.
 apply is_lim_seq_minus'. apply is_lim_seq_const.
 generalize (freq_qseq_0 q Hq).
 now rewrite is_lim_seq_incr_1.
Qed.

Lemma Lim_f0_div_n : is_lim_seq (fun n => f 0 n / n) (1/2).
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_le_le with (u := fun n => 1/2)
                             (w := fun n => (1+/(S n))/2).
 - intros. set (n' := S n).
   rewrite f_0_div2.
   assert (0 < INR n') by apply RSpos.
   split; apply Rmult_le_reg_l with (2 * INR n'); trivial;
    field_simplify; try lra;
     change 2 with (INR 2); rewrite <- mult_INR;
     try (change 1 with (INR 1); rewrite <- plus_INR); apply le_INR;
     generalize (Nat.div2_odd (S n')); rewrite Nat.div2_div;
     destruct Nat.odd; simpl Nat.b2n; intros Hn; lia.
 - apply is_lim_seq_const.
 - replace (1/2) with ((1+0)*(/2)) by lra.
   change (Rbar.Finite ((1+0)*(/2))) with (Rbar.Rbar_mult (1+0) (/2)).
   apply is_lim_seq_scal_r.
   apply is_lim_seq_plus'. apply is_lim_seq_const.
   change (Rbar.Finite 0) with (Rbar.Rbar_inv Rbar.p_infty).
   apply is_lim_seq_inv; try easy.
   rewrite <- is_lim_seq_incr_1. apply is_lim_seq_INR.
Qed.

Lemma Lim_fq_div_n q : is_lim_seq (fun n => f q n / n) (tau q).
Proof.
 destruct (Nat.eq_dec q 0) as [->|Hq].
 - rewrite tau_0. apply Lim_f0_div_n.
 - now apply Lim_fq_div_n_nz.
Qed.

(** Consequence : [f (q+1)] is eventually strictly above [f q]. *)

Lemma fq_lt_fSq_eventually :
 forall q, exists N, forall n, (N<=n -> f q n < f (S q) n)%nat.
Proof.
 intros q.
 assert (H : is_lim_seq (fun n => f (S q) n / n - f q n / n)
                        (tau (S q) - tau q)).
 { apply is_lim_seq_minus'; apply Lim_fq_div_n. }
 rewrite is_lim_seq_Reals in H. red in H.
 set (eps := tau (S q) - tau q).
 assert (Heps : eps > 0).
 { unfold eps. generalize (tau_incr q). lra. }
 destruct (H eps Heps) as (N & HN). clear H. exists (S N).
 intros n Hn. apply INR_lt.
 assert (Hn' : (n >= N)%nat) by lia.
 specialize (HN n Hn'). apply Rdist_impl_pos in HN.
 apply Rmult_lt_reg_r with (/n); try lra.
 apply Rinv_0_lt_compat. apply (lt_INR 0). lia.
Qed.

(* Print Assumptions fq_lt_fSq_eventually. *)

(** Similarly, for [fs] *)

Lemma Lim_fqj_div_n q j : is_lim_seq (fun n => fs q j n / n) ((tau q)^j).
Proof.
 induction j.
 - simpl. rewrite is_lim_seq_incr_1.
   eapply is_lim_seq_ext, is_lim_seq_const.
   intros. change (1 = S n / S n). field. generalize (RSpos n); lra.
 - rewrite is_lim_seq_incr_1. simpl "^".
   apply is_lim_seq_ext with
    (fun n => (f q (S n) / S n)*(fs q j (f q (S n)) / f q (S n))).
   + intros. rewrite iter_S. field. split.
     * generalize (RSpos n); lra.
     * apply not_0_INR. generalize (@f_nonzero q (S n)); lia.
   + apply is_lim_seq_mult'.
     * assert (H := Lim_fq_div_n q). now rewrite is_lim_seq_incr_1 in H.
     * eapply (is_lim_seq_subseq (fun n => fs q j n / n)); trivial.
       intros P (N,HP). repeat red. exists (2*N)%nat. intros n Hn. apply HP.
       transitivity (f q (2*N)). apply f_double_le. apply f_mono; lia.
Qed.

Lemma fs_lt_fs_eventually q q' j j' : tau q ^j < tau q' ^j' ->
 exists N, forall n, (N<=n -> fs q j n < fs q' j' n)%nat.
Proof.
 intros LT.
 assert (H : is_lim_seq (fun n => fs q' j' n / n - fs q j n / n)
                        (tau q' ^j' - tau q ^j)).
 { apply is_lim_seq_minus'; apply Lim_fqj_div_n. }
 rewrite is_lim_seq_Reals in H. red in H.
 set (eps := tau q' ^j' - tau q ^j).
 assert (Heps : eps > 0) by (unfold eps; lra).
 destruct (H eps Heps) as (N & HN). clear H. exists (S N).
 intros n Hn. apply INR_lt.
 assert (Hn' : (n >= N)%nat) by lia.
 specialize (HN n Hn'). apply Rdist_impl_pos in HN.
 apply Rmult_lt_reg_r with (/n); try lra.
 apply Rinv_0_lt_compat. apply (lt_INR 0). lia.
Qed.

(** When parameter q is at least 5, [limsup |f q n - tau q *n| = +infinity].
    It is sufficient to consider numbers [n] of the form [A q m].
    The two following proofs currently rely on an axiom stating that
    the largest secondary root has modulus > 1 when q>=5.
    We do have a paper proof of this axiom, based on the value of the
    minimal Pisot number. To investigate someday in Coq, but probably
    quite non-trivial.

    Note that [limsup |f 4 n - tau 4 * n| = +infinity] as well.
    The proof is different (and without axiom !), see LimCase4.v
*)

Lemma dA_limsup_qgen q : (5<=q)%nat ->
 is_sup_seq (fun n => Rabs (A q (n-1) - tau q * A q n)) Rbar.p_infty.
Proof.
 intros Q M. simpl.
 destruct (SortedRoots_exists q) as (roots & roots_ok).
 assert (LT := axiom_large_second_best_root q roots Q roots_ok).
 destruct (dA_expo q roots ltac:(lia) roots_ok) as (c & Hc).
 set (r := QuantumLib.Complex.Cmod _) in *.
 destruct (large_enough_exponent r (M/c)) as (N, HN); trivial.
 destruct (Hc N) as (n & Hn & LT').
 exists n. eapply Rlt_trans; [|apply LT'].
 rewrite Rmult_comm, <- Rcomplements.Rlt_div_l.
 2:{ destruct c; simpl; lra. }
 eapply Rlt_le_trans; [apply HN|]. apply Rle_pow; trivial; lra.
Qed.

Lemma delta_limsup_qgen q : (5<=q)%nat ->
 is_sup_seq (fun n => Rabs (f q n - tau q * n)) Rbar.p_infty.
Proof.
 intros Q M. destruct (dA_limsup_qgen q Q M) as (n & Hn). simpl in *.
 exists (A q n). now rewrite f_A.
Qed.

(* Print Assumptions delta_limsup_qgen.
   (* Uses: axiom_large_second_best_root *)
*)
