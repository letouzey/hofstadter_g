From Coq Require Import List Arith Lia Reals Lra.
Require Import MoreFun MoreList MoreReals MoreLim.
Require Import GenFib GenG Words Mu ThePoly.
Local Open Scope Z.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** Frequency of letter [0] in the infinite words [kseq].
    Consequences: [f k n / n] tends to [tau k],
    hence [f (k+1)] is eventually strictly above [f k]. *)

Lemma A_pos k n : 1 <= A k n.
Proof.
  apply (le_INR 1). apply A_nz.
Qed.

(** Via some matrix manipulations, we proved that the Fibonacci-like
   numbers [A k n] are a C linear combination [Σ α_i * r_i ^n] where
   the [r_i] are the (complex) roots of [X^(S k)-X^k-1].
   In particular, for k=1, this gives a variant of the Binet formula.
   The roots are (mu k) and k other roots of strictly lower modulus.
   Hence [A k n / mu k ^ n] has a finite limit, and this limit can be
   proved to be a real number. More details in [ThePoly.v] *)

Definition A_div_pow_mu_limit :
 forall k, exists lim:R, is_lim_seq (fun n => A k n / mu k ^n) lim.
Proof.
 intros k. exists (ThePoly.coef_mu k). apply ThePoly.A_div_pow_mu_limit.
Qed.

(* Let's now prove this limit to be >= 1
   TODO: now we could also prove it directly on the expression coef_mu *)

Lemma mu_ineq k n : (n <= k)%nat -> mu k ^ n * (mu k - 1) <= 1.
Proof.
 intros H.
 apply Rmult_le_reg_l with (mu k ^ (k-n)).
 { apply pow_lt. generalize (mu_itvl k). lra. }
 rewrite <- Rmult_assoc, <- pow_add.
 replace (k-n+n)%nat with k by lia.
 ring_simplify. rewrite Rmult_comm, tech_pow_Rmult, mu_carac.
 ring_simplify. apply pow_R1_Rle. generalize (mu_itvl k). lra.
Qed.

Lemma A_gt_mu_pow k n : mu k ^ n <= A k n.
Proof.
 induction n as [[|n] IH] using lt_wf_ind; simpl; try lra.
 destruct (Nat.le_gt_cases n k).
 - (* n <= k *)
   replace (n-k)%nat with O by lia. simpl.
   apply Rle_trans with (mu k ^ n + 1).
   + rewrite Rplus_comm; apply Rcomplements.Rle_minus_l.
     eapply Rle_trans; [|apply (mu_ineq k n H); trivial].
     ring_simplify. lra.
   + rewrite Nat.add_1_r, S_INR. generalize (IH n (Nat.le_refl _)). lra.
 - (* k < n *)
   change (mu k * mu k ^ n) with (mu k ^S n).
   replace (S n) with (n-k + S k)%nat by lia.
   rewrite pow_add, mu_carac, Rmult_plus_distr_l, Rmult_1_r, <- pow_add.
   replace (n-k+k)%nat with n by lia.
   rewrite plus_INR. apply Rplus_le_compat; apply IH; lia.
Qed.

Lemma A_div_pow_mu_gt1 :
 forall k, exists lim:R,
  1 <= lim /\ is_lim_seq (fun n => A k n / mu k ^n) lim.
Proof.
 intros k. destruct (A_div_pow_mu_limit k) as (lim,Hlim).
 exists lim; split; trivial.
 change (Rbar.Rbar_le 1 lim).
 apply is_lim_seq_le with (u:=fun _ => 1) (v:=fun n => A k n/mu k^n);
  trivial; try apply is_lim_seq_const.
 intros. apply Rcomplements.Rle_div_r.
 - apply pow_lt. generalize (mu_itvl k). lra.
 - rewrite Rmult_1_l. apply A_gt_mu_pow.
Qed.

(* Now let's prove that [A k (S n)/A k n] tends to [mu k] *)

Lemma A_ratio k : is_lim_seq (fun n => A k (S n) / A k n) (mu k).
Proof.
 destruct (A_div_pow_mu_gt1 k) as (lim & GT & Hlim).
 apply is_lim_seq_ext with
  (fun n => mu k * ((A k (S n) / mu k^(S n)) / (A k n / mu k^n))).
 { intros n. simpl pow. field; repeat split.
   - generalize (A_pos k n). lra.
   - generalize (pow_lt (mu k) n) (mu_itvl k). lra.
   - generalize (mu_itvl k). lra. }
 replace (mu k) with (mu k * (lim / lim)) at 1 by (field; lra).
 change (Rbar.Finite (mu k * (lim / lim))) with
  (Rbar.Rbar_mult (mu k) (lim/lim)).
 apply is_lim_seq_scal_l.
 apply is_lim_seq_div'; trivial; try lra.
 now apply is_lim_seq_incr_1 in Hlim.
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

Lemma A_ratio_k k p : is_lim_seq (fun n => A k (n+p)/A k n) (mu k^p).
Proof.
 apply (ratio_iter (A k)); try apply A_ratio.
 intros x. generalize (A_pos k x); lra.
Qed.

Lemma A_ratio_Sk k :
 is_lim_seq (fun n => A k (S n) / A k (n-k)) (mu k ^ S k).
Proof.
 apply is_lim_seq_incr_n with k.
 apply is_lim_seq_ext with (fun n => A k (n+S k)/A k n).
 intros. repeat f_equal; lia.
 apply A_ratio_k.
Qed.

Lemma A_ratio_inv k : is_lim_seq (fun n => A k n / A k (S n)) (tau k).
Proof.
 unfold tau.
 apply is_lim_seq_ext with (fun n => / (A k (S n) / A k n)).
 intros. field. generalize (A_pos k n); generalize (A_pos k (S n)); lra.
 change (Rbar.Finite (/ mu k)) with (Rbar.Rbar_inv (mu k)).
 apply is_lim_seq_inv. apply A_ratio.
 intros [= E]. destruct (mu_itvl k). lra.
Qed.

Lemma A_ratio_invSk k :
 is_lim_seq (fun n => A k (n-k) / A k (S n)) (tau k ^ S k).
Proof.
 unfold tau.
 apply is_lim_seq_ext with (fun n => / (A k (S n) / A k (n-k))).
 intros. field. generalize (A_pos k (S n)); generalize (A_pos k (n-k)); lra.
 rewrite pow_inv.
 change (Rbar.Finite (/ mu k ^ S k)) with (Rbar.Rbar_inv (mu k ^ S k)).
 apply is_lim_seq_inv. apply A_ratio_Sk.
 intros [= E].
 assert (0 < mu k ^S k).
 { apply pow_lt. generalize (mu_itvl k); lra. }
 simpl in *; rewrite E in *; lra.
Qed.

Lemma nbocc_all k l : (nbocc k l <= length l)%nat.
Proof.
 induction l; simpl; try lia. case Nat.eqb; lia.
Qed.

Lemma freq_kseq_0 k :
 k<>O -> is_lim_seq (fun n => count (kseq k) 0 n / n) (tau k ^ S k).
Proof.
 intros Hk.
 apply is_lim_seq_incr_1.
 assert (T : tau k = 1 - (tau k)^(S k)) by (generalize (tau_carac k); lra).
 set (lim := tau k ^ S k).
 assert (Hlim: 0 < lim < 1).
 { generalize (tau_itvl k). rewrite T. unfold lim. lra. }
 apply is_lim_seq_Reals. red. intros eps Heps.
 assert (L := A_ratio_invSk k).
 rewrite is_lim_seq_Reals in L. red in L. fold lim in L.
 assert (Heps' : eps/2 > 0) by lra. destruct (L _ Heps') as (G,HG). clear L.
 set (N := S (nat_part (2 * A k (k+S G) / eps))).
 exists N. intros n Hn.
 destruct (A_inv k n) as (p & Hp).
 rewrite (count_kseq k (S n) (S p)) by lia.
 set (w := firstn _ _).
 assert (Hw : length w = S n).
 { unfold w. rewrite firstn_length, kword_len. lia. }
 destruct (Saari_lemma4_ksubst k (S p) w (S G)) as (l & z & E & F & Hz);
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
   apply Rlistsum_le with (g := fun x => A k x * (eps/2)).
   intros a Ha.
   assert (Ha' : (S G <= a)%nat).
   { rewrite Forall_forall in F. now apply F. }
   assert (Ha2 : (G <= a-1)%nat) by lia.
   specialize (HG (a-1)%nat Ha2).
   rewrite kword_len. replace a with (S (a-1))%nat at 1 by lia.
   rewrite nbocc_0_kword; try lia.
   replace (S (a-1))%nat with a in HG by lia.
   assert (HAa := A_pos k a).
   assert (HAa' : 0 < / A k a). { apply Rinv_0_lt_compat; lra. }
   apply Rmult_le_reg_l with (/ A k a); trivial.
   rewrite <- (Rabs_right (/ A k a)) at 1; try lra.
   rewrite <- R_dist_mult_l.
   replace (/ A k a * (A k a * lim)) with lim by (field; lra).
   replace (/ A k a * (A k a * (eps /2))) with (eps / 2) by (field; lra).
   rewrite Rmult_comm.
   apply Rlt_le. apply HG.
   rewrite <- Hw, E, app_length, plus_INR, Rmult_plus_distr_r.
   rewrite flat_map_concat_map, length_concat, map_map.
   rewrite listsum_INR, Rlistsum_distr, !map_map.
   rewrite (map_ext (fun x => length _ * (eps/2))
                    (fun x => A k x * (eps/2))).
   2:{ intros a. now rewrite kword_len. }
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
   + apply Rle_lt_trans with (A k (k+S G)).
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

(** Consequence : [f k n / n] tends to [tau k] *)

Lemma Lim_fk_div_n_nz k : k<>O -> is_lim_seq (fun n => f k n / n) (tau k).
Proof.
 intros Hk.
 rewrite is_lim_seq_incr_1.
 apply is_lim_seq_ext with (u := fun n => 1 - count (kseq k) 0 (S n) / S n).
 { intros n.
   assert (0 < INR (S n)) by apply RSpos.
   replace 1 with (S n / S n) by (field; lra).
   rewrite <- (f_count_0 k (S n) Hk) at 1.
   rewrite plus_INR. lra. }
 assert (T : tau k = 1 - (tau k)^(S k)) by (generalize (tau_carac k); lra).
 rewrite T.
 apply is_lim_seq_minus'. apply is_lim_seq_const.
 generalize (freq_kseq_0 k Hk).
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

Lemma Lim_fk_div_n k : is_lim_seq (fun n => f k n / n) (tau k).
Proof.
 destruct (Nat.eq_dec k 0) as [->|Hk].
 - rewrite tau_0. apply Lim_f0_div_n.
 - now apply Lim_fk_div_n_nz.
Qed.

(** Consequence : [f (k+1)] is eventually strictly above [f k]. *)

Lemma fk_lt_fSk_eventually :
 forall k, exists N, forall n, (N<=n -> f k n < f (S k) n)%nat.
Proof.
 intros k.
 assert (H : is_lim_seq (fun n => f (S k) n / n - f k n / n)
                        (tau (S k) - tau k)).
 { apply is_lim_seq_minus'; apply Lim_fk_div_n. }
 rewrite is_lim_seq_Reals in H. red in H.
 set (eps := tau (S k) - tau k).
 assert (Heps : eps > 0).
 { unfold eps. generalize (tau_incr k). lra. }
 destruct (H eps Heps) as (N & HN). clear H. exists (S N).
 intros n Hn. apply INR_lt.
 assert (Hn' : (n >= N)%nat) by lia.
 specialize (HN n Hn'). apply Rdist_impl_pos in HN.
 apply Rmult_lt_reg_r with (/n); try lra.
 apply Rinv_0_lt_compat. apply (lt_INR 0). lia.
Qed.

(* Print Assumptions fk_lt_fSk_eventually. *)

(** Similarly, for [fs] *)

Lemma Lim_fkj_div_n k j : is_lim_seq (fun n => fs k j n / n) ((tau k)^j).
Proof.
 induction j.
 - simpl. rewrite is_lim_seq_incr_1.
   eapply is_lim_seq_ext, is_lim_seq_const.
   intros. change (1 = S n / S n). field. generalize (RSpos n); lra.
 - rewrite is_lim_seq_incr_1. simpl "^".
   apply is_lim_seq_ext with
    (fun n => (f k (S n) / S n)*(fs k j (f k (S n)) / f k (S n))).
   + intros. rewrite iter_S. field. split.
     * generalize (RSpos n); lra.
     * apply not_0_INR. generalize (@f_nonzero k (S n)); lia.
   + apply is_lim_seq_mult'.
     * assert (H := Lim_fk_div_n k). now rewrite is_lim_seq_incr_1 in H.
     * eapply (is_lim_seq_subseq (fun n => fs k j n / n)); trivial.
       intros P (N,HP). repeat red. exists (2*N)%nat. intros n Hn. apply HP.
       transitivity (f k (2*N)). apply f_double_le. apply f_mono; lia.
Qed.

Lemma fs_lt_fs_eventually k k' j j' : tau k ^j < tau k' ^j' ->
 exists N, forall n, (N<=n -> fs k j n < fs k' j' n)%nat.
Proof.
 intros LT.
 assert (H : is_lim_seq (fun n => fs k' j' n / n - fs k j n / n)
                        (tau k' ^j' - tau k ^j)).
 { apply is_lim_seq_minus'; apply Lim_fkj_div_n. }
 rewrite is_lim_seq_Reals in H. red in H.
 set (eps := tau k' ^j' - tau k ^j).
 assert (Heps : eps > 0) by (unfold eps; lra).
 destruct (H eps Heps) as (N & HN). clear H. exists (S N).
 intros n Hn. apply INR_lt.
 assert (Hn' : (n >= N)%nat) by lia.
 specialize (HN n Hn'). apply Rdist_impl_pos in HN.
 apply Rmult_lt_reg_r with (/n); try lra.
 apply Rinv_0_lt_compat. apply (lt_INR 0). lia.
Qed.
