From Coq Require Import Lia Reals Lra.
From Coquelicot Require Export Lim_seq.
Require Import MoreReals.

Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** Complements to Coquelicot.Lim_seq *)

Lemma is_lim_seq_0_abs u v :
 (forall n, Rabs (u n) <= v n) -> is_lim_seq v 0 -> is_lim_seq u 0.
Proof.
 intros H Hv.
 apply is_lim_seq_le_le with (u := fun n => -v n) (w := v); trivial.
 - intros n. now apply Rcomplements.Rabs_le_between.
 - rewrite is_lim_seq_opp in Hv. simpl in Hv.
   replace (-0) with 0 in Hv by lra. trivial.
Qed.

Lemma is_lim_seq_bound u K :
 (forall n, Rabs (u n) <= K) -> is_lim_seq (fun n => u n / n) 0.
Proof.
 intros H.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_0_abs with (fun n => K / S n).
 - intros n. specialize (H (S n)). unfold Rdiv.
   rewrite Rabs_mult, Rabs_inv by apply RSnz.
   rewrite (Rabs_right (S n)) by (generalize (RSpos n); lra).
   apply Rmult_le_compat_r; trivial.
   rewrite <- (Rmult_1_l (/ _)). apply Rle_mult_inv_pos, RSpos; try lra.
 - apply (is_lim_seq_div _ _ K Rbar.p_infty); try easy.
   + apply is_lim_seq_const.
   + rewrite <- is_lim_seq_incr_1. apply is_lim_seq_INR.
   + red. red. simpl. now rewrite Rmult_0_r.
Qed.

Lemma is_lim_seq_sqrt : is_lim_seq (fun n : nat => sqrt n) Rbar.p_infty.
Proof.
 apply is_lim_seq_p_infty_Reals.
 intros x.
 exists ((2+nat_part x)^2)%nat.
 intros n Hn.
 destruct (Rle_or_lt 0 x) as [Hx|Hx].
 2:{ generalize (sqrt_pos n); lra. }
 rewrite <- (sqrt_Rsqr x Hx).
 apply sqrt_lt_1_alt. rewrite Rsqr_pow2. split. nra.
 apply le_INR in Hn. rewrite pow_INR, plus_INR in Hn.
 change (INR 2) with 2 in Hn.
 eapply Rlt_le_trans; eauto. apply pow_lt_compat_l; try lia.
 split; trivial. generalize (nat_part_INR x Hx). nra.
Qed.
