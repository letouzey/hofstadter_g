From Coq Require Import Lia Reals Lra.
From Coquelicot Require Export Lim_seq.
Require Import MoreReals.
Import Rbar.

Local Open Scope R.
Local Coercion INR : nat >-> R.

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
 - apply (is_lim_seq_div _ _ K p_infty); try easy.
   + apply is_lim_seq_const.
   + rewrite <- is_lim_seq_incr_1. apply is_lim_seq_INR.
   + red. red. simpl. now rewrite Rmult_0_r.
Qed.

Lemma is_lim_seq_invn : is_lim_seq (fun n => /n) 0.
Proof.
 apply is_lim_seq_ext with (fun n => 1/n).
 - intros n. unfold Rdiv. apply Rmult_1_l.
 - apply is_lim_seq_bound with (K:=1). intros. rewrite Rabs_pos_eq; lra.
Qed.

Lemma is_lim_seq_ndivSn :
 is_lim_seq (fun n => n / S n) 1.
Proof.
 replace 1 with (1-0) by lra.
 apply is_lim_seq_ext with (fun n => 1-/(S n)).
 - intros n. rewrite S_INR. field. rewrite <- S_INR.
   generalize (lt_0_INR (S n) ltac:(lia)). lra.
 - apply is_lim_seq_minus'; try apply is_lim_seq_const.
   assert (H := is_lim_seq_invn).
   now apply is_lim_seq_incr_1 in H.
Qed.

Lemma is_lim_seq_sqrt : is_lim_seq (fun n : nat => sqrt n) p_infty.
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

(** sup and limsup *)

Lemma LimSup_seq_correct (u : nat -> R) : is_LimSup_seq u (LimSup_seq u).
Proof.
 destruct (ex_LimSup_seq u) as (l, Hl).
 now rewrite (is_LimSup_seq_unique _ _ Hl).
Qed.

Lemma Lim_LimSup (u : nat -> R) :
  ex_lim_seq u -> Lim_seq u = LimSup_seq u.
Proof.
 intros H. apply ex_lim_LimSup_LimInf_seq in H.
 unfold Lim_seq. rewrite <- H.
 destruct (LimSup_seq u); simpl; trivial. f_equal. lra.
Qed.

Lemma Lim_LimInf (u : nat -> R) :
  ex_lim_seq u -> Lim_seq u = LimInf_seq u.
Proof.
 intros H. apply ex_lim_LimSup_LimInf_seq in H.
 unfold Lim_seq. rewrite -> H.
 destruct (LimInf_seq u); simpl; trivial. f_equal. lra.
Qed.

Lemma finite_max (u:nat->R) N : exists M, forall n, (n<=N)%nat -> u n <= M.
Proof.
 induction N.
 - exists (u O). intros n Hn. inversion Hn. lra.
 - destruct IHN as (M & HM).
   exists (Rmax M (u (S N))).
   intros n Hn. inversion Hn.
   + subst; apply Rmax_r.
   + apply Rle_trans with M; [|apply Rmax_l]. now apply HM.
Qed.

(** A sequence u of values in R (not Rbar !) cannot have -infinity
    as sup. *)

Lemma sup_no_minfty (u:nat -> R) : Sup_seq u <> m_infty.
Proof.
 intro E.
 assert (Hu := Sup_seq_correct u). rewrite E in Hu. simpl in *.
 specialize (Hu (u O) O). lra.
Qed.

(** For a sequence u of values in R (not Rbar  !),
    having +infinity as sup is the same as having +infinity as limsup *)

Lemma Sup_LimSup_pinfty (u:nat -> R) :
 Sup_seq u = p_infty <-> LimSup_seq u = p_infty.
Proof.
 split.
 - intros Hu. apply is_LimSup_seq_unique.
   assert (Hu' := Sup_seq_correct u). rewrite Hu in Hu'. simpl in *.
   intros M N.
   destruct (finite_max u (N-1)) as (M' & HM').
   destruct (Hu' (Rmax M (M'+1))) as (n & Hn). exists n. split.
   + destruct (Nat.le_gt_cases N n); trivial. exfalso.
     specialize (HM' n ltac:(lia)). generalize (Rmax_r M (M'+1)). lra.
   + eapply Rle_lt_trans; [ apply Rmax_l | apply Hn ].
 - intros Hu. apply is_sup_seq_unique.
   assert (Hu' := LimSup_seq_correct u). rewrite Hu in Hu'. simpl in *.
   intros M. destruct (Hu' M O) as (n & _ & H). now exists n.
Qed.

Lemma fekete_subadditive_lemma (u:nat->R) :
 (forall n m, u (n+m)%nat <= u n + u m) ->
 LimSup_seq (fun n => u n / n) = LimInf_seq (fun n => u n / n).
Proof.
 intros U.
 apply Rbar_le_antisym; try apply LimSup_LimInf_seq_le.
 set (f := fun n => u n / n).
 assert (U' : forall a b c, u (a*b+c)%nat <= a * u b + u c).
 { induction a; intros.
   - simpl. lra.
   - replace (S a * b + c)%nat with (b + (a*b+c))%nat by lia.
     eapply Rle_trans. apply U.
     rewrite S_INR, (Rplus_comm a 1), Rmult_plus_distr_r, Rmult_1_l.
     rewrite Rplus_assoc. apply Rplus_le_compat_l. apply IHa. }
 assert (H : forall q, q<>O -> Rbar.Rbar_le (LimSup_seq f) (u q / q)).
 { intros q Q.
   destruct (finite_max u (q-1)) as (M & HM).
   assert (LE : forall n, n<>O ->
                u n / n <= (n-(n mod q))/n * (u q / q) + M/n).
   { intros n Hn.
     assert (Hn' : 0 < /n).
     { apply Rinv_0_lt_compat. destruct n; try lia. apply RSpos. }
     rewrite (Nat.div_mod_eq n q) at 1. rewrite (Nat.mul_comm q).
     eapply Rle_trans;
       [eapply Rmult_le_compat_r;[now apply Rlt_le|apply U']| ].
     rewrite Rmult_plus_distr_r. apply Rplus_le_compat.
     - apply Req_le.
       rewrite <- minus_INR by (apply Nat.mod_le; lia).
       replace (n-n mod q)%nat with (((n/q)*q)%nat).
       2:{ rewrite (Nat.div_mod_eq n q) at 2. lia. }
       rewrite mult_INR. field. split; now apply not_0_INR.
     - apply Rmult_le_compat_r;[now apply Rlt_le| ].
       apply HM. generalize (Nat.mod_upper_bound n q); lia. }
     replace (Finite (u q/q)) with
         (LimSup_seq (fun n => (n- n mod q)/n * (u q / q) + M / n)).
     { apply LimSup_le. exists 1%nat. intros n Hn. apply LE; lia. }
     { apply is_LimSup_seq_unique, is_lim_LimSup_seq.
       rewrite <- (Rplus_0_r (u q / q)) at 1.
       apply is_lim_seq_plus'.
       2:{ apply is_lim_seq_bound with (Rabs M); intros; lra. }
       rewrite <- (Rmult_1_l (u q / q)) at 1.
       apply is_lim_seq_mult'; try apply is_lim_seq_const.

       apply is_lim_seq_ext_loc with (u := fun n => 1 - (n mod q)/n).
       { exists 1%nat. intros n Hn. field. apply not_0_INR; lia. }
       replace 1 with (1-0) at 1 by lra.
       apply is_lim_seq_minus'; try apply is_lim_seq_const.
       apply is_lim_seq_bound with q; intros.
       rewrite Rabs_right by (apply Rle_ge; apply pos_INR).
       apply le_INR. generalize (Nat.mod_upper_bound n q); lia. }}
 destruct (LimSup_seq f) eqn:E.
 - replace (Finite r) with (LimInf_seq (fun n => r)).
   2:{ apply is_LimInf_seq_unique, is_LimInf_seq_const. }
   apply LimInf_le. exists 1%nat. intros n Hn. apply H. lia.
 - simpl in H. now destruct (H 1%nat).
 - simpl; trivial.
Qed.

(*
Lemma fekete_superadditive_lemma (u:nat->R) :
 (forall n m, u (n+m)%nat >= u n + u m) ->
 LimSup_seq (fun n => u n / n) = LimInf_seq (fun n => u n / n).
Proof.
*)
