From Coq Require Import Lia Reals Lra.
From Coquelicot Require Complex.
From Coquelicot Require Export Lim_seq.
From Coquelicot Require Import Hierarchy Continuity Series PSeries.
From QuantumLib Require Import Complex Polynomial.
Import Continuity.
Require Import MoreList MoreReals MoreComplex MoreSum.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

Ltac fixeq ty := change (@eq _) with (@eq ty).
Notation lia := (ltac:(lia)) (only parsing).

Notation R_NM := R_NormedModule.
Notation R_CNM := R_CompleteNormedModule.
Notation C_NM := Coquelicot.Complex.C_R_NormedModule.
Notation C_CNM := Coquelicot.Complex.C_R_CompleteNormedModule.

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
   generalize (lt_0_INR (S n) lia). lra.
 - apply is_lim_seq_minus'; try apply is_lim_seq_const.
   assert (H := is_lim_seq_invn).
   now apply is_lim_seq_incr_1 in H.
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

(** sup and limsup *)

Lemma is_sup_seq_const (c : Rbar.Rbar) : is_sup_seq (fun _ => c) c.
Proof.
 destruct c; red.
 - intros eps. split.
   + intros _; simpl. destruct eps. simpl. lra.
   + exists O. simpl. destruct eps. simpl. lra.
 - intros M; now exists O.
 - now intros M.
Qed.

Lemma is_inf_seq_const (c : Rbar.Rbar) : is_inf_seq (fun _ => c) c.
Proof.
 destruct c; red.
 - intros eps. split.
   + intros _; simpl. destruct eps. simpl. lra.
   + exists O. simpl. destruct eps. simpl. lra.
 - now intros M.
 - intros M; now exists O.
Qed.

Lemma LimSup_seq_correct (u : nat -> R) : is_LimSup_seq u (LimSup_seq u).
Proof.
 destruct (ex_LimSup_seq u) as (l, Hl).
 now rewrite (is_LimSup_seq_unique _ _ Hl).
Qed.

Lemma LimInf_seq_correct (u : nat -> R) : is_LimInf_seq u (LimInf_seq u).
Proof.
 destruct (ex_LimInf_seq u) as (l, Hl).
 now rewrite (is_LimInf_seq_unique _ _ Hl).
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

Lemma sup_no_minfty (u:nat -> R) : Sup_seq u <> Rbar.m_infty.
Proof.
 intro E.
 assert (Hu := Sup_seq_correct u). rewrite E in Hu. simpl in *.
 specialize (Hu (u O) O). lra.
Qed.

Lemma inf_no_pinfty (u:nat -> R) : Inf_seq u <> Rbar.p_infty.
Proof.
 intro E.
 assert (Hu := Inf_seq_correct u). rewrite E in Hu. simpl in *.
 specialize (Hu (u O) O). lra.
Qed.

(** For a sequence u of values in R (not Rbar  !),
    having +infinity as sup is the same as having +infinity as limsup *)

Lemma Sup_LimSup_pinfty (u:nat -> R) :
 Sup_seq u = Rbar.p_infty <-> LimSup_seq u = Rbar.p_infty.
Proof.
 split.
 - intros Hu. apply is_LimSup_seq_unique.
   assert (Hu' := Sup_seq_correct u). rewrite Hu in Hu'. simpl in *.
   intros M N.
   destruct (finite_max u (N-1)) as (M' & HM').
   destruct (Hu' (Rmax M (M'+1))) as (n & Hn). exists n. split.
   + destruct (Nat.le_gt_cases N n); trivial. exfalso.
     specialize (HM' n lia). generalize (Rmax_r M (M'+1)). lra.
   + eapply Rle_lt_trans; [ apply Rmax_l | apply Hn ].
 - intros Hu. apply is_sup_seq_unique.
   assert (Hu' := LimSup_seq_correct u). rewrite Hu in Hu'. simpl in *.
   intros M. destruct (Hu' M O) as (n & _ & H). now exists n.
Qed.

Lemma is_inf_seq_minor (u : nat -> Rbar.Rbar) (l : Rbar.Rbar) :
  is_inf_seq u l -> forall n, Rbar.Rbar_le l (u n).
Proof.
 intros Hu n.
 rewrite <- is_sup_opp_inf_seq in Hu.
 apply is_sup_seq_major with (n:=n) in Hu.
 now apply Rbar.Rbar_opp_le.
Qed.

Lemma Inf_seq_major_le (u : nat -> Rbar.Rbar) (M : R) (n : nat) :
  Rbar.Rbar_le (u n) M -> Rbar.Rbar_le (Inf_seq u) M.
Proof.
 intros. apply Rbar.Rbar_le_trans with (u n); trivial.
 apply is_inf_seq_minor. apply Inf_seq_correct.
Qed.

Lemma LimSup_le_Sup (u:nat->R) : Rbar.Rbar_le (LimSup_seq u) (Sup_seq u).
Proof.
 destruct (Sup_seq u) as [r | | ] eqn:E.
 - rewrite LimSup_InfSup_seq.
   eapply Inf_seq_major_le with (n:=O).
   rewrite Sup_seq_ext with (v:=u). 2:{ intros n. do 2 f_equal. lia. }
   rewrite E. apply Rbar.Rbar_le_refl.
 - now destruct (LimSup_seq u).
 - now destruct (sup_no_minfty u).
Qed.

Lemma Inf_le_LimInf (u:nat->R) : Rbar.Rbar_le (Inf_seq u) (LimInf_seq u).
Proof.
 destruct (Inf_seq u) as [r | | ] eqn:E; try constructor.
 - rewrite LimInf_SupInf_seq.
   eapply Sup_seq_minor_le with (n:=O).
   rewrite Inf_seq_ext with (v:=u). 2:{ intros n. do 2 f_equal. lia. }
   rewrite E. apply Rbar.Rbar_le_refl.
 - now destruct (inf_no_pinfty u).
Qed.

Lemma Fekete_core (u:nat->R) :
 (forall n m, u (n+m)%nat <= u n + u m) ->
 forall q, q<>O -> Rbar.Rbar_le (LimSup_seq (fun n => u n / n)) (u q / q).
Proof.
 intros U q Q.
 assert (U' : forall a b c, u (a*b+c)%nat <= a * u b + u c).
 { induction a; intros.
   - simpl. lra.
   - replace (S a * b + c)%nat with (b + (a*b+c))%nat by lia.
     eapply Rle_trans. apply U.
     rewrite S_INR, (Rplus_comm a 1), Rmult_plus_distr_r, Rmult_1_l.
     rewrite Rplus_assoc. apply Rplus_le_compat_l. apply IHa. }
 destruct (finite_max u (q-1)) as (M & HM).
 replace (Rbar.Finite (u q/q)) with
     (LimSup_seq (fun n => (n- n mod q)/n * (u q / q) + M / n)).
 { apply LimSup_le. exists 1%nat. intros n Hn.
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
     rewrite mult_INR. field. split; apply not_0_INR; lia.
   - apply Rmult_le_compat_r;[now apply Rlt_le| ].
     apply HM. generalize (Nat.mod_upper_bound n q); lia. }
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
   apply le_INR. generalize (Nat.mod_upper_bound n q); lia. }
Qed.

Lemma Fekete_subadditive_lemma (u:nat->R) :
 (forall n m, u (n+m)%nat <= u n + u m) ->
 let f := fun n => u n / n in
 is_lim_seq f (Inf_seq (fun n => f (S n))).
Proof.
 intros U f.
 assert (U' := Fekete_core u U). fold f in U'.
 assert (LE : Rbar.Rbar_le (LimSup_seq f) (Inf_seq (fun n => f (S n)))).
 { replace (LimSup_seq f) with (Inf_seq (fun n => LimSup_seq f)).
   2:{ apply is_inf_seq_unique, is_inf_seq_const. }
   apply Inf_seq_le. intros n. apply U'. lia. }
 assert (E : LimSup_seq f = LimInf_seq f).
 { apply Rbar.Rbar_le_antisym; try apply LimSup_LimInf_seq_le.
   destruct (LimSup_seq f) eqn:E.
   - replace (Rbar.Finite r) with (LimInf_seq (fun n => r)).
     2:{ apply is_LimInf_seq_unique, is_LimInf_seq_const. }
     apply LimInf_le. exists 1%nat. intros n Hn. apply U'. lia.
   - simpl in U'. now destruct (U' 1%nat).
   - simpl; trivial. }
 assert (LE' := Inf_le_LimInf (fun n => f (S n))). simpl in LE'.
 replace (LimInf_seq (fun x => f (S x))) with (LimInf_seq f) in LE'.
 2:{ symmetry. apply is_LimInf_seq_unique.
     rewrite <- is_LimInf_seq_ind_1. apply LimInf_seq_correct. }
 assert (X : ex_lim_seq f).
 { apply ex_lim_LimSup_LimInf_seq, E. }
 replace (Inf_seq (fun n => f (S n))) with (Lim_seq f).
 now apply Lim_seq_correct.
 apply Rbar.Rbar_le_antisym. now rewrite Lim_LimSup. now rewrite Lim_LimInf.
Qed.

Lemma Fekete_superadditive_lemma (u:nat->R) :
 (forall n m, u (n+m)%nat >= u n + u m) ->
 let f := fun n => u n / n in
 is_lim_seq f (Sup_seq (fun n => f (S n))).
Proof.
 intros U. cbn -[INR].
 rewrite is_lim_seq_opp.
 rewrite Sup_seq_ext with (v:=fun n => Rbar.Rbar_opp (- u(S n)/S n)).
 2:{ intros n. cbn -[INR]. f_equal. field. generalize (RSpos n); lra. }
 rewrite <- Inf_opp_sup.
 apply is_lim_seq_ext_loc with (u:=fun n => - u n/n).
 { exists 1%nat. intros n Hn. field. destruct n; try lia.
   generalize (RSpos n); lra. }
 apply Fekete_subadditive_lemma. intros n m. specialize (U n m). lra.
Qed.

(** More on R series *)

Lemma is_series_alt (a:nat->R) (l:R) :
 is_series a l <-> is_lim_seq (sum_n a) l.
Proof.
 reflexivity.
Qed.

Lemma ex_series_alt (a:nat->R) :
 ex_series a <-> ex_finite_lim_seq (sum_n a).
Proof.
 reflexivity.
Qed.

Lemma is_series_R0 : is_series (fun _ => 0%R) 0%R.
Proof.
 rewrite is_series_alt.
 apply is_lim_seq_ext with (fun _ => 0%R); try apply is_lim_seq_const.
 intros n. symmetry. apply (sum_n_zero (G:=R_AbelianMonoid)).
Qed.

Lemma ex_series_Rlistsum {A} (f : nat -> A -> R) (l : list A) :
 (forall x, In x l -> ex_series (fun n => f n x)) ->
 ex_series (fun n => Rlistsum (map (f n) l)).
Proof.
 induction l.
 - intros. simpl. exists 0%R.
   change (is_lim_seq (sum_n (fun _ => R0)) R0).
   apply is_lim_seq_ext with (u:=fun _ => R0); try apply is_lim_seq_const.
   intros n. symmetry. apply sum_n_R0; trivial.
 - intros Hf. simpl.
   apply (ex_series_plus (V:=R_NM)).
   + apply Hf. now left.
   + apply IHl. intros x Hx. apply Hf. now right.
Qed.

Lemma ex_series_bigsum (f : nat -> nat -> R) m :
 (forall i, (i < m)%nat -> ex_series (fun n => f n i)) ->
 ex_series (fun n => big_sum (f n) m).
Proof.
 induction m; intros Hf; simpl.
 - exists 0%R. apply is_series_R0.
 - apply (ex_series_plus (V:=R_NM)).
   + apply IHm. intros i Hi. apply Hf. lia.
   + apply Hf. lia.
Qed.

Lemma ex_series_le_eventually {K : AbsRing} {V : CompleteNormedModule K}
  (a : nat -> V) (b : nat -> R) :
  Hierarchy.eventually (fun n => norm (a n) <= b n) ->
  ex_series b -> ex_series a.
Proof.
 intros (N,H) (l,X).
 set (b' := fun n => if n <=? N then norm (a n) else b n).
 apply (ex_series_le (K:=K) (V:=V) _ b').
 { intros n. unfold b'. case Nat.leb_spec; try lra. intros. apply H. lia. }
 exists (l + (sum_n (norm∘a) N - sum_n b N))%R.
 change (is_lim_seq (sum_n b') (l + (sum_n (norm ∘ a) N - sum_n b N)))%R.
 rewrite is_lim_seq_incr_n with (N:=N).
 apply is_lim_seq_ext
   with (u := (fun n => sum_n b (n+N) + (sum_n (norm ∘ a) N - sum_n b N))%R).
 - unfold b'. clear.
   induction n.
   + simpl. ring_simplify. apply sum_n_ext_loc. intros n Hn.
     case Nat.leb_spec; lia || easy.
   + simpl. rewrite !sum_Sn. case Nat.leb_spec; try lia. intros.
     rewrite <- IHn. simpl. change plus with Rplus. ring.
 - apply is_lim_seq_plus'. now rewrite <- is_lim_seq_incr_n.
   apply is_lim_seq_const.
Qed.

Lemma ex_series_square (a : nat -> R) :
  ex_series (Rabs∘a) -> ex_series (fun n => a n^2)%R.
Proof.
 intros H.
 apply (ex_series_le_eventually (V:=R_CNM)) with (b := Rabs∘a); trivial.
 assert (H' := ex_series_lim_0 _ H).
 destruct (H' (Rgt 1)) as (N, HP).
 { exists (mkposreal 1 ltac:(lra)). simpl. intros y Y.
   apply Rcomplements.Rabs_lt_between in Y.
   change minus with Rminus in Y; lra. }
 exists N. intros n Hn. specialize (HP n Hn).
 change norm with Rabs. rewrite Rabs_right.
 2:{ rewrite <- Rsqr_pow2. apply Rle_ge, Rle_0_sqr. }
 rewrite <- Rsqr_pow2, Rsqr_abs. unfold compose, Rsqr in *.
 rewrite <- (Rmult_1_r (Rabs (a n))) at 3.
 apply Rmult_le_compat_l; try lra. apply Rabs_pos.
Qed.

Lemma Series_rest0 (a : nat -> R) (l : R) :
 is_series a l -> forall n, is_lim_seq (sum_n_m a (S n)) (l-sum_n a n)%R.
Proof.
 intros H n.
 apply (is_lim_seq_ext_loc (fun m => sum_n a m - sum_n a n)%R).
 - exists n. intros m Hm.
   symmetry. now apply (sum_n_m_sum_n (G:=R_AbelianGroup)).
 - apply is_lim_seq_minus'; trivial. apply is_lim_seq_const.
Qed.

Lemma Series_rest (a : nat -> R) :
 ex_series a ->
 forall n, (Series a - sum_n a n = Rbar.real (Lim_seq (sum_n_m a (S n))))%R.
Proof.
 intros (l,H) n.
 rewrite (is_series_unique a l H).
 apply Series_rest0 with (n:=n) in H. apply is_lim_seq_unique in H.
 now rewrite H.
Qed.


(** Limits of C sequences *)

Local Open Scope C.

Lemma C_ball (c c' : C) (eps : R) :
  Cmod (c-c') < eps -> ball c eps c'.
Proof.
 rewrite Cmod_switch. intros H.
 change (Rabs (Re (c' - c)) < eps /\ Rabs (Im (c' - c)) < eps).
 split; apply Rle_lt_trans with (Cmod (c'-c));
  auto using re_le_Cmod, im_le_Cmod.
Qed.

Lemma ball_C (c c' : C) (eps : R) :
  ball c eps c' -> Cmod (c-c') < eps * sqrt 2.
Proof.
 rewrite Cmod_switch. intros (H,H').
 change (Rabs (Re (c' - c)) < eps) in H.
 change (Rabs (Im (c' - c)) < eps) in H'.
 assert (0 <= eps) by (generalize (Rabs_pos (Re (c'-c))); lra).
 rewrite <- (Rabs_right eps) in H,H' by lra.
 apply Rsqr_lt_abs_1 in H, H'.
 apply Rsqr_incrst_0; try apply Cmod_ge_0.
 2:{ apply Rmult_le_pos; trivial; apply sqrt_pos. }
 rewrite Rsqr_mult, Rsqr_sqrt by lra. rewrite !Rsqr_pow2 in *.
 rewrite Cmod2_alt. lra.
Qed.

Definition is_lim_Cseq (f : nat -> C) (c : C) :=
 filterlim f Hierarchy.eventually (locally c).

Lemma is_lim_Cseq_proj (f : nat -> C) (c : C) :
 is_lim_Cseq f c <->
 is_lim_seq (Re ∘ f) (Re c) /\ is_lim_seq (Im ∘ f) (Im c).
Proof.
 split.
 - split.
   + intros P (eps, HP). simpl in HP.
     destruct (H (ball c eps)) as (N, HN); [now exists eps|].
     exists N. intros n Hn. now apply HP, HN.
   + intros P (eps, HP). simpl in HP.
     destruct (H (ball c eps)) as (N, HN); [now exists eps|].
     exists N. intros n Hn. now apply HP, HN.
 - intros (H1,H2) P (eps, HP). simpl in HP.
   destruct (H1 (ball (Re c) eps)) as (N1, HN1); [now exists eps|].
   destruct (H2 (ball (Im c) eps)) as (N2, HN2); [now exists eps|].
   exists (Nat.max N1 N2). intros n Hn. apply HP.
   split; [apply HN1|apply HN2]; lia.
Qed.

Definition ex_lim_Cseq (f : nat -> C) := exists c, is_lim_Cseq f c.

Definition Lim_Cseq (f : nat -> C) : C :=
  (Rbar.real (Lim_seq (Re ∘ f)), Rbar.real (Lim_seq (Im ∘ f))).

Lemma is_lim_Cseq_unique (f : nat -> C) (c : C) :
 is_lim_Cseq f c -> Lim_Cseq f = c.
Proof.
 rewrite is_lim_Cseq_proj. intros (H1,H2). unfold Lim_Cseq.
 apply is_lim_seq_unique in H1, H2. rewrite H1, H2. simpl. now destruct c.
Qed.

Lemma Lim_Cseq_correct (f : nat -> C) :
 ex_lim_Cseq f -> is_lim_Cseq f (Lim_Cseq f).
Proof.
 intros (c & H). now rewrite (is_lim_Cseq_unique _ _ H).
Qed.

Lemma is_lim_Cseq_0_Cmod (f : nat -> C) :
 is_lim_seq (Cmod ∘ f) 0%R -> is_lim_Cseq f 0.
Proof.
 intros H.
 apply is_lim_Cseq_proj. simpl.
 split; apply is_lim_seq_0_abs with (v := Cmod ∘ f); trivial;
 intros; apply re_le_Cmod || apply im_le_Cmod.
Qed.

Lemma is_lim_Cseq_Cmod (f : nat -> C) (l : C) :
 is_lim_Cseq f l -> is_lim_seq (Cmod ∘ f) (Cmod l).
Proof.
 intros H P (eps,HP). simpl in HP.
 assert (LT : 0 < /2 * eps).
 { apply Rmult_lt_0_compat. lra. apply eps. }
 set (eps' := mkposreal _ LT).
 destruct (H (ball l eps')) as (N, HN); [now exists eps'|].
 exists N. intros n Hn. apply HP.
 change (Rabs (Cmod (f n) - Cmod l) < eps).
 assert (Cmod (f n - l) < eps).
 { apply Rsqr_incrst_0; trivial using Cmod_ge_0.
   2:{ generalize (cond_pos eps); lra. }
   rewrite !Rsqr_pow2, Cmod2_alt.
   destruct (HN n Hn) as (H1,H2).
   change (Rabs (Re (f n - l)) < eps') in H1.
   change (Rabs (Im (f n - l)) < eps') in H2.
   rewrite <- (Rabs_right eps') in H1,H2 by (generalize (cond_pos eps'); lra).
   apply Rsqr_lt_abs_1 in H1,H2. rewrite !Rsqr_pow2 in H1,H2.
   change (pos eps') with (/2 * eps)%R in H1,H2. nra. }
 apply Rcomplements.Rabs_lt_between. split.
 - apply Ropp_lt_cancel. rewrite Ropp_involutive, Ropp_minus_distr.
   rewrite <- (Cmod_opp (f n)).
   apply Rle_lt_trans with (Cmod (l - f n)); [apply Cmod_triangle'|].
   now rewrite Cmod_switch.
 - rewrite <- (Cmod_opp l).
   apply Rle_lt_trans with (Cmod (f n - l)); [apply Cmod_triangle'|]. easy.
Qed.

Lemma is_lim_Cseq_ext (f g : nat -> C)(l : C) :
 (forall n, f n = g n) -> is_lim_Cseq f l -> is_lim_Cseq g l.
Proof.
 intros E. rewrite !is_lim_Cseq_proj. intros (Hf,Hg). split.
 - apply is_lim_seq_ext with (u:=Re∘f); trivial.
   intros n. unfold compose. now rewrite E.
 - apply is_lim_seq_ext with (u:=Im∘f); trivial.
   intros n. unfold compose. now rewrite E.
Qed.

Lemma is_lim_Cseq_Cmod' (a : nat -> C) (b : nat -> R) (la : C) (lb : R) :
  (forall n, Cmod (a n) <= b n) ->
  is_lim_Cseq a la -> is_lim_seq b lb -> Cmod la <= lb.
Proof.
 intros LE Ha Hb.
 assert (Ha' := is_lim_Cseq_Cmod a la Ha).
 now apply (is_lim_seq_le (Cmod∘a) b (Cmod la) lb).
Qed.

Lemma is_lim_Cseq_const (c:C) : is_lim_Cseq (fun _ => c) c.
Proof.
 rewrite is_lim_Cseq_proj. split.
 apply is_lim_seq_ext with (u:= fun _ => Re c). easy. apply is_lim_seq_const.
 apply is_lim_seq_ext with (u:= fun _ => Im c). easy. apply is_lim_seq_const.
Qed.

Lemma Lim_Cseq_const (c:C) : Lim_Cseq (fun _ => c) = c.
Proof.
 apply is_lim_Cseq_unique, is_lim_Cseq_const.
Qed.

Lemma is_lim_Cseq_plus (a b : nat -> C) (la lb : C) :
 is_lim_Cseq a la -> is_lim_Cseq b lb ->
 is_lim_Cseq (fun n => a n + b n) (la + lb).
Proof.
 rewrite !is_lim_Cseq_proj. intros (Ha1,Ha2) (Hb1,Hb2). split.
 - apply is_lim_seq_ext with (fun n => (Re ∘ a) n + (Re ∘ b) n)%R.
   + intros n. apply re_plus.
   + now apply is_lim_seq_plus'.
 - apply is_lim_seq_ext with (fun n => (Im ∘ a) n + (Im ∘ b) n)%R.
   + intros n. apply im_plus.
   + now apply is_lim_seq_plus'.
Qed.

Lemma Lim_Cseq_plus (a b : nat -> C) :
 ex_lim_Cseq a -> ex_lim_Cseq b ->
 Lim_Cseq (fun n => a n + b n) = Lim_Cseq a + Lim_Cseq b.
Proof.
 intros (la,Ha) (lb,Hb). apply is_lim_Cseq_unique.
 apply is_lim_Cseq_plus.
 - apply Lim_Cseq_correct. now exists la.
 - apply Lim_Cseq_correct. now exists lb.
Qed.

Lemma is_lim_Cseq_minus (a b : nat -> C) (la lb : C) :
 is_lim_Cseq a la -> is_lim_Cseq b lb ->
 is_lim_Cseq (fun n => a n - b n) (la - lb).
Proof.
 rewrite !is_lim_Cseq_proj. intros (Ha1,Ha2) (Hb1,Hb2). split.
 - apply is_lim_seq_ext with (fun n => (Re ∘ a) n - (Re ∘ b) n)%R.
   + intros n. unfold compose, Rminus. rewrite <- re_opp. apply re_plus.
   + now apply is_lim_seq_minus'.
 - apply is_lim_seq_ext with (fun n => (Im ∘ a) n - (Im ∘ b) n)%R.
   + intros n. unfold compose, Rminus. rewrite <- im_opp. apply im_plus.
   + now apply is_lim_seq_minus'.
Qed.

Lemma is_lim_Cseq_mult (a b : nat -> C) (la lb : C) :
 is_lim_Cseq a la -> is_lim_Cseq b lb ->
 is_lim_Cseq (fun n => a n * b n) (la * lb).
Proof.
 rewrite !is_lim_Cseq_proj. intros (Ha1,Ha2) (Hb1,Hb2). split.
 - apply is_lim_seq_ext with (fun n => (Re ∘ a) n * (Re ∘ b) n
                                     - (Im ∘ a) n * (Im ∘ b) n)%R.
   + intros n. apply re_mult.
   + apply is_lim_seq_plus'. now apply is_lim_seq_mult'.
     change (Rbar.Finite (- _)) with (Rbar.Rbar_opp (Im la * Im lb)%R).
     rewrite <- is_lim_seq_opp. now apply is_lim_seq_mult'.
 - apply is_lim_seq_ext with (fun n => (Re ∘ a) n * (Im ∘ b) n
                                     + (Im ∘ a) n * (Re ∘ b) n)%R.
   + intros n. apply im_mult.
   + apply is_lim_seq_plus'; now apply is_lim_seq_mult'.
Qed.

Lemma is_lim_Cseq_incr_n (u : nat -> C) (N : nat) l :
  is_lim_Cseq u l <-> is_lim_Cseq (fun n : nat => u (n + N)%nat) l.
Proof.
 rewrite !is_lim_Cseq_proj.
 rewrite (is_lim_seq_incr_n (Re∘_) N).
 rewrite (is_lim_seq_incr_n (Im∘_) N). easy.
Qed.

Lemma is_lim_Cseq_Clistsum (f : nat -> C -> C) (g : C -> C) l :
 (forall x, In x l -> is_lim_Cseq (fun n => f n x) (g x)) ->
 is_lim_Cseq (fun n => Clistsum (map (f n) l)) (Clistsum (map g l)).
Proof.
 induction l.
 - simpl. intros _. apply is_lim_Cseq_const.
 - intros H. simpl. apply is_lim_Cseq_plus. apply H; now left.
   apply IHl. intros x Hx. apply H; now right.
Qed.

Lemma is_lim_Cseq_bigsum (f : nat -> nat -> C) (lims : nat -> C) m :
 (forall i, (i < m)%nat -> is_lim_Cseq (fun n => f n i) (lims i)) ->
 is_lim_Cseq (fun n => big_sum (f n) m) (big_sum lims m).
Proof.
 induction m; intros Hf.
 - apply is_lim_Cseq_const.
 - simpl. apply is_lim_Cseq_plus.
   + apply IHm. intros i Hi. apply Hf. lia.
   + apply Hf. lia.
Qed.

(** Series on C *)

Lemma is_Cseries_alt (a : nat -> C) (l : C) :
 is_series a l <-> is_lim_Cseq (sum_n a) l.
Proof.
 reflexivity.
Qed.

Definition CSeries (a : nat -> C) : C := Lim_Cseq (sum_n a).

Lemma CSeries_unique (a : nat -> C) (l : C) :
  is_series a l -> CSeries a = l.
Proof.
 intros H. apply is_lim_Cseq_unique, is_lim_Cseq_proj. split.
 - red. eapply filterlim_comp with (f := sum_n a) (g:=Re); eauto.
   intros P (eps, H'). exists eps. intros c Hc. apply H', Hc.
 - red. eapply filterlim_comp with (f := sum_n a) (g:=Im); eauto.
   intros P (eps, H'). exists eps. intros c Hc. apply H', Hc.
Qed.

Lemma CSeries_correct (a : nat -> C) :
  ex_series a -> is_series a (CSeries a).
Proof.
 intros (l & H). simpl in l. now rewrite (CSeries_unique a l).
Qed.

Lemma pos_series_pos_sum (a : nat -> R) l :
  is_series a l ->
  (forall n, 0 <= a n) ->
  forall n, sum_n a n <= l.
Proof.
 intros H Ha n. change (is_lim_seq (sum_n a) l) in H.
 apply is_lim_seq_incr_compare; trivial.
 intros m. rewrite sum_Sn. unfold plus. simpl. generalize (Ha (S m)). lra.
Qed.

Lemma pos_series_pos_lim (a : nat -> R) l :
  is_series a l -> (forall n, 0 <= a n) -> 0 <= l.
Proof.
 intros H Ha.
 apply Rle_trans with (sum_n a O).
 rewrite sum_O. apply Ha.
 now apply (pos_series_pos_sum _ _ H).
Qed.

Lemma ex_series_Cmod (a : nat -> C) :
 ex_series (Cmod ∘ a) -> ex_series a.
Proof.
 apply (ex_series_le (V := C_CNM)).
 intros. rewrite <- Complex.Cmod_norm. apply Rle_refl.
Qed.

Lemma is_series_Cmod (a : nat -> C) (l:R) :
 is_series (Cmod ∘ a) l ->
 exists l':C, is_series a l' /\ Cmod l' <= l.
Proof.
 intros H. destruct (ex_series_Cmod a) as (l' & Hl'); [now exists l|].
 simpl in l'. exists l'. split; trivial.
 assert (E := is_lim_Cseq_Cmod (sum_n a) l' Hl').
 apply (is_lim_seq_le (Cmod ∘ (sum_n a)) (sum_n (Cmod ∘ a)) (Cmod l') l);
  trivial. intros. apply sum_n_triangle.
Qed.

Lemma CSeries_Cmod (a : nat -> C) :
  ex_series (Cmod ∘ a) -> Cmod (CSeries a) <= Series (Cmod ∘ a).
Proof.
 intros (l,Hl). destruct (is_series_Cmod a l Hl) as (l' & Hl' & LE).
 erewrite CSeries_unique; eauto. erewrite is_series_unique; eauto.
Qed.

Lemma CSeries_rest0 (a : nat -> C) (l : C) :
 is_series a l -> forall n, is_lim_Cseq (sum_n_m a (S n)) (l-sum_n a n).
Proof.
 intros H n.
 assert (H' : is_lim_Cseq (fun m => sum_n a m - sum_n a n) (l-sum_n a n)).
 { apply is_lim_Cseq_minus; trivial. apply is_lim_Cseq_const. }
 rewrite is_lim_Cseq_proj in *. split.
 - apply (is_lim_seq_ext_loc (Re ∘ (fun m => sum_n a m - sum_n a n)));
    try apply H'.
   exists n. intros m Hm. unfold compose. f_equal.
   symmetry. now apply (sum_n_m_sum_n (G:=Complex.C_AbelianGroup)).
 - apply (is_lim_seq_ext_loc (Im ∘ (fun m => sum_n a m - sum_n a n)));
    try apply H'.
   exists n. intros m Hm. unfold compose. f_equal.
   symmetry. now apply (sum_n_m_sum_n (G:=Complex.C_AbelianGroup)).
Qed.

Lemma CSeries_RtoC_impl (a : nat -> R) (l:C) :
  is_series (RtoC∘a) l -> is_series a (Re l) /\ Im l = 0%R.
Proof.
 intros H.
 change (is_lim_Cseq (sum_n (RtoC∘a)) l) in H.
 rewrite is_lim_Cseq_proj in H. destruct H as (H1,H2).
 apply is_lim_seq_ext with (v:=sum_n a) in H1.
 2:{ intros n. unfold compose. rewrite re_sum_n. now apply sum_n_ext. }
 apply is_lim_seq_ext with (v:=fun _ => 0%R) in H2.
 2:{ intros n. unfold compose. rewrite im_sum_n. apply sum_n_R0. }
 split. apply H1. apply is_lim_seq_unique in H2.
 rewrite Lim_seq_const in H2. now injection H2.
Qed.

Lemma CSeries_RtoC (a : nat -> R) (l:R) :
  is_series (RtoC∘a) (RtoC l) <-> is_series a l.
Proof.
 split.
 - intros H. change l with (Re (RtoC l)). now apply CSeries_RtoC_impl.
 - intros H.
   change (is_lim_Cseq (sum_n (RtoC∘a)) l).
   rewrite is_lim_Cseq_proj; simpl. split.
   + apply is_lim_seq_ext with (u:=sum_n a); try easy.
     intros n. unfold compose. rewrite re_sum_n. now apply sum_n_ext.
   + apply is_lim_seq_ext with (u:=fun _ => 0%R); try apply is_lim_seq_const.
     intros n. unfold compose. rewrite im_sum_n. symmetry.
     now apply sum_n_R0.
Qed.

(** Power series on C *)

Definition is_CPowerSeries (a : nat -> C) (z lim : C) :=
  is_lim_Cseq (sum_n (fun n => a n * z^n)) lim.

Definition ex_CPowerSeries (a : nat -> C) (z : C) :=
  exists lim, is_CPowerSeries a z lim.

Definition CPowerSeries (a : nat -> C) (z : C) : C :=
  CSeries (fun k => a k * z ^ k).

Lemma CPowerSeries_unique (a : nat -> C) (z l : C) :
  is_CPowerSeries a z l -> CPowerSeries a z = l.
Proof.
 apply CSeries_unique.
Qed.

Lemma CPowerSeries_correct (a : nat -> C) z :
  ex_CPowerSeries a z -> is_CPowerSeries a z (CPowerSeries a z).
Proof.
 apply CSeries_correct.
Qed.

Lemma Cmod_prod_aux a b n : Cmod b <= 1 -> Cmod (a * b^n) <= Cmod a.
Proof.
 intros Hb.
 rewrite Cmod_mult, Cmod_pow.
 rewrite <- (Rmult_1_r (Cmod a)) at 2.
 apply Rmult_le_compat_l. apply Cmod_ge_0.
 apply Rpow_le1. split. apply Cmod_ge_0. apply Hb.
Qed.

Lemma CPowerSeries_bound1 (a : nat -> C) l z :
  is_series (Cmod ∘ a) l -> Cmod z <= 1 ->
  forall n, Cmod (sum_n (fun k => a k * z^k) n) <= l.
Proof.
 intros Ha Hz n.
 eapply Rle_trans; [apply sum_n_triangle|].
 apply Rle_trans with (sum_n (Cmod ∘ a) n);
  [apply sum_n_le | apply pos_series_pos_sum; eauto; intros; apply Cmod_ge_0].
 intros m. now apply Cmod_prod_aux.
Qed.

Lemma CPowerSeries_bound2 (a : nat -> C) l z :
  is_series (Cmod ∘ a) l -> Cmod z <= 1 ->
  Cmod (CPowerSeries a z) <= l.
Proof.
 intros H Hz.
 unfold CPowerSeries. rewrite <- (is_series_unique (Cmod∘a) l H).
 eapply Rle_trans.
 - apply CSeries_Cmod.
   unfold compose.
   apply (ex_series_le (V :=R_CNM)) with (b:=Cmod∘a);
    try now exists l.
   intros n. change norm with Rabs.
   rewrite Rabs_right by apply Rle_ge, Cmod_ge_0. now apply Cmod_prod_aux.
 - apply Series_le. 2:now exists l.
   intros n. unfold compose. split; try apply Cmod_ge_0.
   now apply Cmod_prod_aux.
Qed.

Lemma CPowerSeries_bound3 (a : nat -> C) (l:R) z :
 is_series (Cmod ∘ a) l -> Cmod z <= 1 ->
 forall n,
 Cmod (CPowerSeries a z - sum_n (fun k => a k * z^k) n) <=
 l - sum_n (Cmod ∘ a) n.
Proof.
 intros H Hz n.
 assert (H' : ex_series (fun k => a k * z^k)).
 { apply ex_series_Cmod.
   apply (ex_series_le (V :=R_CNM)) with (b:=Cmod∘a);
     try now exists l.
   intros m. change norm with Rabs.
   rewrite Rabs_right by apply Rle_ge, Cmod_ge_0. now apply Cmod_prod_aux. }
 destruct H' as (l',H'). simpl in l'.
 unfold CPowerSeries. rewrite (CSeries_unique _ _ H').
 assert (R := Series_rest0 _ _ H n).
 assert (R' := CSeries_rest0 _ _ H' n).
 eapply is_lim_Cseq_Cmod'; eauto.
 intros m. eapply Rle_trans; [apply sum_n_m_triangle|].
 apply sum_n_m_le. intros k. now apply Cmod_prod_aux.
Qed.

Lemma is_powerseries_invlin r x : r<>0 -> Cmod (r*x) < 1 ->
 is_CPowerSeries (fun n => r^S n) x (/ (/r - x)).
Proof.
 intros Hr Hx.
 apply is_lim_Cseq_ext with (fun n => (1 - (r*x)^S n)/(/r-x)).
 { intros n. rewrite <- (Cmult_1_l (sum_n _ _)).
   rewrite <- (Cinv_l (/r-x)) at 2.
   2:{ intros E. apply Ceq_minus in E.
       rewrite <- E, Cinv_r, Cmod_1 in Hx; trivial. lra. }
   unfold Cdiv. rewrite Cmult_comm, <- Cmult_assoc. f_equal.
   rewrite sum_n_ext with (b:=fun k => r * (r*x)^k).
   2:{ intros k. now rewrite Cpow_S, Cpow_mul_l, Cmult_assoc. }
   rewrite sum_n_Cmult_l, Cmult_assoc.
   replace ((/r-x)*r) with (1-r*x) by now field.
   symmetry. apply sum_n_Cpow. }
 unfold Cdiv. rewrite <- (Cmult_1_l (/(/r-x))) at 1.
 apply is_lim_Cseq_mult; [|apply is_lim_Cseq_const].
 replace 1 with (1-0) at 1 by lca.
 apply is_lim_Cseq_minus. apply is_lim_Cseq_const.
 apply is_lim_Cseq_0_Cmod.
 apply is_lim_seq_ext with (fun n => (Cmod (r*x))^S n)%R.
 - intros n. unfold compose. now rewrite Cmod_pow.
 - rewrite <- is_lim_seq_incr_1. apply is_lim_seq_geom.
   now rewrite Rabs_right by apply Rle_ge, Cmod_ge_0.
Qed.

(** Delaying a sequence with extra initial zeros.
    See also Coquelicot.PSeries.PS_incr_n someday. *)

Definition delay {G:AbelianMonoid} (a:nat->G) p :=
  fun n => if n <? p then zero else a (n-p)%nat.

Lemma sum_n_delay {G:AbelianMonoid} (a:nat->G) p n :
  sum_n (delay a p) (n+p) = sum_n a n.
Proof.
 induction n.
 - rewrite Nat.add_0_l, sum_O.
   destruct p.
   + now rewrite sum_O.
   + rewrite sum_Sn.
     erewrite sum_n_ext_loc, sum_n_zero.
     2:{ intros k K. unfold delay. case Nat.ltb_spec; easy || lia. }
     unfold delay. simpl.
     case Nat.ltb_spec; try lia. intros _.
     replace (p-p)%nat with O by lia. apply plus_zero_l.
 - simpl. rewrite !sum_Sn, IHn. f_equal. unfold delay.
   case Nat.ltb_spec; try lia. intros _. f_equal. lia.
Qed.

Lemma delay_comp {G G':AbelianMonoid} (h:G->G') p (a:nat->G) :
 h zero = zero -> forall n, delay (h∘a) p n = h (delay a p n).
Proof.
 intros H n. unfold delay. now case Nat.ltb.
Qed.

Lemma delay_series_R p (a:nat->R) l :
  is_series a l -> is_series (delay a p) l.
Proof.
 intros H.
 change (is_lim_seq (sum_n (delay a p)) l).
 apply is_lim_seq_incr_n with (N:=p).
 eapply is_lim_seq_ext; [|apply H].
 intros n. symmetry. apply sum_n_delay.
Qed.

Lemma delay_powerseries_R p a x lim :
  is_series (fun n => a n * x^n)%R lim ->
  is_series (fun n => delay a p n * x^n)%R (x^p * lim)%R.
Proof.
 intros H.
 rewrite is_series_alt.
 rewrite is_lim_seq_incr_n with (N:=p).
 apply is_lim_seq_ext with (fun n => x^p * sum_n (fun k => a k * x^k) n)%R.
 { intros n. rewrite <- (sum_n_mult_l (K:=R_AbsRing)).
   rewrite <- sum_n_delay with (p:=p). apply sum_n_ext. clear n.
   intros n. unfold delay. case Nat.ltb_spec; intros.
   - change zero with R0. lra.
   - change mult with Rmult.
     rewrite !(Rmult_comm (a _)), <- Rmult_assoc, <- pow_add.
     f_equal. f_equal. lia. }
 apply is_lim_seq_mult'; trivial using is_lim_seq_const.
Qed.

Lemma delay_powerseries p a z lim :
  is_CPowerSeries a z lim ->
  is_CPowerSeries (delay a p) z (z^p * lim).
Proof.
 unfold is_CPowerSeries. intros H.
 rewrite is_lim_Cseq_incr_n with (N:=p).
 apply is_lim_Cseq_ext with (fun n => z^p * sum_n (fun k => a k * z^k) n).
 { intros n. rewrite <- sum_n_Cmult_l.
   rewrite <- sum_n_delay with (p:=p). apply sum_n_ext. clear n.
   intros n. unfold delay. case Nat.ltb_spec; intros.
   - change zero with C0. lca.
   - rewrite Cmult_assoc, (Cmult_comm (z^p)), <- Cmult_assoc. f_equal.
     rewrite <- Cpow_add. f_equal. lia. }
 apply is_lim_Cseq_mult; trivial using is_lim_Cseq_const.
Qed.

Local Open Scope R.

(** More on CV_radius *)

Lemma CV_disk_le_radius (a:nat->R) (x:R) :
 CV_disk a x -> Rbar.Rbar_le x (CV_radius a).
Proof.
 intros H.
 unfold CV_radius, Lub.Lub_Rbar.
 destruct (Lub.ex_lub_Rbar _) as (lu & Hlu). now apply Hlu.
Qed.

Lemma CV_radius_ge_1 (a : nat -> R) :
  ex_series (Rabs∘a) -> Rbar.Rbar_le 1 (CV_radius a).
Proof.
 intros H. apply CV_disk_le_radius.
 red. eapply ex_series_ext; eauto. intros n. now rewrite pow1, Rmult_1_r.
Qed.

Lemma CV_radius_le (a b : nat -> R) :
 (forall n, Rabs (a n) <= Rabs (b n)) ->
 Rbar.Rbar_le (CV_radius b) (CV_radius a).
Proof.
 intros H.
 unfold CV_radius, Lub.Lub_Rbar.
 destruct Lub.ex_lub_Rbar as (ubb & Hb & Hb').
 destruct Lub.ex_lub_Rbar as (uba & Ha & Ha'). simpl.
 - red in Hb, Ha. apply Hb'. red. intros x Hx. apply Ha.
   clear - H Hx. unfold CV_disk in *.
   eapply (ex_series_le (V:=R_CNM)); eauto.
   intros n. change norm with Rabs. rewrite Rabs_Rabsolu, !Rabs_mult.
   apply Rmult_le_compat_r; trivial using Rabs_pos.
Qed.

(** C power series projection (when point x is a Real) *)

Lemma is_CPowerSeries_proj (a:nat->C)(x:R) :
  ex_series (fun n => Cmod (a n) * Rabs x^n) ->
  is_CPowerSeries a x (PSeries (Re∘a) x, PSeries (Im∘a) x).
Proof.
 intros H.
 unfold is_CPowerSeries. rewrite is_lim_Cseq_proj. simpl. split.
 - eapply is_lim_seq_ext with (u:=sum_n (fun k => (Re∘a) k * x^k)%R).
   { intros n. unfold compose. rewrite re_sum_n. apply sum_n_ext.
     clear n. intros n. unfold compose.
     now rewrite <- re_scal_r, <- RtoC_pow. }
   unfold PSeries, Series. apply Lim_seq_correct'. rewrite <- ex_series_alt.
   eapply (ex_series_le (V:=R_CNM)); eauto.
   { intros n. change norm with Rabs.
     rewrite Rabs_mult. unfold compose. rewrite RPow_abs.
     apply Rmult_le_compat_r; try apply Rabs_pos. apply re_le_Cmod. }
 - eapply is_lim_seq_ext with (u:=sum_n (fun k => (Im∘a) k * x^k)%R).
   { intros n. unfold compose. rewrite im_sum_n. apply sum_n_ext.
     clear n. intros n. unfold compose.
     now rewrite <- im_scal_r, <- RtoC_pow. }
   unfold PSeries, Series. apply Lim_seq_correct'. rewrite <- ex_series_alt.
   eapply (ex_series_le (V:=R_CNM)); eauto.
   { intros n. change norm with Rabs.
     rewrite Rabs_mult. unfold compose. rewrite RPow_abs.
     apply Rmult_le_compat_r; try apply Rabs_pos. apply im_le_Cmod. }
Qed.

Lemma CPowerSeries_proj (a:nat->C)(x:R) :
  ex_series (fun n => Cmod (a n) * Rabs x^n) ->
  CPowerSeries a x = (PSeries (Re∘a) x, PSeries (Im∘a) x).
Proof.
 intros. now apply CPowerSeries_unique, is_CPowerSeries_proj.
Qed.

(** Unicity of coefficients of C power series *)

Lemma CPowerSeries_coef_ext (a b : nat -> C) :
 Rbar.Rbar_lt 0 (CV_radius (Cmod∘a)) ->
 Rbar.Rbar_lt 0 (CV_radius (Cmod∘b)) ->
 locally 0 (fun (x:R) => CPowerSeries a x = CPowerSeries b x) ->
 forall n, a n = b n.
Proof.
 intros Ha Hb E n.
 rewrite (surjective_pairing (a n)), (surjective_pairing (b n)).
 assert (L: locally 0 (fun x : R => PSeries (Re ∘ a) x = PSeries (Re ∘ b) x
                                 /\ PSeries (Im ∘ a) x = PSeries (Im ∘ b) x)).
 { destruct E as (eps & E).
   set (ra := match CV_radius (Cmod∘a) with Rbar.Finite r => r | _ => 1 end).
   assert (Ra : 0 < ra).
   { unfold ra. destruct (CV_radius (Cmod∘a)); try easy. lra. }
   set (rb := match CV_radius (Cmod∘b) with Rbar.Finite r => r | _ => 1 end).
   assert (Rb : 0 < rb).
   { unfold rb. destruct (CV_radius (Cmod∘b)); try easy. lra. }
   assert (LT : 0 < Rmin eps (Rmin ra rb)).
   { apply Rmin_glb_lt. apply eps. now apply Rmin_glb_lt. }
   set (eps' := mkposreal _ LT).
   exists eps'. intros y Y. change (Rabs (y-0) < eps') in Y.
   assert (Y0 : Rabs (y - 0) < eps).
   { apply Rlt_le_trans with eps'; trivial. apply Rmin_l. }
   specialize (E y Y0). clear Y0.
   rewrite !CPowerSeries_proj in E; trivial; try lra.
   + now injection E.
   + clear E Ha. clearbody ra.
     rewrite Rminus_0_r in Y.
     assert (ex_pseries (Cmod∘b) (Rabs y)).
     { apply CV_radius_inside. rewrite Rabs_Rabsolu.
       apply Rbar.Rbar_lt_le_trans with eps'; trivial.
       apply Rbar.Rbar_le_trans with (Rmin ra rb); [apply Rmin_r|].
       apply Rbar.Rbar_le_trans with rb; [apply Rmin_r|].
       unfold rb. destruct CV_radius; simpl; trivial; lra. }
     red in H. eapply ex_series_ext; eauto.
     intros k. unfold compose. unfold scal. simpl.
     change mult with Rmult.
     rewrite pow_n_pow. ring.
   + clear E Hb. clearbody rb.
     rewrite Rminus_0_r in Y.
     assert (ex_pseries (Cmod∘a) (Rabs y)).
     { apply CV_radius_inside. rewrite Rabs_Rabsolu.
       apply Rbar.Rbar_lt_le_trans with eps'; trivial.
       apply Rbar.Rbar_le_trans with (Rmin ra rb); [apply Rmin_r|].
       apply Rbar.Rbar_le_trans with ra; [apply Rmin_l|].
       unfold ra. destruct CV_radius; simpl; trivial; lra. }
     red in H. eapply ex_series_ext; eauto.
     intros k. unfold compose. unfold scal. simpl.
     change mult with Rmult.
     rewrite pow_n_pow. ring. }
 f_equal.
 - apply (PSeries_ext_recip (Re∘a) (Re∘b) n).
   + apply Rbar.Rbar_lt_le_trans with (CV_radius (Cmod∘a)); auto.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply re_le_Cmod.
   + apply Rbar.Rbar_lt_le_trans with (CV_radius (Cmod∘b)); auto.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply re_le_Cmod.
   + destruct L as (eps & L). exists eps. apply L.
 - apply (PSeries_ext_recip (Im∘a) (Im∘b) n).
   + apply Rbar.Rbar_lt_le_trans with (CV_radius (Cmod∘a)); auto.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply im_le_Cmod.
   + apply Rbar.Rbar_lt_le_trans with (CV_radius (Cmod∘b)); auto.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply im_le_Cmod.
   + destruct L as (eps & L). exists eps. apply L.
Qed.
