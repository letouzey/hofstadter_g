From Coq Require Import Lia Reals Lra.
From Coquelicot Require Complex.
From Coquelicot Require Import Hierarchy Continuity Derive AutoDerive
 RInt RInt_analysis Series PSeries.
From Hofstadter.HalfQuantum Require Import Complex Polynomial.
Require Import MoreTac MoreList MoreReals MoreLim MoreSum MoreComplex.
Require Import MorePoly MoreIntegral ThePoly GenFib Mu.
Local Open Scope R.
Local Open Scope C.
Local Open Scope poly_scope.
Local Coercion INR : nat >-> R.
Local Coercion RtoC : R >-> C.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * The second largest root of ThePoly has modulus>1 for k>=6

  We recall that ThePoly(k)(x) is x^k-x^(k-1)-1.
  We adapt to ThePoly the first pages of the initial proof that
  the Plastic Ratio (root of x^3-x-1, approx 1.3247...) is the
  smallest Pisot number. Reference:

  "Algebraic Integers whose Conjugates lie in the Unit Circle",
    Carl Ludwig Siegel, 1944.
*)

(** The core idea in Siegel's 1944 article :
    if a function g has no poles inside the unit circle,
    the integral of g(z)*g(/z)/z on the unit circle is
    the series of the square of the coefficients of g as power series. *)

Definition Mu (g : C -> C) :=
 /(2*PI) * CInt (fun t => g (Cexp t) * g (Cexp (-t))) 0 (2*PI).

Lemma Mu_aux1 (a : nat -> C) n :
  let h := fun t : R => sum_n (fun k : nat => a k * Cexp (k * t)) n in
  CInt (fun x => h x * h (-x)%R) 0 (2 * PI)
  = 2 * PI * sum_n (fun k => a k ^2) n.
Proof.
 induction n.
 - intros h. unfold h. rewrite !sum_O.
   rewrite (RInt_ext (V:=C_CNM)) with (g:=fun x => (a O)^2).
   2:{ intros x _. rewrite !sum_O. simpl. rewrite !Rmult_0_l.
       rewrite Cexp_0. fixeq C. ring. }
   rewrite RInt_const.
   rewrite Complex.scal_R_Cmult.
   change Coquelicot.Complex.Cmult with Cmult.
   change Coquelicot.Complex.RtoC with RtoC.
   now rewrite Rminus_0_r, RtoC_mult.
 - intros h. rewrite !sum_Sn.
   set (h1 := fun t => sum_n (fun k : nat => a k * Cexp (k * t)) n) in *.
   assert (Hh : forall x, continuous h x).
   { intros x. apply sum_n_continuous. intros m _. simpl.
     apply (continuous_scal_r (V:=Complex.C_NormedModule)).
     apply continuous_Cexpn. }
   assert (Hh1 : forall x, continuous h1 x).
   { intro x. apply sum_n_continuous. intros m _. simpl.
     apply (continuous_scal_r (V:=Complex.C_NormedModule)).
     apply continuous_Cexpn. }
   simpl in *.
   set (h2 := fun t => a (S n) * Cexp (S n * t)).
   assert (Hh2 : forall x, continuous h2 x).
   { intros x. apply (continuous_scal_r (V:=Complex.C_NormedModule)).
     apply continuous_Cexpn. }
   assert (E : forall t, h t = h1 t + h2 t).
   { intros t. unfold h. now rewrite sum_Sn. }
   rewrite (RInt_ext (V:=C_CNM))
    with (g:=fun x => h1(x)*h1(-x)%R + h1(x)*h2(-x)%R +
                      h2(x)*h1(-x)%R + h2(x)*h2(-x)%R).
   2:{ intros x _. rewrite !E. fixeq C. ring. }
   rewrite !(RInt_plus (V:=C_CNM));
    try apply (ex_RInt_continuous (V:=C_CNM));
    try intros x _.
   2:{ apply continuous_Cmult; trivial. apply continuous_comp; trivial.
       apply (continuous_opp (V:=R_NM)), continuous_id. }
   2:{ apply continuous_Cmult; trivial. apply continuous_comp; trivial.
       apply (continuous_opp (V:=R_NM)), continuous_id. }
   2:{ apply (continuous_plus (V:=C_NM));
        apply continuous_Cmult; trivial; apply continuous_comp; trivial;
        apply (continuous_opp (V:=R_NM)), continuous_id. }
   2:{ apply continuous_Cmult; trivial. apply continuous_comp; trivial.
       apply (continuous_opp (V:=R_NM)), continuous_id. }
   2:{ apply (continuous_plus (V:=C_NM));
       [apply (continuous_plus (V:=C_NM))|];
       apply continuous_Cmult; trivial; apply continuous_comp; trivial;
        apply (continuous_opp (V:=R_NM)), continuous_id. }
   2:{ apply continuous_Cmult; trivial. apply continuous_comp; trivial.
       apply (continuous_opp (V:=R_NM)), continuous_id. }
   rewrite IHn.
   rewrite (RInt_ext (V:=C_CNM))
     with (g:=fun x => a (S n) * sum_n (fun k => a k * Cexp ((S n-k)%nat*-x)) n).
   rewrite CInt_scal, CInt_sum_n_opp; try lia. rewrite Cmult_0_r.
   2:{ apply (ex_RInt_continuous (V:=C_CNM)).
       intros x _. apply sum_n_continuous. intros i _.
       apply continuous_Cmult. apply continuous_const.
       apply (continuous_comp Ropp (fun x => Cexp ((S n-i)%nat * x))).
       apply (continuous_opp (V:=R_NM)), continuous_id.
       apply continuous_Cexpn. }
   2:{ intros x _. unfold h1, h2.
       rewrite Cmult_assoc, (Cmult_comm _ (a (S n))), <- !Cmult_assoc.
       f_equal.
       rewrite <- sum_n_Cmult_r. apply sum_n_ext_loc. intros m Hm.
       rewrite <- Cmult_assoc. f_equal. rewrite <- Cexp_add. f_equal.
       rewrite minus_INR by lia. lra. }
   rewrite (RInt_ext (V:=C_CNM))
     with (g:=fun x => a (S n) * sum_n (fun k => a k * Cexp ((S n-k)%nat*x)) n).
   rewrite CInt_scal, CInt_sum_n; try lia. rewrite Cmult_0_r.
   2:{ apply (ex_RInt_continuous (V:=C_CNM)).
       intros x _. apply sum_n_continuous. intros.
       apply continuous_Cmult. apply continuous_const.
       apply continuous_Cexpn. }
   2:{ intros x _. unfold h1, h2.
       rewrite <- !Cmult_assoc. f_equal. rewrite Cmult_comm.
       rewrite <- sum_n_Cmult_r. apply sum_n_ext_loc. intros m Hm.
       rewrite <- Cmult_assoc. f_equal. rewrite <- Cexp_add. f_equal.
       rewrite minus_INR by lia. lra. }
   rewrite (RInt_ext (V:=C_CNM))
     with (g:=fun x => a (S n)^2).
   2:{ intros x _. unfold h2. ring_simplify.
       rewrite <- Cmult_assoc, <- Cexp_add.
       replace (Rplus _ _) with 0%R by lra. rewrite Cexp_0. apply Cmult_1_r. }
   rewrite CInt_const, RtoC_mult. change plus with Cplus. fixeq C. ring.
Qed.

Lemma Mu_series_square (a : nat -> C) (g : C -> C) :
 ex_series (Cmod ∘ a) ->
 (forall z, Cmod z = 1%R -> g z = CPowerSeries a z) ->
 Mu g = CSeries (fun n => (a n)^2).
Proof.
 intros (l & Hl) Hg. simpl in l.
 assert (Hg' : forall x, continuous (g∘Cexp) x).
 { intros x. apply continuous_ext with (f := CPowerSeries a∘Cexp).
   - intros y. symmetry. apply Hg, Cmod_Cexp.
   - apply CPowerSeries_Cexp_continuous; now exists l. }
 symmetry. apply CSeries_unique.
 intros P (eps,HP). simpl in P, HP.
 assert (LT : 0 < eps / Rmax 1 (4*l)).
 { apply Rmult_lt_0_compat. apply eps.
   apply Rinv_0_lt_compat. generalize (Rmax_l 1 (4*l)); lra. }
 set (eps' := mkposreal _ LT).
 destruct (Hl (ball l eps')) as (N & HN); try (now exists eps').
 exists N. intros n Hn. apply HP, C_ball. clear HP.
 specialize (HN n Hn).
 change (ball _ _ _) with (Rabs ((sum_n (Cmod ∘ a) n)-l) < eps') in HN.
 set (h := fun t => sum_n (fun k => a k * Cexp (k*t)) n). simpl in h.
 assert (Hh : forall x, continuous h x).
 { intros. apply sum_n_continuous. intros. apply continuous_Cmult.
   apply continuous_const. apply continuous_Cexpn. }
 assert (LE : forall t:R,
              Cmod (g(Cexp t)*g(Cexp (-t)) - h t * h(-t)%R) <= eps/2).
 { intros t.
   replace (_ - _) with
       (g (Cexp t) * (g (Cexp (- t)) - h (-t)%R)
        + (g (Cexp t) - h t)*h(-t)%R) by ring.
   eapply Rle_trans; [apply Cmod_triangle| ].
   rewrite !Cmod_mult.
   rewrite !Hg by (rewrite Cmod_Cexp; lra).
   assert (Cmod (CPowerSeries a (Cexp t)) <= l).
   { apply CPowerSeries_bound2; trivial. rewrite Cmod_Cexp; lra. }
   assert (D : forall t', Cmod (CPowerSeries a (Cexp t') - h t') <= eps').
   { intros t'. unfold h.
     rewrite sum_n_ext with (b := fun k => a k * Cexp t'^k).
     2:{ intros m. rewrite Cexp_pow. f_equal. f_equal. lra. }
     eapply Rle_trans. apply CPowerSeries_bound3; eauto.
     rewrite Cmod_Cexp; lra.
     apply Rabs_def2 in HN. lra. }
   apply Rle_trans with (l*eps' + eps'*l)%R.
   - apply Rplus_le_compat.
     + apply Rmult_le_compat; try apply Cmod_ge_0; easy.
     + apply Rmult_le_compat; try apply Cmod_ge_0; try easy.
       { unfold h. rewrite sum_n_ext with (b := fun k => a k * Cexp (-t)^k).
         2:{ intros m. rewrite Cexp_pow. f_equal. f_equal. lra. }
         apply CPowerSeries_bound1; trivial. rewrite Cmod_Cexp; lra. }
   - apply -> Rcomplements.Rle_div_r; try lra. ring_simplify.
     unfold eps'. simpl. unfold Rdiv. rewrite <- Rmult_assoc.
     apply <- Rcomplements.Rle_div_l.
     2:{ apply Rlt_gt. apply Rlt_le_trans with 1%R. lra. apply Rmax_l. }
     rewrite (Rmult_comm eps). apply Rmult_le_compat_r; try apply Rmax_r.
     generalize (cond_pos eps); lra. }
 assert (LE' : Cmod (CInt (fun t => g (Cexp t) * g (Cexp (- t))
                                   - h t * h (- t)%R) 0 (2*PI))
               <= 2*PI * (eps/2)).
 { replace (2*PI)%R with (2*PI - 0)%R at 2 by lra.
   apply CInt_Cmod.
   - generalize Rgt_2PI_0; lra.
   - apply (ex_RInt_continuous (V:=C_CNM)).
     intros x _.
     apply (continuous_minus (V:=C_CNM));
      apply continuous_Cmult; trivial.
     apply (continuous_comp Ropp (g∘Cexp)); trivial.
     apply (continuous_opp (V:=R_CNM)), continuous_id.
     apply (continuous_comp Ropp h); trivial.
     apply (continuous_opp (V:=R_CNM)), continuous_id.
   - intros x _. apply (LE x). }
 clear LE HN eps' LT.
 rewrite CInt_minus in LE'.
 2:{ apply (ex_RInt_continuous (V:=C_CNM)).
     intros x _. apply continuous_Cmult; trivial.
     apply (continuous_comp Ropp (g∘Cexp)); trivial.
     apply (continuous_opp (V:=R_CNM)), continuous_id. }
 2:{ apply (ex_RInt_continuous (V:=C_CNM)).
     intros x _. apply continuous_Cmult; trivial.
     apply continuous_comp; trivial.
     apply (continuous_opp (V:=R_NM)), continuous_id. }
 apply Rmult_le_compat_r with (r:=(/(2*PI))%R) in LE'.
 2:{ apply Rlt_le. apply Rinv_0_lt_compat, Rgt_2PI_0. }
 replace (2 * PI * (eps / 2) * / (2 * PI))%R with (eps/2)%R in LE'.
 2:{ field. apply PI_neq0. }
 rewrite <- (Rabs_right (/(2*PI))%R) in LE'.
 2:{ apply Rle_ge, Rlt_le. apply Rinv_0_lt_compat, Rgt_2PI_0. }
 rewrite <- Cmod_R, <- Cmod_mult in LE'.
 rewrite RtoC_inv, RtoC_mult in LE'.
 unfold Cminus in LE'. rewrite Cmult_plus_distr_r in LE'.
 rewrite Cmult_comm in LE'. fold (Mu g) in LE'.
 rewrite <- Copp_mult_distr_l in LE'.
 assert (E := Mu_aux1 a n). fold h in E. rewrite E in LE'. clear E.
 set (p := C2*PI) in LE'.
 rewrite (Cmult_comm p), <- Cmult_assoc, Cinv_r, Cmult_1_r in LE'.
 2:{ unfold p. rewrite <- RtoC_mult. apply RtoC_inj_neq.
     generalize Rgt_2PI_0; lra. }
 unfold Cminus. eapply Rle_lt_trans; [apply LE'| ].
 generalize (cond_pos eps). lra.
Qed.

(** ThePoly's reciprocal polynomial *)

Definition RevPoly k : Polynomial := monom C1 k +, [-C1;C1].

Lemma RevPoly_eval k x : Peval (RevPoly k) x = x^k + x - 1.
Proof.
 unfold RevPoly. rewrite !Pplus_eval, !monom_eval. cbn. ring.
Qed.

Lemma RevPoly_root_carac r k : Root r (RevPoly k) <-> r^k + r - 1 = 0.
Proof.
 unfold Root. now rewrite RevPoly_eval.
Qed.

Lemma revroot_nz k : k<>O -> ~ Root C0 (RevPoly k).
Proof.
 rewrite !RevPoly_root_carac. intros K. replace k with (S (k-1)) by lia.
 simpl. unfold Cminus. rewrite Cmult_0_l, !Cplus_0_l. intros [= E _].
 revert E. lra.
Qed.

Lemma RevPoly_eqn k x :
  k<>O -> x<>0 -> x^k + x - 1 = - x^k * ((/x)^k - (/x)^(k-1) -1).
Proof.
 intros K Hx.
 unfold Cminus.
 rewrite !Cmult_plus_distr_l.
 rewrite <- !Copp_mult_distr_r, Cmult_1_r, Copp_involutive.
 rewrite <- !Copp_mult_distr_l, Copp_involutive.
 rewrite <- Cpow_mul_l, Cinv_r, Cpow_1_l by trivial.
 replace k with (S (k-1)) at 2 by lia. simpl.
 rewrite <- Cmult_assoc, <- Cpow_mul_l, Cinv_r, Cpow_1_l; trivial.
 ring.
Qed.

Lemma RevPoly_deg k : k<>O -> degree (RevPoly k) = k.
Proof.
 intros K.
 unfold RevPoly.
 rewrite Pplus_comm.
 destruct (Nat.eq_dec k 1) as [->|K'].
 - simpl. rewrite Cplus_0_r. apply degree_is_1.
   rewrite <- RtoC_plus. intros E. apply RtoC_inj in E. lra.
 - rewrite Pplus_degree2.
   rewrite monom_degree. lia. apply C1_neq_C0.
   rewrite monom_degree. 2:apply C1_neq_C0.
   rewrite degree_is_1. lia. apply C1_neq_C0.
Qed.

Lemma RevPoly_monic k : (1<k)%nat -> monic (RevPoly k).
Proof.
 intros K.
 unfold RevPoly. rewrite Pplus_comm. unfold monic.
 rewrite topcoef_plus_ltdeg. apply topcoef_monom.
 rewrite monom_degree. 2:apply C1_neq_C0.
 rewrite degree_is_1. lia. apply C1_neq_C0.
Qed.

Lemma RevRoot_carac k x : k<>O ->
  Root x (RevPoly k) <-> Root (/x) (ThePoly k).
Proof.
 intros K. split.
 - intros H.
   assert (Hx : x <> 0). { intros ->. now apply (revroot_nz k). }
   rewrite RevPoly_root_carac in H. rewrite ThePoly_root_carac.
   rewrite RevPoly_eqn in H by trivial.
   apply Cmult_integral in H. destruct H as [H|H].
   + apply (Cpow_nonzero x k) in Hx.
     destruct Hx. now rewrite <- (Copp_involutive (x^k)), H, Copp_0.
   + apply Cminus_eq_0 in H. rewrite <- H. ring.
 - intros H.
   destruct (Ceq_dec x 0) as [->|N].
   + replace (/0) with 0 in H. now apply root_nz in H.
     unfold Cinv. simpl. rewrite Rmult_0_l, Rplus_0_l.
     unfold Rdiv. now rewrite Ropp_0, !Rmult_0_l.
   + rewrite RevPoly_root_carac. rewrite ThePoly_root_carac in H.
     rewrite RevPoly_eqn, H by trivial. ring.
Qed.

(** Predicates about secondary roots of ThePoly *)

Definition ThePoly_SndRootsLt1 k :=
  forall x, Root x (ThePoly k) -> x<>mu k -> Cmod x < 1.

Definition ThePoly_ExSndRootGe1 k :=
  exists x, Root x (ThePoly k) /\ x<>mu k /\ 1 <= Cmod x.

Lemma ThePoly_SndRoots_neg k :
  k<>O -> ThePoly_ExSndRootGe1 k <-> ~ThePoly_SndRootsLt1 k.
Proof.
 intros K. split.
 - intros (x & Hx & N & LE) H. specialize (H x Hx N). lra.
 - unfold ThePoly_ExSndRootGe1, ThePoly_SndRootsLt1. intros H.
   destruct (SortedRoots_exists k K) as (l & Hl).
   assert (H1 := SortedRoots_length k l Hl).
   assert (H2 := SortedRoots_roots k l Hl).
   assert (H3 := SortedRoots_mu k l Hl).
   destruct (Nat.eq_dec k 1) as [->|K1].
   + destruct H. intros r. rewrite <- H2. destruct l as [|r' [|] ]; try easy.
     rewrite <- H3. unfold Cnth. simpl. intuition.
   + assert (l @ 1 <> mu k).
     { rewrite <- H3. intro E.
       destruct Hl as (_,Hl). apply Csorted_alt in Hl.
       rewrite StronglySorted_nth in Hl. specialize (Hl 0%nat 1%nat lia).
       rewrite E in Hl. revert Hl. apply Cgt_order. }
     exists (l @ 1); repeat split; trivial.
     * rewrite <- H2. apply nth_In; lia.
     * apply Rnot_lt_le. intros H4. apply H.
       intros r Hr Hr'. rewrite <- H2 in Hr.
       eapply Rle_lt_trans; [ | apply H4 ].
       apply SortedRoots_Cmod_sorted in Hl.
       rewrite StronglySorted_nth in Hl.
       destruct (In_nth l r 0 Hr) as (i & Hi & <-).
       change (nth i l 0) with (l @ i) in *.
       destruct i as [|[|i] ]; try lra. intuition.
       apply Rge_le, Hl. lia.
Qed.

(** Main goal for the moment : showing that 6<=k implies ThePoly_ExSndRootGe1.
    Later we will prove that 6<=k implies ThePoly_ExSndRootsGt1.
    For lower values of k, see files F3.v F4.v F5.v.

   Beware: these predicates about ThePoly do not exactly translate to
   (mu k) being a Pisot number or not. Indeed, ThePoly is sometimes reducible
   on Z, hence not the minimal polynomial of (mu k). This occurs when
   k = 5 mod 6, see later. *)

(** The key functions in Siegel's 1944 article.
    - f is ThePoly/RevPoly
    - g is f without its pole at (tau k)
    - h is here an intermediate step for convenience : 1/RevPoly without
      its pole at (tau k).
*)

Definition f k x := (x^k-x^(k-1)-1) / (x^k + x -1).

Definition g k x := (1 - mu k * x) * f k x.

Definition h k x := (1 - mu k * x) / (x^k + x -1).

Lemma ff k x : k<>O -> x<>0 -> ~Root x (ThePoly k) -> ~Root x (RevPoly k) ->
  f k x * f k (/x) = 1.
Proof.
 intros K H1 H2 H3. unfold f.
 rewrite RevPoly_eqn by trivial.
 rewrite RevPoly_eqn, !Cinv_inv by (trivial; now apply nonzero_div_nonzero).
 rewrite !Cpow_inv. field. repeat split; try now apply Cpow_nonzero.
 - intro E. apply H2, ThePoly_root_carac.
   apply Cminus_eq_0 in E. rewrite <- E. ring.
 - replace k with (S (k-1)) at 2 by lia. simpl.
   replace (_-_-_) with ((-x^(k-1))*(x^k + x - 1)) by ring.
   intros E. apply Cmult_integral in E. destruct E as [E|E].
   + apply (Cpow_nonzero x (k-1)) in H1. apply H1.
     rewrite <- (Copp_involutive (x^(k-1))), E. lca.
   + apply H3. now apply RevPoly_root_carac.
Qed.

(** Future PowerSeries coefs for f g h *)

Definition dh k n : R :=
 if n =? 0 then (-1)%R else (mu k * A k (n-k) - A k (n-(k-1)))%R.

Definition df k n : nat :=
 (if n <? k-1 then 1 else A k (n-k) + A k (n-2*(k-1)))%nat.

Definition dg k n : R :=
 if n =? 0 then 1%R else (df k n - mu k * df k (n-1))%R.

Lemma df_1 k n : (n < k-1 -> df k n = 1)%nat.
Proof.
 unfold df. case Nat.ltb_spec; lia.
Qed.

Lemma df_2 k n : (1<k -> n = k-1 \/ n = k -> df k n = 2)%nat.
Proof.
 unfold df. case Nat.ltb_spec; try lia. intros. rewrite !A_base; lia.
Qed.

Lemma df_lin k n : (k<>0 -> k<=n<=2*(k-1) -> df k n = S n-(k-1))%nat.
Proof.
 unfold df. case Nat.ltb_spec; try lia; intros. rewrite !A_base; lia.
Qed.

(** Power series decomposition of 1/RevPoly and h and g *)

Section PowerSeriesDecomp.
Variable k : nat.
Variable K : (1<k)%nat.
Variable roots : list C.
Hypothesis roots_ok : SortedRoots k roots.

Lemma RevPoly_alt : RevPoly k ≅ linfactors (map Cinv roots).
Proof.
 destruct (All_roots (RevPoly k)) as (l, Hl).
 { now apply RevPoly_monic. }
 rewrite Hl.
 apply linfactors_perm.
 symmetry. apply NoDup_Permutation_bis.
 - apply FinFun.Injective_map_NoDup.
   intros x y Hx. now rewrite <- (Cinv_inv x), Hx, Cinv_inv.
   now apply (SortedRoots_nodup k).
 - rewrite map_length, (SortedRoots_length k roots) by trivial.
   rewrite <- linfactors_degree, <- Hl, RevPoly_deg; lia.
 - intros x. rewrite in_map_iff. intros (r & <- & Hr).
   rewrite linfactors_roots. rewrite <- Hl. rewrite RevRoot_carac by lia.
   rewrite Cinv_inv. rewrite <- SortedRoots_roots; eauto.
Qed.

Definition coef r := / (k*r-(k-1)).

Definition coef_alt i :
  (i < k)%nat -> coef (roots@i) = PartFrac.coef (map Cinv roots) i.
Proof.
 intros Hi.
 unfold coef, PartFrac.coef. f_equal.
 rewrite <- Peval_Pdiff_linfactors.
 2:{ apply FinFun.Injective_map_NoDup.
     intros a b E. now rewrite <- (Cinv_inv a), E, Cinv_inv.
     eapply SortedRoots_nodup; eauto. }
 2:{ now rewrite map_length, (SortedRoots_length _ _ roots_ok). }
 rewrite <- RevPoly_alt.
 assert (Hr : Root (roots@i) (ThePoly k)).
 { eapply SortedRoots_roots; eauto. apply nth_In.
   now rewrite (SortedRoots_length _ _ roots_ok). }
 unfold Cnth in *. rewrite nth_map_indep with (d':=0); trivial.
 2:{ now rewrite (SortedRoots_length _ _ roots_ok). }
 set (r := nth _ _ _) in *.
 unfold RevPoly. rewrite Pdiff_plus, diff_monom.
 rewrite Pplus_eval, Pmult_eval, monom_eval, Pconst_eval.
 replace (pred k) with (k-1)%nat by lia.
 simpl Pdiff. rewrite Cplus_0_r. unfold Peval; simpl. ring_simplify. f_equal.
 replace (k*r+-1*k) with (k*(r-1)) by ring. f_equal.
 assert (Hr' : r^(k-1) <> 0).
 { apply Cpow_nonzero. intros ->. eapply root_nz; eauto. }
 apply Cmult_eq_reg_l with (r ^(k-1)); trivial.
 rewrite ThePoly_root_eqn; trivial. rewrite Cpow_inv, Cinv_r; trivial.
Qed.

Definition coef' r := coef r * (1 - mu k / r).

Lemma h_partfrac x : ~Root x (RevPoly k) ->
 h k x = Clistsum (map (fun r => coef' r / (x - /r)) (tl roots)).
Proof.
 intros Hx.
 assert (E : roots = RtoC (mu k) :: tl roots).
 { rewrite <- (SortedRoots_mu _ _ roots_ok).
   generalize (SortedRoots_length _ _ roots_ok).
   destruct roots; simpl; easy || lia. }
 unfold h. replace (1 - mu k * x) with ((-mu k) * (x - /mu k)).
 2:{ field. intros [= H]. generalize (mu_pos k). lra. }
 unfold Cdiv.
 rewrite <- RevPoly_eval, RevPoly_alt.
 rewrite E at 1. simpl map. simpl linfactors.
 rewrite Pmult_eval, cons_eval, Pconst_eval.
 rewrite Cmult_1_r, (Cplus_comm _ x).
 rewrite (Cmult_comm (Peval _ _)), Cinv_mult, Cmult_assoc.
 rewrite <- (Cmult_assoc (-mu k)), Cinv_r, Cmult_1_r.
 2:{ change (x - / mu k <> 0). rewrite <- Ceq_minus.
     intros ->. apply Hx. rewrite RevRoot_carac, Cinv_inv by lia.
     apply mu_is_root; lia. }
 rewrite PartFrac.inv_linfactors.
 2:{ generalize (SortedRoots_length _ _ roots_ok).
     destruct roots as [|a [|b l] ]; simpl; easy || lia. }
 2:{ apply FinFun.Injective_map_NoDup.
     intros a b E'. now rewrite <- (Cinv_inv a), E', Cinv_inv.
     assert (D := SortedRoots_nodup _ _ roots_ok).
     inversion D; subst; easy. }
 2:{ contradict Hx. rewrite RevPoly_alt, <- linfactors_roots, E.
     simpl. now right. }
 rewrite (@big_sum_mult_l _ _ _ _ C_is_ring).
 rewrite Clistsum_map with (d:=0).
 rewrite map_length. apply big_sum_eq_bounded.
 intros i Hi.
 unfold Cnth. rewrite nth_map_indep with (d':=0); trivial.
 set (r := nth _ _ _). simpl. unfold Cdiv. rewrite Cmult_assoc. f_equal.
 assert (Hr' : r = roots@(S i)). { now rewrite E. }
 rewrite Hr' at 1. unfold coef'. rewrite coef_alt.
 2:{ rewrite <- (SortedRoots_length _ _ roots_ok).
     rewrite E. simpl. lia. }
 unfold PartFrac.coef. rewrite E at 2. simpl.
 unfold Cnth in *. rewrite !nth_map_indep with (d':=0); trivial.
 2:{ rewrite E. simpl. lia. }
 rewrite <- Hr'. unfold r at 2. set (m := G_big_mult _).
 rewrite !Cinv_mult. rewrite <- Cmult_assoc, (Cmult_comm (/m)), Cmult_assoc.
 f_equal. clear x Hx m.
 field; repeat split.
 - intros Hr. apply (root_nz k). rewrite <- Hr.
   apply (SortedRoots_roots _ _ roots_ok). rewrite Hr'. apply nth_In.
   rewrite E. simpl. lia.
 - intros M. apply RtoC_inj in M. generalize (mu_pos k). lra.
 - intros E'. apply Ceq_minus in E'.
   assert (D := SortedRoots_nodup _ _ roots_ok).
   rewrite E in D. inversion_clear D. apply H. rewrite E'. now apply nth_In.
Qed.

Lemma tl_roots_nz r : In r (tl roots) -> r<>0.
Proof.
 intros IN ->.
 assert (IN' : In 0 roots).
 { destruct roots. easy. simpl. now right. }
 rewrite linfactors_roots in IN'. rewrite <- (proj1 roots_ok) in IN'.
 revert IN'. apply root_nz.
Qed.

Lemma dh_eqn n :
  RtoC (dh k n) = Clistsum (map (fun r => - coef' r * r^S n) (tl roots)).
Proof.
 assert (E : roots = RtoC (mu k) :: tl roots).
 { rewrite <- (SortedRoots_mu _ _ roots_ok).
   generalize (SortedRoots_length _ _ roots_ok).
   destruct roots; simpl; easy || lia. }
 unfold dh.
 case Nat.eqb_spec; intros N.
 - subst n.
   rewrite map_ext_in with
       (g:=fun r => mu k * (coefB k r * r^(k-2)) - coefB k r * r^(k-1)).
   2:{ intros r R. simpl.
       unfold coef', coefB. unfold Cdiv. fold (coef r).
       replace (r^(k-1)) with (r*r^(k-2)).
       2:{ now replace (k-1)%nat with (S (k-2)) by lia. }
       field.
       split; [apply Cpow_nonzero|]; now apply tl_roots_nz. }
   rewrite <- Clistsum_minus.
   rewrite <- map_map, <- Clistsum_factor_l.
   assert (E0 := Equation_B k roots roots_ok (k-2)).
   rewrite B_zero in E0 by lia.
   rewrite E in E0. simpl in E0. symmetry in E0.
   rewrite Cplus_comm, <- (Copp_involutive (Cmult _ _)) in E0.
   apply Cminus_eq_0 in E0. rewrite E0. clear E0.
   assert (E1 := Equation_B k roots roots_ok (k-1)).
   rewrite B_one in E1 by lia.
   rewrite E in E1. simpl in E1.
   replace (RtoC (-1)) with (Copp C1) by lca. rewrite E1.
   replace (mu k^(k-1)) with (mu k * mu k^(k-2)).
   2:{ now replace (k-1)%nat with (S (k-2)) by lia. }
   ring.
 - rewrite RtoC_minus, RtoC_mult.
   destruct (Nat.le_gt_cases n (k-1)) as [LE|GT].
   + replace (n-(k-1))%nat with O by lia.
     replace (n-k)%nat with O by lia. simpl Cminus.
     rewrite map_ext_in with
         (g:=fun r => mu k * (coefB k r * r^((k-1)+(n-1)))
                      - coefB k r * r^((k-1)+n)).
     2:{ intros r R.
         unfold coef', coefB. unfold Cdiv. fold (coef r).
         replace n with (S (n-1)) at 1 3 by lia. rewrite !Cpow_add, !Cpow_S.
         field.
         split; [apply Cpow_nonzero|]; now apply tl_roots_nz. }
     rewrite <- Clistsum_minus.
     rewrite <- map_map, <- Clistsum_factor_l.
     assert (E0 := Equation_B k roots roots_ok ((k-1)+(n-1))).
     rewrite B_one in E0 by lia.
     rewrite E in E0. simpl in E0. rewrite E0 at 1. clear E0.
     assert (E1 := Equation_B k roots roots_ok ((k-1)+n)).
     rewrite B_one in E1 by lia.
     rewrite E in E1. simpl in E1. rewrite E1.
     rewrite Ceq_minus. ring_simplify.
     replace ((k-1)+n)%nat with (S ((k-1)+(n-1)))%nat by lia. simpl. ring.
   + replace (mu k * _ - _) with
         (mu k * (A k (n-(k-1)-1) - tau k * A k (n-(k-1)))%R).
     2:{ unfold tau. rewrite RtoC_minus, RtoC_mult, RtoC_inv.
         replace (n-(k-1)-1)%nat with (n-k)%nat by lia. field.
         intros [= E']. generalize (mu_pos k); lra. }
     rewrite (Equation_dA k roots roots_ok) by lia.
     rewrite Clistsum_factor_l, map_map. f_equal. apply map_ext_in.
     intros r R.
     unfold coefdA, coefA, coef'. unfold Cdiv. fold (coef r).
     unfold tau. rewrite RtoC_inv.
     rewrite !Cpow_S. replace n with (n-(k-1)+(k-1))%nat at 2 by lia.
     rewrite Cpow_add. replace k with (S (k-1)) at 2 by lia. simpl. field.
     split.
     * now apply tl_roots_nz.
     * intros E'. apply RtoC_inj in E'. generalize (mu_pos k); lra.
Qed.

Lemma ex_pseries_Rabs_dh (x:R) :
  (forall r, In r (tl roots) -> Cmod (r*x) < 1) ->
  ex_series (fun n => Rabs (dh k n * x^n)).
Proof.
 intros H.
 apply (ex_series_le (V:=R_CNM)) with
  (b:=fun n =>
   Rlistsum (map (fun r => Cmod (coef' r * r) * (Cmod (r * x))^n)%R (tl roots))).
 { intros n. change norm with Rabs. rewrite Rabs_Rabsolu.
   rewrite Rabs_mult, <- !Cmod_R, dh_eqn, <- Cmod_mult, Cmult_comm.
   rewrite Clistsum_factor_l, map_map.
   eapply Rle_trans; [eapply Clistsum_mod|]. rewrite map_map.
   apply Rlistsum_le. intros r R.
   rewrite <- RtoC_pow, Cpow_S, !Cmod_mult, Cmod_opp, !Cmod_pow.
   rewrite Rpow_mult_distr. ring_simplify. lra. }
 apply ex_series_Rlistsum.
 intros r R.
 apply (ex_series_scal (V:=R_NM)).
 apply ex_series_geom. rewrite Rabs_pos_eq by apply Cmod_ge_0. now apply H.
Qed.

Lemma ex_series_Rabs_dh :
  (forall r, In r (tl roots) -> Cmod r < 1) ->
  ex_series (Rabs ∘ dh k).
Proof.
 intros H.
 eapply ex_series_ext; [|apply (ex_pseries_Rabs_dh 1); trivial].
 - intros n. simpl. now rewrite pow1, Rmult_1_r.
 - intros r. rewrite Cmult_1_r. apply H.
Qed.

Lemma h_is_powerseries (x:C) :
 x<>tau k ->
 (forall r, In r (tl roots) -> Cmod (r*x) < 1) ->
 is_CPowerSeries (dh k) x (h k x).
Proof.
 intros Hx Hr.
 assert (E : roots = RtoC (mu k) :: tl roots).
 { rewrite <- (SortedRoots_mu _ _ roots_ok).
   generalize (SortedRoots_length _ _ roots_ok).
   destruct roots; simpl; easy||lia. }
 assert (Hx' : ~Root x (RevPoly k)).
 { intro R. rewrite RevPoly_alt, <- linfactors_roots, E in R.
   simpl in R. destruct R as [R|R].
   - apply Hx. rewrite <- R. unfold tau. now rewrite RtoC_inv.
   - rewrite in_map_iff in R. destruct R as (r & <- & IN).
     specialize (Hr _ IN). rewrite Cinv_r, Cmod_1 in Hr; try lra.
     now apply tl_roots_nz. }
 rewrite h_partfrac by trivial.
 apply is_lim_Cseq_ext with
     (f := fun n => Clistsum (map
            (fun r => sum_n (fun k => - coef' r * (r^S k*x^k)) n) (tl roots))).
 - intros n. rewrite <- Clistsum_sum_n. apply sum_n_ext. clear n.
   intros n.
   rewrite dh_eqn.
   rewrite map_ext with (g:=fun r => x^n * (- coef' r * r ^ S n))
    by (intros; ring).
   rewrite <- map_map.
   rewrite <- Clistsum_factor_l. apply Cmult_comm.
 - apply is_lim_Cseq_Clistsum.
   intros r Hr'.
   replace (coef' r / (x - / r)) with (-coef' r * / (/r - x)).
   2:{ field; simpl; repeat split.
       - now apply tl_roots_nz.
       - intros H. apply Ceq_minus in H. specialize (Hr _ Hr').
         rewrite Cmult_comm, H, Cmod_1 in Hr. lra.
       - intros H. apply Ceq_minus in H. specialize (Hr _ Hr').
         rewrite Cmult_comm, <- H, Cmod_1 in Hr. lra. }
   apply is_lim_Cseq_ext with
       (fun n => (-coef' r)*sum_n (fun k => r^S k*x^k) n).
   { intros n. now rewrite sum_n_Cmult_l. }
   apply is_lim_Cseq_mult. apply is_lim_Cseq_const.
   apply is_powerseries_invlin. now apply tl_roots_nz. now apply Hr.
Qed.

Lemma dg_eqn n :
 RtoC (dg k n) = delay (dh k) k n - delay (dh k) (k-1) n - dh k n.
Proof.
 unfold delay, dg, zero. simpl.
 case Nat.eqb_spec; intros Hn.
 - subst. simpl. do 2 case Nat.ltb_spec; try lia.
   intros _ _. unfold dh. simpl. lca.
 - rewrite RtoC_minus, RtoC_mult.
   do 2 case Nat.ltb_spec; try lia.
   + intros Hn' _. unfold dh, df.
     case Nat.eqb_spec; try lia. intros _.
     do 2 case Nat.ltb_spec; try lia. intros _ _.
     replace (n-(k-1))%nat with O by lia. simpl.
     replace (n-k)%nat with O by lia. simpl.
     rewrite RtoC_minus, RtoC_mult. ring.
   + intros Hn2 Hn3. replace n with (k-1)%nat by lia. clear Hn Hn2 Hn3.
     replace ((k-1)-(k-1))%nat with O by lia.
     unfold dh, df. simpl.
     case Nat.eqb_spec; try lia. intros _.
     do 2 case Nat.ltb_spec; try lia. intros _ _.
     repeat (replace (_-_)%nat with O by lia). simpl.
     rewrite RtoC_plus, RtoC_minus, RtoC_mult. ring.
   + intros _ Hn'. unfold dh, df.
     do 2 case Nat.ltb_spec; try lia. intros _ _.
     repeat case Nat.eqb_spec; try lia; intros.
     * replace (n-(k-1))%nat with (S O) by lia.
       repeat replace (_-_)%nat with O by lia. simpl.
       rewrite !RtoC_minus, !RtoC_mult, !RtoC_plus. ring.
     * apply Ceq_minus.
       rewrite !plus_INR, !RtoC_minus, !RtoC_mult, !RtoC_plus.
       replace (n-2*(k-1))%nat with (n-(k-1)-(k-1))%nat by lia.
       ring_simplify.
       replace (n-(k-1))%nat with (S (n-k)) at 2 by lia.
       rewrite A_S, plus_INR, RtoC_plus. ring_simplify.
       replace (n-1-2*(k-1))%nat with (n-(k-1)-k)%nat by lia.
       ring_simplify.
       rewrite (@A_sum k (n-k)), plus_INR, RtoC_plus by lia.
       replace (n-1-k)%nat with (n-k-1)%nat by lia. ring.
Qed.

Lemma ex_pseries_Rabs_dg (x:R) :
  (forall r, In r (tl roots) -> Cmod (r*x) < 1) ->
  ex_series (fun n => Rabs (dg k n * x^n)).
Proof.
 intros H.
 apply (ex_series_le (V:=R_CNM)) with
  (b:=(fun n =>
       (delay (Rabs∘dh k) k n + delay (Rabs∘dh k) (k-1) n + Rabs (dh k n))
       *Rabs (x^n))%R).
 { intros n.
   rewrite !(delay_comp Rabs) by apply Rabs_R0.
   change norm with Rabs.
   rewrite Rabs_pos_eq by apply Rabs_pos.
   rewrite Rabs_mult. apply Rmult_le_compat_r; try apply Rabs_pos.
   rewrite <- Cmod_R, dg_eqn, <- !RtoC_minus, Cmod_R. unfold Rminus.
   eapply Rle_trans; [eapply Rabs_triang|rewrite Rabs_Ropp].
   apply Rplus_le_compat_r.
   eapply Rle_trans; [eapply Rabs_triang|rewrite Rabs_Ropp; lra]. }
 eapply ex_series_ext.
 { intros n. symmetry. rewrite 2 Rmult_plus_distr_r. rewrite <- Rabs_mult.
   rewrite <- RPow_abs. reflexivity. }
 destruct (ex_pseries_Rabs_dh x H) as (l & Hl).
 apply (ex_series_plus (V:=R_NM)); [apply (ex_series_plus (V:=R_NM))|].
 - exists (Rabs x^k * l)%R. apply delay_powerseries_R.
   eapply is_series_ext; eauto.
   { intros n. unfold compose. now rewrite Rabs_mult, RPow_abs. }
 - exists (Rabs x^(k-1) * l)%R. apply delay_powerseries_R.
   eapply is_series_ext; eauto.
   { intros n. unfold compose. now rewrite Rabs_mult, RPow_abs. }
 - exists l; trivial; now apply delay_series_R.
Qed.

Lemma ex_series_Rabs_dg :
  (forall r, In r (tl roots) -> Cmod r < 1) ->
  ex_series (Rabs ∘ dg k).
Proof.
 intros H.
 eapply ex_series_ext; [|apply (ex_pseries_Rabs_dg 1); trivial].
 - intros n. simpl. now rewrite pow1, Rmult_1_r.
 - intros r. rewrite Cmult_1_r. apply H.
Qed.

Lemma g_is_powerseries (x:C) :
 x<>tau k ->
 (forall r, In r (tl roots) -> Cmod (r*x) < 1) ->
 is_CPowerSeries (dg k) x (g k x).
Proof.
 intros Hx Hr.
 unfold g, f. unfold Cdiv.
 rewrite Cmult_assoc, (Cmult_comm (1-_)), <- Cmult_assoc.
 change (_*/_) with (h k x).
 assert (H := h_is_powerseries x Hx Hr).
 assert (H1 := delay_powerseries (k-1) _ _ _ H).
 assert (H2 := delay_powerseries k _ _ _ H).
 assert (H3 := is_lim_Cseq_minus _ _ _ _ H2 H1).
 assert (H4 := is_lim_Cseq_minus _ _ _ _ H3 H). clear H1 H2 H3.
 unfold Cminus. rewrite !Cmult_plus_distr_r.
 rewrite <- !Copp_mult_distr_l, Cmult_1_l.
 eapply is_lim_Cseq_ext; [|apply H4]. clear H H4.
 intros n. simpl. rewrite !sum_n_minus. apply sum_n_ext. clear n.
 intros n.
 unfold Cminus. rewrite !Copp_mult_distr_l, <- !Cmult_plus_distr_r. f_equal.
 symmetry. rewrite dg_eqn. now rewrite <- !(delay_comp RtoC).
Qed.

Lemma g_powerseries (x:C) :
 x<>tau k ->
 (forall r, In r (tl roots) -> Cmod (r*x) < 1) ->
 g k x = CPowerSeries (dg k) x.
Proof.
 intros. symmetry. now apply CPowerSeries_unique, g_is_powerseries.
Qed.

End PowerSeriesDecomp.

Lemma Hyp_alt k roots :
 SortedRoots k roots ->
 ThePoly_SndRootsLt1 k ->
 forall r, In r (tl roots) -> Cmod r < 1.
Proof.
 intros roots_ok Hyp r R.
 assert (L := SortedRoots_length _ _ roots_ok).
 assert (ND := SortedRoots_nodup _ _ roots_ok).
 assert (M := SortedRoots_mu _ _ roots_ok).
 destruct roots as [|r0 l]; try easy. simpl in *.
 apply Hyp.
 - rewrite (proj1 roots_ok), <- linfactors_roots. now right.
 - inversion_clear ND. rewrite <- M. unfold Cnth. simpl. now intros ->.
Qed.

(** Siegel's Lemma 1. Fortunately it is enough here to derive
    a contradiction when 6<=k, no need to formalize the rest of
    Siegel's article. *)

Lemma One k : (1<k)%nat -> ThePoly_SndRootsLt1 k ->
 CSeries (fun n => (dg k n)^2) = 1 + mu k^2.
Proof.
 intros Hk Hyp.
 destruct (SortedRoots_exists k lia) as (roots, roots_ok).
 assert (Hyp' := Hyp_alt _ _ roots_ok Hyp).
 rewrite <- (Mu_series_square (dg k) (g k)).
 { unfold Mu.
   assert (N : C2*PI <> 0).
   { intros E. rewrite <- RtoC_mult in E. apply RtoC_inj in E.
     generalize PI_RGT_0; lra. }
   apply Cmult_eq_reg_l with (C2*PI); trivial.
   rewrite Cmult_assoc, Cinv_r, Cmult_1_l; trivial.
   apply is_CInt_unique.
   apply (is_RInt_ext (V:=C_NM))
    with (f := fun t => 1 + mu k^2 - mu k * (Cexp t - -Cexp (-t))).
   { intros t _.
     transitivity ((1 - mu k * Cexp t)*(1 - mu k * Cexp (-t))).
     { rewrite Cexp_neg. fixeq C. field. apply Cexp_nonzero. }
     unfold g. rewrite <- !Cmult_assoc. f_equal.
     rewrite (Cmult_comm (1-_)), Cmult_assoc.
     rewrite Cexp_neg at 2.
     rewrite ff; try lia; try apply Cexp_nonzero; try ring.
     - intros H. apply Hyp in H. rewrite Cmod_Cexp in H.
       assert (N' : Cexp t <> mu k).
       { intros E. apply (f_equal Cmod) in E.
         assert (T := mu_itvl k).
         rewrite Cmod_Cexp, Cmod_R, Rabs_right in E; lra. }
       specialize (H N'). lra.
     - rewrite RevRoot_carac, <- Cexp_neg; try lia.
       intros H. apply Hyp in H. rewrite Cmod_Cexp in H.
       assert (N' : Cexp (-t) <>  mu k).
       { intros E. apply (f_equal Cmod) in E.
         assert (T := mu_itvl k).
         rewrite Cmod_Cexp, Cmod_R, Rabs_right in E; lra. }
       specialize (H N'). lra. }
   replace (C2*_*_) with (C2*PI*(1+mu k^2) - 0) by ring.
   apply (is_RInt_minus (V:=C_NM)).
   - rewrite <- RtoC_mult.
     replace (RtoC (2*PI)) with (RtoC (2*PI)-0) by ring.
     apply is_CInt_const.
   - replace 0 with ((mu k)*(0-0)) at 1 by ring.
     apply is_CInt_scal, (is_RInt_minus (V:=C_NM)).
     + generalize (is_CInt_Cexp 1 lia). apply is_RInt_ext.
       intros x _. f_equal. now rewrite Rmult_1_l.
     + apply (is_RInt_comp_opp (V:=C_NM)).
       rewrite Ropp_0, Ropp_mult_distr_l.
       generalize (is_CInt_Cexp' 1 lia). apply is_RInt_ext.
       intros x _. f_equal. now rewrite Rmult_1_l. }
 { apply ex_series_ext with (a:=Rabs∘dg k).
   - intros n. symmetry. apply Cmod_R.
   - now apply (ex_series_Rabs_dg k Hk roots roots_ok). }
 { intros z Hz. apply (g_powerseries k Hk roots roots_ok).
   - intros ->.
     rewrite Cmod_R, Rabs_right in Hz; generalize (tau_itvl k); lra.
   - intros r R. rewrite Cmod_mult, Hz, Rmult_1_r. now apply Hyp'. }
Qed.

Local Open Scope R.

Lemma One' k : (1<k)%nat -> ThePoly_SndRootsLt1 k ->
 Series (fun n => (dg k n)^2) = 1 + mu k^2.
Proof.
 intros Hk Hyp.
 apply is_series_unique.
 rewrite <- (re_RtoC (1+mu k^2)).
 apply CSeries_RtoC_impl.
 unfold compose. rewrite RtoC_plus, <- RtoC_pow.
 rewrite <- One by trivial.
 apply is_lim_Cseq_ext with (sum_n (fun m => dg k m^2))%C.
 - intros n. apply sum_n_ext. intros m. now rewrite <- RtoC_pow.
 - apply CSeries_correct.
   destruct (ex_series_square (dg k)) as (l & Hl).
   destruct (SortedRoots_exists k lia) as (roots, roots_ok).
   eapply ex_series_Rabs_dg; eauto using Hyp_alt.
   exists (RtoC l).
   apply CSeries_RtoC in Hl.
   revert Hl. apply is_lim_Cseq_ext. intros n. apply sum_n_ext.
   intros m. unfold compose. now rewrite RtoC_pow.
Qed.

Lemma One_le k : (1<k)%nat -> ThePoly_SndRootsLt1 k ->
  forall n, sum_n (fun n => (dg k n)^2) n <= 1 + mu k^2.
Proof.
 intros Hk Hyp.
 apply pos_series_pos_sum.
 2:{ intros n. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
 rewrite <- One' by trivial.
 apply Series_correct.
 apply (ex_series_square (dg k)).
 destruct (SortedRoots_exists k lia) as (roots, roots_ok).
 eapply ex_series_Rabs_dg; eauto using Hyp_alt.
Qed.

Definition coef0 (k:nat) : R := k*(k+1)*(2*k+1)/6 + k+1.
Definition coef1 (k:nat) : R := -2*((k-1)*k*(k+1)/3 + k+2).
Definition coef2 (k:nat) : R := (k-1)*k*(2*k-1)/6 + k+1.

Lemma One_aux_eqn k m : (3<=k)%nat ->
 sum_n (fun n => (if n=?0 then 1 else df k n - m * df k (n-1))^ 2) (2*(k-1))
 - 1 - m^2
 = coef2 k * m^2 + coef1 k * m + coef0 k.
Proof.
 intros K.
 unfold sum_n.
 rewrite sum_n_m_Chasles with (m:=O); try lia.
 rewrite sum_n_n. change plus with Rplus.
 change (if 0=?0 then _ else _) with 1.
 replace (1^2) with 1 by lra.
 apply Rplus_eq_reg_l with (m^2). ring_simplify.
 rewrite sum_n_m_ext_loc with
  (b:=fun n => m^2 * (df k (n-1))^2 + (-2 * m)*(df k n * df k (n-1)) + df k n^2).
 2:{ intros k' Hk'. case Nat.eqb_spec; try lia. intros _. fixeq R. ring. }
 repeat rewrite (sum_n_m_plus (G:=R_AbelianMonoid)). change plus with Rplus.
 f_equal;[f_equal|].
 { rewrite (sum_n_m_mult_l (K:=R_Ring)). change mult with Rmult.
   rewrite <- (Rmult_1_r (m^2)) at 3. rewrite <- Rmult_plus_distr_l.
   f_equal.
   rewrite sum_n_m_Chasles with (m:=k); try lia. change plus with Rplus.
   replace k with (S (k-1)) at 1 by lia.
   rewrite sum_n_Sm by lia.
   rewrite sum_n_m_ext_loc with (b:=fun _ => 1).
   2:{ intros k' K'. rewrite df_1. simpl; lra. lia. }
   rewrite sum_n_m_const.
   replace (S (k-1) - 1)%nat with (k-1)%nat by lia. rewrite Rmult_1_r.
   rewrite df_2 by lia. simpl INR.
   replace ((1+1)^2) with 4 by lra.
   rewrite sum_n_m_ext_loc with (b:=fun m =>(m-(k-1))%nat^2).
   2:{ intros k' K'. rewrite df_lin, minus_INR by lia.
       f_equal. replace (S (k'-1)) with k' by lia.
       now rewrite !minus_INR by lia. }
   rewrite (sum_n_m_shift (G:=R_AbelianMonoid)) with (a:=fun k=>k^2) by lia.
   replace (S k-(k-1))%nat with 2%nat by lia.
   replace (2*(k-1)-(k-1))%nat with (k-1)%nat by lia.
   rewrite (sum_n_m_sum_n (G:=R_AbelianGroup)) by lia.
   change minus with Rminus. rewrite sum_square.
   rewrite sum_Sn, sum_O. simpl. change plus with Rplus. unfold coef2.
   rewrite minus_INR by lia. simpl. field. }
 { rewrite (sum_n_m_mult_l (K:=R_Ring)). change mult with Rmult.
   unfold coef1. rewrite (Rmult_comm _ m), Rmult_assoc.
   f_equal. f_equal.
   rewrite sum_n_m_Chasles with (m:=k); try lia. change plus with Rplus.
   replace k with (S (k-1)) at 1 by lia.
   rewrite sum_n_Sm by lia.
   replace (k-1)%nat with (S (k-2)) at 1 by lia. rewrite sum_n_Sm by lia.
   rewrite sum_n_m_ext_loc with (b:=fun _ => 1).
   2:{ intros k' K'. rewrite !df_1. simpl; lra. lia. lia. }
   rewrite sum_n_m_const.
   replace (S (k-2) - 1)%nat with (k-2)%nat by lia. rewrite Rmult_1_r.
   rewrite df_2 by lia. simpl INR.
   rewrite df_1 by lia. simpl INR.
   rewrite df_2 by lia. simpl INR.
   rewrite df_2 by lia. simpl INR.
   replace (1+1) with 2 by lra. change plus with Rplus.
   rewrite minus_INR by lia. simpl INR.
   rewrite sum_n_m_ext_loc with (b:=fun m =>(m-(k-1))%nat^2+(m-(k-1))%nat).
   2:{ intros k' K'. rewrite !df_lin by lia.
       replace (S (k'-1) - (k-1))%nat with (k'-(k-1))%nat by lia.
       replace (S k'-(k-1))%nat with (S (k'-(k-1)))%nat by lia.
       rewrite S_INR. lra. }
   rewrite (sum_n_m_shift (G:=R_AbelianMonoid)) with (a:=fun m=>m^2+m) by lia.
   rewrite (sum_n_m_plus (G:=R_AbelianMonoid)). change plus with Rplus.
   replace (2*_-_)%nat with (k-1)%nat by lia.
   replace (S k-(k-1))%nat with 2%nat by lia.
   repeat rewrite (sum_n_m_sum_n (G:=R_AbelianGroup)) by lia.
   change minus with Rminus. rewrite sum_square, sum_INR.
   rewrite !sum_Sn, !sum_O. simpl. change plus with Rplus.
   rewrite minus_INR by lia. simpl. field. }
 { rewrite sum_n_m_Chasles with (m:=(k-1)%nat); try lia.
   change plus with Rplus.
   replace (k-1)%nat with (S (k-2))%nat at 1 by lia. rewrite sum_n_Sm by lia.
   rewrite sum_n_m_ext_loc with (b:=fun _ => 1).
   2:{ intros k' K'. rewrite df_1. simpl; lra. lia. }
   rewrite sum_n_m_const.
   replace (S (k-2)) with (k-1)%nat by lia. change plus with Rplus.
   rewrite Rmult_1_r. rewrite minus_INR by lia. simpl INR.
   rewrite df_2; try lia. rewrite (INR_IZR_INZ 2). simpl IZR.
   replace (2^2) with 4 by lra.
   rewrite sum_n_m_ext_loc with (b:=fun m =>(m-(k-2))%nat^2).
   2:{ intros k' K'. rewrite df_lin, minus_INR; try lia. f_equal.
       rewrite !minus_INR; try lia. rewrite S_INR. simpl. lra. }
   rewrite (sum_n_m_shift (G:=R_AbelianMonoid)) with (a:=fun m=>m^2).
   2:lia.
   replace (S (k-1) - (k-2))%nat with 2%nat by lia.
   replace (2*(k-1) - (k-2))%nat with k by lia.
   rewrite (sum_n_m_sum_n (G:=R_AbelianGroup)) by lia.
   change minus with Rminus. rewrite !sum_square. simpl.
   unfold coef0. rewrite minus_INR by lia. simpl. field. }
Qed.

Lemma LargeSndRoot_after_6 k : (6<=k)%nat -> ThePoly_ExSndRootGe1 k.
Proof.
 intros K.
 rewrite ThePoly_SndRoots_neg by lia. intros Hyp.
 apply Nat.le_lteq in K. apply or_comm in K. destruct K as [<-|K].
 - assert (H := One_le 6 lia Hyp 12).
   apply Rle_minus in H.
   apply Rle_not_gt in H. apply H. clear H.
   unfold sum_n, sum_n_m, Iter.iter_nat. cbn -[pow]. ring_simplify.
   unfold Rminus. rewrite Ropp_mult_distr_l.
   apply Rlt_gt.
   apply discriminant_neg; lra.
 - red in K.
   assert (H := One_le k lia Hyp (2*(k-1))).
   assert (H' : 0 < coef2 k * mu k^2 + coef1 k * mu k + coef0 k).
   { apply le_INR in K. rewrite (INR_IZR_INZ 7) in K. simpl in K.
     apply discriminant_neg.
     - unfold coef2. nra.
     - apply Rminus_gt_0_lt. unfold coef0, coef1, coef2.
       field_simplify. nra. }
   rewrite <- (One_aux_eqn k (mu k)) in H' by lia. unfold dg in H. lra.
Qed.

(* ThePoly can be factorized in Z when k = 5 mod 6,
   one factor being (X^2-X+1)=(X-Cexp(PI/3))(X-Cexp(-PI/3)), ie
   roots of modulus 1, while the minimal polynomial of mu is the other
   factor, with secondary secondary roots of modulus >1 only when k<>5.
   For instance (ThePoly 5) = X^5-X^4-1 = (X^2-X+1)(X^3-X-1).
   Note that for k = 5 mod 6, RevPoly is also divided by (X^2-X+1).
   For instance (RevPoly 5) = X^5+X-1 = (X^2-X+1)(X^3+X^2-1).
   When considering f:=ThePoly/RevPoly, for k = 5 mod 6
   we can factor away the apparent poles (Cexp (+/-PI/3)) of f,
   and f is continuously prolongeable on the unit circle.
*)

Open Scope C.

Lemma ThePoly_root_mod1_carac k z :
  Root z (ThePoly k) -> Cmod z = 1%R -> z^2 = z-1.
Proof.
 intros Hz Hz'.
 apply ThePoly_root_eqn in Hz.
 assert (E := f_equal Cmod Hz).
 rewrite Cmod_1, Cmod_mult, Cmod_pow, Hz', pow1, Rmult_1_l in E.
 assert (E' : (Cmod (z-1)^2 = 1)%R) by (rewrite E; ring).
 assert (Hz2 : (Cmod z^2 = 1)%R) by (rewrite Hz'; ring).
 rewrite Cmod2_alt in E', Hz2.
 destruct z as (x,y); simpl Im in *; simpl Re in *.
 rewrite Ropp_0, Rplus_0_r in E'.
 simpl in E'. ring_simplify in E'.
 assert (Hx : (x = 1/2)%R) by nra.
 assert (Hy : (y^2 = 3/4)%R) by nra.
 simpl. unfold Cmult; simpl.
 replace ((x,y)-1) with (x-1,y)%R by lca. f_equal; nra.
Qed.

Lemma CexpPI3_carac z :
  z^2 = z-1 <-> z = Cexp (PI/3) \/ z = Cexp (-PI/3).
Proof.
 assert (E : z^2-z+1 = (z-Cexp(PI/3))*(z-Cexp(-PI/3))).
 { symmetry. apply Cminus_eq_0. ring_simplify.
   rewrite <- Cexp_add. replace (PI / 3 + - PI / 3)%R with 0%R by lra.
   rewrite Cexp_0. ring_simplify.
   rewrite <- Cmult_plus_distr_l.
   rewrite Ropp_div, <- Cexp_conj_neg, re_alt'. simpl. rewrite cos_PI3.
   lca. }
 split.
 - intros Hz. apply Cminus_diag in Hz.
   replace (z^2-(z-1)) with (z^2-z+1) in Hz by ring. rewrite E in Hz.
   apply Cmult_integral in Hz.
   destruct Hz as [Hz|Hz]; [left|right]; now apply Cminus_eq_0.
 - intros [Hz|Hz]; apply Cminus_eq_0.
   + replace (z^2-(z-1)) with (z^2-z+1) by ring. rewrite E, <- Hz. ring.
   + replace (z^2-(z-1)) with (z^2-z+1) by ring. rewrite E, <- Hz. ring.
Qed.

Lemma CexpPI3_root_carac k :
  Root (Cexp (PI/3)) (ThePoly k) <-> (k mod 6 = 5)%nat.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { simpl. split; try easy. intros R. destruct (ThePoly_0_NoRoot _ R). }
 rewrite ThePoly_root_carac, Ceq_minus.
 replace (Cexp (PI / 3) ^ k - (Cexp (PI / 3) ^ (k-1) + 1)) with
   (Cexp (PI/3) ^ (k-1) * (Cexp (PI/3) - 1) - 1).
 2:{ replace k with (S (k-1)) at 2 by lia. simpl. ring. }
 rewrite <- Ceq_minus.
 rewrite Cexp_pow, Rmult_comm.
 replace (Cexp (PI/3) - 1) with (Cexp (2*(PI/3))).
 2:{ unfold Cexp. rewrite cos_PI3, cos_2PI3, sin_PI3, sin_2PI3.
     unfold Cminus, Cplus. simpl. f_equal; lra. }
 rewrite <- Cexp_add , <- Rmult_plus_distr_r.
 change 2 with (INR 2). rewrite <- plus_INR.
 replace (k-1+2)%nat with (k+1)%nat by lia.
 rewrite (Nat.div_mod_eq (k+1) 6).
 set (q := ((k+1)/6)%nat).
 set (r := ((k+1) mod 6)%nat). rewrite plus_INR, mult_INR.
 rewrite Rmult_plus_distr_r, Cexp_add, INR_IZR_INZ. simpl IZR.
 replace (6 * _ * _)%R with (IZR (2*Z.of_nat q) * PI)%R.
 2:{ rewrite mult_IZR, <-INR_IZR_INZ. field. }
 rewrite Cexp_2nPI, Cmult_1_l.
 split.
 - destruct (Nat.lt_ge_cases r 3) as [Hr|Hr].
   + destruct r as [|[|[|[|] ] ] ] eqn:E; try lia; clear Hr;
     rewrite INR_IZR_INZ; simpl IZR.
     * intros _.
       assert (E' := Nat.div_mod_eq (k+1) 6). fold q in E'.
       fold r in E'. rewrite E, Nat.add_0_r in E'.
       destruct q as [|q]. lia. replace k with (5+q*6)%nat by lia.
       now rewrite Nat.mod_add by lia.
     * rewrite Rmult_1_l. intros [= H _]. rewrite cos_PI3 in H. lra.
     * intros [= H _]. rewrite cos_2PI3 in H. lra.
   + replace (r * (PI/3))%R with (PI + (r-3)*(PI/3))%R by field.
     rewrite Cexp_add, Cexp_PI.
     replace 3 with (INR 3) at 1 by now rewrite INR_IZR_INZ.
     rewrite <- minus_INR by lia.
     assert (Hr' : (r-3 < 3)%nat)
       by (generalize (Nat.mod_upper_bound (k+1) 6); lia).
     destruct (r-3)%nat as [|[|[|[|] ] ] ]; try lia; clear Hr Hr';
     rewrite INR_IZR_INZ; simpl IZR.
     * rewrite Rmult_0_l, Cexp_0. intros [= H]. lra.
     * rewrite Rmult_1_l. intros [= H _]. rewrite cos_PI3 in H. lra.
     * intros [= H _]. rewrite cos_2PI3 in H. lra.
 - intros K'. unfold r. rewrite <- Nat.add_mod_idemp_l, K' by lia.
   simpl. now rewrite Rmult_0_l, Cexp_0.
Qed.

(** Now, let us prove that ThePoly have a secondary root
    of modulus > 1 when 6<=k.
    NB: actually, k=5 is the only situation where (mu k) is Pisot
    while ThePoly has secondary roots of modulus >= 1.
*)

Definition ThePoly_SndRootsLe1 k :=
  forall x, Root x (ThePoly k) -> x <> mu k -> Cmod x <= 1.

Definition ThePoly_ExSndRootGt1 k :=
  exists x, Root x (ThePoly k) /\ x <> mu k /\ 1 < Cmod x.

Lemma ThePoly_SndRoots_neg' k :
  k<>O -> ThePoly_ExSndRootGt1 k <-> ~ThePoly_SndRootsLe1 k.
Proof.
 intros K. split.
 - intros (x & Hx & N & LE) H. specialize (H x Hx N). lra.
 - unfold ThePoly_ExSndRootGt1, ThePoly_SndRootsLe1. intros H.
   destruct (SortedRoots_exists k K) as (l & Hl).
   assert (H1 := SortedRoots_length k l Hl).
   assert (H2 := SortedRoots_roots k l Hl).
   assert (H3 := SortedRoots_mu k l Hl).
   destruct (Nat.eq_dec k 1) as [->|K1].
   { destruct H. intros r. rewrite <- H2. destruct l as [|r' [|] ]; try easy.
     rewrite <- H3. unfold Cnth. simpl. intuition. }
   assert (l @ 1 <> mu k).
   { rewrite <- H3. intro E.
     destruct Hl as (_,Hl). apply Csorted_alt in Hl.
     rewrite StronglySorted_nth in Hl. specialize (Hl 0%nat 1%nat lia).
     rewrite E in Hl. revert Hl. apply Cgt_order. }
   exists (l @ 1); repeat split; trivial.
   * rewrite <- H2. apply nth_In; lia.
   * apply Rnot_le_lt. intros H4. apply H.
     intros r Hr Hr'. rewrite <- H2 in Hr.
     eapply Rle_trans; [ | apply H4 ].
     apply SortedRoots_Cmod_sorted in Hl.
     rewrite StronglySorted_nth in Hl.
     destruct (In_nth l r 0 Hr) as (i & Hi & <-).
     change (nth i l 0) with (l @ i) in *.
     destruct i as [|[|i] ]; try lra. intuition.
     apply Rge_le, Hl. lia.
Qed.

(** First, when there is no root of modulus 1 at all, we're easily done *)

Lemma LargerSndRoot_after_6_easy k :
  (6<=k)%nat -> (k mod 6 <> 5)%nat -> ThePoly_ExSndRootGt1 k.
Proof.
 intros K K'.
 destruct (LargeSndRoot_after_6 k K) as (r & R & N & Ge).
 exists r; repeat split; trivial. destruct Ge as [Gt|E]; trivial. exfalso.
 symmetry in E. assert (E' := ThePoly_root_mod1_carac k r R E).
 apply CexpPI3_carac in E'. destruct E' as [-> | ->].
 - apply CexpPI3_root_carac in R; lia.
 - replace (-PI/3)%R with (-(PI/3))%R in R by field.
   rewrite <- Cexp_conj_neg in R. apply root_conj in R.
   rewrite Cconj_involutive in R.
   apply CexpPI3_root_carac in R; lia.
Qed.

(** Now, we focus on the situation with roots of modulus 1 *)

Section HandlingModulusOne.
Variable k : nat.
Hypothesis K : (6<=k)%nat.
Hypothesis K' : (k mod 6 = 5)%nat.
Hypothesis Hyp : ThePoly_SndRootsLe1 k.
(* And from Hyp we prove False now *)
Variable roots : list C.
Hypothesis roots_ok : SortedRoots k roots.

Lemma roots_0 : roots@0 = mu k.
Proof.
 apply (SortedRoots_mu k roots roots_ok).
Qed.

Lemma Hyp_alt' :
 forall r, In r (tl roots) -> Cmod r <= 1.
Proof.
 intros r R.
 assert (L := SortedRoots_length _ _ roots_ok).
 assert (ND := SortedRoots_nodup _ _ roots_ok).
 apply Hyp.
 - rewrite <-(SortedRoots_roots _ _ roots_ok).
   destruct roots. apply R. now right.
 - rewrite <- roots_0. destruct roots; simpl in *; try easy.
   unfold Cnth. simpl. inversion_clear ND. contradict H. now subst.
Qed.

Lemma roots_layout :
  roots@1 = Cexp (PI/3) /\
  roots@2 = Cexp (-PI/3) /\
  forall i, (3<=i<k)%nat -> Cmod (roots@i) < 1.
Proof.
  destruct (SortedRoots_im_pos k roots roots_ok 0 lia) as (Im1 & Im2).
  simpl in Im1,Im2.
  destruct (second_best_root k roots lia roots_ok) as (_ & LT & H).
  assert (IN : In (Cexp (PI/3)) roots).
  { now apply (SortedRoots_roots k roots roots_ok), CexpPI3_root_carac. }
  apply In_nth with (d:=0) in IN. destruct IN as (n & N & E).
  change (roots@n = Cexp (PI/3)) in E.
  destruct (Nat.eq_dec n 0) as [->|N0].
  { exfalso. rewrite roots_0 in E. apply (f_equal Cmod) in E.
    rewrite Cmod_Cexp in E.
    assert (T := mu_itvl k). rewrite Cmod_R, Rabs_right in E; lra. }
  destruct (Nat.eq_dec n 2) as [->|N2].
  { exfalso. rewrite E in Im2.
    rewrite <- (Cconj_involutive (Cexp (PI/3))) in Im2.
    apply Cconj_simplify in Im2. rewrite <- Im2 in Im1.
    simpl in Im1. rewrite sin_PI3 in Im1. generalize Rlt_sqrt3_0; lra. }
  destruct (Nat.le_gt_cases 3 n).
  { exfalso.
    assert (L := SortedRoots_length _ _ roots_ok).
    specialize (H n lia). rewrite E, Cmod_Cexp in H.
    assert (Cmod (roots @ 1) <= 1); try lra.
    { apply Hyp. apply (SortedRoots_roots _ _ roots_ok). apply nth_In; lia.
      rewrite <- roots_0.
      destruct roots_ok as (_,R). apply Csorted_alt in R.
      rewrite StronglySorted_nth in R. specialize (R 0%nat 1%nat lia).
      intros E'. rewrite E' in R. revert R. apply Cgt_order. }}
  replace n with 1%nat in * by lia. repeat split; trivial.
  - rewrite Im2, E, Cexp_conj_neg. f_equal. field.
  - intros i Hi. specialize (H i Hi). rewrite E, Cmod_Cexp in LT. lra.
Qed.

Lemma roots_1 : roots@1 = Cexp (PI/3).
Proof.
 apply roots_layout.
Qed.

Lemma roots_2 : roots@2 = Cexp (-PI/3).
Proof.
 apply roots_layout.
Qed.

Lemma roots_other i : (i<k)%nat -> (3<=i)%nat <-> Cmod (roots@i) < 1.
Proof.
 intros Hi. split.
 - intros Hi'. apply roots_layout; lia.
 - intros H.
   destruct (Nat.eq_dec i 0) as [->|N0].
   { rewrite roots_0 in H.
     assert (T := mu_itvl k). rewrite Cmod_R, Rabs_right in H; lra. }
   destruct (Nat.eq_dec i 1) as [->|N1].
   { rewrite roots_1, Cmod_Cexp in H. lra. }
   destruct (Nat.eq_dec i 2) as [->|N2].
   { rewrite roots_2, Cmod_Cexp in H. lra. }
   lia.
Qed.

Lemma skipn_3_roots_spec r :
 In r (skipn 3 roots) <-> In r roots /\ Cmod r < 1.
Proof.
 assert (L := SortedRoots_length _ _ roots_ok).
 split.
 - intros IN. apply In_nth with (d:=0) in IN.
   destruct IN as (n & N & <-).
   rewrite skipn_length, L in N.
   rewrite nth_skipn. split.
   + apply nth_In; lia.
   + apply roots_other; lia.
 - intros (IN,LT). apply In_nth with (d:=0) in IN.
   destruct IN as (n & N & <-).
   apply roots_other in LT; try lia.
   replace n with (3+(n-3))%nat by lia. rewrite <- nth_skipn.
   apply nth_In. rewrite skipn_length. lia.
Qed.

Definition rootrest := roots@0 :: skipn 3 roots.

Lemma rootrest_spec r : In r rootrest <-> In r roots /\ Cmod r <> 1%R.
Proof.
 assert (L := SortedRoots_length _ _ roots_ok).
 change (In r rootrest) with (roots @ 0 = r \/ In r (skipn 3 roots)).
 rewrite skipn_3_roots_spec. split.
 - intros [<- | (IN,LT)].
   + split. apply nth_In; lia. rewrite roots_0.
     assert (T := mu_itvl k). rewrite Cmod_R, Rabs_right; lra.
   + split; trivial; lra.
 - intros (IN,NE). destruct (Rle_lt_dec (Cmod r) 1%R).
   + right; split; trivial; lra.
   + left. rewrite roots_0.
     destruct (Ceq_dec r (mu k)) as [E|N]; try easy.
     rewrite (SortedRoots_roots _ _ roots_ok) in IN.
     specialize (Hyp r IN N). lra.
Qed.

Lemma rootrest_perm : Permutation roots (Cexp (PI/3)::Cexp(-PI/3)::rootrest).
Proof.
 assert (L := SortedRoots_length _ _ roots_ok).
 unfold rootrest. rewrite <- roots_1, <- roots_2.
 destruct roots as [|a [|b [|c l] ] ]; unfold Cnth; simpl in *; try lia.
 eapply perm_trans. apply perm_swap. apply perm_skip. apply perm_swap.
Qed.

Definition TheRest := linfactors rootrest.
Definition RevRest := revfactors rootrest.

Definition fbis x := Peval TheRest x / Peval RevRest x.
Definition gbis x :=
 (-mu k) * Peval TheRest x / Peval (revfactors (tl rootrest)) x.

Lemma RevRest_alt x :
  Peval RevRest x = (x - tau k) * Peval (revfactors (tl rootrest)) x.
Proof.
 unfold RevRest, revfactors, rootrest.
 set (l := skipn 3 roots).
 simpl. rewrite Pmult_eval, cons_eval, Pconst_eval.
 rewrite roots_0. unfold tau. rewrite RtoC_inv. ring.
Qed.

Lemma gbis_alt (x:C) : x<>tau k -> gbis x = (1 - mu k * x) * fbis x.
Proof.
 intros Hx. unfold gbis, fbis, Cdiv.
 rewrite RevRest_alt, Cinv_mult. unfold tau in *. rewrite RtoC_inv in *.
 rewrite !Cmult_assoc. f_equal.
 rewrite <- !Cmult_assoc, (Cmult_comm (Peval _ _)), !Cmult_assoc. f_equal.
 field. simpl. split.
 - intros [=E]. generalize (mu_pos k); lra.
 - rewrite <- Ceq_minus. contradict Hx. now apply Cinv_eq.
Qed.

Lemma fbis_f x :
 x <> Cexp (PI/3) /\ x <> Cexp (-PI/3) -> fbis x = f k x.
Proof.
 intros H.
 unfold fbis, f, TheRest, RevRest. rewrite <- ThePoly_eval, <- RevPoly_eval.
 rewrite (proj1 roots_ok).
 rewrite (RevPoly_alt k lia roots roots_ok).
 rewrite (linfactors_perm _ _ rootrest_perm).
 rewrite (linfactors_perm _ _ (Permutation_map Cinv rootrest_perm)).
 cbn -[rootrest linfactors]. rewrite <- !Cexp_neg.
 replace (- (PI/3))%R with (-PI/3)%R by field.
 replace (- (-PI/3))%R with (PI/3)%R by field.
 remember rootrest as l.
 set (r1 := Cexp (PI/3)) in *.
 set (r2 := Cexp (-PI/3)) in *.
 simpl. unfold Cdiv. rewrite !Pmult_eval, !Cinv_mult.
 rewrite !cons_eval. change (Peval [] x) with 0.
 rewrite !Cmult_0_r, !Cplus_0_r, !Cmult_1_r.
 rewrite <- !Cmult_assoc. rewrite (Cmult_comm (/ (Peval _ _))).
 rewrite !Cmult_assoc. f_equal.
 rewrite <- (Cmult_1_r (Peval (linfactors l) x)) at 1.
 rewrite <- !Cmult_assoc. f_equal. field. split.
 - rewrite Cplus_comm. change (x-r2<>0). now rewrite <- Ceq_minus.
 - rewrite Cplus_comm. change (x-r1<>0). now rewrite <- Ceq_minus.
Qed.

Lemma gbis_g (x:C) :
 x <> tau k /\ x <> Cexp (PI/3) /\ x <> Cexp (-PI/3) -> gbis x = g k x.
Proof.
 intros (Hx,Hx'). rewrite gbis_alt; trivial.
 unfold g. now rewrite fbis_f.
Qed.

Lemma RevRest_carac x :
  x <> 0 -> Peval RevRest (/x) = - Peval TheRest x / x^(k-2).
Proof.
 intros Hx.
 unfold RevRest, TheRest.
 rewrite (Reciprocal_gen rootrest x); trivial.
 2:{ rewrite rootrest_spec. intros (IN, _).
     apply (SortedRoots_roots _ _ roots_ok) in IN.
     now apply root_nz in IN. }
 f_equal.
 2:{ f_equal. unfold rootrest.
     change (length _) with (S (length (skipn 3 roots))).
     rewrite skipn_length.
     rewrite (SortedRoots_length _ _ roots_ok). lia. }
 replace (- _) with (-1 * Peval (linfactors rootrest) x) by lca.
 f_equal.
 replace (RtoC (-1)) with (Peval (RevPoly k) 0).
 2:{ rewrite RevPoly_eval. replace k with (S (k-1)) by lia. simpl. lca. }
 rewrite (RevPoly_alt k lia roots roots_ok).
 rewrite (linfactors_perm _ _ (Permutation_map Cinv rootrest_perm)).
 cbn -[rootrest linfactors]. rewrite <- !Cexp_neg.
 remember rootrest as l. unfold revfactors.
 simpl. rewrite !Pmult_eval.
 rewrite !cons_eval. change (Peval [] _) with 0. ring_simplify.
 rewrite <- Cmult_assoc, <- Cexp_add.
 replace (Rplus _ _) with R0 by lra.
 change R0 with 0%R. rewrite Cexp_0. lca.
Qed.

Lemma ffbis x : x <> 0 ->
  ~ Root x TheRest -> ~ Root (/x) TheRest -> fbis x * fbis (/ x) = 1.
Proof.
 intros X0 X1 X2. unfold fbis.
 rewrite RevRest_carac; trivial.
 rewrite <- (Cinv_inv x) at 2.
 rewrite RevRest_carac, Cpow_inv by now apply nonzero_div_nonzero.
 field. repeat split; trivial. now apply Cpow_nonzero.
Qed.

Lemma ggbis x : Cmod x = 1%R ->
  gbis x * gbis (/ x) = (1-mu k * x)*(1-mu k * /x).
Proof.
 intros X. rewrite !gbis_alt.
 2:{ intros E. apply (f_equal Cmod) in E.
     assert (T := tau_itvl k).
     rewrite Cmod_inv, X, Rinv_1, Cmod_R, Rabs_pos_eq in E; lra. }
 2:{ intros E. apply (f_equal Cmod) in E.
     assert (T := tau_itvl k).
     rewrite Cmod_R, Rabs_pos_eq in E; lra. }
 rewrite (Cmult_comm _ (fbis (/x))).
 rewrite Cmult_assoc, <- (Cmult_assoc _ (fbis x)), ffbis. ring.
 - intros ->. rewrite Cmod_0 in X. lra.
 - unfold TheRest. rewrite <- linfactors_roots, rootrest_spec. lra.
 - unfold TheRest. rewrite <- linfactors_roots, rootrest_spec.
   apply (f_equal Rinv) in X. rewrite Rinv_1 in X.
   rewrite Cmod_inv. lra.
Qed.

(** Showing that gbis has a power series decomposition on the whole
    unit circle. The coefficients [dgbis] are quite complex, but we will
    equate them with coefficients [dg] thanks to powerseries unicity. *)

Definition pseries_multfactor c (a:nat->C) :=
 fun n => if n =? 0 then -c * a O else a (n-1)%nat - c * a n.

Lemma is_CPowerSeries_multfactor (c:C) (a:nat->C) x l :
  is_CPowerSeries a x l ->
  is_CPowerSeries (pseries_multfactor c a) x ((x-c)*l).
Proof.
 intros H.
 unfold pseries_multfactor.
 apply is_lim_Cseq_ext with
  (f:=fun n => sum_n (fun k => (delay a 1 k) * x^k) n -
               c * sum_n (fun k => a k * x^k) n).
 { intros n. rewrite <- sum_n_Cmult_l, sum_n_minus. apply sum_n_ext.
   clear n. intros n. unfold delay.
   case Nat.eqb_spec; case Nat.ltb_spec; try lia.
   - intros _ ->. simpl. change zero with C0. lca.
   - intros _ N. fixeq C. ring. }
 replace ((x-c)*l) with (x^1*l-c*l) by ring.
 apply is_lim_Cseq_minus.
 - now apply delay_powerseries.
 - apply is_lim_Cseq_mult; trivial. apply is_lim_Cseq_const.
Qed.

Definition pseries_linfactors := fold_right pseries_multfactor.

Lemma ex_series_multfactor c a :
  ex_series (Cmod ∘ a) -> ex_series (Cmod ∘ (pseries_multfactor c a)).
Proof.
 intros (l,H).
 unfold pseries_multfactor, compose.
 apply (ex_series_le (V:=R_CNM))
   with (fun n => delay (Cmod∘a) 1 n + (Cmod∘a) n * Cmod c)%R.
 { intros n. change norm with Rabs.
   rewrite Rabs_pos_eq by apply Cmod_ge_0.
   unfold delay. case Nat.eqb_spec; case Nat.ltb_spec; try lia; intros.
   - subst. unfold compose. change zero with 0%R.
     rewrite Cmod_mult, Cmod_opp. lra.
   - unfold compose, Cminus. eapply Rle_trans; [apply Cmod_triangle| ].
     rewrite Cmod_opp, Cmod_mult. lra. }
 apply (ex_series_plus (V:=R_CNM)).
 - exists l. now apply delay_series_R.
 - apply ex_series_scal_r. now exists l.
Qed.

Lemma ex_series_linfactors a l :
  ex_series (Cmod ∘ a) ->
  ex_series (Cmod ∘ pseries_linfactors a l).
Proof.
 induction l; simpl; trivial. intros. now apply ex_series_multfactor, IHl.
Qed.

Lemma is_CPowerSeries_linfactors (a:nat->C) l x lim :
  is_CPowerSeries a x lim ->
  is_CPowerSeries (pseries_linfactors a l) x ((Peval (linfactors l) x) * lim).
Proof.
 induction l as [|c l IH]; simpl.
 - now rewrite Pconst_eval, Cmult_1_l.
 - intros H. rewrite Pmult_eval, cons_eval, Pconst_eval, Cmult_1_r.
   rewrite Cplus_comm, (Cmult_comm _ (x+-c)), <- Cmult_assoc.
   now apply is_CPowerSeries_multfactor, IH.
Qed.

Definition dhbis n :=
  let l := map Cinv (tl rootrest) in
  - mu k * big_sum (fun i => - PartFrac.coef l i * (/ l@i)^S n) (k-3).

Definition dgbis := pseries_linfactors dhbis rootrest.

Lemma ex_series_Cmod_dhbis : ex_series (Cmod ∘ dhbis).
Proof.
 unfold dhbis.
 set (l := map Cinv (tl rootrest)). unfold compose.
 eapply ex_series_ext.
 { intros n. symmetry. rewrite Cmod_mult, Rmult_comm. reflexivity. }
 apply ex_series_scal_r.
 apply (ex_series_le (V:=R_CNM)) with
  (b:=fun n =>
        big_sum (fun i => Cmod (-PartFrac.coef l i * (/l@i)^S n)) (k-3)).
 { intros n. unfold compose. change norm with Rabs.
   rewrite Rabs_pos_eq by apply Cmod_ge_0. apply Cmod_bigsum. }
 apply ex_series_bigsum.
 intros i Hi.
 eapply ex_series_ext.
 { intros n. symmetry. rewrite Cpow_S, Cmult_assoc, Cmod_mult, Rmult_comm.
   rewrite Cmod_pow. reflexivity. }
 apply ex_series_scal_r.
 apply ex_series_geom.
 rewrite Rabs_pos_eq by apply Cmod_ge_0.
 unfold l.
 unfold Cnth.
 assert (L : (length (tl rootrest) = k-3)%nat).
 { unfold rootrest. cbn -[skipn]. rewrite skipn_length.
   rewrite (SortedRoots_length _ _ roots_ok). lia. }
 rewrite nth_map_indep with (d':=0), Cinv_inv by lia.
 fold ((tl rootrest)@i).
 set (r := (tl rootrest)@i).
 assert (IN : In r (skipn 3 roots)).
 { unfold r. change (skipn 3 roots) with (tl rootrest).
   apply nth_In. lia. }
 rewrite skipn_3_roots_spec in IN. apply IN.
Qed.

Lemma hbis_is_powerseries (x:C) :
  Cmod x <= 1 ->
  is_CPowerSeries dhbis x ((-mu k) / Peval (revfactors (tl rootrest)) x).
Proof.
 intros Hx.
 unfold dhbis. unfold Cdiv.
 eapply is_lim_Cseq_ext.
 { symmetry. erewrite sum_n_ext; [|intro k'; symmetry; apply Cmult_assoc].
   apply sum_n_Cmult_l. }
 apply is_lim_Cseq_mult; [apply is_lim_Cseq_const| ].
 eapply is_lim_Cseq_ext.
 { symmetry. apply sum_n_big_sum_adhoc. }
 cbn -[rootrest sum_n Cpow].
 unfold revfactors.
 assert (L : (length (tl rootrest) = k-3)%nat).
 { unfold rootrest. cbn -[skipn]. rewrite skipn_length.
   rewrite (SortedRoots_length _ _ roots_ok). lia. }
 rewrite PartFrac.inv_linfactors, map_length.
 2:{ intros E. apply (f_equal (@length _)) in E.
     rewrite map_length, L in E. simpl in E. lia. }
 2:{ apply FinFun.Injective_map_NoDup.
     - intros a b E. now rewrite <- (Cinv_inv a), E, Cinv_inv.
     - unfold rootrest. cbn -[skipn]. apply skipn_nodup.
       apply (SortedRoots_nodup _ _ roots_ok). }
 2:{ unfold rootrest. cbn -[skipn]. rewrite in_map_iff.
     intros (y & <- & IN). rewrite skipn_3_roots_spec in IN.
     rewrite Cmod_inv in Hx.
     apply Rmult_le_compat_l with (r:=Cmod y) in Hx; try apply Cmod_ge_0.
     rewrite Rinv_r in Hx; try lra.
     assert (Hy : y <> 0).
     { intros ->.
       now apply (root_nz k), (SortedRoots_roots _ _ roots_ok). }
     apply Cmod_gt_0 in Hy. lra. }
 rewrite L.
 apply is_lim_Cseq_bigsum. intros i Hi.
 rewrite <- Copp_minus_distr. unfold Cdiv. rewrite Cinv_Copp.
 rewrite <- Copp_mult_distr_r, Copp_mult_distr_l.
 eapply is_lim_Cseq_ext.
 { symmetry. erewrite sum_n_ext; [|intro k'; symmetry; apply Cmult_assoc].
   apply sum_n_Cmult_l. }
 apply is_lim_Cseq_mult; [apply is_lim_Cseq_const| ].
 unfold Cnth.
 rewrite nth_map_indep with (d':=0), Cinv_inv by lia.
 fold ((tl rootrest)@i).
 set (r := (tl rootrest)@i).
 assert (IN : In r (skipn 3 roots)).
 { unfold r. change (skipn 3 roots) with (tl rootrest).
   apply nth_In. lia. }
 apply is_powerseries_invlin.
 - intros E.
   apply (root_nz k). rewrite <- E.
   rewrite <- (SortedRoots_roots _ _ roots_ok).
   apply skipn_3_roots_spec in IN. apply IN.
 - rewrite Cmod_mult.
   apply skipn_3_roots_spec in IN.
   apply Rle_lt_trans with (Cmod r * 1)%R; try lra.
   apply Rmult_le_compat_l; try lra. apply Cmod_ge_0.
Qed.

Lemma ex_series_Cmod_dgbis : ex_series (Cmod ∘ dgbis).
Proof.
 unfold dgbis. apply ex_series_linfactors, ex_series_Cmod_dhbis.
Qed.

Lemma gbis_is_powerseries (x:C) :
  Cmod x <= 1 -> is_CPowerSeries dgbis x (gbis x).
Proof.
 intros Hx. unfold gbis, dgbis.
 rewrite Cmult_comm. unfold Cdiv. rewrite <- Cmult_assoc.
 apply is_CPowerSeries_linfactors.
 now apply hbis_is_powerseries.
Qed.

Lemma gbis_powerseries (x:C) :
  Cmod x <= 1 -> gbis x = CPowerSeries dgbis x.
Proof.
 intros. symmetry. now apply CPowerSeries_unique, gbis_is_powerseries.
Qed.

Lemma dgbis_dg : forall n, dgbis n = dg k n.
Proof.
 apply CPowerSeries_coef_ext.
 - apply Rbar.Rbar_lt_le_trans with (1%R). simpl; lra. apply CV_radius_ge_1.
   apply ex_series_ext with (a:=Cmod∘dgbis).
   + intros n. symmetry. apply Rabs_pos_eq. apply Cmod_ge_0.
   + apply ex_series_Cmod_dgbis.
 - apply Rbar.Rbar_lt_le_trans with (/2)%R. simpl; lra.
   apply CV_disk_le_radius. red.
   eapply ex_series_ext;
   [|apply (ex_pseries_Rabs_dg k lia roots roots_ok) with (x:=(/2)%R)].
   + intros n. unfold compose. rewrite !Rabs_mult.
     now rewrite Cmod_R, Rabs_Rabsolu.
   + intros r Hr. apply Hyp_alt' in Hr.
     rewrite Cmod_mult, Cmod_R, Rabs_pos_eq; lra.
 - assert (LT : 0 < 1/2) by lra.
   set (e := mkposreal _ LT).
   exists e. intros y Hy. change (Rabs (y-0) < 1/2) in Hy.
   rewrite Rminus_0_r in Hy.
   rewrite <- gbis_powerseries.
   2:{ rewrite Cmod_R. lra. }
   assert (Y : y <> tau k).
   { generalize (tau_itvl k) (Rle_abs y). lra. }
   assert (Y' : RtoC y <> RtoC (tau k)).
   { contradict Y. now injection Y. }
   rewrite <- (g_powerseries k lia roots roots_ok); trivial.
   + apply gbis_g. repeat split; trivial.
     * intros E. apply (f_equal Cmod) in E. rewrite Cmod_R in E.
       rewrite Cmod_Cexp in E. lra.
     * intros E. apply (f_equal Cmod) in E. rewrite Cmod_R in E.
       rewrite Cmod_Cexp in E. lra.
   + intros r R. rewrite Cmod_mult, Cmod_R. apply Hyp_alt' in R.
     apply Rle_lt_trans with (1 * Rabs y)%R; try lra.
     apply Rmult_le_compat_r; trivial using Rabs_pos.
Qed.

Lemma One_again : CSeries (fun n => (dgbis n)^2) = 1 + mu k^2.
Proof.
 rewrite <- (Mu_series_square dgbis gbis).
 { unfold Mu.
   assert (N : C2*PI <> 0).
   { intros E. rewrite <- RtoC_mult in E. apply RtoC_inj in E.
     generalize PI_RGT_0; lra. }
   apply Cmult_eq_reg_l with (C2*PI); trivial.
   rewrite Cmult_assoc, Cinv_r, Cmult_1_l; trivial.
   apply is_CInt_unique.
   apply (is_RInt_ext (V:=C_NM))
    with (f := fun t => 1 + mu k^2 - mu k * (Cexp t - -Cexp (-t))).
   { intros t _.
     rewrite Cexp_neg. rewrite ggbis by now rewrite Cmod_Cexp.
     fixeq C. field. apply Cexp_nonzero. }
   replace (C2*_*_) with (C2*PI*(1+mu k^2) - 0) by ring.
   apply (is_RInt_minus (V:=C_NM)).
   - rewrite <- RtoC_mult.
     replace (RtoC (2*PI)) with (RtoC (2*PI)-0) by ring.
     apply is_CInt_const.
   - replace 0 with ((mu k)*(0-0)) at 1 by ring.
     apply is_CInt_scal, (is_RInt_minus (V:=C_NM)).
     + generalize (is_CInt_Cexp 1 lia). apply is_RInt_ext.
       intros x _. f_equal. now rewrite Rmult_1_l.
     + apply (is_RInt_comp_opp (V:=C_NM)).
       rewrite Ropp_0, Ropp_mult_distr_l.
       generalize (is_CInt_Cexp' 1 lia). apply is_RInt_ext.
       intros x _. f_equal. now rewrite Rmult_1_l. }
 { apply ex_series_Cmod_dgbis. }
 { intros z Hz. apply gbis_powerseries. lra. }
Qed.

Local Open Scope R.

Lemma One_again' : Series (fun n => (dg k n)^2) = 1 + mu k^2.
Proof.
 apply is_series_unique.
 rewrite <- (re_RtoC (1+mu k^2)).
 apply CSeries_RtoC_impl.
 unfold compose. rewrite RtoC_plus, <- RtoC_pow.
 rewrite <- One_again.
 apply is_lim_Cseq_ext with (sum_n (fun k => dgbis k^2))%C.
 - intros n. apply sum_n_ext. intros m. now rewrite <- RtoC_pow, dgbis_dg.
 - apply CSeries_correct. apply ex_series_Cmod.
   apply ex_series_ext with (fun k => (Cmod (dgbis k))^2)%R.
   { intros n. unfold compose. now rewrite Cmod_pow. }
   apply ex_series_square.
   apply ex_series_ext with (Cmod ∘ dgbis).
   { intros n. unfold compose. now rewrite Rabs_pos_eq by apply Cmod_ge_0. }
   apply ex_series_Cmod_dgbis.
Qed.

Lemma One_le_again : forall n, sum_n (fun n => (dg k n)^2) n <= 1 + mu k^2.
Proof.
 apply pos_series_pos_sum.
 2:{ intros n. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
 rewrite <- One_again' by trivial.
 apply Series_correct.
 apply (ex_series_square (dg k)).
 apply ex_series_ext with (Cmod ∘ dgbis).
 { intros n. unfold compose. now rewrite dgbis_dg, Cmod_R. }
 apply ex_series_Cmod_dgbis.
Qed.

Lemma the_contradiction : False.
Proof.
 assert (Hk7 : (7 <= k)%nat).
 { apply Nat.le_lteq in K. destruct K; try lia. subst. easy. }
 assert (H := One_le_again (2*(k-1))).
 assert (H' : 0 < coef2 k * mu k^2 + coef1 k * mu k + coef0 k).
 { apply le_INR in Hk7. rewrite (INR_IZR_INZ 7) in Hk7. simpl in Hk7.
   apply discriminant_neg.
   - unfold coef2. nra.
   - apply Rminus_gt_0_lt. unfold coef0, coef1, coef2.
     field_simplify. nra. }
 rewrite <- (One_aux_eqn k (mu k)) in H' by lia. unfold dg in H. lra.
Qed.

End HandlingModulusOne.

Lemma LargerSndRoot_after_6 k : (6<=k)%nat -> ThePoly_ExSndRootGt1 k.
Proof.
 intros K.
 destruct (Nat.eq_dec (k mod 6) 5) as [K'|K'].
 - rewrite ThePoly_SndRoots_neg' by lia. intros Hyp.
   destruct (SortedRoots_exists k lia) as (roots & roots_ok).
   apply (the_contradiction k K K' Hyp roots roots_ok).
 - apply (LargerSndRoot_after_6_easy k K K').
Qed.

(* The former axiom : *)

Lemma large_second_best_root k roots :
  (6<=k)%nat -> SortedRoots k roots -> 1 < Cmod (roots@1).
Proof.
 intros K roots_ok.
 destruct (LargerSndRoot_after_6 k K) as (r & Hr & N & GT).
 eapply Rlt_le_trans; [ apply GT | ].
 assert (M := SortedRoots_mu _ _ roots_ok).
 rewrite (proj1 roots_ok), <- linfactors_roots in Hr.
 apply SortedRoots_Cmod_sorted in roots_ok.
 rewrite StronglySorted_nth in roots_ok.
 destruct (In_nth roots r 0 Hr) as (i & Hi & <-).
 change (nth i roots 0) with (roots @ i) in *.
 destruct i as [|[|i] ]; try lra. intuition.
 apply Rge_le, roots_ok. lia.
Qed.

(* Print Assumptions large_second_best_root. *)
