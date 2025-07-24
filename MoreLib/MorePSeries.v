From Coq Require Import Lia Reals Lra.
From Coquelicot Require Complex.
From Coquelicot Require Export Lim_seq.
From Coquelicot Require Import Rcomplements Hierarchy Continuity Series PSeries.
From Coquelicot Require Import ElemFct Derive.
Close Scope R. (* Issue with Coquelicot *)
From Hofstadter.HalfQuantum Require Import Complex Polynomial.
Require Import MoreTac MoreList MoreReals MoreComplex MoreSum MorePoly MoreLim.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** Power series on R : More on CV_disk and CV_radius *)

Global Instance CV_radius_proper :
  Proper (pointwise_relation _ eq ==> eq) CV_radius.
Proof.
 intros f f' Hf. apply CV_radius_ext. apply Hf.
Qed.

Lemma CV_disk_rabs a x : CV_disk a x <-> CV_disk a (Rabs x).
Proof.
 unfold CV_disk.
 split; apply ex_series_ext; intros n;
  now rewrite !Rabs_mult, !RPow_abs, Rabs_Rabsolu.
Qed.

Lemma CV_disk_le_radius (a:nat->R) (x:R) :
 CV_disk a x -> Rbar.Rbar_le x (CV_radius a).
Proof.
 intros. now apply Lub_Rbar_ub.
Qed.

Lemma CV_radius_ge_1 (a : nat -> R) :
  ex_series (Rabs∘a) -> Rbar.Rbar_le 1%R (CV_radius a).
Proof.
 intros H. apply CV_disk_le_radius.
 red. srewrite Rabs_mult pow1 (Rabs_pos_eq 1); try lra.
 now srewrite Rmult_1_r.
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

Definition CV_disk' (a : nat -> R) (r : R) :=
 exists r', Rabs r' = r /\ ex_series (fun n => a n * r'^n)%R.

Definition CV_radius' (a : nat -> R) : Rbar.Rbar :=
  Lub.Lub_Rbar (CV_disk' a).

Lemma CV_disk_disk' a r : 0<=r -> CV_disk a r -> CV_disk' a r.
Proof.
 unfold CV_disk, CV_disk'. intros Hr H.
 apply ex_series_Rabs in H. exists r. split; trivial. now apply Rabs_pos_eq.
Qed.

Lemma CV_radius_radius' a : CV_radius a = CV_radius' a.
Proof.
 apply Rbar.Rbar_le_antisym.
 { apply Lub.Lub_Rbar_correct. red.
   intros x Hx. destruct (Rle_lt_dec 0 x).
   - apply Lub_Rbar_ub. now apply CV_disk_disk'.
   - apply Rbar.Rbar_le_trans with (Rbar.Finite 0). simpl; lra.
     apply Lub_Rbar_ub. red. exists 0%R. split. apply Rabs_pos_eq; lra.
     eapply ex_series_ext; [ | exists (a O); apply is_pseries_0 ].
     intros n. simpl. now rewrite Rmult_comm. }
 { apply Lub_Rbar_least.
   intros x (x' & <- & E).
   destruct (Rbar.Rbar_le_lt_dec (Rabs x') (CV_radius a)) as [LE|LT]; trivial.
   exfalso.
   now apply (CV_disk_outside _ _ LT), ex_series_lim_0. }
Qed.

(** Power series on C *)

Local Open Scope C.

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

Lemma is_CPowerSeries_alt a z l : is_CPowerSeries a z l <-> is_pseries a z l.
Proof.
 unfold is_CPowerSeries, is_lim_Cseq.
 change (filterlim _ _ _) with (is_series (fun n => a n * z^n) l).
 unfold is_pseries.
 assert (E : forall n, a n * z ^ n = scal (pow_n z n) (a n)).
 { intros n. change scal with Cmult. change pow_n with Cpow. ring. }
 now setoid_rewrite E.
Qed.

Lemma is_CPowerSeries_ext a b z l :
  (forall n, a n = b n) -> is_CPowerSeries a z l -> is_CPowerSeries b z l.
Proof.
 rewrite !is_CPowerSeries_alt. apply is_pseries_ext.
Qed.

Global Instance is_CPowerSeries_proper :
  Proper (pointwise_relation _ eq ==> eq ==> eq ==> iff) is_CPowerSeries.
Proof.
 intros f f' Hf z z' <- l l' <-. split; apply is_CPowerSeries_ext.
 apply Hf. intros. symmetry. apply Hf.
Qed.

Lemma is_pseries_1 (a : nat -> R) (l : R) :
 is_pseries a 1%R l <-> is_series a l.
Proof.
 unfold is_pseries. change pow_n with pow. change scal with Rmult.
 now srewrite pow1 Rmult_1_l.
Qed.

Lemma ex_CPowerSeries_alt a z : ex_CPowerSeries a z <-> ex_pseries a z.
Proof.
 split; intros (l & L); exists l; revert L; apply (is_CPowerSeries_alt a z l).
Qed.

Lemma ex_CPowerSeries_Cmod a z :
  ex_pseries (Cmod∘a) (Cmod z) -> ex_CPowerSeries a z.
Proof.
 intros H.
 rewrite ex_pseries_R in H.
 unfold "∘" in H. setoid_rewrite <- Cmod_pow in H.
 setoid_rewrite <- Cmod_mult in H.
 apply ex_series_Cmod in H. setoid_rewrite Cmult_comm in H.
 now rewrite ex_CPowerSeries_alt.
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

(** Convergence disk and radius for C power series *)

Definition C_CV_disk (a : nat -> C) (r : C) :=
  ex_series (fun n => Cmod (a n * r^n)).

Definition C_CV_radius (a : nat -> C) : Rbar.Rbar :=
  Lub.Lub_Rbar (C_CV_disk a).

Lemma C_CV_disk_alt a r : C_CV_disk a r <-> CV_disk (Cmod∘a) (Cmod r).
Proof.
 unfold C_CV_disk, CV_disk.
 split; apply ex_series_ext;
  intros n; unfold "∘";
   now rewrite <- Cmod_pow, <- Cmod_mult, Rabs_pos_eq by apply Cmod_ge_0.
Qed.

Lemma C_CV_radius_alt a : C_CV_radius a = CV_radius (Cmod∘a).
Proof.
 unfold C_CV_radius, CV_radius. apply Lub.Lub_Rbar_eqset.
 intros x. now rewrite C_CV_disk_alt, Cmod_R, <- CV_disk_rabs.
Qed.

Lemma C_CV_radius_ext a b :
 (forall n, a n = b n) -> C_CV_radius a = C_CV_radius b.
Proof.
 rewrite !C_CV_radius_alt. intros E. apply CV_radius_ext.
 intros. unfold "∘". f_equal. apply E.
Qed.

Global Instance C_CV_radius_proper :
  Proper (pointwise_relation _ eq ==> eq) C_CV_radius.
Proof.
 intros f f' Hf. apply C_CV_radius_ext. apply Hf.
Qed.

Lemma C_CV_disk_correct (a : nat -> C) (z : C) :
  C_CV_disk a z -> ex_CPowerSeries a z.
Proof.
 rewrite C_CV_disk_alt. intros H. apply ex_CPowerSeries_Cmod.
 now apply CV_disk_correct.
Qed.

Lemma C_CV_radius_inside (a : nat -> C) (z : C) :
  Rbar.Rbar_lt (Cmod z) (C_CV_radius a) -> ex_CPowerSeries a z.
Proof.
 intros H. apply ex_CPowerSeries_Cmod. apply CV_radius_inside.
 now rewrite <- C_CV_radius_alt, Rabs_pos_eq by apply Cmod_ge_0.
Qed.

Lemma C_CV_radius_outside (a : nat -> C) (z : C) :
  Rbar.Rbar_lt (C_CV_radius a) (Cmod z) ->
  ~is_lim_Cseq (fun n => a n * z^n) 0.
Proof.
 intros H. rewrite C_CV_radius_alt in H.
 rewrite <- (Rabs_pos_eq (Cmod z)) in H by apply Cmod_ge_0.
 apply CV_disk_outside in H. contradict H.
 apply is_lim_Cseq_Cmod in H. rewrite Cmod_0 in H.
 unfold "∘". now srewrite <- Cmod_pow Cmod_mult.
Qed.

Definition C_CV_disk' (a : nat -> C) (r : R) :=
 exists z, Cmod z = r /\ ex_CPowerSeries a z.

Definition C_CV_radius' (a : nat -> C) : Rbar.Rbar :=
  Lub.Lub_Rbar (C_CV_disk' a).

Lemma C_CV_radius_radius' a : C_CV_radius a = C_CV_radius' a.
Proof.
 apply Rbar.Rbar_le_antisym.
 { apply Lub.Lub_Rbar_correct.
   intros x Hx. destruct (Rle_lt_dec 0 x).
   - apply Lub_Rbar_ub. exists x. split.
     + now rewrite Cmod_R, Rabs_pos_eq.
     + now apply ex_series_Cmod.
   - apply Rbar.Rbar_le_trans with (Rbar.Finite 0). simpl; lra.
     apply Lub_Rbar_ub. red. exists 0%R. split. apply Cmod_0.
     exists (a O). rewrite is_CPowerSeries_alt. apply (is_pseries_0 a). }
 { apply Lub_Rbar_least.
   intros x (z & <- & E).
   destruct (Rbar.Rbar_le_lt_dec (Cmod z) (C_CV_radius a)) as [LE|LT];
    trivial.
   exfalso.
   rewrite C_CV_radius_alt in LT.
   rewrite <- (Rabs_pos_eq (Cmod z)) in LT by apply Cmod_ge_0.
   apply ex_series_lim_C0 in E.
   apply is_lim_Cseq_Cmod in E. rewrite Cmod_0 in E.
   apply (CV_disk_outside _ _ LT).
   unfold "∘". now srewrite <- Cmod_pow Cmod_mult. }
Qed.

Lemma C_CV_radius_minorant (a : nat -> C) (r:R) :
 (forall x, Cmod x < r -> ex_CPowerSeries a x) ->
 Rbar.Rbar_le r (C_CV_radius a).
Proof.
 intros H.
 apply Rbar_le_carac_via_lt.
 intros x Hx. simpl in Hx.
 destruct (Rle_lt_dec 0 x).
 - rewrite C_CV_radius_radius'.
   apply Lub_Rbar_ub. red. exists x; split.
   + rewrite Cmod_R, Rabs_pos_eq; lra.
   + apply H. rewrite Cmod_R, Rabs_pos_eq; lra.
 - apply Rbar.Rbar_le_trans with 0%R. simpl; lra.
   rewrite C_CV_radius_alt. apply CV_radius_ge_0.
Qed.

(** C power series projection (when point x is a Real) *)

Lemma is_CPowerSeries_proj (a:nat->C)(x:R) :
  ex_pseries (Cmod∘a) (Rabs x) ->
  is_CPowerSeries a x (PSeries (Re∘a) x, PSeries (Im∘a) x).
Proof.
 intros H.
 unfold is_CPowerSeries. rewrite is_lim_Cseq_proj. simpl. split.
 - eapply is_lim_seq_ext with (u:=sum_n (fun k => (Re∘a) k * x^k)%R).
   { intros n. unfold "∘". rewrite re_sum_n. unfold "∘".
     now srewrite <- re_scal_r RtoC_pow. }
   unfold PSeries, Series. apply Lim_seq_correct'. rewrite <- ex_series_alt.
   eapply (ex_series_le (V:=R_CNM)); eauto.
   { intros n. change norm with Rabs.
     rewrite Rabs_mult. unfold compose. rewrite RPow_abs.
     change scal with Rmult. rewrite Rmult_comm.
     apply Rmult_le_compat_l. apply Rabs_pos. apply re_le_Cmod. }
 - eapply is_lim_seq_ext with (u:=sum_n (fun k => (Im∘a) k * x^k)%R).
   { intros n. unfold compose. rewrite im_sum_n. unfold "∘".
     now srewrite <- im_scal_r RtoC_pow. }
   unfold PSeries, Series. apply Lim_seq_correct'. rewrite <- ex_series_alt.
   eapply (ex_series_le (V:=R_CNM)); eauto.
   { intros n. change norm with Rabs.
     rewrite Rabs_mult. unfold compose. rewrite RPow_abs.
     change scal with Rmult. rewrite Rmult_comm.
     apply Rmult_le_compat_l. apply Rabs_pos. apply im_le_Cmod. }
Qed.

Lemma CPowerSeries_proj (a:nat->C)(x:R) :
  ex_pseries (Cmod∘a) (Rabs x) ->
  CPowerSeries a x = (PSeries (Re∘a) x, PSeries (Im∘a) x).
Proof.
 intros. now apply CPowerSeries_unique, is_CPowerSeries_proj.
Qed.

(** Unicity of coefficients of C power series *)

Lemma CPowerSeries_coef_ext (a b : nat -> C) :
 Rbar.Rbar_lt R0 (C_CV_radius a) ->
 Rbar.Rbar_lt R0 (C_CV_radius b) ->
 locally R0 (fun x:R => CPowerSeries a x = CPowerSeries b x) ->
 forall n, a n = b n.
Proof.
 intros Ha Hb E n.
 rewrite (surjective_pairing (a n)), (surjective_pairing (b n)).
 assert (L: locally R0 (fun x : R => PSeries (Re ∘ a) x = PSeries (Re ∘ b) x
                                 /\ PSeries (Im ∘ a) x = PSeries (Im ∘ b) x)).
 { destruct E as (eps & E).
   set (ra := match C_CV_radius a with Rbar.Finite r => r | _ => 1%R end).
   assert (Ra : 0 < ra).
   { unfold ra. destruct (C_CV_radius a); try easy. lra. }
   set (rb := match C_CV_radius b with Rbar.Finite r => r | _ => 1%R end).
   assert (Rb : 0 < rb).
   { unfold rb. destruct (C_CV_radius b); try easy. lra. }
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
     apply CV_radius_inside. rewrite Rabs_Rabsolu.
     rewrite <- C_CV_radius_alt.
     apply Rbar.Rbar_lt_le_trans with eps'; trivial.
     apply Rbar.Rbar_le_trans with (Rmin ra rb); [apply Rmin_r|].
     apply Rbar.Rbar_le_trans with rb; [apply Rmin_r|].
     unfold rb. destruct C_CV_radius; simpl; trivial; lra.
   + clear E Hb. clearbody rb.
     rewrite Rminus_0_r in Y.
     apply CV_radius_inside. rewrite Rabs_Rabsolu.
     rewrite <- C_CV_radius_alt.
     apply Rbar.Rbar_lt_le_trans with eps'; trivial.
     apply Rbar.Rbar_le_trans with (Rmin ra rb); [apply Rmin_r|].
     apply Rbar.Rbar_le_trans with ra; [apply Rmin_l|].
     unfold ra. destruct C_CV_radius; simpl; trivial; lra. }
 f_equal.
 - apply (PSeries_ext_recip (Re∘a) (Re∘b) n).
   + apply Rbar.Rbar_lt_le_trans with (C_CV_radius a); auto.
     rewrite C_CV_radius_alt.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply re_le_Cmod.
   + apply Rbar.Rbar_lt_le_trans with (C_CV_radius b); auto.
     rewrite C_CV_radius_alt.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply re_le_Cmod.
   + destruct L as (eps & L). exists eps. apply L.
 - apply (PSeries_ext_recip (Im∘a) (Im∘b) n).
   + apply Rbar.Rbar_lt_le_trans with (C_CV_radius a); auto.
     rewrite C_CV_radius_alt.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply im_le_Cmod.
   + apply Rbar.Rbar_lt_le_trans with (C_CV_radius b); auto.
     rewrite C_CV_radius_alt.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply im_le_Cmod.
   + destruct L as (eps & L). exists eps. apply L.
Qed.

(** Power series and polynomial *)

Definition PS_poly (P:Polynomial) := fun n => coef n P.

Lemma PS_poly_ok (P:Polynomial) z :
  is_CPowerSeries (PS_poly P) z (Peval P z).
Proof.
 red. apply is_lim_Cseq_ext_loc with (fun _ => Peval P z).
 2:apply is_lim_Cseq_const.
 exists (length P); intros n Hn. unfold PS_poly, coef.
 unfold Peval.
 rewrite <- big_sum_sum_n.
 replace (S n) with (length P + (S n - length P))%nat by lia.
 rewrite big_sum_sum.
 rewrite <- (Cplus_0_r (big_sum _ _)) at 1.
 change Gplus with Cplus. f_equal. symmetry.
 apply (@big_sum_0 C). intros x.
 change Gzero with 0.
 rewrite nth_overflow; try lca. lia.
Qed.

Lemma PS_poly_radius p : C_CV_radius (PS_poly p) = Rbar.p_infty.
Proof.
 assert (H : forall x, Rbar.Rbar_le (Cmod x) (C_CV_radius (PS_poly p))).
 { intros x. rewrite C_CV_radius_radius'. apply Lub_Rbar_ub.
   exists x; split; trivial. eexists. apply PS_poly_ok. }
 destruct (C_CV_radius (PS_poly p)) as [x | | ]; trivial; exfalso.
 - specialize (H (Rabs x + 1)%R). simpl in H.
   rewrite Cmod_R in H.
   destruct (Rle_lt_dec 0 x).
   + rewrite !Rabs_pos_eq in H; try (generalize (Rabs_pos x); lra).
   + generalize (Rabs_pos (Rabs x + 1)); lra.
 - apply (H 0).
Qed.

Lemma PS_poly_ex p : ex_series (PS_poly p).
Proof.
 apply ex_series_incr_n with (n := length p).
 apply ex_series_ext with (a := fun _ => 0).
 { intros n. unfold PS_poly, coef. now rewrite nth_overflow by lia. }
 apply ex_series_RtoC. exists 0%R. apply is_series_R0.
Qed.

Lemma Cmod_PS_poly p n :
  RtoC (Cmod (PS_poly p n)) = PS_poly (map (RtoC∘Cmod) p) n.
Proof.
 unfold PS_poly. unfold coef.
 replace 0 with ((RtoC∘Cmod) 0) at 2.
 2:{ unfold "∘". now rewrite Cmod_0. }
 now rewrite map_nth.
Qed.

Lemma PS_poly_pow2 p n :
  (PS_poly p n)^2 = PS_poly (map (fun x => x^2) p) n.
Proof.
 unfold PS_poly, coef.
 rewrite <- (map_nth (fun x => x^2)). f_equal. ring.
Qed.

(** Basic constants for C Power Series *)

Definition PS_zero (n:nat) := 0.

Definition PS_zero_alt n : PS_zero n = PS_poly [] n.
Proof.
 now destruct n.
Qed.

Lemma PS_zero_ok z : is_CPowerSeries PS_zero z 0.
Proof.
 change 0 with (Peval [] z). change PS_zero with (fun k => PS_zero k).
 setoid_rewrite PS_zero_alt at 1. apply PS_poly_ok.
Qed.

Lemma PS_zero_radius : C_CV_radius PS_zero = Rbar.p_infty.
Proof.
 change PS_zero with (fun k => PS_zero k). setoid_rewrite PS_zero_alt.
 apply PS_poly_radius.
Qed.

Definition PS_one n := match n with O => 1 | _ => 0 end.

Definition PS_one_alt n : PS_one n = PS_poly [1] n.
Proof.
 now destruct n as [|[|n]].
Qed.

Lemma PS_one_ok z : is_CPowerSeries PS_one z 1.
Proof.
 rewrite <- (Pconst_eval 1 z).
 change PS_one with (fun k => PS_one k).
 setoid_rewrite PS_one_alt at 1. apply PS_poly_ok.
Qed.

Lemma PS_one_radius : C_CV_radius PS_one = Rbar.p_infty.
Proof.
 change PS_one with (fun k => PS_one k). setoid_rewrite PS_one_alt.
 apply PS_poly_radius.
Qed.

(** Addition of C power series *)

Definition CPS_plus : (nat->C) -> (nat->C) -> (nat->C) := PS_plus (V:=C_NM).

Lemma is_CPS_plus (a b : nat->C) (z la lb : C) :
  is_CPowerSeries a z la -> is_CPowerSeries b z lb
    -> is_CPowerSeries (CPS_plus a b) z (la+lb).
Proof.
 rewrite !is_CPowerSeries_alt. apply (is_pseries_plus a b).
Qed.

Lemma ex_CPS_plus (a b : nat->C) (z : C) :
  ex_CPowerSeries a z -> ex_CPowerSeries b z
    -> ex_CPowerSeries (CPS_plus a b) z.
Proof.
 rewrite !ex_CPowerSeries_alt. apply (ex_pseries_plus a b).
Qed.

Lemma CPowerSeries_plus (a b : nat -> C) (z : C) :
  ex_CPowerSeries a z -> ex_CPowerSeries b z ->
  CPowerSeries (CPS_plus a b) z = CPowerSeries a z + CPowerSeries b z.
Proof.
 intros (la,Ha) (lb,Hb).
 rewrite (CPowerSeries_unique _ _ _ Ha), (CPowerSeries_unique _ _ _ Hb).
 now apply CPowerSeries_unique, is_CPS_plus.
Qed.

Lemma C_CV_disk_plus (a b : nat -> C) (z : C) :
 C_CV_disk a z -> C_CV_disk b z -> C_CV_disk (CPS_plus a b) z.
Proof.
 intros Ha Hb.
 rewrite C_CV_disk_alt in *.
 unfold CPS_plus.
 assert (Hc := CV_disk_plus _ _ _ Ha Hb).
 red. red in Hc.
 eapply (ex_series_le (V:=R_CNM)); eauto.
 intros n. change norm with Rabs. simpl. rewrite Rabs_Rabsolu.
 rewrite !Rabs_mult. apply Rmult_le_compat_r. apply Rabs_pos.
 unfold "∘". unfold PS_plus.
 change plus with Cplus at 1. change plus with Rplus at 1.
 rewrite !Rabs_pos_eq. apply Cmod_triangle.
 generalize (Cmod_ge_0 (a n)), (Cmod_ge_0 (b n)); lra.
 apply Cmod_ge_0.
Qed.

Lemma C_CV_radius_plus (a b : nat -> C) :
  Rbar.Rbar_le (Rbar.Rbar_min (C_CV_radius a) (C_CV_radius b))
               (C_CV_radius (CPS_plus a b)).
Proof.
 apply Rbar_le_carac_via_lt.
 intros c Hc.
 assert (Ha : Rbar.Rbar_lt c (C_CV_radius a)).
 { generalize Hc. apply Rbar.Rbar_min_case_strong; trivial.
   intros. eapply Rbar.Rbar_lt_le_trans; eauto. }
 assert (Hb : Rbar.Rbar_lt c (C_CV_radius b)).
 { generalize Hc. apply Rbar.Rbar_min_case_strong; trivial.
   intros. eapply Rbar.Rbar_lt_le_trans; eauto. }
 clear Hc.
 destruct (Rle_lt_dec 0 c).
 - replace c with (Cmod c) in Ha, Hb.
   2:{ rewrite Cmod_R, Rabs_pos_eq; trivial. }
   apply C_CV_radius_inside in Ha,Hb.
   rewrite C_CV_radius_radius'.
   apply Lub_Rbar_ub. exists c.
   split. rewrite Cmod_R, Rabs_pos_eq; trivial.
   now apply ex_CPS_plus.
 - apply Rbar.Rbar_le_trans with 0%R. simpl; lra.
   rewrite C_CV_radius_alt. apply CV_radius_ge_0.
Qed.

Lemma C_CV_radius_opp (a : nat -> C) :
  C_CV_radius (PS_opp a) = C_CV_radius a.
Proof.
 rewrite !C_CV_radius_alt. apply CV_radius_ext. intros n. apply Cmod_opp.
Qed.

(** Multiplication of C power series *)

Definition CPS_mult (a b : nat->C) (n:nat) : C :=
  sum_n (fun k => a k * b (n - k)%nat) n.

Lemma CPS_mult_eqn a b n :
 CPS_mult a b n = (PS_mult (Re∘a) (Re∘b) n - PS_mult (Im∘a) (Im∘b) n,
                   PS_mult (Re∘a) (Im∘b) n + PS_mult (Im∘a) (Re∘b) n)%R.
Proof.
 unfold CPS_mult, PS_mult.
 rewrite <- !sum_n_Reals.
 rewrite sum_n_proj; f_equal.
 - unfold "∘". simpl. rewrite sum_n_Rminus. now apply sum_n_ext.
 - unfold "∘". simpl. rewrite sum_n_Rplus. now apply sum_n_ext.
Qed.

Lemma CPS_mult_scal (a b : nat -> C) (z : C) n :
  CPS_mult (fun k : nat => scal (pow_n z k) (a k))
           (fun k : nat => scal (pow_n z k) (b k)) n =
  scal (pow_n z n) (CPS_mult a b n).
Proof.
 unfold CPS_mult, PS_mult.
 change pow_n with Cpow. change scal with Cmult.
 rewrite <- sum_n_Cmult_l. apply sum_n_ext_loc.
 intros k Hk. replace n with (k+(n-k))%nat at 3 by lia.
 rewrite Cpow_add_r. fixeq C. ring.
Qed.

(** NB: is_series_mult coud have weaker preconditions, see Mertens thm. *)

Lemma is_series_mult (a b : nat -> C) (la lb : C) :
 Rbar.Rbar_lt 1%R (C_CV_radius a) ->
 Rbar.Rbar_lt 1%R (C_CV_radius b) ->
 is_series a la -> is_series b lb ->
 is_series (CPS_mult a b) (la * lb).
Proof.
 intros Ha0 Hb0 Ha Hb. rewrite is_Cseries_alt, is_lim_Cseq_proj.
 unfold "∘".
 rewrite C_CV_radius_alt, <- (Rabs_pos_eq 1) in Ha0, Hb0 by lra.
 assert (Ra : Rbar.Rbar_lt (Rabs 1) (CV_radius (Re ∘ a))).
 { eapply Rbar.Rbar_lt_le_trans; [ apply Ha0 | ].
   apply CV_radius_le. intros n. unfold "∘". rewrite re_le_Cmod.
   rewrite Rabs_pos_eq by apply Cmod_ge_0. lra. }
 assert (Rb : Rbar.Rbar_lt (Rabs 1) (CV_radius (Re ∘ b))).
 { eapply Rbar.Rbar_lt_le_trans; [ apply Hb0 | ].
   apply CV_radius_le. intros n. unfold "∘". rewrite re_le_Cmod.
   rewrite Rabs_pos_eq by apply Cmod_ge_0. lra. }
 assert (Ia : Rbar.Rbar_lt (Rabs 1) (CV_radius (Im ∘ a))).
 { eapply Rbar.Rbar_lt_le_trans; [ apply Ha0 | ].
   apply CV_radius_le. intros n. unfold "∘". rewrite im_le_Cmod.
   rewrite Rabs_pos_eq by apply Cmod_ge_0. lra. }
 assert (Ib : Rbar.Rbar_lt (Rabs 1) (CV_radius (Im ∘ b))).
 { eapply Rbar.Rbar_lt_le_trans; [ apply Hb0 | ].
   apply CV_radius_le. intros n. unfold "∘". rewrite im_le_Cmod.
   rewrite Rabs_pos_eq by apply Cmod_ge_0. lra. }
 split.
 - eapply is_lim_seq_ext.
   { intros n. symmetry. rewrite re_sum_n. unfold "∘".
     setoid_rewrite CPS_mult_eqn. simpl.
     symmetry. apply sum_n_Rminus. }
   simpl Re. apply is_lim_seq_minus'; rewrite <- is_series_alt.
   + rewrite <- is_pseries_1.
     apply is_pseries_mult; try rewrite is_pseries_1; trivial.
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Ha.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Ha.
       apply re_sum_n. }
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Hb.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Hb.
       apply re_sum_n. }
   + rewrite <- is_pseries_1.
     apply is_pseries_mult; try rewrite is_pseries_1; trivial.
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Ha.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Ha.
       apply im_sum_n. }
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Hb.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Hb.
       apply im_sum_n. }
 - eapply is_lim_seq_ext.
   { intros n. symmetry. rewrite im_sum_n. unfold "∘".
     setoid_rewrite CPS_mult_eqn. simpl.
     symmetry. apply sum_n_Rplus. }
   simpl Im. apply is_lim_seq_plus'; rewrite <- is_series_alt.
   + rewrite <- is_pseries_1.
     apply is_pseries_mult; try rewrite is_pseries_1; trivial.
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Ha.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Ha.
       apply re_sum_n. }
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Hb.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Hb.
       apply im_sum_n. }
   + rewrite <- is_pseries_1.
     apply is_pseries_mult; try rewrite is_pseries_1; trivial.
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Ha.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Ha.
       apply im_sum_n. }
     { rewrite is_Cseries_alt, is_lim_Cseq_proj in Hb.
       rewrite is_series_alt. eapply is_lim_seq_ext; try apply Hb.
       apply re_sum_n. }
Qed.

Lemma CV_radius_scalpow (a : nat -> R) (r : R) :
 0 < r ->
 CV_radius (fun n => scal (pow_n r n) (a n)) =
 Rbar.Rbar_mult (/r)%R (CV_radius a).
Proof.
 intros Hr.
 set (b := fun n => _).
 apply Lub.is_lub_Rbar_unique. unfold CV_disk.
 split.
 - intros x Hx.
   apply Rbar_le_mult_div; trivial.
   apply CV_disk_le_radius. red.
   eapply ex_series_ext; eauto.
   intros n. simpl. f_equal. unfold b.
   change scal with Rmult. change pow_n with pow.
   rewrite Rpow_mult_distr. ring.
 - intros l Hl. red in Hl.
   assert (Hr' : 0 < /r) by now apply Rinv_0_lt_compat.
   apply Rbar_le_mult_div; trivial.
   destruct (Lub.Lub_Rbar_correct (CV_disk a)) as (H1,H2).
   fold (CV_radius a) in H1,H2.
   red in H1. unfold CV_disk in H1.
   apply H2. red. intros x Hx. red in Hx.
   rewrite <- Rbar_le_mult_div; trivial.
   apply Hl.
   eapply ex_series_ext; eauto.
   intros n. simpl. f_equal. unfold b.
   change scal with Rmult. change pow_n with pow.
   rewrite Rpow_mult_distr, pow_inv. field. apply pow_nonzero. lra.
Qed.

Lemma CV_radius_scalpow_lt (a : nat -> R) (r : R) :
 0 < r ->
 Rbar.Rbar_lt r (CV_radius a) ->
 Rbar.Rbar_lt 1%R (CV_radius (fun n => scal (pow_n r n) (a n))).
Proof.
 intros Hr LT.
 rewrite CV_radius_scalpow; trivial.
 rewrite <- Rbar_lt_mult_div; trivial. simpl Rbar.Rbar_mult.
 rewrite Rmult_1_r; trivial.
Qed.

Lemma is_CPS_mult (a b : nat -> C) (z la lb : C) :
  is_CPowerSeries a z la -> is_CPowerSeries b z lb
  -> Rbar.Rbar_lt (Cmod z) (C_CV_radius a)
  -> Rbar.Rbar_lt (Cmod z) (C_CV_radius b)
  -> is_CPowerSeries (CPS_mult a b) z (la * lb).
Proof.
 intros Ha Hb Ha' Hb'.
 destruct (Ceq_dec z 0) as [->|Hz].
 { replace la with (a O).
   2:{ apply CPowerSeries_unique in Ha. rewrite <- Ha.
       symmetry. apply CPowerSeries_unique.
       rewrite is_CPowerSeries_alt.
       apply (is_pseries_0 a). }
   replace lb with (b O).
   2:{ apply CPowerSeries_unique in Hb. rewrite <- Hb.
       symmetry. apply CPowerSeries_unique.
       rewrite is_CPowerSeries_alt.
       apply (is_pseries_0 b). }
   replace (a O * b O) with (CPS_mult a b 0).
   2:{ unfold CPS_mult, PS_mult. now rewrite sum_O. }
   rewrite is_CPowerSeries_alt.
   apply (is_pseries_0 (CPS_mult a b)). }
 rewrite is_CPowerSeries_alt.
 unfold is_pseries.
 setoid_rewrite <- CPS_mult_scal.
 apply is_series_mult; try now rewrite is_CPowerSeries_alt in *.
 - rewrite C_CV_radius_alt in *.
   erewrite CV_radius_ext.
   apply (CV_radius_scalpow_lt (Cmod∘a)); eauto.
   now apply Cmod_gt_0.
   intros k. unfold "∘".
   change (Cmod (z^k * a k) = Cmod z^k * Cmod (a k))%R.
   now rewrite <- Cmod_pow, <- Cmod_mult.
 - rewrite C_CV_radius_alt in *.
   erewrite CV_radius_ext.
   apply (CV_radius_scalpow_lt (Cmod∘b)); eauto.
   now apply Cmod_gt_0.
   intros k. unfold "∘".
   change (Cmod (z^k * b k) = Cmod z^k * Cmod (b k))%R.
   now rewrite <- Cmod_pow, <- Cmod_mult.
Qed.

Lemma ex_CPS_mult (a b : nat -> C) (z : C) :
  Rbar.Rbar_lt (Cmod z) (C_CV_radius a) ->
  Rbar.Rbar_lt (Cmod z) (C_CV_radius b) ->
  ex_CPowerSeries (CPS_mult a b) z.
Proof.
 intros Ha Hb.
 exists ((CPowerSeries a z) * (CPowerSeries b z)).
 apply is_CPS_mult; trivial.
 - apply CPowerSeries_correct. now apply C_CV_radius_inside.
 - apply CPowerSeries_correct. now apply C_CV_radius_inside.
Qed.

Lemma CPowerSeries_mult (a b : nat -> C) (z : C) :
  Rbar.Rbar_lt (Cmod z) (C_CV_radius a) ->
  Rbar.Rbar_lt (Cmod z) (C_CV_radius b) ->
  CPowerSeries (CPS_mult a b) z = CPowerSeries a z * CPowerSeries b z.
Proof.
 intros Ha Hb.
 apply CPowerSeries_unique, is_CPS_mult; trivial.
 - apply CPowerSeries_correct. now apply C_CV_radius_inside.
 - apply CPowerSeries_correct. now apply C_CV_radius_inside.
Qed.

Lemma C_CV_radius_mult (a b : nat -> C) :
  Rbar.Rbar_le (Rbar.Rbar_min (C_CV_radius a) (C_CV_radius b))
               (C_CV_radius (CPS_mult a b)).
Proof.
 apply Rbar_le_carac_via_lt.
 intros c Hc.
 assert (Ha : Rbar.Rbar_lt c (C_CV_radius a)).
 { generalize Hc. apply Rbar.Rbar_min_case_strong; trivial.
   intros. eapply Rbar.Rbar_lt_le_trans; eauto. }
 assert (Hb : Rbar.Rbar_lt c (C_CV_radius b)).
 { generalize Hc. apply Rbar.Rbar_min_case_strong; trivial.
   intros. eapply Rbar.Rbar_lt_le_trans; eauto. }
 clear Hc.
 destruct (Rle_lt_dec 0 c).
 - replace c with (Cmod c) in Ha, Hb.
   2:{ rewrite Cmod_R, Rabs_pos_eq; trivial. }
   rewrite C_CV_radius_radius'.
   apply Lub_Rbar_ub. exists c.
   split. rewrite Cmod_R, Rabs_pos_eq; trivial.
   now apply ex_CPS_mult.
 - apply Rbar.Rbar_le_trans with 0%R. simpl; lra.
   rewrite C_CV_radius_alt. apply CV_radius_ge_0.
Qed.

Lemma CPS_mult_poly q r n :
 CPS_mult (PS_poly q) (PS_poly r) n = PS_poly (Pmult q r) n.
Proof.
 unfold CPS_mult, PS_poly. now rewrite Pmult_coef, big_sum_sum_n.
Qed.

Lemma CPS_mult_real (a b : nat -> C) :
 (forall n, Im (a n) = 0%R) -> (forall n, Im (b n) = 0%R) ->
 forall n, Im (CPS_mult a b n) = 0%R.
Proof.
 intros Ha Hb n.
 unfold CPS_mult. rewrite im_sum_n. rewrite <- (sum_n_R0 n).
 apply sum_n_ext_loc. intros m Hm.
 unfold "∘". rewrite im_mult. rewrite Ha, Hb. lra.
Qed.

Lemma PS_mult_RtoC (a b : nat -> R) n :
 RtoC (PS_mult a b n) = CPS_mult (RtoC∘a) (RtoC∘b) n.
Proof.
 unfold PS_mult, CPS_mult. rewrite <- sum_n_Reals.
 rewrite RtoC_sum_n. unfold "∘". now setoid_rewrite RtoC_mult.
Qed.

Definition ZPS_mult (a b : nat -> Z) (n : nat) :=
 big_sum (fun k : nat => (a k * b (n - k)%nat)%Z) (S n).

Lemma ZPS_mult_IZR (a b : nat -> Z) n :
 IZR (ZPS_mult a b n) = PS_mult (IZR∘a) (IZR∘b) n.
Proof.
 unfold ZPS_mult, PS_mult. rewrite <- sum_n_Reals, <- big_sum_sum_n_R.
 rewrite big_sum_IZR. unfold "∘". now setoid_rewrite mult_IZR.
Qed.

(** Inverse function, obtained via successive powers as coefficients *)

Definition PS_pow := Cpow.

Lemma PS_pow_ok r x : Cmod (r*x) < 1 ->
  is_CPowerSeries (PS_pow r) x (/(1-r*x)).
Proof.
 destruct (Ceq_dec r 0) as [Hr|Hr].
 { intros _.
   rewrite is_CPowerSeries_alt. apply is_pseries_ext with PS_one.
   { intros [|n]; simpl; trivial. subst; lca. }
   rewrite <- is_CPowerSeries_alt. subst.
   replace (/ (1 - _)) with 1 by field. apply PS_one_ok. }
 intros Hx. unfold PS_pow.
 apply is_lim_Cseq_ext with (fun n => (1 - (r*x)^S n)/(1-r*x)).
 { intros n.
   apply Cmult_eq_reg_r with (1-r*x).
   2:{ intros E. apply Ceq_minus in E. rewrite <- E, Cmod_1 in Hx. lra. }
   unfold Cdiv. rewrite <- Cmult_assoc, Cinv_l, Cmult_1_r.
   2:{ intros E. apply Ceq_minus in E. rewrite <- E, Cmod_1 in Hx. lra. }
   setoid_rewrite <- Cpow_mult_l.
   rewrite (Cmult_comm (sum_n _ _)). symmetry. apply sum_n_Cpow. }
 unfold Cdiv. rewrite <- (Cmult_1_l (/(1-r*x))) at 1.
 apply is_lim_Cseq_mult; [|apply is_lim_Cseq_const].
 replace 1 with (1-0) at 1 by lca.
 apply is_lim_Cseq_minus. apply is_lim_Cseq_const.
 apply is_lim_Cseq_0_Cmod.
 apply is_lim_seq_ext with (fun n => (Cmod (r*x))^S n)%R.
 - intros n. unfold compose. now rewrite Cmod_pow.
 - rewrite <- is_lim_seq_incr_1. apply is_lim_seq_geom.
   now rewrite Rabs_right by apply Rle_ge, Cmod_ge_0.
Qed.

Lemma PS_pow_radius (r:C) : r<>0 -> C_CV_radius (PS_pow r) = (/Cmod r)%R.
Proof.
 intros Hr.
 rewrite C_CV_radius_alt.
 apply CV_radius_finite_DAlembert.
 - intros n. unfold "∘", PS_pow.
   rewrite Cmod_pow. apply pow_nonzero.
   rewrite (Cmod_gt_0 r) in Hr. lra.
 - now apply Cmod_gt_0.
 - unfold "∘", PS_pow.
   eapply is_lim_seq_ext; try apply is_lim_seq_const.
   intros n; simpl. rewrite Cmod_mult.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_r.
   + now rewrite Rmult_1_r, Rabs_pos_eq by apply Cmod_ge_0.
   + rewrite Cmod_pow. apply pow_nonzero.
     rewrite (Cmod_gt_0 r) in Hr. lra.
Qed.

Lemma PS_scal_radius (c:C)(a:nat->C) : c<>0 ->
 C_CV_radius (PS_scal c a) = C_CV_radius a.
Proof.
 intros Hc.
 rewrite !C_CV_radius_alt.
 rewrite <- (CV_radius_scal (Cmod c) (Cmod∘a)).
 2:{ apply Cmod_gt_0 in Hc. lra. }
 apply CV_radius_ext. intros n. unfold "∘".
 unfold PS_scal. change scal with Cmult at 1. change scal with Rmult.
 apply Cmod_mult.
Qed.

Definition PS_invlin (r:C) := PS_scal (-/r) (PS_pow (/r)).

Lemma PS_invlin_ok r x : r<>0 -> Cmod x < Cmod r ->
 is_CPowerSeries (PS_invlin r) x (/(x - r)).
Proof.
 intros Hr Hx. unfold PS_invlin.
 replace (/(x-r)) with ((-/r)*(/(1-(/r)*x))).
 2:{ field. repeat split; try easy; rewrite <- Ceq_minus; intros ->; lra. }
 rewrite is_CPowerSeries_alt.
 apply (is_pseries_scal (V:=C_NormedModule)). apply Cmult_comm.
 rewrite <- is_CPowerSeries_alt.
 apply PS_pow_ok.
 rewrite Cmod_mult, Cmod_inv. apply Rmult_lt_reg_l with (Cmod r).
 now apply Cmod_gt_0.
 rewrite <- Rmult_assoc, Rinv_r. lra. apply Cmod_gt_0 in Hr. lra.
Qed.

Lemma PS_invlin_radius (r:C) : r<>0 -> C_CV_radius (PS_invlin r) = Cmod r.
Proof.
 intros Hr. unfold PS_invlin. rewrite PS_scal_radius, PS_pow_radius.
 - now rewrite Cmod_inv, Rinv_inv.
 - now apply nonzero_div_nonzero.
 - apply nonzero_div_nonzero in Hr. contradict Hr.
   rewrite <- (Copp_involutive (/r)). rewrite Hr; lca.
Qed.

Definition PS_inv_linfactors (l:list C) :=
  fold_right (fun r => CPS_mult (PS_invlin r)) PS_one l.

Definition Rbar_minlist (l : list Rbar.Rbar) :=
  fold_right Rbar.Rbar_min Rbar.p_infty l.

Definition min_Cmod_list (l : list C) :=
  Rbar_minlist (map (fun r => Rbar.Finite (Cmod r)) l).

Lemma min_Cmod_cons z l :
  min_Cmod_list (z::l) = Rbar.Rbar_min (Cmod z) (min_Cmod_list l).
Proof.
 easy.
Qed.

Lemma min_Cmod_list_spec (x:R) l :
 Rbar.Rbar_lt x (min_Cmod_list l) <-> Forall (fun r => x < Cmod r) l.
Proof.
 induction l.
 - simpl. split; constructor.
 - rewrite min_Cmod_cons. split; intros H.
   + constructor.
     * change (Rbar.Rbar_lt x (Cmod a)).
       eapply Rbar.Rbar_lt_le_trans; eauto. apply Rbar.Rbar_min_l.
     * apply IHl.
       eapply Rbar.Rbar_lt_le_trans; eauto. apply Rbar.Rbar_min_r.
   + inversion_clear H. apply Rbar.Rbar_min_case; trivial.
     now apply IHl.
Qed.

Lemma PS_inv_linfactors_radius (l : list C) :
  ~In 0 l ->
  Rbar.Rbar_le (min_Cmod_list l) (C_CV_radius (PS_inv_linfactors l)).
Proof.
 induction l.
 - intros _; simpl; now rewrite PS_one_radius.
 - rewrite min_Cmod_cons.
   cbn -[Rbar.Rbar_min]. intros H.
   eapply Rbar.Rbar_le_trans; [| apply C_CV_radius_mult].
   remember (Rbar.Rbar_min _ _) as x.
   apply Rbar.Rbar_min_case; subst x;
     [ eapply Rbar.Rbar_le_trans; try apply Rbar.Rbar_min_l
     | eapply Rbar.Rbar_le_trans; try apply Rbar.Rbar_min_r ].
   + rewrite PS_invlin_radius; simpl; try easy. tauto.
   + apply IHl; tauto.
Qed.

Lemma PS_inv_linfactors_ok l z :
  Forall (fun r => Cmod z < Cmod r) l ->
  is_CPowerSeries (PS_inv_linfactors l) z (/ Peval (linfactors l) z).
Proof.
 induction l.
 - intros _. simpl. rewrite Pconst_eval, Cinv_1. apply PS_one_ok.
 - inversion_clear 1. simpl. rewrite Pmult_eval, Cinv_mult.
   assert (Ha : a <> 0).
   { apply Cmod_gt_0. generalize (Cmod_ge_0 z); lra. }
   replace (Peval [-a;1] z) with (z-a).
   2:{ unfold Peval. simpl. ring. }
   rewrite Cmult_comm.
   apply is_CPS_mult; auto.
   + now apply PS_invlin_ok.
   + now rewrite PS_invlin_radius.
   + eapply Rbar.Rbar_lt_le_trans.
     2:{ apply PS_inv_linfactors_radius.
         intros IN. rewrite Forall_forall in H1. specialize (H1 0 IN).
         rewrite Cmod_0 in H1. generalize (Cmod_ge_0 z); lra. }
     now apply min_Cmod_list_spec.
Qed.

(** Changing x into x^k in a function is obtained by interleaving some 0
    between the coefficients *)

Definition PS_dilate (a:nat->C) (k:nat) :=
 fun n => if (n mod k =? 0)%nat then a (n/k)%nat else 0.

Lemma sum_PS_dilate (a:nat->C) (k:nat) x n :
 k<>O ->
 sum_n (fun m => PS_dilate a k m * x^m) n
 = sum_n (fun m => a m * (x^k)^m) (n/k).
Proof.
 intros Hk.
 induction n.
 - replace (0/k)%nat with 0%nat. 2:{ symmetry. now apply Nat.div_0_l. }
   rewrite !sum_O. unfold PS_dilate. simpl.
   rewrite Nat.mod_0_l, Nat.div_0_l; trivial.
 - rewrite sum_Sn. change plus with Cplus.
   rewrite IHn. unfold PS_dilate.
   case Nat.eqb_spec; intros H.
   + assert (E := Nat.div_mod_eq (S n) k). rewrite H, Nat.add_0_r in E.
     assert (E' := Nat.div_mod_eq n k).
     assert (H' : (n mod k = k-1)%nat).
     { apply Nat.le_antisymm.
       - generalize (Nat.mod_upper_bound n k Hk); lia.
       - apply Nat.le_ngt. intros LT.
         assert (S (n mod k) = (S n) mod k); try lia.
         { apply Nat.mod_unique with (q:=(n/k)%nat); lia. }}
     rewrite H' in E'. apply (f_equal S) in E'.
     replace (S (_+_)) with (k * (S (n/k)))%nat in E' by lia.
     replace (S n / k)%nat with (S (n/k)).
     2:{ apply Nat.div_unique_exact; try lia. }
     rewrite sum_Sn. change plus with Cplus. f_equal. f_equal.
     rewrite <- Cpow_mult_r. f_equal. apply E'.
   + rewrite Cmult_0_l, Cplus_0_r.
     assert (E := Nat.div_mod_eq (S n) k).
     assert (E' := Nat.div_mod_eq n k).
     apply (f_equal S) in E'. rewrite <- Nat.add_succ_r in E'.
     assert (H' : (S (n mod k) = S n mod k)%nat).
     { destruct (Nat.eqb_spec (n mod k) (k-1)) as [H'|H'].
       - rewrite H' in E'.
         replace (_+_)%nat with (k*(S (n/k)))%nat in E' by lia.
         assert (S n mod k = 0)%nat; try lia.
         symmetry. apply Nat.mod_unique with (q:=S (n/k)); lia.
       - apply Nat.mod_unique with (q:=(n/k)%nat); try lia.
         generalize (Nat.mod_upper_bound n k Hk); lia. }
     rewrite H' in E'. f_equal.
     eapply Nat.div_unique; eauto. now apply Nat.mod_upper_bound.
Qed.

Lemma is_CPowerSeries_dilate a k x l : k<>O ->
  is_CPowerSeries a (x^k) l <-> is_CPowerSeries (PS_dilate a k) x l.
Proof.
 intros Hk. unfold is_CPowerSeries.
 rewrite !is_lim_Cseq_alt. split.
 - intros H eps. destruct (H eps) as (N & HN). exists (N*k)%nat.
   intros n Hn. rewrite sum_PS_dilate by trivial. apply HN.
   apply Nat.div_le_lower_bound; lia.
 - intros H eps. destruct (H eps) as (N & HN). exists N.
   intros n Hn.
   assert (Hn' : (N <= n*k)%nat).
   { replace k with (1+(k-1))%nat by lia.
     rewrite Nat.mul_add_distr_l. (* ?! lia should work from here... *)
     rewrite Nat.mul_1_r. apply Nat.le_trans with n; trivial.
     apply Nat.le_add_r. }
   specialize (HN (n*k)%nat Hn').
   rewrite sum_PS_dilate in HN by trivial.
   rewrite Nat.div_mul in HN by trivial. apply HN.
Qed.

Lemma PS_dilate_radius_lt a k r : k<>O ->
 Rbar.Rbar_lt (r^k)%R (C_CV_radius a) ->
 Rbar.Rbar_lt r (C_CV_radius (PS_dilate a k)).
Proof.
 intros Hk H.
 destruct (Rle_lt_dec 0 r) as [LE|LT].
 - assert (H1 : exists r1, r^k < r1 /\ Rbar.Rbar_lt r1 (C_CV_radius a)).
   { destruct (C_CV_radius a) as [ra| | ]; try easy.
     - exists ((r^k+ra)/2)%R. split; simpl in H|-*; lra.
     - exists (r^k+1)%R. split; simpl; lra. }
   assert (H2 : exists r2, r < r2 /\ Rbar.Rbar_lt (r2^k)%R (C_CV_radius a)).
   { destruct H1 as (r1 & H1 & H1').
     exists (nthroot r1 k). split.
     - apply (Rpow_lt_reg_r k); trivial. apply nthroot_pos.
       rewrite nthroot_pow; trivial. apply (pow_le r k) in LE. lra.
     - rewrite nthroot_pow; trivial. apply (pow_le r k) in LE. lra. }
   destruct H2 as (r2 & H2 & H2'). clear H H1.
   replace (r2^k)%R with (Cmod (r2^k)) in H2'.
   2:{ ctor. rewrite Cmod_R, Rabs_pos_eq; trivial. apply pow_le; lra. }
   apply C_CV_radius_inside in H2'. destruct H2' as (l & H2').
   rewrite is_CPowerSeries_dilate in H2' by trivial.
   rewrite C_CV_radius_radius'.
   apply Rbar.Rbar_lt_le_trans with r2; trivial.
   apply Lub_Rbar_ub. red. exists (RtoC r2). split.
   now rewrite Cmod_R, Rabs_pos_eq by lra.
   now exists l.
 - apply Rbar.Rbar_lt_le_trans with 0%R; trivial.
   rewrite C_CV_radius_alt. apply CV_radius_ge_0.
Qed.

Lemma PS_dilate_radius_le a k r : k<>O ->
 Rbar.Rbar_le (r^k)%R (C_CV_radius a) ->
 Rbar.Rbar_le r (C_CV_radius (PS_dilate a k)).
Proof.
 intros Hk H.
 apply Rbar_le_carac_via_lt. intros r' Hr'. simpl in Hr'.
 destruct (Rle_lt_dec 0 r') as [LE|LT].
 - apply Rbar.Rbar_lt_le. apply (PS_dilate_radius_lt a k r'); trivial.
   eapply Rbar.Rbar_lt_le_trans; eauto.
   simpl. apply Rpow_lt_compat_r; trivial.
 - apply Rbar.Rbar_le_trans with 0%R. simpl; lra.
   rewrite C_CV_radius_alt. apply CV_radius_ge_0.
Qed.

Lemma PS_dilate_real (a : nat -> C) r :
 (forall n, Im (a n) = 0%R) -> (forall n, Im (PS_dilate a r n) = 0%R).
Proof.
 intros Ha n. unfold PS_dilate. destruct Nat.eqb. apply Ha. easy.
Qed.

(** Delaying a sequence with p extra initial zeros multiplies by [x^p].
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
   - change zero with 0. lca.
   - rewrite Cmult_assoc, (Cmult_comm (z^p)), <- Cmult_assoc. f_equal.
     rewrite <- Cpow_add. f_equal. lia. }
 apply is_lim_Cseq_mult; trivial using is_lim_Cseq_const.
Qed.
