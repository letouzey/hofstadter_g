From Coq Require Import Lia Reals Lra Morphisms QArith.
Close Scope Q. (* Issue with QArith. *)
From Coquelicot Require Import Hierarchy Continuity Derive AutoDerive
 RInt RInt_analysis Series PSeries.
From Hofstadter.HalfQuantum Require Import Complex Polynomial.
Require Import MoreTac MoreList MoreReals MoreLim MoreSum MoreComplex.
Require Import MorePoly IntPoly MoreIntegral ThePoly GenFib Mu.
Require Phi F3 F4 F5.
Local Open Scope R.
Local Open Scope C.
Local Open Scope poly_scope.
Local Coercion INR : nat >-> R.
Local Coercion IZR : Z >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * Definition of Pisot numbers and Siegel Theorem *)

(** Definition of Pisot numbers *)

Definition Pisot (x:R) :=
  1<x /\
  exists l : list C,
    IntPoly (linfactors (RtoC x :: l)) /\
    Forall (fun r => 0 < Cmod r < 1) l.

Definition PisotConjugates (x:R)(l : list C) :=
  1<x /\
  IntPoly (linfactors (RtoC x :: l)) /\
  Forall (fun r => 0 < Cmod r < 1) l.

Lemma Pisot_alt x : Pisot x <-> exists l, PisotConjugates x l.
Proof.
 split.
 - intros (Hx & l & H1 & H2). now exists l.
 - intros (l & Hx & H1 & H2). split; trivial. now exists l.
Qed.

(** First examples *)

Lemma Pisot_nat_ge_2 (n:nat) : (2<=n)%nat -> Pisot n.
Proof.
 split.
 - apply le_INR in H. simpl in H. lra.
 - exists []; simpl; split; [|constructor].
   apply IntPoly_alt. exists [-Z.of_nat n;1]%Z.
   simpl. unfold "∘"; repeat f_equal; try ring.
   rewrite opp_IZR, <- INR_IZR_INZ, RtoC_opp. ring.
Qed.

Lemma Pisot_mu2 : Pisot (mu 2). (* Golden ratio 1.618.. *)
Proof.
 split.
 - apply (mu_itvl 2).
 - exists [-tau 2]; split.
   + simpl. rewrite !Cmult_1_l, !Cmult_1_r, !Cplus_0_r.
     rewrite !Copp_involutive, <- !Copp_mult_distr_r.
     unfold tau at 1. rewrite RtoC_inv, Cinv_l.
     2:{ intros [= E]. generalize (mu_itvl 2); lra. }
     rewrite <- !RtoC_opp, <- opp_IZR. simpl.
     rewrite <- RtoC_plus. replace (tau 2 + - mu 2)%R with (-1)%R.
     2:{ rewrite tau_2, mu_2. field. }
     apply IntPoly_alt. now exists [-1;-1;1]%Z.
   + repeat constructor; rewrite Cmod_opp, Cmod_R, Rabs_pos_eq;
      generalize (tau_itvl 2); lra.
Qed.

Lemma Pisot_mu3 : Pisot (mu 3). (* 1.465571... *)
Proof.
 split.
 - apply (mu_itvl 3).
 - exists (tl F3.roots). split.
   + change (RtoC (mu 3) :: tl F3.roots) with F3.roots.
     rewrite F3.linfactors_roots.
     unfold ThePoly. simpl. rewrite !Cplus_0_l.
     apply IntPoly_alt. now exists [-1;0;-1;1]%Z.
   + unfold F3.roots. simpl.
     repeat constructor;
     change F3.αbar with (Cconj F3.α); rewrite ?Cmod_conj;
     generalize F3.αmod_approx; unfold Approx.Approx; lra.
Qed.

Lemma Pisot_mu4 : Pisot (mu 4). (* 1.380277... *)
Proof.
 split.
 - apply (mu_itvl 4).
 - exists (tl F4.roots). split.
   + change (RtoC (mu 4) :: tl F4.roots) with F4.roots.
     destruct F4.roots_sorted as (<-,_).
     unfold ThePoly. simpl. rewrite !Cplus_0_l.
     apply IntPoly_alt. now exists [-1;0;0;-1;1]%Z.
   + unfold F4.roots. simpl.
     repeat constructor;
     change F4.αbar with (Cconj F4.α);
     rewrite ?Cmod_conj, ?Cmod_R, ?Rabs_left;
     generalize F4.αmod_approx, F4.ν_approx; unfold Approx.Approx; lra.
Qed.

(** (mu 5) = 1.3247179... is the Plastic Ratio, root of X^3-X-1.
    NB: ThePoly 5 has secondary roots of modulus 1, but can be factorized
    as (X^3-X-1)(X^2-X+1) *)

Lemma Pisot_mu5 : Pisot (mu 5).
Proof.
 split.
 - apply (mu_itvl 5).
 - exists [F5.α; F5.αbar]. split.
   + change (mu 5) with F5.μ. rewrite <- F5.factor2.
     apply IntPoly_alt. now exists [-1;-1;0;1]%Z.
   + assert (0 < Cmod F5.α < 1).
     { split; apply Rsqr_incrst_0; try lra; try apply Cmod_ge_0;
       rewrite ?Rsqr_1, ?Rsqr_0, Rsqr_pow2, F5.αmod2;
       change F5.τ with (tau 5); generalize (tau_itvl 5); lra. }
     repeat constructor; trivial;
     change F5.αbar with (Cconj F5.α); now rewrite ?Cmod_conj.
Qed.

(** With our formulation, we retrieve the irreducibilty and uniqueness
    of the polynomial associated to a Pisot number *)

Definition PisotPoly (x:R)(p : Polynomial) :=
  exists l, PisotConjugates x l /\ Peq p (linfactors (RtoC x :: l)).

Lemma Pisot_alt' x : Pisot x <-> exists p, PisotPoly x p.
Proof.
 rewrite Pisot_alt. split.
 - intros (l & Hl). exists (linfactors (RtoC x :: l)). now exists l.
 - intros (p & (l & Hl & Hl')). now exists l.
Qed.

Lemma PisotIntPoly x p : PisotPoly x p -> IntPoly p.
Proof.
 intros (l & H1 & H2). rewrite H2. apply H1.
Qed.

Lemma PisotPolyRoot x p : PisotPoly x p -> Root x p.
Proof.
 intros (l & H1 & H2). rewrite H2. rewrite <- linfactors_roots. now left.
Qed.

Lemma PisotPolyIrred x p : PisotPoly x p -> ~Zreducible p.
Proof.
 intros Hp (p1 & p2 & E & H1 & H2 & D).
 assert (T : topcoef p1 * topcoef p2 = 1).
 { assert (E' := topcoef_mult p1 p2).
   rewrite <- E in E'.
   destruct Hp as (l & Hl1 & Hl2). rewrite Hl2 in E'.
   now rewrite linfactors_monic in E'. }
 assert (T1 : topcoef p1 = 1 \/ topcoef p1 = -1).
 { apply IntPoly_topcoef, CInteger_alt in H1, H2.
   destruct H1 as (n & Hn), H2 as (m, Hm). rewrite Hn, Hm in *.
   rewrite <- RtoC_mult, <- mult_IZR in T.
   apply RtoC_inj, eq_IZR in T.
   apply Z.mul_eq_1 in T. destruct T as [-> | ->]. now left. now right. }
 destruct (Ceq_dec (Peval p1 x) 0) as [Hx|Hx].
 - assert (Hx' : ~Root x p2).
   { intros Hx'.
     assert (Root x (Pdiff p)).
     { rewrite E, Pdiff_mult. red.
       rewrite Pplus_eval, !Pmult_eval, Hx, Hx'. ring. }
     destruct Hp as (l & Hl & Hl').
     revert H. unfold Root. rewrite Hl'. simpl. rewrite Pdiff_mult; simpl.
     rewrite Pplus_eval, !Pmult_eval.
     replace (Peval [_;_] x) with 0 by (unfold Peval; simpl; ring).
     replace (Peval [_;_] x) with 1 by (unfold Peval; simpl; ring).
     rewrite Cmult_0_r, Cplus_0_l, Cmult_1_r.
     change (~Root x (linfactors l)). rewrite <- linfactors_roots.
     destruct Hl as (Hx1 & Hl1 & Hl2). intros IN.
     rewrite Forall_forall in Hl2. specialize (Hl2 x IN).
     rewrite Cmod_R, Rabs_pos_eq in Hl2; lra. }
   set (p2' := [topcoef p1] *, p2).
   destruct (IntPoly_null_or_large_root p2') as (r & Hr & Hr').
   { apply IntPoly_mult; trivial. constructor; [|constructor].
     rewrite CInteger_alt.
     destruct T1 as [-> | ->]; [now exists 1%Z|now exists (-1)%Z]. }
   { red. unfold p2'. now rewrite topcoef_mult, topcoef_singl. }
   { unfold p2'. rewrite Pscale_degree.
     2:{ destruct T1 as [-> | ->]; injection; lra. }
     rewrite E in D. rewrite Pmult_degree in D; try lia.
     - change (~Peq p1 []). intros E1. rewrite <- topcoef_0_iff in E1.
       rewrite E1 in T. rewrite Cmult_0_l in T. injection T; lra.
     - change (~Peq p2 []). intros E2. rewrite <- topcoef_0_iff in E2.
       rewrite E2 in T. rewrite Cmult_0_r in T. injection T; lra. }
   destruct Hp as (l & (Hx1 & _ & Hl1) & Hl2).
   assert (Hr2 : Root r p2).
   { unfold p2' in Hr. red in Hr.
     rewrite Pmult_eval in Hr. apply Cmult_integral in Hr.
     rewrite Pconst_eval in Hr. destruct Hr as [Hr | Hr]; try easy.
     rewrite Hr in T. rewrite Cmult_0_l in T. injection T; lra. }
   assert (IN : In r (RtoC x :: l)).
   { apply linfactors_roots. rewrite <- Hl2, E. red.
     rewrite Pmult_eval. rewrite Hr2. lca. }
   simpl in IN. destruct IN as [IN | IN]; [ now rewrite IN in Hx'|].
   assert (Hr3 : 0 < Cmod r < 1).
   { rewrite Forall_forall in Hl1. now apply Hl1. }
   rewrite <- Cmod_eq_0_iff in Hr'. generalize (Cmod_ge_0 r); lra.
 - set (p1' := [topcoef p1] *, p1).
   destruct (IntPoly_null_or_large_root p1') as (r & Hr & Hr').
   { apply IntPoly_mult; trivial. constructor; [|constructor].
     rewrite CInteger_alt.
     destruct T1 as [-> | ->]; [now exists 1%Z|now exists (-1)%Z]. }
   { red. unfold p1'. rewrite topcoef_mult, topcoef_singl.
     destruct T1 as [-> | ->]; lca. }
   { unfold p1'. rewrite Pscale_degree; try lia.
     destruct T1 as [-> | ->]; injection; lra. }
   destruct Hp as (l & (Hx1 & _ & Hl1) & Hl2).
   assert (Hr2 : Root r p1).
   { unfold p1' in Hr. red in Hr.
     rewrite Pmult_eval in Hr. apply Cmult_integral in Hr.
     rewrite Pconst_eval in Hr. destruct Hr as [Hr | Hr]; try easy.
     rewrite Hr in T. rewrite Cmult_0_l in T. injection T; lra. }
   assert (IN : In r (RtoC x :: l)).
   { apply linfactors_roots. rewrite <- Hl2, E. red.
     rewrite Pmult_eval. rewrite Hr2. lca. }
   simpl in IN. destruct IN as [IN | IN]; [ now rewrite IN in Hx|].
   assert (Hr3 : 0 < Cmod r < 1).
   { rewrite Forall_forall in Hl1. now apply Hl1. }
   rewrite <- Cmod_eq_0_iff in Hr'. generalize (Cmod_ge_0 r); lra.
Qed.

Definition MinPolyQ x p :=
  monic p /\ RatPoly p /\ Root x p /\
  forall q, ~Peq q [] -> RatPoly q -> Root x q -> (degree p <= degree q)%nat.

(* NB: RootQ_has_MinPolyQ proved here via excluded middle *)

Lemma RootQ_has_MinPolyQ x :
  (exists p, ~Peq p [] /\ RatPoly p /\ Root x p) ->
  (exists p, MinPolyQ x p).
Proof.
 intros (p & NZ & ER & Hx).
 remember (degree p) as d. revert p Heqd NZ ER Hx.
 induction d as [d IH] using lt_wf_ind.
 intros p E NZ ER Hx.
 destruct (Classical_Prop.classic
           (exists q, ~Peq q [] /\ RatPoly q /\ Root x q /\
                      (degree q < d)%nat)) as [(q & NZ' & ER' & Hx' & D)|N].
 - apply (IH (degree q) D q eq_refl NZ' ER' Hx').
 - exists (monicify p); repeat split.
   + now apply monicify_ok.
   + now apply RatPoly_monicify.
   + now rewrite monicify_root.
   + intros q NZ' RP' Hx'. rewrite monicify_degree; trivial. rewrite <- E.
     apply Nat.le_ngt. contradict N. now exists q.
Qed.

Lemma MinPolyQ_unique_aux x p q :
  MinPolyQ x p -> RatPoly q -> Root x q ->
  exists u, RatPoly u /\ Peq q (p *, u).
Proof.
 intros (MO & RP & Hx & MIN) RP' Hx'.
 destruct (Nat.eq_dec (degree p) 0) as [D0|D0].
 { exists q. split; trivial. now rewrite (deg0_monic_carac p), Pmult_1_l. }
 { destruct (Pdiv q p) as (u & v) eqn:E.
   assert (Huv1 := Pdiv_eqn q p).
   assert (Huv2 := Pdiv_degree q p).
   assert (Huv3 := RatPoly_div q p RP' RP).
   rewrite E in *; simpl in *. specialize (Huv2 ltac:(lia)).
   destruct (Peq_0_dec v) as [EQ|NE].
   { exists u. split; try easy. rewrite EQ, Pplus_0_r in Huv1.
     now rewrite Pmult_comm. }
   { assert (Rv : Root x v).
     { rewrite Huv1 in Hx'. red in Hx'. rewrite Pplus_eval, Pmult_eval in Hx'.
       rewrite Hx, Cmult_0_r, Cplus_0_l in Hx'. apply Hx'. }
     specialize (MIN v NE (proj2 Huv3) Rv). lia. }}
Qed.

Lemma MinPolyQ_unique x p q : MinPolyQ x p -> MinPolyQ x q -> Peq p q.
Proof.
 intros Hp Hq.
 destruct (MinPolyQ_unique_aux x p q Hp) as (u & Hu & E); try apply Hq.
 assert (D : degree p = degree q).
 { apply Nat.le_antisymm.
   - apply Hp; try apply Hq. rewrite <- topcoef_0_iff.
     replace (topcoef q) with 1. injection; lra. symmetry; apply Hq.
   - apply Hq; try apply Hp. rewrite <- topcoef_0_iff.
     replace (topcoef p) with 1. injection; lra. symmetry; apply Hp. }
 assert (Tp : topcoef p = 1) by apply Hp.
 assert (Tq : topcoef q = 1) by apply Hq.
 assert (Hu' : monic u).
 { assert (E' : topcoef q = topcoef (p*,u)) by now rewrite E.
   rewrite topcoef_mult, Tp, Tq, Cmult_1_l in E'. now symmetry in E'. }
 rewrite E in D. rewrite Pmult_degree in D.
 2:{ change (~Peq p []). rewrite <- topcoef_0_iff, Tp. injection; lra. }
 2:{ change (~Peq u []). rewrite <- topcoef_0_iff, Hu'. injection; lra. }
 rewrite (deg0_monic_carac u), Pmult_1_r in E; lia || easy.
Qed.

Lemma MinPolyQ_Qirred x p : MinPolyQ x p -> ~Qreducible p.
Proof.
 intros (MO & RP & Hx & MIN) (p1 & p2 & E & H1 & H2 & D).
 assert (E' : Peval (p1 *, p2) x = 0) by now rewrite <- E, Hx.
 assert (N1 : ~ Peq p1 []).
 { intros E1. rewrite E1 in D. unfold degree in D; simpl in D. lia. }
 assert (N2 : ~ Peq p2 []).
 { intros E2. rewrite E2, Pmult_0_r in E. rewrite E in D.
   unfold degree in D; simpl in D. lia. }
 rewrite Pmult_eval in E'. apply Cmult_integral in E'. destruct E' as [E'|E'].
 - generalize (MIN p1 N1 H1 E'). lia.
 - generalize (MIN p2 N2 H2 E').
   rewrite E, Pmult_degree in D |- *; try apply N1; try apply N2. lia.
Qed.

Lemma MinPolyQ_alt x p :
  MinPolyQ x p <-> monic p /\ RatPoly p /\ Root x p /\ ~Qreducible p.
Proof.
 split.
 - intros Hp. repeat split; try apply Hp. now apply (MinPolyQ_Qirred x p).
 - intros (MO & RP & Hx & IR).
   assert (NZ : ~Peq p []).
   { rewrite <- topcoef_0_iff. rewrite MO. injection;lra. }
   destruct (RootQ_has_MinPolyQ x (ex_intro _ p (conj NZ (conj RP Hx))))
     as (q & Hq).
   destruct (MinPolyQ_unique_aux x q p Hq RP Hx) as (u & RPu & E).
   assert (D : ~(0 < degree q < degree p)%nat).
   { contradict IR. exists q, u. repeat (split; try assumption). apply Hq. }
   destruct (Nat.eq_dec (degree q) 0) as [D'|D'].
   + destruct Hq as (MO' & RP' & Hx' & _).
     rewrite (deg0_monic_carac q) in Hx'; trivial.
     red in Hx'. rewrite Pconst_eval in Hx'. injection Hx'; lra.
   + assert (degree p <= degree q)%nat by lia.
     repeat split; trivial.
     intros r Hr1 Hr2 Hr3. apply Nat.le_trans with (degree q); trivial.
     now apply Hq.
Qed.

Lemma PisotPoly_minimal x p : PisotPoly x p -> MinPolyQ x p.
Proof.
 intros Hp.
 assert (Mp : monic p).
 { destruct Hp as (l & Hl & Hl'). red. rewrite Hl'.
   apply linfactors_monic. }
 rewrite MinPolyQ_alt; repeat split; trivial.
 - apply PisotIntPoly in Hp. rewrite IntPoly_alt in Hp.
   destruct Hp as (p' & ->).
   rewrite RatPoly_alt. exists (map inject_Z p').
   unfold Zpoly, Qpoly. rewrite map_map. unfold "∘". apply map_ext.
   intros z. now rewrite Q2R_IZR.
 - now apply PisotPolyRoot.
 - intros Hp'. apply (PisotPolyIrred x p); trivial.
   apply GaussLemma; trivial. eapply PisotIntPoly; eauto.
Qed.

Lemma PisotPolyUnique x p q : PisotPoly x p -> PisotPoly x q -> Peq p q.
Proof.
 intros. apply (MinPolyQ_unique x); now apply PisotPoly_minimal.
Qed.

(** TODO: move here the begin of SecondRoot
    + cleanup of SecondRoot
    AND finish other moves
*)

(** Siegel Theorem : the smallest Pisot number is the Plastic Ratio.
    (Ref: Algbraic numbers whose conjugates lie in the unit circle, 1944) *)

Module SiegelProof.
Section Siegel.
Variable root : R.
Hypothesis Hroot : root^2 < 2.
Variable roots : (list C).
Hypothesis Hroots : PisotConjugates root roots.
Variable coefs : list Z.
Hypothesis Hcoefs : Peq (Zpoly coefs) (linfactors (RtoC root::roots)).

Lemma roots_nz : ~In 0 roots.
Proof.
 intros IN. destruct Hroots as (_ & _ & H).
 rewrite Forall_forall in H. specialize (H _ IN).
 rewrite Cmod_0 in H. lra.
Qed.

Lemma invroot : 0 < /root < 1.
Proof.
 split.
 - apply Rinv_0_lt_compat; red in Hroots; lra.
 - rewrite <- Rinv_1. apply Rinv_lt_contravar; red in Hroots; lra.
Qed.

Ltac lra' := (red in Hroots; generalize invroot; lra).
Ltac nra' := (red in Hroots; generalize invroot; nra).

Lemma roots_nz' : ~In 0 (RtoC root :: roots).
Proof.
 simpl. intros [[= H]|H]. lra'. now apply roots_nz.
Qed.

Local Notation Pcoef := (Zpoly coefs).

Lemma Root_nz : ~Root 0 Pcoef.
Proof.
 rewrite Hcoefs, <- linfactors_roots. apply roots_nz'.
Qed.

Local Notation sgn := (Z.sgn (nth 0 coefs Z0)).

Definition f (x:C) := IZR sgn * Peval Pcoef x / Peval (reciprocal Pcoef) x.

Lemma ff x : ~Root x Pcoef -> ~Root (/x) Pcoef -> x <> 0 -> f x * f (/x) = 1.
Proof.
 intros H1 H2 H3. unfold f.
 rewrite !Peval_reciprocal, Cinv_inv, Cpow_inv; trivial.
 2:{ now apply nonzero_div_nonzero. }
 2:{ contradict H1. now rewrite H1. }
 2:{ contradict H1. now rewrite H1. }
 field_simplify.
 2:{ repeat split; trivial. now apply Cpow_nz. }
 { unfold sgn.
   generalize Root_nz.
   unfold Root. rewrite Peval_0, coef_Zpoly.
   destruct nth; simpl; intros; easy || ring. }
Qed.

Definition fps :=
  CPS_mult (PS_poly ([IZR sgn * /Peval Pcoef 0] *, Pcoef))
           (PS_inv_linfactors (map Cinv (RtoC root::roots))).

Lemma invroot_le_min_Cmod :
  Rbar.Rbar_le (/ root)%R (min_Cmod_list (map Cinv (RtoC root :: roots))).
Proof.
 unfold min_Cmod_list. simpl map.
 cbn -[Rbar.Rbar_min Rbar.Rbar_le].
 apply Rbar.Rbar_min_case.
 - rewrite <- RtoC_inv, Cmod_R, Rabs_pos_eq. now simpl. lra'.
 - change (Rbar.Rbar_le (/root)%R (min_Cmod_list (map Cinv roots))).
   apply Rbar.Rbar_lt_le. apply min_Cmod_list_spec, Forall_forall.
   intros y. rewrite in_map_iff. intros (z & <- & IN).
   red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
   rewrite Cmod_inv.
   apply Rinv_lt_contravar. apply Rmult_lt_0_compat; lra. lra.
Qed.

Lemma fps_radius : Rbar.Rbar_le (/root)%R (C_CV_radius fps).
Proof.
 unfold fps.
 eapply Rbar.Rbar_le_trans; [|apply C_CV_radius_mult].
 rewrite PS_poly_radius.
 apply Rbar.Rbar_min_case; [simpl; trivial|].
 eapply Rbar.Rbar_le_trans; [|apply PS_inv_linfactors_radius].
 - apply invroot_le_min_Cmod.
 - rewrite in_map_iff. intros (r & Hr & IN).
   rewrite Cinv_eq_0_iff in Hr. subst r. now apply roots_nz'.
Qed.

Lemma below_invroot x : Cmod x < / root -> x <> 0 -> ~Root (/ x) Pcoef.
Proof.
 intros H1 H2.
 rewrite Hcoefs.
 intros H. apply linfactors_roots in H. simpl in H. destruct H.
 - replace x with (/root) in H1.
   2:{ now rewrite H, Cinv_inv. }
   rewrite <- RtoC_inv, Cmod_R in H1.
   generalize (Rle_abs (/root)%R); lra.
 - red in Hroots. rewrite Forall_forall in Hroots.
   apply Hroots in H. rewrite Cmod_inv in H.
   apply Rinv_lt_contravar in H1. rewrite Rinv_inv in H1. lra.
   apply Rmult_lt_0_compat; apply Cmod_gt_0 in H2; lra.
Qed.

Lemma fps_ok x : Cmod x < /root -> is_CPowerSeries fps x (f x).
Proof.
 intros Hx.
 unfold fps.
 replace (f x) with ((IZR sgn * /Peval Pcoef 0 * Peval Pcoef x) *
                     (Peval Pcoef 0 * /Peval (reciprocal Pcoef) x)).
 2:{ unfold f. field. split; try apply Root_nz.
     destruct (Ceq_dec x 0) as [Y|N].
     - subst. rewrite Peval_reciprocal_0.
       rewrite Hcoefs, linfactors_monic. intros [=H]; lra.
     - rewrite Peval_reciprocal; trivial.
       + intros H. apply Cmult_integral in H. destruct H.
         apply below_invroot in H; trivial.
         now apply (Cpow_nz x (degree Pcoef)) in N.
       + rewrite <- topcoef_0_iff.
         rewrite Hcoefs, linfactors_monic. intros [=H]; lra. }
 apply is_CPS_mult.
 - rewrite <- (Pconst_eval (_ * /Peval _ 0) x) at 2.
   rewrite <- Pmult_eval. apply PS_poly_ok.
 - rewrite Hcoefs, reciprocal_revfactors by apply roots_nz'.
   rewrite Pmult_eval, Pconst_eval.
   rewrite Cinv_mult, Cmult_assoc, Cinv_r, Cmult_1_l.
   2:{ rewrite <- Hcoefs. apply Root_nz. }
   unfold revfactors.
   apply PS_inv_linfactors_ok.
   rewrite <- min_Cmod_list_spec.
   eapply Rbar.Rbar_lt_le_trans; [|apply invroot_le_min_Cmod]. apply Hx.
 - now rewrite PS_poly_radius.
 - eapply Rbar.Rbar_lt_le_trans; [|apply PS_inv_linfactors_radius].
   2:{ rewrite in_map_iff. intros (y & Hy & IN).
       rewrite Cinv_eq_0_iff in Hy. rewrite Hy in IN. now apply roots_nz'. }
   eapply Rbar.Rbar_lt_le_trans; [|apply invroot_le_min_Cmod]. apply Hx.
Qed.

Lemma fps_eqn n :
  CPS_mult fps (PS_poly (reciprocal Pcoef)) n =
  PS_poly ([RtoC sgn] *, Pcoef) n.
Proof.
 apply CPowerSeries_coef_ext.
 - eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
   rewrite PS_poly_radius.
   apply Rbar.Rbar_min_case; [|simpl; trivial].
   eapply Rbar.Rbar_lt_le_trans; [|apply fps_radius; trivial]. simpl. lra'.
 - now rewrite PS_poly_radius.
 - assert (Hr : 0 < /root) by lra'.
   exists (mkposreal _ Hr). intros y Hy.
   change (Rabs (y-R0) < /root) in Hy. rewrite Rminus_0_r in Hy.
   rewrite <- Cmod_R in Hy.
   rewrite CPowerSeries_mult.
   2:{ eapply Rbar.Rbar_lt_le_trans; [|apply fps_radius]; trivial. }
   2:{ now rewrite PS_poly_radius. }
   do 2 rewrite (CPowerSeries_unique _ _ _ (PS_poly_ok _ _)).
   rewrite (CPowerSeries_unique _ _ _ (fps_ok _ Hy)).
   rewrite Pmult_eval, Pconst_eval.
   unfold f. field.
   { destruct (Ceq_dec y 0) as [->|N].
     - rewrite Peval_reciprocal_0.
       rewrite Hcoefs, linfactors_monic. intros [=H]; lra.
     - rewrite Peval_reciprocal; trivial.
       2:{ rewrite <- topcoef_0_iff.
           rewrite Hcoefs, linfactors_monic. intros [=H]; lra. }
       intros H. apply Cmult_integral in H. destruct H.
       apply below_invroot in H; trivial.
       now apply (Cpow_nz y (degree Pcoef)) in N. }
Qed.

Lemma fps_CInteger n : CInteger (fps n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 generalize (fps_eqn n).
 unfold PS_poly. rewrite Pscale_coef.
 unfold CPS_mult. rewrite coef_Zpoly, <- RtoC_mult, <- mult_IZR.
 rewrite <- big_sum_sum_n, <- big_sum_extend_r.
 simpl. replace (n-n)%nat with 0%nat by lia.
 rewrite <- Peval_0, Peval_reciprocal_0.
 rewrite Hcoefs, linfactors_monic, Cmult_1_r.
 set (bs := big_sum _ _).
 intros E. replace (fps n) with (IZR (sgn * nth n coefs 0%Z) - bs).
 2:{ rewrite <- E. lca. }
 clear E.
 apply CInteger_plus. rewrite CInteger_alt. now eexists.
 replace (-bs) with ((-1)*bs) by ring.
 apply CInteger_mult. rewrite CInteger_alt. now exists (-1)%Z.
 apply CInteger_big_sum.
 intros k Hk. apply CInteger_mult. now apply IH.
 destruct (Nat.le_gt_cases (n-k) (degree Pcoef)).
 - rewrite reciprocal_coef by trivial. apply IntPoly_coef.
   rewrite IntPoly_alt. now eexists.
 - rewrite reciprocal_coef_0 by trivial.
   rewrite CInteger_alt. now exists 0%Z.
Qed.

Definition g x :=
  IZR sgn * Peval Pcoef x / Peval (reciprocal (linfactors roots)) x.

Definition g_f x : x <> /root -> g x = (1-root*x) * f x.
Proof.
 intros Hx.
 unfold g, f, Cdiv. rewrite !Cmult_assoc.
 rewrite (Cmult_comm (_-_)). rewrite <- !Cmult_assoc. f_equal.
 rewrite (Cmult_comm (_-_)). rewrite <- !Cmult_assoc. f_equal.
 rewrite Hcoefs, reciprocal_linfactors_cons by apply roots_nz'.
 rewrite Pmult_eval.
 rewrite Cinv_mult, Cmult_comm, Cmult_assoc.
 rewrite <- (Cmult_1_l (/ _)) at 1. f_equal.
 unfold Peval. simpl. field. simpl. contradict Hx.
 apply Cmult_eq_reg_l with (RtoC root).
 2:{ generalize roots_nz'. simpl; tauto. }
 rewrite Cinv_r. 2:{ generalize roots_nz'. simpl; tauto. }
 symmetry. apply Cminus_eq_0. rewrite <- Hx. ring.
Qed.

Definition gps :=
  CPS_mult (PS_poly ([IZR sgn * /Peval (linfactors roots) 0] *, Pcoef))
           (PS_inv_linfactors (map Cinv roots)).

Lemma gps_radius : Rbar.Rbar_lt 1%R (C_CV_radius gps).
Proof.
 unfold gps.
 eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
 rewrite PS_poly_radius.
 apply Rbar.Rbar_min_case; [simpl; trivial|].
 eapply Rbar.Rbar_lt_le_trans; [|apply PS_inv_linfactors_radius].
 - apply min_Cmod_list_spec, Forall_forall.
   intros x. rewrite in_map_iff. intros (y & <- & IN).
   red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
   rewrite Cmod_inv, <- Rinv_1. apply Rinv_lt_contravar; lra.
 - rewrite in_map_iff. intros (r & Hr & IN).
   rewrite Cinv_eq_0_iff in Hr. subst r. now apply roots_nz.
Qed.

Lemma below_1 x : Cmod x <= 1 -> x <> 0 -> ~Root (/ x) (linfactors roots).
Proof.
 intros H1 H2.
 intros H. apply linfactors_roots in H.
 red in Hroots. rewrite Forall_forall in Hroots.
 apply Hroots in H. rewrite Cmod_inv in H.
 apply Rinv_le_contravar in H1. rewrite Rinv_1 in H1; lra.
 apply Cmod_gt_0 in H2; lra.
Qed.

Lemma gps_ok x :
  Cmod x <= 1 -> is_CPowerSeries gps x (g x).
Proof.
 intros Hx.
 unfold gps.
 replace (g x) with ((IZR sgn * /Peval (linfactors roots) 0 * Peval Pcoef x) *
     (Peval (linfactors roots) 0 * /Peval (reciprocal (linfactors roots)) x)).
 2:{ unfold g. field. split.
     2:{ change (~Root 0 (linfactors roots)).
         rewrite <- linfactors_roots. apply roots_nz. }
     destruct (Ceq_dec x 0) as [Y|N].
     - subst. rewrite Peval_reciprocal_0.
       rewrite linfactors_monic. intros [=H]; lra.
     - rewrite Peval_reciprocal; trivial.
       + intros H. apply Cmult_integral in H. destruct H.
         apply below_1 in H; trivial.
         now apply (Cpow_nz x (degree (linfactors roots))) in N.
       + rewrite <- topcoef_0_iff.
         rewrite linfactors_monic. intros [=H]; lra. }
 apply is_CPS_mult.
 - rewrite <- (Pconst_eval (_ * /Peval _ 0) x) at 2.
   rewrite <- Pmult_eval. apply PS_poly_ok.
 - rewrite reciprocal_revfactors by apply roots_nz.
   rewrite Pmult_eval, Pconst_eval.
   rewrite Cinv_mult, Cmult_assoc, Cinv_r, Cmult_1_l.
   2:{ change (~Root 0 (linfactors roots)).
       rewrite <- linfactors_roots. apply roots_nz. }
   unfold revfactors.
   apply PS_inv_linfactors_ok.
   apply Forall_forall. intros y. rewrite in_map_iff. intros (z & <- & IN).
   red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
   rewrite Cmod_inv. eapply Rle_lt_trans; eauto. rewrite <- Rinv_1.
   apply Rinv_lt_contravar; lra.
 - now rewrite PS_poly_radius.
 - eapply Rbar.Rbar_lt_le_trans; [|apply PS_inv_linfactors_radius].
   2:{ rewrite in_map_iff. intros (y & Hy & IN).
       rewrite Cinv_eq_0_iff in Hy. rewrite Hy in IN. now apply roots_nz. }
   apply min_Cmod_list_spec, Forall_forall.
   intros y. rewrite in_map_iff. intros (z & <- & IN).
   red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
   rewrite Cmod_inv. eapply Rle_lt_trans; eauto. rewrite <- Rinv_1.
   apply Rinv_lt_contravar; lra.
Qed.

Lemma gps_eqn n : gps n = CPS_mult fps (PS_poly [1;-root]) n.
Proof.
 apply CPowerSeries_coef_ext.
 - eapply Rbar.Rbar_lt_trans; [|apply gps_radius; trivial]. simpl. lra.
 - eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
   rewrite PS_poly_radius.
   apply Rbar.Rbar_min_case; [|simpl; trivial].
   eapply Rbar.Rbar_lt_le_trans; [|apply fps_radius; trivial]. simpl; lra'.
 - assert (Hr : 0 < /root) by lra'.
   exists (mkposreal _ Hr). intros y Hy.
   change (Rabs (y-R0) < /root) in Hy. rewrite Rminus_0_r in Hy.
   rewrite <- Cmod_R in Hy.
   rewrite CPowerSeries_mult.
   2:{ eapply Rbar.Rbar_lt_le_trans; [|apply fps_radius]; trivial. }
   2:{ now rewrite PS_poly_radius. }
   rewrite (CPowerSeries_unique _ _ _ (PS_poly_ok _ _)).
   rewrite (CPowerSeries_unique _ _ _ (fps_ok _ Hy)).
   assert (Hy' : Cmod y <= 1).
   { apply Rle_trans with (/root)%R; try lra. rewrite <- Rinv_1.
     red in Hroots. apply Rinv_le_contravar; lra. }
   rewrite (CPowerSeries_unique _ _ _ (gps_ok _ Hy')).
   rewrite cons_eval, Pconst_eval. rewrite g_f. ring.
   intros H. rewrite H in Hy. rewrite <- RtoC_inv, Cmod_R in Hy.
   generalize (Rle_abs (/root)); lra.
Qed.

Lemma gps_square : ex_series (fun n => (gps n)^2).
Proof.
 apply ex_series_Cmod.
 eapply ex_series_ext.
 { intros n. unfold "∘". symmetry. now rewrite Cmod_pow. }
 apply ex_series_square. rewrite <- ex_pseries_1. apply CV_radius_inside.
 unfold "∘".
 erewrite CV_radius_ext.
 2:{ intros n. now rewrite Rabs_pos_eq by apply Cmod_ge_0. }
 change (fun n => Cmod (gps n)) with (Cmod ∘ gps).
 rewrite <- C_CV_radius_alt. rewrite Rabs_pos_eq by lra.
 apply gps_radius.
Qed.

Lemma One_aux : 1 + root^2 = CSeries (fun n => (gps n)^2).
Proof.
 rewrite <- SecondRoot.Mu_series_square with (g:=g).
 2:{ rewrite <- ex_pseries_1. apply CV_radius_inside.
     rewrite <- C_CV_radius_alt. rewrite Rabs_pos_eq by lra.
     apply gps_radius. }
 2:{ intros z Hz. symmetry. apply CPowerSeries_unique, gps_ok. lra. }
 symmetry. unfold SecondRoot.Mu.
 rewrite (RInt_ext (V:=C_CNM))
  with (g := fun t => (1 - root * Cexp t)*(1 - root * Cexp (-t))).
 2:{ intros t _. rewrite !g_f.
     2:{ intros E. apply (f_equal Cmod) in E. rewrite Cmod_Cexp in E.
         rewrite Cmod_inv, Cmod_R, Rabs_pos_eq in E by lra'.
         apply (f_equal Rinv) in E. rewrite Rinv_1, Rinv_inv in E.
         red in Hroots; lra. }
     2:{ intros E. apply (f_equal Cmod) in E. rewrite Cmod_Cexp in E.
         rewrite Cmod_inv, Cmod_R, Rabs_pos_eq in E; lra'. }
     rewrite (Cmult_comm _ (f (Cexp (-t)))).
     rewrite !Cmult_assoc. f_equal.
     rewrite <- Cmult_assoc. rewrite <- (Cmult_1_r (1 - _)) at 2. f_equal.
     rewrite Cexp_neg. apply ff.
     { rewrite Hcoefs. rewrite <- linfactors_roots.
       intros [E|IN].
       - apply (f_equal Cmod) in E. rewrite Cmod_Cexp in E.
         rewrite Cmod_R, Rabs_pos_eq in E; lra'.
       - red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
         rewrite Cmod_Cexp in IN; lra. }
     { rewrite Hcoefs. rewrite <- linfactors_roots, <- Cexp_neg.
       intros [E|IN].
       - apply (f_equal Cmod) in E. rewrite Cmod_Cexp in E.
         rewrite Cmod_R, Rabs_pos_eq in E; lra'.
       - red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
         rewrite Cmod_Cexp in IN; lra. }
     { apply Cexp_nonzero. }}
 rewrite (RInt_ext (V:=C_CNM))
  with (g := fun t => (1 + root ^2) - root * (Cexp t - - Cexp (-t))).
 2:{ intros t _. fixeq C. ring_simplify.
     rewrite <- (Cmult_assoc _ (Cexp _) (Cexp _)).
     rewrite Cexp_mul_neg_r. ring. }
 rewrite CInt_minus.
 2:{ apply (ex_RInt_continuous (V:=C_CNM)); intros x _.
     apply continuous_const. }
 2:{ apply (ex_RInt_continuous (V:=C_CNM)); intros x _.
     apply continuous_Cmult. apply continuous_const.
     apply (continuous_plus (V:=C_NM)). apply continuous_Cexp.
     apply (continuous_opp (V:=C_NM)). apply (continuous_opp (V:=C_NM)).
     apply continuous_comp; trivial.
     apply (continuous_opp (V:=R_NM)), continuous_id.
     apply continuous_Cexp. }
 rewrite CInt_const.
 rewrite !CInt_scal.
 2:{ apply (ex_RInt_continuous (V:=C_CNM)); intros x _.
     apply (continuous_plus (V:=C_NM)). apply continuous_Cexp.
     apply (continuous_opp (V:=C_NM)). apply (continuous_opp (V:=C_NM)).
     apply continuous_comp; trivial.
     apply (continuous_opp (V:=R_NM)), continuous_id.
     apply continuous_Cexp. }
 replace (CInt _ _ _) with (0-0).
 rtoc. field. intros [=E]. now apply PI_neq0.
 symmetry.
 rewrite CInt_minus.
 2:{ apply (ex_RInt_continuous (V:=C_CNM)); intros x _.
     apply continuous_Cexp. }
 2:{ apply (ex_RInt_continuous (V:=C_CNM)); intros x _.
     apply (continuous_opp (V:=C_NM)).
     apply continuous_comp; trivial.
     apply (continuous_opp (V:=R_NM)), continuous_id.
     apply continuous_Cexp. }
 f_equal; apply is_CInt_unique.
 - generalize (is_CInt_Cexp 1 lia). apply is_RInt_ext.
   intros x _. f_equal. now rewrite Rmult_1_l.
 - apply (is_RInt_comp_opp (V:=C_NM)).
   rewrite Ropp_0, Ropp_mult_distr_l.
   generalize (is_CInt_Cexp' 1 lia). apply is_RInt_ext.
   intros x _. f_equal. now rewrite Rmult_1_l.
Qed.

Lemma gps_0 : gps 0 = fps 0.
Proof.
 rewrite gps_eqn.
 unfold CPS_mult. rewrite <- big_sum_sum_n. unfold PS_poly, coef. simpl.
 ring.
Qed.

Lemma gps_S n : gps (S n) = fps (S n) - root * fps n.
Proof.
 rewrite gps_eqn.
 unfold CPS_mult. rewrite <- big_sum_sum_n.
 cbn -[Nat.sub PS_poly].
 rewrite big_sum_0_bounded.
 2:{ intros x Hx. unfold PS_poly, coef. rewrite nth_overflow.
     simpl. ring. simpl length. lia. }
 replace (S n-n)%nat with 1%nat by lia.
 replace (S n-S n)%nat with 0%nat by lia.
 unfold PS_poly, coef; simpl. ring.
Qed.

Lemma One :
  1 + root^2 = (fps 0)^2 + CSeries (fun n => (fps (S n) - root * fps n)^2).
Proof.
 rewrite One_aux. rewrite CSeries_incr_1 by apply gps_square.
 f_equal.
 - now rewrite gps_0.
 - unfold "∘". apply CSeries_ext. intros n. f_equal. apply gps_S.
Qed.

Lemma fps_0 : fps 0 = Z.abs (nth 0 coefs Z0).
Proof.
 generalize (fps_eqn 0).
 unfold CPS_mult, PS_poly. rewrite Pscale_coef, sum_O, reciprocal_coef by lia.
 rewrite Nat.sub_0_r, <- topcoef_alt.
 rewrite Hcoefs at 1. rewrite linfactors_monic, Cmult_1_r.
 intros ->. rewrite coef_Zpoly.
 rewrite <- RtoC_mult, <- mult_IZR. f_equal. f_equal. lia.
Qed.

Lemma coefs0_nz : nth 0 coefs Z0 <> Z0.
Proof.
 intros E.
 apply roots_nz'. rewrite linfactors_roots, <- Hcoefs. red.
 now rewrite Peval_0, coef_Zpoly, E.
Qed.

Definition fps' : nat -> Z := fun n => Int_part (Re (fps n)).

Lemma fps_eqn' n : fps n = IZR (fps' n).
Proof.
 unfold fps'. apply CInteger_intpart. apply fps_CInteger.
Qed.

Lemma diff_f'_square_ex :
  ex_series (fun n => (fps' (S n) - root * fps' n) ^ 2)%R.
Proof.
 assert (E := gps_square).
 apply ex_series_incr_1 in E. unfold "∘" in E.
 eapply ex_series_ext in E.
 2:{ intros n. rewrite gps_S, 2 fps_eqn'. ctor. reflexivity. }
 apply ex_series_RtoC, E.
Qed.

Lemma One' :
 (1 + root^2 =
  (fps' 0)^2 + Series (fun n => (fps' (S n) - root * fps' n)^2))%R.
Proof.
 apply RtoC_inj. rtoc. rewrite One.
 rewrite fps_eqn'. f_equal.
 rewrite <- CSeries_RtoC. apply CSeries_ext.
 { intros n. unfold "∘". rewrite 2 fps_eqn'. now ctor. }
 apply diff_f'_square_ex.
Qed.

Lemma no_degree_0 : degree Pcoef <> 0%nat.
Proof.
 rewrite Hcoefs, linfactors_degree. discriminate.
Qed.

Lemma no_degree_1 : degree Pcoef <> 1%nat.
Proof.
 intros D.
 assert (2 <= root); try nra.
 { rewrite Hcoefs, linfactors_degree in D. simpl in D.
   injection D as D. rewrite length_zero_iff_nil in D.
   rewrite D  in Hcoefs. simpl in Hcoefs.
   rewrite !Cmult_1_l, Cplus_0_r in Hcoefs.
   assert (H : Integer root).
   { rewrite Integer_alt. exists (Z.opp (nth 0 coefs Z0)).
     rewrite opp_IZR. apply RtoC_inj. rewrite RtoC_opp.
     change (RtoC (IZR (nth 0 coefs Z0))) with ((RtoC∘IZR) (nth 0 coefs Z0)).
     rewrite <- map_nth. change (map _ coefs) with (Zpoly coefs).
     change (nth _ _ _) with (coef 0 (Zpoly coefs)).
     rewrite Hcoefs. unfold coef. simpl. now rewrite Copp_involutive. }
   red in Hroots. rewrite Integer_alt in H. destruct H as (n & H).
   rewrite H.
   apply IZR_le. assert (1 < n)%Z; try lia. apply lt_IZR. rewrite <- H.
   apply Hroots. }
Qed.

Lemma invroot_roots_then_degree_2 :
  In (/root) roots -> (degree Pcoef <= 2)%nat.
Proof.
 intros IN. rewrite <- Nat.nlt_ge. unfold lt. intros D.
 assert (E := Peval_0 Pcoef).
 rewrite Hcoefs in E at 1.
 rewrite Peval_linfactors in E.
 rewrite coef_Zpoly in E.
 destruct (in_split _ _ IN) as (l1 & l2 & L).
 rewrite L in E.
 set (opp := fun y => 0-y) in E.
 rewrite Gbigmult_perm with (l' := map opp (RtoC root::/root::l1++l2)) in E.
 2:{ symmetry. apply Permutation_map, perm_skip, Permutation_middle. }
 simpl in E. rewrite Cmult_assoc in E.
 replace (opp root * opp (/root)) with 1 in E.
 2:{ unfold opp. field. intros [=]; lra'. }
 rewrite Cmult_1_l in E.
 apply (f_equal Cmod) in E.
 rewrite G_big_mult_mod, map_map in E.
 rewrite map_ext with (g:=Cmod) in E.
 2:{ intros. unfold opp. rewrite <- (Cmod_opp a). f_equal. lca. }
 clear opp.
 set (g := G_big_mult _) in *.
 assert (LT : 0 < g < 1).
 { apply G_big_mult_small.
   - intros x Hx.
     rewrite in_map_iff in Hx. destruct Hx as (x' & <- & Hx').
     red in Hroots. rewrite Forall_forall in Hroots. apply Hroots.
     rewrite L. rewrite in_app_iff in *. simpl; tauto.
   - rewrite <- length_zero_iff_nil.
     rewrite map_length. rewrite Hcoefs, linfactors_degree in D.
     rewrite L in D. simpl in D. rewrite app_length in *. simpl in D.
     lia. }
 rewrite E in LT. rewrite Cmod_R, <- abs_IZR in LT.
 destruct LT as (LT1,LT2). apply lt_IZR in LT1, LT2. lia.
Qed.

Lemma invroot_roots_not_degree_2 : In (/root) roots -> degree Pcoef <> 2%nat.
Proof.
 intros IN D.
 assert (R : Root root Pcoef).
 { rewrite Hcoefs. apply linfactors_roots. now left. }
 assert (E : roots = [/root]).
 { rewrite Hcoefs, linfactors_degree in D. simpl in D.
   injection D as D.
   destruct roots as [|x l] eqn:E. discriminate D.
   simpl in D. injection D as D. rewrite length_zero_iff_nil in D.
   subst l. f_equal. simpl in IN. intuition. }
 clear IN D.
 rewrite E in Hcoefs.
 simpl in Hcoefs. rewrite !Cmult_1_l, Cmult_1_r, !Cplus_0_r in *.
 assert (INT : Integer (root+/root)).
 { rewrite Integer_alt. exists (Z.opp (nth 1 coefs Z0)).
   rewrite opp_IZR. apply RtoC_inj. rewrite RtoC_opp.
   change (RtoC (IZR (nth 1 coefs Z0))) with ((RtoC∘IZR) (nth 1 coefs Z0)).
   rewrite <- map_nth. change (map _ coefs) with (Zpoly coefs).
   change (nth _ _ _) with (coef 1 (Zpoly coefs)).
   rewrite Hcoefs. unfold coef. simpl. rtoc. ring. }
 assert (1 < root + /root).
 { destruct Hroots as (LT & _). generalize (Rinv_0_lt_compat root). lra. }
 assert (N : root + /root <> 2).
 { intros E'.
   replace (-/root*-root) with 1 in Hcoefs.
   2:{ field. destruct Hroots as (LT & _). intros [= H']. lra. }
   rewrite <- Copp_plus_distr, Cplus_comm, E' in Hcoefs.
   assert (Hp : Peq Pcoef (linfactors [1;1])).
   { rewrite Hcoefs. simpl. apply eq_Peq.
     f_equal. ring. f_equal. ring. f_equal. ring. }
   rewrite Hp in R. apply linfactors_roots in R. simpl in R.
   destruct Hroots as (LT & _). destruct R as [[= R]|[[= R]|[ ]]]; lra. }
 assert (3 <= root + /root).
 { rewrite Integer_alt in INT. destruct INT as (n & Hn).
   rewrite Hn in H |- *. apply lt_IZR in H. apply IZR_le.
   rewrite <- RtoC_inv, <- RtoC_plus, Hn in N.
   assert (n <> 2%Z). { contradict N. now subst. }
   lia. }
 nra'.
Qed.

Lemma invroot_no_roots : ~In (/root) roots.
Proof.
 intros IN.
 generalize
   (invroot_roots_then_degree_2 IN)
   (invroot_roots_not_degree_2 IN) no_degree_0 no_degree_1.
 destruct (degree Pcoef) as [|[|[|d]]]; lia.
Qed.

Section ReciprocalScal.
Variable c : C.
Hypothesis Hc : c <> 0.
Hypothesis Eq : Peq Pcoef ([c] *, reciprocal Pcoef).

Lemma ReciprocalScal_roots_carac r : In r roots -> r = /root.
Proof.
 intros Hr. destruct Hroots as (H1 & _ & H2). rewrite Forall_forall in H2.
 assert (Hr' : Root r Pcoef).
 { rewrite Hcoefs, <- linfactors_roots. now right. }
 rewrite Eq in Hr'. red in Hr'.
 rewrite Pmult_eval, Pconst_eval in Hr'. apply Cmult_integral in Hr'.
 destruct Hr' as [Hr'|Hr']; [easy|].
 apply reciprocal_root in Hr'.
 2:{ apply Cmod_gt_0. now apply H2. }
 rewrite Hcoefs in Hr'. apply linfactors_roots in Hr'.
 destruct Hr' as [Hr'|Hr'].
 - now rewrite Hr', Cinv_inv.
 - apply H2 in Hr, Hr'. destruct Hr' as (H3,H4).
   rewrite Cmod_inv in H4. rewrite <- Rinv_1 in H4.
   apply Rcomplements.Rinv_lt_cancel in H4; lra.
Qed.

Lemma NoReciprocalScal : False.
Proof.
 assert (H1 := no_degree_1).
 rewrite Hcoefs in H1. rewrite linfactors_degree in H1. simpl in H1.
 assert (E := ReciprocalScal_roots_carac).
 apply invroot_no_roots.
 destruct roots as [|r l]. simpl in H1; lia.
 rewrite (E r); now left.
Qed.

End ReciprocalScal.

Section fps_eventually_zero.

Hypothesis fps1z : fps 1 = 0.

Lemma fps1z_const : forall n, fps n = PS_poly [1] n.
Proof.
 assert (LE0 : 1 <= fps' 0).
 { assert (E := fps_0). rewrite fps_eqn' in E. injection E as E.
   rewrite E. apply IZR_le. generalize coefs0_nz; lia. }
 assert (LE0' : 1 <= (fps' 0)^2).
 { apply Rsqr_incr_1 in LE0; try lra. now rewrite Rsqr_1, Rsqr_pow2 in LE0. }
 assert (E := One').
 set (d := fun n => _) in E.
 rewrite Series_incr_1 in E by apply diff_f'_square_ex.
 rewrite fps_eqn' in fps1z. injection fps1z as fps1z.
 unfold d at 1 in E. rewrite fps1z in E.
 replace ((0-_)^2)%R with ((fps' 0)^2*root^2)%R in E by ring.
 assert (0 <= Series (fun n => d (S n))).
 { replace 0%R with (Series (fun _ => 0%R)).
   2:{ apply is_series_unique. apply is_series_R0. }
   apply Series_le.
   - intros m. split; try lra.
     unfold d. rewrite <- Rsqr_pow2. apply Rle_0_sqr.
   - assert (H := diff_f'_square_ex).
     rewrite <- ex_series_RtoC in H |- *.
     now rewrite ex_series_incr_1 in H. }
 assert (E0 : (fps' 0 = 1)%Z).
 { apply eq_IZR.
   rewrite <- (Rabs_pos_eq (fps' 0)) by lra.
   rewrite <- (Rabs_pos_eq 1) by lra.
   apply Rsqr_eq_abs_0. rewrite Rsqr_1, Rsqr_pow2. nra'. }
 assert (E' : Series (fun n => d (S n)) = 0%R) by nra'.
 clear E H.
 assert (D : forall n, d (S n) = 0%R).
 { apply is_series_null.
   - rewrite <- E'. apply Series_correct.
     assert (H := diff_f'_square_ex).
     rewrite <- ex_series_RtoC in H |- *.
     now rewrite ex_series_incr_1 in H.
   - intros m. unfold d. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
 unfold PS_poly, coef.
 induction n.
 - simpl. now rewrite fps_eqn', E0.
 - rewrite nth_overflow by (simpl; lia).
   destruct n.
   + now rewrite fps_eqn', fps1z.
   + specialize (D n). unfold d in D.
     rewrite nth_overflow, fps_eqn' in IHn by (simpl; lia).
     injection IHn as IHn. rewrite IHn in D.
     rewrite fps_eqn'. f_equal. nra.
Qed.

Lemma fps1z_p_eqn : Peq ([RtoC (IZR sgn)] *, Pcoef) (reciprocal Pcoef).
Proof.
 apply Peq_via_coef. intros n.
 change (coef n ([RtoC sgn] *, Pcoef)) with (PS_poly ([RtoC sgn] *, Pcoef) n).
 rewrite <- fps_eqn.
 rewrite <- (Pmult_1_l (reciprocal Pcoef)) at 2.
 change (coef n ([1] *, reciprocal Pcoef))
   with (PS_poly ([1] *, reciprocal Pcoef) n).
 rewrite <- CPS_mult_poly.
 unfold CPS_mult. apply sum_n_ext. intros m. now rewrite fps1z_const.
Qed.

Lemma fps1nz : False.
Proof.
 apply (NoReciprocalScal (IZR sgn)).
 - intros [=H]. apply eq_IZR in H.
   rewrite Z.sgn_null_iff in H. revert H. apply coefs0_nz.
 - rewrite <- fps1z_p_eqn, <- Pmult_assoc.
   replace ([_]*,[_]) with [1]. symmetry; apply Pmult_1_l.
   simpl. f_equal. rewrite Cplus_0_r, <- RtoC_mult, <- mult_IZR.
   f_equal. f_equal. unfold sgn.
   generalize coefs0_nz. now destruct nth.
Qed.

End fps_eventually_zero.

Lemma Two n : (fps' (n-1) <= fps' n)%Z.
Proof.
 induction n as [[|n] IH] using lt_wf_ind; try easy.
 simpl. rewrite Nat.sub_0_r.
 assert (LE : forall m, (m <= n)%nat -> (1 <= fps' m)%Z).
 { induction m.
   - intros _. unfold fps'. rewrite fps_0, re_RtoC, Int_part_IZR.
     generalize coefs0_nz.
     destruct (nth 0 coefs Z0) as [|x|x]; lia.
   - intros Hm. rewrite IHm by lia.
     replace m with (S m - 1)%nat at 1 by lia. apply IH. lia. }
 assert (LE0 : (1 <= fps' O)%Z) by (apply LE; lia).
 specialize (LE n lia).
 apply Z.le_ngt. intros LT.
 clear IH.
 assert (E := One').
 set (d := fun n => _) in E.
 assert (EX : ex_series (fun m => d (S n+m)%nat)).
 { rewrite <- ex_series_incr_n. apply diff_f'_square_ex. }
 assert (E' : (Series d = big_sum d (S n) + Series (fun m => d (S n+m)%nat))%R).
 { apply RtoC_inj. rtoc.
   rewrite big_sum_RtoC.
   rewrite <- 2 CSeries_RtoC; trivial using diff_f'_square_ex.
   rewrite CSeries_incr_n with (n:=S n); try easy.
   apply ex_series_RtoC. apply diff_f'_square_ex. }
 rewrite <- big_sum_extend_r in E'. change Gplus with Rplus in E'.
 assert (0 <= big_sum d n).
 { apply Rsum_ge_0. intros i _. unfold d. rewrite <- Rsqr_pow2.
   apply Rle_0_sqr. }
 assert (0 <= Series (fun m => d (S n+m)%nat)).
 { replace 0%R with (Series (fun _ => 0%R)).
   2:{ apply is_series_unique. apply is_series_R0. }
   apply Series_le.
   - intros m. split; try lra.
     unfold d. rewrite <- Rsqr_pow2. apply Rle_0_sqr.
   - rewrite <- ex_series_incr_n. apply diff_f'_square_ex. }
 assert (D : d n <= root^2).
 { apply Rplus_le_reg_l with 1%R. rewrite E, E'.
   apply IZR_le, Rsqr_incr_1 in LE0; try lra.
   rewrite Rsqr_1, Rsqr_pow2 in LE0.
   lra. }
 destruct (Z.le_gt_cases 0 (fps' (S n))) as [HSn|HSn].
 2:{ apply IZR_lt in HSn.
     unfold d in D. rewrite <- !Rsqr_pow2 in D.
     apply Rsqr_le_abs_0 in D.
     apply IZR_le in LE.
     rewrite Rabs_left in D by nra'.
     rewrite Rabs_right in D by lra'.
     assert (LT' : root * IZR (fps' n) < root * 1) by lra.
     apply Rmult_lt_reg_l in LT'; lra'. }
 destruct (Z.eq_dec 0 (fps' (S n))) as [HSn'|HSn'].
 2:{ apply (Rlt_irrefl (root^2)).
     eapply Rlt_le_trans; [|apply D].
     apply Rle_lt_trans with ((IZR (fps' n) - IZR (fps' (S n)))^2*root^2)%R.
     - rewrite <- (Rmult_1_l (root^2)) at 1.
       apply Rmult_le_compat_r. nra'.
       rewrite <- Rsqr_pow2, <- Rsqr_1. apply Rsqr_incr_1; try lra.
       + apply Zlt_le_succ, IZR_le in LT. rewrite succ_IZR in LT. lra.
       + apply IZR_lt in LT. lra.
     - unfold d. rewrite <- !Rsqr_pow2, <- Rsqr_mult.
       rewrite (Rsqr_neg (_-_)), Ropp_minus_distr, Rmult_comm.
       apply Rsqr_incrst_1.
       + apply Rminus_lt_0. ring_simplify.
         replace (_-_)%R with ((root-1)*IZR (fps' (S n)))%R by ring.
         apply Rmult_lt_0_compat. lra'. apply IZR_lt. lia.
       + apply Rmult_le_pos. lra'. apply IZR_lt in LT; lra.
       + replace (_-_)%R with
         (root*(IZR (fps' n) - IZR (fps' (S n))) +
          ((root-1)*IZR (fps' (S n))))%R by ring.
         apply Rplus_le_le_0_compat.
         * apply Rmult_le_pos. lra'. apply IZR_lt in LT; lra.
         * apply Rmult_le_pos. lra'. apply IZR_le. lia. }
 clear HSn.
 assert (Hn : fps' n = 1%Z).
 { apply Z.le_antisymm; trivial. apply le_IZR.
   unfold d in D. rewrite <- HSn' in D.
   rewrite <- !Rsqr_pow2 in D. unfold Rminus in D. rewrite Rplus_0_l in D.
   rewrite <- Rsqr_neg in D. rewrite Rsqr_mult in D.
   rewrite <- (Rmult_1_r (Rsqr root)) in D at 2.
   apply Rmult_le_reg_l in D. 2:{ apply Rlt_0_sqr. lra'. }
   rewrite <- Rsqr_1 in D.
   apply Rsqr_incr_0; trivial. apply IZR_le; lia. lra. }
 assert (D' : (d n = root^2)%R).
 { unfold d. rewrite <- HSn', Hn. ring. }
 assert (E0 : big_sum d n = 0%R).
 { apply Rle_antisym; trivial.
   apply IZR_le in LE0. apply Rsqr_incr_1 in LE0; try lra.
   rewrite Rsqr_1, Rsqr_pow2 in LE0. lra. }
 clear E E' H0 D D' EX.
 destruct n as [|n].
 - apply fps1nz. now rewrite fps_eqn', <- HSn'.
 - rewrite <- big_sum_extend_r in E0. change Gplus with Rplus in E0.
   assert (0 <= big_sum d n).
   { apply Rsum_ge_0. intros i _. unfold d. rewrite <- Rsqr_pow2.
     apply Rle_0_sqr. }
   assert (0 <= d n).
   { unfold d. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
   assert (D : d n = 0%R) by lra.
   unfold d in D. rewrite Hn, <- Rsqr_pow2 in D. apply Rsqr_eq_0 in D.
   assert (Hn' : (IZR (fps' n) = /root)%R).
   { apply Rmult_eq_reg_l with root. 2:{ lra'. }
     rewrite Rinv_r; try lra. lra'. }
   assert ((0 < fps' n < 1)%Z); try lia.
   { split; apply lt_IZR; rewrite Hn'; nra'. }
Qed.

Definition polypows (r:nat) (c:C) := map (Cpow c) (seq 0 r).

Lemma polypows_eqn (r:nat) (c:C) :
  Peq ((polypows r c) *, [1;-c]) ([1] +, monom (-c^r) r).
Proof.
 induction r.
 - simpl. replace (1+-(1)) with 0 by ring. symmetry. apply C0_Peq_nil.
 - unfold polypows. simpl map. rewrite <- seq_shift, map_map.
   assert (E : Peq (map (fun k => c^S k) (seq 0 r)) ([c] *, polypows r c)).
   { rewrite Pscale_alt. unfold polypows. rewrite map_map.
     apply eq_Peq. now apply map_ext. }
   rewrite E. clear E.
   cbn -[Pplus monom Cpow]. rewrite !Cmult_1_l.
   rewrite <- Pscale_alt.
   rewrite C0_Peq_nil, Pplus_0_r.
   rewrite Pmult_assoc, IHr.
   rewrite Pmult_plus_distr_l, Pmult_1_r.
   rewrite monom_scale, (monom_scale (-c^S r) (S r)).
   rewrite monom_S.
   rewrite <- Pmult_assoc.
   replace ([c] *, [-c^r]) with [-c^S r]. 2:{ simpl. f_equal. ring. }
   rewrite (Pmult_comm _ (0::_)), cons_0_mult, (Pmult_comm _ (monom _ _)).
   set (q := monom _ _ *, _).
   rewrite <- cons_simplify.
   change (Peq (1+0 :: ([-c] +, ([c]+,q))) (1::q)).
   rewrite <- Pplus_assoc.
   replace ([-c]+,[c]) with [0]. 2:{ simpl. f_equal. ring. }
   now rewrite C0_Peq_nil, Cplus_0_r.
Qed.

(* MOVE *)
Definition nthroot (x:R) (n:nat) := exp (ln x / n).

Lemma pow_via_exp x n : 0<x -> (x^n = exp (n * ln x))%R.
Proof.
 intros Hx.
 induction n.
 - simpl. now rewrite Rmult_0_l, exp_0.
 - rewrite <- Nat.add_1_r at 2. rewrite plus_INR. simpl.
   rewrite IHn. rewrite <- (exp_ln x) at 1 by trivial.
   rewrite <- exp_plus. f_equal. lra.
Qed.

Lemma exp_pow x n : (exp x ^ n)%R = exp (x*n).
Proof.
 rewrite pow_via_exp, ln_exp by apply exp_pos. f_equal. ring.
Qed.

Lemma nthroot_pow x n : n<>O -> 0 < x -> ((nthroot x n)^n = x)%R.
Proof.
 intros Hn Hx. unfold nthroot. rewrite exp_pow.
 rewrite <- (exp_ln x) at 2 by trivial. f_equal. field.
 contradict Hn. now apply INR_eq.
Qed.

Lemma pow_inj_l n x y : n<>O -> 0 <= x -> 0 <= y -> (x ^ n = y ^ n)%R -> x = y.
Proof.
 intros Hn Hx Hy H.
 apply Rle_antisym.
 - apply Rnot_lt_le. intros LT.
   apply (Rpow_lt_compat_r n) in LT; trivial. lra.
 - apply Rnot_lt_le. intros LT.
   apply (Rpow_lt_compat_r n) in LT; trivial. lra.
Qed.

Lemma Rpow_lt_reg_r n x y : 0 <= x -> 0 <= y -> x ^ n < y ^ n -> x < y.
Proof.
 intros Hx Hy.
 destruct n as [|n].
 { simpl. lra. }
 destruct (Req_dec x 0) as [Hx'|Hx'], (Req_dec y 0) as [Hy'|Hy'].
 - subst. simpl. lra.
 - lra.
 - subst. apply (pow_le x (S n)) in Hx. rewrite Rpow_0_l by easy. lra.
 - rewrite !pow_via_exp by lra.
   intros H. apply exp_lt_inv in H.
   apply Rmult_lt_reg_l in H; try apply RSpos.
   apply ln_lt_inv; lra.
Qed.

(* MOVE *)
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

Lemma C_CV_radius_dilate a k r : k<>O ->
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
     - apply (Rpow_lt_reg_r k); trivial. apply Rlt_le, exp_pos.
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

Lemma C_CV_radius_dilate' a k r : k<>O ->
 Rbar.Rbar_le (r^k)%R (C_CV_radius a) ->
 Rbar.Rbar_le r (C_CV_radius (PS_dilate a k)).
Proof.
 intros Hk H.
 apply Rbar_le_carac_via_lt. intros r' Hr'. simpl in Hr'.
 destruct (Rle_lt_dec 0 r') as [LE|LT].
 - apply Rbar.Rbar_lt_le. apply (C_CV_radius_dilate a k r'); trivial.
   eapply Rbar.Rbar_lt_le_trans; eauto.
   simpl. apply Rpow_lt_compat_r; trivial.
 - apply Rbar.Rbar_le_trans with 0%R. simpl; lra.
   rewrite C_CV_radius_alt. apply CV_radius_ge_0.
Qed.

Definition vr (r:nat) (x:C) := (1 - root^r*x^r)/(1-x^r/root^r).

(** An expression of [vr r * f] with factorization of the pole at [/root] *)

Definition gr (r:nat) (x:C) :=
  Peval (polypows r root) x / (1 - x^r/root^r) * g x.

Lemma gr_alt (r:nat) (x:C) : x<>/root -> gr r x = vr r x * f x.
Proof.
 intros Hx.
 unfold gr, vr.
 unfold Cdiv. rewrite !(Cmult_comm _ (/_)), <- !Cmult_assoc. f_equal.
 rewrite g_f by trivial. rewrite Cmult_assoc. f_equal.
 replace (1-root*x) with (Peval [1;-root] x).
 2:{ rewrite cons_eval, Pconst_eval. ring. }
 rewrite <- Pmult_eval, polypows_eqn.
 rewrite Pplus_eval, Pconst_eval, monom_eval. ring.
Qed.

Definition grps (r:nat) :=
 CPS_mult
   (CPS_mult (PS_poly (polypows r root)) (PS_dilate (PS_pow (/root^r)) r))
   gps.

Definition grps' (r:nat) :=
 CPS_mult
   (PS_dilate (CPS_mult (PS_poly [1;-root^r]) (PS_pow (/root^r))) r)
   fps.

Lemma grps_ok (r : nat) x : r<>O -> Cmod x <= 1 ->
 is_CPowerSeries (grps r) x (gr r x).
Proof.
 intros Hr Hx. unfold gr, grps.
 set (a := PS_dilate _ _).
 assert (NZ : root^r <> 0) by (apply Cpow_nz; intros [=H]; lra').
 assert (Ha : Rbar.Rbar_lt (Cmod x) (C_CV_radius a)).
 { unfold a. apply C_CV_radius_dilate; trivial.
   rewrite PS_pow_radius. 2:{ now apply nonzero_div_nonzero. }
   simpl. rewrite <- Cmod_inv, Cinv_inv.
   apply Rle_lt_trans with (1^r)%R.
   - apply pow_incr. split; trivial. apply Cmod_ge_0.
   - rewrite Cmod_pow, Cmod_R, Rabs_pos_eq by lra'.
     apply Rpow_lt_compat_r; trivial; lra'. }
 apply is_CPS_mult.
 - apply is_CPS_mult; trivial using PS_poly_ok;
   try now rewrite PS_poly_radius.
   unfold a, Cdiv. rewrite Cmult_comm.
   rewrite <- is_CPowerSeries_dilate by trivial.
   apply PS_pow_ok; try now apply nonzero_div_nonzero.
   rewrite Cmod_mult, Cmod_inv, !Cmod_pow, Cmod_R, Rabs_pos_eq by lra'.
   apply Rmult_lt_reg_l with (root^r)%R.
   { apply pow_lt. lra'. }
   rewrite <- Rmult_assoc, Rinv_r, Rmult_1_r, Rmult_1_l.
   2:{ apply pow_nonzero. lra'. }
   apply Rpow_lt_compat_r; trivial. apply Cmod_ge_0. lra'.
 - now apply gps_ok.
 - eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
   rewrite PS_poly_radius.
   apply Rbar.Rbar_min_case; simpl; trivial.
 - apply Rbar.Rbar_le_lt_trans with 1%R; trivial. apply gps_radius.
Qed.

Lemma grps_radius (r : nat) : r<>O ->
  Rbar.Rbar_lt 1%R (C_CV_radius (grps r)).
Proof.
 intros Hr. unfold grps.
 set (a := PS_dilate _ _).
 assert (NZ : root^r <> 0) by (apply Cpow_nz; intros [=H]; lra').
 assert (Ha : Rbar.Rbar_lt 1%R (C_CV_radius a)).
 { unfold a. apply C_CV_radius_dilate; trivial.
   rewrite PS_pow_radius. 2:{ now apply nonzero_div_nonzero. }
   simpl.
   rewrite <- Cmod_inv, Cinv_inv, Cmod_pow, Cmod_R, Rabs_pos_eq by lra'.
   apply Rpow_lt_compat_r; trivial; lra'. }
 eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
 apply Rbar.Rbar_min_case; [|apply gps_radius].
 eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
 apply Rbar.Rbar_min_case; trivial. now rewrite PS_poly_radius.
Qed.

Lemma grps'_ok (r : nat) x : r<>O -> Cmod x < /root ->
 is_CPowerSeries (grps' r) x (gr r x).
Proof.
 intros Hr Hx. rewrite gr_alt.
 2:{ intros E. rewrite E in Hx.
     rewrite Cmod_inv, Cmod_R, Rabs_pos_eq in Hx; lra'. }
 unfold vr, grps'.
 set (a := PS_dilate _ _).
 assert (NZ : root^r <> 0) by (apply Cpow_nz; intros [=H]; lra').
 assert (Ha : Rbar.Rbar_lt (Cmod x) (C_CV_radius a)).
 { unfold a. apply C_CV_radius_dilate; trivial.
   eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
   rewrite PS_poly_radius, PS_pow_radius.
   2:{ now apply nonzero_div_nonzero. }
   apply Rbar.Rbar_min_case; simpl; trivial.
   rewrite Cmod_inv, Rinv_inv, Cmod_pow, Cmod_R, Rabs_pos_eq by lra'.
   apply Rpow_lt_compat_r; trivial; try lra'. apply Cmod_ge_0. }
 apply is_CPS_mult; trivial.
 - unfold a. rewrite <- is_CPowerSeries_dilate by trivial.
   apply is_CPS_mult.
   + replace (1-_) with (Peval [1;-root^r] (x^r)). apply PS_poly_ok.
     rewrite cons_eval, Pconst_eval. ring.
   + unfold Cdiv. rewrite Cmult_comm.
     apply PS_pow_ok; try now apply nonzero_div_nonzero.
     rewrite Cmod_mult, Cmod_inv, !Cmod_pow, Cmod_R, Rabs_pos_eq by lra'.
     apply Rmult_lt_reg_l with (root^r)%R.
     { apply pow_lt. lra'. }
     rewrite <- Rmult_assoc, Rinv_r, Rmult_1_r, Rmult_1_l.
     2:{ apply pow_nonzero. lra'. }
     apply Rpow_lt_compat_r; trivial. apply Cmod_ge_0.
     apply Rlt_trans with 1%R; try lra'.
   + now rewrite PS_poly_radius.
   + rewrite PS_pow_radius. 2:{ now apply nonzero_div_nonzero. }
     simpl. rewrite Cmod_inv, Rinv_inv, !Cmod_pow.
     apply Rlt_trans with (1^r)%R.
     * apply Rpow_lt_compat_r; trivial. apply Cmod_ge_0. lra'.
     * apply Rpow_lt_compat_r; trivial; try lra.
       rewrite Cmod_R, Rabs_pos_eq; lra'.
 - apply fps_ok; trivial.
 - apply Rbar.Rbar_lt_le_trans with (/root)%R; trivial. apply fps_radius.
Qed.

Lemma grps'_radius (r : nat) : r<>O ->
  Rbar.Rbar_le (/root)%R (C_CV_radius (grps' r)).
Proof.
 intros Hr.
 eapply Rbar.Rbar_le_trans; [|apply C_CV_radius_mult].
 apply Rbar.Rbar_min_case; [|apply fps_radius].
 apply C_CV_radius_dilate'; trivial.
 eapply Rbar.Rbar_le_trans; [|apply C_CV_radius_mult].
 apply Rbar.Rbar_min_case.
 - now rewrite PS_poly_radius.
 - assert (NZ : root^r <> 0) by (apply Cpow_nz; intros [=H]; lra').
   rewrite PS_pow_radius.
   2:{ now apply nonzero_div_nonzero. }
   simpl.
   rewrite Cmod_inv, Rinv_inv, Cmod_pow, Cmod_R, Rabs_pos_eq by lra'.
   apply Rpow_le_compat_r; trivial.
   + apply Rlt_le, Rinv_0_lt_compat; lra'.
   + apply Rlt_le, Rlt_trans with 1%R; lra'.
Qed.

Lemma grps'_eqn (r : nat) n : r<>O -> grps' r n = grps r n.
Proof.
 intros Hr. apply CPowerSeries_coef_ext.
 - apply Rbar.Rbar_lt_le_trans with (/root)%R;
    try apply grps'_radius; trivial.
   simpl. apply Rinv_0_lt_compat; lra'.
 - apply Rbar.Rbar_lt_trans with 1%R; try apply grps_radius; trivial.
   simpl. lra.
 - assert (LT : 0 < /root). { apply Rinv_0_lt_compat; lra'. }
   exists (mkposreal _ LT). intros x Hx.
   change (Rabs (x-0) < /root) in Hx. rewrite Rminus_0_r in Hx.
   transitivity (gr r x).
   + apply CPowerSeries_unique. apply grps'_ok; trivial.
     now rewrite Cmod_R.
   + symmetry. apply CPowerSeries_unique. apply grps_ok; trivial.
     rewrite Cmod_R. apply Rlt_le, Rlt_trans with (/root)%R; trivial.
     rewrite <- Rinv_1. apply Rinv_lt_contravar; lra'.
Qed.

Lemma grps'_init (r : nat) n : (n < r)%nat -> grps' r n = fps n.
Proof.
 intros H.
 unfold grps', CPS_mult.
 rewrite <- big_sum_sum_n. rewrite <- big_sum_extend_l.
 change Gplus with Cplus.
 replace (fps n) with (1 * fps n + 0) by ring. f_equal.
 - rewrite Nat.sub_0_r. f_equal.
   unfold PS_dilate. rewrite Nat.mod_0_l by lia. simpl.
   rewrite Nat.div_0_l, sum_O by lia. simpl. unfold PS_poly, coef; simpl.
   ring.
 - apply (@big_sum_0_bounded C). intros m Hm. apply Cmult_integral; left.
   unfold PS_dilate. now rewrite Nat.mod_small by lia.
Qed.

Lemma vr_vr r x :
  r<>O -> x<>0 -> Cmod x <> root -> Cmod x <> (/root)%R ->
  vr r x * vr r (/x) = root^(2*r).
Proof.
 intros Hr H1 H2 H3. unfold vr.
 replace (root^(2*r)) with ((root^r)^2).
 2:{ now rewrite Nat.mul_comm, Cpow_mult_r. }
 rewrite !Cpow_inv. field; repeat split.
 - now apply Cpow_nz.
 - apply Cpow_nz. intros [=H];lra'.
 - intros E. apply Cminus_eq_0 in E.
   apply (f_equal Cmod) in E.
   rewrite <- Cpow_mult_l, Cmod_pow, Cmod_mult, Cmod_R, Rabs_pos_eq in E.
   2:lra'.
   rewrite Cmod_1 in E.
   apply Rdichotomy in H3. destruct H3 as [H3|H3].
   + apply Rmult_lt_compat_r with (r:=root) in H3; try lra'.
     rewrite Rinv_l in H3 by lra'.
     assert (H3' : 0<= Cmod x * root).
     { apply Rmult_le_pos. apply Cmod_ge_0. lra'. }
     generalize (pow_lt_1_compat (Cmod x*root) r (conj H3' H3) lia). lra.
   + apply Rmult_lt_compat_r with (r:=root) in H3; try lra'.
     rewrite Rinv_l in H3 by lra'.
     generalize (Rlt_pow_R1 _ r H3 lia). lra.
 - intros E. apply Cminus_eq_0 in E.
   apply (f_equal Cmod) in E.
   rewrite !Cmod_pow, Cmod_R, Rabs_pos_eq in E by lra'.
   apply pow_inj_l in E; trivial; try lra'. apply Cmod_ge_0.
Qed.

Lemma gr_gr r x :
  r<>O -> x<>0 -> Cmod x <> root -> Cmod x <> (/root)%R ->
  ~Root x Pcoef -> ~Root (/x) Pcoef ->
  gr r x * gr r (/x) = root^(2*r).
Proof.
 intros Hr H1 H2 H3 H4 H5.
 rewrite !gr_alt, <- (vr_vr r x); trivial.
 2:{ intros E. apply (f_equal Cinv) in E. rewrite !Cinv_inv in E.
     subst x. rewrite Cmod_R, Rabs_pos_eq in H2; lra'. }
 2:{ intros E. subst x. rewrite Cmod_inv, Cmod_R, Rabs_pos_eq in H3; lra'. }
 rewrite (Cmult_comm (vr r (/x))), !Cmult_assoc. f_equal.
 rewrite <- !Cmult_assoc. rewrite <- (Cmult_1_r (vr r x)) at 2. f_equal.
 apply ff; trivial.
Qed.

Lemma grps_square_ex r : r<>O -> ex_series (fun n => (grps r n)^2).
Proof.
 intros Hr.
 apply ex_series_Cmod.
 eapply ex_series_ext.
 { intros n. unfold "∘". symmetry. now rewrite Cmod_pow. }
 apply ex_series_square. rewrite <- ex_pseries_1. apply CV_radius_inside.
 unfold "∘".
 erewrite CV_radius_ext.
 2:{ intros n. now rewrite Rabs_pos_eq by apply Cmod_ge_0. }
 change (fun n => Cmod (grps r n)) with (Cmod ∘ (grps r)).
 rewrite <- C_CV_radius_alt. rewrite Rabs_pos_eq by lra.
 now apply grps_radius.
Qed.

Lemma grps_square r : r<>O -> root^(2*r) = CSeries (fun n => (grps r n)^2).
Proof.
 intros Hr.
 rewrite <- (SecondRoot.Mu_series_square (grps r) (gr r)).
 2:{ rewrite <- ex_pseries_1. apply CV_radius_inside.
     rewrite <- C_CV_radius_alt. rewrite Rabs_pos_eq by lra.
     now apply grps_radius. }
 2:{ intros z Hz. symmetry. apply CPowerSeries_unique, grps_ok; trivial.
     lra. }
 symmetry. unfold SecondRoot.Mu.
 rewrite (RInt_ext (V:=C_CNM)) with (g := fun t => root^(2*r)).
 2:{ intros x _. rewrite Cexp_neg. apply gr_gr; trivial.
     - apply Cexp_nonzero.
     - rewrite Cmod_Cexp; lra'.
     - rewrite Cmod_Cexp. intros E.
       apply (f_equal Rinv) in E. rewrite Rinv_inv, Rinv_1 in E. lra'.
     - rewrite Hcoefs. rewrite <- linfactors_roots.
       intros [E|IN].
       + apply (f_equal Cmod) in E.
         rewrite Cmod_Cexp, Cmod_R, Rabs_pos_eq in E; lra'.
       + red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
         rewrite Cmod_Cexp in IN; lra.
     - rewrite <- Cexp_neg.
       rewrite Hcoefs. rewrite <- linfactors_roots.
       intros [E|IN].
       + apply (f_equal Cmod) in E.
         rewrite Cmod_Cexp, Cmod_R, Rabs_pos_eq in E; lra'.
       + red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
         rewrite Cmod_Cexp in IN; lra. }
 rewrite CInt_const. rtoc. field. intros [=H]. now apply PI_neq0.
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

Lemma PS_dilate_real (a : nat -> C) r :
 (forall n, Im (a n) = 0%R) -> (forall n, Im (PS_dilate a r n) = 0%R).
Proof.
 intros Ha n. unfold PS_dilate. destruct Nat.eqb. apply Ha. easy.
Qed.

Lemma grps_real (r:nat) : r<>O -> forall n, Im (grps r n) = 0%R.
Proof.
 intros Hr n.
 rewrite <- grps'_eqn; trivial.
 unfold grps'. revert n. apply CPS_mult_real.
 - apply PS_dilate_real, CPS_mult_real.
   + intros n. unfold PS_poly.
     destruct n as [|[|n]]; ctor; simpl; try easy.
     unfold coef. rewrite nth_overflow. easy. simpl; lia.
   + intros n. unfold PS_pow. now ctor.
 - intros n. now rewrite fps_eqn'.
Qed.

Lemma grps_square_real (r:nat) : r<>O ->
 CSeries (fun n => (grps r n)^2) =
 RtoC (Series (fun n => (Re (grps r n))^2)%R).
Proof.
 intros Hr.
 rewrite <- CSeries_RtoC.
 - apply CSeries_ext. intros n. unfold "∘". rtoc. f_equal.
   generalize (grps_real r Hr n). destruct (grps r n) as (x,y). simpl.
   now intros ->.
 - rewrite <- ex_series_RtoC.
   apply ex_series_ext with (fun n => (grps r n)^2).
   2:now apply grps_square_ex.
   intros n. unfold "∘". rtoc. f_equal.
   generalize (grps_real r Hr n). destruct (grps r n) as (x,y). simpl.
   now intros ->.
Qed.

Lemma big_sum_sum_n_R (a : nat -> R) n : big_sum a (S n) = sum_n a n.
Proof.
 induction n.
 - simpl; rewrite sum_O; lra.
 - now rewrite sum_Sn, <- IHn, <- big_sum_extend_r.
Qed.

Lemma Ineq8 (r:nat) : IZR (big_sum (fun m => (fps' m)^2)%Z r) <= root^(2*r).
Proof.
 destruct (Nat.eq_dec r 0) as [->|N].
 - simpl. lra.
 - rewrite <- (re_RtoC (root^(2*r))). rtoc. rewrite grps_square; trivial.
   rewrite grps_square_real, re_RtoC; trivial.
   assert (EX : ex_series (fun n : nat => (Re (grps r n) ^ 2)%R)).
   { rewrite <- ex_series_RtoC.
     apply ex_series_ext with (fun n => (grps r n)^2).
     2:now apply grps_square_ex.
     intros n. unfold "∘". rtoc. f_equal.
     generalize (grps_real r N n). destruct (grps r n) as (x,y). simpl.
     now intros ->. }
   rewrite Series_incr_n with (n:=r); trivial; try lia.
   rewrite <- sum_n_Reals, <- big_sum_sum_n_R, big_sum_IZR.
   replace (S (pred r)) with r by lia.
   rewrite <- (Rplus_0_r (big_sum _ r)). apply Rplus_le_compat.
   + apply Req_le. apply big_sum_eq_bounded. intros m Hm.
     unfold "∘". rewrite <- grps'_eqn, grps'_init, fps_eqn' by lia.
     simpl. unfold Z.pow_pos. simpl.
     now rewrite Z.mul_1_r, Rmult_1_r, mult_IZR.
   + eapply pos_series_pos_lim. apply Series_correct.
     2:{ intros n. cbv beta. nra. }
     rewrite <- (ex_series_incr_n (V:=R_NM) (fun m => Re (grps r m)^2)%R r).
     trivial.
Qed.

Lemma Ineq8' (r:nat) : r<>O ->
  (big_sum (fun m => (fps' m)^2) r < 2^Z.of_nat r)%Z.
Proof.
 intros Hr. apply lt_IZR. eapply Rle_lt_trans; [apply Ineq8|].
 rewrite pow_mult, <- pow_IZR. apply Rpow_lt_compat_r; trivial. nra.
Qed.

Lemma fps_0_1 : fps' 0 = 1%Z /\ fps' 1 = 1%Z.
Proof.
 assert (H0 : (1 <= fps' 0)%Z).
 { assert (0 < fps' 0)%Z; try lia.
   { unfold fps'. rewrite fps_0. simpl.
     assert (H := coefs0_nz).
     destruct (nth 0 coefs Z0); simpl; try easy;
      now rewrite Int_part_IZR. }}
 assert (H1 := Two 1).
 simpl in H1.
 assert (H2 := Ineq8' 2 lia). cbn -[Z.pow] in H2. lia.
Qed.

Lemma fps_2 : (1 <= fps' 2 <= 2)%Z.
Proof.
 generalize (Two 2). simpl.
 generalize (Ineq8' 3 lia).
 cbn -[Z.pow]. destruct fps_0_1 as (->,->). lia.
Qed.

Lemma fps_3 : (1 <= fps' 3 <= 3)%Z.
Proof.
 generalize (Two 3). simpl.
 generalize (Ineq8' 4 lia).
 cbn -[Z.pow]. destruct fps_0_1 as (->,->). generalize fps_2. lia.
Qed.

Lemma root_65 : 6/5 < root.
Proof.
 assert (3 <= root^6).
 { eapply Rle_trans; [|apply (Ineq8 3)].
   cbn - [Z.pow]. destruct fps_0_1 as (->,->).
   apply IZR_le. generalize fps_2; lia. }
 assert (~ (5*root <= 6)); try lra.
 intros LE. apply (Rpow_le_compat_r 6) in LE; lra'.
Qed.

Lemma root_43 : fps' 2 = 2%Z -> 4/3 < root.
Proof.
 intros H.
 assert (6 <= root^6).
 { eapply Rle_trans; [|apply (Ineq8 3)].
   cbn - [Z.pow]. rewrite H. destruct fps_0_1 as (->,->). apply IZR_le. lia. }
 assert (~ (3*root <= 4)); try lra.
 intros LE. apply (Rpow_le_compat_r 6) in LE; lra'.
Qed.

Definition Case1 := take 4 fps' = [1;1;1;1]%Z.
Definition Case2 := take 5 fps' = [1;1;1;2;2]%Z.
Definition Case3 := take 5 fps' = [1;1;1;2;3]%Z /\ (3 <= fps' 5 <= 4)%Z.
Definition Case4 := take 4 fps' = [1;1;2;2]%Z.
Definition Case5 := take 6 fps' = [1;1;1;2;3;5]%Z /\ (5 <= fps' 6 <= 7)%Z.
Definition Case6 := take 4 fps' = [1;1;2;3]%Z /\
                    In (fps' 4, fps' 5) [(3,3);(3,4);(3,5);(4,4);(4,5)]%Z.

Section Lemma3.

Let A n := big_sum (fun m => (fps' (S m))^2)%Z n.
Let C n := A (S n).
Let B n := big_sum (fun m => fps' m * fps' (S m))%Z (S n).
Let phi n (x:R) := (IZR (A n) * x^2 - 2*IZR (B n) * x + IZR (C n))%R.

Lemma Ineq9 n : n<>O -> phi n root <= 0.
Proof.
 intros Hn. generalize One'.
 rewrite Series_incr_n with (n:=S n); try lia; try apply diff_f'_square_ex.
 rewrite <- sum_n_Reals, <- big_sum_sum_n_R. simpl pred.
 destruct fps_0_1 as (->,_). rewrite pow1.
 set (a := fun k => _).
 set (b := fun k => _).
 assert (0 <= Series b).
 { apply pos_series_pos_lim with b.
   - apply Series_correct. apply (ex_series_incr_n a (S n)).
     apply diff_f'_square_ex.
   - intros m. unfold b. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
 intros E.
 assert (LE : (big_sum a (S n) <= root ^ 2)%R) by lra. clear E H b.
 revert LE.
 rewrite big_sum_eq_bounded with
  (g := (fun k => IZR ((fps' k)^2) * root^2
                  + IZR (fps' k * fps' (S k)) * (-2*root)
                  + IZR ((fps' (S k))^2))%R).
 2:{ intros x Hx. unfold a.
     rewrite mult_IZR.
     change 2%Z with (Z.of_nat 2); rewrite <- !pow_IZR. ring. }
 rewrite !big_sum_Rplus, <- !big_sum_Rmult_r.
 rewrite <- (big_sum_IZR (fun k => fps' k ^2)%Z).
 rewrite <- (big_sum_IZR (fun k => fps' k * fps' (S k))%Z).
 rewrite <- (big_sum_IZR (fun k => fps' (S k) ^2)%Z).
 fold (B n). fold (A (S n)). fold (C n).
 rewrite <- big_sum_extend_l.
 fold (A n). change Gplus with Z.add.
 destruct fps_0_1 as (->,_). change (1^2)%Z with 1%Z.
 unfold phi. rewrite plus_IZR. lra.
Qed.

Lemma fps_no_1113 : fps' 2 = 1%Z -> fps' 3 = 3%Z -> False.
Proof.
 intros H2 H3.
 generalize (Ineq9 2 lia). unfold phi, C, B, A.
 cbn -[Z.pow pow]. destruct fps_0_1 as (->,->). rewrite H2, H3.
 cbn - [pow]. replace (2*5)%R with 10%R by lra.
 set (f := (fun x => 2 * x^2-10*x+11)%R).
 set (df := (fun x => 4 * x - 10)%R).
 change (f root <= 0 -> False).
 destruct (MVT_weak f df root (sqrt 2)) as (c & Hc & E).
 { intros x _. unfold f, df. auto_derive; trivial. ring. }
 { apply Rsqr_incrst_0; try lra'; try apply sqrt_pos.
   rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
 assert (df c < 0). { unfold df. generalize sqrt2_approx; lra. }
 assert (0 < f (sqrt 2)). { unfold f. generalize sqrt2_approx; nra. }
 nra.
Qed.

Lemma fps_1123 : fps' 2 = 2%Z -> fps' 3 = 3%Z -> Case6.
Proof.
 destruct fps_0_1 as (H0,H1). intros H2 H3. split.
 { unfold take. simpl. now rewrite H0, H1, H2, H3. }
 assert (L4 : (3 <= fps' 4)%Z). { rewrite <- H3. apply (Two 4). }
 assert (T5 : (fps' 4 <= fps' 5)%Z). { apply (Two 5). }
 assert (LE := Ineq8' 6 lia).
 cbn -[Z.pow] in LE. rewrite H0, H1, H2, H3 in LE.
 assert (LE' : (fps' 4 ^2 + fps' 5 ^2 <= 48)%Z) by lia. clear LE.
 assert (U4 : (fps' 4 <= 4)%Z).
 { assert (U : (fps' 4 <> 6)%Z). { intros U. rewrite U in LE', T5. lia. }
   assert (V : (fps' 4 <> 5)%Z). { intros V. rewrite V in LE', T5. lia. }
   lia. }
 assert (U5 : (fps' 5 <= 6)%Z) by lia.
 assert (U5b : (fps' 4 = 4 -> fps' 5 <= 5)%Z) by lia.
 assert (U5c : (fps' 4 = 3 -> fps' 5 = 6 -> False)%Z).
 { intros H4 H5.
   generalize (Ineq9 4 lia). unfold phi, C, B, A.
   cbn -[Z.pow pow]. rewrite H0, H1, H2, H3, H4, H5.
   cbn - [pow].
   generalize (discriminant_neg 23 (-2*36) 59 ltac:(lra) ltac:(lra) root).
   lra. }
 simpl. rewrite !pair_equal_spec. lia.
Qed.

Lemma fps_1112 : fps' 2 = 1%Z -> fps' 3 = 2%Z -> Case2 \/ Case3 \/ Case5.
Proof.
 destruct fps_0_1 as (H0,H1). intros H2 H3.
 (* With just $b_4 >= 4$, the inequality
    $b_4^2+18-4(b_4+2)\sqrt{2} >= 34 - 24\sqrt{2}$
    requires a study of the function $x^2+18-4(x+2)\sqrt{2}$
    (which is increasing for x>=2√2 and in particular x>=4).
    Not in the article, but simpler here: use Inequality (8)
    to obtain $b_4 <= 4$. *)
 assert (LE := Ineq8' 5 lia).
 cbn -[Z.pow pow] in LE. rewrite H0, H1, H2, H3 in LE.
 assert (H4 : (fps' 4 <= 4)%Z) by lia. clear LE.
 destruct (Z.eq_dec (fps' 4) 4) as [H4'|H4'].
 - exfalso. clear H4.
   generalize (Ineq9 3 lia). unfold phi, C, B, A.
   cbn -[Z.pow pow]. rewrite H0, H1, H2, H3, H4'. cbn -[pow].
   replace (2*12)%R with 24%R by lra.
   set (f := (fun x => 6*x^2-24*x+22)%R).
   set (df := (fun x => 12*x - 24)%R).
   change (f root <= 0 -> False).
   destruct (MVT_weak f df root (sqrt 2)) as (c & Hc & E).
   { intros x _. unfold f, df. auto_derive; trivial. ring. }
   { apply Rsqr_incrst_0; try lra'; try apply sqrt_pos.
     rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
   assert (df c < 0). { unfold df. generalize sqrt2_approx; lra. }
   assert (0 < f (sqrt 2)). { unfold f. generalize sqrt2_approx; nra. }
   nra.
 - assert (H4b : (fps' 4 = 2 \/ fps' 4 = 3)%Z).
   { generalize (Two 4). simpl. lia. }
   clear H4' H4. destruct H4b as [H4|H4].
   + left. unfold Case2, take. simpl. congruence.
   + right.
     (* Same as before : Inequality (8) ensures $b_5 <= 6$ and that spares
        us a function study *)
     assert (LE := Ineq8' 6 lia).
     cbn -[Z.pow pow] in LE. rewrite H0, H1, H2, H3, H4 in LE.
     assert (H5 : (fps' 5 <= 6)%Z) by lia. clear LE.
     destruct (Z.eq_dec (fps' 5) 6) as [H5'|H5'].
     * exfalso. clear H5.
       generalize (Ineq9 4 lia). unfold phi, C, B, A.
       cbn -[Z.pow pow]. rewrite H0, H1, H2, H3, H4, H5'. cbn -[pow].
       replace (2*28)%R with 56%R by lra.
       set (f := (fun x => 15*x^2-56*x+51)%R).
       set (df := (fun x => 30*x - 56)%R).
       change (f root <= 0 -> False).
       destruct (MVT_weak f df root (sqrt 2)) as (c & Hc & E).
       { intros x _. unfold f, df. auto_derive; trivial. ring. }
       { apply Rsqr_incrst_0; try lra'; try apply sqrt_pos.
         rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
       assert (df c < 0). { unfold df. generalize sqrt2_approx; lra. }
       assert (0 < f (sqrt 2)). { unfold f. generalize sqrt2_approx; nra. }
       nra.
     * assert (H5b : (fps' 5 = 3 \/ fps' 5 = 4 \/ fps' 5 = 5)%Z).
       { generalize (Two 5). simpl. lia. }
       clear H5' H5. rewrite <- or_assoc in H5b.
       destruct H5b as [H5|H5].
       ** left. unfold Case3, take. split; try lia. simpl. congruence.
       ** right. unfold Case5, take. split. simpl; congruence.
          (* Inequality (8) ensures $b_6 <= 9$ *)
          assert (LE := Ineq8' 7 lia).
          cbn -[Z.pow pow] in LE. rewrite H0, H1, H2, H3, H4, H5 in LE.
          assert (H6 : (fps' 6 <= 9)%Z) by lia. clear LE.
          destruct (Z.le_gt_cases 8 (fps' 6)) as [H6'|H6'].
          2:{ generalize (Two 6). simpl. lia. }
          exfalso.
          generalize (Ineq9 5 lia). unfold phi, C, B, A.
          cbn -[Z.pow pow]. rewrite H0, H1, H2, H3, H4, H5.
          change (_+5^2)%Z with 40%Z.
          change (_+3*5)%Z with 25%Z.
          rewrite !plus_IZR, mult_IZR.
          change 2%Z with (Z.of_nat 2)%Z at 2. rewrite <- pow_IZR.
          set (b6 := fps' 6) in *.
          apply IZR_le in H6'.
          set (f := (fun x => 40*x^2-2*(25+5*b6)*x+(40+b6^2))%R).
          set (df := (fun x => 80*x - 2*(25+5*b6))%R).
          change (f root <= 0 -> False).
          destruct (MVT_weak f df root (sqrt 2)) as (c & Hc & E).
          { intros x _. unfold f, df. auto_derive; trivial. ring. }
          { apply Rsqr_incrst_0; try lra'; try apply sqrt_pos.
            rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
          assert (sqrt 2 < 1.5).
          { apply Rsqr_incrst_0; try lra'; try apply sqrt_pos.
            rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
          assert (LT : df c < 0).
          { unfold df. lra. }
          assert (LT' : 0 < f (sqrt 2)).
          { unfold f. rewrite <- Rsqr_pow2, Rsqr_sqrt by lra.
            assert ((50+10*b6)*sqrt 2 < 120+b6^2); try lra.
            apply Rsqr_incrst_0; try nra.
            2:{ apply Rmult_le_pos. lra. apply sqrt_pos. }
            rewrite Rsqr_mult, Rsqr_sqrt, !Rsqr_pow2 by lra.
            apply le_IZR in H6'.
            assert (B6 : (b6 = 8 \/ b6 = 9)%Z) by lia.
            destruct B6 as [-> | ->]. lra. lra. }
       nra.
Qed.

Lemma Three : Case1 \/ Case2 \/ Case3 \/ Case4 \/ Case5 \/ Case6.
Proof.
 destruct fps_0_1 as (H0,H1).
 assert (H2 : (fps' 2 = 1 \/ fps' 2 = 2)%Z) by (generalize fps_2; lia).
 destruct H2 as [H2|H2].
 - assert (H3 : (fps' 3 = 1 \/ fps' 3 = 2)%Z).
   { generalize fps_no_1113 fps_3; lia. }
   destruct H3 as [H3|H3].
   + left. unfold Case1, take. simpl. congruence.
   + generalize (fps_1112 H2 H3). tauto.
 - assert (H3 : (fps' 3 = 2 \/ fps' 3 = 3)%Z).
    { generalize (Two 3) fps_3; simpl; lia. }
    destruct H3 as [H3|H3].
    + do 3 right; left. unfold Case4, take. simpl. congruence.
    + do 5 right. now apply fps_1123.
Qed.

End Lemma3.

Definition ZPS_mult (a b : nat -> Z) (n : nat) :=
 big_sum (fun k : nat => (a k * b (n - k)%nat)%Z) (S n).

Lemma ZPS_mult_IZR (a b : nat -> Z) n :
 IZR (ZPS_mult a b n) = PS_mult (IZR∘a) (IZR∘b) n.
Proof.
 unfold ZPS_mult, PS_mult. rewrite <- sum_n_Reals, <- big_sum_sum_n_R.
 rewrite big_sum_IZR. apply big_sum_eq_bounded. intros x Hx.
 unfold "∘". now rewrite mult_IZR.
Qed.

Lemma PS_mult_RtoC (a b : nat -> R) n :
 RtoC (PS_mult a b n) = CPS_mult (RtoC∘a) (RtoC∘b) n.
Proof.
 unfold PS_mult, CPS_mult. rewrite <- sum_n_Reals.
 rewrite RtoC_sum_n. apply sum_n_ext. intros x.
 unfold "∘". now rewrite RtoC_mult.
Qed.

Lemma ex_series_PS_poly p : ex_series (PS_poly p).
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

Section Lemma4.

Variable A : list Z.
Definition β := ZPS_mult (fun n => nth n A Z0) fps'.
Definition B n (x:C) := sum_n (fun m => β m * x^m) n.
Definition μ (l : list Z) := big_sum (fun m => (nth m l Z0)^2)%Z (length l).

Section Lemma4_Fixedk.
Variable k:nat.
Let Bkpoly := take (S k) β.

Lemma Bkpoly_ok x : Peval (Zpoly Bkpoly) x = B k x.
Proof.
 unfold Peval, Zpoly, Bkpoly, take, coef, B.
 rewrite !map_length, seq_length, map_map.
 rewrite big_sum_sum_n.
 apply sum_n_ext_loc.
 intros n Hn. f_equal.
 rewrite nth_map_indep with (d' := O); try (rewrite ?seq_length; lia).
 now rewrite seq_nth by lia.
Qed.

Lemma mu_poly l : RtoC (μ l) = SecondRoot.Mu (Peval (Zpoly l)).
Proof.
 rewrite (SecondRoot.Mu_series_square (PS_poly (Zpoly l))).
 2:{ unfold "∘". rewrite <- ex_series_RtoC.
     eapply ex_series_ext. symmetry. apply Cmod_PS_poly.
     apply ex_series_PS_poly. }
 2:{ intros z Hz. symmetry. apply CPowerSeries_unique, PS_poly_ok. }
 rewrite CSeries_incr_n with (n := length l).
 2:{ eapply ex_series_ext. symmetry. apply PS_poly_pow2.
     apply ex_series_PS_poly. }
 rewrite CSeries_ext with (v := fun n => 0).
 2:{ intros n. unfold PS_poly, Zpoly, coef.
     rewrite nth_overflow. ring. rewrite map_length; lia. }
 rewrite CSeries_unique with (l := 0), Cplus_0_r.
 2:{ apply is_CSeries_RtoC, is_series_R0. }
 unfold μ. rewrite big_sum_IZR, big_sum_RtoC.
 apply big_sum_eq_bounded. intros m Hm.
 unfold PS_poly, "∘". rewrite coef_Zpoly. ctor. now rewrite pow_IZR.
Qed.

Lemma continuous_poly p x : continuous (Peval p) x.
Proof.
 unfold Peval.
 destruct (Nat.eq_dec (length p) 0) as [E|N].
 - rewrite E. simpl. apply continuous_const.
 - replace (length p) with (S (length p - 1)) by lia.
   eapply continuous_ext. { intros y. symmetry. apply big_sum_sum_n. }
   apply sum_n_continuous.
   intros i Hi. apply continuous_Cmult. apply continuous_const.
   apply continuous_Cpow.
Qed.

Lemma Mu_ext (f g : C -> C) :
  (forall c, Cmod c = 1%R -> f c = g c) ->
  SecondRoot.Mu f = SecondRoot.Mu g.
Proof.
 intros Eq. unfold SecondRoot.Mu. f_equal.
 apply RInt_ext. intros x _. f_equal; apply Eq; now rewrite Cmod_Cexp.
Qed.

Lemma μA : RtoC (μ A) = SecondRoot.Mu (Peval (Zpoly A)).
Proof.
 apply mu_poly.
Qed.

Lemma μB : RtoC (μ Bkpoly) = SecondRoot.Mu (B k).
Proof.
 rewrite mu_poly. apply Mu_ext. intros c _. apply Bkpoly_ok.
Qed.

Definition vAf x := Peval (Zpoly A) x * gr 1 x.
Definition vB x := vr 1 x * B k x.

Lemma vAf_alt x : x<>/root -> vAf x = vr 1 x * Peval (Zpoly A) x * f x.
Proof.
 intros Hx. unfold vAf. rewrite gr_alt by trivial; ring.
Qed.

Definition Mu_vAf : SecondRoot.Mu vAf = root^2 * μ A.
Proof.
 rewrite μA.
 unfold SecondRoot.Mu.
 rewrite Cmult_assoc, (Cmult_comm (root^2)), <- Cmult_assoc. f_equal.
 rewrite <- CInt_scal.
 2:{ apply (ex_RInt_continuous (V:=C_CNM)).
     intros x _. apply continuous_Cmult.
     - apply continuous_comp;
         [apply continuous_Cexp|apply continuous_poly].
     - apply continuous_comp; [|apply continuous_poly].
       apply continuous_comp; [|apply continuous_Cexp].
       apply (continuous_opp (V:=R_NM)), continuous_id. }
 apply RInt_ext.
 intros x _. unfold vAf.
 change (root^2) with (root^(2*1)).
 rewrite <- (gr_gr 1 (Cexp x));
   try lia; try apply Cexp_nonzero; try (rewrite Cmod_Cexp; lra').
 - rewrite Cexp_neg. fixeq C. ring.
 - rewrite Hcoefs, <- linfactors_roots. intros [E|IN].
   + apply (f_equal Cmod) in E.
     rewrite Cmod_Cexp, Cmod_R, Rabs_pos_eq in E; lra'.
   + red in Hroots. rewrite Forall_forall in Hroots; apply Hroots in IN.
     rewrite Cmod_Cexp in IN; lra.
 - rewrite <- Cexp_neg, Hcoefs, <- linfactors_roots. intros [E|IN].
   + apply (f_equal Cmod) in E.
     rewrite Cmod_Cexp, Cmod_R, Rabs_pos_eq in E; lra'.
   + red in Hroots. rewrite Forall_forall in Hroots; apply Hroots in IN.
     rewrite Cmod_Cexp in IN; lra.
Qed.

Lemma continuous_B x : continuous (B k) x.
Proof.
 eapply continuous_ext. apply Bkpoly_ok. apply continuous_poly.
Qed.

Lemma Mu_vB : SecondRoot.Mu vB = root^2 * μ Bkpoly.
Proof.
 rewrite μB.
 unfold SecondRoot.Mu.
 rewrite Cmult_assoc, (Cmult_comm (root^2)), <- Cmult_assoc. f_equal.
 rewrite <- CInt_scal.
 2:{ apply (ex_RInt_continuous (V:=C_CNM)).
     intros x _. apply continuous_Cmult.
     - apply continuous_comp;
         [apply continuous_Cexp|apply continuous_B].
     - apply continuous_comp; [|apply continuous_B].
       apply continuous_comp; [|apply continuous_Cexp].
       apply (continuous_opp (V:=R_NM)), continuous_id. }
 apply RInt_ext.
 intros x _. unfold vB.
 change (root^2) with (root^(2*1)).
 rewrite <- (vr_vr 1 (Cexp x));
   try lia; try apply Cexp_nonzero; try (rewrite Cmod_Cexp; lra').
 rewrite Cexp_neg. fixeq C. ring.
Qed.

Definition α := CPS_mult (PS_poly (Zpoly A)) (grps 1).
Definition vr1ps := CPS_mult (PS_poly [1;-root]) (PS_pow (/root)).
Definition γ := CPS_mult vr1ps (PS_poly (Zpoly Bkpoly)).

Lemma β_ok x : Cmod x < /root ->
 is_CPowerSeries β x (Peval (Zpoly A) x * f x).
Proof.
 intros Hx.
 unfold β.
 apply is_CPowerSeries_alt.
 apply is_pseries_ext with (CPS_mult (PS_poly (Zpoly A)) fps).
 { intros n. rewrite ZPS_mult_IZR, PS_mult_RtoC.
   unfold CPS_mult. unfold "∘". eapply sum_n_ext.
   intros m. now rewrite <- fps_eqn', <- coef_Zpoly. }
 rewrite <- is_CPowerSeries_alt.
 apply is_CPS_mult.
 - apply PS_poly_ok.
 - now apply fps_ok.
 - now rewrite PS_poly_radius.
 - eapply Rbar.Rbar_lt_le_trans; [| apply fps_radius]. simpl. apply Hx.
Qed.

Lemma β_radius : Rbar.Rbar_le (/root)%R (C_CV_radius β).
Proof.
 apply C_CV_radius_minorant. intros. eexists. now apply β_ok.
Qed.

Lemma α_ok x : Cmod x <= 1 -> is_CPowerSeries α x (vAf x).
Proof.
 intros Hx.
 unfold α, vAf.
 apply is_CPS_mult.
 - apply PS_poly_ok.
 - now apply grps_ok.
 - now rewrite PS_poly_radius.
 - eapply Rbar.Rbar_le_lt_trans; [| apply grps_radius; lia]. apply Hx.
Qed.

Lemma α_radius : Rbar.Rbar_lt 1%R (C_CV_radius α).
Proof.
 unfold α.
 eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
 rewrite PS_poly_radius.
 apply Rbar.Rbar_min_case; [simpl; trivial|]. now apply grps_radius.
Qed.

Lemma vr1ps_ok x : Cmod x < root -> is_CPowerSeries vr1ps x (vr 1 x).
Proof.
 intros Hx.
 unfold vr1ps, vr, Cdiv. rewrite !Cpow_1_r, (Cmult_comm x).
 assert (/root <> 0). { ctor. intros [=H]. lra'. }
 apply is_CPS_mult.
 - replace (1-root*x) with (Peval [1;-root] x). apply PS_poly_ok.
   rewrite cons_eval, Pconst_eval. ring.
 - apply PS_pow_ok; trivial.
   rewrite Cmod_mult, Cmod_inv, Cmod_R, Rabs_pos_eq by lra'.
   apply Rmult_lt_reg_l with root. lra'. field_simplify; lra'.
 - now rewrite PS_poly_radius.
 - rewrite PS_pow_radius; trivial. simpl.
   rewrite Cmod_inv, Rinv_inv, Cmod_R, Rabs_pos_eq; lra'.
Qed.

Lemma vr1ps_radius : Rbar.Rbar_le root (C_CV_radius vr1ps).
Proof.
 apply C_CV_radius_minorant. intros; eexists; now apply vr1ps_ok.
Qed.

Lemma vr1ps_0 : vr1ps 0 = 1.
Proof.
 unfold vr1ps, CPS_mult. simpl. rewrite sum_O; lca.
Qed.

Lemma vr1ps_alt n : n<>O -> vr1ps n = (1-root^2)/root^n.
Proof.
 intros Hn.
 unfold vr1ps, CPS_mult. rewrite <- big_sum_sum_n.
 destruct n as [|n]; try easy.
 rewrite <- !big_sum_extend_l. change Gplus with Cplus.
 rewrite big_sum_0.
 2:{ intros x. unfold PS_poly, coef. rewrite nth_overflow. lca. simpl; lia. }
 rewrite Cplus_0_r. unfold PS_poly, coef. simpl nth.
 unfold PS_pow. simpl. rewrite Nat.sub_0_r, !Cpow_inv. field.
 split; try apply Cpow_nz; intros [=H]; lra'.
Qed.

Lemma γ_ok x : Cmod x <= 1 -> is_CPowerSeries γ x (vB x).
Proof.
 intros Hx.
 unfold γ, vB.
 apply is_CPS_mult.
 - apply vr1ps_ok; lra'.
 - rewrite <- Bkpoly_ok. apply PS_poly_ok.
 - eapply Rbar.Rbar_lt_le_trans; [|apply vr1ps_radius]. simpl; lra'.
 - now rewrite PS_poly_radius.
Qed.

Lemma γ_radius : Rbar.Rbar_lt 1%R (C_CV_radius γ).
Proof.
 unfold γ.
 eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
 rewrite PS_poly_radius.
 apply Rbar.Rbar_min_case; [|simpl; trivial].
 apply Rbar.Rbar_lt_le_trans with root. simpl; lra'. apply vr1ps_radius.
Qed.

Lemma α_alt n : α n = CPS_mult vr1ps β n.
Proof.
 revert n. apply CPowerSeries_coef_ext.
 - apply Rbar.Rbar_lt_trans with 1%R. simpl; lra. apply α_radius.
 - eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
   apply Rbar.Rbar_min_case.
   + apply Rbar.Rbar_lt_le_trans with root. simpl; lra'.
     apply vr1ps_radius.
   + apply Rbar.Rbar_lt_le_trans with (/root)%R. simpl; lra'.
     apply β_radius.
 - assert (LT : 0 < /root) by lra'.
   exists (mkposreal _ LT).
   intros y Hy. change (Rabs (y-0) < /root) in Hy.
   rewrite Rminus_0_r in Hy.
   rewrite CPowerSeries_mult; rewrite ?Cmod_R.
   + assert (Hy1 : Cmod y <= 1). { rewrite Cmod_R. lra'. }
     assert (Hy2 : Cmod y < /root). { rewrite Cmod_R. lra. }
     assert (Hy3 : Cmod y < root). { rewrite Cmod_R. lra'. }
     rewrite (CPowerSeries_unique _ _ _ (α_ok y Hy1)).
     rewrite (CPowerSeries_unique _ _ _ (β_ok y Hy2)).
     rewrite (CPowerSeries_unique _ _ _ (vr1ps_ok y Hy3)).
     rewrite vAf_alt. ring. ctor. intros [= H]. rewrite H in Hy.
     rewrite Rabs_pos_eq in Hy; lra'.
   + apply Rbar.Rbar_lt_le_trans with root. simpl; lra'.
     apply vr1ps_radius.
   + apply Rbar.Rbar_lt_le_trans with (/root)%R. simpl; lra'.
     apply β_radius.
Qed.

Lemma big_sum_rev (a : nat -> C) n :
 big_sum a n = big_sum (fun k => a (n-1-k)%nat) n.
Proof.
 induction n; try easy.
 rewrite <- big_sum_extend_r, <- big_sum_extend_l. change Gplus with Cplus.
 replace (S n - 1 -0)%nat with n by lia. rewrite Cplus_comm. f_equal.
 rewrite IHn. apply big_sum_eq_bounded. intros x Hx. f_equal. lia.
Qed.

Lemma γ_alt n : (n>k)%nat -> γ n = (1-root^2)/root^n * B k root.
Proof.
 intros Hn.
 unfold γ. unfold CPS_mult.
 rewrite <- big_sum_sum_n, <- big_sum_extend_l.
 change Gplus with Cplus.
 unfold PS_poly.
 rewrite coef_Zpoly, Nat.sub_0_r, nth_overflow, Cmult_0_r, Cplus_0_l.
 2:{ unfold Bkpoly. now rewrite take_length. }
 erewrite big_sum_eq_bounded.
 2:{ intros m Hm. rewrite vr1ps_alt by lia. unfold Cdiv.
     rewrite <- Cmult_assoc. reflexivity. }
 rewrite <- big_sum_Cmult_l.
 unfold Cdiv. rewrite <- Cmult_assoc. f_equal.
 apply Cmult_eq_reg_l with (root^n).
 2:{ apply Cpow_nz. intros [=H]; lra'. }
 rewrite Cmult_assoc, Cinv_r, Cmult_1_l.
 2:{ apply Cpow_nz. intros [=H]; lra'. }
 rewrite big_sum_Cmult_l. unfold B.
 rewrite big_sum_rev.
 erewrite big_sum_eq_bounded.
 2:{ intros x Hx.
     rewrite Cmult_assoc.
     replace (root^n * _) with (root^x).
     2:{ replace (S _) with (n-x)%nat by lia.
         replace n with (n-x+x)%nat at 1 by lia.
         rewrite Cpow_add. field. apply Cpow_nz. intros [=H]; lra'. }
     replace (n - S (_ - _))%nat with x by lia.
     rewrite coef_Zpoly, Cmult_comm. reflexivity. }
 replace n with (S k+(n-S k))%nat by lia.
 rewrite big_sum_sum. rewrite big_sum_sum_n. rewrite big_sum_0.
 2:{ intros x. rewrite nth_overflow. apply Cmult_0_l. unfold Bkpoly.
     rewrite take_length; lia. }
 rewrite Cplus_0_r. apply sum_n_ext_loc.
 intros m Hm. f_equal. unfold Bkpoly. now rewrite take_nth by lia.
Qed.

Lemma α_γ_init n : (n <= k)%nat -> α n = γ n.
Proof.
 intros Hn.
 rewrite α_alt. unfold γ.
 unfold CPS_mult. apply sum_n_ext_loc.
 intros m Hm. f_equal. unfold PS_poly. rewrite coef_Zpoly.
 unfold Bkpoly. rewrite take_nth; trivial; lia.
Qed.

Lemma α_γ_Sk : α (S k) = β (S k) + γ (S k).
Proof.
 rewrite α_alt. unfold γ. unfold CPS_mult.
 rewrite <- !big_sum_sum_n.
 do 2 rewrite <- (big_sum_extend_l (S k)). change Gplus with Cplus.
 rewrite Nat.sub_0_r, vr1ps_0.
 rewrite Cmult_1_l. f_equal.
 unfold PS_poly. rewrite coef_Zpoly. rewrite nth_overflow.
 2:{ unfold Bkpoly. now rewrite take_length. }
 rewrite Cmult_0_r, Cplus_0_l. apply big_sum_eq_bounded.
 intros m Hm. f_equal. rewrite coef_Zpoly. unfold Bkpoly.
 rewrite take_nth; trivial; lia.
Qed.

Lemma α_square : SecondRoot.Mu vAf = CSeries (fun n => α n^2).
Proof.
 apply SecondRoot.Mu_series_square.
 - rewrite <- ex_pseries_1.
   apply CV_radius_inside.
   rewrite <- C_CV_radius_alt, Rabs_pos_eq by lra.
   apply α_radius.
 - intros z Hz. symmetry. apply CPowerSeries_unique, α_ok; lra.
Qed.

Lemma γ_square : SecondRoot.Mu vB = CSeries (fun n => γ n^2).
Proof.
 apply SecondRoot.Mu_series_square.
 - rewrite <- ex_pseries_1.
   apply CV_radius_inside.
   rewrite <- C_CV_radius_alt, Rabs_pos_eq by lra.
   apply γ_radius.
 - intros z Hz. symmetry. apply CPowerSeries_unique, γ_ok; lra.
Qed.

Definition α' := Re∘α.
Definition γ' := Re∘γ.

Lemma α_real n : α n = α' n.
Proof.
 rewrite <- (re_im_id (α n)).
 unfold α at 2.
 rewrite CPS_mult_real. now rewrite Cmult_0_r, Cplus_0_r.
 { intros m. unfold PS_poly. now rewrite coef_Zpoly. }
 { intros m. now rewrite grps_real. }
Qed.

Lemma γ_real n : γ n = γ' n.
Proof.
 rewrite <- (re_im_id (γ n)).
 unfold γ at 2.
 rewrite CPS_mult_real. now rewrite Cmult_0_r, Cplus_0_r.
 { intros m. unfold vr1ps. apply CPS_mult_real.
   - intros m'. unfold PS_poly, coef.
     destruct m' as [|[|[|m']]]; simpl; try lra.
   - intros m'. unfold PS_pow. now ctor. }
 { intros m. unfold PS_poly. now rewrite coef_Zpoly. }
Qed.

Lemma α'_square_ex : ex_series (fun n : nat => (α' n ^ 2)%R).
Proof.
 apply ex_series_square.
 apply ex_series_ext with (Cmod∘α).
 { intros n. unfold "∘". now rewrite <- Cmod_R, <- α_real. }
 rewrite <- ex_pseries_1.
 apply CV_radius_inside.
 rewrite <- C_CV_radius_alt, Rabs_pos_eq by lra.
 apply α_radius.
Qed.

Lemma α_square_real :
 CSeries (fun n => (α n)^2) = Series (fun n => (α' n)^2)%R.
Proof.
 rewrite <- CSeries_RtoC; try apply α'_square_ex.
 apply CSeries_ext. intros n. unfold "∘". rtoc. f_equal. apply α_real.
Qed.

Lemma γ'_square_ex : ex_series (fun n : nat => (γ' n ^ 2)%R).
Proof.
 apply ex_series_square.
 apply ex_series_ext with (Cmod∘γ).
 { intros n. unfold "∘". now rewrite <- Cmod_R, <- γ_real. }
 rewrite <- ex_pseries_1.
 apply CV_radius_inside.
 rewrite <- C_CV_radius_alt, Rabs_pos_eq by lra.
 apply γ_radius.
Qed.

Lemma γ_square_real :
 CSeries (fun n => (γ n)^2) = Series (fun n => (γ' n)^2)%R.
Proof.
 rewrite <- CSeries_RtoC; try apply γ'_square_ex.
 apply CSeries_ext. intros n. unfold "∘". rtoc. f_equal. apply γ_real.
Qed.

Definition B' n (x:R) := sum_n (fun m => β m * x^m)%R n.

Lemma B_real n (x:R) : B n x = RtoC (B' n x).
Proof.
 unfold B, B'. rewrite RtoC_sum_n. apply sum_n_ext.
 intros m. unfold "∘". now rtoc.
Qed.

Lemma γ_square_rest :
 (Series (fun n => (γ' (n+S k))^2)
  = (root^2-1) / root^(2*k) * (B' k root)^2)%R.
Proof.
 erewrite Series_ext.
 2:{ intros m. apply RtoC_inj. rtoc. rewrite <- γ_real.
     rewrite γ_alt by lia. ctor. rewrite B_real. ctor.
     unfold Rdiv. rewrite 2 Rpow_mult_distr.
     rewrite <- pow_inv, <- pow_mult.
     rewrite Nat.mul_comm, Nat.add_comm, Nat.mul_add_distr_l.
     rewrite pow_add, (pow_mult _ 2 m).
     rewrite 2 pow_inv. rewrite <- Rmult_assoc. reflexivity. }
 rewrite Series_scal_r. f_equal.
 rewrite Series_scal_l. rewrite Series_geom.
 2:{ rewrite Rabs_inv, <- Rinv_1.
     apply Rinv_lt_contravar; rewrite Rabs_pos_eq; nra'. }
 replace (2 * S k)%nat with (2 + 2*k)%nat by lia.
 rewrite pow_add. field; repeat split; try lra'.
 - apply pow_nonzero; lra'.
 - nra'.
Qed.

Lemma Eq12 :
  (root^2 * (μ A - μ Bkpoly) =
   Series (fun n => (α' (n + S k))^2) -
   Series (fun n => (γ' (n + S k))^2))%R.
Proof.
 rewrite Rmult_minus_distr_l.
 apply RtoC_inj. rtoc.
 rewrite <- Mu_vAf, <- Mu_vB, α_square, γ_square.
 rewrite α_square_real, γ_square_real.
 rewrite (Series_incr_n _ (S k)); try lia; try apply α'_square_ex.
 rewrite (Series_incr_n (fun n => (γ' n)^2)%R (S k));
  try lia; try apply γ'_square_ex.
 simpl pred. rewrite <- !sum_n_Reals.
 erewrite sum_n_ext_loc.
 2:{ intros n Hn. apply RtoC_inj. rtoc.
     rewrite <- α_real, α_γ_init, γ_real; trivial.
     now ctor. }
 erewrite Series_ext. 2:{ intros. now rewrite Nat.add_comm. }
 erewrite (Series_ext (fun n => (γ' (S k+n))^2)%R).
 2:{ intros. now rewrite Nat.add_comm. }
 rtoc. ring.
Qed.

Lemma Ineq12 :
 (β (S k) + γ' (S k))^2 <=
 root^2 * (μ A - μ Bkpoly) + (root^2-1) / root^(2*k) * (B' k root)^2.
Proof.
 replace (β _ + γ' _)%R with (α' (S k)).
 2:{ apply RtoC_inj. rtoc.
     now rewrite <- α_real, <- γ_real, α_γ_Sk. }
 rewrite Eq12, <- γ_square_rest. ring_simplify.
 rewrite Series_incr_1.
 2:{ eapply ex_series_ext. { intros. now rewrite Nat.add_comm. }
     rewrite <- (ex_series_incr_n (fun n => (α' n)^2)%R (S k)).
     apply α'_square_ex. }
 rewrite <- (Rplus_0_r ((α' (S k))^2)), Nat.add_0_l.
 apply Rplus_le_compat_l.
 eapply pos_series_pos_lim; [apply Series_correct|].
 - eapply ex_series_ext.
   { intros. now rewrite Nat.add_succ_l, <- Nat.add_succ_r, Nat.add_comm. }
   rewrite <- (ex_series_incr_n (fun n => (α' n)^2)%R (S (S k))).
   apply α'_square_ex.
 - intros. cbv beta. nra.
Qed.

Definition Cond10 :=
  (μ A <= μ Bkpoly)%R /\
  (Rabs (B' k root) / root^k * (root - /root + sqrt (root^2-1)) < 1)%R.

Lemma Four_core : Cond10 -> β (S k) = Z0.
Proof.
 intros (H1,H2).
 assert (LE : Rabs (β (S k) + γ' (S k)) <=
              sqrt (root^2-1) / root^k * Rabs (B' k root)).
 { rewrite <- (Rabs_pos_eq (sqrt (root^2-1) / root^k)).
   2:{ unfold Rdiv. apply Rmult_le_pos. apply sqrt_pos.
       apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra'. }
   rewrite <- Rabs_mult.
   apply Rsqr_le_abs_0.
   unfold Rdiv. rewrite !Rsqr_mult.
   rewrite Rsqr_sqrt by nra'.
   rewrite !Rsqr_pow2. rewrite pow_inv, <- pow_mult, Nat.mul_comm.
   etransitivity; [apply Ineq12|]. nra. }
 assert (LT : Rabs (β (S k)) < 1).
 { replace (IZR (β (S k)))
    with ((β (S k) + γ' (S k)) + - γ' (S k))%R by ring.
   eapply Rle_lt_trans; [apply Rabs_triang|].
   rewrite Rabs_Ropp.
   eapply Rle_lt_trans; [apply Rplus_le_compat_r; apply LE|]. clear LE.
   rewrite <- (Cmod_R (γ' _)), <- γ_real.
   rewrite γ_alt by lia. rewrite Cmod_mult, Cmod_div.
   rewrite B_real, Cmod_R.
   rewrite Cmod_pow. ctor. rewrite !Cmod_R.
   rewrite (Rabs_left (1 - _)) by nra'.
   rewrite (Rabs_pos_eq root) by lra'.
   eapply Rle_lt_trans; [|apply H2]. apply Req_le.
   rewrite <- (tech_pow_Rmult root k). field; split; try lra'.
   apply pow_nonzero; lra'. }
 apply Rabs_def2 in LT. destruct LT as (LT,LT').
 change (- (1))%R with (IZR (-1)) in LT'.
 apply lt_IZR in LT, LT'; lia.
Qed.

End Lemma4_Fixedk.

Lemma Four_rec_aux k :
  Cond10 k -> forall n, β (n + S k) = Z0 /\ Cond10 (n + k).
Proof.
 intros H.
 induction n.
 - split. now apply Four_core. easy.
 - destruct IHn as (IH1,IH2). simpl.
   assert (E : forall x, B (S (n+k)) x = B (n+k) x).
   { intros x. unfold B. rewrite sum_Sn.
     rewrite Nat.add_succ_r in IH1.
     now rewrite IH1, Cmult_0_l, Cplus_0_r. }
   assert (Cond10 (S (n + k))).
   { destruct IH2 as (IH21,IH22).
     split.
     - rewrite IH21. apply Req_le. apply RtoC_inj. rewrite !μB.
       apply Mu_ext. intros c Hc. symmetry. apply E.
     - rewrite <- Cmod_R, <- B_real in IH22 |- *. rewrite E.
       eapply Rle_lt_trans; [|apply IH22]. apply Rmult_le_compat_r.
       { apply Rplus_le_le_0_compat; try apply sqrt_pos. lra'. }
       unfold Rdiv. apply Rmult_le_compat_l; try apply Cmod_ge_0.
       simpl. rewrite Rinv_mult.
       rewrite <- (Rmult_1_l (/root ^(n+k))) at 2.
       apply Rmult_le_compat_r; try lra'.
       rewrite <- pow_inv. apply Rpow_pos. lra'. }
   split; trivial. apply Four_core. now rewrite Nat.add_succ_r.
Qed.

Lemma Poly_continuously_null p r :
  0 < r -> (forall x:R, 0 <= x < r -> Peval p x = 0) -> Peq p [].
Proof.
 intros Hr Hx.
 set (d := S (degree p)).
 assert (RD : 0 < r/d).
 { unfold Rdiv. apply Rmult_lt_0_compat; trivial.
   apply Rinv_0_lt_compat. apply RSpos. }
 apply (extra_roots_implies_null p (map (fun k:nat => k*r/d) (seq 0 d))).
 - apply FinFun.Injective_map_NoDup; try apply seq_NoDup.
   intros k k'. intros E. unfold Cdiv in E. rewrite <- !Cmult_assoc in E.
   apply Cmult_eq_reg_r in E. now apply RtoC_inj, INR_eq in E.
   ctor. unfold Rdiv in RD. intros E'. apply RtoC_inj in E'. lra.
 - intros x. rewrite in_map_iff. intros (x' & <- & IN).
   rewrite in_seq in IN. destruct IN as (LE,LT). apply le_INR in LE.
   apply lt_INR in LT. rewrite Nat.add_0_l in LT.
   ctor. apply Hx. split.
   + unfold Rdiv. rewrite Rmult_assoc.
     apply Rmult_le_pos; trivial. apply Rlt_le, RD.
   + apply Rmult_lt_compat_r with (r := (r/d)%R) in LT; trivial.
     unfold Rdiv in *. rewrite Rmult_assoc.
     rewrite (Rmult_comm r (/d)) in LT at 2.
     rewrite <- (Rmult_assoc d), Rinv_r, Rmult_1_l in LT. trivial.
     generalize (RSpos (degree p)). unfold d. lra.
 - rewrite map_length, seq_length. lia.
Qed.

Lemma Popp_eval p x : Peval (-, p) x = - Peval p x.
Proof.
 unfold Popp. rewrite Pmult_eval, Pconst_eval. lca.
Qed.

Lemma Poly_continuously_eq p q r :
  0 < r -> (forall x:R, 0 <= x < r -> Peval p x = Peval q x) -> Peq p q.
Proof.
 intros Hr E.
 assert (E' : Peq (p +, -, q) []).
 { apply Poly_continuously_null with r; trivial.
   intros x Hx. rewrite Pplus_eval, Popp_eval.
   rewrite E; trivial. ring. }
 apply (Pplus_eq_compat _ _ q q) in E'; try easy.
 simpl in E'. now rewrite Pplus_assoc, Pplus_opp_l, Pplus_0_r in E'.
Qed.

Lemma Four k : Cond10 k -> B k root = 0.
Proof.
 intros H10.
 assert (EQ : forall x, Cmod x < /root ->
              Peval (Zpoly A) x * f x = B k x).
 { intros x Hx.
   rewrite <- (CPowerSeries_unique _ _ _ (β_ok x Hx)).
   unfold CPowerSeries.
   rewrite (CSeries_incr_n _ (S k)).
   2:{ apply ex_series_Cmod.
       eapply ex_series_ext.
       { intros n. symmetry. unfold "∘".
         now rewrite Cmod_mult, Cmod_pow. }
       rewrite <- ex_pseries_R.
       apply CV_radius_inside.
       change (CV_radius _) with (CV_radius (Cmod∘β)).
       rewrite <- (C_CV_radius_alt β).
       eapply Rbar.Rbar_lt_le_trans; [|apply β_radius].
       simpl. rewrite Rabs_pos_eq; trivial. apply Cmod_ge_0. }
   erewrite CSeries_ext with (v := RtoC ∘ (fun _ => 0%R)).
   2:{ intros n. rewrite Nat.add_comm at 1.
       destruct (Four_rec_aux _ H10 n) as (->,_).
       now rewrite Cmult_0_l. }
   rewrite CSeries_RtoC. rewrite (is_series_unique _ _ is_series_R0).
   2:{ eexists; apply is_series_R0. }
   rewrite Cplus_0_r.
   unfold B.
   now rewrite big_sum_sum_n. }
 assert (EQ' : Peq ([RtoC sgn] *, Zpoly A *, Pcoef)
                (Zpoly (take (S k) β) *, reciprocal Pcoef)).
 { apply Poly_continuously_eq with (/root)%R; try lra'.
   intros x Hx. rewrite !Pmult_eval, Pconst_eval, Bkpoly_ok, <- EQ.
   2:{ rewrite Cmod_R, Rabs_pos_eq; lra. }
   unfold f. field.
   destruct (Req_dec x 0).
   - subst. rewrite Peval_0.
     rewrite reciprocal_coef by lia.
     rewrite Nat.sub_0_r.
     rewrite Hcoefs.
     rewrite linfactors_degree, linfactors_coef. intros [=H]; lra.
   - intros E. apply reciprocal_root in E.
     2:{ intros [=H']; lra. }
     revert E. apply below_invroot.
     2:{ intros [=H']; lra. }
     rewrite Cmod_R, Rabs_pos_eq; lra. }
 assert (EQ2 : B k root * Peval (reciprocal Pcoef) root = 0).
 { rewrite <- Bkpoly_ok, <- Pmult_eval, <- EQ', !Pmult_eval.
   replace (Peval Pcoef root) with 0. ring.
   symmetry. rewrite Hcoefs. apply -> linfactors_roots. now left. }
 apply Cmult_integral in EQ2. destruct EQ2 as [EQ2|EQ2]; trivial.
 apply reciprocal_root in EQ2.
 2:{ intros [=H']; lra'. }
 rewrite Hcoefs, <- linfactors_roots in EQ2. destruct EQ2 as [EQ2|EQ2].
 - rewrite <- RtoC_inv in EQ2. apply RtoC_inj in EQ2. lra'.
 - now apply invroot_no_roots in EQ2.
Qed.

End Lemma4.

Close Scope C.

Lemma root_lt_sqrt2 : root < sqrt 2.
Proof.
 apply Rsqr_incrst_0; try lra'. 2:apply sqrt_pos.
 rewrite Rsqr_sqrt by lra. now rewrite Rsqr_pow2.
Qed.

Lemma Ineq14 (x:R) : 1<x -> 0 <= x - /x + sqrt(x^2-1) < x^2.
Proof.
 intros Hx.
 assert (Hx' : 0 < /x < 1).
 { split.
   - apply Rinv_0_lt_compat; lra.
   - rewrite <- Rinv_1. apply Rinv_lt_contravar; lra. }
 split.
 - generalize (sqrt_pos (x^2-1)); lra.
 - assert (LT : x-/x < sqrt(x^2-1)).
   { apply Rsqr_incrst_0; try lra. 2:apply sqrt_pos.
     rewrite Rsqr_sqrt. 2:nra. rewrite Rsqr_pow2; ring_simplify.
     rewrite Rmult_assoc, Rinv_r by lra. nra. }
   apply Rlt_le_trans with (2*sqrt(x^2-1)); try lra. clear LT.
   apply Rsqr_incr_0_var; try nra.
   rewrite Rsqr_mult, Rsqr_sqrt; try nra. rewrite !Rsqr_pow2.
   replace (2^2) with 4 by ring.
   apply Rminus_le_0. replace (_-_) with ((x^2-2)^2) by ring.
   apply pow2_ge_0.
Qed.

Definition A1 := [1;0;-1;-1]%Z.
Definition A2 := [1;-1;0;0;-1]%Z.
Definition A3 a := [1;-1;-1;1;0;3-a]%Z.
Definition A4 := [1;-1;0;-1]%Z.
Definition A5 b := [1;-1;-1;0;1;0;6-b]%Z.
Definition A6 c d := [1;0;-1;-1;3-c;1+c-d]%Z.

Definition B1 := [1;1;0;-1]%Z.
Definition B2 := [1;0;0;1;-1]%Z.
Definition B3 := [1;0;-1;1;1;-1]%Z.
Definition B4 := [1;0;1;-1]%Z.
Definition B5 := [1;0;-1;0;1;1;-1]%Z.
Definition B6 := [1;1;1;1;0;-1]%Z.

Definition B1_fun (x:R) := 1-x*(x^2-1).

Lemma B1_fun_ok (x:R) : Peval (Zpoly B1) x = B1_fun x.
Proof.
 unfold B1, B1_fun, Peval. simpl. unfold "∘". rtoc. ring.
Qed.

Lemma B1_bound x : 1 < x < sqrt 2 -> -1 < B1_fun x < 1.
Proof.
 intros Hx.
 assert (Hx' : 0 < x^2-1 < 1).
 { split. nra. destruct Hx as (Hx1,Hx2).
   apply Rsqr_incrst_1 in Hx2; try lra. rewrite Rsqr_sqrt in Hx2 by lra.
   rewrite Rsqr_pow2 in Hx2. lra. }
 unfold B1_fun. nra.
Qed.

Lemma Case1_mu5 : Case1 -> root = Mu.mu 5.
Proof.
 intros C.
 assert (E : take 4 (β A1) = B1).
 { revert C. unfold Case1, take. simpl. unfold β, ZPS_mult.
   cbn -[Z.mul]. now intros [= -> -> -> ->]. }
 assert (E' : B A1 3 root = 0%C).
 { apply Four. split.
   - now rewrite E.
   - rewrite <- Cmod_R, <- B_real, <- Bkpoly_ok, E, B1_fun_ok, Cmod_R.
     rewrite <- (Rinv_l (root^2)) at 2 by nra'.
     apply Rmult_lt_compat; [|apply Ineq14; lra'].
     split.
     + unfold Rdiv. apply Rmult_le_pos. apply Rabs_pos.
       apply Rlt_le, Rinv_0_lt_compat. nra'.
     + apply Rmult_lt_reg_r with (root^3). nra'.
       unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by nra'.
       field_simplify; try nra'.
       apply Rlt_trans with 1; try lra'.
       apply Rcomplements.Rabs_lt_between. apply B1_bound. split. lra'.
       apply root_lt_sqrt2. }
 rewrite <- Bkpoly_ok, E, B1_fun_ok in E'.
 unfold B1_fun in E'. apply RtoC_inj in E'.
 assert (E3 : root^3 = 1+root). { ring_simplify in E'. lra. }
 apply mu_unique. lra'. simpl Nat.sub. ring [E3].
Qed.

Definition B2_fun (x:R) := 1-x^3*(x-1).

Lemma B2_fun_ok (x:R) : Peval (Zpoly B2) x = B2_fun x.
Proof.
 unfold B2, B2_fun, Peval. simpl. unfold "∘". rtoc. ring.
Qed.

Lemma B2_bound x : 1 < x < sqrt 2 -> -1 < B2_fun x < 1.
Proof.
 intros Hx.
 assert (Hx' : 0 < x-1 < /2).
 { split. lra.
   assert (sqrt 2 < 3/2); try lra.
   { apply Rsqr_incrst_0; try lra. rewrite Rsqr_sqrt, Rsqr_pow2; lra. }}
 unfold B2_fun.
 assert (0 < x^3*(x-1) < 4*/2); try lra.
 { split. apply Rmult_lt_0_compat; nra. apply Rmult_lt_compat; nra. }
Qed.

Lemma Case2_mu4 : Case2 -> root = Mu.mu 4.
Proof.
 intros C.
 assert (E : take 5 (β A2) = B2).
 { revert C. unfold Case2, take. simpl. unfold β, ZPS_mult.
   cbn -[Z.mul]. now intros [= -> -> -> -> ->]. }
 assert (E' : B A2 4 root = 0%C).
 { apply Four. split.
   - now rewrite E.
   - rewrite <- Cmod_R, <- B_real, <- Bkpoly_ok, E, B2_fun_ok, Cmod_R.
     rewrite <- (Rinv_l (root^2)) at 2 by nra'.
     apply Rmult_lt_compat; [|apply Ineq14; lra'].
     split.
     + unfold Rdiv. apply Rmult_le_pos. apply Rabs_pos.
       apply Rlt_le, Rinv_0_lt_compat. nra'.
     + apply Rmult_lt_reg_r with (root^4). nra'.
       unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by nra'.
       field_simplify; try nra'.
       apply Rlt_trans with 1; try nra'.
       apply Rcomplements.Rabs_lt_between. apply B2_bound. split. lra'.
       apply root_lt_sqrt2. }
 rewrite <- Bkpoly_ok, E, B2_fun_ok in E'.
 unfold B2_fun in E'. apply RtoC_inj in E'.
 apply mu_unique. lra'. simpl Nat.sub. ring_simplify in E'. lra.
Qed.

Definition B3_fun (x:R) := 1-x^2*(x^2-1)*(x-1).

Lemma B3_fun_ok (x:R) : Peval (Zpoly B3) x = B3_fun x.
Proof.
 unfold B3, B3_fun, Peval. simpl. unfold "∘". rtoc. ring.
Qed.

Lemma B3_bound x : 1 < x < sqrt 2 -> 0 < B3_fun x < 1.
Proof.
 intros Hx.
 assert (Hx' : 0 < x-1 < /2).
 { split. lra.
   assert (sqrt 2 < 3/2); try lra.
   { apply Rsqr_incrst_0; try lra. rewrite Rsqr_sqrt, Rsqr_pow2; lra. }}
 assert (Hx2 : 0 < x^2-1 < 1).
 { split. nra. destruct Hx as (Hx1,Hx2).
   apply Rsqr_incrst_1 in Hx2; try lra. rewrite Rsqr_sqrt in Hx2 by lra.
   rewrite Rsqr_pow2 in Hx2. lra. }
 unfold B3_fun.
 assert (0 < x^2*(x^2-1)*(x-1) < 2*1*/2); try lra.
 { split. repeat (apply Rmult_lt_0_compat; nra).
   repeat (apply Rmult_lt_compat; nra). }
Qed.

Lemma Case3_impossible : Case3 -> False.
Proof.
 intros C.
 assert (0 < B3_fun root < 1).
 { apply B3_bound. split; [lra'|apply root_lt_sqrt2]. }
 set (a := fps' 5).
 assert (E : take 6 (β (A3 a)) = B3).
 { revert C. unfold Case3, take. simpl. unfold β, ZPS_mult.
   cbn -[Z.mul Z.sub]. intros ([= -> -> -> -> ->], LE).
   unfold B3. do 6 f_equal. fold a. ring. }
 assert (E' : B (A3 a) 5 root = 0%C).
 { apply Four. split.
   - rewrite E. red in C. fold a in C.
     unfold A3, B3. cbn -[Z.mul Z.sub].
     assert (A : (a = 3 \/ a = 4)%Z) by lia.
     destruct A as [-> | ->]; simpl; lra.
   - rewrite <- Cmod_R, <- B_real, <- Bkpoly_ok, E, B3_fun_ok, Cmod_R.
     rewrite <- (Rinv_l (root^2)) at 2 by nra'.
     apply Rmult_lt_compat; [|apply Ineq14; lra'].
     split.
     + unfold Rdiv. apply Rmult_le_pos. apply Rabs_pos.
       apply Rlt_le, Rinv_0_lt_compat. apply pow_lt; lra'.
     + apply Rmult_lt_reg_r with (root^5). (apply pow_lt; lra').
       unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
       2:{ apply pow_nonzero; lra'. }
       field_simplify; try nra'.
       apply Rlt_trans with 1; try nra'.
       rewrite Rabs_pos_eq; lra. }
 rewrite <- Bkpoly_ok, E, B3_fun_ok in E'. apply RtoC_inj in E'. lra.
Qed.

Definition B4_fun (x:R) := 1-x^2*(x-1).

Lemma B4_fun_ok (x:R) : Peval (Zpoly B4) x = B4_fun x.
Proof.
 unfold B4, B4_fun, Peval. simpl. unfold "∘". rtoc. ring.
Qed.

Lemma B4_bound x : 1 < x < sqrt 2 -> 0 < B4_fun x < 1.
Proof.
 intros Hx.
 assert (Hx' : 0 < x-1 < /2). { generalize sqrt2_approx; lra. }
 assert (Hx2 : 1 < x^2 < 2).
 { split. nra. destruct Hx as (Hx1,Hx2).
   apply Rsqr_incrst_1 in Hx2; try lra. rewrite Rsqr_sqrt in Hx2 by lra.
   rewrite Rsqr_pow2 in Hx2. lra. }
 unfold B4_fun.
 assert (0 < x^2*(x-1) < 2*/2); try lra.
 { split. apply Rmult_lt_0_compat; nra. apply Rmult_lt_compat; nra. }
Qed.

Lemma Case4_impossible : Case4 -> False.
Proof.
 intros C.
 assert (0 < B4_fun root < 1).
 { apply B4_bound. split; [lra'|apply root_lt_sqrt2]. }
 assert (E : take 4 (β A4) = B4).
 { revert C. unfold Case4, take. simpl. unfold β, ZPS_mult.
   cbn -[Z.mul]. now intros [= -> -> -> ->]. }
 assert (E' : B A4 3 root = 0%C).
 { apply Four. split.
   - now rewrite E.
   - rewrite <- Cmod_R, <- B_real, <- Bkpoly_ok, E, B4_fun_ok, Cmod_R.
     rewrite <- (Rinv_l (root^2)) at 2 by nra'.
     apply Rmult_lt_compat; [|apply Ineq14; lra'].
     split.
     + unfold Rdiv. apply Rmult_le_pos. apply Rabs_pos.
       apply Rlt_le, Rinv_0_lt_compat. nra'.
     + apply Rmult_lt_reg_r with (root^3). nra'.
       unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by nra'.
       field_simplify; try nra'.
       apply Rlt_trans with 1; try lra'.
       rewrite Rabs_pos_eq; lra. }
 rewrite <- Bkpoly_ok, E, B4_fun_ok in E'. apply RtoC_inj in E'. lra.
Qed.

Definition B5_fun (x:R) := 1-x^2+x^4+x^5-x^6.

Lemma B5_fun_ok (x:R) : Peval (Zpoly B5) x = B5_fun x.
Proof.
 unfold B5, B5_fun, Peval. simpl. unfold "∘". rtoc. ring.
Qed.

Lemma B5_eqn x :
  x<>0 -> B5_fun x / x^3 = 1 - (1-/x^2)*(1+(x-1)^2*(x+/x+1)).
Proof.
 intros Hx. unfold B5_fun. now field.
Qed.

Lemma B5_bound x : 1 < x < sqrt 2 -> 0 < B5_fun x / x^3 < 1.
Proof.
 intros Hx.
 rewrite B5_eqn by lra.
 set (y := 1 - / x^2).
 set (z := 1 + _).
 assert (0 < y < 1/2).
 { unfold y. assert (/2 < /x^2 < /1); try lra.
   split; apply Rinv_lt_contravar; try nra.
   rewrite <- (Rsqr_sqrt 2), <- Rsqr_pow2 by lra.
   apply Rsqr_incrst_1; lra. }
 assert (1 < z < 2).
 { unfold z. assert (0 < (x-1)^2 * (x + /x + 1) < 1); try lra.
   split.
   - apply Rmult_lt_0_compat. nra. generalize (Rinv_0_lt_compat x). lra.
   - rewrite <- (Rinv_l 4) at 3 by lra.
     apply Rmult_lt_compat.
     + split; try nra. replace (/4) with ((/2)^2) by lra.
       apply Rpow_lt_compat_r; generalize sqrt2_approx; try lra; try lia.
     + split.
       * generalize (Rinv_0_lt_compat x). lra.
       * assert (/x < 1). { rewrite <- Rinv_1. apply Rinv_lt_contravar; nra. }
         generalize sqrt2_approx; lra. }
 nra.
Qed.

Lemma Case5_impossible : Case5 -> False.
Proof.
 intros C.
 assert (0 < B5_fun root / root^3 < 1).
 { apply B5_bound. split; [lra'|apply root_lt_sqrt2]. }
 set (b := fps' 6).
 assert (E : take 7 (β (A5 b)) = B5).
 { revert C. unfold Case5, take. simpl. unfold β, ZPS_mult.
   cbn -[Z.mul Z.sub]. intros ([= -> -> -> -> -> ->], LE).
   unfold B5. do 7 f_equal. fold b. ring. }
 assert (E' : B (A5 b) 6 root = 0%C).
 { apply Four. split.
   - rewrite E. red in C. fold b in C.
     unfold A5, B5. cbn -[Z.mul Z.sub].
     assert (A : (b = 5 \/ b = 6 \/ b = 7)%Z) by lia.
     destruct A as [-> |[-> | ->]]; simpl; lra.
   - rewrite <- Cmod_R, <- B_real, <- Bkpoly_ok, E, B5_fun_ok, Cmod_R.
     rewrite <- (Rinv_l (root^2)) at 2 by nra'.
     apply Rmult_lt_compat; [|apply Ineq14; lra'].
     split.
     + unfold Rdiv. apply Rmult_le_pos. apply Rabs_pos.
       apply Rlt_le, Rinv_0_lt_compat. apply pow_lt; lra'.
     + apply Rmult_lt_reg_r with (root^3). (apply pow_lt; lra').
       field_simplify; try lra'.
       rewrite <- (Rabs_pos_eq (root^3)) by nra'.
       unfold Rdiv in *. rewrite <- Rabs_inv, <- Rabs_mult.
       apply Rlt_trans with 1; try lra'.
       rewrite Rabs_pos_eq; lra. }
 rewrite <- Bkpoly_ok, E, B5_fun_ok in E'. apply RtoC_inj in E'. nra.
Qed.

Definition B6_fun (x:R) := 1+x+x^2+x^3-x^5.

Lemma B6_fun_ok (x:R) : Peval (Zpoly B6) x = B6_fun x.
Proof.
 unfold B6, B6_fun, Peval. simpl. unfold "∘". rtoc. ring.
Qed.

Lemma B6_eqn x :
  x<>0 -> B6_fun x / x^3 = /x^3 + /x^2 + /x + 1 - x^2.
Proof.
 intros Hx. unfold B6_fun. now field.
Qed.

Lemma B6_bound x : 4/3 < x < sqrt 2 -> 0 < B6_fun x / x^3 < 1.
Proof.
 intros Hx.
 rewrite B6_eqn by lra.
 set (f := fun x => /x^3 + /x^2 + /x + 1 - x^2).
 change (0 < f x < 1).
 assert (F : forall a b, 0 < a < b -> f b < f a).
 { intros a b Hab. unfold f. rewrite !Rplus_assoc.
   repeat (apply Rplus_lt_compat_r || apply Rplus_lt_compat);
     repeat apply Rinv_lt_contravar; try nra;
       try apply Rmult_lt_0_compat; try nra.
   apply pow_lt; lra.
   apply pow_lt; lra.
   apply Rpow_lt_compat_r; try lia; lra. }
 split.
 - transitivity (f (sqrt 2)); [|apply F; lra].
   unfold f. replace ((sqrt 2)^3) with ((sqrt 2)^2 * sqrt 2) by ring.
   replace (sqrt 2^2) with 2.
   2:{ rewrite <- Rsqr_pow2, Rsqr_sqrt; lra. }
   rewrite Rinv_mult.
   replace (/sqrt 2) with (sqrt 2/ 2).
   2:{ apply Rmult_eq_reg_l with (sqrt 2). 2:apply sqrt2_neq_0.
       rewrite Rinv_r by apply sqrt2_neq_0.
       unfold Rdiv. rewrite <- Rmult_assoc, sqrt_sqrt; lra. }
   generalize sqrt2_approx; lra.
 - transitivity (f (4/3)); [apply F; lra|]. unfold f. lra.
Qed.

Lemma Case6_impossible : Case6 -> False.
Proof.
 intros C.
 assert (H : 4/3 < root).
 { apply root_43. now destruct C as ([= _ _ ->], _). }
 assert (0 < B6_fun root / root^3 < 1).
 { apply B6_bound. split; [lra|apply root_lt_sqrt2]. }
 set (c := fps' 4).
 set (d := fps' 5).
 assert (E : take 6 (β (A6 c d)) = B6).
 { revert C. unfold Case6, take. simpl. unfold β, ZPS_mult.
   cbn -[Z.mul Z.sub Z.add]. intros ([= -> -> -> ->], LE).
   unfold B6. do 6 f_equal; fold c; fold d. ring. ring. }
 assert (E' : B (A6 c d) 5 root = 0%C).
 { apply Four. split.
   - rewrite E. destruct C as (_,LE). fold c in LE; fold d in LE.
     unfold A6, B6. cbn -[Z.mul Z.sub Z.add].
      repeat (destruct LE as [[= <- <-]|LE]; [simpl; lra|]). easy.
   - rewrite <- Cmod_R, <- B_real, <- Bkpoly_ok, E, B6_fun_ok, Cmod_R.
     rewrite <- (Rinv_l (root^2)) at 2 by nra'.
     apply Rmult_lt_compat; [|apply Ineq14; lra'].
     split.
     + unfold Rdiv. apply Rmult_le_pos. apply Rabs_pos.
       apply Rlt_le, Rinv_0_lt_compat. apply pow_lt; lra'.
     + apply Rmult_lt_reg_r with (root^2). (apply pow_lt; lra').
       field_simplify; try lra'.
       rewrite <- (Rabs_pos_eq (root^3)) by nra'.
       unfold Rdiv in *. rewrite <- Rabs_inv, <- Rabs_mult.
       rewrite Rabs_pos_eq; lra. }
 rewrite <- Bkpoly_ok, E, B6_fun_ok in E'. apply RtoC_inj in E'. nra.
Qed.

Lemma SiegelMain : root = Mu.mu 4 \/ root = Mu.mu 5.
Proof.
 destruct Three as [C1|[C2|[C3|[C4|[C5|C6]]]]].
 - right. now apply Case1_mu5.
 - left. now apply Case2_mu4.
 - exfalso. now apply Case3_impossible.
 - exfalso. now apply Case4_impossible.
 - exfalso. now apply Case5_impossible.
 - exfalso. now apply Case6_impossible.
Qed.

End Siegel.
End SiegelProof.

Lemma SiegelTheoremFull x :
  Pisot x -> x < sqrt 2 -> x = Mu.mu 4 \/ x = Mu.mu 5.
Proof.
 intros H1 H2.
 rewrite Pisot_alt in H1. destruct H1 as (roots,H1).
 assert (H1' := H1).
 destruct H1' as (H3 & H4 & _). rewrite IntPoly_alt' in H4.
 destruct H4 as (coefs & H4). symmetry in H4.
 assert (H2' : x^2 < 2).
 { rewrite <- (Rsqr_sqrt 2), Rsqr_pow2 by lra.
   apply Rpow_lt_compat_r; try lia; lra. }
 apply (SiegelProof.SiegelMain x H2' roots H1 coefs H4).
Qed.

Lemma SiegelTheorem x : Pisot x -> Mu.mu 5 <= x.
Proof.
 intros Hx.
 destruct (Rle_lt_dec (sqrt 2) x) as [Hx'|Hx'].
 - generalize mu_5 sqrt2_approx. lra.
 - destruct (SiegelTheoremFull x Hx Hx') as [-> | ->]; try easy.
   generalize mu_4 mu_5; lra.
Qed.

Lemma mu_non_Pisot_above_6 n : (6 <= n)%nat -> ~Pisot (mu n).
Proof.
 intros Hn.
 assert (mu n < mu 5).
 { replace n with ((n-6)+6)%nat by lia. clear Hn.
   induction (n-6)%nat.
   - apply mu_decr; lia.
   - eapply Rlt_trans; eauto. apply mu_decr; lia. }
 intros P. apply SiegelTheorem in P. lra.
Qed.
