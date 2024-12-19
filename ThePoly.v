From Coq Require Import Lia Reals Lra Permutation.
From QuantumLib Require Import Complex Matrix Eigenvectors VecSet Polynomial.
Require Import MoreList MoreReals MoreLim MoreComplex MoreSum MorePoly.
Require Import MoreMatrix GenFib GenG Mu.
Local Open Scope C.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

Definition ThePoly (q:nat) : Polynomial :=
 monom C1 (q+1) +, monom (-C1) q +, [-C1].

Lemma ThePoly_eval q x : Peval (ThePoly q) x = x^(S q)-x^q-1.
Proof.
 unfold ThePoly. rewrite !Pplus_eval, !monom_eval.
 rewrite Nat.add_1_r, Cmult_1_l. rewrite Pconst_eval. ring.
Qed.

Lemma ThePoly_root_carac r q : Root r (ThePoly q) <-> r^(S q) = r^q + 1.
Proof.
 unfold Root. rewrite ThePoly_eval. rewrite (Ceq_minus _ (_+_)).
 unfold Cminus. now rewrite Copp_plus_distr, Cplus_assoc.
Qed.

Lemma mu_is_root q : Root (mu q) (ThePoly q).
Proof.
 rewrite ThePoly_root_carac.
 now rewrite !RtoC_pow, mu_carac, !RtoC_plus.
Qed.

Lemma root_nz q : ~ Root C0 (ThePoly q).
Proof.
 rewrite !ThePoly_root_carac.
 destruct q; simpl; intros E; ring_simplify in E;
  apply RtoC_inj_neq in E;trivial; lra.
Qed.

Lemma root_non_1 q : ~ Root C1 (ThePoly q).
Proof.
 rewrite !ThePoly_root_carac. rewrite !Cpow_1_l.
 intro E. ring_simplify in E. apply RtoC_inj_neq in E; trivial. lra.
Qed.

Lemma ThePoly_subdeg q : (degree (monom (-C1) q +, [-C1]) <= q)%nat.
Proof.
 etransitivity; [apply Pplus_degree1| ].
 rewrite monom_degree. 2:apply Copp_neq_0_compat, C1_neq_C0.
 generalize (degree_length [-C1]). simpl. lia.
Qed.

Lemma ThePoly_deg q : degree (ThePoly q) = S q.
Proof.
 unfold ThePoly.
 rewrite Pplus_assoc, Pplus_comm.
 rewrite Pplus_degree2.
 rewrite monom_degree. lia. apply C1_neq_C0.
 rewrite monom_degree. 2:apply C1_neq_C0.
 generalize (ThePoly_subdeg q). lia.
Qed.

Lemma ThePoly_monic (q:nat) : monic (ThePoly q).
Proof.
 unfold ThePoly. rewrite Pplus_assoc, Pplus_comm. unfold monic.
 rewrite topcoef_plus_ltdeg. apply topcoef_monom.
 rewrite monom_degree. 2:apply C1_neq_C0.
 generalize (ThePoly_subdeg q). lia.
Qed.

Lemma ThePoly_diff q : q<>O ->
 Pdiff (ThePoly q) ≅ [-q; q+1] *, monom C1 (q-1).
Proof.
 intros Hq.
 unfold ThePoly.
 rewrite !Pdiff_plus, !diff_monom.
 replace (pred (q+1)) with (S (q-1)) by lia.
 replace (pred q) with (q-1)%nat by lia.
 simpl Pdiff. rewrite Pzero_alt, Pplus_0_r.
 rewrite monom_S.
 rewrite (monom_scale (-C1)), <- Pmult_assoc.
 replace ([RtoC q] *, [-C1]) with [-RtoC q].
 2: simpl; f_equal; lca.
 rewrite <- Pmult_X. rewrite <- Pmult_assoc.
 rewrite (Pmult_comm _ _X_), Pmult_X.
 rewrite <- Pmult_plus_distr_r. simpl Pplus.
 apply Peq_iff. f_equal. f_equal. f_equal. lca.
 f_equal. rewrite plus_INR, RtoC_plus. lca.
Qed.

Lemma ThePoly_diff_0 : Pdiff (ThePoly 0) ≅ [C1].
Proof.
 unfold ThePoly. simpl. apply Peq_iff.
 rewrite Cplus_0_r. apply (app_C0_compactify_reduce_1 [C1]).
Qed.

Lemma ThePoly_no_common_root_with_diff q c :
  Root c (ThePoly q) -> ~ Root c (Pdiff (ThePoly q)).
Proof.
 intros Hc.
 destruct (Nat.eq_dec q 0) as [->|Hq].
 - rewrite ThePoly_diff_0. unfold Root. cbn. rewrite Cmult_1_l, Cplus_0_l.
   apply C1_neq_C0.
 - rewrite ThePoly_diff by trivial.
   unfold Root.
   rewrite Pmult_eval, monom_eval. cbn.
   rewrite !Cmult_1_r, Cmult_1_l, Cplus_0_l. intro E.
   apply Cmult_integral in E. destruct E as [E|E].
   + rewrite Cplus_comm in E. apply Ceq_minus in E.
     assert (Hc' : c = (INR q / INR (S q))%C).
     { rewrite <- E. rewrite <- RtoC_plus, <- S_INR. field.
       intros H'. apply RtoC_inj in H'. generalize (RSpos q). lra. }
     rewrite <- RtoC_div in Hc'.
     revert Hc.
     rewrite ThePoly_root_carac, Ceq_minus. unfold Cminus.
     rewrite Copp_plus_distr, Cplus_assoc.
     change (c^S q - c^q - 1 <> 0)%C.
     replace (c^S q - c^q - 1)%C with (c^S q - (c^q + 1))%C by ring.
     apply Cminus_eq_contra. intro Hc.
     set (r := Rdiv _ _) in *.
     assert (r <= 1).
     { unfold r. apply Rcomplements.Rle_div_l.
       generalize (RSpos q); lra. rewrite S_INR; lra. }
     subst c. rewrite !RtoC_pow, <- RtoC_plus in Hc.
     apply RtoC_inj in Hc.
     apply mu_unique in Hc. generalize (mu_itvl q); lra.
     apply Rcomplements.Rdiv_le_0_compat. apply pos_INR. apply RSpos.
   + revert E.
     apply Cpow_nonzero.
     contradict Hc. subst c.
     rewrite ThePoly_root_carac.
     destruct q; try lia. simpl.
     rewrite !Cmult_0_l, !Cplus_0_l. auto using C1_neq_C0.
Qed.

Lemma ThePoly_separated_roots q :
  exists l, length l = S q /\ NoDup l /\ ThePoly q ≅ linfactors l.
Proof.
 destruct (separated_roots (ThePoly q)) as (l & D & E).
 - apply ThePoly_monic.
 - apply ThePoly_no_common_root_with_diff.
 - exists l; repeat split; auto.
   rewrite <- linfactors_degree. now rewrite <- E, ThePoly_deg.
Qed.

Lemma roots_le_mu q (r:C) :
 Root r (ThePoly q) -> (Cmod r <= mu q)%R.
Proof.
 rewrite ThePoly_root_carac. intros E.
 apply Rnot_lt_le. intros L.
 assert (Iv := mu_itvl q).
 assert (H : mu q -1 < Cmod (r-1)).
 { apply Rlt_le_trans with (Cmod r -1)%R; try lra.
   apply Rle_minus_l.
   replace r with ((r-C1)+C1) at 1 by lca.
   eapply Rle_trans; [apply Cmod_triangle|]. rewrite Cmod_1. lra. }
 assert (H' : (mu q)^q <= Cmod (r^q)).
 { rewrite Cmod_pow. apply pow_incr; lra. }
 assert (LT : (mu q)^q*(mu q -1) < Cmod (r^q*(r-1))).
 { rewrite Cmod_mult. apply Rle_lt_mult_compat; split; try lra.
   apply pow_lt; lra. }
 revert LT. apply Rle_not_lt.
 unfold Rminus, Cminus. rewrite Rmult_plus_distr_l, Cmult_plus_distr_l.
 rewrite Rmult_comm, Cmult_comm. simpl in E. rewrite E.
 assert (E' := mu_carac q). simpl in E'. rewrite E'. ring_simplify.
 replace (_ + _)%C with C1 by ring. rewrite Cmod_1; lra.
Qed.

Lemma other_roots_lt_mu q (r:C) :
 Root r (ThePoly q) -> r <> mu q -> (Cmod r < mu q)%R.
Proof.
 intros R N.
 assert (LE := roots_le_mu q r R).
 apply Rle_lt_or_eq_dec in LE. destruct LE as [LT|E]; trivial.
 destruct N.
 apply ThePoly_root_carac in R.
 assert (E' : (Cmod (r^q * (r - 1)) = mu q^q * (mu q -1))%R).
 { unfold Rminus, Cminus. rewrite Rmult_plus_distr_l, Cmult_plus_distr_l.
   rewrite Rmult_comm, Cmult_comm. simpl in R. rewrite R.
   replace (_ + _)%C with C1 by ring. rewrite Cmod_1.
   generalize (mu_carac q); simpl. intros ->. ring. }
 rewrite Cmod_mult, Cmod_pow, E in E'.
 apply Rmult_eq_reg_l in E'.
 2:{ apply pow_nonzero. generalize (mu_itvl q); lra. }
 rewrite <- E in E'.
 apply Cmod_triangle_exact in E'. congruence.
Qed.

Lemma root_equal_Cmod_Re q (r1 r2:C) :
 Root r1 (ThePoly q) -> Root r2 (ThePoly q) ->
 Cmod r1 = Cmod r2 -> Re r1 = Re r2.
Proof.
 rewrite !ThePoly_root_carac. intros R1 R2 E.
 assert (E' : (Cmod (r1^q * (r1 - 1)) = Cmod (r2^q * (r2 -1)))).
 { unfold Rminus, Cminus. rewrite !Cmult_plus_distr_l.
   rewrite (Cmult_comm _ r1), (Cmult_comm _ r2).
   simpl in R1,R2. rewrite R1,R2. f_equal. ring. }
 rewrite !Cmod_mult, !Cmod_pow, <- E in E'.
 apply Rmult_eq_reg_l in E'.
 2:{ apply pow_nonzero. intro C. apply Cmod_eq_0 in C.
     apply (root_nz q). rewrite ThePoly_root_carac. now subst r1. }
 assert (E2 : ((Cmod r1)^2 = (Cmod r2)^2)%R) by now rewrite E. clear E.
 assert (E3 : (Cmod (r1-1)^2 = Cmod (r2-1)^2)%R) by now rewrite E'. clear E'.
 rewrite !Cmod2_alt in E2,E3.
 unfold Cminus in *. rewrite !re_plus, !im_plus in *.
 replace (Im (-(1))) with 0%R in * by (unfold Im; simpl; lra).
 replace (Re (-(1))) with (-1)%R in * by (unfold Re; simpl; lra).
 lra.
Qed.

Lemma root_equal_Cmod_Im q (r1 r2:C) :
 Root r1 (ThePoly q) -> Root r2 (ThePoly q) ->
 Cmod r1 = Cmod r2 -> Rabs (Im r1) = Rabs (Im r2).
Proof.
 intros R1 R2 E.
 assert (E1 : Re r1 = Re r2). eapply root_equal_Cmod_Re; eauto.
 assert (E2 : ((Cmod r1)^2 = (Cmod r2)^2)%R) by now rewrite E. clear E.
 rewrite !Cmod2_alt, <-E1 in E2.
 apply Rsqr_eq_abs_0. rewrite !Rsqr_pow2. lra.
Qed.

Lemma root_order_Cmod_Re q (r1 r2:C) :
 Root r1 (ThePoly q) -> Root r2 (ThePoly q) ->
 (Cmod r1 < Cmod r2 -> Re r1 < Re r2)%R.
Proof.
 rewrite !ThePoly_root_carac. intros R1 R2 LT.
 assert (q<>O).
 { intros ->. simpl in *. rewrite !Cmult_1_r in *. subst. lra. }
 assert (E : (Cmod (r1^q * (r1 - 1)) = Cmod (r2^q * (r2 -1)))).
 { unfold Rminus, Cminus. rewrite !Cmult_plus_distr_l.
   rewrite (Cmult_comm _ r1), (Cmult_comm _ r2).
   simpl in R1,R2. rewrite R1,R2. f_equal. ring. }
 rewrite !Cmod_mult, !Cmod_pow in E.
 assert (LT' : (Cmod (r2 - 1) < Cmod (r1 - 1))%R).
 { apply Rmult_lt_reg_l with (Cmod r1 ^q)%R.
   - apply pow_lt. apply Cmod_gt_0. intros ->.
     apply (root_nz q). now rewrite ThePoly_root_carac.
   - rewrite E. apply Rmult_lt_compat_r.
     + apply Cmod_gt_0. intros E2. apply Ceq_minus in E2. subst.
       apply (root_non_1 q). now rewrite ThePoly_root_carac.
     + apply pow_lt_compat_l; trivial. split; trivial. apply Cmod_ge_0. }
 assert (LT2 : (Cmod r1^2 < Cmod r2^2)%R).
 { rewrite <- !Rsqr_pow2. apply Rsqr_lt_abs_1.
   rewrite !Rabs_right; trivial; apply Rle_ge, Cmod_ge_0. }
 assert (LT2' : (Cmod (r2-1)^2 < Cmod (r1-1)^2)%R).
 { rewrite <- !Rsqr_pow2. apply Rsqr_lt_abs_1.
   rewrite !Rabs_right; trivial; apply Rle_ge, Cmod_ge_0. }
 rewrite !Cmod2_alt in LT2,LT2'.
 unfold Cminus in *. rewrite !re_plus, !im_plus in *.
 replace (Im (-(1))) with 0%R in * by (unfold Im; simpl; lra).
 replace (Re (-(1))) with (-1)%R in * by (unfold Re; simpl; lra).
 lra.
Qed.

Lemma root_equal_Cmod_Re_iff q (r1 r2:C) :
 Root r1 (ThePoly q) -> Root r2 (ThePoly q) ->
 (Cmod r1 = Cmod r2 <-> Re r1 = Re r2)%R.
Proof.
 intros R1 R2. split; [ apply (root_equal_Cmod_Re q); eauto | intros E ].
 destruct (Rtotal_order (Cmod r1) (Cmod r2)) as [H|[H|H] ]; trivial.
 - apply (root_order_Cmod_Re q) in H; trivial. lra.
 - apply (root_order_Cmod_Re q) in H; trivial. lra.
Qed.

Lemma root_equal_or_conj q (r1 r2:C) :
 Root r1 (ThePoly q) -> Root r2 (ThePoly q) ->
 Re r1 = Re r2 -> r1 = r2 \/ r1 = Cconj r2.
Proof.
 intros R1 R2 E.
 assert (E' : Cmod r1 = Cmod r2).
 { rewrite <- root_equal_Cmod_Re_iff in E; eauto. }
 eapply root_equal_Cmod_Im in E'; eauto.
 clear R1 R2.
 destruct r1 as (x1,y1), r2 as (x2,y2); simpl in *.
 unfold Cconj. simpl. subst x2.
 revert E'.
 destruct (Rle_or_lt 0 y1), (Rle_or_lt 0 y2);
   do 2 ((rewrite Rabs_right by lra) || (rewrite Rabs_left by lra));
   intros; subst; intuition.
 left. f_equal. lra.
Qed.

Lemma root_order_Cmod_Re_iff q (r1 r2:C) :
 Root r1 (ThePoly q) -> Root r2 (ThePoly q) ->
 (Cmod r1 < Cmod r2 <-> Re r1 < Re r2)%R.
Proof.
 intros R1 R2. split; [ apply (root_order_Cmod_Re q); eauto | intros LT ].
 destruct (Rtotal_order (Cmod r1) (Cmod r2)) as [H|[H|H] ]; trivial.
 - apply (root_equal_Cmod_Re q) in H; trivial. lra.
 - apply (root_order_Cmod_Re q) in H; trivial. lra.
Qed.

Lemma roots_ge_nu q (r:C) :
 Nat.Odd q -> Root r (ThePoly q) -> (-nu q <= Cmod r)%R.
Proof.
 intros Q.
 rewrite ThePoly_root_carac. intros E.
 apply Rnot_lt_le. intros L.
 assert (Iv := nu_itvl q Q).
 assert (H : (Cmod (r-1) < 1 - nu q)%R).
 { apply Rle_lt_trans with (1 + Cmod r)%R; try lra.
   eapply Rle_trans; [apply Cmod_triangle|]. rewrite Cmod_opp, Cmod_1. lra. }
 assert (H' : Cmod (r^q) <= (-nu q)^q).
 { rewrite Cmod_pow. apply pow_incr. split; try lra. apply Cmod_ge_0. }
 assert (LT : Cmod (r^q*(r-1)) < (-nu q)^q*(1 - nu q)).
 { rewrite Cmod_mult. apply Rle_lt_mult_compat; split; trivial; try lra.
   - apply Cmod_gt_0. apply Cpow_nonzero. intros ->. apply (root_nz q).
     now rewrite ThePoly_root_carac.
   - apply Cmod_gt_0. intros E'. rewrite <- Ceq_minus in E'. subst.
     apply (root_non_1 q). now rewrite ThePoly_root_carac. }
 revert LT. unfold Cminus. rewrite Cmult_plus_distr_l.
 simpl in E. rewrite Cmult_comm, E.
 replace (_ + _ + _)%C with C1 by lca. rewrite Cmod_1.
 replace (-nu q)%R with ((-1)*nu q)%R by ring.
 rewrite Rpow_mult_distr, minusone_pow_odd by trivial.
 replace (_*_)%R with 1%R. lra.
 ring_simplify. rewrite Rmult_comm, tech_pow_Rmult, nu_carac; trivial. lra.
Qed.

Lemma other_roots_gt_nu q (r:C) :
 Nat.Odd q -> Root r (ThePoly q) -> r <> nu q -> (-nu q < Cmod r)%R.
Proof.
 intros Q R N.
 assert (GE := roots_ge_nu q r Q R).
 apply Rle_lt_or_eq_dec in GE. destruct GE as [GT|E]; trivial.
 destruct N.
 apply ThePoly_root_carac in R.
 assert (E' : (Cmod (r^q * (r - 1)) = nu q^q * (nu q -1))%R).
 { unfold Rminus, Cminus. rewrite Rmult_plus_distr_l, Cmult_plus_distr_l.
   rewrite Rmult_comm, Cmult_comm. simpl in R. rewrite R.
   replace (_ + _)%C with C1 by ring. rewrite Cmod_1.
   generalize (nu_carac q Q); simpl. intros ->. ring. }
 replace (nu q^q*(nu q -1))%R with ((-nu q)^q*(1-nu q))%R in E'.
 2:{ replace (-nu q)%R with ((-1)*nu q)%R by ring.
     rewrite Rpow_mult_distr, minusone_pow_odd; trivial; ring. }
 rewrite Cmod_mult, Cmod_pow, <- E in E'.
 apply Rmult_eq_reg_l in E'.
 2:{ apply pow_nonzero. generalize (nu_itvl q Q); lra. }
 unfold Rminus in E'. rewrite E in E'.
 assert (1-r = Cmod (1-r)).
 { apply Cmod_triangle_exact.
   replace (1-r-1)%C with (-r)%C  by ring.
   replace (1-r)%C with (-(r-1))%C by ring. rewrite !Cmod_opp. lra. }
 replace (1-r)%C with (-(r-1))%C in H at 2 by ring. rewrite Cmod_opp in H.
 rewrite E', <-E in H. rewrite RtoC_plus, RtoC_opp in H.
 replace r with (1-(1-r))%C by ring. rewrite H. ring.
Qed.

(** Enumeration of roots, in lexicographic decreasing order *)

Definition SortedRoots q l := ThePoly q ≅ linfactors l /\ Csorted l.

Lemma SortedRoots_exists q : exists l, SortedRoots q l.
Proof.
 destruct (ThePoly_separated_roots q) as (l & _ & ND & E).
 destruct (Csorted_exists l ND) as (l' & P & L').
 exists l'. split; trivial. rewrite E. now apply linfactors_perm.
Qed.

Lemma SortedRoots_roots q l :
  SortedRoots q l -> forall r, In r l <-> Root r (ThePoly q).
Proof.
 intros (E,_) r. rewrite E. apply linfactors_roots.
Qed.

Lemma SortedRoots_length q l : SortedRoots q l -> length l = S q.
Proof.
 intros (E,_). rewrite <- linfactors_degree, <- E. apply ThePoly_deg.
Qed.

Lemma SortedRoots_nodup q l : SortedRoots q l -> NoDup l.
Proof.
 intros L. apply Csorted_nodup, L.
Qed.

Lemma SortedRoots_unique q l l' :
  SortedRoots q l -> SortedRoots q l' -> l = l'.
Proof.
 intros L L'.
 apply Csorted_unique. apply L. apply L'.
 apply NoDup_Permutation_bis.
 - eapply SortedRoots_nodup; eauto.
 - erewrite !SortedRoots_length; eauto.
 - intro. erewrite !SortedRoots_roots; eauto.
Qed.

Local Instance Clt_order : RelationClasses.StrictOrder Clt := Clt_order.

Lemma StronglySorted_nth : forall (R : C -> C -> Prop) l,
 Sorted.StronglySorted R l <->
 (forall n m : nat, (n < m < length l)%nat -> R (l@n) (l@m)).
Proof.
 exact StronglySorted_nth.
Qed.

Lemma SortedRoots_mu q l : SortedRoots q l -> l@0 = mu q.
Proof.
 intros SR.
 assert (H : length l = S q) by apply (SortedRoots_length _ _ SR).
 destruct l as [|r l]; try easy. clear H.
 simpl.
 destruct (Ceq_dec r (mu q)) as [ |N]; [trivial|exfalso].
 assert (M : In (RtoC (mu q)) (r::l))
  by apply (SortedRoots_roots _ _ SR), mu_is_root.
 simpl in M. destruct M as [M|M]; try easy.
 assert (R : Root r (ThePoly q))
   by (apply (SortedRoots_roots _ _ SR); now left).
 assert (LT : Cmod r < mu q) by (apply other_roots_lt_mu; trivial).
 replace (mu q) with (Cmod (mu q)) in LT.
 2:{ rewrite Cmod_R. apply Rabs_right. generalize (mu_itvl q). lra. }
 eapply root_order_Cmod_Re in LT; eauto. 2:apply mu_is_root.
 destruct SR as (E,SC). rewrite Csorted_alt in SC. inversion_clear SC.
 rewrite Forall_forall in H0. specialize (H0 _ M). do 2 red in H0.
 assert (Clt r r). { transitivity (RtoC (mu q)); trivial. now left. }
 revert H1. apply Clt_order.
Qed.

Lemma SortedRoots_nu q l : Nat.Odd q -> SortedRoots q l -> l@q = nu q.
Proof.
 intros Q SR.
 assert (H : length l = S q) by apply (SortedRoots_length _ _ SR).
 replace q with (length l - 1)%nat at 1 by lia.
 unfold Cnth. rewrite <- rev_nth by lia.
 assert (RO := SortedRoots_roots _ _ SR).
 destruct SR as (_,CS). rewrite Csorted_rev in CS.
 rewrite <- rev_length in H.
 setoid_rewrite In_rev in RO.
 destruct (rev l) as [|r l']; simpl in H; try lia; clear H. simpl.
 destruct (Ceq_dec r (nu q)) as [ |N]; [trivial|exfalso].
 assert (R : Root r (ThePoly q)) by (apply RO; now left).
 assert (NU : In (RtoC (nu q)) (r::l')).
 { apply RO, ThePoly_root_carac.
   now rewrite !RtoC_pow, <- RtoC_plus, nu_carac. }
 simpl in NU. destruct NU as [NU|NU]; try easy.
 apply other_roots_gt_nu in R; trivial.
 rewrite <- Rabs_left in R by (generalize (nu_itvl q Q); lra).
 rewrite <- Cmod_R in R.
 apply (root_order_Cmod_Re q) in R.
 2:{ apply RO. now right. }
 2:{ apply RO. now left. }
 apply Sorted.Sorted_StronglySorted in CS; try apply Clt_order.
 inversion_clear CS.
 rewrite Forall_forall in H0. specialize (H0 _ NU).
 assert (Clt r r). { transitivity (RtoC (nu q)); trivial. now left. }
 revert H1. apply Clt_order.
Qed.

Lemma root_conj q c : Root c (ThePoly q) -> Root (Cconj c) (ThePoly q).
Proof.
 rewrite !ThePoly_root_carac. intros E.
 now rewrite <- !Cpow_conj, E, Cconj_plus_distr, Cconj_R.
Qed.

Lemma root_img q c :
  Root c (ThePoly q) -> c<>mu q -> c<>nu q -> Im c <> 0%R.
Proof.
 intros R M N E.
 destruct c as (x,y). simpl in *. subst. change (x,0%R) with (RtoC x) in *.
 rewrite ThePoly_root_carac in R. rewrite !RtoC_pow,<-RtoC_plus in R.
 apply RtoC_inj in R.
 destruct (Nat.Even_or_Odd q) as [E|O].
 - apply M. f_equal. apply mu_unique_even; trivial. now rewrite P_root_equiv.
 - destruct (mu_or_nu q x O); trivial; subst; now rewrite ?P_root_equiv.
Qed.

Lemma root_non_qSq (q:nat) : ~ Root (q/S q) (ThePoly q).
Proof.
 intros R.
 apply root_img in R.
 - rewrite <- RtoC_div, im_RtoC in R. now apply R.
 - assert (H := mu_itvl q). intros E.
   rewrite <- RtoC_div in E. apply RtoC_inj in E.
   assert (mu q < 1).
   { rewrite <- E. rewrite <- Rcomplements.Rdiv_lt_1.
     rewrite S_INR. lra. apply RSpos. }
   lra.
 - destruct (Nat.Even_Odd_dec q) as [EV|OD] eqn:E.
   + unfold nu. rewrite E. intros EQ. rewrite EQ in R. now apply root_nz in R.
   + assert (H := nu_itvl q OD).
     assert (LE : 0 <= q / S q).
     { apply Rcomplements.Rdiv_le_0_compat. apply pos_INR. apply RSpos. }
     intros EQ. rewrite <- RtoC_div in EQ.
     apply RtoC_inj in EQ. lra.
Qed.

Lemma SortedRoots_next q l :
  SortedRoots q l ->
  forall n, (n+2 <= q)%nat -> Im (l@n) <= 0 ->
    0 < Im (l@(n+1)) /\ l@(n+2) = Cconj (l@(n+1)).
Proof.
 intros SR n N H.
 set (r := l @ (n + 1)).
 assert (length l = S q) by now apply SortedRoots_length.
 assert (SR' := SortedRoots_roots q l SR).
 assert (R : Root r (ThePoly q)). { apply SR', nth_In. lia. }
 assert (IN : In (Cconj r) l). { apply SR'. now apply root_conj. }
 destruct (In_nth l (Cconj r) 0 IN) as (m & M & E'). clear IN.
 change (l@m = r^*) in E'.
 destruct (Rle_or_lt (Im r) 0).
 - exfalso.
   set (r0 := l@n) in *.
   assert (R0' : Root r0 (ThePoly q)). { apply SR', nth_In. lia. }
   assert (Im r <> R0).
   { apply (root_img q); trivial.
     - assert (EM : l@0 = mu q) by now apply (SortedRoots_mu q).
       destruct SR as (E,SC). rewrite Csorted_alt, StronglySorted_nth in SC.
       assert (MM : Cgt (l@0) (l@(n+1))) by (apply SC; lia).
       fold r in MM. rewrite EM in MM. intros ->. revert MM. apply Cgt_order.
     - destruct (Nat.Even_Odd_dec q) as [E|O] eqn:EO.
       + unfold nu. rewrite EO. intros ->. now apply (root_nz q).
       + assert (EN : l@q = nu q) by now apply (SortedRoots_nu q).
         destruct SR as (E,SC). rewrite Csorted_alt, StronglySorted_nth in SC.
         assert (NN : Cgt (l@(n+1)) (l@q)) by (apply SC; lia).
         fold r in NN. rewrite EN in NN. intros ->. revert NN.
         apply Cgt_order. }
   destruct SR as (E,SC). rewrite Csorted_alt, StronglySorted_nth in SC.
   assert (Clt r r0) by (apply SC; lia).
   assert (m <= n+1)%nat.
   { rewrite Nat.le_ngt. intro LT. specialize (SC _ _ (conj LT M)).
     fold r in SC. rewrite E' in SC.
     destruct r as (x,y). repeat red in SC. simpl in *. lra. }
   assert (m <> n+1)%nat.
   { intros ->. fold r in E'. symmetry in E'. apply is_real_carac in E'.
     destruct r as (x,y). simpl in *. lra. }
   assert (m <> n).
   { intros ->. unfold r0 in H. rewrite E' in *.
     destruct r as (x,y). simpl in *. lra. }
   assert (Clt r0 (Cconj r)). { rewrite <- E'. apply SC. lia. }
   destruct (root_equal_or_conj q r0 r) as [-> | ->]; trivial.
   + destruct r as (x,y), r0 as (x0,y0). unfold Clt, Cconj in *. simpl in *.
     lra.
   + destruct r as (x,y). unfold Clt, Cconj in *. simpl in *. lra.
   + revert H7. apply Clt_order.
 - split; trivial. clear H.
   set (r' := l@(n+2)) in *.
   assert (R' : Root r' (ThePoly q)). { apply SR', nth_In. lia. }
   destruct SR as (E,SC). rewrite Csorted_alt, StronglySorted_nth in SC.
   assert (Clt r' r) by (apply SC; lia).
   assert (n+1 <= m)%nat.
   { rewrite Nat.le_ngt. intro LT. specialize (SC m (n+1) lia)%nat.
     fold r in SC. rewrite E' in SC.
     destruct r as (x,y). repeat red in SC. simpl in *. lra. }
   assert (m <> n+1)%nat.
   { intros ->. fold r in E'.
     symmetry in E'. apply is_real_carac in E'. lra. }
   destruct (Nat.eq_dec m (n+2))%nat.
   + unfold r'. rewrite <- E'. now f_equal.
   + assert (Clt (Cconj r) r'). { rewrite <- E'. apply SC. lia. }
     destruct (root_equal_or_conj q r' r) as [-> | ->]; trivial.
     * destruct r as (x,y), r' as (x',y').
       unfold Clt, Cconj in *. simpl in *. lra.
     * destruct r as (x,y). unfold Clt, Cconj in *. simpl in *. lra.
Qed.

Lemma SortedRoots_im_pos q l :
  SortedRoots q l ->
  forall p, (2*p+2<=q)%nat ->
     let r := l@(2*p+1) in
     let r' := l@(2*p+2) in
     0 < Im r /\ r' = Cconj r.
Proof.
 induction p; intros Hp.
 - simpl in Hp. simpl.
   apply (SortedRoots_next q l H 0); simpl; try lia.
   rewrite (SortedRoots_mu q), im_RtoC; trivial. lra.
 - apply (SortedRoots_next q l H); try lia.
   destruct IHp as (LT,E); try lia.
   replace (2*p+2)%nat with (2*S p)%nat in E by lia. rewrite E.
   rewrite im_conj. lra.
Qed.

Lemma SortedRoots_Re_sorted q l :
  SortedRoots q l ->
  Sorted.StronglySorted (fun c c' => Re c >= Re c') l.
Proof.
 intros SR.
 apply StronglySorted_nth. intros n m H.
 assert (SR' := SortedRoots_roots q l SR).
 set (r := l@n).
 set (r' := l@m).
 assert (R : Root r (ThePoly q)). { apply SR', nth_In. lia. }
 assert (R' : Root r' (ThePoly q)). { apply SR', nth_In. lia. }
 destruct SR as (E,SC). rewrite Csorted_alt, StronglySorted_nth in SC.
 assert (LT : Clt r' r) by (apply SC; lia).
 destruct LT; lra.
Qed.

Lemma SortedRoots_Cmod_sorted q l :
  SortedRoots q l ->
  Sorted.StronglySorted (fun c c' => Cmod c >= Cmod c') l.
Proof.
 intros SR.
 apply StronglySorted_nth. intros n m H.
 assert (SR' := SortedRoots_roots q l SR).
 set (r := l@n).
 set (r' := l@m).
 assert (R : Root r (ThePoly q)). { apply SR', nth_In. lia. }
 assert (R' : Root r' (ThePoly q)). { apply SR', nth_In. lia. }
 destruct SR as (E,SC). rewrite Csorted_alt, StronglySorted_nth in SC.
 assert (LT : Clt r' r) by (apply SC; lia).
 destruct LT as [LT|(EQ,LT)].
 - rewrite <- root_order_Cmod_Re_iff in LT; eauto. lra.
 - rewrite <- root_equal_Cmod_Re_iff in EQ; eauto. lra.
Qed.

Lemma second_best_root q l :
  (3 <= q)%nat ->
  SortedRoots q l ->
  l@2 = Cconj (l@1) /\ Cmod (l@3) < Cmod (l@1) /\
  forall n, (3<=n<=q)%nat -> Cmod (l@n) <= Cmod (l@3).
Proof.
 intros Q SR. split.
 { apply (SortedRoots_im_pos q l SR 0 lia). }
 assert (SR' := SortedRoots_roots q l SR).
 assert (LN := SortedRoots_length q l SR).
 assert (Cmod (l@3) < Cmod (l@1)).
 { set (r := l@1). set (r' := l@3).
   assert (R : Root r (ThePoly q)). { apply SR', nth_In. lia. }
   assert (R' : Root r' (ThePoly q)). { apply SR', nth_In. lia. }
   destruct (SortedRoots_im_pos q l SR 0) as (IM,E); try lia.
   simpl in IM, E. fold r in IM, E.
   destruct SR as (_,SC). rewrite Csorted_alt, StronglySorted_nth in SC.
   assert (LT : Clt r' r) by (apply SC; lia).
   destruct LT as [LT|(EQ,LT)].
   - rewrite <- root_order_Cmod_Re_iff in LT; eauto.
   - exfalso. eapply root_equal_or_conj in EQ; eauto.
     destruct EQ as [-> |EQ]; try lra.
     specialize (SC 2%nat 3%nat lia).
     fold r' in SC. rewrite E, <- EQ in SC.
     revert SC. apply Cgt_order. }
 split; trivial.
 intros n N.
 apply SortedRoots_Cmod_sorted in SR. rewrite StronglySorted_nth in SR.
 destruct (Nat.eq_dec n 3) as [->|Hn]. apply Rle_refl. apply Rge_le, SR. lia.
Qed.

(** B : Variant of the sequence A, with different initial values,
    and hence shifted. *)

Fixpoint B (q n : nat) :=
  match n with
  | 0 => 1-q
  | S n => B q n + B q (n-q) + if S n =? q then 1 else 0
  end%nat.

Lemma B_zero q n : (n < q)%nat -> B q n = 0%nat.
Proof.
 induction n as [ [|n] IH] using lt_wf_ind.
 - now destruct q.
 - intros H. simpl. rewrite !IH by lia.
   destruct q. easy. case Nat.eqb_spec; lia.
Qed.

Lemma B_one q n : (q <= n <= 2*q)%nat -> B q n = 1%nat.
Proof.
 induction n as [ [|n] IH] using lt_wf_ind; intros H.
 - now replace q with 0%nat by lia.
 - simpl.
   destruct (Nat.le_gt_cases q n).
   + rewrite IH by lia.
     rewrite B_zero by lia.
     destruct q. easy. case Nat.eqb_spec; lia.
   + rewrite !B_zero by lia.
     destruct q. lia. case Nat.eqb_spec; lia.
Qed.

Lemma A_B q n : A q n = B q (n+2*q).
Proof.
 induction n as [ [|n] IH] using lt_wf_ind.
 - rewrite B_one; simpl; trivial. lia.
 - cbn -["=?"]. rewrite !IH by lia.
   case Nat.eqb_spec; try lia. intros _. rewrite Nat.add_0_r. f_equal.
   destruct (Nat.lt_ge_cases n q).
   + rewrite !B_one; lia.
   + f_equal. lia.
Qed.

(** Some more properties of parity, multdiffs, big_sum, etc *)

Lemma parity_pow n : parity n = (-1)^n.
Proof.
 induction n; rewrite ?parity_S, ?IHn; simpl; ring.
Qed.

Lemma parity_even n : parity (2*n) = 1.
Proof.
 induction n. easy.
 replace (2 * S n)%nat with (S (S (2 * n)))%nat by lia.
 rewrite !parity_S, IHn. ring.
Qed.

Lemma multdiffs_nodup (l : list C) : NoDup l -> multdiffs l <> 0.
Proof.
 induction 1; simpl.
 - apply C1_neq_C0.
 - intros E. apply Cmult_integral in E. destruct E as [E|E]; try easy.
   apply Gbigmult_0 in E. rewrite in_map_iff in E.
   destruct E as (y & E & IN). apply H. apply Ceq_minus in E. now subst.
Qed.

Lemma multdiffs_eqn c l :
 multdiffs (c :: l) =
 G_big_mult (map (fun y => c-y) l) * multdiffs l * parity (length l).
Proof.
 simpl. rewrite <- Cmult_assoc, (Cmult_comm (multdiffs l)), Cmult_assoc.
 f_equal. rewrite parity_pow.
 set (f := fun y => c-y). rewrite <- (map_length f l).
 rewrite <- Gbigmult_factor_r, map_map. f_equal. apply map_ext.
 intro a. unfold f. ring.
Qed.

Lemma multdiffs_insert_at c l i :
 (i <= length l)%nat ->
 multdiffs (insert_at i c l) = multdiffs (c :: l) * parity i.
Proof.
 revert i. induction l; destruct i; cbn -[parity]; intros.
 - simpl. ring.
 - lia.
 - simpl. ring.
 - rewrite parity_S. rewrite IHl by lia. simpl.
   erewrite Gbigmult_perm.
   2:apply Permutation_map, insert_at_perm. simpl. ring.
Qed.

Lemma multdiffs_insert_at' c l i :
 (i <= length l)%nat ->
 G_big_mult (map (fun y => c-y) l) * multdiffs l
 = multdiffs (insert_at i c l) * parity (i + length l).
Proof.
 intros. rewrite multdiffs_insert_at, multdiffs_eqn by trivial.
 rewrite <- !Cmult_assoc. rewrite <- (Cmult_1_r (multdiffs l)) at 1.
 f_equal. f_equal. rewrite !parity_pow, <- !Cpow_add_r, <-parity_pow.
 replace (length l + _)%nat with (2*(length l + i))%nat by lia.
 now rewrite parity_even.
Qed.

Lemma Re_Σ f n : Re (big_sum f n) = big_sum (fun i => Re (f i)) n.
Proof.
 induction n; cbn; trivial. now f_equal.
Qed.

Lemma is_lim_seq_Σ_0 (f:nat -> nat -> R) n :
 (forall i, (i<n)%nat -> is_lim_seq (fun q => f q i) R0) ->
 is_lim_seq (fun q => big_sum (f q) n) R0.
Proof.
 intros H. induction n; simpl.
 - apply is_lim_seq_const.
 - replace R0 with (0+0)%R by lra. apply is_lim_seq_plus'; auto.
Qed.

(** pows : n-th powers of the elements of a list *)

Definition pows (l:list C) n := map (fun c => c^n) l.

Lemma nth_pows i l p : (i < length l)%nat -> (pows l p)@i = (l@i)^p.
Proof.
 intros H. unfold Cnth.
 rewrite <- map_nth with (f := fun c => c ^ p).
 apply nth_indep. unfold pows; rewrite map_length; lia.
Qed.

Lemma big_sum_kronecker f n m :
 (m < n)%nat ->
 (forall i, (i < n)%nat -> i<>m -> f i = 0) ->
 big_sum f n = f m.
Proof.
 revert m.
 induction n.
 - lia.
 - intros m M F. rewrite <- big_sum_extend_r. simpl.
   destruct (Nat.eq_dec n m) as [<-|M'].
   + rewrite big_sum_0_bounded. lca. intros i Hi. apply F; lia.
   + rewrite F, Cplus_0_r by lia. apply IHn; try lia.
     intros i Hi. apply F; lia.
Qed.

Lemma Peval_Pdiff_linfactors l i :
  NoDup l -> (i < length l)%nat ->
  Peval (Pdiff (linfactors l)) (l@i)
  = G_big_mult (map (fun y => l@i - y) (remove_at i l)).
Proof.
 intros Hl Hi.
 assert (Hl' := remove_at_length l i Hi).
 rewrite <- Peval_linfactors.
 rewrite Pdiff_linfactors, Peval_Plistsum, map_map.
 rewrite Clistsum_map with (d:=O).
 rewrite big_sum_kronecker with (m:=i).
 - now rewrite seq_nth.
 - now rewrite seq_length.
 - intros j Hj Hij. rewrite seq_length in Hj.
   rewrite seq_nth by trivial. simpl.
   change (Root (l@i) (linfactors (remove_at j l))).
   rewrite <- linfactors_roots. now apply remove_at_In.
Qed.

Section Roots.
Variable q : nat.
Variable roots : list C.
Hypothesis roots_ok : SortedRoots q roots.

Definition vdmroot := Vandermonde (S q) roots.
Definition vdminv := Minverse vdmroot.
Definition coefs0 : Vector (S q) := transpose (get_row vdminv q).

Lemma VdmRoots_det_nz : Determinant vdmroot <> 0.
Proof.
 assert (len := SortedRoots_length _ _ roots_ok).
 unfold vdmroot.
 rewrite Vandermonde_det; trivial.
 apply multdiffs_nodup. now apply (SortedRoots_nodup q).
Qed.

(** Conjecture (TODO?) : the square of this determinant seems to be
    [+/- ((q+1)^(q+1)+q^q)].
    For instance +5 for q=1, -31 for q=2, -283 for q=3, +3381 for q=4
    See OEIS A056788.
    At least, this square is clearly an integer, since it's a symmetric
    polynomial of the roots (determinant is alternating) with coefficients
    in Z, hence it is a Z polynomial of the elementary symmetric polynomials
    that here are -1 or 0 or 1 (coefficients of ThePoly). *)

Lemma VdmRoots_invertible : invertible vdmroot.
Proof.
 apply lin_indep_iff_invertible. apply WF_Vandermonde.
 apply lin_indep_det_neq_0. apply WF_Vandermonde.
 red. split; auto. apply VdmRoots_det_nz.
Qed.

Lemma coefs0_LinComb p :
  (p <= q)%nat ->
  scalprod coefs0 (mkvect _ (pows roots p)) = if p =? q then 1 else 0.
Proof.
 assert (len := SortedRoots_length _ _ roots_ok).
 assert (VdmWF : WF_Matrix vdmroot) by apply WF_Vandermonde.
 destruct (Minverse_is_inv vdmroot VdmWF VdmRoots_invertible) as (_ & E).
 fold vdminv in E.
 set (V := (fun i j => if (i =? 0) && (j =? q) then 1 else 0) : Matrix 1 (S q)).
 assert (WF_Matrix V).
 { intros x y. unfold V. do 2 case Nat.eqb_spec; simpl; trivial. lia. }
 assert (E0 : transpose coefs0 = Mmult V vdminv).
 { apply mat_equiv_eq; trivial.
   - unfold coefs0. rewrite transpose_involutive.
     apply WF_get_row, WF_scale, WF_adjugate.
   - apply WF_mult; trivial. apply WF_scale, WF_adjugate.
   - intros i j Hi Hj. unfold coefs0, V, get_row, transpose.
     replace i with 0%nat by lia. simpl.
     unfold Mmult. simpl. rewrite Nat.eqb_refl. simpl.
     rewrite big_sum_0_bounded. lca.
     intros x Hx. case Nat.eqb_spec; try lia. simpl. intros. lca. }
 intros Hp.
 replace (mkvect _ (pows roots p)) with (get_col vdmroot p).
 2:{ apply mat_equiv_eq.
     - apply WF_get_col, WF_Vandermonde.
     - apply WF_mkvect. unfold pows. rewrite map_length.
       now apply SortedRoots_length.
     - intros i j Hi Hj. replace j with O by lia; clear j Hj.
       rewrite mkvect_eqn, nth_pows by lia.
       unfold get_row, vdmroot, Vandermonde, Cnth, transpose. cbn.
       do 2 case Nat.leb_spec; auto; lia. }
 unfold scalprod. rewrite E0.
 rewrite get_col_mult_eq; trivial.
 2:{ apply WF_mult, WF_scale, WF_adjugate; trivial. }
 rewrite Mmult_assoc, E, Mmult_1_r; trivial.
Qed.

Lemma coefs0_LinCombB n :
  scalprod coefs0 (mkvect _ (pows roots n)) = B q n.
Proof.
 induction n as [n IH] using lt_wf_ind.
 destruct (Nat.compare_spec n q).
 - rewrite B_one, coefs0_LinComb by lia. subst. now rewrite Nat.eqb_refl.
 - rewrite B_zero, coefs0_LinComb by lia. case Nat.eqb_spec; trivial. lia.
 - destruct n; try lia. cbn -[scalprod Nat.eqb].
   case Nat.eqb_spec; try lia. intros _. rewrite Nat.add_0_r.
   rewrite plus_INR, RtoC_plus, <- !IH by lia.
   replace (mkvect _ (pows roots (S n))) with
       (mkvect (S q) (pows roots n) .+ mkvect _ (pows roots (n-q))).
   + unfold scalprod. now rewrite Mmult_plus_distr_l.
   + assert (len := SortedRoots_length _ _ roots_ok).
     apply mat_equiv_eq.
     * apply WF_plus; apply WF_mkvect; unfold pows; rewrite map_length; lia.
     * apply WF_mkvect; unfold pows; rewrite map_length; lia.
     * intros i j Hi Hj. replace j with O by lia.
       unfold Mplus. rewrite !mkvect_eqn, !nth_pows by lia.
       set (r := roots@i).
       assert (R : Root r (ThePoly q)).
       { apply (SortedRoots_roots _ _ roots_ok). apply nth_In; lia. }
       rewrite ThePoly_root_carac in R.
       replace n with (q + (n-q))%nat at 1 3 by lia.
       rewrite <- Nat.add_succ_l, !Cpow_add_r, R. lca.
Qed.

Lemma coefs0_eqn i :
 (i < S q)%nat ->
 let c := roots@i in
 let l := remove_at i roots in
 coefs0 i O * G_big_mult (map (fun y => c-y) l) = 1.
Proof.
 intros Hi c l.
 assert (len := SortedRoots_length _ _ roots_ok).
 assert (len' : length l = q). { unfold l; rewrite remove_at_length; lia. }
 unfold coefs0, get_row, transpose. simpl.
 unfold vdminv, Minverse, adjugate, scale.
 do 2 (case Nat.ltb_spec; try lia); intros _ _. cbn -[Determinant].
 unfold vdmroot.
 rewrite get_minor_vandermonde by lia. fold l.
 rewrite !Vandermonde_det by lia.
 rewrite <- (insert_at_remove_at roots i 0) at 1 by lia.
 change (nth i roots 0) with c. fold l.
 rewrite <- !Cmult_assoc, (Cmult_comm (multdiffs l)).
 rewrite (multdiffs_insert_at' c l i), len' by lia. field_simplify.
 - rewrite Nat.add_comm, parity_pow, <- Cpow_mul_l.
   replace (-1*-1) with 1 by ring. apply Cpow_1_l.
 - apply multdiffs_nodup. unfold c, l, Cnth.
   rewrite insert_at_remove_at by lia.
   eapply SortedRoots_nodup; eauto.
Qed.

Definition coefB r := r / r^q /((S q)*r-q).

Lemma coefs0_coefB i : coefs0 i O = coefB (roots@i).
Proof.
 assert (len := SortedRoots_length _ _ roots_ok).
 set (r := roots@i).
 destruct (Nat.eq_dec q 0) as [Q|Q].
 { unfold coefs0, get_row, transpose, vdminv, Minverse. simpl. rewrite Q.
   unfold scale. simpl.
   case Nat.ltb_spec; simpl; intros.
   - unfold vdmroot, Vandermonde. simpl. replace i with O by lia. simpl.
     unfold coefB. rewrite Q. simpl. field. intros EQ.
     apply (root_nz 0). rewrite <- EQ, <- Q.
     rewrite <- (SortedRoots_roots q); eauto. apply nth_In. lia.
   - rewrite Cmult_0_r. unfold coefB. unfold r, Cnth.
     rewrite nth_overflow by lia.
     unfold Cdiv. now rewrite !Cmult_0_l. }
 destruct (Nat.ltb_spec i (S q)).
 - unfold coefB.
   assert (roots_nodup := SortedRoots_nodup _ _ roots_ok).
   assert (roots_len := SortedRoots_length _ _ roots_ok).
   assert (E := Peval_Pdiff_linfactors roots i roots_nodup lia).
   rewrite <- (proj1 roots_ok) in E. fold r in E.
   generalize (coefs0_eqn i H).
   fold r. set (l := remove_at i roots) in *. cbv zeta. rewrite <- E.
   rewrite ThePoly_diff; try lia.
   rewrite Pmult_eval, monom_eval. cbn -[INR coefs0].
   rewrite !Cmult_1_l, !Cmult_1_r, !Cplus_0_l.
   assert (R : r<>0).
   { intros R. apply (root_nz q). rewrite <- R.
     apply (SortedRoots_roots _ _ roots_ok r). apply nth_In. lia. }
   replace (r / r^q) with (/r ^(q-1)).
   2:{ replace q with (S (q-1)) at 2 by lia. rewrite Cpow_S. field.
       split; trivial. now apply Cpow_nonzero. }
   replace (/ r ^ (q - 1) / (S q * r - q)) with (/(r ^(q-1) * ((S q)*r-q))).
   2:{ field. split.
       now apply Cpow_nonzero.
       intros EQ.
       assert (EQ' : r = q / S q).
       { apply Cminus_eq_0 in EQ. rewrite <- EQ at 1. field.
         intros EQ'. apply RtoC_inj in EQ'. revert EQ'. apply RSnz. }
       apply (root_non_qSq q). rewrite <- EQ'.
       rewrite <- SortedRoots_roots; eauto. apply nth_In. lia. }
   intros EQ.
   apply Cinv_eq.
   rewrite <- EQ at 1. f_equal. rewrite Cmult_comm. f_equal.
   unfold Cminus. rewrite Cplus_comm. f_equal. f_equal.
   now rewrite S_INR, RtoC_plus.
 - unfold coefs0, get_row, transpose. simpl.
   unfold vdminv, Minverse, adjugate, scale.
   do 2 (case Nat.ltb_spec; try lia); intros _ Hi.
   cbn -[Determinant]. rewrite Cmult_0_r. unfold coefB, r, Cnth.
   rewrite nth_overflow by lia. unfold Cdiv. now rewrite !Cmult_0_l.
Qed.

Lemma Equation_B n :
  RtoC (B q n) = Clistsum (map (fun r => coefB r * r^n) roots).
Proof.
 assert (len := SortedRoots_length _ _ roots_ok).
 rewrite <- coefs0_LinCombB. rewrite scalprod_alt.
 rewrite Clistsum_map with (d:=0). rewrite len.
 apply big_sum_eq_bounded. intros x Hx.
 rewrite mkvect_eqn, nth_pows, coefs0_coefB; trivial. lia.
Qed.

Definition coefA r := r^(S q) / ((S q)*r-q).

Lemma Equation_A n :
  RtoC (A q n) = Clistsum (map (fun r => coefA r * r^n) roots).
Proof.
 erewrite A_B, Equation_B; eauto. f_equal. apply map_ext_in. intros r R.
 rewrite Cpow_add_r. unfold coefB, coefA.
 unfold Cdiv.
 rewrite !(Cmult_comm (_*/(_-_))), !Cmult_assoc. f_equal.
 replace (2*q)%nat with (q+q)%nat by lia. rewrite Cpow_add_r, Cpow_S.
 field. apply Cpow_nonzero. eapply SortedRoots_roots in R; eauto.
 intros ->. now apply root_nz in R.
Qed.

Definition coefdA r := coefA r * (/r - tau q).

Lemma coefdA_mu : coefdA (mu q) = 0.
Proof.
 unfold coefdA, tau. rewrite RtoC_inv. ring.
Qed.

Lemma coefdA_sum : q<>O -> Clistsum (map coefdA roots) = 1-tau q.
Proof.
 intros Q.
 rewrite map_ext with (g := fun r => coefA r * /r - tau q * coefA r).
 2:{ intros a. unfold coefdA. ring. }
 rewrite <- Clistsum_minus. f_equal.
 - rewrite map_ext_in with (g := fun x => coefB x * x ^ (2*q-1)).
   + rewrite <- Equation_B. rewrite B_one. lca. lia.
   + intros r R. unfold coefA, coefB.
     replace (2*q-1)%nat with (q-1+q)%nat by lia. rewrite Cpow_add_r.
     replace (S q) with (S (S (q-1))) at 1 by lia. rewrite !Cpow_S. field.
     assert (r<>0).
     { eapply SortedRoots_roots in R; eauto. intros ->.
       now apply root_nz in R. }
     split. now apply Cpow_nonzero. split; trivial.
     intros E. apply Cminus_eq_0 in E.
     assert (RtoC (S q) <> 0)%C.
     { intros EQ. apply RtoC_inj in EQ. now apply RSnz in EQ. }
     eapply SortedRoots_roots in R; eauto.
     replace r with (q/S q) in R.
     2:{ apply Cmult_eq_reg_l with (RtoC (S q)); trivial.
         rewrite E. now field. }
     now apply root_non_qSq in R.
 - rewrite map_ext with
     (g := Basics.compose (Cmult (tau q)) (fun x => coefA x * x^0)).
   2:{ intros. unfold Basics.compose. simpl. lca. }
   rewrite <- map_map with (g:=Cmult (tau q)) (f:=fun x => coefA x * x^0).
   rewrite <- Clistsum_factor_l. rewrite <- Equation_A. simpl. lca.
Qed.

Lemma Equation_dA n :
  q<>O ->
  RtoC (A q (n-1) - tau q * A q n) =
  Clistsum (map (fun r => coefdA r * r^n) (tl roots)).
Proof.
 intros Q.
 assert (E : roots = RtoC (mu q) :: tl roots).
 { assert (len := SortedRoots_length _ _ roots_ok).
   destruct roots; simpl in *; try easy. f_equal.
   now apply SortedRoots_mu in roots_ok. }
 destruct (Nat.eq_dec n 0) as [->|N].
 - simpl. rewrite Rmult_1_r, RtoC_minus, <- coefdA_sum; trivial.
   rewrite E at 1. simpl. rewrite coefdA_mu, Cplus_0_l.
   f_equal. apply map_ext. intros. lca.
 - rewrite RtoC_minus, RtoC_mult, !Equation_A.
   rewrite Clistsum_factor_l, map_map, Clistsum_minus.
   rewrite E at 1. simpl.
   replace n with (S (n-1)) at 2 by lia. simpl.
   unfold tau at 1.
   assert (mu q <> R0) by (generalize (mu_itvl q); lra).
   rewrite RtoC_inv.
   field_simplify. 2:{ intro E'. apply RtoC_inj in E'. lra. }
   f_equal. apply map_ext_in. intros r R. unfold coefdA.
   replace n with (S (n-1)) at 2 3 by lia. simpl.
   field. intros ->. apply (root_nz q).
   rewrite <- (SortedRoots_roots q roots roots_ok).
   destruct roots; simpl in *; try easy. now right.
Qed.

Lemma sumA_Rlistsum l :
  INR (sumA q l) = Rlistsum (map (fun n => INR (A q n)) l).
Proof.
 induction l; simpl; trivial.
 now rewrite plus_INR, IHl.
Qed.

Lemma Equation_delta n :
 q<>O ->
 RtoC (f q n - tau q * n) =
 Clistsum (map (fun m =>
   Clistsum (map (fun r => coefdA r * r^m) (tl roots)))
  (decomp q n)).
Proof.
 intros Q.
 rewrite f_decomp. rewrite <- (decomp_sum q n) at 2.
 set (l := decomp q n).
 rewrite RtoC_minus, RtoC_mult, !sumA_Rlistsum, !RtoC_Rlistsum, !map_map.
 rewrite Clistsum_factor_l, map_map, Clistsum_minus.
 f_equal. apply map_ext. intros m. replace (pred m) with (m-1)%nat by lia.
 rewrite <- Equation_dA; trivial. now rewrite RtoC_minus, RtoC_mult.
Qed.

Lemma Equation_delta' n :
 q<>O ->
 RtoC (f q n - tau q * n) =
 Clistsum (map (fun r => coefdA r * Clistsum (map (Cpow r) (decomp q n)))
               (tl roots)).
Proof.
 intros Q.
 rewrite Equation_delta; trivial.
 rewrite Clistsum_Clistsum. f_equal. apply map_ext.
 intros a. now rewrite Clistsum_factor_l, map_map.
Qed.

End Roots.

Lemma coefB_nz q r : Root r (ThePoly q) -> coefB q r <> 0.
Proof.
 unfold coefB. intros R. unfold Cdiv. intros E.
 rewrite <- Cmult_assoc in E. apply Cmult_integral in E.
 destruct E as [->|E]. now apply root_nz in R.
 apply Cmult_integral in E. destruct E as [E|E].
 - apply C1_neq_C0.
   rewrite <- (Cinv_l (r^q)), E. lca. apply Cpow_nonzero. intros ->.
   now apply root_nz in R.
 - apply C1_neq_C0.
   rewrite <- (Cinv_l ((S q)*r-q)), E. lca.
   intros E'. apply Cminus_eq_0 in E'.
   assert (RtoC (S q) <> 0)%C.
   { intros EQ. apply RtoC_inj in EQ. now apply RSnz in EQ. }
   replace r with (q/S q) in R.
   2:{ apply Cmult_eq_reg_l with (RtoC (S q)); trivial.
       rewrite E'. now field. }
   now apply root_non_qSq in R.
Qed.

Lemma coefA_nz q r : Root r (ThePoly q) -> coefA q r <> 0.
Proof.
 intros R.
 unfold coefA. replace (r^S q)%C with (r^(2*q)*r/r^q).
 2:{ replace (2*q)%nat with (q+q)%nat by lia.
     rewrite Cpow_add. simpl. field. apply Cpow_nonzero.
     intros ->. now apply root_nz in R. }
 unfold Cdiv. rewrite <- !Cmult_assoc, (Cmult_assoc r).
 change (r^(2*q)*coefB q r <> 0). intros E. apply Cmult_integral in E.
 destruct E as [E|E].
 - apply Cpow_nonzero in E; trivial. intros ->. now apply root_nz in R.
 - revert E. now apply coefB_nz.
Qed.

Lemma coefdA_nz q r : Root r (ThePoly q) -> r <> mu q -> coefdA q r <> 0.
Proof.
 intros R R'. unfold coefdA. intros E. apply Cmult_integral in E.
 destruct E as [E|E]. apply (coefA_nz q r R E).
 apply Cminus_eq_0 in E. apply R'.
 now rewrite tau_inv, RtoC_inv, <- E, Cinv_inv.
Qed.

Definition coef_mu q : R := (mu q ^(S q) / ((S q)*mu q -q))%R.

Lemma coef_mu_ok q : RtoC (coef_mu q) = coefA q (mu q).
Proof.
 unfold coef_mu, coefA.
 now rewrite !RtoC_pow, <- RtoC_mult, <- RtoC_minus, <- RtoC_div.
Qed.

Lemma A_div_pow_mu_limit q :
 is_lim_seq (fun n => A q n / mu q ^n)%R (coef_mu q).
Proof.
 destruct (SortedRoots_exists q) as (roots & roots_ok).
 assert (E := Equation_A q roots roots_ok).
 assert (roots_mu : roots@0 = mu q) by now apply SortedRoots_mu.
 assert (roots_len : length roots = S q) by now apply SortedRoots_length.
 assert (mu12 := mu_itvl q).
 set (root := fun i => roots@i).
 set (coef := fun i => coefA q (root i)).
 assert (E' : forall n, big_sum (fun i => coef i * root i ^n) (S q) = A q n).
 { intros n. now rewrite E, Clistsum_map with (d:=0), roots_len. }
 clear E.
 set (rest := (fun n i => Re (coef (S i) * (root (S i))^n) / mu q^n)%R).
 apply is_lim_seq_ext with (u := (fun n => coef_mu q + big_sum (rest n) q)%R).
 - intros n.
   rewrite <- (re_RtoC (A q n)). rewrite <- E'. clear E'.
   rewrite big_sum_shift.
   rewrite re_plus, Re_Σ, Rdiv_plus_distr.
   unfold Rdiv. rewrite (@big_sum_mult_r _ _ _ _ R_is_ring).
   f_equal. unfold coef, root. rewrite roots_mu, <- coef_mu_ok.
   rewrite RtoC_pow, <- RtoC_mult, re_RtoC. field. apply pow_nonzero. lra.
 - clear E'.
   rewrite <- (Rplus_0_r (coef_mu q)) at 1.
   apply is_lim_seq_plus'; [apply is_lim_seq_const|].
   apply is_lim_seq_Σ_0. intros i Hi.
   apply is_lim_seq_0_abs with
     (fun n => Cmod (coef (S i)) * (Cmod (root (S i)) / mu q)^n)%R.
   + intros n. unfold rest. clear rest.
     unfold Rdiv. rewrite <- re_scal_r.
     eapply Rle_trans; [apply re_le_Cmod|].
     rewrite <- Cmult_assoc, Cmod_mult.
     apply Rmult_le_compat_l. apply Cmod_ge_0.
     rewrite Cmod_mult.
     rewrite Rpow_mult_distr.
     rewrite <- Cmod_pow.
     apply Rmult_le_compat_l. apply Cmod_ge_0.
     rewrite Cmod_R. rewrite Rabs_right. rewrite pow_inv; lra.
     left. apply Rinv_0_lt_compat. apply pow_lt; lra.
   + clear rest.
     set (c := Cmod _).
     replace 0%R with (c * 0)%R at 1 by lra.
     apply is_lim_seq_mult'; [apply is_lim_seq_const|].
     apply is_lim_seq_geom.
     rewrite Rabs_right.
     2:{ apply Rle_ge, Rcomplements.Rdiv_le_0_compat. apply Cmod_ge_0. lra. }
     apply -> Rcomplements.Rdiv_lt_1; try lra.
     apply other_roots_lt_mu.
     * apply (SortedRoots_roots _ _ roots_ok). apply nth_In; lia.
     * rewrite <- roots_mu. intros E.
       apply NoDup_nth in E; try lia. now apply (SortedRoots_nodup q).
Qed.

(* Print Assumptions A_div_pow_mu_limit. *)

Lemma coefA_conj q r :
  coefA q (Cconj r) = Cconj (coefA q r).
Proof.
 unfold coefA.
 rewrite Cdiv_conj, Cpow_conj, Cconj_minus_distr, Cconj_mult_distr, !Cconj_R.
 easy.
Qed.

Lemma coefdA_conj q r :
  coefdA q (Cconj r) = Cconj (coefdA q r).
Proof.
 unfold coefdA. rewrite coefA_conj.
 now rewrite Cconj_mult_distr, Cconj_minus_distr, Cinv_conj, Cconj_R.
Qed.

Lemma dA_expo q roots : (3<=q)%nat -> SortedRoots q roots ->
 let r := roots@1 in
 exists c : posreal,
 forall N, exists n, (N<=n)%nat /\
    c * (Cmod r)^n < Rabs (A q (n-1) - tau q * A q n).
Proof.
 intros Q roots_ok r.
 assert (len := SortedRoots_length _ _ roots_ok).
 destruct (second_best_root q _ lia roots_ok) as (E & LT & LE).
 fold r in E, LT.
 assert (R : Root r (ThePoly q)).
 { eapply SortedRoots_roots; eauto. apply nth_In. lia. }
 assert (R0 : r <> 0). { intros ->. now apply root_nz in R. }
 set (d := coefdA q r).
 assert (Hd : d<>0).
 { apply coefdA_nz; trivial.
   rewrite <- (SortedRoots_mu q _ roots_ok). intros EQ.
   apply NoDup_nth in EQ; try lia. eapply SortedRoots_nodup; eauto. }
 set (c_rest := Rlistsum (map (fun r => Cmod (coefdA q r)) (skipn 3 roots))).
 set (theta := Polar.get_arg r).
 set (rho := Polar.get_arg d).
 destruct (affine_cos_apart_zero theta rho) as [c_r Cr].
 { destruct (SortedRoots_im_pos _ _ roots_ok 0) as (IM & _); try lia.
   simpl in IM. fold r in IM. rewrite <- (polar_eqn r) in IM.
   fold theta in IM. rewrite im_scal_l in IM.
   unfold Im, Cexp in IM. simpl in IM. nra. }
 set (c := (c_r * Cmod d)%R).
 assert (Hc : 0 < c).
 { unfold c. apply Rmult_lt_0_compat.
   - now destruct c_r.
   - apply Cmod_gt_0; trivial. }
 exists (mkposreal c Hc). intros N. simpl.
 set (r' := roots@3) in *.
 set (ratio := (Cmod r' / Cmod r)%R).
 assert (R' : Root r' (ThePoly q)).
 { eapply SortedRoots_roots; eauto. apply nth_In. lia. }
 assert (R0' : r' <> 0). { intros ->. now apply root_nz in R'. }
 assert (Hratio : (0 < ratio < 1)%R).
 { unfold ratio. split.
   - apply Rdiv_lt_0_compat; apply Cmod_gt_0; trivial.
   - rewrite <- Rcomplements.Rdiv_lt_1; trivial. apply Cmod_gt_0; trivial. }
 assert (Hrest : 0 < c_rest).
 { unfold c_rest.
   replace (skipn 3 roots) with (r' :: skipn 4 roots).
   2:{ now do 4 (destruct roots as [|? roots]; unfold Cnth in *;
                 simpl in *; try lia). }
   cbn - [skipn]. change (fold_right Rplus _) with Rlistsum.
   rewrite <- map_map with (g := Cmod) (f:=coefdA q).
   apply Rlt_le_trans
    with (Cmod (coefdA q r') + Cmod (Clistsum (map (coefdA q) (skipn 4 roots))))%R.
   - apply Rplus_lt_le_0_compat; [ | apply Cmod_ge_0].
     apply Cmod_gt_0. apply coefdA_nz; trivial.
     rewrite <- (SortedRoots_mu q _ roots_ok). intros EQ.
     apply NoDup_nth in EQ; try lia. eapply SortedRoots_nodup; eauto.
   - apply Rplus_le_compat_l. apply Clistsum_mod. }
 destruct (large_enough_exponent' ratio (c/c_rest)) as (N' & HN'); trivial.
 { apply Rdiv_lt_0_compat; trivial. }
 destruct (Cr (max N N')) as (n & Hn & LTn).
 exists n. split; try lia.
 rewrite <- Cmod_R, (Equation_dA q _ roots_ok); trivial; try lia.
 assert (roots_eq : roots = roots@0 :: r :: Cconj r :: skipn 3 roots).
 { rewrite <- E.
   now do 3 (destruct roots; unfold Cnth in *; simpl in *; try lia). }
 rewrite roots_eq. clear Cr E.
 set (f := fun r => _).
 cbn -[skipn]. change (fold_right _ _) with Clistsum. unfold f at 1 2.
 rewrite coefdA_conj.
 fold d.
 rewrite <- Cpow_conj, <- Cconj_mult_distr, Cplus_assoc, re_alt'.
 eapply Rlt_le_trans; [|apply Cmod_triangle'].
 rewrite Cmod_mult. rewrite !Cmod_R, Rabs_right by lra.
 rewrite <- (polar_eqn d). fold rho.
 rewrite <- (polar_eqn r) at 2. fold theta. rewrite Cpow_mul_l, Cexp_pow.
 replace (_ * _ * _)
  with (Cmod d * Cmod r ^ n * (Cexp rho * Cexp (theta * n))) by ring.
 rewrite <- Cexp_add.
 rewrite <- Cmult_assoc, RtoC_pow, !re_scal_l, <- Rmult_assoc.
 rewrite !Rabs_mult.
 rewrite 2 Rabs_right by (rewrite <- ?Cmod_pow; apply Rle_ge, Cmod_ge_0).
 unfold Cexp, Re. simpl fst.
 rewrite Rplus_comm.
 apply Rlt_trans with (2 * c * Cmod r ^ n - Cmod (Clistsum (map f (skipn 3 roots))))%R.
 2:{ unfold c. unfold Rminus. apply Rplus_lt_compat_r.
     rewrite !Rmult_assoc, (Rmult_comm c_r), <- !Rmult_assoc.
     apply Rmult_lt_compat_l; trivial.
     rewrite <- Cmod_pow, Rmult_assoc, <- Cmod_mult.
     apply Rmult_lt_0_compat; try lra. apply Cmod_gt_0.
     intros E.
     apply Cmult_integral in E. destruct E as [E|E]. now apply Hd.
     revert E. now apply Cpow_nonzero. }
 clear theta rho LTn.
 assert (Cmod (Clistsum (map f (skipn 3 roots))) < c * Cmod r ^n); try lra.
 eapply Rle_lt_trans; [apply Clistsum_mod|]. rewrite map_map. unfold f.
 eapply Rle_lt_trans; [apply Rlistsum_le
                       with (g:=(fun x => ratio^n * Cmod (coefdA q x * r ^ n))%R)|].
 { intros a Ha. unfold ratio. rewrite !Cmod_mult.
   destruct (In_nth _ _ 0 Ha) as (m & Hm & <-).
   replace (nth m (skipn 3 roots) 0) with (roots@(3+m))
    by now rewrite roots_eq at 1.
   rewrite skipn_length in Hm.
   specialize (LE (3+m)%nat lia).
   set (rm := roots@(3+m)) in *.
   set (dm := coefdA q rm). unfold Rdiv.
   rewrite Rpow_mult_distr, pow_inv, !Cmod_pow. field_simplify.
   2:{ apply pow_nonzero. intros E. now apply Cmod_eq_0 in E. }
   apply Rmult_le_compat_l. apply Cmod_ge_0. apply pow_incr; split; trivial.
   apply Cmod_ge_0. }
 { clearbody c. clear roots_eq f c_r len roots_ok Q LE.
   rewrite map_ext
     with (g:=(fun x => Cmod (coefdA q x) * (ratio^n * Cmod (r^n)))%R).
   2:{ intros a. rewrite Cmod_mult. ring. }
   replace (Rlistsum _) with (c_rest * (ratio ^ n * Cmod (r ^ n)))%R.
   2:{ unfold c_rest. now rewrite Rlistsum_distr, map_map. }
   rewrite Cmod_pow, <- Rmult_assoc. apply Rmult_lt_compat_r.
   - now apply pow_lt, Cmod_gt_0.
   - rewrite Rmult_comm. apply Rcomplements.Rlt_div_r; try lra.
     apply Rle_lt_trans with (ratio ^ N')%R; trivial.
     apply Rle_pow_low. lra. lia. }
Qed.

(* Print Assumptions dA_expo. *)
