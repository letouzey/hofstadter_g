From Coq Require Import Lia Reals Lra Permutation.
From Hofstadter.HalfQuantum Require Import Complex Polynomial.
Require Import MoreTac MoreList MoreReals MoreLim MoreComplex MoreSum.
Require Import MoreSets MorePoly GenFib GenG Mu.
Local Open Scope R.
Local Open Scope C.
Local Open Scope poly_scope.
Local Coercion INR : nat >-> R.
Local Coercion RtoC : R >-> C.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

Definition ThePoly (k:nat) : Polynomial :=
 monom C1 k +, monom (-C1) (k-1) +, [-C1].

Lemma ThePoly_eval k x : Peval (ThePoly k) x = x^k-x^(k-1)-1.
Proof.
 unfold ThePoly. rewrite !Pplus_eval, !monom_eval.
 rewrite Pconst_eval. ring.
Qed.

Lemma ThePoly_root_carac r k : Root r (ThePoly k) <-> r^k = r^(k-1) + 1.
Proof.
 unfold Root. rewrite ThePoly_eval. rewrite (Ceq_minus _ (_+_)).
 unfold Cminus. now rewrite Copp_plus_distr, Cplus_assoc.
Qed.

Lemma ThePoly_0 : ThePoly 0 ≅ [-C1].
Proof.
 unfold ThePoly. simpl. apply eq_Peq. f_equal. lca.
Qed.

Lemma ThePoly_0_NoRoot c : ~Root c (ThePoly 0).
Proof.
 rewrite ThePoly_0. unfold Root, Peval. simpl. intros E. ring_simplify in E.
 injection E; lra.
Qed.

Lemma ThePoly_root_eqn r k : Root r (ThePoly k) -> r^(k-1)*(r-1) = 1.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { intros Hr. now apply ThePoly_0_NoRoot in Hr. }
 { rewrite ThePoly_root_carac. rewrite <- (succ_pred K) at 1.
   simpl. unfold Cminus. rewrite Cmult_plus_distr_l, (Cmult_comm _ r).
   intros ->. ring. }
Qed.

Lemma mu_is_root k : k<>O -> Root (mu k) (ThePoly k).
Proof.
 intros K.
 rewrite ThePoly_root_carac.
 now rewrite !RtoC_pow, mu_carac, !RtoC_plus.
Qed.

Lemma root_nz k : ~ Root 0 (ThePoly k).
Proof.
 rewrite !ThePoly_root_carac.
 destruct k as [|[|k]]; simpl; intros E; ring_simplify in E;
  apply RtoC_inj_neq in E;trivial; lra.
Qed.

Lemma root_non_1 k : ~ Root 1 (ThePoly k).
Proof.
 rewrite !ThePoly_root_carac. rewrite !Cpow_1_l.
 intro E. ring_simplify in E. apply RtoC_inj_neq in E; trivial. lra.
Qed.

Lemma root_non_km1k (k:nat) : ~ Root ((k-1)/k) (ThePoly k).
Proof.
 rewrite <- RtoC_minus, <- RtoC_div.
 set (r := ((k-1)/k)%R).
 rewrite ThePoly_root_carac.
 rewrite !RtoC_pow, <- RtoC_plus. intros [= E].
 assert (K : k<>O). { intros ->. unfold r in E. simpl in *. lra. }
 assert (K1 : k<>1%nat). { intros ->. unfold r in E. simpl in *. lra. }
 set (q := QArith_base.Qmake (Z.of_nat (k-1)) (Pos.of_nat k)).
 replace r with (Q2R q) in E.
 2:{ unfold r, q, Q2R. simpl. unfold Rdiv. repeat f_equal.
     now rewrite <- INR_IZR_INZ, minus_INR by lia.
     unfold IZR. rewrite <- INR_IPR. now rewrite Nat2Pos.id. }
 revert E. apply (root_irrat k q lia).
Qed.

Lemma ThePoly_subdeg q : (degree (monom (-C1) q +, [-C1]) <= q)%nat.
Proof.
 etransitivity; [apply Pplus_degree1| ].
 rewrite monom_degree. 2:apply Copp_neq_0_compat, C1_neq_C0.
 generalize (degree_length [-C1]). simpl. lia.
Qed.

Lemma ThePoly_deg k : degree (ThePoly k) = k.
Proof.
 unfold ThePoly.
 destruct (Nat.eq_dec k 0) as [->|K].
 { simpl. set (l := [_]). generalize (degree_length l). unfold l.
   simpl. lia. }
 rewrite Pplus_assoc, Pplus_comm.
 rewrite Pplus_degree2.
 rewrite monom_degree. lia. apply C1_neq_C0.
 rewrite monom_degree. 2:apply C1_neq_C0.
 generalize (ThePoly_subdeg (k-1)). lia.
Qed.

Lemma ThePoly_monic (k:nat) : k<>O -> monic (ThePoly k).
Proof.
 intros K.
 unfold ThePoly. rewrite Pplus_assoc, Pplus_comm. unfold monic.
 rewrite topcoef_plus_ltdeg. apply topcoef_monom.
 rewrite monom_degree. 2:apply C1_neq_C0.
 generalize (ThePoly_subdeg (k-1)). lia.
Qed.

Lemma ThePoly_diff k : (1<k)%nat ->
 Pdiff (ThePoly k) ≅ [-(k-1); RtoC k] *, monom C1 (k-2).
Proof.
 intros K.
 unfold ThePoly.
 rewrite !Pdiff_plus, !diff_monom.
 replace (pred k) with (S (k-2)) by lia.
 replace (pred (k-1)) with (k-2)%nat by lia.
 simpl Pdiff. rewrite Pzero_alt, Pplus_0_r.
 rewrite monom_S.
 rewrite (monom_scale (-C1)), <- Pmult_assoc.
 replace ([RtoC (k-1)] *, [-C1]) with [-RtoC (k-1)].
 2: simpl; f_equal; lca.
 rewrite <- Pmult_X. rewrite <- Pmult_assoc.
 rewrite (Pmult_comm _ _X_), Pmult_X.
 rewrite <- Pmult_plus_distr_r. simpl Pplus.
 apply Peq_iff. f_equal. f_equal. f_equal. rewrite minus_INR by lia. lca.
Qed.

Lemma ThePoly_diff_expr k r : (1 < k)%nat ->
  Peval (Pdiff (ThePoly k)) r = r^(k-2) * (k*r-(k-1)).
Proof.
 intros. rewrite ThePoly_diff by trivial. rewrite Pmult_eval, monom_eval.
 unfold Peval; simpl. ring.
Qed.

Lemma ThePoly_diff_1 : Pdiff (ThePoly 1) ≅ [C1].
Proof.
 unfold ThePoly. simpl. apply Peq_iff.
 rewrite Cplus_0_r. apply (app_C0_compactify_reduce_1 [C1]).
Qed.

Lemma ThePoly_no_common_root_with_diff k c :
  Root c (ThePoly k) -> ~ Root c (Pdiff (ThePoly k)).
Proof.
 intros Hc.
 destruct (Nat.eq_dec k 0) as [->|K0].
 { now apply ThePoly_0_NoRoot in Hc. }
 destruct (Nat.eq_dec k 1) as [->|K1].
 { rewrite ThePoly_diff_1. unfold Root. cbn. rewrite Cmult_1_l, Cplus_0_l.
   apply C1_neq_C0. }
 unfold Root.
 rewrite ThePoly_diff_expr by lia.
 intro E. apply Cmult_integral in E. destruct E as [E|E].
 - revert E. apply Cpow_nonzero. intros ->. now apply (root_nz k).
 - apply Ceq_minus in E.
   assert (c = (k-1) / k).
   { rewrite <- E. field. intros [= E']. now apply not_INR in K0. }
   subst c. revert Hc. apply root_non_km1k.
Qed.

Lemma ThePoly_separated_roots k :
  k<>O -> exists l, length l = k /\ NoDup l /\ ThePoly k ≅ linfactors l.
Proof.
 intros K.
 destruct (separated_roots (ThePoly k)) as (l & D & E).
 - now apply ThePoly_monic.
 - apply ThePoly_no_common_root_with_diff.
 - exists l; repeat split; auto.
   rewrite <- linfactors_degree. now rewrite <- E, ThePoly_deg.
Qed.

Lemma roots_le_mu k (r:C) :
 Root r (ThePoly k) -> Cmod r <= mu k.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { intros Hr. now apply ThePoly_0_NoRoot in Hr. }
 intros E. apply ThePoly_root_eqn in E.
 apply Rnot_lt_le. intros L.
 assert (Iv := mu_itvl k).
 assert (H : mu k -1 < Cmod (r-1)).
 { apply Rlt_le_trans with (Cmod r -1)%R; try lra.
   apply Rle_minus_l.
   replace r with ((r-C1)+C1) at 1 by lca.
   eapply Rle_trans; [apply Cmod_triangle|]. rewrite Cmod_1. lra. }
 assert (H' : (mu k)^(k-1) <= Cmod (r^(k-1))).
 { rewrite Cmod_pow. apply pow_incr; lra. }
 assert (LT : (mu k)^(k-1)*(mu k -1) < Cmod (r^(k-1)*(r-1))).
 { rewrite Cmod_mult. apply Rle_lt_mult_compat; split; try lra.
   apply pow_lt; lra. }
 rewrite E, Cmod_1, mu_carac' in LT; trivial; lra.
Qed.

Lemma other_roots_lt_mu k (r:C) :
 Root r (ThePoly k) -> r <> mu k -> Cmod r < mu k.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { intros Hr. now apply ThePoly_0_NoRoot in Hr. }
 intros R N.
 assert (LE := roots_le_mu k r R).
 apply Rle_lt_or_eq_dec in LE. destruct LE as [LT|E]; trivial.
 destruct N.
 apply ThePoly_root_eqn in R.
 assert (E' : (Cmod (r^(k-1) * (r - 1)) = mu k^(k-1) * (mu k -1))%R).
 { rewrite R, Cmod_1, mu_carac'; trivial; lra. }
 rewrite Cmod_mult, Cmod_pow, E in E'.
 apply Rmult_eq_reg_l in E'.
 2:{ apply pow_nonzero. generalize (mu_itvl k); lra. }
 rewrite <- E in E'.
 apply Cmod_triangle_exact in E'. congruence.
Qed.

Lemma root_equal_Cmod_Re k (r1 r2:C) :
 Root r1 (ThePoly k) -> Root r2 (ThePoly k) ->
 Cmod r1 = Cmod r2 -> Re r1 = Re r2.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { intros Hr. now apply ThePoly_0_NoRoot in Hr. }
 intros R1 R2 E.
 assert (E1 := ThePoly_root_eqn _ _ R1).
 assert (E2 := ThePoly_root_eqn _ _ R2).
 assert (E' : (Cmod (r1^(k-1) * (r1 - 1)) = Cmod (r2^(k-1) * (r2 -1)))).
 { now rewrite E1, E2. }
 rewrite !Cmod_mult, !Cmod_pow, <- E in E'.
 apply Rmult_eq_reg_l in E'.
 2:{ apply pow_nonzero. intro C. apply Cmod_eq_0 in C. subst r1.
     now apply (root_nz k). }
 assert (E3 : ((Cmod r1)^2 = (Cmod r2)^2)%R) by now rewrite E. clear E.
 assert (E4 : (Cmod (r1-1)^2 = Cmod (r2-1)^2)%R) by now rewrite E'. clear E'.
 rewrite !Cmod2_alt in E3,E4.
 unfold Cminus in *. rewrite !re_plus, !im_plus in *.
 replace (Im (-(1))) with 0%R in * by (unfold Im; simpl; lra).
 replace (Re (-(1))) with (-1)%R in * by (unfold Re; simpl; lra).
 lra.
Qed.

Lemma root_equal_Cmod_Im k (r1 r2:C) :
 Root r1 (ThePoly k) -> Root r2 (ThePoly k) ->
 Cmod r1 = Cmod r2 -> Rabs (Im r1) = Rabs (Im r2).
Proof.
 intros R1 R2 E.
 assert (E1 : Re r1 = Re r2). eapply root_equal_Cmod_Re; eauto.
 assert (E2 : ((Cmod r1)^2 = (Cmod r2)^2)%R) by now rewrite E. clear E.
 rewrite !Cmod2_alt, <-E1 in E2.
 apply Rsqr_eq_abs_0. rewrite !Rsqr_pow2. lra.
Qed.

Lemma root_order_Cmod_Re k (r1 r2:C) :
 Root r1 (ThePoly k) -> Root r2 (ThePoly k) ->
 (Cmod r1 < Cmod r2 -> Re r1 < Re r2)%R.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { intros Hr. now apply ThePoly_0_NoRoot in Hr. }
 intros R1 R2 LT.
 assert (E1 := ThePoly_root_eqn _ _ R1).
 assert (E2 := ThePoly_root_eqn _ _ R2).
 assert (K1 : k<>1%nat).
 { intros ->. simpl in *. rewrite !Cmult_1_l in *.
   replace r1 with ((r1-1)+1) in LT by ring.
   replace r2 with ((r2-1)+1) in LT by ring. rewrite E1,E2 in LT. lra. }
 assert (E : (Cmod (r1^(k-1) * (r1 - 1)) = Cmod (r2^(k-1) * (r2 -1)))).
 { now rewrite E1,E2. }
 rewrite !Cmod_mult, !Cmod_pow in E.
 assert (LT' : (Cmod (r2 - 1) < Cmod (r1 - 1))%R).
 { apply Rmult_lt_reg_l with (Cmod r1 ^(k-1))%R.
   - apply pow_lt. apply Cmod_gt_0. intros ->. now apply (root_nz k).
   - rewrite E. apply Rmult_lt_compat_r.
     + apply Cmod_gt_0. intros E'. apply Ceq_minus in E'. subst.
       now apply (root_non_1 k).
     + apply pow_lt_compat_l. 2:lia. split; trivial. apply Cmod_ge_0. }
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

Lemma roots_ge_nu k (r:C) :
 Nat.Even k -> Root r (ThePoly k) -> -nu k <= Cmod r.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { intros _ Hr. now apply ThePoly_0_NoRoot in Hr. }
 intros K' R.
 assert (E := ThePoly_root_eqn _ _ R).
 apply Rnot_lt_le. intros L.
 assert (Iv := nu_itvl k K K').
 assert (H : (Cmod (r-1) < 1 - nu k)%R).
 { apply Rle_lt_trans with (1 + Cmod r)%R; try lra.
   eapply Rle_trans; [apply Cmod_triangle|]. rewrite Cmod_opp, Cmod_1. lra. }
 assert (H' : Cmod (r^(k-1)) <= (-nu k)^(k-1)).
 { rewrite Cmod_pow. apply pow_incr. split; try lra. apply Cmod_ge_0. }
 assert (LT : Cmod (r^(k-1)*(r-1)) < (-nu k)^(k-1)*(1 - nu k)).
 { rewrite Cmod_mult. apply Rle_lt_mult_compat; split; trivial; try lra.
   - apply Cmod_gt_0. apply Cpow_nonzero. intros ->. now apply (root_nz k).
   - apply Cmod_gt_0. intros E'. rewrite <- Ceq_minus in E'. subst.
     now apply (root_non_1 k). }
 revert LT. rewrite E, Cmod_1.
 replace (-nu k)%R with ((-1)*nu k)%R by ring.
 rewrite Rpow_mult_distr, minusone_pow_odd.
 2:{ apply Nat.Even_succ. now fixpred. }
 replace (_*_)%R with 1%R. lra.
 ring_simplify. rewrite Rmult_comm, tech_pow_Rmult. fixpred.
 rewrite nu_carac; trivial. lra.
Qed.

Lemma other_roots_gt_nu k (r:C) :
 Nat.Even k -> Root r (ThePoly k) -> r <> nu k -> -nu k < Cmod r.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { intros _ Hr. now apply ThePoly_0_NoRoot in Hr. }
 intros K' R N.
 assert (GE := roots_ge_nu k r K' R).
 apply Rle_lt_or_eq_dec in GE. destruct GE as [GT|E]; trivial.
 destruct N.
 assert (E' : (Cmod (r^(k-1) * (r - 1)) = nu k^(k-1) * (nu k -1))%R).
 { rewrite (ThePoly_root_eqn _ _ R), Cmod_1, nu_carac'; trivial; lra. }
 replace (nu k^(k-1)*(nu k -1))%R with ((-nu k)^(k-1)*(1-nu k))%R in E'.
 2:{ replace (-nu k)%R with ((-1)*nu k)%R by ring.
     rewrite Rpow_mult_distr, minusone_pow_odd. ring.
     rewrite <- Nat.Even_succ; now fixpred. }
 rewrite Cmod_mult, Cmod_pow, <- E in E'.
 apply Rmult_eq_reg_l in E'.
 2:{ apply pow_nonzero. generalize (nu_itvl k K K'); lra. }
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

Definition SortedRoots k l := ThePoly k ≅ linfactors l /\ Csorted l.

Lemma SortedRoots_exists k : k<>O -> exists l, SortedRoots k l.
Proof.
 intros K.
 destruct (ThePoly_separated_roots k K) as (l & _ & ND & E).
 destruct (Csorted_exists l ND) as (l' & P & L').
 exists l'. split; trivial. rewrite E. now apply linfactors_perm.
Qed.

Lemma SortedRoots_nz l : ~SortedRoots 0 l.
Proof.
 intros (E,_).
 rewrite ThePoly_0 in E.
 assert (length l = O).
 { rewrite <- (linfactors_degree l), <- E.
   generalize (degree_length [-C1]). simpl. lia. }
 destruct l; try easy. simpl in *.
 assert (E' : Peval [-C1] 0 = Peval [C1] 0) by now rewrite E.
 cbn in E'. injection E'. lra.
Qed.

Lemma SortedRoots_roots k l :
  SortedRoots k l -> forall r, In r l <-> Root r (ThePoly k).
Proof.
 intros (E,_) r. rewrite E. apply linfactors_roots.
Qed.

Lemma SortedRoots_length k l : SortedRoots k l -> length l = k.
Proof.
 intros (E,_). rewrite <- linfactors_degree, <- E. apply ThePoly_deg.
Qed.

Lemma SortedRoots_nodup k l : SortedRoots k l -> NoDup l.
Proof.
 intros L. apply Csorted_nodup, L.
Qed.

Lemma SortedRoots_unique k l l' :
  SortedRoots k l -> SortedRoots k l' -> l = l'.
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

Lemma SortedRoots_mu k l : SortedRoots k l -> l@0 = mu k.
Proof.
 intros SR.
 destruct (Nat.eq_dec k 0) as [->|K]. { now apply SortedRoots_nz in SR. }
 assert (H : length l = k) by apply (SortedRoots_length _ _ SR).
 destruct l as [|r l]. simpl in *; lia. clear H.
 unfold Cnth. simpl.
 destruct (Ceq_dec r (mu k)) as [ |N]; [trivial|exfalso].
 assert (M : In (RtoC (mu k)) (r::l))
  by (apply (SortedRoots_roots _ _ SR), mu_is_root; trivial).
 simpl in M. destruct M as [M|M]; try easy.
 assert (R : Root r (ThePoly k))
   by (apply (SortedRoots_roots _ _ SR); now left).
 assert (LT : Cmod r < mu k) by (apply other_roots_lt_mu; trivial).
 replace (mu k) with (Cmod (mu k)) in LT.
 2:{ rewrite Cmod_R. apply Rabs_right. generalize (mu_pos k). lra. }
 eapply root_order_Cmod_Re in LT; eauto. 2:now apply mu_is_root.
 destruct SR as (E,SC). rewrite Csorted_alt in SC. inversion_clear SC.
 rewrite Forall_forall in H0. specialize (H0 _ M). do 2 red in H0.
 assert (Clt r r). { transitivity (RtoC (mu k)); trivial. now left. }
 revert H1. apply Clt_order.
Qed.

Lemma SortedRoots_nu k l : Nat.Even k -> SortedRoots k l -> l@(k-1) = nu k.
Proof.
 intros K' SR.
 destruct (Nat.eq_dec k 0) as [->|K]. { now apply SortedRoots_nz in SR. }
 assert (H : length l = k) by apply (SortedRoots_length _ _ SR).
 rewrite <- H at 1.
 unfold Cnth. rewrite <- rev_nth by lia.
 assert (RO := SortedRoots_roots _ _ SR).
 destruct SR as (_,CS). rewrite Csorted_rev in CS.
 rewrite <- rev_length in H.
 setoid_rewrite In_rev in RO.
 destruct (rev l) as [|r l']; simpl in H; try lia; clear H. simpl.
 destruct (Ceq_dec r (nu k)) as [ |N]; [trivial|exfalso].
 assert (R : Root r (ThePoly k)) by (apply RO; now left).
 assert (NU : In (RtoC (nu k)) (r::l')).
 { apply RO, ThePoly_root_carac.
   now rewrite !RtoC_pow, <- RtoC_plus, nu_carac. }
 simpl in NU. destruct NU as [NU|NU]; try easy.
 apply other_roots_gt_nu in R; trivial.
 rewrite <- Rabs_left in R by (generalize (nu_itvl k K K'); lra).
 rewrite <- Cmod_R in R.
 apply (root_order_Cmod_Re k) in R.
 2:{ apply RO. now right. }
 2:{ apply RO. now left. }
 apply Sorted.Sorted_StronglySorted in CS; try apply Clt_order.
 inversion_clear CS.
 rewrite Forall_forall in H0. specialize (H0 _ NU).
 assert (Clt r r). { transitivity (RtoC (nu k)); trivial. now left. }
 revert H1. apply Clt_order.
Qed.

Lemma root_conj k c : Root c (ThePoly k) -> Root (Cconj c) (ThePoly k).
Proof.
 rewrite !ThePoly_root_carac. intros E.
 now rewrite <- !Cpow_conj, E, Cconj_plus_distr, Cconj_R.
Qed.

Lemma root_img k c :
  Root c (ThePoly k) -> c<>mu k -> c<>nu k -> Im c <> 0%R.
Proof.
 intros R M N E.
 destruct (Nat.eq_dec k 0) as [->|K]. { now apply ThePoly_0_NoRoot in R. }
 destruct c as (x,y). simpl in *. subst. change (x,0%R) with (RtoC x) in *.
 rewrite ThePoly_root_carac in R. rewrite !RtoC_pow,<-RtoC_plus in R.
 apply RtoC_inj in R.
 destruct (Nat.Even_or_Odd k) as [E|O].
 - destruct (mu_or_nu k x E); trivial; subst; now rewrite ?P_root_equiv.
 - apply M. f_equal. apply mu_unique_odd; trivial. now rewrite P_root_equiv.
Qed.

Lemma SortedRoots_next k l :
  SortedRoots k l ->
  forall n, (n+2 < k)%nat -> Im (l@n) <= 0 ->
    0 < Im (l@(n+1)) /\ l@(n+2) = Cconj (l@(n+1)).
Proof.
 intros SR n N H.
 destruct (Nat.eq_dec k 0) as [->|K]. { now apply SortedRoots_nz in SR. }
 set (r := l @ (n + 1)).
 assert (length l = k) by now apply SortedRoots_length.
 assert (SR' := SortedRoots_roots k l SR).
 assert (R : Root r (ThePoly k)). { apply SR', nth_In. lia. }
 assert (IN : In (Cconj r) l). { apply SR'. now apply root_conj. }
 destruct (In_nth l (Cconj r) 0 IN) as (m & M & E'). clear IN.
 change (l@m = r^*) in E'.
 destruct (Rle_or_lt (Im r) 0).
 - exfalso.
   set (r0 := l@n) in *.
   assert (R0' : Root r0 (ThePoly k)). { apply SR', nth_In. lia. }
   assert (Im r <> R0).
   { apply (root_img k); trivial.
     - assert (EM : l@0 = mu k) by now apply (SortedRoots_mu k).
       destruct SR as (E,SC). rewrite Csorted_alt, StronglySorted_nth in SC.
       assert (MM : Cgt (l@0) (l@(n+1))) by (apply SC; lia).
       fold r in MM. rewrite EM in MM. intros ->. revert MM. apply Cgt_order.
     - destruct (Nat.Even_Odd_dec k) as [E|O] eqn:EO.
       + assert (EN : l@(k-1) = nu k) by now apply (SortedRoots_nu k).
         destruct SR as (_,SC).
         rewrite Csorted_alt, StronglySorted_nth in SC.
         assert (NN : Cgt (l@(n+1)) (l@(k-1))) by (apply SC; lia).
         fold r in NN. rewrite EN in NN. intros ->. revert NN.
         apply Cgt_order.
       + unfold nu. destruct k.
         * intros ->. now apply (root_nz 0).
         * rewrite EO. intros ->. now apply (root_nz (S k)). }
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
   destruct (root_equal_or_conj k r0 r) as [-> | ->]; trivial.
   + destruct r as (x,y), r0 as (x0,y0). unfold Clt, Cconj in *. simpl in *.
     lra.
   + destruct r as (x,y). unfold Clt, Cconj in *. simpl in *. lra.
   + revert H7. apply Clt_order.
 - split; trivial. clear H.
   set (r' := l@(n+2)) in *.
   assert (R' : Root r' (ThePoly k)). { apply SR', nth_In. lia. }
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
     destruct (root_equal_or_conj k r' r) as [-> | ->]; trivial.
     * destruct r as (x,y), r' as (x',y').
       unfold Clt, Cconj in *. simpl in *. lra.
     * destruct r as (x,y). unfold Clt, Cconj in *. simpl in *. lra.
Qed.

Lemma SortedRoots_im_pos k l :
  SortedRoots k l ->
  forall p, (2*p+2<k)%nat ->
     let r := l@(2*p+1) in
     let r' := l@(2*p+2) in
     0 < Im r /\ r' = Cconj r.
Proof.
 induction p; intros Hp.
 - simpl in Hp. simpl.
   apply (SortedRoots_next k l H 0); simpl; try lia.
   rewrite (SortedRoots_mu k), im_RtoC; trivial. lra.
 - apply (SortedRoots_next k l H); try lia.
   destruct IHp as (LT,E); try lia.
   replace (2*p+2)%nat with (2*S p)%nat in E by lia. rewrite E.
   rewrite im_conj. lra.
Qed.

Lemma SortedRoots_Re_sorted k l :
  SortedRoots k l ->
  Sorted.StronglySorted (fun c c' => Re c >= Re c') l.
Proof.
 intros SR.
 apply StronglySorted_nth. intros n m H.
 assert (SR' := SortedRoots_roots k l SR).
 set (r := l@n).
 set (r' := l@m).
 assert (R : Root r (ThePoly k)). { apply SR', nth_In. lia. }
 assert (R' : Root r' (ThePoly k)). { apply SR', nth_In. lia. }
 destruct SR as (E,SC). rewrite Csorted_alt, StronglySorted_nth in SC.
 assert (LT : Clt r' r) by (apply SC; lia).
 destruct LT; lra.
Qed.

Lemma SortedRoots_Cmod_sorted k l :
  SortedRoots k l ->
  Sorted.StronglySorted (fun c c' => Cmod c >= Cmod c') l.
Proof.
 intros SR.
 apply StronglySorted_nth. intros n m H.
 assert (SR' := SortedRoots_roots k l SR).
 set (r := l@n).
 set (r' := l@m).
 assert (R : Root r (ThePoly k)). { apply SR', nth_In. lia. }
 assert (R' : Root r' (ThePoly k)). { apply SR', nth_In. lia. }
 destruct SR as (E,SC). rewrite Csorted_alt, StronglySorted_nth in SC.
 assert (LT : Clt r' r) by (apply SC; lia).
 destruct LT as [LT|(EQ,LT)].
 - rewrite <- root_order_Cmod_Re_iff in LT; eauto. lra.
 - rewrite <- root_equal_Cmod_Re_iff in EQ; eauto. lra.
Qed.

Lemma second_best_root k l :
  (4 <= k)%nat ->
  SortedRoots k l ->
  l@2 = Cconj (l@1) /\ Cmod (l@3) < Cmod (l@1) /\
  forall n, (3<=n<k)%nat -> Cmod (l@n) <= Cmod (l@3).
Proof.
 intros Q SR. split.
 { apply (SortedRoots_im_pos k l SR 0 lia). }
 assert (SR' := SortedRoots_roots k l SR).
 assert (LN := SortedRoots_length k l SR).
 assert (Cmod (l@3) < Cmod (l@1)).
 { set (r := l@1). set (r' := l@3).
   assert (R : Root r (ThePoly k)). { apply SR', nth_In. lia. }
   assert (R' : Root r' (ThePoly k)). { apply SR', nth_In. lia. }
   destruct (SortedRoots_im_pos k l SR 0) as (IM,E); try lia.
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

Section Roots.
Variable k : nat.
Variable roots : list C.
Hypothesis roots_ok : SortedRoots k roots.

Let K : k<>O.
Proof.
 intros ->. apply (SortedRoots_nz _ roots_ok).
Qed.

Let roots_len : length roots = k.
Proof.
 now apply SortedRoots_length.
Qed.

(** sum of roots, product, sigma functions, newton sums *)

Lemma sigma_roots_gen p :
  (p <= k)%nat -> sigma p roots = (-1)^p * coef (k-p) (ThePoly k).
Proof.
 intros Hp.
 destruct roots_ok as (->,_).
 rewrite (linfactors_coefs roots k (k-p)); try lia.
 replace (k-(k-p))%nat with p by lia. rewrite Cmult_assoc, <- Cpow_mul_l.
 replace (-1*-1) with 1 by lca. rewrite Cpow_1_l. lca.
Qed.

Lemma sum_roots : (1<k)%nat -> Clistsum roots = 1.
Proof.
 intros Hk.
 rewrite <- sigma_1, sigma_roots_gen by lia.
 unfold ThePoly. rewrite !Pplus_coef, !coef_monom.
 repeat case Nat.eqb_spec; try lia; intros _ _.
 unfold coef; rewrite nth_overflow by (simpl; lia). lca.
Qed.

Lemma prod_roots : (1<k)%nat -> G_big_mult roots = (-1)^(k-1).
Proof.
 intros Hk.
 rewrite <- sigma_len, roots_len, sigma_roots_gen, Nat.sub_diag by lia.
 unfold ThePoly. rewrite !Pplus_coef, !coef_monom.
 repeat case Nat.eqb_spec; try lia; intros _ _.
 unfold coef; simpl. replace k with (S (k-1)) at 1 by lia. simpl. lca.
Qed.

Lemma sigma_roots_0 p : (1 < p < k)%nat -> sigma p roots = 0.
Proof.
 intros Hp.
 rewrite sigma_roots_gen by lia.
 unfold ThePoly. rewrite !Pplus_coef, !coef_monom.
 repeat case Nat.eqb_spec; try lia; intros _ _.
 unfold coef; rewrite nth_overflow by (simpl; lia). lca.
Qed.

Lemma newton_sum_roots p : (1 <= p < k)%nat -> newton_sum p roots = 1.
Proof.
 intros Hp.
 apply newton_identities_nosigma; rewrite ?roots_len; trivial.
 - rewrite sigma_1. apply sum_roots; lia.
 - apply sigma_roots_0.
Qed.

(** For expressing [A k] numbers, we consider linear combination of
    root powers with particular coefficents (not just 1 as in newton_sum) *)

Definition coefB r := r / r^(k-1) /(k*r-(k-1)).

Lemma krkm1_nz r : In r roots -> k*r-(k-1) <> 0.
Proof.
 intros R E.
 apply Cminus_eq_0 in E.
 assert (E' : r = (k-1)/k).
 { rewrite <- E; field. intros [=EQ]. apply (INR_eq k 0) in EQ.
   subst k. now apply (ThePoly_0_NoRoot r). }
 apply (root_non_km1k k). rewrite <- E'.
 now apply (SortedRoots_roots _ _ roots_ok).
Qed.

Lemma coefB_nz r : In r roots -> coefB r <> 0.
Proof.
 unfold coefB. intros R. apply (SortedRoots_roots _ _ roots_ok) in R.
 unfold Cdiv.
 rewrite <- Cmult_assoc, !Cmult_integral.
 intros [->|[E|E]].
 - now apply root_nz in R.
 - apply C1_neq_C0.
   rewrite <- (Cinv_l (r^(k-1))), E. lca. apply Cpow_nonzero.
   intros ->. now apply root_nz in R.
 - apply C1_neq_C0.
   rewrite <- (Cinv_l (k*r-(k-1))), E. lca.
   intros E'. apply Cminus_eq_0 in E'.
   assert (E'' : r = (k-1)/k).
   { rewrite <- E'; field. intros [=EQ]. apply (INR_eq k 0) in EQ.
     subst k. now apply (ThePoly_0_NoRoot r). }
   apply (root_non_km1k k). now rewrite <- E''.
Qed.

Lemma coefB_diff r : r<>0 -> coefB r = / Peval (Pdiff (ThePoly k)) r.
Proof.
 intros Hr. unfold coefB. destruct (Nat.eq_dec k 1) as [->|Hk].
 - rewrite ThePoly_diff_1. unfold Peval; simpl. now field.
 - rewrite ThePoly_diff_expr by lia.
   rewrite Cinv_mult. unfold Cdiv. f_equal.
   replace (k-1)%nat with (S (k-2)) at 1 by lia. simpl.
   rewrite Cinv_mult, Cmult_assoc, Cinv_r by trivial. lca.
Qed.

Definition Interpol : Polynomial :=
  big_sum (fun i => [coefB (roots@i)] *, linfactors (remove_at i roots)) k
  +, [-(1)].

Lemma Interpol_roots r : In r roots -> Root r Interpol.
Proof.
 intros Hr. destruct (In_nth _ _ 0 Hr) as (i & Hi & <-).
 rewrite roots_len in Hi. fold (roots @ i) in *.
 unfold Root, Interpol.
 rewrite Pplus_eval, Psum_eval, (big_sum_kronecker _ _ i); trivial.
 2:{ intros j J J'. rewrite Pmult_eval. apply Cmult_integral. right.
     apply linfactors_roots.
     apply remove_at_In; trivial; rewrite roots_len; lia. }
 rewrite Pmult_eval, !Pconst_eval.
 rewrite Peval_linfactors, <- Peval_Pdiff_linfactors; try lia.
 2:{ now apply (SortedRoots_nodup k). }
 rewrite coefB_diff, <- (proj1 roots_ok).
 2:{ intros E. apply (root_nz k). rewrite <- E.
     now apply (SortedRoots_roots _ _ roots_ok). }
 field.
 apply ThePoly_no_common_root_with_diff.
 now apply (SortedRoots_roots _ _ roots_ok).
Qed.

Lemma Interpol_degree : (degree Interpol <= k-1)%nat.
Proof.
 unfold Interpol.
 etransitivity; [apply Pplus_degree1|].
 replace (degree [_]) with O.
 2:{ generalize (degree_length [-(1)]). simpl. lia. }
 rewrite Nat.max_0_r.
 apply Psum_degree.
 intros i Hi.
 rewrite Pscale_degree.
 2:{ apply coefB_nz. apply nth_In; lia. }
 rewrite linfactors_degree, remove_at_length; lia.
Qed.

Lemma Interpol_null : Peq Interpol [].
Proof.
 apply (extra_roots_implies_null _ roots).
 - apply (SortedRoots_nodup _ _ roots_ok).
 - apply Interpol_roots.
 - generalize Interpol_degree. lia.
Qed.

Lemma sum_coefB_div_r : (1<k)%nat ->
  Clistsum (map (fun r => coefB r / r) roots) = 1.
Proof.
 intros K'.
 rewrite Clistsum_map with (d:=0). rewrite roots_len.
 assert (E : Peval Interpol 0 = 0). { now rewrite Interpol_null. }
 unfold Interpol in E. rewrite Pplus_eval, Psum_eval, Pconst_eval in E.
 apply Ceq_minus in E. rewrite <- E. clear E.
 apply big_sum_eq_bounded. intros i Hi.
 rewrite Pmult_eval, Pconst_eval. unfold Cdiv. f_equal.
 assert (Z : roots@i <> 0).
 { intros E. apply (root_nz k). rewrite <- E.
   apply (SortedRoots_roots _ _ roots_ok). apply nth_In; lia. }
 apply Cmult_eq_reg_l with (roots@i); trivial. rewrite Cinv_r; trivial.
 symmetry.
 rewrite Peval_linfactors.
 erewrite map_ext.
 2:{ intros a. replace (0-a) with (a*(-1)) by lca. reflexivity. }
 rewrite Gbigmult_factor_r, remove_at_length; rewrite roots_len; try lia.
 rewrite Cmult_assoc.
 change (roots@i * _) with (G_big_mult (roots@i :: remove_at i roots)).
 rewrite Gbigmult_perm with (l':=roots).
 - rewrite prod_roots by trivial.
   rewrite <- Nat.sub_1_r, <- Cpow_mul_l. replace (-1*-1) with 1 by lca.
   apply Cpow_1_l.
 - rewrite <- (insert_permut i).
   apply eq_Permutation, insert_at_remove_at. lia.
Qed.

(* Actually unused, can be retrieved differently, see Equation_B: *)
Lemma sum_coefB : (1<k)%nat -> Clistsum (map coefB roots) = 0.
Proof.
 intros K'.
 rewrite Clistsum_map with (d:=0). rewrite roots_len.
 assert (E : coef (k-1) Interpol = 0).
 { rewrite Interpol_null. now destruct (k-1)%nat. }
 unfold Interpol in E. rewrite Pplus_coef, Psum_coef in E.
 replace (coef (k-1) [_]) with 0 in E.
 2:{ unfold coef. replace (k-1)%nat with (S (k-2)) by lia. simpl.
     now destruct (k-2)%nat. }
 rewrite Cplus_0_r in E. rewrite <- E at 1. clear E.
 apply big_sum_eq_bounded. intros i Hi.
 rewrite Pscale_coef.
 replace (k-1)%nat with (length (remove_at i roots)).
 2:{ rewrite remove_at_length; lia. }
 now rewrite linfactors_coef, Cmult_1_r.
Qed.

(** The other coefficients of Interpol are much harder to exploit,
    fortunately we can proceed differently. *)

Definition Amk p := Clistsum (map (fun r => r^p /(k*r-(k-1))) roots).

Lemma Amk1_Amk0 : (1<k)%nat -> Amk 1 - Amk 0 = 1.
Proof.
 intros K'.
 replace (Amk 1 - Amk 0) with (Amk 1 - Amk 0) by lca.
 unfold Amk. rewrite Clistsum_minus.
 rewrite <- sum_coefB_div_r at 1 by trivial. f_equal.
 apply map_ext_in. intros r Hr. unfold coefB.
 set (d := k * r - (k - 1)).
 assert (D : d<>0) by now apply krkm1_nz.
 apply (SortedRoots_roots _ _ roots_ok) in Hr.
 assert (R : r<>0). { intros E. apply (root_nz k). now rewrite <- E. }
 assert (R' : r^(k-1)<>0) by now apply Cpow_nonzero.
 apply Cmult_eq_reg_l with (d * r ^(k-1)).
 2:{ rewrite Cmult_integral; now intros [ | ]. }
 rewrite Ceq_minus. field_simplify; try easy.
 rewrite (Cmult_comm _ r), <- Cpow_S. fixpred.
 apply ThePoly_root_carac in Hr. rewrite Hr. ring.
Qed.

Lemma Amk1_Amk0_alt :  k * Amk 1 + (1-k) * Amk 0 = k.
Proof.
 unfold Amk.
 rewrite !Clistsum_factor_l, !map_map, Clistsum_plus.
 rewrite map_ext_in with (g := fun _ => 1).
 rewrite Clistsum_const, roots_len; lca.
 intros r Hr. field. now apply krkm1_nz.
Qed.

Lemma Amk0_is_0 : (1<k)%nat -> Amk 0 = 0.
Proof.
 intros K'.
 assert (E1 := Amk1_Amk0 K').
 assert (E2 := Amk1_Amk0_alt). rewrite Ceq_minus in E2.
 replace (Amk 1) with (Amk 0 + 1) in E2 by (rewrite <- E1; ring).
 now ring_simplify in E2.
Qed.

Lemma Amk_is_1 p : (1<=p<=k)%nat -> Amk p = 1.
Proof.
 destruct (Nat.eq_dec k 1) as [K'|K'].
 { intros Hp. replace p with 1%nat by lia.
   generalize Amk1_Amk0_alt. rewrite K'. simpl.
   replace (1-1) with 0 by lca.
   now rewrite Cmult_1_l, Cmult_0_l, Cplus_0_r. }
 induction p as [[|p] IH] using lt_wf_ind; try easy.
 intros Hp.
 assert (E := newton_identities_adhoc roots).
 rewrite roots_len in E. cbv zeta in E.
 rewrite sigma_1 in E.
 specialize (E (sum_roots lia) sigma_roots_0 p lia).
 set (d := fun r => k * r + (1-k)) in *.
 assert (D : forall r, In r roots -> d r <> 0).
 { intros r Hr. unfold d.
   replace (1-k) with (-(k-1)) by lca. now apply krkm1_nz. }
 rewrite map_ext_in with (g:=fun r => (d r)^S p / d r) in E.
 2:{ intros r Hr. unfold d. simpl. field. now apply D. }
 erewrite map_ext_in in E.
 2:{ intros r Hr. unfold d at 1. rewrite binomial_formula.
     unfold Cdiv.
     change Cmult with (Gmult (R:=C)).
     rewrite big_sum_mult_r. change Gmult with Cmult.
     rewrite big_sum_sum_n. reflexivity. }
 rewrite <- Clistsum_sum_n, <- big_sum_sum_n in E.
 rewrite big_sum_shift in E.
 replace (Clistsum _) with 0 in E.
 2:{ clear E. cbn - [Cpow]. replace 0 with ((1-k)^S p * Amk 0).
     2:{ rewrite Amk0_is_0 by lia. lca. }
     unfold Amk. rewrite Clistsum_factor_l, map_map. f_equal.
     apply map_ext_in. intros r Hr.
     simpl. unfold d. field. now apply D. }
 rewrite Cplus_0_l in E.
 replace 1 with ((k+(1-k))^S p) in E at 1.
 2:{ replace (k+(1-k)) with 1 by lca. apply Cpow_1_l. }
 rewrite binomial_formula in E. symmetry in E.
 rewrite big_sum_shift in E. rewrite Nat.sub_0_r in E.
 replace (binom _ _ * _) with 1 in E by (simpl; lca).
 rewrite Cmult_1_l in E. change Gplus with Cplus in E.
 ring_simplify in E.
 rewrite <- !big_sum_extend_r in E. change Gplus with Cplus in E.
 set (S1 := big_sum _ _) in E.
 set (S2 := big_sum _ _) in E.
 rewrite Ceq_minus in E.
 replace S1 with S2 in E.
 2:{ apply big_sum_eq_bounded. intros i Hi. clear S1 S2 E.
     rewrite <- (Cmult_1_r (binom _ _ * _ * _)).
     rewrite <- (IH (S i) lia lia) at 2. unfold Amk.
     rewrite Clistsum_factor_l, map_map. f_equal. apply map_ext_in.
     intros r Hr. unfold d. rewrite Cpow_mul_l. field.
     now apply krkm1_nz. }
 ring_simplify in E. clear S1 S2.
 rewrite binom_diag, Nat.sub_diag, Cpow_0_r in E.
 replace (Clistsum _) with (k^S p * Amk (S p)) in E.
 2:{ unfold Amk. rewrite Clistsum_factor_l, map_map. f_equal.
     apply map_ext_in. intros r Hr.
     rewrite Cpow_mul_l. unfold d. simpl INR. field. now apply D. }
 replace (_+_) with (k^S p * (1 - Amk (S p))) in E by (simpl; ring).
 apply Cmult_integral in E. destruct E as [E|E].
 { exfalso. revert E. apply Cpow_nonzero. intros [= E].
   apply K, INR_eq, E. }
 now rewrite <- Ceq_minus in E.
Qed.

Lemma Amk_rec p : (k <= p)%nat -> Amk p = Amk (p-1) + Amk (p-k).
Proof.
 intros Hp.
 unfold Amk.
 rewrite Clistsum_plus. f_equal. apply map_ext_in. intros r Hr.
 set (d := _ - _).
 assert (d <> 0) by now apply krkm1_nz.
 apply (SortedRoots_roots _ _ roots_ok), ThePoly_root_carac in Hr.
 replace p with (k + (p-k))%nat at 1 by lia.
 rewrite Cpow_add_r, Hr, Cmult_plus_distr_r, <- Cpow_add_r.
 replace (k-1+(p-k))%nat with (p-1)%nat by lia. now field.
Qed.

Lemma Amk_A p : Amk (k+p) = A k p.
Proof.
 destruct (Nat.eq_dec k 1) as [K'|K'].
 - rewrite K', A_1_pow2.
   assert (In C2 roots).
   { rewrite (SortedRoots_roots _ _ roots_ok).
     rewrite <- mu_1. rewrite K'. now apply mu_is_root. }
   assert (E : roots = [C2]).
   { destruct roots as [|a [|b l]]; simpl in *; try lia.
     f_equal; tauto. }
   unfold Amk. rewrite E, K'. simpl. rewrite pow_INR, <-RtoC_pow.
   change (INR 2) with 2. field.
 - induction p as [[|p] IH] using lt_wf_ind.
   + rewrite Nat.add_0_r, A_base by lia. apply Amk_is_1; lia.
   + simpl. rewrite Amk_rec, plus_INR, RtoC_plus by lia. f_equal.
     * rewrite <- IH by lia. f_equal; lia.
     * destruct (Nat.lt_ge_cases p (k-1)).
       { replace (p - (k-1))%nat with O by lia. apply Amk_is_1; lia. }
       { rewrite <- IH by lia. f_equal; lia. }
Qed.

Definition coefA r := r^k / (k*r-(k-1)).

Lemma Equation_A n :
  RtoC (A k n) = Clistsum (map (fun r => coefA r * r^n) roots).
Proof.
 rewrite <- Amk_A. unfold Amk. f_equal. apply map_ext.
 intros r. unfold coefA, Cdiv. rewrite Cpow_add_r. ring.
Qed.

(** Differences *)

Definition coefdA r := coefA r * (/r - tau k).

Lemma coefdA_mu : coefdA (mu k) = 0.
Proof.
 unfold coefdA, tau. rewrite RtoC_inv. ring.
Qed.

Lemma coefdA_sum : k<>1%nat -> Clistsum (map coefdA roots) = 1-tau k.
Proof.
 intros K'.
 replace (Clistsum _) with (Amk (k-1) - tau k * Amk k).
 2:{ unfold Amk. rewrite Clistsum_factor_l, map_map, Clistsum_minus.
     f_equal. apply map_ext_in.
     intros r Hr. unfold coefdA, coefA, Cdiv, Cminus.
     rewrite (Cmult_comm _ (/r + _)), !Cmult_assoc, !Copp_mult_distr_l.
     rewrite <- Cmult_plus_distr_r. f_equal.
     rewrite Cmult_plus_distr_r. f_equal.
     assert (r <> 0).
     { intros ->.
       now apply (SortedRoots_roots _ _ roots_ok), root_nz in Hr. }
     apply Cmult_eq_reg_l with r; trivial.
     rewrite <- !Cpow_S. fixpred. now field. }
 rewrite !Amk_is_1; try lia. lca.
Qed.

Lemma Equation_dA n :
  k<>1%nat ->
  RtoC (A k (n-1) - tau k * A k n) =
  Clistsum (map (fun r => coefdA r * r^n) (tl roots)).
Proof.
 intros K'.
 assert (E : roots = RtoC (mu k) :: tl roots).
 { assert (len := SortedRoots_length _ _ roots_ok).
   destruct roots; simpl in *; try lia. f_equal.
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
   assert (mu k <> R0) by (generalize (mu_pos k); lra).
   rewrite RtoC_inv.
   field_simplify. 2:{ intro E'. apply RtoC_inj in E'. lra. }
   f_equal. apply map_ext_in. intros r R. unfold coefdA.
   replace n with (S (n-1)) at 2 3 by lia. simpl.
   field. intros ->. apply (root_nz k).
   rewrite <- (SortedRoots_roots k roots roots_ok).
   destruct roots; simpl in *; try easy. now right.
Qed.

Lemma sumA_Rlistsum l :
  INR (sumA k l) = Rlistsum (map (fun n => INR (A k n)) l).
Proof.
 induction l; simpl; trivial.
 now rewrite plus_INR, IHl.
Qed.

Lemma Equation_delta n :
 k<>1%nat ->
 RtoC (f k n - tau k * n) =
 Clistsum (map (fun m =>
   Clistsum (map (fun r => coefdA r * r^m) (tl roots)))
  (decomp k n)).
Proof.
 intros K'.
 rewrite f_decomp; trivial. rewrite <- (decomp_sum k n) at 2.
 set (l := decomp k n).
 rewrite RtoC_minus, RtoC_mult, !sumA_Rlistsum, !RtoC_Rlistsum, !map_map.
 rewrite Clistsum_factor_l, map_map, Clistsum_minus.
 f_equal. apply map_ext. intros m. replace (pred m) with (m-1)%nat by lia.
 rewrite <- Equation_dA; trivial. now rewrite RtoC_minus, RtoC_mult.
Qed.

Lemma Equation_delta' n :
 k<>1%nat ->
 RtoC (f k n - tau k * n) =
 Clistsum (map (fun r => coefdA r * Clistsum (map (Cpow r) (decomp k n)))
               (tl roots)).
Proof.
 intros K'.
 rewrite Equation_delta; trivial.
 rewrite Clistsum_Clistsum. f_equal. apply map_ext.
 intros a. now rewrite Clistsum_factor_l, map_map.
Qed.

End Roots.

Lemma coefA_nz k r : Root r (ThePoly k) -> coefA k r <> 0.
Proof.
 intros R.
 destruct (Nat.eq_dec k 0) as [->|K0].
 { now apply ThePoly_0_NoRoot in R. }
 unfold coefA. replace (r^k)%C with (r^(2*(k-1))*r/r^(k-1)).
 2:{ replace k with (S (k-1)) at 3 by lia.
     replace (2*(k-1))%nat with ((k-1)+(k-1))%nat by lia.
     rewrite Cpow_add. simpl. field. apply Cpow_nonzero.
     intros ->. now apply root_nz in R. }
 unfold Cdiv. rewrite <- !Cmult_assoc, (Cmult_assoc r).
 change (r^(2*(k-1))*coefB k r <> 0). intros E. apply Cmult_integral in E.
 destruct E as [E|E].
 - apply Cpow_nonzero in E; trivial. intros ->. now apply root_nz in R.
 - revert E. destruct (SortedRoots_exists k K0) as (roots & roots_ok).
   apply (coefB_nz _ _ roots_ok).
   now apply (SortedRoots_roots _ _ roots_ok).
Qed.

Lemma coefdA_nz k r : Root r (ThePoly k) -> r <> mu k -> coefdA k r <> 0.
Proof.
 intros R R'. unfold coefdA. intros E. apply Cmult_integral in E.
 destruct E as [E|E]. apply (coefA_nz k r R E).
 apply Cminus_eq_0 in E. apply R'.
 now rewrite tau_inv, RtoC_inv, <- E, Cinv_inv.
Qed.

Definition coef_mu k : R := (mu k ^k / (k*mu k -(k-1)))%R.

Lemma coef_mu_ok k : RtoC (coef_mu k) = coefA k (mu k).
Proof.
 unfold coef_mu, coefA.
 now rewrite !RtoC_pow, <- RtoC_mult, <- !RtoC_minus, <- RtoC_div.
Qed.

Lemma A_div_pow_mu_limit k :
 is_lim_seq (fun n => A k n / mu k ^n)%R (coef_mu k).
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { apply is_lim_seq_ext with (fun _ => R1).
   - intros n. rewrite A_0, A_1_pow2, mu_0. rewrite pow_INR.
     unfold Rdiv. rewrite Rinv_r. lra. apply pow_nonzero; lra.
   - unfold coef_mu. rewrite mu_0. simpl.
     replace (1/(0*2-(0-1)))%R with R1 by lra.
     apply is_lim_seq_const. }
 destruct (SortedRoots_exists k K) as (roots & roots_ok).
 assert (E := Equation_A k roots roots_ok).
 assert (roots_mu : roots@0 = mu k) by now apply SortedRoots_mu.
 assert (roots_len : length roots = k) by now apply SortedRoots_length.
 assert (mu12 := mu_itvl k).
 set (root := fun i => roots@i).
 set (coef := fun i => coefA k (root i)).
 assert (E' : forall n, big_sum (fun i => coef i * root i ^n) k = A k n).
 { intros n. now rewrite E, Clistsum_map with (d:=0), roots_len. }
 clear E.
 set (rest := (fun n i => Re (coef (S i) * (root (S i))^n) / mu k^n)%R).
 apply is_lim_seq_ext with (u := (fun n => coef_mu k + big_sum (rest n) (k-1))%R).
 - intros n.
   rewrite <- (re_RtoC (A k n)). rewrite <- E'. clear E'.
   replace k with (S (k-1)) at 3 by lia.
   rewrite big_sum_shift.
   rewrite re_plus, Re_big_sum, Rdiv_plus_distr.
   unfold Rdiv. rewrite (@big_sum_mult_r _ _ _ _ R_is_ring).
   f_equal. unfold coef, root. rewrite roots_mu, <- coef_mu_ok.
   rewrite RtoC_pow, <- RtoC_mult, re_RtoC. field. apply pow_nonzero. lra.
 - clear E'.
   rewrite <- (Rplus_0_r (coef_mu k)) at 1.
   apply is_lim_seq_plus'; [apply is_lim_seq_const|].
   apply is_lim_seq_big_sum_0. intros i Hi.
   apply is_lim_seq_0_abs with
     (fun n => Cmod (coef (S i)) * (Cmod (root (S i)) / mu k)^n)%R.
   + exists O. intros n _. unfold rest. clear rest.
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
       apply NoDup_nth in E; try lia. now apply (SortedRoots_nodup k).
Qed.

(* Print Assumptions A_div_pow_mu_limit. *)

Lemma coefA_conj k r :
  coefA k (Cconj r) = Cconj (coefA k r).
Proof.
 unfold coefA.
 rewrite Cdiv_conj, Cpow_conj, !Cconj_minus_distr, Cconj_mult_distr, !Cconj_R.
 easy.
Qed.

Lemma coefdA_conj k r :
  coefdA k (Cconj r) = Cconj (coefdA k r).
Proof.
 unfold coefdA. rewrite coefA_conj.
 now rewrite Cconj_mult_distr, Cconj_minus_distr, Cinv_conj, Cconj_R.
Qed.

Lemma coefdA_R n (r:R) : coefdA n r = Re (coefdA n r).
Proof.
 rewrite re_alt. rewrite <- coefdA_conj, Cconj_R. field.
Qed.

Lemma dA_expo k roots : (4<=k)%nat -> SortedRoots k roots ->
 let r := roots@1 in
 exists c : posreal,
 forall N, exists n, (N<=n)%nat /\
    c * (Cmod r)^n < A k (n-1) - tau k * A k n.
Proof.
 intros K roots_ok r.
 assert (len := SortedRoots_length _ _ roots_ok).
 destruct (second_best_root k _ lia roots_ok) as (E & LT & LE).
 fold r in E, LT.
 assert (R : Root r (ThePoly k)).
 { eapply SortedRoots_roots; eauto. apply nth_In. lia. }
 assert (R0 : r <> 0). { intros ->. now apply root_nz in R. }
 set (d := coefdA k r).
 assert (Hd : d<>0).
 { apply coefdA_nz; trivial.
   rewrite <- (SortedRoots_mu k _ roots_ok). intros EQ.
   apply NoDup_nth in EQ; try lia. eapply SortedRoots_nodup; eauto. }
 set (c_rest := Rlistsum (map (fun r => Cmod (coefdA k r)) (skipn 3 roots))).
 set (theta := Polar.get_arg r).
 set (rho := Polar.get_arg d).
 assert (Ht : (sin theta <> 0)%R).
 { destruct (SortedRoots_im_pos _ _ roots_ok 0) as (IM & _); try lia.
   simpl in IM. fold r in IM. rewrite <- (polar_eqn r) in IM.
   fold theta in IM. rewrite im_scal_l in IM.
   unfold Im, Cexp in IM. simpl in IM. nra. }
 assert (Cr := affine_cos_pos theta rho Ht). clear Ht.
 set (c := (1/2 * Cmod d)%R).
 assert (Hc : 0 < c).
 { unfold c. apply Rmult_lt_0_compat. lra. apply Cmod_gt_0; trivial. }
 exists (mkposreal c Hc). intros N. simpl.
 set (r' := roots@3) in *.
 set (ratio := (Cmod r' / Cmod r)%R).
 assert (R' : Root r' (ThePoly k)).
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
   rewrite <- map_map with (g := Cmod) (f:=coefdA k).
   apply Rlt_le_trans
    with (Cmod (coefdA k r') + Cmod (Clistsum (map (coefdA k) (skipn 4 roots))))%R.
   - apply Rplus_lt_le_0_compat; [ | apply Cmod_ge_0].
     apply Cmod_gt_0. apply coefdA_nz; trivial.
     rewrite <- (SortedRoots_mu k _ roots_ok). intros EQ.
     apply NoDup_nth in EQ; try lia. eapply SortedRoots_nodup; eauto.
   - apply Rplus_le_compat_l. apply Clistsum_mod. }
 destruct (large_enough_exponent' ratio (c/c_rest)) as (N' & HN'); trivial.
 { apply Rdiv_lt_0_compat; trivial. }
 destruct (Cr (max N N')) as (n & Hn & LTn).
 exists n. split; try lia.
 rewrite <- (re_RtoC (_-_)), (Equation_dA k _ roots_ok); trivial; try lia.
 assert (roots_eq : roots = roots@0 :: r :: Cconj r :: skipn 3 roots).
 { rewrite <- E.
   now do 3 (destruct roots; unfold Cnth in *; simpl in *; try lia). }
 rewrite roots_eq. clear Cr E.
 set (f := fun r => _).
 cbn -[skipn Re]. change (fold_right _ _) with Clistsum. unfold f at 1 2.
 rewrite coefdA_conj.
 fold d.
 rewrite <- Cpow_conj, <- Cconj_mult_distr, Cplus_assoc, !re_plus.
 rewrite re_conj, <- double.
 apply Rlt_minus_l. unfold Rminus. rewrite <- re_opp.
 eapply Rle_lt_trans;
   [eapply Rplus_le_compat_l, Rle_trans; [apply Rle_abs | apply re_le_Cmod] | ].
 rewrite Cmod_opp.
 rewrite <- (polar_eqn d). fold rho.
 rewrite <- (polar_eqn r) at 2. fold theta. rewrite Cpow_mul_l, Cexp_pow.
 replace (_ * _ * _)
  with (Cmod d * Cmod r ^ n * (Cexp rho * Cexp (theta * n))) by ring.
 rewrite <- Cexp_add.
 rewrite <- Cmult_assoc, RtoC_pow, !re_scal_l, <- Rmult_assoc.
 unfold Cexp, Re. simpl fst.
 rewrite (Rplus_comm rho).
 apply Rlt_le_trans with (2 * c * Cmod r ^ n)%R.
 2:{ unfold c.
     rewrite !Rmult_assoc, (Rmult_comm (1/2)), <- !Rmult_assoc.
     apply Rmult_le_compat_l; trivial.
     repeat apply Rmult_le_pos; try lra; try apply pow_le; apply Cmod_ge_0. }
 clear theta rho LTn.
 assert (Cmod (Clistsum (map f (skipn 3 roots))) < c * Cmod r ^n); try lra.
 eapply Rle_lt_trans; [apply Clistsum_mod|]. rewrite map_map. unfold f.
 eapply Rle_lt_trans; [apply Rlistsum_le
                       with (g:=(fun x => ratio^n * Cmod (coefdA k x * r ^ n))%R)|].
 { intros a Ha. unfold ratio. rewrite !Cmod_mult.
   destruct (In_nth _ _ 0 Ha) as (m & Hm & <-).
   replace (nth m (skipn 3 roots) 0) with (roots@(3+m))
    by now rewrite roots_eq at 1.
   rewrite skipn_length in Hm.
   specialize (LE (3+m)%nat lia).
   set (rm := roots@(3+m)) in *.
   set (dm := coefdA k rm). unfold Rdiv.
   rewrite Rpow_mult_distr, pow_inv, !Cmod_pow. field_simplify.
   2:{ apply pow_nonzero. intros E. now apply Cmod_eq_0 in E. }
   apply Rmult_le_compat_l. apply Cmod_ge_0. apply pow_incr; split; trivial.
   apply Cmod_ge_0. }
 { clearbody c. clear roots_eq f len roots_ok K LE.
   rewrite map_ext
     with (g:=(fun x => Cmod (coefdA k x) * (ratio^n * Cmod (r^n)))%R).
   2:{ intros a. rewrite Cmod_mult. ring. }
   replace (Rlistsum _) with (c_rest * (ratio ^ n * Cmod (r ^ n)))%R.
   2:{ unfold c_rest. now rewrite Rlistsum_distr, map_map. }
   rewrite Cmod_pow, <- Rmult_assoc. apply Rmult_lt_compat_r.
   - now apply pow_lt, Cmod_gt_0.
   - rewrite Rmult_comm. apply Rcomplements.Rlt_div_r; try lra.
     apply Rle_lt_trans with (ratio ^ N')%R; trivial.
     apply Rle_pow_low. lra. lia. }
Qed.

Lemma dA_expo' k roots : (4<=k)%nat -> SortedRoots k roots ->
 let r := roots@1 in
 exists c : posreal,
 forall N, exists n, (N<=n)%nat /\
    A k (n-1) - tau k * A k n < -c * (Cmod r)^n.
Proof.
 intros K roots_ok r.
 assert (len := SortedRoots_length _ _ roots_ok).
 destruct (second_best_root k _ lia roots_ok) as (E & LT & LE).
 fold r in E, LT.
 assert (R : Root r (ThePoly k)).
 { eapply SortedRoots_roots; eauto. apply nth_In. lia. }
 assert (R0 : r <> 0). { intros ->. now apply root_nz in R. }
 set (d := coefdA k r).
 assert (Hd : d<>0).
 { apply coefdA_nz; trivial.
   rewrite <- (SortedRoots_mu k _ roots_ok). intros EQ.
   apply NoDup_nth in EQ; try lia. eapply SortedRoots_nodup; eauto. }
 set (c_rest := Rlistsum (map (fun r => Cmod (coefdA k r)) (skipn 3 roots))).
 set (theta := Polar.get_arg r).
 set (rho := Polar.get_arg d).
 assert (Ht : (sin theta <> 0)%R).
 { destruct (SortedRoots_im_pos _ _ roots_ok 0) as (IM & _); try lia.
   simpl in IM. fold r in IM. rewrite <- (polar_eqn r) in IM.
   fold theta in IM. rewrite im_scal_l in IM.
   unfold Im, Cexp in IM. simpl in IM. nra. }
 assert (Cr := affine_cos_neg theta rho Ht). clear Ht.
 set (c := (1/2 * Cmod d)%R).
 assert (Hc : 0 < c).
 { unfold c. apply Rmult_lt_0_compat. lra. apply Cmod_gt_0; trivial. }
 exists (mkposreal c Hc). intros N. simpl.
 set (r' := roots@3) in *.
 set (ratio := (Cmod r' / Cmod r)%R).
 assert (R' : Root r' (ThePoly k)).
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
   rewrite <- map_map with (g := Cmod) (f:=coefdA k).
   apply Rlt_le_trans
    with (Cmod (coefdA k r') + Cmod (Clistsum (map (coefdA k) (skipn 4 roots))))%R.
   - apply Rplus_lt_le_0_compat; [ | apply Cmod_ge_0].
     apply Cmod_gt_0. apply coefdA_nz; trivial.
     rewrite <- (SortedRoots_mu k _ roots_ok). intros EQ.
     apply NoDup_nth in EQ; try lia. eapply SortedRoots_nodup; eauto.
   - apply Rplus_le_compat_l. apply Clistsum_mod. }
 destruct (large_enough_exponent' ratio (c/c_rest)) as (N' & HN'); trivial.
 { apply Rdiv_lt_0_compat; trivial. }
 destruct (Cr (max N N')) as (n & Hn & LTn).
 exists n. split; try lia.
 rewrite <- (re_RtoC (_-_)), (Equation_dA k _ roots_ok); trivial; try lia.
 assert (roots_eq : roots = roots@0 :: r :: Cconj r :: skipn 3 roots).
 { rewrite <- E.
   now do 3 (destruct roots; unfold Cnth in *; simpl in *; try lia). }
 rewrite roots_eq. clear Cr E.
 set (f := fun r => _).
 cbn -[skipn Re]. change (fold_right _ _) with Clistsum. unfold f at 1 2.
 rewrite coefdA_conj.
 fold d.
 rewrite <- Cpow_conj, <- Cconj_mult_distr, Cplus_assoc, !re_plus.
 rewrite re_conj, <- double.
 eapply Rle_lt_trans;
   [eapply Rplus_le_compat_l, Rle_trans; [apply Rle_abs | apply re_le_Cmod] | ].
 apply Rlt_minus_r.
 rewrite <- (polar_eqn d). fold rho.
 rewrite <- (polar_eqn r) at 1. fold theta. rewrite Cpow_mul_l, Cexp_pow.
 replace (_ * _ * _)
  with (Cmod d * Cmod r ^ n * (Cexp rho * Cexp (theta * n))) by ring.
 rewrite <- Cexp_add.
 rewrite <- Cmult_assoc, RtoC_pow, !re_scal_l, <- Rmult_assoc.
 unfold Cexp, Re. simpl fst.
 rewrite (Rplus_comm rho).
 apply Rle_lt_trans with (-(2 * c * Cmod r ^ n))%R.
 { unfold c.
   rewrite !Rmult_assoc, (Rmult_comm (1/2)), <- !Rmult_assoc.
   rewrite Ropp_mult_distr_r.
   apply Rmult_le_compat_l; try lra.
   repeat apply Rmult_le_pos; try lra; try apply pow_le; apply Cmod_ge_0. }
 clear theta rho LTn.
 assert (Cmod (Clistsum (map f (skipn 3 roots))) < c * Cmod r ^n); try lra.
 eapply Rle_lt_trans; [apply Clistsum_mod|]. rewrite map_map. unfold f.
 eapply Rle_lt_trans; [apply Rlistsum_le
                       with (g:=(fun x => ratio^n * Cmod (coefdA k x * r ^ n))%R)|].
 { intros a Ha. unfold ratio. rewrite !Cmod_mult.
   destruct (In_nth _ _ 0 Ha) as (m & Hm & <-).
   replace (nth m (skipn 3 roots) 0) with (roots@(3+m))
    by now rewrite roots_eq at 1.
   rewrite skipn_length in Hm.
   specialize (LE (3+m)%nat lia).
   set (rm := roots@(3+m)) in *.
   set (dm := coefdA k rm). unfold Rdiv.
   rewrite Rpow_mult_distr, pow_inv, !Cmod_pow. field_simplify.
   2:{ apply pow_nonzero. intros E. now apply Cmod_eq_0 in E. }
   apply Rmult_le_compat_l. apply Cmod_ge_0. apply pow_incr; split; trivial.
   apply Cmod_ge_0. }
 { clearbody c. clear roots_eq f len roots_ok K LE.
   rewrite map_ext
     with (g:=(fun x => Cmod (coefdA k x) * (ratio^n * Cmod (r^n)))%R).
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
(* Print Assumptions dA_expo'. *)

(** ** Appendix *)

(** The coefB coefficient used above corresponds to a B sequence,
    variant of the sequence A, with different initial values
    and hence shifted. This B sequence used to be important when using
    Vandermonde matrices, but it is far less crucial now. *)

Fixpoint B (k n : nat) :=
  match n with
  | 0 => 1-(k-1)
  | S n => B k n + B k (n-(k-1)) + if S n =? k-1 then 1 else 0
  end%nat.

Lemma B_zero k n : (n < k-1)%nat -> B k n = 0%nat.
Proof.
 induction n as [ [|n] IH] using lt_wf_ind.
 - now destruct k as [|[|k]].
 - intros H. simpl. rewrite !IH by lia.
   destruct k as [|[|k]]; simpl; trivial. case Nat.eqb_spec; lia.
Qed.

Lemma B_one k n : (k-1 <= n < 2*k-1)%nat -> B k n = 1%nat.
Proof.
 induction n as [ [|n] IH] using lt_wf_ind; intros H.
 - simpl. now replace (k-1)%nat with 0%nat by lia.
 - simpl.
   destruct (Nat.le_gt_cases (k-1) n).
   + rewrite IH by lia.
     rewrite B_zero by lia.
     destruct k as [|[|k]]; simpl; trivial. case Nat.eqb_spec; lia.
   + rewrite !B_zero by lia.
     destruct k as [|[|k]]; simpl; trivial; try lia. case Nat.eqb_spec; lia.
Qed.

Lemma A_B k n : A k n = B k (n+2*(k-1)).
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { induction n; trivial. simpl.
   rewrite !Nat.add_0_r, !Nat.sub_0_r in *. lia. }
 induction n as [ [|n] IH] using lt_wf_ind.
 - rewrite B_one; simpl; trivial. lia.
 - cbn -["=?"]. rewrite !IH by lia.
   case Nat.eqb_spec; try lia. intros _. rewrite Nat.add_0_r. f_equal.
   destruct (Nat.lt_ge_cases n (k-1)).
   + rewrite !B_one; lia.
   + f_equal. lia.
Qed.

Lemma Amk_B k roots : SortedRoots k roots -> (1<k)%nat ->
  forall p, Amk k roots p = B k (p+k-2).
Proof.
 intros roots_ok K' p.
 destruct (Nat.eq_dec p 0) as [->|Hp].
 - rewrite Amk0_is_0 by trivial. rewrite B_zero. easy. lia.
 - destruct (Nat.lt_ge_cases p k).
   + rewrite B_one by lia. simpl. apply Amk_is_1; trivial; lia.
   + replace p with (k + (p-k))%nat at 1 by lia.
     rewrite Amk_A, A_B; trivial. do 3 f_equal. lia.
Qed.

Lemma Equation_B k roots : SortedRoots k roots ->
  forall n, RtoC (B k n) = Clistsum (map (fun r => coefB k r * r^n) roots).
Proof.
 intros roots_ok n.
 assert (K : (k<>0)%nat).
 { intros ->. apply (SortedRoots_nz _ roots_ok). }
 destruct (Nat.eq_dec k 1) as [->|K'].
 - replace (B 1 n) with (A 1 n). 2:{ rewrite A_B. f_equal; lia. }
   rewrite (Equation_A _ _ roots_ok). f_equal. apply map_ext_in.
   intros r Hr. unfold coefA, coefB. simpl.
   unfold Cdiv. now rewrite Cinv_1.
 - destruct (Nat.lt_ge_cases n (k-2)).
   + rewrite B_zero by lia. simpl.
     replace (Clistsum _)
       with (Amk k roots (n+2) - Amk k roots (n+1)).
     * rewrite !Amk_is_1; trivial; try lia. lca.
     * unfold Amk. rewrite Clistsum_minus.
       f_equal. apply map_ext_in. intros r Hr.
       unfold coefB.
       unfold Cdiv, Cminus.
       rewrite Copp_mult_distr_l, <- Cmult_plus_distr_r.
       rewrite (Cmult_comm _ (r^n)), Cmult_assoc. f_equal.
       assert (r^(k-1) <> 0).
       { apply Cpow_nonzero. intros ->.
         now apply (SortedRoots_roots _ _ roots_ok), root_nz in Hr. }
       apply Cmult_eq_reg_l with (r^(k-1)); trivial.
       field_simplify; trivial.
       rewrite Nat.add_succ_r, Cpow_S, Cmult_assoc, !(Cmult_comm _ r).
       rewrite <- !Cpow_S. fixpred.
       apply (SortedRoots_roots _ _ roots_ok), ThePoly_root_carac in Hr.
       rewrite Hr, Nat.add_1_r. ring.
   + replace n with ((n-(k-2))+k-2)%nat at 1 by lia.
     rewrite <- (Amk_B k roots) by (trivial; lia).
     unfold Amk. f_equal. apply map_ext_in.
     intros r Hr. unfold coefB.
     unfold Cdiv. rewrite (Cmult_comm _ (r^n)), Cmult_assoc. f_equal.
     assert (r^(k-1) <> 0).
     { apply Cpow_nonzero. intros ->.
       now apply (SortedRoots_roots _ _ roots_ok), root_nz in Hr. }
     apply Cmult_eq_reg_l with (r^(k-1)); trivial.
     field_simplify; trivial.
     rewrite (Cmult_comm _ r), <- Cpow_S, <- Cpow_add_r. f_equal; lia.
Qed.

(** Conjecture (TODO?) : A former approach was to consider the
    Vandermonde matrix of the roots. The square of the determinant
    of this Vandermonde matrix seems to be [+/-(k^k+(k-1)^(k-1))].
    For instance +5 for k=2, -31 for k=3, -283 for k=4, +3381 for k=5
    See OEIS A056788.
    At least, this square is clearly an integer, since it's a symmetric
    polynomial of the roots (determinant is alternating) with coefficients
    in Z, hence it is a Z polynomial of the elementary symmetric polynomials
    that here are -1 or 0 or 1 (coefficients of ThePoly). *)
