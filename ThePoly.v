From Coq Require Import Reals Lra Lia.
From QuantumLib Require Import Complex Polynomial.
Require Import Lim MorePolynomial.
Local Open Scope C.
Local Coercion INR : nat >-> R.

Definition ThePoly (k:nat) : Polynomial :=
 monom C1 (k+1) +, monom (-C1) k +, [-C1].

Lemma mu_is_root k : Root (mu k) (ThePoly k).
Proof.
 unfold ThePoly, Root. rewrite !Pplus_eval, !monom_eval. cbn.
 rewrite Nat.add_1_r, !RtoC_pow, mu_carac, !RtoC_plus. lca.
Qed.

Lemma ThePoly_subdeg k : (degree (monom (-C1) k +, [-C1]) <= k)%nat.
Proof.
 etransitivity; [apply Pplus_degree1| ].
 rewrite monom_degree. 2:apply Copp_neq_0_compat, C1_neq_C0.
 generalize (degree_length [-C1]). simpl. lia.
Qed.

Lemma ThePoly_deg k : degree (ThePoly k) = S k.
Proof.
 unfold ThePoly.
 rewrite Pplus_assoc, Pplus_comm.
 rewrite Pplus_degree2.
 rewrite monom_degree. lia. apply C1_neq_C0.
 rewrite monom_degree. 2:apply C1_neq_C0.
 generalize (ThePoly_subdeg k). lia.
Qed.

Lemma topcoef_monom c k : topcoef (monom c k) = c.
Proof.
 destruct (Ceq_dec c 0); subst.
 - unfold monom, topcoef.
   rewrite app_C0_compactify_reduce_1.
   change (repeat C0 k) with ([]++repeat C0 k).
   now rewrite app_C0_compactify_reduce.
 - unfold topcoef. rewrite compactify_monom; auto.
   unfold monom. apply last_last.
Qed.

Lemma ThePoly_monic (k:nat) : monic (ThePoly k).
Proof.
 unfold ThePoly. rewrite Pplus_assoc, Pplus_comm. unfold monic.
 rewrite topcoef_plus_ltdeg. apply topcoef_monom.
 rewrite monom_degree. 2:apply C1_neq_C0.
 generalize (ThePoly_subdeg k). lia.
Qed.

Lemma map_repeat {A B}(f : A -> B) a n :
 map f (repeat a n) = repeat (f a) n.
Proof.
 induction n; simpl; f_equal; auto.
Qed.

Lemma monom_scale c k : monom c k ≅ [c] *, monom C1 k.
Proof.
 unfold monom. rewrite Pscale_alt, map_app. simpl.
 apply Peq_iff. f_equal. f_equal.
 now rewrite map_repeat, Cmult_0_r.
 f_equal. lca.
Qed.

Definition _X_ := [C0;C1].

Lemma Pmult_X (p:Polynomial) : _X_ *, p ≅ C0::p.
Proof.
 simpl.
 rewrite <- Pscale_alt.
 rewrite Pzero_alt. simpl. rewrite Pplus_0_r.
 rewrite <- Pscale_alt.
 now rewrite Pmult_1_l.
Qed.

Lemma ThePoly_diff k : k<>O ->
 Pdiff (ThePoly k) ≅ [-k; k+1] *, monom C1 (k-1).
Proof.
 intros Hk.
 unfold ThePoly.
 rewrite !Pdiff_plus, !diff_monom.
 replace (pred (k+1)) with (S (k-1)) by lia.
 replace (pred k) with (k-1)%nat by lia.
 simpl Pdiff. rewrite Pzero_alt, Pplus_0_r.
 rewrite monom_S.
 rewrite (monom_scale (-C1)), <- Pmult_assoc.
 replace ([RtoC k] *, [-C1]) with [-RtoC k].
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

(* TODO: QuantumLib.Complex.Cpow_nonzero is buggy (only on reals) *)
Lemma Cpow_nz (c : C) n : c <> 0 -> c ^ n <> 0.
Proof.
 induction n; simpl; intro H.
 - injection. apply R1_neq_R0.
 - apply Cmult_neq_0; auto.
Qed.

Lemma ThePoly_no_common_root_with_diff k c :
  Root c (ThePoly k) -> ~ Root c (Pdiff (ThePoly k)).
Proof.
 intros Hc.
 destruct (Nat.eq_dec k 0) as [->|Hk].
 - rewrite ThePoly_diff_0. unfold Root. cbn. rewrite Cmult_1_l, Cplus_0_l.
   apply C1_neq_C0.
 - rewrite ThePoly_diff by trivial.
   unfold Root.
   rewrite Pmult_eval, monom_eval. cbn.
   rewrite !Cmult_1_r, Cmult_1_l, Cplus_0_l. intro E.
   apply Cmult_integral in E. destruct E as [E|E].
   + rewrite Cplus_comm in E. apply Cminus_eq in E.
     assert (Hc' : c = (INR k / INR (S k))%C).
     { rewrite <- E. rewrite <- RtoC_plus, <- S_INR. field.
       intros H'. apply RtoC_inj in H'. generalize (RSpos k). lra. }
     rewrite <- RtoC_div in Hc'. 2:generalize (RSpos k); lra.
     revert Hc.
     unfold ThePoly, Root.
     rewrite !Pplus_eval, !monom_eval. cbn.
     rewrite <- !Copp_mult_distr_l.
     rewrite !Cmult_1_l, Cplus_0_l.
     rewrite Nat.add_1_r.
     change (c^S k - c^k - 1 <> 0)%C.
     replace (c^S k - c^k - 1)%C with (c^S k - (c^k + 1))%C by ring.
     apply Cminus_eq_contra. intro Hc.
     set (r := Rdiv _ _) in *.
     assert (r <= 1).
     { unfold r. apply Rcomplements.Rle_div_l.
       generalize (RSpos k); lra. rewrite S_INR; lra. }
     subst c. rewrite !RtoC_pow, <- RtoC_plus in Hc.
     apply RtoC_inj in Hc.
     apply mu_unique in Hc. generalize (mu_itvl k); lra.
     apply Rcomplements.Rdiv_le_0_compat. apply pos_INR. apply RSpos.
   + revert E.
     apply Cpow_nz.
     contradict Hc. subst c.
     unfold ThePoly, Root.
     rewrite !Pplus_eval, !monom_eval. cbn.
     destruct k; try lia. simpl.
     rewrite !Cmult_0_l, !Cmult_0_r, !Cplus_0_l, Cmult_1_r.
     apply Copp_neq_0_compat, C1_neq_C0.
Qed.

Lemma ThePoly_separated_roots k :
  exists l, length l = S k /\ NoDup l /\ ThePoly k ≅ linfactors l.
Proof.
 destruct (separated_roots (ThePoly k)) as (l & D & E).
 - apply ThePoly_monic.
 - apply ThePoly_no_common_root_with_diff.
 - exists l; repeat split; auto.
   rewrite <- linfactors_degree. now rewrite <- E, ThePoly_deg.
Qed.
