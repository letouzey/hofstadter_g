From Coq Require Import Reals Lra Lia.
From CoRN Require Import FTA Rreals Rreals_iso CRings.
From Coquelicot Require Import Complex.
Require Import Lim ClassicFTA.

Local Open Scope R.

Add Search Blacklist "RefLemma" "TaylorLemma" "RefSeparated" "_lemma".

Definition ThePoly (k:nat) : CX := monom [1] (k+1) [-] monom [1] k [-] [1].

Lemma mu_is_root (k:nat) : CXRoot (mu k) (ThePoly k).
Proof.
 unfold ThePoly, CXRoot. rewrite !minus_apply, !monom_apply. simpl.
 unfold "[-]". simpl.
 rewrite Nat.add_1_r. ring_simplify.
 rewrite <- RtoC_pow, mu_carac. rewrite RtoC_plus, RtoC_pow. ring.
Qed.

Lemma ThePoly_deg (k:nat) : degree (S k) (ThePoly k).
Proof.
 unfold ThePoly.
 apply degree_minus_lft with O; auto with *.
 - red. simpl. destruct m. inversion 1. trivial.
 - apply degree_minus_lft with k; auto with *.
   apply monom_degree.
   rewrite Nat.add_1_r.
   apply monom_degree_eq. apply C1_nz.
Qed.

Lemma ThePoly_monic (k:nat) : monic (S k) (ThePoly k).
Proof.
 unfold ThePoly. apply monic_minus with O; auto with *.
 - red. simpl. destruct m. inversion 1. trivial.
 - apply monic_minus with k; auto with *.
   apply monom_degree.
   rewrite Nat.add_1_r. split.
   now rewrite monom_coeff.
   apply monom_degree.
Qed.

Lemma ThePoly_nonConst (k:nat) : nonConst _ (ThePoly k).
Proof.
 apply monic_nonConst with k. apply ThePoly_monic.
Qed.

Lemma ThePoly_diff k : k<>O ->
 _D_ (ThePoly k) [=]
 (nring (S k) [*] _X_ [-] nring k) [*] monom [1] (pred k).
Proof.
 intros Hk.
 unfold ThePoly.
 rewrite !diff_minus, diff_one, !diff_monom.
 rewrite Nat.add_1_r. simpl pred.
 rewrite cg_inv_zero.
 replace k with (S (pred k)) at 2 by lia.
 rewrite monom_S. rewrite mult_assoc. algebra.
Qed.

Lemma ThePoly_diff_0 : _D_ (ThePoly 0) [=] [1].
Proof.
 unfold ThePoly. simpl. repeat split; trivial. now ring_simplify.
Qed.

Lemma ThePoly_no_common_root_with_diff k c :
  CXRoot c (ThePoly k) -> ~ CXRoot c (_D_ (ThePoly k)).
Proof.
 intros Hc.
 destruct (Nat.eq_dec k 0) as [->|Hk].
 - rewrite ThePoly_diff_0. unfold CXRoot. rewrite one_apply. apply C1_nz.
 - rewrite ThePoly_diff by trivial.
   unfold CXRoot.
   rewrite mult_apply, !monom_apply, minus_apply, mult_apply, x_apply.
   rewrite !nring_CX, !c_apply.
   apply Cmult_neq_0.
   + change (INR (S k) * c - INR k <> 0)%C.
     apply Cminus_eq_contra. intros H.
     assert (Hc' : c = (INR k / INR (S k))%C).
     { rewrite <- H. field. intros H'. apply RtoC_inj in H'.
       generalize (RSpos k). lra. }
     rewrite <- RtoC_div in Hc'. 2:generalize (RSpos k); lra.
     revert Hc.
     unfold ThePoly, CXRoot.
     rewrite !minus_apply, one_apply, !monom_apply.
     change [1] with (RtoC 1). rewrite !Cmult_1_l.
     rewrite Nat.add_1_r.
     change (c^S k - c^k - 1 <> 0)%C.
     replace (c^S k - c^k - 1)%C with (c^S k - (c^k + 1))%C by ring.
     apply Cminus_eq_contra. intro Hc.
     set (r := Rdiv _ _) in *.
     assert (r <= 1).
     { unfold r. apply Rcomplements.Rle_div_l.
       generalize (RSpos k); lra. rewrite S_INR; lra. }
     subst c. rewrite <- !RtoC_pow, <- RtoC_plus in Hc.
     apply RtoC_inj in Hc.
     apply mu_unique in Hc. generalize (mu_itvl k); lra.
     apply Rcomplements.Rdiv_le_0_compat. apply pos_INR. apply RSpos.
   + change (1 * c ^ pred k <> 0)%C.
     rewrite Cmult_1_l.
     apply Cpow_nz.
     contradict Hc. subst c.
     unfold ThePoly, CXRoot.
     rewrite !minus_apply, one_apply, !monom_apply.
     destruct k; try lia.
     simpl. rewrite !Cmult_0_l, !Cmult_0_r.
     apply Cminus_eq_contra.
     change (0-0 <> 1)%C. unfold Cminus. rewrite Cplus_opp_r.
     intro H. symmetry in H. now apply C1_nz.
Qed.

Lemma ThePoly_separated_roots k :
  { l | length l = S k /\ NoDup l /\ ThePoly k [=] linprod l }.
Proof.
 apply (separated_roots (S k) (ThePoly k) (ThePoly_monic k)).
 apply ThePoly_no_common_root_with_diff.
Qed.



(* liens : https://github.com/coq-community/awesome-coq

   https://valentinblot.org/pro/M1_report.pdf : Cayley-Hamilton, Liouville,
   etc
*)
