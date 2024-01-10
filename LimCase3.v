From Coq Require Import Bool Arith Lia QArith Reals Lra Qreals.
From QuantumLib Require Import Complex Polynomial Matrix.
Require Import MoreFun MoreList MoreReals MoreComplex.
Require Import MoreLim MorePoly MoreMatrix.
Require Import DeltaList GenFib GenG GenAdd Words Mu ThePoly Approx.
Import Permutation.
Local Open Scope Z.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.
Local Set Printing Coercions.

(** * Studying case k=3

   We focus here on the case k=3, compute the complex roots of [X^4-X^3-1],
   and express (A 3 n) in term of combinations of powers of these roots.
   Then we study the frequencies in [Words.kseq 3] and the behaviour of
   function [f 3].
*)

Definition μ := mu 3.
Definition τ := tau 3.
Definition ν := nu 3.

Lemma τ_μ : τ = /μ.
Proof.
 reflexivity.
Qed.

Lemma μ_τ : μ = /τ.
Proof.
 apply tau_inv.
Qed.

Lemma τ4 : τ^4 = 1 - τ.
Proof.
 generalize (tau_carac 3). fold τ. lra.
Qed.

Lemma τ5 : τ^5 = τ - τ^2.
Proof.
 change (τ^5) with (τ*τ^4). rewrite τ4. ring.
Qed.

Lemma τ6 : τ^6 = τ^2 - τ^3.
Proof.
 change (τ^6) with (τ*τ^5). rewrite τ5. ring.
Qed.

Lemma τ3456 : τ^3 + τ^4 + τ^5 + τ^6 = 1.
Proof.
 rewrite τ6, τ5, τ4; ring.
Qed.

#[local] Instance : Approx 0.7244919590005 τ 0.7244919590006.
Proof. red. unfold τ. generalize tau_3. lra. Qed.

#[local] Instance : Approx 1.380277569097 μ 1.380277569098.
Proof. red. unfold μ. generalize mu_3. lra. Qed.

#[local] Instance : Approx (-0.819172513397) ν (-0.819172513396).
Proof. red. unfold ν. generalize nu_3. lra. Qed.

Lemma μ_nz : μ <> 0. Proof. approx. Qed.
Lemma ν_nz : ν <> 0. Proof. approx. Qed.
Lemma τ_nz : τ <> 0. Proof. approx. Qed.

(** The complex roots of [X^4-X^3-1] *)

Definition re_α := (1 - μ - ν)/2.
Definition im_α := sqrt (τ/(-ν)-re_α^2).

Definition α : C := (re_α, im_α).
Definition αbar : C := (re_α, - im_α).

Lemma α_conj : Cconj α = αbar.
Proof. reflexivity. Qed.

Lemma αbar_conj : Cconj αbar = α.
Proof. now rewrite <- (Cconj_involutive α). Qed.

#[local] Instance : Approx 0.2194474721 re_α 0.2194474722.
Proof. unfold re_α. approx. Qed.

#[local] Instance : Approx 0.0481571930 (re_α^2) 0.0481571931.
Proof. approx. Qed.

#[local] Instance : Approx 0.884419273293 (τ/-ν) 0.884419273296.
Proof. approx. Qed.

Lemma im_α_2_pos :  re_α ^ 2 < τ/-ν.
Proof. approx. Qed.

Lemma im_α_2 : im_α^2 = τ/(-ν)-re_α^2.
Proof.
 unfold im_α.
 rewrite pow2_sqrt; generalize im_α_2_pos; lra.
Qed.

Lemma im_α_pos : 0 < im_α.
Proof.
 apply sqrt_lt_R0. generalize im_α_2_pos. lra.
Qed.

Lemma im_α_nz : im_α <> 0.
Proof. generalize im_α_pos; lra. Qed.

#[local] Instance : Approx 0.8362620801 (im_α^2) 0.8362620803.
Proof. rewrite im_α_2. approx. Qed.

#[local] Instance : Approx 0.9144736628 im_α 0.9144736630.
Proof.
 apply pow2_approx_inv. approx. qle. generalize im_α_pos; lra. qle.
Qed.

Lemma αmod2 : Cmod α ^2 = τ/-ν.
Proof.
 rewrite Cmod2_alt. unfold α. simpl Re; simpl Im.
 rewrite im_α_2. lra.
Qed.

#[local] Instance : Approx 0.884419273293 (Cmod α ^2) 0.884419273296.
Proof. rewrite αmod2. approx. Qed.

#[local] Instance : Approx 0.9404356826 (Cmod α) 0.9404356828.
Proof.
 apply pow2_approx_inv; try qle; try apply Cmod_ge_0. approx.
Qed.

Lemma αmod_lt : 0 < Cmod α < 1.
Proof. approx. Qed.

Definition roots3 := [RtoC μ; RtoC ν; α; αbar].

Lemma distinct_roots :
  α <> μ /\ αbar <> μ /\ αbar <> α /\
  α <> ν /\ αbar <> ν /\ ν <> μ.
Proof.
 unfold α, αbar, RtoC; repeat split.
 - intros [= A B]. now destruct im_α_nz.
 - intros [= A B]. generalize im_α_nz. lra.
 - intros [= B]. generalize im_α_nz. lra.
 - intros [= A B]. now destruct im_α_nz.
 - intros [= A B]. generalize im_α_nz. lra.
 - approx.
Qed.

Lemma nodup_roots : NoDup roots3.
Proof.
 destruct distinct_roots as (D1 & D2 & D3 & D4 & D5 & D6).
 assert (RtoC ν <> RtoC μ) by (contradict D6; now apply RtoC_inj).
 repeat constructor; simpl; tauto.
Qed.

Local Hint Rewrite RtoC_pow : RtoC.
Local Hint Rewrite <- RtoC_opp RtoC_plus RtoC_mult RtoC_minus RtoC_inv
 RtoC_div using approx : RtoC.

Lemma ThePoly3_linfactors :
  ThePoly 3 ≅ linfactors roots3.
Proof.
 destruct (ThePoly_separated_roots_mu 3) as (l & Hl & ND & E & Hμ).
 fold μ in Hμ. rewrite E. apply linfactors_perm.
 destruct l as [|a [|b [|c [|d [|? l] ] ] ] ]; try (simpl; easy).
 clear Hl. simpl in Hμ. subst a.
 apply perm_skip.
 assert (In (RtoC ν) [RtoC μ;b;c;d]).
 { apply linfactors_roots. rewrite <- E, ThePoly_root_carac.
   autorewrite with RtoC. f_equal. apply (nu_carac 3).
   now apply Nat.odd_spec. }
 assert (EF : exists e f, Permutation [RtoC ν; e; f] [b;c;d]).
 { simpl in H. destruct H.
   + exfalso. apply RtoC_inj in H. revert H. approx.
   + repeat destruct H; try easy; subst.
     * now exists c, d.
     * exists b, d. apply perm_swap.
     * exists b, c. apply perm_trans with [b;d;c].
       apply perm_swap. apply perm_skip, perm_swap. }
 destruct EF as (e & f & EF). rewrite <- EF. apply perm_skip.
 assert (EF' : Permutation [RtoC μ; b;c;d] [RtoC μ;RtoC ν; e; f]).
 { now apply perm_skip. }
 rewrite (linfactors_perm _ _ EF') in E.
 apply (Permutation_NoDup EF') in ND. clear H EF EF'.
 assert (He : Root e (ThePoly 3)).
 { rewrite E. apply linfactors_roots. simpl; auto. }
 assert (He' : Root (Cconj e) (ThePoly 3)).
 { rewrite ThePoly_root_carac in *. rewrite <- !Cpow_conj, He. lca. }
 rewrite E in He'. apply linfactors_roots in He'.
 assert (f = Cconj e).
 { simpl in He'; destruct He' as [H|[H|[H|[H|H] ] ] ];
   trivial; exfalso; trivial.
   - clear E. rewrite <- Cconj_R in H. apply Cconj_simplify in H.
     subst. inversion_clear ND. simpl in *. tauto.
   - clear E. rewrite <- Cconj_R in H. apply Cconj_simplify in H.
     subst. inversion_clear ND. inversion_clear H0. simpl in *; tauto.
   - destruct e as (x,y). unfold Cconj in H. simpl in H.
     injection H as H. replace y with 0 in * by lra. clear H.
     rewrite ThePoly_root_carac in He.
     replace (x,0) with (RtoC x) in * by trivial.
     autorewrite with RtoC in He. apply RtoC_inj in He.
     rewrite <- (P_root_equiv 3) in He.
     apply mu_or_nu in He. 2:now apply Nat.odd_spec.
     change (x = μ \/ x = ν) in He.
     destruct He as [-> | ->]; inversion_clear ND.
     + simpl in H; tauto.
     + inversion_clear H0. simpl in H1; tauto. }
 subst f. clear He' ND.
 assert (E0 := coef_compat 0 _ _ E).
 assert (E3 := coef_compat 3 _ _ E).
 unfold ThePoly,coef in E0,E3; simpl in E0,E3.
 ring_simplify in E0. field_simplify in E3.
 assert (E3' : (RtoC μ + RtoC ν + e + Cconj e = 1)%C).
 { rewrite Ceq_minus in E3. ring_simplify in E3.
   replace (RtoC (-1)) with (-(1))%C in E3 by lca.
   apply Ceq_minus in E3. rewrite <- E3. lca. }
 clear E E3 He.
 assert (Hx : Re e = re_α).
 { apply RtoC_inj. rewrite re_alt.
   replace (e+Cconj e)%C with (1-μ-ν)%C by (rewrite <- E3'; lca).
   unfold re_α. lca. }
 assert (Hm : Cmod e ^2 = Cmod α ^2).
 { apply RtoC_inj.
   rewrite αmod2, <- RtoC_pow, Cmod_sqr.
   replace (τ/-ν) with ((-1)*(τ/ν)) by (field; approx).
   rewrite RtoC_mult, RtoC_div by approx.
   rewrite E0, τ_μ, RtoC_inv by approx. field.
   split; apply RtoC_neq; approx. }
 assert (Hy : (Im e)^2 = im_α^2).
 { rewrite !Cmod2_alt, Hx in Hm. unfold α in Hm; simpl in Hm; lra. }
 clear E0 E3' Hm.
 rewrite <- !Rsqr_pow2 in Hy.
 apply Rsqr_eq in Hy.
 destruct Hy as [Hy|Hy]; destruct e as (x,y);
  unfold Cconj, αbar, α in *; simpl in *; subst;
  rewrite ?Ropp_involutive; apply perm_swap || reflexivity.
Qed.

Lemma μ_is_Rroot : μ^4 = μ^3 + 1.
Proof.
 exact (mu_carac 3).
Qed.

Lemma μ_is_Croot : (μ^4 = μ^3 + 1)%C.
Proof.
 autorewrite with RtoC. f_equal. apply μ_is_Rroot.
Qed.

Lemma ν_is_Rroot : ν^4 = ν^3+1.
Proof.
 apply nu_carac. now apply Nat.odd_spec.
Qed.

Lemma ν_is_Croot : (ν ^4 = ν ^3 + 1)%C.
Proof.
 autorewrite with RtoC. f_equal. apply ν_is_Rroot.
Qed.

Lemma α_is_Croot : (α^4 = α^3 + 1)%C.
Proof.
 rewrite <- ThePoly_root_carac, ThePoly3_linfactors.
 apply linfactors_roots. simpl. tauto.
Qed.

Lemma αbar_is_Croot : (αbar^4 = αbar^3 + 1)%C.
Proof.
 rewrite <- ThePoly_root_carac, ThePoly3_linfactors.
 apply linfactors_roots. simpl. tauto.
Qed.

Lemma A3_eqn_exists :
 exists (a b c d:C),
 forall n, RtoC (A 3 n) = (a*μ^n + b*ν^n + c*α^n + d*αbar^n)%C.
Proof.
 destruct (coefs_LinCombA 3 roots3) as (v & H).
 - reflexivity.
 - apply nodup_roots.
 - apply ThePoly3_linfactors.
 - exists (v O O), (v 1 O)%nat, (v 2 O)%nat, (v 3 O)%nat.
   intros n. rewrite <- H. unfold roots3. simpl.
   rewrite scalprod_alt. cbn -[nu]. ring.
Qed.

(** Note about A3_eqn_exists : if someday precise estimates of coefficients
    a b c d are needed, they can be obtained by inversing the Vandermonde
    matrix of roots3. And if we just need that a is real and >=1, then
    see Freq.A_gt_mu_pow. *)

(** ** Occurrences of letters in morphic word [Words.kseq 3]

    We will see below how this relates to function [f 3])
    and its iterates.

    For a finite word [w], the frequency of letter [a] is
    [nbocc a w / length w]. For infinite words, the frequency
    of a letter (if it exists) is the limit of frequencies for
    ever-growing finite prefixes of the infinite word.

    Here for [Words.kseq 3], the frequencies of letters [0],[1],[2],[3]
    will be respectively [τ^4],[τ^5],[τ^6],[τ^3]
    (another numbering of letters would make that more uniform).
    For proving that and even more, we now consider the following
    differences :
*)

Definition Diff0 w := τ^4 * length w - nbocc 0 w.
Definition Diff1 w := τ^5 * length w - nbocc 1 w.
Definition Diff2 w := τ^6 * length w - nbocc 2 w.
Definition Diff3 w := τ^3 * length w - nbocc 3 w.

Definition diff0 n := Diff0 (take n (kseq 3)).
Definition diff1 n := Diff1 (take n (kseq 3)).
Definition diff2 n := Diff2 (take n (kseq 3)).
Definition diff3 n := Diff3 (take n (kseq 3)).

(** One of these differences can be deduced from the other three. *)

Lemma Diff0123 w :
 List.Forall (fun a => a <= 3)%nat w ->
 Diff0 w + Diff1 w + Diff2 w + Diff3 w = 0.
Proof.
 intros H.
 apply nbocc_total_le in H. simpl in H.
 unfold Diff0, Diff1, Diff2, Diff3.
 rewrite τ4, τ5, τ6. ring_simplify.
 rewrite H, !plus_INR. change (INR 0) with 0. ring.
Qed.

Lemma diff0123 n : diff0 n + diff1 n + diff2 n + diff3 n = 0.
Proof.
 apply Diff0123.
 apply Forall_nth. intros i d. rewrite take_length. intros H.
 rewrite take_nth by trivial. apply kseq_letters.
Qed.

(** Expressing diff0 and co in terms of
    [f 3] and [f 3^^2] and [f 3^^3] *)

Lemma diff0_alt n : diff0 n = f 3 n - τ * n.
Proof.
 unfold diff0, Diff0. rewrite take_length.
 rewrite <- count_nbocc.
 rewrite τ4. rewrite Rmult_minus_distr_r.
 rewrite <- (f_count_0 3 n) at 1 by easy. rewrite plus_INR. lra.
Qed.

Lemma diff3_alt n : diff3 n = τ^3 * n - (f 3^^3) n.
Proof.
 unfold diff3, Diff3. rewrite take_length.
 rewrite <- count_nbocc.
 now rewrite fs_count_k.
Qed.

Lemma diff1_alt n : diff1 n = τ^5 * n + (f 3^^2) n - f 3 n.
Proof.
 unfold diff1, Diff1. rewrite take_length.
 rewrite <- count_nbocc.
 change (f 3 n) with ((f 3^^1) n).
 rewrite (fs_count_above 3 1) by lia.
 rewrite count_above_S.
 rewrite (fs_count_above 3 2) by lia.
 rewrite plus_INR. lra.
Qed.

Lemma diff2_alt n : diff2 n = τ^6 * n + (f 3^^3) n - (f 3^^2) n.
Proof.
 unfold diff2, Diff2. rewrite take_length.
 rewrite <- count_nbocc.
 rewrite (fs_count_above 3 2) by lia.
 rewrite (fs_count_above 3 3) by lia.
 rewrite (count_above_S (kseq 3) 2).
 rewrite plus_INR. lra.
Qed.

(** Equations giving Diff0 and co after a substitution [ksubst 3]. *)

Lemma Diff0_ksubst3 w : Diff0 (apply (ksubst 3) w) = τ * Diff3 w.
Proof.
 unfold Diff0, Diff3.
 rewrite len_ksubst, plus_INR.
 destruct (nbocc_ksubst3 w) as (-> & _ & _ & _).
 ring_simplify. unfold Rminus. rewrite Rplus_assoc. f_equal.
 rewrite τ4. lra.
Qed.

Lemma Diff3_ksubst3 w :
  List.Forall (fun a => a <= 3)%nat w ->
  Diff3 (apply (ksubst 3) w) = - τ^3 * Diff3 w - Diff0 w - Diff1 w.
Proof.
 intros H.
 unfold Diff0, Diff1, Diff3.
 rewrite len_ksubst.
 destruct (nbocc_ksubst3 w) as (_ & _ & _ & ->).
 rewrite !plus_INR.
 ring_simplify. rewrite τ6, τ5, τ4. ring_simplify.
 rewrite !len_nbocc_0123 by trivial. rewrite !plus_INR. ring.
Qed.

Lemma Diff1_ksubst3 w :
  List.Forall (fun a => a <= 3)%nat w ->
  Diff1 (apply (ksubst 3) w) = - τ^5 * Diff3 w + Diff0 w.
Proof.
 intros H.
 unfold Diff0, Diff1, Diff3.
 rewrite len_ksubst.
 destruct (nbocc_ksubst3 w) as (_ & -> & _ & _).
 rewrite !plus_INR.
 ring_simplify. replace (τ^8) with ((τ^4)^2) by ring.
 rewrite τ5, τ4. ring_simplify.
 rewrite !len_nbocc_0123 by trivial. rewrite !plus_INR. ring.
Qed.

(** Same, expressed via matrix *)

Definition Diffs w : Vector 3 := mkvectR 3 [Diff3 w; Diff0 w; Diff1 w].
Definition diffs n : Vector 3 := mkvectR 3 [diff3 n; diff0 n; diff1 n].

Definition B : Square 3 :=
 list2D_to_matrix [ [-τ^3;-1%C;-1%C];[RtoC τ;0;0];[-τ^5;1;0] ]%C.

Lemma WF_B : WF_Matrix B.
Proof.
 apply WF_list2D_to_matrix; simpl; intuition; subst; auto.
Qed.

Lemma WF_Diffs w : WF_Matrix (Diffs w).
Proof.
 now apply WF_mkvectR.
Qed.

Lemma WF_diffs n : WF_Matrix (diffs n).
Proof.
 now apply WF_mkvectR.
Qed.

#[local] Hint Resolve WF_B WF_Diffs WF_diffs : wf_db.

Lemma diffs_alt n : diffs n = Diffs (take n (kseq 3)).
Proof.
 reflexivity.
Qed.

Lemma Diffs_ksubst3 w :
  List.Forall (fun a => a <= 3)%nat w ->
  Diffs (apply (ksubst 3) w) = B × Diffs w.
Proof.
 intro.
 apply Vect3_eq; auto with wf_db;
  unfold Diffs; cbn -[Cpow];
  rewrite ?Diff3_ksubst3, ?Diff0_ksubst3, ?Diff1_ksubst3 by trivial;
  autorewrite with RtoC; f_equal; ring.
Qed.

(* Initial vector of differences *)
Definition V0 : Vector 3 := mkvectR 3 [τ^3-1; τ^4; τ^5].

Lemma WF_V0 : WF_Matrix V0.
Proof. now apply WF_mkvectR. Qed.

#[local] Hint Resolve WF_V0 : wf_db.

(** Hence diffs for (A 3) numbers are given by powers of matrix B *)

Lemma diffs_A3 n :
 diffs (A 3 n) = Mpow B n × V0.
Proof.
 induction n.
 - unfold diffs, diff3, diff0, diff1, Diff3, Diff0, Diff1, V0.
   cbn -[pow Cpow].
   rewrite Mmult_1_l by now apply WF_mkvectR.
   now rewrite !Rmult_1_r, !Rminus_0_r.
 - rewrite diffs_alt, kseq_take_A, kword_S, Diffs_ksubst3, IHn in *
    by (apply kword_letters).
   simpl. now rewrite Mmult_assoc.
Qed.

Definition U : Square 3 :=
 list2D_to_matrix [ [-α^2;α+1;α];
                    [-αbar^2;αbar+1; αbar];
                    [-ν^2;ν+1;RtoC ν] ]%C.

Definition D : Square 3 :=
 list2D_to_matrix [ [α;0;0]; [0;αbar;0]; [0;0;RtoC ν] ]%C.

Definition Dn n : Square 3 :=
 list2D_to_matrix [ [α^n;0;0]; [0;αbar^n;0]; [0;0;RtoC ν ^n] ]%C.

Lemma WF_U : WF_Matrix U.
Proof.
 apply WF_list2D_to_matrix; simpl; intuition; subst; auto.
Qed.

Lemma WF_D : WF_Matrix D.
Proof.
 apply WF_list2D_to_matrix; simpl; intuition; subst; auto.
Qed.

Lemma WF_Dn n : WF_Matrix (Dn n).
Proof.
 apply WF_list2D_to_matrix; simpl; intuition; subst; auto.
Qed.

#[local] Hint Resolve WF_U WF_D WF_Dn : wf_db.

Lemma P_factor_μ (x:C) :
 (x^4-x^3-1 = (x - μ) * (x^3 + τ^3*x^2 + τ^2*x + τ))%C.
Proof.
 ring_simplify. rewrite μ_τ, RtoC_inv by approx.
 field_simplify; try (apply RtoC_neq; approx).
 rewrite RtoC_pow, τ4, RtoC_minus.
 field. apply RtoC_neq; approx.
Qed.

Lemma P_factor_μ_eq0 (x:C) :
  x<>μ -> (x^4 = x^3+1)%C -> (x^3 + τ^3*x^2 + τ^2*x + τ = 0)%C.
Proof.
 intros Hx E.
 rewrite Ceq_minus in E.
 replace (_-_)%C with (x^4-x^3-1)%C in E by ring.
 rewrite P_factor_μ in E. apply Cmult_integral in E.
 destruct E as [E|E]; trivial. now rewrite <- Ceq_minus in E.
Qed.

(* Finally unused, but may someday : symmetry for <> in goal
Ltac sym_not :=
 let H := fresh in
 match goal with |- ?x <> ?y =>
  intro H; symmetry in H; revert H; change (y <> x)
 end.
*)

Lemma UB_DU : U×B = D×U.
Proof.
 apply Mat3_eq; auto with wf_db; unfold U, B, D; cbn -[nu pow Cpow];
  rewrite !Cplus_0_l; try ring;
  rewrite Ceq_minus; ring_simplify;
  rewrite !(RtoC_pow τ), τ5, RtoC_minus, <- !RtoC_pow; ring_simplify.
 - rewrite <- (P_factor_μ_eq0 α);
    [ ring | apply distinct_roots | apply α_is_Croot].
 - rewrite <- (P_factor_μ_eq0 αbar);
    [ ring | apply distinct_roots | apply αbar_is_Croot].
 - rewrite <- (P_factor_μ_eq0 ν);
    [ ring | apply RtoC_inj_neq, distinct_roots | apply ν_is_Croot].
Qed.

Definition detU := ((α-αbar)*ν^2+(αbar^2-α^2)*ν+α*αbar*(α-αbar))%C.

Lemma detU_alt :
 detU = (2*im_α*Ci*(Cmod α ^2+ν^2+2*(-ν)*re_α))%C.
Proof.
 unfold detU. rewrite <- α_conj, im_alt'.
 rewrite <- Cmod2_conj, conj2_minus_pow2, <- !RtoC_pow.
 replace (RtoC (-4)) with (-(4))%C by lca.
 change (Re α) with re_α.
 change (Im α) with im_α. ring.
Qed.

Lemma detU_conj : Cconj detU = Copp detU.
Proof.
 rewrite detU_alt, !Cconj_mult_distr, Cconj_R, Ci_conj, Cconj_R.
 rewrite !Cconj_plus_distr, !Cconj_mult_distr, Cconj_opp,
  !Cpow_conj, !Cconj_R. ring.
Qed.

Lemma detU_nz : detU <> 0.
Proof.
 rewrite detU_alt. intros E. rewrite !Cmult_integral in E.
 repeat destruct E as [E|E]; try apply RtoC_inj in E; try lra.
 - now apply im_α_nz.
 - compute in E. injection E; lra.
 - autorewrite with RtoC in E. apply RtoC_inj in E. revert E. approx.
Qed.

Definition invU_detU : Square 3 :=
 list2D_to_matrix
  [ [ ν-αbar; -(ν-α); αbar-α];
    [-αbar*ν*(ν-αbar); α*ν*(ν-α);
       -α*αbar*(αbar-α)];
    [(ν-αbar)*(αbar*ν+ν+αbar);
       -(ν-α)*(α*ν+ν+α);
       (αbar-α)*(α*αbar+αbar+α)] ]%C.

Definition invU := /detU .* invU_detU.

Lemma WF_invU_detU : WF_Matrix invU_detU.
Proof.
 apply WF_list2D_to_matrix; simpl; intuition; subst; auto.
Qed.

Lemma WF_invU : WF_Matrix invU.
Proof.
 apply WF_scale, WF_invU_detU.
Qed.

#[local] Hint Resolve WF_invU_detU WF_invU : wf_db.

Lemma invU_detU_U : invU_detU × U = detU .* (I 3).
Proof.
 apply Mat3_eq; auto with wf_db;
  unfold detU, I, scale; cbn -[ν Cpow]; ring.
Qed.

Lemma U_invU_detU : U × invU_detU = detU .* (I 3).
Proof.
 apply Mat3_eq; auto with wf_db;
  unfold detU, I, scale; cbn -[ν Cpow]; ring.
Qed.

Lemma invU_U : invU × U = I 3.
Proof.
 unfold invU.
 rewrite Mscale_mult_dist_l, invU_detU_U.
 rewrite Mscale_assoc.
 replace (/detU * detU)%C with 1%C. apply Mscale_1_l.
 symmetry. apply Cinv_l. apply detU_nz.
Qed.

Lemma U_invU : U × invU = I 3.
Proof.
 unfold invU.
 rewrite Mscale_mult_dist_r, U_invU_detU.
 rewrite Mscale_assoc.
 replace (/detU * detU)%C with 1%C. apply Mscale_1_l.
 symmetry. apply Cinv_l. apply detU_nz.
Qed.

Lemma B_diag : B = invU × D × U.
Proof.
 rewrite Mmult_assoc, <- UB_DU, <- Mmult_assoc, invU_U, Mmult_1_l;
   auto using WF_B.
Qed.

Lemma Dn_0 : Dn 0 = I 3.
Proof.
 apply Mat3_eq; auto with wf_db.
Qed.

Lemma Dn_S n : Dn (S n) = D × Dn n.
Proof.
 apply Mat3_eq; auto with wf_db; unfold Dn, D; cbn -[ν]; ring.
Qed.

Lemma Dn_D n : Mpow D n = Dn n.
Proof.
 induction n; simpl; now rewrite ?Dn_0, ?Dn_S, ?IHn.
Qed.

Lemma Bn_diag n : Mpow B n = invU × Dn n × U.
Proof.
 induction n; simpl.
 - now rewrite Dn_0, Mmult_1_r, invU_U by apply WF_invU.
 - rewrite Dn_S, IHn, B_diag.
   rewrite !Mmult_assoc. f_equal. f_equal.
   now rewrite <- !Mmult_assoc, U_invU, Mmult_1_l by apply WF_Dn.
Qed.

Definition UV0a := (1+α+α^2+α^3)%C.
Definition UV0ν := (1+ν+ν^2+ν^3)%C.
(** possible alternative forms : α^3/(α-1) and ν^3/(ν-1) *)

Definition coefa_detU := ((ν-αbar)*UV0a)%C.
Definition coefν_detU := ((αbar-α)*UV0ν)%C.
Definition vecta := mkvect 3 [1;-ν*αbar;ν*αbar+ν+αbar]%C.
Definition vectν := mkvect 3 [1;-α*αbar;α*αbar+α+αbar]%C.

Definition coefsa := (/detU * coefa_detU) .* vecta.
Definition coefsν := (/detU * coefν_detU) .* vectν.

Local Hint Rewrite Cconj_mult_distr Cconj_plus_distr Cconj_minus_distr
 Cconj_opp Cdiv_conj Cinv_conj Cconj_R Cpow_conj αbar_conj α_conj
 : cconj.

Lemma U_V0_alt : U × V0 = mkvect 3 [UV0a;Cconj UV0a;UV0ν]%C.
Proof.
 apply Vect3_eq; auto with wf_db;
 unfold U, V0, scale; cbn -[ν Cpow pow];
 rewrite τ4, τ5; rewrite !RtoC_minus, <- !RtoC_pow.
 - rewrite <- (P_factor_μ_eq0 α);
   [ | apply distinct_roots | apply α_is_Croot ]. unfold UV0a. ring.
 - rewrite <- (P_factor_μ_eq0 αbar);
   [ | apply distinct_roots | apply αbar_is_Croot ].
   unfold UV0a. autorewrite with cconj. ring.
 - rewrite <- (P_factor_μ_eq0 ν);
   [ | apply RtoC_inj_neq,distinct_roots | apply ν_is_Croot ].
   unfold UV0ν. autorewrite with RtoC. f_equal. ring.
Qed.

(** diffs for (A 3) numbers are linear combinations of little roots *)

Lemma diffs_A3_powers n :
  diffs (A 3 n) =
   (α^n .* coefsa .+ αbar^n .* Mconj coefsa .+ ν^n .* coefsν)%C.
Proof.
 rewrite diffs_A3, Bn_diag.
 unfold invU, coefsa, coefsν.
 rewrite !Mscale_mult_dist_l.
 rewrite Mconj_scale, Cconj_mult_distr, Cinv_conj by apply detU_nz.
 rewrite detU_conj.
 replace (/-detU)%C with (/detU * (-1))%C by (field; apply detU_nz).
 rewrite !Mscale_assoc, !Cmult_assoc, !(Cmult_comm _ (/detU)),
  <-Cmult_assoc, <- !Mscale_assoc, <- !Mscale_plus_distr_r.
 f_equal.
 rewrite Mmult_assoc, U_V0_alt.
 assert (Hva : WF_Matrix vecta) by now apply WF_mkvect.
 assert (Hvν : WF_Matrix vectν) by now apply WF_mkvect.
 apply Vect3_eq; auto 7 with wf_db;
 unfold coefa_detU, coefν_detU, Dn, invU_detU, vecta, vectν;
 unfold scale, Mplus, Mconj; cbn -[ν Cpow pow];
 apply Ceq_minus; autorewrite with cconj; ring.
Qed.

(* In particular for diff0 : *)

Definition coefa0 := coefsa 1%nat 0%nat.
Definition coefν0 := Re (coefsν 1%nat 0%nat).

Lemma vectν_alt :
 vectν = mkvectR 3 [1; -Cmod α^2; Cmod α^2 + 2*re_α].
Proof.
 apply Vect3_eq; try (now apply WF_mkvect); try (now apply WF_mkvectR);
 unfold vectν, mkvectR; rewrite !mkvect_eqn; cbn -[pow]; trivial.
 - rewrite RtoC_opp, Cmod2_conj, α_conj. ring.
 - change re_α with (Re α).
   rewrite RtoC_plus, RtoC_mult, Cmod2_conj, re_alt, α_conj. field.
Qed.

Lemma coefsν_real i : (i < 3)%nat -> Im (coefsν i O) = 0.
Proof.
 assert (E0 : Cconj UV0ν = UV0ν).
 { unfold UV0ν. now autorewrite with cconj. }
 assert (E : Im (/ detU * coefν_detU) = 0).
 { rewrite is_real_carac. autorewrite with cconj; try apply detU_nz.
   rewrite detU_conj.
   unfold coefν_detU. autorewrite with cconj. rewrite E0. field.
   apply detU_nz. }
 unfold coefsν. rewrite vectν_alt;
 intros Hi; destruct i as [|[|[| ] ] ]; try lia; clear Hi;
 unfold scale, mkvectR; rewrite mkvect_eqn; simpl nth;
 rewrite im_scal_r; apply Rmult_eq_0_compat_r; trivial.
Qed.

Lemma diff0_A3_powers n :
  diff0 (A 3 n) = 2 * Re (coefa0 * α^n) + coefν0 * ν^n.
Proof.
  apply RtoC_inj.
  change (RtoC (diff0 (A 3 n))) with (diffs (A 3 n) 1%nat 0%nat).
  rewrite diffs_A3_powers.
  rewrite RtoC_plus, !RtoC_mult, <- !RtoC_pow.
  rewrite re_alt, Cconj_mult_distr, Cpow_conj, α_conj.
  unfold Mplus, Mconj, scale; cbn -[ν Cpow pow Re].
  unfold coefa0, coefν0.
  field_simplify. f_equal. f_equal.
  assert (Im (coefsν 1%nat 0%nat) = 0).
  { apply coefsν_real; lia. }
  destruct coefsν as (x,y). simpl in *. now subst.
Qed.


(** Now, any arbitrary number [n] is a sum of [A 3] numbers by Zeckendorf
    theorem (cf. [GenFib.decomp]). So [diffs n] will be a sum of powers
    of [α], [αbar], [ν]. *)

Lemma Diff0_app u v : Diff0 (u++v) = Diff0 u + Diff0 v.
Proof.
 unfold Diff0.
 rewrite List.app_length, nbocc_app, !plus_INR. lra.
Qed.

Lemma Diff0_concat l : Diff0 (List.concat l) = Rlistsum (List.map Diff0 l).
Proof.
 induction l; simpl; auto.
 - unfold Diff0. simpl. lra.
 - rewrite Diff0_app. lra.
Qed.

Lemma diff0_decomp_eqn n :
  diff0 n =
   Rlistsum (List.map (fun n => 2*Re(coefa0 * α^n)+coefν0*ν^n)
                      (decomp 3 n)).
Proof.
 unfold diff0.
 rewrite decomp_prefix_kseq. unfold kwords. rewrite flat_map_concat_map.
 rewrite Diff0_concat, List.map_map, List.map_rev, Rlistsum_rev.
 f_equal.
 apply List.map_ext; intros.
 rewrite <- kseq_take_A. apply diff0_A3_powers.
Qed.

Lemma diff0_decomp_eqn' n :
  diff0 n =
   2*Re (coefa0 * Clistsum (List.map (Cpow α) (decomp 3 n))) +
   coefν0 * Rlistsum (List.map (pow ν) (decomp 3 n)).
Proof.
 rewrite diff0_decomp_eqn.
 induction decomp.
 - cbn -[Re ν]. rewrite Cmult_0_r. simpl. ring.
 - set (f := fun n => _) in *.
   simpl map. rewrite !Rlistsum_cons, Clistsum_cons.
   rewrite Cmult_plus_distr_l, re_plus, !Rmult_plus_distr_l, IHl.
   unfold f at 1. ring.
Qed.

(** With the previous expression of [diff0 n], we will progressively bound it
    by some constant independent from [n]. *)

Lemma diff0_decomp_le n :
 Rabs (diff0 n) <=
  2 * Cmod coefa0 * Rlistsum (List.map (pow (Cmod α)) (decomp 3 n))
  + Rabs coefν0 * Rlistsum (List.map (pow (Rabs ν)) (decomp 3 n)).
Proof.
 rewrite diff0_decomp_eqn.
 induction decomp.
 - simpl. rewrite Rabs_R0. lra.
 - set (f := fun n => _) in *.
   simpl map. rewrite !Rlistsum_cons.
   rewrite !Rmult_plus_distr_l, Rplus_reorder.
   eapply Rle_trans. apply Rabs_triang.
   apply Rplus_le_compat; [|apply IHl]. clear IHl.
   unfold f at 1.
   eapply Rle_trans. apply Rabs_triang.
   apply Rplus_le_compat.
   + rewrite Rabs_mult. rewrite (Rabs_right 2) by lra.
     rewrite Rmult_assoc. apply Rmult_le_compat_l; try lra.
     rewrite <- Cmod_pow, <-Cmod_mult. apply re_le_Cmod.
   + rewrite Rabs_mult. apply Rmult_le_compat_l. apply Rabs_pos.
     rewrite RPow_abs; lra.
Qed.

Lemma diff0_indep_bound n :
 Rabs (diff0 n) <=
  2 * Cmod coefa0 / (1 - Cmod α^4) + Rabs coefν0 / (1 - ν^4).
Proof.
 eapply Rle_trans. apply diff0_decomp_le.
 unfold Rdiv.
 apply Rplus_le_compat.
 - apply Rmult_le_compat_l.
   + generalize (Cmod_ge_0 coefa0). lra.
   + apply sum_pow; try lia; try apply decomp_delta. approx.
 - apply Rmult_le_compat_l; try apply Rabs_pos.
   replace (ν^4) with (Rabs ν^4) by (rewrite Rabs_left by approx; ring).
   apply sum_pow; try lia; try apply decomp_delta.
   rewrite Rabs_left; approx.
Qed.

(** Experimentally, this first bound is around 2.187.
    Having this finite bound is enough to prove that the frequency
    of letter 0 is [τ^4] and that [f 3 n / n] converges towards τ.
    See Freq.v now for more general results.
    Now, with some more sweat, we prove now a better bound, strictly
    below 2, with nice consequences (not already in Freq.v) :

     - [f 3 n = nat_part (τ*n)+{-1,0,1,2}]
     - [f 3] is quasi-additive:
        [forall n p, -5 <= f 3 (n+p) - f 3 n - f 3 p <= 5]
*)

(* First, the ν part of the bound (easier) *)

Definition max4packν := 1+ν^4+ν^8+ν^12.

#[local] Instance : Approx 1.74437626251 max4packν 1.74437626252.
Proof. unfold max4packν. approx. Qed.

Lemma best_4packν_0 l :
  Delta 4 (O::l) -> Below l 16 ->
  Rabs (Rlistsum (List.map (pow ν) (O::l))) <= max4packν.
Proof.
 intros D B.
 inversion D; subst; cbn -[Cpow pow ν]. rewrite !pow_0_r.
 { rewrite Rplus_0_r, Rabs_right by lra. approx. }
 eapply Rle_trans; [apply Rabs_triang|].
 unfold max4packν. rewrite Rabs_right by lra.
 rewrite !Rplus_assoc. apply Rplus_le_compat_l.
 eapply Rle_trans; [apply Rabs_triang|].
 apply Rplus_le_compat.
 { rewrite <- (Rabs_right (ν^4)) by approx.
   rewrite <- !RPow_abs. apply Rle_pow_le1; try lia. approx. }
 inversion H2; subst; cbn -[Cpow pow ν]; rewrite ?Rabs_R0; try approx.
 eapply Rle_trans; [apply Rabs_triang|].
 apply Rplus_le_compat.
 { rewrite <- (Rabs_right (ν^8)) by approx.
   rewrite <- !RPow_abs. apply Rle_pow_le1; try lia. approx. }
 inversion H4; subst; cbn -[Cpow pow ν]; rewrite ?Rabs_R0; try approx.
 eapply Rle_trans; [apply Rabs_triang|].
 rewrite <- (Rplus_0_r (ν^12)).
 apply Rplus_le_compat.
 { rewrite <- (Rabs_right (ν^12)) by approx.
   rewrite <- !RPow_abs. apply Rle_pow_le1; try lia. approx. }
 inversion H6; subst. simpl. rewrite Rabs_R0; lra.
 assert (n2 < 16)%nat; try lia. { apply B. simpl. tauto. }
Qed.

Lemma best_4packν_below l :
  Delta 4 l -> Below l 16 ->
  Rabs (Rlistsum (List.map (pow ν) l)) <= max4packν.
Proof.
 intros D B.
 destruct l as [|a l].
 - simpl. rewrite Rabs_R0. approx.
 - revert l D B. induction a as [|a IH]; intros l D B.
   + apply best_4packν_0; auto. unfold Below in *. simpl in *. intuition.
   + replace (S a::l)%list with (List.map S (a :: List.map pred l))%list.
     2:{ simpl. f_equal. rewrite List.map_map.
         rewrite <- (List.map_id l) at 2. apply List.map_ext_in.
         intros b Hb.
         assert (b<>O); try lia.
         { contradict Hb. subst b.
           apply (@Delta_nz' 4 (S a) l); auto; try lia. }}
     rewrite List.map_map, (Rlistsum_pow_factor ν 1), Rabs_mult, pow_1.
     set (l' := List.map pred l).
     eapply Rle_trans. 2:apply (IH l').
     * rewrite <- (Rmult_1_l (Rabs (Rlistsum _))) at 2.
       apply Rmult_le_compat_r; try apply Rabs_pos. approx.
     * unfold l'. clear l'.
       destruct l as [|b l].
       { simpl; constructor. }
       { inversion_clear D. simpl. constructor. lia.
         apply (@Delta_pred 4 (b::l)); auto.
         apply (@Delta_nz' 4 a (b::l)); try lia.
         constructor; auto; try lia. }
     * unfold Below in *. intros y [->|Hy].
       { specialize (B (S y)). simpl in B; lia. }
       { unfold l' in *. clear l'.
         rewrite List.in_map_iff in Hy. destruct Hy as (x & <- & Hx).
         assert (x < 16)%nat by (apply (B x); simpl; intuition).
         lia. }
Qed.

Lemma best_4packν l :
  Delta 4 l ->
  Rabs (Rlistsum (List.map (pow ν) l)) <= max4packν / (1 - ν ^16).
Proof.
 intros D.
 assert (B := maxlist0_above l).
 setoid_rewrite <- Nat.lt_succ_r in B.
 set (N := S (maxlist 0 l)). change (Below l N) in B. clearbody N.
 revert l D B.
 induction N as [N IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases N 16).
 - clear IH. intros l D B.
   eapply Rle_trans. apply best_4packν_below; auto.
   unfold Below in *. intros y Hy. specialize (B y Hy). lia.
   approx.
 - intros l D B. destruct (cut_lt_ge 16 l) as (l1,l2) eqn:E.
   assert (D' := D).
   assert (E' := cut_app 16 l). rewrite E in E'. rewrite <- E' in D',B |- *.
   rewrite Delta_app_iff in D'. destruct D' as (D1 & D2 & D3).
   rewrite List.map_app, Rlistsum_app.
   eapply Rle_trans. apply Rabs_triang.
   eapply Rle_trans; [eapply Rplus_le_compat_r|].
   + apply best_4packν_below; auto.
     generalize (cut_fst 16 l). now rewrite E.
   + assert (A : forall n, List.In n l2 -> (16 <= n)%nat).
     { intros n Hn. apply (@cut_snd' 4 16 l); auto. now rewrite E. }
     rewrite (Rlistsum_pow_factor_above ν 16 l2) by trivial.
     set (l2' := List.map (decr 16) l2).
     rewrite Rabs_mult.
     replace (max4packν / _)
       with (max4packν + Rabs (ν^16) * (max4packν / (1 - ν^16))).
     * apply Rplus_le_compat_l.
       apply Rmult_le_compat_l; try apply Rabs_pos.
       apply (IH (N-16)%nat); try lia.
       { apply Delta_map_decr; auto. }
       { unfold l2'. intros x Hx. rewrite List.in_map_iff in Hx.
         destruct Hx as (y & <- & Hy).
         specialize (A y Hy).
         assert (y < N)%nat by (apply B; rewrite List.in_app_iff; now right).
         unfold decr. lia. }
     * rewrite Rabs_right; try field; approx.
Qed.

(** Now the α part of the bound *)

Definition max4packa := Cmod (1+α^5+α^9+α^14).

#[local] Instance : Approx 0.37433943916 (Cmod α ^16) 0.37433943918.
Proof.
 replace (Cmod α^16) with ((Cmod α^2)^8) by ring. approx.
Qed.

Ltac simpl_α := repeat (autorewrite with α; ring_simplify).
#[local] Hint Rewrite α_is_Croot : α.

Local Open Scope C.
Lemma α5 : α^5 = 1 + α + α^3.
Proof. rewrite Cpow_S. now simpl_α. Qed.
#[local] Hint Rewrite α5 : α.
Lemma α6 : α^6 = 1 + α + α^2 + α^3.
Proof. rewrite Cpow_S. now simpl_α. Qed.
#[local] Hint Rewrite α6 : α.
Lemma α7 : α^7 = 1 + α + α^2 + 2*α^3.
Proof. rewrite Cpow_S. now simpl_α. Qed.
#[local] Hint Rewrite α7 : α.
Lemma α8 : α^8 = 2 + α + α^2 + 3*α^3.
Proof. rewrite Cpow_S. now simpl_α. Qed.
#[local] Hint Rewrite α8 : α.
Lemma α9 : α^9 = 3 + 2*α + α^2 + 4*α^3.
Proof. rewrite Cpow_S. now simpl_α. Qed.
#[local] Hint Rewrite α9 : α.
Lemma α10 : α^10 = 4 + 3*α + 2*α^2 + 5*α^3.
Proof. rewrite Cpow_S. now simpl_α. Qed.
#[local] Hint Rewrite α10 : α.
Lemma α11 : α^11 = 5 + 4*α + 3*α^2 + 7*α^3.
Proof. rewrite Cpow_S. now simpl_α. Qed.
#[local] Hint Rewrite α11 : α.
Lemma α12 : α^12 = 7 + 5*α + 4*α^2 + 10*α^3.
Proof. rewrite Cpow_S. now simpl_α. Qed.
#[local] Hint Rewrite α12 : α.
Lemma α13 : α^13 = 10 + 7*α + 5*α^2 + 14*α^3.
Proof. rewrite Cpow_S. now simpl_α. Qed.
#[local] Hint Rewrite α13 : α.
Lemma α14 : α^14 = 14 + 10*α + 7*α^2 + 19*α^3.
Proof. rewrite Cpow_S. now simpl_α. Qed.
#[local] Hint Rewrite α14 : α.
Lemma α15 : α^15 = 19 + 14*α + 10*α^2 + 26*α^3.
Proof. rewrite Cpow_S. now simpl_α. Qed.
#[local] Hint Rewrite α15 : α.
Local Close Scope C.

Module FixQuadrinomial.
(* explicit polynomial syntax [a*α^3+b*α^2+c*α+d]
   even if some coefficients are 0 or 1. Needed for application
   of cmod2_α_quadrinomial below. *)
Local Open Scope C.
Ltac fix1 t :=
 match t with
 | ?c * α + _ => constr:(t)
 | ?c * α => constr:(c*α+0)
 | α + ?t => constr:(1*α+t)
 | α => constr:(1*α+0)
 | _ => constr:(0*α+t)
 end.
Ltac fix2 t :=
 match t with
 | ?c * α^2 + ?t => let t' := fix1 t in constr:(c*α^2+t')
 | ?c * α^2 => fix2 constr:(t+0)
 | α^2 + ?t => fix2 constr:(1*α^2+t)
 | α^2 => fix2 constr:(1*α^2+0)
 | _ => fix2 constr:(0*α^2+t)
 end.
Ltac fix3 t :=
 match t with
 | ?c * α^3 + ?t => let t' := fix2 t in constr:(c*α^3+t')
 | ?c * α^2 => fix3 constr:(t+0)
 | α^3 + ?t => fix3 constr:(1*α^3+t)
 | α^3 => fix3 constr:(1*α^3+0)
 | _ => fix3 constr:(0*α^3+t)
 end.
End FixQuadrinomial.

Ltac calc_α :=
  let c := fresh in
  let H := fresh in
  remember (Cplus _ _) as c eqn:H; (* ad-hoc but enough here ! *)
  repeat (autorewrite with α in H; ring_simplify in H);
  (* fixing quadrinomial *)
  rewrite <- ?Cplus_assoc in H;
  match type of H with _ = ?t =>
    let t' := FixQuadrinomial.fix3 t in replace t with t' in H by ring
  end;
  rewrite ?Cplus_assoc in H;
  rewrite H; clear c H.

Lemma cmod2_α_quadrinomial (a b c d : R) :
 Cmod (d*α^3+c*α^2+b*α+a)^2 =
 (a + b*re_α + c*re_α^2 + d*re_α^3 - (c+3*d*re_α)*im_α^2)^2
 + (re_α*im_α*(2*c+3*d*re_α) + im_α*b - d*im_α^3)^2.
Proof.
 rewrite Cmod2_alt. f_equal; f_equal; unfold α; cbn; ring.
Qed.

#[local] Instance : Approx 6.7073103 (max4packa^2) 6.7073105.
Proof.
 unfold max4packa. calc_α. rewrite cmod2_α_quadrinomial. approx.
Qed.

Lemma best_4packa_0 l :
  Delta 4 (O::l) -> Below l 16 ->
  Cmod (Clistsum (List.map (Cpow α) (O::l))) <= max4packa.
Proof.
 intros D B.
 apply Rle_pow2_inv; [apply Cmod_ge_0| ].
 assert (H : Delta 4 (O::l) /\ Below (O::l) 16).
 { split; trivial. intros x [<-|Hx]. lia. now apply B. }
 rewrite enum_delta_below_ok0 in H.
 compute in H;
 repeat destruct H as [<-|H]; try destruct H as [ ]; cbn -[Cpow pow];
  try (calc_α; rewrite cmod2_α_quadrinomial; approx). (* slow... *)
 rewrite !Cplus_assoc, Cplus_0_r; apply Rle_refl. (* for max4packa *)
Qed.

Lemma best_4packa_below l :
  Delta 4 l -> Below l 16 ->
  Cmod (Clistsum (List.map (Cpow α) l)) <= max4packa.
Proof.
 intros D B.
 destruct l as [|a l].
 - cbn -[Cpow]. rewrite Cmod_0. apply Cmod_ge_0.
 - revert l D B. induction a as [|a IH]; intros l D B.
   + apply best_4packa_0; auto. unfold Below in *. simpl in *. intuition.
   + replace (S a::l)%list with (List.map S (a :: List.map pred l))%list.
     2:{ simpl. f_equal. rewrite List.map_map.
         rewrite <- (List.map_id l) at 2. apply List.map_ext_in.
         intros b Hb.
         assert (b<>O); try lia.
         { contradict Hb. subst b.
           apply (@Delta_nz' 4 (S a) l); auto; try lia. }}
     rewrite List.map_map, (Clistsum_pow_factor α 1), Cmod_mult, Cpow_1_r.
     set (l' := List.map pred l).
     eapply Rle_trans. 2:apply (IH l').
     * rewrite <- (Rmult_1_l (Cmod (Clistsum _))) at 2.
       apply Rmult_le_compat_r; try apply Cmod_ge_0; try approx.
     * unfold l'. clear l'.
       destruct l as [|b l].
       { simpl; constructor. }
       { inversion_clear D. simpl. constructor. lia.
         apply (@Delta_pred 4 (b::l)); auto.
         apply (@Delta_nz' 4 a (b::l)); try lia.
         constructor; auto; try lia. }
     * unfold Below in *. intros y [->|Hy].
       { specialize (B (S y)). simpl in B; lia. }
       { unfold l' in *. clear l'.
         rewrite List.in_map_iff in Hy. destruct Hy as (x & <- & Hx).
         assert (x < 16)%nat by (apply (B x); simpl; intuition).
         lia. }
Qed.

Lemma best_4packa l :
  Delta 4 l ->
  Cmod (Clistsum (List.map (Cpow α) l)) <=
   max4packa / (1 - Cmod α ^16).
Proof.
 intros D.
 assert (B := maxlist0_above l).
 setoid_rewrite <- Nat.lt_succ_r in B.
 set (N := S (maxlist 0 l)). change (Below l N) in B. clearbody N.
 revert l D B.
 induction N as [N IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases N 16).
 - clear IH. intros l D B.
   eapply Rle_trans. apply best_4packa_below; auto.
   unfold Below in *. intros y Hy. specialize (B y Hy). lia.
   rewrite <- (Rmult_1_r max4packa) at 1. unfold Rdiv.
   apply Rmult_le_compat_l; try apply Cmod_ge_0. approx.
 - intros l D B. destruct (cut_lt_ge 16 l) as (l1,l2) eqn:E.
   assert (D' := D).
   assert (E' := cut_app 16 l). rewrite E in E'. rewrite <- E' in D',B |- *.
   rewrite Delta_app_iff in D'. destruct D' as (D1 & D2 & D3).
   rewrite List.map_app, Clistsum_app.
   eapply Rle_trans. apply Cmod_triangle.
   eapply Rle_trans; [eapply Rplus_le_compat_r|].
   + apply best_4packa_below; auto.
     generalize (cut_fst 16 l). now rewrite E.
   + assert (A : forall n, List.In n l2 -> (16 <= n)%nat).
     { intros n Hn. apply (@cut_snd' 4 16 l); auto. now rewrite E. }
     rewrite (Clistsum_pow_factor_above α 16 l2) by trivial.
     set (l2' := List.map (decr 16) l2).
     rewrite Cmod_mult.
     replace (max4packa / _)
       with (max4packa + Cmod (α^16) * (max4packa / (1 - Cmod α ^16))).
     * apply Rplus_le_compat_l.
       apply Rmult_le_compat_l; try apply Cmod_ge_0.
       apply (IH (N-16)%nat); try lia.
       { apply Delta_map_decr; auto. }
       { unfold l2'. intros x Hx. rewrite List.in_map_iff in Hx.
         destruct Hx as (y & <- & Hy).
         specialize (A y Hy).
         assert (y < N)%nat by (apply B; rewrite List.in_app_iff; now right).
         unfold decr. lia. }
     * rewrite Cmod_pow. field. approx.
Qed.

(** And finally: *)

Definition TheBound :=
  2 * Cmod coefa0 * max4packa / (1 - Cmod α ^16) +
  Rabs coefν0 * max4packν / (1 - ν ^16).

Lemma diff0_better_bound n : Rabs (diff0 n) <= TheBound.
Proof.
 unfold TheBound.
 rewrite diff0_decomp_eqn'.
 eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat.
 - rewrite Rabs_mult. rewrite Rabs_right by lra.
   unfold Rdiv. rewrite !Rmult_assoc. apply Rmult_le_compat_l; try lra.
   eapply Rle_trans; [apply re_le_Cmod|].
   rewrite Cmod_mult. apply Rmult_le_compat_l; try apply Cmod_ge_0.
   apply best_4packa, decomp_delta.
 - rewrite Rabs_mult.
   unfold Rdiv. rewrite !Rmult_assoc. apply Rmult_le_compat_l.
   apply Rabs_pos. apply best_4packν, decomp_delta.
Qed.

(** And finally, we obtain that diff0 is always strictly less than 2.
    (experimentally the new bound is around 1.997) *)

#[local] Instance : Approx 12.2669622508 (Cmod detU ^2) 12.266962256.
Proof.
 rewrite detU_alt.
 rewrite !Cmod_mult, !Rpow_mult_distr, !Cmod_R, Cmod_Ci.
 rewrite !Rabs_right by approx. autorewrite with RtoC. rewrite Cmod_R.
 approx.
Qed.

#[local] Instance : Approx 0.4785740967 (Cmod UV0a ^2) 0.4785740985.
Proof.
 unfold UV0a. calc_α. rewrite cmod2_α_quadrinomial. approx.
Qed.

#[local] Instance : Approx 0.916466310 (Cmod coefa_detU ^2) 0.916466315.
Proof.
 unfold coefa_detU.
 rewrite !Cmod_mult, !Rpow_mult_distr.
 rewrite Cmod2_alt.
 unfold Cminus. rewrite re_plus, im_plus, re_RtoC, im_RtoC.
 rewrite re_opp. change (Re αbar) with re_α.
 rewrite im_opp. change (Im αbar) with (-im_α).
 rewrite Ropp_involutive, Rplus_0_l.
 approx.
Qed.

#[local] Instance : Approx 0.04433925756 (Cmod coefa0 ^2) 0.04433925783.
Proof.
 unfold coefa0, coefsa. unfold scale. cbn -[pow ν].
 rewrite !Cmod_mult, !Rpow_mult_distr.
 rewrite <- α_conj, Cmod_Cconj, αmod2.
 autorewrite with RtoC. rewrite Cmod_R, Rabs_right by approx.
 replace (_*(τ/_)) with ((-ν)*τ) by (field; approx).
 rewrite Cmod_inv, pow_inv by apply detU_nz.
 approx.
Qed.

#[local] Instance :
  Approx 1.09068264 (2 * Cmod coefa0 * max4packa) 1.09068267.
Proof.
 apply pow2_approx_inv; try qle.
 - rewrite !Rpow_mult_distr; approx.
 - repeat apply Rmult_le_pos; try apply Cmod_ge_0; lra.
Qed.

#[local] Instance : Approx 0.1395542639 (Rabs coefν0) 0.1395542641.
Proof.
 unfold coefν0. unfold coefsν, scale. rewrite vectν_alt.
 rewrite αmod2. unfold mkvectR, mkvect, list2D_to_matrix.
 simpl nth.
 rewrite re_scal_r.
 rewrite Rabs_mult.
 replace (/detU * coefν_detU)%C with
     (-UV0ν / (Cmod α ^2 + ν^2 + 2 * - ν * re_α))%C.
 2:{ unfold coefν_detU.
     replace (αbar-α)%C with (-(α - Cconj α))%C
       by (rewrite α_conj; ring).
     rewrite im_alt'. change (Im α) with im_α.
     rewrite detU_alt. field.
     repeat split.
     - autorewrite with RtoC. apply RtoC_inj_neq. approx.
     - injection 1. lra.
     - apply RtoC_inj_neq. approx. }
 unfold UV0ν. autorewrite with RtoC. rewrite re_RtoC.
 approx.
Qed.

#[local] Instance : Approx 1.9968 TheBound 1.99798.
Proof.
 unfold TheBound. approx.
Qed.

Lemma diff0_lt_2 n : Rabs (diff0 n) < 2.
Proof.
 eapply Rle_lt_trans. apply diff0_better_bound. approx.
Qed.

(* Print Assumptions diff0_lt_2. *)

(* Consequences for f3 : *)

Lemma f3_alt n : INR (f 3 n) = τ*n + diff0 n.
Proof.
 rewrite diff0_alt; lra.
Qed.

Lemma f3_close_τn (n:nat) : -2 < τ*n - f 3 n < 2.
Proof.
 rewrite f3_alt.
 assert (H := diff0_lt_2 n).
 rewrite Rcomplements.Rabs_lt_between in H. lra.
Qed.

Lemma f3_close_natpart (n:nat) :
 (nat_part (τ*n) - 1 <= f 3 n <= nat_part (τ*n) + 2)%nat.
Proof.
assert (LT := f3_close_τn n).
assert (LE : 0 <= τ*n).
{ apply Rmult_le_pos. approx. apply pos_INR. }
split.
- assert (H : 0 <= τ*n < INR(2 + f 3 n)).
  { rewrite plus_INR. simpl. lra. }
  apply nat_part_lt in H. lia.
- assert (INR(f 3 n - 2) <= τ*n).
  { destruct (Nat.le_gt_cases (f 3 n) 2).
    - replace (f 3 n - 2)%nat with O by lia. simpl. lra.
    - rewrite minus_INR by lia. simpl. lra. }
  apply nat_part_le in H; auto; lia.
Qed.

(* NB: both lower and upper bounds are reached. *)

(* A quasi-additivity result for f 3 that I was unable to obtain
   directly on f 3.
   Note : the -5 and +5 constants could probably be improved here. *)

Lemma f3_quasiadd p n :
 (f 3 p + f 3 n -5 <= f 3 (p+n) <= f 3 p + f 3 n + 5)%nat.
Proof.
split.
 - destruct (Nat.le_gt_cases (f 3 p + f 3 n) 5); try lia.
   assert (f 3 p + f 3 n < f 3 (p+n) +6)%nat; try lia.
   apply INR_lt. rewrite !plus_INR. simpl INR.
   generalize (f3_close_τn (p+n)) (f3_close_τn p) (f3_close_τn n).
   rewrite plus_INR. lra.
 - rewrite <- Nat.lt_succ_r.
   apply INR_lt. rewrite S_INR, !plus_INR. simpl INR.
   generalize (f3_close_τn (p+n)) (f3_close_τn p) (f3_close_τn n).
   rewrite plus_INR. lra.
Qed.

(* Print Assumptions f3_quasiadd. *)

(** To finish someday, less interesting : frequencies for the other letters. *)
