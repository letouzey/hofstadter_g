From Coq Require Import Bool Arith Lia Reals Lra.
From Hofstadter.HalfQuantum Require Import Matrix.
Require Import MoreFun MoreList MoreReals MoreComplex MoreSum.
Require Import MoreLim MorePoly MoreMatrix.
Require Import DeltaList GenFib GenG GenAdd Words Mu ThePoly Approx.
Local Open Scope Q.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion RtoC : R >-> C.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * Studying case q=3

   We focus here on the case q=3, compute the complex roots of [X^4-X^3-1],
   and express (A 3 n) in term of combinations of powers of these roots.
   Then we study the frequencies in [Words.qseq 3] and the behaviour of
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

#[local] Instance : Approx 0.9144736628 im_α 0.9144736630.
Proof. approx. Qed.

#[local] Instance : Approx 0.8362620801 (im_α^2) 0.8362620803.
Proof. approx. Qed.

Lemma im_α_2 : im_α^2 = τ/(-ν)-re_α^2.
Proof.
 unfold im_α. rewrite pow2_sqrt. lra. approx.
Qed.

Lemma αmod2 : Cmod α ^2 = τ/-ν.
Proof.
 rewrite Cmod2_alt. unfold α. simpl Re; simpl Im.
 rewrite im_α_2. lra.
Qed.

#[local] Instance αmod_approx : Approx 0.9404356826 (Cmod α) 0.9404356828.
Proof. approx. Qed.

#[local] Instance : Approx 0.884419273293 (Cmod α ^2) 0.884419273296.
Proof. rewrite αmod2. approx. Qed.

Definition roots := [RtoC μ; α; αbar; RtoC ν].

Lemma roots_sorted : SortedRoots 3 roots.
Proof.
 split.
 2:{ do 3 constructor.
     - repeat constructor.
     - constructor. left. unfold αbar. simpl. approx.
     - right. unfold α, αbar. simpl. split; trivial. approx.
     - unfold α. simpl. approx. }
 destruct (SortedRoots_exists 3) as (l & Hl).
 case Hl. intros E _. rewrite E. apply linfactors_perm. clear E.
 assert (LN := SortedRoots_length 3 l Hl).
 assert (FS := SortedRoots_mu 3 l Hl).
 assert (K : Nat.Odd 3) by now exists 1%nat.
 assert (LT := SortedRoots_nu 3 l K Hl).
 destruct (SortedRoots_im_pos 3 l Hl 0) as (LT',EQ); try lia.
 simpl in LT', EQ.
 destruct l as [|a [|b [|c [|d [|? l]]]]]; try (simpl; easy).
 unfold Cnth in *; simpl in *. subst. clear LN K. unfold roots.
 assert (b = α); subst; try easy.
 destruct Hl as (E,CS).
 assert (E0 := coef_compat 0 _ _ E).
 assert (E3 := coef_compat 3 _ _ E).
 unfold ThePoly,coef in E0,E3; simpl in E0,E3. fold μ in *. fold ν in *.
 ring_simplify in E0. field_simplify in E3.
 assert (E3' : (RtoC μ + RtoC ν + b + Cconj b = 1)%C).
 { rewrite Ceq_minus in E3. ring_simplify in E3.
   replace (RtoC (-1)) with (-(1))%C in E3 by lca.
   apply Ceq_minus in E3. rewrite <- E3. lca. }
 clear E E3.
 assert (Rb : Re b = re_α).
 { apply RtoC_inj. rewrite re_alt.
   replace (b+Cconj b)%C with (1-μ-ν)%C by (rewrite <- E3'; lca).
   unfold re_α. lca. }
 assert (Cb : Cmod b ^2 = Cmod α ^2).
 { apply RtoC_inj.
   rewrite αmod2, <- RtoC_pow, Cmod_sqr.
   replace (τ/-ν) with ((-1)*(τ/ν)) by (field; approx).
   rewrite RtoC_mult, RtoC_div, E0, τ_μ, RtoC_inv. field.
   split; apply RtoC_neq; approx. }
 assert (Ib : (Im b)^2 = im_α^2).
 { rewrite !Cmod2_alt, Rb in Cb. unfold α in Cb; simpl in Cb; lra. }
 clear E0 E3' Cb.
 rewrite <- !Rsqr_pow2 in Ib.
 apply Rsqr_eq in Ib.
 destruct Ib as [Ib|Ib]; destruct b as (x,y);
  unfold Cconj, αbar, α in *; simpl in *; subst; f_equal. exfalso.
 revert LT'. apply Rle_not_lt. approx.
Qed.

Local Hint Rewrite RtoC_pow : RtoC.
Local Hint Rewrite <- RtoC_opp RtoC_plus RtoC_mult RtoC_minus RtoC_inv
 RtoC_div : RtoC.

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
 rewrite <- ThePoly_root_carac. destruct roots_sorted as (->,_).
 apply linfactors_roots. simpl. tauto.
Qed.

Lemma αbar_is_Croot : (αbar^4 = αbar^3 + 1)%C.
Proof.
 rewrite <- ThePoly_root_carac. destruct roots_sorted as (->,_).
 apply linfactors_roots. simpl. tauto.
Qed.

Lemma nodup_roots : NoDup roots.
Proof.
 apply (SortedRoots_nodup 3), roots_sorted.
Qed.

Lemma distinct_roots :
  α <> μ /\ αbar <> μ /\ αbar <> α /\
  RtoC ν <> α /\ RtoC ν <> αbar /\ ν <> μ.
Proof.
 assert (H := nodup_roots).
 inversion_clear H. inversion_clear H1. inversion_clear H2. simpl in *.
 intuition.
Qed.

Lemma A3_eqn :
 let a := coefA 3 μ in
 let b := coefA 3 α in
 let c := coefA 3 αbar in
 let d := coefA 3 ν in
 forall n, RtoC (A 3 n) = (a*μ^n + b*α^n + c*αbar^n + d*ν^n)%C.
Proof.
 intros a b c d n.
 rewrite (Equation_A 3 roots roots_sorted). unfold roots.
 simpl. fold a b c d. ring.
Qed.

(** Note about A3_eqn :
    coefficients a b c d are obtained by inversing the Vandermonde
    matrix of roots. Fortunately, they also have simple expressions
    in terms of μ α αbar ν respectively.
    For showing that a is real and >=1, see Freq.A_gt_mu_pow.
    Interestingly, these coefficients are also roots
    of [X^4-X^3-(162/283)*X^2-(24/283)*X-1/283] (not proved here). *)

(** ** Occurrences of letters in morphic word [Words.qseq 3]

    We will see below how this relates to function [f 3])
    and its iterates.

    For a finite word [w], the frequency of letter [a] is
    [nbocc a w / length w]. For infinite words, the frequency
    of a letter (if it exists) is the limit of frequencies for
    ever-growing finite prefixes of the infinite word.

    Here for [Words.qseq 3], the frequencies of letters [0],[1],[2],[3]
    will be respectively [τ^4],[τ^5],[τ^6],[τ^3]
    (another numbering of letters would make that more uniform).
    For proving that and even more, we now consider the following
    differences :
*)

Definition Diff0 w := τ^4 * length w - nbocc 0 w.
Definition Diff1 w := τ^5 * length w - nbocc 1 w.
Definition Diff2 w := τ^6 * length w - nbocc 2 w.
Definition Diff3 w := τ^3 * length w - nbocc 3 w.

Definition diff0 n := Diff0 (take n (qseq 3)).
Definition diff1 n := Diff1 (take n (qseq 3)).
Definition diff2 n := Diff2 (take n (qseq 3)).
Definition diff3 n := Diff3 (take n (qseq 3)).

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
 rewrite take_nth by trivial. apply qseq_letters.
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

Lemma diff3_alt n : diff3 n = τ^3 * n - fs 3 3 n.
Proof.
 unfold diff3, Diff3. rewrite take_length.
 rewrite <- count_nbocc.
 now rewrite fs_count_q.
Qed.

Lemma diff1_alt n : diff1 n = τ^5 * n + fs 3 2 n - f 3 n.
Proof.
 unfold diff1, Diff1. rewrite take_length.
 rewrite <- count_nbocc.
 change (f 3 n) with (fs 3 1 n).
 rewrite (fs_count_above 3 1) by lia.
 rewrite count_above_S.
 rewrite (fs_count_above 3 2) by lia.
 rewrite plus_INR. lra.
Qed.

Lemma diff2_alt n : diff2 n = τ^6 * n + fs 3 3 n - fs 3 2 n.
Proof.
 unfold diff2, Diff2. rewrite take_length.
 rewrite <- count_nbocc.
 rewrite (fs_count_above 3 2) by lia.
 rewrite (fs_count_above 3 3) by lia.
 rewrite (count_above_S (qseq 3) 2).
 rewrite plus_INR. lra.
Qed.

(** Equations giving Diff0 and co after a substitution [qsubst 3]. *)

Lemma Diff0_qsubst3 w : Diff0 (qsubstw 3 w) = τ * Diff3 w.
Proof.
 unfold Diff0, Diff3.
 rewrite len_qsubst, plus_INR.
 destruct (nbocc_qsubst3 w) as (-> & _ & _ & _).
 ring_simplify. unfold Rminus. rewrite Rplus_assoc. f_equal.
 rewrite τ4. lra.
Qed.

Lemma Diff3_qsubst3 w :
  List.Forall (fun a => a <= 3)%nat w ->
  Diff3 (qsubstw 3 w) = - τ^3 * Diff3 w - Diff0 w - Diff1 w.
Proof.
 intros H.
 unfold Diff0, Diff1, Diff3.
 rewrite len_qsubst.
 destruct (nbocc_qsubst3 w) as (_ & _ & _ & ->).
 rewrite !plus_INR.
 ring_simplify. rewrite τ6, τ5, τ4. ring_simplify.
 rewrite !len_nbocc_0123 by trivial. rewrite !plus_INR. ring.
Qed.

Lemma Diff1_qsubst3 w :
  List.Forall (fun a => a <= 3)%nat w ->
  Diff1 (qsubstw 3 w) = - τ^5 * Diff3 w + Diff0 w.
Proof.
 intros H.
 unfold Diff0, Diff1, Diff3.
 rewrite len_qsubst.
 destruct (nbocc_qsubst3 w) as (_ & -> & _ & _).
 rewrite !plus_INR.
 ring_simplify. replace (τ^8) with ((τ^4)^2) by ring.
 rewrite τ5, τ4. ring_simplify.
 rewrite !len_nbocc_0123 by trivial. rewrite !plus_INR. ring.
Qed.

(** Same, expressed via matrix *)

Definition Diffs w : Vector 3 := mkvectR 3 [Diff3 w; Diff0 w; Diff1 w].
Definition diffs n : Vector 3 := mkvectR 3 [diff3 n; diff0 n; diff1 n].

Definition B : Square 3 :=
 list2D_to_matrix [[-τ^3;-1%C;-1%C];[RtoC τ;0;0];[-τ^5;1;0]]%C.

Lemma WF_B : WF_Matrix B.
Proof.
 apply WF_list2D_to_matrix; simpl; intuition; subst; auto.
Qed.

Lemma WF_Diffs w : WF_Matrix (Diffs w).
Proof.
 now apply WF_mkvectR.
Qed.

#[local] Hint Resolve WF_B WF_Diffs : wf_db.

Lemma diffs_alt n : diffs n = Diffs (take n (qseq 3)).
Proof.
 reflexivity.
Qed.

Lemma Diffs_qsubst3 w :
  List.Forall (fun a => a <= 3)%nat w ->
  Diffs (qsubstw 3 w) = B × Diffs w.
Proof.
 intro.
 apply Vect3_eq; auto with wf_db;
  unfold Diffs; cbn -[Cpow];
  rewrite ?Diff3_qsubst3, ?Diff0_qsubst3, ?Diff1_qsubst3 by trivial;
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
 - rewrite diffs_alt, qseq_take_A, qword_S, Diffs_qsubst3, IHn in *
    by (apply qword_letters).
   simpl. now rewrite Mmult_assoc.
Qed.

Definition U : Square 3 :=
 list2D_to_matrix [[-α^2;α+1;α];
                   [-αbar^2;αbar+1; αbar];
                   [-ν^2;ν+1;RtoC ν]]%C.

Definition D : Square 3 :=
 list2D_to_matrix [[α;0;0]; [0;αbar;0]; [0;0;RtoC ν]]%C.

Definition Dn n : Square 3 :=
 list2D_to_matrix [[α^n;0;0]; [0;αbar^n;0]; [0;0;RtoC ν ^n]]%C.

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
 ring_simplify. rewrite μ_τ, RtoC_inv.
 field_simplify; [|injection; approx].
 rewrite RtoC_pow, τ4, RtoC_minus.
 field. injection; approx.
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
    [ ring | injection; apply distinct_roots | apply ν_is_Croot].
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
 rewrite detU_alt, !Cmult_integral. intros E.
 repeat destruct E as [E|E]; autorewrite with RtoC in E; injection E; approx.
Qed.

Definition invU_detU : Square 3 :=
 list2D_to_matrix
  [[ ν-αbar; -(ν-α); αbar-α];
   [-αbar*ν*(ν-αbar); α*ν*(ν-α);
       -α*αbar*(αbar-α)];
   [(ν-αbar)*(αbar*ν+ν+αbar);
       -(ν-α)*(α*ν+ν+α);
       (αbar-α)*(α*αbar+αbar+α)]]%C.

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
   [ | injection; apply distinct_roots | apply ν_is_Croot ].
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
 { rewrite is_real_carac. autorewrite with cconj.
   rewrite detU_conj.
   unfold coefν_detU. autorewrite with cconj. rewrite E0. field.
   apply detU_nz. }
 unfold coefsν. rewrite vectν_alt;
 intros Hi; destruct i as [|[|[|]]]; try lia; clear Hi;
 unfold scale, mkvectR; rewrite mkvect_eqn; unfold Cnth; simpl nth;
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
 rewrite decomp_prefix_qseq. unfold qwords. rewrite flat_map_concat_map.
 rewrite Diff0_concat, List.map_map, List.map_rev, Rlistsum_rev.
 f_equal.
 apply List.map_ext; intros.
 rewrite <- qseq_take_A. apply diff0_A3_powers.
Qed.

Lemma diff0_decomp_eqn' n :
  diff0 n =
   2*Re (coefa0 * Cpoly α (decomp 3 n)) + coefν0 * Rpoly ν (decomp 3 n).
Proof.
 rewrite diff0_decomp_eqn.
 induction decomp.
 - cbn -[Re ν]. rewrite Cmult_0_r. simpl. ring.
 - set (f := fun n => _) in *.
   simpl map. rewrite Rpoly_cons, Cpoly_cons, Rlistsum_cons.
   rewrite Cmult_plus_distr_l, re_plus, !Rmult_plus_distr_l, IHl.
   unfold f at 1. ring.
Qed.

(** With the previous expression of [diff0 n], we will progressively bound it
    by some constant independent from [n]. *)

Lemma diff0_decomp_le n :
 Rabs (diff0 n) <=
  2 * Cmod coefa0 * Rpoly (Cmod α) (decomp 3 n)
  + Rabs coefν0 * Rpoly (Rabs ν) (decomp 3 n).
Proof.
 rewrite diff0_decomp_eqn. unfold Rpoly.
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
   + apply Rlt_le,sum_pow; try lia; try apply decomp_delta. approx.
 - apply Rmult_le_compat_l; try apply Rabs_pos.
   replace (ν^4) with (Rabs ν^4) by (rewrite Rabs_left by approx; ring).
   apply Rlt_le,sum_pow; try lia; try apply decomp_delta.
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
  Delta 4 (O::l) -> Below l 16 -> Rabs (Rpoly ν (O::l)) <= max4packν.
Proof.
 intros D B. unfold Rpoly.
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
  Delta 4 l -> Below l 16 -> Rabs (Rpoly ν l) <= max4packν.
Proof.
 intros D B.
 destruct l as [|a l].
 - unfold Rpoly; simpl. rewrite Rabs_R0. approx.
 - revert l D B. induction a as [|a IH]; intros l D B.
   + apply best_4packν_0; auto. unfold Below in *. simpl in *. intuition.
   + replace (S a::l)%list with (List.map S (a :: List.map pred l))%list.
     2:{ simpl. f_equal. rewrite List.map_map.
         rewrite <- (List.map_id l) at 2. apply List.map_ext_in.
         intros b Hb.
         assert (b<>O); try lia.
         { contradict Hb. subst b.
           apply (@Delta_nz' 4 (S a) l); auto; try lia. }}
     unfold Rpoly.
     rewrite List.map_map, (Rlistsum_pow_factor ν 1), Rabs_mult, pow_1.
     set (l' := List.map pred l).
     eapply Rle_trans. 2:apply (IH l').
     * rewrite <- (Rmult_1_l (Rabs (Rpoly _ _))) at 2.
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
  Delta 4 l -> Rabs (Rpoly ν l) <= max4packν / (1 - ν ^16).
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
   rewrite Rpoly_app.
   eapply Rle_trans. apply Rabs_triang.
   eapply Rle_trans; [eapply Rplus_le_compat_r|].
   + apply best_4packν_below; auto.
     generalize (cut_fst 16 l). now rewrite E.
   + assert (A : forall n, List.In n l2 -> (16 <= n)%nat).
     { intros n Hn. apply (@cut_snd' 4 16 l); auto. now rewrite E. }
     rewrite (Rpoly_factor_above ν 16 l2) by trivial.
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

Module Coefs.
(** Quadruplets (a,b,c,d) for "reduced" polynomials a+bα+cα^2+dα^3 *)
Local Open Scope nat.

Variant coefs := Coefs (a b c d : nat).

Definition zero : coefs := Coefs 0 0 0 0.

Definition add '(Coefs a b c d) '(Coefs a' b' c' d') :=
 Coefs (a+a') (b+b') (c+c') (d+d').

Fixpoint of_exp n :=
 match n with
 | 0 => Coefs 1 0 0 0
 | 1 => Coefs 0 1 0 0
 | 2 => Coefs 0 0 1 0
 | 3 => Coefs 0 0 0 1
 | S n => add (of_exp n) (of_exp (n-3))
 end.

Definition of_poly l := List.fold_right add zero (map of_exp l).

Definition Ceval x '(Coefs a b c d) := (a + b * x + c * x^2 + d * x^3)%C.

Lemma of_exp_S n : 3 <= n ->
  of_exp (S n) = add (of_exp n) (of_exp (n-3)).
Proof.
 destruct n as [|[|[|n]]]; lia || easy.
Qed.

Lemma Ceval_add x c c' :
  (Ceval x (add c c') = Ceval x c + Ceval x c')%C.
Proof.
 destruct c as [a b c d], c' as [a' b' c' d']. simpl.
 rewrite !plus_INR. lca.
Qed.

Lemma Cpow_α_reduce n : (α^n = Ceval α (of_exp n))%C.
Proof.
 induction n as [n IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases n 3).
 - destruct n as [|[|[|[|n]]]]; lca || lia.
 - destruct n; try lia. rewrite of_exp_S by lia.
   rewrite Ceval_add, <- !IH by lia. clear IH.
   replace (S n) with (4 + (n-3)) by lia.
   rewrite Cpow_add_r, α_is_Croot.
   replace n with (3 + (n-3)) at 2 by lia.
   rewrite Cpow_add_r. ring.
Qed.

Lemma Cpoly_α_reduce l : (Cpoly α l = Ceval α (of_poly l))%C.
Proof.
 induction l.
 - unfold Cpoly. simpl. lca.
 - cbn. rewrite Ceval_add, Cpow_α_reduce. f_equal. apply IHl.
Qed.

End Coefs.

Lemma cmod2_α_quadrinomial (a b c d : R) :
 Cmod (a+b*α+c*α^2+d*α^3)^2 =
 (a + b*re_α + c*re_α^2 + d*re_α^3 - (c+3*d*re_α)*im_α^2)^2
 + (re_α*im_α*(2*c+3*d*re_α) + im_α*b - d*im_α^3)^2.
Proof.
 rewrite Cmod2_alt. f_equal; f_equal; unfold α; cbn; ring.
Qed.

Ltac calc_α_poly :=
 rewrite Coefs.Cpoly_α_reduce; cbn -[pow INR];
 rewrite cmod2_α_quadrinomial; approx.

(** The best "pack" *)
Definition max4lista := [0;5;9;14]%nat.
Definition max4packa := Cmod (Cpoly α max4lista).

#[local] Instance : Approx 6.7073103 (max4packa^2) 6.7073105.
Proof.
 unfold max4packa, max4lista. calc_α_poly.
Qed.

#[local] Instance : Approx 2.58984 max4packa 2.58985.
Proof.
 apply pow2_approx_inv; try lra; try apply Cmod_ge_0. approx.
Qed.

Lemma best_4packa_enum l :
  In l (enum_sparse_subsets0 3 16) -> Cmod (Cpoly α l) <= max4packa.
Proof.
 intros H. apply Rle_pow2_inv; [apply Cmod_ge_0|]. revert l H.
 apply Forall_forall. vm_compute enum_sparse_subsets0.
 repeat (constructor; [ calc_α_poly || apply Rle_refl | ]). constructor.
Qed.

Lemma best_4packa_below l :
  Delta 4 l -> Below l 16 ->
  Cmod (Cpoly α l) <= max4packa.
Proof.
 intros D B.
 destruct l as [|a l].
 - cbn -[Cpow]. rewrite Cmod_0. apply Cmod_ge_0.
 - revert l D B. induction a as [|a IH]; intros l D B.
   + apply best_4packa_enum.
     now rewrite enum_sparse_subsets0_ok, enum_sparse_subsets_ok.
   + replace (S a::l)%list with (List.map S (a :: List.map pred l))%list.
     2:{ simpl. f_equal. rewrite List.map_map.
         rewrite <- (List.map_id l) at 2. apply List.map_ext_in.
         intros b Hb.
         assert (b<>O); try lia.
         { intros ->. apply (@Delta_nz' 4 (S a) l); auto; lia. }}
     unfold Cpoly.
     rewrite List.map_map, (Clistsum_pow_factor α 1), Cmod_mult, Cpow_1_r.
     set (l' := List.map pred l).
     eapply Rle_trans. 2:apply (IH l').
     * rewrite <- (Rmult_1_l (Cmod (Cpoly _ _))) at 2.
       apply Rmult_le_compat_r; try apply Cmod_ge_0; try approx.
     * change (Delta 4 (map pred (S a :: l))). clear l'.
       apply Delta_pred; trivial. eapply Delta_nz; eauto; lia.
     * change (Below (map pred (S a :: l)) 16). clear l'.
       unfold Below in *. intros x. rewrite in_map_iff.
       intros (y & <- & Hy). specialize (B y Hy). lia.
Qed.

Lemma best_4packa l :
  Delta 4 l -> Cmod (Cpoly α l) <= max4packa / (1 - Cmod α ^16).
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
   rewrite Cpoly_app.
   eapply Rle_trans. apply Cmod_triangle.
   eapply Rle_trans; [eapply Rplus_le_compat_r|].
   + apply best_4packa_below; auto.
     generalize (cut_fst 16 l). now rewrite E.
   + assert (A : forall n, List.In n l2 -> (16 <= n)%nat).
     { intros n Hn. apply (@cut_snd' 4 16 l); auto. now rewrite E. }
     rewrite (Cpoly_factor_above α 16 l2) by trivial.
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

(** And finally, we obtain that |diff0| is always strictly less than 2.
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
 replace UV0a with (Cpoly α [0;1;2;3])%nat. calc_α_poly.
 unfold Cpoly, UV0a. simpl. ring.
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
 rewrite Cmod_inv, pow_inv. approx.
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
     repeat split; autorewrite with RtoC; injection; approx. }
 unfold UV0ν. autorewrite with RtoC. rewrite re_RtoC.
 approx.
Qed.

#[local] Instance TheBound_approx : Approx 1.9970 TheBound 1.9979.
Proof.
 unfold TheBound. approx.
Qed.

Lemma diff0_lt_2 n : Rabs (diff0 n) < 2.
Proof.
 eapply Rle_lt_trans. apply diff0_better_bound. approx.
Qed.

(* Print Assumptions diff0_lt_2. *)

(** Even the sup of |diff0| is strictly less than 2. *)

Lemma sup_diff0_lt_2 :
 Rbar.Rbar_lt (Sup_seq (fun n => Rabs (diff0 n))) 2.
Proof.
 apply Rbar.Rbar_le_lt_trans with (Sup_seq (fun _ => TheBound)).
 - apply Sup_seq_le. intros n. simpl. apply diff0_better_bound.
 - replace (Sup_seq _) with (Rbar.Finite TheBound); simpl. approx.
   symmetry. apply is_sup_seq_unique. apply is_sup_seq_const.
Qed.

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

Lemma f3_natpart_lower (n:nat) :
 (nat_part (τ*n) <= 1 + f 3 n)%nat.
Proof.
assert (LT := f3_close_τn n).
assert (LE : 0 <= τ*n).
{ apply Rmult_le_pos. approx. apply pos_INR. }
assert (H : 0 <= τ*n < INR(2 + f 3 n)).
{ rewrite plus_INR. simpl. lra. }
apply nat_part_lt in H. lia.
Qed.

Lemma f3_natpart_higher (n:nat) :
 (f 3 n <= nat_part (τ*n) + 2)%nat.
Proof.
assert (LT := f3_close_τn n).
assert (LE : 0 <= τ*n).
{ apply Rmult_le_pos. approx. apply pos_INR. }
assert (INR(f 3 n - 2) <= τ*n).
{ destruct (Nat.le_gt_cases (f 3 n) 2).
  - replace (f 3 n - 2)%nat with O by lia. simpl. lra.
  - rewrite minus_INR by lia. simpl. lra. }
apply nat_part_le in H; auto; lia.
Qed.

Lemma f3_close_natpart (n:nat) :
 (nat_part (τ*n) - 1 <= f 3 n <= nat_part (τ*n) + 2)%nat.
Proof.
split; [|apply f3_natpart_higher]. generalize (f3_natpart_lower n); lia.
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
