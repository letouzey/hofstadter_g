From Coq Require Import Arith Lia Reals Lra.
From QuantumLib Require Import Complex Polynomial Matrix.
Require Import MoreReals MoreLim MoreComplex MorePoly MoreMatrix.
Require Import DeltaList FunG GenFib GenG GenAdd Words Mu ThePoly.
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

Definition mu := mu 3.
Definition tau := tau 3.
Definition nu := nu 3.

Definition re_alpha := (1 - mu - nu)/2.
Definition im_alpha := sqrt (tau/(-nu)-re_alpha^2).

Definition alpha : C := (re_alpha, im_alpha).
Definition alphabar : C := (re_alpha, - im_alpha).

Lemma tau_mu : tau = /mu.
Proof.
 reflexivity.
Qed.

Lemma mu_tau : mu = /tau.
Proof.
 apply tau_inv.
Qed.

Lemma tau4 : tau^4 = 1 - tau.
Proof.
 generalize (tau_carac 3). fold tau. lra.
Qed.

Lemma tau5 : tau^5 = tau - tau^2.
Proof.
 change (tau^5) with (tau*tau^4). rewrite tau4. ring.
Qed.

Lemma tau6 : tau^6 = tau^2 - tau^3.
Proof.
 change (tau^6) with (tau*tau^5). rewrite tau5. ring.
Qed.

Lemma tau3456 : tau^3 + tau^4 + tau^5 + tau^6 = 1.
Proof.
 rewrite tau6, tau5, tau4; ring.
Qed.

Lemma tau_approx : 0.7244 < tau < 0.7245.
Proof.
 exact tau_3.
Qed.

Lemma mu_approx : 1.380 < mu < 1.381.
Proof.
 exact mu_3.
Qed.

Lemma nu_approx : -0.820 < nu < -0.819.
Proof.
 exact nu_3.
Qed.

Ltac lra' := generalize nu_approx mu_approx tau_approx; lra.

Lemma mu_nz : mu <> 0. Proof. lra'. Qed.
Lemma nu_nz : nu <> 0. Proof. lra'. Qed.
Lemma tau_nz : tau <> 0. Proof. lra'. Qed.

Lemma re_alpha_approx : 0.219 < re_alpha < 0.220.
Proof. unfold re_alpha. lra'. Qed.

Lemma re_alpha_nz : re_alpha <> 0.
Proof. generalize re_alpha_approx. lra. Qed.

Lemma im_alpha_2_pos :  re_alpha ^ 2 < tau / - nu.
Proof.
 apply Rlt_trans with (0.220 ^ 2).
 - rewrite <- !Rsqr_pow2.
   apply Rsqr_incrst_1; generalize re_alpha_approx; lra.
 - apply Rmult_lt_reg_r with (-nu).
   + lra'.
   + field_simplify; lra'.
Qed.

Lemma im_alpha_2 : im_alpha^2 = tau/(-nu)-re_alpha^2.
Proof.
 unfold im_alpha.
 rewrite pow2_sqrt; generalize im_alpha_2_pos; lra.
Qed.

Lemma im_alpha_pos : 0 < im_alpha.
Proof.
 apply sqrt_lt_R0. generalize im_alpha_2_pos. lra.
Qed.

Lemma im_alpha_nz : im_alpha <> 0.
Proof. generalize im_alpha_pos; lra. Qed.

Lemma alphamod2 : (Cmod alpha)^2 = tau/(-nu).
Proof.
 rewrite Cmod2_alt. unfold alpha. simpl Re; simpl Im.
 rewrite im_alpha_2. lra.
Qed.

Definition roots3 := [RtoC mu;RtoC nu;alpha;alphabar].

Lemma distinct_roots :
  alpha <> mu /\ alphabar <> mu /\ alphabar <> alpha /\
  alpha <> nu /\ alphabar <> nu /\ nu <> mu.
Proof.
 unfold alpha, alphabar, RtoC; repeat split.
 - intros [= A B]. now destruct im_alpha_nz.
 - intros [= A B]. generalize im_alpha_nz. lra.
 - intros [= B]. generalize im_alpha_nz. lra.
 - intros [= A B]. now destruct im_alpha_nz.
 - intros [= A B]. generalize im_alpha_nz. lra.
 - lra'.
Qed.

Lemma nodup_roots : NoDup roots3.
Proof.
 destruct distinct_roots as (D1 & D2 & D3 & D4 & D5 & D6).
 assert (RtoC nu <> RtoC mu) by (contradict D6; now apply RtoC_inj).
 repeat constructor; simpl; try tauto.
Qed.

Lemma ThePoly3_linfactors :
  ThePoly 3 ≅ linfactors roots3.
Proof.
 destruct (ThePoly_separated_roots_mu 3) as (l & Hl & ND & E & Hmu).
 fold mu in Hmu. rewrite E. apply linfactors_perm.
 destruct l as [|a [|b [|c [|d [|? l] ] ] ] ]; try (simpl; easy).
 clear Hl. simpl in Hmu. subst a.
 apply perm_skip.
 assert (In (RtoC nu) [RtoC mu;b;c;d]).
 { apply linfactors_roots. rewrite <- E, ThePoly_root_carac.
   rewrite !RtoC_pow, <- RtoC_plus. f_equal. apply (nu_carac 3).
   now apply Nat.odd_spec. }
 assert (EF : exists e f, Permutation [RtoC nu; e; f] [b;c;d]).
 { simpl in H. destruct H.
   + exfalso. apply RtoC_inj in H. lra'.
   + repeat destruct H; try easy; subst.
     * now exists c, d.
     * exists b, d. apply perm_swap.
     * exists b, c. apply perm_trans with [b;d;c].
       apply perm_swap. apply perm_skip, perm_swap. }
 destruct EF as (e & f & EF). rewrite <- EF. apply perm_skip.
 assert (EF' : Permutation [RtoC mu; b;c;d] [RtoC mu;RtoC nu; e; f]).
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
     rewrite !RtoC_pow, <- RtoC_plus in He. apply RtoC_inj in He.
     rewrite <- (P_root_equiv 3) in He.
     apply mu_or_nu in He.  2:now apply Nat.odd_spec.
     change (x = mu \/ x = nu) in He.
     destruct He as [-> | ->]; inversion_clear ND.
     + simpl in H; tauto.
     + inversion_clear H0. simpl in H1; tauto. }
 subst f. clear He' ND.
 assert (E0 := coef_compat 0 _ _ E).
 assert (E3 := coef_compat 3 _ _ E).
 unfold ThePoly,coef in E0,E3; simpl in E0,E3.
 ring_simplify in E0. field_simplify in E3.
 assert (E3' : (RtoC mu + RtoC nu + e + Cconj e = 1)%C).
 { rewrite Ceq_minus in E3. ring_simplify in E3.
   replace (RtoC (-1)) with (- C1)%C in E3 by lca.
   change (_+ - C1)%C with ((Cconj e+e+nu+mu)-1)%C in E3.
   rewrite <- Ceq_minus in E3. rewrite <- E3. lca. }
 clear E E3 He.
 assert (Hx : Re e = re_alpha).
 { apply RtoC_inj. rewrite re_alt.
   replace (e+Cconj e)%C with (C1-mu-nu)%C by (rewrite <- E3'; lca).
   unfold re_alpha. lca. }
 assert (Hm : ((Cmod e)^2 = (Cmod alpha)^2)).
 { apply RtoC_inj.
   rewrite alphamod2, <- RtoC_pow, Cmod_sqr.
   replace (tau/-nu) with ((-1)*(tau/nu)) by (field; lra').
   rewrite RtoC_mult, RtoC_div by lra'.
   rewrite E0, tau_mu, RtoC_inv by lra'. field.
   split; apply RtoC_neq; lra'. }
 assert (Hy : (Im e)^2 = im_alpha^2).
 { rewrite !Cmod2_alt, Hx in Hm. unfold alpha in Hm; simpl in Hm; lra. }
 clear E0 E3' Hm.
 rewrite <- !Rsqr_pow2 in Hy.
 apply Rsqr_eq in Hy.
 destruct Hy as [Hy|Hy]; destruct e as (x,y);
  unfold Cconj, alphabar, alpha in *; simpl in *; subst;
  rewrite ?Ropp_involutive; apply perm_swap || reflexivity.
Qed.

Lemma mu_is_Rroot : mu^4 = mu^3 + 1.
Proof.
 exact (mu_carac 3).
Qed.

Lemma mu_is_Croot : (mu^4 = mu^3 + 1)%C.
Proof.
 rewrite !RtoC_pow, <- RtoC_plus. f_equal. apply mu_is_Rroot.
Qed.

Lemma nu_is_Rroot : nu^4 = nu^3+1.
Proof.
 apply nu_carac. now apply Nat.odd_spec.
Qed.

Lemma nu_is_Croot : (nu ^4 = nu ^3 + 1)%C.
Proof.
 rewrite !RtoC_pow, <- RtoC_plus. f_equal. apply nu_is_Rroot.
Qed.

Lemma alpha_is_Croot : (alpha^4 = alpha^3 + 1)%C.
Proof.
 rewrite <- ThePoly_root_carac, ThePoly3_linfactors.
 apply linfactors_roots. simpl. tauto.
Qed.

Lemma alphabar_is_Croot : (alphabar^4 = alphabar^3 + 1)%C.
Proof.
 rewrite <- ThePoly_root_carac, ThePoly3_linfactors.
 apply linfactors_roots. simpl. tauto.
Qed.

Lemma A3_eqn_exists :
 exists (a b c d:C),
 forall n, RtoC (A 3 n) = (a*mu^n + b*nu^n + c*alpha^n + d*alphabar^n)%C.
Proof.
 destruct (coefs_LinCombA 3 roots3) as (v & H).
 - reflexivity.
 - apply nodup_roots.
 - apply ThePoly3_linfactors.
 - exists (v O O), (v 1 O)%nat, (v 2 O)%nat, (v 3 O)%nat.
   intros n. rewrite <- H. unfold roots3. simpl.
   rewrite scalprod_alt. unfold mkvect; simpl. lca.
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
    will be respectively [tau^4],[tau^5],[tau^6],[tau^3]
    (another numbering of letters would make that more uniform).
    For proving that and even more, we now consider the following
    differences :
*)

Definition Diff0 w := tau^4 * length w - nbocc 0 w.
Definition Diff1 w := tau^5 * length w - nbocc 1 w.
Definition Diff2 w := tau^6 * length w - nbocc 2 w.
Definition Diff3 w := tau^3 * length w - nbocc 3 w.

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
 rewrite tau4, tau5, tau6. ring_simplify.
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

Lemma diff0_alt n :
  diff0 n = f 3 n - tau * n.
Proof.
 unfold diff0, Diff0. rewrite take_length.
 rewrite <- count_nbocc.
 rewrite tau4. rewrite Rmult_minus_distr_r.
 rewrite <- (f_count_0 3 n) at 1 by easy. rewrite plus_INR. lra.
Qed.

Lemma diff3_alt n :
  diff3 n = tau^3 * n - (f 3^^3) n.
Proof.
 unfold diff3, Diff3. rewrite take_length.
 rewrite <- count_nbocc.
 now rewrite fs_count_k.
Qed.

Lemma diff1_alt n :
  diff1 n = tau^5 * n + (f 3^^2) n - f 3 n.
Proof.
 unfold diff1, Diff1. rewrite take_length.
 rewrite <- count_nbocc.
 change (f 3 n) with ((f 3^^1) n).
 rewrite (fs_count_above 3 1) by lia.
 rewrite count_above_S.
 rewrite (fs_count_above 3 2) by lia.
 rewrite plus_INR. lra.
Qed.

Lemma diff2_alt n :
  diff2 n = tau^6 * n + (f 3^^3) n - (f 3^^2) n.
Proof.
 unfold diff2, Diff2. rewrite take_length.
 rewrite <- count_nbocc.
 rewrite (fs_count_above 3 2) by lia.
 rewrite (fs_count_above 3 3) by lia.
 rewrite (count_above_S (kseq 3) 2).
 rewrite plus_INR. lra.
Qed.

(** Equations giving Diff0 and co after a substitution [ksubst 3]. *)

Lemma Diff0_ksubst3 w :
  Diff0 (apply (ksubst 3) w) = tau * Diff3 w.
Proof.
 unfold Diff0, Diff3.
 rewrite len_ksubst3, plus_INR.
 destruct (nbocc_ksubst3 w) as (-> & _ & _ & _).
 ring_simplify. unfold Rminus. rewrite Rplus_assoc. f_equal.
 rewrite tau4. lra.
Qed.

Lemma Diff3_ksubst3 w :
  List.Forall (fun a => a <= 3)%nat w ->
  Diff3 (apply (ksubst 3) w) = - tau^3 * Diff3 w - Diff0 w - Diff1 w.
Proof.
 intros H.
 unfold Diff0, Diff1, Diff3.
 rewrite len_ksubst3.
 destruct (nbocc_ksubst3 w) as (_ & _ & _ & ->).
 rewrite !plus_INR.
 ring_simplify. rewrite tau6, tau5, tau4. ring_simplify.
 rewrite !len_nbocc_0123 by trivial. rewrite !plus_INR. ring.
Qed.

Lemma Diff1_ksubst3 w :
  List.Forall (fun a => a <= 3)%nat w ->
  Diff1 (apply (ksubst 3) w) = - tau^5 * Diff3 w + Diff0 w.
Proof.
 intros H.
 unfold Diff0, Diff1, Diff3.
 rewrite len_ksubst3.
 destruct (nbocc_ksubst3 w) as (_ & -> & _ & _).
 rewrite !plus_INR.
 ring_simplify. replace (tau^8) with ((tau^4)^2) by ring.
 rewrite tau5, tau4. ring_simplify.
 rewrite !len_nbocc_0123 by trivial. rewrite !plus_INR. ring.
Qed.

(** Same, expressed via matrix *)

Definition mkvect n l : Vector n := list2D_to_matrix (map (fun x => [x]) l).
Definition mkvectR n l : Vector n := mkvect n (map RtoC l).

Definition Diffs w : Vector 3 := mkvectR 3 [Diff3 w; Diff0 w; Diff1 w].
Definition diffs n : Vector 3 := mkvectR 3 [diff3 n; diff0 n; diff1 n].

Definition B : Square 3 :=
 list2D_to_matrix [ [-tau^3;-C1;-C1];[RtoC tau;C0;C0];[-tau^5;C1;C0] ]%C.

Lemma WF_B : WF_Matrix B.
Proof.
 apply WF_list2D_to_matrix; simpl; intuition; subst; auto.
Qed.

Lemma WF_mkvect n l : length l = n -> WF_Matrix (mkvect n l).
Proof.
 intros.
 apply WF_list2D_to_matrix; simpl.
 - now rewrite map_length.
 - intros li. rewrite in_map_iff. now intros (x & <- & _).
Qed.

Lemma WF_mkvectR n l : length l = n -> WF_Matrix (mkvectR n l).
Proof.
 intros. apply WF_mkvect. now rewrite map_length.
Qed.

Lemma WF_Diffs w : WF_Matrix (Diffs w).
Proof.
 now apply WF_mkvectR.
Qed.

Lemma WF_diffs n : WF_Matrix (diffs n).
Proof.
 now apply WF_mkvectR.
Qed.

Lemma diffs_alt n : diffs n = Diffs (take n (kseq 3)).
Proof.
 reflexivity.
Qed.

Lemma Diffs_ksubst3 w :
  List.Forall (fun a => a <= 3)%nat w ->
  Diffs (apply (ksubst 3) w) = B × Diffs w.
Proof.
 intros F. apply mat_equiv_eq; auto using WF_Diffs, WF_mult, WF_B.
 intros i j Hi Hj. replace j with O by lia. clear j Hj.
 destruct i as [|[|[|?] ] ]; try lia; clear Hi;
  unfold Diffs, B, list2D_to_matrix, Mmult; cbn -[Cpow].
 - rewrite Diff3_ksubst3 by trivial.
   rewrite !RtoC_minus, !RtoC_mult, !RtoC_pow, !RtoC_opp. ring.
 - rewrite Diff0_ksubst3. rewrite !RtoC_mult. ring.
 - rewrite Diff1_ksubst3 by trivial.
   rewrite !RtoC_plus, !RtoC_mult, !RtoC_pow, !RtoC_opp. ring.
Qed.

Fixpoint Mpow {n} (M:Square n) m : Square n :=
 match m with
 | O => I n
 | S m => M × Mpow M m
 end.

Lemma WF_Mpow {n} (M:Square n) m : WF_Matrix M -> WF_Matrix (Mpow M m).
Proof.
 induction m; simpl; auto using WF_I, WF_mult.
Qed.

(* Initial vector of differences *)
Definition V0 : Vector 3 := mkvectR 3 [tau^3-1; tau^4; tau^5].

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
 list2D_to_matrix [ [-alpha^2;alpha+1;alpha];
                    [-alphabar^2;alphabar+1; alphabar];
                    [-nu^2;nu+1;RtoC nu] ]%C.

Definition D : Square 3 :=
 list2D_to_matrix [ [alpha;C0;C0]; [C0;alphabar;C0]; [C0;C0;RtoC nu] ]%C.

Definition Dn n : Square 3 :=
 list2D_to_matrix
   [ [alpha^n;C0;C0]; [C0;alphabar^n;C0]; [C0;C0;(RtoC nu)^n] ]%C.

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

Lemma P_factor_mu (x:C) :
 (x^4-x^3-1 = (x - mu) * (x^3 + tau^3*x^2 + tau^2*x + tau))%C.
Proof.
 ring_simplify. rewrite mu_tau, RtoC_inv by lra'.
 field_simplify; try (apply RtoC_neq; lra').
 rewrite RtoC_pow, tau4, RtoC_minus.
 field; try (apply RtoC_neq; lra').
Qed.

Lemma P_factor_mu_eq0 (x:C) :
  x<>mu -> (x^4 = x^3+1)%C -> (x^3 + tau^3*x^2 + tau^2*x + tau = 0)%C.
Proof.
 intros Hx E.
 rewrite Ceq_minus in E.
 replace (_-_)%C with (x^4-x^3-1)%C in E by ring.
 rewrite P_factor_mu in E. apply Cmult_integral in E.
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
 apply mat_equiv_eq; auto using WF_mult, WF_U, WF_B, WF_D.
 intros i j Hi Hj.
 assert (N : RtoC tau <> C0).
 { intro E. apply RtoC_inj in E. now apply tau_nz. }
 destruct i as [|[|[|?] ] ]; try lia; clear Hi;
  destruct j as [|[|[|?] ] ]; try lia; clear Hj;
  unfold U, B, D, list2D_to_matrix, Mmult; cbn -[nu pow Cpow];
  rewrite !Cplus_0_l; try ring;
  rewrite Ceq_minus; ring_simplify;
  rewrite !(RtoC_pow tau), tau5, RtoC_minus, <- !RtoC_pow;
  ring_simplify.
 - rewrite <- (P_factor_mu_eq0 alpha);
    [ ring | apply distinct_roots | apply alpha_is_Croot].
 - rewrite <- (P_factor_mu_eq0 alphabar);
    [ ring | apply distinct_roots | apply alphabar_is_Croot].
 - rewrite <- (P_factor_mu_eq0 nu);
    [ ring | apply RtoC_inj_neq; try apply distinct_roots | apply nu_is_Croot].
Qed.

Definition detU :=
 ((alpha-alphabar)*nu^2+(alphabar^2-alpha^2)*nu
  +alpha*alphabar*(alpha-alphabar))%C.

Lemma detU_alt :
 detU = (2*im_alpha*Ci*(Cmod(alpha)^2+nu^2+2*(-nu)*re_alpha))%C.
Proof.
 unfold detU. change alphabar with (Cconj alpha).
 rewrite im_alt'. change (Im alpha) with im_alpha.
 rewrite <- Cmod2_conj.
 replace ((Cconj alpha)^2-alpha^2)%C with (-4*Ci*im_alpha*re_alpha)%C.
 2:{ rewrite <- (re_im_conj alpha).
     change (Re alpha) with re_alpha.
     change (Im alpha) with im_alpha.
     rewrite <- (re_im_id alpha).
     change (Re alpha) with re_alpha.
     change (Im alpha) with im_alpha. ring. }
 rewrite <- !RtoC_pow. ring.
Qed.

Lemma detU_nz : detU <> 0.
Proof.
 rewrite detU_alt. intros E. rewrite !Cmult_integral in E.
 repeat destruct E as [E|E]; try apply RtoC_inj in E; try lra.
 - now apply im_alpha_nz.
 - compute in E. injection E; lra.
 - rewrite !RtoC_pow, <- !RtoC_opp, <- !RtoC_mult, <- !RtoC_plus in E.
   apply RtoC_inj in E. symmetry in E. revert E. apply Rlt_not_eq.
   repeat apply Rplus_lt_0_compat.
   + rewrite alphamod2. apply Rmult_lt_0_compat. lra'.
     apply Rinv_0_lt_compat; lra'.
   + rewrite <- Rsqr_pow2. apply Rlt_0_sqr; lra'.
   + repeat apply Rmult_lt_0_compat; lra'.
Qed.

Definition invU_detU : Square 3 :=
 list2D_to_matrix
  [ [ nu-alphabar; -(nu-alpha); alphabar-alpha];
    [-alphabar*nu*(nu-alphabar); alpha*nu*(nu-alpha);
       -alpha*alphabar*(alphabar-alpha)];
    [(nu-alphabar)*(alphabar*nu+nu+alphabar);
       -(nu-alpha)*(alpha*nu+nu+alpha);
       (alphabar-alpha)*(alpha*alphabar+alphabar+alpha)] ]%C.

Definition invU := /detU .* invU_detU.

Lemma WF_invU_detU : WF_Matrix invU_detU.
Proof.
 apply WF_list2D_to_matrix; simpl; intuition; subst; auto.
Qed.

Lemma WF_invU : WF_Matrix invU.
Proof.
 apply WF_scale, WF_invU_detU.
Qed.

Lemma invU_detU_U : invU_detU × U = detU .* (I 3).
Proof.
 apply mat_equiv_eq; auto using WF_mult, WF_U, WF_invU_detU, WF_scale, WF_I.
 intros i j Hi Hj.
 destruct i as [|[|[|?] ] ]; try lia; clear Hi;
  destruct j as [|[|[|?] ] ]; try lia; clear Hj;
  unfold U, invU_detU, detU, list2D_to_matrix, Mmult, scale, I;
  cbn -[nu Cpow pow]; ring.
Qed.

Lemma U_invU_detU : U × invU_detU = detU .* (I 3).
Proof.
 apply mat_equiv_eq; auto using WF_mult, WF_U, WF_invU_detU, WF_scale, WF_I.
 intros i j Hi Hj.
 destruct i as [|[|[|?] ] ]; try lia; clear Hi;
  destruct j as [|[|[|?] ] ]; try lia; clear Hj;
  unfold U, invU_detU, detU, list2D_to_matrix, Mmult, scale, I;
  cbn -[nu Cpow pow]; ring.
Qed.

Lemma invU_U : invU × U = I 3.
Proof.
 unfold invU.
 rewrite Mscale_mult_dist_l, invU_detU_U.
 rewrite Mscale_assoc.
 replace (/detU * detU)%C with C1. apply Mscale_1_l.
 symmetry. apply Cinv_l. apply detU_nz.
Qed.

Lemma U_invU : U × invU = I 3.
Proof.
 unfold invU.
 rewrite Mscale_mult_dist_r, U_invU_detU.
 rewrite Mscale_assoc.
 replace (/detU * detU)%C with C1. apply Mscale_1_l.
 symmetry. apply Cinv_l. apply detU_nz.
Qed.

Lemma B_diag : B = invU × D × U.
Proof.
 rewrite Mmult_assoc, <- UB_DU, <- Mmult_assoc, invU_U, Mmult_1_l;
   auto using WF_B.
Qed.

Lemma Dn_0 : Dn 0 = I 3.
Proof.
 apply mat_equiv_eq; auto using WF_Dn, WF_I.
 intros i j Hi Hj.
 destruct i as [|[|[|?] ] ]; try lia; clear Hi;
  destruct j as [|[|[|?] ] ]; try lia; clear Hj;
  unfold I, D, list2D_to_matrix; cbn -[nu]; try ring.
Qed.

Lemma Dn_S n : Dn (S n) = D × Dn n.
Proof.
 apply mat_equiv_eq; auto using WF_mult, WF_D, WF_Dn.
 intros i j Hi Hj.
 destruct i as [|[|[|?] ] ]; try lia; clear Hi;
  destruct j as [|[|[|?] ] ]; try lia; clear Hj;
  unfold Dn, D, list2D_to_matrix, Mmult; cbn -[nu]; try ring.
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

Definition UV0a := (alpha^3/(alpha-1))%C.
Definition UV0abar := (alphabar^3/(alphabar-1))%C.
Definition UV0nu := (nu^3/(nu-1))%C.

Definition coefa_detU := ((nu-alphabar)*UV0a)%C.
Definition coefnu_detU := ((alphabar-alpha)*UV0nu)%C.
Definition vecta := mkvect 3 [C1;-nu*alphabar;nu*alphabar+nu+alphabar]%C.
Definition vectabar := mkvect 3 [C1;-nu*alpha;nu*alpha+nu+alpha]%C.
Definition vectnu := mkvect 3 [C1;-(Cmod alpha)^2;(Cmod alpha)^2+2*re_alpha]%C.

Definition coefsa := (/detU * coefa_detU) .* vecta.
Definition coefsabar := (/detU * (-Cconj coefa_detU)) .* vectabar.
Definition coefsnu := (/detU * coefnu_detU) .* vectnu.

Lemma U_V0_alt :
  U × V0 = mkvect 3 [UV0a;UV0abar;UV0nu]%C.
Proof.
 apply mat_equiv_eq.
 - apply WF_mult. apply WF_U. now apply WF_mkvectR.
 - now apply WF_mkvect.
 - intros i j Hi Hj.
   destruct i as [|[|[|?] ] ]; try lia; clear Hi;
   destruct j as [|? ]; try lia; clear Hj;
   unfold U, V0, mkvectR, mkvect, list2D_to_matrix, Mmult, scale;
    cbn -[nu Cpow pow];
    rewrite tau4, tau5; rewrite !RtoC_minus, <- !RtoC_pow.
   + rewrite <- (P_factor_mu_eq0 alpha);
       [ | apply distinct_roots | apply alpha_is_Croot ].
     ring_simplify.
     assert (N : (alpha-1 <> 0)%C).
     { apply Cminus_eq_contra. unfold alpha. intros [= E E'].
       generalize re_alpha_approx; lra. }
     unfold UV0a.
     apply Cmult_eq_reg_l with (alpha-1)%C; try field_simplify; trivial.
     rewrite alpha_is_Croot; field.
   + rewrite <- (P_factor_mu_eq0 alphabar);
       [ | apply distinct_roots | apply alphabar_is_Croot ].
     ring_simplify.
     assert (N : (alphabar-1 <> 0)%C).
     { apply Cminus_eq_contra. unfold alphabar. intros [= E E'].
       generalize re_alpha_approx; lra. }
     unfold UV0abar.
     apply Cmult_eq_reg_l with (alphabar-1)%C; try field_simplify; trivial.
     rewrite alphabar_is_Croot; field.
   + rewrite <- (P_factor_mu_eq0 nu);
       [ | apply RtoC_inj_neq,distinct_roots | apply nu_is_Croot ].
     ring_simplify.
     assert (N : (nu-1 <> 0)%C).
     { apply Cminus_eq_contra. intros [= E]; lra'. }
     unfold UV0nu.
     apply Cmult_eq_reg_l with (nu-1)%C; try field_simplify; trivial.
     rewrite nu_is_Croot; field.
Qed.

Lemma alphabar_conj : Cconj alphabar = alpha.
Proof.
 unfold alpha, alphabar, Cconj; simpl; f_equal; lra.
Qed.

Lemma alpha_conj : Cconj alpha = alphabar.
Proof.
 unfold alpha, alphabar, Cconj; simpl; f_equal; lra.
Qed.

Lemma UV0a_conj : Cconj UV0a = UV0abar.
Proof.
 unfold UV0abar, UV0a.
 rewrite Cdiv_conj, Cconj_minus_distr, Cpow_conj, alpha_conj.
 - f_equal. f_equal. lca.
 - apply Cminus_eq_contra. unfold alpha. intros [= E E'].
   generalize re_alpha_approx; lra.
Qed.

(** diffs for (A 3) numbers are linear combinations of little roots *)

Lemma diffs_A3_powers n :
  diffs (A 3 n) =
   (alpha^n .* coefsa .+ alphabar^n .* coefsabar .+ nu^n .* coefsnu)%C.
Proof.
 rewrite diffs_A3, Bn_diag.
 unfold invU, coefsa, coefsabar, coefsnu.
 rewrite !Mscale_mult_dist_l.
 rewrite !Mscale_assoc, !Cmult_assoc, !(Cmult_comm _ (/detU)),
  <-Cmult_assoc, <- !Mscale_assoc, <- !Mscale_plus_distr_r.
 f_equal.
 rewrite Mmult_assoc, U_V0_alt.
 unfold coefa_detU, coefnu_detU.
 apply mat_equiv_eq.
 - repeat apply WF_mult; try apply WF_scale;
   auto using WF_Dn, WF_invU_detU.
   now apply WF_mkvect.
 - repeat apply WF_plus; repeat apply WF_scale; now apply WF_mkvect.
 - intros i j Hi Hj.
   destruct i as [|[|[|?] ] ]; try lia; clear Hi;
   destruct j as [|?]; try lia; clear Hj;
   unfold Dn, invU_detU, vecta, vectabar, vectnu, mkvect,
    list2D_to_matrix, Mplus, Mmult, scale;
   cbn -[nu Cpow pow]; apply Ceq_minus; ring_simplify.
   + rewrite Cconj_mult_distr, Cconj_minus_distr, Cconj_R, alphabar_conj,
      UV0a_conj. ring.
   + rewrite Cconj_mult_distr, Cconj_minus_distr, Cconj_R, alphabar_conj,
      UV0a_conj. ring_simplify.
     rewrite (RtoC_pow (Cmod _)), Cmod2_conj, alpha_conj. ring.
   + rewrite Cconj_mult_distr, Cconj_minus_distr, Cconj_R, alphabar_conj,
      UV0a_conj. ring_simplify.
     rewrite (RtoC_pow (Cmod _)), Cmod2_conj, alpha_conj. ring_simplify.
     change re_alpha with (Re alpha). rewrite re_alt, alpha_conj.
     field.
Qed. (* TODO too slow *)

(* In particular for diff0 : *)

Definition coefa0 := coefsa 1%nat 0%nat.
Definition coefnu0 := Re (coefsnu 1%nat 0%nat).

Lemma diff0_A3_powers n :
  diff0 (A 3 n) = 2 * Re (coefa0 * alpha^n) + coefnu0 * nu^n.
Proof.
  apply RtoC_inj.
  change (RtoC (diff0 (A 3 n))) with (diffs (A 3 n) 1%nat 0%nat).
  rewrite diffs_A3_powers.
  rewrite RtoC_plus, !RtoC_mult, <- !RtoC_pow.
  rewrite re_alt, Cconj_mult_distr, Cpow_conj, alpha_conj.
  unfold Mplus, scale; cbn -[nu Cpow pow Re].
  unfold coefa0, coefnu0.
  field_simplify. f_equal; f_equal. f_equal.
  - admit. (* coefsabar est bien Cconj coefsa *)
  - admit. (* coefsnu est bien reel *)
Admitted.

(** Now, any arbitrary number [n] is a sum of [A 3] numbers by Zeckendorf
    theorem (cf. [GenFib.decomp]). So [diffs n] will be a sum of powers
    of [alpha], [alphabar], [nu]. *)

(* TODO: factor with LimCase2 ? *)
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
   Rlistsum (List.map (fun n => 2*Re(coefa0 * alpha^n)%C+coefnu0*nu^n)
                      (decomp 3 n)).
Proof.
 unfold diff0.
 rewrite decomp_prefix_kseq.
 rewrite Diff0_concat, List.map_map, List.map_rev, Rlistsum_rev.
 f_equal.
 apply List.map_ext; intros.
 rewrite <- kseq_take_A. apply diff0_A3_powers.
Qed.

(* TODO continuer
Lemma diff0_decomp_eqn' n :
  diff0 n =
   2*Re (coefa0 * Clistsum (List.map (Cpow alpha) (decomp 2 n))).
Proof.
 rewrite diff0_decomp_eqn.
 induction decomp; cbn -[Re].
 - rewrite Cmult_0_r. cconst.
 - rewrite Cmult_plus_distr_l, re_plus, Rmult_plus_distr_l.
   f_equal. apply IHl.
Qed.

(** With the previous expression of [diff0 n], we will progressively bound it
    by some constant independent from [n]. *)

Lemma diff0_decomp_le n :
 Rabs (diff0 n) <=
  2 * Cmod coefa0 * Rlistsum (List.map (pow (Cmod alpha)) (decomp 2 n)).
Proof.
 rewrite diff0_decomp_eqn.
 induction decomp.
 - simpl. rewrite Rabs_R0. lra.
 - cbn -[Re].
   eapply Rle_trans. apply Rabs_triang.
   rewrite Rmult_plus_distr_l.
   apply Rplus_le_compat; [|apply IHl].
   rewrite Rabs_mult. rewrite Rabs_right by lra.
   rewrite Rmult_assoc.
   apply Rmult_le_compat_l; try lra.
   rewrite <- Cmod_pow, <-Cmod_mult.
   apply re_le_Cmod.
Qed.

Lemma sum_pow_cons k l n r :
  O<>k -> 0<=r<1 -> Delta k (n::l) ->
  Rlistsum (List.map (pow r) (n::l)) <= r^n/(1-r^k).
Proof.
 intros Hk Hr.
 assert (H3 : 0 <= r^k < 1).
 { apply pow_lt_1_compat. lra. lia. }
 revert n.
 induction l.
 - intros n _. cbn -[pow].
   rewrite Rplus_0_r.
   apply Rcomplements.Rle_div_r; try lra.
   rewrite <- (Rmult_1_r (r^n)) at 2.
   apply Rmult_le_compat_l; try lra.
   apply pow_le; lra.
 - intros n. inversion_clear 1.
   change (Rlistsum _) with (r^n + Rlistsum (List.map (pow r) (a::l))).
   eapply Rle_trans. eapply Rplus_le_compat_l. apply IHl; eauto.
   apply Rcomplements.Rle_div_r; try lra.
   field_simplify; try lra.
   rewrite <- Ropp_mult_distr_l, <- pow_add.
   assert (r^a <= r^(n+k)). { apply Rle_pow_low; auto. }
   lra.
Qed.

Lemma sum_pow k l r :
  O<>k -> 0<=r<1 -> Delta k l ->
  Rlistsum (List.map (pow r) l) <= /(1-r^k).
Proof.
 intros Hk Hr D.
 assert (H3 : 0 <= r^k < 1).
 { apply pow_lt_1_compat. lra. lia. }
 destruct l as [|n l].
 - cbn -[pow].
   rewrite <- (Rmult_1_l (/ _)).
   apply Rcomplements.Rle_div_r; try lra.
 - eapply Rle_trans. apply (sum_pow_cons k); auto.
   rewrite <- (Rmult_1_l (/ _)).
   apply Rmult_le_compat_r.
   rewrite <- (Rmult_1_l (/ _)).
   apply Rcomplements.Rle_div_r; try lra.
   rewrite <-(pow1 n).
   apply pow_maj_Rabs. rewrite Rabs_right; lra.
Qed.

Lemma diff0_indep_bound n :
 Rabs (diff0 n) <= 2 * Cmod coefa0 / (1 - Cmod alpha^3).
Proof.
 eapply Rle_trans. apply diff0_decomp_le.
 unfold Rdiv.
 apply Rmult_le_compat_l.
 - generalize (Cmod_ge_0 coefa0). lra.
 - apply sum_pow; try lia; try apply decomp_delta.
   split; try apply Cmod_ge_0.
   apply Rlt_pow2_inv; try lra.
   rewrite alphamod2. generalize tau_approx. lra.
Qed.

(** Experimentally, this first bound is around 1.112.
    Having this finite bound is enough to prove that the frequency
    of letter 0 is [tau^3] and that [h n / n] converges towards tau.
*)

Lemma lim_diff0_div_n : is_lim_seq (fun n => diff0 n / n) 0.
Proof.
 eapply is_lim_seq_bound. apply diff0_indep_bound.
Qed.

Lemma frequency_0 :
 is_lim_seq (fun n => count (kseq 2) 0 n / n) (tau^3).
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with (u := fun n => tau^3 - diff0 (S n) / S n).
 - intros n.
   unfold diff0, Diff0. rewrite take_length.
   rewrite <- count_nbocc. field. apply RSnz.
 - replace (Rbar.Finite (tau^3)) with (Rbar.Finite (tau^3 + -0))
    by (f_equal; lra).
   eapply is_lim_seq_plus'. apply is_lim_seq_const.
   change (Rbar.Finite (-0)) with (Rbar.Rbar_opp 0).
   apply -> is_lim_seq_opp.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff0 n / n)).
   apply lim_diff0_div_n.
Qed.

Lemma Lim_h_div_n :
 is_lim_seq (fun n => h n / n) tau.
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with (u := fun n => tau + diff0 (S n) / S n).
 - intros n. rewrite diff0_alt. field. apply RSnz.
 - replace (Rbar.Finite tau) with (Rbar.Finite (tau + 0)) by (f_equal; lra).
   eapply is_lim_seq_plus'. apply is_lim_seq_const.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff0 n / n)).
   apply lim_diff0_div_n.
Qed.

(** NB : Classical reals are now Dedekind cuts,
    just 4 logical axioms remaining :)
*)

(* Print Assumptions Lim_H_div_n. *)


(** With some more sweat, we prove now a better bound, strictly
    below 1, with nice consequences :

     - [h n = nat_part (tau*n)+{0,1}]
     - [h] is quasi-additive [forall n p, -2 <= h (n+p) - h n - h p <= 2]
*)

Lemma re_alpha2 : Re (alpha^2) = re_alpha^2 - im_alpha^2.
Proof.
 simpl. ring.
Qed.

Lemma re_alpha2_tau : Re (alpha^2) = -tau*(1+tau)/2.
Proof.
 rewrite re_alpha2. rewrite re_alpha_alt, im_alpha_2.
 field_simplify.
 rewrite tau4. field.
Qed.

Lemma im_alpha2 : Im (alpha^2) = 2*re_alpha*im_alpha.
Proof.
 simpl. ring.
Qed.

Definition alpha3 := alpha_is_root.

Lemma alpha4 : (alpha^4 = 1 + alpha + alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha3. ring_simplify. rewrite alpha3. ring.
Qed.

Lemma alpha5 : (alpha^5 = 1 + alpha + 2*alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha4. ring_simplify. rewrite alpha3. ring.
Qed.

Lemma alpha6 : (alpha^6 = 2 + alpha + 3*alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha5. ring_simplify. rewrite alpha3. ring.
Qed.

Lemma alpha7 : (alpha^7 = 3 + 2*alpha + 4*alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha6. ring_simplify. rewrite alpha3. ring.
Qed.

Lemma alpha8 : (alpha^8 = 4 + 3*alpha + 6*alpha^2)%C.
Proof.
 rewrite Cpow_S, alpha7. ring_simplify. rewrite alpha3. ring.
Qed.

Lemma cmod2_trinom_alpha (a b c : R) :
 (Cmod (a + b*alpha + c*alpha^2)%C)^2 =
 (1/4)*((2*a - b*tau^2 - c*tau*(1+tau))^2 + tau*(3+tau)*(b-c*tau^2)^2).
Proof.
 rewrite Cmod2_alt.
 rewrite !re_plus, !im_plus, re_RtoC, im_RtoC.
 rewrite !re_scal_l, !im_scal_l, re_alpha2_tau, im_alpha2.
 simpl Im. simpl Re.
 replace (0 + _ + _) with (im_alpha * (b + c * (2*re_alpha))) by ring.
 rewrite Rpow_mult_distr, im_alpha_2, re_alpha_alt. field.
Qed.

Ltac solve_trinom a b c :=
  replace ((Cmod _)^2) with (Cmod (a+b*alpha+c*alpha^2)%C^2);
  [ rewrite (cmod2_trinom_alpha a b c);
    field_simplify; rewrite ?tau6, ?tau5, ?tau4, ?tau3; field_simplify
  | f_equal; f_equal;
    rewrite ?alpha3, ?alpha4, ?alpha5, ?alpha6, ?alpha7, ?alpha8; ring ].

Definition max3pack := Cmod (1+alpha^3+alpha^7)%C.

Lemma max3pack_eqn : max3pack^2 = 15 - 11*tau - 10*tau^2.
Proof.
 unfold max3pack. solve_trinom 5 2 5. field.
Qed.

(* Curious note : all the trinoms we consider lead to N - M*tau - K*tau^2
   except (Cmod (1+alpha^4+alpha^8)%C)^2 = 8 + 2*tau - 17*tau^2. *)

(* TODO : how to improve the next lemma ? *)
Ltac finish B n := specialize (B n); simpl in B; lia.
Lemma best_3pack_0 l :
  Delta 3 (O::l) -> Below l 9 ->
  Cmod (Clistsum (List.map (Cpow alpha) (O::l))) <= max3pack.
Proof.
 intros D B.
 apply Rle_pow2_inv; [apply Cmod_ge_0| rewrite max3pack_eqn].
 assert (T := tau_approx).
 assert (T2 := tau2_approx).
 inversion D; subst; cbn -[Cpow pow]; simpl (alpha^0)%C.
 { rewrite Cplus_0_r, Cmod_1. lra. (* 1 *) }
 destruct (Nat.eq_dec n 3) as [->|?].
 { inversion H2; subst; cbn -[Cpow pow].
   { solve_trinom 2 0 1. lra. (* 1 + alpha^3 *) }
   destruct (Nat.eq_dec n 6) as [->|?].
   { inversion H4; subst; cbn -[Cpow pow]; [|finish B n].
     solve_trinom 4 1 4. lra. (* 1 + alpha^3 + alpha^6 *) }
   destruct (Nat.eq_dec n 7) as [->|?].
   { inversion H4; subst; cbn -[Cpow pow]; [|finish B n].
     (* 1 + alpha^3 + alpha^7 *)
     apply Req_le. now rewrite Cplus_0_r, Cplus_assoc, <- max3pack_eqn. }
   destruct (Nat.eq_dec n 8) as [->|?]; [|finish B n].
   { inversion H4; subst; cbn -[Cpow pow]; [|finish B n].
     solve_trinom 6 3 7. lra. (* 1+alpha^3+alpha^8 *) }}
 destruct (Nat.eq_dec n 4) as [->|?].
 { inversion H2; subst; cbn -[Cpow pow].
   { solve_trinom 2 1 1. lra. (* 1+alpha^4*) }
   destruct (Nat.eq_dec n 7) as [->|?].
   { inversion H4; subst; cbn -[Cpow pow]; [|finish B n].
     solve_trinom 5 3 5. lra. (* 1+alpha^4+alpha^7 *) }
   destruct (Nat.eq_dec n 8) as [->|?]; [|finish B n].
   { inversion H4; subst; cbn -[Cpow pow]; [|finish B n].
     solve_trinom 6 4 7. lra. (* 1+alpha^4+alpha^8 *) }}
 destruct (Nat.eq_dec n 5) as [->|?].
 { inversion H2; subst; cbn -[Cpow pow].
   { solve_trinom 2 1 2. lra. (* 1+alpha^5 *) }
   destruct (Nat.eq_dec n 8) as [->|?]; [|finish B n].
   { inversion H4; subst; cbn -[Cpow pow]; [|finish B n].
     solve_trinom 6 4 8. lra. (* 1+alpha^5+alpha^8 *) }}
 destruct (Nat.eq_dec n 6) as [->|?].
 { inversion H2; subst; cbn -[Cpow pow]; [|finish B n].
   solve_trinom 3 1 3. lra. (* 1+alpha^6 *) }
 destruct (Nat.eq_dec n 7) as [->|?].
 { inversion H2; subst; cbn -[Cpow pow]; [|finish B n].
   solve_trinom 4 2 4. lra. (* 1+alpha^7 *) }
 destruct (Nat.eq_dec n 8) as [->|?]; [|finish B n].
 { inversion H2; subst; cbn -[Cpow pow]; [|finish B n].
   solve_trinom 5 3 6. lra. (* 1+alpha^8 *) }
Qed.

Lemma Clistsum_factor p l :
 Clistsum (List.map (fun n => alpha^(p+n))%C l) =
 (alpha^p * Clistsum (List.map (Cpow alpha) l))%C.
Proof.
 induction l; cbn -[Cpow].
 - ring.
 - change (List.fold_right Cplus 0)%C with Clistsum. rewrite IHl.
   rewrite Cpow_add_r. ring.
Qed.

Lemma Clistsum_factor_above p l :
 (forall n, List.In n l -> p <= n)%nat ->
 Clistsum (List.map (Cpow alpha) l) =
 (alpha^p * Clistsum (List.map (Cpow alpha) (List.map (decr p) l)))%C.
Proof.
 induction l as [|a l IH]; cbn -[Cpow]; intros Hl.
 - ring.
 - change (List.fold_right Cplus 0)%C with Clistsum. rewrite IH by intuition.
   replace a with ((a-p)+p)%nat at 1 by (specialize (Hl a); lia).
   rewrite Cpow_add_r. unfold decr at 2. ring.
Qed.

Lemma best_3pack l :
  Delta 3 l -> Below l 9 ->
  Cmod (Clistsum (List.map (Cpow alpha) l)) <= max3pack.
Proof.
 intros D B.
 destruct l as [|a l].
 - cbn -[Cpow]. rewrite Cmod_0. apply Cmod_ge_0.
 - revert l D B. induction a as [|a IH]; intros l D B.
   + apply best_3pack_0; auto. unfold Below in *. simpl in *. intuition.
   + replace (S a::l)%list with (List.map S (a :: List.map pred l))%list.
     2:{ simpl. f_equal. rewrite List.map_map.
         rewrite <- (List.map_id l) at 2. apply List.map_ext_in.
         intros b Hb.
         assert (b<>O); try lia.
         { contradict Hb. subst b.
           apply (@Delta_nz' 3 (S a) l); auto; try lia. }}
     rewrite List.map_map, (Clistsum_factor 1), Cmod_mult, Cpow_1_r.
     set (l' := List.map pred l).
     eapply Rle_trans. 2:apply (IH l').
     * rewrite <- (Rmult_1_l (Cmod (Clistsum _))) at 2.
       apply Rmult_le_compat_r; try apply Cmod_ge_0.
       apply Rle_pow2_inv; try lra.
       rewrite alphamod2. generalize tau_approx; lra.
     * unfold l'. clear l'.
       destruct l as [|b l].
       { simpl; constructor. }
       { inversion_clear D. simpl. constructor. lia.
         apply (@Delta_pred 3 (b::l)); auto.
         apply (@Delta_nz' 3 a (b::l)); try lia.
         constructor; auto; try lia. }
       { unfold Below in *. intros y [->|Hy].
         - specialize (B (S y)). simpl in B; lia.
         - unfold l' in *. clear l'.
           rewrite List.in_map_iff in Hy. destruct Hy as (x & <- & Hx).
           assert (x < 9)%nat by (apply (B x); simpl; intuition).
           lia. }
Qed.

Lemma alphamod_lt : 0 < Cmod alpha < 1.
Proof.
 split.
 - apply Cmod_gt_0. unfold alpha. injection 1 as H H'. now apply re_alpha_nz.
 - apply Rlt_pow2_inv; try lra.
   rewrite alphamod2. generalize tau_approx; lra.
Qed.

Lemma alphamod9_lt : 0 < Cmod alpha^9 < 1.
Proof.
 assert (H := alphamod_lt).
 split.
 - apply pow_lt; lra.
 - change ((Cmod alpha)^9) with ((Cmod alpha)*(Cmod alpha)^8).
   apply Rle_lt_trans with (Cmod alpha * 1); try lra.
   apply Rmult_le_compat_l; try lra.
   rewrite <- (pow1 8). apply pow_incr. lra.
Qed.

Lemma Delta_map_decr p k l :
  (forall n, List.In n l -> k <= n)%nat ->
  Delta p l -> Delta p (List.map (decr k) l).
Proof.
 induction l as [|a l IH]; simpl; auto.
 - intros H. inversion 1; subst; constructor.
   + unfold decr. specialize (H a). lia.
   + apply IH; auto.
Qed.

Lemma Clistsum_delta_below N l :
  Delta 3 l -> Below l N ->
  Cmod (Clistsum (List.map (Cpow alpha) l)) <=
   max3pack / (1 - Cmod alpha ^9).
Proof.
 revert l.
 induction N as [N IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases N 9).
 - clear IH. intros l D B.
   eapply Rle_trans. apply best_3pack; auto.
   unfold Below in *. intros y Hy. specialize (B y Hy). lia.
   rewrite <- (Rmult_1_r max3pack) at 1. unfold Rdiv.
   apply Rmult_le_compat_l; try apply Cmod_ge_0.
   rewrite <- (Rmult_1_l (/ _)).
   assert (P := Cmod_ge_0 alpha).
   apply Rcomplements.Rle_div_r; generalize alphamod9_lt; lra.
 - intros l D B. destruct (cut_lt_ge 9 l) as (l1,l2) eqn:E.
   assert (D' := D).
   assert (E' := cut_app 9 l). rewrite E in E'. rewrite <- E' in D',B |- *.
   rewrite Delta_app_iff in D'. destruct D' as (D1 & D2 & D3).
   rewrite List.map_app, Clistsum_app.
   eapply Rle_trans. apply Cmod_triangle.
   eapply Rle_trans; [eapply Rplus_le_compat_r|].
   + apply best_3pack; auto.
     generalize (cut_fst 9 l). now rewrite E.
   + assert (A : forall n, List.In n l2 -> (9 <= n)%nat).
     { intros n Hn. apply (@cut_snd' 3 9 l); auto. now rewrite E. }
     rewrite (Clistsum_factor_above 9 l2) by trivial.
     set (l2' := List.map (decr 9) l2).
     rewrite Cmod_mult.
     replace (max3pack / _)
       with (max3pack + Cmod (alpha^9) * (max3pack / (1 - Cmod alpha ^9))).
     * apply Rplus_le_compat_l.
       apply Rmult_le_compat_l; try apply Cmod_ge_0.
       apply (IH (N-9)%nat); try lia.
       { apply Delta_map_decr; auto. }
       { unfold l2'. intros x Hx. rewrite List.in_map_iff in Hx.
         destruct Hx as (y & <- & Hy).
         specialize (A y Hy).
         assert (y < N)%nat by (apply B; rewrite List.in_app_iff; now right).
         unfold decr. lia. }
     * rewrite Cmod_pow. field. generalize alphamod9_lt; lra.
Qed.

(** We need below to have an upper bound of the elements of a list *)

Fixpoint listmax l :=
 match l with
 | nil => O
 | n::l' => Nat.max n (listmax l')
 end%list.

Lemma listmax_above l :
 forall n, List.In n l -> (n <= listmax l)%nat.
Proof.
 induction l; inversion 1; simpl; subst. apply Nat.le_max_l.
 transitivity (listmax l); auto. apply Nat.le_max_r.
Qed.

Lemma Clistsum_delta l :
  Delta 3 l ->
  Cmod (Clistsum (List.map (Cpow alpha) l)) <=
   max3pack / (1 - Cmod alpha ^9).
Proof.
 intros D.
 apply (Clistsum_delta_below (S (listmax l))); auto.
 intros x Hx. apply listmax_above in Hx. lia.
Qed.

Lemma diff0_better_bound n :
 Rabs (diff0 n) <= 2 * Cmod coefa0 * max3pack / (1 - Cmod alpha ^9).
Proof.
 rewrite diff0_decomp_eqn'.
 rewrite Rabs_mult. rewrite Rabs_right by lra.
 unfold Rdiv. rewrite !Rmult_assoc. apply Rmult_le_compat_l; try lra.
 eapply Rle_trans; [apply re_le_Cmod|].
 rewrite Cmod_mult. apply Rmult_le_compat_l; try apply Cmod_ge_0.
 apply Clistsum_delta, decomp_delta.
Qed.

(* TODO : toujours quelques %C parasites *)

Lemma coefa2_inner_mod :
  Cmod (alpha * (tau ^ 2 - 1) - tau ^ 3)%C ^ 2 = tau*(1-tau).
Proof.
 rewrite !RtoC_pow, <- RtoC_minus.
 rewrite Cmod2_alt. unfold Cminus.
 rewrite re_plus, im_plus, re_scal_r, im_scal_r.
 rewrite <- !RtoC_opp, re_RtoC, im_RtoC, Rplus_0_r. simpl Re; simpl Im.
 rewrite re_alpha_alt.
 rewrite Rpow_mult_distr. rewrite im_alpha_2.
 rewrite tau3. field_simplify.
 replace (tau^8) with ((tau^4)^2) by ring.
 rewrite tau6, tau5, tau4, tau3. field_simplify.
 rewrite tau4, tau3. field.
Qed.

Lemma Cmod2_coefa2 :
  Cmod coefa2 ^2 = (1-tau)/(3+tau).
Proof.
 unfold coefa2, Cdiv.
 rewrite !Cmod_mult, !Rpow_mult_distr, Cmod_inv.
 2:{ apply Cminus_eq_contra. apply distinct_roots. }
 rewrite coefa2_inner_mod.
 rewrite im_alt', !Cmod_mult.
 rewrite !Cmod_R, Rabs_right by lra.
 rewrite Cmod_Ci, Rmult_1_r.
 simpl Im.
 rewrite pow_inv, Rpow_mult_distr.
 rewrite pow2_abs. rewrite im_alpha_2. field. generalize tau_approx; lra.
Qed.

(** And finally, we obtain that diff0 is always strictly less than 1.
    (experimentally the new bound is around 0.996) *)

Lemma diff0_lt_1 n : Rabs (diff0 n) < 1.
Proof.
 eapply Rle_lt_trans. apply diff0_better_bound.
 assert (A9 := alphamod9_lt).
 apply -> Rcomplements.Rdiv_lt_1; try lra.
 apply Rlt_pow2_inv; try lra.
 clear A9.
 rewrite !Rpow_mult_distr.
 rewrite max3pack_eqn.
 replace (Cmod alpha^9) with (((Cmod alpha)^2)^4*Cmod alpha) by ring.
 rewrite alphamod2, tau4.
 unfold coefa0. rewrite Cmod_mult, Rpow_mult_distr, Cmod2_coefa2.
 change alphabar with (Cconj alpha). rewrite Cmod_Cconj, alphamod2.
 assert (H := tau_approx).
 assert (H2 := tau2_approx).
 field_simplify; try lra. rewrite alphamod2, tau4, tau3.
 field_simplify; try lra. apply Rcomplements.Rlt_div_l; try lra.
 field_simplify; try lra. rewrite tau3. field_simplify; try lra.
 assert (LT : Cmod alpha * (-4*tau^2 + 8*tau -2) < 151 * tau^2 - 104*tau + 2).
 { apply Rlt_pow2_inv; try lra.
   rewrite Rpow_mult_distr. rewrite alphamod2. ring_simplify.
   rewrite tau5, tau4, tau3. ring_simplify; lra. }
 ring_simplify in LT. lra.
Qed.

(* Print Assumptions diff0_lt_1. *)

(* Consequences for h : *)

Lemma h_alt n : INR (h n) = tau*n + diff0 n.
Proof.
 rewrite diff0_alt; lra.
Qed.

Lemma h_natpart_or (n:nat) :
 h n = nat_part (tau*n) \/ h n = S (nat_part (tau*n)).
Proof.
assert (-1 < tau*n - h n < 1).
{ rewrite h_alt.
  assert (H := diff0_lt_1 n).
  rewrite Rcomplements.Rabs_lt_between in H. lra. }
destruct (Rle_or_lt 0 (tau*n-h n)).
- left. symmetry. apply nat_part_carac; lra.
- right.
  case (Nat.eq_dec n 0); intros Hn.
  + subst n. change (h 0) with O in *. simpl in *. lra.
  + assert (h n <> O). { contradict Hn. eapply f_0_inv; eauto. }
    assert (nat_part (tau*n) = h n -1)%nat; try lia.
    apply nat_part_carac. rewrite minus_INR by lia. simpl. lra.
Qed.

(* NB: both sides are reached, e.g. left for n=0 and right for n=1.
   I've found no easy way to predict on which side will be some (h n). *)

Lemma h_natpart_bound (n:nat) :
 (nat_part (tau*n) <= h n <= 1 + nat_part (tau*n))%nat.
Proof.
 destruct (h_natpart_or n) as [-> | ->]; lia.
Qed.

(* A quasi-additivity result for h = f 2 that I was unable to obtain
   directly on h. *)

Lemma h_quasiadd p n :
 (h p + h n -2 <= h (p+n) <= h p + h n + 2)%nat.
Proof.
  case (Nat.eq_dec p 0); intros Hp.
  - subst p. simpl. lia.
  - case (Nat.eq_dec n 0); intros Hn.
    + subst n. change (h 0) with 0%nat. rewrite !Nat.add_0_r. lia.
    + split; apply Nat.lt_succ_r; apply INR_lt.
      * rewrite minus_INR, plus_INR. rewrite !S_INR, !h_alt.
        2:{ generalize (@f_nonzero 2 p) (@f_nonzero 2 n). fold h. lia. }
        rewrite plus_INR.
        assert (Dp := diff0_lt_1 p).
        assert (Dn := diff0_lt_1 n).
        assert (Dpn := diff0_lt_1 (p+n)).
        rewrite Rcomplements.Rabs_lt_between in *.
        simpl. lra.
      * rewrite !S_INR, !plus_INR. rewrite !h_alt, plus_INR.
        assert (Dp := diff0_lt_1 p).
        assert (Dn := diff0_lt_1 n).
        assert (Dpn := diff0_lt_1 (p+n)).
        rewrite Rcomplements.Rabs_lt_between in *.
        simpl. lra.
Qed.

(* Print Assumptions h_quasiadd. *)

(** Now, same study for [diff2 n], giving the frequency of letter 2,
    and the limit of [h^^2]. Less interesting, the bound is in [1..2]. *)

Lemma Diff2_app u v : Diff2 (u++v) = Diff2 u + Diff2 v.
Proof.
 unfold Diff2.
 rewrite List.app_length, nbocc_app, !plus_INR. lra.
Qed.

Lemma Diff2_concat l : Diff2 (List.concat l) = Rlistsum (List.map Diff2 l).
Proof.
 induction l; simpl; auto.
 - unfold Diff2. simpl. lra.
 - rewrite Diff2_app. lra.
Qed.

Lemma diff2_decomp_eqn n :
  diff2 n =
   Rlistsum (List.map (fun n => 2*Re(coefa2 * alpha^n)%C) (decomp 2 n)).
Proof.
 unfold diff2.
 rewrite decomp_prefix_kseq.
 rewrite Diff2_concat, List.map_map, List.map_rev, Rlistsum_rev.
 f_equal.
 apply List.map_ext; intros.
 rewrite <- kseq_take_A. apply diff_A.
Qed.

Lemma diff2_decomp_eqn' n :
  diff2 n =
   2*Re (coefa2 * Clistsum (List.map (Cpow alpha) (decomp 2 n))).
Proof.
 rewrite diff2_decomp_eqn.
 induction decomp; cbn -[Re].
 - rewrite Cmult_0_r. cconst.
 - rewrite Cmult_plus_distr_l, re_plus, Rmult_plus_distr_l.
   f_equal. apply IHl.
Qed.

(** With the previous expression of [diff2 n], we will progressively bound it
    by some constant independent from [n]. *)

Lemma diff2_decomp_le n :
 Rabs (diff2 n) <=
  2 * Cmod coefa2 * Rlistsum (List.map (pow (Cmod alpha)) (decomp 2 n)).
Proof.
 rewrite diff2_decomp_eqn.
 induction decomp.
 - simpl. rewrite Rabs_R0. lra.
 - cbn -[Re].
   eapply Rle_trans. apply Rabs_triang.
   rewrite Rmult_plus_distr_l.
   apply Rplus_le_compat; [|apply IHl].
   rewrite Rabs_mult. rewrite Rabs_right by lra.
   rewrite Rmult_assoc.
   apply Rmult_le_compat_l; try lra.
   rewrite <- Cmod_pow, <-Cmod_mult.
   apply re_le_Cmod.
Qed.

Lemma diff2_indep_bound n :
 Rabs (diff2 n) <= 2 * Cmod coefa2 / (1 - Cmod alpha^3).
Proof.
 eapply Rle_trans. apply diff2_decomp_le.
 unfold Rdiv.
 apply Rmult_le_compat_l.
 - generalize (Cmod_ge_0 coefa2). lra.
 - apply sum_pow; try lia; try apply decomp_delta.
   split; try apply Cmod_ge_0.
   apply Rlt_pow2_inv; try lra.
   rewrite alphamod2. generalize tau_approx. lra.
Qed.

Lemma diff2_lt_2 n : Rabs (diff2 n) < 2.
Proof.
 eapply Rle_lt_trans. apply diff2_indep_bound.
 replace 2 with (2*1) at 2 by lra.
 unfold Rdiv. rewrite Rmult_assoc. apply Rmult_lt_compat_l; try lra.
 assert (H := tau_approx).
 assert (H2 := tau2_approx).
 assert (Cmod alpha^3 < 1).
 { apply Rlt_pow2_inv; try lra. ring_simplify.
   change 6%nat with (2*3)%nat. rewrite pow_mult, alphamod2, tau3. lra. }
 apply Rcomplements.Rlt_div_l; try lra.
 rewrite Rmult_1_l.
 apply Rlt_pow2_inv; try lra. rewrite Cmod2_coefa2.
 apply Rcomplements.Rlt_div_l; try lra.
 ring_simplify.
 change 6%nat with (2*3)%nat. rewrite pow_mult, alphamod2, tau3.
 ring_simplify.
 assert (LT : Cmod alpha^3 * (2*tau + 6) < 5 - tau^2).
 { apply Rlt_pow2_inv; try lra.
   rewrite Rpow_mult_distr. ring_simplify.
   change 6%nat with (2*3)%nat. rewrite pow_mult, alphamod2, tau3.
   ring_simplify. rewrite tau3, tau4. ring_simplify. lra. }
 ring_simplify in LT. lra.
Qed.


(** Experimentally, this bound for diff2 is around 1.3462 and cannot be
    improved significantly (unlike the first bound 1.112 for diff0 improved
    to 0.996 later).
    Anyway, having this finite bound is enough to prove that the frequency
    of letter 2 is [tau^2] and that [(h^^2)(n) / n] converges towards [tau^2].
*)

Lemma lim_diff2_div_n : is_lim_seq (fun n => diff2 n / n) 0.
Proof.
 eapply is_lim_seq_bound. apply diff2_indep_bound.
Qed.

Lemma frequency_2 :
 is_lim_seq (fun n => count (kseq 2) 2 n / n) (tau^2).
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with
  (u := fun n => tau^2 - diff2 (S n) / INR (S n)).
 - intros n.
   unfold diff2, Diff2. rewrite take_length.
   rewrite <- count_nbocc. field. apply RSnz.
 - replace (Rbar.Finite (tau^2)) with (Rbar.Finite (tau^2 + -0))
    by (f_equal; lra).
   eapply is_lim_seq_plus'. apply is_lim_seq_const.
   change (Rbar.Finite (-0)) with (Rbar.Rbar_opp 0).
   apply -> is_lim_seq_opp.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff2 n / n)).
   apply lim_diff2_div_n.
Qed.

Lemma frequency_1 :
 is_lim_seq (fun n => count (kseq 2) 1 n / n) (tau^4).
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with
  (u := fun n => tau^4 + diff0 (S n) / INR (S n) + diff2 (S n) / INR (S n)).
 - intros n.
   field_simplify; try apply RSnz. f_equal.
   rewrite Rplus_assoc.
   replace (diff0 (S n) + diff2 (S n)) with (-diff1 (S n))
     by (generalize (diff012 (S n)); lra).
   unfold diff1, Diff1. rewrite take_length.
   rewrite <- count_nbocc. field.
 - replace (Rbar.Finite (tau^4)) with (Rbar.Finite (tau^4 + 0 + 0))
    by (f_equal; lra).
   apply is_lim_seq_plus'. apply is_lim_seq_plus'. apply is_lim_seq_const.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff0 n / n)).
   apply lim_diff0_div_n.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff2 n / n)).
   apply lim_diff2_div_n.
Qed.

Lemma Lim_h2_div_n :
 is_lim_seq (fun n => (h^^2) n / n) (tau^2).
Proof.
 apply is_lim_seq_incr_1.
 apply is_lim_seq_ext with
  (u := fun n => tau^2 - diff2 (S n) / INR (S n)).
 - intros n. rewrite diff2_alt. field. rewrite S_INR.
   generalize (pos_INR n). lra.
 - replace (Rbar.Finite (tau^2)) with (Rbar.Finite (tau^2 - 0))
    by (f_equal; lra).
   eapply is_lim_seq_plus'. apply is_lim_seq_const.
   change (Rbar.Finite (-0)) with (Rbar.Rbar_opp 0).
   apply -> is_lim_seq_opp.
   rewrite <- (is_lim_seq_incr_1 (fun n => diff2 n / n)).
   apply lim_diff2_div_n.
Qed.

Lemma h2_alt n : INR ((h^^2) n) = tau^2 * n - diff2 n.
Proof.
 rewrite diff2_alt; lra.
Qed.


(** Distance between [h^^2] and [nat_part (tau^2 * n)].
    This distance may be "+2", for instance for n=1235.
    But the theoretical "-1" does not seem to happen
    (TODO: how to prove it ?) *)

Lemma h2_natpart_bound (n:nat) :
 (nat_part (tau^2 * n) -1 <= (h^^2) n <= 2 + nat_part (tau^2 * n))%nat.
Proof.
 split.
 - assert (nat_part (tau^2 * n) < 2 + (h^^2) n)%nat; try lia.
   { apply nat_part_lt. split.
     - apply Rmult_le_pos. generalize tau2_approx; lra. apply pos_INR.
     - rewrite plus_INR. replace (INR 2) with 2 by auto.
       assert (LT := diff2_lt_2 n). apply Rcomplements.Rabs_lt_between in LT.
       generalize (diff2_alt n). lra. }
 - assert ((h^^2) n - 2 <= nat_part (tau^2 * n))%nat; try lia.
   { apply nat_part_le.
     - apply Rmult_le_pos. generalize tau2_approx; lra. apply pos_INR.
     - destruct (Nat.le_gt_cases 4 n) as [LE|LT].
       + assert (LE' := fs_mono 2 2 LE).
         rewrite minus_INR by trivial.
         replace (INR 2) with 2 by auto.
         assert (LT := diff2_lt_2 n). apply Rcomplements.Rabs_lt_between in LT.
         generalize (diff2_alt n). lra.
       + destruct n. simpl; lra.
         destruct n. simpl. rewrite !Rmult_1_r. generalize tau2_approx. lra.
         destruct n. simpl. rewrite !Rmult_1_r. generalize tau2_approx. lra.
         destruct n. simpl. rewrite !Rmult_1_r. generalize tau2_approx. lra.
         lia. }
Qed.
*)
