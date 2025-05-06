From Coq Require Import Arith Lia NArith Reals Lra.
From Hofstadter.HalfQuantum Require Import Complex.
Require Import MoreTac MoreFun MoreList MoreReals MoreLim MoreComplex MoreSum.
Require Import DeltaList Approx.
Require Import GenFib GenG GenAdd Words Mu ThePoly Freq Discrepancy F3.
Require Equidistrib.
Local Open Scope C.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

#[local] Hint Resolve μ_approx τ_approx αmod_approx : typeclass_instances.

(** * Mean discrepancy in the case k=3

    We consider simultaneously (diff 3 n = h n - τ * n) and
    (diffh2 n = h (h n) - τ^2 * n). For that, we reuse
    complex C = R*R for 2D vectors *)

Definition sumdiff n := big_sum (diff 3) n.
Definition meandiff n := sumdiff n / n.

Definition sumdiffh2 n := big_sum diffh2 n.
Definition meandiffh2 n := sumdiffh2 n / n.

Local Open Scope C.

Definition vdiff n : C := (diff 3 n, diffh2 n).
Definition vsumdiff n : C := (sumdiff n, sumdiffh2 n).
Definition vmeandiff n : C := (meandiff n, meandiffh2 n).

Lemma vdiff_0 : vdiff 0 = 0.
Proof.
 unfold vdiff, diff, diffh2. simpl. lca.
Qed.

Lemma vsumdiff_0 : vsumdiff 0 = 0.
Proof.
 easy.
Qed.

Lemma vsumdiff_S n : vsumdiff (S n) = vsumdiff n + vdiff n.
Proof.
 easy.
Qed.

Lemma diffh2_app l l' : Delta 3 (l++l') ->
 (diffh2 (sumA 3 (l++l')) = diffh2 (sumA 3 l) + diffh2 (sumA 3 l'))%R.
Proof.
 intros D. destruct (Delta_app_inv l l' D) as (D1 & D2 & D3).
 rewrite !diffh2_eqn.
 rewrite !rchild_decomp, !decomp_sum' by easy.
 rewrite map_app, diff_app; try easy. ring.
 rewrite <- map_app. eapply Delta_map; eauto. lia.
Qed.

Lemma vdiff_app l l' : Delta 3 (l++l') ->
 vdiff (sumA 3 (l++l')) = vdiff (sumA 3 l) + vdiff (sumA 3 l').
Proof.
 intros D. unfold vdiff, Cplus. f_equal.
 now apply diff_app. now apply diffh2_app.
Qed.

Lemma vdiff_cons p l : Delta 3 (p::l) ->
 vdiff (sumA 3 (p::l)) = vdiff (A 3 p) + vdiff (sumA 3 l).
Proof.
 intros D.
 replace (A 3 p) with (sumA 3 [p]) by (simpl; lia).
 now rewrite <- vdiff_app.
Qed.

Lemma vdiff_add p n : (n < A3 (p-2))%nat ->
 vdiff (n + A3 p) = vdiff n + vdiff (A3 p).
Proof.
 intros Hn.
 assert (E : decomp 3 (n+A3 p) = decomp 3 n++[p]).
 { now apply decomp_plus_A. }
 rewrite <- (decomp_sum 3 (n+A3 p)), E.
 rewrite vdiff_app. 2:{ rewrite <- E. apply decomp_delta. }
 rewrite decomp_sum. simpl. now rewrite Nat.add_0_r.
Qed.

(** Minimalistic theory of 2x2 matrices: vectors as R*R i.e. C
    and matrix as (R*R)*(R*R). *)

Definition Mapply '((a,b),(c,d)) '(x,y) := (a*x+b*y, c*x+d*y)%R.
Definition Mcube M V := Mapply M (Mapply M (Mapply M V)).

Lemma Mapply_Cplus M V V' : Mapply M (V+V') = Mapply M V + Mapply M V'.
Proof.
 unfold Cplus.
 destruct M as ((a,b),(c,d)), V as (x,y), V' as (x',y').
 simpl. f_equal; ring.
Qed.

Lemma Mcube_Cplus M V V' : Mcube M (V+V') = Mcube M V + Mcube M V'.
Proof.
 unfold Mcube. now rewrite !Mapply_Cplus.
Qed.

Lemma Mapply_scal M (r:R) V : Mapply M (r * V) = r * (Mapply M V).
Proof.
 unfold Mapply, Cmult. destruct M as ((a,b),(c,d)), V as (x,y).
 simpl. f_equal; ring.
Qed.

Lemma Mcube_scal M (r:R) V : Mcube M (r * V) = r * (Mcube M V).
Proof.
 unfold Mcube. now rewrite !Mapply_scal.
Qed.

Lemma Mapply_lim M u l :
 is_lim_Cseq u l -> is_lim_Cseq (fun n => Mapply M (u n)) (Mapply M l).
Proof.
 intros Hl. destruct M as ((a,b),(c,d)), l as (lx,ly).
 rewrite is_lim_Cseq_proj in Hl. simpl in Hl.
 rewrite is_lim_Cseq_proj. simpl. split.
 - eapply is_lim_seq_ext.
   + intros n. unfold compose. rewrite (surjective_pairing (u n)).
     simpl. reflexivity.
   + apply is_lim_seq_plus';
      apply is_lim_seq_mult'; apply Hl || apply is_lim_seq_const.
 - eapply is_lim_seq_ext.
   + intros n. unfold compose. rewrite (surjective_pairing (u n)).
     simpl. reflexivity.
   + apply is_lim_seq_plus';
      apply is_lim_seq_mult'; apply Hl || apply is_lim_seq_const.
Qed.

(** The matrix and initial vector corresponding to vdiff *)

Definition Mat := ((0,-τ),(1,-τ^2))%R.
Definition Vinit : C := (1-τ,1-τ^2)%R.

Lemma Vinit_ok : Vinit = vdiff 1.
Proof.
 unfold Vinit, vdiff, diff, diffh2. simpl. change (tau 3) with τ.
 f_equal; ring.
Qed.

Lemma vdiff_A_S p : vdiff (A 3 (S p)) = Mapply Mat (vdiff (A 3 p)).
Proof.
 unfold vdiff, Mat, Mapply.
 rewrite <- !diff0_alt'.
 do 2 rewrite <- (Ropp_involutive (diffh2 _)), <- diff2_alt'.
 rewrite diff0_diff2_A, diff2_diff0_A. f_equal; ring.
Qed.

Lemma vdiff_sumA l : Delta 3 l ->
 vdiff (sumA 3 (map S l)) = Mapply Mat (vdiff (sumA 3 l)).
Proof.
 induction l.
 - intros _. simpl. unfold vdiff, diff, diffh2. simpl. f_equal; ring.
 - intros D. simpl map. rewrite !vdiff_cons; trivial.
   2:{ change (Delta 3 (map S (a::l))). eapply Delta_map; eauto. lia. }
   rewrite vdiff_A_S, IHl, Mapply_Cplus. easy. eapply Delta_inv; eauto.
Qed.

Lemma vdiff_ranknz n :
 rank 3 n <> Some O ->
 vdiff n = Mapply Mat (vdiff (h n)).
Proof.
 intros Hn. unfold rank in Hn. unfold h. rewrite f_decomp by easy.
 rewrite <- (decomp_sum 3 n) at 1.
 assert (D := decomp_delta 3 n).
 set (l := decomp 3 n) in *. clearbody l. clear n.
 assert (Hl : ~In O l).
 { destruct l. easy. eapply Delta_nz; eauto.
   assert (n<>O) by (contradict Hn; now subst). lia. }
 rewrite <- vdiff_sumA, map_S_pred; try easy. now apply Delta_pred.
Qed.

Lemma vdiff_rank0 n :
 rank 3 n = Some O ->
 vdiff n = Vinit + Mcube Mat (vdiff (n - h n)).
Proof.
 intros Hn.
 replace (n - h n)%nat with (fs 3 3 (n-1)%nat).
 2:{ destruct n. easy. unfold h. rewrite f_S.
     replace (S n -1)%nat with n by lia. generalize (fs_le 3 3 n). lia. }
 unfold rank in Hn. rewrite fs_decomp by easy.
 rewrite <- (decomp_sum 3 n) at 1.
 assert (D := decomp_delta 3 n).
 rewrite decomp_pred by easy.
 set (l := decomp 3 n) in *. clearbody l. clear n.
 destruct l as [|r l]; try easy. inversion Hn; subst. clear Hn.
 rewrite vdiff_cons, Vinit_ok by easy. f_equal.
 simpl prev_decomp. unfold Mcube.
 assert (Hl : forall x, In x l -> (3 <= x)%nat).
 { intros. eapply Delta_le in D; eauto. }
 assert (D3 : Delta 3 (map (decr 3) l)).
 { apply Delta_map_decr; eauto using Delta_inv. }
 rewrite <- !vdiff_sumA; trivial.
 - f_equal. f_equal. rewrite !map_map.
   rewrite map_ext_in with (g:=fun n => n). symmetry; apply map_id.
   { intros x Hx. unfold decr. specialize (Hl x Hx). lia. }
 - rewrite map_map. eapply Delta_map; eauto. lia.
 - eapply Delta_map; eauto. lia.
Qed.

Lemma vsumdiff_eqn n :
  vsumdiff n =
  Mapply Mat (vsumdiff (h n)) +
  ((n - h n)%nat * Vinit + Mcube Mat (vsumdiff (n - h n))).
Proof.
 induction n.
 - unfold vsumdiff, sumdiff, sumdiffh2, Cplus. simpl. f_equal; ring.
 - rewrite vsumdiff_S, IHn.
   assert (H := @flat_rank_0 3%nat lia n).
   destruct (f_step 3 n) as [E|E]; fold h in *.
   + rewrite E in *.
     rewrite vdiff_rank0 by now rewrite <- H.
     replace (S n - h n)%nat with (S (n - h n)).
     2:{ unfold h. generalize (f_le 3 n); lia. }
     rewrite vsumdiff_S.
     rewrite <- !Cplus_assoc. f_equal.
     replace ((S _) * _) with ((n-h n)%nat * Vinit + Vinit).
     2:{ unfold Cplus, Cmult. rewrite S_INR.
         destruct Vinit; simpl; f_equal; ring. }
     rewrite Mcube_Cplus. ring.
   + rewrite E in *. replace (S n - S _)%nat with (n - h n)%nat by lia.
     rewrite vsumdiff_S, Mapply_Cplus.
     rewrite <- vdiff_ranknz. fixeq C. ring.
     rewrite <- H. lia.
Qed.

Lemma vmeandiff_alt n : vmeandiff n = (/n)%R * vsumdiff n.
Proof.
 unfold vmeandiff, meandiff, meandiffh2, Cmult. simpl.
 unfold Rdiv. f_equal; ring.
Qed.

Lemma vmeandiff_eqn n : n<>O ->
  vmeandiff n =
  (h n / n)%R * Mapply Mat (vmeandiff (h n)) +
  (1 - h n / n)%R * (Vinit + Mcube Mat (vmeandiff (n - h n))).
Proof.
 intros Hn.
 destruct (Nat.eq_dec n 1) as [->|Hn'].
 { change (h 1) with 1%nat.
   simpl Rdiv. replace (1/1)%R with 1%R by lra.
   replace (1-1)%R with 0%R by lra. rewrite Cmult_0_l.
   replace (vmeandiff 1) with 0; try lca.
   rewrite vmeandiff_alt, vsumdiff_S, vsumdiff_0, vdiff_0. lca. }
 rewrite !vmeandiff_alt, vsumdiff_eqn.
 rewrite Mcube_scal, Mapply_scal.
 rewrite !Cmult_plus_distr_l. f_equal; [|f_equal].
 - rewrite Cmult_assoc. f_equal. ctor. f_equal.
   unfold Rdiv. rewrite (Rmult_comm (h n)), Rmult_assoc, Rinv_r. ring.
   contradict Hn. apply (INR_eq _ 0) in Hn.
   generalize (@f_nonzero 3%nat n). unfold h in *; lia.
 - rewrite Cmult_assoc. f_equal. ctor. f_equal.
   rewrite minus_INR by apply f_le. field.
   now apply (not_INR n 0).
 - rewrite Cmult_assoc. f_equal. ctor. f_equal.
   rewrite minus_INR by apply f_le. field.
   split.
   + assert (LT := @f_lt 3 n lia). apply lt_INR in LT. unfold h. lra.
   + now apply (not_INR n 0).
Qed.

Lemma vmeandiff_A_eqn p :
  let r := (A3 (p-1) / A3 p)%R in
  vmeandiff (A3 p) =
  r * Mapply Mat (vmeandiff (A3 (p-1))) +
  (1-r) * (Vinit + Mcube Mat (vmeandiff (A3 (p-3)))).
Proof.
 intros r. rewrite vmeandiff_eqn.
 2:{ generalize (A_nz 3 p). lia. }
 unfold h. rewrite f_A by easy.
 f_equal. fold r. rtoc.
 destruct p.
 - simpl A3 in *. replace (1-r) with 0. now rewrite !Cmult_0_l.
   unfold r. simpl. lca.
 - do 4 f_equal. simpl. rewrite Nat.sub_0_r. lia.
Qed.

Definition limit : C := ((-τ^2+4*τ-2)/6,(5*τ^2+τ-2)/6)%R.

#[local] Instance : Approx 0.043956663905 (Re limit) 0.043956663906.
Proof.
 unfold limit. simpl. approx.
Qed.

#[local] Instance : Approx 0.168363993868 (Im limit) 0.168363993869.
Proof.
 unfold limit. simpl. approx.
Qed.

Lemma limit_ok :
 limit = τ * Mapply Mat limit + (1-τ)*(Vinit + Mcube Mat limit).
Proof.
 unfold Vinit, Mcube, Mapply, Mat, limit.
 rewrite !Rmult_0_l.
 unfold Cmult, Cplus. simpl. f_equal; field [τ3].
Qed.

Lemma limit_unique l :
 l = τ * Mapply Mat l + (1-τ)*(Vinit + Mcube Mat l) -> l = limit.
Proof.
 destruct l as (x,y).
 unfold Mcube, Mapply, Mat, Vinit, limit, Cplus.
 intros [= E1 E2]. simpl in E1,E2. apply Rminus_diag_eq in E1, E2.
 ring_simplify [τ3] in E1. ring_simplify [τ3] in E2.
 assert (Hx : (x = (-τ^2 + 4*τ - 2)/ 6)%R).
 { apply Rmult_eq_compat_l with (r:=(τ^2+τ)%R) in E1. ring_simplify [τ3] in E1.
   apply Rmult_eq_compat_l with (r:=(2*τ-1)%R) in E2. ring_simplify [τ3] in E2.
   rewrite <- E2 in E1. clear E2.
   apply Rminus_diag_eq in E1. ring_simplify [τ3] in E1.
   apply Rmult_eq_reg_r with (r := (4*τ^2 + 2*τ - 2)%R). 2:approx.
   field_simplify [τ3]. rewrite <- (Rplus_0_l (_/6)). rewrite <- E1. field. }
 f_equal; trivial.
 rewrite Hx in E1. field_simplify [τ3] in E1.
 apply Rmult_integral in E1. destruct E1 as [E1|E1]; [|lra].
 apply Rmult_eq_reg_l with (r:=(12*τ-6)%R). 2:approx.
 rewrite <- (Rplus_0_l (_*(_/_))). rewrite <- E1. field [τ3].
Qed.

(** NB: [Re limit] and [Im limit] are also the respective real roots of
    two polynomials of degree 3. *)

Lemma re_limit_poly : let x := Re limit in (24*x^3+16*x^2+22*x-1 = 0)%R.
Proof.
 unfold limit. simpl. field [τ3].
Qed.

Lemma im_limit_poly : let x := Im limit in (24*x^3+64*x^2+42*x-9 = 0)%R.
Proof.
 unfold limit. simpl. field [τ3].
Qed.

Definition vsumdiff' n := vsumdiff n - n * limit.
Definition vmeandiff' n := vmeandiff n - limit.
Definition rest n :=
  Mapply Mat (vmeandiff (h n)) - Vinit - Mcube Mat (vmeandiff (n - h n)).

Lemma vmeandiff'_eqn n : n<>O ->
  vmeandiff' n =
  τ * Mapply Mat (vmeandiff' (h n))
  + (1 - τ) * Mcube Mat (vmeandiff' (n-h n))
  + (h n / n - τ) * rest n.
Proof.
 intros Hn.
 unfold vmeandiff', rest. rewrite Ceq_minus.
 rewrite vmeandiff_eqn by easy.
 rewrite limit_ok at 1. rtoc.
 unfold Cminus. rewrite Mcube_Cplus, !Mapply_Cplus.
 replace (-limit) with ((-1)%R * limit) by lca.
 rewrite Mcube_scal, Mapply_scal. ring.
Qed.

Lemma vmeandiff'_A_eqn p : (p<>0)%nat ->
  vmeandiff' (A3 p) =
  τ * Mapply Mat (vmeandiff' (A3 (p-1)))
  + (1 - τ) * Mcube Mat (vmeandiff' (A3 (p-3)))
  + (A3 (p-1) / A3 p - τ) * rest (A3 p).
Proof.
 intros Hp.
 rewrite vmeandiff'_eqn.
 2:{ generalize (A_nz 3 p). lia. }
 unfold h. rewrite f_A by easy.
 replace (A3 p - _)%nat with (A3 (p-3)).
 2:{ destruct p; try easy. simpl. rewrite Nat.sub_0_r. lia. }
 lca.
Qed.

Local Close Scope C.

(** A norm inspired by Rauzy's norm for tribonacci *)

Definition Rnorm (c:C) := Cmod (fst c + α * snd c).

Lemma Rnorm_Mapply c :
  Rnorm (Mapply Mat c) = Cmod α * Rnorm c.
Proof.
 unfold Mat, Mapply, Rnorm. destruct c as (x,y).
 simpl. rewrite <- Cmod_mult. f_equal. rtoc.
 rewrite Ceq_minus. ring_simplify.
 replace (RtoC τ) with (α * αbar)%C at 2.
 2:{ now rewrite <- Cmod2_conj, αmod2. }
 replace (τ^2)%C with (-(α+αbar))%C.
 2:{ rewrite re_alt'. unfold Re, α. simpl.
     rewrite re_α_alt. rtoc. field. }
 ring.
Qed.

Lemma Rnorm_triangle c c' : Rnorm (c+c') <= Rnorm c + Rnorm c'.
Proof.
 unfold Rnorm. simpl. rtoc. rewrite <- Cmod_triangle.
 apply Req_le. f_equal. ring.
Qed.

Lemma Rnorm_scal (r:R) c : Rnorm (r*c) = Rabs r * Rnorm c.
Proof.
 destruct c as (x,y). unfold Rnorm.
 rewrite <- Cmod_R, <- Cmod_mult. f_equal. simpl. rtoc. ring.
Qed.

Lemma Rnorm_opp c : Rnorm (-c) = Rnorm c.
Proof.
 replace (-c)%C with ((-1)*c)%C by lca. rewrite Rnorm_scal.
 rewrite Rabs_left; lra.
Qed.

Lemma Rnorm_ge_scal_Im c : Rabs (Im c) <= /im_α * Rnorm c.
Proof.
 unfold Rnorm.
 apply Rmult_le_reg_l with (r:=im_α). approx.
 field_simplify; [|approx].
 rewrite <- im_le_Cmod. simpl. rewrite Rmult_0_r, !Rplus_0_l.
 now rewrite Rabs_mult, (Rabs_right' im_α) by approx.
Qed.

Lemma Rnorm_ge_scal_Re c : Rabs (Re c) <= (1 + Cmod α / im_α) * Rnorm c.
Proof.
 unfold Re.
 rewrite <- Cmod_R.
 replace (RtoC (fst c)) with ((fst c + α * snd c) + -α * snd c)%C by ring.
 rewrite Cmod_triangle.
 fold (Rnorm c). rewrite Cmod_mult, Cmod_opp, Cmod_R.
 rewrite Rmult_plus_distr_r, Rmult_1_l. apply Rplus_le_compat_l.
 unfold Rdiv. rewrite Rmult_assoc.
 apply Rmult_le_compat_l. apply Cmod_ge_0. apply Rnorm_ge_scal_Im.
Qed.

Lemma Re_le_3Rnorm c : Rabs (Re c) <= 3 * Rnorm c.
Proof.
 rewrite Rnorm_ge_scal_Re. apply Rmult_le_compat_r. apply Cmod_ge_0. approx.
Qed.

Lemma Im_le_2Rnorm c : Rabs (Im c) <= 2 * Rnorm c.
Proof.
 rewrite Rnorm_ge_scal_Im. apply Rmult_le_compat_r. apply Cmod_ge_0. approx.
Qed.

Lemma Rnorm_lim0 u : is_lim_seq (Rnorm ∘ u) 0 <-> is_lim_Cseq u 0.
Proof.
 split; intros H.
 - apply is_lim_Cseq_proj. simpl. split.
   + apply is_lim_seq_scal_l with (a:=3) in H.
     simpl in H. rewrite Rmult_0_r in H.
     eapply is_lim_seq_0_abs; eauto.
     exists O. intros n _. apply Re_le_3Rnorm.
   + apply is_lim_seq_scal_l with (a:=2) in H.
     simpl in H. rewrite Rmult_0_r in H.
     eapply is_lim_seq_0_abs; eauto.
     exists O. intros n _. apply Im_le_2Rnorm.
 - rewrite is_lim_Cseq_proj in H.
   rewrite <- Cmod_0.
   apply is_lim_Cseq_Cmod. replace 0%C with (0+α*0)%C by lca.
   apply is_lim_Cseq_plus.
   + rewrite is_lim_Cseq_proj. unfold compose. simpl.
     split. apply H. apply is_lim_seq_const.
   + apply is_lim_Cseq_mult. apply is_lim_Cseq_const.
     rewrite is_lim_Cseq_proj. unfold compose. simpl.
     split. apply H. apply is_lim_seq_const.
Qed.

(** rest is bounded *)

Lemma meandiff_bounded n : -0.709 <= meandiff n <= 0.855.
Proof.
 unfold meandiff. revert n.
 assert (forall n:nat, -0.709 * n <= sumdiff n <= 0.855 * n).
 { induction n.
   - simpl. unfold sumdiff. simpl. lra.
   - unfold sumdiff in *. rewrite S_INR. simpl.
     generalize (diff_bound n). lra. }
 intros n. destruct (Nat.eq_dec n 0) as [->|Hn].
 { simpl. unfold Rdiv. rewrite Rinv_0, Rmult_0_r. lra. }
 specialize (H n). split.
 - apply (Rmult_le_reg_r n). apply (lt_INR 0). lia.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_l. lra.
   contradict Hn. now apply INR_eq.
 - apply (Rmult_le_reg_r n). apply (lt_INR 0). lia.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_l. lra.
   contradict Hn. now apply INR_eq.
Qed.

Lemma meandiffh2_bounded n : -0.787 <= meandiffh2 n <= 1.039.
Proof.
 unfold meandiffh2. revert n.
 assert (forall n:nat, -0.787 * n <= sumdiffh2 n <= 1.039 * n).
 { induction n.
   - simpl. unfold sumdiffh2. simpl. lra.
   - unfold sumdiffh2 in *. rewrite S_INR. simpl.
     generalize (diffh2_bounds n). lra. }
 intros n. destruct (Nat.eq_dec n 0) as [->|Hn].
 { simpl. unfold Rdiv. rewrite Rinv_0, Rmult_0_r. lra. }
 specialize (H n). split.
 - apply (Rmult_le_reg_r n). apply (lt_INR 0). lia.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_l. lra.
   contradict Hn. now apply INR_eq.
 - apply (Rmult_le_reg_r n). apply (lt_INR 0). lia.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_l. lra.
   contradict Hn. now apply INR_eq.
Qed.

Lemma Rnorm_vmeandiff_bound n : Rnorm (vmeandiff n) < 2.
Proof.
 unfold Rnorm, vmeandiff. simpl.
 eapply Rle_lt_trans; [apply Cmod_triangle|].
 rewrite Cmod_mult, !Cmod_R.
 replace 2 with (1+1) by lra.
 apply Rplus_lt_compat.
 - apply Rcomplements.Rabs_lt_between. generalize (meandiff_bounded n); lra.
 - assert (0 <= Rabs (meandiffh2 n) < 1.04).
   { split. apply Rabs_pos.
     apply Rcomplements.Rabs_lt_between.
     generalize (meandiffh2_bounded n); lra. }
   generalize αmod_approx. unfold Approx. nra.
Qed.

Definition K0 := Cmod α * 2 + Rnorm Vinit + (Cmod α)^3 * 2.

Lemma K0_pos : 0 <= K0.
Proof.
 unfold K0.
 rewrite <- Cmod_pow.
 assert (0 <= Rnorm Vinit) by apply Cmod_ge_0.
 generalize (Cmod_ge_0 α), (Cmod_ge_0 (α^3)); lra.
Qed.

Lemma rest_bounded n : Rnorm (rest n) <= K0.
Proof.
 unfold rest, K0, Cminus.
 rewrite !Rnorm_triangle, !Rnorm_opp.
 repeat apply Rplus_le_compat; try lra.
 - rewrite Rnorm_Mapply.
   generalize (Rnorm_vmeandiff_bound (h n)), (Cmod_ge_0 α). nra.
 - unfold Mcube. rewrite !Rnorm_Mapply. simpl. rewrite !Rmult_assoc.
   assert (H := Cmod_ge_0 α).
   repeat (apply Rmult_le_compat_l; trivial).
   generalize (Rnorm_vmeandiff_bound (n - h n)); nra.
Qed.

(** We focus now on the subsequence n=A3 p *)

Lemma ratio_bound p :
  Rabs (A3 (p-1) / A3 p - τ) <= 2 * Cmod (coefdA 3 α) * (τ * Cmod α)^p.
Proof.
 apply Rmult_le_reg_r with (r:=A3 p).
 { apply lt_0_INR. generalize (A_nz 3 p); lia. }
 rewrite <- (Rabs_right' (A3 p)) at 2 by apply pos_INR.
 rewrite <- Rabs_mult.
 replace (_ * A3 p) with (A3 (p-1) - τ * A3 p).
 2:{ field. apply not_0_INR. generalize (A_nz 3 p); lia. }
 rewrite <- Cmod_R. change τ with (tau 3) at 1.
 rewrite (Equation_dA 3 _ roots_sorted p lia).
 unfold roots. simpl. rewrite Cplus_0_r.
 change αbar with (Cconj α). rewrite coefdA_conj. conj_out.
 rewrite re_alt'. rewrite Cmod_mult, !Cmod_R.
 rewrite Rabs_right' by lra.
 rewrite !Rmult_assoc.
 apply Rmult_le_compat_l; try lra.
 rewrite re_le_Cmod.
 rewrite Cmod_mult. apply Rmult_le_compat_l. apply Cmod_ge_0.
 rewrite Cmod_pow, (Rmult_comm τ), Rpow_mult_distr.
 rewrite <- (Rmult_1_r (Cmod α ^p)) at 1. rewrite Rmult_assoc.
 apply Rmult_le_compat_l. apply pow_le, Cmod_ge_0.
 rewrite τ_μ. rewrite pow_inv.
 apply Rmult_le_reg_l with (r:=μ^p).
 { apply pow_lt. approx. }
 field_simplify. 2:{ apply pow_nonzero. approx. }
 apply A_ge_mu_pow.
Qed.

(** Auxiliary sequence used for bounding (vmeandiff∘A) *)

Definition U p := Rnorm (vmeandiff' (A3 p)) / (τ*Cmod α)^p.

Definition K1 := 2 * Cmod (coefdA 3 α) * K0.

Lemma U_pos p : 0 <= U p.
Proof.
 unfold U. apply Rmult_le_pos. apply Cmod_ge_0.
 apply Rlt_le, Rinv_0_lt_compat. apply pow_lt. approx.
Qed.

Lemma K1_pos : 0 <= K1.
Proof.
 repeat apply Rmult_le_pos. lra. apply Cmod_ge_0. apply K0_pos.
Qed.

Lemma U_ineq p : (3<=p)%nat -> U p <= U (p-1) + U (p-3) + K1.
Proof.
 intros Hp.
 unfold U.
 apply Rmult_le_reg_r with (r:=(τ * Cmod α) ^ p).
 { apply pow_lt. approx. }
 rewrite !Rmult_plus_distr_r.
 replace p with (S (p-1)) at 6 by lia.
 rewrite <- tech_pow_Rmult.
 replace p with (3+(p-3))%nat at 9 by lia.
 rewrite pow_add.
 field_simplify; try (try split; apply pow_nonzero; approx).
 rewrite vmeandiff'_A_eqn by lia.
 rewrite !Rnorm_triangle.
 rewrite Rplus_comm, Rplus_assoc.
 repeat apply Rplus_le_compat.
 - ctor. rewrite Rnorm_scal. unfold K1.
   rewrite <- !Rmult_assoc. apply Rmult_le_compat.
   + apply Rabs_pos.
   + apply Cmod_ge_0.
   + rewrite Rmult_assoc, Rmult_comm. apply ratio_bound.
   + apply rest_bounded.
 - rewrite Rnorm_scal, Rnorm_Mapply. rewrite Rabs_right' by approx.
   apply Req_le; ring.
 - ctor. replace (1-τ) with (τ^3) by ring [τ3].
   unfold Mcube. rewrite Rnorm_scal, !Rnorm_Mapply.
   rewrite Rabs_right' by approx. apply Req_le; ring.
Qed.

Definition K2 := Rmax (U 0) (Rmax (U 1) (U 2)) + K1.

Lemma K2_pos : 0 <= K2.
Proof.
 apply Rplus_le_le_0_compat. 2:apply K1_pos.
 rewrite Rmax_Rle. left. apply U_pos.
Qed.

Lemma U_scal_A_minus_cst p : U p <= K2 * A3 p - K1.
Proof.
 induction p as [p IH] using lt_wf_ind.
 destruct (Nat.eq_dec p 0) as [->|P0].
 { simpl. unfold K2. ring_simplify. apply Rmax_l. }
 destruct (Nat.eq_dec p 1) as [->|P1].
 { transitivity (K2*1 - K1).
   - unfold K2. ring_simplify. rewrite <- Rmax_r. apply Rmax_l.
   - simpl. generalize K2_pos. lra. }
 destruct (Nat.eq_dec p 2) as [->|P2].
 { transitivity (K2*1 - K1).
   - unfold K2. ring_simplify. rewrite <- Rmax_r. apply Rmax_r.
   - simpl. generalize K2_pos. lra. }
 rewrite U_ineq by lia.
 rewrite !IH by lia.
 ring_simplify.
 destruct p; try easy.
 rewrite A_S. simpl. rewrite Nat.sub_0_r. rewrite plus_INR. lra.
Qed.

Lemma U_scal_A p : U p <= K2 * A3 p.
Proof.
 generalize (U_scal_A_minus_cst p) K1_pos; lra.
Qed.

Lemma Rnorm_vmeandiff'_A_bound p :
  Rnorm (vmeandiff' (A3 p)) <= K2 * (A3 p / μ^p) * (Cmod α)^p.
Proof.
 apply Rmult_le_reg_r with (r:=/(τ*Cmod α)^p).
 { apply Rinv_0_lt_compat, pow_lt. approx. }
 change (Rnorm _ */_) with (U p).
 rewrite U_scal_A. apply Req_le.
 rewrite τ_μ, Rpow_mult_distr, pow_inv. field.
 split; apply pow_nonzero; approx.
Qed.

Definition K3 := Rbar.real (Sup_seq (fun p => A3 p / μ^p)).

Lemma A3_le_pow_mu p : A3 p <= K3 * μ^p.
Proof.
 apply Rmult_le_reg_r with (r:=/μ^p).
 { apply Rinv_0_lt_compat. apply pow_lt. approx. }
 rewrite Rmult_assoc, Rinv_r, Rmult_1_r.
 2:{ apply pow_nonzero. approx. }
 apply (finite_lim_bounded (fun p => A3 p  / μ^p)).
 exists (coef_mu 3). apply ThePoly.A_div_pow_mu_limit.
Qed.

Lemma K3_pos : 0 <= K3.
Proof.
 generalize (A3_le_pow_mu 0). simpl. lra.
Qed.

Definition K4 := K2 * K3.

Lemma K4_pos : 0 <= K4.
Proof.
 apply Rmult_le_pos. apply K2_pos. apply K3_pos.
Qed.

Lemma Rnorm_vmeandiff'_A_bound' p :
  Rnorm (vmeandiff' (A3 p)) <= K4 * (Cmod α)^p.
Proof.
 rewrite Rnorm_vmeandiff'_A_bound. unfold K4.
 apply Rmult_le_compat_r. apply pow_le, Cmod_ge_0.
 apply Rmult_le_compat_l. apply K2_pos.
 rewrite (finite_lim_bounded (fun p => A3 p / μ^p)); try easy.
 exists (coef_mu 3). apply ThePoly.A_div_pow_mu_limit.
Qed.

Lemma αmod_μ : Cmod α * μ = sqrt μ.
Proof.
 symmetry. apply sqrt_lem_1. approx. approx.
 ring_simplify. rewrite αmod2, τ_μ. field. approx.
Qed.

Definition K5 := K4 * K3.

Lemma K5_pos : 0 <= K5.
Proof.
 apply Rmult_le_pos. apply K4_pos. apply K3_pos.
Qed.

Lemma Rnorm_vsumdiff'_A p : Rnorm (vsumdiff' (A3 p)) <= K5 * (sqrt μ)^p.
Proof.
  unfold vsumdiff'.
  assert (H := Rnorm_vmeandiff'_A_bound' p).
  unfold vmeandiff' in H. rewrite vmeandiff_alt in H.
  unfold Vscale in H. apply Rmult_le_compat_r with (r:=A3 p) in H.
  2:{ apply pos_INR. }
  etransitivity; [|etransitivity; [apply H|]].
  - rewrite Rmult_comm.
    rewrite <- (Rabs_right' (A3 p)) at 2 by apply pos_INR.
    rewrite <- Rnorm_scal.
    apply Req_le. f_equal. rtoc. field. intros [= E]. revert E.
    apply not_0_INR. generalize (A_nz 3 p). lia.
  - unfold K5. rewrite !Rmult_assoc.
    apply Rmult_le_compat_l. apply K4_pos.
    rewrite <- αmod_μ.
    rewrite Rpow_mult_distr, <- Rmult_assoc, (Rmult_comm K3), Rmult_assoc.
    apply Rmult_le_compat_l. { apply pow_le. approx. }
    apply A3_le_pow_mu.
Qed.

Lemma vsumdiff_split p n : (n < A3 (p-2))%nat ->
  vsumdiff (n + A3 p) = (vsumdiff n + vsumdiff (A3 p) + n * vdiff (A3 p))%C.
Proof.
 intros Hn.
 rewrite Nat.add_comm.
 assert (E := vdiff_add p).
 unfold vsumdiff, vdiff, sumdiff, sumdiffh2, Cmult, Cplus in *. simpl in *.
 rewrite !Rmult_0_l, Rplus_0_r, Rminus_0_r.
 rewrite !big_sum_sum. simpl.
 f_equal.
 - ring_simplify. rewrite Rplus_assoc. f_equal.
   erewrite big_sum_eq_bounded.
   2:{ intros x Hx. injection (E x lia) as E1 E2.
       now rewrite Nat.add_comm, E1. }
   rewrite big_sum_Rplus, big_sum_Rconst. ring.
 - ring_simplify. rewrite Rplus_assoc. f_equal.
   erewrite big_sum_eq_bounded.
   2:{ intros x Hx. injection (E x lia) as E1 E2.
       now rewrite Nat.add_comm, E2. }
   rewrite big_sum_Rplus, big_sum_Rconst. ring.
Qed.

Lemma vsumdiff'_split p n : (n < A3 (p-2))%nat ->
  vsumdiff' (n + A3 p) =
  (vsumdiff' n + vsumdiff' (A3 p) + n * vdiff (A3 p))%C.
Proof.
 intros. unfold vsumdiff'. rewrite vsumdiff_split by trivial.
 rewrite plus_INR, RtoC_plus; ring.
Qed.

Definition K6 := (K5 + K3 * Rnorm Vinit) / (sqrt μ - 1).

Lemma K6_pos : 0 <= K6.
Proof.
 apply Rcomplements.Rdiv_le_0_compat. 2:approx.
 apply Rplus_le_le_0_compat; apply Rmult_le_pos; trivial using K3_pos, K4_pos.
 apply Cmod_ge_0.
Qed.

Lemma Rnorm_vdiff_A p : Rnorm (vdiff (A3 p)) = (Cmod α)^p * Rnorm Vinit.
Proof.
 induction p.
 - simpl. rewrite Vinit_ok. lra.
 - rewrite vdiff_A_S, Rnorm_Mapply, IHp. simpl. ring.
Qed.

Lemma vsumdiff'_ineq p n : (n < A3 p)%nat ->
  Rnorm (vsumdiff' n) <= K6 * (sqrt μ)^p.
Proof.
 revert n.
 induction p as [[|p] IH] using lt_wf_ind.
 - simpl. intros n Hn. replace n with O by lia.
   unfold vsumdiff'. rewrite vsumdiff_0. simpl.
   replace (0 - 0*limit)%C with 0%C by lca.
   unfold Rnorm; simpl. replace (0+_)%C with 0%C by lca. rewrite Cmod_0.
   rewrite Rmult_1_r. apply K6_pos.
 - intros n Hn.
   destruct (Nat.lt_ge_cases n (A3 p)).
   + rewrite (IH p); try lia.
     apply Rmult_le_compat_l. apply K6_pos.
     simpl. rewrite <- (Rmult_1_l ((sqrt μ)^p)) at 1.
     apply Rmult_le_compat_r. apply pow_le. approx. approx.
   + replace n with ((n-A3 p) + A3 p)%nat by lia.
     rewrite vsumdiff'_split by (simpl in Hn; lia).
     rewrite 2 Rnorm_triangle, Rnorm_scal, Rnorm_vdiff_A.
     rewrite Rnorm_vsumdiff'_A.
     rewrite (IH (p-2)%nat) by (simpl in Hn; lia).
     rewrite Rabs_right' by apply pos_INR.
     assert (LT : (n-A3 p <= A3 p)%nat).
     { simpl in Hn. generalize (@A_mono 3 (p-2) p lia). lia. }
     apply le_INR in LT.
     rewrite A3_le_pow_mu in LT.
     apply Rmult_le_compat_r with (r:=(Cmod α^p * Rnorm Vinit)) in LT.
     2:{ apply Rmult_le_pos. apply pow_le. approx. apply Cmod_ge_0. }
     rewrite LT. clear LT.
     replace (K3 * _ * _) with ((K3 * Rnorm Vinit) * sqrt μ ^p).
     2:{ rewrite <- αmod_μ. rewrite Rpow_mult_distr. ring. }
     rewrite Rplus_assoc, <- Rmult_plus_distr_r.
     replace (K5+_) with (K6 * (sqrt μ -1)).
     2:{ unfold K6. field. approx. }
     rewrite Rmult_assoc, <- Rmult_plus_distr_l.
     apply Rmult_le_compat_l. apply K6_pos.
     rewrite (Rle_pow (sqrt μ) (p-2) p) by (lia||approx). simpl. lra.
Qed.

Definition K7 := K6 * sqrt μ.

Lemma K7_pos : 0 <= K7.
Proof.
 apply Rmult_le_pos. apply K6_pos. apply sqrt_pos.
Qed.

Lemma vsumdiff'_ineq' n : Rnorm (vsumdiff' n) <= K7 * sqrt n.
Proof.
 destruct (Nat.eq_dec n 0) as [->|Hn].
 - simpl. unfold vsumdiff'. rewrite vsumdiff_0, sqrt_0. simpl.
   replace (0-_)%C with 0%C by lca.
   unfold Rnorm; simpl. replace (0+_)%C with 0%C by lca. rewrite Cmod_0.
   lra.
 - assert (H := invA_spec 3 (n-1)).
   set (p := invA 3 (n-1)) in *.
   replace (S (n-1)) with n in  H by lia.
   rewrite (vsumdiff'_ineq (S p) n) by lia. simpl.
   rewrite <- !Rmult_assoc. apply Rmult_le_compat_l. apply K7_pos.
   rewrite <- sqrt_pow. 2:approx. apply sqrt_le_1.
   apply pow_le; approx. apply pos_INR. rewrite (A_ge_mu_pow 3).
   now apply le_INR.
Qed.

Lemma vmeandiff'_ineq n : n<>O ->
  Rnorm (vmeandiff' n) <= K7 / sqrt n.
Proof.
 intros Hn.
 assert (0 < n). { apply (lt_INR 0); lia. }
 unfold vmeandiff'. rewrite vmeandiff_alt. unfold Vscale.
 replace limit with ((/n)%R * (n*limit))%C.
 2:{ rtoc. field. intros [= E]. lra. }
 unfold Cminus. rewrite Copp_mult_distr_r, <- Cmult_plus_distr_l.
 rewrite Rnorm_scal.
 rewrite Rabs_right'.
 2:{ now apply Rlt_le, Rinv_0_lt_compat. }
 apply Rmult_le_reg_l with (r:=n); trivial.
 rewrite <- (sqrt_def n) at 4 by lra. field_simplify; try lra.
 2:{ generalize (sqrt_lt_R0 n); lra. }
 rewrite Rmult_comm. apply vsumdiff'_ineq'.
Qed.

Lemma vmeandiff'_CV : is_lim_Cseq vmeandiff' 0.
Proof.
 rewrite <- Rnorm_lim0.
 apply is_lim_seq_le_le_loc with (u:=fun _ => 0) (w:=fun n => K7 / sqrt n).
 - exists 1%nat. intros n Hn. split.
   apply Cmod_ge_0. apply vmeandiff'_ineq. lia.
 - apply is_lim_seq_const.
 - replace 0 with (K7 * 0) by lra.
   apply is_lim_seq_mult'. apply is_lim_seq_const. apply lim_inv_sqrt.
Qed.

Lemma vmeandiff_CV : is_lim_Cseq vmeandiff limit.
Proof.
 apply is_lim_Cseq_ext
   with (fun n => (vmeandiff n - limit) + limit)%C.
 { intros. unfold compose. ring. }
 replace limit with (0+limit)%C at 1 by lca.
 apply is_lim_Cseq_plus. apply vmeandiff'_CV. apply is_lim_Cseq_const.
Qed.

Lemma meandiff_CV : is_lim_seq meandiff (Re limit).
Proof.
 generalize vmeandiff_CV. rewrite is_lim_Cseq_proj. intros H. apply H.
Qed.

Lemma meandiffh2_CV : is_lim_seq meandiffh2 (Im limit).
Proof.
 generalize vmeandiff_CV. rewrite is_lim_Cseq_proj. intros H. apply H.
Qed.

Definition intdiff n := (h n - nat_part (τ*n))%nat.

Lemma intdiff_0_1 n : intdiff n = O \/ intdiff n = 1%nat.
Proof.
 unfold intdiff. generalize (@h_natpart_bound n); lia.
Qed.

Lemma diff_eqn n : diff 3 n = intdiff n - frac_part (τ*n).
Proof.
 unfold diff, intdiff. change (tau 3) with τ. change (f 3) with h.
 rewrite minus_INR by (generalize (@h_natpart_bound n); lia).
 rewrite (nat_frac (τ * n)) at 1. lra.
 apply Rmult_le_pos. approx. apply pos_INR.
Qed.

Lemma intdiff_eqn n : INR (intdiff n) = diff 3 n + frac_part (τ*n).
Proof.
 rewrite diff_eqn. lra.
Qed.

Lemma intdiff_carac_1 n : intdiff n = 1%nat <-> 0 < diff 3 n.
Proof.
 rewrite diff_eqn.
 split.
 - intros ->. simpl. generalize (base_fp (τ*n)). lra.
 - intros H.
   assert (H' : 0 < intdiff n). { generalize (base_fp (τ*n)); lra. }
   apply (INR_lt 0) in H'. generalize (intdiff_0_1 n); lia.
Qed.

Lemma intdiff_carac_0 n : intdiff n = O <-> diff 3 n <= 0.
Proof.
 split; intros H.
 - apply Rnot_lt_le.
   rewrite <- intdiff_carac_1. generalize (intdiff_0_1 n); lia.
 - apply Rle_not_lt in H.
   rewrite <- intdiff_carac_1 in H. generalize (intdiff_0_1 n); lia.
Qed.

Lemma sumintdiff_sumdiff n :
  INR (big_sum intdiff n) =
  sumdiff n + big_sum (fun m => frac_part (τ*m)) n.
Proof.
 rewrite big_sum_INR. unfold sumdiff.
 erewrite big_sum_eq_bounded. 2:{ intros x Hx. apply intdiff_eqn. }
 apply big_sum_Rplus.
Qed.

Lemma meanintdiff_meandiff n :
 big_sum intdiff n / n =
 meandiff n + big_sum (fun m => frac_part (τ*m)) n / n.
Proof.
 rewrite sumintdiff_sumdiff. unfold meandiff. apply Rmult_plus_distr_r.
Qed.

Definition lim_meanintdiff := Re limit + 0.5.

(** Cf conjecture in https://oeis.org/A082401 : *)

Lemma meanintdiff_CV :
 is_lim_seq (fun n => big_sum intdiff n / n) lim_meanintdiff.
Proof.
 eapply is_lim_seq_ext.
 { intros n. symmetry. apply meanintdiff_meandiff. }
 apply is_lim_seq_plus'. apply meandiff_CV.
 eapply is_lim_seq_ext.
 { intros n. symmetry. erewrite big_sum_eq_bounded.
   2:{ intros m Hm. now rewrite Rmult_comm. }
   reflexivity. }
 apply Equidistrib.MultIrrat_mean.
 intros q. apply tau_irrat; lia.
Qed.

#[local] Instance : Approx 0.543956663905 lim_meanintdiff 0.543956663906.
Proof.
 unfold lim_meanintdiff, limit. simpl. approx.
Qed.

Lemma lim_meanintdiff_poly :
  let x := lim_meanintdiff in 24*x^3-20*x^2+24*x-11 = 0.
Proof.
 unfold lim_meanintdiff, limit. simpl.
 replace 0.5 with (/2) by lra. field [τ3].
Qed.

(* TODO : median diff3 also CV to (Re limit) *)
