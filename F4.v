From Coq Require Import Arith Lia NArith Reals Lra.
From Hofstadter.HalfQuantum Require Import Complex.
Require Import MoreTac MoreFun MoreList MoreReals MoreLim MoreComplex MoreSum.
Require Import MorePoly DeltaList Approx.
Require Import GenFib GenG GenAdd Words Mu ThePoly Freq Discrepancy.
Local Open Scope Q.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * Studying case k=4

   We focus here on the case k=4, compute the complex roots of [X^4-X^3-1],
   and express (A 4 n) in term of combinations of powers of these roots.
   Then we study the frequencies in [Words.kseq 4] and the behaviour of
   function [f 4].
*)

Definition μ := mu 4.
Definition τ := tau 4.
Definition ν := nu 4.

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
 generalize (tau_carac 4 lia). fold τ. lra.
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
Proof. red. unfold τ. generalize tau_4. lra. Qed.

#[local] Instance : Approx 1.380277569097 μ 1.380277569098.
Proof. red. unfold μ. generalize mu_4. lra. Qed.

#[local] Instance : Approx (-0.819172513397) ν (-0.819172513396).
Proof. red. unfold ν. generalize nu_4. lra. Qed.

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

Lemma roots_sorted : SortedRoots 4 roots.
Proof.
 split.
 2:{ do 3 constructor.
     - repeat constructor.
     - constructor. left. unfold αbar. simpl. approx.
     - right. unfold α, αbar. simpl. split; trivial. approx.
     - unfold α. simpl. approx. }
 destruct (SortedRoots_exists 4 lia) as (l & Hl).
 case Hl. intros E _. rewrite E. apply linfactors_perm. clear E.
 assert (LN := SortedRoots_length 4 l Hl).
 assert (FS := SortedRoots_mu 4 l Hl).
 assert (K : Nat.Even 4) by now exists 2%nat.
 assert (LT := SortedRoots_nu 4 l K Hl).
 destruct (SortedRoots_im_pos 4 l Hl 0) as (LT',EQ); try lia.
 simpl in LT', EQ.
 destruct l as [|a [|b [|c [|d [|? l]]]]]; try (simpl; easy).
 unfold Cnth in *; cbn -[mu nu] in *. subst. clear LN K. unfold roots.
 assert (b = α); subst; try easy.
 destruct Hl as (E,CS).
 assert (E0 := coef_compat 0 _ _ E).
 assert (E3 := coef_compat 3 _ _ E).
 unfold ThePoly,coef in E0,E3. cbn -[Cpow mu nu] in E0,E3.
 fold μ in *. fold ν in *.
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
   (*compat*) try replace (-(1))%C with (RtoC (-1)) in E0 by lca.
   rewrite <- ?RtoC_opp in E0.
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
 exact (mu_carac 4 lia).
Qed.

Lemma μ_is_Croot : (μ^4 = μ^3 + 1)%C.
Proof.
 autorewrite with RtoC. f_equal. apply μ_is_Rroot.
Qed.

Lemma ν_is_Rroot : ν^4 = ν^3+1.
Proof.
 apply nu_carac. lia. now apply Nat.even_spec.
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
 apply (SortedRoots_nodup 4), roots_sorted.
Qed.

Lemma distinct_roots :
  α <> μ /\ αbar <> μ /\ αbar <> α /\
  RtoC ν <> α /\ RtoC ν <> αbar /\ ν <> μ.
Proof.
 assert (H := nodup_roots).
 inversion_clear H. inversion_clear H1. inversion_clear H2. simpl in *.
 intuition.
Qed.

Lemma A4_eqn :
 let a := coefA 4 μ in
 let b := coefA 4 α in
 let c := coefA 4 αbar in
 let d := coefA 4 ν in
 forall n, RtoC (A 4 n) = (a*μ^n + b*α^n + c*αbar^n + d*ν^n)%C.
Proof.
 intros a b c d n.
 rewrite (Equation_A 4 roots roots_sorted). unfold roots.
 simpl. fold a b c d. ring.
Qed.

(** Note about A4_eqn :
    coefficients a b c d used to be obtained by inversing the Vandermonde
    matrix of the roots. Fortunately, they also have simple expressions
    in terms of μ α αbar ν respectively.
    For showing that a is real and >=1, see Freq.A_gt_mu_pow.
    Interestingly, these coefficients are also roots
    of [X^4-X^3-(162/283)*X^2-(24/283)*X-1/283] (not proved here). *)

Lemma diff_A4_powers n :
  diff 4 (A 4 n) = 2 * Re (coefdA 4 α * α^n) + Re (coefdA 4 ν) * ν^n.
Proof.
  apply RtoC_inj.
  unfold diff. rewrite f_A, Equation_dA with (roots:=roots); try easy.
  2:apply roots_sorted.
  cbn -[Cmult Cpow pow ν]. rewrite Cplus_0_r, RtoC_plus, Cplus_assoc. f_equal.
  - change αbar with (Cconj α).
    rewrite coefdA_conj, <- Cpow_conj, <- Cconj_mult_distr, re_alt'.
    now rewrite RtoC_mult.
  - rewrite RtoC_mult, <- RtoC_pow. f_equal. apply coefdA_R.
Qed.


(** For the coming study of discrepancies, build and check an approx
    of τ up to 10^-100 *)

Definition tau100 :=
 (0.7244919590005156115883722821870365657864944813500110172703980284374529064751243679175832811454400193,
  0.7244919590005156115883722821870365657864944813500110172703980284374529064751243679175832811454400194)%Q.

Lemma tau100_approx : Approx (fst tau100) τ (snd tau100).
Proof.
 split.
 - apply Rlt_le. apply Mu.Ptau_lower; try easy; approx.
 - apply Rlt_le. apply Mu.Ptau_upper; try easy; approx.
Qed.

(** ** Discrepancies, i.e. differences [f 4 n - τ*n].

    We show that these differences are always in -1.5061 .. 1.5835 .
    Differences are all of the form [a-b*τ], let's encode them
    via pairs of N numbers. The key operation is then to compare
    to compare [a1-b1*τ] and [a2-b2*τ]. *)

Module NN.
Local Open Scope N.

Definition t : Type := N*N.

Definition N2R n := IZR (Z.of_N n).
Definition N2Q n := inject_Z (Z.of_N n).

Definition to_R '(a,b) : R := (N2R a - N2R b * τ)%R.

Definition to_QQ '(a,b) : Q*Q :=
  (N2Q a - N2Q b * snd tau100, N2Q a - N2Q b * fst tau100)%Q.

Lemma to_QQ_ok ab :
  Approx (fst (to_QQ ab)) (to_R ab) (snd (to_QQ ab)).
Proof.
 assert (H := tau100_approx).
 destruct ab as (a,b). cbn -[to_QQ].
 unfold to_QQ. unfold fst at 1. unfold snd at 2.
 apply minus_approx. apply IZR_approx.
 apply mult_approx. apply IZR_approx. apply H. red; simpl; lia. easy.
Qed.

Definition ltb '(a1,b1) '(a2,b2) :=
  let r := (Z.of_N a1 - Z.of_N a2)%Z in
  let s := (Z.of_N b1 - Z.of_N b2)%Z in
  match r, s with
  | Z.pos _, Z.pos _ => (r*(r^3+s^3) <? s^4)%Z
  | Z.neg _, Z.neg _ => (s^4 <? r*(r^3+s^3))%Z
  | Z.neg _, _ => true
  | _, Z.pos _ => true
  | _, _ => false
  end.

Lemma ltb_spec ab1 ab2 : ltb ab1 ab2 = true <-> (to_R ab1 < to_R ab2)%R.
Proof.
 destruct ab1 as (a1,b1), ab2 as (a2,b2).
 cbn -[Z.pow].
 rewrite Rminus_lt_0.
 set (r := (Z.of_N a1 - Z.of_N a2)%Z) in *.
 set (s := (Z.of_N b1 - Z.of_N b2)%Z) in *.
 replace (_-_-_)%R with (τ*IZR s - IZR r)%R.
 2:{ unfold r, s, N2R. rewrite !minus_IZR. ring. }
 rewrite <- Rminus_lt_0.
 destruct r as [|r|r], s as [|s|s]; try rewrite Rmult_0_r.
 - lra.
 - split; intros. apply Rmult_lt_0_compat. approx. now apply IZR_lt. easy.
 - split. easy. intros H. exfalso. revert H. apply Rle_not_lt.
   apply Rcomplements.Rmult_le_0_l. approx. now apply IZR_le.
 - split. easy. intros H. apply lt_IZR in H. lia.
 - rewrite <- Rcomplements.Rlt_div_l by now apply IZR_lt.
   unfold τ. rewrite <- Ptau_lt1_iff; try easy.
   2:{ apply Rcomplements.Rdiv_le_0_compat.
       now apply IZR_le. now apply IZR_lt. }
   unfold Ptau. set (r' := Z.pos r). set (s' := Z.pos s).
   rewrite Z.ltb_lt.
   split; intros LT.
   + apply Rmult_lt_reg_r with (IZR s'^4)%R.
     { rewrite pow_IZR. apply IZR_lt; lia. }
     field_simplify. 2:{ apply IZR_neq. lia. }
     rewrite !pow_IZR, <- !mult_IZR, <- plus_IZR. apply IZR_lt.
     simpl Z.of_nat. now ring_simplify in LT.
   + apply Rmult_lt_compat_r with (r := (IZR s'^4)%R) in LT.
     2:{ rewrite pow_IZR. apply IZR_lt; lia. }
     field_simplify in LT. 2:{ try (*compat*) revert LT. apply IZR_neq. lia. }
     rewrite !pow_IZR, <- !mult_IZR, <- plus_IZR in LT. apply lt_IZR in LT.
     simpl Z.of_nat in LT. now ring_simplify.
 - split. easy. intros H. exfalso. revert H. apply Rle_not_lt.
   apply Rle_trans with 0%R; [|now apply IZR_le].
   apply Rcomplements.Rmult_le_0_l. approx. now apply IZR_le.
 - split; intros. now apply IZR_lt. easy.
 - split; intros; trivial. apply Rlt_trans with 0%R; [now apply IZR_lt|].
   apply Rmult_lt_0_compat. approx. now apply IZR_lt.
 - rewrite Z.ltb_lt.
   set (r' := Z.neg r). set (s' := Z.neg s).
   rewrite Rminus_lt_0. replace (_ - _)%R with (IZR (-r') - τ * IZR (-s'))%R.
   2:{ rewrite !opp_IZR. lra. }
   rewrite <- Rminus_lt_0.
   rewrite Rcomplements.Rlt_div_r by (apply IZR_lt; lia).
   unfold τ. rewrite <- Ptau_gt1_iff; try easy.
   2:{ apply Rcomplements.Rdiv_le_0_compat.
       now apply IZR_le. now apply IZR_lt. }
   unfold Ptau.
   split; intros LT.
   + apply Rmult_lt_reg_r with (IZR (-s')^4)%R.
     { rewrite pow_IZR. apply IZR_lt; lia. }
     field_simplify. 2:{ apply IZR_neq. lia. }
     rewrite !pow_IZR, <- !mult_IZR, <- plus_IZR. apply IZR_lt.
     simpl Z.of_nat. ring_simplify. now ring_simplify in LT.
   + apply Rmult_lt_compat_r with (r := (IZR (-s')^4)%R) in LT.
     2:{ rewrite pow_IZR. apply IZR_lt; lia. }
     field_simplify in LT. 2:{ try (*compat*) revert LT. apply IZR_neq. lia. }
     rewrite !pow_IZR, <- !mult_IZR, <- plus_IZR in LT. apply lt_IZR in LT.
     simpl Z.of_nat in LT. ring_simplify in LT. now ring_simplify.
Qed.

Definition max ab cd := if ltb ab cd then cd else ab.
Definition min ab cd := if ltb cd ab then cd else ab.

Definition add '(a,b) '(c,d) := (a+c,b+d).

Lemma add_ok ab cd : to_R (add ab cd) = (to_R ab + to_R cd)%R.
Proof.
 destruct ab as (a,b), cd as (c,d). simpl.
 unfold N2R. rewrite !N2Z.inj_add, !plus_IZR. lra.
Qed.

Lemma max_ok ab cd : to_R (max ab cd) = Rmax (to_R ab) (to_R cd).
Proof.
 unfold max.
 destruct (ltb ab cd) eqn:E.
 - rewrite ltb_spec in E. rewrite Rmax_right; trivial. lra.
 - rewrite <- not_true_iff_false, ltb_spec in E.
   rewrite Rmax_left; trivial. lra.
Qed.

Lemma min_ok ab cd : to_R (min ab cd) = Rmin (to_R ab) (to_R cd).
Proof.
 unfold min.
 destruct (ltb cd ab) eqn:E.
 - rewrite ltb_spec in E. rewrite Rmin_right; trivial. lra.
 - rewrite <- not_true_iff_false, ltb_spec in E.
   rewrite Rmin_left; trivial. lra.
Qed.

(** Simultaneous computations of (diff 4 (A 4 n)) and (MaxDeltas 4) *)

Record buffer := Buffer { d0:t; d1:t; d2:t; d3:t; m0:t; m1:t; m2:t; m3:t }.

Definition max_init := Buffer (1,1) (1,2) (2,3) (3,4) (0,0) (1,1) (1,1) (1,1).
Definition max_next '(Buffer d1 d2 d3 d4 m1 m2 m3 m4) :=
  Buffer d2 d3 d4 (add d1 d4) m2 m3 m4 (max m4 (add m1 d4)).
Definition max_loop (n:N) := N.iter (n-3) max_next max_init.
Definition maxdeltas (n:N) := (max_loop n).(m3).

Definition min_init := Buffer (1,1) (1,2) (2,3) (3,4) (0,0) (0,0) (1,2) (1,2).
Definition min_next '(Buffer d0 d1 d2 d3 m0 m1 m2 m3) :=
  Buffer d1 d2 d3 (add d0 d3) m1 m2 m3 (min m3 (add m0 d3)).
Definition min_loop (n:N) := N.iter (n-3) min_next min_init.
Definition mindeltas (n:N) := (min_loop n).(m3).

Lemma max_loop_spec (n:nat) :
  let '(Buffer d0 d1 d2 d3 m0 m1 m2 m3) := max_loop (N.of_nat n + 3) in
  to_R d0 = diff 4 (A 4 n) /\
  to_R d1 = diff 4 (A 4 (n+1)) /\
  to_R d2 = diff 4 (A 4 (n+2)) /\
  to_R d3 = diff 4 (A 4 (n+3)) /\
  to_R m0 = MaxDeltas 4 n /\
  to_R m1 = MaxDeltas 4 (n+1) /\
  to_R m2 = MaxDeltas 4 (n+2) /\
  to_R m3 = MaxDeltas 4 (n+3).
Proof.
 unfold max_loop.
 rewrite N2Nat.inj_iter.
 replace (N.to_nat (_+3-3)) with n by lia.
 induction n.
 - simpl; unfold diff. fold τ. unfold N2R. simpl.
   rewrite (Rmax_right 0) by approx.
   rewrite (Rmax_left (_+_)) by approx. repeat split; try lra.
   rewrite Rmax_left by approx. lra.
 - simpl Nat.iter. destruct (Nat.iter _ _ _) as [d0 d1 d2 d3 m0 m1 m2 m3].
   unfold max_next.
   replace (S n + 2)%nat with (n+3)%nat by lia.
   replace (S n + 1)%nat with (n+2)%nat by lia.
   replace (S n)%nat with (n+1)%nat at 1 3 by lia.
   destruct IHn as (IH1 & IH2 & IH3 & IH4 & IH1' & IH2' & IH3' & IH4').
   repeat split; trivial.
   + rewrite add_ok, IH1, IH4.
     simpl. rewrite (Nat.add_comm (A 4 _)).
     rewrite diff_A_A by lia. f_equal. f_equal. f_equal. lia.
   + rewrite max_ok, add_ok. simpl. f_equal; trivial.
     f_equal; trivial. rewrite IH1'. f_equal. lia.
Qed.

Lemma maxdeltas_spec (n:nat) : (3 <= n)%nat ->
  MaxDeltas 4 n = to_R (maxdeltas (N.of_nat n)).
Proof.
 intros Hn. unfold maxdeltas.
 assert (H := max_loop_spec (n-3)).
 replace (N.of_nat (n-3) + 3)%N with (N.of_nat n) in H by lia.
 destruct (max_loop _); simpl in *.
 replace (n-3+3)%nat with n in H by lia. symmetry. apply H.
Qed.

Definition checkapprox a b '(q1,q2) := Qle_bool a q1 && Qle_bool q2 b.

Lemma checkapprox_ok a b qq :
 checkapprox a b qq = true -> (a <= fst qq)%Q /\ (snd qq <= b)%Q.
Proof.
 unfold checkapprox. destruct qq as (q1,q2).
 now rewrite andb_true_iff, !Qle_bool_iff.
Qed.

Lemma maxdeltas_approx n a b : (3 <= n)%nat ->
 checkapprox a b (to_QQ (maxdeltas (N.of_nat n))) = true
 -> Approx a (MaxDeltas 4 n) b.
Proof.
 intros Hn H. rewrite (maxdeltas_spec n Hn).
 eapply approx_trans; [apply to_QQ_ok| | ]; eapply checkapprox_ok; eauto.
Qed.

Lemma min_loop_spec (n:nat) :
  let '(Buffer d0 d1 d2 d3 m0 m1 m2 m3) := min_loop (N.of_nat n + 3) in
  to_R d0 = diff 4 (A 4 n) /\
  to_R d1 = diff 4 (A 4 (n+1)) /\
  to_R d2 = diff 4 (A 4 (n+2)) /\
  to_R d3 = diff 4 (A 4 (n+3)) /\
  to_R m0 = MinDeltas 4 n /\
  to_R m1 = MinDeltas 4 (n+1) /\
  to_R m2 = MinDeltas 4 (n+2) /\
  to_R m3 = MinDeltas 4 (n+3).
Proof.
 unfold min_loop.
 rewrite N2Nat.inj_iter.
 replace (N.to_nat (_+3-3)) with n by lia.
 induction n.
 - simpl; unfold diff. fold τ. unfold N2R. simpl.
   rewrite (Rmin_left 0) by approx.
   rewrite (Rmin_right 0) by approx. repeat split; try lra.
   rewrite Rmin_left by approx. lra.
 - simpl Nat.iter. destruct (Nat.iter _ _ _) as [d1 d2 d3 m1 m2 m3].
   unfold min_next.
   replace (S n + 2)%nat with (n+3)%nat by lia.
   replace (S n + 1)%nat with (n+2)%nat by lia.
   replace (S n)%nat with (n+1)%nat at 1 3 by lia.
   destruct IHn as (IH1 & IH2 & IH3 & IH4 & IH1' & IH2' & IH3' & IH4').
   repeat split; trivial.
   + rewrite add_ok, IH1, IH4.
     simpl. rewrite (Nat.add_comm (A 4 _)).
     rewrite diff_A_A by lia. f_equal. f_equal. f_equal. lia.
   + rewrite min_ok, add_ok. simpl. f_equal; trivial.
     f_equal; trivial. rewrite IH1'. f_equal. lia.
Qed.

Lemma mindeltas_spec (n:nat) : (3 <= n)%nat ->
  MinDeltas 4 n = to_R (mindeltas (N.of_nat n)).
Proof.
 intros Hn. unfold mindeltas.
 assert (H := min_loop_spec (n-3)).
 replace (N.of_nat (n-3) + 3)%N with (N.of_nat n) in H by lia.
 destruct (min_loop _); simpl in *.
 replace (n-3+3)%nat with n in H by lia. symmetry. apply H.
Qed.

Lemma mindeltas_approx n a b : (3 <= n)%nat ->
 checkapprox a b (to_QQ (mindeltas (N.of_nat n))) = true
 -> Approx a (MinDeltas 4 n) b.
Proof.
 intros Hn H. rewrite (mindeltas_spec n Hn).
 eapply approx_trans; [apply to_QQ_ok| | ]; eapply checkapprox_ok; eauto.
Qed.

End NN.

(** Taking n=600 is enough to get 15 decimal digits of precision *)

#[local] Instance maxdeltas_600 :
  Approx 1.58346877932474708 (MaxDeltas 4 600) 1.58346877932474715.
Proof.
 apply NN.maxdeltas_approx. lia. now vm_compute.
Qed.

(** Now we bound (residue 3 roots 600). *)

Definition restν := Cmod (coefdA 4 ν)/(1 - Rabs ν^4).
Definition restα := 2*Cmod (coefdA 4 α)/(1 - Cmod α^4).

Lemma residue4_eqn n :
  residue 4 roots n = restα * Cmod α^n + restν * Rabs ν^n.
Proof.
 unfold residue, roots. cbn -[pow ν].
 change αbar with (Cconj α). rewrite coefdA_conj, !Cmod_Cconj.
 rewrite Rplus_0_r, <- Rplus_assoc, <- double.
 unfold restα, restν. rewrite Cmod_R. field. approx.
Qed.

#[local] Instance : Approx 0.25 restν 0.26.
Proof.
 unfold restν. unfold coefdA, coefA. fold τ.
 rewrite !INR_IZR_INZ. cbn -[pow Cpow ν].
 rewrite RtoC_pow, <- RtoC_inv, <- !RtoC_mult, <- !RtoC_minus.
 rewrite <- RtoC_div, <- RtoC_mult, Cmod_R. approx.
Qed.

#[local] Instance : Approx 1.93 restα 1.94.
Proof.
 unfold restα. unfold coefdA, coefA. fold τ.
 rewrite !INR_IZR_INZ. cbn -[pow Cpow].
 unfold Cdiv. rewrite !Cmod_mult, Cmod_pow. change 4%nat with (2*2)%nat.
 rewrite pow_mult, αmod2. rewrite Cmod_inv. approx.
Qed.

Lemma residue4_600_upper : residue 4 roots 600 < 3 * / 10^16.
Proof.
 rewrite residue4_eqn.
 apply Rle_lt_trans with (1.2*restα * Cmod α ^600).
 { replace 1.2 with (1+0.2) by lra.
   rewrite !Rmult_plus_distr_r, Rmult_1_l. apply Rplus_le_compat_l.
   apply Rmult_le_compat. approx. apply pow_le; approx. approx.
   apply Rpow_le_compat_r. approx. approx. }
 change (600)%nat with (2*300)%nat. rewrite pow_mult, αmod2.
 apply Rmult_lt_reg_r with (10^16). apply pow_lt; lra.
 rewrite (Rmult_assoc 3), Rinv_l. 2:{ apply pow_nonzero. lra. }
 replace (10^16) with (Q2R (10^16)).
 2:{ replace 10 with (Q2R 10). now rewrite <- Q2R_pow. apply Q2R_IZR. }
 rewrite (Rmult_comm _ (Q2R _)), <- Rmult_assoc.
 apply Rlt_trans with ((Q2R (10 ^ 16) * (1.2 * restα)) * 0.885^300); [|approx].
 apply Rmult_lt_compat_l. approx.
 apply Rpow_lt_compat_r. lia. approx. approx.
Qed.

#[local] Instance sup_deltas_approx :
  Approx 1.5834687793247470 (sup_deltas' 4) 1.5834687793247475.
Proof.
 split.
 - eapply Rle_trans;
   [|apply (MaxDeltas_below_lim' 4 lia roots) with (p:=600%nat)].
   approx. apply roots_sorted. unfold roots, Cnth; simpl; approx.
 - eapply Rle_trans;
   [apply (sup_deltas_upper 4 lia roots) with (p:=600%nat)|].
   apply roots_sorted. unfold roots, Cnth; simpl; approx.
   eapply Rle_trans;
   [apply Rplus_le_compat_l; apply Rlt_le; apply residue4_600_upper|].
   approx.
Qed.

(* Print Assumptions sup_deltas_approx. *)

(* Current final precision : below 1O^-15 *)

#[local] Instance mindeltas_600 :
  Approx (-1.5060895457389588) (MinDeltas 4 600) (-1.5060895457389585).
Proof.
 apply NN.mindeltas_approx. lia. now vm_compute.
Qed.

#[local] Instance inf_deltas_approx :
  Approx (-1.5060895457389591) (inf_deltas' 4) (-1.5060895457389585).
Proof.
 split.
 - eapply Rle_trans;
   [|apply (inf_deltas_lower 4 lia roots) with (p:=600%nat)].
   2:apply roots_sorted. 2:unfold roots, Cnth; simpl; approx.
   eapply Rle_trans;
   [|apply Rplus_le_compat_l, Ropp_le_contravar, Rlt_le;
     apply residue4_600_upper].
   approx.
 - eapply Rle_trans;
   [apply (MinDeltas_above_lim' 4 lia roots) with (p:=600%nat)|].
   apply roots_sorted. unfold roots, Cnth; simpl; approx. approx.
Qed.

Lemma diff_bound n : -1.5060895457389591 <= diff 4 n <= 1.5834687793247475.
Proof.
 split.
 - apply Rle_trans with (inf_deltas' 4). approx.
   apply diff_ge_inf' with roots. lia. apply roots_sorted.
   unfold roots, Cnth; simpl; approx.
 - apply Rle_trans with (sup_deltas' 4).
   apply diff_le_sup' with roots. lia. apply roots_sorted.
   unfold roots, Cnth; simpl; approx. approx.
Qed.

Lemma abs_diff_bound n : Rabs (diff 4 n) <= 1.5834687793247475.
Proof.
 apply Rabs_le. generalize (diff_bound n). lra.
Qed.



(** ** Occurrences of letters in morphic word [Words.kseq 4]

    We will see below how this relates to function [f 4])
    and its iterates.

    For a finite word [w], the frequency of letter [a] is
    [nbocc a w / length w]. For infinite words, the frequency
    of a letter (if it exists) is the limit of frequencies for
    ever-growing finite prefixes of the infinite word.

    Here for [Words.kseq 4], the frequencies of letters [0],[1],[2],[3]
    will be respectively [τ^4],[τ^5],[τ^6],[τ^3]
    (another numbering of letters would make that more uniform).
    For proving that and even more, we now consider the following
    differences :
*)

Definition Diff0 w := τ^4 * length w - nbocc 0 w.
Definition Diff1 w := τ^5 * length w - nbocc 1 w.
Definition Diff2 w := τ^6 * length w - nbocc 2 w.
Definition Diff3 w := τ^3 * length w - nbocc 3 w.

Definition diff0 n := Diff0 (take n (kseq 4)).
Definition diff1 n := Diff1 (take n (kseq 4)).
Definition diff2 n := Diff2 (take n (kseq 4)).
Definition diff3 n := Diff3 (take n (kseq 4)).

(** One of these differences can be deduced from the other three. *)

Lemma Diff0123 w :
 List.Forall (fun a => a < 4)%nat w ->
 Diff0 w + Diff1 w + Diff2 w + Diff3 w = 0.
Proof.
 intros H.
 apply nbocc_total_lt in H. simpl in H.
 unfold Diff0, Diff1, Diff2, Diff3.
 rewrite τ4, τ5, τ6. ring_simplify.
 rewrite H, !plus_INR. change (INR 0) with 0. ring.
Qed.

Lemma diff0123 n : diff0 n + diff1 n + diff2 n + diff3 n = 0.
Proof.
 apply Diff0123.
 apply Forall_nth. intros i d. rewrite take_length. intros H.
 rewrite take_nth by trivial. now apply kseq_letters.
Qed.

(** Expressing diff0 and co in terms of [f 4] and [f 4^^2] and [f 4^^3] *)

Lemma diff0_alt n : diff0 n = f 4 n - τ * n.
Proof.
 unfold diff0, Diff0. rewrite take_length.
 rewrite <- count_nbocc.
 rewrite τ4. rewrite Rmult_minus_distr_r.
 rewrite <- (f_count_0 4 n) at 1 by lia. rewrite plus_INR. lra.
Qed.

Lemma diff0_alt' n : diff0 n = diff 4 n.
Proof.
 apply diff0_alt.
Qed.

Lemma diff3_alt n : diff3 n = τ^3 * n - fs 4 3 n.
Proof.
 unfold diff3, Diff3. rewrite take_length. f_equal. symmetry.
 rewrite <- count_nbocc. f_equal. exact (fs_count_km1 4 n).
Qed.

Lemma diff1_alt n : diff1 n = τ^5 * n + fs 4 2 n - f 4 n.
Proof.
 unfold diff1, Diff1. rewrite take_length.
 rewrite <- count_nbocc.
 change (f 4 n) with (fs 4 1 n).
 rewrite (fs_count_above 4 1) by lia.
 rewrite count_above_S.
 rewrite (fs_count_above 4 2) by lia.
 rewrite plus_INR. lra.
Qed.

Lemma diff2_alt n : diff2 n = τ^6 * n + fs 4 3 n - fs 4 2 n.
Proof.
 unfold diff2, Diff2. rewrite take_length.
 rewrite <- count_nbocc.
 rewrite (fs_count_above 4 2) by lia.
 rewrite (fs_count_above 4 3) by lia.
 rewrite (count_above_S (kseq 4) 2).
 rewrite plus_INR. lra.
Qed.

(** Equations giving Diff0 and co after a substitution [ksubst 4].
    In older revisions of this file, we also had these equations
    expressed via matrix. *)

Lemma Diff0_ksubst4 w : Diff0 (ksubstw 4 w) = τ * Diff3 w.
Proof.
 unfold Diff0, Diff3.
 rewrite len_ksubst, plus_INR.
 destruct (nbocc_ksubst4 w) as (-> & _ & _ & _).
 ring_simplify. unfold Rminus. rewrite Rplus_assoc. f_equal.
 rewrite τ4. simpl. lra.
Qed.

Lemma Diff3_ksubst4 w :
  List.Forall (fun a => a < 4)%nat w ->
  Diff3 (ksubstw 4 w) = - τ^3 * Diff3 w - Diff0 w - Diff1 w.
Proof.
 intros H.
 unfold Diff0, Diff1, Diff3.
 rewrite len_ksubst. simpl Nat.sub.
 destruct (nbocc_ksubst4 w) as (_ & _ & _ & ->).
 rewrite !plus_INR.
 ring_simplify. rewrite τ6, τ5, τ4. ring_simplify.
 rewrite !len_nbocc_0123 by trivial. rewrite !plus_INR. ring.
Qed.

Lemma Diff1_ksubst4 w :
  List.Forall (fun a => a < 4)%nat w ->
  Diff1 (ksubstw 4 w) = - τ^5 * Diff3 w + Diff0 w.
Proof.
 intros H.
 unfold Diff0, Diff1, Diff3.
 rewrite len_ksubst. simpl Nat.sub.
 destruct (nbocc_ksubst4 w) as (_ & -> & _ & _).
 rewrite !plus_INR.
 ring_simplify. replace (τ^8) with ((τ^4)^2) by ring.
 rewrite τ5, τ4. ring_simplify.
 rewrite !len_nbocc_0123 by trivial. rewrite !plus_INR. ring.
Qed.


(** We now reuse the bound for diff: *)

Lemma diff0_bound n : Rabs (diff0 n) <= 1.5834687793247475.
Proof.
 rewrite diff0_alt'. apply abs_diff_bound.
Qed.

Lemma diff0_lt_2 n : Rabs (diff0 n) < 2.
Proof.
 eapply Rle_lt_trans. apply diff0_bound. lra.
Qed.

(* Print Assumptions diff0_lt_2. *)

(** Even the sup of |diff0| is strictly less than 2. *)

Lemma sup_diff0_lt_2 :
 Rbar.Rbar_lt (Sup_seq (fun n => Rabs (diff0 n))) 2.
Proof.
 apply Rbar.Rbar_le_lt_trans with (Sup_seq (fun _ => 1.6)).
 - apply Sup_seq_le. intros n. simpl.
   eapply Rle_trans. apply diff0_bound. lra.
 - replace (Sup_seq _) with (Rbar.Finite 1.6); simpl. approx.
   symmetry. apply is_sup_seq_unique. apply is_sup_seq_const.
Qed.

(* Consequences for f4 : *)

Lemma f4_alt n : INR (f 4 n) = τ*n + diff0 n.
Proof.
 rewrite diff0_alt; lra.
Qed.

Lemma f4_close_τn (n:nat) : -2 < τ*n - f 4 n < 2.
Proof.
 rewrite f4_alt.
 assert (H := diff0_lt_2 n).
 rewrite Rcomplements.Rabs_lt_between in H. lra.
Qed.

Lemma f4_natpart_lower (n:nat) :
 (nat_part (τ*n) <= 1 + f 4 n)%nat.
Proof.
assert (LT := f4_close_τn n).
assert (LE : 0 <= τ*n).
{ apply Rmult_le_pos. approx. apply pos_INR. }
assert (H : 0 <= τ*n < INR(2 + f 4 n)).
{ rewrite plus_INR. simpl. lra. }
apply nat_part_lt in H. lia.
Qed.

Lemma f4_natpart_higher (n:nat) :
 (f 4 n <= nat_part (τ*n) + 2)%nat.
Proof.
assert (LT := f4_close_τn n).
assert (LE : 0 <= τ*n).
{ apply Rmult_le_pos. approx. apply pos_INR. }
assert (INR(f 4 n - 2) <= τ*n).
{ destruct (Nat.le_gt_cases (f 4 n) 2).
  - replace (f 4 n - 2)%nat with O by lia. simpl. lra.
  - rewrite minus_INR by lia. simpl. lra. }
apply nat_part_le in H; auto; lia.
Qed.

Lemma f4_close_natpart (n:nat) :
 (nat_part (τ*n) - 1 <= f 4 n <= nat_part (τ*n) + 2)%nat.
Proof.
split; [|apply f4_natpart_higher]. generalize (f4_natpart_lower n); lia.
Qed.

(* NB: both lower and upper bounds are reached. *)

(* A quasi-additivity result for f 4 that I was unable to obtain
   directly on f 4.
   Note : the -4 and +4 constants do not seem to be reached, maybe
   -3 and 3 could do ? *)

Lemma f4_quasiadd p n :
 (f 4 p + f 4 n -4 <= f 4 (p+n) <= f 4 p + f 4 n + 4)%nat.
Proof.
split.
 - destruct (Nat.le_gt_cases (f 4 p + f 4 n) 4); try lia.
   assert (f 4 p + f 4 n < f 4 (p+n) +5)%nat; try lia.
   apply INR_lt. rewrite !plus_INR. rewrite (INR_IZR_INZ 5). simpl.
   generalize (diff_bound p) (diff_bound n) (diff_bound (p+n)).
   unfold diff in *. rewrite plus_INR. lra.
 - rewrite <- Nat.lt_succ_r.
   apply INR_lt. rewrite S_INR, !plus_INR. rewrite (INR_IZR_INZ 4). simpl.
   generalize (diff_bound p) (diff_bound n) (diff_bound (p+n)).
   unfold diff in *. rewrite plus_INR. lra.
Qed.

(* Print Assumptions f4_quasiadd. *)

(** To finish someday, less interesting : frequencies for the other letters. *)
