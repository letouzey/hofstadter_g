From Coq Require Import Bool Arith Lia QArith Reals Lra Qreals Qminmax.
From QuantumLib Require Import Complex Polynomial Matrix.
Require Import MoreList MoreReals MoreLim MoreComplex MorePoly MoreMatrix.
Require Import DeltaList FunG GenFib GenG GenAdd Words Mu ThePoly.
Import Permutation.
Local Open Scope Z.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.
Local Set Printing Coercions.

(** TODO move elsewhere *)

Lemma Qpos_or_neg (x y:Q) :
 Z.eqb (Qsgn x) 1%Z || Z.eqb (Qsgn y) (-1)%Z = true ->
 (0 < x \/ y < 0)%Q.
Proof.
 case Z.eqb_spec; simpl. rewrite Qsgn_pos; now left.
 intros _. rewrite Z.eqb_eq, Qsgn_neg. now right.
Qed.

Ltac qle := apply Qle_bool_imp_le; vm_compute; reflexivity.
Ltac qlt := apply Qle_bool_nimp_lt; vm_compute; reflexivity.
Ltac qposneg := apply Qpos_or_neg; vm_compute; reflexivity.

#[local] Hint Extern 3 (Qle _ _) => qle : typeclass_instances.
#[local] Hint Extern 3 (Qlt _ _) => qlt : typeclass_instances.
#[local] Hint Extern 3 (Qlt _ _ \/ Qlt _ _) => qposneg : typeclass_instances.

(** A little real approximation library *)

Class Approx (low:Q)(r:R)(high:Q) := the_approx : Q2R low <= r <= Q2R high.

#[global] Instance Q2R_approx q : Approx q (Q2R q) q.
Proof. red. lra. Qed.

#[global] Instance IZR_approx z : Approx (inject_Z z) (IZR z) (inject_Z z).
Proof. rewrite <- Q2R_IZR. typeclasses eauto. Qed.

#[global] Instance plus_approx {a r b a' r' b'} :
  Approx a r b -> Approx a' r' b' -> Approx (a+a') (r+r') (b+b').
Proof.
 unfold Approx. intros. rewrite !Q2R_plus. lra.
Qed.

#[global] Instance opp_approx {a r b} :
  Approx a r b -> Approx (-b) (-r) (-a).
Proof.
 unfold Approx. intros. rewrite !Q2R_opp. lra.
Qed.

#[global] Instance minus_approx {a r b a' r' b'} :
  Approx a r b -> Approx a' r' b' -> Approx (a-b') (r-r') (b-a').
Proof.
 intros. unfold Qminus, Rminus. typeclasses eauto.
Qed.

#[global] Instance mult_approx {a r b a' r' b'} :
  Approx a r b -> Approx a' r' b' -> (0 <= a)%Q -> (0 <= a')%Q ->
  Approx (a*a') (r*r') (b*b').
Proof.
 unfold Approx. intros A A' LE LE'. rewrite !Q2R_mult.
 apply Qle_Rle in LE,LE'. split; apply Rmult_le_compat; lra.
Qed.

Definition Qmult_lb a b a' b' := Qmin4 (a*a') (a*b') (b*a') (b*b').
Definition Qmult_ub a b a' b' := Qmax4 (a*a') (a*b') (b*a') (b*b').

#[global] Instance mult_approx_gen {a r b a' r' b'} :
  Approx a r b -> Approx a' r' b' ->
  Approx (Qmult_lb a b a' b') (r*r') (Qmult_ub a b a' b').
Proof.
 unfold Approx. intros A A'. unfold Qmult_lb, Qmult_ub. split.
 - generalize (Qmin4_ok (a*a') (a*b') (b*a') (b*b')).
   set (m := Qmin4 _ _ _ _). cbn. intros (LE1 & LE2 & LE3 &LE4).
   clearbody m.
   apply Qle_Rle in LE1,LE2,LE3,LE4. rewrite !Q2R_mult in *.
   generalize (Rmult_ge_lowerbound _ _ _ _ _ _ A A'). lra.
 - generalize (Qmax4_ok (a*a') (a*b') (b*a') (b*b')).
   set (m := Qmax4 _ _ _ _). cbn. intros (LE1 & LE2 & LE3 &LE4).
   clearbody m.
   apply Qle_Rle in LE1,LE2,LE3,LE4. rewrite !Q2R_mult in *.
   generalize (Rmult_le_upperbound _ _ _ _ _ _ A A'). lra.
Qed.

Definition Qpow_lb a b n :=
  if Nat.eqb n 0 || Nat.odd n then (a^Z.of_nat n)%Q
  else if Z.eqb (Qsgn a) (-1) && Z.eqb (Qsgn b) 1 then 0%Q
  else Qmin (a^Z.of_nat n) (b^Z.of_nat n).

Definition Qpow_ub a b n := Qmax (a^Z.of_nat n) (b^Z.of_nat n).

#[global] Instance pow_approx {a r b} (n:nat) :
  Approx a r b -> Approx (Qpow_lb a b n) (r^n) (Qpow_ub a b n).
Proof.
 unfold Approx. intros A.
 destruct (Nat.eqb n 0) eqn:ZE.
 { rewrite Nat.eqb_eq in ZE. subst n. unfold Qpow_lb, Qpow_ub; cbn. lra. }
 unfold Qpow_lb. rewrite ZE.
 destruct (Nat.odd n) eqn:OD; cbn.
 - (* n odd *)
   rewrite Nat.odd_spec in OD.
   unfold Qpow_ub. rewrite Q.max_r.
   + rewrite !Q2R_pow. split; apply pow_incr_odd; trivial; lra.
   + apply Rle_Qle. rewrite !Q2R_pow. apply pow_incr_odd; trivial; lra.
 - (* n even *)
   rewrite <- Nat.negb_even in OD.
   assert (EV : Nat.even n = true) by now destruct Nat.even.
   rewrite Nat.even_spec in EV. clear OD.
   case Z.eqb_spec; simpl; intros Ha.
   + rewrite Qsgn_neg in Ha.
     case Z.eqb_spec; simpl; intros Hb.
     * rewrite Qsgn_pos in Hb.
       split. replace (Q2R 0) with 0 by lra. now apply pow_even_nonneg.
       destruct (Rle_lt_dec 0 r).
       { apply Rle_trans with (Q2R (b^Z.of_nat n)).
         - rewrite Q2R_pow. apply pow_incr; lra.
         - apply Qle_Rle. apply Q.le_max_r. }
       { apply Rle_trans with (Q2R (a^Z.of_nat n)).
         - rewrite Q2R_pow. apply pow_decr_even_neg; auto. lra.
         - apply Qle_Rle. apply Q.le_max_l. }
     * rewrite Qsgn_pos in Hb. apply Qnot_lt_le in Hb. apply Qle_Rle in Hb.
       rewrite Q.min_r. unfold Qpow_ub. rewrite Q.max_l.
       rewrite !Q2R_pow. split; apply pow_decr_even_neg; trivial; lra.
       apply Rle_Qle. rewrite !Q2R_pow.
       apply pow_decr_even_neg; trivial; lra.
       apply Rle_Qle. rewrite !Q2R_pow.
       apply pow_decr_even_neg; trivial; lra.
   + rewrite Qsgn_neg in Ha. apply Qnot_lt_le in Ha. apply Qle_Rle in Ha.
     rewrite Q.min_l. unfold Qpow_ub. rewrite Q.max_r.
     rewrite !Q2R_pow. split; apply pow_incr; lra.
     apply Rle_Qle. rewrite !Q2R_pow. apply pow_incr; lra.
     apply Rle_Qle. rewrite !Q2R_pow. apply pow_incr; lra.
Qed.

#[global] Instance inv_approx {a r b} :
  Approx a r b -> (0 < a \/ b < 0)%Q -> Approx (/b) (/r) (/a).
Proof.
 unfold Approx. intros A [LT|LT]; apply Qlt_Rlt in LT.
 - rewrite !Q2R_inv by (intro E; rewrite E in *; lra).
   split; apply Rinv_le_contravar; lra.
 - rewrite !Q2R_inv by (intro E; rewrite E in *; lra).
   split; apply Ropp_le_cancel; rewrite <- !Rinv_opp;
    apply Rinv_le_contravar; lra.
Qed.

#[global] Instance div_approx {a r b a' r' b'} :
  Approx a r b -> Approx a' r' b' -> (0 <= a)%Q -> (0 < a')%Q ->
  Approx (a/b') (r/r') (b/a').
Proof.
 unfold Rdiv, Qdiv. intros A A' LE LT.
 apply mult_approx; trivial. apply inv_approx; auto.
 clear A LE. red in A'. apply Rle_Qle. apply Qlt_Rlt in LT.
 rewrite !Q2R_inv by (intro E; rewrite E in *; lra).
 assert (Hb : 0 < Q2R b') by lra.
 apply Rinv_0_lt_compat in Hb. lra.
Qed.

Lemma approx_trans {a a' r b b'} :
 Approx a r b -> (a'<=a)%Q -> (b<=b')%Q -> Approx a' r b'.
Proof.
 unfold Approx. intros A LE LE'. apply Qle_Rle in LE,LE'. lra.
Qed.

(* UNUSED ?
Class HasApprox (r:R) := { low:Q; high:Q; prf:Approx low r high }.

#[global] Instance Q2R_apx q : HasApprox (Q2R q).
Proof. econstructor. typeclasses eauto. Defined.

#[global] Instance IZR_apx z : HasApprox (IZR z).
Proof. econstructor. typeclasses eauto. Defined.

#[global] Instance plus_apx {r r'} :
  HasApprox r -> HasApprox r' -> HasApprox (r+r').
Proof. intros (a,b,A) (a',b',A'). econstructor. typeclasses eauto. Defined.

#[global] Instance opp_apx {r} : HasApprox r -> HasApprox (-r).
Proof. intros (a,b,A). econstructor. typeclasses eauto. Defined.

#[global] Instance minus_apx {r r'} :
  HasApprox r -> HasApprox r' -> HasApprox (r-r').
Proof. intros (a,b,A) (a',b',A'). econstructor. typeclasses eauto. Defined.

#[global] Instance mult_apx {r r'} :
  HasApprox r -> HasApprox r' -> HasApprox (r*r').
Proof.
 intros (a,b,A) (a',b',A'). econstructor. eapply mult_approx_gen; eauto.
Defined.

#[global] Instance pow_apx {r} (n:nat) : HasApprox r -> HasApprox (r^n).
Proof.
 intros (a,b,A). econstructor. eapply pow_approx; eauto.
Defined.

Definition ApartZero {r} (apx:HasApprox r) :=
  (0 < apx.(low) \/ apx.(high) < 0)%Q.

#[global] Instance inv_apx {r} :
  forall apx : HasApprox r, ApartZero apx -> HasApprox (/r).
Proof.
 unfold Approx. intros (a,b,A) AZ.
 econstructor. eapply inv_approx; eauto.
Defined.

#[global] Instance div_apx {r r'} :
  HasApprox r -> forall apx : HasApprox r',
   ApartZero apx -> HasApprox (r/r').
Proof.
 intros. unfold Rdiv. apply mult_apx; trivial. now apply (inv_apx apx).
Defined.
*)

Ltac approximate r :=
  let A := fresh in
  assert (A : Approx _ r _) by once (typeclasses eauto 20);
  revert A.

Ltac approxnorm r :=
  approximate r;
  match goal with |- Approx ?a ?r ?b -> ?g =>
    let a' := (eval vm_compute in a) in
    let b' := (eval vm_compute in b) in
    change (Approx a' r b' -> g)
  end.

Ltac approx :=
 match goal with
 | |- Approx _ _ _ => eapply approx_trans; once (typeclasses eauto 20)
 | |- ?r <= ?r' =>
   let H := fresh in let H' := fresh in
   approximate r; intros (_,H); approximate r'; intros (H',_);
   eapply Rle_trans; [exact H| ]; eapply Rle_trans; [ |exact H'];
   apply Qle_Rle; qle
 | |- ?r < ?r' =>
   let H := fresh in let H' := fresh in
   approximate r; intros (_,H); approximate r'; intros (H',_);
   eapply Rle_lt_trans; [exact  H| ]; eapply Rlt_le_trans; [ |exact H'];
   apply Qlt_Rlt; qlt
 | |- ?r >= ?r' => apply Rle_ge; approx
 | |- ?r > ?r' => apply Rlt_gt; approx
 | |- ?r <> ?r' =>
   apply Rlt_dichotomy_converse; (left; approx)||(right; approx)
 | |- _ /\ _ => split; approx
 end.

(** * Studying case k=3

   We focus here on the case k=3, compute the complex roots of [X^4-X^3-1],
   and express (A 3 n) in term of combinations of powers of these roots.
   Then we study the frequencies in [Words.kseq 3] and the behaviour of
   function [f 3].
*)

Definition mu := mu 3.
Definition tau := tau 3.
Definition nu := nu 3.

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

#[local] Instance tau_approx : Approx 0.7244919590005 tau 0.7244919590006.
Proof. red. unfold tau. generalize tau_3. lra. Qed.

#[local] Instance mu_approx : Approx 1.380277569097 mu 1.380277569098.
Proof. red. unfold mu. generalize mu_3. lra. Qed.

#[local] Instance nu_approx : Approx (-0.819172513397) nu (-0.819172513396).
Proof. red. unfold nu. generalize nu_3. lra. Qed.

Ltac lra' :=
 generalize nu_approx mu_approx tau_approx; unfold Approx; lra.

#[local] Instance opp_nu_approx : Approx 0.819172513396 (-nu) 0.819172513397.
Proof. approx. Qed.

#[local] Instance inv_nu_approx : Approx  1.220744084604 (/-nu) 1.220744084607.
Proof. approx. Qed.

Lemma mu_nz : mu <> 0. Proof. approx. Qed.
Lemma nu_nz : nu <> 0. Proof. approx. Qed.
Lemma tau_nz : tau <> 0. Proof. approx. Qed.

(** The complex root of [X^4-X^3-1] *)

Definition re_alpha := (1 - mu - nu)/2.
Definition im_alpha := sqrt (tau/(-nu)-re_alpha^2).

Definition alpha : C := (re_alpha, im_alpha).
Definition alphabar : C := (re_alpha, - im_alpha).

#[local] Instance re_alpha_approx : Approx 0.2194474721 re_alpha 0.2194474722.
Proof. unfold re_alpha. approx. Qed.

Lemma re_alpha_nz : re_alpha <> 0.
Proof. approx. Qed.

#[local] Instance re_alpha_2_approx :
 Approx 0.0481571930 (re_alpha^2) 0.0481571931.
Proof. approx. Qed.

#[local] Instance tau_div_nu_approx :
 Approx 0.884419273293 (tau / -nu) 0.884419273296.
Proof. approx. Qed.

Lemma im_alpha_2_pos :  re_alpha ^ 2 < tau / - nu.
Proof. approx. Qed.

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

#[local] Instance alphamod2_approx :
 Approx 0.884419273293 ((Cmod alpha)^2) 0.884419273296.
Proof. rewrite alphamod2. approx. Qed.

Lemma pow2_approx_inv {a r b} :
  Approx (a^2) (r^2) (b^2) -> (0 <= a)%Q -> 0 <= r -> (0 <= b)%Q ->
  Approx a r b.
Proof.
 unfold Approx. intros p Ha Hr Hb.
 apply Qle_Rle in Ha,Hb. rewrite !Q2R_pow2 in p.
 rewrite <- !Rsqr_pow2 in p.
 split; apply Rsqr_incr_0; lra.
Qed.

(* TODO: general approx of sqrt ? *)

#[local] Instance alphamod_approx :
  Approx 0.9404356826 (Cmod alpha) 0.9404356828 |20.
Proof.
 apply pow2_approx_inv; try qle; try apply Cmod_ge_0. approx.
Qed.

Lemma alphamod_lt : 0 < Cmod alpha < 1.
Proof. approx. Qed.

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
 - approx.
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

Definition Diffs w : Vector 3 := mkvectR 3 [Diff3 w; Diff0 w; Diff1 w].
Definition diffs n : Vector 3 := mkvectR 3 [diff3 n; diff0 n; diff1 n].

Definition B : Square 3 :=
 list2D_to_matrix [ [-tau^3;-C1;-C1];[RtoC tau;C0;C0];[-tau^5;C1;C0] ]%C.

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
  rewrite ?RtoC_plus, ?RtoC_minus, ?RtoC_mult, ?RtoC_pow, ?RtoC_opp; ring.
Qed.

(* Initial vector of differences *)
Definition V0 : Vector 3 := mkvectR 3 [tau^3-1; tau^4; tau^5].

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

#[local] Hint Resolve WF_U WF_D WF_Dn : wf_db.

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
 apply Mat3_eq; auto with wf_db; unfold U, B, D; cbn -[nu pow Cpow];
  rewrite !Cplus_0_l; try ring;
  rewrite Ceq_minus; ring_simplify;
  rewrite !(RtoC_pow tau), tau5, RtoC_minus, <- !RtoC_pow; ring_simplify.
 - rewrite <- (P_factor_mu_eq0 alpha);
    [ ring | apply distinct_roots | apply alpha_is_Croot].
 - rewrite <- (P_factor_mu_eq0 alphabar);
    [ ring | apply distinct_roots | apply alphabar_is_Croot].
 - rewrite <- (P_factor_mu_eq0 nu);
    [ ring | apply RtoC_inj_neq, distinct_roots | apply nu_is_Croot].
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

Lemma Ci_conj : Cconj Ci = Copp Ci.
Proof.
 lca.
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
 - now apply im_alpha_nz.
 - compute in E. injection E; lra.
 - rewrite !RtoC_pow, <- !RtoC_opp, <- !RtoC_mult, <- !RtoC_plus in E.
   apply RtoC_inj in E. symmetry in E. revert E. apply Rlt_not_eq.
   approx.
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

#[local] Hint Resolve WF_invU_detU WF_invU : wf_db.

Lemma invU_detU_U : invU_detU × U = detU .* (I 3).
Proof.
 apply Mat3_eq; auto with wf_db;
  unfold detU, I, scale; cbn -[nu Cpow]; ring.
Qed.

Lemma U_invU_detU : U × invU_detU = detU .* (I 3).
Proof.
 apply Mat3_eq; auto with wf_db;
  unfold detU, I, scale; cbn -[nu Cpow]; ring.
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
 apply Mat3_eq; auto with wf_db.
Qed.

Lemma Dn_S n : Dn (S n) = D × Dn n.
Proof.
 apply Mat3_eq; auto with wf_db; unfold Dn, D; cbn -[nu]; ring.
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
Definition UV0nu := (nu^3/(nu-1))%C.

Definition coefa_detU := ((nu-alphabar)*UV0a)%C.
Definition coefnu_detU := ((alphabar-alpha)*UV0nu)%C.
Definition vecta := mkvect 3 [C1;-nu*alphabar;nu*alphabar+nu+alphabar]%C.
Definition vectnu :=
 mkvect 3 [C1;-alpha*alphabar;alpha*alphabar+alpha+alphabar]%C.

Definition coefsa := (/detU * coefa_detU) .* vecta.
Definition coefsnu := (/detU * coefnu_detU) .* vectnu.

Lemma alpha_neq_1 : alpha <> 1.
Proof.
 unfold alpha. intros [= ? ?].
 generalize re_alpha_approx; unfold Approx; lra.
Qed.

Lemma alphabar_neq_1 : alphabar <> 1.
 unfold alphabar. intros [= ? ?].
 generalize re_alpha_approx; unfold Approx; lra.
Qed.

Lemma alphabar_conj : Cconj alphabar = alpha.
Proof.
 unfold alpha, alphabar, Cconj; simpl; f_equal; lra.
Qed.

Lemma alpha_conj : Cconj alpha = alphabar.
Proof.
 unfold alpha, alphabar, Cconj; simpl; f_equal; lra.
Qed.

Lemma UV0a_conj : Cconj UV0a = (alphabar^3/(alphabar-1))%C.
Proof.
 unfold UV0a. rewrite Cdiv_conj by apply Cminus_eq_contra, alpha_neq_1.
 rewrite Cconj_minus_distr, Cpow_conj, alpha_conj. f_equal. f_equal. lca.
Qed.

Lemma U_V0_alt :
  U × V0 = mkvect 3 [UV0a;Cconj UV0a;UV0nu]%C.
Proof.
 apply Vect3_eq; auto with wf_db;
 unfold U, V0, scale; cbn -[nu Cpow pow];
 rewrite tau4, tau5; rewrite !RtoC_minus, <- !RtoC_pow.
 - rewrite <- (P_factor_mu_eq0 alpha);
   [ | apply distinct_roots | apply alpha_is_Croot ].
   ring_simplify.
   unfold UV0a.
   apply Cmult_eq_reg_l with (alpha-1)%C; try field_simplify;
    try apply Cminus_eq_contra, alpha_neq_1.
   rewrite alpha_is_Croot; field.
 - rewrite <- (P_factor_mu_eq0 alphabar);
   [ | apply distinct_roots | apply alphabar_is_Croot ].
   ring_simplify.
   rewrite UV0a_conj.
   apply Cmult_eq_reg_l with (alphabar-1)%C; try field_simplify;
    try apply Cminus_eq_contra, alphabar_neq_1.
   rewrite alphabar_is_Croot; field.
 - rewrite <- (P_factor_mu_eq0 nu);
   [ | apply RtoC_inj_neq,distinct_roots | apply nu_is_Croot ].
   ring_simplify.
   unfold UV0nu.
   apply Cmult_eq_reg_l with (nu-1)%C; try field_simplify;
    try (apply Cminus_eq_contra, RtoC_inj_neq; lra').
   rewrite nu_is_Croot; field.
Qed.

(** diffs for (A 3) numbers are linear combinations of little roots *)

Local Hint Rewrite Cconj_mult_distr Cconj_plus_distr Cconj_minus_distr
 Cconj_opp Cdiv_conj Cinv_conj Cconj_R Cpow_conj alphabar_conj alpha_conj
 : cconj.

Lemma diffs_A3_powers n :
  diffs (A 3 n) =
   (alpha^n .* coefsa .+ alphabar^n .* Mconj coefsa .+ nu^n .* coefsnu)%C.
Proof.
 rewrite diffs_A3, Bn_diag.
 unfold invU, coefsa, coefsnu.
 rewrite !Mscale_mult_dist_l.
 rewrite Mconj_scale, Cconj_mult_distr, Cinv_conj by apply detU_nz.
 rewrite detU_conj.
 replace (/-detU)%C with (/detU * (-1))%C by (field; apply detU_nz).
 rewrite !Mscale_assoc, !Cmult_assoc, !(Cmult_comm _ (/detU)),
  <-Cmult_assoc, <- !Mscale_assoc, <- !Mscale_plus_distr_r.
 f_equal.
 rewrite Mmult_assoc, U_V0_alt.
 assert (Hva : WF_Matrix vecta) by now apply WF_mkvect.
 assert (Hvnu : WF_Matrix vectnu) by now apply WF_mkvect.
 apply Vect3_eq; auto 7 with wf_db;
 unfold coefa_detU, coefnu_detU, Dn, invU_detU, vecta, vectnu;
 unfold scale, Mplus, Mconj; cbn -[nu Cpow pow];
 apply Ceq_minus; autorewrite with cconj; ring.
Qed.

(* In particular for diff0 : *)

Definition coefa0 := coefsa 1%nat 0%nat.
Definition coefnu0 := Re (coefsnu 1%nat 0%nat).

Lemma vectnu_alt :
 vectnu = mkvectR 3 [1; -Cmod alpha^2; Cmod alpha^2 + 2*re_alpha].
Proof.
 apply Vect3_eq; try (now apply WF_mkvect); try (now apply WF_mkvectR);
 unfold vectnu, mkvectR; rewrite !mkvect_eqn; cbn -[pow]; trivial.
 - rewrite RtoC_opp, Cmod2_conj, alpha_conj. ring.
 - change re_alpha with (Re alpha).
   rewrite RtoC_plus, RtoC_mult, Cmod2_conj, re_alt, alpha_conj. field.
Qed.

Lemma is_real_carac c : Im c = 0 <-> Cconj c = c.
Proof.
 split; intros H.
 - destruct c as (x,y); unfold Cconj, Im in *; simpl in *. subst.
   f_equal. lra.
 - destruct c as (x,y); unfold Cconj, Im in *; simpl in *. injection H.
   lra.
Qed.

Lemma coefsnu_real i : (i < 3)%nat -> Im (coefsnu i O) = 0.
Proof.
 assert (E0 : Cconj UV0nu = UV0nu).
 { unfold UV0nu. autorewrite with cconj; trivial.
   apply Cminus_eq_contra, RtoC_inj_neq; lra'. }
 assert (E : Im (/ detU * coefnu_detU) = 0).
 { rewrite is_real_carac. autorewrite with cconj; try apply detU_nz.
   rewrite detU_conj.
   unfold coefnu_detU. autorewrite with cconj. rewrite E0. field.
   apply detU_nz. }
 unfold coefsnu. rewrite vectnu_alt;
 intros Hi; destruct i as [|[|[| ] ] ]; try lia; clear Hi;
 unfold scale, mkvectR; rewrite mkvect_eqn; simpl nth;
 rewrite im_scal_r; apply Rmult_eq_0_compat_r; trivial.
Qed.

Lemma diff0_A3_powers n :
  diff0 (A 3 n) = 2 * Re (coefa0 * alpha^n) + coefnu0 * nu^n.
Proof.
  apply RtoC_inj.
  change (RtoC (diff0 (A 3 n))) with (diffs (A 3 n) 1%nat 0%nat).
  rewrite diffs_A3_powers.
  rewrite RtoC_plus, !RtoC_mult, <- !RtoC_pow.
  rewrite re_alt, Cconj_mult_distr, Cpow_conj, alpha_conj.
  unfold Mplus, Mconj, scale; cbn -[nu Cpow pow Re].
  unfold coefa0, coefnu0.
  field_simplify. f_equal. f_equal.
  assert (Im (coefsnu 1%nat 0%nat) = 0).
  { apply coefsnu_real; lia. }
  destruct coefsnu as (x,y). simpl in *. now subst.
Qed.


(** Now, any arbitrary number [n] is a sum of [A 3] numbers by Zeckendorf
    theorem (cf. [GenFib.decomp]). So [diffs n] will be a sum of powers
    of [alpha], [alphabar], [nu]. *)

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

Lemma diff0_decomp_eqn' n :
  diff0 n =
   2*Re (coefa0 * Clistsum (List.map (Cpow alpha) (decomp 3 n))) +
   coefnu0 * Rlistsum (List.map (pow nu) (decomp 3 n)).
Proof.
 rewrite diff0_decomp_eqn.
 induction decomp.
 - cbn -[Re nu]. rewrite Cmult_0_r. simpl. ring.
 - set (f := fun n => _) in *.
   simpl map. rewrite !Rlistsum_cons, Clistsum_cons.
   rewrite Cmult_plus_distr_l, re_plus, !Rmult_plus_distr_l, IHl.
   unfold f at 1. ring.
Qed.

(** With the previous expression of [diff0 n], we will progressively bound it
    by some constant independent from [n]. *)

Lemma diff0_decomp_le n :
 Rabs (diff0 n) <=
  2 * Cmod coefa0 * Rlistsum (List.map (pow (Cmod alpha)) (decomp 3 n))
  + Rabs coefnu0 * Rlistsum (List.map (pow (Rabs nu)) (decomp 3 n)).
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
  2 * Cmod coefa0 / (1 - Cmod alpha^4) + Rabs coefnu0 / (1 - nu^4).
Proof.
 eapply Rle_trans. apply diff0_decomp_le.
 unfold Rdiv.
 apply Rplus_le_compat.
 - apply Rmult_le_compat_l.
   + generalize (Cmod_ge_0 coefa0). lra.
   + apply sum_pow; try lia; try apply decomp_delta.
     split; try apply Cmod_ge_0.
     apply Rlt_pow2_inv; try lra.
     rewrite alphamod2, pow1.
     apply Rmult_lt_reg_r with (-nu); try lra'. field_simplify; lra'.
 - apply Rmult_le_compat_l; try apply Rabs_pos.
   replace (nu^4) with (Rabs nu^4) by (rewrite Rabs_left by lra'; ring).
   apply sum_pow; try lia; try apply decomp_delta.
   rewrite Rabs_left; lra'.
Qed.

(** Experimentally, this first bound is around 2.187.
    Having this finite bound is enough to prove that the frequency
    of letter 0 is [tau^4] and that [f 3 n / n] converges towards tau.
    See Freq.v now for more general results.
    Now, with some more sweat, we prove now a better bound, strictly
    below 2, with nice consequences (not already in Freq.v) :

     - [f 3 n = nat_part (tau*n)+{-1,0,1,2}]
     - [f 3] is quasi-additive:
        [forall n p, -5 <= f 3 (n+p) - f 3 n - f 3 p <= 5]
*)

(* First, the nu part of the bound (easier) *)

Definition max4packnu := 1+nu^4+nu^8+nu^12.

#[local] Instance nu4_approx : Approx 0.44992 (nu^4) 0.452122.
Proof. replace (nu^4) with ((-nu)^4) by ring. approx. Qed.

#[local] Instance nu8_approx : Approx 0.20242 (nu^8) 0.20442.
Proof. replace (nu^8) with ((-nu)^8) by ring. approx. Qed.

#[local] Instance nu12_approx : Approx 0.09107 (nu^12) 0.092421.
Proof. replace (nu^12) with ((-nu)^12) by ring. approx. Qed.

#[local] Instance nu16_approx : Approx 0.04097 (nu^16) 0.04179.
Proof. replace (nu^16) with ((-nu)^16) by ring. approx. Qed.

#[local] Instance max4packnu_approx : Approx 1.743 max4packnu 1.749.
Proof. unfold max4packnu. approx. Qed.

Lemma best_4packnu_0 l :
  Delta 4 (O::l) -> Below l 16 ->
  Rabs (Rlistsum (List.map (pow nu) (O::l))) <= max4packnu.
Proof.
 intros D B.
 inversion D; subst; cbn -[Cpow pow nu]. rewrite !pow_0_r.
 { rewrite Rplus_0_r, Rabs_right by lra. approx. }
 eapply Rle_trans; [apply Rabs_triang|].
 unfold max4packnu. rewrite Rabs_right by lra.
 rewrite !Rplus_assoc. apply Rplus_le_compat_l.
 eapply Rle_trans; [apply Rabs_triang|].
 apply Rplus_le_compat.
 { rewrite <- (Rabs_right (nu^4)) by approx.
   rewrite <- !RPow_abs. apply Rle_pow_le1; try lia.
   rewrite Rabs_left; approx. }
 inversion H2; subst; cbn -[Cpow pow nu]; rewrite ?Rabs_R0; try approx.
 eapply Rle_trans; [apply Rabs_triang|].
 apply Rplus_le_compat.
 { rewrite <- (Rabs_right (nu^8)) by approx.
   rewrite <- !RPow_abs. apply Rle_pow_le1; try lia.
   rewrite Rabs_left; lra'. }
 inversion H4; subst; cbn -[Cpow pow nu]; rewrite ?Rabs_R0; try approx.
 eapply Rle_trans; [apply Rabs_triang|].
 rewrite <- (Rplus_0_r (nu^12)).
 apply Rplus_le_compat.
 { rewrite <- (Rabs_right (nu^12)) by approx.
   rewrite <- !RPow_abs. apply Rle_pow_le1; try lia.
   rewrite Rabs_left; approx. }
 inversion H6; subst. simpl. rewrite Rabs_R0; lra.
 assert (n2 < 16)%nat; try lia. { apply B. simpl. tauto. }
Qed.

Lemma best_4packnu_below l :
  Delta 4 l -> Below l 16 ->
  Rabs (Rlistsum (List.map (pow nu) l)) <= max4packnu.
Proof.
 intros D B.
 destruct l as [|a l].
 - simpl. rewrite Rabs_R0. approx.
 - revert l D B. induction a as [|a IH]; intros l D B.
   + apply best_4packnu_0; auto. unfold Below in *. simpl in *. intuition.
   + replace (S a::l)%list with (List.map S (a :: List.map pred l))%list.
     2:{ simpl. f_equal. rewrite List.map_map.
         rewrite <- (List.map_id l) at 2. apply List.map_ext_in.
         intros b Hb.
         assert (b<>O); try lia.
         { contradict Hb. subst b.
           apply (@Delta_nz' 4 (S a) l); auto; try lia. }}
     rewrite List.map_map, (Rlistsum_pow_factor nu 1), Rabs_mult, pow_1.
     set (l' := List.map pred l).
     eapply Rle_trans. 2:apply (IH l').
     * rewrite <- (Rmult_1_l (Rabs (Rlistsum _))) at 2.
       apply Rmult_le_compat_r; try apply Rabs_pos.
       rewrite Rabs_left; lra'.
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

Lemma best_4packnu l :
  Delta 4 l ->
  Rabs (Rlistsum (List.map (pow nu) l)) <= max4packnu / (1 - nu ^16).
Proof.
 intros D.
 assert (B := listmax_above l).
 setoid_rewrite <- Nat.lt_succ_r in B.
 set (N := S (listmax l)). change (Below l N) in B. clearbody N.
 revert l D B.
 induction N as [N IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases N 16).
 - clear IH. intros l D B.
   eapply Rle_trans. apply best_4packnu_below; auto.
   unfold Below in *. intros y Hy. specialize (B y Hy). lia.
   approx.
 - intros l D B. destruct (cut_lt_ge 16 l) as (l1,l2) eqn:E.
   assert (D' := D).
   assert (E' := cut_app 16 l). rewrite E in E'. rewrite <- E' in D',B |- *.
   rewrite Delta_app_iff in D'. destruct D' as (D1 & D2 & D3).
   rewrite List.map_app, Rlistsum_app.
   eapply Rle_trans. apply Rabs_triang.
   eapply Rle_trans; [eapply Rplus_le_compat_r|].
   + apply best_4packnu_below; auto.
     generalize (cut_fst 16 l). now rewrite E.
   + assert (A : forall n, List.In n l2 -> (16 <= n)%nat).
     { intros n Hn. apply (@cut_snd' 4 16 l); auto. now rewrite E. }
     rewrite (Rlistsum_pow_factor_above nu 16 l2) by trivial.
     set (l2' := List.map (decr 16) l2).
     rewrite Rabs_mult.
     replace (max4packnu / _)
       with (max4packnu + Rabs (nu^16) * (max4packnu / (1 - nu^16))).
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

(** Now the alpha part of the bound *)

Definition max4packa := Cmod (1+alpha^5+alpha^9+alpha^14).

#[local] Instance alphamod16_approx :
 Approx 0.3709 (Cmod alpha ^16) 0.3753.
Proof.
 replace (Cmod alpha^16) with ((Cmod alpha^2)^8) by ring. approx.
Qed.

Lemma alphamod16_lt : 0 < Cmod alpha ^16 < 1.
Proof. approx. Qed.

Lemma re_alpha2 : Re (alpha^2) = re_alpha^2 - im_alpha^2.
Proof.
 simpl. ring.
Qed.

Lemma im_alpha2 : Im (alpha^2) = 2*re_alpha*im_alpha.
Proof.
 simpl. ring.
Qed.

Ltac simpl_alpha := repeat (autorewrite with alpha; ring_simplify).
#[local] Hint Rewrite alpha_is_Croot : alpha.

Lemma alpha5 : (alpha^5 = 1 + alpha + alpha^3)%C.
Proof. rewrite Cpow_S. now simpl_alpha. Qed.
#[local] Hint Rewrite alpha5 : alpha.
Lemma alpha6 : (alpha^6 = 1 + alpha + alpha^2 + alpha^3)%C.
Proof. rewrite Cpow_S. now simpl_alpha. Qed.
#[local] Hint Rewrite alpha6 : alpha.
Lemma alpha7 : (alpha^7 = 1 + alpha + alpha^2 + 2*alpha^3)%C.
Proof. rewrite Cpow_S. now simpl_alpha. Qed.
#[local] Hint Rewrite alpha7 : alpha.
Lemma alpha8 : (alpha^8 = 2 + alpha + alpha^2 + 3*alpha^3)%C.
Proof. rewrite Cpow_S. now simpl_alpha. Qed.
#[local] Hint Rewrite alpha8 : alpha.
Lemma alpha9 : (alpha^9 = 3 + 2*alpha + alpha^2 + 4*alpha^3)%C.
Proof. rewrite Cpow_S. now simpl_alpha. Qed.
#[local] Hint Rewrite alpha9 : alpha.
Lemma alpha10 : (alpha^10 = 4 + 3*alpha + 2*alpha^2 + 5*alpha^3)%C.
Proof. rewrite Cpow_S. now simpl_alpha. Qed.
#[local] Hint Rewrite alpha10 : alpha.
Lemma alpha11 : (alpha^11 = 5 + 4*alpha + 3*alpha^2 + 7*alpha^3)%C.
Proof. rewrite Cpow_S. now simpl_alpha. Qed.
#[local] Hint Rewrite alpha11 : alpha.
Lemma alpha12 : (alpha^12 = 7 + 5*alpha + 4*alpha^2 + 10*alpha^3)%C.
Proof. rewrite Cpow_S. now simpl_alpha. Qed.
#[local] Hint Rewrite alpha12 : alpha.
Lemma alpha13 : (alpha^13 = 10 + 7*alpha + 5*alpha^2 + 14*alpha^3)%C.
Proof. rewrite Cpow_S. now simpl_alpha. Qed.
#[local] Hint Rewrite alpha13 : alpha.
Lemma alpha14 : (alpha^14 = 14 + 10*alpha + 7*alpha^2 + 19*alpha^3)%C.
Proof. rewrite Cpow_S. now simpl_alpha. Qed.
#[local] Hint Rewrite alpha14 : alpha.
Lemma alpha15 : (alpha^15 = 19 + 14*alpha + 10*alpha^2 + 26*alpha^3)%C.
Proof. rewrite Cpow_S. now simpl_alpha. Qed.
#[local] Hint Rewrite alpha15 : alpha.

Module ExactQuadrinom.
(* explicit polynomial syntax [a*alpha^3+b*alpha^2+c*alpha+d]
   even if some coefficients are 0 or 1. Needed for application
   of cmod2_quadri below. *)
Local Open Scope C.
Ltac fix1 t :=
 match t with
 | ?c * alpha + _ => constr:(t)
 | ?c * alpha => constr:(c*alpha+0)
 | alpha + ?t => constr:(1*alpha+t)
 | alpha => constr:(1*alpha+0)
 | _ => constr:(0*alpha+t)
 end.
Ltac fix2 t :=
 match t with
 | ?c * alpha^2 + ?t => let t' := fix1 t in constr:(c*alpha^2+t')
 | ?c * alpha^2 => fix2 constr:(t+0)
 | alpha^2 + ?t => fix2 constr:(1*alpha^2+t)
 | alpha^2 => fix2 constr:(1*alpha^2+0)
 | _ => fix2 constr:(0*alpha^2+t)
 end.
Ltac fix3 t :=
 match t with
 | ?c * alpha^3 + ?t => let t' := fix2 t in constr:(c*alpha^3+t')
 | ?c * alpha^2 => fix3 constr:(t+0)
 | alpha^3 + ?t => fix3 constr:(1*alpha^3+t)
 | alpha^3 => fix3 constr:(1*alpha^3+0)
 | _ => fix3 constr:(0*alpha^3+t)
 end.
End ExactQuadrinom.

Ltac calc_alpha :=
  let c := fresh in
  let H := fresh in
  remember (Cplus _ _) as c eqn:H; (* ad-hoc but enough here ! *)
  repeat (autorewrite with alpha in H; ring_simplify in H);
  (* fixing quadrinom *)
  rewrite <- ?Cplus_assoc in H;
  match type of H with _ = ?t =>
    let t' := ExactQuadrinom.fix3 t in replace t with t' in H by ring
  end;
  rewrite ?Cplus_assoc in H;
  rewrite H; clear c H.

Lemma re_quadri (a b c d : R) :
 Re (d*alpha^3+c*alpha^2+b*alpha+a) =
 a + b*re_alpha + c*re_alpha^2 + d*re_alpha^3 - (c+3*d*re_alpha)*im_alpha^2.
Proof.
 unfold alpha. cbn. ring.
Qed.

Lemma im_quadri (a b c d : R) :
 Im (d*alpha^3+c*alpha^2+b*alpha+a) =
 re_alpha*im_alpha*(2*c+3*d*re_alpha) + im_alpha*b - d*im_alpha^3.
Proof.
 unfold alpha. cbn. ring.
Qed.

Lemma cmod2_quadri (a b c d : R) :
 Cmod (d*alpha^3+c*alpha^2+b*alpha+a)^2 =
 (a + b*re_alpha + c*re_alpha^2 + d*re_alpha^3 - (c+3*d*re_alpha)*im_alpha^2)^2
 + (re_alpha*im_alpha*(2*c+3*d*re_alpha) + im_alpha*b - d*im_alpha^3)^2.
Proof.
 now rewrite Cmod2_alt, re_quadri, im_quadri.
Qed.

(* TODO: Mieux que ce cmod2_quadri ? *)

#[local] Instance im_alpha_2_approx :
  Approx 0.8362620801 (im_alpha^2) 0.8362620803.
Proof. rewrite im_alpha_2. approx. Qed.

#[local] Instance im_alpha_approx :
  Approx 0.9144736628 im_alpha 0.9144736630 |10.
Proof.
 apply pow2_approx_inv. approx. qle. generalize im_alpha_pos; lra. qle.
Qed.

#[local] Instance max4packa2_approx :
 Approx 6.7073103 (max4packa^2) 6.7073105.
Proof.
 unfold max4packa. calc_alpha. rewrite cmod2_quadri. approx.
Qed.

Lemma best_4packa_0 l :
  Delta 4 (O::l) -> Below l 16 ->
  Cmod (Clistsum (List.map (Cpow alpha) (O::l))) <= max4packa.
Proof.
 intros D B.
 apply Rle_pow2_inv; [apply Cmod_ge_0| ].
 assert (H : Delta 4 (O::l) /\ Below (O::l) 16).
 { split; trivial. intros x [<-|Hx]. lia. now apply B. }
 rewrite enum_delta_below_ok0 in H.
 compute in H;
 repeat destruct H as [<-|H]; try destruct H as [ ];
  cbn -[Cpow pow]; rewrite ?Cpow_0_r, ?Cplus_0_r, ?Cplus_assoc;
  try apply Rle_refl; (* for max4packa itself *)
  try (calc_alpha; rewrite cmod2_quadri; approx). (* slow... *)
 rewrite Cmod_1, pow1. approx.
Qed.

Lemma best_4packa_below l :
  Delta 4 l -> Below l 16 ->
  Cmod (Clistsum (List.map (Cpow alpha) l)) <= max4packa.
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
     rewrite List.map_map, (Clistsum_pow_factor alpha 1), Cmod_mult, Cpow_1_r.
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
  Cmod (Clistsum (List.map (Cpow alpha) l)) <=
   max4packa / (1 - Cmod alpha ^16).
Proof.
 intros D.
 assert (B := listmax_above l).
 setoid_rewrite <- Nat.lt_succ_r in B.
 set (N := S (listmax l)). change (Below l N) in B. clearbody N.
 revert l D B.
 induction N as [N IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases N 16).
 - clear IH. intros l D B.
   eapply Rle_trans. apply best_4packa_below; auto.
   unfold Below in *. intros y Hy. specialize (B y Hy). lia.
   rewrite <- (Rmult_1_r max4packa) at 1. unfold Rdiv.
   apply Rmult_le_compat_l; try apply Cmod_ge_0.
   rewrite <- (Rmult_1_l (/ _)).
   assert (P := Cmod_ge_0 alpha).
   apply Rcomplements.Rle_div_r; generalize alphamod16_lt; lra.
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
     rewrite (Clistsum_pow_factor_above alpha 16 l2) by trivial.
     set (l2' := List.map (decr 16) l2).
     rewrite Cmod_mult.
     replace (max4packa / _)
       with (max4packa + Cmod (alpha^16) * (max4packa / (1 - Cmod alpha ^16))).
     * apply Rplus_le_compat_l.
       apply Rmult_le_compat_l; try apply Cmod_ge_0.
       apply (IH (N-16)%nat); try lia.
       { apply Delta_map_decr; auto. }
       { unfold l2'. intros x Hx. rewrite List.in_map_iff in Hx.
         destruct Hx as (y & <- & Hy).
         specialize (A y Hy).
         assert (y < N)%nat by (apply B; rewrite List.in_app_iff; now right).
         unfold decr. lia. }
     * rewrite Cmod_pow. field. generalize alphamod16_lt; lra.
Qed.

(** And finally: *)

Lemma diff0_better_bound n :
 Rabs (diff0 n) <=
  2 * Cmod coefa0 * max4packa / (1 - Cmod alpha ^16) +
  Rabs coefnu0 * max4packnu / (1 - nu ^16).
Proof.
 rewrite diff0_decomp_eqn'.
 eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat.
 - rewrite Rabs_mult. rewrite Rabs_right by lra.
   unfold Rdiv. rewrite !Rmult_assoc. apply Rmult_le_compat_l; try lra.
   eapply Rle_trans; [apply re_le_Cmod|].
   rewrite Cmod_mult. apply Rmult_le_compat_l; try apply Cmod_ge_0.
   apply best_4packa, decomp_delta.
 - rewrite Rabs_mult.
   unfold Rdiv. rewrite !Rmult_assoc. apply Rmult_le_compat_l.
   apply Rabs_pos. apply best_4packnu, decomp_delta.
Qed.

(** And finally, we obtain that diff0 is always strictly less than 2.
    (experimentally the new bound is below 1.998) *)

(* TODO
#[local] Instance : Approx 0 (Cmod coefa0) 0.
Proof.
 unfold coefa0, coefsa. unfold scale. cbn -[nu].
 unfold coefa_detU. rewrite detU_alt. unfold UV0a.
 field_simplify.

#[local] Instance : Approx 0 (Rabs coefnu0) 0.
Proof.
Admitted.
*)

Lemma diff0_lt_2 n : Rabs (diff0 n) < 2.
Proof.
 eapply Rle_lt_trans. apply diff0_better_bound.
(*  approx. *)
Admitted.
(*
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
*)

(* Print Assumptions diff0_lt_2. *)

(* Consequences for f3 : *)

Lemma f3_alt n : INR (f 3 n) = tau*n + diff0 n.
Proof.
 rewrite diff0_alt; lra.
Qed.

Lemma f3_close_tau_n (n:nat) : -2 < tau*n - f 3 n < 2.
Proof.
 rewrite f3_alt.
 assert (H := diff0_lt_2 n).
 rewrite Rcomplements.Rabs_lt_between in H. lra.
Qed.

Lemma f3_close_natpart (n:nat) :
 (nat_part (tau*n) - 1 <= f 3 n <= nat_part (tau*n) + 2)%nat.
Proof.
assert (LT := f3_close_tau_n n).
assert (LE : 0 <= tau*n).
{ apply Rmult_le_pos; try lra'. apply pos_INR. }
split.
- assert (H : 0 <= tau*n < INR(2 + f 3 n)).
  { rewrite plus_INR. simpl. lra. }
  apply nat_part_lt in H. lia.
- assert (INR(f 3 n - 2) <= tau*n).
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
   generalize (f3_close_tau_n (p+n)) (f3_close_tau_n p) (f3_close_tau_n n).
   rewrite plus_INR. lra.
 - rewrite <- Nat.lt_succ_r.
   apply INR_lt. rewrite S_INR, !plus_INR. simpl INR.
   generalize (f3_close_tau_n (p+n)) (f3_close_tau_n p) (f3_close_tau_n n).
   rewrite plus_INR. lra.
Qed.

(* Print Assumptions h_quasiadd. *)

(** To finish someday, less interesting : frequencies for the other letters. *)
