From Coq Require Import Lia Reals Lra Morphisms QArith.
Close Scope Q. (* Issue with QArith. *)
From Coquelicot Require Import Hierarchy Continuity Derive AutoDerive
 RInt RInt_analysis Series PSeries.
From Hofstadter.HalfQuantum Require Import Complex Polynomial.
Require Import MoreTac MoreList MoreReals MoreLim MoreSum MoreComplex.
Require Import MorePoly MoreIntegral ThePoly GenFib Mu.
Require Phi F3 F4 F5.
Local Open Scope R.
Local Open Scope C.
Local Open Scope poly_scope.
Local Coercion INR : nat >-> R.
Local Coercion IZR : Z >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * Definition of Pisot number and Siegel Theorem *)

(** Rational numbers seen as subsets of R, C. Polynomials in Q[x] *)

Definition Rational (x : R) := exists q:Q, x = Q2R q.
Definition CRational (z : C) := exists q:Q, z = RtoC (Q2R q).
Definition RatPoly (p : Polynomial) := Forall CRational p.

Definition Qpoly := map (RtoC∘Q2R).

Lemma Rational_RtoC (r:R) : Rational r -> CRational (RtoC r).
Proof.
 intros (z & ->). now exists z.
Qed.

Lemma Rational_Q (q:Q) : Rational (Q2R q).
Proof.
 now eexists.
Qed.

Lemma Rational_Z (n:Z) : Rational n.
Proof.
 exists (inject_Z n). now rewrite Q2R_IZR.
Qed.

Lemma Rational_nat (n:nat) : Rational n.
Proof.
 rewrite INR_IZR_INZ. apply Rational_Z.
Qed.

Lemma CRational_Q (q:Q) : CRational (Q2R q).
Proof.
 apply Rational_RtoC, Rational_Q.
Qed.

Lemma CRational_Z (n:Z) : CRational n.
Proof.
 apply Rational_RtoC, Rational_Z.
Qed.

Lemma CRational_nat (n:nat) : CRational n.
Proof.
 apply Rational_RtoC, Rational_nat.
Qed.

Lemma RatPoly_alt p :
  RatPoly p <-> exists (q : list Q), p = Qpoly q.
Proof.
 induction p; split.
 - now exists [].
 - constructor.
 - inversion_clear 1. apply IHp in H1. destruct H1 as (q & ->).
   destruct H0 as (n & ->). now exists (n::q).
 - intros ([|n q] & E); try easy. injection E as -> ->.
   constructor. now exists n. rewrite IHp. now exists q.
Qed.

Lemma RatPoly_prune p :  RatPoly (prune p) <-> RatPoly p.
Proof.
 induction p as [|a p]; simpl; try easy.
 destruct Ceq_dec.
 - subst a. rewrite IHp.
   split. constructor; trivial. apply CRational_Z. now inversion_clear 1.
 - split; inversion_clear 1; constructor; trivial.
Qed.

Lemma RatPoly_compactify p : RatPoly p <-> RatPoly (compactify p).
Proof.
 unfold compactify, RatPoly.
 split; intros H. now apply Forall_rev, RatPoly_prune, Forall_rev.
 apply Forall_rev in H. rewrite rev_involutive, RatPoly_prune in H.
 apply Forall_rev in H. now rewrite rev_involutive in H.
Qed.

Global Instance RatPoly_Peq : Proper (Peq ==> iff) RatPoly.
Proof.
 intros p q E. apply Peq_compactify_eq in E.
 now rewrite (RatPoly_compactify p), (RatPoly_compactify q), E.
Qed.

Lemma RatPoly_alt' p :
  RatPoly p <-> exists (q : list Q), Peq p (Qpoly q).
Proof.
 induction p; split.
 - now exists [].
 - constructor.
 - inversion_clear 1. apply IHp in H1. destruct H1 as (q & Eq).
   destruct H0 as (n & ->). exists (n::q). simpl. now rewrite <- Eq.
 - intros ([|n q] & E); try easy; simpl in E.
   + destruct (Peq_nil_reduce _ _ E) as (->,->).
     rewrite RatPoly_alt. exists [0%Q]. simpl. unfold "∘". f_equal. lca.
   + constructor.
     * apply Peq_head_eq in E. now exists n.
     * apply IHp. exists q. now apply Peq_tail_Peq in E.
Qed.

Lemma RatPoly_coef p n : RatPoly p -> CRational (coef n p).
Proof.
 rewrite RatPoly_alt. intros (q & ->). unfold coef, Qpoly.
 replace 0%C with ((RtoC∘Q2R) 0%Q) by (unfold "∘"; f_equal; lra).
 rewrite map_nth. now eexists.
Qed.

Lemma RatPoly_topcoef p : RatPoly p -> CRational (topcoef p).
Proof.
 rewrite topcoef_alt. apply RatPoly_coef.
Qed.

Lemma Rational_plus a b : Rational a -> Rational b -> Rational (a+b).
Proof.
 intros (qa, ->) (qb, ->). exists (qa+qb)%Q. now rewrite Qreals.Q2R_plus.
Qed.

Lemma Rational_mult a b : Rational a -> Rational b -> Rational (a*b).
Proof.
 intros (qa, ->) (qb, ->). exists (qa*qb)%Q. now rewrite Qreals.Q2R_mult.
Qed.

Lemma Rational_inv a : Rational a -> Rational (/a).
Proof.
 destruct (Req_dec a 0) as [->|N].
 - now rewrite Rinv_0.
 - intros (qa, ->). exists (Qinv qa). rewrite Qreals.Q2R_inv; trivial.
   contradict N. rewrite N. lra.
Qed.

Lemma Rational_div a b : Rational a -> Rational b -> Rational (a/b).
Proof.
 intros. apply Rational_mult; trivial. now apply Rational_inv.
Qed.

Lemma CRational_plus a b : CRational a -> CRational b -> CRational (a+b).
Proof.
 intros (qa, ->) (qb, ->). exists (qa+qb)%Q.
 now rewrite <- RtoC_plus, Qreals.Q2R_plus.
Qed.

Lemma CRational_mult a b : CRational a -> CRational b -> CRational (a*b).
Proof.
 intros (qa, ->) (qb, ->). exists (qa*qb)%Q.
 now rewrite <- RtoC_mult, Qreals.Q2R_mult.
Qed.

Lemma CRational_inv a : CRational a -> CRational (/a).
Proof.
 destruct (Ceq_dec a 0) as [E|N]; subst.
 - now rewrite Cinv_0.
 - intros (qa, ->). exists (Qinv qa).
   rewrite <- RtoC_inv, Qreals.Q2R_inv; trivial.
   contradict N. rewrite N. f_equal. lra.
Qed.

Lemma CRational_div a b : CRational a -> CRational b -> CRational (a/b).
Proof.
 intros. apply CRational_mult; trivial. now apply CRational_inv.
Qed.

Lemma RatPoly_plus p q : RatPoly p -> RatPoly q -> RatPoly (p +, q).
Proof.
 revert q. induction p; simpl; trivial.
 intros q H1 H2. destruct q; simpl; trivial.
 inversion_clear H1. inversion_clear H2. constructor; try apply IHp; trivial.
 now apply CRational_plus.
Qed.

Lemma RatPoly_mult p q : RatPoly p -> RatPoly q -> RatPoly (p *, q).
Proof.
 revert q. induction p; simpl; trivial.
 intros q H1 H2. apply RatPoly_plus.
 - inversion_clear H1. apply Forall_map.
   rewrite Forall_forall. intros x IN. apply CRational_mult; trivial.
   red in H2. rewrite Forall_forall in H2. now apply H2.
 - constructor. apply CRational_Z.
   apply IHp; trivial. now inversion_clear H1.
Qed.

Lemma RatPoly_opp p : RatPoly p -> RatPoly (-, p).
Proof.
 intros Hp. apply RatPoly_mult; trivial. constructor; [|constructor].
 rewrite <- RtoC_opp, <- opp_IZR. apply CRational_Z.
Qed.

Lemma RatPoly_monom z k : CRational z -> RatPoly (monom z k).
Proof.
 intros. unfold monom. apply Forall_app. split.
 - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst.
   apply CRational_Z.
 - now constructor.
Qed.

(** Integers seen as subsets of R, C. Polynomials in Z[x] *)

Definition Integer (x : R) := frac_part x = 0%R.
Definition CInteger (z : C) := Integer (Re z) /\ Im z = 0%R.
Definition IntPoly (p : Polynomial) := Forall CInteger p.

Definition Zpoly := map (RtoC∘IZR).

Lemma Integer_alt (x : R) : Integer x <-> exists n:Z, x = n.
Proof.
 split.
 - apply fp_nat.
 - intros (n, ->). red. rewrite <- (Rplus_0_l (IZR n)).
   now rewrite frac_part_addZ, fp_R0.
Qed.

Lemma CInteger_alt (z : C) : CInteger z <-> exists n:Z, z = n.
Proof.
 unfold CInteger. rewrite Integer_alt.
 split.
 - intros ((n,E1),E2). exists n. destruct z; simpl in *; now subst.
 - intros (n,->). simpl; split; trivial. now exists n.
Qed.

Lemma Integer_Z (n:Z) : Integer n.
Proof.
 rewrite Integer_alt. now exists n.
Qed.

Lemma CInteger_Z (n:Z) : CInteger n.
Proof.
 rewrite CInteger_alt. now exists n.
Qed.

Lemma Integer_nat (n:nat) : Integer n.
Proof.
 rewrite INR_IZR_INZ. apply Integer_Z.
Qed.

Lemma CInteger_nat (n:nat) : CInteger n.
Proof.
 rewrite INR_IZR_INZ. apply CInteger_Z.
Qed.

Lemma IntPoly_alt p :
  IntPoly p <-> exists (q : list Z), p = Zpoly q.
Proof.
 induction p; split.
 - now exists [].
 - constructor.
 - inversion_clear 1. apply IHp in H1. destruct H1 as (q & ->).
   rewrite CInteger_alt in H0. destruct H0 as (n & ->).
   now exists (n::q).
 - intros ([|n q] & E); try easy. injection E as -> ->.
   constructor. apply CInteger_alt. now exists n.
   rewrite IHp. now exists q.
Qed.

Lemma IntPoly_prune p :  IntPoly (prune p) <-> IntPoly p.
Proof.
 induction p as [|a p]; simpl; try easy.
 destruct Ceq_dec.
 - subst a. rewrite IHp.
   split. constructor; trivial. apply CInteger_Z. now inversion_clear 1.
 - split; inversion_clear 1; constructor; trivial.
Qed.

Lemma IntPoly_compactify p : IntPoly p <-> IntPoly (compactify p).
Proof.
 unfold compactify, IntPoly.
 split; intros H. now apply Forall_rev, IntPoly_prune, Forall_rev.
 apply Forall_rev in H. rewrite rev_involutive, IntPoly_prune in H.
 apply Forall_rev in H. now rewrite rev_involutive in H.
Qed.

Global Instance IntPoly_Peq : Proper (Peq ==> iff) IntPoly.
Proof.
 intros p q E. apply Peq_compactify_eq in E.
 now rewrite (IntPoly_compactify p), (IntPoly_compactify q), E.
Qed.

Lemma IntPoly_alt' p :
  IntPoly p <-> exists (l : list Z), Peq p (Zpoly l).
Proof.
 induction p; split.
 - now exists [].
 - constructor.
 - inversion_clear 1. apply IHp in H1. destruct H1 as (l & Eq).
   rewrite CInteger_alt in H0. destruct H0 as (n & ->).
   exists (n::l). simpl. now rewrite <- Eq.
 - intros ([|n q] & E); try easy; simpl in E.
   + destruct (Peq_nil_reduce _ _ E) as (->,->).
     rewrite IntPoly_alt. now exists [0%Z].
   + constructor.
     * apply Peq_head_eq in E. apply CInteger_alt. now exists n.
     * apply IHp. exists q. now apply Peq_tail_Peq in E.
Qed.

Lemma coef_Zpoly n p : coef n (Zpoly p) = nth n p Z0.
Proof.
 unfold coef, Zpoly. change 0%C with ((RtoC∘IZR) Z0).
 now rewrite map_nth.
Qed.

Lemma IntPoly_coef p n : IntPoly p -> CInteger (coef n p).
Proof.
 rewrite IntPoly_alt. intros (q & ->). rewrite coef_Zpoly.
 apply CInteger_alt. now eexists.
Qed.

Lemma IntPoly_topcoef p : IntPoly p -> CInteger (topcoef p).
Proof.
 rewrite topcoef_alt. apply IntPoly_coef.
Qed.

Lemma Integer_plus a b : Integer a -> Integer b -> Integer (a+b).
Proof.
 rewrite !Integer_alt. intros (za, ->) (zb, ->). exists (za+zb)%Z.
 now rewrite plus_IZR.
Qed.

Lemma Integer_mult a b : Integer a -> Integer b -> Integer (a*b).
Proof.
 rewrite !Integer_alt. intros (za, ->) (zb, ->). exists (za*zb)%Z.
 now rewrite mult_IZR.
Qed.

Lemma CInteger_plus a b : CInteger a -> CInteger b -> CInteger (a+b).
Proof.
 rewrite !CInteger_alt. intros (za, ->) (zb, ->). exists (za+zb)%Z.
 now rewrite <- RtoC_plus, plus_IZR.
Qed.

Lemma CInteger_mult a b : CInteger a -> CInteger b -> CInteger (a*b).
Proof.
 rewrite !CInteger_alt. intros (za, ->) (zb, ->). exists (za*zb)%Z.
 now rewrite <- RtoC_mult, mult_IZR.
Qed.

Lemma IntPoly_plus p q : IntPoly p -> IntPoly q -> IntPoly (p +, q).
Proof.
 revert q. induction p; simpl; trivial.
 intros q H1 H2. destruct q; simpl; trivial.
 inversion_clear H1. inversion_clear H2. constructor; try apply IHp; trivial.
 now apply CInteger_plus.
Qed.

Lemma IntPoly_mult p q : IntPoly p -> IntPoly q -> IntPoly (p *, q).
Proof.
 revert q. induction p; simpl; trivial.
 intros q H1 H2. apply IntPoly_plus.
 - inversion_clear H1. apply Forall_map.
   rewrite Forall_forall. intros x IN. apply CInteger_mult; trivial.
   red in H2. rewrite Forall_forall in H2. now apply H2.
 - constructor. rewrite CInteger_alt. now exists Z0.
   apply IHp; trivial. now inversion_clear H1.
Qed.

Lemma IntPoly_opp p : IntPoly p -> IntPoly (-, p).
Proof.
 intros Hp. apply IntPoly_mult; trivial. constructor; [|constructor].
 rewrite <- RtoC_opp, <- opp_IZR. apply CInteger_Z.
Qed.

Lemma IntPoly_monom z k : CInteger z -> IntPoly (monom z k).
Proof.
 intros. unfold monom. apply Forall_app. split.
 - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst.
   apply CInteger_Z.
 - now constructor.
Qed.

(** Definition of Pisot numbers *)

Definition Pisot (x:R) :=
  1<x /\
  exists l : list C,
    IntPoly (linfactors (RtoC x :: l)) /\
    Forall (fun r => 0 < Cmod r < 1) l.

Definition PisotConjugates (x:R)(l : list C) :=
  1<x /\
  IntPoly (linfactors (RtoC x :: l)) /\
  Forall (fun r => 0 < Cmod r < 1) l.

Lemma Pisot_alt x : Pisot x <-> exists l, PisotConjugates x l.
Proof.
 split.
 - intros (Hx & l & H1 & H2). now exists l.
 - intros (l & Hx & H1 & H2). split; trivial. now exists l.
Qed.

(** First examples *)

Lemma Pisot_nat_ge_2 (n:nat) : (2<=n)%nat -> Pisot n.
Proof.
 split.
 - apply le_INR in H. simpl in H. lra.
 - exists []; simpl; split; [|constructor].
   apply IntPoly_alt. exists [-Z.of_nat n;1]%Z.
   simpl. unfold "∘"; repeat f_equal; try ring.
   rewrite opp_IZR, <- INR_IZR_INZ, RtoC_opp. ring.
Qed.

Lemma Pisot_mu2 : Pisot (mu 2). (* Golden ratio 1.618.. *)
Proof.
 split.
 - apply (mu_itvl 2).
 - exists [-tau 2]; split.
   + simpl. rewrite !Cmult_1_l, !Cmult_1_r, !Cplus_0_r.
     rewrite !Copp_involutive, <- !Copp_mult_distr_r.
     unfold tau at 1. rewrite RtoC_inv, Cinv_l.
     2:{ intros [= E]. generalize (mu_itvl 2); lra. }
     rewrite <- !RtoC_opp, <- opp_IZR. simpl.
     rewrite <- RtoC_plus. replace (tau 2 + - mu 2)%R with (-1)%R.
     2:{ rewrite tau_2, mu_2. field. }
     apply IntPoly_alt. now exists [-1;-1;1]%Z.
   + repeat constructor; rewrite Cmod_opp, Cmod_R, Rabs_pos_eq;
      generalize (tau_itvl 2); lra.
Qed.

Lemma Pisot_mu3 : Pisot (mu 3). (* 1.465571... *)
Proof.
 split.
 - apply (mu_itvl 3).
 - exists (tl F3.roots). split.
   + change (RtoC (mu 3) :: tl F3.roots) with F3.roots.
     rewrite F3.linfactors_roots.
     unfold ThePoly. simpl. rewrite !Cplus_0_l.
     apply IntPoly_alt. now exists [-1;0;-1;1]%Z.
   + unfold F3.roots. simpl.
     repeat constructor;
     change F3.αbar with (Cconj F3.α); rewrite ?Cmod_conj;
     generalize F3.αmod_approx; unfold Approx.Approx; lra.
Qed.

Lemma Pisot_mu4 : Pisot (mu 4). (* 1.380277... *)
Proof.
 split.
 - apply (mu_itvl 4).
 - exists (tl F4.roots). split.
   + change (RtoC (mu 4) :: tl F4.roots) with F4.roots.
     destruct F4.roots_sorted as (<-,_).
     unfold ThePoly. simpl. rewrite !Cplus_0_l.
     apply IntPoly_alt. now exists [-1;0;0;-1;1]%Z.
   + unfold F4.roots. simpl.
     repeat constructor;
     change F4.αbar with (Cconj F4.α);
     rewrite ?Cmod_conj, ?Cmod_R, ?Rabs_left;
     generalize F4.αmod_approx, F4.ν_approx; unfold Approx.Approx; lra.
Qed.

(** (mu 5) = 1.3247179... is the Plastic Ratio, root of X^3-X-1.
    NB: ThePoly 5 has secondary roots of modulus 1, but can be factorized
    as (X^3-X-1)(X^2-X+1) *)

Lemma Pisot_mu5 : Pisot (mu 5).
Proof.
 split.
 - apply (mu_itvl 5).
 - exists [F5.α; F5.αbar]. split.
   + change (mu 5) with F5.μ. rewrite <- F5.factor2.
     apply IntPoly_alt. now exists [-1;-1;0;1]%Z.
   + assert (0 < Cmod F5.α < 1).
     { split; apply Rsqr_incrst_0; try lra; try apply Cmod_ge_0;
       rewrite ?Rsqr_1, ?Rsqr_0, Rsqr_pow2, F5.αmod2;
       change F5.τ with (tau 5); generalize (tau_itvl 5); lra. }
     repeat constructor; trivial;
     change F5.αbar with (Cconj F5.α); now rewrite ?Cmod_conj.
Qed.

(** With our formulation, we retrieve the irreducibilty and uniqueness
    of the polynomial associated to a Pisot number *)

Definition PisotPoly (x:R)(p : Polynomial) :=
  exists l, PisotConjugates x l /\ Peq p (linfactors (RtoC x :: l)).

Lemma Pisot_alt' x : Pisot x <-> exists p, PisotPoly x p.
Proof.
 rewrite Pisot_alt. split.
 - intros (l & Hl). exists (linfactors (RtoC x :: l)). now exists l.
 - intros (p & (l & Hl & Hl')). now exists l.
Qed.

Definition Zreducible (p:Polynomial) :=
  exists q r,
    Peq p (Pmult q r) /\ IntPoly q /\ IntPoly r /\
    (0 < degree q < degree p)%nat.

Lemma PisotIntPoly x p : PisotPoly x p -> IntPoly p.
Proof.
 intros (l & H1 & H2). rewrite H2. apply H1.
Qed.

Lemma PisotPolyRoot x p : PisotPoly x p -> Root x p.
Proof.
 intros (l & H1 & H2). rewrite H2. rewrite <- linfactors_roots. now left.
Qed.

Lemma All_roots' (p : Polynomial) :
  exists l : list C, p ≅ [topcoef p] *, linfactors l.
Proof.
 destruct (Ceq_dec (topcoef p) 0) as [E|N].
 - exists []. simpl. rewrite E. rewrite Cmult_0_l, Cplus_0_l.
   rewrite C0_Peq_nil. now apply topcoef_0_iff.
 - destruct (All_roots ([/topcoef p]*,p)) as (l & E).
   { red. rewrite topcoef_mult, topcoef_singl. now field. }
   exists l. rewrite <- E. rewrite <- Pmult_assoc.
   replace ([_]*,[_]) with [1]. now rewrite ?Pmult_1_l.
   simpl. f_equal. now field.
Qed.

Definition Rlt01 r :=
  if Rle_lt_dec r 0 then false else if Rle_lt_dec 1 r then false else true.

Lemma Rlt01_spec r : Rlt01 r = true <-> 0 < r < 1.
Proof.
 unfold Rlt01. repeat destruct Rle_lt_dec; split; lra || easy.
Qed.

Lemma Rlt01_Cmod c : negb (Rlt01 (Cmod c)) = true <-> c = 0 \/ 1 <= Cmod c.
Proof.
 rewrite negb_true_iff, <- not_true_iff_false, Rlt01_spec.
 generalize (Cmod_ge_0 c). rewrite <- Cmod_eq_0_iff. lra.
Qed.

Lemma existsb_negb_forallb {A} f (l:list A) :
  existsb f l = negb (forallb (negb∘f) l).
Proof.
 induction l; simpl; trivial. rewrite IHl.
 unfold "∘". now destruct (f a), forallb.
Qed.

Lemma Peval_0 p : Peval p 0 = coef 0 p.
Proof.
 destruct p; try easy.
 rewrite cons_eval. rewrite Cmult_0_l, Cplus_0_r. now unfold coef.
Qed.

Lemma IntPoly_null_or_large_root (p : Polynomial) :
 IntPoly p -> monic p -> (0 < degree p)%nat ->
 exists r, Root r p /\ (r = 0 \/ 1 <= Cmod r).
Proof.
 intros H1 H2 H3.
 destruct (All_roots p H2) as (l & E).
 rewrite E, linfactors_degree in H3.
 setoid_rewrite <- Rlt01_Cmod.
 setoid_rewrite E. setoid_rewrite <- linfactors_roots.
 rewrite <- existsb_exists, existsb_negb_forallb.
 rewrite negb_true_iff, <- not_true_iff_false.
 unfold "∘". rewrite forallb_forall.
 setoid_rewrite negb_involutive. setoid_rewrite Rlt01_spec.
 intros F.
 set (m := Cmod (Peval p 0)).
 assert (Hm : Integer m).
 { unfold m. rewrite Peval_0. destruct p.
   - unfold coef; simpl. rewrite Cmod_0. apply Integer_Z.
   - unfold coef; simpl. inversion_clear H1. rewrite CInteger_alt in H.
     destruct H as (z,->). rewrite Cmod_R, <- abs_IZR. apply Integer_Z. }
 assert (Hm' : 0 < m < 1).
 { unfold m. rewrite E, Peval_linfactors. revert H3 F. clear.
   induction l; simpl; try easy.
   intros _ H.
   unfold Cminus at 1 3. rewrite Cplus_0_l, Cmod_mult, Cmod_opp.
   assert (aux : forall x y, 0<x<1 -> y=1%R\/0<y<1 -> 0<x*y<1) by (intros; nra).
   apply aux. apply H; now left.
   destruct l as [|b l].
   - left. simpl. apply Cmod_1.
   - right. apply IHl. simpl; try lia. intros x Hx. apply H; now right. }
 rewrite Integer_alt in Hm. destruct Hm as (z & Hz). rewrite Hz in Hm'.
 destruct Hm' as (Hz1,Hz2). apply lt_IZR in Hz1, Hz2. lia.
Qed.

Lemma PisotPolyIrred x p : PisotPoly x p -> ~Zreducible p.
Proof.
 intros Hp (p1 & p2 & E & H1 & H2 & D).
 assert (T : topcoef p1 * topcoef p2 = 1).
 { assert (E' := topcoef_mult p1 p2).
   rewrite <- E in E'.
   destruct Hp as (l & Hl1 & Hl2). rewrite Hl2 in E'.
   now rewrite linfactors_monic in E'. }
 assert (T1 : topcoef p1 = 1 \/ topcoef p1 = -1).
 { apply IntPoly_topcoef, CInteger_alt in H1, H2.
   destruct H1 as (n & Hn), H2 as (m, Hm). rewrite Hn, Hm in *.
   rewrite <- RtoC_mult, <- mult_IZR in T.
   apply RtoC_inj, eq_IZR in T.
   apply Z.mul_eq_1 in T. destruct T as [-> | ->]. now left. now right. }
 destruct (Ceq_dec (Peval p1 x) 0) as [Hx|Hx].
 - assert (Hx' : ~Root x p2).
   { intros Hx'.
     assert (Root x (Pdiff p)).
     { rewrite E, Pdiff_mult. red.
       rewrite Pplus_eval, !Pmult_eval, Hx, Hx'. ring. }
     destruct Hp as (l & Hl & Hl').
     revert H. unfold Root. rewrite Hl'. simpl. rewrite Pdiff_mult; simpl.
     rewrite Pplus_eval, !Pmult_eval.
     replace (Peval [_;_] x) with 0 by (unfold Peval; simpl; ring).
     replace (Peval [_;_] x) with 1 by (unfold Peval; simpl; ring).
     rewrite Cmult_0_r, Cplus_0_l, Cmult_1_r.
     change (~Root x (linfactors l)). rewrite <- linfactors_roots.
     destruct Hl as (Hx1 & Hl1 & Hl2). intros IN.
     rewrite Forall_forall in Hl2. specialize (Hl2 x IN).
     rewrite Cmod_R, Rabs_pos_eq in Hl2; lra. }
   set (p2' := [topcoef p1] *, p2).
   destruct (IntPoly_null_or_large_root p2') as (r & Hr & Hr').
   { apply IntPoly_mult; trivial. constructor; [|constructor].
     rewrite CInteger_alt.
     destruct T1 as [-> | ->]; [now exists 1%Z|now exists (-1)%Z]. }
   { red. unfold p2'. now rewrite topcoef_mult, topcoef_singl. }
   { unfold p2'. rewrite Pscale_degree.
     2:{ destruct T1 as [-> | ->]; injection; lra. }
     rewrite E in D. rewrite Pmult_degree in D; try lia.
     - change (~Peq p1 []). intros E1. rewrite <- topcoef_0_iff in E1.
       rewrite E1 in T. rewrite Cmult_0_l in T. injection T; lra.
     - change (~Peq p2 []). intros E2. rewrite <- topcoef_0_iff in E2.
       rewrite E2 in T. rewrite Cmult_0_r in T. injection T; lra. }
   destruct Hp as (l & (Hx1 & _ & Hl1) & Hl2).
   assert (Hr2 : Root r p2).
   { unfold p2' in Hr. red in Hr.
     rewrite Pmult_eval in Hr. apply Cmult_integral in Hr.
     rewrite Pconst_eval in Hr. destruct Hr as [Hr | Hr]; try easy.
     rewrite Hr in T. rewrite Cmult_0_l in T. injection T; lra. }
   assert (IN : In r (RtoC x :: l)).
   { apply linfactors_roots. rewrite <- Hl2, E. red.
     rewrite Pmult_eval. rewrite Hr2. lca. }
   simpl in IN. destruct IN as [IN | IN]; [ now rewrite IN in Hx'|].
   assert (Hr3 : 0 < Cmod r < 1).
   { rewrite Forall_forall in Hl1. now apply Hl1. }
   rewrite <- Cmod_eq_0_iff in Hr'. generalize (Cmod_ge_0 r); lra.
 - set (p1' := [topcoef p1] *, p1).
   destruct (IntPoly_null_or_large_root p1') as (r & Hr & Hr').
   { apply IntPoly_mult; trivial. constructor; [|constructor].
     rewrite CInteger_alt.
     destruct T1 as [-> | ->]; [now exists 1%Z|now exists (-1)%Z]. }
   { red. unfold p1'. rewrite topcoef_mult, topcoef_singl.
     destruct T1 as [-> | ->]; lca. }
   { unfold p1'. rewrite Pscale_degree; try lia.
     destruct T1 as [-> | ->]; injection; lra. }
   destruct Hp as (l & (Hx1 & _ & Hl1) & Hl2).
   assert (Hr2 : Root r p1).
   { unfold p1' in Hr. red in Hr.
     rewrite Pmult_eval in Hr. apply Cmult_integral in Hr.
     rewrite Pconst_eval in Hr. destruct Hr as [Hr | Hr]; try easy.
     rewrite Hr in T. rewrite Cmult_0_l in T. injection T; lra. }
   assert (IN : In r (RtoC x :: l)).
   { apply linfactors_roots. rewrite <- Hl2, E. red.
     rewrite Pmult_eval. rewrite Hr2. lca. }
   simpl in IN. destruct IN as [IN | IN]; [ now rewrite IN in Hx|].
   assert (Hr3 : 0 < Cmod r < 1).
   { rewrite Forall_forall in Hl1. now apply Hl1. }
   rewrite <- Cmod_eq_0_iff in Hr'. generalize (Cmod_ge_0 r); lra.
Qed.

Lemma RatPoly_div a b :
  RatPoly a -> RatPoly b ->
  let '(q,r) := Pdiv a b in RatPoly q /\ RatPoly r.
Proof.
 intros Ha Hb. unfold Pdiv. remember (degree a) as d. clear Heqd.
 revert a Ha. induction d; simpl; intros a Ha.
 - split; trivial. constructor.
 - case Nat.ltb_spec; intros. split; trivial. constructor.
   set (k := (degree a - degree b)%nat).
   set (c := topcoef a / topcoef b).
   set (a' := a +, _).
   assert (Ha' : RatPoly a').
   { unfold a'. apply RatPoly_plus; trivial.
     apply RatPoly_opp, RatPoly_mult; trivial.
     apply RatPoly_monom, CRational_div; now apply RatPoly_topcoef. }
   specialize (IHd a' Ha').
   destruct (Pdiv_loop a' b d) as (q,r); split; try easy.
   apply RatPoly_plus; try easy.
   apply RatPoly_monom, CRational_div; now apply RatPoly_topcoef.
Qed.

Lemma IntPoly_div a b :
  IntPoly a -> IntPoly b -> monic b ->
  let '(q,r) := Pdiv a b in IntPoly q /\ IntPoly r.
Proof.
 intros Ha Hb Hb'. unfold Pdiv. remember (degree a) as d. clear Heqd.
 revert a Ha. induction d; simpl; intros a Ha.
 - split; trivial. constructor.
 - case Nat.ltb_spec; intros. split; trivial. constructor.
   set (k := (degree a - degree b)%nat).
   rewrite Hb', Cdiv_1_r.
   set (c := topcoef a).
   set (a' := a +, _).
   assert (Ha' : IntPoly a').
   { unfold a'. apply IntPoly_plus; trivial.
     apply IntPoly_opp, IntPoly_mult; trivial.
     apply IntPoly_monom. now apply IntPoly_topcoef. }
   specialize (IHd a' Ha').
   destruct (Pdiv_loop a' b d) as (q,r); split; try easy.
   apply IntPoly_plus; try easy.
   apply IntPoly_monom. now apply IntPoly_topcoef.
Qed.

Definition monicify p := [/topcoef p]*,p.

Lemma monicify_ok p : ~Peq p [] -> monic (monicify p).
Proof.
 intros H. red. unfold monicify. rewrite topcoef_mult, topcoef_singl.
 rewrite <- topcoef_0_iff in H. now field.
Qed.

Lemma RatPoly_monicify p : RatPoly p -> RatPoly (monicify p).
Proof.
 intros. apply RatPoly_mult; trivial.
 constructor; [|constructor]. now apply CRational_inv, RatPoly_topcoef.
Qed.

Lemma monicify_root x p :
  ~Peq p [] -> Root x (monicify p) <-> Root x p.
Proof.
 intros H. unfold Root, monicify. rewrite Pmult_eval, Pconst_eval.
 split.
 - intros E. apply Cmult_integral in E. destruct E as [E|E]; try easy.
   rewrite <- topcoef_0_iff in H. apply nonzero_div_nonzero in H. easy.
 - intros ->. lca.
Qed.

Lemma const_degree a : degree [a] = 0%nat.
Proof.
 rewrite degree_cons. destruct Peq_0_dec as [E|N]; trivial. now destruct N.
Qed.

Lemma monicify_degree p : ~Peq p [] -> degree (monicify p) = degree p.
Proof.
 intros H.
 unfold monicify. rewrite Pmult_degree, const_degree; trivial.
 rewrite <- topcoef_0_iff in H. apply nonzero_div_nonzero in H.
 change (~Peq [/topcoef p] []). now rewrite <- topcoef_0_iff, topcoef_singl.
Qed.

Definition Qreducible (p:Polynomial) :=
  exists q r,
    Peq p (Pmult q r) /\ RatPoly q /\ RatPoly r /\
    (0 < degree q < degree p)%nat.

Definition MinPolyQ x p :=
  monic p /\ RatPoly p /\ Root x p /\
  forall q, ~Peq q [] -> RatPoly q -> Root x q -> (degree p <= degree q)%nat.

(* NB: RootQ_has_MinPolyQ proved here via excluded middle *)

Lemma RootQ_has_MinPolyQ x :
  (exists p, ~Peq p [] /\ RatPoly p /\ Root x p) ->
  (exists p, MinPolyQ x p).
Proof.
 intros (p & NZ & ER & Hx).
 remember (degree p) as d. revert p Heqd NZ ER Hx.
 induction d as [d IH] using lt_wf_ind.
 intros p E NZ ER Hx.
 destruct (Classical_Prop.classic
           (exists q, ~Peq q [] /\ RatPoly q /\ Root x q /\
                      (degree q < d)%nat)) as [(q & NZ' & ER' & Hx' & D)|N].
 - apply (IH (degree q) D q eq_refl NZ' ER' Hx').
 - exists (monicify p); repeat split.
   + now apply monicify_ok.
   + now apply RatPoly_monicify.
   + now rewrite monicify_root.
   + intros q NZ' RP' Hx'. rewrite monicify_degree; trivial. rewrite <- E.
     apply Nat.le_ngt. contradict N. now exists q.
Qed.

Lemma MinPolyQ_unique_aux x p q :
  MinPolyQ x p -> RatPoly q -> Root x q ->
  exists u, RatPoly u /\ Peq q (p *, u).
Proof.
 intros (MO & RP & Hx & MIN) RP' Hx'.
 destruct (Nat.eq_dec (degree p) 0) as [D0|D0].
 { exists q. split; trivial. now rewrite (deg0_monic_carac p), Pmult_1_l. }
 { destruct (Pdiv q p) as (u & v) eqn:E.
   assert (Huv1 := Pdiv_eqn q p).
   assert (Huv2 := Pdiv_degree q p).
   assert (Huv3 := RatPoly_div q p RP' RP).
   rewrite E in *; simpl in *. specialize (Huv2 ltac:(lia)).
   destruct (Peq_0_dec v) as [EQ|NE].
   { exists u. split; try easy. rewrite EQ, Pplus_0_r in Huv1.
     now rewrite Pmult_comm. }
   { assert (Rv : Root x v).
     { rewrite Huv1 in Hx'. red in Hx'. rewrite Pplus_eval, Pmult_eval in Hx'.
       rewrite Hx, Cmult_0_r, Cplus_0_l in Hx'. apply Hx'. }
     specialize (MIN v NE (proj2 Huv3) Rv). lia. }}
Qed.

Lemma MinPolyQ_unique x p q : MinPolyQ x p -> MinPolyQ x q -> Peq p q.
Proof.
 intros Hp Hq.
 destruct (MinPolyQ_unique_aux x p q Hp) as (u & Hu & E); try apply Hq.
 assert (D : degree p = degree q).
 { apply Nat.le_antisymm.
   - apply Hp; try apply Hq. rewrite <- topcoef_0_iff.
     replace (topcoef q) with 1. injection; lra. symmetry; apply Hq.
   - apply Hq; try apply Hp. rewrite <- topcoef_0_iff.
     replace (topcoef p) with 1. injection; lra. symmetry; apply Hp. }
 assert (Tp : topcoef p = 1) by apply Hp.
 assert (Tq : topcoef q = 1) by apply Hq.
 assert (Hu' : monic u).
 { assert (E' : topcoef q = topcoef (p*,u)) by now rewrite E.
   rewrite topcoef_mult, Tp, Tq, Cmult_1_l in E'. now symmetry in E'. }
 rewrite E in D. rewrite Pmult_degree in D.
 2:{ change (~Peq p []). rewrite <- topcoef_0_iff, Tp. injection; lra. }
 2:{ change (~Peq u []). rewrite <- topcoef_0_iff, Hu'. injection; lra. }
 rewrite (deg0_monic_carac u), Pmult_1_r in E; lia || easy.
Qed.

Lemma MinPolyQ_Qirred x p : MinPolyQ x p -> ~Qreducible p.
Proof.
 intros (MO & RP & Hx & MIN) (p1 & p2 & E & H1 & H2 & D).
 assert (E' : Peval (p1 *, p2) x = 0) by now rewrite <- E, Hx.
 assert (N1 : ~ Peq p1 []).
 { intros E1. rewrite E1 in D. unfold degree in D; simpl in D. lia. }
 assert (N2 : ~ Peq p2 []).
 { intros E2. rewrite E2, Pmult_0_r in E. rewrite E in D.
   unfold degree in D; simpl in D. lia. }
 rewrite Pmult_eval in E'. apply Cmult_integral in E'. destruct E' as [E'|E'].
 - generalize (MIN p1 N1 H1 E'). lia.
 - generalize (MIN p2 N2 H2 E').
   rewrite E, Pmult_degree in D |- *; try apply N1; try apply N2. lia.
Qed.

Lemma MinPolyQ_alt x p :
  MinPolyQ x p <-> monic p /\ RatPoly p /\ Root x p /\ ~Qreducible p.
Proof.
 split.
 - intros Hp. repeat split; try apply Hp. now apply (MinPolyQ_Qirred x p).
 - intros (MO & RP & Hx & IR).
   assert (NZ : ~Peq p []).
   { rewrite <- topcoef_0_iff. rewrite MO. injection;lra. }
   destruct (RootQ_has_MinPolyQ x (ex_intro _ p (conj NZ (conj RP Hx))))
     as (q & Hq).
   destruct (MinPolyQ_unique_aux x q p Hq RP Hx) as (u & RPu & E).
   assert (D : ~(0 < degree q < degree p)%nat).
   { contradict IR. exists q, u. repeat (split; try assumption). apply Hq. }
   destruct (Nat.eq_dec (degree q) 0) as [D'|D'].
   + destruct Hq as (MO' & RP' & Hx' & _).
     rewrite (deg0_monic_carac q) in Hx'; trivial.
     red in Hx'. rewrite Pconst_eval in Hx'. injection Hx'; lra.
   + assert (degree p <= degree q)%nat by lia.
     repeat split; trivial.
     intros r Hr1 Hr2 Hr3. apply Nat.le_trans with (degree q); trivial.
     now apply Hq.
Qed.

Definition Zcontent (l : list Z) := fold_right Z.gcd Z0 l.

Lemma Zcontent_pos l : (0 <= Zcontent l)%Z.
Proof.
 destruct l; simpl. lia. apply Z.gcd_nonneg.
Qed.

Lemma Zcontent_0 l : (forall x, In x l -> x=Z0) -> Zcontent l = Z0.
Proof.
 induction l; simpl; trivial.
 intros H. now rewrite (H a), IHl by firstorder.
Qed.

Lemma Zcontent_0_rev l : Zcontent l = Z0 -> Peq (Zpoly l) [].
Proof.
 induction l; simpl; try easy.
 intros E. rewrite (Z.gcd_eq_0_l _ _ E). unfold "∘".
 rewrite IHl. 2:now apply Z.gcd_eq_0_r in E. apply C0_Peq_nil.
Qed.

Lemma monic_Zcontent l : monic (Zpoly l) -> Zcontent l = 1%Z.
Proof.
 unfold monic.
 induction l; simpl.
 - unfold topcoef. simpl. intros [= E]. lra.
 - rewrite topcoef_cons. destruct Peq_0_dec as [E|N].
   + rewrite Zcontent_0. intros Ha. apply RtoC_inj, eq_IZR in Ha. now subst a.
     intros x IN.
     apply eq_IZR, RtoC_inj. apply (Peq_nil_contains_C0 _ E).
     change (RtoC (IZR x)) with ((RtoC∘IZR) x). now apply in_map.
   + intros H. rewrite IHl; trivial. now rewrite Z.gcd_1_r.
Qed.

Lemma Zcontent_ok (l : list Z) x : In x l -> Z.divide (Zcontent l) x.
Proof.
 unfold Zcontent.
 revert x.
 induction l; simpl; try easy.
 intros x [->|IN]. apply Z.gcd_divide_l.
 eapply Z.divide_trans; [apply Z.gcd_divide_r|]. now apply IHl.
Qed.

Lemma Zcontent_1_first_nondiv (l : list Z) x :
 (1 < x)%Z -> Z.gcd x (Zcontent l) = 1%Z ->
 exists i, ~Z.divide x (nth i l Z0)
           /\ forall j, (j<i)%nat -> Z.divide x (nth j l Z0).
Proof.
 intros Hx.
 induction l; intros H; simpl in H.
 - rewrite Z.gcd_0_r in H. lia.
 - destruct (Znumtheory.Zdivide_dec x a) as [D|ND].
   + rewrite Z.gcd_assoc in H.
     destruct IHl as (i & H1 & H2).
     { rewrite Z.divide_gcd_iff in D by lia. now rewrite D in H. }
     exists (S i); split; try easy.
     intros [|j] Hj; simpl; trivial. apply H2; lia.
   + exists O; split; simpl; trivial; try lia.
Qed.

Definition PolyZ_factor (l : list Z) : list Z :=
  map (fun x => x / Zcontent l)%Z l.

Lemma PolyZ_factor_ok (l : list Z) :
 Peq ([RtoC (IZR (Zcontent l))] *, Zpoly (PolyZ_factor l)) (Zpoly l).
Proof.
 destruct (Z.eq_dec (Zcontent l) 0) as [E|N].
 - rewrite E. apply Zcontent_0_rev in E. rewrite E, C0_Peq_nil. easy.
 - simpl.
   unfold PolyZ_factor, Zpoly.
   simpl. rewrite !map_map, C0_Peq_nil, Pplus_0_r. apply eq_Peq.
   apply map_ext_in. intros x Hx. unfold "∘".
   rewrite <- RtoC_mult, <- mult_IZR. do 2 f_equal.
   destruct (Zcontent_ok l x Hx) as (r & ->).
   rewrite Zdiv.Z_div_mult_full; trivial. ring.
Qed.

Lemma Zcontent_factor (l : list Z) a :
 Zcontent (map (Z.mul a) l) = (Z.abs a * Zcontent l)%Z.
Proof.
 induction l; simpl. ring.
 rewrite IHl.
 destruct (Z.abs_eq_or_opp a) as [E|N].
 - rewrite E at 1. now rewrite Z.gcd_mul_mono_l.
 - rewrite N at 1. now rewrite Z.mul_opp_l, Z.gcd_opp_r, Z.gcd_mul_mono_l.
Qed.

Lemma PolyZ_factor_content (l : list Z) :
 ~Peq (Zpoly l) [] ->
 Zcontent (PolyZ_factor l) = 1%Z.
Proof.
 intros H.
 assert (NZ : Zcontent l <> Z0).
 { contradict H. now apply Zcontent_0_rev. }
 apply Z.mul_cancel_l with (Zcontent l); trivial.
 rewrite <- (Z.abs_eq (Zcontent l)) at 1 by apply Zcontent_pos.
 rewrite <- Zcontent_factor, Z.mul_1_r. f_equal.
 unfold PolyZ_factor. rewrite map_map.
 erewrite map_ext_in; [apply map_id|]. intros x Hx. simpl.
 destruct (Zcontent_ok l x Hx) as (r & ->).
 rewrite Zdiv.Z_div_mult_full by easy. ring.
Qed.

Definition lcm_denoms (l : list Q) : Z :=
  fold_right Z.lcm 1%Z (map (Z.pos ∘ Qden) l).

Lemma lcm_denoms_ok (l : list Q) q :
  In q l -> Z.divide (Zpos (Qden q)) (lcm_denoms l).
Proof.
 unfold lcm_denoms.
 revert q.
 induction l; simpl; try easy.
 intros q [->|IN]. apply Z.divide_lcm_l.
 eapply Z.divide_trans; [|apply Z.divide_lcm_r]. now apply IHl.
Qed.

Lemma lcm_denoms_nz (l : list Q) : lcm_denoms l <> Z0.
Proof.
 unfold lcm_denoms.
 induction l; simpl; try lia. rewrite Z.lcm_eq_0. now intros [E|E].
Qed.

Definition PolyQ_factor (l : list Q) : list Z :=
  map (fun q => lcm_denoms l/(Zpos (Qden q)) * Qnum q)%Z l.

Lemma PolyQ_factor_ok (l : list Q) :
 Peq (Zpoly (PolyQ_factor l))
     ([RtoC (lcm_denoms l)] *, Qpoly l).
Proof.
 unfold PolyQ_factor, Zpoly, Qpoly.
 simpl. rewrite !map_map, C0_Peq_nil, Pplus_0_r. apply eq_Peq.
 apply map_ext_in. intros q Hq. unfold "∘". rewrite <- RtoC_mult. f_equal.
 unfold Q2R. rewrite mult_IZR.
 destruct (lcm_denoms_ok l q Hq) as (r & ->).
 rewrite Zdiv.Z_div_mult_full by easy.
 rewrite mult_IZR. field. now apply IZR_neq.
Qed.

Lemma RatPoly_scal_IntPoly p :
 RatPoly p -> exists z:Z, z<>Z0 /\ IntPoly ([RtoC z]*,p).
Proof.
 rewrite RatPoly_alt'. intros (q & E).
 exists (lcm_denoms q). split. apply lcm_denoms_nz.
 rewrite IntPoly_alt'. exists (PolyQ_factor q). symmetry.
 rewrite E. apply PolyQ_factor_ok.
Qed.

Definition Qcontent (l : list Q) :=
  (inject_Z (Zcontent (PolyQ_factor l)) / inject_Z (lcm_denoms l))%Q.

Global Program Instance Z_is_monoid : Monoid Z :=
 { Gzero := Z0 ; Gplus := Z.add }.
Solve All Obligations with lia.

Lemma big_sum_IZR (f : nat -> Z) n :
 IZR (big_sum f n) = big_sum (IZR∘f) n.
Proof.
 induction n; simpl; trivial. now rewrite plus_IZR, IHn.
Qed.

Lemma big_sum_RtoC (f : nat -> R) n :
 RtoC (big_sum f n) = big_sum (RtoC∘f) n.
Proof.
 induction n; simpl; trivial. now rewrite RtoC_plus, IHn.
Qed.

Lemma Pmult_Zpoly_coef (p q : list Z) n:
 coef n (Zpoly p *, Zpoly q) =
 big_sum (fun k => nth k p Z0 * nth (n-k) q Z0)%Z (S n).
Proof.
 rewrite Pmult_coef, big_sum_IZR, big_sum_RtoC.
 apply big_sum_eq_bounded. intros x Hx.
 rewrite !coef_Zpoly. unfold "∘". now rewrite mult_IZR, RtoC_mult.
Qed.

Lemma divide_big_sum (f : nat -> Z) n x :
 (forall i, (i < n)%nat -> Z.divide x (f i)) -> Z.divide x (big_sum f n).
Proof.
 induction n; simpl; intros H.
 - apply Z.divide_0_r.
 - apply Z.divide_add_r.
   + apply IHn. intros i Hi. apply H; lia.
   + apply H. lia.
Qed.

Lemma prime_divisor (n : Z) :
  (1 < n)%Z -> exists p, Znumtheory.prime p /\ Z.divide p n.
Proof.
 intros Hn. generalize Hn.
 pattern n. apply Z_lt_induction; try lia. clear n Hn.
 intros n IH Hn.
 destruct (Znumtheory.prime_dec n) as [P|NP].
 - now exists n.
 - apply Znumtheory.not_prime_divide in NP; try lia.
   destruct NP as (q & Hq & D).
   destruct (IH q) as (p & Hp & D'); try lia.
   exists p; split; trivial. eapply Z.divide_trans; eauto.
Qed.

Lemma GaussLemma p : IntPoly p -> monic p -> Qreducible p -> Zreducible p.
Proof.
 intros Hp Mp (q & r & E & Hq & Hr & D).
 destruct (RatPoly_scal_IntPoly q Hq) as (c & Hc & Hq1).
 set (c1 := RtoC c) in *.
 set (q1 := [c1] *, q) in *.
 destruct (RatPoly_scal_IntPoly r Hr) as (d & Hd & Hr1).
 set (d1 := RtoC d) in *.
 set (r1 := [d1] *, r) in *.
 apply (Pmult_eq_compat [c1*d1] ([c1]*,[d1])) in E.
 2:{ simpl. now rewrite Cplus_0_r. }
 rewrite Pmult_assoc, (Pmult_comm _ (q*,r)), !Pmult_assoc in E.
 rewrite (Pmult_comm r) in E. fold r1 in E.
 rewrite <- Pmult_assoc in E. fold q1 in E.
 assert (D' : (0 < degree q1 < degree p)%nat).
 { unfold q1. rewrite Pscale_degree; trivial. intros [= H].
   now apply (not_0_IZR c). }
 clearbody q1 r1. clear q r Hq Hr D.
 assert (NZq : ~Peq q1 []).
 { intros E1. rewrite E1 in D'. unfold degree in D'. simpl in D'. lia. }
 apply IntPoly_alt in Hq1. destruct Hq1 as (q1', ->).
 rewrite <- (PolyZ_factor_ok q1') in E.
 set (c2 := RtoC (Zcontent q1')) in *.
 assert (Hq2 := PolyZ_factor_content q1' NZq).
 set (q2 := PolyZ_factor q1') in *.
 assert (NZr : ~Peq r1 []).
 { intros E2. rewrite E2 in E. rewrite Pmult_0_r in E.
   rewrite <- (Pscale_degree (c1 * d1) p) in D'. rewrite E in D'.
   unfold degree in D'. simpl in D'. lia. unfold c1, d1.
   rewrite <- RtoC_mult, <- mult_IZR. intros [= H].
   apply not_0_IZR in H; trivial. lia. }
 apply IntPoly_alt in Hr1. destruct Hr1 as (r1', ->).
 rewrite <- (PolyZ_factor_ok r1') in E.
 set (d2 := RtoC (Zcontent r1')) in *.
 assert (Hr2 := PolyZ_factor_content r1' NZr).
 set (r2 := PolyZ_factor r1') in *.
 rewrite Pmult_assoc, <- (Pmult_assoc (Zpoly q2)) in E.
 rewrite (Pmult_comm (Zpoly q2)), <- !Pmult_assoc in E.
 assert (Hc2 : c2 <> 0).
 { intros [= H]. apply not_0_IZR in H; trivial.
   contradict NZq. now apply Zcontent_0_rev. }
 assert (Hd2 : d2 <> 0).
 { intros [= H]. apply not_0_IZR in H; trivial.
   contradict NZr. now apply Zcontent_0_rev. }
 assert (E' : Peq ([c2]*,[d2]) [c2 * d2]).
 { simpl. now rewrite Cplus_0_r. }
 rewrite E' in E. clear E'.
 assert (D2 : (0 < degree (Zpoly q2) < degree p)%nat).
 { unfold q2.
   rewrite <- (Pscale_degree c2 (Zpoly (PolyZ_factor q1'))); trivial.
   unfold c2. now rewrite PolyZ_factor_ok. }
 set (g := Z.gcd (c * d) (Zcontent q1' * Zcontent r1')).
 set (m := (c * d / g)%Z).
 set (l := (Zcontent q1' * Zcontent r1' / g)%Z).
 assert (Hg : (0 < g)%Z).
 { apply Z.le_neq; split.
   - apply Z.gcd_nonneg.
   - intros H. symmetry in H. apply Z.gcd_eq_0_l in H. lia. }
 assert (E1 : c1 * d1 = RtoC g * RtoC m).
 { unfold c1, d1. rewrite <- !RtoC_mult, <- !mult_IZR. do 2 f_equal.
   unfold m. rewrite <- Znumtheory.Zdivide_Zdiv_eq; trivial.
   apply Z.gcd_divide_l. }
 rewrite E1 in E.
 assert (Hm : m <> Z0).
 { intros ->. rewrite Cmult_0_r in E1.
   unfold c1, d1 in E1. rewrite <- !RtoC_mult, <- !mult_IZR in E1.
   injection E1 as E1. apply not_0_IZR in E1; trivial. lia. }
 assert (E2 : c2 * d2 = RtoC g * RtoC l).
 { unfold c2, d2. rewrite <- !RtoC_mult, <- !mult_IZR. do 2 f_equal.
   unfold l. rewrite <- Znumtheory.Zdivide_Zdiv_eq; trivial.
   apply Z.gcd_divide_r. }
 rewrite E2 in E.
 assert (Hl : (0 < l)%Z).
 { apply Z.le_neq. split.
   - apply Z.div_pos; trivial. apply Z.mul_nonneg_nonneg; apply Zcontent_pos.
   - intros <-. rewrite Cmult_0_r in E2.
     apply Cmult_integral in E2. now destruct E2. }
 assert (Hml : Z.gcd m l = 1%Z).
 { apply Z.mul_cancel_l with g; try lia.
   rewrite <- (Z.abs_eq g) at 1 by apply Z.gcd_nonneg.
   rewrite <- Z.gcd_mul_mono_l.
   unfold c1, d1 in E1.
   rewrite <- !RtoC_mult, <- !mult_IZR in E1.
   apply RtoC_inj, eq_IZR in E1. rewrite <- E1.
   unfold c2, d2 in E2.
   rewrite <- !RtoC_mult, <- !mult_IZR in E2.
   apply RtoC_inj, eq_IZR in E2. rewrite <- E2.
   fold g. lia. }
 clear E1 E2.
 assert (E1 : Peq [RtoC g * RtoC m] ([RtoC g] *, [RtoC m])).
 { simpl. now rewrite Cplus_0_r. }
 rewrite E1 in E.
 assert (E2 : Peq [RtoC g * RtoC l] ([RtoC g] *, [RtoC l])).
 { simpl. now rewrite Cplus_0_r. }
 rewrite E2 in E. clear E1 E2.
 rewrite !Pmult_assoc in E. apply Pmult_Peq_reg_l in E.
 2:{ rewrite <- topcoef_0_iff, topcoef_singl.
     intros [= H]. apply not_0_IZR in H; lia. }
 clearbody r2 q2 g l m.
 clear c d Hc Hd c1 d1 q1' r1' c2 d2 NZq NZr D' Hc2 Hd2.
 replace l with 1%Z in *.
 2:{ assert (H := Proper_instance_1 _ _ E).
     rewrite !topcoef_mult, !topcoef_singl in H. rewrite Mp in H.
     rewrite Cmult_1_r in H.
     assert (Tq := IntPoly_topcoef (Zpoly q2)).
     rewrite IntPoly_alt, CInteger_alt in Tq.
     destruct Tq as (z & Hz). now eexists. rewrite Hz in H.
     assert (Tr := IntPoly_topcoef (Zpoly r2)).
     rewrite IntPoly_alt, CInteger_alt in Tr.
     destruct Tr as (z' & Hz'). now eexists. rewrite Hz' in H. clear Hz Hz'.
     rewrite <- !RtoC_mult, <- !mult_IZR in H. apply RtoC_inj in H.
     apply eq_IZR in H.
     assert (H' : Z.divide l m). { exists (z*z')%Z. subst m. ring. }
     rewrite Z.divide_gcd_iff in H'; try lia. rewrite Z.gcd_comm in H'.
     now rewrite Hml in H'. }
 rewrite Pmult_1_l in E.
 clear g l Hml Hg Hl.
 destruct (Z.eq_dec m 1%Z) as [->|Hm1].
 { rewrite Pmult_1_l in E.
   exists (Zpoly q2), (Zpoly r2); repeat split; try easy.
   rewrite IntPoly_alt. now eexists.
   rewrite IntPoly_alt. now eexists. }
 destruct (Z.eq_dec m (-1)%Z) as [->|Hm1'].
 { rewrite <- (Pmult_1_l (Zpoly q2 *, _)) in E.
   replace [1] with ([-1]*,[-1]) in E.
   2:{ simpl. f_equal. ring. }
   rewrite Pmult_assoc in E. apply Pmult_Peq_reg_l in E.
   2:{ rewrite <- topcoef_0_iff, topcoef_singl. intros [= H]; lra. }
   rewrite <- Pmult_assoc in E.
   exists ([-1] *, Zpoly q2), (Zpoly r2); repeat split; try easy.
   - apply IntPoly_mult.
     + rewrite IntPoly_alt. now exists [(-1)%Z].
     + rewrite IntPoly_alt. now eexists.
   - rewrite IntPoly_alt. now eexists.
   - rewrite Pscale_degree; try easy. intros [= H]; lra.
   - rewrite Pscale_degree; try easy. intros [= H]; lra. }
 exfalso.
 assert (Hm2 : (1 < Z.abs m)%Z) by lia.
 destruct (prime_divisor (Z.abs m) Hm2) as (pr & Hpr & D).
 rewrite Z.divide_abs_r in D.
 destruct (Zcontent_1_first_nondiv q2 pr) as (i & Hi & Hi').
 { apply Hpr. }
 { now rewrite Hq2, Z.gcd_1_r. }
 destruct (Zcontent_1_first_nondiv r2 pr) as (j & Hj & Hj').
 { apply Hpr. }
 { now rewrite Hr2, Z.gcd_1_r. }
 rewrite IntPoly_alt in Hp. destruct Hp as (p2 & ->).
 assert (E' := Pmult_Zpoly_coef q2 r2 (i+j)).
 rewrite <- E in E'.
 rewrite Pscale_coef, coef_Zpoly, <- RtoC_mult, <- mult_IZR in E'.
 apply RtoC_inj, eq_IZR in E'.
 set (bs := big_sum _ _) in E'.
 assert (D' : Z.divide pr bs).
 { apply Z.divide_trans with m; trivial. eexists.
   symmetry. rewrite Z.mul_comm. apply E'. }
 unfold bs in *; clear E' bs.
 rewrite <- Nat.add_succ_r in D'.
 rewrite big_sum_sum in D'.
 apply Z.divide_add_cancel_r in D'.
 2:{ clear D'. apply divide_big_sum. intros k Hk. apply Z.divide_mul_l.
     apply Hi'; trivial. }
 rewrite <- big_sum_extend_l, Z.add_comm in D'.
 apply Z.divide_add_cancel_r in D'.
 2:{ clear D'. apply divide_big_sum. intros k Hk. apply Z.divide_mul_r.
     apply Hj'. lia. }
 rewrite Nat.add_0_r in D'.
 replace (i+j-i)%nat with j in D' by lia.
 apply Znumtheory.prime_mult in D'; trivial. tauto.
Qed.

Lemma PisotPoly_minimal x p : PisotPoly x p -> MinPolyQ x p.
Proof.
 intros Hp.
 assert (Mp : monic p).
 { destruct Hp as (l & Hl & Hl'). red. rewrite Hl'.
   apply linfactors_monic. }
 rewrite MinPolyQ_alt; repeat split; trivial.
 - apply PisotIntPoly in Hp. rewrite IntPoly_alt in Hp.
   destruct Hp as (p' & ->).
   rewrite RatPoly_alt. exists (map inject_Z p').
   unfold Zpoly, Qpoly. rewrite map_map. unfold "∘". apply map_ext.
   intros z. now rewrite Q2R_IZR.
 - now apply PisotPolyRoot.
 - intros Hp'. apply (PisotPolyIrred x p); trivial.
   apply GaussLemma; trivial. eapply PisotIntPoly; eauto.
Qed.

Lemma PisotPolyUnique x p q : PisotPoly x p -> PisotPoly x q -> Peq p q.
Proof.
 intros. apply (MinPolyQ_unique x); now apply PisotPoly_minimal.
Qed.

Lemma big_sum_CInteger (f : nat -> C) n :
 (forall k, (k < n)%nat -> CInteger (f k)) -> CInteger (big_sum f n).
Proof.
 induction n; simpl.
 - intros _. rewrite CInteger_alt. now exists 0%Z.
 - intros H. apply CInteger_plus.
   + apply IHn. intros k Hk. apply H; lia.
   + apply H. lia.
Qed.

Lemma reciprocal_linfactors_cons a l :
 ~In 0 (a::l) ->
 Peq (reciprocal (linfactors (a::l)))
     ([1;-a] *, reciprocal (linfactors l)).
Proof.
 intros H.
 rewrite !reciprocal_revfactors; trivial.
 2:{ simpl in H. tauto. }
 unfold revfactors. simpl linfactors.
 rewrite Pmult_eval. rewrite (Peval_0 [_;_]).
 unfold coef. simpl nth.
 replace [_*_] with ([Peval (linfactors l) 0]*,[-a]).
 2:{ simpl. f_equal. ring. }
 rewrite <- (Pmult_assoc [1;-a]), (Pmult_comm [1;-a]), !Pmult_assoc.
 apply Pmult_eq_compat; try easy.
 rewrite <- (Pmult_assoc [-a]), (Pmult_comm [-a]), (Pmult_comm [1;-a]).
 rewrite Pmult_assoc. apply Pmult_eq_compat; try easy.
 simpl. apply eq_Peq. f_equal. field. simpl in H. tauto.
 now rewrite Cmult_1_r.
Qed.

(** Siegel Theorem : the smallest Pisot number is the Plastic Ratio.
    (Ref: Algbraic numbers whose conjugates lie in the unit circle, 1944) *)

Module SiegelProof.
Section Siegel.
Variable root : R.
Hypothesis Hroot : root^2 < 2.
Variable roots : (list C).
Hypothesis Hroots : PisotConjugates root roots.
Variable coefs : list Z.
Hypothesis Hcoefs : Peq (Zpoly coefs) (linfactors (RtoC root::roots)).

Lemma roots_nz : ~In 0 roots.
Proof.
 intros IN. destruct Hroots as (_ & _ & H).
 rewrite Forall_forall in H. specialize (H _ IN).
 rewrite Cmod_0 in H. lra.
Qed.

Lemma invroot : 0 < /root < 1.
Proof.
 split.
 - apply Rinv_0_lt_compat; red in Hroots; lra.
 - rewrite <- Rinv_1. apply Rinv_lt_contravar; red in Hroots; lra.
Qed.

Ltac lra' := (red in Hroots; generalize invroot; lra).

Lemma roots_nz' : ~In 0 (RtoC root :: roots).
Proof.
 simpl. intros [[= H]|H]. lra'. now apply roots_nz.
Qed.

Local Notation Pcoef := (Zpoly coefs).

Lemma Root_nz : ~Root 0 Pcoef.
Proof.
 rewrite Hcoefs, <- linfactors_roots. apply roots_nz'.
Qed.

Local Notation sgn := (Z.sgn (nth 0 coefs Z0)).

Definition f (x:C) := IZR sgn * Peval Pcoef x / Peval (reciprocal Pcoef) x.

Lemma ff x : ~Root x Pcoef -> ~Root (/x) Pcoef -> x <> 0 -> f x * f (/x) = 1.
Proof.
 intros H1 H2 H3. unfold f.
 rewrite !Peval_reciprocal, Cinv_inv, Cpow_inv; trivial.
 2:{ now apply nonzero_div_nonzero. }
 2:{ contradict H1. now rewrite H1. }
 2:{ contradict H1. now rewrite H1. }
 field_simplify.
 2:{ repeat split; trivial. now apply Cpow_nz. }
 { unfold sgn.
   generalize Root_nz.
   unfold Root. rewrite Peval_0, coef_Zpoly.
   destruct nth; simpl; intros; easy || ring. }
Qed.

Definition fps :=
  CPS_mult (PS_poly ([IZR sgn * /Peval Pcoef 0] *, Pcoef))
           (PS_inv_linfactors (map Cinv (RtoC root::roots))).

Lemma invroot_le_min_Cmod :
  Rbar.Rbar_le (/ root)%R (min_Cmod_list (map Cinv (RtoC root :: roots))).
Proof.
 unfold min_Cmod_list. simpl map.
 cbn -[Rbar.Rbar_min Rbar.Rbar_le].
 apply Rbar.Rbar_min_case.
 - rewrite <- RtoC_inv, Cmod_R, Rabs_pos_eq. now simpl. lra'.
 - change (Rbar.Rbar_le (/root)%R (min_Cmod_list (map Cinv roots))).
   apply Rbar.Rbar_lt_le. apply min_Cmod_list_spec, Forall_forall.
   intros y. rewrite in_map_iff. intros (z & <- & IN).
   red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
   rewrite Cmod_inv.
   apply Rinv_lt_contravar. apply Rmult_lt_0_compat; lra. lra.
Qed.

Lemma fps_radius : Rbar.Rbar_le (/root)%R (C_CV_radius fps).
Proof.
 unfold fps.
 eapply Rbar.Rbar_le_trans; [|apply C_CV_radius_mult].
 rewrite PS_poly_radius.
 apply Rbar.Rbar_min_case; [simpl; trivial|].
 eapply Rbar.Rbar_le_trans; [|apply PS_inv_linfactors_radius].
 - apply invroot_le_min_Cmod.
 - rewrite in_map_iff. intros (r & Hr & IN).
   rewrite Cinv_eq_0_iff in Hr. subst r. now apply roots_nz'.
Qed.

Lemma below_invroot x : Cmod x < / root -> x <> 0 -> ~Root (/ x) Pcoef.
Proof.
 intros H1 H2.
 rewrite Hcoefs.
 intros H. apply linfactors_roots in H. simpl in H. destruct H.
 - replace x with (/root) in H1.
   2:{ now rewrite H, Cinv_inv. }
   rewrite <- RtoC_inv, Cmod_R in H1.
   generalize (Rle_abs (/root)%R); lra.
 - red in Hroots. rewrite Forall_forall in Hroots.
   apply Hroots in H. rewrite Cmod_inv in H.
   apply Rinv_lt_contravar in H1. rewrite Rinv_inv in H1. lra.
   apply Rmult_lt_0_compat; apply Cmod_gt_0 in H2; lra.
Qed.

Lemma fps_ok x : Cmod x < /root -> is_CPowerSeries fps x (f x).
Proof.
 intros Hx.
 unfold fps.
 replace (f x) with ((IZR sgn * /Peval Pcoef 0 * Peval Pcoef x) *
                     (Peval Pcoef 0 * /Peval (reciprocal Pcoef) x)).
 2:{ unfold f. field. split; try apply Root_nz.
     destruct (Ceq_dec x 0) as [Y|N].
     - subst. rewrite Peval_reciprocal_0.
       rewrite Hcoefs, linfactors_monic. intros [=H]; lra.
     - rewrite Peval_reciprocal; trivial.
       + intros H. apply Cmult_integral in H. destruct H.
         apply below_invroot in H; trivial.
         now apply (Cpow_nz x (degree Pcoef)) in N.
       + rewrite <- topcoef_0_iff.
         rewrite Hcoefs, linfactors_monic. intros [=H]; lra. }
 apply is_CPS_mult.
 - rewrite <- (Pconst_eval (_ * /Peval _ 0) x) at 2.
   rewrite <- Pmult_eval. apply PS_poly_ok.
 - rewrite Hcoefs, reciprocal_revfactors by apply roots_nz'.
   rewrite Pmult_eval, Pconst_eval.
   rewrite Cinv_mult, Cmult_assoc, Cinv_r, Cmult_1_l.
   2:{ rewrite <- Hcoefs. apply Root_nz. }
   unfold revfactors.
   apply PS_inv_linfactors_ok.
   rewrite <- min_Cmod_list_spec.
   eapply Rbar.Rbar_lt_le_trans; [|apply invroot_le_min_Cmod]. apply Hx.
 - now rewrite PS_poly_radius.
 - eapply Rbar.Rbar_lt_le_trans; [|apply PS_inv_linfactors_radius].
   2:{ rewrite in_map_iff. intros (y & Hy & IN).
       rewrite Cinv_eq_0_iff in Hy. rewrite Hy in IN. now apply roots_nz'. }
   eapply Rbar.Rbar_lt_le_trans; [|apply invroot_le_min_Cmod]. apply Hx.
Qed.

Lemma fps_eqn n :
  CPS_mult fps (PS_poly (reciprocal Pcoef)) n =
  PS_poly ([RtoC sgn] *, Pcoef) n.
Proof.
 apply CPowerSeries_coef_ext.
 - eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
   rewrite PS_poly_radius.
   apply Rbar.Rbar_min_case; [|simpl; trivial].
   eapply Rbar.Rbar_lt_le_trans; [|apply fps_radius; trivial]. simpl. lra'.
 - now rewrite PS_poly_radius.
 - assert (Hr : 0 < /root) by lra'.
   exists (mkposreal _ Hr). intros y Hy.
   change (Rabs (y-R0) < /root) in Hy. rewrite Rminus_0_r in Hy.
   rewrite <- Cmod_R in Hy.
   rewrite CPowerSeries_mult.
   2:{ eapply Rbar.Rbar_lt_le_trans; [|apply fps_radius]; trivial. }
   2:{ now rewrite PS_poly_radius. }
   do 2 rewrite (CPowerSeries_unique _ _ _ (PS_poly_ok _ _)).
   rewrite (CPowerSeries_unique _ _ _ (fps_ok _ Hy)).
   rewrite Pmult_eval, Pconst_eval.
   unfold f. field.
   { destruct (Ceq_dec y 0) as [->|N].
     - rewrite Peval_reciprocal_0.
       rewrite Hcoefs, linfactors_monic. intros [=H]; lra.
     - rewrite Peval_reciprocal; trivial.
       2:{ rewrite <- topcoef_0_iff.
           rewrite Hcoefs, linfactors_monic. intros [=H]; lra. }
       intros H. apply Cmult_integral in H. destruct H.
       apply below_invroot in H; trivial.
       now apply (Cpow_nz y (degree Pcoef)) in N. }
Qed.

Lemma fps_CInteger n : CInteger (fps n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 generalize (fps_eqn n).
 unfold PS_poly. rewrite Pscale_coef.
 unfold CPS_mult. rewrite coef_Zpoly, <- RtoC_mult, <- mult_IZR.
 rewrite <- big_sum_sum_n, <- big_sum_extend_r.
 simpl. replace (n-n)%nat with 0%nat by lia.
 rewrite <- Peval_0, Peval_reciprocal_0.
 rewrite Hcoefs, linfactors_monic, Cmult_1_r.
 set (bs := big_sum _ _).
 intros E. replace (fps n) with (IZR (sgn * nth n coefs 0%Z) - bs).
 2:{ rewrite <- E. lca. }
 clear E.
 apply CInteger_plus. rewrite CInteger_alt. now eexists.
 replace (-bs) with ((-1)*bs) by ring.
 apply CInteger_mult. rewrite CInteger_alt. now exists (-1)%Z.
 apply big_sum_CInteger.
 intros k Hk. apply CInteger_mult. now apply IH.
 destruct (Nat.le_gt_cases (n-k) (degree Pcoef)).
 - rewrite reciprocal_coef by trivial. apply IntPoly_coef.
   rewrite IntPoly_alt. now eexists.
 - rewrite reciprocal_coef_0 by trivial.
   rewrite CInteger_alt. now exists 0%Z.
Qed.

Definition g x :=
  IZR sgn * Peval Pcoef x / Peval (reciprocal (linfactors roots)) x.

Definition g_f x : x <> /root -> g x = (1-root*x) * f x.
Proof.
 intros Hx.
 unfold g, f, Cdiv. rewrite !Cmult_assoc.
 rewrite (Cmult_comm (_-_)). rewrite <- !Cmult_assoc. f_equal.
 rewrite (Cmult_comm (_-_)). rewrite <- !Cmult_assoc. f_equal.
 rewrite Hcoefs, reciprocal_linfactors_cons by apply roots_nz'.
 rewrite Pmult_eval.
 rewrite Cinv_mult, Cmult_comm, Cmult_assoc.
 rewrite <- (Cmult_1_l (/ _)) at 1. f_equal.
 unfold Peval. simpl. field. simpl. contradict Hx.
 apply Cmult_eq_reg_l with (RtoC root).
 2:{ generalize roots_nz'. simpl; tauto. }
 rewrite Cinv_r. 2:{ generalize roots_nz'. simpl; tauto. }
 symmetry. apply Cminus_eq_0. rewrite <- Hx. ring.
Qed.

Definition gps :=
  CPS_mult (PS_poly ([IZR sgn * /Peval (linfactors roots) 0] *, Pcoef))
           (PS_inv_linfactors (map Cinv roots)).

Lemma gps_radius : Rbar.Rbar_lt 1%R (C_CV_radius gps).
Proof.
 unfold gps.
 eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
 rewrite PS_poly_radius.
 apply Rbar.Rbar_min_case; [simpl; trivial|].
 eapply Rbar.Rbar_lt_le_trans; [|apply PS_inv_linfactors_radius].
 - apply min_Cmod_list_spec, Forall_forall.
   intros x. rewrite in_map_iff. intros (y & <- & IN).
   red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
   rewrite Cmod_inv, <- Rinv_1. apply Rinv_lt_contravar; lra.
 - rewrite in_map_iff. intros (r & Hr & IN).
   rewrite Cinv_eq_0_iff in Hr. subst r. now apply roots_nz.
Qed.

Lemma below_1 x : Cmod x <= 1 -> x <> 0 -> ~Root (/ x) (linfactors roots).
Proof.
 intros H1 H2.
 intros H. apply linfactors_roots in H.
 red in Hroots. rewrite Forall_forall in Hroots.
 apply Hroots in H. rewrite Cmod_inv in H.
 apply Rinv_le_contravar in H1. rewrite Rinv_1 in H1; lra.
 apply Cmod_gt_0 in H2; lra.
Qed.

Lemma gps_ok x :
  Cmod x <= 1 -> is_CPowerSeries gps x (g x).
Proof.
 intros Hx.
 unfold gps.
 replace (g x) with ((IZR sgn * /Peval (linfactors roots) 0 * Peval Pcoef x) *
     (Peval (linfactors roots) 0 * /Peval (reciprocal (linfactors roots)) x)).
 2:{ unfold g. field. split.
     2:{ change (~Root 0 (linfactors roots)).
         rewrite <- linfactors_roots. apply roots_nz. }
     destruct (Ceq_dec x 0) as [Y|N].
     - subst. rewrite Peval_reciprocal_0.
       rewrite linfactors_monic. intros [=H]; lra.
     - rewrite Peval_reciprocal; trivial.
       + intros H. apply Cmult_integral in H. destruct H.
         apply below_1 in H; trivial.
         now apply (Cpow_nz x (degree (linfactors roots))) in N.
       + rewrite <- topcoef_0_iff.
         rewrite linfactors_monic. intros [=H]; lra. }
 apply is_CPS_mult.
 - rewrite <- (Pconst_eval (_ * /Peval _ 0) x) at 2.
   rewrite <- Pmult_eval. apply PS_poly_ok.
 - rewrite reciprocal_revfactors by apply roots_nz.
   rewrite Pmult_eval, Pconst_eval.
   rewrite Cinv_mult, Cmult_assoc, Cinv_r, Cmult_1_l.
   2:{ change (~Root 0 (linfactors roots)).
       rewrite <- linfactors_roots. apply roots_nz. }
   unfold revfactors.
   apply PS_inv_linfactors_ok.
   apply Forall_forall. intros y. rewrite in_map_iff. intros (z & <- & IN).
   red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
   rewrite Cmod_inv. eapply Rle_lt_trans; eauto. rewrite <- Rinv_1.
   apply Rinv_lt_contravar; lra.
 - now rewrite PS_poly_radius.
 - eapply Rbar.Rbar_lt_le_trans; [|apply PS_inv_linfactors_radius].
   2:{ rewrite in_map_iff. intros (y & Hy & IN).
       rewrite Cinv_eq_0_iff in Hy. rewrite Hy in IN. now apply roots_nz. }
   apply min_Cmod_list_spec, Forall_forall.
   intros y. rewrite in_map_iff. intros (z & <- & IN).
   red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
   rewrite Cmod_inv. eapply Rle_lt_trans; eauto. rewrite <- Rinv_1.
   apply Rinv_lt_contravar; lra.
Qed.

Lemma gps_eqn n : gps n = CPS_mult fps (PS_poly [1;-root]) n.
Proof.
 apply CPowerSeries_coef_ext.
 - eapply Rbar.Rbar_lt_trans; [|apply gps_radius; trivial]. simpl. lra.
 - eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
   rewrite PS_poly_radius.
   apply Rbar.Rbar_min_case; [|simpl; trivial].
   eapply Rbar.Rbar_lt_le_trans; [|apply fps_radius; trivial]. simpl; lra'.
 - assert (Hr : 0 < /root) by lra'.
   exists (mkposreal _ Hr). intros y Hy.
   change (Rabs (y-R0) < /root) in Hy. rewrite Rminus_0_r in Hy.
   rewrite <- Cmod_R in Hy.
   rewrite CPowerSeries_mult.
   2:{ eapply Rbar.Rbar_lt_le_trans; [|apply fps_radius]; trivial. }
   2:{ now rewrite PS_poly_radius. }
   rewrite (CPowerSeries_unique _ _ _ (PS_poly_ok _ _)).
   rewrite (CPowerSeries_unique _ _ _ (fps_ok _ Hy)).
   assert (Hy' : Cmod y <= 1).
   { apply Rle_trans with (/root)%R; try lra. rewrite <- Rinv_1.
     red in Hroots. apply Rinv_le_contravar; lra. }
   rewrite (CPowerSeries_unique _ _ _ (gps_ok _ Hy')).
   rewrite cons_eval, Pconst_eval. rewrite g_f. ring.
   intros H. rewrite H in Hy. rewrite <- RtoC_inv, Cmod_R in Hy.
   generalize (Rle_abs (/root)); lra.
Qed.

Lemma gps_square : ex_series (fun n => (gps n)^2).
Proof.
 apply ex_series_Cmod.
 eapply ex_series_ext.
 { intros n. unfold "∘". symmetry. now rewrite Cmod_pow. }
 apply ex_series_square. rewrite <- ex_pseries_1. apply CV_radius_inside.
 unfold "∘".
 erewrite CV_radius_ext.
 2:{ intros n. now rewrite Rabs_pos_eq by apply Cmod_ge_0. }
 change (fun n => Cmod (gps n)) with (Cmod ∘ gps).
 rewrite <- C_CV_radius_alt. rewrite Rabs_pos_eq by lra.
 apply gps_radius.
Qed.

Lemma One_aux : 1 + root^2 = CSeries (fun n => (gps n)^2).
Proof.
 rewrite <- SecondRoot.Mu_series_square with (g:=g).
 2:{ rewrite <- ex_pseries_1. apply CV_radius_inside.
     rewrite <- C_CV_radius_alt. rewrite Rabs_pos_eq by lra.
     apply gps_radius. }
 2:{ intros z Hz. symmetry. apply CPowerSeries_unique, gps_ok. lra. }
 symmetry. unfold SecondRoot.Mu.
 rewrite (RInt_ext (V:=C_CNM))
  with (g := fun t => (1 - root * Cexp t)*(1 - root * Cexp (-t))).
 2:{ intros t _. rewrite !g_f.
     2:{ intros E. apply (f_equal Cmod) in E. rewrite Cmod_Cexp in E.
         rewrite Cmod_inv, Cmod_R, Rabs_pos_eq in E by lra'.
         apply (f_equal Rinv) in E. rewrite Rinv_1, Rinv_inv in E.
         red in Hroots; lra. }
     2:{ intros E. apply (f_equal Cmod) in E. rewrite Cmod_Cexp in E.
         rewrite Cmod_inv, Cmod_R, Rabs_pos_eq in E; lra'. }
     rewrite (Cmult_comm _ (f (Cexp (-t)))).
     rewrite !Cmult_assoc. f_equal.
     rewrite <- Cmult_assoc. rewrite <- (Cmult_1_r (1 - _)) at 2. f_equal.
     rewrite Cexp_neg. apply ff.
     { rewrite Hcoefs. rewrite <- linfactors_roots.
       intros [E|IN].
       - apply (f_equal Cmod) in E. rewrite Cmod_Cexp in E.
         rewrite Cmod_R, Rabs_pos_eq in E; lra'.
       - red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
         rewrite Cmod_Cexp in IN; lra. }
     { rewrite Hcoefs. rewrite <- linfactors_roots, <- Cexp_neg.
       intros [E|IN].
       - apply (f_equal Cmod) in E. rewrite Cmod_Cexp in E.
         rewrite Cmod_R, Rabs_pos_eq in E; lra'.
       - red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
         rewrite Cmod_Cexp in IN; lra. }
     { apply Cexp_nonzero. }}
 rewrite (RInt_ext (V:=C_CNM))
  with (g := fun t => (1 + root ^2) - root * (Cexp t - - Cexp (-t))).
 2:{ intros t _. fixeq C. ring_simplify.
     rewrite <- (Cmult_assoc _ (Cexp _) (Cexp _)).
     rewrite Cexp_mul_neg_r. ring. }
 rewrite CInt_minus.
 2:{ apply (ex_RInt_continuous (V:=C_CNM)); intros x _.
     apply continuous_const. }
 2:{ apply (ex_RInt_continuous (V:=C_CNM)); intros x _.
     apply continuous_Cmult. apply continuous_const.
     apply (continuous_plus (V:=C_NM)). apply continuous_Cexp.
     apply (continuous_opp (V:=C_NM)). apply (continuous_opp (V:=C_NM)).
     apply continuous_comp; trivial.
     apply (continuous_opp (V:=R_NM)), continuous_id.
     apply continuous_Cexp. }
 rewrite CInt_const.
 rewrite !CInt_scal.
 2:{ apply (ex_RInt_continuous (V:=C_CNM)); intros x _.
     apply (continuous_plus (V:=C_NM)). apply continuous_Cexp.
     apply (continuous_opp (V:=C_NM)). apply (continuous_opp (V:=C_NM)).
     apply continuous_comp; trivial.
     apply (continuous_opp (V:=R_NM)), continuous_id.
     apply continuous_Cexp. }
 replace (CInt _ _ _) with (0-0).
 rtoc. field. intros [=E]. now apply PI_neq0.
 symmetry.
 rewrite CInt_minus.
 2:{ apply (ex_RInt_continuous (V:=C_CNM)); intros x _.
     apply continuous_Cexp. }
 2:{ apply (ex_RInt_continuous (V:=C_CNM)); intros x _.
     apply (continuous_opp (V:=C_NM)).
     apply continuous_comp; trivial.
     apply (continuous_opp (V:=R_NM)), continuous_id.
     apply continuous_Cexp. }
 f_equal; apply is_CInt_unique.
 - generalize (is_CInt_Cexp 1 lia). apply is_RInt_ext.
   intros x _. f_equal. now rewrite Rmult_1_l.
 - apply (is_RInt_comp_opp (V:=C_NM)).
   rewrite Ropp_0, Ropp_mult_distr_l.
   generalize (is_CInt_Cexp' 1 lia). apply is_RInt_ext.
   intros x _. f_equal. now rewrite Rmult_1_l.
Qed.

Lemma gps_0 : gps 0 = fps 0.
Proof.
 rewrite gps_eqn.
 unfold CPS_mult. rewrite <- big_sum_sum_n. unfold PS_poly, coef. simpl.
 ring.
Qed.

Lemma gps_S n : gps (S n) = fps (S n) - root * fps n.
Proof.
 rewrite gps_eqn.
 unfold CPS_mult. rewrite <- big_sum_sum_n.
 cbn -[Nat.sub PS_poly].
 rewrite big_sum_0_bounded.
 2:{ intros x Hx. unfold PS_poly, coef. rewrite nth_overflow.
     simpl. ring. simpl length. lia. }
 replace (S n-n)%nat with 1%nat by lia.
 replace (S n-S n)%nat with 0%nat by lia.
 unfold PS_poly, coef; simpl. ring.
Qed.

Lemma One :
  1 + root^2 = (fps 0)^2 + CSeries (fun n => (fps (S n) - root * fps n)^2).
Proof.
 rewrite One_aux. rewrite CSeries_shift by apply gps_square.
 f_equal.
 - now rewrite gps_0.
 - unfold "∘". apply CSeries_ext. intros n. f_equal. apply gps_S.
Qed.

Lemma fps_0 : fps 0 = Z.abs (nth 0 coefs Z0).
Proof.
 generalize (fps_eqn 0).
 unfold CPS_mult, PS_poly. rewrite Pscale_coef, sum_O, reciprocal_coef by lia.
 rewrite Nat.sub_0_r, <- topcoef_alt.
 rewrite Hcoefs at 1. rewrite linfactors_monic, Cmult_1_r.
 intros ->. rewrite coef_Zpoly.
 rewrite <- RtoC_mult, <- mult_IZR. f_equal. f_equal. lia.
Qed.

Lemma coefs0_nz : nth 0 coefs Z0 <> Z0.
Proof.
 intros E.
 apply roots_nz'. rewrite linfactors_roots, <- Hcoefs. red.
 now rewrite Peval_0, coef_Zpoly, E.
Qed.

Lemma Integer_intpart r : Integer r -> r = Int_part r.
Proof.
 rewrite Integer_alt. intros (z & ->). now rewrite Int_part_IZR.
Qed.

Lemma CInteger_intpart c : CInteger c -> c = Int_part (Re c).
Proof.
 rewrite CInteger_alt. intros (z & ->).
 now rewrite re_RtoC, Int_part_IZR.
Qed.

Definition fps' : nat -> Z := fun n => Int_part (Re (fps n)).

Lemma fps_eqn' n : fps n = IZR (fps' n).
Proof.
 unfold fps'. apply CInteger_intpart. apply fps_CInteger.
Qed.

Lemma ex_series_diff_f' :
  ex_series (fun n => (fps' (S n) - root * fps' n) ^ 2)%R.
Proof.
 assert (E := gps_square).
 apply ex_series_shift in E. unfold "∘" in E.
 eapply ex_series_ext in E.
 2:{ intros n. rewrite gps_S, 2 fps_eqn'. ctor. reflexivity. }
 apply ex_series_RtoC, E.
Qed.

Lemma One' :
 (1 + root^2 =
  (fps' 0)^2 + Series (fun n => (fps' (S n) - root * fps' n)^2))%R.
Proof.
 apply RtoC_inj. rtoc. rewrite One.
 rewrite fps_eqn'. f_equal.
 rewrite <- CSeries_RtoC. apply CSeries_ext.
 { intros n. unfold "∘". rewrite 2 fps_eqn'. now ctor. }
 apply ex_series_diff_f'.
Qed.

Section fps_eventually_zero.

Hypothesis fps1z : fps 1 = 0.

Lemma fps1z_const : forall n, fps n = PS_poly [1] n.
Proof.
 assert (LE0 : 1 <= fps' 0).
 { assert (E := fps_0). rewrite fps_eqn' in E. injection E as E.
   rewrite E. apply IZR_le. generalize coefs0_nz; lia. }
 assert (LE0' : 1 <= (fps' 0)^2).
 { apply Rsqr_incr_1 in LE0; try lra. now rewrite Rsqr_1, Rsqr_pow2 in LE0. }
 assert (E := One').
 set (d := fun n => _) in E.
 rewrite Series_incr_1 in E by apply ex_series_diff_f'.
 rewrite fps_eqn' in fps1z. injection fps1z as fps1z.
 unfold d at 1 in E. rewrite fps1z in E.
 replace ((0-_)^2)%R with ((fps' 0)^2*root^2)%R in E by ring.
 assert (0 <= Series (fun n => d (S n))).
 { replace 0%R with (Series (fun _ => 0%R)).
   2:{ apply is_series_unique. apply is_series_R0. }
   apply Series_le.
   - intros m. split; try lra.
     unfold d. rewrite <- Rsqr_pow2. apply Rle_0_sqr.
   - assert (H := ex_series_diff_f').
     rewrite <- ex_series_RtoC in H |- *.
     now rewrite ex_series_shift in H. }
 assert (E0 : (fps' 0 = 1)%Z).
 { apply eq_IZR.
   rewrite <- (Rabs_pos_eq (fps' 0)) by lra.
   rewrite <- (Rabs_pos_eq 1) by lra.
   apply Rsqr_eq_abs_0. rewrite Rsqr_1, Rsqr_pow2. red in Hroots; nra. }
 assert (E' : Series (fun n => d (S n)) = 0%R) by (red in Hroots; nra).
 clear E H.
 assert (D : forall n, d (S n) = 0%R).
 { apply is_series_null.
   - rewrite <- E'. apply Series_correct.
     assert (H := ex_series_diff_f').
     rewrite <- ex_series_RtoC in H |- *.
     now rewrite ex_series_shift in H.
   - intros m. unfold d. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
 unfold PS_poly, coef.
 induction n.
 - simpl. now rewrite fps_eqn', E0.
 - rewrite nth_overflow by (simpl; lia).
   destruct n.
   + now rewrite fps_eqn', fps1z.
   + specialize (D n). unfold d in D.
     rewrite nth_overflow, fps_eqn' in IHn by (simpl; lia).
     injection IHn as IHn. rewrite IHn in D.
     rewrite fps_eqn'. f_equal. nra.
Qed.

Lemma fps1z_p_eqn : Peq ([RtoC (IZR sgn)] *, Pcoef) (reciprocal Pcoef).
Proof.
 apply Peq_via_coef. intros n.
 change (coef n ([RtoC sgn] *, Pcoef)) with (PS_poly ([RtoC sgn] *, Pcoef) n).
 rewrite <- fps_eqn.
 rewrite <- (Pmult_1_l (reciprocal Pcoef)) at 2.
 change (coef n ([1] *, reciprocal Pcoef))
   with (PS_poly ([1] *, reciprocal Pcoef) n).
 rewrite <- CPS_mult_poly.
 unfold CPS_mult. apply sum_n_ext. intros m. now rewrite fps1z_const.
Qed.

Lemma fps1z_p_eqn' : exists c, c<>0 /\ Peq Pcoef ([c] *, reciprocal Pcoef).
Proof.
 exists (IZR sgn). split.
 - intros [=H]. apply eq_IZR in H.
   rewrite Z.sgn_null_iff in H. revert H. apply coefs0_nz.
 - rewrite <- fps1z_p_eqn, <- Pmult_assoc.
   replace ([_]*,[_]) with [1]. symmetry; apply Pmult_1_l.
   simpl. f_equal. rewrite Cplus_0_r, <- RtoC_mult, <- mult_IZR.
   f_equal. f_equal. unfold sgn.
   generalize coefs0_nz. now destruct nth.
Qed.

Lemma fps1z_roots_carac r : In r roots -> r = /root.
Proof.
 destruct fps1z_p_eqn' as (c & Hc & E).
 intros Hr. destruct Hroots as (H1 & _ & H2). rewrite Forall_forall in H2.
 assert (Hr' : Root r Pcoef).
 { rewrite Hcoefs, <- linfactors_roots. now right. }
 rewrite E in Hr'. red in Hr'.
 rewrite Pmult_eval, Pconst_eval in Hr'. apply Cmult_integral in Hr'.
 destruct Hr' as [Hr'|Hr']; [easy|].
 apply reciprocal_root in Hr'.
 2:{ apply Cmod_gt_0. now apply H2. }
 rewrite Hcoefs in Hr'. apply linfactors_roots in Hr'.
 destruct Hr' as [Hr'|Hr'].
 - now rewrite Hr', Cinv_inv.
 - apply H2 in Hr, Hr'. destruct Hr' as (H3,H4).
   rewrite Cmod_inv in H4. rewrite <- Rinv_1 in H4.
   apply Rcomplements.Rinv_lt_cancel in H4; lra.
Qed.

Lemma fps1z_degree_0 : degree Pcoef = 0%nat -> False.
Proof.
 rewrite Hcoefs, linfactors_degree. discriminate.
Qed.

Lemma fps1z_degree_1 : degree Pcoef = 1%nat -> 2 <= root.
Proof.
 intros D.
 rewrite Hcoefs, linfactors_degree in D. simpl in D.
 injection D as D. rewrite length_zero_iff_nil in D.
 rewrite D  in Hcoefs. simpl in Hcoefs.
 rewrite !Cmult_1_l, Cplus_0_r in Hcoefs.
 assert (H : Integer root).
 { rewrite Integer_alt. exists (Z.opp (nth 0 coefs Z0)).
   rewrite opp_IZR. apply RtoC_inj. rewrite RtoC_opp.
   change (RtoC (IZR (nth 0 coefs Z0))) with ((RtoC∘IZR) (nth 0 coefs Z0)).
   rewrite <- map_nth. change (map _ coefs) with (Zpoly coefs).
   change (nth _ _ _) with (coef 0 (Zpoly coefs)).
   rewrite Hcoefs. unfold coef. simpl. now rewrite Copp_involutive. }
 red in Hroots. rewrite Integer_alt in H. destruct H as (n & H).
 rewrite H.
 apply IZR_le. assert (1 < n)%Z; try lia. apply lt_IZR. rewrite <- H.
 apply Hroots.
Qed.

Lemma fps1z_degree_2 : degree Pcoef = 2%nat -> 2 < root.
Proof.
 intros D.
 assert (R : Root root Pcoef).
 { rewrite Hcoefs. apply linfactors_roots. now left. }
 replace roots with [/root] in *.
 2:{ rewrite Hcoefs, linfactors_degree in D. simpl in D.
     injection D as D. assert (H := fps1z_roots_carac).
     destruct roots as [|x l] eqn:E. discriminate D.
     simpl in D. injection D as D. rewrite length_zero_iff_nil in D.
     subst l. f_equal. symmetry. apply H. now left. }
 simpl in Hcoefs. rewrite !Cmult_1_l, Cmult_1_r, !Cplus_0_r in *.
 assert (INT : Integer (root+/root)).
 { rewrite Integer_alt. exists (Z.opp (nth 1 coefs Z0)).
   rewrite opp_IZR. apply RtoC_inj. rewrite RtoC_opp.
   change (RtoC (IZR (nth 1 coefs Z0))) with ((RtoC∘IZR) (nth 1 coefs Z0)).
   rewrite <- map_nth. change (map _ coefs) with (Zpoly coefs).
   change (nth _ _ _) with (coef 1 (Zpoly coefs)).
   rewrite Hcoefs. unfold coef. simpl. rtoc. ring. }
 assert (1 < root + /root).
 { destruct Hroots as (LT & _). generalize (Rinv_0_lt_compat root). lra. }
 assert (N : root + /root <> 2).
 { intros E.
   replace (-/root*-root) with 1 in Hcoefs.
   2:{ field. destruct Hroots as (LT & _). intros [= H']. lra. }
   rewrite <- Copp_plus_distr, Cplus_comm, E in Hcoefs.
   assert (Hp : Peq Pcoef (linfactors [1;1])).
   { rewrite Hcoefs. simpl. apply eq_Peq.
     f_equal. ring. f_equal. ring. f_equal. ring. }
   rewrite Hp in R. apply linfactors_roots in R. simpl in R.
   destruct Hroots as (LT & _). destruct R as [[= R]|[[= R]|[ ]]]; lra. }
 assert (3 <= root + /root).
 { rewrite Integer_alt in INT. destruct INT as (n & Hn).
   rewrite Hn in H |- *. apply lt_IZR in H. apply IZR_le.
   rewrite <- RtoC_inv, <- RtoC_plus, Hn in N.
   assert (n <> 2%Z). { contradict N. now subst. }
   lia. }
 destruct (Rle_lt_dec root 2); try lra.
 destruct Hroots as (LT & _).
 assert (/root < 1). { rewrite <- Rinv_1. apply Rinv_lt_contravar; lra. }
 lra.
Qed.

Lemma fps1z_degree_3 : (3 <= degree Pcoef)%nat -> False.
Proof.
 intros D.
 assert (E := Peval_0 Pcoef).
 rewrite Hcoefs in E at 1.
 rewrite Peval_linfactors in E.
 unfold coef, Zpoly in E.
 change 0 with ((RtoC∘IZR) Z0) in E at 2.
 rewrite map_nth in E.
 assert (R : roots = repeat (/root) (degree Pcoef - 1)).
 { replace (degree Pcoef - 1)%nat with (length roots).
   2:{ unfold Pcoef. rewrite Hcoefs. rewrite linfactors_degree. simpl. lia. }
   apply Forall_eq_repeat. apply Forall_forall.
   intros r Hr. symmetry. now apply fps1z_roots_carac. }
 set (d := (degree Pcoef - 1)%nat) in *.
 set (n := nth 0 coefs Z0) in *. unfold "∘" in E.
 replace d with (S (d-1)) in R by lia.
 rewrite R in E. simpl in E.
 rewrite Cmult_assoc in E.
 replace ((0-_)*(0-_)) with 1 in E.
 2:{ field. intros [=H]. destruct Hroots. lra. }
 rewrite Cmult_1_l in E.
 apply (f_equal Cmod) in E.
 rewrite G_big_mult_mod, map_map, map_repeat in E.
 replace (Cmod (0-_)) with (/root)%R in E.
 2:{ unfold Cminus. rewrite Cplus_0_l, Cmod_opp, <- RtoC_inv, Cmod_R.
     symmetry. apply Rabs_pos_eq. apply Rlt_le.
     apply Rinv_0_lt_compat. lra'. }
 rewrite Cmod_R, Rabs_Zabs in E.
 set (g := G_big_mult _) in *.
 assert (LT : 0 < g < 1).
 { apply G_big_mult_small. intros x Hx. apply repeat_spec in Hx.
   - rewrite Hx. split.
     + apply Rinv_0_lt_compat. lra'.
     + rewrite <- Rinv_1. apply Rinv_lt_contravar; lra'.
   - rewrite <- length_zero_iff_nil.
     rewrite repeat_length. lia. }
 rewrite E in LT. destruct LT as (LT1,LT2).
 apply lt_IZR in LT1, LT2. lia.
Qed.

Lemma fps1nz : False.
Proof.
 assert (H0 := fps1z_degree_0).
 assert (H1 := fps1z_degree_1).
 assert (H2 := fps1z_degree_2).
 assert (H3 := fps1z_degree_3).
 destruct (degree Pcoef) as [|[|[|d]]].
 - now apply H0.
 - specialize (H1 eq_refl). nra.
 - specialize (H2 eq_refl). nra.
 - apply H3; lia.
Qed.

End fps_eventually_zero.

Lemma Two n : (fps' (n-1) <= fps' n)%Z.
Proof.
 induction n as [[|n] IH] using lt_wf_ind; try easy.
 simpl. rewrite Nat.sub_0_r.
 assert (LE : forall m, (m <= n)%nat -> (1 <= fps' m)%Z).
 { induction m.
   - intros _. unfold fps'. rewrite fps_0, re_RtoC, Int_part_IZR.
     generalize coefs0_nz.
     destruct (nth 0 coefs Z0) as [|x|x]; lia.
   - intros Hm. rewrite IHm by lia.
     replace m with (S m - 1)%nat at 1 by lia. apply IH. lia. }
 assert (LE0 : (1 <= fps' O)%Z) by (apply LE; lia).
 specialize (LE n lia).
 apply Z.le_ngt. intros LT.
 clear IH.
 assert (E := One').
 set (d := fun n => _) in E.
 assert (EX : ex_series (fun m => d (m+S n)%nat)).
 { rewrite <- ex_series_RtoC. unfold "∘".
   rewrite <- (ex_series_shiftn (RtoC∘d) (S n)).
   rewrite ex_series_RtoC. apply ex_series_diff_f'. }
 assert (E' : (Series d = big_sum d (S n) + Series (fun m => d (m+S n)%nat))%R).
 { apply RtoC_inj. rtoc.
   rewrite big_sum_RtoC.
   rewrite <- 2 CSeries_RtoC; trivial using ex_series_diff_f'.
   rewrite CSeries_shiftn with (N:=S n); try easy.
   apply ex_series_RtoC. apply ex_series_diff_f'. }
 rewrite <- big_sum_extend_r in E'. change Gplus with Rplus in E'.
 assert (0 <= big_sum d n).
 { apply Rsum_ge_0. intros i _. unfold d. rewrite <- Rsqr_pow2.
   apply Rle_0_sqr. }
 assert (0 <= Series (fun m => d (m+S n)%nat)).
 { replace 0%R with (Series (fun _ => 0%R)).
   2:{ apply is_series_unique. apply is_series_R0. }
   apply Series_le.
   - intros m. split; try lra.
     unfold d. rewrite <- Rsqr_pow2. apply Rle_0_sqr.
   - rewrite <- ex_series_RtoC. unfold "∘".
     rewrite <- (ex_series_shiftn (RtoC∘d) (S n)).
     rewrite ex_series_RtoC. apply ex_series_diff_f'. }
 assert (D : d n <= root^2).
 { apply Rplus_le_reg_l with 1%R. rewrite E, E'.
   apply IZR_le, Rsqr_incr_1 in LE0; try lra.
   rewrite Rsqr_1, Rsqr_pow2 in LE0.
   lra. }
 destruct (Z.le_gt_cases 0 (fps' (S n))) as [HSn|HSn].
 2:{ apply IZR_lt in HSn.
     unfold d in D. rewrite <- !Rsqr_pow2 in D.
     apply Rsqr_le_abs_0 in D.
     apply IZR_le in LE.
     rewrite Rabs_left in D by (red in Hroots; nra).
     rewrite Rabs_right in D by lra'.
     assert (LT' : root * IZR (fps' n) < root * 1) by lra.
     apply Rmult_lt_reg_l in LT'; lra'. }
 destruct (Z.eq_dec 0 (fps' (S n))) as [HSn'|HSn'].
 2:{ apply (Rlt_irrefl (root^2)).
     eapply Rlt_le_trans; [|apply D].
     apply Rle_lt_trans with ((IZR (fps' n) - IZR (fps' (S n)))^2*root^2)%R.
     - rewrite <- (Rmult_1_l (root^2)) at 1.
       apply Rmult_le_compat_r. red in Hroots. nra.
       rewrite <- Rsqr_pow2, <- Rsqr_1. apply Rsqr_incr_1; try lra.
       + apply Zlt_le_succ, IZR_le in LT. rewrite succ_IZR in LT. lra.
       + apply IZR_lt in LT. lra.
     - unfold d. rewrite <- !Rsqr_pow2, <- Rsqr_mult.
       rewrite (Rsqr_neg (_-_)), Ropp_minus_distr, Rmult_comm.
       apply Rsqr_incrst_1.
       + apply Rminus_lt_0. ring_simplify.
         replace (_-_)%R with ((root-1)*IZR (fps' (S n)))%R by ring.
         apply Rmult_lt_0_compat. lra'. apply IZR_lt. lia.
       + apply Rmult_le_pos. lra'. apply IZR_lt in LT; lra.
       + replace (_-_)%R with
         (root*(IZR (fps' n) - IZR (fps' (S n))) +
          ((root-1)*IZR (fps' (S n))))%R by ring.
         apply Rplus_le_le_0_compat.
         * apply Rmult_le_pos. lra'. apply IZR_lt in LT; lra.
         * apply Rmult_le_pos. lra'. apply IZR_le. lia. }
 clear HSn.
 assert (Hn : fps' n = 1%Z).
 { apply Z.le_antisymm; trivial. apply le_IZR.
   unfold d in D. rewrite <- HSn' in D.
   rewrite <- !Rsqr_pow2 in D. unfold Rminus in D. rewrite Rplus_0_l in D.
   rewrite <- Rsqr_neg in D. rewrite Rsqr_mult in D.
   rewrite <- (Rmult_1_r (Rsqr root)) in D at 2.
   apply Rmult_le_reg_l in D. 2:{ apply Rlt_0_sqr. lra'. }
   rewrite <- Rsqr_1 in D.
   apply Rsqr_incr_0; trivial. apply IZR_le; lia. lra. }
 assert (D' : (d n = root^2)%R).
 { unfold d. rewrite <- HSn', Hn. ring. }
 assert (E0 : big_sum d n = 0%R).
 { apply Rle_antisym; trivial.
   apply IZR_le in LE0. apply Rsqr_incr_1 in LE0; try lra.
   rewrite Rsqr_1, Rsqr_pow2 in LE0. lra. }
 clear E E' H0 D D' EX.
 destruct n as [|n].
 - apply fps1nz. now rewrite fps_eqn', <- HSn'.
 - rewrite <- big_sum_extend_r in E0. change Gplus with Rplus in E0.
   assert (0 <= big_sum d n).
   { apply Rsum_ge_0. intros i _. unfold d. rewrite <- Rsqr_pow2.
     apply Rle_0_sqr. }
   assert (0 <= d n).
   { unfold d. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
   assert (D : d n = 0%R) by lra.
   unfold d in D. rewrite Hn, <- Rsqr_pow2 in D. apply Rsqr_eq_0 in D.
   assert (Hn' : (IZR (fps' n) = /root)%R).
   { apply Rmult_eq_reg_l with root. 2:{ lra'. }
     rewrite Rinv_r; try lra. lra'. }
   assert ((0 < fps' n < 1)%Z); try lia.
   { split; apply lt_IZR; rewrite Hn'; red in Hroots; nra. }
Qed.

Definition polypows (r:nat) (c:C) := map (Cpow c) (seq 0 r).

Lemma polypows_eqn (r:nat) (c:C) :
  Peq ((polypows r c) *, [1;-c]) ([1] +, monom (-c^r) r).
Proof.
 induction r.
 - simpl. replace (1+-(1)) with 0 by ring. symmetry. apply C0_Peq_nil.
 - unfold polypows. simpl map. rewrite <- seq_shift, map_map.
   assert (E : Peq (map (fun k => c^S k) (seq 0 r)) ([c] *, polypows r c)).
   { rewrite Pscale_alt. unfold polypows. rewrite map_map.
     apply eq_Peq. now apply map_ext. }
   rewrite E. clear E.
   cbn -[Pplus monom Cpow]. rewrite !Cmult_1_l.
   rewrite <- Pscale_alt.
   rewrite C0_Peq_nil, Pplus_0_r.
   rewrite Pmult_assoc, IHr.
   rewrite Pmult_plus_distr_l, Pmult_1_r.
   rewrite monom_scale, (monom_scale (-c^S r) (S r)).
   rewrite monom_S.
   rewrite <- Pmult_assoc.
   replace ([c] *, [-c^r]) with [-c^S r]. 2:{ simpl. f_equal. ring. }
   rewrite (Pmult_comm _ (0::_)), cons_0_mult, (Pmult_comm _ (monom _ _)).
   set (q := monom _ _ *, _).
   rewrite <- cons_simplify.
   change (Peq (1+0 :: ([-c] +, ([c]+,q))) (1::q)).
   rewrite <- Pplus_assoc.
   replace ([-c]+,[c]) with [0]. 2:{ simpl. f_equal. ring. }
   now rewrite C0_Peq_nil, Cplus_0_r.
Qed.

(* MOVE *)
Definition PS_pow r := (Cpow r).

Lemma is_CPowerSeries_pow r x : r<>0 -> Cmod (r*x) < 1 ->
 is_CPowerSeries (PS_pow r) x (/(1-r*x)).
Proof.
 intros Hr Hx. unfold PS_pow.
 apply is_lim_Cseq_ext with (fun n => (1 - (r*x)^S n)/(1-r*x)).
 { intros n.
   apply Cmult_eq_reg_r with (1-r*x).
   2:{ intros E. apply Ceq_minus in E. rewrite <- E, Cmod_1 in Hx. lra. }
   unfold Cdiv. rewrite <- Cmult_assoc, Cinv_l, Cmult_1_r.
   2:{ intros E. apply Ceq_minus in E. rewrite <- E, Cmod_1 in Hx. lra. }
   erewrite sum_n_ext.
   2:{ intros m. symmetry. apply Cpow_mult_l. }
   rewrite (Cmult_comm (sum_n _ _)). symmetry. apply sum_n_Cpow. }
 unfold Cdiv. rewrite <- (Cmult_1_l (/(1-r*x))) at 1.
 apply is_lim_Cseq_mult; [|apply is_lim_Cseq_const].
 replace 1 with (1-0) at 1 by lca.
 apply is_lim_Cseq_minus. apply is_lim_Cseq_const.
 apply is_lim_Cseq_0_Cmod.
 apply is_lim_seq_ext with (fun n => (Cmod (r*x))^S n)%R.
 - intros n. unfold compose. now rewrite Cmod_pow.
 - rewrite <- is_lim_seq_incr_1. apply is_lim_seq_geom.
   now rewrite Rabs_right by apply Rle_ge, Cmod_ge_0.
Qed.

Lemma C_CV_radius_pow (r:C) : r<>0 -> C_CV_radius (PS_pow r) = (/Cmod r)%R.
Proof.
 intros Hr.
 rewrite C_CV_radius_alt.
 apply CV_radius_finite_DAlembert.
 - intros n. unfold "∘", PS_geom.
   rewrite Cmod_pow. apply pow_nonzero.
   rewrite (Cmod_gt_0 r) in Hr. lra.
 - now apply Cmod_gt_0.
 - unfold "∘", PS_pow.
   eapply is_lim_seq_ext; try apply is_lim_seq_const.
   intros n; simpl. rewrite Cmod_mult.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_r.
   + now rewrite Rmult_1_r, Rabs_pos_eq by apply Cmod_ge_0.
   + rewrite Cmod_pow. apply pow_nonzero.
     rewrite (Cmod_gt_0 r) in Hr. lra.
Qed.

Definition PS_dilate (a:nat->C) (k:nat) :=
 fun n => if (n mod k =? 0)%nat then a (n/k)%nat else 0.

Lemma sum_PS_dilate (a:nat->C) (k:nat) x n :
 k<>O ->
 sum_n (fun m => PS_dilate a k m * x^m) n
 = sum_n (fun m => a m * (x^k)^m) (n/k).
Proof.
 intros Hk.
 induction n.
 - replace (0/k)%nat with 0%nat. 2:{ symmetry. now apply Nat.div_0_l. }
   rewrite !sum_O. unfold PS_dilate. simpl.
   rewrite Nat.mod_0_l, Nat.div_0_l; trivial.
 - rewrite sum_Sn. change plus with Cplus.
   rewrite IHn. unfold PS_dilate.
   case Nat.eqb_spec; intros H.
   + assert (E := Nat.div_mod_eq (S n) k). rewrite H, Nat.add_0_r in E.
     assert (E' := Nat.div_mod_eq n k).
     assert (H' : (n mod k = k-1)%nat).
     { apply Nat.le_antisymm.
       - generalize (Nat.mod_upper_bound n k Hk); lia.
       - apply Nat.le_ngt. intros LT.
         assert (S (n mod k) = (S n) mod k); try lia.
         { apply Nat.mod_unique with (q:=(n/k)%nat); lia. }}
     rewrite H' in E'. apply (f_equal S) in E'.
     replace (S (_+_)) with (k * (S (n/k)))%nat in E' by lia.
     replace (S n / k)%nat with (S (n/k)).
     2:{ apply Nat.div_unique_exact; try lia. }
     rewrite sum_Sn. change plus with Cplus. f_equal. f_equal.
     rewrite <- Cpow_mult_r. f_equal. apply E'.
   + rewrite Cmult_0_l, Cplus_0_r.
     assert (E := Nat.div_mod_eq (S n) k).
     assert (E' := Nat.div_mod_eq n k).
     apply (f_equal S) in E'. rewrite <- Nat.add_succ_r in E'.
     assert (H' : (S (n mod k) = S n mod k)%nat).
     { destruct (Nat.eqb_spec (n mod k) (k-1)) as [H'|H'].
       - rewrite H' in E'.
         replace (_+_)%nat with (k*(S (n/k)))%nat in E' by lia.
         assert (S n mod k = 0)%nat; try lia.
         symmetry. apply Nat.mod_unique with (q:=S (n/k)); lia.
       - apply Nat.mod_unique with (q:=(n/k)%nat); try lia.
         generalize (Nat.mod_upper_bound n k Hk); lia. }
     rewrite H' in E'. f_equal.
     eapply Nat.div_unique; eauto. now apply Nat.mod_upper_bound.
Qed.

Lemma is_CPowerSeries_dilate a k x l : k<>O ->
  is_CPowerSeries a (x^k) l <-> is_CPowerSeries (PS_dilate a k) x l.
Proof.
 intros Hk. unfold is_CPowerSeries.
 rewrite !is_lim_Cseq_alt. split.
 - intros H eps. destruct (H eps) as (N & HN). exists (N*k)%nat.
   intros n Hn. rewrite sum_PS_dilate by trivial. apply HN.
   apply Nat.div_le_lower_bound; lia.
 - intros H eps. destruct (H eps) as (N & HN). exists N.
   intros n Hn.
   assert (Hn' : (N <= n*k)%nat).
   { replace k with (1+(k-1))%nat by lia.
     rewrite Nat.mul_add_distr_l. (* ?! lia should work from here... *)
     rewrite Nat.mul_1_r. apply Nat.le_trans with n; trivial.
     apply Nat.le_add_r. }
   specialize (HN (n*k)%nat Hn').
   rewrite sum_PS_dilate in HN by trivial.
   rewrite Nat.div_mul in HN by trivial. apply HN.
Qed.

Definition nroot (x:R) (n:nat) := exp (ln x / n).

Lemma pow_via_exp x n : 0<x -> (x^n = exp (n * ln x))%R.
Proof.
 intros Hx.
 induction n.
 - simpl. now rewrite Rmult_0_l, exp_0.
 - rewrite <- Nat.add_1_r at 2. rewrite plus_INR. simpl.
   rewrite IHn. rewrite <- (exp_ln x) at 1 by trivial.
   rewrite <- exp_plus. f_equal. lra.
Qed.

Lemma exp_pow x n : (exp x ^ n)%R = exp (x*n).
Proof.
 rewrite pow_via_exp, ln_exp by apply exp_pos. f_equal. ring.
Qed.

Lemma nroot_pow x n : n<>O -> 0 < x -> ((nroot x n)^n = x)%R.
Proof.
 intros Hn Hx. unfold nroot. rewrite exp_pow.
 rewrite <- (exp_ln x) at 2 by trivial. f_equal. field.
 contradict Hn. now apply INR_eq.
Qed.

Lemma pow_inj_l n x y : n<>O -> 0 <= x -> 0 <= y -> (x ^ n = y ^ n)%R -> x = y.
Proof.
 intros Hn Hx Hy H.
 apply Rle_antisym.
 - apply Rnot_lt_le. intros LT.
   apply (Rpow_lt_compat_r n) in LT; trivial. lra.
 - apply Rnot_lt_le. intros LT.
   apply (Rpow_lt_compat_r n) in LT; trivial. lra.
Qed.

Lemma Rpow_lt_reg_r n x y : 0 <= x -> 0 <= y -> x ^ n < y ^ n -> x < y.
Proof.
 intros Hx Hy.
 destruct n as [|n].
 { simpl. lra. }
 destruct (Req_dec x 0) as [Hx'|Hx'], (Req_dec y 0) as [Hy'|Hy'].
 - subst. simpl. lra.
 - lra.
 - subst. apply (pow_le x (S n)) in Hx. rewrite Rpow_0_l by easy. lra.
 - rewrite !pow_via_exp by lra.
   intros H. apply exp_lt_inv in H.
   apply Rmult_lt_reg_l in H; try apply RSpos.
   apply ln_lt_inv; lra.
Qed.

(* MOVE *)
Lemma C_CV_radius_minorant (a : nat -> C) (r:R) :
 (forall x, Cmod x < r -> ex_CPowerSeries a x) ->
 Rbar.Rbar_le r (C_CV_radius a).
Proof.
 intros H.
 apply Rbar_le_carac_via_lt.
 intros x Hx. simpl in Hx.
 destruct (Rle_lt_dec 0 x).
 - rewrite C_CV_radius_radius'.
   apply Lub_Rbar_ub. red. exists x; split.
   + rewrite Cmod_R, Rabs_pos_eq; lra.
   + apply H. rewrite Cmod_R, Rabs_pos_eq; lra.
 - apply Rbar.Rbar_le_trans with 0%R. simpl; lra.
   rewrite C_CV_radius_alt. apply CV_radius_ge_0.
Qed.

Lemma C_CV_radius_dilate a k r : k<>O ->
 Rbar.Rbar_lt (r^k)%R (C_CV_radius a) ->
 Rbar.Rbar_lt r (C_CV_radius (PS_dilate a k)).
Proof.
 intros Hk H.
 destruct (Rle_lt_dec 0 r) as [LE|LT].
 - assert (H1 : exists r1, r^k < r1 /\ Rbar.Rbar_lt r1 (C_CV_radius a)).
   { destruct (C_CV_radius a) as [ra| | ]; try easy.
     - exists ((r^k+ra)/2)%R. split; simpl in H|-*; lra.
     - exists (r^k+1)%R. split; simpl; lra. }
   assert (H2 : exists r2, r < r2 /\ Rbar.Rbar_lt (r2^k)%R (C_CV_radius a)).
   { destruct H1 as (r1 & H1 & H1').
     exists (nroot r1 k). split.
     - apply (Rpow_lt_reg_r k); trivial. apply Rlt_le, exp_pos.
       rewrite nroot_pow; trivial. apply (pow_le r k) in LE. lra.
     - rewrite nroot_pow; trivial. apply (pow_le r k) in LE. lra. }
   destruct H2 as (r2 & H2 & H2'). clear H H1.
   replace (r2^k)%R with (Cmod (r2^k)) in H2'.
   2:{ ctor. rewrite Cmod_R, Rabs_pos_eq; trivial. apply pow_le; lra. }
   apply C_CV_radius_inside in H2'. destruct H2' as (l & H2').
   rewrite is_CPowerSeries_dilate in H2' by trivial.
   rewrite C_CV_radius_radius'.
   apply Rbar.Rbar_lt_le_trans with r2; trivial.
   apply Lub_Rbar_ub. red. exists (RtoC r2). split.
   now rewrite Cmod_R, Rabs_pos_eq by lra.
   now exists l.
 - apply Rbar.Rbar_lt_le_trans with 0%R; trivial.
   rewrite C_CV_radius_alt. apply CV_radius_ge_0.
Qed.

Lemma C_CV_radius_dilate' a k r : k<>O ->
 Rbar.Rbar_le (r^k)%R (C_CV_radius a) ->
 Rbar.Rbar_le r (C_CV_radius (PS_dilate a k)).
Proof.
 intros Hk H.
 apply Rbar_le_carac_via_lt. intros r' Hr'. simpl in Hr'.
 destruct (Rle_lt_dec 0 r') as [LE|LT].
 - apply Rbar.Rbar_lt_le. apply (C_CV_radius_dilate a k r'); trivial.
   eapply Rbar.Rbar_lt_le_trans; eauto.
   simpl. apply Rpow_lt_compat_r; trivial.
 - apply Rbar.Rbar_le_trans with 0%R. simpl; lra.
   rewrite C_CV_radius_alt. apply CV_radius_ge_0.
Qed.

Definition vr (r:nat) (x:C) := (1 - root^r*x^r)/(1-x^r/root^r).

(** An expression of [vr r * f] with factorization of the pole at [/root] *)

Definition gr (r:nat) (x:C) :=
  Peval (polypows r root) x / (1 - x^r/root^r) * g x.

Lemma gr_alt (r:nat) (x:C) : x<>/root -> gr r x = vr r x * f x.
Proof.
 intros Hx.
 unfold gr, vr.
 unfold Cdiv. rewrite !(Cmult_comm _ (/_)), <- !Cmult_assoc. f_equal.
 rewrite g_f by trivial. rewrite Cmult_assoc. f_equal.
 replace (1-root*x) with (Peval [1;-root] x).
 2:{ rewrite cons_eval, Pconst_eval. ring. }
 rewrite <- Pmult_eval, polypows_eqn.
 rewrite Pplus_eval, Pconst_eval, monom_eval. ring.
Qed.

Definition grps (r:nat) :=
 CPS_mult
   (CPS_mult (PS_poly (polypows r root)) (PS_dilate (PS_pow (/root^r)) r))
   gps.

Definition grps' (r:nat) :=
 CPS_mult
   (PS_dilate (CPS_mult (PS_poly [1;-root^r]) (PS_pow (/root^r))) r)
   fps.

Lemma grps_ok (r : nat) x : r<>O -> Cmod x <= 1 ->
 is_CPowerSeries (grps r) x (gr r x).
Proof.
 intros Hr Hx. unfold gr, grps.
 set (a := PS_dilate _ _).
 assert (NZ : root^r <> 0) by (apply Cpow_nz; intros [=H]; lra').
 assert (Ha : Rbar.Rbar_lt (Cmod x) (C_CV_radius a)).
 { unfold a. apply C_CV_radius_dilate; trivial.
   rewrite C_CV_radius_pow. 2:{ now apply nonzero_div_nonzero. }
   simpl. rewrite <- Cmod_inv, Cinv_inv.
   apply Rle_lt_trans with (1^r)%R.
   - apply pow_incr. split; trivial. apply Cmod_ge_0.
   - rewrite Cmod_pow, Cmod_R, Rabs_pos_eq by lra'.
     apply Rpow_lt_compat_r; trivial; lra'. }
 apply is_CPS_mult.
 - apply is_CPS_mult; trivial using PS_poly_ok;
   try now rewrite PS_poly_radius.
   unfold a, Cdiv. rewrite Cmult_comm.
   rewrite <- is_CPowerSeries_dilate by trivial.
   apply is_CPowerSeries_pow; try now apply nonzero_div_nonzero.
   rewrite Cmod_mult, Cmod_inv, !Cmod_pow, Cmod_R, Rabs_pos_eq by lra'.
   apply Rmult_lt_reg_l with (root^r)%R.
   { apply pow_lt. lra'. }
   rewrite <- Rmult_assoc, Rinv_r, Rmult_1_r, Rmult_1_l.
   2:{ apply pow_nonzero. lra'. }
   apply Rpow_lt_compat_r; trivial. apply Cmod_ge_0. lra'.
 - now apply gps_ok.
 - eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
   rewrite PS_poly_radius.
   apply Rbar.Rbar_min_case; simpl; trivial.
 - apply Rbar.Rbar_le_lt_trans with 1%R; trivial. apply gps_radius.
Qed.

Lemma grps_radius (r : nat) : r<>O ->
  Rbar.Rbar_lt 1%R (C_CV_radius (grps r)).
Proof.
 intros Hr. unfold grps.
 set (a := PS_dilate _ _).
 assert (NZ : root^r <> 0) by (apply Cpow_nz; intros [=H]; lra').
 assert (Ha : Rbar.Rbar_lt 1%R (C_CV_radius a)).
 { unfold a. apply C_CV_radius_dilate; trivial.
   rewrite C_CV_radius_pow. 2:{ now apply nonzero_div_nonzero. }
   simpl.
   rewrite <- Cmod_inv, Cinv_inv, Cmod_pow, Cmod_R, Rabs_pos_eq by lra'.
   apply Rpow_lt_compat_r; trivial; lra'. }
 eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
 apply Rbar.Rbar_min_case; [|apply gps_radius].
 eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
 apply Rbar.Rbar_min_case; trivial. now rewrite PS_poly_radius.
Qed.

Lemma grps'_ok (r : nat) x : r<>O -> Cmod x < /root ->
 is_CPowerSeries (grps' r) x (gr r x).
Proof.
 intros Hr Hx. rewrite gr_alt.
 2:{ intros E. rewrite E in Hx.
     rewrite Cmod_inv, Cmod_R, Rabs_pos_eq in Hx; lra'. }
 unfold vr, grps'.
 set (a := PS_dilate _ _).
 assert (NZ : root^r <> 0) by (apply Cpow_nz; intros [=H]; lra').
 assert (Ha : Rbar.Rbar_lt (Cmod x) (C_CV_radius a)).
 { unfold a. apply C_CV_radius_dilate; trivial.
   eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
   rewrite PS_poly_radius, C_CV_radius_pow.
   2:{ now apply nonzero_div_nonzero. }
   apply Rbar.Rbar_min_case; simpl; trivial.
   rewrite Cmod_inv, Rinv_inv, Cmod_pow, Cmod_R, Rabs_pos_eq by lra'.
   apply Rpow_lt_compat_r; trivial; try lra'. apply Cmod_ge_0. }
 apply is_CPS_mult; trivial.
 - unfold a. rewrite <- is_CPowerSeries_dilate by trivial.
   apply is_CPS_mult.
   + replace (1-_) with (Peval [1;-root^r] (x^r)). apply PS_poly_ok.
     rewrite cons_eval, Pconst_eval. ring.
   + unfold Cdiv. rewrite Cmult_comm.
     apply is_CPowerSeries_pow; try now apply nonzero_div_nonzero.
     rewrite Cmod_mult, Cmod_inv, !Cmod_pow, Cmod_R, Rabs_pos_eq by lra'.
     apply Rmult_lt_reg_l with (root^r)%R.
     { apply pow_lt. lra'. }
     rewrite <- Rmult_assoc, Rinv_r, Rmult_1_r, Rmult_1_l.
     2:{ apply pow_nonzero. lra'. }
     apply Rpow_lt_compat_r; trivial. apply Cmod_ge_0.
     apply Rlt_trans with 1%R; try lra'.
   + now rewrite PS_poly_radius.
   + rewrite C_CV_radius_pow. 2:{ now apply nonzero_div_nonzero. }
     simpl. rewrite Cmod_inv, Rinv_inv, !Cmod_pow.
     apply Rlt_trans with (1^r)%R.
     * apply Rpow_lt_compat_r; trivial. apply Cmod_ge_0. lra'.
     * apply Rpow_lt_compat_r; trivial; try lra.
       rewrite Cmod_R, Rabs_pos_eq; lra'.
 - apply fps_ok; trivial.
 - apply Rbar.Rbar_lt_le_trans with (/root)%R; trivial. apply fps_radius.
Qed.

Lemma grps'_radius (r : nat) : r<>O ->
  Rbar.Rbar_le (/root)%R (C_CV_radius (grps' r)).
Proof.
 intros Hr.
 eapply Rbar.Rbar_le_trans; [|apply C_CV_radius_mult].
 apply Rbar.Rbar_min_case; [|apply fps_radius].
 apply C_CV_radius_dilate'; trivial.
 eapply Rbar.Rbar_le_trans; [|apply C_CV_radius_mult].
 apply Rbar.Rbar_min_case.
 - now rewrite PS_poly_radius.
 - assert (NZ : root^r <> 0) by (apply Cpow_nz; intros [=H]; lra').
   rewrite C_CV_radius_pow.
   2:{ now apply nonzero_div_nonzero. }
   simpl.
   rewrite Cmod_inv, Rinv_inv, Cmod_pow, Cmod_R, Rabs_pos_eq by lra'.
   apply Rpow_le_compat_r; trivial.
   + apply Rlt_le, Rinv_0_lt_compat; lra'.
   + apply Rlt_le, Rlt_trans with 1%R; lra'.
Qed.

Lemma grps'_eqn (r : nat) n : r<>O -> grps' r n = grps r n.
Proof.
 intros Hr. apply CPowerSeries_coef_ext.
 - apply Rbar.Rbar_lt_le_trans with (/root)%R;
    try apply grps'_radius; trivial.
   simpl. apply Rinv_0_lt_compat; lra'.
 - apply Rbar.Rbar_lt_trans with 1%R; try apply grps_radius; trivial.
   simpl. lra.
 - assert (LT : 0 < /root). { apply Rinv_0_lt_compat; lra'. }
   exists (mkposreal _ LT). intros x Hx.
   change (Rabs (x-0) < /root) in Hx. rewrite Rminus_0_r in Hx.
   transitivity (gr r x).
   + apply CPowerSeries_unique. apply grps'_ok; trivial.
     now rewrite Cmod_R.
   + symmetry. apply CPowerSeries_unique. apply grps_ok; trivial.
     rewrite Cmod_R. apply Rlt_le, Rlt_trans with (/root)%R; trivial.
     rewrite <- Rinv_1. apply Rinv_lt_contravar; lra'.
Qed.

Lemma grps'_init (r : nat) n : (n < r)%nat -> grps' r n = fps n.
Proof.
 intros H.
 unfold grps', CPS_mult.
 rewrite <- big_sum_sum_n. rewrite <- big_sum_extend_l.
 change Gplus with Cplus.
 replace (fps n) with (1 * fps n + 0) by ring. f_equal.
 - rewrite Nat.sub_0_r. f_equal.
   unfold PS_dilate. rewrite Nat.mod_0_l by lia. simpl.
   rewrite Nat.div_0_l, sum_O by lia. simpl. unfold PS_poly, coef; simpl.
   ring.
 - apply (@big_sum_0_bounded C). intros m Hm. apply Cmult_integral; left.
   unfold PS_dilate. now rewrite Nat.mod_small by lia.
Qed.

Lemma vr_vr r x :
  r<>O -> x<>0 -> Cmod x <> root -> Cmod x <> (/root)%R ->
  vr r x * vr r (/x) = root^(2*r).
Proof.
 intros Hr H1 H2 H3. unfold vr.
 replace (root^(2*r)) with ((root^r)^2).
 2:{ now rewrite Nat.mul_comm, Cpow_mult_r. }
 rewrite !Cpow_inv. field; repeat split.
 - now apply Cpow_nz.
 - apply Cpow_nz. intros [=H];lra'.
 - intros E. apply Cminus_eq_0 in E.
   apply (f_equal Cmod) in E.
   rewrite <- Cpow_mult_l, Cmod_pow, Cmod_mult, Cmod_R, Rabs_pos_eq in E.
   2:lra'.
   rewrite Cmod_1 in E.
   apply Rdichotomy in H3. destruct H3 as [H3|H3].
   + apply Rmult_lt_compat_r with (r:=root) in H3; try lra'.
     rewrite Rinv_l in H3 by lra'.
     assert (H3' : 0<= Cmod x * root).
     { apply Rmult_le_pos. apply Cmod_ge_0. lra'. }
     generalize (pow_lt_1_compat (Cmod x*root) r (conj H3' H3) lia). lra.
   + apply Rmult_lt_compat_r with (r:=root) in H3; try lra'.
     rewrite Rinv_l in H3 by lra'.
     generalize (Rlt_pow_R1 _ r H3 lia). lra.
 - intros E. apply Cminus_eq_0 in E.
   apply (f_equal Cmod) in E.
   rewrite !Cmod_pow, Cmod_R, Rabs_pos_eq in E by lra'.
   apply pow_inj_l in E; trivial; try lra'. apply Cmod_ge_0.
Qed.

Lemma gr_gr r x :
  r<>O -> x<>0 -> Cmod x <> root -> Cmod x <> (/root)%R ->
  ~Root x Pcoef -> ~Root (/x) Pcoef ->
  gr r x * gr r (/x) = root^(2*r).
Proof.
 intros Hr H1 H2 H3 H4 H5.
 rewrite !gr_alt, <- (vr_vr r x); trivial.
 2:{ intros E. apply (f_equal Cinv) in E. rewrite !Cinv_inv in E.
     subst x. rewrite Cmod_R, Rabs_pos_eq in H2; lra'. }
 2:{ intros E. subst x. rewrite Cmod_inv, Cmod_R, Rabs_pos_eq in H3; lra'. }
 rewrite (Cmult_comm (vr r (/x))), !Cmult_assoc. f_equal.
 rewrite <- !Cmult_assoc. rewrite <- (Cmult_1_r (vr r x)) at 2. f_equal.
 apply ff; trivial.
Qed.

Lemma grps_square_ex r : r<>O -> ex_series (fun n => (grps r n)^2).
Proof.
 intros Hr.
 apply ex_series_Cmod.
 eapply ex_series_ext.
 { intros n. unfold "∘". symmetry. now rewrite Cmod_pow. }
 apply ex_series_square. rewrite <- ex_pseries_1. apply CV_radius_inside.
 unfold "∘".
 erewrite CV_radius_ext.
 2:{ intros n. now rewrite Rabs_pos_eq by apply Cmod_ge_0. }
 change (fun n => Cmod (grps r n)) with (Cmod ∘ (grps r)).
 rewrite <- C_CV_radius_alt. rewrite Rabs_pos_eq by lra.
 now apply grps_radius.
Qed.

Lemma grps_square r : r<>O -> root^(2*r) = CSeries (fun n => (grps r n)^2).
Proof.
 intros Hr.
 rewrite <- (SecondRoot.Mu_series_square (grps r) (gr r)).
 2:{ rewrite <- ex_pseries_1. apply CV_radius_inside.
     rewrite <- C_CV_radius_alt. rewrite Rabs_pos_eq by lra.
     now apply grps_radius. }
 2:{ intros z Hz. symmetry. apply CPowerSeries_unique, grps_ok; trivial.
     lra. }
 symmetry. unfold SecondRoot.Mu.
 rewrite (RInt_ext (V:=C_CNM)) with (g := fun t => root^(2*r)).
 2:{ intros x _. rewrite Cexp_neg. apply gr_gr; trivial.
     - apply Cexp_nonzero.
     - rewrite Cmod_Cexp; lra'.
     - rewrite Cmod_Cexp. intros E.
       apply (f_equal Rinv) in E. rewrite Rinv_inv, Rinv_1 in E. lra'.
     - rewrite Hcoefs. rewrite <- linfactors_roots.
       intros [E|IN].
       + apply (f_equal Cmod) in E.
         rewrite Cmod_Cexp, Cmod_R, Rabs_pos_eq in E; lra'.
       + red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
         rewrite Cmod_Cexp in IN; lra.
     - rewrite <- Cexp_neg.
       rewrite Hcoefs. rewrite <- linfactors_roots.
       intros [E|IN].
       + apply (f_equal Cmod) in E.
         rewrite Cmod_Cexp, Cmod_R, Rabs_pos_eq in E; lra'.
       + red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
         rewrite Cmod_Cexp in IN; lra. }
 rewrite CInt_const. rtoc. field. intros [=H]. now apply PI_neq0.
Qed.

Lemma CPS_mult_real (a b : nat -> C) :
 (forall n, Im (a n) = 0%R) -> (forall n, Im (b n) = 0%R) ->
 forall n, Im (CPS_mult a b n) = 0%R.
Proof.
 intros Ha Hb n.
 unfold CPS_mult. rewrite im_sum_n. rewrite <- (sum_n_R0 n).
 apply sum_n_ext_loc. intros m Hm.
 unfold "∘". rewrite im_mult. rewrite Ha, Hb. lra.
Qed.

Lemma PS_dilate_real (a : nat -> C) r :
 (forall n, Im (a n) = 0%R) -> (forall n, Im (PS_dilate a r n) = 0%R).
Proof.
 intros Ha n. unfold PS_dilate. destruct Nat.eqb. apply Ha. easy.
Qed.

Lemma grps_real (r:nat) : r<>O -> forall n, Im (grps r n) = 0%R.
Proof.
 intros Hr n.
 rewrite <- grps'_eqn; trivial.
 unfold grps'. revert n. apply CPS_mult_real.
 - apply PS_dilate_real, CPS_mult_real.
   + intros n. unfold PS_poly.
     destruct n as [|[|n]]; ctor; simpl; try easy.
     unfold coef. rewrite nth_overflow. easy. simpl; lia.
   + intros n. unfold PS_pow. now ctor.
 - intros n. now rewrite fps_eqn'.
Qed.

Lemma grps_square_real (r:nat) : r<>O ->
 CSeries (fun n => (grps r n)^2) =
 RtoC (Series (fun n => (Re (grps r n))^2)%R).
Proof.
 intros Hr.
 rewrite <- CSeries_RtoC.
 - apply CSeries_ext. intros n. unfold "∘". rtoc. f_equal.
   generalize (grps_real r Hr n). destruct (grps r n) as (x,y). simpl.
   now intros ->.
 - rewrite <- ex_series_RtoC.
   apply ex_series_ext with (fun n => (grps r n)^2).
   2:now apply grps_square_ex.
   intros n. unfold "∘". rtoc. f_equal.
   generalize (grps_real r Hr n). destruct (grps r n) as (x,y). simpl.
   now intros ->.
Qed.

Lemma big_sum_sum_n_R (a : nat -> R) n : big_sum a (S n) = sum_n a n.
Proof.
 induction n.
 - simpl; rewrite sum_O; lra.
 - now rewrite sum_Sn, <- IHn, <- big_sum_extend_r.
Qed.

Lemma Ineq8 (r:nat) : IZR (big_sum (fun m => (fps' m)^2)%Z r) <= root^(2*r).
Proof.
 destruct (Nat.eq_dec r 0) as [->|N].
 - simpl. lra.
 - rewrite <- (re_RtoC (root^(2*r))). rtoc. rewrite grps_square; trivial.
   rewrite grps_square_real, re_RtoC; trivial.
   assert (EX : ex_series (fun n : nat => (Re (grps r n) ^ 2)%R)).
   { rewrite <- ex_series_RtoC.
     apply ex_series_ext with (fun n => (grps r n)^2).
     2:now apply grps_square_ex.
     intros n. unfold "∘". rtoc. f_equal.
     generalize (grps_real r N n). destruct (grps r n) as (x,y). simpl.
     now intros ->. }
   rewrite Series_incr_n with (n:=r); trivial; try lia.
   rewrite <- sum_n_Reals, <- big_sum_sum_n_R, big_sum_IZR.
   replace (S (pred r)) with r by lia.
   rewrite <- (Rplus_0_r (big_sum _ r)). apply Rplus_le_compat.
   + apply Req_le. apply big_sum_eq_bounded. intros m Hm.
     unfold "∘". rewrite <- grps'_eqn, grps'_init, fps_eqn' by lia.
     simpl. unfold Z.pow_pos. simpl.
     now rewrite Z.mul_1_r, Rmult_1_r, mult_IZR.
   + eapply pos_series_pos_lim. apply Series_correct.
     2:{ intros n. cbv beta. nra. }
     rewrite <- (ex_series_incr_n (V:=R_NM) (fun m => Re (grps r m)^2)%R r).
     trivial.
Qed.

Lemma Ineq8' (r:nat) : r<>O ->
  (big_sum (fun m => (fps' m)^2) r < 2^Z.of_nat r)%Z.
Proof.
 intros Hr. apply lt_IZR. eapply Rle_lt_trans; [apply Ineq8|].
 rewrite pow_mult, <- pow_IZR. apply Rpow_lt_compat_r; trivial. nra.
Qed.

Lemma fps_0_1 : fps' 0 = 1%Z /\ fps' 1 = 1%Z.
Proof.
 assert (H0 : (1 <= fps' 0)%Z).
 { assert (0 < fps' 0)%Z; try lia.
   { unfold fps'. rewrite fps_0. simpl.
     assert (H := coefs0_nz).
     destruct (nth 0 coefs Z0); simpl; try easy;
      now rewrite Int_part_IZR. }}
 assert (H1 := Two 1).
 simpl in H1.
 assert (H2 := Ineq8' 2 lia). cbn -[Z.pow] in H2. lia.
Qed.

Lemma fps_2 : (1 <= fps' 2 <= 2)%Z.
Proof.
 generalize (Two 2). simpl.
 generalize (Ineq8' 3 lia).
 cbn -[Z.pow]. destruct fps_0_1 as (->,->). lia.
Qed.

Lemma fps_3 : (1 <= fps' 3 <= 3)%Z.
Proof.
 generalize (Two 3). simpl.
 generalize (Ineq8' 4 lia).
 cbn -[Z.pow]. destruct fps_0_1 as (->,->). generalize fps_2. lia.
Qed.

Lemma root_65 : 6/5 < root.
Proof.
 assert (3 <= root^6).
 { eapply Rle_trans; [|apply (Ineq8 3)].
   cbn - [Z.pow]. destruct fps_0_1 as (->,->).
   apply IZR_le. generalize fps_2; lia. }
 assert (~ (5*root <= 6)); try lra.
 intros LE. apply (Rpow_le_compat_r 6) in LE; lra'.
Qed.

Lemma root_43 : fps' 2 = 2%Z -> 4/3 < root.
Proof.
 intros H.
 assert (6 <= root^6).
 { eapply Rle_trans; [|apply (Ineq8 3)].
   cbn - [Z.pow]. rewrite H. destruct fps_0_1 as (->,->). apply IZR_le. lia. }
 assert (~ (3*root <= 4)); try lra.
 intros LE. apply (Rpow_le_compat_r 6) in LE; lra'.
Qed.

Definition Case1 := take 4 fps' = [1;1;1;1]%Z.
Definition Case2 := take 5 fps' = [1;1;1;2;2]%Z.
Definition Case3 := take 5 fps' = [1;1;1;2;3]%Z /\ (3 <= fps' 5 <= 4)%Z.
Definition Case4 := take 4 fps' = [1;1;2;2]%Z.
Definition Case5 := take 6 fps' = [1;1;1;2;3;5]%Z /\ (5 <= fps' 6 <= 7)%Z.
Definition Case6 := take 4 fps' = [1;1;2;3]%Z /\
                    In (fps' 4, fps' 5) [(3,3);(3,4);(3,5);(4,4);(4,5)]%Z.

Section Lemma3.

Let A n := big_sum (fun m => (fps' (S m))^2)%Z n.
Let C n := A (S n).
Let B n := big_sum (fun m => fps' m * fps' (S m))%Z (S n).
Let phi n (x:R) := (IZR (A n) * x^2 - 2*IZR (B n) * x + IZR (C n))%R.

(* MOVE *)
Lemma ex_series_incr_n {K} {V : NormedModule K} (a : nat -> V) (n:nat) :
  (0 < n)%nat -> ex_series a -> ex_series (fun k => a (n+k)%nat).
Proof.
 intros Hn (l,H). exists (plus l (opp (sum_n a (pred n)))).
 apply is_series_incr_n; trivial.
 replace (plus _ _) with l; trivial. set (x := sum_n _ _).
 symmetry. rewrite <- Hierarchy.plus_assoc, (plus_opp_l (G:=V)).
 apply plus_zero_r.
Qed.

Lemma Ineq9 n : n<>O -> phi n root <= 0.
Proof.
 intros Hn. generalize One'.
 rewrite Series_incr_n with (n:=S n); try lia; try apply ex_series_diff_f'.
 rewrite <- sum_n_Reals, <- big_sum_sum_n_R. simpl pred.
 destruct fps_0_1 as (->,_). rewrite pow1.
 set (a := fun k => _).
 set (b := fun k => _).
 assert (0 <= Series b).
 { apply pos_series_pos_lim with b.
   - apply Series_correct. apply (ex_series_incr_n a (S n)); try lia.
     apply ex_series_diff_f'.
   - intros m. unfold b. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
 intros E.
 assert (LE : (big_sum a (S n) <= root ^ 2)%R) by lra. clear E H b.
 revert LE.
 rewrite big_sum_eq_bounded with
  (g := (fun k => IZR ((fps' k)^2) * root^2
                  + IZR (fps' k * fps' (S k)) * (-2*root)
                  + IZR ((fps' (S k))^2))%R).
 2:{ intros x Hx. unfold a.
     rewrite mult_IZR.
     change 2%Z with (Z.of_nat 2); rewrite <- !pow_IZR. ring. }
 rewrite !big_sum_Rplus, <- !big_sum_Rmult_r.
 rewrite <- (big_sum_IZR (fun k => fps' k ^2)%Z).
 rewrite <- (big_sum_IZR (fun k => fps' k * fps' (S k))%Z).
 rewrite <- (big_sum_IZR (fun k => fps' (S k) ^2)%Z).
 fold (B n). fold (A (S n)). fold (C n).
 rewrite <- big_sum_extend_l.
 fold (A n). change Gplus with Z.add.
 destruct fps_0_1 as (->,_). change (1^2)%Z with 1%Z.
 unfold phi. rewrite plus_IZR. lra.
Qed.

Lemma fps_no_1113 : fps' 2 = 1%Z -> fps' 3 = 3%Z -> False.
Proof.
 intros H2 H3.
 generalize (Ineq9 2 lia). unfold phi, C, B, A.
 cbn -[Z.pow pow]. destruct fps_0_1 as (->,->). rewrite H2, H3.
 cbn - [pow]. replace (2*5)%R with 10%R by lra.
 set (f := (fun x => 2 * x^2-10*x+11)%R).
 set (df := (fun x => 4 * x - 10)%R).
 change (f root <= 0 -> False).
 destruct (MVT_weak f df root (sqrt 2)) as (c & Hc & E).
 { intros x _. unfold f, df. auto_derive; trivial. ring. }
 { apply Rsqr_incrst_0; try lra'; try apply sqrt_pos.
   rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
 assert (sqrt 2 < 2).
 { apply Rsqr_incrst_0; try lra'; try apply sqrt_pos.
   rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
 assert (LT : df c < 0).
 { unfold df. lra. }
 assert (LT' : 0 < f (sqrt 2)).
 { unfold f. rewrite <- Rsqr_pow2, Rsqr_sqrt by lra.
   assert (sqrt 2 < 1.5); try lra.
   apply Rsqr_incrst_0; try lra; try apply sqrt_pos.
   rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
 nra.
Qed.

Lemma fps_1123 : fps' 2 = 2%Z -> fps' 3 = 3%Z -> Case6.
Proof.
 destruct fps_0_1 as (H0,H1). intros H2 H3. split.
 { unfold take. simpl. now rewrite H0, H1, H2, H3. }
 assert (L4 : (3 <= fps' 4)%Z). { rewrite <- H3. apply (Two 4). }
 assert (T5 : (fps' 4 <= fps' 5)%Z). { apply (Two 5). }
 assert (LE := Ineq8' 6 lia).
 cbn -[Z.pow] in LE. rewrite H0, H1, H2, H3 in LE.
 assert (LE' : (fps' 4 ^2 + fps' 5 ^2 <= 48)%Z) by lia. clear LE.
 assert (U4 : (fps' 4 <= 4)%Z).
 { assert (U : (fps' 4 <> 6)%Z). { intros U. rewrite U in LE', T5. lia. }
   assert (V : (fps' 4 <> 5)%Z). { intros V. rewrite V in LE', T5. lia. }
   lia. }
 assert (U5 : (fps' 5 <= 6)%Z) by lia.
 assert (U5b : (fps' 4 = 4 -> fps' 5 <= 5)%Z) by lia.
 assert (U5c : (fps' 4 = 3 -> fps' 5 = 6 -> False)%Z).
 { intros H4 H5.
   generalize (Ineq9 4 lia). unfold phi, C, B, A.
   cbn -[Z.pow pow]. rewrite H0, H1, H2, H3, H4, H5.
   cbn - [pow].
   generalize (discriminant_neg 23 (-2*36) 59 ltac:(lra) ltac:(lra) root).
   lra. }
 simpl. rewrite !pair_equal_spec. lia.
Qed.

Lemma fps_1112 : fps' 2 = 1%Z -> fps' 3 = 2%Z -> Case2 \/ Case3 \/ Case5.
Proof.
 destruct fps_0_1 as (H0,H1). intros H2 H3.
 (* With just $b_4 >= 4$, the inequality
    $b_4^2+18-4(b_4+2)\sqrt{2} >= 34 - 24\sqrt{2}$
    requires a study of the function $x^2+18-4(x+2)\sqrt{2}$
    (which is increasing for x>=2√2 and in particular x>=4).
    Not in the article, but simpler here: use Inequality (8)
    to obtain $b_4 <= 4$. *)
 assert (LE := Ineq8' 5 lia).
 cbn -[Z.pow pow] in LE. rewrite H0, H1, H2, H3 in LE.
 assert (H4 : (fps' 4 <= 4)%Z) by lia. clear LE.
 destruct (Z.eq_dec (fps' 4) 4) as [H4'|H4'].
 - exfalso. clear H4.
   generalize (Ineq9 3 lia). unfold phi, C, B, A.
   cbn -[Z.pow pow]. rewrite H0, H1, H2, H3, H4'. cbn -[pow].
   replace (2*12)%R with 24%R by lra.
   set (f := (fun x => 6*x^2-24*x+22)%R).
   set (df := (fun x => 12*x - 24)%R).
   change (f root <= 0 -> False).
   destruct (MVT_weak f df root (sqrt 2)) as (c & Hc & E).
   { intros x _. unfold f, df. auto_derive; trivial. ring. }
   { apply Rsqr_incrst_0; try lra'; try apply sqrt_pos.
     rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
   assert (sqrt 2 < 2).
   { apply Rsqr_incrst_0; try lra'; try apply sqrt_pos.
     rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
   assert (LT : df c < 0).
   { unfold df. lra. }
   assert (LT' : 0 < f (sqrt 2)).
   { unfold f. rewrite <- Rsqr_pow2, Rsqr_sqrt by lra.
     assert (24*sqrt 2 < 34); try lra.
     apply Rsqr_incrst_0; try nra.
     2:{ apply Rmult_le_pos. lra. apply sqrt_pos. }
     rewrite Rsqr_mult, Rsqr_sqrt, !Rsqr_pow2; lra. }
   nra.
 - assert (H4b : (fps' 4 = 2 \/ fps' 4 = 3)%Z).
   { generalize (Two 4). simpl. lia. }
   clear H4' H4. destruct H4b as [H4|H4].
   + left. unfold Case2, take. simpl. congruence.
   + right.
     (* Same as before : Inequality (8) ensures $b_5 <= 6$ and that spares
        us a function study *)
     assert (LE := Ineq8' 6 lia).
     cbn -[Z.pow pow] in LE. rewrite H0, H1, H2, H3, H4 in LE.
     assert (H5 : (fps' 5 <= 6)%Z) by lia. clear LE.
     destruct (Z.eq_dec (fps' 5) 6) as [H5'|H5'].
     * exfalso. clear H5.
       generalize (Ineq9 4 lia). unfold phi, C, B, A.
       cbn -[Z.pow pow]. rewrite H0, H1, H2, H3, H4, H5'. cbn -[pow].
       replace (2*28)%R with 56%R by lra.
       set (f := (fun x => 15*x^2-56*x+51)%R).
       set (df := (fun x => 30*x - 56)%R).
       change (f root <= 0 -> False).
       destruct (MVT_weak f df root (sqrt 2)) as (c & Hc & E).
       { intros x _. unfold f, df. auto_derive; trivial. ring. }
       { apply Rsqr_incrst_0; try lra'; try apply sqrt_pos.
         rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
       assert (sqrt 2 < 1.5).
       { apply Rsqr_incrst_0; try lra'; try apply sqrt_pos.
         rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
       assert (LT : df c < 0).
       { unfold df. lra. }
       assert (LT' : 0 < f (sqrt 2)).
       { unfold f. rewrite <- Rsqr_pow2, Rsqr_sqrt by lra.
         assert (56*sqrt 2 < 81); try lra.
         apply Rsqr_incrst_0; try nra.
         2:{ apply Rmult_le_pos. lra. apply sqrt_pos. }
         rewrite Rsqr_mult, Rsqr_sqrt, !Rsqr_pow2; lra. }
       nra.
     * assert (H5b : (fps' 5 = 3 \/ fps' 5 = 4 \/ fps' 5 = 5)%Z).
       { generalize (Two 5). simpl. lia. }
       clear H5' H5. rewrite <- or_assoc in H5b.
       destruct H5b as [H5|H5].
       ** left. unfold Case3, take. split; try lia. simpl. congruence.
       ** right. unfold Case5, take. split. simpl; congruence.
          (* Inequality (8) ensures $b_6 <= 9$ *)
          assert (LE := Ineq8' 7 lia).
          cbn -[Z.pow pow] in LE. rewrite H0, H1, H2, H3, H4, H5 in LE.
          assert (H6 : (fps' 6 <= 9)%Z) by lia. clear LE.
          destruct (Z.le_gt_cases 8 (fps' 6)) as [H6'|H6'].
          2:{ generalize (Two 6). simpl. lia. }
          exfalso.
          generalize (Ineq9 5 lia). unfold phi, C, B, A.
          cbn -[Z.pow pow]. rewrite H0, H1, H2, H3, H4, H5.
          change (_+5^2)%Z with 40%Z.
          change (_+3*5)%Z with 25%Z.
          rewrite !plus_IZR, mult_IZR.
          change 2%Z with (Z.of_nat 2)%Z at 2. rewrite <- pow_IZR.
          set (b6 := fps' 6) in *.
          apply IZR_le in H6'.
          set (f := (fun x => 40*x^2-2*(25+5*b6)*x+(40+b6^2))%R).
          set (df := (fun x => 80*x - 2*(25+5*b6))%R).
          change (f root <= 0 -> False).
          destruct (MVT_weak f df root (sqrt 2)) as (c & Hc & E).
          { intros x _. unfold f, df. auto_derive; trivial. ring. }
          { apply Rsqr_incrst_0; try lra'; try apply sqrt_pos.
            rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
          assert (sqrt 2 < 1.5).
          { apply Rsqr_incrst_0; try lra'; try apply sqrt_pos.
            rewrite Rsqr_sqrt, Rsqr_pow2; lra. }
          assert (LT : df c < 0).
          { unfold df. lra. }
          assert (LT' : 0 < f (sqrt 2)).
          { unfold f. rewrite <- Rsqr_pow2, Rsqr_sqrt by lra.
            assert ((50+10*b6)*sqrt 2 < 120+b6^2); try lra.
            apply Rsqr_incrst_0; try nra.
            2:{ apply Rmult_le_pos. lra. apply sqrt_pos. }
            rewrite Rsqr_mult, Rsqr_sqrt, !Rsqr_pow2 by lra.
            apply le_IZR in H6'.
            assert (B6 : (b6 = 8 \/ b6 = 9)%Z) by lia.
            destruct B6 as [-> | ->]. lra. lra. }
       nra.
Qed.

Lemma Three : Case1 \/ Case2 \/ Case3 \/ Case4 \/ Case5 \/ Case6.
Proof.
 destruct fps_0_1 as (H0,H1).
 assert (H2 : (fps' 2 = 1 \/ fps' 2 = 2)%Z) by (generalize fps_2; lia).
 destruct H2 as [H2|H2].
 - assert (H3 : (fps' 3 = 1 \/ fps' 3 = 2)%Z).
   { generalize fps_no_1113 fps_3; lia. }
   destruct H3 as [H3|H3].
   + left. unfold Case1, take. simpl. congruence.
   + generalize (fps_1112 H2 H3). tauto.
 - assert (H3 : (fps' 3 = 2 \/ fps' 3 = 3)%Z).
    { generalize (Two 3) fps_3; simpl; lia. }
    destruct H3 as [H3|H3].
    + do 3 right; left. unfold Case4, take. simpl. congruence.
    + do 5 right. now apply fps_1123.
Qed.

End Lemma3.

Definition ZPS_mult (a b : nat -> Z) (n : nat) :=
 big_sum (fun k : nat => (a k * b (n - k)%nat)%Z) (S n).

Lemma ZPS_mult_IZR (a b : nat -> Z) n :
 IZR (ZPS_mult a b n) = PS_mult (IZR∘a) (IZR∘b) n.
Proof.
 unfold ZPS_mult, PS_mult. rewrite <- sum_n_Reals, <- big_sum_sum_n_R.
 rewrite big_sum_IZR. apply big_sum_eq_bounded. intros x Hx.
 unfold "∘". now rewrite mult_IZR.
Qed.

Lemma PS_mult_RtoC (a b : nat -> R) n :
 RtoC (PS_mult a b n) = CPS_mult (RtoC∘a) (RtoC∘b) n.
Proof.
 unfold PS_mult, CPS_mult. rewrite <- sum_n_Reals.
 rewrite RtoC_sum_n. apply sum_n_ext. intros x.
 unfold "∘". now rewrite RtoC_mult.
Qed.

Lemma ex_series_PS_poly p : ex_series (PS_poly p).
Proof.
 apply ex_series_shiftn with (N := length p).
 apply ex_series_ext with (a := fun _ => 0).
 { intros n. unfold PS_poly, coef. now rewrite nth_overflow by lia. }
 apply ex_series_RtoC. exists 0%R. apply is_series_R0.
Qed.

Lemma Cmod_PS_poly p n :
  RtoC (Cmod (PS_poly p n)) = PS_poly (map (RtoC∘Cmod) p) n.
Proof.
 unfold PS_poly. unfold coef.
 replace 0 with ((RtoC∘Cmod) 0) at 2.
 2:{ unfold "∘". now rewrite Cmod_0. }
 now rewrite map_nth.
Qed.

Lemma PS_poly_pow2 p n :
  (PS_poly p n)^2 = PS_poly (map (fun x => x^2) p) n.
Proof.
 unfold PS_poly, coef.
 rewrite <- (map_nth (fun x => x^2)). f_equal. ring.
Qed.

Section Lemma4.

Variable A : list Z.
Definition beta := ZPS_mult (fun n => nth n A Z0) fps'.
Let B n (x:C) := sum_n (fun m => beta m * x^m) n.
Let mu (l : list Z) := big_sum (fun m => (nth m l Z0)^2)%Z (length l).
Variable k:nat.
Let Bkpoly := take (S k) beta.

Lemma Bkpoly_ok x : Peval (Zpoly Bkpoly) x = B k x.
Proof.
 unfold Peval, Zpoly, Bkpoly, take, coef, B.
 rewrite !map_length, seq_length, map_map.
 rewrite big_sum_sum_n.
 apply sum_n_ext_loc.
 intros n Hn. f_equal.
 rewrite nth_map_indep with (d' := O); try (rewrite ?seq_length; lia).
 now rewrite seq_nth by lia.
Qed.

Lemma mu_poly l : RtoC (mu l) = SecondRoot.Mu (Peval (Zpoly l)).
Proof.
 rewrite (SecondRoot.Mu_series_square (PS_poly (Zpoly l))).
 2:{ unfold "∘". rewrite <- ex_series_RtoC.
     eapply ex_series_ext. symmetry. apply Cmod_PS_poly.
     apply ex_series_PS_poly. }
 2:{ intros z Hz. symmetry. apply CPowerSeries_unique, PS_poly_ok. }
 rewrite CSeries_shiftn with (N := length l).
 2:{ eapply ex_series_ext. symmetry. apply PS_poly_pow2.
     apply ex_series_PS_poly. }
 rewrite CSeries_ext with (v := fun n => 0).
 2:{ intros n. unfold PS_poly, Zpoly, coef.
     rewrite nth_overflow. ring. rewrite map_length; lia. }
 rewrite CSeries_unique with (l := 0), Cplus_0_r.
 2:{ apply is_CSeries_RtoC, is_series_R0. }
 unfold mu. rewrite big_sum_IZR, big_sum_RtoC.
 apply big_sum_eq_bounded. intros m Hm.
 unfold PS_poly, "∘". rewrite coef_Zpoly. ctor. now rewrite pow_IZR.
Qed.

Lemma continuous_poly p x : continuous (Peval p) x.
Proof.
 unfold Peval.
 destruct (Nat.eq_dec (length p) 0) as [E|N].
 - rewrite E. simpl. apply continuous_const.
 - replace (length p) with (S (length p - 1)) by lia.
   eapply continuous_ext. { intros y. symmetry. apply big_sum_sum_n. }
   apply sum_n_continuous.
   intros i Hi. apply continuous_Cmult. apply continuous_const.
   apply continuous_Cpow.
Qed.

Lemma Mu_ext (f g : C -> C) :
  (forall c, Cmod c = 1%R -> f c = g c) ->
  SecondRoot.Mu f = SecondRoot.Mu g.
Proof.
 intros Eq. unfold SecondRoot.Mu. f_equal.
 apply RInt_ext. intros x _. f_equal; apply Eq; now rewrite Cmod_Cexp.
Qed.

Lemma mu_A : RtoC (mu A) = SecondRoot.Mu (Peval (Zpoly A)).
Proof.
 apply mu_poly.
Qed.

Lemma mu_B : RtoC (mu Bkpoly) = SecondRoot.Mu (B k).
Proof.
 rewrite mu_poly. apply Mu_ext. intros c _. apply Bkpoly_ok.
Qed.

Definition vAf x := Peval (Zpoly A) x * gr 1 x.
Definition vB x := vr 1 x * B k x.

Lemma vAf_alt x : x<>/root -> vAf x = vr 1 x * Peval (Zpoly A) x * f x.
Proof.
 intros Hx. unfold vAf. rewrite gr_alt by trivial; ring.
Qed.

Definition mu_vAf : SecondRoot.Mu vAf = root^2 * mu A.
Proof.
 rewrite mu_A.
 unfold SecondRoot.Mu.
 rewrite Cmult_assoc, (Cmult_comm (root^2)), <- Cmult_assoc. f_equal.
 rewrite <- CInt_scal.
 2:{ apply (ex_RInt_continuous (V:=C_CNM)).
     intros x _. apply continuous_Cmult.
     - apply continuous_comp;
         [apply continuous_Cexp|apply continuous_poly].
     - apply continuous_comp; [|apply continuous_poly].
       apply continuous_comp; [|apply continuous_Cexp].
       apply (continuous_opp (V:=R_NM)), continuous_id. }
 apply RInt_ext.
 intros x _. unfold vAf.
 change (root^2) with (root^(2*1)).
 rewrite <- (gr_gr 1 (Cexp x));
   try lia; try apply Cexp_nonzero; try (rewrite Cmod_Cexp; lra').
 - rewrite Cexp_neg. fixeq C. ring.
 - rewrite Hcoefs, <- linfactors_roots. intros [E|IN].
   + apply (f_equal Cmod) in E.
     rewrite Cmod_Cexp, Cmod_R, Rabs_pos_eq in E; lra'.
   + red in Hroots. rewrite Forall_forall in Hroots; apply Hroots in IN.
     rewrite Cmod_Cexp in IN; lra.
 - rewrite <- Cexp_neg, Hcoefs, <- linfactors_roots. intros [E|IN].
   + apply (f_equal Cmod) in E.
     rewrite Cmod_Cexp, Cmod_R, Rabs_pos_eq in E; lra'.
   + red in Hroots. rewrite Forall_forall in Hroots; apply Hroots in IN.
     rewrite Cmod_Cexp in IN; lra.
Qed.

Lemma continuous_B x : continuous (B k) x.
Proof.
 eapply continuous_ext. apply Bkpoly_ok. apply continuous_poly.
Qed.

Lemma mu_vB : SecondRoot.Mu vB = root^2 * mu Bkpoly.
Proof.
 rewrite mu_B.
 unfold SecondRoot.Mu.
 rewrite Cmult_assoc, (Cmult_comm (root^2)), <- Cmult_assoc. f_equal.
 rewrite <- CInt_scal.
 2:{ apply (ex_RInt_continuous (V:=C_CNM)).
     intros x _. apply continuous_Cmult.
     - apply continuous_comp;
         [apply continuous_Cexp|apply continuous_B].
     - apply continuous_comp; [|apply continuous_B].
       apply continuous_comp; [|apply continuous_Cexp].
       apply (continuous_opp (V:=R_NM)), continuous_id. }
 apply RInt_ext.
 intros x _. unfold vB.
 change (root^2) with (root^(2*1)).
 rewrite <- (vr_vr 1 (Cexp x));
   try lia; try apply Cexp_nonzero; try (rewrite Cmod_Cexp; lra').
 rewrite Cexp_neg. fixeq C. ring.
Qed.

Definition alpha := CPS_mult (PS_poly (Zpoly A)) (grps 1).
Definition vr1ps := CPS_mult (PS_poly [1;-root]) (PS_pow (/root)).
Definition gamma := CPS_mult vr1ps (PS_poly (Zpoly Bkpoly)).

Lemma beta_ok x : Cmod x < /root ->
 is_CPowerSeries beta x (Peval (Zpoly A) x * f x).
Proof.
 intros Hx.
 unfold beta.
 apply is_CPowerSeries_alt.
 apply is_pseries_ext with (CPS_mult (PS_poly (Zpoly A)) fps).
 { intros n. rewrite ZPS_mult_IZR, PS_mult_RtoC.
   unfold CPS_mult. unfold "∘". eapply sum_n_ext.
   intros m. now rewrite <- fps_eqn', <- coef_Zpoly. }
 rewrite <- is_CPowerSeries_alt.
 apply is_CPS_mult.
 - apply PS_poly_ok.
 - now apply fps_ok.
 - now rewrite PS_poly_radius.
 - eapply Rbar.Rbar_lt_le_trans; [| apply fps_radius]. simpl. apply Hx.
Qed.

Lemma beta_radius : Rbar.Rbar_le (/root)%R (C_CV_radius beta).
Proof.
 apply C_CV_radius_minorant. intros. eexists. now apply beta_ok.
Qed.

Lemma alpha_ok x : Cmod x <= 1 -> is_CPowerSeries alpha x (vAf x).
Proof.
 intros Hx.
 unfold alpha, vAf.
 apply is_CPS_mult.
 - apply PS_poly_ok.
 - now apply grps_ok.
 - now rewrite PS_poly_radius.
 - eapply Rbar.Rbar_le_lt_trans; [| apply grps_radius; lia]. apply Hx.
Qed.

Lemma alpha_radius : Rbar.Rbar_lt 1%R (C_CV_radius alpha).
Proof.
 unfold alpha.
 eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
 rewrite PS_poly_radius.
 apply Rbar.Rbar_min_case; [simpl; trivial|]. now apply grps_radius.
Qed.

Lemma vr1ps_ok x : Cmod x < root -> is_CPowerSeries vr1ps x (vr 1 x).
Proof.
 intros Hx.
 unfold vr1ps, vr, Cdiv. rewrite !Cpow_1_r, (Cmult_comm x).
 assert (/root <> 0). { ctor. intros [=H]. lra'. }
 apply is_CPS_mult.
 - replace (1-root*x) with (Peval [1;-root] x). apply PS_poly_ok.
   rewrite cons_eval, Pconst_eval. ring.
 - apply is_CPowerSeries_pow; trivial.
   rewrite Cmod_mult, Cmod_inv, Cmod_R, Rabs_pos_eq by lra'.
   apply Rmult_lt_reg_l with root. lra'. field_simplify; lra'.
 - now rewrite PS_poly_radius.
 - rewrite C_CV_radius_pow; trivial. simpl.
   rewrite Cmod_inv, Rinv_inv, Cmod_R, Rabs_pos_eq; lra'.
Qed.

Lemma vr1ps_radius : Rbar.Rbar_le root (C_CV_radius vr1ps).
Proof.
 apply C_CV_radius_minorant. intros; eexists; now apply vr1ps_ok.
Qed.

Lemma vr1ps_0 : vr1ps 0 = 1.
Proof.
 unfold vr1ps, CPS_mult. simpl. rewrite sum_O; lca.
Qed.

Lemma vr1ps_alt n : n<>O -> vr1ps n = (1-root^2)/root^n.
Proof.
 intros Hn.
 unfold vr1ps, CPS_mult. rewrite <- big_sum_sum_n.
 destruct n as [|n]; try easy.
 rewrite <- !big_sum_extend_l. change Gplus with Cplus.
 rewrite big_sum_0.
 2:{ intros x. unfold PS_poly, coef. rewrite nth_overflow. lca. simpl; lia. }
 rewrite Cplus_0_r. unfold PS_poly, coef. simpl nth.
 unfold PS_pow. simpl. rewrite Nat.sub_0_r, !Cpow_inv. field.
 split; try apply Cpow_nz; intros [=H]; lra'.
Qed.

Lemma gamma_ok x : Cmod x <= 1 -> is_CPowerSeries gamma x (vB x).
Proof.
 intros Hx.
 unfold gamma, vB.
 apply is_CPS_mult.
 - apply vr1ps_ok; lra'.
 - rewrite <- Bkpoly_ok. apply PS_poly_ok.
 - eapply Rbar.Rbar_lt_le_trans; [|apply vr1ps_radius]. simpl; lra'.
 - now rewrite PS_poly_radius.
Qed.

Lemma gamma_radius : Rbar.Rbar_lt 1%R (C_CV_radius gamma).
Proof.
 unfold gamma.
 eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
 rewrite PS_poly_radius.
 apply Rbar.Rbar_min_case; [|simpl; trivial].
 apply Rbar.Rbar_lt_le_trans with root. simpl; lra'. apply vr1ps_radius.
Qed.

Lemma alpha_alt n : alpha n = CPS_mult vr1ps beta n.
Proof.
 revert n. apply CPowerSeries_coef_ext.
 - apply Rbar.Rbar_lt_trans with 1%R. simpl; lra. apply alpha_radius.
 - eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
   apply Rbar.Rbar_min_case.
   + apply Rbar.Rbar_lt_le_trans with root. simpl; lra'.
     apply vr1ps_radius.
   + apply Rbar.Rbar_lt_le_trans with (/root)%R. simpl; lra'.
     apply beta_radius.
 - assert (LT : 0 < /root) by lra'.
   exists (mkposreal _ LT).
   intros y Hy. change (Rabs (y-0) < /root) in Hy.
   rewrite Rminus_0_r in Hy.
   rewrite CPowerSeries_mult; rewrite ?Cmod_R.
   + assert (Hy1 : Cmod y <= 1). { rewrite Cmod_R. lra'. }
     assert (Hy2 : Cmod y < /root). { rewrite Cmod_R. lra. }
     assert (Hy3 : Cmod y < root). { rewrite Cmod_R. lra'. }
     rewrite (CPowerSeries_unique _ _ _ (alpha_ok y Hy1)).
     rewrite (CPowerSeries_unique _ _ _ (beta_ok y Hy2)).
     rewrite (CPowerSeries_unique _ _ _ (vr1ps_ok y Hy3)).
     rewrite vAf_alt. ring. ctor. intros [= H]. rewrite H in Hy.
     rewrite Rabs_pos_eq in Hy; lra'.
   + apply Rbar.Rbar_lt_le_trans with root. simpl; lra'.
     apply vr1ps_radius.
   + apply Rbar.Rbar_lt_le_trans with (/root)%R. simpl; lra'.
     apply beta_radius.
Qed.

Lemma big_sum_rev (a : nat -> C) n :
 big_sum a n = big_sum (fun k => a (n-1-k)%nat) n.
Proof.
 induction n; try easy.
 rewrite <- big_sum_extend_r, <- big_sum_extend_l. change Gplus with Cplus.
 replace (S n - 1 -0)%nat with n by lia. rewrite Cplus_comm. f_equal.
 rewrite IHn. apply big_sum_eq_bounded. intros x Hx. f_equal. lia.
Qed.

Lemma gamma_alt n : (n>k)%nat -> gamma n = (1-root^2)/root^n * B k root.
Proof.
 intros Hn.
 unfold gamma. unfold CPS_mult.
 rewrite <- big_sum_sum_n, <- big_sum_extend_l.
 change Gplus with Cplus.
 unfold PS_poly.
 rewrite coef_Zpoly, Nat.sub_0_r, nth_overflow, Cmult_0_r, Cplus_0_l.
 2:{ unfold Bkpoly. now rewrite take_length. }
 erewrite big_sum_eq_bounded.
 2:{ intros m Hm. rewrite vr1ps_alt by lia. unfold Cdiv.
     rewrite <- Cmult_assoc. reflexivity. }
 rewrite <- big_sum_Cmult_l.
 unfold Cdiv. rewrite <- Cmult_assoc. f_equal.
 apply Cmult_eq_reg_l with (root^n).
 2:{ apply Cpow_nz. intros [=H]; lra'. }
 rewrite Cmult_assoc, Cinv_r, Cmult_1_l.
 2:{ apply Cpow_nz. intros [=H]; lra'. }
 rewrite big_sum_Cmult_l. unfold B.
 rewrite big_sum_rev.
 erewrite big_sum_eq_bounded.
 2:{ intros x Hx.
     rewrite Cmult_assoc.
     replace (root^n * _) with (root^x).
     2:{ replace (S _) with (n-x)%nat by lia.
         replace n with (n-x+x)%nat at 1 by lia.
         rewrite Cpow_add. field. apply Cpow_nz. intros [=H]; lra'. }
     replace (n - S (_ - _))%nat with x by lia.
     rewrite coef_Zpoly, Cmult_comm. reflexivity. }
 replace n with (S k+(n-S k))%nat by lia.
 rewrite big_sum_sum. rewrite big_sum_sum_n. rewrite big_sum_0.
 2:{ intros x. rewrite nth_overflow. apply Cmult_0_l. unfold Bkpoly.
     rewrite take_length; lia. }
 rewrite Cplus_0_r. apply sum_n_ext_loc.
 intros m Hm. f_equal. unfold Bkpoly. now rewrite take_nth by lia.
Qed.

Lemma alpha_gamma_init n : (n <= k)%nat -> alpha n = gamma n.
Proof.
 intros Hn.
 rewrite alpha_alt. unfold gamma.
 unfold CPS_mult. apply sum_n_ext_loc.
 intros m Hm. f_equal. unfold PS_poly. rewrite coef_Zpoly.
 unfold Bkpoly. rewrite take_nth; trivial; lia.
Qed.

Lemma alpha_gamma_Sk : alpha (S k) = beta (S k) + gamma (S k).
Proof.
 rewrite alpha_alt. unfold gamma. unfold CPS_mult.
 rewrite <- !big_sum_sum_n.
 do 2 rewrite <- (big_sum_extend_l (S k)). change Gplus with Cplus.
 rewrite Nat.sub_0_r, vr1ps_0.
 rewrite Cmult_1_l. f_equal.
 unfold PS_poly. rewrite coef_Zpoly. rewrite nth_overflow.
 2:{ unfold Bkpoly. now rewrite take_length. }
 rewrite Cmult_0_r, Cplus_0_l. apply big_sum_eq_bounded.
 intros m Hm. f_equal. rewrite coef_Zpoly. unfold Bkpoly.
 rewrite take_nth; trivial; lia.
Qed.

Lemma alpha_square : SecondRoot.Mu vAf = CSeries (fun n => alpha n^2).
Proof.
 apply SecondRoot.Mu_series_square.
 - rewrite <- ex_pseries_1.
   apply CV_radius_inside.
   rewrite <- C_CV_radius_alt, Rabs_pos_eq by lra.
   apply alpha_radius.
 - intros z Hz. symmetry. apply CPowerSeries_unique, alpha_ok; lra.
Qed.

Lemma gamma_square : SecondRoot.Mu vB = CSeries (fun n => gamma n^2).
Proof.
 apply SecondRoot.Mu_series_square.
 - rewrite <- ex_pseries_1.
   apply CV_radius_inside.
   rewrite <- C_CV_radius_alt, Rabs_pos_eq by lra.
   apply gamma_radius.
 - intros z Hz. symmetry. apply CPowerSeries_unique, gamma_ok; lra.
Qed.

Definition alpha' := Re∘alpha.
Definition gamma' := Re∘gamma.

Lemma alpha_real n : alpha n = alpha' n.
Proof.
 rewrite <- (re_im_id (alpha n)).
 unfold alpha at 2.
 rewrite CPS_mult_real. now rewrite Cmult_0_r, Cplus_0_r.
 { intros m. unfold PS_poly. now rewrite coef_Zpoly. }
 { intros m. now rewrite grps_real. }
Qed.

Lemma gamma_real n : gamma n = gamma' n.
Proof.
 rewrite <- (re_im_id (gamma n)).
 unfold gamma at 2.
 rewrite CPS_mult_real. now rewrite Cmult_0_r, Cplus_0_r.
 { intros m. unfold vr1ps. apply CPS_mult_real.
   - intros m'. unfold PS_poly, coef.
     destruct m' as [|[|[|m']]]; simpl; try lra.
   - intros m'. unfold PS_pow. now ctor. }
 { intros m. unfold PS_poly. now rewrite coef_Zpoly. }
Qed.

Lemma alpha_square_real :
 CSeries (fun n => (alpha n)^2) = Series (fun n => (alpha' n)^2)%R.
Proof.
 rewrite <- CSeries_RtoC.
 - apply CSeries_ext. intros n. unfold "∘". rtoc. f_equal. apply alpha_real.
 - apply ex_series_square.
   apply ex_series_ext with (Cmod∘alpha).
   { intros n. unfold "∘". now rewrite <- Cmod_R, <- alpha_real. }
   rewrite <- ex_pseries_1.
   apply CV_radius_inside.
   rewrite <- C_CV_radius_alt, Rabs_pos_eq by lra.
   apply alpha_radius.
Qed.

Lemma gamma_square_real :
 CSeries (fun n => (gamma n)^2) = Series (fun n => (gamma' n)^2)%R.
Proof.
 rewrite <- CSeries_RtoC.
 - apply CSeries_ext. intros n. unfold "∘". rtoc. f_equal. apply gamma_real.
 - apply ex_series_square.
   apply ex_series_ext with (Cmod∘gamma).
   { intros n. unfold "∘". now rewrite <- Cmod_R, <- gamma_real. }
   rewrite <- ex_pseries_1.
   apply CV_radius_inside.
   rewrite <- C_CV_radius_alt, Rabs_pos_eq by lra.
   apply gamma_radius.
Qed.

Hypothesis Hyp1 : (mu A <= mu Bkpoly)%Z.
Hypothesis Hyp2 :
  Cmod (B k root) / root^k * (root - /root + sqrt (root^2-1)) < 1.

(*
Lemma Four : B k root = 0.
Proof.
Admitted.
*)

End Siegel.

(*
Lemma SiegelTheorem x : Pisot x -> mu 5 <= x.
Proof.
Admitted.

Lemma mu_non_Pisot_above_6 n : (6 <= n)%nat -> ~Pisot (mu n).
Proof.
 intros Hn.
 assert (mu n < mu 5).
 { replace n with ((n-6)+6)%nat by lia. clear Hn.
   induction (n-6)%nat.
   - apply mu_decr; lia.
   - eapply Rlt_trans; eauto. apply mu_decr; lia. }
 intros P. apply SiegelTheorem in P. lra.
Qed.
*)

End SiegelProof.
