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

Lemma Rational_Z (n:Z) : Rational (IZR n).
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

Lemma CRational_Z (n:Z) : CRational (IZR n).
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

Lemma Integer_alt (x : R) : Integer x <-> exists n:Z, x = IZR n.
Proof.
 split.
 - apply fp_nat.
 - intros (n, ->). red. rewrite <- (Rplus_0_l (IZR n)).
   now rewrite frac_part_addZ, fp_R0.
Qed.

Lemma CInteger_alt (z : C) : CInteger z <-> exists n:Z, z = IZR n.
Proof.
 unfold CInteger. rewrite Integer_alt.
 split.
 - intros ((n,E1),E2). exists n. destruct z; simpl in *; now subst.
 - intros (n,->). simpl; split; trivial. now exists n.
Qed.

Lemma Integer_Z (n:Z) : Integer (IZR n).
Proof.
 rewrite Integer_alt. now exists n.
Qed.

Lemma CInteger_Z (n:Z) : CInteger (IZR n).
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

Lemma IntPoly_coef p n : IntPoly p -> CInteger (coef n p).
Proof.
 rewrite IntPoly_alt. intros (q & ->). unfold coef, Zpoly.
 change 0%C with ((RtoC∘IZR) Z0).
 rewrite map_nth. apply CInteger_alt. now eexists.
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
     ([RtoC (IZR (lcm_denoms l))] *, Qpoly l).
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
 RatPoly p -> exists z, z<>Z0 /\ IntPoly ([RtoC (IZR z)]*,p).
Proof.
 rewrite RatPoly_alt'. intros (q & E).
 exists (lcm_denoms q). split. apply lcm_denoms_nz.
 rewrite IntPoly_alt'. exists (PolyQ_factor q). symmetry.
 rewrite E. apply PolyQ_factor_ok.
Qed.

Definition Qcontent (l : list Q) :=
  (inject_Z (Zcontent (PolyQ_factor l)) / inject_Z (lcm_denoms l))%Q.

Lemma coef_P0 k : coef k [] = 0.
Proof.
 now destruct k.
Qed.

Lemma Pmult_coef p q n:
 coef n (p*,q) = big_sum (fun k => coef k p * coef (n-k) q) (S n).
Proof.
 revert q n.
 induction p; intros.
 - simpl. rewrite coef_P0. rewrite big_sum_0. lca.
   intros k. rewrite coef_P0. lca.
 - simpl. rewrite <- Pscale_alt, Pplus_coef, Pscale_coef.
   replace (n-n)%nat with O by lia.
   destruct n as [|n]. unfold coef; simpl; lca.
   change (coef (S n) (0 :: _)) with (coef n (p*,q)).
   change (coef (S n) (a::p)) with (coef n p).
   rewrite IHp.
   symmetry. rewrite big_sum_shift. rewrite <- big_sum_extend_r.
   change (coef 0 (a::p)) with a.
   replace (n-n)%nat with O by lia.
   change Gplus with Cplus. rewrite Nat.sub_0_r. ring_simplify.
   rewrite <- !Cplus_assoc. f_equal. apply Cplus_comm.
Qed.

Global Program Instance Z_is_monoid : Monoid Z :=
 { Gzero := Z0 ; Gplus := Z.add }.
Solve All Obligations with lia.

Lemma Zpoly_coef (l : list Z) i : coef i (Zpoly l) = IZR (nth i l Z0).
Proof.
 unfold coef, Zpoly, "∘". apply (map_nth (fun x => RtoC (IZR x))).
Qed.

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
 IZR (big_sum (fun k => nth k p Z0 * nth (n-k) q Z0)%Z (S n)).
Proof.
 rewrite Pmult_coef, big_sum_IZR, big_sum_RtoC.
 apply big_sum_eq_bounded. intros x Hx.
 rewrite !Zpoly_coef. unfold "∘". now rewrite mult_IZR, RtoC_mult.
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
 set (c1 := RtoC (IZR c)) in *.
 set (q1 := [c1] *, q) in *.
 destruct (RatPoly_scal_IntPoly r Hr) as (d & Hd & Hr1).
 set (d1 := RtoC (IZR d)) in *.
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
 set (c2 := RtoC (IZR (Zcontent q1'))) in *.
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
 set (d2 := RtoC (IZR (Zcontent r1'))) in *.
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
 assert (E1 : c1 * d1 = RtoC (IZR g) * RtoC (IZR m)).
 { unfold c1, d1. rewrite <- !RtoC_mult, <- !mult_IZR. do 2 f_equal.
   unfold m. rewrite <- Znumtheory.Zdivide_Zdiv_eq; trivial.
   apply Z.gcd_divide_l. }
 rewrite E1 in E.
 assert (Hm : m <> Z0).
 { intros ->. rewrite Cmult_0_r in E1.
   unfold c1, d1 in E1. rewrite <- !RtoC_mult, <- !mult_IZR in E1.
   injection E1 as E1. apply not_0_IZR in E1; trivial. lia. }
 assert (E2 : c2 * d2 = RtoC (IZR g) * RtoC (IZR l)).
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
 assert (E1 : Peq [RtoC (IZR g) * RtoC (IZR m)]
                  ([RtoC (IZR g)] *, [RtoC (IZR m)])).
 { simpl. now rewrite Cplus_0_r. }
 rewrite E1 in E.
 assert (E2 : Peq [RtoC (IZR g) * RtoC (IZR l)]
                  ([RtoC (IZR g)] *, [RtoC (IZR l)])).
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
 rewrite Pscale_coef, Zpoly_coef, <- RtoC_mult, <- mult_IZR in E'.
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

Lemma roots_nz' : ~In 0 (RtoC root :: roots).
Proof.
 simpl. intros [[= H]|H]. red in Hroots; lra. now apply roots_nz.
Qed.

Let p := Zpoly coefs.

Lemma Root_nz : ~Root 0 p.
Proof.
 unfold p. rewrite Hcoefs, <- linfactors_roots. apply roots_nz'.
Qed.

Let sgn := Z.sgn (nth 0 coefs Z0).

Let f (x : C) := IZR sgn * Peval p x / Peval (reciprocal p) x.

Lemma ff x : ~Root x p -> ~Root (/x) p -> x <> 0 -> f x * f (/x) = 1.
Proof.
 intros H1 H2 H3. unfold f.
 rewrite !Peval_reciprocal, Cinv_inv, Cpow_inv; trivial.
 2:{ now apply nonzero_div_nonzero. }
 2:{ contradict H1. now rewrite H1. }
 2:{ contradict H1. now rewrite H1. }
 field_simplify.
 2:{ repeat split; trivial. now apply Cpow_nz. }
 { unfold sgn.
   assert (H0 := Root_nz).
   unfold Root in H0. rewrite Peval_0 in H0. unfold coef, Zpoly in H0.
   change 0 with ((RtoC∘IZR) Z0) in H0 at 1.
   unfold p, Zpoly in H0. rewrite map_nth in H0.
   destruct nth; simpl; try ring. now destruct H0. }
Qed.

Definition PS_f :=
  CPS_mult (PS_poly ([IZR sgn * /Peval p 0] *, p))
           (PS_inv_linfactors (map Cinv (RtoC root::roots))).

Lemma invroot_le_min_Cmod :
  Rbar.Rbar_le (/ root)%R (min_Cmod_list (map Cinv (RtoC root :: roots))).
Proof.
 unfold min_Cmod_list. simpl map.
 cbn -[Rbar.Rbar_min Rbar.Rbar_le].
 apply Rbar.Rbar_min_case.
 - rewrite <- RtoC_inv, Cmod_R, Rabs_pos_eq.
   apply Rbar.Rbar_le_refl. apply Rlt_le, Rinv_0_lt_compat.
   destruct Hroots; lra.
 - change (Rbar.Rbar_le (/root)%R (min_Cmod_list (map Cinv roots))).
   apply Rbar.Rbar_lt_le. apply min_Cmod_list_spec, Forall_forall.
   intros y. rewrite in_map_iff. intros (z & <- & IN).
   red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
   rewrite Cmod_inv.
   apply Rinv_lt_contravar. apply Rmult_lt_0_compat; lra. lra.
Qed.

Lemma PS_f_radius : Rbar.Rbar_le (/root)%R (C_CV_radius PS_f).
Proof.
 unfold PS_f.
 eapply Rbar.Rbar_le_trans; [|apply C_CV_radius_mult].
 rewrite PS_poly_radius.
 apply Rbar.Rbar_min_case; [simpl; trivial|].
 eapply Rbar.Rbar_le_trans; [|apply PS_inv_linfactors_radius].
 - apply invroot_le_min_Cmod.
 - rewrite in_map_iff. intros (r & Hr & IN).
   rewrite Cinv_eq_0_iff in Hr. subst r. now apply roots_nz'.
Qed.

Lemma below_invroot x : Cmod x < / root -> x <> 0 -> ~Root (/ x) p.
Proof.
 intros H1 H2.
 unfold p. rewrite Hcoefs.
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

Lemma PS_f_ok x : Cmod x < /root -> is_CPowerSeries PS_f x (f x).
Proof.
 intros Hx.
 unfold PS_f.
 replace (f x) with ((IZR sgn * /Peval p 0 * Peval p x) *
                     (Peval p 0 * /Peval (reciprocal p) x)).
 2:{ unfold f. field. split; try apply Root_nz.
     destruct (Ceq_dec x 0) as [Y|N].
     - subst. rewrite Peval_reciprocal_0.
       unfold p. rewrite Hcoefs, linfactors_monic. intros [=H]; lra.
     - rewrite Peval_reciprocal; trivial.
       + intros H. apply Cmult_integral in H. destruct H.
         apply below_invroot in H; trivial.
         now apply (Cpow_nz x (degree p)) in N.
       + rewrite <- topcoef_0_iff.
         unfold p. rewrite Hcoefs, linfactors_monic. intros [=H]; lra. }
 apply is_CPS_mult.
 - rewrite <- (Pconst_eval (_ * /Peval _ 0) x) at 2.
   rewrite <- Pmult_eval. apply PS_poly_ok.
 - unfold p. rewrite Hcoefs, reciprocal_revfactors by apply roots_nz'.
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

Lemma PS_f_eqn n :
  CPS_mult PS_f (PS_poly (reciprocal p)) n
  = PS_poly ([RtoC (IZR sgn)] *, p) n.
Proof.
 apply CPowerSeries_coef_ext.
 - eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
   rewrite PS_poly_radius.
   apply Rbar.Rbar_min_case; [|simpl; trivial].
   eapply Rbar.Rbar_lt_le_trans; [|apply PS_f_radius; trivial]. simpl.
   red in Hroots. apply Rinv_0_lt_compat. lra.
 - now rewrite PS_poly_radius.
 - assert (Hr : 0 < /root).
   { apply Rinv_0_lt_compat. red in Hroots. lra. }
   exists (mkposreal _ Hr). intros y Hy.
   change (Rabs (y-R0) < /root) in Hy. rewrite Rminus_0_r in Hy.
   rewrite <- Cmod_R in Hy.
   rewrite CPowerSeries_mult.
   2:{ eapply Rbar.Rbar_lt_le_trans; [|apply PS_f_radius]; trivial. }
   2:{ now rewrite PS_poly_radius. }
   do 2 rewrite (CPowerSeries_unique _ _ _ (PS_poly_ok _ _)).
   rewrite (CPowerSeries_unique _ _ _ (PS_f_ok _ Hy)).
   rewrite Pmult_eval, Pconst_eval.
   unfold f. field.
   { destruct (Ceq_dec y 0) as [->|N].
     - rewrite Peval_reciprocal_0. unfold p.
       rewrite Hcoefs, linfactors_monic. intros [=H]; lra.
     - rewrite Peval_reciprocal; trivial.
       2:{ rewrite <- topcoef_0_iff. unfold p.
           rewrite Hcoefs, linfactors_monic. intros [=H]; lra. }
       intros H. apply Cmult_integral in H. destruct H.
       apply below_invroot in H; trivial.
       now apply (Cpow_nz y (degree p)) in N. }
Qed.

Lemma PS_f_CInteger n : CInteger (PS_f n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 generalize (PS_f_eqn n).
 unfold PS_poly. rewrite Pscale_coef.
 unfold p, CPS_mult. rewrite Zpoly_coef, <- RtoC_mult, <- mult_IZR.
 rewrite <- big_sum_sum_n, <- big_sum_extend_r.
 simpl. replace (n-n)%nat with 0%nat by lia.
 rewrite <- Peval_0, Peval_reciprocal_0.
 rewrite Hcoefs, linfactors_monic, Cmult_1_r.
 set (bs := big_sum _ _).
 intros E. replace (PS_f n) with (IZR (sgn * nth n coefs 0%Z) - bs).
 2:{ rewrite <- E. lca. }
 clear E.
 apply CInteger_plus. rewrite CInteger_alt. now eexists.
 replace (-bs) with ((-1)*bs) by ring.
 apply CInteger_mult. rewrite CInteger_alt. now exists (-1)%Z.
 apply big_sum_CInteger.
 intros k Hk. apply CInteger_mult. now apply IH.
 destruct (Nat.le_gt_cases (n-k) (degree p)).
 - rewrite reciprocal_coef by trivial. apply IntPoly_coef.
   rewrite IntPoly_alt. now eexists.
 - rewrite reciprocal_coef_0 by trivial.
   rewrite CInteger_alt. now exists 0%Z.
Qed.

Definition g x :=
  IZR sgn * Peval p x / Peval (reciprocal (linfactors roots)) x.

Definition g_f x : x <> /root -> g x = (1-root*x) * f x.
Proof.
 intros Hx.
 unfold g, f, Cdiv. rewrite !Cmult_assoc.
 rewrite (Cmult_comm (_-_)). rewrite <- !Cmult_assoc. f_equal.
 rewrite (Cmult_comm (_-_)). rewrite <- !Cmult_assoc. f_equal.
 unfold p. rewrite Hcoefs, reciprocal_linfactors_cons by apply roots_nz'.
 rewrite Pmult_eval.
 rewrite Cinv_mult, Cmult_comm, Cmult_assoc.
 rewrite <- (Cmult_1_l (/ _)) at 1. f_equal.
 unfold Peval. simpl. field. simpl. contradict Hx.
 apply Cmult_eq_reg_l with (RtoC root).
 2:{ generalize roots_nz'. simpl; tauto. }
 rewrite Cinv_r. 2:{ generalize roots_nz'. simpl; tauto. }
 symmetry. apply Cminus_eq_0. rewrite <- Hx. ring.
Qed.

Definition PS_g :=
  CPS_mult (PS_poly ([IZR sgn * /Peval (linfactors roots) 0] *, p))
           (PS_inv_linfactors (map Cinv roots)).

Lemma PS_g_radius : Rbar.Rbar_lt 1%R (C_CV_radius PS_g).
Proof.
 unfold PS_g.
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

Lemma PS_g_ok x :
  Cmod x <= 1 -> is_CPowerSeries PS_g x (g x).
Proof.
 intros Hx.
 unfold PS_g.
 replace (g x) with ((IZR sgn * /Peval (linfactors roots) 0 * Peval p x) *
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

Lemma PS_g_eqn n : PS_g n = CPS_mult PS_f (PS_poly [1;-root]) n.
Proof.
 apply CPowerSeries_coef_ext.
 - eapply Rbar.Rbar_lt_trans; [|apply PS_g_radius; trivial]. simpl. lra.
 - eapply Rbar.Rbar_lt_le_trans; [|apply C_CV_radius_mult].
   rewrite PS_poly_radius.
   apply Rbar.Rbar_min_case; [|simpl; trivial].
   eapply Rbar.Rbar_lt_le_trans; [|apply PS_f_radius; trivial]. simpl.
   red in Hroots. apply Rinv_0_lt_compat. lra.
 - assert (Hr : 0 < /root).
   { apply Rinv_0_lt_compat. red in Hroots. lra. }
   exists (mkposreal _ Hr). intros y Hy.
   change (Rabs (y-R0) < /root) in Hy. rewrite Rminus_0_r in Hy.
   rewrite <- Cmod_R in Hy.
   rewrite CPowerSeries_mult.
   2:{ eapply Rbar.Rbar_lt_le_trans; [|apply PS_f_radius]; trivial. }
   2:{ now rewrite PS_poly_radius. }
   rewrite (CPowerSeries_unique _ _ _ (PS_poly_ok _ _)).
   rewrite (CPowerSeries_unique _ _ _ (PS_f_ok _ Hy)).
   assert (Hy' : Cmod y <= 1).
   { apply Rle_trans with (/root)%R; try lra. rewrite <- Rinv_1.
     red in Hroots. apply Rinv_le_contravar; lra. }
   rewrite (CPowerSeries_unique _ _ _ (PS_g_ok _ Hy')).
   rewrite cons_eval, Pconst_eval. rewrite g_f. ring.
   intros H. rewrite H in Hy. rewrite <- RtoC_inv, Cmod_R in Hy.
   generalize (Rle_abs (/root)); lra.
Qed.

Lemma PS_g_square : ex_series (fun n => (PS_g n)^2).
Proof.
 apply ex_series_Cmod.
 eapply ex_series_ext.
 { intros n. unfold "∘". symmetry. now rewrite Cmod_pow. }
 apply ex_series_square. rewrite <- ex_pseries_1. apply CV_radius_inside.
 unfold "∘".
 erewrite CV_radius_ext.
 2:{ intros n. now rewrite Rabs_pos_eq by apply Cmod_ge_0. }
 change (fun n => Cmod (PS_g n)) with (Cmod ∘ PS_g).
 rewrite <- C_CV_radius_alt. rewrite Rabs_pos_eq by lra.
 apply PS_g_radius.
Qed.

Lemma One_aux : 1 + root^2 = CSeries (fun n => (PS_g n)^2).
Proof.
 rewrite <- SecondRoot.Mu_series_square with (g:=g).
 2:{ rewrite <- ex_pseries_1. apply CV_radius_inside.
     rewrite <- C_CV_radius_alt. rewrite Rabs_pos_eq by lra.
     apply PS_g_radius. }
 2:{ intros z Hz. symmetry. apply CPowerSeries_unique, PS_g_ok. lra. }
 symmetry. unfold SecondRoot.Mu.
 rewrite (RInt_ext (V:=C_CNM))
  with (g := fun t => (1 - root * Cexp t)*(1 - root * Cexp (-t))).
 2:{ intros t _. rewrite !g_f.
     2:{ intros E. apply (f_equal Cmod) in E. rewrite Cmod_Cexp in E.
         rewrite Cmod_inv, Cmod_R, Rabs_pos_eq in E by (red in Hroots; lra).
         apply (f_equal Rinv) in E. rewrite Rinv_1, Rinv_inv in E.
         red in Hroots; lra. }
     2:{ intros E. apply (f_equal Cmod) in E. rewrite Cmod_Cexp in E.
         rewrite Cmod_inv, Cmod_R, Rabs_pos_eq in E by (red in Hroots; lra).
         apply (f_equal Rinv) in E. rewrite Rinv_1, Rinv_inv in E.
         red in Hroots; lra. }
     rewrite (Cmult_comm _ (f (Cexp (-t)))).
     rewrite !Cmult_assoc. f_equal.
     rewrite <- Cmult_assoc. rewrite <- (Cmult_1_r (1 - _)) at 2. f_equal.
     rewrite Cexp_neg. apply ff.
     { unfold p. rewrite Hcoefs. rewrite <- linfactors_roots.
       intros [E|IN].
       - apply (f_equal Cmod) in E. rewrite Cmod_Cexp in E.
         rewrite Cmod_R, Rabs_pos_eq in E; red in Hroots; lra.
       - red in Hroots. rewrite Forall_forall in Hroots. apply Hroots in IN.
         rewrite Cmod_Cexp in IN; lra. }
     { unfold p. rewrite Hcoefs. rewrite <- linfactors_roots, <- Cexp_neg.
       intros [E|IN].
       - apply (f_equal Cmod) in E. rewrite Cmod_Cexp in E.
         rewrite Cmod_R, Rabs_pos_eq in E; red in Hroots; lra.
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

Lemma PS_g_0 : PS_g 0 = PS_f 0.
Proof.
 rewrite PS_g_eqn.
 unfold CPS_mult. rewrite <- big_sum_sum_n. unfold PS_poly, coef. simpl.
 ring.
Qed.

Lemma PS_g_S n : PS_g (S n) = PS_f (S n) - root * PS_f n.
Proof.
 rewrite PS_g_eqn.
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
  1 + root^2 = (PS_f 0)^2 + CSeries (fun n => (PS_f (S n) - root * PS_f n)^2).
Proof.
 rewrite One_aux. rewrite CSeries_shift by apply PS_g_square.
 f_equal.
 - now rewrite PS_g_0.
 - unfold "∘". apply CSeries_ext. intros n. f_equal. apply PS_g_S.
Qed.

Lemma PS_f_0 : PS_f 0 = IZR (Z.abs (nth 0 coefs Z0)).
Proof.
 generalize (PS_f_eqn 0).
 unfold CPS_mult, PS_poly. rewrite Pscale_coef, sum_O, reciprocal_coef by lia.
 rewrite Nat.sub_0_r, <- topcoef_alt.
 unfold p at 1. rewrite Hcoefs, linfactors_monic, Cmult_1_r.
 intros ->. unfold sgn. unfold p, coef, Zpoly.
 change 0 with ((RtoC∘IZR) Z0). rewrite map_nth. unfold "∘".
 rewrite <- RtoC_mult, <- mult_IZR. f_equal. f_equal. lia.
Qed.

Lemma coefs0_nz : nth 0 coefs Z0 <> Z0.
Proof.
 intros E.
 apply roots_nz'. rewrite linfactors_roots, <- Hcoefs. red.
 rewrite Peval_0. unfold coef, Zpoly.
 change 0 with ((RtoC∘IZR) Z0). rewrite map_nth. unfold "∘". now rewrite E.
Qed.

Section PS_f_eventually_zero.

Hypothesis PS_f_ez : Hierarchy.eventually (fun n : nat => PS_f n = 0).

Lemma PS_f_poly : exists q, forall n, PS_f n = PS_poly q n.
Proof.
 destruct PS_f_ez as (n & Hn).
 exists (take n PS_f). intros m. unfold PS_poly, coef, take.
 destruct (Nat.ltb_spec m n).
 - rewrite nth_map_indep with (d':=O) by now rewrite seq_length.
   now rewrite seq_nth.
 - rewrite nth_overflow. now apply Hn. now rewrite map_length, seq_length.
Qed.

(* MOVE *)
Lemma CPS_mult_poly q r n :
 CPS_mult (PS_poly q) (PS_poly r) n = PS_poly (q *, r) n.
Proof.
 unfold CPS_mult, PS_poly. now rewrite Pmult_coef, big_sum_sum_n.
Qed.

(* MOVE *)
Lemma Peq_via_coef q r : Peq q r <-> forall n, coef n q = coef n r.
Proof.
 split.
 - intros E n. now rewrite E.
 - intros E. apply Peq_iff.
   assert (E' : forall n, coef n (compactify q) = coef n (compactify r)).
   { intros n. rewrite !compactify_coef. apply E. }
   clear E.
   apply nth_ext with (d:=0) (d':=0); [|intros; apply E'].
   destruct (compactify_last q) as [Hq|Hq], (compactify_last r) as [Hr|Hr].
   + now rewrite Hq, Hr.
   + exfalso. rewrite Hq in E'. rewrite last_nth in Hr.
     unfold coef in E'. rewrite <- E' in Hr.
     now destruct (length _-1)%nat in Hr.
   + exfalso. rewrite Hr in E'. rewrite last_nth in Hq.
     unfold coef in E'. rewrite E' in Hq.
     now destruct (length _-1)%nat in Hq.
   + destruct (Nat.compare_spec (length (compactify q))
                                (length (compactify r)));
      trivial || exfalso.
     * apply Hr. rewrite last_nth. unfold coef in E'.
       rewrite <- E'. apply nth_overflow. lia.
     * apply Hq. rewrite last_nth. unfold coef in E'.
       rewrite E'. apply nth_overflow. lia.
Qed.

Lemma PF_f_ez_p_eqn : exists q, Peq ([RtoC (IZR sgn)] *, p) (q *, reciprocal p).
Proof.
 destruct PS_f_poly as (q,Hq).
 exists q. apply Peq_via_coef. intros n.
 change (coef n ([RtoC (IZR sgn)] *, p))
  with (PS_poly ([RtoC (IZR sgn)] *, p) n).
 rewrite <- PS_f_eqn.
 change (coef n (q *, reciprocal p)) with (PS_poly (q *, reciprocal p) n).
 rewrite <- CPS_mult_poly.
 unfold CPS_mult. apply sum_n_ext. intros m. now rewrite Hq.
Qed.

(* MOVE *)
Lemma reciprocal_degree q :
 coef 0 q <> 0 -> degree (reciprocal q) = degree q.
Proof.
 intros H.
 unfold degree, reciprocal. unfold compactify at 1.
 rewrite rev_involutive, rev_length.
 rewrite <- compactify_coef in H.
 destruct (compactify q) as [|x l]; simpl; try easy.
 unfold coef in H; simpl in H. now destruct Ceq_dec.
Qed.

Lemma PF_f_ez_p_eqn' : exists c, c<>0 /\ Peq p ([c] *, reciprocal p).
Proof.
 destruct PF_f_ez_p_eqn as (q & E).
 assert (NZ : RtoC (IZR sgn) <> 0).
 { unfold sgn. intros [=H]. apply eq_IZR in H.
   rewrite Z.sgn_null_iff in H. revert H. apply coefs0_nz. }
 assert (Hq : ~Peq q []).
 { apply degree_mor in E. rewrite Pscale_degree in E by trivial.
   intros H. revert E. rewrite H. change (degree ([] *, _)) with O.
   unfold p. rewrite Hcoefs. now rewrite linfactors_degree. }
 assert (Hr : ~Peq (reciprocal p) []).
 { apply degree_mor in E. rewrite Pscale_degree in E by trivial.
   intros H. revert E. rewrite H, Pmult_0_r. change (degree []) with O.
   unfold p. rewrite Hcoefs. now rewrite linfactors_degree. }
 assert (degree q = O).
 { apply degree_mor in E. rewrite Pscale_degree in E by trivial.
   rewrite Pmult_degree in E; trivial.
   rewrite reciprocal_degree in E; try lia.
   unfold p, Zpoly, coef. change 0 with ((RtoC∘IZR) Z0) at 1.
   rewrite map_nth. intros [=H]. apply eq_IZR in H. revert H.
   apply coefs0_nz. }
 destruct q as [|c q].
 - exfalso. now apply Hq.
 - rewrite degree_cons in H.
   destruct Peq_0_dec as [Hq'|Hq']; try easy. rewrite Hq' in *.
   exists (c*IZR sgn). split.
   + intros M. apply Cmult_integral in M. destruct M as [M|M]; try easy.
     rewrite M in Hq. apply Hq. apply C0_Peq_nil.
   + replace [c * IZR sgn] with ([RtoC (IZR sgn)] *, [c]).
     2:{ simpl. f_equal. lca. }
     rewrite Pmult_assoc, <- E, <- Pmult_assoc.
     replace ([_]*,[_]) with [1]. symmetry; apply Pmult_1_l.
     simpl. f_equal. rewrite Cplus_0_r, <- RtoC_mult, <- mult_IZR.
     f_equal. f_equal. unfold sgn in NZ|-*.
     destruct (Z.sgn_spec (nth 0 coefs Z0)) as [(_,SG)|[(_,SG)|(_,SG)]];
      now rewrite SG in *.
Qed.

Lemma PF_f_ez_roots_carac r : In r roots -> r = /root.
Proof.
 destruct PF_f_ez_p_eqn' as (c & Hc & E).
 intros Hr. destruct Hroots as (H1 & _ & H2). rewrite Forall_forall in H2.
 assert (Hr' : Root r p).
 { unfold p. rewrite Hcoefs, <- linfactors_roots. now right. }
 rewrite E in Hr'. red in Hr'.
 rewrite Pmult_eval, Pconst_eval in Hr'. apply Cmult_integral in Hr'.
 destruct Hr' as [Hr'|Hr']; try easy.
 apply reciprocal_root in Hr'.
 2:{ apply Cmod_gt_0. now apply H2. }
 unfold p in Hr'. rewrite Hcoefs in Hr'. apply linfactors_roots in Hr'.
 destruct Hr' as [Hr'|Hr'].
 - now rewrite Hr', Cinv_inv.
 - apply H2 in Hr, Hr'. destruct Hr' as (H3,H4).
   rewrite Cmod_inv in H4. rewrite <- Rinv_1 in H4.
   apply Rcomplements.Rinv_lt_cancel in H4; lra.
Qed.

Lemma PF_f_ez_degree_0 : degree p = 0%nat -> False.
Proof.
 unfold p. now rewrite Hcoefs, linfactors_degree.
Qed.

Lemma PF_f_ez_degree_1 : degree p = 1%nat -> 2 <= root.
Proof.
 intros D.
 unfold p in D. rewrite Hcoefs, linfactors_degree in D. simpl in D.
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
 apply IZR_le. assert (1 < n)%Z; try lia. apply lt_IZR. now rewrite <- H.
Qed.

Lemma PF_f_ez_degree_2 : degree p = 2%nat -> 2 < root.
Proof.
 intros D.
 assert (R : Root root p).
 { unfold p. rewrite Hcoefs. apply linfactors_roots. now left. }
 replace roots with [/root] in *.
 2:{ unfold p in D. rewrite Hcoefs, linfactors_degree in D. simpl in D.
     injection D as D. assert (H := PF_f_ez_roots_carac).
     destruct roots as [|x l] eqn:E; try easy.
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
   assert (Hp : Peq p (linfactors [1;1])).
   { unfold p. rewrite Hcoefs. simpl. apply eq_Peq.
     f_equal. ring. f_equal. ring. f_equal. ring. }
   rewrite Hp in R. apply linfactors_roots in R. simpl in R.
   destruct Hroots as (LT & _). destruct R as [[= R]|[[= R]|[ ]]]; lra. }
 assert (3 <= root + /root).
 { rewrite Integer_alt in INT. destruct INT as (n & Hn).
   rewrite Hn in H |- *. apply lt_IZR in H. apply IZR_le.
   rewrite <- RtoC_inv, <- RtoC_plus, Hn in N.
   assert (n <> 2%Z). { contradict N. now subst. }
   lia. }
 destruct (Rle_lt_dec root 2); try easy.
 destruct Hroots as (LT & _).
 assert (/root < 1). { rewrite <- Rinv_1. apply Rinv_lt_contravar; lra. }
 lra.
Qed.

Lemma PF_f_ez_degree_3 : (3 <= degree p)%nat -> False.
Proof.
 intros D.
 assert (E := Peval_0 p).
 unfold p in E. rewrite Hcoefs in E at 1.
 rewrite Peval_linfactors in E.
 unfold coef, Zpoly in E.
 change 0 with ((RtoC∘IZR) Z0) in E at 2.
 rewrite map_nth in E.
 assert (R : roots = repeat (/root) (degree p - 1)).
 { replace (degree p - 1)%nat with (length roots).
   2:{ unfold p. rewrite Hcoefs. rewrite linfactors_degree. simpl. lia. }
   apply Forall_eq_repeat. apply Forall_forall.
   intros r Hr. symmetry. now apply PF_f_ez_roots_carac. }
 set (d := (degree p - 1)%nat) in *.
 set (n := nth 0 coefs Z0) in *. unfold "∘" in E.
 replace d with (S (d-1)) in R by lia.
 rewrite R in E. simpl in E.
 rewrite Cmult_assoc in E.
 replace ((0-_)*(0-_)) with 1 in E.
 2:{ field. intros [=H]. destruct Hroots. lra. }
 rewrite Cmult_1_l in E.
 (* E donne (/root)^(d-1) entier et d-1>0, ce qui est impossible
    vu que 1<root donc 0</root<1 *)
Admitted.

End PS_f_eventually_zero.

Hypothesis PS_f_nez : ~ Hierarchy.eventually (fun n : nat => PS_f n = 0).

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
