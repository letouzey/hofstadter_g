From Coq Require Import Lia Reals Lra Morphisms.
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

(** Integers seen as subsets of R, C. Polynomials in Z[x] *)

Definition Integer (x : R) := frac_part x = 0%R.
Definition CInteger (z : C) := Integer (Re z) /\ Im z = 0%R.
Definition IntPoly (p : Polynomial) := Forall CInteger p.

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
  IntPoly p <-> exists (q : list Z), p = map (RtoC∘IZR) q.
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

Lemma IntPoly_coef p n : IntPoly p -> CInteger (coef n p).
Proof.
 rewrite IntPoly_alt. intros (q & ->). unfold coef.
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

(*
Lemma PisotPolyUnique x p q : PisotPoly x p -> PisotPoly x q -> Peq p q.
Proof.
Admitted.
*)

(** Siegel Theorem : the smallest Pisot number is the Plastic Ratio.
    (Ref: Algbraic numbers whose conjugates lie in the unit circle, 1944) *)

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
