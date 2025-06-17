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

Definition Pisot (x:R) :=
  1<x /\
  exists l : list C,
    IntPoly (linfactors (RtoC x :: l)) /\
    Forall (fun r => 0 < Cmod r < 1) l.

Lemma Pisot_nat_ge_2 (n:nat) : (2<=n)%nat -> Pisot n.
Proof.
 split.
 - apply le_INR in H. simpl in H. lra.
 - exists []; simpl; split; [|constructor].
   apply IntPoly_alt. exists [-Z.of_nat n;1]%Z.
   simpl. unfold "∘"; repeat f_equal; try ring.
   rewrite opp_IZR, <- INR_IZR_INZ, RtoC_opp. ring.
Qed.

Lemma Pisot_mu2 : Pisot (mu 2). (* Golden ratio *)
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

Lemma Pisot_mu3 : Pisot (mu 3).
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

Lemma Pisot_mu4 : Pisot (mu 4).
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

(** (mu 5) is the Plastic Ratio, the minimal Pisot number, root
    of X^3-X-1.
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
