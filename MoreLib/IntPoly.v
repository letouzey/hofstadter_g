From Coq Require Import Lia Reals Lra Morphisms QArith.
Close Scope Q. (* Issue with QArith. *)
From Hofstadter.HalfQuantum Require Import Complex Polynomial.
Require Import MoreTac MoreList MoreReals MoreSum MoreComplex MorePoly.
Local Open Scope R.
Local Open Scope C.
Local Open Scope poly_scope.
Local Coercion INR : nat >-> R.
Local Coercion IZR : Z >-> R.

(** * IntPoly : Polynomial in Z and in Q, Gauss Lemma *)

(** Integers seen as subsets of R, C. Polynomials in Z[x] *)

Definition Integer (x : R) := frac_part x = 0%R.
Definition CInteger (z : C) := Integer (Re z) /\ Im z = 0%R.
Definition IntPoly (p : Polynomial) := Forall CInteger p.

Definition Zpoly := map (RtoC∘IZR).

Lemma coef_Zpoly n p : coef n (Zpoly p) = nth n p Z0.
Proof.
 unfold coef, Zpoly. change 0%C with ((RtoC∘IZR) Z0).
 now rewrite map_nth.
Qed.

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

Lemma CInteger_big_sum (f : nat -> C) n :
 (forall k, (k < n)%nat -> CInteger (f k)) -> CInteger (big_sum f n).
Proof.
 induction n; simpl.
 - intros _. rewrite CInteger_alt. now exists 0%Z.
 - intros H. apply CInteger_plus.
   + apply IHn. intros k Hk. apply H; lia.
   + apply H. lia.
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

Lemma Integer_intpart r : Integer r -> r = Int_part r.
Proof.
 rewrite Integer_alt. intros (z & ->). now rewrite Int_part_IZR.
Qed.

Lemma CInteger_intpart c : CInteger c -> c = Int_part (Re c).
Proof.
 rewrite CInteger_alt. intros (z & ->).
 now rewrite re_RtoC, Int_part_IZR.
Qed.

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

(** monicify : scale a polynomial to obtain 1 as topcoef *)

Definition monicify p := [/topcoef p]*,p.

Lemma monicify_ok p : ~Peq p [] -> monic (monicify p).
Proof.
 intros H. red. unfold monicify. rewrite topcoef_mult, topcoef_singl.
 rewrite <- topcoef_0_iff in H. now field.
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

Lemma monicify_degree p : ~Peq p [] -> degree (monicify p) = degree p.
Proof.
 intros H.
 unfold monicify. rewrite Pmult_degree, const_degree; trivial.
 rewrite <- topcoef_0_iff in H. apply nonzero_div_nonzero in H.
 change (~Peq [/topcoef p] []). now rewrite <- topcoef_0_iff, topcoef_singl.
Qed.

Lemma RatPoly_monicify p : RatPoly p -> RatPoly (monicify p).
Proof.
 intros. apply RatPoly_mult; trivial.
 constructor; [|constructor]. now apply CRational_inv, RatPoly_topcoef.
Qed.

(** Any monic nonzero polynomial in Z[X] has a root whose module is 0 or
    at least 1. *)

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

(** The Euclidean division of polynomials stays in Q[X] *)

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

(** The Euclidean division of polynomials stays in Z[X] at least
    when the divisor is monic. *)

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

(** Auxiliary notions for the Gauss Lemma below. In particular,
    Zcontent is the gcd of all coefficients (seen as [list Z]). *)

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

(** Reducibility in Z[X] and Q[X] *)

Definition Zreducible (p:Polynomial) :=
  exists q r,
    Peq p (Pmult q r) /\ IntPoly q /\ IntPoly r /\
    (0 < degree q < degree p)%nat.

Definition Qreducible (p:Polynomial) :=
  exists q r,
    Peq p (Pmult q r) /\ RatPoly q /\ RatPoly r /\
    (0 < degree q < degree p)%nat.

(** Gauss Lemma : any monic polynomial in Z[X] which is reducible
    in Q[X] is also reducible in Z[X]. *)

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
