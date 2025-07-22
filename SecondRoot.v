From Coq Require Import Lia Reals Lra QArith Morphisms.
Close Scope Q. (* Issue with QArith. *)
From Coquelicot Require Import Hierarchy Continuity Derive AutoDerive
 RInt RInt_analysis Series PSeries.
From Hofstadter.HalfQuantum Require Import Complex Polynomial.
Require Import MoreTac MoreList MoreReals MoreSum MoreComplex MoreLim.
Require Import MorePSeries MorePoly IntPoly MoreIntegral ThePoly Mu.
Require Import Siegel GenFib GenG Freq.
Local Open Scope R.
Local Open Scope C.
Local Open Scope poly_scope.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * The second largest root of ThePoly has modulus>1 for k>=6

  We recall that ThePoly(k)(x) is x^k-x^(k-1)-1. First, we apply
  Siegel's theorem: the Plastic Ratio (root of x^3-x-1, approx 1.3247...)
  is the smallest Pisot number. See now the file Siegel.v for a full proof.
  This provides here a secondary root of modulus>=1. Moreover we prove
  here that this largest secondary root cannot have modulus 1, otherwise
  [mu k] would be a Salem number, hence its minimal polynomial would
  be self-reciprocal and [1/mu k] also a root of this minimal polynomial
  and hence of ThePoly, contradiction. *)

Definition SalemConjugates (x:R)(l : list C) :=
  1<x /\
  let p := linfactors (RtoC x :: l) in
  IntPoly p /\ ~Zreducible p /\
  (exists r, In r l /\ Cmod r = 1%R) /\
  (forall r, In r l -> Cmod r <= 1).

Definition Salem (x:R) := exists l, SalemConjugates x l.

Definition SalemPoly (x:R)(p : Polynomial) :=
  exists l, SalemConjugates x l /\ Peq p (linfactors (RtoC x :: l)).

Lemma Salem_alt x : Salem x <-> exists p, SalemPoly x p.
Proof.
 unfold Salem. split.
 - intros (l & Hl). exists (linfactors (RtoC x :: l)). now exists l.
 - intros (p & (l & Hl & Hl')). now exists l.
Qed.

Lemma SalemIntPoly x p : SalemPoly x p -> IntPoly p.
Proof.
 intros (l & H1 & H2). rewrite H2. apply H1.
Qed.

Lemma SalemPolyRoot x p : SalemPoly x p -> Root x p.
Proof.
 intros (l & H1 & H2). rewrite H2. rewrite <- linfactors_roots. now left.
Qed.

Lemma SalemPoly_no_0_root x p : SalemPoly x p -> ~Root 0 p.
Proof.
 intros (l & Hl & E).
 unfold Root. rewrite Peval_0. destruct Hl as (Hx & P1 & P2 & _ & _).
 rewrite <- E in P2. contradict P2.
 exists _X_, (tl p); repeat split.
 - unfold _X_. rewrite cons_0_mult, Pmult_1_l, <- P2.
   destruct p; simpl; try easy. symmetry. apply C0_Peq_nil.
 - rewrite IntPoly_alt. now exists [0;1]%Z.
 - rewrite <- E in P1. rewrite IntPoly_alt in *. destruct P1 as (q & ->).
   exists (tl q). simpl. now destruct q.
 - rewrite X_degree. lia.
 - rewrite X_degree. rewrite E, linfactors_degree. simpl.
   destruct l as [|r l]; simpl; try lia.
   simpl in *. rewrite !Cmult_1_l, Cplus_0_r in *.
   rewrite E in P2. unfold coef in P2. injection P2 as P2 _. lra.
Qed.

Lemma SalemPoly_no_1_root x p : SalemPoly x p -> ~Root 1 p.
Proof.
 intros (l & Hl & E).
 unfold Root. destruct Hl as (Hx & P1 & P2 & _ & _).
 rewrite <- E in P1, P2. contradict P2.
 assert (D1 : degree [-1;1] = 1%nat).
 { rewrite degree_nzlast; try easy. intros [=H]; lra. }
 assert (EQ := Pdiv_eqn p [-1;1]).
 assert (D := Pdiv_degree p [-1;1]).
 assert (INT := IntPoly_div p [-1;1] P1).
 destruct (Pdiv p [-1;1]) as (q,r). simpl in EQ,D,INT.
 rewrite D1 in D. assert (D' : (degree r = 0)%nat) by lia. clear D.
 assert (R : Peq r []).
 { destruct r. easy.
   rewrite degree_cons in D'. destruct Peq_0_dec as [R|R]; try easy.
   rewrite R in *.
   rewrite EQ, Pplus_eval, Pmult_eval, !cons_eval in P2.
   change (Peval [] 1) with 0 in P2. ring_simplify in P2. rewrite P2.
   apply C0_Peq_nil. }
 rewrite R in *. clear D' R. rewrite Pplus_0_r in EQ.
 exists [-1;1], q; repeat split.
 - now rewrite Pmult_comm.
 - rewrite IntPoly_alt. now exists [-1;1]%Z.
 - apply INT. rewrite IntPoly_alt. now exists [-1;1]%Z.
   red. now rewrite topcoef_alt, D1.
 - rewrite D1; lia.
 - rewrite D1. rewrite E, linfactors_degree. simpl.
   assert (In 1 l).
   { change (Root 1 p) in P2. rewrite E, <- linfactors_roots in P2.
     destruct P2 as [[=P2]|P2]; trivial; lra. }
   destruct l. easy. simpl. lia.
Qed.

Lemma SalemPolyIrred x p : SalemPoly x p -> ~Zreducible p.
Proof.
 intros (l & H1 & H2). rewrite H2. apply H1.
Qed.

Lemma SalemPoly_minimal x p : SalemPoly x p -> MinPolyQ x p.
Proof.
 intros Hp.
 assert (Mp : monic p).
 { destruct Hp as (l & Hl & Hl'). red. rewrite Hl'.
   apply linfactors_monic. }
 rewrite MinPolyQ_alt; repeat split; trivial.
 - eapply IntRatPoly, SalemIntPoly; eauto.
 - now apply SalemPolyRoot.
 - intros Hp'. apply (SalemPolyIrred x p); trivial.
   apply GaussLemma; trivial. eapply SalemIntPoly; eauto.
Qed.

Lemma SalemPoly_unique x p q : SalemPoly x p -> SalemPoly x q -> Peq p q.
Proof.
 intros. apply (MinPolyQ_unique x); now apply SalemPoly_minimal.
Qed.

Lemma SalemPoly_monicify_reciprocal x p :
  SalemPoly x p -> Peq p (reciprocal p).
Proof.
 intros P.
 assert (P' := SalemPoly_minimal _ _ P).
 assert (NZ := SalemPoly_no_0_root x p P).
 assert (NO := SalemPoly_no_1_root x p P).
 destruct P as (l & (Hx & P1 & P2 & P3 & P4) & E). rewrite <- E in P1, P2.
 destruct P3 as (r & IN & Hr).
 assert (Hr1 : Root r p). { rewrite E, <- linfactors_roots. now right. }
 assert (Hr2 : Root (/r) p).
 { replace (/r) with (Cconj r).
   2:{ rewrite <- (polar_eqn r).
       now rewrite Hr, Cmult_1_l, Cexp_conj_neg, <- Cexp_neg. }
   replace p with (map Cconj p). now apply Root_conj.
   rewrite IntPoly_alt in P1. destruct P1 as (q & ->).
   unfold Zpoly. rewrite map_map. apply map_ext.
   intros a. unfold "∘". now conj_in. }
 assert (M : MinPolyQ r p).
 { rewrite MinPolyQ_alt. rewrite MinPolyQ_alt in P'. tauto. }
 assert (N : ~Peq (reciprocal p) []).
 { intros Eq.
   generalize (Peval_reciprocal_0 p). rewrite Eq, E.
   rewrite linfactors_monic. intros [=H]. lra. }
 assert (D : degree (monicify (reciprocal p)) = degree p).
 { rewrite monicify_degree; trivial.
   apply reciprocal_degree. rewrite <- Peval_0. apply NZ. }
 assert (M' : MinPolyQ r (monicify (reciprocal p))).
 { red. repeat split.
   - now apply monicify_ok.
   - now apply RatPoly_monicify, RatPoly_reciprocal, IntRatPoly.
   - rewrite monicify_root; trivial. rewrite reciprocal_root; trivial.
     intros Eq. rewrite Eq, Cmod_0 in Hr. lra.
   - rewrite D. apply M. }
 assert (E' : Peq p (monicify (reciprocal p))).
 { now apply (MinPolyQ_unique r). }
 clear r IN Hr Hr1 Hr2 M M'.
 unfold monicify in E'.
 set (c := /topcoef (reciprocal p)) in *.
 replace c with 1 in E'. now rewrite Pmult_1_l in E'.
 apply Cmult_eq_reg_r with (Peval p 1); [|apply NO].
 rewrite E' at 1. rewrite Pmult_eval, Pconst_eval, Peval_1_reciprocal. ring.
Qed.

(* The former axiom : *)

Lemma large_second_best_root k roots :
  (6<=k)%nat -> SortedRoots k roots -> 1 < Cmod (roots@1).
Proof.
 intros K roots_ok.
 assert (M := SortedRoots_mu _ _ roots_ok).
 assert (INT : IntPoly (ThePoly k)).
 { repeat apply IntPoly_plus; try apply IntPoly_monom; try apply CInteger_Z.
   apply IntPoly_alt. now exists [-1]%Z. }
 destruct (RootQ_has_MinPolyQ (mu k)) as (p & P).
 { exists (ThePoly k); repeat split.
   - rewrite <- topcoef_0_iff, ThePoly_monic. intros [=H]; lra. lia.
   - now apply IntRatPoly.
   - apply mu_is_root; lia. }
 assert (D : exists q, RatPoly q /\ Peq (ThePoly k) (p*,q)).
 { apply (MinPolyQ_divide (mu k)); trivial.
   - now apply IntRatPoly.
   - apply mu_is_root; lia. }
 assert (P' : IntPoly p).
 { apply (MinPolyQ_Int (mu k)); trivial.
   exists (ThePoly k); repeat split; trivial.
   - red. destruct roots_ok as (->,_). apply linfactors_monic.
   - apply mu_is_root; lia. }
 destruct (All_roots p) as (l & Hp); try apply P.
 destruct (in_split (RtoC (mu k)) l) as (l1 & l2 & Hl).
 { rewrite linfactors_roots. rewrite <- Hp. apply P. }
 rewrite Hl in Hp.
 rewrite linfactors_perm in Hp; [|symmetry; apply Permutation_middle].
 clear l Hl. set (l := l1++l2) in *. clearbody l. clear l1 l2.
 destruct (Classical_Prop.classic (forall r, In r l -> Cmod r <= 1)).
 { exfalso.
   assert (N : ~(forall r, In r l -> 0 < Cmod r < 1)).
   { assert (N0 := Siegel.mu_non_Pisot_above_6 k K). contradict N0.
     split.
     - apply mu_itvl.
     - exists l; split; trivial. now rewrite <- Hp. }
   assert (R : existsb (fun r => negb (Rlt01 (Cmod r))) l = true).
   { rewrite existsb_negb_forallb. unfold "∘".
     apply eq_true_not_negb. rewrite forallb_forall.
     contradict N. intros r Hr. apply Rlt01_spec. specialize (N r Hr).
     now rewrite negb_involutive in N. }
   rewrite existsb_exists in R. destruct R as (r & Hr & Hr').
   apply Rlt01_Cmod in Hr'. destruct Hr' as [Hr'|Hr'].
   { exfalso. apply (root_nz k). rewrite <- Hr'.
     destruct D as (q & _ & ->). red. rewrite Pmult_eval.
     assert (IN : In r ((RtoC (mu k)) :: l)) by now right.
     apply linfactors_roots in IN. rewrite <- Hp in IN.
     rewrite IN; lca. }
   assert (Hr2 : Cmod r = 1%R). { specialize (H _ Hr). lra. }
   assert (S : SalemPoly (mu k) p).
   { red. exists l; split; trivial.
     red; repeat split.
     - apply mu_itvl.
     - now rewrite <- Hp.
     - rewrite <- Hp. apply MinPolyQ_Qirred in P. contradict P.
       now apply Zred_Qred.
     - now exists r.
     - apply H. }
   apply SalemPoly_monicify_reciprocal in S.
   assert (R : Root (/mu k) (ThePoly k)).
   { destruct D as (q & _ & ->). red. rewrite Pmult_eval.
     rewrite Cmult_integral. left. rewrite S.
     apply reciprocal_root.
     - apply nonzero_div_nonzero.
       intros [=?]. generalize (mu_itvl k); lra.
     - rewrite Cinv_inv. rewrite Hp, <- linfactors_roots; now left. }
   revert R. rewrite ThePoly_root_carac. ctor. intros [=R].
   assert (Mu := mu_itvl k).
   assert (Mu' : 0 <= /mu k < 1).
   { split. apply Rlt_le, Rinv_0_lt_compat; lra.
     rewrite <- Rinv_1. apply Rinv_lt_contravar; lra. }
   apply mu_unique in R; lra. }
 { apply Classical_Pred_Type.not_all_ex_not in H.
   destruct H as (r & Hr).
   apply Classical_Prop.imply_to_and in Hr. destruct Hr as (Hr,Hr').
   assert (E' : roots = RtoC (mu k) :: tl roots).
   { generalize (SortedRoots_length _ _ roots_ok).
     rewrite <- M. destruct roots; simpl; easy || lia. }
   assert (IN : In r (tl roots)).
   { destruct D as (q & _ & E).
     assert (Mo : monic (ThePoly k)).
     { red. now rewrite (proj1 roots_ok), linfactors_monic. }
     assert (Hq : monic q).
     { revert Mo. unfold monic in *. rewrite E, topcoef_mult.
       destruct P as (-> & _). now rewrite Cmult_1_l. }
     destruct (All_roots q Hq) as (l' & Hl').
     rewrite (proj1 roots_ok), Hp, Hl', <- linfactors_app in E.
     apply linfactors_perm_iff in E.
     rewrite E' in E.
     simpl in E. apply Permutation_cons_inv, Permutation_sym in E.
     apply (Permutation_in _ E), in_app_iff. now left. }
   apply SortedRoots_Cmod_sorted in roots_ok.
   rewrite MoreComplex.StronglySorted_nth in roots_ok.
   destruct (In_nth (tl roots) r 0 IN) as (i & Hi & Hi').
   destruct i as [|i].
   - rewrite E'. unfold Cnth. simpl. rewrite Hi'; lra.
   - apply Rlt_le_trans with (Cmod (roots @ (S (S i)))).
     + rewrite E'. unfold Cnth. simpl. rewrite Hi'; lra.
     + apply Rge_le, roots_ok. rewrite E'. simpl. lia. }
Qed.

(* Print Assumptions large_second_best_root. *)

Local Close Scope C.

(** When parameter k is at least 6,
     [sup (f k n - tau k *n) = +infinity]
    and
     [inf (f k n - tau k *n) = -infinity].
    It is sufficient to consider some numbers [n] of the form [A k m].

    The two following proofs used to rely on an axiom stating that
    the largest secondary root has modulus > 1 when k>=6. This axiom
    has been replaced by a full proof.
    So these proofs now depend only on the 4 usual logical axioms
    just as the whole Coq theory of classical real numbers.

    Note that [f 5 n - tau 5 * n] is also unbounded.
    The proof is quite different, since the largest secondary root
    has modulus just 1. See F5.v.
*)

Lemma dA_sup_k6 k : (6<=k)%nat ->
 is_sup_seq (fun n => A k (n-1) - tau k * A k n) Rbar.p_infty.
Proof.
 intros K M. simpl.
 destruct (SortedRoots_exists k lia) as (roots & roots_ok).
 assert (LT := SecondRoot.large_second_best_root k roots K roots_ok).
 destruct (dA_expo k roots lia roots_ok) as (c & Hc).
 set (r := Complex.Cmod _) in *.
 destruct (large_enough_exponent r (M/c)) as (N, HN); trivial.
 destruct (Hc N) as (n & Hn & Hn').
 exists n. rewrite <- Hn'.
 rewrite Rmult_comm, <- Rcomplements.Rlt_div_l; try apply c.
 eapply Rlt_le_trans; [apply HN|]. apply Rle_pow; lia || lra.
Qed.

Lemma delta_sup_k6 k : (6<=k)%nat ->
 is_sup_seq (fun n => f k n - tau k * n) Rbar.p_infty.
Proof.
 intros K M. destruct (dA_sup_k6 k K M) as (n & Hn). simpl in *.
 exists (A k n). rewrite f_A; easy || lia.
Qed.

Lemma dA_inf_k6 k : (6<=k)%nat ->
 is_inf_seq (fun n => A k (n-1) - tau k * A k n) Rbar.m_infty.
Proof.
 intros K M. simpl.
 destruct (SortedRoots_exists k lia) as (roots & roots_ok).
 assert (LT := SecondRoot.large_second_best_root k roots K roots_ok).
 destruct (dA_expo' k roots lia roots_ok) as (c & Hc).
 set (r := Complex.Cmod _) in *.
 destruct (large_enough_exponent r (-M/c)) as (N, HN); trivial.
 destruct (Hc N) as (n & Hn & Hn').
 exists n. rewrite Hn'.
 apply Ropp_lt_cancel. rewrite Ropp_mult_distr_l, Ropp_involutive.
 rewrite Rmult_comm, <- Rcomplements.Rlt_div_l; try apply c.
 eapply Rlt_le_trans; [apply HN|]. apply Rle_pow; lia || lra.
Qed.

Lemma delta_inf_k6 k : (6<=k)%nat ->
 is_inf_seq (fun n => f k n - tau k * n) Rbar.m_infty.
Proof.
 intros K M. destruct (dA_inf_k6 k K M) as (n & Hn). simpl in *.
 exists (A k n). rewrite f_A; easy || lia.
Qed.

(* Print Assumptions delta_sup_k6. *)
(* Print Assumptions delta_inf_k6. *)
