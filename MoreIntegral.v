From Coq Require Import Lia Reals Lra.
From Coquelicot Require Import Hierarchy RInt RInt_analysis Series PSeries.
From Coquelicot Require Import Derive AutoDerive Continuity ElemFct.
From Hofstadter.MiniQuantumLib Require Import Complex.
Import Continuity.
Require Import MoreList MoreReals MoreLim MoreSum MoreComplex MoreLim.
Local Open Scope C.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * R->C integral *)

Notation is_CInt := (@is_RInt C_NM).
Notation ex_CInt := (@ex_RInt C_NM).
Notation CInt := (@RInt C_CNM).

Lemma is_CInt_unique (f : R -> C) (a b : R) (c : C) :
  is_CInt f a b c -> CInt f a b = c.
Proof.
 intros. now apply is_RInt_unique.
Qed.

(* NB : Basics.compose is ∘ a.k.a \circ *)

Lemma is_CInt_proj (f : R -> C) (a b : R) (c : C) :
 is_CInt f a b c <->
 is_RInt (Re ∘ f) a b (Re c) /\
 is_RInt (Im ∘ f) a b (Im c).
Proof.
 split.
 - intros H. split.
   + now apply is_RInt_fct_extend_fst.
   + now apply is_RInt_fct_extend_snd.
 - intros (H1,H2). destruct c as (x,y). simpl in *.
   now apply is_RInt_fct_extend_pair.
Qed.

Lemma ex_CInt_proj (f : R -> C) (a b : R) :
 ex_CInt f a b <-> ex_RInt (Re ∘ f) a b /\ ex_RInt (Im ∘ f) a b.
Proof.
 split.
 - intros (c & H). rewrite is_CInt_proj in H.
   split; [now exists (Re c) | now exists (Im c)].
 - intros ((x & Hx),(y & Hy)). exists (x,y). now rewrite is_CInt_proj.
Qed.

Lemma CInt_proj (f : R -> C) (a b : R) :
 ex_CInt f a b ->
 CInt f a b = (RInt (Re ∘ f) a b, RInt (Im ∘ f) a b).
Proof.
 intros H. symmetry.
 apply RInt_fct_extend_pair.
 - intros f0 a0 b0 l. apply (is_RInt_unique (V:=R_CNM)).
 - intros f0 a0 b0 l. apply (is_RInt_unique (V:=R_CNM)).
 - now apply (RInt_correct (V:=C_CNM)).
Qed.

Lemma is_CInt_RtoC_gen (f : R -> R) (a b : R) (c : C) :
 is_CInt (RtoC ∘ f) a b c <-> is_RInt f a b (Re c) /\ Im c = 0%R.
Proof.
 rewrite is_CInt_proj. destruct c as (x,y). simpl.
 split; intros (H1,H2); split; trivial.
 - apply (is_RInt_unique (V:=R_CNM)) in H2.
   rewrite <- H2. unfold compose. simpl. rewrite RInt_const.
   unfold scal. simpl. unfold mult. simpl. lra.
 - replace y with ((b-a)*0)%R by lra.
   apply (is_RInt_const (V:=R_NM)).
Qed.

Lemma is_CInt_RtoC (f : R -> R) (a b r : R) :
 is_CInt (RtoC ∘ f) a b (RtoC r) <-> is_RInt f a b r.
Proof.
 rewrite is_CInt_RtoC_gen. simpl. intuition.
Qed.

Lemma ex_CInt_RtoC (f : R -> R) (a b : R) :
 ex_CInt (RtoC ∘ f) a b <-> ex_RInt f a b.
Proof.
 unfold ex_RInt. setoid_rewrite is_CInt_RtoC_gen.
 split; intros (If & H); simpl in *.
 - now exists (Re If).
 - now exists (RtoC If).
Qed.

Lemma CInt_RtoC (f : R -> R) (a b : R) :
 ex_RInt f a b -> CInt (RtoC ∘ f) a b = RtoC (RInt f a b).
Proof.
 intros H. apply is_CInt_unique. apply is_CInt_RtoC.
 now apply (RInt_correct (V:=R_CNM)).
Qed.

Lemma CInt_Cmod (f : R -> C) (a b M : R) :
 a <= b -> ex_CInt f a b ->
 (forall x : R, a <= x <= b -> Cmod (f x) <= M) ->
 Cmod (CInt f a b) <= (b-a)*M.
Proof.
 intros Hab (If,H) H'.
 rewrite (is_CInt_unique _ _ _ _ H).
 rewrite Complex.Cmod_norm.
 apply (norm_RInt_le_const (V:=C_NM) f); trivial.
 intros x Hx. rewrite <- Complex.Cmod_norm. now apply H'.
Qed.

Lemma is_CInt_plus (f g : R -> C) (a b : R) :
 ex_CInt f a b -> ex_CInt g a b ->
 is_CInt (fun x => f x + g x) a b (CInt f a b + CInt g a b).
Proof.
 intros (If,Hf) (Ig,Hg). simpl in *.
 apply (is_RInt_plus (V:=C_NM)).
 now rewrite (is_CInt_unique f a b If).
 now rewrite (is_CInt_unique g a b Ig).
Qed.

Lemma CInt_plus (f g : R -> C) (a b : R) :
 ex_CInt f a b -> ex_CInt g a b ->
 CInt (fun x => f x + g x) a b = CInt f a b + CInt g a b.
Proof.
 intros Hf Hg. now apply is_CInt_unique, is_CInt_plus.
Qed.

Lemma is_CInt_minus (f g : R -> C) (a b : R) :
 ex_CInt f a b -> ex_CInt g a b ->
 is_CInt (fun x => f x - g x) a b (CInt f a b - CInt g a b).
Proof.
 intros (If,Hf) (Ig,Hg). simpl in *.
 apply (is_RInt_minus (V:=C_NM)).
 now rewrite (is_CInt_unique f a b If).
 now rewrite (is_CInt_unique g a b Ig).
Qed.

Lemma CInt_minus (f g : R -> C) (a b : R) :
 ex_CInt f a b -> ex_CInt g a b ->
 CInt (fun x => f x - g x) a b = CInt f a b - CInt g a b.
Proof.
 intros Hf Hg. now apply is_CInt_unique, is_CInt_minus.
Qed.

Lemma is_CInt_const (a b : R) (c : C) : is_CInt (fun _ => c) a b ((b-a)*c).
Proof.
 apply is_CInt_proj. split.
 - apply is_RInt_ext with (fun _ => Re c); trivial.
   rewrite <- RtoC_minus, re_scal_l.
   apply (is_RInt_const (V:=R_NM)).
 - apply is_RInt_ext with (fun _ => Im c); trivial.
   rewrite <- RtoC_minus, im_scal_l.
   apply (is_RInt_const (V:=R_NM)).
Qed.

Lemma CInt_const (a b : R) (c : C) : CInt (fun _ => c) a b = (b-a)*c.
Proof.
 apply is_CInt_unique, is_CInt_const.
Qed.

Lemma is_CInt_scal (f : R -> C) (a b : R) (c If : C) :
  is_CInt f a b If ->
  is_CInt (fun x => c * f x) a b (c*If).
Proof.
 intros H.
 rewrite is_CInt_proj in *. split.
 - apply is_RInt_ext with (fun x => Re c * Re (f x) - Im c * Im (f x))%R;
    try easy.
   rewrite re_mult.
   apply (is_RInt_minus (V:=R_NM));
    now apply (is_RInt_scal (V:=R_NM)).
 - apply is_RInt_ext with (fun x => Re c * Im (f x) + Im c * Re (f x))%R;
    try easy.
   rewrite im_mult.
   apply (is_RInt_plus (V:=R_NM));
    now apply (is_RInt_scal (V:=R_NM)).
Qed.

Lemma CInt_scal (f : R -> C) (a b : R) (c : C) :
  ex_CInt f a b ->
  CInt (fun x => c * f x) a b = c * CInt f a b.
Proof.
 intros (l,H).
 apply is_CInt_unique. rewrite (is_CInt_unique _ _ _ _ H).
 now apply is_CInt_scal.
Qed.

Lemma is_CInt_conj (f : R -> C) (a b : R) (If : C) :
  is_CInt f a b If ->
  is_CInt (Cconj∘f) a b (Cconj If).
Proof.
 intros H.
 rewrite is_CInt_proj in *. split.
 - apply is_RInt_ext with (Re ∘ f).
   { intros. unfold compose. now rewrite re_conj. }
   now rewrite re_conj.
 - apply is_RInt_ext with (Ropp ∘ Im ∘ f).
   { intros. unfold compose. now rewrite im_conj. }
   rewrite im_conj. now apply (is_RInt_opp (V:=R_NM)).
Qed.

(** Continuity *)

Lemma continuous_C {U:UniformSpace}(f : U -> C) (x : U) :
 continuous f x <-> continuous (Re∘f) x /\ continuous (Im∘f) x.
Proof.
 split.
 - intros Hf. split.
   + apply (continuous_comp f Re). apply Hf. apply continuous_fst.
   + apply (continuous_comp f Im). apply Hf. apply continuous_snd.
 - intros (H1,H2).
   apply continuous_ext with (fun x => (Re (f x), Im (f x))).
   { intros. now rewrite surjective_pairing. }
   apply continuous_comp_2; trivial.
   apply continuous_ext with (fun p => p).
   apply surjective_pairing.
   apply continuous_id.
Qed.

(* NB: continuous_mult won't work here ?! *)
Lemma continuous_Cmult {U:UniformSpace}(f g : U -> C) (x : U) :
 continuous f x -> continuous g x -> continuous (fun x => f x * g x) x.
Proof.
 intros Hf Hg.
 rewrite !continuous_C in *. split.
 - apply continuous_ext
     with (fun x => (Re∘f) x * (Re∘g) x - (Im∘f) x * (Im∘g) x)%R; try easy.
   apply (continuous_minus (V:=R_NM));
     now apply (continuous_mult (K:=R_AbsRing)).
 - apply continuous_ext
     with (fun x => (Re∘f) x * (Im∘g) x + (Im∘f) x * (Re∘g) x)%R; try easy.
   apply (continuous_plus (V:=R_NM));
     now apply (continuous_mult (K:=R_AbsRing)).
Qed.

Lemma continuous_Cexp (x : R) : continuous Cexp x.
Proof.
 apply continuous_C. split.
 - apply continuous_ext with cos; try easy.
   apply continuous_cos_comp, continuous_id.
 - apply continuous_ext with sin; try easy.
   apply continuous_sin_comp, continuous_id.
Qed.

Lemma continuous_Cexpn (n : nat) (x : R) :
  continuous (fun x => Cexp (n * x)) x.
Proof.
 apply continuous_comp with (g:=Cexp); try apply continuous_Cexp.
 apply (continuous_scal_r (INR n) (fun x:R => x)), continuous_id.
Qed.

Lemma continuous_Cpow x n : continuous (fun x => x^n) x.
Proof.
 induction n; simpl; try apply continuous_const.
 apply continuous_Cmult; trivial using continuous_id.
Qed.

Lemma sum_n_continuous {U:UniformSpace}(f : nat -> U -> C) n x :
 (forall i, (i<=n)%nat -> continuous (f i) x) ->
 continuous (fun x => sum_n (fun k => f k x) n) x.
Proof.
 induction n; intros Hf.
 - apply continuous_ext with (f O). intros; now rewrite sum_O. now apply Hf.
 - apply continuous_ext with (fun x => sum_n (fun k => f k x) n + f (S n) x).
   intros; now rewrite sum_Sn.
   apply (continuous_plus (V:=C_NM)).
   + apply IHn. intros. apply Hf; lia.
   + now apply Hf.
Qed.

Lemma CPowerSeries_Cexp_continuous (a : nat -> C) (x:R) :
 ex_series (Cmod ∘ a) ->
 continuous (CPowerSeries a ∘ Cexp) x.
Proof.
 intros (l & H). simpl in l.
 intros P (eps & HP). simpl in *. red. red.
 assert (LT : 0 < eps/3). { generalize (cond_pos eps). lra. }
 set (e3 := mkposreal _ LT).
 destruct (H (ball l e3)) as (N & HN). { now exists e3. }
 specialize (HN N lia). repeat red in HN.
 change (Rabs (sum_n (Cmod∘a) N - l) < e3) in HN.
 assert (sum_n (Cmod∘a) N <= l).
 { apply pos_series_pos_sum; trivial. intros. apply Cmod_ge_0. }
 rewrite Rabs_minus_sym, Rabs_pos_eq in HN by lra.
 set (f := CPowerSeries a ∘ Cexp) in *.
 set (g := fun x => sum_n (fun k => a k * Cexp x ^k) N). simpl in g.
 assert (Hg : continuous g x).
 { apply sum_n_continuous. intros i Hi.
   apply continuous_Cmult. apply continuous_const.
   apply continuous_comp with (g:=fun z => Cpow z i).
   apply continuous_Cexp. apply continuous_Cpow. }
 assert (LT' : 0 < e3/sqrt 2).
 { apply Rdiv_lt_0_compat. apply LT. apply Rlt_sqrt2_0. }
 set (e3b := mkposreal _ LT').
 specialize (Hg (ball (g x) e3b)) as (eps' & Heps'). { now exists e3b. }
 assert (D : forall y, Cmod (f y - g y) < e3).
 { intros y. eapply Rle_lt_trans; [ | apply HN ].
   unfold f. apply CPowerSeries_bound3; trivial. rewrite Cmod_Cexp. lra. }
 exists eps'. intros y Y. apply HP. apply C_ball.
 replace (f x - f y) with ((f x - g x)+(g x - g y)+(g y - f y)) by ring.
 replace (pos eps) with (e3 + e3 + e3)%R. 2:{ unfold e3. simpl. lra. }
 eapply Rle_lt_trans; [ eapply Cmod_triangle | ].
 apply Rplus_lt_compat. 2:{ rewrite Cmod_switch. apply D. }
 eapply Rle_lt_trans; [ eapply Cmod_triangle | ].
 apply Rplus_lt_compat. apply D.
 replace (pos e3) with (e3b*sqrt 2)%R.
 2:{ unfold e3b. simpl. field. generalize Rlt_sqrt2_0. lra. }
 apply ball_C, Heps', Y.
Qed.

(** Integral of Cexp and sums of Cexp *)

Lemma ex_CInt_Cexp (n : nat) a b : ex_CInt (fun x => Cexp (n * x)) a b.
Proof.
 apply (ex_RInt_continuous (V:=C_CNM)). intros. apply continuous_Cexpn.
Qed.

Lemma is_CInt_Cexp_gen (n : nat) a b : n<>O -> Cexp (n*a) = Cexp (n*b) ->
  is_CInt (fun x => Cexp (n * x)) a b 0.
Proof.
 intros Hn [= E1 E2].
 rewrite is_CInt_proj by easy.
 split.
 - apply is_RInt_ext with (f := fun x => cos (n*x)); try easy. simpl.
   assert (D : forall x, is_derive (fun x => sin (n*x)/n)%R x (cos (n*x))).
   { intros. simpl. auto_derive; trivial. field.
     contradict Hn. now apply INR_eq. }
   simpl in D.
   set (df := (fun x => sin (n*x)/n)%R) in *.
   replace 0%R with (df b - df a)%R.
   2:{ unfold df. rewrite E2. lra. }
   apply (is_RInt_derive (V:=R_CNM)); trivial.
   intros x _.
   apply continuous_comp.
   + apply (continuous_scal_r (INR n) (fun x:R => x)), continuous_id.
   + apply continuity_pt_filterlim. apply continuity_cos.
 - apply is_RInt_ext with (f := fun x => sin (n*x)); try easy. simpl.
   assert (D : forall x, is_derive (fun x => -cos (n*x)/n)%R x (sin (n*x))).
   { intros. simpl. auto_derive; trivial. field.
     contradict Hn. now apply INR_eq. }
   simpl in D.
   set (df := (fun x => -cos (n*x)/n)%R) in *.
   replace 0%R with (df b - df a)%R.
   2:{ unfold df. rewrite E1. lra. }
   apply (is_RInt_derive (V:=R_CNM)); trivial.
   intros x _.
   apply continuous_comp.
   + apply (continuous_scal_r (INR n) (fun x:R => x)), continuous_id.
   + apply continuity_pt_filterlim. apply continuity_sin.
Qed.

Lemma is_CInt_Cexp (n : nat) : n<>O ->
  is_CInt (fun x => Cexp (n * x)) 0 (2*PI) 0.
Proof.
 intros Hn. apply is_CInt_Cexp_gen; trivial. unfold Cexp.
 generalize (sin_period 0 n) (cos_period 0 n).
 rewrite Rplus_0_l, (Rmult_comm 2 n), Rmult_assoc. intros -> ->.
 now rewrite Rmult_0_r.
Qed.

Lemma is_CInt_Cexp' (n : nat) : n<>O ->
  is_CInt (fun x => Cexp (n * x)) 0 (-2*PI) 0.
Proof.
 intros Hn. apply is_CInt_Cexp_gen; trivial. unfold Cexp.
 rewrite Rmult_0_r.
 replace (n*(-2*PI))%R with (-(n*(2*PI)))%R by lra.
 rewrite cos_neg, sin_neg.
 generalize (sin_period 0 n) (cos_period 0 n).
 rewrite Rplus_0_l, (Rmult_comm 2 n), Rmult_assoc. intros -> ->.
 rewrite sin_0. lca.
Qed.

Lemma CInt_Cexp (n : nat) : n<>O ->
  CInt (fun x => Cexp (n * x)) 0 (2 * PI) = 0.
Proof.
 intros. now apply is_CInt_unique, is_CInt_Cexp.
Qed.

Lemma is_CInt_sum_n (a : nat -> C) n m : (n < m)%nat ->
 is_CInt (fun x => sum_n (fun k => a k * Cexp ((m-k)%nat*x)) n) 0 (2*PI) 0.
Proof.
 revert m.
 induction n; intros m Hm.
 - apply (is_RInt_ext (V:=C_NM))
     with (fun x => a O * Cexp ((m-0)%nat * x)).
   { intros. now rewrite sum_O. }
   replace 0 with (a O * 0) by lca.
   apply is_CInt_scal. rewrite <- (CInt_Cexp (m-0)%nat) by lia.
   apply (RInt_correct (V:=C_CNM)).
   apply ex_CInt_Cexp.
 - apply (is_RInt_ext (V:=C_NM))
     with (fun x => sum_n (fun k => a k * Cexp ((m-k)%nat*x)) n
                    + a (S n) * Cexp ((m-S n)%nat * x)).
   { intros. now rewrite sum_Sn. }
   replace 0 with (0+0) by lca.
   apply (is_RInt_plus (V:=C_NM)). apply IHn; lia.
   replace 0 with (a (S n) * 0) by lca.
   apply is_CInt_scal. rewrite <- (CInt_Cexp (m-S n)%nat) by lia.
   apply (RInt_correct (V:=C_CNM)).
   apply ex_CInt_Cexp.
Qed.

Lemma CInt_sum_n (a : nat -> C) n m : (n < m)%nat ->
 CInt (fun x => sum_n (fun k => a k * Cexp ((m-k)%nat*x)) n) 0 (2*PI) = 0.
Proof.
 intros. now apply is_CInt_unique, is_CInt_sum_n.
Qed.

Lemma is_CInt_sum_n_opp (a : nat -> C) n m : (n < m)%nat ->
 is_CInt (fun x => sum_n (fun k => a k * Cexp ((m-k)%nat*-x)) n) 0 (2*PI) 0.
Proof.
 intros H.
 apply (is_RInt_ext (V:=C_NM))
   with (fun x => Cconj (sum_n (fun k => Cconj (a k) * Cexp ((m-k)%nat*x)) n)).
 { intros x _. rewrite sum_n_conj. apply sum_n_ext. intros p.
   unfold compose. rewrite Cconj_mult_distr, Cconj_involutive. f_equal.
   rewrite Cexp_conj_neg. f_equal. lra. }
 rewrite <- Cconj_0. now apply is_CInt_conj, is_CInt_sum_n.
Qed.

Lemma CInt_sum_n_opp (a : nat -> C) n m : (n < m)%nat ->
 CInt (fun x => sum_n (fun k => a k * Cexp ((m-k)%nat*-x)) n) 0 (2*PI) = 0.
Proof.
 intros. now apply is_CInt_unique, is_CInt_sum_n_opp.
Qed.
