From Coq Require Import Lia Reals Lra.
From Coquelicot Require Complex.
From Coquelicot Require Import Hierarchy Continuity Derive AutoDerive
 RInt RInt_analysis Series PSeries.
From QuantumLib Require Import Complex Polynomial.
Import Continuity.
Require Import MoreList MoreReals MoreLim MoreComplex MorePoly ThePoly.
Require Import GenFib Mu.
Local Open Scope C.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * The second largest root of ThePoly has modulus>1 for q>=5

  We recall that ThePoly(x) is x^(q+1)-x^q-1.
  We adapt to ThePoly the first pages of the initial proof that
  the Plastic Ratio (root of x^3-x-1, approx 1.3247...) is the
  smallest Pisot number. Reference:

  "Algebraic Integers whose Conjugates lie in the Unit Circle",
    Carl Ludwig Siegel, 1944.
*)

Notation R_NM := R_NormedModule.
Notation R_CNM := R_CompleteNormedModule.
Notation C_NM := Complex.C_R_NormedModule.
Notation C_CNM := Complex.C_R_CompleteNormedModule.

Ltac fixeq ty := change (@eq _) with (@eq ty).

(** R->C integral *)

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

(** More on Coquelicot [sum_n_m] and [sum_n] *)

Lemma sum_n_minus (a b : nat -> C) n :
 sum_n a n - sum_n b n = sum_n (fun n => a n - b n) n.
Proof.
 induction n.
 - now rewrite !sum_O.
 - rewrite !sum_Sn. rewrite <- IHn. change plus with Cplus. ring.
Qed.

Lemma sum_n_m_triangle (a : nat -> C) n m :
  Cmod (sum_n_m a n m) <= sum_n_m (Cmod ∘ a) n m.
Proof.
 destruct (Nat.le_gt_cases n m).
 - induction H.
   + rewrite !sum_n_n. apply Rle_refl.
   + rewrite !sum_n_Sm; try lia.
     eapply Rle_trans; [apply Cmod_triangle | apply Rplus_le_compat];
       try apply IHle. apply Rle_refl.
 - rewrite !sum_n_m_zero; trivial.
   change (Cmod zero) with (Cmod 0). rewrite Cmod_0. apply Rle_refl.
Qed.

Lemma sum_n_triangle (a : nat -> C) n :
  Cmod (sum_n a n) <= sum_n (Cmod ∘ a) n.
Proof.
 unfold sum_n. apply sum_n_m_triangle.
Qed.

Lemma sum_n_proj (a : nat -> C) n :
 sum_n a n = (sum_n (Re ∘ a) n, sum_n (Im ∘ a) n).
Proof.
 induction n.
 - rewrite !sum_O. apply surjective_pairing.
 - now rewrite !sum_Sn, IHn.
Qed.

Lemma sum_n_zero {G:AbelianMonoid} n : @sum_n G (fun _ => zero) n = zero.
Proof.
 induction n.
 - now rewrite sum_O.
 - rewrite sum_Sn, IHn. apply plus_zero_l.
Qed.

Lemma sum_n_R0 n : sum_n (fun _ => R0) n = R0.
Proof.
 apply (sum_n_zero (G:=R_AbelianMonoid)).
Qed.

Lemma sum_n_C0 n : sum_n (fun n => C0) n = C0.
Proof.
 apply (sum_n_zero (G:=Complex.C_AbelianMonoid)).
Qed.

Lemma sum_n_Cconst n (c:C) : sum_n (fun _ => c) n = S n * c.
Proof.
 rewrite sum_n_proj. unfold compose. rewrite !sum_n_const.
 unfold Cmult, Re, Im. simpl. lca.
Qed.

Lemma sum_n_conj (a : nat -> C) n :
 Cconj (sum_n a n) = sum_n (Cconj ∘ a) n.
Proof.
 induction n.
 - now rewrite !sum_O.
 - rewrite !sum_Sn. rewrite <- IHn. apply Cconj_plus_distr.
Qed.

Lemma re_sum_n (a : nat -> C) n : Re (sum_n a n) = sum_n (Re ∘ a) n.
Proof.
 now rewrite sum_n_proj.
Qed.

Lemma im_sum_n (a : nat -> C) n : Im (sum_n a n) = sum_n (Im ∘ a) n.
Proof.
 now rewrite sum_n_proj.
Qed.

Lemma RtoC_sum_n (a : nat -> R) n :
 RtoC (sum_n a n) = sum_n (RtoC∘a) n.
Proof.
 rewrite sum_n_proj. unfold compose. simpl. now rewrite sum_n_R0.
Qed.

Lemma sum_n_Cmult_l a (b : nat -> C) n :
  sum_n (fun k => a * b k) n = a * sum_n b n.
Proof.
 apply (sum_n_mult_l (K:=Complex.C_Ring)).
Qed.

Lemma sum_n_Cmult_r (a : nat -> C) b n :
  sum_n (fun k => a k * b) n = sum_n a n * b.
Proof.
 apply (sum_n_mult_r (K:=Complex.C_Ring)).
Qed.

Lemma sum_n_m_le (a a' : nat -> R) :
  (forall n, a n <= a' n) -> forall n m, sum_n_m a n m <= sum_n_m a' n m.
Proof.
 intros Ha n m.
 destruct (Nat.le_gt_cases n m).
 - induction H.
   + now rewrite !sum_n_n.
   + rewrite !sum_n_Sm; try lia.
     now apply Rplus_le_compat.
 - rewrite !sum_n_m_zero; trivial. lra.
Qed.

Lemma sum_n_le (a a' : nat -> R) :
  (forall n, a n <= a' n) -> forall n, sum_n a n <= sum_n a' n.
Proof.
 intros Ha n. unfold sum_n. now apply sum_n_m_le.
Qed.

Lemma sum_n_Cpow x n : (1-x) * sum_n (Cpow x) n = 1 - x^S n.
Proof.
 induction n.
 - rewrite sum_O. lca.
 - rewrite sum_Sn. change plus with Cplus.
   rewrite Cmult_plus_distr_l, IHn, !Cpow_S. ring.
Qed.

Lemma sum_INR n : (sum_n INR n = n*(n+1)/2)%R.
Proof.
 induction n.
 - rewrite sum_O. simpl. lra.
 - rewrite sum_Sn. rewrite IHn. change plus with Rplus.
   rewrite S_INR. lra.
Qed.

Lemma sum_square n : (sum_n (fun k => k^2) n = n*(n+1)*(2*n+1)/6)%R.
Proof.
 induction n.
 - rewrite sum_O. simpl. lra.
 - rewrite sum_Sn. rewrite IHn. change plus with Rplus.
   rewrite S_INR. lra.
Qed.

Lemma sum_n_m_shift {G : AbelianMonoid} (a : nat -> G) n m p :
  (p <= n <= m)%nat ->
  sum_n_m (fun k => a (k-p)%nat) n m = sum_n_m a (n-p) (m-p).
Proof.
 intros (Hp,H).
 induction H.
 - now rewrite !sum_n_n.
 - replace (S m -p)%nat with (S (m-p))%nat by lia.
   rewrite !sum_n_Sm; try lia. rewrite IHle by lia. f_equal. f_equal. lia.
Qed.

Lemma Clistsum_sum_n (f : nat -> C -> C) l n :
 sum_n (fun k => Clistsum (map (f k) l)) n =
 Clistsum (map (fun x => sum_n (fun k => f k x) n) l).
Proof.
 induction n.
 - rewrite sum_O. f_equal. apply map_ext. intros x. now rewrite sum_O.
 - rewrite !sum_Sn, IHn. change plus with Cplus.
   rewrite Clistsum_plus. f_equal. apply map_ext. intros x.
   now rewrite !sum_Sn.
Qed.

(** Limits of C sequences *)

Lemma C_ball (c c' : C) (eps : R) :
  Cmod (c-c') < eps -> ball c eps c'.
Proof.
 rewrite Cmod_switch. intros H.
 change (Rabs (Re (c' - c)) < eps /\ Rabs (Im (c' - c)) < eps).
 split; apply Rle_lt_trans with (Cmod (c'-c));
  auto using re_le_Cmod, im_le_Cmod.
Qed.

Lemma ball_C (c c' : C) (eps : R) :
  ball c eps c' -> Cmod (c-c') < eps * sqrt 2.
Proof.
 rewrite Cmod_switch. intros (H,H').
 change (Rabs (Re (c' - c)) < eps) in H.
 change (Rabs (Im (c' - c)) < eps) in H'.
 assert (0 <= eps) by (generalize (Rabs_pos (Re (c'-c))); lra).
 rewrite <- (Rabs_right eps) in H,H' by lra.
 apply Rsqr_lt_abs_1 in H, H'.
 apply Rsqr_incrst_0; try apply Cmod_ge_0.
 2:{ apply Rmult_le_pos; trivial; apply sqrt_pos. }
 rewrite Rsqr_mult, Rsqr_sqrt by lra. rewrite !Rsqr_pow2 in *.
 rewrite Cmod2_alt. lra.
Qed.

Definition is_lim_Cseq (f : nat -> C) (c : C) :=
 filterlim f Hierarchy.eventually (locally c).

Lemma is_lim_Cseq_proj (f : nat -> C) (c : C) :
 is_lim_Cseq f c <->
 is_lim_seq (Re ∘ f) (Re c) /\ is_lim_seq (Im ∘ f) (Im c).
Proof.
 split.
 - split.
   + intros P (eps, HP). simpl in HP.
     destruct (H (ball c eps)) as (N, HN); [now exists eps|].
     exists N. intros n Hn. now apply HP, HN.
   + intros P (eps, HP). simpl in HP.
     destruct (H (ball c eps)) as (N, HN); [now exists eps|].
     exists N. intros n Hn. now apply HP, HN.
 - intros (H1,H2) P (eps, HP). simpl in HP.
   destruct (H1 (ball (Re c) eps)) as (N1, HN1); [now exists eps|].
   destruct (H2 (ball (Im c) eps)) as (N2, HN2); [now exists eps|].
   exists (Nat.max N1 N2). intros n Hn. apply HP.
   split; [apply HN1|apply HN2]; lia.
Qed.

Definition ex_lim_Cseq (f : nat -> C) := exists c, is_lim_Cseq f c.

Definition Lim_Cseq (f : nat -> C) : C :=
  (Rbar.real (Lim_seq (Re ∘ f)), Rbar.real (Lim_seq (Im ∘ f))).

Lemma is_lim_Cseq_unique (f : nat -> C) (c : C) :
 is_lim_Cseq f c -> Lim_Cseq f = c.
Proof.
 rewrite is_lim_Cseq_proj. intros (H1,H2). unfold Lim_Cseq.
 apply is_lim_seq_unique in H1, H2. rewrite H1, H2. simpl. now destruct c.
Qed.

Lemma Lim_Cseq_correct (f : nat -> C) :
 ex_lim_Cseq f -> is_lim_Cseq f (Lim_Cseq f).
Proof.
 intros (c & H). now rewrite (is_lim_Cseq_unique _ _ H).
Qed.

Lemma is_lim_Cseq_0_Cmod (f : nat -> C) :
 is_lim_seq (Cmod ∘ f) 0%R -> is_lim_Cseq f 0.
Proof.
 intros H.
 apply is_lim_Cseq_proj. simpl.
 split; apply is_lim_seq_0_abs with (v := Cmod ∘ f); trivial;
 intros; apply re_le_Cmod || apply im_le_Cmod.
Qed.

Lemma is_lim_Cseq_Cmod (f : nat -> C) (l : C) :
 is_lim_Cseq f l -> is_lim_seq (Cmod ∘ f) (Cmod l).
Proof.
 intros H P (eps,HP). simpl in HP.
 assert (LT : 0 < /2 * eps).
 { apply Rmult_lt_0_compat. lra. apply eps. }
 set (eps' := mkposreal _ LT).
 destruct (H (ball l eps')) as (N, HN); [now exists eps'|].
 exists N. intros n Hn. apply HP.
 change (Rabs (Cmod (f n) - Cmod l) < eps).
 assert (Cmod (f n - l) < eps).
 { apply Rsqr_incrst_0; trivial using Cmod_ge_0.
   2:{ generalize (cond_pos eps); lra. }
   rewrite !Rsqr_pow2, Cmod2_alt.
   destruct (HN n Hn) as (H1,H2).
   change (Rabs (Re (f n - l)) < eps') in H1.
   change (Rabs (Im (f n - l)) < eps') in H2.
   rewrite <- (Rabs_right eps') in H1,H2 by (generalize (cond_pos eps'); lra).
   apply Rsqr_lt_abs_1 in H1,H2. rewrite !Rsqr_pow2 in H1,H2.
   change (pos eps') with (/2 * eps)%R in H1,H2. nra. }
 apply Rcomplements.Rabs_lt_between. split.
 - apply Ropp_lt_cancel. rewrite Ropp_involutive, Ropp_minus_distr.
   rewrite <- (Cmod_opp (f n)).
   apply Rle_lt_trans with (Cmod (l - f n)); [apply Cmod_triangle'|].
   now rewrite Cmod_switch.
 - rewrite <- (Cmod_opp l).
   apply Rle_lt_trans with (Cmod (f n - l)); [apply Cmod_triangle'|]. easy.
Qed.

Lemma is_lim_Cseq_ext (f g : nat -> C)(l : C) :
 (forall n, f n = g n) -> is_lim_Cseq f l -> is_lim_Cseq g l.
Proof.
 intros E. rewrite !is_lim_Cseq_proj. intros (Hf,Hg). split.
 - apply is_lim_seq_ext with (u:=Re∘f); trivial.
   intros n. unfold compose. now rewrite E.
 - apply is_lim_seq_ext with (u:=Im∘f); trivial.
   intros n. unfold compose. now rewrite E.
Qed.

Lemma is_lim_Cseq_Cmod' (a : nat -> C) (b : nat -> R) (la : C) (lb : R) :
  (forall n, Cmod (a n) <= b n) ->
  is_lim_Cseq a la -> is_lim_seq b lb -> Cmod la <= lb.
Proof.
 intros LE Ha Hb.
 assert (Ha' := is_lim_Cseq_Cmod a la Ha).
 now apply (is_lim_seq_le (Cmod∘a) b (Cmod la) lb).
Qed.

Lemma is_lim_Cseq_const (c:C) : is_lim_Cseq (fun _ => c) c.
Proof.
 rewrite is_lim_Cseq_proj. split.
 apply is_lim_seq_ext with (u:= fun _ => Re c). easy. apply is_lim_seq_const.
 apply is_lim_seq_ext with (u:= fun _ => Im c). easy. apply is_lim_seq_const.
Qed.

Lemma Lim_Cseq_const (c:C) : Lim_Cseq (fun _ => c) = c.
Proof.
 apply is_lim_Cseq_unique, is_lim_Cseq_const.
Qed.

Lemma is_lim_Cseq_plus (a b : nat -> C) (la lb : C) :
 is_lim_Cseq a la -> is_lim_Cseq b lb ->
 is_lim_Cseq (fun n => a n + b n) (la + lb).
Proof.
 rewrite !is_lim_Cseq_proj. intros (Ha1,Ha2) (Hb1,Hb2). split.
 - apply is_lim_seq_ext with (fun n => (Re ∘ a) n + (Re ∘ b) n)%R.
   + intros n. apply re_plus.
   + now apply is_lim_seq_plus'.
 - apply is_lim_seq_ext with (fun n => (Im ∘ a) n + (Im ∘ b) n)%R.
   + intros n. apply im_plus.
   + now apply is_lim_seq_plus'.
Qed.

Lemma Lim_Cseq_plus (a b : nat -> C) :
 ex_lim_Cseq a -> ex_lim_Cseq b ->
 Lim_Cseq (fun n => a n + b n) = Lim_Cseq a + Lim_Cseq b.
Proof.
 intros (la,Ha) (lb,Hb). apply is_lim_Cseq_unique.
 apply is_lim_Cseq_plus.
 - apply Lim_Cseq_correct. now exists la.
 - apply Lim_Cseq_correct. now exists lb.
Qed.

Lemma is_lim_Cseq_minus (a b : nat -> C) (la lb : C) :
 is_lim_Cseq a la -> is_lim_Cseq b lb ->
 is_lim_Cseq (fun n => a n - b n) (la - lb).
Proof.
 rewrite !is_lim_Cseq_proj. intros (Ha1,Ha2) (Hb1,Hb2). split.
 - apply is_lim_seq_ext with (fun n => (Re ∘ a) n - (Re ∘ b) n)%R.
   + intros n. unfold compose, Rminus. rewrite <- re_opp. apply re_plus.
   + now apply is_lim_seq_minus'.
 - apply is_lim_seq_ext with (fun n => (Im ∘ a) n - (Im ∘ b) n)%R.
   + intros n. unfold compose, Rminus. rewrite <- im_opp. apply im_plus.
   + now apply is_lim_seq_minus'.
Qed.

Lemma is_lim_Cseq_mult (a b : nat -> C) (la lb : C) :
 is_lim_Cseq a la -> is_lim_Cseq b lb ->
 is_lim_Cseq (fun n => a n * b n) (la * lb).
Proof.
 rewrite !is_lim_Cseq_proj. intros (Ha1,Ha2) (Hb1,Hb2). split.
 - apply is_lim_seq_ext with (fun n => (Re ∘ a) n * (Re ∘ b) n
                                     - (Im ∘ a) n * (Im ∘ b) n)%R.
   + intros n. apply re_mult.
   + apply is_lim_seq_plus'. now apply is_lim_seq_mult'.
     change (Rbar.Finite (- _)) with (Rbar.Rbar_opp (Im la * Im lb)%R).
     rewrite <- is_lim_seq_opp. now apply is_lim_seq_mult'.
 - apply is_lim_seq_ext with (fun n => (Re ∘ a) n * (Im ∘ b) n
                                     + (Im ∘ a) n * (Re ∘ b) n)%R.
   + intros n. apply im_mult.
   + apply is_lim_seq_plus'; now apply is_lim_seq_mult'.
Qed.

Lemma is_lim_Cseq_incr_n (u : nat -> C) (N : nat) l :
  is_lim_Cseq u l <-> is_lim_Cseq (fun n : nat => u (n + N)%nat) l.
Proof.
 rewrite !is_lim_Cseq_proj.
 rewrite (is_lim_seq_incr_n (Re∘_) N).
 rewrite (is_lim_seq_incr_n (Im∘_) N). easy.
Qed.

Lemma is_lim_Cseq_Clistsum (f : nat -> C -> C) (g : C -> C) l :
 (forall x, In x l -> is_lim_Cseq (fun n => f n x) (g x)) ->
 is_lim_Cseq (fun n => Clistsum (map (f n) l)) (Clistsum (map g l)).
Proof.
 induction l.
 - simpl. intros _. apply is_lim_Cseq_const.
 - intros H. simpl. apply is_lim_Cseq_plus. apply H; now left.
   apply IHl. intros x Hx. apply H; now right.
Qed.

(** More on R series *)

Lemma is_series_alt (a:nat->R) (l:R) :
 is_series a l <-> is_lim_seq (sum_n a) l.
Proof.
 reflexivity.
Qed.

Lemma ex_series_alt (a:nat->R) :
 ex_series a <-> ex_finite_lim_seq (sum_n a).
Proof.
 reflexivity.
Qed.

Lemma ex_series_Rlistsum {A} (f : nat -> A -> R) (l : list A) :
 (forall x, In x l -> ex_series (fun n => f n x)) ->
 ex_series (fun n => Rlistsum (map (f n) l)).
Proof.
 induction l.
 - intros. simpl. exists 0%R.
   change (is_lim_seq (sum_n (fun _ => R0)) R0).
   apply is_lim_seq_ext with (u:=fun _ => R0); try apply is_lim_seq_const.
   intros n. symmetry. apply sum_n_R0; trivial.
 - intros Hf. simpl.
   apply (ex_series_plus (V:=R_NM)).
   + apply Hf. now left.
   + apply IHl. intros x Hx. apply Hf. now right.
Qed.

Lemma ex_series_le_eventually {K : AbsRing} {V : CompleteNormedModule K}
  (a : nat -> V) (b : nat -> R) :
  Hierarchy.eventually (fun n => norm (a n) <= b n) ->
  ex_series b -> ex_series a.
Proof.
 intros (N,H) (l,X).
 set (b' := fun n => if n <=? N then norm (a n) else b n).
 apply (ex_series_le (K:=K) (V:=V) _ b').
 { intros n. unfold b'. case Nat.leb_spec; try lra. intros. apply H. lia. }
 exists (l + (sum_n (norm∘a) N - sum_n b N))%R.
 change (is_lim_seq (sum_n b') (l + (sum_n (norm ∘ a) N - sum_n b N)))%R.
 rewrite is_lim_seq_incr_n with (N:=N).
 apply is_lim_seq_ext
   with (u := (fun n => sum_n b (n+N) + (sum_n (norm ∘ a) N - sum_n b N))%R).
 - unfold b'. clear.
   induction n.
   + simpl. ring_simplify. apply sum_n_ext_loc. intros n Hn.
     case Nat.leb_spec; lia || easy.
   + simpl. rewrite !sum_Sn. case Nat.leb_spec; try lia. intros.
     rewrite <- IHn. simpl. change plus with Rplus. ring.
 - apply is_lim_seq_plus'. now rewrite <- is_lim_seq_incr_n.
   apply is_lim_seq_const.
Qed.

Lemma ex_series_square (a : nat -> R) :
  ex_series (Rabs∘a) -> ex_series (fun n => a n^2)%R.
Proof.
 intros H.
 apply (ex_series_le_eventually (V:=R_CNM)) with (b := Rabs∘a); trivial.
 assert (H' := ex_series_lim_0 _ H).
 destruct (H' (Rgt 1)) as (N, HP).
 { exists (mkposreal 1 ltac:(lra)). simpl. intros y Y.
   apply Rcomplements.Rabs_lt_between in Y.
   change minus with Rminus in Y; lra. }
 exists N. intros n Hn. specialize (HP n Hn).
 change norm with Rabs. rewrite Rabs_right.
 2:{ rewrite <- Rsqr_pow2. apply Rle_ge, Rle_0_sqr. }
 rewrite <- Rsqr_pow2, Rsqr_abs. unfold compose, Rsqr in *.
 rewrite <- (Rmult_1_r (Rabs (a n))) at 3.
 apply Rmult_le_compat_l; try lra. apply Rabs_pos.
Qed.

Lemma Series_rest0 (a : nat -> R) (l : R) :
 is_series a l -> forall n, is_lim_seq (sum_n_m a (S n)) (l-sum_n a n)%R.
Proof.
 intros H n.
 apply (is_lim_seq_ext_loc (fun m => sum_n a m - sum_n a n)%R).
 - exists n. intros m Hm.
   symmetry. now apply (sum_n_m_sum_n (G:=R_AbelianGroup)).
 - apply is_lim_seq_minus'; trivial. apply is_lim_seq_const.
Qed.

Lemma Series_rest (a : nat -> R) :
 ex_series a ->
 forall n, (Series a - sum_n a n = Rbar.real (Lim_seq (sum_n_m a (S n))))%R.
Proof.
 intros (l,H) n.
 rewrite (is_series_unique a l H).
 apply Series_rest0 with (n:=n) in H. apply is_lim_seq_unique in H.
 now rewrite H.
Qed.

(** Series on C *)

Lemma is_Cseries_alt (a : nat -> C) (l : C) :
 is_series a l <-> is_lim_Cseq (sum_n a) l.
Proof.
 easy.
Qed.

Definition CSeries (a : nat -> C) : C := Lim_Cseq (sum_n a).

Lemma CSeries_unique (a : nat -> C) (l : C) :
  is_series a l -> CSeries a = l.
Proof.
 intros H. apply is_lim_Cseq_unique, is_lim_Cseq_proj. split.
 - red. eapply filterlim_comp with (f := sum_n a) (g:=Re); eauto.
   intros P (eps, H'). exists eps. intros c Hc. apply H', Hc.
 - red. eapply filterlim_comp with (f := sum_n a) (g:=Im); eauto.
   intros P (eps, H'). exists eps. intros c Hc. apply H', Hc.
Qed.

Lemma CSeries_correct (a : nat -> C) :
  ex_series a -> is_series a (CSeries a).
Proof.
 intros (l & H). simpl in l. now rewrite (CSeries_unique a l).
Qed.

Lemma pos_series_pos_sum (a : nat -> R) l :
  is_series a l ->
  (forall n, 0 <= a n) ->
  forall n, sum_n a n <= l.
Proof.
 intros H Ha n. change (is_lim_seq (sum_n a) l) in H.
 apply is_lim_seq_incr_compare; trivial.
 intros m. rewrite sum_Sn. unfold plus. simpl. generalize (Ha (S m)). lra.
Qed.

Lemma pos_series_pos_lim (a : nat -> R) l :
  is_series a l -> (forall n, 0 <= a n) -> 0 <= l.
Proof.
 intros H Ha.
 apply Rle_trans with (sum_n a O).
 rewrite sum_O. apply Ha.
 now apply (pos_series_pos_sum _ _ H).
Qed.

Lemma ex_series_Cmod (a : nat -> C) :
 ex_series (Cmod ∘ a) -> ex_series a.
Proof.
 apply (ex_series_le (V := C_CNM)).
 intros. rewrite <- Complex.Cmod_norm. apply Rle_refl.
Qed.

Lemma is_series_Cmod (a : nat -> C) (l:R) :
 is_series (Cmod ∘ a) l ->
 exists l':C, is_series a l' /\ Cmod l' <= l.
Proof.
 intros H. destruct (ex_series_Cmod a) as (l' & Hl'); [now exists l|].
 simpl in l'. exists l'. split; trivial.
 assert (E := is_lim_Cseq_Cmod (sum_n a) l' Hl').
 apply (is_lim_seq_le (Cmod ∘ (sum_n a)) (sum_n (Cmod ∘ a)) (Cmod l') l);
  trivial. intros. apply sum_n_triangle.
Qed.

Lemma CSeries_Cmod (a : nat -> C) :
  ex_series (Cmod ∘ a) -> Cmod (CSeries a) <= Series (Cmod ∘ a).
Proof.
 intros (l,Hl). destruct (is_series_Cmod a l Hl) as (l' & Hl' & LE).
 erewrite CSeries_unique; eauto. erewrite is_series_unique; eauto.
Qed.

Lemma CSeries_rest0 (a : nat -> C) (l : C) :
 is_series a l -> forall n, is_lim_Cseq (sum_n_m a (S n)) (l-sum_n a n).
Proof.
 intros H n.
 assert (H' : is_lim_Cseq (fun m => sum_n a m - sum_n a n) (l-sum_n a n)).
 { apply is_lim_Cseq_minus; trivial. apply is_lim_Cseq_const. }
 rewrite is_lim_Cseq_proj in *. split.
 - apply (is_lim_seq_ext_loc (Re ∘ (fun m => sum_n a m - sum_n a n)));
    try apply H'.
   exists n. intros m Hm. unfold compose. f_equal.
   symmetry. now apply (sum_n_m_sum_n (G:=Complex.C_AbelianGroup)).
 - apply (is_lim_seq_ext_loc (Im ∘ (fun m => sum_n a m - sum_n a n)));
    try apply H'.
   exists n. intros m Hm. unfold compose. f_equal.
   symmetry. now apply (sum_n_m_sum_n (G:=Complex.C_AbelianGroup)).
Qed.

Lemma CSeries_rest (a : nat -> C) :
 ex_series a ->
 forall n, CSeries a - sum_n a n = Lim_Cseq (sum_n_m a (S n)).
Proof.
 intros (l,H) n. simpl in l.
 rewrite (CSeries_unique a l H).
 apply CSeries_rest0 with (n:=n) in H. apply is_lim_Cseq_unique in H.
 now rewrite H.
Qed.

Lemma CSeries_RtoC_impl (a : nat -> R) (l:C) :
  is_series (RtoC∘a) l -> is_series a (Re l) /\ Im l = 0%R.
Proof.
 intros H.
 change (is_lim_Cseq (sum_n (RtoC∘a)) l) in H.
 rewrite is_lim_Cseq_proj in H. destruct H as (H1,H2).
 apply is_lim_seq_ext with (v:=sum_n a) in H1.
 2:{ intros n. unfold compose. rewrite re_sum_n. now apply sum_n_ext. }
 apply is_lim_seq_ext with (v:=fun _ => 0%R) in H2.
 2:{ intros n. unfold compose. rewrite im_sum_n. apply sum_n_R0. }
 split. apply H1. apply is_lim_seq_unique in H2.
 rewrite Lim_seq_const in H2. now injection H2.
Qed.

Lemma CSeries_RtoC (a : nat -> R) (l:R) :
  is_series (RtoC∘a) (RtoC l) <-> is_series a l.
Proof.
 split.
 - intros H. change l with (Re (RtoC l)). now apply CSeries_RtoC_impl.
 - intros H.
   change (is_lim_Cseq (sum_n (RtoC∘a)) l).
   rewrite is_lim_Cseq_proj; simpl. split.
   + apply is_lim_seq_ext with (u:=sum_n a); try easy.
     intros n. unfold compose. rewrite re_sum_n. now apply sum_n_ext.
   + apply is_lim_seq_ext with (u:=fun _ => 0%R); try apply is_lim_seq_const.
     intros n. unfold compose. rewrite im_sum_n. symmetry.
     now apply sum_n_R0.
Qed.

(** Power series on C *)

Definition is_CPowerSeries (a : nat -> C) (z lim : C) :=
  is_lim_Cseq (sum_n (fun n => a n * z^n)) lim.

Definition ex_CPowerSeries (a : nat -> C) (z : C) :=
  exists lim, is_CPowerSeries a z lim.

Definition CPowerSeries (a : nat -> C) (z : C) : C :=
  CSeries (fun k => a k * z ^ k).

Lemma CPowerSeries_unique (a : nat -> C) (z l : C) :
  is_CPowerSeries a z l -> CPowerSeries a z = l.
Proof.
 apply CSeries_unique.
Qed.

Lemma CPowerSeries_correct (a : nat -> C) z :
  ex_CPowerSeries a z -> is_CPowerSeries a z (CPowerSeries a z).
Proof.
 apply CSeries_correct.
Qed.

Lemma Cmod_prod_aux a b n : Cmod b <= 1 -> Cmod (a * b^n) <= Cmod a.
Proof.
 intros Hb.
 rewrite Cmod_mult, Cmod_pow.
 rewrite <- (Rmult_1_r (Cmod a)) at 2.
 apply Rmult_le_compat_l. apply Cmod_ge_0.
 apply Rpow_le1. split. apply Cmod_ge_0. apply Hb.
Qed.

Lemma CPowerSeries_bound1 (a : nat -> C) l z :
  is_series (Cmod ∘ a) l -> Cmod z <= 1 ->
  forall n, Cmod (sum_n (fun k => a k * z^k) n) <= l.
Proof.
 intros Ha Hz n.
 eapply Rle_trans; [apply sum_n_triangle|].
 apply Rle_trans with (sum_n (Cmod ∘ a) n);
  [apply sum_n_le | apply pos_series_pos_sum; eauto; intros; apply Cmod_ge_0].
 intros m. now apply Cmod_prod_aux.
Qed.

Lemma CPowerSeries_bound2 (a : nat -> C) l z :
  is_series (Cmod ∘ a) l -> Cmod z <= 1 ->
  Cmod (CPowerSeries a z) <= l.
Proof.
 intros H Hz.
 unfold CPowerSeries. rewrite <- (is_series_unique (Cmod∘a) l H).
 eapply Rle_trans.
 - apply CSeries_Cmod.
   unfold compose.
   apply (ex_series_le (V :=R_CNM)) with (b:=Cmod∘a);
    try now exists l.
   intros n. change norm with Rabs.
   rewrite Rabs_right by apply Rle_ge, Cmod_ge_0. now apply Cmod_prod_aux.
 - apply Series_le. 2:now exists l.
   intros n. unfold compose. split; try apply Cmod_ge_0.
   now apply Cmod_prod_aux.
Qed.

Lemma CPowerSeries_bound3 (a : nat -> C) (l:R) z :
 is_series (Cmod ∘ a) l -> Cmod z <= 1 ->
 forall n,
 Cmod (CPowerSeries a z - sum_n (fun k => a k * z^k) n) <=
 l - sum_n (Cmod ∘ a) n.
Proof.
 intros H Hz n.
 assert (H' : ex_series (fun k => a k * z^k)).
 { apply ex_series_Cmod.
   apply (ex_series_le (V :=R_CNM)) with (b:=Cmod∘a);
     try now exists l.
   intros m. change norm with Rabs.
   rewrite Rabs_right by apply Rle_ge, Cmod_ge_0. now apply Cmod_prod_aux. }
 destruct H' as (l',H'). simpl in l'.
 unfold CPowerSeries. rewrite (CSeries_unique _ _ H').
 assert (R := Series_rest0 _ _ H n).
 assert (R' := CSeries_rest0 _ _ H' n).
 eapply is_lim_Cseq_Cmod'; eauto.
 intros m. eapply Rle_trans; [apply sum_n_m_triangle|].
 apply sum_n_m_le. intros k. now apply Cmod_prod_aux.
Qed.

Lemma is_powerseries_invlin r x : r<>0 -> Cmod (r*x) < 1 ->
 is_CPowerSeries (fun n => r^S n) x (/ (/r - x)).
Proof.
 intros Hr Hx.
 apply is_lim_Cseq_ext with (fun n => (1 - (r*x)^S n)/(/r-x)).
 { intros n. rewrite <- (Cmult_1_l (sum_n _ _)).
   rewrite <- (Cinv_l (/r-x)) at 2.
   2:{ intros E. apply Ceq_minus in E.
       rewrite <- E, Cinv_r, Cmod_1 in Hx; trivial. lra. }
   unfold Cdiv. rewrite Cmult_comm, <- Cmult_assoc. f_equal.
   rewrite sum_n_ext with (b:=fun k => r * (r*x)^k).
   2:{ intros k. now rewrite Cpow_S, Cpow_mul_l, Cmult_assoc. }
   rewrite sum_n_Cmult_l, Cmult_assoc.
   replace ((/r-x)*r) with (1-r*x) by now field.
   symmetry. apply sum_n_Cpow. }
 unfold Cdiv. rewrite <- (Cmult_1_l (/(/r-x))) at 1.
 apply is_lim_Cseq_mult; [|apply is_lim_Cseq_const].
 replace 1 with (1-0) at 1 by lca.
 apply is_lim_Cseq_minus. apply is_lim_Cseq_const.
 apply is_lim_Cseq_0_Cmod.
 apply is_lim_seq_ext with (fun n => (Cmod (r*x))^S n)%R.
 - intros n. unfold compose. now rewrite Cmod_pow.
 - rewrite <- is_lim_seq_incr_1. apply is_lim_seq_geom.
   now rewrite Rabs_right by apply Rle_ge, Cmod_ge_0.
Qed.

Lemma PowerSeries_invlin r x : r<>0 -> Cmod (r*x) < 1 ->
 CPowerSeries (fun n => r^S n) x = / (/r - x).
Proof.
 intros. now apply CPowerSeries_unique, is_powerseries_invlin.
Qed.

(** Delaying a sequence with extra initial zeros.
    See also Coquelicot.PSeries.PS_incr_n someday. *)

Definition delay {G:AbelianMonoid} (a:nat->G) p :=
  fun n => if n <? p then zero else a (n-p)%nat.

Lemma sum_n_delay {G:AbelianMonoid} (a:nat->G) p n :
  sum_n (delay a p) (n+p) = sum_n a n.
Proof.
 induction n.
 - rewrite Nat.add_0_l, sum_O.
   destruct p.
   + now rewrite sum_O.
   + rewrite sum_Sn.
     erewrite sum_n_ext_loc, sum_n_zero.
     2:{ intros k K. unfold delay. case Nat.ltb_spec; easy || lia. }
     unfold delay. simpl.
     case Nat.ltb_spec; try lia. intros _.
     replace (p-p)%nat with O by lia. apply plus_zero_l.
 - simpl. rewrite !sum_Sn, IHn. f_equal. unfold delay.
   case Nat.ltb_spec; try lia. intros _. f_equal. lia.
Qed.

Lemma delay_comp {G G':AbelianMonoid} (h:G->G') p (a:nat->G) :
 h zero = zero -> forall n, delay (h∘a) p n = h (delay a p n).
Proof.
 intros H n. unfold delay. now case Nat.ltb.
Qed.

Lemma delay_series_R p (a:nat->R) l :
  is_series a l -> is_series (delay a p) l.
Proof.
 intros H.
 change (is_lim_seq (sum_n (delay a p)) l).
 apply is_lim_seq_incr_n with (N:=p).
 eapply is_lim_seq_ext; [|apply H].
 intros n. symmetry. apply sum_n_delay.
Qed.

Lemma delay_powerseries_R p a x lim :
  is_series (fun n => a n * x^n)%R lim ->
  is_series (fun n => delay a p n * x^n)%R (x^p * lim)%R.
Proof.
 intros H.
 rewrite is_series_alt.
 rewrite is_lim_seq_incr_n with (N:=p).
 apply is_lim_seq_ext with (fun n => x^p * sum_n (fun k => a k * x^k) n)%R.
 { intros n. rewrite <- (sum_n_mult_l (K:=R_AbsRing)).
   rewrite <- sum_n_delay with (p:=p). apply sum_n_ext. clear n.
   intros n. unfold delay. case Nat.ltb_spec; intros.
   - change zero with R0. lra.
   - change mult with Rmult.
     rewrite !(Rmult_comm (a _)), <- Rmult_assoc, <- pow_add.
     f_equal. f_equal. lia. }
 apply is_lim_seq_mult'; trivial using is_lim_seq_const.
Qed.

Lemma delay_powerseries p a z lim :
  is_CPowerSeries a z lim ->
  is_CPowerSeries (delay a p) z (z^p * lim).
Proof.
 unfold is_CPowerSeries. intros H.
 rewrite is_lim_Cseq_incr_n with (N:=p).
 apply is_lim_Cseq_ext with (fun n => z^p * sum_n (fun k => a k * z^k) n).
 { intros n. rewrite <- sum_n_Cmult_l.
   rewrite <- sum_n_delay with (p:=p). apply sum_n_ext. clear n.
   intros n. unfold delay. case Nat.ltb_spec; intros.
   - change zero with C0. lca.
   - rewrite Cmult_assoc, (Cmult_comm (z^p)), <- Cmult_assoc. f_equal.
     rewrite <- Cpow_add. f_equal. lia. }
 apply is_lim_Cseq_mult; trivial using is_lim_Cseq_const.
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
   apply ElemFct.continuous_cos_comp, continuous_id.
 - apply continuous_ext with sin; try easy.
   apply ElemFct.continuous_sin_comp, continuous_id.
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

Lemma CInt_Cexp_0 : CInt (fun _ => Cexp 0) 0 (2 * PI) = 2*PI.
Proof.
 rewrite CInt_const, Cexp_0, <- RtoC_minus, Rminus_0_r, RtoC_mult. lca.
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

(** The core idea in Siegel's 1944 article :
    if a function g has no poles inside the unit circle,
    the integral of g(z)*g(/z)/z on the unit circle is
    the series of the square of the coefficients of g as power series. *)

Definition Mu (g : C -> C) :=
 /(2*PI) * CInt (fun t => g (Cexp t) * g (Cexp (-t))) 0 (2*PI).

Lemma Mu_aux1 (a : nat -> C) n :
  let h := fun t : R => sum_n (fun k : nat => a k * Cexp (k * t)) n in
  CInt (fun x => h x * h (-x)%R) 0 (2 * PI)
  = 2 * PI * sum_n (fun k => a k ^2) n.
Proof.
 induction n.
 - intros h. unfold h. rewrite !sum_O.
   rewrite (RInt_ext (V:=C_CNM)) with (g:=fun x => (a O)^2).
   2:{ intros x _. rewrite !sum_O. simpl. rewrite !Rmult_0_l.
       rewrite Cexp_0. fixeq C. ring. }
   rewrite RInt_const.
   rewrite Complex.scal_R_Cmult.
   change Coquelicot.Complex.Cmult with Cmult.
   change Coquelicot.Complex.RtoC with RtoC.
   now rewrite Rminus_0_r, RtoC_mult.
 - intros h. rewrite !sum_Sn.
   set (h1 := fun t => sum_n (fun k : nat => a k * Cexp (k * t)) n) in *.
   assert (Hh : forall x, continuous h x).
   { intros x. apply sum_n_continuous. intros m _. simpl.
     apply (continuous_scal_r (V:=Complex.C_NormedModule)).
     apply continuous_Cexpn. }
   assert (Hh1 : forall x, continuous h1 x).
   { intro x. apply sum_n_continuous. intros m _. simpl.
     apply (continuous_scal_r (V:=Complex.C_NormedModule)).
     apply continuous_Cexpn. }
   simpl in *.
   set (h2 := fun t => a (S n) * Cexp (S n * t)).
   assert (Hh2 : forall x, continuous h2 x).
   { intros x. apply (continuous_scal_r (V:=Complex.C_NormedModule)).
     apply continuous_Cexpn. }
   assert (E : forall t, h t = h1 t + h2 t).
   { intros t. unfold h. now rewrite sum_Sn. }
   rewrite (RInt_ext (V:=C_CNM))
    with (g:=fun x => h1(x)*h1(-x)%R + h1(x)*h2(-x)%R +
                      h2(x)*h1(-x)%R + h2(x)*h2(-x)%R).
   2:{ intros x _. rewrite !E. fixeq C. ring. }
   rewrite !(RInt_plus (V:=C_CNM));
    try apply (ex_RInt_continuous (V:=C_CNM));
    try intros x _.
   2:{ apply continuous_Cmult; trivial. apply continuous_comp; trivial.
       apply (continuous_opp (V:=R_NM)), continuous_id. }
   2:{ apply continuous_Cmult; trivial. apply continuous_comp; trivial.
       apply (continuous_opp (V:=R_NM)), continuous_id. }
   2:{ apply (continuous_plus (V:=C_NM));
        apply continuous_Cmult; trivial; apply continuous_comp; trivial;
        apply (continuous_opp (V:=R_NM)), continuous_id. }
   2:{ apply continuous_Cmult; trivial. apply continuous_comp; trivial.
       apply (continuous_opp (V:=R_NM)), continuous_id. }
   2:{ apply (continuous_plus (V:=C_NM));
       [apply (continuous_plus (V:=C_NM))|];
       apply continuous_Cmult; trivial; apply continuous_comp; trivial;
        apply (continuous_opp (V:=R_NM)), continuous_id. }
   2:{ apply continuous_Cmult; trivial. apply continuous_comp; trivial.
       apply (continuous_opp (V:=R_NM)), continuous_id. }
   rewrite IHn.
   rewrite (RInt_ext (V:=C_CNM))
     with (g:=fun x => a (S n) * sum_n (fun k => a k * Cexp ((S n-k)%nat*-x)) n).
   rewrite CInt_scal, CInt_sum_n_opp; try lia. rewrite Cmult_0_r.
   2:{ apply (ex_RInt_continuous (V:=C_CNM)).
       intros x _. apply sum_n_continuous. intros i _.
       apply continuous_Cmult. apply continuous_const.
       apply (continuous_comp Ropp (fun x => Cexp ((S n-i)%nat * x))).
       apply (continuous_opp (V:=R_NM)), continuous_id.
       apply continuous_Cexpn. }
   2:{ intros x _. unfold h1, h2.
       rewrite Cmult_assoc, (Cmult_comm _ (a (S n))), <- !Cmult_assoc.
       f_equal.
       rewrite <- sum_n_Cmult_r. apply sum_n_ext_loc. intros m Hm.
       rewrite <- Cmult_assoc. f_equal. rewrite <- Cexp_add. f_equal.
       rewrite minus_INR by lia. lra. }
   rewrite (RInt_ext (V:=C_CNM))
     with (g:=fun x => a (S n) * sum_n (fun k => a k * Cexp ((S n-k)%nat*x)) n).
   rewrite CInt_scal, CInt_sum_n; try lia. rewrite Cmult_0_r.
   2:{ apply (ex_RInt_continuous (V:=C_CNM)).
       intros x _. apply sum_n_continuous. intros.
       apply continuous_Cmult. apply continuous_const.
       apply continuous_Cexpn. }
   2:{ intros x _. unfold h1, h2.
       rewrite <- !Cmult_assoc. f_equal. rewrite Cmult_comm.
       rewrite <- sum_n_Cmult_r. apply sum_n_ext_loc. intros m Hm.
       rewrite <- Cmult_assoc. f_equal. rewrite <- Cexp_add. f_equal.
       rewrite minus_INR by lia. lra. }
   rewrite (RInt_ext (V:=C_CNM))
     with (g:=fun x => a (S n)^2).
   2:{ intros x _. unfold h2. ring_simplify.
       rewrite <- Cmult_assoc, <- Cexp_add.
       replace (Rplus _ _) with 0%R by lra. rewrite Cexp_0. apply Cmult_1_r. }
   rewrite CInt_const, RtoC_mult. change plus with Cplus. fixeq C. ring.
Qed.

Lemma Mu_series_square (a : nat -> C) (g : C -> C) :
 ex_series (Cmod ∘ a) ->
 (forall z, Cmod z = 1%R -> g z = CPowerSeries a z) ->
 Mu g = CSeries (fun n => (a n)^2).
Proof.
 intros (l & Hl) Hg. simpl in l.
 assert (Hg' : forall x, continuous (g∘Cexp) x).
 { intros x. apply continuous_ext with (f := CPowerSeries a∘Cexp).
   - intros y. symmetry. apply Hg, Cmod_Cexp.
   - apply CPowerSeries_Cexp_continuous; now exists l. }
 symmetry. apply CSeries_unique.
 intros P (eps,HP). simpl in P, HP.
 assert (LT : 0 < eps / Rmax 1 (4*l)).
 { apply Rmult_lt_0_compat. apply eps.
   apply Rinv_0_lt_compat. generalize (Rmax_l 1 (4*l)); lra. }
 set (eps' := mkposreal _ LT).
 destruct (Hl (ball l eps')) as (N & HN); try (now exists eps').
 exists N. intros n Hn. apply HP, C_ball. clear HP.
 specialize (HN n Hn).
 change (ball _ _ _) with (Rabs ((sum_n (Cmod ∘ a) n)-l) < eps') in HN.
 set (h := fun t => sum_n (fun k => a k * Cexp (k*t)) n). simpl in h.
 assert (Hh : forall x, continuous h x).
 { intros. apply sum_n_continuous. intros. apply continuous_Cmult.
   apply continuous_const. apply continuous_Cexpn. }
 assert (LE : forall t:R,
              Cmod (g(Cexp t)*g(Cexp (-t)) - h t * h(-t)%R) <= eps/2).
 { intros t.
   replace (_ - _) with
       (g (Cexp t) * (g (Cexp (- t)) - h (-t)%R)
        + (g (Cexp t) - h t)*h(-t)%R) by ring.
   eapply Rle_trans; [apply Cmod_triangle| ].
   rewrite !Cmod_mult.
   rewrite !Hg by (rewrite Cmod_Cexp; lra).
   assert (Cmod (CPowerSeries a (Cexp t)) <= l).
   { apply CPowerSeries_bound2; trivial. rewrite Cmod_Cexp; lra. }
   assert (D : forall t', Cmod (CPowerSeries a (Cexp t') - h t') <= eps').
   { intros t'. unfold h.
     rewrite sum_n_ext with (b := fun k => a k * Cexp t'^k).
     2:{ intros m. rewrite Cexp_pow. f_equal. f_equal. lra. }
     eapply Rle_trans. apply CPowerSeries_bound3; eauto.
     rewrite Cmod_Cexp; lra.
     apply Rabs_def2 in HN. lra. }
   apply Rle_trans with (l*eps' + eps'*l)%R.
   apply Rplus_le_compat.
   - apply Rmult_le_compat; try apply Cmod_ge_0; easy.
   - apply Rmult_le_compat; try apply Cmod_ge_0; try easy.
     { unfold h. rewrite sum_n_ext with (b := fun k => a k * Cexp (-t)^k).
       2:{ intros m. rewrite Cexp_pow. f_equal. f_equal. lra. }
       apply CPowerSeries_bound1; trivial. rewrite Cmod_Cexp; lra. }
     apply -> Rcomplements.Rle_div_r; try lra. ring_simplify.
     unfold eps'. simpl. unfold Rdiv. rewrite <- Rmult_assoc.
     apply <- Rcomplements.Rle_div_l.
     2:{ apply Rlt_gt. apply Rlt_le_trans with 1%R. lra. apply Rmax_l. }
     rewrite (Rmult_comm eps). apply Rmult_le_compat_r; try apply Rmax_r.
     generalize (cond_pos eps); lra. }
 assert (LE' : Cmod (CInt (fun t => g (Cexp t) * g (Cexp (- t))
                                   - h t * h (- t)%R) 0 (2*PI))
               <= 2*PI * (eps/2)).
 { replace (2*PI)%R with (2*PI - 0)%R at 2 by lra.
   apply CInt_Cmod.
   - generalize Rgt_2PI_0; lra.
   - apply (ex_RInt_continuous (V:=C_CNM)).
     intros x _.
     apply (continuous_minus (V:=C_CNM));
      apply continuous_Cmult; trivial.
     apply (continuous_comp Ropp (g∘Cexp)); trivial.
     apply (continuous_opp (V:=R_CNM)), continuous_id.
     apply (continuous_comp Ropp h); trivial.
     apply (continuous_opp (V:=R_CNM)), continuous_id.
   - intros x _. apply (LE x). }
 clear LE HN eps' LT.
 rewrite CInt_minus in LE'.
 2:{ apply (ex_RInt_continuous (V:=C_CNM)).
     intros x _. apply continuous_Cmult; trivial.
     apply (continuous_comp Ropp (g∘Cexp)); trivial.
     apply (continuous_opp (V:=R_CNM)), continuous_id. }
 2:{ apply (ex_RInt_continuous (V:=C_CNM)).
     intros x _. apply continuous_Cmult; trivial.
     apply continuous_comp; trivial.
     apply (continuous_opp (V:=R_NM)), continuous_id. }
 apply Rmult_le_compat_r with (r:=(/(2*PI))%R) in LE'.
 2:{ apply Rlt_le. apply Rinv_0_lt_compat, Rgt_2PI_0. }
 replace (2 * PI * (eps / 2) * / (2 * PI))%R with (eps/2)%R in LE'.
 2:{ field. apply PI_neq0. }
 rewrite <- (Rabs_right (/(2*PI))%R) in LE'.
 2:{ apply Rle_ge, Rlt_le. apply Rinv_0_lt_compat, Rgt_2PI_0. }
 rewrite <- Cmod_R, <- Cmod_mult in LE'.
 rewrite RtoC_inv, RtoC_mult in LE'.
 unfold Cminus in LE'. rewrite Cmult_plus_distr_r in LE'.
 rewrite Cmult_comm in LE'. fold (Mu g) in LE'.
 rewrite <- Copp_mult_distr_l in LE'.
 assert (E := Mu_aux1 a n). fold h in E. rewrite E in LE'. clear E.
 set (p := C2*PI) in LE'.
 rewrite (Cmult_comm p), <- Cmult_assoc, Cinv_r, Cmult_1_r in LE'.
 2:{ unfold p. rewrite <- RtoC_mult. apply RtoC_inj_neq.
     generalize Rgt_2PI_0; lra. }
 unfold Cminus. eapply Rle_lt_trans; [apply LE'| ].
 generalize (cond_pos eps). lra.
Qed.

(** ThePoly's reciprocal polynomial *)

Definition RevPoly q : Polynomial := monom C1 (q+1) +, [-C1;C1].

Lemma RevPoly_eval q x : Peval (RevPoly q) x = x^S q + x - 1.
Proof.
 unfold RevPoly. rewrite !Pplus_eval, !monom_eval.
 rewrite Nat.add_1_r, Cmult_1_l.
 replace (Peval [-C1;C1] x) with (x-1) by (cbn;ring). ring.
Qed.

Lemma RevPoly_root_carac r q : Root r (RevPoly q) <-> r^(S q) + r - 1 = 0.
Proof.
 unfold Root. now rewrite RevPoly_eval.
Qed.

Lemma revroot_nz q : ~ Root C0 (RevPoly q).
Proof.
 rewrite !RevPoly_root_carac. simpl. rewrite Cmult_0_l, Cplus_0_l.
 rewrite <- RtoC_minus. apply RtoC_inj_neq. lra.
Qed.

Lemma RevPoly_eqn q x :
  x<>0 -> x^S q + x - 1 = - x^S q * ((/x)^S q - (/x)^q -1).
Proof.
 intros Hx.
 unfold Cminus.
 rewrite !Cmult_plus_distr_l.
 rewrite <- !Copp_mult_distr_r, Cmult_1_r, Copp_involutive.
 rewrite <- !Copp_mult_distr_l, Copp_involutive.
 rewrite <- Cpow_mul_l, Cinv_r, Cpow_1_l by trivial.
 rewrite Cpow_S at 2.
 rewrite <- Cmult_assoc, <- Cpow_mul_l, Cinv_r, Cpow_1_l; trivial.
 ring.
Qed.

Lemma RevPoly_deg q : degree (RevPoly q) = S q.
Proof.
 unfold RevPoly.
 rewrite Pplus_comm.
 destruct (Nat.eq_dec q 0) as [->|Hq].
 - simpl. rewrite Cplus_0_r. apply degree_is_1.
   rewrite <- RtoC_plus. intros E. apply RtoC_inj in E. lra.
 - rewrite Pplus_degree2.
   rewrite monom_degree. lia. apply C1_neq_C0.
   rewrite monom_degree. 2:apply C1_neq_C0.
   rewrite degree_is_1. lia. apply C1_neq_C0.
Qed.

Lemma RevPoly_monic (q:nat) : q<>O -> monic (RevPoly q).
Proof.
 intros Hq.
 unfold RevPoly. rewrite Pplus_comm. unfold monic.
 rewrite topcoef_plus_ltdeg. apply topcoef_monom.
 rewrite monom_degree. 2:apply C1_neq_C0.
 rewrite degree_is_1. lia. apply C1_neq_C0.
Qed.

Lemma RevRoot_carac q x : Root x (RevPoly q) <-> Root (/x) (ThePoly q).
Proof.
 split.
 - intros H.
   assert (Hx : x <> 0). { intros ->. now apply (revroot_nz q). }
   rewrite RevPoly_root_carac in H. rewrite ThePoly_root_carac.
   rewrite RevPoly_eqn in H by trivial.
   apply Cmult_integral in H. destruct H as [H|H].
   + apply (Cpow_nonzero x (S q)) in Hx.
     destruct Hx. now rewrite <- (Copp_involutive (x^S q)), H, Copp_0.
   + apply Cminus_eq_0 in H. rewrite <- H. ring.
 - intros H.
   destruct (Ceq_dec x 0) as [->|N].
   + replace (/0) with 0 in H. now apply root_nz in H.
     unfold Cinv. simpl. rewrite Rmult_0_l, Rplus_0_l.
     unfold Rdiv. now rewrite Ropp_0, !Rmult_0_l.
   + rewrite RevPoly_root_carac. rewrite ThePoly_root_carac in H.
     rewrite RevPoly_eqn, H by trivial. ring.
Qed.

(** Predicates about secondary roots of ThePoly *)

Definition ThePoly_SndRootsLt1 q :=
  forall x, Root x (ThePoly q) -> x<>mu q -> Cmod x < 1.

Definition ThePoly_ExSndRootGe1 q :=
  exists x, Root x (ThePoly q) /\ x<>mu q /\ 1 <= Cmod x.

Lemma ThePoly_SndRoots_neg q :
  ThePoly_ExSndRootGe1 q <-> ~ThePoly_SndRootsLt1 q.
Proof.
 split.
 - intros (x & Hx & N & LE) H. specialize (H x Hx N). lra.
 - unfold ThePoly_ExSndRootGe1, ThePoly_SndRootsLt1. intros H.
   destruct (SortedRoots_exists q) as (l & Hl).
   assert (H1 := SortedRoots_length q l Hl).
   assert (H2 := SortedRoots_roots q l Hl).
   assert (H3 := SortedRoots_mu q l Hl).
   destruct q as [ | q].
   + destruct H. intros r. rewrite <- H2. destruct l as [|r' [|] ]; try easy.
     unfold Cnth in H3. simpl in *. subst r'. intuition.
   + assert (l @ 1 <> mu (S q)).
     { rewrite <- H3. intro E.
       destruct Hl as (_,Hl). apply Csorted_alt in Hl.
       rewrite StronglySorted_nth in Hl. specialize (Hl 0%nat 1%nat lia).
       rewrite E in Hl. revert Hl. apply Cgt_order. }
     exists (l @ 1); repeat split; trivial.
     * rewrite <- H2. apply nth_In; lia.
     * apply Rnot_lt_le. intros H4. apply H.
       intros r Hr Hr'. rewrite <- H2 in Hr.
       eapply Rle_lt_trans; [ | apply H4 ].
       apply SortedRoots_Cmod_sorted in Hl.
       rewrite StronglySorted_nth in Hl.
       destruct (In_nth l r 0 Hr) as (i & Hi & <-).
       change (nth i l 0) with (l @ i) in *.
       destruct i as [|[|i] ]; try lra. intuition.
       apply Rge_le, Hl. lia.
Qed.

(** Main goal for the moment : showing that 5<=q implies ThePoly_ExSndRootGe1.
    Later we will prove that 5<=q implies ThePoly_ExSndRootsGt1.
    For lower values of q, see LimCase2, LimCase3, LimCase4.

   Beware: these predicates about ThePoly do not exactly translate to
   (mu q) being a Pisot number or not. Indeed, ThePoly is sometimes reducible
   on Z, hence not the minimal polynomial of (mu q). This occurs when
   q = 4 mod 6, see later. *)

(** The key functions in Siegel's 1944 article.
    - f is ThePoly/RevPoly
    - g is f without its pole at (tau q)
    - h is here an intermediate step for convenience : 1/RevPoly without
      its pole at (tau q).
*)

Definition f q x := (x^S q-x^q-1) / (x^S q + x -1).

Definition g q x := (1 - mu q * x) * f q x.

Definition h q x := (1 - mu q * x) / (x^S q + x -1).

Lemma ff q x : x<>0 -> ~Root x (ThePoly q) -> ~Root x (RevPoly q) ->
  f q x * f q (/x) = 1.
Proof.
 intros H1 H2 H3. unfold f.
 rewrite RevPoly_eqn by trivial.
 rewrite RevPoly_eqn, !Cinv_inv by now apply nonzero_div_nonzero.
 rewrite !Cpow_inv. field. repeat split; try now apply Cpow_nonzero.
 - intro E. apply H2, ThePoly_root_carac.
   apply Cminus_eq_0 in E. rewrite <- E. ring.
 - rewrite Cpow_S at 1.
   replace (_-_-_) with ((-x^q)*(x^S q + x - 1)) by ring.
   intros E. apply Cmult_integral in E. destruct E as [E|E].
   + apply (Cpow_nonzero x q) in H1. apply H1.
     rewrite <- (Copp_involutive (x^q)), E. lca.
   + apply H3. now apply RevPoly_root_carac.
Qed.

(** Future PowerSeries coefs for f g h *)

Definition dh q n : R :=
 if n =? 0 then (-1)%R else (mu q * A q (n-q-1) - A q (n-q))%R.

Definition df q n : nat :=
 (if n <? q then 1 else A q (n-q-1) + A q (n-2*q))%nat.

Definition dg q n : R :=
 if n =? 0 then 1%R else (df q n - mu q * df q (n-1))%R.

Lemma df_1 q n : (n < q -> df q n = 1)%nat.
Proof.
 unfold df. case Nat.ltb_spec; lia.
Qed.

Lemma df_2 q n : (q<>0 -> n = q \/ n = S q -> df q n = 2)%nat.
Proof.
 unfold df. case Nat.ltb_spec; try lia. intros. rewrite !A_base; lia.
Qed.

Lemma df_lin q n : (S q<=n<=2*q -> df q n = S n-q)%nat.
Proof.
 unfold df. case Nat.ltb_spec; try lia; intros. rewrite !A_base; lia.
Qed.

(** Partial Fraction Decomposition *)

Definition gencoef l i := / G_big_mult (map (fun r => l@i - r) (remove_at i l)).

Lemma gencoef_nz l i : NoDup l -> (i < length l)%nat -> gencoef l i <> 0.
Proof.
 intros Hl Hi.
 apply nonzero_div_nonzero.
 rewrite <- Peval_linfactors.
 change (~Root (l@i) (linfactors (remove_at i l))).
 rewrite <- linfactors_roots.
 apply remove_at_notIn; trivial.
Qed.

Lemma inv_linfactors_partfrac (l:list C) : l<>[] -> NoDup l ->
 forall x, ~In x l ->
 Cinv (Peval (linfactors l) x) =
  big_sum (fun i => gencoef l i / (x - l@i)) (length l).
Proof.
 intros Hl0 Hl x Hx.
 symmetry. apply Cinv_eq.
 rewrite (@big_sum_mult_r _ _ _ _ C_is_ring).
 rewrite big_sum_eq_bounded with
     (g := fun i => Peval ([gencoef l i] *, linfactors (remove_at i l)) x).
 2:{ intros i Hi. rewrite Pmult_eval. simpl. rewrite Pconst_eval.
     unfold Cdiv. rewrite <- Cmult_assoc. f_equal.
     rewrite (linfactors_perm l (l@i :: remove_at i l)).
     2:{ rewrite <- insert_permut with (n:=i).
         unfold Cnth. now rewrite insert_at_remove_at. }
     simpl. rewrite Pmult_eval. rewrite cons_eval, Pconst_eval. field.
     rewrite <- Ceq_minus. contradict Hx. subst. now apply nth_In. }
 rewrite <- Psum_eval.
 rewrite Ceq_minus. unfold Cminus. rewrite <- (Pconst_eval (-(1)) x).
 rewrite <- Pplus_eval.
 rewrite (extra_roots_implies_null _ l); trivial.
 - intros r Hr. destruct (In_nth l r 0 Hr) as (i & Hi & E).
   red. rewrite Pplus_eval, Pconst_eval, Psum_eval.
   rewrite big_sum_kronecker with (m:=i); trivial.
   + rewrite Pmult_eval, Pconst_eval, Peval_linfactors, <- E.
     unfold gencoef. rewrite Cinv_l; try lca.
     rewrite <- (Cinv_inv (G_big_mult _)). apply nonzero_div_nonzero.
     now apply gencoef_nz.
   + intros j Hj Hij. rewrite Pmult_eval.
     apply Cmult_integral. right.
     change (Root r (linfactors (remove_at j l))).
     rewrite <- linfactors_roots, <- E.
     apply remove_at_In; trivial.
 - set (p := big_sum _ _).
   assert (degree p <= pred (length l))%nat.
   { apply Psum_degree.
     intros i Hi.
     rewrite Pscale_degree by now apply gencoef_nz.
     now rewrite linfactors_degree, remove_at_length. }
   generalize (Pplus_degree1 p [-(1)]).
   generalize (degree_length [-(1)]). simpl.
   rewrite <- length_zero_iff_nil in Hl0. lia.
Qed.

(** Partial Fraction Decomposition of 1/RevPoly and h and g *)

Section PartialFraction.
Variable q : nat.
Variable Hq : q<>O.
Variable roots : list C.
Hypothesis roots_ok : SortedRoots q roots.

Lemma RevPoly_alt : RevPoly q ≅ linfactors (map Cinv roots).
Proof.
 destruct (All_roots (RevPoly q)) as (l, Hl).
 { now apply RevPoly_monic. }
 rewrite Hl.
 apply linfactors_perm.
 symmetry. apply NoDup_Permutation_bis.
 - apply FinFun.Injective_map_NoDup.
   intros x y Hx. now rewrite <- (Cinv_inv x), Hx, Cinv_inv.
   now apply (SortedRoots_nodup q).
 - rewrite map_length, (SortedRoots_length q roots) by trivial.
   now rewrite <- linfactors_degree, <- Hl, RevPoly_deg.
 - intros x. rewrite in_map_iff. intros (r & <- & Hr).
   rewrite linfactors_roots. rewrite <- Hl. rewrite RevRoot_carac.
   rewrite Cinv_inv. rewrite <- SortedRoots_roots; eauto.
Qed.

Definition coef r := / ((S q)*r-q).

Definition coef_alt i :
  (i < S q)%nat -> coef (roots@i) = gencoef (map Cinv roots) i.
Proof.
 intros Hi.
 unfold coef, gencoef. f_equal.
 rewrite <- Peval_Pdiff_linfactors.
 2:{ apply FinFun.Injective_map_NoDup.
     intros a b E. now rewrite <- (Cinv_inv a), E, Cinv_inv.
     eapply SortedRoots_nodup; eauto. }
 2:{ now rewrite map_length, (SortedRoots_length _ _ roots_ok). }
 rewrite <- RevPoly_alt.
 unfold Cnth. rewrite nth_map_indep with (d':=0); trivial.
 2:{ now rewrite (SortedRoots_length _ _ roots_ok). }
 set (r := nth _ _ _).
 unfold RevPoly. rewrite Pdiff_plus, diff_monom.
 rewrite Nat.add_1_r. simpl pred. simpl Pdiff. rewrite Cplus_0_r.
 rewrite Pplus_eval, Pmult_eval, monom_eval, Pconst_eval.
 rewrite cons_eval, Pconst_eval. ring_simplify.
 rewrite Cpow_inv.
 assert (E : r ^S q = r^q + 1).
 { rewrite <- ThePoly_root_carac. eapply SortedRoots_roots; eauto.
   apply nth_In. now rewrite (SortedRoots_length _ _ roots_ok). }
 assert (Hr : r^q <> 0).
 { apply Cpow_nonzero. intros ->.
   destruct q; try lia. rewrite !Cpow_S in E. ring_simplify in E.
   apply RtoC_inj in E. lra. }
 rewrite Cpow_S in E. rewrite <- (Cinv_l (r^q)) in E by trivial.
 rewrite <- (Cmult_1_l (r^q)) in E at 2.
 rewrite <- Cmult_plus_distr_r in E.
 apply Cmult_eq_reg_r in E; trivial.
 rewrite E at 1. rewrite S_INR, RtoC_plus. ring.
Qed.

Lemma inv_RevPoly_partfrac x : ~Root x (RevPoly q) ->
 /(x^S q + x - 1) = Clistsum (map (fun r => coef r / (x - /r)) roots).
Proof.
 intros Hx.
 rewrite <- RevPoly_eval, RevPoly_alt, inv_linfactors_partfrac.
 2:{ generalize (SortedRoots_length _ _ roots_ok). now destruct roots. }
 2:{ apply FinFun.Injective_map_NoDup.
     intros a b E. now rewrite <- (Cinv_inv a), E, Cinv_inv.
     eapply SortedRoots_nodup; eauto. }
 2:{ now rewrite linfactors_roots, <- RevPoly_alt. }
 rewrite Clistsum_map with (d:=0).
 rewrite map_length. apply big_sum_eq_bounded.
 intros i Hi.
 unfold Cnth. rewrite nth_map_indep with (d':=0); trivial.
 f_equal. symmetry. apply coef_alt.
 now rewrite <- (SortedRoots_length _ _ roots_ok).
Qed.

Definition coef' r := coef r * (1 - mu q / r).

Lemma h_partfrac x : ~Root x (RevPoly q) ->
 h q x = Clistsum (map (fun r => coef' r / (x - /r)) (tl roots)).
Proof.
 intros Hx.
 assert (E : roots = RtoC (mu q) :: tl roots).
 { rewrite <- (SortedRoots_mu _ _ roots_ok).
   generalize (SortedRoots_length _ _ roots_ok). now destruct roots. }
 unfold h. replace (1 - mu q * x) with ((-mu q) * (x - /mu q)).
 2:{ field. intros H. apply RtoC_inj in H. generalize (mu_itvl q). lra. }
 unfold Cdiv.
 rewrite <- RevPoly_eval, RevPoly_alt.
 rewrite E at 1. simpl map. simpl linfactors.
 rewrite Pmult_eval, cons_eval, Pconst_eval.
 rewrite Cmult_1_r, (Cplus_comm _ x).
 rewrite (Cmult_comm (Peval _ _)), Cinv_mult, Cmult_assoc.
 rewrite <- (Cmult_assoc (-mu q)), Cinv_r, Cmult_1_r.
 2:{ change (x - / mu q <> 0). rewrite <- Ceq_minus.
     intros ->. apply Hx. rewrite RevRoot_carac, Cinv_inv. apply mu_is_root. }
 rewrite inv_linfactors_partfrac.
 2:{ generalize (SortedRoots_length _ _ roots_ok).
     destruct roots as [|a [|b l] ]; simpl; easy || lia. }
 2:{ apply FinFun.Injective_map_NoDup.
     intros a b E'. now rewrite <- (Cinv_inv a), E', Cinv_inv.
     assert (D := SortedRoots_nodup _ _ roots_ok).
     inversion D; subst; easy. }
 2:{ contradict Hx. rewrite RevPoly_alt, <- linfactors_roots, E.
     simpl. now right. }
 rewrite (@big_sum_mult_l _ _ _ _ C_is_ring).
 rewrite Clistsum_map with (d:=0).
 rewrite map_length. apply big_sum_eq_bounded.
 intros i Hi.
 unfold Cnth. rewrite nth_map_indep with (d':=0); trivial.
 set (r := nth _ _ _). simpl. unfold Cdiv. rewrite Cmult_assoc. f_equal.
 assert (Hr' : r = roots@(S i)). { now rewrite E. }
 rewrite Hr' at 1. unfold coef'. rewrite coef_alt.
 2:{ rewrite <- (SortedRoots_length _ _ roots_ok).
     rewrite E. simpl. lia. }
 unfold gencoef. rewrite E at 2. simpl.
 unfold Cnth in *. rewrite !nth_map_indep with (d':=0); trivial.
 2:{ rewrite E. simpl. lia. }
 rewrite <- Hr'. unfold r at 2. set (m := G_big_mult _).
 rewrite !Cinv_mult. rewrite <- Cmult_assoc, (Cmult_comm (/m)), Cmult_assoc.
 f_equal. clear x Hx m.
 field; repeat split.
 - intros Hr. apply (root_nz q). rewrite <- Hr.
   apply (SortedRoots_roots _ _ roots_ok). rewrite Hr'. apply nth_In.
   rewrite E. simpl. lia.
 - intros M. apply RtoC_inj in M. generalize (mu_itvl q). lra.
 - intros E'. apply Ceq_minus in E'.
   assert (D := SortedRoots_nodup _ _ roots_ok).
   rewrite E in D. inversion_clear D. apply H. rewrite E'. now apply nth_In.
Qed.

Lemma tl_roots_nz r : In r (tl roots) -> r<>0.
Proof.
 intros IN ->.
 assert (IN' : In 0 roots).
 { destruct roots. easy. simpl. now right. }
 rewrite linfactors_roots in IN'. rewrite <- (proj1 roots_ok) in IN'.
 revert IN'. apply root_nz.
Qed.

Lemma dh_eqn n :
  RtoC (dh q n) = Clistsum (map (fun r => - coef' r * r^S n) (tl roots)).
Proof.
 assert (E : roots = RtoC (mu q) :: tl roots).
 { rewrite <- (SortedRoots_mu _ _ roots_ok).
   generalize (SortedRoots_length _ _ roots_ok). now destruct roots. }
 unfold dh.
 case Nat.eqb_spec; intros N.
 - subst n.
   rewrite map_ext_in with
       (g:=fun r => mu q * (coefB q r * r^(q-1)) - coefB q r * r^q).
   2:{ intros r R. simpl.
       unfold coef', coefB. unfold Cdiv. fold (coef r).
       replace (r^q) with (r*r^(q-1)).
       2:{ replace q with (S (q-1)) at 2 by lia. apply Cpow_S. }
       field.
       split; [apply Cpow_nonzero|]; now apply tl_roots_nz. }
   rewrite <- Clistsum_minus.
   rewrite <- map_map, <- Clistsum_factor_l.
   assert (E0 := Equation_B q roots roots_ok (q-1)).
   rewrite B_zero in E0 by lia.
   rewrite E in E0. simpl in E0. symmetry in E0.
   rewrite Cplus_comm, <- (Copp_involutive (Cmult _ _)) in E0.
   apply Cminus_eq_0 in E0. rewrite E0. clear E0.
   assert (E1 := Equation_B q roots roots_ok q).
   rewrite B_one in E1 by lia.
   rewrite E in E1. simpl in E1.
   replace (RtoC (-1)) with (Copp C1) by lca. rewrite E1.
   replace (mu q^q) with (mu q * mu q^(q-1)).
   2:{ replace q with (S (q-1)) at 5 by lia. apply Cpow_S. }
   ring.
 - rewrite RtoC_minus, RtoC_mult.
   destruct (Nat.le_gt_cases n q) as [LE|GT].
   + replace (n-q)%nat with O by lia. simpl Cminus.
     rewrite map_ext_in with
         (g:=fun r => mu q * (coefB q r * r^(q+(n-1))) - coefB q r * r^(q+n)).
     2:{ intros r R.
         unfold coef', coefB. unfold Cdiv. fold (coef r).
         replace n with (S (n-1)) at 1 3 by lia. rewrite !Cpow_add, !Cpow_S.
         field.
         split; [apply Cpow_nonzero|]; now apply tl_roots_nz. }
     rewrite <- Clistsum_minus.
     rewrite <- map_map, <- Clistsum_factor_l.
     assert (E0 := Equation_B q roots roots_ok (q+(n-1))).
     rewrite B_one in E0 by lia.
     rewrite E in E0. simpl in E0. rewrite E0 at 1. clear E0.
     assert (E1 := Equation_B q roots roots_ok (q+n)).
     rewrite B_one in E1 by lia.
     rewrite E in E1. simpl in E1. rewrite E1.
     rewrite Ceq_minus. ring_simplify.
     replace (q+n)%nat with (S (q+(n-1)))%nat by lia. rewrite Cpow_S. ring.
   + replace (mu q * _ - _) with
         (mu q * (A q (n-q-1) - tau q * A q (n-q))%R).
     2:{ unfold tau. rewrite RtoC_minus, RtoC_mult, RtoC_inv. field.
         intros E'. apply RtoC_inj in E'. generalize (mu_itvl q); lra. }
     rewrite (Equation_dA q roots) by trivial.
     rewrite Clistsum_factor_l, map_map. f_equal. apply map_ext_in.
     intros r R.
     unfold coefdA, coefA, coef'. unfold Cdiv. fold (coef r).
     unfold tau. rewrite RtoC_inv.
     rewrite !Cpow_S. replace n with (n-q+q)%nat at 2 by lia.
     rewrite Cpow_add. field. split.
     * now apply tl_roots_nz.
     * intros E'. apply RtoC_inj in E'. generalize (mu_itvl q); lra.
Qed.

Lemma ex_series_Rabs_dh :
  (forall r, In r (tl roots) -> Cmod r < 1) ->
  ex_series (Rabs ∘ dh q).
Proof.
 intros Hr.
 apply (ex_series_le (V:=R_CNM)) with
  (b:=fun n =>
        Rlistsum (map (fun r => Cmod (coef' r * r) * (Cmod r)^n)%R (tl roots))).
 { intros n. unfold compose. change norm with Rabs.
   rewrite Rabs_pos_eq by apply Rabs_pos.
   rewrite <- Cmod_R.
   rewrite dh_eqn. eapply Rle_trans; [eapply Clistsum_mod|].
   rewrite map_map. apply Rlistsum_le. intros r R.
   rewrite Cpow_S, !Cmod_mult, Cmod_opp, Cmod_pow.
   ring_simplify. lra. }
 apply ex_series_Rlistsum.
 intros r R.
 apply (ex_series_scal (V:=R_NM)).
 apply ex_series_geom. rewrite Rabs_pos_eq by apply Cmod_ge_0.
 now apply Hr.
Qed.

Lemma ex_pseries_Rabs_dh x :
  (forall r, In r (tl roots) -> Cmod r <= 1) -> Rabs x < 1 ->
  ex_series (fun n => Rabs (dh q n * x^n)).
Proof.
 intros Hr Hx.
 apply (ex_series_le (V:=R_CNM)) with
  (b:=fun n =>
   Rlistsum (map (fun r => Cmod (coef' r * r) * (Cmod (r * x))^n)%R (tl roots))).
 { intros n. change norm with Rabs. rewrite Rabs_Rabsolu.
   rewrite Rabs_mult, <- !Cmod_R, dh_eqn, <- Cmod_mult, Cmult_comm.
   rewrite Clistsum_factor_l, map_map.
   eapply Rle_trans; [eapply Clistsum_mod|]. rewrite map_map.
   apply Rlistsum_le. intros r R.
   rewrite <- RtoC_pow, Cpow_S, !Cmod_mult, Cmod_opp, !Cmod_pow.
   rewrite Rpow_mult_distr. ring_simplify. lra. }
 apply ex_series_Rlistsum.
 intros r R.
 apply (ex_series_scal (V:=R_NM)).
 apply ex_series_geom. rewrite Rabs_pos_eq by apply Cmod_ge_0.
 rewrite Cmod_mult, Cmod_R.
 apply Rle_lt_trans with (1 * Rabs x)%R; try lra.
 apply Rmult_le_compat_r. try apply Rabs_pos. now apply Hr.
Qed.

Lemma h_is_powerseries (x:C) :
 x<>tau q ->
 (forall r, In r (tl roots) -> Cmod (r*x) < 1) ->
 is_CPowerSeries (dh q) x (h q x).
Proof.
 intros Hx Hr.
 assert (E : roots = RtoC (mu q) :: tl roots).
 { rewrite <- (SortedRoots_mu _ _ roots_ok).
   generalize (SortedRoots_length _ _ roots_ok). now destruct roots. }
 assert (Hx' : ~Root x (RevPoly q)).
 { intro R. rewrite RevPoly_alt, <- linfactors_roots, E in R.
   simpl in R. destruct R as [R|R].
   - apply Hx. rewrite <- R. unfold tau. now rewrite RtoC_inv.
   - rewrite in_map_iff in R. destruct R as (r & <- & IN).
     specialize (Hr _ IN). rewrite Cinv_r, Cmod_1 in Hr; try lra.
     now apply tl_roots_nz. }
 rewrite h_partfrac by trivial.
 apply is_lim_Cseq_ext with
     (f := fun n => Clistsum (map
            (fun r => sum_n (fun k => - coef' r * (r^S k*x^k)) n) (tl roots))).
 - intros n. rewrite <- Clistsum_sum_n. apply sum_n_ext. clear n.
   intros n.
   rewrite dh_eqn.
   rewrite map_ext with (g:=fun r => x^n * (- coef' r * r ^ S n))
    by (intros; ring).
   rewrite <- map_map.
   rewrite <- Clistsum_factor_l. apply Cmult_comm.
 - apply is_lim_Cseq_Clistsum.
   intros r Hr'.
   replace (coef' r / (x - / r)) with (-coef' r * / (/r - x)).
   2:{ field; simpl; repeat split.
       - now apply tl_roots_nz.
       - intros H. apply Ceq_minus in H. specialize (Hr _ Hr').
         rewrite Cmult_comm, H, Cmod_1 in Hr. lra.
       - intros H. apply Ceq_minus in H. specialize (Hr _ Hr').
         rewrite Cmult_comm, <- H, Cmod_1 in Hr. lra. }
   apply is_lim_Cseq_ext with
       (fun n => (-coef' r)*sum_n (fun k => r^S k*x^k) n).
   { intros n. now rewrite sum_n_Cmult_l. }
   apply is_lim_Cseq_mult. apply is_lim_Cseq_const.
   apply is_powerseries_invlin. now apply tl_roots_nz. now apply Hr.
Qed.

Lemma h_powerseries (x:C) :
 x<>tau q ->
 (forall r, In r (tl roots) -> Cmod (r*x) < 1) ->
 h q x = CPowerSeries (dh q) x.
Proof.
 intros. symmetry. now apply CPowerSeries_unique, h_is_powerseries.
Qed.

Lemma dg_eqn n :
 RtoC (dg q n) = delay (dh q) (S q) n - delay (dh q) q n - dh q n.
Proof.
 unfold delay, dg, zero. simpl.
 case Nat.eqb_spec; intros Hn.
 - subst. simpl. case Nat.ltb_spec; try lia.
   intros _. unfold dh. simpl. lca.
 - rewrite RtoC_minus, RtoC_mult.
   do 2 case Nat.ltb_spec; try lia.
   + intros Hn' _. unfold dh, df.
     case Nat.eqb_spec; try lia. intros _.
     do 2 case Nat.ltb_spec; try lia. intros _ _.
     replace (n-q)%nat with O by lia. simpl.
     rewrite RtoC_minus, RtoC_mult. ring.
   + intros Hn2 Hn3. replace n with q by lia. clear Hn Hn2 Hn3.
     replace (q-q)%nat with O by lia.
     unfold dh, df. simpl.
     case Nat.eqb_spec; try lia. intros _.
     do 2 case Nat.ltb_spec; try lia. intros _ _.
     replace (q-q)%nat with O by lia.
     replace (q-_)%nat with O by lia. simpl.
     rewrite RtoC_plus, RtoC_minus, RtoC_mult. ring.
   + intros _ Hn'. unfold dh, df.
     do 2 case Nat.ltb_spec; try lia. intros _ _.
     repeat case Nat.eqb_spec; try lia; intros.
     * replace (n-q-_-_)%nat with O by lia.
       repeat replace (n-q-_)%nat with O by lia.
       replace (n-2*q)%nat with O by lia.
       replace (n-q)%nat with (S O) by lia.
       replace (n-_-_-_)%nat with O by lia.
       replace (n-_-_)%nat with O by lia. simpl.
       rewrite !RtoC_minus, !RtoC_mult, !RtoC_plus. ring.
     * apply Ceq_minus.
       rewrite !plus_INR, !RtoC_minus, !RtoC_mult, !RtoC_plus.
       replace (n-2*q)%nat with (n-q-q)%nat by lia.
       replace (n-q-q-1)%nat with (n-1-2*q)%nat by lia. ring_simplify.
       replace (n-q-1)%nat with (S (n-1-q-1)) at 1 by lia.
       rewrite A_S, plus_INR, RtoC_plus.
       replace (n-S q-q-1)%nat with (n-1-q-1-q)%nat by lia.
       ring_simplify.
       replace (n-q)%nat with (S (n-q-1)) at 2 by lia.
       rewrite A_S, plus_INR, RtoC_plus.
       replace (n-q-1-q)%nat with (n-S q-q)%nat by lia.
       ring.
Qed.

Lemma ex_series_Rabs_dg :
  (forall r, In r (tl roots) -> Cmod r < 1) ->
  ex_series (Rabs ∘ dg q).
Proof.
 intros Hr.
 apply (ex_series_le (V:=R_CNM)) with
  (b:=(fun n =>
       delay (Rabs∘dh q) (S q) n + delay (Rabs∘dh q) q n + Rabs (dh q n))%R).
 { intros n.
   rewrite !(delay_comp Rabs) by apply Rabs_R0.
   unfold compose. change norm with Rabs.
   rewrite Rabs_pos_eq by apply Rabs_pos.
   rewrite <- Cmod_R, dg_eqn, <- !RtoC_minus, Cmod_R. unfold Rminus.
   eapply Rle_trans; [eapply Rabs_triang|rewrite Rabs_Ropp].
   apply Rplus_le_compat_r.
   eapply Rle_trans; [eapply Rabs_triang|rewrite Rabs_Ropp; lra]. }
 destruct (ex_series_Rabs_dh Hr) as (l & Hl).
 apply (ex_series_plus (V:=R_NM)); [apply (ex_series_plus (V:=R_NM))|];
  exists l; trivial; now apply delay_series_R.
Qed.

Lemma ex_pseries_Rabs_dg x :
  (forall r, In r (tl roots) -> Cmod r <= 1) -> Rabs x < 1 ->
  ex_series (fun n => Rabs (dg q n * x^n)).
Proof.
 intros Hr Hx.
 apply (ex_series_le (V:=R_CNM)) with
  (b:=(fun n =>
       (delay (Rabs∘dh q) (S q) n + delay (Rabs∘dh q) q n + Rabs (dh q n))
       *Rabs (x^n))%R).
 { intros n.
   rewrite !(delay_comp Rabs) by apply Rabs_R0.
   change norm with Rabs.
   rewrite Rabs_pos_eq by apply Rabs_pos.
   rewrite Rabs_mult. apply Rmult_le_compat_r; try apply Rabs_pos.
   rewrite <- Cmod_R, dg_eqn, <- !RtoC_minus, Cmod_R. unfold Rminus.
   eapply Rle_trans; [eapply Rabs_triang|rewrite Rabs_Ropp].
   apply Rplus_le_compat_r.
   eapply Rle_trans; [eapply Rabs_triang|rewrite Rabs_Ropp; lra]. }
 eapply ex_series_ext.
 { intros n. symmetry. rewrite 2 Rmult_plus_distr_r. rewrite <- Rabs_mult.
   rewrite <- RPow_abs. reflexivity. }
 destruct (ex_pseries_Rabs_dh x Hr Hx) as (l & Hl).
 apply (ex_series_plus (V:=R_NM)); [apply (ex_series_plus (V:=R_NM))|].
 - exists (Rabs x^S q * l)%R. apply delay_powerseries_R.
   eapply is_series_ext; eauto.
   { intros n. unfold compose. now rewrite Rabs_mult, RPow_abs. }
 - exists (Rabs x^q * l)%R. apply delay_powerseries_R.
   eapply is_series_ext; eauto.
   { intros n. unfold compose. now rewrite Rabs_mult, RPow_abs. }
 - exists l; trivial; now apply delay_series_R.
Qed.

Lemma g_is_powerseries (x:C) :
 x<>tau q ->
 (forall r, In r (tl roots) -> Cmod (r*x) < 1) ->
 is_CPowerSeries (dg q) x (g q x).
Proof.
 intros Hx Hr.
 unfold g, f. unfold Cdiv.
 rewrite Cmult_assoc, (Cmult_comm (1-_)), <- Cmult_assoc.
 change (_*/_) with (h q x).
 assert (H := h_is_powerseries x Hx Hr).
 assert (H1 := delay_powerseries q _ _ _ H).
 assert (H2 := delay_powerseries (S q) _ _ _ H).
 assert (H3 := is_lim_Cseq_minus _ _ _ _ H2 H1).
 assert (H4 := is_lim_Cseq_minus _ _ _ _ H3 H). clear H1 H2 H3.
 unfold Cminus. rewrite !Cmult_plus_distr_r.
 rewrite <- !Copp_mult_distr_l, Cmult_1_l.
 eapply is_lim_Cseq_ext; [|apply H4]. clear H H4.
 intros n. simpl. rewrite !sum_n_minus. apply sum_n_ext. clear n.
 intros n.
 unfold Cminus. rewrite !Copp_mult_distr_l, <- !Cmult_plus_distr_r. f_equal.
 symmetry. rewrite dg_eqn. now rewrite <- !(delay_comp RtoC).
Qed.

Lemma g_powerseries (x:C) :
 x<>tau q ->
 (forall r, In r (tl roots) -> Cmod (r*x) < 1) ->
 g q x = CPowerSeries (dg q) x.
Proof.
 intros. symmetry. now apply CPowerSeries_unique, g_is_powerseries.
Qed.

Lemma Hyp_alt :
 ThePoly_SndRootsLt1 q ->
 forall r, In r (tl roots) -> Cmod r < 1.
Proof.
 intros Hyp r R.
 assert (L := SortedRoots_length _ _ roots_ok).
 assert (ND := SortedRoots_nodup _ _ roots_ok).
 assert (M := SortedRoots_mu _ _ roots_ok).
 destruct roots as [|r0 l]; try easy. simpl in *.
 apply Hyp.
 - rewrite (proj1 roots_ok), <- linfactors_roots. now right.
 - inversion_clear ND. rewrite <- M. unfold Cnth. simpl. now intros ->.
Qed.

End PartialFraction.

(** Siegel's Lemma 1. Fortunately it is enough here to derive
    a contradiction when 5<=q, no need to formalize the rest of
    Siegel's article. *)

Lemma One q : q<>O -> ThePoly_SndRootsLt1 q ->
 CSeries (fun n => (dg q n)^2) = 1 + mu q^2.
Proof.
 intros Hq Hyp.
 destruct (SortedRoots_exists q) as (roots, roots_ok).
 assert (Hyp' := Hyp_alt _ _ roots_ok Hyp).
 rewrite <- (Mu_series_square (dg q) (g q)).
 { unfold Mu.
   assert (N : C2*PI <> 0).
   { intros E. rewrite <- RtoC_mult in E. apply RtoC_inj in E.
     generalize PI_RGT_0; lra. }
   apply Cmult_eq_reg_l with (C2*PI); trivial.
   rewrite Cmult_assoc, Cinv_r, Cmult_1_l; trivial.
   apply is_CInt_unique.
   apply (is_RInt_ext (V:=C_NM))
    with (f := fun t => 1 + mu q^2 - mu q * (Cexp t - -Cexp (-t))).
   { intros t _.
     transitivity ((1 - mu q * Cexp t)*(1 - mu q * Cexp (-t))).
     { rewrite Cexp_neg. fixeq C. field. apply Cexp_nonzero. }
     unfold g. rewrite <- !Cmult_assoc. f_equal.
     rewrite (Cmult_comm (1-_)), Cmult_assoc.
     rewrite Cexp_neg at 2. rewrite ff; try apply Cexp_nonzero; try ring.
     - intros H. apply Hyp in H. rewrite Cmod_Cexp in H.
       assert (N' : Cexp t <> mu q).
       { intros E. apply (f_equal Cmod) in E.
         assert (T := mu_itvl q).
         rewrite Cmod_Cexp, Cmod_R, Rabs_right in E; lra. }
       specialize (H N'). lra.
     - rewrite RevRoot_carac, <- Cexp_neg.
       intros H. apply Hyp in H. rewrite Cmod_Cexp in H.
       assert (N' : Cexp (-t) <>  mu q).
       { intros E. apply (f_equal Cmod) in E.
         assert (T := mu_itvl q).
         rewrite Cmod_Cexp, Cmod_R, Rabs_right in E; lra. }
       specialize (H N'). lra. }
   replace (C2*_*_) with (C2*PI*(1+mu q^2) - 0) by ring.
   apply (is_RInt_minus (V:=C_NM)).
   - rewrite <- RtoC_mult.
     replace (RtoC (2*PI)) with (RtoC (2*PI)-0) by ring.
     apply is_CInt_const.
   - replace 0 with ((mu q)*(0-0)) at 1 by ring.
     apply is_CInt_scal, (is_RInt_minus (V:=C_NM)).
     + generalize (is_CInt_Cexp 1 lia). apply is_RInt_ext.
       intros x _. f_equal. now rewrite Rmult_1_l.
     + apply (is_RInt_comp_opp (V:=C_NM)).
       rewrite Ropp_0, Ropp_mult_distr_l.
       generalize (is_CInt_Cexp' 1 lia). apply is_RInt_ext.
       intros x _. f_equal. now rewrite Rmult_1_l. }
 { apply ex_series_ext with (a:=Rabs∘dg q).
   - intros n. symmetry. apply Cmod_R.
   - now apply (ex_series_Rabs_dg q Hq roots roots_ok). }
 { intros z Hz. apply (g_powerseries q Hq roots roots_ok).
   - intros ->.
     rewrite Cmod_R, Rabs_right in Hz; generalize (tau_itvl q); lra.
   - intros r R. rewrite Cmod_mult, Hz, Rmult_1_r. now apply Hyp'. }
Qed.

(* Print Assumptions One. *)

Section RStuff.
Local Open Scope R.

Lemma One' q : q<>O -> ThePoly_SndRootsLt1 q ->
 Series (fun n => (dg q n)^2) = 1 + mu q^2.
Proof.
 intros Hq Hyp.
 apply is_series_unique.
 rewrite <- (re_RtoC (1+mu q^2)).
 apply CSeries_RtoC_impl.
 unfold compose. rewrite RtoC_plus, <- RtoC_pow.
 rewrite <- One by trivial.
 apply is_lim_Cseq_ext with (sum_n (fun k => dg q k^2))%C.
 - intros n. apply sum_n_ext. intros m. now rewrite <- RtoC_pow.
 - apply CSeries_correct.
   destruct (ex_series_square (dg q)) as (l & Hl).
   destruct (SortedRoots_exists q) as (roots, roots_ok).
   eapply ex_series_Rabs_dg; eauto using Hyp_alt.
   exists (RtoC l).
   apply CSeries_RtoC in Hl.
   revert Hl. apply is_lim_Cseq_ext. intros n. apply sum_n_ext.
   intros m. unfold compose. now rewrite RtoC_pow.
Qed.

Lemma One_le q : q<>O -> ThePoly_SndRootsLt1 q ->
  forall n, sum_n (fun n => (dg q n)^2) n <= 1 + mu q^2.
Proof.
 intros Hq Hyp.
 apply pos_series_pos_sum.
 2:{ intros n. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
 rewrite <- One' by trivial.
 apply Series_correct.
 apply (ex_series_square (dg q)).
 destruct (SortedRoots_exists q) as (roots, roots_ok).
 eapply ex_series_Rabs_dg; eauto using Hyp_alt.
Qed.

Definition coef0 q : R := (q+1)*(q+2)*(2*q+3)/6 + q+2.
Definition coef1 q : R := -2*(q*(q+1)*(q+2)/3 + q+3).
Definition coef2 q : R := q*(q+1)*(2*q+1)/6 + q+2.

Lemma One_aux_eqn q m : (2<=q)%nat ->
 sum_n (fun n => (if n=?0 then 1 else df q n - m * df q (n-1))^ 2) (2 * q)
 - 1 - m^2
 = coef2 q * m^2 + coef1 q * m + coef0 q.
Proof.
 intros Hq.
 unfold sum_n.
 rewrite sum_n_m_Chasles with (m:=O); try lia.
 rewrite sum_n_n. change plus with Rplus.
 change (if 0=?0 then _ else _) with 1.
 replace (1^2) with 1 by lra.
 apply Rplus_eq_reg_l with (m^2). ring_simplify.
 rewrite sum_n_m_ext_loc with
  (b:=fun n => m^2 * (df q (n-1))^2 + (-2 * m)*(df q n * df q (n-1)) + df q n^2).
 2:{ intros k Hk. case Nat.eqb_spec; try lia. intros _. fixeq R. ring. }
 repeat rewrite (sum_n_m_plus (G:=R_AbelianMonoid)). change plus with Rplus.
 f_equal;[f_equal|].
 { rewrite (sum_n_m_mult_l (K:=R_Ring)). change mult with Rmult.
   rewrite <- (Rmult_1_r (m^2)) at 3. rewrite <- Rmult_plus_distr_l.
   f_equal.
   rewrite sum_n_m_Chasles with (m:=S q); try lia. change plus with Rplus.
   rewrite sum_n_Sm by lia.
   rewrite sum_n_m_ext_loc with (b:=fun _ => 1).
   2:{ intros k K. rewrite df_1. simpl; lra. lia. }
   rewrite sum_n_m_const.
   replace (S q - 1)%nat with q by lia. rewrite Rmult_1_r.
   rewrite df_2 by lia. simpl INR.
   replace ((1+1)^2) with 4 by lra.
   rewrite sum_n_m_ext_loc with (b:=fun k =>(k-q)%nat^2).
   2:{ intros k K. rewrite df_lin, minus_INR by lia.
       f_equal. rewrite minus_INR by lia. f_equal. f_equal. lia. }
   rewrite (sum_n_m_shift (G:=R_AbelianMonoid)) with (a:=fun k=>k^2) by lia.
   replace (S (S q)-q)%nat with 2%nat by lia.
   replace (2*q-q)%nat with q by lia.
   rewrite (sum_n_m_sum_n (G:=R_AbelianGroup)) by lia.
   change minus with Rminus. rewrite sum_square.
   rewrite sum_Sn, sum_O. simpl. change plus with Rplus. unfold coef2.
   field. }
 { rewrite (sum_n_m_mult_l (K:=R_Ring)). change mult with Rmult.
   unfold coef1. rewrite (Rmult_comm _ m), Rmult_assoc.
   f_equal. f_equal.
   rewrite sum_n_m_Chasles with (m:=S q); try lia. change plus with Rplus.
   rewrite sum_n_Sm by lia.
   replace q with (S (q-1)) at 1 by lia. rewrite sum_n_Sm by lia.
   rewrite sum_n_m_ext_loc with (b:=fun _ => 1).
   2:{ intros k K. rewrite !df_1. simpl; lra. lia. lia. }
   rewrite sum_n_m_const.
   replace (S (q-1) - 1)%nat with (q-1)%nat by lia. rewrite Rmult_1_r.
   rewrite df_2 by lia. simpl INR.
   rewrite df_1 by lia. simpl INR.
   rewrite df_2 by lia. simpl INR.
   rewrite df_2 by lia. simpl INR.
   replace (1+1) with 2 by lra. change plus with Rplus.
   rewrite minus_INR by lia. simpl INR.
   rewrite sum_n_m_ext_loc with (b:=fun k =>(k-q)%nat^2+(k-q)%nat).
   2:{ intros k K. rewrite !df_lin by lia.
       replace (S (k-1) - q)%nat with (k-q)%nat by lia.
       replace (S k-q)%nat with (S (k-q))%nat by lia. rewrite S_INR. lra. }
   rewrite (sum_n_m_shift (G:=R_AbelianMonoid)) with (a:=fun k=>k^2+k) by lia.
   rewrite (sum_n_m_plus (G:=R_AbelianMonoid)). change plus with Rplus.
   replace (S (S q)-q)%nat with 2%nat by lia.
   replace (2*q-q)%nat with q by lia.
   repeat rewrite (sum_n_m_sum_n (G:=R_AbelianGroup)) by lia.
   change minus with Rminus. rewrite sum_square, sum_INR.
   rewrite !sum_Sn, !sum_O. simpl. change plus with Rplus.
   field. }
 { unfold coef2.
   rewrite sum_n_m_Chasles with (m:=q); try lia. change plus with Rplus.
   replace q with (S (q-1)) at 1 by lia. rewrite sum_n_Sm by lia.
   rewrite sum_n_m_ext_loc with (b:=fun _ => 1).
   2:{ intros k K. rewrite df_1. simpl; lra. lia. }
   rewrite sum_n_m_const.
   replace (S (q-1)) with q by lia. change plus with Rplus.
   rewrite Rmult_1_r. rewrite minus_INR by lia. simpl INR.
   rewrite df_2; try lia. rewrite (INR_IZR_INZ 2). simpl IZR.
   replace (2^2) with 4 by lra.
   rewrite sum_n_m_ext_loc with (b:=fun k =>(k-(q-1))%nat^2).
   2:{ intros k K. rewrite df_lin, minus_INR; try lia. f_equal.
       rewrite !minus_INR; try lia. rewrite S_INR. simpl. lra. }
   rewrite (sum_n_m_shift (G:=R_AbelianMonoid)) with (a:=fun k=>k^2).
   2:lia.
   replace (S q - (q-1))%nat with 2%nat by lia.
   replace (2*q - (q-1))%nat with (S q)%nat by lia.
   rewrite (sum_n_m_sum_n (G:=R_AbelianGroup)) by lia.
   change minus with Rminus. rewrite sum_square, S_INR.
   rewrite sum_Sn, sum_O. simpl. change plus with Rplus. unfold coef0.
   field. }
Qed.

Lemma LargeSndRoot_after_5 q : (5<=q)%nat -> ThePoly_ExSndRootGe1 q.
Proof.
 intros Hq.
 rewrite ThePoly_SndRoots_neg. intros Hyp.
 apply Nat.le_lteq in Hq. apply or_comm in Hq. destruct Hq as [<-|Hq].
 - assert (H := One_le 5 lia Hyp 12).
   apply Rle_minus in H.
   apply Rle_not_gt in H. apply H. clear H.
   unfold sum_n, sum_n_m, Iter.iter_nat. cbn -[pow]. ring_simplify.
   unfold Rminus. rewrite Ropp_mult_distr_l.
   apply Rlt_gt.
   apply discriminant_neg; lra.
 - red in Hq.
   assert (H := One_le q lia Hyp (2*q)).
   assert (H' : 0 < coef2 q * mu q^2 + coef1 q * mu q + coef0 q).
   { apply le_INR in Hq. rewrite (INR_IZR_INZ 6) in Hq. simpl in Hq.
     apply discriminant_neg.
     - unfold coef2. nra.
     - apply Rminus_gt_0_lt. unfold coef0, coef1, coef2.
       field_simplify. nra. }
   rewrite <- (One_aux_eqn q (mu q)) in H' by lia. unfold dg in H. lra.
Qed.

End RStuff.

(* Print Assumptions LargeSndRoot_after_5. *)

(* ThePoly can be factorized in Z when q = 4 mod 6,
   one factor being (X^2-X+1)=(X-Cexp(PI/3))(X-Cexp(-PI/3)), ie
   roots of modulus 1, while the minimal polynomial of mu is the other
   factor, with secondary secondary roots of modulus >1 only when q<>4.
   For instance (ThePoly 4) = X^5-X^4-1 = (X^2-X+1)(X^3-X-1).
   Note that for q = 4 mod 6, RevPoly is also divided by (X^2-X+1).
   For instance (RevPoly 4) = X^5+X-1 = (X^2-X+1)(X^3+X^2-1).
   When considering f:=ThePoly/RevPoly, for q = 4 mod 6 we
   we can factor away the apparent poles (Cexp (+/-PI/3)) of f,
   and f is continuously prolongeable on the unit circle.
*)

Lemma ThePoly_root_mod1_carac q z :
  Root z (ThePoly q) -> Cmod z = 1%R -> z^2 = z-1.
Proof.
 intros Hz Hz'.
 rewrite ThePoly_root_carac in Hz.
 assert  (E : Cmod (z^S q - z^q) = 1%R).
 { rewrite Hz. replace (_+1-_) with 1 by ring. now rewrite Cmod_1. }
 rewrite Cpow_S in E.
 replace (z*z^q - z^q) with (z^q*(z-1)) in E by ring.
 rewrite Cmod_mult, Cmod_pow in E. rewrite Hz', pow1, Rmult_1_l in E.
 assert (E' : (Cmod (z-1)^2 = 1)%R) by (rewrite E; ring).
 assert (Hz2 : (Cmod z^2 = 1)%R) by (rewrite Hz'; ring).
 rewrite Cmod2_alt in E', Hz2.
 destruct z as (x,y); simpl Im in *; simpl Re in *.
 rewrite Ropp_0, Rplus_0_r in E'.
 simpl in E'. ring_simplify in E'.
 assert (Hx : (x = 1/2)%R) by nra.
 assert (Hy : (y^2 = 3/4)%R) by nra.
 simpl. unfold Cmult; simpl.
 replace ((x,y)-1) with (x-1,y)%R by lca. f_equal; nra.
Qed.

Lemma CexpPI3_carac z :
  z^2 = z-1 <-> z = Cexp (PI/3) \/ z = Cexp (-PI/3).
Proof.
 assert (E : z^2-z+1 = (z-Cexp(PI/3))*(z-Cexp(-PI/3))).
 { symmetry. apply Cminus_eq_0. ring_simplify.
   rewrite <- Cexp_add. replace (PI / 3 + - PI / 3)%R with 0%R by lra.
   rewrite Cexp_0. ring_simplify.
   rewrite <- Cmult_plus_distr_l.
   rewrite Ropp_div, <- Cexp_conj_neg, re_alt'. simpl. rewrite cos_PI3.
   lca. }
 split.
 - intros Hz. apply Cminus_diag in Hz.
   replace (z^2-(z-1)) with (z^2-z+1) in Hz by ring. rewrite E in Hz.
   apply Cmult_integral in Hz.
   destruct Hz as [Hz|Hz]; [left|right]; now apply Cminus_eq_0.
 - intros [Hz|Hz]; apply Cminus_eq_0.
   + replace (z^2-(z-1)) with (z^2-z+1) by ring. rewrite E, <- Hz. ring.
   + replace (z^2-(z-1)) with (z^2-z+1) by ring. rewrite E, <- Hz. ring.
Qed.

Lemma CexpPI3_root_carac q :
  Root (Cexp (PI/3)) (ThePoly q) <-> (q mod 6 = 4)%nat.
Proof.
 rewrite ThePoly_root_carac, Ceq_minus.
 replace (Cexp (PI / 3) ^ S q - (Cexp (PI / 3) ^ q + 1)) with
   (Cexp (PI/3) ^ q * (Cexp (PI/3) - 1) - 1) by (rewrite Cpow_S; ring).
 rewrite <- Ceq_minus.
 rewrite Cexp_pow, Rmult_comm.
 replace (Cexp (PI/3) - 1) with (Cexp (2*(PI/3))).
 2:{ unfold Cexp. rewrite cos_PI3, cos_2PI3, sin_PI3, sin_2PI3.
     unfold Cminus, Cplus. simpl. f_equal; lra. }
 rewrite <- Cexp_add , <- Rmult_plus_distr_r.
 change 2 with (INR 2). rewrite <- plus_INR.
 rewrite (Nat.div_mod_eq (q+2) 6).
 set (q' := ((q+2)/6)%nat).
 set (r := ((q+2) mod 6)%nat). rewrite plus_INR, mult_INR.
 rewrite Rmult_plus_distr_r, Cexp_add, INR_IZR_INZ. simpl IZR.
 replace (6 * _ * _)%R with (IZR (2*Z.of_nat q') * PI)%R.
 2:{ rewrite mult_IZR, <-INR_IZR_INZ. field. }
 rewrite Cexp_2nPI, Cmult_1_l.
 split.
 - destruct (Nat.lt_ge_cases r 3) as [Hr|Hr].
   + destruct r as [|[|[|[|] ] ] ] eqn:E; try lia; clear Hr;
     rewrite INR_IZR_INZ; simpl IZR.
     * intros _.
       assert (E' := Nat.div_mod_eq (q+2) 6). fold q' in E'.
       fold r in E'. rewrite E, Nat.add_0_r in E'.
       destruct q' as [|q']. lia. replace q with (4+q'*6)%nat by lia.
       now rewrite Nat.mod_add by lia.
     * rewrite Rmult_1_l. intros [= H _]. rewrite cos_PI3 in H. lra.
     * intros [= H _]. rewrite cos_2PI3 in H. lra.
   + replace (r * (PI/3))%R with (PI + (r-3)*(PI/3))%R by field.
     rewrite Cexp_add, Cexp_PI.
     replace 3 with (INR 3) at 1 by now rewrite INR_IZR_INZ.
     rewrite <- minus_INR by lia.
     assert (Hr' : (r-3 < 3)%nat)
       by (generalize (Nat.mod_upper_bound (q+2) 6); lia).
     destruct (r-3)%nat as [|[|[|[|] ] ] ]; try lia; clear Hr Hr';
     rewrite INR_IZR_INZ; simpl IZR.
     * rewrite Rmult_0_l, Cexp_0. intros [= H]. lra.
     * rewrite Rmult_1_l. intros [= H _]. rewrite cos_PI3 in H. lra.
     * intros [= H _]. rewrite cos_2PI3 in H. lra.
 - intros Hq. unfold r. rewrite <- Nat.add_mod_idemp_l, Hq by lia.
   simpl. now rewrite Rmult_0_l, Cexp_0.
Qed.

(** Now, let us prove that ThePoly have a secondary root
    of modulus > 1 when 5<=q.
    NB: actually, q=4 is the only situation where (mu q) is Pisot
    while ThePoly has secondary roots of modulus >= 1.
*)

Definition ThePoly_SndRootsLe1 q :=
  forall x, Root x (ThePoly q) -> x <> mu q -> Cmod x <= 1.

Definition ThePoly_ExSndRootGt1 q :=
  exists x, Root x (ThePoly q) /\ x <> mu q /\ 1 < Cmod x.

Lemma ThePoly_SndRoots_neg' q :
  ThePoly_ExSndRootGt1 q <-> ~ThePoly_SndRootsLe1 q.
Proof.
 split.
 - intros (x & Hx & N & LE) H. specialize (H x Hx N). lra.
 - unfold ThePoly_ExSndRootGt1, ThePoly_SndRootsLe1. intros H.
   destruct (SortedRoots_exists q) as (l & Hl).
   assert (H1 := SortedRoots_length q l Hl).
   assert (H2 := SortedRoots_roots q l Hl).
   assert (H3 := SortedRoots_mu q l Hl).
   destruct q as [ | q].
   + destruct H. intros r. rewrite <- H2. destruct l as [|r' [|] ]; try easy.
     unfold Cnth in H3. simpl in *. subst r'. intuition.
   + assert (l @ 1 <> mu (S q)).
     { rewrite <- H3. intro E.
       destruct Hl as (_,Hl). apply Csorted_alt in Hl.
       rewrite StronglySorted_nth in Hl. specialize (Hl 0%nat 1%nat lia).
       rewrite E in Hl. revert Hl. apply Cgt_order. }
     exists (l @ 1); repeat split; trivial.
     * rewrite <- H2. apply nth_In; lia.
     * apply Rnot_le_lt. intros H4. apply H.
       intros r Hr Hr'. rewrite <- H2 in Hr.
       eapply Rle_trans; [ | apply H4 ].
       apply SortedRoots_Cmod_sorted in Hl.
       rewrite StronglySorted_nth in Hl.
       destruct (In_nth l r 0 Hr) as (i & Hi & <-).
       change (nth i l 0) with (l @ i) in *.
       destruct i as [|[|i] ]; try lra. intuition.
       apply Rge_le, Hl. lia.
Qed.

(** First, when there is no root of modulus 1 at all, we're easily done *)

Lemma LargerSndRoot_after_5_easy q :
  (5<=q)%nat -> (q mod 6 <> 4)%nat -> ThePoly_ExSndRootGt1 q.
Proof.
 intros Hq Hq'.
 destruct (LargeSndRoot_after_5 q Hq) as (r & R & N & Ge).
 exists r; repeat split; trivial. destruct Ge as [Gt|E]; trivial. exfalso.
 symmetry in E. assert (E' := ThePoly_root_mod1_carac q r R E).
 apply CexpPI3_carac in E'. destruct E' as [-> | ->].
 - apply CexpPI3_root_carac in R; lia.
 - replace (-PI/3)%R with (-(PI/3))%R in R by field.
   rewrite <- Cexp_conj_neg in R. apply root_conj in R.
   rewrite Cconj_involutive in R.
   apply CexpPI3_root_carac in R; lia.
Qed.

(** Now, we focus on the situation with roots of modulus 1 *)

Section HandlingModulusOne.
Variable q : nat.
Hypothesis Hq : (5<=q)%nat.
Hypothesis Hq' : (q mod 6 = 4)%nat.
Hypothesis Hyp : ThePoly_SndRootsLe1 q.
(* And from Hyp we prove False now *)
Variable roots : list C.
Hypothesis roots_ok : SortedRoots q roots.

Lemma roots_0 : roots@0 = mu q.
Proof.
 apply (SortedRoots_mu q roots roots_ok).
Qed.

Lemma Hyp_alt' :
 forall r, In r (tl roots) -> Cmod r <= 1.
Proof.
 intros r R.
 assert (L := SortedRoots_length _ _ roots_ok).
 assert (ND := SortedRoots_nodup _ _ roots_ok).
 apply Hyp.
 - rewrite <-(SortedRoots_roots _ _ roots_ok).
   destruct roots. apply R. now right.
 - rewrite <- roots_0. destruct roots; simpl in *; try easy.
   unfold Cnth. simpl. inversion_clear ND. contradict H. now subst.
Qed.

Lemma roots_layout :
  roots@1 = Cexp (PI/3) /\
  roots@2 = Cexp (-PI/3) /\
  forall i, (3<=i<=q)%nat -> Cmod (roots@i) < 1.
Proof.
  destruct (SortedRoots_im_pos q roots roots_ok 0 lia) as (Im1 & Im2).
  simpl in Im1,Im2.
  destruct (second_best_root q roots lia roots_ok) as (_ & LT & H).
  assert (IN : In (Cexp (PI/3)) roots).
  { now apply (SortedRoots_roots q roots roots_ok), CexpPI3_root_carac. }
  apply In_nth with (d:=0) in IN. destruct IN as (n & N & E).
  change (roots@n = Cexp (PI/3)) in E.
  destruct (Nat.eq_dec n 0) as [->|N0].
  { exfalso. rewrite roots_0 in E. apply (f_equal Cmod) in E.
    rewrite Cmod_Cexp in E.
    assert (T := mu_itvl q). rewrite Cmod_R, Rabs_right in E; lra. }
  destruct (Nat.eq_dec n 2) as [->|N2].
  { exfalso. rewrite E in Im2.
    rewrite <- (Cconj_involutive (Cexp (PI/3))) in Im2.
    apply Cconj_simplify in Im2. rewrite <- Im2 in Im1.
    simpl in Im1. rewrite sin_PI3 in Im1. generalize Rlt_sqrt3_0; lra. }
  destruct (Nat.le_gt_cases 3 n).
  { exfalso.
    assert (L := SortedRoots_length _ _ roots_ok).
    specialize (H n lia). rewrite E, Cmod_Cexp in H.
    assert (Cmod (roots @ 1) <= 1); try lra.
    { apply Hyp. apply (SortedRoots_roots _ _ roots_ok). apply nth_In; lia.
      rewrite <- roots_0.
      destruct roots_ok as (_,R). apply Csorted_alt in R.
      rewrite StronglySorted_nth in R. specialize (R 0%nat 1%nat lia).
      intros E'. rewrite E' in R. revert R. apply Cgt_order. }}
  replace n with 1%nat in * by lia. repeat split; trivial.
  - rewrite Im2, E, Cexp_conj_neg. f_equal. field.
  - intros i Hi. specialize (H i Hi). rewrite E, Cmod_Cexp in LT. lra.
Qed.

Lemma roots_1 : roots@1 = Cexp (PI/3).
Proof.
 apply roots_layout.
Qed.

Lemma roots_2 : roots@2 = Cexp (-PI/3).
Proof.
 apply roots_layout.
Qed.

Lemma roots_other i : (i<=q)%nat -> (3<=i)%nat <-> Cmod (roots@i) < 1.
Proof.
 intros Hi. split.
 - intros Hi'. apply roots_layout; lia.
 - intros H.
   destruct (Nat.eq_dec i 0) as [->|N0].
   { rewrite roots_0 in H.
     assert (T := mu_itvl q). rewrite Cmod_R, Rabs_right in H; lra. }
   destruct (Nat.eq_dec i 1) as [->|N1].
   { rewrite roots_1, Cmod_Cexp in H. lra. }
   destruct (Nat.eq_dec i 2) as [->|N2].
   { rewrite roots_2, Cmod_Cexp in H. lra. }
   lia.
Qed.

Lemma skipn_3_roots_spec r :
 In r (skipn 3 roots) <-> In r roots /\ Cmod r < 1.
Proof.
 assert (L := SortedRoots_length _ _ roots_ok).
 split.
 - intros IN. apply In_nth with (d:=0) in IN.
   destruct IN as (n & N & <-).
   rewrite skipn_length, L in N.
   rewrite nth_skipn. split.
   + apply nth_In; lia.
   + apply roots_other; lia.
 - intros (IN,LT). apply In_nth with (d:=0) in IN.
   destruct IN as (n & N & <-).
   apply roots_other in LT; try lia.
   replace n with (3+(n-3))%nat by lia. rewrite <- nth_skipn.
   apply nth_In. rewrite skipn_length. lia.
Qed.

Definition rootrest := roots@0 :: skipn 3 roots.

Lemma rootrest_spec r : In r rootrest <-> In r roots /\ Cmod r <> 1%R.
Proof.
 assert (L := SortedRoots_length _ _ roots_ok).
 change (In r rootrest) with (roots @ 0 = r \/ In r (skipn 3 roots)).
 rewrite skipn_3_roots_spec. split.
 - intros [<- | (IN,LT)].
   + split. apply nth_In; lia. rewrite roots_0.
     assert (T := mu_itvl q). rewrite Cmod_R, Rabs_right; lra.
   + split; trivial; lra.
 - intros (IN,NE). destruct (Rle_lt_dec (Cmod r) 1%R).
   + right; split; trivial; lra.
   + left. rewrite roots_0.
     destruct (Ceq_dec r (mu q)) as [E|N]; try easy.
     rewrite (SortedRoots_roots _ _ roots_ok) in IN.
     specialize (Hyp r IN N). lra.
Qed.

Lemma rootrest_perm : Permutation roots (Cexp (PI/3)::Cexp(-PI/3)::rootrest).
Proof.
 assert (L := SortedRoots_length _ _ roots_ok).
 unfold rootrest. rewrite <- roots_1, <- roots_2.
 destruct roots as [|a [|b [|c l] ] ]; unfold Cnth; simpl in *; try lia.
 eapply perm_trans. apply perm_swap. apply perm_skip. apply perm_swap.
Qed.

Definition revfactors l := linfactors (map Cinv l).

Definition TheRest := linfactors rootrest.
Definition RevRest := revfactors rootrest.

Definition fbis x := Peval TheRest x / Peval RevRest x.
Definition gbis x :=
 (-mu q) * Peval TheRest x / Peval (revfactors (tl rootrest)) x.

Lemma RevRest_alt x :
  Peval RevRest x = (x - tau q) * Peval (revfactors (tl rootrest)) x.
Proof.
 unfold RevRest, revfactors, rootrest.
 set (l := skipn 3 roots).
 simpl. rewrite Pmult_eval, cons_eval, Pconst_eval.
 rewrite roots_0. unfold tau. rewrite RtoC_inv. ring.
Qed.

Lemma gbis_alt (x:C) : x<>tau q -> gbis x = (1 - mu q * x) * fbis x.
Proof.
 intros Hx. unfold gbis, fbis, Cdiv.
 rewrite RevRest_alt, Cinv_mult. unfold tau in *. rewrite RtoC_inv in *.
 rewrite !Cmult_assoc. f_equal.
 rewrite <- !Cmult_assoc, (Cmult_comm (Peval _ _)), !Cmult_assoc. f_equal.
 field. simpl. split.
 - intros [=E]. generalize (mu_itvl q); lra.
 - rewrite <- Ceq_minus. contradict Hx. now apply Cinv_eq.
Qed.

Lemma fbis_f x :
 x <> Cexp (PI/3) /\ x <> Cexp (-PI/3) -> fbis x = f q x.
Proof.
 intros H.
 unfold fbis, f, TheRest, RevRest. rewrite <- ThePoly_eval, <- RevPoly_eval.
 rewrite (proj1 roots_ok).
 rewrite (RevPoly_alt q lia roots roots_ok).
 rewrite (linfactors_perm _ _ rootrest_perm).
 rewrite (linfactors_perm _ _ (Permutation_map Cinv rootrest_perm)).
 cbn -[rootrest linfactors]. rewrite <- !Cexp_neg.
 replace (- (PI/3))%R with (-PI/3)%R by field.
 replace (- (-PI/3))%R with (PI/3)%R by field.
 remember rootrest as l.
 set (r1 := Cexp (PI/3)) in *.
 set (r2 := Cexp (-PI/3)) in *.
 simpl. unfold Cdiv. rewrite !Pmult_eval, !Cinv_mult.
 rewrite !cons_eval. change (Peval [] x) with 0.
 rewrite !Cmult_0_r, !Cplus_0_r, !Cmult_1_r.
 rewrite <- !Cmult_assoc. rewrite (Cmult_comm (/ (Peval _ _))).
 rewrite !Cmult_assoc. f_equal.
 rewrite <- (Cmult_1_r (Peval (linfactors l) x)) at 1.
 rewrite <- !Cmult_assoc. f_equal. field. split.
 - rewrite Cplus_comm. change (x-r2<>0). now rewrite <- Ceq_minus.
 - rewrite Cplus_comm. change (x-r1<>0). now rewrite <- Ceq_minus.
Qed.

Lemma gbis_g (x:C) :
 x <> tau q /\ x <> Cexp (PI/3) /\ x <> Cexp (-PI/3) -> gbis x = g q x.
Proof.
 intros (Hx,Hx'). rewrite gbis_alt; trivial.
 unfold g. now rewrite fbis_f.
Qed.

Lemma Reciprocal_gen l x :
  ~In 0 l -> x<>0 ->
  Peval (revfactors l) (/x) =
  Peval (revfactors l) 0 * Peval (linfactors l) x / x^length l.
Proof.
 unfold revfactors.
 induction l; intros Hl Hx.
 - simpl. rewrite !Pconst_eval. lca.
 - simpl. rewrite !Pmult_eval, IHl; trivial.
   2:{ contradict Hl. now right. }
   unfold Cdiv. rewrite !Cinv_mult.
   rewrite <- !Cmult_assoc. f_equal.
   rewrite (Cmult_comm (Peval _ 0)).
   rewrite <- !Cmult_assoc. f_equal.
   rewrite !(Cmult_comm (/ x^length l)).
   rewrite !Cmult_assoc. f_equal.
   rewrite !cons_eval. change (Peval [] _) with 0.
   field. split; trivial. contradict Hl. now left.
Qed.

Lemma RevRest_carac x :
  x <> 0 -> Peval RevRest (/x) = - Peval TheRest x / x^(q-1).
Proof.
 intros Hx.
 unfold RevRest, TheRest.
 rewrite (Reciprocal_gen rootrest x); trivial.
 2:{ rewrite rootrest_spec. intros (IN, _).
     apply (SortedRoots_roots _ _ roots_ok) in IN.
     now apply root_nz in IN. }
 f_equal.
 2:{ f_equal. unfold rootrest.
     change (length _) with (S (length (skipn 3 roots))).
     rewrite skipn_length.
     rewrite (SortedRoots_length _ _ roots_ok). lia. }
 replace (- _) with (-1 * Peval (linfactors rootrest) x) by lca.
 f_equal.
 replace (RtoC (-1)) with (Peval (RevPoly q) 0).
 2:{ rewrite RevPoly_eval. simpl. lca. }
 rewrite (RevPoly_alt q lia roots roots_ok).
 rewrite (linfactors_perm _ _ (Permutation_map Cinv rootrest_perm)).
 cbn -[rootrest linfactors]. rewrite <- !Cexp_neg.
 remember rootrest as l. unfold revfactors.
 simpl. rewrite !Pmult_eval.
 rewrite !cons_eval. change (Peval [] _) with 0. ring_simplify.
 rewrite <- Cmult_assoc, <- Cexp_add.
 replace (Rplus _ _) with R0 by lra.
 change R0 with 0%R. rewrite Cexp_0. lca.
Qed.

Lemma ffbis x : x <> 0 ->
  ~ Root x TheRest -> ~ Root (/x) TheRest -> fbis x * fbis (/ x) = 1.
Proof.
 intros X0 X1 X2. unfold fbis.
 rewrite RevRest_carac; trivial.
 rewrite <- (Cinv_inv x) at 2.
 rewrite RevRest_carac, Cpow_inv by now apply nonzero_div_nonzero.
 field. repeat split; trivial. now apply Cpow_nonzero.
Qed.

Lemma ggbis x : Cmod x = 1%R ->
  gbis x * gbis (/ x) = (1-mu q * x)*(1-mu q * /x).
Proof.
 intros X. rewrite !gbis_alt.
 2:{ intros E. apply (f_equal Cmod) in E.
     assert (T := tau_itvl q).
     rewrite Cmod_inv, X, Rinv_1, Cmod_R, Rabs_pos_eq in E; lra. }
 2:{ intros E. apply (f_equal Cmod) in E.
     assert (T := tau_itvl q).
     rewrite Cmod_R, Rabs_pos_eq in E; lra. }
 rewrite (Cmult_comm _ (fbis (/x))).
 rewrite Cmult_assoc, <- (Cmult_assoc _ (fbis x)), ffbis. ring.
 - intros ->. rewrite Cmod_0 in X. lra.
 - unfold TheRest. rewrite <- linfactors_roots, rootrest_spec. lra.
 - unfold TheRest. rewrite <- linfactors_roots, rootrest_spec.
   apply (f_equal Rinv) in X. rewrite Rinv_1 in X.
   rewrite Cmod_inv. lra.
Qed.


Definition pseries_multfactor c (a:nat->C) :=
 fun n => if n =? 0 then -c * a O else a (n-1)%nat - c * a n.

Lemma is_CPowerSeries_multfactor (c:C) (a:nat->C) x l :
  is_CPowerSeries a x l ->
  is_CPowerSeries (pseries_multfactor c a) x ((x-c)*l).
Proof.
 intros H.
 unfold pseries_multfactor.
 apply is_lim_Cseq_ext with
  (f:=fun n => sum_n (fun k => (delay a 1 k) * x^k) n -
               c * sum_n (fun k => a k * x^k) n).
 { intros n. rewrite <- sum_n_Cmult_l, sum_n_minus. apply sum_n_ext.
   clear n. intros n. unfold delay.
   case Nat.eqb_spec; case Nat.ltb_spec; try lia.
   - intros _ ->. simpl. change zero with C0. lca.
   - intros _ N. fixeq C. ring. }
 replace ((x-c)*l) with (x^1*l-c*l) by ring.
 apply is_lim_Cseq_minus.
 - now apply delay_powerseries.
 - apply is_lim_Cseq_mult; trivial. apply is_lim_Cseq_const.
Qed.

Definition pseries_linfactors := fold_right pseries_multfactor.

Lemma ex_series_multfactor c a :
  ex_series (Cmod ∘ a) -> ex_series (Cmod ∘ (pseries_multfactor c a)).
Proof.
 intros (l,H).
 unfold pseries_multfactor, compose.
 apply (ex_series_le (V:=R_CNM))
   with (fun n => delay (Cmod∘a) 1 n + (Cmod∘a) n * Cmod c)%R.
 { intros n. change norm with Rabs.
   rewrite Rabs_pos_eq by apply Cmod_ge_0.
   unfold delay. case Nat.eqb_spec; case Nat.ltb_spec; try lia; intros.
   - subst. unfold compose. change zero with 0%R.
     rewrite Cmod_mult, Cmod_opp. lra.
   - unfold compose, Cminus. eapply Rle_trans; [apply Cmod_triangle| ].
     rewrite Cmod_opp, Cmod_mult. lra. }
 apply (ex_series_plus (V:=R_CNM)).
 - exists l. now apply delay_series_R.
 - apply ex_series_scal_r. now exists l.
Qed.

Lemma ex_series_linfactors a l :
  ex_series (Cmod ∘ a) ->
  ex_series (Cmod ∘ pseries_linfactors a l).
Proof.
 induction l; simpl; trivial. intros. now apply ex_series_multfactor, IHl.
Qed.

Lemma is_CPowerSeries_linfactors (a:nat->C) l x lim :
  is_CPowerSeries a x lim ->
  is_CPowerSeries (pseries_linfactors a l) x ((Peval (linfactors l) x) * lim).
Proof.
 induction l as [|c l IH]; simpl.
 - now rewrite Pconst_eval, Cmult_1_l.
 - intros H. rewrite Pmult_eval, cons_eval, Pconst_eval, Cmult_1_r.
   rewrite Cplus_comm, (Cmult_comm _ (x+-c)), <- Cmult_assoc.
   now apply is_CPowerSeries_multfactor, IH.
Qed.

Definition dhbis n :=
  let l := map Cinv (tl rootrest) in
  - mu q * big_sum (fun i => - gencoef l i * (/ l@i)^S n) (q-2).

Definition dgbis := pseries_linfactors dhbis rootrest.

Lemma sum_n_big_sum (f : nat -> nat -> C) (n m : nat) :
  sum_n (fun k => big_sum (f k) m) n =
  big_sum (fun i => sum_n (fun k => f k i) n) m.
Proof.
 induction n; simpl.
 - rewrite sum_O. apply big_sum_eq_bounded.
   intros i _. now rewrite sum_O.
 - rewrite sum_Sn, IHn. change plus with Cplus.
   rewrite <- (@big_sum_plus _ _ _ C_is_comm_group).
   apply big_sum_eq_bounded.
   intros i _. now rewrite sum_Sn.
Qed.

Lemma sum_n_big_sum_adhoc (f : nat -> nat -> C) (g : nat -> C) n m :
  sum_n (fun k => big_sum (f k) m * g k) n =
  big_sum (fun i => sum_n (fun k => f k i * g k) n) m.
Proof.
 rewrite <- sum_n_big_sum. apply sum_n_ext. intros k.
 exact (big_sum_mult_r (g k) (f k) m).
Qed.

Lemma is_lim_Cseq_bigsum (f : nat -> nat -> C) (lims : nat -> C) m :
 (forall i, (i < m)%nat -> is_lim_Cseq (fun n => f n i) (lims i)) ->
 is_lim_Cseq (fun n => big_sum (f n) m) (big_sum lims m).
Proof.
 induction m; intros Hf.
 - apply is_lim_Cseq_const.
 - simpl. apply is_lim_Cseq_plus.
   + apply IHm. intros i Hi. apply Hf. lia.
   + apply Hf. lia.
Qed.

Lemma is_series_R0 : is_series (fun _ => 0%R) 0%R.
Proof.
 apply filterlim_locally. intros eps. exists O. intros n _.
 rewrite (sum_n_zero (G:=R_AbelianMonoid)).
 change (Rabs (0-0) < eps).
 rewrite Rminus_0_r, Rabs_R0. apply eps.
Qed.

Lemma ex_series_bigsum (f : nat -> nat -> R) m :
 (forall i, (i < m)%nat -> ex_series (fun n => f n i)) ->
 ex_series (fun n => big_sum (f n) m).
Proof.
 induction m; intros Hf; simpl.
 - exists 0%R. apply is_series_R0.
 - apply (ex_series_plus (V:=R_NM)).
   + apply IHm. intros i Hi. apply Hf. lia.
   + apply Hf. lia.
Qed.

Lemma Cmod_bigsum (f : nat -> C) n :
 Cmod (big_sum f n) <= big_sum (Cmod∘f) n.
Proof.
 induction n; simpl.
 - rewrite Cmod_0. lra.
 - eapply Rle_trans; [apply Cmod_triangle|apply Rplus_le_compat_r, IHn].
Qed.

Lemma ex_series_Cmod_dhbis : ex_series (Cmod ∘ dhbis).
Proof.
 unfold dhbis.
 set (l := map Cinv (tl rootrest)). unfold compose.
 eapply ex_series_ext.
 { intros n. symmetry. rewrite Cmod_mult, Rmult_comm. reflexivity. }
 apply ex_series_scal_r.
 apply (ex_series_le (V:=R_CNM)) with
  (b:=fun n =>
        big_sum (fun i => Cmod (-gencoef l i * (/l@i)^S n)) (q-2)).
 { intros n. unfold compose. change norm with Rabs.
   rewrite Rabs_pos_eq by apply Cmod_ge_0. apply Cmod_bigsum. }
 apply ex_series_bigsum.
 intros i Hi.
 eapply ex_series_ext.
 { intros n. symmetry. rewrite Cpow_S, Cmult_assoc, Cmod_mult, Rmult_comm.
   rewrite Cmod_pow. reflexivity. }
 apply ex_series_scal_r.
 apply ex_series_geom.
 rewrite Rabs_pos_eq by apply Cmod_ge_0.
 unfold l.
 unfold Cnth.
 assert (L : (length (tl rootrest) = q-2)%nat).
 { unfold rootrest. cbn -[skipn]. rewrite skipn_length.
   rewrite (SortedRoots_length _ _ roots_ok). lia. }
 rewrite nth_map_indep with (d':=0), Cinv_inv by lia.
 fold ((tl rootrest)@i).
 set (r := (tl rootrest)@i).
 assert (IN : In r (skipn 3 roots)).
 { unfold r. change (skipn 3 roots) with (tl rootrest).
   apply nth_In. lia. }
 rewrite skipn_3_roots_spec in IN. apply IN.
Qed.

Lemma hbis_is_powerseries (x:C) :
  Cmod x <= 1 ->
  is_CPowerSeries dhbis x ((-mu q) / Peval (revfactors (tl rootrest)) x).
Proof.
 intros Hx.
 unfold dhbis. unfold Cdiv.
 eapply is_lim_Cseq_ext.
 { symmetry. erewrite sum_n_ext; [|intro k; symmetry; apply Cmult_assoc].
   apply sum_n_Cmult_l. }
 apply is_lim_Cseq_mult; [apply is_lim_Cseq_const| ].
 eapply is_lim_Cseq_ext.
 { symmetry. apply sum_n_big_sum_adhoc. }
 cbn -[rootrest sum_n Cpow].
 unfold revfactors.
 assert (L : (length (tl rootrest) = q-2)%nat).
 { unfold rootrest. cbn -[skipn]. rewrite skipn_length.
   rewrite (SortedRoots_length _ _ roots_ok). lia. }
 rewrite inv_linfactors_partfrac, map_length.
 2:{ intros E. apply (f_equal (@length _)) in E.
     rewrite map_length, L in E. simpl in E. lia. }
 2:{ apply FinFun.Injective_map_NoDup.
     - intros a b E. now rewrite <- (Cinv_inv a), E, Cinv_inv.
     - unfold rootrest. cbn -[skipn]. apply skipn_nodup.
       apply (SortedRoots_nodup _ _ roots_ok). }
 2:{ unfold rootrest. cbn -[skipn]. rewrite in_map_iff.
     intros (y & <- & IN). rewrite skipn_3_roots_spec in IN.
     rewrite Cmod_inv in Hx.
     apply Rmult_le_compat_l with (r:=Cmod y) in Hx; try apply Cmod_ge_0.
     rewrite Rinv_r in Hx; try lra.
     assert (Hy : y <> 0).
     { intros ->.
       now apply (root_nz q), (SortedRoots_roots _ _ roots_ok). }
     apply Cmod_gt_0 in Hy. lra. }
 rewrite L.
 apply is_lim_Cseq_bigsum. intros i Hi.
 rewrite <- Copp_minus_distr. unfold Cdiv. rewrite Cinv_Copp.
 rewrite <- Copp_mult_distr_r, Copp_mult_distr_l.
 eapply is_lim_Cseq_ext.
 { symmetry. erewrite sum_n_ext; [|intro k; symmetry; apply Cmult_assoc].
   apply sum_n_Cmult_l. }
 apply is_lim_Cseq_mult; [apply is_lim_Cseq_const| ].
 unfold Cnth.
 rewrite nth_map_indep with (d':=0), Cinv_inv by lia.
 fold ((tl rootrest)@i).
 set (r := (tl rootrest)@i).
 assert (IN : In r (skipn 3 roots)).
 { unfold r. change (skipn 3 roots) with (tl rootrest).
   apply nth_In. lia. }
 apply is_powerseries_invlin.
 - intros E.
   apply (root_nz q). rewrite <- E.
   rewrite <- (SortedRoots_roots _ _ roots_ok).
   apply skipn_3_roots_spec in IN. apply IN.
 - rewrite Cmod_mult.
   apply skipn_3_roots_spec in IN.
   apply Rle_lt_trans with (Cmod r * 1)%R; try lra.
   apply Rmult_le_compat_l; try lra. apply Cmod_ge_0.
Qed.

Lemma ex_series_Cmod_dgbis : ex_series (Cmod ∘ dgbis).
Proof.
 unfold dgbis. apply ex_series_linfactors, ex_series_Cmod_dhbis.
Qed.

Lemma gbis_is_powerseries (x:C) :
  Cmod x <= 1 -> is_CPowerSeries dgbis x (gbis x).
Proof.
 intros Hx. unfold gbis, dgbis.
 rewrite Cmult_comm. unfold Cdiv. rewrite <- Cmult_assoc.
 apply is_CPowerSeries_linfactors.
 now apply hbis_is_powerseries.
Qed.

Lemma gbis_powerseries (x:C) :
  Cmod x <= 1 -> gbis x = CPowerSeries dgbis x.
Proof.
 intros. symmetry. now apply CPowerSeries_unique, gbis_is_powerseries.
Qed.

Lemma is_CPowerSeries_proj (a:nat->C)(x:R) :
  ex_series (fun n => Cmod (a n) * Rabs x^n)%R ->
  is_CPowerSeries a x (PSeries (Re∘a) x, PSeries (Im∘a) x).
Proof.
 intros H.
 unfold is_CPowerSeries. rewrite is_lim_Cseq_proj. simpl. split.
 - eapply is_lim_seq_ext with (u:=sum_n (fun k => (Re∘a) k * x^k)%R).
   { intros n. unfold compose. rewrite re_sum_n. apply sum_n_ext.
     clear n. intros n. unfold compose.
     now rewrite <- re_scal_r, <- RtoC_pow. }
   unfold PSeries, Series. apply Lim_seq_correct'. rewrite <- ex_series_alt.
   eapply (ex_series_le (V:=R_CNM)); eauto.
   { intros n. change norm with Rabs.
     rewrite Rabs_mult. unfold compose. rewrite RPow_abs.
     apply Rmult_le_compat_r; try apply Rabs_pos. apply re_le_Cmod. }
 - eapply is_lim_seq_ext with (u:=sum_n (fun k => (Im∘a) k * x^k)%R).
   { intros n. unfold compose. rewrite im_sum_n. apply sum_n_ext.
     clear n. intros n. unfold compose.
     now rewrite <- im_scal_r, <- RtoC_pow. }
   unfold PSeries, Series. apply Lim_seq_correct'. rewrite <- ex_series_alt.
   eapply (ex_series_le (V:=R_CNM)); eauto.
   { intros n. change norm with Rabs.
     rewrite Rabs_mult. unfold compose. rewrite RPow_abs.
     apply Rmult_le_compat_r; try apply Rabs_pos. apply im_le_Cmod. }
Qed.

Lemma CPowerSeries_proj (a:nat->C)(x:R) :
  ex_series (fun n => Cmod (a n) * Rabs x^n)%R ->
  CPowerSeries a x = (PSeries (Re∘a) x, PSeries (Im∘a) x).
Proof.
 intros. now apply CPowerSeries_unique, is_CPowerSeries_proj.
Qed.

Lemma CV_disk_le_radius (a:nat->R) (x:R) :
 CV_disk a x -> Rbar.Rbar_le x (CV_radius a).
Proof.
 intros H.
 unfold CV_radius, Lub.Lub_Rbar.
 destruct (Lub.ex_lub_Rbar _) as (lu & Hlu). now apply Hlu.
Qed.

Lemma CV_radius_ge_1 (a : nat -> R) :
  ex_series (Rabs∘a) -> Rbar.Rbar_le 1%R (CV_radius a).
Proof.
 intros H. apply CV_disk_le_radius.
 red. eapply ex_series_ext; eauto. intros n. now rewrite pow1, Rmult_1_r.
Qed.

Lemma CV_radius_le (a b : nat -> R) :
 (forall n, Rabs (a n) <= Rabs (b n)) ->
 Rbar.Rbar_le (CV_radius b) (CV_radius a).
Proof.
 intros H.
 unfold CV_radius, Lub.Lub_Rbar.
 destruct Lub.ex_lub_Rbar as (ubb & Hb & Hb').
 destruct Lub.ex_lub_Rbar as (uba & Ha & Ha'). simpl.
 - red in Hb, Ha. apply Hb'. red. intros x Hx. apply Ha.
   clear - H Hx. unfold CV_disk in *.
   eapply (ex_series_le (V:=R_CNM)); eauto.
   intros n. change norm with Rabs. rewrite Rabs_Rabsolu, !Rabs_mult.
   apply Rmult_le_compat_r; trivial using Rabs_pos.
Qed.

Lemma CPowerSeries_coef_ext (a b : nat -> C) :
 Rbar.Rbar_lt 0%R (CV_radius (Cmod∘a)) ->
 Rbar.Rbar_lt 0%R (CV_radius (Cmod∘b)) ->
 locally 0%R (fun (x:R) => CPowerSeries a x = CPowerSeries b x) ->
 forall n, a n = b n.
Proof.
 intros Ha Hb E n.
 rewrite (surjective_pairing (a n)), (surjective_pairing (b n)).
 assert (L: locally 0%R
             (fun x : R => PSeries (Re ∘ a) x = PSeries (Re ∘ b) x
                        /\ PSeries (Im ∘ a) x = PSeries (Im ∘ b) x)).
 { destruct E as (eps & E).
   set (ra := match CV_radius (Cmod∘a) with Rbar.Finite r => r | _ => 1%R end).
   assert (Ra : 0 < ra).
   { unfold ra. destruct (CV_radius (Cmod∘a)); try easy. lra. }
   set (rb := match CV_radius (Cmod∘b) with Rbar.Finite r => r | _ => 1%R end).
   assert (Rb : 0 < rb).
   { unfold rb. destruct (CV_radius (Cmod∘b)); try easy. lra. }
   assert (LT : 0 < Rmin eps (Rmin ra rb)).
   { apply Rmin_glb_lt. apply eps. now apply Rmin_glb_lt. }
   set (eps' := mkposreal _ LT).
   exists eps'. intros y Y. change (Rabs (y-0) < eps') in Y.
   assert (Y0 : Rabs (y - 0) < eps).
   { apply Rlt_le_trans with eps'; trivial. apply Rmin_l. }
   specialize (E y Y0). clear Y0.
   rewrite !CPowerSeries_proj in E; trivial; try lra.
   + now injection E.
   + clear E Ha. clearbody ra.
     rewrite Rminus_0_r in Y.
     assert (ex_pseries (Cmod∘b) (Rabs y)).
     { apply CV_radius_inside. rewrite Rabs_Rabsolu.
       apply Rbar.Rbar_lt_le_trans with eps'; trivial.
       apply Rbar.Rbar_le_trans with (Rmin ra rb); [apply Rmin_r|].
       apply Rbar.Rbar_le_trans with rb; [apply Rmin_r|].
       unfold rb. destruct CV_radius; simpl; trivial; lra. }
     red in H. eapply ex_series_ext; eauto.
     intros k. unfold compose. unfold scal. simpl.
     change mult with Rmult.
     rewrite pow_n_pow. ring.
   + clear E Hb. clearbody rb.
     rewrite Rminus_0_r in Y.
     assert (ex_pseries (Cmod∘a) (Rabs y)).
     { apply CV_radius_inside. rewrite Rabs_Rabsolu.
       apply Rbar.Rbar_lt_le_trans with eps'; trivial.
       apply Rbar.Rbar_le_trans with (Rmin ra rb); [apply Rmin_r|].
       apply Rbar.Rbar_le_trans with ra; [apply Rmin_l|].
       unfold ra. destruct CV_radius; simpl; trivial; lra. }
     red in H. eapply ex_series_ext; eauto.
     intros k. unfold compose. unfold scal. simpl.
     change mult with Rmult.
     rewrite pow_n_pow. ring. }
 f_equal.
 - apply (PSeries_ext_recip (Re∘a) (Re∘b) n).
   + apply Rbar.Rbar_lt_le_trans with (CV_radius (Cmod∘a)); auto.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply re_le_Cmod.
   + apply Rbar.Rbar_lt_le_trans with (CV_radius (Cmod∘b)); auto.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply re_le_Cmod.
   + destruct L as (eps & L). exists eps. apply L.
 - apply (PSeries_ext_recip (Im∘a) (Im∘b) n).
   + apply Rbar.Rbar_lt_le_trans with (CV_radius (Cmod∘a)); auto.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply im_le_Cmod.
   + apply Rbar.Rbar_lt_le_trans with (CV_radius (Cmod∘b)); auto.
     apply CV_radius_le. intros k. unfold compose.
     rewrite (Rabs_pos_eq (Cmod _)) by apply Cmod_ge_0. apply im_le_Cmod.
   + destruct L as (eps & L). exists eps. apply L.
Qed.

Lemma dgbis_dg : forall n, dgbis n = dg q n.
Proof.
 apply CPowerSeries_coef_ext.
 - apply Rbar.Rbar_lt_le_trans with (1%R). simpl; lra. apply CV_radius_ge_1.
   apply ex_series_ext with (a:=Cmod∘dgbis).
   + intros n. symmetry. apply Rabs_pos_eq. apply Cmod_ge_0.
   + apply ex_series_Cmod_dgbis.
 - apply Rbar.Rbar_lt_le_trans with (/2)%R. simpl; lra.
   apply CV_disk_le_radius. red.
   eapply ex_series_ext;
   [|apply (ex_pseries_Rabs_dg q lia roots roots_ok) with (x:=(/2)%R)].
   + intros n. unfold compose. rewrite !Rabs_mult.
     now rewrite Cmod_R, Rabs_Rabsolu.
   + apply Hyp_alt'.
   + rewrite Rabs_pos_eq; lra.
 - assert (LT : 0 < 1/2) by lra.
   set (e := mkposreal _ LT).
   exists e. intros y Hy. change (Rabs (y-0) < 1/2) in Hy.
   rewrite Rminus_0_r in Hy.
   rewrite <- gbis_powerseries.
   2:{ rewrite Cmod_R. lra. }
   assert (Y : y <> tau q).
   { generalize (tau_itvl q) (Rle_abs y). lra. }
   assert (Y' : RtoC y <> RtoC (tau q)).
   { contradict Y. now injection Y. }
   rewrite <- (g_powerseries q lia roots roots_ok); trivial.
   + apply gbis_g. repeat split; trivial.
     * intros E. apply (f_equal Cmod) in E. rewrite Cmod_R in E.
       rewrite Cmod_Cexp in E. lra.
     * intros E. apply (f_equal Cmod) in E. rewrite Cmod_R in E.
       rewrite Cmod_Cexp in E. lra.
   + intros r R. rewrite Cmod_mult, Cmod_R. apply Hyp_alt' in R.
     apply Rle_lt_trans with (1 * Rabs y)%R; try lra.
     apply Rmult_le_compat_r; trivial using Rabs_pos.
Qed.

Lemma One_again : CSeries (fun n => (dgbis n)^2) = 1 + mu q^2.
Proof.
 rewrite <- (Mu_series_square dgbis gbis).
 { unfold Mu.
   assert (N : C2*PI <> 0).
   { intros E. rewrite <- RtoC_mult in E. apply RtoC_inj in E.
     generalize PI_RGT_0; lra. }
   apply Cmult_eq_reg_l with (C2*PI); trivial.
   rewrite Cmult_assoc, Cinv_r, Cmult_1_l; trivial.
   apply is_CInt_unique.
   apply (is_RInt_ext (V:=C_NM))
    with (f := fun t => 1 + mu q^2 - mu q * (Cexp t - -Cexp (-t))).
   { intros t _.
     rewrite Cexp_neg. rewrite ggbis by now rewrite Cmod_Cexp.
     fixeq C. field. apply Cexp_nonzero. }
   replace (C2*_*_) with (C2*PI*(1+mu q^2) - 0) by ring.
   apply (is_RInt_minus (V:=C_NM)).
   - rewrite <- RtoC_mult.
     replace (RtoC (2*PI)) with (RtoC (2*PI)-0) by ring.
     apply is_CInt_const.
   - replace 0 with ((mu q)*(0-0)) at 1 by ring.
     apply is_CInt_scal, (is_RInt_minus (V:=C_NM)).
     + generalize (is_CInt_Cexp 1 lia). apply is_RInt_ext.
       intros x _. f_equal. now rewrite Rmult_1_l.
     + apply (is_RInt_comp_opp (V:=C_NM)).
       rewrite Ropp_0, Ropp_mult_distr_l.
       generalize (is_CInt_Cexp' 1 lia). apply is_RInt_ext.
       intros x _. f_equal. now rewrite Rmult_1_l. }
 { apply ex_series_Cmod_dgbis. }
 { intros z Hz. apply gbis_powerseries. lra. }
Qed.

Local Open Scope R.

Lemma One_again' : Series (fun n => (dg q n)^2) = 1 + mu q^2.
Proof.
 apply is_series_unique.
 rewrite <- (re_RtoC (1+mu q^2)).
 apply CSeries_RtoC_impl.
 unfold compose. rewrite RtoC_plus, <- RtoC_pow.
 rewrite <- One_again.
 apply is_lim_Cseq_ext with (sum_n (fun k => dgbis k^2))%C.
 - intros n. apply sum_n_ext. intros m. now rewrite <- RtoC_pow, dgbis_dg.
 - apply CSeries_correct. apply ex_series_Cmod.
   apply ex_series_ext with (fun k => (Cmod (dgbis k))^2)%R.
   { intros n. unfold compose. now rewrite Cmod_pow. }
   apply ex_series_square.
   apply ex_series_ext with (Cmod ∘ dgbis).
   { intros n. unfold compose. now rewrite Rabs_pos_eq by apply Cmod_ge_0. }
   apply ex_series_Cmod_dgbis.
Qed.

Lemma One_le_again : forall n, sum_n (fun n => (dg q n)^2) n <= 1 + mu q^2.
Proof.
 apply pos_series_pos_sum.
 2:{ intros n. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
 rewrite <- One_again' by trivial.
 apply Series_correct.
 apply (ex_series_square (dg q)).
 apply ex_series_ext with (Cmod ∘ dgbis).
 { intros n. unfold compose. now rewrite dgbis_dg, Cmod_R. }
 apply ex_series_Cmod_dgbis.
Qed.

Lemma the_contradiction : False.
Proof.
 assert (Hq6 : (6 <= q)%nat).
 { apply Nat.le_lteq in Hq. destruct Hq; try lia. subst. easy. }
 assert (H := One_le_again (2*q)).
 assert (H' : 0 < coef2 q * mu q^2 + coef1 q * mu q + coef0 q).
 { apply le_INR in Hq6. rewrite (INR_IZR_INZ 6) in Hq6. simpl in Hq6.
   apply discriminant_neg.
   - unfold coef2. nra.
   - apply Rminus_gt_0_lt. unfold coef0, coef1, coef2.
     field_simplify. nra. }
 rewrite <- (One_aux_eqn q (mu q)) in H' by lia. unfold dg in H. lra.
Qed.

End HandlingModulusOne.

Lemma LargerSndRoot_after_5 q : (5<=q)%nat -> ThePoly_ExSndRootGt1 q.
Proof.
 intros Hq.
 destruct (Nat.eq_dec (q mod 6) 4) as [Hq'|Hq'].
 - rewrite ThePoly_SndRoots_neg'. intros Hyp.
   destruct (SortedRoots_exists q) as (roots & roots_ok).
   apply (the_contradiction q Hq Hq' Hyp roots roots_ok).
 - apply (LargerSndRoot_after_5_easy q Hq Hq').
Qed.

(* The former axiom : *)

Lemma large_second_best_root q roots :
  (5<=q)%nat -> SortedRoots q roots -> 1 < Cmod (roots@1).
Proof.
 intros Hq roots_ok.
 destruct (LargerSndRoot_after_5 q Hq) as (r & Hr & N & GT).
 eapply Rlt_le_trans; [ apply GT | ].
 assert (M := SortedRoots_mu _ _ roots_ok).
 rewrite (proj1 roots_ok), <- linfactors_roots in Hr.
 apply SortedRoots_Cmod_sorted in roots_ok.
 rewrite StronglySorted_nth in roots_ok.
 destruct (In_nth roots r 0 Hr) as (i & Hi & <-).
 change (nth i roots 0) with (roots @ i) in *.
 destruct i as [|[|i] ]; try lra. intuition.
 apply Rge_le, roots_ok. lia.
Qed.

(* Print Assumptions large_second_best_root. *)
