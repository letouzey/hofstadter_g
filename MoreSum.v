From Coq Require Import Lia Reals Lra.
From Coquelicot Require Complex.
From Coquelicot Require Import Hierarchy.
From QuantumLib Require Import Complex.
Require Import DeltaList MoreList MoreReals MoreComplex.
Local Open Scope R.
Local Coercion INR : nat >-> R.

(** * Various flavours of summations *)

(** Sum of [List R]. *)

Definition Rlistsum (l: list R) := List.fold_right Rplus 0 l.

Lemma Rlistsum_cons x l : Rlistsum (x::l) = x + Rlistsum l.
Proof.
 reflexivity.
Qed.

Lemma Rlistsum_app l l' : Rlistsum (l++l') = Rlistsum l + Rlistsum l'.
Proof.
 induction l; simpl; rewrite ?IHl; lra.
Qed.

Lemma Rlistsum_rev l : Rlistsum (List.rev l) = Rlistsum l.
Proof.
 induction l; simpl; auto.
 rewrite Rlistsum_app, IHl. simpl; lra.
Qed.

Lemma listsum_INR (l:list nat) : INR (list_sum l) = Rlistsum (map INR l).
Proof.
 induction l; simpl; trivial. rewrite plus_INR. now f_equal.
Qed.

Lemma Rlistsum_distr l r : Rlistsum l * r = Rlistsum (map (fun x => x*r) l).
Proof.
 induction l; simpl; lra.
Qed.

Lemma Rdist_listsum {A}(f g:A->R) l :
 R_dist (Rlistsum (map f l)) (Rlistsum (map g l)) <=
 Rlistsum (map (fun x => R_dist (f x) (g x)) l).
Proof.
 induction l; simpl.
 - rewrite R_dist_eq; lra.
 - eapply Rle_trans. apply R_dist_plus.
   apply Rplus_le_compat_l. apply IHl.
Qed.

Lemma Rlistsum_le {A}(f g:A->R) l :
 (forall a, In a l -> f a <= g a) ->
 Rlistsum (map f l) <= Rlistsum (map g l).
Proof.
 induction l; simpl. lra.
 intros H. apply Rplus_le_compat. apply H; intuition.
 apply IHl; intuition.
Qed.

Definition Rpoly x l := Rlistsum (List.map (pow x) l).

Lemma Rpoly_cons x n l : Rpoly x (n::l) = (x^n + Rpoly x l)%R.
Proof.
 easy.
Qed.

Lemma Rpoly_app x l l' : Rpoly x (l++l') = (Rpoly x l + Rpoly x l')%R.
Proof.
 unfold Rpoly. now rewrite map_app, Rlistsum_app.
Qed.

Lemma Rlistsum_pow_factor r p l :
 Rlistsum (List.map (fun n => r^(p+n)) l) = r^p * Rpoly r l.
Proof.
 induction l; cbn -[pow].
 - ring.
 - change (List.fold_right Rplus 0) with Rlistsum. rewrite IHl.
   fold (Rpoly r l). rewrite Rdef_pow_add. ring.
Qed.

Lemma Rpoly_factor_above r p l :
 (forall n, List.In n l -> p <= n)%nat ->
 Rpoly r l = r^p * Rpoly r (List.map (decr p) l).
Proof.
 induction l as [|a l IH]; cbn -[pow]; intros Hl.
 - ring.
 - change (List.fold_right Rplus 0) with Rlistsum.
   fold (Rpoly r l). fold (Rpoly r (map (decr p) l)).
   rewrite IH by intuition.
   replace a with ((a-p)+p)%nat at 1 by (specialize (Hl a); lia).
   rewrite Rdef_pow_add. unfold decr at 2. ring.
Qed.

Lemma sum_pow_cons k l n r :
  O<>k -> 0<=r<1 -> Delta k (n::l) ->
  Rlistsum (List.map (pow r) (n::l)) <= r^n/(1-r^k).
Proof.
 intros Hk Hr.
 assert (H3 : 0 <= r^k < 1).
 { apply pow_lt_1_compat. lra. lia. }
 revert n.
 induction l.
 - intros n _. cbn -[pow].
   rewrite Rplus_0_r.
   apply Rcomplements.Rle_div_r; try lra.
   rewrite <- (Rmult_1_r (r^n)) at 2.
   apply Rmult_le_compat_l; try lra.
   apply pow_le; lra.
 - intros n. inversion_clear 1.
   change (Rlistsum _) with (r^n + Rlistsum (List.map (pow r) (a::l))).
   eapply Rle_trans. eapply Rplus_le_compat_l. apply IHl; eauto.
   apply Rcomplements.Rle_div_r; try lra.
   field_simplify; try lra.
   rewrite <- Ropp_mult_distr_l, <- pow_add.
   assert (r^a <= r^(n+k)). { apply Rle_pow_low; auto. }
   lra.
Qed.

Lemma sum_pow k l r :
  O<>k -> 0<=r<1 -> Delta k l ->
  Rlistsum (List.map (pow r) l) <= /(1-r^k).
Proof.
 intros Hk Hr D.
 assert (H3 : 0 <= r^k < 1).
 { apply pow_lt_1_compat. lra. lia. }
 destruct l as [|n l].
 - cbn -[pow].
   rewrite <- (Rmult_1_l (/ _)).
   apply Rcomplements.Rle_div_r; try lra.
 - eapply Rle_trans. apply (sum_pow_cons k); auto.
   rewrite <- (Rmult_1_l (/ _)).
   apply Rmult_le_compat_r.
   rewrite <- (Rmult_1_l (/ _)).
   apply Rcomplements.Rle_div_r; try lra.
   rewrite <-(pow1 n).
   apply pow_maj_Rabs. rewrite Rabs_right; lra.
Qed.

(** Sums of (list C). *)

Local Open Scope C.

Definition Clistsum l := List.fold_right Cplus 0 l.

Lemma Clistsum_cons x l : Clistsum (x::l) = (x + Clistsum l)%C.
Proof.
 reflexivity.
Qed.

Lemma Clistsum_app l l' : Clistsum (l++l') = Clistsum l + Clistsum l'.
Proof.
 induction l; simpl; rewrite ?IHl; ring.
Qed.

Lemma Clistsum_zero {A}(l:list A) : Clistsum (map (fun _ => C0) l) = C0.
Proof.
 induction l; simpl; rewrite ?IHl; lca.
Qed.

Lemma Clistsum_const {A}(l:list A) c :
  Clistsum (map (fun _ => c) l) = c * RtoC (INR (length l)).
Proof.
 induction l; cbn -[INR]. lca. unfold Clistsum in *.
 rewrite IHl, S_INR, RtoC_plus. ring.
Qed.

Lemma Clistsum_map {A} (f : A -> C) (l:list A) (d:A) :
  Clistsum (map f l) = big_sum (fun i => f (nth i l d)) (length l).
Proof.
 induction l; trivial.
 simpl length. rewrite big_sum_shift. simpl. now f_equal.
Qed.

Lemma Clistsum_factor_l c l : c * Clistsum l = Clistsum (map (Cmult c) l).
Proof.
 induction l; simpl. lca. rewrite <- IHl. lca.
Qed.

Lemma Clistsum_plus {A} (f g : A->C) l :
 Clistsum (map f l) + Clistsum (map g l) =
 Clistsum (map (fun x => f x + g x) l).
Proof.
 induction l; simpl. lca. rewrite <- IHl. lca.
Qed.

Lemma Clistsum_minus {A} (f g : A->C) l :
 Clistsum (map f l) - Clistsum (map g l) =
 Clistsum (map (fun x => f x - g x) l).
Proof.
 induction l; simpl. lca. rewrite <- IHl. lca.
Qed.

Lemma Clistsum_conj l : Cconj (Clistsum l) = Clistsum (map Cconj l).
Proof.
 induction l; simpl. lca. rewrite <- IHl. lca.
Qed.

Lemma Clistsum_Clistsum {A B} (f : A -> B -> C) lA lB :
 Clistsum (map (fun a => Clistsum (map (f a) lB)) lA)
 = Clistsum (map (fun b => Clistsum (map (fun a => f a b) lA)) lB).
Proof.
 revert lB. induction lA. simpl; intros. now rewrite Clistsum_zero.
 intros lB. simpl. rewrite IHlA.
 now rewrite Clistsum_plus.
Qed.

Lemma RtoC_Rlistsum l : RtoC (Rlistsum l) = Clistsum (map RtoC l).
Proof.
 induction l; simpl; trivial. now rewrite RtoC_plus, IHl.
Qed.

Lemma Clistsum_mod l : (Cmod (Clistsum l) <= Rlistsum (map Cmod l))%R.
Proof.
 induction l; simpl.
 - rewrite Cmod_0; lra.
 - eapply Rle_trans; [apply Cmod_triangle|]. lra.
Qed.

Definition Cpoly x l := Clistsum (List.map (Cpow x) l).

Lemma Cpoly_cons x n l : Cpoly x (n::l) = x^n + Cpoly x l.
Proof.
 easy.
Qed.

Lemma Cpoly_app x l l' : Cpoly x (l++l') = Cpoly x l + Cpoly x l'.
Proof.
 unfold Cpoly. now rewrite map_app, Clistsum_app.
Qed.

Lemma Clistsum_pow_factor c p l :
 Clistsum (List.map (fun n => c^(p+n))%C l) = c^p * Cpoly c l.
Proof.
 induction l; cbn -[Cpow].
 - ring.
 - change (List.fold_right Cplus 0) with Clistsum. rewrite IHl.
   fold (Cpoly c l). rewrite Cpow_add_r. ring.
Qed.

Lemma Cpoly_factor_above c p l :
 (forall n, List.In n l -> p <= n)%nat ->
 Cpoly c l = c^p * Cpoly c (List.map (decr p) l).
Proof.
 induction l as [|a l IH]; cbn -[Cpow]; intros Hl.
 - ring.
 - change (List.fold_right Cplus 0) with Clistsum.
   fold (Cpoly c l). fold (Cpoly c (map (decr p) l)).
   rewrite IH by intuition.
   replace a with ((a-p)+p)%nat at 1 by (specialize (Hl a); lia).
   rewrite Cpow_add_r. unfold decr at 2. ring.
Qed.

(** G_big_mult : Product of a list of complex *)

Lemma Gbigmult_0 (l : list C) : G_big_mult l = C0 <-> In C0 l.
Proof.
 induction l; simpl.
 - split. apply C1_neq_C0. easy.
 - rewrite <- IHl. apply Cmult_integral.
Qed.

Lemma Gbigmult_factor_r l c :
  G_big_mult (map (fun x => x * c) l) = G_big_mult l * c ^ length l.
Proof.
 induction l; simpl; rewrite ?IHl; ring.
Qed.

Lemma Gbigmult_perm l l' : Permutation l l' -> G_big_mult l = G_big_mult l'.
Proof.
 induction 1; simpl; ring || congruence.
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

(** QuantumLib's big_sum *)

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

Lemma Cmod_bigsum (f : nat -> C) n :
 Cmod (big_sum f n) <= big_sum (Cmod∘f) n.
Proof.
 induction n; simpl.
 - rewrite Cmod_0. lra.
 - eapply Rle_trans; [apply Cmod_triangle|apply Rplus_le_compat_r, IHn].
Qed.

Lemma big_sum_kronecker f n m :
 (m < n)%nat ->
 (forall i, (i < n)%nat -> i<>m -> f i = 0) ->
 big_sum f n = f m.
Proof.
 revert m.
 induction n.
 - lia.
 - intros m M F. rewrite <- big_sum_extend_r. simpl.
   destruct (Nat.eq_dec n m) as [<-|M'].
   + rewrite big_sum_0_bounded. lca. intros i Hi. apply F; lia.
   + rewrite F, Cplus_0_r by lia. apply IHn; try lia.
     intros i Hi. apply F; lia.
Qed.