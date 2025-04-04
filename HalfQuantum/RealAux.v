(** Supplement to Coq's axiomatized Reals *)

Require Export Znat.
Require Export Reals.
Require Import Psatz.
Require Export Program.
Require Export Summation.
 
(** * Basic lemmas *)

(** Relevant lemmas from Coquelicot's Rcomplements.v **)

Local Open Scope R_scope.
Local Coercion INR : nat >-> R.

Lemma Rle_minus_l : forall a b c,(a - c <= b <-> a <= b + c). Proof. intros. lra. Qed.
Lemma Rlt_minus_r : forall a b c,(a < b - c <-> a + c < b). Proof. intros. lra. Qed.
Lemma Rlt_minus_l : forall a b c,(a - c < b <-> a < b + c). Proof. intros. lra. Qed.
Lemma Rle_minus_r : forall a b c,(a <= b - c <-> a + c <= b). Proof. intros. lra. Qed.
Lemma Rminus_le_0 : forall a b, a <= b <-> 0 <= b - a. Proof. intros. lra. Qed.
Lemma Rminus_lt_0 : forall a b, a < b <-> 0 < b - a. Proof. intros. lra. Qed.
Lemma Ropp_lt_0 : forall x : R, x < 0 -> 0 < -x. Proof. intros. lra. Qed.

(* Automation *)

Lemma Rminus_unfold : forall r1 r2, (r1 - r2 = r1 + -r2). Proof. reflexivity. Qed.
Lemma Rdiv_unfold : forall r1 r2, (r1 / r2 = r1 */ r2). Proof. reflexivity. Qed.

#[export] Hint Rewrite Rminus_unfold Rdiv_unfold Ropp_0 Ropp_involutive Rplus_0_l 
             Rplus_0_r Rmult_0_l Rmult_0_r Rmult_1_l Rmult_1_r : R_db.
#[export] Hint Rewrite <- Ropp_mult_distr_l Ropp_mult_distr_r : R_db.
#[export] Hint Rewrite Rinv_l Rinv_r sqrt_sqrt using lra : R_db.

Notation "√ n" := (sqrt n) (at level 20) : R_scope.

(** Other useful facts *)

Lemma Rmult_div_assoc : forall (x y z : R), x * (y / z) = x * y / z.
Proof. intros. unfold Rdiv. rewrite Rmult_assoc. reflexivity. Qed.

Lemma Rmult_div : forall r1 r2 r3 r4 : R, r2 <> 0 -> r4 <> 0 -> 
  r1 / r2 * (r3 / r4) = r1 * r3 / (r2 * r4). 
Proof. intros. unfold Rdiv. rewrite Rinv_mult; trivial. lra. Qed.

Lemma Rdiv_cancel :  forall r r1 r2 : R, r1 = r2 -> r / r1 = r / r2.
Proof. intros. rewrite H. reflexivity. Qed.

(* FIXME: TODO: Remove; included in later versions of stdlib *)
Lemma Rdiv_0_r : forall r, r / 0 = 0.
Proof. intros. rewrite Rdiv_unfold, Rinv_0, Rmult_0_r. reflexivity. Qed.

Lemma Rdiv_0_l : forall r, 0 / r = 0.
Proof. intros. rewrite Rdiv_unfold, Rmult_0_l. reflexivity. Qed.

Lemma Rdiv_opp_l : forall r1 r2, - r1 / r2 = - (r1 / r2).
Proof. intros. lra. Qed.

Lemma Rsqr_def : forall r, r² = r * r.
Proof. intros r. easy. Qed.

(* END FIXME *)

Lemma Rsum_nonzero : forall r1 r2 : R, r1 <> 0 \/ r2 <> 0 -> r1 * r1 + r2 * r2 <> 0. 
Proof.
  intros.
  replace (r1 * r1)%R with (r1 ^ 2)%R by lra.
  replace (r2 * r2)%R with (r2 ^ 2)%R by lra.
  specialize (pow2_ge_0 (r1)). intros GZ1.
  specialize (pow2_ge_0 (r2)). intros GZ2.
  destruct H.
  - specialize (pow_nonzero r1 2 H). intros NZ. lra.
  - specialize (pow_nonzero r2 2 H). intros NZ. lra.
Qed.

Lemma Rmult_le_impl_le_disj_nonneg (x y z w : R) 
  (Hz : 0 <= z) (Hw : 0 <= w) : 
  x * y <= z * w -> x <= z \/ y <= w.
Proof.
  destruct (Rle_or_lt x z), (Rle_or_lt y w); 
  [left + right; easy..|].
  assert (Hx : 0 < x) by lra.
  assert (Hy : 0 < y) by lra.
  intros Hfasle.
  destruct Hz, Hw; enough (z * w < x * y) by lra;
  [|subst; rewrite ?Rmult_0_l, ?Rmult_0_r; 
    apply Rmult_lt_0_compat; easy..].
  pose proof (Rmult_lt_compat_r w z x) as Ht1.
  pose proof (Rmult_lt_compat_l x w y) as Ht2.
  lra.
Qed.

Lemma Rle_pow_le_nonneg (x y : R) (Hx : 0 <= x) (Hy : 0 <= y) n :
  x ^ (S n) <= y ^ (S n) -> x <= y.
Proof.
  induction n; [rewrite !pow_1; easy|].
  change (?z ^ S ?m) with (z * z ^ m).
  intros H.
  apply Rmult_le_impl_le_disj_nonneg in H; 
  [|easy|apply pow_le; easy].
  destruct H; auto.
Qed.

Lemma Rabs_eq_0_iff a : Rabs a = 0 <-> a = 0.
Proof.
  split; [|intros ->; apply Rabs_R0]. 
  unfold Rabs.
  destruct (Rcase_abs a); lra.
Qed.

Lemma Rplus_ge_0_of_ge_Rabs a b : Rabs a <= b -> 0 <= a + b.
Proof.
  unfold Rabs.
  destruct (Rcase_abs a); lra.
Qed.

Lemma Rpow_0_l n : O <> n -> (0 ^ n = 0)%R.
Proof.
  intros H.
  destruct n; [easy|].
  simpl; now field_simplify.
Qed.

Lemma Rpow_le1: forall (x : R) (n : nat), 0 <= x <= 1 -> x ^ n <= 1.
Proof.
  intros; induction n.
  - simpl; lra.
  - simpl.
    rewrite <- Rmult_1_r.
    apply Rmult_le_compat; try lra.
    apply pow_le; lra.
Qed.

(* The other side of Rle_pow, needed below *)
Lemma Rle_pow_le1: forall (x : R) (m n : nat), 
  0 <= x <= 1 -> (m <= n)%nat -> x ^ n <= x ^ m.
Proof.
  intros x m n [G0 L1] L.
  remember (n - m)%nat as p.
  replace n with (m+p)%nat in * by lia.
  clear -G0 L1.
  rewrite pow_add.
  rewrite <- Rmult_1_r.
  apply Rmult_le_compat; try lra.
  apply pow_le; trivial.
  apply pow_le; trivial.
  apply Rpow_le1; lra.
Qed.


(** * Square roots *)

Lemma pow2_sqrt : forall x:R, 0 <= x -> (√ x) ^ 2 = x.
Proof. intros; simpl; rewrite Rmult_1_r, sqrt_def; auto. Qed.

Lemma sqrt_pow : forall (r : R) (n : nat), (0 <= r)%R -> (√ (r ^ n) = √ r ^ n)%R.
Proof.
  intros r n Hr.
  induction n.
  simpl. apply sqrt_1.
  rewrite <- 2 tech_pow_Rmult.
  rewrite sqrt_mult_alt by assumption.
  rewrite IHn. reflexivity.
Qed.

Lemma pow2_sqrt2 : (√ 2) ^ 2 = 2.
Proof. apply pow2_sqrt; lra. Qed.

Lemma pown_sqrt : forall (x : R) (n : nat), 
  0 <= x -> √ x ^ (S (S n)) = x * √ x ^ n.
Proof.
  intros. simpl. rewrite <- Rmult_assoc. rewrite sqrt_sqrt; auto.
Qed.  

Lemma sqrt_neq_0_compat : forall r : R, 0 < r -> √ r <> 0.
Proof. intros. specialize (sqrt_lt_R0 r). lra. Qed.

Lemma sqrt_inv : forall (r : R), 0 < r -> √ (/ r) = (/ √ r)%R.
Proof.
  intros.
  replace (/r)%R with (1/r)%R by lra.
  rewrite sqrt_div_alt, sqrt_1 by lra.
  lra.
Qed.  

Lemma sqrt2_div2 : (√ 2 / 2)%R = (1 / √ 2)%R.
Proof.
   field_simplify_eq; try (apply sqrt_neq_0_compat; lra).
   rewrite pow2_sqrt2; easy.
Qed.

Lemma sqrt2_inv : √ (/ 2) = (/ √ 2)%R.
Proof. apply sqrt_inv; lra. Qed.  

Lemma sqrt_sqrt_inv : forall (r : R), 0 < r -> (√ r * √ / r)%R = 1.
Proof. 
  intros. 
  rewrite sqrt_inv; trivial. 
  rewrite Rinv_r; trivial. 
  apply sqrt_neq_0_compat; easy.
Qed.

Lemma sqrt2_sqrt2_inv : (√ 2 * √ / 2)%R = 1.
Proof. apply sqrt_sqrt_inv. lra. Qed.

Lemma sqrt2_inv_sqrt2 : ((√ / 2) * √ 2)%R = 1.
Proof. rewrite Rmult_comm. apply sqrt2_sqrt2_inv. Qed.

Lemma sqrt2_inv_sqrt2_inv : ((√ / 2) * (√ / 2) = /2)%R.
Proof. 
  rewrite sqrt2_inv. field_simplify. 
  rewrite pow2_sqrt2. easy. 
  apply sqrt_neq_0_compat; lra. 
Qed.

Lemma sqrt_1_unique : forall x, 1 = √ x -> x = 1.
Proof. intros. assert (H' := H). unfold sqrt in H. destruct (Rcase_abs x).
       - apply R1_neq_R0 in H; easy. 
       - rewrite <- (sqrt_def x); try rewrite <- H'; lra.
Qed.

Lemma sqrt_eq_iff_eq_sqr (r s : R) (Hs : 0 < s) : 
  sqrt r = s <-> r = pow s 2.
Proof.
  split.
  - destruct (Rcase_abs r) as [Hr | Hr];
    [rewrite sqrt_neg_0; lra|].
    intros H.
    apply (f_equal (fun i => pow i 2)) in H.
    rewrite pow2_sqrt in H; lra.
  - intros ->.
    rewrite sqrt_pow2; lra.
Qed.

Lemma sqrt_eq_1_iff_eq_1 (r : R) :
  sqrt r = 1 <-> r = 1.
Proof.
  rewrite sqrt_eq_iff_eq_sqr by lra.
  now rewrite pow1.
Qed.

Lemma lt_ep_helper : forall (ϵ : R),
  ϵ > 0 <-> ϵ / √ 2 > 0.
Proof. intros; split; intros. 
       - unfold Rdiv. 
         apply Rmult_gt_0_compat; auto; 
           apply Rinv_0_lt_compat; apply Rlt_sqrt2_0.
       - rewrite <- (Rmult_1_r ϵ).
         rewrite <- (Rinv_l (√ 2)), <- Rmult_assoc.
         apply Rmult_gt_0_compat; auto. 
         apply Rlt_sqrt2_0.
         apply sqrt2_neq_0.
Qed.

Lemma pow2_mono_le_inv a b : 0 <= b -> a^2 <= b^2 -> a <= b.
Proof.
  intros Hb Hab.
  destruct (Rlt_le_dec a 0); [lra|].
  simpl in *.
  rewrite 2!Rmult_1_r in *.
  destruct (Rlt_le_dec b a); [|easy].
  pose proof (Rmult_lt_compat_l a b a).
  pose proof (Rmult_le_compat b a b b).
  lra.
Qed.  

Lemma sqrt_ge a b : 
  a^2 <= b -> a <= √ b.
Proof.
  intros Hab.
  pose proof (pow2_ge_0 a).
  apply pow2_mono_le_inv.
  - apply sqrt_pos.
  - rewrite pow2_sqrt by lra.
    easy.
Qed.

Lemma sqrt_ge_abs a b : 
  a^2 <= b -> Rabs a <= √ b.
Proof.
  intros Hab.
  apply sqrt_ge.
  now rewrite pow2_abs.
Qed.



(* Automation *)
Ltac R_field_simplify := repeat field_simplify_eq [pow2_sqrt2 sqrt2_inv].
Ltac R_field := R_field_simplify; easy.

#[export] Hint Rewrite sin_0 sin_PI4 sin_PI2 sin_PI cos_0 cos_PI4 cos_PI2 
             cos_PI sin_neg cos_neg : trig_db.

(** * glb support *) 

Definition is_lower_bound (E:R -> Prop) (m:R) := forall x:R, E x -> m <= x.

Definition bounded_below (E:R -> Prop) := exists m : R, is_lower_bound E m.

Definition is_glb (E:R -> Prop) (m:R) :=
  is_lower_bound E m /\ (forall b:R, is_lower_bound E b -> b <= m).

Definition neg_Rset (E : R -> Prop) :=
  fun r => E (-r).

Lemma lb_negset_ub : forall (E : R -> Prop) (b : R),
  is_lower_bound E b <-> is_upper_bound (neg_Rset E) (-b).
Proof. unfold is_lower_bound, is_upper_bound, neg_Rset; split; intros.
       - apply H in H0; lra. 
       - rewrite <- Ropp_involutive in H0. 
         apply H in H0; lra.
Qed.

Lemma ub_negset_lb : forall (E : R -> Prop) (b : R),
  is_upper_bound E b <-> is_lower_bound (neg_Rset E) (-b).
Proof. unfold is_lower_bound, is_upper_bound, neg_Rset; split; intros.
       - apply H in H0; lra. 
       - rewrite <- Ropp_involutive in H0. 
         apply H in H0; lra.
Qed.

Lemma negset_bounded_above : forall (E : R -> Prop),
  bounded_below E -> (bound (neg_Rset E)).
Proof. intros. 
       destruct H.
       exists (-x).
       apply lb_negset_ub; easy.
Qed.

Lemma negset_glb : forall (E : R -> Prop) (m : R),
  is_lub (neg_Rset E) m -> is_glb E (-m).
Proof. intros.  
       destruct H; split. 
       - apply lb_negset_ub.
         rewrite Ropp_involutive; easy. 
       - intros. 
         apply lb_negset_ub in H1.
           apply H0 in H1; lra.
Qed.

Lemma glb_completeness :
  forall E:R -> Prop,
    bounded_below E -> (exists x : R, E x) -> { m:R | is_glb E m }.
Proof. intros.  
       apply negset_bounded_above in H.
       assert (H' : exists x : R, (neg_Rset E) x).
       { destruct H0; exists (-x).
         unfold neg_Rset; rewrite Ropp_involutive; easy. }
       apply completeness in H'; auto.
       destruct H' as [m [H1 H2] ].
       exists (-m).
       apply negset_glb; easy.
Qed.



(** * Showing that R is a field, and a vector space over itself *)

Global Program Instance R_is_monoid : Monoid R := 
  { Gzero := 0
  ; Gplus := Rplus
  }.
Solve All Obligations with program_simpl; try lra.

Global Program Instance R_is_group : Group R :=
  { Gopp := Ropp }.
Solve All Obligations with program_simpl; try lra.

Global Program Instance R_is_comm_group : Comm_Group R.
Solve All Obligations with program_simpl; lra. 

Global Program Instance R_is_ring : Ring R :=
  { Gone := 1
  ; Gmult := Rmult
  }.
Solve All Obligations with program_simpl; try lra. 
Next Obligation. try apply Req_EM_T. Qed.


Global Program Instance R_is_comm_ring : Comm_Ring R.
Solve All Obligations with program_simpl; lra. 
                                                     
Global Program Instance R_is_field : Field R :=
  { Ginv := Rinv }.
Next Obligation. 
  rewrite Rinv_r; easy.
Qed.

Global Program Instance R_is_module_space : Module_Space R R :=
  { Vscale := Rmult }.
Solve All Obligations with program_simpl; lra. 


Global Program Instance R_is_vector_space : Vector_Space R R.  



(** * some big_sum lemmas specific to R *)

Lemma Rsum_le : forall (f g : nat -> R) (n : nat),
  (forall i, (i < n)%nat -> f i <= g i) ->
  (big_sum f n) <= (big_sum g n).
Proof. induction n as [| n']; simpl; try lra.  
       intros.
       apply Rplus_le_compat.
       apply IHn'; intros. 
       all : apply H; try lia. 
Qed.

Lemma Rsum_ge_0 : forall (f : nat -> R) (n : nat),
  (forall i, (i < n)%nat -> 0 <= f i) ->
  0 <= big_sum f n.
Proof. induction n as [| n'].
       - intros; simpl; lra. 
       - intros. simpl; apply Rplus_le_le_0_compat.
         apply IHn'; intros; apply H; lia. 
         apply H; lia. 
Qed.

Lemma Rsum_ge_0_on (n : nat) (f : nat -> R) : 
  (forall k, (k < n)%nat -> 0 <= f k) ->
  0 <= big_sum f n.
Proof.
  induction n; [simpl; lra|].
  intros Hf.
  specialize (IHn ltac:(intros;apply Hf;lia)).
  simpl.
  specialize (Hf n ltac:(lia)).
  lra.
Qed.

Lemma Rsum_nonneg_le (n : nat) (f : nat -> R) a : 
  (forall k, (k < n)%nat -> 0 <= f k) ->
  big_sum f n <= a ->
  forall k, (k < n)%nat -> f k <= a.
Proof.
  intros Hfge0 Hle.
  induction n; [easy|].
  specialize (IHn ltac:(intros; apply Hfge0; lia)
    ltac:(simpl in Hle; specialize (Hfge0 n ltac:(lia)); lra)).
  simpl in Hle.
  pose proof (Rsum_ge_0_on n f ltac:(intros; apply Hfge0; lia)).
  intros k Hk.
  bdestruct (k =? n).
  - subst; lra.
  - apply IHn; lia.
Qed.

Lemma Rsum_nonneg_ge_any n (f : nat -> R) k (Hk : (k < n)%nat) : 
  (forall i, (i < n)%nat -> 0 <= f i) ->
  f k <= big_sum f n.
Proof.
  intros Hle.
  induction n; [easy|].
  bdestruct (k =? n).
  - subst.
    simpl.
    pose proof (Rsum_ge_0_on n f ltac:(intros;apply Hle;lia)).
    lra.
  - pose proof (Hle n ltac:(lia)).
    simpl.
    apply Rle_trans with (big_sum f n).
    + apply IHn; [lia | intros; apply Hle; lia].
    + lra.
Qed.

Lemma pos_IZR (p : positive) : IZR (Z.pos p) = INR (Pos.to_nat p).
Proof.
  induction p.
  - rewrite IZR_POS_xI.
    rewrite Pos2Nat.inj_xI.
    rewrite IHp.
    rewrite S_INR, mult_INR.
    simpl.
    lra.
  - rewrite IZR_POS_xO.
    rewrite Pos2Nat.inj_xO.
    rewrite IHp.
    rewrite mult_INR.
    simpl.
    lra.
  - reflexivity.
Qed.

Lemma INR_to_nat (z : Z) : (0 <= z)%Z ->
  INR (Z.to_nat z) = IZR z.
Proof.
  intros Hz.
  destruct z; [reflexivity| | ].
  - simpl.
    rewrite pos_IZR.
    reflexivity.
  - lia.
Qed.

(* For compatibility pre-8.18 FIXME: Remove when we deprecate those versions *)
Lemma Int_part_spec_compat : forall r z, r - 1 < IZR z <= r -> z = Int_part r.
Proof.
  unfold Int_part; intros r z [Hle Hlt]; apply Z.add_move_r, tech_up.
  - rewrite <-(Rplus_0_r r), <-(Rplus_opp_l 1), <-Rplus_assoc, plus_IZR.
    now apply Rplus_lt_compat_r.
  - now rewrite plus_IZR; apply Rplus_le_compat_r.
Qed.
Lemma Rplus_Int_part_frac_part_compat : forall r, r = IZR (Int_part r) + frac_part r.
Proof. now unfold frac_part; intros r; rewrite Rplus_minus. Qed.

Notation Rplus_Int_part_frac_part := Rplus_Int_part_frac_part_compat.
Notation Int_part_spec := Int_part_spec_compat.


Lemma lt_S_Int_part r : r < IZR (1 + Int_part r).
Proof.
  rewrite (Rplus_Int_part_frac_part r) at 1.
  rewrite Z.add_comm, plus_IZR.
  pose proof (base_fp r).
  lra.
Qed.

Lemma lt_Int_part (r s : R) : (Int_part r < Int_part s)%Z -> r < s.
Proof.
  intros Hlt.
  apply Rlt_le_trans with (IZR (Int_part s));
  [apply Rlt_le_trans with (IZR (1 + Int_part r))|].
  - apply lt_S_Int_part.
  - apply IZR_le.
    lia.
  - apply base_Int_part.
Qed.

Lemma Int_part_le (r s : R) : r <= s -> (Int_part r <= Int_part s)%Z.
Proof.
  intros Hle.
  rewrite <- Z.nlt_ge.
  intros H%lt_Int_part.
  lra.
Qed.

Lemma IZR_le_iff (z y : Z) : IZR z <= IZR y <-> (z <= y)%Z.
Proof.
  split.
  - apply le_IZR.
  - apply IZR_le.
Qed.

Lemma IZR_lt_iff (z y : Z) : IZR z < IZR y <-> (z < y)%Z.
Proof.
  split.
  - apply lt_IZR.
  - apply IZR_lt.
Qed.

Lemma Int_part_IZR (z : Z) : Int_part (IZR z) = z.
Proof.
  symmetry.
  apply Int_part_spec.
  change 1 with (INR (Pos.to_nat 1)).
  rewrite <- pos_IZR, <- minus_IZR.
  rewrite IZR_le_iff, IZR_lt_iff.
  lia.
Qed.

Lemma Int_part_ge_iff (r : R) (z : Z) : 
  (z <= Int_part r)%Z <-> (IZR z <= r).
Proof.
  split.
  - intros Hle.
    apply Rle_trans with (IZR (Int_part r)).
    + apply IZR_le, Hle.
    + apply base_Int_part.
  - intros Hle.
    rewrite <- (Int_part_IZR z).
    apply Int_part_le, Hle.
Qed.

Lemma Rpower_pos (b c : R) : 
  0 < Rpower b c.
Proof.
  apply exp_pos.
Qed.

Lemma ln_nondecreasing x y : 0 < x ->
  x <= y -> ln x <= ln y.
Proof.
  intros Hx [Hlt | ->]; [|right; reflexivity].
  left.
  apply ln_increasing; auto.
Qed.

Lemma ln_le_inv x y : 0 < x -> 0 < y ->
  ln x <= ln y -> x <= y.
Proof.
  intros Hx Hy [Hlt | Heq];
  [left; apply ln_lt_inv; auto|].
  right.
  apply ln_inv; auto.
Qed.


Lemma Rdiv_le_iff a b c (Hb : 0 < b) : 
  a / b <= c <-> a <= b * c.
Proof.
  split.
  - intros Hle.
    replace a with (b * (a / b)).
    2: {
      unfold Rdiv.
      rewrite <- Rmult_assoc, (Rmult_comm b a), Rmult_assoc.
      rewrite Rinv_r; lra.
    }
    apply Rmult_le_compat_l; lra.
  - intros Hle.
    apply Rle_trans with (b * c / b).
    + apply Rmult_le_compat_r.
      * enough (0 < / b) by lra.
        now apply Rinv_0_lt_compat.
      * easy.
    + rewrite Rmult_comm.
      unfold Rdiv.
      rewrite Rmult_assoc, Rinv_r; lra.
Qed.

Lemma div_Rpower_le_of_le (r b c d : R) : 
  0 < r -> 1 < b -> 0 < c -> 0 < d ->
  ln (r / d) / ln b <= c ->
  r / (Rpower b c) <= d.
Proof.
  intros Hr Hb Hc Hd Hle.
  assert (0 < Rpower b c) by apply Rpower_pos.
  rewrite Rdiv_le_iff, Rmult_comm, 
    <- Rdiv_le_iff by auto.
  apply ln_le_inv;
  [apply Rdiv_lt_0_compat; lra|auto|].
  unfold Rpower.
  rewrite ln_exp.
  rewrite Rmult_comm.
  rewrite <- Rdiv_le_iff; [auto|].
  rewrite <- ln_1.
  apply ln_increasing; lra.
Qed.

Lemma Rpow_pos n x : 0 <= x -> 0 <= x ^ n.
Proof.
  intros Hx.
  induction n; [lra|].
  simpl.
  replace 0 with (0 * 0) by lra.
  apply Rmult_le_compat; lra.
Qed.

Lemma Rpow_le_compat_r n x y : 0 <= x ->
  x <= y -> x ^ n <= y ^ n.
Proof.
  intros Hx Hxy.
  induction n; [lra|].
  simpl.
  pose proof (Rpow_pos n x Hx).
  apply Rmult_le_compat; lra.
Qed.

Lemma Rpow_lt_compat_r n x y : n <> O -> 0 <= x ->
  x < y -> x ^ n < y ^ n.
Proof.
  intros Hn Hx Hxy.
  induction n; [easy|].
  destruct n; [lra|].
  simpl in *.
  specialize (IHn ltac:(easy)).
  apply Rle_lt_trans with (y * (x * x ^ n)).
  - pose proof (Rpow_pos (S n) x Hx); simpl in *.
    apply Rmult_le_compat_r; lra.
  - apply Rmult_lt_compat_l; lra.
Qed.
