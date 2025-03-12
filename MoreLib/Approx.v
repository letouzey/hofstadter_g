From Coq Require Import Reals Lra.
From Coq Require Export QArith Qreals Qminmax Qabs.
Close Scope Q. (* Issue with QArith. *)
Local Open Scope Q.
Require Import MoreReals.
Local Open Scope Z.
Local Open Scope R.

(** * Approx : A little real approximation library *)

(** Complements on rationals : Qsign, Qmax4, Qmin4 *)

Definition Qsgn q := Z.sgn q.(Qnum).

Lemma Qsgn_pos q : Qsgn q = 1%Z <-> (0 < q)%Q.
Proof.
 now destruct q as ([ ],?).
Qed.

Lemma Qsgn_neg q : Qsgn q = (-1)%Z <-> (q < 0)%Q.
Proof.
 now destruct q as ([ ],?).
Qed.

Definition Qmin4 a b c d := Qmin (Qmin a b) (Qmin c d).
Definition Qmax4 a b c d := Qmax (Qmax a b) (Qmax c d).

Lemma Qmin4_ok a b c d :
  let m := Qmin4 a b c d in (m <= a /\ m <= b /\ m <= c /\ m <= d)%Q.
Proof.
 set (m := Qmin4 a b c d). unfold Qmin4 in *.
 assert (LE : (m <= Qmin a b)%Q) by apply Q.le_min_l.
 assert (LE' : (m <= Qmin c d)%Q) by apply Q.le_min_r.
 repeat split.
 apply Qle_trans with (Qmin a b); auto. apply Q.le_min_l.
 apply Qle_trans with (Qmin a b); auto. apply Q.le_min_r.
 apply Qle_trans with (Qmin c d); auto. apply Q.le_min_l.
 apply Qle_trans with (Qmin c d); auto. apply Q.le_min_r.
Qed.

Lemma Qmax4_ok a b c d :
  let m := Qmax4 a b c d in (a <= m /\ b <= m /\ c <= m /\ d <= m)%Q.
Proof.
 set (m := Qmax4 a b c d). unfold Qmax4 in *.
 assert (LE : (Qmax a b <= m)%Q) by apply Q.le_max_l.
 assert (LE' : (Qmax c d <= m)%Q) by apply Q.le_max_r.
 repeat split.
 apply Qle_trans with (Qmax a b); auto. apply Q.le_max_l.
 apply Qle_trans with (Qmax a b); auto. apply Q.le_max_r.
 apply Qle_trans with (Qmax c d); auto. apply Q.le_max_l.
 apply Qle_trans with (Qmax c d); auto. apply Q.le_max_r.
Qed.

Definition Qsqrt '(Qmake n d) := Qmake (Z.sqrt (n * Zpos d)) d.
Definition Qsqrt_up '(Qmake n d) := Qmake (Z.sqrt_up (n * Zpos d)) d.

Lemma Qsqrt_ok q : ((Qsqrt q)^2 <= Qmax 0 q)%Q.
Proof.
 destruct q as (n,d).
 destruct (Z.lt_ge_cases n Z0).
 - now destruct n.
 - rewrite Q.max_r by now destruct n. unfold Qle. simpl.
   rewrite Pos2Z.inj_mul, Z.mul_assoc. apply Z.mul_le_mono_nonneg_r; try easy.
   apply Z.sqrt_spec. now apply Z.mul_nonneg_nonneg.
Qed.

Lemma Qsqrt_up_ok q : (Qmax 0 q <= (Qsqrt_up q)^2)%Q.
Proof.
 destruct q as (n,d).
 destruct (Z.le_gt_cases n Z0).
 - now destruct n.
 - rewrite Q.max_r by now destruct n. unfold Qle. simpl.
   rewrite Pos2Z.inj_mul, Z.mul_assoc. apply Z.mul_le_mono_nonneg_r; try easy.
   apply Z.sqrt_up_spec. now apply Z.mul_pos_pos.
Qed.

(** Deciding comparison on Q *)

Lemma Qle_bool_nimp_lt (x y:Q) : Qle_bool y x = false -> (x < y)%Q.
Proof.
 intro E. apply Qnot_le_lt. intro LE. rewrite <- Qle_bool_iff in LE.
 now rewrite E in LE.
Qed.

Lemma Qpos_or_neg (x y:Q) :
 Z.eqb (Qsgn x) 1%Z || Z.eqb (Qsgn y) (-1)%Z = true ->
 (0 < x \/ y < 0)%Q.
Proof.
 case Z.eqb_spec; simpl. rewrite Qsgn_pos; now left.
 intros _. rewrite Z.eqb_eq, Qsgn_neg. now right.
Qed.

Ltac qle := apply Qle_bool_imp_le; vm_compute; reflexivity.
Ltac qlt := apply Qle_bool_nimp_lt; vm_compute; reflexivity.
Ltac qposneg := apply Qpos_or_neg; vm_compute; reflexivity.

#[global] Hint Extern 3 (Qle _ _) => qle : typeclass_instances.
#[global] Hint Extern 3 (Qlt _ _) => qlt : typeclass_instances.
#[global] Hint Extern 3 (Qlt _ _ \/ Qlt _ _) => qposneg : typeclass_instances.


(** The class of approximation *)

Class Approx (low:Q)(r:R)(high:Q) := the_approx : Q2R low <= r <= Q2R high.

#[global] Instance Q2R_approx q : Approx q (Q2R q) q.
Proof. red. lra. Qed.

#[global] Instance IZR_approx z : Approx (inject_Z z) (IZR z) (inject_Z z).
Proof. rewrite <- Q2R_IZR. typeclasses eauto. Qed.

#[global] Instance INR_approx n :
  Approx (inject_Z (Z.of_nat n)) (INR n) (inject_Z (Z.of_nat n)).
Proof. rewrite INR_IZR_INZ. typeclasses eauto. Qed.

#[global] Instance plus_approx {a r b a' r' b'} :
  Approx a r b -> Approx a' r' b' -> Approx (a+a') (r+r') (b+b').
Proof.
 unfold Approx. intros. rewrite !Q2R_plus. lra.
Qed.

#[global] Instance opp_approx {a r b} :
  Approx a r b -> Approx (-b) (-r) (-a).
Proof.
 unfold Approx. intros. rewrite !Q2R_opp. lra.
Qed.

#[global] Instance minus_approx {a r b a' r' b'} :
  Approx a r b -> Approx a' r' b' -> Approx (a-b') (r-r') (b-a').
Proof.
 intros. unfold Qminus, Rminus. typeclasses eauto.
Qed.

#[global] Instance mult_approx {a r b a' r' b'} :
  Approx a r b -> Approx a' r' b' -> (0 <= a)%Q -> (0 <= a')%Q ->
  Approx (a*a') (r*r') (b*b').
Proof.
 unfold Approx. intros A A' LE LE'. rewrite !Q2R_mult.
 apply Qle_Rle in LE,LE'. split; apply Rmult_le_compat; lra.
Qed.

Definition Qmult_lb a b a' b' := Qmin4 (a*a') (a*b') (b*a') (b*b').
Definition Qmult_ub a b a' b' := Qmax4 (a*a') (a*b') (b*a') (b*b').

#[global] Instance mult_approx_gen {a r b a' r' b'} :
  Approx a r b -> Approx a' r' b' ->
  Approx (Qmult_lb a b a' b') (r*r') (Qmult_ub a b a' b').
Proof.
 unfold Approx. intros A A'. unfold Qmult_lb, Qmult_ub. split.
 - generalize (Qmin4_ok (a*a') (a*b') (b*a') (b*b')).
   set (m := Qmin4 _ _ _ _). cbn. intros (LE1 & LE2 & LE3 &LE4).
   clearbody m.
   apply Qle_Rle in LE1,LE2,LE3,LE4. rewrite !Q2R_mult in *.
   generalize (Rmult_ge_lowerbound _ _ _ _ _ _ A A'). lra.
 - generalize (Qmax4_ok (a*a') (a*b') (b*a') (b*b')).
   set (m := Qmax4 _ _ _ _). cbn. intros (LE1 & LE2 & LE3 &LE4).
   clearbody m.
   apply Qle_Rle in LE1,LE2,LE3,LE4. rewrite !Q2R_mult in *.
   generalize (Rmult_le_upperbound _ _ _ _ _ _ A A'). lra.
Qed.

Definition Qpow_lb a b n :=
  if Nat.eqb n 0 || Nat.odd n then (a^Z.of_nat n)%Q
  else if Z.eqb (Qsgn a) (-1) && Z.eqb (Qsgn b) 1 then 0%Q
  else Qmin (a^Z.of_nat n) (b^Z.of_nat n).

Definition Qpow_ub a b n := Qmax (a^Z.of_nat n) (b^Z.of_nat n).

#[global] Instance pow_approx {a r b} (n:nat) :
  Approx a r b -> Approx (Qpow_lb a b n) (r^n) (Qpow_ub a b n).
Proof.
 unfold Approx. intros A.
 destruct (Nat.eqb n 0) eqn:ZE.
 { rewrite Nat.eqb_eq in ZE. subst n. unfold Qpow_lb, Qpow_ub; cbn. lra. }
 unfold Qpow_lb. rewrite ZE.
 destruct (Nat.odd n) eqn:OD; cbn.
 - (* n odd *)
   rewrite Nat.odd_spec in OD.
   unfold Qpow_ub. rewrite Q.max_r.
   + rewrite !Q2R_pow. split; apply pow_incr_odd; trivial; lra.
   + apply Rle_Qle. rewrite !Q2R_pow. apply pow_incr_odd; trivial; lra.
 - (* n even *)
   rewrite <- Nat.negb_even in OD.
   assert (EV : Nat.even n = true) by now destruct Nat.even.
   rewrite Nat.even_spec in EV. clear OD.
   case Z.eqb_spec; simpl; intros Ha.
   + rewrite Qsgn_neg in Ha.
     case Z.eqb_spec; simpl; intros Hb.
     * rewrite Qsgn_pos in Hb.
       split. replace (Q2R 0) with 0 by lra. now apply pow_even_nonneg.
       destruct (Rle_lt_dec 0 r).
       { apply Rle_trans with (Q2R (b^Z.of_nat n)).
         - rewrite Q2R_pow. apply pow_incr; lra.
         - apply Qle_Rle. apply Q.le_max_r. }
       { apply Rle_trans with (Q2R (a^Z.of_nat n)).
         - rewrite Q2R_pow. apply pow_decr_even_neg; auto. lra.
         - apply Qle_Rle. apply Q.le_max_l. }
     * rewrite Qsgn_pos in Hb. apply Qnot_lt_le in Hb. apply Qle_Rle in Hb.
       rewrite Q.min_r. unfold Qpow_ub. rewrite Q.max_l.
       rewrite !Q2R_pow. split; apply pow_decr_even_neg; trivial; lra.
       apply Rle_Qle. rewrite !Q2R_pow.
       apply pow_decr_even_neg; trivial; lra.
       apply Rle_Qle. rewrite !Q2R_pow.
       apply pow_decr_even_neg; trivial; lra.
   + rewrite Qsgn_neg in Ha. apply Qnot_lt_le in Ha. apply Qle_Rle in Ha.
     rewrite Q.min_l. unfold Qpow_ub. rewrite Q.max_r.
     rewrite !Q2R_pow. split; apply pow_incr; lra.
     apply Rle_Qle. rewrite !Q2R_pow. apply pow_incr; lra.
     apply Rle_Qle. rewrite !Q2R_pow. apply pow_incr; lra.
Qed.

#[global] Instance inv_approx {a r b} :
  Approx a r b -> (0 < a \/ b < 0)%Q -> Approx (/b) (/r) (/a).
Proof.
 unfold Approx. intros A [LT|LT]; apply Qlt_Rlt in LT.
 - rewrite !Q2R_inv by (intro E; rewrite E in *; lra).
   split; apply Rinv_le_contravar; lra.
 - rewrite !Q2R_inv by (intro E; rewrite E in *; lra).
   split; apply Ropp_le_cancel; rewrite <- !Rinv_opp;
    apply Rinv_le_contravar; lra.
Qed.

#[global] Instance div_approx {a r b a' r' b'} :
  Approx a r b -> Approx a' r' b' -> (0 <= a)%Q -> (0 < a')%Q ->
  Approx (a/b') (r/r') (b/a').
Proof.
 unfold Rdiv, Qdiv. intros A A' LE LT.
 apply mult_approx; trivial. apply inv_approx; auto.
 clear A LE. red in A'. apply Rle_Qle. apply Qlt_Rlt in LT.
 rewrite !Q2R_inv by (intro E; rewrite E in *; lra).
 assert (Hb : 0 < Q2R b') by lra.
 apply Rinv_0_lt_compat in Hb. lra.
Qed.

Definition Qabs_lb a b :=
  if Z.eqb (Qsgn a) (-1) && Z.eqb (Qsgn b) 1 then 0%Q
  else Qmin (Qabs a) (Qabs b).

Definition Qabs_ub a b := Qmax (Qabs a) (Qabs b).

#[global] Instance abs_approx {a r b} :
  Approx a r b -> Approx (Qabs_lb a b) (Rabs r) (Qabs_ub a b).
Proof.
 unfold Approx. intros A. split.
 - unfold Qabs_lb.
   case Z.eqb_spec; simpl; intros Ha.
   + rewrite Qsgn_neg in Ha.
     case Z.eqb_spec; simpl; intros Hb.
     * replace (Q2R 0) with 0 by lra. apply Rabs_pos.
     * rewrite Qsgn_pos in Hb. apply Qnot_lt_le in Hb.
       apply Qle_Rle in Hb. clear Ha.
       rewrite Q.min_r.
       2:{ rewrite !Qabs_neg; apply Rle_Qle; rewrite ?Q2R_opp; lra. }
       rewrite Qabs_neg; try apply Rle_Qle; rewrite ?Q2R_opp; try lra.
       rewrite Rabs_left'; lra.
   + rewrite Qsgn_neg in Ha. apply Qnot_lt_le in Ha.
     apply Qle_Rle in Ha.
     rewrite Q.min_l.
     2:{ rewrite !Qabs_pos; apply Rle_Qle; lra. }
     rewrite Qabs_pos; try apply Rle_Qle; try lra.
     rewrite Rabs_right; lra.
 - unfold Qabs_ub.
   destruct (Rle_lt_dec 0 r).
   + rewrite Rabs_right by lra.
     rewrite (Qabs_pos b) by (apply Rle_Qle; lra).
     apply Rle_trans with (Q2R b); try lra.
     apply Qle_Rle. apply Q.le_max_r.
   + rewrite Rabs_left by lra.
     rewrite (Qabs_neg a) by (apply Rle_Qle; lra).
     apply Rle_trans with (Q2R (-a)). rewrite Q2R_opp; lra.
     apply Qle_Rle. apply Q.le_max_l.
Qed.

Lemma approx_trans {a a' r b b'} :
 Approx a r b -> (a'<=a)%Q -> (b<=b')%Q -> Approx a' r b'.
Proof.
 unfold Approx. intros A LE LE'. apply Qle_Rle in LE,LE'. lra.
Qed.

Lemma pow2_approx_inv {a r b} :
  Approx (a^2) (r^2) (b^2) -> (0 <= a)%Q -> 0 <= r -> (0 <= b)%Q ->
  Approx a r b.
Proof.
 unfold Approx. intros p Ha Hr Hb.
 apply Qle_Rle in Ha,Hb. rewrite !Q2R_pow2 in p.
 rewrite <- !Rsqr_pow2 in p.
 split; apply Rsqr_incr_0; lra.
Qed.

#[global] Instance sqrt_approx {a r b} :
 Approx a r b -> Approx (Qsqrt a) (sqrt r) (Qsqrt_up b).
Proof.
 intros. apply pow2_approx_inv; try apply sqrt_pos.
 2:{ now destruct a as [[]]. }
 2:{ destruct b as [[] ]; unfold Qle; simpl; try easy.
     rewrite Z.mul_1_r. apply Z.sqrt_up_nonneg. }
 destruct (Rle_lt_dec r 0).
 - rewrite sqrt_neg_0 by trivial. simpl pow at 1; rewrite Rmult_0_l.
   destruct H as (H,H'). replace 0 with (Q2R 0) in * by lra. split.
   + apply Qle_Rle.
     rewrite <- (Q.max_l 0 a). apply Qsqrt_ok. apply Rle_Qle. lra.
   + apply Qle_Rle. apply Q.max_lub_l with b. apply Qsqrt_up_ok.
 - rewrite pow2_sqrt by lra. destruct H as (H,H'). split.
   + apply Rle_trans with (Q2R (Qmax 0 a)). apply Qle_Rle, Qsqrt_ok.
     apply Q.max_case; try lra. now intros x y ->.
   + apply Rle_trans with (Q2R (Qmax 0 b)). 2:apply Qle_Rle, Qsqrt_up_ok.
     apply Rle_trans with (Q2R b); trivial. apply Qle_Rle, Q.le_max_r.
Qed.

Ltac approxim r :=
  let A := fresh in
  assert (A : Approx _ r _) by once (typeclasses eauto 20);
  revert A.

Ltac approx :=
 match goal with
 | |- Approx _ _ _ => eapply approx_trans; once (typeclasses eauto 20)
 | |- ?r <= ?r' =>
   let H := fresh in let H' := fresh in
   approxim r; intros (_,H); approxim r'; intros (H',_);
   eapply Rle_trans; [exact H| ]; eapply Rle_trans; [ |exact H'];
   apply Qle_Rle; qle
 | |- ?r < ?r' =>
   let H := fresh in let H' := fresh in
   approxim r; intros (_,H); approxim r'; intros (H',_);
   eapply Rle_lt_trans; [exact  H| ]; eapply Rlt_le_trans; [ |exact H'];
   apply Qlt_Rlt; qlt
 | |- ?r >= ?r' => apply Rle_ge; approx
 | |- ?r > ?r' => apply Rlt_gt; approx
 | |- ?r <> ?r' =>
   apply Rlt_dichotomy_converse; (left; approx)||(right; approx)
 | |- ?r = ?r' -> False => change (r<>r'); approx
 | |- _ /\ _ => split; approx
 end.

(* When used interactively, let's rather compute the Q numbers at once *)
Ltac approximate r :=
  approxim r;
  match goal with |- Approx ?a ?r ?b -> ?g =>
    let a' := (eval vm_compute in a) in
    let b' := (eval vm_compute in b) in
    change (Approx a' r b' -> g)
  end.
