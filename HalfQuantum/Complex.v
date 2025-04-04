(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either 
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.

---------------------------------------------------------------

This version modified to work without SSReflect,
or any other dependencies, as part of the QWIRE project
by Robert Rand and Jennifer Paykin (June 2017).

---------------------------------------------------------------

Additional lemmas added as part of work on projects in inQWIRE 
(https://github.com/inQWIRE) 2019-2021.

---------------------------------------------------------------
Re-merged with Coquelicot.Complex (and minimized) by P. Letouzey (April 2025)

*)

Require Export Prelim. 
Require Export RealAux.
Require Export Summation. 
From Coquelicot Require Export Complex.
(* Fix the lack of proper bullets in Coquelicot, inherited from math-comp *)
Global Set Bullet Behavior "Strict Subproofs".
Local Open Scope R.
Local Open Scope C.

Module Compat.
Notation C0 := (RtoC 0) (only parsing).
Notation C1 := (RtoC 1) (only parsing).
Notation C2 := (RtoC 2) (only parsing).
Notation C1_neq_C0 := C1_nz (only parsing).
Notation Cpow_mul_l := Cpow_mult_l (only parsing).
End Compat.
Import Compat.

(* lca, a great tactic for solving computations or basic equality checking *)
Lemma c_proj_eq : forall (c1 c2 : C), fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.  
Proof. intros c1 c2 H1 H2. destruct c1, c2. simpl in *. subst. reflexivity. Qed.

(* essentially, we just bootsrap coq's lra *)
Ltac lca := eapply c_proj_eq; simpl; lra.

(** * Showing that C is a field, and a vector space over itself *)
            
Global Program Instance C_is_monoid : Monoid C := 
  { Gzero := 0
  ; Gplus := Cplus
  }.
Solve All Obligations with program_simpl; try lca.

Global Program Instance C_is_group : Group C :=
  { Gopp := Copp }.
Solve All Obligations with program_simpl; try lca.
        
Global Program Instance C_is_comm_group : Comm_Group C.
Solve All Obligations with program_simpl; lca. 
                                             
Global Program Instance C_is_ring : Ring C :=
  { Gone := 1
  ; Gmult := Cmult
  }.
Solve All Obligations with program_simpl; try lca; apply Ceq_dec. 

Global Program Instance C_is_comm_ring : Comm_Ring C.
Solve All Obligations with program_simpl; lca. 

Global Program Instance C_is_field : Field C :=
  { Ginv := Cinv }.
Next Obligation.
  assert (H := R1_neq_R0).
  contradict H.  
  apply (f_equal_gen fst fst) in H; simpl in H; easy. 
Qed.
Next Obligation.
  apply injective_projections ; simpl ; field; 
  contradict H; apply Rplus_sqr_eq_0 in H;
  apply injective_projections ; simpl ; apply H.
Qed.

Global Program Instance C_is_module_space : Module_Space C C :=
  { Vscale := Cmult }.
Solve All Obligations with program_simpl; lca. 

Global Program Instance C_is_vector_space : Vector_Space C C.



(** *** Other usual functions *)

Notation "a ^*" := (Cconj a) (at level 10) : C_scope.

Lemma Cmod_ge_fst z : 
  fst z <= Cmod z.
Proof.
  unfold Cmod.
  apply sqrt_ge.
  pose proof (pow2_ge_0 (snd z)).
  lra.
Qed.

Lemma Cmod_ge_snd z : 
  snd z <= Cmod z.
Proof.
  unfold Cmod.
  apply sqrt_ge.
  pose proof (pow2_ge_0 (fst z)).
  lra.
Qed.

Lemma C_neq_iff : forall c d : C, c <> d <-> (fst c <> fst d \/ snd c <> snd d).
Proof.
  intros [cr ci] [dr di].
  split.
  - intros Hne.
    destruct (Req_dec cr dr); [|now left].
    destruct (Req_dec ci di); [|now right].
    subst; easy.
  - simpl.
    intros []; congruence.
Qed.

Lemma C_neq_0 : forall c : C, c <> 0 -> (fst c) <> 0 \/ (snd c) <> 0.
Proof.
  intros c.
  apply C_neq_iff.
Qed.

Lemma Cinv_0 : / 0 = 0.
Proof.
  lca.
Qed.

Lemma Cdiv_0_r z : z / 0 = 0.
Proof.
  lca.
Qed.

(* some lemmas to help simplify addition/multiplication scenarios *)
Lemma Cplus_simplify : forall (a b c d : C),
    a = b -> c = d -> (a + c = b + d)%C.
Proof. intros. 
       rewrite H, H0; easy.
Qed.

Lemma Cmult_simplify : forall (a b c d : C),
    a = b -> c = d -> (a * c = b * d)%C.
Proof. intros. 
       rewrite H, H0; easy.
Qed.

(** ** C is a field *)

Lemma RtoC_inv (x : R) : RtoC (/ x) = / RtoC x.
Proof. destruct (Req_dec x 0).
  - subst; now rewrite Cinv_0, Rinv_0.
  - apply injective_projections ; simpl ; field ; auto. 
Qed.

Lemma RtoC_div (x y : R) : RtoC (x / y) = RtoC x / RtoC y.
Proof. destruct (Req_dec y 0).
  - subst; unfold Rdiv; now rewrite Cdiv_0_r, Rinv_0, Rmult_0_r.
  - apply injective_projections ; simpl ; field ; auto. 
Qed.

Lemma Cdiv_mult_r (c d : C) : d <> 0%R ->
  c / d * d = c.
Proof.
  intros.
  unfold Cdiv.
  rewrite <- Cmult_assoc, Cinv_l by easy.
  apply Cmult_1_r.
Qed.

Lemma Cdiv_mult_l (c d : C) : d <> 0%R ->
  d * c / d = c.
Proof.
  intros.
  unfold Cdiv.
  rewrite (Cmult_comm d c), <- Cmult_assoc, (Cmult_comm d), Cmult_assoc.
  apply Cdiv_mult_r.
  easy.
Qed.

Lemma Cdiv_mult_l' (c d : C) : d <> 0%R ->
  d * (c / d) = c.
Proof.
  intros.
  rewrite Cmult_comm.
  apply Cdiv_mult_r.
  easy.
Qed.

Lemma Cdiv_1_r : forall c, c / 1 = c.
Proof. intros. lca. Qed.

Lemma Cmod_real : forall (c : C), 
  fst c >= 0 -> snd c = 0 -> Cmod c = fst c. 
Proof. intros. 
       unfold Cmod. 
       rewrite H0.
       simpl. 
       autorewrite with R_db.
       apply sqrt_square.
       lra. 
Qed.

Lemma Cmod_eq_0_iff x : Cmod x = 0 <-> x = 0.
Proof.
  split; [apply Cmod_eq_0|intros ->; apply Cmod_0].
Qed.

Lemma Cmod_eq_C0_iff x : @eq C (Cmod x) 0 <-> x = 0.
Proof.
  split; [intros H; apply Cmod_eq_0
  |intros ->; now rewrite Cmod_0].
  apply (f_equal fst) in H.
  apply H.
Qed.

Lemma Cmod_real_abs z : snd z = 0 -> Cmod z = Rabs (fst z).
Proof.
  intros Hreal.
  unfold Cmod.
  rewrite Hreal.
  rewrite Rpow_0_l, Rplus_0_r by easy.
  rewrite <- pow2_abs.
  now rewrite sqrt_pow2 by (apply Rabs_pos).
Qed.

Lemma Cmult_integral : forall c1 c2 : C, c1 * c2 = 0 -> c1 = 0 \/ c2 = 0.
Proof. intros. 
       destruct (Ceq_dec c1 0); try (left; easy).
       destruct (Ceq_dec c2 0); try (right; easy).
       apply (Cmult_neq_0 c1 c2) in n0; auto.
       easy. 
Qed.

Lemma Cmult_integral_iff (a b : C) : 
  a * b = 0 <-> (a = 0 \/ b = 0).
Proof.
  split; [apply Cmult_integral|].
  intros [-> | ->]; lca.
Qed.

Lemma Cminus_diag : forall r1 r2, r1 = r2 -> r1 - r2 = 0.
Proof. intros; subst; lca. 
Qed.


Lemma Cminus_eq_0 : forall r1 r2 : C, r1 - r2 = 0 -> r1 = r2.
Proof. intros.
       apply injective_projections; 
         apply Rminus_diag_uniq. 
       now apply (f_equal (@fst R R)) in H.
       now apply (f_equal (@snd R R)) in H.
Qed.


Lemma Cmult_cancel_l : forall a c1 c2 : C,
  a <> 0 ->
  a * c1 = a * c2 -> c1 = c2.
Proof. intros. 
       apply (f_equal_gen (Cmult (/ a)) (Cmult (/ a))) in H0; auto.
       do 2 rewrite Cmult_assoc in H0.
       rewrite Cinv_l in H0; auto.
       do 2 rewrite Cmult_1_l in H0.
       easy.
Qed.

Lemma Cmult_cancel_r : forall a c1 c2 : C,
  a <> 0 ->
  c1 * a = c2 * a -> c1 = c2.
Proof. intros. 
       apply (Cmult_cancel_l a); auto.
       rewrite Cmult_comm, H0; lca.
Qed.


(** * Content added as part of inQWIRE  **)


Lemma Ci2 : Ci * Ci = -(1). Proof. lca. Qed.
Lemma Ci2' : Ci^2 = -(1). Proof. lca. Qed.
Lemma Copp_mult_distr_r : forall c1 c2 : C, - (c1 * c2) = c1 * - c2.
Proof. intros; lca. Qed.
Lemma Copp_mult_distr_l : forall c1 c2 : C, - (c1 * c2) = - c1 * c2.
Proof. intros; lca. Qed.
Lemma Cplus_opp_l : forall c : C, - c + c = 0. Proof. intros; lca. Qed.
Lemma Cdouble : forall c : C, 2 * c = c + c. Proof. intros; lca. Qed.
Lemma Copp_involutive: forall c : C, - - c = c. Proof. intros; lca. Qed.

Lemma C0_imp : forall c : C, c <> 0 -> (fst c <> 0 \/ snd c <> 0)%R.  
Proof. intros c H. destruct c. simpl.
       destruct (Req_EM_T r 0), (Req_EM_T r0 0); subst; intuition. Qed.
Lemma C0_fst_neq : forall (c : C), fst c <> 0 -> c <> 0. 
Proof. intros c. intros N E. apply N. rewrite E. reflexivity. Qed.
Lemma C0_snd_neq : forall (c : C), snd c <> 0 -> c <> 0. 
Proof. intros c. intros N E. apply N. rewrite E. reflexivity. Qed.
Lemma RtoC_neq : forall (r : R), r <> 0 -> RtoC r <> 0. 
Proof. intros. apply C0_fst_neq. easy. Qed.

(** Other useful facts *)

Lemma Copp_neq_0_compat: forall c : C, c <> 0 -> (- c)%C <> 0.
Proof.
 intros c H.
 apply C0_imp in H as [H | H].
 apply C0_fst_neq.
 apply Ropp_neq_0_compat.
 assumption.
 apply C0_snd_neq.
 apply Ropp_neq_0_compat.
 assumption.
Qed.

Lemma C2_nonzero : RtoC 2 <> 0.
Proof.
  apply RtoC_neq.
  lra.
Qed.

Lemma Cconj_neq_0 : forall c : C, c <> 0 -> c^* <> 0.
Proof.
  intros.
  unfold Cconj.
  apply C_neq_0 in H.
  destruct H.
  - apply C0_fst_neq.
    simpl.
    assumption.
  - apply C0_snd_neq.
    simpl.
    apply Ropp_neq_0_compat.
    assumption.
Qed.

Lemma nonzero_div_nonzero : forall c : C, c <> 0 -> / c <> 0.
Proof. intros. 
       unfold not; intros. 
        assert (H' : (c * (/ c) = c * 0)%C). 
        { rewrite H0; easy. } 
        rewrite Cinv_r in H'; try easy.
        rewrite Cmult_0_r in H'.
        apply C1_neq_C0; easy.
Qed.

Lemma Cinv_eq_0_iff (a : C) : / a = 0 <-> a = 0.
Proof.
  split.
  - destruct (Ceq_dec a 0) as [? | H%nonzero_div_nonzero]; easy.
  - intros ->.
    lca.
Qed.

Lemma Cdiv_integral_iff (a b : C) : 
  a / b = 0 <-> (a = 0 \/ b = 0).
Proof.
  unfold Cdiv.
  rewrite Cmult_integral_iff, Cinv_eq_0_iff.
  reflexivity.
Qed.

Lemma Cdiv_integral (a b : C) : 
  a / b = 0 -> (a = 0 \/ b = 0).
Proof.
  rewrite Cdiv_integral_iff.
  easy.
Qed.

Lemma Cdiv_nonzero (c d : C) : c <> 0 -> d <> 0 ->
  c / d <> 0.
Proof.
  intros Hc Hd Hf; apply Hc.
  apply (f_equal (Cmult d)) in Hf.
  rewrite Cdiv_mult_l' in Hf; [|easy].
  rewrite Hf.
  lca.
Qed.

Lemma div_real : forall (c : C),
  snd c = 0 -> snd (/ c) = 0.
Proof. intros. 
       unfold Cinv. 
       simpl. 
       rewrite H. lra. 
Qed.

Lemma Cinv_mult : forall c1 c2 : C, / (c1 * c2) = / c1 * / c2.
Proof.
  intros.
  destruct (Ceq_dec c1 0) as [?|H]; 
    [subst; now rewrite Cmult_0_l, !Cinv_0, Cmult_0_l|].
  destruct (Ceq_dec c2 0) as [?|H0]; 
    [subst; now rewrite Cmult_0_r, !Cinv_0, Cmult_0_r|].
  now field.
Qed.

Lemma Cinv_inv : forall c : C, / / c = c.
Proof.
  intros.
  destruct (Ceq_dec c 0).
  - subst. now rewrite 2!Cinv_0.
  - now field.
Qed.

Lemma Cconj_eq_implies_real : forall c : C, c = Cconj c -> snd c = 0%R.
Proof. intros. 
       unfold Cconj in H.
       apply (f_equal snd) in H.
       simpl in H.
       assert (H' : (2 * snd c = 0)%R).
       replace (2 * snd c)%R with (snd c + (- snd c))%R by lra.
       lra.
       replace (snd c) with (/2 * (2 * snd c))%R by lra.
       rewrite H'; lra.
Qed.

(** * some C big_sum specific lemmas *)

Local Open Scope nat_scope. 

Lemma Rsum_big_sum : forall n (f : nat -> R),
  fst (big_sum (fun i => RtoC (f i)) n) = big_sum f n.
Proof.
  intros. induction n.
  - easy.
  - simpl. rewrite IHn.
    easy. 
Qed.

Lemma Re_big_sum (n : nat) (f : nat -> C) : 
  fst (big_sum (fun i => f i) n) = big_sum (fun i => fst (f i)) n.
Proof.
  induction n; [easy|].
  simpl; f_equal; easy.
Qed. 

Lemma Im_big_sum (n : nat) (f : nat -> C) : 
  snd (big_sum (fun i => f i) n) = big_sum (fun i => snd (f i)) n.
Proof.
  induction n; [easy|].
  simpl; f_equal; easy.
Qed.

Local Close Scope nat_scope.

Lemma big_sum_ge_0 : forall f n, (forall x, 0 <= fst (f x)) -> (0 <= fst (big_sum f n))%R.
Proof.
  intros f n H.
  induction n.
  - simpl. lra. 
  - simpl in *.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat; easy.
Qed.

Lemma big_sum_Cmod_0_all_0 : forall (f : nat -> C) (n : nat),
  big_sum (fun i => Cmod (f i)) n = 0 -> 
  forall i, (i < n)%nat -> f i = 0.
Proof. induction n as [| n']; try nia.   
       intros; simpl in H.
       assert (H' := H).
       rewrite Rplus_comm in H; apply Rplus_eq_0_l in H. 
       apply Rplus_eq_0_l in H'.
       all : try apply Rsum_ge_0; intros.
       all : try apply Cmod_ge_0.
       bdestruct (i <? n')%nat.
       - apply IHn'; easy. 
       - bdestruct (i =? n')%nat; try lia; subst. 
         apply Cmod_eq_0; try easy.
Qed.

Lemma big_sum_triangle : forall f n,
  Cmod (big_sum f n) <= big_sum (fun i => Cmod (f i)) n.
Proof. induction n as [| n'].
       - simpl. rewrite Cmod_0; lra.
       - simpl.
         eapply Rle_trans; try apply Cmod_triangle.
         apply Rplus_le_compat_r.
         easy. 
Qed. 

(** * Lemmas about Cpow *)

Lemma Re_Cpow (c : C) (Hc : snd c = 0) n : 
  fst (Cpow c n) = pow (fst c) n.
Proof.
  induction n; [easy|].
  simpl.
  rewrite Hc, IHn.
  lra.
Qed.

Lemma Cpow_nonzero_real : forall (r : R) (n : nat), (r <> 0 -> r ^ n <> 0)%C.
Proof.
  intros.
  rewrite <- RtoC_pow. 
  apply C0_fst_neq. 
  apply pow_nonzero. 
  lra.
Qed.

Lemma Cpow_0_l : forall n, n <> O -> 0 ^ n = 0.
Proof.
  intros n.
  destruct n; [easy|].
  simpl.
  rewrite Cmult_0_l.
  reflexivity.
Qed.

Lemma Cpow_add : forall (c : C) (n m : nat), (c ^ (n + m) = c^n * c^m)%C.
Proof.
  intros. induction n. simpl. lca.
  simpl. rewrite IHn. lca.
Qed.

(** * Lemmas about Cmod *)

Lemma Cmod_real_pos :
  forall x : C,
    snd x = 0 ->
    fst x >= 0 ->
    x = Cmod x.
Proof.
  intros. 
  unfold Cmod. 
  rewrite H. 
  replace (fst x ^ 2 + 0 ^ 2)%R with (fst x ^ 2)%R by lra. 
  rewrite sqrt_pow2 by lra.
  destruct x; simpl in *.
  rewrite H.
  reflexivity.
Qed.

Lemma Cmod_sqr : forall c : C, (Cmod c ^2 = c^* * c)%C.
Proof.
  intro.
  rewrite <- RtoC_pow.
  simpl.
  rewrite Rmult_1_r.
  rewrite <- Cmod_conj at 1. 
  rewrite <- Cmod_mult.
  rewrite Cmod_real_pos; auto.
  destruct c. simpl. lra.
  destruct c. simpl. nra.
Qed.

Lemma Cmod_switch : forall (a b : C),
  Cmod (a - b) = Cmod (b - a).
Proof. intros. 
       replace (b - a) with (- (a - b)) by lca. 
       rewrite Cmod_opp; easy.
Qed.

Lemma Cmod_triangle_le : forall (a b : C) (ϵ : R),
  Cmod a + Cmod b < ϵ -> Cmod (a + b) < ϵ.
Proof. intros. 
       assert (H0 := Cmod_triangle a b).
       lra. 
Qed.

Lemma Cmod_triangle_diff : forall (a b c : C) (ϵ : R),
  Cmod (c - b) + Cmod (b - a) < ϵ -> Cmod (c - a) < ϵ.
Proof. intros. 
       replace (c - a) with ((c - b) + (b - a)) by lca. 
       apply Cmod_triangle_le.
       easy. 
Qed.

(** * Lemmas about Cconj *)

Lemma Cconj_R : forall r : R, r^* = r.         Proof. intros; lca. Qed.
Lemma Cconj_0 : 0^* = 0.                  Proof. lca. Qed.
Lemma Cconj_rad2 : (/ √2)^* = / √2.       Proof. lca. Qed.
Lemma Cplus_div2 : /2 + /2 = 1.           Proof. lca. Qed.

Lemma Cinv_Cconj : forall c : C, (/ (c ^*) = (/ c) ^*)%C.
Proof. intros. 
       unfold Cinv, Cconj; simpl.
       apply c_proj_eq; simpl; try lra.
       apply f_equal. lra.
       (* this is just Ropp_div or Ropp_div_l, depending on Coq version *) 
       assert (H' : forall x y : R, (- x / y)%R = (- (x / y))%R).
       { intros. lra. }
       rewrite <- H'.
       apply f_equal. lra.
Qed.
                                    
Lemma Cmult_conj_real : forall (c : C), snd (c * c^*) = 0.
Proof.
  intros c.
  unfold Cconj.
  unfold Cmult.
  simpl.
  rewrite <- Ropp_mult_distr_r.
  rewrite Rmult_comm.
  rewrite Rplus_opp_l.
  reflexivity.
Qed.

Lemma Cmult_conj_nonneg (c : C) : 
  0 <= fst (c ^* * c)%C.
Proof.
  rewrite <- Cmod_sqr, <- RtoC_pow.
  apply pow2_ge_0.
Qed.


Lemma Cconj_simplify : forall (c1 c2 : C), c1^* = c2^* -> c1 = c2.
Proof. intros. 
       assert (H1 : c1 ^* ^* = c2 ^* ^*). { rewrite H; easy. }
       do 2 rewrite Cconj_conj in H1.   
       easy. 
Qed.


(** * Complex exponentiation **)


(** Compute e^(iθ) *)
Definition Cexp (θ : R) : C := (cos θ, sin θ).

Lemma Cexp_spec : forall α, Cexp α = cos α + Ci * sin α.
Proof. intros; lca. Qed.

Lemma Cexp_0 : Cexp 0 = 1.
Proof. unfold Cexp. autorewrite with trig_db; easy. Qed.

Lemma Cexp_add: forall (x y : R), Cexp (x + y) = Cexp x * Cexp y.
Proof.
  intros.
  unfold Cexp.
  apply c_proj_eq; simpl.
  - apply cos_plus.
  - rewrite sin_plus. field.
Qed.

Lemma Cexp_neg : forall θ, Cexp (- θ) = / Cexp θ.
Proof.
  intros θ.
  unfold Cexp.
  rewrite sin_neg, cos_neg.
  apply c_proj_eq; simpl.
  - replace (cos θ * (cos θ * 1) + sin θ * (sin θ * 1))%R with 
        (cos θ ^ 2 + sin θ ^ 2)%R by reflexivity.
    repeat rewrite <- Rsqr_pow2.
    rewrite Rplus_comm.
    rewrite sin2_cos2.
    field.
  - replace ((cos θ * (cos θ * 1) + sin θ * (sin θ * 1)))%R with 
        (cos θ ^ 2 + sin θ ^ 2)%R by reflexivity.
    repeat rewrite <- Rsqr_pow2.
    rewrite Rplus_comm.
    rewrite sin2_cos2.
    field.
Qed.

Lemma Cexp_minus : forall θ,
	Cexp θ + Cexp (-θ) = 2 * cos θ.
Proof.
	intros.
	unfold Cexp.
	rewrite cos_neg.
	rewrite sin_neg.
	lca.
Qed.

Lemma Cexp_plus_PI : forall x,
  Cexp (x + PI) = (- (Cexp x))%C.
Proof.
  intros.
  unfold Cexp.
  rewrite neg_cos, neg_sin.
  lca.
Qed.

Lemma Cexp_minus_PI: forall x : R, Cexp (x - PI) = (- Cexp x)%C.
Proof.
  intros x.
  unfold Cexp.
  rewrite cos_sym.
  rewrite Ropp_minus_distr.
  rewrite Rtrigo_facts.cos_pi_minus.
  rewrite <- Ropp_minus_distr.
  rewrite sin_antisym.
  rewrite Rtrigo_facts.sin_pi_minus.
  lca.
Qed.

Lemma Cexp_nonzero : forall θ, Cexp θ <> 0.
Proof. 
  intro θ. unfold Cexp.
  specialize (cos_sin_0_var θ) as [? | ?].
  apply C0_fst_neq; auto. 
  apply C0_snd_neq; auto.
Qed.

Lemma Cexp_mul_neg_l : forall θ, Cexp (- θ) * Cexp θ = 1.
Proof.  
  unfold Cexp. intros θ.
  eapply c_proj_eq; simpl.
  - autorewrite with R_db trig_db.
    field_simplify_eq.
    repeat rewrite <- Rsqr_pow2.
    rewrite Rplus_comm.
    apply sin2_cos2.
  - autorewrite with R_db trig_db. field.
Qed.

Lemma Cexp_mul_neg_r : forall θ, Cexp θ * Cexp (-θ) = 1.
Proof. intros. rewrite Cmult_comm. apply Cexp_mul_neg_l. Qed.

Lemma Cexp_pow : forall θ k, Cexp θ ^ k = Cexp (θ * INR k).
Proof.
  intros.
  induction k. 
  simpl. rewrite Rmult_0_r, Cexp_0. reflexivity.
  Local Opaque INR.
  simpl. rewrite IHk.
  rewrite <- Cexp_add.
  replace (S k) with (k + 1)%nat by lia.
  Local Transparent INR.
  rewrite plus_INR; simpl.
  apply f_equal. lra.
Qed.

Lemma Cexp_conj_neg : forall θ, (Cexp θ)^* = Cexp (-θ)%R.
Proof.
  intros.
  unfold Cexp.
  unfold Cconj.
  simpl.
  apply c_proj_eq; simpl.
  - rewrite cos_neg.
    reflexivity.
  - rewrite sin_neg.
    reflexivity.
Qed.

Lemma Cmod_Cexp : forall θ, Cmod (Cexp θ) = 1.
Proof.
  intro. unfold Cexp, Cmod. simpl. 
  replace ((cos θ * (cos θ * 1) + sin θ * (sin θ * 1)))%R 
    with (cos θ * cos θ + sin θ * sin θ)%R by lra. 
  specialize (sin2_cos2 θ) as H. 
  unfold Rsqr in H. 
  rewrite Rplus_comm in H. 
  rewrite H. apply sqrt_1.
Qed.

Lemma Cmod_Cexp_alt : forall θ, Cmod (1 - Cexp (2 * θ)) = Cmod (2 * (sin θ)).
Proof.
  intro θ.
  unfold Cexp, Cminus, Cplus.
  simpl.
  unfold Cmod. simpl. 
  apply f_equal.
  field_simplify_eq.
  unfold Rminus.
  rewrite (Rplus_assoc (_ ^ 2)).
  rewrite (Rplus_comm (- _)).
  rewrite <- Rplus_assoc.
  rewrite (Rplus_comm (_ ^ 2)).
  rewrite <- 2 Rsqr_pow2.
  rewrite sin2_cos2.
  rewrite cos_2a_sin.
  lra.
Qed.


(** Cexp of multiples of PI **)

(* Euler's Identity *) 
Lemma Cexp_PI : Cexp PI = -1.
Proof. unfold Cexp. autorewrite with trig_db; easy. Qed.

Lemma Cexp_PI2 : Cexp (PI/2) = Ci.
Proof. unfold Cexp. autorewrite with trig_db; easy. Qed.

Lemma Cexp_2PI : Cexp (2 * PI) = 1.
Proof.
  unfold Cexp. rewrite sin_2PI, cos_2PI. reflexivity.
Qed.

Lemma Cexp_PI4 : Cexp (PI / 4) = /√2 + /√2 * Ci.
Proof.
  unfold Cexp.
  rewrite sin_PI4, cos_PI4.
  eapply c_proj_eq; simpl.
  field_simplify_eq; trivial; apply sqrt2_neq_0.
  field_simplify_eq; trivial; apply sqrt2_neq_0.
Qed.

Lemma Cexp_2nPI : forall (k : Z), Cexp (IZR (2 * k) * PI) = 1.
Proof.
  induction k using Z.peano_ind.
  - simpl. rewrite Rmult_0_l. apply Cexp_0.
  - rewrite Z.mul_succ_r.
    rewrite plus_IZR.
    rewrite Rmult_plus_distr_r.
    rewrite Cexp_add, Cexp_2PI.
    rewrite IHk.
    lca.
  - rewrite Z.mul_pred_r.
    rewrite minus_IZR.
    unfold Rminus.
    rewrite Rmult_plus_distr_r.
    rewrite <- Ropp_mult_distr_l.
    rewrite Cexp_add, Cexp_neg, Cexp_2PI.
    rewrite IHk.
    lca.
Qed.


(** * Automation **)


Lemma Cminus_unfold : forall c1 c2, (c1 - c2 = c1 + -c2)%C. Proof. reflexivity. Qed.
Lemma Cdiv_unfold : forall c1 c2, (c1 / c2 = c1 */ c2)%C. Proof. reflexivity. Qed.

(* For proving goals of the form x <> 0 or 0 < x *)
Ltac nonzero :=
  repeat split;
  repeat
    match goal with
    | |- not (@eq _ (Copp _) (RtoC (IZR Z0))) => apply Copp_neq_0_compat
    | |- not (@eq _ (Cpow _ _) (RtoC (IZR Z0))) => apply Cpow_nz
    | |- not (@eq _ Ci (RtoC (IZR Z0))) => apply C0_snd_neq; simpl
    | |- not (@eq _ (Cexp _) (RtoC (IZR Z0))) => apply Cexp_nonzero
    | |- not (@eq _ _ (RtoC (IZR Z0))) => apply RtoC_neq
    end;
  repeat
    match goal with
    | |- not (@eq _ (sqrt (pow _ _)) (IZR Z0)) => rewrite sqrt_pow
    | |- not (@eq _ (pow _ _) (IZR Z0)) => apply pow_nonzero; try apply RtoC_neq
    | |- not (@eq _ (sqrt _) (IZR Z0)) => apply sqrt_neq_0_compat
    | |- not (@eq _ (Rinv _) (IZR Z0)) => apply Rinv_neq_0_compat
    | |- not (@eq _ (Rmult _ _) (IZR Z0)) => apply Rmult_integral_contrapositive_currified
    end;
  repeat
    match goal with
    | |- Rlt (IZR Z0) (Rmult _ _) => apply Rmult_lt_0_compat
    | |- Rlt (IZR Z0) (Rinv _) => apply Rinv_0_lt_compat
    | |- Rlt (IZR Z0) (pow _ _) => apply pow_lt
    end;
  match goal with
  | |- not (@eq _ _ _) => lra
  | |- Rlt _ _ => lra
  | |- Rle _ _ => lra
  end.

(*

#[global] Hint Rewrite Cexp_0 Cexp_PI Cexp_PI2 Cexp_2PI
  Cexp_PI4 Cexp_add Cexp_neg Cexp_plus_PI Cexp_minus_PI : Cexp_db.

#[global] Hint Rewrite Cminus_unfold Cdiv_unfold Ci2 Cconj_R Copp_conj Cconj_rad2 
     Cplus_0_l Cplus_0_r Cplus_opp_r Cplus_opp_l Copp_0  Copp_involutive
     Cmult_0_l Cmult_0_r Cmult_1_l Cmult_1_r : C_db.

#[global] Hint Rewrite <- Copp_mult_distr_l Copp_mult_distr_r Cdouble : C_db.
#[global] Hint Rewrite Cinv_l Cinv_r using nonzero : C_db.
(* Previously in the other direction *)
#[global] Hint Rewrite Cinv_mult : C_db.

(* Light rewriting db *)
#[global] Hint Rewrite Cplus_0_l Cplus_0_r Cmult_0_l Cmult_0_r Copp_0 
             Cconj_R Cmult_1_l Cmult_1_r : C_db_light.

(* Distributing db *)
#[global] Hint Rewrite Cmult_plus_distr_l Cmult_plus_distr_r 
  Copp_plus_distr Copp_mult_distr_l Copp_involutive : Cdist_db.

#[global] Hint Rewrite RtoC_opp RtoC_mult RtoC_minus RtoC_plus : RtoC_db.
#[global] Hint Rewrite RtoC_inv using nonzero : RtoC_db.
#[global] Hint Rewrite RtoC_pow : RtoC_db.

Lemma Copp_Ci : / Ci = - Ci.
Proof. field_simplify_eq; lca + nonzero. Qed.

#[global] Hint Rewrite Copp_Ci : C_db.


Ltac Csimpl := 
  repeat match goal with
  | _ => rewrite Cmult_0_l
  | _ => rewrite Cmult_0_r
  | _ => rewrite Cplus_0_l
  | _ => rewrite Cplus_0_r
  | _ => rewrite Cmult_1_l
  | _ => rewrite Cmult_1_r
  | _ => rewrite Cconj_R
  end.

Ltac Csimpl_in H := 
  repeat
  match goal with
  | _ => rewrite Cmult_0_l in H
  | _ => rewrite Cmult_0_r in H
  | _ => rewrite Cplus_0_l in H
  | _ => rewrite Cplus_0_r in H
  | _ => rewrite Cmult_1_l in H
  | _ => rewrite Cmult_1_r in H
  | _ => rewrite Cconj_R in H
  end.
*)

Ltac C_field_simplify := repeat field_simplify_eq [ Ci2 Ci2'].
Ltac C_field := C_field_simplify; nonzero || trivial.
