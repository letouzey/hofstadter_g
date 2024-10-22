From Coq Require Import Lia Reals Lra Permutation.
From QuantumLib Require Import Complex.
From QuantumLib Require Polar.

Local Open Scope C.

(** Better Ring / Field, handling Z constants and power
    (now integrated in Coquelicot >= 3.3.0) *)

Definition C_ring_morph :
 ring_morph (RtoC 0) (RtoC 1) Cplus Cmult Cminus Copp (@eq C)
  0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb (fun z => RtoC (IZR z)).
Proof.
 constructor; try reflexivity; intros.
 - now rewrite plus_IZR, RtoC_plus.
 - now rewrite minus_IZR, RtoC_minus.
 - now rewrite mult_IZR, RtoC_mult.
 - now rewrite opp_IZR, RtoC_opp.
 - f_equal. f_equal. now apply Z.eqb_eq.
Qed.

Lemma Zeqb_Ccomplete z z' : RtoC (IZR z) = RtoC (IZR z') -> Z.eqb z z' = true.
Proof.
 intros H. apply Z.eqb_eq. now apply eq_IZR, RtoC_inj.
Qed.

Lemma C_power_theory : @power_theory C 1 Cmult (@eq C) _ N.to_nat Cpow.
Proof.
 constructor. destruct n. reflexivity.
 simpl. induction p.
 - rewrite Pos2Nat.inj_xI. simpl. now rewrite Nat.add_0_r, Cpow_add_r, IHp.
 - rewrite Pos2Nat.inj_xO. simpl. now rewrite Nat.add_0_r, Cpow_add_r, IHp.
 - simpl. now rewrite Cmult_1_r.
Qed.

Ltac RtoC_IZR_tac t :=
  match t with
  | RtoC ?x => IZR_tac x
  | _ => constr:(NotConstant)
  end.

Lemma C_ring_theory : ring_theory (RtoC 0) (RtoC 1) Cplus Cmult Cminus Copp eq.
Proof.
constructor.
exact Cplus_0_l.
exact Cplus_comm.
exact Cplus_assoc.
exact Cmult_1_l.
exact Cmult_comm.
exact Cmult_assoc.
exact Cmult_plus_distr_r.
easy.
exact Cplus_opp_r.
Qed.

Add Ring C_ring_ring :
 C_ring_theory
  (morphism C_ring_morph,
   constants [RtoC_IZR_tac],
   power_tac C_power_theory [Rpow_tac]).

Lemma C_field_theory : field_theory (RtoC 0) (RtoC 1) Cplus Cmult Cminus Copp Cdiv Cinv eq.
Proof.
constructor.
constructor.
exact Cplus_0_l.
exact Cplus_comm.
exact Cplus_assoc.
exact Cmult_1_l.
exact Cmult_comm.
exact Cmult_assoc.
exact Cmult_plus_distr_r.
easy.
exact Cplus_opp_r.
intros H.
injection H.
exact R1_neq_R0.
easy.
apply Cinv_l.
Qed.

Add Field C_field2 :
 C_field_theory
  (morphism C_ring_morph,
   completeness Zeqb_Ccomplete,
   constants [RtoC_IZR_tac],
   power_tac C_power_theory [Rpow_tac]).

(* Properties now in Coquelicot 3.3, but only partly in
   QuantumLib.Complex *)

Lemma Cpow_1_l n : 1^n = 1.
Proof.
 induction n; simpl; auto. now rewrite IHn, Cmult_1_l.
Qed.
Lemma Cpow_1_r c : c^1 = c. Proof. ring. Qed.
Lemma Cpow_S c n : c^(S n) = c*c^n. Proof. reflexivity. Qed.

(* Cpow_add_r : ok *)
(* Cpow_mult_l --> Cpow_mul_l *)
(* Cpow_mult_r --> Cpow_mult *)
(* Cpow_nz --> Cpow_nonzero *)
(* C1_nz --> C1_neq_C0 *)

Lemma Ceq_minus (c c' : C) : c = c' <-> c-c' = 0.
Proof.
 split; intros H.
 - subst c. apply Cplus_opp_r.
 - destruct c as (x,y), c' as (x',y'). compute in H.
   injection H as Hx Hy.
   apply Rminus_diag_uniq_sym in Hx. apply Rminus_diag_uniq_sym in Hy.
   now f_equal.
Qed.

(* Also in QuantumLib, but with a worse precondition *)
Lemma Cpow_inv (c:C) n : c<>0 -> (/c)^n = /(c^n).
Proof.
 intros Hc. induction n; simpl; auto.
 - symmetry. rewrite <-(Cmult_1_l (/1)). apply Cinv_r, C1_neq_C0.
 - rewrite IHn. field. auto using Cpow_nonzero.
Qed.

(* Cmod_pow : ok *)

Lemma Cmod2_alt (c:C) : (Cmod c ^2 = Re c ^2 + Im c ^2)%R.
Proof.
 unfold Cmod.
 rewrite <-Rsqr_pow2, Rsqr_sqrt. trivial.
 apply Rplus_le_le_0_compat; apply pow2_ge_0.
Qed.

Lemma Cmod2_conj (c:C) : RtoC (Cmod c ^2) = c * Cconj c.
Proof.
 rewrite Cmod2_alt.
 destruct c as (x,y). unfold Cconj, Cmult, RtoC. simpl. f_equal; ring.
Qed.

Lemma re_alt (c:C) : RtoC (Re c) = (c + Cconj c)/2.
Proof.
 destruct c as (x,y).
 unfold Cconj, RtoC, Cplus, Cdiv, Cmult. simpl. f_equal; field.
Qed.

Lemma im_alt (c:C) : RtoC (Im c) = (c - Cconj c)/(2*Ci).
Proof.
 destruct c as (x,y).
 unfold Cconj, RtoC, Ci, Cminus, Cplus, Cdiv, Cmult. simpl. f_equal; field.
Qed.

Lemma im_alt' (c:C) : c - Cconj c = 2*Ci*Im c.
Proof.
 rewrite im_alt. field. C_field.
Qed.

Lemma re_conj (c:C) : Re (Cconj c) = Re c.
Proof.
 now destruct c.
Qed.

Lemma im_conj (c:C) : Im (Cconj c) = (- Im c)%R.
Proof.
 now destruct c.
Qed.

Lemma re_plus a b : (Re (a+b) = Re a + Re b)%R.
Proof.
 now destruct a as (xa,ya), b as (xb,yb).
Qed.

Lemma re_opp a : (Re (-a) = - Re a)%R.
Proof.
 now destruct a as (xa,ya).
Qed.

Lemma re_mult a b : (Re (a*b) = Re a * Re b - Im a * Im b)%R.
Proof.
 now destruct a as (xa,ya), b as (xb,yb).
Qed.

Lemma im_plus a b : (Im (a+b) = Im a + Im b)%R.
Proof.
 now destruct a as (xa,ya), b as (xb,yb).
Qed.

Lemma im_opp a : (Im (-a) = - Im a)%R.
Proof.
 now destruct a as (xa,ya).
Qed.

Lemma im_mult a b : (Im (a*b) = Re a * Im b + Im a * Re b)%R.
Proof.
 now destruct a as (xa,ya), b as (xb,yb).
Qed.

Lemma re_RtoC (r:R) : Re (RtoC r) = r.
Proof.
 reflexivity.
Qed.

Lemma im_RtoC (r:R) : Im (RtoC r) = 0%R.
Proof.
 reflexivity.
Qed.

Lemma re_scal_l (r:R)(c:C) : (Re (r*c) = r * Re c)%R.
Proof.
 destruct c as (x,y); simpl. ring.
Qed.

Lemma re_scal_r (c:C)(r:R) : (Re (c*r) = Re c * r)%R.
Proof.
 destruct c as (x,y); simpl. ring.
Qed.

Lemma im_scal_l (r:R)(c:C) : (Im (r*c) = r * Im c)%R.
Proof.
 destruct c as (x,y); simpl. ring.
Qed.

Lemma im_scal_r (c:C)(r:R) : (Im (c*r) = Im c * r)%R.
Proof.
 destruct c as (x,y); simpl. ring.
Qed.

(* Cconj_conj --> Cconj_involutive *)
(* Cplus_conj --> Cconj_plus_distr *)
(* Cmult_conj --> Cconj_mult_distr *)
(* Copp_conj --> Cconj_opp (* TODO: strange variable name C0 !! *) *)
(* Cminus_conj --> Cconj_minus_distr *)

Lemma Cpow_conj a n : Cconj (a^n) = (Cconj a)^n.
Proof.
 induction n; simpl. compute; f_equal; lra. rewrite Cconj_mult_distr.
 now f_equal.
Qed.

(* Cmod_conj --> Cmod_Cconj *)

(* Already in QuantumLib (but in the other direction)
Lemma RtoC_pow (a:R)(n:nat) : RtoC (a^n) = (RtoC a)^n.
Proof.
 induction n; simpl; auto. rewrite RtoC_mult. now f_equal.
Qed.
*)

Lemma Ci_inv : /Ci = -Ci.
Proof.
 lca.
Qed.

Lemma re_mult_Ci (c:C) : (Re (c*Ci) = - Im c)%R.
Proof.
 destruct c as (x,y). compute. lra.
Qed.

Lemma im_mult_Ci (c:C) : (Im (c*Ci) = Re c)%R.
Proof.
 destruct c as (x,y). compute. lra.
Qed.

Lemma re_le_Cmod (c:C) : Rabs (Re c) <= Cmod c.
Proof.
 rewrite <- (Rabs_right (Cmod c)) by (apply Rle_ge; apply Cmod_ge_0).
 apply Rsqr_le_abs_0.
 rewrite !Rsqr_pow2, Cmod2_alt.
 assert (0 <= (Im c)^2) by (rewrite <- Rsqr_pow2; apply Rle_0_sqr).
 lra.
Qed.

Lemma Cmod_Ci : Cmod Ci = 1%R.
Proof.
 unfold Cmod, Ci. simpl fst; simpl snd.
 replace (_ + _)%R with 1%R by (simpl; lra). apply sqrt_1.
Qed.

(* TODO: Coquelicot.Cinv_conj has an extra precondition to get rid of.
   QuantumLib.Cinv_Cconj has a less natural direction. *)
Lemma Cinv_conj (a:C) : Cconj (/a) = /Cconj a.
Proof.
 symmetry. apply Cinv_Cconj.
Qed.

(* TODO: Coquelicot.Cdiv_conj has an extra precondition to get rid of.
   Not in QuantumLib. *)
Lemma Cdiv_conj (a b : C) : Cconj (a/b) = Cconj a / Cconj b.
Proof.
 unfold Cdiv. now rewrite Cconj_mult_distr, Cinv_conj.
Qed.

(** Extra properties, not in Coquelicot nor in QuantumLib *)

Lemma re_alt' (c:C) : c + Cconj c = 2*Re c.
Proof. rewrite re_alt. field. Qed.

Lemma Ci_conj : Cconj Ci = - Ci.
Proof. compute. f_equal. symmetry. exact Ropp_0. Qed.

Lemma Cpow_0_r c : c^0 = 1.
Proof. reflexivity. Qed.

Lemma RtoC_inj_neq x y : x<>y -> RtoC x <> RtoC y.
Proof.
 intros N E. now apply RtoC_inj in E.
Qed.

Lemma re_im_id (c:C) : (Re c + Ci * Im c = c)%C.
Proof.
 destruct c as (x,y). unfold Ci, Cmult, Cplus. simpl. f_equal; ring.
Qed.

Lemma re_im_conj (c:C) : (Re c - Ci * Im c = Cconj c)%C.
Proof.
 destruct c as (x,y). unfold Cconj, Ci, Cmult, Cminus, Cplus, Copp.
 simpl. f_equal; ring.
Qed.

Lemma pow2_minus_conj2 c : c^2 - Cconj c ^2 = 4*Ci* Re c * Im c.
Proof.
 rewrite <- (re_im_conj c). rewrite <- (re_im_id c) at 1. ring.
Qed.

Lemma conj2_minus_pow2 c : Cconj c ^2 - c^2 = -4*Ci* Re c * Im c.
Proof.
 replace (RtoC (-4)) with (-(4)) by lca.
 rewrite <- !Copp_mult_distr_l, <- pow2_minus_conj2. ring.
Qed.

Lemma Cinv0 : /0 = 0.
Proof.
 compute. f_equal; ring.
Qed.

Lemma Cinv_alt (a : C) : a<>0 ->
 /a = Cconj a / (Cmod a^2)%R.
Proof.
 intros Hb. rewrite Cmod2_conj. field; split;trivial. now apply Cconj_neq_0.
Qed.

(* Note : QuantumLib.Complex.Cmult_integral is only the -> direction *)
Lemma Cmult_integral (a b : C) : a * b = 0 <-> a = 0 \/ b = 0.
Proof.
 split.
 - destruct (Ceq_dec a 0) as [->|A]. now left.
   destruct (Ceq_dec b 0) as [->|B]. now right.
   intros H. now destruct (Cmult_neq_0 a b).
 - intros [-> | ->]; ring.
Qed.

Lemma Cmult_eq_reg_r a b c : a * c = b * c -> c<>0 -> a = b.
Proof.
 intros E N. rewrite Ceq_minus. rewrite Ceq_minus in E.
 replace (a*c-b*c) with ((a-b)*c) in E by ring.
 apply Cmult_integral in E. tauto.
Qed.

Lemma Cmult_eq_reg_l a b c : c * a = c * b -> c<>0 -> a = b.
Proof.
 intros E N. rewrite (Cmult_comm c a), (Cmult_comm c b) in E.
 now apply Cmult_eq_reg_r with c.
Qed.

Lemma Cinv_eq a b : a*b = 1 -> a = /b.
Proof.
 intros E.
 assert (b<>0).
 { intros ->. rewrite Cmult_0_r in E. symmetry in E.
   revert E. apply C1_neq_C0. }
 apply Cmult_eq_reg_r with b; trivial. rewrite E. field; trivial.
Qed.

Lemma polar_eqn (c:C) : Cmod c * Cexp (Polar.get_arg c) = c.
Proof.
 destruct (Ceq_dec c 0) as [->|Hc].
 - now rewrite Cmod_0, Cmult_0_l.
 - now apply Polar.rect_to_polar_to_rect.
Qed.

Local Open Scope R.

Lemma Cmod_Re (c:C) : Re c = Cmod c -> Im c = 0.
Proof.
 intros E.
 assert (E' : Cmod c ^2 = Re c ^2) by now rewrite E.
 rewrite Cmod2_alt in E'.
 apply Rsqr_eq_0. rewrite Rsqr_pow2. lra.
Qed.

(* Note: QuantumLib.Complex.Cconj_eq_implies_real is just the <- direction *)
Lemma is_real_carac c : Im c = 0 <-> Cconj c = c.
Proof.
 split; intros H.
 - destruct c as (x,y); unfold Cconj, Im in *; simpl in *. subst.
   f_equal. lra.
 - destruct c as (x,y); unfold Cconj, Im in *; simpl in *. injection H.
   lra.
Qed.

Lemma Cmod_triangle' a b : Cmod a - Cmod b <= Cmod (a + b).
Proof.
 generalize (Cmod_triangle (a+b) (-b)). replace (a+b+-b)%C with a by lca.
 rewrite Cmod_opp. lra.
Qed.

Lemma Cmod_triangle_exact (c:C) :
  Cmod (c - 1) = Cmod c - 1 -> c = Cmod c.
Proof.
 intros E.
 assert (E' : Cmod (c-1)^2 = (Cmod c - 1)^2) by now rewrite E.
 clear E. rename E' into E.
 rewrite <- (Rsqr_pow2 (_ - _)) in E.
 unfold Rsqr in E. ring_simplify in E.
 rewrite !Cmod2_alt in E.
 replace (Re (c-1)) with (Re c - 1) in E.
 2:{ destruct c as (x,y). simpl. lra. }
 replace (Im (c-1)) with (Im c) in E.
 2:{ destruct c as (x,y). simpl. lra. }
 ring_simplify in E.
 assert (RE : Re c = Cmod c) by lra.
 assert (IM := Cmod_Re _ RE).
 rewrite <- RE. destruct c. simpl in *. now rewrite IM.
Qed.
