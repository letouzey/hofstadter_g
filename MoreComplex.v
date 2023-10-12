From Coq Require Import Lia Reals Lra Permutation.
From Coquelicot Require Complex.
From QuantumLib Require Import Complex.

Module CC := Coquelicot.Complex.

(* A tactic solving (dis)equalities between C constants *)
Ltac cconst := compute; injection || f_equal ; lra.

(* Tactic negapply : With f : C->D ; turn a goal ~C into a subgoal ~D *)
Ltac negapply f :=
 let H := fresh in intro H; apply f in H;
 let c := type of H in revert H; change (not c).

Local Open Scope C.

(* Sums of (list C). *)

Definition Clistsum l := List.fold_right Cplus 0%C l.

Lemma Clistsum_cons x l : Clistsum (x::l) = (x + Clistsum l)%C.
Proof.
 reflexivity.
Qed.

Lemma Clistsum_app l l' : Clistsum (l++l') = (Clistsum l + Clistsum l')%C.
Proof.
 induction l; simpl; rewrite ?IHl; ring.
Qed.

(** Better Ring / Field than in Coquelicot, handling Z constants and power *)

Definition C_ring_morph :
 ring_morph (RtoC 0) (RtoC 1) Cplus Cmult Cminus Copp (@eq C)
  0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb (fun z => RtoC (IZR z)).
Proof. apply CC.C_ring_morph. Qed.

Lemma Zeqb_Ccomplete z z' : RtoC (IZR z) = RtoC (IZR z') -> Z.eqb z z' = true.
Proof. apply CC.Zeqb_Ccomplete. Qed.

Lemma C_power_theory : @power_theory C 1 Cmult (@eq C) _ N.to_nat Cpow.
Proof. apply CC.C_power_theory. Qed.

Ltac IZC_tac t :=
  match t with
  | RtoC ?x => IZR_tac x
  | _ => constr:(NotConstant)
  end.

Add Field C_field2 :
 C_field_theory
  (morphism C_ring_morph,
   completeness Zeqb_Ccomplete,
   constants [IZC_tac],
   power_tac C_power_theory [Rpow_tac]).


(* Old MoreComplex.v, now in Coquelicot 3.3, but only partly in
   QuantumLib.Complex *)

Lemma Cpow_1_l n : 1^n = 1. Proof. apply CC.Cpow_1_l. Qed.
Lemma Cpow_1_r c : c^1 = c. Proof. apply CC.Cpow_1_r. Qed.
Lemma Cpow_S c n : c^(S n) = c*c^n. Proof. reflexivity. Qed.

(* Cpow_add_r : ok *)
(* Cpow_mult_l --> Cpow_mul_l *)
(* Cpow_mult_r --> Cpow_mult *)

(* TODO: QuantumLib.Complex.Cpow_nonzero is buggy (only on reals) *)
Lemma Cpow_nz (c : C) n : c <> 0 -> c ^ n <> 0.
Proof. apply CC.Cpow_nz. Qed.

(* C1_nz --> C1_neq_C0 *)

Lemma Ceq_minus (c c' : C) : c = c' <-> c-c' = 0.
Proof. apply CC.Ceq_minus. Qed.

(* Also in QuantumLib, but with a worse precondition *)
Lemma Cpow_inv (c:C) n : c<>0 -> (/c)^n = /(c^n).
Proof. apply CC.Cpow_inv. Qed.

(* Cmod_pow : ok *)

Lemma Cmod2_alt (c:C) : (Cmod c ^2 = Re c ^2 + Im c ^2)%R.
Proof. apply CC.Cmod2_alt. Qed.

Lemma Cmod2_conj (c:C) : RtoC (Cmod c ^2) = c * Cconj c. (* Almost Cmod_sqr *)
Proof. apply CC.Cmod2_conj. Qed.

Lemma re_alt (c:C) : RtoC (Re c) = (c + Cconj c)/2.
Proof. apply CC.re_alt. Qed.

Lemma im_alt (c:C) : RtoC (Im c) = (c - Cconj c)/(2*Ci).
Proof. apply CC.im_alt. Qed.

Lemma im_alt' (c:C) : c - Cconj c = 2*Ci*Im c.
Proof. apply CC.im_alt'. Qed.

Lemma re_conj (c:C) : Re (Cconj c) = Re c.
Proof. apply CC.re_conj. Qed.

Lemma im_conj (c:C) : Im (Cconj c) = (- Im c)%R.
Proof. apply CC.im_conj. Qed.

Lemma re_plus a b : (Re (a+b) = Re a + Re b)%R.
Proof. apply CC.re_plus. Qed.

Lemma re_opp a : (Re (-a) = - Re a)%R.
Proof. apply CC.re_opp. Qed.

Lemma re_mult a b : (Re (a*b) = Re a * Re b - Im a * Im b)%R.
Proof. apply CC.re_mult. Qed.

Lemma im_plus a b : (Im (a+b) = Im a + Im b)%R.
Proof. apply CC.im_plus. Qed.

Lemma im_opp a : (Im (-a) = - Im a)%R.
Proof. apply CC.im_opp. Qed.

Lemma im_mult a b : (Im (a*b) = Re a * Im b + Im a * Re b)%R.
Proof. apply CC.im_mult. Qed.

Lemma re_RtoC (r:R) : Re (RtoC r) = r.
Proof. reflexivity. Qed.

Lemma im_RtoC (r:R) : Im (RtoC r) = 0.
Proof. reflexivity. Qed.

Lemma re_scal_l (r:R)(c:C) : (Re (r*c) = r * Re c)%R.
Proof. apply CC.re_scal_l. Qed.

Lemma re_scal_r (c:C)(r:R) : (Re (c*r) = Re c * r)%R.
Proof. apply CC.re_scal_r. Qed.

Lemma im_scal_l (r:R)(c:C) : (Im (r*c) = r * Im c)%R.
Proof. apply CC.im_scal_l. Qed.

Lemma im_scal_r (c:C)(r:R) : (Im (c*r) = Im c * r)%R.
Proof. apply CC.im_scal_r. Qed.

(* Cconj_conj --> Cconj_involutive *)
(* Cplus_conj --> Cconj_plus_distr *)
(* Cmult_conj --> Cconj_mult_distr *)
(* Copp_conj --> Cconj_opp (* TODO: strange variable name C0 !! *) *)
(* Cminus_conj --> Cconj_minus_distr *)

Lemma Cinv_conj (a:C) : a<>0 -> Cconj (/a) = /Cconj a.
Proof.
 intros H.
 assert (H' := H). rewrite Cmod_gt_0 in H'.
 rewrite <- sqrt_0 in H'. apply sqrt_lt_0_alt in H'.
 destruct a as (xa,ya). simpl in *. unfold Cinv, Cconj. simpl.
 f_equal; field; lra.
Qed.

Lemma Cdiv_conj (a b : C) : b<>0 -> Cconj (a/b) = Cconj a / Cconj b.
Proof.
 intros H. unfold Cdiv. now rewrite Cconj_mult_distr, Cinv_conj.
Qed.

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

Lemma Cmod_Ci : Cmod Ci = 1.
Proof.
 unfold Cmod, Ci. simpl fst; simpl snd.
 replace (_ + _)%R with 1 by (simpl; lra). apply sqrt_1.
Qed.

(** Extra properties, not in Coquelicot nor in QuantumLib *)

Lemma Cinv0 : Cinv 0 = 0.
Proof.
 compute. f_equal; ring.
Qed.

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

Local Open Scope R.

Lemma Cmod_Re (c:C) : Re c = Cmod c -> Im c = 0.
Proof.
 intros E.
 assert (E' : Cmod c ^2 = Re c ^2) by now rewrite E.
 rewrite Cmod2_alt in E'.
 apply Rsqr_eq_0. rewrite Rsqr_pow2. lra.
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
