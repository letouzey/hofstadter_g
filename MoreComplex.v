
From Coq Require Import Reals Lra.
From Coquelicot Require Import Complex.

(** * Some complements to Coquelicot.Complex *)

Local Open Scope R.
Local Open Scope C.

(** Missing in Coquelicot.Complex *)
Bind Scope C_scope with C.
(** Workaround for already defined operations *)
Global Arguments Cplus _%C _%C.
Global Arguments Copp _%C.
Global Arguments Cminus _%C _%C.
Global Arguments Cmult _%C _%C.
Global Arguments Cinv _%C.
Global Arguments Cdiv _%C _%C.
Global Arguments Re _%C.
Global Arguments Im _%C.
Global Arguments Cmod _%C.
Global Arguments Cconj _%C.

(** A tactic solving (dis)equalities between C constants *)

Ltac cconst := compute; injection || f_equal ; lra.

(** A power function : c^n *)

Fixpoint Cpow (c : C) n : C :=
 match n with
 | O => 1
 | S n => c * Cpow c n
 end.

Global Infix "^" := Cpow : C_scope.

Lemma Cpow_1_l n : 1^n = 1.
Proof.
 induction n; simpl; auto. now rewrite IHn, Cmult_1_l.
Qed.

Lemma Cpow_1_r c : c^1 = c.
Proof.
 simpl. apply Cmult_1_r.
Qed.

Lemma Cpow_S c n : c^(S n) = c*c^n.
Proof.
 reflexivity.
Qed.

Lemma Cpow_add_r c n m : c^(n+m) = c^n*c^m.
Proof.
 induction n; simpl. now rewrite Cmult_1_l. now rewrite IHn, Cmult_assoc.
Qed.

Lemma Cpow_mult_l a b n : (a*b)^n = a^n * b^n.
Proof.
 induction n; simpl. now rewrite Cmult_1_l. rewrite IHn.
 rewrite Cmult_assoc.
 rewrite <- (Cmult_assoc a b _). rewrite (Cmult_comm b _).
 now rewrite !Cmult_assoc.
Qed.

Lemma Cpow_mult_r c n m : c^(n*m) = (c^n)^m.
Proof.
 induction n; simpl. now rewrite Cpow_1_l.
 now rewrite !Cpow_add_r, IHn, Cpow_mult_l.
Qed.

Lemma Cpow_nz (c:C) n : c <> 0 -> c^n <> 0.
Proof.
 induction n; simpl; intro H. cconst. apply Cmult_neq_0; auto.
Qed.

(* Better Ring / Field than in Coquelicot,
   handling Z constants and power *)

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


(** Various lemmas not in Coquelicot.Complex *)

Lemma C1_nz : RtoC 1 <> 0.
Proof.
 cconst.
Qed.

Lemma Ceq_minus (c c' : C) : c = c' <-> c-c' = 0.
Proof.
 split; intros H.
 - subst c. apply Cplus_opp_r.
 - destruct c as (x,y), c' as (x',y'). compute in H.
   injection H as Hx Hy.
   f_equal. lra. lra.
Qed.

Lemma Cpow_inv (c:C) n : c<>0 -> (/c)^n = /(c^n).
Proof.
 intros Hc. induction n; simpl; auto.
 - cconst.
 - rewrite IHn. field. auto using Cpow_nz.
Qed.

Lemma Cmod_pow (c:C) n : Cmod (c^n) = (Cmod c ^n)%R.
Proof.
 induction n; simpl; auto.
 - apply Cmod_1.
 - now rewrite Cmod_mult, IHn.
Qed.

Lemma Cmod2_alt (c:C) : (Cmod c ^2 = Re c ^2 + Im c ^2)%R.
Proof.
 unfold Cmod.
 rewrite pow2_sqrt. trivial.
 generalize (pow2_ge_0 (fst c)) (pow2_ge_0 (snd c)); lra.
Qed.

Lemma Cmod2_conj (c:C) : RtoC (Cmod c ^2) = c * Cconj c.
Proof.
 rewrite Cmod2_alt.
 destruct c as (x,y). unfold Cconj, Cmult, RtoC. simpl. f_equal; lra.
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
 rewrite im_alt. field. cconst.
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

Lemma im_RtoC (r:R) : Im (RtoC r) = 0.
Proof.
 reflexivity.
Qed.

Lemma re_scal_l (r:R)(c:C) : (Re (r*c) = r * Re c)%R.
Proof.
 destruct c as (x,y); simpl. lra.
Qed.

Lemma re_scal_r (c:C)(r:R) : (Re (c*r) = Re c * r)%R.
Proof.
 destruct c as (x,y); simpl. lra.
Qed.

Lemma im_scal_l (r:R)(c:C) : (Im (r*c) = r * Im c)%R.
Proof.
 destruct c as (x,y); simpl. lra.
Qed.

Lemma im_scal_r (c:C)(r:R) : (Im (c*r) = Im c * r)%R.
Proof.
 destruct c as (x,y); simpl. lra.
Qed.

Lemma Cconj_conj (c:C) : Cconj (Cconj c) = c.
Proof.
 unfold Cconj. simpl. destruct c; simpl; f_equal; lra.
Qed.

Lemma Cplus_conj a b : Cconj (a+b) = Cconj a + Cconj b.
Proof.
 destruct a as (xa,ya), b as (xb,yb). unfold Cplus, Cconj. simpl.
 f_equal. lra.
Qed.

Lemma Cmult_conj a b : Cconj (a*b) = Cconj a * Cconj b.
Proof.
 destruct a as (xa,ya), b as (xb,yb). unfold Cmult, Cconj. simpl.
 f_equal; lra.
Qed.

Lemma Copp_conj a : Cconj (-a) = - Cconj a.
Proof.
 reflexivity.
Qed.

Lemma Cminus_conj a b : Cconj (a-b) = Cconj a - Cconj b.
Proof.
 apply Cplus_conj.
Qed.

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
 intros H. unfold Cdiv. now rewrite Cmult_conj, Cinv_conj.
Qed.

Lemma Cpow_conj a n : Cconj (a^n) = (Cconj a)^n.
Proof.
 induction n; simpl. compute; f_equal; lra. rewrite Cmult_conj. now f_equal.
Qed.

Lemma Cmod_conj (c:C) : Cmod (Cconj c) = Cmod c.
Proof.
 unfold Cmod. destruct c as (x,y); simpl. f_equal. lra.
Qed.

Lemma RtoC_pow (a:R)(n:nat) : RtoC (a^n) = (RtoC a)^n.
Proof.
 induction n; simpl; auto. rewrite RtoC_mult. now f_equal.
Qed.

Lemma Ci_inv : /Ci = -Ci.
Proof.
 cconst.
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
