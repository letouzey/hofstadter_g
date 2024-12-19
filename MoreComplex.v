From Coq Require Import Lia Reals Lra Permutation RelationClasses Sorted.
From QuantumLib Require Import Complex.
From QuantumLib Require Polar.
Require Import MoreList MoreReals.

Global Notation "0" := C0 : C_scope. (* TODO *)
Global Notation "1" := C1 : C_scope. (* TODO *)

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

(** Properties in Coquelicot and QuantumLib, for which a precondition
    can be removed now that [/0 = 0]
    (cf Coq 8.16 and the future Coquelicot 4) *)

Lemma RtoC_inv (x : R) : RtoC (/ x) = / RtoC x.
Proof.
  apply injective_projections ; simpl.
  2: unfold Rdiv; ring.
  destruct (Req_dec x 0) as [->|Hx].
  rewrite Rinv_0.
  unfold Rdiv; ring.
  now field.
Qed.

Lemma RtoC_div (x y : R) : RtoC (x / y) = RtoC x / RtoC y.
Proof.
 unfold Cdiv, Rdiv. now rewrite <- RtoC_inv, <- RtoC_mult.
Qed.

Lemma Cinv_0 : /C0 = C0.
Proof.
 now rewrite <- RtoC_inv, Rinv_0.
Qed.

Lemma Cinv_1 : /C1 = C1.
Proof.
 now rewrite <- RtoC_inv, Rinv_1.
Qed.

Lemma Cinv_Copp c : /-c = -/c.
Proof.
 destruct (Ceq_dec c 0) as [->|N]; try lca. now field.
Qed.

Lemma Cmod_inv (c : C) : Cmod (/ c) = Rinv (Cmod c).
Proof.
  destruct (Req_dec (Cmod c) 0) as [Hm|Hm].
  - rewrite Hm, Rinv_0.
    apply Cmod_eq_0 in Hm.
    rewrite Hm, Cinv_0.
    apply Cmod_0.
  - apply Cmod_inv. contradict Hm. now rewrite Hm, Cmod_0.
Qed.

Lemma Cmod_div (x y : C) : Cmod (x / y) = Rdiv (Cmod x) (Cmod y).
Proof.
 unfold Cdiv, Rdiv. now rewrite Cmod_mult, Cmod_inv.
Qed.

Lemma Cinv_inv (c : C) : Cinv (Cinv c) = c.
Proof.
 destruct (Ceq_dec c 0) as [->|N].
 - now rewrite !Cinv_0.
 - now apply Cinv_inv.
Qed.

Lemma Cinv_mult (x y : C) : Cinv (Cmult x y) = Cmult (Cinv x) (Cinv y).
Proof.
  destruct (Ceq_dec x 0) as [->|Zx].
  { rewrite Cinv_0, !Cmult_0_l. apply Cinv_0. }
  destruct (Ceq_dec y 0) as [->|Zy].
  { rewrite Cinv_0, !Cmult_0_r. apply Cinv_0. }
  now field.
Qed.

(* Also in QuantumLib, but with a worse precondition *)
Lemma Cpow_inv (c:C) n : (/c)^n = /(c^n).
Proof.
  induction n; simpl; auto.
  - apply sym_eq, Cinv_1.
  - now rewrite Cinv_mult, IHn.
Qed.

Lemma Cinv_conj (a:C) : Cconj (/a) = /Cconj a.
Proof.
 symmetry. apply Cinv_Cconj.
Qed.

Lemma Cdiv_conj (a b : C) : Cconj (a/b) = Cconj a / Cconj b.
Proof.
 unfold Cdiv. now rewrite Cconj_mult_distr, Cinv_conj.
Qed.

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
 apply Rle_trans with (Rmax (Rabs (Re c)) (Rabs (Im c)));
  [ apply Rmax_l | apply Rmax_Cmod ].
Qed.

Lemma im_le_Cmod (c:C) : Rabs (Im c) <= Cmod c.
Proof.
 apply Rle_trans with (Rmax (Rabs (Re c)) (Rabs (Im c)));
  [ apply Rmax_r | apply Rmax_Cmod ].
Qed.

Lemma Cmod_Ci : Cmod Ci = 1%R.
Proof.
 unfold Cmod, Ci. simpl fst; simpl snd.
 replace (_ + _)%R with 1%R by (simpl; lra). apply sqrt_1.
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

Local Close Scope R.

(** Lexicographic order on complex numbers *)

Definition Clt c c' := (Re c < Re c' \/ (Re c = Re c' /\ Im c < Im c'))%R.
Definition Cgt := flip Clt.

Local Instance Clt_order : StrictOrder Clt.
Proof.
 split.
 - intros (x,y). red. unfold Clt, Re, Im. simpl. lra.
 - intros (x1,y1) (x2,y2) (x3,y3). unfold Clt, Re, Im; simpl. lra.
Qed.

Local Instance Cgt_order : StrictOrder Cgt.
Proof.
 apply flip_StrictOrder, Clt_order.
Qed.

Lemma Ctotal_order c c' : Clt c c' \/ c = c' \/ Clt c' c.
Proof.
 destruct c as (x,y), c' as (x',y'). unfold Clt, Re, Im. simpl.
 destruct (Rtotal_order x x') as [X|[<-|X] ]; try lra.
 destruct (Rtotal_order y y') as [Y|[<-|Y] ]; try lra.
 right. now left.
Qed.

(** Sorted complex lists (in decreasing lex order) *)

Definition Csorted (l : list C) := Sorted Cgt l.

Lemma Csorted_alt l : Csorted l <-> StronglySorted Cgt l.
Proof.
 split.
 - apply Sorted_StronglySorted; trivial. apply Cgt_order.
 - apply StronglySorted_Sorted.
Qed.

Lemma Csorted_nodup l : Csorted l -> NoDup l.
Proof.
 rewrite Csorted_alt.
 induction l; simpl; intros; auto; constructor; inversion_clear H; auto.
 intros IN. rewrite Forall_forall in *. generalize (H1 _ IN). apply Clt_order.
Qed.

Lemma Csorted_unique l l' :
  Csorted l -> Csorted l' -> Permutation l l' -> l = l'.
Proof.
 rewrite !Csorted_alt.
 revert l'. induction l as [|x l IH]; destruct l' as [|x' l']; trivial;
  intros S S' P.
 - now apply Permutation_nil_cons in P.
 - symmetry in P. now apply Permutation_nil_cons in P.
 - inversion_clear S. inversion_clear S'. rewrite Forall_forall in *.
   assert (x = x').
   { assert (X : In x (x'::l')). rewrite <- P; now left.
     assert (X' : In x' (x::l)). rewrite P; now left.
     simpl in *.
     destruct X as [->|X]; trivial.
     destruct X' as [<-|X']; trivial.
     specialize (H0 _ X'). specialize (H2 _ X).
     assert (XX : Cgt x x) by now transitivity x'.
     now apply Cgt_order in XX. }
   subst x'. f_equal. apply IH; trivial. eapply Permutation_cons_inv; eauto.
Qed.

(** Existence of sorted lists of complex numbers : thanks to
    Rlt_le_dec we could write a boolean C comparison and use mergesort
    on it, but that will not compute.
    Instead, we prove here an existence in Prop, by mimicking an
    insertion sort. *)

Lemma Cinsert_exists x l :
  Csorted l -> ~In x l -> exists l', Permutation (x::l) l' /\ Csorted l'.
Proof.
 rewrite Csorted_alt. setoid_rewrite Csorted_alt.
 induction l as [|y l IH].
 - exists [x]; split; now constructor.
 - intros Y X.
   destruct (Ctotal_order x y) as [H|[<-|H]].
   + inversion_clear Y.
     destruct IH as (l' & P & L'); trivial. simpl; intuition.
     exists (y::l'); split.
     * rewrite <- P. apply perm_swap.
     * constructor; trivial. rewrite <- P. now constructor.
   + simpl in X. intuition.
   + exists (x::y::l). split; trivial.
     rewrite <- Csorted_alt. constructor. now rewrite Csorted_alt.
     now constructor.
Qed.

Lemma Csorted_exists l : NoDup l -> exists l', Permutation l l' /\ Csorted l'.
Proof.
 induction 1.
 - exists []. split; constructor.
 - destruct IHNoDup as (l' & P & L').
   destruct (Cinsert_exists x l') as (l2 & P2 & L2); trivial.
   now rewrite <- P.
   exists l2. split; trivial. now rewrite <- P2, <- P.
Qed.

Lemma StronglySorted_nth (R : C -> C -> Prop) (l : list C) :
 StronglySorted R l <->
 forall n m, (n < m < length l)%nat -> R (nth n l C0) (nth m l C0).
Proof.
 split.
 - induction 1; simpl length; try lia.
   intros [|n] [|m]; try lia; intros; simpl nth.
   + rewrite Forall_forall in H0. apply H0. apply nth_In; lia.
   + apply IHStronglySorted; lia.
 - induction l; simpl length; intros H; constructor.
   + apply IHl. intros n m NM. apply (H (S n) (S m)). lia.
   + apply Forall_forall. intros x X.
     destruct (In_nth l x C0 X) as (n & LT & <-). apply (H O (S n)). lia.
Qed.

Lemma Csorted_rev l : Csorted l <-> Sorted Clt (rev l).
Proof.
 rewrite Csorted_alt. split.
 - rewrite StronglySorted_nth. intros H. apply StronglySorted_Sorted.
   rewrite StronglySorted_nth.
   intros n m NM. rewrite rev_length in NM. rewrite !rev_nth by lia.
   apply H. lia.
 - intros H. apply Sorted_StronglySorted in H; try apply Clt_order.
   rewrite !StronglySorted_nth in *.
   intros n m NM.
   replace n with (length l - S (length l - S n))%nat by lia.
   replace m with (length l - S (length l - S m))%nat by lia.
   rewrite <- !rev_nth by lia. apply H. rewrite rev_length. lia.
Qed.

(** Short notation of nth element in a C list *)

Definition Cnth l i := nth i l C0.
Infix "@" := Cnth (at level 10) : C_scope.
