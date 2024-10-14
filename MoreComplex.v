From Coq Require Import Lia Reals Lra Permutation RelationClasses Sorted.
From Coquelicot Require Complex.
From QuantumLib Require Import Complex.
Require Import MoreList.

Module CC := Coquelicot.Complex.

Global Notation "0" := C0 : C_scope. (* TODO *)
Global Notation "1" := C1 : C_scope. (* TODO *)

(* A tactic solving (dis)equalities between C constants *)
Ltac cconst := compute; injection || f_equal ; lra.

(* Tactic negapply : With f : C->D ; turn a goal ~C into a subgoal ~D *)
Ltac negapply f :=
 let H := fresh in intro H; apply f in H;
 let c := type of H in revert H; change (not c).

Local Open Scope C.

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

Lemma im_RtoC (r:R) : Im (RtoC r) = 0%R.
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

Lemma Cmod_Ci : Cmod Ci = 1%R.
Proof.
 unfold Cmod, Ci. simpl fst; simpl snd.
 replace (_ + _)%R with 1%R by (simpl; lra). apply sqrt_1.
Qed.

(** Extra properties, not in Coquelicot nor in QuantumLib *)

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

Local Open Scope R.

Lemma Cmod_Re (c:C) : Re c = Cmod c -> Im c = 0.
Proof.
 intros E.
 assert (E' : Cmod c ^2 = Re c ^2) by now rewrite E.
 rewrite Cmod2_alt in E'.
 apply Rsqr_eq_0. rewrite Rsqr_pow2. lra.
Qed.

Lemma is_real_carac c : Im c = 0 <-> Cconj c = c.
Proof.
 split; intros H.
 - destruct c as (x,y); unfold Cconj, Im in *; simpl in *. subst.
   f_equal. lra.
 - destruct c as (x,y); unfold Cconj, Im in *; simpl in *. injection H.
   lra.
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

Lemma Clistsum_zero {A}(l:list A) : Clistsum (map (fun _ => C0) l) = C0.
Proof.
 induction l; simpl; rewrite ?IHl; lca.
Qed.

Lemma Clistsum_map {A} (f : A -> C) (l:list A) (d:A) :
  Clistsum (map f l) = big_sum (fun i => f (nth i l d)) (length l).
Proof.
 induction l; trivial.
 simpl length. rewrite big_sum_shift. simpl. now f_equal.
Qed.

Definition Cpoly x l := Clistsum (List.map (Cpow x) l).

Lemma Cpoly_cons x n l : Cpoly x (n::l) = (x^n + Cpoly x l)%C.
Proof.
 easy.
Qed.

Lemma Cpoly_app x l l' : Cpoly x (l++l') = (Cpoly x l + Cpoly x l')%C.
Proof.
 unfold Cpoly. now rewrite map_app, Clistsum_app.
Qed.

Lemma Clistsum_pow_factor c p l :
 Clistsum (List.map (fun n => c^(p+n))%C l) = (c^p * Cpoly c l)%C.
Proof.
 induction l; cbn -[Cpow].
 - ring.
 - change (List.fold_right Cplus 0)%C with Clistsum. rewrite IHl.
   fold (Cpoly c l). rewrite Cpow_add_r. ring.
Qed.

Lemma Cpoly_factor_above c p l :
 (forall n, List.In n l -> p <= n)%nat ->
 Cpoly c l = (c^p * Cpoly c (List.map (decr p) l))%C.
Proof.
 induction l as [|a l IH]; cbn -[Cpow]; intros Hl.
 - ring.
 - change (List.fold_right Cplus 0)%C with Clistsum.
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
  G_big_mult (map (fun x => x * c) l)%C = (G_big_mult l * c ^ length l)%C.
Proof.
 induction l; simpl; rewrite ?IHl; ring.
Qed.

Lemma Gbigmult_perm l l' : Permutation l l' -> G_big_mult l = G_big_mult l'.
Proof.
 induction 1; simpl; ring || congruence.
Qed.

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
