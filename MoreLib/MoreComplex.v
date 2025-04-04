From Coq Require Import NArith Lia Reals Lra Permutation RelationClasses Sorted.
From Hofstadter.HalfQuantum Require Import Complex.
From Hofstadter.HalfQuantum Require Polar.
Require Import MoreList MoreReals.

Local Open Scope R.
Local Open Scope C.

(** Most of the time, the RtoC coercion already allows to parse numbers
    as C constants. But that only works when the context clearly indicates
    that a C term is expected. Several situations are hence problematic,
    e.g. inside lists, equality starting by a number, etc. Instead
    of writing RtoC manually in these cases, we add a proper Number Notation
    for C. *)


Local Set Warnings "-via-type-remapping,-via-type-mismatch".
Variant IC := ICR : IR -> IC.
Definition of_number n := ICR (Rdefinitions.of_number n).
Definition to_number '(ICR r) := Rdefinitions.to_number r.
Number Notation C of_number to_number (via IC mapping
 [RtoC => ICR,
  IZR => IRZ, Q2R => IRQ, Rmult => IRmult, Rdiv => IRdiv,
  Z.pow_pos => QArith_base.IZpow_pos,
  Z0 => QArith_base.IZ0,
  Zpos => QArith_base.IZpos,
  Zneg => QArith_base.IZneg
 ]) : C_scope.

Lemma Cinv_1 : /1 = 1.
Proof.
 now rewrite <- RtoC_inv, Rinv_1.
Qed.

(** Properties in Coquelicot and QuantumLib, for which a precondition
    can be removed now that [/0 = 0]
    (cf Coq 8.16 and the future Coquelicot 4) *)

(* RtoC_inv RtoC_div Cinv_0 without precond : already in QuantumLib *)

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

(* Also in QuantumLib, but with a wierd precondition *)
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
 unfold Cdiv. now rewrite Cmult_conj, Cinv_conj.
Qed.

(** Extra properties, not in Coquelicot nor in QuantumLib *)

Lemma Cinv_Copp c : /-c = -/c.
Proof.
 destruct (Ceq_dec c 0) as [->|N]; try lca. now field.
Qed.

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
   revert E. apply C1_nz. }
 apply Cmult_eq_reg_r with b; trivial. rewrite E. field; trivial.
Qed.

Lemma polar_eqn (c:C) : Cmod c * Cexp (Polar.get_arg c) = c.
Proof.
 destruct (Ceq_dec c 0) as [->|Hc].
 - now rewrite Cmod_0, Cmult_0_l.
 - now apply Polar.rect_to_polar_to_rect.
Qed.

Lemma Cmod_Re (c:C) : Re c = Cmod c -> Im c = 0%R.
Proof.
 intros E.
 assert (E' : (Cmod c ^2 = Re c ^2)%R) by now rewrite E.
 rewrite Cmod2_alt in E'.
 apply Rsqr_eq_0. rewrite Rsqr_pow2. lra.
Qed.

Lemma im_le_Cmod (c:C) : Rabs (Im c) <= Cmod c.
Proof.
 apply Rle_trans with (Rmax (Rabs (Re c)) (Rabs (Im c)));
  [ apply Rmax_r | apply Rmax_Cmod ].
Qed.

(* Note: QuantumLib.Complex.Cconj_eq_implies_real is just the <- direction *)
Lemma is_real_carac c : Im c = 0%R <-> Cconj c = c.
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
  Cmod (c - 1) = (Cmod c - 1)%R -> c = Cmod c.
Proof.
 intros E.
 assert (E' : (Cmod (c-1)^2 = (Cmod c - 1)^2)%R) by now rewrite E.
 clear E. rename E' into E.
 rewrite <- (Rsqr_pow2 (_ - _)) in E.
 unfold Rsqr in E. ring_simplify in E.
 rewrite !Cmod2_alt in E.
 replace (Re (c-1)) with (Re c - 1)%R in E.
 2:{ destruct c as (x,y). simpl. lra. }
 replace (Im (c-1)) with (Im c) in E.
 2:{ destruct c as (x,y). simpl. lra. }
 ring_simplify in E.
 assert (RE : Re c = Cmod c) by lra.
 assert (IM := Cmod_Re _ RE).
 rewrite <- RE. destruct c. simpl in *. now rewrite IM.
Qed.

(** Pushing RtoC inside or outside *)

(* NB: RtoC_pow was also in QuantumLib, but in the opposite direction *)

#[global] Hint Rewrite RtoC_plus RtoC_minus RtoC_opp RtoC_mult
 RtoC_inv RtoC_div RtoC_pow : RtoC.
Ltac rtoc := autorewrite with RtoC.

#[global] Hint Rewrite <- RtoC_plus RtoC_minus RtoC_opp RtoC_mult
 RtoC_inv RtoC_div RtoC_pow : CtoR.
Ltac ctor := autorewrite with CtoR.

(** Pushing Cconj inside or outside *)

#[global] Hint Rewrite Copp_conj Cplus_conj Cminus_conj Cmult_conj
 Cinv_conj Cdiv_conj Cpow_conj Cconj_R Ci_conj Cconj_conj : ConjIn.
Ltac conj_in := autorewrite with ConjIn.

#[global] Hint Rewrite <- Copp_conj Cplus_conj Cminus_conj Cmult_conj
 Cinv_conj Cdiv_conj Cpow_conj : ConjOut.
#[global] Hint Rewrite re_conj im_conj Cmod_conj Cconj_conj : ConjOut.
Ltac conj_out := autorewrite with ConjOut.


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
 forall n m, (n < m < length l)%nat -> R (nth n l 0) (nth m l 0).
Proof.
 split.
 - induction 1; simpl length; try lia.
   intros [|n] [|m]; try lia; intros; simpl nth.
   + rewrite Forall_forall in H0. apply H0. apply nth_In; lia.
   + apply IHStronglySorted; lia.
 - induction l; simpl length; intros H; constructor.
   + apply IHl. intros n m NM. apply (H (S n) (S m)). lia.
   + apply Forall_forall. intros x X.
     destruct (In_nth l x 0 X) as (n & LT & <-). apply (H O (S n)). lia.
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

Definition Cnth l i := nth i l 0.
Infix "@" := Cnth (at level 10) : C_scope.
