From Coq Require Import Reals Lra Permutation.
From CoRN Require Import FTA Rreals Rreals_iso CRing_Homomorphisms R_morphism.
From Coquelicot Require Import Complex.

(* Coquelicot Complex C seen as a CoRN CField. *)

Lemma C_is_CSetoid : is_CSetoid C (@eq C) (fun x y : C => x <> y).
Proof.
 constructor; repeat red; try congruence.
 - intros. destruct (Ceq_dec x z); [right|left]; subst; trivial.
 - unfold Not. split.
   * destruct (Ceq_dec x y); tauto.
   * tauto.
Qed.

Definition C_oid : CSetoid :=
 Build_CSetoid C (@eq C) (fun x y => x <> y) C_is_CSetoid.
Canonical Structure C_oid.
Canonical Structure C_Setoid := cs_crr C_oid.

Lemma CPlus_is_setoid_bin_fun:
 bin_fun_strext C_oid C_oid C_oid Cplus.
Proof.
 unfold bin_fun_strext.
 intros x1 x2 y1 y2 H.
 unfold "[#]" in *. simpl in *.
 destruct (Ceq_dec x1 x2); [subst|now left].
 destruct (Ceq_dec y1 y2); [subst|now right].
 now destruct H.
Qed.

Definition CPlus_sbinfun : CSetoid_bin_op C_oid :=
 Build_CSetoid_bin_op _ Cplus CPlus_is_setoid_bin_fun.

Lemma C_is_CSemiGroup : is_CSemiGroup _ CPlus_sbinfun.
Proof.
 repeat red. unfold C_oid. simpl. intros. ring.
Qed.

Definition C_csg : CSemiGroup :=
  Build_CSemiGroup _ CPlus_sbinfun C_is_CSemiGroup.
Canonical Structure C_csg.

Lemma C_is_CMonoid : is_CMonoid _ (RtoC 0).
Proof.
 constructor; repeat red; simpl; intros; ring.
Qed.

Definition C_mon : CMonoid := Build_CMonoid _ _ C_is_CMonoid.
Canonical Structure C_mon.

Lemma CNeg_sunop : fun_strext Copp.
Proof.
 unfold fun_strext. intros x y. unfold "[#]"; simpl. now intros ? ->.
Qed.

Definition CNeg_op : CSetoid_un_op C_oid :=
 Build_CSetoid_un_op _ Copp CNeg_sunop.

Lemma C_is_Group : is_CGroup C_mon CNeg_op.
Proof.
 repeat red. unfold C_mon; simpl. split; ring.
Qed.

Definition C_grp := Build_CGroup _ _ C_is_Group.
Canonical Structure C_grp.

Lemma C_is_AbGroup : is_CAbGroup C_grp.
Proof.
 exact Cplus_comm.
Qed.

Definition C_abg := Build_CAbGroup _ C_is_AbGroup.
Canonical Structure C_abg.

Lemma CMul_is_csbinop : bin_fun_strext _ _ _ Cmult.
Proof.
 red. unfold C_oid; simpl. intros x1 x2 y1 y2 H.
 destruct (Ceq_dec x1 x2); [subst|now left].
 destruct (Ceq_dec y1 y2); [subst|now right].
 now destruct H.
Qed.

Definition CMul_op : CSetoid_bin_op C_mon :=
 Build_CSetoid_bin_op C_oid Cmult CMul_is_csbinop.

Lemma CMul_assoc : associative (S:=C_abg) CMul_op.
Proof.
 exact Cmult_assoc.
Qed.

Lemma C_is_Ring : is_CRing C_abg (RtoC 1) CMul_op.
Proof.
 exists CMul_assoc.
 - constructor.
   + exact Cmult_1_r.
   + exact Cmult_1_l.
 - exact Cmult_comm.
 - exact Cmult_plus_distr_l.
 - exact C1_nz.
Qed.

Definition C_rg := Build_CRing _ _ _ C_is_Ring.
Canonical Structure C_rg.

Definition Crecip :
 forall x : C_rg, x [#] [0] -> C_rg := fun x _ => Cinv x.

Lemma C_is_Field : is_CField C_rg Crecip.
Proof.
 constructor.
 - now apply Cinv_r.
 - now apply Cinv_l.
Qed.

Lemma C_is_Field2: forall (x y : C_rg) (x_ : x[#][0]) (y_ : y[#][0]),
   Crecip x x_[#]Crecip y y_ -> x[#]y.
Proof.
 intros x y x1 y1 H. unfold "[#]", Crecip in *. simpl in *.
 contradict H. now subst.
Qed.

Definition C_fd : CField :=
 Build_CField _ _ C_is_Field C_is_Field2.
Canonical Structure C_fd.

(* Isomorphism between C and CC. First C_CC is an Ring Homomorphism : *)

Definition CasCC : C -> CC :=
  fun (c:C) => Build_CC_set (RasIR (Re c)) (RasIR (Im c)).

Definition CCasC : CC -> C :=
  fun (c:CC) => (IRasR (CComplex.Re c), IRasR (CComplex.Im c)).

Lemma CasCCasC (c:C) : CCasC (CasCC c) = c.
Proof.
 destruct c as (x,y). unfold CCasC, CasCC; simpl. now rewrite !RasIRasR_id.
Qed.

Lemma CCasCasCC (c:CC) : CasCC (CCasC c) [=] c.
Proof.
 destruct c as (x,y). unfold CCasC, CasCC; simpl. unfold cc_eq. simpl.
 split; apply IRasRasIR_id.
Qed.

Lemma CasCC_inj (c c':C) : CasCC c [=] CasCC c' -> c=c'.
Proof.
 destruct c as (x,y), c' as (x',y'). intros (H,H'). simpl in *.
 apply R_eq_as_IR_back in H,H'. congruence.
Qed.

Lemma CasCC_0 : CasCC 0%R [=] [0].
Proof.
 red; simpl. unfold cc_eq. simpl. now rewrite R_Zero_as_IR.
Qed.

Lemma CasCC_1 : CasCC 1%R [=] [1].
Proof.
 red; simpl. unfold cc_eq. simpl. now rewrite R_Zero_as_IR, R_One_as_IR.
Qed.

Lemma CCasC_0 : CCasC [0] = 0%R.
Proof.
 unfold CCasC. simpl. now rewrite IR_Zero_as_R.
Qed.

Lemma CCasC_1 : CCasC [1] = 1%R.
Proof.
 unfold CCasC. simpl. now rewrite IR_One_as_R, IR_Zero_as_R.
Qed.

Lemma CasCC_strext : fun_strext CasCC.
Proof.
 red. unfold C_oid. simpl. unfold cc_ap. simpl.
 intros (x1,x2) (y1,y2). simpl.
 intros [H|H]; apply R_ap_as_IR in H; congruence.
Qed.

Lemma CasCC_plus (c c' : C) : CasCC (c+c') [=] CasCC c [+] CasCC c'.
Proof.
 destruct c as (x1,x2), c' as (y1,y2). simpl. unfold cc_eq, CasCC. simpl.
 now rewrite !R_plus_as_IR.
Qed.

Lemma CasCC_mult (c c' : C) : CasCC (c*c') [=] CasCC c [*] CasCC c'.
 destruct c as (x1,x2), c' as (y1,y2). simpl. unfold cc_eq, CasCC. simpl.
 now rewrite R_minus_as_IR, R_plus_as_IR, !R_mult_as_IR.
Qed.

Definition CasCC_funoid : CSetoid_fun C CC :=
 Build_CSetoid_fun _ _ CasCC CasCC_strext.

Definition CasCC_Hom : RingHom C_fd CC :=
 Build_RingHom _ _ CasCC_funoid CasCC_plus CasCC_mult CasCC_1.

(* Now CCasC is also a Ring Homomorphism *)

Lemma CCasC_strext : fun_strext CCasC.
Proof.
 red. unfold CC. simpl. unfold cc_ap.
 intros (x1,x2) (y1,y2) N. simpl in *. unfold CCasC in *; simpl in *.
 destruct (Req_EM_T (IRasR x1) (IRasR y1)) as [E1|N1].
 - destruct (Req_EM_T (IRasR x2) (IRasR y2)) as [E2|N2].
   + destruct N. now f_equal.
   + right. apply (map_strext _ _ (iso_map_rht _ _ RIR_iso)). exact N2.
 - left. apply (map_strext _ _ (iso_map_rht _ _ RIR_iso)). exact N1.
Qed.

Lemma CCasC_plus (c c' : CC) : CCasC (c [+] c') = (CCasC c + CCasC c')%C.
Proof.
 destruct c as (x1,x2), c' as (y1,y2). simpl. unfold CCasC, Cplus. simpl.
 now rewrite !IR_plus_as_R.
Qed.

Lemma CCasC_mult (c c' : CC) : CCasC (c [*] c') = (CCasC c * CCasC c')%C.
Proof.
 destruct c as (x1,x2), c' as (y1,y2). simpl. unfold CCasC, Cmult. simpl.
 now rewrite IR_minus_as_R, IR_plus_as_R, !IR_mult_as_R.
Qed.

Definition CCasC_funoid : CSetoid_fun CC C_fd :=
 Build_CSetoid_fun _ _ CCasC CCasC_strext.

Definition CCasC_Hom : RingHom CC C_fd :=
 Build_RingHom _ _ CCasC_funoid CCasC_plus CCasC_mult CCasC_1.

(* Possible extensions : things like fun_pres_Lim, and preservations
   of Re Im norm conjugate etc *)

(* Following R_morphism.Isomomorphism but on C, and without explicit
   structure *)

Definition ringmap_is_id (R : CRing)(f : R -> R) := forall x : R, f x[=]x.

Lemma inversity_lft :
  ringmap_is_id _ (RHcompose _ _ _ CCasC_Hom CasCC_Hom).
Proof.
 exact CasCCasC.
Qed.

Lemma inversity_rht :
  ringmap_is_id _ (RHcompose _ _ _ CasCC_Hom CCasC_Hom).
Proof.
 exact CCasCasCC.
Qed.

(* Polynomials with respect to ring homomorphisms *)

Lemma cpoly_map_id [R:CRing](h:RingHom R R) :
 ringmap_is_id _ h -> forall f : cpoly_cring R, cpoly_map h f [=] f.
Proof.
 now induction f.
Qed.

Lemma coeff_map [R S:CRing](h:RingHom R S)(f : cpoly_cring R) n :
 nth_coeff n (cpoly_map h f) [=] h (nth_coeff n f).
Proof.
 revert n.
 induction f; simpl.
 - algebra.
 - now destruct n.
Qed.

Lemma nonConst_wd [R:CRing](p q : cpoly_cring R) :
  p[=]q -> nonConst _ p -> nonConst _ q.
Proof.
 intros E (n,Hn,Hn'). exists n; trivial. now astepl (nth_coeff n p).
Qed.

Lemma nonConst_map [R S:CRing](h:RingHom R S) :
 forall f : cpoly_cring R, nonConst S (cpoly_map h f) -> nonConst R f.
Proof.
 intros f (n,Hn,Hn'). exists n; trivial.
 apply (rh_apzero _ _ h).
 stepl (nth_coeff n (cpoly_map h f)); trivial.
 apply coeff_map.
Qed.

Lemma nonConst_map2 [R S:CRing](h:RingHom R S)(g:RingHom S R) :
 ringmap_is_id R (RHcompose _ _ _ g h) ->
 forall f : cpoly_cring R, nonConst R f -> nonConst S (cpoly_map h f).
Proof.
 intros E f NC.
 apply (nonConst_map g). apply nonConst_wd with f; trivial.
 rewrite <- cpoly_map_compose. symmetry. now apply cpoly_map_id.
Qed.

(* Finally, FTA theorem for Coquelicot C structure (based on Coq reals R) *)

Theorem Coq_FTA : forall f : cpoly_cring C_fd,
       nonConst C_fd f -> {z : C_fd & f ! z [=] [0]}.
Proof.
 intros f Hf.
 destruct (FTA (cpoly_map CasCC_Hom f)) as (z,Hz).
 - apply nonConst_map2 with CCasC_Hom; trivial. apply inversity_lft.
 - exists (CCasC z).
   rewrite <- (CCasCasCC z), <- cpoly_map_apply in Hz.
   rewrite <- CasCC_0 in Hz. now apply CasCC_inj.
Qed.

(* TODO : Factorisation d'un polynôme par (X-root) ...
   et repetition tant que degré non-nul

   TODO : passer par FTA_1 ?
   f = f1*f2 avec f1 de degré <= 1 et f2 de degré moins que f *)

(* Example : *)

Definition CX := cpoly_cring C_fd.

Definition ThePoly (k:nat) : CX := monom [1] (k+1) [-] monom [1] k [-] [1].

Require Import Lim.

Lemma monom_apply (a c:C)(n:nat) : (monom a n) ! c = (a*c^n)%C.
Proof.
 induction n; simpl in *; rewrite ?IHn; ring.
Qed.

Lemma mu_is_root (k:nat) : (ThePoly k) ! (RtoC (mu k)) = RtoC 0.
Proof.
 unfold ThePoly. rewrite !minus_apply, !monom_apply. simpl.
 unfold "[-]". simpl.
 rewrite Nat.add_1_r. ring_simplify.
 rewrite <- RtoC_pow, mu_carac. rewrite RtoC_plus, RtoC_pow. ring.
Qed.

Lemma monom_degree_eq (a:C)(n:nat) : a<>0%R -> degree n (monom a n).
Proof.
 intros Ha. split. rewrite monom_coeff. apply Ha.
 apply monom_degree.
Qed.

Lemma ThePoly_deg (k:nat) : degree (S k) (ThePoly k).
Proof.
 unfold ThePoly.
 apply degree_minus_lft with O; auto with *.
 - red. simpl. destruct m. inversion 1. trivial.
 - apply degree_minus_lft with k; auto with *.
   apply monom_degree.
   rewrite Nat.add_1_r.
   apply monom_degree_eq. apply C1_nz.
Qed.

Lemma ThePoly_monic (k:nat) : monic (S k) (ThePoly k).
Proof.
 unfold ThePoly. apply monic_minus with O; auto with *.
 - red. simpl. destruct m. inversion 1. trivial.
 - apply monic_minus with k; auto with *.
   apply monom_degree.
   rewrite Nat.add_1_r. split.
   now rewrite monom_coeff.
   apply monom_degree.
Qed.

Lemma monic_nonConst [R : CRing] (f : cpoly_cring R)(n:nat) :
  monic (S n) f -> nonConst _ f.
Proof.
 intros (A,B). exists (S n); auto with *. stepl ([1]:R); algebra.
Qed.

Lemma monic_degree [R : CRing] (f : cpoly_cring R)(n:nat) :
 monic n f -> degree n f.
Proof.
 intros (A,B). split; trivial. stepl ([1]:R); algebra.
Qed.

Lemma ThePoly_nonConst (k:nat) : nonConst _ (ThePoly k).
Proof.
 apply monic_nonConst with k. apply ThePoly_monic.
Qed.

Fixpoint linprod [R:CRing](l: list R) : cpoly_cring R :=
 match l with
 | nil => [1]
 | c::l => (_X_ [-] _C_ c) [*] linprod l
 end.

Lemma c_opp [R : CRing] (a : R) : _C_ ([--] a) [=] [--] (_C_ a).
Proof.
 easy.
Qed.

Lemma split_CCX k (f:CCX) :
 monic k f -> { l:list CC | length l = k /\ f [=] linprod l }.
Proof.
 revert f.
 induction k.
 - intros f (A,B). exists nil. split; auto. simpl linprod.
   apply degree_le_zero in B. destruct B as (c,Hc).
   now rewrite Hc in *.
 - intros f M.
   destruct (poly_apzero_CC f (monic_apzero _ _ _ M)) as (c & Hc).
   assert (D := monic_degree _ _ M).
   destruct (FTA_reg' f k D) as (f1,Hf1,(f2,Hf2,E)).
   destruct Hf1 as (Hf1,Hf1').
   destruct (degree_le_1_imp _ f1 Hf1') as (a & b & Ef1).
   assert (Ha : a [#] [0]).
   { stepl (nth_coeff 1 f1); trivial.
     rewrite Ef1. change (a [*] [1] [=] a). algebra. }
   set (inva := [1][/]a[//]Ha).
   set (b' := [--] b [*] inva).
   set (f2' := f2 [*] _C_ a).
   assert (D2' : degree_le k f2').
   { unfold f2'. apply degree_le_mult_constant_r, Hf2. }
   assert (M' : monic k f2').
   { split; trivial.
     unfold f2' in *.
     rewrite nth_coeff_p_mult_c_.
     generalize (nth_coeff_complicated _ a b f2 k).
     rewrite <- Ef1, <- E. destruct M as (->,_).
     destruct Hf2 as (_,D2). rewrite (D2 (S k)) by auto with arith.
     rewrite cring_mult_zero, cm_rht_unit_unfolded.
     now rewrite mult_commutes. }
   destruct (IHk f2' M') as (l & Hl & Ef2').
   exists (b'::l). split. simpl; f_equal; trivial.
   change (f [=] (_X_ [-] _C_ b')[*]linprod l).
   rewrite <- Ef2'.
   rewrite E, Ef1. unfold f2'.
   assert (Hb : b [=] [--] b' [*] a).
   { unfold b', inva.
     rewrite 3 cring_inv_mult_rht, cg_inv_inv.
     unfold cf_div.
     rewrite <- !mult_assoc.
     rewrite field_mult_inv_op.
     now rewrite !mult_one. }
   rewrite Hb. rewrite c_mult.
   change (_C_ [--] b') with ([--] (_C_ b')).
   rewrite (mult_commutes _ f2).
   rewrite mult_assoc.
   apply mult_wd; try easy.
   rewrite (mult_commutes _ (_C_ a)).
   rewrite cring_inv_mult_rht.
   now rewrite ring_distr2.
Qed.

Lemma degree_le_map [R S](h:RingHom R S)(f : cpoly_cring R) k :
 degree_le k f -> degree_le k (cpoly_map h f).
Proof.
 unfold degree_le; intros H m Hm. rewrite coeff_map, H. algebra. trivial.
Qed.

Lemma monic_map [R S](h:RingHom R S)(f : cpoly_cring R) k :
 monic k f -> monic k (cpoly_map h f).
Proof.
 intros (A,B). split.
 rewrite coeff_map, A. algebra.
 now apply degree_le_map.
Qed.

Lemma linprod_map [R S](h:RingHom R S)(l : list R) :
 cpoly_map h (linprod l) [=] linprod (List.map h l).
Proof.
 induction l.
 - simpl. algebra.
 - cbn [linprod List.map]. rewrite <- IHl.
   rewrite rh2. apply mult_wdl. clear IHl.
   unfold "[-]". rewrite rh1, <- !c_opp, cpoly_map_X, cpoly_map_C. algebra.
Qed.

Lemma split_CX k (f:CX) :
 monic k f -> { l:list C | length l = k /\ f [=] linprod l }.
Proof.
 intros Hf.
 destruct (split_CCX k (cpoly_map CasCC_Hom f)) as (l & Hl & E).
 - now apply monic_map.
 - exists (List.map CCasC l); split.
   + now rewrite map_length.
   + stepl (cpoly_map CCasC_Hom (cpoly_map CasCC_Hom f)).
     * rewrite E, linprod_map. now rewrite map_ext with (g:=CCasC).
     * rewrite <- cpoly_map_compose.
       apply cpoly_map_id, inversity_lft.
Qed.


Lemma linprod_perm (l l' : list C) :
 Permutation l l' -> linprod l [=] linprod l'.
Proof.
 induction 1; cbn [linprod].
 - algebra.
 - rewrite IHPermutation. algebra.
 - rewrite !mult_assoc. algebra.
 - now rewrite IHPermutation1, IHPermutation2.
Qed.

Lemma Cmult_integral (c1 c2 : C) :
 (c1 * c2 = 0 <-> c1 = 0 \/ c2 = 0)%C.
Proof.
 split.
 - destruct (Ceq_dec c1 0) as [->|H1]. now left.
   destruct (Ceq_dec c2 0) as [->|H2]. now right.
   intros H. now destruct (Cmult_neq_0 c1 c2).
 - intros [-> | ->]; ring.
Qed.

Lemma linprod_roots (l : list C) :
 forall c, In c l <-> (linprod l) ! c = RtoC 0.
Proof.
 induction l; cbn [linprod In].
 - intros c. simpl. rewrite Cmult_0_r, Cplus_0_r. split. easy. apply C1_nz.
 - intros c. rewrite IHl, mult_apply, Cmult_integral. clear IHl.
   split; destruct 1 as [A|B]; (now right) || left.
   + subst. simpl. ring.
   + simpl in A. ring_simplify in A. rewrite Cplus_comm in A.
     symmetry. apply Ceq_minus. now ring_simplify.
Qed.

(* Derivées et racines simples ? *)

(* Les racines complexes non réelles d'un poly à coeffs réels vont par deux

Lemma apply_conj (f:CX)(c:C) : (* Todo : dire que f a des coeffs reels *)
 Cconj (f ! c) = f ! (Cconj c).
Proof.
 induction f; simpl.
 - compute; f_equal; lra.
 - rewrite Cplus_conj, Cmult_conj.
*)

(* liens : https://github.com/coq-community/awesome-coq

   https://valentinblot.org/pro/M1_report.pdf : Cayley-Hamilton, Liouville,
   etc
*)
