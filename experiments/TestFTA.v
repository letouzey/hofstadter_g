From Coq Require Import Reals Lra Permutation Lia.
From CoRN Require Import FTA Rreals Rreals_iso CRing_Homomorphisms R_morphism.
From Coquelicot Require Import Complex.
Require Import Lim.

Add Search Blacklist "RefLemma" "TaylorLemma" "RefSeparated" "_lemma".

(* Coquelicot Complex C seen as a CoRN CField. *)

Lemma C_is_CSetoid : is_CSetoid C eq (fun x y : C => x <> y).
Proof.
 constructor; repeat red; try congruence.
 - intros. destruct (Ceq_dec x z); [right|left]; subst; trivial.
 - unfold Not. split.
   * destruct (Ceq_dec x y); tauto.
   * tauto.
Qed.

Definition C_oid : CSetoid := Build_CSetoid _ _ _ C_is_CSetoid.
Canonical Structure C_oid. (* TODO : warnings (redundant canonical proj) *)
Canonical Structure C_Setoid := cs_crr C_oid. (* TODO idem *)

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

Definition C_csg : CSemiGroup := Build_CSemiGroup _ _ C_is_CSemiGroup.
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

Lemma c_opp [R : CRing] (a : R) : _C_ ([--] a) [=] [--] (_C_ a).
Proof.
 easy.
Qed.

Fixpoint linprod [R:CRing](l: list R) : cpoly_cring R :=
 match l with
 | nil => [1]
 | c::l => (_X_ [-] _C_ c) [*] linprod l
 end.

Lemma linprod_map [R S](h:RingHom R S)(l : list R) :
 cpoly_map h (linprod l) [=] linprod (List.map h l).
Proof.
 induction l.
 - simpl. algebra.
 - cbn [linprod List.map]. rewrite <- IHl.
   rewrite rh2. apply mult_wdl. clear IHl.
   unfold "[-]". rewrite rh1, <- !c_opp, cpoly_map_X, cpoly_map_C. algebra.
Qed.

Lemma linprod_app [R:CRing](l1 l2 : list R) :
 linprod (l1++l2) [=] linprod l1 [*] linprod l2.
Proof.
 induction l1; cbn [linprod app].
 - algebra.
 - now rewrite IHl1, mult_assoc.
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

(* TODO move elsewhere *)
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

Lemma count_occ_repeat [A](decA : forall x y : A, {x = y} + {x <> y})
  x n y :
  count_occ decA (repeat x n) y = if decA x y then n else O.
Proof.
 induction n; simpl; destruct decA; simpl; congruence.
Qed.

Lemma count_occ_remove [A](decA : forall x y : A, {x = y} + {x <> y})
  l x y :
  count_occ decA (remove decA x l) y =
   if decA x y then O else count_occ decA l y.
Proof.
 induction l; repeat (simpl; destruct decA); congruence.
Qed.

Lemma permfront [A](decA : forall x y : A, {x = y} + {x <> y})
 (l:list A)(x:A)(n := count_occ decA l x) :
 Permutation l (repeat x n ++ remove decA x l).
Proof.
 rewrite (Permutation_count_occ decA). intros y.
 rewrite count_occ_app, count_occ_remove, count_occ_repeat.
 unfold n. destruct decA; subst; lia.
Qed.

Lemma diff_opp [R](f : cpoly_cring R) :
 _D_ ([--] f) [=] [--] (_D_ f).
Proof.
 rewrite <- (mult_minus1 _ f), <- (mult_minus1 _ (_D_ f)).
 change [1] with (_C_ ([1]:R)).
 rewrite <- c_opp. rewrite diff_mult, diff_const.
 rewrite c_opp. rewrite cring_mult_zero_op. algebra.
Qed.

Lemma diff_minus [R](f g : cpoly_cring R) :
 _D_ (f [-] g) [=] _D_ f [-] _D_ g.
Proof.
 unfold "[-]". rewrite diff_plus, diff_opp. algebra.
Qed.

Lemma diff_linprod_repeat (c:C)(n:nat) :
 _D_ (linprod (repeat c (S n))) [=]
   _C_ (RtoC (INR (S n))) [*] (linprod (repeat c n)).
Proof.
 induction n.
 - cbn [repeat linprod].
   rewrite mult_one, diff_minus, diff_x, diff_const.
   change (INR 1) with (1%C). algebra.
 - set (n' := S n).
   cbn [repeat linprod].
   rewrite diff_mult. unfold n'. rewrite IHn.
   rewrite mult_assoc, (mult_commutes _ _ (_C_ _)), <- mult_assoc.
   change ((_[-]_) [*] linprod (repeat c n)) with (linprod (repeat c (S n))).
   rewrite <- ring_distl_unfolded.
   apply mult_wdl.
   rewrite diff_minus, diff_x, diff_const.
   rewrite !S_INR, !RtoC_plus, !c_plus. algebra.
Qed.

Lemma multiple_root (l : list C) c :
  (1 < count_occ Ceq_dec l c)%nat -> (_D_ (linprod l)) ! c = RtoC 0.
Proof.
 intros Hc.
 set (n := count_occ Ceq_dec l c) in *.
 rewrite (linprod_perm _ _ (permfront Ceq_dec l c)).
 fold n.
 set (l' := remove Ceq_dec c l). clearbody l'.
 rewrite linprod_app, diff_mult, plus_apply, !mult_apply.
 assert (E : forall m, (0<m)%nat -> (linprod (repeat c m)) ! c = RtoC 0).
 { intros. rewrite <- linprod_roots. destruct m. lia. now left. }
 rewrite E by lia.
 assert (E' : (_D_ (linprod (repeat c n))) ! c = RtoC 0).
 { destruct n as [|n]; try lia.
   rewrite diff_linprod_repeat, mult_apply, E by lia. apply Cmult_0_r. }
 now rewrite E', !Cmult_0_l, Cplus_0_l.
Qed.

Lemma separated_roots (l : list C) :
 (forall c, In c l -> (_D_ (linprod l)) ! c <> RtoC 0) -> NoDup l.
Proof.
 intros.
 apply (NoDup_count_occ' Ceq_dec).
 intros c Hc.
 assert (Hc' := Hc). rewrite (count_occ_In Ceq_dec) in Hc'.
 destruct (Nat.eq_dec (count_occ Ceq_dec l c) 1). trivial.
 specialize (H c Hc). rewrite multiple_root in H by lia. easy.
Qed.

Lemma monom_add [R:CRing](a b:R)(k:nat) :
 monom a k [+] monom b k [=] monom (a[+]b) k.
Proof.
 induction k.
 - algebra.
 - rewrite !monom_S, <- IHk. algebra.
Qed.


Lemma diff_monom [R:CRing](a:R)(k:nat) :
 _D_ (monom a k) [=] (nring k) [*] monom a (pred k).
Proof.
 induction k.
 - simpl. algebra.
 - simpl pred.
   rewrite monom_S, diff_mult, diff_x, IHk.
   cbn [nring].
   rewrite mult_assoc, (mult_commutes _ _X_), <- mult_assoc, <- monom_S.
   destruct k.
   + simpl. algebra.
   + cbn [pred nring]. rewrite <- ring_distl_unfolded. algebra.
Qed.

Lemma nring_C n : @nring C_fd n = RtoC (INR n).
Proof.
 induction n; cbn [nring] in *; trivial.
 now rewrite IHn, S_INR, RtoC_plus.
Qed.

Lemma nring_CX n : @nring CX n [=] _C_ (RtoC (INR n)).
Proof.
 induction n; cbn [nring] in *; try easy.
 rewrite IHn, S_INR, RtoC_plus. algebra.
Qed.

Lemma ThePoly_separated_roots k :
  { l | length l = S k /\ NoDup l /\ ThePoly k [=] linprod l }.
Proof.
 destruct (split_CX (S k) (ThePoly k)) as (l & Hl & E).
 - apply ThePoly_monic.
 - exists l; repeat split; trivial.
   apply separated_roots. intros c Hc.
   rewrite <- E. unfold ThePoly.
   rewrite !diff_minus, diff_one, !diff_monom.
   rewrite Nat.add_1_r. simpl pred.
   rewrite cg_inv_zero, minus_apply, !mult_apply, !monom_apply.
   rewrite !nring_CX, !c_apply.
   change [1] with (RtoC 1). rewrite !Cmult_1_l.
   change (INR (S k) * (c^k) - INR k * (c ^ pred k) <> 0)%C.
   destruct (Nat.eq_dec k 0) as [->|Hk].
   + simpl. intro H. ring_simplify in H. now apply C1_nz.
   + replace k with (S (pred k)) at 2 by lia.
     intro H. ring_simplify in H.
     rewrite Cpow_S, Cmult_assoc in H.
     rewrite <- Cmult_plus_distr_r in H.
     rewrite Cmult_integral in H. destruct H as [H|H].
     * replace (-1 * INR k)%C with (-INR k)%C in H by ring.
       change (INR (S k) * c - INR k = 0)%C in H.
       rewrite <- Ceq_minus in H.
       assert (Hc' : c = (INR k / INR (S k))%C).
       { rewrite <- H. field. intros H'. apply RtoC_inj in H'.
         generalize (RSpos k). lra. }
       rewrite <- RtoC_div in Hc'. 2:generalize (RSpos k); lra.
       revert Hc.
       rewrite linprod_roots, <- E. unfold ThePoly.
       rewrite !minus_apply, one_apply, !monom_apply.
       change [1] with (RtoC 1). rewrite !Cmult_1_l.
       rewrite Nat.add_1_r.
       change (c^S k - c^k - 1 <> 0)%C.
       replace (c^S k - c^k - 1)%C with (c^S k - (c^k + 1))%C by ring.
       apply Cminus_eq_contra. intro Hc.
       set (r := Rdiv _ _) in *.
       assert (r <= 1).
       { unfold r. apply Rcomplements.Rle_div_l.
         generalize (RSpos k); lra. rewrite S_INR; lra. }
       subst c. rewrite <- !RtoC_pow, <- RtoC_plus in Hc.
       apply RtoC_inj in Hc.
       apply mu_unique in Hc. generalize (mu_itvl k); lra.
       apply Rcomplements.Rdiv_le_0_compat. apply pos_INR. apply RSpos.
     * revert H. apply Cpow_nz.
       contradict Hc. subst c. rewrite linprod_roots, <- E.
       unfold ThePoly.
       rewrite !minus_apply, one_apply, !monom_apply.
       destruct k; try lia.
       simpl. rewrite !Cmult_0_l, !Cmult_0_r.
       apply Cminus_eq_contra.
       change (0-0 <> 1)%C. unfold Cminus. rewrite Cplus_opp_r.
       intro H. symmetry in H. now apply C1_nz.
Qed.

(* Derivées et racines simples : Au moins dans le cas particulier ThePoly *)

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
