From Coq Require Import Reals Lra Permutation Lia.
From CoRN Require Import FTA Rreals Rreals_iso CRing_Homomorphisms R_morphism.
From Coquelicot Require Import Complex.

Local Open Scope R.

(** * Revisiting CoRN FTA theorem for Coquelicot complex C *)

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

(** First, Coquelicot Complex C seen as a CoRN CField. *)

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

(** Isomorphism between C and CC. First C_CC is an Ring Homomorphism : *)

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

(** Now CCasC is also a Ring Homomorphism *)

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

(* TODO: Possible extensions : things like fun_pres_Lim, and preservations
   of Re Im norm conjugate etc *)

(** Following R_morphism.Isomomorphism but on C, and without any explicit
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

(** Polynomials with respect to ring homomorphisms *)

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

(** Polynomials C[X] *)
Definition CX := cpoly_cring C_fd.

(** FTA theorem for Coquelicot C structure (based on Coq reals R) *)

Theorem Coq_FTA : forall f : CX, nonConst C_fd f -> {z : C & f ! z [=] [0]}.
Proof.
 intros f Hf.
 destruct (FTA (cpoly_map CasCC_Hom f)) as (z,Hz).
 - apply nonConst_map2 with CCasC_Hom; trivial. apply inversity_lft.
 - exists (CCasC z).
   rewrite <- (CCasCasCC z), <- cpoly_map_apply in Hz.
   rewrite <- CasCC_0 in Hz. now apply CasCC_inj.
Qed.

(** Some complements on polynomials (monic, apply, monom, ...) *)

Lemma c_opp [R : CRing] (a : R) : _C_ ([--] a) [=] [--] (_C_ a).
Proof.
 easy.
Qed.

Lemma c_minus [R : CRing] (a b : R) : _C_ (a [-] b) [=] _C_ a [-] _C_ b.
Proof.
 unfold "[-]". now rewrite c_plus, c_opp.
Qed.

(* Unused for now.
   TODO : rename k into n in this lemma, and algebra won't work ?! *)

Lemma monom_add_coeff [R:CRing](a b:R)(k:nat) :
 monom a k [+] monom b k [=] monom (a[+]b) k.
Proof.
 induction k; rewrite ?monom_S, <- ?IHk; algebra.
Qed.

Lemma monom_apply (a c:C)(n:nat) : (monom a n) ! c = (a*c^n)%C.
Proof.
 induction n; simpl in *; rewrite ?IHn; ring.
Qed.

Lemma monom_degree_eq (a:C)(n:nat) : a<>0%R -> degree n (monom a n).
Proof.
 intros Ha. split. rewrite monom_coeff. apply Ha.
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

(** [linprod] : from a list of roots [r1]..[rn] to
    polynomial [(X-r1)...(X-rn)] *)

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
   rewrite rh_pres_mult. apply mult_wdl. clear IHl. unfold "[-]".
   rewrite rh_pres_plus, <- !c_opp, cpoly_map_X, cpoly_map_C. algebra.
Qed.

Lemma linprod_app [R:CRing](l1 l2 : list R) :
 linprod (l1++l2) [=] linprod l1 [*] linprod l2.
Proof.
 induction l1; cbn [linprod app].
 - algebra.
 - now rewrite IHl1, mult_assoc.
Qed.

(** In [linprod] we can permute freely the roots *)

Lemma linprod_perm [R:CRing](l l' : list R) :
 Permutation l l' -> linprod l [=] linprod l'.
Proof.
 induction 1; cbn [linprod].
 - algebra.
 - rewrite IHPermutation. algebra.
 - rewrite !mult_assoc. algebra.
 - now rewrite IHPermutation1, IHPermutation2.
Qed.

(** The roots of [linprod l] are exactly the elements of [l]. *)

Definition CXRoot (c:C) (f:CX) := f ! c = RtoC 0.

Lemma CXRoot_wd c f f' : f [=] f' -> CXRoot c f -> CXRoot c f'.
Proof.
 unfold CXRoot. now intros <-.
Qed.

Global Instance: Proper (eq ==> @st_eq _ ==> iff) CXRoot.
Proof. intros c c' <- f f'. split; now apply CXRoot_wd. Qed.

Lemma linprod_roots (l : list C) c : In c l <-> CXRoot c (linprod l).
Proof.
 revert c. induction l; unfold CXRoot; cbn [linprod In].
 - intros c. simpl. rewrite Cmult_0_r, Cplus_0_r. split. easy. apply C1_nz.
 - intros c. rewrite IHl, mult_apply, Cmult_integral. clear IHl.
   split; destruct 1 as [A|B]; (now right) || left.
   + subst. simpl. ring.
   + simpl in A. ring_simplify in A. rewrite Cplus_comm in A.
     symmetry. apply Ceq_minus. now ring_simplify.
Qed.

(** Repeating FTA for splitting a polynomial into basic factors.
    Version for CCX, the polynomials on CoRN C.
    The list of roots isn't sorted, and may contains the roots several times
    (the number of occurrences is the multiplicity). *)

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

(** Same result, but for CX (polynomials on Coquelicot C). *)

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

(* TODO: move elsewhere *)
Lemma count_occ_repeat [A](decA : forall x y : A, {x = y} + {x <> y})
  x n y :
  count_occ decA (repeat x n) y = if decA x y then n else O.
Proof.
 induction n; simpl; destruct decA; simpl; congruence.
Qed.

(* TODO: move elsewhere *)
Lemma count_occ_remove [A](decA : forall x y : A, {x = y} + {x <> y})
  l x y :
  count_occ decA (remove decA x l) y =
   if decA x y then O else count_occ decA l y.
Proof.
 induction l; repeat (simpl; destruct decA); congruence.
Qed.

(** In a list, moving all the occurrences of a value at front. *)

Definition movefront [A](decA : forall x y : A, {x = y} + {x <> y}) x l :=
 repeat x (count_occ decA l x) ++ remove decA x l.

Lemma movefront_perm [A](decA : forall x y : A, {x = y} + {x <> y}) x l :
 Permutation l (movefront decA x l).
Proof.
 rewrite (Permutation_count_occ decA). intros y. unfold movefront.
 rewrite count_occ_app, count_occ_remove, count_occ_repeat.
 destruct decA; subst; lia.
Qed.

(** Complements on [_D_] (derivative of a polynomial) *)

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

(** A multiple root of a polynomial is also a root of its derivative. *)

Lemma multiple_root_diff (l : list C) c :
  (1 < count_occ Ceq_dec l c)%nat -> CXRoot c (_D_ (linprod l)).
Proof.
 intros Hc. unfold CXRoot.
 set (n := count_occ Ceq_dec l c) in *.
 rewrite (linprod_perm _ _ (movefront_perm Ceq_dec c l)).
 unfold movefront. fold n. set (l' := remove Ceq_dec c l). clearbody l'.
 rewrite linprod_app, diff_mult, plus_apply, !mult_apply.
 assert (E : forall m, (0<m)%nat -> CXRoot c (linprod (repeat c m))).
 { intros. rewrite <- linprod_roots. destruct m. lia. now left. }
 rewrite E by lia.
 assert (E' : CXRoot c (_D_ (linprod (repeat c n)))).
 { destruct n as [|n]; try lia. unfold CXRoot.
   rewrite diff_linprod_repeat, mult_apply, E by lia. apply Cmult_0_r. }
 now rewrite E', !Cmult_0_l, Cplus_0_l.
Qed.

(** A polynomial without common roots with its derivative has only
    simple roots. First, version for [linprod] polynomials. *)

Lemma linprod_separated_roots (l : list C) :
 (forall c, CXRoot c (linprod l) -> ~CXRoot c (_D_ (linprod l))) -> NoDup l.
Proof.
 intros.
 apply (NoDup_count_occ' Ceq_dec).
 intros c Hc.
 assert (Hc' := Hc). rewrite (count_occ_In Ceq_dec) in Hc'.
 destruct (Nat.eq_dec (count_occ Ceq_dec l c) 1). trivial.
 apply linprod_roots in Hc. specialize (H c Hc).
 destruct H. apply multiple_root_diff. lia.
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

(** A polynomial without common roots with its derivative has only
    simple roots. Version for monic polynomial. *)

Lemma separated_roots k (f:CX) :
 monic k f ->
 (forall c, CXRoot c f -> ~CXRoot c (_D_ f)) ->
 { l | length l = k /\ NoDup l /\ f [=] linprod l }.
Proof.
 intros Hf Df.
 destruct (split_CX k f Hf) as (l & Hl & E).
 exists l; repeat split; trivial.
 apply linprod_separated_roots. intros c. rewrite <- E. apply Df.
Qed.

(* TODO: full treatment of multiplicity *)

(* TODO:
   Les racines complexes non réelles d'un poly à coeffs réels vont par deux

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
