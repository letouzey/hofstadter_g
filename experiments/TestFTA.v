From Coq Require Import Reals Lra.
From CoRN Require Import FTA Rreals Rreals_iso.
From Coquelicot Require Import Complex.
Check FTA.

(* liens : https://github.com/coq-community/awesome-coq *)

(*
FTA
     : forall f : cpoly_cring CC,
       nonConst CC f -> {z : CC & f ! z [=] [0]}
*)

(* Print Assumptions FTA. *)

Print CC.

Print cc_cfield.
Print cc_cring.
Print cc_cabgroup.
Print CC_set.
Check CauchySeq.IR.

(* Rreals_iso *)
Locate R. (* C'est celui de Coq, maintenant une implem abstraite via dedekind *)
Print RasIR. (* R -> CauchySeq.IR *)
Print IRasR. (* CauchySeq.IR -> R *)

Print RIR_iso.

Print R_morphism.Isomorphism.

Print RReals. (* hierarchie par dessus R de Coq *)
Print ROrdField.
Print RField.
Print RRing.
Print RAbGroup.
Print RSetoid.
Print RCSetoid.


Print cpoly_cring. (* Anneau des polynomes sur un anneau *)
Print cpoly_cabgroup.
Print cpoly_cgroup.
Print cpoly_csetoid. (* Tout est basé sur cpoly, le type algébrique *)
Print cpoly.
(* 
cpoly_zero : cpoly CR | cpoly_linear : CR -> cpoly CR -> cpoly CR.
*)

(* ! c'est cpoly_apply_fun *)
(* cpoly_apply *)

(*
cpoly_apply =
fun CR : CRing =>
fix cpoly_apply (p : cpoly_cring CR) (x : CR) {struct p} : CR :=
  match p with
  | cpoly_zero _ => [0]
  | cpoly_linear _ c p1 => c [+] x [*] cpoly_apply p1 x
  end
     : forall CR : CRing, cpoly_cring CR -> CR -> CR
*)


Print nonConst.
(* fun (R : CRing) (p : cpoly_cring R) =>
{n : nat | 0 < n | nth_coeff n p [#] [0]}
     : forall R : CRing, cpoly_cring R -> CProp *)
Print nth_coeff.

(* Coquelicot Complex C is a CoRN CComplex. *)

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

Lemma C_is_CMonoid : is_CMonoid _ (RtoC 0%R).
Proof.
 constructor; repeat red; simpl; intros; ring.
Qed.

Definition C_mon : CMonoid := Build_CMonoid _ _ C_is_CMonoid.
Canonical Structure C_mon.

Lemma CNeg_sunop : fun_strext (S1:=C_oid) (S2:=C_oid) Copp.
Proof.
 unfold fun_strext.
 intros x y. unfold "[#]". simpl. now intros H ->.
Qed.

Definition CNeg_op : CSetoid_un_op C_oid :=
 Build_CSetoid_un_op _ Copp CNeg_sunop.

Lemma C_is_Group : is_CGroup C_mon CNeg_op.
Proof.
 unfold is_CGroup.
 intro x.
 unfold is_inverse.
 unfold C_mon in *. simpl in *. split; ring.
Qed.

Definition C_grp := Build_CGroup _ _ C_is_Group.
Canonical Structure C_grp.

Lemma C_is_AbGroup : is_CAbGroup C_grp.
Proof.
 unfold is_CAbGroup.
 unfold commutes.
 intros x y.
 apply Cplus_comm.
Qed.

Definition C_abg := Build_CAbGroup _ C_is_AbGroup.
Canonical Structure C_abg.

Lemma CMul_is_csbinop : bin_fun_strext C_oid C_oid C_oid Cmult.
Proof.
 unfold bin_fun_strext.
 intros x1 x2 y1 y2 H.
 unfold C_oid in *. simpl in *.
 destruct (Ceq_dec x1 x2); [subst|now left].
 destruct (Ceq_dec y1 y2); [subst|now right].
 now destruct H.
Qed.

Definition CMul_op : CSetoid_bin_op C_mon :=
 Build_CSetoid_bin_op C_oid Cmult CMul_is_csbinop.

Lemma CMul_assoc : associative (S:=C_abg) CMul_op.
Proof.
 repeat red. unfold C_abg. simpl. intros. ring.
Qed.

Lemma C_is_Ring : is_CRing C_abg (RtoC 1) CMul_op.
Proof.
 exists CMul_assoc.
 - constructor.
   + unfold is_rht_unit; intro x. simpl in *. ring.
   + unfold is_lft_unit; intro x. simpl in *. ring.
 - unfold commutes. apply Cmult_comm.
 - unfold distributive; intros x y z. apply Cmult_plus_distr_l.
 - simpl. intro H. apply RtoC_inj in H. lra.
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

(* Maintenant isomorphisme avec CC : *)

Definition CasCC : C -> CC :=
  fun (c:C) => Build_CC_set (RasIR (Re c)) (RasIR (Im c)).

Definition CCasC : CC -> C :=
  fun (c:CC) => (IRasR (CComplex.Re c), IRasR (CComplex.Im c)).

(* TODO : suite de l'isomorphisme... *)

(* Puis : *)

Theorem Coq_FTA : forall f : cpoly_cring C_fd,
       nonConst C_fd f -> {z : C_fd & f ! z [=] [0]}.
Admitted.

(* TODO : Factorisation d'un polynôme par (X-root) ...
   et repetition tant que degré non-nul
*)
