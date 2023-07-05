From Coq Require Import Arith Reals Lra Lia Permutation Morphisms.
From QuantumLib Require Import Complex Polynomial Matrix VecSet Eigenvectors.
Require Import MoreList MorePermut MorePoly MoreMatrix.
Local Open Scope C.

(** * Some diagonalization theory *)

Definition Diag n l : Square n :=
 fun i j => if (i =? j)%nat then nth i l C0 else C0.

(* prep_mat A := A - X.Id
   hence DeterminantP (prep_mat A) isn't monic when n is odd.
   Instead of tweaking with prep_mat, we simply multiply by the parity
   afterwards. *)

Definition CharPoly {n} (A:Square n) := monicify (DeterminantP (prep_mat A)).

Lemma parity_pow n : parity n = (-C1)^n.
Proof.
 induction n as [|n IH]. simpl; auto. rewrite parity_S, IH. simpl. ring.
Qed.

Lemma parity_nz n : parity n <> C0.
Proof.
 induction n as [|n IH].
 apply C1_neq_C0.
 rewrite parity_S. apply Cmult_neq_0; auto.
 apply Copp_neq_0_compat, C1_neq_C0.
Qed.

Lemma CharPoly_deg {n} (A:Square n) : degree (CharPoly A) = n.
Proof.
 unfold CharPoly. now rewrite monicify_degree, detP_deg.
Qed.

Lemma detP_nz {n} (A:Square n) : ~DeterminantP (prep_mat A) ≅ [].
Proof.
 intro H.
 assert (H' := detP_deg A). rewrite H in H'. cbn in H'. subst n.
 revert H. cbn. rewrite Peq0_carac. cbn. destruct Ceq_dec; try easy.
 now destruct C1_neq_C0.
Qed.

Lemma detP_topcoef {n} (A:Square n) :
 topcoef (DeterminantP (prep_mat A)) <> C0.
Proof.
 rewrite topcoef_0_iff. apply detP_nz.
Qed.

Lemma CharPoly_monic {n} (A:Square n) : monic (CharPoly A).
Proof.
 apply monicify_monic. apply detP_nz.
Qed.

(* TODO : finir un jour
Lemma detP_topcoef_parity {n} (A:Square n) :
 topcoef (DeterminantP (prep_mat A)) = parity n.
Proof.
 rewrite topcoef_alt. rewrite detP_deg. unfold coef.
 induction n as [|[|n] IH].
 - easy.
 - easy.
 - simpl parity. rewrite DetP_simplify.
...
*)

Lemma reduce_scale {n} (A:Square (S n)) x y c :
 reduce (c.*A) x y == c.*(reduce A x y).
Proof.
 intros i j Hi Hj. unfold reduce, scale. simpl.
 now do 2 destruct Nat.ltb.
Qed.

Lemma Determinant_scale {n} (A:Square n) c :
 Determinant (c .* A) = c ^ n * Determinant A.
Proof.
 revert A. induction n as [|[|] IH]; intros.
 - simpl. ring.
 - simpl. unfold scale. ring.
 - rewrite !Det_simplify.
   transitivity (Σ
    (fun i =>
     c ^ S (S n) * ((parity i * A i O) * Determinant (reduce A i 0)))
    (S (S n))).
   + apply big_sum_eq_bounded; intros.
     rewrite reduce_scale, IH. simpl Cpow. unfold scale. ring.
   + symmetry.
     apply (@big_sum_mult_l _ _ _ _ C_is_ring).
Qed.

Lemma Determinant_Mopp {n} (A:Square n) :
 Determinant (Mopp A) = parity n * Determinant A.
Proof.
 unfold Mopp. now rewrite Determinant_scale, parity_pow.
Qed.

Definition MatOfCols {n} (l : list (Vector n)) : Square n :=
 fun i j => (nth j l Zero) i O.

Lemma WF_MatOfCols {n} (l : list (Vector n)) :
 length l = n -> Forall WF_Matrix l -> WF_Matrix (MatOfCols l).
Proof.
 unfold MatOfCols.
 intros H F. red. intros x y Hxy.
 destruct (Nat.lt_ge_cases y n).
 - rewrite Forall_forall in F.
   apply (F (nth y l Zero)); try lia. apply nth_In; lia.
 - rewrite nth_overflow. easy. lia.
Qed.

Lemma MatOfCols_col {n} (l : list (Vector n)) j :
 get_vec j (MatOfCols l) == nth j l Zero.
Proof.
 unfold get_vec. intros x y Hx Hy. now replace y with O by lia.
Qed.

Lemma MatOfCols_col_eq {n} (l : list (Vector n)) j :
 length l = n -> Forall WF_Matrix l ->
 get_vec j (MatOfCols l) = nth j l Zero.
Proof.
 intros L F.
 apply mat_equiv_eq, MatOfCols_col.
 - apply WF_get_vec, WF_MatOfCols; auto.
 - destruct (Nat.ltb_spec j n); intros.
   + rewrite Forall_forall in F.
     apply (F (nth j l Zero)); try lia. apply nth_In. lia.
   + rewrite nth_overflow; auto with wf_db. lia.
Qed.

Lemma Diag_col n (l : list C) j :
 get_vec j (Diag n l) == (nth j l C0) .* e_i j.
Proof.
 intros x y Hx Hy.
 unfold Diag, get_vec. replace y with O by lia. simpl.
 unfold e_i, scale. case Nat.eqb_spec; simpl; intros; try ring.
 subst j.
 case Nat.ltb_spec; intros; simpl; try lia. ring.
Qed.

Lemma Diag_times_vect n (l : list C) (a : Vector n) :
 Diag n l × a == (fun i _ => nth i l C0 * a i O).
Proof.
 intros x y Hx Hy. unfold Mmult, Diag.
 induction n; simpl; auto. lia.
 case (Nat.eqb_spec x n); intros.
 - subst x. replace y with O by lia.
   rewrite big_sum_0_bounded, Cplus_0_l; trivial.
   intros x' Hx'. case Nat.eqb_spec; intros. lia. now rewrite Cmult_0_l.
 - rewrite IHn by lia. ring.
Qed.

Lemma WF_Diag n (l : list C) : length l = n -> WF_Matrix (Diag n l).
Proof.
 intros Hl x y Hxy. unfold Diag.
 case Nat.eqb_spec; intros; auto. subst. rewrite nth_overflow; auto. lia.
Qed.

Lemma MatOfCols_eqn {n} (A : Square n) (l : list (Vector n * C)) :
 length l = n ->
 Forall (fun '(v,c) => WF_Matrix v /\ v<>Zero /\ A × v = c .* v) l ->
 let B := MatOfCols (map fst l) in
 let D := Diag n (map snd l) in
 A × B = B × D.
Proof.
 intros H F B D. rewrite Forall_forall in F.
 apply det_by_get_vec. intros j.
 rewrite <- !get_vec_mult.
 assert (F' : Forall WF_Matrix (map fst l)).
 { rewrite Forall_forall. intros x.
   rewrite in_map_iff. intros ((v,c) & <- & IN). simpl.
   apply (F _ IN). }
 assert (WB : WF_Matrix B).
 { apply WF_MatOfCols; auto. now rewrite map_length. }
 assert (E : get_vec j B = nth j (map fst l) Zero).
 { apply MatOfCols_col_eq; auto. now rewrite map_length. }
 rewrite E.
 assert (E' : get_vec j D = nth j (map snd l) C0 .* e_i j).
 { apply mat_equiv_eq, Diag_col; auto with wf_db.
   apply WF_get_vec, WF_Diag. now rewrite map_length. }
 rewrite E', Mscale_mult_dist_r.
 destruct (Nat.lt_ge_cases j n) as [LT|GE].
 - rewrite <-H in LT.
   rewrite <- matrix_by_basis by lia. rewrite E.
   assert (IN := nth_In l (Zero,C0) LT).
   destruct (nth j l (Zero, C0)) as (v,c) eqn:E2.
   destruct (F _ IN) as (WF & _ & E3).
   change (@Zero n 1) with (fst (@Zero n 1,C0)).
   rewrite map_nth, E2. simpl.
   change C0 with (snd (@Zero n 1, C0)). now rewrite map_nth, E2.
 - rewrite !nth_overflow by (rewrite map_length; lia).
   now rewrite Mmult_0_r, Mscale_0_l.
Qed.

Lemma times_ei_col {n} (A : Square n) m :
 WF_Matrix A ->
 A × e_i m = get_vec m A.
Proof.
 intros HA.
 apply mat_equiv_eq; auto with wf_db.
 intros x y Hx Hy. replace y with O by lia. clear y Hy.
 unfold Mmult, e_i, get_vec. simpl.
 destruct (Nat.ltb_spec m n) as [Hm|Hm].
 - apply big_sum_unique. exists m. split. apply Hm. split.
   + case Nat.eqb_spec; intros; simpl; try lia.
     case Nat.ltb_spec; intros; simpl; try lia. ring.
   + intros y Hy Hy'.
     case Nat.eqb_spec; intros; simpl; try lia. ring.
 - replace (A x m) with C0 by (symmetry; apply HA; lia).
   apply (@big_sum_0_bounded _ C_is_monoid). intros y Hy.
   case Nat.eqb_spec; intros; simpl; try lia. ring.
Qed.

Lemma scale_integral {n} (v:Vector n) c : WF_Matrix v ->
 v <> Zero -> c .* v = Zero -> c = C0.
Proof.
 intros WF Hv E. destruct (nonzero_vec_nonzero_elem _ WF Hv) as (i,H).
 assert (E' : (c .* v) i O = C0) by now rewrite E.
 unfold scale in E'. apply Cmult_integral in E'. intuition.
Qed.

Definition VecZeroAbove {n} (v : Vector n) m := @WF_Matrix m 1 v.

Lemma exists_eigenbasis n (A : Square n) eigvals :
  WF_Matrix A ->
  CharPoly A ≅ linfactors eigvals ->
  NoDup eigvals ->
  exists B : Square n, WF_Matrix B /\ invertible B /\
                       A × B = B × Diag n eigvals.
Proof.
 intros HA D ND.
 assert (Step1 : forall c, In c eigvals -> det_eq_c C0 (A .+ (-c) .* I n)).
 { intros c Hc.
   red. split; trivial.
   rewrite linfactors_roots in Hc. rewrite <- D in Hc. unfold CharPoly in Hc.
   rewrite monicify_root in Hc. red in Hc.
   rewrite <- Peval_Det in Hc.
   rewrite <- Hc. clear Hc. apply Determinant_compat.
   unfold eval_matP, prep_mat in *.
   intros i j Hi Hj. unfold Mplus, scale, I.
   destruct andb; cbn; ring. }
 assert (Step2 : forall c, In c eigvals ->
          exists v:Vector n, WF_Matrix v /\ v<>Zero /\ A × v = c .* v).
 { intros c Hc. apply Step1 in Hc.
   apply lin_dep_det_eq_0 in Hc; auto with wf_db.
   destruct Hc as (v & H1 & H2 & H3).
   exists v; repeat split; auto.
   rewrite Mmult_plus_distr_r, Mscale_mult_dist_l, Mmult_1_l in H3; auto.
   assert (H4 : A × v .+ (-c .* v) .+ (c .* v) = (c .* v)).
   { rewrite H3. lma. }
   rewrite Mplus_assoc in H4.
   rewrite <- Mscale_plus_distr_l in H4.
   replace (-c + c)%C with C0 in H4 by lca.
   rewrite <- H4.
   lma. }
 assert (Step3 : forall l, NoDup l -> incl l eigvals ->
          exists eigpairs : list (Vector n * C),
          map snd eigpairs = l /\
          Forall (fun '(v,c) =>
                  WF_Matrix v /\ v<>Zero /\ A × v = c .* v) eigpairs).
 { induction l; intros NDl INl.
   - exists []; split; auto.
   - destruct IHl as (ep & E & F).
     now inversion NDl.
     unfold incl in *. simpl in INl; intuition.
     destruct (Step2 a) as (v & WF & Ha & Ev). apply INl; now left.
     exists ((v,a)::ep); split.
     + simpl. now f_equal.
     + constructor; auto. }
 destruct (Step3 eigvals ND (incl_refl _)) as (eigpairs & E & F).
 clear Step1 Step2 Step3.
 assert (Lv : length eigvals = n).
 { rewrite <- (CharPoly_deg A). rewrite D.
   symmetry. apply linfactors_degree. }
 clear D.
 assert (Lp : length eigpairs = n).
 { rewrite <- E in Lv. now rewrite map_length in Lv. }
 set (B := MatOfCols (map fst eigpairs)).
 assert (HB : WF_Matrix B).
 { apply WF_MatOfCols.
   + now rewrite map_length.
   + rewrite Forall_map.
     rewrite Forall_forall in *. intros (v,c) Hvc.
     specialize (F _ Hvc). now simpl in *. }
 assert (EQN : A × B = B × Diag n eigvals).
 { rewrite <- E. apply MatOfCols_eqn; auto. }
 exists B; repeat split; auto.
 apply lin_indep_invertible; auto.
 (* B linearly indep *)
 assert (IND : forall m (a:Vector n), (m <= n)%nat ->
          VecZeroAbove a m -> B × a = Zero -> a = Zero);
 [| intros a Ha; now apply (IND n a) ].
 induction m.
 - intros a _ Ha _.
   apply mat_equiv_eq; auto with wf_db.
   unfold VecZeroAbove, WF_Matrix in *. intuition.
   intros i j Hi Hj. apply Ha. lia.
 - intros a LE Ha E'.
   assert (WFa : WF_Matrix a).
   { unfold VecZeroAbove, WF_Matrix in *; intuition. }
   set (c := nth m eigvals C0).
   set (a' := (Diag n eigvals × a .+ (- c) .* a)).
   assert (WFa' : WF_Matrix a').
   { unfold a'. auto using WF_Diag with wf_db. }
   assert (Ha' : a' = Zero).
   { apply IHm. lia.
     - (* VecZeroAbove a' m *)
       intros i j Hij.
       destruct (Nat.leb_spec 1 j).
       + apply WFa'. lia.
       + destruct (Nat.leb_spec n i).
         * apply WFa'. lia.
         * replace j with O by lia.
           unfold a', Mplus, scale.
           rewrite Diag_times_vect by lia.
           destruct (Nat.ltb_spec m i).
           { replace (a i O) with C0 by (symmetry; apply Ha; lia). ring. }
           { replace i with m by lia. fold c. ring. }
     - (* B × a' = Zero *)
       unfold a'.
       rewrite Mmult_plus_distr_l.
       rewrite <- Mmult_assoc, <- EQN, Mmult_assoc, E', Mmult_0_r.
       rewrite Mscale_mult_dist_r, E'. now rewrite Mscale_0_r, Mplus_0_l. }
   assert (Ea : a = a m O .* e_i m).
   { apply mat_equiv_eq; auto with wf_db.
     intros x y Hxn Hy. replace y with O by lia. clear y Hy.
     unfold e_i, scale.
     case Nat.eqb_spec; intros; simpl.
     + subst. case Nat.ltb_spec; intros; simpl; try lia. ring.
     + rewrite Cmult_0_r.
       destruct (Nat.ltb_spec x m) as [Hxm|Hxm]; [|apply Ha; lia].
       assert (H : a' x O = 0) by now rewrite Ha'.
       unfold a', Mplus, scale in H.
       rewrite Diag_times_vect in H by lia.
       rewrite <- Cmult_plus_distr_r in H. apply Cmult_integral in H.
       destruct H as [H|H]; auto. exfalso.
       apply Cminus_eq in H. apply NoDup_nth in H; auto; lia. }
   rewrite Ea in E'. rewrite Mscale_mult_dist_r in E'.
   rewrite times_ei_col in E'; auto with wf_db.
   unfold B in E'.
   assert (Forall WF_Matrix (map fst eigpairs)).
   { rewrite Forall_forall in *. intros x.
     rewrite in_map_iff. intros ((v',c') & <- & IN). simpl.
     apply (F _ IN). }
   rewrite MatOfCols_col_eq in E' by (auto; rewrite map_length; lia).
   set (v := nth m (map fst eigpairs) Zero) in *.
   assert (IN : In (v,c) eigpairs).
   { unfold v, c. rewrite <- E.
     change (@Zero n 1) with (fst (@Zero n 1, C0)). rewrite map_nth.
     change C0 with (snd (@Zero n 1, C0)) at 2. rewrite map_nth.
     rewrite <- surjective_pairing. apply nth_In. lia. }
   rewrite Forall_forall in F. specialize (F _ IN). simpl in F.
   replace (a m O) with C0 in *. now rewrite Mscale_0_l in Ea.
   symmetry. apply (@scale_integral n v); intuition.
Qed.

(* Print Assumptions exists_eigenbasis. *)
