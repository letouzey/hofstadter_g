From Coq Require Import Arith Lia NArith Reals Lra.
From Hofstadter.HalfQuantum Require Import Complex.
Require Import MoreTac MoreFun MoreList MoreReals MoreLim MoreComplex MoreSum.
Require Import DeltaList Approx.
Require Import GenFib GenG GenAdd Words Mu ThePoly Freq Discrepancy F4.
Require Equidistrib.
Local Open Scope C.
Local Open Scope R.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

#[local] Hint Resolve
 μ_approx τ_approx ν_approx αmod_approx
 sup_deltas_approx inf_deltas_approx
 : typeclass_instances.

(** * Mean discrepancy in the case k=4

    We consider simultaneously [diff 4 n = f 4 n - τ * n] as well as
    [(f 4 ^^2) n - τ^2 * n] and
    [(f 4 ^^3) n - t^3 * n]. *)

Definition diff_4_2 n := (f 4 ^^2) n - τ^2 * n.
Definition diff_4_3 n := (f 4 ^^3) n - τ^3 * n.

Definition sumdiff n := big_sum (diff 4) n.
Definition meandiff n := sumdiff n / n.

Definition sumdiff_4_2 n := big_sum diff_4_2 n.
Definition meandiff_4_2 n := sumdiff_4_2 n / n.

Definition sumdiff_4_3 n := big_sum diff_4_3 n.
Definition meandiff_4_3 n := sumdiff_4_3 n / n.

(** Minimalistic theory of 3x3 matrices: vectors as triplets of reals
    and matrix as 9 reals. *)

Inductive vect := Vect : R -> R -> R -> vect.

Inductive matrix :=
  Matrix : R -> R -> R -> R -> R -> R -> R -> R -> R -> matrix.

Definition Vadd V V' :=
 match V, V' with Vect a b c,  Vect a' b' c' => Vect (a+a') (b+b') (c+c') end.

Definition Vscal r V :=
 match V with Vect a b c => Vect (r*a) (r*b) (r*c) end.

Declare Scope vect.
Local Open Scope vect.

Infix "++" := Vadd : vect.
Infix "**" := Vscal (at level 40) : vect.

Lemma Vadd_comm V V' : V ++ V' = V' ++ V.
Proof.
 destruct V, V'; simpl; f_equal; ring.
Qed.

Lemma Vadd_assoc V1 V2 V3 : V1 ++ (V2 ++ V3) = (V1 ++ V2) ++ V3.
Proof.
 destruct V1, V2, V3; simpl; f_equal; ring.
Qed.

Lemma Vscal_0 V : 0 ** V = Vect 0 0 0.
Proof.
 destruct V. simpl; f_equal; ring.
Qed.

Lemma Vscal_1 V : 1 ** V = V.
Proof.
 destruct V. simpl; f_equal; ring.
Qed.

Lemma Vscal_Vadd_r r V V' : r ** (V ++ V') = (r ** V) ++ (r ** V').
Proof.
 destruct V, V'; simpl; f_equal; ring.
Qed.

Lemma Vscal_Vadd_l r r' V : r ** V ++ r' ** V = (r+r') ** V.
Proof.
 destruct V; simpl; f_equal; ring.
Qed.

Lemma Vscal_Vscal r r' V : r ** (r' ** V) = (r*r') ** V.
Proof.
 destruct V; simpl; f_equal; ring.
Qed.

Definition Mapply M V :=
 match M, V with
 Matrix m11 m12 m13 m21 m22 m23 m31 m32 m33, Vect a b c =>
 Vect (m11*a + m12*b + m13*c) (m21*a + m22*b + m23*c) (m31*a + m32*b + m33*c)
 end.

Definition Mapply4 m v := Mapply m (Mapply m (Mapply m (Mapply m v))).

Lemma Mapply_Vadd M V V' :
  Mapply M (Vadd V V') = Vadd (Mapply M V) (Mapply M V').
Proof.
 destruct M, V, V'. simpl. f_equal; ring.
Qed.

Lemma Mapply4_Vadd M V V' :
  Mapply4 M (V ++ V') = Mapply4 M V ++ Mapply4 M V'.
Proof.
 unfold Mapply4. now rewrite !Mapply_Vadd.
Qed.

Lemma Mapply_Vscal M (r:R) V : Mapply M (r ** V) = r ** Mapply M V.
Proof.
 destruct M, V; simpl; f_equal; ring.
Qed.

Lemma Mapply4_Vscal M (r:R) V : Mapply4 M (r ** V) = r ** Mapply4 M V.
Proof.
 unfold Mapply4. now rewrite !Mapply_Vscal.
Qed.

Definition vdiff n := Vect (diff 4 n) (diff_4_2 n) (diff_4_3 n).
Definition vsumdiff n := Vect (sumdiff n) (sumdiff_4_2 n) (sumdiff_4_3 n).
Definition vmeandiff n := Vect (meandiff n) (meandiff_4_2 n) (meandiff_4_3 n).

Lemma vdiff_0 : vdiff 0 = Vect 0 0 0.
Proof.
 unfold vdiff, diff, diff_4_2, diff_4_3. simpl. f_equal; lra.
Qed.

Lemma vsumdiff_0 : vsumdiff 0 = Vect 0 0 0.
Proof.
 easy.
Qed.

Lemma vsumdiff_S n : vsumdiff (S n) = vsumdiff n ++ vdiff n.
Proof.
 easy.
Qed.

Lemma diff_4_2_app l l' : Delta 4 (l++l') ->
 (diff_4_2 (sumA 4 (l++l')) = diff_4_2 (sumA 4 l) + diff_4_2 (sumA 4 l'))%R.
Proof.
 intros D. destruct (Delta_app_inv l l' D) as (D1 & D2 & D3).
 unfold diff_4_2.
 rewrite !fs_sumA by (lia||easy).
 rewrite map_app, !sumA_app, !plus_INR. ring.
Qed.

Lemma diff_4_3_app l l' : Delta 4 (l++l') ->
 (diff_4_3 (sumA 4 (l++l')) = diff_4_3 (sumA 4 l) + diff_4_3 (sumA 4 l'))%R.
Proof.
 intros D. destruct (Delta_app_inv l l' D) as (D1 & D2 & D3).
 unfold diff_4_3.
 rewrite !fs_sumA by (lia||easy).
 rewrite map_app, !sumA_app, !plus_INR. ring.
Qed.

Lemma vdiff_app l l' : Delta 4 (l++l') ->
 vdiff (sumA 4 (l++l')) = vdiff (sumA 4 l) ++ vdiff (sumA 4 l').
Proof.
 intros D. unfold vdiff, Vadd. f_equal.
 now apply diff_app. now apply diff_4_2_app. now apply diff_4_3_app.
Qed.

Lemma vdiff_cons p l : Delta 4 (p::l) ->
 vdiff (sumA 4 (p::l)) = vdiff (A 4 p) ++ vdiff (sumA 4 l).
Proof.
 intros D.
 replace (A 4 p) with (sumA 4 [p]) by (simpl; lia).
 now rewrite <- vdiff_app.
Qed.

Lemma vdiff_add p n : (n < A 4 (p-3))%nat ->
 vdiff (n + A 4 p) = vdiff n ++ vdiff (A 4 p).
Proof.
 intros Hn.
 assert (E : decomp 4 (n+A 4 p) = (decomp 4 n++[p])%list).
 { now apply decomp_plus_A. }
 rewrite <- (decomp_sum 4 (n+A 4 p)), E.
 rewrite vdiff_app. 2:{ rewrite <- E. apply decomp_delta. }
 rewrite decomp_sum. simpl. now rewrite Nat.add_0_r.
Qed.

(** The matrix and initial vector corresponding to vdiff *)

Definition Mat :=
  Matrix 0 0 (-τ)
         1 0 (-τ^2)
         0 1 (-τ^3).
Definition Vinit := Vect (1-τ) (1-τ^2) (1-τ^3).

Lemma Vinit_ok : Vinit = vdiff 1.
Proof.
 unfold Vinit, vdiff, diff, diff_4_2, diff_4_3. simpl.
 change (tau 4) with τ. f_equal; ring.
Qed.

Lemma diff3_alt' n : diff_4_3 n = - diff3 n.
Proof.
 rewrite diff3_alt. unfold diff_4_3. ring.
Qed.

Lemma diff1_alt' n : diff_4_2 n = diff0 n + diff1 n.
Proof.
 rewrite diff1_alt, diff0_alt. unfold diff_4_2. ring [τ4].
Qed.

Lemma diff0_A p : diff0 (A 4 (S p)) = τ * diff3 (A 4 p).
Proof.
 unfold diff0, diff3.
 now rewrite !kprefix_A_kword, kword_S, Diff0_ksubst4.
Qed.

Lemma diff3_A p :
  diff3 (A 4 (S p)) = - τ^3 * diff3 (A 4 p) - diff0 (A 4 p) - diff1 (A 4 p).
Proof.
 unfold diff0, diff1, diff3.
 rewrite !kprefix_A_kword, kword_S, Diff3_ksubst4; trivial.
 now apply kword_letters.
Qed.

Lemma diff1_A p :
  diff1 (A 4 (S p)) = - τ^5 * diff3 (A 4 p) + diff0 (A 4 p).
Proof.
 unfold diff0, diff1, diff3.
 rewrite !kprefix_A_kword, kword_S, Diff1_ksubst4; trivial.
 now apply kword_letters.
Qed.

Lemma vdiff_A_S p : vdiff (A 4 (S p)) = Mapply Mat (vdiff (A 4 p)).
Proof.
 unfold vdiff, Mat, Mapply.
 rewrite <- !diff0_alt', !diff3_alt', !diff1_alt'.
 rewrite diff0_A, diff1_A, diff3_A. f_equal; ring [τ4].
Qed.

Lemma vdiff_sumA l : Delta 4 l ->
 vdiff (sumA 4 (map S l)) = Mapply Mat (vdiff (sumA 4 l)).
Proof.
 induction l.
 - intros _. simpl sumA. rewrite vdiff_0. simpl. f_equal; ring.
 - intros D. simpl map. rewrite !vdiff_cons; trivial.
   2:{ change (Delta 4 (map S (a::l))). eapply Delta_map; eauto. lia. }
   rewrite vdiff_A_S, IHl, Mapply_Vadd. easy. eapply Delta_inv; eauto.
Qed.

Lemma vdiff_ranknz n :
 rank 4 n <> Some O ->
 vdiff n = Mapply Mat (vdiff (f 4 n)).
Proof.
 intros Hn. unfold rank in Hn. unfold h. rewrite f_decomp by easy.
 rewrite <- (decomp_sum 4 n) at 1.
 assert (D := decomp_delta 4 n).
 set (l := decomp 4 n) in *. clearbody l. clear n.
 assert (Hl : ~In O l).
 { destruct l. easy. eapply Delta_nz; eauto.
   assert (n<>O) by (contradict Hn; now subst). lia. }
 rewrite <- vdiff_sumA, map_S_pred; try easy. now apply Delta_pred.
Qed.

Lemma vdiff_rank0 n :
 rank 4 n = Some O ->
 vdiff n = Vinit ++ Mapply4 Mat (vdiff (n - f 4 n)).
Proof.
 intros Hn.
 replace (n - f 4 n)%nat with (fs 4 4 (n-1)%nat).
 2:{ destruct n. easy. unfold h. rewrite f_S.
     replace (S n -1)%nat with n by lia. generalize (fs_le 4 4 n). lia. }
 unfold rank in Hn. rewrite fs_decomp by easy.
 rewrite <- (decomp_sum 4 n) at 1.
 assert (D := decomp_delta 4 n).
 rewrite decomp_pred by easy.
 set (l := decomp 4 n) in *. clearbody l. clear n.
 destruct l as [|r l]; try easy. inversion Hn; subst. clear Hn.
 rewrite vdiff_cons, Vinit_ok by easy. f_equal.
 simpl prev_decomp. unfold Mapply4.
 assert (Hl : forall x, In x l -> (4 <= x)%nat).
 { intros. eapply Delta_le in D; eauto. }
 assert (D3 : Delta 4 (map (decr 4) l)).
 { apply Delta_map_decr; eauto using Delta_inv. }
 rewrite <- !vdiff_sumA; trivial.
 - f_equal. f_equal. rewrite !map_map.
   rewrite map_ext_in with (g:=fun n => n). symmetry; apply map_id.
   { intros x Hx. unfold decr. specialize (Hl x Hx). lia. }
 - rewrite 2 map_map. eapply Delta_map; eauto. lia.
 - rewrite map_map. eapply Delta_map; eauto. lia.
 - eapply Delta_map; eauto. lia.
Qed.

Lemma vsumdiff_eqn n :
  vsumdiff n =
  Mapply Mat (vsumdiff (f 4 n)) ++
  ((n - f 4 n)%nat ** Vinit ++ Mapply4 Mat (vsumdiff (n - f 4 n))).
Proof.
 induction n.
 - rewrite f_k_0, Nat.sub_0_l, vsumdiff_0. simpl; f_equal; ring.
 - rewrite vsumdiff_S, IHn.
   assert (H := @flat_rank_0 4%nat lia n).
   destruct (f_step 4 n) as [E|E]; fold h in *.
   + rewrite E in *.
     rewrite vdiff_rank0 by now rewrite <- H.
     replace (S n - f 4 n)%nat with (S (n - f 4 n)).
     2:{ unfold h. generalize (f_le 4 n); lia. }
     rewrite vsumdiff_S.
     rewrite <- !Vadd_assoc. f_equal.
     replace (Vscal (S _) _) with (Vadd (Vscal (n-f 4 n)%nat Vinit) Vinit).
     2:{ rewrite S_INR. unfold Vinit. simpl; f_equal; ring. }
     rewrite Mapply4_Vadd.
     rewrite <- !Vadd_assoc. f_equal.
     rewrite !Vadd_assoc. f_equal. apply Vadd_comm.
   + rewrite E in *. replace (S n - S _)%nat with (n - f 4 n)%nat by lia.
     rewrite vsumdiff_S, Mapply_Vadd.
     rewrite <- vdiff_ranknz by (rewrite <- H; lia).
     rewrite <- !Vadd_assoc. f_equal.
     now rewrite (Vadd_comm (vdiff n)), Vadd_assoc.
Qed.

Lemma vmeandiff_alt n : vmeandiff n = (/n) ** vsumdiff n.
Proof.
 unfold vmeandiff, meandiff, meandiff_4_2, meandiff_4_3. simpl.
 unfold Rdiv. f_equal; ring.
Qed.

Lemma vmeandiff_eqn n : n<>O ->
  vmeandiff n =
  (f 4 n / n) ** Mapply Mat (vmeandiff (f 4 n))
  ++ (1 - f 4 n / n) ** (Vinit ++ Mapply4 Mat (vmeandiff (n - f 4 n))).
Proof.
 intros Hn.
 destruct (Nat.eq_dec n 1) as [->|Hn'].
 { change (f 4 1) with 1%nat.
   simpl Rdiv. replace (1/1) with 1 by lra.
   replace (1-1) with 0 by lra. rewrite Vscal_0.
   rewrite vmeandiff_alt, vsumdiff_S, vsumdiff_0, vdiff_0.
   simpl; f_equal; ring. }
 rewrite !vmeandiff_alt, vsumdiff_eqn.
 rewrite Mapply4_Vscal, Mapply_Vscal, !Vscal_Vadd_r, !Vscal_Vscal.
 f_equal; [|f_equal]; f_equal.
 - field. split. 2:inr.
   contradict Hn. apply (INR_eq _ 0) in Hn.
   generalize (@f_nonzero 4%nat n). lia.
 - rewrite minus_INR by apply f_le. field. inr.
 - rewrite minus_INR by apply f_le. field. split. 2:inr.
   assert (LT := @f_lt 4 n lia). inr.
Qed.

Lemma vmeandiff_A_eqn p :
  let r := (A 4 (p-1) / A 4 p) in
  vmeandiff (A 4 p) =
  r ** Mapply Mat (vmeandiff (A 4 (p-1)))
  ++ (1-r) ** (Vinit ++ Mapply4 Mat (vmeandiff (A 4 (p-4)))).
Proof.
 intros r. rewrite vmeandiff_eqn.
 2:{ generalize (A_nz 4 p). lia. }
 rewrite f_A by easy. fold r. f_equal.
 destruct p.
 - simpl A in *. replace (1-r) with 0 by (unfold r; simpl; lra).
   now rewrite !Vscal_0.
 - do 4 f_equal. simpl. rewrite Nat.sub_0_r. lia.
Qed.

Definition limit1 := (-4 * τ^3 - 3 * τ^2 + 19 * τ - 11)/34.
Definition limit2 := (-6 * τ^3 + 21 * τ^2 + 3 * τ -8)/34.
Definition limit3 := (28 * τ^3 + 4 * τ^2 + 3 * τ -8)/34.
Definition limit := Vect limit1 limit2 limit3.

Lemma limit_ok :
 limit = τ ** Mapply Mat limit ++ (1-τ) ** (Vinit ++ Mapply4 Mat limit).
Proof.
 unfold Vinit, Mat, limit, limit1, limit2, limit3.
 cbn -[pow]. f_equal; field [τ4].
Qed.

Lemma limit_unique l :
 l = τ ** Mapply Mat l ++ (1-τ) ** (Vinit ++ Mapply4 Mat l) -> l = limit.
Proof.
 destruct l as (x,y,z).
 unfold Vinit, Mat, limit.
 intros [= E1 E2 E3]. simpl in E1,E2,E3. apply Rminus_diag_eq in E1, E2, E3.
 ring_simplify [τ4] in E1. ring_simplify [τ4] in E2. ring_simplify [τ4] in E3.
 assert (E3' : z * (τ^3+τ) =
               -(τ ^ 3 * x + τ ^ 3 * y + τ ^ 3 + τ * x + 2 * τ - x - y - 2))
  by lra.
 clear E3.
 apply Rmult_eq_compat_l with (r:=(τ^3+τ^2)) in E3'.
 ring_simplify [τ4] in E3'.
 rewrite !E3' in E1, E2. ring_simplify [τ4] in E1. ring_simplify [τ4] in E2.
 assert (E2' : y * (3*τ^3 + 3*τ^2-τ-3) =
               - τ ^ 3 * x + τ ^ 3 - 2 * τ ^ 2 * x -
               3 * τ ^ 2 - 3 * τ * x - 4 * τ + 3 * x + 4) by lra.
 clear E2.
 apply Rmult_eq_compat_l with (r:=-(71*τ^3+66*τ^2+24*τ+140)/221) in E2'.
 field_simplify [τ4] in E2'.
 replace (221 * y/221) with y in E2' by field.
 rewrite !E2' in E1. field_simplify [τ4] in E1.
 assert (E1' : x * (7*τ^3-τ^2+2*τ-10) =
               -τ^3+2*τ^2-21/2*τ+7) by lra.
 clear E1.
 apply Rmult_eq_compat_l with (r:=-(11*τ^3+4*τ^2+3*τ+26)/221) in E1'.
 field_simplify [τ4] in E1'.
 replace (221 * x/221) with x in E1' by field.
 assert (E1 : x = limit1) by (rewrite E1'; unfold limit1; field [τ4]).
 assert (E2 : y = limit2).
 { rewrite E2', !E1. unfold limit1, limit2. field [τ4]. }
 assert (E3 : z = limit3).
 { rewrite E3', !E1, !E2. unfold limit1, limit2, limit3. field [τ4]. }
 f_equal; trivial.
Qed.

#[local] Instance limit1_approx :
  Approx (-0.00971849563) limit1 (-0.00971849562).
Proof.
 unfold limit1. simpl. approx.
Qed.

#[local] Instance limit2_approx : Approx 0.085719736 limit2 0.085719737.
Proof.
 unfold limit2. simpl. approx.
Qed.

#[local] Instance limit3_approx :
  Approx 0.20355300606 limit3 0.20355300607.
Proof.
 unfold limit3. simpl. approx.
Qed.

(** NB: these limits are also real roots of polynomials of degree 4.
    Beware that each of these polynomials also has another real root. *)

Lemma limit1_poly : let x := limit1 in 272*x^4+256*x^3+116*x^2+104*x+1 = 0.
Proof.
 unfold limit1. simpl. field [τ4].
Qed.

Lemma limit2_poly : let x := limit2 in 272*x^4+112*x^3-132*x^2-188*x+17 = 0.
Proof.
 unfold limit2. simpl. field [τ4].
Qed.

Lemma limit3_poly : let x := limit3 in 272*x^4+928*x^3+1040*x^2+342*x-121 = 0.
Proof.
 unfold limit3. simpl. field [τ4].
Qed.


Definition vsumdiff' n := vsumdiff n ++ (- n) ** limit.
Definition vmeandiff' n := vmeandiff n ++ (-1) ** limit.
Definition rest n :=
  Mapply Mat (vmeandiff (f 4 n))
  ++ (-1) ** (Vinit ++ Mapply4 Mat (vmeandiff (n - f 4 n))).

Lemma vmeandiff'_eqn n : n<>O ->
  vmeandiff' n =
  τ ** Mapply Mat (vmeandiff' (f 4 n))
  ++ (1 - τ) ** Mapply4 Mat (vmeandiff' (n-f 4 n))
  ++ (f 4 n / n - τ) ** rest n.
Proof.
 intros Hn.
 unfold vmeandiff', rest.
 rewrite vmeandiff_eqn by easy.
 rewrite limit_ok at 1.
 rewrite Mapply_Vadd, Mapply4_Vadd, Mapply_Vscal, Mapply4_Vscal.
 rewrite !Vscal_Vadd_r, !Vscal_Vscal.
 rewrite !Vadd_assoc.
 rewrite (Vadd_comm _ (_ ** Mapply Mat (vmeandiff (f 4 n)))).
 rewrite !Vadd_assoc, Vscal_Vadd_l, <- !Vadd_assoc. f_equal; [f_equal; ring|].
 rewrite !Vadd_assoc.
 rewrite !(Vadd_comm _ (_ ** Vinit)).
 rewrite !Vadd_assoc, Vscal_Vadd_l, <- !Vadd_assoc. f_equal; [f_equal; ring|].
 rewrite !Vadd_assoc.
 rewrite !(Vadd_comm _ (_ ** Mapply4 Mat (vmeandiff _))).
 rewrite !Vadd_assoc, Vscal_Vadd_l, <- !Vadd_assoc. f_equal; [f_equal; ring|].
 f_equal; f_equal; ring.
Qed.

Lemma vmeandiff'_A_eqn p : (p<>0)%nat ->
  vmeandiff' (A 4 p) =
  τ ** Mapply Mat (vmeandiff' (A 4 (p-1)))
  ++ (1 - τ) ** Mapply4 Mat (vmeandiff' (A 4 (p-4)))
  ++ (A 4 (p-1) / A 4 p - τ) ** rest (A 4 p).
Proof.
 intros Hp.
 rewrite vmeandiff'_eqn.
 2:{ generalize (A_nz 4 p). lia. }
 rewrite f_A by easy.
 replace (A 4 p - _)%nat with (A 4 (p-4)); trivial.
 { destruct p; try easy. simpl. rewrite Nat.sub_0_r. lia. }
Qed.

(** A norm inspired by Rauzy's norm for tribonacci *)

Definition Rnorm2 V :=
  match V with Vect a b c =>
    2 * (Cmod (a + α * b + α^2 * c)) ^ 2 + (a + ν * b + ν^2 * c)^2
  end.

Definition Rnorm V := sqrt (Rnorm2 V).

Lemma Rnorm2_pos V : 0 <= Rnorm2 V.
Proof.
 unfold Rnorm2. destruct V. apply Rplus_le_le_0_compat.
 - apply Rmult_le_pos; try lra. apply pow2_ge_0.
 - apply pow2_ge_0.
Qed.

Lemma Rnorm2_0_iff V : Rnorm2 V = 0 <-> V = Vect 0 0 0.
Proof.
 unfold Rnorm2. destruct V as (a,b,c). split.
 2:{ intros [= -> -> ->]. rewrite !Cmult_0_r, !Cplus_0_l, Cmod_0; ring. }
 intros E.
 assert (E' : Cmod (a + α * b + α ^ 2 * c) = 0 /\ a + ν * b + ν ^ 2 * c = 0).
 { assert (H := Cmod_ge_0 (a + α * b + α ^ 2 * c)).
   assert (H' := pow2_ge_0 (a + ν * b + ν ^ 2 * c)).
   nra. }
 clear E. destruct E' as (E,E3). apply Cmod_eq_0 in E.
 unfold α in E.
 unfold Cmult in E. simpl in E.
 rewrite !Rmult_0_r, !Rplus_0_l in E.
 unfold Cplus in E; simpl in E. injection E as E1 E2.
 ring_simplify in E1. ring_simplify in E2.
 replace (_+_) with (im_α * (b + 2*re_α * c)) in E2 by ring.
 apply Rmult_integral in E2.
 destruct E2 as [E2|E2]; [exfalso; revert E2; approx|].
 assert (E2' : b = -2*re_α * c) by lra. clear E2.
 rewrite E2' in E1, E3. ring_simplify in E1. ring_simplify in E3.
 assert (E1' : a = (re_α^2 + im_α^2) * c) by lra. clear E1.
 rewrite E1' in E3. ring_simplify in E3.
 replace (_+_+_) with (c * (re_α^2 + im_α^2 - 2*re_α*ν + ν^2)) in E3 by ring.
 apply Rmult_integral in E3.
 destruct E3 as [E3|E3]; [|exfalso; revert E3; approx].
 subst c. rewrite Rmult_0_r in *. now subst.
Qed.

Lemma Rnorm_0_iff V : Rnorm V = 0 <-> V = Vect 0 0 0.
Proof.
 unfold Rnorm. split.
 - intros E. apply Rnorm2_0_iff. apply (f_equal Rsqr) in E.
   rewrite Rsqr_sqrt in E by apply Rnorm2_pos. now rewrite E, Rsqr_0.
 - intros E. rewrite <- Rnorm2_0_iff in E. now rewrite E, sqrt_0.
Qed.

Lemma Rnorm2_Mapply V :
  Rnorm2 (Mapply Mat V) =
  match V with Vect a b c =>
    2 * (Cmod α)^2 * (Cmod (a + α * b + α^2 * c)) ^ 2
    + ν^2 * (a + ν * b + ν^2 * c)^2
  end.
Proof.
 unfold Mat, Mapply, Rnorm2. destruct V as (a,b,c).
 rewrite !Rmult_0_l, !Rplus_0_l, !Rplus_0_r, !Rmult_1_l.
 rewrite Rmult_assoc, <- !Rpow_mult_distr, <- Cmod_mult.
 f_equal; [f_equal|f_equal].
 - rtoc. f_equal. f_equal.
   apply Cmult_eq_reg_l with (α - /τ)%C.
   2:{ ctor. unfold α, Cminus, Cplus. simpl.
       intros [= _ E]. revert E. approx. }
   assert (H : RtoC τ <> 0%C) by (intros [= E]; revert E; approx).
   field_simplify [α_is_Croot]; trivial.
   ctor. rewrite τ4. rtoc. field; trivial.
 - apply Rmult_eq_reg_l with (ν - /τ); try approx.
   field [τ4 ν_is_Rroot]. approx.
Qed.

Lemma Rnorm2_Mapply_le V :
  Rnorm2 (Mapply Mat V) <= (Cmod α)^2 * Rnorm2 V.
Proof.
 rewrite Rnorm2_Mapply. unfold Rnorm2. destruct V as (a,b,c).
 rewrite Rmult_plus_distr_l.
 rewrite <- Rmult_assoc, (Rmult_comm _ 2), Rmult_assoc.
 apply Rplus_le_compat_l.
 apply Rmult_le_compat_r. apply pow2_ge_0. approx.
Qed.

Lemma Rnorm_Mapply_le V :
  Rnorm (Mapply Mat V) <= Cmod α * Rnorm V.
Proof.
 unfold Rnorm.
 rewrite <- (sqrt_pow2 (Cmod α)) by approx.
 rewrite <- sqrt_mult. 2:approx. 2:apply Rnorm2_pos.
 apply sqrt_le_1_alt. apply Rnorm2_Mapply_le.
Qed.

Lemma Rnorm_Mapply4_le V :
  Rnorm (Mapply4 Mat V) <= (Cmod α)^4 * Rnorm V.
Proof.
 simpl pow. rewrite !Rmult_assoc, Rmult_1_l.
 unfold Mapply4.
 do 4
 (rewrite Rnorm_Mapply_le; apply Rmult_le_compat_l; [apply Cmod_ge_0|]).
 apply Rle_refl.
Qed.

Lemma Rnorm2_scal r V : Rnorm2 (r ** V) = r^2 * Rnorm2 V.
Proof.
 unfold Rnorm2. destruct V as (a,b,c). cbn -[τ ν α pow Cpow]. rtoc.
 rewrite Rmult_plus_distr_l. f_equal. 2:ring.
 rewrite <- Rmult_assoc, (Rmult_comm _ 2), Rmult_assoc. f_equal.
 rewrite <- (pow2_abs r), <- Cmod_R, <- Rpow_mult_distr, <- Cmod_mult.
 f_equal; f_equal. ring.
Qed.

Lemma Rnorm_scal r V : Rnorm (r ** V) = Rabs r * Rnorm V.
Proof.
 unfold Rnorm. rewrite Rnorm2_scal, sqrt_mult.
 - now rewrite <- Rsqr_pow2, sqrt_Rsqr_abs.
 - apply pow2_ge_0.
 - apply Rnorm2_pos.
Qed.

Lemma Rnorm_triangle V V' : Rnorm (V++V') <= Rnorm V + Rnorm V'.
Proof.
 apply Rsqr_incr_0.
 2: apply sqrt_pos.
 2: apply Rplus_le_le_0_compat; apply sqrt_pos.
 unfold Rnorm.
 rewrite Rsqr_plus.
 rewrite !Rsqr_sqrt by apply Rnorm2_pos.
 rewrite Rplus_comm. apply Rcomplements.Rle_minus_l.
 unfold Rnorm2. destruct V as (a,b,c), V' as (a',b',c').
 cbn -[τ ν α pow Cpow].
 rtoc.
 set (u := (a + α * b + α ^ 2 * c)%C).
 set (u' := (a' + α * b' + α ^ 2 * c')%C).
 replace (a + _ + _ + _)%C with (u+u')%C by (unfold u, u'; ring).
 set (v := a + ν * b + ν^2 * c).
 set (v' := a' + ν * b' + ν ^ 2 * c').
 replace (a + _ + _ + _) with (v+v') by (unfold v, v'; ring).
 rewrite <- !Rsqr_pow2, Rsqr_plus. ring_simplify.
 apply Rle_trans with (4 * Cmod u * Cmod u' + 2 * v * v').
 { rewrite <- Rcomplements.Rle_minus_l. ring_simplify.
   assert (H := Cmod_triangle u u').
   apply Rsqr_incr_1 in H.
   2: apply Cmod_ge_0.
   2: apply Rplus_le_le_0_compat; apply Cmod_ge_0.
   rewrite Rsqr_plus in H. lra. }
 apply Rle_trans with (4 * Cmod u * Cmod u' + 2 * Rabs (v * v')).
 { apply Rplus_le_compat_l. rewrite Rmult_assoc.
   apply Rmult_le_compat_l; try lra. apply Rle_abs. }
 apply Rsqr_incr_0.
 2:{ apply Rplus_le_le_0_compat.
     - rewrite Rmult_assoc. apply Rmult_le_pos; try lra.
       rewrite <- Cmod_mult. apply Cmod_ge_0.
     - apply Rmult_le_pos; try lra. apply Rabs_pos. }
 2:{ repeat apply Rmult_le_pos; try lra; apply sqrt_pos. }
 apply Rminus_le_0.
 rewrite !Rsqr_mult. rewrite !Rsqr_sqrt.
 2:{ apply Rplus_le_le_0_compat.
     apply Rmult_le_pos; try lra. apply Rle_0_sqr. apply Rle_0_sqr. }
 2:{ apply Rplus_le_le_0_compat.
     apply Rmult_le_pos; try lra. apply Rle_0_sqr. apply Rle_0_sqr. }
 rewrite Rsqr_plus, Rabs_mult, !Rsqr_mult.
 rewrite (Rsqr_abs v), (Rsqr_abs v').
 rewrite !Rsqr_pow2. ring_simplify.
 replace (_-_+_) with (8 * (Cmod u * Rabs v' - Cmod u' * Rabs v)^2) by ring.
 apply Rmult_le_pos; try lra. apply pow2_ge_0.
Qed.

Lemma Rnorm_small a b c e :
  Rnorm (Vect a b c) <= e ->
  Rabs a <= 4 * e /\ Rabs b <= 2 * e /\ Rabs c <= 2 * e.
Proof.
 unfold Rnorm. intros H.
 assert (He : 0 <= e). { generalize (sqrt_pos (Rnorm2 (Vect a b c))). lra. }
 apply Rsqr_incr_1 in H; trivial using sqrt_pos.
 rewrite Rsqr_sqrt in H by apply Rnorm2_pos.
 unfold Rnorm2 in H.
 assert (H3 : (a + ν * b + ν ^ 2 * c) ^ 2 <= e²).
 { generalize (Cmod_ge_0 (a + α * b + α ^ 2 * c)). nra. }
 assert (H1 : Cmod (a + α * b + α ^ 2 * c) ^ 2 <= e² / 2).
 { generalize (pow2_ge_0 (a + ν * b + ν ^ 2 * c)). nra. }
 clear H.
 rewrite <- Rsqr_pow2 in H3. apply Rsqr_le_abs_0 in H3.
 rewrite (Rabs_pos_eq e) in H3 by lra.
 replace (Rsqr e/2) with (Rsqr (e/sqrt 2)) in H1.
 2:{ rewrite Rsqr_div', Rsqr_sqrt; lra. }
 rewrite <- Rsqr_pow2 in H1. apply Rsqr_le_abs_0 in H1.
 rewrite (Rabs_pos_eq (e/sqrt 2)) in H1.
 2:{ apply Rcomplements.Rdiv_le_0_compat. lra. apply sqrt_lt_R0; lra. }
 rewrite (Rabs_pos_eq (Cmod _)) in H1 by apply Cmod_ge_0.
 assert (H2 := H1).
 rewrite <- re_le_Cmod in H1.
 rewrite <- im_le_Cmod in H2.
 replace (Re _) with (a + re_α * b + (re_α^2-im_α^2)*c) in H1.
 2:{ unfold α. simpl. ring. }
 replace (Im _) with (im_α * (b + 2*re_α*c)) in H2.
 2:{ unfold α. simpl. ring. }
 rewrite Rabs_mult, (Rabs_pos_eq im_α) in H2 by approx.
 apply Rmult_le_compat_l with (r:=/im_α) in H2; try approx.
 rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l in H2 by approx.
 rewrite (Rmult_comm (/_)) in H2. change (_*/im_α) with (e/sqrt 2/im_α) in H2.
 apply Rcomplements.Rabs_le_between in H1,H2,H3.
 assert (H2' : -e/sqrt 2/im_α-2*re_α*c <= b <= e/sqrt 2/im_α-2*re_α*c) by lra.
 clear H2.
 assert (H3' : -e - (-ν) * e/sqrt 2/im_α + 2 * ν * re_α * c - ν^2*c <=
               a <= e + (-ν) * e/sqrt 2/im_α + 2 * ν * re_α * c - ν^2*c).
 { assert (ν < 0) by approx. nra. }
 clear H3.
 set (u := - re_α ^ 2 + im_α ^ 2 - 2 * ν * re_α + ν^2 + 2*re_α^2).
 assert (H1' : (1+/sqrt 2 - ν/sqrt 2/im_α + re_α/sqrt 2/im_α) * (-e)
               <= -u * c <=
               (1+/sqrt 2 - ν/sqrt 2/im_α + re_α/sqrt 2/im_α) * e).
 { assert (0 < re_α) by approx. unfold u. nra. }
 clear H1.
 destruct H1' as (H1,H1').
 apply Rmult_le_compat_l with (r:=/u) in H1. 2:{ approx. }
 replace (/u * (-u *c)) with (-c) in H1. 2:{ field. approx. }
 apply Rmult_le_compat_l with (r:=/u) in H1'. 2:{ approx. }
 replace (/u * (-u *c)) with (-c) in H1'. 2:{ field. approx. }
 assert (Hc : Rabs c <= 2 * e).
 { rewrite <- (Rabs_Ropp c). apply Rcomplements.Rabs_le_between.
   split.
   - rewrite <- H1, <- Ropp_mult_distr_r, !Ropp_mult_distr_l, <- Rmult_assoc.
     apply Rmult_le_compat_r. lra. approx.
   - rewrite H1', <- Rmult_assoc. apply Rmult_le_compat_r. lra. approx. }
 clear H1 H1' u.
 repeat split; trivial.
 - apply Rcomplements.Rabs_le_between in Hc.
   apply Rcomplements.Rabs_le_between.
   assert (H3 : (-(1-ν/sqrt 2/im_α+2*(ν^2-2*ν*re_α)))*e <= a
                <= (1-ν/sqrt 2/im_α+2*(ν^2-2*ν*re_α))*e).
   { assert (0 < ν^2-2*ν*re_α) by approx. nra. }
   clear H3'. destruct H3 as (H3, H3'). split.
   + rewrite <- H3.
     rewrite !Ropp_mult_distr_l.
     apply Rmult_le_compat_r. lra. approx.
   + rewrite H3'. apply Rmult_le_compat_r. lra. approx.
 - apply Rcomplements.Rabs_le_between in Hc.
   apply Rcomplements.Rabs_le_between.
   assert (H2 : (-(/sqrt 2/im_α+4*re_α))*e <= b <= (/sqrt 2/im_α+4*re_α)*e).
   { assert (0 < re_α) by approx. nra. }
   clear H2'. destruct H2 as (H2, H2'). split.
   + rewrite <- H2.
     rewrite !Ropp_mult_distr_l.
     apply Rmult_le_compat_r. lra. approx.
   + rewrite H2'. apply Rmult_le_compat_r. lra. approx.
Qed.

Definition Vproj1 V := match V with Vect a b c => a end.
Definition Vproj2 V := match V with Vect a b c => b end.
Definition Vproj3 V := match V with Vect a b c => c end.

Definition is_lim_vect u V :=
 is_lim_seq (Vproj1∘u) (Vproj1 V) /\
 is_lim_seq (Vproj2∘u) (Vproj2 V) /\
 is_lim_seq (Vproj3∘u) (Vproj3 V).

Lemma Vproj1_le_4Rnorm V : Rabs (Vproj1 V) <= 4 * Rnorm V.
Proof.
 destruct V as (a,b,c). now apply (Rnorm_small a b c).
Qed.

Lemma Vproj2_le_2Rnorm V : Rabs (Vproj2 V) <= 2 * Rnorm V.
Proof.
 destruct V as (a,b,c). now apply (Rnorm_small a b c).
Qed.

Lemma Vproj3_le_2Rnorm V : Rabs (Vproj3 V) <= 2 * Rnorm V.
Proof.
 destruct V as (a,b,c). now apply (Rnorm_small a b c).
Qed.

Lemma Rnorm_lim0 (u : nat -> vect) :
  is_lim_seq (Rnorm ∘ u) 0 -> is_lim_vect u (Vect 0 0 0).
Proof.
 intros H. repeat split.
 + apply is_lim_seq_scal_l with (a:=4) in H.
   simpl in H. rewrite Rmult_0_r in H.
   eapply is_lim_seq_0_abs; eauto.
   exists O. intros n _. apply Vproj1_le_4Rnorm.
 + apply is_lim_seq_scal_l with (a:=2) in H.
   simpl in H. rewrite Rmult_0_r in H.
   eapply is_lim_seq_0_abs; eauto.
   exists O. intros n _. apply Vproj2_le_2Rnorm.
 + apply is_lim_seq_scal_l with (a:=2) in H.
   simpl in H. rewrite Rmult_0_r in H.
   eapply is_lim_seq_0_abs; eauto.
   exists O. intros n _. apply Vproj3_le_2Rnorm.
Qed.

(** rest is bounded *)

Lemma meandiff_bounded n : Rabs (meandiff n) <= 2.
Proof.
 apply Rcomplements.Rabs_le_between.
 unfold meandiff. revert n.
 assert (forall n:nat, -2 * n <= sumdiff n <= 2 * n).
 { induction n.
   - simpl. unfold sumdiff. simpl. lra.
   - unfold sumdiff in *. rewrite S_INR. simpl.
     generalize (diff_bound n). lra. }
 intros n. destruct (Nat.eq_dec n 0) as [->|Hn].
 { simpl. unfold Rdiv. rewrite Rinv_0, Rmult_0_r. lra. }
 specialize (H n). split.
 - apply (Rmult_le_reg_r n). inr.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_l. lra. inr.
 - apply (Rmult_le_reg_r n). inr.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_l. lra. inr.
Qed.

Lemma diff_4_2_alt n : diff_4_2 n = diff 4 (f 4 n) + τ * diff 4 n.
Proof.
 unfold diff_4_2, diff, τ. simpl. ring.
Qed.

Lemma diff_4_2_bound n : -3 <= diff_4_2 n <= 3.
Proof.
 rewrite diff_4_2_alt.
 generalize (diff_bound (f 4 n)) (diff_bound n) τ_approx.
 unfold Approx. nra.
Qed.

Lemma diff_4_3_alt n :
  diff_4_3 n = diff 4 (fs 4 2 n) + τ * diff 4 (f 4 n) + τ^2 * diff 4 n.
Proof.
 unfold diff_4_3, diff, τ. simpl. ring.
Qed.

Lemma diff_4_3_bound n : -4 <= diff_4_3 n <= 4.
Proof.
 rewrite diff_4_3_alt.
 generalize (diff_bound (fs 4 2 n)) (diff_bound (f 4 n)) (diff_bound n).
 generalize τ_approx.
 unfold Approx. nra.
Qed.

Lemma meandiff_4_2_bounded n : Rabs (meandiff_4_2 n) <= 3.
Proof.
 apply Rcomplements.Rabs_le_between.
 unfold meandiff_4_2. revert n.
 assert (forall n:nat, -3 * n <= sumdiff_4_2 n <= 3 * n).
 { induction n.
   - simpl. unfold sumdiff_4_2. simpl. lra.
   - unfold sumdiff_4_2 in *. rewrite S_INR. simpl.
     generalize (diff_4_2_bound n). lra. }
 intros n. destruct (Nat.eq_dec n 0) as [->|Hn].
 { simpl. unfold Rdiv. rewrite Rinv_0, Rmult_0_r. lra. }
 specialize (H n). split.
 - apply (Rmult_le_reg_r n). inr.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_l. lra. inr.
 - apply (Rmult_le_reg_r n). inr.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_l. lra. inr.
Qed.

Lemma meandiff_4_3_bounded n : Rabs (meandiff_4_3 n) <= 4.
Proof.
 apply Rcomplements.Rabs_le_between.
 unfold meandiff_4_3. revert n.
 assert (forall n:nat, -4 * n <= sumdiff_4_3 n <= 4 * n).
 { induction n.
   - simpl. unfold sumdiff_4_3. simpl. lra.
   - unfold sumdiff_4_3 in *. rewrite S_INR. simpl.
     generalize (diff_4_3_bound n). lra. }
 intros n. destruct (Nat.eq_dec n 0) as [->|Hn].
 { simpl. unfold Rdiv. rewrite Rinv_0, Rmult_0_r. lra. }
 specialize (H n). split.
 - apply (Rmult_le_reg_r n). inr.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_l. lra. inr.
 - apply (Rmult_le_reg_r n). inr.
   unfold Rdiv. rewrite Rmult_assoc, Rinv_l. lra. inr.
Qed.

Lemma Rnorm_vmeandiff_bound n : Rnorm (vmeandiff n) < 16.
Proof.
 unfold Rnorm, Rnorm2, vmeandiff.
 apply Rsqr_incrst_0. 2:apply sqrt_pos. 2:lra. rewrite Rsqr_sqrt.
 2:{ apply Rplus_le_le_0_compat. apply Rmult_le_pos. lra. apply pow2_ge_0.
     apply pow2_ge_0. }
 apply Rle_lt_trans with (2 * 9^2 + 9^2); [|rewrite Rsqr_pow2; lra].
 assert (H1 := meandiff_bounded n).
 assert (H2 := meandiff_4_2_bounded n).
 assert (H3 := meandiff_4_3_bounded n).
 apply Rplus_le_compat.
 - apply Rmult_le_compat_l. lra.
   apply Rpow_le_compat_r. apply Cmod_ge_0.
   rewrite !Cmod_triangle, !Cmod_mult, Cmod_pow, !Cmod_R.
   generalize αmod_approx. unfold Approx. nra.
 - rewrite <- pow2_abs.
   apply Rpow_le_compat_r. apply Rabs_pos.
   rewrite !Rabs_triang, !Rabs_mult.
   rewrite (Rabs_left ν) by approx.
   rewrite (Rabs_pos_eq (ν^2)) by approx.
   generalize ν_approx. unfold Approx. nra.
Qed.

Definition K0 := Cmod α * 16 + Rnorm Vinit + (Cmod α)^4 * 16.

Lemma K0_pos : 0 <= K0.
Proof.
 unfold K0.
 rewrite <- Cmod_pow.
 assert (0 <= Rnorm Vinit) by apply sqrt_pos.
 generalize (Cmod_ge_0 α), (Cmod_ge_0 (α^4)); lra.
Qed.

Lemma rest_bounded n : Rnorm (rest n) <= K0.
Proof.
 unfold rest, K0.
 rewrite !Rnorm_triangle, Rnorm_scal.
 rewrite Rabs_left by lra. replace (-(-1)) with 1 by lra.
 rewrite Rmult_1_l, Rnorm_triangle, Rplus_assoc.
 repeat apply Rplus_le_compat; try lra.
 - rewrite Rnorm_Mapply_le.
   apply Rmult_le_compat_l. apply Cmod_ge_0.
   apply Rlt_le, Rnorm_vmeandiff_bound.
 - rewrite Rnorm_Mapply4_le. apply Rmult_le_compat_l. approx.
   apply Rlt_le, Rnorm_vmeandiff_bound.
Qed.

(** We focus now on the subsequence n=A4 p *)

Lemma ratio_bound p :
  Rabs (A 4 (p-1) / A 4 p - τ) <=
  (2 * Cmod (coefdA 4 α) + Cmod (coefdA 4 ν)) * (τ * Cmod α)^p.
Proof.
 apply Rmult_le_reg_r with (r:=A 4 p).
 { apply lt_0_INR. generalize (A_nz 4 p); lia. }
 rewrite <- (Rabs_right' (A 4 p)) at 2 by inr.
 rewrite <- Rabs_mult.
 replace (_ * A 4 p) with (A 4 (p-1) - τ * A 4 p).
 2:{ field. assert (H := A_nz 4 p); inr. }
 rewrite <- Cmod_R. change τ with (tau 4) at 1.
 rewrite (Equation_dA 4 _ roots_sorted p lia).
 unfold roots. simpl. rewrite Cplus_0_r.
 change αbar with (Cconj α). rewrite coefdA_conj. conj_out.
 rewrite Cplus_assoc, re_alt'. rewrite Cmod_triangle, Cmod_mult, !Cmod_R.
 rewrite Rabs_right' by lra.
 rewrite (Rmult_comm τ), Rpow_mult_distr.
 rewrite <- Rmult_assoc, Rmult_assoc.
 transitivity
   ((2 * Cmod (coefdA 4 α) + Cmod (coefdA 4 ν)) * Cmod α ^ p * 1).
 2:{ apply Rmult_le_compat_l. apply Rmult_le_pos.
     generalize (Cmod_ge_0 (coefdA 4 α)) (Cmod_ge_0 (coefdA 4 ν)); lra.
     apply pow_le, Cmod_ge_0.
     apply Rmult_le_reg_l with (r:=μ^p).
     { apply pow_lt. approx. }
     rewrite τ_μ. rewrite pow_inv.
     field_simplify. 2:{ apply pow_nonzero. approx. }
     apply A_ge_mu_pow. }
 rewrite Rmult_1_r, Rmult_plus_distr_r. apply Rplus_le_compat.
 - rewrite Rmult_assoc. apply Rmult_le_compat_l. lra.
   rewrite re_le_Cmod. now rewrite Cmod_mult, Cmod_pow.
 - rewrite Cmod_mult, Cmod_pow. apply Rmult_le_compat_l. apply Cmod_ge_0.
   apply Rpow_le_compat_r. apply Cmod_ge_0.
   rewrite Cmod_R, Rabs_left; approx.
Qed.

(** Auxiliary sequence used for bounding (vmeandiff∘A) *)

Definition U p := Rnorm (vmeandiff' (A 4 p)) / (τ*Cmod α)^p.

Definition K1 := (2 * Cmod (coefdA 4 α) + Cmod (coefdA 4 ν)) * K0.

Lemma U_pos p : 0 <= U p.
Proof.
 unfold U. apply Rmult_le_pos. apply sqrt_pos.
 apply Rlt_le, Rinv_0_lt_compat. apply pow_lt. approx.
Qed.

Lemma K1_pos : 0 <= K1.
Proof.
 repeat apply Rmult_le_pos.
 generalize (Cmod_ge_0 (coefdA 4 α)) (Cmod_ge_0 (coefdA 4 ν)); lra.
 apply K0_pos.
Qed.

Lemma U_ineq p : (4<=p)%nat -> U p <= U (p-1) + U (p-4) + K1.
Proof.
 intros Hp.
 unfold U.
 apply Rmult_le_reg_r with (r:=(τ * Cmod α) ^ p).
 { apply pow_lt. approx. }
 rewrite !Rmult_plus_distr_r.
 replace p with (S (p-1)) at 6 by lia.
 rewrite <- tech_pow_Rmult.
 replace p with (4+(p-4))%nat at 9 by lia.
 rewrite pow_add.
 field_simplify; try (try split; apply pow_nonzero; approx).
 rewrite vmeandiff'_A_eqn by lia.
 rewrite !Rnorm_triangle, !Rnorm_scal.
 rewrite <- !Rplus_assoc, Rplus_comm, <- Rplus_assoc.
 repeat apply Rplus_le_compat.
 - unfold K1.
   rewrite <- !Rmult_assoc, (Rmult_comm (_^p)). apply Rmult_le_compat.
   + apply Rabs_pos.
   + apply sqrt_pos.
   + apply ratio_bound.
   + apply rest_bounded.
 - rewrite Rabs_pos_eq by approx.
   rewrite (Rmult_comm _ τ), !Rmult_assoc. apply Rmult_le_compat_l.
   approx. rewrite Rnorm_Mapply_le. nra.
 - replace (1-τ) with (τ^4) by ring [τ4].
   rewrite Rabs_pos_eq, !Rmult_assoc by approx. apply Rmult_le_compat_l.
   approx. apply Rnorm_Mapply4_le.
Qed.

Definition K2 := Rmax (U 0) (Rmax (U 1) (Rmax (U 2) (U 3))) + K1.

Lemma K2_pos : 0 <= K2.
Proof.
 apply Rplus_le_le_0_compat. 2:apply K1_pos.
 rewrite Rmax_Rle. left. apply U_pos.
Qed.

Lemma U_scal_A_minus_cst p : U p <= K2 * A 4 p - K1.
Proof.
 induction p as [p IH] using lt_wf_ind.
 destruct (Nat.eq_dec p 0) as [->|P0].
 { simpl. unfold K2. ring_simplify. apply Rmax_l. }
 destruct (Nat.eq_dec p 1) as [->|P1].
 { transitivity (K2*1 - K1).
   - unfold K2. ring_simplify. rewrite <- Rmax_r. apply Rmax_l.
   - simpl. generalize K2_pos. lra. }
 destruct (Nat.eq_dec p 2) as [->|P2].
 { transitivity (K2*1 - K1).
   - unfold K2. ring_simplify. rewrite <- 2 Rmax_r. apply Rmax_l.
   - simpl. generalize K2_pos. lra. }
 destruct (Nat.eq_dec p 3) as [->|P3].
 { transitivity (K2*1 - K1).
   - unfold K2. ring_simplify. rewrite <- 2 Rmax_r. apply Rmax_r.
   - simpl. generalize K2_pos. lra. }
 rewrite U_ineq by lia.
 rewrite !IH by lia.
 ring_simplify.
 destruct p; try easy.
 rewrite A_S. simpl. rewrite Nat.sub_0_r. inr.
Qed.

Lemma U_scal_A p : U p <= K2 * A 4 p.
Proof.
 generalize (U_scal_A_minus_cst p) K1_pos; lra.
Qed.

Lemma Rnorm_vmeandiff'_A_bound p :
  Rnorm (vmeandiff' (A 4 p)) <= K2 * (A 4 p / μ^p) * (Cmod α)^p.
Proof.
 apply Rmult_le_reg_r with (r:=/(τ*Cmod α)^p).
 { apply Rinv_0_lt_compat, pow_lt. approx. }
 change (Rnorm _ */_) with (U p).
 rewrite U_scal_A. apply Req_le.
 rewrite τ_μ, Rpow_mult_distr, pow_inv. field.
 split; apply pow_nonzero; approx.
Qed.

Definition K3 := Rbar.real (Sup_seq (fun p => A 4 p / μ^p)).

Lemma A4_le_pow_mu p : A 4 p <= K3 * μ^p.
Proof.
 apply Rmult_le_reg_r with (r:=/μ^p).
 { apply Rinv_0_lt_compat. apply pow_lt. approx. }
 rewrite Rmult_assoc, Rinv_r, Rmult_1_r.
 2:{ apply pow_nonzero. approx. }
 apply (finite_lim_bounded (fun p => A 4 p  / μ^p)).
 exists (coef_mu 4). apply ThePoly.A_div_pow_mu_limit.
Qed.

Lemma K3_pos : 0 <= K3.
Proof.
 generalize (A4_le_pow_mu 0). simpl. lra.
Qed.

Definition K4 := K2 * K3.

Lemma K4_pos : 0 <= K4.
Proof.
 apply Rmult_le_pos. apply K2_pos. apply K3_pos.
Qed.

Lemma Rnorm_vmeandiff'_A_bound' p :
  Rnorm (vmeandiff' (A 4 p)) <= K4 * (Cmod α)^p.
Proof.
 rewrite Rnorm_vmeandiff'_A_bound. unfold K4.
 apply Rmult_le_compat_r. apply pow_le, Cmod_ge_0.
 apply Rmult_le_compat_l. apply K2_pos.
 rewrite (finite_lim_bounded (fun p => A 4 p / μ^p)); try easy.
 exists (coef_mu 4). apply ThePoly.A_div_pow_mu_limit.
Qed.

Definition rate := Cmod α * μ.

Definition K5 := K4 * K3.

Lemma K5_pos : 0 <= K5.
Proof.
 apply Rmult_le_pos. apply K4_pos. apply K3_pos.
Qed.

Lemma Rnorm_vsumdiff'_A p : Rnorm (vsumdiff' (A 4 p)) <= K5 * rate^p.
Proof.
 unfold vsumdiff'.
 assert (H := Rnorm_vmeandiff'_A_bound' p).
 unfold vmeandiff' in H. rewrite vmeandiff_alt in H.
 unfold Vscale in H. apply Rmult_le_compat_r with (r:=A 4 p) in H. 2:inr.
 etransitivity; [|etransitivity; [apply H|]].
 - rewrite Rmult_comm.
   rewrite <- (Rabs_right' (A 4 p)) at 2 by inr.
   rewrite <- Rnorm_scal.
   apply Req_le. f_equal.
   rewrite Vscal_Vadd_r, !Vscal_Vscal. f_equal; [|f_equal; ring].
   rewrite Rinv_r, Vscal_1; trivial.
   assert (H' := A_nz 4 p); inr.
 - unfold K5. rewrite !Rmult_assoc.
   apply Rmult_le_compat_l. apply K4_pos.
   unfold rate.
   rewrite Rpow_mult_distr, <- Rmult_assoc, (Rmult_comm K3), Rmult_assoc.
   apply Rmult_le_compat_l. { apply pow_le. approx. }
   apply A4_le_pow_mu.
Qed.

Lemma vsumdiff_split p n : (n < A 4 (p-3))%nat ->
  vsumdiff (n + A 4 p) =
  vsumdiff n ++ vsumdiff (A 4 p) ++ n ** vdiff (A 4 p).
Proof.
 intros Hn.
 rewrite Nat.add_comm.
 assert (E := vdiff_add p).
 unfold vsumdiff, vdiff, sumdiff, sumdiff_4_2, sumdiff_4_3 in *.
 simpl in *.
 rewrite !big_sum_sum. simpl. f_equal.
 - ring_simplify. rewrite Rplus_assoc. f_equal.
   erewrite big_sum_eq_bounded.
   2:{ intros x Hx. injection (E x lia) as E1 E2 E3.
       now rewrite Nat.add_comm, E1. }
   rewrite big_sum_Rplus, big_sum_Rconst. ring.
 - ring_simplify. rewrite Rplus_assoc. f_equal.
   erewrite big_sum_eq_bounded.
   2:{ intros x Hx. injection (E x lia) as E1 E2 E3.
       now rewrite Nat.add_comm, E2. }
   rewrite big_sum_Rplus, big_sum_Rconst. ring.
 - ring_simplify. rewrite Rplus_assoc. f_equal.
   erewrite big_sum_eq_bounded.
   2:{ intros x Hx. injection (E x lia) as E1 E2 E3.
       now rewrite Nat.add_comm, E3. }
   rewrite big_sum_Rplus, big_sum_Rconst. ring.
Qed.

Lemma vsumdiff'_split p n : (n < A 4 (p-3))%nat ->
  vsumdiff' (n + A 4 p) =
  vsumdiff' n ++ vsumdiff' (A 4 p) ++ n ** vdiff (A 4 p).
Proof.
 intros. unfold vsumdiff'. rewrite vsumdiff_split by trivial.
 rewrite <- !Vadd_assoc. f_equal.
 rewrite (Vadd_comm (-n ** limit)), <- Vadd_assoc. f_equal.
 rewrite (Vadd_comm (_ ** limit)), <- Vadd_assoc. f_equal.
 rewrite Vscal_Vadd_l. f_equal. rewrite plus_INR. ring.
Qed.

Definition K6 := (K5 + K3 * Rnorm Vinit) / (rate - 1).

Lemma K6_pos : 0 <= K6.
Proof.
 apply Rcomplements.Rdiv_le_0_compat. 2:approx.
 apply Rplus_le_le_0_compat; apply Rmult_le_pos; trivial using K3_pos, K4_pos.
 apply sqrt_pos.
Qed.

Lemma Rnorm_vdiff_A p : Rnorm (vdiff (A 4 p)) <= (Cmod α)^p * Rnorm Vinit.
Proof.
 induction p.
 - simpl. rewrite Vinit_ok. lra.
 - rewrite vdiff_A_S, Rnorm_Mapply_le. simpl pow.
   rewrite Rmult_assoc. apply Rmult_le_compat_l; trivial. approx.
Qed.

Lemma vsumdiff'_ineq p n : (n < A 4 p)%nat ->
  Rnorm (vsumdiff' n) <= K6 * rate^p.
Proof.
 revert n.
 induction p as [[|p] IH] using lt_wf_ind.
 - simpl. intros n Hn. replace n with O by lia.
   unfold vsumdiff'. rewrite vsumdiff_0.
   replace (Rnorm _) with 0; try (generalize K6_pos; lra).
   symmetry. apply Rnorm_0_iff. simpl. f_equal; ring.
 - intros n Hn.
   destruct (Nat.lt_ge_cases n (A 4 p)).
   + rewrite (IH p); try lia.
     apply Rmult_le_compat_l. apply K6_pos.
     simpl. rewrite <- (Rmult_1_l (rate^p)) at 1.
     apply Rmult_le_compat_r. apply pow_le. approx. approx.
   + replace n with ((n-A 4 p) + A 4 p)%nat by lia.
     rewrite vsumdiff'_split by (simpl in Hn; lia).
     rewrite 2 Rnorm_triangle, Rnorm_scal.
     assert (LE := Rnorm_vdiff_A p).
     apply Rmult_le_compat_l with (r := Rabs (n - A 4 p)%nat) in LE.
     2:{ apply Rabs_pos. }
     rewrite LE. clear LE.
     rewrite Rnorm_vsumdiff'_A.
     rewrite (IH (p-3)%nat) by (simpl in Hn; lia).
     rewrite Rabs_right' by inr.
     assert (LT : (n-A 4 p <= A 4 p)%nat).
     { simpl in Hn. generalize (@A_mono 4 (p-3) p lia). lia. }
     apply le_INR in LT.
     rewrite A4_le_pow_mu in LT.
     apply Rmult_le_compat_r with (r:=(Cmod α^p * Rnorm Vinit)) in LT.
     2:{ apply Rmult_le_pos. apply pow_le. approx. apply sqrt_pos. }
     rewrite LT. clear LT.
     replace (K3 * _ * _) with ((K3 * Rnorm Vinit) * rate ^p).
     2:{ unfold rate. rewrite Rpow_mult_distr. ring. }
     rewrite <- Rmult_plus_distr_r.
     replace (K5+_) with (K6 * (rate -1)).
     2:{ unfold K6. field. approx. }
     rewrite Rmult_assoc, <- Rmult_plus_distr_l.
     apply Rmult_le_compat_l. apply K6_pos.
     rewrite (Rle_pow rate (p-3) p) by (lia||approx). simpl. lra.
Qed.

Definition K7 := K6 * rate.

Lemma K7_pos : 0 <= K7.
Proof.
 apply Rmult_le_pos. apply K6_pos. approx.
Qed.

Lemma exp_increasing' x y : x <= y -> exp x <= exp y.
Proof.
 generalize (exp_lt_inv y x); lra.
Qed.

Lemma vsumdiff'_ineq' n : Rnorm (vsumdiff' n) <= K7 * Rpower n 0.9.
Proof.
 destruct (Nat.eq_dec n 0) as [->|Hn].
 - simpl. unfold vsumdiff'.
   replace (Rnorm _) with 0. apply Rmult_le_pos. apply K7_pos.
   apply Rlt_le, Rpower_pos.
   symmetry. apply Rnorm_0_iff. rewrite vsumdiff_0. simpl. f_equal; ring.
 - assert (H := invA_spec 4 (n-1)).
   set (p := invA 4 (n-1)) in *.
   replace (S (n-1)) with n in  H by lia.
   rewrite (vsumdiff'_ineq (S p) n) by lia. simpl.
   rewrite <- !Rmult_assoc. apply Rmult_le_compat_l. apply K7_pos.
   rewrite <- Rpower_pow by approx. unfold Rpower.
   apply exp_increasing'.
   assert (H' := A_ge_mu_pow 4 p). change (mu 4) with μ in H'.
   assert (LE : rate^10 < μ^9) by approx.
   apply ln_increasing in LE; [|approx].
   rewrite !ln_pow in LE by approx.
   transitivity (p * (0.9 * ln μ)).
   + apply Rmult_le_compat_l. inr. simpl in LE; lra.
   + replace (p * (0.9 * ln μ)) with (0.9 * (p * ln μ)) by ring.
     apply Rmult_le_compat_l. lra.
     rewrite <- ln_pow by approx.
     apply ln_nondecreasing.
     * apply pow_lt. approx.
     * destruct H as (H,_). inr.
Qed.

Lemma vmeandiff'_ineq n : n<>O ->
  Rnorm (vmeandiff' n) <= K7 * Rpower n (-0.1).
Proof.
 intros Hn.
 assert (0 < n) by inr.
 unfold vmeandiff'. rewrite vmeandiff_alt.
 replace (-1) with (/n * (-n)). 2:{ field. intros [=E]; lra. }
 rewrite <- Vscal_Vscal, <- Vscal_Vadd_r, Rnorm_scal. fold (vsumdiff' n).
 rewrite Rabs_pos_eq. 2:{ now apply Rlt_le, Rinv_0_lt_compat. }
 apply Rmult_le_reg_l with (r:=n); trivial. field_simplify; try lra.
 rewrite vsumdiff'_ineq'. apply Req_le.
 rewrite (Rmult_comm _ K7), Rmult_assoc. f_equal.
 replace 0.9 with (1+-0.1) by lra. rewrite Rpower_plus. f_equal.
 now apply Rpower_1.
Qed.

Lemma Rnorm_vmeandiff'_CV : is_lim_seq (Rnorm ∘ vmeandiff') 0.
Proof.
 apply is_lim_seq_le_le_loc with
  (u:=fun _ => 0) (w:=fun n => K7 * Rpower n (-0.1)).
 - exists 1%nat. intros n Hn. split.
   apply sqrt_pos. apply vmeandiff'_ineq. lia.
 - apply is_lim_seq_const.
 - replace 0 with (K7 * 0) by lra.
   apply is_lim_seq_mult'. apply is_lim_seq_const. apply Rpower_lim_zero; lra.
Qed.

Lemma meandiff_CV :
  is_lim_seq meandiff limit1 /\
  is_lim_seq meandiff_4_2 limit2 /\
  is_lim_seq meandiff_4_3 limit3.
Proof.
 assert (H := Rnorm_vmeandiff'_CV). apply Rnorm_lim0 in H.
 unfold is_lim_vect in H. simpl in H.
 unfold vmeandiff', vmeandiff, limit, "∘" in H. simpl in H.
 destruct H as (H1 & H2 & H3). repeat split.
 - replace limit1 with (0+limit1) by lra.
   eapply is_lim_seq_ext.
   { intros n. symmetry.
     replace (meandiff n) with ((meandiff n + -1 * limit1) + limit1) by lra.
     reflexivity. }
   apply is_lim_seq_plus'; trivial. apply is_lim_seq_const.
 - replace limit2 with (0+limit2) by lra.
   eapply is_lim_seq_ext.
   { intros n. symmetry.
     replace (meandiff_4_2 n) with ((meandiff_4_2 n + -1 * limit2) + limit2)
       by lra.
     reflexivity. }
   apply is_lim_seq_plus'; trivial. apply is_lim_seq_const.
 - replace limit3 with (0+limit3) by lra.
   eapply is_lim_seq_ext.
   { intros n. symmetry.
     replace (meandiff_4_3 n) with ((meandiff_4_3 n + -1 * limit3) + limit3)
       by lra.
     reflexivity. }
   apply is_lim_seq_plus'; trivial. apply is_lim_seq_const.
Qed.
