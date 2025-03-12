From Coq Require Import Arith Reals Lra Lia Permutation Morphisms.
From Hofstadter.MiniQuantumLib Require Import Complex Matrix VecSet.
Require Import MoreList MoreComplex.
Local Open Scope C.

(** * Complements about QuantumLib matrices *)

Fixpoint Mpow {n} (M:Square n) m : Square n :=
 match m with
 | O => I n
 | S m => M × Mpow M m
 end.

Lemma WF_Mpow {n} (M:Square n) m : WF_Matrix M -> WF_Matrix (Mpow M m).
Proof.
 induction m; simpl; auto using WF_I, WF_mult.
Qed.

(** Mconj of QuantumLib is too restrictive (only on Square) *)

Definition Mconj {n m} (M:Matrix n m) : Matrix n m :=
 fun i j => Cconj (M i j).

Lemma WF_Mconj {n m} (M : Matrix n m) : WF_Matrix M -> WF_Matrix (Mconj M).
Proof.
 intros WF x y Hxy. unfold Mconj. rewrite (WF x y Hxy). lca.
Qed.

Lemma Mconj_scale {n m} c (M : Matrix n m) :
 Mconj (c .* M) = Cconj c .* Mconj M.
Proof.
 apply functional_extensionality. intros i.
 apply functional_extensionality. intros j.
 unfold Mconj, scale; cbn. apply Cconj_mult_distr.
Qed.

Definition mkvect n l : Vector n := list2D_to_matrix (map (fun x => [x]) l).
Definition mkvectR n l : Vector n := mkvect n (map RtoC l).

Lemma mkvect_eqn n l i : mkvect n l i O = l @ i.
Proof.
 unfold mkvect, list2D_to_matrix.
 set (f := fun x => [x]).
 destruct (Nat.lt_ge_cases i (length l)).
 - rewrite nth_map_indep with (d':=C0); auto.
 - rewrite nth_overflow with (n:=i) by now rewrite map_length.
   simpl. unfold Cnth. now rewrite nth_overflow.
Qed.

Lemma WF_mkvect n l : length l = n -> WF_Matrix (mkvect n l).
Proof.
 intros.
 apply WF_list2D_to_matrix; simpl.
 - now rewrite map_length.
 - intros li. rewrite in_map_iff. now intros (x & <- & _).
Qed.

Lemma WF_mkvectR n l : length l = n -> WF_Matrix (mkvectR n l).
Proof.
 intros. apply WF_mkvect. now rewrite map_length.
Qed.

#[export] Hint Resolve WF_Mpow WF_Mconj WF_mkvect WF_mkvectR : wf_db.

(** Specialized versions of mat_equiv_eq for 3D Vectors and Matrix *)

Lemma Vect3_eq (V V' : Vector 3) : WF_Matrix V -> WF_Matrix V' ->
 (V 0 0 = V' 0 0 -> V 1 0 = V' 1 0 -> V 2 0 = V' 2 0 -> V = V')%nat.
Proof.
 intros. apply mat_equiv_eq; auto. intros i j Hi Hj.
 replace j with O by lia; clear j Hj.
 destruct i as [|[|[|?] ] ]; try lia; trivial.
Qed.

Lemma Mat3_eq (M M' : Square 3) : WF_Matrix M -> WF_Matrix M' ->
 (M 0 0 = M' 0 0 -> M 1 0 = M' 1 0 -> M 2 0 = M' 2 0 ->
  M 0 1 = M' 0 1 -> M 1 1 = M' 1 1 -> M 2 1 = M' 2 1 ->
  M 0 2 = M' 0 2 -> M 1 2 = M' 1 2 -> M 2 2 = M' 2 2 -> M = M')%nat.
Proof.
 intros. apply mat_equiv_eq; auto. intros i j Hi Hj.
 destruct i as [|[|[|?] ] ]; try lia;
 destruct j as [|[|[|?] ] ]; try lia; trivial.
Qed.

(** [get_col] and multiplication *)

Lemma get_col_mult n m p (A : Matrix n m) (B : Matrix m p) q :
 Mmult A (get_col B q) == get_col (Mmult A B) q.
Proof.
 intros i j Hi Hj. unfold get_col, Mmult. case Nat.eqb_spec; auto; lia.
Qed.

Lemma get_col_mult_eq n m p (A : Matrix n m) (B : Matrix m p) q :
 WF_Matrix A -> WF_Matrix B ->
 Mmult A (get_col B q) = get_col (Mmult A B) q.
Proof.
 intros. apply mat_equiv_eq; auto using WF_get_col, WF_mult.
 apply get_col_mult.
Qed.

(** Scalar product *)

Definition scalprod {n} (v v' : Vector n) : C :=
 Mmult (transpose v) v' O O.

Lemma scalprod_alt {n} (v v' : Vector n) :
 scalprod v v' = Σ (fun i => v i O * v' i O) n.
Proof.
 now unfold scalprod, Mmult, transpose.
Qed.

(** More on determinant *)

Lemma Determinant_row_add {n} (A : Square n) (i j : nat) (c : C) :
  (i < n)%nat -> (j < n)%nat -> i <> j ->
  Determinant (row_add A i j c) = Determinant A.
Proof.
 intros Hi Hj D.
 rewrite <- (transpose_involutive _ _ A) at 1.
 rewrite <- col_add_transpose, <- Determinant_transpose.
 rewrite Determinant_col_add; auto.
 apply Determinant_transpose.
Qed.

(** Auxiliary matrix manipulations : addcols and rows_scale *)

(** addcols changes the cols [M_i] into [M_i - c*M_{i-1}] *)

Fixpoint addcolsaux {n} c (M : Square n) k :=
 match k with
 | 0 => M
 | S k => addcolsaux c (col_add M (S k) k (Copp c)) k
 end.

Definition addcols {n} c (M : Square (S n)) := addcolsaux c M n.

Lemma det_addcolsaux k n c (M : Square n) : (k < n)%nat ->
  Determinant (addcolsaux c M k) = Determinant M.
Proof.
 revert M.
 induction k; intros M Hk; simpl; try easy.
 rewrite IHk, Determinant_col_add; trivial; lia.
Qed.

Lemma det_addcols n c (M : Square (S n)) :
  Determinant (addcols c M) = Determinant M.
Proof.
 apply det_addcolsaux; lia.
Qed.

Lemma addcolsaux_spec0 k n c (M:Square n) p :
 (addcolsaux c M k) p O = M p O.
Proof.
 revert M.
 induction k; simpl; auto.
 intros M. rewrite IHk. now unfold col_add.
Qed.

Lemma addcols_spec0 n c (M : Square (S n)) p :
 addcols c M p O = M p O.
Proof.
 apply addcolsaux_spec0.
Qed.

Lemma addcolsaux_specS k n c (M:Square n) p q :
 (k < n)%nat ->
 (addcolsaux c M k) p (S q) =
 if q <? k then M p (S q) - c * M p q else M p (S q).
Proof.
 revert q M.
 induction k; simpl; auto.
 intros q M Hk.
 unfold col_add.
 rewrite IHk by lia.
 simpl.
 case Nat.ltb_spec; try lia; case Nat.eqb_spec; try lia; intros.
 - case Nat.eqb_spec; try lia; intros.
   case Nat.ltb_spec; try lia; intros. lca.
 - subst. case Nat.ltb_spec; try lia; intros. lca.
 - case Nat.ltb_spec; try lia; intros. lca.
Qed.

Lemma addcols_specS n c (M:Square (S n)) p q :
 (q < n)%nat ->
 addcols c M p (S q) = M p (S q) - c * M p q.
Proof.
 unfold addcols. intros Hq. rewrite addcolsaux_specS by lia.
 apply Nat.ltb_lt in Hq. now rewrite Hq.
Qed.

(** rows_scale scales the i-th rows by the i-th element of a list *)

Fixpoint rows_scale {n} p l (M : Square n) :=
 match l with
 | [] => M
 | c::l => rows_scale (S p) l (row_scale M p c)
 end.

Lemma rows_scale_altgen n p l (M : Square n) :
 rows_scale p l M ==
  fun i j => (if p <=? i then nth (i-p) l C1 else C1) * M i j.
Proof.
 revert p M.
 induction l; simpl; intros p M i j Hi Hj.
 - case Nat.leb_spec; intros; try lca. destruct (i-p)%nat; lca.
 - rewrite IHl by trivial. unfold row_scale.
   do 2 case Nat.leb_spec; intros; try lia;
    case Nat.eqb_spec; intros; try lia; trivial.
   + destruct (i-p)%nat as [|k] eqn:E; intros; try lia.
     f_equal. f_equal. lia.
   + subst. rewrite Nat.sub_diag. lca.
Qed.

Lemma rows_scale_alt n l (M : Square n) :
 rows_scale 0 l M == fun i j => nth i l C1 * M i j.
Proof.
 intros i j Hi Hj. rewrite rows_scale_altgen; simpl; trivial.
 now rewrite Nat.sub_0_r.
Qed.

Lemma rows_scale_det n p l (M : Square n) :
 (p + length l <= n)%nat ->
 Determinant (rows_scale p l M) = G_big_mult l * Determinant M.
Proof.
 revert p M.
 induction l; simpl; intros; try lca.
 rewrite IHl by lia. rewrite Determinant_row_scale by lia. lca.
Qed.

(** Determinant and matrix equality *)

Lemma get_minor_compat {n} (A B : Square (S n)) : A == B ->
 forall x y, get_minor A x y == get_minor B x y.
Proof.
 intros E x y i j Hi Hj. unfold get_minor.
 do 2 (case Nat.ltb_spec; intros); apply E; lia.
Qed.

Lemma Determinant_compat {n} (A B : Square n) : A == B ->
 Determinant A = Determinant B.
Proof.
 revert A B. induction n as [|[|] IH]; intros A B E; try easy.
 - simpl. apply E; lia.
 - rewrite !Det_simplify.
   apply big_sum_eq_bounded; intros x Hx.
   f_equal.
   + f_equal. apply E; lia.
   + apply IH. now apply get_minor_compat.
Qed.

Global Instance : forall n, Proper (@mat_equiv n n ==> eq) Determinant.
Proof.
 exact @Determinant_compat.
Qed.

(** Vandermonde matrix and its determinant *)

Definition Vandermonde n (l : list C) : Square n :=
  fun i j => if (i <? n) && (j <? n) then (l @ i)^j else C0.

Lemma WF_Vandermonde n (l : list C) : WF_Matrix (Vandermonde n l).
Proof.
 intros x y [Hx|Hy]; unfold Vandermonde;
 do 2 case Nat.ltb_spec; trivial; lia.
Qed.

Fixpoint multdiffs (l : list C) :=
 match l with
 | [] => C1
 | x::l => G_big_mult (map (fun y => y-x) l) * multdiffs l
 end.

(** Determinant of the Vandermonde matrix.

For example, with n=4 and l=[x;y;z;t], the Vandermonde matrix is

[[1; x; x^2; x^3];
 [1; y; y^2; y^3];
 [1; z; z^2; z^3];
 [1; t; t^2; t^3]]

and its determinant is [(y-x)*(z-x)*(t-x)*(z-y)*(t-y)*(t-z)].

For proving that, we substract each col by x times the previous one,
leading to:

[[1; 0;   0;       0        ];
 [1; y-x; y*(y-x); y^2*(y-x)];
 [1; z-x; z*(z-x); z^2*(z-x)];
 [1; t-x; t*(t-x); t^2*(t-x)]]

After removing the first row and column, the columns can be factorised
by [y-x] or [z-x] or [t-x], and that leaves us with a Vandermonde of
dimension 3.
*)

Lemma Vandermonde_det n (l : list C) :
 length l = n -> Determinant (Vandermonde n l) = multdiffs l.
Proof.
 revert l.
 induction n as [|[|n] IH]; intros l Hn.
 - simpl. now destruct l.
 - simpl. unfold Vandermonde. simpl. destruct l as [|x [|y l] ]; try easy.
   lca.
 - set (n' := S n) in *.
   set (V := Vandermonde (S n') l).
   destruct l as [|x l]; try easy. simpl in Hn. injection Hn as Hn.
   set (W := addcols x V).
   rewrite <- (det_addcols n' x V) by lia. fold W.
   unfold n'. rewrite Determinant_transpose, Det_simplify. fold n'.
   unfold transpose at 1.
   rewrite big_sum_shift.
   rewrite big_sum_eq_bounded with (g := fun _ => C0).
   2:{ intros i Hi. rewrite !Cmult_integral. left; right.
       unfold W, V, Vandermonde, Cnth. rewrite addcols_specS by lia.
       repeat (case Nat.ltb_spec; try lia; intros _). simpl. lca. }
   rewrite big_sum_0; auto.
   rewrite <- get_minor_transpose, <- Determinant_transpose.
   replace (W O O) with C1.
   2:{ symmetry. unfold W. rewrite addcols_spec0.
       unfold V, Vandermonde; lca. }
   simpl parity.
   simpl multdiffs.
   assert (get_minor W 0 0 ==
           rows_scale 0 (map (fun y => y-x) l) (Vandermonde n' l)).
   { intros i j Hi Hj.
     rewrite rows_scale_alt by trivial.
     unfold W, get_minor. simpl. rewrite addcols_specS by trivial.
     unfold V, Vandermonde, Cnth. simpl.
     repeat (case Nat.ltb_spec; intros; try lia). simpl.
     rewrite nth_map_indep with (d':=C0); try lia. lca. }
   rewrite H.
   rewrite rows_scale_det by (rewrite map_length; lia).
   rewrite IH by trivial. lca.
Qed.

Lemma get_minor_vandermonde n (l:list C) i : (i <= n)%nat ->
  get_minor (Vandermonde (S n) l) i n = Vandermonde n (remove_at i l).
Proof.
 intros Hi.
 apply mat_equiv_eq.
 - apply WF_get_minor, WF_Vandermonde; try lia.
 - apply WF_Vandermonde.
 - intros x y Hx Hy. unfold get_minor, Vandermonde, Cnth.
   rewrite remove_at_nth.
   repeat (case Nat.ltb_spec; try lia; simpl; trivial).
Qed.

(** An expression of the inverse matrix, thanks to the adjugate matrix. *)

Definition Minverse {n} (A:Square n) := /Determinant A .* adjugate A.

Lemma Minverse_is_inv {n} (A:Square n) :
  WF_Matrix A -> invertible A -> Minv A (Minverse A).
Proof.
 intros WF H. apply invertible_iff_det_neq_0 in H; trivial.
 red. unfold Minverse. rewrite Mscale_mult_dist_r, Mscale_mult_dist_l.
 split.
 - destruct n.
   + simpl.
     apply functional_extensionality. intros i.
     apply functional_extensionality. intros j.
     unfold Mmult, scale. simpl. rewrite Cmult_0_r. unfold I.
     case Nat.ltb_spec; try lia. now case Nat.eqb.
   + rewrite mult_by_adjugate_r; trivial.
     rewrite Mscale_assoc, Cinv_l, Mscale_1_l; trivial.
 - rewrite mult_by_adjugate_l; trivial.
   rewrite Mscale_assoc, Cinv_l, Mscale_1_l; trivial.
Qed.
