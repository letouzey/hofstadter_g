From Coq Require Import Arith Reals Lra Lia Permutation Morphisms.
From QuantumLib Require Import Complex Matrix VecSet.
Require Import MoreList.
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

Lemma mkvect_eqn n l i : mkvect n l i O = nth i l 0.
Proof.
 unfold mkvect, list2D_to_matrix.
 set (f := fun x => [x]).
 destruct (Nat.lt_ge_cases i (length l)).
 - rewrite nth_map_indep with (d':=C0); auto.
 - rewrite nth_overflow with (n:=i) by now rewrite map_length.
   simpl. now rewrite nth_overflow.
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

(** Scalar product *)

Definition scalprod {n} (v v' : Vector n) : C :=
 Mmult (transpose v) v' O O.

Lemma scalprod_alt {n} (v v' : Vector n) :
 scalprod v v' = Σ (fun i => v i O * v' i O) n.
Proof.
 now unfold scalprod, Mmult, transpose.
Qed.

Lemma bigsum_ext {G} {H : Monoid G} (f g : nat -> G) n :
 (forall x, (x < n)%nat -> f x = g x) -> big_sum f n = big_sum g n.
Proof.
 induction n; simpl; intros; f_equal; auto.
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

(** Auxiliary matrix manipulations : addrows and cols_scale *)

(** addrows changes the rows [M_i] into [M_i - c*M_{i-1}] *)

Fixpoint addrowsaux {n} c (M : Square n) k :=
 match k with
 | 0 => M
 | S k => addrowsaux c (row_add M (S k) k (Copp c)) k
 end.

Definition addrows {n} c (M : Square (S n)) := addrowsaux c M n.

Lemma det_addrowsaux k n c (M : Square n) : (k < n)%nat ->
  Determinant (addrowsaux c M k) = Determinant M.
Proof.
 revert M.
 induction k; intros M Hk; simpl; try easy.
 rewrite IHk, Determinant_row_add; trivial; lia.
Qed.

Lemma det_addrows n c (M : Square (S n)) :
  Determinant (addrows c M) = Determinant M.
Proof.
 apply det_addrowsaux; lia.
Qed.

Lemma addrowsaux_spec0 k n c (M:Square n) p :
 (addrowsaux c M k) O p = M O p.
Proof.
 revert M.
 induction k; simpl; auto.
 intros M. rewrite IHk. now unfold row_add.
Qed.

Lemma addrows_spec0 n c (M : Square (S n)) p :
 addrows c M O p = M O p.
Proof.
 apply addrowsaux_spec0.
Qed.

Lemma addrowsaux_specS k n c (M:Square n) p q :
 (k < n)%nat ->
 (addrowsaux c M k) (S p) q =
 if p <? k then M (S p) q - c * M p q else M (S p) q.
Proof.
 revert p M.
 induction k; simpl; auto.
 intros p M Hk.
 unfold row_add.
 rewrite IHk by lia.
 simpl.
 case Nat.ltb_spec; try lia; case Nat.eqb_spec; try lia; intros.
 - case Nat.eqb_spec; try lia; intros.
   case Nat.ltb_spec; try lia; intros. lca.
 - subst. case Nat.ltb_spec; try lia; intros. lca.
 - case Nat.ltb_spec; try lia; intros. lca.
Qed.

Lemma addrows_specS n c (M:Square (S n)) p q :
 (p < n)%nat ->
 addrows c M (S p) q = M (S p) q - c * M p q.
Proof.
 unfold addrows. intros Hp. rewrite addrowsaux_specS by lia.
 apply Nat.ltb_lt in Hp. now rewrite Hp.
Qed.

(** cols_scale scales the j-th columns by the j-th element of a list *)

Fixpoint cols_scale {n} p l (M : Square n) :=
 match l with
 | [] => M
 | c::l => cols_scale (S p) l (col_scale M p c)
 end.

Lemma cols_scale_altgen n p l (M : Square n) :
 cols_scale p l M ==
  fun i j => (if p <=? j then nth (j-p) l C1 else C1) * M i j.
Proof.
 revert p M.
 induction l; simpl; intros p M i j Hi Hj.
 - case Nat.leb_spec; intros; try lca. destruct (j-p)%nat; lca.
 - rewrite IHl by trivial. unfold col_scale.
   do 2 case Nat.leb_spec; intros; try lia;
    case Nat.eqb_spec; intros; try lia; trivial.
   + destruct (j-p)%nat as [|k] eqn:E; intros; try lia.
     f_equal. f_equal. lia.
   + subst. rewrite Nat.sub_diag. lca.
Qed.

Lemma cols_scale_alt n l (M : Square n) :
 cols_scale 0 l M == fun i j => nth j l C1 * M i j.
Proof.
 intros i j Hi Hj. rewrite cols_scale_altgen; simpl; trivial.
 now rewrite Nat.sub_0_r.
Qed.

Lemma cols_scale_det n p l (M : Square n) :
 (p + length l <= n)%nat ->
 Determinant (cols_scale p l M) = G_big_mult l * Determinant M.
Proof.
 revert p M.
 induction l; simpl; intros; try lca.
 rewrite IHl by lia. rewrite Determinant_col_scale by lia. lca.
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
  fun i j => if (i <? n) && (j <? n) then (nth j l C0)^i else C0.

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

[[1;  1;  1;  1];
 [x;  y;  z;  t];
 [x^2;y^2;z^2;t^2];
 [x^3;y^3;z^3;t^3]]

and its determinant is [(y-x)*(z-x)*(t-x)*(z-y)*(t-y)*(t-z)].

For proving that, we substract each row by x times the previous one,
leading to:

[[1; 1;        1;        1];
 [0; y-x;      z-x;      t-x];
 [0; y*(y-x);  z*(z-x);  t(t-x)];
 [0; y^2*(y-x);z^2*(z-x);t^2*(t-x)]]

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
   set (W := addrows x V).
   rewrite <- (det_addrows n' x V) by lia. fold W.
   unfold n'. rewrite Det_simplify. fold n'.
   rewrite big_sum_shift.
   rewrite big_sum_eq_bounded with (g := fun _ => C0).
   2:{ intros i Hi. unfold W. rewrite addrows_specS by lia.
       unfold V at 1 2; unfold Vandermonde.
       repeat (case Nat.ltb_spec; try lia; intros _). simpl. lca. }
   rewrite big_sum_0; auto.
   replace (W O O) with C1.
   2:{ symmetry. unfold W. rewrite addrows_spec0.
       unfold V, Vandermonde; lca. }
   simpl parity.
   simpl multdiffs.
   assert (get_minor W 0 0 ==
           cols_scale 0 (map (fun y => y-x) l) (Vandermonde n' l)).
   { intros i j Hi Hj.
     rewrite cols_scale_alt by trivial.
     unfold W, get_minor. simpl. rewrite addrows_specS by trivial.
     unfold V, Vandermonde. simpl.
     repeat (case Nat.ltb_spec; intros; try lia). simpl.
     rewrite nth_map_indep with (d':=C0); try lia. lca. }
   rewrite H.
   rewrite cols_scale_det by (rewrite map_length; lia).
   rewrite IH by trivial. lca.
Qed.
