From Coq Require Import Arith Reals Lra Lia Permutation Morphisms.
From QuantumLib Require Import Complex Matrix VecSet.
Require Import MoreList MorePermut.
Local Open Scope C.

(** * Complements about QuantumLib matrices *)

(** More on big sums and products *)

Lemma Gbigplus_permut (l l' : list C) :
  Permutation l l' -> G_big_plus l = G_big_plus l'.
Proof.
 induction 1; simpl; auto; try lca; try congruence.
Qed.

Lemma Gbigmult_permut (l l' : list C) :
  Permutation l l' -> G_big_mult l = G_big_mult l'.
Proof.
 induction 1; simpl; auto; try lca; try congruence.
Qed.

Lemma Gbigplus_factor c (l : list C) :
 G_big_plus (map (Cmult c) l) = c * G_big_plus l.
Proof.
 induction l; simpl; try rewrite IHl; lca.
Qed.

Lemma Gbigmult_app (l l':list C) :
 G_big_mult (l++l') = G_big_mult l * G_big_mult l'.
Proof.
 induction l; simpl; try rewrite IHl; lca.
Qed.

Lemma Gbigplus_flatmap_seq (F : nat -> list C) n :
  G_big_plus (flat_map F (seq 0 n)) =
  Σ (fun i : nat => G_big_plus (F i)) n.
Proof.
 induction n; trivial.
 rewrite seq_S, flat_map_app. simpl. rewrite app_nil_r, <- IHn.
 now rewrite <- big_plus_app.
Qed.

Lemma bigsum_ext {G} {H : Monoid G} (f g : nat -> G) n :
 (forall x, (x < n)%nat -> f x = g x) -> big_sum f n = big_sum g n.
Proof.
 induction n; simpl; intros; f_equal; auto.
Qed.

Definition Π (f : nat -> C) n := G_big_mult (List.map f (seq 0 n)).


(** Extensions about permutation and determinant *)

Definition sum_perms n (F : (nat -> nat) -> C) : C :=
  G_big_plus (List.map F (qperms n)).

Definition sum_lperms n (F : list nat -> C) : C :=
  G_big_plus (List.map F (lperms n)).

Lemma sum_perms_alt n (F : (nat -> nat) -> C) :
  sum_perms n F = sum_lperms n (compose F perm2fun).
Proof.
 unfold sum_perms, sum_lperms, qperms. f_equal. apply map_map.
Qed.

Lemma sum_lperms_reorder (F : list nat -> C) n :
 sum_lperms (S n) F =
 Σ (fun i => sum_lperms n (compose F (extend_lperm i))) (S n).
Proof.
unfold sum_lperms at 1.
assert (P := reorder_perms_ok n).
apply Permutation_sym in P.
apply Permutation_map with (f:=F) in P.
erewrite Gbigplus_permut; eauto.
unfold reorder_lperms. rewrite map_flatmap, Gbigplus_flatmap_seq.
apply bigsum_ext. intros x _. unfold sum_lperms. now rewrite map_map.
Qed.

Local Coercion IZR : Z >-> R.

Lemma parity_z n : parity n = zparity n.
Proof.
 unfold zparity.
 induction n as [ [| [|n] ] IH] using lt_wf_ind; simpl; try lca.
 apply IH; lia.
Qed.

Lemma reduce_extend n l x (A:Square (S n)) :
 lpermutation n l -> (x <= n)%nat ->
 A x O * Π (fun i => reduce A x 0 i (perm2fun l i)) n =
 Π (fun i => A i (perm2fun (extend_lperm x l) i)) (S n).
Proof.
 intros Hl Hx.
 assert (length l = n).
 { apply Permutation_length in Hl. rewrite seq_length in Hl. lia. }
 unfold Π.
 replace (A x O) with (G_big_mult [A x O]) by lca.
 rewrite <- Gbigmult_app.
 apply Gbigmult_permut. simpl app.
 replace n with (x+(n-x))%nat by lia.
 rewrite <- Nat.add_succ_r.
 rewrite !seq_app, !map_app.
 eapply perm_trans; [apply Permutation_middle; auto| ].
 apply Permutation_app; apply eq_Permutation.
 - apply map_ext_in. intros a Ha. apply in_seq in Ha.
   unfold reduce, extend_lperm.
   case Nat.ltb_spec; try lia; intros _.
   case Nat.ltb_spec; try lia; intros _.
   f_equal. unfold perm2fun. rewrite nth_insert.
   2: rewrite map_length; lia.
   case Nat.compare_spec; intros; try lia.
   rewrite (nth_indep (map S l) O (S O)).
   rewrite map_nth; lia. rewrite map_length; lia.
 - simpl. f_equal.
   + f_equal. unfold extend_lperm, perm2fun.
     rewrite nth_insert. now rewrite Nat.compare_refl.
     rewrite map_length; lia.
   + rewrite <- seq_shift. rewrite map_map.
     apply map_ext_in. intros a Ha. apply in_seq in Ha.
     unfold reduce, extend_lperm.
     case Nat.ltb_spec; try lia; intros _.
     case Nat.ltb_spec; try lia; intros _.
     f_equal. unfold perm2fun. rewrite nth_insert.
     2: rewrite map_length; lia.
     case Nat.compare_spec; intros; try lia.
     simpl. rewrite Nat.sub_0_r.
     rewrite (nth_indep (map S l) O (S O)).
     rewrite map_nth; lia. rewrite map_length; lia.
Qed.

Lemma LeibnizFormula n (A:Square n) :
 Determinant A =
  sum_perms n (fun f => zsign n f * Π (fun i => A i (f i)) n).
Proof.
 revert A. induction n as [|[|n] IH]; intros A.
 - simpl. unfold sum_perms, qperms, Π. simpl.
   rewrite zsign_0. ring.
 - simpl. unfold sum_perms, qperms, Π. simpl.
   rewrite zsign_1. unfold perm2fun. simpl. ring.
 - rewrite Det_simplify.
   remember (S n) as m.
   rewrite sum_perms_alt, sum_lperms_reorder.
   apply bigsum_ext. intros x Hx.
   rewrite IH, sum_perms_alt.
   unfold sum_lperms. rewrite <- Gbigplus_factor. f_equal.
   rewrite map_map. apply map_ext_in. intros l Hl.
   rewrite lperms_ok in Hl. unfold compose.
   rewrite <- reduce_extend by (auto; lia).
   rewrite zsign_extend by (auto; lia). rewrite parity_z.
   rewrite mult_IZR, RtoC_mult. lca.
Qed.

Lemma Determinant_transpose n (A:Square n) :
 Determinant (Matrix.transpose A) = Determinant A.
Proof.
 rewrite !LeibnizFormula. unfold Matrix.transpose.
 rewrite !sum_perms_alt; unfold sum_lperms.
 assert (P := lperms_inv_permut n).
 set (F := compose _ _).
 apply Permutation_map with (f:=F) in P.
 apply Gbigplus_permut in P. rewrite P; clear P.
 rewrite map_map. unfold F; clear F.
 f_equal. apply map_ext_in. intros l Hl. rewrite lperms_ok in Hl.
 assert (Hl' : length l = n).
 { apply Permutation_length in Hl. now rewrite seq_length in Hl. }
 unfold compose.
 rewrite zsign_ext with (f' := qinv n (perm2fun l)); auto using linv_qinv.
 rewrite zsign_qinv by now apply l_q_permutation.
 f_equal.
 unfold Π.
 apply Gbigmult_permut.
 set (F := fun i => _).
 assert (Pm := Permutation_map F Hl). apply Permutation_sym in Pm.
 eapply perm_trans; [apply Pm| ]. clear Pm.
 apply eq_Permutation.
 rewrite <- (perm2list_perm2fun n l) at 1; auto. unfold perm2list.
 rewrite map_map. apply map_ext_in. intros a Ha. rewrite in_seq in Ha.
 unfold F. f_equal.
 unfold linv. rewrite perm2fun_perm2list.
 2:{ apply l_q_permutation in Hl. apply q_f_permutation in Hl.
     now apply Hl. }
 unfold lqinv, perm2fun. apply index_nth; try lia.
 apply Permutation_sym in Hl. eapply Permutation_NoDup; eauto using seq_NoDup.
Qed.

Lemma Determinant_row_add {n} (A : Square n) (i j : nat) (c : C) :
  (i < n)%nat -> (j < n)%nat -> i <> j ->
  Determinant (row_add A i j c) = Determinant A.
Proof.
 intros Hi Hj D.
 rewrite <- (transpose_involutive _ _ A) at 1.
 rewrite <- col_add_transpose, Determinant_transpose.
 rewrite Determinant_col_add; auto.
 apply Determinant_transpose.
Qed.

(** Auxiliary matrix manipulations : addrows and cols_scale *)

(** addrows changes the row [M_i] into [M_i - c*M_{i-1}] *)

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
 rewrite IHl by lia. rewrite Determinant_scale by lia. lca.
Qed.

(** Determinant and matrix equality *)

Lemma reduce_compat {n} (A B : Square (S n)) : A == B ->
 forall x y, reduce A x y == reduce B x y.
Proof.
 intros E x y i j Hi Hj. unfold reduce.
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
   + apply IH. now apply reduce_compat.
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
   assert (reduce W 0 0 ==
           cols_scale 0 (map (fun y => y-x) l) (Vandermonde n' l)).
   { intros i j Hi Hj.
     rewrite cols_scale_alt by trivial.
     unfold W, reduce. simpl. rewrite addrows_specS by trivial.
     unfold V, Vandermonde. simpl.
     repeat (case Nat.ltb_spec; intros; try lia). simpl.
     set (subx := fun y => _).
     rewrite nth_indep with (d:=C1) (d':=subx 0) by (rewrite map_length; lia).
     rewrite map_nth. unfold subx. lca. }
   rewrite H.
   rewrite cols_scale_det by (rewrite map_length; lia).
   rewrite IH by trivial. lca.
Qed.
