From QuantumLib Require Import Complex Matrix VecSet.
Require Import MoreList MoreMatrix MorePermut.
Local Open Scope C.

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

Definition Π (f : nat -> C) n := G_big_mult (take n f).

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

Lemma get_minor_extend n l x (A:Square (S n)) :
 lpermutation n l -> (x <= n)%nat ->
 A x O * Π (fun i => get_minor A x 0 i (perm2fun l i)) n =
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
 rewrite <- Nat.add_succ_r. unfold take.
 rewrite !seq_app, !map_app.
 eapply perm_trans; [apply Permutation_middle; auto| ].
 apply Permutation_app; apply eq_Permutation.
 - apply map_ext_in. intros a Ha. apply in_seq in Ha.
   unfold get_minor, extend_lperm.
   case Nat.ltb_spec; try lia; intros _.
   case Nat.ltb_spec; try lia; intros _.
   f_equal. unfold perm2fun. rewrite nth_insert.
   2: rewrite map_length; lia.
   case Nat.compare_spec; intros; try lia.
   rewrite nth_map_indep with (d':=O); lia.
 - simpl. f_equal.
   + f_equal. unfold extend_lperm, perm2fun.
     rewrite nth_insert. now rewrite Nat.compare_refl.
     rewrite map_length; lia.
   + rewrite <- seq_shift. rewrite map_map.
     apply map_ext_in. intros a Ha. apply in_seq in Ha.
     unfold get_minor, extend_lperm.
     case Nat.ltb_spec; try lia; intros _.
     case Nat.ltb_spec; try lia; intros _.
     f_equal. unfold perm2fun. rewrite nth_insert.
     2: rewrite map_length; lia.
     case Nat.compare_spec; intros; try lia.
     simpl. rewrite Nat.sub_0_r.
     rewrite nth_map_indep with (d':=O); lia.
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
   rewrite <- get_minor_extend by (auto; lia).
   rewrite zsign_extend by (auto; lia). rewrite parity_z.
   rewrite mult_IZR, RtoC_mult. lca.
Qed.
