Require Import MoreFun DeltaList GenFib GenG GenAdd.
Import ListNotations.
Set Implicit Arguments.

(* Almost inverse of fk : shift, i.e. map S on the decomposition *)

Definition shift k n := sumA k (map S (decomp k n)).

(* We've already seen this function, under the name [rchild],
   defined as [n + fk^(k-1) n] *)

Lemma shift_rchild k n : shift k n = rchild k n.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - unfold shift, rchild. simpl.
   now rewrite decomp_0, sumA0, <- rchild_decomp.
 - symmetry. now apply rchild_decomp.
Qed.

Lemma shift_0 n : shift 0 n = n+n.
Proof.
 now rewrite shift_rchild.
Qed.

Lemma shift_sum k l :
 k<>0 -> Delta (k-1) l -> shift k (sumA k l) = sumA k (map S l).
Proof.
 intros K D.
 rewrite <- renorm_sum. unfold shift.
 rewrite decomp_sum'; trivial. 2:now apply renorm_delta.
 rewrite renorm_mapS. apply renorm_sum.
Qed.

Lemma f_shift k n : k<>0 -> f k (shift k n) = n.
Proof.
 intros K. unfold shift. rewrite f_sumA; trivial.
 rewrite map_map. simpl. rewrite map_id. apply decomp_sum.
 apply Delta_map with k.
 - intros. lia.
 - apply decomp_delta.
Qed.

Lemma fs_shifts k p n : k<>0 -> fs k p ((shift k ^^p) n) = n.
Proof.
 intros K. revert n. induction p; intros n; auto.
 rewrite (iter_S (shift k)). simpl. now rewrite IHp, f_shift.
Qed.

Lemma shift_f_rankpos k n :
  k<>0 -> rank k n <> Some 0 -> shift k (f k n) = n.
Proof.
 unfold rank. intros K Hrank.
 assert (E := decomp_sum k n).
 assert (D := decomp_delta k n).
 assert (NZ : ~In 0 (decomp k n)).
 { destruct (decomp k n) as [|a l]; auto.
   apply Delta_nz with k; auto. destruct a; intuith. }
 clear Hrank.
 rewrite <- E. rewrite f_sumA; auto.
 rewrite shift_sum; trivial.
 2:{ apply Delta_pred; trivial. apply Delta_S; now fixpred. }
 apply f_equal. rewrite map_map.
 rewrite <- (map_id (decomp k n)) at 2.
 apply map_ext_in. intros [|a] Ha; intuition.
Qed.

Lemma shift_f_rank0 k n :
  k<>0 -> rank k n = Some 0 -> shift k (f k n) = S n.
Proof.
 unfold rank. intros K Hrank.
 assert (E := decomp_sum k n).
 assert (D := decomp_delta k n).
 destruct (decomp k n) as [|a l]; try easy.
 injection Hrank as ->.
 assert (~In 0 l).
 { eapply Delta_nz'; trivial. 2:eauto. lia. }
 subst n. rewrite f_sumA; auto.
 rewrite shift_sum; trivial.
 2:{ change (Delta (k-1) (map pred (1::l))).
     apply Delta_pred. simpl; intuition lia.
     apply Delta_S_cons; now fixpred. }
 simpl. f_equal. f_equal. f_equal.
 rewrite map_map.
 rewrite <- (map_id l) at 2.
 apply map_ext_in. intros [|a] Ha; intuition.
Qed.

(* Equation about shift iterations *)

Lemma shift_iter k n :
  k<>0 -> ((shift k)^^k) n = ((shift k)^^(k-1)) n + n.
Proof.
 intros K.
 replace (shift k^^k) with (shift k^^(S (k-1))). 2:{ f_equal;lia. }
 simpl. rewrite shift_rchild at 1. unfold rchild. f_equal.
 now apply fs_shifts.
Qed.

(* shift is injective *)

Lemma shift_injective k n m : shift k n = shift k m -> n = m.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - rewrite !shift_0. lia.
 - intros. rewrite <- (@f_shift k n K), <- (@f_shift k m K). now f_equal.
Qed.

(* shift grows by +1 or +2 steps *)

Lemma shift_steps k n :
  shift k (S n) = S (shift k n) \/ shift k (S n) = S (S (shift k n)).
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { rewrite !shift_0. lia. }
 unfold shift. rewrite decomp_S by trivial.
 assert (D := decomp_delta k n).
 destruct (decomp k n) as [|a l].
 - simpl; now right.
 - simpl map. case Nat.ltb_spec; intros; [|simpl; now right].
   rewrite !renormS_alt, renorm_mapS, renorm_sum by trivial.
   simpl map. rewrite !sumA_cons, <- !Nat.add_succ_l.
   destruct (Nat.eqb_spec a (k-1)).
   + right. f_equal. subst a.
     rewrite A_S. fixpred. replace (k -(k-1)) with 1 by lia.
     rewrite A_k_1. lia.
   + left. f_equal. rewrite !A_base; lia.
Qed.

(* TODO: quasi-additivity of shift ?
   Probably similar to the quasi-additivity of f
*)
