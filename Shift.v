Require Import Arith Lia List Bool.
Require Import DeltaList FunG GenFib GenG GenAdd.
Import ListNotations.
Set Implicit Arguments.

(* Almost inverse of fk : shift, i.e. map S on the decomposition *)

Definition shift k n := sumA k (map S (decomp k n)).

(* We've already seen this function, under the name [rchild],
   defined as [n + fk^k n] *)

Lemma shift_rchild k n : shift k n = rchild k n.
Proof.
 symmetry. apply rchild_decomp.
Qed.

Lemma shift_sum k l :
 Delta k l -> shift k (sumA k l) = sumA k (map S l).
Proof.
 intros D.
 rewrite <- renorm_sum. unfold shift.
 rewrite decomp_sum' by now apply renorm_delta.
 rewrite renorm_mapS. apply renorm_sum.
Qed.

Lemma f_shift k n : f k (shift k n) = n.
Proof.
 unfold shift. rewrite f_sumA.
 rewrite map_map. simpl. rewrite map_id. apply decomp_sum.
 apply Delta_map with (S k).
 - intros. lia.
 - apply decomp_delta.
Qed.

Lemma fs_shifts k p n : ((f k)^^p) (((shift k)^^p) n) = n.
Proof.
 revert n. induction p; intros n; auto.
 rewrite (iter_S (shift k)). simpl. now rewrite IHp, f_shift.
Qed.

Lemma shift_f_rankpos k n :
  rank k n <> Some 0 -> shift k (f k n) = n.
Proof.
 unfold rank. intros Hrank.
 assert (E := decomp_sum k n).
 assert (D := decomp_delta k n).
 assert (NZ : ~In 0 (decomp k n)).
 { destruct (decomp k n) as [|a l]; auto.
   apply Delta_nz with (S k); auto. destruct a; intuition. }
 clear Hrank.
 rewrite <- E. rewrite f_sumA; auto.
 rewrite shift_sum by auto using Delta_pred.
 apply f_equal. rewrite map_map.
 rewrite <- (map_id (decomp k n)) at 2.
 apply map_ext_in. intros [|a] Ha; intuition.
Qed.

Lemma shift_f_rank0 k n :
  rank k n = Some 0 -> shift k (f k n) = S n.
Proof.
 unfold rank. intros Hrank.
 assert (E := decomp_sum k n).
 assert (D := decomp_delta k n).
 destruct (decomp k n) as [|a l]; try easy.
 injection Hrank as ->.
 assert (~In 0 l).
 { eapply Delta_nz'. 2:eauto. auto with arith. }
 subst n. rewrite f_sumA; auto.
 rewrite shift_sum.
 2:{ change (Delta k (map pred (1::l))).
     apply Delta_pred; auto using Delta_S_cons. simpl. intuition lia. }
 simpl. f_equal. f_equal. f_equal.
 rewrite map_map.
 rewrite <- (map_id l) at 2.
 apply map_ext_in. intros [|a] Ha; intuition.
Qed.

(* Equation about shift iterations *)

Lemma shift_iter k n :
  ((shift k)^^(S k)) n = ((shift k)^^k) n + n.
Proof.
 simpl. rewrite shift_rchild at 1. unfold rchild. f_equal. apply fs_shifts.
Qed.

(* shift is injective *)

Lemma shift_injective k n m : shift k n = shift k m -> n = m.
Proof.
 intros.
 rewrite <- (f_shift k n), <- (f_shift k m). now f_equal.
Qed.

(* shift grows by +1 or +2 steps *)

Lemma shift_steps k n :
  shift k (S n) = S (shift k n) \/ shift k (S n) = S (S (shift k n)).
Proof.
 unfold shift. rewrite decomp_S.
 assert (D := decomp_delta k n).
 destruct (decomp k n) as [|a l].
 - simpl; now right.
 - simpl map. case Nat.leb_spec; intros; [|simpl; now right].
   rewrite renorm_mapS, renorm_sum.
   simpl map. rewrite !sumA_cons, <- !Nat.add_succ_l.
   destruct (Nat.eqb_spec a k).
   + right. f_equal. subst a.
     rewrite A_S. replace (S k -k) with 1 by lia.
     rewrite A_k_1. lia.
   + left. f_equal. rewrite !A_base; lia.
Qed.

(* TODO: quasi-additivity of shift ?
   Probably similar to the quasi-additivity of f
*)
