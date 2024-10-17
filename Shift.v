Require Import MoreFun DeltaList GenFib GenG GenAdd.
Import ListNotations.
Set Implicit Arguments.

(* Almost inverse of fq : shift, i.e. map S on the decomposition *)

Definition shift q n := sumA q (map S (decomp q n)).

(* We've already seen this function, under the name [rchild],
   defined as [n + fq^q n] *)

Lemma shift_rchild q n : shift q n = rchild q n.
Proof.
 symmetry. apply rchild_decomp.
Qed.

Lemma shift_sum q l :
 Delta q l -> shift q (sumA q l) = sumA q (map S l).
Proof.
 intros D.
 rewrite <- renorm_sum. unfold shift.
 rewrite decomp_sum' by now apply renorm_delta.
 rewrite renorm_mapS. apply renorm_sum.
Qed.

Lemma f_shift q n : f q (shift q n) = n.
Proof.
 unfold shift. rewrite f_sumA.
 rewrite map_map. simpl. rewrite map_id. apply decomp_sum.
 apply Delta_map with (S q).
 - intros. lia.
 - apply decomp_delta.
Qed.

Lemma fs_shifts q p n : fs q p ((shift q ^^p) n) = n.
Proof.
 revert n. induction p; intros n; auto.
 rewrite (iter_S (shift q)). simpl. now rewrite IHp, f_shift.
Qed.

Lemma shift_f_rankpos q n :
  rank q n <> Some 0 -> shift q (f q n) = n.
Proof.
 unfold rank. intros Hrank.
 assert (E := decomp_sum q n).
 assert (D := decomp_delta q n).
 assert (NZ : ~In 0 (decomp q n)).
 { destruct (decomp q n) as [|a l]; auto.
   apply Delta_nz with (S q); auto. destruct a; intuith. }
 clear Hrank.
 rewrite <- E. rewrite f_sumA; auto.
 rewrite shift_sum by auto using Delta_pred with hof.
 apply f_equal. rewrite map_map.
 rewrite <- (map_id (decomp q n)) at 2.
 apply map_ext_in. intros [|a] Ha; intuition.
Qed.

Lemma shift_f_rank0 q n :
  rank q n = Some 0 -> shift q (f q n) = S n.
Proof.
 unfold rank. intros Hrank.
 assert (E := decomp_sum q n).
 assert (D := decomp_delta q n).
 destruct (decomp q n) as [|a l]; try easy.
 injection Hrank as ->.
 assert (~In 0 l).
 { eapply Delta_nz'. 2:eauto. auto with arith. }
 subst n. rewrite f_sumA; auto.
 rewrite shift_sum.
 2:{ change (Delta q (map pred (1::l))).
     apply Delta_pred; auto using Delta_S_cons. simpl. intuition lia. }
 simpl. f_equal. f_equal. f_equal.
 rewrite map_map.
 rewrite <- (map_id l) at 2.
 apply map_ext_in. intros [|a] Ha; intuition.
Qed.

(* Equation about shift iterations *)

Lemma shift_iter q n :
  ((shift q)^^(S q)) n = ((shift q)^^q) n + n.
Proof.
 simpl. rewrite shift_rchild at 1. unfold rchild. f_equal. apply fs_shifts.
Qed.

(* shift is injective *)

Lemma shift_injective q n m : shift q n = shift q m -> n = m.
Proof.
 intros.
 rewrite <- (f_shift q n), <- (f_shift q m). now f_equal.
Qed.

(* shift grows by +1 or +2 steps *)

Lemma shift_steps q n :
  shift q (S n) = S (shift q n) \/ shift q (S n) = S (S (shift q n)).
Proof.
 unfold shift. rewrite decomp_S.
 assert (D := decomp_delta q n).
 destruct (decomp q n) as [|a l].
 - simpl; now right.
 - simpl map. case Nat.leb_spec; intros; [|simpl; now right].
   rewrite !renormS_alt, renorm_mapS, renorm_sum by trivial.
   simpl map. rewrite !sumA_cons, <- !Nat.add_succ_l.
   destruct (Nat.eqb_spec a q).
   + right. f_equal. subst a.
     rewrite A_S. replace (S q -q) with 1 by lia.
     rewrite A_q_1. lia.
   + left. f_equal. rewrite !A_base; lia.
Qed.

(* TODO: quasi-additivity of shift ?
   Probably similar to the quasi-additivity of f
*)
