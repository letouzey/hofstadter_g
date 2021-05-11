Require Import Arith Lia List Bool.
Require Import DeltaList GenFib GenG GenAdd.
Import ListNotations.
Set Implicit Arguments.

(** Addendum to GenG :
    Could we have [f k (sumA k l) = sumA k (map pred l)]
    when l is less than Delta k ?
*)

(* A delta of (k-1) is enough between two large-enough A-numbers *)
Lemma f_AA k n p : k<>0 -> k<n -> n+k-1<=p ->
 f k (A k n + A k p) = A k (n-1) + A k (p-1).
Proof.
 intros.
 rewrite A_sum by lia.
 rewrite (Nat.add_comm (A k (n-1))).
 replace (f k _) with (f k (sumA k [n-S k; n-1; p])).
 2:{ f_equal. simpl. lia. }
 rewrite f_sumA_lax; auto.
 - simpl.
   rewrite <- !Nat.sub_1_r.
   rewrite Nat.add_0_r, Nat.add_assoc. f_equal.
   replace (n-S k -1) with (n-1-S k) by lia. symmetry.
   rewrite Nat.add_comm. apply A_sum. lia.
 - constructor. lia. constructor. lia. auto.
Qed.


(******* k=0 *******)

(* k = 0
   strict = Delta 1
   pas de lax (precondition thm f_lax)
   Quid de Delta 0 ? *)

(* Counter-examples *)
Compute (f 0 (A 0 0 + A 0 0), A 0 0 + A 0 0).
Compute (f 0 (A 0 0 + A 0 0 + A 0 0), A 0 0 + A 0 0 + A 0 0).

Lemma sumA_0_even l : ~In 0 l -> sumA 0 l = 2 * sumA 0 (map pred l).
Proof.
 induction l; trivial.
 intros H. simpl in H. simpl sumA.
 rewrite Nat.mul_add_distr_l.
 rewrite <- IHl by intuition. f_equal.
 destruct a. intuition.
 now rewrite !A_0_pow2.
Qed.

(* Any 0-decomp without 1 = A0 0 satisfies the equation *)

Lemma f0_nozero l : ~In 0 l -> f 0 (sumA 0 l) = sumA 0 (map pred l).
Proof.
 intros H.
 rewrite !f_0_div2. rewrite sumA_0_even; auto.
 now rewrite <- Nat.div2_div, Nat.div2_succ_double.
Qed.

(* Actually, A0 0 can be tolerated, but only once. *)

Lemma f0_maybe_one_zero l : ~In 0 (tail l) ->
 f 0 (sumA 0 l) = sumA 0 (map pred l).
Proof.
 destruct l as [|[|n] l]; trivial.
 - simpl. intros. rewrite <- f0_nozero by trivial.
   rewrite !f_0_div2, <-!Nat.div2_div. simpl Nat.div2 at 1.
   f_equal. rewrite sumA_0_even; auto.
   now rewrite Nat.div2_succ_double, Nat.div2_double.
 - intros H. simpl in H.
   apply f0_nozero. simpl. intuition.
Qed.


(******* k=1 *******)

(* k = 1
   strict = Delta 2
   lax = Delta 1
   Quid de Delta 0 *)

(* contre-exemples: *)
Compute (f 1 (A 1 0 + A 1 0), A 1 0 + A 1 0).
Compute (f 1 (A 1 1 + A 1 1), A 1 0 + A 1 0).
Compute (f 1 (5*A 1 3), 5*A 1 2).


Definition tests := seq 0 20.
Compute
  filter (fun '(n,u,v) => negb (u =? v))
   (map (fun n => (n,fopt 1 (12 * A 1 n), 12*A 1 (n-1))) (seq 0 10)).

(* Apparemment f1 (A1 n + A1 n) = A1 (n-1) + A(n-1) dès que n>=2 *)
(*             f1 (5*A1 n) = 5*A1 (n-1) dès que n>=4 *)
(*             f1 (12*A1 n) = 12*A1 (n-1) dès que n>=6 *)

Compute decomp 1 (2 * A 1 0).  (* [1] *)
Compute decomp 1 (2 * A 1 1).  (* [0;2] *)
Compute decomp 1 (2 * A 1 2).  (* [0;3] *)
Compute decomp 1 (2 * A 1 3).  (* [1;4]=map S [0;3], donc stable *)

Lemma A1_times2 n : 2 * A 1 (2+n) = sumA 1 [n;3+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma A1_times2' n : 1<=n -> 2 * A 1 n = sumA 1 [n-2;n+1].
Proof.
 rewrite Nat.lt_eq_cases.
 intros [H|<-]; trivial.
 replace n with (2+(n-2)) by lia. rewrite A1_times2.
 repeat (f_equal; try lia).
Qed.

Lemma f1_twiceA n : 2<=n -> f 1 (2 * A 1 n) = 2 * A 1 (n-1).
Proof.
 intros H. rewrite !A1_times2' by lia.
 rewrite f_sumA. f_equal; simpl. repeat (f_equal; try lia).
 repeat (constructor; try lia).
Qed.

Compute decomp 1 (3 * A 1 0).  (* [2] *)
Compute decomp 1 (3 * A 1 1).  (* [0;3] *)
Compute decomp 1 (3 * A 1 2).  (* [0;4] *)
Compute decomp 1 (3 * A 1 3).  (* [1;5]=map S [0;4], donc stable *)

Lemma A1_times3 n : 3 * A 1 (2+n) = sumA 1 [n;4+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma A1_times3' n : 1<=n -> 3 * A 1 n = sumA 1 [n-2;n+2].
Proof.
 rewrite Nat.lt_eq_cases.
 intros [H|<-]; trivial.
 replace n with (2+(n-2)) by lia. rewrite A1_times3.
 repeat (f_equal; try lia).
Qed.

Lemma f1_tripleA n : 2<=n -> f 1 (3 * A 1 n) = 3 * A 1 (n-1).
Proof.
 intros H. rewrite !A1_times3' by lia.
 rewrite f_sumA. f_equal; simpl. repeat (f_equal; try lia).
 repeat (constructor; try lia).
Qed.

Compute decomp 1 (4 * A 1 0).  (* [0;2] *)
Compute decomp 1 (4 * A 1 1).  (* [4] *)
Compute decomp 1 (4 * A 1 2).  (* [0;2;4] *)
Compute decomp 1 (4 * A 1 3).  (* [1;3;5]=map S [0;2;4], donc stable *)

Lemma A1_times4 n : 4 * A 1 (2+n) = sumA 1 [n;2+n;4+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma A1_times4' n : 1<=n -> 4 * A 1 n = sumA 1 [n-2;n;n+2].
Proof.
 rewrite Nat.lt_eq_cases.
 intros [H|<-]; trivial.
 replace n with (2+(n-2)) by lia. rewrite A1_times4.
 repeat (f_equal; try lia).
Qed.

Lemma f1_times4 n : 2 <= n -> f 1 (4 * A 1 n) = 4 * A 1 (n-1).
Proof.
 intros H. rewrite !A1_times4' by lia.
 rewrite f_sumA. f_equal; simpl. repeat (f_equal; try lia).
 repeat (constructor; try lia).
Qed.

Compute decomp 1 (5 * A 1 0).  (* [3] *)
Compute decomp 1 (5 * A 1 1).  (* [1;4] *)
Compute decomp 1 (5 * A 1 2).  (* [1;5] *)
Compute decomp 1 (5 * A 1 3).  (* [0;2;6] *)
Compute decomp 1 (5 * A 1 4).  (* [0;3;7] OK car: *)
Compute decomp 1 (5 * A 1 5).  (* [1;4;8] = map S [0;3;7] *)

Lemma A1_times5 n : 5 * A 1 (4+n) = sumA 1 [n;3+n;7+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma A1_times5' n : 3<=n -> 5 * A 1 n = sumA 1 [n-4;n-1;n+3].
Proof.
 rewrite Nat.lt_eq_cases.
 intros [H|<-]; trivial.
 replace n with (4+(n-4)) by lia. rewrite A1_times5.
 repeat (f_equal; try lia).
Qed.

Lemma f1_times5 n : 4<=n -> f 1 (5 * A 1 n) = 5 * A 1 (n-1).
Proof.
 intros H. rewrite !A1_times5' by lia.
 rewrite f_sumA. f_equal; simpl. repeat (f_equal; try lia).
 repeat (constructor; try lia).
Qed.

Compute decomp 1 (6 * A 1 0).  (* [0;3] *)
Compute decomp 1 (6 * A 1 1).  (* [0;2;4] *)
Compute decomp 1 (6 * A 1 2).  (* [3;5] *)
Compute decomp 1 (6 * A 1 3).  (* [0;4;6] *)
Compute decomp 1 (6 * A 1 4).  (* [0;5;7] OK car: *)
Compute decomp 1 (6 * A 1 5).  (* [1;6;8] = map S [0;5;7] *)

Lemma A1_times6 n : 6 * A 1 (4+n) = sumA 1 [n;5+n;7+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma A1_times6' n : 3<=n -> 6 * A 1 n = sumA 1 [n-4;n+1;n+3].
Proof.
 rewrite Nat.lt_eq_cases.
 intros [H|<-]; trivial.
 replace n with (4+(n-4)) by lia. rewrite A1_times6.
 repeat (f_equal; try lia).
Qed.

Lemma f1_times6 n : 4<=n -> f 1 (6 * A 1 n) = 6 * A 1 (n-1).
Proof.
 intros H. rewrite !A1_times6' by lia.
 rewrite f_sumA. f_equal; simpl. repeat (f_equal; try lia).
 repeat (constructor; try lia).
Qed.

Compute decomp 1 (7 * A 1 0).  (* [1;3] *)
Compute decomp 1 (7 * A 1 1).  (* [0;5] *)
Compute decomp 1 (7 * A 1 2).  (* [6] *)
Compute decomp 1 (7 * A 1 3).  (* [0;7] *)
Compute decomp 1 (7 * A 1 4).  (* [0;8] OK car: *)
Compute decomp 1 (7 * A 1 5).  (* [1;9] = map S [0;8] *)

Lemma A1_times7 n : 7 * A 1 (4+n) = sumA 1 [n;8+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma A1_times7' n : 3<=n -> 7 * A 1 n = sumA 1 [n-4;n+4].
Proof.
 rewrite Nat.lt_eq_cases.
 intros [H|<-]; trivial.
 replace n with (4+(n-4)) by lia. rewrite A1_times7.
 repeat (f_equal; try lia).
Qed.

Lemma f1_times7 n : 4<=n -> f 1 (7 * A 1 n) = 7 * A 1 (n-1).
Proof.
 intros H. rewrite !A1_times7' by lia.
 rewrite f_sumA. f_equal; simpl. repeat (f_equal; try lia).
 repeat (constructor; try lia).
Qed.

Compute decomp 1 (12 * A 1 0).  (* [0;2;4] *)
Compute decomp 1 (12 * A 1 1).  (* [2;6] *)
Compute decomp 1 (12 * A 1 2).  (* [1;7] *)
Compute decomp 1 (12 * A 1 3).  (* [3;8] *)
Compute decomp 1 (12 * A 1 4).  (* [1;3;9] *)
Compute decomp 1 (12 * A 1 5).  (* [0;2;4;10] *)
Compute decomp 1 (12 * A 1 6).  (* [0;3;5;11] OK car: *)
Compute decomp 1 (12 * A 1 7).  (* [1;4;6;12] = map S ... *)


(* Conjecture : forall p, exists N, forall n, N<=n
   f 1 (p * A 1 n) = p * A 1 (n-1) *)

(* Conjecture : prendre N=p convient (mais moins est possible) *)

Compute decomp 1 (2 * A 1 2). (* [0;3] *)
Compute decomp 1 (3 * A 1 3). (* [1;5] donc décalage -1: 3*A1 2 = [0;4] *)
Compute decomp 1 (4 * A 1 4). (* [2;4;6] donc décalage -2: 4*A1 2 = [0;2;4] *)
Compute decomp 1 (5 * A 1 5). (* [1;4;8] donc décalage -1: 5*A1 4 = [0;3;7] *)
Compute decomp 1 (6 * A 1 6). (* [2;7;9] donc décalage -2: 6*A1 4 = [0;5;7] *)
Compute decomp 1 (7 * A 1 7). (* [3;11] donc décalage -3: 7*A1 4 = [0;8] *)
Compute decomp 1 (8 * A 1 8). (* [4;8;12] donc décalage -4: 8*A1 4 = [0;4;8] *)
Compute decomp 1 (9 * A 1 9). (* [5;7;10;13] donc décalage -5: 9*A1 4 = [0;2;5;8] *)
Compute decomp 1 (10 * A 1 10). (* [6;8;12;14] donc décalage -6 *)
Compute decomp 1 (11 * A 1 11). (* [7;9;11;13;15] donc décalage -7 *)
Compute decomp 1 (12 * A 1 12). (* [6;9;11;17] donc décalage -6 *)
Compute decomp 1 (13 * A 1 13). (* [7;10;14;18] donc décalage -7 *)


(* Particular case : k=1 and equal A-numbers *)

Lemma f1_AA n : 1<n -> f 1 (2 * A 1 n) = 2 * A 1 (n-1).
Proof.
 intros. simpl. rewrite !Nat.add_0_r. apply f_AA; lia.
Qed.


(******* k=2 *******)

Definition A2 := A 2.

(* pour k = 2:
   strict = Delta 3
   lax = Delta 2

   Mais on n'a pas Delta 0 ni Delta 1: *)

Compute (h (A2 0 + A2 0), A2 0 + A2 0).
Compute (h (A2 1 + A2 2), A2 0 + A2 1).

(* Pour deux A-nombres consécutifs, ce sont les seuls à problème,
   cf f_AA + verification manuelle pour n=0 et n=2
*)

Lemma f2_AA n : n<>1 -> h (A2 n + A2 (S n)) = A2 (n-1) + A2 n.
Proof.
 destruct (Nat.eq_dec n 0).
 - subst; trivial.
 - destruct (Nat.eq_dec n 2).
   + subst; trivial.
   + intro H. unfold h,A2. rewrite f_AA; try lia. f_equal. f_equal. lia.
Qed.

(* Deux nombres égaux: *)

Compute decomp 2 (2 * A2 2). (* [4] *)
Compute decomp 2 (2 * A2 3). (* [1;4] *)
Compute decomp 2 (2 * A2 4). (* [2;5] *)
Compute decomp 2 (2 * A2 5). (* [0;3;6] *)
Compute decomp 2 (2 * A2 6). (* [0;4;7] *)
Compute decomp 2 (2 * A2 7). (* [0;5;8] OK *)
Compute decomp 2 (2 * A2 8). (* [1;6;9] *)
Compute decomp 2 (2 * A2 9). (* [2;7;10] *)
(*

          2
       *.**
      ***.*
      **...*
   *.*.*...*
   *....*..*
*)

Lemma A2_times2 n : 2 * A2 (7+n) = sumA 2 [n;5+n;8+n].
Proof.
 unfold A2. simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma A2_times2' n : 5<=n -> 2 * A2 n = sumA 2 [n-7;n-2;n+1].
Proof.
 rewrite Nat.lt_eq_cases.
 intros [H|<-]; trivial.
 red in H. rewrite Nat.lt_eq_cases in H. destruct H as [H|<-]; trivial.
 replace n with (7+(n-7)) at 1 by lia.
 rewrite A2_times2. f_equal. repeat (f_equal; try lia).
Qed.

Lemma f2_times2 n : 6<=n -> h (2 * A2 n) = 2 * A2 (n-1).
Proof.
 intros H. rewrite !A2_times2' by lia.
 unfold h. rewrite f_sumA. f_equal; simpl. repeat (f_equal; try lia).
 repeat (constructor; try lia).
Qed.

(* 3 nombres egaux *)

Compute decomp 2 (3 * A2 3). (* [2;5] *)
Compute decomp 2 (3 * A2 4). (* [0;3;6] *)
Compute decomp 2 (3 * A2 5). (* [1;4;7] *)
Compute decomp 2 (3 * A2 6). (* [1;5;8] *)
Compute decomp 2 (3 * A2 7). (* [2;6;9] *)
Compute decomp 2 (3 * A2 8). (* [0;3;7;10] *)
Compute decomp 2 (3 * A2 9). (* [0;4;8;11] *)
Compute decomp 2 (3 * A2 10). (* [0;5;9;12] OK *)
Compute decomp 2 (3 * A2 11). (* [1;6;10;13] *)
Compute decomp 2 (3 * A2 12). (* [2;7;11;14] *)

(*

          3
       *.*2
      ***.2
      **..**
   *.*.2.*.*
   *****....*
   **.*.*...*
*.*.*.*.*...*
*....*...*..*

*)

Lemma A2_times3 n : 3 * A2 (10+n) = sumA 2 [n;5+n;9+n;12+n].
Proof.
 unfold A2. simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma A2_times3' n : 9<=n -> 3 * A2 n = sumA 2 [n-10;n-5;n-1;n+2].
Proof.
 rewrite Nat.lt_eq_cases.
 intros [H|<-]; trivial.
 replace n with (10+(n-10)) at 1 by lia.
 rewrite A2_times3. f_equal. repeat (f_equal; try lia).
Qed.

Lemma f2_times3 n : 10<=n -> h (3 * A 2 n) = 3 * A2 (n-1).
Proof.
 intros H. rewrite !A2_times3' by lia.
 unfold h. rewrite f_sumA. f_equal; simpl. repeat (f_equal; try lia).
 repeat (constructor; try lia).
Qed.

(* triplets consecutifs : tout va bien, zero exceptions *)
(* *** = .*.* *)

Lemma A2_seq3 n : sumA 2 [n;1+n;2+n] = sumA 2 [1+n;3+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma f2_seq3 n : h (sumA 2 [n;1+n;2+n]) = sumA 2 [n-1;n;1+n].
Proof.
 destruct n; trivial.
 simpl "-". rewrite Nat.sub_0_r, !A2_seq3.
 apply f_sumA_lax; auto. repeat (constructor; try lia).
Qed.

(* quadruplets : OK aussi *)
(* **** = *.*.* = *....*  *)

Lemma A2_seq4 n : sumA 2 [n;1+n;2+n;3+n] = sumA 2 [n;5+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma f2_seq4 n : h (sumA 2 [n;1+n;2+n;3+n]) = sumA 2 [n-1;n;1+n;2+n].
Proof.
 destruct n; trivial.
 simpl "-". rewrite Nat.sub_0_r.
 rewrite !A2_seq4.
 apply f_sumA_lax; auto. repeat (constructor; try lia).
Qed.

(* quintuplets : dès que n>=2 *)

Lemma A2_seq5 n : sumA 2 [3+n;4+n;5+n;6+n;7+n] = sumA 2 [n;5+n;9+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma f2_seq5 n : 2<=n ->
 h (sumA 2 [n;1+n;2+n;3+n;4+n]) = sumA 2 [n-1;n;1+n;2+n;3+n].
Proof.
 unfold h.
 rewrite Nat.lt_eq_cases.
 intros [H|<-].
 2:{ rewrite <- fopt_spec; trivial. }
 red in H; rewrite Nat.lt_eq_cases in H. destruct H as [H|<-].
 2:{ rewrite <- fopt_spec; trivial. }
 replace n with (3+(n-3)) at 1 2 3 4 5 by lia.
 rewrite A2_seq5.
 replace (n-1) with (3+(n-4)) by lia.
 replace n with (4+(n-4)) at 5 6 7 8 by lia.
 rewrite A2_seq5.
 rewrite f_sumA. f_equal. simpl. repeat (f_equal; try lia).
 repeat (constructor; try lia).
Qed.

(* Important equations for later *)

Lemma twice_A2_eqn n : 2 * A2 (5+n) + A2 n = A2 (7+n).
Proof.
 unfold A2; simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma twice_A2_eqn' n : 3<=n -> 2 * A2 n = A2 (n+2) - A2 (n-5).
Proof.
 rewrite Nat.lt_eq_cases; intros [H|<-]; [|trivial].
 red in H. rewrite Nat.lt_eq_cases in H. destruct H as [H|<-]; [|trivial].
 replace n with (5+(n-5)) at 1 by lia.
 replace (n+2) with (7+(n-5)) by lia.
 generalize (twice_A2_eqn (n-5)). lia.
Qed.

Lemma twice_A2_le n : 2 * A2 n <= A2 (2+n).
Proof.
 unfold A2.
 destruct n; simpl; auto.
 replace (n-0) with n by lia.
 generalize (@A_mono 2 (n-2) (n-1)). lia.
Qed.

Lemma seq_A2_eqn n : A2 (3+n) + A2 (4+n) = A2 (5+n) + A2 n.
Proof.
 unfold A2. simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma seq_A2_eqn' n : 1<=n -> A2 n + A2 (S n) = A2 (n+2) + A2 (n-3).
Proof.
 rewrite Nat.lt_eq_cases; intros [H|<-]; [|trivial].
 red in H. rewrite Nat.lt_eq_cases in H. destruct H as [H|<-]; [|trivial].
 replace n with (3+(n-3)) at 1 2 by lia.
 rewrite seq_A2_eqn. f_equal. f_equal. lia.
Qed.


(* optimized version of GenG.increase_bottom_decomp for k=2 *)

Lemma increase_bottom_decomp_k2 p :
  forall l, Delta 3 l ->
   exists l1 l1' l2,
     l = l1 ++ l2 /\
     sumA 2 l1' = p + sumA 2 l1 /\
     Below l1 (3 + invA_up 2 p) /\
     Delta 2 (l1'++l2).
Proof.
 intros l D.
 set (u := invA_up 2 p).
 assert (Hu : 0 < u).
 { unfold u, invA_up. lia. }
 destruct (cut_lt_ge u l) as (l1,l2) eqn:E.
 assert (E' := cut_app u l). rewrite E in E'.
 assert (B1 := cut_fst u l). rewrite E in B1. simpl in B1.
 assert (U := invA_up_spec 2 p).
 fold u in U.
 destruct l2 as [|a l2].
 - exists l1, (decomp 2 (p+sumA 2 l)), [].
   repeat split; auto.
   + rewrite decomp_sum. rewrite <- E', app_nil_r. auto.
   + intros x Hx. specialize (B1 x Hx). lia.
   + rewrite app_nil_r. apply Delta_S, decomp_delta.
 - assert (Ha : u <= a).
   { assert (B1' := @cut_snd u l a l2). rewrite E in B1'.
     simpl snd in B1'. specialize (B1' eq_refl). lia. }
   destruct (Nat.eq_dec a (u+2)).
   { set (l1' := decompminus 2 (l1++[S a]) (A 2 (S a)-A 2 a-p)).
     exists (l1++[a]), l1', l2.
     repeat split.
     * rewrite <- E'. now rewrite app_ass.
     * unfold l1'. rewrite decompminus_sum. rewrite !sumA_app.
       assert (LE : p <= A 2 (a-2)).
       { transitivity (A 2 u); auto. apply A_mono. lia. }
       clear -LE. simpl sumA. rewrite A_S. lia.
     * intro x. rewrite in_app_iff. intros [IN|[<-|[]]]; try lia.
       specialize (B1 x IN). lia.
     * { rewrite <- E', Delta_app_iff in D.
         destruct D as (D1 & D2 & D3).
         apply Delta_app with (S a).
         - apply decompminus_delta_lax.
           apply Delta_app_iff; repeat split.
           + apply Delta_S, D1.
           + constructor.
           + intros x x' Hx [<-|[]]. specialize (D3 x a Hx).
             simpl in D3. intuition.
         - now apply Delta_S_cons.
         - intro y. rewrite <- Nat.lt_succ_r. apply decompminus_below.
           intro z. rewrite in_app_iff. intros [Hz|[<-|[]]].
           + specialize (B1 z Hz). lia.
           + lia. }}
   destruct (Nat.eq_dec a (1+u)).
   { set (l1' := decompminus 2 (l1++[u;S a]) (A 2 u + A 2 (S a)-A 2 a-p)).
     exists (l1++[a]), l1', l2.
     repeat split.
     * rewrite <- E'. now rewrite app_ass.
     * unfold l1'. rewrite decompminus_sum. rewrite !sumA_app. clear l1'.
       subst a. clearbody u. simpl. lia.
     * intro x. rewrite in_app_iff. intros [IN|[<-|[]]]; try lia.
       specialize (B1 x IN). lia.
     * { rewrite <- E', Delta_app_iff in D.
         destruct D as (D1 & D2 & D3).
         apply Delta_app with (S a).
         - apply decompminus_delta_lax.
           apply Delta_app_iff; repeat split.
           + apply Delta_S, D1.
           + constructor. lia. auto.
           + intros x x' Hx [<-|[<-|[]]].
             * specialize (D3 x a Hx). simpl in D3. intuition.
             * specialize (B1 _ Hx). lia.
         - now apply Delta_S_cons.
         - intro y. rewrite <- Nat.lt_succ_r. apply decompminus_below.
           intro z. rewrite in_app_iff. intros [Hz|[<-|[<-|[]]]].
           + specialize (B1 z Hz). lia.
           + lia.
           + lia. }}
   destruct (Nat.eq_dec a u).
   { subst a.
     set (l1' := decompminus 2 (l1++[u-1;1+u]) (A 2 (2+u)-A 2 u-p)).
     exists (l1++[u]), l1', l2.
     repeat split.
     * rewrite <- E'. now rewrite app_ass.
     * unfold l1'. rewrite decompminus_sum. rewrite !sumA_app. clear l1'.
       clearbody u. generalize (twice_A2_le u). unfold A2. simpl. lia.
     * intro x. rewrite in_app_iff. intros [IN|[<-|[]]]; try lia.
       specialize (B1 x IN). lia.
     * { rewrite <- E', Delta_app_iff in D.
         destruct D as (D1 & D2 & D3).
         apply Delta_app with (1+u).
         - apply decompminus_delta_lax.
           apply Delta_app_iff; repeat split.
           + apply Delta_S, D1.
           + constructor. lia. auto.
           + intros x x' Hx [<-|[<-|[]]].
             * specialize (D3 x u Hx). simpl in D3. intuition.
             * specialize (B1 _ Hx). lia.
         - now apply Delta_S_cons.
         - intro y. rewrite <- Nat.lt_succ_r. apply decompminus_below.
           intro z. rewrite in_app_iff. intros [Hz|[<-|[<-|[]]]].
           + specialize (B1 z Hz). lia.
           + lia.
           + lia. }}
   { set (l1' := decompminus 2 (l1++[1+u]) (A 2 (1+u)-p)).
     exists l1, l1', (a::l2).
     repeat split.
     * auto.
     * unfold l1'. rewrite decompminus_sum. rewrite !sumA_app. clear l1'.
       clearbody u. simpl. lia.
     * intros x IN. specialize (B1 x IN). lia.
     * { rewrite <- E', Delta_app_iff in D.
         destruct D as (D1 & D2 & D3).
         apply Delta_app with (1+u).
         - apply decompminus_delta_lax.
           apply Delta_app_iff; repeat split.
           + apply Delta_S, D1.
           + constructor.
           + intros x x' Hx [<-|[]]. specialize (B1 _ Hx). lia.
         - constructor. lia. now apply Delta_S.
         - intro y. rewrite <- Nat.lt_succ_r. apply decompminus_below.
           intro z. rewrite in_app_iff. intros [Hz|[<-|[]]].
           + specialize (B1 z Hz). lia.
           + lia. }}
Qed.

Definition add_bound_k2 p := A2 (3 + invA_up 2 p).

Lemma additivity_bounded_k2 p :
 forall n, exists m,
   m < add_bound_k2 p /\
   h (p+n) - h n = h (p+m) - h m.
Proof.
 intros n.
 destruct (decomp_exists 2 n) as (l & E & D).
 destruct (@increase_bottom_decomp_k2 p l D)
   as (l1 & l1' & l2 & El & E1 & B1 & D1).
 exists (sumA 2 l1).
 split.
 - unfold add_bound_k2. set (q := 3+invA_up 2 p) in *. clearbody q.
   rewrite El in D. apply Delta_app_inv in D.
   rewrite <- DeltaRev_rev in D.
   rewrite <- sumA_rev.
   assert (B1r : Below (rev l1) q).
   { intro y. rewrite <- in_rev. apply B1. }
   destruct (rev l1) as [|a l1r].
   + simpl. apply A_nz.
   + apply Nat.lt_le_trans with (A 2 (S a)).
     * apply decomp_max; auto. apply D.
     * apply A_mono. apply B1r. now left.
 - rewrite <- E.
   rewrite El at 1. rewrite sumA_app, Nat.add_assoc, <- E1, <- sumA_app.
   unfold h.
   rewrite !f_sumA_lax; auto using Delta_S.
   + rewrite El, !map_app, !sumA_app. lia.
   + rewrite El in D. apply Delta_app_inv in D. apply Delta_S, D.
   + apply Delta_app_inv in D1. apply D1.
Qed.

Lemma destruct_last {A} (l : list A) : l = [] \/ exists a l', l = l' ++ [a].
Proof.
 destruct l as [|a l].
 - now left.
 - right. destruct (rev (a::l)) as [|a' l'] eqn:E.
   + now apply rev_switch in E.
   + exists a', (rev l'). apply rev_switch in E. apply E.
Qed.

(*
Ajout de p=A2 q à un nombre n. Apparemment f2 (n+p) = f2(n)+f2(p) + {-1,0,1}
En utilisant le théorème précédent, on peut se ramener à un n tel
que sa décomposition a au plus q+2 comme plus grand terme.

#### Si n a <=q-2 comme grand terme #####
OK, l'addition est une decomp lax

#### Si n a q+2 comme grand terme #####

 xxxxxx..*
+      *
=xxxxxx...*
OK

#### Si n a q-1 comme grand terme  ####

Si q>=4

Reste+A(q-1))+Aq<
 = Reste+A(q-4)+A(q-2)+Aq
 = Reste+A(q-4)+A(q+1)

HR sur l'ajout de A(q-4) à (Reste+A(q+1))

#### Si n a q+1 comme grand terme ####

Si q>=3

(Reste+A(q+1))+Aq
 = Reste+A(q-3)+A(q-1)+A(q+1)
 = Reste+A(q-3)+A(q+2)

HR sur l'ajout de A(q-3) à Reste+A(q+2)

#### Si n a q comme grand terme ####

Note: 2*Aq = A(q+2)-A(q-5)
     *....2
     *.*.**
     ...***
     ....*.*
     .......*

(Reste+Aq)+Aq = (Reste+A(q+2))-A(q-5)


f((Reste+Aq)+Aq)
= f((Reste+A(q+2))-A(q-5))
= f(Reste+A(q+2))-f(A(q-5)) +{-1,0,1}   par HR renversé
= f(Reste)+A(q+1)-A(q-6) +{-1,0,1}
= f(Reste)+2*A(q-1) + {-1,0,1}
= f(Reste+Aq) + f(Aq) + {-1,0,1}

OK!

*)



Lemma f2_addA q n : A2 (q-1) + h n - 1 <= h (A2 q + n) <= A2 (q-1) + h n + 1.
Proof.
 revert n.
 induction q as [q IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases q 3) as [LE|GT].
 - destruct q as [|[|[|[|n]]]]; simpl; intros.
   + generalize (h_add_1 n). simpl. lia.
   + generalize (h_add_2 n). simpl. lia.
   + generalize (h_add_3 n). simpl. lia.
   + generalize (h_add_4 n). simpl. lia.
   + lia.
 - intros n.
   destruct (additivity_bounded_k2 (A2 q) n) as (m & Hm & E).
   cut (A2 (q - 1) + h m - 1 <= h (A2 q + m) <= A2 (q - 1) + h m + 1).
   { generalize (@f_mono 2 n (A2 q + n)) (@f_mono 2 m (A2 q + m)).
     generalize (@A_nz 2 (q-1)). unfold A2, h in *. lia. }
   clear E n.
   replace (add_bound_k2 (A2 q)) with (A2 (3+q)) in Hm.
   2:{ unfold add_bound_k2. f_equal. f_equal. rewrite invA_up_A; lia. }
   assert (D := decomp_delta 2 m).
   rewrite <- (decomp_sum 2 m). set (l := decomp 2 m) in *.
   destruct (destruct_last l) as [->|(a & l' & E)].
   + simpl. change (h 0) with 0.
     rewrite !Nat.add_0_r. unfold A2, h. rewrite f_A. lia.
   + assert (Ha : a < 3+q).
     { apply (@A_lt_inv 2).
       rewrite <- (decomp_sum 2 m) in Hm. fold l in Hm.
       rewrite E in Hm. rewrite sumA_app in Hm. simpl sumA in Hm.
       unfold A2 in Hm. lia. }
     clearbody l. subst l. clear m Hm.
     simpl in Ha. rewrite Nat.lt_succ_r, Nat.lt_eq_cases, or_comm in Ha.
     destruct Ha as [Ha|Ha].
     { (* a = q+2 *)
       clear IH.
       replace (A2 q + _) with (sumA 2 (l'++[S a])).
       2:{ rewrite !sumA_app. simpl. unfold A2.
           replace (a-2) with q; lia. }
       unfold h,A2. rewrite !f_sumA; eauto using Delta_up_last.
       rewrite !map_app, !sumA_app. subst a; simpl. lia. }
     rewrite Nat.lt_succ_r, Nat.lt_eq_cases, or_comm in Ha.
     destruct Ha as [Ha|Ha].
     { (* a = q+1 *)
       subst a.
       replace (A2 q + _) with (A2 (q-3) + sumA 2 (l'++[q+2])) in *.
       2:{ rewrite !sumA_app. simpl.
           generalize (@seq_A2_eqn' q). unfold A2. simpl. lia. }
       assert (Hm : q-3 < q) by lia.
       specialize (IH (q-3) Hm (sumA 2 (l'++[q+2]))). revert IH.
       replace (q-3-1) with (q-4) by lia.
       set (u := h (_+_)) in *; clearbody u.
       unfold h, A2.
       rewrite !f_sumA by (try apply Delta_up_last with (S q); auto; lia).
       rewrite !map_app, !sumA_app. simpl.
       generalize (@seq_A2_eqn' (q-1)). unfold A2.
       replace (pred (q+2)) with (q+1) by lia.
       replace (S (q-1)) with q by lia.
       replace (q-1+2) with (q+1) by lia.
       replace (q-1-3) with (q-4) by lia. lia. }
     rewrite Nat.lt_succ_r, Nat.lt_eq_cases, or_comm in Ha.
     destruct Ha as [Ha|Ha].
     { (* a = q *)
       subst a.
       assert (LE : A2 (q-5) <= A2 (q+2)) by (apply A_mono; lia).
       replace (A2 q + _) with (sumA 2 (l'++[q+2]) - A2 (q-5)) in *.
       2:{ rewrite !sumA_app. simpl. rewrite Nat.add_0_r.
           rewrite <- Nat.add_sub_assoc; trivial.
           rewrite <- twice_A2_eqn' by lia. simpl. unfold A2. lia. }
       assert (Hq : q-5 < q) by lia.
       set (u := sumA 2 (l'++[q+2])).
       assert (Hu : A2 (q-5) <= u).
       { unfold u, A2. rewrite sumA_app. simpl. unfold A2 in *. lia. }
       generalize (IH (q-5) Hq (u-A2 (q-5))); clear IH.
       rewrite (Nat.add_comm _ (_-_)), Nat.sub_add; trivial.
       set (v := u - _) in *. clearbody v.
       unfold h, A2, u in *.
       rewrite !f_sumA by (try apply Delta_up_last with q; auto with arith).
       rewrite !map_app, !sumA_app. simpl.
       replace (pred (q+2)) with (q+1) by lia.
       replace (pred q) with (q-1) by lia.
       replace (q-5-1) with (q-6) by lia.
       assert (Hq' : 3 <= q-1) by lia.
       generalize (@twice_A2_eqn' (q-1) Hq').
       replace (q-1-5) with (q-6) by lia.
       replace ((q-1)+2) with (q+1) by lia. unfold A2.
       generalize (@A_nz 2 (q-1)). lia. }
     red in Ha. rewrite Nat.lt_eq_cases, or_comm in Ha.
     destruct Ha as [Ha|Ha].
     { (* a = q-1 *)
       subst q.
       replace (A2 (S a) + _) with (A2 a + sumA 2 (l'++[S a])) in *.
       2:{ rewrite !sumA_app. unfold A2. simpl. lia. }
       assert (Ha : a < S a) by lia.
       specialize (IH a Ha (sumA 2 (l'++[S a]))). revert IH.
       simpl. rewrite Nat.sub_0_r.
       set (u := h (_+_)) in *; clearbody u.
       unfold h, A2.
       rewrite !f_sumA_lax by (try apply Delta_up_last with a; auto with arith).
       rewrite !map_app, !sumA_app. simpl.
       replace (pred a) with (a-1) by lia. lia. }
     { (* a <= q-2 *)
       clear IH.
       replace (A2 q + _) with (sumA 2 (l'++[a;q])).
       2:{ rewrite !sumA_app. simpl. unfold A2. lia. }
       unfold h, A2. rewrite !f_sumA_lax; auto.
       - rewrite !map_app, !sumA_app. simpl. replace (pred q) with (q-1); lia.
       - apply Delta_app_iff in D. destruct D as (D1 & D2 & D3).
         apply Delta_app_iff; repeat split; auto.
         + constructor. lia. auto.
         + intros x x' IN [<-|[<-|[ ]]];
           specialize (D3 x a IN); simpl in *; lia. }
Qed.

(* Generalization à h(n+p), p quelconque au lieu de Aq.
   Essayons la même idée.
   on peut passer de n à m en coupant au dela de q+2 si
   q est le terme dominant de p.

#### Si m < p

On inverse les roles de m et p, puis HR sur m

#### Si m a q+2 comme grand terme #####

m = xxxxxx..*
p = xxxx..*

HR sur

m'= xxxxxx...*
p'= xxxx

OK

#### Si m a q+1 comme grand terme ####

m = xxxxxxx..*
p = xxxxxx..*

Aq+A(q+1) = A(q+2)+A(q-3)

m'= xxxxxxx...*
p'= xxxxxx
  +      *

??
On décompose plus ?

a)
p = xxx*....* ou plus d'écart : OK, p-Aq+A(q-3) lax

b)
p = xx..*...* :
p'= xx..**
  = x*....*
etc avec des doublons ou des consécutifs...

c)
p = xxx..*..*
p'= xxx..2
  = xxx....*
   -*



#### Si m a q comme grand terme ####

Note: 2*Aq = A(q+2)-A(q-5)
     *....2
     *.*.**
     ...***
     ....*.*
     .......*

m = xxxxxxx..*
p = xxxxxxx..*

m'= xxxxxxx....*
p'= xxxxxxx
  -     *


a)
p'= xxxx*..
  -     *
p'= xxxx
OK

b)
p'= xxx..*.
  -     *
p'= xxx
  +   *
et ensuite ??

c)
p'= xxxx..*
  -     *
p'= xxxx


d) p' negatif ?

p' = x..*...
  -      *
ou plus d'écart
ici: x
  -   *
etc

??

HR avec negation :

h (m-p) + h p -2 <= h (m) <= h (m-p) + h p + 2
donc (pour m>=p)
h(m)-h(p)-2 <= h(m-p) <= h(m)-h(p)+2




autre piste :
2 * A2 n = A2 (n-7) + A2(n-2) + A2(n+1).

m = xxxxxxx..*
p = xxxxxxx..*

m'= xxxxxxx...*
p'= xxxxxxx*
  +   *



??

(Reste+Aq)+Aq = (Reste+A(q+2))-A(q-5)


f((Reste+Aq)+Aq)
= f((Reste+A(q+2))-A(q-5))
= f(Reste+A(q+2))-f(A(q-5)) +{-1,0,1}   par HR renversé
= f(Reste)+A(q+1)-A(q-6) +{-1,0,1}
= f(Reste)+2*A(q-1) + {-1,0,1}
= f(Reste+Aq) + f(Aq) + {-1,0,1}

*)



(*
Lemma f2_add n m : h n + h m - 2 <= h (n + m) <= h n + h m + 2.
Proof.
 revert m.
 induction n as [n IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases n 1) as [LE|GT].
 - clear IH.
   destruct n as [|[|n]]; simpl; intros; try lia.
   generalize (h_add_1 m). simpl. lia.
 - intros m.
*)


(*
Example de "combinaison" d'additivité:
h(2+n)-h n = 1,2

donc h(4+n)-h n = (h(2+(2+n))-h(2+n))-(h(2+n) -h n)
                = {1,2}+{1,2}
                = {2,4}   (en fait {2,3} est prouvable )

Et pour l'additivité générale entre -2 et 2 :


en décalant de 1:

h (n+m) <= h (n+1+m) <= 1 + h(n+m)
h n + h m -2 <= h (n+1+m) <= 1 + 2 + h n + h m  (par IH)

donc:
h (n+1)+h m -3 <= 1+h n + h m -3 <= h(n+1+m) <= 3+h n + h m <= 3+h(n+1)+h m


en décalant de 2:

1 + h (n+m) <= h (n+2+m) <= 2 + h(n+m)
1 + h n + h m -2 <= h (n+2+m) <= 2 + 2 + h n + h m  (par IH)

donc:
h (n+2)+h m -3 <= 2+h n + h m -3 <= h(n+2+m) <= 3 + 1+h n + h m <= 3+h(n+2)+h m

h(n+m)+h(Aq) - 1 <= h(n+Aq+m) <= h(n+m)+h(Aq) +1 (dernier thm)

h(n)+h(m)+h(Aq) -2-1 <= h(n+Aq+m) <= h(n)+h(m)+h(Aq) +2+1 (IH)
h(n+Aq)+h(m) -3 <= h(n+Aq+m) <= h(n+Aq)+h(m)+3 (en prenant Aq au dela de n p.ex)

BOF
*)



(******* k=3 *******)

(* Pour f 3, on n'a pas Delta 1, avec beaucoup d'exceptions.
   Par exemple: *)

Compute (f 3 (A 3 3 + A 3 4), A 3 2 + A 3 3).

(* Mais Delta 2 n'est problématique pour f 3 que pour A 3 1 + A 3 2 *)

Lemma f3_AA n : n<>1 -> f 3 (A 3 n + A 3 (2+n)) = A 3 (n-1) + A 3 (1+n).
Proof.
 destruct (Nat.eq_dec n 0); [subst; trivial| ].
 destruct (Nat.eq_dec n 2); [subst; trivial| ].
 destruct (Nat.eq_dec n 3); [subst; trivial| ].
 intro H. rewrite f_AA; try lia. auto.
Qed.



(******* k=4 *******)

(* Idem pour Delta 3 et f 4 *)

Lemma f4_AA n : n<>1 -> f 4 (A 4 n + A 4 (3+n)) = A 4 (n-1) + A 4 (2+n).
Proof.
 destruct (Nat.eq_dec n 0); [subst; trivial| ].
 destruct (Nat.eq_dec n 2); [subst; trivial| ].
 destruct (Nat.eq_dec n 3); [subst; trivial| ].
 destruct (Nat.eq_dec n 4); [subst; trivial| ].
 intro H. rewrite f_AA; try lia. auto.
Qed.

Compute
 filter (fun '(n,u,v) => negb (u =? v))
 (map (fun n => (n,fopt 4 (A 4 n + A 4 (n+1)), A 4 (n-1) + A 4 (n))) tests).

(*
Bref, conjecture : pour tout k et tout "agencement", en "décalant"
cet agencement suffisamment vers le haut on peut le "canoniser" et
donc f (agencement) = map pred agencement
*)

(*

l = decomp (n+m)

ln = decomp n
lm = decomp m

f(n+m) = map pred l

f(n)+f(m) = map pred ln + map pred lm

lien entre decomp (n+m) et (decomp n, decomp m) ?



Soit m.
 Supposons exists I= [-2..0] ou [-1..1] ou [0..2] t.q.
  forall n, H(m+n)-H(m)-H(n) \in I.

 étudions maintenant le cas m+1.
 - soit H(m+1)=H(m)

   H(m+1+n)
   = H(m+(1+n))
   = H(m) + H(1+n) + I  (cf HR)
   = H(m+1) + H(n)+{0,1} + I  Pas concluant

 - soit H(m+1)=1+H(m)

   H(m+1+n)
   = H(m+(1+n))
   = H(m) + H(1+n) + I  (cf HR)
   = H(m+1) -1 + H(n)+{0,1} + I  Pas concluant

*)


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
     apply Delta_pred; auto using Delta_S_cons. simpl. intuition. }
 simpl. f_equal. f_equal. f_equal.
 rewrite map_map.
 rewrite <- (map_id l) at 2.
 apply map_ext_in. intros [|a] Ha; intuition.
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
