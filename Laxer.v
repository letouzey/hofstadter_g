Require Import Arith Lia Wf_nat List Bool.
Require Import DeltaList GenFib GenG.
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

(* pour k = 2:
   strict = Delta 3
   lax = Delta 2

   Mais on n'a pas Delta 0 ni Delta 1: *)

Compute (f 2 (A 2 0 + A 2 0), A 2 0 + A 2 0).
Compute (f 2 (A 2 1 + A 2 2), A 2 0 + A 2 1).

(* Pour deux A-nombres consécutifs, ce sont les seuls à problème,
   cf f_AA + verification manuelle pour n=0 et n=2
*)

Lemma f2_AA n : n<>1 -> f 2 (A 2 n + A 2 (S n)) = A 2 (n-1) + A 2 n.
Proof.
 destruct (Nat.eq_dec n 0).
 - subst; trivial.
 - destruct (Nat.eq_dec n 2).
   + subst; trivial.
   + intro H. rewrite f_AA; try lia. f_equal. f_equal. lia.
Qed.

(* Deux nombres égaux: *)

Compute decomp 2 (2 * A 2 2). (* [4] *)
Compute decomp 2 (2 * A 2 3). (* [1;4] *)
Compute decomp 2 (2 * A 2 4). (* [2;5] *)
Compute decomp 2 (2 * A 2 5). (* [0;3;6] *)
Compute decomp 2 (2 * A 2 6). (* [0;4;7] *)
Compute decomp 2 (2 * A 2 7). (* [0;5;8] OK *)
Compute decomp 2 (2 * A 2 8). (* [1;6;9] *)
Compute decomp 2 (2 * A 2 9). (* [2;7;10] *)
(*

          2
       *.**
      ***.*
      **...*
   *.*.*...*
   *....*..*
*)

Lemma A2_times2 n : 2 * A 2 (7+n) = sumA 2 [n;5+n;8+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma A2_times2' n : 5<=n -> 2 * A 2 n = sumA 2 [n-7;n-2;n+1].
Proof.
 rewrite Nat.lt_eq_cases.
 intros [H|<-]; trivial.
 red in H. rewrite Nat.lt_eq_cases in H. destruct H as [H|<-]; trivial.
 replace n with (7+(n-7)) at 1 by lia.
 rewrite A2_times2. f_equal. repeat (f_equal; try lia).
Qed.

Lemma f2_times2 n : 6<=n -> f 2 (2 * A 2 n) = 2 * A 2 (n-1).
Proof.
 intros H. rewrite !A2_times2' by lia.
 rewrite f_sumA. f_equal; simpl. repeat (f_equal; try lia).
 repeat (constructor; try lia).
Qed.

(* 3 nombres egaux *)

Compute decomp 2 (3 * A 2 3). (* [2;5] *)
Compute decomp 2 (3 * A 2 4). (* [0;3;6] *)
Compute decomp 2 (3 * A 2 5). (* [1;4;7] *)
Compute decomp 2 (3 * A 2 6). (* [1;5;8] *)
Compute decomp 2 (3 * A 2 7). (* [2;6;9] *)
Compute decomp 2 (3 * A 2 8). (* [0;3;7;10] *)
Compute decomp 2 (3 * A 2 9). (* [0;4;8;11] *)
Compute decomp 2 (3 * A 2 10). (* [0;5;9;12] OK *)
Compute decomp 2 (3 * A 2 11). (* [1;6;10;13] *)
Compute decomp 2 (3 * A 2 12). (* [2;7;11;14] *)

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

Lemma A2_times3 n : 3 * A 2 (10+n) = sumA 2 [n;5+n;9+n;12+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma A2_times3' n : 9<=n -> 3 * A 2 n = sumA 2 [n-10;n-5;n-1;n+2].
Proof.
 rewrite Nat.lt_eq_cases.
 intros [H|<-]; trivial.
 replace n with (10+(n-10)) at 1 by lia.
 rewrite A2_times3. f_equal. repeat (f_equal; try lia).
Qed.

Lemma f2_times3 n : 10<=n -> f 2 (3 * A 2 n) = 3 * A 2 (n-1).
Proof.
 intros H. rewrite !A2_times3' by lia.
 rewrite f_sumA. f_equal; simpl. repeat (f_equal; try lia).
 repeat (constructor; try lia).
Qed.

(* triplets consecutifs : tout va bien, zero exceptions *)
(* *** = .*.* *)

Lemma A2_seq3 n : sumA 2 [n;1+n;2+n] = sumA 2 [1+n;3+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma f2_seq3 n : f 2 (sumA 2 [n;1+n;2+n]) = sumA 2 [n-1;n;1+n].
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

Lemma f2_seq4 n : f 2 (sumA 2 [n;1+n;2+n;3+n]) = sumA 2 [n-1;n;1+n;2+n].
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
 f 2 (sumA 2 [n;1+n;2+n;3+n;4+n]) = sumA 2 [n-1;n;1+n;2+n;3+n].
Proof.
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

(*
Ajout d'un A2 à un nombre.
Si l'ajout reste lax, RAS (p.ex. en bas ou en haut de la decomp)

Si juste avant: OK (dès que assez grand)
     *..*..*
+   *
=*.*.*..*..*

Si juste au dessus, par exemple:
        *..*..*
+              *
=       *..2.*.*
=       *..2....*
=       2.**....*
=      *2*.*....*
=      *2...*...*
=    *.2*...*...*
=   *****...*...*
=   **.*.*..*...*
=   **....*.*...*
=   **.......*..*
=*....*......*..*



Si égaux au dernier

 *..*..*
+*


 *..*..**.*
 *..*..*.*** ?


Si en bas d'intervalle : RAS

 *..*..*
+ *
=*...*.*
OK

Si en haut d'intervalle:

 *..*..*
+  *
=...2..*
=


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
