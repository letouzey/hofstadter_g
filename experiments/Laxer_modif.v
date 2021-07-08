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
   + intro H. unfold h. rewrite f_AA; try lia. f_equal. f_equal. lia.
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
 simpl. rewrite Nat.sub_0_r; lia.
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
 simpl. rewrite Nat.sub_0_r; lia.
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

Compute decomp 2 18. (* [0; 3; 6], donne du -2 avec lui-même *)
Compute decomp 2 59. (* [0; 3; 6; 9] donne du -2 avec lui-même *)
Compute decomp 2 188. (* [0; 3; 6; 9; 12] donne du -2 avec lui-même *)

(** Apparement avec n = [0;3;...3*q] et au moins 3 termes donc q>=2,
    h (2n) = 2h(n)-2

Ce sont les nombres A(3q+1)-1 pour q>=2 *)

Lemma h_additivity_minus2 q:
 let p := A2 (3*q+7)-1 in
 h (2*p) = 2 * h p - 2.
Proof.
 intros p.
 assert (E : h (S p) = h p).
 { apply flat_rank_0.
   unfold p. rewrite rank_pred with (r:=3*q+7); try lia.
   - f_equal. replace (3*q+7-1) with (6+q*3) by lia.
     rewrite Nat.mod_add; auto.
   - unfold rank. replace (A2 _) with (sumA 2 [3*q+7]) by (simpl; lia).
     rewrite decomp_sum'; auto. }
 rewrite <- E.
 replace (S p) with (A2 (3*q+7)) by (generalize (@A_nz 2 (3*q+7)); lia).
 unfold h at 2. rewrite f_A.
 rewrite <- f2_times2 by lia.
 unfold p. clear E p. set (q' := 3*q+7).
 replace (2*(A2 q' - 1)) with (2*A2 q' - 2) by lia.
 set (p' := 2*A2 q').
 assert (R : rank 2 p' = Some (3*q)).
 { unfold p'. rewrite A2_times2' by lia.
   unfold rank. rewrite decomp_sum'. f_equal. lia.
   constructor. lia. constructor. lia. auto. }
 destruct (Nat.eq_dec q 0) as [->|NE].
 - simpl in q'. clear R. subst p' q'. unfold h. now rewrite <- !fopt_spec.
 - assert (NE' : 3*q<>0) by lia.
   assert (R1 := @rank_pred 2 p' _ R NE').
   replace (3*q-1) with (2+(q-1)*3) in R1 by lia.
   rewrite Nat.mod_add in R1; auto. simpl in R1.
   assert (NE'' : 2<>0) by lia.
   assert (R2 := @rank_pred 2 (p'-1) _ R1 NE'').
   simpl in R2. replace (p'-1-1) with (p'-2) in R2 by lia.
   assert (E2 : h (S (p'-2)) = S (h (p'-2))).
   { apply nonflat_rank_nz. now rewrite R2. }
   replace (S (p'-2)) with (p'-1) in E2 by (generalize (@A_nz 2 q'); lia).
   assert (E1 : h (S (p'-1)) = S (h (p'-1))).
   { apply nonflat_rank_nz. now rewrite R1. }
   replace (S (p'-1)) with p' in E1 by (generalize (@A_nz 2 q'); lia).
   lia.
Qed.

(*
generalisation en quasi-add -2..2 pour p=(A2 q) -1 :

h(n+A2 q -1)
= h(n-1+A2 q)
= h(n-1)+h(A2 q) + {-1,0,1}
= h(n)+{-1,0} + h(A2 q - 1) + {0,1} + {-1,0,1}
= h(n)+h(A2 q -1) + {-2..2}

(ça c'est pour n<>0.
 et h(0+A2 q -1) = h(0) + h(A2 q -1) + 0)


h(n-2)+h(A2 q) + {-1..1}
h(n)+{-2,-1}+h(A2 q -2) + {1,2} + {-1..1}
h(n)+h(A2 q-2)+{-2..2}

idem pour (A2 q)-4
          (A2 q)-5
          (A2 q)-8
          (A2 q)-11
                 33
*)




Compute (decomp 2 46, decomp 2 78). (* [0; 3; 9], [0; 3; 6; 10] *)
(* Cf règle An+A(Sn) = A(n-3)+A(n+2)
   qui amène ici à   [0;3;6]+[0;3;6;11] et le 11 dégage par reduction *)

Compute decomp 2 65. (* [0; 3; 10], avec 59 par exemple *)
(* [0;3;6;9] [0;3;10]
   Encore An+ASn ...
   [0;3;6;11] [0;3;6] puis idem
*)

Compute decomp 2 84. (* [0; 3; 7; 10] avec lui-même *)
Compute sumA 2 [0;3;7].

Compute decomp 2 78. (* [0; 3; 6; 10] avec 18 (reduced_k2 vers 18) *)
Compute decomp 2 106. (* [0; 3; 6; 11] avec 18 (reduced_k2 vers 18) *)
Compute decomp 2 147. (* [0; 3; 6; 12] avec 18 (reduced_k2 vers 18) *)

Compute (decomp 2 134, decomp 2 267).
(* ([0; 3; 12], [0; 3; 6; 10; 13])
   règle An+A(Sn) =A(n-3)+A(n+2)
   [0;3;12]+[0;3;6;10;13]
   =[0;3;9;14]+[0;3;6;10]  et le 14 dégage par réduction,
   ce qui ramène à 46+78
*)

Compute (fopt 2 (sumA 2 [0;3;7;12] + sumA 2 [0;3;6;9;13]),
         fopt 2 (sumA 2 [0;3;7;12]) + fopt 2 (sumA 2 [0;3;6;9;13])).

Compute (fopt 2 (sumA 2 [0;3;10] + sumA 2 [0;3;6;9]),
         fopt 2 (sumA 2 [0;3;10]) + fopt 2 (sumA 2 [0;3;6;9])).

Compute (decomp 2 153, decomp 2 248).
 (* ([0; 3; 7; 12], [0; 3; 6; 9; 13])
    règle An+ASn
    [0;3;7;9;14] [0;3;6;9]
    [0;3;10;14] [0;3;6;9] et le 14 dégage par réduction
    ce qui ramène à 65+59
 *)

Compute (decomp 2 175, decomp 2 267).
 (* ([0; 3; 9; 12], [0; 3; 6; 10; 13])
    règle An+ASn
    [0;3;9;14] [0;3;6;9;10]
    et de nouveau
    [0;3;6;9;14] [0;3;6;11]
    puis 9+11 =12
    et 12+14 = 15, qui dégage par réduction, on arrive à 2*18
 *)

Compute (decomp 2 194, decomp 2 207).
 (* ([0; 3; 13], [0; 3; 6; 13])
    2*[13] = [6;11;14] donc
    [0;3;6;11;14] [0;3;6] et 11 et 14 dégage...
 *)

(** Pour delta=+2 *)

Compute decomp 2 39. (* [1; 5; 8] donne +2 avec lui même *)
Compute (decomp 2 99, decomp 2 168).
 (* ([1; 5; 11], [1; 5; 8; 12]) *)
Compute decomp 2 124. (* [1; 4; 8; 11] donne +2 avec lui-même *)
Compute decomp 2 127. (* [1; 5; 8; 11] donne +2 avec lui-même *)
Compute decomp 2 140. (* [1; 5; 12] donne +2 avec 127 *)
Compute decomp 2 168. (* [1; 5; 8; 12] donne +2 avec 39 :
                         exemple de reduction de 168 vers 39 *)

(* [1;5;8] : +4 +3
   [1;4;8;11] : +3 +4 +3
   [1;5;8;11] : +4 +3 +3
   [1;5;8;12] : +4 +3 +4
*)

(** bound_idx_k2 : si p est un A2 q, alors q+3
    sinon, avec A2 q le terme dominant de p, alors q+4
    (invA_up donne (q+1) pour majorer p).
 *)



(* Generalization à h(n+p), p quelconque au lieu de Aq.
   Essayons la même idée.
   on peut passer de n à m en coupant au dela de q+3 si
   q est le terme dominant de p.

#### Si m < p

On inverse les roles de m et p, puis HR sur m


#### Si m a q+3 comme grand terme #####

m = xxxxxx..*
p = xxx..*

Sous-cas:

m = xxx..*..*
p = xxx..*

??


HR sur

m'= xxxxxx...*
p'= xxxx

OK


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

