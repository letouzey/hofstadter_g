(** * Fib : Fibonacci sequence and decomposition *)

Require Import MoreTac MoreList DeltaList.
Import ListNotations.
Set Implicit Arguments.

(** * Generalized Fibonacci sequence *)

Fixpoint A (k n : nat) :=
  match n with
  | O => 1
  | S n => A k n + A k (n-(k-1))
  end.

(**
 - k<=1 : binary numbers
 - k=2 : Fibonacci numbers (non-standard indexes)
         1 2 3 5 8 ...
 - k=3 : Narayana’s Cows, see OEIS A930 (shifted)
 - k=4 : See OEIS A003269 (shifted)
*)

(*
Compute take 10 (A 1).
Compute take 10 (A 2).
Compute take 10 (A 3).
Compute take 10 (A 4).
*)
(*
A 1 : [1; 2; 4; 8; 16; 32; 64; 128; 256; 512]
A 2 : [1; 2; 3; 5; 8; 13; 21; 34; 55; 89]
A 3 : [1; 2; 3; 4; 6; 9; 13; 19; 28; 41]
A 4 : [1; 2; 3; 4; 5; 7; 10; 14; 19; 26]
*)

Lemma A_k_0 k : A k 0 = 1.
Proof.
 reflexivity.
Qed.

Lemma A_S k n : A k (S n) = A k n + A k (n-(k-1)).
Proof.
 reflexivity.
Qed.

Lemma A_base k n : n <= k -> A k n = S n.
Proof.
 induction n; auto.
 simpl. intros.
 replace (n-(k-1)) with 0 by lia. simpl.
 rewrite IHn; lia.
Qed.

Lemma pred_succ p : S p - 1 = p.
Proof. lia. Qed.
Lemma succ_pred p : p<>0 -> S (p-1) = p.
Proof. lia. Qed.
Ltac fixpred := rewrite ?pred_succ, ?succ_pred in * by lia.

Lemma A_sum k n : k<>0 -> n<>0 -> A k n = A k (n-1) + A k (n-k).
Proof.
 destruct n.
 - now destruct 2.
 - intros Hk _. fixpred. now replace (S n - k) with (n-(k-1)) by lia.
Qed.

Lemma A_sum' k n : k<>0 -> A k (n+k) = A k n + A k (n+(k-1)).
Proof.
 intros.
 rewrite A_sum by lia.
 rewrite Nat.add_comm. f_equal; f_equal; lia.
Qed.

(** The case k=0 is meaningless and will be excluded most of the time.
    Our implementation makes A 0 be the same as A 1. *)
Lemma A_0 n : A 0 n = A 1 n.
Proof.
 induction n; simpl; trivial. rewrite Nat.sub_0_r. lia.
Qed.

Lemma A_k_1 k : A k 1 = 2.
Proof.
 reflexivity.
Qed.

Lemma A_1_pow2 n : A 1 n = 2^n.
Proof.
 induction n.
 - reflexivity.
 - rewrite A_S, Nat.sub_0_r. simpl. lia.
Qed.

Lemma A_nz k n : 1 <= A k n.
Proof.
 induction n; simpl; auto with arith.
Qed.

Lemma A_lt_S k n : A k n < A k (S n).
Proof.
 simpl. generalize (A_nz k (n-(k-1))). lia.
Qed.

Lemma A_lt k n n' : n < n' -> A k n < A k n'.
Proof.
 induction 1.
 - apply A_lt_S.
 - transitivity (A k m); trivial. apply A_lt_S.
Qed.

Lemma A_mono k n n' : n <= n' -> A k n <= A k n'.
Proof.
 induction 1; trivial.
 transitivity (A k m); trivial. apply Nat.lt_le_incl, A_lt_S.
Qed.

Lemma A_S_le_twice k n : A k (S n) <= 2 * A k n.
Proof.
 rewrite A_S. simpl. generalize (@A_mono k (n-(k-1)) n). lia.
Qed.

Lemma A_inj k n n' : A k n = A k n' -> n = n'.
Proof.
 intros.
 destruct (lt_eq_lt_dec n n') as [[LT|EQ]|LT]; trivial;
  apply (A_lt k) in LT; lia.
Qed.

Lemma A_lt_inv k n n' : A k n < A k n' -> n < n'.
Proof.
 intros.
 destruct (le_lt_dec n' n) as [LE|LT]; trivial.
 apply (A_mono k) in LE. lia.
Qed.

Lemma A_le_inv k x y : A k x <= A k y -> x <= y.
Proof.
 rewrite Nat.lt_eq_cases. intros [LT|EQ].
 - apply A_lt_inv in LT. lia.
 - apply A_inj in EQ. lia.
Qed.

Lemma A_lt_id k n : n < A k n.
Proof.
 induction n; simpl; auto.
 generalize (A_nz k (n-(k-1))). lia.
Qed.

Lemma A_base_iff k n : k<>0 -> n <= k <-> A k n = S n.
Proof.
 intros Hk.
 split. apply A_base.
 intros.
 destruct n; auto with arith.
 rewrite A_S in H.
 generalize (A_lt_id k n).
 generalize (A_lt_id k (n-(k-1))).
 lia.
Qed.

Lemma A_high k n : k<>0 -> k < n <-> S n < A k n.
Proof.
 intros Hk.
 generalize (@A_base_iff k n Hk) (A_lt_id k n). lia.
Qed.

Lemma A_Sk_le k n : A (S k) n <= A k n.
Proof.
 induction n as [[|n] IH] using lt_wf_ind; auto.
 rewrite !A_S. fixpred.
 apply Nat.add_le_mono. apply IH; lia.
 etransitivity. apply IH; lia. apply A_mono. lia.
Qed.

Lemma A_Sk_lt k n : 0 < k < n -> A (S k) n < A k n.
Proof.
 intros LT.
 replace n with (k + 1 + (n - k - 1)) by lia.
 set (m := n - k - 1). clearbody m. destruct LT as (LT,_). clear n.
 induction m.
 - rewrite Nat.add_0_r.
   rewrite A_base by lia.
   rewrite Nat.add_succ_r.
   rewrite A_S.
   rewrite A_base by lia.
   replace (k+0-(k-1)) with 1 by lia. rewrite A_k_1. lia.
 - rewrite Nat.add_succ_r.
   rewrite !A_S.
   apply Nat.add_lt_le_mono; auto. clear IHm.
   fixpred.
   replace (k + 1 + m - k) with (S m) by lia.
   replace (k + 1 + m - (k-1)) with (S (S m)) by lia.
   transitivity (A k (S m)). apply A_Sk_le. apply A_mono; lia.
Qed.

(* (A k) is sub-multiplicative

   Note : Thanks to Fekete theorem, this implies that
   [(ln (A k n))/n] has a finite limit when n grows. But without
   extra details about the next term in the asymptotic development,
   we cannot say much more this way, especially nothing on the limit
   of the ratio [A k (S n) / A k n] or even its existence.
*)

Lemma A_submult k n p : A k (n+p) <= A k n * A k p.
Proof.
 induction n as [[|n] IH] using lt_wf_ind.
 - cbn. lia.
 - destruct (Nat.le_gt_cases k (S n)).
   + cbn.
     assert (IHn := IH n).
     assert (IHnq := IH (n-(k-1))).
     replace (n-(k-1)+p) with (n+p-(k-1)) in IHnq; lia.
   + rewrite (@A_base k (S n)) by lia.
     cbn - ["*"].
     assert (IHn := IH n).
     rewrite (@A_base k n) in IHn by lia.
     assert (LE : n + p - (k-1) <= p) by lia.
     apply (A_mono k) in LE. lia.
Qed.

(* After the "base" zone, a "triangular" zone *)

Definition triangle p := p*(p+1)/2.

Lemma pSp_even p : p*(p+1) mod 2 = 0.
Proof.
 destruct (Nat.Even_or_Odd p) as [(p',->)|(p',->)].
 - rewrite <- Nat.mul_assoc, Nat.mul_comm.
   apply Nat.mod_mul; auto.
 - replace (2*p'+1+1) with (2*(p'+1)) by lia.
   rewrite (Nat.mul_comm 2 (p'+1)), Nat.mul_assoc.
   apply Nat.mod_mul; auto.
Qed.

Lemma double_triangle p : 2 * triangle p = p*(p+1).
Proof.
 rewrite (Nat.div_mod (p*(p+1)) 2); auto. now rewrite pSp_even.
Qed.

Lemma triangle_succ p : triangle (S p) = triangle p + S p.
Proof.
 apply Nat.mul_cancel_l with 2; auto.
 rewrite Nat.mul_add_distr_l.
 rewrite !double_triangle. lia.
Qed.

Lemma triangle_aboveid p : p <= triangle p.
Proof.
 induction p; auto. rewrite triangle_succ. lia.
Qed.

Lemma A_triangle k n : k<>0 -> n <= k+1 -> A k (k-1 + n) = k + triangle n.
Proof.
 intros Hk.
 induction n.
 - intros _. rewrite A_base by lia. unfold triangle. simpl. lia.
 - intros LE.
   rewrite Nat.add_succ_r, A_S.
   replace (_ + n - _) with n by lia.
   rewrite (@A_base k n) by lia.
   rewrite triangle_succ.
   rewrite IHn; lia.
Qed.

(* Just after the triangular zone : *)

Lemma A_2k1_eqn k : k<>0 -> A k (2*k+1) = A k (2*k) + A k k + 2.
Proof.
 intros Hk.
 rewrite Nat.add_succ_r, A_S.
 rewrite <- Nat.add_assoc. f_equal. f_equal. lia.
 replace (2*k+0-(k-1)) with (S k) by lia.
 rewrite A_S. f_equal.
 replace (k - (k-1)) with 1 by lia.
 apply A_k_1.
Qed.

Lemma A_2k1_tri k : k<>0 -> A k (2*k+1) = triangle (k+3) - 2.
Proof.
 intros Hk.
 rewrite A_2k1_eqn by trivial.
 replace (2*k) with (k-1+S k) by lia.
 rewrite A_triangle, A_base by lia.
 replace (k+3) with (S (S (S k))) by lia.
 rewrite (triangle_succ (S (S k))).
 rewrite (triangle_succ (S k)). lia.
Qed.

(* Behavior of A diagonals :
   decreasing then flat at [n=2*k+1] then [+1] steps. *)

Lemma A_diag_eq k n : k<>0 -> n = 2*k+1 -> A (S k) (S n) = A k n.
Proof.
 intros Hk ->.
 replace (S (2*k + 1)) with (S k-1 + S (k+1)) by lia.
 rewrite A_triangle by lia.
 rewrite A_2k1_tri by trivial.
 replace (k+3) with (S (S (k+1))) by lia.
 rewrite (triangle_succ (S (k+1))). lia.
Qed.

Lemma A_diag_step k n : k<>0 -> n < 2*k+1 -> A (S k) (S n) = S (A k n).
Proof.
 intros Hk.
 induction n.
 - intros _. now rewrite A_k_1, A_k_0.
 - intros LT.
   rewrite A_S.
   rewrite IHn by lia. rewrite A_S. cbn -[Nat.sub]. f_equal. f_equal.
   rewrite !A_base; lia.
Qed.

Lemma A_diag_decr k n : k<>0 -> 2*k+1 < n -> A (S k) (S n) < A k n.
Proof.
 intros Hk LT.
 replace n with (2*k+2+(n-2*k-2)) by lia.
 set (m := n-2*k-2). clearbody m. clear n LT.
 induction m.
 - rewrite !Nat.add_0_r.
   rewrite A_S. rewrite Nat.add_succ_r, A_diag_eq by lia.
   replace (S(2*k+1)-(S k-1)) with (k+2) by lia.
   rewrite A_S.
   apply Nat.add_lt_mono_l.
   replace (2*k+1-(k-1)) with (k+2) by lia.
   apply A_Sk_lt. lia.
 - rewrite Nat.add_succ_r, (A_S (S k)), (A_S k).
   replace (S k - 1) with (S (k-1)) by lia.
   apply Nat.add_lt_le_mono; auto using A_Sk_le.
Qed.

Lemma A_diag_decr_exact k n : k<>0 -> 2*k+1 <= n <= 3*k ->
  A k n = A (S k) (S n) + ((n-2*k-1)*(n-2*k+2))/2.
Proof.
 induction n as [n IH] using lt_wf_ind.
 intros Hk Hn.
 destruct (Nat.eq_dec n (2*k+1)) as [E|N].
 - replace (n-2*k-1) with 0 by lia. simpl "/". now rewrite A_diag_eq.
 - replace n with (S (n-1)) at 1 by lia. simpl A.
   rewrite (IH (n-1)) by lia.
   replace (S (n-1)) with n by lia.
   rewrite <- !Nat.add_assoc. f_equal.
   replace (n-(k-0)) with (S (n-k-1)) by lia.
   rewrite A_diag_step by lia.
   replace (n-1-(k-1)) with (S (n-k-1)) by lia.
   rewrite A_S. rewrite (@A_base k (n-k-1-(k-1))) by lia.
   rewrite Nat.add_shuffle3. rewrite !Nat.add_succ_r, Nat.add_succ_l.
   f_equal. f_equal.
   set (m := n-1-2*k-1).
   replace (n-2*k-1) with (m+1) by lia.
   replace (n-k-1-(k-1)) with (m+2) by lia.
   replace (S (S (n-1-2*k+0))) with (m+3) by lia.
   replace (S (S (n-2*k+0))) with (m+4) by lia.
   replace ((m+1)*(m+4)) with (m*(m+3)+(m+2)*2) by ring.
   rewrite Nat.div_add; lia.
Qed.

(* Inverting A *)

Fixpoint invA k n :=
  match n with
  | 0 => 0
  | S n =>
    let p := invA k n in
    if S (S n) =? A k (S p) then S p else p
  end.

Lemma invA_spec k n : A k (invA k n) <= S n < A k (S (invA k n)).
Proof.
 induction n as [|n IH].
 - simpl. auto.
 - cbn -[A Nat.eqb].
   case Nat.eqb_spec; [intros E|intros; lia].
   split. lia. rewrite E. apply A_lt_S.
Qed.

Lemma invA_spec' k n p : A k p <= S n < A k (S p) -> invA k n = p.
Proof.
 intros H.
 assert (H' := invA_spec k n).
 assert (p < S (invA k n)) by (apply (A_lt_inv k); lia).
 assert (invA k n < S p) by (apply (A_lt_inv k); lia).
 lia.
Qed.

Lemma A_inv k n : { p | A k p <= S n < A k (S p) }.
Proof.
 exists (invA k n). apply invA_spec.
Defined.

Lemma A_inv' k n : n<>0 -> { p | A k p <= n < A k (S p) }.
Proof.
 destruct n.
 - now destruct 1.
 - intros _. apply A_inv.
Defined.

Lemma invA_A k p : invA k (A k p - 1) = p.
Proof.
 apply invA_spec'.
 replace (S (A k p -1)) with (A k p) by (generalize (A_nz k p); lia).
 split; auto. apply A_lt. lia.
Qed.

Lemma invA_A' k p : p<>0 -> invA k (A k p - 2) = p-1.
Proof.
 intros Hq.
 apply invA_spec'.
 assert (2 <= A k p) by (apply (@A_mono k 1 p); lia).
 replace (S (A k p - 2)) with (A k p - 1) by lia.
 replace (S (p-1)) with p by lia.
 split; try lia.
 generalize (@A_lt k (p-1) p). lia.
Qed.

Lemma invA_0 n : invA 0 n = invA 1 n.
Proof.
 induction n; simpl; trivial. now rewrite !Nat.sub_0_r, IHn, A_0.
Qed.

(** The first [A] number greater or equal to [n]. *)

Definition invA_up k n := invA k (n-2) + if 1 <? n then 1 else 0.

Lemma invA_up_spec k n : n <= A k (invA_up k n).
Proof.
 unfold invA_up. destruct (invA_spec k (n-2)) as (_,H).
 set (p := invA _ _) in *.
 case Nat.ltb_spec.
 - rewrite Nat.add_1_r. lia.
 - generalize (A_nz k (p+0)). lia.
Qed.

Lemma invA_up_is_0 k n : invA_up k n = 0 <-> n <= 1.
Proof.
 unfold invA_up.
 case Nat.ltb_spec; simpl.
 - rewrite Nat.add_1_r; lia.
 - split; trivial. now replace (n-2) with 0 by lia.
Qed.

Lemma invA_up_least k n : 1<n -> A k ((invA_up k n)-1) < n.
Proof.
 intros H. unfold invA_up. case Nat.ltb_spec; try lia. intros _.
 replace (_+1-1) with (invA k (n-2)) by lia.
 destruct (invA_spec k (n-2)) as (H',_). lia.
Qed.

Lemma invA_up_A k n : invA_up k (A k n) = n.
Proof.
 unfold invA_up. case Nat.ltb_spec.
 - intros H. change 1 with (A k 0) in H. apply A_lt_inv in H.
   rewrite invA_A'; lia.
 - intros H. change 1 with (A k 0) in H. apply A_le_inv in H.
   now replace n with 0 by lia.
Qed.

(** * Decomposition via sums of Ak numbers.

    Zeckendorf's theorem (actually discovered earlier by
    Lekkerkerker) states that any natural number can be obtained
    by a sum of distinct Fibonacci numbers, and this decomposition
    is moreover unique when Fibonacci numbers in the decomposition
    aren't consecutive.

    This is the generalization to Ak numbers.
*)

(** ** The [sumA] function

   We represent a decomposition by the list of indexes
   of the Ak numbers in this decomposition.
   The sumA function is the sum of the Fibonacci numbers of
   these indexes. For the first results below, the indexes may be
   arbitrary : redundant, in any order, ... *)

Definition sumA k l := fold_right (fun n acc => A k n + acc) 0 l.

Lemma sumA_cons k a l : sumA k (a::l) = A k a + sumA k l.
Proof.
 reflexivity.
Qed.

Lemma sumA_eqn k l :
 sumA k l + sumA k (map (decr (k-1)) l) = sumA k (map S l).
Proof.
 induction l; trivial.
 simpl map. rewrite !sumA_cons, <- IHl, A_S.
 unfold decr at 1. lia.
Qed.

Lemma sumA_eqn' k l :
 sumA k (map S l) - sumA k (map (decr (k-1)) l) = sumA k l.
Proof.
 rewrite <- sumA_eqn. apply Nat.add_sub.
Qed.

Lemma sumA_eqn_pred k l :
 k<>0 ->
 ~In 0 l ->
 sumA k l = sumA k (map (decr 1) l) + sumA k (map (decr k) l).
Proof.
 intros Hk.
 induction l; trivial.
 simpl map. simpl. intros. rewrite IHl by intuition.
 unfold decr at 3 5.
 rewrite (@A_sum k a Hk); lia.
Qed.

Lemma sumA_app k l l' : sumA k (l++l') = sumA k l + sumA k l'.
Proof.
 revert l'.
 induction l; intros.
 - trivial.
 - simpl. rewrite IHl. lia.
Qed.

Lemma sumA_rev k l : sumA k (rev l) = sumA k l.
Proof.
 induction l.
 - trivial.
 - simpl. rewrite sumA_app, IHl. simpl. lia.
Qed.

Lemma sumA_0 k l : sumA k l = 0 <-> l = [].
Proof.
 split.
 - intros H. destruct l; [ now elim H |].
   simpl in *. generalize (A_nz k n). lia.
 - intros; now subst.
Qed.

Lemma sumA_in_le k l x : In x l -> A k x <= sumA k l.
Proof.
 induction l; simpl.
 - inversion 1.
 - intros [<-|IN]; auto with arith.
   transitivity (sumA k l); auto with arith.
Qed.

Lemma sumA0 l : sumA 0 l = sumA 1 l.
Proof.
 induction l; simpl; trivial. now rewrite A_0, IHl.
Qed.

(** ** Zeckendorf's Theorem *)

(** All numbers can be decomposed as a sum of A numbers.
    Existence of the decomposition is given by the [decomp] function below
    (small terms first). *)

Fixpoint decomp k n :=
 match n with
 | 0 => []
 | S n =>
   let p := invA k n in
   decomp k (n - (A k p - 1)) ++ [p]
 end.

Lemma decomp_sum k n :
 sumA k (decomp k n) = n.
Proof.
 induction n as [[|n] IH] using lt_wf_rec; trivial.
 cbn - [invA sumA].
 destruct (invA_spec k n) as (H,_).
 set (p := invA k n) in *.
 rewrite sumA_app. rewrite IH by lia. simpl.
 generalize (A_nz k p). lia.
Qed.

Lemma decomp_in k n x : In x (decomp k n) -> A k x <= n.
Proof.
 induction n as [[|n] IH] using lt_wf_rec; try easy.
 cbn - [invA sumA]. rewrite in_app_iff. intros [IN|[<-|[ ]]].
 apply IH in IN; lia.
 apply invA_spec.
Qed.

Lemma decomp_delta k n : Delta k (decomp k n).
Proof.
 induction n as [[|n] IH] using lt_wf_rec; autoh.
 cbn - [invA sumA].
 destruct (invA_spec k n) as (H,H').
 set (p := invA k n) in *.
 apply Delta_app_iff; repeat split; autoh.
 - apply IH. lia.
 - intros x x' IN [<-|[ ]].
   apply decomp_in in IN.
   cut (x < p - (k-1)); [lia|].
   apply (A_lt_inv k).
   rewrite A_S in H'. lia.
Qed.
#[global] Hint Resolve decomp_sum decomp_delta : hof.

Lemma decomp_exists k n :
  { l | sumA k l = n /\ Delta k l }.
Proof.
 exists (decomp k n). split. apply decomp_sum. apply decomp_delta.
Qed.

(** Technical lemma for uniqueness of decomposition :
    A canonical decomposition cannot excess the next Ak. *)

Lemma decomp_max k n l :
  k<>0 -> DeltaRev k (n::l) -> sumA k (n::l) < A k (S n).
Proof.
 intros Hk.
 revert n.
 induction l.
 - intros n _. simpl sumA. rewrite Nat.add_0_r. apply A_lt_S.
 - intros n.
   inversion 1; subst. simpl sumA.
   rewrite A_S.
   apply Nat.add_lt_mono_l.
   apply Nat.lt_le_trans with (A k (S a)).
   + apply IHl; auto.
   + apply A_mono; lia.
Qed.

Lemma rev_switch {A} (l l' : list A) : rev l = l' -> l = rev l'.
Proof.
 intros. now rewrite <- (rev_involutive l), H.
Qed.

Lemma sumA_below k l p : k<>0 -> Delta k l -> Below l p -> sumA k l < A k p.
Proof.
 intros K D B.
 destruct (rev l) as [|a rl'] eqn:E''.
 - apply rev_switch in E''. subst l. simpl.
   generalize (@A_nz k p). lia.
 - rewrite <- sumA_rev, E''.
   apply Nat.lt_le_trans with (A k (S a)).
   + apply decomp_max; trivial. rewrite <- E''. now apply DeltaRev_rev.
   + apply A_mono. specialize (B a).
     rewrite in_rev, E'' in B. simpl in B. intuition.
Qed.

(** Uniqueness. Easier to prove on lists with large terms first. *)

Lemma decomp_unique_rev k l l' :
 k<>0 ->
 DeltaRev k l ->
 DeltaRev k l' ->
 sumA k l = sumA k l' -> l = l'.
Proof.
 intros Hk.
 revert l'.
 induction l as [|n l IH]; destruct l' as [|n' l'].
 - trivial.
 - intros _ Hn'. simpl in *. generalize (A_nz k n'); lia.
 - intros Hn _. simpl in *. generalize (A_nz k n); lia.
 - intros DR DR' EQ.
   assert (n < S n').
   { apply (A_lt_inv k). simpl in EQ.
     apply Nat.le_lt_trans with (A k n' + sumA k l'); [lia|].
     now apply decomp_max. }
   assert (n' < S n).
   { apply (A_lt_inv k). simpl in EQ.
     apply Nat.le_lt_trans with (A k n + sumA k l); [lia|].
     now apply decomp_max. }
   replace n' with n in * by lia. clear H H0.
   simpl in EQ.
   f_equal.
   apply IH; clear IH; simpl in *; try lia; intuition.
   + apply DeltaRev_alt in DR. intuition.
   + apply DeltaRev_alt in DR'. intuition.
Qed.

Lemma decomp_unique k l l' :
 k<>0 -> Delta k l -> Delta k l' -> sumA k l = sumA k l' -> l = l'.
Proof.
 intros K D D' EQ.
 rewrite <- (rev_involutive l), <- (rev_involutive l'). f_equal.
 apply (@decomp_unique_rev k); trivial.
 - now apply DeltaRev_rev.
 - now apply DeltaRev_rev.
 - now rewrite !sumA_rev.
Qed.

Lemma decomp_carac k n l :
 k<>0 -> Delta k l -> sumA k l = n -> decomp k n = l.
Proof.
 intros K D Eq. apply (@decomp_unique k); autoh.
 now rewrite decomp_sum.
Qed.
#[global] Hint Resolve decomp_carac : hof.

Lemma decomp_sum' k l :
 k<>0 -> Delta k l -> decomp k (sumA k l) = l.
Proof.
 intros. now apply decomp_carac.
Qed.

Lemma decomp_0 n : decomp 0 n = decomp 1 n.
Proof.
 induction n as [[|n] IH] using lt_wf_ind; trivial.
 simpl. now rewrite IH, invA_0, A_0 by lia.
Qed.

Lemma decomp_low k n : 1 <= n <= k+1 -> decomp k n = [n-1].
Proof.
 revert n.
 withoutloss k (k<>0).
 { intros K n Hn.
   apply decomp_carac. trivial. constructor. cbn. rewrite A_base; lia. }
 { intros n Hn.
   destruct (Nat.eq_dec k 0) as [->|K].
   - rewrite decomp_0. apply WL; lia.
   - now apply WL. }
Qed.

Lemma decomp_plus_A k n p :
 k<>0 -> p < A k (n-(k-1)) -> decomp k (p + A k n) = decomp k p ++ [n].
Proof.
 intros Hk LT.
 apply decomp_carac; trivial.
 - apply Delta_app_iff; repeat split;
     [apply decomp_delta|constructor|].
   intros x x' Hx [<-|[ ]].
   apply decomp_in in Hx.
   assert (LT' := Nat.le_lt_trans _ _ _ Hx LT).
   apply A_lt_inv in LT'. lia.
 - rewrite sumA_app, decomp_sum. simpl. lia.
Qed.

(** ** Normalisation of a Fibonacci decomposition.

    Starting from an relaxed decomposition (with gaps
    of at least [k-1]), we can transform it into a canonical
    decomposition (with gaps of at least [k]),
    by simply saturating the basic equation
    [A k n + A k (n-(k-1)) = A k (S n)]
    in the right order (highest terms first).

    Termination isn't obvious for Coq, since we might have
    to re-launch normalisation on by-products of a first
    normalisation. The number of terms in the decomposition
    decreases strictly during the process, we use that to
    justify the termination.

    Moreover, the lowest term in the decomposition grows by
    steps of [k] during the process (or stays equal).
*)

Fixpoint renorm_loop k l n :=
 match n with
 | 0 => []
 | S n =>
   match l with
   | [] => []
   | p::l =>
     match renorm_loop k l n with
     | [] => [p]
     | p'::l' =>
       if p+(k-1) =? p' then
         renorm_loop k (S p' :: l') n
       else
         p::p'::l'
     end
   end
 end.

Definition renorm k l := renorm_loop k l (length l).

(*
Compute renorm 2 [0;1;3;4;5;7]. (* [4; 8] *)
Compute renorm 1 [1;3;5;8]. (* [1; 9] *)
*)

Lemma renorm_loop_length k l n :
  length l <= n -> length (renorm_loop k l n) <= length l.
Proof.
 revert l.
 induction n; simpl; auto with arith.
 intros [|p l] LE; simpl in *; auto.
 apply Nat.succ_le_mono in LE.
 assert (Hl := IHn l LE).
 destruct renorm_loop as [|p' l']. simpl in *; try lia.
 case Nat.eqb_spec; intros; simpl in *; try lia.
 etransitivity; try eapply IHn; simpl; lia.
Qed.

Lemma renorm_length k l : length (renorm k l) <= length l.
Proof.
 unfold renorm. now apply renorm_loop_length.
Qed.
#[global] Hint Resolve renorm_length : hof.

Lemma renorm_loop_sum k l n :
  length l <= n -> sumA k (renorm_loop k l n) = sumA k l.
Proof.
 revert l.
 induction n; intros [|p l]; simpl; auto.
 - inversion 1.
 - intros LE. apply Nat.succ_le_mono in LE.
   assert (Hl := IHn l LE).
   assert (L := renorm_loop_length k l LE).
   destruct renorm_loop as [|p' l']; simpl in *; try lia.
   case Nat.eqb_spec; simpl in *; intros; try lia.
   rewrite IHn by (simpl;lia). simpl.
   replace (p'-(k-1)) with p; lia.
Qed.

Lemma renorm_sum k l : sumA k (renorm k l) = sumA k l.
Proof.
 unfold renorm. now apply renorm_loop_sum.
Qed.
#[global] Hint Resolve renorm_sum : hof.

Definition HeadStep k l l' := match l, l' with
| [], [] => True
| p::_, p'::_ => exists m, p' = p + m*k
| _, _ => False
end.

Lemma renorm_loop_head k l n :
  k<>0 -> length l <= n -> HeadStep k l (renorm_loop k l n).
Proof.
 intros Hk.
 revert l.
 induction n; intros [|p l]; simpl; auto.
 - inversion 1.
 - intros LE. apply Nat.succ_le_mono in LE.
   assert (Hd := IHn l LE).
   assert (L := renorm_loop_length k l LE).
   destruct renorm_loop as [|p' l']; simpl in *.
   + now exists 0.
   + case Nat.eqb_spec; simpl in *; intros.
     * specialize (IHn (S p'::l')).
       destruct renorm_loop; simpl in *; try lia.
       destruct IHn as (m,E); try lia.
       exists (S m). simpl. lia.
     * exists 0; lia.
Qed.

Lemma renorm_head k l : k<>0 -> HeadStep k l (renorm k l).
Proof.
 intros. unfold renorm. now apply renorm_loop_head.
Qed.

Lemma renorm_0 l : renorm 0 l = renorm 1 l.
Proof.
 revert l.
 assert (forall n l, length l <= n -> renorm_loop 0 l n = renorm_loop 1 l n).
 { induction n; intros l Hl; simpl; trivial.
   destruct l as [|p l]; trivial. simpl in *. rewrite IHn by lia.
   destruct renorm_loop eqn:E; trivial. destruct Nat.eqb; trivial.
   apply IHn; simpl. generalize (@renorm_loop_length 1 l n). rewrite E.
   simpl. lia. }
 unfold renorm. intros. now apply H.
Qed.

Lemma renorm_loop_delta k l n :
  k<>0 -> length l <= n -> Delta (k-1) l -> Delta k (renorm_loop k l n).
Proof.
 intros Hk.
 revert l.
 induction n; intros [|p l] LE D; simpl in *; autoh.
 apply Nat.succ_le_mono in LE.
 apply Delta_alt in D. destruct D as (D,IN).
 assert (D' := IHn l LE D).
 assert (LE' := renorm_loop_length k l LE).
 assert (Hd := @renorm_loop_head k l _ Hk LE).
 destruct renorm_loop as [|p' l']; simpl in *; autoh.
 case Nat.eqb_spec; simpl in *; intros.
 - apply IHn; simpl; autoh. apply Delta_S_cons. now fixpred.
 - destruct l as [|x l]; simpl in *; [intuition|].
   destruct Hd as (m,Hd).
   constructor; auto.
   assert (p+(k-1) <= x). { apply IN; auto. }
   lia.
Qed.

Lemma renorm_delta k l : Delta (k-1) l -> Delta k (renorm k l).
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - simpl. rewrite renorm_0. intros D.
   apply Delta_S, renorm_loop_delta; trivial; lia.
 - intros. unfold renorm. now apply renorm_loop_delta.
Qed.
#[global] Hint Resolve renorm_delta : hof.

Lemma renorm_nop k l : k<>0 -> Delta k l -> renorm k l = l.
Proof.
 intros.
 rewrite <- (@decomp_carac k (sumA k l) (renorm k l)); auto with hof.
 apply renorm_delta; trivial. apply Delta_S. now fixpred.
Qed.

Lemma renorm_le k x l : k<>0 -> Delta (k-1) (x::l) ->
  forall y, In y (renorm k (x::l)) -> x <= y.
Proof.
 intros K D y Hy.
 apply renorm_delta in D; trivial.
 assert (Hd := @renorm_head k (x::l) K).
 destruct renorm as [|p l']; try easy.
 destruct Hd as (m,Hd).
 transitivity p.
 - subst; auto with arith.
 - apply Delta_alt in D.
   simpl in Hy. destruct Hy as [->|Hy]; auto.
   destruct D as (_,IN'). specialize (IN' y Hy). lia.
Qed.

Lemma renorm_loop_mapS k l n :
 map S (renorm_loop k l n) = renorm_loop k (map S l) n.
Proof.
 revert l.
 induction n; trivial; intros [|p l]; trivial.
 simpl in *.
 rewrite <- IHn.
 destruct (renorm_loop k l n) eqn:E; simpl; trivial.
 case Nat.eqb_spec; intros. apply IHn. trivial.
Qed.

Lemma renorm_mapS k l : map S (renorm k l) = renorm k (map S l).
Proof.
 unfold renorm. rewrite map_length. apply renorm_loop_mapS.
Qed.

Lemma renorm_loop_mapdecr k m l n : m < k -> length l <= n ->
  sumA k (map (decr m) (renorm_loop k l n)) =
  sumA k (map (decr m) l).
Proof.
 intros Hm.
 revert l.
 induction n; intros [|p l] LE; simpl in *; auto.
 - inversion LE.
 - apply Nat.succ_le_mono in LE.
   rewrite <- (IHn l LE).
   assert (LE' := renorm_loop_length k l LE).
   assert (Hd := @renorm_loop_head k l _ ltac:(lia) LE).
   destruct renorm_loop as [|p' l']; simpl in *; auto.
   case Nat.eqb_spec; simpl in *; intros; auto.
   rewrite IHn by (simpl; lia).
   subst p'. rewrite <- Nat.add_succ_r. fixpred. simpl.
   rewrite Nat.add_assoc. f_equal.
   unfold decr.
   rewrite A_sum by lia.
   rewrite Nat.add_comm. f_equal; f_equal; lia.
Qed.

Lemma renorm_mapdecr k m l : m < k ->
  sumA k (map (decr m) (renorm k l)) = sumA k (map (decr m) l).
Proof.
 unfold renorm. intros. now apply renorm_loop_mapdecr.
Qed.

Definition LeHd m l :=
  match l with [] => True | a::_ => m <= a end.

Lemma renorm_loop_mapdecr' k m l n :
  k<>0 ->
  length l <= n ->
  Delta (k-1) l ->
  LeHd (m-(k-1)) l ->
  sumA k (map (decr m) (renorm_loop k l n)) =
  sumA k (map (decr m) l).
Proof.
 intros Hk.
 revert l.
 induction n; intros [|a l] LE D H; simpl in *; try lia.
 apply Nat.succ_le_mono in LE.
 apply Delta_alt in D. destruct D as (D,IN).
 assert (LH : LeHd (m-(k-1)) l).
 { destruct l as [|x l]; simpl in *; trivial.
   assert (a+(k-1) <= x) by auto. lia. }
 rewrite <- (IHn l LE D LH).
 assert (LE' := renorm_loop_length k l LE).
 assert (Hd := @renorm_loop_head k l _ Hk LE).
 assert (D' := @renorm_loop_delta k l n Hk LE D).
 destruct renorm_loop as [|p' l']; simpl in *; auto.
 case Nat.eqb_spec; simpl in *; intros; auto.
 rewrite IHn; autoh; try (simpl; lia).
 2:{ apply Delta_S_cons. now fixpred. }
 subst p'. rewrite <- Nat.add_succ_r. simpl.
 rewrite Nat.add_assoc. f_equal.
 unfold decr.
 rewrite A_sum by lia.
 rewrite Nat.add_comm. f_equal; f_equal; lia.
Qed.

Lemma renorm_mapdecr' k m l :
  k<>0 -> Delta (k-1) l -> LeHd (m-(k-1)) l ->
  sumA k (map (decr m) (renorm k l)) = sumA k (map (decr m) l).
Proof.
 unfold renorm. intros. now apply renorm_loop_mapdecr'.
Qed.

Lemma renorm_low k l : k<>0 -> Delta k (k-1 :: l) ->
  renorm k (0 :: k-1 :: l) = renorm k (k :: l).
Proof.
 intros K D. transitivity (decomp k (sumA k (0::k-1::l))).
 - symmetry. apply decomp_carac; trivial.
   + apply renorm_delta; trivial. constructor. lia.
     apply Delta_S. now fixpred.
   + now rewrite renorm_sum.
 - apply decomp_carac; trivial.
   + apply renorm_delta; trivial.
     replace k with (S (k-1)) at 2 by lia.
     replace k with (S (k-1)) in D at 1 by lia. now apply Delta_S_cons.
   + rewrite renorm_sum. simpl. rewrite !A_base; lia.
Qed.

(** Below, [renormS k a l] is a simplified version of [renorm k (S a :: l)].
    Indeed, when a decomposition starts by one lax gap and is strict
    afterwards, no need for the full renorm, a single
    bottom-up pass is enough. This particular situation is used
    in next_decomp below. *)

Fixpoint renormS k a l :=
  match l with
  | [] => [S a]
  | b::l' => if b =? a+k then renormS k b l' else S a :: l
  end.

Lemma renormS_sum k a l : k<>0 -> sumA k (renormS k a l) = sumA k (S a :: l).
Proof.
 intros Hk.
 revert a. induction l as [|b l IH]; intros a; simpl; auto.
 case Nat.eqb_spec; simpl; intros H; auto.
 rewrite IH. simpl. replace (b-(k-1)) with (S a); simpl; lia.
Qed.

Lemma renormS_delta k a l :
  Delta k (a::l) -> Delta k (renormS k a l).
Proof.
 revert a. induction l as [|b l IH]; intros a; simpl; auto.
 - intros. constructor.
 - inversion 1; subst.
   case Nat.eqb_spec; simpl; intros E; auto.
   constructor; auto. lia.
Qed.

Lemma renormS_alt k a l : k<>0 -> Delta k (a::l) ->
  renormS k a l = renorm k (S a :: l).
Proof.
 intros K D. eapply decomp_unique; eauto using renormS_delta.
 - apply renorm_delta; auto with hof. apply Delta_S_cons. now fixpred.
 - now rewrite renormS_sum, renorm_sum.
Qed.

Lemma renormS_head k a l : HeadStep k (S a :: l) (renormS k a l).
Proof.
 revert a. induction l as [|b l IH]; simpl.
 - exists 0; lia.
 - intros a. case Nat.eqb_spec; intros H.
   + specialize (IH b). destruct renormS; simpl in *; trivial.
     destruct IH as (m & ->). exists (S m). simpl; lia.
   + exists 0; lia.
Qed.

(** ** Decomposition of the next number *)

Definition next_decomp k l :=
  match l with
  | [] => [0]
  | a :: l' =>
    if a <? k then
      renormS k a l'  (* same here as renorm k (S a :: l') *)
    else
      0::l
  end.

Lemma next_decomp_sum k l : sumA k (next_decomp k l) = S (sumA k l).
Proof.
 destruct l; simpl; trivial.
 case Nat.ltb_spec; intros; rewrite ?renormS_sum; simpl; trivial; try lia.
 replace (n-(k-1)) with 0; simpl; lia.
Qed.

Lemma next_decomp_delta k l : Delta k l -> Delta k (next_decomp k l).
Proof.
 destruct l; simpl; autoh.
 case Nat.ltb_spec; intros. now apply renormS_delta.
 constructor. lia. trivial.
Qed.

Lemma decomp_S k n : k<>0 -> decomp k (S n) = next_decomp k (decomp k n).
Proof.
 intros. apply decomp_carac; trivial.
 - apply next_decomp_delta, decomp_delta.
 - now rewrite next_decomp_sum, decomp_sum.
Qed.


(** ** Classification of decompositions *)

(** The q-rank of a number is the least index in its q-decomposition. *)

Definition rank k n :=
  match decomp k n with
  | [] => None
  | p :: _ => Some p
  end.

Definition Rank k n r :=
 exists l, n = sumA k (r::l) /\ Delta k (r::l).

Lemma rank_Rank k n r :
 k<>0 -> rank k n = Some r <-> Rank k n r.
Proof.
 split.
 - unfold rank.
   destruct (decomp k n) eqn:E.
   + discriminate.
   + injection 1 as ->.
     exists l. rewrite <- E; autoh.
 - intros (l & E & D).
   unfold rank.
   rewrite decomp_carac with (l:=r::l); auto.
Qed.

Lemma rank_none k n : rank k n = None <-> n = 0.
Proof.
 split.
 - unfold rank. destruct decomp eqn:H.
   + now rewrite <- (decomp_sum k n), H.
   + discriminate.
 - now intros ->.
Qed.

Lemma rank_next_0 k n r : k<>0 -> rank k n = Some r -> k < r ->
 rank k (S n) = Some 0.
Proof.
 unfold rank.
 intros Hk Hr.
 rewrite decomp_S; trivial.
 destruct decomp as [|r' l]; try discriminate.
 injection Hr as ->. simpl.
 case Nat.ltb_spec; auto. lia.
Qed.

Lemma rank_next_high k n r : rank k n = Some r -> r < k ->
 exists m, rank k (S n) = Some (S r + m*k).
Proof.
 unfold rank.
 intros Hr LT.
 rewrite decomp_S by lia.
 destruct decomp as [|r' l]; try discriminate.
 injection Hr as ->. simpl.
 rewrite <- Nat.ltb_lt in LT. rewrite LT.
 assert (R := renormS_head k r l).
 destruct renormS as [|r' l']; simpl in *; intuition.
 destruct R as (m, Hm).
 exists m. now f_equal.
Qed.

Lemma rank_next_high' k n r : rank k n = Some r -> r < k ->
 exists r', rank k (S n) = Some r' /\ r < r'.
Proof.
 intros H H'.
 destruct (rank_next_high _ H H') as (m & Hm).
 exists (S r + m * k); auto with arith.
Qed.

Lemma rank_next k n r : k<>0 -> rank k n = Some r ->
 rank k (S n) = Some 0 \/
 exists m, rank k (S n) = Some (S r + m*k).
Proof.
 unfold rank.
 intros Hk Hr.
 rewrite decomp_S; trivial.
 destruct decomp as [|r' l]; try discriminate.
 injection Hr as ->. simpl.
 case Nat.ltb_spec; auto. intros LE.
 assert (R := renormS_head k r l).
 destruct renormS as [|r' l']; simpl in *; intuition.
 destruct R as (m, Hm).
 right. exists m. now f_equal.
Qed.

Lemma rank_next' k n r : k<>0 -> rank k n = Some r ->
 exists r', rank k (S n) = Some r' /\ (r' = 0 \/ r < r').
Proof.
 intros Hk Hr. apply rank_next in Hr; trivial.
 destruct Hr as [Hr|(m,Hr)].
 - exists 0; intuition.
 - exists (S r + m * k); split; auto. right. auto with arith.
Qed.

Lemma ranks_next k n r p : k<>0 -> rank k n = Some r ->
 (exists a, a<=p /\ rank k (a+n) = Some 0) \/
 (exists r', rank k (p+n) = Some r' /\ p+r <= r').
Proof.
 intros Hk.
 revert n r.
 induction p as [|p IH].
 - right. exists r; auto.
 - intros n r Hn.
   destruct (@rank_next' k n _ Hk Hn) as (r' & Hr & [->|LT]).
   + left. exists 1; auto with arith.
   + destruct (IH (S n) r' Hr) as [(a & Ha & H)|(r'' & H & Hr'')];
     rewrite Nat.add_succ_r in H.
     * left. exists (S a); auto with arith.
     * right. exists r''. split; auto; lia.
Qed.

Lemma rank_later_is_high k n r p : k<>0 -> p <= k ->
 rank k n = Some r ->
 exists r', exists a, a <= p /\ rank k (a+n) = Some r' /\ p <= r'.
Proof.
 intros Hk.
 revert n r.
 induction p as [|p IH]; intros n r Hp Hr.
 - exists r, 0. auto with arith.
 - destruct (IH n r) as (r' & a & H1 & H2 & H3); auto; try lia.
   destruct (Nat.ltb_spec r' k) as [LE|LT].
   destruct (rank_next_high' _ H2 LE) as (r'' & Hr'' & LT').
   + exists r''. exists (S a). repeat split; auto with arith.
     lia.
   + exists r'. exists a. repeat split; auto with arith. lia.
Qed.

Lemma rank_later_is_zero k n : k<>0 ->
 exists p, p <= k /\ rank k (p+n) = Some 0.
Proof.
 intros Hk.
 destruct (rank k n) as [r|] eqn:Hr.
 - destruct r as [|r].
   + exists 0; auto with arith.
   + destruct (ranks_next n (k-1) Hk Hr) as [(a & Hq & H)|(r' & H & LT)].
     * exists a; auto. split;trivial. lia.
     * clear Hr.
       exists k. split; auto.
       replace (k+n) with (S (k-1+n)) by lia.
       unfold rank in *.
       rewrite decomp_S by trivial.
       destruct (decomp k (k-1+n)) as [|r'' l]; auto.
       injection H as ->; simpl.
       case Nat.ltb_spec; auto; lia.
 - rewrite rank_none in *. subst. exists 1. split. lia. reflexivity.
Qed.


(** ** Decomposition of the predecessor of a Ak number

   [(A k n) - 1 = A k (n-1) + A k (n-1-k) + ... + A k (n-1-p*k)]

   with [p] such that [n-1-p*k] is in [0..k-1].
   i.e. [p = (n-1)/k]
*)

Fixpoint decompred k n :=
 match n with
 | 0 => []
 | S n => decompred k (n-(k-1)) ++ [n]
 end.

Lemma decompred_sum k n : sumA k (decompred k n) = A k n - 1.
Proof.
 induction n as [[|n] IH] using lt_wf_rec; trivial.
 simpl. rewrite sumA_app. simpl. rewrite IH by lia.
 generalize (A_nz k (n-(k-1))); lia.
Qed.

Lemma decompred_below k n : Below (decompred k n) n.
Proof.
 induction n as [[|n] IH] using lt_wf_rec; simpl; try easy.
 intros y. rewrite in_app_iff. intros [IN|[<-|[ ]]]; try lia.
 apply IH in IN; lia.
Qed.

Lemma decompred_delta k n : Delta k (decompred k n).
Proof.
 induction n as [[|n] IH] using lt_wf_rec; autoh.
 simpl. destruct (Nat.le_gt_cases n (k-1)).
 - replace (n-(k-1)) with 0 by lia. simpl. constructor.
 - apply Delta_app with (n-k).
   + apply IH; lia.
   + constructor. lia. autoh.
   + intros y IN. apply decompred_below in IN. lia.
Qed.

(** Decomposition of the previous number *)

Definition prev_decomp k l :=
 match l with
 | [] => []
 | x::l => decompred k x ++ l
 end.

Lemma prev_decomp_sum k l : sumA k (prev_decomp k l) = sumA k l - 1.
Proof.
 destruct l as [|x l]; simpl; trivial. rewrite sumA_app, decompred_sum.
 generalize (A_nz k x). lia.
Qed.

Lemma prev_decomp_below k l N : Below l N -> Below (prev_decomp k l) N.
Proof.
 destruct l as [|x l]; simpl; trivial.
 intros B y. rewrite in_app_iff. intros [IN|IN].
 - apply decompred_below in IN. specialize (B x). simpl in B. lia.
 - apply B. now right.
Qed.

Lemma prev_decomp_delta k l : Delta k l -> Delta k (prev_decomp k l).
Proof.
 destruct l as [|x l]; simpl; trivial. intros D.
 apply Delta_app with x; eauto using Delta_more, decompred_delta.
 intros y IN. apply decompred_below in IN. lia.
Qed.

Lemma prev_decomp_delta_lax k l :
 Delta (k-1) l -> Delta (k-1) (prev_decomp k l).
Proof.
 destruct l as [|x l]; simpl; trivial. intros D.
 apply Delta_app with x; trivial.
 - apply Delta_more with k. lia. apply decompred_delta.
 - intros y IN. apply decompred_below in IN. lia.
Qed.

Lemma decomp_pred k n : k<>0 -> decomp k (n-1) = prev_decomp k (decomp k n).
Proof.
 intros. apply decomp_carac; trivial.
 - apply prev_decomp_delta, decomp_delta.
 - now rewrite prev_decomp_sum, decomp_sum.
Qed.

Lemma rank_pred k n r : k<>0 ->
  rank k n = Some r -> r <> 0 ->
  rank k (n-1) = Some ((r-1) mod k).
Proof.
 intros Hk.
 unfold rank.
 set (l := decomp k n).
 rewrite <- (decomp_sum k n). fold l.
 rewrite <- prev_decomp_sum, decomp_sum'; trivial.
 2:apply prev_decomp_delta, decomp_delta.
 destruct l as [|a l]; try easy.
 intros [= <-] Ha. clear n. cbn -[Nat.modulo].
 revert Ha l.
 induction a as [[|a] IH] using lt_wf_ind.
 - now destruct 1.
 - intros _ l. cbn -[Nat.modulo].
   destruct (Nat.eq_dec (a-(k-1)) 0) as [E|NE].
   + rewrite E. cbn -[Nat.modulo]. f_equal. rewrite Nat.sub_0_r.
     rewrite Nat.mod_small; auto. lia.
   + rewrite <- app_assoc, IH; try lia.
     f_equal. rewrite Nat.sub_0_r.
     rewrite <- (@Nat.mod_add (a-(k-1)-1) 1 k); auto. f_equal. lia.
Qed.

(** We can decrease a decomposition by iterating [prev_decomp].
    Note: the highest term of the decomposition will not grow. *)

Fixpoint decompminus k l p :=
  match p with
  | 0 => l
  | S p => decompminus k (prev_decomp k l) p
  end.

Lemma decompminus_sum k l p : sumA k (decompminus k l p) = sumA k l - p.
Proof.
 revert l. induction p as [|p IH]; intros l; simpl; try lia.
 rewrite IH, prev_decomp_sum. lia.
Qed.

Lemma decompminus_below k l p N : Below l N -> Below (decompminus k l p) N.
Proof.
 revert l. induction p as [|p IH]; intros l Hl; simpl; auto.
 now apply IH, prev_decomp_below.
Qed.

Lemma decompminus_delta k l p :
 Delta k l -> Delta k (decompminus k l p).
Proof.
 revert l. induction p as [|p IH]; intros l Hl; simpl; auto.
 now apply IH, prev_decomp_delta.
Qed.

Lemma decompminus_delta_lax k l p : k<>0 ->
 Delta (k-1) l -> Delta (k-1) (decompminus k l p).
Proof.
 intros Hk. revert l. induction p as [|p IH]; intros l Hl; simpl; auto.
 now apply IH, prev_decomp_delta_lax.
Qed.

Lemma decompminus_app_delta k l l' p : k<>0 ->
  Delta (k-1) (l++l') -> Delta (k-1) (decompminus k l p ++ l').
Proof.
 intros Hk.
 rewrite !Delta_app_iff. intros (D1 & D2 & D3).
 repeat split; auto using decompminus_delta_lax.
 intros x x' IN IN'.
 assert (B : Below l (S x'-(k-1))).
 { intros y Hy. specialize (D3 y x' Hy IN'). lia. }
 apply (@decompminus_below k l p) in B.
 specialize (B _ IN). lia.
Qed.

(** [decomp] can be used to generate all the subsets of [{0..p-1}]
    whose elements are at distance of at least k. *)

Definition enum_sparse_subsets k p := map (decomp k) (seq 0 (A k p)).

Lemma decomp_max' k p l :
  k<>0 -> Delta k l -> Below l p -> sumA k l < A k p.
Proof.
 intros K D B.
 rewrite <- DeltaRev_rev in D.
 assert (B' : Below (rev l) p). { intros y. rewrite <- in_rev. apply B. }
 clear B.
 rewrite <- sumA_rev.
 destruct (rev l) as [|n l'].
 - apply A_nz.
 - apply Nat.lt_le_trans with (A k (S n)).
   + now apply decomp_max.
   + apply A_mono. apply B'. now left.
Qed.

Lemma enum_sparse_subsets_ok k p l :
  k<>0 -> In l (enum_sparse_subsets k p) <-> Below l p /\ Delta k l.
Proof.
 intros Hk.
 unfold enum_sparse_subsets.
 rewrite in_map_iff. setoid_rewrite in_seq.
 split.
 - intros (n & Hl & (_,Hn)). simpl in Hn. split.
   + intros x Hx. subst l.
     apply decomp_in in Hx. apply (@A_lt_inv k). lia.
   + subst l. apply decomp_delta.
 - intros (Hl,D). exists (sumA k l). split.
   + now apply decomp_sum'.
   + split; [lia|]. apply decomp_max'; trivial.
Qed.

Lemma enum_sparse_subsets_nodup k p : NoDup (enum_sparse_subsets k p).
Proof.
 apply FinFun.Injective_map_NoDup; [|apply seq_NoDup].
 intros x y E.
 now rewrite <- (@decomp_sum k x), E, decomp_sum.
Qed.
