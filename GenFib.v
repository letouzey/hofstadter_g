(** * Fib : Fibonacci sequence and decomposition *)

Require Import MoreList DeltaList.
Import ListNotations.
Set Implicit Arguments.

(** * Generalized Fibonacci sequence *)

Fixpoint A (q n : nat) :=
  match n with
  | O => 1
  | S n => A q n + A q (n-q)
  end.

(**
 - q=0 : binary numbers
 - q=1 : Fibonacci numbers (non-standard indexes)
         1 2 3 5 8 ...
 - q=2 : Narayana’s Cows, see OEIS A930 (shifted)
 - q=3 : See OEIS A003269 (shifted)
*)

(*
Compute take 10 (A 0).
Compute take 10 (A 1).
Compute take 10 (A 2).
Compute take 10 (A 3).
*)
(*
A 0 : [1; 2; 4; 8; 16; 32; 64; 128; 256; 512]
A 1 : [1; 2; 3; 5; 8; 13; 21; 34; 55; 89]
A 2 : [1; 2; 3; 4; 6; 9; 13; 19; 28; 41]
A 3 : [1; 2; 3; 4; 5; 7; 10; 14; 19; 26]
*)

Lemma A_q_0 q : A q 0 = 1.
Proof.
 reflexivity.
Qed.

Lemma A_S q n : A q (S n) = A q n + A q (n-q).
Proof.
 reflexivity.
Qed.

Lemma A_base q n : n <= S q -> A q n = S n.
Proof.
 induction n; auto.
 simpl. intros.
 replace (n-q) with 0 by lia. simpl.
 rewrite IHn; lia.
Qed.

Lemma S_sub_1 p : S p - 1 = p.
Proof.
 lia.
Qed.

Lemma A_sum q n : n<>0 -> A q n = A q (n-1) + A q (n-S q).
Proof.
 destruct n.
 - now destruct 1.
 - intros _. now rewrite S_sub_1.
Qed.

Lemma A_sum' q n : A q (n+S q) = A q n + A q (n+q).
Proof.
 intros.
 rewrite A_sum by lia.
 rewrite Nat.add_comm. f_equal; f_equal; lia.
Qed.

Lemma A_q_1 q : A q 1 = 2.
Proof.
 reflexivity.
Qed.

Lemma A_0_pow2 n : A 0 n = 2^n.
Proof.
 induction n.
 - reflexivity.
 - rewrite A_S, Nat.sub_0_r. simpl. lia.
Qed.

Lemma A_nz q n : 1 <= A q n.
Proof.
 induction n; simpl; auto with arith.
Qed.

Lemma A_lt_S q n : A q n < A q (S n).
Proof.
 simpl. generalize (A_nz q (n-q)). lia.
Qed.

Lemma A_lt q n n' : n < n' -> A q n < A q n'.
Proof.
 induction 1.
 - apply A_lt_S.
 - transitivity (A q m); trivial. apply A_lt_S.
Qed.

Lemma A_mono q n n' : n <= n' -> A q n <= A q n'.
Proof.
 induction 1; trivial.
 transitivity (A q m); trivial. apply Nat.lt_le_incl, A_lt_S.
Qed.

Lemma A_S_le_twice q n : A q (S n) <= 2 * A q n.
Proof.
 rewrite A_S. simpl. generalize (@A_mono q (n-q) n). lia.
Qed.

Lemma A_inj q n n' : A q n = A q n' -> n = n'.
Proof.
 intros.
 destruct (lt_eq_lt_dec n n') as [[LT|EQ]|LT]; trivial;
  apply (A_lt q) in LT; lia.
Qed.

Lemma A_lt_inv q n n' : A q n < A q n' -> n < n'.
Proof.
 intros.
 destruct (le_lt_dec n' n) as [LE|LT]; trivial.
 apply (A_mono q) in LE. lia.
Qed.

Lemma A_le_inv q x y : A q x <= A q y -> x <= y.
Proof.
 rewrite Nat.lt_eq_cases. intros [LT|EQ].
 - apply A_lt_inv in LT. lia.
 - apply A_inj in EQ. lia.
Qed.

Lemma A_lt_id q n : n < A q n.
Proof.
 induction n; simpl; auto.
 generalize (A_nz q (n-q)). lia.
Qed.

Lemma A_base_iff q n : n <= S q <-> A q n = S n.
Proof.
 split. apply A_base.
 intros.
 destruct n; auto with arith.
 rewrite A_S in H.
 generalize (A_lt_id q n).
 generalize (A_lt_id q (n-q)).
 lia.
Qed.

Lemma A_high q n : S q < n <-> S n < A q n.
Proof.
 generalize (A_base_iff q n) (A_lt_id q n). lia.
Qed.

Lemma A_Sq_le q n : A (S q) n <= A q n.
Proof.
 induction n as [[|n] IH] using lt_wf_ind; auto.
 rewrite !A_S.
 transitivity (A q n + A q (n - S q)).
 - apply Nat.add_le_mono; apply IH; lia.
 - apply Nat.add_le_mono; auto. apply A_mono. lia.
Qed.

Lemma A_Sq_lt q n : S q < n -> A (S q) n < A q n.
Proof.
 intros LT.
 replace n with (q + 2 + (n - q - 2)) by lia.
 set (m := n - q - 2). clearbody m. clear LT n.
 induction m.
 - rewrite Nat.add_0_r.
   rewrite A_base by lia.
   rewrite Nat.add_succ_r.
   rewrite A_S.
   rewrite A_base by lia.
   replace (q+1-q) with 1 by lia. rewrite A_q_1. lia.
 - rewrite Nat.add_succ_r.
   rewrite !A_S.
   apply Nat.add_lt_le_mono; auto. clear IHm.
   replace (q + 2 + m - S q) with (S m) by lia.
   replace (q + 2 + m - q) with (S (S m)) by lia.
   transitivity (A q (S m)). apply A_Sq_le. apply A_mono; lia.
Qed.

(* (A q) is sub-multiplicative

   Note : Thanks to Fekete theorem, this implies that
   [(ln (A q n))/n] has a finite limit when n grows. But without
   extra details about the next term in the asymptotic development,
   we cannot say much more this way, especially nothing on the limit
   of the ratio [A q (S n) / A q n] or even its existence.
*)

Lemma A_submult q p n : A q (n+p) <= A q n * A q p.
Proof.
 induction n as [[|n] IH] using lt_wf_ind.
 - cbn. lia.
 - destruct (Nat.le_gt_cases q n).
   + cbn.
     assert (IHn := IH n).
     assert (IHnq := IH (n-q)).
     replace (n-q+p) with (n+p-q) in IHnq; lia.
   + rewrite (@A_base q (S n)) by lia.
     (* apply A_shift_mult. lia. *)
     cbn - ["*"].
     assert (IHn := IH n).
     rewrite (@A_base q n) in IHn by lia.
     assert (LE : n + p - q <= p) by lia.
     apply (A_mono q) in LE. lia.
Qed.

(* After the "base" zone, a "triangular" zone *)

Definition triangle q := q*(q+1)/2.

Lemma qSq_even q : q*(q+1) mod 2 = 0.
Proof.
 destruct (Nat.Even_or_Odd q) as [(l,->)|(l,->)].
 - rewrite <- Nat.mul_assoc, Nat.mul_comm.
   apply Nat.mod_mul; auto.
 - replace (2*l+1+1) with (2*(l+1)) by lia.
   rewrite (Nat.mul_comm 2 (l+1)), Nat.mul_assoc.
   apply Nat.mod_mul; auto.
Qed.

Lemma double_triangle q : 2 * triangle q = q*(q+1).
Proof.
 rewrite (Nat.div_mod (q * (q+1)) 2); auto. now rewrite qSq_even.
Qed.

Lemma triangle_succ q : triangle (S q) = triangle q + S q.
Proof.
 apply Nat.mul_cancel_l with 2; auto.
 rewrite Nat.mul_add_distr_l.
 rewrite !double_triangle. lia.
Qed.

Lemma triangle_aboveid q : q <= triangle q.
Proof.
 induction q; auto. rewrite triangle_succ. lia.
Qed.

Lemma A_triangle q n : n <= q+2 -> A q (q + n) = S q + triangle n.
Proof.
 induction n.
 - intros _. rewrite A_base by lia. reflexivity.
 - intros LE.
   rewrite Nat.add_succ_r, A_S.
   replace (q + n - q) with n by lia.
   rewrite (@A_base q n) by lia.
   rewrite triangle_succ.
   rewrite IHn; lia.
Qed.

(* Just after the triangular zone : *)

Lemma A_2q3_eqn q : A q (2*q+3) = A q (2*q+2) + A q (S q) + 2.
Proof.
 rewrite Nat.add_succ_r, A_S.
 rewrite <- Nat.add_assoc. f_equal.
 replace (2*q+2-q) with (S (S q)) by lia.
 rewrite A_S. f_equal.
 replace (S q - q) with 1 by lia.
 apply A_q_1.
Qed.

Lemma A_2q3_tri q : A q (2*q+3) = triangle (q+4) - 2.
Proof.
 rewrite A_2q3_eqn.
 replace (2*q+2) with (q+S (S q)) by lia.
 rewrite A_triangle, A_base by lia.
 replace (q+4) with (S (S (S (S q)))) by lia.
 rewrite (triangle_succ (S (S (S q)))).
 rewrite (triangle_succ (S (S q))). lia.
Qed.

(* Behavior of A diagonals :
   decreasing then flat at [n=2*q+3] then [+1] steps. *)

Lemma A_diag_eq q n : n = 2*q+3 -> A (S q) (S n) = A q n.
Proof.
 intros ->.
 replace (S (2*q + 3)) with (S q + S (q+2)) by lia.
 rewrite A_triangle by lia.
 rewrite A_2q3_tri.
 replace (q+4) with (S (S (q+2))) by lia.
 rewrite (triangle_succ (S (q+2))). lia.
Qed.

Lemma A_diag_step q n : n < 2*q+3 -> A (S q) (S n) = S (A q n).
Proof.
 induction n.
 - intros _. now rewrite A_q_1, A_q_0.
 - intros LT.
   rewrite A_S. simpl Nat.sub.
   rewrite IHn by lia. rewrite A_S. simpl. f_equal. f_equal.
   rewrite !A_base; lia.
Qed.

Lemma A_diag_decr q n : 2*q+3 < n -> A (S q) (S n) < A q n.
Proof.
 intros LT.
 replace n with (2*q+4+(n-2*q-4)) by lia.
 set (m := n-2*q-4). clearbody m. clear n LT.
 induction m.
 - rewrite !Nat.add_0_r.
   rewrite A_S. rewrite Nat.add_succ_r, A_diag_eq by lia.
   replace (S(2*q+3)-S q) with (q+3) by lia.
   rewrite A_S.
   replace (2*q+3-q) with (q+3) by lia.
   apply Nat.add_lt_mono_l.
   apply A_Sq_lt. lia.
 - rewrite Nat.add_succ_r, (A_S (S q)), (A_S q).
   apply Nat.add_lt_le_mono; auto using A_Sq_le.
Qed.

Lemma A_diag_decr_exact q n : 2*q+3 <= n <= 3*q+3 ->
  A q n = A (S q) (S n) + ((n-2*q-3)*(n-2*q))/2.
Proof.
 induction n as [n IH] using lt_wf_ind.
 intros Hn.
 destruct (Nat.eq_dec n (2*q+3)) as [E|N].
 - replace (n-2*q-3) with 0 by lia. simpl "/". now rewrite A_diag_eq.
 - replace n with (S (n-1)) at 1 by lia. simpl A.
   rewrite (IH (n-1)) by lia.
   replace (S (n-1)) with n by lia.
   rewrite <- !Nat.add_assoc. f_equal.
   replace (n-S q) with (S (n-q-2)) by lia.
   rewrite A_diag_step by lia.
   replace (n-1-q) with (S (n-q-2)) by lia.
   rewrite A_S. rewrite (@A_base q (n-q-2-q)) by lia.
   rewrite Nat.add_shuffle3. rewrite !Nat.add_succ_r, Nat.add_succ_l.
   f_equal. f_equal.
   set (m := n-1-2*q-3).
   replace (n-2*q-3) with (m+1) by lia.
   replace (n-q-2-q) with (m+2) by lia.
   replace (n-1-2*q) with (m+3) by lia.
   replace (n-2*q) with (m+4) by lia.
   replace ((m+1)*(m+4)) with (m*(m+3)+(m+2)*2) by ring.
   rewrite Nat.div_add; lia.
Qed.

(* Inverting A *)

Fixpoint invA q n :=
  match n with
  | 0 => 0
  | S n =>
    let p := invA q n in
    if S (S n) =? A q (S p) then S p else p
  end.

Lemma invA_spec q n : A q (invA q n) <= S n < A q (S (invA q n)).
Proof.
 induction n as [|n IH].
 - simpl. auto.
 - cbn -[A Nat.eqb].
   case Nat.eqb_spec; [intros E|intros; lia].
   split. lia. rewrite E. apply A_lt_S.
Qed.

Lemma invA_spec' q n p : A q p <= S n < A q (S p) -> invA q n = p.
Proof.
 intros H.
 assert (H' := invA_spec q n).
 assert (p < S (invA q n)) by (apply (A_lt_inv q); lia).
 assert (invA q n < S p) by (apply (A_lt_inv q); lia).
 lia.
Qed.

Lemma A_inv q n : { p | A q p <= S n < A q (S p) }.
Proof.
 exists (invA q n). apply invA_spec.
Defined.

Lemma A_inv' q n : n<>0 -> { p | A q p <= n < A q (S p) }.
Proof.
 destruct n.
 - now destruct 1.
 - intros _. apply A_inv.
Defined.

Lemma invA_A q p : invA q (A q p - 1) = p.
Proof.
 apply invA_spec'.
 replace (S (A q p -1)) with (A q p) by (generalize (A_nz q p); lia).
 split; auto. apply A_lt. lia.
Qed.

Lemma invA_A' q p : p<>0 -> invA q (A q p - 2) = p-1.
Proof.
 intros Hq.
 apply invA_spec'.
 assert (2 <= A q p) by (apply (@A_mono q 1 p); lia).
 replace (S (A q p - 2)) with (A q p - 1) by lia.
 replace (S (p-1)) with p by lia.
 split; try lia.
 generalize (@A_lt q (p-1) p). lia.
Qed.

(** Any number has a [A] number above it. *)

Definition invA_up q n := S (invA q (n-2)).

Lemma invA_up_spec q n : n <= A q (invA_up q n).
Proof.
 unfold invA_up. destruct (invA_spec q (n-2)) as (_,H). lia.
Qed.

Lemma invA_up_A q n : n<>0 -> invA_up q (A q n) = n.
Proof.
 intros Hn. unfold invA_up. rewrite invA_A'; lia.
Qed.

(** * Decomposition via sums of Aq numbers.

    Zeckendorf's theorem (actually discovered earlier by
    Lekkerkerker) states that any natural number can be obtained
    by a sum of distinct Fibonacci numbers, and this decomposition
    is moreover unique when Fibonacci numbers in the decomposition
    aren't consecutive.

    This is the generalization to Aq numbers.
*)

(** ** The [sumA] function

   We represent a decomposition by the list of indexes
   of the Aq numbers in this decomposition.
   The sumA function is the sum of the Fibonacci numbers of
   these indexes. For the first results below, the indexes may be
   arbitrary : redundant, in any order, ... *)

Definition sumA q l := fold_right (fun n acc => A q n + acc) 0 l.

Lemma sumA_cons q a l : sumA q (a::l) = A q a + sumA q l.
Proof.
 reflexivity.
Qed.

Lemma sumA_eqn q l :
 sumA q l + sumA q (map (decr q) l) = sumA q (map S l).
Proof.
 induction l; trivial.
 simpl map. rewrite !sumA_cons, <- IHl, A_S.
 unfold decr at 1. lia.
Qed.

Lemma sumA_eqn' q l :
 sumA q (map S l) - sumA q (map (decr q) l) = sumA q l.
Proof.
 rewrite <- sumA_eqn. apply Nat.add_sub.
Qed.

Lemma sumA_eqn_pred q l :
 ~In 0 l ->
 sumA q l = sumA q (map (decr 1) l) + sumA q (map (decr (S q)) l).
Proof.
 induction l; trivial.
 simpl map. simpl. intros. rewrite IHl by intuition.
 unfold decr at 3 5.
 rewrite (@A_sum q a); lia.
Qed.

Lemma sumA_app q l l' : sumA q (l++l') = sumA q l + sumA q l'.
Proof.
 revert l'.
 induction l; intros.
 - trivial.
 - simpl. rewrite IHl. lia.
Qed.

Lemma sumA_rev q l : sumA q (rev l) = sumA q l.
Proof.
 induction l.
 - trivial.
 - simpl. rewrite sumA_app, IHl. simpl. lia.
Qed.

Lemma sumA_0 q l : sumA q l = 0 <-> l = [].
Proof.
 split.
 - intros H. destruct l; [ now elim H |].
   simpl in *. generalize (A_nz q n). lia.
 - intros; now subst.
Qed.

Lemma sumA_in_le q l x : In x l -> A q x <= sumA q l.
Proof.
 induction l; simpl.
 - inversion 1.
 - intros [<-|IN]; auto with arith.
   transitivity (sumA q l); auto with arith.
Qed.

(** ** Zeckendorf's Theorem *)

(** All numbers can be decomposed as a sum of A numbers.
    Existence of the decomposition is given by the [decomp] function below
    (small terms first). *)

Fixpoint decomp q n :=
 match n with
 | 0 => []
 | S n =>
   let p := invA q n in
   decomp q (n - (A q p - 1)) ++ [p]
 end.

Lemma decomp_sum q n :
 sumA q (decomp q n) = n.
Proof.
 induction n as [[|n] IH] using lt_wf_rec; trivial.
 cbn - [invA sumA].
 destruct (invA_spec q n) as (H,_).
 set (p := invA q n) in *.
 rewrite sumA_app. rewrite IH by lia. simpl.
 generalize (A_nz q p). lia.
Qed.

Lemma decomp_in q n x : In x (decomp q n) -> A q x <= n.
Proof.
 induction n as [[|n] IH] using lt_wf_rec; try easy.
 cbn - [invA sumA]. rewrite in_app_iff. intros [IN|[<-|[ ]]].
 apply IH in IN; lia.
 apply invA_spec.
Qed.

Lemma decomp_delta q n : Delta (S q) (decomp q n).
Proof.
 induction n as [[|n] IH] using lt_wf_rec; autoh.
 cbn - [invA sumA].
 destruct (invA_spec q n) as (H,H').
 set (p := invA q n) in *.
 apply Delta_app_iff; repeat split; autoh.
 - apply IH. lia.
 - intros x x' IN [<-|[ ]].
   apply decomp_in in IN.
   cut (x < p - q); [lia|].
   apply (A_lt_inv q).
   rewrite A_S in H'. lia.
Qed.
#[global] Hint Resolve decomp_sum decomp_delta : hof.

Lemma decomp_exists q n :
  { l | sumA q l = n /\ Delta (S q) l }.
Proof.
 exists (decomp q n). split. apply decomp_sum. apply decomp_delta.
Qed.

(** Technical lemma for uniqueness of decomposition :
    A canonical decomposition cannot excess the next Ak. *)

Lemma decomp_max q n l :
  DeltaRev (S q) (n::l) ->
    sumA q (n::l) < A q (S n).
Proof.
 revert n.
 induction l.
 - intros n _. simpl sumA. rewrite Nat.add_0_r. apply A_lt_S.
 - intros n.
   inversion 1; subst. simpl sumA.
   rewrite A_S.
   apply Nat.add_lt_mono_l.
   apply Nat.lt_le_trans with (A q (S a)).
   + apply IHl; auto.
   + apply A_mono; lia.
Qed.

Lemma rev_switch {A} (l l' : list A) : rev l = l' -> l = rev l'.
Proof.
 intros. now rewrite <- (rev_involutive l), H.
Qed.

Lemma sumA_below q l p : Delta (S q) l -> Below l p -> sumA q l < A q p.
Proof.
 intros D B.
 destruct (rev l) as [|a rl'] eqn:E''.
 - apply rev_switch in E''. subst l. simpl.
   generalize (@A_nz q p). lia.
 - rewrite <- sumA_rev, E''.
   apply Nat.lt_le_trans with (A q (S a)).
   + apply decomp_max. rewrite <- E''. now apply DeltaRev_rev.
   + apply A_mono. specialize (B a).
     rewrite in_rev, E'' in B. simpl in B. intuition.
Qed.

(** Uniqueness. Easier to prove on lists with large terms first. *)

Lemma decomp_unique_rev q l l' :
 DeltaRev (S q) l ->
 DeltaRev (S q) l' ->
 sumA q l = sumA q l' -> l = l'.
Proof.
 revert l'.
 induction l as [|n l IH]; destruct l' as [|n' l'].
 - trivial.
 - intros _ Hn'. simpl in *. generalize (A_nz q n'); lia.
 - intros Hn _. simpl in *. generalize (A_nz q n); lia.
 - intros DR DR' EQ.
   assert (n < S n').
   { apply (A_lt_inv q). simpl in EQ.
     apply Nat.le_lt_trans with (A q n' + sumA q l'); [lia|].
     now apply decomp_max. }
   assert (n' < S n).
   { apply (A_lt_inv q). simpl in EQ.
     apply Nat.le_lt_trans with (A q n + sumA q l); [lia|].
     now apply decomp_max. }
   replace n' with n in * by lia. clear H H0.
   simpl in EQ.
   f_equal.
   apply IH; clear IH; simpl in *; try lia; intuition.
   + apply DeltaRev_alt in DR. intuition.
   + apply DeltaRev_alt in DR'. intuition.
Qed.

Lemma decomp_unique q l l' :
 Delta (S q) l -> Delta (S q) l' -> sumA q l = sumA q l' -> l = l'.
Proof.
 intros D D' EQ.
 rewrite <- (rev_involutive l), <- (rev_involutive l'). f_equal.
 apply (@decomp_unique_rev q).
 - now apply DeltaRev_rev.
 - now apply DeltaRev_rev.
 - now rewrite !sumA_rev.
Qed.

Lemma decomp_carac q n l :
 Delta (S q) l -> sumA q l = n -> decomp q n = l.
Proof.
 intros D Eq. apply (@decomp_unique q); autoh.
 now rewrite decomp_sum.
Qed.
#[global] Hint Resolve decomp_carac : hof.

Lemma decomp_sum' q l :
 Delta (S q) l -> decomp q (sumA q l) = l.
Proof.
 intros D. now apply decomp_carac.
Qed.

Lemma decomp_low q n : 1 <= n <= q+2 -> decomp q n = [n-1].
Proof.
 intros.
 apply decomp_carac. constructor. cbn. rewrite A_base; lia.
Qed.

Lemma decomp_plus_A q n p :
  p < A q (n-q) -> decomp q (p + A q n) = decomp q p ++ [n].
Proof.
 intros LT.
 apply decomp_carac.
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
    of at least [k]), we can transform it into a canonical
    decomposition (with gaps of at least [S k]),
    by simply saturating the basic equation
    [A q n + A q (n-q) = A q (S n)]
    in the right order (highest terms first).

    Termination isn't obvious for Coq, since we might have
    to re-launch normalisation on by-products of a first
    normalisation. The number of terms in the decomposition
    decreases strictly during the process, we use that to
    justify the termination.

    Moreover, the lowest term in the decomposition grows by
    steps of [S k] during the process (or stays equal).
*)

Fixpoint renorm_loop q l n :=
 match n with
 | 0 => []
 | S n =>
   match l with
   | [] => []
   | p::l =>
     match renorm_loop q l n with
     | [] => [p]
     | p'::l' =>
       if p+q =? p' then
         renorm_loop q (S p' :: l') n
       else
         p::p'::l'
     end
   end
 end.

Definition renorm q l := renorm_loop q l (length l).

(*
Compute renorm 1 [0;1;3;4;5;7]. (* [4; 8] *)
Compute renorm 2 [1;3;5;8]. (* [1; 9] *)
*)

Lemma renorm_loop_length q l n :
  length l <= n -> length (renorm_loop q l n) <= length l.
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

Lemma renorm_length q l : length (renorm q l) <= length l.
Proof.
 unfold renorm. now apply renorm_loop_length.
Qed.
#[global] Hint Resolve renorm_length : hof.

Lemma renorm_loop_sum q l n :
  length l <= n -> sumA q (renorm_loop q l n) = sumA q l.
Proof.
 revert l.
 induction n; intros [|p l]; simpl; auto.
 - inversion 1.
 - intros LE. apply Nat.succ_le_mono in LE.
   assert (Hl := IHn l LE).
   assert (L := renorm_loop_length q l LE).
   destruct renorm_loop as [|p' l']; simpl in *; try lia.
   case Nat.eqb_spec; simpl in *; intros; try lia.
   rewrite IHn by (simpl;lia). simpl.
   replace (p'-q) with p; lia.
Qed.

Lemma renorm_sum q l : sumA q (renorm q l) = sumA q l.
Proof.
 unfold renorm. now apply renorm_loop_sum.
Qed.
#[global] Hint Resolve renorm_sum : hof.

Definition HeadStep q l l' := match l, l' with
| [], [] => True
| p::_, p'::_ => exists m, p' = p + m*(S q)
| _, _ => False
end.

Lemma renorm_loop_head q l n :
  length l <= n -> HeadStep q l (renorm_loop q l n).
Proof.
 revert l.
 induction n; intros [|p l]; simpl; auto.
 - inversion 1.
 - intros LE. apply Nat.succ_le_mono in LE.
   assert (Hd := IHn l LE).
   assert (L := renorm_loop_length q l LE).
   destruct renorm_loop as [|p' l']; simpl in *.
   + now exists 0.
   + case Nat.eqb_spec; simpl in *; intros.
     * specialize (IHn (S p'::l')).
       destruct renorm_loop; simpl in *; try lia.
       destruct IHn as (m,E); try lia.
       exists (S m). simpl. lia.
     * exists 0; lia.
Qed.

Lemma renorm_head q l : HeadStep q l (renorm q l).
Proof.
 unfold renorm. now apply renorm_loop_head.
Qed.

Lemma renorm_loop_delta q l n :
  length l <= n -> Delta q l -> Delta (S q) (renorm_loop q l n).
Proof.
 revert l.
 induction n; intros [|p l] LE D; simpl in *; autoh.
 apply Nat.succ_le_mono in LE.
 apply Delta_alt in D. destruct D as (D,IN).
 assert (D' := IHn l LE D).
 assert (LE' := renorm_loop_length q l LE).
 assert (Hd := renorm_loop_head q l LE).
 destruct renorm_loop as [|p' l']; simpl in *; autoh.
 case Nat.eqb_spec; simpl in *; intros.
 - apply IHn; simpl; autoh; lia.
 - destruct l as [|x l]; simpl in *; [intuition|].
   destruct Hd as (m,Hd).
   constructor; auto.
   assert (p+q <= x). { apply IN; auto. }
   lia.
Qed.

Lemma renorm_delta q l : Delta q l -> Delta (S q) (renorm q l).
Proof.
 unfold renorm. now apply renorm_loop_delta.
Qed.
#[global] Hint Resolve renorm_delta : hof.

Lemma renorm_nop q l : Delta (S q) l -> renorm q l = l.
Proof.
 intros.
 rewrite <- (@decomp_carac q (sumA q l) (renorm q l)); auto with hof.
Qed.

Lemma renorm_le q x l : Delta q (x::l) ->
  forall y, In y (renorm q (x::l)) -> x <= y.
Proof.
 intros D y Hy.
 apply renorm_delta in D.
 assert (Hd := renorm_head q (x::l)).
 destruct renorm as [|p l'].
 - elim Hy.
 - destruct Hd as (m,Hd).
   transitivity p.
   + subst; auto with arith.
   + apply Delta_alt in D.
     simpl in Hy. destruct Hy as [->|Hy]; auto.
     destruct D as (_,IN'). specialize (IN' y Hy). lia.
Qed.

Lemma renorm_loop_mapS q l n :
 map S (renorm_loop q l n) = renorm_loop q (map S l) n.
Proof.
 revert l.
 induction n; trivial; intros [|p l]; trivial.
 simpl in *.
 rewrite <- IHn.
 destruct (renorm_loop q l n) eqn:E; simpl; trivial.
 case Nat.eqb_spec; intros. apply IHn. trivial.
Qed.

Lemma renorm_mapS q l : map S (renorm q l) = renorm q (map S l).
Proof.
 unfold renorm. rewrite map_length. apply renorm_loop_mapS.
Qed.

Lemma renorm_loop_mapdecr q m l n : m <= q -> length l <= n ->
  sumA q (map (decr m) (renorm_loop q l n)) =
  sumA q (map (decr m) l).
Proof.
 intros Hm.
 revert l.
 induction n; intros [|p l] LE; simpl in *; auto.
 - inversion LE.
 - apply Nat.succ_le_mono in LE.
   rewrite <- (IHn l LE).
   assert (LE' := renorm_loop_length q l LE).
   assert (Hd := renorm_loop_head q l LE).
   destruct renorm_loop as [|p' l']; simpl in *; auto.
   case Nat.eqb_spec; simpl in *; intros; auto.
   rewrite IHn by (simpl; lia).
   subst p'. rewrite <- Nat.add_succ_r. simpl.
   rewrite Nat.add_assoc. f_equal.
   unfold decr.
   rewrite A_sum by lia.
   rewrite Nat.add_comm. f_equal; f_equal; lia.
Qed.

Lemma renorm_mapdecr q m l : m <= q ->
  sumA q (map (decr m) (renorm q l)) = sumA q (map (decr m) l).
Proof.
 unfold renorm. intros. now apply renorm_loop_mapdecr.
Qed.

Definition LeHd m l :=
  match l with [] => True | a::_ => m <= a end.

Lemma renorm_loop_mapdecr' q m l n :
  length l <= n ->
  Delta q l ->
  LeHd (m-q) l ->
  sumA q (map (decr m) (renorm_loop q l n)) =
  sumA q (map (decr m) l).
Proof.
 revert l.
 induction n; intros [|a l] LE D H; simpl in *; try lia.
 apply Nat.succ_le_mono in LE.
 apply Delta_alt in D. destruct D as (D,IN).
 assert (LH : LeHd (m-q) l).
 { destruct l as [|x l]; simpl in *; trivial.
   assert (a+q <= x) by auto. lia. }
 rewrite <- (IHn l LE D LH).
 assert (LE' := renorm_loop_length q l LE).
 assert (Hd := renorm_loop_head q l LE).
 assert (D' := @renorm_loop_delta q l n LE D).
 destruct renorm_loop as [|p' l']; simpl in *; auto.
 case Nat.eqb_spec; simpl in *; intros; auto.
 rewrite IHn; autoh; try (simpl; lia).
 subst p'. rewrite <- Nat.add_succ_r. simpl.
 rewrite Nat.add_assoc. f_equal.
 unfold decr.
 rewrite A_sum by lia.
 rewrite Nat.add_comm. f_equal; f_equal; lia.
Qed.

Lemma renorm_mapdecr' q m l :
  Delta q l -> LeHd (m-q) l ->
  sumA q (map (decr m) (renorm q l)) = sumA q (map (decr m) l).
Proof.
 unfold renorm. intros. now apply renorm_loop_mapdecr'.
Qed.

Lemma renorm_low q l : Delta (S q) (q::l) ->
  renorm q (0 :: q :: l) = renorm q (S q :: l).
Proof.
 intros D. transitivity (decomp q (sumA q (0::q::l))).
 - symmetry. apply decomp_carac.
   + apply renorm_delta. constructor. lia. auto with hof.
   + now rewrite renorm_sum.
 - apply decomp_carac.
   + apply renorm_delta. auto with hof.
   + rewrite renorm_sum. simpl. rewrite Nat.sub_diag. simpl. lia.
Qed.

(** Below, [renormS q a l] is a simplified version of [renorm q (S a :: l)].
    Indeed, when a decomposition starts by one lax gap and is strict
    afterwards, no need for the full renorm, a single
    bottom-up pass is enough. This particular situation is used
    in next_decomp below. *)

Fixpoint renormS q a l :=
  match l with
  | [] => [S a]
  | b::l' => if b =? S (a+q) then renormS q b l' else S a :: l
  end.

Lemma renormS_sum q a l : sumA q (renormS q a l) = sumA q (S a :: l).
Proof.
 revert a. induction l as [|b l IH]; intros a; simpl; auto.
 case Nat.eqb_spec; simpl; intros H; auto.
 rewrite IH. simpl. replace (b-q) with (S a); simpl; lia.
Qed.

Lemma renormS_delta q a l :
  Delta (S q) (a::l) -> Delta (S q) (renormS q a l).
Proof.
 revert a. induction l as [|b l IH]; intros a; simpl; auto.
 - intros. constructor.
 - inversion 1; subst.
   case Nat.eqb_spec; simpl; intros E; auto.
   constructor; auto. lia.
Qed.

Lemma renormS_alt q a l : Delta (S q) (a::l) ->
  renormS q a l = renorm q (S a :: l).
Proof.
 intros D. eapply decomp_unique; eauto using renormS_delta.
 - apply renorm_delta; auto with hof.
 - now rewrite renormS_sum, renorm_sum.
Qed.

Lemma renormS_head q a l : HeadStep q (S a :: l) (renormS q a l).
Proof.
 revert a. induction l as [|b l IH]; simpl.
 - exists 0; lia.
 - intros a. case Nat.eqb_spec; intros H.
   + specialize (IH b). destruct renormS; simpl in *; trivial.
     destruct IH as (m & ->). exists (S m). simpl; lia.
   + exists 0; lia.
Qed.

(** ** Decomposition of the next number *)

Definition next_decomp q l :=
  match l with
  | [] => [0]
  | a :: l' =>
    if a <=? q then
      renormS q a l'  (* same here as renorm q (S a :: l') *)
    else
      0::l
  end.

Lemma next_decomp_sum q l : sumA q (next_decomp q l) = S (sumA q l).
Proof.
 destruct l; simpl; trivial.
 case Nat.leb_spec; intros; rewrite ?renormS_sum; simpl; trivial.
 replace (n-q) with 0; simpl; lia.
Qed.

Lemma next_decomp_delta q l : Delta (S q) l -> Delta (S q) (next_decomp q l).
Proof.
 destruct l; simpl; autoh.
 case Nat.leb_spec; intros; auto using renormS_delta with hof.
Qed.

Lemma decomp_S q n : decomp q (S n) = next_decomp q (decomp q n).
Proof.
 apply decomp_carac.
 - apply next_decomp_delta, decomp_delta.
 - now rewrite next_decomp_sum, decomp_sum.
Qed.


(** ** Classification of decompositions *)

(** The k-ranq of a number is the least index in its k-decomposition. *)

Definition rank q n :=
  match decomp q n with
  | [] => None
  | p :: _ => Some p
  end.

Definition Rank q n r :=
 exists l, n = sumA q (r::l) /\ Delta (S q) (r::l).

Lemma rank_Rank q n r :
 rank q n = Some r <-> Rank q n r.
Proof.
 split.
 - unfold rank.
   destruct (decomp q n) eqn:E.
   + discriminate.
   + injection 1 as ->.
     exists l. rewrite <- E; autoh.
 - intros (l & E & D).
   unfold rank.
   rewrite decomp_carac with (l:=r::l); auto.
Qed.

Lemma rank_none q n : rank q n = None <-> n = 0.
Proof.
 split.
 - unfold rank. destruct decomp eqn:H.
   + now rewrite <- (decomp_sum q n), H.
   + discriminate.
 - now intros ->.
Qed.

Lemma rank_next_0 q n r : rank q n = Some r -> q < r ->
 rank q (S n) = Some 0.
Proof.
 unfold rank.
 intros Hr.
 rewrite decomp_S.
 destruct decomp as [|r' l]; try discriminate.
 injection Hr as ->. simpl.
 case Nat.leb_spec; auto. lia.
Qed.

Lemma rank_next_high q n r : rank q n = Some r -> r <= q ->
 exists m, rank q (S n) = Some (S r + m*(S q)).
Proof.
 unfold rank.
 intros Hr.
 rewrite decomp_S.
 destruct decomp as [|r' l]; try discriminate.
 injection Hr as ->. simpl.
 rewrite <- Nat.leb_le. intros ->.
 assert (R := renormS_head q r l).
 destruct renormS as [|r' l']; simpl in *; intuition.
 destruct R as (m, Hm).
 exists m. now f_equal.
Qed.

Lemma rank_next_high' q n r : rank q n = Some r -> r <= q ->
 exists r', rank q (S n) = Some r' /\ r < r'.
Proof.
 intros H H'.
 destruct (rank_next_high _ H H') as (m & Hm).
 exists (S r + m * S q); auto with arith.
Qed.

Lemma rank_next q n r : rank q n = Some r ->
 rank q (S n) = Some 0 \/
 exists m, rank q (S n) = Some (S r + m*(S q)).
Proof.
 unfold rank.
 intros Hr.
 rewrite decomp_S.
 destruct decomp as [|r' l]; try discriminate.
 injection Hr as ->. simpl.
 case Nat.leb_spec; auto. intros LE.
 assert (R := renormS_head q r l).
 destruct renormS as [|r' l']; simpl in *; intuition.
 destruct R as (m, Hm).
 right. exists m. now f_equal.
Qed.

Lemma rank_next' q n r : rank q n = Some r ->
 exists r', rank q (S n) = Some r' /\ (r' = 0 \/ r < r').
Proof.
 intros Hr. apply rank_next in Hr.
 destruct Hr as [Hr|(m,Hr)].
 - exists 0; intuition.
 - exists (S r + m * S q); split; auto. right. auto with arith.
Qed.

Lemma ranks_next q n r p : rank q n = Some r ->
 (exists a, a<=p /\ rank q (a+n) = Some 0) \/
 (exists r', rank q (p+n) = Some r' /\ p+r <= r').
Proof.
 revert n r.
 induction p as [|p IH].
 - right. exists r; auto.
 - intros n r Hn.
   destruct (rank_next' q n Hn) as (r' & Hr & [->|LT]).
   + left. exists 1; auto with arith.
   + destruct (IH (S n) r' Hr) as [(a & Ha & H)|(r'' & H & Hr'')];
     rewrite Nat.add_succ_r in H.
     * left. exists (S a); auto with arith.
     * right. exists r''. split; auto; lia.
Qed.

Lemma rank_later_is_high q n r p : p <= S q ->
 rank q n = Some r ->
 exists r', exists a, a <= p /\ rank q (a+n) = Some r' /\ p <= r'.
Proof.
 revert n r.
 induction p as [|p IH]; intros n r Hp Hr.
 - exists r, 0. auto with arith.
 - destruct (IH n r) as (r' & a & H1 & H2 & H3); auto; try lia.
   destruct (Nat.leb_spec r' q) as [LE|LT].
   destruct (rank_next_high' _ H2 LE) as (r'' & Hr'' & LT').
   + exists r''. exists (S a). repeat split; auto with arith.
     lia.
   + exists r'. exists a. repeat split; auto with arith. lia.
Qed.

Lemma rank_later_is_zero q n :
 exists p, p <= S q /\ rank q (p+n) = Some 0.
Proof.
 destruct (rank q n) as [r|] eqn:Hr.
 - destruct r as [|r].
   + exists 0; auto with arith.
   + destruct (ranks_next q n q Hr) as [(a & Hq & H)|(r' & H & LT)].
     * exists a; auto.
     * clear Hr.
       exists (S q). split; auto.
       simpl.
       unfold rank in *.
       rewrite decomp_S.
       destruct (decomp q (q+n)) as [|r'' l]; auto.
       injection H as ->; simpl.
       case Nat.leb_spec; auto; lia.
 - rewrite rank_none in *. subst. exists 1; auto with arith.
Qed.


(** ** Decomposition of the predecessor of a Aq number

   [(A q n) - 1 = A q (n-1) + A q (n-1-S q) + ... + A q (n-1-p*(S q))]

   with [p] such that [n-1-p*(S q)] is in [0..q].
   i.e. [p = (n-1)/(S q)]
*)

Fixpoint decompred q n :=
 match n with
 | 0 => []
 | S n => decompred q (n-q) ++ [n]
 end.

Lemma decompred_sum q n : sumA q (decompred q n) = A q n - 1.
Proof.
 induction n as [[|n] IH] using lt_wf_rec; trivial.
 simpl. rewrite sumA_app. simpl. rewrite IH by lia.
 generalize (A_nz q (n-q)); lia.
Qed.

Lemma decompred_below q n : Below (decompred q n) n.
Proof.
 induction n as [[|n] IH] using lt_wf_rec; simpl; try easy.
 intros y. rewrite in_app_iff. intros [IN|[<-|[ ]]]; try lia.
 apply IH in IN; lia.
Qed.

Lemma decompred_delta q n : Delta (S q) (decompred q n).
Proof.
 induction n as [[|n] IH] using lt_wf_rec; autoh.
 simpl. destruct (Nat.le_gt_cases n q).
 - replace (n-q) with 0 by lia. simpl. constructor.
 - apply Delta_app with (n-S q).
   + apply IH; lia.
   + constructor. lia. autoh.
   + intros y IN. apply decompred_below in IN. lia.
Qed.

(** Decomposition of the previous number *)

Definition prev_decomp q l :=
 match l with
 | [] => []
 | x::l => decompred q x ++ l
 end.

Lemma prev_decomp_sum q l : sumA q (prev_decomp q l) = sumA q l - 1.
Proof.
 destruct l as [|x l]; simpl; trivial. rewrite sumA_app, decompred_sum.
 generalize (A_nz q x). lia.
Qed.

Lemma prev_decomp_below q l N : Below l N -> Below (prev_decomp q l) N.
Proof.
 destruct l as [|x l]; simpl; trivial.
 intros B y. rewrite in_app_iff. intros [IN|IN].
 - apply decompred_below in IN. specialize (B x). simpl in B. lia.
 - apply B. now right.
Qed.

Lemma prev_decomp_delta q l : Delta (S q) l -> Delta (S q) (prev_decomp q l).
Proof.
 destruct l as [|x l]; simpl; trivial. intros D.
 apply Delta_app with x; eauto using Delta_more, decompred_delta.
 intros y IN. apply decompred_below in IN. lia.
Qed.

Lemma prev_decomp_delta_lax q l : Delta q l -> Delta q (prev_decomp q l).
Proof.
 destruct l as [|x l]; simpl; trivial. intros D.
 apply Delta_app with x; eauto using Delta_more, decompred_delta.
 intros y IN. apply decompred_below in IN. lia.
Qed.

Lemma decomp_pred q n : decomp q (n-1) = prev_decomp q (decomp q n).
Proof.
 apply decomp_carac.
 - apply prev_decomp_delta, decomp_delta.
 - now rewrite prev_decomp_sum, decomp_sum.
Qed.

Lemma rank_pred q n r :
  rank q n = Some r -> r <> 0 ->
  rank q (n-1) = Some ((r-1) mod (S q)).
Proof.
 unfold rank.
 set (l := decomp q n).
 rewrite <- (decomp_sum q n). fold l.
 rewrite <- prev_decomp_sum, decomp_sum'.
 2:apply prev_decomp_delta, decomp_delta.
 destruct l as [|a l]; try easy.
 intros [= <-] Ha. clear n. cbn -[Nat.modulo].
 revert Ha l.
 induction a as [[|a] IH] using lt_wf_ind.
 - now destruct 1.
 - intros _ l. cbn -[Nat.modulo].
   destruct (Nat.eq_dec (a-q) 0) as [E|NE].
   + rewrite E. cbn -[Nat.modulo]. f_equal. rewrite Nat.sub_0_r.
     rewrite Nat.mod_small; auto. lia.
   + rewrite <- app_assoc, IH; try lia.
     f_equal. rewrite Nat.sub_0_r.
     rewrite <- (@Nat.mod_add (a-q-1) 1 (S q)); auto. f_equal. lia.
Qed.

(** We can decrease a decomposition by iterating [prev_decomp].
    Note: the highest term of the decomposition will not grow. *)

Fixpoint decompminus q l p :=
  match p with
  | 0 => l
  | S p => decompminus q (prev_decomp q l) p
  end.

Lemma decompminus_sum q l p : sumA q (decompminus q l p) = sumA q l - p.
Proof.
 revert l. induction p as [|p IH]; intros l; simpl; try lia.
 rewrite IH, prev_decomp_sum. lia.
Qed.

Lemma decompminus_below q l p N : Below l N -> Below (decompminus q l p) N.
Proof.
 revert l. induction p as [|p IH]; intros l Hl; simpl; auto.
 now apply IH, prev_decomp_below.
Qed.

Lemma decompminus_delta q l p :
 Delta (S q) l -> Delta (S q) (decompminus q l p).
Proof.
 revert l. induction p as [|p IH]; intros l Hl; simpl; auto.
 now apply IH, prev_decomp_delta.
Qed.

Lemma decompminus_delta_lax q l p :
 Delta q l -> Delta q (decompminus q l p).
Proof.
 revert l. induction p as [|p IH]; intros l Hl; simpl; auto.
 now apply IH, prev_decomp_delta_lax.
Qed.

Lemma decompminus_app_delta q l l' p :
  Delta q (l++l') -> Delta q (decompminus q l p ++ l').
Proof.
 rewrite !Delta_app_iff. intros (D1 & D2 & D3).
 repeat split; auto using decompminus_delta_lax.
 intros x x' IN IN'.
 assert (B : Below l (S x'-q)).
 { intros y Hy. specialize (D3 y x' Hy IN'). lia. }
 apply (@decompminus_below q l p) in B.
 specialize (B _ IN). lia.
Qed.

(** [decomp] can be used to generate all the subsets of [{0..p-1}]
    whose elements are at distance of at least (k+1). *)

Definition enum_sparse_subsets q p := map (decomp q) (seq 0 (A q p)).

Lemma decomp_max' q p l :
  Delta (S q) l -> Below l p -> sumA q l < A q p.
Proof.
 intros D B.
 rewrite <- DeltaRev_rev in D.
 assert (B' : Below (rev l) p). { intros y. rewrite <- in_rev. apply B. }
 clear B.
 rewrite <- sumA_rev.
 destruct (rev l) as [|n l'].
 - apply A_nz.
 - apply Nat.lt_le_trans with (A q (S n)).
   + now apply decomp_max.
   + apply A_mono. apply B'. now left.
Qed.

Lemma enum_sparse_subsets_ok q p l :
  In l (enum_sparse_subsets q p) <-> Below l p /\ Delta (S q) l.
Proof.
 unfold enum_sparse_subsets.
 rewrite in_map_iff. setoid_rewrite in_seq.
 split.
 - intros (n & Hl & (_,Hn)). simpl in Hn. split.
   + intros x Hx. subst l.
     apply decomp_in in Hx. apply (@A_lt_inv q). lia.
   + subst l. apply decomp_delta.
 - intros (Hl,D). exists (sumA q l). split.
   + now apply decomp_sum'.
   + split; [lia|]. apply decomp_max'; trivial.
Qed.

Lemma enum_sparse_subsets_nodup q p : NoDup (enum_sparse_subsets q p).
Proof.
 apply FinFun.Injective_map_NoDup; [|apply seq_NoDup].
 intros x y E.
 now rewrite <- (@decomp_sum q x), E, decomp_sum.
Qed.

(** The decompositions of rank 0 can be obtained in a more efficient way *)

Definition zeroshift q l := 0::map (Nat.add q) l.

Lemma zeroshift_delta q l : Delta q (zeroshift q l) <-> Delta q l.
Proof.
 unfold zeroshift; split; intros D.
 - replace l with (map (decr q) (map (Nat.add q) l)).
   2:{ rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext.
       unfold decr. lia. }
   apply Delta_map_decr. 2:eapply Delta_inv; eauto.
   intros x. rewrite in_map_iff. intros (y & <- & IN). lia.
 - rewrite Delta_alt; split.
   + eapply Delta_map; eauto; lia.
   + intros x. rewrite in_map_iff. intros (y & <- & IN). lia.
Qed.

Lemma zeroshift_below d b l :
 Below (zeroshift (S d) l) (S b) <-> Below l (b-d).
Proof.
 unfold zeroshift; split; intros B x IN.
 - assert (S d + x < S b); try lia.
   { apply B. simpl; right. rewrite in_map_iff. now exists x. }
 - simpl in IN. rewrite in_map_iff in IN.
   destruct IN as [<-|(y & <- & IN)]; try lia. specialize (B y IN). lia.
Qed.

Definition enum_sparse_subsets0 q p :=
  map (zeroshift (S q)) (enum_sparse_subsets q (p-S q)).

Lemma enum_sparse_subsets0_ok q p l :
 In (0::l) (enum_sparse_subsets0 q (S p)) <->
 In (0::l) (enum_sparse_subsets q (S p)).
Proof.
 unfold enum_sparse_subsets0. rewrite in_map_iff, enum_sparse_subsets_ok.
 setoid_rewrite enum_sparse_subsets_ok.
 split.
 - intros (l' & E & B & D).
   now rewrite <- E, zeroshift_delta, zeroshift_below.
 - intros (B,D).
   set (l' := map (decr (S q)) l).
   assert (E : zeroshift (S q) l' = 0::l).
   { unfold zeroshift. f_equal. unfold l'. rewrite map_map.
     rewrite <- (map_id l) at 2. apply map_ext_in.
     intros a Ha. eapply Delta_le in D; eauto. unfold decr. lia. }
   exists l'. split. trivial.
   simpl. now rewrite <- zeroshift_delta, <- zeroshift_below, E.
Qed.

(** Another enumeration, more algorithmic and faster,
    building the same sparse subsets (but in a different order) *)

Fixpoint enum_delta_below d b :=
  match b with
  | 0 => [[]]
  | S b =>
    map (zeroshift (S d)) (enum_delta_below d (b - d))
    ++ map (map S) (enum_delta_below d b)
  end.

Lemma enum_delta_below_ok d b l :
 In l (enum_delta_below d b) <-> Delta (S d) l /\ Below l b.
Proof.
 revert l.
 induction b as [[|b] IH] using lt_wf_ind; cbn; intros l; split.
 - intros [<-|[]]. split. constructor. now red.
 - intros (D,B). destruct l as [|n l]; auto.
   assert (n < 0)%nat by (apply B; now left). lia.
 - rewrite in_app_iff, !in_map_iff.
   intros [(u & <- & IN)|(u & <- & IN)]; rewrite IH in IN by lia; clear IH.
   + now rewrite zeroshift_delta, zeroshift_below.
   + destruct IN as (D,B). split.
     * eapply Delta_map; eauto; lia.
     * intros x. rewrite in_map_iff. intros (y & <- & IN). apply B in IN. lia.
 - intros (D,B). rewrite in_app_iff, !in_map_iff.
   destruct l as [|[|x] l].
   + right. exists []. split; auto. rewrite IH by lia; split; auto. now red.
   + left. assert (D' := fun x => @Delta_le (S d) l 0 x D).
     replace (0 :: l) with (zeroshift (S d) (map (decr (S d)) l)) in *.
     rewrite zeroshift_delta in D.
     rewrite zeroshift_below in B.
     2:{ unfold zeroshift. f_equal. rewrite map_map.
         rewrite <- (map_id l) at 2. apply map_ext_in.
         intros x Hx. unfold decr. specialize (D' x Hx). lia. }
     eexists; split; [ reflexivity | ]. rewrite IH by lia. easy.
   + right. assert (D' := fun y => @Delta_le (S d) l (S x) y D).
     replace (S x :: l) with (map S (x :: map (decr 1) l)).
     2:{ unfold decr. simpl. f_equal. rewrite map_map.
         rewrite <- (map_id l) at 2. apply map_ext_in.
         intros y Hy. specialize (D' y Hy). lia. }
     eexists; split; [ reflexivity | ]. rewrite IH by lia; split.
     { rewrite Delta_alt. split.
       - apply Delta_map_decr. intros y Hy. specialize (D' y Hy). lia.
         eapply Delta_inv; eauto.
       - intro y. rewrite in_map_iff. intros (z & <- & IN).
         specialize (D' z IN). unfold decr. lia. }
     { intros y. simpl. rewrite in_map_iff. intros [<-|(z & <- & IN)].
       - specialize (B (S x)). simpl in B. lia.
       - unfold decr. specialize (B z (or_intror IN)). specialize (D' z IN).
         lia. }
Qed.

Lemma enum_delta_below_nodup q p : NoDup (enum_delta_below q p).
Proof.
 induction p as [[|p] IH] using lt_wf_ind; simpl.
 - now repeat constructor.
 - apply app_nodup.
   + apply FinFun.Injective_map_NoDup; [ | apply IH; lia].
     intros x y. unfold zeroshift. intros [=E].
     clear IH. revert y E.
     induction x; destruct y; try easy; intros [= E E'].
     f_equal. lia. now apply IHx.
   + apply FinFun.Injective_map_NoDup; [ | apply IH; lia].
     intros x. induction x; destruct y; try easy; intros [= E E'].
     f_equal; auto.
   + intros x. rewrite !in_map_iff.
     now intros ((l & E & _),([|l'] & <- & _)).
Qed.

Lemma enums_equiv q p :
  Permutation (enum_sparse_subsets q p) (enum_delta_below q p).
Proof.
 apply NoDup_Permutation;
  trivial using enum_delta_below_nodup, enum_sparse_subsets_nodup.
 intros l. now rewrite enum_sparse_subsets_ok, enum_delta_below_ok.
Qed.
