(** * Fib : Fibonacci sequence and decomposition *)

Require Import Arith Lia Wf_nat List.
Require Import DeltaList.
Import ListNotations.
Set Implicit Arguments.

(** * Generalized Fibonacci sequence *)

Fixpoint A (k n : nat) :=
  match n with
  | O => 1
  | S n => A k n + A k (n-k)
  end.

(**
 - k=0 : binary numbers
 - k=1 : Fibonacci numbers (non-standard indexes)
         1 2 3 5 8 ...
 - k=2 : Narayana’s Cows, see OEIS A930 (shifted)
 - k=3 : See OEIS A003269 (shifted)
*)

Definition test := List.seq 0 10.

(*
Compute map (A 0) test.
Compute map (A 1) test.
Compute map (A 2) test.
Compute map (A 3) test.
*)
(*
A 0 : [1; 2; 4; 8; 16; 32; 64; 128; 256; 512]
A 1 : [1; 2; 3; 5; 8; 13; 21; 34; 55; 89]
A 2 : [1; 2; 3; 4; 6; 9; 13; 19; 28; 41]
A 3 : [1; 2; 3; 4; 5; 7; 10; 14; 19; 26]
*)

Lemma A_k_0 k : A k 0 = 1.
Proof.
 reflexivity.
Qed.

Lemma A_S k n : A k (S n) = A k n + A k (n-k).
Proof.
 reflexivity.
Qed.

Lemma A_base k n : n <= S k -> A k n = S n.
Proof.
 induction n; auto.
 simpl. intros.
 replace (n-k) with 0 by lia. simpl.
 rewrite IHn; lia.
Qed.

Lemma S_sub_1 p : S p - 1 = p.
Proof.
 lia.
Qed.

Lemma A_sum k n : n<>0 -> A k n = A k (n-1) + A k (n-S k).
Proof.
 destruct n.
 - now destruct 1.
 - intros _. now rewrite S_sub_1.
Qed.

Lemma A_sum' k n : A k (n+S k) = A k n + A k (n+k).
Proof.
 intros.
 rewrite A_sum by lia.
 rewrite Nat.add_comm. f_equal; f_equal; lia.
Qed.

Lemma A_k_1 k : A k 1 = 2.
Proof.
 reflexivity.
Qed.

Lemma A_0_pow2 n : A 0 n = 2^n.
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
 simpl. generalize (A_nz k (n-k)). lia.
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

Lemma A_lt_id k n : n < A k n.
Proof.
 induction n; simpl; auto.
 generalize (A_nz k (n-k)). lia.
Qed.

Lemma A_base_iff k n : n <= S k <-> A k n = S n.
Proof.
 split. apply A_base.
 intros.
 destruct n; auto with arith.
 rewrite A_S in H.
 generalize (A_lt_id k n).
 generalize (A_lt_id k (n-k)).
 lia.
Qed.

Lemma A_high k n : S k < n <-> S n < A k n.
Proof.
 generalize (A_base_iff k n) (A_lt_id k n). lia.
Qed.

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

(* Compute proj1_sig (A_inv 2 10).   (* = 5 *) *)

(** * Decomposition via sums of Ak numbers.

    Zeckendorf's theorem (actually discovered earlier by
    Lekkerkerker) states that any natural number can be obtained
    by a sum of distinct Fibonacci numbers, and this decomposition
    is moreover unique when Fibonacci numbers in the decomposition
    aren't consecutive.

    This is the generalization to Ak numbers.
*)

(** ** The [sumA] function

   We represent a decomposition by the list of ranks
   of the Ak numbers in this decomposition.
   The sumA function is the sum of the Fibonacci numbers of
   these ranks. For the first results below, the ranks may be
   arbitrary : redundant, in any order, ... *)

Definition sumA k l := fold_right (fun n acc => A k n + acc) 0 l.

Lemma sumA_cons k a l : sumA k (a::l) = A k a + sumA k l.
Proof.
 reflexivity.
Qed.

Definition decr x y := Nat.sub y x.

Lemma decr_0 x : decr 0 x = x.
Proof.
 apply Nat.sub_0_r.
Qed.

Lemma map_decr_1 l : map (decr 1) l = map pred l.
Proof.
 apply map_ext. intros; unfold decr. lia.
Qed.

Lemma map_decr_S k l :
 map (decr (S k)) l = map (decr k) (map pred l).
Proof.
 rewrite map_map. apply map_ext. intros. unfold decr. lia.
Qed.

Lemma sumA_eqn k l :
 sumA k l + sumA k (map (decr k) l) = sumA k (map S l).
Proof.
 induction l; trivial.
 simpl map. rewrite !sumA_cons, <- IHl, A_S.
 unfold decr at 1. lia.
Qed.

Lemma sumA_eqn' k l :
 sumA k (map S l) - sumA k (map (decr k) l) = sumA k l.
Proof.
 rewrite <- sumA_eqn. apply Nat.add_sub.
Qed.

Lemma sumA_eqn_pred k l :
 ~In 0 l ->
 sumA k l = sumA k (map (decr 1) l) + sumA k (map (decr (S k)) l).
Proof.
 induction l; trivial.
 simpl map. simpl. intros. rewrite IHl by intuition.
 unfold decr at 3 5.
 rewrite (@A_sum k a); lia.
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

(** ** Zeckendorf's Theorem *)

(** Technical lemma:
    A canonical decomposition cannot excess the next Ak. *)

Lemma decomp_max k n l :
  DeltaRev (S k) (n::l) ->
    sumA k (n::l) < A k (S n).
Proof.
 revert n.
 induction l.
 - intros n _. simpl sumA. rewrite Nat.add_0_r. apply A_lt_S.
 - intros n.
   inversion 1; subst. simpl sumA.
   rewrite A_S.
   apply Nat.add_lt_mono_l.
   apply lt_le_trans with (A k (S a)).
   + apply IHl; auto.
   + apply A_mono; lia.
Qed.

(** Zeckendorf's Theorem, in a variant that consider
    decompositions with largest terms first
    (easiest for the proof). *)

Lemma decomp_exists_rev k n :
  { l | sumA k l = n /\ DeltaRev (S k) l }.
Proof.
 induction n as [n IH] using lt_wf_rec.
 destruct (Nat.eq_dec n 0) as [EQ|NE].
 - exists []. subst; simpl; intuition.
 - destruct (A_inv' k NE) as (p,Hp).
   destruct (IH (n - A k p)) as (l & EQ & DR).
   { generalize (A_nz k p); lia. }
   exists (p::l); simpl; split; try lia.
   destruct l as [|p' l]; trivial.
   constructor; trivial.
   assert (p' < p - k); [|lia].
   apply (A_lt_inv k).
   simpl in EQ. rewrite A_S in Hp. lia.
Defined.

Definition decomp_rev k n := proj1_sig (decomp_exists_rev k n).

Lemma decomp_rev_sum k n :
  sumA k (decomp_rev k n) = n.
Proof.
 unfold decomp_rev. now destruct decomp_exists_rev.
Qed.

Lemma decomp_rev_delta k n :
  DeltaRev (S k) (decomp_rev k n).
Proof.
 unfold decomp_rev. now destruct decomp_exists_rev.
Qed.

Lemma decomp_unique_rev k l l' :
 DeltaRev (S k) l ->
 DeltaRev (S k) l' ->
 sumA k l = sumA k l' -> l = l'.
Proof.
 revert l'.
 induction l as [|n l IH]; destruct l' as [|n' l'].
 - trivial.
 - intros _ Hn'. simpl in *. generalize (A_nz k n'); lia.
 - intros Hn _. simpl in *. generalize (A_nz k n); lia.
 - intros DR DR' EQ.
   assert (n < S n').
   { apply (A_lt_inv k). simpl in EQ.
     apply le_lt_trans with (A k n' + sumA k l'); [lia|].
     now apply decomp_max. }
   assert (n' < S n).
   { apply (A_lt_inv k). simpl in EQ.
     apply le_lt_trans with (A k n + sumA k l); [lia|].
     now apply decomp_max. }
   replace n' with n in * by lia. clear H H0.
   simpl in EQ.
   f_equal.
   apply IH; clear IH; simpl in *; try lia; intuition.
   + apply DeltaRev_alt in DR. intuition.
   + apply DeltaRev_alt in DR'. intuition.
Qed.

Lemma decomp_rev_carac k n l :
 DeltaRev (S k) l -> sumA k l = n -> decomp_rev k n = l.
Proof.
 intros D Eq. apply (@decomp_unique_rev k); auto.
 apply decomp_rev_delta.
 rewrite <- Eq. apply decomp_rev_sum.
Qed.

(** Same theorems, in the other order (smallest term first). *)

Lemma decomp_exists k n :
  { l | sumA k l = n /\ Delta (S k) l }.
Proof.
 destruct (decomp_exists_rev k n) as (l & Hn & Hl).
 exists (rev l); repeat split.
 - now rewrite sumA_rev.
 - now apply Delta_rev.
Defined.

Definition decomp k n := proj1_sig (decomp_exists k n).

Lemma decomp_sum k n : sumA k (decomp k n) = n.
Proof.
 unfold decomp. now destruct decomp_exists.
Qed.

Lemma decomp_delta k n : Delta (S k) (decomp k n).
Proof.
 unfold decomp. now destruct decomp_exists.
Qed.
Hint Resolve decomp_sum decomp_delta.

Lemma decomp_unique k l l' :
 Delta (S k) l -> Delta (S k) l' ->
  sumA k l = sumA k l' -> l = l'.
Proof.
 intros D D' EQ.
 rewrite <- (rev_involutive l), <- (rev_involutive l'). f_equal.
 apply (@decomp_unique_rev k).
 - now apply DeltaRev_rev.
 - now apply DeltaRev_rev.
 - now rewrite !sumA_rev.
Qed.

Lemma decomp_carac k n l :
 Delta (S k) l -> sumA k l = n -> decomp k n = l.
Proof.
 intros D Eq. apply (@decomp_unique k); auto.
 rewrite <- Eq; auto.
Qed.
Hint Resolve decomp_carac.

(** ** Normalisation of a Fibonacci decomposition.

    Starting from an relaxed decomposition (with gaps
    of at least [k]), we can transform it into a canonical
    decomposition (with gaps of at least [S k]),
    by simply saturating the basic equation
    [A k n + A k (n-k) = A k (S n)]
    in the right order (highest terms first).

    Termination isn't obvious for Coq, since we might have
    to re-launch normalisation on by-products of a first
    normalisation. The number of terms in the decomposition
    decreases strictly during the process, we use that to
    justify the termination.

    Moreover, the lowest term in the decomposition grows by
    steps of [S k] during the process (or stays equal).
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
       if p+k =? p' then
         renorm_loop k (S p' :: l') n
       else
         p::p'::l'
     end
   end
 end.

Definition renorm k l := renorm_loop k l (length l).

(*
Compute renorm 1 [0;1;3;4;5;7]. (* [4; 8] *)
Compute renorm 2 [1;3;5;8]. (* [1; 9] *)
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
Hint Resolve renorm_length.

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
   replace (p'-k) with p; lia.
Qed.

Lemma renorm_sum k l : sumA k (renorm k l) = sumA k l.
Proof.
 unfold renorm. now apply renorm_loop_sum.
Qed.
Hint Resolve renorm_sum.

Definition HeadStep k l l' := match l, l' with
| [], [] => True
| p::_, p'::_ => exists m, p' = p + m*(S k)
| _, _ => False
end.

Lemma renorm_loop_head k l n :
  length l <= n -> HeadStep k l (renorm_loop k l n).
Proof.
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

Lemma renorm_head k l : HeadStep k l (renorm k l).
Proof.
 unfold renorm. now apply renorm_loop_head.
Qed.

Lemma renorm_loop_delta k l n :
  length l <= n -> Delta k l -> Delta (S k) (renorm_loop k l n).
Proof.
 revert l.
 induction n; intros [|p l] LE D; simpl in *; auto.
 apply Nat.succ_le_mono in LE.
 apply Delta_alt in D. destruct D as (D,IN).
 assert (D' := IHn l LE D).
 assert (LE' := renorm_loop_length k l LE).
 assert (Hd := renorm_loop_head k l LE).
 destruct renorm_loop as [|p' l']; simpl in *; auto.
 case Nat.eqb_spec; simpl in *; intros.
 - apply IHn; simpl; auto; lia.
 - destruct l as [|x l]; simpl in *; [intuition|].
   destruct Hd as (m,Hd).
   constructor; auto.
   assert (p+k <= x). { apply IN; auto. }
   lia.
Qed.

Lemma renorm_delta k l : Delta k l -> Delta (S k) (renorm k l).
Proof.
 unfold renorm. now apply renorm_loop_delta.
Qed.
Hint Resolve renorm_delta.

Lemma renorm_le k x l : Delta k (x::l) ->
  forall y, In y (renorm k (x::l)) -> x <= y.
Proof.
 intros D y Hy.
 apply renorm_delta in D.
 assert (Hd := renorm_head k (x::l)).
 destruct renorm as [|p l'].
 - elim Hy.
 - destruct Hd as (m,Hd).
   transitivity p.
   + subst; auto with arith.
   + apply Delta_alt in D.
     simpl in Hy. destruct Hy as [->|Hy]; auto.
     destruct D as (_,IN'). specialize (IN' y Hy). lia.
Qed.

Lemma renorm_loop_mapdecr k m l n : m < S k -> length l <= n ->
  sumA k (map (decr m) (renorm_loop k l n)) =
  sumA k (map (decr m) l).
Proof.
 intros Hm.
 revert l.
 induction n; intros [|p l] LE; simpl in *; auto.
 - inversion LE.
 - apply Nat.succ_le_mono in LE.
   assert (H := IHn l LE).
   assert (LE' := renorm_loop_length k l LE).
   assert (Hd := renorm_loop_head k l LE).
   destruct renorm_loop as [|p' l']; simpl in *; auto.
   case Nat.eqb_spec; simpl in *; intros.
   + rewrite IHn by (simpl; lia).
     subst p'. rewrite <- H.
     rewrite <- Nat.add_succ_r. simpl.
     rewrite Nat.add_assoc. f_equal.
     unfold decr.
     rewrite A_sum by lia.
     rewrite Nat.add_comm. f_equal; f_equal; lia.
   + now rewrite <- H.
Qed.

Lemma renorm_mapdecr k m l : m < S k ->
  sumA k (map (decr m) (renorm k l)) = sumA k (map (decr m) l).
Proof.
 unfold renorm. intros. now apply renorm_loop_mapdecr.
Qed.

Definition LeHd m l :=
  match l with [] => True | a::_ => m <= a end.

Lemma renorm_loop_mapdecr' k m l n :
  length l <= n ->
  Delta k l ->
  LeHd m l ->
  sumA k (map (decr m) (renorm_loop k l n)) =
  sumA k (map (decr m) l).
Proof.
 revert l.
 induction n; intros [|a l] LE D H; simpl in *; auto.
 - inversion LE.
 - apply Nat.succ_le_mono in LE.
   apply Delta_alt in D. destruct D as (D,IN).
   assert (LH : LeHd m l).
   { destruct l as [|x l]; simpl in *; [intuition|].
     assert (a+k <= x) by auto. lia. }
   assert (H' := IHn l LE D LH).
   assert (LE' := renorm_loop_length k l LE).
   assert (Hd := renorm_loop_head k l LE).
   assert (D' := @renorm_loop_delta k l n LE D).
   destruct renorm_loop as [|p' l']; simpl in *; auto.
   case Nat.eqb_spec; simpl in *; intros.
   + rewrite IHn; auto; try (simpl; lia).
     subst p'. rewrite <- H'; auto.
     rewrite <- Nat.add_succ_r. simpl.
     rewrite Nat.add_assoc. f_equal.
     unfold decr.
     rewrite A_sum by lia.
     rewrite Nat.add_comm. f_equal; f_equal; lia.
   + rewrite <- H'; auto.
Qed.

Lemma renorm_mapdecr' k m l :
  Delta k l -> LeHd m l ->
  sumA k (map (decr m) (renorm k l)) = sumA k (map (decr m) l).
Proof.
 unfold renorm. intros. now apply renorm_loop_mapdecr'.
Qed.

(** ** Decomposition of the next number *)

Definition next_decomp k l :=
  match l with
  | [] => [0]
  | a :: l =>
    if a <=? k then
      renorm k (S a :: l)
    else
      0::a::l
  end.

Lemma decomp_S k n : decomp k (S n) = next_decomp k (decomp k n).
Proof.
 apply decomp_carac.
 - assert (D:=decomp_delta k n).
   destruct decomp as [|a l]; simpl; auto.
   case Nat.leb_spec; intros; auto using renorm_delta.
 - rewrite <- (decomp_sum k n) at 2.
   destruct decomp as [|a l]; simpl; auto.
   case Nat.leb_spec; intros; auto.
   rewrite renorm_sum. simpl.
   replace (a-k) with 0; simpl; lia.
Qed.

(** ** Classification of decompositions *)

Definition rank k n :=
  match decomp k n with
  | [] => None
  | p :: _ => Some p
  end.

Definition Rank k n r :=
 exists l, n = sumA k (r::l) /\ Delta (S k) (r::l).

Lemma rank_Rank k n r :
 rank k n = Some r <-> Rank k n r.
Proof.
 split.
 - unfold rank.
   destruct (decomp k n) eqn:E.
   + discriminate.
   + injection 1 as ->.
     exists l. rewrite <- E; auto.
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

Lemma rank_next_0 k n r : rank k n = Some r -> k < r ->
 rank k (S n) = Some 0.
Proof.
 unfold rank.
 intros Hr.
 rewrite decomp_S.
 destruct decomp as [|r' l]; try discriminate.
 injection Hr as ->. simpl.
 case Nat.leb_spec; auto. lia.
Qed.

Lemma rank_next_high k n r : rank k n = Some r -> r <= k ->
 exists m, rank k (S n) = Some (S r + m*(S k)).
Proof.
 unfold rank.
 intros Hr.
 rewrite decomp_S.
 destruct decomp as [|r' l]; try discriminate.
 injection Hr as ->. simpl.
 rewrite <- Nat.leb_le. intros ->.
 assert (R := renorm_head k (S r::l)).
 destruct renorm as [|r' l']; simpl in *; intuition.
 destruct R as (m, Hm).
 exists m. now f_equal.
Qed.

Lemma rank_next_high' k n r : rank k n = Some r -> r <= k ->
 exists r', rank k (S n) = Some r' /\ r < r'.
Proof.
 intros H H'.
 destruct (rank_next_high _ H H') as (m & Hm).
 exists (S r + m * S k); auto with arith.
Qed.

Lemma rank_next k n r : rank k n = Some r ->
 rank k (S n) = Some 0 \/
 exists m, rank k (S n) = Some (S r + m*(S k)).
Proof.
 unfold rank.
 intros Hr.
 rewrite decomp_S.
 destruct decomp as [|r' l]; try discriminate.
 injection Hr as ->. simpl.
 case Nat.leb_spec; auto. intros LE.
 assert (R := renorm_head k (S r::l)).
 destruct renorm as [|r' l']; simpl in *; intuition.
 destruct R as (m, Hm).
 right. exists m. now f_equal.
Qed.

Lemma rank_next' k n r : rank k n = Some r ->
 exists r', rank k (S n) = Some r' /\ (r' = 0 \/ r < r').
Proof.
 intros Hr. apply rank_next in Hr.
 destruct Hr as [Hr|(m,Hr)].
 - exists 0; intuition.
 - exists (S r + m * S k); split; auto. right. auto with arith.
Qed.

Lemma ranks_next k n r p : rank k n = Some r ->
 (exists q, q<=p /\ rank k (q+n) = Some 0) \/
 (exists r', rank k (p+n) = Some r' /\ p+r <= r').
Proof.
 revert n r.
 induction p as [|p IH].
 - right. exists r; auto.
 - intros n r Hn.
   destruct (rank_next' k n Hn) as (r' & Hr & [->|LT]).
   + left. exists 1; auto with arith.
   + destruct (IH (S n) r' Hr) as [(q & Hq & H)|(r'' & H & Hr'')];
     rewrite Nat.add_succ_r in H.
     * left. exists (S q); auto with arith.
     * right. exists r''. split; auto; lia.
Qed.

Lemma rank_later_is_high k n r p : p <= S k ->
 rank k n = Some r ->
 exists r', exists q, q <= p /\ rank k (q+n) = Some r' /\ p <= r'.
Proof.
 revert n r.
 induction p as [|p IH]; intros n r Hp Hr.
 - exists r. exists 0. auto with arith.
 - destruct (IH n r) as (r' & q & H1 & H2 & H3); auto; try lia.
   destruct (Nat.leb_spec r' k) as [LE|LT].
   destruct (rank_next_high' _ H2 LE) as (r'' & Hr'' & LT').
   + exists r''. exists (S q). repeat split; auto with arith.
     lia.
   + exists r'. exists q. repeat split; auto with arith. lia.
Qed.

Lemma rank_later_is_zero k n :
 exists p, p <= S k /\ rank k (p+n) = Some 0.
Proof.
 destruct (rank k n) as [r|] eqn:Hr.
 - destruct r as [|r].
   + exists 0; auto with arith.
   + destruct (ranks_next k n k Hr) as [(q & Hq & H)|(r' & H & LT)].
     * exists q; auto.
     * clear Hr.
       exists (S k). split; auto.
       simpl.
       unfold rank in *.
       rewrite decomp_S.
       destruct (decomp k (k+n)) as [|r'' l]; auto.
       injection H as ->; simpl.
       case Nat.leb_spec; auto; lia.
 - rewrite rank_none in *. subst. exists 1; auto with arith.
Qed.


(** ** Decomposition of the predecessor of a Ak number

   [(A k n) - 1 = A k (n-1) + A k (n-1-S k) + ... + A k (n-1-p*(S k))]

   with [p] such that [n-1-p*(S k)] is in [0..k].
   i.e. [p = (n-1)/(S k)]
*)

Definition Below l x := forall y, In y l -> y < x.

Lemma decompred_spec_rev k n :
  { l | sumA k l = A k n - 1 /\
        DeltaRev (S k) l /\ Below l n }.
Proof.
 induction n as [n IH] using lt_wf_rec.
 destruct (Nat.eq_dec n 0) as [EQ|NE].
 - exists []; subst; unfold Below; simpl; repeat split; intuition.
 - destruct (le_lt_dec n (S k)) as [LE|LT].
   + exists [n-1]; unfold Below; simpl; repeat split; intuition; try lia.
     rewrite 2 A_base; lia.
   + destruct (IH (n-S k)) as (l & SUM & DR & IN) ; try lia.
     exists (n-1::l); simpl; repeat split; auto.
     * rewrite SUM. rewrite (@A_sum k n) by lia.
       generalize (A_nz k (n - S k)). lia.
     * apply DeltaRev_alt. split; auto.
       intros y Hy. specialize (IN y Hy). lia.
     * intros y [Hy|Hy]; try specialize (IN y Hy); lia.
Defined.

Lemma decompred_spec k n :
  { l | sumA k l = A k n - 1 /\
        Delta (S k) l /\ Below l n }.
Proof.
 destruct (decompred_spec_rev k n) as (l & SUM & DR & IN).
 exists (rev l); repeat split.
 - now rewrite sumA_rev.
 - now apply Delta_rev.
 - intros p. rewrite <- in_rev; now apply IN.
Defined.

Definition decompred k n := proj1_sig (decompred_spec k n).

Lemma decompred_sum k n :
  sumA k (decompred k n) = A k n - 1.
Proof.
 unfold decompred; destruct decompred_spec; simpl; intuition.
Qed.

Lemma decompred_delta k n : Delta (S k) (decompred k n).
Proof.
 unfold decompred; destruct decompred_spec; simpl; intuition.
Qed.

Lemma decompred_in k n : Below (decompred k n) n.
Proof.
 unfold decompred; destruct decompred_spec; simpl; intuition.
Qed.

(** We can decrease a decomposition (and the highest term will not grow).
    This is the version with lax decomposition, but a strict version would
    be possible too. *)

Lemma decompminus_spec k l p :
  { l' | sumA k l' = sumA k l - p /\
        (Delta k l -> Delta k l') /\
        (forall N, Below l N -> Below l' N) }.
Proof.
 revert l.
 induction p as [|p IH]; intros l.
 - exists l. split; auto. lia.
 - destruct l.
   + exists []. simpl; auto.
   + destruct (decompred_spec k n) as (l1 & E1 & D1 & B1).
     destruct (IH (l1++l)) as (l2 & E2 & D2 & B2).
     exists l2; repeat split.
     * rewrite E2. rewrite sumA_app. rewrite E1. simpl.
       generalize (A_nz k n). lia.
     * intros D. apply D2.
       apply Delta_app with n; eauto using Delta_more.
       intros x IN. apply B1 in IN. lia.
     * intros N B.
       assert (n < N) by (apply B; simpl; auto).
       apply B2.
       intros x. rewrite in_app_iff. specialize (B x). specialize (B1 x).
       simpl in B. intuition; lia.
Defined.
