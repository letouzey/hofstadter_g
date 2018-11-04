(** * Fib : Fibonacci sequence and decomposition *)

Require Import Arith Omega Wf_nat List.
Require Import DeltaList.
Import ListNotations.
Set Implicit Arguments.

(** * Generalized Fibonacci sequence *)

Fixpoint A (k n : nat) :=
  match n with
  | O => 1
  | S n => A k n + A k (n-k)
  end.

Definition test := List.seq 0 10.

Compute map (A 0) test. (* [1; 2; 4; 8; 16; 32; 64; 128; 256; 512] *)
Compute map (A 1) test. (* [1; 2; 3; 5; 8; 13; 21; 34; 55; 89] *)
Compute map (A 2) test. (* [1; 2; 3; 4; 6; 9; 13; 19; 28; 41] *)
Compute map (A 3) test. (* [1; 2; 3; 4; 5; 7; 10; 14; 19; 26] *)

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
 replace (n-k) with 0 by omega. simpl.
 rewrite IHn; omega.
Qed.

Lemma A_sum k n : n<>0 -> A k n = A k (n-1) + A k (n-S k).
Proof.
 destruct n.
 - now destruct 1.
 - intros _. simpl; rewrite Nat.sub_0_r; auto.
Qed.

Lemma A_sum' k n : A k (n+S k) = A k n + A k (n+k).
Proof.
 intros.
 rewrite A_sum by omega.
 rewrite Nat.add_comm. f_equal; f_equal; omega.
Qed.

Lemma A_k_1 k : A k 1 = 2.
Proof.
 reflexivity.
Qed.

Lemma A_0_pow2 n : A 0 n = 2^n.
Proof.
 induction n.
 - reflexivity.
 - rewrite A_S, Nat.sub_0_r. simpl. omega.
Qed.

Lemma A_nz k n : 1 <= A k n.
Proof.
 induction n; simpl; auto with arith.
Qed.

Lemma A_lt_S k n : A k n < A k (S n).
Proof.
 simpl. generalize (A_nz k (n-k)). omega.
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
  apply (A_lt k) in LT; omega.
Qed.

Lemma A_lt_inv k n n' : A k n < A k n' -> n < n'.
Proof.
 intros.
 destruct (le_lt_dec n' n) as [LE|LT]; trivial.
 apply (A_mono k) in LE. omega.
Qed.

Lemma A_lt_id k n : n < A k n.
Proof.
 induction n; simpl; auto.
 generalize (A_nz k (n-k)). omega.
Qed.

Lemma A_inv k n : { p | A k p <= S n < A k (S p) }.
Proof.
 induction n as [|n IH].
 - exists 0. auto.
 - destruct IH as (p,Hp).
   destruct (Nat.eq_dec (S (S n)) (A k (S p))) as [->|N].
   + exists (S p). split; trivial. apply A_lt_S.
   + exists p. omega.
Defined.

Lemma A_inv' k n : n<>0 -> { p | A k p <= n < A k (S p) }.
Proof.
 destruct n.
 - now destruct 1.
 - intros _. apply A_inv.
Defined.

Compute proj1_sig (A_inv 2 10).
Compute A 2 5.
Compute A 2 6.

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

Lemma sumA_eqn k l :
 sumA k l + sumA k (map (decr k) l) = sumA k (map S l).
Proof.
 induction l; trivial.
 simpl map. rewrite !sumA_cons, <- IHl, A_S.
 unfold decr at 1. omega.
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
 rewrite (@A_sum k a); omega.
Qed.

Lemma map_decr k l :
 map (decr (S k)) l = map (decr k) (map (decr 1) l).
Proof.
 rewrite map_map.
 apply map_ext.
 intros. unfold decr. omega.
Qed.

Lemma sumA_app k l l' : sumA k (l++l') = sumA k l + sumA k l'.
Proof.
 revert l'.
 induction l; intros.
 - trivial.
 - simpl. rewrite IHl. omega.
Qed.

Lemma sumA_rev k l : sumA k (rev l) = sumA k l.
Proof.
 induction l.
 - trivial.
 - simpl. rewrite sumA_app, IHl. simpl. omega.
Qed.

Lemma sumA_0 k l : sumA k l = 0 <-> l = [].
Proof.
 split.
 - intros H. destruct l; [ now elim H |].
   simpl in *. generalize (A_nz k n). omega.
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
   + apply A_mono; omega.
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
   { generalize (A_nz k p); omega. }
   exists (p::l); simpl; split; try omega.
   destruct l as [|p' l]; trivial.
   constructor; trivial.
   assert (p' < p - k); [|omega].
   apply (A_lt_inv k).
   simpl in EQ. rewrite A_S in Hp. omega.
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
 - intros _ Hn'. simpl in *. generalize (A_nz k n'); omega.
 - intros Hn _. simpl in *. generalize (A_nz k n); omega.
 - intros DR DR' EQ.
   assert (n < S n').
   { apply (A_lt_inv k). simpl in EQ.
     apply le_lt_trans with (A k n' + sumA k l'); [omega|].
     now apply decomp_max. }
   assert (n' < S n).
   { apply (A_lt_inv k). simpl in EQ.
     apply le_lt_trans with (A k n + sumA k l); [omega|].
     now apply decomp_max. }
   replace n' with n in * by omega. clear H H0.
   simpl in EQ.
   f_equal.
   apply IH; clear IH; simpl in *; try omega; intuition.
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
 apply decomp_delta.
 rewrite <- Eq. apply decomp_sum.
Qed.


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

Compute renorm 1 [0;1;3;4;5;7].
Compute renorm 2 [1;3;5;8].

Lemma renorm_loop_length k l n :
  length l <= n -> length (renorm_loop k l n) <= length l.
Proof.
 revert l.
 induction n; simpl; auto with arith.
 intros [|p l] LE; simpl in *; auto.
 apply Nat.succ_le_mono in LE.
 assert (Hl := IHn l LE).
 destruct renorm_loop as [|p' l']. simpl in *; try omega.
 case Nat.eqb_spec; intros; simpl in *; try omega.
 etransitivity; try eapply IHn; simpl; omega.
Qed.

Lemma renorm_length k l : length (renorm k l) <= length l.
Proof.
 unfold renorm. now apply renorm_loop_length.
Qed.

Lemma renorm_loop_sum k l n :
  length l <= n -> sumA k (renorm_loop k l n) = sumA k l.
Proof.
 revert l.
 induction n; intros [|p l]; simpl; auto.
 - inversion 1.
 - intros LE. apply Nat.succ_le_mono in LE.
   assert (Hl := IHn l LE).
   assert (L := renorm_loop_length k l LE).
   destruct renorm_loop as [|p' l']; simpl in *; try omega.
   case Nat.eqb_spec; simpl in *; intros; try omega.
   rewrite IHn by (simpl;omega). simpl.
   replace (p'-k) with p; omega.
Qed.

Lemma renorm_sum k l : sumA k (renorm k l) = sumA k l.
Proof.
 unfold renorm. now apply renorm_loop_sum.
Qed.

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
       destruct renorm_loop; simpl in *; try omega.
       destruct IHn as (m,E); try omega.
       exists (S m). simpl. omega.
     * exists 0; omega.
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
 - apply IHn; simpl; auto; omega.
 - destruct l as [|x l]; simpl in *; [intuition|].
   destruct Hd as (m,Hd).
   constructor; auto.
   assert (p+k <= x). { apply IN; auto. }
   zify; omega.
Qed.

Lemma renorm_delta k l : Delta k l -> Delta (S k) (renorm k l).
Proof.
 unfold renorm. now apply renorm_loop_delta.
Qed.

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
     destruct D as (_,IN'). specialize (IN' y Hy). omega.
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
   + rewrite IHn by (simpl; omega).
     subst p'. rewrite <- H.
     rewrite <- Nat.add_succ_r. simpl.
     rewrite Nat.add_assoc. f_equal.
     unfold decr.
     rewrite A_sum by omega.
     rewrite Nat.add_comm. f_equal; f_equal; omega.
   + now rewrite <- H.
Qed.

Lemma renorm_mapdecr k m l : m < S k ->
  sumA k (map (decr m) (renorm k l)) = sumA k (map (decr m) l).
Proof.
 unfold renorm. intros. now apply renorm_loop_mapdecr.
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
   replace (a-k) with 0; simpl; omega.
Qed.

(** ** Classification of decompositions *)

Definition low k n :=
  match decomp k n with
  | [] => None
  | p :: _ => Some p
  end.

Definition Low k n p :=
 exists l, n = sumA k (p::l) /\ Delta (S k) (p::l).

(** ** Decomposition of the predecessor of a Ak number

   [(A k n) - 1 = A k (n-1) + A k (n-1-S k) + ... + A k (n-1-p*(S k))]

   with [p] such that [n-1-p*(S k)] is in [0..k].
   i.e. [p = (n-1)/(S k)]
*)

Lemma decompred_spec_rev k n :
  { l | sumA k l = A k n - 1 /\
        DeltaRev (S k) l /\
        forall p, In p l -> p < n }.
Proof.
 induction n as [n IH] using lt_wf_rec.
 destruct (Nat.eq_dec n 0) as [EQ|NE].
 - exists []; subst; simpl; repeat split; intuition.
 - destruct (le_lt_dec n (S k)) as [LE|LT].
   + exists [n-1]; simpl; repeat split; intuition.
     rewrite 2 A_base; omega.
   + destruct (IH (n-S k)) as (l & SUM & DR & IN) ; try omega.
     exists (n-1::l); simpl; repeat split; auto.
     * rewrite SUM. rewrite (@A_sum k n) by omega.
       generalize (A_nz k (n - S k)). omega.
     * apply DeltaRev_alt. split; auto.
       intros y Hy. specialize (IN y Hy). omega.
     * intros y [Hy|Hy]; try specialize (IN y Hy); omega.
Defined.

Lemma decompred_spec k n :
  { l | sumA k l = A k n - 1 /\
        Delta (S k) l /\
        forall p, In p l -> p < n }.
Proof.
 destruct (decompred_spec_rev k n) as (l & SUM & DR & IN).
 exists (rev l); repeat split.
 - now rewrite sumA_rev.
 - now apply Delta_rev.
 - intros p. rewrite <- in_rev; now apply IN.
Defined.

Definition decompred k n := proj1_sig (decompred_spec k n).

Compute decompred 0 10.
Compute decompred 1 10.
Compute decompred 1 9.
Compute decompred 2 10.

Lemma decompred_sum k n :
  sumA k (decompred k n) = A k n - 1.
Proof.
 unfold decompred; destruct decompred_spec; simpl; intuition.
Qed.

Lemma decompred_delta k n : Delta (S k) (decompred k n).
Proof.
 unfold decompred; destruct decompred_spec; simpl; intuition.
Qed.

Lemma decompred_in k n p : In p (decompred k n) -> p < n.
Proof.
 unfold decompred; destruct decompred_spec; simpl; intuition.
Qed.
