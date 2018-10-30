(** * Fib : Fibonacci sequence and decomposition *)

Require Import Arith Omega Wf_nat List Recdef.
Require Import DeltaList.
Import ListNotations.
Set Implicit Arguments.

(** * Generalized Fibonacci sequence *)

Function A (k n : nat) { measure id n } : nat :=
  if n <=? S k then n
  else A k (n-1) + A k (n-S k).
Proof.
 - intros; unfold id. rewrite Nat.leb_gt in *. omega.
 - intros; unfold id. rewrite Nat.leb_gt in *. omega.
Defined.

Definition test := List.seq 0 10.

Compute map (A 0) test. (* [0; 1; 2; 4; 8; 16; 32; 64; 128; 256] *)
Compute map (A 1) test. (* [0; 1; 2; 3; 5; 8; 13; 21; 34; 55] *)
Compute map (A 2) test. (* [0; 1; 2; 3; 4; 6; 9; 13; 19; 28] *)
Compute map (A 3) test. (* [0; 1; 2; 3; 4; 5; 7; 10; 14; 19] *)

Lemma A_base k n : n <= S k -> A k n = n.
Proof.
 functional induction A k n; auto.
 rewrite Nat.leb_gt in *. intros. omega.
Qed.

Lemma A_sum k n : S k < n -> A k n = A k (n-1) + A k (n-S k).
Proof.
 functional induction A k n; auto.
 rewrite Nat.leb_le in *. intros. omega.
Qed.

Lemma A_sum' k n : n<>0 -> A k (n+S k) = A k n + A k (n+k).
Proof.
 intros.
 remember (n+S k) as N.
 replace (n+k) with (N-1) by omega.
 replace n with (N-S k) by omega.
 rewrite Nat.add_comm.
 apply A_sum. omega.
Qed.

Lemma A_S k n : k<n -> A k (S n) = A k n + A k (n-k).
Proof.
 intros.
 rewrite A_sum, Nat.sub_succ, Nat.sub_0_r; auto with arith.
Qed.

Lemma A_k_1 k : A k 1 = 1.
Proof.
 rewrite !A_base; auto with arith.
Qed.

Lemma A_base' k n : n <= S (S k) -> A k n = n.
Proof.
 intros H. apply Nat.lt_eq_cases in H. destruct H.
 - apply A_base; omega.
 - rewrite A_sum by omega.
   replace (n - S k) with 1 by omega. rewrite A_k_1.
   rewrite !A_base; omega.
Qed.

Lemma A_0_pow2 n : A 0 (S n) = 2^n.
Proof.
 induction n.
 - reflexivity.
 - rewrite A_sum. simpl Nat.sub. rewrite IHn. simpl. omega.
   omega.
Qed.

Lemma A_nz k n : n<>0 -> 1 <= A k n.
Proof.
 functional induction A k n.
 - omega.
 - rewrite Nat.leb_gt in *. omega.
Qed.

Lemma A_0_inv k n : A k n = 0 -> n = 0.
Proof.
 generalize (@A_nz k n). omega.
Qed.

Lemma A_lt_S k n : A k n < A k (S n).
Proof.
 destruct (le_lt_dec n k).
 - rewrite !A_base; omega.
 - rewrite A_S by omega.
   generalize (@A_nz k (n-k)). omega.
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
  apply (@A_lt k) in LT; omega.
Qed.

Lemma A_lt_inv k n n' : A k n < A k n' -> n < n'.
Proof.
 intros.
 destruct (le_lt_dec n' n) as [LE|LT]; trivial.
 apply (@A_mono k) in LE. omega.
Qed.

Lemma A_le_id k n : n <= A k n.
Proof.
 functional induction A k n; trivial.
 rewrite Nat.leb_gt in *.
 generalize (@A_nz k (n-S k)). omega.
Qed.

Lemma A_inv k n : { p | A k p <= n < A k (S p) }.
Proof.
 induction n as [|n IH].
 - exists 0. auto.
 - destruct IH as (p,Hp).
   destruct (Nat.eq_dec (S n) (A k (S p))) as [->|N].
   + exists (S p). split; trivial. apply A_lt_S.
   + exists p. omega.
Defined.

(*
Compute proj1_sig (A_inv 2 10).
Compute A 2 6.
Compute A 2 7.
*)

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

Definition flipsub x y := Nat.sub y x.

Lemma sumA_eqn k l :
 (forall n, In n l -> k < n) ->
 sumA k l + sumA k (map (flipsub k) l) = sumA k (map S l).
Proof.
 induction l; trivial.
 intros H. simpl map. rewrite !sumA_cons, <- IHl by intuition.
 rewrite A_S.
 unfold flipsub at 1. omega.
 specialize (H a). intuition.
Qed.

Lemma sumA_eqn' k l : (forall n, In n l -> k < n) ->
 sumA k (map S l) - sumA k (map (flipsub k) l) = sumA k l.
Proof.
 intros. rewrite <- sumA_eqn; auto. apply Nat.add_sub.
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

Lemma sumA_0 k l : ~In 0 l -> (sumA k l = 0 <-> l = []).
Proof.
 intro N. split.
 - intros H. destruct l; [ now elim H |].
   simpl in *. generalize (@A_nz k n). omega.
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
   rewrite A_S by omega.
   apply Nat.add_lt_mono_l.
   apply lt_le_trans with (A k (S a)).
   + apply IHl; auto.
   + apply A_mono; omega.
Qed.

(** Zeckendorf's Theorem, in a variant that consider
    decompositions with largest terms first
    (easiest for the proof). *)

Lemma decomp_exists_rev k n :
  { l | sumA k l = n /\ DeltaRev (S k) l /\ ~In 0 l }.
Proof.
 induction n as [n IH] using lt_wf_rec.
 destruct (Nat.eq_dec n 0) as [EQ|NE].
 - subst. exists []. simpl; intuition.
 - destruct (A_inv k n) as (p,Hp).
   assert (Hp' : p<>0). { intro; subst p; compute in Hp; omega. }
   destruct (le_lt_dec p (S k)) as [LE|LT].
   + rewrite 2 A_base' in Hp by omega.
     exists [p]. simpl. rewrite A_base by omega.
     intuition.
   + destruct (IH (n - A k p)) as (l & EQ & DR & NI).
     { generalize (@A_nz k p); omega. }
     destruct l as [|p' l]; simpl in EQ.
     * exists [p]; simpl; repeat split; try constructor; omega.
     * exists (p::p'::l); simpl; simpl in NI; intuition.
       constructor; trivial.
       rewrite A_S in H0 by omega.
       assert (A k p' < A k (p - k)) by omega.
       apply A_lt_inv in H3. omega.
Qed.

Lemma decomp_unique_rev k l l' :
 ~In 0 l -> DeltaRev (S k) l ->
 ~In 0 l' -> DeltaRev (S k) l' ->
 sumA k l = sumA k l' -> l = l'.
Proof.
 revert l'.
 induction l as [|n l IH]; destruct l' as [|n' l'].
 - trivial.
 - intros _ _ Hn' _. simpl in *. generalize (@A_nz k n'); omega.
 - intros Hn _ _ _. simpl in *. generalize (@A_nz k n); omega.
 - intros N0 DR N0' DR' EQ.
   assert (n < S n').
   { apply (@A_lt_inv k). simpl in EQ.
     apply le_lt_trans with (A k n' + sumA k l'); [omega|].
     now apply decomp_max. }
   assert (n' < S n).
   { apply (@A_lt_inv k). simpl in EQ.
     apply le_lt_trans with (A k n + sumA k l); [omega|].
     now apply decomp_max. }
   replace n' with n in * by omega. clear H H0.
   simpl in EQ.
   f_equal.
   apply IH; clear IH; simpl in *; try omega; intuition.
   + apply DeltaRev_alt in DR. intuition.
   + apply DeltaRev_alt in DR'. intuition.
Qed.

(** Same theorem, in the other order (smallest term first). *)

Lemma decomp_exists k n :
  { l | sumA k l = n /\ Delta (S k) l /\ ~In 0 l }.
Proof.
 destruct (decomp_exists_rev k n) as (l & Hn & Hl & N0).
 exists (rev l); repeat split.
 - now rewrite sumA_rev.
 - now apply Delta_rev.
 - now rewrite <- in_rev.
Qed.

Lemma decomp_unique k l l' :
 Delta (S k) l -> Delta (S k) l' -> ~In 0 l -> ~In 0 l' ->
 sumA k l = sumA k l' -> l = l'.
Proof.
 intros D D' IN IN' EQ.
 assert (rev l = rev l').
 { apply (@decomp_unique_rev k);
   rewrite <- ?in_rev, ?DeltaRev_rev, ?sumA_rev; trivial. }
 rewrite <- (rev_involutive l), <- (rev_involutive l').
 now f_equal.
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

    Moreover, the lowest term in the decomposition grows
    (or stays equal).
*)

Definition HeadLe l l' := match l, l' with
| [], [] => True
| 0::_, _ => True
| p::_, p'::_ => p <= p'
| _, _ => False
end.

Lemma renorm_spec k l :
 { l' | sumA k l' = sumA k l /\
        length l' <= length l /\
        (Delta k l -> Delta (S k) l') /\
        HeadLe l l' }.
Proof.
 remember (length l) as n eqn:Hn. revert l Hn.
 induction n as [n IH] using lt_wf_rec.
 destruct l as [|p l].
 - exists (@nil nat); repeat split; subst; auto.
 - intros Hn. simpl in Hn.
   assert (Hn' : length l < n) by omega.
   destruct (IH (length l) Hn' l) as (l' & Eq & Le & St & Hd); trivial.
   destruct (Nat.eq_dec p 0) as [E|N].
   + exists l'; repeat split; subst; simpl; auto.
     inversion 1; subst; auto.
   + destruct l' as [|p' l'].
     * exists [p].
       simpl in *. repeat split; subst; auto with arith.
       destruct p; auto.
     * assert (Delta k (p::l) -> p + k <= p').
       { intros Hl.
         destruct l as [|x l0]. elim Hd. simpl in Hd.
         apply Delta_alt in Hl. destruct Hl as (Hl,Hl').
         specialize (Hl' x). simpl in Hl'.
         transitivity x; auto.
         destruct x; auto with arith. }
       destruct (Nat.eq_dec (p + k) p') as [E'|N'].
       { assert (Lt : length (S p' :: l') < n).
         { simpl in *; omega. }
         destruct (IH _ Lt (S p' :: l')) as (l'' & Eq' & Le' & St' & Hd');
         trivial; clear IH.
         exists l''; repeat split; auto.
         { rewrite Eq'. simpl. rewrite <- Eq. simpl.
           rewrite A_S by omega.
           replace (p'-k) with p; omega. }
         { simpl in *; omega. }
         { intros Hl.
           apply St'.
           rewrite Delta_alt in St, Hl.
           apply Delta_alt. split.
           - apply Delta_more with (S k); auto. apply St, Hl.
           - intros y Hy. apply St in Hy; [|apply Hl]. omega. }
         { destruct l'' as [|x3 l3]. elim Hd'. simpl in Hd'.
           simpl. destruct p; auto. omega. } }
       { exists (p::p'::l'); repeat split; simpl in *; auto.
         { omega. }
         { intros Hl.
           specialize (H Hl).
           constructor. omega. eauto. }
         { destruct p; auto. } }
Defined.

Definition renorm k l := let (l',_) := renorm_spec k l in l'.

Compute renorm 1 [2;3;4;5].
Compute renorm 2 [1;3;5;7].

Lemma renorm_sum k l : sumA k (renorm k l) = sumA k l.
Proof.
 unfold renorm. destruct renorm_spec. intuition.
Qed.

Lemma renorm_ok k l : Delta k l -> Delta (S k) (renorm k l).
Proof.
 unfold renorm. destruct renorm_spec. intuition.
Qed.

Lemma renorm_hd k l : HeadLe l (renorm k l).
Proof.
 unfold renorm. destruct renorm_spec. intuition.
Qed.

Lemma renorm_le k x l : Delta k (x::l) ->
  forall y, In y (renorm k (x::l)) -> x <= y.
Proof.
 intros H y Hy.
 apply renorm_ok in H.
 assert (Hd := renorm_hd k (x::l)).
 destruct (renorm k (x::l)) as [|k' l'].
 - elim Hy.
 - simpl in Hd.
   destruct x; auto with arith.
   assert (x <= k') by omega.
   simpl in Hy. destruct Hy as [Hy|Hy]; try omega.
   transitivity k'; auto.
   apply Delta_alt in H. apply H in Hy. omega.
Qed.

(** ** Classification of decompositions *)

Definition Low k d n p :=
 exists l, n = sumA k (p::l) /\ Delta d (p::l).

(** ** Decomposition of the predecessor of a Ak number

   [(A k n) - 1 = A k (n-1) + A k (n-1-S k) + ... + A k (n-1-p*(S k))]

   with [p] such that [n-1-p*(S k)] is in [1..S k].
   i.e. [p = (n-2)/(S k)]
*)

Lemma decompred_spec_rev k n :
  { l | sumA k l = A k n - 1 /\
        DeltaRev (S k) l /\
        forall p, In p l -> 0 < p < n }.
Proof.
 induction n as [n IH] using lt_wf_rec.
 destruct (le_lt_dec n 1) as [LE|LT].
 - exists []; subst; simpl; repeat split; intuition.
   apply (A_mono k) in LE. rewrite A_k_1 in LE. omega.
 - destruct (le_lt_dec n (k+2)) as [LE'|LT'].
   + exists [n-1]; simpl; repeat split; intuition.
     rewrite 2 A_base'; omega.
   + destruct (IH (n-S k)) as (l & SUM & DR & IN) ; try omega.
     exists (n-1::l); simpl; repeat split; auto.
     * rewrite SUM. rewrite (@A_sum k n) by omega.
       generalize (@A_nz k (n - S k)). omega.
     * apply DeltaRev_alt. split; auto.
       intros y Hy. specialize (IN y Hy). omega.
     * destruct H. omega. specialize (IN p H). omega.
     * destruct H. omega. specialize (IN p H). omega.
Defined.

Lemma decompred_spec k n :
  { l | sumA k l = A k n - 1 /\
        Delta (S k) l /\
        forall p, In p l -> 0 < p < n }.
Proof.
 destruct (decompred_spec_rev k n) as (l & SUM & DR & IN).
 exists (rev l); repeat split.
 - now rewrite sumA_rev.
 - now apply Delta_rev.
 - rewrite <- in_rev in *; now apply IN.
 - rewrite <- in_rev in *; now apply IN.
Defined.

Definition decompred k n :=
  let (l,_) := decompred_spec k n in l.

Compute decompred 0 10.
Compute decompred 1 10.
Compute decompred 1 9.
Compute decompred 2 10.

Lemma decompred_sum k n :
  sumA k (decompred k n) = A k n - 1.
Proof.
 unfold decompred; destruct (decompred_spec k n); intuition.
Qed.

Lemma decompred_ok k n : Delta (S k) (decompred k n).
Proof.
 unfold decompred; destruct (decompred_spec k n); intuition.
Qed.

Lemma decompred_in k n p : In p (decompred k n) -> 0 < p < n.
Proof.
 unfold decompred; destruct (decompred_spec k n) as (l & _ & _ & IN).
 apply IN.
Qed.
