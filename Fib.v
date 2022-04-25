(** * Fib : Fibonacci sequence and decomposition *)

Require Import Arith Lia List.
Require Import DeltaList.
Import ListNotations.
Set Implicit Arguments.

(** * Fibonacci sequence

    First, a definition of the Fibonacci sequence.
    We use the standard definition that starts with 0 1 1 2 3 ...
    (See OEIS A000045).

    Note: an earlier version of this development was using
    a shifted Fibonacci sequence, without its initial 0
    (e.g. fib(0)=1, fib(1)=1, fib(2)=2, ...). This was
    convenient during some Coq proofs, but confusing for
    external readers, so we migrated back to the standard
    definition (with little overhead to the proofs, btw).
*)

Fixpoint fib (n:nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' => fib n' + fib n''
    end
  end.

Lemma fib_eqn n : fib (S (S n)) = fib (S n) + fib n.
Proof.
 reflexivity.
Qed.

Lemma fib_eqn' n : n<>0 -> fib (S n) = fib n + fib (n-1).
Proof.
 destruct n.
 - now destruct 1.
 - intros _. replace (S n - 1) with n by lia.
   apply fib_eqn.
Qed.

Lemma fib_S_nz k : 1 <= fib (S k).
Proof.
 induction k as [|k IH]; trivial.
 rewrite fib_eqn. lia.
Qed.

Lemma fib_nz k : k<>0 -> 1 <= fib k.
Proof.
 destruct k.
 - now destruct 1.
 - intros _. apply fib_S_nz.
Qed.

Lemma fib_0_inv k : fib k = 0 -> k = 0.
Proof.
 generalize (@fib_nz k). lia.
Qed.

Lemma fib_lt_S k : 1 < k -> fib k < fib (S k).
Proof.
 intro. rewrite fib_eqn' by lia.
 generalize (@fib_nz (k-1)). lia.
Qed.

Lemma fib_lt k k' : 1 < k -> k < k' -> fib k < fib k'.
Proof.
 induction 2.
 - apply fib_lt_S; lia.
 - transitivity (fib m); trivial. apply fib_lt_S; lia.
Qed.

Lemma fib_mono_S k : fib k <= fib (S k).
Proof.
 destruct k. simpl; auto. rewrite fib_eqn. lia.
Qed.

Lemma fib_mono k k' : k <= k' -> fib k <= fib k'.
Proof.
 induction 1; trivial.
 transitivity (fib m); trivial. apply fib_mono_S.
Qed.

Lemma fib_inj k k' : 1<k -> 1<k' -> fib k = fib k' -> k = k'.
Proof.
 intros.
 destruct (lt_eq_lt_dec k k') as [[LT|EQ]|LT]; trivial;
  apply fib_lt in LT; lia.
Qed.

Lemma fib_lt_inv k k' : fib k < fib k' -> k < k'.
Proof.
 intros.
 destruct (le_lt_dec k' k) as [LE|LT]; trivial.
 apply fib_mono in LE. lia.
Qed.

Lemma fib_le_id k : k <= S (fib k).
Proof.
 induction k as [|[|[|k]] IH].
 - simpl; auto.
 - simpl; auto.
 - simpl; auto.
 - rewrite fib_eqn. generalize (fib_S_nz k). lia.
Qed.

Lemma fib_inv n : { k | fib k <= n < fib (S k) }.
Proof.
 induction n as [|[|n] IH].
 - exists 0. auto.
 - exists 2. auto.
 - destruct IH as (k,Hk).
   destruct (eq_nat_dec (S (S n)) (fib (S k))) as [->|N].
   + exists (S k).
     rewrite fib_eqn. split; trivial.
     assert (k<>0). { intros ->. simpl in *. lia. }
     generalize (@fib_nz k); lia.
   + exists k. lia.
Defined.


(** * Decomposition via sums of Fibonacci numbers.

    Zeckendorf's theorem (actually discovered earlier by
    Lekkerkerker) states that any natural number can be obtained
    by a sum of distinct Fibonacci numbers, and this decomposition
    is moreover unique when :
     - [fib 0] and [fib 1] aren't in the decomposition
     - Fibonacci numbers in the decomposition aren't consecutive.
*)

(** ** The [sumfib] function

   We represent a Fibonacci decomposition by the list of ranks
   of the Fibonacci numbers in this decomposition.
   The sumfib function is the sum of the Fibonacci numbers of
   these ranks. For the first results below, the ranks may be
   arbitrary : redundant, in any order, ... *)

Definition sumfib l := fold_right (fun n acc => fib n + acc) 0 l.

Lemma sumfib_cons a l : sumfib (a::l) = fib a + sumfib l.
Proof.
 reflexivity.
Qed.

Lemma sumfib_eqn l :
 ~In 0 l ->
 sumfib l + sumfib (map pred l) = sumfib (map S l).
Proof.
 induction l; trivial.
 intros N. simpl in N.
 simpl map. rewrite !sumfib_cons, <-IHl by intuition.
 rewrite fib_eqn' by intuition.
 rewrite Nat.sub_1_r. lia.
Qed.

Lemma sumfib_eqn' l : ~In 0 l ->
 sumfib (map S l) - sumfib (map pred l) = sumfib l.
Proof.
 intros. rewrite <- sumfib_eqn; auto. apply Nat.add_sub.
Qed.

Lemma sumfib_app l l' : sumfib (l++l') = sumfib l + sumfib l'.
Proof.
 revert l'.
 induction l; intros.
 - trivial.
 - simpl. rewrite IHl. lia.
Qed.

Lemma sumfib_rev l : sumfib (rev l) = sumfib l.
Proof.
 induction l.
 - trivial.
 - simpl. rewrite sumfib_app, IHl. simpl. lia.
Qed.

Lemma sumfib_0 l : ~In 0 l -> (sumfib l = 0 <-> l = []).
Proof.
 intro N. split.
 - intros H. destruct l; [ now elim H |].
   simpl in *. generalize (@fib_nz n). lia.
 - intros; now subst.
Qed.

(** ** Zeckendorf's Theorem *)

(** Technical lemma:
    A canonical decomposition cannot excess the next Fibonacci. *)

Lemma decomp_max k l :
  ~In 1 (k::l) -> DeltaRev 2 (k::l) -> sumfib (k::l) < fib (S k).
Proof.
 revert k.
 induction l.
 - intros k Hk _. simpl in Hk. simpl sumfib. rewrite Nat.add_0_r.
   destruct k; auto. apply fib_lt_S. intuition; lia.
 - intros k Hk.
   inversion 1; subst. simpl sumfib.
   rewrite fib_eqn' by lia. apply Nat.add_lt_mono_l.
   apply lt_le_trans with (fib (S a)).
   + apply IHl; auto. simpl in Hk. simpl; intuition.
   + apply fib_mono; lia.
Qed.

(** Zeckendorf's Theorem, in a variant that consider
    decompositions with largest terms first
    (easiest for the proof). *)

Lemma decomp_exists_rev n :
  { l | sumfib l = n /\ DeltaRev 2 l /\ ~In 0 l /\ ~In 1 l }.
Proof.
 induction n as [n IH] using lt_wf_rec.
 destruct (eq_nat_dec n 0) as [EQ|NE].
 - subst. exists (@nil nat). simpl; intuition.
 - destruct (fib_inv n) as (k,Hk).
   assert (Hk' : k<>0). { intro; subst k; compute in Hk; lia. }
   assert (Hk'' : k<>1). { intro; subst k; compute in Hk; lia. }
   destruct (IH (n - fib k)) as (l & EQ & DR & NI).
   { generalize (@fib_nz k); lia. }
   destruct l as [|k' l]; simpl in EQ.
   + exists (k::nil); simpl; repeat split; try constructor; lia.
   + exists (k::k'::l); simpl; simpl in NI; repeat split.
     * lia.
     * constructor; trivial.
       rewrite fib_eqn' in Hk by trivial.
       assert (k' < k-1); try lia.
       { apply Nat.lt_nge. intro LE. apply fib_mono in LE. lia. }
     * intuition.
     * intuition.
Defined.

Lemma decomp_unique_rev l l' :
 ~In 0 l -> ~In 1 l -> DeltaRev 2 l ->
 ~In 0 l' -> ~In 1 l' -> DeltaRev 2 l' ->
 sumfib l = sumfib l' -> l = l'.
Proof.
 revert l'.
 induction l as [|n l IH]; destruct l' as [|n' l'].
 - trivial.
 - intros _ _ _ Hn' _ _. simpl in *. generalize (@fib_nz n'); lia.
 - intros Hn _ _ _ _ _. simpl in *. generalize (@fib_nz n); lia.
 - intros N0 N1 DR N0' N1' DR' EQ.
   assert (n < S n').
   { apply fib_lt_inv. simpl in EQ.
     apply le_lt_trans with (fib n' + sumfib l'); [lia|].
     now apply decomp_max. }
   assert (n' < S n).
   { apply fib_lt_inv. simpl in EQ.
     apply le_lt_trans with (fib n + sumfib l); [lia|].
     now apply decomp_max. }
   replace n' with n in * by lia. clear H H0.
   simpl in EQ.
   f_equal.
   apply IH; clear IH; simpl in *; try lia; intuition.
   + apply DeltaRev_alt in DR. intuition.
   + apply DeltaRev_alt in DR'. intuition.
Qed.

(** Same theorem, in the other order (smallest term first). *)

Lemma decomp_exists n :
  { l | sumfib l = n /\ Delta 2 (0::l) }.
Proof.
 destruct (decomp_exists_rev n) as (l & Hn & Hl & N0 & N1).
 exists (rev l); repeat split.
 - now rewrite sumfib_rev.
 - apply Delta_alt; split.
   + now apply Delta_rev.
   + intros y. rewrite <- in_rev. do 2 (destruct y; intuition); lia.
Defined.

Lemma decomp_unique l l' :
 Delta 2 (0::l) -> Delta 2 (0::l') ->
 sumfib l = sumfib l' -> l = l'.
Proof.
 rewrite !Delta_alt; intros (D,IN) (D',IN') EQ.
 assert (rev l = rev l').
 { apply decomp_unique_rev;
   rewrite <- ?in_rev, ?DeltaRev_rev, ?sumfib_rev; trivial.
   - intro H0. apply IN in H0. lia.
   - intro H1. apply IN in H1. lia.
   - intro H0. apply IN' in H0. lia.
   - intro H1. apply IN' in H1. lia. }
 rewrite <- (rev_involutive l), <- (rev_involutive l').
 now f_equal.
Qed.

Definition decomp n := proj1_sig (decomp_exists n).

Lemma decomp_sumfib n : sumfib (decomp n) = n.
Proof.
 unfold decomp. now destruct decomp_exists as (l & E & D).
Qed.

Lemma decomp_ok n : Delta 2 (0::decomp n).
Proof.
 unfold decomp. now destruct decomp_exists as (l & E & D).
Qed.

Lemma decomp_spec n l : sumfib l = n -> Delta 2 (0::l) -> decomp n = l.
Proof.
 intros E D. apply decomp_unique; auto. apply decomp_ok.
 rewrite E. apply decomp_sumfib.
Qed.

(** ** Normalisation of a Fibonacci decomposition.

    Starting from an increasing decomposition, we can
    transform it into a canonical decomposition (with no
    consecutive Fibonacci numbers), by simply saturating
    the basic Fibonacci equation [fib k + fib (k+1) = fib (k+2)]
    in the right order (highest terms first).

    Termination isn't obvious for Coq, since we might have
    to re-launch normalisation on by-products of a first
    normalisation. The number of terms in the decomposition
    decreases strictly during the process, we use that to
    justify the termination.

    Moreover, the lowest term in the decomposition grows
    (or stays equal), and the parity of its rank is preserved.
    This is expressed by the HeadLeEven predicate below.
*)

Definition HeadLeEven l l' := match l, l' with
| [], [] => True
| k::_, k'::_ => exists p, k' = k + 2*p
| _, _ => False
end.

Lemma norm_spec l :
 { l' | sumfib l' = sumfib l /\
        (Delta 1 l -> Delta 2 l') /\
        length l' <= length l /\
        HeadLeEven l l' }.
Proof.
 remember (length l) as n eqn:Hn. revert l Hn.
 induction n as [n IH] using lt_wf_rec.
 destruct l as [|k l].
 - exists (@nil nat); repeat split; subst; auto.
 - intros Hn. simpl in Hn.
   assert (Hn' : length l < n) by lia.
   destruct (IH (length l) Hn' l) as (l' & Eq & St & Le & Hd);
    trivial.
   destruct l' as [|k' l'].
   + exists [k].
     simpl in *. repeat split; subst; auto with arith.
     exists 0. lia.
   + assert (Delta 1 (k::l) -> k < k').
     { intros Hl.
       destruct l as [|x l0]. elim Hd. simpl in Hd. destruct Hd as (p,Hd).
       apply Delta_alt in Hl.
       assert (k+1 <= x) by (apply Hl; now left).
       lia. }
     destruct (eq_nat_dec (S k) k') as [E|N].
     * assert (Lt : length (S k' :: l') < n).
       { simpl in *; lia. }
       destruct (IH _ Lt (S k' :: l')) as (l'' & Eq' & St' & Le' & Hd');
         trivial; clear IH.
       exists l''; repeat split; auto.
       { rewrite Eq'. simpl. rewrite <- Eq. simpl.
         rewrite <- E. lia. }
       { intros Hl.
         apply St'.
         rewrite Delta_alt in St, Hl.
         apply Delta_alt. split.
         - apply Delta_S, St, Hl.
         - intros y Hy. apply St in Hy; [|apply Hl]. lia. }
       { simpl in *; lia. }
       { subst k'.
         destruct l''; simpl in Hd'. elim Hd'.
         destruct Hd' as (p,Hd'). exists (S p). lia. }
     * exists (k::k'::l'); repeat split; simpl in *; auto.
       { intros Hl.
         assert (k<k') by auto.
         constructor; auto. lia.
         eauto. }
       { lia. }
       { exists 0. lia. }
Defined.

Definition norm l := let (l',_) := norm_spec l in l'.

(* For example: Compute norm [2;3;4;5] *)

Lemma norm_sum l : sumfib (norm l) = sumfib l.
Proof.
 unfold norm. destruct norm_spec. intuition.
Qed.

Lemma norm_ok l : Delta 1 l -> Delta 2 (norm l).
Proof.
 unfold norm. destruct norm_spec. intuition.
Qed.

Lemma norm_ok' l : Delta 1 (1::l) -> Delta 2 (0::norm l).
Proof.
 unfold norm. destruct norm_spec as (l' & Eq & St & Ln & Hd).
 intros D.
 destruct l' as [|a l'].
 - intros. constructor.
 - intros. constructor; eauto.
   destruct l; simpl in *; intuition.
   destruct Hd as (p,Hd).
   inversion_clear D. lia.
Qed.

Lemma norm_hd l : HeadLeEven l (norm l).
Proof.
 unfold norm. destruct norm_spec. intuition.
Qed.

Lemma norm_le x l : Delta 1 (x::l) ->
  forall y, In y (norm (x::l)) -> x <= y.
Proof.
 intros H y Hy.
 apply norm_ok in H.
 assert (Hd := norm_hd (x::l)).
 destruct (norm (x::l)) as [|k' l'].
 - elim Hd.
 - simpl in Hd.
   destruct Hd as (p,Hd).
   assert (x <= k') by lia.
   simpl in Hy. destruct Hy as [Hy|Hy]; try lia.
   transitivity k'; auto.
   apply Delta_alt in H. apply H in Hy. lia.
Qed.

(** ** Classification of Fibonacci decompositions

    For a later theorem ([g'_g]), we'll need to classify
    the Fibonacci decompositions according to their lowest
    terms. Is the lowest rank 2, 3 or more ? Is it even or odd ?

    In [Low p n k]:
    - [p] is the delta between ranks in the decomposition (usually 2)
    - [n] is the number we're decomposing
    - [k] is the lowest rank in the decomposition (we force [1<k]).
*)

Definition Low p n k :=
 exists l, n = sumfib (k::l) /\ Delta p (k::l) /\ 1<k.

Definition Two p n := Low p n 2.
Definition Three p n := Low p n 3.
Definition Four p n := Low p n 4.
Definition High p n := exists k, 3 < k /\ Low p n k.

Definition Even p n := exists k, Low p n (2*k).
Definition Odd p n := exists k, Low p n (2*k+1).

(** Some properties of the [Low] predicate *)

Lemma Low_exists n : n<>0 -> exists k, Low 2 n k.
Proof.
 intros.
 destruct (decomp_exists n) as (l & E & L).
 destruct l as [|k l]; simpl in *.
 - congruence.
 - exists k; exists l. repeat split; eauto. now inversion L.
Qed.

Lemma Low_nz p n k : Low p n k -> 1<k.
Proof.
 firstorder.
Qed.

Lemma Low_unique n k k' : Low 2 n k -> Low 2 n k' -> k = k'.
Proof.
 intros (l & E & D & K) (l' & E' & D' & K').
 assert (Eq : k::l = k'::l'); [|now injection Eq].
 { apply decomp_unique; auto. congruence. }
Qed.

Lemma Low_21 n k : Low 2 n k -> Low 1 n k.
Proof.
 firstorder.
Qed.

Lemma Low_12 n k : Low 1 n k -> exists p, Low 2 n (k+2*p).
Proof.
 intros (l & E & D & K).
 rewrite <- norm_sum in E.
 assert (D' := norm_ok D).
 assert (H := norm_hd (k::l)).
 set (l' := norm (k :: l)) in *.
 destruct l' as [|k' l'].
 + elim H.
 + simpl in H. destruct H as (p, H).
   exists p. exists l'. subst; simpl; repeat split; auto. lia.
Qed.

Lemma Low_le p n k : Low p n k -> fib k <= n.
Proof.
 intros (l & -> & _ & _). simpl. lia.
Qed.

(** Properties specialized to [Two], [Three], etc *)

Lemma High_12 n : High 1 n <-> High 2 n.
Proof.
 split; intros (k & K & L).
 - apply Low_12 in L. destruct L as (p,L).
   exists (k+2*p). split; auto. lia.
 - apply Low_21 in L. exists k; auto.
Qed.

Lemma Two_21 n : Two 2 n -> Two 1 n.
Proof.
 apply Low_21.
Qed.

Lemma Two_12 n : Two 1 n -> Two 2 n \/ High 2 n.
Proof.
 intros L. apply Low_12 in L. destruct L as (p,L).
 destruct p.
 - now left.
 - right. exists (2+2*(S p)). split; auto. lia.
Qed.

Lemma Three_21 n : Three 2 n -> Three 1 n.
Proof.
 apply Low_21.
Qed.

Lemma Three_12 n : Three 1 n -> Three 2 n \/ High 2 n.
Proof.
 intros L. apply Low_12 in L. destruct L as (p,L).
 destruct p.
 - now left.
 - right. exists (3+2*(S p)). split; auto. lia.
Qed.

Lemma decomp_complete n : n<>0 -> Two 2 n \/ Three 2 n \/ High 2 n.
Proof.
 intros Hn.
 destruct (Low_exists Hn) as (k,L).
 destruct k as [|[|[|[|k]]]].
 - apply Low_nz in L. now elim L.
 - apply Low_nz in L. lia.
 - now left.
 - now (right; left).
 - right; right. exists (4+k). split; auto. lia.
Qed.

Lemma Two_not_High n : Two 2 n -> ~High 2 n.
Proof.
 intros L (k & K & L').
 assert (k = 2) by (eapply Low_unique; eauto).
 lia.
Qed.

Lemma Two_not_Three n : Two 2 n -> ~Three 2 n.
Proof.
 intros L L'.
 assert (2 = 3) by (eapply Low_unique; eauto). discriminate.
Qed.

Lemma High_not_Three n : High 2 n -> ~Three 2 n.
Proof.
 intros (k & K & L) L'.
 assert (k = 3) by (eapply Low_unique; eauto).
 lia.
Qed.

Lemma Two_not_Three' n : Two 1 n -> ~Three 2 n.
Proof.
 intros L.
 destruct (Two_12 L); auto using Two_not_Three, High_not_Three.
Qed.

Lemma Two_not_Three'' n : Two 1 n -> ~Three 1 n.
Proof.
 intros L L'.
 destruct (Low_12 L) as (p,Lp).
 destruct (Low_12 L') as (p',Lp').
 assert (2+2*p = 3+2*p') by (eapply Low_unique; eauto).
 lia.
Qed.

Lemma High_not_Three' n : High 1 n -> ~Three 2 n.
Proof.
 intros. now apply High_not_Three, High_12.
Qed.

(** Special subdivisions of decompositions starting by 3. *)

Definition ThreeEven p n :=
 exists k l, n = sumfib (3::2*k::l) /\ Delta p (3::2*k::l).
Definition ThreeOdd p n :=
 exists k l, n = sumfib (3::2*k+1::l) /\ Delta p (3::2*k+1::l).

Lemma ThreeOdd_le n : ThreeOdd 2 n -> 6 <= n.
Proof.
 intros (k & l & E & D). subst n. rewrite !sumfib_cons.
 generalize (@fib_mono 5 (2*k+1)).
 inversion_clear D. simpl; lia.
Qed.

Lemma ThreeEven_le n : ThreeEven 2 n -> 7 <= n.
Proof.
 intros (k & l & E & D). subst n. rewrite !sumfib_cons.
 generalize (@fib_mono 6 (2*k)).
 inversion_clear D. simpl; lia.
Qed.

Lemma ThreeEven_Three p n : ThreeEven p n -> Three p n.
Proof.
 firstorder.
Qed.

Lemma ThreeOdd_Three p n : ThreeOdd p n -> Three p n.
Proof.
 firstorder.
Qed.
Hint Resolve ThreeOdd_Three ThreeEven_Three : core.

Lemma Three_split p n : 2<n -> Three p n -> ThreeEven p n \/ ThreeOdd p n.
Proof.
 intros N (l & E & D & _).
 destruct l as [|k l].
 - simpl in E. lia.
 - destruct (Nat.Even_or_Odd k) as [(k',->)|(k',->)].
   + left. exists k'; exists l; auto.
   + right. exists k'; exists l; auto.
Qed.

Lemma ThreeEven_not_ThreeOdd n : ThreeEven 2 n -> ~ThreeOdd 2 n.
Proof.
 intros (p & l & Hn & Hl) (p' & l' & Hn' & Hl').
 assert (E : 3::2*p::l = 3::2*p'+1::l').
 { apply decomp_unique; try eapply Delta_nz; auto; lia. }
 injection E. lia.
Qed.

Lemma decomp_complete' n : 2<n ->
 Two 2 n \/ ThreeEven 2 n \/ ThreeOdd 2 n \/ High 2 n.
Proof.
 intros N.
 destruct (@decomp_complete n) as [H|[H|H]]; auto.
 - lia.
 - destruct (Three_split N H); auto.
Qed.

Lemma ThreeOdd_12 n : ThreeOdd 1 n <-> ThreeOdd 2 n.
Proof.
 split; intros (p & l & Hn & Hl).
 - assert (2 <= p).
   { destruct p as [|[|p]].
     - simpl in Hl. inversion Hl; lia.
     - simpl in Hl. inversion Hl; lia.
     - lia. }
   assert (Hla : Delta 1 (2*p+1::l)) by eauto.
   assert (Hlb := norm_ok Hla).
   assert (Hlc := norm_hd (2*p+1::l)).
   assert (Hld := norm_le Hla).
   assert (Hle := norm_sum (2*p+1::l)).
   set (l0 := norm (2*p+1 :: l)) in *.
   destruct l0 as [|k0 l0].
   + elim Hlc.
   + simpl in Hlc. destruct Hlc as (p', Hlc).
     replace k0 with (2*(p+p')+1) in * by lia.
     exists (p+p'); exists l0; split.
     * simpl in *. lia.
     * constructor; auto. lia.
 - exists p; exists l; auto.
Qed.

Lemma ThreeEven_21 n : ThreeEven 2 n -> ThreeEven 1 n.
Proof.
 intros (p & l & Hn & Hl). exists p; exists l; auto.
Qed.

Lemma ThreeEven_12 n : ThreeEven 1 n -> ThreeEven 2 n \/ High 2 n.
Proof.
 intros (p & l & Hn & Hl).
 assert (Hla : Delta 1 (2*p::l)) by eauto.
 assert (Hlb := norm_ok Hla).
 assert (Hlc := norm_hd (2*p::l)).
 assert (Hld := norm_le Hla).
 assert (Hle := norm_sum (2*p::l)).
 set (l0 := norm (2*p :: l)) in *.
 destruct l0 as [|k0 l0].
 - elim Hlc.
 - destruct (eq_nat_dec k0 4) as [E|N].
   + right. apply High_12.
     subst k0.
     exists 5. split; auto. exists l0; repeat split; auto.
     simpl in *. lia.
   + simpl in Hlc. destruct Hlc as (p', Hlc).
     replace k0 with (2*(p+p')) in * by lia.
     left. exists (p+p'); exists l0; repeat split.
     { simpl in *. lia. }
     { constructor; auto. inversion Hl; subst. lia. }
Qed.

Lemma Two_not_ThreeOdd n : Two 2 n -> ~ThreeOdd 2 n.
Proof.
 intros O T. now apply (Two_not_Three O), ThreeOdd_Three.
Qed.

Lemma Two_not_ThreeOdd' n : Two 1 n -> ~ThreeOdd 2 n.
Proof.
 intros O T. now apply (Two_not_Three' O), ThreeOdd_Three.
Qed.

Lemma High_not_ThreeOdd n : High 2 n -> ~ThreeOdd 2 n.
Proof.
 intros H T. now apply (High_not_Three H), ThreeOdd_Three.
Qed.

Lemma High_not_ThreeOdd' n : High 1 n -> ~ThreeOdd 2 n.
Proof.
 intros H T. now apply (High_not_Three' H), ThreeOdd_Three.
Qed.

Lemma ThreeEven_not_ThreeOdd' n : ThreeEven 1 n -> ~ThreeOdd 2 n.
Proof.
 intros H. destruct (ThreeEven_12 H).
 - now apply ThreeEven_not_ThreeOdd.
 - now apply High_not_ThreeOdd.
Qed.

Hint Resolve Two_not_ThreeOdd ThreeEven_not_ThreeOdd High_not_ThreeOdd : core.
Hint Resolve Two_not_ThreeOdd' ThreeEven_not_ThreeOdd' High_not_ThreeOdd' : core.

(** Properties of Even and Odd *)

Lemma Even_or_Odd n : n<>0 -> Even 2 n \/ Odd 2 n.
Proof.
 intros N.
 destruct (Low_exists N) as (k,K).
 destruct (Nat.Even_or_Odd k) as [(k',->)|(k',->)]; firstorder.
Qed.

Lemma Even_xor_Odd n : Even 2 n -> Odd 2 n -> False.
Proof.
 intros (k,K) (k',K').
 assert (2*k = 2*k'+1) by (eapply Low_unique; eauto). lia.
Qed.

Lemma Even_12 n : Even 1 n <-> Even 2 n.
Proof.
 split; intros (k,K).
 - apply Low_12 in K. destruct K as (p,K).
   replace (2*k+2*p) with (2*(k+p)) in K by lia.
   now exists (k+p).
 - exists k. now apply Low_21.
Qed.

Lemma Odd_12 n : Odd 1 n <-> Odd 2 n.
Proof.
 split; intros (k,K).
 - apply Low_12 in K. destruct K as (p,K).
   replace (2*k+1+2*p) with (2*(k+p)+1) in K by lia.
   now exists (k+p).
 - exists k. now apply Low_21.
Qed.

Lemma Two_Even p n : Two p n -> Even p n.
Proof.
 now exists 1.
Qed.

Lemma Three_Odd p n : Three p n -> Odd p n.
Proof.
 now exists 1.
Qed.

Lemma Even_not_ThreeOdd n : Even 2 n -> ~ThreeOdd 2 n.
Proof.
 intros H H'.
 eapply Even_xor_Odd; eauto.
 now apply Three_Odd, ThreeOdd_Three.
Qed.
Hint Resolve Three_Odd Two_Even Even_not_ThreeOdd : core.

(** ** Decomposition of the predecessor of a Fibonacci number

    We discriminate according to the parity of the rank:
     - [fib (2k) - 1 = fib 3 + ... + fib (2k-1)]
     - [fib (2k+1) - 1 = fib 2 + fib 4 + ... + fib (2k)]

    So we explicitely builds these decompositions:
     - [evens k = [2;4;...;2k] ]
     - [odds k =  [3;5;...;2k+1] ]
*)

Definition evens k := map (fun x => 2*x) (seq 1 k).

Definition odds k := map (fun x => 2*x+1) (seq 1 k).

Lemma seq_S n k : seq (S n) k = map S (seq n k).
Proof.
 revert n. induction k; intros; trivial. simpl. now f_equal.
Qed.

Lemma seq_end n k : seq n (S k) = seq n k ++ [n+k].
Proof.
 revert n. induction k; intros.
 - simpl. f_equal. lia.
 - remember (S k) as k' eqn:Hk.
   simpl. rewrite IHk.
   rewrite Hk.
   simpl.
   now rewrite Nat.add_succ_r.
Qed.

Lemma sumfib_evens k :
  sumfib (evens k) = pred (fib (2*k+1)).
Proof.
 induction k; trivial.
 unfold evens in *.
 rewrite seq_end, map_app, sumfib_app, IHk.
 simpl map. rewrite sumfib_cons. simpl sumfib.
 simpl mult. rewrite !Nat.add_succ_r, !Nat.add_0_r.
 rewrite (fib_eqn (S (k+k))).
 generalize (@fib_nz (S (k+k))); lia.
Qed.

Lemma sumfib_odds k :
  sumfib (odds k) = pred (fib (2*(S k))).
Proof.
 induction k; trivial.
 unfold odds in *.
 rewrite seq_end, map_app, sumfib_app, IHk.
 simpl map. rewrite sumfib_cons. simpl sumfib.
 simpl mult. rewrite !Nat.add_succ_r, !Nat.add_0_r.
 rewrite (fib_eqn (S (S (k + k)))).
 generalize (@fib_nz (S (S (k+k)))). lia.
Qed.

Lemma S_evens k : map S (evens k) = odds k.
Proof.
 unfold odds, evens. rewrite map_map.
 apply map_ext. intros; lia.
Qed.

Lemma evens_S k : evens (S k) = 2 :: map S (odds k).
Proof.
  unfold odds, evens. simpl seq. rewrite seq_S.
  simpl. f_equal. rewrite !map_map.
  apply map_ext. intros. lia.
Qed.

Lemma evens_in k y : In y (evens k) -> 2<=y<=2*k.
Proof.
 unfold evens.
 rewrite in_map_iff. intros (x & Hx & IN).
 rewrite in_seq in IN. lia.
Qed.

Lemma odds_in k y : In y (odds k) -> 3<=y<=2*k+1.
Proof.
 unfold odds.
 rewrite in_map_iff. intros (x & Hx & IN).
 rewrite in_seq in IN. lia.
Qed.

Lemma Delta_evens k : Delta 2 (0::evens k).
Proof.
 change (Delta 2 (map (fun x => 2*x) (seq 0 (S k)))).
 apply Delta_map with 1.
 intros. lia.
 apply Delta_seq.
Qed.

Lemma Delta_odds k : Delta 2 (1::odds k).
Proof.
 change (Delta 2 (map (fun x=>2*x+1) (seq 0 (S k)))).
 apply Delta_map with 1.
 intros. lia.
 apply Delta_seq.
Qed.

(** A more direct approach : [preds] instead of [odds] and [even] *)

Fixpoint preds n :=
 match n with
 | 0 | 1 | 2 => []
 | S (S n) => (preds n)++[S n]
 end.

Lemma preds_ok n : sumfib (preds n) = pred (fib n).
Proof.
 induction n as [[|[|[|n]]] IH] using lt_wf_ind; trivial.
 change (preds _) with (preds (S n) ++ [S (S n)]).
 rewrite sumfib_app. rewrite IH by lia. clear IH.
 cbn - [fib]. rewrite (fib_eqn (S n)). generalize (@fib_nz (S n)). lia.
Qed.

Lemma preds_lt n x : In x (preds n) -> x < n.
Proof.
 induction n as [[|[|[|n]]] IH] using lt_wf_ind; try easy.
 change (preds _) with (preds (S n) ++ [S (S n)]).
 rewrite in_app_iff. intros [H|[->|[ ]]]. apply IH in H; lia. lia.
Qed.

Lemma preds_nil n : preds n = [] <-> n <= 2.
Proof.
 destruct n as [|[|[|n]]].
 - intuition.
 - intuition.
 - intuition.
 - change (preds _) with (preds (S n) ++ [S (S n)]).
   split; try lia.
   intros. now destruct (app_cons_not_nil (preds (S n)) [] (S (S n))).
Qed.

Lemma preds_low n x l : preds n = x :: l -> x = 2 \/ x = 3.
Proof.
 revert l.
 induction n as [[|[|[|n]]] IH] using lt_wf_ind; try easy.
 intros l.
 change (preds _) with (preds (S n) ++ [S (S n)]).
 destruct (Nat.le_decidable (S n) 2) as [LE|NLE].
 - pose proof LE as H. rewrite <- preds_nil in H. rewrite H.
   simpl. intros [= <- _]. lia.
 - rewrite <- preds_nil in NLE. specialize (IH (S n)).
   destruct (preds (S n)) as [|x' l']; try easy.
   simpl.
   intros [= -> E].
   assert (H : S n < S (S (S n))) by lia.
   now apply (IH H l').
Qed.

Lemma preds_delta n : Delta 2 (0::preds n).
Proof.
 induction n as [[|[|[|n]]] IH] using lt_wf_ind; trivial.
 change (preds _) with (preds (S n) ++ [S (S n)]).
 change (Delta 2 ((0::preds (S n))++[S (S n)])).
 apply Delta_app_iff; repeat split; auto.
 intros x x' [<-|IN] [<-|[ ]]. lia. apply preds_lt in IN. lia.
Qed.

Lemma tl_app_nn {A} (l l':list A) : l<>[] -> tl (l++l') = tl l ++ l'.
Proof.
 now destruct l.
Qed.

Lemma preds_shift n:
  map pred (map pred (tl (preds n))) = preds (n-2).
Proof.
 induction n as [[|[|[|n]]] IH] using lt_wf_ind; trivial.
 change (preds (S (S (S n)))) with (preds (S n) ++ [S (S n)]).
 simpl Nat.sub.
 destruct (Nat.le_decidable (S n) 2).
 - rewrite <- preds_nil in H. now rewrite H.
 - pose proof H as H'. rewrite <- preds_nil in H. rewrite tl_app_nn; auto.
   rewrite !map_app, IH; auto. simpl map.
   now destruct n as [|[|n]].
Qed.

(** ** Classification of successor's decomposition *)

Lemma Two_succ_Three n : Two 2 n -> Three 1 (S n).
Proof.
 intros (l & E & D & _). exists l; subst; simpl; auto.
Qed.

Lemma Two_succ_Odd n : Two 2 n <-> Odd 2 (S n).
Proof.
 split.
 - intros. now apply Odd_12, Three_Odd, Two_succ_Three.
 - intros (k & l & E & D & K).
   exists (map S (odds (k-1)) ++ l). repeat split; auto.
   + rewrite app_comm_cons, <- evens_S, sumfib_app, sumfib_evens.
     replace (S (k-1)) with k by lia.
     rewrite sumfib_cons in E. generalize (@fib_nz (2*k+1)). lia.
   + rewrite app_comm_cons, <- evens_S.
     replace (S (k-1)) with k by lia.
     apply Delta_app with (2*k+1); eauto using Delta_evens.
     intros y Hy. apply evens_in in Hy. lia.
Qed.

Lemma Three_succ_Four n : Three 2 n -> Four 1 (S n).
Proof.
 intros (l & E & D & _). exists l; subst; simpl; repeat split; auto.
Qed.

Lemma Three_succ_EvenHigh n : Three 2 n -> Even 2 (S n) /\ High 2 (S n).
Proof.
 split.
 - apply Even_12. exists 2. simpl. now apply Three_succ_Four.
 - apply High_12. exists 4. split; auto. now apply Three_succ_Four.
Qed.

Lemma High_succ_Two n : High 2 n <-> Two 2 (S n) /\ 0<n.
Proof.
 split.
 - intros (k & K & L); split.
   + destruct L as (l & E & D & _). exists (k::l); subst; auto.
   + apply Low_le in L.
     generalize (@fib_mono 3 k). simpl fib. lia.
 - intros ((l & E & D & _),N).
   simpl in E. injection E as E'.
   destruct l as [|k l]; [simpl in *; lia|].
   inversion_clear D.
   exists k. split; auto.
   exists l; repeat split; simpl; eauto; lia.
Qed.

Lemma Odd_succ_Even n : Odd 2 n -> Even 2 (S n).
Proof.
 intros (k,K).
 destruct k as [|[|k]].
 - simpl in *. apply Low_nz in K. lia.
 - now apply Three_succ_EvenHigh.
 - apply Two_Even, High_succ_Two. exists (2*(2+k)+1); split; eauto.
   lia.
Qed.

(** No general result for successor and [Even n] :
    - either [Two n] and then [Odd (S n)]
    - or [High n] and then [Two (S n)] *)


(** ** Classification of predecessor's decomposition *)

Lemma Odd_pred_Two n : Odd 2 n <-> Two 2 (n-1).
Proof.
 rewrite Two_succ_Odd.
 destruct n; simpl; rewrite ?Nat.sub_0_r; try reflexivity.
 split; intros (k,K).
 - apply Low_le in K. generalize (@fib_nz (2*k+1)); lia.
 - assert (2*k+1 = 2); try lia.
   { eapply Low_unique; eauto. exists (@nil nat). firstorder. }
Qed.

Lemma EvenHigh_pred_Odd n : Even 2 n -> High 2 n -> Odd 2 (n-1).
Proof.
 intros (k,L) (k' & K' & L').
 assert (k<>0). { intros ->. destruct L. intuition; lia. }
 assert (k<>1).
 { intros ->.
   replace k' with 2 in K' by (eapply Low_unique; eauto). lia. }
 clear k' K' L'.
 destruct L as (l & E & D & _).
 exists 1; exists (map S (map S (odds (k-2))) ++ l).
 change (2*1+1 :: map S (map S (odds (k-2))) ++ l) with
 (map S (2 :: map S (odds (k-2))) ++ l).
 rewrite <- evens_S, S_evens.
 replace (S (k-2)) with (k-1) by lia.
 repeat split.
 + subst n. rewrite sumfib_app, sumfib_odds, sumfib_cons.
   replace (S (k-1)) with k by lia.
   generalize (@fib_nz (2*k)); lia.
 + apply Delta_app with (2*k); eauto using Delta_odds.
   intros y Hy; apply odds_in in Hy; lia.
 + lia.
Qed.

Lemma Two_pred_High n : 1<n -> Two 2 n -> High 2 (n-1).
Proof.
 intros N O.
 rewrite High_succ_Two. split; try lia.
 now replace (S (n-1)) with n by lia.
Qed.

Lemma Three_pred_Two n : Three 2 n -> Two 2 (n-1).
Proof.
 intros. now apply Odd_pred_Two, Three_Odd.
Qed.

Lemma Four_pred_Three n : Four 2 n -> Three 2 (n-1).
Proof.
 intros (l & -> & D & _). simpl.
 exists l; repeat split; auto.
 apply Delta_low_hd with 4; auto.
Qed.

Lemma EvenHigh_pred_ThreeOdd n :
 Even 2 n -> ~Two 2 n -> ~Four 2 n -> ThreeOdd 2 (n-1).
Proof.
 intros (k,L) H H'.
 assert (2<k).
 { destruct k as [|[|[|k]]]; intuition; destruct L; intuition; lia. }
 clear H H'.
 destruct L as (l & E & D & _).
 exists 2. exists (map (fun n=>4+n) (odds (k-3)) ++ l).
 rewrite !app_comm_cons.
 assert (Eq : odds (k-1) = 3::2*2+1::map (fun n=>4+n) (odds (k-3))).
 { replace (k-1) with (S (S (k-3))) at 1 by lia.
   do 2 (rewrite <- S_evens, evens_S). simpl.
   now rewrite !map_map. }
 rewrite <- Eq. split.
 - rewrite E, sumfib_cons, sumfib_app, sumfib_odds.
   replace (S (k-1)) with k by lia.
   generalize (@fib_nz (2*k)); lia.
 - apply Delta_app with (2*k); eauto using Delta_odds.
   intros y Hy. apply odds_in in Hy. lia.
Qed.

(** We can now prove alternate formulations for [ThreeOdd]
    and [ThreeEven]. *)

Lemma ThreeOdd_alt n :
  ThreeOdd 2 n <-> Three 2 n /\ Odd 2 (n-2).
Proof.
 split.
 - intros H. split.
   + now apply ThreeOdd_Three.
   + destruct H as (k & l & E & D).
     exists k; exists l; repeat split; eauto.
     * subst n. simpl. lia.
     * inversion_clear D. lia.
 - intros ((l & E & D & _),(k & l' & E' & Hk & D')).
   assert (4 <= n).
   { rewrite sumfib_cons in E'.
     generalize (@fib_mono 3 (2*k+1)). simpl (fib 3). lia. }
   assert (k<>1).
   { intros ->. simpl mult in *.
     apply (@Two_not_High (n-1)).
     - apply Odd_pred_Two. exists 1; exists l; simpl; auto.
     - replace (n-1) with (S (n-2)) by lia.
       apply Three_succ_EvenHigh. exists l'; eauto. }
   exists k; exists l'; split.
   + subst n. simpl in *. lia.
   + constructor; auto. lia.
Qed.

Lemma ThreeEven_alt n :
  ThreeEven 2 n <-> Three 2 n /\ Even 2 (n-2).
Proof.
 split.
 - intros H. split.
   + now apply ThreeEven_Three.
   + destruct H as (k & l & E & D).
     exists k; exists l; repeat split; eauto.
     * subst n. simpl. lia.
     * inversion_clear D. lia.
 - intros ((l & E & D & _),(k & l' & E' & D' & K')).
   assert (3<=n).
   { rewrite sumfib_cons in E'.
     generalize (@fib_mono 2 (2*k)). simpl (fib 2). lia. }
   assert (k<>1).
   { intros ->. simpl plus in *.
     apply (@Two_not_Three'' (n-1)).
     - apply Low_21, Odd_pred_Two.
       exists 1. simpl. exists l; auto.
     - replace (n-1) with (S (n-2)) by lia.
       apply Two_succ_Three. exists l'; auto. }
   assert (k<>2).
   { intros ->. simpl plus in *.
     assert (Eq : 2::l = 2::4::l').
     { apply decomp_unique; eauto using Delta_nz, Delta_low_hd.
       simpl in *; lia. }
     injection Eq as ->. inversion D; lia. }
   exists k; exists l'; split.
   + subst n. simpl in *. lia.
   + constructor; auto. lia.
Qed.

(** ** Two consecutive [ThreeOdd] numbers are separated by 5 or 8 *)

Lemma ThreeOdd_next n :
  ThreeOdd 2 n -> ThreeOdd 2 (n+5) \/ ThreeOdd 2 (n+8).
Proof.
  intros (k & l & E & D).
  destruct k as [|[|[|k]]].
  - simpl in D. inversion D. lia.
  - simpl in D. inversion D. lia.
  - right. simpl in *.
    destruct l as [|k l].
    + simpl in *.
      exists 3; exists []. subst. auto.
    + apply ThreeOdd_12.
      destruct (le_lt_dec k 7).
      * assert (k=7).
        { inversion D; subst. inversion H3; subst. lia. }
        subst k.
        exists 2; exists (8::l); split.
        { subst; simpl; lia. }
        { constructor. lia. constructor. lia. eauto. }
      * exists 3; exists (k::l); split.
        { subst; simpl; lia. }
        { constructor. lia. constructor. lia. eauto. }
  - left. apply ThreeOdd_12.
    exists 2; exists (2*(3+k)+1::l); split.
    { subst. simpl. lia. }
    { constructor. lia. constructor. lia. eauto. }
Qed.

Lemma ThreeOdd_add_1 n : ThreeOdd 2 n -> High 2 (n+1).
Proof.
  intros.
  rewrite Nat.add_1_r. now apply Three_succ_EvenHigh, ThreeOdd_Three.
Qed.

Lemma ThreeOdd_add_2 n : ThreeOdd 2 n -> Two 2 (n+2).
Proof.
 intros.
 rewrite Nat.add_succ_r. now apply High_succ_Two, ThreeOdd_add_1.
Qed.

Lemma ThreeOdd_add_3 n : ThreeOdd 2 n -> ThreeEven 2 (n+3) \/ High 2 (n+3).
Proof.
  intros (k & l & E & D).
  destruct k as [|[|[|k]]].
  - inversion D; lia.
  - inversion D; lia.
  - apply ThreeEven_12.
    exists 3; exists l; split.
    + subst; simpl; lia.
    + constructor. lia. simpl. eauto.
  - right.
    apply High_12.
    exists 5; split; auto. exists (2*(3+k)+1::l); repeat split; auto.
    + subst; simpl; lia.
    + apply Delta_inv in D. constructor. lia. eauto.
Qed.

Lemma ThreeOdd_add_4 n : ThreeOdd 2 n -> Two 2 (n+4) \/ High 2 (n+4).
Proof.
  intros H.
  rewrite Nat.add_succ_r.
  destruct (ThreeOdd_add_3 H) as [H'|H'].
  - right. now apply Three_succ_EvenHigh, ThreeEven_Three.
  - left. now apply High_succ_Two.
Qed.

Lemma ThreeOdd_add_6 n : ThreeOdd 2 n -> High 2 (n+6).
Proof.
  intros (k & l & E & D).
  apply High_12.
  destruct k as [|[|[|k]]].
  - inversion D; lia.
  - inversion D; lia.
  - exists 5; split; auto. exists (6::l); repeat split; auto.
    + subst; simpl; lia.
    + constructor. lia. eauto.
  - exists 6; split; auto. exists (2*(3+k)+1::l); repeat split; auto.
    + subst; simpl; lia.
    + constructor. lia. eauto.
    + lia.
Qed.

Lemma ThreeOdd_add_7 n : ThreeOdd 2 n -> Two 2 (n+7).
Proof.
  intros. rewrite Nat.add_succ_r.
  now apply High_succ_Two, ThreeOdd_add_6.
Qed.

Lemma ThreeOdd_next_5_xor_8 n :
  ThreeOdd 2 (n+5) -> ThreeOdd 2 (n+8) -> False.
Proof.
 intros Hn.
 change (~ThreeOdd 2 (n+8)).
 apply ThreeOdd_add_3 in Hn.
 replace (n+5+3) with (n+8) in Hn by lia.
 destruct Hn; auto.
Qed.

Lemma ThreeOdd_next5 n :
 ThreeOdd 2 n -> ThreeOdd 2 (n+5) ->
 forall m, n<m<n+5 -> ~ThreeOdd 2 m.
Proof.
 intros Hn Hn' m H.
 assert (Hm : m=n+1 \/ m=n+2 \/ m=n+3 \/ m=n+4) by lia.
 destruct Hm as [Hm|[Hm|[Hm|Hm]]]; subst m.
 - apply ThreeOdd_add_1 in Hn. auto.
 - apply ThreeOdd_add_2 in Hn. auto.
 - apply ThreeOdd_add_3 in Hn. destruct Hn; auto.
 - apply ThreeOdd_add_4 in Hn. destruct Hn; auto.
Qed.

Lemma ThreeOdd_next8 n :
 ThreeOdd 2 n -> ThreeOdd 2 (n+8) ->
 forall m, n<m<n+8 -> ~ThreeOdd 2 m.
Proof.
 intros Hn Hn' m H.
 assert (Hm : m=n+1 \/ m=n+2 \/ m=n+3 \/ m=n+4 \/
              m=n+5 \/ m=n+6 \/ m=n+7) by lia.
 destruct Hm as [Hm|[Hm|[Hm|[Hm|[Hm|[Hm|Hm]]]]]]; subst m.
 - apply ThreeOdd_add_1 in Hn. auto.
 - apply ThreeOdd_add_2 in Hn. auto.
 - apply ThreeOdd_add_3 in Hn. destruct Hn; auto.
 - apply ThreeOdd_add_4 in Hn. destruct Hn; auto.
 - intros Hn''. eapply ThreeOdd_next_5_xor_8; eauto.
 - apply ThreeOdd_add_6 in Hn. auto.
 - apply ThreeOdd_add_7 in Hn. auto.
Qed.

Lemma ThreeOdd_next_inv n m :
  ThreeOdd 2 n -> ThreeOdd 2 m -> n < m ->
  (forall p, n < p < m -> ~ThreeOdd 2 p) ->
  m = n+5 \/ m = n+8.
Proof.
  intros Hn Hm LT Hp.
  destruct (ThreeOdd_next Hn) as [Hn'|Hn'].
  - destruct (lt_eq_lt_dec m (n+5)) as [[LT'|EQ]|LT']; auto.
    + elim (@ThreeOdd_next5 _ Hn Hn' m). lia. auto.
    + elim (Hp (n+5)). lia. auto.
  - destruct (lt_eq_lt_dec m (n+8)) as [[LT'|EQ]|LT']; auto.
    + elim (@ThreeOdd_next8 _ Hn Hn' m). lia. auto.
    + elim (Hp (n+8)). lia. auto.
Qed.
