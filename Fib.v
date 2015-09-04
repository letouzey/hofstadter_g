(** * Fib : Fibonacci sequence and decomposition *)

Require Import Arith Omega Wf_nat List NPeano.
Require Import DeltaList.
Import ListNotations.
Set Implicit Arguments.

(** * Fibonacci sequence

    First, a definition of the Fibonacci sequence.
    We use here the variant that starts with 1 1 2 3 ...
    (no zero).
*)

Fixpoint fib (n:nat) : nat :=
  match n with
  | 0 => 1
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
 - intros _. replace (S n - 1) with n by omega.
   apply fib_eqn.
Qed.

Lemma fib_nz k : 1 <= fib k.
Proof.
 induction k as [|[|k] IH]; trivial. rewrite fib_eqn. omega.
Qed.

Lemma fib_lt_S k : k<>0 -> fib k < fib (S k).
Proof.
 intro. rewrite fib_eqn' by trivial.
 generalize (fib_nz (k-1)). omega.
Qed.

Lemma fib_lt k k' : 0 < k -> k < k' -> fib k < fib k'.
Proof.
 induction 2.
 - apply fib_lt_S; omega.
 - transitivity (fib m); trivial. apply fib_lt_S; omega.
Qed.

Lemma fib_mono_S k : fib k <= fib (S k).
Proof.
 destruct k. trivial. rewrite fib_eqn. omega.
Qed.

Lemma fib_mono k k' : k <= k' -> fib k <= fib k'.
Proof.
 induction 1; trivial.
 transitivity (fib m); trivial. apply fib_mono_S.
Qed.

Lemma fib_inj k k' : 0<k -> 0<k' -> fib k = fib k' -> k = k'.
Proof.
 intros.
 destruct (lt_eq_lt_dec k k') as [[LT|EQ]|LT]; trivial;
  apply fib_lt in LT; omega.
Qed.

Lemma fib_lt_inv k k' : fib k < fib k' -> k < k'.
Proof.
 intros.
 destruct (le_lt_dec k' k) as [LE|LT]; trivial.
 apply fib_mono in LE. omega.
Qed.

Lemma fib_le_id k : k <= fib k.
Proof.
 induction k as [|[|k] IH].
 - simpl; auto.
 - simpl; auto.
 - rewrite fib_eqn. generalize (fib_nz k). omega.
Qed.

Lemma fib_inv n : { k | n<>0 -> fib k <= n < fib (S k) }.
Proof.
 induction n as [|n IH].
 - exists 0. now destruct 1.
 - destruct (eq_nat_dec n 0) as [E|N].
   + exists 1. subst. compute. now split.
   + destruct IH as (k,Hk). specialize (Hk N).
     destruct (eq_nat_dec (S n) (fib (S k))) as [->|N'].
     * exists (S k). intros _.
       rewrite fib_eqn. generalize (fib_nz k); omega.
     * exists k. intros _. omega.
Defined.


(** * Decomposition via sums of Fibonacci numbers.

    Zeckendorf's theorem (actually discovered earlier by
    Lekkerkerker) states that any natural number can be obtained
    by a sum of distinct Fibonacci numbers, and this decomposition
    is moreover unique when :
     - [fib 0] isn't in the decomposition
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
 rewrite Nat.sub_1_r. omega.
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
 - simpl. rewrite IHl. omega.
Qed.

Lemma sumfib_rev l : sumfib (rev l) = sumfib l.
Proof.
 induction l.
 - trivial.
 - simpl. rewrite sumfib_app, IHl. simpl. omega.
Qed.

Lemma sumfib_0 l : sumfib l = 0 <-> l = [].
Proof.
 split.
 - intros H. destruct l; [ now elim H |].
   simpl in H. generalize (fib_nz n). omega.
 - intros; now subst.
Qed.

(** ** Zeckendorf's Theorem *)

(** Technical lemma:
    A canonical decomposition cannot excess the next Fibonacci. *)

Lemma decomp_max k l :
  ~In 0 (k::l) -> DeltaRev 2 (k::l) -> sumfib (k::l) < fib (S k).
Proof.
 revert k.
 induction l.
 - intros k Hk _. simpl in Hk. simpl sumfib. rewrite Nat.add_0_r.
   apply fib_lt_S; omega.
 - intros k Hk. simpl in Hk.
   inversion 1; subst. simpl sumfib.
   rewrite fib_eqn' by omega. apply Nat.add_lt_mono_l.
   apply lt_le_trans with (fib (S a)).
   + apply IHl. simpl; intuition. now inversion H.
   + apply fib_mono; omega.
Qed.

(** Zeckendorf's Theorem, in a variant that consider
    decompositions with largest terms first
    (easiest for the proof). *)

Lemma decomp_exists_rev n : { l | sumfib l = n /\ DeltaRev 2 l /\ ~In 0 l }.
Proof.
 induction n as [n IH] using lt_wf_rec.
 destruct (eq_nat_dec n 0) as [EQ|NE].
 - subst. exists (@nil nat). simpl; intuition.
 - destruct (fib_inv n) as (k,Hk).
   specialize (Hk NE).
   assert (Hk' : k<>0). { intro; subst k; compute in Hk; omega. }
   destruct (IH (n - fib k)) as (l & EQ & DR & NI).
   { generalize (fib_nz k); omega. }
   destruct l as [|k' l]; simpl in EQ.
   + exists (k::nil); simpl; repeat split; try constructor; omega.
   + exists (k::k'::l); simpl; simpl in NI; repeat split.
     * omega.
     * constructor; trivial.
       rewrite fib_eqn' in Hk by trivial.
       assert (k' < k-1); try omega.
       { apply Nat.lt_nge. intro LE. apply fib_mono in LE. omega. }
     * intuition.
Qed.

Lemma decomp_unique_rev l l' :
 ~In 0 l -> ~In 0 l' -> DeltaRev 2 l -> DeltaRev 2 l' ->
 sumfib l = sumfib l' -> l = l'.
Proof.
 revert l'.
 induction l as [|n l IH]; destruct l' as [|n' l'].
 - trivial.
 - intros _ _ _ _. simpl. generalize (fib_nz n'); omega.
 - intros _ _ _ _. simpl. generalize (fib_nz n); omega.
 - intros NI NI' DR DR' EQ.
   assert (n < S n').
   { apply fib_lt_inv. simpl in EQ.
     apply le_lt_trans with (fib n' + sumfib l'); [omega|].
     now apply decomp_max. }
   assert (n' < S n).
   { apply fib_lt_inv. simpl in EQ.
     apply le_lt_trans with (fib n + sumfib l); [omega|].
     now apply decomp_max. }
   replace n' with n in * by omega. clear H H0.
   simpl in EQ.
   f_equal.
   apply IH; try omega.
   + simpl in NI; intuition.
   + simpl in NI'; intuition.
   + apply DeltaRev_alt in DR. intuition.
   + apply DeltaRev_alt in DR'. intuition.
Qed.

(** Same theorem, in the other order (smallest term first). *)

Lemma decomp_exists n : { l | sumfib l = n /\ Delta 2 l /\ ~In 0 l }.
Proof.
 destruct (decomp_exists_rev n) as (l & Hn & Hl & Nz).
 exists (rev l); repeat split.
 - now rewrite sumfib_rev.
 - now apply Delta_rev.
 - now rewrite <- in_rev.
Qed.

Lemma decomp_unique l l' :
 ~In 0 l -> ~In 0 l' -> Delta 2 l -> Delta 2 l' ->
 sumfib l = sumfib l' -> l = l'.
Proof.
 intros.
 assert (rev l = rev l').
 { apply decomp_unique_rev;
   now rewrite <- ?in_rev, ?DeltaRev_rev, ?sumfib_rev. }
 rewrite <- (rev_involutive l), <- (rev_involutive l').
 now f_equal.
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
   assert (Hn' : length l < n) by omega.
   destruct (IH (length l) Hn' l) as (l' & Eq & St & Le & Hd);
    trivial.
   destruct l' as [|k' l'].
   + exists [k].
     simpl in *. repeat split; subst; auto with arith.
     exists 0. omega.
   + assert (Delta 1 (k::l) -> k < k').
     { intros Hl.
       destruct l as [|x l0]. elim Hd. simpl in Hd. destruct Hd as (p,Hd).
       apply Delta_alt in Hl.
       assert (k+1 <= x) by (apply Hl; now left).
       omega. }
     destruct (eq_nat_dec (S k) k') as [E|N].
     * assert (Lt : length (S k' :: l') < n).
       { simpl in *; omega. }
       destruct (IH _ Lt (S k' :: l')) as (l'' & Eq' & St' & Le' & Hd');
         trivial; clear IH.
       exists l''; repeat split; auto.
       { rewrite Eq'. simpl. rewrite <- Eq. simpl.
         rewrite <- E. omega. }
       { intros Hl.
         apply St'.
         rewrite Delta_alt in St, Hl.
         apply Delta_alt. split.
         - apply Delta_21, St, Hl.
         - intros y Hy. apply St in Hy; [|apply Hl]. omega. }
       { simpl in *; omega. }
       { subst k'.
         destruct l''; simpl in Hd'. elim Hd'.
         destruct Hd' as (p,Hd'). exists (S p). omega. }
     * exists (k::k'::l'); repeat split; simpl in *; auto.
       { intros Hl.
         assert (k<k') by auto.
         constructor; auto. omega.
         eauto. }
       { omega. }
       { exists 0. omega. }
Defined.

Definition norm l := let (l',_) := norm_spec l in l'.

(* For example: Compute norm [1;2;3;4] *)

Lemma norm_sum l : sumfib (norm l) = sumfib l.
Proof.
 unfold norm. destruct norm_spec. intuition.
Qed.

Lemma norm_ok l : Delta 1 l -> Delta 2 (norm l).
Proof.
 unfold norm. destruct norm_spec. intuition.
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
   assert (x <= k') by omega.
   simpl in Hy. destruct Hy as [Hy|Hy]; try omega.
   transitivity k'; auto.
   apply Delta_alt in H. apply H in Hy. omega.
Qed.


(** ** Classification of Fibonacci decompositions

    For a later theorem ([g'_g]), we'll need to classify
    the Fibonacci decompositions according to their lowest
    terms. Is the lowest rank 1, 2 or more ? Is it even or odd ?

    In [Low p n k]:
    - [p] is the delta between ranks in the decomposition (usually 2)
    - [n] is the number we're decomposing
    - [k] is the lowest rank in the decomposition (we force [0<k]).
*)

Definition Low p n k :=
 exists l, n = sumfib (k::l) /\ Delta p (k::l) /\ k<>0.

Definition One p n := Low p n 1.
Definition Two p n := Low p n 2.
Definition Three p n := Low p n 3.
Definition High p n := exists k, 2 < k /\ Low p n k.

Definition Even p n := exists k, Low p n (2*k).
Definition Odd p n := exists k, Low p n (2*k+1).

(** Some properties of the [Low] predicate *)

Lemma Low_exists n : n<>0 -> exists k, Low 2 n k.
Proof.
 intros.
 destruct (decomp_exists n) as (l & E & D & L).
 destruct l as [|k l]; simpl in *.
 - congruence.
 - exists k; exists l. simpl; intuition.
Qed.

Lemma Low_nz p n k : Low p n k -> k<>0.
Proof.
 firstorder.
Qed.

Lemma Low_unique n k k' : Low 2 n k -> Low 2 n k' -> k = k'.
Proof.
 intros (l & E & D & K) (l' & E' & D' & K').
 assert (Eq : k::l = k'::l'); [|now injection Eq].
 { apply decomp_unique; auto.
   - eapply Delta_nz; eauto. omega.
   - eapply Delta_nz; eauto. omega.
   - congruence. }
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
   exists p. exists l'. subst; simpl; repeat split; auto. omega.
Qed.

Lemma Low_le p n k : Low p n k -> fib k <= n.
Proof.
 intros (l & -> & _ & _). simpl. omega.
Qed.

(** Properties specialized to [One], [Two], etc *)

Lemma High_12 n : High 1 n <-> High 2 n.
Proof.
 split; intros (k & K & L).
 - apply Low_12 in L. destruct L as (p,L).
   exists (k+2*p). split; auto. omega.
 - apply Low_21 in L. exists k; auto.
Qed.

Lemma One_21 n : One 2 n -> One 1 n.
Proof.
 apply Low_21.
Qed.

Lemma One_12 n : One 1 n -> One 2 n \/ High 2 n.
Proof.
 intros L. apply Low_12 in L. destruct L as (p,L).
 destruct p.
 - now left.
 - right. exists (1+2*(S p)). split; auto. omega.
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
 - right. exists (2+2*(S p)). split; auto. omega.
Qed.

Lemma decomp_complete n : n<>0 -> One 2 n \/ Two 2 n \/ High 2 n.
Proof.
 intros Hn.
 destruct (Low_exists Hn) as (k,L).
 destruct k as [|[|[|k]]].
 - apply Low_nz in L. now elim L.
 - now left.
 - now (right; left).
 - right; right. exists (3+k). split; auto. omega.
Qed.

Lemma One_not_High n : One 2 n -> ~High 2 n.
Proof.
 intros L (k & K & L').
 assert (k = 1) by (eapply Low_unique; eauto).
 omega.
Qed.

Lemma One_not_Two n : One 2 n -> ~Two 2 n.
Proof.
 intros L L'.
 assert (1 = 2) by (eapply Low_unique; eauto). discriminate.
Qed.

Lemma High_not_Two n : High 2 n -> ~Two 2 n.
Proof.
 intros (k & K & L) L'.
 assert (k = 2) by (eapply Low_unique; eauto).
 omega.
Qed.

Lemma One_not_Two' n : One 1 n -> ~Two 2 n.
Proof.
 intros L.
 destruct (One_12 L); auto using One_not_Two, High_not_Two.
Qed.

Lemma One_not_Two'' n : One 1 n -> ~Two 1 n.
Proof.
 intros L L'.
 destruct (Low_12 L) as (p,Lp).
 destruct (Low_12 L') as (p',Lp').
 assert (1+2*p = 2+2*p') by (eapply Low_unique; eauto).
 omega.
Qed.

Lemma High_not_Two' n : High 1 n -> ~Two 2 n.
Proof.
 intros. now apply High_not_Two, High_12.
Qed.

(** Special subdivisions of decompositions starting by 2. *)

Definition TwoEven p n :=
 exists k l, n = sumfib (2::2*k::l) /\ Delta p (2::2*k::l).
Definition TwoOdd p n :=
 exists k l, n = sumfib (2::2*k+1::l) /\ Delta p (2::2*k+1::l).

Lemma TwoEven_le n : TwoEven 2 n -> 6 <= n.
Proof.
 intros (k & l & E & D). subst n. rewrite !sumfib_cons.
 generalize (@fib_mono 4 (2*k)).
 inversion_clear D. simpl; omega.
Qed.

Lemma TwoOdd_le n : TwoOdd 2 n -> 7 <= n.
Proof.
 intros (k & l & E & D). subst n. rewrite !sumfib_cons.
 generalize (@fib_mono 5 (2*k+1)).
 inversion_clear D. simpl; omega.
Qed.

Lemma TwoEven_Two p n : TwoEven p n -> Two p n.
Proof.
 firstorder.
Qed.

Lemma TwoOdd_Two p n : TwoOdd p n -> Two p n.
Proof.
 firstorder.
Qed.
Hint Resolve TwoEven_Two TwoOdd_Two.

Lemma Two_split p n : 2<n -> Two p n -> TwoEven p n \/ TwoOdd p n.
Proof.
 intros N (l & E & D & _).
 destruct l as [|k l].
 - simpl in E. omega.
 - destruct (Nat.Even_or_Odd k) as [(k',->)|(k',->)].
   + left. exists k'; exists l; auto.
   + right. exists k'; exists l; auto.
Qed.

Lemma TwoOdd_not_TwoEven n : TwoOdd 2 n -> ~TwoEven 2 n.
Proof.
 intros (p & l & Hn & Hl) (p' & l' & Hn' & Hl').
 assert (E : 2::2*p+1::l = 2::2*p'::l').
 { apply decomp_unique; try eapply Delta_nz; auto; omega. }
 injection E. omega.
Qed.

Lemma decomp_complete' n : 2<n ->
 One 2 n \/ TwoEven 2 n \/ TwoOdd 2 n \/ High 2 n.
Proof.
 intros N.
 destruct (@decomp_complete n) as [H|[H|H]]; auto.
 - omega.
 - destruct (Two_split N H); auto.
Qed.

Lemma TwoEven_12 n : TwoEven 1 n <-> TwoEven 2 n.
Proof.
 split; intros (p & l & Hn & Hl).
 - assert (2 <= p).
   { destruct p as [|[|p]].
     - simpl in Hl. inversion Hl; omega.
     - simpl in Hl. inversion Hl; omega.
     - omega. }
   assert (Hla : Delta 1 (2*p::l)) by eauto.
   assert (Hlb := norm_ok Hla).
   assert (Hlc := norm_hd (2*p::l)).
   assert (Hld := norm_le Hla).
   assert (Hle := norm_sum (2*p::l)).
   set (l0 := norm (2*p :: l)) in *.
   destruct l0 as [|k0 l0].
   + elim Hlc.
   + simpl in Hlc. destruct Hlc as (p', Hlc).
     replace k0 with (2*(p+p')) in * by omega.
     exists (p+p'); exists l0; split.
     * simpl in *. omega.
     * constructor; auto. omega.
 - exists p; exists l; auto.
Qed.

Lemma TwoOdd_21 n : TwoOdd 2 n -> TwoOdd 1 n.
Proof.
 intros (p & l & Hn & Hl). exists p; exists l; auto.
Qed.

Lemma TwoOdd_12 n : TwoOdd 1 n -> TwoOdd 2 n \/ High 2 n.
Proof.
 intros (p & l & Hn & Hl).
 assert (Hla : Delta 1 (2*p+1::l)) by eauto.
 assert (Hlb := norm_ok Hla).
 assert (Hlc := norm_hd (2*p+1::l)).
 assert (Hld := norm_le Hla).
 assert (Hle := norm_sum (2*p+1::l)).
 set (l0 := norm (2*p+1 :: l)) in *.
 destruct l0 as [|k0 l0].
 - elim Hlc.
 - destruct (eq_nat_dec k0 3) as [E|N].
   + right. apply High_12.
     subst k0.
     exists 4. split; auto. exists l0; repeat split; auto.
     simpl in *. omega.
   + simpl in Hlc. destruct Hlc as (p', Hlc).
     replace k0 with (2*(p+p')+1) in * by omega.
     left. exists (p+p'); exists l0; repeat split.
     { simpl in *. omega. }
     { constructor; auto. inversion Hl; subst. omega. }
Qed.

Lemma One_not_TwoEven n : One 2 n -> ~TwoEven 2 n.
Proof.
 intros O T. now apply (One_not_Two O), TwoEven_Two.
Qed.

Lemma One_not_TwoEven' n : One 1 n -> ~TwoEven 2 n.
Proof.
 intros O T. now apply (One_not_Two' O), TwoEven_Two.
Qed.

Lemma High_not_TwoEven n : High 2 n -> ~TwoEven 2 n.
Proof.
 intros H T. now apply (High_not_Two H), TwoEven_Two.
Qed.

Lemma High_not_TwoEven' n : High 1 n -> ~TwoEven 2 n.
Proof.
 intros H T. now apply (High_not_Two' H), TwoEven_Two.
Qed.

Lemma TwoOdd_not_TwoEven' n : TwoOdd 1 n -> ~TwoEven 2 n.
Proof.
 intros H. destruct (TwoOdd_12 H).
 - now apply TwoOdd_not_TwoEven.
 - now apply High_not_TwoEven.
Qed.

Hint Resolve One_not_TwoEven TwoOdd_not_TwoEven High_not_TwoEven.
Hint Resolve One_not_TwoEven' TwoOdd_not_TwoEven' High_not_TwoEven'.

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
 assert (2*k = 2*k'+1) by (eapply Low_unique; eauto). omega.
Qed.

Lemma Even_12 n : Even 1 n <-> Even 2 n.
Proof.
 split; intros (k,K).
 - apply Low_12 in K. destruct K as (p,K).
   replace (2*k+2*p) with (2*(k+p)) in K by omega.
   now exists (k+p).
 - exists k. now apply Low_21.
Qed.

Lemma Odd_12 n : Odd 1 n <-> Odd 2 n.
Proof.
 split; intros (k,K).
 - apply Low_12 in K. destruct K as (p,K).
   replace (2*k+1+2*p) with (2*(k+p)+1) in K by omega.
   now exists (k+p).
 - exists k. now apply Low_21.
Qed.

Lemma One_Odd p n : One p n -> Odd p n.
Proof.
 now exists 0.
Qed.

Lemma Two_Even p n : Two p n -> Even p n.
Proof.
 now exists 1.
Qed.

Lemma Odd_not_TwoEven n : Odd 2 n -> ~TwoEven 2 n.
Proof.
 intros H H'.
 eapply Even_xor_Odd; eauto.
 now apply Two_Even, TwoEven_Two.
Qed.
Hint Resolve Two_Even One_Odd Odd_not_TwoEven.

(** ** Decomposition of the predecessor of a Fibonacci number

    We discriminate according to the parity of the rank:
     - [fib (2k) - 1 = fib 1 + fib 3 + ... + fib (2k-1)]
     - [fib (2k+1) - 1 = fib 2 + fib 4 + ... + fib (2k)]

    So we explicitely builds these decompositions:
     - [odds k = [1;3;...;2k-1] ]
     - [evens k = [2;4;...;2k] ]
*)

Definition odds k := map (fun x => 2*x+1) (seq 0 k).

Definition evens k := map (fun x => 2*x+2) (seq 0 k).

Lemma seq_S n k : seq (S n) k = map S (seq n k).
Proof.
 revert n. induction k; intros; trivial. simpl. now f_equal.
Qed.

Lemma seq_end n k : seq n (S k) = seq n k ++ [n+k].
Proof.
 revert n. induction k; intros.
 - simpl. f_equal. omega.
 - remember (S k) as k' eqn:Hk.
   simpl. rewrite IHk.
   rewrite Hk.
   simpl.
   now rewrite Nat.add_succ_r.
Qed.

Lemma sumfib_odds k :
  sumfib (odds k) = pred (fib (2*k)).
Proof.
 induction k; trivial.
 unfold odds in *.
 rewrite seq_end, map_app, sumfib_app, IHk.
 simpl map. rewrite sumfib_cons. simpl sumfib.
 simpl mult. rewrite !Nat.add_succ_r, !Nat.add_0_r.
 rewrite fib_eqn.
 generalize (fib_nz (k+k)); omega.
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
 generalize (fib_nz (S (k+k))); omega.
Qed.

Lemma S_odds k : map S (odds k) = evens k.
Proof.
 unfold odds, evens. rewrite map_map.
 apply map_ext. intros; omega.
Qed.

Lemma odds_S k : odds (S k) = 1 :: map S (evens k).
Proof.
  unfold odds, evens. simpl seq. rewrite seq_S.
  simpl. f_equal. rewrite !map_map.
  apply map_ext. intros. omega.
Qed.

Lemma odds_in k : forall y, In y (odds k) -> 1<=y<2*k.
Proof.
 induction k.
 - simpl; intuition.
 - intros y. rewrite odds_S, <- S_odds.
   rewrite map_map. simpl.
   rewrite in_map_iff.
   intros [H|(x,(Hx,Hx'))]. omega. apply IHk in Hx'. omega.
Qed.

Lemma evens_in k : forall y, In y (evens k) -> 2<=y<=2*k.
Proof.
 intros y. rewrite <- S_odds, in_map_iff.
 intros (x,(<-,Hx)). apply odds_in in Hx. omega.
Qed.

Lemma Delta_odds k : Delta 2 (odds k).
Proof.
 unfold odds. apply Delta_map with 1.
 intros. omega.
 apply Delta_seq.
Qed.

Lemma Delta_evens k : Delta 2 (evens k).
Proof.
 unfold odds. apply Delta_map with 1.
 intros. omega.
 apply Delta_seq.
Qed.

(** ** Classification of successor's decomposition *)

Lemma One_succ_Two n : One 2 n -> Two 1 (S n).
Proof.
 intros (l & E & D & _). exists l; subst; simpl; auto.
Qed.

Lemma One_succ_Even n : One 2 n <-> Even 2 (S n).
Proof.
 split.
 - intros. now apply Even_12, Two_Even, One_succ_Two.
 - intros (k & l & E & D & K).
   exists (map S (evens (k-1)) ++ l). repeat split; auto.
   + rewrite app_comm_cons, <- odds_S, sumfib_app, sumfib_odds.
     replace (S (k-1)) with k by omega.
     rewrite sumfib_cons in E. generalize (fib_nz (2*k)). omega.
   + rewrite app_comm_cons, <- odds_S.
     replace (S (k-1)) with k by omega.
     apply Delta_app with (2*k); auto using Delta_odds.
     intros y Hy. apply odds_in in Hy. omega.
Qed.

Lemma Two_succ_Three n : Two 2 n -> Three 1 (S n).
Proof.
 intros (l & E & D & _). exists l; subst; simpl; auto.
Qed.

Lemma Two_succ_OddHigh n : Two 2 n -> Odd 2 (S n) /\ High 2 (S n).
Proof.
 split.
 - apply Odd_12. exists 1. simpl. now apply Two_succ_Three.
 - apply High_12. exists 3. split; auto. now apply Two_succ_Three.
Qed.

Lemma High_succ_One n : High 2 n <-> One 2 (S n) /\ 0<n.
Proof.
 split.
 - intros (k & K & L); split.
   + destruct L as (l & E & D & _). exists (k::l); subst; auto.
   + apply Low_le in L.
     generalize (@fib_mono 3 k). simpl fib. omega.
 - intros ((l & E & D & _),N).
   simpl in E. injection E as E'.
   destruct l as [|k l]; [simpl in *; omega|].
   inversion_clear D.
   exists k. split; auto.
   exists l; repeat split; simpl; eauto; omega.
Qed.

Lemma Even_succ_Odd n : Even 2 n -> Odd 2 (S n).
Proof.
 intros (k,K).
 destruct k as [|[|k]].
 - simpl in *. apply Low_nz in K. now elim K.
 - now apply Two_succ_OddHigh.
 - apply One_Odd, High_succ_One. exists (2*(2+k)); split; auto.
   omega.
Qed.

(** No general result for successor and [Odd n] :
    - either [One n] and then [Even (S n)]
    - or [High n] and then [One (S n)] *)


(** ** Classification of predecessor's decomposition *)

Lemma Even_pred_One n : Even 2 n <-> One 2 (n-1).
Proof.
 rewrite One_succ_Even.
 destruct n; simpl; rewrite ?Nat.sub_0_r; try reflexivity.
 split; intros (k,K).
 - apply Low_le in K. generalize (fib_nz (2*k)); omega.
 - assert (2*k = 1); try omega.
   { eapply Low_unique; eauto. exists (@nil nat). firstorder. }
Qed.

Lemma OddHigh_pred_Even n : Odd 2 n -> High 2 n -> Even 2 (n-1).
Proof.
 intros (k,L) (k' & K' & L').
 assert (k<>0).
 { intros ->.
   replace k' with 1 in K' by (eapply Low_unique; eauto). omega. }
 clear k' K' L'.
 destruct L as (l & E & D & _).
 exists 1; exists (map S (map S (evens (k-1))) ++ l).
 change (2*1 :: map S (map S (evens (k-1))) ++ l) with
 (map S (1 :: map S (evens (k-1))) ++ l).
 rewrite <- odds_S, S_odds.
 replace (S (k-1)) with k by omega.
 repeat split.
 + subst n. rewrite sumfib_app, sumfib_evens, sumfib_cons.
   generalize (fib_nz (2*k+1)); omega.
 + apply Delta_app with (2*k+1); auto using Delta_evens.
   intros y Hy; apply evens_in in Hy; omega.
 + omega.
Qed.

Lemma One_pred_High n : 1<n -> One 2 n -> High 2 (n-1).
Proof.
 intros N O.
 rewrite High_succ_One. split; try omega.
 now replace (S (n-1)) with n by omega.
Qed.

Lemma Two_pred_One n : Two 2 n -> One 2 (n-1).
Proof.
 intros. now apply Even_pred_One, Two_Even.
Qed.

Lemma Three_pred_Two n : Three 2 n -> Two 2 (n-1).
Proof.
 intros (l & -> & D & _). simpl.
 exists l; repeat split; auto.
 apply Delta_low_hd with 3; auto.
Qed.

Lemma OddHigh_pred_TwoEven n :
 Odd 2 n -> ~One 2 n -> ~Three 2 n -> TwoEven 2 (n-1).
Proof.
 intros (k,L) H H'.
 assert (1<k) by (destruct k as [|[|k]]; intuition).
 clear H H'.
 destruct L as (l & E & D & _).
 exists 2. exists (map (fun n=>4+n) (evens (k-2)) ++ l).
 rewrite !app_comm_cons.
 assert (Eq : evens k = 2::2*2::map (fun n=>4+n) (evens (k-2))).
 { replace k with (S (S (k-2))) at 1 by omega.
   do 2 (rewrite <- S_odds, odds_S). simpl.
   now rewrite !map_map. }
 rewrite <- Eq. split.
 - rewrite E, sumfib_cons, sumfib_app, sumfib_evens.
   generalize (fib_nz (2*k+1)); omega.
 - apply Delta_app with (2*k+1); auto using Delta_evens.
   intros y Hy. apply evens_in in Hy. omega.
Qed.

(** We can now prove alternate formulations for [TwoEven]
    and [TwoOdd]. *)

Lemma TwoEven_alt n :
  TwoEven 2 n <-> Two 2 n /\ Even 2 (n-2).
Proof.
 split.
 - intros H. split.
   + now apply TwoEven_Two.
   + destruct H as (k & l & E & D).
     exists k; exists l; repeat split; eauto.
     * subst n. simpl. omega.
     * inversion_clear D. omega.
 - intros ((l & E & D & _),(k & l' & E' & Hk & D')).
   assert (4 <= n).
   { rewrite sumfib_cons in E'.
     generalize (@fib_mono 2 (2*k)). simpl (fib 2). omega. }
   assert (k<>1).
   { intros ->. simpl mult in *.
     apply (@One_not_High (n-1)).
     - apply Even_pred_One. exists 1; exists l; auto.
     - replace (n-1) with (S (n-2)) by omega.
       apply Two_succ_OddHigh. exists l'; auto. }
   exists k; exists l'; split.
   + subst n. simpl in *. omega.
   + constructor; auto. omega.
Qed.

Lemma TwoOdd_alt n :
  TwoOdd 2 n <-> Two 2 n /\ Odd 2 (n-2).
Proof.
 split.
 - intros H. split.
   + now apply TwoOdd_Two.
   + destruct H as (k & l & E & D).
     exists k; exists l; repeat split; eauto.
     * subst n. simpl. omega.
     * omega.
 - intros ((l & E & D & _),(k & l' & E' & D' & K')).
   assert (3<=n).
   { rewrite sumfib_cons in E'.
     generalize (@fib_mono 1 (2*k+1)). simpl (fib 1). omega. }
   assert (k<>0).
   { intros ->. simpl plus in *.
     apply (@One_not_Two'' (n-1)).
     - apply Low_21, Even_pred_One.
       exists 1. simpl. exists l; auto.
     - replace (n-1) with (S (n-2)) by omega.
       apply One_succ_Two. exists l'; auto. }
   assert (k<>1).
   { intros ->. simpl plus in *.
     assert (Eq : 1::l = 1::3::l').
     { apply decomp_unique; eauto using Delta_nz, Delta_low_hd.
       simpl in *; omega. }
     injection Eq as ->. inversion D; omega. }
   exists k; exists l'; split.
   + subst n. simpl in *. omega.
   + constructor; auto. omega.
Qed.

(** ** Two consecutive [TwoEven] numbers are separated by 5 or 8 *)

Lemma TwoEven_next n :
  TwoEven 2 n -> TwoEven 2 (n+5) \/ TwoEven 2 (n+8).
Proof.
  intros (k & l & E & D).
  destruct k as [|[|[|k]]].
  - simpl in D. inversion D. omega.
  - simpl in D. inversion D. omega.
  - simpl in *.
    destruct l as [|k l].
    + simpl in *.
      right. exists 3; exists []. subst. split; auto.
      constructor. omega. constructor.
    + right. apply TwoEven_12.
      destruct (le_lt_dec k 6).
      * assert (k=6).
        { inversion D; subst. inversion H3; subst. omega. }
        subst k.
        exists 2; exists (7::l); split.
        { subst; simpl; omega. }
        { constructor. omega. constructor. omega. eauto. }
      * exists 3; exists (k::l); split.
        { subst; simpl; omega. }
        { constructor. omega. constructor. omega. eauto. }
  - left. apply TwoEven_12.
    exists 2; exists (2*(3+k)::l); split.
    { subst. simpl. omega. }
    { constructor. omega. constructor. omega. eauto. }
Qed.

Lemma TwoEven_add_1 n : TwoEven 2 n -> High 2 (n+1).
Proof.
  intros.
  rewrite Nat.add_1_r. now apply Two_succ_OddHigh, TwoEven_Two.
Qed.

Lemma TwoEven_add_2 n : TwoEven 2 n -> One 2 (n+2).
Proof.
 intros.
 rewrite Nat.add_succ_r. now apply High_succ_One, TwoEven_add_1.
Qed.

Lemma TwoEven_add_3 n : TwoEven 2 n -> TwoOdd 2 (n+3) \/ High 2 (n+3).
Proof.
  intros (k & l & E & D).
  destruct k as [|[|[|k]]].
  - inversion D; omega.
  - inversion D; omega.
  - apply TwoOdd_12.
    exists 2; exists l; split.
    + subst; simpl; omega.
    + constructor. omega. simpl. eauto.
  - right.
    apply High_12.
    exists 4; split; auto. exists (2*(3+k)::l); repeat split; auto.
    + subst; simpl; omega.
    + apply Delta_inv in D. constructor. omega. eauto.
Qed.

Lemma TwoEven_add_4 n : TwoEven 2 n -> One 2 (n+4) \/ High 2 (n+4).
Proof.
  intros H.
  rewrite Nat.add_succ_r.
  destruct (TwoEven_add_3 H) as [H'|H'].
  - right. now apply Two_succ_OddHigh, TwoOdd_Two.
  - left. now apply High_succ_One.
Qed.

Lemma TwoEven_add_6 n : TwoEven 2 n -> High 2 (n+6).
Proof.
  intros (k & l & E & D).
  apply High_12.
  destruct k as [|[|[|k]]].
  - inversion D; omega.
  - inversion D; omega.
  - exists 4; split; auto. exists (5::l); repeat split; auto.
    + subst; simpl; omega.
    + constructor. omega. eauto.
  - exists 5; split; auto. exists (2*(3+k)::l); repeat split; auto.
    + subst; simpl; omega.
    + constructor. omega. eauto.
Qed.

Lemma TwoEven_add_7 n : TwoEven 2 n -> One 2 (n+7).
Proof.
  intros. rewrite Nat.add_succ_r.
  now apply High_succ_One, TwoEven_add_6.
Qed.

Lemma TwoEven_next_5_xor_8 n :
  TwoEven 2 (n+5) -> TwoEven 2 (n+8) -> False.
Proof.
 intros Hn.
 change (~TwoEven 2 (n+8)).
 apply TwoEven_add_3 in Hn.
 replace (n+5+3) with (n+8) in Hn by omega.
 destruct Hn; auto.
Qed.

Lemma TwoEven_next5 n :
 TwoEven 2 n -> TwoEven 2 (n+5) ->
 forall m, n<m<n+5 -> ~TwoEven 2 m.
Proof.
 intros Hn Hn' m H.
 assert (Hm : m=n+1 \/ m=n+2 \/ m=n+3 \/ m=n+4) by omega.
 destruct Hm as [Hm|[Hm|[Hm|Hm]]]; subst m.
 - apply TwoEven_add_1 in Hn. auto.
 - apply TwoEven_add_2 in Hn. auto.
 - apply TwoEven_add_3 in Hn. destruct Hn; auto.
 - apply TwoEven_add_4 in Hn. destruct Hn; auto.
Qed.

Lemma TwoEven_next8 n :
 TwoEven 2 n -> TwoEven 2 (n+8) ->
 forall m, n<m<n+8 -> ~TwoEven 2 m.
Proof.
 intros Hn Hn' m H.
 assert (Hm : m=n+1 \/ m=n+2 \/ m=n+3 \/ m=n+4 \/
              m=n+5 \/ m=n+6 \/ m=n+7) by omega.
 destruct Hm as [Hm|[Hm|[Hm|[Hm|[Hm|[Hm|Hm]]]]]]; subst m.
 - apply TwoEven_add_1 in Hn. auto.
 - apply TwoEven_add_2 in Hn. auto.
 - apply TwoEven_add_3 in Hn. destruct Hn; auto.
 - apply TwoEven_add_4 in Hn. destruct Hn; auto.
 - intros Hn''. eapply TwoEven_next_5_xor_8; eauto.
 - apply TwoEven_add_6 in Hn. auto.
 - apply TwoEven_add_7 in Hn. auto.
Qed.

Lemma TwoEven_next_inv n m :
  TwoEven 2 n -> TwoEven 2 m -> n < m ->
  (forall p, n < p < m -> ~TwoEven 2 p) ->
  m = n+5 \/ m = n+8.
Proof.
  intros Hn Hm LT Hp.
  destruct (TwoEven_next Hn) as [Hn'|Hn'].
  - destruct (lt_eq_lt_dec m (n+5)) as [[LT'|EQ]|LT']; auto.
    + elim (@TwoEven_next5 _ Hn Hn' m). omega. auto.
    + elim (Hp (n+5)). omega. auto.
  - destruct (lt_eq_lt_dec m (n+8)) as [[LT'|EQ]|LT']; auto.
    + elim (@TwoEven_next8 _ Hn Hn' m). omega. auto.
    + elim (Hp (n+8)). omega. auto.
Qed.
