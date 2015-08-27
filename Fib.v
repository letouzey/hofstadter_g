Require Import Arith Omega Wf_nat List NPeano.
Require Import DeltaList.
Import ListNotations.
Set Implicit Arguments.

(** * Fibonacci sequence and decomposition *)

(** First, a definition of the Fibonacci sequence.

    We use here the variant that starts with 1 1 2 3 ...
    (no zero).
*)

Fixpoint fib (n:nat) : nat := match n with
  | 0 => 1
  | 1 => 1
  | S ((S n) as p) => fib p + fib n
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


(** Decomposition via sums of Fibonacci numbers.

    Zeckendorf's theorem (actually discovered earlier by
    Lekkerkerker) states that any natural number can be obtained
    by a sum of distinct Fibonacci numbers, and this decomposition
    is moreover unique when :
     - fib 0 isn't in the decomposition
     - Fibonacci numbers in the decomposition aren't consecutive.
*)

(** sumfib

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

(** Technical lemma for Zeckendorf's theorem:
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

(** Normalisation of a Fibonacci decomposition.

    Starting from an increasing decomposition, we can
    transform it into a canonical decomposition (with no
    consecutive Fibonacci numbers), by simply saturating
    the basic Fibonacci equation (fib k + fib (k+1) = fib (k+2))
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

(** Classification of Fibonacci decompositions according to
    their lowest terms: for n>3, a decomposition starts either
    by:
        fib 1 + ...
        fib 2 + fib (2*k) + ...
        fib 2 + fib (2*k+1) + ...
        fib k + ...    (with k>2)
*)

Definition One p n :=
 exists l, n = sumfib (1::l) /\ Delta p (1::l).

Definition TwoEven p n :=
 exists k l, n = sumfib (2::2*k::l) /\ Delta p (2::2*k::l).

Definition TwoOdd p n :=
 exists k l, n = sumfib (2::2*k+1::l) /\ Delta p (2::2*k+1::l).

Definition High p n :=
 exists k l, n = sumfib (k::l) /\ 2<k /\ Delta p (k::l).

Lemma decomp_complete n : 3<n ->
 One 2 n \/ TwoEven 2 n \/ TwoOdd 2 n \/ High 2 n.
Proof.
 intros Hn.
 destruct (decomp_exists n) as (l & H1 & H2 & H3).
 destruct l as [|k l].
 - simpl in H1. omega.
 - destruct k as [|[|[|k]]].
   + simpl in H3. intuition.
   + left. exists l. auto.
   + destruct l as [|k' l].
     * simpl in H1. omega.
     * destruct (Nat.Even_or_Odd k') as [(k2,Hk2)|(k2,Hk2)].
       { right; left. exists k2; exists l. subst. auto. }
       { right; right; left. exists k2; exists l.
         repeat split; subst k'; auto; omega. }
   + right; right; right. exists (3+k); exists l. intuition.
Qed.

Lemma High_equiv n : High 1 n <-> High 2 n.
Proof.
 split; intros (k & l & Hn & Hk & Hl).
 - assert (Hla := norm_ok Hl).
   assert (Hlb := norm_hd (k::l)).
   assert (Hlc := norm_le Hl).
   assert (Hld := norm_sum (k::l)).
   set (l0 := norm (k :: l)) in *.
   destruct l0 as [|k0 l0].
   + elim Hlb.
   + simpl in Hlb. destruct Hlb as (p', Hlb).
     exists k0; exists l0; repeat split; auto; omega.
 - exists k; exists l; auto.
Qed.

Lemma TwoEven_equiv n : TwoEven 1 n <-> TwoEven 2 n.
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
   + right. apply High_equiv.
     subst k0.
     exists 4; exists l0; repeat split; auto. simpl in *. omega.
   + simpl in Hlc. destruct Hlc as (p', Hlc).
     replace k0 with (2*(p+p')+1) in * by omega.
     left. exists (p+p'); exists l0; repeat split.
     { simpl in *. omega. }
     { constructor; auto. inversion Hl; subst. omega. }
Qed.

Lemma One_21 n : One 2 n -> One 1 n.
Proof.
 intros (l & Hn & Hl). exists l; auto.
Qed.

Lemma One_12 n : One 1 n -> One 2 n \/ High 2 n.
Proof.
 intros (l & Hn & Hl).
 destruct l as [|k l].
 - left; exists (@nil nat); auto.
 - inversion_clear Hl.
   assert (Hla := norm_ok H0).
   assert (Hlb := norm_hd (k::l)).
   assert (Hlc := norm_le H0).
   assert (Hld := norm_sum (k::l)).
   set (l0 := norm (k :: l)) in *.
   destruct l0 as [|k0 l0].
   + elim Hlb.
   + simpl in Hlb. destruct Hlb as (p,Hlb).
     destruct (eq_nat_dec k0 2) as [E|N].
     * right. apply High_equiv.
       rewrite E in *.
       exists 3; exists l0; repeat split; auto. simpl in *; omega.
     * left. exists (k0::l0); repeat split.
       { simpl in *; omega. }
       { constructor; auto. omega. }
Qed.

Lemma High_not_TwoEven n : High 2 n -> ~TwoEven 2 n.
Proof.
 intros (k & l & Hn & Hk & Hl) (p & l' & Hn' & Hl').
 assert (E : k::l = 2::2*p::l').
 { apply decomp_unique; try eapply Delta_nz; auto; omega. }
 injection E. omega.
Qed.

Lemma High_not_TwoEven' n : High 1 n -> ~TwoEven 2 n.
Proof.
 intros. now apply High_not_TwoEven, High_equiv.
Qed.

Lemma TwoOdd_not_TwoEven n : TwoOdd 2 n -> ~TwoEven 2 n.
Proof.
 intros (p & l & Hn & Hl) (p' & l' & Hn' & Hl').
 assert (E : 2::2*p+1::l = 2::2*p'::l').
 { apply decomp_unique; try eapply Delta_nz; auto; omega. }
 injection E. omega.
Qed.

Lemma TwoOdd_not_TwoEven' n : TwoOdd 1 n -> ~TwoEven 2 n.
Proof.
 intros H.
 apply TwoOdd_12 in H. destruct H.
 - now apply TwoOdd_not_TwoEven.
 - now apply High_not_TwoEven.
Qed.

Lemma One_not_TwoEven n : One 2 n -> ~TwoEven 2 n.
Proof.
 intros (l & Hn & Hl) (p & l' & Hn' & Hl').
 assert (E : 1::l = 2::2*p::l').
 { apply decomp_unique; try eapply Delta_nz; auto; omega. }
 discriminate.
Qed.

Lemma One_not_TwoEven' n : One 1 n -> ~TwoEven 2 n.
Proof.
 intros H.
 apply One_12 in H. destruct H.
 - now apply One_not_TwoEven.
 - now apply High_not_TwoEven.
Qed.

Hint Resolve One_not_TwoEven' TwoOdd_not_TwoEven' High_not_TwoEven'.


(** Fibonacci decomposition of ((fib k)-1)

    fib (2k) - 1 = fib 1 + fib 3 + ... + fib (2k-1)
    fib (2k+1) - 1 = fib 2 + fib 4 + ... + fib (2k)

    We explicitely builds these decompositions :

    odds k = [1;3;...;(2k-1)]
    evens k = [2;4;...;(2*k)]
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


(** Interval between two consecutive TwoEven numbers is 5 or 8 *)

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
    + right. apply TwoEven_equiv.
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
  - left. apply TwoEven_equiv.
    exists 2; exists (2*(3+k)::l); split.
    { subst. simpl. omega. }
    { constructor. omega. constructor. omega. eauto. }
Qed.

Lemma TwoEven_add_1 n : TwoEven 2 n -> High 1 (n+1).
Proof.
  intros (k & l & E & D).
  exists 3; exists (2*k::l); repeat split.
  - subst; simpl; omega.
  - omega.
  - inversion D; subst. constructor. omega. eauto.
Qed.

Lemma TwoEven_add_2 n : TwoEven 2 n -> One 1 (n+2).
Proof.
  intros (k & l & E & D).
  exists (3::2*k::l); repeat split.
  - subst; simpl; omega.
  - inversion D; subst. constructor. omega. constructor. omega. eauto.
Qed.

Lemma TwoEven_add_3 n : TwoEven 2 n -> TwoOdd 1 (n+3) \/ High 1 (n+3).
Proof.
  intros (k & l & E & D).
  destruct k as [|[|[|k]]].
  - inversion D; omega.
  - inversion D; omega.
  - left.
    exists 2; exists l; split.
    + subst; simpl; omega.
    + constructor. omega. simpl. eauto.
  - right.
    exists 4; exists (2*(3+k)::l); repeat split.
    + subst; simpl; omega.
    + omega.
    + apply Delta_inv in D. constructor. omega. eauto.
Qed.

Lemma TwoEven_add_4 n : TwoEven 2 n -> One 1 (n+4) \/ High 1 (n+4).
Proof.
  intros (k & l & E & D).
  destruct k as [|[|[|k]]].
  - inversion D; omega.
  - inversion D; omega.
  - right.
    exists 3; exists (5::l); repeat split.
    + subst; simpl; omega.
    + omega.
    + constructor. omega. eauto.
  - left.
    exists (4::2*(3+k)::l); repeat split.
    + subst; simpl; omega.
    + constructor. omega. constructor. omega. eauto.
Qed.

Lemma TwoEven_add_6 n : TwoEven 2 n -> High 1 (n+6).
Proof.
  intros (k & l & E & D).
  destruct k as [|[|[|k]]].
  - inversion D; omega.
  - inversion D; omega.
  - exists 4; exists (5::l); repeat split.
    + subst; simpl; omega.
    + omega.
    + constructor. omega. eauto.
  - exists 5; exists (2*(3+k)::l); repeat split.
    + subst; simpl; omega.
    + omega.
    + constructor. omega. eauto.
Qed.

Lemma TwoEven_add_7 n : TwoEven 2 n -> One 1 (n+7).
Proof.
  intros (k & l & E & D).
  destruct k as [|[|[|k]]].
  - inversion D; omega.
  - inversion D; omega.
  - exists (4::5::l); split.
    + subst; simpl; omega.
    + constructor. omega. constructor. omega. eauto.
  - exists (5::2*(3+k)::l); repeat split.
    + subst; simpl; omega.
    + constructor. omega. constructor. omega. eauto.
Qed.

Lemma TwoEven_itvl n m :
  TwoEven 2 n -> TwoEven 2 m -> n < m ->
  (forall p, n < p < m -> ~TwoEven 2 p) ->
  m = n+5 \/ m = n+8.
Proof.
  intros Hn Hm LT Hp.
  assert (H : m <= n+8).
  { apply Nat.le_ngt. intro.
    destruct (TwoEven_next Hn) as [Hn'|Hn'].
    - elim (Hp (n+5)); auto; omega.
    - elim (Hp (n+8)); auto; omega. }
  assert (H' : m = n+1 \/ m = n+2 \/ m = n+3 \/ m = n+4 \/ m = n+5 \/
               m = n+6 \/ m = n+7 \/ m = n+8) by omega.
  destruct H' as [H'|[H'|[H'|[H'|[H'|[H'|[H'|H']]]]]]]; subst m; auto;
   contradict Hm.
  - apply TwoEven_add_1 in Hn. auto.
  - apply TwoEven_add_2 in Hn. auto.
  - apply TwoEven_add_3 in Hn. destruct Hn; auto.
  - apply TwoEven_add_4 in Hn. destruct Hn; auto.
  - apply TwoEven_add_6 in Hn. auto.
  - apply TwoEven_add_7 in Hn. auto.
Qed.
