Require Import MoreList GenFib Words.
Import ListNotations.

(** * [kword] Suffixes *)

(** Always exactly (k+1) different [kword] suffixes of the same length *)

Lemma kword_suffix_cycle k n u :
  Suffix u (kword k n) -> Suffix u (kword k (n+S k)).
Proof.
 intros Su.
 rewrite Nat.add_succ_r, kword_alt by lia. replace (n+k-k) with n by lia.
 now apply Suffix_app_l.
Qed.

Lemma kword_suffix_pcycle k n p u :
  Suffix u (kword k n) -> Suffix u (kword k (n+p*S k)).
Proof.
 intros H.
 induction p.
 - simpl. now rewrite Nat.add_0_r.
 - replace (n+S p * S k) with ((n+p*S k)+S k) by lia.
   now apply kword_suffix_cycle.
Qed.

Lemma kword_suffix_cycle' k n u :
  S k <= n ->
  length u <= A k (n-S k) ->
  Suffix u (kword k n) -> Suffix u (kword k (n-S k)).
Proof.
 intros Hn Hu Su.
 replace n with (S (n-1)) in Su by lia.
 rewrite kword_alt in Su by lia.
 replace (n-1-k) with (n-S k) in Su by lia.
 apply Suffix_app_inv in Su.
 destruct Su as [Su|(u' & E & SU)]; trivial.
 rewrite E, app_length, kword_len in Hu.
 assert (Hu' : length u' = 0) by lia.
 rewrite length_zero_iff_nil in Hu'. subst u'. subst u. now exists [].
Qed.

Lemma kword_suffix_pcycle' k n p u :
  p*S k <= n ->
  length u <= A k (n-p*S k) ->
  Suffix u (kword k n) -> Suffix u (kword k (n-p*S k)).
Proof.
 intros Hn Hu SU. revert Hn Hu.
 induction p.
 - intros _ _. simpl. now replace (n-0) with n by lia.
 - intros Hn Hu.
   replace (n - _) with ((n-p*S k)-S k) in * by lia.
   apply kword_suffix_cycle'. lia. trivial. apply IHp. lia.
   etransitivity; [apply Hu| ]. apply A_mono. lia.
Qed.

(* When n varies, the last letters of the successive [kword k n]
   is k 0 1 ... k 0 *)

Lemma kword_last k n : last (kword k n) 0 = (n+k) mod (S k).
Proof.
 induction n as [n IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases n k).
 - rewrite kword_low by lia.
   destruct n.
   + rewrite Nat.mod_small; simpl; lia.
   + replace (S n + k) with (n + 1 * S k) by lia.
     rewrite Nat.mod_add, Nat.mod_small by lia.
     now rewrite last_cons, last_seq.
 - destruct n as [|n]; try lia.
   replace (S n + k) with (n + 1 * S k) by lia.
   rewrite Nat.mod_add by lia.
   rewrite kword_alt by lia. rewrite last_app.
   2:{ rewrite <- length_zero_iff_nil, kword_len.
       generalize (A_nz k (n - k)). lia. }
   destruct (Nat.eq_dec k n) as [->|NE].
   + now rewrite Nat.sub_diag, Nat.mod_small by lia.
   + replace (n-k) with (S (n-S k)) by lia.
     rewrite IH by lia. f_equal. lia.
Qed.

(** Hence any group of (k+1) successive suffixes is without duplicate *)

Lemma mod_diff a a' b :
  b <> 0 -> a <= a' -> a mod b = a' mod b <-> (a'-a) mod b = 0.
Proof.
 intros Hb Ha.
 split.
 - rewrite (Nat.div_mod_eq a b) at 2.
   rewrite (Nat.div_mod_eq a' b) at 2.
   intros ->.
   replace (_-_) with (b*(a'/b) - b*(a/b)) by lia.
   rewrite <- Nat.mul_sub_distr_l, Nat.mul_comm.
   now rewrite Nat.mod_mul.
 - assert (E := Nat.div_mod_eq (a'-a) b).
   intros E'.
   replace a' with (a + b*((a'-a)/b)) by lia. rewrite Nat.mul_comm.
   rewrite Nat.mod_add; trivial.
Qed.

Lemma kword_suffix_cycle_inv0 k u n m :
  u<>[] -> Suffix u (kword k n) -> Suffix u (kword k m) ->
  n mod (S k) = m mod (S k).
Proof.
 intros Hu. revert n m.
 (* wlog *)
 assert (forall n m, n <= m ->
         Suffix u (kword k n) -> Suffix u (kword k m) ->
         n mod (S k) = m mod (S k)).
 { intros n m LE (v,Hn) (w,Hm).
   rewrite mod_diff; try lia.
   replace (m-n) with ((m+k)-(n+k)) by lia.
   rewrite <- mod_diff; try lia.
   rewrite <- !kword_last, <- Hn, <- Hm.
   now rewrite !last_app. }
 intros n m; destruct (Nat.le_gt_cases n m); intros; auto.
 symmetry; apply H; auto. lia.
Qed.

Definition allsuffixesAt k p n0 :=
  map (fun n => lastn p (kword k n)) (seq n0 (S k)).

Definition allsuffixes k p := allsuffixesAt k p (invA_up k p).

Lemma allsuffixesAt_length k p n0 :
  length (allsuffixesAt k p n0) = S k.
Proof.
 unfold allsuffixesAt. now rewrite map_length, seq_length.
Qed.

Definition SuffixWords u (f : nat -> word) := exists n, Suffix u (f n).

Lemma allsuffixesAt_spec k p n0 :
  p <= A k n0 ->
  forall u, In u (allsuffixesAt k p n0) <->
            length u = p /\ SuffixWords u (kword k).
Proof.
 intros Hn0 u. unfold allsuffixesAt. rewrite in_map_iff. split.
 - intros (n & <- & IN).
   rewrite in_seq in IN. split.
   + rewrite lastn_length_le; auto. rewrite kword_len.
     transitivity (A k n0); trivial. now apply A_mono.
   + exists n. apply lastn_Suffix.
 - intros (Hu,(n & SU)).
   setoid_rewrite in_seq.
   destruct (Nat.le_gt_cases n0 n).
   + assert (NZ : S k <> 0) by lia.
     assert (E := Nat.div_mod (n-n0) (S k) NZ).
     set (r := (n-n0) mod S k) in *.
     set (q := (n-n0) / S k) in *.
     rewrite Nat.mul_comm in E.
     assert (E' : n0+r = n-q*S k) by lia.
     exists (n0+r). split.
     2:{ split. lia. generalize (Nat.mod_upper_bound (n-n0) (S k)). lia. }
     apply (kword_suffix_pcycle' k n q u) in SU; try lia.
     * rewrite <- Hu. symmetry. apply Suffix_equiv. now rewrite E'.
     * rewrite <- E', Hu.
       etransitivity; [apply Hn0| ]. apply A_mono; lia.
   + assert (NZ : S k <> 0) by lia.
     assert (E := Nat.div_mod (n0+k-n) (S k) NZ).
     set (r := (n0+k-n) mod S k) in *.
     set (q := (n0+k-n) / S k) in *.
     assert (E' : n0+k-r = n+q*S k) by lia.
     exists (n0+k-r). split.
     2:{ generalize (Nat.mod_upper_bound (n0+k-n) (S k)). fold r. lia. }
     apply (kword_suffix_pcycle k n q u) in SU.
     rewrite <- Hu. symmetry. apply Suffix_equiv. now rewrite E'.
Qed.

Lemma allsuffixesAt_nodup k p n0 :
  p<>0 -> NoDup (allsuffixesAt k p n0).
Proof.
  intros Hp.
  unfold allsuffixesAt. set (f := fun n => _).
  apply NoDup_nth with (d:=f 0).
  intros i j. rewrite map_length, seq_length. intros Hi Hj.
  rewrite !map_nth, !seq_nth by lia.
  unfold f; clear f.
  intros E.
  assert (E' : last (kword k (n0+i)) 0 = last (kword k (n0+j)) 0).
  { rewrite <- last_lastn with (n:=p) by trivial.
    rewrite <- (last_lastn (kword k (n0+j)) p) by trivial.
    now f_equal. }
  rewrite !kword_last in E'.
  destruct (Nat.le_gt_cases i j).
  - apply mod_diff in E'; try lia. replace (_-_) with (j-i) in E' by lia.
    rewrite Nat.mod_small in E'; lia.
  - symmetry in E'. apply mod_diff in E'; try lia.
    replace (_-_) with (i-j) in E' by lia.
    rewrite Nat.mod_small in E'; lia.
Qed.

Lemma allsuffixesAt_permut k p n0 n0' :
  p <= A k n0 -> p <= A k n0' ->
  Permutation (allsuffixesAt k p n0) (allsuffixesAt k p n0').
Proof.
 intros H H'.
 destruct (Nat.eq_dec p 0) as [->|Hp].
 - unfold allsuffixesAt. apply eq_Permutation.
   rewrite <- (Nat.add_0_r n0), <- (Nat.add_0_r n0').
   rewrite <- !(map_add_seq (S k) 0), !map_map.
   apply map_ext. intros a. unfold lastn.
   now rewrite !Nat.sub_0_r, !skipn_all.
 - apply NoDup_Permutation; auto using allsuffixesAt_nodup.
   intros u. rewrite !allsuffixesAt_spec by trivial. reflexivity.
Qed.

Lemma allsuffixes_length k p : length (allsuffixes k p) = S k.
Proof.
 apply allsuffixesAt_length.
Qed.

Lemma allsuffixes_spec k p :
  forall u, In u (allsuffixes k p) <->
            length u = p /\ SuffixWords u (kword k).
Proof.
 apply allsuffixesAt_spec, invA_up_spec.
Qed.

Lemma allsuffixes_nodup k p :
  p<>0 -> NoDup (allsuffixes k p).
Proof.
  apply allsuffixesAt_nodup.
Qed.

Lemma SuffixWords_extend k p u :
  SuffixWords u (kword k) ->
  length u <= p ->
  exists v, length v = p /\ Suffix u v /\ SuffixWords v (kword k).
Proof.
 intros (n & Hu) LE.
 set (q := S ((p-n)/S k)).
 assert (p <= n + q*S k).
 { generalize (Nat.div_mod_eq (p-n) (S k)) (Nat.mod_upper_bound (p-n) (S k)).
   lia. }
 set (p' := n+q*S k).
 set (v := lastn p (kword k p')).
 assert (length v = p).
 { unfold v. rewrite lastn_length_le; trivial. rewrite kword_len.
   transitivity (S p'). lia. apply A_lt_id. }
 exists v. repeat split; auto.
 - apply Suffix_Suffix with (kword k p').
   + lia.
   + now apply kword_suffix_pcycle.
   + apply lastn_Suffix.
 - exists p'. apply lastn_Suffix.
Qed.

Lemma allsuffixes_extend k p q u : p <= q ->
  In u (allsuffixes k p) -> exists v, Suffix u v /\ In v (allsuffixes k q).
Proof.
 rewrite allsuffixes_spec. intros LE (E,SW).
 destruct (SuffixWords_extend k q u SW) as (v & Hv & SU & SW'). lia.
 exists v; split; trivial. now rewrite allsuffixes_spec.
Qed.
