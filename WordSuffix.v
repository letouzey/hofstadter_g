Require Import MoreTac MoreList GenFib Words.
Import ListNotations.

(** * [kword] Suffixes *)

(** Always exactly k different [kword] suffixes of the same length *)

Lemma kword_suffix_cycle k n u :
  Suffix u (kword k n) -> Suffix u (kword k (n+k)).
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - now rewrite Nat.add_0_r.
 - intros Su.
   rewrite kword_eqn by lia. replace (n+k-k) with n by lia.
   now apply Suffix_app_l.
Qed.

Lemma kword_suffix_pcycle k n p u :
  Suffix u (kword k n) -> Suffix u (kword k (n+p*k)).
Proof.
 intros H.
 induction p.
 - simpl. now rewrite Nat.add_0_r.
 - replace (n+S p * k) with ((n+p*k)+k) by lia.
   now apply kword_suffix_cycle.
Qed.

Lemma kword_suffix_cycle' k n u :
  k <= n ->
  length u <= A k (n-k) ->
  Suffix u (kword k n) -> Suffix u (kword k (n-k)).
Proof.
 intros Hn Hu Su.
 destruct (Nat.eq_dec k 0) as [->|K].
 { now rewrite Nat.sub_0_r. }
 rewrite kword_eqn in Su by lia.
 apply Suffix_app_inv in Su.
 destruct Su as [Su|(u' & E & SU)]; trivial.
 rewrite E, app_length, kword_len in Hu.
 assert (Hu' : length u' = 0) by lia.
 rewrite length_zero_iff_nil in Hu'. subst u'. subst u. now exists [].
Qed.

Lemma kword_suffix_pcycle' k n p u :
  p*k <= n ->
  length u <= A k (n-p*k) ->
  Suffix u (kword k n) -> Suffix u (kword k (n-p*k)).
Proof.
 intros Hn Hu SU. revert Hn Hu.
 induction p.
 - intros _ _. simpl. now replace (n-0) with n by lia.
 - intros Hn Hu.
   replace (n - _) with ((n-p*k)-k) in * by lia.
   apply kword_suffix_cycle'. lia. trivial. apply IHp. lia.
   etransitivity; [apply Hu| ]. apply A_mono. lia.
Qed.

(* When n varies, the last letters of the successive [kword k n]
   is (k-1) 0 1 ... (k-1) 0 *)

Lemma kword_last k n : k<>0 -> last (kword k n) 0 = (n+k-1) mod k.
Proof.
 intros K. induction n as [n IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases n (k-1)).
 - rewrite kword_low by lia.
   destruct n.
   + rewrite Nat.mod_small; simpl; lia.
   + replace (S n + k - 1) with (n + 1 * k) by lia.
     rewrite Nat.mod_add, Nat.mod_small by lia.
     now rewrite last_cons, last_seq.
 - rewrite kword_eqn by lia. rewrite last_app.
   2:{ rewrite <- length_zero_iff_nil, kword_len.
       generalize (A_nz k (n - k)). lia. }
   red in H. fixpred. rewrite IH by lia.
   replace (n+k-1) with (n-1 + 1 * k) by lia.
   rewrite Nat.mod_add by lia. f_equal. lia.
Qed.

(** Hence any group of k successive suffixes is without duplicate *)

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
  k<>0 -> u<>[] -> Suffix u (kword k n) -> Suffix u (kword k m) ->
  n mod k = m mod k.
Proof.
 intros K Hu.
 withoutloss2 n m (n<=m).
 { intros LE (v,Hn) (w,Hm).
   rewrite mod_diff; try lia.
   replace (m-n) with ((m+k-1)-(n+k-1)) by lia.
   rewrite <- mod_diff; try lia.
   rewrite <- !kword_last, <- Hn, <- Hm, !last_app; trivial. }
 { destruct (Nat.le_gt_cases n m); intros; auto.
   symmetry; apply WL; auto. lia. }
Qed.

Definition allsuffixesAt k p n0 :=
  map (fun n => lastn p (kword k n)) (seq n0 k).

Definition allsuffixes k p := allsuffixesAt k p (invA_up k p).

Lemma allsuffixesAt_length k p n0 :
  length (allsuffixesAt k p n0) = k.
Proof.
 unfold allsuffixesAt. now rewrite map_length, seq_length.
Qed.

Definition SuffixWords u (f : nat -> word) := exists n, Suffix u (f n).

Lemma allsuffixesAt_spec k p n0 :
  k<>0 -> p <= A k n0 ->
  forall u, In u (allsuffixesAt k p n0) <->
            length u = p /\ SuffixWords u (kword k).
Proof.
 intros K Hn0 u. unfold allsuffixesAt. rewrite in_map_iff. split.
 - intros (n & <- & IN).
   rewrite in_seq in IN. split.
   + rewrite lastn_length_le; auto. rewrite kword_len.
     transitivity (A k n0); trivial. now apply A_mono.
   + exists n. apply lastn_Suffix.
 - intros (Hu,(n & SU)).
   setoid_rewrite in_seq.
   destruct (Nat.le_gt_cases n0 n).
   + assert (E := Nat.div_mod (n-n0) k K).
     set (r := (n-n0) mod k) in *.
     set (s := (n-n0) / k) in *.
     rewrite Nat.mul_comm in E.
     assert (E' : n0+r = n-s*k) by lia.
     exists (n0+r). split.
     2:{ split. lia. generalize (Nat.mod_upper_bound (n-n0) k). lia. }
     apply (kword_suffix_pcycle' k n s u) in SU; try lia.
     * rewrite <- Hu. symmetry. apply Suffix_equiv. now rewrite E'.
     * rewrite <- E', Hu.
       etransitivity; [apply Hn0| ]. apply A_mono; lia.
   + assert (E := Nat.div_mod (n0+(k-1)-n) k K).
     set (r := (n0+(k-1)-n) mod k) in *.
     set (s := (n0+(k-1)-n) / k) in *.
     assert (E' : n0+(k-1)-r = n+s*k) by lia.
     exists (n0+(k-1)-r). split.
     2:{ generalize (Nat.mod_upper_bound (n0+(k-1)-n) k). fold r. lia. }
     apply (kword_suffix_pcycle k n s u) in SU.
     rewrite <- Hu. symmetry. apply Suffix_equiv. now rewrite E'.
Qed.

Lemma allsuffixesAt_nodup k p n0 :
  k<>0 -> p<>0 -> NoDup (allsuffixesAt k p n0).
Proof.
  intros K Hp.
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
  rewrite !kword_last in E'; trivial.
  destruct (Nat.le_gt_cases i j).
  - apply mod_diff in E'; try lia. replace (_-_) with (j-i) in E' by lia.
    rewrite Nat.mod_small in E'; lia.
  - symmetry in E'. apply mod_diff in E'; try lia.
    replace (_-_) with (i-j) in E' by lia.
    rewrite Nat.mod_small in E'; lia.
Qed.

Lemma allsuffixesAt_permut k p n0 n0' :
  k<>0 -> p <= A k n0 -> p <= A k n0' ->
  Permutation (allsuffixesAt k p n0) (allsuffixesAt k p n0').
Proof.
 intros K H H'.
 destruct (Nat.eq_dec p 0) as [->|Hp].
 - unfold allsuffixesAt. apply eq_Permutation.
   rewrite <- (Nat.add_0_r n0), <- (Nat.add_0_r n0').
   rewrite <- !(map_add_seq k 0), !map_map.
   apply map_ext. intros a. unfold lastn.
   now rewrite !Nat.sub_0_r, !skipn_all.
 - apply NoDup_Permutation; auto using allsuffixesAt_nodup.
   intros u. rewrite !allsuffixesAt_spec by trivial. reflexivity.
Qed.

Lemma allsuffixes_length k p : length (allsuffixes k p) = k.
Proof.
 apply allsuffixesAt_length.
Qed.

Lemma allsuffixes_spec k p :
  k<>0 -> forall u, In u (allsuffixes k p) <->
                    length u = p /\ SuffixWords u (kword k).
Proof.
 intros. now apply allsuffixesAt_spec, invA_up_spec.
Qed.

Lemma allsuffixes_nodup k p :
  k<>0 -> p<>0 -> NoDup (allsuffixes k p).
Proof.
 intros. now apply allsuffixesAt_nodup.
Qed.

Lemma SuffixWords_extend k p u :
  k<>0 -> SuffixWords u (kword k) ->
  length u <= p ->
  exists v, length v = p /\ Suffix u v /\ SuffixWords v (kword k).
Proof.
 intros K (n & Hu) LE.
 set (s := S ((p-n)/k)).
 assert (p <= n + s*k).
 { generalize (Nat.div_mod_eq (p-n) k) (Nat.mod_upper_bound (p-n) k).
   lia. }
 set (p' := n+s*k).
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

Lemma allsuffixes_extend k p p' u : k<>0 -> p <= p' ->
  In u (allsuffixes k p) -> exists v, Suffix u v /\ In v (allsuffixes k p').
Proof.
 intros K. rewrite allsuffixes_spec by trivial. intros LE (E,SW).
 destruct (SuffixWords_extend k p' u K SW) as (v & Hv & SU & SW'). lia.
 exists v; split; trivial. now rewrite allsuffixes_spec.
Qed.
