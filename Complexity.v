Require Import MoreFun MoreList DeltaList GenFib GenG Words Words2.
Import ListNotations.

(** * Follow-up of [Words.v] : Complexity of infinite word [kseq k] *)

(** First, study of [kword] suffixes : always exactly (k+1) different
    suffixes of the same length *)

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

(* TODO move *)
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

Lemma A_above_id k n : n < A k n.
Proof.
 induction n; simpl. lia. generalize (A_nz k (n-k)). lia.
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
   transitivity (S p'). lia. apply A_above_id. }
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


(** Complexity of infinite words : for each value of p,
    number of sub-words of length p *)

Definition subseq q n (f:sequence) := map f (seq q n).

Definition SubSeq u (f:sequence) := exists q, u = subseq q (length u) f.

Definition SubSeqLen p u (f:sequence) := length u = p /\ SubSeq u f.

Lemma SubSeq_alt0 u f : SubSeq u f <-> exists v, Suffix u v /\ PrefixSeq v f.
Proof.
 split.
 - intros (q, E). remember (length u) as n.
   exists (map f (seq 0 (q+n))).
   split.
   + exists (map f (seq 0 q)). subst u. unfold subseq.
     rewrite <- map_app. f_equal. symmetry. apply seq_app.
   + unfold PrefixSeq. now rewrite map_length, seq_length.
 - intros (v & (u' & <-) & PR). exists (length u').
   red in PR. unfold take in PR. rewrite app_length in PR.
   rewrite seq_app, map_app in PR.
   apply app_inv in PR. apply PR. now rewrite map_length, seq_length.
Qed.

Lemma PrefixSeq_app_r u v f : PrefixSeq (u++v) f -> PrefixSeq u f.
Proof.
 unfold PrefixSeq, take. rewrite app_length, seq_app, map_app. intros E.
 apply app_inv in E. apply E. now rewrite map_length, seq_length.
Qed.

Lemma Prefix_PrefixSeq u v f : Prefix u v -> PrefixSeq v f -> PrefixSeq u f.
Proof.
 intros (u' & <-). apply PrefixSeq_app_r.
Qed.

Lemma SubSeq_alt u f : SubSeq u f <-> exists v, Sub u v /\ PrefixSeq v f.
Proof.
 rewrite SubSeq_alt0.
 split.
 - intros (v & SU & PR). exists v; auto using Suffix_Sub.
 - intros (v & (u1 & u2 & <-) & PR). exists (u1++u). split.
   now exists u1. eapply Prefix_PrefixSeq; eauto.
   exists u2; now rewrite app_assoc.
Qed.

Lemma kword_prefixseq k n : PrefixSeq (kword k n) (kseq k).
Proof.
 apply PrefixSeq_napply. apply ksubst_noerase. apply ksubst_prolong.
 reflexivity.
Qed.

Lemma kword_le_prefix k n m : n <= m -> Prefix (kword k n) (kword k m).
Proof.
 induction 1. apply Prefix_id.
 eapply Prefix_trans; eauto.
 destruct (Nat.le_gt_cases m k).
 - rewrite !kword_low by lia.
   exists [m]. now rewrite seq_S.
 - rewrite kword_alt by lia. now exists (kword k (m-k)).
Qed.

Lemma kword_Suffix_Prefix_Sub k u1 u2 n m :
  Suffix u1 (kword k n) -> Prefix u2 (kword k m) ->
  exists q, Sub (u1++u2) (kword k q).
Proof.
 intros SU PR.
 destruct (Nat.le_gt_cases m n).
 - exists (S (n + S k)). rewrite kword_alt by lia.
   assert (HSn : Prefix u2 (kword k (S n))).
   { eapply Prefix_trans; eauto. apply kword_le_prefix. lia. }
   apply kword_suffix_cycle in SU.
   destruct SU as (u1' & E1).
   destruct HSn as (u2' & E2).
   exists u1', u2'. rewrite <- app_assoc, E2, app_assoc, E1.
   f_equal. f_equal. lia.
 - set (m' := n + S ((m-n)/S k)*S k).
   assert (Hm' : m < m').
   { assert (Hk : S k <> 0) by lia.
     assert (E := Nat.div_mod (m-n) (S k) Hk).
     generalize (Nat.mod_upper_bound (m-n) (S k)). lia. }
   apply kword_suffix_pcycle with (p := S ((m-n)/S k)) in SU.
   fold m' in SU.
   assert (HSm' : Prefix u2 (kword k (S m'))).
   { eapply Prefix_trans; eauto. apply kword_le_prefix. lia. }
   exists (S (m' + S k)).
   rewrite kword_alt by lia.
   apply kword_suffix_cycle in SU.
   destruct SU as (u1' & E1).
   destruct HSm' as (u2' & E2).
   exists u1', u2'. rewrite <- app_assoc, E2, app_assoc, E1.
   f_equal. f_equal. lia.
Qed.

Lemma SubSeq_kseq_Sub_kword k u :
 SubSeq u (kseq k) <-> exists n, Sub u (kword k n).
Proof.
 rewrite SubSeq_alt.
 split.
 - intros (v & SU & PR).
   set (n := invA_up k (length v)).
   exists n.
   eapply Sub_Prefix_Sub; eauto.
   eapply PrefixSeq_incl; eauto using kword_prefixseq.
   rewrite kword_len; apply invA_up_spec.
 - intros (n & SU). exists (kword k n); split; trivial.
   apply kword_prefixseq.
Qed.

Lemma Sub_kword_minimal k u n :
 Sub u (kword k n) ->
 exists n0, Sub u (kword k n0) /\ forall q, q<n0 -> ~Sub u (kword k q).
Proof.
 induction n; intros SU.
 - exists 0. split; trivial. inversion 1.
 - destruct (subb_spec u (kword k n)) as [SU'|NS].
   + apply (IHn SU').
   + exists (S n). split; trivial. intros q Hq SU'. apply NS.
     eapply Sub_Prefix_Sub; eauto. apply kword_le_prefix; lia.
Qed.

Lemma SubSeq_kseq_carac k u :
  SubSeq u (kseq k) <->
  Sub u (kword k k) \/
  exists u1 u2, u1<>[] /\ u2<>[] /\ u=u1++u2 /\
     SuffixWords u1 (kword k) /\ PrefixSeq u2 (kseq k).
Proof.
 split.
 - rewrite SubSeq_kseq_Sub_kword. intros (n & SU).
   apply Sub_kword_minimal in SU. clear n.
   destruct SU as (n & SU & NS).
   destruct (Nat.le_gt_cases n k).
   + left. eapply Sub_Prefix_Sub; eauto. apply kword_le_prefix; lia.
   + right. destruct n as [|n]; try lia.
     rewrite kword_alt in SU by lia.
     apply Sub_app_inv in SU.
     destruct SU as [SU|[SU|(u1 & u2 & E & SU & PR)]].
     * exfalso. apply (NS n); auto.
     * exfalso. apply (NS (n-k)); auto; lia.
     * exists u1, u2; repeat split; trivial.
       { intros ->. simpl in E. subst u2. apply Prefix_Sub in PR.
         apply (NS (n-k)); auto; lia. }
       { intros ->. simpl in E. rewrite app_nil_r in E.
         subst u1. apply Suffix_Sub in SU. apply (NS n); auto. }
       { now exists n. }
       { eapply Prefix_PrefixSeq; eauto. apply kword_prefixseq. }
 - rewrite SubSeq_alt.
   intros [SU|(u1 & u2 & Hu1 & Hu2 & E & SU & PR)].
   + exists (kword k k); split; trivial.
     apply PrefixSeq_napply; try easy.
     apply ksubst_noerase. apply ksubst_prolong.
   + subst. destruct SU as (n & SU).
     set (m := invA_up k (length u2)).
     assert (Hm : Prefix u2 (kword k m)).
     { eapply PrefixSeq_incl; eauto using kword_prefixseq.
       rewrite kword_len; apply invA_up_spec. }
     destruct (kword_Suffix_Prefix_Sub k u1 u2 n m) as (q & Hq); trivial.
     exists (kword k q); split; auto using kword_prefixseq.
Qed.

Lemma allsubs_kword_nodup k p : p<>0 -> NoDup (allsubs p (kword k k)).
Proof.
 intros Hp.
 unfold allsubs.
 rewrite kword_low by lia. simpl length. rewrite seq_length.
 set (f := fun i => _).
 rewrite NoDup_nth with (d:=f 0).
 rewrite map_length, seq_length. intros i j Hi Hj.
 rewrite !map_nth, !seq_nth; auto. unfold f; clear f. simpl.
 assert (F0 : hd 0 (sub (k::seq 0 k) 0 p) = k).
 { unfold hd, sub. simpl. destruct p; simpl; lia. }
 assert (F : forall x, 0<S x<S (S k)-p ->
             hd 0 (sub (k::seq 0 k) (S x) p) = x).
 { intros x Hx. unfold hd, sub. simpl. rewrite skipn_seq.
   rewrite firstn_seq by lia. destruct p; simpl; lia. }
 intros E.
 assert (E' : hd 0 (sub (k :: seq 0 k) i p) =
              hd 0 (sub (k :: seq 0 k) j p)).
 { unfold letter in E. now rewrite E. }
 clear E.
 destruct i, j; trivial.
 - rewrite F0, (F j) in E'; lia.
 - rewrite (F i), F0 in E'; lia.
 - rewrite (F i), (F j) in E'; lia.
Qed.

Definition kprefix k n := firstn n (kword k (invA_up k n)).

Lemma kprefix_length k n : length (kprefix k n) = n.
Proof.
 unfold kprefix. rewrite firstn_length_le; auto.
 rewrite kword_len. apply invA_up_spec.
Qed.

Lemma kprefix_ok k n : PrefixSeq (kprefix k n) (kseq k).
Proof.
 unfold kprefix. eapply Prefix_PrefixSeq; eauto.
 apply firstn_Prefix. apply kword_prefixseq.
Qed.

Lemma kprefix_alt k n : kprefix k n = take n (kseq k).
Proof.
 generalize (kprefix_ok k n). unfold PrefixSeq.
 now rewrite kprefix_length.
Qed.

Lemma kprefix_prefix_kword k n p :
  n <= A k p -> Prefix (kprefix k n) (kword k p).
Proof.
 intros. eapply PrefixSeq_incl; eauto using kprefix_ok, kword_prefixseq.
 now rewrite kprefix_length, kword_len.
Qed.

Lemma kprefix_A_kword k p : kprefix k (A k p) = kword k p.
Proof.
 assert (P := kprefix_prefix_kword k (A k p) p (Nat.le_refl _)).
 rewrite Prefix_equiv in P. rewrite P, kprefix_length, <- kword_len.
 apply firstn_all.
Qed.


(** A first listing of factors, which is complete but may contain
    a few duplicates *)

Definition kfactors0 k p :=
 allsubs p (kword k k) ++
 flat_map (fun p1 => map_appr (allsuffixes k p1) (kprefix k (p-p1)))
  (seq 1 (p-1)).

Lemma kfactors0_in k p u : In u (kfactors0 k p) <-> SubSeqLen p u (kseq k).
Proof.
 unfold kfactors0, SubSeqLen.
 rewrite in_app_iff, allsubs_ok, SubSeq_kseq_carac, in_flat_map.
 split.
 - intros [(L,S)|(p1 & IN & IN')].
   + split; auto.
   + rewrite in_seq in IN.
     rewrite map_appr_in in IN'. destruct IN' as (u1 & <- & IN').
     rewrite allsuffixes_spec in IN'. destruct IN' as (IN', SU).
     destruct SU as (m & SU).
     set (u2 := kprefix k (p-p1)).
     split.
     * rewrite app_length, IN'. unfold u2.
       rewrite kprefix_length. lia.
     * right. exists u1, u2; repeat split.
       { rewrite <- length_zero_iff_nil, IN'. lia. }
       { rewrite <- length_zero_iff_nil. unfold u2.
         rewrite kprefix_length. lia. }
       { now exists m. }
       { unfold u2. apply kprefix_ok. }
 - intros (L, [S|(u1 & u2 & Hu1 & Hu2 & -> & SU & PR)]).
   + left; auto.
   + right.
     rewrite app_length in L.
     set (p1 := length u1) in *.
     exists p1. split.
     * rewrite in_seq. rewrite <- length_zero_iff_nil in Hu1, Hu2. lia.
     * apply map_appr_in. exists u1. rewrite allsuffixes_spec; split; auto.
       f_equal. rewrite kprefix_alt. rewrite PR. f_equal. lia.
Qed.

(** Similar to ksubsdups, but much more efficient.
    Still with a few duplicates. *)

Definition kfactors0opt k p :=
  let p' := pred p in
  let q := invA_up k p' in
  let pref := firstn p' (kword k q) in
  let suffs := allsuffixesAt k p' q in
  allsubs p (kword k k) ++ flat_map (allsubs p) (map_appr suffs pref).

Lemma kfactors0opt_0_r k u : In u (kfactors0opt k 0) <-> u = [].
Proof.
 unfold kfactors0opt. rewrite in_app_iff.
 split.
 - intros [IN|IN].
   + now rewrite allsubs_ok, length_zero_iff_nil in IN.
   + rewrite in_flat_map in IN. destruct IN as (w & _ & IN).
     apply allsubs_ok in IN.
     now apply length_zero_iff_nil.
 - intros ->. left. apply allsubs_ok. auto using Sub_nil_l.
Qed.

Lemma kfactors0opt_in k p u :
  In u (kfactors0opt k p) <-> SubSeqLen p u (kseq k).
Proof.
 destruct (Nat.eq_dec p 0) as [->|Hp].
 - rewrite kfactors0opt_0_r. split.
   + intros ->. split; auto. now exists 0.
   + unfold SubSeqLen. now rewrite length_zero_iff_nil.
 - rewrite <- kfactors0_in.
   unfold kfactors0, kfactors0opt.
   set (p' := pred p).
   fold (allsuffixes k p').
   fold (kprefix k p').
   rewrite !in_app_iff, !in_flat_map. apply or_iff_compat_l. split.
   + intros (w0 & Hw0 & Hu).
     rewrite map_appr_in in Hw0.
     destruct Hw0 as (w & <- & Hw).
     apply allsuffixes_spec in Hw. destruct Hw as (Hw,SF).
     rewrite allsubs_ok in Hu. destruct Hu as (Hu,SB).
     apply Sub_app_inv in SB.
     destruct SB as [SB|[SB|(u1 & u2 & -> & H1 & H2)]].
     * apply Sub_len in SB. lia.
     * apply Sub_len in SB. rewrite kprefix_length in SB. lia.
     * rewrite app_length in Hu.
       set (p1 := length u1) in *.
       exists p1; split; auto.
       { rewrite in_seq.
         apply Suffix_len in H1. apply Prefix_len in H2.
         rewrite kprefix_length in H2. lia. }
       { apply map_appr_in. exists u1. split.
         - f_equal.
           assert (PR : PrefixSeq u2 (kseq k)).
           { eapply Prefix_PrefixSeq; eauto. apply kprefix_ok. }
           rewrite kprefix_alt, PR. f_equal. lia.
         - rewrite allsuffixes_spec. split; auto. unfold SuffixWords in *.
           destruct SF as (n & SF). exists n.
           apply Suffix_trans with w; auto. }
   + intros (p1 & Hp1 & Hu). apply in_seq in Hp1. apply map_appr_in in Hu.
     destruct Hu as (u1 & <- & Hu1).
     destruct (allsuffixes_extend k p1 p' u1) as (u1' & Hu1');
      trivial; try lia.
     exists (u1' ++ kprefix k p'); split.
     * apply map_appr_in. now eexists.
     * apply allsubs_ok; split.
       { rewrite app_length, kprefix_length.
         apply allsuffixes_spec in Hu1. lia. }
       { destruct Hu1' as ((v & <-),_).
         assert (PR : Prefix (kprefix k (p-p1)) (kprefix k p')).
         { eapply PrefixSeq_incl; eauto using kprefix_ok.
           rewrite !kprefix_length. lia. }
         destruct PR as (w & <-).
         exists v, w. now rewrite !app_assoc. }
Qed.

Lemma kfactors0opt_nbocc0_le k p a b :
  extrems (map (nbocc 0) (kfactors0opt k p)) = (a,b) -> a <= p /\ b <= p.
Proof.
 set (l := map (nbocc 0) (kfactors0opt k p)).
 destruct (list_eq_dec Nat.eq_dec l []) as [->|NE].
 - inversion 1. lia.
 - intros E. generalize (extrems_in1 l NE) (extrems_in2 l NE).
   rewrite E. simpl. unfold l.
   rewrite !in_map_iff. intros (u & <- & Hu) (v & <- & Hv).
   rewrite kfactors0opt_in in Hu, Hv.
   split.
   + destruct Hu as (<-,_); apply nbocc_le_length.
   + destruct Hv as (<-,_); apply nbocc_le_length.
Qed.

(** Application to quasi-additivity of f, in a faster way than in GenAdd *)

Lemma f_additivity_via_factors k p a b :
 k<>0 ->
 extrems (map (nbocc 0) (kfactors0opt k p)) = (a,b) ->
 forall n, f k n + (p-b) <= f k (n+p) <= f k n + (p-a).
Proof.
 intros Hk E n.
 assert (Hn := f_count_0 k n Hk).
 assert (Hnp := f_count_0 k (n+p) Hk).
 rewrite count_nbocc in Hn,Hnp.
 set (u := @take nat n (kseq k)) in *.
 set (w := @take nat (n+p) (kseq k)) in *.
 set (v := lastn p w).
 assert (Hw : w = u++v).
 { rewrite <- (firstn_skipn n w). f_equal.
   - unfold u, w. rewrite firstn_take; trivial. lia.
   - unfold v, lastn. f_equal. unfold w. rewrite take_length. lia. }
 rewrite Hw, nbocc_app in Hnp.
 assert (a <= nbocc 0 v <= b).
 { eapply extrems_spec; eauto. apply in_map.
   rewrite kfactors0opt_in. split.
   - unfold v. rewrite lastn_length_le; auto.
     unfold w. rewrite take_length; lia.
   - rewrite SubSeq_alt0. exists w. split. now exists u.
     unfold w. red. now rewrite take_length. }
 generalize (kfactors0opt_nbocc0_le k p a b E). lia.
Qed.

Lemma f_additivity_via_factors' k p a b :
 k<>0 -> a <= p -> b <= p ->
 extrems (map (nbocc 0) (kfactors0opt k p)) = (p-b,p-a) ->
 forall n, f k n + a <= f k (n+p) <= f k n + b.
Proof.
 intros Hk Ha Hb E n.
 generalize (f_additivity_via_factors k p _ _ Hk E n).
 replace (p-(p-a)) with a; replace (p-(p-b)) with b; lia.
Qed.

Ltac solve_additivity :=
 apply f_additivity_via_factors';
 [ apply Nat.eqb_neq; now vm_compute |
   apply Nat.leb_le; now vm_compute |
   apply Nat.leb_le; now vm_compute |
   match goal with |- _ = ?p =>
     vm_cast_no_check (@eq_refl _ p); reflexivity
   end ].

Lemma f5_add_424 n : f 5 n + 326 <= f 5 (n+424) <= f 5 n + 333.
Proof.
 solve_additivity.
Qed.

Lemma f6_add_424 n : f 6 n + 333 <= f 6 (n+424) <= f 6 n + 342.
Proof.
 solve_additivity.
Qed.

Lemma f5_below_f6 n : f 5 n <= f 6 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 424) as [LT|LE].
- clear IH.
  assert
    (E : forallb (fun n => Nat.leb (fopt 5 n) (fopt 6 n)) (seq 0 424) = true)
    by now vm_compute.
  rewrite <- !fopt_spec, <- Nat.leb_le.
  rewrite forallb_forall in E. apply E. apply in_seq. lia.
- replace n with ((n-424)+424) by lia.
  etransitivity; [ apply f5_add_424 | ].
  etransitivity; [ | apply f6_add_424 ].
  specialize (IH (n-424)). lia.
Qed.

(*
Lemma f6_add_843 n : f 6 n + 666 <= f 6 (n+843) <= f 6 n + 677.
Proof.
 solve_additivity.
Qed.

Lemma f7_add_843 n : f 7 n + 677 <= f 7 (n+843) <= f 7 n + 692.
Proof.
 solve_additivity.
Qed.

Lemma f6_below_f7 n : f 6 n <= f 7 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 843) as [LT|LE].
- clear IH.
  assert
    (E : forallb (fun n => Nat.leb (fopt 6 n) (fopt 7 n)) (seq 0 843) = true)
    by now vm_compute.
  rewrite <- !fopt_spec, <- Nat.leb_le.
  rewrite forallb_forall in E. apply E. apply in_seq. lia.
- replace n with ((n-843)+843) by lia.
  etransitivity; [ apply f6_add_843 | ].
  etransitivity; [ | apply f7_add_843 ].
  specialize (IH (n-843)). lia.
Qed.

Lemma f7_add_1617 n : f 7 n + 1304 <= f 7 (n+1617) <= f 7 n + 1322.
Proof.
 solve_additivity.
Qed.

Lemma f8_add_1617 n : f 8 n + 1322 <= f 8 (n+1617) <= f 8 n + 1345.
Proof.
 solve_additivity.
Time Qed. (* 50s *)
*)

(** Any kprefix u longer than (k+2) can be decomposed uniquely into
    - the larger possible kword which is a strict prefix of u.
    - and then a strict suffix of u which is also a kprefix.
*)

Definition invA_low k q := pred (invA_up k q).
Definition prevkword k q := kword k (invA_low k q).
Definition prevkprefix k q := kprefix k (q - length (prevkword k q)).

(** [invA_low k q] is the largest index of A numbers strictly below q *)

Lemma invA_low_spec k q :
  2 <= q -> A k (invA_low k q) < q <= A k (S (invA_low k q)).
Proof.
 unfold invA_low, invA_up. cbn - [A]. generalize (invA_spec k (q-2)); lia.
Qed.

Lemma invA_low_spec' k q p :
  A k p < q <= A k (S p) -> invA_low k q = p.
Proof.
 intros. unfold invA_low, invA_up. simpl. apply invA_spec'.
 generalize (A_nz k p). lia.
Qed.

Lemma invA_low_pred k q :
  invA_low k q = invA_low k (q-1) \/ invA_low k q = S (invA_low k (q-1)).
Proof.
 destruct (Nat.le_gt_cases q 2).
 - unfold invA_low, invA_up. simpl.
   replace (q-2) with 0; replace (q-1-2) with 0; lia.
 - destruct (invA_low_spec k q); try lia.
   destruct (invA_low_spec k (q-1)); try lia.
   set (p := invA_low k q) in *.
   set (p' := invA_low k (q-1)) in *.
   assert (p' <= p). { apply Nat.lt_succ_r. apply (@A_lt_inv k). lia. }
   assert (p <= S p'). { apply (@A_le_inv k). lia. }
   lia.
Qed.

Lemma invA_low_flat k q :
 2 < q -> invA_low k q = invA_low k (q-1) <-> A k (invA_low k q) < q-1.
Proof.
 intros Q.
 destruct (invA_low_spec k q); try lia.
 destruct (invA_low_spec k (q-1)); try lia.
 set (p := invA_low k q) in *.
 set (p' := invA_low k (q-1)) in *.
 split.
 - now intros <-.
 - intros. apply Nat.le_antisymm.
   + apply Nat.lt_succ_r. apply (@A_lt_inv k). lia.
   + apply Nat.lt_succ_r. apply (@A_lt_inv k). lia.
Qed.

Lemma invA_low_nonflat k q :
 2 < q -> invA_low k q <> invA_low k (q-1) <-> q = S (A k (invA_low k q)).
Proof.
 intros.
 rewrite invA_low_flat by trivial. generalize (invA_low_spec k q). lia.
Qed.

Lemma prevkword_eqn k q :
  k+2 <= q -> prevkword k q ++ prevkprefix k q = kprefix k q.
Proof.
 intros H. unfold prevkprefix, prevkword. rewrite kword_len.
 assert (H' : 2 <= q) by lia.
 destruct (invA_low_spec k q H') as (Lo,Hi).
 eapply PrefixSeq_unique; eauto using kprefix_ok.
 - rewrite app_length, kword_len, !kprefix_length. lia.
 - set (p := invA_low k q) in *.
   apply Prefix_PrefixSeq with (kword k (S p)); try apply kword_prefixseq.
   rewrite kword_alt.
   2:{ apply Nat.succ_le_mono. apply (A_le_inv k).
       rewrite A_base by lia. lia. }
   apply Prefix_app_r.
   apply kprefix_prefix_kword. rewrite A_S in Hi. lia.
Qed.

Lemma prevkword_length k q : 2 <= q -> length (prevkword k q) < q.
Proof.
 unfold prevkword. rewrite kword_len. intros. now apply invA_low_spec.
Qed.

Lemma prevkprefix_length k q : 2 <= q -> 0 < length (prevkprefix k q) < q.
Proof.
 intros H.
 unfold prevkprefix. rewrite kprefix_length. split.
 - generalize (prevkword_length k q H). lia.
 - unfold prevkword. rewrite kword_len.
   generalize (A_nz k (invA_low k q)). lia.
Qed.

Lemma invA_low_low k q :
  2 <= q <= k+3 -> A k (invA_low k q) = q-1.
Proof.
 intros Hq.
 unfold invA_low, invA_up. simpl. destruct (invA_spec k (q-2)) as (Lo,Hi).
 set (p := invA k (q-2)) in *.
 assert (p <= q-2).
 { apply (A_le_inv k). rewrite <- (@A_base k) in Lo; lia. }
 rewrite (@A_base k p) in * by lia.
 rewrite <- (@A_base k (q-2)) in Hi by lia.
 apply A_lt_inv in Hi. lia.
Qed.

Lemma prevkword_length_low k q :
  2 <= q <= k+3 -> length (prevkword k q) = q-1.
Proof.
 intros Hq. unfold prevkword. rewrite kword_len. now apply invA_low_low.
Qed.

Lemma prevkword_low k q :
  2 <= q <= k+3 -> prevkword k q = kword k (q-2).
Proof.
 intros Hq.
 assert (H := prevkword_length_low k q Hq).
 unfold prevkword in *. f_equal. rewrite kword_len in H.
 apply (A_inj k). rewrite H. rewrite A_base; lia.
Qed.

Lemma prevkprefix_length_low k q :
  2 <= q <= k+3 -> length (prevkprefix k q) = 1.
Proof.
 intros Hq.
 unfold prevkprefix. rewrite prevkword_length_low by trivial.
 replace (q-(q-1)) with 1 by lia. apply kprefix_length.
Qed.

Lemma prevkprefix_low k q :
  2 <= q <= k+3 -> prevkprefix k q = [k].
Proof.
 intros Hq.
 assert (H := prevkprefix_length_low k q Hq).
 unfold prevkprefix in *. rewrite kprefix_length in H. rewrite H.
 now rewrite kprefix_alt.
Qed.

Lemma PrefixSeq_kseq_alt' k u :
  PrefixSeq u (kseq k) <->
  exists m : nat, Prefix u (napply (ksubst k) m [k]).
Proof.
 apply PrefixSeq_alt'. apply ksubst_noerase. apply ksubst_prolong.
Qed.

Lemma ksubst_inv k :
  forall u v, apply (ksubst k) u = apply (ksubst k) v -> u = v.
Proof.
 assert (H : forall u v,
             apply (ksubst k) (rev u) = apply (ksubst k) (rev v) -> u = v).
 { induction u as [|a u]; destruct v as [|b v]; simpl; auto.
   - rewrite apply_app. simpl. rewrite app_nil_r.
     intros E. symmetry in E. apply length_zero_iff_nil in E.
     rewrite app_length in E. unfold ksubst in E at 2.
     destruct (Nat.eqb b k); simpl in E; lia.
   - rewrite apply_app. simpl. rewrite app_nil_r.
     intros E. apply length_zero_iff_nil in E.
     rewrite app_length in E. unfold ksubst in E at 2.
     destruct (Nat.eqb a k); simpl in E; lia.
   - rewrite !apply_app.
     unfold ksubst at 2 4. simpl.
     do 2 case Nat.eqb_spec; intros; subst; rewrite !app_nil_r in *.
     + apply app_inv' in H; trivial. f_equal. apply IHu, H.
     + apply (f_equal (@rev nat)) in H. now rewrite !rev_app_distr in H.
     + apply (f_equal (@rev nat)) in H. now rewrite !rev_app_distr in H.
     + apply app_inv' in H; trivial.
       destruct H as (H,[= ->]). f_equal. apply IHu, H. }
 intros u v. rewrite <- (rev_involutive u), <- (rev_involutive v).
 intros E. apply H in E. now f_equal.
Qed.

(** If the substitution of u is a kprefix which isn't followed by
    a 0 letter, then u is also a kprefix.
    The condition about the following 0 letter is mandatory:
    otherwise a first counterexample is u=[k-1]. *)

Lemma ksubst_prefix_inv k u :
  PrefixSeq (apply (ksubst k) u) (kseq k) ->
  is_k0 k (length (apply (ksubst k) u)) = false ->
  PrefixSeq u (kseq k).
Proof.
 set (v := apply _ _).
 destruct (Nat.eq_dec k 0) as [->|K].
 - unfold is_k0.
   replace (kseq 0 (length v)) with 0.
   2:{ generalize (kseq_letters 0 (length v)); lia. }
   easy.
 - intros P N.
   assert (E := kseq_take_inv k (length v) K).
   rewrite N in E. rewrite Nat.add_0_r in E. red in P. rewrite <- P in E.
   unfold v in E at 1. apply ksubst_inv in E. rewrite E.
   red. now rewrite take_length.
Qed.

Lemma ksubst_prefix_inv' k u :
  k<>0 ->
  PrefixSeq u (kseq k) ->
  exists v w,
    PrefixSeq v (kseq k) /\ (w=[]\/w=[k]) /\ u = apply (ksubst k) v ++ w.
Proof.
 intros K P.
 assert (E := kseq_take_inv k (length u) K).
 remember (length u) as n eqn:U.
 unfold is_k0 in *.
 destruct (Nat.eqb_spec (kseq k n) 0) as [N|N].
 - rewrite Nat.add_1_r, take_S in E.
   rewrite N in E.
   destruct n.
   + exfalso. now rewrite kseq_k_0 in N.
   + rewrite take_S, <- app_assoc in E.
     assert (f k (S n) <> 0).
     { intros H. rewrite H in E. simpl in E.
       apply (f_equal (@rev _)) in E. now rewrite rev_app_distr in E. }
     replace (f k (S n)) with (S (f k (S n) - 1)) in E by lia.
     rewrite take_S, apply_app in E. simpl in E. rewrite app_nil_r in E.
     set (m := f k (S n) - 1) in *.
     exists (take m (kseq k)), [k]; repeat split.
     * red. f_equal. now rewrite take_length.
     * now right.
     * apply (f_equal (@rev _)) in E. rewrite !rev_app_distr in E.
       simpl in E.
       unfold ksubst in E at 1.
       destruct (Nat.eqb_spec (kseq k m) k) as [M|M]; try easy.
       simpl in E. injection E as N' E. apply rev_inj in E.
       rewrite <- E, P, <- U, take_S. f_equal. now f_equal.
 - rewrite Nat.add_0_r in E.
   exists (take (f k n) (kseq k)), []; repeat split.
   + red. f_equal. now rewrite take_length.
   + now left.
   + rewrite <- E, app_nil_r. rewrite P. now f_equal.
Qed.


(** Now, a list of factors that was meant to be without duplicates,
    for computing the complexixity.
    But actually it only removes some of the duplicates but not all :-( *)

Definition hacksuffixes k p q :=
  let suff := allsuffixes k p in
  if q <=? S k then suff
  else
    (* the largest kword which is a strict prefix of [kprefix k q] *)
    let w := prevkword k q in
    (* extend w into a suffix of size (p + length w) *)
    let ext := filter (fun u => listnat_eqb (skipn p u) w)
                    (allsuffixes k (p + length w)) in
    (* the suffix we hence need to drop *)
    let u := firstn p (hd [] ext) in
    (* let's remove it *)
    filter (fun v => negb (listnat_eqb u v)) suff.

Definition kfactorsBUG k p :=
 if p =? 0 then [[]]
 else
   allsubs p (kword k k) ++
   flat_map
    (fun p1 => map_appr (hacksuffixes k p1 (p-p1)) (kprefix k (p-p1)))
    (seq 1 (p-1)).

Lemma hacksuffixes_incl k p q u :
 In u (hacksuffixes k p q) -> In u (allsuffixes k p).
Proof.
 unfold hacksuffixes. case Nat.leb; trivial. now rewrite filter_In.
Qed.

Lemma hacksuffixes_incl_inv k p q u :
 In u (allsuffixes k p) ->
 In u (hacksuffixes k p q) \/
 k+2<=q /\
  exists v,
  firstn p v = u /\
  skipn p v = prevkword k q /\
  In v (allsuffixes k (p + length (prevkword k q))).
Proof.
 unfold hacksuffixes. case Nat.leb_spec; [now left|].
 intros Lt Hu. rewrite filter_In.
 set (w := prevkword k q).
 set (n := length w).
 remember (filter _ _) as l eqn:L.
 assert (L' : forall v, In v l <-> In v (allsuffixes k (p+n)) /\ skipn p v = w).
 { intro. rewrite L, filter_In. case listnat_eqb_spec; intuition. }
 clear L. rename L' into L.
 case listnat_eqb_spec; intros E; [right; split; try lia | now left].
 destruct (allsuffixes_extend k n (p+n) w) as (v & SU & IN); try lia.
 { rewrite allsuffixes_spec. split; trivial.
   unfold prevkword in w. exists (invA_low k q). now exists []. }
 assert (V : In v l).
 { rewrite L. split; trivial.
   rewrite Suffix_equiv in SU. rewrite SU. unfold lastn.
   rewrite allsuffixes_spec in IN. replace (_-_) with p by lia. easy. }
 (* actually v is the only element in l, but we don't prove that here. *)
 destruct l as [|v' l]; try easy. clear v SU IN V. simpl in E.
 exists v'. split. easy. apply and_comm. rewrite <- L. simpl. now left.
Qed.

(** At least kfactorsBUG exactly enumerates the factors
    (just as kfactors0 et kfactors0opt). *)

Lemma kfactorsBUG_in k p u :
  In u (kfactorsBUG k p) <-> SubSeqLen p u (kseq k).
Proof.
 unfold kfactorsBUG.
 case Nat.eqb_spec.
 - intros ->. simpl. split.
   + intros [<-|[ ]]. split; auto. now exists 0.
   + unfold SubSeqLen. rewrite length_zero_iff_nil. now left.
 - intros Hp.
   rewrite <- kfactors0_in. unfold kfactors0.
   rewrite !in_app_iff, !in_flat_map. apply or_iff_compat_l. split.
   + intros (p1 & P1 & U). exists p1. split; trivial.
     rewrite map_appr_in in *.
     destruct U as (v & <- & V). exists v. split; trivial.
     now apply hacksuffixes_incl in V.
   + intros (p1 & P1 & U).
     rewrite in_seq in P1. setoid_rewrite in_seq.
     remember (p-p1) as p2 eqn:P2.
     revert p1 P1 P2 U.
     induction p2 as [p2 IH] using lt_wf_ind.
     intros p1 P1 P2 U.
     rewrite map_appr_in in U. destruct U as (v & <- & V).
     destruct (hacksuffixes_incl_inv k p1 p2 v V)
       as [V'|(LE & e & E & E' & V')].
     * exists p1. split; trivial. rewrite <- P2, map_appr_in. now exists v.
     * set (w := prevkword k p2) in *.
       set (n := length w) in *.
       assert (Ee : e = v++w).
       { rewrite <- (firstn_skipn p1 e). now rewrite E, E'. }
       assert (N : 1 <= n < p2).
       { split.
         - unfold n, w, prevkword. rewrite kword_len. apply A_nz.
         - apply prevkword_length; lia. }
       assert (P2' : p2-n < p2) by lia.
       apply (IH (p2-n) P2' (p1+n)); clear IH; try lia.
       assert (W := prevkword_eqn k p2 LE). fold w in W. rewrite <- W.
       rewrite app_assoc, <- Ee, map_appr_in. now exists e.
Qed.

Definition find_dups (l : list word) :=
  filter (fun u => negb (count_occ (list_eq_dec Nat.eq_dec) l u =? 1)) l.

(** Finally, NoDup (kfactorsBUG k p) is actually False.
    Some first counterexamples *)

Compute find_dups (kfactorsBUG 1 7).
Compute find_dups (kfactorsBUG 2 11).

(** Post-mortem analysis : I thought we add exactly one duplicate
   for each call to allsuffixes in kfactors0 (when p2>=k+2).
   Hence the hacksuffixes function designed to remove this duplicate.
   But actually we may have sometimes less, sometimes more duplicates.
   For instance with k=2 p=11 the factors are:

2202012012 2
2012201220 2
0201220201 2

202012012 20
012201220 20
201220201 20

02012012 201
12201220 201
01220201 201

2012012 2012
2201220 2012 : BUG No duplicate, 22021220 <> 0201220, but 1st occ, see below!
1220201 2012

012012 20122
201220 20122
220201 20122 : duplicate ok, see above 2202012012 2

12012 201220
01220 201220
20201 201220 : duplicate ok, see above 202012012 20

2012 2012202 : duplicate ok, see above 2012201220 2
1220 2012202
0201 2012202

012 20122020 : duplicate ok, see above 012201220 20
220 20122020
201 20122020

12 201220201 : duplicate ok, see above 12201220 201
20 201220201
01 201220201

2 2012202012 : unexpected duplicate, see above 2201220 2012
0 2012202012 : duplicate ok, see above 0201220201 2
1 2012202012

Conclusion: Finally, no obvious way to count these duplicates
(even if there's a linear number of them).
It seems easier to obtain complexity by proving there's only one Left-Special
of each length.

*)


Definition Complexity f p n :=
  exists l, NoDup l /\ length l = n /\ forall u, In u l <-> SubSeqLen p u f.

(*
Lemma kseq_complexity k : forall p, Complexity (kseq k) p (k*p+1).
Proof.
 intros p. exists (kfactors k p). split; [|split].
 - apply kfactors_nodup.
 - apply kfactors_length.
 - apply kfactors_in.
Qed.
*)

(* Idee: dilute the (nbocc 0) en dessous des concat *)

(* TODO: est-ce que ça donne -2..2 pour k=2 sans axiomes réels ?
 *)

(* Idee : left_special préservé par subst ? *)
