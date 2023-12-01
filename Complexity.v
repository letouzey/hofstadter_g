Require Import MoreFun MoreList DeltaList FunG GenFib GenG Words Words2.
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


(** Complexity of infinite words : for each value of p,
    number of sub-words of length p *)

Definition subseq q n (f:sequence) := map f (seq q n).

Definition SubSeq u (f:sequence) := exists q, u = subseq q (length u) f.

Definition SubpSeq p u (f:sequence) := length u = p /\ SubSeq u f.

Definition AllSubp p l f := NoDup l /\ (forall w, In w l <-> SubpSeq p w f).

Definition Complexity f p n := exists l, AllSubp p l f /\ length l = n.

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
   apply PrefixSeq_incl with (kseq k); trivial.
   + rewrite kword_len; apply invA_up_spec.
   + apply kword_prefixseq.
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
     { apply PrefixSeq_incl with (kseq k); trivial.
       - rewrite kword_len; apply invA_up_spec.
       - apply kword_prefixseq. }
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

Definition map_app_r l (v:word) := map (fun u => u++v) l.

Definition kseq_prefix k n :=
  let p := invA_up k n in
  firstn n (kword k p).

Lemma kseq_prefix_length k n : length (kseq_prefix k n) = n.
Proof.
 unfold kseq_prefix. rewrite firstn_length_le; auto.
 rewrite kword_len. apply invA_up_spec.
Qed.

Lemma kseq_prefix_ok k n : PrefixSeq (kseq_prefix k n) (kseq k).
Proof.
 unfold kseq_prefix. eapply Prefix_PrefixSeq; eauto.
 apply firstn_Prefix. apply kword_prefixseq.
Qed.

(* A first listing of factors, which is complete but may contain
   a few duplicates *)

Definition ksubsdups k p :=
 allsubs p (kword k k) ++
 concat (map (fun p1 => map_app_r (allsuffixes k p1) (kseq_prefix k (p-p1)))
             (seq 1 (p-1))).

Lemma ksubsdups_ok k p u :
  In u (ksubsdups k p) <-> length u = p /\ SubSeq u (kseq k).
Proof.
 unfold ksubsdups. rewrite in_app_iff, allsubs_ok.
 rewrite SubSeq_kseq_carac, in_concat. setoid_rewrite in_map_iff.
 split.
 - intros [(L,S)|(ll & (p1 & <- & IN) & IN')].
   + split; auto.
   + rewrite in_seq in IN. unfold map_app_r in IN'.
     rewrite in_map_iff in IN'. destruct IN' as (u1 & <- & IN').
     rewrite allsuffixes_spec in IN'. destruct IN' as (IN', SU).
     destruct SU as (m & SU).
     set (u2 := kseq_prefix k (p-p1)).
     split.
     * rewrite app_length, IN'. unfold u2.
       rewrite kseq_prefix_length. lia.
     * right. exists u1, u2; repeat split.
       { rewrite <- length_zero_iff_nil, IN'. lia. }
       { rewrite <- length_zero_iff_nil. unfold u2.
         rewrite kseq_prefix_length. lia. }
       { now exists m. }
       { unfold u2. apply kseq_prefix_ok. }
 - intros (L, [S|(u1 & u2 & Hu1 & Hu2 & -> & SU & PR)]).
   + left; auto.
   + right. setoid_rewrite in_seq.
     rewrite app_length in L.
     set (p1 := length u1) in *.
     assert (E : u2 = kseq_prefix k (p-p1)).
     { apply Prefix_antisym;
       apply PrefixSeq_incl with (kseq k); auto using kseq_prefix_ok;
       (rewrite kseq_prefix_length; lia). }
     exists (map_app_r (allsuffixes k p1) u2).
     split.
     * exists p1. split. now rewrite E.
       rewrite <- length_zero_iff_nil in Hu1, Hu2. lia.
     * unfold map_app_r. set (f := fun u => _).
       change (u1 ++ u2) with (f u1). apply in_map. clear f.
       rewrite allsuffixes_spec; auto.
Qed.

(* Avec ça on peut déjà dire que la complexité est linéaire
   Mais ksubsdups k n contient n-(k+2) doublons en trop *)

(* TODO: ksubsdups optimisé pour éviter tout calcul répétitif ?
   application à la quasi-additivité ?
   est-ce que ça donne -2..2 pour k=2 sans axiomes réels ?
 *)

(* Idee : left_special préservé par subst ? *)


(*
Lemma Complexity_kseq k : forall p, Complexity (kseq k) p (k*p+1).
Proof.
Admitted. (* TODO *)
*)

(* TODO : explicitely enumerate these (k*p+1) sub-words of length p
   and deduce additivity bounds for f in a nicer way than in GenAdd ! *)
