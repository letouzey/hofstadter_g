Require Import MoreTac MoreFun MoreList DeltaList.
Require Import GenFib GenG Words WordSuffix.
Import ListNotations.

(** * Factors of infinite word (kseq k) *)

(** ** General definitions *)

Definition subseq q n (f:sequence) := map f (seq q n).

Definition SubSeq u (f:sequence) := exists q, u = subseq q (length u) f.

Definition SubSeqLen p u (f:sequence) := length u = p /\ SubSeq u f.

(** The complexity of an infinite word is the function giving
    the number of factors of a given length. *)

Definition Complexity f p n :=
  exists l, NoDup l /\ length l = n /\ forall u, In u l <-> SubSeqLen p u f.

Lemma SubSeq_alt0 u f : SubSeq u f <-> exists v, Suffix u v /\ PrefixSeq v f.
Proof.
 split.
 - intros (q, E). remember (length u) as n.
   exists (take (q+n) f).
   split.
   + exists (take q f). subst u. unfold subseq, take.
     rewrite <- map_app. f_equal. symmetry. apply seq_app.
   + unfold PrefixSeq. now rewrite take_length.
 - intros (v & (u' & <-) & PR). exists (length u').
   red in PR. unfold take in PR. rewrite app_length in PR.
   rewrite seq_app, map_app in PR.
   apply app_inv in PR. apply PR. now rewrite map_length, seq_length.
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

Lemma Sub_SubSeq f u v : Sub u v -> SubSeq v f -> SubSeq u f.
Proof.
 rewrite !SubSeq_alt. intros (w1 & w2 & <-) (r & (w0 & w3 & E) & PR).
 exists r; split; trivial. exists (w0++w1), (w2++w3).
 now rewrite <-E, <- !app_assoc.
Qed.

(** ** application to [kseq] *)

Lemma kword_prefixseq k n : PrefixSeq (kword k n) (kseq k).
Proof.
 apply PrefixSeq_napply. apply ksubst_noerase. apply ksubst_prolong.
 reflexivity.
Qed.

Lemma kword_le_prefix k n m :
  n <= m -> Prefix (kword k n) (kword k m).
Proof.
 induction 1. apply Prefix_id.
 eapply Prefix_trans; eauto.
 destruct (Nat.eq_dec k 0) as [->|K].
 { rewrite !kword_01 by lia. simpl. rewrite Nat.add_0_r.
   rewrite repeat_app. now eexists. }
 destruct (Nat.le_gt_cases m (k-1)).
 - rewrite !kword_low by lia.
   exists [m]. simpl. now rewrite <- seq_S.
 - rewrite (kword_eqn k (S m)) by lia. fixpred. now eexists.
Qed.

Lemma kword_Suffix_Prefix_Sub k u1 u2 n m :
  Suffix u1 (kword k n) -> Prefix u2 (kword k m) ->
  exists p, Sub (u1++u2) (kword k p).
Proof.
 revert u1 u2 n m.
 withoutloss k (k<>0).
 { intros K u1 u2 n m SU PR.
   destruct (Nat.le_gt_cases m n).
   - exists (S (n + k)). rewrite kword_eqn by lia.
     assert (HSn : Prefix u2 (kword k (S n))).
     { eapply Prefix_trans; eauto. apply kword_le_prefix. lia. }
     apply kword_suffix_cycle in SU.
     destruct SU as (u1' & E1).
     destruct HSn as (u2' & E2).
     exists u1', u2'. rewrite <- app_assoc, E2, app_assoc, E1.
     f_equal; f_equal; lia.
   - set (m' := n + S ((m-n)/k)*k).
     assert (Hm' : m < m').
     { assert (Hq : k <> 0) by lia.
       assert (E := Nat.div_mod (m-n) (k) Hq).
       generalize (Nat.mod_upper_bound (m-n) (k)). lia. }
     apply kword_suffix_pcycle with (p := S ((m-n)/k)) in SU.
     fold m' in SU.
     assert (HSm' : Prefix u2 (kword k (S m'))).
     { eapply Prefix_trans; eauto. apply kword_le_prefix. lia. }
     exists (S (m' + k)).
     rewrite kword_eqn by lia.
     apply kword_suffix_cycle in SU.
     destruct SU as (u1' & E1).
     destruct HSm' as (u2' & E2).
     exists u1', u2'. rewrite <- app_assoc, E2, app_assoc, E1.
     f_equal; f_equal; lia. }
 { destruct (Nat.eq_dec k 0) as [->|K]; [ | now apply WL].
   intros u1 u2 n m.
   specialize (WL 1 lia u1 u2 n m).
   revert WL. setoid_rewrite kword_01; easy || lia. }
Qed.

Lemma SubSeq_kseq_alt k u :
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
 exists n0, Sub u (kword k n0) /\ forall p, p<n0 -> ~Sub u (kword k p).
Proof.
 induction n; intros SU.
 - exists 0. split; trivial. inversion 1.
 - destruct (subb_spec u (kword k n)) as [SU'|NS].
   + apply (IHn SU').
   + exists (S n). split; trivial. intros p Hp SU'. apply NS.
     eapply Sub_Prefix_Sub; eauto. apply kword_le_prefix; lia.
Qed.

Lemma SubSeq_kseq_carac k u : k<>0 ->
  SubSeq u (kseq k) <->
  Sub u (kword k (k-1)) \/
  exists u1 u2, u1<>[] /\ u2<>[] /\ u=u1++u2 /\
     SuffixWords u1 (kword k) /\ PrefixSeq u2 (kseq k).
Proof.
 split.
 - rewrite SubSeq_kseq_alt. intros (n & SU).
   apply Sub_kword_minimal in SU. clear n.
   destruct SU as (n & SU & NS).
   destruct (Nat.le_gt_cases n (k-1)).
   + left. eapply Sub_Prefix_Sub; eauto. apply kword_le_prefix; lia.
   + right. destruct n as [|n]; try lia.
     rewrite kword_eqn in SU by lia. fixpred.
     apply Sub_app_inv in SU.
     destruct SU as [SU|[SU|(u1 & u2 & U1 & U2 & E & SU & PR)]].
     * exfalso. apply (NS n); auto.
     * exfalso. apply (NS (S n-k)); auto; lia.
     * exists u1, u2; repeat split; trivial.
       { now exists n. }
       { eapply Prefix_PrefixSeq; eauto. apply kword_prefixseq. }
 - rewrite SubSeq_alt.
   intros [SU|(u1 & u2 & Hu1 & Hu2 & E & SU & PR)].
   + exists (kword k (k-1)); split; trivial.
     apply PrefixSeq_napply; try easy.
     apply ksubst_noerase. apply ksubst_prolong.
   + subst. destruct SU as (n & SU).
     set (m := invA_up k (length u2)).
     assert (Hm : Prefix u2 (kword k m)).
     { eapply PrefixSeq_incl; eauto using kword_prefixseq.
       rewrite kword_len; apply invA_up_spec. }
     destruct (kword_Suffix_Prefix_Sub k u1 u2 n m) as (p & Hp); trivial.
     exists (kword k p); split; auto using kword_prefixseq.
Qed.

Lemma allsubs_kword_nodup k p :
  k<>0 -> p<>0 -> NoDup (allsubs p (kword k (k-1))).
Proof.
 intros K Hp.
 unfold allsubs.
 rewrite kword_low by lia. simpl length. rewrite seq_length. fixpred.
 set (w := k-1 :: seq 0 (k-1)).
 set (f := fun i => _).
 rewrite NoDup_nth with (d:=f 0).
 rewrite take_length. intros i j Hi Hj.
 rewrite !take_nth; auto. unfold f; clear f.
 assert (F0 : hd 0 (sub w 0 p) = k-1).
 { unfold hd, sub. simpl. destruct p; simpl; lia. }
 assert (F : forall x, 0<S x<S k-p -> hd 0 (sub w (S x) p) = x).
 { intros x Hx. unfold hd, sub. simpl. rewrite skipn_seq.
   rewrite firstn_seq by lia. destruct p; simpl; lia. }
 intros E.
 assert (E' : hd 0 (sub w i p) = hd 0 (sub w j p)). { now rewrite E. }
 clear E.
 destruct i, j; trivial.
 - rewrite F0, (F j) in E'; lia.
 - rewrite (F i), F0 in E'; lia.
 - rewrite (F i), (F j) in E'; lia.
Qed.

(** A first listing of factors, which is complete but may contain
    a few duplicates. Not meant to be efficient. *)

Definition kfactors0 k p :=
 allsubs p (kword k (k-1)) ++
 flat_map (fun p1 => map_appr (allsuffixes k p1) (kprefix k (p-p1)))
  (seq 1 (p-1)).

Lemma kfactors0_in k p u :
  k<>0 -> In u (kfactors0 k p) <-> SubSeqLen p u (kseq k).
Proof.
 intros K. unfold kfactors0, SubSeqLen.
 rewrite in_app_iff, allsubs_ok, SubSeq_kseq_carac, in_flat_map; trivial.
 split.
 - intros [(L,S)|(p1 & IN & IN')].
   + split; auto.
   + rewrite in_seq in IN.
     rewrite map_appr_in in IN'. destruct IN' as (u1 & <- & IN').
     rewrite allsuffixes_spec in IN'; trivial. destruct IN' as (IN', SU).
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
     * apply map_appr_in. exists u1.
       rewrite allsuffixes_spec; trivial; split; auto.
       rewrite PR. f_equal. f_equal. lia.
Qed.

(** Compared with the expected (k-1)*p+1 complexity, we have some duplicates
    when p>k+1. More precisely k*(p-1)-(k-1)*p-1 = p-k-1 duplicates.
    This is still enough to say that the complexity is linear. *)

Lemma kfactors0_length k p :
 p<>0 -> length (kfactors0 k p) = if p <=? k+1 then (k-1)*p+1 else k*(p-1).
Proof.
 intros Hp.
 unfold kfactors0.
 rewrite app_length, allsubs_length, kword_len, A_base by lia.
 rewrite MoreList.flat_map_length with (k:=k), seq_length.
 2:{ intros. unfold map_appr. rewrite map_length. apply allsuffixes_length. }
 case Nat.leb_spec; nia.
Qed.


(** Similar to kfactors0, but much more efficient.
    Still the same amount of duplicates. *)

Definition kfactors0opt k p :=
  let p' := pred p in
  let r := invA_up k p' in
  let pref := firstn p' (kword k r) in
  let suffs := allsuffixesAt k p' r in
  allsubs p (kword k (k-1)) ++ flat_map (allsubs p) (map_appr suffs pref).

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
  k<>0 -> In u (kfactors0opt k p) <-> SubSeqLen p u (kseq k).
Proof.
 intros K. destruct (Nat.eq_dec p 0) as [->|Hp].
 - rewrite kfactors0opt_0_r. split.
   + intros ->. split; auto. now exists 0.
   + unfold SubSeqLen. now rewrite length_zero_iff_nil.
 - rewrite <- kfactors0_in; trivial.
   unfold kfactors0, kfactors0opt.
   set (p' := pred p).
   fold (allsuffixes k p').
   fold (kprefix k p').
   rewrite !in_app_iff, !in_flat_map. apply or_iff_compat_l. split.
   + intros (w0 & Hw0 & Hu).
     rewrite map_appr_in in Hw0.
     destruct Hw0 as (w & <- & Hw).
     apply allsuffixes_spec in Hw; trivial. destruct Hw as (Hw,SF).
     rewrite allsubs_ok in Hu. destruct Hu as (Hu,SB).
     rewrite <- kprefix_alt in SB.
     apply Sub_app_inv in SB.
     destruct SB as [SB|[SB|(u1 & u2 & U1 & U2 & -> & H1 & H2)]].
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
           rewrite PR. f_equal. lia.
         - rewrite allsuffixes_spec; trivial.
           split; auto. unfold SuffixWords in *.
           destruct SF as (n & SF). exists n.
           apply Suffix_trans with w; auto. }
   + intros (p1 & Hp1 & Hu). apply in_seq in Hp1. apply map_appr_in in Hu.
     destruct Hu as (u1 & <- & Hu1).
     destruct (allsuffixes_extend k p1 p' u1) as (u1' & Hu1');
      trivial; try lia.
     exists (u1' ++ kprefix k p'); split; rewrite <- ?kprefix_alt.
     * apply map_appr_in. now eexists.
     * apply allsubs_ok; split.
       { rewrite app_length, kprefix_length.
         apply allsuffixes_spec in Hu1; trivial. lia. }
       { destruct Hu1' as ((v & <-),_).
         assert (PR : Prefix (kprefix k (p-p1)) (kprefix k p')).
         { eapply PrefixSeq_incl; eauto using kprefix_ok.
           rewrite !kprefix_length. lia. }
         destruct PR as (w & <-).
         exists v, w. now rewrite !app_assoc. }
Qed.

Lemma kfactors0opt_length k p :
 k<>0 -> p<>0 ->
 length (kfactors0opt k p) = if p <=? k+1 then (k-1)*p+1 else k*(p-1).
Proof.
 intros K Hp.
 unfold kfactors0opt.
 set (p' := pred p).
 set (r := invA_up k p').
 set (pref := firstn p' (kword k r)).
 set (suffs := allsuffixesAt k p' r).
 rewrite app_length, allsubs_length, kword_len, A_base by lia.
 rewrite MoreList.flat_map_length with (k:=p').
 2:{ intros a. rewrite map_appr_in. intros (w & <- & IN).
     rewrite allsubs_length, app_length.
     apply allsuffixesAt_spec in IN; trivial. 2:apply invA_up_spec.
     destruct IN as (->,_).
     unfold pref. rewrite firstn_length_le. lia.
     rewrite kword_len. apply invA_up_spec. }
 unfold map_appr. rewrite map_length. unfold suffs.
 rewrite allsuffixesAt_length.
 case Nat.leb_spec; nia.
Qed.

Lemma kfactors0opt_nbocc0_le k p a b :
  k<>0 ->
  extrems (map (nbocc 0) (kfactors0opt k p)) = (a,b) -> a <= p /\ b <= p.
Proof.
 intros K. set (l := map (nbocc 0) (kfactors0opt k p)).
 destruct (list_eq_dec Nat.eq_dec l []) as [->|NE].
 - inversion 1. lia.
 - intros E. generalize (extrems_in1 l NE) (extrems_in2 l NE).
   rewrite E. simpl. unfold l.
   rewrite !in_map_iff. intros (u & <- & Hu) (v & <- & Hv).
   rewrite kfactors0opt_in in Hu, Hv; trivial.
   split.
   + destruct Hu as (<-,_); apply nbocc_le_length.
   + destruct Hv as (<-,_); apply nbocc_le_length.
Qed.

(** Application to quasi-additivity of f, in a faster way than in GenAdd *)

Lemma f_additivity_via_factors k p a b :
 1<k ->
 extrems (map (nbocc 0) (kfactors0opt k p)) = (a,b) ->
 forall n, f k n + (p-b) <= f k (n+p) <= f k n + (p-a).
Proof.
 intros K E n.
 assert (Hn := f_count_0 k n K).
 assert (Hnp := f_count_0 k (n+p) K).
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
   rewrite kfactors0opt_in; try lia. split.
   - unfold v. rewrite lastn_length_le; auto.
     unfold w. rewrite take_length; lia.
   - rewrite SubSeq_alt0. exists w. split. now exists u.
     unfold w. red. now rewrite take_length. }
 generalize (kfactors0opt_nbocc0_le k p a b lia E). lia.
Qed.

Lemma f_additivity_via_factors' k p a b :
 1<k -> a <= p -> b <= p ->
 extrems (map (nbocc 0) (kfactors0opt k p)) = (p-b,p-a) ->
 forall n, f k n + a <= f k (n+p) <= f k n + b.
Proof.
 intros K Ha Hb E n.
 generalize (f_additivity_via_factors k p _ _ K E n).
 replace (p-(p-a)) with a; replace (p-(p-b)) with b; lia.
Qed.

Ltac solve_additivity :=
 apply f_additivity_via_factors';
 [ apply Nat.ltb_lt; now vm_compute |
   apply Nat.leb_le; now vm_compute |
   apply Nat.leb_le; now vm_compute |
   match goal with |- _ = ?p =>
     vm_cast_no_check (@eq_refl _ p); reflexivity
   end ].

Lemma f6_add_424 n : f 6 n + 326 <= f 6 (n+424) <= f 6 n + 333.
Proof.
 solve_additivity.
Qed.

Lemma f7_add_424 n : f 7 n + 333 <= f 7 (n+424) <= f 7 n + 342.
Proof.
 solve_additivity.
Qed.

Lemma f6_below_f7 n : f 6 n <= f 7 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 424) as [LT|LE].
- clear IH.
  assert
    (E : forallb (fun n => Nat.leb (fopt 6 n) (fopt 7 n)) (seq 0 424) = true)
    by now vm_compute.
  rewrite <- !fopt_spec, <- Nat.leb_le.
  rewrite forallb_forall in E. apply E. apply in_seq. lia.
- replace n with ((n-424)+424) by lia.
  etransitivity; [ apply f6_add_424 | ].
  etransitivity; [ | apply f7_add_424 ].
  specialize (IH (n-424)). lia.
Qed.

(*
Lemma f7_add_843 n : f 7 n + 666 <= f 7 (n+843) <= f 7 n + 677.
Proof.
 solve_additivity.
Qed.

Lemma f8_add_843 n : f 8 n + 677 <= f 8 (n+843) <= f 8 n + 692.
Proof.
 solve_additivity.
Qed.

Lemma f7_below_f8 n : f 7 n <= f 8 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 843) as [LT|LE].
- clear IH.
  assert
    (E : forallb (fun n => Nat.leb (fopt 7 n) (fopt 8 n)) (seq 0 843) = true)
    by now vm_compute.
  rewrite <- !fopt_spec, <- Nat.leb_le.
  rewrite forallb_forall in E. apply E. apply in_seq. lia.
- replace n with ((n-843)+843) by lia.
  etransitivity; [ apply f7_add_843 | ].
  etransitivity; [ | apply f8_add_843 ].
  specialize (IH (n-843)). lia.
Qed.

Lemma f8_add_1617 n : f 8 n + 1304 <= f 8 (n+1617) <= f 8 n + 1322.
Proof.
 solve_additivity.
Qed.

Lemma f9_add_1617 n : f 9 n + 1322 <= f 9 (n+1617) <= f 9 n + 1345.
Proof.
 solve_additivity.
Time Qed. (* 50s *)
*)

(** kfactors : All factors of some length, without duplicates.
    Obtained via cleanup of kfactors0opt from its duplicates.
    Could be more efficient someday. *)

Definition kfactors k p :=
 nodup (list_eq_dec Nat.eq_dec) (kfactors0opt k p).

Lemma kfactors_in k p u : k<>0 ->
  In u (kfactors k p) <-> SubSeqLen p u (kseq k).
Proof.
 unfold kfactors. rewrite nodup_In. apply kfactors0opt_in.
Qed.

Lemma kfactors_nodup k p : NoDup (kfactors k p).
Proof.
 apply NoDup_nodup.
Qed.

Lemma kfactors_0_r k : kfactors k 0 = [[]].
Proof.
 assert (D := kfactors_nodup k 0).
 assert (I : forall u, In u (kfactors k 0) <-> u=[]).
 { intros u. unfold kfactors. rewrite nodup_In. apply kfactors0opt_0_r. }
 destruct (kfactors k 0) as [|u [|v l]].
 - now destruct (I []) as (_,[ ]).
 - f_equal. rewrite <- I. now left.
 - replace u with (@nil nat) in D by (symmetry; rewrite <- I; intuith).
   replace v with (@nil nat) in D by (symmetry; rewrite <- I; intuith).
   inversion_clear D. simpl in *. intuition.
Qed.

Lemma kfactors_1_l p : kfactors 1 p = [repeat 0 p].
Proof.
 assert (E : forall b a, subseq a b (kseq 1) = repeat 0 b).
 { unfold subseq. induction b; simpl; auto. intros a. f_equal; auto.
   now rewrite kseq_01. }
 assert (IN : In (repeat 0 p) (kfactors 1 p)).
 { rewrite kfactors_in by easy. split. now rewrite repeat_length.
   exists 0. rewrite repeat_length. auto. }
 apply Permutation_length_1_inv. symmetry. apply NoDup_Permutation_bis.
 - apply kfactors_nodup.
 - simpl. destruct (kfactors 1 p). easy. simpl. lia.
 - intros x. rewrite kfactors_in by easy. intros (L & k & ->).
   simpl. left. now rewrite E, L.
Qed.

Lemma nodup_length_le {A}(dec : forall (a b:A),{a=b}+{a<>b}) l :
  length (nodup dec l) <= length l.
Proof.
 induction l; simpl; auto. destruct in_dec; simpl; lia.
Qed.

Lemma kfactors_linear_length k p :
  k<>0 -> length (kfactors k p) <= if p <=? k+1 then (k-1)*p+1 else k*(p-1).
Proof.
 intros K. destruct (Nat.eq_dec p 0) as [->|Hp].
 - rewrite kfactors_0_r. simpl; lia.
 - rewrite <- kfactors0opt_length; trivial. apply nodup_length_le.
Qed.

(** Next, we prove in [Special.v] that [length (kfactors k p) = (k-1)*p+1]
    and hence the complexity of [kseq k] is [fun p => (k-1)*p+1].
    For that, the key property is that the left special factors
    of [kseq] are exactly its prefixes. *)
