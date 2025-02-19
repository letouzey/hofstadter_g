Require Import MoreFun MoreList DeltaList GenFib GenG Words WordSuffix.
Import ListNotations.

(** * Factors of infinite word (qseq q) *)

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

Lemma qword_prefixseq q n : PrefixSeq (qword q n) (qseq q).
Proof.
 apply PrefixSeq_napply. apply qsubst_noerase. apply qsubst_prolong.
 reflexivity.
Qed.

Lemma qword_le_prefix q n m : n <= m -> Prefix (qword q n) (qword q m).
Proof.
 induction 1. apply Prefix_id.
 eapply Prefix_trans; eauto.
 destruct (Nat.le_gt_cases m q).
 - rewrite !qword_low by lia.
   exists [m]. now rewrite seq_S.
 - rewrite qword_eqn by lia. now exists (qword q (m-q)).
Qed.

Lemma qword_Suffix_Prefix_Sub q u1 u2 n m :
  Suffix u1 (qword q n) -> Prefix u2 (qword q m) ->
  exists p, Sub (u1++u2) (qword q p).
Proof.
 intros SU PR.
 destruct (Nat.le_gt_cases m n).
 - exists (S (n + S q)). rewrite qword_eqn by lia.
   assert (HSn : Prefix u2 (qword q (S n))).
   { eapply Prefix_trans; eauto. apply qword_le_prefix. lia. }
   apply qword_suffix_cycle in SU.
   destruct SU as (u1' & E1).
   destruct HSn as (u2' & E2).
   exists u1', u2'. rewrite <- app_assoc, E2, app_assoc, E1.
   f_equal. f_equal. lia.
 - set (m' := n + S ((m-n)/S q)*S q).
   assert (Hm' : m < m').
   { assert (Hq : S q <> 0) by lia.
     assert (E := Nat.div_mod (m-n) (S q) Hq).
     generalize (Nat.mod_upper_bound (m-n) (S q)). lia. }
   apply qword_suffix_pcycle with (p := S ((m-n)/S q)) in SU.
   fold m' in SU.
   assert (HSm' : Prefix u2 (qword q (S m'))).
   { eapply Prefix_trans; eauto. apply qword_le_prefix. lia. }
   exists (S (m' + S q)).
   rewrite qword_eqn by lia.
   apply qword_suffix_cycle in SU.
   destruct SU as (u1' & E1).
   destruct HSm' as (u2' & E2).
   exists u1', u2'. rewrite <- app_assoc, E2, app_assoc, E1.
   f_equal. f_equal. lia.
Qed.

Lemma SubSeq_qseq_alt q u :
 SubSeq u (qseq q) <-> exists n, Sub u (qword q n).
Proof.
 rewrite SubSeq_alt.
 split.
 - intros (v & SU & PR).
   set (n := invA_up q (length v)).
   exists n.
   eapply Sub_Prefix_Sub; eauto.
   eapply PrefixSeq_incl; eauto using qword_prefixseq.
   rewrite qword_len; apply invA_up_spec.
 - intros (n & SU). exists (qword q n); split; trivial.
   apply qword_prefixseq.
Qed.

Lemma Sub_qword_minimal q u n :
 Sub u (qword q n) ->
 exists n0, Sub u (qword q n0) /\ forall p, p<n0 -> ~Sub u (qword q p).
Proof.
 induction n; intros SU.
 - exists 0. split; trivial. inversion 1.
 - destruct (subb_spec u (qword q n)) as [SU'|NS].
   + apply (IHn SU').
   + exists (S n). split; trivial. intros p Hp SU'. apply NS.
     eapply Sub_Prefix_Sub; eauto. apply qword_le_prefix; lia.
Qed.

Lemma SubSeq_qseq_carac q u :
  SubSeq u (qseq q) <->
  Sub u (qword q q) \/
  exists u1 u2, u1<>[] /\ u2<>[] /\ u=u1++u2 /\
     SuffixWords u1 (qword q) /\ PrefixSeq u2 (qseq q).
Proof.
 split.
 - rewrite SubSeq_qseq_alt. intros (n & SU).
   apply Sub_qword_minimal in SU. clear n.
   destruct SU as (n & SU & NS).
   destruct (Nat.le_gt_cases n q).
   + left. eapply Sub_Prefix_Sub; eauto. apply qword_le_prefix; lia.
   + right. destruct n as [|n]; try lia.
     rewrite qword_eqn in SU by lia.
     apply Sub_app_inv in SU.
     destruct SU as [SU|[SU|(u1 & u2 & U1 & U2 & E & SU & PR)]].
     * exfalso. apply (NS n); auto.
     * exfalso. apply (NS (n-q)); auto; lia.
     * exists u1, u2; repeat split; trivial.
       { now exists n. }
       { eapply Prefix_PrefixSeq; eauto. apply qword_prefixseq. }
 - rewrite SubSeq_alt.
   intros [SU|(u1 & u2 & Hu1 & Hu2 & E & SU & PR)].
   + exists (qword q q); split; trivial.
     apply PrefixSeq_napply; try easy.
     apply qsubst_noerase. apply qsubst_prolong.
   + subst. destruct SU as (n & SU).
     set (m := invA_up q (length u2)).
     assert (Hm : Prefix u2 (qword q m)).
     { eapply PrefixSeq_incl; eauto using qword_prefixseq.
       rewrite qword_len; apply invA_up_spec. }
     destruct (qword_Suffix_Prefix_Sub q u1 u2 n m) as (p & Hp); trivial.
     exists (qword q p); split; auto using qword_prefixseq.
Qed.

Lemma allsubs_qword_nodup q p : p<>0 -> NoDup (allsubs p (qword q q)).
Proof.
 intros Hp.
 unfold allsubs.
 rewrite qword_low by lia. simpl length. rewrite seq_length.
 set (f := fun i => _).
 rewrite NoDup_nth with (d:=f 0).
 rewrite take_length. intros i j Hi Hj.
 rewrite !take_nth; auto. unfold f; clear f.
 assert (F0 : hd 0 (sub (q::seq 0 q) 0 p) = q).
 { unfold hd, sub. simpl. destruct p; simpl; lia. }
 assert (F : forall x, 0<S x<S (S q)-p ->
             hd 0 (sub (q::seq 0 q) (S x) p) = x).
 { intros x Hx. unfold hd, sub. simpl. rewrite skipn_seq.
   rewrite firstn_seq by lia. destruct p; simpl; lia. }
 intros E.
 assert (E' : hd 0 (sub (q :: seq 0 q) i p) =
              hd 0 (sub (q :: seq 0 q) j p)).
 { now rewrite E. }
 clear E.
 destruct i, j; trivial.
 - rewrite F0, (F j) in E'; lia.
 - rewrite (F i), F0 in E'; lia.
 - rewrite (F i), (F j) in E'; lia.
Qed.

(** A first listing of factors, which is complete but may contain
    a few duplicates. Not meant to be efficient. *)

Definition qfactors0 q p :=
 allsubs p (qword q q) ++
 flat_map (fun p1 => map_appr (allsuffixes q p1) (qprefix q (p-p1)))
  (seq 1 (p-1)).

Lemma qfactors0_in q p u : In u (qfactors0 q p) <-> SubSeqLen p u (qseq q).
Proof.
 unfold qfactors0, SubSeqLen.
 rewrite in_app_iff, allsubs_ok, SubSeq_qseq_carac, in_flat_map.
 split.
 - intros [(L,S)|(p1 & IN & IN')].
   + split; auto.
   + rewrite in_seq in IN.
     rewrite map_appr_in in IN'. destruct IN' as (u1 & <- & IN').
     rewrite allsuffixes_spec in IN'. destruct IN' as (IN', SU).
     destruct SU as (m & SU).
     set (u2 := qprefix q (p-p1)).
     split.
     * rewrite app_length, IN'. unfold u2.
       rewrite qprefix_length. lia.
     * right. exists u1, u2; repeat split.
       { rewrite <- length_zero_iff_nil, IN'. lia. }
       { rewrite <- length_zero_iff_nil. unfold u2.
         rewrite qprefix_length. lia. }
       { now exists m. }
       { unfold u2. apply qprefix_ok. }
 - intros (L, [S|(u1 & u2 & Hu1 & Hu2 & -> & SU & PR)]).
   + left; auto.
   + right.
     rewrite app_length in L.
     set (p1 := length u1) in *.
     exists p1. split.
     * rewrite in_seq. rewrite <- length_zero_iff_nil in Hu1, Hu2. lia.
     * apply map_appr_in. exists u1. rewrite allsuffixes_spec; split; auto.
       rewrite PR. f_equal. f_equal. lia.
Qed.

(** Compared with the expected q*p+1 complexity, we have some duplicates
    when p>q+2. More precisely (q+1)*(p-1)-(q*p+1) = p-q-2 duplicates.
    This is still enough to say that the complexity is linear. *)

Lemma qfactors0_length q p :
 p<>0 -> length (qfactors0 q p) = if p <=? q+2 then q*p+1 else (q+1)*(p-1).
Proof.
 intros Hp.
 unfold qfactors0.
 rewrite app_length, allsubs_length, qword_len, A_base by lia.
 rewrite MoreList.flat_map_length with (k:=S q), seq_length.
 2:{ intros. unfold map_appr. rewrite map_length. apply allsuffixes_length. }
 case Nat.leb_spec; nia.
Qed.


(** Similar to qfactors0, but much more efficient.
    Still the same amount of duplicates. *)

Definition qfactors0opt q p :=
  let p' := pred p in
  let r := invA_up q p' in
  let pref := firstn p' (qword q r) in
  let suffs := allsuffixesAt q p' r in
  allsubs p (qword q q) ++ flat_map (allsubs p) (map_appr suffs pref).

Lemma qfactors0opt_0_r q u : In u (qfactors0opt q 0) <-> u = [].
Proof.
 unfold qfactors0opt. rewrite in_app_iff.
 split.
 - intros [IN|IN].
   + now rewrite allsubs_ok, length_zero_iff_nil in IN.
   + rewrite in_flat_map in IN. destruct IN as (w & _ & IN).
     apply allsubs_ok in IN.
     now apply length_zero_iff_nil.
 - intros ->. left. apply allsubs_ok. auto using Sub_nil_l.
Qed.

Lemma qfactors0opt_in q p u :
  In u (qfactors0opt q p) <-> SubSeqLen p u (qseq q).
Proof.
 destruct (Nat.eq_dec p 0) as [->|Hp].
 - rewrite qfactors0opt_0_r. split.
   + intros ->. split; auto. now exists 0.
   + unfold SubSeqLen. now rewrite length_zero_iff_nil.
 - rewrite <- qfactors0_in.
   unfold qfactors0, qfactors0opt.
   set (p' := pred p).
   fold (allsuffixes q p').
   fold (qprefix q p').
   rewrite !in_app_iff, !in_flat_map. apply or_iff_compat_l. split.
   + intros (w0 & Hw0 & Hu).
     rewrite map_appr_in in Hw0.
     destruct Hw0 as (w & <- & Hw).
     apply allsuffixes_spec in Hw. destruct Hw as (Hw,SF).
     rewrite allsubs_ok in Hu. destruct Hu as (Hu,SB).
     rewrite <- qprefix_alt in SB.
     apply Sub_app_inv in SB.
     destruct SB as [SB|[SB|(u1 & u2 & U1 & U2 & -> & H1 & H2)]].
     * apply Sub_len in SB. lia.
     * apply Sub_len in SB. rewrite qprefix_length in SB. lia.
     * rewrite app_length in Hu.
       set (p1 := length u1) in *.
       exists p1; split; auto.
       { rewrite in_seq.
         apply Suffix_len in H1. apply Prefix_len in H2.
         rewrite qprefix_length in H2. lia. }
       { apply map_appr_in. exists u1. split.
         - f_equal.
           assert (PR : PrefixSeq u2 (qseq q)).
           { eapply Prefix_PrefixSeq; eauto. apply qprefix_ok. }
           rewrite PR. f_equal. lia.
         - rewrite allsuffixes_spec. split; auto. unfold SuffixWords in *.
           destruct SF as (n & SF). exists n.
           apply Suffix_trans with w; auto. }
   + intros (p1 & Hp1 & Hu). apply in_seq in Hp1. apply map_appr_in in Hu.
     destruct Hu as (u1 & <- & Hu1).
     destruct (allsuffixes_extend q p1 p' u1) as (u1' & Hu1');
      trivial; try lia.
     exists (u1' ++ qprefix q p'); split; rewrite <- ?qprefix_alt.
     * apply map_appr_in. now eexists.
     * apply allsubs_ok; split.
       { rewrite app_length, qprefix_length.
         apply allsuffixes_spec in Hu1. lia. }
       { destruct Hu1' as ((v & <-),_).
         assert (PR : Prefix (qprefix q (p-p1)) (qprefix q p')).
         { eapply PrefixSeq_incl; eauto using qprefix_ok.
           rewrite !qprefix_length. lia. }
         destruct PR as (w & <-).
         exists v, w. now rewrite !app_assoc. }
Qed.

Lemma qfactors0opt_length q p :
 p<>0 -> length (qfactors0opt q p) = if p <=? q+2 then q*p+1 else (q+1)*(p-1).
Proof.
 intros Hp.
 unfold qfactors0opt.
 set (p' := pred p).
 set (r := invA_up q p').
 set (pref := firstn p' (qword q r)).
 set (suffs := allsuffixesAt q p' r).
 rewrite app_length, allsubs_length, qword_len, A_base by lia.
 rewrite MoreList.flat_map_length with (k:=p').
 2:{ intros a. rewrite map_appr_in. intros (w & <- & IN).
     rewrite allsubs_length, app_length.
     apply allsuffixesAt_spec in IN. 2:apply invA_up_spec.
     destruct IN as (->,_).
     unfold pref. rewrite firstn_length_le. lia.
     rewrite qword_len. apply invA_up_spec. }
 unfold map_appr. rewrite map_length. unfold suffs.
 rewrite allsuffixesAt_length.
 case Nat.leb_spec; nia.
Qed.

Lemma qfactors0opt_nbocc0_le q p a b :
  extrems (map (nbocc 0) (qfactors0opt q p)) = (a,b) -> a <= p /\ b <= p.
Proof.
 set (l := map (nbocc 0) (qfactors0opt q p)).
 destruct (list_eq_dec Nat.eq_dec l []) as [->|NE].
 - inversion 1. lia.
 - intros E. generalize (extrems_in1 l NE) (extrems_in2 l NE).
   rewrite E. simpl. unfold l.
   rewrite !in_map_iff. intros (u & <- & Hu) (v & <- & Hv).
   rewrite qfactors0opt_in in Hu, Hv.
   split.
   + destruct Hu as (<-,_); apply nbocc_le_length.
   + destruct Hv as (<-,_); apply nbocc_le_length.
Qed.

(** Application to quasi-additivity of f, in a faster way than in GenAdd *)

Lemma f_additivity_via_factors q p a b :
 q<>0 ->
 extrems (map (nbocc 0) (qfactors0opt q p)) = (a,b) ->
 forall n, f q n + (p-b) <= f q (n+p) <= f q n + (p-a).
Proof.
 intros Hq E n.
 assert (Hn := f_count_0 q n Hq).
 assert (Hnp := f_count_0 q (n+p) Hq).
 rewrite count_nbocc in Hn,Hnp.
 set (u := @take nat n (qseq q)) in *.
 set (w := @take nat (n+p) (qseq q)) in *.
 set (v := lastn p w).
 assert (Hw : w = u++v).
 { rewrite <- (firstn_skipn n w). f_equal.
   - unfold u, w. rewrite firstn_take; trivial. lia.
   - unfold v, lastn. f_equal. unfold w. rewrite take_length. lia. }
 rewrite Hw, nbocc_app in Hnp.
 assert (a <= nbocc 0 v <= b).
 { eapply extrems_spec; eauto. apply in_map.
   rewrite qfactors0opt_in. split.
   - unfold v. rewrite lastn_length_le; auto.
     unfold w. rewrite take_length; lia.
   - rewrite SubSeq_alt0. exists w. split. now exists u.
     unfold w. red. now rewrite take_length. }
 generalize (qfactors0opt_nbocc0_le q p a b E). lia.
Qed.

Lemma f_additivity_via_factors' q p a b :
 q<>0 -> a <= p -> b <= p ->
 extrems (map (nbocc 0) (qfactors0opt q p)) = (p-b,p-a) ->
 forall n, f q n + a <= f q (n+p) <= f q n + b.
Proof.
 intros Hq Ha Hb E n.
 generalize (f_additivity_via_factors q p _ _ Hq E n).
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

(** qfactors : All factors of some length, without duplicates.
    Obtained via cleanup of qfactors0opt from its duplicates.
    Could be more efficient someday. *)

Definition qfactors q p :=
 nodup (list_eq_dec Nat.eq_dec) (qfactors0opt q p).

Lemma qfactors_in q p u : In u (qfactors q p) <-> SubSeqLen p u (qseq q).
Proof.
 unfold qfactors. rewrite nodup_In. apply qfactors0opt_in.
Qed.

Lemma qfactors_nodup q p : NoDup (qfactors q p).
Proof.
 apply NoDup_nodup.
Qed.

Lemma qfactors_0_r q : qfactors q 0 = [[]].
Proof.
 assert (D := qfactors_nodup q 0).
 assert (I : forall u, In u (qfactors q 0) <-> u=[]).
 { intros u. unfold qfactors. rewrite nodup_In. apply qfactors0opt_0_r. }
 destruct (qfactors q 0) as [|u [|v l]].
 - now destruct (I []) as (_,[ ]).
 - f_equal. rewrite <- I. now left.
 - replace u with (@nil nat) in D by (symmetry; rewrite <- I; intuith).
   replace v with (@nil nat) in D by (symmetry; rewrite <- I; intuith).
   inversion_clear D. simpl in *. intuition.
Qed.

Lemma qfactors_0_l p : qfactors 0 p = [repeat 0 p].
Proof.
 assert (E : forall b a, subseq a b (qseq 0) = repeat 0 b).
 { unfold subseq. induction b; simpl; auto. intros a. f_equal; auto.
   generalize (qseq_letters 0 a). lia. }
 assert (IN : In (repeat 0 p) (qfactors 0 p)).
 { rewrite qfactors_in. split. now rewrite repeat_length.
   exists 0. rewrite repeat_length. auto. }
 apply Permutation_length_1_inv. symmetry. apply NoDup_Permutation_bis.
 - apply qfactors_nodup.
 - simpl. destruct (qfactors 0 p). easy. simpl. lia.
 - intros x. rewrite qfactors_in. intros (L & q & ->).
   simpl. left. now rewrite E, L.
Qed.

Lemma nodup_length_le {A}(dec : forall (a b:A),{a=b}+{a<>b}) l :
  length (nodup dec l) <= length l.
Proof.
 induction l; simpl; auto. destruct in_dec; simpl; lia.
Qed.

Lemma qfactors_linear_length q p :
  length (qfactors q p) <= if p <=? q+2 then q*p+1 else (q+1)*(p-1).
Proof.
 destruct (Nat.eq_dec p 0) as [->|Hp].
 - rewrite qfactors_0_r. simpl; lia.
 - rewrite <- qfactors0opt_length by trivial. apply nodup_length_le.
Qed.

(** Next, we prove in [Special.v] that [length (qfactors q p) = q*p+1]
    and hence the complexity of [qseq q] is [fun p => q*p+1].
    For that, the key property is that the left special factors
    of [qseq] are exactly its prefixes. *)
