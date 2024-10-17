Require Import MoreList GenFib Words.
Import ListNotations.

(** * [qword] Suffixes *)

(** Always exactly (q+1) different [qword] suffixes of the same length *)

Lemma qword_suffix_cycle q n u :
  Suffix u (qword q n) -> Suffix u (qword q (n+S q)).
Proof.
 intros Su.
 rewrite Nat.add_succ_r, qword_eqn by lia. replace (n+q-q) with n by lia.
 now apply Suffix_app_l.
Qed.

Lemma qword_suffix_pcycle q n p u :
  Suffix u (qword q n) -> Suffix u (qword q (n+p*S q)).
Proof.
 intros H.
 induction p.
 - simpl. now rewrite Nat.add_0_r.
 - replace (n+S p * S q) with ((n+p*S q)+S q) by lia.
   now apply qword_suffix_cycle.
Qed.

Lemma qword_suffix_cycle' q n u :
  S q <= n ->
  length u <= A q (n-S q) ->
  Suffix u (qword q n) -> Suffix u (qword q (n-S q)).
Proof.
 intros Hn Hu Su.
 replace n with (S (n-1)) in Su by lia.
 rewrite qword_eqn in Su by lia.
 replace (n-1-q) with (n-S q) in Su by lia.
 apply Suffix_app_inv in Su.
 destruct Su as [Su|(u' & E & SU)]; trivial.
 rewrite E, app_length, qword_len in Hu.
 assert (Hu' : length u' = 0) by lia.
 rewrite length_zero_iff_nil in Hu'. subst u'. subst u. now exists [].
Qed.

Lemma qword_suffix_pcycle' q n p u :
  p*S q <= n ->
  length u <= A q (n-p*S q) ->
  Suffix u (qword q n) -> Suffix u (qword q (n-p*S q)).
Proof.
 intros Hn Hu SU. revert Hn Hu.
 induction p.
 - intros _ _. simpl. now replace (n-0) with n by lia.
 - intros Hn Hu.
   replace (n - _) with ((n-p*S q)-S q) in * by lia.
   apply qword_suffix_cycle'. lia. trivial. apply IHp. lia.
   etransitivity; [apply Hu| ]. apply A_mono. lia.
Qed.

(* When n varies, the last letters of the successive [qword q n]
   is q 0 1 ... q 0 *)

Lemma qword_last q n : last (qword q n) 0 = (n+q) mod (S q).
Proof.
 induction n as [n IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases n q).
 - rewrite qword_low by lia.
   destruct n.
   + rewrite Nat.mod_small; simpl; lia.
   + replace (S n + q) with (n + 1 * S q) by lia.
     rewrite Nat.mod_add, Nat.mod_small by lia.
     now rewrite last_cons, last_seq.
 - destruct n as [|n]; try lia.
   replace (S n + q) with (n + 1 * S q) by lia.
   rewrite Nat.mod_add by lia.
   rewrite qword_eqn by lia. rewrite last_app.
   2:{ rewrite <- length_zero_iff_nil, qword_len.
       generalize (A_nz q (n - q)). lia. }
   destruct (Nat.eq_dec q n) as [->|NE].
   + now rewrite Nat.sub_diag, Nat.mod_small by lia.
   + replace (n-q) with (S (n-S q)) by lia.
     rewrite IH by lia. f_equal. lia.
Qed.

(** Hence any group of (q+1) successive suffixes is without duplicate *)

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

Lemma qword_suffix_cycle_inv0 q u n m :
  u<>[] -> Suffix u (qword q n) -> Suffix u (qword q m) ->
  n mod (S q) = m mod (S q).
Proof.
 intros Hu. revert n m.
 (* wlog *)
 assert (forall n m, n <= m ->
         Suffix u (qword q n) -> Suffix u (qword q m) ->
         n mod (S q) = m mod (S q)).
 { intros n m LE (v,Hn) (w,Hm).
   rewrite mod_diff; try lia.
   replace (m-n) with ((m+q)-(n+q)) by lia.
   rewrite <- mod_diff; try lia.
   rewrite <- !qword_last, <- Hn, <- Hm.
   now rewrite !last_app. }
 intros n m; destruct (Nat.le_gt_cases n m); intros; auto.
 symmetry; apply H; auto. lia.
Qed.

Definition allsuffixesAt q p n0 :=
  map (fun n => lastn p (qword q n)) (seq n0 (S q)).

Definition allsuffixes q p := allsuffixesAt q p (invA_up q p).

Lemma allsuffixesAt_length q p n0 :
  length (allsuffixesAt q p n0) = S q.
Proof.
 unfold allsuffixesAt. now rewrite map_length, seq_length.
Qed.

Definition SuffixWords u (f : nat -> word) := exists n, Suffix u (f n).

Lemma allsuffixesAt_spec q p n0 :
  p <= A q n0 ->
  forall u, In u (allsuffixesAt q p n0) <->
            length u = p /\ SuffixWords u (qword q).
Proof.
 intros Hn0 u. unfold allsuffixesAt. rewrite in_map_iff. split.
 - intros (n & <- & IN).
   rewrite in_seq in IN. split.
   + rewrite lastn_length_le; auto. rewrite qword_len.
     transitivity (A q n0); trivial. now apply A_mono.
   + exists n. apply lastn_Suffix.
 - intros (Hu,(n & SU)).
   setoid_rewrite in_seq.
   destruct (Nat.le_gt_cases n0 n).
   + assert (NZ : S q <> 0) by lia.
     assert (E := Nat.div_mod (n-n0) (S q) NZ).
     set (r := (n-n0) mod S q) in *.
     set (s := (n-n0) / S q) in *.
     rewrite Nat.mul_comm in E.
     assert (E' : n0+r = n-s*S q) by lia.
     exists (n0+r). split.
     2:{ split. lia. generalize (Nat.mod_upper_bound (n-n0) (S q)). lia. }
     apply (qword_suffix_pcycle' q n s u) in SU; try lia.
     * rewrite <- Hu. symmetry. apply Suffix_equiv. now rewrite E'.
     * rewrite <- E', Hu.
       etransitivity; [apply Hn0| ]. apply A_mono; lia.
   + assert (NZ : S q <> 0) by lia.
     assert (E := Nat.div_mod (n0+q-n) (S q) NZ).
     set (r := (n0+q-n) mod S q) in *.
     set (s := (n0+q-n) / S q) in *.
     assert (E' : n0+q-r = n+s*S q) by lia.
     exists (n0+q-r). split.
     2:{ generalize (Nat.mod_upper_bound (n0+q-n) (S q)). fold r. lia. }
     apply (qword_suffix_pcycle q n s u) in SU.
     rewrite <- Hu. symmetry. apply Suffix_equiv. now rewrite E'.
Qed.

Lemma allsuffixesAt_nodup q p n0 :
  p<>0 -> NoDup (allsuffixesAt q p n0).
Proof.
  intros Hp.
  unfold allsuffixesAt. set (f := fun n => _).
  apply NoDup_nth with (d:=f 0).
  intros i j. rewrite map_length, seq_length. intros Hi Hj.
  rewrite !map_nth, !seq_nth by lia.
  unfold f; clear f.
  intros E.
  assert (E' : last (qword q (n0+i)) 0 = last (qword q (n0+j)) 0).
  { rewrite <- last_lastn with (n:=p) by trivial.
    rewrite <- (last_lastn (qword q (n0+j)) p) by trivial.
    now f_equal. }
  rewrite !qword_last in E'.
  destruct (Nat.le_gt_cases i j).
  - apply mod_diff in E'; try lia. replace (_-_) with (j-i) in E' by lia.
    rewrite Nat.mod_small in E'; lia.
  - symmetry in E'. apply mod_diff in E'; try lia.
    replace (_-_) with (i-j) in E' by lia.
    rewrite Nat.mod_small in E'; lia.
Qed.

Lemma allsuffixesAt_permut q p n0 n0' :
  p <= A q n0 -> p <= A q n0' ->
  Permutation (allsuffixesAt q p n0) (allsuffixesAt q p n0').
Proof.
 intros H H'.
 destruct (Nat.eq_dec p 0) as [->|Hp].
 - unfold allsuffixesAt. apply eq_Permutation.
   rewrite <- (Nat.add_0_r n0), <- (Nat.add_0_r n0').
   rewrite <- !(map_add_seq (S q) 0), !map_map.
   apply map_ext. intros a. unfold lastn.
   now rewrite !Nat.sub_0_r, !skipn_all.
 - apply NoDup_Permutation; auto using allsuffixesAt_nodup.
   intros u. rewrite !allsuffixesAt_spec by trivial. reflexivity.
Qed.

Lemma allsuffixes_length q p : length (allsuffixes q p) = S q.
Proof.
 apply allsuffixesAt_length.
Qed.

Lemma allsuffixes_spec q p :
  forall u, In u (allsuffixes q p) <->
            length u = p /\ SuffixWords u (qword q).
Proof.
 apply allsuffixesAt_spec, invA_up_spec.
Qed.

Lemma allsuffixes_nodup q p :
  p<>0 -> NoDup (allsuffixes q p).
Proof.
  apply allsuffixesAt_nodup.
Qed.

Lemma SuffixWords_extend q p u :
  SuffixWords u (qword q) ->
  length u <= p ->
  exists v, length v = p /\ Suffix u v /\ SuffixWords v (qword q).
Proof.
 intros (n & Hu) LE.
 set (s := S ((p-n)/S q)).
 assert (p <= n + s*S q).
 { generalize (Nat.div_mod_eq (p-n) (S q)) (Nat.mod_upper_bound (p-n) (S q)).
   lia. }
 set (p' := n+s*S q).
 set (v := lastn p (qword q p')).
 assert (length v = p).
 { unfold v. rewrite lastn_length_le; trivial. rewrite qword_len.
   transitivity (S p'). lia. apply A_lt_id. }
 exists v. repeat split; auto.
 - apply Suffix_Suffix with (qword q p').
   + lia.
   + now apply qword_suffix_pcycle.
   + apply lastn_Suffix.
 - exists p'. apply lastn_Suffix.
Qed.

Lemma allsuffixes_extend q p p' u : p <= p' ->
  In u (allsuffixes q p) -> exists v, Suffix u v /\ In v (allsuffixes q p').
Proof.
 rewrite allsuffixes_spec. intros LE (E,SW).
 destruct (SuffixWords_extend q p' u SW) as (v & Hv & SU & SW'). lia.
 exists v; split; trivial. now rewrite allsuffixes_spec.
Qed.
