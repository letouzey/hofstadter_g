Require Import MoreFun MoreList DeltaList FunG GenFib GenG Words.
Import ListNotations.

Notation lia := (ltac:(lia)) (only parsing).

(** * WordGrowth *)

(** Follow-up of [Words.v] dedicated to the study of positions
    of some letters in the infinite words [(qseq q)].
    Applications :
    - the count of letter q decreases with q
    - the count of letter 0 decreases with q
    - for all point n, [f q n <= f (S q) n]. *)

(** [qnsub] : a shortcut for repeated application of [qsubst] *)

Definition qnsub q j : word -> word := napply (qsubst q) j.

Lemma qnsub_app q j u v : qnsub q j (u++v) = qnsub q j u ++ qnsub q j v.
Proof.
 apply napply_app.
Qed.

Lemma qnsub_prefixseq_gen q j w :
  PrefixSeq w (qseq q) -> PrefixSeq (qnsub q j w) (qseq q).
Proof.
 intros.
 apply PrefixSeq_napply; trivial using qsubst_noerase, qsubst_prolong.
Qed.

Lemma qnsub_prefixseq q j n : PrefixSeq (qnsub q j (qprefix q n)) (qseq q).
Proof.
 apply qnsub_prefixseq_gen, qprefix_ok.
Qed.

Lemma qnsub_qword_gen q j n :
  n <= q -> q <= j+n -> qnsub q j [n] = qword q (j+n-q).
Proof.
 intros. unfold qnsub. now apply napply_qsubst_is_qword.
Qed.

Lemma qnsub_qword q j : qnsub q j [q] = qword q j.
Proof.
 rewrite qnsub_qword_gen; f_equal; lia.
Qed.

Lemma qnsub_alt q j n :
  n <= q -> qnsub q j [n] = if j+n <? q then [j+n] else qword q (j+n-q).
Proof.
 case Nat.ltb_spec; intros.
 - unfold qnsub. rewrite napply_qsubst_shift; f_equal; lia.
 - apply qnsub_qword_gen; lia.
Qed.

Lemma qnsub_len q j n : n <= q -> length (qnsub q j [n]) = A q (j+n-q).
Proof.
 intros. rewrite qnsub_alt by trivial.
 case Nat.ltb_spec; intros; simpl; try apply qword_len.
 replace (j+n-q) with 0 by lia. trivial.
Qed.

Lemma qnsub_q_alt q n : n <= q -> qnsub q q [n] = qword q n.
Proof.
 intros. rewrite qnsub_qword_gen; f_equal; lia.
Qed.

Lemma qnsub_Sq_alt q n : n <= q -> qnsub q (S q) [n] = qword q (S n).
Proof.
 intros. rewrite qnsub_qword_gen; f_equal; lia.
Qed.

Lemma qnsub_q_len q n : n <= q -> length (qnsub q q [n]) = S n.
Proof.
 intros. rewrite qnsub_len, A_base; lia.
Qed.

Lemma qnsub_Sq_len q n : n <= q -> length (qnsub q (S q) [n]) = 2+n.
Proof.
 intros. rewrite qnsub_len, A_base; lia.
Qed.

Lemma qnsub_len_low q j : j <= S q -> length (qnsub q j [q]) = j+1.
Proof.
 intros. rewrite qnsub_len, A_base; lia.
Qed.

Lemma qnsub_len_le q j n : n <= q -> length (qnsub q j [n]) <= A q j.
Proof.
 intros. rewrite qnsub_len by trivial. apply A_mono. lia.
Qed.

(** Fun fact: for n <= q, qsubst^q(n) = qsubst^n(q) *)

Lemma qnsub_pearl q n : n <= q -> qnsub q q [n] = qnsub q n [q].
Proof.
 intros. rewrite !qnsub_alt by lia. now rewrite (Nat.add_comm q n).
Qed.


(** [L] : length of the repeated expansion of a qseq prefix.
    Right adjoint of [f]. *)

Definition L q j n := length (qnsub q j (qprefix q n)).

Lemma L_0 q j : L q j 0 = 0.
Proof.
 unfold L, qnsub. cbn. now rewrite napply_nil.
Qed.

Lemma L_S q j n : L q j (S n) = L q j n + length (qnsub q j [qseq q n]).
Proof.
 unfold L. now rewrite take_S, qnsub_app, app_length.
Qed.

Lemma L_incr q j : IncrFun (L q j).
Proof.
 intro n. rewrite L_S.
 generalize (@napply_mono _ 0 j [qseq q n] (qsubst_noerase q)).
 unfold qnsub. simpl. lia.
Qed.

Lemma L_lt q j n m : n < m <-> L q j n < L q j m.
Proof.
 apply incr_strmono_iff. apply L_incr.
Qed.

Lemma L_add q i j n : L q i (L q j n) = L q (i+j) n.
Proof.
 unfold L. f_equal.
 generalize (qnsub_prefixseq q j n). unfold PrefixSeq. intros <-.
 unfold qnsub. symmetry. apply napply_add.
Qed.

Lemma L_q_0 q n : L q 0 n = n.
Proof.
 unfold L, qnsub. simpl. apply qprefix_length.
Qed.

Lemma L_iter q j n : L q j n = ((L q 1)^^j) n.
Proof.
 revert n. induction j; simpl; intros.
 - apply L_q_0.
 - now rewrite <- IHj, L_add.
Qed.

Lemma L_ge_n q j n : n <= L q j n.
Proof.
 revert n.
 assert (H : forall n, n <= L q 1 n).
 { intros n. unfold L, qnsub. simpl.
   rewrite <- (qprefix_length q n) at 1.
   apply apply_grow, qsubst_noerase. }
 induction j; intros.
 - cbn. now rewrite qprefix_length.
 - change (S j) with (1+j). rewrite <- L_add.
   transitivity (L q j n); trivial.
Qed.

Lemma L_mono_j q j j' n : j <= j' -> L q j n <= L q j' n.
Proof.
 intros. replace j' with ((j'-j)+j) by lia. rewrite <- L_add. apply L_ge_n.
Qed.

Lemma L_gt_n q j n : 0<j -> 0<n -> n < L q j n.
Proof.
 revert n.
 assert (H : forall n, 0<n -> n < L q 1 n).
 { intros n Hn. unfold L, qnsub. simpl.
   destruct n; try easy. cbn. rewrite app_length.
   set (w := map _ _).
   assert (n <= length (apply (qsubst q) w)).
   { replace n with (length w)
      by (unfold w; now rewrite map_length, seq_length).
     apply apply_grow, qsubst_noerase. }
   rewrite qsubst_q. simpl. lia. }
 induction j; intros; try easy.
 destruct j. now apply H.
 change (S (S j)) with (1+S j). rewrite <- L_add.
 apply Nat.lt_le_trans with (L q (S j) n). apply IHj; lia.
 apply L_ge_n.
Qed.

Lemma L_strmono_j q j j' n : 0 < n -> j < j' -> L q j n < L q j' n.
Proof.
 intros. replace j' with ((j'-j)+j) by lia. rewrite <- L_add. apply L_gt_n.
 lia. apply Nat.lt_le_trans with n; trivial. apply L_ge_n.
Qed.

Lemma L_0_1 n : L 0 1 n = 2*n.
Proof.
 induction n; try easy.
 rewrite L_S, IHn. cbn. unfold qsubst.
 replace (qseq 0 n) with 0 by (generalize (qseq_letters 0 n); lia).
 simpl. lia.
Qed.

Lemma qnsub_qprefix q j n : qnsub q j (qprefix q n) = qprefix q (L q j n).
Proof.
 apply qnsub_prefixseq.
Qed.

(** Steiner's Theorem : direct linq between f and qseq *)

Definition LBound q j n m := L q j (m-1) < n <= L q j m.

Definition SteinerThm q j n := 0<n -> LBound q j n (fs q j n).

Lemma steiner_thm_q0_j1 n : SteinerThm 0 1 n.
Proof.
 red. red. rewrite !L_0_1. simpl fs.
 induction n.
 - inversion 1.
 - intros _. rewrite f_S. simpl fs.
   destruct (Nat.eq_dec n 0) as [->|N]; [simpl; lia | lia].
Qed.

Lemma steiner_thm_disj q n :
  LBound q 1 n (f q n) -> L q 1 (f q n) = n \/ qseq q n = 0.
Proof.
  unfold LBound. intros IH1.
  destruct (Nat.eq_dec n 0) as [->|N]; [now left|].
  generalize (qnsub_prefixseq q 1 (f q n)).
  revert IH1.
  replace (f q n) with (S (f q n - 1)) at 2 3 4
    by (generalize (@f_nonzero q n); lia).
  rewrite L_S. unfold L.
  rewrite take_S, qnsub_app. unfold PrefixSeq. rewrite app_length.
  set (w := qnsub q 1 (qprefix q (f q n - 1))).
  set (x := qseq _ _) in *.
  unfold qnsub. simpl. rewrite app_nil_r.
  unfold qsubst. case Nat.eqb; intros W0 W; simpl in *; try lia.
  destruct (Nat.eq_dec (length w) (n-1)) as [W'|W']; try lia.
  right. rewrite W' in W.
  rewrite Nat.add_succ_r, Nat.add_1_r in W.
  rewrite !take_S, <- app_assoc in W. simpl in W.
  apply app_inv' in W; try easy.
  destruct W as (_,[= _ ->]). f_equal. lia.
Qed.

Lemma steiner_thm_corestep q n : 2<=n ->
  (forall j, SteinerThm q j (n-1)) ->
  (forall j, SteinerThm q j n) ->
  SteinerThm q 1 (S n).
Proof.
 intros Hn IHn1 IHn.
 (* Case q=0 must be handled separately (but it's easy, L is double) *)
 destruct (Nat.eq_dec q 0) as [->|Hq]; [ apply steiner_thm_q0_j1 | ].
 assert (Hn' : S (n-1) = n) by lia.
 destruct (fs_step q (S q) (n-1)) as [E|E]; rewrite Hn' in E.
 - (* First case : f^^(S q) flat at (n-1) *)
   destruct (steiner_thm_disj q n (IHn 1 lia)) as [EQ|EQ].
   + intros _. simpl. clear IHn1 IHn.
     replace (f q (S n)) with (S (f q n)).
     2:{ rewrite <- Hn' at 1. rewrite !f_S, E.
         generalize (fs_le q (S q) (n-1)). lia. }
     unfold LBound. simpl. rewrite Nat.sub_0_r, L_S, EQ.
     unfold qnsub. simpl. unfold qsubst. case Nat.eqb; simpl; lia.
   + exfalso.
     specialize (IHn (S q) lia). destruct IHn as (_,IHn).
     apply Nat.le_lteq, or_comm in IHn. destruct IHn as [IHn|IHn].
     * clear IHn1.
       set (m := fs q (S q) n) in *.
       generalize (qnsub_prefixseq q (S q) (S m)).
       generalize (qnsub_prefixseq q (S q) m).
       rewrite take_S, qnsub_app. unfold PrefixSeq. rewrite app_length.
       unfold L in IHn. rewrite <- IHn. intros ->. clear IHn.
       assert (Hx := qseq_letters q m).
       set (x := qseq q m) in *.
       rewrite qnsub_Sq_len, qnsub_Sq_alt, qword_low by lia.
       rewrite take_add.
       intros W. apply app_inv_head in W. simpl in W.
       injection W as W _ _. lia.
     * specialize (IHn1 (S q) lia). destruct IHn1 as (IHn1,_).
       rewrite <- E in IHn1.
       set (m := fs q (S q) n - 1) in *.
       replace (fs _ _ _) with (S m) in IHn.
       2:{ unfold m. generalize (@fs_nonzero q n (S q)); lia. }
       rewrite L_S in IHn.
       generalize (qnsub_prefixseq q (S q) (S m)).
       generalize (qnsub_prefixseq q (S q) m).
       rewrite take_S, qnsub_app. unfold PrefixSeq. rewrite app_length.
       assert (Hx := qseq_letters q m).
       set (x := qseq q m) in *.
       rewrite qnsub_Sq_len, qnsub_Sq_alt, qword_low in * by lia.
       fold (L q (S q) m). set (lm := L q (S q) m) in *. intros ->.
       simpl. rewrite take_add.
       intros W. apply app_inv_head in W. simpl in W.
       injection W as _ _ W.
       assert (IN : In 0 (seq 1 x)).
       { rewrite W, <- EQ. apply in_map, in_seq. lia. }
       apply in_seq in IN. lia.
 - (* Second case : f^^(S q) step at (n-1) *)
   intros _. simpl. replace (f q (S n)) with (f q n).
   2:{ rewrite <- Hn' at 1.
       rewrite !f_S, E. generalize (fs_le q (S q) (n-1)). lia. }
   split; [ apply Nat.lt_lt_succ_r, (IHn 1); lia| ].
   assert (E' : f q n = S (f q (n-1))).
   { destruct (f_step q (n-1)) as [E'|E']; rewrite Hn' in *; trivial.
     exfalso. rewrite !iter_S, <- E' in E; lia. }
   rewrite E', L_S.
   assert (HL : L q 1 (f q (n-1)) = n-1).
   { destruct (IHn1 1 lia) as (_,LB).
     destruct (IHn 1 lia) as (UB,_).
     simpl in LB,UB. rewrite E' in UB.
     simpl in UB. rewrite Nat.sub_0_r in *. lia. }
   rewrite HL.
   assert (HL' : L q (S q) (fs q (S q) (n-1)) = n-1).
   { destruct (IHn1 (S q) lia) as (_,LB).
     destruct (IHn (S q) lia) as (UB,_).
     rewrite E in UB. simpl in *. rewrite Nat.sub_0_r in *. lia. }
   clear IHn1 IHn.
   assert (EL := qnsub_prefixseq q 1 (f q (n-1))).
   assert (EL' := qnsub_prefixseq q (S q) (fs q (S q) (n-1))).
   red in EL,EL'. unfold L in HL,HL'. rewrite HL,HL' in *. clear HL HL'.
   assert (Q0 : qseq q (n-1) = q /\ qseq q n = 0).
   { generalize (qnsub_prefixseq q (S q) (fs q (S q) n)).
     rewrite E, take_S, qnsub_app, EL'.
     assert (Hx := qseq_letters q (fs q (S q) (n-1))).
     set (x := qseq _ _) in *.
     unfold PrefixSeq. rewrite app_length, qprefix_length, take_add.
     rewrite qnsub_Sq_len, qnsub_Sq_alt, qword_low by lia.
     simpl. rewrite Hn'.
     intro V. apply app_inv_head in V. now injection V as <- <- _. }
   destruct Q0 as (Q,Q').
   generalize (qnsub_prefixseq q 1 (S (f q n))).
   rewrite E', 2 take_S, !qnsub_app, EL. clear E E' EL EL'.
   set (x := qseq q (f q (n-1))).
   set (y := qseq q (S _)). clearbody x y.
   unfold qnsub. simpl. rewrite !app_nil_r. unfold PrefixSeq.
   rewrite !app_length, qprefix_length, <- Nat.add_assoc, <- app_assoc.
   rewrite take_add.
   intros V. apply app_inv_head in V. revert V.
   unfold qsubst.
   case Nat.eqb. intros _; simpl; lia.
   case Nat.eqb; simpl; rewrite Hn'; injection 1; lia.
Qed.

Lemma steiner_thm q j n : 0 < n -> LBound q j n (fs q j n).
Proof.
 change (SteinerThm q j n).
 revert j. induction n as [n IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases n 2) as [Hn|Hn].
 - destruct n as [|[|[|n]]]; try lia.
   + (* n=0 *) inversion 1.
   + (* n=1 *)
     intros j _. unfold LBound. rewrite fs_q_1, L_0. auto using L_ge_n.
   + (* n=2 *)
     intros [|j] _; unfold LBound.
     * simpl. rewrite !L_q_0. lia.
     * rewrite fs_q_2, L_0 by lia. split; auto. apply L_gt_n; lia.
 - destruct n; try lia.
   assert (J1 : SteinerThm q 1 (S n)).
   { apply steiner_thm_corestep; try apply IH; lia. }
   intros [|j].
   + (* j=0 *)
     intros _. unfold LBound. rewrite !L_q_0. cbn. lia.
   + (* j<>0 *)
     assert (FS : f q (S n) < S n) by (apply f_lt; lia).
     assert (FS0 : 0 < f q (S n)) by (apply f_nonzero; lia).
     specialize (IH (f q (S n)) FS j FS0).
     rewrite <- iter_S in IH.
     destruct IH as (IH1,IH2). apply Nat.lt_le_pred in IH1.
     rewrite <- Nat.sub_1_r in IH1.
     apply (incr_mono _ (L_incr q 1)) in IH1,IH2.
     rewrite L_add in IH1, IH2. simpl "+" in IH1,IH2.
     unfold SteinerThm, LBound in *. simpl in J1. lia.
Qed.

Lemma LBound_unique q j m n n' : LBound q j m n -> LBound q j m n' -> n=n'.
Proof.
 unfold LBound; intros.
 assert (n'-1 < n) by (apply (incr_strmono_iff _ (L_incr q j)); lia).
 assert (n-1 < n') by (apply (incr_strmono_iff _ (L_incr q j)); lia).
 lia.
Qed.

Lemma steiner_thm_iff q j n m : 0<n -> fs q j m = n <-> LBound q j m n.
Proof.
 intros Hn.
 split.
 - intros <-. apply steiner_thm.
   destruct m; try lia. now rewrite fs_q_0 in *.
 - intros.
   apply (LBound_unique q j m); trivial.
   apply steiner_thm. unfold LBound in *. lia.
Qed.

(** Said otherwise, [L q j n] is the largest antecedent of [n] by [fs q j],
    and [S (L q j n)] is the least antecedent of [S n]. *)

Lemma fs_L q j n : fs q j (L q j n) = n.
Proof.
 destruct n.
 - now rewrite L_0, fs_q_0.
 - apply steiner_thm_iff; try lia. split; trivial. apply L_lt; lia.
Qed.

Lemma fs_S_L q j n : fs q j (S (L q j n)) = S n.
Proof.
 apply steiner_thm_iff; try lia. split.
 - replace (S n - 1) with n; lia.
 - apply L_lt; lia.
Qed.

Lemma fs_rightmost_child_carac q j a n :
  fs q j n = a -> fs q j (S n) = S a <-> n = L q j a.
Proof.
 destruct (Nat.eq_dec a 0) as [->|Ha]; intros E.
 - apply fs_0_inv in E. subst n. now rewrite fs_q_1, L_0.
 - split; intros E'.
   + apply steiner_thm_iff in E, E'; try lia. unfold LBound in *.
     replace (S a - 1) with a in *; lia.
   + rewrite E'. apply fs_S_L.
Qed.

Lemma L_q_1_rchild q n : L q 1 n = rchild q n.
Proof.
 rewrite <- rightmost_child_carac. apply (fs_S_L q 1). apply (fs_L q 1).
Qed.

(** Exactly enumerating antecedents of [fs q j], in increasing order *)

Definition fsinv q j n :=
  if n =? 0 then [0]
  else
    let a := L q j (n-1) in
    let b := L q j n in
    seq (S a) (b-a).

Lemma fsinv_spec q j n m : In m (fsinv q j n) <-> fs q j m = n.
Proof.
 unfold fsinv.
 case Nat.eqb_spec; [intros ->|intros Hn].
 - split; simpl.
   + intros [<-|[ ]]. apply fs_q_0.
   + generalize (@fs_nonzero q m j). lia.
 - rewrite in_seq, steiner_thm_iff; unfold LBound; lia.
Qed.

Lemma fsinv_delta1 q j n : Delta 1 (fsinv q j n).
Proof.
 unfold fsinv. case Nat.eqb. constructor. apply Delta_seq.
Qed.

Lemma fsinv_nodup q j n : NoDup (fsinv q j n).
Proof.
 eapply Delta_NoDup, fsinv_delta1.
Qed.

Lemma fsinv_S_length q j n :
  length (fsinv q j (S n)) = length (qnsub q j [qseq q n]).
Proof.
 unfold fsinv. simpl. rewrite Nat.sub_0_r, L_S, seq_length. lia.
Qed.

Lemma fsinv_length q j n :
  length (fsinv q j n) =
  match n with 0 => 1 | S n => length (qnsub q j [qseq q n]) end.
Proof.
 unfold fsinv. destruct n; simpl; trivial. now rewrite <- fsinv_S_length.
Qed.

Lemma fsinv_bound q j n : 0<n ->
  A q (j-q) <= length (fsinv q j n) <= A q j.
Proof.
 destruct n; try easy. intros _.
 rewrite fsinv_S_length.
 set (x := qseq q n).
 assert (Hx : x <= q) by apply qseq_letters.
 rewrite qnsub_len by trivial. split; apply A_mono; lia.
Qed.

(** For each q and j, these bounds are reached infinitely often when n vary.
    For instance : *)

Lemma fsinv_1 q j : length (fsinv q j 1) = A q j.
Proof.
 rewrite fsinv_S_length, qseq_q_0, qnsub_len; f_equal; lia.
Qed.

Lemma fsinv_2 q j : length (fsinv q j 2) = A q (j-q).
Proof.
 rewrite fsinv_S_length, qseq_q_1, qnsub_len; f_equal; lia.
Qed.


(** Streiner's second theorem :
    Monotony statements about [L q j] when q varies,
    and application to monotony of [fs] and [f].
    Inspired by an earlier proof by Shuo Li. *)

Definition C q i n := count (qseq q) i n.

Lemma Cqq_nz q n : 0 < n -> 0 < C q q n.
Proof.
 unfold C.
 induction n.
 - lia.
 - intros _. destruct n; simpl in *; try lia.
   rewrite qseq_q_0, Nat.eqb_refl. lia.
Qed.

Lemma Lq1_Cqq q n : L q 1 n = n + C q q n.
Proof.
 induction n; [easy|].
 rewrite L_S, IHn. unfold C. cbn. unfold qsubst.
 case Nat.eqb; simpl; lia.
Qed.

Lemma steiner_trick q n : (* with additions instead of subtractions *)
  L (S q) (S (S q)) n + L q q n = L (S q) (S q) n + L q (S q) n.
Proof.
 induction n.
 - now rewrite !L_0.
 - rewrite !L_S, !qnsub_Sq_len, !qnsub_q_len by apply qseq_letters. lia.
Qed.

Lemma qnsub_q_nbocc q u :
  Forall (fun a : nat => a <= q) u ->
  nbocc q (qnsub q q u) = length u.
Proof.
 induction u as [|i u IH]; intros Hu.
 - unfold qnsub. now rewrite napply_nil.
 - inversion Hu; subst.
   rewrite (qnsub_app _ _ [i] u), nbocc_app, IH by trivial. clear IH.
   rewrite qnsub_q_alt by trivial.
   rewrite qword_low by lia. simpl. rewrite Nat.eqb_refl.
   rewrite nbocc_notin; rewrite ?in_seq; lia.
Qed.

Lemma LBound_Cqq q n m : 0<n -> LBound q q n m -> m = C q q n.
Proof.
 unfold LBound. intros Hn H.
 assert (m <> 0). { intros ->. simpl in *. rewrite !L_0 in H. lia. }
 replace m with (S (m-1)) in H at 2 by lia.
 rewrite L_S in H.
 assert (Hx := qseq_letters q (m-1)).
 set (x := qseq q (m-1)) in *.
 unfold C. rewrite count_nbocc.
 assert (P := qnsub_prefixseq q q (S (m-1))).
 rewrite !take_S, !qnsub_app in P. fold x in P.
 rewrite qnsub_q_alt in * by trivial.
 set (u := qnsub _ _ _) in *.
 change (L q q (m-1)) with (length u) in H.
 assert (P' : Prefix (qprefix q n) (u++qword q x)).
 { eapply PrefixSeq_incl; eauto using qprefix_ok.
   rewrite qprefix_length, app_length; lia. }
 clear P. rename P' into P.
 apply Prefix_app in P. destruct P as [P|(v & E & P)].
 { apply Prefix_len in P. rewrite qprefix_length in P. lia. }
 rewrite E, nbocc_app. unfold u.
 rewrite qnsub_q_nbocc, qprefix_length by apply qprefix_letters.
 rewrite qword_low in P by lia.
 apply Prefix_cons_inv in P. destruct P as [->|(w & E' & P)].
 { apply (f_equal (@length _)) in E.
   rewrite qprefix_length, app_nil_r in E. lia. }
 { rewrite E'. simpl. rewrite Nat.eqb_refl. rewrite nbocc_notin; try lia.
   intro IN. apply Prefix_incl in P. specialize (P q IN).
   rewrite in_seq in P. lia. }
Qed.

(* NB: already in Words, via a different proof *)

Lemma fs_count_q q n : fs q q n = C q q n.
Proof.
 destruct (Nat.eq_dec n 0) as [->|N].
 - now rewrite fs_q_0.
 - apply LBound_Cqq; try lia. apply steiner_thm; lia.
Qed.

Lemma Lq_LSq q n :
 L (S q) 1 n <= L q 1 n
 /\ (0<n -> forall j, j<=S q -> L q j n < L (S q) (S j) n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 destruct (Nat.eq_dec n 0) as [->|N0]; [easy|].
 destruct (Nat.eq_dec n 1) as [->|N1].
 { clear N0 IH. split; intros;
   rewrite !L_S, !L_0, !qseq_q_0, !qnsub_qword, !qword_len, !A_base; lia. }
 split.
 - rewrite !Lq1_Cqq, <- !fs_count_q, <- Nat.add_le_mono_l.
   set (c := fs q q n).
   set (c' := fs (S q) (S q) n).
   destruct (Nat.eq_dec c' 0); try lia.
   replace c' with (S (c'-1)) by lia. change (c'-1 < c).
   apply (incr_strmono_iff _ (L_incr (S q) (S q))).
   apply Nat.lt_le_trans with n; [apply steiner_thm; lia|].
   transitivity (L q q c); [apply steiner_thm; lia|].
   destruct (Nat.eq_dec q 0) as [->|Q].
   + rewrite L_q_0. apply L_ge_n.
   + apply Nat.lt_le_incl, IH; try apply fs_lt; try apply fs_nonzero; lia.
 - intros _. destruct n; try easy.
   destruct (Nat.eq_dec (qseq (S q) n) (S q)) as [E|N].
   + intros j Hj. rewrite !L_S, E.
     rewrite qnsub_qword, qword_len.
     assert (Hx := qseq_letters q n).
     set (x := qseq q n) in *.
     generalize (qnsub_len_le q j x Hx). rewrite !A_base by lia.
     destruct (IH n lia) as (_,IH').
     specialize (IH' lia j Hj).
     lia.
   + destruct (qsubst_prefix_inv (S q) (qprefix (S q) (S n)))
       as (v & w & Hv & E & Hw); try apply qprefix_ok.
     destruct Hw as [-> | ->].
     2:{ rewrite take_S in Hv; apply app_inv' in Hv; trivial;
         destruct Hv as (_,[= E']); lia. }
     rewrite app_nil_r in Hv.
     red in E.
     set (l := length v) in *.
     assert (E' : L (S q) 1 l = S n).
     { now rewrite <- (qprefix_length (S q) (S n)), Hv, E. }
     assert (Hl0 : l <> 0). { intros ->. now rewrite L_0 in E'. }
     assert (Hl : l < S n).
     { rewrite <- E'. rewrite Lq1_Cqq.
       generalize (Cqq_nz (S q) l). lia. }
     destruct (IH l Hl) as (IH5,IH6). clear IH. rewrite E' in IH5.
     specialize (IH6 lia).
     assert (LT : forall j, j <= q -> L q j (S n) < L (S q) (S j) (S n)).
     { intros j Hj. specialize (IH6 (S j) lia).
       rewrite <- E' at 2. rewrite L_add, Nat.add_1_r.
       eapply Nat.le_lt_trans; [|apply IH6].
       rewrite <- (Nat.add_1_r j), <- L_add. apply incr_mono; trivial.
       apply L_incr. }
     intros j Hj. destruct (Nat.eq_dec j (S q)) as [->|Hj'].
     * generalize (steiner_trick q (S n)).
       specialize (LT q (Nat.le_refl _)). lia.
     * apply LT. lia.
Qed.

Lemma Lq1_ge_LSq1 q n : L (S q) 1 n <= L q 1 n.
Proof.
 apply Lq_LSq.
Qed.

Lemma Lqj_lt_LSqSj q j n :
 j <= S q -> 0 < n -> L q j n < L (S q) (S j) n.
Proof.
 intros. now apply Lq_LSq.
Qed.

Lemma fs_decreases q j n :
 j <= S q -> fs (S q) (S j) n <= fs q j n.
Proof.
 intros Hj.
 destruct (Nat.eq_dec n 0) as [->|Hn].
 - now rewrite !fs_q_0.
 - apply Nat.lt_pred_le. rewrite <- Nat.sub_1_r, (L_lt (S q) (S j)).
   transitivity n; [ apply steiner_thm; lia |].
   eapply Nat.le_lt_trans; [ apply (steiner_thm q j); lia|].
   apply Lqj_lt_LSqSj; trivial. apply fs_nonzero; lia.
Qed.

Theorem f_grows q n : f q n <= f (S q) n.
Proof.
 destruct n; [easy|].
 rewrite !f_S. generalize (fs_decreases q (S q) n). lia.
Qed.

(* TODO: show this inequality is actually strict except for a few low n *)

Lemma f_grows_gen q q' n n' : q <= q' -> n <= n' -> f q n <= f q' n'.
Proof.
 intros Q N. transitivity (f q' n); [ | now apply f_mono]. clear n' N.
 induction Q; trivial. generalize (f_grows m n); lia.
Qed.

Lemma fs_grows q p n : fs q p n <= fs (S q) p n.
Proof.
 revert n.
 induction p as [|p IH]; intros n; try easy.
 rewrite !iter_S. etransitivity; [apply IH|]. apply fs_mono, f_grows.
Qed.

Lemma fs_grows_gen q q' p p' n n' :
  q <= q' -> p >= p' -> n <= n' -> fs q p n <= fs q' p' n'.
Proof.
 intros Q P N.
 transitivity (fs q p' n).
 - replace p with ((p-p')+p') by lia. rewrite iter_add. apply fs_le.
 - clear P p. rename p' into p.
   transitivity (fs q' p n); [ | now apply fs_mono]. clear n' N.
   induction Q; trivial. generalize (fs_grows m p n). lia.
Qed.

(** Note: when j=q+2, it seems that L q j n <= L (q+1) (j+1) n.
    Especially we can have L q j n = L (q+1) (j+1) n,
    for instance L 2 4 4 = L 3 5 4 = 19.
    This equality is always in n=q+2,
    and L q (q+2) (q+2) = L (S q) (q+3) (q+2) is provable by
    direct enumeration (qsubstw q Sq (qsubstw(qword q (S q)), etc).

    Proving this L q (q+2) n <= L (q+1) (q+3) n would imply
    fs q (q+2) n >= fs (q+1) (q+3) n.

    And for j>q+2, we can even have L q j n > L (q+1) (j+1) n,
    for instance L 2 5 4 = 28 > L 3 6 4 = 26.
*)

(** An interesting lattice of increasing functions : *)

Lemma fs_bound_gen q j n :
 j <= S q -> fs q j n <= fs (q-1) (j-1) n <= fs q (j-1) n.
Proof.
 destruct q, j; try easy.
 - inversion 1. simpl. split; trivial. apply f_le.
   simpl. split; trivial. rewrite Nat.sub_0_r. apply f_le.
 - replace (S q - 1) with q by lia.
   replace (S j - 1) with j by lia.
   split. apply fs_decreases; lia. apply fs_grows_gen; lia.
Qed.

Lemma fs_bound_gen' q j n :
 j <= q+2 -> fs q j n <= fs (S q) j n <= fs q (j-1) n.
Proof.
 destruct j; try easy.
 split. apply fs_grows_gen; lia.
 replace (S j - 1) with j by lia. apply fs_decreases; lia.
Qed.


(** Counting letter p < q.

    The key idea: no matter which letter is i, the letter p occurs
    exactly once in [qnsub q (q+S p) [i]], always at position (S p).

    This subsumes an older section dedicated specifically to letter 0.
*)

Lemma qword_flatmap q n :
  qword q (q+n) = flat_map (qword q) (q :: seq 0 n).
Proof.
 induction n.
 - rewrite Nat.add_0_r. simpl. now rewrite app_nil_r.
 - rewrite Nat.add_succ_r, qword_eqn, IHn by lia.
   replace (q+n-q) with n by lia.
   rewrite seq_S. simpl. rewrite <- app_assoc, flat_map_app.
   do 2 f_equal. simpl. now rewrite app_nil_r.
Qed.

Lemma qnsub_unique_letter q p i : p < q -> i <= q ->
 exists w, qnsub q (q+S p) [i] = qword q p ++ [p] ++ w /\ ~In p w.
Proof.
 intros Hp Hi. rewrite qnsub_qword_gen by lia.
 replace (q+S p+i-q) with (S p+i) by lia.
 destruct (qword_prefix q (S p) (S p+i) lia) as (w,Hw).
 exists w. split.
 - rewrite <- Hw. rewrite !qword_low, seq_S by lia. simpl.
   now rewrite <- app_assoc.
 - destruct (Nat.le_gt_cases (S p + i) q).
   + rewrite !qword_low in Hw by lia.
     rewrite seq_app in Hw. injection Hw as Hw. apply app_inv_head in Hw.
     subst. rewrite in_seq. lia.
   + replace (S p + i) with (q + (S p + i - q)) in Hw by lia.
     rewrite qword_flatmap in Hw.
     set (n := S p + i - q) in *.
     simpl in Hw. rewrite !qword_low in Hw by lia.
     replace q with (S p + (q - S p)) in Hw at 3 by lia.
     rewrite seq_app in Hw. injection Hw as Hw.
     rewrite <- app_assoc in Hw. apply app_inv_head in Hw.
     subst. rewrite in_app_iff, in_seq.
     intros [IN|IN]; try lia.
     rewrite in_flat_map in IN. destruct IN as (x & Hx & IN).
     rewrite in_seq in Hx. rewrite qword_low in IN by lia. simpl in IN.
     rewrite in_seq in IN. lia.
Qed.

Lemma qnsub_unique_letter' q p i : p < q -> i <= q ->
 exists w w', qnsub q (q+S p) [i] = w++[p]++w'
              /\ length w = S p /\ ~In p w /\ ~In p w'.
Proof.
 intros Hp Hi.
 destruct (qnsub_unique_letter q p i Hp Hi) as (w & E & W).
 exists (qword q p), w; repeat split; trivial.
 - rewrite qword_len, A_base; lia.
 - rewrite qword_low by lia. simpl. rewrite in_seq; lia.
Qed.

Lemma qnsub_nbocc q p u : p < q ->
  Forall (fun a : nat => a <= q) u ->
  nbocc p (qnsub q (q+S p) u) = length u.
Proof.
 intros Hp.
 induction u as [|i u IH]; intros Hu.
 - unfold qnsub. now rewrite napply_nil.
 - inversion Hu; subst.
   rewrite (qnsub_app _ _ [i] u), nbocc_app, IH by trivial. clear IH.
   destruct (qnsub_unique_letter' q p i Hp) as (w & w' & -> & _ & W & W');
    trivial.
   rewrite !nbocc_app. simpl. rewrite Nat.eqb_refl. now rewrite !nbocc_notin.
Qed.

Lemma LBound_Cqp q p c n : p < q ->
  LBound q (q+S p) n c -> c = C q p (n+S p).
Proof.
intros Hp H. unfold LBound in *.
assert (c <> 0). { intros ->. rewrite !L_0 in *. lia. }
set (p' := q+S p) in *.
replace c with (S (c-1)) in H at 2 by lia. rewrite L_S in H.
unfold L in H. set (u := qnsub _ _ _) in *.
set (x := qseq q (c-1)) in *.
set (y := qseq q c) in *.
set (vx := qnsub q p' [x]) in *.
set (vy := qnsub q p' [y]).
unfold C. rewrite count_nbocc.
assert (P := qnsub_prefixseq q p' (S (S (c-1)))).
rewrite !take_S, !qnsub_app in P. replace (S (c-1)) with c in P by lia.
fold u x y vx vy in P. rewrite <- app_assoc in P.
destruct (qnsub_unique_letter' q p x Hp) as (w1 & w2 & E & L & W1 & W2);
 try apply qseq_letters.
destruct (qnsub_unique_letter' q p y Hp) as (w3 & w4 & E' & L' & W3 & W4);
 try apply qseq_letters. fold p' vx vy in E,E'.
assert (P' : Prefix (qprefix q (n+S p)) (u++vx++vy)).
{ eapply PrefixSeq_incl; eauto using qprefix_ok.
  rewrite qprefix_length, E', !app_length, L'. simpl. lia. }
clear P. rename P' into P.
rewrite E,E', <- !app_assoc, !app_length, L in *. simpl in *.
clear E E' x y vx vy.
rewrite (app_assoc u), (app_assoc w2) in P.
apply Prefix_app in P.
destruct P as [P|(w & E & P)].
{ apply Prefix_len in P. rewrite qprefix_length, app_length, L in P. lia. }
rewrite E, !nbocc_app.
unfold u.
rewrite qnsub_nbocc, qprefix_length by trivial using qprefix_letters.
clearbody u.
rewrite nbocc_notin by trivial.
apply (f_equal (@length _)) in E.
rewrite qprefix_length, !app_length, L in E.
apply Prefix_cons_inv in P. destruct P as [->|(w' & -> & P)].
{ simpl in E. lia. }
simpl in E. rename w' into w. simpl. rewrite Nat.eqb_refl.
apply Prefix_app in P.
destruct P as [P|(w' & E' & P)].
{ rewrite nbocc_notin; try lia. apply Prefix_incl in P.
  intros IN. specialize (P p IN). rewrite in_app_iff in P. tauto. }
{ destruct w' as [|z w'].
  - rewrite E', app_nil_r, nbocc_notin; try lia.
    rewrite in_app_iff; tauto.
  - exfalso. apply (f_equal (@length _)) in E'.
    rewrite !app_length, L' in E'. simpl in E'. lia. }
Qed.

Lemma fs_count q p n : p < q -> fs q (q+S p) n = C q p (n+S p).
Proof.
 intros Hp.
 destruct (Nat.eq_dec n 0) as [->|N].
 - unfold C. rewrite Nat.add_0_l, fs_q_0, count_nbocc.
   rewrite <- (@A_base q p lia), qprefix_A_qword, qword_low by lia.
   rewrite nbocc_notin; trivial. simpl. rewrite in_seq. lia.
 - apply LBound_Cqp; trivial. apply steiner_thm. lia.
Qed.

(** Application to letter 0 (espcially a different proof of f_count_0). *)

Lemma fs_count_0 q n : 0 < q -> fs q (S q) n = C q 0 (S n).
Proof.
 rewrite <- (Nat.add_1_r q), <- (Nat.add_1_r n). apply fs_count.
Qed.

Lemma f_count_0 q n : q <> 0 -> C q 0 n + f q n = n.
Proof.
 intros Q.
 destruct n; try easy.
 rewrite <- fs_count_0, f_S; generalize (fs_le q (S q) n); lia.
Qed.

Lemma Cq0_ge_CSq0 q n : C (S q) 0 n <= C q 0 n.
Proof.
 destruct (Nat.eq_dec q 0) as [->|Q].
 - unfold C. rewrite (count_all (qseq 0)). apply count_subid.
   intros m _. generalize (qseq_letters 0 m). lia.
 - generalize (f_count_0 q n Q) (f_count_0 (S q) n lia) (f_grows q n). lia.
Qed.


(** Application to letter 1 *)

Lemma fs_count_1 q n : 1 < q -> fs q (q+2) n = C q 1 (n+2).
Proof.
 apply fs_count.
Qed.

(** For 1<q, the previous conjecture fs q (q+2) n >= fs (q+1) (q+3) n
    hence implies:  C q 1 n >= C (S q) 1 n.
    (at least for 2<=q, and probably even 1<=q)
*)


(** Counting many letters at once : all the ones larger than some p.

    Qey idea here: for j <= q, [qnsub q j [i]] has only its first letter
    that is j or more.

    NB: [LBound_count_above] subsumes previous [LBound_Cqq] but we keep
    it for its simplificity.
 *)

Lemma qnsub_nbabove q p u : p <= q ->
  Forall (fun a : nat => a <= q) u ->
  nbabove p (qnsub q p u) = length u.
Proof.
 intros Hp.
 induction u as [|i u IH]; intros Hu.
 - unfold qnsub. now rewrite napply_nil.
 - inversion Hu; subst.
   rewrite (qnsub_app _ _ [i] u), nbabove_app, IH by trivial. clear IH Hu.
   rewrite qnsub_alt by trivial.
   case Nat.ltb_spec; intros; simpl.
   + case Nat.leb_spec; lia.
   + rewrite qword_low by lia. simpl.
     case Nat.leb_spec; intros; try lia.
     rewrite nbabove_0; try lia. apply Forall_forall.
     intro x. rewrite in_seq. lia.
Qed.

Lemma LBound_count_above q p c n : p <= q ->
 LBound q p n c -> c = count_above (qseq q) p n.
Proof.
 unfold LBound. intros Hn H.
 assert (c <> 0). { intros ->. simpl in *. rewrite !L_0 in H. lia. }
 replace c with (S (c-1)) in H at 2 by lia.
 rewrite L_S in H.
 assert (Hx := qseq_letters q (c-1)).
 set (x := qseq q (c-1)) in *.
 rewrite count_above_nbabove.
 assert (P := qnsub_prefixseq q p (S (c-1))).
 rewrite take_S, qnsub_app in P. fold x in P.
 unfold L in *. set (u := qnsub _ _ _) in *.
 assert (P' : Prefix (qprefix q n) (u++qnsub q p [x])).
 { eapply PrefixSeq_incl; eauto using qprefix_ok.
   rewrite qprefix_length, app_length. lia. }
 clear P. rename P' into P.
 rewrite qnsub_alt in * by trivial.
 destruct (Nat.ltb_spec (p+x) q).
 - simpl in H.
   destruct P as ([|],P).
   + rewrite app_nil_r in P. rewrite P, nbabove_app. simpl.
     case Nat.leb_spec; intros; try lia.
     unfold u. rewrite qnsub_nbabove; trivial using qprefix_letters.
     rewrite qprefix_length. lia.
   + apply (f_equal (@length _)) in P.
     rewrite !app_length, qprefix_length in P. simpl in P. lia.
 - rewrite qword_len, A_base, qword_low in * by lia.
   apply Prefix_app in P. destruct P as [P|(w & E & P)].
   + apply Prefix_len in P. rewrite qprefix_length in P. lia.
   + rewrite E, nbabove_app.
     unfold u. rewrite qnsub_nbabove; trivial using qprefix_letters.
     rewrite qprefix_length.
     apply Prefix_cons_inv in P. destruct P as [->|(w' & -> & P)].
     * rewrite app_nil_r in E. apply (f_equal (@length _)) in E.
       rewrite qprefix_length in E. lia.
     * simpl. case Nat.leb_spec; intros; try lia.
       rewrite nbabove_0; try lia.
       apply Forall_forall. intros y IN. apply Prefix_incl in P.
       specialize (P y IN). rewrite in_seq in P. lia.
Qed.

Lemma fs_count_above q p n : p <= q -> fs q p n = count_above (qseq q) p n.
Proof.
 intros P.
 destruct n.
 - now rewrite fs_q_0.
 - apply LBound_count_above; trivial. apply steiner_thm; lia.
Qed.

(** Hence the monotony results on fs also correspond to results on
    some ΣCqp. *)

(** C as difference between count_above *)

Lemma Cqp_diff_fs q p n : p < q -> C q p n = fs q p n - fs q (S p) n.
Proof.
 intros. unfold C. rewrite !fs_count_above, count_above_S; lia.
Qed.

Lemma Cqp_diff_bis q p n : p < q -> C q p n = fs q (S q) (fs q p n - 1).
Proof.
 intros. rewrite Cqp_diff_fs; trivial.
 rewrite <- (f_eqn_pred q (fs q p n)) at 1. rewrite <- Nat.sub_1_r.
 simpl. lia.
Qed.

(** Weird consequence (see also GenG.f_alt_eqn) *)

Lemma wierd_law q p n : p < q ->
   fs q (q+S p) n = fs q (S q) (fs q p (n+S p) - 1).
Proof.
 intros. rewrite <- Cqp_diff_bis; trivial. now apply fs_count.
Qed.


(** Galois connection : L is a right adjoint to f *)

Lemma L_f_galois q j n m : fs q j n <= m <-> n <= L q j m.
Proof.
 intros. destruct (Nat.eq_dec n 0) as [->|N].
 - rewrite fs_q_0; lia.
 - split; intros.
   + etransitivity. 2:apply incr_mono; eauto using L_incr.
     apply steiner_thm; lia.
   + rewrite <- (fs_L q j m). now apply fs_mono.
Qed.

Lemma LL_fsfs_le_iff q q' j j' n :
  L q j n <= L q' j' n <-> let m := L q j n in fs q' j' m <= fs q j m.
Proof.
 simpl. rewrite fs_L. split; intros; now apply L_f_galois.
Qed.

Lemma LL_fsfs_lt_iff q q' j j' n :
  L q j n < L q' j' n -> let m := L q' j' n in fs q' j' m < fs q j m.
Proof.
 rewrite !Nat.lt_nge. now rewrite LL_fsfs_le_iff.
Qed.

Lemma LL_fsfs_le_bis q q' j j' n :
 let m := fs q j n in L q j m <= L q' j' m -> fs q' j' n <= fs q j n.
Proof.
 simpl; intros H.
 destruct (Nat.eq_dec n 0) as [->|N].
 - now rewrite !fs_q_0.
 - apply L_f_galois. etransitivity; [|apply H]. apply steiner_thm; lia.
Qed.

Lemma fsfs_LL_lt q q' j j' n :
 fs q j n < fs q' j' n -> let m := fs q j n in L q' j' m < L q j m.
Proof.
 simpl. rewrite !Nat.lt_nge. intros H. contradict H.
 now apply LL_fsfs_le_bis.
Qed.

Definition pointwise_le (f1 f2 : nat -> nat) := forall n, f1 n <= f2 n.

Infix "[<=]" := pointwise_le (at level 70, no associativity).

Lemma L_f_dual q q' j j' : fs q j [<=] fs q' j' <-> L q' j' [<=] L q j.
Proof.
 split; intros H n. now apply LL_fsfs_le_iff. now apply LL_fsfs_le_bis.
Qed.

(** L at n=1 *)

Lemma Lqj1_A q j : L q j 1 = A q j.
Proof.
 now rewrite L_S, L_0, qnsub_qword, qword_len, qseq_q_0.
Qed.

Lemma Lqj1_diag_decr_ultimately q j :
  2*q+3 < j -> L (S q) (S j) 1 < L q j 1.
Proof.
 intros J. rewrite !Lqj1_A. now apply A_diag_decr.
Qed.

Lemma L_diag_nle_ultimately q j :
  2*q+3 < j -> ~(L q j [<=] L (S q) (S j)).
Proof.
 intros J LE. specialize (LE 1). apply Lqj1_diag_decr_ultimately in J. lia.
Qed.

Lemma L_diag_decr_gen q j p :
 q+3 <= j -> 2*q+4 <= p+j -> p <= q+1 ->
 L (S q) (S j) (S p) < L q j (S p).
Proof.
 intros J PJ P.
 rewrite <- (@A_base (S q) p) at 1 by lia.
 rewrite <- (@A_base q p) by lia.
 rewrite <- !Lqj1_A, !L_add, Nat.add_succ_l.
 apply Lqj1_diag_decr_ultimately. lia.
Qed.

Lemma L_diag_decr_example q j :
 q+3 <= j -> let p := 2*q+4-j in L (S q) (S j) (S p) < L q j (S p).
Proof.
 intros J p. unfold p. apply L_diag_decr_gen; lia.
Qed.

Lemma L_diag_decr_example_qp3 q :
 L (S q) (q+4) (q+2) < L q (q+3) (q+2).
Proof.
 replace (q+2) with (S (2*q+4-(q+3))) by lia.
 replace (q+4) with (S (q+3)) by lia.
 now apply L_diag_decr_example.
Qed.

Lemma L_diag_incr_example q j : j <= 2*q+2 -> L q j 1 < L (S q) (S j) 1.
Proof.
 intros. rewrite !Lqj1_A, A_diag_step; lia.
Qed.

Lemma fs_diag_incr_example q j :
 q+3 <= j -> let p := L q j (S (2*q+4-j)) in
 fs q j p < fs (S q) (S j) p.
Proof.
 intros J p. unfold p. apply LL_fsfs_lt_iff.
 now apply L_diag_decr_example.
Qed.

Lemma fs_diag_incr_example_qp3 q :
 let p := L q (q+3) (q+2) in
 fs q (q+3) p < fs (S q) (q+4) p.
Proof.
 replace (q+2) with (S (2*q+4-(q+3))) by lia.
 replace (q+4) with (S (q+3)) by lia.
 now apply fs_diag_incr_example.
Qed.

Lemma fs_diag_decr_example q j :
 j <= 2*q+2 -> let p := L (S q) (S j) 1 in
 fs (S q) (S j) p < fs q j p.
Proof.
 intros J p. unfold p. apply LL_fsfs_lt_iff.
 now apply L_diag_incr_example.
Qed.

(** For letters [2<=i<q], [C q i] and [C (q+1) i] are uncomparable. *)

Lemma C_diag_incr_example q i :
 2 <= i < q ->
 let n := L q (2*q+4) 1 + S i in
 C q i n < C (S q) i n.
Proof.
 intros Hi n. unfold n. rewrite <- !fs_count by lia.
 rewrite (Nat.add_succ_l q).
 set (j := q + S i).
 replace (L q (2*q+4) 1) with (L q j (S (2*q+4-j))).
 2:{ replace (2*q+4) with (j + (q+3-i)) by lia.
     rewrite <- L_add. f_equal. rewrite Lqj1_A, A_base; lia. }
 apply fs_diag_incr_example; lia.
Qed.

Lemma C_diag_decr_example q i :
 2 <= i < q ->
 let n := L (S q) (2+q+i) 1 + S i in
 C (S q) i n < C q i n.
Proof.
 intros Hi n. unfold n. rewrite <- !fs_count by lia.
 rewrite (Nat.add_succ_l q).
 set (j := q + S i). replace (2+q+i) with (S j) by lia.
 apply fs_diag_decr_example; lia.
Qed.


(** Bacq to [Lq_LSq], large inequalities, decreasing [j].
    USELESS THEOREM actually, since
    - concl already proved for j <= q+1
    - hyp false for j >= q+2 (cf L_diag_decr_gen)
 *)

Lemma Lq_LSq_again q j :
 L q (S j) [<=] L (S q) (S (S j)) ->
 L q j [<=] L (S q) (S j).
Proof.
 intros H n.
 induction n as [n IH] using lt_wf_ind.
 destruct n; try now rewrite !L_0.
 destruct (Nat.eq_dec (qseq (S q) n) (S q)) as [E|N].
 + rewrite !L_S, E.
   rewrite qnsub_qword, qword_len.
   assert (Hx := qseq_letters q n).
   set (x := qseq q n) in *.
   rewrite qnsub_len by trivial.
   apply Nat.add_le_mono.
   * apply IH; lia.
   * transitivity (A q j); [apply A_mono; lia|].
     assert (S j <= 2*q+3).
     { apply Nat.le_ngt. intros J. now apply L_diag_nle_ultimately in J. }
     generalize (@A_diag_step q j) (@A_diag_eq q j). lia.
 + destruct (qsubst_prefix_inv (S q) (qprefix (S q) (S n)))
     as (v & w & Hv & E & Hw); try apply qprefix_ok.
   destruct Hw as [-> | ->].
   2:{ rewrite take_S in Hv; apply app_inv' in Hv; trivial.
       destruct Hv as (_,[= E']); lia. }
   rewrite app_nil_r in Hv.
   red in E.
   set (l := length v) in *.
   assert (E' : L (S q) 1 l = S n).
   { now rewrite <- (qprefix_length (S q) (S n)), Hv, E. }
   assert (Hl0 : l <> 0). { intros ->. now rewrite L_0 in E'. }
   assert (Hl : l < S n).
   { rewrite <- E'. rewrite Lq1_Cqq.
       generalize (Cqq_nz (S q) l). lia. }
   specialize (IH l Hl).
   assert (IH5 := Lq1_ge_LSq1 q l). rewrite E' in IH5.
   rewrite <- E' at 2.
   rewrite L_add. rewrite Nat.add_1_r.
   etransitivity; [|apply H; lia].
   rewrite <- (Nat.add_1_r j), <- L_add. apply incr_mono; trivial.
   apply L_incr.
Qed.

Lemma f_L_conjectures q :
 (forall m, quad (S q) < m -> f (S q) m < f (S (S q)) m) ->
 (forall m, quad q < m -> L (S (S q)) 1 m < L (S q) 1 m).
Proof.
 intros H m Hm.
 red in Hm.
 apply Nat.le_lteq in Hm. destruct Hm as [Hm|<-].
 - apply (incr_strmono (L (S q) 1)) in Hm. 2:apply L_incr.
   rewrite L_q_1_rchild, rchild_Sq_Squad in Hm.
   rewrite Nat.lt_nge, LL_fsfs_le_iff, <- Nat.lt_nge.
   apply H. lia.
 - rewrite !L_q_1_rchild. rewrite rchild_SSq_Squad, rchild_Sq_Squad. lia.
Qed.

(* Recip ??
 (forall m, quad q < m -> L (S (S q)) 1 m < L (S q) 1 m) ->
 (forall m, quad (S q) < m -> f (S q) m < f (S (S q)) m).
*)

Lemma L11_le_2np3 n : L 1 1 (n+2) <= 2*n+3.
Proof.
 induction n as [|n IH]; simpl; try easy.
 rewrite L_S. unfold qnsub. simpl. unfold qsubst.
 destruct Nat.eqb; simpl; lia.
Qed.

Lemma L11_lt_2n n : 2 <= n -> L 1 1 n < 2*n.
Proof.
 intros. replace n with (n-2+2) by lia. generalize (L11_le_2np3 (n-2)). lia.
Qed.

Lemma f_L_conjectures_bis q :
 (forall m, quad q < m -> f q m < f (S q) m) ->
 (forall m, quad (q-1) < m -> L (S q) 1 m < L q 1 m).
Proof.
 intros H m Hm.
 destruct q.
 - simpl in Hm. rewrite L_0_1. apply L11_lt_2n. compute in Hm. lia.
 - replace (S q -1) with q in Hm by lia.
   apply f_L_conjectures; auto.
Qed.

(** More about L at n=1 *)

Lemma L_q_2q_1 q : L q (2*q) 1 = triangle (q+1).
Proof.
 rewrite Lqj1_A. replace (2*q) with (q+q) by lia.
 rewrite A_triangle by lia.
 rewrite Nat.add_1_r, triangle_succ. lia.
Qed.

Lemma L_q_2q1_1 q : L q (2*q+1) 1 = triangle (q+2) - 1.
Proof.
 rewrite Lqj1_A. replace (2*q+1) with (q+(q+1)) by lia.
 rewrite A_triangle by lia.
 rewrite (Nat.add_succ_r q 1), triangle_succ. lia.
Qed.

Lemma L_q_2q2_1 q : L q (2*q+2) 1 = triangle (q+3) - 2.
Proof.
 rewrite Lqj1_A. replace (2*q+2) with (q+(q+2)) by lia.
 rewrite A_triangle by lia.
 rewrite (Nat.add_succ_r q 2), triangle_succ. lia.
Qed.

Lemma L_q_2q3_1 q : L q (2*q+3) 1 = triangle (q+4) - 2.
Proof.
 rewrite Lqj1_A. apply A_2q3_tri.
Qed.

Lemma L_q_q2_q1 q : L q (q+2) (q+1) = triangle (q+3) - 2.
Proof.
 rewrite Nat.add_1_r.
 rewrite <- (@A_base q q), <- Lqj1_A by lia.
 rewrite L_add, <- L_q_2q2_1. f_equal. lia.
Qed.

Lemma L_q_q2_q2 q : L q (q+2) (q+2) = triangle (q+4) - 2.
Proof.
 rewrite (Nat.add_succ_r q 1) at 2.
 rewrite <- (@A_base q (q+1)), <- Lqj1_A by lia.
 rewrite L_add, <- L_q_2q3_1. f_equal. lia.
Qed.

Lemma L_equality q : L q (q+2) (q+2) = L (q+1) (q+3) (q+2).
Proof.
 rewrite L_q_q2_q2.
 replace (q+4) with (q+1+3) by lia.
 rewrite <- L_q_q2_q1. f_equal; lia.
Qed.

Definition cex q j := S (2*q+4-j).

Lemma cex_spec q j :
  q+3 <= j ->
  L (S q) (S j) (cex q j) < L q j (cex q j).
Proof.
 intros Hj.
 destruct (Nat.le_gt_cases (2*q+4) j) as [Hj'|Hj'].
 - unfold cex. replace (2*q+4-j) with 0 by lia.
   rewrite !Lqj1_A. apply A_diag_decr. lia.
 - unfold cex. set (p := 2*q+4-j) in *.
   rewrite <- (@A_base q p) at 2 by lia. rewrite <- Lqj1_A, L_add, Lqj1_A.
   replace (j+p) with (2*q+4) by lia.
   rewrite <- (@A_base (S q) p) by lia. rewrite <- Lqj1_A, L_add, Lqj1_A.
   replace (S j+p) with (S (2*q+4)) by lia.
   apply A_diag_decr. lia.
Qed.

Lemma cex_spec' q j :
  q+3 <= j ->
  let m := L q j (cex q j) in
  fs q j m < fs (S q) (S j) m.
Proof.
 intros Hj. apply LL_fsfs_lt_iff. now apply cex_spec.
Qed.
