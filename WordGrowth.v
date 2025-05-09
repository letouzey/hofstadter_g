Require Import MoreTac MoreFun MoreList DeltaList FunG GenFib GenG Words.
Import ListNotations.

(** * WordGrowth *)

(** Follow-up of [Words.v] dedicated to the study of positions
    of some letters in the infinite words [(kseq k)].
    Applications :
    - the count of letter (k-1) decreases with k
    - the count of letter 0 decreases with k
    - for all point n, [f k n <= f (S k) n]. *)

(** [knsub] : a shortcut for repeated application of [ksubst] *)

Definition knsub k j : word -> word := napply (ksubst k) j.

Lemma knsub_app k j u v : knsub k j (u++v) = knsub k j u ++ knsub k j v.
Proof.
 apply napply_app.
Qed.

Lemma knsub_prefixseq_gen k j w :
  PrefixSeq w (kseq k) -> PrefixSeq (knsub k j w) (kseq k).
Proof.
 intros.
 apply PrefixSeq_napply; trivial using ksubst_noerase, ksubst_prolong.
Qed.

Lemma knsub_prefixseq k j n : PrefixSeq (knsub k j (kprefix k n)) (kseq k).
Proof.
 apply knsub_prefixseq_gen, kprefix_ok.
Qed.

Lemma knsub_kword_gen k j n :
  n < k -> k-1 <= j+n -> knsub k j [n] = kword k (j+n-(k-1)).
Proof.
 intros. unfold knsub. now apply napply_ksubst_is_kword.
Qed.

Lemma knsub_kword k j : 0<k -> knsub k j [k-1] = kword k j.
Proof.
 intros. rewrite knsub_kword_gen; f_equal; lia.
Qed.

Lemma knsub_alt k j n :
  n < k -> knsub k j [n] = if j+n <? k-1 then [j+n] else kword k (j+n-(k-1)).
Proof.
 case Nat.ltb_spec; intros.
 - unfold knsub. rewrite napply_ksubst_shift; f_equal; lia.
 - apply knsub_kword_gen; lia.
Qed.

Lemma knsub_len k j n : n < k -> length (knsub k j [n]) = A k (j+n-(k-1)).
Proof.
 intros. rewrite knsub_alt by trivial.
 case Nat.ltb_spec; intros; simpl; try apply kword_len.
 replace (j+n-(k-1)) with 0 by lia. trivial.
Qed.

Lemma knsub_km1_alt k n : n < k -> knsub k (k-1) [n] = kword k n.
Proof.
 intros. rewrite knsub_kword_gen; f_equal; lia.
Qed.

Lemma knsub_k_alt k n : n < k -> knsub k k [n] = kword k (S n).
Proof.
 intros. rewrite knsub_kword_gen; f_equal; lia.
Qed.

Lemma knsub_km1_len k n : n < k -> length (knsub k (k-1) [n]) = S n.
Proof.
 intros. rewrite knsub_len, A_base; lia.
Qed.

Lemma knsub_k_len k n : n < k -> length (knsub k k [n]) = 2+n.
Proof.
 intros. rewrite knsub_len, A_base; lia.
Qed.

Lemma knsub_len_low k j : j <= k -> length (knsub k j [k-1]) = j+1.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - intros Hj. now replace j with 0 by lia.
 - intros. rewrite knsub_len, A_base; try lia.
Qed.

Lemma knsub_len_le k j n : n < k -> length (knsub k j [n]) <= A k j.
Proof.
 intros. rewrite knsub_len by trivial. apply A_mono. lia.
Qed.

(** Fun fact: for n < k, ksubst^(k-1)(n) = ksubst^n(k-1) *)

Lemma knsub_pearl k n : n < k -> knsub k (k-1) [n] = knsub k n [k-1].
Proof.
 intros. rewrite !knsub_alt by lia. now rewrite (Nat.add_comm (k-1) n).
Qed.


(** [L] : length of the repeated expansion of a kseq prefix.
    Right adjoint of [f]. *)

Definition L k j n := length (knsub k j (kprefix k n)).

Lemma L_0 k j : L k j 0 = 0.
Proof.
 unfold L, knsub. cbn. now rewrite napply_nil.
Qed.

Lemma L_S k j n : L k j (S n) = L k j n + length (knsub k j [kseq k n]).
Proof.
 unfold L. now rewrite take_S, knsub_app, app_length.
Qed.

Lemma L_incr k j : IncrFun (L k j).
Proof.
 intro n. rewrite L_S.
 generalize (@napply_mono _ 0 j [kseq k n] (ksubst_noerase k)).
 unfold knsub. simpl. lia.
Qed.

Lemma L_lt k j n m : n < m <-> L k j n < L k j m.
Proof.
 apply incr_strmono_iff. apply L_incr.
Qed.

Lemma L_add k i j n : L k i (L k j n) = L k (i+j) n.
Proof.
 unfold L. f_equal.
 generalize (knsub_prefixseq k j n). unfold PrefixSeq. intros <-.
 unfold knsub. symmetry. apply napply_add.
Qed.

Lemma L_k_0 k n : L k 0 n = n.
Proof.
 unfold L, knsub. simpl. apply kprefix_length.
Qed.

Lemma L_iter k j n : L k j n = ((L k 1)^^j) n.
Proof.
 revert n. induction j; simpl; intros.
 - apply L_k_0.
 - now rewrite <- IHj, L_add.
Qed.

Lemma L_ge_n k j n : n <= L k j n.
Proof.
 revert n.
 assert (H : forall n, n <= L k 1 n).
 { intros n. unfold L, knsub. simpl.
   rewrite <- (kprefix_length k n) at 1.
   apply apply_grow, ksubst_noerase. }
 induction j; intros.
 - cbn. now rewrite kprefix_length.
 - change (S j) with (1+j). rewrite <- L_add.
   transitivity (L k j n); trivial.
Qed.

Lemma L_mono_j k j j' n : j <= j' -> L k j n <= L k j' n.
Proof.
 intros. replace j' with ((j'-j)+j) by lia. rewrite <- L_add. apply L_ge_n.
Qed.

Lemma L_gt_n k j n : 0<j -> 0<n -> n < L k j n.
Proof.
 revert n.
 assert (H : forall n, 0<n -> n < L k 1 n).
 { intros n Hn. unfold L, knsub. simpl.
   destruct n; try easy. cbn. rewrite app_length.
   set (w := map _ _).
   assert (n <= length (apply (ksubst k) w)).
   { replace n with (length w)
      by (unfold w; now rewrite map_length, seq_length).
     apply apply_grow, ksubst_noerase. }
   rewrite ksubst_km1. simpl. lia. }
 induction j; intros; try easy.
 destruct j. now apply H.
 change (S (S j)) with (1+S j). rewrite <- L_add.
 apply Nat.lt_le_trans with (L k (S j) n). apply IHj; lia.
 apply L_ge_n.
Qed.

Lemma L_strmono_j k j j' n : 0 < n -> j < j' -> L k j n < L k j' n.
Proof.
 intros. replace j' with ((j'-j)+j) by lia. rewrite <- L_add. apply L_gt_n.
 lia. apply Nat.lt_le_trans with n; trivial. apply L_ge_n.
Qed.

Lemma L_01_1 k n : k<=1 -> L k 1 n = 2*n.
Proof.
 intros K.
 induction n; try easy.
 rewrite L_S, IHn. cbn. unfold ksubst. rewrite kseq_01 by easy.
 replace (k-1) with 0 by lia. simpl. lia.
Qed.

Lemma knsub_kprefix k j n : knsub k j (kprefix k n) = kprefix k (L k j n).
Proof.
 apply knsub_prefixseq.
Qed.

(** Steiner's Theorem : direct linq between f and kseq *)

Definition LBound k j n m := L k j (m-1) < n <= L k j m.

Definition SteinerThm k j n := 0<n -> LBound k j n (fs k j n).

Lemma steiner_thm_k1_j1 n : SteinerThm 1 1 n.
Proof.
 intros Hn. red. rewrite !L_01_1; trivial. simpl fs.
 induction n.
 - inversion Hn.
 - rewrite f_S. simpl fs.
   destruct (Nat.eq_dec n 0) as [->|N]; [simpl; lia | lia].
Qed.

Lemma steiner_thm_disj k n :
  LBound k 1 n (f k n) -> L k 1 (f k n) = n \/ kseq k n = 0.
Proof.
  unfold LBound. intros IH1.
  destruct (Nat.eq_dec n 0) as [->|N]; [now left|].
  generalize (knsub_prefixseq k 1 (f k n)).
  revert IH1.
  replace (f k n) with (S (f k n - 1)) at 2 3 4
    by (generalize (@f_nonzero k n); lia).
  rewrite L_S. unfold L.
  rewrite take_S, knsub_app. unfold PrefixSeq. rewrite app_length.
  set (w := knsub k 1 (kprefix k (f k n - 1))).
  set (x := kseq _ _) in *.
  unfold knsub. simpl. rewrite app_nil_r.
  unfold ksubst. case Nat.eqb; intros W0 W; simpl in *; try lia.
  destruct (Nat.eq_dec (length w) (n-1)) as [W'|W']; try lia.
  right. rewrite W' in W.
  rewrite Nat.add_succ_r, Nat.add_1_r in W.
  rewrite !take_S, <- app_assoc in W. simpl in W.
  apply app_inv' in W; try easy.
  destruct W as (_,[= _ ->]). f_equal. lia.
Qed.

Lemma steiner_thm_corestep k n : 0<k -> 2<=n ->
  (forall j, SteinerThm k j (n-1)) ->
  (forall j, SteinerThm k j n) ->
  SteinerThm k 1 (S n).
Proof.
 intros K Hn IHn1 IHn.
 (* Case k=1 must be handled separately (but it's easy, L is double) *)
 destruct (Nat.eq_dec k 1) as [->|Hq]; [ apply steiner_thm_k1_j1 | ].
 assert (Hn' : S (n-1) = n) by lia.
 destruct (fs_step k k (n-1)) as [E|E]; rewrite Hn' in E.
 - (* First case : f^^k flat at (n-1) *)
   destruct (steiner_thm_disj k n (IHn 1 lia)) as [EQ|EQ].
   + intros _. simpl. clear IHn1 IHn.
     replace (f k (S n)) with (S (f k n)).
     2:{ rewrite <- Hn' at 1. rewrite !f_S, E.
         generalize (fs_le k k (n-1)). lia. }
     unfold LBound. simpl. rewrite Nat.sub_0_r, L_S, EQ.
     unfold knsub. simpl. unfold ksubst. case Nat.eqb; simpl; lia.
   + exfalso.
     specialize (IHn k lia). destruct IHn as (_,IHn).
     apply Nat.le_lteq, or_comm in IHn. destruct IHn as [IHn|IHn].
     * clear IHn1.
       set (m := fs k k n) in *.
       generalize (knsub_prefixseq k k (S m)).
       generalize (knsub_prefixseq k k m).
       rewrite take_S, knsub_app. unfold PrefixSeq. rewrite app_length.
       unfold L in IHn. rewrite <- IHn. intros ->. clear IHn.
       assert (Hx := kseq_letters k m).
       set (x := kseq k m) in *.
       rewrite knsub_k_len, knsub_k_alt, kword_low by lia.
       rewrite take_add.
       intros W. apply app_inv_head in W. simpl in W.
       injection W as W _ _. lia.
     * specialize (IHn1 k lia). destruct IHn1 as (IHn1,_).
       rewrite <- E in IHn1.
       set (m := fs k k n - 1) in *.
       replace (fs _ _ _) with (S m) in IHn.
       2:{ unfold m. generalize (@fs_nonzero k n k); lia. }
       rewrite L_S in IHn.
       generalize (knsub_prefixseq k k (S m)).
       generalize (knsub_prefixseq k k m).
       rewrite take_S, knsub_app. unfold PrefixSeq. rewrite app_length.
       assert (Hx := kseq_letters k m).
       set (x := kseq k m) in *.
       rewrite knsub_k_len, knsub_k_alt, kword_low in * by lia.
       fold (L k k m). set (lm := L k k m) in *. intros ->.
       simpl. rewrite take_add.
       intros W. apply app_inv_head in W. simpl in W.
       injection W as _ _ W.
       assert (IN : In 0 (seq 1 x)).
       { rewrite W, <- EQ. apply in_map, in_seq. lia. }
       apply in_seq in IN. lia.
 - (* Second case : f^^k step at (n-1) *)
   intros _. simpl. replace (f k (S n)) with (f k n).
   2:{ rewrite <- Hn' at 1.
       rewrite !f_S, E. generalize (fs_le k k (n-1)). lia. }
   split; [ apply Nat.lt_lt_succ_r, (IHn 1); lia| ].
   assert (E' : f k n = S (f k (n-1))).
   { destruct (f_step k (n-1)) as [E'|E']; rewrite Hn' in *; trivial.
     exfalso.
     replace (fs k k) with (fs k (S (k-1))) in E by (f_equal; lia).
     rewrite !iter_S, <- E' in E; lia. }
   rewrite E', L_S.
   assert (HL : L k 1 (f k (n-1)) = n-1).
   { destruct (IHn1 1 lia) as (_,LB).
     destruct (IHn 1 lia) as (UB,_).
     simpl in LB,UB. rewrite E' in UB.
     simpl in UB. rewrite Nat.sub_0_r in *. lia. }
   rewrite HL.
   assert (HL' : L k k (fs k k (n-1)) = n-1).
   { destruct (IHn1 k lia) as (_,LB).
     destruct (IHn k lia) as (UB,_).
     rewrite E in UB. simpl in *. rewrite Nat.sub_0_r in *. lia. }
   clear IHn1 IHn.
   assert (EL := knsub_prefixseq k 1 (f k (n-1))).
   assert (EL' := knsub_prefixseq k k (fs k k (n-1))).
   red in EL,EL'. unfold L in HL,HL'. rewrite HL,HL' in *. clear HL HL'.
   assert (H : kseq k (n-1) = k-1 /\ kseq k n = 0).
   { generalize (knsub_prefixseq k k (fs k k n)).
     rewrite E, take_S, knsub_app, EL'.
     assert (Hx := kseq_letters k (fs k k (n-1)) lia).
     set (x := kseq _ _) in *.
     unfold PrefixSeq. rewrite app_length, kprefix_length, take_add.
     rewrite knsub_k_len, knsub_k_alt, kword_low by lia.
     simpl. rewrite Hn'.
     intro V. apply app_inv_head in V. now injection V as <- <- _. }
   destruct H as (H1,H2).
   generalize (knsub_prefixseq k 1 (S (f k n))).
   rewrite E', 2 take_S, !knsub_app, EL. clear E E' EL EL'.
   set (x := kseq k (f k (n-1))).
   set (y := kseq k (S _)). clearbody x y.
   unfold knsub. simpl. rewrite !app_nil_r. unfold PrefixSeq.
   rewrite !app_length, kprefix_length, <- Nat.add_assoc, <- app_assoc.
   rewrite take_add.
   intros V. apply app_inv_head in V. revert V.
   unfold ksubst.
   case Nat.eqb. intros _; simpl; lia.
   case Nat.eqb; simpl; rewrite Hn'; injection 1; lia.
Qed.

Lemma steiner_thm k j n : 0<k -> 0 < n -> LBound k j n (fs k j n).
Proof.
 intros K. change (SteinerThm k j n).
 revert j. induction n as [n IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases n 2) as [Hn|Hn].
 - destruct n as [|[|[|n]]]; try lia.
   + (* n=0 *) inversion 1.
   + (* n=1 *)
     intros j _. unfold LBound. rewrite fs_k_1, L_0. auto using L_ge_n.
   + (* n=2 *)
     intros [|j] _; unfold LBound.
     * simpl. rewrite !L_k_0. lia.
     * rewrite fs_k_2, L_0 by lia. split; auto. apply L_gt_n; lia.
 - destruct n; try lia.
   assert (J1 : SteinerThm k 1 (S n)).
   { apply steiner_thm_corestep; try apply IH; lia. }
   intros [|j].
   + (* j=0 *)
     intros _. unfold LBound. rewrite !L_k_0. cbn. lia.
   + (* j<>0 *)
     assert (FS : f k (S n) < S n) by (apply f_lt; lia).
     assert (FS0 : 0 < f k (S n)) by (apply f_nonzero; lia).
     specialize (IH (f k (S n)) FS j FS0).
     rewrite <- iter_S in IH.
     destruct IH as (IH1,IH2). apply Nat.lt_le_pred in IH1.
     rewrite <- Nat.sub_1_r in IH1.
     apply (incr_mono _ (L_incr k 1)) in IH1,IH2.
     rewrite L_add in IH1, IH2. simpl "+" in IH1,IH2.
     unfold SteinerThm, LBound in *. simpl in J1. lia.
Qed.

Lemma LBound_unique k j m n n' : LBound k j m n -> LBound k j m n' -> n=n'.
Proof.
 unfold LBound; intros.
 assert (n'-1 < n) by (apply (incr_strmono_iff _ (L_incr k j)); lia).
 assert (n-1 < n') by (apply (incr_strmono_iff _ (L_incr k j)); lia).
 lia.
Qed.

Lemma steiner_thm_iff k j n m :
  0<k -> 0<n -> fs k j m = n <-> LBound k j m n.
Proof.
 intros K Hn.
 split.
 - intros <-. apply steiner_thm; trivial.
   destruct m; try lia. now rewrite fs_k_0 in *.
 - intros.
   apply (LBound_unique k j m); trivial.
   apply steiner_thm; trivial. unfold LBound in *. lia.
Qed.

(** Said otherwise, [L k j n] is the largest antecedent of [n] by [fs k j],
    and [S (L k j n)] is the least antecedent of [S n]. *)

Lemma fs_L k j n : 0<k -> fs k j (L k j n) = n.
Proof.
 intros K. destruct n.
 - now rewrite L_0, fs_k_0.
 - apply steiner_thm_iff; try lia. split; trivial. apply L_lt; lia.
Qed.

Lemma fs_S_L k j n : 0<k -> fs k j (S (L k j n)) = S n.
Proof.
 intros K. apply steiner_thm_iff; try lia. split.
 - fixpred. lia.
 - apply L_lt; lia.
Qed.

Lemma fs_rightmost_child_carac k j a n :
  0<k -> fs k j n = a -> fs k j (S n) = S a <-> n = L k j a.
Proof.
 intros K. destruct (Nat.eq_dec a 0) as [->|Ha]; intros E.
 - apply fs_0_inv in E. subst n. now rewrite fs_k_1, L_0.
 - split; intros E'.
   + apply steiner_thm_iff in E, E'; try lia. unfold LBound in *.
     replace (S a - 1) with a in *; lia.
   + rewrite E'. now apply fs_S_L.
Qed.

Lemma L_k_1_rchild k n : L k 1 n = rchild k n.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - rewrite L_01_1 by lia. unfold rchild. simpl. lia.
 - rewrite <- rightmost_child_carac; try lia.
   apply (fs_S_L k 1); lia. apply (fs_L k 1); lia.
Qed.

(** Exactly enumerating antecedents of [fs k j], in increasing order *)

Definition fsinv k j n :=
  if n =? 0 then [0]
  else
    let a := L k j (n-1) in
    let b := L k j n in
    seq (S a) (b-a).

Lemma fsinv_spec k j n m : 0<k -> In m (fsinv k j n) <-> fs k j m = n.
Proof.
 intros K. unfold fsinv.
 case Nat.eqb_spec; [intros ->|intros Hn].
 - split; simpl.
   + intros [<-|[ ]]. apply fs_k_0.
   + generalize (@fs_nonzero k m j). lia.
 - rewrite in_seq, steiner_thm_iff; unfold LBound; lia.
Qed.

Lemma fsinv_delta1 k j n : Delta 1 (fsinv k j n).
Proof.
 unfold fsinv. case Nat.eqb. constructor. apply Delta_seq.
Qed.

Lemma fsinv_nodup k j n : NoDup (fsinv k j n).
Proof.
 eapply Delta_NoDup, fsinv_delta1.
Qed.

Lemma fsinv_S_length k j n :
  length (fsinv k j (S n)) = length (knsub k j [kseq k n]).
Proof.
 unfold fsinv. simpl. rewrite Nat.sub_0_r, L_S, seq_length. lia.
Qed.

Lemma fsinv_length k j n :
  length (fsinv k j n) =
  match n with 0 => 1 | S n => length (knsub k j [kseq k n]) end.
Proof.
 unfold fsinv. destruct n; simpl; trivial. now rewrite <- fsinv_S_length.
Qed.

Lemma fsinv_bound k j n : 0<k -> 0<n ->
  A k (j-(k-1)) <= length (fsinv k j n) <= A k j.
Proof.
 intros K. destruct n; try easy. intros _.
 rewrite fsinv_S_length.
 set (x := kseq k n).
 assert (Hx : x < k) by (apply kseq_letters; lia).
 rewrite knsub_len by trivial. split; apply A_mono; lia.
Qed.

(** For each k and j, these bounds are reached infinitely often when n vary.
    For instance : *)

Lemma fsinv_1 k j : 0<k -> length (fsinv k j 1) = A k j.
Proof.
 intros K. rewrite fsinv_S_length, kseq_k_0, knsub_len; f_equal; lia.
Qed.

Lemma fsinv_2 k j : 0<k -> length (fsinv k j 2) = A k (j-(k-1)).
Proof.
 intros K. rewrite fsinv_S_length, kseq_k_1, knsub_len; f_equal; lia.
Qed.


(** Streiner's second theorem :
    Monotony statements about [L k j] when k varies,
    and application to monotony of [fs] and [f].
    Inspired by an earlier proof by Shuo Li. *)

Local Notation C k i n := (count (kseq k) i n).

Lemma Ckkm1_nz k n : 0 < n -> 0 < C k (k-1) n.
Proof.
 unfold C.
 induction n.
 - lia.
 - intros _. destruct n; simpl in *; try lia.
   rewrite kseq_k_0, Nat.eqb_refl. lia.
Qed.

Lemma Lk1_Ckkm1 k n : L k 1 n = n + C k (k-1) n.
Proof.
 induction n; [easy|].
 rewrite L_S, IHn. unfold C. cbn. unfold ksubst.
 case Nat.eqb; simpl; lia.
Qed.

Lemma steiner_trick k n : (* with additions instead of subtractions *)
  k<>0 -> L (S k) (S k) n + L k (k-1) n = L (S k) k n + L k k n.
Proof.
 intro K.
 induction n.
 - now rewrite !L_0.
 - rewrite !L_S.
   replace (knsub (S k) k) with (knsub (S k) (S k-1)) by (f_equal; lia).
   rewrite !knsub_k_len, !knsub_km1_len by (apply kseq_letters; lia).
   lia.
Qed.

Lemma knsub_km1_nbocc k u :
  Forall (fun a : nat => a < k) u ->
  nbocc (k-1) (knsub k (k-1) u) = length u.
Proof.
 induction u as [|i u IH]; intros Hu.
 - unfold knsub. now rewrite napply_nil.
 - inversion Hu; subst.
   rewrite (knsub_app _ _ [i] u), nbocc_app, IH by trivial. clear IH.
   rewrite knsub_km1_alt by trivial.
   rewrite kword_low by lia. simpl. rewrite Nat.eqb_refl.
   rewrite nbocc_notin; rewrite ?in_seq; lia.
Qed.

Lemma LBound_Ckkm1 k n m :
  0<k -> 0<n -> LBound k (k-1) n m -> m = C k (k-1) n.
Proof.
 unfold LBound. intros K Hn H.
 assert (m <> 0). { intros ->. simpl in *. rewrite !L_0 in H. lia. }
 replace m with (S (m-1)) in H at 2 by lia.
 rewrite L_S in H.
 assert (Hx := kseq_letters k (m-1) lia).
 set (x := kseq k (m-1)) in *.
 unfold C. rewrite count_nbocc.
 assert (P := knsub_prefixseq k (k-1) (S (m-1))).
 rewrite !take_S, !knsub_app in P. fold x in P.
 rewrite knsub_km1_alt in * by trivial.
 set (u := knsub _ _ _) in *.
 change (L k (k-1) (m-1)) with (length u) in H.
 assert (P' : Prefix (kprefix k n) (u++kword k x)).
 { eapply PrefixSeq_incl; eauto using kprefix_ok.
   rewrite kprefix_length, app_length; lia. }
 clear P. rename P' into P.
 apply Prefix_app in P. destruct P as [P|(v & E & P)].
 { apply Prefix_len in P. rewrite kprefix_length in P. lia. }
 rewrite E, nbocc_app. unfold u.
 rewrite knsub_km1_nbocc, kprefix_length by (apply kprefix_letters; lia).
 rewrite kword_low in P by lia.
 apply Prefix_cons_inv in P. destruct P as [->|(w & E' & P)].
 { apply (f_equal (@length _)) in E.
   rewrite kprefix_length, app_nil_r in E. lia. }
 { rewrite E'. simpl. rewrite Nat.eqb_refl. rewrite nbocc_notin; try lia.
   intro IN. apply Prefix_incl in P. specialize (P _ IN).
   rewrite in_seq in P. lia. }
Qed.

(* NB: already in Words, via a different proof *)

Lemma fs_count_km1 k n : fs k (k-1) n = C k (k-1) n.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { simpl. symmetry. apply count_all. intros m _. apply kseq_01; lia. }
 destruct (Nat.eq_dec n 0) as [->|N].
 { now rewrite fs_k_0. }
 apply LBound_Ckkm1; try lia. apply steiner_thm; lia.
Qed.

Lemma Lk_LSk k n : 0<k ->
 L (S k) 1 n <= L k 1 n
 /\ (0<n -> forall j, j<=k -> L k j n < L (S k) (S j) n).
Proof.
 intros K. induction n as [n IH] using lt_wf_ind.
 destruct (Nat.eq_dec n 0) as [->|N0]; [easy|].
 destruct (Nat.eq_dec n 1) as [->|N1].
 { clear N0 IH. split; intros;
   rewrite !L_S, !L_0, !kseq_k_0, !knsub_kword, !kword_len, !A_base; lia. }
 split.
 - rewrite !Lk1_Ckkm1, <- !fs_count_km1, <- Nat.add_le_mono_l.
   fixpred.
   set (c := fs k (k-1) n).
   set (c' := fs (S k) k n).
   destruct (Nat.eq_dec c' 0); try lia.
   replace c' with (S (c'-1)) by lia. change (c'-1 < c).
   apply (incr_strmono_iff _ (L_incr (S k) k)).
   apply Nat.lt_le_trans with n; [apply steiner_thm; lia|].
   transitivity (L k (k-1) c); [apply steiner_thm; lia|].
   destruct (Nat.eq_dec k 1) as [->|K1].
   + rewrite L_k_0. apply L_ge_n.
   + apply Nat.lt_le_incl. replace k with (S (k-1)) at 4 by lia.
     apply IH; try apply fs_lt; try apply fs_nonzero; lia.
 - intros _. destruct n; try easy.
   destruct (Nat.eq_dec (kseq (S k) n) (S k - 1)) as [E|N].
   + intros j Hj. rewrite !L_S, E.
     rewrite knsub_kword, kword_len by lia.
     assert (Hx := kseq_letters k n lia).
     set (x := kseq k n) in *.
     generalize (knsub_len_le k j x Hx). rewrite !A_base by lia.
     destruct (IH n lia) as (_,IH').
     specialize (IH' lia j Hj).
     lia.
   + destruct (ksubst_prefix_inv (S k) (kprefix (S k) (S n)))
       as (v & w & Hv & E & Hw); try apply kprefix_ok.
     destruct Hw as [-> | ->].
     2:{ rewrite take_S in Hv; apply app_inv' in Hv; trivial;
         destruct Hv as (_,[= E']); lia. }
     rewrite app_nil_r in Hv.
     red in E.
     set (l := length v) in *.
     assert (E' : L (S k) 1 l = S n).
     { now rewrite <- (kprefix_length (S k) (S n)), Hv, E. }
     assert (Hl0 : l <> 0). { intros ->. now rewrite L_0 in E'. }
     assert (Hl : l < S n).
     { rewrite <- E'. rewrite Lk1_Ckkm1.
       generalize (Ckkm1_nz (S k) l). lia. }
     destruct (IH l Hl) as (IH5,IH6). clear IH. rewrite E' in IH5.
     specialize (IH6 lia).
     assert (LT : forall j, j < k -> L k j (S n) < L (S k) (S j) (S n)).
     { intros j Hj. specialize (IH6 (S j) lia).
       rewrite <- E' at 2. rewrite L_add, Nat.add_1_r.
       eapply Nat.le_lt_trans; [|apply IH6].
       rewrite <- (Nat.add_1_r j), <- L_add. apply incr_mono; trivial.
       apply L_incr. }
     intros j Hj. destruct (Nat.eq_dec j k) as [->|Hj'].
     * generalize (steiner_trick k (S n) lia).
       specialize (LT (k-1) lia). fixpred. lia.
     * apply LT. lia.
Qed.

Lemma Lk1_ge_LSk1 k n : L (S k) 1 n <= L k 1 n.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { rewrite !L_01_1; lia. }
 { apply Lk_LSk; lia. }
Qed.

Lemma Lkj_lt_LSkSj k j n :
  j<=k -> 0 < n -> L k j n < L (S k) (S j) n.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { intros Hj Hn. replace j with 0 by lia.
   rewrite L_k_0, L_01_1 by lia. lia. }
 { intros. apply Lk_LSk; lia. }
Qed.

Lemma fs_decreases k j n :
 j<=k -> fs (S k) (S j) n <= fs k j n.
Proof.
 intros Hj.
 destruct (Nat.eq_dec k 0) as [->|K].
 { replace j with 0 by lia. simpl. apply f_le. }
 destruct (Nat.eq_dec n 0) as [->|Hn].
 { now rewrite !fs_k_0. }
 apply Nat.lt_pred_le. rewrite <- Nat.sub_1_r, (L_lt (S k) (S j)).
 transitivity n; [ apply steiner_thm; lia |].
 eapply Nat.le_lt_trans; [ apply (steiner_thm k j); lia|].
 apply Lkj_lt_LSkSj; trivial. apply fs_nonzero; lia.
Qed.

Theorem f_grows k n : f k n <= f (S k) n.
Proof.
 destruct n; [easy|].
 rewrite !f_S. generalize (fs_decreases k k n lia). lia.
Qed.

(* TODO: show this inequality is actually strict except for a few low n *)

Lemma f_grows_gen k k' n n' : k <= k' -> n <= n' -> f k n <= f k' n'.
Proof.
 intros K N. transitivity (f k' n); [ | now apply f_mono]. clear n' N.
 induction K; trivial. generalize (f_grows m n); lia.
Qed.

Lemma fs_grows k p n : fs k p n <= fs (S k) p n.
Proof.
 revert n.
 induction p as [|p IH]; intros n; try easy.
 rewrite !iter_S. etransitivity; [apply IH|]. apply fs_mono, f_grows.
Qed.

Lemma fs_grows_gen k k' p p' n n' :
  k <= k' -> p >= p' -> n <= n' -> fs k p n <= fs k' p' n'.
Proof.
 intros K P N.
 transitivity (fs k p' n).
 - replace p with ((p-p')+p') by lia. rewrite iter_add. apply fs_le.
 - clear P p. rename p' into p.
   transitivity (fs k' p n); [ | now apply fs_mono]. clear n' N.
   induction K; trivial. generalize (fs_grows m p n). lia.
Qed.

(** Note: when j=k+1, it seems that L k j n <= L (k+1) (j+1) n.
    Especially we can have L k j n = L (k+1) (j+1) n,
    for instance L 3 4 4 = L 4 5 4 = 19.
    This equality is always in n=k+1,
    and L k (k+1) (k+1) = L (S k) (k+2) (k+1) is proved below,
    see L_equality.

    Proving this L k (k+1) n <= L (k+1) (k+2) n would imply
    fs k (k+1) n >= fs (k+1) (k+2) n.

    And for j>k+1, we can even have L k j n > L (k+1) (j+1) n,
    for instance L 3 5 4 = 28 > L 4 6 4 = 26.
*)

(** An interesting lattice of increasing functions : *)

Lemma fs_bound_gen k j n :
 j <= k -> fs k j n <= fs (k-1) (j-1) n <= fs k (j-1) n.
Proof.
 destruct k, j; try easy.
 intros. fixpred.
 split. apply fs_decreases; lia. apply fs_grows_gen; lia.
Qed.

Lemma fs_bound_gen' k j n :
 j <= k+1 -> fs k j n <= fs (S k) j n <= fs k (j-1) n.
Proof.
 destruct j; try easy.
 split. apply fs_grows_gen; lia. fixpred. apply fs_decreases; lia.
Qed.


(** Counting letter p < k-1.

    The key idea: no matter which letter is i, the letter p occurs
    exactly once in [knsub k (k+p) [i]], always at position (S p).

    This subsumes an older section dedicated specifically to letter 0.
*)

Lemma kword_flatmap k n :
  kword k (k-1+n) = flat_map (kword k) (k-1 :: seq 0 n).
Proof.
 revert n.
 withoutloss k (1<=k).
 { intros K.
   induction n.
   - rewrite Nat.add_0_r. simpl. now rewrite app_nil_r.
   - rewrite kword_eqn by lia.
     replace (k-1 + S n -1) with (k-1+n) by lia. rewrite IHn.
     rewrite seq_S. simpl. rewrite <- app_assoc, flat_map_app.
     do 2 f_equal. simpl. rewrite app_nil_r. f_equal. lia. }
 { intros n.
   destruct (Nat.eq_dec k 0) as [->|K]; [|apply WL; lia].
   simpl. specialize (WL 1 lia n). simpl in WL. apply WL. }
Qed.

Lemma knsub_unique_letter k p i : p < k-1 -> i < k ->
 exists w, knsub k (k+p) [i] = kword k p ++ [p] ++ w /\ ~In p w.
Proof.
 intros Hp Hi. rewrite knsub_kword_gen by lia.
 replace (k+p+i-(k-1)) with (S p+i) by lia.
 destruct (kword_prefix k (S p) (S p+i) lia) as (w,Hw).
 exists w. split.
 - rewrite <- Hw. rewrite !kword_low, seq_S by lia. simpl.
   now rewrite <- app_assoc.
 - destruct (Nat.le_gt_cases (S p + i) (k-1)).
   + rewrite !kword_low in Hw by lia.
     rewrite seq_app in Hw. injection Hw as Hw. apply app_inv_head in Hw.
     subst. rewrite in_seq. lia.
   + replace (S p + i) with ((k-1) + (S p + i - (k-1))) in Hw by lia.
     rewrite kword_flatmap in Hw.
     set (n := S p + i - (k-1)) in *.
     simpl in Hw. rewrite !kword_low in Hw by lia.
     replace (k-1) with (S p + ((k-1) - S p)) in Hw at 3 by lia.
     rewrite seq_app in Hw. injection Hw as Hw.
     rewrite <- app_assoc in Hw. apply app_inv_head in Hw.
     subst. rewrite in_app_iff, in_seq.
     intros [IN|IN]; try lia.
     rewrite in_flat_map in IN. destruct IN as (x & Hx & IN).
     rewrite in_seq in Hx. rewrite kword_low in IN by lia. simpl in IN.
     rewrite in_seq in IN. lia.
Qed.

Lemma knsub_unique_letter' k p i : p < k-1 -> i < k ->
 exists w w', knsub k (k+p) [i] = w++[p]++w'
              /\ length w = S p /\ ~In p w /\ ~In p w'.
Proof.
 intros Hp Hi.
 destruct (knsub_unique_letter k p i Hp Hi) as (w & E & W).
 exists (kword k p), w; repeat split; trivial.
 - rewrite kword_len, A_base; lia.
 - rewrite kword_low by lia. simpl. rewrite in_seq; lia.
Qed.

Lemma knsub_nbocc k p u : p < k-1 ->
  Forall (fun a : nat => a < k) u ->
  nbocc p (knsub k (k+p) u) = length u.
Proof.
 intros Hp.
 induction u as [|i u IH]; intros Hu.
 - unfold knsub. now rewrite napply_nil.
 - inversion Hu; subst.
   rewrite (knsub_app _ _ [i] u), nbocc_app, IH by trivial. clear IH.
   destruct (knsub_unique_letter' k p i Hp) as (w & w' & -> & _ & W & W');
    trivial.
   rewrite !nbocc_app. simpl. rewrite Nat.eqb_refl. now rewrite !nbocc_notin.
Qed.

Lemma LBound_Ckp k p c n : p < k-1 ->
  LBound k (k+p) n c -> c = C k p (n+S p).
Proof.
intros Hp H. unfold LBound in *.
assert (c <> 0). { intros ->. rewrite !L_0 in *. lia. }
set (p' := k+p) in *.
replace c with (S (c-1)) in H at 2 by lia. rewrite L_S in H.
unfold L in H. set (u := knsub _ _ _) in *.
set (x := kseq k (c-1)) in *.
set (y := kseq k c) in *.
set (vx := knsub k p' [x]) in *.
set (vy := knsub k p' [y]).
unfold C. rewrite count_nbocc.
assert (P := knsub_prefixseq k p' (S (S (c-1)))).
rewrite !take_S, !knsub_app in P. replace (S (c-1)) with c in P by lia.
fold u x y vx vy in P. rewrite <- app_assoc in P.
destruct (knsub_unique_letter' k p x Hp) as (w1 & w2 & E & L & W1 & W2);
 try (apply kseq_letters; lia).
destruct (knsub_unique_letter' k p y Hp) as (w3 & w4 & E' & L' & W3 & W4);
 try (apply kseq_letters; lia). fold p' vx vy in E,E'.
assert (P' : Prefix (kprefix k (n+S p)) (u++vx++vy)).
{ eapply PrefixSeq_incl; eauto using kprefix_ok.
  rewrite kprefix_length, E', !app_length, L'. simpl. lia. }
clear P. rename P' into P.
rewrite E,E', <- !app_assoc, !app_length, L in *. simpl in *.
clear E E' x y vx vy.
rewrite (app_assoc u), (app_assoc w2) in P.
apply Prefix_app in P.
destruct P as [P|(w & E & P)].
{ apply Prefix_len in P. rewrite kprefix_length, app_length, L in P. lia. }
rewrite E, !nbocc_app.
unfold u.
rewrite knsub_nbocc, kprefix_length; trivial. 2:{ apply kprefix_letters; lia. }
clearbody u.
rewrite nbocc_notin by trivial.
apply (f_equal (@length _)) in E.
rewrite kprefix_length, !app_length, L in E.
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

Lemma fs_count k p n : p < k-1 -> fs k (k+p) n = C k p (n+S p).
Proof.
 intros Hp.
 destruct (Nat.eq_dec n 0) as [->|N].
 - rewrite Nat.add_0_l, fs_k_0, count_nbocc.
   rewrite <- (@A_base k p lia), kprefix_A_kword, kword_low by lia.
   rewrite nbocc_notin; trivial. simpl. rewrite in_seq. lia.
 - apply LBound_Ckp; trivial. apply steiner_thm; lia.
Qed.

(** Application to letter 0 (especially a different proof of f_count_0). *)

Lemma fs_count_0 k n : 1 < k -> fs k k n = C k 0 (S n).
Proof.
 intros. generalize (fs_count k 0 n lia).
 now rewrite Nat.add_0_r, Nat.add_1_r.
Qed.

Lemma f_count_0 k n : 1 < k -> C k 0 n + f k n = n.
Proof.
 intros.
 destruct n; try easy.
 rewrite <- fs_count_0, f_S by easy. generalize (fs_le k k n); lia.
Qed.

Lemma Ck0_ge_CSk0 k n : C (S k) 0 n <= C k 0 n.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K0].
 { apply Nat.le_refl. }
 destruct (Nat.eq_dec k 1) as [->|K1].
 { rewrite (count_all (kseq 1)). apply count_subid.
   intros m _. rewrite kseq_01; lia. }
 generalize (f_count_0 k n lia) (f_count_0 (S k) n lia) (f_grows k n). lia.
Qed.


(** Application to letter 1 *)

Lemma fs_count_1 k n : 2 < k -> fs k (k+1) n = C k 1 (n+2).
Proof.
 intros K. apply fs_count. lia.
Qed.

(** The previous conjecture fs k (k+1) n >= fs (k+1) (k+2) n
    hence implies:  C k 1 n >= C (S k) 1 n.
    (at least for 3<=k, and probably even 2<=k)
*)


(** Counting many letters at once : all the letters larger than some p.

    Key idea here: for j < k, [knsub k j [i]] has only its first letter
    that is j or more.

    NB: [LBound_count_above] subsumes previous [LBound_Ckkm1] but we keep
    it for its simplificity.
 *)

Lemma knsub_nbabove k p u : p < k ->
  Forall (fun a : nat => a < k) u ->
  nbabove p (knsub k p u) = length u.
Proof.
 intros Hp.
 induction u as [|i u IH]; intros Hu.
 - unfold knsub. now rewrite napply_nil.
 - inversion Hu; subst.
   rewrite (knsub_app _ _ [i] u), nbabove_app, IH by trivial. clear IH Hu.
   rewrite knsub_alt by trivial.
   case Nat.ltb_spec; intros; simpl.
   + case Nat.leb_spec; lia.
   + rewrite kword_low by lia. simpl.
     case Nat.leb_spec; intros; try lia.
     rewrite nbabove_0; try lia. apply Forall_forall.
     intro x. rewrite in_seq. lia.
Qed.

Lemma LBound_count_above k p c n : p < k ->
 LBound k p n c -> c = count_above (kseq k) p n.
Proof.
 unfold LBound. intros Hn H.
 assert (c <> 0). { intros ->. simpl in *. rewrite !L_0 in H. lia. }
 replace c with (S (c-1)) in H at 2 by lia.
 rewrite L_S in H.
 assert (Hx := kseq_letters k (c-1) lia).
 set (x := kseq k (c-1)) in *.
 rewrite count_above_nbabove.
 assert (P := knsub_prefixseq k p (S (c-1))).
 rewrite take_S, knsub_app in P. fold x in P.
 unfold L in *. set (u := knsub _ _ _) in *.
 assert (P' : Prefix (kprefix k n) (u++knsub k p [x])).
 { eapply PrefixSeq_incl; eauto using kprefix_ok.
   rewrite kprefix_length, app_length. lia. }
 clear P. rename P' into P.
 rewrite knsub_alt in * by trivial.
 destruct (Nat.ltb_spec (p+x) (k-1)).
 - simpl in H.
   destruct P as ([|],P).
   + rewrite app_nil_r in P. rewrite P, nbabove_app. simpl.
     case Nat.leb_spec; intros; try lia.
     unfold u. rewrite knsub_nbabove; trivial.
     2:{ apply kprefix_letters; lia. }
     rewrite kprefix_length. lia.
   + apply (f_equal (@length _)) in P.
     rewrite !app_length, kprefix_length in P. simpl in P. lia.
 - rewrite kword_len, A_base, kword_low in * by lia.
   apply Prefix_app in P. destruct P as [P|(w & E & P)].
   + apply Prefix_len in P. rewrite kprefix_length in P. lia.
   + rewrite E, nbabove_app.
     unfold u. rewrite knsub_nbabove; trivial.
     2:{ apply kprefix_letters; lia. }
     rewrite kprefix_length.
     apply Prefix_cons_inv in P. destruct P as [->|(w' & -> & P)].
     * rewrite app_nil_r in E. apply (f_equal (@length _)) in E.
       rewrite kprefix_length in E. lia.
     * simpl. case Nat.leb_spec; intros; try lia.
       rewrite nbabove_0; try lia.
       apply Forall_forall. intros y IN. apply Prefix_incl in P.
       specialize (P y IN). rewrite in_seq in P. lia.
Qed.

Lemma fs_count_above k p n : p < k -> fs k p n = count_above (kseq k) p n.
Proof.
 intros P.
 destruct n.
 - now rewrite fs_k_0.
 - apply LBound_count_above; trivial. apply steiner_thm; lia.
Qed.

(** Hence the monotony results on fs also correspond to results on
    some ΣCkp. *)

(** C as difference between count_above *)

Lemma Ckp_diff_fs k p n : p < k-1 -> C k p n = fs k p n - fs k (S p) n.
Proof.
 intros. rewrite !fs_count_above, count_above_S; lia.
Qed.

Lemma Ckp_diff_bis k p n : p < k-1 -> C k p n = fs k k (fs k p n - 1).
Proof.
 intros. rewrite Ckp_diff_fs; trivial.
 rewrite <- (f_eqn_pred k (fs k p n)) at 1. rewrite <- Nat.sub_1_r.
 simpl. lia.
Qed.

(** Weird consequence (see also GenG.f_alt_eqn) *)

Lemma wierd_law k p n : p < k-1 ->
   fs k (k+p) n = fs k k (fs k p (n+S p) - 1).
Proof.
 intros. rewrite <- Ckp_diff_bis; trivial. now apply fs_count.
Qed.


(** Galois connection : L is a right adjoint to f *)

Lemma L_f_galois k j n m : 0<k -> fs k j n <= m <-> n <= L k j m.
Proof.
 intros. destruct (Nat.eq_dec n 0) as [->|N].
 - rewrite fs_k_0; lia.
 - split; intros.
   + etransitivity. 2:apply incr_mono; eauto using L_incr.
     apply steiner_thm; lia.
   + rewrite <- (fs_L k j m) by trivial. now apply fs_mono.
Qed.

Lemma LL_fsfs_le_iff k k' j j' n :
  0<k -> 0<k' ->
  L k j n <= L k' j' n <-> let m := L k j n in fs k' j' m <= fs k j m.
Proof.
 intros. simpl. rewrite fs_L; trivial. split; intros; now apply L_f_galois.
Qed.

Lemma LL_fsfs_lt_iff k k' j j' n :
  0<k -> 0<k' ->
  L k j n < L k' j' n -> let m := L k' j' n in fs k' j' m < fs k j m.
Proof.
 intros K K'. rewrite !Nat.lt_nge. now rewrite LL_fsfs_le_iff.
Qed.

Lemma LL_fsfs_le_bis k k' j j' n :
  0<k -> 0<k' ->
  let m := fs k j n in L k j m <= L k' j' m -> fs k' j' n <= fs k j n.
Proof.
 simpl; intros K K' H.
 destruct (Nat.eq_dec n 0) as [->|N].
 - now rewrite !fs_k_0.
 - apply L_f_galois; trivial.
   etransitivity; [|apply H]. apply steiner_thm; lia.
Qed.

Lemma fsfs_LL_lt k k' j j' n :
  0<k -> 0<k' ->
  fs k j n < fs k' j' n -> let m := fs k j n in L k' j' m < L k j m.
Proof.
 intros K K'. simpl. rewrite !Nat.lt_nge. intros H. contradict H.
 now apply LL_fsfs_le_bis.
Qed.

Definition pointwise_le (f1 f2 : nat -> nat) := forall n, f1 n <= f2 n.

Infix "[<=]" := pointwise_le (at level 70, no associativity).

Lemma L_f_dual k k' j j' :
  0<k -> 0<k' ->
  fs k j [<=] fs k' j' <-> L k' j' [<=] L k j.
Proof.
 intros K K'.
 split; intros H n. now apply LL_fsfs_le_iff. now apply LL_fsfs_le_bis.
Qed.

(** L at n=1 *)

Lemma Lkj1_A k j : L k j 1 = A k j.
Proof.
 rewrite L_S, L_0. rewrite kseq_k_0.
 destruct (Nat.eq_dec k 0) as [->|K].
 - simpl. change (knsub 0 j [0]) with (knsub 1 j [0]). rewrite A_0.
   now rewrite knsub_kword, kword_len by lia.
 - now rewrite knsub_kword, kword_len by lia.
Qed.

Lemma Lkj1_diag_decr_ultimately k j :
  0<k -> 2*k+1 < j -> L (S k) (S j) 1 < L k j 1.
Proof.
 intros K J. rewrite !Lkj1_A. apply A_diag_decr; lia.
Qed.

Lemma L_diag_nle_ultimately k j :
  0<k -> 2*k+1 < j -> ~(L k j [<=] L (S k) (S j)).
Proof.
 intros K J LE. specialize (LE 1). apply Lkj1_diag_decr_ultimately in J; lia.
Qed.

Lemma L_diag_decr_gen k j p :
 0<k -> k+1 <= j -> 2*k+2 <= p+j -> p <= k ->
 L (S k) (S j) (S p) < L k j (S p).
Proof.
 intros K J PJ P.
 rewrite <- (@A_base (S k) p) at 1 by lia.
 rewrite <- (@A_base k p) by lia.
 rewrite <- !Lkj1_A, !L_add, Nat.add_succ_l.
 apply Lkj1_diag_decr_ultimately; lia.
Qed.

Lemma L_diag_decr_example k j :
 0<k -> k+2 <= j -> let p := 2*k+2-j in L (S k) (S j) (S p) < L k j (S p).
Proof.
 intros K J p. unfold p. apply L_diag_decr_gen; lia.
Qed.

Lemma L_diag_decr_example_kp1 k :
 0<k -> L (S k) (k+3) (k+1) < L k (k+2) (k+1).
Proof.
 intros.
 replace (k+1) with (S (2*k+2-(k+2))) by lia.
 replace (k+3) with (S (k+2)) by lia.
 now apply L_diag_decr_example.
Qed.

Lemma L_diag_incr_example k j : j <= 2*k -> L k j 1 < L (S k) (S j) 1.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - intros J. replace j with 0 by lia. now compute.
 - intros J. rewrite !Lkj1_A, A_diag_step; lia.
Qed.

Lemma fs_diag_incr_example k j :
 0<k -> k+2 <= j -> let p := L k j (S (2*k+2-j)) in
 fs k j p < fs (S k) (S j) p.
Proof.
 intros K J p. unfold p. apply LL_fsfs_lt_iff; try lia.
 apply L_diag_decr_example; lia.
Qed.

Lemma fs_diag_incr_example_kp1 k :
 0<k -> let p := L k (k+2) (k+1) in
 fs k (k+2) p < fs (S k) (k+3) p.
Proof.
 intros K.
 replace (k+1) with (S (2*k+2-(k+2))) by lia.
 replace (k+3) with (S (k+2)) by lia.
 now apply fs_diag_incr_example.
Qed.

Lemma fs_diag_decr_example k j :
 0<k -> j <= 2*k -> let p := L (S k) (S j) 1 in
 fs (S k) (S j) p < fs k j p.
Proof.
 intros K J p. unfold p. apply LL_fsfs_lt_iff; try lia.
 now apply L_diag_incr_example.
Qed.

(** For letters [2<=i<k-1], [C k i] and [C (k+1) i] are uncomparable. *)

Lemma C_diag_incr_example k i :
 2 <= i < k-1 ->
 let n := L k (2*k+2) 1 + S i in
 C k i n < C (S k) i n.
Proof.
 intros Hi n. unfold n. rewrite <- !fs_count by lia.
 rewrite (Nat.add_succ_l k).
 set (j := k + i).
 replace (L k (2*k+2) 1) with (L k j (S (2*k+2-j))).
 2:{ replace (2*k+2) with (j + (k+2-i)) by lia.
     rewrite <- L_add. f_equal. rewrite Lkj1_A, A_base; lia. }
 apply fs_diag_incr_example; lia.
Qed.

Lemma C_diag_decr_example k i :
 2 <= i < k-1 ->
 let n := L (S k) (1+k+i) 1 + S i in
 C (S k) i n < C k i n.
Proof.
 intros Hi n. unfold n. rewrite <- !fs_count by lia.
 rewrite (Nat.add_succ_l k).
 set (j := k + i). replace (1+k+i) with (S j) by lia.
 apply fs_diag_decr_example; lia.
Qed.


(** Back to [Lk_LSk], large inequalities, decreasing [j].
    USELESS THEOREM actually, since
    - concl already proved for j <= k
    - hyp false for j >= k+1 (cf L_diag_decr_gen)

Lemma Lk_LSk_again k j :
 L k (S j) [<=] L (S k) (S (S j)) ->
 L k j [<=] L (S k) (S j).
*)

Lemma f_L_conjectures k :
 (forall m, quad (S k) < m -> f (S k) m < f (S (S k)) m) ->
 (forall m, quad k < m -> L (S (S k)) 1 m < L (S k) 1 m).
Proof.
 intros H m Hm.
 red in Hm.
 apply Nat.le_lteq in Hm. destruct Hm as [Hm|<-].
 - apply (incr_strmono (L (S k) 1)) in Hm. 2:apply L_incr.
   rewrite L_k_1_rchild, rchild_Sk_Squad in Hm by lia.
   rewrite Nat.lt_nge, LL_fsfs_le_iff, <- Nat.lt_nge by lia.
   apply H. lia.
 - rewrite !L_k_1_rchild, rchild_SSk_Squad, rchild_Sk_Squad; lia.
Qed.

(* Recip ??
 (forall m, quad k < m -> L (S (S k)) 1 m < L (S k) 1 m) ->
 (forall m, quad (S k) < m -> f (S k) m < f (S (S k)) m).
*)

Lemma L21_le_2np3 n : L 2 1 (n+2) <= 2*n+3.
Proof.
 induction n as [|n IH]; simpl; try easy.
 rewrite L_S. unfold knsub. simpl. unfold ksubst.
 destruct Nat.eqb; simpl; lia.
Qed.

Lemma L21_lt_2n n : 2 <= n -> L 2 1 n < 2*n.
Proof.
 intros. replace n with (n-2+2) by lia.
 generalize (L21_le_2np3 (n-2)). lia.
Qed.

Lemma f_L_conjectures_bis k : 0<k ->
 (forall m, quad k < m -> f k m < f (S k) m) ->
 (forall m, quad (k-1) < m -> L (S k) 1 m < L k 1 m).
Proof.
 intros K H m Hm.
 destruct (Nat.eq_dec k 1) as [->|K1].
 { simpl in Hm. rewrite (L_01_1 1) by trivial.
   apply L21_lt_2n. compute in Hm. lia. }
 destruct k; try easy. fixpred.
 apply f_L_conjectures; auto.
Qed.

(** More about L at n=1 *)

Lemma L_k_2km2 k : 0<k -> L k (2*k-2) 1 = triangle k.
Proof.
 intros.
 rewrite Lkj1_A. replace (2*k-2) with ((k-1)+(k-1)) by lia.
 rewrite A_triangle by lia.
 replace k with (S (k-1)) at 3 by lia.
 rewrite triangle_succ. lia.
Qed.

Lemma L_k_2km1 k : 0<k -> L k (2*k-1) 1 = triangle (k+1) - 1.
Proof.
 intros.
 rewrite Lkj1_A. replace (2*k-1) with (k-1+k) by lia.
 rewrite A_triangle by lia. rewrite Nat.add_1_r, triangle_succ. lia.
Qed.

Lemma L_k_2k k : L k (2*k) 1 = triangle (k+2) - 2.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K]; try easy.
 rewrite Lkj1_A. replace (2*k) with (k-1+(k+1)) by lia.
 rewrite A_triangle by lia.
 rewrite (Nat.add_succ_r _ 1), triangle_succ. lia.
Qed.

Lemma L_k_2kp1 k : 0<k -> L k (2*k+1) 1 = triangle (k+3) - 2.
Proof.
 intros K. rewrite Lkj1_A. apply A_2k1_tri; lia.
Qed.

Lemma L_k_Sk_k k : 0<k -> L k (S k) k = triangle (k+2) - 2.
Proof.
 intros K.
 replace k with (S (k -1)) at 3 by lia.
 rewrite <- (@A_base k (k-1)), <- Lkj1_A by lia.
 rewrite L_add, <- L_k_2k. f_equal. lia.
Qed.

Lemma L_k_Sk_Sk k : 0<k -> L k (S k) (S k) = triangle (k+3) - 2.
Proof.
 intros K.
 rewrite <- (@A_base k k) at 2 by lia.
 rewrite <- Lkj1_A.
 rewrite L_add, <- L_k_2kp1 by trivial. f_equal. lia.
Qed.

Lemma L_equality k : 0<k -> L k (S k) (S k) = L (S k) (k+2) (S k).
Proof.
 intros K.
 rewrite L_k_Sk_Sk; trivial.
 replace (k+3) with ((k+1)+2) by lia.
 rewrite <- L_k_Sk_k by lia. f_equal; lia.
Qed.

Definition cex k j := S (2*k+2-j).

Lemma cex_spec k j :
  0<k -> k+2 <= j ->
  L (S k) (S j) (cex k j) < L k j (cex k j).
Proof.
 intros K Hj.
 destruct (Nat.le_gt_cases (2*k+2) j) as [Hj'|Hj'].
 - unfold cex. replace (2*k+2-j) with 0 by lia.
   rewrite !Lkj1_A. apply A_diag_decr; lia.
 - unfold cex. set (p := 2*k+2-j) in *.
   rewrite <- (@A_base k p) at 2 by lia.
   rewrite <- Lkj1_A, L_add, Lkj1_A.
   replace (j+p) with (2*k+2) by lia.
   rewrite <- (@A_base (S k) p) by lia.
   rewrite <- Lkj1_A, L_add, Lkj1_A.
   replace (S j+p) with (S (2*k+2)) by lia.
   apply A_diag_decr; lia.
Qed.

Lemma cex_spec' k j :
  0<k -> k+2 <= j ->
  let m := L k j (cex k j) in
  fs k j m < fs (S k) (S j) m.
Proof.
 intros K Hj. apply LL_fsfs_lt_iff; try lia. now apply cex_spec.
Qed.
