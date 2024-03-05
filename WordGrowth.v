Require Import MoreFun MoreList DeltaList FunG GenFib GenG Words.
Import ListNotations.

(** * WordGrowth *)

(** Follow-up of [Words.v] dedicated to the study of positions
    of some letters in the infinite words [(kseq k)].
    Main result : the partial sums of [kseq k] grow with k.
    Applications :
    - the count of letter k decreases with k
    - the count of letter 0 decreases with k
    - for all point n, [f k n <= f (S k) n]. *)

(** First, we focus on the substitution [(ksubst k)^k] which is
    quite interesting :
    as for [ksubst k], its infinite word is also [kseq k], but
    it produces it by blocks starting by all the [k] letters. *)

Definition ksubstk k n := napply (ksubst k) k [n].

Definition ksubstkw k := apply (ksubstk k).

Lemma ksubstkw_app k u v : ksubstkw k (u++v) = ksubstkw k u ++ ksubstkw k v.
Proof.
 apply apply_app.
Qed.

(** Fun fact: for n <= k, ksubst^k(n) = ksubst^n(k) *)

Lemma ksubst_pearl k n :
  n <= k -> napply (ksubst k) k [n] = napply (ksubst k) n [k].
Proof.
 intros LE.
 rewrite <- (ksubst_low0 k n LE).
 rewrite <- (ksubst_low0 k k (Nat.le_refl _)).
 rewrite <- !napply_add. f_equal. lia.
Qed.

Lemma ksubstk_kword k n : n <= k -> ksubstk k n = kword k n.
Proof.
 intros. now apply ksubst_pearl.
Qed.

Lemma ksubstk_alt k n : n <= k -> ksubstk k n = k :: seq 0 n.
Proof.
 intros. rewrite <- kword_low by lia. now apply ksubstk_kword.
Qed.

Lemma ksubstk_len k n : n <= k -> length (ksubstk k n) = S n.
Proof.
 intros H. rewrite ksubstk_alt by trivial. simpl. f_equal. apply seq_length.
Qed.

Lemma ksubstk_noerase k : NoErase (ksubstk k).
Proof.
 intro a. apply noerase_nonnil_napply; try easy. apply ksubst_noerase.
Qed.

Lemma ksubstk_prolong k : k<>0 -> Prolong (ksubstk k) k.
Proof.
 exists (seq 0 k); split.
 - contradict H. now rewrite <- (seq_length k 0), H.
 - now rewrite ksubstk_alt by lia.
Qed.

Lemma apply_napply s n l :
  apply (fun x => napply s n [x]) l = napply s n l.
Proof.
 induction l; simpl.
 - symmetry. apply napply_nil.
 - rewrite IHl. symmetry. apply napply_cons.
Qed.

Lemma napply_ksubstk k n l :
 napply (ksubstk k) n l = napply (ksubst k) (n*k) l.
Proof.
 induction n; trivial.
 rewrite napply_alt, IHn.
 simpl. rewrite napply_add. apply apply_napply.
Qed.

Definition kseqk k := subst2seq (ksubstk k) k.

Lemma kseqk_kseq k : forall n, kseqk k n = kseq k n.
Proof.
 destruct (Nat.eq_dec k 0) as [->|N].
 - (* We don't really care about k=0, but for the fun... *)
   intros n. unfold kseqk, subst2seq.
   assert (E : napply (ksubstk 0) n [0] = [0]) by now induction n.
   rewrite E.
   replace (nth n [0] 0) with 0.
   2:{ now destruct n as [|[|n]]. }
   generalize (kseq_letters 0 n). lia.
 - intros n.
   unfold kseqk.
   rewrite subst2seq_indep with (m:=n) (b:=k);
    auto using ksubstk_noerase, ksubstk_prolong.
   unfold kseq.
   rewrite subst2seq_indep with (m:=n*k) (b:=k);
    auto using ksubst_noerase, ksubst_prolong.
   2:{ destruct k; simpl; lia. }
   f_equal. apply napply_ksubstk.
Qed.

Lemma ksubstk_prefix k u :
 PrefixSeq u (kseq k) -> PrefixSeq (ksubstkw k u) (kseq k).
Proof.
  unfold ksubstkw.
  rewrite <- napply_1.
  rewrite napply_ksubstk. apply PrefixSeq_napply.
  apply ksubst_noerase.
  apply ksubst_prolong.
Qed.


(** Shuo Li / W. Steiner proof : the partial sums of kseq grow with k.
    Applications :
    - the count of letter k decreases with k
    - the count of letter 0 decreases with k
*)

(** Where is the p-th letter k in [kseq k] ?
    We count occurrences from 0 : the 0-th letter k is at position 0 *)

Definition positionk k p := length (ksubstkw k (kprefix k p)).

Lemma positionk_S k p : positionk k (S p) = positionk k p + S (kseq k p).
Proof.
 unfold positionk.
 rewrite take_S, ksubstkw_app, app_length; simpl.
 now rewrite app_nil_r, ksubstk_len by apply kseq_letters.
Qed.

Lemma kseq_positionk k p : kseq k (positionk k p) = k.
Proof.
 rewrite <- (take_nth (kseq k) (positionk k (S p)) _ k).
 2:{ rewrite positionk_S; lia. }
 set (u := kprefix k (S p)).
 assert (Hu : PrefixSeq u (kseq k)) by apply kprefix_ok.
 apply ksubstk_prefix in Hu. red in Hu. unfold u at 2 in Hu.
 fold (positionk k (S p)) in Hu. rewrite <- Hu.
 clear Hu. unfold u. rewrite take_S, ksubstkw_app.
 rewrite app_nth2 by (unfold positionk; lia).
 replace (_-_) with 0 by (unfold positionk; lia). simpl.
 now rewrite app_nil_r, ksubstk_alt by apply kseq_letters.
Qed.

Lemma count_k_nz k n : 0 < n -> 0 < count (kseq k) k n.
Proof.
 induction n.
 - lia.
 - intros _. destruct n; simpl in *; try lia.
   rewrite kseq_k_0, Nat.eqb_refl. lia.
Qed.

Lemma nbocc_ksubstk k u :
  Forall (fun a => a <= k) u ->
  nbocc k (ksubstkw k u) = length u.
Proof.
 induction u; trivial.
 simpl. intros Hu. inversion_clear Hu.
 rewrite nbocc_app, IHu by trivial.
 rewrite ksubstk_alt by trivial. simpl.
 rewrite Nat.eqb_refl. rewrite nbocc_notin; try lia.
 rewrite in_seq. lia.
Qed.

Lemma take_kseq_letters k n :
  Forall (fun a => a <= k) (kprefix k n).
Proof.
 induction n.
 - constructor.
 - rewrite take_S. apply Forall_app. split; trivial.
   repeat constructor. apply kseq_letters.
Qed.

Lemma countk_positionk k p :
 count (kseq k) k (positionk k p) = p.
Proof.
 rewrite count_nbocc.
 set (u := kprefix k p).
 assert (Hu : PrefixSeq u (kseq k)) by apply kprefix_ok.
 apply ksubstk_prefix in Hu. red in Hu. unfold u at 2 in Hu.
 fold (positionk k p) in Hu. rewrite <- Hu.
 rewrite nbocc_ksubstk. apply kprefix_length.
 apply take_kseq_letters.
Qed.

Lemma countk_S_positionk k p :
 count (kseq k) k (S (positionk k p)) = S p.
Proof.
 rewrite count_nbocc, take_S, nbocc_app, <- count_nbocc, countk_positionk.
 rewrite kseq_positionk. simpl. rewrite Nat.eqb_refl. lia.
Qed.

Lemma positionk_bounds k n :
  0 < n ->
  exists p, positionk k p < n <= positionk k (S p).
Proof.
 intros. apply incr_function_bounds'; auto. intro. rewrite positionk_S. lia.
Qed.

Lemma positionk_complete k n :
 kseq k n = k -> exists p, n = positionk k p.
Proof.
 destruct (Nat.eq_dec n 0).
 - subst. now exists 0.
 - destruct (positionk_bounds k n) as (p, (Hp, HSp)). lia.
   exists (S p).
   apply Nat.le_lteq in HSp. destruct HSp; trivial.
   exfalso.
   assert (LE : S (positionk k p) <= positionk k (S p)).
   { rewrite positionk_S. lia. }
   set (a := positionk k p) in *.
   set (b := positionk k (S p)) in *.
   assert (E : count (kseq k) k (S a) = count (kseq k) k b).
   { unfold a, b. now rewrite countk_S_positionk, countk_positionk. }
   assert (P := count_flat (kseq k) k (S a) b LE E n). lia.
Qed.

Lemma positionk_is_position k : IsPosition (kseq k) k (positionk k).
Proof.
 constructor.
 - red. intros. rewrite positionk_S. lia.
 - apply kseq_positionk.
 - apply positionk_complete.
Qed.

Lemma positionk_cumul k n :
  positionk k n = n + cumul (kseq k) n.
Proof.
 unfold positionk.
 induction n. trivial.
 rewrite take_S, ksubstkw_app, app_length, IHn. simpl.
 rewrite app_nil_r, ksubstk_len by apply kseq_letters. lia.
Qed.

Lemma positionk_bounds' k n p :
  0 < n ->
  p = count (kseq k) k n ->
  positionk k (p-1) < n <= positionk k p.
Proof.
  intros Hn Hp.
  destruct (positionk_bounds k n Hn) as (p' & (U,V)).
  assert (U' := count_mono (kseq k) k _ _ U).
  rewrite countk_S_positionk, <- Hp in U'.
  assert (V' := count_mono (kseq k) k _ _ V).
  rewrite countk_positionk, <- Hp in V'.
  replace p with (S p') by lia. simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma length_ksubstw k m :
  length (ksubstw k (kprefix k m)) = m + count (kseq k) k m.
Proof.
 induction m; trivial.
 rewrite take_S, ksubstw_app, app_length, IHm. simpl. unfold ksubst.
 case Nat.eqb_spec; simpl; lia.
Qed.

Lemma list_sum_ksubstw k u :
  list_sum (ksubstw k u) + nbocc k u = list_sum u + length u.
Proof.
 induction u; trivial.
 simpl. rewrite list_sum_app. unfold ksubst at 1.
 case Nat.eqb_spec; simpl; try lia.
Qed.

Lemma list_sum_ksubstw' k u :
  list_sum (ksubstw k u) = list_sum u + length u - nbocc k u.
Proof.
 generalize (nbocc_le_length k u) (list_sum_ksubstw k u). lia.
Qed.

Lemma cumul_kseq_grows k n : 0<n -> cumul (kseq k) n < cumul (kseq (S k)) n.
Proof.
 induction n as [[|n] IH] using lt_wf_ind; [lia|intros _].
 destruct (Nat.eq_dec n 0) as [->|Hn'].
 - simpl. rewrite kseq_bounded_rank. unfold bounded_rank. simpl. lia.
 - destruct (Nat.le_gt_cases k (kseq (S k) n)) as [LE|LT].
   + simpl. specialize (IH n). generalize (kseq_letters k n). lia.
   + assert (Hk : S k <> 0) by lia.
     assert (E := kseq_take_inv (S k) (S n) Hk).
     replace (is_k0 (S k) (S n)) with false in *.
     2:{ unfold is_k0. case Nat.eqb_spec; trivial.
         intros H. apply k0_pred_k in H. simpl in H. lia. }
     rewrite Nat.add_0_r in E.
     set (m := f (S k) (S n)) in *.
     assert (Hm : m < S n) by (apply f_lt; lia).
     assert (Hm0 : 0 < m) by (apply f_nonzero; lia).
     assert (IHm := IH m Hm Hm0).
     set (a := fun k => count (kseq k) k).
     assert (LE : a (S k) m <= a k m).
     { rewrite Nat.le_ngt. intro.
       assert (E1 : m <= positionk k (a k m))
         by (apply positionk_bounds'; trivial).
       assert (E2 := positionk_cumul k (a k m)).
       assert (E3 : cumul (kseq k) (a k m) < cumul (kseq (S k)) (a k m)).
       { apply IH. apply Nat.le_lt_trans with m. apply count_subid. lia.
         apply count_k_nz. lia. }
       assert (E4 : cumul (kseq (S k)) (a k m) <=
                    cumul (kseq (S k)) (a (S k) m -1)).
       { apply cumul_mono. lia. }
       assert (E5 := positionk_cumul (S k) (a (S k) m -1)).
       assert (E6 : positionk (S k) (a (S k) m - 1) < m).
       { apply positionk_bounds'; trivial. }
       lia.
     }
     assert (E1 : S n <= length (ksubstw k (kprefix k m))).
     { rewrite length_ksubstw. fold (a k m).
       transitivity (m + a (S k) m); try lia.
       unfold a. now rewrite <- length_ksubstw, <- E, kprefix_length. }
     assert (P : Prefix (kprefix k (S n)) (ksubstw k (kprefix k m))).
     { apply (PrefixSeq_incl (kseq k)); auto using kprefix_ok, ksubstw_prefix.
       now rewrite kprefix_length. }
     apply list_sum_prefix in P.
     rewrite <- cumul_alt in P.
     eapply Nat.le_lt_trans; [ apply P | ]. clear P.
     rewrite cumul_alt, E. clear E.
     generalize (nbocc_le_length k (kprefix k m)).
     generalize (nbocc_le_length (S k) (kprefix (S k) m)).
     rewrite !list_sum_ksubstw'.
     rewrite <- !cumul_alt, !take_length, <- !count_nbocc.
     fold (a k m) (a (S k) m). lia.
Qed.

(** Application : counting letter k *)

Lemma positionk_grows k n : positionk k n <= positionk (S k) n.
Proof.
 rewrite !positionk_cumul.
 destruct (Nat.le_gt_cases n 0) as [Hn|Hn].
 - replace n with 0 by lia. trivial.
 - assert (H := cumul_kseq_grows k n Hn). lia.
Qed.

Lemma countk_decreases k n :
  count (kseq (S k)) (S k) n <= count (kseq k) k n.
Proof.
  apply (IsPosition_count_anti _ _ _ _ (positionk k) (positionk (S k))).
  - apply positionk_is_position.
  - apply positionk_is_position.
  - apply positionk_grows.
Qed.

Lemma fs_decreases k n : fs (S k) (S k) n <= fs k k n.
Proof.
 rewrite !fs_count_k. apply countk_decreases.
Qed.

(** Hence rchild (a.k.a Shift.shift) decreases with k *)

Lemma rchild_decreases k n : rchild (S k) n <= rchild k n.
Proof.
 unfold rchild. generalize (fs_decreases k n). lia.
Qed.

(** Let's now count letter 0 *)

(** The substitution [(ksubst k)^(S k)] is also quite interesting :
    its infinite word is also [kseq k], but it produces it by
    blocks starting by all the [k;0] letters. *)

Definition ksubstSk k n := napply (ksubst k) (S k) [n].

Definition ksubstSkw k := apply (ksubstSk k).

Lemma ksubstSkw_app k u v : ksubstSkw k (u++v) = ksubstSkw k u ++ ksubstSkw k v.
Proof.
 apply apply_app.
Qed.

Lemma ksubstSk_alt0 k n :
  ksubstSk k n = ksubstw k (ksubstkw k [n]).
Proof.
 unfold ksubstSk, ksubstk. rewrite napply_alt at 1. f_equal. simpl.
 now rewrite !app_nil_r.
Qed.

Lemma napply_ksubstSk k n l :
 napply (ksubstSk k) n l = napply (ksubst k) (n*(S k)) l.
Proof.
 induction n; trivial.
 rewrite napply_alt, IHn.
 simpl Nat.mul. rewrite napply_alt, napply_add.
 set (u := napply _ _ _). clearbody u.
 unfold ksubstSk. now rewrite apply_napply, napply_alt.
Qed.

Lemma ksubstSk_kword k n : n <= k ->
  ksubstSk k n = kword k (S n).
Proof.
 intros H. rewrite ksubstSk_alt0.
 simpl. rewrite app_nil_r, ksubstk_kword by trivial.
 now rewrite <- kword_S.
Qed.

Lemma ksubstSk_alt k n : n <= k ->
  ksubstSk k n = k :: seq 0 (S n).
Proof.
 intros. rewrite <- kword_low by lia. now apply ksubstSk_kword.
Qed.

Lemma ksubstSk_len k n : n <= k -> length (ksubstSk k n) = 2+n.
Proof.
 intros. rewrite ksubstSk_kword, kword_len by trivial. rewrite A_base; lia.
Qed.

Lemma nbocc_ksubstSk k u :
  k<>0 ->
  Forall (fun a : nat => a <= k) u ->
  nbocc 0 (ksubstSkw k u) = length u.
Proof.
 intros Hk.
 induction u; trivial.
 simpl. intros Hu. inversion_clear Hu.
 rewrite nbocc_app, IHu by trivial.
 rewrite ksubstSk_alt by trivial. simpl.
 case Nat.eqb_spec; intros; try easy.
 rewrite nbocc_notin; try lia.
 rewrite in_seq; lia.
Qed.

Lemma ksubstSk_prefix k u :
  PrefixSeq u (kseq k) -> PrefixSeq (ksubstSkw k u) (kseq k).
Proof.
 unfold ksubstSkw.
 rewrite <- napply_1.
 rewrite napply_ksubstSk. apply PrefixSeq_napply.
 apply ksubst_noerase.
 apply ksubst_prolong.
Qed.

Definition position0 k p := S (length (ksubstSkw k (take p (kseq k)))).

Lemma position0_S k p : position0 k (S p) = position0 k p + kseq k p + 2.
Proof.
 unfold position0.
 rewrite take_S, ksubstSkw_app, app_length; simpl.
 rewrite app_nil_r, ksubstSk_len by apply kseq_letters. lia.
Qed.

Lemma kseq_position0 k p : kseq k (position0 k p) = 0.
Proof.
 rewrite <- (take_nth (kseq k) (position0 k (S p) - 1) _ k).
 2:{ rewrite position0_S; lia. }
 set (u := take (S p) (kseq k)).
 assert (Hu : PrefixSeq u (kseq k)).
 { red. unfold u. f_equal. now rewrite take_length. }
 apply ksubstSk_prefix in Hu. red in Hu. unfold u at 2 in Hu.
 replace (length _) with (position0 k (S p) - 1) in Hu.
 2:{ unfold position0. lia. }
 rewrite <- Hu.
 clear Hu. unfold u. rewrite take_S, ksubstSkw_app.
 rewrite app_nth2 by (unfold position0; lia).
 replace (_-_) with 1 by (unfold position0; lia). simpl.
 now rewrite app_nil_r, ksubstSk_alt by apply kseq_letters.
Qed.

Lemma count0_position0 k p :
 k<>0 ->
 count (kseq k) 0 (position0 k p) = p.
Proof.
 intros Hk.
 rewrite count_nbocc.
 set (u := take p (kseq k)).
 assert (Hu : PrefixSeq u (kseq k)).
 { red. unfold u. f_equal. now rewrite take_length. }
 apply ksubstSk_prefix in Hu. red in Hu. unfold u at 2 in Hu.
 unfold position0. rewrite take_S.
 rewrite <- Hu.
 rewrite nbocc_app.
 rewrite nbocc_ksubstSk; trivial. 2:{ unfold u. apply take_kseq_letters. }
 unfold u. rewrite take_length.
 change (length _) with (pred (position0 k p)).
 rewrite k0_pred_k by apply kseq_position0.
 simpl. case Nat.eqb_spec; lia.
Qed.

Lemma count0_S_position0 k p :
 k<>0 ->
 count (kseq k) 0 (S (position0 k p)) = S p.
Proof.
 intros Hk.
 rewrite count_nbocc, take_S, nbocc_app, <- count_nbocc, kseq_position0.
 rewrite count0_position0 by trivial. simpl. lia.
Qed.

Lemma position0_bounds k n :
  1 < n ->
  exists p, position0 k p < n <= position0 k (S p).
Proof.
 intros. apply incr_function_bounds'; auto. intro. rewrite position0_S. lia.
Qed.

Lemma position0_complete k n :
 k<>0 ->
 kseq k n = 0 -> exists p, n = position0 k p.
Proof.
 intros Hk.
 destruct (Nat.le_gt_cases n 1).
 - intros E. exists 0. unfold position0. simpl.
   inversion_clear H; trivial. replace n with 0 in * by lia.
   rewrite kseq_k_0 in E. lia.
 - destruct (position0_bounds k n) as (p, (Hp, HSp)). lia.
   exists (S p).
   apply Nat.le_lteq in HSp. destruct HSp; trivial.
   exfalso.
   assert (LE : S (position0 k p) <= position0 k (S p)).
   { rewrite position0_S. lia. }
   set (a := position0 k p) in *.
   set (b := position0 k (S p)) in *.
   assert (E : count (kseq k) 0 (S a) = count (kseq k) 0 b).
   { unfold a, b. now rewrite count0_S_position0, count0_position0. }
   assert (P := count_flat (kseq k) 0 (S a) b LE E n). lia.
Qed.

Lemma position0_is_position k : k<>0 -> IsPosition (kseq k) 0 (position0 k).
Proof.
 intros Hk. constructor.
 - red. intros. rewrite position0_S. lia.
 - apply kseq_position0.
 - intros. now apply position0_complete.
Qed.

Lemma position0_cumul k n :
  position0 k n = 1+2*n + cumul (kseq k) n.
Proof.
 unfold position0.
 induction n; trivial.
 rewrite take_S, ksubstSkw_app, app_length.
 rewrite <- Nat.add_succ_l, IHn. simpl length.
 rewrite app_nil_r, ksubstSk_len by apply kseq_letters. simpl. lia.
Qed.

Lemma position0_grows k n :
 k<>0 ->
 position0 k n <= position0 (S k) n.
Proof.
 intros Hk.
 rewrite !position0_cumul.
 destruct (Nat.le_gt_cases n 0) as [Hn|Hn].
 - replace n with 0 by lia. trivial.
 - assert (H := cumul_kseq_grows k n Hn). lia.
Qed.

Lemma count0_decreases k n :
  count (kseq (S k)) 0 n <= count (kseq k) 0 n.
Proof.
 destruct (Nat.eq_dec k 0) as [->|Hk].
 - transitivity n. apply count_subid. rewrite count_all; trivial.
   intros m _. generalize (kseq_letters 0 m). lia.
 - apply (IsPosition_count_anti _ _ _ _ (position0 k) (position0 (S k))).
   + now apply position0_is_position.
   + now apply position0_is_position.
   + intros. now apply position0_grows.
Qed.

Theorem f_grows k n : f k n <= f (S k) n.
Proof.
 destruct (Nat.eq_dec k 0) as [->|Hk].
 - rewrite f_0_div2. rewrite f_1_g. apply g_Sdiv2_le.
 - generalize (count0_decreases k n) (f_count_0 k n) (f_count_0 (S k) n).
   lia.
Qed.

(* TODO: this inequality is actually strict except for a few low n *)

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

Lemma fs_bound k n : fs (S k) (S k) n <= fs k k n <= fs (S k) k n.
Proof.
 split. apply fs_decreases. apply fs_grows.
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

(** Steiner's Thm 1 (direct link between f and kseq) *)

(** Note: in Wolfgang text, substitution [tau_k] is [map S]
    of my [(ksubst (k-1))] and function [F_k] is my [f (k-1)]. *)

Definition knsubstw k j : word -> word := napply (ksubst k) j.

Definition L k j n := length (knsubstw k j (kprefix k n)).

Lemma knsubstw_app k j u v :
  knsubstw k j (u++v) = knsubstw k j u ++ knsubstw k j v.
Proof.
 apply napply_app.
Qed.

Lemma knsubstw_prefixseq_gen k j w :
  PrefixSeq w (kseq k) -> PrefixSeq (knsubstw k j w) (kseq k).
Proof.
 intros.
 apply PrefixSeq_napply; trivial using ksubst_noerase, ksubst_prolong.
Qed.

Lemma knsubstw_prefixseq k j n :
  PrefixSeq (knsubstw k j (kprefix k n)) (kseq k).
Proof.
 apply knsubstw_prefixseq_gen, kprefix_ok.
Qed.

Lemma knsubstw_k k n : knsubstw k k [n] = ksubstk k n.
Proof.
 reflexivity.
Qed.

Lemma knsubstw_Sk k n : knsubstw k (S k) [n] = ksubstSk k n.
Proof.
 reflexivity.
Qed.

Lemma L_incr k j : IncrFun (L k j).
Proof.
 intro n.
 unfold L, knsubstw. rewrite take_S, napply_app, app_length.
 generalize (@napply_mono _ 0 j [kseq k n] (ksubst_noerase k)).
 simpl. lia.
Qed.

Lemma L_lt k j n m : n < m <-> L k j n < L k j m.
Proof.
 apply incr_monoiff. apply L_incr.
Qed.

Lemma L_add k i j n : L k i (L k j n) = L k (i+j) n.
Proof.
 unfold L. f_equal.
 generalize (knsubstw_prefixseq k j n). unfold PrefixSeq. intros <-.
 unfold knsubstw. symmetry. apply napply_add.
Qed.

Lemma L_0 k j : L k j 0 = 0.
Proof.
 unfold L, knsubstw. cbn. now rewrite napply_nil.
Qed.

Lemma L_S k j n :
 L k j (S n) = L k j n + length (knsubstw k j [kseq k n]).
Proof.
 unfold L. now rewrite take_S, knsubstw_app, app_length.
Qed.

Lemma L_k_0 k n : L k 0 n = n.
Proof.
 unfold L, knsubstw. simpl. apply kprefix_length.
Qed.

Lemma L_0_1 n : L 0 1 n = 2*n.
Proof.
 induction n; try easy.
 rewrite L_S, IHn. cbn. unfold ksubst.
 replace (kseq 0 n) with 0 by (generalize (kseq_letters 0 n); lia).
 simpl. lia.
Qed.

Definition Thm1 k j n :=
  0<n -> L k j (Nat.pred (fs k j n)) < n <= L k j (fs k j n).

Lemma steiner_thm1_k0_j1 n : Thm1 0 1 n.
Proof.
 red. rewrite !L_0_1. simpl fs.
 induction n.
 - inversion 1.
 - intros _. rewrite f_S. simpl fs.
   destruct (Nat.eq_dec n 0) as [->|N]; [simpl; lia | lia].
Qed.

Lemma steiner_thm1_aux1 k n :
  Thm1 k 1 n -> L k 1 (f k n) = n \/ kseq k n = 0.
Proof.
  intros IH1.
  destruct (Nat.eq_dec n 0) as [->|Hn]; try now left.
  specialize (IH1 ltac:(lia)). simpl in IH1.
  generalize (knsubstw_prefixseq k 1 (f k n)).
  revert IH1.
  replace (f k n) with (S (Nat.pred (f k n))) at 2 3 4
    by (generalize (@f_nonzero k n); lia).
  rewrite L_S. unfold L.
  rewrite take_S, knsubstw_app. unfold PrefixSeq. rewrite app_length.
  set (w := knsubstw k 1 (kprefix k (Nat.pred (f k n)))).
  set (x := kseq _ _) in *.
  unfold knsubstw. simpl. rewrite app_nil_r.
  unfold ksubst. case Nat.eqb; intros W0 W; simpl in *; try lia.
  destruct (Nat.eq_dec (length w) (n-1)) as [W'|W']; try lia.
  right. rewrite W' in W.
  rewrite Nat.add_succ_r, Nat.add_1_r in W.
  rewrite !take_S, <- app_assoc in W. simpl in W.
  apply app_inv' in W; try easy.
  destruct W as (_,[= _ ->]). f_equal. lia.
Qed.

Lemma steiner_thm1_corestep k n : 2<=n ->
  (forall j, Thm1 k j (n-1)) -> (forall j, Thm1 k j n) -> Thm1 k 1 (S n).
Proof.
 intros Hn IHn1 IHn.
 (* Case k=0 must be handled separately (but it's easy, L is double) *)
 destruct (Nat.eq_dec k 0) as [->|Hk]; [ apply steiner_thm1_k0_j1 | ].
 assert (Hn' : S (n-1) = n) by lia.
 destruct (fs_step k (S k) (n-1)) as [E|E]; rewrite Hn' in E.
 - (* First case : f^^(S k) flat at (n-1) *)
   destruct (steiner_thm1_aux1 k n (IHn 1)) as [EQ|EQ].
   + intros _. simpl. clear IHn1 IHn.
     replace (f k (S n)) with (S (f k n)).
     2:{ rewrite <- Hn' at 1. rewrite !f_S, E.
         generalize (fs_le k (S k) (n-1)). lia. }
     simpl. rewrite L_S, EQ.
     unfold knsubstw. simpl. unfold ksubst. case Nat.eqb; simpl; lia.
   + exfalso.
     specialize (IHn (S k) ltac:(lia)). destruct IHn as (_,IHn).
     apply Nat.le_lteq, or_comm in IHn. destruct IHn as [IHn|IHn].
     * clear IHn1.
       set (m := fs k (S k) n) in *.
       generalize (knsubstw_prefixseq k (S k) (S m)).
       generalize (knsubstw_prefixseq k (S k) m).
       rewrite take_S, knsubstw_app. unfold PrefixSeq. rewrite app_length.
       unfold L in IHn. rewrite <- IHn. intros ->. clear IHn.
       set (x := kseq _ _).
       rewrite knsubstw_Sk, ksubstSk_len, ksubstSk_alt by apply kseq_letters.
       rewrite take_add.
       intros W. apply app_inv_head in W. simpl in W.
       injection W as W _ _. lia.
     * specialize (IHn1 (S k) ltac:(lia)). destruct IHn1 as (IHn1,_).
       rewrite <- E in IHn1.
       replace (fs _ _ _) with (S (Nat.pred (fs k (S k) n))) in IHn.
       2:{ generalize (@fs_nonzero k n (S k)); lia. }
       rewrite L_S in IHn.
       set (m := Nat.pred _) in *.
       generalize (knsubstw_prefixseq k (S k) (S m)).
       generalize (knsubstw_prefixseq k (S k) m).
       rewrite take_S, knsubstw_app. unfold PrefixSeq. rewrite app_length.
       set (x := kseq k m) in *.
       assert (Hx : x <= k) by apply kseq_letters.
       rewrite knsubstw_Sk, ksubstSk_len, ksubstSk_alt in * by trivial.
       fold (L k (S k) m). set (lm := L k (S k) m) in *. intros ->.
       simpl. rewrite take_add.
       intros W. apply app_inv_head in W. simpl in W.
       injection W as _ _ W.
       assert (IN : In 0 (seq 1 x)).
       { rewrite W, <- EQ. apply in_map, in_seq. lia. }
       apply in_seq in IN. lia.
 - (* Second case : f^^(S k) step at (n-1) *)
   intros _. simpl. replace (f k (S n)) with (f k n).
   2:{ rewrite <- Hn' at 1.
       rewrite !f_S, E. generalize (fs_le k (S k) (n-1)). lia. }
   split; [ apply Nat.lt_lt_succ_r, (IHn 1); lia| ].
   assert (E' : f k n = S (f k (n-1))).
   { destruct (f_step k (n-1)) as [E'|E']; rewrite Hn' in *; trivial.
     exfalso. rewrite !iter_S, <- E' in E; lia. }
   rewrite E', L_S.
   assert (HL : L k 1 (f k (n-1)) = n-1).
   { destruct (IHn1 1 ltac:(lia)) as (_,LB).
     destruct (IHn 1 ltac:(lia)) as (UB,_).
     simpl in LB,UB. rewrite E' in UB. simpl in UB. lia. }
   rewrite HL.
   assert (HL' : L k (S k) (fs k (S k) (n-1)) = n-1).
   { destruct (IHn1 (S k) ltac:(lia)) as (_,LB).
     destruct (IHn (S k) ltac:(lia)) as (UB,_).
     rewrite E in UB. simpl in *. lia. }
   clear IHn1 IHn.
   assert (EL := knsubstw_prefixseq k 1 (f k (n-1))).
   assert (EL' := knsubstw_prefixseq k (S k) (fs k (S k) (n-1))).
   red in EL,EL'. unfold L in HL,HL'. rewrite HL,HL' in *. clear HL HL'.
   assert (K0 : kseq k (n-1) = k /\ kseq k n = 0).
   { generalize (knsubstw_prefixseq k (S k) (fs k (S k) n)).
     rewrite E, take_S, knsubstw_app, EL'.
     set (x := kseq _ _).
     unfold PrefixSeq. rewrite app_length, kprefix_length, take_add.
     rewrite knsubstw_Sk, ksubstSk_len, ksubstSk_alt by apply kseq_letters.
     simpl. rewrite Hn'.
     intro V. apply app_inv_head in V. now injection V as <- <- _. }
   destruct K0 as (K,K').
   generalize (knsubstw_prefixseq k 1 (S (f k n))).
   rewrite E', 2 take_S, !knsubstw_app, EL. clear E E' EL EL'.
   set (x := kseq k (f k (n-1))).
   set (y := kseq k (S _)). clearbody x y.
   unfold knsubstw. simpl. rewrite !app_nil_r. unfold PrefixSeq.
   rewrite !app_length, kprefix_length, <- Nat.add_assoc, <- app_assoc.
   rewrite take_add.
   intros V. apply app_inv_head in V. revert V.
   unfold ksubst.
   case Nat.eqb. intros _; simpl; lia.
   case Nat.eqb; simpl; rewrite Hn'; injection 1; lia.
Qed.

Lemma steiner_thm1_alt k j n : Thm1 k j n.
Proof.
 revert j. induction n as [n IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases n 2) as [Hn|Hn].
 - destruct n as [|[|[|n]]]; try lia.
   + (* n=0 *) unfold Thm1. inversion 1.
   + (* n=1 *)
     unfold Thm1. intros j _. rewrite fs_k_1, L_0. split; auto.
     apply (napply_mono _ 0 j [k]). apply ksubst_noerase. lia.
   + (* n=2 *)
     unfold Thm1. intros [|j] _.
     * simpl. rewrite !L_k_0. lia.
     * rewrite fs_k_2, L_0 by lia. split; auto.
       unfold L,knsubstw. cbn. rewrite ksubst_k. cbn.
       apply (napply_mono _ 0 j [k;0]). apply ksubst_noerase. lia.
 - destruct n; try lia.
   assert (J1 : Thm1 k 1 (S n)).
   { apply steiner_thm1_corestep; try apply IH; lia. }
   intros [|j].
   + (* j=0 *)
     intros _. rewrite !L_k_0. cbn. lia.
   + (* j<>0 *)
     assert (FS : f k (S n) < S n) by (apply f_lt; lia).
     assert (FS0 : 0 < f k (S n)) by (apply f_nonzero; lia).
     specialize (IH (f k (S n)) FS j FS0).
     rewrite <- iter_S in IH.
     destruct IH as (IH1,IH2). apply Nat.lt_le_pred in IH1.
     apply (incr_mono _ (L_incr k 1)) in IH1,IH2.
     rewrite L_add in IH1, IH2. simpl "+" in IH1,IH2.
     unfold Thm1 in *. simpl in J1. lia.
Qed.

Lemma steiner_thm1 k j n m : 0<n ->
  fs k j m = n <-> L k j (n-1) < m <= L k j n.
Proof.
 intros Hn.
 split.
 - intros <-. rewrite Nat.sub_1_r. apply steiner_thm1_alt.
   destruct m; try lia. now rewrite fs_k_0 in *.
 - intros H.
   assert (Hm : 0 < m) by lia.
   assert (H' := steiner_thm1_alt k j m Hm).
   destruct (Nat.lt_trichotomy (fs k j m) n) as [LT|[E|LT]];
    [exfalso|trivial|exfalso].
   + assert (LE : fs k j m <= n-1) by lia.
     apply (incr_mono _ (L_incr k j)) in LE. lia.
   + assert (LE : n <= Nat.pred (fs k j m)) by lia.
     apply (incr_mono _ (L_incr k j)) in LE. lia.
Qed.

(** Said otherwise, [L k j n] is the largest antecedent of [n] by [fs k j],
    and [S (L k j n)] is the least antecedent of [S n]. *)

Lemma fs_L k j n : fs k j (L k j n) = n.
Proof.
 destruct n.
 - now rewrite L_0, fs_k_0.
 - apply steiner_thm1; try lia. split; trivial. apply L_lt; lia.
Qed.

Lemma fs_S_L k j n : fs k j (S (L k j n)) = S n.
Proof.
 apply steiner_thm1; try lia. split.
 - replace (S n - 1) with n; lia.
 - apply L_lt; lia.
Qed.

Lemma fs_rightmost_child_carac k j a n :
  fs k j n = a -> fs k j (S n) = S a <-> n = L k j a.
Proof.
 destruct (Nat.eq_dec a 0) as [->|Ha]; intros E.
 - apply fs_0_inv in E. subst n. now rewrite fs_k_1, L_0.
 - split; intros E'.
   + apply steiner_thm1 in E, E'; try lia.
     replace (S a - 1) with a in *; lia.
   + rewrite E'. apply fs_S_L.
Qed.

Lemma L_k_1_rchild k n : L k 1 n = rchild k n.
Proof.
 rewrite <- rightmost_child_carac. apply (fs_S_L k 1). apply (fs_L k 1).
Qed.

(** Exactly enumerating antecedents of [fs k j], in increasing order *)

Definition fsinv k j n :=
  if n =? 0 then [0]
  else
    let a := L k j (n-1) in
    let b := L k j n in
    seq (S a) (b-a).

Lemma fsinv_spec k j n m : In m (fsinv k j n) <-> fs k j m = n.
Proof.
 unfold fsinv.
 case Nat.eqb_spec; [intros ->|intros Hn].
 - split; simpl.
   + intros [<-|[ ]]. apply fs_k_0.
   + generalize (@fs_nonzero k m j). lia.
 - rewrite in_seq, steiner_thm1; lia.
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
  length (fsinv k j (S n)) = length (knsubstw k j [kseq k n]).
Proof.
 unfold fsinv. simpl. rewrite Nat.sub_0_r, L_S, seq_length. lia.
Qed.

Lemma fsinv_length k j n :
  length (fsinv k j n) =
  match n with 0 => 1 | S n => length (knsubstw k j [kseq k n]) end.
Proof.
 unfold fsinv. destruct n; simpl; trivial. now rewrite <- fsinv_S_length.
Qed.

Lemma knsubstw_kword k j : knsubstw k j [k] = kword k j.
Proof.
 unfold knsubstw. rewrite napply_ksubst_is_kword; try f_equal; lia.
Qed.

Lemma knsubstw_0 k j :
  knsubstw k j [0] = if j <? k then [j] else kword k (j-k).
Proof.
 unfold knsubstw. case Nat.ltb_spec; intros.
 - rewrite ksubst_low0; trivial; lia.
 - rewrite napply_ksubst_is_kword; try f_equal; lia.
Qed.

Lemma knsubstw_0_len k j : length (knsubstw k j [0]) = A k (j-k).
Proof.
 rewrite knsubstw_0. case Nat.ltb_spec; intros; simpl; try apply kword_len.
 replace (j-k) with 0 by lia. trivial.
Qed.

Lemma fsinv_bound k j n : 0<n ->
  A k (j-k) <= length (fsinv k j n) <= A k j.
Proof.
 destruct n; try easy. intros _.
 rewrite fsinv_S_length.
 set (x := kseq k n).
 assert (Hx : x <= k) by apply kseq_letters.
 rewrite <- knsubstw_0_len.
 rewrite <- !kword_len, <- knsubstw_kword.
 unfold knsubstw.
 rewrite <- (ksubst_low0 k x), <- napply_add by trivial.
 rewrite <- (ksubst_low0 k k), <- napply_add by trivial.
 split.
 - apply napply_mono. apply ksubst_noerase. lia.
 - apply napply_mono. apply ksubst_noerase. lia.
Qed.

(** For each k and j, these bounds are reached infinitely often when n vary.
    For instance : *)

Lemma fsinv_1 k j : length (fsinv k j 1) = A k j.
Proof.
 now rewrite fsinv_S_length, kseq_k_0, knsubstw_kword, kword_len.
Qed.

Lemma fsinv_2 k j : length (fsinv k j 2) = A k (j-k).
Proof.
 now rewrite fsinv_S_length, kseq_k_1, knsubstw_0_len.
Qed.

(** Page 2 of W. Steiner's text *)

Lemma steiner_eqn2bis k n : (* with additions instead of subtractions *)
  L (S k) (S (S k)) n + L k k n = L (S k) (S k) n + L k (S k) n.
Proof.
 induction n.
 - now rewrite !L_0.
 - rewrite !L_S, !knsubstw_Sk, !knsubstw_k, !ksubstk_len, !ksubstSk_len
     by apply kseq_letters. lia.
Qed.

Definition C k i n := count (kseq k) i n.

Lemma steiner_eqn3 k n : L k 1 n = n + C k k n.
Proof.
 induction n; [easy|].
 rewrite L_S, IHn. unfold C. cbn. unfold ksubst.
 case Nat.eqb; simpl; lia.
Qed.

Lemma Lkk_positionk k n : L k k n = positionk k n.
Proof.
 unfold L, positionk, knsubstw, ksubstkw.
 replace k with (1*k) at 2 by lia.
 now rewrite <- napply_ksubstk.
Qed.

Lemma steiner_eqn4 k n : 0<n ->
  L k k (C k k n - 1) < n <= L k k (C k k n).
Proof.
 intros. rewrite !Lkk_positionk. now apply positionk_bounds'.
Qed.

Lemma steiner_eqn4_coro k n : fs k k n = C k k n.
Proof.
 apply fs_count_k.
Qed.

Lemma len_knsubstw_low k j : j <= S k ->
  length (knsubstw k j [k]) = j+1.
Proof.
 intros Hj. unfold knsubstw.
 destruct (Nat.eq_dec j (S k)) as [->|Hj'].
 - fold (ksubstSk k k). rewrite ksubstSk_len; lia.
 - rewrite <- ksubst_pearl by lia.
   fold (ksubstk k j). rewrite ksubstk_len; lia.
Qed.

Lemma len_knsubstw_low_le k j x : j <= S k -> x <= k ->
 length (knsubstw k j [x]) <= j+1.
Proof.
 intros.
 rewrite <- (len_knsubstw_low k j) by lia.
 unfold knsubstw.
 rewrite <- (ksubst_low0 k x), <- napply_add by lia.
 rewrite <- (ksubst_low0 k k), <- napply_add by lia.
 apply napply_mono. apply ksubst_noerase. lia.
Qed.

Lemma steiner_prop2 k n :
 L (S k) 1 n <= L k 1 n
 /\ (0<n -> forall j, j<=S k -> L k j n < L (S k) (S j) n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 destruct (Nat.eq_dec n 0) as [->|N0]; [easy|].
 destruct (Nat.eq_dec n 1) as [->|N1].
 { split.
   - unfold L. unfold kprefix. simpl. rewrite !kseq_k_0.
     unfold knsubstw. simpl. rewrite !ksubst_k. simpl. trivial.
   - intros _. intros j Hj.
     rewrite !L_S, !L_0, !kseq_k_0, !len_knsubstw_low; lia. }
 split.
 - rewrite !steiner_eqn3.
   destruct (Nat.lt_ge_cases (C k k n) (C (S k) (S k) n)); try lia.
   exfalso.
   assert (L k k (C k k n) < L (S k) (S k) (C k k n)).
   { destruct (Nat.eq_dec k 0) as [->|Hk].
     - cbn. unfold C. rewrite count_all.
       2:{ intros m _. generalize (kseq_letters 0 m). lia. }
       rewrite kprefix_length.
       destruct n; try easy. cbn. set (w := map _ _).
       generalize (apply_grow (ksubst 1) w (ksubst_noerase 1)).
       unfold w at 1; rewrite map_length, seq_length. lia.
     - apply IH; try lia; unfold C; rewrite <- fs_count_k.
       + apply fs_lt; lia.
       + apply fs_nonzero; lia. }
   destruct (steiner_eqn4 k n) as (_,E1); try lia.
   destruct (steiner_eqn4 (S k) n) as (E3,_); try lia.
   assert (E2 : C k k n <= C (S k) (S k) n - 1) by lia.
   apply (incr_mono _ (L_incr (S k) (S k))) in E2.
   lia.
 - intros _. destruct n; try easy.
   destruct (Nat.eq_dec (kseq (S k) n) (S k)) as [E|N].
   + intros j Hj. rewrite !L_S, E.
     rewrite len_knsubstw_low by lia.
     assert (Hx := kseq_letters k n).
     set (x := kseq k n) in *.
     generalize (len_knsubstw_low_le k j x Hj Hx).
     destruct (IH n) as (_,IH'); try lia.
     specialize (IH' ltac:(lia) j Hj).
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
     { rewrite <- E'. rewrite steiner_eqn3.
       generalize (count_k_nz (S k) l). unfold C. lia. }
     destruct (IH l Hl) as (IH5,IH6). clear IH. rewrite E' in IH5.
     specialize (IH6 ltac:(lia)).
     assert (LT : forall j, j <= k -> L k j (S n) < L (S k) (S j) (S n)).
     { intros j Hj. specialize (IH6 (S j) ltac:(lia)).
       rewrite <- E' at 2. rewrite L_add, Nat.add_1_r.
       eapply Nat.le_lt_trans; [|apply IH6].
       rewrite <- (Nat.add_1_r j), <- L_add. apply incr_mono; trivial.
       apply L_incr. }
     intros j Hj. destruct (Nat.eq_dec j (S k)) as [->|Hj'].
     * generalize (steiner_eqn2bis k (S n)).
       specialize (LT k (Nat.le_refl k)). lia.
     * apply LT. lia.
Qed.

Lemma steiner_prop2_eqn5 k n : L (S k) 1 n <= L k 1 n.
Proof.
 apply steiner_prop2.
Qed.

Lemma steiner_prop2_eqn6 k j n :
 j <= S k -> 0 < n -> L k j n < L (S k) (S j) n.
Proof.
 intros. now apply steiner_prop2.
Qed.

Lemma fs_decreases_gen k j n :
 j <= S k -> fs (S k) (S j) n <= fs k j n.
Proof.
 intros Hj.
 destruct (Nat.eq_dec n 0) as [->|Hn].
 - now rewrite !fs_k_0.
 - apply Nat.nlt_ge. intros LT.
   set (m := fs k j n) in *.
   assert (Hm : 0 < m). { apply fs_nonzero. lia. }
   assert (E6 := steiner_prop2_eqn6 k j m Hj Hm).
   destruct (steiner_thm1_alt k j n) as (_,E1); try lia.
   fold m in E1.
   assert (LE : m <= Nat.pred (fs (S k) (S j) n)) by lia.
   apply (incr_mono _ (L_incr (S k) (S j))) in LE.
   destruct (steiner_thm1_alt (S k) (S j) n) as (E1',_); lia.
Qed.

Lemma fs_bound_gen k j n :
 j <= S k -> fs k j n <= fs (k-1) (j-1) n <= fs k (j-1) n.
Proof.
 destruct k, j; try easy.
 - inversion 1. simpl. split; trivial. apply f_le.
   simpl. split; trivial. rewrite Nat.sub_0_r. apply f_le.
 - replace (S k - 1) with k by lia.
   replace (S j - 1) with j by lia.
   split. apply fs_decreases_gen; lia. apply fs_grows_gen; lia.
Qed.

Lemma fs_bound_gen' k j n :
 j <= k+2 -> fs k j n <= fs (S k) j n <= fs k (j-1) n.
Proof.
 destruct j; try easy.
 split. apply fs_grows_gen; lia.
 replace (S j - 1) with j by lia. apply fs_decreases_gen; lia.
Qed.
