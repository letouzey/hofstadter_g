Require Import MoreFun MoreList FunG GenFib GenG Words.
Import ListNotations.

(** Follow-up of [Words.v] *)

(** The substitution [(ksubst k)^k] is quite interesting :
    as for [ksubst k], its infinite word is also [kseq k], but
    it produces it by blocks starting by all the [k] letters. *)

Definition ksubstk k n := napply (ksubst k) k [n].

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
   unfold letter in *. rewrite E.
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

(** More on PrefixSeq *)

Lemma PrefixSeq_incl w u v :
  length u <= length v -> PrefixSeq u w -> PrefixSeq v w -> Prefix u v.
Proof.
 unfold PrefixSeq. intros H -> ->. now apply Prefix_take.
Qed.

Lemma PrefixSeq_alt s a :
  NoErase s -> Prolong s a ->
  forall u,
    PrefixSeq u (subst2seq s a) <-> Prefix u (napply s (length u) [a]).
Proof.
 intros NE PR u. unfold PrefixSeq.
 split.
 - generalize (length u). intros n Hu.
   rewrite Prefix_nth_nat. intros m b Hm.
   subst u. rewrite take_length in Hm.
   rewrite take_nth by trivial.
   rewrite <- subst2seq_indep; trivial; lia.
 - set (n := length u). intros Hu.
   symmetry. apply take_carac; trivial.
   intros m b Hm. rewrite Prefix_nth_nat in Hu.
   rewrite Hu by trivial. symmetry. apply subst2seq_indep; trivial. lia.
Qed.

Lemma PrefixSeq_alt' s a :
  NoErase s -> Prolong s a ->
  forall u,
    PrefixSeq u (subst2seq s a) <-> exists m, Prefix u (napply s m [a]).
Proof.
 intros NE PR u. rewrite PrefixSeq_alt by trivial.
 split.
 - intros H. now exists (length u).
 - intros (m,H). destruct (Nat.le_gt_cases m (length u)) as [L|L].
   + eapply Prefix_trans; eauto. apply napply_prefix_mono; trivial.
   + eapply Prefix_Prefix; eauto.
     * apply Nat.lt_le_incl, noerase_prolong_napply_len; trivial.
     * apply napply_prefix_mono; trivial; lia.
Qed.

Lemma PrefixSeq_apply s a :
  NoErase s -> Prolong s a ->
  forall u,
   PrefixSeq u (subst2seq s a) ->
   PrefixSeq (apply s u) (subst2seq s a).
Proof.
  intros NE PR u.
  rewrite !PrefixSeq_alt' by trivial.
  intros (m,(u',E)). exists (S m).
  rewrite napply_alt, <- E, apply_app. now exists (apply s u').
Qed.

Lemma PrefixSeq_napply s a n :
  NoErase s -> Prolong s a ->
  forall u,
   PrefixSeq u (subst2seq s a) ->
   PrefixSeq (napply s n u) (subst2seq s a).
Proof.
  intros NE PR.
  induction n; trivial.
  intros u Hu. simpl. apply IHn, PrefixSeq_apply; trivial.
Qed.

(** PrefixSeq and kseq : *)

Lemma ksubst_prefix k u :
 PrefixSeq u (kseq k) -> PrefixSeq (apply (ksubst k) u) (kseq k).
Proof.
  apply PrefixSeq_apply. apply ksubst_noerase. apply ksubst_prolong.
Qed.

Lemma ksubstk_prefix k u :
 PrefixSeq u (kseq k) -> PrefixSeq (apply (ksubstk k) u) (kseq k).
Proof.
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

Definition positionk k p := length (apply (ksubstk k) (take p (kseq k))).

Lemma positionk_S k p : positionk k (S p) = positionk k p + S (kseq k p).
Proof.
 unfold positionk.
 rewrite take_S, apply_app, app_length; simpl.
 now rewrite app_nil_r, ksubstk_len by apply kseq_letters.
Qed.

Lemma kseq_positionk k p : kseq k (positionk k p) = k.
Proof.
 rewrite <- (take_nth (kseq k) (positionk k (S p)) _ k).
 2:{ rewrite positionk_S; lia. }
 set (u := take (S p) (kseq k)).
 assert (Hu : PrefixSeq u (kseq k)).
 { red. unfold u. f_equal. now rewrite take_length. }
 apply ksubstk_prefix in Hu. red in Hu. unfold u at 2 in Hu.
 fold (positionk k (S p)) in Hu. rewrite <- Hu.
 clear Hu. unfold u. rewrite take_S, apply_app.
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
  nbocc k (apply (ksubstk k) u) = length u.
Proof.
 induction u; trivial.
 simpl. intros Hu. inversion_clear Hu.
 rewrite nbocc_app, IHu by trivial.
 rewrite ksubstk_alt by trivial. simpl.
 rewrite Nat.eqb_refl. rewrite nbocc_notin; try lia.
 rewrite in_seq. lia.
Qed.

Lemma take_kseq_letters k n :
  Forall (fun a => a <= k) (take n (kseq k)).
Proof.
 induction n.
 - unfold take. simpl. constructor.
 - rewrite take_S. apply Forall_app. split; trivial.
   repeat constructor. apply kseq_letters.
Qed.

Lemma countk_positionk k p :
 count (kseq k) k (positionk k p) = p.
Proof.
 rewrite count_nbocc.
 set (u := take p (kseq k)).
 assert (Hu : PrefixSeq u (kseq k)).
 { red. unfold u. f_equal. now rewrite take_length. }
 apply ksubstk_prefix in Hu. red in Hu. unfold u at 2 in Hu.
 fold (positionk k p) in Hu. unfold letter in Hu. rewrite <- Hu.
 rewrite nbocc_ksubstk. unfold u. apply take_length.
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
 rewrite take_S, apply_app, app_length, IHn. simpl.
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

Lemma length_apply_ksubst k m :
  length (apply (ksubst k) (take m (kseq k))) = m + count (kseq k) k m.
Proof.
 induction m; trivial.
 rewrite take_S, apply_app, app_length, IHm. simpl. unfold ksubst.
 case Nat.eqb_spec; simpl; lia.
Qed.

Lemma listsum_ksubst k u :
  listsum (apply (ksubst k) u) + nbocc k u = listsum u + length u.
Proof.
 induction u; trivial.
 simpl. rewrite listsum_app. unfold ksubst at 1.
 case Nat.eqb_spec; simpl; try lia.
Qed.

Lemma listsum_ksubst' k u :
  listsum (apply (ksubst k) u) = listsum u + length u - nbocc k u.
Proof.
 generalize (nbocc_le_length k u) (listsum_ksubst k u). lia.
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
       assert (E1 : m <= positionk k (a k m)) by (apply positionk_bounds'; trivial).
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
     assert (E1 : S n <= length (apply (ksubst k) (take m (kseq k)))).
     { rewrite length_apply_ksubst. fold (a k m).
       transitivity (m + a (S k) m); try lia.
       unfold a. now rewrite <- length_apply_ksubst, <- E, take_length. }
     assert (P : Prefix (take (S n) (kseq k)) (apply (ksubst k) (take m (kseq k)))).
     { apply (PrefixSeq_incl (kseq k)).
       - now rewrite take_length.
       - red. now rewrite take_length.
       - apply ksubst_prefix. red. now rewrite take_length. }
     apply listsum_prefix in P.
     rewrite <- cumul_alt in P.
     eapply Nat.le_lt_trans; [ apply P | ].
     rewrite cumul_alt. unfold letter in E. rewrite E.
     rewrite !listsum_ksubst'.
     generalize (nbocc_le_length k (take m (kseq k))).
     generalize (nbocc_le_length (S k) (take m (kseq (S k)))).
     rewrite <- !cumul_alt, !take_length, <- !count_nbocc.
     fold (a k m). fold (a (S k) m).
     lia.
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

Lemma fs_decreases k n :
 (f (S k) ^^ (S k)) n <= (f k ^^ k) n.
Proof.
 rewrite !fs_count_k. apply countk_decreases.
Qed.

(** Let's now count letter 0 *)

(** The substitution [(ksubst k)^(S k)] is also quite interesting :
    its infinite word is also [kseq k], but it produces it by
    blocks starting by all the [k;0] letters. *)

Definition ksubstSk k n := napply (ksubst k) (S k) [n].

Lemma ksubstSk_alt0 k n :
  ksubstSk k n = apply (ksubst k) (apply (ksubstk k) [n]).
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
 simpl (apply _ [n]). rewrite app_nil_r, ksubstk_kword by trivial.
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
  nbocc 0 (apply (ksubstSk k) u) = length u.
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
  PrefixSeq u (kseq k) -> PrefixSeq (apply (ksubstSk k) u) (kseq k).
Proof.
 rewrite <- napply_1.
 rewrite napply_ksubstSk. apply PrefixSeq_napply.
 apply ksubst_noerase.
 apply ksubst_prolong.
Qed.

Definition position0 k p := S (length (apply (ksubstSk k) (take p (kseq k)))).

Lemma position0_S k p : position0 k (S p) = position0 k p + kseq k p + 2.
Proof.
 unfold position0.
 rewrite take_S, apply_app, app_length; simpl.
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
 clear Hu. unfold u. rewrite take_S, apply_app.
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
 unfold letter in *. rewrite <- Hu.
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
 rewrite take_S, apply_app, app_length.
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
