From Coq Require Import List Arith Lia Reals Lra.
Import ListNotations.
Require Import MoreTac MoreFun MoreList.
Require GenFib GenG Fast Words WordGrowth MoreLim.
Require Mu Freq.

(** * Article1.v *)

(** This file is a wrapper around the rest of the current Coq development,
    for regrouping in one place all the results presented in the article:

      Pointwise order of generalized Hofstadter functions G, H and beyond.
      Pierre Letouzey, Shuo Li, Wolfgang Steiner. Preprint, 2024.

    Nota Bene : the current idea is to machine-check the statements
    presented in the article. The original proofs made in Coq are normally
    quite close from the ones presented in the article, but may differ
    here and there. Moreover, in the other files we use words in the alphabet
    0..k-1 instead of the alphabet 1..k used here and in the article.
*)

(** ** The definitions

    We simply refer to code defined elsewhere, but prove its adequacy
    below. For substitution and words, we adapt the alphabet on the fly.
    Note that f^^n is f composed n times with itself. See
    for instance lemma iter_S : (f ^^ S n) p = (f ^^ n) (f p) *)

Definition F := Fast.Nat.f.

Definition dF k j n := ((F k)^^j) (n+1) - ((F k)^^j) n.

Definition A := GenFib.A.

Definition subst_τ k w := map S (Words.ksubstw k (map Nat.pred w)).

Definition word_x k n := S (Words.kseq k n).

Definition L := Fast.Nat.rchild.

(** Equivalence with earlier definitions, on which the actual proofs have
    been made. Fast.Nat.f is compatible with GenG.f, while computing
    faster. Anyway, for really big computations, rather consider Fast.f
    and Fast.A that work on the N datatype, or Fast.f_array that
    tabulates f at once on an interval. *)

Lemma F_alt k n : F k n = GenG.f k n.
Proof.
 apply Fast.Nat.f_alt.
Qed.

Lemma Fs_alt k p n : (F k ^^p) n = GenG.fs k p n.
Proof.
 apply iter_ext, F_alt.
Qed.

Lemma L_alt k n : L k n = WordGrowth.L k 1 n.
Proof.
 rewrite Fast.Nat.rchild_alt. symmetry. apply WordGrowth.L_k_1_rchild.
Qed.

Lemma L_iter k j n : ((L k)^^j) n = WordGrowth.L k j n.
Proof.
 unfold L. rewrite WordGrowth.L_iter. apply iter_ext, L_alt.
Qed.

(** Beware, [A 0] and [subst_τ 0] and [word_x 0] and [L 0] are arbitrary
    (and actually equal to [A 1], [subst_τ 1] and [word_x 1] and [L 1]). *)

(** [F 0] is non-recursive, flat except at 0. Most of the results
    have a [k>0] precondition, just as in the article, but
    a few statements do not need this precondition *)

Lemma F0_alt n : F 0 n = Nat.min 1 n.
Proof.
 now rewrite F_alt, GenG.f_0.
Qed.

Lemma F0_F0 n : F 0 (F 0 n) = F 0 n.
Proof.
 rewrite !F0_alt. lia.
Qed.

Lemma F0_Sj j n : (F 0^^S j) n = F 0 n.
Proof.
 revert n. induction j; intros; trivial. now rewrite iter_S, IHj, F0_F0.
Qed.

Lemma F0_j j n : (F 0^^j) n = if j =? 0 then n else F 0 n.
Proof.
 destruct j; trivial. now rewrite F0_Sj.
Qed.

(** Justify that these definitions are indeed adequate, by showing
    they satisfy the various defining equations. *)

Lemma F_0 k : F k 0 = 0.
Proof.
 now rewrite F_alt.
Qed.

Lemma F_rec k n : F k n = n - ((F k)^^k) (n-1).
Proof.
 rewrite F_alt, Fs_alt.
 destruct n as [|n]; try easy.
 rewrite GenG.f_S. do 2 f_equal; lia.
Qed.

Lemma A_init k p : p<=k -> A k p = p+1.
Proof.
 intros Hp. unfold A. rewrite GenFib.A_base; lia.
Qed.

Lemma A_rec k p : 0<k -> k<=p -> A k p = A k (p-1) + A k (p-k).
Proof.
 intros K Hp. unfold A. destruct p as [|p]; try lia.
 rewrite GenFib.A_S. do 2 f_equal; lia.
Qed.

Lemma subst_τ_k k : 0<k -> subst_τ k [k] = [k;1].
Proof.
 intros K. unfold subst_τ. cbn. rewrite <- Nat.sub_1_r.
 rewrite Words.ksubst_km1. cbn. f_equal; lia.
Qed.

Lemma subst_τ_nk k i : 0<k -> 0<i<k -> subst_τ k [i] = [i+1].
Proof.
 intros K I. unfold subst_τ. cbn. rewrite <- Nat.sub_1_r.
 unfold Words.ksubst. case Nat.eqb_spec; intros; try lia.
 cbn. f_equal. lia.
Qed.

Lemma take_word_x k n :
  take n (word_x k) = map S (Words.kprefix k n).
Proof.
 unfold word_x, take. now rewrite map_map.
Qed.

Lemma subst_τ_j_eqn k j w :
 Forall (lt 0) w ->
 (subst_τ k ^^j) w = map S (WordGrowth.knsub k j (map Nat.pred w)).
Proof.
 intros Hw.
 induction j.
 - cbn. rewrite map_map. symmetry. erewrite map_ext_in. apply map_id.
   intros x Hx. rewrite Forall_forall in Hw. apply Hw in Hx. lia.
 - simpl. rewrite IHj. unfold subst_τ. rewrite map_map. cbn. rewrite map_id.
   f_equal. unfold WordGrowth.knsub, Words.ksubstw.
   set (sub := Words.ksubst k).
   change (Words.apply sub) with (Words.napply sub 1).
   rewrite <- !Words.napply_add. f_equal. lia.
Qed.

Lemma L_eqn_gen k j n :
  ((L k)^^j) n = length (((subst_τ k)^^j) (take n (word_x k))).
Proof.
 rewrite subst_τ_j_eqn, map_length.
 - rewrite L_iter. now rewrite take_word_x, map_map, map_id.
 - rewrite take_word_x. apply Forall_forall.
   intros x. rewrite in_map_iff. intros (y & <- & _). lia.
Qed.

Lemma L_eqn k n : L k n = length (subst_τ k (take n (word_x k))).
Proof.
 apply (L_eqn_gen k 1).
Qed.

(** Justifying [word_x] : *)

Lemma word_x_0 k : 0<k -> word_x k 0 = k.
Proof.
 intros K. unfold word_x. rewrite Words.kseq_k_0. lia.
Qed.

Lemma word_x_subst k j n :
  ((subst_τ k)^^j) (take n (word_x k)) = take (((L k)^^j) n) (word_x k).
Proof.
 rewrite subst_τ_j_eqn, !take_word_x, L_iter.
 2:{ apply Forall_forall. intros x. rewrite take_word_x, in_map_iff.
     intros (y & <- & _). lia. }
 f_equal. rewrite map_map, map_id. apply WordGrowth.knsub_kprefix.
Qed.

(** Particular cases:
    - n=1 : All words [(subst_τ k)^^j [k]] are prefixes of [word_x k]
      Their lengths are [(L k ^^j) 1] (hence a strictly growing sequence).
    - j=1 : Substituting any prefix of [word_x k] gives another prefix of
      [word_x k]. The new length is [L k 1] of the initial length
      (hence longer).
*)

Lemma word_x_subst_n1 k j : 0<k ->
  ((subst_τ k)^^j) [k] = take ((L k ^^j) 1) (word_x k).
Proof.
 intros K. rewrite <- word_x_subst; trivial. f_equal. cbn.
 now rewrite word_x_0.
Qed.

Lemma word_x_subst_j1 k n :
  subst_τ k (take n (word_x k)) = take (L k n) (word_x k).
Proof.
 apply (word_x_subst k 1).
Qed.

Lemma word_x_letters k n : 0<k -> 1 <= word_x k n <= k.
Proof.
 unfold word_x. generalize (Words.kseq_letters k n). lia.
Qed.

(** Properties stated in the article *)

Lemma F_le_id k n : 0 <= F k n <= n.
Proof.
 rewrite F_alt. split. lia. apply GenG.f_le.
Qed.

Lemma Fkj_le_id k j n : 0 <= ((F k)^^j) n <= n.
Proof.
 rewrite Fs_alt. split. lia. apply GenG.fs_le.
Qed.

(** Prop. 2.1 *)

Lemma Fkj_0 k j : ((F k)^^j) 0 = 0.
Proof.
 rewrite Fs_alt. apply GenG.fs_k_0.
Qed.

Lemma Fkj_1 k j : ((F k)^^j) 1 = 1.
Proof.
 rewrite Fs_alt. apply GenG.fs_k_1.
Qed.

Lemma Fkj_2 k j : 1<=j -> ((F k)^^j) 2 = 1.
Proof.
 rewrite Fs_alt. now apply GenG.fs_k_2.
Qed.

Lemma Fkj_nonzero k j n : 1 <= n <-> 1 <= (F k ^^j) n.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - rewrite F0_j. destruct j; simpl. lia. rewrite F0_alt. lia.
 - rewrite Fs_alt. split.
   + generalize (@GenG.fs_nonzero k n j). lia.
   + destruct n; try lia. now rewrite GenG.fs_k_0.
Qed.

Lemma Fkj_lt_id k j n : 1<=j -> (2<=n <-> ((F k)^^j) n < n).
Proof.
 intros Hj.
 destruct (Nat.eq_dec k 0) as [->|K].
 - rewrite F0_j. destruct j; simpl. lia. rewrite F0_alt; lia.
 - rewrite Fs_alt. split.
   + intros. apply GenG.fs_lt; lia.
   + destruct n as [|[|n]]; try lia. rewrite GenG.fs_k_1. lia.
Qed.

Lemma dF_eqn k n : 0<n -> dF k 1 n = 1 - dF k k (n-1).
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - unfold dF. simpl. rewrite !F0_alt.
   replace (n-1+1-(n-1)) with 1; lia.
 - intros N. unfold dF. simpl Nat.iter.
   rewrite !F_rec. replace (n+1-1) with n by lia.
   replace (n-1+1) with n by lia.
   assert (((F k)^^k) (n-1) <= ((F k)^^k) n).
   { rewrite !Fs_alt. apply GenG.fs_mono. lia. }
   generalize (Fkj_le_id k k n) (Fkj_le_id k k (n-1)). lia.
Qed.

Lemma dF_step k j n : dF k j n = 0 \/ dF k j n = 1.
Proof.
 unfold dF. rewrite !Fs_alt, Nat.add_1_r.
 destruct (GenG.fs_step k j n); lia.
Qed.

Lemma Fkj_mono k j n m : n <= m -> ((F k)^^j) n <= ((F k)^^j) m.
Proof.
 rewrite !Fs_alt. now apply GenG.fs_mono.
Qed.

Lemma Fkj_onto k j : 0<k -> forall n, exists m, ((F k)^^j) m = n.
Proof.
 intros K. setoid_rewrite Fs_alt.
 induction j; intros n.
 - now exists n.
 - destruct (IHj n) as (p,Hp).
   destruct (@GenG.f_onto k p lia) as (m,Hm).
   exists m. now rewrite iter_S, Hm, Hp.
Qed.

Lemma subst_τ_k_km1 k i : 1 <= i <= k ->
  (subst_τ k^^(k-1)) [i] = k :: seq 1 (i-1).
Proof.
 intros Hi.
 rewrite subst_τ_j_eqn. 2:repeat constructor; lia.
 simpl. rewrite WordGrowth.knsub_km1_alt, Words.kword_low by lia.
 simpl. f_equal; try lia. rewrite seq_shift. f_equal; lia.
Qed.

Lemma subst_τ_k_k k i : 1 <= i <= k ->
  (subst_τ k^^k) [i] = k :: seq 1 i.
Proof.
 intros Hi.
 rewrite subst_τ_j_eqn. 2:repeat constructor; lia.
 simpl. rewrite WordGrowth.knsub_k_alt, Words.kword_low by lia.
 simpl. f_equal; try lia. rewrite seq_shift.
 now replace i with (S (Nat.pred i)) at 2 by lia.
Qed.

(** Prop 2.2 *)

Lemma subst_τ_j_k_alt k j : 0<k ->
  (subst_τ k ^^j) [k] = map S (Words.kword k j).
Proof.
 intros Hk. rewrite subst_τ_j_eqn. 2:repeat constructor; lia.
 f_equal. simpl. replace (Nat.pred k) with (k-1) by lia.
 now apply WordGrowth.knsub_kword.
Qed.

Lemma subst_τ_low k j : 1 <= k -> j <= k ->
  (subst_τ k ^^j) [k] = k :: seq 1 j.
Proof.
 intros. rewrite subst_τ_j_k_alt, Words.kword_low by lia.
 simpl. f_equal; try lia. now rewrite seq_shift.
Qed.

Lemma subst_τ_rec k j : 1 <= k <= j ->
  (subst_τ k ^^j) [k] = (subst_τ k ^^(j-1)) [k] ++ (subst_τ k ^^(j-k)) [k].
Proof.
 intros. rewrite !subst_τ_j_k_alt by lia.
 rewrite Words.kword_eqn by lia. now rewrite map_app.
Qed.

(** Prop 2.3 *)

(** first point : see L_eqn_gen *)

Lemma L_0 k j : (L k ^^j) 0 = 0.
Proof.
 rewrite L_iter. now rewrite WordGrowth.L_0.
Qed.

Lemma L_S k j n :
  (L k ^^j) (S n) = (L k ^^j) n + length ((subst_τ k ^^j) [word_x k n]).
Proof.
 assert (H : Forall (lt 0) (take n (word_x k) ++ [word_x k n])).
 { rewrite <- take_S, take_word_x, Forall_forall. intros x.
   rewrite in_map_iff. intros (y & <- & _). lia. }
 assert (H' := H).
 rewrite Forall_app in H'. destruct H' as (H1,H2).
 rewrite !L_eqn_gen, take_S, !subst_τ_j_eqn by auto.
 now rewrite !map_app, !WordGrowth.knsub_app, map_app, app_length.
Qed.

Lemma L_1_alt k j : (L k ^^j) 1 = A k j.
Proof.
 now rewrite L_iter, WordGrowth.Lkj1_A.
Qed.

Lemma L_1_low k j : j <= k -> (L k ^^j) 1 = j+1.
Proof.
 intros. rewrite L_1_alt. unfold A. rewrite GenFib.A_base; lia.
Qed.

Lemma L_1_rec k j : 0 < k <= j ->
 (L k ^^j) 1 = (L k ^^(j-1)) 1 + (L k ^^(j-k)) 1.
Proof.
 intros. rewrite !L_1_alt. unfold A.
 replace j with (S (j-1)) at 1 by lia.
 rewrite GenFib.A_S. do 2 f_equal; lia.
Qed.

Lemma L_incr k j : IncrFun (L k ^^j).
Proof.
 intros n. rewrite !L_iter. apply WordGrowth.L_incr.
Qed.

Lemma L_ge_n k j n : n <= (L k ^^ j) n.
Proof.
 rewrite !L_iter. apply WordGrowth.L_ge_n.
Qed.

Lemma L_gt_n k j n : 0<j -> 0<n -> n < (L k ^^j) n.
Proof.
 rewrite !L_iter. apply WordGrowth.L_gt_n.
Qed.

Lemma L_incr_j k j n : 0<n -> (L k ^^j) n < (L k ^^(S j)) n.
Proof.
 intros. simpl. apply (L_gt_n k 1). lia.
 rewrite <- (L_0 k j). apply incr_strmono; trivial. apply L_incr.
Qed.

(** An extra property, not yet in the article *)

Lemma L_le_2n k n : 0<k -> L k n <= 2*n.
Proof.
 intros K.
 induction n; simpl. now rewrite L_alt.
 assert (E := L_S k 1 n). simpl in E. rewrite E. clear E.
 assert (H := word_x_letters k n K).
 destruct (Nat.eq_dec (word_x k n) k) as [->|NE];
  rewrite ?subst_τ_k, ?subst_τ_nk; simpl; lia.
Qed.

(** Prop 2.4 *)

Lemma Prop_2_4_exists k j m : 0<k -> 0<m ->
 exists n, 0<n /\ (L k ^^j) (n-1) < m <= (L k ^^j) n.
Proof.
 intros.
 destruct (incr_function_bounds' _ (L_incr k j) m) as (n,Hn).
 - now rewrite L_0.
 - exists (S n). replace (S n - 1) with n; lia.
Qed.

Lemma Prop_2_4_unique k j m n n' : 0<k ->
  (L k ^^j) (n-1) < m <= (L k ^^j) n ->
  (L k ^^j) (n'-1) < m <= (L k ^^j) n' ->
  n=n'.
Proof.
 intros.
 generalize (L_incr k j). set (f := L k ^^j) in *. clearbody f.
 intros.
 assert (LT1 : f (n-1) < f n') by lia.
 assert (LT2 : f (n'-1) < f n) by lia.
 apply incr_strmono_iff in LT1, LT2; trivial. lia.
Qed.

(** Section 3 *)

Theorem Thm_3_1_alt k j m : 0<k -> 0<m ->
 (L k ^^ j) ((F k ^^ j) m - 1) < m <= (L k ^^ j) ((F k ^^ j) m).
Proof.
 intros. rewrite !L_iter, !Fs_alt. now apply WordGrowth.steiner_thm.
Qed.

Theorem Thm_3_1_main k j n : 0<k -> 0<n ->
  forall m, (F k ^^j) m = n <-> (L k ^^ j) (n-1) < m <= (L k ^^ j) n.
Proof.
 intros. split.
 - intros <-. apply Thm_3_1_alt; trivial.
   now rewrite (Fkj_nonzero k j m).
 - intros E. apply (Prop_2_4_unique k j m); trivial.
   apply Thm_3_1_alt; trivial. lia.
Qed.

Lemma Fkj_Lkj k j n : 0<k -> (F k ^^j) ((L k ^^j) n) = n.
Proof.
 intros. destruct (Nat.eq_dec n 0) as [->|N].
 - now rewrite L_0, Fkj_0.
 - apply Thm_3_1_main; try lia. split; trivial.
   apply incr_strmono; apply L_incr || lia.
Qed.

Lemma Fkj_S_Lkj k j n : 0<k -> (F k ^^j) (1 + (L k ^^j) n) = 1+n.
Proof.
 intros. apply Thm_3_1_main; try lia.
 replace (1+n-1) with n by lia. split; try lia.
 simpl. apply incr_strmono; apply L_incr || lia.
Qed.

Lemma Fkj_S_Lkjm1 k j n : 0<k -> 0<n ->
 (F k ^^j) (1 + (L k ^^j) (n-1)) = n.
Proof.
 intros. rewrite Fkj_S_Lkj; trivial. lia.
Qed.

Lemma Cor_3_2 k j : 0<k ->
  forall n m, (F k ^^j) n <= m <-> n <= (L k ^^j) m.
Proof.
 intros. destruct (Nat.eq_dec n 0) as [->|N].
 - rewrite Fkj_0; lia.
 - split; intros.
   + etransitivity. 2:apply incr_mono; eauto using L_incr.
     apply Thm_3_1_alt; lia.
   + rewrite <- (Fkj_Lkj k j m) by lia. now apply Fkj_mono.
Qed.

(** Section 4 *)

Module Count.
Definition C k (f:nat->bool) n := length (filter f (take n (word_x k))).
End Count.
Import Count.

Lemma C_le k f n : C k f n <= n.
Proof.
 unfold C. rewrite <- (take_length n (word_x k)) at 2. apply filter_length_le.
Qed.

Lemma Ceqb_count k i n : 1<=i ->
  C k (Nat.eqb i) n = count (Words.kseq k) (i-1) n.
Proof.
 intros.
 induction n; trivial.
 simpl. rewrite <- IHn.
 unfold C. rewrite take_S, filter_app, app_length. simpl. f_equal.
 unfold word_x. repeat case Nat.eqb_spec; simpl; lia.
Qed.

Lemma Cltb_countabove k i n :
  C k (Nat.ltb i) n = count_above (Words.kseq k) i n.
Proof.
 intros.
 induction n; trivial.
 simpl. rewrite <- IHn.
 unfold C. rewrite take_S, filter_app, app_length. simpl. f_equal.
 unfold word_x. case Nat.ltb_spec; case Nat.leb_spec; simpl; lia.
Qed.

Lemma Prop_4_1_a k n : 0<k -> (F k^^(k-1)) n = C k (Nat.eqb k) n.
Proof.
 intros. rewrite Fs_alt, Ceqb_count by lia. apply Words.fs_count_km1.
Qed.

Lemma Prop_4_1_b k j n : j<k -> (F k ^^j) n = C k (Nat.ltb j) n.
Proof.
 intros. rewrite Fs_alt, Cltb_countabove by lia.
 apply WordGrowth.fs_count_above; lia.
Qed.

Lemma Prop_4_1_c k i n : 1<=i<k ->
 (F k ^^(k+i-1)) n = C k (Nat.eqb i) (n+i).
Proof.
 intros. rewrite Fs_alt, Ceqb_count by lia.
 replace (k+i-1) with (k+(i-1)) by lia.
 rewrite WordGrowth.fs_count by lia. f_equal. lia.
Qed.

Lemma Prop_4_2 k n : L k n = n + (F k ^^(k-1)) n.
Proof.
 unfold L. now rewrite Fast.Nat.rchild_alt, Fs_alt.
Qed.

Lemma Lkj_Fkj k n : 0<k -> n <= L k (F k n) <= S n.
Proof.
 intros. rewrite Prop_4_2, <- iter_S. replace (S (k-1)) with k by lia.
 generalize (F_rec k (S n)). replace (S n-1) with n by lia.
 generalize (dF_step k 1 n). unfold dF.
 generalize (Fkj_le_id k k n). rewrite !Nat.add_1_r.
 generalize (Fkj_mono k 1 n (S n)). simpl Nat.iter. lia.
Qed.

Lemma Eqn_4_4_alt k j n : 1<=j<k ->
  (F k ^^(j-1)) n = (F k ^^j) n + C k (Nat.eqb j) n.
Proof.
 intros.
 rewrite !Prop_4_1_b by lia.
 induction n; trivial.
 unfold C in *. rewrite !take_S, !filter_app, !app_length, IHn.
 simpl. do 2 case Nat.ltb_spec; case Nat.eqb_spec; simpl; lia.
Qed.

Lemma Eqn_4_4 k j n : 1<=j<k ->
  (F k ^^(j-1)) n - (F k ^^j) n = C k (Nat.eqb j) n.
Proof.
 intros. rewrite Eqn_4_4_alt; lia.
Qed.

Lemma Prop_4_3 k n : 1<k -> F k n = n - C k (Nat.eqb 1) n.
Proof.
 intros. rewrite <- Eqn_4_4 by lia.
 generalize (Fkj_le_id k 1 n). simpl. lia.
Qed.

Lemma Prop_4_3_alt k n : 1<k -> F k n = C k (fun x => negb (1 =? x)) n.
Proof.
 intros. rewrite Prop_4_3 by trivial.
 assert (C k (Nat.eqb 1) n + C k (fun x => negb (1=?x)) n = n); try lia.
 { induction n; unfold C in *; trivial.
   rewrite take_S, !filter_app, !app_length.
   rewrite Nat.add_shuffle1, IHn. cbn -[Nat.eqb].
   case Nat.eqb; simpl; lia. }
Qed.

Lemma Prop_4_3_dF_carac k n : 1<k ->
  (dF k 1 n = 0 <-> word_x k n = 1).
Proof.
 intros. unfold dF. simpl. rewrite Nat.add_1_r.
 rewrite !Prop_4_3_alt by trivial.
 unfold C. rewrite take_S, filter_app, app_length.
 rewrite Nat.add_comm, Nat.add_sub. cbn -[Nat.eqb].
 case Nat.eqb_spec; simpl; now intuition.
Qed.

Lemma dF_no_two_zeros k n : 0<k -> dF k 1 n = 0 -> dF k 1 (S n) = 1.
Proof.
 intros K. unfold dF. simpl. rewrite !F_alt.
 generalize
   (@GenG.f_nonflat k n lia)
   (@GenG.f_mono k n (1+n))
   (@GenG.f_mono k (1+n) (2+n)).
 rewrite Nat.add_1_r; simpl. lia.
Qed.

Lemma dF_max_k_ones k n : 0<k ->
  (forall p, p<k -> dF k 1 (n+p) = 1) -> dF k 1 (n+k) = 0.
Proof.
 intros K. unfold dF. simpl. setoid_rewrite F_alt.
 intros H.
 assert (E : forall p, p<=k -> GenG.f k (n+p) = GenG.f k n + p).
 { induction p.
   - rewrite Nat.add_0_r; lia.
   - intros P. specialize (H p P).
     rewrite <- (Nat.add_1_r p), Nat.add_assoc.
     generalize (@GenG.f_mono k (n+p) (n+p+1)); lia. }
 rewrite (E k) by lia.
 generalize (@GenG.f_maxsteps k lia n) (@GenG.f_mono k n (n+k+1)). lia.
Qed.

Lemma dF_max_k_ones_example k : 0<k ->
 forall p, p<k -> dF k 1 (2+p) = 1.
Proof.
 intros K p P. unfold dF. simpl. rewrite !F_alt.
 rewrite Nat.add_1_r, !GenG.f_init; lia.
Qed.

(** On the road to Prop 4.4 : *)

Lemma dF_k_0_n k n : dF k 0 n = 1.
Proof.
 unfold dF. simpl. lia.
Qed.

Lemma dF_k_j_0 k j : dF k j 0 = 1.
Proof.
 unfold dF. rewrite !Fs_alt. now rewrite GenG.fs_k_1, GenG.fs_k_0.
Qed.

Lemma Fkj_decr k j n : (F k ^^j) n <= Nat.max 1 (n-j).
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - destruct j. simpl Nat.iter; lia. rewrite F0_Sj. rewrite F0_alt. lia.
 - induction j.
   + simpl Nat.iter. lia.
   + simpl Nat.iter.
     destruct (Nat.le_gt_cases ((F k ^^j) n) 1) as [LE|GT].
     * transitivity (F k 1). now apply (Fkj_mono k 1).
       change (F k 1) with ((F k^^1) 1). rewrite Fkj_1. lia.
     * assert (F k ((F k^^j) n) < (F k^^j) n).
       { apply (Fkj_lt_id k 1); trivial. }
       lia.
Qed.

Lemma Fkj_finally_1 k j n : 0 < n <= S j -> (F k ^^ j) n = 1.
Proof.
 intros. generalize (Fkj_decr k j n) (Fkj_mono k j 1 n).
 rewrite Fkj_1. lia.
Qed.

Lemma dF_diag_0 k n : 0<n -> dF k n n = 0.
Proof.
 intros. unfold dF. rewrite !Fkj_finally_1; lia.
Qed.

Lemma dF_propagates_0 k j n : dF k j n = 0 -> dF k (S j) n = 0.
Proof.
 unfold dF. intros E.
 simpl. replace ((F k ^^j) (n+1)) with ((F k^^j) n); try lia.
 generalize (Fkj_mono k j n (n+1)); lia.
Qed.

Lemma dF_propagates_0' k j j' n : j<=j' -> dF k j n = 0 -> dF k j' n = 0.
Proof.
 induction 1; trivial. intros E. apply dF_propagates_0; auto.
Qed.

Lemma dF_propagates_1 k j n : dF k j n = 1 -> dF k (j-1) n = 1.
Proof.
 destruct j; trivial. replace (S j-1) with j by lia.
 generalize (dF_step k j n) (dF_step k (S j) n) (dF_propagates_0 k j n).
 lia.
Qed.

Definition dF_first_zero := GenG.succrank.

Lemma dF_1_then_0 k j n : k<>0 -> 0<n ->
  dF k j n = if j <? dF_first_zero k n then 1 else 0.
Proof.
 intros K N. unfold dF, dF_first_zero. rewrite !Fs_alt, Nat.add_1_r.
 case Nat.ltb_spec; intros.
 - destruct (@GenG.fs_nonflat_iff k lia j n) as (_,E).
   rewrite E; intuition lia.
 - destruct (@GenG.fs_flat_iff k lia j n) as (_,E).
   rewrite E; intuition lia.
Qed.

Lemma Prop_4_4 k j n : 0<j<k ->
   word_x k n = j <-> dF k (j-1) n = 1 /\ dF k j n = 0.
Proof.
 intros. unfold dF. rewrite !Fs_alt, Nat.add_1_r.
 rewrite <- !Words.kseq_above_p_is_delta_fs; try lia.
 unfold word_x. do 2 case Nat.leb_spec; try lia.
Qed.

Lemma Prop_4_4_k k n : 0<k -> word_x k n = k <-> dF k (k-1) n = 1.
Proof.
 intros. unfold dF. rewrite !Fs_alt, Nat.add_1_r.
 assert (H2 := word_x_letters k n H).
 destruct (Nat.eq_dec k 1) as [->|K].
 - rewrite !Nat.sub_diag. simpl Nat.iter. lia.
 - rewrite <- Words.kseq_above_p_is_delta_fs; try lia.
   unfold word_x in *. case Nat.leb_spec; lia.
Qed.

Local Open Scope R_scope.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.
Import Lim_seq.

(** Section 5 *)

Definition P (k:nat) (x:R) : R := x^k+x-1.
Definition Q (k:nat) (x:R) : R := x^k-x^(k-1)-1.

Definition α : nat -> R := Mu.tau.
Definition β : nat -> R := Mu.mu.

Lemma α_root (k:nat) : k<>O -> P k (α k) = 0.
Proof.
 intros K. unfold P, α. rewrite Mu.tau_carac; trivial. lra.
Qed.

Lemma α_itvl (k:nat) : 1/2 <= α k < 1.
Proof.
 apply Mu.tau_itvl.
Qed.

Lemma α_unique (k:nat) (r:R) : k<>O -> 0<=r -> P k r = 0 -> r = α k.
Proof.
 intros K E Hr. apply Mu.tau_unique; trivial. unfold Mu.Ptau, P in *. lra.
Qed.

Lemma β_root (k:nat) : k<>O -> Q k (β k) = 0.
Proof.
 intros K. unfold Q, β. rewrite Mu.mu_carac; trivial. lra.
Qed.

Lemma β_itvl (k:nat) : 1 < β k <= 2.
Proof.
 apply Mu.mu_itvl.
Qed.

Lemma β_unique (k:nat) (r:R) : k<>O -> 0<=r -> Q k r = 0 -> r = β k.
Proof.
 intros K E Hr. apply Mu.mu_unique; trivial. unfold Q in *. lra.
Qed.

Lemma α_β (k:nat) : β k = 1 / α k.
Proof.
 unfold α, β. rewrite Mu.tau_inv. lra.
Qed.

Lemma α_incr (k:nat) : k<>O -> α k < α (k+1).
Proof.
 intros K. rewrite Nat.add_1_r. now apply Mu.tau_incr.
Qed.

Lemma β_decr (k:nat) : k<>O -> β (k+1) < β k.
Proof.
 intros K. rewrite Nat.add_1_r. now apply Mu.mu_decr.
Qed.

Lemma β_bound (k:nat) : k<>O -> 1+1/k <= β k <= 1+1/sqrt(k).
Proof.
 intros K. unfold Rdiv. rewrite !Rmult_1_l. split.
 - now apply Mu.mu_lower_bound.
 - now apply Mu.mu_upper_bound.
Qed.

Lemma β_bound' (k:nat) : k<>O -> sqrt k <= (β k)^(k-1) <= k.
Proof.
 intros K. split.
 - apply Mu.pow_mu_lower_bound.
 - now apply Mu.pow_mu_upper_bound.
Qed.

Lemma β_limit : is_lim_seq β 1.
Proof.
 apply Mu.mu_limit.
Qed.

Lemma α_limit : is_lim_seq α 1.
Proof.
 apply Mu.tau_limit.
Qed.

(** Section 6 *)

Lemma Fkj_limit (k j : nat) : k<>O ->
  is_lim_seq (fun n => (F k ^^j) n / n) (α k ^j).
Proof.
 intros K.
 assert (H := Freq.Lim_fkj_div_n k j K).
 eapply is_lim_seq_ext; try apply H.
 intros n. simpl. f_equal. now rewrite Fs_alt.
Qed.

Lemma Lkj_limit (k j : nat) : k<>O ->
  is_lim_seq (fun n => (L k ^^j) n / n) (β k ^j).
Proof.
 intros K.
 rewrite α_β. unfold Rdiv at 2. rewrite Rmult_1_l, pow_inv.
 change (Rbar.Finite (/ _)) with (Rbar.Rbar_inv ((α k)^j)).
 eapply is_lim_seq_ext_loc with
     (fun n => / ((F k^^j) ((L k ^^j) n) / (L k ^^j) n)).
 - exists 1%nat. intros n Hn. rewrite Fkj_Lkj by lia. field. split.
   + apply not_0_INR; lia.
   + apply not_0_INR. generalize (L_ge_n k j n). lia.
 - apply is_lim_seq_inv.
   + apply (is_lim_seq_subseq (fun n => (F k ^^j) n / n)).
     * intros P (N,HP). exists N. intros n Hn. apply HP.
       generalize (L_ge_n k j n). lia.
     * now apply Fkj_limit.
   + intros [= E]. generalize (pow_lt (α k) j) (α_itvl k). lra.
Qed.

Lemma freq_i (k i : nat) : (0 < i < k)%nat ->
 is_lim_seq (fun n => C k (Nat.eqb i) n /n) (α k ^(k+i-1)).
Proof.
 intros Hi.
 replace (α k ^(k+i-1)) with (α k ^ (i-1) - α k ^i).
 2:{ replace (k+i-1)%nat with (k+(i-1))%nat by lia. rewrite pow_add.
     replace (α k ^k) with (1 - α k)
      by (generalize (α_root k lia); unfold P; lra).
     replace i with (S (i-1)) at 2 by lia. rewrite <- tech_pow_Rmult. ring. }
 eapply is_lim_seq_ext_loc with
     (fun n => (F k^^(i-1)) n / n - (F k^^i) n / n).
 - exists 1%nat. intros n Hn. rewrite Eqn_4_4_alt by trivial.
   rewrite plus_INR. field. apply not_0_INR. lia.
 - apply is_lim_seq_minus'; apply Fkj_limit; lia.
Qed.

Lemma freq_k k : k<>O ->
 is_lim_seq (fun n => C k (Nat.eqb k) n /n) (α k ^(k-1)).
Proof.
 intros K.
 eapply is_lim_seq_ext; try apply (Fkj_limit k (k-1) K).
 intros. cbn -[INR C]. f_equal. f_equal. apply Prop_4_1_a; lia.
Qed.

Lemma α_km1_βm1 k : α k ^(k-1) = β k - 1.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - simpl. unfold β. simpl. rewrite Mu.mu_0. lra.
 - assert (Hα : α k <> 0). { generalize (α_itvl k); lra. }
   rewrite α_β. apply Rmult_eq_reg_l with (α k); trivial.
   rewrite tech_pow_Rmult. replace (S (k-1)) with k by lia.
   field_simplify; trivial. generalize (α_root k K). unfold P. lra.
Qed.

Lemma freq_k' k : k<>O ->
 is_lim_seq (fun n => C k (Nat.eqb k) n /n) (β k - 1).
Proof.
 intros K. rewrite <- α_km1_βm1. now apply freq_k.
Qed.

Local Close Scope R_scope.

Lemma Fk_lt_FSk_eventually k : k<>O ->
 exists N, forall n, N<=n -> F k n < F (k+1) n.
Proof.
 intros K. setoid_rewrite F_alt. setoid_rewrite Nat.add_1_r.
 apply Freq.fk_lt_fSk_eventually.
Qed.

Lemma fs_lt_fs_eventually k k' j j' : k<>O -> k'<>O ->
 (α k ^j < α k' ^j')%R ->
 exists N, forall n, N<=n -> (F k ^^j) n < (F k' ^^j') n.
Proof.
 intros K K' LT. setoid_rewrite Fs_alt. now apply Freq.fs_lt_fs_eventually.
Qed.

(** Ratio of numbers having a unique antecedent by F.
    Note: remember that [F] is onto (cf. [Fkj_onto]) hence every
    number has at least one antecedent by F. *)

Definition UniqueAntecedentByF k n :=
 forall p q, F k p = n -> F k q = n -> p = q.

Definition uniqueAntecedentByF k n :=
  (n =? 0) || (S (L k (n-1)) =? L k n).

Lemma UniqueAntecedentByF_equiv k : 0<k ->
 forall n, UniqueAntecedentByF k n <-> uniqueAntecedentByF k n = true.
Proof.
 intros K n.
 unfold uniqueAntecedentByF; rewrite orb_true_iff, !Nat.eqb_eq. split.
 - intros H. destruct n as [|n].
   + now left.
   + right. apply H.
     * apply (Thm_3_1_main k 1); auto; simpl; try lia. split; try lia.
       rewrite Nat.sub_0_r. apply incr_strmono. apply (L_incr k 1). lia.
     * now apply (Fkj_Lkj k 1).
 - intros [H|H] p q Hp Hq.
   + subst n. generalize (Fkj_nonzero k 1 p) (Fkj_nonzero k 1 q). simpl. lia.
   + destruct n as [|n]. simpl in *; lia.
     change (F k p) with ((F k ^^1) p) in Hp.
     rewrite (Thm_3_1_main k 1) in Hp by lia.
     change (F k q) with ((F k ^^1) q) in Hq.
     rewrite (Thm_3_1_main k 1) in Hq by lia.
     simpl in *. lia.
Qed.

Definition U k n := length (filter (uniqueAntecedentByF k) (seq 0 n)).

Lemma Prop_6_3_a k n : 0<k -> U k n = 2*n - 1 - L k (n-1).
Proof.
 intros K.
 assert (U k n + L k (n-1) = 2*n-1); try lia.
 { induction n. now rewrite L_alt.
   unfold U in *. rewrite seq_S, filter_app, app_length. simpl.
   rewrite Nat.add_0_r, !Nat.sub_0_r.
   unfold uniqueAntecedentByF at 2.
   case Nat.eqb_spec; intros N. subst n; simpl in *; lia.
   case Nat.eqb_spec; intros E; simpl. lia.
   assert (H := L_S k 1 (n-1)). simpl in H.
   replace (S (n-1)) with n in H by lia.
   assert (HL := word_x_letters k (n-1) K).
   destruct (Nat.eq_dec (word_x k (n-1)) k) as [E'|NE].
   - rewrite E' in *. rewrite subst_τ_k in H by trivial. simpl in H. lia.
   - rewrite subst_τ_nk in H by lia. simpl in H. lia. }
Qed.

Lemma Prop_6_3_b k n : 0<k -> U k n = n - (F k ^^(k-1)) (n-1).
Proof.
 intros K. rewrite Prop_6_3_a by trivial. rewrite Prop_4_2. lia.
Qed.

Lemma U_limit k : k<>0 -> (is_lim_seq (fun n => U k n / n) (2 - β k))%R.
Proof.
 intros K.
 replace (2 - β k)%R with (1-α k ^(k-1)*1)%R
   by (generalize (α_km1_βm1 k); lra).
 eapply is_lim_seq_incr_1, is_lim_seq_incr_1, is_lim_seq_ext;
 try rewrite <- is_lim_seq_incr_1 with
  (u:=(fun n => 1 - ((F k ^^(k-1)) n / n) * (n / S n))%R).
 - intros n. rewrite Prop_6_3_b; try lia.
   replace (S (S n) -1) with (S n) by lia.
   rewrite minus_INR.
   + field. generalize (lt_0_INR (S n) lia).
     generalize (lt_0_INR (S (S n)) lia). lra.
   + generalize (Fkj_le_id k (k-1) (S n)). lia.
 - apply is_lim_seq_minus'; try apply is_lim_seq_const.
   apply is_lim_seq_mult'.
   + now apply Fkj_limit.
   + apply MoreLim.is_lim_seq_ndivSn.
Qed.


(** Section 7 *)

Lemma Prop_7_1_a k k' j j' n : 0<k -> 0<k' ->
 (L k ^^j) n <= (L k' ^^j') n <->
 let m := (L k ^^ j) n in (F k' ^^j') m <= (F k ^^j) m.
Proof.
 intros. rewrite !L_iter. rewrite WordGrowth.LL_fsfs_le_iff by lia.
 cbn. now rewrite !Fs_alt.
Qed.

Lemma Prop_7_1_b k k' j j' n : 0<k -> 0<k' ->
 (L k ^^j) n < (L k' ^^j') n <->
 let m := (L k' ^^ j') n in (F k' ^^j') m < (F k ^^j) m.
Proof.
 intros. rewrite !Nat.lt_nge. now rewrite Prop_7_1_a.
Qed.

Lemma Prop_7_1_c k k' j j' n : 0<k -> 0<k' ->
 let m := (F k ^^j) n in
 (L k ^^j) m <= (L k' ^^j') m ->
 (F k' ^^j') n <= (F k ^^j) n.
Proof.
 intros Hk Hk' m. unfold m; clear m.
 rewrite !L_iter, !Fs_alt. now apply WordGrowth.LL_fsfs_le_bis.
Qed.

Lemma Prop_7_1_d k k' j j' n : 0<k -> 0<k' ->
 (F k' ^^j') n < (F k ^^j) n ->
 let m := (F k' ^^j') n in
 (L k ^^j) m < (L k' ^^j') m.
Proof.
 intros Hk Hk'. rewrite !Nat.lt_nge. intros H. contradict H.
 apply Prop_7_1_c; auto.
Qed.

Lemma Prop_7_1 k k' j j' : 0<k -> 0<k' ->
 (forall n, (L k ^^j) n <= (L k' ^^j') n) <->
 (forall n, (F k' ^^j') n <= (F k ^^j) n).
Proof.
 split; intros. now apply Prop_7_1_c. now apply Prop_7_1_a.
Qed.

Lemma Eqn_7_1_add k n : 0<k ->
  (L (k+1) ^^(k+1)) n + (L k ^^(k-1)) n = (L (k+1) ^^k) n + (L k ^^k) n.
Proof.
 intros K.
 rewrite !L_iter. rewrite !Nat.add_1_r. apply WordGrowth.steiner_trick; lia.
Qed.

Lemma Eqn_7_1 k n : 0<k ->
  (L (k+1) ^^(k+1)) n - (L k ^^k) n = (L (k+1) ^^k) n - (L k ^^(k-1)) n.
Proof.
 intros K. generalize (Eqn_7_1_add k n K). lia.
Qed.

Theorem Thm_7_2_a k n : L (k+1) n <= L k n.
Proof.
 rewrite !L_alt. rewrite Nat.add_1_r. apply WordGrowth.Lk1_ge_LSk1.
Qed.

Theorem Thm_7_2_a' k n : 0<k -> C (k+1) (Nat.eqb (k+1)) n <= C k (Nat.eqb k) n.
Proof.
 intros. generalize (Thm_7_2_a k n). rewrite !Prop_4_2, !Prop_4_1_a; lia.
Qed.

Theorem Thm_7_2_b k n j : 0<k -> 0<n -> j<=k ->
  (L k^^j) n < (L (k+1) ^^(j+1)) n.
Proof.
 intros. rewrite !L_iter, !Nat.add_1_r. now apply WordGrowth.Lkj_lt_LSkSj.
Qed.

Theorem Cor_7_3 k j n : (L (k+1) ^^j) n <= (L k ^^j) n.
Proof.
 revert n. induction j; simpl; trivial.
 intros n. transitivity (L (k+1) ((L k ^^j) n)).
 - apply incr_mono; trivial. apply (L_incr (k+1) 1).
 - apply Thm_7_2_a.
Qed.

Theorem Thm_7_4 k j n : (F k ^^j) n <= (F (k+1) ^^j) n.
Proof.
 rewrite !Fs_alt, Nat.add_1_r. apply WordGrowth.fs_grows.
Qed.

Theorem Thm_7_4' k n : F k n <= F (k+1) n.
Proof.
 apply (Thm_7_4 k 1).
Qed.

Theorem Thm_7_5 k j n : j<=k -> (F (k+1) ^^(j+1)) n <= (F k ^^j) n.
Proof.
 rewrite !Fs_alt, !Nat.add_1_r. apply WordGrowth.fs_decreases.
Qed.

Definition N k := (k+1)*(k+6)/2.

Lemma N_alt k : N k = GenG.quad k.
Proof.
 symmetry. apply GenG.quad_other_eqn.
Qed.

Lemma N_succ k : N (S k) = N k + (k+4).
Proof.
 rewrite !N_alt. apply GenG.quad_S.
Qed.

Lemma LkSkSk k : 0<k -> (L k ^^(k+1)) (k+1) = S (N k).
Proof.
 intros Hk. rewrite L_iter, Nat.add_1_r.
 rewrite WordGrowth.L_k_Sk_Sk, N_alt by trivial.
 generalize (GenFib.triangle_aboveid (k+3)). unfold GenG.quad. lia.
Qed.

Lemma LkSkk k : 0<k -> (L k ^^(k+1)) k = S (N (k-1)).
Proof.
 intros Hk. rewrite L_iter, Nat.add_1_r.
 rewrite WordGrowth.L_k_Sk_k, N_alt by trivial.
 unfold GenG.quad. replace (k-1+3) with (k+2) by lia.
 generalize (GenFib.triangle_aboveid (k+2)). lia.
Qed.

Lemma Equality_LkSkSk_LSkSSkSk k : 0<k ->
 (L k ^^(k+1)) (k+1) = (L (k+1) ^^(k+2)) (k+1).
Proof.
 intros Hk. rewrite LkSkSk by lia.
 replace (k+2) with (k+1+1) by lia. rewrite LkSkk by lia.
 do 2 f_equal. lia.
Qed.

Lemma Lem_7_6_low k j :
  0<k -> j <= 2*k -> (L (k+1) ^^(j+1)) 1 = (L k ^^j) 1 + 1.
Proof.
 intros K J. rewrite !L_1_alt, !Nat.add_1_r. apply GenFib.A_diag_step; lia.
Qed.

Lemma Lem_7_6_eq k j :
  0<k -> j = 2*k+1 -> (L (k+1) ^^(j+1)) 1 = (L k ^^j) 1.
Proof.
 intros K J. rewrite !L_1_alt, !Nat.add_1_r. apply GenFib.A_diag_eq; lia.
Qed.

Lemma Lem_7_6_high k j :
  0<k -> 2*k+1 <= j <= 3*k ->
  (L k ^^j) 1 = (L (k+1) ^^(j+1)) 1 + ((j-2*k-1)*(j-2*k+2))/2.
Proof.
 intros K J. rewrite !L_1_alt. unfold A.
 rewrite GenFib.A_diag_decr_exact by lia. f_equal; f_equal; lia.
Qed.

Lemma Lem_7_6_lt k j :
  0<k -> 2*k+2 <= j -> (L (k+1) ^^(j+1)) 1 < (L k ^^j) 1.
Proof.
 intros K J. rewrite !L_1_alt, !Nat.add_1_r. apply GenFib.A_diag_decr; lia.
Qed.

Definition cex k j := S (2*k+2-j).

Lemma Lem_7_7 k j : 0<k -> k+2 <= j ->
  (L (S k) ^^(S j)) (cex k j) < (L k ^^j) (cex k j).
Proof.
 intros. rewrite !L_iter. apply WordGrowth.cex_spec; lia.
Qed.

Lemma Lem_7_7' k j :
  0<k -> k+2 <= j ->
  let m := (L k ^^j) (cex k j) in
  (F k ^^j) m < (F (S k) ^^(S j)) m.
Proof.
 intros. apply Prop_7_1_b; try lia. apply Lem_7_7; lia.
Qed.

Lemma F_last_equality k : 0<k -> F k (N k) = F (S k) (N k).
Proof.
 intros. rewrite !F_alt, N_alt. apply GenG.fk_fSk_last_equality; lia.
Qed.

Lemma L_last_equality k :
  1<k -> let n := N (k-1) in L k n = L (S k) n.
Proof.
 intros Hk n. unfold L; rewrite !Fast.Nat.rchild_alt.
 unfold n. clear n. rewrite N_alt.
 destruct k as [|k]; try easy. replace (S k-1) with k by lia.
 apply GenG.rchild_k_Sk_last_equality; lia.
Qed.

Lemma L_last_equality' k :
  0<k -> L (k+1) (N k) = L (k+2) (N k).
Proof.
 intros Hk. replace (k+2) with (S (k+1)) by lia.
 replace k with (k+1-1) at 2 4 by lia.
 apply L_last_equality; lia.
Qed.

Lemma conjecture_strength_1 k : 0<k ->
 (forall m, N k < m -> F k m < F (S k) m) ->
 (forall n, n<>1 -> F k n < F (S k) (S n)).
Proof.
 intros Hk H n Hn. rewrite !F_alt in *.
 apply GenG.fk_fSk_conjectures; try lia.
 intros m. rewrite <- !F_alt, <- N_alt. apply H.
Qed.

Lemma conjectures_strength_2 k : 0<k ->
 (forall m, N (S k) < m -> F (S k) m < F (S (S k)) m) ->
 (forall m, N k < m -> L (S (S k)) m < L (S k) m).
Proof.
 intros Hk H m Hm. rewrite !L_alt.
 apply WordGrowth.f_L_conjectures.
 - intros p. rewrite <- N_alt, <- !F_alt. apply H.
 - now rewrite <- N_alt.
Qed.


(** Section 8 *)

Lemma Prop_8_1 k n : C (S k) (Nat.eqb 1) n <= C k (Nat.eqb 1) n.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K]; try easy.
 destruct (Nat.eq_dec k 1) as [->|K'].
 - transitivity n. apply C_le. unfold C. rewrite filter_all.
   now rewrite take_length.
   intros x. rewrite in_take. intros (i & <- & Hi). rewrite Nat.eqb_eq.
   generalize (word_x_letters 1 i). lia.
 - generalize (Thm_7_4' k n). rewrite Nat.add_1_r.
   rewrite !Prop_4_3; try lia.
   generalize (C_le (S k) (Nat.eqb 1) n) (C_le k (Nat.eqb 1) n). lia.
Qed.

(** For letters [3<=i<k], [C k (=i)] and [C (k+1) (=i)] are uncomparable. *)

Lemma Prop_8_2_a k i :
 3 <= i < k ->
 let n := (L k ^^(2*k+2)) 1 + i in
 C k (Nat.eqb i) n < C (k+1) (Nat.eqb i) n.
Proof.
 intros Hi n. rewrite !Ceqb_count, Nat.add_1_r by lia.
 unfold n. rewrite L_iter in *.
 replace i with (S (i-1)) at 2 4 by lia.
 apply WordGrowth.C_diag_incr_example; lia.
Qed.

Lemma Prop_8_2_b k i :
 3 <= i < k ->
 let n := (L (S k)^^(k+i)) 1 + i in
 C (k+1) (Nat.eqb i) n < C k (Nat.eqb i) n.
Proof.
 intros Hi n. rewrite !Ceqb_count, Nat.add_1_r by lia.
 unfold n. rewrite L_iter in *.
 replace i with (S (i-1)) at 3 6 by lia.
 replace (k+i) with (1+k+(i-1)) by lia.
 apply WordGrowth.C_diag_decr_example; lia.
Qed.

(* Final examples *)

(*
Compute let k := 5 in let i := 4 in (L k ^^(2*k+2)) 1 + i. (* 49 *)
Compute C 5 (Nat.eqb 4) 49. (* 5 *)
Compute C 6 (Nat.eqb 4) 49. (* 6 *)
(* Actually here, counter-example as soon as n=48 (same F_k ?) *)
Compute C 5 (Nat.eqb 4) 48. (* 5 *)
Compute C 6 (Nat.eqb 4) 48. (* 6 *)

Compute let i := 4 in let k := 5 in (L (S k)^^(k+i)) 1 + i. (* 20 *)
Compute C 5 (Nat.eqb 4) 20. (* 2 *)
Compute C 6 (Nat.eqb 4) 20. (* 1 *)
*)
