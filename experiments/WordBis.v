Require Import MoreFun MoreList DeltaList GenFib GenG Words.
Import ListNotations.

(* UNUSED, NOT SO INTERESTING ? *)

(** Another possible susbstitution for Hofstadter functions,
    giving [min (rank n) (S k)] instead of [min (rank n) k].
    Hence it works on 0..(S k) instead of 0..k *)

Definition ksubstbis k n := if n <? k then [S n] else [S k; 0].

Definition kwordbis k n := napply (ksubstbis k) n [S k].

Definition kseqbis k := subst2seq (ksubstbis k) (S k).

Compute kprefix 2 20.

(* Compute take 20 (kseqbis 2). *)
(* [3; 0; 1; 2; 3; 0; 3; 0; 1; 3; 0; 1; 2; 3; 0; 1; 2; 3; 0; 3] *)

Lemma ksubstbis_noerase k : NoErase (ksubstbis k).
Proof.
 red. intros c. unfold ksubstbis. now case Nat.ltb_spec.
Qed.

Lemma ksubstbis_prolong k : Prolong (ksubstbis k) (S k).
Proof.
 red. exists [0]. split. easy.
 unfold ksubstbis. case Nat.ltb_spec; auto; lia.
Qed.

Lemma kseqbis_SubstSeq k : SubstSeq (ksubstbis k) (kseqbis k) (S k).
Proof.
 apply substseq_exists. apply ksubstbis_noerase. apply ksubstbis_prolong.
Qed.

(** Initial values *)

Lemma kwordbis_0 k : kwordbis k 0 = [S k].
Proof.
 reflexivity.
Qed.

Lemma kwordbis_1 k : kwordbis k 1 = [S k; 0].
Proof.
 cbn. unfold ksubstbis.
 case Nat.ltb_spec; auto. lia.
Qed.

Lemma ksubstbis_low0 k n : n <= k -> napply (ksubstbis k) n [0] = [n].
Proof.
 induction n. auto.
 intros LE.
 rewrite napply_alt. rewrite IHn; try lia. simpl.
 unfold ksubstbis. case Nat.ltb_spec; auto. lia.
Qed.

Lemma ksubstbis_low0' k : napply (ksubstbis k) (S k) [0] = [S k; 0].
Proof.
 change (S k) with (1+k) at 1. rewrite napply_add.
 rewrite ksubstbis_low0 by lia. simpl.
 unfold ksubstbis. case Nat.ltb_spec; auto. lia.
Qed.

Lemma kwordbis_low k n : n <= S k -> kwordbis k n = S k :: List.seq 0 n.
Proof.
 induction n.
 - now rewrite kwordbis_0.
 - intros LE.
   rewrite seq_S.
   cbn. unfold ksubstbis at 2. case Nat.ltb_spec; try lia. intros _.
   simpl. rewrite napply_cons.
   rewrite ksubstbis_low0; auto; try lia.
   change (kwordbis k n ++ [n] = S k :: List.seq 0 n ++ [n]).
   rewrite IHn; try lia. auto.
Qed.

(** Alt equation : *)

Lemma kwordbis_alt k n :
  k<n -> kwordbis k (S n) = kwordbis k n ++ kwordbis k (n-k).
Proof.
 induction n.
 - inversion 1.
 - rewrite Nat.lt_succ_r, Nat.lt_eq_cases.
   intros [LT| <-].
   + replace (S n -k) with (S (n-k)) by lia.
     remember (S n) as m eqn:E.
     cbn.
     rewrite app_nil_r.
     unfold ksubstbis at 2. case Nat.ltb_spec; try lia. intros _.
     rewrite napply_cons. f_equal.
     replace m with (m-k+k) by lia.
     rewrite napply_add. rewrite ksubstbis_low0 by lia.
     replace (m-k) with (S (n-k)) by lia.
     simpl. f_equal. unfold ksubstbis.
     do 2 (case Nat.ltb_spec; try lia). auto.
   + clear IHn.
     replace (S k-k) with 1 by lia. rewrite kwordbis_1.
     remember (S k) as m eqn:E.
     unfold kwordbis at 1. simpl. unfold ksubstbis at 2.
     case Nat.ltb_spec; try lia. intros _. simpl.
     rewrite napply_cons. f_equal. subst m. apply ksubstbis_low0'.
Qed.

Lemma kwordbis_len k n : length (kwordbis k n) = A k n.
Proof.
 induction n as [[|n] IH] using lt_wf_ind.
 - now rewrite kwordbis_0.
 - case (Nat.lt_ge_cases k n) as [LT|GE].
   + rewrite kwordbis_alt; auto. rewrite app_length, !IH; try lia.
     simpl; auto.
   + rewrite kwordbis_low by lia. simpl.
     rewrite seq_length. rewrite !A_base; lia.
Qed.

Lemma kseqbis_alt k n m a : n < A k m -> kseqbis k n = nth n (kwordbis k m) a.
Proof.
 intros LE.
 rewrite (kseqbis_SubstSeq k m).
 change (napply _ _ _) with (kwordbis k m).
 rewrite kwordbis_len, take_nth; auto.
Qed.

(** Link between [kseqbis] and Zeckendorf decomposition :
    0 iff rank 0,
    1 iff rank 1,
    ...
    (S k) iff rank > k (or no rank, ie n=0)

    Hence 0 in [kseqbis] whenever the [f k] function is flat.
*)

Definition bounded_rankbis k n := omin (rank k n) (S k).

Lemma kseqbis_bounded_rank k n : kseqbis k n = bounded_rankbis k n.
Proof.
 induction n as [n IH] using lt_wf_ind.
 assert (E := decomp_sum k n).
 assert (D := decomp_delta k n).
 set (l := decomp k n) in *.
 destruct (rev l) as [|a rl] eqn:E'; apply rev_switch in E'.
 - rewrite E' in *. simpl in E. rewrite <- E. easy.
 - assert (A k a <= n < A k (S a)).
   { rewrite <- E, E', sumA_rev.
     split.
     + simpl; lia.
     + apply decomp_max. apply Delta_rev. now rewrite <- E'. }
   rewrite (kseqbis_alt k n (S a) 0) by lia.
   destruct (Nat.le_gt_cases a k) as [LE|LT].
   + rewrite kwordbis_low by lia.
     destruct n as [|n]; try easy.
     change (nth _ _ _) with (nth n (List.seq 0 (S a)) 0).
     rewrite !A_base in H; try lia.
     replace n with a by lia.
     rewrite seq_nth by lia. simpl.
     unfold bounded_rankbis, rank. rewrite decomp_low; simpl; lia.
   + rewrite kwordbis_alt by auto.
     rewrite app_nth2; rewrite kwordbis_len; try lia.
     rewrite <- kseqbis_alt by (simpl in H; lia).
     rewrite IH by (generalize (@A_nz k a); lia).
     unfold bounded_rankbis, rank. fold l; rewrite E'; simpl rev.
     replace (decomp _ _) with (rev rl).
     2:{ symmetry; apply decomp_carac.
         - rewrite E' in D. simpl in D. now apply Delta_app_iff in D.
         - revert E. rewrite E'. simpl. rewrite sumA_app. simpl. lia. }
     destruct (rev rl); simpl; lia.
Qed.

(** From (kseqbis k) to (kseq k) : change all (S k) into k *)

Lemma kseqbis_kseq k n : kseq k n = Nat.min k (kseqbis k n).
Proof.
 rewrite kseq_bounded_rank, kseqbis_bounded_rank.
 unfold bounded_rank, bounded_rankbis.
 destruct rank; simpl; lia.
Qed.

(** From (kseq k) to (kseqbis k) : change all k that are followed by 0
    into (S k), and leave intact the k followed by k. *)

(** Other expressions:
    kseqbis k n - kseq k n = fs k (S k) (S n) - fs k (S k) n
                           = S (f k (n+1)) - f k (n+2)
*)
