From Coq Require Import List Arith Lia Reals Lra.
From Coq Require Epsilon.
From Hofstadter.HalfQuantum Require Import Complex.
Require Import DeltaList MoreTac MoreFun MoreList MoreReals MoreComplex.
Require Import MoreSum MoreLim.
Require GenFib GenG Words WordGrowth Mu Freq RootEquiv F3 F4 F5.
Require Import Article1.
Local Coercion INR : nat >-> R.
Local Coercion Rbar.Finite : R >-> Rbar.Rbar.

(** * Article2.v *)

(** This file is a wrapper around the rest of the current Coq development
    and can serve as an entry point when reading our second article:

      Generalized Hofstadter functions G, H and beyond : numeration systems
      and discrepancy

    We start here by loading definitions and results from Article1.v,
    the Coq artifact for the first article:

      Pointwise order of generalized Hofstadter functions G, H and beyond
*)


(** ** Section 1 : Introduction *)

(** Definition 1.1 : F already defined as [Article1.F] *)

(** Definition 1.2 : subst_τ and word_x and L already defined as
    [Article1.subst_τ] [Article1.word_x] [Article1.L] *)

(** ** Section 2 : Basic properties of F_k *)

(** Proposition 2.1 : Cf. Article1 *)

(** Proposition 2.2 : *)

Definition L_via_F : forall k n, L k n = n + (F k ^^ (k - 1)) n.
Proof.
exact Article1.Prop_4_2.
Qed.

(** Proposition 2.3 : Cf. [Article1.Fkj_Lkj] and [Article1.Lkj_Fkj]. *)

(** Corollary 2.4 : Cf. [Article1.Cor_3_2] *)


(** ** Section 3 : Related Fibonacci-like recurrence *)

(** Definition 3.1 : Sequences A are already defined as [Article1.A],
    with proofs :
     A_init: forall k p : nat, p <= k -> A k p = p + 1
     A_rec: forall k p : nat,
      0 < k -> k <= p -> A k p = A k (p - 1) + A k (p - k)
*)

Lemma A_pos k p : 0 < A k p.
Proof.
 apply GenFib.A_nz.
Qed.

Lemma A_lt k p p' : p < p' -> A k p < A k p'.
Proof.
 apply GenFib.A_lt.
Qed.

(** Proposition 3.2:
    As a combinatorial interpretation of [A k p], we consider
    all possible subsets of [0..p-1] with a distance of at least k
    between elements. This enumeration internally exploits the
    k-decompositions that will be presented below.
*)

Definition enum_sparse_subsets k p := GenFib.enum_sparse_subsets k p.

Lemma enum_sparse_subsets_ok k p : 0<k ->
  forall l, In l (enum_sparse_subsets k p) <-> Below l p /\ Delta k l.
Proof.
 intros Hk l. unfold enum_sparse_subsets.
 apply GenFib.enum_sparse_subsets_ok; lia.
Qed.

Lemma enum_sparse_subsets_nodup k p : NoDup (enum_sparse_subsets k p).
Proof.
 apply GenFib.enum_sparse_subsets_nodup.
Qed.

Lemma A_combi k p : length (enum_sparse_subsets k p) = A k p.
Proof.
 unfold enum_sparse_subsets, GenFib.enum_sparse_subsets.
 now rewrite map_length, seq_length.
Qed.

(** Proposition 3.3.
    Note that Coq subtraction on natural number is rounded: 0-1 = 0.
*)

Lemma F_A k j p : 0<k -> (F k ^^j) (A k p) = A k (p-j).
Proof.
 intros K. rewrite Fs_alt. unfold A.
 induction j; simpl; rewrite ?IHj, ?F_f, ?GenG.f_A; f_equal; lia.
Qed.

Lemma L_A k j p : 0<k -> (L k ^^j) (A k p) = A k (p+j).
Proof.
 intros K. rewrite <- !L_1_alt. rewrite <- iter_add. f_equal; lia.
Qed.

(** ** Section 4 : Fibonacci-like digital expansions *)

Definition decomp := GenFib.decomp.

Definition sum := GenFib.sumA.

(*
Compute decomp 2 17. (* [0;2;5] *)
Compute sum 2 [0;2;5]. (* 17 *)
Compute sum 2 [0;2;3;4]. (* 17 *)
Compute sum 2 [0;4;4]. (* 17 *)
Compute decomp 3 17. (* [3;6] *)
Compute sum 3 [3;6]. (* 17 *)
Compute decomp 1 17. (* [0;4] *)
*)

Lemma A_k_0 k : A k 0 = 1.
Proof.
 easy.
Qed.

Lemma A_k_1 k : A k 1 = 2.
Proof.
 easy.
Qed.

Lemma A_k_2 k : In (A k 2) [3;4].
Proof.
 unfold A. destruct k as [|[|k]]; simpl; lia.
Qed.

Lemma A_k_3 k : In (A k 3) [4;5;8].
Proof.
 unfold A. destruct k as [|[|[|k]]]; simpl; lia.
Qed.

(** The Delta predicate on lists states that two elements
    in the list are apart by at least a value p.
    Delta is defined inductively in DeltaList.v.
    It amounts to the two following properties : *)

Lemma Delta_nil p : Delta p [].
Proof.
 constructor.
Qed.

Lemma Delta_alt p x l :
  Delta p (x::l) <-> Delta p l /\ forall y, In y l -> x+p <= y.
Proof.
 apply DeltaList.Delta_alt.
Qed.

(** Theorem 4.2 (Zeckendorf decomposition).
    Properties of the decomposition: *)

Lemma decomp_canon k n : Delta k (decomp k n).
Proof.
 apply GenFib.decomp_delta.
Qed.

Lemma decomp_sum k n : sum k (decomp k n) = n.
Proof.
 apply GenFib.decomp_sum.
Qed.

Lemma decomp_unique k n l : 0<k -> Delta k l -> sum k l = n -> decomp k n = l.
Proof.
 intros K. apply GenFib.decomp_carac; lia.
Qed.

(** Renormalisation of lax decompositions *)

Definition norm k l := GenFib.renorm k l.

(* Compute norm 2 [0;2;3;4]. (* [0;2;5] *) *)

Lemma norm_canon k l : Delta (k-1) l -> Delta k (norm k l).
Proof.
 apply GenFib.renorm_delta.
Qed.

Lemma norm_sum k l : sum k (norm k l) = sum k l.
Proof.
 apply GenFib.renorm_sum.
Qed.

(** Definition 4.3 : Rank.
    Answers [Some r] for a finite rank (i.e. non-empty decomposition)
    and [None] otherwise (for n=0 and its empty decomposition) *)

Definition rank : nat -> nat -> option nat := GenFib.rank.

Lemma rank_None k n : rank k n = None <-> n = 0.
Proof.
 unfold rank. apply GenFib.rank_none.
Qed.

Lemma rank_Some k n r :
  rank k n = Some r <-> exists l, decomp k n = r::l.
Proof.
 unfold rank, GenFib.rank, decomp.
 destruct (GenFib.decomp k n) as [|r' l]; split.
 - easy.
 - intros (l,[=]).
 - intros [= ->]. now exists l.
 - now intros (l',[= -> ->]).
Qed.

(** Proposition 4.4 *)

Definition next_decomp := GenFib.next_decomp.

Lemma next_decomp_delta k l : Delta k l -> Delta k (next_decomp k l).
Proof.
 apply GenFib.next_decomp_delta.
Qed.

Lemma next_decomp_sum k l : sum k (next_decomp k l) = 1 + sum k l.
Proof.
 apply GenFib.next_decomp_sum.
Qed.

Lemma next_decomp_highrank k r l :
  0<k -> k <= r -> next_decomp k (r::l) = 0::r::l.
Proof.
 unfold next_decomp. simpl. case Nat.ltb_spec; trivial; lia.
Qed.

Lemma next_decomp_lowrank k r l :
  r < k -> Delta k (r::l) -> next_decomp k (r::l) = norm k (r+1 :: l).
Proof.
 unfold next_decomp. simpl. case Nat.ltb_spec; try lia.
 intros _ R D. rewrite GenFib.renormS_alt, Nat.add_1_r; trivial; lia.
Qed.

(** Definition 4.5 : shifts *)

Definition lshift l q := map (Nat.add q) l.
Definition rshiftup l q := map (decr q) l.
Definition rshift l q := map (decr q) (filter (Nat.leb q) l).

Local Infix "<<" := lshift (at level 30).
Local Infix ">>+" := rshiftup (at level 30).
Local Infix ">>" := rshift (at level 30).

Lemma lshift_0 l : l << 0 = l.
Proof.
 unfold lshift. rewrite <- (map_id l) at 2. now apply map_ext.
Qed.

Lemma rshiftup_0 l : l >>+ 0 = l.
Proof.
 unfold rshiftup. rewrite <- (map_id l) at 2. apply map_ext.
 unfold decr. lia.
Qed.

Lemma rshift_0 l : l >> 0 = l.
Proof.
 unfold rshift. rewrite filter_all.
 2:{ intros. apply Nat.leb_le. lia. }
 rewrite <- (map_id l) at 2. apply map_ext. unfold decr. lia.
Qed.

Lemma lshift_add p q l : l << (p+q) = l << p << q.
Proof.
 unfold lshift. rewrite map_map. apply map_ext. lia.
Qed.

Lemma rshiftup_add p q l : l >>+ (p+q) = l >>+ p >>+ q.
Proof.
 unfold rshiftup. rewrite map_map. apply map_ext. unfold decr. lia.
Qed.

Lemma rshift_add p q l : l >> (p+q) = l >> p >> q.
Proof.
 unfold rshift. rewrite map_filter, map_map, filter_filter.
 unfold Basics.compose. set (h := fun a => _ && _).
 rewrite (filter_ext (Nat.leb (p+q)) h).
 2:{ intros a. unfold h, decr. do 3 case Nat.leb_spec; lia. }
 apply map_ext. intros a. unfold decr. lia.
Qed.

Lemma lshift_delta k l q : Delta k l -> Delta k (l << q).
Proof.
 apply Delta_map. lia.
Qed.

Lemma rshift_delta k l q : Delta k l -> Delta k (l >> q).
Proof.
 intros D. apply Delta_map_decr.
 - intro x. now rewrite filter_In, Nat.leb_le.
 - now apply Delta_filter.
Qed.

Lemma rshiftup_delta k l q : Delta k l -> Delta (k-q) (l >>+ q).
Proof.
 intros D. eapply Delta_map; eauto. unfold decr. lia.
Qed.

(** Digression: study of the 1-decomposition and its shifts *)

Lemma rshiftup_rshift_diff x l :
  Delta 1 (x::l) ->
  (x::l) >>+ 1 =
  match x with
  | 0 => 0 :: (x::l) >> 1
  | _ => (x::l) >> 1
  end.
Proof.
 intros D.
 unfold rshift, rshiftup.
 destruct x; cbn -[Nat.leb].
 - f_equal. rewrite filter_all; trivial.
   intros y Y. rewrite Nat.leb_le. eapply Delta_le in D; eauto.
 - rewrite filter_all; trivial.
   intros y Y. rewrite Nat.leb_le. eapply Delta_le in D; eauto. lia.
Qed.

Lemma lshift_decomp_k1 n q : decomp 1 n << q = decomp 1 (n*2^q).
Proof.
 symmetry. apply decomp_unique; try constructor.
 - apply lshift_delta, decomp_canon.
 - rewrite <- (decomp_sum 1 n) at 2.
   induction (decomp 1 n); simpl; trivial; rewrite ?IHl.
   rewrite !GenFib.A_1_pow2. rewrite Nat.pow_add_r. ring.
Qed.

(** NB: for [nat] datatype, [n/2] is a floor approximation *)

Lemma rshift_decomp_k1 n q : decomp 1 n >> q = decomp 1 (n/2^q).
Proof.
 symmetry. apply decomp_unique; try constructor.
 - apply rshift_delta, decomp_canon.
 - rewrite <- (decomp_sum 1 n) at 2.
   generalize (decomp_canon 1 n).
   induction (decomp 1 n); simpl; intros D; rewrite ?IHl.
   + rewrite Nat.div_0_l; trivial. now apply Nat.pow_nonzero.
   + apply Delta_alt in D. destruct D as (D,H).
     unfold rshift in *. simpl.
     case Nat.leb_spec; simpl; intros; rewrite IHl, !GenFib.A_1_pow2; trivial.
     * unfold decr.
       replace a with ((a-q)+q) at 2 by lia.
       rewrite Nat.pow_add_r, Nat.div_add_l. lia.
       now apply Nat.pow_nonzero.
     * replace q with (S a+(q-S a)) by lia.
       rewrite Nat.pow_add_r, <-!Nat.div_div by now apply Nat.pow_nonzero.
       f_equal.
       rewrite <- (Nat.add_1_r a), Nat.pow_add_r.
       rewrite <-!Nat.div_div by now apply Nat.pow_nonzero.
       replace (2^a) with (1*2^a) at 2 by lia.
       rewrite Nat.div_add_l by now apply Nat.pow_nonzero.
       change (2^1) with 2.
       assert (H1 : exists x, sum 1 l / 2^a = 2*x).
       { clear - H. induction l as [|y l IH].
         - exists 0; rewrite Nat.div_0_l. easy. now apply Nat.pow_nonzero.
         - destruct IH as (x,E). simpl in H; intuition.
           simpl sum. rewrite GenFib.A_1_pow2. exists (x+2^(y-S a)).
           assert (S a <= y).
           { rewrite <- Nat.add_1_r. apply H. now left. }
           replace y with (S (y - S a) + a) at 1 by lia.
           rewrite Nat.pow_add_r, Nat.div_add_l by now apply Nat.pow_nonzero.
           rewrite E. simpl. lia. }
       destruct H1 as (x & ->).
       now rewrite Nat.mul_comm, Nat.div_mul, Nat.div_add.
Qed.

Definition div_up a b := a/b + Nat.min (a mod b) 1.

Lemma div_up_unique a b q r : r < b -> a + r = b * q -> q = div_up a b.
Proof.
 intros R E. unfold div_up.
 destruct (Nat.eq_dec r 0) as [->|R'].
 - rewrite Nat.add_0_r in *. rewrite <- (Nat.div_unique_exact a b q) by lia.
   subst a. rewrite Nat.mul_comm, Nat.mod_mul; simpl; lia.
 - assert (q<>0) by lia.
   assert (E' : a = b * (q-1) + (b-r)).
   { replace q with (S (q-1)) in E; lia. }
   replace (a mod b) with (b-r).
   2:{ eapply Nat.mod_unique with (q-1); eauto. lia. }
   replace (a/b) with (q-1).
   2:{ eapply Nat.div_unique with (b-r); eauto. lia. }
   lia.
Qed.

Lemma div_up_unique_exact a b q : b<>0 -> a = b*q -> q = div_up a b.
Proof.
 intros B E. apply div_up_unique with 0; lia.
Qed.

Lemma div_up_alt a b : b<>0 -> div_up a b = (a+b-1)/b.
Proof.
 intros B. symmetry.
 assert ((a + b - 1) mod b < b) by now apply Nat.mod_upper_bound.
 apply div_up_unique with (b-1 - (a+b-1) mod b); try lia.
 generalize (Nat.div_mod_eq (a+b-1) b). lia.
Qed.

Lemma rshiftup_decomp_k1_q1 n :
  sum 1 (decomp 1 n >>+ 1) = div_up n 2.
Proof.
 remember (decomp 1 n) as l eqn:E.
 destruct l as [|r l].
 - simpl. now rewrite <- (decomp_sum 1 n), <- E.
 - rewrite rshiftup_rshift_diff.
   2:{ rewrite E. apply decomp_canon. }
   assert (D := decomp_canon 1 n). rewrite <- E in D.
   apply Delta_alt in D.
   assert (sum 1 l = 2 * sum 1 (map pred l)).
   { replace l with (map S (map pred l)) at 1.
     - clear. set (l' := map pred l). clearbody l'.
       induction l'; simpl; trivial; rewrite ?IHl'. rewrite Nat.sub_0_r. lia.
     - rewrite map_map. rewrite <- (map_id l) at 2.
       apply map_ext_in. intros a A. destruct D as (_,D).
       specialize (D a A). lia. }
   destruct r as [|r].
   + rewrite E, rshift_decomp_k1. simpl "^".
     change (S (sum 1 (decomp 1 (n/2))) = div_up n 2).
     rewrite decomp_sum. unfold div_up.
     replace (n mod 2) with 1; [simpl; lia|].
     rewrite <- (decomp_sum 1 n), <- E.
     change (sum _ _) with (1 + sum 1 l).
     now rewrite H, Nat.mul_comm, Nat.mod_add.
   + rewrite E, rshift_decomp_k1. simpl "^".
     rewrite decomp_sum. unfold div_up.
     replace (n mod 2) with 0; [simpl; lia|].
     rewrite <- (decomp_sum 1 n), <- E.
     change (sum _ _) with (GenFib.A 1 (S r) + sum 1 l).
     rewrite H, Nat.mul_comm, Nat.mod_add; try easy.
     now rewrite GenFib.A_1_pow2, Nat.pow_succ_r', Nat.mul_comm, Nat.mod_mul.
Qed.

Lemma rshiftup_decomp_k1_q1_alt n :
  norm 1 (decomp 1 n >>+ 1) = decomp 1 (div_up n 2).
Proof.
 symmetry. apply decomp_unique; try constructor.
 - apply norm_canon, rshiftup_delta, decomp_canon.
 - rewrite norm_sum. apply rshiftup_decomp_k1_q1.
Qed.

(** Beware : for arbitrary q,
    [sum 1 (rshiftup (decomp 1 n) q)] might differ from [div_up n (2^q)].
    P.ex. q=3 n=19. *)

(** Proposition 4.9 *)

Lemma sum_rshiftup_norm k l q : q<k ->
 sum k (norm k l >>+ q) = sum k (l >>+ q).
Proof.
 intros. apply GenFib.renorm_mapdecr. lia.
Qed.

(** Theorem 4.10 *)

Lemma Fs_decomp k q n :
  0<k -> q<=k -> (F k ^^q) n = sum k (decomp k n >>+ q).
Proof.
 intros K Q. rewrite Fs_alt. apply GenG.fs_decomp; lia.
Qed.

(** Beware, no generalization of [Fkj_alt] to [q>k].
    Consider for instance k=2 q=3 n=4. *)

Lemma F_decomp k n : 0<k -> F k n = sum k (decomp k n >>+ 1).
Proof.
 intros. apply (Fs_decomp k 1); lia.
Qed.

(** Definition 4.6, reversed, we start from the Proposition 4.7 : *)

Definition Ftilde k n := F k (n+1) - 1.

Definition Ftilde_iter k q n : (Ftilde k ^^q) n = (F k ^^q) (n+1) - 1.
Proof.
 revert n.
 induction q; intros; simpl; try lia.
 rewrite IHq. unfold Ftilde. f_equal. f_equal.
 assert (1 <= (F k ^^q) (n+1)). { rewrite <- Fkj_nonzero. lia. }
 lia.
Qed.

(** And we show now that the recurrence of Definition 4.6 holds : *)

Definition Ftilde_0 k : Ftilde k 0 = 0.
Proof.
 unfold Ftilde. generalize (Fkj_1 k 1). simpl. lia.
Qed.

Definition Ftilde_rec k n : Ftilde k (S n) = n - (Ftilde k ^^k) n.
Proof.
 rewrite Ftilde_iter. unfold Ftilde.
 rewrite F_rec. replace (S n +1-1) with (n+1) by lia.
 assert (1 <= (F k ^^k) (n+1)). { rewrite <- Fkj_nonzero. lia. }
 lia.
Qed.

(** Theorem 4.8, direct proof following Meek and Van Rees *)

Lemma Ftilde_alt k n :
  0<k -> Ftilde k n = sum k (decomp k n >> 1).
Proof.
 intros K.
 induction n as [[|n] IH] using lt_wf_ind.
 - simpl. apply Ftilde_0.
 - rewrite Ftilde_rec.
   assert (forall j m, m <= n -> (Ftilde k ^^ j) m = sum k (decomp k m >> j)).
   { induction j; intros m M.
     - simpl. now rewrite rshift_0, decomp_sum.
     - rewrite iter_S. rewrite IHj, IH; try lia.
       2:{ destruct m. now rewrite Ftilde_0. rewrite Ftilde_rec. lia. }
       f_equal.
       set (l := decomp k m >> 1).
       replace (decomp k (sum k l)) with l.
       2:{ symmetry. apply decomp_unique; trivial.
           unfold l. apply rshift_delta, decomp_canon. }
       unfold l; clear l. now rewrite <- rshift_add. }
   rewrite H by trivial. clear IH H.
   rewrite <- (decomp_sum k n) at 1.
   replace (decomp k (S n)) with (next_decomp k (decomp k n)).
   2:{ symmetry. apply decomp_unique; trivial.
       - apply next_decomp_delta, decomp_canon; trivial.
       - now rewrite next_decomp_sum, decomp_sum. }
   assert (D := decomp_canon k n).
   destruct (decomp k n) as [|r l]; trivial.
   destruct (Nat.le_gt_cases k r) as [R|R].
   + rewrite next_decomp_highrank by trivial.
     unfold rshift. rewrite filter_all.
     2:{ intros x. rewrite Nat.leb_le. intros [<-|IN]; trivial.
         eapply Delta_le in D; eauto; lia. }
     replace (filter _ _) with (r :: l).
     2:{ rewrite <- (@filter_all _ (Nat.leb 1) (r::l)) at 1. easy.
         intros x. rewrite Nat.leb_le. intros [<-|IN]; try lia.
         eapply Delta_le in D; eauto; lia. }
     unfold sum. rewrite GenFib.sumA_eqn_pred; try lia.
     eapply Delta_nz; eauto; lia.
   + rewrite next_decomp_lowrank by trivial.
     unfold rshift.
     replace (filter _ (r::l)) with l.
     2:{ rewrite <- (@filter_all _ (Nat.leb k) l) at 1.
         simpl. case Nat.leb_spec; trivial; lia.
         intros x X. rewrite Nat.leb_le.
         eapply Delta_le in D; eauto; lia. }
     rewrite filter_all.
     2:{ intros x X. rewrite Nat.leb_le.
         apply GenFib.renorm_le in X; try lia.
         rewrite Nat.add_1_r. apply Delta_S_cons.
         now replace (S (k-1)) with k by lia. }
     unfold norm, sum. rewrite GenFib.renorm_mapdecr'; try lia.
     2:{ rewrite Nat.add_1_r. apply Delta_S_cons.
         now replace (S (k-1)) with k by lia. }
     2:{ red. lia. }
     simpl. rewrite GenFib.sumA_eqn_pred; try lia.
     2:{ eapply Delta_nz'; eauto; lia. }
     replace (S (k-1)) with k by lia.
     replace (decr 1 (r+1)) with r by (unfold decr; lia). lia.
Qed.

(** Theorem 4.8 : indirect proof via F_alt *)

Lemma Ftilde_alt' k n :
  0<k -> Ftilde k n = sum k (decomp k n >> 1).
Proof.
 intros K. unfold Ftilde.
 destruct (Nat.eq_dec k 1) as [->|K'].
 { rewrite F_alt, GenG.f_1_div2 by lia.
   replace (S (n+1)) with (n+1*2) by lia. rewrite Nat.div_add by easy.
   rewrite rshift_decomp_k1, decomp_sum. simpl Nat.pow. lia. }
 rewrite F_decomp by lia.
 replace (decomp k (n+1)) with (next_decomp k (decomp k n)).
 2:{ symmetry. apply decomp_unique; trivial.
     - apply next_decomp_delta, decomp_canon.
     - rewrite next_decomp_sum, decomp_sum; lia. }
 remember (decomp k n) as l eqn:E.
 assert (D : Delta k l). { subst l; apply decomp_canon. }
 destruct l as [|r l]; trivial.
 destruct (Nat.lt_ge_cases r k) as [R|R].
 - rewrite next_decomp_lowrank; trivial.
   rewrite sum_rshiftup_norm by lia. rewrite rshiftup_rshift_diff.
   2:{ rewrite Nat.add_1_r.
       eapply Delta_S_cons; eauto. eapply Delta_more with k; eauto. lia. }
   rewrite Nat.add_1_r.
   destruct r as [|r].
   + unfold rshift. simpl. now rewrite Nat.sub_0_r.
   + unfold rshift. simpl. unfold decr. rewrite Nat.sub_0_r.
     replace (r-(k-1)) with 0 by lia. simpl. lia.
 - rewrite next_decomp_highrank; try lia.
   rewrite rshiftup_rshift_diff.
   + simpl. now rewrite Nat.sub_0_r.
   + constructor. lia. apply Delta_more with k; trivial.
Qed.

Lemma Ftilde_iter_alt k q n :
  0<k -> (Ftilde k ^^q) n = sum k (decomp k n >> q).
Proof.
 intros K. induction q.
 - simpl. now rewrite rshift_0, decomp_sum.
 - simpl. rewrite IHq, Ftilde_alt by trivial.
   f_equal.
   set (l := rshift (decomp k n) q).
   replace (decomp k (sum k l)) with l.
   2:{ symmetry. apply decomp_unique; trivial.
       unfold l. apply rshift_delta, decomp_canon. }
   unfold l; clear l. now rewrite <- rshift_add, Nat.add_1_r.
Qed.

(** Theorem 4.11 *)

Lemma dFkj_rank k q n : 0<k -> q<=k ->
  dF k q n = 0 <->
  match rank k n with Some r => r < q | None => False end.
Proof.
 intros K Q.
 generalize (Fkj_mono k q n (S n) lia).
 unfold dF, rank. rewrite !Fs_alt, !Nat.add_1_r.
 rewrite <- GenG.fs_flat_iff'; lia.
Qed.

Lemma dF_rank k n : 0<k -> dF k 1 n = 0 <-> rank k n = Some 0.
Proof.
 intros K. rewrite dFkj_rank by lia.
 destruct (rank k n) as [[|r]|]; try easy; split; easy || lia.
Qed.

(** Proposition 4.12 *)

Lemma L_decomp k n : 0<k -> L k n = sum k (decomp k n << 1).
Proof.
 intros K. rewrite L_via_F. rewrite Fs_alt. apply GenG.rchild_decomp; lia.
Qed.

Lemma Lkj_decomp k q n : 0<k -> (L k ^^q) n = sum k (decomp k n << q).
Proof.
 intros K. induction q; simpl.
 - now rewrite lshift_0, decomp_sum.
 - rewrite IHq, L_decomp by trivial.
   set (l := lshift (decomp k n) q).
   replace (decomp k (sum k l)) with l.
   2:{ symmetry. apply decomp_unique; trivial.
       unfold l. apply lshift_delta, decomp_canon. }
   unfold l. now rewrite <- lshift_add, Nat.add_1_r.
Qed.

Lemma decomp_Lkj k q n :
  0<k -> decomp k ((L k^^q) n) = decomp k n << q.
Proof.
 intros K. apply decomp_unique; trivial.
 - apply lshift_delta, decomp_canon.
 - symmetry. now apply Lkj_decomp.
Qed.


(** ** Section 5 : Decompositions and morphic words *)

(** Proposition 5.1 : Cf. Article1.Prop_4_4 *)

(** Theorem 5.2 *)

Definition bounded_succ_rank k n :=
 match rank k n with
 | Some r => min (r+1) k
 | None => k
 end.

Lemma xk_rank k n : 0<k -> word_x k n = bounded_succ_rank k n.
Proof.
 intros K. unfold bounded_succ_rank.
 destruct (rank k n) as [r|] eqn:E.
 - destruct (Nat.lt_ge_cases (r+1) k).
   + replace (min _ _) with (r+1) by lia.
     rewrite Prop_4_4 by lia.
     replace (r+1-1) with r by lia.
     split.
     * assert (~(dF k r n = 0)) by (rewrite dFkj_rank, E; lia).
       generalize (dF_step k r n). lia.
     * rewrite dFkj_rank, E; lia.
   + replace (min _ _) with k by lia.
     rewrite Prop_4_4_k by lia.
     assert (~(dF k (k-1) n = 0)).
     { rewrite dFkj_rank, E by lia. lia. }
     generalize (dF_step k (k-1) n). lia.
 - rewrite rank_None in E. subst. now apply word_x_0.
Qed.

(** Proposition 5.3. Some parts are already in Article1:

    Lemma L_1_alt k j : (L k ^^j) 1 = A k j.

    Lemma subst_τ_low : forall k j : nat,
    1 <= k -> j <= k -> (subst_τ k ^^ j) [k] = k :: seq 1 j

    Lemma subst_τ_rec: forall k j : nat,
    1 <= k <= j ->
    (subst_τ k ^^ j) [k] =
    (subst_τ k ^^ (j - 1)) [k] ++ (subst_τ k ^^ (j - k)) [k]
*)

Lemma word_x_prefix_A k j : 0<k ->
  take (A k j) (word_x k) = (subst_τ k ^^j) [k].
Proof.
 intros K.
 rewrite <- L_1_alt, <- word_x_subst. f_equal. unfold take. simpl.
 now rewrite word_x_0.
Qed.

Lemma length_subst_τ_k k j : 0<k ->
  length ((subst_τ k ^^j) [k]) = A k j.
Proof.
 intros K. rewrite <- word_x_prefix_A by trivial. apply take_length.
Qed.

(** Definition 5.4 *)

Definition W k l := flat_map (fun j => (subst_τ k ^^j) [k]) (List.rev l).

Lemma W_nil k : W k [] = [].
Proof.
 reflexivity.
Qed.

Lemma W_cons k n l : W k (n::l) = W k l ++ (subst_τ k ^^n) [k].
Proof.
 unfold W. simpl. rewrite flat_map_app. simpl. now rewrite app_nil_r.
Qed.

Lemma W_alt k l : 0<k -> W k l = map S (Words.kwords k (List.rev l)).
Proof.
 intros K. induction l; simpl; trivial. rewrite W_cons, IHl.
 rewrite Words.kwords_app, map_app. f_equal. simpl. rewrite app_nil_r.
 now apply subst_τ_j_k_alt.
Qed.

(** Theorem 5.5 *)

Lemma word_x_W k n : 0<k -> take n (word_x k) = W k (decomp k n).
Proof.
 intros K.
 rewrite W_alt by trivial.
 unfold decomp, word_x. rewrite <- Words.decomp_prefix_kseq by lia.
 unfold take. now rewrite map_map.
Qed.

Lemma subst_τ_app k j l l' :
 (subst_τ k ^^j) (l++l') = (subst_τ k ^^j) l ++ (subst_τ k ^^j) l'.
Proof.
 revert l l'. induction j; simpl; intros; trivial.
 rewrite IHj. set (u := _ l). set (u' := _ l'). clear. clearbody u u'.
 unfold subst_τ. now rewrite map_app, Words.ksubstw_app, map_app.
Qed.

Lemma subst_τ_W k j l : (subst_τ k ^^j) (W k l) = W k (l << j).
Proof.
 induction l; simpl.
 - rewrite W_nil. rewrite <- length_zero_iff_nil.
   change [] with (take 0 (word_x k)). now rewrite <- L_eqn_gen, L_0.
 - rewrite !W_cons, subst_τ_app. rewrite <- iter_add. now f_equal.
Qed.

Lemma subst_τ_prefix_x k j n :
  0<k -> (subst_τ k ^^j) (take n (word_x k)) = W k (decomp k n << j).
Proof.
 intros. now rewrite word_x_W, subst_τ_W.
Qed.


(** ** Section 6 : Related polynomials and algebraic integers *)

(** Definition 6.1 : Cf. [Article1.P] and [Article1.Q] and
    [Article1.α] and [Article2.β]. *)

(** Proposition 6.2 : Cf. [Article1.α_incr] and [Article1.α_itvl]
    and [Article1.β_decr] and [Article1.β_itvl] and [Article1.β_bound]. *)

(** Proposition 6.3 : Cf. [Article1.Fkj_limit] and [Article1.Lkj_limit]. *)

(** Proposition 6.4 *)

Local Open Scope R_scope.

Lemma α_equiv :
 exists ϵ : nat -> R,
   is_lim_seq ϵ 0 /\
   forall k, (1 < k)%nat -> α k = 1 - ln k / k * (1 - ϵ k).
Proof.
 apply RootEquiv.root_tau_equiv.
Qed.

Lemma β_equiv :
 exists ϵ : nat -> R,
   is_lim_seq ϵ 0 /\
   Hierarchy.eventually (fun k => β k = 1 + ln k / k * (1 + ϵ k)).
Proof.
 apply RootEquiv.root_mu_equiv.
Qed.

(** We now need the polynomial Q_k(X) = x^k-x^(k-1)-1 defined this time
    on complex numbers *)

Local Open Scope C_scope.

Definition Q (k:nat) (x:C) : C := x^k-x^(k-1)-1.

Definition IsRoot k r := (Q k r = 0).

Lemma IsRoot_alt k r : k<>O ->
  IsRoot k r <-> MorePoly.Root r (ThePoly.ThePoly k).
Proof.
 intros K. unfold IsRoot, Q. rewrite ThePoly.ThePoly_root_carac.
 replace (S (k-1)) with k by lia.
 split.
 - intro E. apply Cminus_eq_0 in E. rewrite <- E. ring.
 - intros ->. ring.
Qed.

Lemma k0_no_root r : ~IsRoot 0 r.
Proof.
 unfold IsRoot, Q. simpl. injection 1. lra.
Qed.

(** The positive root β_k of Q was already defined in Article1,
    of course it can also be seen as a complex root.
    NB: reals numbers are silently injected into complex numbers
    (the function RtoC is a coercion). *)

Lemma β_root k : k<>O -> IsRoot k (β k).
Proof.
 intros K. unfold β. rewrite IsRoot_alt by trivial.
 now apply ThePoly.mu_is_root.
Qed.

(** Enumeration of complex roots:
    For a change, we use the epsilon logical axiom, here to exhibit and
    name the list of roots of Q_k. This could be avoided by placing
    the rest of this file in a Coq section or module depending on the
    existence of these roots, and then instantiate this section/module
    thanks to SortedRoots_exists.

    Predicate [Csorted] means that this list of roots is
    strictly decreasing by lexicographic order (Real part
    then Imaginary part). In particular a Csorted list is
    without duplicates. *)

Definition AllRoots k l := forall r, In r l <-> IsRoot k r.
Definition SortedRoots k l := AllRoots k l /\ Csorted l.

Lemma SortedRoots_unique k l l' :
  SortedRoots k l -> SortedRoots k l' -> l=l'.
Proof.
 intros (U,V) (U',V').
 apply Csorted_unique, NoDup_Permutation;
  try apply Csorted_nodup; trivial.
 intros x. now rewrite (U x), (U' x).
Qed.

Lemma SortedRoots_0 l : SortedRoots 0 l <-> l=[].
Proof.
 split.
 - intros (U,V). destruct l as [|r l]; easy||exfalso.
   apply (k0_no_root r). rewrite <- (U r). now left.
 - intros ->. split. 2:constructor. intros r.
   now generalize (k0_no_root r).
Qed.

(** Link with an internal version *)
Lemma SortedRoots_alt k l :
  k<>O -> SortedRoots k l <-> ThePoly.SortedRoots k l.
Proof.
 intros K. revert l.
 assert (H : forall l, ThePoly.SortedRoots k l -> SortedRoots k l).
 { intros l Hl. split; try apply Hl.
   red. setoid_rewrite IsRoot_alt; trivial.
   now apply ThePoly.SortedRoots_roots. }
 split; try apply H.
 intros Hl.
 destruct (ThePoly.SortedRoots_exists k lia) as (l', Hl').
 replace l' with l in *; trivial.
 apply (SortedRoots_unique k); trivial. now apply H.
Qed.

Lemma SortedRoots_exists k : exists! roots, SortedRoots k roots.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - exists []. split. now rewrite SortedRoots_0.
   intros l. now rewrite SortedRoots_0.
 - destruct (ThePoly.SortedRoots_exists k lia) as (l, Hl).
   exists l. split. now apply SortedRoots_alt.
   intros l'. now apply SortedRoots_unique, SortedRoots_alt.
Qed.

(** The announced use of the epsilon axiom *)

Definition TheRoots k : list C :=
 Epsilon.iota (inhabits []) (SortedRoots k).

Lemma TheRoots_ok k : SortedRoots k (TheRoots k).
Proof.
 unfold TheRoots. apply Epsilon.iota_spec, SortedRoots_exists.
Qed.

Lemma TheRoots_0 : TheRoots 0 = [].
Proof.
 apply (SortedRoots_unique 0).
 apply TheRoots_ok.
 now rewrite SortedRoots_0.
Qed.

Lemma TheRoots_roots k r : In r (TheRoots k) <-> IsRoot k r.
Proof.
 apply TheRoots_ok.
Qed.

Lemma TheRoots_sorted k : Csorted (TheRoots k).
Proof.
 apply TheRoots_ok.
Qed.

Lemma TheRoots_nodup k : NoDup (TheRoots k).
Proof.
 apply Csorted_nodup, TheRoots_sorted.
Qed.

Lemma TheRoots_length k : length (TheRoots k) = k.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - now rewrite TheRoots_0.
 - now apply ThePoly.SortedRoots_length, SortedRoots_alt, TheRoots_ok.
Qed.

(** Note : l@i denotes here the i-th element of a complex list l
    (or 0 if the list is not long enough).
    The index i ranges from 0 to [length l - 1].
    Hence the article notation $r_{k,i}$ is here [TheRoots k @ i]. *)

Definition root_r k i := TheRoots k @ i.

Lemma TheRoots_first k : k<>O -> root_r k 0 = β k.
Proof.
 intros. now apply ThePoly.SortedRoots_mu, SortedRoots_alt, TheRoots_ok.
Qed.

Lemma TheRoots_last k :
 k<>O -> Nat.Even k -> root_r k (k-1) = Mu.nu k.
Proof.
 intros K K'. apply ThePoly.SortedRoots_nu; trivial.
 apply SortedRoots_alt, TheRoots_ok; trivial.
Qed.

Lemma TheRoots_last_carac k : k<>O -> Nat.Even k ->
  let r := root_r k (k-1) in (Im r = 0 /\ Re r < 0)%R.
Proof.
 intros K K'. rewrite (TheRoots_last k K K'). split; trivial.
 simpl. generalize (Mu.nu_itvl k K K'). lra.
Qed.

(** Proposition 6.5 *)

Lemma TheRoots_dominated_by_beta k r :
  In r (TheRoots k) -> r <> β k -> Cmod r < β k.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - now rewrite TheRoots_0.
 - intros IN.
   apply ThePoly.other_roots_lt_mu.
   now rewrite <- IsRoot_alt, <- TheRoots_roots.
Qed.

(** Proposition 6.6 *)

Lemma TheRoots_same_mod_re k r r' :
 In r (TheRoots k) -> In r' (TheRoots k) -> Cmod r = Cmod r' <-> Re r = Re r'.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - now rewrite TheRoots_0.
 - intros IN IN'.
   rewrite TheRoots_roots, IsRoot_alt in IN, IN' by trivial.
   apply (ThePoly.root_equal_Cmod_Re_iff _ _ _ IN IN').
Qed.

Lemma TheRoots_lt_mod_re k r r' :
 In r (TheRoots k) -> In r' (TheRoots k) -> Cmod r < Cmod r' <-> Re r < Re r'.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - now rewrite TheRoots_0.
 - intros IN IN'.
   rewrite TheRoots_roots, IsRoot_alt in IN, IN' by trivial.
   apply (ThePoly.root_order_Cmod_Re_iff _ _ _ IN IN').
Qed.

Lemma TheRoots_same_mod_conj k r r' :
 In r (TheRoots k) -> In r' (TheRoots k) -> Cmod r = Cmod r' ->
 r = r' \/ r = Cconj r'.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - now rewrite TheRoots_0.
 - intros IN IN'.
   rewrite TheRoots_roots, IsRoot_alt in IN, IN' by trivial.
   intros E.
   assert (R := ThePoly.root_equal_Cmod_Re _ _ _ IN IN' E).
   assert (I := ThePoly.root_equal_Cmod_Im _ _ _ IN IN' E).
   clear IN IN' E.
   destruct r as (x,y), r' as (x',y'). simpl in *.
   subst x'.
   unfold Rabs in I. unfold Cconj; simpl.
   destruct (Rcase_abs y), (Rcase_abs y'); try subst;
   try (left; f_equal; lra); try (right; f_equal; lra).
Qed.

(** Description of the root ordering for complex roots *)

Lemma TheRoots_conj k p : (1<2*p<k)%nat ->
  let r := root_r k (2*p-1) in
  let r' := root_r k (2*p) in
  0 < Im r /\ r' = Cconj r.
Proof.
 intros Hp.
 replace (2*p-1)%nat with (2*(p-1)+1)%nat by lia.
 replace (2*p)%nat with (2*(p-1)+2)%nat by lia.
 apply (ThePoly.SortedRoots_im_pos k); try lia.
 apply SortedRoots_alt, TheRoots_ok. lia.
Qed.

(** In this ordering, roots are weakly decreasing in modulus. *)

Lemma TheRoots_mod_decr k n m :
  (n < m < k)%nat -> Cmod (root_r k n) >= Cmod (root_r k m).
Proof.
 intros H.
 assert (OK := TheRoots_ok k).
 rewrite SortedRoots_alt in OK by lia.
 apply ThePoly.SortedRoots_Cmod_sorted in OK.
 rewrite ThePoly.StronglySorted_nth in OK.
 apply OK. now rewrite TheRoots_length.
Qed.

(** Particular cases : roots for Q_1 .. Q_5 *)

Lemma TheRoots_1 : TheRoots 1 = [2].
Proof.
 generalize (TheRoots_first 1 lia).
 generalize (TheRoots_length 1).
 unfold root_r, Cnth.
 destruct (TheRoots 1) as [|x [|y l]]; try easy. simpl. now intros _ ->.
Qed.

Lemma TheRoots_2 : TheRoots 2 = [(1+sqrt 5)/2; (1-sqrt 5)/2].
Proof.
 generalize (TheRoots_first 2 lia).
 generalize (TheRoots_last 2 lia (ex_intro _ 1%nat eq_refl)).
 generalize (TheRoots_length 2).
 unfold root_r, Cnth.
 destruct (TheRoots 2) as [|x [|y [|z l]]]; try easy. cbn -[Mu.nu].
 intros _ -> ->. f_equal.
 - unfold β. simpl. now rewrite Mu.mu_2, RtoC_div, RtoC_plus.
 - f_equal. rewrite Mu.nu_2. now rewrite RtoC_div, RtoC_minus.
Qed.

Lemma TheRoots_3 : TheRoots 3 = F3.roots.
Proof.
 apply (SortedRoots_unique 3); try apply TheRoots_ok.
 rewrite SortedRoots_alt; simpl; try lia. apply F3.roots_sorted.
Qed.

Lemma TheRoots_4 : TheRoots 4 = F4.roots.
Proof.
 apply (SortedRoots_unique 4); try apply TheRoots_ok.
 rewrite SortedRoots_alt; simpl; try lia. apply F4.roots_sorted.
Qed.

Lemma TheRoots_5 : TheRoots 5 = F5.roots.
Proof.
 apply (SortedRoots_unique 5); try apply TheRoots_ok.
 rewrite SortedRoots_alt; simpl; try lia. apply F5.roots_sorted.
Qed.

(** Proposition 6.8, in three parts *)

Lemma secondary_low k : (2 <= k <= 4)%nat -> Cmod (root_r k 1) < 1.
Proof.
 intros K. unfold root_r.
 destruct k as [|[|[|[|[|k]]]]]; try lia; clear K.
 - rewrite TheRoots_2. unfold Cnth. simpl.
   rewrite <- RtoC_minus, <-RtoC_div, Cmod_R.
   apply Rabs_def1.
   + rewrite <- Rcomplements.Rdiv_lt_1 by lra.
     generalize (sqrt_pos 5). lra.
   + apply Ropp_lt_cancel. rewrite Ropp_involutive, <- Ropp_div.
     rewrite <- Rcomplements.Rdiv_lt_1 by lra. ring_simplify.
     rewrite Rlt_minus_l. apply MoreReals.Rlt_pow2_inv; try lra.
     rewrite pow2_sqrt; lra.
 - rewrite TheRoots_3. unfold F3.roots, Cnth; simpl.
   generalize F3.αmod_approx. unfold Approx.Approx. lra.
 - rewrite TheRoots_4. unfold F3.roots, Cnth; simpl.
   generalize F4.αmod_approx. unfold Approx.Approx. lra.
Qed.

Lemma secondary_mod1 : Cmod (root_r 5 1) = 1%R.
Proof.
 unfold root_r. rewrite TheRoots_5. apply F5.γmod.
Qed.

(** Note: for once, the following Coq proof differ sensibly from the
    article proof, since the article can simply rely on well-known
    results about Pisot and Salem numbers. In Coq we specialize the first
    part of the original proof by Siegel about the smallest Pisot number.
    More details in file SecondRoot. *)

Lemma secondary_high k : (6 <= k)%nat -> Cmod (root_r k 1) > 1.
Proof.
 intros. apply (SecondRoot.large_second_best_root k); try lia.
 apply SortedRoots_alt, TheRoots_ok; lia.
Qed.

(** ** Section 7 : Algebraic expressions of Fibonacci-like sequences *)

(** Proposition 7.1 *)

Lemma A_ge_mu_pow k n : k<>O -> ((β k)^n <= A k n)%R.
Proof.
 intros K. unfold β, A. apply Freq.A_ge_mu_pow.
Qed.

Definition coef_c k i := let r := root_r k i in r^k / (k*r-(k-1)).

Lemma coef_c_alt k i : coef_c k i = ThePoly.coefA k (root_r k i).
Proof.
 easy.
Qed.

(** Proposition 7.2.
    Note: [Sigma f a b] is [f a + ... + f (b-1)]. It is defined in MoreSum. *)

Lemma Equation_A k n : k<>O ->
  RtoC (A k n) = Sigma (fun i => coef_c k i * (root_r k i)^n) 0 k.
Proof.
 intros K. unfold A. rewrite (ThePoly.Equation_A k (TheRoots k)).
 2:{ apply SortedRoots_alt, TheRoots_ok; trivial. }
 rewrite Clistsum_map with (d:=0). rewrite TheRoots_length.
 rewrite Sigma_0. apply big_sum_eq_bounded.
 intros x Hx. now rewrite coef_c_alt.
Qed.

Lemma coef_c_nonzero k i : (i<k)%nat -> coef_c k i <> 0.
Proof.
 intros K. rewrite coef_c_alt by lia. apply ThePoly.coefA_nz.
 apply IsRoot_alt, TheRoots_roots, nth_In; try lia.
 now rewrite TheRoots_length.
Qed.

Definition coef_c_0 k : R := ThePoly.coef_mu k.

Lemma coef_c_0_real k : k<>O -> coef_c k 0 = RtoC (coef_c_0 k).
Proof.
 intros K. rewrite coef_c_alt.
 rewrite TheRoots_first; trivial.
 symmetry. apply ThePoly.coef_mu_ok.
Qed.

Lemma coef_c_0_ge_1 k : 1 <= coef_c_0 k.
Proof.
 unfold coef_c_0. apply Freq.coef_mu_ge1.
Qed.

Local Close Scope C_scope.

Lemma A_div_pow_beta_limit k :
 is_lim_seq (fun n => A k n / β k ^n) (coef_c_0 k).
Proof.
 unfold A, β, coef_c_0. apply ThePoly.A_div_pow_mu_limit.
Qed.

Lemma A_ratio k : is_lim_seq (fun n => A k (S n) / A k n) (β k).
Proof.
 unfold A, β. apply Freq.A_ratio.
Qed.

Local Open Scope C_scope.

Definition coef_d k i := coef_c k i * (/root_r k i - α k).

Lemma coef_d_alt k i : k<>O -> coef_d k i = ThePoly.coefdA k (root_r k i).
Proof.
 intros K. unfold coef_d, ThePoly.coefdA. now rewrite coef_c_alt.
Qed.

Lemma coef_d_0 k : k<>O -> coef_d k 0 = 0.
Proof.
 intros K. unfold coef_d. rewrite TheRoots_first by trivial.
 rewrite α_β. unfold Rdiv. rewrite Rmult_1_l, RtoC_inv, Cinv_inv. ring.
Qed.

Lemma coef_d_nz k i : (0<i<k)%nat -> coef_d k i <> 0.
Proof.
 intros. rewrite coef_d_alt by lia. apply ThePoly.coefdA_nz.
 apply IsRoot_alt, TheRoots_roots, nth_In; try lia.
 rewrite TheRoots_length; lia.
 fold (β k). rewrite <- TheRoots_first by lia. intros E.
 apply NoDup_nth in E; rewrite ?TheRoots_length; try lia.
 apply TheRoots_nodup.
Qed.

(** Proposition 7.3 *)

Lemma Equation_dA k n : (1 < k)%nat ->
  RtoC (A k (n - 1) - α k * A k n) =
  Sigma (fun i => coef_d k i * (root_r k i)^n) 1 k.
Proof.
 intros K. unfold A. rewrite Sigma_alt by lia.
 rewrite (ThePoly.Equation_dA k (TheRoots k)); try lia.
 2:{ apply SortedRoots_alt, TheRoots_ok; lia. }
 rewrite Clistsum_map with (d:=0).
 replace (length (tl (TheRoots k))) with (k-1)%nat.
 2:{ generalize (TheRoots_length k).
     destruct (TheRoots k); simpl; try lia. }
 apply big_sum_eq_bounded.
 intros x Hx. rewrite coef_d_alt by lia.
 unfold root_r, Cnth.
 generalize (TheRoots_length k).
 destruct (TheRoots k); simpl; easy || lia.
Qed.

(** Proposition 7.4 *)

Lemma affine_cos_pos (a b : R) : sin a <> R0 ->
  forall N, exists n, (N<=n)%nat /\ 1/2 <= cos (a * n + b).
Proof.
 exact (MoreReals.affine_cos_pos a b).
Qed.

Lemma affine_cos_neg (a b : R) : sin a <> R0 ->
  forall N, exists n, (N<=n)%nat /\ cos (a * n + b) <= -1/2.
Proof.
 exact (MoreReals.affine_cos_neg a b).
Qed.

(** Proposition 7.5.
    NB: Actually, this lemma also holds for lower values of k,
    but it is of little interest before k>=6 *)

Lemma dA_lower_bound k : (6<=k)%nat ->
 exists c : posreal,
 forall N, exists n, (N<=n)%nat /\
    c * (Cmod (root_r k 1))^n < A k (n-1) - α k * A k n.
Proof.
 intros. apply ThePoly.dA_expo. lia. apply SortedRoots_alt, TheRoots_ok; lia.
Qed.

Lemma dA_upper_bound k : (6<=k)%nat ->
 exists c : posreal,
 forall N, exists n, (N<=n)%nat /\
    A k (n-1) - α k * A k n < -c * (Cmod (root_r k 1))^n .
Proof.
 intros. apply ThePoly.dA_expo'. lia. apply SortedRoots_alt, TheRoots_ok; lia.
Qed.

Lemma dA_sup_gen k : (6<=k)%nat ->
 is_sup_seq (fun n => A k (n-1) - α k * A k n)%R Rbar.p_infty.
Proof.
 intros. apply Freq.dA_sup_k6. lia.
Qed.

Lemma dA_inf_gen k : (6<=k)%nat ->
 is_inf_seq (fun n => A k (n-1) - α k * A k n)%R Rbar.m_infty.
Proof.
 intros. apply Freq.dA_inf_k6. lia.
Qed.


(** ** Section 8 : Discrepancy : maximal distance to the linear equivalent *)

(** Definition 8.1 *)

Definition δ k n := (F k n - α k * n)%R.
Definition supδ k := Sup_seq (δ k).
Definition infδ k := Inf_seq (δ k).
Definition Δ k := Sup_seq (fun n => Rabs (δ k n)).

(** Proposition 8.3.
    Note that Clistsum is the sum of all elements of a complex list. *)

Lemma Equation_delta k n : (2<=k)%nat ->
 RtoC (δ k n) =
 Clistsum (map
          (fun m => Sigma (fun i => coef_d k i * (root_r k i)^m) 1 k)
          (decomp k n)).
Proof.
 intros. unfold δ. rewrite F_alt by lia.
 rewrite (ThePoly.Equation_delta k (TheRoots k)); try lia.
 2:{ apply SortedRoots_alt, TheRoots_ok; lia. }
 unfold decomp. f_equal. apply map_ext. intros a.
 rewrite <- Equation_dA by lia. symmetry. unfold A.
 apply ThePoly.Equation_dA; try lia.
 apply SortedRoots_alt, TheRoots_ok; lia.
Qed.

Lemma Equation_delta' k n : (2<=k)%nat ->
 RtoC (δ k n) =
 Sigma (fun i => coef_d k i *
                 Clistsum (map (Cpow (root_r k i)) (decomp k n))) 1 k.
Proof.
 intros. unfold δ. rewrite F_alt by lia.
 rewrite (ThePoly.Equation_delta' k (TheRoots k)); try lia.
 2:{ apply SortedRoots_alt, TheRoots_ok; lia. }
 unfold decomp. rewrite Clistsum_map with (d:=0).
 replace (length (tl (TheRoots k))) with (k-1)%nat.
 2:{ generalize (TheRoots_length k).
     destruct (TheRoots k); simpl; try lia. }
 rewrite Sigma_alt by lia.
 apply big_sum_eq_bounded.
 intros x Hx. rewrite coef_d_alt by lia.
 unfold root_r, Cnth.
 generalize (TheRoots_length k).
 destruct (TheRoots k); simpl; easy || lia.
Qed.

Local Close Scope C_scope.

(** Theorem 8.2 and 8.5 together.
    No Coq proof yet about the speed of divergence. *)

Lemma supdelta_gen k : (5<=k)%nat -> supδ k = Rbar.p_infty.
Proof.
 intros.
 apply is_sup_seq_unique.
 eapply is_sup_seq_ext.
 - intros n. unfold δ. rewrite F_alt; lia || easy.
 - destruct (Nat.eq_dec k 5) as [->|K'].
   + apply F5.delta_sup_k5.
   + apply Freq.delta_sup_k6; lia.
Qed.

Lemma infdelta_gen k : (5<=k)%nat -> infδ k = Rbar.m_infty.
Proof.
 intros.
 apply is_inf_seq_unique.
 eapply is_inf_seq_ext.
 - intros n. unfold δ. rewrite F_alt; lia || easy.
 - destruct (Nat.eq_dec k 5) as [->|K'].
   + apply F5.delta_inf_k5.
   + apply Freq.delta_inf_k6; lia.
Qed.

Lemma sup_abs (u:nat -> R) :
  Sup_seq u = Rbar.p_infty -> Sup_seq (fun n => Rabs (u n)) = Rbar.p_infty.
Proof.
 intros Hu.
 assert (Hu' := Sup_seq_correct u). rewrite Hu in Hu'.
 apply is_sup_seq_unique.
 intros M. destruct (Hu' M) as (n & H). simpl in H.
 exists n. simpl. apply Rlt_le_trans with (u n); trivial. apply Rle_abs.
Qed.

Lemma Delta_gen k : (5<=k)%nat -> Δ k = Rbar.p_infty.
Proof.
 intros Hk. apply sup_abs. now apply supdelta_gen.
Qed.

(** Theorem 8.7 *)

Lemma delta_bound_3 n : Rabs (δ 3 n) <= 0.854187179928304211983581540152668.
Proof.
 unfold δ. rewrite F_alt by lia. apply F3.abs_diff_bound.
Qed.

Lemma Delta_sup_3 : Rbar.Rbar_lt (Δ 3) 1.
Proof.
 unfold Δ. erewrite Sup_seq_ext.
 - apply F3.sup_diff_lt_1.
 - intros n. simpl. unfold δ. now rewrite F_alt by lia.
Qed.

Lemma delta_bound_4 n : Rabs (δ 4 n) <= 1.5834687793247475.
Proof.
 unfold δ. rewrite F_alt by lia. apply F4.abs_diff_bound.
Qed.

Lemma Delta_sup_4 : Rbar.Rbar_lt (Δ 4) 2.
Proof.
 unfold Δ. erewrite Sup_seq_ext.
 - apply F4.sup_diff0_lt_2.
 - intros n. simpl. unfold δ. now rewrite F_alt, <- F4.diff0_alt by lia.
Qed.

(*
Print Assumptions Delta_gen.
Print Assumptions Delta_sup_3.
Print Assumptions Delta_sup_4.
*)

(** Corollary 8.8 *)

Lemma F3_natpart n :
  let d := F 3 n - nat_part (α 3 * n) in
  d = 0 \/ d = 1.
Proof.
 rewrite F_alt by lia. simpl.
 destruct (F3.h_natpart_or n) as [E|E]; unfold GenAdd.h in *;
  rewrite E; unfold F3.τ, α; simpl Nat.sub.
 - left. ring.
 - right. rewrite S_INR. ring.
Qed.

Lemma F4_natpart n :
  let d := F 4 n - nat_part (α 4 * n) in
  d = -1 \/ d = 0 \/ d = 1 \/ d = 2.
Proof.
 rewrite F_alt by lia. simpl.
 assert (U := F4.f4_natpart_lower n).
 assert (V := F4.f4_natpart_higher n).
 apply le_INR in U, V.
 rewrite plus_INR in U, V.
 rewrite (INR_IZR_INZ 1) in U. rewrite (INR_IZR_INZ 2) in V. simpl in U,V.
 change F4.τ with (α 4) in U,V.
 remember (Rminus _ _) as d eqn:E.
 assert (-1 <= d <= 2) by (rewrite E; lra). clear U V.
 rewrite !INR_IZR_INZ, Z_R_minus in E.
 remember (Z.sub _ _) as z eqn:E'. clear E'. subst d.
 destruct H as (H,H'). apply le_IZR in H, H'.
 assert (Hz : (z = -1 \/ z = 0 \/ z = 1 \/ z = 2)%Z) by lia.
 destruct Hz as [->|[->|[-> | ->]]];
 [ now left | right; now left | do 2 right; now left | now do 3 right].
Qed.

(** Corollary 8.10 *)

Lemma F3_almostadd p n : Rabs (F 3 (p+n) - F 3 p - F 3 n) <= 2.
Proof.
 rewrite !F_alt by lia. simpl. apply Rabs_le.
 generalize (F3.h_quasiadd p n). unfold GenAdd.h.
 intros (U,V). apply le_INR in U, V.
 rewrite !plus_INR in V.
 rewrite (INR_IZR_INZ 2) in V. simpl in V.
 split. 2:lra.
 destruct (Nat.le_gt_cases 2 (GenG.f 3 p + GenG.f 3 n)) as [H|H].
 - rewrite minus_INR in U by lia.
   rewrite (INR_IZR_INZ 2), plus_INR in U. simpl in U. lra.
 - apply lt_INR in H. rewrite plus_INR in H.
   rewrite (INR_IZR_INZ 2) in H. simpl in H.
   generalize (pos_INR (GenG.f 3 (p+n))). lra.
Qed.

Lemma F4_almostadd p n : Rabs (F 4 (p+n) - F 4 p - F 4 n) <= 4.
Proof.
 rewrite !F_alt by lia. simpl. apply Rabs_le.
 generalize (F4.f4_quasiadd p n).
 intros (U,V). apply le_INR in U,V.
 rewrite !plus_INR in V.
 rewrite (INR_IZR_INZ 4) in V. simpl in V.
 split. 2:lra.
 destruct (Nat.le_gt_cases 4 (GenG.f 4 p + GenG.f 4 n)) as [H|H].
 - rewrite minus_INR in U by lia.
   rewrite (INR_IZR_INZ 4), plus_INR in U. simpl in U. lra.
 - apply lt_INR in H. rewrite plus_INR in H.
   rewrite (INR_IZR_INZ 4) in H. simpl in H.
   generalize (pos_INR (GenG.f 4 (p+n))). lra.
Qed.

(** Proposition 8.11 *)

Lemma no_almostadd_after_k5 k M : (5 <= k)%nat ->
 ~(forall p n, Rabs (F k (p+n) - F k p - F k n) <= M).
Proof.
 intros K QA.
 assert (BD : forall n, Rabs (δ k n) <= M).
 { intros n. unfold δ. destruct (Nat.eq_dec n 0) as [->|Hn].
   { generalize (QA O O). simpl. now rewrite Rmult_0_r, !Rminus_0_r. }
   apply Rcomplements.Rabs_le_between. split.
   - apply Rcomplements.Rle_minus_r. rewrite Rplus_comm.
     apply Rcomplements.Rle_minus_l. apply Rcomplements.Rle_div_r.
     destruct n; try lia. generalize (RSpos n); lra.
     set (u := fun n => F k n + M).
     change (α k <= u n / n).
     destruct n; try lia.
     apply (is_inf_seq_minor (fun n => u (S n)/S n) (α k)).
     clear n Hn.
     assert (Hu : forall p n, u (p + n)%nat <= u p + u n).
     { intros p q. unfold u. specialize (QA p q).
       apply Rcomplements.Rabs_le_between in QA. lra. }
     assert (Lu := Fekete_subadditive_lemma u Hu). cbn -[INR] in Lu.
     assert (Lu' : is_lim_seq (fun n => u n / n) (α k)).
     { apply (is_lim_seq_ext_loc (fun n => F k n/n + M/n)).
       exists 1%nat. intros p Hp. unfold u. field. destruct p; try lia.
       generalize (RSpos p); lra.
       replace (α k) with ((α k)^1+0) by ring.
       apply is_lim_seq_plus'.
       apply (Fkj_limit k 1); lia.
       apply is_lim_seq_bound with (Rabs M); intros; lra. }
     apply is_lim_seq_unique in Lu, Lu'. rewrite <- Lu', Lu.
     apply Inf_seq_correct.
   - apply Rcomplements.Rle_minus_l. rewrite Rplus_comm.
     rewrite <- Rcomplements.Rle_minus_l. apply Rcomplements.Rle_div_l.
     destruct n; try lia. generalize (RSpos n); lra.
     set (u := fun n => F k n - M).
     change (u n / n <= α k).
     destruct n; try lia.
     apply (is_sup_seq_major (fun n => u (S n)/S n) (α k)).
     clear n Hn.
     assert (Hu : forall p n, u (p + n)%nat >= u p + u n).
     { intros p q. unfold u. specialize (QA p q).
       apply Rcomplements.Rabs_le_between in QA. lra. }
     assert (Lu := Fekete_superadditive_lemma u Hu). cbn -[INR] in Lu.
     assert (Lu' : is_lim_seq (fun n => u n / n) (α k)).
     { apply (is_lim_seq_ext_loc (fun n => F k n/n - M/n)).
       exists 1%nat. intros p Hp. unfold u. field. destruct p; try lia.
       generalize (RSpos p); lra.
       replace (α k) with ((α k)^1-0) by ring.
       apply is_lim_seq_minus'.
       apply (Fkj_limit k 1); lia.
       apply is_lim_seq_bound with (Rabs M); intros; lra. }
     apply is_lim_seq_unique in Lu, Lu'. rewrite <- Lu', Lu.
     apply Sup_seq_correct. }
 assert (DS := Sup_seq_correct (fun n => Rabs (δ k n))).
 fold (Δ k) in DS.
 rewrite Delta_gen in DS by lia.
 destruct (DS M) as (n & Hn). simpl in Hn. specialize (BD n). lra.
Qed.

(** Proposition 8.12 *)

Lemma no_intpart_after_k3 k (a b : R) :
  (3 <= k)%nat -> ~(forall n, Z.of_nat (F k n) = Int_part (a * n + b)).
Proof.
 intros K E.
 assert (L : is_lim_seq (fun n => IZR (Int_part (a * n + b))/n) a).
 { clear K E. apply is_lim_seq_incr_1.
   apply is_lim_seq_le_le with (u := fun n => a+(b-1)/S n)
                               (w := fun n => a + b/S n).
   - intro n. split.
     + replace (a+(b-1)/S n) with ((a*S n+b-1)/S n).
       2:field; generalize (RSpos n); lra.
       unfold Rdiv. apply Rmult_le_compat_r.
       generalize (Rinv_0_lt_compat (S n)) (RSpos n). lra.
       rewrite (int_frac (a*S n + b)) at 1.
       generalize (base_fp (a*S n + b)); lra.
     + replace (a+b/S n) with ((a*S n+b)/S n).
       2:field; generalize (RSpos n); lra.
       unfold Rdiv. apply Rmult_le_compat_r.
       generalize (Rinv_0_lt_compat (S n)) (RSpos n). lra.
       rewrite (int_frac (a*S n + b)) at 2.
       generalize (base_fp (a*S n + b)); lra.
   - rewrite <- (Rplus_0_r a) at 1.
     apply is_lim_seq_plus'; try apply is_lim_seq_const.
     rewrite <- is_lim_seq_incr_1 with (u := (fun n => (b-1)/n)).
     apply is_lim_seq_bound with (K:=Rabs (b-1)); intros; lra.
   - rewrite <- (Rplus_0_r a) at 1.
     apply is_lim_seq_plus'; try apply is_lim_seq_const.
     rewrite <- is_lim_seq_incr_1 with (u := (fun n => b/n)).
     apply is_lim_seq_bound with (K:=Rabs b); intros; lra. }
 replace a with (α k) in *. clear a L.
 2:{ apply is_lim_seq_ext with (v:= (fun n => F k n /n)) in L.
     2:{ intros n. f_equal. rewrite <- E. symmetry. apply INR_IZR_INZ. }
     assert (H := Fkj_limit k 1 lia). simpl in H.
     rewrite Rmult_1_r in H. apply is_lim_seq_unique in H,L. congruence. }
 assert (B : forall n, Rabs (δ k n) <= Rabs b + 1).
 { intros n. unfold δ. specialize (E n).
   assert (E' := int_frac (α k * n + b)).
   replace (F k n - α k * n) with (b - frac_part (α k * n + b)).
   2:{ rewrite (INR_IZR_INZ (F k n)), E. lra. }
   unfold Rminus. eapply Rle_trans; [apply Rabs_triang|].
   apply Rplus_le_compat_l. rewrite Rabs_Ropp. apply Rabs_le.
   generalize (base_fp (α k*n+b)). lra. }
 destruct (Nat.le_gt_cases 5 k) as [K'|K'].
 { assert (DS := Sup_seq_correct (fun n => Rabs (δ k n))).
   fold (Δ k) in DS. rewrite Delta_gen in DS by lia.
   destruct (DS (Rabs b +1)) as (n & LT).
   specialize (B n). simpl in *. lra. }
 destruct (Nat.eq_dec k 4) as [->|K4].
 { clear K K' B.
   assert (E2 := E 2%nat). assert (E6 := E 6%nat).
   rewrite (INR_IZR_INZ 2), (INR_IZR_INZ 6) in *.
   change (F 4 2) with 1%nat in E2.
   change (F 4 6) with 5%nat in E6.
   symmetry in E2; symmetry in E6. rewrite <- int_part_iff in *.
   simpl IZR in *.
   unfold α in *. simpl in *. generalize Mu.tau_4. lra. }
 replace k with 3%nat in * by lia.
 { clear K K' K4 B.
   assert (E5 := E 5%nat). assert (E8 := E 8%nat).
   rewrite (INR_IZR_INZ 5), (INR_IZR_INZ 8) in *.
   change (F 3 5) with 4%nat in E5.
   change (F 3 8) with 5%nat in E8.
   symmetry in E5; symmetry in E8. rewrite <- int_part_iff in *.
   simpl IZR in *.
   unfold α in *. simpl in *. generalize Mu.tau_3. lra. }
Qed.

Lemma no_ceil_after_k3 k (a b : R) :
  (3 <= k)%nat -> ~(forall n, Z.of_nat (F k n) = ceil (a * n + b)).
Proof.
 intros K E.
 assert (L : is_lim_seq (fun n => IZR (ceil (a * n + b))/n) a).
 { clear K E. apply is_lim_seq_incr_1.
   apply is_lim_seq_le_le with (u := fun n => a + b/S n)
                               (w := fun n => a + (b+1)/S n).
   - intro n. split.
     + replace (a+b/S n) with ((a*S n+b)/S n).
       2:field; generalize (RSpos n); lra.
       unfold Rdiv. apply Rmult_le_compat_r.
       generalize (Rinv_0_lt_compat (S n)) (RSpos n). lra.
       apply ceil_bound.
     + replace (a+(b+1)/S n) with ((a*S n+b+1)/S n).
       2:field; generalize (RSpos n); lra.
       unfold Rdiv. apply Rmult_le_compat_r.
       generalize (Rinv_0_lt_compat (S n)) (RSpos n). lra.
       apply Rlt_le. apply ceil_bound.
   - rewrite <- (Rplus_0_r a) at 1.
     apply is_lim_seq_plus'; try apply is_lim_seq_const.
     rewrite <- is_lim_seq_incr_1 with (u := (fun n => b/n)).
     apply is_lim_seq_bound with (K:=Rabs b); intros; lra.
   - rewrite <- (Rplus_0_r a) at 1.
     apply is_lim_seq_plus'; try apply is_lim_seq_const.
     rewrite <- is_lim_seq_incr_1 with (u := (fun n => (b+1)/n)).
     apply is_lim_seq_bound with (K:=Rabs (b+1)); intros; lra. }
 replace a with (α k) in *. clear a L.
 2:{ apply is_lim_seq_ext with (v:= (fun n => F k n /n)) in L.
     2:{ intros n. f_equal. rewrite <- E. symmetry. apply INR_IZR_INZ. }
     assert (H := Fkj_limit k 1 lia). simpl in H.
     rewrite Rmult_1_r in H. apply is_lim_seq_unique in H,L. congruence. }
 assert (B : forall n, Rabs (δ k n) <= Rabs b + 1).
 { intros n. unfold δ. specialize (E n).
   assert (E' := ceil_bound (α k * n + b)).
   apply Rabs_le. rewrite INR_IZR_INZ, E. split.
   - apply Rle_trans with b; try lra.
     generalize (Rcomplements.Rabs_maj2 b); lra.
   - apply Rle_trans with (b+1); try lra.
     generalize (Rle_abs b); lra. }
 destruct (Nat.le_gt_cases 5 k) as [K'|K'].
 { assert (DS := Sup_seq_correct (fun n => Rabs (δ k n))).
   fold (Δ k) in DS. rewrite Delta_gen in DS by lia.
   destruct (DS (Rabs b +1)) as (n & LT).
   specialize (B n). simpl in *. lra. }
 destruct (Nat.eq_dec k 4) as [->|K4].
 { clear K K' B.
   assert (E2 := E 2%nat). assert (E6 := E 6%nat).
   rewrite (INR_IZR_INZ 2), (INR_IZR_INZ 6) in *.
   change (F 4 2) with 1%nat in E2.
   change (F 4 6) with 5%nat in E6.
   symmetry in E2; symmetry in E6. rewrite <- ceil_iff in *.
   simpl IZR in *.
   unfold α in *. simpl in *. generalize Mu.tau_4. lra. }
 replace k with 3%nat in * by lia.
 { clear K K' K4 B.
   assert (E5 := E 5%nat). assert (E8 := E 8%nat).
   rewrite (INR_IZR_INZ 5), (INR_IZR_INZ 8) in *.
   change (F 3 5) with 4%nat in E5.
   change (F 3 8) with 5%nat in E8.
   symmetry in E5; symmetry in E8. rewrite <- ceil_iff in *.
   simpl IZR in *.
   unfold α in *. simpl in *. generalize Mu.tau_3. lra. }
Qed.
