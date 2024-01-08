Require Import MoreFun MoreList DeltaList GenFib GenG Words Words2 Complexity.
Import ListNotations.

(** * Study of Left-Special words *)

(** Especially, for all length p, [kseq k] has a unique left-special word,
    namely its initial prefix of length p.

    This is a particular case of this article + its Corrigendum :

    Complexity of Infinite Words Associated with Beta-expansions,
    C. Frougny, Z. Masáková, E. Pelantová, 2004.
*)

Definition LeftExt a u (f:sequence) := SubSeq (a::u) f.

Definition LeftSpecial u (f:sequence) :=
  exists a a', a<>a' /\ LeftExt a u f /\ LeftExt a' u f.

Definition RightExt u a (f:sequence) := SubSeq (u++[a]) f.

Definition RightSpecial u (f:sequence) :=
  exists a a', a<>a' /\ RightExt u a f /\ RightExt u a' f.

Definition AllLeftExts l u (f:sequence) :=
  NoDup l /\ forall a, In a l <-> LeftExt a u f.

Definition AllRightExts u l (f:sequence) :=
  NoDup l /\ forall a, In a l <-> RightExt u a f.

Lemma AllLeftExts_unique l l' u f :
 AllLeftExts l u f -> AllLeftExts l' u f -> Permutation l l'.
Proof.
 intros (ND,IN) (ND',IN').
 apply NoDup_Permutation; trivial.
 intros. now rewrite IN, IN'.
Qed.

Lemma AllRightExts_unique l l' u f :
 AllRightExts u l f -> AllRightExts u l' f -> Permutation l l'.
Proof.
 intros (ND,IN) (ND',IN').
 apply NoDup_Permutation; trivial.
 intros. now rewrite IN, IN'.
Qed.

Lemma LeftExt_letter k a u : LeftExt a u (kseq k) -> a <= k.
Proof.
  unfold LeftExt, SubSeq. intros (q, E). unfold subseq in E.
  simpl in E. injection E as E _.
  generalize (kseq_letters k q). lia.
Qed.

Lemma RightExt_letter k u a : RightExt u a (kseq k) -> a <= k.
Proof.
  unfold RightExt, SubSeq. intros (q, E). revert E.
  unfold subseq. rewrite app_length. simpl.
  rewrite Nat.add_succ_r, seq_S, map_app. simpl. intros E.
  apply app_inv' in E; trivial. destruct E as (_,[= ->]).
  apply kseq_letters.
Qed.

Lemma LeftExt_Prefix a u v f :
  Prefix v u -> LeftExt a u f -> LeftExt a v f.
Proof.
 unfold LeftExt. intros PR SU. eapply Sub_SubSeq; eauto.
 now apply Prefix_Sub, Prefix_cons.
Qed.

Lemma RightExt_Suffix a u v f :
  Suffix v u -> RightExt u a f -> RightExt v a f.
Proof.
 unfold RightExt. intros SU SU'. eapply Sub_SubSeq; eauto.
 now apply Suffix_Sub, Suffix_app_r.
Qed.

Lemma SubSeq_RightExt u f : SubSeq u f -> exists a, RightExt u a f.
Proof.
 unfold RightExt, SubSeq.
 intros (q, ->). exists (f (q+length u)), q.
 unfold subseq. rewrite app_length, map_length, seq_length. simpl.
 rewrite Nat.add_succ_r, seq_S, map_app. simpl. repeat f_equal; lia.
Qed.


Definition wordmem u l := existsb (listnat_eqb u) l.

Lemma wordmem_spec u l : wordmem u l = true <-> In u l.
Proof.
 unfold wordmem. rewrite existsb_exists. split.
 - intros (x & IN & E). revert E.
   case listnat_eqb_spec. now intros ->. easy.
 - intros IN. exists u. split; trivial. now case listnat_eqb_spec.
Qed.

Definition kleftexts k u :=
 let l := kfactors0opt k (S (length u)) in
 filter (fun a => wordmem (a::u) l) (seq 0 (S k)).

Definition klvalence k (u:word) := length (kleftexts k u).

Definition krightexts k u :=
 let l := kfactors0opt k (S (length u)) in
 filter (fun a => wordmem (u++[a]) l) (seq 0 (S k)).

Definition krvalence k (u:word) := length (krightexts k u).

Lemma kleftexts_ok k u : AllLeftExts (kleftexts k u) u (kseq k).
Proof.
 split.
 - apply NoDup_filter, seq_NoDup.
 - intros a.
   unfold kleftexts.
   rewrite filter_In, in_seq, wordmem_spec, kfactors0opt_in.
   split.
   + intros (_ & _ & SU). apply SU.
   + unfold LeftExt. intros SU. split; [|split]; trivial.
     red in SU. destruct SU as (q & E). unfold subseq in E. simpl in E.
     injection E as E _. generalize (kseq_letters k q); lia.
Qed.

Lemma krightexts_ok k u : AllRightExts u (krightexts k u) (kseq k).
Proof.
 split.
 - apply NoDup_filter, seq_NoDup.
 - intros a.
   unfold krightexts.
   rewrite filter_In, in_seq, wordmem_spec, kfactors0opt_in.
   split.
   + intros (_ & _ & SU). apply SU.
   + unfold RightExt. intros SU. split; [|split]; trivial.
     2:{ rewrite app_length; simpl; lia. }
     red in SU. destruct SU as (q & E). unfold subseq in E.
     rewrite app_length in E. simpl in *.
     rewrite Nat.add_succ_r, seq_S, map_app in E. simpl in E.
     apply app_inv' in E; trivial. destruct E as (_,E).
     injection E as E. generalize (kseq_letters k (q+(length u+0))); lia.
Qed.

Lemma klvalence_ok k l u :
  AllLeftExts l u (kseq k) -> klvalence k u = length l.
Proof.
 intros A. rewrite (@Permutation_length _ l (kleftexts k u)); try easy.
 eapply AllLeftExts_unique; eauto using kleftexts_ok.
Qed.

Lemma krvalence_ok k u l :
  AllRightExts u l (kseq k) -> krvalence k u = length l.
Proof.
 intros A. rewrite (@Permutation_length _ l (krightexts k u)); try easy.
 eapply AllRightExts_unique; eauto using krightexts_ok.
Qed.

Lemma kword_nz k n : kword k n <> [].
Proof.
 unfold word,letter. rewrite <- length_zero_iff_nil,  kword_len.
 generalize (A_nz k n); lia.
Qed.

Lemma kword_ls k p a : a <= k -> LeftExt a (kword k p) (kseq k).
Proof.
 intros Ha.
 set (q := a + p + S k - p mod S k).
 assert (p <= q).
 { generalize (Nat.mod_upper_bound p (S k)). lia. }
 assert (E : q mod S k = a).
 { unfold q. replace (a+p+S k) with (a+S k+p) by lia.
   rewrite (Nat.div_mod_eq p (S k)) at 1 by lia.
   rewrite Nat.add_assoc, Nat.add_sub.
   rewrite Nat.mul_comm, Nat.mod_add by lia.
   replace (S k) with (1 * S k) at 1 by lia. rewrite Nat.mod_add by lia.
   apply Nat.mod_small; lia. }
 apply LeftExt_Prefix with (kword k (q+2)).
 - apply kword_le_prefix; lia.
 - assert (SU : SubSeq (kword k (q+2+S k)) (kseq k)).
   { rewrite SubSeq_kseq_Sub_kword. exists (q+2+S k). apply Sub_id. }
   rewrite Nat.add_succ_r, kword_alt in SU by lia.
   replace (q+2+k-k) with (q+2) in SU by lia.
   rewrite (@app_removelast_last _ (kword k (q+2+k)) 0) in SU.
   2:{ apply kword_nz. }
   rewrite <- app_assoc in SU.
   rewrite kword_last in SU.
   replace (q+2+k+k) with (q+2*(S k)) in SU by lia.
   rewrite Nat.mod_add, E in SU by lia.
   red. eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id.
Qed.

Lemma kprefix_leftext k n a : a <= k -> LeftExt a (kprefix k n) (kseq k).
Proof.
 intros Ha.
 unfold kprefix.
 set (p := invA_up k n).
 apply LeftExt_Prefix with (kword k p).
 - rewrite Prefix_equiv. f_equal. rewrite firstn_length_le; trivial.
   rewrite kword_len. apply invA_up_spec.
 - now apply kword_ls.
Qed.

Lemma kprefix_allleftexts k n :
  AllLeftExts (seq 0 (S k)) (kprefix k n) (kseq k).
Proof.
 split.
 - apply seq_NoDup.
 - intros a. rewrite in_seq. split.
   + intros Ha. apply kprefix_leftext. lia.
   + intros Ha. apply LeftExt_letter in Ha. lia.
Qed.

Lemma kprefix_klvalence k n : klvalence k (kprefix k n) = S k.
Proof.
 rewrite <- (seq_length (S k) 0). apply klvalence_ok.
 apply kprefix_allleftexts.
Qed.

Lemma kseq_leftext k u : SubSeq u (kseq k) -> exists a, LeftExt a u (kseq k).
Proof.
 rewrite SubSeq_kseq_Sub_kword; intros (n, (v & w & E)).
 rewrite <- (rev_involutive v) in E.
 destruct (rev v) as [|a v']; simpl in E.
 - exists 0. replace u with (kprefix k (length u)).
   + apply kprefix_leftext; lia.
   + symmetry. rewrite kprefix_alt. change (PrefixSeq u (kseq k)).
     eapply Prefix_PrefixSeq.
     * now exists w.
     * rewrite E. apply kword_prefixseq.
 - exists a. red. rewrite SubSeq_kseq_Sub_kword. exists n.
   rewrite <- E, <- !app_assoc. simpl. now do 2 eexists.
Qed.

Lemma klvalence_nz k u : SubSeq u (kseq k) -> klvalence k u <> 0.
Proof.
 intros Hu.
 unfold klvalence. rewrite length_zero_iff_nil.
 destruct (kseq_leftext k u Hu) as (a & Ha).
 destruct (kleftexts_ok k u) as (ND,H). rewrite <- H in Ha.
 intros E. now rewrite E in Ha.
Qed.

Lemma krvalence_nz k u : SubSeq u (kseq k) -> krvalence k u <> 0.
Proof.
 intros Hu.
 unfold krvalence. rewrite length_zero_iff_nil.
 destruct (SubSeq_RightExt u _ Hu) as (a & Ha).
 destruct (krightexts_ok k u) as (ND,H). rewrite <- H in Ha.
 intros E. now rewrite E in Ha.
Qed.

Lemma klvalence_le_Sk k u : klvalence k u <= S k.
Proof.
 unfold klvalence, kleftexts.
 rewrite <- (seq_length (S k) 0) at 2. apply filter_length_le.
Qed.

Lemma krvalence_le_Sk k u : krvalence k u <= S k.
Proof.
 unfold krvalence, krightexts.
 rewrite <- (seq_length (S k) 0) at 2. apply filter_length_le.
Qed.

Lemma prefix_incl_allleftexts k u u' l l' :
  Prefix u u' -> AllLeftExts l u (kseq k) -> AllLeftExts l' u' (kseq k) ->
  incl l' l.
Proof.
 intros P (ND,Hu) (ND',Hu') a Ha. rewrite Hu' in Ha. apply Hu.
 eapply LeftExt_Prefix; eauto.
Qed.

Lemma prefix_klvalence k u v : Prefix u v -> klvalence k v <= klvalence k u.
Proof.
 intros P. unfold klvalence. apply NoDup_incl_length.
 - apply kleftexts_ok.
 - eapply prefix_incl_allleftexts; eauto using kleftexts_ok.
Qed.

Lemma suffix_incl_allrightexts k u u' l l' :
  Suffix u u' -> AllRightExts u l (kseq k) -> AllRightExts u' l' (kseq k) ->
  incl l' l.
Proof.
 intros P (ND,Hu) (ND',Hu') a Ha. rewrite Hu' in Ha. apply Hu.
 eapply RightExt_Suffix; eauto.
Qed.

Lemma suffix_krvalence k u v : Suffix u v -> krvalence k v <= krvalence k u.
Proof.
 intros P. unfold krvalence. apply NoDup_incl_length.
 - apply krightexts_ok.
 - eapply suffix_incl_allrightexts; eauto using krightexts_ok.
Qed.

(** Letters, what's before, what's after, valence of letters, etc *)

Definition next_letter k a := if a =? k then 0 else S a.
Definition prev_letter k a := if a =? 0 then k else pred a.

Lemma next_letter_le k a : a <= k -> next_letter k a <= k.
Proof.
 intros Ha. unfold next_letter. case Nat.eqb_spec; lia.
Qed.

Lemma prev_letter_le k a : a <= k -> prev_letter k a <= k.
Proof.
 intros Ha. unfold prev_letter. case Nat.eqb_spec; lia.
Qed.

Lemma next_letter_alt k a : a <= k -> next_letter k a = (S a) mod (S k).
Proof.
 intros Ha. unfold next_letter.
 case Nat.eqb_spec.
 - intros ->. symmetry. apply Nat.mod_same; lia.
 - intros. symmetry. apply Nat.mod_small. lia.
Qed.

Lemma prev_letter_alt k a : a <= k -> prev_letter k a = (a+k) mod (S k).
Proof.
 intros Ha. unfold prev_letter.
 case Nat.eqb_spec.
 - intros ->. symmetry. apply Nat.mod_small. lia.
 - intros. replace (a+k) with (a-1 + 1*(S k)) by lia.
   rewrite Nat.mod_add, Nat.mod_small; lia.
Qed.

Lemma next_prev_letter k a : a <= k -> next_letter k (prev_letter k a) = a.
Proof.
 intros Ha. unfold prev_letter.
 case Nat.eqb_spec.
 - intros ->. unfold next_letter. now rewrite Nat.eqb_refl.
 - intros. unfold next_letter. case Nat.eqb_spec; lia.
Qed.

Lemma prev_next_letter k a : a <= k -> prev_letter k (next_letter k a) = a.
Proof.
 intros Ha. unfold next_letter.
 case Nat.eqb_spec; trivial.
 intros ->. unfold prev_letter. now rewrite Nat.eqb_refl.
Qed.

Lemma ksubst_next_letter k a : a<>k -> ksubst k a = [next_letter k a].
Proof.
 intros A. unfold ksubst, next_letter. case Nat.eqb_spec; auto; lia.
Qed.

Lemma kseq_prev_letter k p :
  kseq k p <> k -> kseq k (p-1) = prev_letter k (kseq k p).
Proof.
 intros Ha.
 assert (Ha' := kseq_letters k p).
 remember (kseq k p) as a eqn:Ea in *.
 rewrite kseq_bounded_rank in *.
 unfold bounded_rank, omin, rank in *.
 set (l := decomp k p) in *.
 destruct l as [|r l'] eqn:Hl; try lia.
 replace r with a in * by lia.
 rewrite decomp_pred. fold l. rewrite Hl. simpl.
 destruct a as [|a]; unfold prev_letter; simpl.
 - assert (D := decomp_delta k p). fold l in D. rewrite Hl in D.
   destruct l'; simpl; trivial. inversion_clear D. lia.
 - replace (a-k) with 0 by lia. simpl. lia.
Qed.

Lemma kseq_next_letter k p :
  kseq k (S p) <> k -> kseq k (S p) = next_letter k (kseq k p).
Proof.
 intros Ha. replace p with (S p-1) at 2 by lia.
 rewrite kseq_prev_letter; trivial. rewrite next_prev_letter; trivial.
 apply kseq_letters.
Qed.

Lemma kseq_next_km1 k p : kseq k p = k-1 -> kseq k (S p) = k.
Proof.
 intros E.
 destruct (Nat.eq_dec (kseq k (S p)) k) as [E'|E']; trivial.
 rewrite kseq_next_letter, E; trivial.
 unfold next_letter.
 case Nat.eqb_spec; lia.
Qed.

Lemma all_letters_occur k a : a <= k -> kseq k (S a) = a.
Proof.
 intros Ha. rewrite kseq_bounded_rank. unfold bounded_rank, rank.
 replace (decomp k (S a)) with [a]. simpl. lia.
 symmetry. apply decomp_carac. constructor. simpl. rewrite A_base; lia.
Qed.

Lemma all_letters_subseq k a : a <= k <-> SubSeq [a] (kseq k).
Proof.
 split.
 - intros Ha. exists (S a). simpl. unfold subseq. simpl.
   now rewrite all_letters_occur.
 - apply LeftExt_letter.
Qed.

Lemma ls_head_k k a u : LeftSpecial (a::u) (kseq k) -> a = k.
Proof.
 intros (b & c & N & (p,Hb) & (q,Hc)).
 unfold subseq in *. simpl in *.
 injection Hb as Hb Hb' _.
 injection Hc as Hc Hc' _.
 destruct (Nat.eq_dec a k) as [A|A]; trivial. exfalso.
 assert (b = prev_letter k a).
 { rewrite Hb, Hb'. rewrite <- (kseq_prev_letter k (S p)) by lia.
   f_equal; lia. }
 assert (c = prev_letter k a).
 { rewrite Hc, Hc'. rewrite <- (kseq_prev_letter k (S q)) by lia.
   f_equal; lia. }
 lia.
Qed.

Lemma ls_knz k u : LeftSpecial u (kseq k) -> k<>0.
Proof.
 intros (a & b & AB & A & B). apply LeftExt_letter in A,B. lia.
Qed.

Lemma ls_head_nz k a u : LeftSpecial (a::u) (kseq k) -> a <> 0.
Proof.
 intros LS. rewrite (ls_head_k _ _ _ LS). now apply ls_knz in LS.
Qed.

Lemma AllRightExts_km1 k : AllRightExts [k-1] [k] (kseq k).
Proof.
 split.
 - repeat constructor. intuition.
 - intros a. simpl. split; [intros [<-|[ ]] | intros R; left].
   + exists k. unfold subseq. simpl. symmetry. f_equal.
     * destruct (Nat.eq_dec k 0) as [->|K]. easy.
       replace k with (S (k-1)) at 2 by lia.
       apply all_letters_occur; lia.
     * f_equal. now apply all_letters_occur.
   + destruct R as (q,R). unfold subseq in R. simpl in R.
     injection R as R ->. symmetry. now apply kseq_next_km1.
Qed.

Lemma krvalence_km1 k : krvalence k [k-1] = 1.
Proof.
 change 1 with (length [k]) at 2. apply krvalence_ok. apply AllRightExts_km1.
Qed.

Lemma krvalence_last_km1 k u :
  u<>[] -> SubSeq u (kseq k) -> last u 0 = k-1 -> krvalence k u = 1.
Proof.
 intros U U' L.
 assert (SU : Suffix [k-1] u).
 { exists (removelast u). symmetry. rewrite <- L.
   now apply app_removelast_last. }
 generalize (suffix_krvalence k _ _ SU) (krvalence_nz k u U').
 rewrite krvalence_km1. lia.
Qed.

Lemma letters_LeftExt k a b : b<k ->
 LeftExt a [b] (kseq k) <-> a = prev_letter k b.
Proof.
 intros B. split.
 - intros (q, E). unfold subseq in E. simpl in E. injection E as Ea Eb.
   subst. replace q with (S q - 1) at 1 by lia. apply kseq_prev_letter; lia.
 - intros ->. exists b. unfold subseq. simpl. f_equal; symmetry.
   + unfold prev_letter.
     case Nat.eqb_spec.
     * intros ->. apply kseq_k_0.
     * intros B'. replace b with (S (pred b)) at 1 by lia.
       apply all_letters_occur. lia.
   + f_equal. apply all_letters_occur. lia.
Qed.

Lemma letters_RightExt k a b :
  RightExt [a] b (kseq k) -> b = next_letter k a \/ b = k.
Proof.
 intros (q, E). unfold subseq in E. simpl in E. injection E as Ea Eb.
 case (Nat.eq_dec b k) as [Eb'|Eb']. now right. left. subst.
 now apply kseq_next_letter.
Qed.

Lemma letters_AllLeftExts k a l : a<k ->
  AllLeftExts l [a] (kseq k) <-> l = [prev_letter k a].
Proof.
 split.
 - intros (ND,A).
   assert (IC :incl l [prev_letter k a]).
   { intros x Hx. rewrite A in Hx. apply letters_LeftExt in Hx; try lia.
     simpl; intuition. }
   assert (length l <= 1).
   { change 1 with (length [prev_letter k a]).
     apply NoDup_incl_length; auto. }
   destruct l as [|x [|y l]]; simpl in *; try lia.
   + destruct (kseq_leftext k [a]) as (b & B).
     { apply all_letters_subseq; lia. }
     now rewrite <- A in B.
   + f_equal. specialize (IC x). simpl in *; intuition.
 - intros ->. split.
   + now repeat constructor.
   + intros b. rewrite letters_LeftExt; trivial. simpl; intuition.
Qed.

Lemma letters_AllRightExts_incl k a l :
  AllRightExts [a] l (kseq k) -> incl l [next_letter k a; k].
Proof.
 intros (_,A) x Hx. rewrite A in Hx. apply letters_RightExt in Hx.
 simpl; intuition.
Qed.

Lemma klvalence_letter k a : a<k -> klvalence k [a] = 1.
Proof.
 intros A. unfold klvalence.
 replace (kleftexts k [a]) with [prev_letter k a]; trivial.
 symmetry. apply letters_AllLeftExts; auto using kleftexts_ok.
Qed.

Lemma klvalence_letter_k k : klvalence k [k] = S k.
Proof.
 replace [k] with (kprefix k 1). apply kprefix_klvalence.
 now rewrite kprefix_alt.
Qed.

Lemma krvalence_letter k a : krvalence k [a] <= 2.
Proof.
 unfold krvalence. change 2 with (length [next_letter k a; k]).
 apply NoDup_incl_length. apply krightexts_ok.
 apply letters_AllRightExts_incl. apply krightexts_ok.
Qed.

(** Actually, all letters have krvalence 2 except (k-1) which krvalence is 1. *)

Lemma krvalence_le_2 k u : u<>[] -> krvalence k u <= 2.
Proof.
 intros Hu. transitivity (krvalence k [last u 0]).
 - apply suffix_krvalence.
   exists (removelast u). symmetry. now apply app_removelast_last.
 - apply krvalence_letter.
Qed.


(** Lemmas from the article by Frougny et al. *)

Lemma lemma_3_7_i k u a :
  LeftExt a u (kseq k) ->
  LeftExt (next_letter k a) (apply (ksubst k) u) (kseq k).
Proof.
 intros Ha. assert (Ha' := LeftExt_letter _ _ _ Ha).
 unfold LeftExt in *. rewrite SubSeq_kseq_Sub_kword in *.
 destruct Ha as (n, (v & w & E)). exists (S n).
 rewrite kword_S, <- E, !apply_app. simpl apply. clear E.
 unfold ksubst at 3. unfold next_letter.
 case Nat.eqb_spec; intros.
 - exists (apply (ksubst k) v ++ [k]), (apply (ksubst k) w).
   now rewrite <- !app_assoc.
 - now exists (apply (ksubst k) v), (apply (ksubst k) w).
Qed.

Lemma lemma_3_7_i_ls k u :
  LeftSpecial u (kseq k) ->
  LeftSpecial (apply (ksubst k) u) (kseq k).
Proof.
 intros (a & b & AB & A & B).
 assert (A' := LeftExt_letter _ _ _ A).
 assert (B' := LeftExt_letter _ _ _ B).
 apply lemma_3_7_i in A, B.
 exists (next_letter k a), (next_letter k b); repeat split; trivial.
 contradict AB.
 rewrite <- (prev_next_letter k a), <- (prev_next_letter k b) by trivial.
 now rewrite AB.
Qed.

Lemma PrefixSeq_substlength_prefix k u v :
  PrefixSeq u (kseq k) -> PrefixSeq v (kseq k) ->
  length (apply (ksubst k) u) <= length (apply (ksubst k) v) ->
  Prefix u v.
Proof.
 intros U V L.
 destruct (Nat.le_gt_cases (length u) (length v)).
 - eapply PrefixSeq_incl; eauto.
 - assert (P : Prefix v u) by (eapply PrefixSeq_incl; eauto; lia).
   destruct P as (w & <-).
   rewrite apply_app, app_length in L.
   assert (L' : length (apply (ksubst k) w) = 0) by lia.
   apply length_zero_iff_nil in L'.
   apply (ksubst_inv k w []) in L'. subst w. rewrite app_nil_r.
   apply Prefix_id.
Qed.

Lemma lemma_3_7_ii_aux k u a :
  hd 0 u <> 0 -> last u 0 <> k ->
  LeftExt a u (kseq k) ->
  exists v, apply (ksubst k) v = u /\
            LeftExt (prev_letter k a) v (kseq k).
Proof.
 intros HD LA Ha. assert (Ha' := LeftExt_letter _ _ _ Ha).
 unfold LeftExt in *. rewrite SubSeq_alt0 in Ha.
 destruct Ha as (w & (u1 & E) & P).
 destruct (ksubst_prefix_inv _ _ P) as (w' & r & E' & P' & [->|Hr]).
 - rewrite app_nil_r in E'.
   assert (Pu1 : PrefixSeq (u1++[a]) (kseq k)).
   { apply Prefix_PrefixSeq with w; trivial.
     exists u. now rewrite <- app_assoc. }
   destruct (ksubst_prefix_inv _ _ Pu1) as (u1' & r' & E1 & Pu1' & [->|Hr']).
   + rewrite app_nil_r in E1.
     assert (PR : Prefix u1' w').
     { eapply PrefixSeq_substlength_prefix; eauto.
       rewrite <- E1, <- E', <- E, !app_length. simpl. lia. }
     destruct PR as (u' & PR).
     exists u'. split.
     * rewrite <- PR in E'. rewrite apply_app, <- E, <- E1 in E'.
       change (a::u) with ([a]++u) in E'. rewrite app_assoc in E'.
       now apply app_inv_head in E'.
     * rewrite <- (rev_involutive u1') in *.
       destruct (rev u1') as [|a' u2']; simpl in E1.
       { now destruct u1. }
       { rewrite SubSeq_alt0. exists w'. split; trivial.
         exists (rev u2'). simpl in PR. rewrite <- app_assoc in PR.
         replace (prev_letter k a) with a'; trivial.
         revert E1. rewrite apply_app. simpl. rewrite app_nil_r.
         unfold ksubst at 2.
         case Nat.eqb_spec.
         - intros ->. change [k;0] with ([k]++[0]).
           rewrite app_assoc. intros E1. apply app_inv' in E1; trivial.
           now destruct E1 as (_,[= ->]).
         - intros NE E1. apply app_inv' in E1; trivial.
           now destruct E1 as (_,[= ->]). }
   + subst r'. apply app_inv' in E1; trivial. destruct E1 as (E1,[= ->]).
     assert (PR : Prefix u1' w').
     { eapply PrefixSeq_substlength_prefix; eauto.
       rewrite <- E1, <- E', <- E, !app_length. simpl. lia. }
     destruct PR as ([|a' u'] & PR).
     { rewrite app_nil_r in PR. exfalso.
       apply (f_equal (@length nat)) in E. rewrite app_length in E.
       simpl in E. subst. unfold letter in *; lia. }
     rewrite <- PR in E'. rewrite E1, E' in E.
     rewrite apply_app in E. apply app_inv_head in E. simpl in E.
     unfold ksubst in E at 1. destruct (Nat.eqb_spec a' k).
     * injection E as E. now rewrite E in HD.
     * injection E as E2 E3. exists u'. split. symmetry. apply E3.
       unfold prev_letter. rewrite E2 at 1. simpl. rewrite E2 at 1. simpl.
       rewrite SubSeq_alt0. exists w'. split; trivial.
       now exists u1'.
 - subst r. rewrite E' in E.
   assert (u=[]).
   { destruct (list_eq_dec Nat.eq_dec u []) as [U|U]; trivial.
     change (a::u) with ([a]++u) in E.
     rewrite (@app_removelast_last _ u 0 U) in E.
     rewrite !app_assoc in E.
     apply app_inv' in E; trivial. now destruct E as (_,[= E]). }
   now subst u.
Qed.

Lemma Sub_cons_r {A} (a:A) u : Sub u (a::u).
Proof.
 apply (Sub_app_l [a]), Sub_id.
Qed.

Lemma lemma_3_7_ii_cor k u : hd 0 u <> 0 -> last u 0 <> k ->
  SubSeq u (kseq k) ->
  exists v : word, apply (ksubst k) v = u /\ SubSeq v (kseq k).
Proof.
 intros U U' SU. destruct (kseq_leftext _ _ SU) as (a & LE).
 destruct (lemma_3_7_ii_aux k u a U U' LE) as (v & V & V').
 exists v. split; trivial. eapply Sub_SubSeq; eauto using Sub_cons_r.
Qed.

Lemma lemma_3_7_ii_all' k u l :
  SubSeq u (kseq k) -> hd 0 u <> 0 -> last u 0 <> k ->
  AllLeftExts l u (kseq k) ->
  exists v, apply (ksubst k) v = u /\
            AllLeftExts (map (prev_letter k) l) v (kseq k).
Proof.
 intros SU U U' (ND,A).
 destruct l as [|a l].
 { destruct (kseq_leftext k u SU) as (a & Ha). now rewrite <- A in Ha. }
 destruct (lemma_3_7_ii_aux k u a) as (v & Hv & Ha); trivial.
 { rewrite <- A. simpl; intuition. }
 exists v; split; auto. split.
 + apply NoDup_map_inv with (f:=next_letter k).
   rewrite map_map, map_ext_in with (g:=id), map_id; auto.
   intros c Hc. apply next_prev_letter. rewrite A in Hc.
   now apply LeftExt_letter in Hc.
 + intros c. rewrite in_map_iff. split.
   * intros (x & <- & IN). rewrite A in IN.
     destruct (lemma_3_7_ii_aux k u x) as (v' & Hv' & Hx); trivial.
     replace v' with v in *; auto.
     { apply (ksubst_inv k). now rewrite Hv, Hv'. }
   * intros Hc. exists (next_letter k c). split.
     { apply prev_next_letter. eapply LeftExt_letter; eauto. }
     rewrite A, <- Hv. now apply lemma_3_7_i.
Qed.

Lemma lemma_3_7_ii_val' k u :
  SubSeq u (kseq k) -> hd 0 u <> 0 -> last u 0 <> k ->
  exists v, apply (ksubst k) v = u /\ klvalence k v = klvalence k u.
Proof.
 intros SU U U'.
 destruct (lemma_3_7_ii_all' k u (kleftexts k u) SU U U') as (v & Hv & H);
  auto using kleftexts_ok.
 exists v; split; auto.
 unfold klvalence at 2.
 rewrite <- (map_length (prev_letter k) (kleftexts k u)).
 now apply klvalence_ok.
Qed.

Lemma lemma_3_7_ii_all k u l :
  last u 0 <> k ->
  AllLeftExts l u (kseq k) -> 2 <= length l ->
  exists v, apply (ksubst k) v = u /\
            AllLeftExts (map (prev_letter k) l) v (kseq k).
Proof.
 intros U (ND,A) L.
 destruct (list_eq_dec Nat.eq_dec u []).
 - subst. simpl in *. exists []. repeat split; trivial.
   + apply NoDup_map_inv with (f:=next_letter k).
     rewrite map_map, map_ext_in with (g:=id), map_id; auto.
     intros a Ha. apply next_prev_letter. rewrite A in Ha.
     now apply LeftExt_letter in Ha.
   + rewrite in_map_iff.
     intros (x & E & IN). rewrite A in IN. apply LeftExt_letter in IN.
     red. apply all_letters_subseq. subst a. now apply prev_letter_le.
   + rewrite in_map_iff. intros Ha. apply LeftExt_letter in Ha.
     exists (next_letter k a). split.
     * now apply prev_next_letter.
     * rewrite A. now apply all_letters_subseq, next_letter_le.
 - assert (hd 0 u <> 0).
   { destruct u as [|x u]; try easy.
     simpl. apply (ls_head_nz k x u).
     destruct l as [|a [|b l]]; simpl in L; try lia.
     exists a, b; repeat split.
     - inversion ND; simpl in *; intuition.
     - apply A; simpl; intuition.
     - apply A; simpl; intuition. }
   apply lemma_3_7_ii_all'; auto. 2:now red.
   destruct l as [|a l]; simpl in L; try lia.
   assert (SU : SubSeq (a::u) (kseq k)). { apply A. simpl; intuition. }
   eapply Sub_SubSeq; eauto using Sub_cons_r.
Qed.

Lemma lengthle2_carac {A}(a b:A) l :
  a<>b -> In a l -> In b l -> 2 <= length l.
Proof.
 destruct l as [|c [|d l]]; simpl; try easy; try lia.
 now intros ND [<-|[ ]] [<-|[ ]].
Qed.

Lemma ls_val k u : LeftSpecial u (kseq k) <-> 2 <= klvalence k u.
Proof.
 split.
 - intros (a & b & NE & Ha & Hb).
   unfold klvalence.
   assert (H := kleftexts_ok k u). destruct H as (_,H).
   rewrite <- H in Ha, Hb. eapply lengthle2_carac; eauto.
 - unfold klvalence.
   assert (H := kleftexts_ok k u). destruct H as (ND,H).
   destruct (kleftexts k u) as [|a [|b l]] eqn:E; simpl; try lia.
   intros _. exists a, b; repeat split.
   + inversion_clear ND; simpl in *; intuition.
   + apply H; simpl; intuition.
   + apply H; simpl; intuition.
Qed.

Lemma lemma_3_7_ii_val k u :
  last u 0 <> k -> 2 <= klvalence k u ->
  exists v, apply (ksubst k) v = u /\ klvalence k v = klvalence k u.
Proof.
 intros U L.
 destruct (lemma_3_7_ii_all k u (kleftexts k u) U) as (v & Hv & H);
  auto using kleftexts_ok.
 exists v; split; auto.
 unfold klvalence.
 rewrite <- (map_length (prev_letter k) (kleftexts k u)).
 now apply klvalence_ok.
Qed.

Lemma lemma_3_7_ii_ls k u :
  last u 0 <> k -> LeftSpecial u (kseq k) ->
  exists v, apply (ksubst k) v = u /\ LeftSpecial v (kseq k).
Proof.
 rewrite ls_val. intros U L.
 destruct (lemma_3_7_ii_val k u U L) as (v & V & E).
 exists v; split; auto. apply ls_val. lia.
Qed.


Lemma lemma_3_7_i_all_incl k u l l' :
  AllLeftExts l u (kseq k) ->
  AllLeftExts l' (apply (ksubst k) u) (kseq k) ->
  incl (map (next_letter k) l) l'.
Proof.
 intros (ND,A) (ND',A') a. rewrite in_map_iff. intros (x & <- & Hx).
 rewrite A in Hx. rewrite A'. now apply lemma_3_7_i.
Qed.

Lemma lemma_3_7_i_val_le k u :
  klvalence k u <= klvalence k (apply (ksubst k) u).
Proof.
 unfold klvalence.
 rewrite <- (map_length (next_letter k) (kleftexts k u)).
 apply NoDup_incl_length.
 - apply NoDup_map_inv with (f:=prev_letter k).
   rewrite map_map, map_ext_in with (g:=id), map_id; auto.
   apply kleftexts_ok.
   intros a Ha. apply prev_next_letter.
   assert (H := kleftexts_ok k u). destruct H as (_,H).
   rewrite H in Ha. now apply LeftExt_letter in Ha.
 - eapply lemma_3_7_i_all_incl; eauto using kleftexts_ok.
Qed.

(** Note: [k-1] has klvalence of 1 since it could only come after
    (prev_letter k (k-1)). But (apply (ksubst k) [k-1])=[k] has
    klvalence of (S k).
    Hence the klvalence is preserved by ksubst only when it is at least 2
    (i.e. for left-special words). *)

(* /!\ Problem with the last line of Lemma 3.7 : \tilde{p} = p cannot
   be obtained in general, since (ii) needs last letter to be different
   from k. Probably no big deal, since eventually the only LS words
   (the kprefix) have klvalence (S k), hence the same for their image
   by ksubst. But is this precise part of Lemma 3.7 reused in the rest
   of the article / corrigendum ??

Lemma lemma_3_7_i_all k u l :
  2 <= length l ->
  AllLeftExts l u (kseq k) ->
  AllLeftExts (map (next_letter k) l) (apply (ksubst k) u) (kseq k).
Proof.
 intros Hl (ND,A).
 split.
 - apply NoDup_map_inv with (f:=prev_letter k).
   rewrite map_map, map_ext_in with (g:=id), map_id; auto.
   intros a Ha. apply prev_next_letter. rewrite A in Ha.
   now apply LeftExt_letter in Ha.
 - destruct (Nat.eq_dec (length u) 0) as [L|L].
   { rewrite length_zero_iff_nil in L. subst u.
     simpl in *. unfold LeftExt in *.
     intros a. rewrite <- all_letters_subseq in *.
     rewrite in_map_iff. split.
     - intros (a' & <- & Ha'). rewrite A, <- all_letters_subseq in Ha'.
       now apply next_letter_le.
     - intros Ha. exists (prev_letter k a). split.
       + now apply next_prev_letter.
       + rewrite A. now apply all_letters_subseq, prev_letter_le. }
   destruct (Nat.eq_dec (length u) 1) as [L'|L'].
   { destruct u as [|x [|y l']]; simpl in L'; try lia. clear L L'.
     intros a.
     simpl. unfold ksubst.
     case Nat.eqb_spec; intros X; subst; simpl.
     - rewrite in_map_iff. split.
       + intros (a' & <- & Ha'). unfold letter.
         replace [k;0] with (kprefix k 2).
         2:{ rewrite kprefix_alt. unfold take. simpl.
             now rewrite kseq_k_0, kseq_k_1. }
         apply kprefix_leftext, next_letter_le.
         apply A in Ha'. now apply LeftExt_letter in Ha'.
       + intros Ha. apply LeftExt_letter in Ha.
         exists (prev_letter k a). split. now apply next_prev_letter.
         apply A. unfold letter.
         replace [k] with (kprefix k 1).
         2:{ rewrite kprefix_alt. unfold take. simpl.
             now rewrite kseq_k_0. }
         now apply kprefix_leftext, prev_letter_le.
     - exfalso. clear a.
       assert (forall a, In a l -> a = prev_letter k x).
       { intros a. rewrite A. clear A.
         unfold LeftExt, SubSeq, subseq. simpl.
         intros (p & [= E E']).
         replace p with (S p - 1) in E by lia.
         rewrite kseq_prev_letter in E by lia. now rewrite <- E' in E. }
       destruct l as [|a [|b l']]; simpl in Hl; try lia.
       assert (a = b).
       { rewrite (H a), (H b); simpl; intuition. }
       inversion_clear ND. simpl in *; intuition. }
   intro a. rewrite in_map_iff. split.
   + intros (a' & <- & IN). apply lemma_3_7_i. now apply A.
   + intros Ha. exists (prev_letter k a). split.
     apply next_prev_letter. eapply LeftExt_letter; eauto.
     rewrite A.
     set (v := apply (ksubst k) u) in *.
     assert (Hv : hd 0 v <> 0).
     { admit. }
     destruct (Nat.eq_dec (last v 0) k) as [Hv'|Hv'].
     * (* v <> [] --> removelast v exists *)
       (* last u 0 = k-1 *)
       (* last last u = k-2 *)
       (* last (removelast v) <> k *)
       (* ksubst (removelast v) = removelast u *)
       (* leftext a (removelast v)
          exist u', ksubst u' = removelast v et
          leftext a u'
          u' = removelast u

          Bref leftext a (removelast u)
          et ensuite ?? *)
        admit.

     * destruct (lemma_3_7_ii_aux k v a Hv Hv' Ha) as (u' & Hu' & Ha').
       replace u' with u in * by (now apply ksubst_inv in Hu').
       auto.
Admitted.
*)

Definition InfiniteLeftSpecial (f g : sequence) :=
 forall u, PrefixSeq u f -> LeftSpecial u g.

Lemma remark_3_6 k : k<>0 -> InfiniteLeftSpecial (kseq k) (kseq k).
Proof.
 intros Hk u Hu. red in Hu. rewrite <- kprefix_alt in Hu. rewrite Hu.
 rewrite ls_val. rewrite kprefix_klvalence. lia.
Qed.

Definition StrictPrefix {A} (u v : list A) := Prefix u v /\ u<>v.

Definition limword (f : nat -> word) : sequence :=
  fun (n:nat) => nth n (f (S n)) 0.

Lemma limword_ok (f : nat -> word) :
 (forall n, StrictPrefix (f n) (f (S n))) ->
 forall n, PrefixSeq (f n) (limword f).
Proof.
 intros P n. red. symmetry. apply take_carac; trivial.
 intros m a H. rewrite nth_indep with (d':=0) by trivial.
 unfold limword.
 assert (L : forall n, n <= length (f n)).
 { clear - P. induction n; try lia.
   apply Nat.le_lt_trans with (length (f n)); try lia.
   destruct (P n) as ((u,<-),NE). rewrite app_length.
   destruct u. now rewrite app_nil_r in NE. simpl; lia. }
 assert (P' : forall p q , p <= q -> Prefix (f p) (f q)).
 { induction 1. apply Prefix_id. eapply Prefix_trans; eauto. apply P. }
 destruct (Nat.le_ge_cases n (S m)) as [LE|GE].
 - apply P' in LE. rewrite Prefix_nth in LE. now apply LE.
 - apply P' in GE. rewrite Prefix_nth in GE. symmetry. apply GE. apply L.
Qed.

Lemma limword_unique (f : nat -> word) (g : sequence) :
 (forall n, StrictPrefix (f n) (f (S n))) ->
 (forall n, PrefixSeq (f n) g) ->
 forall n, g n = limword f n.
Proof.
 intros P PR n.
 assert (L : forall n, n <= length (f n)).
 { clear - P. induction n; try lia.
   apply Nat.le_lt_trans with (length (f n)); try lia.
   destruct (P n) as ((u,<-),NE). rewrite app_length.
   destruct u. now rewrite app_nil_r in NE. simpl; lia. }
 specialize (PR (S n)).
 assert (PR' := limword_ok f P (S n)).
 unfold PrefixSeq in *.
 rewrite <- (take_nth g (length (f (S n))) n 0) by apply L.
 rewrite <- PR, PR'. apply take_nth. apply L.
Qed.

Lemma infinitly_many_0_letters k :
 forall n, { m | n <= m /\ kseq k m = 0 }.
Proof.
 intros n.
 destruct (Nat.eq_dec k 0) as [->|K].
 - exists n. split; trivial. generalize (kseq_letters 0 n). lia.
 - set (p := invA_up k n).
   exists (S (Nat.max (k+2) (A k p))). split.
   + generalize (invA_up_spec k n). unfold p. lia.
   + apply Nat.max_case_strong; intros LE.
     * rewrite kseq_bounded_rank. unfold bounded_rank, rank.
       rewrite decomp_S.
       replace (decomp k (k+2)) with [S k].
       2:{ symmetry. apply decomp_carac.
           - constructor.
           - replace (k+2) with (S (S k)) by lia.
             rewrite <- (@A_base k (S k)) by lia. simpl; lia. }
       unfold next_decomp. case Nat.leb_spec; simpl; lia.
     * rewrite kseq_bounded_rank. unfold bounded_rank, rank.
       replace (decomp k (S (A k p))) with [0;p]; trivial.
       symmetry. apply decomp_carac; simpl; try lia.
       constructor. 2:constructor. simpl. apply (A_le_inv k).
       rewrite A_base; lia.
Qed.
(*
Fixpoint nonk k n :=
 match n with
 | 0 => proj1_sig (infinitly_many_0_letters k 0)
 | S n => proj1_sig (infinitly_many_0_letters k (S (nonk k n)))
 end.

Lemma nonk_ok k n : kseq k (nonk k n) = 0.
Proof.
 destruct n; simpl; destruct infinitly_many_0_letters; simpl; intuition.
Qed.

Lemma nonk_incr k n : nonk k n < nonk k (S n).
Proof.
 simpl. destruct infinitly_many_0_letters; simpl; intuition.
Qed.
*)

Lemma proposition_3_8 k f :
  InfiniteLeftSpecial f (kseq k) ->
  exists g, InfiniteLeftSpecial g (kseq k) /\ SubstSeqSeq (ksubst k) f g.
Proof.
(*
 set (h := fun n => take (S (nonk k n)) f).
 assert (forall n, last (h n) 0 <> k).
 { intros n. unfold h. rewrite take_S. KO }
 assert (forall n, LeftSpecial (h n) (kseq k)).
*)

(* toujours un non-k un peu plus loin.
   soit u_i ce prefix de f ne finissant pas par k et de taille >= i,
   donc exists v_i, s(v_i) = u_i et LS v_i.

   Or les u_i sont strictement imbriqués 2 à 2.
   Idem pour les v_i, donc on a une limite


 *)

(* repeated use of:
Lemma lemma_3_7_ii_ls k u :
  last u 0 <> k -> LeftSpecial u (kseq k) ->
  exists v, apply (ksubst k) v = u /\ LeftSpecial v (kseq k).
*)

(* Suite infini de mots finis strictement imbriqués --> un mot infini
   dont les autres sont des prefix *)

Admitted.

Lemma theorem_3_9 k f :
  InfiniteLeftSpecial f (kseq k) -> forall n, f n = kseq k n.
Proof.
Admitted.

Definition MaxLeftSpecial u (f:sequence) :=
  LeftSpecial u f /\ forall a, ~LeftSpecial (u++[a]) f.

Lemma observation_4_2_contra u f : MaxLeftSpecial u f -> RightSpecial u f.
Proof.
 intros ((a & b & AB & A & B),H).
 destruct (SubSeq_RightExt (a::u) f A) as (c & C).
 destruct (SubSeq_RightExt (b::u) f B) as (d & D).
 destruct (Nat.eq_dec c d).
 - subst d. destruct (H c). exists a, b. repeat split; auto.
 - exists c, d; repeat split; auto.
   + eapply RightExt_Suffix; eauto. now exists [a].
   + eapply RightExt_Suffix; eauto. now exists [b].
Qed.

Lemma observation_4_2 u f :
  LeftSpecial u f -> ~RightSpecial u f -> ~MaxLeftSpecial u f.
Proof.
 intros H H'. contradict H'. now apply observation_4_2_contra.
Qed.

Lemma lemma_4_4 k n a : n<>0 ->
  last (kword k n) 0 = a -> Suffix [prev_letter k a; a] (kword k n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 intros Hn Ha. destruct (Nat.le_gt_cases n (S k)).
 - clear IH. rewrite kword_low in * by lia.
   destruct n as [|[|n]]; try easy.
   + simpl in *. subst a. now exists [].
   + rewrite seq_S in Ha. simpl "+" in Ha.
     change (k::_++[S n]) with ((k::seq 0 (S n))++[S n]) in Ha.
     rewrite last_last in Ha. subst a.
     rewrite !seq_S. exists (k::seq 0 n). simpl. f_equal.
     now rewrite <- app_assoc.
 - destruct n; try easy. rewrite kword_alt in * by lia.
   rewrite last_app in Ha.
   2:{ apply kword_nz. }
   destruct (IH (n-k)) as (u & <-); trivial; try lia.
   exists (kword k n ++ u). now rewrite app_assoc.
Qed.

Lemma Sub_app {A} (u1 u2 v1 v2 : list A) :
  Suffix u1 v1 -> Prefix u2 v2 -> Sub (u1++u2) (v1++v2).
Proof.
 intros (u0, <-) (u3, <-). exists u0, u3. now rewrite !app_assoc.
Qed.

Lemma Suffix_last {A} (l:list A) (a:A) : l<>[] -> Suffix [last l a] l.
Proof.
 exists (removelast l). symmetry. now apply app_removelast_last.
Qed.

Lemma lemma_4_5 k r a b : a<>k -> b<>k ->
  SubSeq ([a] ++ repeat k r ++ [b]) (kseq k) <->
  (r=0 /\ a = b-1 /\ 0 < b < k) \/
  (r=1 /\ a < k /\ b = 0) \/
  (r=2 /\ a = k-1 /\ b = 0).
Proof.
 intros A B. split.
 - rewrite SubSeq_kseq_Sub_kword. intros (n,SU). revert SU.
   induction n as [n IH] using lt_wf_ind.
   destruct (Nat.le_gt_cases n k) as [LE|GT].
   + clear IH. rewrite kword_low by lia. intros (u & v & E). left.
     rewrite <- !app_assoc in E.
     destruct u; simpl in E; injection E as -> E; try easy.
     assert (length u < n).
     { rewrite <- (seq_length n 0). rewrite <- E. rewrite app_length.
       simpl. lia. }
     replace n with (length u + (n-length u)) in E by lia.
     rewrite seq_app in E.
     apply app_inv in E. destruct E as (_,E).
     2:{ now rewrite seq_length. }
     destruct (n-length u) as [|n'] eqn:N'; try lia.
     simpl in E. injection E as E1 E2.
     destruct r; destruct n'; simpl in E2; try easy;
      injection E2 as E2 _; lia.
   + destruct n; try easy.
     rewrite kword_alt by lia. intros SU. apply Sub_app_inv in SU.
     destruct SU as [SU|[SU|(u1 & u2 & U1 & U2 & E & SU & PR)]].
     * apply (IH n); auto.
     * apply (IH (n-k)); auto. lia.
     * clear IH. right.
       destruct u1 as [|x1 u1]; try easy. clear U1. simpl in E.
       injection E as <- E.
       rewrite <- (rev_involutive u2) in *.
       destruct (rev u2) as [|x2 u2']; try easy. clear U2. simpl in *.
       clear u2.
       rewrite app_assoc in E.
       apply app_inv' in E; trivial. destruct E as (E & [= <-]).
       destruct (Nat.eq_dec n k) as [->|N].
       { rewrite Nat.sub_diag, kword_0 in PR.
         destruct PR as (u2, PR).
         assert (L := f_equal (@length nat) PR).
         rewrite !app_length, rev_length in L. simpl in L.
         assert (length u2' = 0) by lia.
         rewrite length_zero_iff_nil in *. subst u2'.
         simpl in PR. now injection PR as -> ->. }
       { assert (PR' : 1 <= n-k) by lia.
         apply (kword_le_prefix k) in PR'. rewrite kword_1 in PR'.
         destruct (rev u2') as [|x [|y u2]]; simpl in PR.
         - assert (PR2 : Prefix [b] [k;0]).
           { eapply Prefix_Prefix; simpl; eauto. }
           now destruct PR2 as (v & [= -> _]).
         - clear u2'. destruct PR as (v & PR).
           destruct PR' as (v' & PR').
           rewrite <- PR' in PR. apply app_inv in PR; auto.
           destruct PR as ([= -> ->],_). clear PR'.
           destruct r as [|r]; [now destruct u1| ].
           rewrite <- Nat.add_1_r, repeat_app in E. simpl in E.
           apply app_inv' in E; auto. destruct E as (<-,_). clear v v'.
           destruct r as [|[|r]].
           + left; repeat split; auto.
             simpl in SU. destruct SU as (w & SU).
             generalize (kword_letters k n). rewrite <- SU, Forall_app.
             intros (_,F). inversion_clear F. lia.
           + right; repeat split; auto.
             simpl in SU.
             destruct SU as (u & SU).
             assert (N' : n <> 0) by lia.
             assert (L : last (kword k n) 0 = k).
             { now rewrite <- SU, last_app. }
             assert (SU' := lemma_4_4 k n k N' L).
             destruct SU' as (u' & SU'). rewrite <- SU' in SU.
             apply app_inv' in SU; auto. destruct SU as (_,[= ->]).
             unfold prev_letter.
             case Nat.eqb_spec; lia.
           + exfalso.
             replace (S (S r)) with (r+2) in SU by lia.
             rewrite repeat_app in SU. simpl in SU.
             destruct SU as (u & SU).
             change (a::_ ++ _) with ((a::repeat k r)++[k;k]) in SU.
             rewrite app_assoc in SU.
             assert (N' : n <> 0) by lia.
             assert (L : last (kword k n) 0 = k).
             { now rewrite <- SU, last_app. }
             assert (SU' := lemma_4_4 k n k N' L).
             destruct SU' as (u' & SU'). rewrite <- SU' in SU.
             apply app_inv' in SU; auto. destruct SU as (_,[= E]).
             revert E. unfold prev_letter. case Nat.eqb_spec; lia.
         - exfalso.
           assert (IN : In a (kword k n)).
           { destruct SU as (u & <-). rewrite in_app_iff; right.
             simpl; intuition. }
           assert (LT : a < k).
           { generalize (kword_letters k n). rewrite Forall_forall.
             intros F. specialize (F a IN). lia. }
           clear IN.
           assert (PR2 : Prefix [k;0] (x::y::u2++[b])).
           { eapply Prefix_Prefix; simpl; eauto; try lia. }
           destruct PR2 as (u & [= <- <- PR2]).
           assert (IN : In 0 (repeat k r)).
           { rewrite E. rewrite in_app_iff. right. simpl; intuition. }
           apply repeat_spec in IN. lia. }
 - intros [(-> & -> & B')|[(-> & A' & ->)|(-> & -> & ->)]].
   + simpl. exists b. unfold subseq. simpl.
     assert (E : b = kseq k (S b)).
     { symmetry. apply all_letters_occur. lia. }
     f_equal; [|now f_equal].
     symmetry. replace b with ((S b)-1) at 1 by lia.
     rewrite kseq_prev_letter by lia. rewrite <- E.
     unfold prev_letter. case Nat.eqb_spec; lia.
   + simpl. apply SubSeq_kseq_Sub_kword. exists (S (k+a+2)).
     rewrite kword_alt by lia.
     assert (E : last (kword k (k+a+2)) 0 = a).
     { rewrite kword_last. replace (k+a+2+k) with (a+2*(S k)) by lia.
       rewrite Nat.mod_add, Nat.mod_small; lia. }
     change [a;k;0] with ([a]++[k;0]).
     apply Sub_app.
     * rewrite <- E at 1. apply Suffix_last. apply kword_nz.
     * replace [k;0] with (kword k 1).
       2:{ rewrite kword_low; simpl; trivial; lia. }
       apply kword_le_prefix; lia.
   + simpl. apply SubSeq_kseq_Sub_kword. exists (S (k+1)).
     rewrite kword_alt by lia.
     assert (E : last (kword k (k+1)) 0 = k).
     { rewrite kword_last. replace (k+1+k) with (k+1*(S k)) by lia.
       rewrite Nat.mod_add, Nat.mod_small; lia. }
     change [k-1;k;k;0] with ([k-1;k]++[k;0]).
     apply Sub_app.
     * replace (k-1) with (prev_letter k k).
       apply lemma_4_4; try lia.
       unfold prev_letter. case Nat.eqb_spec; lia.
     * replace [k;0] with (kword k 1).
       2:{ rewrite kword_low; simpl; trivial; lia. }
       apply kword_le_prefix; lia.
Qed.

Lemma lemma_4_5_bis k r a :
  k<>0 -> a<>k -> SubSeq ([a] ++ repeat k r) (kseq k) -> r <= 2.
Proof.
 intros K A (q,E).
 rewrite app_length, repeat_length in E. simpl in E.
 destruct (infinitly_many_0_letters k (q+S r)) as (n,(N,N')).
 remember (n-(q+S r)) as m eqn:M.
 revert r E N N' M.
 induction m; intros.
 - replace n with (q+S r) in N' by lia.
   assert (SU : SubSeq ([a] ++ repeat k r ++ [0]) (kseq k)).
   { exists q. rewrite !app_length, repeat_length, Nat.add_1_r. simpl.
     unfold subseq in *. now rewrite seq_S, map_app, <- E, <- N'. }
   apply lemma_4_5 in SU; trivial; lia.
 - destruct (Nat.eq_dec (kseq k (q+S r)) k) as [E'|E'].
   + assert (S r <= 2); try lia.
     apply IHm; try lia. clear IHm.
     rewrite <- (Nat.add_1_r r), repeat_app at 1. simpl.
     unfold subseq in *. rewrite seq_S, map_app, <- E. simpl.
     now repeat f_equal.
   + set (b := kseq k (q+S r)) in *.
     assert (SU : SubSeq ([a] ++ repeat k r ++ [b]) (kseq k)).
     { exists q. rewrite !app_length, repeat_length, Nat.add_1_r. simpl.
       unfold subseq in *. now rewrite seq_S, map_app, <- E. }
     apply lemma_4_5 in SU; trivial; lia.
Qed.

Lemma lemma_4_5_ter k r : k<>0 -> SubSeq (repeat k r) (kseq k) -> r <= 2.
Proof.
 intros K (q,E). rewrite repeat_length in E. revert r E.
 induction q; intros.
 - unfold subseq in E. destruct r as [|[|r]]; try lia.
   simpl in E. rewrite kseq_k_1 in E. now injection E as [= E _].
 - destruct (Nat.eq_dec (kseq k q) k) as [E'|E'].
   + assert (S r <= 2); try lia.
     { apply IHq. unfold subseq in *. simpl. now rewrite E', E. }
   + eapply lemma_4_5_bis; eauto. exists q.
     rewrite app_length, repeat_length. simpl. now rewrite E.
Qed.

Lemma corollary_4_6_aux k r : k<>0 -> 2 <= r ->
  ~RightSpecial (repeat k r) (kseq k).
Proof.
 intros K R (b & c & BC & B & C).
 assert (SU : SubSeq (repeat k r) (kseq k)).
 { red in B. eapply Sub_SubSeq; eauto. apply Sub_app_r, Sub_id. }
 apply lemma_4_5_ter in SU; trivial. replace r with 2 in * by lia. clear R SU.
 assert (H : forall b, RightExt [k;k] b (kseq k) -> b = 0).
 { clear b c BC B C. intros b B.
   destruct (Nat.eq_dec b k) as [->|B'].
   { apply (lemma_4_5_ter k 3) in B; lia. }
   destruct B as (p,B).
   destruct (Nat.eq_dec p 0) as [->|P].
   { unfold subseq in B. simpl in B. rewrite kseq_k_1 in B. injection B. lia. }
   set (a := kseq k (p-1)).
   assert (SU' : SubSeq ([a]++repeat k 2++[b]) (kseq k)).
   { exists (p-1). simpl. unfold subseq in *. simpl in *. unfold a; f_equal.
     replace (S (p-1)) with p by lia. trivial. }
   assert (A : a <> k).
   { intros ->.
     assert (SU3 : SubSeq [k;k;k] (kseq k)).
     { eapply Sub_SubSeq; eauto. rewrite app_assoc. apply Sub_app_r, Sub_id. }
     apply (lemma_4_5_ter k 3) in SU3; lia. }
   apply lemma_4_5 in SU'; lia. }
 apply H in B, C. lia.
Qed.

Lemma LeftSpecial_Prefix f u v :
  Prefix u v -> LeftSpecial v f -> LeftSpecial u f.
Proof.
 intros P (a & b & AB & B & C).
 exists a, b; repeat split; eauto using LeftExt_Prefix.
Qed.

Lemma RightSpecial_Suffix f u v :
  Suffix u v -> RightSpecial v f -> RightSpecial u f.
Proof.
 intros P (a & b & AB & B & C).
 exists a, b; repeat split; eauto using RightExt_Suffix.
Qed.

Lemma corollary_4_6 k u r : k<>0 -> 2 <= r ->
  ~RightSpecial (u++repeat k r) (kseq k).
Proof.
 intros K R RS. apply (corollary_4_6_aux k r K R).
 eapply RightSpecial_Suffix; eauto. now exists u.
Qed.

Lemma lemma_4_7 k r : ~MaxLeftSpecial (repeat k r) (kseq k).
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { intros ((a & b & AB & A & B),_). apply LeftExt_letter in A, B. lia. }
 intros (LS,NLS).
 assert (SU : SubSeq (repeat k r) (kseq k)).
 { destruct LS as (a & b & AB & A & B).
   red in A. eapply Sub_SubSeq; eauto using Sub_cons_r. }
 apply lemma_4_5_ter in SU; auto.
 destruct r as [|[|r]]; simpl in *.
 - apply (NLS k). apply ls_val. rewrite klvalence_letter_k. lia.
 - apply (NLS 0). apply ls_val.
   assert (E : [k;0] = kprefix k 2).
   { rewrite kprefix_alt. unfold take. simpl. now rewrite kseq_k_1. }
   unfold letter in *; rewrite E, kprefix_klvalence. lia.
 - replace r with 0 in * by lia. simpl in *. clear NLS SU.
   destruct LS as (a & b & AB & A & B).
   destruct (Nat.eq_dec a k) as [->|A'].
   { unfold LeftExt in A. apply (lemma_4_5_ter k 3) in A; lia. }
   destruct (SubSeq_RightExt _ _ A) as (c & AR).
   destruct (Nat.eq_dec c k) as [->|C].
   { apply (lemma_4_5_bis k 3 a) in AR; trivial; lia. }
   apply (lemma_4_5 k 2 a c) in AR; trivial.
   destruct (Nat.eq_dec b k) as [->|B'].
   { unfold LeftExt in B. apply (lemma_4_5_ter k 3) in B; lia. }
   destruct (SubSeq_RightExt _ _ B) as (d & BR).
   destruct (Nat.eq_dec d k) as [->|D].
   { apply (lemma_4_5_bis k 3 b) in BR; trivial; lia. }
   apply (lemma_4_5 k 2 b d) in BR; trivial.
   lia.
Qed.

(*
Lemma lemma_4_8 k u :
  LeftSpecial u (kseq k) -> ~PrefixSeq u (kseq k) -> klvalence k u = 2.
Proof.
Admitted.
*)

Lemma lemma_4_9 k u a :
  SubSeq u (kseq k) -> Suffix [k-1;a] u -> a = k.
Proof.
 intros SU SU'.
 assert (R : RightExt [k-1] a (kseq k)).
 { red. eapply Sub_SubSeq; eauto using Suffix_Sub. }
 apply letters_RightExt in R. destruct R as [R|R]; trivial.
 revert R. unfold next_letter. case Nat.eqb_spec; try lia.
Qed.

Fixpoint factorhead a u :=
  match u with
  | [] => (0,[])
  | x::u => if x =? a then let (n,u') := factorhead a u in (S n,u')
            else (0,x::u)
  end.

Lemma factorhead_ok a u :
  let (n,u') := factorhead a u in u = repeat a n ++ u'.
Proof.
 induction u; simpl; auto.
 destruct factorhead as (n,u').
 case Nat.eqb_spec; simpl; intros; auto. subst; auto.
Qed.

Lemma factorhead_max a u : hd_error (snd (factorhead a u)) <> Some a.
Proof.
 induction u; simpl; try easy.
 destruct factorhead as (n,u'). simpl in *.
 case Nat.eqb_spec; simpl; intros; auto. now intros [= ->].
Qed.

Lemma rev_repeat {A} (a:A) n : rev (repeat a n) = repeat a n.
Proof.
 induction n; trivial.
 rewrite <- Nat.add_1_r at 1. rewrite repeat_app, rev_app_distr.
 simpl. now f_equal.
Qed.

Lemma lemma_4_10 k u a :
  MaxLeftSpecial u (kseq k) -> a<>k -> In a u ->
  exists v w, MaxLeftSpecial v (kseq k) /\ (w=[]\/w=[k]) /\
              u = apply (ksubst k) v ++ w.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { intros ((b & c & BC & B & C),_). apply LeftExt_letter in B, C. lia. }
 intros (LS,NLS) A IN.
 destruct (factorhead k (rev u)) as (r,u0) eqn:E.
 assert (E' := factorhead_ok k (rev u)).
 assert (F := factorhead_max k (rev u)).
 rewrite E in *. simpl in *.
 rewrite <- (rev_involutive (_++_)) in E'. apply rev_inj in E'.
 rewrite rev_app_distr, rev_repeat in E'.
 assert (U' : In a (rev u0)).
 { rewrite <- in_rev.
   rewrite E', in_app_iff, <- in_rev in IN. destruct IN as [IN|IN]; trivial.
   apply repeat_spec in IN; lia. }
 assert (L : last (rev u0) 0 <> k).
 { destruct u0 as [|x u']; simpl in *; try easy.
   rewrite last_last. contradict F. now subst. }
 clear F. set (u' := rev u0) in *. clearbody u'. clear u0 E a A IN U'.
 assert (R : r <= 2).
 { apply (lemma_4_5_ter k); trivial.
   rewrite E' in LS. destruct LS as (b & _ & _ & B & _).
   red in B. eapply Sub_SubSeq; eauto. apply (Sub_app_l (b::u')), Sub_id. }
 assert (R2 : r <> 2).
 { intros R'. apply (corollary_4_6 k u' r); try lia. rewrite <- E'.
   apply observation_4_2_contra; split; trivial. }
 assert (R' : r = 0 \/ r = 1) by lia. clear R R2.
 assert (LS' : LeftSpecial u' (kseq k)).
 { eapply LeftSpecial_Prefix; eauto. now exists (repeat k r). }
 destruct (lemma_3_7_ii_ls k u' L LS') as (v' & V1 & V2).
 exists v', (repeat k r). split.
 2:{ rewrite V1; split; trivial.
     destruct R' as [-> | ->]; [now left|now right]. }
 (* Maximality *)
 split; trivial.
 intros a A. assert (LS2 := lemma_3_7_i_ls _ _ A).
 rewrite apply_app, V1 in LS2.
 assert (a <> k).
 { intros ->. simpl in LS2. unfold ksubst in LS2.
   rewrite Nat.eqb_refl, app_nil_r in LS2.
   destruct R' as [-> | ->]; simpl in E'.
   - rewrite app_nil_r in E'. rewrite <- E' in *.
     apply (NLS k). eapply LeftSpecial_Prefix; [|exact LS2].
     exists [0]; now rewrite <- app_assoc.
   - change [k;0] with ([k]++[0]) in LS2. rewrite app_assoc, <- E' in LS2.
     now apply (NLS 0). }
 assert (RS: RightSpecial u (kseq k)).
 { apply observation_4_2_contra; split; trivial. }
 destruct RS as (b & c & BC & B & C). red in B,C.
 assert (B' := NLS b).
 assert (C' := NLS c).

(*
 SI r=1 :

   SI b<>k alors b=0 et u'++[k;0] a un antécédent
                     donc v'++k facteur, k RightExt de v'
   SI b=k alors u'++[k;k;0] facteur et a un antécédent
          donc v'++[k-1;k] facteur donc (k-1) RightExt de v'

   Idem pour c et on ne peut donc pas avoir b=c=k ou b=c=0 en même temps
   Donc deux RightExt de v' : (k-1) et k

   et ~LeftSpecial (v'++[k]) sinon u'++[k;0] LS
      ~LeftSpecial (v'++[k-1;k]) sinon u'++[k;k;0] LS et donc aussi u'++[k;k].

   BUG ?? Rien ne garantit a<>k-1 en effet on peut avoir LS (v'++[k-1]) ...

 SI r=0 :

     SI b<>k alors b<>0 et u'++[b] a un antécédent et (b-1) RightExt de v'
     SI b=k alors u'++[k;0] ou u'++[k;k;0] facteur
       donc l'un ou l'autre ont antécédent
       et donc k ou (k-1) RightExt de v'

     Idem pour c et on ne peut pas avoir b=c=k donc un seulement est k
     ou aucun (et alors b-1<>c-1). Bref, deux RightExt <> de v'.

     ~LeftSpecial (v'++[b-1]) sinon u'++[b] LS
     a<>k déjà obtenu. Et ici a<>k-1 aussi dans ce cas.
     (car ~LS (u+[k]) donc aussi ~LS (v'++[k-1]) or LS(v'++[a]))


lemma_3_7_ii_cor:
  forall (k : nat) (u : list nat),
  hd 0 u <> 0 ->
  last u 0 <> k ->
  SubSeq u (kseq k) ->
  exists v : word, apply (ksubst k) v = u /\ SubSeq v (kseq k)


*)
Admitted.


Lemma corollary_4_11 k u : ~MaxLeftSpecial u (kseq k).
Proof.
Admitted.

Lemma LS_carac k u : LeftSpecial u (kseq k) <-> u = kprefix k (length u).
Proof.
Admitted.

(* on a besoin de parler de l'unicité des InfiniteLeftSpecial

   pas de MaxLeftSpecial signifie que tout LS est un prefix d'un ILS *)




(* TODO: formule sur l'evolution du nombre de facteurs
   en fonction de la valence des left-special.
*)
