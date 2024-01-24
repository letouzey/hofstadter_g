Require Import MoreFun MoreList DeltaList GenFib GenG Words WordFactor.
Import ListNotations.

(** * Study of Left-Special words of [kseq k] *)

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

Lemma LeftSpecial_Prefix u v f :
  Prefix u v -> LeftSpecial v f -> LeftSpecial u f.
Proof.
 intros P (a & b & AB & A & B).
 exists a, b; repeat split; eauto using LeftExt_Prefix.
Qed.

Lemma RightSpecial_Suffix u v f :
  Suffix u v -> RightSpecial v f -> RightSpecial u f.
Proof.
 intros P (a & b & AB & A & B).
 exists a, b; repeat split; eauto using RightExt_Suffix.
Qed.

Lemma LeftSpecial_SubSeq u f : LeftSpecial u f -> SubSeq u f.
Proof.
 intros (a & _ & _ & A & _). eapply Sub_SubSeq; eauto. apply Sub_cons_r.
Qed.

Lemma RightSpecial_SubSeq u f : RightSpecial u f -> SubSeq u f.
Proof.
 intros (a & _ & _ & A & _). eapply Sub_SubSeq; eauto.
 apply Sub_app_r, Sub_id.
Qed.

(** Computing the left and right extensions, thanks to kfactors
    (not meant to be efficient).
    The number of extensions is named the (left and right) valence
    of the factor. *)

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
   { rewrite SubSeq_kseq_alt. exists (q+2+S k). apply Sub_id. }
   rewrite Nat.add_succ_r, kword_eqn in SU by lia.
   replace (q+2+k-k) with (q+2) in SU by lia.
   rewrite (@app_removelast_last _ (kword k (q+2+k)) 0) in SU.
   2:{ apply kword_nz. }
   rewrite <- app_assoc in SU.
   rewrite WordSuffix.kword_last in SU.
   replace (q+2+k+k) with (q+2*(S k)) in SU by lia.
   rewrite Nat.mod_add, E in SU by lia.
   red. eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id.
Qed.

Lemma kprefix_leftext k n a : a <= k -> LeftExt a (kprefix k n) (kseq k).
Proof.
 intros Ha.
 rewrite kprefix_alt.
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
 rewrite SubSeq_kseq_alt; intros (n, (v & w & E)).
 rewrite <- (rev_involutive v) in E.
 destruct (rev v) as [|a v']; simpl in E.
 - exists 0. replace u with (kprefix k (length u)).
   + apply kprefix_leftext; lia.
   + symmetry. change (PrefixSeq u (kseq k)).
     eapply Prefix_PrefixSeq.
     * now exists w.
     * rewrite E. apply kword_prefixseq.
 - exists a. red. rewrite SubSeq_kseq_alt. exists n.
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

Lemma ls_val k u : LeftSpecial u (kseq k) <-> 2 <= klvalence k u.
Proof.
 split.
 - intros (a & b & NE & Ha & Hb).
   unfold klvalence.
   assert (H := kleftexts_ok k u). destruct H as (_,H).
   rewrite <- H in Ha, Hb. eapply lengthge2_carac; eauto.
 - unfold klvalence.
   assert (H := kleftexts_ok k u). destruct H as (ND,H).
   destruct (kleftexts k u) as [|a [|b l]] eqn:E; simpl; try lia.
   intros _. exists a, b; repeat split.
   + inversion_clear ND; simpl in *; intuition.
   + apply H; simpl; intuition.
   + apply H; simpl; intuition.
Qed.

Lemma rs_val k u : RightSpecial u (kseq k) <-> 2 <= krvalence k u.
Proof.
 split.
 - intros (a & b & NE & Ha & Hb).
   unfold krvalence.
   assert (H := krightexts_ok k u). destruct H as (_,H).
   rewrite <- H in Ha, Hb. eapply lengthge2_carac; eauto.
 - unfold krvalence.
   assert (H := krightexts_ok k u). destruct H as (ND,H).
   destruct (krightexts k u) as [|a [|b l]] eqn:E; simpl; try lia.
   intros _. exists a, b; repeat split.
   + inversion_clear ND; simpl in *; intuition.
   + apply H; simpl; intuition.
   + apply H; simpl; intuition.
Qed.

(** Letters, what's before, what's after, their valence, etc *)

Definition next_letter k a := if a =? k then 0 else S a.
Definition prev_letter k a := if a =? 0 then k else pred a.

Lemma next_letter_le k a : a <= k -> next_letter k a <= k.
Proof.
 intros Ha. unfold next_letter. case Nat.eqb_spec; lia.
Qed.

Lemma next_letter_k k : next_letter k k = 0.
Proof.
 unfold next_letter. now rewrite Nat.eqb_refl.
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
 - intros ->. apply next_letter_k.
 - intros. unfold next_letter. case Nat.eqb_spec; lia.
Qed.

Lemma prev_next_letter k a : a <= k -> prev_letter k (next_letter k a) = a.
Proof.
 intros Ha. unfold next_letter.
 case Nat.eqb_spec; trivial.
 intros ->. unfold prev_letter. now rewrite Nat.eqb_refl.
Qed.

Lemma ksubst_k k : ksubst k k = [k;0].
Proof.
 unfold ksubst. now rewrite Nat.eqb_refl.
Qed.

Lemma ksubst_km1 k : k<>0 -> ksubst k (k-1) = [k].
Proof.
 intros K. unfold ksubst. case Nat.eqb_spec; intros. lia. f_equal. lia.
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
 change [k] with (kprefix k 1). apply kprefix_klvalence.
Qed.

Lemma krvalence_letter_le k a : krvalence k [a] <= 2.
Proof.
 unfold krvalence. change 2 with (length [next_letter k a; k]).
 apply NoDup_incl_length. apply krightexts_ok.
 apply letters_AllRightExts_incl. apply krightexts_ok.
Qed.

(** We'll prove later that actually all letters have krvalence of 2
    except (k-1) whose krvalence is 1 (see krvalence_km1). *)

Lemma krvalence_le_2 k u : u<>[] -> krvalence k u <= 2.
Proof.
 intros Hu. transitivity (krvalence k [last u 0]).
 - apply suffix_krvalence.
   exists (removelast u). symmetry. now apply app_removelast_last.
 - apply krvalence_letter_le.
Qed.


(** Lemmas from the article by Frougny et al. *)

Lemma lemma_3_7_i k u a :
  LeftExt a u (kseq k) ->
  LeftExt (next_letter k a) (ksubstw k u) (kseq k).
Proof.
 intros Ha. assert (Ha' := LeftExt_letter _ _ _ Ha).
 unfold LeftExt in *. rewrite SubSeq_kseq_alt in *.
 destruct Ha as (n, (v & w & E)). exists (S n).
 rewrite kword_S, <- E, !ksubstw_app. cbn. clear E.
 unfold ksubst, next_letter.
 case Nat.eqb_spec; intros.
 - subst. exists (ksubstw k v ++ [k]), (ksubstw k w).
   now rewrite <- !app_assoc.
 - now exists (ksubstw k v), (ksubstw k w).
Qed.

Lemma lemma_3_7_i_ls k u :
  LeftSpecial u (kseq k) ->
  LeftSpecial (ksubstw k u) (kseq k).
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
  length (ksubstw k u) <= length (ksubstw k v) ->
  Prefix u v.
Proof.
 intros U V L.
 destruct (Nat.le_gt_cases (length u) (length v)).
 - eapply PrefixSeq_incl; eauto.
 - assert (P : Prefix v u) by (eapply PrefixSeq_incl; eauto; lia).
   destruct P as (w & <-).
   rewrite ksubstw_app, app_length in L.
   assert (L' : length (ksubstw k w) = 0) by lia.
   apply length_zero_iff_nil in L'.
   apply (ksubstw_inv k w []) in L'. subst w. rewrite app_nil_r.
   apply Prefix_id.
Qed.

Lemma lemma_3_7_ii_aux k u a :
  hd 0 u <> 0 -> last u 0 <> k ->
  LeftExt a u (kseq k) ->
  exists v, ksubstw k v = u /\
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
     * rewrite <- PR in E'. rewrite ksubstw_app, <- E, <- E1 in E'.
       change (a::u) with ([a]++u) in E'. rewrite app_assoc in E'.
       now apply app_inv_head in E'.
     * rewrite <- (rev_involutive u1') in *.
       destruct (rev u1') as [|a' u2']; simpl in E1.
       { now destruct u1. }
       { rewrite SubSeq_alt0. exists w'. split; trivial.
         exists (rev u2'). simpl in PR. rewrite <- app_assoc in PR.
         replace (prev_letter k a) with a'; trivial.
         revert E1. rewrite ksubstw_app. simpl. rewrite app_nil_r.
         unfold ksubst.
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
       simpl in E. subst. lia. }
     rewrite <- PR in E'. rewrite E1, E' in E.
     rewrite ksubstw_app in E. apply app_inv_head in E. simpl in E.
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

Lemma lemma_3_7_ii_cor k u : hd 0 u <> 0 -> last u 0 <> k ->
  SubSeq u (kseq k) ->
  exists v : word, ksubstw k v = u /\ SubSeq v (kseq k).
Proof.
 intros U U' SU. destruct (kseq_leftext _ _ SU) as (a & LE).
 destruct (lemma_3_7_ii_aux k u a U U' LE) as (v & V & V').
 exists v. split; trivial. eapply Sub_SubSeq; eauto using Sub_cons_r.
Qed.

Lemma lemma_3_7_ii_all' k u l :
  SubSeq u (kseq k) -> hd 0 u <> 0 -> last u 0 <> k ->
  AllLeftExts l u (kseq k) ->
  exists v, ksubstw k v = u /\
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
     { apply (ksubstw_inv k). now rewrite Hv, Hv'. }
   * intros Hc. exists (next_letter k c). split.
     { apply prev_next_letter. eapply LeftExt_letter; eauto. }
     rewrite A, <- Hv. now apply lemma_3_7_i.
Qed.

Lemma lemma_3_7_ii_val' k u :
  SubSeq u (kseq k) -> hd 0 u <> 0 -> last u 0 <> k ->
  exists v, ksubstw k v = u /\ klvalence k v = klvalence k u.
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
  exists v, ksubstw k v = u /\
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

Lemma lemma_3_7_ii_val k u :
  last u 0 <> k -> 2 <= klvalence k u ->
  exists v, ksubstw k v = u /\ klvalence k v = klvalence k u.
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
  exists v, ksubstw k v = u /\ LeftSpecial v (kseq k).
Proof.
 rewrite ls_val. intros U L.
 destruct (lemma_3_7_ii_val k u U L) as (v & V & E).
 exists v; split; auto. apply ls_val. lia.
Qed.

Lemma lemma_3_7_i_all_incl k u l l' :
  AllLeftExts l u (kseq k) ->
  AllLeftExts l' (ksubstw k u) (kseq k) ->
  incl (map (next_letter k) l) l'.
Proof.
 intros (ND,A) (ND',A') a. rewrite in_map_iff. intros (x & <- & Hx).
 rewrite A in Hx. rewrite A'. now apply lemma_3_7_i.
Qed.

Lemma lemma_3_7_i_val_le k u :
  klvalence k u <= klvalence k (ksubstw k u).
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
    (prev_letter k (k-1)). But (ksubstw k [k-1])=[k] has
    klvalence of (S k).
    Hence the klvalence is preserved by ksubst only when it is at least 2
    (i.e. for left-special words). *)

(* /!\ Problem with the last line of the proof of Lemma 3.7 :
   \tilde{p} = p cannot be obtained in general, since (ii) needs
   last letter to be different from k.
   No big issue, since eventually the only LeftSpecial words
   (the kprefix) have klvalence (S k), hence the same for their image
   by ksubst. And this precise part of Lemma 3.7 (i) doesn't seem
   to be used in the rest of the article / corrigendum. *)

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
 - destruct n; try easy. rewrite kword_eqn in * by lia.
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
 - rewrite SubSeq_kseq_alt. intros (n,SU). revert SU.
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
     rewrite kword_eqn by lia. intros SU. apply Sub_app_inv in SU.
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
         simpl in PR. now injection PR as -> _. }
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
             unfold prev_letter. case Nat.eqb_spec; lia.
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
   + simpl. apply SubSeq_kseq_alt. exists (S (k+a+2)).
     rewrite kword_eqn by lia.
     assert (E : last (kword k (k+a+2)) 0 = a).
     { rewrite WordSuffix.kword_last.
       replace (k+a+2+k) with (a+2*(S k)) by lia.
       rewrite Nat.mod_add, Nat.mod_small; lia. }
     change [a;k;0] with ([a]++[k;0]).
     apply Sub_app.
     * rewrite <- E at 1. apply Suffix_last. apply kword_nz.
     * replace [k;0] with (kword k 1).
       2:{ rewrite kword_low; simpl; trivial; lia. }
       apply kword_le_prefix; lia.
   + simpl. apply SubSeq_kseq_alt. exists (S (k+1)).
     rewrite kword_eqn by lia.
     assert (E : last (kword k (k+1)) 0 = k).
     { rewrite WordSuffix.kword_last.
       replace (k+1+k) with (k+1*(S k)) by lia.
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

Lemma lemma_4_5_kk k a b :
 SubSeq [a;k;k;b] (kseq k) -> a = k-1 /\ b = 0.
Proof.
 intros SU.
 destruct (Nat.eq_dec k 0) as [->|K].
 { simpl. destruct SU as (q & SU). unfold subseq in SU. simpl in SU.
   injection SU as E1 _ _ E2.
   generalize (kseq_letters 0 q) (kseq_letters 0 (S (S (S q)))). lia. }
 destruct (Nat.eq_dec a k) as [->|A].
 { exfalso.
   assert (SU' : SubSeq (repeat k 3) (kseq k)).
   { eapply Sub_SubSeq; eauto. now exists [], [b]. }
   apply lemma_4_5_ter in SU'; lia. }
 destruct (Nat.eq_dec b k) as [->|B].
 { exfalso.
   assert (SU' : SubSeq (repeat k 3) (kseq k)).
   { eapply Sub_SubSeq; eauto. now exists [a], []. }
   apply lemma_4_5_ter in SU'; lia. }
 rewrite (lemma_4_5 k 2 a b) in SU; lia.
Qed.

Lemma lemma_4_5_kk' k a : SubSeq [k;k;a] (kseq k) -> a = 0.
Proof.
 intros ([|q],SU).
 - unfold subseq in SU. simpl in SU. injection SU as E1 E2.
   rewrite kseq_k_1 in E1. generalize (kseq_letters k 2). lia.
 - assert (SU' : SubSeq [kseq k q; k; k; a] (kseq k)).
   { exists q. unfold subseq in *. simpl in *. now f_equal. }
   apply lemma_4_5_kk in SU'. lia.
Qed.

Lemma lemma_4_5_k0 k a b :
  SubSeq [a;k;b] (kseq k) -> a <> k-1 -> b = 0.
Proof.
 intros SU N.
 destruct (Nat.eq_dec a k) as [->|A].
 - eapply lemma_4_5_kk'; eauto.
 - destruct (SubSeq_RightExt _ _ SU) as (c, SU').
   destruct (Nat.eq_dec b k) as [->|B].
   + apply lemma_4_5_kk in SU'. lia.
   + apply (lemma_4_5 k 1 a b) in SU; lia.
Qed.

Lemma RS_ak k u a : RightSpecial (u ++ [a;k]) (kseq k) -> a = k-1.
Proof.
 intros RS.
 eapply RightSpecial_Suffix in RS; [|now exists u].
 destruct RS as (b & c & BC & B & C).
 destruct (Nat.eq_dec a (k-1)) as [E|N]; try easy.
 apply lemma_4_5_k0 in B, C; trivial. lia.
Qed.

Lemma corollary_4_6_aux k r : k<>0 -> 2 <= r ->
  ~RightSpecial (repeat k r) (kseq k).
Proof.
 intros K R RS.
 apply RightSpecial_Suffix with (u:=[k;k]) in RS.
 - destruct RS as (a & b & AB & A & B). apply lemma_4_5_kk' in A, B. lia.
 - exists (repeat k (r-2)). change [k;k] with (repeat k 2).
   rewrite <- repeat_app. f_equal; lia.
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
   { cbn. now rewrite ksubst_k. }
   rewrite E, kprefix_klvalence. lia.
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

Lemma SubSeq_kk k u :
  SubSeq (u++[k;k]) (kseq k) -> SubSeq (u++[k;k;0]) (kseq k).
Proof.
 intros (q,SU).
 assert (SU' : SubSeq (u++[k;k;kseq k (q + length u + 2)]) (kseq k)).
 { exists q. unfold subseq in *; rewrite app_length in *. simpl in *.
   rewrite (Nat.add_succ_r (length u)), seq_S, map_app, <- SU.
   rewrite <- app_assoc. simpl. do 5 f_equal. lia. }
 set (n := q + _ + 2) in *.
 replace (kseq k n) with 0 in *; trivial.
 symmetry. apply (lemma_4_5_kk' k). eapply Sub_SubSeq; eauto.
 apply Sub_app_l, Sub_id.
Qed.

Lemma LeftSpecial_kk k u :
  LeftSpecial (u++[k;k]) (kseq k) -> LeftSpecial (u++[k;k;0]) (kseq k).
Proof.
 intros (a & b & AB & A & B). exists a, b. split; trivial. split.
 apply (SubSeq_kk k (a::u)), A.
 apply (SubSeq_kk k (b::u)), B.
Qed.

Lemma lemma_4_9 k u :
  SubSeq (u++[k-1]) (kseq k) -> SubSeq (u++[k-1;k]) (kseq k).
Proof.
 intros (q,E). exists q. rewrite app_length in *.
 unfold subseq in *. simpl in *.
 rewrite !Nat.add_succ_r, !seq_S, !map_app in *. simpl in *.
 set (n := length u) in *. rewrite Nat.add_0_r in *.
 apply app_inv' in E; trivial. destruct E as (<-,[= E]).
 now rewrite Nat.add_succ_r, kseq_next_km1, <- E, <- app_assoc.
Qed.

Lemma lemma_4_9_ls k u :
  LeftSpecial (u++[k-1]) (kseq k) -> LeftSpecial (u++[k-1;k]) (kseq k).
Proof.
 intros (a & b & AB & A & B). exists a, b; repeat split; trivial.
 now apply (lemma_4_9 k (a::u)).
 now apply (lemma_4_9 k (b::u)).
Qed.

Lemma kseq_after_k k a : SubSeq [k;a] (kseq k) -> a = 0 \/ a = k.
Proof.
 intros (q,SU). unfold subseq in *. simpl in *. injection SU as E1 E2.
 generalize (kseq_next_letter k q). rewrite <- E2, <- E1, next_letter_k. lia.
Qed.

Lemma kword_kp2 k : kword k (k+2) = kword k k ++ [k;k;0].
Proof.
 rewrite !Nat.add_succ_r, !kword_eqn, !Nat.add_0_r, Nat.sub_diag by lia.
 rewrite <- app_assoc. f_equal.
 replace (S k - k) with 1 by lia. cbn. now rewrite ksubst_k.
Qed.

Lemma krvalence_letter_k k : k<>0 -> krvalence k [k] = 2.
Proof.
 intros K.
 unfold krvalence. change 2 with (length [0; k]).
 eapply Permutation_length, AllRightExts_unique; eauto using krightexts_ok.
 split.
 - repeat constructor; simpl; intuition.
 - intros a. simpl. intuition; try subst a.
   + exists 0. cbn. now rewrite ksubst_k.
   + apply SubSeq_kseq_alt. exists (k+2). rewrite kword_kp2.
     apply Sub_app_l. now exists [],[0].
   + apply kseq_after_k in H. intuition.
Qed.

Lemma krvalence_low_letter k a : a<k-1 -> krvalence k [a] = 2.
Proof.
 intros K.
 unfold krvalence. change 2 with (length [S a; k]).
 eapply Permutation_length, AllRightExts_unique; eauto using krightexts_ok.
 split.
 - repeat constructor; simpl; intuition. lia.
 - intros b. simpl. intuition; try subst b.
   + exists (S a). unfold subseq. simpl.
     now rewrite !all_letters_occur by lia.
   + red. simpl.
     assert (SubSeq [a;k;0] (kseq k)) by (apply (lemma_4_5 k 1); lia).
     eapply Sub_SubSeq; eauto. now exists [], [0].
   + red in H. simpl in H.
     destruct (Nat.eq_dec k b) as [->|N]. intuition.
     apply (lemma_4_5 k 0) in H; lia.
Qed.

(** Instead of proposition 3.8 and theorem 3.9 about Infinite Left Special,
    we use here an ad-hoc decreasing principle, that avoid the need for
    infinitary objects (delicates in Coq). Moreover, it explicits the fact
    that we may need to right-extend LeftSpecial words, but at most once. *)

Lemma DecrLemma k u :
  1 < length u ->
  LeftSpecial u (kseq k) ->
  (last u 0 = k -> exists x, LeftSpecial (u++[x]) (kseq k)) ->
  exists v w,
    LeftSpecial v (kseq k) /\
    (w=[]\/w=[0]) /\
    ksubstw k v = u++w /\
    length v < length u.
Proof.
 intros U LS LS'.
 assert (K := ls_knz _ _ LS).
 destruct (Nat.eq_dec (last u 0) k) as [L|N].
 - specialize (LS' L). destruct LS' as (x & LS'). clear LS.
   assert (U' : u <> []) by now intros ->.
   assert (E := app_removelast_last 0 U').
   rewrite L in E.
   set (u' := removelast u) in *. clearbody u'. subst u. clear L U'.
   rewrite app_length in U. simpl in U. rewrite Nat.add_1_r in U.
   rewrite <- app_assoc in LS'. simpl in LS'.
   destruct (Nat.eq_dec x k) as [->|N'].
   + destruct (lemma_3_7_ii_ls k (u'++[k;k;0])) as (v & V & V').
     { rewrite last_app; simpl. lia. easy. }
     { now apply LeftSpecial_kk. }
     assert (N : v <> []).
     { intros ->. simpl in V. now destruct u'. }
     assert (E := app_removelast_last 0 N).
     set (v' := @removelast nat v) in *. clearbody v'.
     rewrite E in V. rewrite ksubstw_app in V.
     revert V. simpl. rewrite app_nil_r.
     unfold ksubst. case Nat.eqb_spec.
     2:{ change [k;k;0] with ([k;k]++[0]).
         rewrite app_assoc. intros _ V. apply app_inv' in V; easy. }
     change [k;k;0] with ([k]++[k;0]); rewrite app_assoc.
     intros E' V. rewrite E' in E. clear E'.
     apply app_inv' in V; simpl; trivial. destruct V as (V,_).
     exists v', []; repeat split; trivial.
     * rewrite E in V'. eapply LeftSpecial_Prefix; eauto.
       now exists [k].
     * now left.
     * now rewrite app_nil_r.
     * rewrite <- V. rewrite len_ksubst.
       destruct v' as [|a v']; [now destruct u'|].
       rewrite E in V'. simpl in V'. apply ls_head_k in V'. subst a.
       simpl in *. rewrite Nat.eqb_refl. lia.
   + destruct (kseq_after_k k x) as [-> | ->]; try lia.
     { apply LeftSpecial_SubSeq in LS'. eapply Sub_SubSeq; eauto.
       apply Sub_app_l, Sub_id. }
     clear N'.
     destruct (lemma_3_7_ii_ls k (u'++[k;0])) as (v & V & V'); trivial.
     { rewrite last_app; simpl. lia. easy. }
     exists v, [0]; repeat split; trivial.
     * now right.
     * now rewrite V, <- app_assoc.
     * assert (E := len_ksubst k v).
       rewrite V in E. rewrite app_length in *. simpl in *.
       assert (N : v <> []) by (intros ->; now destruct u').
       assert (E' := app_removelast_last 0 N).
       set (v' := @removelast nat v) in *. clearbody v'.
       rewrite E' in V. rewrite ksubstw_app in V.
       revert V. simpl. rewrite app_nil_r.
       unfold ksubst. case Nat.eqb_spec.
       2:{ change [k;0] with ([k]++[0]).
           rewrite app_assoc. intros _ V. apply app_inv' in V; easy. }
       intros E2 V. rewrite E2 in E'. clear E2.
       apply app_inv' in V; simpl; trivial. destruct V as (V,_).
       assert (2 <= nbocc k v); try lia.
       { rewrite E'. rewrite nbocc_app. simpl. rewrite Nat.eqb_refl.
         destruct v' as [|a v']; simpl in *. now subst u'.
         rewrite E' in V'. apply ls_head_k in V'. subst a.
         rewrite Nat.eqb_refl. lia. }
 - clear LS'.
   destruct (lemma_3_7_ii_ls k u) as (v & V & V'); trivial.
   exists v, []; repeat split; trivial.
   + now left.
   + now rewrite app_nil_r.
   + rewrite <- V, len_ksubst.
     destruct v as [|a v]; simpl in *. now subst u.
     apply ls_head_k in V'. subst a. rewrite Nat.eqb_refl. lia.
Qed.

(** Turn the lack of MaxLeftSpecial into a positive fact about LeftSpecial. *)

Lemma NoMaxLS_exists k u :
  LeftSpecial u (kseq k) ->
  ~MaxLeftSpecial u (kseq k) ->
  exists a, LeftSpecial (u++[a]) (kseq k).
Proof.
 intros LS NM.
 set (l := seq 0 (S k)).
 destruct (existsb (fun a => Nat.leb 2 (klvalence k (u++[a]))) l) eqn:E.
 - rewrite existsb_exists in E.
   destruct E as (a & IN & LS'). exists a. now apply ls_val, Nat.leb_le.
 - exfalso. apply NM. split; trivial. intros a LS'.
   assert (a <= k).
   { apply all_letters_subseq. apply LeftSpecial_SubSeq in LS'.
     eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
   apply ls_val, Nat.leb_le in LS'.
   rewrite <- not_true_iff_false, existsb_exists in E. apply E. clear E.
   exists a; split; trivial. apply in_seq. lia.
Qed.

(* Two auxiliary lemmas for Proposition 4.10 : ante-image of right
   extensions *)

Lemma inv_letter_for_4_10 k u v' b :
  MaxLeftSpecial u (kseq k) -> last u 0 <> k -> ksubstw k v' = u ->
  RightExt u b (kseq k) ->
  exists b', RightExt v' b' (kseq k) /\ ~LeftSpecial (v'++[b']) (kseq k) /\
             head (ksubst k b') = Some b.
Proof.
 intros (LS,NLS) L E B.
 assert (K : k<>0) by now apply ls_knz in LS.
 assert (U : u<>[]). { intros ->. now apply (lemma_4_7 k 0). }
 destruct (Nat.eq_dec b k) as [->|NB].
 - destruct (SubSeq_RightExt _ _ B) as (b2 & B2).
   red in B2. rewrite <- app_assoc in B2. simpl in B2.
   assert (B2' : SubSeq [k;b2] (kseq k)).
   { eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
   destruct (kseq_after_k _ _ B2') as [-> | ->].
   + destruct (lemma_3_7_ii_cor k (u++[k;0])) as (v & V & SU); trivial.
     { destruct u; simpl; try easy. apply ls_head_k in LS; lia. }
     { rewrite last_app; simpl; easy || lia. }
     assert (E2 : v = v' ++ [k]).
     { apply (ksubstw_inv k). rewrite ksubstw_app, V, E. f_equal.
       cbn. now rewrite ksubst_k. }
     exists k; repeat split.
     { red. now rewrite <- E2. }
     { rewrite <- E2. intro LS3.
       apply lemma_3_7_i_ls in LS3. rewrite V in LS3.
       apply (NLS k).
       eapply LeftSpecial_Prefix; eauto.
       exists [0]. now rewrite <- app_assoc. }
     { now rewrite ksubst_k. }
   + destruct (SubSeq_RightExt _ _ B2) as (b3 & B3).
     red in B3. rewrite <- app_assoc in B3. simpl in B3.
     assert (B3' : SubSeq [k;k;b3] (kseq k)).
     { eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
     rewrite (lemma_4_5_kk' _ _ B3') in *.
     destruct (lemma_3_7_ii_cor k (u++[k;k;0])) as (v & V & SU); trivial.
     { destruct u; simpl; try easy. apply ls_head_k in LS; lia. }
     { rewrite last_app; simpl; easy || lia. }
     assert (E2 : v = v' ++ [k-1;k]).
     { apply (ksubstw_inv k). rewrite ksubstw_app, V, E. f_equal.
       cbn. now rewrite ksubst_km1, ksubst_k by trivial. }
     exists (k-1); repeat split; rewrite ?ksubst_km1 in *; trivial.
     { red. apply Sub_SubSeq with v; auto. subst v.
       exists [], [k]. now rewrite <- !app_assoc. }
     { intro LS3. apply lemma_3_7_i_ls in LS3.
       rewrite ksubstw_app, E in LS3. simpl in LS3.
       rewrite app_nil_r in LS3. rewrite ksubst_km1 in LS3 by trivial.
       now apply NLS in LS3. }
 - assert (b<>0).
   { intros ->.
     red in B.
     rewrite (app_removelast_last 0 U), <- app_assoc in B.
     simpl in B.
     eapply Sub_SubSeq in B; [|apply Sub_app_l, Sub_id].
     apply letters_RightExt in B. destruct B as [B|B]; try lia.
     revert B. unfold next_letter in *. case Nat.eqb_spec; lia. }
   destruct (lemma_3_7_ii_cor k (u++[b])) as (v & V & SU); trivial.
   { destruct u as [|x u]; simpl; try easy. apply ls_head_k in LS.
     now subst x. }
   { now rewrite last_last. }
   assert (b <= k).
   { eapply Sub_SubSeq in B; [|apply Sub_app_l, Sub_id].
     now apply all_letters_subseq in B. }
   assert (B2 : ksubst k (b-1) = [b]).
   { unfold ksubst. case Nat.eqb_spec. lia. intros _. f_equal; lia. }
   assert (E2 : v = v'++[b-1]).
   { apply (ksubstw_inv k). rewrite ksubstw_app, E, V. f_equal.
     simpl. now rewrite app_nil_r. }
   exists (b-1); repeat split.
   { red. now rewrite <- E2. }
   { rewrite <- E2. intros LS3.
     apply lemma_3_7_i_ls in LS3. rewrite V in LS3.
     now apply NLS in LS3. }
   { now rewrite B2. }
Qed.

Lemma inv_letter_bis_for_4_10 k u v' b :
  MaxLeftSpecial (u++[k]) (kseq k) -> ksubstw k v' = u ->
  RightExt (u++[k]) b (kseq k) ->
  exists b', RightExt v' b' (kseq k) /\ ~LeftSpecial (v'++[b']) (kseq k) /\
             ((b = k /\ b' = k-1) \/ (b = 0 /\ b' = k)).
Proof.
 intros (LS,NLS) E B.
 assert (K : k<>0) by now apply ls_knz in LS.
 assert (U : u<>[]). { intros ->. now apply (lemma_4_7 k 1). }
 destruct (kseq_after_k k b) as [-> | ->].
 { red in B. rewrite <- app_assoc in B. simpl in B.
   eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
 - exists k.
   destruct (lemma_3_7_ii_cor k (u++[k;0])) as (v & V & SU); trivial.
   { destruct u; simpl; try easy. apply ls_head_k in LS; lia. }
   { rewrite last_app; simpl; easy || lia. }
   { red in B. now rewrite <- app_assoc in B. }
   replace v with (v' ++ [k]) in *.
   2:{ apply (ksubstw_inv k). rewrite ksubstw_app, V, E. f_equal.
       cbn. now rewrite ksubst_k. }
   repeat split; trivial; [|now right].
   intros LS'. apply lemma_3_7_i_ls in LS'.
   rewrite V in LS'. apply (NLS 0). now rewrite <- !app_assoc.
 - exists (k-1).
   destruct (SubSeq_RightExt _ _ B) as (b2 & B2).
   red in B2. rewrite <- !app_assoc in B2. simpl in B2.
   assert (B2' : SubSeq [k;k;b2] (kseq k)).
   { eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
   apply lemma_4_5_kk' in B2'. subst b2.
   destruct (lemma_3_7_ii_cor k (u++[k;k;0])) as (v & V & SU); trivial.
   { destruct u; simpl; try easy. apply ls_head_k in LS; lia. }
   { rewrite last_app; simpl; easy || lia. }
   replace v with (v' ++ [k-1;k]) in *.
   2:{ apply (ksubstw_inv k). rewrite ksubstw_app, V, E. f_equal.
     cbn. now rewrite ksubst_k, ksubst_km1. }
   repeat split; try now left.
   { eapply Sub_SubSeq; eauto.
     exists [], [k]. now rewrite <- app_assoc. }
   { intros LS'. apply lemma_4_9_ls in LS'. apply lemma_3_7_i_ls in LS'.
     rewrite V in LS'. apply (NLS k).
     eapply LeftSpecial_Prefix; eauto. exists [0].
     now rewrite <- !app_assoc. }
Qed.

(** Proposition 4.10 as proved in Corrigendum (as Proposition 2.2).
    Some parts of the proofs were unecessary here :
    - We are here in the case "t_1 > max(t_2...t_{m-1})" (t_1=t_m=1>0=t_i).
    - The last paragraph is skipped since factors of (kseq k) cannot
      have a right valence of 3>2.

    Moreover This proof of proposition 4.10 is left here for completeness
    reasons, but a shorter approach is also possible (and was used in a
    former version of this work) : just prove that v is LeftSpecial
    instead of MaxLeftSpecial, and moreover that
      [w=[k] -> ~RightSpecial (ksubstw k v) (kseq k)].
    This is enough for completing [LeftSpecial_kprefix] below, and then
    proving ~MaxLeftSpecial afterwards. *)

Lemma proposition_4_10 k u x :
  MaxLeftSpecial u (kseq k) -> x<>k -> In x u ->
  exists v w,
    MaxLeftSpecial v (kseq k) /\ u = ksubstw k v ++ w /\ (w=[] \/ w = [k]).
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { intros ((b & c & BC & B & C),_). apply LeftExt_letter in B, C. lia. }
 intros (LS,NLS) X IN.
 assert (E : exists u' r, u = u' ++ repeat k r /\ last u' 0 <> k /\ (r=0\/r=1)).
 { destruct (Nat.eq_dec (last u 0) k) as [E|N].
   - assert (N : u <> []) by (intros ->; inversion IN).
     assert (U' := app_removelast_last 0 N).
     set (u' := removelast u) in *. clearbody u'. rewrite E in *. clear N E.
     exists u', 1; repeat split; trivial; try now right. intros E'.
     assert (N' : u' <> []). { intros ->. simpl in *. now apply K. }
     rewrite (app_removelast_last 0 N'), E', <- app_assoc in U'. simpl in U'.
     clear E' N'.
     eapply (corollary_4_6 k _ 2); trivial.
     apply observation_4_2_contra. simpl. rewrite <- U'. split; trivial.
   - exists u, 0; repeat split; trivial; try now left. simpl.
     now rewrite app_nil_r. }
 destruct E as (u' & r & E & L & R).
 assert (LS' : LeftSpecial u' (kseq k)).
 { eapply LeftSpecial_Prefix; eauto. now exists (repeat k r). }
 assert (U' : u' <> []).
 { intros ->. simpl in *. subst u. apply repeat_spec in IN; lia. }
 clear x X IN.
 destruct (lemma_3_7_ii_ls k u' L LS') as (v' & V1 & V2).
 exists v', (repeat k r); repeat split; trivial; try congruence.
 2:{ destruct R; subst; simpl; intuition. }
 (* v' is Maximal Left Special *)
 intros a A.
 assert (RS: RightSpecial u (kseq k)).
 { apply observation_4_2_contra; split; trivial. }
 destruct RS as (b & c & BC & B & C). red in B,C.
 assert (B' := NLS b).
 assert (C' := NLS c).
 assert (E' : exists b' c', b'<>c' /\
            RightExt v' b' (kseq k) /\ ~LeftSpecial (v'++[b']) (kseq k) /\
            RightExt v' c' (kseq k) /\ ~LeftSpecial (v'++[c']) (kseq k)).
 { destruct R; subst r; simpl in E; rewrite ?app_nil_r in E; subst u.
   - destruct (inv_letter_for_4_10 k u' v' b) as (b' & B1 & B2 & B3);
     destruct (inv_letter_for_4_10 k u' v' c) as (c' & C1 & C2 & C3);
       try split; trivial.
     exists b', c'; repeat split; trivial; congruence.
   - destruct (inv_letter_bis_for_4_10 k u' v' b) as (b' & B1 & B2 & B3);
     destruct (inv_letter_bis_for_4_10 k u' v' c) as (c' & C1 & C2 & C3);
       try split; trivial.
     exists b',c'; repeat split; trivial; lia. }
 clear b c BC B B' C C'.
 destruct E' as (b & c & BC & B & B' & C & C').
 assert (AB : a <> b). { intros ->. now apply B'. }
 assert (AC : a <> c). { intros ->. now apply C'. }
 assert (3 <= krvalence k v').
 { apply LeftSpecial_SubSeq in A.
   change 3 with (length [a;b;c]).
   apply NoDup_incl_length.
   - clear -AB AC BC. repeat constructor; simpl; intuition.
   - destruct (krightexts_ok k v') as (_,RE). clear - A B C RE.
     intros x X. simpl in X. intuition; subst x; rewrite RE; auto. }
 assert (krvalence k v' <= 2).
 { apply krvalence_le_2. intros ->. simpl in *. now subst. }
 lia.
Qed.

Lemma norepeat_exists (k:nat) u :
  u <> repeat k (length u) -> exists a, a<>k /\ In a u.
Proof.
 induction u as [|a u IH]; simpl; intros N; try easy.
 destruct (Nat.eq_dec a k) as [->|N']; [|exists a; tauto].
 destruct IH as (a & A & IN).
 { contradict N. now f_equal. }
 exists a; tauto.
Qed.

Lemma corollary_4_11 k u : ~MaxLeftSpecial u (kseq k).
Proof.
 remember (length u) as n eqn:N. symmetry in N. revert u N.
 induction n as [n IH] using lt_wf_ind. intros u N LS.
 destruct (norepeat_exists k u) as (x & X & IN); trivial.
 { rewrite N. intros ->. now apply (lemma_4_7 k n). }
 destruct (proposition_4_10 k u x) as (v & w & V & E & W); trivial.
 assert (L : length v < n).
 { rewrite <- N, E, app_length, len_ksubst.
   destruct V as (V,_). destruct v.
   - simpl in *. intuition; subst; simpl. inversion IN. lia.
   - apply ls_head_k in V. subst. simpl. rewrite Nat.eqb_refl. lia. }
 apply (IH (length v) L v); auto.
Qed.

(** Major property : the only LeftSpecial factors of (kseq k) are
    its prefixes. *)

Lemma LeftSpecial_kprefix k u :
  LeftSpecial u (kseq k) -> PrefixSeq u (kseq k).
Proof.
 remember (length u) as n eqn:N. revert u N.
 induction n as [n IH] using lt_wf_ind. intros u N LS.
 destruct (Nat.eq_dec n 0) as [->|N0].
 { now destruct u. }
 destruct (Nat.eq_dec n 1) as [->|N1].
 { destruct u as [|a [|b u]]; try easy. apply ls_head_k in LS. now subst a. }
 destruct (DecrLemma k u) as (v & w & V & W & E' & L); lia||auto.
 - intros _. apply NoMaxLS_exists; trivial. apply corollary_4_11.
 - rewrite <- N in L.
   specialize (IH _ L v eq_refl V). apply ksubstw_prefix in IH.
   rewrite E' in IH. eapply Prefix_PrefixSeq; eauto. now exists w.
Qed.

Lemma LeftSpecial_carac k u : k<>0 ->
  LeftSpecial u (kseq k) <-> PrefixSeq u (kseq k).
Proof.
 intros K. split.
 - apply LeftSpecial_kprefix.
 - intros P. rewrite P. fold (kprefix k (length u)).
   apply ls_val. rewrite kprefix_klvalence. lia.
Qed.

Lemma LeftSpecial_carac' k u : k<>0 ->
  LeftSpecial u (kseq k) <-> u = kprefix k (length u).
Proof.
 intros K. now rewrite LeftSpecial_carac.
Qed.

(** Some leftover proofs that could only be obtained now : *)

Lemma ls_val_Sk k u : LeftSpecial u (kseq k) -> klvalence k u = S k.
Proof.
 intros LS.
 assert (K := ls_knz _ _ LS).
 apply LeftSpecial_carac' in LS; trivial. rewrite LS.
 apply kprefix_klvalence.
Qed.

Lemma lemma_3_7_i_ls_val k u :
  LeftSpecial u (kseq k) -> klvalence k (ksubstw k u) = klvalence k u.
Proof.
 intros LS. rewrite (ls_val_Sk _ _ LS).
 now apply ls_val_Sk, lemma_3_7_i_ls.
Qed.

Lemma klvalence_1_or_Sk k u :
  SubSeq u (kseq k) -> klvalence k u = 1 \/ klvalence k u = S k.
Proof.
 intros SU. apply klvalence_nz in SU.
 destruct (Nat.eq_dec (klvalence k u) 1) as [E|N].
 - now left.
 - right. apply ls_val_Sk, ls_val. lia.
Qed.


(** Now that we have a unique LeftSpecial per length,
    application to factor counting and complexity. *)

Definition next_kfactors k p :=
  let f := kprefix k p in
  let l := filter (fun u => negb (listnat_eqb u f)) (kfactors k p) in
  map (fun x => x::f) (seq 0 (S k)) ++
  map (fun u => hd 0 (kleftexts k u) :: u) l.

Lemma next_kfactors_iff k p u : k<>0 ->
  In u (next_kfactors k p) <-> In u (kfactors k (S p)).
Proof.
 intros K.
 split.
 - rewrite kfactors_in.
   unfold next_kfactors.
   rewrite in_app_iff, !in_map_iff.
   intros [(x & <- & IN)|(v & E & IN)].
   + split.
     * simpl. f_equal. apply kprefix_length.
     * destruct (kprefix_allleftexts k p) as (_,H).
       rewrite H in IN. apply IN.
   + rewrite filter_In in IN. destruct IN as (IN,E').
     revert E'. case listnat_eqb_spec; intros; try easy. clear E'.
     rewrite kfactors_in in IN. destruct IN as (L,IN).
     assert (NLS : ~LeftSpecial v (kseq k)).
     { now rewrite LeftSpecial_carac', L. }
     rewrite ls_val in NLS.
     assert (N := klvalence_nz k v IN).
     assert (E' : klvalence k v = 1) by lia. clear NLS N.
     unfold klvalence in E'.
     destruct (kleftexts_ok k v) as (_,LE).
     destruct (kleftexts k v) as [|a [|b l]]; simpl in *; try easy.
     rewrite <- E.
     split.
     * simpl. now f_equal.
     * apply LE. now left.
 - rewrite kfactors_in. intros (L,IN).
   unfold next_kfactors. rewrite in_app_iff, !in_map_iff.
   destruct u as [|a u]; try easy. simpl in L. injection L as L.
   destruct (listnat_eqb_spec u (kprefix k p)) as [->|N].
   + left. exists a; split; trivial.
     apply in_seq. apply LeftExt_letter in IN. lia.
   + right. exists u; split; trivial.
     * f_equal.
       assert (NLS : ~LeftSpecial u (kseq k)).
       { now rewrite LeftSpecial_carac', L. }
       rewrite ls_val in NLS.
       assert (SU : SubSeq u (kseq k)).
       { eapply Sub_SubSeq; eauto. apply Sub_cons_r. }
       assert (N' := klvalence_nz k u SU).
       assert (E : klvalence k u = 1) by lia. clear NLS N'.
       unfold klvalence in E.
       destruct (kleftexts_ok k u) as (_,LE).
       rewrite <- (LE a) in IN. clear LE.
       destruct (kleftexts k u) as [|b [|c ]]; simpl in *; try easy.
       intuition.
     * apply filter_In. split.
       { rewrite kfactors_in. split; trivial.
         eapply Sub_SubSeq; eauto. apply Sub_cons_r. }
       { now case listnat_eqb_spec. }
Qed.

Lemma next_kfactors_nodup k p : NoDup (next_kfactors k p).
Proof.
 apply app_nodup.
 - apply FinFun.Injective_map_NoDup; try apply seq_NoDup.
   now injection 1.
 - apply FinFun.Injective_map_NoDup.
   + now injection 1.
   + apply NoDup_filter, kfactors_nodup.
 - intros x. rewrite !in_map_iff.
   intros ((a & <- & IN),(u & E & IN')).
   rewrite filter_In in IN'. destruct IN' as (IN',E').
   injection E as E1 E2.
   revert E'. now case listnat_eqb_spec.
Qed.

Lemma next_kfactors_ok k p : k<>0 ->
  Permutation (next_kfactors k p) (kfactors k (S p)).
Proof.
 intros K.
 apply NoDup_Permutation.
 - apply next_kfactors_nodup.
 - apply kfactors_nodup.
 - intros u. now apply next_kfactors_iff.
Qed.

Lemma filter_partition {A} (f : A -> bool) l :
 Permutation (filter f l ++ filter (fun x => negb (f x)) l) l.
Proof.
 induction l as [|a l IH]; simpl; auto.
 destruct (f a); simpl.
 - now apply perm_skip.
 - apply Permutation_sym.
   eapply Permutation_trans. 2:apply Permutation_middle.
   now apply perm_skip.
Qed.

Lemma filter_partition_length {A} (f : A -> bool) l :
 length (filter f l) + length (filter (fun x => negb (f x)) l) = length l.
Proof.
 rewrite <- app_length. apply Permutation_length, filter_partition.
Qed.

Lemma next_kfactor_length k p : k<>0 ->
 length (next_kfactors k p) = length (kfactors k p) + k.
Proof.
 intros K.
 unfold next_kfactors. rewrite app_length, !map_length, seq_length.
 set (f := fun u => listnat_eqb u (kprefix k p)).
 change (fun u => _) with (fun u => negb (f u)).
 rewrite <- (filter_partition_length f (kfactors k p)).
 set (l2 := filter (fun x => _) _).
 replace (filter f (kfactors k p)) with [kprefix k p]; simpl; try lia.
 symmetry. apply Permutation_length_1_inv.
 symmetry. apply NoDup_Permutation_bis.
 - apply NoDup_filter, kfactors_nodup.
 - simpl.
   apply lengthge1_carac with (kprefix k p).
   apply filter_In. split.
   + rewrite kfactors_in. split. now rewrite kprefix_length.
     eapply Sub_SubSeq. 2:apply (kprefix_leftext k p 0); try lia.
     apply Sub_cons_r.
   + unfold f. now case listnat_eqb_spec.
 - intros u. rewrite filter_In. unfold f.
   case listnat_eqb_spec; intros; subst; intuition.
Qed.

Lemma kfactors_length k p : length (kfactors k p) = k*p+1.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 { now rewrite kfactors_0_l. }
 induction p.
 - rewrite kfactors_0_r. simpl. lia.
 - assert (E := next_kfactors_ok k p).
   apply Permutation_length in E; trivial.
   rewrite <- E, next_kfactor_length, IHp; lia.
Qed.

Lemma kseq_complexity k : forall p, Complexity (kseq k) p (k*p+1).
Proof.
 intros p. exists (kfactors k p). split; [|split].
 - apply kfactors_nodup.
 - apply kfactors_length.
 - apply kfactors_in.
Qed.

(* Print Assumptions kseq_complexity. *)
