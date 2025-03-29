Require Import MoreTac MoreList DeltaList GenFib GenG Words WordFactor.
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

(** Computing the left and right extensions, thanks to qfactors
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

Section Knonzero.
Variable k:nat.
Hypothesis K:k<>0.

Lemma LeftExt_letter a u : LeftExt a u (kseq k) -> a < k.
Proof.
  unfold LeftExt, SubSeq. intros (p, E). unfold subseq in E.
  simpl in E. injection E as E _.
  generalize (kseq_letters k p). lia.
Qed.

Lemma RightExt_letter u a : RightExt u a (kseq k) -> a < k.
Proof.
  unfold RightExt, SubSeq. intros (p, E). revert E.
  unfold subseq. rewrite app_length. simpl.
  rewrite Nat.add_succ_r, seq_S, map_app. simpl. intros E.
  apply app_inv' in E; trivial. destruct E as (_,[= ->]).
  now apply kseq_letters.
Qed.

Definition kleftexts u :=
 let l := kfactors0opt k (S (length u)) in
 filter (fun a => wordmem (a::u) l) (seq 0 k).

Definition klvalence (u:word) := length (kleftexts u).

Definition krightexts u :=
 let l := kfactors0opt k (S (length u)) in
 filter (fun a => wordmem (u++[a]) l) (seq 0 k).

Definition krvalence (u:word) := length (krightexts u).

Lemma kleftexts_ok u : AllLeftExts (kleftexts u) u (kseq k).
Proof.
 split.
 - apply NoDup_filter, seq_NoDup.
 - intros a.
   unfold kleftexts.
   rewrite filter_In, in_seq, wordmem_spec, kfactors0opt_in by trivial.
   split.
   + intros (_ & _ & SU). apply SU.
   + unfold LeftExt. intros SU. split; [|split]; trivial.
     red in SU. destruct SU as (p & E). unfold subseq in E. simpl in E.
     injection E as E _. generalize (kseq_letters k p); lia.
Qed.

Lemma krightexts_ok u : AllRightExts u (krightexts u) (kseq k).
Proof.
 split.
 - apply NoDup_filter, seq_NoDup.
 - intros a.
   unfold krightexts.
   rewrite filter_In, in_seq, wordmem_spec, kfactors0opt_in by trivial.
   split.
   + intros (_ & _ & SU). apply SU.
   + unfold RightExt. intros SU. split; [|split]; trivial.
     2:{ rewrite app_length; simpl; lia. }
     red in SU. destruct SU as (p & E). unfold subseq in E.
     rewrite app_length in E. simpl in *.
     rewrite Nat.add_succ_r, seq_S, map_app in E. simpl in E.
     apply app_inv' in E; trivial. destruct E as (_,E).
     injection E as E. generalize (kseq_letters k (p+(length u+0))); lia.
Qed.

Lemma klvalence_ok l u :
  AllLeftExts l u (kseq k) -> klvalence u = length l.
Proof.
 intros A. rewrite (@Permutation_length _ l (kleftexts u)); try easy.
 eapply AllLeftExts_unique; eauto using kleftexts_ok.
Qed.

Lemma krvalence_ok u l :
  AllRightExts u l (kseq k) -> krvalence u = length l.
Proof.
 intros A. rewrite (@Permutation_length _ l (krightexts u)); try easy.
 eapply AllRightExts_unique; eauto using krightexts_ok.
Qed.

Lemma kword_ls p a : a < k -> LeftExt a (kword k p) (kseq k).
Proof.
 intros Ha.
 set (r := a + p + k - p mod k).
 assert (p <= r).
 { generalize (Nat.mod_upper_bound p k). lia. }
 assert (E : r mod k = a).
 { unfold r. replace (a+p+k) with (a+k+p) by lia.
   rewrite (Nat.div_mod_eq p k) at 1 by lia.
   rewrite Nat.add_assoc, Nat.add_sub.
   rewrite Nat.mul_comm, Nat.mod_add by lia.
   replace k with (1 * k) at 1 by lia. rewrite Nat.mod_add by lia.
   apply Nat.mod_small; lia. }
 apply LeftExt_Prefix with (kword k (r+2)).
 - apply kword_le_prefix; lia.
 - assert (SU : SubSeq (kword k (r+2+k)) (kseq k)).
   { rewrite SubSeq_kseq_alt. exists (r+2+k). apply Sub_id. }
   rewrite kword_eqn in SU by lia.
   replace (r+2+k-k) with (r+2) in SU by lia.
   rewrite (@app_removelast_last _ (kword k (r+2+k-1)) 0) in SU.
   2:{ apply kword_nz. }
   rewrite <- app_assoc in SU.
   rewrite WordSuffix.kword_last in SU by trivial.
   replace (r+2+k-1+k-1) with (r+2*k) in SU by lia.
   rewrite Nat.mod_add, E in SU by lia.
   red. eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id.
Qed.

Lemma kprefix_leftext n a : a < k -> LeftExt a (kprefix k n) (kseq k).
Proof.
 intros Ha.
 rewrite kprefix_alt.
 set (p := invA_up k n).
 apply LeftExt_Prefix with (kword k p).
 - rewrite Prefix_equiv. f_equal. rewrite firstn_length_le; trivial.
   rewrite kword_len. apply invA_up_spec.
 - now apply kword_ls.
Qed.

Lemma kprefix_allleftexts n :
  AllLeftExts (seq 0 k) (kprefix k n) (kseq k).
Proof.
 split.
 - apply seq_NoDup.
 - intros a. rewrite in_seq. split.
   + intros Ha. apply kprefix_leftext. lia.
   + intros Ha. apply LeftExt_letter in Ha. lia.
Qed.

Lemma kprefix_klvalence n : klvalence (kprefix k n) = k.
Proof.
 rewrite <- (seq_length k 0) at 2. apply klvalence_ok.
 apply kprefix_allleftexts.
Qed.

Lemma kseq_leftext u : SubSeq u (kseq k) -> exists a, LeftExt a u (kseq k).
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

Lemma klvalence_nz u : SubSeq u (kseq k) -> klvalence u <> 0.
Proof.
 intros Hu.
 unfold klvalence. rewrite length_zero_iff_nil.
 destruct (kseq_leftext u Hu) as (a & Ha).
 destruct (kleftexts_ok u) as (ND,H). rewrite <- H in Ha.
 intros E. now rewrite E in Ha.
Qed.

Lemma krvalence_nz u : SubSeq u (kseq k) -> krvalence u <> 0.
Proof.
 intros Hu.
 unfold krvalence. rewrite length_zero_iff_nil.
 destruct (SubSeq_RightExt u _ Hu) as (a & Ha).
 destruct (krightexts_ok u) as (ND,H); trivial. rewrite <- H in Ha.
 intros E. now rewrite E in Ha.
Qed.

Lemma klvalence_le_k u : klvalence u <= k.
Proof.
 unfold klvalence, kleftexts.
 rewrite <- (seq_length k 0) at 2. apply filter_length_le.
Qed.

Lemma krvalence_le_k u : krvalence u <= k.
Proof.
 unfold krvalence, krightexts.
 rewrite <- (seq_length k 0) at 2. apply filter_length_le.
Qed.

Lemma prefix_incl_allleftexts u u' l l' :
  Prefix u u' -> AllLeftExts l u (kseq k) -> AllLeftExts l' u' (kseq k) ->
  incl l' l.
Proof.
 intros P (ND,Hu) (ND',Hu') a Ha. rewrite Hu' in Ha. apply Hu.
 eapply LeftExt_Prefix; eauto.
Qed.

Lemma prefix_klvalence u v : Prefix u v -> klvalence v <= klvalence u.
Proof.
 intros P. unfold klvalence. apply NoDup_incl_length.
 - apply kleftexts_ok.
 - eapply prefix_incl_allleftexts; eauto using kleftexts_ok.
Qed.

Lemma suffix_incl_allrightexts u u' l l' :
  Suffix u u' -> AllRightExts u l (kseq k) -> AllRightExts u' l' (kseq k) ->
  incl l' l.
Proof.
 intros P (ND,Hu) (ND',Hu') a Ha. rewrite Hu' in Ha. apply Hu.
 eapply RightExt_Suffix; eauto.
Qed.

Lemma suffix_krvalence u v : Suffix u v -> krvalence v <= krvalence u.
Proof.
 intros P. unfold krvalence. apply NoDup_incl_length.
 - now apply krightexts_ok.
 - eapply suffix_incl_allrightexts; eauto using krightexts_ok.
Qed.

Lemma ls_val u : LeftSpecial u (kseq k) <-> 2 <= klvalence u.
Proof.
 split.
 - intros (a & b & NE & Ha & Hb).
   unfold klvalence.
   assert (H := kleftexts_ok u). destruct H as (_,H).
   rewrite <- H in Ha, Hb. eapply lengthge2_carac; eauto.
 - unfold klvalence.
   assert (H := kleftexts_ok u). destruct H as (ND,H).
   destruct (kleftexts u) as [|a [|b l]] eqn:E; simpl; try lia.
   intros _. exists a, b; repeat split.
   + inversion_clear ND; simpl in *; intuition.
   + apply H; simpl; intuition.
   + apply H; simpl; intuition.
Qed.

Lemma rs_val u : RightSpecial u (kseq k) <-> 2 <= krvalence u.
Proof.
 split.
 - intros (a & b & NE & Ha & Hb).
   unfold krvalence.
   assert (H := krightexts_ok u). destruct H as (_,H).
   rewrite <- H in Ha, Hb. eapply lengthge2_carac; eauto.
 - unfold krvalence.
   assert (H := krightexts_ok u). destruct H as (ND,H).
   destruct (krightexts u) as [|a [|b l]] eqn:E; simpl; try lia.
   intros _. exists a, b; repeat split.
   + inversion_clear ND; simpl in *; intuition.
   + apply H; simpl; intuition.
   + apply H; simpl; intuition.
Qed.

(** Valence of letters *)

Lemma all_letters_subseq a : a < k <-> SubSeq [a] (kseq k).
Proof.
 split.
 - intros Ha. exists (S a). simpl. unfold subseq. simpl.
   now rewrite all_letters_occur.
 - apply LeftExt_letter.
Qed.

Lemma ls_head_km1 a u : LeftSpecial (a::u) (kseq k) -> a = k-1.
Proof.
 intros (b & c & N & (p,Hb) & (r,Hc)).
 unfold subseq in *. simpl in *.
 injection Hb as Hb Hb' _.
 injection Hc as Hc Hc' _.
 destruct (Nat.eq_dec a (k-1)) as [A|A]; trivial. exfalso.
 assert (b = prev_letter k a).
 { rewrite Hb, Hb'. rewrite <- (kseq_prev_letter k (S p)) by lia.
   f_equal; lia. }
 assert (c = prev_letter k a).
 { rewrite Hc, Hc'. rewrite <- (kseq_prev_letter k (S r)) by lia.
   f_equal; lia. }
 lia.
Qed.

Lemma ls_kgt1 u : LeftSpecial u (kseq k) -> 1<k.
Proof.
 intros (a & b & AB & A & B). apply LeftExt_letter in A,B. lia.
Qed.

Lemma ls_head_nz a u : LeftSpecial (a::u) (kseq k) -> a <> 0.
Proof.
 intros LS. rewrite (ls_head_km1 _ _ LS). apply ls_kgt1 in LS; lia.
Qed.

Lemma AllRightExts_km2 : AllRightExts [k-2] [k-1] (kseq k).
Proof.
 split.
 - repeat constructor. intuition.
 - intros a. simpl. split; [intros [<-|[ ]] | intros R; left].
   + exists (k-1). unfold subseq. simpl. symmetry. f_equal.
     * destruct (Nat.eq_dec k 1) as [->|K']. easy.
       replace (k-1) with (S (k-2)) by lia.
       apply all_letters_occur; lia.
     * f_equal. apply all_letters_occur; lia.
   + destruct R as (p,R). unfold subseq in R. simpl in R.
     injection R as R ->. symmetry. now apply kseq_next_km2.
Qed.

Lemma krvalence_km2 : krvalence [k-2] = 1.
Proof.
 change 1 with (length [k-1]) at 2.
 apply krvalence_ok. apply AllRightExts_km2.
Qed.

Lemma krvalence_last_km2 u :
  u<>[] -> SubSeq u (kseq k) -> last u 0 = k-2 -> krvalence u = 1.
Proof.
 intros U U' L.
 assert (SU : Suffix [k-2] u).
 { exists (removelast u). symmetry. rewrite <- L.
   now apply app_removelast_last. }
 generalize (suffix_krvalence _ _ SU) (krvalence_nz u U').
 rewrite krvalence_km2. lia.
Qed.

Lemma letters_LeftExt a b : b<k-1 ->
 LeftExt a [b] (kseq k) <-> a = prev_letter k b.
Proof.
 intros B. split.
 - intros (p, E). unfold subseq in E. simpl in E. injection E as Ea Eb.
   subst. replace p with (S p - 1) at 1 by lia. apply kseq_prev_letter; lia.
 - intros ->. exists b. unfold subseq. simpl. f_equal; symmetry.
   + unfold prev_letter.
     case Nat.eqb_spec.
     * intros ->. apply kseq_k_0.
     * intros B'. replace b with (S (pred b)) at 1 by lia.
       apply all_letters_occur. lia.
   + f_equal. apply all_letters_occur. lia.
Qed.

Lemma letters_RightExt a b :
  RightExt [a] b (kseq k) -> b = next_letter k a \/ b = k-1.
Proof.
 intros (p, E). unfold subseq in E. simpl in E. injection E as Ea Eb.
 case (Nat.eq_dec b (k-1)) as [Eb'|Eb']. now right. left. subst.
 now apply kseq_next_letter.
Qed.

Lemma letters_AllLeftExts a l : a<k-1 ->
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
   + destruct (kseq_leftext [a]) as (b & B).
     { apply all_letters_subseq; lia. }
     now rewrite <- A in B.
   + f_equal. specialize (IC x). simpl in *; intuition.
 - intros ->. split.
   + now repeat constructor.
   + intros b. rewrite letters_LeftExt; trivial. simpl; intuition.
Qed.

Lemma letters_AllRightExts_incl a l :
  AllRightExts [a] l (kseq k) -> incl l [next_letter k a; k-1].
Proof.
 intros (_,A) x Hx. rewrite A in Hx. apply letters_RightExt in Hx.
 simpl; intuition.
Qed.

Lemma klvalence_letter a : a<k-1 -> klvalence [a] = 1.
Proof.
 intros A. unfold klvalence.
 replace (kleftexts [a]) with [prev_letter k a]; trivial.
 symmetry. apply letters_AllLeftExts; auto using kleftexts_ok.
Qed.

Lemma klvalence_letter_km1 : klvalence [k-1] = k.
Proof.
 change [k-1] with (kprefix k 1). apply kprefix_klvalence.
Qed.

Lemma krvalence_letter_le a : krvalence [a] <= 2.
Proof.
 unfold krvalence. change 2 with (length [next_letter k a; k-1]).
 apply NoDup_incl_length. apply krightexts_ok.
 apply letters_AllRightExts_incl. apply krightexts_ok.
Qed.

(** We'll prove later that actually all letters have krvalence of 2
    except (k-2) whose krvalence is 1 (see krvalence_km2). *)

Lemma krvalence_le_2 u : u<>[] -> krvalence u <= 2.
Proof.
 intros Hu. transitivity (krvalence [last u 0]).
 - apply suffix_krvalence.
   exists (removelast u). symmetry. now apply app_removelast_last.
 - apply krvalence_letter_le.
Qed.


(** Lemmas from the article by Frougny et al. *)

Lemma lemma_3_7_i u a :
  LeftExt a u (kseq k) ->
  LeftExt (next_letter k a) (ksubstw k u) (kseq k).
Proof.
 intros Ha. assert (Ha' := LeftExt_letter _ _ Ha).
 unfold LeftExt in *. rewrite SubSeq_kseq_alt in *.
 destruct Ha as (n, (v & w & E)). exists (S n).
 rewrite kword_S, <- E, !ksubstw_app. cbn. clear E.
 unfold ksubst, next_letter.
 case Nat.eqb_spec; intros.
 - subst. exists (ksubstw k v ++ [k-1]), (ksubstw k w).
   now rewrite <- !app_assoc.
 - now exists (ksubstw k v), (ksubstw k w).
Qed.

Lemma lemma_3_7_i_ls u :
  LeftSpecial u (kseq k) ->
  LeftSpecial (ksubstw k u) (kseq k).
Proof.
 intros (a & b & AB & A & B).
 assert (A' := LeftExt_letter _ _ A).
 assert (B' := LeftExt_letter _ _ B).
 apply lemma_3_7_i in A, B.
 exists (next_letter k a), (next_letter k b); repeat split; trivial.
 contradict AB.
 rewrite <- (prev_next_letter k a), <- (prev_next_letter k b) by trivial.
 now rewrite AB.
Qed.

Lemma PrefixSeq_substlength_prefix u v :
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

Lemma lemma_3_7_ii_aux u a :
  hd 0 u <> 0 -> last u 0 <> k-1 ->
  LeftExt a u (kseq k) ->
  exists v, ksubstw k v = u /\
            LeftExt (prev_letter k a) v (kseq k).
Proof.
 intros HD LA Ha. assert (Ha' := LeftExt_letter _ _ Ha).
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
         - intros ->. change [k-1;0] with ([k-1]++[0]).
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
     unfold ksubst in E at 1. destruct (Nat.eqb_spec a' (k-1)).
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

Lemma lemma_3_7_ii_cor u : hd 0 u <> 0 -> last u 0 <> k-1 ->
  SubSeq u (kseq k) ->
  exists v : word, ksubstw k v = u /\ SubSeq v (kseq k).
Proof.
 intros U U' SU. destruct (kseq_leftext _ SU) as (a & LE).
 destruct (lemma_3_7_ii_aux u a U U' LE) as (v & V & V').
 exists v. split; trivial. eapply Sub_SubSeq; eauto using Sub_cons_r.
Qed.

Lemma lemma_3_7_ii_all' u l :
  SubSeq u (kseq k) -> hd 0 u <> 0 -> last u 0 <> k-1 ->
  AllLeftExts l u (kseq k) ->
  exists v, ksubstw k v = u /\
            AllLeftExts (map (prev_letter k) l) v (kseq k).
Proof.
 intros SU U U' (ND,A).
 destruct l as [|a l].
 { destruct (kseq_leftext u SU) as (a & Ha). now rewrite <- A in Ha. }
 destruct (lemma_3_7_ii_aux u a) as (v & Hv & Ha); trivial.
 { rewrite <- A. simpl; intuition. }
 exists v; split; auto. split.
 + apply NoDup_map_inv with (f:=next_letter k).
   rewrite map_map, map_ext_in with (g:=id), map_id; auto.
   intros c Hc. apply next_prev_letter. rewrite A in Hc.
   now apply LeftExt_letter in Hc.
 + intros c. rewrite in_map_iff. split.
   * intros (x & <- & IN). rewrite A in IN.
     destruct (lemma_3_7_ii_aux u x) as (v' & Hv' & Hx); trivial.
     replace v' with v in *; auto.
     { apply (ksubstw_inv k). now rewrite Hv, Hv'. }
   * intros Hc. exists (next_letter k c). split.
     { apply prev_next_letter. eapply LeftExt_letter; eauto. }
     rewrite A, <- Hv. now apply lemma_3_7_i.
Qed.

Lemma lemma_3_7_ii_val' u :
  SubSeq u (kseq k) -> hd 0 u <> 0 -> last u 0 <> k-1 ->
  exists v, ksubstw k v = u /\ klvalence v = klvalence u.
Proof.
 intros SU U U'.
 destruct (lemma_3_7_ii_all' u (kleftexts u) SU U U') as (v & Hv & H);
  auto using kleftexts_ok.
 exists v; split; auto.
 unfold klvalence at 2.
 rewrite <- (map_length (prev_letter k) (kleftexts u)).
 now apply klvalence_ok.
Qed.

Lemma lemma_3_7_ii_all u l :
  last u 0 <> k-1 ->
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
     red. apply all_letters_subseq. subst a. now apply prev_letter_lt.
   + rewrite in_map_iff. intros Ha. apply LeftExt_letter in Ha.
     exists (next_letter k a). split.
     * now apply prev_next_letter.
     * rewrite A. now apply all_letters_subseq, next_letter_lt.
 - assert (hd 0 u <> 0).
   { destruct u as [|x u]; try easy.
     simpl. apply (ls_head_nz x u).
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

Lemma lemma_3_7_ii_val u :
  last u 0 <> k-1 -> 2 <= klvalence u ->
  exists v, ksubstw k v = u /\ klvalence v = klvalence u.
Proof.
 intros U L.
 destruct (lemma_3_7_ii_all u (kleftexts u) U) as (v & Hv & H);
  auto using kleftexts_ok.
 exists v; split; auto.
 unfold klvalence.
 rewrite <- (map_length (prev_letter k) (kleftexts u)).
 now apply klvalence_ok.
Qed.

Lemma lemma_3_7_ii_ls u :
  last u 0 <> k-1 -> LeftSpecial u (kseq k) ->
  exists v, ksubstw k v = u /\ LeftSpecial v (kseq k).
Proof.
 rewrite ls_val. intros U L.
 destruct (lemma_3_7_ii_val u U L) as (v & V & E).
 exists v; split; auto. apply ls_val. lia.
Qed.

Lemma lemma_3_7_i_all_incl u l l' :
  AllLeftExts l u (kseq k) ->
  AllLeftExts l' (ksubstw k u) (kseq k) ->
  incl (map (next_letter k) l) l'.
Proof.
 intros (ND,A) (ND',A') a. rewrite in_map_iff. intros (x & <- & Hx).
 rewrite A in Hx. rewrite A'. now apply lemma_3_7_i.
Qed.

Lemma lemma_3_7_i_val_le u :
  klvalence u <= klvalence (ksubstw k u).
Proof.
 unfold klvalence.
 rewrite <- (map_length (next_letter k) (kleftexts u)).
 apply NoDup_incl_length.
 - apply NoDup_map_inv with (f:=prev_letter k).
   rewrite map_map, map_ext_in with (g:=id), map_id; auto.
   apply kleftexts_ok.
   intros a Ha. apply prev_next_letter.
   assert (H := kleftexts_ok u). destruct H as (_,H).
   rewrite H in Ha. now apply LeftExt_letter in Ha.
 - eapply lemma_3_7_i_all_incl; eauto using kleftexts_ok.
Qed.

(** Note: [k-2] has klvalence of 1 since it could only come after
    (prev_letter k (k-2)). But (ksubstw k [k-2])=[k-1] has
    klvalence of k.
    Hence the klvalence is preserved by ksubst only when it is at least 2
    (i.e. for left-special words). *)

(* /!\ Problem with the last line of the proof of Lemma 3.7 :
   \tilde{p} = p cannot be obtained in general, since (ii) needs
   last letter to be different from k-1.
   No big issue, since eventually the only LeftSpecial words
   (the kprefix) have klvalence k, hence the same for their image
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

Lemma lemma_4_4 n a : n<>0 ->
  last (kword k n) 0 = a -> Suffix [prev_letter k a; a] (kword k n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 intros Hn Ha. destruct (Nat.le_gt_cases n k).
 - clear IH. rewrite kword_low in * by lia.
   destruct n as [|[|n]]; try easy.
   + simpl in *. subst a. now exists [].
   + rewrite seq_S in Ha. simpl "+" in Ha.
     change (k-1::_++[S n]) with ((k-1::seq 0 (S n))++[S n]) in Ha.
     rewrite last_last in Ha. subst a.
     rewrite !seq_S. exists (k-1::seq 0 n). simpl. f_equal.
     now rewrite <- app_assoc.
 - destruct n; try easy. rewrite kword_eqn in * by lia.
   rewrite last_app in Ha.
   2:{ apply kword_nz. }
   destruct (IH (S n-k)) as (u & <-); trivial; try lia.
   exists (kword k n ++ u). fixpred. now rewrite app_assoc.
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

Lemma lemma_4_5 r a b : a<>k-1 -> b<>k-1 ->
  SubSeq ([a] ++ repeat (k-1) r ++ [b]) (kseq k) <->
  (r=0 /\ a = b-1 /\ 0 < b < k-1) \/
  (r=1 /\ a < k-1 /\ b = 0) \/
  (r=2 /\ a = k-2 /\ b = 0).
Proof.
 intros A B. split.
 - rewrite SubSeq_kseq_alt. intros (n,SU). revert SU.
   induction n as [n IH] using lt_wf_ind.
   destruct (Nat.le_gt_cases n (k-1)) as [LE|GT].
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
   + rewrite kword_eqn by lia. intros SU. apply Sub_app_inv in SU.
     destruct SU as [SU|[SU|(u1 & u2 & U1 & U2 & E & SU & PR)]].
     * apply (IH (n-1)); auto. lia.
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
         - assert (PR2 : Prefix [b] [k-1;0]).
           { eapply Prefix_Prefix; simpl; eauto. }
           now destruct PR2 as (v & [= -> _]).
         - clear u2'. destruct PR as (v & PR).
           destruct PR' as (v' & PR').
           rewrite <- PR' in PR. apply app_inv in PR; auto.
           destruct PR as ([= -> ->],_). clear PR'.
           destruct r as [|r]; [now destruct u1| ].
           rewrite <- (Nat.add_1_r r), repeat_app in E. simpl in E.
           apply app_inv' in E; auto. destruct E as (<-,_). clear v v'.
           destruct r as [|[|r]].
           + left; repeat split; auto.
             simpl in SU. destruct SU as (w & SU).
             generalize (kword_letters k (n-1) lia).
             rewrite <- SU, Forall_app.
             intros (_,F). inversion_clear F. lia.
           + right; repeat split; auto.
             simpl in SU.
             destruct SU as (u & SU).
             assert (N' : n-1 <> 0) by lia.
             assert (L : last (kword k (n-1)) 0 = k-1).
             { now rewrite <- SU, last_app. }
             assert (SU' := lemma_4_4 _ (k-1) N' L).
             destruct SU' as (u' & SU'). rewrite <- SU' in SU.
             apply app_inv' in SU; auto. destruct SU as (_,[= ->]).
             unfold prev_letter. case Nat.eqb_spec; lia.
           + exfalso.
             replace (S (S r)) with (r+2) in SU by lia.
             rewrite repeat_app in SU. simpl in SU.
             destruct SU as (u & SU).
             change (a::_ ++ _) with ((a::repeat (k-1) r)++[k-1;k-1]) in SU.
             rewrite app_assoc in SU.
             assert (N' : n-1 <> 0) by lia.
             assert (L : last (kword k (n-1)) 0 = k-1).
             { now rewrite <- SU, last_app. }
             assert (SU' := lemma_4_4 _ (k-1) N' L).
             destruct SU' as (u' & SU'). rewrite <- SU' in SU.
             apply app_inv' in SU; auto. destruct SU as (_,[= E]).
             revert E. unfold prev_letter. case Nat.eqb_spec; lia.
         - exfalso.
           assert (IN : In a (kword k (n-1))).
           { destruct SU as (u & <-). rewrite in_app_iff; right.
             simpl; intuition. }
           assert (LT : a < k-1).
           { generalize (kword_letters k (n-1) lia). rewrite Forall_forall.
             intros F. specialize (F a IN). lia. }
           clear IN.
           assert (PR2 : Prefix [k-1;0] (x::y::u2++[b])).
           { eapply Prefix_Prefix; simpl; eauto; try lia. }
           destruct PR2 as (u & [= <- <- PR2]).
           assert (IN : In 0 (repeat (k-1) r)).
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
   + simpl. apply SubSeq_kseq_alt. exists (k+a+2).
     rewrite kword_eqn by lia.
     assert (E : last (kword k (k+a+2-1)) 0 = a).
     { rewrite WordSuffix.kword_last by trivial.
       replace (k+a+2-1+k-1) with (a+2*k) by lia.
       rewrite Nat.mod_add, Nat.mod_small; lia. }
     change [a;k-1;0] with ([a]++[k-1;0]).
     apply Sub_app.
     * rewrite <- E at 1. apply Suffix_last. apply kword_nz.
     * replace [k-1;0] with (kword k 1).
       2:{ rewrite kword_low; simpl; trivial; lia. }
       apply kword_le_prefix; lia.
   + simpl. apply SubSeq_kseq_alt. exists (k+1).
     rewrite kword_eqn by lia. replace (k+1-1) with k by lia.
     assert (E : last (kword k k) 0 = k-1).
     { rewrite WordSuffix.kword_last by trivial.
       replace (k+k-1) with (k-1+1*k) by lia.
       rewrite Nat.mod_add, Nat.mod_small; lia. }
     change [k-2;k-1;k-1;0] with ([k-2;k-1]++[k-1;0]).
     apply Sub_app.
     * replace (k-2) with (prev_letter k (k-1)).
       apply lemma_4_4; try lia.
       unfold prev_letter. case Nat.eqb_spec; lia.
     * replace [k-1;0] with (kword k 1).
       2:{ rewrite kword_low; simpl; trivial; lia. }
       apply kword_le_prefix; lia.
Qed.

Lemma infinitly_many_0_letters :
 forall n, { m | n <= m /\ kseq k m = 0 }.
Proof.
 intros n.
 destruct (Nat.eq_dec k 1) as [->|K'].
 - exists n. split; trivial. now rewrite kseq_01.
 - set (p := invA_up k n).
   exists (S (Nat.max (k+1) (A k p))). split.
   + generalize (invA_up_spec k n). unfold p. lia.
   + apply Nat.max_case_strong; intros LE.
     * rewrite kseq_bounded_rank. unfold bounded_rank, rank.
       rewrite decomp_S by trivial.
       replace (decomp k (k+1)) with [k].
       2:{ symmetry. apply decomp_carac; trivial.
           - constructor.
           - replace (k+1) with (S k) by lia.
             rewrite <- (@A_base k k) by lia. simpl; lia. }
       unfold next_decomp. case Nat.ltb_spec; simpl; lia.
     * rewrite kseq_bounded_rank. unfold bounded_rank, rank.
       replace (decomp k (S (A k p))) with [0;p]; trivial.
       symmetry. apply decomp_carac; simpl; try lia.
       constructor. 2:constructor. simpl. apply (A_le_inv k).
       rewrite A_base; lia.
Qed.

Lemma lemma_4_5_bis r a :
  k<>1 -> a<>k-1 -> SubSeq ([a] ++ repeat (k-1) r) (kseq k) -> r <= 2.
Proof.
 intros K' A (p,E).
 rewrite app_length, repeat_length in E. simpl in E.
 destruct (infinitly_many_0_letters (p+S r)) as (n,(N,N')).
 remember (n-(p+S r)) as m eqn:M.
 revert r E N N' M.
 induction m; intros.
 - replace n with (p+S r) in N' by lia.
   assert (SU : SubSeq ([a] ++ repeat (k-1) r ++ [0]) (kseq k)).
   { exists p. rewrite !app_length, repeat_length, Nat.add_1_r. simpl.
     unfold subseq in *. now rewrite seq_S, map_app, <- E, <- N'. }
   apply lemma_4_5 in SU; trivial; lia.
 - destruct (Nat.eq_dec (kseq k (p+S r)) (k-1)) as [E'|E'].
   + assert (S r <= 2); try lia.
     apply IHm; try lia. clear IHm.
     rewrite <- (Nat.add_1_r r), repeat_app at 1. simpl.
     unfold subseq in *. rewrite seq_S, map_app, <- E. simpl.
     now do 3 f_equal.
   + set (b := kseq k (p+S r)) in *.
     assert (SU : SubSeq ([a] ++ repeat (k-1) r ++ [b]) (kseq k)).
     { exists p. rewrite !app_length, repeat_length, Nat.add_1_r. simpl.
       unfold subseq in *. now rewrite seq_S, map_app, <- E. }
     apply lemma_4_5 in SU; trivial; lia.
Qed.

Lemma lemma_4_5_ter r : k<>1 -> SubSeq (repeat (k-1) r) (kseq k) -> r <= 2.
Proof.
 intros K' (p,E). rewrite repeat_length in E. revert r E.
 induction p; intros.
 - unfold subseq in E. destruct r as [|[|r]]; try lia.
   simpl in E. rewrite kseq_k_1 in E. injection E as [= E _]. lia.
 - destruct (Nat.eq_dec (kseq k p) (k-1)) as [E'|E'].
   + assert (S r <= 2); try lia.
     { apply IHp. unfold subseq in *. simpl. now rewrite E', E. }
   + eapply lemma_4_5_bis; eauto. exists p.
     rewrite app_length, repeat_length. simpl. now rewrite E.
Qed.

Lemma lemma_4_5_km1km1 a b :
 SubSeq [a;k-1;k-1;b] (kseq k) -> a = k-2 /\ b = 0.
Proof.
 intros SU.
 destruct (Nat.eq_dec k 1) as [->|K'].
 { simpl. destruct SU as (q & SU). unfold subseq in SU. simpl in SU.
   injection SU as E1 _ _ E2. now rewrite kseq_01 in E1,E2. }
 destruct (Nat.eq_dec a (k-1)) as [->|A].
 { exfalso.
   assert (SU' : SubSeq (repeat (k-1) 3) (kseq k)).
   { eapply Sub_SubSeq; eauto. now exists [], [b]. }
   apply lemma_4_5_ter in SU'; lia. }
 destruct (Nat.eq_dec b (k-1)) as [->|B].
 { exfalso.
   assert (SU' : SubSeq (repeat (k-1) 3) (kseq k)).
   { eapply Sub_SubSeq; eauto. now exists [a], []. }
   apply lemma_4_5_ter in SU'; lia. }
 rewrite (lemma_4_5 2 a b) in SU; lia.
Qed.

Lemma lemma_4_5_km1km1' a : SubSeq [k-1;k-1;a] (kseq k) -> a = 0.
Proof.
 intros ([|p],SU).
 - unfold subseq in SU. simpl in SU. injection SU as E1 E2.
   rewrite kseq_k_1 in E1. rewrite kseq_01 in E2; lia.
 - assert (SU' : SubSeq [kseq k p; k-1; k-1; a] (kseq k)).
   { exists p. unfold subseq in *. simpl in *. now f_equal. }
   apply lemma_4_5_km1km1 in SU'. lia.
Qed.

Lemma lemma_4_5_km10 a b : SubSeq [a;k-1;b] (kseq k) -> a <> k-2 -> b = 0.
Proof.
 intros SU N.
 destruct (Nat.eq_dec a (k-1)) as [->|A].
 - eapply lemma_4_5_km1km1'; eauto.
 - destruct (SubSeq_RightExt _ _ SU) as (c, SU').
   destruct (Nat.eq_dec b (k-1)) as [->|B].
   + apply lemma_4_5_km1km1 in SU'. lia.
   + apply (lemma_4_5 1 a b) in SU; lia.
Qed.

Lemma RS_aq u a : RightSpecial (u ++ [a;k-1]) (kseq k) -> a = k-2.
Proof.
 intros RS.
 eapply RightSpecial_Suffix in RS; [|now exists u].
 destruct RS as (b & c & BC & B & C).
 destruct (Nat.eq_dec a (k-2)) as [E|N]; try easy.
 apply lemma_4_5_km10 in B, C; trivial. lia.
Qed.

Lemma corollary_4_6_aux r : k<>1 -> 2 <= r ->
  ~RightSpecial (repeat (k-1) r) (kseq k).
Proof.
 intros K' R RS.
 apply RightSpecial_Suffix with (u:=[k-1;k-1]) in RS.
 - destruct RS as (a & b & AB & A & B). apply lemma_4_5_km1km1' in A, B. lia.
 - exists (repeat (k-1) (r-2)). change [k-1;k-1] with (repeat (k-1) 2).
   rewrite <- repeat_app. f_equal; lia.
Qed.

Lemma corollary_4_6 u r : k<>1 -> 2 <= r ->
  ~RightSpecial (u++repeat (k-1) r) (kseq k).
Proof.
 intros K' R RS. apply (corollary_4_6_aux r K' R).
 eapply RightSpecial_Suffix; eauto. now exists u.
Qed.

Lemma lemma_4_7 r : ~MaxLeftSpecial (repeat (k-1) r) (kseq k).
Proof.
 destruct (Nat.eq_dec (k-1) 0) as [K'|K'].
 { intros ((a & b & AB & A & B),_). rewrite K' in *.
   apply LeftExt_letter in A, B. lia. }
 intros (LS,NLS).
 assert (SU : SubSeq (repeat (k-1) r) (kseq k)).
 { destruct LS as (a & b & AB & A & B).
   red in A. eapply Sub_SubSeq; eauto using Sub_cons_r. }
 apply lemma_4_5_ter in SU; try lia.
 destruct r as [|[|r]]; simpl in *.
 - apply (NLS (k-1)). apply ls_val. rewrite klvalence_letter_km1. lia.
 - apply (NLS 0). apply ls_val.
   assert (E : [k-1;0] = kprefix k 2).
   { cbn. now rewrite ksubst_km1. }
   rewrite E, kprefix_klvalence. lia.
 - replace r with 0 in * by lia. simpl in *. clear NLS SU.
   destruct LS as (a & b & AB & A & B).
   destruct (Nat.eq_dec a (k-1)) as [->|A'].
   { unfold LeftExt in A. apply (lemma_4_5_ter 3) in A; lia. }
   destruct (SubSeq_RightExt _ _ A) as (c & AR).
   destruct (Nat.eq_dec c (k-1)) as [->|C].
   { apply (lemma_4_5_bis 3 a) in AR; trivial; lia. }
   apply (lemma_4_5 2 a c) in AR; trivial.
   destruct (Nat.eq_dec b (k-1)) as [->|B'].
   { unfold LeftExt in B. apply (lemma_4_5_ter 3) in B; lia. }
   destruct (SubSeq_RightExt _ _ B) as (d & BR).
   destruct (Nat.eq_dec d (k-1)) as [->|D].
   { apply (lemma_4_5_bis 3 b) in BR; trivial; lia. }
   apply (lemma_4_5 2 b d) in BR; trivial.
   lia.
Qed.

Lemma SubSeq_km1km1 u :
  SubSeq (u++[k-1;k-1]) (kseq k) -> SubSeq (u++[k-1;k-1;0]) (kseq k).
Proof.
 intros (p,SU).
 assert (SU' : SubSeq (u++[k-1;k-1;kseq k (p + length u + 2)]) (kseq k)).
 { exists p. unfold subseq in *; rewrite app_length in *. simpl in *.
   rewrite (Nat.add_succ_r (length u)), seq_S, map_app, <- SU.
   rewrite <- app_assoc. simpl. do 5 f_equal. lia. }
 set (n := p + _ + 2) in *.
 replace (kseq k n) with 0 in *; trivial.
 symmetry. apply lemma_4_5_km1km1'. eapply Sub_SubSeq; eauto.
 apply Sub_app_l, Sub_id.
Qed.

Lemma LeftSpecial_km1km1 u :
  LeftSpecial (u++[k-1;k-1]) (kseq k) -> LeftSpecial (u++[k-1;k-1;0]) (kseq k).
Proof.
 intros (a & b & AB & A & B). exists a, b. split; trivial. split.
 apply (SubSeq_km1km1 (a::u)), A.
 apply (SubSeq_km1km1 (b::u)), B.
Qed.

Lemma lemma_4_9 u :
  SubSeq (u++[k-2]) (kseq k) -> SubSeq (u++[k-2;k-1]) (kseq k).
Proof.
 intros (p,E). exists p. rewrite app_length in *.
 unfold subseq in *. simpl in *.
 rewrite !Nat.add_succ_r, !seq_S, !map_app in *. simpl in *.
 set (n := length u) in *. rewrite Nat.add_0_r in *.
 apply app_inv' in E; trivial. destruct E as (<-,[= E]).
 now rewrite Nat.add_succ_r, kseq_next_km2, <- E, <- app_assoc.
Qed.

Lemma lemma_4_9_ls u :
  LeftSpecial (u++[k-2]) (kseq k) -> LeftSpecial (u++[k-2;k-1]) (kseq k).
Proof.
 intros (a & b & AB & A & B). exists a, b; repeat split; trivial.
 now apply (lemma_4_9 (a::u)).
 now apply (lemma_4_9 (b::u)).
Qed.

Lemma kseq_after_km1 a : SubSeq [k-1;a] (kseq k) -> a = 0 \/ a = k-1.
Proof.
 intros (p,SU). unfold subseq in *. simpl in *. injection SU as E1 E2.
 generalize (kseq_next_letter k p).
 rewrite <- E2, <- E1, next_letter_km1. lia.
Qed.

Lemma kword_kp1 : kword k (k+1) = kword k (k-1) ++ [k-1;k-1;0].
Proof.
 rewrite (kword_eqn k (k+1)) by lia.
 replace (k+1-1) with k by lia. replace (k+1-k) with 1 by lia.
 rewrite (kword_eqn k k) by lia. rewrite Nat.sub_diag.
 rewrite <- app_assoc. f_equal. cbn. now rewrite ksubst_km1.
Qed.

Lemma krvalence_letter_km1 : k<>1 -> krvalence [k-1] = 2.
Proof.
 intros K'.
 unfold krvalence. change 2 with (length [0; k-1]).
 eapply Permutation_length, AllRightExts_unique; eauto using krightexts_ok.
 split.
 - repeat constructor; simpl; lia.
 - intros a. simpl. intuition; try subst a.
   + exists 0. cbn. now rewrite ksubst_km1.
   + apply SubSeq_kseq_alt. exists (k+1). rewrite kword_kp1.
     apply Sub_app_l. now exists [],[0].
   + apply kseq_after_km1 in H. intuition.
Qed.

Lemma krvalence_low_letter a : a<k-2 -> krvalence [a] = 2.
Proof.
 intros K'.
 unfold krvalence. change 2 with (length [S a; k-1]).
 eapply Permutation_length, AllRightExts_unique; eauto using krightexts_ok.
 split.
 - repeat constructor; simpl; intuition. lia.
 - intros b. simpl. intuition; try subst b.
   + exists (S a). unfold subseq. simpl.
     now rewrite !all_letters_occur by lia.
   + red. simpl.
     assert (SubSeq [a;k-1;0] (kseq k)) by (apply (lemma_4_5 1); lia).
     eapply Sub_SubSeq; eauto. now exists [], [0].
   + red in H. simpl in H.
     destruct (Nat.eq_dec (k-1) b) as [->|N]. intuition.
     apply (lemma_4_5 0) in H; lia.
Qed.

(** Instead of proposition 3.8 and theorem 3.9 about Infinite Left Special,
    we use here an ad-hoc decreasing principle, that avoid the need for
    infinitary objects (delicate in Coq). Moreover, it explicits the fact
    that we may need to right-extend LeftSpecial words, but at most once. *)

Lemma DecrLemma u :
  1 < length u ->
  LeftSpecial u (kseq k) ->
  (last u 0 = k-1 -> exists x, LeftSpecial (u++[x]) (kseq k)) ->
  exists v w,
    LeftSpecial v (kseq k) /\
    (w=[]\/w=[0]) /\
    ksubstw k v = u++w /\
    length v < length u.
Proof.
 intros U LS LS'.
 assert (K' := ls_kgt1 _ LS).
 destruct (Nat.eq_dec (last u 0) (k-1)) as [L|N].
 - specialize (LS' L). destruct LS' as (x & LS'). clear LS.
   assert (U' : u <> []) by now intros ->.
   assert (E := app_removelast_last 0 U').
   rewrite L in E.
   set (u' := removelast u) in *. clearbody u'. subst u. clear L U'.
   rewrite app_length in U. simpl in U. rewrite Nat.add_1_r in U.
   rewrite <- app_assoc in LS'. simpl in LS'.
   destruct (Nat.eq_dec x (k-1)) as [->|N'].
   + destruct (lemma_3_7_ii_ls (u'++[k-1;k-1;0])) as (v & V & V').
     { rewrite last_app; simpl. lia. easy. }
     { now apply LeftSpecial_km1km1. }
     assert (N : v <> []).
     { intros ->. simpl in V. now destruct u'. }
     assert (E := app_removelast_last 0 N).
     set (v' := @removelast nat v) in *. clearbody v'.
     rewrite E in V. rewrite ksubstw_app in V.
     revert V. simpl. rewrite app_nil_r.
     unfold ksubst. case Nat.eqb_spec.
     2:{ change [k-1;k-1;0] with ([k-1;k-1]++[0]).
         rewrite app_assoc. intros _ V. apply app_inv' in V; easy. }
     change [k-1;k-1;0] with ([k-1]++[k-1;0]); rewrite app_assoc.
     intros E' V. rewrite E' in E. clear E'.
     apply app_inv' in V; simpl; trivial. destruct V as (V,_).
     exists v', []; repeat split; trivial.
     * rewrite E in V'. eapply LeftSpecial_Prefix; eauto.
       now exists [k-1].
     * now left.
     * now rewrite app_nil_r.
     * rewrite <- V. rewrite len_ksubst.
       destruct v' as [|a v']; [now destruct u'|].
       rewrite E in V'. simpl in V'. apply ls_head_km1 in V'. subst a.
       simpl in *. rewrite Nat.eqb_refl. lia.
   + destruct (kseq_after_km1 x) as [-> | ->]; try lia.
     { apply LeftSpecial_SubSeq in LS'. eapply Sub_SubSeq; eauto.
       apply Sub_app_l, Sub_id. }
     clear N'.
     destruct (lemma_3_7_ii_ls (u'++[k-1;0])) as (v & V & V'); trivial.
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
       2:{ change [k-1;0] with ([k-1]++[0]).
           rewrite app_assoc. intros _ V. apply app_inv' in V; easy. }
       intros E2 V. rewrite E2 in E'. clear E2.
       apply app_inv' in V; simpl; trivial. destruct V as (V,_).
       assert (2 <= nbocc (k-1) v); try lia.
       { rewrite E'. rewrite nbocc_app. simpl. rewrite Nat.eqb_refl.
         destruct v' as [|a v']; simpl in *. now subst u'.
         rewrite E' in V'. apply ls_head_km1 in V'. subst a.
         rewrite Nat.eqb_refl. lia. }
 - clear LS'.
   destruct (lemma_3_7_ii_ls u) as (v & V & V'); trivial.
   exists v, []; repeat split; trivial.
   + now left.
   + now rewrite app_nil_r.
   + rewrite <- V, len_ksubst.
     destruct v as [|a v]; simpl in *. now subst u.
     apply ls_head_km1 in V'. subst a. rewrite Nat.eqb_refl. lia.
Qed.

(** Turn the lack of MaxLeftSpecial into a positive fact about LeftSpecial. *)

Lemma NoMaxLS_exists u :
  LeftSpecial u (kseq k) ->
  ~MaxLeftSpecial u (kseq k) ->
  exists a, LeftSpecial (u++[a]) (kseq k).
Proof.
 intros LS NM.
 set (l := seq 0 k).
 destruct (existsb (fun a => Nat.leb 2 (klvalence (u++[a]))) l) eqn:E.
 - rewrite existsb_exists in E.
   destruct E as (a & IN & LS'). exists a. now apply ls_val, Nat.leb_le.
 - exfalso. apply NM. split; trivial. intros a LS'.
   assert (a < k).
   { apply all_letters_subseq. apply LeftSpecial_SubSeq in LS'.
     eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
   apply ls_val, Nat.leb_le in LS'.
   rewrite <- not_true_iff_false, existsb_exists in E. apply E. clear E.
   exists a; split; trivial. apply in_seq. lia.
Qed.

(* Two auxiliary lemmas for Proposition 4.10 : ante-image of right
   extensions *)

Lemma inv_letter_for_4_10 u v' b :
  MaxLeftSpecial u (kseq k) -> last u 0 <> k-1 -> ksubstw k v' = u ->
  RightExt u b (kseq k) ->
  exists b', RightExt v' b' (kseq k) /\ ~LeftSpecial (v'++[b']) (kseq k) /\
             head (ksubst k b') = Some b.
Proof.
 intros (LS,NLS) L E B.
 assert (K' : 1<k) by now apply ls_kgt1 in LS.
 assert (U : u<>[]). { intros ->. now apply (lemma_4_7 0). }
 destruct (Nat.eq_dec b (k-1)) as [->|NB].
 - destruct (SubSeq_RightExt _ _ B) as (b2 & B2).
   red in B2. rewrite <- app_assoc in B2. simpl in B2.
   assert (B2' : SubSeq [k-1;b2] (kseq k)).
   { eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
   destruct (kseq_after_km1 _ B2') as [-> | ->].
   + destruct (lemma_3_7_ii_cor (u++[k-1;0])) as (v & V & SU); trivial.
     { destruct u; simpl; try easy. apply ls_head_km1 in LS; lia. }
     { rewrite last_app; simpl; easy || lia. }
     assert (E2 : v = v' ++ [k-1]).
     { apply (ksubstw_inv k). rewrite ksubstw_app, V, E. f_equal.
       cbn. now rewrite ksubst_km1. }
     exists (k-1); repeat split.
     { red. now rewrite <- E2. }
     { rewrite <- E2. intro LS3.
       apply lemma_3_7_i_ls in LS3. rewrite V in LS3.
       apply (NLS (k-1)).
       eapply LeftSpecial_Prefix; eauto.
       exists [0]. now rewrite <- app_assoc. }
     { now rewrite ksubst_km1. }
   + destruct (SubSeq_RightExt _ _ B2) as (b3 & B3).
     red in B3. rewrite <- app_assoc in B3. simpl in B3.
     assert (B3' : SubSeq [k-1;k-1;b3] (kseq k)).
     { eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
     rewrite (lemma_4_5_km1km1' _ B3') in *.
     destruct (lemma_3_7_ii_cor (u++[k-1;k-1;0])) as (v & V & SU); trivial.
     { destruct u; simpl; try easy. apply ls_head_km1 in LS; lia. }
     { rewrite last_app; simpl; easy || lia. }
     assert (E2 : v = v' ++ [k-2;k-1]).
     { apply (ksubstw_inv k). rewrite ksubstw_app, V, E. f_equal.
       cbn. now rewrite ksubst_km2, ksubst_km1 by trivial. }
     exists (k-2); repeat split; rewrite ?ksubst_km2 in *; trivial.
     { red. apply Sub_SubSeq with v; auto. subst v.
       exists [], [k-1]. now rewrite <- !app_assoc. }
     { intro LS3. apply lemma_3_7_i_ls in LS3.
       rewrite ksubstw_app, E in LS3. simpl in LS3.
       rewrite app_nil_r in LS3. rewrite ksubst_km2 in LS3 by trivial.
       now apply NLS in LS3. }
 - assert (b<>0).
   { intros ->.
     red in B.
     rewrite (app_removelast_last 0 U), <- app_assoc in B.
     simpl in B.
     eapply Sub_SubSeq in B; [|apply Sub_app_l, Sub_id].
     apply letters_RightExt in B. destruct B as [B|B]; try lia.
     revert B. unfold next_letter in *. case Nat.eqb_spec; lia. }
   destruct (lemma_3_7_ii_cor (u++[b])) as (v & V & SU); trivial.
   { destruct u as [|x u]; simpl; try easy. apply ls_head_km1 in LS.
     subst x; lia. }
   { now rewrite last_last. }
   assert (b <= k-1).
   { eapply Sub_SubSeq in B; [|apply Sub_app_l, Sub_id].
     apply all_letters_subseq in B. lia. }
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

Lemma inv_letter_bis_for_4_10 u v' b :
  MaxLeftSpecial (u++[k-1]) (kseq k) -> ksubstw k v' = u ->
  RightExt (u++[k-1]) b (kseq k) ->
  exists b', RightExt v' b' (kseq k) /\ ~LeftSpecial (v'++[b']) (kseq k) /\
             ((b = k-1 /\ b' = k-2) \/ (b = 0 /\ b' = k-1)).
Proof.
 intros (LS,NLS) E B.
 assert (K' : 1<k) by now apply ls_kgt1 in LS.
 assert (U : u<>[]). { intros ->. now apply (lemma_4_7 1). }
 destruct (kseq_after_km1 b) as [-> | ->].
 { red in B. rewrite <- app_assoc in B. simpl in B.
   eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
 - exists (k-1).
   destruct (lemma_3_7_ii_cor (u++[k-1;0])) as (v & V & SU); trivial.
   { destruct u; simpl; try easy. apply ls_head_km1 in LS; lia. }
   { rewrite last_app; simpl; easy || lia. }
   { red in B. now rewrite <- app_assoc in B. }
   replace v with (v' ++ [k-1]) in *.
   2:{ apply (ksubstw_inv k). rewrite ksubstw_app, V, E. f_equal.
       cbn. now rewrite ksubst_km1. }
   repeat split; trivial; [|now right].
   intros LS'. apply lemma_3_7_i_ls in LS'.
   rewrite V in LS'. apply (NLS 0). now rewrite <- !app_assoc.
 - exists (k-2).
   destruct (SubSeq_RightExt _ _ B) as (b2 & B2).
   red in B2. rewrite <- !app_assoc in B2. simpl in B2.
   assert (B2' : SubSeq [k-1;k-1;b2] (kseq k)).
   { eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
   apply lemma_4_5_km1km1' in B2'. subst b2.
   destruct (lemma_3_7_ii_cor (u++[k-1;k-1;0])) as (v & V & SU); trivial.
   { destruct u; simpl; try easy. apply ls_head_km1 in LS; lia. }
   { rewrite last_app; simpl; easy || lia. }
   replace v with (v' ++ [k-2;k-1]) in *.
   2:{ apply (ksubstw_inv k). rewrite ksubstw_app, V, E. f_equal.
     cbn. now rewrite ksubst_km1, ksubst_km2. }
   repeat split; try now left.
   { eapply Sub_SubSeq; eauto.
     exists [], [k-1]. now rewrite <- app_assoc. }
   { intros LS'. apply lemma_4_9_ls in LS'. apply lemma_3_7_i_ls in LS'.
     rewrite V in LS'. apply (NLS (k-1)).
     eapply LeftSpecial_Prefix; eauto. exists [0].
     now rewrite <- !app_assoc. }
Qed.

(** Proposition 4.10 as proved in Corrigendum (as Proposition 2.2).
    Some parts of the proofs were unecessary here :
    - We are here in the case "t_1 > max(t_2...t_{m-1})" (t_1=t_m=1>0=t_i).
    - The last paragraph is skipped since factors of (kseq k) cannot
      have a right valence of 3>2.

    Moreover, this proof of proposition 4.10 is left here for completeness
    reasons, but a shorter approach is also possible (and was used in a
    former version of this work) : just prove that v is LeftSpecial
    instead of MaxLeftSpecial, and moreover that
      [w=[k-1] -> ~RightSpecial (ksubstw k v) (kseq k)].
    This is enough for completing [LeftSpecial_kprefix] below, and then
    proving ~MaxLeftSpecial afterwards. *)

Lemma proposition_4_10 u x :
  MaxLeftSpecial u (kseq k) -> x<>k-1 -> In x u ->
  exists v w,
    MaxLeftSpecial v (kseq k) /\ u = ksubstw k v ++ w /\ (w=[] \/ w = [k-1]).
Proof.
 destruct (Nat.eq_dec k 1) as [K'|K'].
 { intros ((b & c & BC & B & C),_). apply LeftExt_letter in B, C. lia. }
 intros (LS,NLS) X IN.
 assert (E : exists u' r, u = u' ++ repeat (k-1) r /\
                          last u' 0 <> k-1 /\ (r=0\/r=1)).
 { destruct (Nat.eq_dec (last u 0) (k-1)) as [E|N].
   - assert (N : u <> []) by (intros ->; inversion IN).
     assert (U' := app_removelast_last 0 N).
     set (u' := removelast u) in *. clearbody u'. rewrite E in *. clear N E.
     exists u', 1; repeat split; trivial; try now right. intros E'.
     assert (N' : u' <> []). { intros ->. simpl in *. apply K'. lia. }
     rewrite (app_removelast_last 0 N'), E', <- app_assoc in U'. simpl in U'.
     clear E' N'.
     eapply (corollary_4_6 _ 2); trivial.
     apply observation_4_2_contra. simpl. rewrite <- U'. split; trivial.
   - exists u, 0; repeat split; trivial; try now left. simpl.
     now rewrite app_nil_r. }
 destruct E as (u' & r & E & L & R).
 assert (LS' : LeftSpecial u' (kseq k)).
 { eapply LeftSpecial_Prefix; eauto. now exists (repeat (k-1) r). }
 assert (U' : u' <> []).
 { intros ->. simpl in *. subst u. apply repeat_spec in IN; lia. }
 clear x X IN.
 destruct (lemma_3_7_ii_ls u' L LS') as (v' & V1 & V2).
 exists v', (repeat (k-1) r); repeat split; trivial; try congruence.
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
   - destruct (inv_letter_for_4_10 u' v' b) as (b' & B1 & B2 & B3);
     destruct (inv_letter_for_4_10 u' v' c) as (c' & C1 & C2 & C3);
       try split; trivial.
     exists b', c'; repeat split; trivial; congruence.
   - destruct (inv_letter_bis_for_4_10 u' v' b) as (b' & B1 & B2 & B3);
     destruct (inv_letter_bis_for_4_10 u' v' c) as (c' & C1 & C2 & C3);
       try split; trivial.
     exists b',c'; repeat split; trivial; lia. }
 clear b c BC B B' C C'.
 destruct E' as (b & c & BC & B & B' & C & C').
 assert (AB : a <> b). { intros ->. now apply B'. }
 assert (AC : a <> c). { intros ->. now apply C'. }
 assert (3 <= krvalence v').
 { apply LeftSpecial_SubSeq in A.
   change 3 with (length [a;b;c]).
   apply NoDup_incl_length.
   - clear -AB AC BC. repeat constructor; simpl; intuition.
   - destruct (krightexts_ok v') as (_,RE). clear - A B C RE.
     intros x X. simpl in X. intuition; subst x; rewrite RE; auto. }
 assert (krvalence v' <= 2).
 { apply krvalence_le_2. intros ->. simpl in *. now subst. }
 lia.
Qed.

Lemma norepeat_exists (q:nat) u :
  u <> repeat (k-1) (length u) -> exists a, a<>k-1 /\ In a u.
Proof.
 induction u as [|a u IH]; simpl; intros N; try easy.
 destruct (Nat.eq_dec a (k-1)) as [->|N']; [|exists a; tauto].
 destruct IH as (a & A & IN).
 { contradict N. now f_equal. }
 exists a; tauto.
Qed.

Lemma corollary_4_11 u : ~MaxLeftSpecial u (kseq k).
Proof.
 remember (length u) as n eqn:N. symmetry in N. revert u N.
 induction n as [n IH] using lt_wf_ind. intros u N LS.
 destruct (norepeat_exists k u) as (x & X & IN); trivial.
 { rewrite N. intros ->. now apply (lemma_4_7 n). }
 destruct (proposition_4_10 u x) as (v & w & V & E & W); trivial.
 assert (L : length v < n).
 { rewrite <- N, E, app_length, len_ksubst.
   destruct V as (V,_). destruct v.
   - simpl in *. intuition; subst; simpl. inversion IN. lia.
   - apply ls_head_km1 in V. subst. simpl. rewrite Nat.eqb_refl. lia. }
 apply (IH (length v) L v); auto.
Qed.

(** Major property : the only LeftSpecial factors of (kseq k) are
    its prefixes. *)

Lemma LeftSpecial_kprefix u :
  LeftSpecial u (kseq k) -> PrefixSeq u (kseq k).
Proof.
 remember (length u) as n eqn:N. revert u N.
 induction n as [n IH] using lt_wf_ind. intros u N LS.
 destruct (Nat.eq_dec n 0) as [->|N0].
 { now destruct u. }
 destruct (Nat.eq_dec n 1) as [->|N1].
 { destruct u as [|a [|b u]]; try easy. apply ls_head_km1 in LS. now subst a. }
 destruct (DecrLemma u) as (v & w & V & W & E' & L); lia||auto.
 - intros _. apply NoMaxLS_exists; trivial. apply corollary_4_11.
 - rewrite <- N in L.
   specialize (IH _ L v eq_refl V). apply ksubstw_prefix in IH.
   rewrite E' in IH. eapply Prefix_PrefixSeq; eauto. now exists w.
Qed.

Lemma LeftSpecial_carac u : k<>1 ->
  LeftSpecial u (kseq k) <-> PrefixSeq u (kseq k).
Proof.
 intros K'. split.
 - apply LeftSpecial_kprefix.
 - intros P. rewrite P. fold (kprefix k (length u)).
   apply ls_val. rewrite kprefix_klvalence. lia.
Qed.

Lemma LeftSpecial_carac' u : k<>1 ->
  LeftSpecial u (kseq k) <-> u = kprefix k (length u).
Proof.
 intros K'. now rewrite LeftSpecial_carac.
Qed.

(** Some leftover proofs that could only be obtained now : *)

Lemma ls_val_k u : LeftSpecial u (kseq k) -> klvalence u = k.
Proof.
 intros LS.
 assert (K' := ls_kgt1 _ LS).
 apply LeftSpecial_carac' in LS; try lia. rewrite LS.
 apply kprefix_klvalence.
Qed.

Lemma lemma_3_7_i_ls_val u :
  LeftSpecial u (kseq k) -> klvalence (ksubstw k u) = klvalence u.
Proof.
 intros LS. rewrite (ls_val_k _ LS).
 now apply ls_val_k, lemma_3_7_i_ls.
Qed.

Lemma klvalence_1_or_k u :
  SubSeq u (kseq k) -> klvalence u = 1 \/ klvalence u = k.
Proof.
 intros SU. apply klvalence_nz in SU.
 destruct (Nat.eq_dec (klvalence u) 1) as [E|N].
 - now left.
 - right. apply ls_val_k, ls_val. lia.
Qed.


(** Now that we have a unique LeftSpecial per length,
    application to factor counting and complexity. *)

Definition next_kfactors p :=
  let f := kprefix k p in
  let l := filter (fun u => negb (listnat_eqb u f)) (kfactors k p) in
  take k (fun x => x::f) ++
  map (fun u => hd 0 (kleftexts u) :: u) l.

Lemma next_kfactors_iff p u : k<>1 ->
  In u (next_kfactors p) <-> In u (kfactors k (S p)).
Proof.
 intros K'.
 split.
 - rewrite kfactors_in; trivial.
   unfold next_kfactors.
   rewrite in_app_iff, in_take, in_map_iff.
   intros [(x & <- & IN)|(v & E & IN)].
   + split.
     * simpl. f_equal. apply kprefix_length.
     * destruct (kprefix_allleftexts p) as (_,H). apply H.
       rewrite in_seq; lia.
   + rewrite filter_In in IN. destruct IN as (IN,E').
     revert E'. case listnat_eqb_spec; intros; try easy. clear E'.
     rewrite kfactors_in in IN; trivial. destruct IN as (L,IN).
     assert (NLS : ~LeftSpecial v (kseq k)).
     { now rewrite LeftSpecial_carac', L. }
     rewrite ls_val in NLS.
     assert (N := klvalence_nz v IN).
     assert (E' : klvalence v = 1) by lia. clear NLS N.
     unfold klvalence in E'.
     destruct (kleftexts_ok v) as (_,LE).
     destruct (kleftexts v) as [|a [|b l]]; simpl in *; try easy.
     rewrite <- E.
     split.
     * simpl. now f_equal.
     * apply LE. now left.
 - rewrite kfactors_in; trivial. intros (L,IN).
   unfold next_kfactors. rewrite in_app_iff, in_take, in_map_iff.
   destruct u as [|a u]; try easy. simpl in L. injection L as L.
   destruct (listnat_eqb_spec u (kprefix k p)) as [->|N].
   + left. exists a; split; trivial.
     apply LeftExt_letter in IN. lia.
   + right. exists u; split; trivial.
     * f_equal.
       assert (NLS : ~LeftSpecial u (kseq k)).
       { now rewrite LeftSpecial_carac', L. }
       rewrite ls_val in NLS.
       assert (SU : SubSeq u (kseq k)).
       { eapply Sub_SubSeq; eauto. apply Sub_cons_r. }
       assert (N' := klvalence_nz u SU).
       assert (E : klvalence u = 1) by lia. clear NLS N'.
       unfold klvalence in E.
       destruct (kleftexts_ok u) as (_,LE).
       rewrite <- (LE a) in IN. clear LE.
       destruct (kleftexts u) as [|b [|c ]]; simpl in *; try easy.
       intuition.
     * apply filter_In. split.
       { rewrite kfactors_in; trivial. split; trivial.
         eapply Sub_SubSeq; eauto. apply Sub_cons_r. }
       { now case listnat_eqb_spec. }
Qed.

Lemma next_kfactors_nodup p : NoDup (next_kfactors p).
Proof.
 apply app_nodup.
 - apply FinFun.Injective_map_NoDup; try apply seq_NoDup.
   now injection 1.
 - apply FinFun.Injective_map_NoDup.
   + now injection 1.
   + apply NoDup_filter, kfactors_nodup.
 - intros x. rewrite in_take, in_map_iff.
   intros ((a & <- & LT),(u & E & IN')).
   rewrite filter_In in IN'. destruct IN' as (IN',E').
   injection E as E1 E2.
   revert E'. now case listnat_eqb_spec.
Qed.

Lemma next_kfactors_ok p : k<>1 ->
  Permutation (next_kfactors p) (kfactors k (S p)).
Proof.
 intros K'.
 apply NoDup_Permutation.
 - apply next_kfactors_nodup.
 - apply kfactors_nodup.
 - intros u. now apply next_kfactors_iff.
Qed.

Lemma next_kfactor_length p : k<>1 ->
 length (next_kfactors p) = length (kfactors k p) + k-1.
Proof.
 intros K'.
 unfold next_kfactors. rewrite app_length, take_length, map_length.
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
   + rewrite kfactors_in; trivial. split. now rewrite kprefix_length.
     eapply Sub_SubSeq. 2:apply (kprefix_leftext p 0); try lia.
     apply Sub_cons_r.
   + unfold f. now case listnat_eqb_spec.
 - intros u. rewrite filter_In. unfold f.
   case listnat_eqb_spec.
   + intros ->. simpl. now left.
   + intros _ (_,[=]).
Qed.

Lemma kfactors_length p : length (kfactors k p) = (k-1)*p+1.
Proof.
 destruct (Nat.eq_dec k 1) as [->|Q].
 { now rewrite kfactors_1_l. }
 induction p.
 - rewrite kfactors_0_r. simpl. lia.
 - assert (E := next_kfactors_ok p).
   apply Permutation_length in E; trivial.
   rewrite <- E, next_kfactor_length, IHp; lia.
Qed.

End Knonzero.

Lemma kseq_complexity k p : k<>0 -> Complexity (kseq k) p ((k-1)*p+1).
Proof.
 intros K. exists (kfactors k p). split; [|split].
 - apply kfactors_nodup.
 - now apply kfactors_length.
 - intros u. now apply kfactors_in.
Qed.

(* Print Assumptions kseq_complexity. *)
