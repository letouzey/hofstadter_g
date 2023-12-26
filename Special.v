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

Definition AllLeftExts l u (f:sequence) :=
  NoDup l /\ forall a, In a l <-> LeftExt a u f.

Lemma AllLeftExts_unique l l' u f :
 AllLeftExts l u f -> AllLeftExts l' u f -> Permutation l l'.
Proof.
 intros (ND,IN) (ND',IN').
 apply NoDup_Permutation; trivial.
 intros. now rewrite IN, IN'.
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

Lemma klvalence_ok k l u :
  AllLeftExts l u (kseq k) -> klvalence k u = length l.
Proof.
 intros A. rewrite (@Permutation_length _ l (kleftexts k u)); try easy.
 eapply AllLeftExts_unique; eauto using kleftexts_ok.
Qed.

Lemma LeftExt_letter k a u : LeftExt a u (kseq k) -> a <= k.
Proof.
  unfold LeftExt, SubSeq. intros (q, E). unfold subseq in E.
  simpl in E. injection E as E _.
  generalize (kseq_letters k q). lia.
Qed.

Lemma LeftExt_Prefix a u v f :
  Prefix v u -> LeftExt a u f -> LeftExt a v f.
Proof.
 unfold LeftExt. rewrite !SubSeq_alt.
 intros PR (w & SU & PS). exists w. split; auto.
 destruct PR as (v' & PR).
 destruct SU as (w1 & w2 & <-). exists w1, (v'++w2).
 rewrite <- PR. simpl. now rewrite app_assoc.
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
   2:{ rewrite <- length_zero_iff_nil, kword_len.
       generalize (A_nz k (q+2+k)); lia. }
   rewrite <- app_assoc in SU.
   rewrite kword_last in SU.
   replace (q+2+k+k) with (q+2*(S k)) in SU by lia.
   rewrite Nat.mod_add, E in SU by lia.
   red. rewrite SubSeq_alt0 in *.
   destruct SU as (v & (w & SU) & PR). exists v. split; trivial.
   simpl in SU. rewrite app_assoc in SU. eexists. apply SU.
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

Lemma kseq_klvalence_nz k u : SubSeq u (kseq k) -> klvalence k u <> 0.
Proof.
 intros Hu.
 unfold klvalence. rewrite length_zero_iff_nil.
 destruct (kseq_leftext k u Hu) as (a & Ha).
 destruct (kleftexts_ok k u) as (ND,H). rewrite <- H in Ha.
 intros E. now rewrite E in Ha.
Qed.

Lemma klvalence_le_Sk k u : klvalence k u <= S k.
Proof.
 unfold klvalence, kleftexts.
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


(** Since 0 can only come after the k letter,
    it cannot start a left special factor. *)

Lemma ls_no_init_0 k a u : LeftSpecial (a::u) (kseq k) -> a <> 0.
Proof.
 intros (b & c & N & (p,Hb) & (q,Hc)) ->.
 unfold subseq in *. simpl in *.
 injection Hb as Hb Hb' _.
 injection Hc as Hc Hc' _.
 generalize (k0_pred_k k (S p)) (k0_pred_k k (S q)). simpl in *. lia.
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
     simpl. apply (ls_no_init_0 k x u).
     destruct l as [|a [|b l]]; simpl in L; try lia.
     exists a, b; repeat split.
     - inversion ND; simpl in *; intuition.
     - apply A; simpl; intuition.
     - apply A; simpl; intuition. }
   apply lemma_3_7_ii_all'; auto. 2:now red.
   destruct l as [|a l]; simpl in L; try lia.
   assert (SU : SubSeq (a::u) (kseq k)). { apply A. simpl; intuition. }
   rewrite SubSeq_alt0 in *. destruct SU as (w & (v & E) & Hw).
   exists w; repeat split; auto. subst w. exists (v++[a]).
   now rewrite <- app_assoc.
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

Lemma kseq_k_1 k : kseq k 1 = 0.
Proof.
 rewrite kseq_bounded_rank. unfold bounded_rank, rank.
 rewrite decomp_carac with (l:=[0]); simpl; auto. constructor.
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

(* TODO: formule sur l'evolution du nombre de facteurs
   en fonction de la valence des left-special.
*)
