Require Import MoreFun MoreList DeltaList GenFib GenG Words WordFactor.
Import ListNotations.

(** * Study of Left-Special words of [qseq q] *)

(** Especially, for all length p, [qseq q] has a unique left-special word,
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

Lemma LeftExt_letter q a u : LeftExt a u (qseq q) -> a <= q.
Proof.
  unfold LeftExt, SubSeq. intros (p, E). unfold subseq in E.
  simpl in E. injection E as E _.
  generalize (qseq_letters q p). lia.
Qed.

Lemma RightExt_letter q u a : RightExt u a (qseq q) -> a <= q.
Proof.
  unfold RightExt, SubSeq. intros (p, E). revert E.
  unfold subseq. rewrite app_length. simpl.
  rewrite Nat.add_succ_r, seq_S, map_app. simpl. intros E.
  apply app_inv' in E; trivial. destruct E as (_,[= ->]).
  apply qseq_letters.
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

Definition qleftexts q u :=
 let l := qfactors0opt q (S (length u)) in
 filter (fun a => wordmem (a::u) l) (seq 0 (S q)).

Definition qlvalence q (u:word) := length (qleftexts q u).

Definition qrightexts q u :=
 let l := qfactors0opt q (S (length u)) in
 filter (fun a => wordmem (u++[a]) l) (seq 0 (S q)).

Definition qrvalence q (u:word) := length (qrightexts q u).

Lemma qleftexts_ok q u : AllLeftExts (qleftexts q u) u (qseq q).
Proof.
 split.
 - apply NoDup_filter, seq_NoDup.
 - intros a.
   unfold qleftexts.
   rewrite filter_In, in_seq, wordmem_spec, qfactors0opt_in.
   split.
   + intros (_ & _ & SU). apply SU.
   + unfold LeftExt. intros SU. split; [|split]; trivial.
     red in SU. destruct SU as (p & E). unfold subseq in E. simpl in E.
     injection E as E _. generalize (qseq_letters q p); lia.
Qed.

Lemma qrightexts_ok q u : AllRightExts u (qrightexts q u) (qseq q).
Proof.
 split.
 - apply NoDup_filter, seq_NoDup.
 - intros a.
   unfold qrightexts.
   rewrite filter_In, in_seq, wordmem_spec, qfactors0opt_in.
   split.
   + intros (_ & _ & SU). apply SU.
   + unfold RightExt. intros SU. split; [|split]; trivial.
     2:{ rewrite app_length; simpl; lia. }
     red in SU. destruct SU as (p & E). unfold subseq in E.
     rewrite app_length in E. simpl in *.
     rewrite Nat.add_succ_r, seq_S, map_app in E. simpl in E.
     apply app_inv' in E; trivial. destruct E as (_,E).
     injection E as E. generalize (qseq_letters q (p+(length u+0))); lia.
Qed.

Lemma qlvalence_ok q l u :
  AllLeftExts l u (qseq q) -> qlvalence q u = length l.
Proof.
 intros A. rewrite (@Permutation_length _ l (qleftexts q u)); try easy.
 eapply AllLeftExts_unique; eauto using qleftexts_ok.
Qed.

Lemma qrvalence_ok q u l :
  AllRightExts u l (qseq q) -> qrvalence q u = length l.
Proof.
 intros A. rewrite (@Permutation_length _ l (qrightexts q u)); try easy.
 eapply AllRightExts_unique; eauto using qrightexts_ok.
Qed.

Lemma qword_ls q p a : a <= q -> LeftExt a (qword q p) (qseq q).
Proof.
 intros Ha.
 set (r := a + p + S q - p mod S q).
 assert (p <= r).
 { generalize (Nat.mod_upper_bound p (S q)). lia. }
 assert (E : r mod S q = a).
 { unfold r. replace (a+p+S q) with (a+S q+p) by lia.
   rewrite (Nat.div_mod_eq p (S q)) at 1 by lia.
   rewrite Nat.add_assoc, Nat.add_sub.
   rewrite Nat.mul_comm, Nat.mod_add by lia.
   replace (S q) with (1 * S q) at 1 by lia. rewrite Nat.mod_add by lia.
   apply Nat.mod_small; lia. }
 apply LeftExt_Prefix with (qword q (r+2)).
 - apply qword_le_prefix; lia.
 - assert (SU : SubSeq (qword q (r+2+S q)) (qseq q)).
   { rewrite SubSeq_qseq_alt. exists (r+2+S q). apply Sub_id. }
   rewrite Nat.add_succ_r, qword_eqn in SU by lia.
   replace (r+2+q-q) with (r+2) in SU by lia.
   rewrite (@app_removelast_last _ (qword q (r+2+q)) 0) in SU.
   2:{ apply qword_nz. }
   rewrite <- app_assoc in SU.
   rewrite WordSuffix.qword_last in SU.
   replace (r+2+q+q) with (r+2*(S q)) in SU by lia.
   rewrite Nat.mod_add, E in SU by lia.
   red. eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id.
Qed.

Lemma qprefix_leftext q n a : a <= q -> LeftExt a (qprefix q n) (qseq q).
Proof.
 intros Ha.
 rewrite qprefix_alt.
 set (p := invA_up q n).
 apply LeftExt_Prefix with (qword q p).
 - rewrite Prefix_equiv. f_equal. rewrite firstn_length_le; trivial.
   rewrite qword_len. apply invA_up_spec.
 - now apply qword_ls.
Qed.

Lemma qprefix_allleftexts q n :
  AllLeftExts (seq 0 (S q)) (qprefix q n) (qseq q).
Proof.
 split.
 - apply seq_NoDup.
 - intros a. rewrite in_seq. split.
   + intros Ha. apply qprefix_leftext. lia.
   + intros Ha. apply LeftExt_letter in Ha. lia.
Qed.

Lemma qprefix_qlvalence q n : qlvalence q (qprefix q n) = S q.
Proof.
 rewrite <- (seq_length (S q) 0). apply qlvalence_ok.
 apply qprefix_allleftexts.
Qed.

Lemma qseq_leftext q u : SubSeq u (qseq q) -> exists a, LeftExt a u (qseq q).
Proof.
 rewrite SubSeq_qseq_alt; intros (n, (v & w & E)).
 rewrite <- (rev_involutive v) in E.
 destruct (rev v) as [|a v']; simpl in E.
 - exists 0. replace u with (qprefix q (length u)).
   + apply qprefix_leftext; lia.
   + symmetry. change (PrefixSeq u (qseq q)).
     eapply Prefix_PrefixSeq.
     * now exists w.
     * rewrite E. apply qword_prefixseq.
 - exists a. red. rewrite SubSeq_qseq_alt. exists n.
   rewrite <- E, <- !app_assoc. simpl. now do 2 eexists.
Qed.

Lemma qlvalence_nz q u : SubSeq u (qseq q) -> qlvalence q u <> 0.
Proof.
 intros Hu.
 unfold qlvalence. rewrite length_zero_iff_nil.
 destruct (qseq_leftext q u Hu) as (a & Ha).
 destruct (qleftexts_ok q u) as (ND,H). rewrite <- H in Ha.
 intros E. now rewrite E in Ha.
Qed.

Lemma qrvalence_nz q u : SubSeq u (qseq q) -> qrvalence q u <> 0.
Proof.
 intros Hu.
 unfold qrvalence. rewrite length_zero_iff_nil.
 destruct (SubSeq_RightExt u _ Hu) as (a & Ha).
 destruct (qrightexts_ok q u) as (ND,H). rewrite <- H in Ha.
 intros E. now rewrite E in Ha.
Qed.

Lemma qlvalence_le_Sq q u : qlvalence q u <= S q.
Proof.
 unfold qlvalence, qleftexts.
 rewrite <- (seq_length (S q) 0) at 2. apply filter_length_le.
Qed.

Lemma qrvalence_le_Sq q u : qrvalence q u <= S q.
Proof.
 unfold qrvalence, qrightexts.
 rewrite <- (seq_length (S q) 0) at 2. apply filter_length_le.
Qed.

Lemma prefix_incl_allleftexts q u u' l l' :
  Prefix u u' -> AllLeftExts l u (qseq q) -> AllLeftExts l' u' (qseq q) ->
  incl l' l.
Proof.
 intros P (ND,Hu) (ND',Hu') a Ha. rewrite Hu' in Ha. apply Hu.
 eapply LeftExt_Prefix; eauto.
Qed.

Lemma prefix_qlvalence q u v : Prefix u v -> qlvalence q v <= qlvalence q u.
Proof.
 intros P. unfold qlvalence. apply NoDup_incl_length.
 - apply qleftexts_ok.
 - eapply prefix_incl_allleftexts; eauto using qleftexts_ok.
Qed.

Lemma suffix_incl_allrightexts q u u' l l' :
  Suffix u u' -> AllRightExts u l (qseq q) -> AllRightExts u' l' (qseq q) ->
  incl l' l.
Proof.
 intros P (ND,Hu) (ND',Hu') a Ha. rewrite Hu' in Ha. apply Hu.
 eapply RightExt_Suffix; eauto.
Qed.

Lemma suffix_qrvalence q u v : Suffix u v -> qrvalence q v <= qrvalence q u.
Proof.
 intros P. unfold qrvalence. apply NoDup_incl_length.
 - apply qrightexts_ok.
 - eapply suffix_incl_allrightexts; eauto using qrightexts_ok.
Qed.

Lemma ls_val q u : LeftSpecial u (qseq q) <-> 2 <= qlvalence q u.
Proof.
 split.
 - intros (a & b & NE & Ha & Hb).
   unfold qlvalence.
   assert (H := qleftexts_ok q u). destruct H as (_,H).
   rewrite <- H in Ha, Hb. eapply lengthge2_carac; eauto.
 - unfold qlvalence.
   assert (H := qleftexts_ok q u). destruct H as (ND,H).
   destruct (qleftexts q u) as [|a [|b l]] eqn:E; simpl; try lia.
   intros _. exists a, b; repeat split.
   + inversion_clear ND; simpl in *; intuition.
   + apply H; simpl; intuition.
   + apply H; simpl; intuition.
Qed.

Lemma rs_val q u : RightSpecial u (qseq q) <-> 2 <= qrvalence q u.
Proof.
 split.
 - intros (a & b & NE & Ha & Hb).
   unfold qrvalence.
   assert (H := qrightexts_ok q u). destruct H as (_,H).
   rewrite <- H in Ha, Hb. eapply lengthge2_carac; eauto.
 - unfold qrvalence.
   assert (H := qrightexts_ok q u). destruct H as (ND,H).
   destruct (qrightexts q u) as [|a [|b l]] eqn:E; simpl; try lia.
   intros _. exists a, b; repeat split.
   + inversion_clear ND; simpl in *; intuition.
   + apply H; simpl; intuition.
   + apply H; simpl; intuition.
Qed.

(** Valence of letters *)

Lemma all_letters_subseq q a : a <= q <-> SubSeq [a] (qseq q).
Proof.
 split.
 - intros Ha. exists (S a). simpl. unfold subseq. simpl.
   now rewrite all_letters_occur.
 - apply LeftExt_letter.
Qed.

Lemma ls_head_q q a u : LeftSpecial (a::u) (qseq q) -> a = q.
Proof.
 intros (b & c & N & (p,Hb) & (r,Hc)).
 unfold subseq in *. simpl in *.
 injection Hb as Hb Hb' _.
 injection Hc as Hc Hc' _.
 destruct (Nat.eq_dec a q) as [A|A]; trivial. exfalso.
 assert (b = prev_letter q a).
 { rewrite Hb, Hb'. rewrite <- (qseq_prev_letter q (S p)) by lia.
   f_equal; lia. }
 assert (c = prev_letter q a).
 { rewrite Hc, Hc'. rewrite <- (qseq_prev_letter q (S r)) by lia.
   f_equal; lia. }
 lia.
Qed.

Lemma ls_qnz q u : LeftSpecial u (qseq q) -> q<>0.
Proof.
 intros (a & b & AB & A & B). apply LeftExt_letter in A,B. lia.
Qed.

Lemma ls_head_nz q a u : LeftSpecial (a::u) (qseq q) -> a <> 0.
Proof.
 intros LS. rewrite (ls_head_q _ _ _ LS). now apply ls_qnz in LS.
Qed.

Lemma AllRightExts_qm1 q : AllRightExts [q-1] [q] (qseq q).
Proof.
 split.
 - repeat constructor. intuition.
 - intros a. simpl. split; [intros [<-|[ ]] | intros R; left].
   + exists q. unfold subseq. simpl. symmetry. f_equal.
     * destruct (Nat.eq_dec q 0) as [->|Q]. easy.
       replace q with (S (q-1)) at 2 by lia.
       apply all_letters_occur; lia.
     * f_equal. now apply all_letters_occur.
   + destruct R as (p,R). unfold subseq in R. simpl in R.
     injection R as R ->. symmetry. now apply qseq_next_qm1.
Qed.

Lemma qrvalence_qm1 q : qrvalence q [q-1] = 1.
Proof.
 change 1 with (length [q]) at 2. apply qrvalence_ok. apply AllRightExts_qm1.
Qed.

Lemma qrvalence_last_qm1 q u :
  u<>[] -> SubSeq u (qseq q) -> last u 0 = q-1 -> qrvalence q u = 1.
Proof.
 intros U U' L.
 assert (SU : Suffix [q-1] u).
 { exists (removelast u). symmetry. rewrite <- L.
   now apply app_removelast_last. }
 generalize (suffix_qrvalence q _ _ SU) (qrvalence_nz q u U').
 rewrite qrvalence_qm1. lia.
Qed.

Lemma letters_LeftExt q a b : b<q ->
 LeftExt a [b] (qseq q) <-> a = prev_letter q b.
Proof.
 intros B. split.
 - intros (p, E). unfold subseq in E. simpl in E. injection E as Ea Eb.
   subst. replace p with (S p - 1) at 1 by lia. apply qseq_prev_letter; lia.
 - intros ->. exists b. unfold subseq. simpl. f_equal; symmetry.
   + unfold prev_letter.
     case Nat.eqb_spec.
     * intros ->. apply qseq_q_0.
     * intros B'. replace b with (S (pred b)) at 1 by lia.
       apply all_letters_occur. lia.
   + f_equal. apply all_letters_occur. lia.
Qed.

Lemma letters_RightExt q a b :
  RightExt [a] b (qseq q) -> b = next_letter q a \/ b = q.
Proof.
 intros (p, E). unfold subseq in E. simpl in E. injection E as Ea Eb.
 case (Nat.eq_dec b q) as [Eb'|Eb']. now right. left. subst.
 now apply qseq_next_letter.
Qed.

Lemma letters_AllLeftExts q a l : a<q ->
  AllLeftExts l [a] (qseq q) <-> l = [prev_letter q a].
Proof.
 split.
 - intros (ND,A).
   assert (IC :incl l [prev_letter q a]).
   { intros x Hx. rewrite A in Hx. apply letters_LeftExt in Hx; try lia.
     simpl; intuition. }
   assert (length l <= 1).
   { change 1 with (length [prev_letter q a]).
     apply NoDup_incl_length; auto. }
   destruct l as [|x [|y l]]; simpl in *; try lia.
   + destruct (qseq_leftext q [a]) as (b & B).
     { apply all_letters_subseq; lia. }
     now rewrite <- A in B.
   + f_equal. specialize (IC x). simpl in *; intuition.
 - intros ->. split.
   + now repeat constructor.
   + intros b. rewrite letters_LeftExt; trivial. simpl; intuition.
Qed.

Lemma letters_AllRightExts_incl q a l :
  AllRightExts [a] l (qseq q) -> incl l [next_letter q a; q].
Proof.
 intros (_,A) x Hx. rewrite A in Hx. apply letters_RightExt in Hx.
 simpl; intuition.
Qed.

Lemma qlvalence_letter q a : a<q -> qlvalence q [a] = 1.
Proof.
 intros A. unfold qlvalence.
 replace (qleftexts q [a]) with [prev_letter q a]; trivial.
 symmetry. apply letters_AllLeftExts; auto using qleftexts_ok.
Qed.

Lemma qlvalence_letter_q q : qlvalence q [q] = S q.
Proof.
 change [q] with (qprefix q 1). apply qprefix_qlvalence.
Qed.

Lemma qrvalence_letter_le q a : qrvalence q [a] <= 2.
Proof.
 unfold qrvalence. change 2 with (length [next_letter q a; q]).
 apply NoDup_incl_length. apply qrightexts_ok.
 apply letters_AllRightExts_incl. apply qrightexts_ok.
Qed.

(** We'll prove later that actually all letters have qrvalence of 2
    except (q-1) whose qrvalence is 1 (see qrvalence_qm1). *)

Lemma qrvalence_le_2 q u : u<>[] -> qrvalence q u <= 2.
Proof.
 intros Hu. transitivity (qrvalence q [last u 0]).
 - apply suffix_qrvalence.
   exists (removelast u). symmetry. now apply app_removelast_last.
 - apply qrvalence_letter_le.
Qed.


(** Lemmas from the article by Frougny et al. *)

Lemma lemma_3_7_i q u a :
  LeftExt a u (qseq q) ->
  LeftExt (next_letter q a) (qsubstw q u) (qseq q).
Proof.
 intros Ha. assert (Ha' := LeftExt_letter _ _ _ Ha).
 unfold LeftExt in *. rewrite SubSeq_qseq_alt in *.
 destruct Ha as (n, (v & w & E)). exists (S n).
 rewrite qword_S, <- E, !qsubstw_app. cbn. clear E.
 unfold qsubst, next_letter.
 case Nat.eqb_spec; intros.
 - subst. exists (qsubstw q v ++ [q]), (qsubstw q w).
   now rewrite <- !app_assoc.
 - now exists (qsubstw q v), (qsubstw q w).
Qed.

Lemma lemma_3_7_i_ls q u :
  LeftSpecial u (qseq q) ->
  LeftSpecial (qsubstw q u) (qseq q).
Proof.
 intros (a & b & AB & A & B).
 assert (A' := LeftExt_letter _ _ _ A).
 assert (B' := LeftExt_letter _ _ _ B).
 apply lemma_3_7_i in A, B.
 exists (next_letter q a), (next_letter q b); repeat split; trivial.
 contradict AB.
 rewrite <- (prev_next_letter q a), <- (prev_next_letter q b) by trivial.
 now rewrite AB.
Qed.

Lemma PrefixSeq_substlength_prefix q u v :
  PrefixSeq u (qseq q) -> PrefixSeq v (qseq q) ->
  length (qsubstw q u) <= length (qsubstw q v) ->
  Prefix u v.
Proof.
 intros U V L.
 destruct (Nat.le_gt_cases (length u) (length v)).
 - eapply PrefixSeq_incl; eauto.
 - assert (P : Prefix v u) by (eapply PrefixSeq_incl; eauto; lia).
   destruct P as (w & <-).
   rewrite qsubstw_app, app_length in L.
   assert (L' : length (qsubstw q w) = 0) by lia.
   apply length_zero_iff_nil in L'.
   apply (qsubstw_inv q w []) in L'. subst w. rewrite app_nil_r.
   apply Prefix_id.
Qed.

Lemma lemma_3_7_ii_aux q u a :
  hd 0 u <> 0 -> last u 0 <> q ->
  LeftExt a u (qseq q) ->
  exists v, qsubstw q v = u /\
            LeftExt (prev_letter q a) v (qseq q).
Proof.
 intros HD LA Ha. assert (Ha' := LeftExt_letter _ _ _ Ha).
 unfold LeftExt in *. rewrite SubSeq_alt0 in Ha.
 destruct Ha as (w & (u1 & E) & P).
 destruct (qsubst_prefix_inv _ _ P) as (w' & r & E' & P' & [->|Hr]).
 - rewrite app_nil_r in E'.
   assert (Pu1 : PrefixSeq (u1++[a]) (qseq q)).
   { apply Prefix_PrefixSeq with w; trivial.
     exists u. now rewrite <- app_assoc. }
   destruct (qsubst_prefix_inv _ _ Pu1) as (u1' & r' & E1 & Pu1' & [->|Hr']).
   + rewrite app_nil_r in E1.
     assert (PR : Prefix u1' w').
     { eapply PrefixSeq_substlength_prefix; eauto.
       rewrite <- E1, <- E', <- E, !app_length. simpl. lia. }
     destruct PR as (u' & PR).
     exists u'. split.
     * rewrite <- PR in E'. rewrite qsubstw_app, <- E, <- E1 in E'.
       change (a::u) with ([a]++u) in E'. rewrite app_assoc in E'.
       now apply app_inv_head in E'.
     * rewrite <- (rev_involutive u1') in *.
       destruct (rev u1') as [|a' u2']; simpl in E1.
       { now destruct u1. }
       { rewrite SubSeq_alt0. exists w'. split; trivial.
         exists (rev u2'). simpl in PR. rewrite <- app_assoc in PR.
         replace (prev_letter q a) with a'; trivial.
         revert E1. rewrite qsubstw_app. simpl. rewrite app_nil_r.
         unfold qsubst.
         case Nat.eqb_spec.
         - intros ->. change [q;0] with ([q]++[0]).
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
     rewrite qsubstw_app in E. apply app_inv_head in E. simpl in E.
     unfold qsubst in E at 1. destruct (Nat.eqb_spec a' q).
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

Lemma lemma_3_7_ii_cor q u : hd 0 u <> 0 -> last u 0 <> q ->
  SubSeq u (qseq q) ->
  exists v : word, qsubstw q v = u /\ SubSeq v (qseq q).
Proof.
 intros U U' SU. destruct (qseq_leftext _ _ SU) as (a & LE).
 destruct (lemma_3_7_ii_aux q u a U U' LE) as (v & V & V').
 exists v. split; trivial. eapply Sub_SubSeq; eauto using Sub_cons_r.
Qed.

Lemma lemma_3_7_ii_all' q u l :
  SubSeq u (qseq q) -> hd 0 u <> 0 -> last u 0 <> q ->
  AllLeftExts l u (qseq q) ->
  exists v, qsubstw q v = u /\
            AllLeftExts (map (prev_letter q) l) v (qseq q).
Proof.
 intros SU U U' (ND,A).
 destruct l as [|a l].
 { destruct (qseq_leftext q u SU) as (a & Ha). now rewrite <- A in Ha. }
 destruct (lemma_3_7_ii_aux q u a) as (v & Hv & Ha); trivial.
 { rewrite <- A. simpl; intuition. }
 exists v; split; auto. split.
 + apply NoDup_map_inv with (f:=next_letter q).
   rewrite map_map, map_ext_in with (g:=id), map_id; auto.
   intros c Hc. apply next_prev_letter. rewrite A in Hc.
   now apply LeftExt_letter in Hc.
 + intros c. rewrite in_map_iff. split.
   * intros (x & <- & IN). rewrite A in IN.
     destruct (lemma_3_7_ii_aux q u x) as (v' & Hv' & Hx); trivial.
     replace v' with v in *; auto.
     { apply (qsubstw_inv q). now rewrite Hv, Hv'. }
   * intros Hc. exists (next_letter q c). split.
     { apply prev_next_letter. eapply LeftExt_letter; eauto. }
     rewrite A, <- Hv. now apply lemma_3_7_i.
Qed.

Lemma lemma_3_7_ii_val' q u :
  SubSeq u (qseq q) -> hd 0 u <> 0 -> last u 0 <> q ->
  exists v, qsubstw q v = u /\ qlvalence q v = qlvalence q u.
Proof.
 intros SU U U'.
 destruct (lemma_3_7_ii_all' q u (qleftexts q u) SU U U') as (v & Hv & H);
  auto using qleftexts_ok.
 exists v; split; auto.
 unfold qlvalence at 2.
 rewrite <- (map_length (prev_letter q) (qleftexts q u)).
 now apply qlvalence_ok.
Qed.

Lemma lemma_3_7_ii_all q u l :
  last u 0 <> q ->
  AllLeftExts l u (qseq q) -> 2 <= length l ->
  exists v, qsubstw q v = u /\
            AllLeftExts (map (prev_letter q) l) v (qseq q).
Proof.
 intros U (ND,A) L.
 destruct (list_eq_dec Nat.eq_dec u []).
 - subst. simpl in *. exists []. repeat split; trivial.
   + apply NoDup_map_inv with (f:=next_letter q).
     rewrite map_map, map_ext_in with (g:=id), map_id; auto.
     intros a Ha. apply next_prev_letter. rewrite A in Ha.
     now apply LeftExt_letter in Ha.
   + rewrite in_map_iff.
     intros (x & E & IN). rewrite A in IN. apply LeftExt_letter in IN.
     red. apply all_letters_subseq. subst a. now apply prev_letter_le.
   + rewrite in_map_iff. intros Ha. apply LeftExt_letter in Ha.
     exists (next_letter q a). split.
     * now apply prev_next_letter.
     * rewrite A. now apply all_letters_subseq, next_letter_le.
 - assert (hd 0 u <> 0).
   { destruct u as [|x u]; try easy.
     simpl. apply (ls_head_nz q x u).
     destruct l as [|a [|b l]]; simpl in L; try lia.
     exists a, b; repeat split.
     - inversion ND; simpl in *; intuition.
     - apply A; simpl; intuition.
     - apply A; simpl; intuition. }
   apply lemma_3_7_ii_all'; auto. 2:now red.
   destruct l as [|a l]; simpl in L; try lia.
   assert (SU : SubSeq (a::u) (qseq q)). { apply A. simpl; intuition. }
   eapply Sub_SubSeq; eauto using Sub_cons_r.
Qed.

Lemma lemma_3_7_ii_val q u :
  last u 0 <> q -> 2 <= qlvalence q u ->
  exists v, qsubstw q v = u /\ qlvalence q v = qlvalence q u.
Proof.
 intros U L.
 destruct (lemma_3_7_ii_all q u (qleftexts q u) U) as (v & Hv & H);
  auto using qleftexts_ok.
 exists v; split; auto.
 unfold qlvalence.
 rewrite <- (map_length (prev_letter q) (qleftexts q u)).
 now apply qlvalence_ok.
Qed.

Lemma lemma_3_7_ii_ls q u :
  last u 0 <> q -> LeftSpecial u (qseq q) ->
  exists v, qsubstw q v = u /\ LeftSpecial v (qseq q).
Proof.
 rewrite ls_val. intros U L.
 destruct (lemma_3_7_ii_val q u U L) as (v & V & E).
 exists v; split; auto. apply ls_val. lia.
Qed.

Lemma lemma_3_7_i_all_incl q u l l' :
  AllLeftExts l u (qseq q) ->
  AllLeftExts l' (qsubstw q u) (qseq q) ->
  incl (map (next_letter q) l) l'.
Proof.
 intros (ND,A) (ND',A') a. rewrite in_map_iff. intros (x & <- & Hx).
 rewrite A in Hx. rewrite A'. now apply lemma_3_7_i.
Qed.

Lemma lemma_3_7_i_val_le q u :
  qlvalence q u <= qlvalence q (qsubstw q u).
Proof.
 unfold qlvalence.
 rewrite <- (map_length (next_letter q) (qleftexts q u)).
 apply NoDup_incl_length.
 - apply NoDup_map_inv with (f:=prev_letter q).
   rewrite map_map, map_ext_in with (g:=id), map_id; auto.
   apply qleftexts_ok.
   intros a Ha. apply prev_next_letter.
   assert (H := qleftexts_ok q u). destruct H as (_,H).
   rewrite H in Ha. now apply LeftExt_letter in Ha.
 - eapply lemma_3_7_i_all_incl; eauto using qleftexts_ok.
Qed.

(** Note: [q-1] has qlvalence of 1 since it could only come after
    (prev_letter q (q-1)). But (qsubstw q [q-1])=[q] has
    qlvalence of (S q).
    Hence the qlvalence is preserved by qsubst only when it is at least 2
    (i.e. for left-special words). *)

(* /!\ Problem with the last line of the proof of Lemma 3.7 :
   \tilde{p} = p cannot be obtained in general, since (ii) needs
   last letter to be different from q.
   No big issue, since eventually the only LeftSpecial words
   (the qprefix) have qlvalence (S q), hence the same for their image
   by qsubst. And this precise part of Lemma 3.7 (i) doesn't seem
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

Lemma lemma_4_4 q n a : n<>0 ->
  last (qword q n) 0 = a -> Suffix [prev_letter q a; a] (qword q n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 intros Hn Ha. destruct (Nat.le_gt_cases n (S q)).
 - clear IH. rewrite qword_low in * by lia.
   destruct n as [|[|n]]; try easy.
   + simpl in *. subst a. now exists [].
   + rewrite seq_S in Ha. simpl "+" in Ha.
     change (q::_++[S n]) with ((q::seq 0 (S n))++[S n]) in Ha.
     rewrite last_last in Ha. subst a.
     rewrite !seq_S. exists (q::seq 0 n). simpl. f_equal.
     now rewrite <- app_assoc.
 - destruct n; try easy. rewrite qword_eqn in * by lia.
   rewrite last_app in Ha.
   2:{ apply qword_nz. }
   destruct (IH (n-q)) as (u & <-); trivial; try lia.
   exists (qword q n ++ u). now rewrite app_assoc.
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

Lemma lemma_4_5 q r a b : a<>q -> b<>q ->
  SubSeq ([a] ++ repeat q r ++ [b]) (qseq q) <->
  (r=0 /\ a = b-1 /\ 0 < b < q) \/
  (r=1 /\ a < q /\ b = 0) \/
  (r=2 /\ a = q-1 /\ b = 0).
Proof.
 intros A B. split.
 - rewrite SubSeq_qseq_alt. intros (n,SU). revert SU.
   induction n as [n IH] using lt_wf_ind.
   destruct (Nat.le_gt_cases n q) as [LE|GT].
   + clear IH. rewrite qword_low by lia. intros (u & v & E). left.
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
     rewrite qword_eqn by lia. intros SU. apply Sub_app_inv in SU.
     destruct SU as [SU|[SU|(u1 & u2 & U1 & U2 & E & SU & PR)]].
     * apply (IH n); auto.
     * apply (IH (n-q)); auto. lia.
     * clear IH. right.
       destruct u1 as [|x1 u1]; try easy. clear U1. simpl in E.
       injection E as <- E.
       rewrite <- (rev_involutive u2) in *.
       destruct (rev u2) as [|x2 u2']; try easy. clear U2. simpl in *.
       clear u2.
       rewrite app_assoc in E.
       apply app_inv' in E; trivial. destruct E as (E & [= <-]).
       destruct (Nat.eq_dec n q) as [->|N].
       { rewrite Nat.sub_diag, qword_0 in PR.
         destruct PR as (u2, PR).
         assert (L := f_equal (@length nat) PR).
         rewrite !app_length, rev_length in L. simpl in L.
         assert (length u2' = 0) by lia.
         rewrite length_zero_iff_nil in *. subst u2'.
         simpl in PR. now injection PR as -> _. }
       { assert (PR' : 1 <= n-q) by lia.
         apply (qword_le_prefix q) in PR'. rewrite qword_1 in PR'.
         destruct (rev u2') as [|x [|y u2]]; simpl in PR.
         - assert (PR2 : Prefix [b] [q;0]).
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
             generalize (qword_letters q n). rewrite <- SU, Forall_app.
             intros (_,F). inversion_clear F. lia.
           + right; repeat split; auto.
             simpl in SU.
             destruct SU as (u & SU).
             assert (N' : n <> 0) by lia.
             assert (L : last (qword q n) 0 = q).
             { now rewrite <- SU, last_app. }
             assert (SU' := lemma_4_4 q n q N' L).
             destruct SU' as (u' & SU'). rewrite <- SU' in SU.
             apply app_inv' in SU; auto. destruct SU as (_,[= ->]).
             unfold prev_letter. case Nat.eqb_spec; lia.
           + exfalso.
             replace (S (S r)) with (r+2) in SU by lia.
             rewrite repeat_app in SU. simpl in SU.
             destruct SU as (u & SU).
             change (a::_ ++ _) with ((a::repeat q r)++[q;q]) in SU.
             rewrite app_assoc in SU.
             assert (N' : n <> 0) by lia.
             assert (L : last (qword q n) 0 = q).
             { now rewrite <- SU, last_app. }
             assert (SU' := lemma_4_4 q n q N' L).
             destruct SU' as (u' & SU'). rewrite <- SU' in SU.
             apply app_inv' in SU; auto. destruct SU as (_,[= E]).
             revert E. unfold prev_letter. case Nat.eqb_spec; lia.
         - exfalso.
           assert (IN : In a (qword q n)).
           { destruct SU as (u & <-). rewrite in_app_iff; right.
             simpl; intuition. }
           assert (LT : a < q).
           { generalize (qword_letters q n). rewrite Forall_forall.
             intros F. specialize (F a IN). lia. }
           clear IN.
           assert (PR2 : Prefix [q;0] (x::y::u2++[b])).
           { eapply Prefix_Prefix; simpl; eauto; try lia. }
           destruct PR2 as (u & [= <- <- PR2]).
           assert (IN : In 0 (repeat q r)).
           { rewrite E. rewrite in_app_iff. right. simpl; intuition. }
           apply repeat_spec in IN. lia. }
 - intros [(-> & -> & B')|[(-> & A' & ->)|(-> & -> & ->)]].
   + simpl. exists b. unfold subseq. simpl.
     assert (E : b = qseq q (S b)).
     { symmetry. apply all_letters_occur. lia. }
     f_equal; [|now f_equal].
     symmetry. replace b with ((S b)-1) at 1 by lia.
     rewrite qseq_prev_letter by lia. rewrite <- E.
     unfold prev_letter. case Nat.eqb_spec; lia.
   + simpl. apply SubSeq_qseq_alt. exists (S (q+a+2)).
     rewrite qword_eqn by lia.
     assert (E : last (qword q (q+a+2)) 0 = a).
     { rewrite WordSuffix.qword_last.
       replace (q+a+2+q) with (a+2*(S q)) by lia.
       rewrite Nat.mod_add, Nat.mod_small; lia. }
     change [a;q;0] with ([a]++[q;0]).
     apply Sub_app.
     * rewrite <- E at 1. apply Suffix_last. apply qword_nz.
     * replace [q;0] with (qword q 1).
       2:{ rewrite qword_low; simpl; trivial; lia. }
       apply qword_le_prefix; lia.
   + simpl. apply SubSeq_qseq_alt. exists (S (q+1)).
     rewrite qword_eqn by lia.
     assert (E : last (qword q (q+1)) 0 = q).
     { rewrite WordSuffix.qword_last.
       replace (q+1+q) with (q+1*(S q)) by lia.
       rewrite Nat.mod_add, Nat.mod_small; lia. }
     change [q-1;q;q;0] with ([q-1;q]++[q;0]).
     apply Sub_app.
     * replace (q-1) with (prev_letter q q).
       apply lemma_4_4; try lia.
       unfold prev_letter. case Nat.eqb_spec; lia.
     * replace [q;0] with (qword q 1).
       2:{ rewrite qword_low; simpl; trivial; lia. }
       apply qword_le_prefix; lia.
Qed.

Lemma infinitly_many_0_letters q :
 forall n, { m | n <= m /\ qseq q m = 0 }.
Proof.
 intros n.
 destruct (Nat.eq_dec q 0) as [->|Q].
 - exists n. split; trivial. generalize (qseq_letters 0 n). lia.
 - set (p := invA_up q n).
   exists (S (Nat.max (q+2) (A q p))). split.
   + generalize (invA_up_spec q n). unfold p. lia.
   + apply Nat.max_case_strong; intros LE.
     * rewrite qseq_bounded_rank. unfold bounded_rank, rank.
       rewrite decomp_S.
       replace (decomp q (q+2)) with [S q].
       2:{ symmetry. apply decomp_carac.
           - constructor.
           - replace (q+2) with (S (S q)) by lia.
             rewrite <- (@A_base q (S q)) by lia. simpl; lia. }
       unfold next_decomp. case Nat.leb_spec; simpl; lia.
     * rewrite qseq_bounded_rank. unfold bounded_rank, rank.
       replace (decomp q (S (A q p))) with [0;p]; trivial.
       symmetry. apply decomp_carac; simpl; try lia.
       constructor. 2:constructor. simpl. apply (A_le_inv q).
       rewrite A_base; lia.
Qed.

Lemma lemma_4_5_bis q r a :
  q<>0 -> a<>q -> SubSeq ([a] ++ repeat q r) (qseq q) -> r <= 2.
Proof.
 intros Q A (p,E).
 rewrite app_length, repeat_length in E. simpl in E.
 destruct (infinitly_many_0_letters q (p+S r)) as (n,(N,N')).
 remember (n-(p+S r)) as m eqn:M.
 revert r E N N' M.
 induction m; intros.
 - replace n with (p+S r) in N' by lia.
   assert (SU : SubSeq ([a] ++ repeat q r ++ [0]) (qseq q)).
   { exists p. rewrite !app_length, repeat_length, Nat.add_1_r. simpl.
     unfold subseq in *. now rewrite seq_S, map_app, <- E, <- N'. }
   apply lemma_4_5 in SU; trivial; lia.
 - destruct (Nat.eq_dec (qseq q (p+S r)) q) as [E'|E'].
   + assert (S r <= 2); try lia.
     apply IHm; try lia. clear IHm.
     rewrite <- (Nat.add_1_r r), repeat_app at 1. simpl.
     unfold subseq in *. rewrite seq_S, map_app, <- E. simpl.
     now repeat f_equal.
   + set (b := qseq q (p+S r)) in *.
     assert (SU : SubSeq ([a] ++ repeat q r ++ [b]) (qseq q)).
     { exists p. rewrite !app_length, repeat_length, Nat.add_1_r. simpl.
       unfold subseq in *. now rewrite seq_S, map_app, <- E. }
     apply lemma_4_5 in SU; trivial; lia.
Qed.

Lemma lemma_4_5_ter q r : q<>0 -> SubSeq (repeat q r) (qseq q) -> r <= 2.
Proof.
 intros Q (p,E). rewrite repeat_length in E. revert r E.
 induction p; intros.
 - unfold subseq in E. destruct r as [|[|r]]; try lia.
   simpl in E. rewrite qseq_q_1 in E. now injection E as [= E _].
 - destruct (Nat.eq_dec (qseq q p) q) as [E'|E'].
   + assert (S r <= 2); try lia.
     { apply IHp. unfold subseq in *. simpl. now rewrite E', E. }
   + eapply lemma_4_5_bis; eauto. exists p.
     rewrite app_length, repeat_length. simpl. now rewrite E.
Qed.

Lemma lemma_4_5_qq q a b :
 SubSeq [a;q;q;b] (qseq q) -> a = q-1 /\ b = 0.
Proof.
 intros SU.
 destruct (Nat.eq_dec q 0) as [->|Q].
 { simpl. destruct SU as (q & SU). unfold subseq in SU. simpl in SU.
   injection SU as E1 _ _ E2.
   generalize (qseq_letters 0 q) (qseq_letters 0 (S (S (S q)))). lia. }
 destruct (Nat.eq_dec a q) as [->|A].
 { exfalso.
   assert (SU' : SubSeq (repeat q 3) (qseq q)).
   { eapply Sub_SubSeq; eauto. now exists [], [b]. }
   apply lemma_4_5_ter in SU'; lia. }
 destruct (Nat.eq_dec b q) as [->|B].
 { exfalso.
   assert (SU' : SubSeq (repeat q 3) (qseq q)).
   { eapply Sub_SubSeq; eauto. now exists [a], []. }
   apply lemma_4_5_ter in SU'; lia. }
 rewrite (lemma_4_5 q 2 a b) in SU; lia.
Qed.

Lemma lemma_4_5_qq' q a : SubSeq [q;q;a] (qseq q) -> a = 0.
Proof.
 intros ([|p],SU).
 - unfold subseq in SU. simpl in SU. injection SU as E1 E2.
   rewrite qseq_q_1 in E1. generalize (qseq_letters q 2). lia.
 - assert (SU' : SubSeq [qseq q p; q; q; a] (qseq q)).
   { exists p. unfold subseq in *. simpl in *. now f_equal. }
   apply lemma_4_5_qq in SU'. lia.
Qed.

Lemma lemma_4_5_q0 q a b :
  SubSeq [a;q;b] (qseq q) -> a <> q-1 -> b = 0.
Proof.
 intros SU N.
 destruct (Nat.eq_dec a q) as [->|A].
 - eapply lemma_4_5_qq'; eauto.
 - destruct (SubSeq_RightExt _ _ SU) as (c, SU').
   destruct (Nat.eq_dec b q) as [->|B].
   + apply lemma_4_5_qq in SU'. lia.
   + apply (lemma_4_5 q 1 a b) in SU; lia.
Qed.

Lemma RS_aq q u a : RightSpecial (u ++ [a;q]) (qseq q) -> a = q-1.
Proof.
 intros RS.
 eapply RightSpecial_Suffix in RS; [|now exists u].
 destruct RS as (b & c & BC & B & C).
 destruct (Nat.eq_dec a (q-1)) as [E|N]; try easy.
 apply lemma_4_5_q0 in B, C; trivial. lia.
Qed.

Lemma corollary_4_6_aux q r : q<>0 -> 2 <= r ->
  ~RightSpecial (repeat q r) (qseq q).
Proof.
 intros Q R RS.
 apply RightSpecial_Suffix with (u:=[q;q]) in RS.
 - destruct RS as (a & b & AB & A & B). apply lemma_4_5_qq' in A, B. lia.
 - exists (repeat q (r-2)). change [q;q] with (repeat q 2).
   rewrite <- repeat_app. f_equal; lia.
Qed.

Lemma corollary_4_6 q u r : q<>0 -> 2 <= r ->
  ~RightSpecial (u++repeat q r) (qseq q).
Proof.
 intros Q R RS. apply (corollary_4_6_aux q r Q R).
 eapply RightSpecial_Suffix; eauto. now exists u.
Qed.

Lemma lemma_4_7 q r : ~MaxLeftSpecial (repeat q r) (qseq q).
Proof.
 destruct (Nat.eq_dec q 0) as [->|Q].
 { intros ((a & b & AB & A & B),_). apply LeftExt_letter in A, B. lia. }
 intros (LS,NLS).
 assert (SU : SubSeq (repeat q r) (qseq q)).
 { destruct LS as (a & b & AB & A & B).
   red in A. eapply Sub_SubSeq; eauto using Sub_cons_r. }
 apply lemma_4_5_ter in SU; auto.
 destruct r as [|[|r]]; simpl in *.
 - apply (NLS q). apply ls_val. rewrite qlvalence_letter_q. lia.
 - apply (NLS 0). apply ls_val.
   assert (E : [q;0] = qprefix q 2).
   { cbn. now rewrite qsubst_q. }
   rewrite E, qprefix_qlvalence. lia.
 - replace r with 0 in * by lia. simpl in *. clear NLS SU.
   destruct LS as (a & b & AB & A & B).
   destruct (Nat.eq_dec a q) as [->|A'].
   { unfold LeftExt in A. apply (lemma_4_5_ter q 3) in A; lia. }
   destruct (SubSeq_RightExt _ _ A) as (c & AR).
   destruct (Nat.eq_dec c q) as [->|C].
   { apply (lemma_4_5_bis q 3 a) in AR; trivial; lia. }
   apply (lemma_4_5 q 2 a c) in AR; trivial.
   destruct (Nat.eq_dec b q) as [->|B'].
   { unfold LeftExt in B. apply (lemma_4_5_ter q 3) in B; lia. }
   destruct (SubSeq_RightExt _ _ B) as (d & BR).
   destruct (Nat.eq_dec d q) as [->|D].
   { apply (lemma_4_5_bis q 3 b) in BR; trivial; lia. }
   apply (lemma_4_5 q 2 b d) in BR; trivial.
   lia.
Qed.

Lemma SubSeq_qq q u :
  SubSeq (u++[q;q]) (qseq q) -> SubSeq (u++[q;q;0]) (qseq q).
Proof.
 intros (p,SU).
 assert (SU' : SubSeq (u++[q;q;qseq q (p + length u + 2)]) (qseq q)).
 { exists p. unfold subseq in *; rewrite app_length in *. simpl in *.
   rewrite (Nat.add_succ_r (length u)), seq_S, map_app, <- SU.
   rewrite <- app_assoc. simpl. do 5 f_equal. lia. }
 set (n := p + _ + 2) in *.
 replace (qseq q n) with 0 in *; trivial.
 symmetry. apply (lemma_4_5_qq' q). eapply Sub_SubSeq; eauto.
 apply Sub_app_l, Sub_id.
Qed.

Lemma LeftSpecial_qq q u :
  LeftSpecial (u++[q;q]) (qseq q) -> LeftSpecial (u++[q;q;0]) (qseq q).
Proof.
 intros (a & b & AB & A & B). exists a, b. split; trivial. split.
 apply (SubSeq_qq q (a::u)), A.
 apply (SubSeq_qq q (b::u)), B.
Qed.

Lemma lemma_4_9 q u :
  SubSeq (u++[q-1]) (qseq q) -> SubSeq (u++[q-1;q]) (qseq q).
Proof.
 intros (p,E). exists p. rewrite app_length in *.
 unfold subseq in *. simpl in *.
 rewrite !Nat.add_succ_r, !seq_S, !map_app in *. simpl in *.
 set (n := length u) in *. rewrite Nat.add_0_r in *.
 apply app_inv' in E; trivial. destruct E as (<-,[= E]).
 now rewrite Nat.add_succ_r, qseq_next_qm1, <- E, <- app_assoc.
Qed.

Lemma lemma_4_9_ls q u :
  LeftSpecial (u++[q-1]) (qseq q) -> LeftSpecial (u++[q-1;q]) (qseq q).
Proof.
 intros (a & b & AB & A & B). exists a, b; repeat split; trivial.
 now apply (lemma_4_9 q (a::u)).
 now apply (lemma_4_9 q (b::u)).
Qed.

Lemma qseq_after_q q a : SubSeq [q;a] (qseq q) -> a = 0 \/ a = q.
Proof.
 intros (p,SU). unfold subseq in *. simpl in *. injection SU as E1 E2.
 generalize (qseq_next_letter q p). rewrite <- E2, <- E1, next_letter_q. lia.
Qed.

Lemma qword_qp2 q : qword q (q+2) = qword q q ++ [q;q;0].
Proof.
 rewrite !Nat.add_succ_r, !qword_eqn, !Nat.add_0_r, Nat.sub_diag by lia.
 rewrite <- app_assoc. f_equal.
 replace (S q - q) with 1 by lia. cbn. now rewrite qsubst_q.
Qed.

Lemma qrvalence_letter_q q : q<>0 -> qrvalence q [q] = 2.
Proof.
 intros Q.
 unfold qrvalence. change 2 with (length [0; q]).
 eapply Permutation_length, AllRightExts_unique; eauto using qrightexts_ok.
 split.
 - repeat constructor; simpl; intuition.
 - intros a. simpl. intuition; try subst a.
   + exists 0. cbn. now rewrite qsubst_q.
   + apply SubSeq_qseq_alt. exists (q+2). rewrite qword_qp2.
     apply Sub_app_l. now exists [],[0].
   + apply qseq_after_q in H. intuition.
Qed.

Lemma qrvalence_low_letter q a : a<q-1 -> qrvalence q [a] = 2.
Proof.
 intros Q.
 unfold qrvalence. change 2 with (length [S a; q]).
 eapply Permutation_length, AllRightExts_unique; eauto using qrightexts_ok.
 split.
 - repeat constructor; simpl; intuition. lia.
 - intros b. simpl. intuition; try subst b.
   + exists (S a). unfold subseq. simpl.
     now rewrite !all_letters_occur by lia.
   + red. simpl.
     assert (SubSeq [a;q;0] (qseq q)) by (apply (lemma_4_5 q 1); lia).
     eapply Sub_SubSeq; eauto. now exists [], [0].
   + red in H. simpl in H.
     destruct (Nat.eq_dec q b) as [->|N]. intuition.
     apply (lemma_4_5 q 0) in H; lia.
Qed.

(** Instead of proposition 3.8 and theorem 3.9 about Infinite Left Special,
    we use here an ad-hoc decreasing principle, that avoid the need for
    infinitary objects (delicates in Coq). Moreover, it explicits the fact
    that we may need to right-extend LeftSpecial words, but at most once. *)

Lemma DecrLemma q u :
  1 < length u ->
  LeftSpecial u (qseq q) ->
  (last u 0 = q -> exists x, LeftSpecial (u++[x]) (qseq q)) ->
  exists v w,
    LeftSpecial v (qseq q) /\
    (w=[]\/w=[0]) /\
    qsubstw q v = u++w /\
    length v < length u.
Proof.
 intros U LS LS'.
 assert (Q := ls_qnz _ _ LS).
 destruct (Nat.eq_dec (last u 0) q) as [L|N].
 - specialize (LS' L). destruct LS' as (x & LS'). clear LS.
   assert (U' : u <> []) by now intros ->.
   assert (E := app_removelast_last 0 U').
   rewrite L in E.
   set (u' := removelast u) in *. clearbody u'. subst u. clear L U'.
   rewrite app_length in U. simpl in U. rewrite Nat.add_1_r in U.
   rewrite <- app_assoc in LS'. simpl in LS'.
   destruct (Nat.eq_dec x q) as [->|N'].
   + destruct (lemma_3_7_ii_ls q (u'++[q;q;0])) as (v & V & V').
     { rewrite last_app; simpl. lia. easy. }
     { now apply LeftSpecial_qq. }
     assert (N : v <> []).
     { intros ->. simpl in V. now destruct u'. }
     assert (E := app_removelast_last 0 N).
     set (v' := @removelast nat v) in *. clearbody v'.
     rewrite E in V. rewrite qsubstw_app in V.
     revert V. simpl. rewrite app_nil_r.
     unfold qsubst. case Nat.eqb_spec.
     2:{ change [q;q;0] with ([q;q]++[0]).
         rewrite app_assoc. intros _ V. apply app_inv' in V; easy. }
     change [q;q;0] with ([q]++[q;0]); rewrite app_assoc.
     intros E' V. rewrite E' in E. clear E'.
     apply app_inv' in V; simpl; trivial. destruct V as (V,_).
     exists v', []; repeat split; trivial.
     * rewrite E in V'. eapply LeftSpecial_Prefix; eauto.
       now exists [q].
     * now left.
     * now rewrite app_nil_r.
     * rewrite <- V. rewrite len_qsubst.
       destruct v' as [|a v']; [now destruct u'|].
       rewrite E in V'. simpl in V'. apply ls_head_q in V'. subst a.
       simpl in *. rewrite Nat.eqb_refl. lia.
   + destruct (qseq_after_q q x) as [-> | ->]; try lia.
     { apply LeftSpecial_SubSeq in LS'. eapply Sub_SubSeq; eauto.
       apply Sub_app_l, Sub_id. }
     clear N'.
     destruct (lemma_3_7_ii_ls q (u'++[q;0])) as (v & V & V'); trivial.
     { rewrite last_app; simpl. lia. easy. }
     exists v, [0]; repeat split; trivial.
     * now right.
     * now rewrite V, <- app_assoc.
     * assert (E := len_qsubst q v).
       rewrite V in E. rewrite app_length in *. simpl in *.
       assert (N : v <> []) by (intros ->; now destruct u').
       assert (E' := app_removelast_last 0 N).
       set (v' := @removelast nat v) in *. clearbody v'.
       rewrite E' in V. rewrite qsubstw_app in V.
       revert V. simpl. rewrite app_nil_r.
       unfold qsubst. case Nat.eqb_spec.
       2:{ change [q;0] with ([q]++[0]).
           rewrite app_assoc. intros _ V. apply app_inv' in V; easy. }
       intros E2 V. rewrite E2 in E'. clear E2.
       apply app_inv' in V; simpl; trivial. destruct V as (V,_).
       assert (2 <= nbocc q v); try lia.
       { rewrite E'. rewrite nbocc_app. simpl. rewrite Nat.eqb_refl.
         destruct v' as [|a v']; simpl in *. now subst u'.
         rewrite E' in V'. apply ls_head_q in V'. subst a.
         rewrite Nat.eqb_refl. lia. }
 - clear LS'.
   destruct (lemma_3_7_ii_ls q u) as (v & V & V'); trivial.
   exists v, []; repeat split; trivial.
   + now left.
   + now rewrite app_nil_r.
   + rewrite <- V, len_qsubst.
     destruct v as [|a v]; simpl in *. now subst u.
     apply ls_head_q in V'. subst a. rewrite Nat.eqb_refl. lia.
Qed.

(** Turn the lacq of MaxLeftSpecial into a positive fact about LeftSpecial. *)

Lemma NoMaxLS_exists q u :
  LeftSpecial u (qseq q) ->
  ~MaxLeftSpecial u (qseq q) ->
  exists a, LeftSpecial (u++[a]) (qseq q).
Proof.
 intros LS NM.
 set (l := seq 0 (S q)).
 destruct (existsb (fun a => Nat.leb 2 (qlvalence q (u++[a]))) l) eqn:E.
 - rewrite existsb_exists in E.
   destruct E as (a & IN & LS'). exists a. now apply ls_val, Nat.leb_le.
 - exfalso. apply NM. split; trivial. intros a LS'.
   assert (a <= q).
   { apply all_letters_subseq. apply LeftSpecial_SubSeq in LS'.
     eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
   apply ls_val, Nat.leb_le in LS'.
   rewrite <- not_true_iff_false, existsb_exists in E. apply E. clear E.
   exists a; split; trivial. apply in_seq. lia.
Qed.

(* Two auxiliary lemmas for Proposition 4.10 : ante-image of right
   extensions *)

Lemma inv_letter_for_4_10 q u v' b :
  MaxLeftSpecial u (qseq q) -> last u 0 <> q -> qsubstw q v' = u ->
  RightExt u b (qseq q) ->
  exists b', RightExt v' b' (qseq q) /\ ~LeftSpecial (v'++[b']) (qseq q) /\
             head (qsubst q b') = Some b.
Proof.
 intros (LS,NLS) L E B.
 assert (Q : q<>0) by now apply ls_qnz in LS.
 assert (U : u<>[]). { intros ->. now apply (lemma_4_7 q 0). }
 destruct (Nat.eq_dec b q) as [->|NB].
 - destruct (SubSeq_RightExt _ _ B) as (b2 & B2).
   red in B2. rewrite <- app_assoc in B2. simpl in B2.
   assert (B2' : SubSeq [q;b2] (qseq q)).
   { eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
   destruct (qseq_after_q _ _ B2') as [-> | ->].
   + destruct (lemma_3_7_ii_cor q (u++[q;0])) as (v & V & SU); trivial.
     { destruct u; simpl; try easy. apply ls_head_q in LS; lia. }
     { rewrite last_app; simpl; easy || lia. }
     assert (E2 : v = v' ++ [q]).
     { apply (qsubstw_inv q). rewrite qsubstw_app, V, E. f_equal.
       cbn. now rewrite qsubst_q. }
     exists q; repeat split.
     { red. now rewrite <- E2. }
     { rewrite <- E2. intro LS3.
       apply lemma_3_7_i_ls in LS3. rewrite V in LS3.
       apply (NLS q).
       eapply LeftSpecial_Prefix; eauto.
       exists [0]. now rewrite <- app_assoc. }
     { now rewrite qsubst_q. }
   + destruct (SubSeq_RightExt _ _ B2) as (b3 & B3).
     red in B3. rewrite <- app_assoc in B3. simpl in B3.
     assert (B3' : SubSeq [q;q;b3] (qseq q)).
     { eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
     rewrite (lemma_4_5_qq' _ _ B3') in *.
     destruct (lemma_3_7_ii_cor q (u++[q;q;0])) as (v & V & SU); trivial.
     { destruct u; simpl; try easy. apply ls_head_q in LS; lia. }
     { rewrite last_app; simpl; easy || lia. }
     assert (E2 : v = v' ++ [q-1;q]).
     { apply (qsubstw_inv q). rewrite qsubstw_app, V, E. f_equal.
       cbn. now rewrite qsubst_qm1, qsubst_q by trivial. }
     exists (q-1); repeat split; rewrite ?qsubst_qm1 in *; trivial.
     { red. apply Sub_SubSeq with v; auto. subst v.
       exists [], [q]. now rewrite <- !app_assoc. }
     { intro LS3. apply lemma_3_7_i_ls in LS3.
       rewrite qsubstw_app, E in LS3. simpl in LS3.
       rewrite app_nil_r in LS3. rewrite qsubst_qm1 in LS3 by trivial.
       now apply NLS in LS3. }
 - assert (b<>0).
   { intros ->.
     red in B.
     rewrite (app_removelast_last 0 U), <- app_assoc in B.
     simpl in B.
     eapply Sub_SubSeq in B; [|apply Sub_app_l, Sub_id].
     apply letters_RightExt in B. destruct B as [B|B]; try lia.
     revert B. unfold next_letter in *. case Nat.eqb_spec; lia. }
   destruct (lemma_3_7_ii_cor q (u++[b])) as (v & V & SU); trivial.
   { destruct u as [|x u]; simpl; try easy. apply ls_head_q in LS.
     now subst x. }
   { now rewrite last_last. }
   assert (b <= q).
   { eapply Sub_SubSeq in B; [|apply Sub_app_l, Sub_id].
     now apply all_letters_subseq in B. }
   assert (B2 : qsubst q (b-1) = [b]).
   { unfold qsubst. case Nat.eqb_spec. lia. intros _. f_equal; lia. }
   assert (E2 : v = v'++[b-1]).
   { apply (qsubstw_inv q). rewrite qsubstw_app, E, V. f_equal.
     simpl. now rewrite app_nil_r. }
   exists (b-1); repeat split.
   { red. now rewrite <- E2. }
   { rewrite <- E2. intros LS3.
     apply lemma_3_7_i_ls in LS3. rewrite V in LS3.
     now apply NLS in LS3. }
   { now rewrite B2. }
Qed.

Lemma inv_letter_bis_for_4_10 q u v' b :
  MaxLeftSpecial (u++[q]) (qseq q) -> qsubstw q v' = u ->
  RightExt (u++[q]) b (qseq q) ->
  exists b', RightExt v' b' (qseq q) /\ ~LeftSpecial (v'++[b']) (qseq q) /\
             ((b = q /\ b' = q-1) \/ (b = 0 /\ b' = q)).
Proof.
 intros (LS,NLS) E B.
 assert (Q : q<>0) by now apply ls_qnz in LS.
 assert (U : u<>[]). { intros ->. now apply (lemma_4_7 q 1). }
 destruct (qseq_after_q q b) as [-> | ->].
 { red in B. rewrite <- app_assoc in B. simpl in B.
   eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
 - exists q.
   destruct (lemma_3_7_ii_cor q (u++[q;0])) as (v & V & SU); trivial.
   { destruct u; simpl; try easy. apply ls_head_q in LS; lia. }
   { rewrite last_app; simpl; easy || lia. }
   { red in B. now rewrite <- app_assoc in B. }
   replace v with (v' ++ [q]) in *.
   2:{ apply (qsubstw_inv q). rewrite qsubstw_app, V, E. f_equal.
       cbn. now rewrite qsubst_q. }
   repeat split; trivial; [|now right].
   intros LS'. apply lemma_3_7_i_ls in LS'.
   rewrite V in LS'. apply (NLS 0). now rewrite <- !app_assoc.
 - exists (q-1).
   destruct (SubSeq_RightExt _ _ B) as (b2 & B2).
   red in B2. rewrite <- !app_assoc in B2. simpl in B2.
   assert (B2' : SubSeq [q;q;b2] (qseq q)).
   { eapply Sub_SubSeq; eauto. apply Sub_app_l, Sub_id. }
   apply lemma_4_5_qq' in B2'. subst b2.
   destruct (lemma_3_7_ii_cor q (u++[q;q;0])) as (v & V & SU); trivial.
   { destruct u; simpl; try easy. apply ls_head_q in LS; lia. }
   { rewrite last_app; simpl; easy || lia. }
   replace v with (v' ++ [q-1;q]) in *.
   2:{ apply (qsubstw_inv q). rewrite qsubstw_app, V, E. f_equal.
     cbn. now rewrite qsubst_q, qsubst_qm1. }
   repeat split; try now left.
   { eapply Sub_SubSeq; eauto.
     exists [], [q]. now rewrite <- app_assoc. }
   { intros LS'. apply lemma_4_9_ls in LS'. apply lemma_3_7_i_ls in LS'.
     rewrite V in LS'. apply (NLS q).
     eapply LeftSpecial_Prefix; eauto. exists [0].
     now rewrite <- !app_assoc. }
Qed.

(** Proposition 4.10 as proved in Corrigendum (as Proposition 2.2).
    Some parts of the proofs were unecessary here :
    - We are here in the case "t_1 > max(t_2...t_{m-1})" (t_1=t_m=1>0=t_i).
    - The last paragraph is sqipped since factors of (qseq q) cannot
      have a right valence of 3>2.

    Moreover This proof of proposition 4.10 is left here for completeness
    reasons, but a shorter approach is also possible (and was used in a
    former version of this worq) : just prove that v is LeftSpecial
    instead of MaxLeftSpecial, and moreover that
      [w=[q] -> ~RightSpecial (qsubstw q v) (qseq q)].
    This is enough for completing [LeftSpecial_qprefix] below, and then
    proving ~MaxLeftSpecial afterwards. *)

Lemma proposition_4_10 q u x :
  MaxLeftSpecial u (qseq q) -> x<>q -> In x u ->
  exists v w,
    MaxLeftSpecial v (qseq q) /\ u = qsubstw q v ++ w /\ (w=[] \/ w = [q]).
Proof.
 destruct (Nat.eq_dec q 0) as [->|Q].
 { intros ((b & c & BC & B & C),_). apply LeftExt_letter in B, C. lia. }
 intros (LS,NLS) X IN.
 assert (E : exists u' r, u = u' ++ repeat q r /\ last u' 0 <> q /\ (r=0\/r=1)).
 { destruct (Nat.eq_dec (last u 0) q) as [E|N].
   - assert (N : u <> []) by (intros ->; inversion IN).
     assert (U' := app_removelast_last 0 N).
     set (u' := removelast u) in *. clearbody u'. rewrite E in *. clear N E.
     exists u', 1; repeat split; trivial; try now right. intros E'.
     assert (N' : u' <> []). { intros ->. simpl in *. now apply Q. }
     rewrite (app_removelast_last 0 N'), E', <- app_assoc in U'. simpl in U'.
     clear E' N'.
     eapply (corollary_4_6 q _ 2); trivial.
     apply observation_4_2_contra. simpl. rewrite <- U'. split; trivial.
   - exists u, 0; repeat split; trivial; try now left. simpl.
     now rewrite app_nil_r. }
 destruct E as (u' & r & E & L & R).
 assert (LS' : LeftSpecial u' (qseq q)).
 { eapply LeftSpecial_Prefix; eauto. now exists (repeat q r). }
 assert (U' : u' <> []).
 { intros ->. simpl in *. subst u. apply repeat_spec in IN; lia. }
 clear x X IN.
 destruct (lemma_3_7_ii_ls q u' L LS') as (v' & V1 & V2).
 exists v', (repeat q r); repeat split; trivial; try congruence.
 2:{ destruct R; subst; simpl; intuition. }
 (* v' is Maximal Left Special *)
 intros a A.
 assert (RS: RightSpecial u (qseq q)).
 { apply observation_4_2_contra; split; trivial. }
 destruct RS as (b & c & BC & B & C). red in B,C.
 assert (B' := NLS b).
 assert (C' := NLS c).
 assert (E' : exists b' c', b'<>c' /\
            RightExt v' b' (qseq q) /\ ~LeftSpecial (v'++[b']) (qseq q) /\
            RightExt v' c' (qseq q) /\ ~LeftSpecial (v'++[c']) (qseq q)).
 { destruct R; subst r; simpl in E; rewrite ?app_nil_r in E; subst u.
   - destruct (inv_letter_for_4_10 q u' v' b) as (b' & B1 & B2 & B3);
     destruct (inv_letter_for_4_10 q u' v' c) as (c' & C1 & C2 & C3);
       try split; trivial.
     exists b', c'; repeat split; trivial; congruence.
   - destruct (inv_letter_bis_for_4_10 q u' v' b) as (b' & B1 & B2 & B3);
     destruct (inv_letter_bis_for_4_10 q u' v' c) as (c' & C1 & C2 & C3);
       try split; trivial.
     exists b',c'; repeat split; trivial; lia. }
 clear b c BC B B' C C'.
 destruct E' as (b & c & BC & B & B' & C & C').
 assert (AB : a <> b). { intros ->. now apply B'. }
 assert (AC : a <> c). { intros ->. now apply C'. }
 assert (3 <= qrvalence q v').
 { apply LeftSpecial_SubSeq in A.
   change 3 with (length [a;b;c]).
   apply NoDup_incl_length.
   - clear -AB AC BC. repeat constructor; simpl; intuition.
   - destruct (qrightexts_ok q v') as (_,RE). clear - A B C RE.
     intros x X. simpl in X. intuition; subst x; rewrite RE; auto. }
 assert (qrvalence q v' <= 2).
 { apply qrvalence_le_2. intros ->. simpl in *. now subst. }
 lia.
Qed.

Lemma norepeat_exists (q:nat) u :
  u <> repeat q (length u) -> exists a, a<>q /\ In a u.
Proof.
 induction u as [|a u IH]; simpl; intros N; try easy.
 destruct (Nat.eq_dec a q) as [->|N']; [|exists a; tauto].
 destruct IH as (a & A & IN).
 { contradict N. now f_equal. }
 exists a; tauto.
Qed.

Lemma corollary_4_11 q u : ~MaxLeftSpecial u (qseq q).
Proof.
 remember (length u) as n eqn:N. symmetry in N. revert u N.
 induction n as [n IH] using lt_wf_ind. intros u N LS.
 destruct (norepeat_exists q u) as (x & X & IN); trivial.
 { rewrite N. intros ->. now apply (lemma_4_7 q n). }
 destruct (proposition_4_10 q u x) as (v & w & V & E & W); trivial.
 assert (L : length v < n).
 { rewrite <- N, E, app_length, len_qsubst.
   destruct V as (V,_). destruct v.
   - simpl in *. intuition; subst; simpl. inversion IN. lia.
   - apply ls_head_q in V. subst. simpl. rewrite Nat.eqb_refl. lia. }
 apply (IH (length v) L v); auto.
Qed.

(** Major property : the only LeftSpecial factors of (qseq q) are
    its prefixes. *)

Lemma LeftSpecial_qprefix q u :
  LeftSpecial u (qseq q) -> PrefixSeq u (qseq q).
Proof.
 remember (length u) as n eqn:N. revert u N.
 induction n as [n IH] using lt_wf_ind. intros u N LS.
 destruct (Nat.eq_dec n 0) as [->|N0].
 { now destruct u. }
 destruct (Nat.eq_dec n 1) as [->|N1].
 { destruct u as [|a [|b u]]; try easy. apply ls_head_q in LS. now subst a. }
 destruct (DecrLemma q u) as (v & w & V & W & E' & L); lia||auto.
 - intros _. apply NoMaxLS_exists; trivial. apply corollary_4_11.
 - rewrite <- N in L.
   specialize (IH _ L v eq_refl V). apply qsubstw_prefix in IH.
   rewrite E' in IH. eapply Prefix_PrefixSeq; eauto. now exists w.
Qed.

Lemma LeftSpecial_carac q u : q<>0 ->
  LeftSpecial u (qseq q) <-> PrefixSeq u (qseq q).
Proof.
 intros Q. split.
 - apply LeftSpecial_qprefix.
 - intros P. rewrite P. fold (qprefix q (length u)).
   apply ls_val. rewrite qprefix_qlvalence. lia.
Qed.

Lemma LeftSpecial_carac' q u : q<>0 ->
  LeftSpecial u (qseq q) <-> u = qprefix q (length u).
Proof.
 intros Q. now rewrite LeftSpecial_carac.
Qed.

(** Some leftover proofs that could only be obtained now : *)

Lemma ls_val_Sq q u : LeftSpecial u (qseq q) -> qlvalence q u = S q.
Proof.
 intros LS.
 assert (Q := ls_qnz _ _ LS).
 apply LeftSpecial_carac' in LS; trivial. rewrite LS.
 apply qprefix_qlvalence.
Qed.

Lemma lemma_3_7_i_ls_val q u :
  LeftSpecial u (qseq q) -> qlvalence q (qsubstw q u) = qlvalence q u.
Proof.
 intros LS. rewrite (ls_val_Sq _ _ LS).
 now apply ls_val_Sq, lemma_3_7_i_ls.
Qed.

Lemma qlvalence_1_or_Sq q u :
  SubSeq u (qseq q) -> qlvalence q u = 1 \/ qlvalence q u = S q.
Proof.
 intros SU. apply qlvalence_nz in SU.
 destruct (Nat.eq_dec (qlvalence q u) 1) as [E|N].
 - now left.
 - right. apply ls_val_Sq, ls_val. lia.
Qed.


(** Now that we have a unique LeftSpecial per length,
    application to factor counting and complexity. *)

Definition next_qfactors q p :=
  let f := qprefix q p in
  let l := filter (fun u => negb (listnat_eqb u f)) (qfactors q p) in
  take (S q) (fun x => x::f) ++
  map (fun u => hd 0 (qleftexts q u) :: u) l.

Lemma next_qfactors_iff q p u : q<>0 ->
  In u (next_qfactors q p) <-> In u (qfactors q (S p)).
Proof.
 intros Q.
 split.
 - rewrite qfactors_in.
   unfold next_qfactors.
   rewrite in_app_iff, in_take, in_map_iff.
   intros [(x & <- & IN)|(v & E & IN)].
   + split.
     * simpl. f_equal. apply qprefix_length.
     * destruct (qprefix_allleftexts q p) as (_,H). apply H.
       rewrite in_seq; lia.
   + rewrite filter_In in IN. destruct IN as (IN,E').
     revert E'. case listnat_eqb_spec; intros; try easy. clear E'.
     rewrite qfactors_in in IN. destruct IN as (L,IN).
     assert (NLS : ~LeftSpecial v (qseq q)).
     { now rewrite LeftSpecial_carac', L. }
     rewrite ls_val in NLS.
     assert (N := qlvalence_nz q v IN).
     assert (E' : qlvalence q v = 1) by lia. clear NLS N.
     unfold qlvalence in E'.
     destruct (qleftexts_ok q v) as (_,LE).
     destruct (qleftexts q v) as [|a [|b l]]; simpl in *; try easy.
     rewrite <- E.
     split.
     * simpl. now f_equal.
     * apply LE. now left.
 - rewrite qfactors_in. intros (L,IN).
   unfold next_qfactors. rewrite in_app_iff, in_take, in_map_iff.
   destruct u as [|a u]; try easy. simpl in L. injection L as L.
   destruct (listnat_eqb_spec u (qprefix q p)) as [->|N].
   + left. exists a; split; trivial.
     apply LeftExt_letter in IN. lia.
   + right. exists u; split; trivial.
     * f_equal.
       assert (NLS : ~LeftSpecial u (qseq q)).
       { now rewrite LeftSpecial_carac', L. }
       rewrite ls_val in NLS.
       assert (SU : SubSeq u (qseq q)).
       { eapply Sub_SubSeq; eauto. apply Sub_cons_r. }
       assert (N' := qlvalence_nz q u SU).
       assert (E : qlvalence q u = 1) by lia. clear NLS N'.
       unfold qlvalence in E.
       destruct (qleftexts_ok q u) as (_,LE).
       rewrite <- (LE a) in IN. clear LE.
       destruct (qleftexts q u) as [|b [|c ]]; simpl in *; try easy.
       intuition.
     * apply filter_In. split.
       { rewrite qfactors_in. split; trivial.
         eapply Sub_SubSeq; eauto. apply Sub_cons_r. }
       { now case listnat_eqb_spec. }
Qed.

Lemma next_qfactors_nodup q p : NoDup (next_qfactors q p).
Proof.
 apply app_nodup.
 - apply FinFun.Injective_map_NoDup; try apply seq_NoDup.
   now injection 1.
 - apply FinFun.Injective_map_NoDup.
   + now injection 1.
   + apply NoDup_filter, qfactors_nodup.
 - intros x. rewrite in_take, in_map_iff.
   intros ((a & <- & LT),(u & E & IN')).
   rewrite filter_In in IN'. destruct IN' as (IN',E').
   injection E as E1 E2.
   revert E'. now case listnat_eqb_spec.
Qed.

Lemma next_qfactors_ok q p : q<>0 ->
  Permutation (next_qfactors q p) (qfactors q (S p)).
Proof.
 intros Q.
 apply NoDup_Permutation.
 - apply next_qfactors_nodup.
 - apply qfactors_nodup.
 - intros u. now apply next_qfactors_iff.
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

Lemma next_qfactor_length q p : q<>0 ->
 length (next_qfactors q p) = length (qfactors q p) + q.
Proof.
 intros Q.
 unfold next_qfactors. rewrite app_length, take_length, map_length.
 set (f := fun u => listnat_eqb u (qprefix q p)).
 change (fun u => _) with (fun u => negb (f u)).
 rewrite <- (filter_partition_length f (qfactors q p)).
 set (l2 := filter (fun x => _) _).
 replace (filter f (qfactors q p)) with [qprefix q p]; simpl; try lia.
 symmetry. apply Permutation_length_1_inv.
 symmetry. apply NoDup_Permutation_bis.
 - apply NoDup_filter, qfactors_nodup.
 - simpl.
   apply lengthge1_carac with (qprefix q p).
   apply filter_In. split.
   + rewrite qfactors_in. split. now rewrite qprefix_length.
     eapply Sub_SubSeq. 2:apply (qprefix_leftext q p 0); try lia.
     apply Sub_cons_r.
   + unfold f. now case listnat_eqb_spec.
 - intros u. rewrite filter_In. unfold f.
   case listnat_eqb_spec.
   + intros ->. simpl. now left.
   + intros _ (_,[=]).
Qed.

Lemma qfactors_length q p : length (qfactors q p) = q*p+1.
Proof.
 destruct (Nat.eq_dec q 0) as [->|Q].
 { now rewrite qfactors_0_l. }
 induction p.
 - rewrite qfactors_0_r. simpl. lia.
 - assert (E := next_qfactors_ok q p).
   apply Permutation_length in E; trivial.
   rewrite <- E, next_qfactor_length, IHp; lia.
Qed.

Lemma qseq_complexity q : forall p, Complexity (qseq q) p (q*p+1).
Proof.
 intros p. exists (qfactors q p). split; [|split].
 - apply qfactors_nodup.
 - apply qfactors_length.
 - apply qfactors_in.
Qed.

(* Print Assumptions qseq_complexity. *)
