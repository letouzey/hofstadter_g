From Coq Require Import Bool Arith Lia Permutation FinFun List ZArith.
From QuantumLib Require Permutations.
Require Import MoreList.
Import Basics ListNotations.

Module QPerm := QuantumLib.Permutations.

(** Full and bounded equality between functions *)

Definition fEq (f g : nat->nat) := forall x, f x = g x.

Definition bEq n (f f':nat->nat) := forall x, x < n -> f x = f' x.

(** Convert between permutation as list and permutation as functions *)

Definition perm2list n (f:nat->nat) := map f (seq 0 n).

Definition perm2fun (l:list nat) := fun k => nth k l O.

Lemma perm2list_ext n f g : bEq n f g -> perm2list n f = perm2list n g.
Proof.
 intros E. apply map_ext_in. intros a. rewrite in_seq. intro IN. now apply E.
Qed.

Lemma perm2list_perm2fun n l : length l = n -> perm2list n (perm2fun l) = l.
Proof.
 revert n.
 induction l.
 - simpl. intros n <-. now unfold perm2list, perm2fun.
 - simpl. intros n <-. unfold perm2list, perm2fun. simpl. f_equal.
   rewrite <- seq_shift. rewrite map_map. now apply IHl.
Qed.

Lemma perm2fun_perm2list n f : bEq n (perm2fun (perm2list n f)) f.
Proof.
 intros x Hx.
 unfold perm2fun, perm2list.
 rewrite nth_indep with (d' := f O).
 2:{ now rewrite map_length, seq_length. }
 rewrite map_nth. f_equal. now apply seq_nth.
Qed.

(** Three possible definition of n-permutations :
    [lpermutation] on lists or [fpermutation on functions (the Coq way) or
    [qpermutation] on functions (QuantumLib's way). *)

Definition lpermutation n l := Permutation l (seq 0 n).

Definition fpermutation n (f:nat->nat) := bFun n f /\ bInjective n f.

Definition qpermutation := QPerm.permutation.

(** Interaction between QuantumLib's permutation and FinFun *)

Lemma q_f_permutation n (f:nat->nat) : qpermutation n f <-> fpermutation n f.
Proof.
 split; intros Hf.
 - split. firstorder. red. now apply QPerm.permutation_is_injective.
 - destruct Hf as (Hf1,Hf2).
   assert (Hf3 : bSurjective n f) by now apply bInjective_bSurjective.
   apply bSurjective_bBijective in Hf3; trivial.
   destruct Hf3 as (g & Hg & H). exists g; firstorder.
Qed.

Lemma qpermutation_id n : qpermutation n id.
Proof.
 exists id. intros x Hx. unfold id; firstorder.
Qed.

(** Interaction between QuantumLib's permutation
    and Coq's Permutation predicate on lists *)

Lemma q_l_permutation n f :
 qpermutation n f -> lpermutation n (perm2list n f).
Proof.
 intros Hf. unfold lpermutation.
 destruct (proj1 (q_f_permutation n f) Hf) as (Hf1,Hf2).
 set (f' := fun k => if k <? n then f k else k).
 rewrite perm2list_ext with (g:=f').
 2:{ intros a Ha. unfold f'. apply Nat.ltb_lt in Ha. now rewrite Ha. }
 apply nat_bijection_Permutation.
 - intros x Hx. unfold f'. specialize (Hf1 x Hx). case Nat.ltb_spec; lia.
 - intros x y. unfold f'. do 2 case Nat.ltb_spec; intros Hy Hx; trivial.
   + now apply Hf2.
   + specialize (Hf1 x Hx). lia.
   + specialize (Hf1 y Hy). lia.
Qed.

(** Conversely, from lpermutation to qpermutation : let's build the inverse
    function. *)

Definition lqinv (l:list nat) : nat -> nat := fun k => index k l.
Definition linv n (l:list nat) : list nat := perm2list n (lqinv l).
Definition qinv n (f:nat->nat) : nat -> nat := lqinv (perm2list n f).

Lemma l_q_permutation n l : lpermutation n l -> qpermutation n (perm2fun l).
Proof.
 intros Hl. unfold lpermutation, perm2fun in *.
 assert (Hn : length l = n).
 { rewrite <- (seq_length n 0). now apply Permutation_length. }
 exists (lqinv l).
 intros x Hx.
 assert (IN : In x l).
 { apply Permutation_in with (l:=seq 0 n); auto with *.
   apply in_seq; lia. }
 repeat split.
 - assert (IN' : In (nth x l O) l) by (apply nth_In; lia).
   apply Permutation_in with (l':=seq 0 n) in IN'; trivial.
   apply in_seq in IN'. lia.
 - rewrite <- Hn. now apply index_lt_len.
 - apply index_nth; try lia.
   apply Permutation_NoDup with (l:=seq 0 n); auto with *. apply seq_NoDup.
 - now apply nth_index.
Qed.

Lemma qinv_bfun n f : qpermutation n f -> bFun n (qinv n f).
Proof.
 intros Hf x Hx.
 unfold qinv, lqinv, perm2list.
 set (l := map f (seq 0 n)).
 replace n with (length l).
 2:{ unfold l. now rewrite map_length, seq_length. }
 apply index_lt_len.
 { apply Permutation_in with (l:=seq 0 n).
   apply Permutation_sym. now apply q_l_permutation.
   apply in_seq; lia. }
Qed.

Lemma qinv_left_inverse n f :
  qpermutation n f -> forall x, x<n -> qinv n f (f x) = x.
Proof.
 intros Hf x Hx.
 unfold qinv, lqinv, perm2list.
 set (l := map f (seq 0 n)).
 assert (length l = n).
 { unfold l. now rewrite map_length, seq_length. }
 replace (f x) with (nth x l 0).
 2:{ rewrite nth_indep with (d' := f 0) by lia.
     unfold l. rewrite map_nth, seq_nth; simpl; lia. }
 rewrite index_nth; try lia.
 apply Permutation_NoDup with (l:=seq 0 n); auto using seq_NoDup.
 apply Permutation_sym. now apply q_l_permutation.
Qed.

Lemma qinv_right_inverse n f :
  qpermutation n f -> forall x, x<n -> f (qinv n f x) = x.
Proof.
 intros Hf x Hx.
 unfold qinv, lqinv, perm2list.
 set (l := map f (seq 0 n)).
 assert (Hl : length l = n).
 { unfold l. now rewrite map_length, seq_length. }
 assert (IN : In x l).
 { apply Permutation_in with (l:=seq 0 n).
   apply Permutation_sym. now apply q_l_permutation.
   apply in_seq; lia. }
 replace (f (index x l)) with (nth (index x l) l 0).
 2:{ set (y := index x l).
     assert (y < n). { unfold y. rewrite <- Hl. now apply index_lt_len. }
     rewrite nth_indep with (d' := f 0).
     unfold l. rewrite map_nth, seq_nth; simpl; trivial. lia. }
 now apply nth_index.
Qed.

Lemma qinv_permutation n f :
  qpermutation n f -> qpermutation n (qinv n f).
Proof.
 intros Hf. exists f. intros x Hx; repeat split.
 - now apply qinv_bfun.
 - destruct Hf as (q,Hq). now apply Hq.
 - now apply qinv_right_inverse.
 - now apply qinv_left_inverse.
Qed.

Lemma qinv_unique_left_inverse n f g :
  qpermutation n f -> (forall x, x<n -> g (f x) = x) -> bEq n g (qinv n f).
Proof.
 intros Hf Hg x Hx.
 rewrite <- (qinv_right_inverse n f Hf x Hx) at 1. rewrite Hg; trivial.
 now apply qinv_bfun.
Qed.

Lemma qinv_unique_right_inverse n f g :
  qpermutation n f -> bFun n g -> (forall x, x<n -> f (g x) = x) ->
  bEq n g (qinv n f).
Proof.
 intros Hf Hg Hg' x Hx.
 assert (Hf' := Hf). apply q_f_permutation in Hf'. apply Hf'.
 - now apply Hg.
 - now apply qinv_bfun.
 - rewrite Hg', qinv_right_inverse; auto.
Qed.

Lemma linv_qinv n l :
 length l = n ->
 bEq n (perm2fun (linv n l)) (qinv n (perm2fun l)).
Proof.
 intros L.
 unfold linv, qinv.
 rewrite perm2list_perm2fun; auto.
 intros x Hx. rewrite perm2fun_perm2list; auto.
Qed.

Lemma linv_lperm n l : lpermutation n l -> lpermutation n (linv n l).
Proof.
 intros Hl.
 rewrite <- (perm2list_perm2fun n l).
 2:{ apply Permutation_length in Hl. now rewrite seq_length in Hl. }
 now apply q_l_permutation, qinv_permutation, l_q_permutation.
Qed.

Lemma linv_invo n l :
 lpermutation n l -> linv n (linv n l) = l.
Proof.
 intros Hl. unfold linv. symmetry.
 rewrite <- (perm2list_perm2fun n l).
 2:{ apply Permutation_length in Hl. now rewrite seq_length in Hl. }
 apply perm2list_ext.
 apply l_q_permutation in Hl.
 set (f := perm2fun l) in *.
 change (bEq n f (qinv n (qinv n f))).
 apply qinv_unique_left_inverse.
 - now apply qinv_permutation.
 - now apply qinv_right_inverse.
Qed.

(** Enumeration of all permutations of [seq 0 n] (in the form of lists) *)

Fixpoint allinserts {A} (x:A) l :=
 match l with
 | [] => [[x]]
 | y::l' => (x::l)::(map (cons y) (allinserts x l'))
 end.

Fixpoint allperms {A} (l:list A) :=
 match l with
 | [] => [[]]
 | x::l => flat_map (allinserts x) (allperms l)
 end.

Definition lperms n := allperms (seq 0 n).

Definition qperms n := map perm2fun (lperms n).

(** Correctness of [inserts], [perms], [lperms] *)

Definition Insert {A} (x:A) l l' :=
 exists l1 l2, l=l1++l2 /\ l'=l1++x::l2.

Lemma allinserts_spec {A} (x:A) l l' :
 In l' (allinserts x l) <-> Insert x l l'.
Proof.
 revert l'.
 induction l as [|y l IH]; intros l'; simpl; split.
 - intros [<-|[]]. now exists [], [].
 - intros (l1 & l2 & E & ->). left.
   symmetry in E. apply app_eq_nil in E. now destruct E as (->,->).
 - intros [<-|IN].
   + now exists [], (y::l).
   + rewrite in_map_iff in IN. destruct IN as (r & <- & IN).
     rewrite IH in IN. destruct IN as (l1 & l2 & -> & ->).
     now exists (y::l1), l2.
 - intros (l1 & l2 & E & E').
   destruct l1 as [|x1 l1].
   + left. simpl in *. now rewrite E', E.
   + right. rewrite in_map_iff.
     simpl in E. injection E as <- E.
     exists (l1++x::l2). split; auto. rewrite IH. now exists l1, l2.
Qed.

Lemma allperms_spec {A} (l:list A) l' :
  In l' (allperms l) <-> Permutation l l'.
Proof.
 revert l'.
 induction l as [|x l IH]; intros l'; simpl; split.
 - intros [<-|[]]; auto.
 - intros H. apply Permutation_nil in H. now left.
 - rewrite in_flat_map. intros (r & IN & IN').
   rewrite IH in IN. rewrite allinserts_spec in IN'.
   destruct IN' as (l1 & l2 & -> & ->).
   now apply Permutation_cons_app.
 - intros H.
   assert (IN : In x l').
   { eapply Permutation_in; eauto. simpl; auto. }
   apply in_split in IN. destruct IN as (l1 & l2 & ->).
   apply Permutation_cons_app_inv in H.
   apply IH in H.
   rewrite in_flat_map. exists (l1++l2); split; auto.
   rewrite allinserts_spec. now exists l1, l2.
Qed.

Lemma lperms_ok n l :
 In l (lperms n) <-> lpermutation n l.
Proof.
 unfold lperms. rewrite allperms_spec. now rewrite Permutation_sym_iff.
Qed.

Lemma qperms_ok1 n f :
 In f (qperms n) -> qpermutation n f.
Proof.
 unfold qperms. rewrite in_map_iff.
 intros (l & <- & IN). now apply l_q_permutation, lperms_ok.
Qed.

Lemma qperms_ok2 n f :
 qpermutation n f -> exists f', In f' (qperms n) /\ bEq n f f'.
Proof.
 intros Hf. exists (perm2fun (perm2list n f)). split.
 - unfold qperms. now apply in_map, lperms_ok, q_l_permutation.
 - unfold bEq, perm2fun, perm2list. intros x Hx.
   rewrite nth_indep with (d':=f 0) by now rewrite map_length, seq_length.
   rewrite map_nth, seq_nth; auto with *.
Qed.

(** [allinserts], [allperms], [lperms] produce lists without duplicates *)

Lemma allinserts_nodup {A} (x:A) l : ~In x l -> NoDup (allinserts x l).
Proof.
 induction l as [|y l IH]; simpl.
 - intros _. constructor; auto. constructor.
 - intros H. constructor.
   + rewrite in_map_iff. intros (l' & [= E _] & _). intuition.
   + apply Injective_map_NoDup; auto. congruence.
Qed.

Lemma allperms_nodup {A} (l:list A) : NoDup l -> NoDup (allperms l).
Proof.
 induction l as [|x l IH]; simpl.
 - intros _. constructor; auto. constructor.
 - inversion_clear 1.
   apply flat_map_nodup; auto.
   + intros a Ha. apply allinserts_nodup.
     rewrite allperms_spec in Ha. apply Permutation_sym in Ha.
     contradict H0. eapply Permutation_in; eauto.
   + intros a a' IN IN' NE b (IN1,IN2).
     rewrite allperms_spec in IN, IN'.
     rewrite allinserts_spec in IN1,IN2.
     destruct IN1 as (l1 & l2 & E1 & E2).
     destruct IN2 as (l1' & l2' & -> & ->). subst a.
     apply NE. apply split_inv in E2.
     * now f_equal.
     * contradict H0. apply Permutation_sym in IN'.
       eapply Permutation_in in IN'; eauto. apply in_app_iff; auto.
     * contradict H0. apply Permutation_sym in IN.
       eapply Permutation_in in IN; eauto. apply in_app_iff; auto.
Qed.

Lemma lperms_nodup n : NoDup (lperms n).
Proof.
 apply allperms_nodup, seq_NoDup.
Qed.

(** lengths of [allinserts], [allperms], [lperms] *)

Lemma allinserts_length {A} (x:A) l : length (allinserts x l) = S (length l).
Proof.
 induction l as [|y l IH]; simpl; trivial.
 f_equal. now rewrite map_length.
Qed.

Lemma allperms_length {A} (l:list A) : length (allperms l) = fact (length l).
Proof.
 induction l as [|x l IH]; simpl; trivial.
 rewrite flat_map_length with (k := S (length l)).
 rewrite IH. lia.
 intros a Ha. rewrite allinserts_length. f_equal.
 now apply Permutation_length, Permutation_sym, allperms_spec.
Qed.

Lemma lperms_length n : length (lperms n) = fact n.
Proof.
 unfold lperms. now rewrite allperms_length, seq_length.
Qed.

Lemma qperms_length n : length (qperms n) = fact n.
Proof.
 unfold qperms. now rewrite map_length, lperms_length.
Qed.

(** The inverse permutations also enumerate all permutations *)

Lemma lperms_inv_permut n :
  Permutation (lperms n) (map (linv n) (lperms n)).
Proof.
 apply NoDup_Permutation_bis; auto using lperms_nodup.
 - rewrite map_length; lia.
 - intros l Hl. rewrite lperms_ok in Hl.
   apply in_map_iff. exists (linv n l); split; auto using linv_invo.
   now apply lperms_ok, linv_lperm.
Qed.


(** Sign of a permutation *)

Fixpoint inversions l :=
 match l with
 | [] => 0
 | x::l => length (filter (fun y => y <? x) l) + inversions l
 end.

Definition lsign l := Nat.even (inversions l).

Definition qsign n f := lsign (perm2list n f).

Lemma qsign_ext n f g : bEq n f g -> qsign n f = qsign n g.
Proof.
 intros E. unfold qsign. f_equal. now apply perm2list_ext.
Qed.

(** Another definition, via iterated xor *)

Fixpoint bigxor {A} (f:A->bool) l :=
 match l with
 | [] => false
 | x::l => xorb (f x) (bigxor f l)
 end.

Lemma bigxor_app {A} (f:A->bool) l1 l2 :
 bigxor f (l1++l2) = xorb (bigxor f l1) (bigxor f l2).
Proof.
 induction l1; simpl; trivial.
 - now destruct bigxor.
 - now rewrite IHl1, xorb_assoc.
Qed.

Lemma bigxor_map {A B} (h:A->B)(f:B->bool) l :
 bigxor f (map h l) = bigxor (compose f h) l.
Proof.
 induction l; simpl; trivial. rewrite IHl. f_equal.
Qed.

Fixpoint lsign' l :=
 match l with
 | [] => true
 | x::l => xorb (bigxor (fun y => y <? x) l) (lsign' l)
 end.

Lemma lsign'_alt x l :
  lsign' (l++[x]) = xorb (lsign' l) (bigxor (fun y => x <? y) l).
Proof.
 induction l; simpl; trivial. rewrite bigxor_app, IHl. simpl.
 rewrite xorb_false_r.
 rewrite !xorb_assoc. f_equal.
 rewrite <- !xorb_assoc. f_equal. apply xorb_comm.
Qed.

Lemma eqb_xorb b b' : eqb b b' = negb (xorb b b').
Proof.
 now destruct b, b'.
Qed.

Lemma eqb_xorb' b b' : eqb b b' = xorb (negb b) b'.
Proof.
 now destruct b, b'.
Qed.

Lemma lsign_equiv l : lsign l = lsign' l.
Proof.
 unfold lsign.
 induction l; simpl; auto.
 rewrite Nat.even_add, IHl.
 rewrite eqb_xorb'. f_equal.
 rewrite Nat.negb_even. clear IHl.
 induction l; simpl; trivial.
 case Nat.ltb_spec; intros; simpl.
 - rewrite Nat.odd_succ, <- Nat.negb_odd, IHl. now destruct bigxor.
 - rewrite IHl. now destruct bigxor.
Qed.

(** Signature of the identity permutation *)

Lemma inversions_id i n : inversions (seq i n) = 0.
Proof.
 revert i.
 induction n; simpl; intros i; auto.
 rewrite IHn.
 rewrite Nat.add_0_r.
 apply length_zero_iff_nil, nil_carac. intros x.
 rewrite filter_In, in_seq. intros (H,H').
 apply Nat.ltb_lt in H'. lia.
Qed.

Lemma lsign_id n : lsign (seq 0 n) = true.
Proof.
 unfold lsign. now rewrite inversions_id.
Qed.

Lemma qsign_id n : qsign n id = true.
Proof.
 unfold qsign, perm2list. rewrite map_id. apply lsign_id.
Qed.

(** incrpairs : all pairs [(i,j)] with [0<=i<j<n] *)

Fixpoint incrpairs n :=
  match n with
  | O => []
  | S n => incrpairs n ++ map (fun k => (k,n)) (seq 0 n)
  end.

(* Finally unused, a "symmetric" version of incrpairs :
Definition decrpairs n := map (fun '(i,j) => (j,i)) (incrpairs n).
Definition diffpairs n := incrpairs n ++ decrpairs n.
Lemma diffpairs_countocc n i j :
 count_occ natnatdec (diffpairs n) (i,j) =
  if (j <? n) && (i <? n) && negb (i =? j) then 1 else 0.
Lemma permut_diffpairs n f :
  qpermutation n f ->
  Permutation (diffpairs n) (map (couple f) (diffpairs n)).
*)

Definition natnatdec (p q : nat*nat) : { p = q }+{ p<> q }.
Proof.
 decide equality; apply Nat.eq_dec.
Defined.

Lemma mapincr_countocc n m i j :
  count_occ natnatdec (map (fun k : nat => (k, m)) (seq 0 n)) (i, j) =
  if (i <? n) && (j =? m) then 1 else 0.
Proof.
 revert m i j.
 induction n; intros.
 - simpl count_occ.
   case Nat.ltb_spec; simpl; auto. inversion 1.
 - rewrite seq_S, map_app, count_occ_app.
   cbn -[natnatdec]. rewrite IHn.
   destruct natnatdec as [[= -> ->]|NE].
   + now rewrite Nat.eqb_refl, Nat.ltb_irrefl, Nat.leb_refl.
   + case Nat.ltb_spec; case Nat.eqb_spec; case Nat.leb_spec; intros;
       simpl; auto. lia. subst. replace i with n in NE by lia. easy.
Qed.

Lemma incrpairs_countocc n i j :
  count_occ natnatdec (incrpairs n) (i,j) =
  if (i <? j) && (j <? n) then 1 else 0.
Proof.
 revert i j.
 induction n; simpl; intros.
 - do 2 case Nat.ltb_spec; intros; simpl; auto; lia.
 - rewrite count_occ_app, IHn.
   rewrite mapincr_countocc.
   repeat (case Nat.ltb_spec; intros; simpl; auto; try lia);
    case Nat.eqb_spec; intros; simpl; auto; try lia.
Qed.

Lemma incrpairs_in n i j :
  In (i,j) (incrpairs n) <-> i < j < n.
Proof.
 rewrite count_occ_In with (eq_dec:=natnatdec).
 rewrite incrpairs_countocc.
 repeat (case Nat.ltb_spec; simpl; try lia).
Qed.

Definition couple (g:nat->nat) '(i,j) := (g i, g j).
Definition sortpair '(i,j) := if i <? j then (i,j) else (j,i).
Definition sortedcouple g p := sortpair (couple g p).

Lemma permut_incrpairs_sorted n f :
 qpermutation n f ->
 Permutation (map (sortedcouple f) (incrpairs n)) (incrpairs n).
Proof.
 intros Q.
 apply Permutation_sym.
 apply NoDup_Permutation_bis.
 - rewrite NoDup_count_occ with (decA := natnatdec). intros (i,j).
   rewrite incrpairs_countocc.
   repeat (case Nat.ltb_spec; simpl; trivial); lia.
 - now rewrite map_length.
 - intros (i,j). rewrite incrpairs_in. intros H.
   destruct Q as (g & Hg).
   generalize (Hg i) (Hg j); intros.
   rewrite in_map_iff. exists (sortedcouple g (i,j)). split.
   + unfold sortedcouple, sortpair, couple.
     do 2 case Nat.ltb_spec; intros; f_equal; try lia.
   + unfold sortedcouple, sortpair, couple.
     case Nat.ltb_spec; intros; rewrite incrpairs_in; split; try lia.
     assert (g i <> g j); try lia.
     intros E. replace i with (f (g i)) in H by lia.
     replace j with (f (g j)) in H by lia. rewrite E in H. lia.
Qed.

(** Product in Z of the map of a list *)

Local Open Scope Z.

Fixpoint zPi {A} (f:A->Z) l :=
  match l with
   | [] => 1
   | x::l => f x * zPi f l
  end.

Lemma zPi_app {A} (f:A->Z) l1 l2 :
  zPi f (l1++l2) = zPi f l1 * zPi f l2.
Proof.
 induction l1; simpl zPi; rewrite ?IHl1; lia.
Qed.

Lemma zPi_map {A B} (f:B->Z) (h:A->B) l :
 zPi f (map h l) = zPi (compose f h) l.
Proof.
 induction l; simpl; auto. now rewrite IHl.
Qed.

Lemma zPi_permut {A} (f:A->Z) l l' :
  Permutation l l' -> zPi f l = zPi f l'.
Proof.
 induction 1; simpl; auto; try lia.
Qed.

Lemma zPi_ext {A} (f g : A -> Z) l :
 (forall x, In x l -> f x = g x) -> zPi f l = zPi g l.
Proof.
 induction l; simpl; auto. intros H. rewrite IHl by firstorder. f_equal.
 apply H; now left.
Qed.

Lemma zPi_mult {A} (f g : A -> Z) l :
 zPi (fun x => f x * g x) l = zPi f l * zPi g l.
Proof.
 induction l; simpl; auto. rewrite IHl. lia.
Qed.

Lemma zPi_pos {A} (f:A->Z) l :
  (forall x, In x l -> 0 < f x) -> 0 < zPi f l.
Proof.
 induction l; simpl; auto; try lia.
 intros H. apply Z.mul_pos_pos. apply H; now left. apply IHl; firstorder.
Qed.

Lemma zPi_bigxor {A}(f:A->Z)(g:A->bool) l :
 (forall x, In x l -> f x = if g x then -1 else 1) ->
  zPi f l = if bigxor g l then -1 else 1.
Proof.
 intros H.
 induction l; simpl; auto.
 rewrite (H a) by (now left). rewrite IHl by (simpl in *; firstorder).
 destruct (g a), (bigxor g l); simpl; try lia.
Qed.

(** Signature expressed as (-1) or 1, hence in Z *)

Local Coercion Z.of_nat : nat >-> Z.

Definition zsign n (f:nat->nat) : Z :=
  zPi (fun '(i,j) => Z.sgn (f j - f i)) (incrpairs n).

Lemma zsign_ok n f : bInjective n f ->
 zsign n f = if qsign n f then 1 else -1.
Proof.
 unfold zsign, qsign, perm2list. rewrite lsign_equiv. revert f.
 induction n as [|n IH]; intros f Hf; trivial.
 rewrite seq_S, map_app. cbn. rewrite zPi_app. rewrite IH by firstorder.
 rewrite lsign'_alt. rewrite bigxor_map, zPi_map. unfold compose.
 rewrite zPi_bigxor with (g := fun x : nat => (f n <? f x)%nat).
 destruct lsign', bigxor; simpl; try lia.
 intros x. clear IH. rewrite in_seq. intros Hx.
 case Nat.ltb_spec. lia. specialize (Hf x n); lia.
Qed.

Lemma zsign_0 (f:nat->nat) : zsign 0 f = 1.
Proof.
 unfold zsign. now simpl.
Qed.

Lemma zsign_1 (f:nat->nat) : zsign 1 f = 1.
Proof.
 unfold zsign. now simpl.
Qed.

Lemma zsign_id n : zsign n id = 1.
Proof.
 rewrite zsign_ok, qsign_id; firstorder.
Qed.

Lemma zsign_ext n f f' : bEq n f f' -> zsign n f = zsign n f'.
Proof.
 intros E. unfold zsign. apply zPi_ext. intros (i,j).
 rewrite incrpairs_in. intros H.
 rewrite <- (E i), <- (E j); lia.
Qed.

Lemma zPi_reindex_comm n (F : nat*nat -> Z) g :
 qpermutation n g -> (forall i j, F (j,i) = F (i,j)) ->
 zPi (compose F (couple g)) (incrpairs n) = zPi F (incrpairs n).
Proof.
 intros Hg HF.
 rewrite zPi_ext with (g := compose F (sortedcouple g)).
 2:{ intros (i,j) IN. rewrite incrpairs_in in IN.
     unfold compose, sortedcouple, couple, sortpair.
     case Nat.ltb_spec; intros; trivial. }
 rewrite <- zPi_map. apply zPi_permut. now apply permut_incrpairs_sorted.
Qed.

Lemma sign_move (a b c : Z) : b=1\/b=-1 -> a*b = c -> a = b*c.
Proof.
 lia.
Qed.

Lemma zPi_reindex_anticomm n (F : nat*nat -> Z) g :
 qpermutation n g -> (forall i j, F (j,i) = - F (i,j)) ->
 zPi (compose F (couple g)) (incrpairs n) = zsign n g * zPi F (incrpairs n).
Proof.
 intros Hg HF. apply sign_move.
 { rewrite zsign_ok.
   destruct qsign; lia. apply q_f_permutation in Hg. apply Hg. }
 unfold zsign.
 rewrite <- zPi_mult.
 rewrite zPi_ext with (g := compose F (sortedcouple g)).
 2:{ intros (i,j) IN. rewrite incrpairs_in in IN.
     unfold compose, sortedcouple, couple, sortpair.
     case Nat.ltb_spec; intros. lia.
     assert (g j <> g i).
     { intros E. apply q_f_permutation in Hg. apply Hg in E; lia. }
     rewrite HF. lia. }
 rewrite <- zPi_map. apply zPi_permut. now apply permut_incrpairs_sorted.
Qed.

Definition subpair : nat*nat -> Z := fun '(i,j) =>  j - i.

Lemma zsign_eqn n f : qpermutation n f ->
 zsign n f * zPi subpair (incrpairs n) =
  zPi (fun '(i,j) => f j - f i) (incrpairs n).
Proof.
 intros Hf.
 set (F := fun '(i, j) => Z.abs (Z.of_nat j - Z.of_nat i)).
 rewrite zPi_ext with (g:=F).
 2:{ intros (i,j). rewrite incrpairs_in. unfold subpair, F. lia. }
 rewrite <- zPi_reindex_comm  with (g:=f); trivial.
 2:{ intros i j. unfold F. lia. }
 unfold zsign. rewrite <- zPi_mult. apply zPi_ext.
 { intros (i,j) _. unfold compose; simpl; lia. }
Qed.

Lemma zsign_altdef n f : qpermutation n f ->
 zsign n f =
  zPi (fun '(i,j) => f j - f i) (incrpairs n) / zPi subpair (incrpairs n).
Proof.
 intros.
 rewrite <- zsign_eqn by trivial. symmetry. apply Z.div_mul.
 assert (0 < zPi subpair (incrpairs n)); try lia.
 { apply zPi_pos. intros (i,j). rewrite incrpairs_in. unfold subpair. lia. }
Qed.

Lemma zsign_compose n f g :
 qpermutation n f -> qpermutation n g ->
 zsign n (compose f g) = zsign n f * zsign n g.
Proof.
 intros Hf Hg.
 assert (Hfg : qpermutation n (compose f g))
   by now apply QPerm.permutation_compose.
 assert (E := zsign_eqn _ _ Hfg).
 unfold compose at 2 3 in E. symmetry in E.
 set (F := fun '(i,j) => f j - f i).
 rewrite zPi_ext with (g:=compose F (couple g)) in E.
 2:{ intros (i,j) _. unfold compose; simpl; lia. }
 rewrite zPi_reindex_anticomm in E; trivial.
 2:{ intros i j. unfold F. lia. }
 unfold F in E. rewrite <- zsign_eqn in E by trivial.
 rewrite Z.mul_assoc in E. apply Z.mul_reg_r in E; try lia.
 assert (0 < zPi subpair (incrpairs n)); try lia.
 { apply zPi_pos. intros (i,j). rewrite incrpairs_in. unfold subpair. lia. }
Qed.

Lemma zsign_qinv n f : qpermutation n f -> zsign n (qinv n f) = zsign n f.
Proof.
 intros Hf.
 assert (E := zsign_compose n f (qinv n f) Hf (qinv_permutation n f Hf)).
 rewrite zsign_ext with (f':=id) in E.
 rewrite zsign_id in E. symmetry in E; rewrite Z.mul_comm in E.
 apply sign_move in E; try lia.
 rewrite zsign_ok. destruct qsign; lia. apply q_f_permutation in Hf. apply Hf.
 intros x Hx. now apply qinv_right_inverse.
Qed.

Local Close Scope Z.

(** Permutations and transpositions *)

Definition transpo '(i,j) := fun n =>
  if n =? i then j else if n =? j then i else n.

Lemma transpo_fperm n i j :
  i < n -> j < n -> fpermutation n (transpo (i,j)).
Proof.
 intros Hi Hj. split.
 - intros x Hx. unfold transpo.
   repeat (case Nat.eqb_spec; try lia).
 - intros x y Hx Hy. unfold transpo.
   repeat (case Nat.eqb_spec; try lia).
Qed.

Lemma transpo_qperm n i j :
  i < n -> j < n -> qpermutation n (transpo (i,j)).
Proof.
 intros. now apply q_f_permutation, transpo_fperm.
Qed.

Lemma transpo_invo i j :
  fEq (compose (transpo (i,j)) (transpo (i,j))) id.
Proof.
 intros x.
 unfold transpo, compose, id.
 repeat (case Nat.eqb_spec; simpl); lia.
Qed.

Lemma transpo_comm i j :
 fEq (transpo (j,i)) (transpo (i,j)).
Proof.
 intros x. unfold transpo.
 do 2 case Nat.eqb_spec; lia.
Qed.

Lemma transpo_l i j : transpo (i,j) i = j.
Proof.
 unfold transpo. now rewrite Nat.eqb_refl.
Qed.

Lemma transpo_r i j : transpo (i,j) j = i.
Proof.
 unfold transpo. case Nat.eqb_spec; try lia. now rewrite Nat.eqb_refl.
Qed.

Lemma transpo_else i j x : x<>i -> x<>j -> transpo (i,j) x = x.
Proof.
 unfold transpo. intros Hi Hj.
 case Nat.eqb_spec; intros; try lia.
 case Nat.eqb_spec; intros; try lia.
Qed.

Fixpoint ltranspo (l : list (nat*nat)) :=
  match l with
  | [] => fun x => x
  | ij::l => compose (transpo ij) (ltranspo l)
  end.

Lemma ltranspo_one i j : fEq (ltranspo [(i,j)]) (transpo (i,j)).
Proof.
 intros x. cbn -[transpo]. now unfold compose.
Qed.

Lemma ltranspo_app l1 l2 :
 fEq (ltranspo (l1++l2)) (compose (ltranspo l1) (ltranspo l2)).
Proof.
 intros x; unfold compose.
 induction l1; simpl; trivial. unfold compose. now rewrite IHl1.
Qed.

Lemma ltranspo_qperm n l :
 Forall (fun '(i,j) => i < j < n) l -> qpermutation n (ltranspo l).
Proof.
 induction 1; simpl.
 - apply qpermutation_id.
 - destruct x as (i,j).
   apply QPerm.permutation_compose; auto. apply transpo_qperm; lia.
Qed.

Fixpoint transposify n f :=
 match n with
 | 0 => []
 | S n =>
   if f n =? n then transposify n f
   else (f n, n)::transposify n (compose (transpo (f n, n)) f)
 end.

Lemma subpermut_1 n f :
 fpermutation (S n) f -> f n = n -> fpermutation n f.
Proof.
 intros (Hf1,Hf2) E. split; [|firstorder].
 intros x Hx.
 assert (f x < S n) by (specialize (Hf1 x); lia).
 assert (f x <> n); try lia.
 { rewrite <- E. intros E'. apply Hf2 in E'; lia. }
Qed.

Lemma subpermut_2 n f :
 fpermutation (S n) f -> fpermutation n (compose (transpo (f n, n)) f).
Proof.
 intros (Hf1,Hf2). split.
 - intros x Hx.
   assert (f x < S n) by (specialize (Hf1 x); lia).
   unfold compose, transpo.
   case Nat.eqb_spec; intros E.
   + apply Hf2 in E; try lia.
   + case Nat.eqb_spec; intros E'; try lia.
     specialize (Hf1 n); lia.
 - intros x y Hx Hy. unfold compose. intros E.
   apply (transpo_fperm (S n) (f n) n) in E; try apply Hf1; try lia.
   apply Hf2; lia.
Qed.

Lemma transposify_ok n f :
  fpermutation n f -> Forall (fun '(i,j) => i < j < n) (transposify n f).
Proof.
 revert f.
 induction n; intros f Hf.
 - constructor.
 - cbn -[transpo]. case Nat.eqb_spec; intros E.
   + generalize (IHn f (subpermut_1 n f Hf E)).
     apply Forall_impl. intros (i,j); lia.
   + constructor.
     * split; auto.
       destruct Hf as (Hf1,Hf2). specialize (Hf1 n). lia.
     * assert (Hf' := subpermut_2 n f Hf).
       set (f' := compose _ _) in *.
       generalize (IHn f' Hf'). apply Forall_impl. intros (i,j); lia.
Qed.

Lemma transposify_eq n f :
  fpermutation n f -> (forall x, n<=x -> f x = x) ->
  fEq f (ltranspo (transposify n f)).
Proof.
 revert f.
 induction n; intros f Hf Hf'.
 - simpl. firstorder lia.
 - cbn -[transpo]. case Nat.eqb_spec; intros E.
   + apply IHn. now apply subpermut_1.
     intros x Hx. destruct Hx; [ lia | apply Hf'; lia ].
   + cbn -[transpo].
     intro x. unfold compose. rewrite <- IHn.
     * now generalize (transpo_invo (f n) n (f x)).
     * now apply subpermut_2.
     * clear x. intros x Hx. destruct Hx.
       { simpl. now rewrite Nat.eqb_refl. }
       { rewrite (Hf' (S m)) by lia. apply transpo_else; try lia.
         assert (f n < S n) by (apply Hf; lia). lia. }
Qed.

Lemma transposify_ext n f f' :
 bEq n f f' -> transposify n f = transposify n f'.
Proof.
 revert f f'.
 induction n; intros f f' B; cbn -[transpo]; auto.
 rewrite <- (B n) by lia. case Nat.eqb_spec; intros.
 - apply IHn. firstorder.
 - f_equal. apply IHn. intros x Hx. unfold compose.
   now rewrite <- (B x) by lia.
Qed.

Lemma transposify_beq n f :
  fpermutation n f -> bEq n f (ltranspo (transposify n f)).
Proof.
 intros Hf.
 set (f' := fun k => if k <? n then f k else k).
 assert (bEq n f f').
 { intros x Hx. unfold f'. apply Nat.ltb_lt in Hx. now rewrite Hx. }
 rewrite transposify_ext with (f':=f'); trivial.
 intros x Hx. rewrite H by trivial. apply transposify_eq; clear x Hx.
 - destruct Hf as (Hf1,Hf2). split.
   + intros x Hx. unfold f'. specialize (Hf1 x Hx). case Nat.ltb_spec; lia.
   + intros x y. unfold f'. do 2 case Nat.ltb_spec; intros Hy Hx; trivial.
     * now apply Hf2.
     * specialize (Hf1 x Hx). lia.
     * specialize (Hf1 y Hy). lia.
 - unfold f'. intros x Hx. case Nat.ltb_spec; lia.
Qed.

Lemma transpo_simplify i j :
 0<i<j -> fEq (transpo (i,j)) (ltranspo [(0,i);(0,j);(0,i)]).
Proof.
 intros H x. unfold ltranspo, transpo, compose.
 repeat (case Nat.eqb_spec; simpl; try lia).
Qed.

Lemma perm2list_transpo0 n j :
 0<j<n ->
 perm2list n (transpo (0,j)) =
  [j] ++ seq 1 (j-1) ++ [0] ++ seq (S j) (n-j-1).
Proof.
 intros H.
 unfold perm2list.
 replace n with (j+(n-j)) at 1 by lia.
 rewrite seq_app, map_app.
 replace j with (S (j-1)) at 2 by lia.
 replace (n-j) with (S (n-j-1)) at 1 by lia.
 simpl seq. cbn -[transpo].
 rewrite transpo_l. f_equal. f_equal.
 rewrite map_ext_in with (g := id). now rewrite map_id.
 intros a. rewrite in_seq. intros Ha. rewrite transpo_else; auto; lia.
 rewrite transpo_r. f_equal.
 rewrite map_ext_in with (g := id). now rewrite map_id.
 intros a. rewrite in_seq. intros Ha. rewrite transpo_else; auto; lia.
Qed.

Lemma inversions_app_adhoc x u v :
 (forall y z, In y u -> In z v -> y < z) ->
 inversions (u++x::v) =
 inversions u + inversions (x::v) + length (filter (fun y => x <? y) u).
Proof.
 induction u; intros H.
 - simpl; lia.
 - simpl. rewrite IHu by firstorder.
   rewrite filter_app, app_length. simpl. rewrite <- !Nat.add_assoc.
   f_equal.
   rewrite filter_nop.
   2:{ intros z IN. apply Nat.ltb_ge. generalize (H a z). simpl.
       firstorder. lia. }
   case Nat.ltb_spec; simpl; lia.
Qed.

Lemma qsign_transpo0 n j : 0<j<n -> qsign n (transpo (0,j)) = false.
Proof.
 intros H. unfold qsign, lsign.
 rewrite perm2list_transpo0; trivial. cbn -[Nat.ltb].
 rewrite filter_app. cbn -[Nat.ltb].
 replace (0<?j) with true by (symmetry; apply Nat.ltb_lt; lia).
 rewrite app_length. cbn -[Nat.ltb].
 rewrite filter_all.
 2:{ intros x. rewrite in_seq. intros Hx. apply Nat.ltb_lt. lia. }
 rewrite seq_length.
 rewrite filter_nop.
 2:{ intros x. rewrite in_seq. intros Hx. apply Nat.ltb_ge. lia. }
 simpl.
 rewrite inversions_app_adhoc.
 2:{ intros y z. rewrite !in_seq. lia. }
 rewrite filter_all.
 2:{ intros x. rewrite in_seq, Nat.ltb_lt. lia. }
 rewrite seq_length.
 simpl. rewrite !inversions_id.
 rewrite filter_nop.
 2:{ intros x. rewrite in_seq, Nat.ltb_ge. lia. }
 simpl.
 replace (j-1+1+(j-1)) with (1+2*(j-1)) by lia.
 now rewrite Nat.even_add_mul_2.
Qed.

Lemma zsign_transpo0 n j : 0<j<n -> zsign n (transpo (0,j)) = (-1)%Z.
Proof.
 intros H. rewrite zsign_ok, qsign_transpo0; auto.
 apply (transpo_fperm n 0 j); lia.
Qed.

Lemma zsign_transpo n i j : i<j<n -> zsign n (transpo (i,j)) = (-1)%Z.
Proof.
 intros H. destruct (Nat.eq_dec i 0) as [->|N].
 - now apply zsign_transpo0.
 - rewrite zsign_ext with (f' := ltranspo [(0,i);(0,j);(0,i)]).
   2:{ intros x Hx. rewrite transpo_simplify; auto. lia. }
   cbn -[transpo].
   assert (Qi : qpermutation n (transpo (0,i)))
     by (apply transpo_qperm; lia).
   assert (Qj : qpermutation n (transpo (0,j)))
     by (apply transpo_qperm; lia).
   rewrite !zsign_compose; auto.
   + rewrite !zsign_transpo0, zsign_id; lia.
   + apply qpermutation_id.
   + apply QPerm.permutation_compose; auto.
Qed.

Lemma qsign_transpo n i j : i<j<n -> qsign n (transpo (i,j)) = false.
Proof.
 intros H. generalize (zsign_transpo n i j H). rewrite zsign_ok.
 destruct qsign; auto. congruence.
 apply transpo_fperm; lia.
Qed.

Definition zparity n := if Nat.even n then 1%Z else (-1)%Z.

Lemma zsign_ltranspo n l :
 Forall (fun '(i,j) => i < j < n) l ->
 zsign n (ltranspo l) = zparity (length l).
Proof.
 induction 1; cbn -[Nat.even].
 - apply zsign_id.
 - destruct x as (i,j).
   rewrite zsign_compose, zsign_transpo, IHForall; try lia.
   2:{ apply transpo_qperm; lia. }
   2:{ apply ltranspo_qperm; auto. }
   unfold zparity.
   rewrite Nat.even_succ, <- Nat.negb_even. now destruct Nat.even.
Qed.

Lemma qsign_ltranspo n l :
 Forall (fun '(i,j) => i < j < n) l ->
 qsign n (ltranspo l) = Nat.even (length l).
Proof.
 intros H. generalize (zsign_ltranspo n l H). rewrite zsign_ok.
 unfold zparity. destruct qsign, Nat.even; auto; congruence.
 assert (F : fpermutation n (ltranspo l)).
 { now apply q_f_permutation, ltranspo_qperm. }
 apply F.
Qed.

Lemma qsign_transposify n f :
 qpermutation n f ->
 qsign n f = Nat.even (length (transposify n f)).
Proof.
 intros H. rewrite qsign_ext with (g:= ltranspo (transposify n f)).
 - now apply qsign_ltranspo, transposify_ok, q_f_permutation.
 - now apply transposify_beq, q_f_permutation.
Qed.

(** Extending / Reducing a permutation.

    Here we insert or remove a 0 somewhere and shift the rest.
    This will be used for proving the Leibniz formula about
    the determinant of matrices. *)

Definition extend_lperm i l := insert_at i O (map S l).

Definition reduce_lperm l := map pred (remove Nat.eq_dec O l).

Lemma reduce_extend_lperm i l :
 reduce_lperm (extend_lperm i l) = l.
Proof.
 unfold reduce_lperm, extend_lperm.
 rewrite remove_insert.
 - rewrite map_map. simpl. apply map_id.
 - rewrite in_map_iff. intros (x & [= ] & _).
Qed.

Lemma extend_reduce_lperm l : count_occ Nat.eq_dec l 0 = 1 ->
 extend_lperm (index O l) (reduce_lperm l) = l.
Proof.
 unfold reduce_lperm, extend_lperm. intros C.
 rewrite map_map.
 rewrite map_ext_in with (g:=fun n:nat => n).
 2:{ intros a Ha. assert (a <> O); try lia.
     intros ->. revert Ha. apply remove_In. }
 rewrite map_id.
 induction l; simpl in *; try lia.
 destruct Nat.eq_dec; subst; simpl.
 - f_equal. apply notin_remove. injection C as C.
   now apply count_occ_not_In in C.
 - destruct a as [|a]; simpl; try lia. f_equal.
   now apply IHl.
Qed.

Lemma lperm_head_count n x l :
 lpermutation n l ->
 count_occ Nat.eq_dec l x = if x <? n then 1 else 0.
Proof.
 intros L. rewrite <- count_occ_seq. now apply Permutation_count_occ.
Qed.

Lemma extend_lperm_is_lperm n i l :
 lpermutation n l -> lpermutation (S n) (extend_lperm i l).
Proof.
 unfold extend_lperm, lpermutation. simpl. intros L.
 apply perm_trans with (O :: map S l); auto using insert_permut.
 constructor. rewrite <- seq_shift. now apply Permutation_map.
Qed.

Lemma reduce_lperm_is_lperm n l :
 lpermutation (S n) l -> lpermutation n (reduce_lperm l).
Proof.
 unfold reduce_lperm, lpermutation. intros L.
 assert (IN : In O l).
 { apply Permutation_sym in L. eapply Permutation_in; eauto.
   apply in_seq; lia. }
 apply Permutation_sym.
 apply NoDup_Permutation_bis; auto using seq_NoDup.
 - apply Permutation_length in L.
   rewrite !seq_length in *.
   unfold reduce_lperm. rewrite map_length.
   apply remove_length_lt with (eq_dec:=Nat.eq_dec) in IN. lia.
 - intros x Hx. rewrite in_seq in Hx.
   unfold reduce_lperm.
   rewrite in_map_iff. exists (S x); split; trivial.
   apply in_in_remove; try lia.
   apply Permutation_sym in L. eapply Permutation_in; eauto.
   apply in_seq; lia.
Qed.

(** Another way of listing all permutations *)

Definition reorder_lperms n :=
  flat_map (fun i => map (extend_lperm i) (lperms n)) (seq 0 (S n)).

Lemma reorder_perms_ok n :
 Permutation (reorder_lperms n) (lperms (S n)).
Proof.
 apply Permutation_sym.
 apply NoDup_Permutation_bis.
 - apply lperms_nodup.
 - rewrite lperms_length. unfold reorder_lperms.
   rewrite flat_map_length with (k := fact n).
   + rewrite seq_length. simpl; lia.
   + intros a _. now rewrite map_length, lperms_length.
 - intros p Hp. rewrite lperms_ok in Hp.
   rewrite <- (extend_reduce_lperm p).
   2:{ rewrite (lperm_head_count (S n) 0 p); auto. }
   unfold reorder_lperms.
   apply in_flat_map_Exists, Exists_exists. exists (index 0 p). split.
   + apply in_seq. split; try lia. simpl. replace (S n) with (length p).
     apply index_lt_len.
     * apply Permutation_sym in Hp. eapply Permutation_in; eauto.
       apply in_seq; lia.
     * apply Permutation_length in Hp. now rewrite seq_length in Hp.
   + rewrite in_map_iff. exists (reduce_lperm p); split; trivial.
     apply lperms_ok. now apply reduce_lperm_is_lperm.
Qed.

(** Signature of extended permutation *)

Lemma inversions_map_mono (f : nat -> nat) :
 (forall x y, x < y -> f x < f y) ->
 forall l, inversions (map f l) = inversions l.
Proof.
 intros Hf.
 induction l; simpl; auto.
 rewrite IHl. f_equal. rewrite map_filter, map_length. unfold compose.
 f_equal. apply filter_ext. intros x.
 do 2 case Nat.ltb_spec; intros; auto.
 - destruct (Nat.eq_dec a x); subst; try lia. specialize (Hf a x); lia.
 - destruct (Nat.eq_dec a x); subst; try lia. specialize (Hf x a); lia.
Qed.

Lemma inversions_extend l x : x <= length l ->
 inversions (extend_lperm x l) = x + inversions l.
Proof.
 unfold extend_lperm. revert l.
 induction x; intros l Hx; simpl.
 - rewrite filter_nop.
   2:{ intros y. rewrite in_map_iff. now intros (z & <- & IN). }
   apply inversions_map_mono; lia.
 - destruct l; simpl in *; try lia.
   rewrite IHx by lia.
   assert (P := insert_permut x O (map S l)).
   set (fS := fun y => _).
   set (f := fun y => _).
   apply Permutation_filter with (f:=fS) in P.
   apply Permutation_length in P. rewrite P. simpl.
   rewrite map_filter, map_length.
   rewrite filter_ext with (g:=f); try easy; lia.
Qed.

Lemma zsign_extend n l x : lpermutation n l -> x <= n ->
   zsign (S n) (perm2fun (extend_lperm x l)) =
   (zparity x * zsign n (perm2fun l))%Z.
Proof.
 intros Hl Hx.
 rewrite !zsign_ok.
 2:{ now apply q_f_permutation, l_q_permutation. }
 2:{ apply q_f_permutation, l_q_permutation.
     now apply extend_lperm_is_lperm. }
 unfold qsign.
 assert (length l = n).
 { apply Permutation_length in Hl. now rewrite seq_length in Hl. }
 rewrite !perm2list_perm2fun; trivial.
 2:{ unfold extend_lperm. rewrite insert_length, map_length; lia. }
 unfold lsign.
 rewrite inversions_extend by lia.
 rewrite Nat.even_add. unfold zparity. now do 2 destruct Nat.even.
Qed.
