From Coq Require Import Bool Arith Lia Permutation FinFun List ZArith.
From QuantumLib Require Permutations.
Import ListNotations.
Import Basics.

Module QPerm := QuantumLib.Permutations.

(** More on permutations *)

Lemma Permutation_sym_iff {A} (l:list A) l' :
 Permutation l l' <-> Permutation l' l.
Proof.
 split; apply Permutation_sym.
Qed.

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

(** Interaction between QuantumLib's permutation
    and Coq's Permutation predicate on lists *)

Definition perm2list n (f:nat->nat) := map f (seq 0 n).

Lemma q_l_permutation n f :
 qpermutation n f -> lpermutation n (perm2list n f).
Proof.
 intros Hf. unfold lpermutation, perm2list.
 destruct (proj1 (q_f_permutation n f) Hf) as (Hf1,Hf2).
 set (f' := fun k => if k <? n then f k else k).
 cbn.
 rewrite map_ext_in with (g:=f').
 2:{ intros a Ha. rewrite in_seq in Ha. unfold f'.
     case Nat.ltb_spec; lia. }
 apply nat_bijection_Permutation.
 - intros x Hx. unfold f'. specialize (Hf1 x Hx). case Nat.ltb_spec; lia.
 - intros x y. unfold f'. do 2 case Nat.ltb_spec; intros Hy Hx; trivial.
   + now apply Hf2.
   + specialize (Hf1 x Hx). lia.
   + specialize (Hf1 y Hy). lia.
Qed.

(** Conversely, from lpermutation to qpermutation : let's build the inverse
    function. *)

Definition perm2fun (l:list nat) := fun k => nth k l O.

Fixpoint index x (l:list nat) :=
 match l with
 | [] => O
 | y::l' => if x =? y then O else S (index x l')
 end.

Lemma nth_index x l : In x l -> nth (index x l) l O = x.
Proof.
 induction l.
 - inversion 1.
 - simpl. intros [->|IN].
   + now rewrite Nat.eqb_refl.
   + case Nat.eqb_spec; auto.
Qed.

Lemma index_nth n l :
  NoDup l -> n < length l -> index (nth n l O) l = n.
Proof.
 revert n.
 induction l.
 - inversion 2.
 - destruct n; simpl.
   + now rewrite Nat.eqb_refl.
   + inversion_clear 1. intros H. rewrite IHl by (trivial;lia).
     case Nat.eqb_spec; trivial.
     intros E. destruct H0. rewrite <- E. apply nth_In. lia.
Qed.

Lemma index_lt_len x l : In x l -> index x l < length l.
Proof.
 induction l.
 - inversion 1.
 - simpl. intros [->|IN].
   + rewrite Nat.eqb_refl. lia.
   + case Nat.eqb_spec; intros. lia. auto with *.
Qed.

Definition lperm_qinv (l:list nat) := fun k => index k l.

Definition lperm_inv n (l:list nat) := perm2list n (lperm_qinv l).
Definition qperm_inv n (f:nat->nat) := lperm_qinv (perm2list n f).

Lemma l_q_permutation n l : lpermutation n l -> qpermutation n (perm2fun l).
Proof.
 intros Hl. unfold lpermutation, perm2fun in *.
 assert (Hn : length l = n).
 { rewrite <- (seq_length n 0). now apply Permutation_length. }
 exists (lperm_qinv l).
 intros x Hx.
 assert (IN : In x l).
 { apply Permutation_in with (l:=seq 0 n); auto with *.
   apply in_seq; lia. }
 assert (IN' : In (nth x l O) l) by (apply nth_In; lia).
 repeat split.
 - apply Permutation_in with (l':=seq 0 n) in IN'; trivial.
   apply in_seq in IN'. lia.
 - rewrite <- Hn. now apply index_lt_len.
 - apply index_nth; try lia.
   apply Permutation_NoDup with (l:=seq 0 n); auto with *. apply seq_NoDup.
 - now apply nth_index.
Qed.

(** Enumeration of all permutations of [seq 0 n] (in the form of lists) *)

Fixpoint inserts {A} (x:A) l :=
 match l with
 | [] => [[x]]
 | y::l' => (x::l)::(map (cons y) (inserts x l'))
 end.

Fixpoint perms {A} (l:list A) :=
 match l with
 | [] => [[]]
 | x::l => flat_map (inserts x) (perms l)
 end.

Definition lperms n := perms (seq 0 n).

Definition qperms n := map perm2fun (lperms n).

(** Correctness of [inserts], [perms], [lperms] *)

Definition Insert {A} (x:A) l l' :=
 exists l1 l2, l=l1++l2 /\ l'=l1++x::l2.

Lemma inserts_spec {A} (x:A) l l' :
 In l' (inserts x l) <-> Insert x l l'.
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

Lemma perms_spec {A} (l:list A) l' : In l' (perms l) <-> Permutation l l'.
Proof.
 revert l'.
 induction l as [|x l IH]; intros l'; simpl; split.
 - intros [<-|[]]; auto.
 - intros H. apply Permutation_nil in H. now left.
 - rewrite in_flat_map. intros (r & IN & IN').
   rewrite IH in IN. rewrite inserts_spec in IN'.
   destruct IN' as (l1 & l2 & -> & ->).
   now apply Permutation_cons_app.
 - intros H.
   assert (IN : In x l').
   { eapply Permutation_in; eauto. simpl; auto. }
   apply in_split in IN. destruct IN as (l1 & l2 & ->).
   apply Permutation_cons_app_inv in H.
   apply IH in H.
   rewrite in_flat_map. exists (l1++l2); split; auto.
   rewrite inserts_spec. now exists l1, l2.
Qed.

Lemma lperms_ok n l :
 In l (lperms n) <-> lpermutation n l.
Proof.
 unfold lperms. rewrite perms_spec. now rewrite Permutation_sym_iff.
Qed.

Lemma qperms_ok1 n f :
 In f (qperms n) -> qpermutation n f.
Proof.
 unfold qperms. rewrite in_map_iff.
 intros (l & <- & IN). now apply l_q_permutation, lperms_ok.
Qed.

Definition bEq n (f f':nat->nat) := forall x, x < n -> f x = f' x.

Lemma qperms_ok2 n f :
 qpermutation n f -> exists f', In f' (qperms n) /\ bEq n f f'.
Proof.
 intros Hf. exists (perm2fun (perm2list n f)). split.
 - unfold qperms. now apply in_map, lperms_ok, q_l_permutation.
 - unfold bEq, perm2fun, perm2list. intros x Hx.
   rewrite nth_indep with (d':=f 0) by now rewrite map_length, seq_length.
   rewrite map_nth, seq_nth; auto with *.
Qed.


(** [inserts], [perms], [lperms] produce lists without duplicates *)

Definition EmptyInter {A} (u v : list A) := forall a, ~(In a u /\ In a v).

Lemma app_nodup {A} (l l':list A) :
  NoDup l -> NoDup l' -> EmptyInter l l' -> NoDup (l++l').
Proof.
 revert l'.
 induction l as [|x l IH]; simpl; trivial.
 intros l'. inversion_clear 1. intros Hl' EI. constructor.
 - specialize (EI x). simpl in EI. rewrite in_app_iff. intuition.
 - apply IH; auto. intros y. specialize (EI y). simpl in EI. intuition.
Qed.

Lemma flat_map_nodup {A B} (f:A -> list B) l :
 (forall a, In a l -> NoDup (f a)) ->
 (forall a a', In a l -> In a' l -> a<>a' -> EmptyInter (f a) (f a')) ->
 NoDup l ->
 NoDup (flat_map f l).
Proof.
 induction l as [|x l IH]; simpl; intros H1 H2 H3.
 - constructor.
 - inversion_clear H3.
   apply app_nodup; auto.
   intros y (Hy1,Hy2). rewrite in_flat_map in Hy2.
   destruct Hy2 as (x' & IN & IN').
   refine (H2 x x' _ _ _ y _); auto; congruence.
Qed.

Lemma inserts_nodup {A} (x:A) l : ~In x l -> NoDup (inserts x l).
Proof.
 induction l as [|y l IH]; simpl.
 - intros _. constructor; auto. constructor.
 - intros H. constructor.
   + rewrite in_map_iff. intros (l' & [= E _] & _). intuition.
   + apply Injective_map_NoDup; auto. congruence.
Qed.

Lemma split_inv {A} (x:A) u u' v v' :
 ~In x u -> ~In x u' -> u++x::v = u'++x::v' -> u=u' /\ v=v'.
Proof.
 revert u' v v'.
 induction u as [|y u IH]; intros [|y' u'] v v'.
 - intros _ _. simpl. split; auto. congruence.
 - intros _ NI. simpl in *. intros [= <- _]. destruct NI. now left.
 - intros NI _. simpl in *. intros [= -> _]. destruct NI. now left.
 - intros NI NI'. simpl in *. intros [= <- E]. apply IH in E; try tauto.
   split; now f_equal.
Qed.

Lemma perms_nodup {A} (l:list A) : NoDup l -> NoDup (perms l).
Proof.
 induction l as [|x l IH]; simpl.
 - intros _. constructor; auto. constructor.
 - inversion_clear 1.
   apply flat_map_nodup; auto.
   + intros a Ha. apply inserts_nodup.
     rewrite perms_spec in Ha. apply Permutation_sym in Ha.
     contradict H0. eapply Permutation_in; eauto.
   + intros a a' IN IN' NE b (IN1,IN2).
     rewrite perms_spec in IN, IN'.
     rewrite inserts_spec in IN1,IN2.
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
 apply perms_nodup, seq_NoDup.
Qed.

(** lengths of [inserts], [perms], [allpermutations] *)

Lemma inserts_length {A} (x:A) l : length (inserts x l) = S (length l).
Proof.
 induction l as [|y l IH]; simpl; trivial.
 f_equal. now rewrite map_length.
Qed.

Lemma flat_map_length {A B} (f:A->list B) l k :
 (forall a, In a l -> length (f a) = k) ->
 length (flat_map f l) = k * length l.
Proof.
 intros H.
 induction l as [|x l IH]; simpl. lia.
 rewrite app_length, IH. rewrite H; simpl; auto. lia. simpl in *. auto.
Qed.

Lemma perms_length {A} (l:list A) : length (perms l) = fact (length l).
Proof.
 induction l as [|x l IH]; simpl; trivial.
 rewrite flat_map_length with (k := S (length l)).
 rewrite IH. lia.
 intros a Ha. rewrite inserts_length. f_equal.
 now apply Permutation_length, Permutation_sym, perms_spec.
Qed.

Lemma lperms_length n : length (lperms n) = fact n.
Proof.
 unfold lperms. now rewrite perms_length, seq_length.
Qed.

Lemma qperms_length n : length (qperms n) = fact n.
Proof.
 unfold qperms. now rewrite map_length, lperms_length.
Qed.

(* Permutations and transpositions *)

Definition fEq (f g : nat->nat) := forall x, f x = g x.

Definition transpose '(i,j) := fun n =>
  if n =? i then j else if n =? j then i else n.

Lemma transpose_invo i j :
  fEq (compose (transpose (i,j)) (transpose (i,j))) id.
Proof.
 intros x.
 unfold transpose, compose, id.
 repeat (case Nat.eqb_spec; simpl); lia.
Qed.

Lemma transpose_l i j : transpose (i,j) i = j.
Proof.
 unfold transpose. now rewrite Nat.eqb_refl.
Qed.

Lemma transpose_r i j : transpose (i,j) j = i.
Proof.
 unfold transpose. case Nat.eqb_spec; try lia. now rewrite Nat.eqb_refl.
Qed.

Lemma transpose_id i j x : x<>i -> x<>j -> transpose (i,j) x = x.
Proof.
 unfold transpose. intros Hi Hj.
 case Nat.eqb_spec; intros; try lia.
 case Nat.eqb_spec; intros; try lia.
Qed.

Fixpoint ltranspose (l : list (nat*nat)) :=
  match l with
  | [] => fun x => x
  | ij::l => compose (transpose ij) (ltranspose l)
  end.

Lemma ltranspose_one i j : fEq (ltranspose [(i,j)]) (transpose (i,j)).
Proof.
 intros x. cbn -[transpose]. now unfold compose.
Qed.

Lemma ltranspose_app l1 l2 :
 fEq (ltranspose (l1++l2)) (compose (ltranspose l1) (ltranspose l2)).
Proof.
 intros x; unfold compose.
 induction l1; simpl; trivial. unfold compose. now rewrite IHl1.
Qed.

Lemma fpermutation'_ltranspose n f :
  fpermutation n f -> (forall x, n<=x -> f x = x) ->
  exists l,
    Forall (fun '(i,j) => i < j < n) l /\
    fEq f (ltranspose l).
Proof.
 revert f.
 induction n.
 - intros f _. exists []. split. constructor. simpl. firstorder lia.
 - intros f Hf Hf'. assert (Hf1 := Hf).
   destruct Hf1 as (Hf1,Hf2).
   assert (Hf3 := Hf2). rewrite bInjective_bSurjective in Hf3 by auto.
   destruct (Nat.eq_dec (f n) n) as [E|N].
   + assert (Q : fpermutation n f).
     { split.
       - intros x Hx.
         assert (f x < S n) by (specialize (Hf1 x); lia).
         assert (f x <> f n); try lia. { intros E'. apply Hf2 in E'; lia. }
       - intros x y Hx Hy. apply Hf2; lia. }
     assert (Q' : forall x, n <= x -> f x = x).
     { intros x Hx. destruct Hx; auto. apply Hf'; lia. }
     destruct (IHn f Q Q') as (l & Hl & Hl').
     exists l; split; auto.
     rewrite Forall_forall in *.
     intros (i,j) Hij. specialize (Hl (i,j) Hij). simpl in *. lia.
   + assert (N' : f n < n).
     { generalize (Hf1 n). lia. }
     clear N.
     destruct (Hf3 n) as (i & Hi1 & Hi2); try lia.
     assert (i <> n) by (intros ->; lia).
     set (g := compose f (transpose (i,n))).
     assert (Hg : fpermutation n g).
     { split.
       - intros x Hx. unfold g.
         unfold transpose, compose; simpl.
         case Nat.eqb_spec; try lia.
         intros Hxi. case Nat.eqb_spec; try lia.
         intros _. assert (f x < S n) by (apply Hf1; lia).
         assert (f x <> f i); try lia. { intros E. apply Hf2 in E; lia. }
       - intros x y Hx Hy. unfold g, compose.
         unfold transpose.
         repeat (case Nat.eqb_spec; simpl; intro; try lia);
          intro E; apply Hf2 in E; lia. }
     assert (Hg' : forall x, n <= x -> g x = x).
     { intros x Hx. unfold g. unfold compose.
       destruct (Nat.eq_dec x n) as [->|Hx'].
       - now rewrite transpose_r, Hi2.
       - rewrite (transpose_id i n); try lia. apply Hf'; lia. }
     destruct (IHn g Hg Hg') as (l & Hl & Hl').
     exists (l ++ [(i,n)]); split.
     * rewrite !Forall_app. split; repeat constructor; try lia.
       rewrite Forall_forall in *.
       intros (u,v) Huv. specialize (Hl (u,v) Huv). simpl in Hl. lia.
     * intros x. rewrite ltranspose_app. unfold compose.
       rewrite <- Hl', ltranspose_one. unfold g.
       generalize (transpose_invo i n x). unfold compose, id. now intros ->.
Qed.

Lemma fpermutation_ltranspose n f : fpermutation n f ->
  exists l,
    Forall (fun '(i,j) => i < j < n) l /\
    bEq n f (ltranspose l).
Proof.
 intros Hf.
 set (f' := fun k => if k <? n then f k else k).
 destruct (fpermutation'_ltranspose n f') as (l & Hl & Hl').
 - destruct Hf as (Hf1,Hf2).
   split.
   + intros x Hx. unfold f'. specialize (Hf1 x Hx). case Nat.ltb_spec; lia.
   + intros x y. unfold f'. do 2 case Nat.ltb_spec; intros Hy Hx; trivial.
     * now apply Hf2.
     * specialize (Hf1 x Hx). lia.
     * specialize (Hf1 y Hy). lia.
 - unfold f'. intros x Hx. case Nat.ltb_spec; lia.
 - exists l; split; trivial. intros x Hx. rewrite <- Hl'. unfold f'.
   case Nat.ltb_spec; lia.
Qed.

(* TODO: fonction donnant une decomp en transpositions
   (via "index" pour trouver l'antécédent de n par f)

   Lien entre signature (comme parité du nombre d'inversion)
   et parité du nb de transpo dans la decomp de cette permut ?

   application à la signature d'une composition puis d'un inverse.

*)


(* Sign of a permutation *)

Fixpoint inversions l :=
 match l with
 | [] => 0
 | x::l => length (filter (fun y => y <? x) l) + inversions l
 end.

Definition lsign l := Nat.even (inversions l).

Definition qsign n f := lsign (perm2list n f).

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

Lemma nil_carac {A} (l:list A) : l = [] <-> forall x, ~In x l.
Proof.
 split.
 - now intros ->.
 - destruct l; trivial. simpl. intros H. specialize (H a); intuition.
Qed.

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

Lemma qsign_id n : qsign n (fun k => k) = true.
Proof.
 unfold qsign, perm2list. rewrite map_id. apply lsign_id.
Qed.

Fixpoint incrpairs n :=
  match n with
  | O => []
  | S n => incrpairs n ++ map (fun k => (k,n)) (seq 0 n)
  end.

Definition decrpairs n := map (fun '(i,j) => (j,i)) (incrpairs n).

Definition diffpairs n := incrpairs n ++ decrpairs n.

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

Lemma decrpairs_countocc n i j :
  count_occ natnatdec (decrpairs n) (i,j) =
  if (j <? i) && (i <? n) then 1 else 0.
Proof.
 unfold decrpairs.
 change (i,j) with ((fun '(i0, j0) => (j0, i0)) (j,i)).
 erewrite <- count_occ_map with (decA := natnatdec).
 apply incrpairs_countocc.
 intros (x,y) (x',y'). congruence.
Qed.

Lemma diffpairs_countocc n i j :
 count_occ natnatdec (diffpairs n) (i,j) =
  if (j <? n) && (i <? n) && negb (i =? j) then 1 else 0.
Proof.
 unfold diffpairs.
 rewrite count_occ_app, incrpairs_countocc, decrpairs_countocc.
 repeat (case Nat.ltb_spec; intros; simpl; auto; try lia);
   case Nat.eqb_spec; intros; simpl; auto; try lia.
Qed.

Fixpoint zPi {A} (f:A->Z) l :=
  match l with
   | [] => 1
   | x::l => f x * zPi f l
  end%Z.

Lemma zPi_app {A} (f:A->Z) l1 l2 :
  (zPi f (l1++l2) = zPi f l1 * zPi f l2)%Z.
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
 (zPi (fun x => f x * g x) l = zPi f l * zPi g l)%Z.
Proof.
 induction l; simpl; auto. rewrite IHl. lia.
Qed.

Local Coercion Z.of_nat : nat >-> Z.

Definition zsign n (f:nat->nat) : Z :=
  zPi (fun '(i,j) => Z.sgn (f j - f i)) (incrpairs n).

Lemma zPi_bigxor {A}(f:A->Z)(g:A->bool) l :
 (forall x, In x l -> f x = if g x then (-1)%Z else 1%Z) ->
 zPi f l = if bigxor g l then (-1)%Z else 1%Z.
Proof.
 intros H.
 induction l; simpl; auto.
 rewrite (H a) by (now left). rewrite IHl by (simpl in *; firstorder).
 destruct (g a), (bigxor g l); simpl; try lia.
Qed.

Lemma zsign_ok n f : bInjective n f ->
 zsign n f = if qsign n f then 1%Z else (-1)%Z.
Proof.
 unfold zsign, qsign, perm2list. rewrite lsign_equiv. revert f.
 induction n as [|n IH]; intros f Hf; trivial.
 rewrite seq_S, map_app. cbn. rewrite zPi_app. rewrite IH by firstorder.
 rewrite lsign'_alt. rewrite bigxor_map, zPi_map. unfold compose.
 rewrite zPi_bigxor with (g := fun x : nat => f n <? f x).
 destruct lsign', bigxor; simpl; try lia.
 intros x. clear IH. rewrite in_seq. intros Hx.
 case Nat.ltb_spec. lia. specialize (Hf x n); lia.
Qed.

Lemma permut_diffpairs n f :
  qpermutation n f ->
  Permutation (diffpairs n)
              (map (fun '(i,j) => (f i, f j)) (diffpairs n)).
Proof.
 intros Q.
 rewrite Permutation_count_occ with (eq_dec := natnatdec).
 intros (i,j). rewrite diffpairs_countocc.
 destruct Q as (g & Hg).
 set (f' := fun k => if k <? n then f k else k).
 assert (Hf' : Injective f').
 { intros x y. unfold f'.
   repeat (case Nat.ltb_spec; simpl; trivial); try lia.
   - intros; destruct (Hg x), (Hg y); trivial.
     replace x with (g (f x)) by lia.
     replace y with (g (f y)) by lia. replace (f x) with (f y); lia.
   - intros. destruct (Hg x); trivial; lia.
   - intros. destruct (Hg y); trivial; lia. }
 set (F := fun _ => _).
 set (F' := fun '(i,j) => (f' i,f' j)).
 rewrite map_ext_in with (g:=F').
 2:{ intros (x,y). rewrite count_occ_In with (eq_dec := natnatdec).
     rewrite diffpairs_countocc.
     unfold F, F', f'.
     repeat (case Nat.ltb_spec; simpl; trivial); try lia. }
 case Nat.ltb_spec; intros; simpl.
 - case Nat.ltb_spec; intros; simpl.
   + replace (i,j) with (F' (g i, g j)).
     2:{ simpl. unfold f'. destruct (Hg i), (Hg j); trivial.
         f_equal; repeat (case Nat.ltb_spec; simpl; trivial); try lia. }
     rewrite <- count_occ_map with (decA := natnatdec).
     2:{ intros (x,y) (x',y'). unfold F'. intros [= Hx Hy].
         apply Hf' in Hx, Hy. congruence. }
     rewrite diffpairs_countocc.
     destruct (Hg i), (Hg j); trivial.
     repeat (case Nat.ltb_spec; simpl; intros; try lia).
     case Nat.eqb_spec; [intros ->|intros NE]; simpl.
     * now rewrite Nat.eqb_refl.
     * replace i with (f (g i)) in NE by lia.
       replace j with (f (g j)) in NE by lia.
       case Nat.eqb_spec; simpl; intros; auto; congruence.
   + symmetry. apply count_occ_not_In.
     rewrite in_map_iff. intros ((x,y) & [= <- <-] & IN). revert IN.
     rewrite count_occ_In with (eq_dec := natnatdec).
     rewrite diffpairs_countocc.
     repeat (case Nat.ltb_spec; simpl; trivial); try lia.
     intros. destruct (Hg x); trivial. revert H0. unfold f'.
     repeat (case Nat.ltb_spec; simpl; trivial); try lia.
  - symmetry. apply count_occ_not_In.
    rewrite in_map_iff. intros ((x,y) & [= <- <-] & IN). revert IN.
    rewrite count_occ_In with (eq_dec := natnatdec).
    rewrite diffpairs_countocc.
    repeat (case Nat.ltb_spec; simpl; trivial); try lia.
    intros. destruct (Hg y); trivial. revert H. unfold f'.
    repeat (case Nat.ltb_spec; simpl; trivial); try lia.
Qed.

Lemma zPi_reindex n f : qpermutation n f ->
 zPi (fun '(i,j) =>  Z.abs (f j - f i)) (diffpairs n)
 = zPi (fun '(i,j) => Z.abs (Z.of_nat j - Z.of_nat i)) (diffpairs n).
Proof.
 intros Q. symmetry. rewrite (zPi_permut _ _ _ (permut_diffpairs n f Q)).
 rewrite zPi_map. unfold compose. apply zPi_ext. now intros (i,j).
Qed.

Lemma zPi_diffpairs_incrpairs_square n (f : nat * nat -> Z) :
 (forall i j, In (i,j) (incrpairs n) -> f (j,i) = f (i,j)) ->
 (zPi f (diffpairs n) = (zPi f (incrpairs n))^2)%Z.
Proof.
 intros H.
 unfold diffpairs. rewrite zPi_app, Z.pow_2_r. f_equal.
 unfold decrpairs. rewrite zPi_map. apply zPi_ext.
 intros (i,j). unfold compose. now apply H.
Qed.

Lemma zPi_diffpairs_incrpairs_square' n (f : nat * nat -> Z) :
 (forall i j, In (i,j) (incrpairs n) -> f (j,i) = - f (i,j))%Z ->
 (zPi f (diffpairs n) =
  (zPi f (incrpairs n))^2 * zPi (fun _ => -1) (incrpairs n))%Z.
Proof.
 intros H.
 unfold diffpairs. rewrite zPi_app, Z.pow_2_r. rewrite <- Z.mul_assoc.
 f_equal. rewrite <- zPi_mult.
 unfold decrpairs. rewrite zPi_map. apply zPi_ext.
 intros (i,j). unfold compose. intros IN. apply H in IN. lia.
Qed.

Lemma zPi_pos {A} (f:A->Z) l :
  (forall x, In x l -> 0 < f x)%Z -> (0 < zPi f l)%Z.
Proof.
 induction l; simpl; auto; try lia.
 intros H. apply Z.mul_pos_pos. apply H; now left. apply IHl; firstorder.
Qed.

Lemma zPi_nonneg {A} (f:A->Z) l :
  (forall x, In x l -> 0 <= f x)%Z -> (0 <= zPi f l)%Z.
Proof.
 induction l; simpl; auto; try lia.
 intros H. apply Z.mul_nonneg_nonneg. apply H; now left. apply IHl; firstorder.
Qed.

Lemma zsign_eqn n f : qpermutation n f ->
 (zsign n f * zPi (fun '(i,j) => Z.of_nat j - Z.of_nat i) (incrpairs n) =
 zPi (fun '(i,j) => f j - f i) (incrpairs n))%Z.
Proof.
 unfold zsign.
 intros Q.
 transitivity
   ((zPi (fun '(i, j) => Z.sgn (f j - f i)) (incrpairs n) *
     zPi (fun '(i, j) => Z.abs (f j - f i)) (incrpairs n))%Z).
 2:{ rewrite <- zPi_mult. apply zPi_ext. intros (i,j) IN.
     now rewrite Z.mul_comm, Z.abs_sgn. }
 f_equal.
 rewrite <- (Z.sqrt_square
               (zPi (fun '(i, j) => Z.abs (f j - f i)) (incrpairs n))).
 2:{ apply zPi_nonneg. intros (i,j) _. apply Z.abs_nonneg. }
 rewrite <- Z.pow_2_r, <- zPi_diffpairs_incrpairs_square by lia.
 rewrite zPi_reindex; trivial.
 rewrite zPi_diffpairs_incrpairs_square, Z.pow_2_r by lia.
 rewrite Z.sqrt_square.
 2:{ apply zPi_nonneg. intros (i,j) _. apply Z.abs_nonneg. }
 apply zPi_ext.
 intros (i,j). rewrite count_occ_In with (eq_dec := natnatdec).
 rewrite incrpairs_countocc.
 case Nat.ltb_spec; simpl; lia.
Qed.

(*
Lemma zsign_eqn' n f :
 (zsign n f * zPi (fun '(i,j) => Z.of_nat j - Z.of_nat i) (diffpairs n) =
 zPi (fun '(i,j) => Z.of_nat (f j) - Z.of_nat (f i)) (diffpairs n))%Z.
Proof.
Admitted.
(* Hum, souci avec la page wikipedia *)
*)


(* composition and sign, inverse and sign ?
   transpositions ? decomp in cycles ? *)
