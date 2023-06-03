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

Lemma index_notin x l : ~In x l -> index x l = length l.
Proof.
 induction l; simpl; try easy.
 intros H. case Nat.eqb_spec; intuition.
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

Lemma transpose_fperm n i j :
  i < n -> j < n -> fpermutation n (transpose (i,j)).
Proof.
 intros Hi Hj. split.
 - intros x Hx. unfold transpose.
   repeat (case Nat.eqb_spec; try lia).
 - intros x y Hx Hy. unfold transpose.
   repeat (case Nat.eqb_spec; try lia).
Qed.

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

Lemma transpose_else i j x : x<>i -> x<>j -> transpose (i,j) x = x.
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

Fixpoint transposify n f :=
 match n with
 | 0 => []
 | S n =>
   if f n =? n then transposify n f
   else (f n, n)::transposify n (compose (transpose (f n, n)) f)
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
 fpermutation (S n) f -> fpermutation n (compose (transpose (f n, n)) f).
Proof.
 intros (Hf1,Hf2). split.
 - intros x Hx.
   assert (f x < S n) by (specialize (Hf1 x); lia).
   unfold compose, transpose.
   case Nat.eqb_spec; intros E.
   + apply Hf2 in E; try lia.
   + case Nat.eqb_spec; intros E'; try lia.
     specialize (Hf1 n); lia.
 - intros x y Hx Hy. unfold compose. intros E.
   apply (transpose_fperm (S n) (f n) n) in E; try apply Hf1; try lia.
   apply Hf2; lia.
Qed.

Lemma transposify_ok n f :
  fpermutation n f -> Forall (fun '(i,j) => i < j < n) (transposify n f).
Proof.
 revert f.
 induction n; intros f Hf.
 - constructor.
 - cbn -[transpose]. case Nat.eqb_spec; intros E.
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
  fEq f (ltranspose (transposify n f)).
Proof.
 revert f.
 induction n; intros f Hf Hf'.
 - simpl. firstorder lia.
 - cbn -[transpose]. case Nat.eqb_spec; intros E.
   + apply IHn. now apply subpermut_1.
     intros x Hx. destruct Hx; [ lia | apply Hf'; lia ].
   + cbn -[transpose].
     intro x. unfold compose. rewrite <- IHn.
     * now generalize (transpose_invo (f n) n (f x)).
     * now apply subpermut_2.
     * clear x. intros x Hx. destruct Hx.
       { simpl. now rewrite Nat.eqb_refl. }
       { rewrite (Hf' (S m)) by lia. apply transpose_else; try lia.
         assert (f n < S n) by (apply Hf; lia). lia. }
Qed.

Lemma transposify_ext n f f' :
 bEq n f f' -> transposify n f = transposify n f'.
Proof.
 revert f f'.
 induction n; intros f f' B; cbn -[transpose]; auto.
 rewrite <- (B n) by lia. case Nat.eqb_spec; intros.
 - apply IHn. firstorder.
 - f_equal. apply IHn. intros x Hx. unfold compose.
   now rewrite <- (B x) by lia.
Qed.

Lemma transposify_beq n f :
  fpermutation n f -> bEq n f (ltranspose (transposify n f)).
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

(* Lien entre signature (comme parité du nombre d'inversion)
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

Lemma incrpairs_in n i j :
  In (i,j) (incrpairs n) <-> i < j < n.
Proof.
 rewrite count_occ_In with (eq_dec:=natnatdec).
 rewrite incrpairs_countocc.
 repeat (case Nat.ltb_spec; simpl; try lia).
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

Lemma diffpairs_in n i j :
  In (i,j) (diffpairs n) <-> i < n /\ j < n /\ i<>j.
Proof.
 rewrite count_occ_In with (eq_dec:=natnatdec).
 rewrite diffpairs_countocc.
 repeat (case Nat.ltb_spec; simpl; try lia).
 case Nat.eqb_spec; simpl; try lia.
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
 ((forall x, In x l -> f x = if g x then -1 else 1) ->
  zPi f l = if bigxor g l then -1 else 1)%Z.
Proof.
 intros H.
 induction l; simpl; auto.
 rewrite (H a) by (now left). rewrite IHl by (simpl in *; firstorder).
 destruct (g a), (bigxor g l); simpl; try lia.
Qed.

Lemma zsign_ok n f : bInjective n f ->
 (zsign n f = if qsign n f then 1 else -1)%Z.
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

Definition couple (g:nat->nat) '(i,j) := (g i, g j).

Definition sortpair '(i,j) := if i <? j then (i,j) else (j,i).

Definition sortedcouple g p := sortpair (couple g p).

Lemma permut_diffpairs n f :
  qpermutation n f ->
  Permutation (diffpairs n) (map (couple f) (diffpairs n)).
Proof.
 intros Q.
 apply NoDup_Permutation_bis.
 - rewrite NoDup_count_occ with (decA := natnatdec). intros (i,j).
   rewrite diffpairs_countocc. destruct andb; lia.
 - now rewrite map_length.
 - intros (i,j). rewrite diffpairs_in. intros (Hi & Hj & D).
   destruct Q as (g & Hg).
   rewrite in_map_iff. exists (g i, g j). simpl. split.
   + generalize (Hg i) (Hg j). intros. f_equal; lia.
   + rewrite diffpairs_in.
     generalize (Hg i) (Hg j). intros. repeat split; try lia.
     intros E. replace i with (f (g i)) in D by lia.
     replace j with (f (g j)) in D by lia. rewrite E in D. lia.
Qed.

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


Lemma zPi_reindex_gen n (g:nat->nat->Z) f : qpermutation n f ->
 zPi (fun '(i,j) =>  g (f j) (f i)) (diffpairs n)
 = zPi (fun '(i,j) => g j i) (diffpairs n).
Proof.
 intros Q. symmetry. rewrite (zPi_permut _ _ _ (permut_diffpairs n f Q)).
 rewrite zPi_map. apply zPi_ext. now intros (i,j).
Qed.

Lemma zPi_reindex n f : qpermutation n f ->
 zPi (fun '(i,j) =>  Z.abs (f j - f i)) (diffpairs n)
 = zPi (A:=nat*nat) (fun '(i,j) => Z.abs (j - i)) (diffpairs n).
Proof.
 apply zPi_reindex_gen with (g := fun x y => Z.abs (x - y)).
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

Lemma zPi_reindex_incr_gen n (g:nat->nat->Z) f : qpermutation n f ->
 (forall i j, g j i = g i j)%Z -> (forall i j, 0 <= g i j)%Z ->
 zPi (fun '(i,j) => g (f j) (f i)) (incrpairs n)
 = zPi (fun '(i,j) => g j i) (incrpairs n).
Proof.
 intros Q G1 G2.
 rewrite <- (Z.sqrt_square
               (zPi (fun '(i, j) => g (f j) (f i)) (incrpairs n))).
 2:{ apply zPi_nonneg. intros (i,j) _. apply G2. }
 rewrite <- Z.pow_2_r, <- zPi_diffpairs_incrpairs_square by intuition.
 rewrite zPi_reindex_gen; trivial.
 rewrite zPi_diffpairs_incrpairs_square, Z.pow_2_r by intuition.
 rewrite Z.sqrt_square; trivial.
 apply zPi_nonneg. intros (i,j) _. apply G2.
Qed.

Lemma zsign_eqn n f : qpermutation n f ->
 (zsign n f * zPi (A:=nat*nat) (fun '(i,j) => j - i) (incrpairs n) =
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
 rewrite zPi_reindex_incr_gen with (g := fun i j => Z.abs(i-j));
  auto; try lia.
 apply zPi_ext.
 intros (i,j) IN. rewrite incrpairs_in in IN. lia.
Qed.

Lemma zPi_reindex_again n (F : nat*nat -> Z)(g:nat->nat) :
 qpermutation n g ->
 (forall i j, F (j,i) = - F (i,j))%Z ->
 (zPi (compose F (couple g)) (incrpairs n) * zsign n g =
   zPi F (incrpairs n))%Z.
Proof.
 intros Hg HF.
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

Lemma zsign_compose n f g :
 qpermutation n f -> qpermutation n g ->
 (zsign n (compose f g) = zsign n f * zsign n g)%Z.
Proof.
 intros Hf Hg.
 assert (Hfg : qpermutation n (compose f g))
   by now apply QPerm.permutation_compose.
 assert (E1 := zsign_eqn _ _ Hfg).
 unfold compose at 2 3 in E1.
 assert (E2 := zsign_eqn _ _ Hf).
 rewrite <- (zPi_reindex_again n (fun '(i,j) => f j - f i)%Z g Hg) in E2
  by lia.
 unfold compose in E2. symmetry in E2.
 rewrite zPi_ext with (g := fun '(i, j) => (f (g j) - f (g i))%Z) in E2.
 2:{ now intros (i,j). }
 rewrite <- E1 in E2. clear E1.
 set (A := zPi _ _) in *.
 rewrite <- Z.mul_assoc, (Z.mul_comm A), Z.mul_assoc in E2.
 apply Z.mul_reg_r in E2.
 2:{ clear E2. assert (0 < A)%Z; try lia.
     apply zPi_pos. intros (i,j). rewrite incrpairs_in. lia. }
 rewrite <- E2. rewrite (zsign_ok n g). destruct qsign; lia.
 apply q_f_permutation in Hg. apply Hg.
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
