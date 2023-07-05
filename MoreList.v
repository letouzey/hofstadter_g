From Coq Require Import Arith Lia List Permutation.
Import Basics ListNotations.

(** Some complements on Coq lists *)

Lemma nil_carac {A} (l:list A) : l = [] <-> forall x, ~In x l.
Proof.
 split.
 - now intros ->.
 - destruct l; trivial. simpl. intros H. specialize (H a); intuition.
Qed.

Lemma rev_switch {A} (l l' : list A) : rev l = l' -> l = rev l'.
Proof.
 intros. now rewrite <- (rev_involutive l), H.
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

Lemma last_nth {A}(l : list A) d :
 last l d = nth (length l - 1) l d.
Proof.
 induction l as [|x [|y l] IH]; simpl; auto.
 destruct l; simpl; auto.
Qed.

Lemma nth_map_indep {A B}(f : A -> B) l n d d' :
 n < length l -> nth n (map f l) d = f (nth n l d').
Proof.
 intros L. rewrite nth_indep with (d':=f d') by now rewrite map_length.
 apply map_nth.
Qed.

(* Quite ad-hoc, but used several times *)
Lemma nth_map_seq {A} (f:nat->A) k n d :
 k < n -> nth k (map f (seq 0 n)) d = f k.
Proof.
 intros L. rewrite nth_map_indep with (d':=0) by now rewrite seq_length.
 f_equal. now apply seq_nth.
Qed.

Lemma map_repeat {A B}(f : A -> B) a n :
 map f (repeat a n) = repeat (f a) n.
Proof.
 induction n; simpl; f_equal; auto.
Qed.

(** More on count_occ *)

Lemma count_occ_seq n x :
 count_occ Nat.eq_dec (seq 0 n) x = if x <? n then 1 else 0.
Proof.
 induction n; auto.
 rewrite seq_S, count_occ_app, IHn; simpl.
 do 2 case Nat.ltb_spec; destruct Nat.eq_dec; lia.
Qed.

Lemma count_occ_repeat [A](dec: forall x y : A, {x = y} + {x <> y}) x n y :
  count_occ dec (repeat x n) y = if dec x y then n else 0.
Proof.
 induction n; simpl; destruct dec; simpl; congruence.
Qed.

Lemma count_occ_remove [A](dec: forall x y : A, {x = y} + {x <> y}) l x y :
  count_occ dec (remove dec x l) y =
   if dec x y then 0 else count_occ dec l y.
Proof.
 induction l; repeat (simpl; destruct dec); congruence.
Qed.

(** More on filter *)

Lemma filter_nop {A} (f:A->bool) l :
 (forall x, In x l -> f x = false) -> filter f l = [].
Proof.
 induction l; simpl; intros H; auto.
 rewrite H; firstorder.
Qed.

Lemma filter_all {A} (f:A->bool) l :
 (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
 induction l; simpl; intros H; auto.
 rewrite H; firstorder. f_equal. firstorder.
Qed.

Lemma map_filter {A B} (f:A->B)(h:B->bool) l :
 filter h (map f l) = map f (filter (compose h f) l).
Proof.
 induction l; simpl; auto. unfold compose.
 destruct (h (f a)); simpl; f_equal; auto.
Qed.

(** More on flat_map *)

Lemma flat_map_length {A B} (f:A->list B) l k :
 (forall a, In a l -> length (f a) = k) ->
 length (flat_map f l) = k * length l.
Proof.
 intros H.
 induction l as [|x l IH]; simpl. lia.
 rewrite app_length, IH. rewrite H; simpl; auto. lia. simpl in *. auto.
Qed.

Lemma map_flatmap {A B C} (f:B->C)(g:A -> list B) l :
 map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Proof.
 induction l; simpl; auto. rewrite map_app. now f_equal.
Qed.

(** More on Coq Permutation predicate *)

Lemma eq_Permutation {A} (l l':list A) : l = l' -> Permutation l l'.
Proof.
 intros <-. apply Permutation_refl.
Qed.

Lemma Permutation_sym_iff {A} (l:list A) l' :
 Permutation l l' <-> Permutation l' l.
Proof.
 split; apply Permutation_sym.
Qed.

Lemma Permutation_filter {A} (f: A -> bool) l l' :
 Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
 induction 1; simpl; try constructor.
 - destruct (f x); auto.
 - destruct (f x), (f y); auto. constructor.
 - econstructor; eauto.
Qed.

(** Sum of a [nat list] *)

Definition listsum l := List.fold_right Nat.add 0 l.

Lemma listsum_cons x l : listsum (x::l) = x + listsum l.
Proof.
 reflexivity.
Qed.

Lemma listsum_app l l' : listsum (l++l') = listsum l + listsum l'.
Proof.
 induction l; simpl; rewrite ?IHl; lia.
Qed.

Lemma listsum_rev l : listsum (rev l) = listsum l.
Proof.
 induction l; simpl; auto.
 rewrite listsum_app, IHl. simpl; lia.
Qed.

Lemma length_concat {A} (l:list (list A)) :
 length (concat l) = listsum (map (@length _) l).
Proof.
 induction l; simpl; trivial.
 rewrite app_length. now f_equal.
Qed.


(** index : first position of a value in a list.
    Returns the length of the list if the element is not in the list. *)

Fixpoint index x (l:list nat) :=
 match l with
 | [] => 0
 | y::l' => if x =? y then 0 else S (index x l')
 end.

Lemma nth_index x l : In x l -> nth (index x l) l 0 = x.
Proof.
 induction l.
 - inversion 1.
 - simpl. intros [->|IN].
   + now rewrite Nat.eqb_refl.
   + case Nat.eqb_spec; auto.
Qed.

Lemma index_nth n l :
  NoDup l -> n < length l -> index (nth n l 0) l = n.
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
 induction l; simpl. easy. case Nat.eqb_spec; intuition lia.
Qed.

(** Inserting a value at some position in a list *)

Fixpoint insert_at {A} n x (l:list A) :=
 match n, l with
 | O, _ => x::l
 | S n, a::l => a::insert_at n x l
 | _, [] => [x]
 end.

Lemma remove_insert n x l :
  ~In x l -> remove Nat.eq_dec x (insert_at n x l) = l.
Proof.
 revert l.
 induction n.
 - intros l NI. simpl. destruct Nat.eq_dec; try lia.
   apply notin_remove; intuition.
 - intros [|a l].
   + intros _. simpl. destruct Nat.eq_dec; try lia; auto.
   + intros NI. simpl in *. destruct Nat.eq_dec; subst; intuition.
     f_equal. now apply IHn.
Qed.

Lemma insert_permut {A} n x (l:list A) :
 Permutation (insert_at n x l) (x::l).
Proof.
 revert l.
 induction n; simpl; auto. destruct l; simpl; auto.
 apply perm_trans with (a::x::l); auto. constructor.
Qed.

Lemma insert_length {A} n x (l:list A) :
  length (insert_at n x l) = S (length l).
Proof.
 change (S (length l)) with (length (x::l)).
 apply Permutation_length, insert_permut.
Qed.

Lemma insert_in {A} n x y (l:list A) :
  In y (insert_at n x l) <-> In y (x :: l).
Proof.
 split; apply Permutation_in; auto using Permutation_sym, insert_permut.
Qed.

Lemma nth_insert {A} n k x (l:list A) d : n <= length l ->
 nth k (insert_at n x l) d =
 match Nat.compare k n with
 | Lt => nth k l d
 | Eq => x
 | Gt => nth (k-1) l d
 end.
Proof.
 revert k l.
 induction n; simpl; intros k l Hn.
 - case Nat.compare_spec; intros Hk; subst; auto.
   inversion Hk.
   destruct k; try lia. f_equal. lia.
 - destruct l; simpl in *; try lia.
   destruct k; auto. rewrite IHn by lia. simpl Nat.compare.
   case Nat.compare_spec; intros Hk; subst; auto.
   simpl. rewrite Nat.sub_0_r. destruct k; try lia. f_equal. lia.
Qed.

(** Lists with empty intersection *)

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

(** In a list, moving all the occurrences of a value at front. *)

Definition movefront [A](dec : forall x y : A, {x = y} + {x <> y}) x l :=
 repeat x (count_occ dec l x) ++ remove dec x l.

Lemma movefront_perm [A](dec : forall x y : A, {x = y} + {x <> y}) x l :
 Permutation l (movefront dec x l).
Proof.
 rewrite (Permutation_count_occ dec). intros y. unfold movefront.
 rewrite count_occ_app, count_occ_remove, count_occ_repeat.
 destruct dec; subst; lia.
Qed.
