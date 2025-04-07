From Coq Require Export Arith Lia List Bool Permutation.
Require Import MoreTac MoreFun.
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

Lemma rev_inj {A} (l l' : list A) : rev l = rev l' -> l = l'.
Proof.
 intro H. now rewrite <- (rev_involutive l), H, rev_involutive.
Qed.

Lemma rev_repeat {A} (a:A) n : rev (repeat a n) = repeat a n.
Proof.
 induction n; trivial.
 rewrite <- Nat.add_1_r at 1. rewrite repeat_app, rev_app_distr.
 simpl. now f_equal.
Qed.

Lemma app_inv {A} (u u' v v':list A) :
 length u = length v -> u++u' = v++v' -> u=v /\ u'=v'.
Proof.
 revert v. induction u; destruct v; simpl; try easy.
 intros [= E] [= <- E']. apply IHu in E'; trivial. intuition congruence.
Qed.

Lemma app_inv' {A} (u u' v v' : list A) :
 length u' = length v' -> u ++ u' = v ++ v' -> u = v /\ u' = v'.
Proof.
 intros L E. apply app_inv; trivial.
 apply (f_equal (@length A)) in E. rewrite !app_length in E. lia.
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

Lemma last_cons {A} (a:A) l d : l<>[] -> last (a::l) d = last l d.
Proof.
 now destruct l.
Qed.

Lemma last_app {A} u v (d:A) : v<>[] -> last (u++v) d = last v d.
Proof.
 intros Hv.
 assert (Hv' : length v <> 0) by now destruct v.
 rewrite !last_nth, app_length, app_nth2 by lia. f_equal; lia.
Qed.

Lemma last_seq a n d : last (seq a (S n)) d = a+n.
Proof.
 rewrite seq_S. apply last_last.
Qed.

Lemma map_nth' {A B} (f:A->B)(l:list A)(d:B)(d':A) n :
 d = f d' -> nth n (map f l) d = f (nth n l d').
Proof.
 intros ->. apply map_nth.
Qed.

Lemma nth_map_indep {A B}(f : A -> B) l n d d' :
 n < length l -> nth n (map f l) d = f (nth n l d').
Proof.
 intros L. rewrite nth_indep with (d':=f d') by now rewrite map_length.
 apply map_nth.
Qed.

Lemma map_nth_seq_id {A} (l:list A)(d:A) :
  map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
 induction l; trivial. simpl. now rewrite <- seq_shift, map_map, IHl.
Qed.

Lemma seq_S a b : List.seq a (S b) = List.seq a b ++ [a+b].
Proof.
 revert a.
 induction b; simpl; intros. f_equal; lia.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l. now rewrite <- IHb.
Qed.

Lemma map_add_seq len start n :
  map (Nat.add n) (seq start len) = seq (n+start) len.
Proof.
 revert start.
 induction n; simpl; intros.
 - now rewrite map_id.
 - now rewrite <- seq_shift, <- IHn, map_map.
Qed.

Lemma map_repeat {A B}(f : A -> B) a n :
 map f (repeat a n) = repeat (f a) n.
Proof.
 induction n; simpl; f_equal; auto.
Qed.

Lemma repeat_map_seq {A} (a:A) n :
 repeat a n = map (fun _ => a) (seq 0 n).
Proof.
 induction n; simpl; trivial. rewrite <- seq_shift, map_map. now f_equal.
Qed.

(** Insertion at the right spot in a sorted [nat list] *)

Fixpoint insert (x : nat) (l : list nat) :=
 match l with
 | [] => [x]
 | y::l' => if x <=? y then x::l else y::insert x l'
 end.

Lemma insert_0 l : insert 0 l = 0 :: l.
Proof.
 induction l; simpl; auto.
Qed.

Lemma map_pred_insert x l:
  map Nat.pred (insert x l) = insert (Nat.pred x) (map Nat.pred l).
Proof.
 induction l; simpl; auto.
 do 2 case Nat.leb_spec; intros; try lia; simpl; auto.
 - replace a with 0 in * by lia.
   replace x with 1 in * by lia. simpl. f_equal.
   rewrite IHl. simpl. apply insert_0.
 - f_equal; auto.
Qed.

Lemma insert_in x l y : In y (insert x l) <-> x = y \/ In y l.
Proof.
 induction l; simpl; auto.
 - intuition.
 - case Nat.leb; simpl; rewrite ?IHl; intuition.
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

Lemma filter_length_le {A} (f:A->bool) l :
 length (filter f l) <= length l.
Proof.
 induction l; simpl; auto. destruct (f a); simpl; lia.
Qed.

Lemma filter_filter {A} h h' (l:list A) :
  filter h (filter h' l) = filter (fun a => h a && h' a) l.
Proof.
 induction l; simpl; trivial.
 destruct (h' a); simpl; destruct (h a); simpl; trivial. now f_equal.
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

Lemma flatmap_map {A B C} (f:A->B)(g:B -> list C) l :
 flat_map g (map f l) = flat_map (compose g f) l.
Proof.
 rewrite !flat_map_concat_map. f_equal. apply map_map.
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

(** More about [list_sum], the sum of a [nat list] *)

Lemma list_sum_cons x l : list_sum (x::l) = x + list_sum l.
Proof.
 reflexivity.
Qed.

Lemma list_sum_rev l : list_sum (rev l) = list_sum l.
Proof.
 induction l; simpl; auto.
 rewrite list_sum_app, IHl. simpl; lia.
Qed.

Lemma length_concat {A} (l:list (list A)) :
 length (concat l) = list_sum (map (@length _) l).
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

Lemma insert_at_in {A} n x y (l:list A) :
  In y (insert_at n x l) <-> In y (x :: l).
Proof.
 split; apply Permutation_in; auto using Permutation_sym, insert_permut.
Qed.

Lemma nth_insert_at {A} n k x (l:list A) d : n <= length l ->
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

(** remove_at : dual of insert_at *)

Fixpoint remove_at {A} i (l:list A) :=
 match l, i with
 | [], _ => []
 | x::l, 0 => l
 | x::l, S i => x :: remove_at i l
 end.

Lemma remove_at_nth {A} (l:list A) (d:A) i j :
 nth j (remove_at i l) d = if j <? i then nth j l d else nth (S j) l d.
Proof.
 revert i j. induction l; destruct i, j; simpl; trivial.
 - now case Nat.ltb.
 - apply (IHl i j).
Qed.

Lemma remove_at_length {A} (l:list A) i :
  i < length l -> length (remove_at i l) = pred (length l).
Proof.
 revert i. induction l; destruct i; simpl; intros; trivial. rewrite IHl; lia.
Qed.

Lemma insert_at_remove_at {A} (l:list A) i (d:A) :
  i < length l -> insert_at i (nth i l d) (remove_at i l) = l.
Proof.
 revert i. induction l; destruct i; simpl; trivial; try lia.
 intros Hi. f_equal. apply IHl. lia.
Qed.

Lemma remove_at_permut {A} (l:list A) i (d:A) :
  i < length l -> Permutation (nth i l d :: remove_at i l) l.
Proof.
 intros Hi. now rewrite <- insert_permut with (n:=i), insert_at_remove_at.
Qed.

Lemma remove_at_notIn {A} (l:list A) i d :
  NoDup l -> i < length l -> ~In (nth i l d) (remove_at i l).
Proof.
 intros Hl Hi IN.
 destruct (In_nth _ _ d IN) as (j & Hj & E).
 rewrite remove_at_nth in E.
 rewrite NoDup_nth with (d:=d) in Hl.
 rewrite remove_at_length in Hj by trivial.
 destruct (Nat.ltb_spec j i).
 - specialize (Hl j i lia Hi E). lia.
 - specialize (Hl (S j) i lia Hi E). lia.
Qed.

Lemma remove_at_In {A} (l:list A) i j d :
 i < length l -> j < length l -> i<>j -> In (nth j l d) (remove_at i l).
Proof.
 intros Hi Hj Hij.
 destruct (Nat.ltb j i) eqn:E.
 - assert (H := remove_at_nth l d i j). rewrite E in H.
   rewrite <- H. apply nth_In.
   apply Nat.ltb_lt in E.
   rewrite remove_at_length; trivial. lia.
 - rewrite Nat.ltb_nlt, Nat.nlt_ge in E.
   assert (H := remove_at_nth l d i (j-1)).
   destruct (Nat.ltb_spec (j-1) i); try lia.
   replace (S (j-1)) with j in H by lia.
   rewrite <- H. apply nth_In.
   rewrite remove_at_length; trivial. lia.
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

(** Upper bound of the elements of a list *)

Fixpoint minlist a l :=
 match l with
 | [] => a
 | b::l => Nat.min b (minlist a l)
 end.

Fixpoint maxlist a l :=
 match l with
 | [] => a
 | b::l => Nat.max b (maxlist a l)
 end.

Definition extrems l :=
  match l with
  | [] => (0,0)
  | a::l => (minlist a l, maxlist a l)
  end.

Lemma minlist_spec a l x : In x (a::l) -> minlist a l <= x.
Proof.
 induction l as [|b l IH].
 - intros [->|[ ]]. simpl. auto.
 - simpl in *. intuition; lia.
Qed.

Lemma minlist_in a l : In (minlist a l) (a::l).
Proof.
 induction l as [|b l IH].
 - simpl; now left.
 - simpl minlist.
   destruct (Nat.min_spec b (minlist a l)) as [(_,->)|(_,->)];
    simpl in *; intuition.
Qed.

Lemma maxlist_spec a l x : In x (a::l) -> x <= maxlist a l.
Proof.
 induction l as [|b l IH].
 - intros [->|[ ]]. simpl. auto.
 - simpl in *. intuition; lia.
Qed.

Lemma maxlist0_above l n : In n l -> n <= maxlist 0 l.
Proof.
 revert n.
 induction l; inversion 1; simpl; subst. apply Nat.le_max_l.
 transitivity (maxlist 0 l); auto. apply Nat.le_max_r.
Qed.

Lemma maxlist_in a l : In (maxlist a l) (a::l).
Proof.
 induction l as [|b l IH].
 - simpl; now left.
 - simpl maxlist.
   destruct (Nat.max_spec b (maxlist a l)) as [(_,->)|(_,->)];
    simpl in *; intuition.
Qed.

Lemma extrems_spec l a b x : In x l -> extrems l = (a,b) -> a<=x<=b.
Proof.
 intros IN.
 destruct l as [|n l]; try easy.
 simpl. intros [= <- <-]. split.
 now apply minlist_spec. now apply maxlist_spec.
Qed.

Lemma extrems_in1 l : l<>[] -> In (fst (extrems l)) l.
Proof.
 destruct l. easy. intros _. simpl fst. apply minlist_in.
Qed.

Lemma extrems_in2 l : l<>[] -> In (snd (extrems l)) l.
Proof.
 destruct l. easy. intros _. simpl fst. apply maxlist_in.
Qed.


(** Decreasing all elements of a list *)

Definition decr x y := Nat.sub y x.

Lemma decr_0 x : decr 0 x = x.
Proof.
 apply Nat.sub_0_r.
Qed.

Lemma map_decr_0 l : map (decr 0) l = l.
Proof.
 rewrite <- (map_id l) at 2. apply map_ext, decr_0.
Qed.

Lemma map_decr_1 l : map (decr 1) l = map pred l.
Proof.
 apply map_ext. intros; unfold decr. lia.
Qed.

Lemma map_decr_decr k k' l :
 map (decr k) (map (decr k') l) = map (decr (k+k')) l.
Proof.
 rewrite map_map. apply map_ext. unfold decr; lia.
Qed.

Lemma map_decr_S k l :
 map (decr (S k)) l = map (decr k) (map pred l).
Proof.
 now rewrite <- map_decr_1, map_decr_decr, Nat.add_1_r.
Qed.

Lemma map_decr_S' k l :
 map (decr (S k)) l = map pred (map (decr k) l).
Proof.
 now rewrite <- map_decr_1, map_decr_decr.
Qed.

Lemma map_S_pred l : ~In 0 l -> map S (map pred l) = l.
Proof.
 intros.
 rewrite map_map. rewrite <- (map_id l) at 2.
 apply map_ext_in.
 intros a Ha. assert (a<>0) by congruence. lia.
Qed.

(** take : the list of the n first elements of a infinite sequence
    (given as a function over nat). A.k.a List.init in OCaml. *)

Definition take {A} n (f:nat -> A) : list A := map f (seq 0 n).

Notation list_init := take (only parsing).

Lemma take_S {A} n (f:nat -> A) : take (S n) f = take n f ++ [f n].
Proof.
 unfold take. now rewrite seq_S, map_app.
Qed.

Lemma take_add {A} a b (f:nat->A) :
  take (a+b) f = take a f ++ map f (seq a b).
Proof.
 unfold take. now rewrite seq_app, map_app.
Qed.

Lemma take_S_shift {A} n (f:nat -> A) :
 take (S n) f = f 0 :: take n (fun n => f (S n)).
Proof.
 cbn. f_equal. now rewrite <- seq_shift, map_map.
Qed.

Lemma take_length {A} n (f:nat -> A) : length (take n f) = n.
Proof.
 unfold take. now rewrite map_length, seq_length.
Qed.

Lemma take_nth {A} f n m (a:A) : m < n -> nth m (take n f) a = f m.
Proof.
 intros L. unfold take.
 rewrite nth_map_indep with (d':=0) by now rewrite seq_length.
 f_equal. now apply seq_nth.
Qed.

Lemma in_take {A} (f:nat->A) n x :
  In x (take n f) <-> exists i, f i = x /\ i < n.
Proof.
 unfold take. rewrite in_map_iff. setoid_rewrite in_seq. firstorder lia.
Qed.

Lemma take_carac {A} n (u:list A) (f:nat->A) :
 length u = n ->
 (forall m a, m<n -> nth m u a = f m) ->
 take n f = u.
Proof.
 revert u f.
 induction n.
 - destruct u; simpl; easy.
 - intros u f Hu H. rewrite take_S.
   destruct (rev u) as [|a ru] eqn:E.
   + apply rev_switch in E. now subst u.
   + apply rev_switch in E. simpl in E. subst u.
     rewrite app_length in Hu. simpl in Hu.
     f_equal.
     * apply IHn; try lia.
       intros m b Hm.
       specialize (H m b). rewrite app_nth1 in H; auto; lia.
     * f_equal.
       specialize (H n a). rewrite app_nth2 in H; auto; try lia.
       replace (n - length (rev ru)) with 0 in H by lia. simpl in H.
       symmetry. apply H; auto.
Qed.

Lemma cumul_alt f n : cumul f n = list_sum (take n f).
Proof.
 induction n. trivial. unfold take in *.
 rewrite seq_S, map_app, list_sum_app, <- IHn. simpl. lia.
Qed.

(** Counting values in [list nat] *)

Fixpoint nbocc (a:nat) (l:list nat) :=
 match l with
 | [] => 0
 | b::l' => nbocc a l' + if b =? a then 1 else 0
 end.

(** [nbocc] is similar to [count_occ Nat.eq_dec], but more convenient
    (order of arguments, Nat.eqb instead of Nat.eq_dec) *)

Lemma nbocc_alt a l : nbocc a l = count_occ Nat.eq_dec l a.
Proof.
 induction l; simpl; auto. rewrite IHl.
 case Nat.eq_dec; case Nat.eqb_spec; lia.
Qed.

Lemma nbocc_app a u v : nbocc a (u++v) = nbocc a u + nbocc a v.
Proof.
 induction u; simpl; auto; lia.
Qed.

Lemma nbocc_le_length k u : nbocc k u <= length u.
Proof.
 induction u; simpl; trivial. case Nat.eqb; lia.
Qed.

Lemma nbocc_total_lt u k :
  Forall (fun n => n < k) u ->
  length u = cumul (fun n => nbocc n u) k.
Proof.
 induction u; simpl; intros H.
 - now rewrite cumul_0.
 - inversion_clear H. rewrite cumul_add. rewrite IHu by trivial.
   rewrite cumul_eqb; simpl; lia.
Qed.

Lemma nbocc_concat a l :
 nbocc a (concat l) = list_sum (map (nbocc a) l).
Proof.
 induction l as [|w l IH]; simpl; auto.
 rewrite nbocc_app. now f_equal.
Qed.

Lemma nbocc_notin x l : ~In x l -> nbocc x l = 0.
Proof.
 induction l; simpl; trivial.
 intros H. apply Decidable.not_or in H.
 case Nat.eqb_spec; try lia. intros. now rewrite IHl.
Qed.

Lemma nbocc_0 l x : nbocc x l = 0 -> ~In x l.
Proof.
 induction l as [|y l IH]; simpl; try easy.
 case Nat.eqb_spec; intros Y E; try lia.
 rewrite Nat.add_0_r in E. tauto.
Qed.

Lemma nbocc_S l x n :
  nbocc x l = S n ->
  exists l1 l2, l = l1 ++ x :: l2 /\ nbocc x l1 = O /\ nbocc x l2 = n.
Proof.
 revert n.
 induction l as [|y l IH]; intros n; simpl; try easy.
 case Nat.eqb_spec; intros Y E; try subst y.
 - exists [], l. split; simpl; trivial; lia.
 - rewrite Nat.add_0_r in E.
   destruct (IH n E) as (l1 & l2 & E0 & E1 & E2).
   exists (y::l1),l2. simpl; repeat split; trivial.
   + now rewrite E0.
   + case Nat.eqb_spec; lia.
Qed.

Lemma count_nbocc f a n : count f a n = nbocc a (take n f).
Proof.
 induction n. simpl; auto. rewrite take_S.
 rewrite nbocc_app. simpl. now f_equal.
Qed.

(** Same as nbocc but for counting value above a given threshold. *)

Fixpoint nbabove (a:nat) (l:list nat) :=
 match l with
 | [] => 0
 | b::l' => nbabove a l' + if a <=? b then 1 else 0
 end.

Lemma nbabove_app a u v : nbabove a (u++v) = nbabove a u + nbabove a v.
Proof.
 induction u; simpl; auto; lia.
Qed.

Lemma nbabove_le_length k u : nbabove k u <= length u.
Proof.
 induction u; simpl; trivial. case Nat.leb; lia.
Qed.

Lemma nbabove_0 x l : Forall (fun y => y < x) l -> nbabove x l = 0.
Proof.
 induction l; simpl; trivial.
 inversion 1; subst.
 case Nat.leb_spec; try lia. intros. now rewrite IHl.
Qed.

Lemma count_above_nbabove f a n : count_above f a n = nbabove a (take n f).
Proof.
 induction n. simpl; auto. rewrite take_S.
 rewrite nbabove_app. simpl. now f_equal.
Qed.

(** Some predicates on words : Prefix, Suffix, Sub *)

Definition Prefix {A} (u v : list A) := exists w, u++w = v.
Definition Suffix {A} (u v : list A) := exists w, w++u = v.
Definition Sub {A} (u v : list A) := exists w w', w++u++w' = v.

Lemma Prefix_id {A} (w : list A) : Prefix w w.
Proof.
 exists []. apply app_nil_r.
Qed.

Lemma Prefix_trans {A} (u v w : list A) :
  Prefix u v -> Prefix v w -> Prefix u w.
Proof.
 intros (u',<-) (v',<-). exists (u'++v'). apply app_assoc.
Qed.

Lemma Prefix_len {A} (u v : list A) : Prefix u v -> length u <= length v.
Proof.
 intros (w,<-). rewrite app_length. lia.
Qed.

Lemma Prefix_incl {A} (u v: list A) : Prefix u v -> incl u v.
Proof.
 intros (w,<-). now apply incl_appl.
Qed.

Lemma Prefix_antisym {A} (u v : list A) : Prefix u v -> Prefix v u -> u = v.
Proof.
 intros (u',<-) P. apply Prefix_len in P. rewrite app_length in P.
 assert (length u' = 0) by lia.
 destruct u'. now rewrite app_nil_r. easy.
Qed.

Lemma Prefix_nil {A} (u : list A) : Prefix u [] -> u = [].
Proof.
 intros Pr. apply Prefix_len in Pr. simpl in Pr. now destruct u.
Qed.

Lemma Prefix_cons {A} (a:A) u v : Prefix u v -> Prefix (a::u) (a::v).
Proof.
 intros (w,<-). now exists w.
Qed.

Lemma Prefix_nth {A} (u v : list A) :
  Prefix u v <->
   length u <= length v /\
   forall n a, n < length u -> nth n u a = nth n v a.
Proof.
 split.
 - intros (w & <-).
   rewrite app_length. split. lia. intros. rewrite app_nth1; auto.
 - revert v. induction u; intros v (LE,H).
   + now exists v.
   + simpl in LE. destruct v; try easy. simpl in LE.
     assert (P : Prefix u v).
     { apply IHu. split. lia.
       intros n b H'. apply (H (S n) b); simpl; auto with arith. }
     destruct P as (w & P).
     exists w. simpl. f_equal; auto.
     apply (H 0 a). simpl. lia.
Qed.

(** Specialized version when [A=nat] we can exploit a different default
    value and get rid of [length u <= length v]. Could be generalize to
    any non-singleton domain. *)

Lemma Prefix_nth_nat (u v : list nat) :
  Prefix u v <-> forall n a, n < length u -> nth n u a = nth n v a.
Proof.
 split.
 - intros (w & <-). intros. rewrite app_nth1; auto.
 - revert v. induction u; intros v H.
   + now exists v.
   + destruct v.
     * exfalso. specialize (H 0 (S a)). simpl in H. lia.
     * assert (P : Prefix u v).
       { apply IHu. intros m b H'. apply (H (S m) b). simpl. lia. }
       destruct P as (w & P).
       exists w. simpl. f_equal; auto.
       apply (H 0 a). simpl. lia.
Qed.

Lemma Prefix_cons_inv {A} (a:A) u v :
  Prefix u (a::v) -> u = [] \/ exists u', u = a::u' /\ Prefix u' v.
Proof.
 intros (w,E).
 destruct u as [|a' u'].
 - now left.
 - right. exists u'. injection E as -> E'. split; auto. now exists w.
Qed.

Lemma Prefix_Prefix {A} (u v w : list A) : length u <= length v ->
  Prefix u w -> Prefix v w -> Prefix u v.
Proof.
 intros L. rewrite !Prefix_nth. intros (LE,P) (LE',P').
 split. lia. intros n a Hn. now rewrite P, P' by lia.
Qed.

Lemma Prefix_app_r {A} (u v w : list A) :
  Prefix v w -> Prefix (u++v) (u++w).
Proof.
 intros (v' & <-). exists v'. now rewrite app_assoc.
Qed.

Lemma Prefix_app {A} (u v w : list A) :
 Prefix u (v++w) -> Prefix u v \/ exists u', u = v++u' /\ Prefix u' w.
Proof.
 revert v w.
 induction u.
 - intros v w _. left. now exists v.
 - intros v w (t,E). simpl in E.
   destruct v.
   + right. exists (a::u). split; auto. now exists t.
   + injection E as <- E.
     destruct (IHu v w) as [IH|(u',IH)]; try now exists t.
     * left. now apply Prefix_cons.
     * right. exists u'. simpl; split. now f_equal. apply IH.
Qed.

Lemma Prefix_seq (w : list nat) a n :
 Prefix w (List.seq a n) -> w = List.seq a (length w).
Proof.
 revert w a.
 induction n as [|n IH]; simpl; intros w a P.
 - apply Prefix_nil in P. now subst w.
 - apply Prefix_cons_inv in P. destruct P as [->|(w' & -> & P)]; trivial.
   simpl. f_equal; auto.
Qed.

Lemma Prefix_rev_Suffix {A} (u v : list A) :
  Prefix (rev u) (rev v) <-> Suffix u v.
Proof.
 split; intros (w,E).
 - exists (rev w).
   rewrite <- (rev_involutive w), <- rev_app_distr in E.
   now apply rev_inj in E.
 - exists (rev w). now rewrite <- rev_app_distr, E.
Qed.

Lemma Suffix_rev_Prefix {A} (u v : list A) :
  Suffix (rev u) (rev v) <-> Prefix u v.
Proof.
 now rewrite <- Prefix_rev_Suffix, !rev_involutive.
Qed.

Lemma Prefix_take {A}(w:nat->A) n m : n <= m -> Prefix (take n w) (take m w).
Proof.
 intros H.
 apply Prefix_nth; rewrite !take_length; split; trivial.
 intros p a Hp. rewrite !take_nth; trivial; lia.
Qed.

Lemma list_sum_prefix (u v:list nat) :
  Prefix u v -> list_sum u <= list_sum v.
Proof.
 intros (u',<-). rewrite list_sum_app. lia.
Qed.

Lemma Suffix_id {A} (w : list A) : Suffix w w.
Proof.
 now exists [].
Qed.

Lemma Suffix_trans {A} (u v w : list A) :
  Suffix u v -> Suffix v w -> Suffix u w.
Proof.
 intros (u',<-) (v',<-). exists (v'++u'). now rewrite app_assoc.
Qed.

Lemma Suffix_len {A} (u v : list A) : Suffix u v -> length u <= length v.
Proof.
 intros (w,<-). rewrite app_length. lia.
Qed.

Lemma Suffix_nil {A} (u : list A) : Suffix u [] -> u = [].
Proof.
 intros Su. apply Suffix_len in Su. simpl in Su. now destruct u.
Qed.

Lemma Suffix_app_l {A} (l u v : list A) : Suffix u v -> Suffix u (l++v).
Proof.
 intros (w,<-). exists (l++w). now rewrite app_assoc.
Qed.

Lemma Suffix_app_r {A} (u v r : list A) : Suffix u v -> Suffix (u++r) (v++r).
Proof.
 intros (w,<-). exists w. now rewrite app_assoc.
Qed.

Lemma Suffix_cons_inv {A} (a:A) u v :
 Suffix u (a::v) -> u = a::v \/ Suffix u v.
Proof.
 intros ([|a' w],E).
 - now left.
 - right. injection E as -> E. now exists w.
Qed.

Lemma Suffix_Suffix {A} (u v w : list A) : length u <= length v ->
  Suffix u w -> Suffix v w -> Suffix u v.
Proof.
 rewrite <- !Prefix_rev_Suffix. intro. apply Prefix_Prefix.
 now rewrite !rev_length.
Qed.

Lemma Suffix_app_inv {A} (u v w : list A) :
 Suffix u (v++w) -> Suffix u w \/ exists u', u = u'++w /\ Suffix u' v.
Proof.
 revert u. induction v as [|a v IH]; intros u H.
 - now left.
 - simpl in H. apply Suffix_cons_inv in H. destruct H as [->|H].
   + right. exists (a::v); split; auto. apply Suffix_id.
   + apply IH in H. destruct H as [H|(u' & E & H)].
     * now left.
     * right. exists u'; split; auto. now apply (Suffix_app_l [a]).
Qed.

Lemma Suffix_seq (w : list nat) a n :
 Suffix w (List.seq a n) -> w = List.seq (a+n-length w) (length w).
Proof.
 revert w a.
 induction n as [|n IH]; simpl; intros w a P.
 - apply Suffix_nil in P. now subst w.
 - apply Suffix_cons_inv in P. destruct P as [E|P].
   + replace (length w) with (S n).
     2:{ subst. simpl. now rewrite seq_length. }
     replace (a+_-_) with a by lia. trivial.
   + apply IH in P. rewrite P at 1. f_equal. lia.
Qed.

Lemma Sub_id {A} (w : list A) : Sub w w.
Proof.
 exists [], []. now rewrite app_nil_r.
Qed.

Lemma Sub_nil_l {A} (u : list A) : Sub [] u.
Proof.
 now exists [], u.
Qed.

Lemma Prefix_Sub {A} (u v : list A) : Prefix u v -> Sub u v.
Proof.
 intros (w,<-). now exists [], w.
Qed.

Lemma Suffix_Sub {A} (u v : list A) : Suffix u v -> Sub u v.
Proof.
 intros (w,<-). exists w, []. now rewrite app_nil_r.
Qed.

Lemma Sub_Prefix_Sub {A} (u v w : list A) : Sub u v -> Prefix v w -> Sub u w.
Proof.
 intros (u1 & u2 & <-) (v' & <-). exists u1, (u2++v').
 now rewrite !app_assoc.
Qed.

Lemma Sub_len {A} (u v : list A) : Sub u v -> length u <= length v.
Proof.
 intros (w & w' & <-). rewrite !app_length. lia.
Qed.

Lemma Sub_nil_r {A} (u : list A) : Sub u [] -> u = [].
Proof.
 intros H. apply Sub_len in H. simpl in H. now destruct u.
Qed.

Lemma Sub_app_l {A} (l u v : list A) : Sub u v -> Sub u (l++v).
Proof.
 intros (w & w' & <-). exists (l++w), w'. now rewrite <- app_assoc.
Qed.

Lemma Sub_app_r {A} (u v r : list A) : Sub u v -> Sub u (v++r).
Proof.
 intros (w & w' & <-). exists w, (w'++r). now rewrite !app_assoc.
Qed.

Lemma Sub_cons_r {A} (a:A) u : Sub u (a::u).
Proof.
 apply (Sub_app_l [a]), Sub_id.
Qed.

Lemma Sub_cons_inv {A} (a:A) u v :
 Sub u (a::v) -> Sub u v \/ exists u', u = a::u' /\ Prefix u' v.
Proof.
 intros ([|a' w] & w' & E).
 - destruct u as [|a' u'].
   + left. apply Sub_nil_l.
   + injection E as -> E. right. exists u'. split; trivial. now exists w'.
 - injection E as -> E. left. now exists w, w'.
Qed.

Lemma Sub_carac {A} (u v : list A) :
  Sub u v <-> exists w, Suffix u w /\ Prefix w v.
Proof.
 split.
 - intros (u1 & u2 & <-). exists (u1++u); split.
   + now exists u1.
   + exists u2. now rewrite app_assoc.
 - intros (w & (u1 & <-) & (u2 & <-)). exists u1, u2.
   now rewrite app_assoc.
Qed.

Lemma Sub_app_inv {A} (u l r : list A) :
 Sub u (l++r) ->
  Sub u l \/ Sub u r \/
  exists u1 u2, u1<>[] /\ u2<>[] /\ u = u1++u2 /\ Suffix u1 l /\ Prefix u2 r.
Proof.
 revert u. induction l as [|a l IH]; intros u H.
 - now (right; left).
 - simpl in H. apply Sub_cons_inv in H. destruct H as [H|(u' & E & H)].
   + apply IH in H. clear IH.
     destruct H as [H|[H|(u1 & u2 & U1 & U2 & E & Su & Pr)]].
     * left. now apply (Sub_app_l [a]).
     * now (right; left).
     * right; right. exists u1, u2; repeat split; trivial.
       now apply (Suffix_app_l [a]).
   + subst u. apply Prefix_app in H. destruct H as [H|(u2 & E & Pr)].
     * left. destruct H as (w & <-). now exists [], w.
     * destruct u2 as [|a2 u2].
       { rewrite app_nil_r in E. subst. left. apply Sub_id. }
       { right. right. exists (a::l), (a2::u2).
         repeat split; trivial; try easy.
         simpl; now f_equal. apply Suffix_id. }
Qed.

Lemma Sub_seq (w : list nat) a n :
 Sub w (List.seq a n) ->
 exists b, a <= b <= a+n-length w /\ w = List.seq b (length w).
Proof.
 revert w a.
 induction n as [|n IH]; simpl; intros w a H.
 - apply Sub_nil_r in H. subst w; simpl. exists a. split; trivial; lia.
 - apply Sub_cons_inv in H. destruct H as [H|(u & E & H)].
   + apply IH in H. destruct H as (b & Hb & E). exists b; split; trivial; lia.
   + subst w; simpl. assert (H' := Prefix_len _ _ H).
     rewrite seq_length in H'.
     apply Prefix_seq in H. exists a; split. lia. now f_equal.
Qed.

(** More on firstn, skipn, etc *)

Lemma firstn_seq a b n : n <= b -> firstn n (seq a b) = seq a n.
Proof.
 induction 1.
 - rewrite <- (seq_length n a) at 1. apply firstn_all.
 - rewrite seq_S, firstn_app, IHle.
   rewrite seq_length. replace (n-m) with 0 by lia. simpl. apply app_nil_r.
Qed.

Lemma firstn_take {A} (f:nat -> A) n m :
  n <= m -> firstn n (take m f) = take n f.
Proof.
 intros. unfold take. now rewrite firstn_map, firstn_seq.
Qed.

Lemma skipn_S {A} n (l:list A) : skipn (S n) l = tl (skipn n l).
Proof.
 revert l.
 induction n; destruct l; try easy. simpl. rewrite <- IHn. now destruct l.
Qed.

Lemma skipn_seq a b n : skipn n (seq a b) = seq (n+a) (b-n).
Proof.
 revert a b.
 induction n; intros; simpl.
 - f_equal. lia.
 - destruct b; simpl; auto.
   rewrite IHn. f_equal. lia.
Qed.

Lemma skipn_nodup {A} (l:list A) n : NoDup l -> NoDup (skipn n l).
Proof.
 revert l.
 induction n; try easy; intros [|a l]; simpl; try easy.
 intros D. inversion_clear D. now apply IHn.
Qed.

Lemma firstn_Prefix {A} n (l : list A) : Prefix (firstn n l) l.
Proof.
 exists (skipn n l). apply firstn_skipn.
Qed.

Lemma nth_firstn {A} n m (l:list A) a :
 m < n -> nth m (firstn n l) a = nth m l a.
Proof.
 revert l n.
 induction m; destruct n, l; simpl; trivial; try lia.
 intros. apply IHm. lia.
Qed.

Definition lastn {A} n (l:list A) := skipn (length l - n) l.

Lemma lastn_length_le {A} n (l:list A) :
  n <= length l -> length (lastn n l) = n.
Proof.
 intros H. unfold lastn. rewrite skipn_length. lia.
Qed.

Lemma last_lastn {A} u n (d:A) : n <> 0 -> last (lastn n u) d = last u d.
Proof.
 intros Hn.
 destruct u. trivial.
 unfold lastn.
 rewrite <- (firstn_skipn (length (a::u) - n) (a::u)) at 3.
 symmetry. apply last_app. rewrite <- length_zero_iff_nil, skipn_length.
 simpl length. lia.
Qed.

Lemma skipn_Suffix {A} n (u : list A) : Suffix (skipn n u) u.
Proof.
 unfold Suffix. exists (firstn n u). unfold lastn. apply firstn_skipn.
Qed.

Lemma lastn_Suffix {A} n (u : list A) : Suffix (lastn n u) u.
Proof.
 apply skipn_Suffix.
Qed.

Lemma Prefix_equiv {A} (u v : list A) :
  Prefix u v <-> u = firstn (length u) v.
Proof.
 split.
 - intros (u' & <-). rewrite firstn_app.
   replace (_-_) with 0 by lia.
   now rewrite firstn_O, firstn_all, app_nil_r.
 - intros ->. apply firstn_Prefix.
Qed.

Lemma Suffix_equiv {A} (u v : list A) :
  Suffix u v <-> u = lastn (length u) v.
Proof.
 split.
 - intros (u' & <-). unfold lastn. rewrite app_length.
   replace (_-_) with (length u') by lia.
   rewrite skipn_app.
   replace (_-_) with 0 by lia.
   now rewrite skipn_O, skipn_all.
 - intros ->. apply lastn_Suffix.
Qed.

(** [sub] : sub-list at some position and length *)

Definition sub {A} (l:list A) start len := firstn len (skipn start l).

Lemma sub_alt {A} (l:list A) start len :
 sub l start len = skipn start (firstn (start+len) l).
Proof.
 unfold sub. revert start.
 induction l; destruct start; simpl; auto. now rewrite firstn_nil.
Qed.

Lemma Sub_equiv {A} (u v : list A) :
  Sub u v <->
  exists i, i <= length v - length u /\ u = sub v i (length u).
Proof.
 rewrite Sub_carac. split.
 - intros (w & SU & PR). exists (length w - length u).
   assert (length u <= length w) by now apply Suffix_len.
   assert (length w <= length v) by now apply Prefix_len.
   split. lia. rewrite sub_alt.
   apply Suffix_equiv in SU.
   apply Prefix_equiv in PR. replace (_+_) with (length w) by lia.
   rewrite <- PR. exact SU.
 - intros (i & Hi & E). rewrite sub_alt in E.
   set (w := firstn (i+length u) v) in *.
   exists w; split; [|apply firstn_Prefix].
   rewrite E. apply skipn_Suffix.
Qed.

(** Boolean test of list equality, instead of [List.list_eq_dec]. *)

Open Scope lazy_bool_scope.

Fixpoint list_eqb {A} (eqb:A->A->bool) l l' :=
  match l, l' with
  | [], [] => true
  | x::l, x'::l' => (eqb x x') &&& (list_eqb eqb l l')
  | _, _ => false
  end.

Definition reflectEq {A} (eqb:A->A->bool) :=
  forall a a', reflect (a=a') (eqb a a').

Lemma list_eqb_spec {A} (eqb:A->A->bool) :
 reflectEq eqb -> reflectEq (list_eqb eqb).
Proof.
 intros R. red.
 induction a as [|a l IH]; destruct a' as [|a' l']; simpl;
  try case R; try case IH; constructor; congruence.
Qed.

Definition listnat_eqb := list_eqb Nat.eqb.

Definition listnat_eqb_spec := list_eqb_spec Nat.eqb Nat.eqb_spec.

(** Boolean tests for Prefix, Suffix, Sub on [list nat]. *)

Definition prefixb (u v : list nat) := listnat_eqb u (firstn (length u) v).
Definition suffixb (u v : list nat) := listnat_eqb u (lastn (length u) v).

Definition subb (u v : list nat) :=
 let len := length u in
 existsb (fun i => listnat_eqb u (sub v i len)) (seq 0 (S (length v - len))).

Lemma prefixb_spec (u v : list nat) : reflect (Prefix u v) (prefixb u v).
Proof.
 unfold prefixb.
 case listnat_eqb_spec; constructor; now rewrite Prefix_equiv.
Qed.

Lemma suffixb_spec (u v : list nat): reflect (Suffix u v) (suffixb u v).
Proof.
 unfold suffixb.
 case listnat_eqb_spec; constructor; now rewrite Suffix_equiv.
Qed.

Lemma subb_spec (u v : list nat) : reflect (Sub u v) (subb u v).
Proof.
 destruct (subb u v) eqn:E; unfold subb in *; constructor.
 - apply existsb_exists in E. destruct E as (i & Hi & E).
   rewrite Sub_equiv. exists i. split.
   + rewrite in_seq in Hi. destruct Hi. simpl in *. lia.
   + revert E. now case listnat_eqb_spec.
 - rewrite Sub_equiv. intros (i & Hi & E').
   contradict E. rewrite not_false_iff_true, existsb_exists.
   exists i. rewrite in_seq. split; try lia.
   now case listnat_eqb_spec.
Qed.

(** All sub-lists of a list.
    In general this enumeration may contain duplicates. *)

Definition allsubs {A} p (u:list A) :=
  take (S (length u) - p) (fun i => sub u i p).

Lemma allsubs_length {A} p (u:list A) :
  length (allsubs p u) = S (length u) - p.
Proof.
 unfold allsubs. now rewrite take_length.
Qed.

Lemma allsubs_ok {A} p (u:list A) :
  forall w, In w (allsubs p u) <-> length w = p /\ Sub w u.
Proof.
 intros. unfold allsubs. rewrite in_take.
 split.
 - intros (i & <- & Hi).
   rewrite Sub_equiv.
   replace (length (sub u i p)) with p.
   2:{ unfold sub. rewrite firstn_length_le; auto.
       rewrite skipn_length. lia. }
   split; trivial. exists i. split; auto; lia.
 - intros (L & SU). assert (L' := Sub_len _ _ SU).
   rewrite Sub_equiv in SU. destruct SU as (i & Hi & E).
   exists i. split. congruence. lia.
Qed.

(** [map_appr] : concatenating a suffix at the right of many words *)

Definition appr {A} (u v:list A) := v++u.

Definition map_appr {A} l (v:list A) := map (appr v) l.

Lemma map_appr_nil {A} (l:list (list A)) : map_appr l [] = l.
Proof.
 unfold map_appr. rewrite map_ext with (g:=id). apply map_id.
 intro. apply app_nil_r.
Qed.

Lemma map_appr_in {A} l (v u:list A) :
 In u (map_appr l v) <-> exists w,  w++v = u /\ In w l.
Proof.
 apply in_map_iff.
Qed.

(** Proving that a list has length >= 1 (resp. >= 2). *)

Lemma lengthge1_carac {A}(a:A) l : In a l -> 1 <= length l.
Proof.
 destruct l as [|b l]. inversion 1. simpl. lia.
Qed.

Lemma lengthge2_carac {A}(a b:A) l :
  a<>b -> In a l -> In b l -> 2 <= length l.
Proof.
 destruct l as [|c [|d l]]; simpl; try easy; try lia.
 now intros ND [<-|[ ]] [<-|[ ]].
Qed.

(** [Below l x] means that [x] is a strict upper bound for [l] *)

Definition Below l x := forall y, In y l -> y < x.

(** Various statements of the pigeonhole principle *)

Lemma pigeonhole_nbocc n l :
  Below l n -> n < length l -> exists x, 1 < nbocc x l.
Proof.
 revert l.
 induction n.
 - destruct l as [|x l]; simpl; try lia.
   intros B _. specialize (B x); simpl in B; lia.
 - intros l B L.
   destruct (Nat.lt_ge_cases 1 (nbocc n l)).
   + now exists n.
   + destruct (Nat.le_gt_cases 1 (nbocc n l)).
     * destruct (nbocc_S l n 0 ltac:(lia)) as (l1 & l2 & E0 & E1 & E2).
       destruct (IHn (l1++l2)) as (x & Hx).
       { intros x Hx.
         apply nbocc_0 in E1, E2.
         assert (x < S n)%nat.
         { apply B. rewrite E0. rewrite in_app_iff in *. simpl. tauto. }
         assert (x <> n) by (intros ->; rewrite in_app_iff in *; tauto).
         lia. }
       { rewrite E0 in L. rewrite app_length in *. simpl in L. lia. }
       exists x. rewrite E0. rewrite nbocc_app in *. simpl. lia.
     * apply (IHn l); try lia.
       intros x Hx. specialize (B x Hx).
       assert (~In n l). { apply nbocc_0. lia. }
       assert (x <> n) by (now intros ->).
       lia.
Qed.

Lemma pigeonhole_dup n l : Below l n -> n < length l -> ~NoDup l.
Proof.
 intros B L. destruct (pigeonhole_nbocc n l B L) as (m & Hm).
 rewrite (NoDup_count_occ Nat.eq_dec). intros H. specialize (H m).
 rewrite <- nbocc_alt in H. lia.
Qed.

Lemma pigeonhole_split n l :
  Below l n -> n < length l ->
  exists x l1 l2 l3, l = l1 ++ x :: l2 ++ x :: l3.
Proof.
 intros B L. destruct (pigeonhole_nbocc n l B L) as (x & Hx).
 destruct (nbocc_S l x (nbocc x l - 1) ltac:(lia))
   as (l1 & l23 & E & _ & E23).
 destruct (nbocc_S l23 x (nbocc x l - 2) ltac:(lia))
   as (l2 & l3 & E' & _ & _).
 exists x,l1,l2,l3. now rewrite E,E'.
Qed.

(** More on nth_error *)

Lemma nth_error_ext {A} (l l':list A) :
  (forall n, nth_error l n = nth_error l' n) -> l = l'.
Proof.
 revert l'.
 induction l; destruct l'; intros H; trivial; try now specialize (H O).
 f_equal.
 - now injection (H O).
 - apply IHl. intros n. apply (H (S n)).
Qed.

Lemma nth_error_ext' {A} (l l':list A) :
 length l = length l' ->
 (forall n, n < length l -> nth_error l n = nth_error l' n) ->
 l = l'.
Proof.
 intros E H.
 apply nth_error_ext. intros n.
 destruct (Nat.lt_ge_cases n (length l)) as [LT|GE].
 - now apply H.
 - destruct (nth_error_None l n) as (_,->); trivial.
   rewrite E in GE. destruct (nth_error_None l' n) as (_,->); trivial.
Qed.

Lemma nth_error_map {A B} (f:A -> B) (l:list A) n :
  nth_error (List.map f l) n = option_map f (nth_error l n).
Proof.
 revert n. induction l; destruct n; simpl; easy.
Qed.
Lemma nth_error_seq (a b n : nat) : (n < b)%nat ->
  nth_error (seq a b) n = Some (a+n).
Proof.
 revert a n. induction b; destruct n; intros; simpl; try lia.
 - f_equal. lia.
 - rewrite Nat.add_succ_r. apply IHb. lia.
Qed.

(** Mix : alternate elements from l1 and l2. Used in FlexArray.to_list *)

Fixpoint mix {A} (l1 l2 : list A) :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | x1::l1, x2::l2 => x1::x2::mix l1 l2
  end.

Lemma mix_eqn {A} (a1:A) l1 l2 : mix (a1::l1) l2 = a1 :: mix l2 l1.
Proof.
 revert l1 a1 l2. fix IH 1.
 destruct l1 as [|b1 [|c1 l1]], l2 as [|a2 [|b2 l2]]; simpl; trivial.
 do 4 f_equal. apply (IH l1 c1 l2).
Qed.

Lemma mix_concat_l {A} l1 l2 (a1:A) :
 length l1 = length l2 ->
 mix (l1++[a1]) l2 = mix l1 l2 ++ [a1].
Proof.
 revert l2 a1.
 induction l1; destruct l2; simpl; intros a1 E; try easy.
 f_equal. f_equal. apply IHl1; lia.
Qed.

Lemma mix_concat_r {A} l1 l2 (a2:A) :
 length l1 = S (length l2) ->
 mix l1 (l2++[a2]) = mix l1 l2 ++ [a2].
Proof.
 revert l2 a2.
 induction l1; destruct l2; simpl; intros a2 E; try easy.
 - now destruct l1.
 - f_equal. f_equal. apply IHl1; lia.
Qed.

Lemma mix_spec {A} (l1 l2 : list A) :
  length l2 <= length l1 <= S (length l2) ->
  forall n,
  nth_error (mix l1 l2) (2*n) = nth_error l1 n
  /\ nth_error (mix l1 l2) (2*n+1) = nth_error l2 n.
Proof.
 revert l2.
 induction l1 as [|a1 l1 IH]; destruct l2 as [|a2 l2]; simpl; try lia.
 - intros _. now destruct n.
 - destruct l1 as [|b1 l1]; simpl; try lia.
   intros _. destruct n; simpl; try easy.
   rewrite Nat.add_succ_r. simpl. now destruct n.
 - intros H. destruct n; simpl; try easy.
   rewrite Nat.add_succ_r. simpl. apply IH. lia.
Qed.

Lemma mix_length {A} (l1 l2 : list A) :
  length (mix l1 l2) = length l1 + length l2.
Proof.
 revert l2. induction l1; destruct l2; simpl; rewrite ?IHl1; lia.
Qed.

Lemma mix_permut {A} (l1 l2 : list A) : Permutation (mix l1 l2) (l1++l2).
Proof.
 revert l2. induction l1; destruct l2; simpl; rewrite ?app_nil_r; try easy.
 apply perm_skip. rewrite IHl1. apply Permutation_middle.
Qed.
