From Coq Require Import List Arith NArith Lia.
Require Import MoreList.
Import ListNotations.
Local Open Scope N.

(** * Flexible Persistent Arrays.

    Operations size, get, set, cons, tail, snoc, liat have logarithmic
    complexity.

    Inspired by: https://github.com/backtracking/flex-array
    Modifications:
    - Non-empty, i.e. a [Leaf _] constructor instead of an [Empty].
      simpler this way, but [get _ 0] is not constant anymore.
    - Instead of storing externally the whole size, we store its parity
      at each node.
*)

Definition parity := bool.

Inductive tree (A:Type) :=
 | Leaf : A -> tree A
 | Node : parity -> tree A -> tree A -> tree A.

Arguments Leaf {A}.
Arguments Node {A}.

Fixpoint size {A} (t : tree A) :=
  match t with
  | Leaf _ => 1
  | Node parity _ t => N.double (size t) + if parity then 0 else 1
  end.

Definition singleton {A} (a:A) := Leaf a.

Fixpoint get {A} (t : tree A) n : A :=
  match t with
  | Leaf x => x
  | Node _ evens odds =>
    if N.even n then get evens (N.div2 n) else get odds (N.div2 n)
  end.

Fixpoint set {A} (t : tree A) n x :=
  match t with
  | Leaf _ => Leaf x
  | Node p evens odds =>
    if N.even n then
      Node p (set evens (N.div2 n) x) odds
    else
      Node p evens (set odds (N.div2 n) x)
  end.

Fixpoint cons {A} x (t : tree A) :=
  match t with
  | Leaf _ => Node true (Leaf x) t
  | Node parity evens odds => Node (negb parity) (cons x odds) evens
  end.

Fixpoint snoc {A} (t : tree A) x :=
  match t with
  | Leaf y => Node true (Leaf y) (Leaf x)
  | Node true evens odds => Node false (snoc evens x) odds
  | Node false evens odds => Node true evens (snoc odds x)
  end.

(** tail_or_id and liat_or_id :
    remove first (resp. last) on non-singleton, leave singletons intact *)

Fixpoint tail_or_id {A} (t : tree A) : tree A :=
  match t with
  | Leaf _ => t
  | Node _ (Leaf _) t => t
  | Node parity evens odds => Node (negb parity) odds (tail_or_id evens)
  end.

Fixpoint liat_or_id {A} (t : tree A) : tree A :=
  match t with
  | Leaf _ => t
  | Node _ ((Leaf x) as t') _ => t'
  | Node p evens odds =>
    if p then Node false evens (liat_or_id odds)
         else Node true (liat_or_id evens) odds
  end.

(** tail and liat : return None on singletons *)

Definition tail {A} (t : tree A) : option (tree A) :=
  match t with
  | Leaf _ => None
  | _ => Some (tail_or_id t)
  end.

Definition liat {A} (t : tree A) : option (tree A) :=
  match t with
  | Leaf _ => None
  | _ => Some (liat_or_id t)
  end.

Fixpoint to_list {A} (t : tree A) :=
  match t with
  | Leaf x => [x]
  | Node _ evens odds => mix (to_list evens) (to_list odds)
  end.

Fixpoint of_list {A} (a : A) (l : list A) : tree A :=
  match l with
  | [] => Leaf a
  | x::l' => cons a (of_list x l')
  end.

Fixpoint map {A B} (f : A -> B) (t:tree A) : tree B :=
  match t with
  | Leaf x => Leaf (f x)
  | Node parity evens odds => Node parity (map f evens) (map f odds)
  end.

Fixpoint mapi {A B} (f : N -> A -> B) (t:tree A) : tree B :=
  match t with
  | Leaf x => Leaf (f 0 x)
  | Node parity evens odds =>
    Node parity (mapi (fun i x => f (N.double i) x) evens)
                (mapi (fun i x => f (N.succ_double i) x) odds)
  end.

Fixpoint reduce {A} (op : A -> A -> A) (t : tree A) : A :=
  match t with
  | Leaf x => x
  | Node _ evens odds => op (reduce op evens) (reduce op odds)
  end.

Fixpoint map_reduce {A B} (f : A -> B) (op : B -> B -> B) (t : tree A) : B :=
  match t with
  | Leaf x => f x
  | Node _ evens odds => op (map_reduce f op evens) (map_reduce f op odds)
  end.

(** Proofs *)

Fixpoint fullsize {A} (t:tree A) :=
 match t with
 | Leaf _ => 1
 | Node _ evens odds => fullsize evens + fullsize odds
 end.

Fixpoint Ok {A} (t:tree A) :=
 match t with
 | Leaf _ => True
 | Node parity evens odds =>
   Ok evens /\ Ok odds /\
   fullsize evens = fullsize odds + if parity then 0 else 1
 end.

Lemma size_spec {A} (t:tree A) : Ok t -> size t = fullsize t.
Proof.
 induction t; simpl; trivial.
 intros (H1 & H2 & E).
 rewrite IHt2 by trivial. rewrite E. lia.
Qed.

Inductive Get {A} : tree A -> N -> A -> Prop :=
 | GLeaf a : Get (Leaf a) 0 a
 | GEven parity evens odds n a :
     Get evens n a -> Get (Node parity evens odds) (2*n) a
 | GOdd parity evens odds n a :
     Get odds n a -> Get (Node parity evens odds) (2*n+1) a.

Lemma Get_fun {A} (t:tree A) : forall n a b, Get t n a -> Get t n b -> a=b.
Proof.
 induction 1; inversion 1; try easy.
 - change (N.double n0 = N.double n) in H5.
   replace n0 with n in H6 by lia. now apply IHGet.
 - change (N.double n0 + 1 = N.double n) in H5. lia.
 - change (N.double n0 = N.double n + 1) in H5. lia.
 - change (N.double n0 + 1 = N.double n + 1) in H5.
   replace n0 with n in H6 by lia. now apply IHGet.
Qed.

Lemma get_spec {A} n (t:tree A) :
  Ok t -> n < fullsize t -> Get t n (get t n).
Proof.
 revert n.
 induction t; simpl; intros n OK Hn.
 - replace n with 0 by lia. apply GLeaf.
 - destruct (N.even n) eqn:E.
   + rewrite N.even_spec in E. destruct E as (m & ->).
     apply GEven. replace (N.div2 _) with m.
     2:{ symmetry. apply N.div2_double. }
     apply IHt1. apply OK. lia.
   + rewrite <- N.negb_odd in E. apply Bool.negb_false_iff in E.
     rewrite N.odd_spec in E. destruct E as (m & ->).
     apply GOdd. replace (N.div2 _) with m.
     2:{ now rewrite <- N.succ_double_spec, N.div2_succ_double. }
     apply IHt2. apply OK. destruct p; lia.
Qed.

Lemma to_list_length {A} (t:tree A) :
 length (to_list t) = N.to_nat (fullsize t).
Proof.
 induction t; simpl; trivial. rewrite mix_length, IHt1, IHt2. lia.
Qed.

Lemma to_list_spec {A} n a (t:tree A) :
 Ok t -> n < size t ->
 nth_error (to_list t) (N.to_nat n) = Some a <-> Get t n a.
Proof.
 revert n a. induction t as [x|p t1 IH1 t2 IH2]; simpl; intros n a OK LT.
 - replace n with 0 by lia. simpl.
   split.
   + intros [= ->]; constructor.
   + inversion 1; now subst.
 - set (l1 := to_list t1) in *.
   set (l2 := to_list t2) in *.
   assert (H : (length l2 <= length l1 <= S (length l2))%nat).
   { unfold l1,l2. rewrite !to_list_length. destruct p; lia. }
   destruct (N.Even_or_Odd n) as [(m & Hm)|(m & Hm)].
   + subst n. rewrite N2Nat.inj_mul. change (N.to_nat 2) with 2%nat.
     destruct (mix_spec (to_list t1) (to_list t2) H (N.to_nat m)) as (H1,_).
     fold l1 l2 in H1. rewrite H1, IH1; try easy.
     * split. apply GEven. inversion 1; subst; trivial.
       { replace m with n; trivial.
         assert (N.double n = N.double m) by easy. lia. }
       { assert (N.double n + 1 = N.double m) by easy. lia. }
     * rewrite size_spec by apply OK. rewrite size_spec in LT by apply OK.
       destruct p; lia.
   + subst n. rewrite N2Nat.inj_add, N2Nat.inj_mul.
     change (N.to_nat 2) with 2%nat. change (N.to_nat 1) with 1%nat.
     destruct (mix_spec (to_list t1) (to_list t2) H (N.to_nat m)) as (_,H2).
     fold l1 l2 in H2. rewrite H2, IH2; try easy.
     * split. apply GOdd. inversion 1; subst; trivial.
       { assert (N.double n = N.double m + 1) by easy. lia. }
       { replace m with n; trivial.
         assert (N.double n + 1 = N.double m + 1) by easy. lia. }
     * rewrite size_spec by apply OK. rewrite size_spec in LT by apply OK.
       destruct p; lia.
Qed.

Lemma to_list_spec' {A} (t:tree A) :
 Ok t ->
 to_list t = List.map (fun n => get t (N.of_nat n)) (seq 0 (N.to_nat (size t))).
Proof.
 intros OK. apply nth_error_ext'.
 - now rewrite to_list_length, map_length, seq_length, size_spec.
 - intros n Hn.
   destruct (nth_error (to_list t) n) as [a|] eqn:E; symmetry.
   + rewrite to_list_length, <- size_spec in Hn; trivial.
     rewrite <- (Nat2N.id n) in E.
     apply to_list_spec in E; trivial. 2:lia.
     rewrite nth_error_map, nth_error_seq; trivial. simpl. f_equal.
     eapply Get_fun; eauto. apply get_spec; trivial.
     rewrite <- size_spec; trivial. lia.
   + apply nth_error_None in E. lia.
Qed.

Lemma get_to_list {A} n (t:tree A)(d:A) :
  Ok t -> n < size t -> get t n = nth (N.to_nat n) (to_list t) d.
Proof.
 intros OK LT. rewrite to_list_spec'; trivial.
 rewrite nth_map_indep with (d':=O) by (rewrite seq_length; lia).
 rewrite seq_nth by lia. f_equal; lia.
Qed.

Lemma singleton_to_list {A} (a:A) : to_list (singleton a) = [a].
Proof.
 easy.
Qed.

Lemma cons_to_list {A} a (t:tree A) :
 Ok t -> to_list (cons a t) = a :: to_list t.
Proof.
 induction t; simpl; intros OK; trivial.
 rewrite IHt2; try easy. apply mix_eqn.
Qed.

Lemma snoc_to_list {A} (t:tree A) a :
 Ok t -> to_list (snoc t a) = to_list t ++ [a].
Proof.
 induction t; simpl; intros OK; trivial.
 destruct p; simpl.
 - rewrite IHt1; try easy. apply mix_concat_l. rewrite !to_list_length. lia.
 - rewrite IHt2; try easy. apply mix_concat_r. rewrite !to_list_length. lia.
Qed.

Lemma cons_fullsize {A} a (t:tree A) :
  fullsize (cons a t) = N.succ (fullsize t).
Proof.
 induction t; simpl; trivial. rewrite IHt2. lia.
Qed.

Lemma snoc_fullsize {A} (t:tree A) a :
  fullsize (snoc t a) = N.succ (fullsize t).
Proof.
 induction t; simpl; trivial.
 destruct p; simpl; rewrite ?IHt1, ?IHt2; lia.
Qed.

Lemma cons_ok {A} a (t:tree A) : Ok t -> Ok (cons a t).
Proof.
 induction t; simpl; intros OK; repeat split; try tauto.
 rewrite cons_fullsize. destruct p; simpl; lia.
Qed.

Lemma snoc_ok {A} (t:tree A) a : Ok t -> Ok (snoc t a).
Proof.
 induction t; simpl; intros OK; repeat split; try tauto.
 destruct p; simpl.
 - repeat split; try apply IHt1; try easy. rewrite snoc_fullsize; lia.
 - repeat split; try apply IHt2; try easy. rewrite snoc_fullsize; lia.
Qed.

Lemma cons_size {A} a (t:tree A) : Ok t -> size (cons a t) = N.succ (size t).
Proof.
 intros. rewrite !size_spec; auto using cons_ok. apply cons_fullsize.
Qed.

Lemma snoc_size {A} (t:tree A) a : Ok t -> size (snoc t a) = N.succ (size t).
Proof.
 intros. rewrite !size_spec; auto using snoc_ok. apply snoc_fullsize.
Qed.

Lemma fullsize_pos {A} (t:tree A) : 1 <= fullsize t.
Proof.
 induction t; simpl; lia.
Qed.

Lemma fullsize_node {A} p (t1 t2:tree A) : 2 <= fullsize (Node p t1 t2).
Proof.
 simpl. generalize (fullsize_pos t1) (fullsize_pos t2). lia.
Qed.

Lemma tail_or_id_fullsize {A} (t:tree A) :
 fullsize (tail_or_id t) = N.max 1 (fullsize t - 1).
Proof.
 induction t; simpl; try lia.
 destruct t1.
 - simpl fullsize. generalize (fullsize_pos t2). lia.
 - assert (LE := fullsize_node p0 t1_1 t1_2).
   remember (Node p0 t1_1 t1_2) as t1.
   simpl. rewrite IHt1. generalize (fullsize_pos t2). lia.
Qed.

Lemma tail_or_id_ok {A} (t:tree A) : Ok t -> Ok (tail_or_id t).
Proof.
 induction t; simpl; trivial.
 destruct t1.
 - tauto.
 - assert (LE := fullsize_node p0 t1_1 t1_2).
   remember (Node p0 t1_1 t1_2) as t1. intros OK.
   simpl. repeat split; try easy. now apply IHt1.
   rewrite tail_or_id_fullsize.
   destruct p; simpl; lia.
Qed.

Lemma tail_or_id_size {A} (t:tree A) : Ok t ->
 size (tail_or_id t) = N.max 1 (size t - 1).
Proof.
 intros. rewrite !size_spec; auto using tail_or_id_fullsize, tail_or_id_ok.
Qed.

Lemma tail_or_id_spec {A} (t:tree A) :
  Ok t -> 2 <= size t -> to_list (tail_or_id t) = tl (to_list t).
Proof.
 intros OK. rewrite size_spec by trivial. revert OK.
 induction t; simpl; try lia.
 destruct t1; intros OK LE.
 - simpl. now destruct (to_list t2).
 - assert (LE' := fullsize_node p0 t1_1 t1_2).
   remember (Node p0 t1_1 t1_2) as t1.
   simpl. rewrite IHt1; try easy.
   assert (E1 := to_list_length t1).
   destruct (to_list t1) as [|a l1].
   + simpl in E1. lia.
   + now rewrite mix_eqn.
Qed.

Lemma tail_none {A} (t:tree A) : tail t = None <-> fullsize t = 1.
Proof.
 destruct t.
 - easy.
 - simpl. split; try easy.
   generalize (fullsize_pos t1) (fullsize_pos t2); lia.
Qed.

Lemma tail_ok {A} (t t':tree A) : Ok t -> tail t = Some t' -> Ok t'.
Proof.
 destruct t; cbn -[tail_or_id]; try easy.
 intros OK [= <-]. now apply (tail_or_id_ok (Node p t1 t2)).
Qed.

Lemma tail_size {A} (t t':tree A) :
 Ok t -> tail t = Some t' -> size t' = size t - 1.
Proof.
 intros OK E. rewrite !size_spec; trivial. 2:{ eapply tail_ok; eauto. }
 destruct t; cbn -[tail_or_id]; try easy.
 unfold tail in E. injection E as <-.
 change (fullsize (tail_or_id (Node p t1 t2)) = fullsize t1 + fullsize t2 -1).
 rewrite tail_or_id_fullsize. simpl.
 generalize (fullsize_pos t1) (fullsize_pos t2). lia.
Qed.

Lemma tail_spec {A} (t t':tree A) :
  Ok t -> tail t = Some t' -> to_list t' = tl (to_list t).
Proof.
 intros OK E. destruct t; simpl in *; try easy.
 injection E as E. change (tail_or_id (Node p t1 t2) = t') in E.
 rewrite <- E. rewrite tail_or_id_spec. easy. apply OK.
 rewrite size_spec. simpl.
 generalize (fullsize_pos t1) (fullsize_pos t2). lia. apply OK.
Qed.

Lemma liat_or_id_fullsize {A} (t:tree A) :
 Ok t -> fullsize (liat_or_id t) = N.max 1 (fullsize t - 1).
Proof.
 induction t; simpl; intros OK; try lia.
 destruct t1.
 - simpl fullsize. simpl in OK. destruct p; lia.
 - assert (LE := fullsize_node p0 t1_1 t1_2).
   remember (Node p0 t1_1 t1_2) as t1.
   destruct p.
   + simpl. rewrite IHt2 by easy.
     rewrite N.add_0_r in OK.
     destruct OK as (_ & _ & <-). lia.
   + simpl. rewrite IHt1 by easy. lia.
Qed.

Lemma liat_or_id_ok {A} (t:tree A) : Ok t -> Ok (liat_or_id t).
Proof.
 induction t; simpl; trivial.
 destruct t1; try easy.
 assert (LE := fullsize_node p0 t1_1 t1_2).
 remember (Node p0 t1_1 t1_2) as t1. intros OK.
 destruct p.
 - simpl. repeat split; try tauto.
   rewrite liat_or_id_fullsize by apply OK.
   rewrite N.add_0_r in OK.
   destruct OK as (_ & _ & <-). lia.
 - simpl. repeat split; try tauto.
   rewrite liat_or_id_fullsize by apply OK.
   destruct OK as (_ & _ & ->). generalize (fullsize_pos t2). lia.
Qed.

Lemma liat_or_id_size {A} (t:tree A) : Ok t ->
 size (liat_or_id t) = N.max 1 (size t - 1).
Proof.
 intros. rewrite !size_spec; auto using liat_or_id_fullsize, liat_or_id_ok.
Qed.

Lemma removelast_mix_eq {A} (l1 l2:list A) : length l1 = length l2 ->
  removelast (mix l1 l2) = mix l1 (removelast l2).
Proof.
 intros E.
 destruct l1 as [|a1 l1]; try easy.
 destruct l2 as [|a2 l2]; try easy.
 assert (E' : a2::l2 <> []) by easy.
 apply app_removelast_last with (d:=a2) in E'.
 rewrite E' at 1.
 rewrite mix_concat_r.
 - now rewrite removelast_last.
 - rewrite E. rewrite E' at 1. rewrite app_length; simpl; lia.
Qed.

Lemma removelast_mix_neq {A} (l1 l2:list A) : length l1 = S (length l2) ->
  removelast (mix l1 l2) = mix (removelast l1) l2.
Proof.
 intros E.
 destruct l1 as [|a1 l1]; try easy. simpl in E.
 assert (E' : a1::l1 <> []) by easy.
 apply app_removelast_last with (d:=a1) in E'.
 rewrite E' at 1.
 rewrite mix_concat_l.
 - now rewrite removelast_last.
 - apply (f_equal (@length A)) in E'. rewrite app_length in E'.
   change (length [_]) with 1%nat in E'.
   change (length (a1::l1)) with (S (length l1)) in E'. lia.
Qed.

Lemma liat_or_id_spec {A} (t:tree A) :
  Ok t -> 2 <= size t -> to_list (liat_or_id t) = removelast (to_list t).
Proof.
 intros OK. rewrite size_spec by trivial. revert OK.
 induction t; simpl; try lia.
 destruct t1; intros OK LE.
 - simpl in OK. simpl fullsize in LE.
   destruct p; try lia.
   destruct t2; try easy.
   generalize (fullsize_node p t2_1 t2_2). lia.
 - assert (LE' := fullsize_node p0 t1_1 t1_2).
   remember (Node p0 t1_1 t1_2) as t1.
   destruct p.
   + simpl. rewrite N.add_0_r in OK. rewrite IHt2 by (easy||lia).
     rewrite <- removelast_mix_eq; trivial.
     rewrite !to_list_length. lia.
   + simpl. rewrite IHt1 by (easy||lia).
     rewrite <- removelast_mix_neq; trivial.
     rewrite !to_list_length. lia.
Qed.

Lemma liat_none {A} (t:tree A) : liat t = None <-> fullsize t = 1.
Proof.
 destruct t.
 - easy.
 - simpl. split; try easy.
   generalize (fullsize_pos t1) (fullsize_pos t2); lia.
Qed.

Lemma liat_ok {A} (t t':tree A) : Ok t -> liat t = Some t' -> Ok t'.
Proof.
 destruct t; cbn -[liat_or_id]; try easy.
 intros OK [= <-]. now apply (liat_or_id_ok (Node p t1 t2)).
Qed.

Lemma liat_size {A} (t t':tree A) :
 Ok t -> liat t = Some t' -> size t' = size t - 1.
Proof.
 intros OK E. rewrite !size_spec; trivial. 2:{ eapply liat_ok; eauto. }
 destruct t; cbn -[liat_or_id]; try easy.
 unfold liat in E. injection E as <-.
 change (fullsize (liat_or_id (Node p t1 t2)) = fullsize t1 + fullsize t2 -1).
 rewrite liat_or_id_fullsize; trivial. simpl.
 generalize (fullsize_pos t1) (fullsize_pos t2). lia.
Qed.

Lemma liat_spec {A} (t t':tree A) :
  Ok t -> liat t = Some t' -> to_list t' = removelast (to_list t).
Proof.
 intros OK E. destruct t; simpl in *; try easy.
 injection E as E. change (liat_or_id (Node p t1 t2) = t') in E.
 rewrite <- E. rewrite liat_or_id_spec. easy. apply OK.
 rewrite size_spec. simpl.
 generalize (fullsize_pos t1) (fullsize_pos t2). lia. apply OK.
Qed.

(** TODO specs of [set] *)

Lemma of_list_ok {A} a (l:list A) : Ok (of_list a l).
Proof.
 revert a. induction l; simpl; trivial. intros b. now apply cons_ok.
Qed.

Lemma of_list_size {A} a (l:list A) :
  size (of_list a l) = N.succ (N.of_nat (length l)).
Proof.
 revert a. induction l; trivial. intros b.
 simpl of_list. rewrite cons_size by apply of_list_ok.
 rewrite IHl. simpl length. lia.
Qed.

Lemma of_to_list {A} a (l:list A) : to_list (of_list a l) = a::l.
Proof.
 revert a. induction l; simpl; trivial. intros b.
 rewrite cons_to_list by apply of_list_ok. f_equal. apply IHl.
Qed.

Lemma mix_map {A B} (f:A->B) (l1 l2:list A) :
  mix (List.map f l1) (List.map f l2) = List.map f (mix l1 l2).
Proof.
 revert l2. induction l1; destruct l2; simpl; trivial.
 f_equal. f_equal. apply IHl1.
Qed.

Lemma map_to_list {A B} (f:A->B) (t:tree A) :
 Ok t -> to_list (map f t) = List.map f (to_list t).
Proof.
 induction t; simpl; intros OK; trivial.
 now rewrite IHt1, IHt2, mix_map.
Qed.

Lemma map_fullsize {A B} (f:A->B) (t:tree A) :
 fullsize (map f t) = fullsize t.
Proof.
 induction t; simpl; lia.
Qed.

Lemma map_ok {A B} (f:A->B) (t:tree A) :
 Ok t -> Ok (map f t).
Proof.
 induction t; simpl; trivial. rewrite !map_fullsize. tauto.
Qed.

Lemma map_size {A B} (f:A->B) (t:tree A) :
 Ok t -> size (map f t) = size t.
Proof.
 intros. rewrite !size_spec; trivial. apply map_fullsize. now apply map_ok.
Qed.


Lemma mapi_fullsize {A B} (f:N->A->B) (t:tree A) :
 fullsize (mapi f t) = fullsize t.
Proof.
 revert f. induction t; simpl; trivial; intros. now rewrite IHt1, IHt2.
Qed.

Lemma mapi_ok {A B} (f:N->A->B) (t:tree A) :
 Ok t -> Ok (mapi f t).
Proof.
 revert f. induction t; simpl; trivial; intros f OK.
 repeat split. now apply IHt1. now apply IHt2.
 now rewrite !mapi_fullsize.
Qed.

Lemma mapi_size {A B} (f:N->A->B) (t:tree A) :
 Ok t -> size (mapi f t) = size t.
Proof.
 intros. rewrite !size_spec; trivial. apply mapi_fullsize. now apply mapi_ok.
Qed.

Lemma mapi_spec {A B} (f:N->A->B) (t:tree A) n :
 Ok t -> n < size t -> get (mapi f t) n = f n (get t n).
Proof.
 revert f n. induction t; simpl; intros f n OK LT.
 - now replace n with 0 by lia.
 - destruct (N.even n) eqn:E.
   + assert (n = N.double (N.div2 n)).
     { rewrite (N.div2_odd n) at 1. rewrite <- N.negb_even, E.
       simpl N.b2n. lia. }
     rewrite IHt1; try easy.
     * f_equal. lia.
     * clear IHt1 IHt2. rewrite size_spec in * by easy. destruct p; lia.
   + assert (n = N.double (N.div2 n) + 1).
     { rewrite (N.div2_odd n) at 1. rewrite <- N.negb_even, E.
       simpl N.b2n. lia. }
     rewrite IHt2; try easy.
     * f_equal. lia.
     * clear IHt1 IHt2. rewrite size_spec in * by easy. destruct p; lia.
Qed.

Lemma mapi_spec' {A B} (f:N->A->B) (t:tree A) :
 Ok t ->
 to_list (mapi f t) =
 List.map (fun n => f (N.of_nat n) (get t (N.of_nat n)))
          (seq 0 (N.to_nat (size t))).
Proof.
 intros OK.
 rewrite to_list_spec' by now apply mapi_ok.
 rewrite mapi_size by easy. apply map_ext_in.
 intros n. rewrite in_seq. intros Hn. apply mapi_spec; trivial. lia.
Qed.

(** Spec of reduce and map_reduce *)

Definition Commutative {A} (op:A->A->A) :=
  forall a b, op a b = op b a.
Definition Associative {A} (op:A->A->A) :=
  forall a b c, op a (op b c) = op (op a b) c.

Local Notation foldl op a l := (fold_left op l a).

Lemma foldl_op_init {A} (op:A->A->A) a b l :
  Associative op ->
  op a (foldl op b l) = foldl op (op a b) l.
Proof.
 intros. revert a b. induction l as [|c l IH]; simpl; intros; trivial.
 now rewrite <- !IH.
Qed.

Lemma foldl_assoc {A} (op:A->A->A) a a' l l' :
  Associative op ->
  op (foldl op a l) (foldl op a' l') = foldl op a (l ++ a'::l').
Proof.
 revert a. induction l; simpl; intros. now apply foldl_op_init. now apply IHl.
Qed.

Lemma foldl_permut {A} (op:A->A->A) a l l' :
  Commutative op -> Associative op -> Permutation l l' ->
  foldl op a l = foldl op a l'.
Proof.
 intros CO AS P. revert a. induction P; simpl; intros; trivial.
 - now rewrite <- !AS, (CO y x).
 - now rewrite IHP1.
Qed.

Lemma reduce_spec {A} (op:A->A->A) (t:tree A) :
  Commutative op -> Associative op ->
  match to_list t with
  | [] => False
  | a::l => reduce op t = foldl op a l
  end.
Proof.
 intros CO AS.
 induction t; simpl; trivial.
 destruct (to_list t1) as [|x1 l1] eqn:E1; try easy.
 destruct (to_list t2) as [|x2 l2] eqn:E2; try easy.
 simpl. rewrite IHt1, IHt2. clear p t1 t2 E1 IHt1 E2 IHt2.
 rewrite (foldl_permut op _ (mix l1 l2) (l1++l2)); trivial.
 2:apply mix_permut.
 rewrite foldl_assoc by easy.
 rewrite (foldl_permut op _ _ (x2::(l1++l2))); try easy.
 symmetry. now apply Permutation_cons_app.
Qed.

Lemma map_reduce_spec {A B} (f:A->B) (op:B->B->B) (t:tree A) :
  map_reduce f op t = reduce op (map f t).
Proof.
 induction t; simpl; now rewrite ?IHt1, ?IHt2.
Qed.
