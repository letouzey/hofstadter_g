(** * DeltaList : lists of natural numbers with constrained differences *)

From Coq Require Export Arith Lia List Bool.
Require Import MoreList.
Import ListNotations.
Set Implicit Arguments.

Ltac autoh := lia || auto with hof datatypes.
Ltac eautoh := lia || eauto with hof datatypes.
Ltac intuith := intuition autoh.

(** * Increasing lists *)

(** [Delta p l] means that consecutives values in the list [l]
    have differences of at least [p]. *)

Inductive Delta (p:nat) : list nat -> Prop :=
  | Dnil : Delta p []
  | Done n : Delta p [n]
  | Dcons n m l : m+p <= n -> Delta p (n::l) -> Delta p (m::n::l).
#[global] Hint Constructors Delta : hof.

(** In particular:
    - [Delta 0 l] means that [l] is increasing
    - [Delta 1 l] means that [l] is stricly increasing
    - [Delta 2 l] implies in addition that no consecutive
      numbers can occur in [l].
*)

Lemma Delta_alt p x l :
 Delta p (x::l) <-> Delta p l /\ (forall y, In y l -> x+p <= y).
Proof.
 split.
 - revert x. induction l as [|a l IH].
   + intros x _. split. constructor. inversion 1.
   + intros x. inversion 1; subst. split; trivial.
     intros y [Hy|Hy]. now subst.
     apply (IH a) in Hy; autoh.
 - intros (H,H').
   destruct l; constructor; trivial. apply H'. now left.
Qed.

Lemma Delta_inv p x l : Delta p (x::l) -> Delta p l.
Proof.
 now rewrite Delta_alt.
Qed.

Lemma Delta_inv2 p x y l :
 Delta p (x::y::l) -> x+p <= y /\ Delta p (y::l).
Proof.
 inversion 1; subst; auto.
Qed.

Lemma Delta_more l p p' : p <= p' -> Delta p' l -> Delta p l.
Proof.
 induction 2; constructor; autoh.
Qed.

Lemma Delta_S n l : Delta (S n) l -> Delta n l.
Proof.
 apply Delta_more; auto.
Qed.

Lemma Delta_nz p k l : 0<k -> Delta p (k::l) -> ~In 0 (k::l).
Proof.
 intros H H' [X|X]. autoh.
 apply Delta_alt in H'. apply H' in X. autoh.
Qed.
#[global] Hint Resolve Delta_S Delta_inv Delta_nz : hof.

Lemma Delta_nz' p k l : 0<p -> Delta p (k::l) -> ~In 0 l.
Proof.
 intros H H' X.
 apply Delta_alt in H'. apply H' in X. autoh.
Qed.

Lemma Delta_low_hd p k k' l :
 k'<=k -> Delta p (k::l) -> Delta p (k'::l).
Proof.
 intros Hk. rewrite !Delta_alt. intros (H,H').
 split; trivial. intros y Hy. apply H' in Hy. autoh.
Qed.

Lemma Delta_S_cons k x l :
  Delta (S k) (x::l) -> Delta k (S x :: l).
Proof.
  intros D. apply Delta_alt in D. destruct D as (D,D').
  apply Delta_alt; split.
  apply Delta_more with (S k); auto.
  intros y Hy. apply D' in Hy. autoh.
Qed.
#[global] Hint Resolve Delta_S_cons : hof.

Lemma Delta_map p p' f l :
  (forall x y, x+p <= y -> f x + p' <= f y) ->
  Delta p l -> Delta p' (map f l).
Proof.
 induction 2; constructor; auto.
Qed.

Lemma Delta_pred p l :
 ~In 0 l -> Delta p l -> Delta p (map pred l).
Proof.
 induction 2; simpl in *; constructor; autoh.
Qed.

Lemma Delta_seq n k : Delta 1 (seq n k).
Proof.
 revert n. induction k.
 - constructor.
 - intros. simpl. apply Delta_alt. split; auto.
   intros y Hy. rewrite in_seq in Hy. autoh.
Qed.

Lemma Delta_app p x l l' :
  Delta p l -> Delta p (x::l') ->
  (forall y, In y l -> y <= x) -> Delta p (l++l').
Proof.
 induction l.
 - intros _ Hl' H. simpl. eautoh.
 - intros Hl Hl' H. simpl. apply Delta_alt. split.
   + eautoh.
   + intros y Hy. rewrite in_app_iff in Hy.
     destruct Hy as [Hy|Hy].
     * rewrite Delta_alt in Hl. now apply Hl.
     * assert (a <= x) by (apply H; now left).
       apply Delta_alt in Hl'. apply Hl' in Hy. autoh.
Qed.

(* Another approach, more suitable for inversion: *)

Lemma Delta_app_iff p l l':
  Delta p (l++l') <->
  Delta p l /\ Delta p l' /\
  (forall x x' : nat, In x l -> In x' l' -> x + p <= x').
Proof.
 induction l; simpl.
 - intuith.
 - rewrite !Delta_alt, IHl. split.
   + intros ((D & D' & H) & H'). repeat split; auto.
     * intuith.
     * intros x x' [<-|IN] IN'; auto.
       apply H'. rewrite in_app_iff; now right.
   + intros ((D,H) & D' & H'). repeat split; auto.
     intros y. rewrite in_app_iff. intros [IN|IN']; auto.
Qed.

Lemma Delta_app_inv p l l' :
 Delta p (l++l') ->
 Delta p l /\ Delta p l' /\
 forall x x', In x l -> In x' l' -> x+p <= x'.
Proof.
 apply Delta_app_iff.
Qed.

Lemma Delta2_apart l x :
 Delta 2 l -> In x l -> In (S x) l -> False.
Proof.
 induction l as [|a l IH].
 - inversion 2.
 - rewrite Delta_alt. intros (D,D').
   simpl. intros [E|H] [E'|H']; autoh.
   + apply D' in H'. autoh.
   + apply D' in H. autoh.
Qed.

Lemma Delta_le k l x y : Delta k (x::l) -> In y l -> x+k <= y.
Proof.
 rewrite Delta_alt. intros (_,H). apply H.
Qed.

Lemma Delta_last_le p l x y : Delta p (l++[x]) -> In y (l++[x]) -> y <= x.
Proof.
 rewrite Delta_app_iff. intros (_ & _ & D).
 rewrite in_app_iff. intros [IN|[<-|[ ]]]; auto.
 specialize (D y x IN (or_introl eq_refl)). autoh.
Qed.

Lemma Delta_up_last p l a b : Delta p (l++[a]) -> a<=b -> Delta p (l++[b]).
Proof.
 rewrite !Delta_app_iff. intros (D1 & D2 & D3) LE. repeat split; autoh.
 intros x x' IN [<-|[ ]]. specialize (D3 x a IN). simpl in D3. autoh.
Qed.

(** * Decreasing lists *)

(** [DeltaRev p l] is [Delta p (rev l)] :
    it considers differences in the reversed order,
    leading to decreasing lists *)

Inductive DeltaRev (p:nat) : list nat -> Prop :=
  | DRnil : DeltaRev p []
  | DRone n : DeltaRev p [n]
  | DRcons n m l : n+p <= m -> DeltaRev p (n::l) -> DeltaRev p (m::n::l).
#[global] Hint Constructors DeltaRev : hof.

Lemma DeltaRev_alt p x l :
 DeltaRev p (x::l) <-> DeltaRev p l /\ (forall y, In y l -> y+p <= x).
Proof.
 split.
 - revert x. induction l as [|a l IH].
   + intros x _. split. constructor. inversion 1.
   + intros x. inversion 1; subst. split; trivial.
     intros y [Hy|Hy]. now subst.
     apply (IH a) in Hy; autoh.
 - intros (H,H').
   destruct l; constructor; trivial. apply H'. now left.
Qed.

Lemma DeltaRev_app p x l l' :
  DeltaRev p l -> DeltaRev p (x::l') ->
  (forall y, In y l -> x <= y) -> DeltaRev p (l++l').
Proof.
 induction l.
 - intros _ Hl' H. simpl. now rewrite DeltaRev_alt in Hl'.
 - intros Hl Hl' H. simpl. apply DeltaRev_alt. split.
   + apply IHl; auto.
     * now rewrite DeltaRev_alt in Hl.
     * intros y Hy. apply H. now right.
   + intros y Hy. rewrite in_app_iff in Hy.
     destruct Hy as [Hy|Hy].
     * rewrite DeltaRev_alt in Hl. now apply Hl.
     * assert (x <= a) by (apply H; now left).
       apply DeltaRev_alt in Hl'. apply Hl' in Hy. autoh.
Qed.

Lemma DeltaRev_app_inv p l l' :
 DeltaRev p (l++l') ->
 DeltaRev p l /\ DeltaRev p l' /\
 forall x x', In x l -> In x' l' -> x'+p <= x.
Proof.
 induction l; simpl.
 - split. constructor. intuith.
 - rewrite !DeltaRev_alt. intuith.
   subst. apply H1. rewrite in_app_iff. now right.
Qed.

Lemma Delta_rev p l : Delta p (rev l) <-> DeltaRev p l.
Proof.
 split.
 - rewrite <- (rev_involutive l) at 2.
   set (l':=rev l); clearbody l'. clear l.
   induction 1.
   + constructor.
   + constructor.
   + simpl in *.
     apply DeltaRev_app with n; autoh.
     intros y Hy. apply DeltaRev_app_inv in IHDelta.
     destruct IHDelta as (_ & _ & IH).
     specialize (IH y n).
     rewrite in_app_iff in Hy. simpl in *. intuith.
 - induction 1.
   + constructor.
   + constructor.
   + simpl in *.
     apply Delta_app with n; autoh.
     intros y Hy. apply Delta_app_inv in IHDeltaRev.
     destruct IHDeltaRev as (_ & _ & IH).
     specialize (IH y n).
     rewrite in_app_iff in Hy. simpl in *. intuith.
Qed.

Lemma DeltaRev_rev p l : DeltaRev p (rev l) <-> Delta p l.
Proof.
 now rewrite <- Delta_rev, rev_involutive.
Qed.

Lemma Delta_map_decr p k l :
  (forall n, List.In n l -> k <= n)%nat ->
  Delta p l -> Delta p (List.map (decr k) l).
Proof.
 induction l as [|a l IH]; simpl; auto.
 - intros H. inversion 1; subst; constructor.
   + unfold decr. specialize (H a). lia.
   + apply IH; auto.
Qed.

Definition Below l x := forall y, In y l -> y < x.

(** All lists l such that [Delta (S d) l] and [Below l b] *)

Definition zeroshift k l := 0::map (Nat.add k) l.

Fixpoint enum_delta_below d b :=
  match b with
  | 0 => [[]]
  | S b =>
    map (zeroshift (S d)) (enum_delta_below d (b - d))
    ++ map (map S) (enum_delta_below d b)
  end.

Lemma zeroshift_delta k l : Delta k (zeroshift k l) <-> Delta k l.
Proof.
 unfold zeroshift; split; intros D.
 - replace l with (map (decr k) (map (Nat.add k) l)).
   2:{ rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext.
       unfold decr. lia. }
   apply Delta_map_decr. 2:eapply Delta_inv; eauto.
   intros x. rewrite in_map_iff. intros (y & <- & IN). lia.
 - rewrite Delta_alt; split.
   + eapply Delta_map; eauto; lia.
   + intros x. rewrite in_map_iff. intros (y & <- & IN). lia.
Qed.

Lemma zeroshift_below d b l :
 Below (zeroshift (S d) l) (S b) <-> Below l (b-d).
Proof.
 unfold zeroshift; split; intros B x IN.
 - assert (S d + x < S b); try lia.
   { apply B. simpl; right. rewrite in_map_iff. now exists x. }
 - simpl in IN. rewrite in_map_iff in IN.
   destruct IN as [<-|(y & <- & IN)]; try lia. specialize (B y IN). lia.
Qed.

Lemma enum_delta_below_ok d b l :
 In l (enum_delta_below d b) <-> Delta (S d) l /\ Below l b.
Proof.
 revert l.
 induction b as [[|b] IH] using lt_wf_ind; cbn; intros l; split.
 - intros [<-|[]]. split. constructor. now red.
 - intros (D,B). destruct l as [|n l]; auto.
   assert (n < 0)%nat by (apply B; now left). lia.
 - rewrite in_app_iff, !in_map_iff.
   intros [(u & <- & IN)|(u & <- & IN)]; rewrite IH in IN by lia; clear IH.
   + now rewrite zeroshift_delta, zeroshift_below.
   + destruct IN as (D,B). split.
     * eapply Delta_map; eauto; lia.
     * intros x. rewrite in_map_iff. intros (y & <- & IN). apply B in IN. lia.
 - intros (D,B). rewrite in_app_iff, !in_map_iff.
   destruct l as [|[|x] l].
   + right. exists []. split; auto. rewrite IH by lia; split; auto. now red.
   + left. assert (D' := fun x => @Delta_le (S d) l 0 x D).
     replace (0 :: l) with (zeroshift (S d) (map (decr (S d)) l)) in *.
     rewrite zeroshift_delta in D.
     rewrite zeroshift_below in B.
     2:{ unfold zeroshift. f_equal. rewrite map_map.
         rewrite <- (map_id l) at 2. apply map_ext_in.
         intros x Hx. unfold decr. specialize (D' x Hx). lia. }
     eexists; split; [ reflexivity | ]. rewrite IH by lia. easy.
   + right. assert (D' := fun y => @Delta_le (S d) l (S x) y D).
     replace (S x :: l) with (map S (x :: map (decr 1) l)).
     2:{ unfold decr. simpl. f_equal. rewrite map_map.
         rewrite <- (map_id l) at 2. apply map_ext_in.
         intros y Hy. specialize (D' y Hy). lia. }
     eexists; split; [ reflexivity | ]. rewrite IH by lia; split.
     { rewrite Delta_alt. split.
       - apply Delta_map_decr. intros y Hy. specialize (D' y Hy). lia.
         eapply Delta_inv; eauto.
       - intro y. rewrite in_map_iff. intros (z & <- & IN).
         specialize (D' z IN). unfold decr. lia. }
     { intros y. simpl. rewrite in_map_iff. intros [<-|(z & <- & IN)].
       - specialize (B (S x)). simpl in B. lia.
       - unfold decr. specialize (B z (or_intror IN)). specialize (D' z IN).
         lia. }
Qed.

Lemma enum_delta_below_ok0 d b l :
 Delta (S d) (0::l) /\ Below (0::l) (S b) <->
 In (0::l) (map (zeroshift (S d)) (enum_delta_below d (b-d))).
Proof.
 rewrite in_map_iff. split.
 - intros (D,B).
   assert (D' := fun x => @Delta_le (S d) l 0 x D).
   replace (0 :: l) with (zeroshift (S d) (map (decr (S d)) l)) in *.
   rewrite zeroshift_delta in D.
   rewrite zeroshift_below in B.
   2:{ unfold zeroshift. f_equal. rewrite map_map.
       rewrite <- (map_id l) at 2. apply map_ext_in.
       intros x Hx. unfold decr. specialize (D' x Hx). lia. }
   eexists; split; [ reflexivity | ]. rewrite enum_delta_below_ok by lia.
   easy.
 - intros (u & <- & IN). rewrite enum_delta_below_ok in IN by lia.
   split. now apply zeroshift_delta. now apply zeroshift_below.
Qed.

Lemma insert_delta x l a :
 Delta 2 (Nat.pred a::l) -> ~In x l -> a < x -> Delta 1 (a::insert x l).
Proof.
 revert a.
 induction l as [|b l IH]; simpl.
 - constructor. lia. constructor.
 - intro a. case Nat.leb_spec; intro.
   + inversion 1; subst. intros.
     constructor. lia. constructor; autoh.
   + inversion 1; subst. intros.
     constructor. lia. apply IH; auto.
     apply Delta_low_hd with b. lia. auto.
Qed.
