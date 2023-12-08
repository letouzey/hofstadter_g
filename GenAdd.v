
Require Import MoreFun MoreList DeltaList FunG GenFib GenG.
Import ListNotations.
Set Implicit Arguments.

(** Study of quasi-additivity for [f k n] function defined in [GenG]:
    [f k (p+n)] is close to [f k p + f k n].
    Said otherwise, for some fixed p, few values are reached by
    [f k (p+n)-f k n] when n varies.
    For this study, we'll turn a strict k-decomposition of n into
    a lax decomp of (p+n).
*)

(** First, some proofs for [p<=4] that hold for any [k] *)

Lemma fk_add_1 k n : f k n <= f k (1+n) <= 1 + f k n.
Proof.
 destruct (f_step k n); simpl; lia.
Qed.

Lemma fk_add_2 k n : 1 + f k n <= f k (2+n) <= 2 + f k n.
Proof.
 split.
 - generalize (f_SS k n). simpl. lia.
 - apply f_le_add.
Qed.

Lemma fk_add_3 k n : 1 + f k n <= f k (3+n) <= 3 + f k n.
Proof.
 split.
 - transitivity (f k (2+n)). apply fk_add_2. apply f_mono. lia.
 - apply f_le_add.
Qed.

Lemma fk_add_4 k n : 2 + f k n <= f k (4+n) <= 4 + f k n.
Proof.
 split.
 - transitivity (1 + f k (2 + n)).
   + generalize (fk_add_2 k n). lia.
   + apply (fk_add_2 k (2+n)).
 - apply f_le_add.
Qed.

(** Cut a decomposition in two, all the left being < p *)

Fixpoint cut_lt_ge p l :=
 match l with
 | [] => ([],[])
 | a::l' => if p <=? a then ([],l)
            else let '(l1,l2) := cut_lt_ge p l' in (a::l1,l2)
 end.

Lemma cut_app p l :
  let '(l1,l2) := cut_lt_ge p l in l1++l2 = l.
Proof.
 induction l; simpl; auto.
 case Nat.leb_spec; simpl; auto. intros LE.
 destruct cut_lt_ge. simpl. f_equal. auto.
Qed.

Lemma cut_fst p l :
  Below (fst (cut_lt_ge p l)) p.
Proof.
 induction l as [|a l IH]; simpl.
 - unfold Below; simpl. intuition.
 - case Nat.leb_spec.
   + unfold Below; simpl; intuition.
   + destruct cut_lt_ge. unfold Below in *; simpl in *. intuition.
     subst; auto.
Qed.

Lemma cut_snd p l a l':
  snd (cut_lt_ge p l) = a::l' -> p <= a.
Proof.
 induction l as [|b l IH]; simpl.
 - inversion 1.
 - case Nat.leb_spec.
   + simpl. intros LT [= -> ->]; auto.
   + intros _. destruct cut_lt_ge. simpl in *; auto.
Qed.

Lemma cut_snd' k p l :
  Delta k l ->
  forall x, In x (snd (cut_lt_ge p l)) -> p <= x.
Proof.
 generalize (cut_app p l) (cut_snd p l).
 destruct (cut_lt_ge p l) as (l1,l2). simpl.
 intros <-. rewrite Delta_app_iff. intros H (_ & H' & _).
 destruct l2 as [|a l2]; simpl.
 - inversion 1.
 - specialize (H a l2 eq_refl).
   intros x [<-|IN]; auto.
   transitivity (a+k). lia. eapply Delta_le; eauto.
Qed.

(* To add p to a strict k-decomposition (while possibly relaxing it),
   no need to dig deeper than value [invA_up k p + 3*k-1].
   Note : tighter upper bounds than that could probably be found,
   but seem harder to prove *)

Definition bound_idx k p := invA_up k p + 3*k-1.

Definition low_high k p l := cut_lt_ge (bound_idx k p) l.

Definition addlow k p low :=
 match rev low with
 | [] => decomp k p
 | a::rlow' =>
   let u:=invA_up k p +k-1 in
   if u <? a then
     (* a is big enough : putting (S a) instead of a in the decomposition
        adds at least p (while remaining lax). *)
     decompminus k (rev rlow'++[S a]) (A k (a-k) - p)
   else
     (* a is low enough : we can add an extra term in the decomposition *)
     decompminus k (low ++[u+k]) (A k (u+k) - p)
 end.

Lemma addlow_sum k p l : k<>0 ->
  let low := fst (low_high k p l) in
  sumA k (addlow k p low) = p + sumA k low.
Proof.
 intros Hk.
 destruct (low_high k p l) as (low,high) eqn:E. simpl.
 unfold addlow.
 destruct (rev low) as [|a rlow'] eqn:E'.
 - apply rev_switch in E'. rewrite decomp_sum, E'. simpl; auto.
 - apply rev_switch in E'. simpl in E'.
   set (u := invA_up k p + k - 1).
   case Nat.ltb_spec; intros.
   + rewrite decompminus_sum, E'.
     rewrite !sumA_app.
     cbn - [A]. rewrite A_S.
     assert (p <= A k (a-k)); try lia.
     { etransitivity. apply (invA_up_spec k). apply A_mono. lia. }
   + rewrite decompminus_sum. rewrite sumA_app. simpl.
     assert (p <= A k (u+k)); try lia.
     { etransitivity. apply (invA_up_spec k). apply A_mono. lia. }
Qed.

Definition addlow_delta k p l : k<>0 -> Delta (S k) l ->
  let (low,high) := low_high k p l in
  Delta k (addlow k p low ++ high).
Proof.
 intros Hk D.
 set (u := bound_idx k p).
 generalize (cut_app u l) (cut_fst u l) (cut_snd' u D).
 change (cut_lt_ge _ _) with (low_high k p l).
 destruct (low_high k p l) as (low,high). simpl.
 intros E Hlow Hhigh.
 unfold addlow.
 destruct (rev low) as [|a rlow'] eqn:E'.
 - apply rev_switch in E'. subst low. simpl in E. subst high.
   apply Delta_app_iff. repeat split; auto using decomp_delta with hof.
   intros x x' IN IN'. apply Hhigh in IN'.
   transitivity u; auto with arith.
   assert (A k x <= p).
   { rewrite <- (decomp_sum k p). apply sumA_in_le; auto. }
   assert (x <= invA_up k p).
   { apply (@A_le_inv k).
     transitivity p; auto. apply invA_up_spec. }
   unfold bound_idx in u. lia.
 - apply rev_switch in E'. simpl in E'.
   set (v := invA_up k p + k-1).
   subst l.
   rewrite Delta_app_iff in D. destruct D as (D1 & D2 & D3).
   case Nat.ltb_spec; intros.
   + apply decompminus_app_delta.
     rewrite Delta_app_iff. repeat split; autoh.
     eapply Delta_up_last with a; auto. rewrite <- E'; autoh.
     intros x x' IN IN'.
     rewrite in_app_iff in IN. destruct IN as [IN|[<-|[ ]]].
     * specialize (D3 x x').
       rewrite E', in_app_iff in D3.
       specialize (D3 (or_introl IN) IN'). lia.
     * specialize (D3 a x').
       rewrite E', in_app_iff in D3.
       specialize (D3 (or_intror (or_introl eq_refl)) IN'). lia.
   + apply decompminus_app_delta.
     rewrite <- app_assoc. apply Delta_app_iff; repeat split; autoh.
     * rewrite Delta_app_iff; repeat split; autoh.
       intros x x' [<-|[ ]] IN'. specialize (Hhigh x' IN').
       unfold bound_idx in u. lia.
     * intros x x'. rewrite in_app_iff.
       intros IN [[<-|[ ]]|IN'].
       { rewrite E' in *. assert (LE := Delta_last_le _ _ _ D1 IN). lia. }
       { specialize (D3 x x' IN IN'). lia. }
Qed.

(* So, all values taken by [f k (p+n)-f k n] when n varies in [nat] are
   values that are already encountered when n varies in just
   [0..add_bound k p[. *)

Definition add_bound k p := A k (bound_idx k p).

Definition reduced k p n := sumA k (fst (low_high k p (decomp k n))).

Lemma reduced_lt k p n :
  reduced k p n < add_bound k p.
Proof.
 unfold reduced, add_bound.
 assert (D := decomp_delta k n).
 set (l := decomp k n) in *. clearbody l.
 assert (E := cut_app (bound_idx k p) l).
 assert (B := cut_fst (bound_idx k p) l).
 change (cut_lt_ge _ _) with (low_high k p l) in E,B.
 destruct (low_high k p l) as (low,high) eqn:E'. simpl in *.
 rewrite <-E in D.
 rewrite Delta_app_iff in D. destruct D as (D1 & D2 & D3).
 apply sumA_below; auto.
Qed.

Lemma additivity_reduced k p : k<>0 ->
 forall n,
   let m := reduced k p n in
   f k (p+n) - f k n = f k (p+m) - f k m.
Proof.
 intros Hk n.
 assert (D := decomp_delta k n).
 unfold reduced; simpl.
 rewrite <- (decomp_sum k n) at 1 2.
 set (l := decomp k n) in *. clearbody l.
 assert (E := cut_app (bound_idx k p) l).
 change (cut_lt_ge _ _) with (low_high k p l) in E.
 assert (E' := @addlow_sum k p l Hk).
 assert (D' := @addlow_delta k p l Hk D).
 destruct (low_high k p l) as (low,high). simpl in *.
 subst l.
 rewrite sumA_app at 1.
 rewrite Nat.add_assoc, <- E', <- !sumA_app.
 rewrite !f_sumA_lax; autoh.
 - rewrite !map_app, !sumA_app. lia.
 - rewrite Delta_app_iff in D. intuition.
 - rewrite Delta_app_iff in D'. intuition.
Qed.

Lemma additivity_bounded k p : k<>0 ->
 forall n, exists m,
   m < add_bound k p /\
   f k (p+n) - f k n = f k (p+m) - f k m.
Proof.
 intros Hk n. exists (reduced k p n). split.
 - apply reduced_lt.
 - now apply additivity_reduced.
Qed.

(** We could hence prove bounds for [f k (p+n)-f k p] by computation. *)

Fixpoint map2 {A B C}(f:A->B->C) l1 l2 :=
  match l1,l2 with
  | x1::l1', x2::l2' => f x1 x2 :: map2 f l1' l2'
  | _, _ => []
  end.

Definition all_diffs k p bound :=
  let stk := ftabulate k (p + (bound-1)) in
  map2 Nat.sub stk (npop p stk).

Lemma all_diffs_spec k p bound :
  all_diffs k p bound =
  map (fun x => f k (p+x)-f k x) (countdown (bound - 1)).
Proof.
 unfold all_diffs.
 rewrite ftabulate_spec.
 rewrite npop_map.
 replace p with (p+(bound-1)-(bound-1)) at 2 by lia.
 rewrite npop_countdown by lia.
 induction (bound-1).
 - simpl. destruct p; simpl; auto. f_equal. now destruct countdown.
 - rewrite Nat.add_succ_r. simpl. f_equal; auto.
Qed.

Definition calc_additivity k p bound := extrems (all_diffs k p bound).

Lemma decide_additivity k p a b : k<>0 ->
 calc_additivity k p (add_bound k p) = (a,b) ->
 forall n, a + f k n <= f k (p+n) <= b + f k n.
Proof.
 intros Hk E n.
 assert (H : f k n <= f k (p+n)) by (apply f_mono; lia).
 assert (a <= f k (p+n) - f k n <= b); try lia.
 { destruct (@additivity_bounded k p Hk n) as (m & Hm & ->).
   clear n H.
   unfold calc_additivity in E.
   revert E. apply extrems_spec.
   rewrite all_diffs_spec.
   set (delta := fun x => _). apply (in_map delta). clear delta.
   apply countdown_in. lia. }
Qed.

(** For exemple, let's do some proofs by computations for f 3.
    Note : f 2 (known as H) is considered afterwards, with an improved
    bound.
*)

Lemma f3_add_5 n : 3 + f 3 n <= f 3 (5+n) <= 4 + f 3 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f3_add_6 n : 3 + f 3 n <= f 3 (6+n) <= 5 + f 3 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f3_add_7 n : 4 + f 3 n <= f 3 (7+n) <= 6 + f 3 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f3_add_8 n : 5 + f 3 n <= f 3 (8+n) <= 7 + f 3 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f3_add_9 n : 6 + f 3 n <= f 3 (9+n) <= 8 + f 3 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f3_add_10 n : 6 + f 3 n <= f 3 (10+n) <= 8 + f 3 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f3_add_33 n : 23 + f 3 n <= f 3 (33+n) <= 25 + f 3 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

(* TODO general bounds for f3(n+m)-f3(n)-f3(m) ??
   Same for any fk ??
*)

(** Particular case of function H, i.e. k=2 *)

Definition h := f 2.

Notation A2 := (A 2).

(** First, for H the previous results could be slightly improved,
    with a bound of [invA_up 2 p + 3] instead of
    [bound_idx 2 p = invA_up 2 p + 3*2-1] *)

Lemma twice_A2_le n : 2 * A2 n <= A2 (2+n).
Proof.
 destruct n; simpl; auto.
 replace (n-0) with n by lia.
 generalize (@A_mono 2 (n-2) (n-1)). lia.
Qed.

Definition bound_idx_k2 p := invA_up 2 p + 3.

Definition low_high_k2 p l := cut_lt_ge (bound_idx_k2 p) l.

Definition addlow_k2 p low :=
 match rev low with
 | [] => decomp 2 p
 | a::rlow' =>
   let u:=invA_up 2 p in
   if a <? u then
     decompminus 2 (low ++[u+1]) (A2 (u+1) - p)
   else
     decompminus 2 (rev rlow'++[a-1;1+a]) (A2 (a+2) - A2 a - p)
 end.

Lemma addlow_sum_k2 p l :
  let low := fst (low_high_k2 p l) in
  sumA 2 (addlow_k2 p low) = p + sumA 2 low.
Proof.
 destruct (low_high_k2 p l) as (low,high) eqn:E. simpl.
 unfold addlow_k2.
 destruct (rev low) as [|a rlow'] eqn:E'.
 - apply rev_switch in E'. rewrite decomp_sum, E'. simpl; auto.
 - apply rev_switch in E'. simpl in E'.
   remember (invA_up 2 p) as u.
   case Nat.ltb_spec; intros.
   + rewrite decompminus_sum. rewrite sumA_app. simpl.
     assert (p <= A2 (u+1)); try lia.
     { etransitivity. apply (invA_up_spec 2). apply A_mono. lia. }
   + rewrite decompminus_sum, E'. rewrite !sumA_app.
     cbn - [A]. rewrite Nat.add_0_r.
     replace (A2 _ + A2 _) with (A2 (a+2)).
     2:{ rewrite (@A_sum 2 (a+2)), Nat.add_comm by lia.
         f_equal; f_equal; lia. }
     assert (p + A2 a <= A2 (a+2)); try lia.
     { generalize (invA_up_spec 2 p). rewrite <- Hequ.
       generalize (@A_mono 2 u a) (twice_A2_le a).
       rewrite Nat.add_comm. lia. }
Qed.

Definition addlow_delta_k2 p l : Delta 3 l ->
  let (low,high) := low_high_k2 p l in
  Delta 2 (addlow_k2 p low ++ high).
Proof.
 intros D.
 set (u := bound_idx_k2 p).
 generalize (cut_app u l) (cut_fst u l) (cut_snd' u D).
 change (cut_lt_ge _ _) with (low_high_k2 p l).
 destruct (low_high_k2 p l) as (low,high). simpl.
 intros E Hlow Hhigh.
 unfold addlow_k2.
 destruct (rev low) as [|a rlow'] eqn:E'.
 - apply rev_switch in E'. subst low. simpl in E. subst high.
   apply Delta_app_iff. repeat split; auto using decomp_delta with hof.
   intros x x' IN IN'. apply Hhigh in IN'.
   transitivity u; auto with arith.
   assert (A 2 x <= p).
   { rewrite <- (decomp_sum 2 p). apply sumA_in_le; auto. }
   assert (x <= invA_up 2 p).
   { apply (@A_le_inv 2).
     transitivity p; auto. apply invA_up_spec. }
   unfold bound_idx_k2 in u. lia.
 - apply rev_switch in E'. simpl in E'.
   set (v := invA_up 2 p).
   subst l.
   rewrite Delta_app_iff in D. destruct D as (D1 & D2 & D3).
   case Nat.ltb_spec; intros.
   + apply decompminus_app_delta.
     rewrite Delta_app_iff. repeat split; autoh.
     * rewrite Delta_app_iff; repeat split; autoh.
       intros x x' IN [<-|[ ]].
       rewrite E' in *. eapply Delta_last_le in IN; eauto. lia.
     * intros x x'. rewrite in_app_iff. intros [IN|[<-|[ ]]] IN'.
       { specialize (D3 x x' IN IN'). lia. }
       { specialize (Hhigh x' IN'). unfold bound_idx_k2 in u. lia. }
   + apply decompminus_app_delta.
     rewrite Delta_app_iff. repeat split; autoh.
     * rewrite E' in D1. rewrite Delta_app_iff in D1.
       destruct D1 as (D11 & D12 & D13).
       rewrite Delta_app_iff. repeat split; autoh.
       { constructor; autoh. unfold invA_up in v. lia. }
       { intros x x' IN [<-|[<-|[ ]]].
         - specialize (D13 x a IN (or_introl eq_refl)). lia.
         - specialize (D13 x a IN (or_introl eq_refl)). lia. }
     * intros x x'. rewrite in_app_iff.
       intros [IN|[<-|[<-|[ ]]]] IN'.
       { rewrite E' in D3. specialize (D3 x x').
         rewrite in_app_iff in D3. specialize (D3 (or_introl IN) IN'). lia. }
       { rewrite E' in D3. specialize (D3 a x').
         rewrite in_app_iff in D3.
         specialize (D3 (or_intror (or_introl eq_refl)) IN'). lia. }
       { rewrite E' in D3. specialize (D3 a x').
         rewrite in_app_iff in D3.
         specialize (D3 (or_intror (or_introl eq_refl)) IN'). lia. }
Qed.

Definition add_bound_k2 p := A2 (invA_up 2 p + 3).

Definition reduced_k2 p n := sumA 2 (fst (low_high_k2 p (decomp 2 n))).

Lemma reduced_lt_k2 p n :
  reduced_k2 p n < add_bound_k2 p.
Proof.
 unfold reduced_k2, add_bound_k2. fold (bound_idx_k2 p).
 assert (D := decomp_delta 2 n).
 set (l := decomp 2 n) in *. clearbody l.
 assert (E := cut_app (bound_idx_k2 p) l).
 assert (B := cut_fst (bound_idx_k2 p) l).
 change (cut_lt_ge _ _) with (low_high_k2 p l) in E,B.
 destruct (low_high_k2 p l) as (low,high) eqn:E'. simpl fst in *.
 apply sumA_below; auto.
 rewrite <-E, Delta_app_iff in D. intuition.
Qed.

Lemma additivity_reduced_k2 p n :
  let m := reduced_k2 p n in
  h (p+n) - h n = h (p+m) - h m.
Proof.
 assert (D := decomp_delta 2 n).
 unfold reduced_k2; simpl.
 rewrite <- (decomp_sum 2 n) at 1 2.
 set (l := decomp 2 n) in *. clearbody l.
 assert (E := cut_app (bound_idx_k2 p) l).
 change (cut_lt_ge _ _) with (low_high_k2 p l) in E.
 assert (E' := @addlow_sum_k2 p l).
 assert (D' := @addlow_delta_k2 p l D).
 destruct (low_high_k2 p l) as (low,high). simpl in *.
 subst l.
 rewrite sumA_app at 1.
 rewrite Nat.add_assoc, <- E', <- !sumA_app.
 unfold h. rewrite !f_sumA_lax; autoh.
 - rewrite !map_app, !sumA_app. lia.
 - rewrite Delta_app_iff in D. intuition.
 - rewrite Delta_app_iff in D'. intuition.
Qed.

Lemma additivity_bounded_k2 p :
 forall n, exists m,
   m < add_bound_k2 p /\
   h (p+n) - h n = h (p+m) - h m.
Proof.
 intros n. exists (reduced_k2 p n). split.
 - apply reduced_lt_k2.
 - now apply additivity_reduced_k2.
Qed.

Lemma decide_additivity_k2 p a b :
 calc_additivity 2 p (add_bound_k2 p) = (a,b) ->
 forall n, a + h n <= h (p+n) <= b + h n.
Proof.
 intros E n.
 assert (H : h n <= h (p+n)) by (apply f_mono; lia).
 assert (a <= h (p+n) - h n <= b); try lia.
 { destruct (@additivity_bounded_k2 p n) as (m & Hm & ->).
   clear n H.
   unfold calc_additivity in E.
   revert E. apply extrems_spec.
   rewrite all_diffs_spec.
   set (delta := fun x => _). apply (in_map delta). clear delta.
   apply countdown_in. lia. }
Qed.

(** Some initial results about quasi-additivity of H
    (for little values of p). *)

Lemma h_add_1 n : h n <= h (1+n) <= 1 + h n.
Proof.
 apply fk_add_1.
Qed.

Lemma h_add_2 n : 1 + h n <= h (2+n) <= 2 + h n.
Proof.
 apply fk_add_2.
Qed.

Lemma h_add_3 n : 1 + h n <= h (3+n) <= 3 + h n.
Proof.
 apply fk_add_3.
Qed.

Lemma h_add_4 n : 2 + h n <= h (4+n) <= 3 + h n.
Proof.
 apply decide_additivity_k2. now vm_compute.
Qed.

Lemma h_add_5 n : 3 + h n <= h (5+n) <= 4 + h n.
Proof.
 apply decide_additivity_k2. now vm_compute.
Qed.

Lemma h_add_6 n : 3 + h n <= h (6+n) <= 5 + h n.
Proof.
 apply decide_additivity_k2. now vm_compute.
Qed.

Lemma h_add_7 n : 4 + h n <= h (7+n) <= 6 + h n.
Proof.
 apply decide_additivity_k2. now vm_compute.
Qed.

Lemma h_add_8 n : 5 + h n <= h (8+n) <= 6 + h n.
Proof.
 apply decide_additivity_k2. now vm_compute.
Qed.

Lemma h_add_9 n : 5 + h n <= h (9+n) <= 7 + h n.
Proof.
 apply decide_additivity_k2. now vm_compute.
Qed.

Lemma h_add_10 n : 6 + h n <= h (10+n) <= 8 + h n.
Proof.
 apply decide_additivity_k2. now vm_compute.
Qed.

Lemma h_add_11 n : 7 + h n <= h (11+n) <= 8 + h n.
Proof.
 apply decide_additivity_k2. now vm_compute.
Qed.

Lemma h_add_12 n : 7 + h n <= h (12+n) <= 9 + h n.
Proof.
 apply decide_additivity_k2. now vm_compute.
Qed.

(** All the earlier cases were satisfying h(p+n)-h(p)-h(n) = {-1,0,1}
    But for p=18, h(18+n) = h n + h 18 + [-2..0] *)
Lemma h_add_18 n : 11 + h n <= h (18+n) <= 13 + h n.
Proof.
 apply decide_additivity_k2. now vm_compute.
Qed.

(** For comparison with f 3 *)
Lemma h_add_33 n : 22 + h n <= h (33+n) <= 23 + h n.
Proof.
 apply decide_additivity_k2. now vm_compute.
Qed.

(** h(39+n) = h n + h 39 + [0..2] *)
Lemma h_add_39 n : 26 + h n <= h (39+n) <= 28 + h n.
Proof.
 apply decide_additivity_k2. now vm_compute.
Qed.

(* TODO: experimentally, h(p+n)-h(p)-h(n) is in [-2..2] in general.
   Proof: ??
*)

(** At least, [h_addA] below proves that when p is a [A 2] number
    then [h(p+n)-h(p)-h(n)] is in {-1,0,1} for all n. *)

Lemma twice_A2_eqn n : 2 * A2 (5+n) + A2 n = A2 (7+n).
Proof.
 simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma twice_A2_eqn' n : 3<=n -> 2 * A2 n = A2 (n+2) - A2 (n-5).
Proof.
 rewrite Nat.lt_eq_cases; intros [H|<-]; [|trivial].
 red in H. rewrite Nat.lt_eq_cases in H. destruct H as [H|<-]; [|trivial].
 replace n with (5+(n-5)) at 1 by lia.
 replace (n+2) with (7+(n-5)) by lia.
 generalize (twice_A2_eqn (n-5)). lia.
Qed.

Lemma seq_A2_eqn n : A2 (3+n) + A2 (4+n) = A2 (5+n) + A2 n.
Proof.
 simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma seq_A2_eqn' n : 1<=n -> A2 n + A2 (S n) = A2 (n+2) + A2 (n-3).
Proof.
 rewrite Nat.lt_eq_cases; intros [H|<-]; [|trivial].
 red in H. rewrite Nat.lt_eq_cases in H. destruct H as [H|<-]; [|trivial].
 replace n with (3+(n-3)) at 1 2 by lia.
 rewrite seq_A2_eqn. f_equal. f_equal. lia.
Qed.

Lemma destruct_last {A} (l : list A) : l = [] \/ exists a l', l = l' ++ [a].
Proof.
 destruct l as [|a l].
 - now left.
 - right. destruct (rev (a::l)) as [|a' l'] eqn:E.
   + now apply rev_switch in E.
   + exists a', (rev l'). apply rev_switch in E. apply E.
Qed.

Lemma sumA_insert k x l :
 sumA k (insert x l) = A k x + sumA k l.
Proof.
 induction l; simpl; auto.
 destruct (x <=? a); simpl; rewrite ?IHl; lia.
Qed.

Lemma insert_in x l y : In y (insert x l) <-> x = y \/ In y l.
Proof.
 induction l; simpl; auto.
 - intuition.
 - case Nat.leb; simpl; rewrite ?IHl; intuition.
Qed.

Lemma insert_delta x l :
 Delta 3 l -> ~In x l -> ~In (x-1) l -> ~In (x+1) l -> Delta 2 (insert x l).
Proof.
 induction l.
 - simpl. autoh.
 - intros D H0 H1 H2.
   simpl.
   case Nat.leb_spec; intros.
   + constructor; autoh.
     simpl in H0,H2. lia.
   + rewrite Delta_alt in *; split; auto.
     * apply IHl; simpl in *; auto. destruct D; auto.
     * intros y. rewrite insert_in.
       intros [<-|IN]. simpl in *. lia.
       destruct D as (_,D). specialize (D y IN). lia.
Qed.

Lemma h_addA_eq q l : Delta 3 l ->
  ~In q l -> ~In (q-1) l -> ~In (q+1) l ->
  h (A2 q + sumA 2 l) = A2 (q-1) + h (sumA 2 l).
Proof.
 intros D Hq Hpq Hsq.
 rewrite <- sumA_insert.
 unfold h.
 rewrite f_sumA_lax; auto.
 rewrite f_sumA; auto.
 rewrite map_pred_insert, sumA_insert; auto.
 replace (Nat.pred q) with (q-1); lia.
 apply insert_delta; auto.
Qed.

Lemma h_addA q n : A2 (q-1) + h n - 1 <= h (A2 q + n) <= A2 (q-1) + h n + 1.
Proof.
 revert n.
 induction q as [q IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases q 3) as [LE|GT].
 - destruct q as [|[|[|[|n]]]]; simpl; intros.
   + generalize (h_add_1 n). simpl. lia.
   + generalize (h_add_2 n). simpl. lia.
   + generalize (h_add_3 n). simpl. lia.
   + generalize (h_add_4 n). simpl. lia.
   + lia.
 - intros n.
   destruct (additivity_bounded_k2 (A2 q) n) as (m & Hm & E).
   cut (A2 (q - 1) + h m - 1 <= h (A2 q + m) <= A2 (q - 1) + h m + 1).
   { generalize (@f_mono 2 n (A2 q + n)) (@f_mono 2 m (A2 q + m)).
     generalize (@A_nz 2 (q-1)). unfold h in *. lia. }
   clear E n.
   replace (add_bound_k2 (A2 q)) with (A2 (q+3)) in Hm.
   2:{ unfold add_bound_k2. f_equal. f_equal. rewrite invA_up_A; lia. }
   assert (D := decomp_delta 2 m).
   rewrite <- (decomp_sum 2 m). set (l := decomp 2 m) in *.
   destruct (destruct_last l) as [->|(a & l' & E)].
   + simpl. change (h 0) with 0.
     rewrite !Nat.add_0_r. unfold h. rewrite f_A. lia.
   + assert (Ha : a < 3+q).
     { apply (@A_lt_inv 2).
       rewrite <- (decomp_sum 2 m) in Hm. fold l in Hm.
       rewrite E in Hm. rewrite sumA_app in Hm. simpl sumA in Hm.
       rewrite Nat.add_comm. lia. }
     clearbody l. subst l. clear m Hm.
     rewrite Nat.add_succ_l, Nat.lt_succ_r, Nat.lt_eq_cases, or_comm in Ha.
     destruct Ha as [Ha|Ha].
     { (* a = q+2 *)
       clear IH.
       replace (A2 q + _) with (sumA 2 (l'++[S a])).
       2:{ rewrite !sumA_app. simpl. replace (a-2) with q; lia. }
       unfold h. rewrite !f_sumA; eauto using Delta_up_last.
       rewrite !map_app, !sumA_app. subst a; simpl.
       replace (pred (q+2)) with (q+1) by lia. lia. }
     rewrite Nat.add_succ_l, Nat.lt_succ_r, Nat.lt_eq_cases, or_comm in Ha.
     destruct Ha as [Ha|Ha].
     { (* a = q+1 *)
       subst a.
       replace (A2 q + _) with (A2 (q-3) + sumA 2 (l'++[q+2])) in *.
       2:{ rewrite !sumA_app. simpl.
           generalize (@seq_A2_eqn' q). simpl. lia. }
       assert (Hm : q-3 < q) by lia.
       specialize (IH (q-3) Hm (sumA 2 (l'++[q+2]))). revert IH.
       replace (q-3-1) with (q-4) by lia.
       set (u := h (_+_)) in *; clearbody u.
       unfold h.
       rewrite !f_sumA by (try apply Delta_up_last with (S q); auto; lia).
       rewrite !map_app, !sumA_app. simpl.
       generalize (@seq_A2_eqn' (q-1)).
       replace (pred (q+2)) with (q+1) by lia.
       replace (S (q-1)) with q by lia.
       replace (q-1+2) with (q+1) by lia.
       replace (q-1-3) with (q-4) by lia. lia. }
     rewrite Nat.lt_succ_r, Nat.lt_eq_cases, or_comm in Ha.
     destruct Ha as [Ha|Ha].
     { (* a = q *)
       subst a.
       assert (LE : A2 (q-5) <= A2 (q+2)) by (apply A_mono; lia).
       replace (A2 q + _) with (sumA 2 (l'++[q+2]) - A2 (q-5)) in *.
       2:{ rewrite !sumA_app. simpl. rewrite Nat.add_0_r.
           rewrite <- Nat.add_sub_assoc; trivial.
           rewrite <- twice_A2_eqn' by lia. simpl. lia. }
       assert (Hq : q-5 < q) by lia.
       set (u := sumA 2 (l'++[q+2])).
       assert (Hu : A2 (q-5) <= u).
       { unfold u. rewrite sumA_app. simpl. lia. }
       generalize (IH (q-5) Hq (u-A2 (q-5))); clear IH.
       rewrite (Nat.add_comm _ (_-_)), Nat.sub_add; trivial.
       set (v := u - _) in *. clearbody v.
       unfold h, u in *.
       rewrite !f_sumA by (try apply Delta_up_last with q; auto with arith).
       rewrite !map_app, !sumA_app. simpl.
       replace (pred (q+2)) with (q+1) by lia.
       replace (pred q) with (q-1) by lia.
       replace (q-5-1) with (q-6) by lia.
       assert (Hq' : 3 <= q-1) by lia.
       generalize (@twice_A2_eqn' (q-1) Hq').
       replace (q-1-5) with (q-6) by lia.
       replace ((q-1)+2) with (q+1) by lia.
       generalize (@A_nz 2 (q-1)). lia. }
     red in Ha. rewrite Nat.lt_eq_cases, or_comm in Ha.
     destruct Ha as [Ha|Ha].
     { (* a = q-1 *)
       subst q.
       replace (A2 (S a) + _) with (A2 a + sumA 2 (l'++[S a])) in *.
       2:{ rewrite !sumA_app. simpl. lia. }
       assert (Ha : a < S a) by lia.
       specialize (IH a Ha (sumA 2 (l'++[S a]))). revert IH.
       simpl. rewrite Nat.sub_0_r.
       set (u := h (_+_)) in *; clearbody u.
       unfold h.
       rewrite !f_sumA_lax
         by (try apply Delta_up_last with a; auto with arith hof).
       rewrite !map_app, !sumA_app. simpl.
       replace (pred a) with (a-1) by lia. lia. }
     { (* a <= q-2 *)
       clear IH.
       replace (A2 q + _) with (sumA 2 (l'++[a;q])).
       2:{ rewrite !sumA_app. simpl. lia. }
       unfold h. rewrite !f_sumA_lax; autoh.
       - rewrite !map_app, !sumA_app. simpl. replace (pred q) with (q-1); lia.
       - apply Delta_app_iff in D. destruct D as (D1 & D2 & D3).
         apply Delta_app_iff; repeat split; autoh.
         + constructor; autoh.
         + intros x x' IN [<-|[<-|[ ]]];
           specialize (D3 x a IN); simpl in *; lia. }
Qed.

(** Easy consequence : quasi-additivity -2..2 when p
    is the sum of two A2 numbers. *)

Lemma A2_times2 n : 2 * A2 (7+n) = sumA 2 [n;5+n;8+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma A2_times2' n : 5<=n -> 2 * A2 n = sumA 2 [n-7;n-2;n+1].
Proof.
 rewrite Nat.lt_eq_cases.
 intros [H|<-]; trivial.
 red in H. rewrite Nat.lt_eq_cases in H. destruct H as [H|<-]; trivial.
 replace n with (7+(n-7)) at 1 by lia.
 rewrite A2_times2. f_equal. repeat (f_equal; try lia).
Qed.

Lemma h_times2 n : 6<=n -> h (2 * A2 n) = 2 * A2 (n-1).
Proof.
 intros H. rewrite !A2_times2' by lia.
 unfold h. rewrite f_sumA. f_equal; simpl. repeat (f_equal; try lia).
 repeat (constructor; try lia).
Qed.

Lemma h_add_A_A p n u v : p = A2 u + A2 v ->
 h p + h n -2 <= h(p+n) <= h p + h n + 2.
Proof.
 revert u v.
 assert (H : forall u v, u+2<=v -> p = A2 u + A2 v ->
         h p + h n -2 <= h(p+n) <= h p + h n + 2).
 { intros u v LE ->.
   assert (Hu := h_addA u (A2 v+n)).
   rewrite Nat.add_assoc in Hu.
   assert (Hv := h_addA v n).
   replace (A2 u + A2 v) with (sumA 2 [u;v]) at 1 4 by (simpl; lia).
   unfold h at 1 5. rewrite f_sumA_lax; autoh. simpl.
   replace (pred u) with (u-1) by lia.
   replace (pred v) with (v-1) by lia. lia. }
 assert (H' : forall u v, u < v -> p = A2 u + A2 v ->
         h p + h n -2 <= h(p+n) <= h p + h n + 2).
 { intros u v LT E.
   destruct (Nat.leb_spec (u+2) v) as [LE|LT'].
   - eapply H; eauto.
   - replace v with (S u) in * by lia. clear LT LT'.
     destruct (Nat.eq_dec u 0) as [->|NE].
     + change (A2 0 + A2 1) with 3 in E. subst p.
       change (h 3) with 2.
       generalize (h_add_3 n). lia.
     + rewrite seq_A2_eqn' in E by lia.
       rewrite Nat.add_comm in E.
       apply H with (u-3) (u+2); auto. lia. }
 intros u v E.
 destruct (Nat.lt_total u v) as [LT|EQ_LT].
 - apply (H' u v); auto.
 - rewrite or_comm in EQ_LT. destruct EQ_LT as [LT|EQ].
   + rewrite Nat.add_comm in E. apply (H' v u); auto.
   + clear H H'. subst v p.
     destruct (Nat.leb_spec 6 u).
     * assert (Hu := h_addA u (A2 u+n)).
       rewrite Nat.add_assoc in Hu.
       assert (Hv := h_addA u n).
       replace (A2 u + A2 u) with (2 * A2 u) at 1 4 by lia.
       rewrite h_times2 by lia.
       lia.
     * destruct (Nat.eq_dec u 0) as [->|H0].
       { change (A2 0 + A2 0) with 2. change (h 2) with 1.
         generalize (h_add_2 n). lia. }
       destruct (Nat.eq_dec u 1) as [->|H1].
       { change (A2 1 + A2 1) with 4. change (h 4) with 3.
         generalize (h_add_4 n). lia. }
       destruct (Nat.eq_dec u 2) as [->|H2].
       { change (A2 2 + A2 2) with 6. change (h 6) with 4.
         generalize (h_add_6 n). lia. }
       destruct (Nat.eq_dec u 3) as [->|H3].
       { change (A2 3 + A2 3) with 8. change (h 8) with 5.
         generalize (h_add_8 n). lia. }
       destruct (Nat.eq_dec u 4) as [->|H4].
       { change (A2 4 + A2 4) with 12. change (h 12) with 8.
         generalize (h_add_12 n). lia. }
       destruct (Nat.eq_dec u 5) as [->|H5].
       { change (A2 5 + A2 5) with 18. change (h 18) with 13.
         generalize (h_add_18 n). lia. }
       lia.
Qed.

(* TODO : is there a version for substraction : p = A2 u - A2 v ? *)


(** * Comparing (f k) functions when k varies *)

Lemma f0_below_g n : f 0 n <= g n.
Proof.
 rewrite f_0_div2. apply g_Sdiv2_le.
Qed.

(** g_add_8 and h_add_8 are enough to show that g <= h *)

Lemma g_below_h n : g n <= h n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 8).
- (* compute for all n < 8 or : *)
  rewrite <- f_1_g. apply f_triangle_incrk. simpl. lia.
- replace n with (8+(n-8)) by lia.
  transitivity (5 + g (n - 8)). apply g_add_8.
  transitivity (5 + h (n - 8)). 2:apply h_add_8.
  specialize (IH (n-8)). lia.
Qed.

(** h_add_33 and f3_add_33 imply h <= f 3 *)

Lemma h_below_f3 n : h n <= f 3 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 33).
- clear IH.
  (* Alas f_triangle_incrk isn't enough : triangle(2+4)-3 = 18 < 33 *)
  unfold h. rewrite <- !fopt_spec.
  do 33 (destruct n; [vm_compute; auto|]). exfalso. lia.
- replace n with (33+(n-33)) by lia.
  transitivity (23 + h (n - 33)). apply h_add_33.
  transitivity (23 + f 3 (n - 33)).
  specialize (IH (n-33)). lia.
  apply (f3_add_33 (n-33)).
Qed.

(** Similarly, f 3 <= f 4 *)

Lemma f3_add_73 n : 51 + f 3 n <= f 3 (73+n) <= 54 + f 3 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f4_add_73 n : 54 + f 4 n <= f 4 (73+n) <= 57 + f 4 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f3_below_f4 n : f 3 n <= f 4 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 73).
- clear IH.
  rewrite <- !fopt_spec.
  do 73 (destruct n; [vm_compute; auto|]). exfalso. lia.
- replace n with (73+(n-73)) by lia.
  transitivity (54 + f 3 (n - 73)). apply (f3_add_73 (n-73)).
  transitivity (54 + f 4 (n - 73)).
  specialize (IH (n-73)). lia.
  apply (f4_add_73 (n-73)).
Qed.

(* And f 4 <= f 5 *)

Lemma f4_add_169 n : 125 + f 4 n <= f 4 (169+n) <= 129 + f 4 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f5_add_169 n : 129 + f 5 n <= f 5 (169+n) <= 135 + f 5 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f4_below_f5 n : f 4 n <= f 5 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 169).
- clear IH.
  rewrite <- !fopt_spec.
  do 169 (destruct n; [vm_compute; auto|]). exfalso. lia.
- replace n with (169+(n-169)) by lia.
  transitivity (129 + f 4 (n - 169)). apply (f4_add_169 (n-169)).
  transitivity (129 + f 5 (n - 169)).
  specialize (IH (n-169)). lia.
  apply (f5_add_169 (n-169)).
Qed.

(* And f 5 <= f 6 *)

(*
Lemma f5_add_424 n : 326 + f 5 n <= f 5 (424+n) <= 333 + f 5 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f6_add_424 n : 333 + f 6 n <= f 6 (424+n) <= 342 + f 6 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f5_below_f6 n : f 5 n <= f 6 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 424).
- clear IH.
  rewrite <- !fopt_spec. rewrite <- Nat.leb_le.
  do 424 (destruct n; [now vm_compute|]). exfalso. lia.
- replace n with (424+(n-424)) by lia.
  transitivity (333 + f 5 (n - 424)). apply (f5_add_424 (n-424)).
  transitivity (333 + f 6 (n - 424)).
  specialize (IH (n-424)). lia.
  apply (f6_add_424 (n-424)).
Qed.
*)

(** General proof : cf Words.f_grows *)
