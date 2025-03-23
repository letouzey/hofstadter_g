
Require Import MoreFun MoreList DeltaList FunG GenFib GenG.
Import ListNotations.
Set Implicit Arguments.

(** Study of quasi-additivity for [f k n] function defined in [GenG]:
    [f k (p+n)] is close to [f k p + f k n].
    Said otherwise, for some fixed p, few values are reached by
    [f k (p+n)-f k n] when n varies.
    For this study, we'll turn a strict q-decomposition of n into
    a lax decomp of (p+n).
*)

(** First, some proofs for [p<=4] that hold for any [k<>0] *)

Lemma fk_add_1 k n : f k n <= f k (1+n) <= 1 + f k n.
Proof.
 destruct (f_step k n); simpl; lia.
Qed.

Lemma fk_add_2 k n : k<>0 -> 1 + f k n <= f k (2+n) <= 2 + f k n.
Proof.
 intros K. split.
 - generalize (@f_SS k n K). simpl. lia.
 - apply f_le_add.
Qed.

Lemma fk_add_3 k n : k<>0 -> 1 + f k n <= f k (3+n) <= 3 + f k n.
Proof.
 intros K. split.
 - transitivity (f k (2+n)). now apply fk_add_2. apply f_mono. lia.
 - apply f_le_add.
Qed.

Lemma fk_add_4 k n : k<>0 -> 2 + f k n <= f k (4+n) <= 4 + f k n.
Proof.
 intros K. split.
 - transitivity (1 + f k (2 + n)).
   + generalize (@fk_add_2 k n K). lia.
   + apply (@fk_add_2 k (2+n) K).
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
   no need to dig deeper than value [invA_up k p + 3*k-4].
   Note : tighter upper bounds than that could probably be found,
   but seem harder to prove *)

Definition bound_idx k p := invA_up k p + 3*k-4.

Definition low_high k p l := cut_lt_ge (bound_idx k p) l.

Definition addlow k p low :=
 match rev low with
 | [] => decomp k p
 | a::rlow' =>
   let u:=invA_up k p +k-2 in
   if u <? a then
     (* a is big enough : putting (S a) instead of a in the decomposition
        adds at least p (while remaining lax). *)
     decompminus k (rev rlow'++[S a]) (A k (a-(k-1)) - p)
   else
     (* a is low enough : we can add an extra term in the decomposition *)
     decompminus k (low ++[u+(k-1)]) (A k (u+(k-1)) - p)
 end.

Lemma addlow_sum k p l : 1<k ->
  let low := fst (low_high k p l) in
  sumA k (addlow k p low) = p + sumA k low.
Proof.
 intros K.
 destruct (low_high k p l) as (low,high) eqn:E. simpl.
 unfold addlow.
 destruct (rev low) as [|a rlow'] eqn:E'.
 - apply rev_switch in E'. rewrite decomp_sum, E'. simpl; auto.
 - apply rev_switch in E'. simpl in E'.
   set (u := invA_up k p + k - 2).
   case Nat.ltb_spec; intros.
   + rewrite decompminus_sum, E'.
     rewrite !sumA_app.
     cbn - [A]. rewrite A_S.
     assert (p <= A k (a-(k-1))); try lia.
     { etransitivity. apply (invA_up_spec k). apply A_mono. lia. }
   + rewrite decompminus_sum. rewrite sumA_app. simpl.
     assert (p <= A k (u+(k-1))); try lia.
     { etransitivity. apply (invA_up_spec k). apply A_mono. lia. }
Qed.

Definition addlow_delta k p l : 1<k -> Delta k l ->
  let (low,high) := low_high k p l in
  Delta (k-1) (addlow k p low ++ high).
Proof.
 intros K D.
 set (u := bound_idx k p).
 generalize (cut_app u l) (cut_fst u l) (cut_snd' u D).
 change (cut_lt_ge _ _) with (low_high k p l).
 destruct (low_high k p l) as (low,high). simpl.
 intros E Hlow Hhigh.
 unfold addlow.
 destruct (rev low) as [|a rlow'] eqn:E'.
 - apply rev_switch in E'. subst low. simpl in E. subst high.
   apply Delta_app_iff. repeat split.
   { apply Delta_S. fixpred. apply decomp_delta. }
   { apply Delta_S. now fixpred. }
   { intros x x' IN IN'. apply Hhigh in IN'.
     transitivity u; auto with arith.
     assert (A k x <= p).
     { rewrite <- (decomp_sum k p). apply sumA_in_le; auto. }
     assert (x <= invA_up k p).
     { apply (@A_le_inv k).
       transitivity p; auto. apply invA_up_spec. }
     unfold bound_idx in u. lia. }
 - apply rev_switch in E'. simpl in E'.
   set (v := invA_up k p + k-2).
   subst l.
   rewrite Delta_app_iff in D. destruct D as (D1 & D2 & D3).
   case Nat.ltb_spec; intros.
   + apply decompminus_app_delta; try lia.
     rewrite Delta_app_iff. repeat split.
     { eapply Delta_up_last with a; auto. rewrite <- E'.
       apply Delta_S. now fixpred. }
     { apply Delta_S. now fixpred. }
     { intros x x' IN IN'.
       rewrite in_app_iff in IN. destruct IN as [IN|[<-|[ ]]].
       * specialize (D3 x x').
         rewrite E', in_app_iff in D3.
         specialize (D3 (or_introl IN) IN'). lia.
       * specialize (D3 a x').
         rewrite E', in_app_iff in D3.
         specialize (D3 (or_intror (or_introl eq_refl)) IN'). lia. }
   + apply decompminus_app_delta; try lia.
     rewrite <- app_assoc. apply Delta_app_iff; repeat split.
     * apply Delta_S; now fixpred.
     * rewrite Delta_app_iff; repeat split; autoh.
       { apply Delta_S. now fixpred. }
       { intros x x' [<-|[ ]] IN'. specialize (Hhigh x' IN').
         unfold bound_idx in u. lia. }
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
  k<>0 -> reduced k p n < add_bound k p.
Proof.
 intros K.
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

Lemma additivity_reduced k p : 1<k ->
 forall n,
   let m := reduced k p n in
   f k (p+n) - f k n = f k (p+m) - f k m.
Proof.
 intros K n.
 assert (D := decomp_delta k n).
 unfold reduced; simpl.
 rewrite <- (decomp_sum k n) at 1 2.
 set (l := decomp k n) in *. clearbody l.
 assert (E := cut_app (bound_idx k p) l).
 change (cut_lt_ge _ _) with (low_high k p l) in E.
 assert (E' := @addlow_sum k p l K).
 assert (D' := @addlow_delta k p l K D).
 destruct (low_high k p l) as (low,high). simpl in *.
 subst l.
 rewrite sumA_app at 1.
 rewrite Nat.add_assoc, <- E', <- !sumA_app.
 rewrite !f_sumA_lax; autoh.
 - rewrite !map_app, !sumA_app. lia.
 - rewrite Delta_app_iff in D. apply Delta_S. now fixpred.
 - rewrite Delta_app_iff in D'. apply D'.
 - rewrite Delta_app_iff in D'. apply Delta_S. now fixpred.
Qed.

Lemma additivity_bounded k p : 1<k ->
 forall n, exists m,
   m < add_bound k p /\
   f k (p+n) - f k n = f k (p+m) - f k m.
Proof.
 intros K n. exists (reduced k p n). split.
 - apply reduced_lt; lia.
 - now apply additivity_reduced.
Qed.

(** We could hence prove bounds for [f k (p+n)-f k p] by computation. *)

Fixpoint map2 {A B C}(f:A->B->C) l1 l2 :=
  match l1,l2 with
  | x1::l1', x2::l2' => f x1 x2 :: map2 f l1' l2'
  | _, _ => []
  end.

Definition all_diffs k p bound :=
  let stq := ftabulate k (p + (bound-1)) in
  map2 Nat.sub stq (skipn p stq).

Lemma all_diffs_spec k p bound :
  all_diffs k p bound =
  map (fun x => f k (p+x)-f k x) (countdown (bound - 1)).
Proof.
 unfold all_diffs.
 rewrite ftabulate_spec.
 rewrite skipn_map.
 replace p with (p+(bound-1)-(bound-1)) at 2 by lia.
 rewrite skipn_countdown by lia.
 induction (bound-1).
 - simpl. destruct p; simpl; auto. f_equal. now destruct countdown.
 - rewrite Nat.add_succ_r. simpl. f_equal; auto.
Qed.

Definition calc_additivity k p bound := extrems (all_diffs k p bound).

Lemma decide_additivity k p a b : 1<k ->
 calc_additivity k p (add_bound k p) = (a,b) ->
 forall n, a + f k n <= f k (p+n) <= b + f k n.
Proof.
 intros Hq E n.
 assert (H : f k n <= f k (p+n)) by (apply f_mono; lia).
 assert (a <= f k (p+n) - f k n <= b); try lia.
 { destruct (@additivity_bounded k p Hq n) as (m & Hm & ->).
   clear n H.
   unfold calc_additivity in E.
   revert E. apply extrems_spec.
   rewrite all_diffs_spec.
   set (delta := fun x => _). apply (in_map delta). clear delta.
   apply countdown_in. lia. }
Qed.

(** For exemple, let's do some proofs by computations for f 4.
    Note : f 3 (known as H) is considered afterwards, with an improved
    bound.
*)

Lemma f4_add_5 n : 3 + f 4 n <= f 4 (5+n) <= 4 + f 4 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f4_add_6 n : 3 + f 4 n <= f 4 (6+n) <= 5 + f 4 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f4_add_7 n : 4 + f 4 n <= f 4 (7+n) <= 6 + f 4 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f4_add_8 n : 5 + f 4 n <= f 4 (8+n) <= 7 + f 4 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f4_add_9 n : 6 + f 4 n <= f 4 (9+n) <= 8 + f 4 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f4_add_10 n : 6 + f 4 n <= f 4 (10+n) <= 8 + f 4 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f4_add_33 n : 23 + f 4 n <= f 4 (33+n) <= 25 + f 4 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

(* TODO general bounds for f4(n+m)-f4(n)-f4(m) ??
   Same for any fk ??
*)

(** Particular case of function H, i.e. k=3 *)

Definition h := f 3.

Notation A3 := (A 3).

(** First, for H the previous results could be slightly improved,
    with a bound of [invA_up 3 p + 3] instead of
    [bound_idx 3 p = invA_up 3 p + 3*3-4] *)

Lemma twice_A3_le n : 2 * A3 n <= A3 (2+n).
Proof.
 destruct n; simpl; auto.
 replace (n-0) with n by lia.
 generalize (@A_mono 3 (n-2) (n-1)). lia.
Qed.

Definition bound_idx_k3 p := invA_up 3 p + 3.

Definition low_high_k3 p l := cut_lt_ge (bound_idx_k3 p) l.

Definition addlow_k3 p low :=
 match rev low with
 | [] => decomp 3 p
 | a::rlow' =>
   let u:=invA_up 3 p in
   if a <? u then
     decompminus 3 (low ++[u+1]) (A3 (u+1) - p)
   else
     decompminus 3 (rev rlow'++[a-1;1+a]) (A3 (a+2) - A3 a - p)
 end.

Lemma addlow_sum_k3 p l :
  let low := fst (low_high_k3 p l) in
  sumA 3 (addlow_k3 p low) = p + sumA 3 low.
Proof.
 destruct (low_high_k3 p l) as (low,high) eqn:E. simpl.
 unfold addlow_k3.
 destruct (rev low) as [|a rlow'] eqn:E'.
 - apply rev_switch in E'. rewrite decomp_sum, E'. simpl; auto.
 - apply rev_switch in E'. simpl in E'.
   remember (invA_up 3 p) as u.
   case Nat.ltb_spec; intros.
   + rewrite decompminus_sum. rewrite sumA_app. simpl.
     assert (p <= A3 (u+1)); try lia.
     { etransitivity. apply (invA_up_spec 3). apply A_mono. lia. }
   + rewrite decompminus_sum, E'. rewrite !sumA_app.
     cbn - [A]. rewrite Nat.add_0_r.
     replace (A3 _ + A3 _) with (A3 (a+2)).
     2:{ rewrite (@A_sum 3 (a+2)), Nat.add_comm by lia.
         f_equal; f_equal; lia. }
     assert (p + A3 a <= A3 (a+2)); try lia.
     { generalize (invA_up_spec 3 p). rewrite <- Hequ.
       generalize (@A_mono 3 u a) (twice_A3_le a).
       rewrite Nat.add_comm. lia. }
Qed.

Definition addlow_delta_k3 p l : 1<p -> Delta 3 l ->
  let (low,high) := low_high_k3 p l in
  Delta 2 (addlow_k3 p low ++ high).
Proof.
 intros Hp D.
 set (u := bound_idx_k3 p).
 generalize (cut_app u l) (cut_fst u l) (cut_snd' u D).
 change (cut_lt_ge _ _) with (low_high_k3 p l).
 destruct (low_high_k3 p l) as (low,high). simpl.
 intros E Hlow Hhigh.
 unfold addlow_k3.
 destruct (rev low) as [|a rlow'] eqn:E'.
 - apply rev_switch in E'. subst low. simpl in E. subst high.
   apply Delta_app_iff. repeat split; auto using decomp_delta with hof.
   intros x x' IN IN'. apply Hhigh in IN'.
   transitivity u; auto with arith.
   assert (A3 x <= p).
   { rewrite <- (decomp_sum 3 p). apply sumA_in_le; auto. }
   assert (x <= invA_up 3 p).
   { apply (@A_le_inv 3).
     transitivity p; auto. apply invA_up_spec. }
   unfold bound_idx_k3 in u. lia.
 - apply rev_switch in E'. simpl in E'.
   set (v := invA_up 3 p).
   subst l.
   rewrite Delta_app_iff in D. destruct D as (D1 & D2 & D3).
   case Nat.ltb_spec; intros.
   + change 2 with (3-1) at 1. apply decompminus_app_delta; try easy.
     rewrite Delta_app_iff. repeat split; autoh.
     * rewrite Delta_app_iff; repeat split; autoh.
       intros x x' IN [<-|[ ]].
       rewrite E' in *. eapply Delta_last_le in IN; eauto. lia.
     * intros x x'. rewrite in_app_iff. intros [IN|[<-|[ ]]] IN'.
       { specialize (D3 x x' IN IN'). lia. }
       { specialize (Hhigh x' IN'). unfold bound_idx_k3 in u. lia. }
   + change 2 with (3-1) at 1. apply decompminus_app_delta; try easy.
     rewrite Delta_app_iff. repeat split; autoh.
     * rewrite E' in D1. rewrite Delta_app_iff in D1.
       destruct D1 as (D11 & D12 & D13).
       rewrite Delta_app_iff. repeat split; autoh.
       { constructor; autoh. rewrite Nat.lt_nge in Hp.
         rewrite <- (invA_up_is_0 3) in Hp. lia. }
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

Definition add_bound_k3 p := A3 (invA_up 3 p + 3).

Definition reduced_k3 p n := sumA 3 (fst (low_high_k3 p (decomp 3 n))).

Lemma reduced_lt_k3 p n :
  reduced_k3 p n < add_bound_k3 p.
Proof.
 unfold reduced_k3, add_bound_k3. fold (bound_idx_k3 p).
 assert (D := decomp_delta 3 n).
 set (l := decomp 3 n) in *. clearbody l.
 assert (E := cut_app (bound_idx_k3 p) l).
 assert (B := cut_fst (bound_idx_k3 p) l).
 change (cut_lt_ge _ _) with (low_high_k3 p l) in E,B.
 destruct (low_high_k3 p l) as (low,high) eqn:E'. simpl fst in *.
 apply sumA_below; auto.
 rewrite <-E, Delta_app_iff in D. intuition.
Qed.

Lemma additivity_reduced_k3 p n : 1<p ->
  let m := reduced_k3 p n in
  h (p+n) - h n = h (p+m) - h m.
Proof.
 intros Hp. assert (D := decomp_delta 3 n).
 unfold reduced_k3; simpl.
 rewrite <- (decomp_sum 3 n) at 1 2.
 set (l := decomp 3 n) in *. clearbody l.
 assert (E := cut_app (bound_idx_k3 p) l).
 change (cut_lt_ge _ _) with (low_high_k3 p l) in E.
 assert (E' := @addlow_sum_k3 p l).
 assert (D' := @addlow_delta_k3 p l Hp D).
 destruct (low_high_k3 p l) as (low,high). simpl in *.
 subst l.
 rewrite sumA_app at 1.
 rewrite Nat.add_assoc, <- E', <- !sumA_app.
 unfold h. rewrite !f_sumA_lax; autoh.
 - rewrite !map_app, !sumA_app. lia.
 - rewrite Delta_app_iff in D. intuith.
 - rewrite Delta_app_iff in D'. intuith.
Qed.

Lemma additivity_bounded_k3 p : 1<p ->
 forall n, exists m,
   m < add_bound_k3 p /\
   h (p+n) - h n = h (p+m) - h m.
Proof.
 intros Hp n. exists (reduced_k3 p n). split.
 - apply reduced_lt_k3.
 - now apply additivity_reduced_k3.
Qed.

Lemma decide_additivity_k3 p a b : 1<p ->
 calc_additivity 3 p (add_bound_k3 p) = (a,b) ->
 forall n, a + h n <= h (p+n) <= b + h n.
Proof.
 intros Hp E n.
 assert (H : h n <= h (p+n)) by (apply f_mono; lia).
 assert (a <= h (p+n) - h n <= b); try lia.
 { destruct (@additivity_bounded_k3 p Hp n) as (m & Hm & ->).
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
 now apply fk_add_2.
Qed.

Lemma h_add_3 n : 1 + h n <= h (3+n) <= 3 + h n.
Proof.
 now apply fk_add_3.
Qed.

Lemma h_add_4 n : 2 + h n <= h (4+n) <= 3 + h n.
Proof.
 apply decide_additivity_k3. lia. now vm_compute.
Qed.

Lemma h_add_5 n : 3 + h n <= h (5+n) <= 4 + h n.
Proof.
 apply decide_additivity_k3. lia. now vm_compute.
Qed.

Lemma h_add_6 n : 3 + h n <= h (6+n) <= 5 + h n.
Proof.
 apply decide_additivity_k3. lia. now vm_compute.
Qed.

Lemma h_add_7 n : 4 + h n <= h (7+n) <= 6 + h n.
Proof.
 apply decide_additivity_k3. lia. now vm_compute.
Qed.

Lemma h_add_8 n : 5 + h n <= h (8+n) <= 6 + h n.
Proof.
 apply decide_additivity_k3. lia. now vm_compute.
Qed.

Lemma h_add_9 n : 5 + h n <= h (9+n) <= 7 + h n.
Proof.
 apply decide_additivity_k3. lia. now vm_compute.
Qed.

Lemma h_add_10 n : 6 + h n <= h (10+n) <= 8 + h n.
Proof.
 apply decide_additivity_k3. lia. now vm_compute.
Qed.

Lemma h_add_11 n : 7 + h n <= h (11+n) <= 8 + h n.
Proof.
 apply decide_additivity_k3. lia. now vm_compute.
Qed.

Lemma h_add_12 n : 7 + h n <= h (12+n) <= 9 + h n.
Proof.
 apply decide_additivity_k3. lia. now vm_compute.
Qed.

(** All the earlier cases were satisfying h(p+n)-h(p)-h(n) = {-1,0,1}
    But for p=18, h(18+n) = h n + h 18 + [-2..0] *)
Lemma h_add_18 n : 11 + h n <= h (18+n) <= 13 + h n.
Proof.
 apply decide_additivity_k3. lia. now vm_compute.
Qed.

(** For comparison with f 3 *)
Lemma h_add_33 n : 22 + h n <= h (33+n) <= 23 + h n.
Proof.
 apply decide_additivity_k3. lia. now vm_compute.
Qed.

(** h(39+n) = h n + h 39 + [0..2] *)
Lemma h_add_39 n : 26 + h n <= h (39+n) <= 28 + h n.
Proof.
 apply decide_additivity_k3. lia. now vm_compute.
Qed.

(* In general, h(p+n)-h(p)-h(n) is in [-2..2].
   Proof: See F3.h_quasiadd (via real frequencies, hence R axioms)
   TODO: Constructive Proof ?
*)

(** At least, [h_addA] below proves that when p is a [A 2] number
    then [h(p+n)-h(p)-h(n)] is in {-1,0,1} for all n. *)

Lemma twice_A3_eqn n : 2 * A3 (5+n) + A3 n = A3 (7+n).
Proof.
 simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma twice_A3_eqn' n : 3<=n -> 2 * A3 n = A3 (n+2) - A3 (n-5).
Proof.
 rewrite Nat.lt_eq_cases; intros [H|<-]; [|trivial].
 red in H. rewrite Nat.lt_eq_cases in H. destruct H as [H|<-]; [|trivial].
 replace n with (5+(n-5)) at 1 by lia.
 replace (n+2) with (7+(n-5)) by lia.
 generalize (twice_A3_eqn (n-5)). lia.
Qed.

Lemma seq_A3_eqn n : A3 (3+n) + A3 (4+n) = A3 (5+n) + A3 n.
Proof.
 simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma seq_A3_eqn' n : 1<=n -> A3 n + A3 (S n) = A3 (n+2) + A3 (n-3).
Proof.
 rewrite Nat.lt_eq_cases; intros [H|<-]; [|trivial].
 red in H. rewrite Nat.lt_eq_cases in H. destruct H as [H|<-]; [|trivial].
 replace n with (3+(n-3)) at 1 2 by lia.
 rewrite seq_A3_eqn. f_equal. f_equal. lia.
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

Lemma h_addA_eq p l : Delta 3 l ->
  ~In p l -> ~In (p-1) l -> ~In (p+1) l ->
  h (A3 p + sumA 3 l) = A3 (p-1) + h (sumA 3 l).
Proof.
 intros D H0 H1 H2.
 rewrite <- sumA_insert.
 unfold h.
 rewrite f_sumA_lax; auto.
 rewrite f_sumA; auto.
 rewrite map_pred_insert, sumA_insert; auto.
 replace (Nat.pred p) with (p-1); lia.
 now apply insert_delta2.
Qed.

Lemma h_addA p n : A3 (p-1) + h n - 1 <= h (A3 p + n) <= A3 (p-1) + h n + 1.
Proof.
 revert n.
 induction p as [p IH] using lt_wf_ind.
 destruct (Nat.le_gt_cases p 3) as [LE|GT].
 - destruct p as [|[|[|[|n]]]]; simpl; intros.
   + generalize (h_add_1 n). simpl. lia.
   + generalize (h_add_2 n). simpl. lia.
   + generalize (h_add_3 n). simpl. lia.
   + generalize (h_add_4 n). simpl. lia.
   + lia.
 - intros n.
   assert (Hp : 1 < A3 p) by (apply (@A_lt 3 0); lia).
   destruct (@additivity_bounded_k3 (A3 p) Hp n) as (m & Hm & E).
   cut (A3 (p - 1) + h m - 1 <= h (A3 p + m) <= A3 (p - 1) + h m + 1).
   { generalize (@f_mono 3 n (A3 p + n)) (@f_mono 3 m (A3 p + m)).
     generalize (@A_nz 3 (p-1)). unfold h in *. lia. }
   clear E n.
   replace (add_bound_k3 (A3 p)) with (A3 (p+3)) in Hm.
   2:{ unfold add_bound_k3. f_equal. f_equal. rewrite invA_up_A; lia. }
   assert (D := decomp_delta 3 m).
   rewrite <- (decomp_sum 3 m). set (l := decomp 3 m) in *.
   destruct (destruct_last l) as [->|(a & l' & E)].
   + simpl. change (h 0) with 0.
     rewrite !Nat.add_0_r. unfold h. rewrite f_A; lia.
   + assert (Ha : a < 3+p).
     { apply (@A_lt_inv 3).
       rewrite <- (decomp_sum 3 m) in Hm. fold l in Hm.
       rewrite E in Hm. rewrite sumA_app in Hm. simpl sumA in Hm.
       rewrite Nat.add_comm. lia. }
     clearbody l. subst l. clear m Hm.
     rewrite Nat.add_succ_l, Nat.lt_succ_r, Nat.lt_eq_cases, or_comm in Ha.
     destruct Ha as [Ha|Ha].
     { (* a = p+2 *)
       clear IH.
       replace (A3 p + _) with (sumA 3 (l'++[S a])).
       2:{ rewrite !sumA_app. simpl. replace (a-2) with p; lia. }
       unfold h. rewrite !f_sumA; eauto using Delta_up_last.
       rewrite !map_app, !sumA_app. subst a; simpl.
       replace (pred (p+2)) with (p+1) by lia. lia. }
     rewrite Nat.add_succ_l, Nat.lt_succ_r, Nat.lt_eq_cases, or_comm in Ha.
     destruct Ha as [Ha|Ha].
     { (* a = p+1 *)
       subst a.
       replace (A3 p + _) with (A3 (p-3) + sumA 3 (l'++[p+2])) in *.
       2:{ rewrite !sumA_app. simpl.
           generalize (@seq_A3_eqn' p). simpl. lia. }
       assert (Hm : p-3 < p) by lia.
       specialize (IH (p-3) Hm (sumA 3 (l'++[p+2]))). revert IH.
       replace (p-3-1) with (p-4) by lia.
       set (u := h (_+_)) in *; clearbody u.
       unfold h.
       rewrite !f_sumA by (try apply Delta_up_last with (S p); auto; lia).
       rewrite !map_app, !sumA_app. simpl.
       generalize (@seq_A3_eqn' (p-1)).
       replace (pred (p+2)) with (p+1) by lia.
       replace (S (p-1)) with p by lia.
       replace (p-1+2) with (p+1) by lia.
       replace (p-1-3) with (p-4) by lia. lia. }
     rewrite Nat.lt_succ_r, Nat.lt_eq_cases, or_comm in Ha.
     destruct Ha as [Ha|Ha].
     { (* a = p *)
       subst a.
       assert (LE : A3 (p-5) <= A3 (p+2)) by (apply A_mono; lia).
       replace (A3 p + _) with (sumA 3 (l'++[p+2]) - A3 (p-5)) in *.
       2:{ rewrite !sumA_app. simpl. rewrite Nat.add_0_r.
           rewrite <- Nat.add_sub_assoc; trivial.
           rewrite <- twice_A3_eqn' by lia. simpl. lia. }
       clear Hp.
       assert (Hp : p-5 < p) by lia.
       set (u := sumA 3 (l'++[p+2])).
       assert (Hu : A3 (p-5) <= u).
       { unfold u. rewrite sumA_app. simpl. lia. }
       generalize (IH (p-5) Hp (u-A3 (p-5))); clear IH.
       rewrite (Nat.add_comm _ (_-_)), Nat.sub_add; trivial.
       set (v := u - _) in *. clearbody v.
       unfold h, u in *.
       rewrite !f_sumA by (try apply Delta_up_last with p; auto with arith).
       rewrite !map_app, !sumA_app. simpl.
       replace (pred (p+2)) with (p+1) by lia.
       replace (pred p) with (p-1) by lia.
       replace (p-5-1) with (p-6) by lia.
       assert (Hp' : 3 <= p-1) by lia.
       generalize (@twice_A3_eqn' (p-1) Hp').
       replace (p-1-5) with (p-6) by lia.
       replace ((p-1)+2) with (p+1) by lia.
       generalize (@A_nz 3 (p-1)). lia. }
     red in Ha. rewrite Nat.lt_eq_cases, or_comm in Ha.
     destruct Ha as [Ha|Ha].
     { (* a = p-1 *)
       subst p.
       replace (A3 (S a) + _) with (A3 a + sumA 3 (l'++[S a])) in *.
       2:{ rewrite !sumA_app. simpl. lia. }
       assert (Ha : a < S a) by lia.
       specialize (IH a Ha (sumA 3 (l'++[S a]))). revert IH.
       simpl. rewrite Nat.sub_0_r.
       set (u := h (_+_)) in *; clearbody u.
       unfold h.
       rewrite !f_sumA_lax
         by (try apply Delta_up_last with a; auto with arith hof).
       rewrite !map_app, !sumA_app. simpl.
       replace (pred a) with (a-1) by lia. lia. }
     { (* a <= p-2 *)
       clear IH.
       replace (A3 p + _) with (sumA 3 (l'++[a;p])).
       2:{ rewrite !sumA_app. simpl. lia. }
       unfold h. rewrite !f_sumA_lax; autoh.
       - rewrite !map_app, !sumA_app. simpl. replace (pred p) with (p-1); lia.
       - apply Delta_app_iff in D. destruct D as (D1 & D2 & D3).
         apply Delta_app_iff; repeat split; autoh.
         + constructor; autoh.
         + intros x x' IN [<-|[<-|[ ]]];
           specialize (D3 x a IN); simpl in *; lia. }
Qed.

(** Easy consequence : quasi-additivity -2..2 when p
    is the sum of two A3 numbers. *)

Lemma A3_times2 n : 2 * A3 (7+n) = sumA 3 [n;5+n;8+n].
Proof.
 simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma A3_times2' n : 5<=n -> 2 * A3 n = sumA 3 [n-7;n-2;n+1].
Proof.
 rewrite Nat.lt_eq_cases.
 intros [H|<-]; trivial.
 red in H. rewrite Nat.lt_eq_cases in H. destruct H as [H|<-]; trivial.
 replace n with (7+(n-7)) at 1 by lia.
 rewrite A3_times2. f_equal. repeat (f_equal; try lia).
Qed.

Lemma h_times2 n : 6<=n -> h (2 * A3 n) = 2 * A3 (n-1).
Proof.
 intros H. rewrite !A3_times2' by lia.
 unfold h. rewrite f_sumA; try easy.
 f_equal; simpl. repeat (f_equal; try lia).
 repeat (constructor; try lia).
Qed.

Lemma h_add_A_A p n u v : p = A3 u + A3 v ->
 h p + h n -2 <= h(p+n) <= h p + h n + 2.
Proof.
 revert u v.
 assert (H : forall u v, u+2<=v -> p = A3 u + A3 v ->
         h p + h n -2 <= h(p+n) <= h p + h n + 2).
 { intros u v LE ->.
   assert (Hu := h_addA u (A3 v+n)).
   rewrite Nat.add_assoc in Hu.
   assert (Hv := h_addA v n).
   replace (A3 u + A3 v) with (sumA 3 [u;v]) at 1 4 by (simpl; lia).
   unfold h at 1 5. rewrite f_sumA_lax; autoh. simpl.
   replace (pred u) with (u-1) by lia.
   replace (pred v) with (v-1) by lia. lia. }
 assert (H' : forall u v, u < v -> p = A3 u + A3 v ->
         h p + h n -2 <= h(p+n) <= h p + h n + 2).
 { intros u v LT E.
   destruct (Nat.leb_spec (u+2) v) as [LE|LT'].
   - eapply H; eauto.
   - replace v with (S u) in * by lia. clear LT LT'.
     destruct (Nat.eq_dec u 0) as [->|NE].
     + change (A3 0 + A3 1) with 3 in E. subst p.
       change (h 3) with 2.
       generalize (h_add_3 n). lia.
     + rewrite seq_A3_eqn' in E by lia.
       rewrite Nat.add_comm in E.
       apply H with (u-3) (u+2); auto. lia. }
 intros u v E.
 destruct (Nat.lt_total u v) as [LT|EQ_LT].
 - apply (H' u v); auto.
 - rewrite or_comm in EQ_LT. destruct EQ_LT as [LT|EQ].
   + rewrite Nat.add_comm in E. apply (H' v u); auto.
   + clear H H'. subst v p.
     destruct (Nat.leb_spec 6 u).
     * assert (Hu := h_addA u (A3 u+n)).
       rewrite Nat.add_assoc in Hu.
       assert (Hv := h_addA u n).
       replace (A3 u + A3 u) with (2 * A3 u) at 1 4 by lia.
       rewrite h_times2 by lia.
       lia.
     * destruct (Nat.eq_dec u 0) as [->|H0].
       { change (A3 0 + A3 0) with 2. change (h 2) with 1.
         generalize (h_add_2 n). lia. }
       destruct (Nat.eq_dec u 1) as [->|H1].
       { change (A3 1 + A3 1) with 4. change (h 4) with 3.
         generalize (h_add_4 n). lia. }
       destruct (Nat.eq_dec u 2) as [->|H2].
       { change (A3 2 + A3 2) with 6. change (h 6) with 4.
         generalize (h_add_6 n). lia. }
       destruct (Nat.eq_dec u 3) as [->|H3].
       { change (A3 3 + A3 3) with 8. change (h 8) with 5.
         generalize (h_add_8 n). lia. }
       destruct (Nat.eq_dec u 4) as [->|H4].
       { change (A3 4 + A3 4) with 12. change (h 12) with 8.
         generalize (h_add_12 n). lia. }
       destruct (Nat.eq_dec u 5) as [->|H5].
       { change (A3 5 + A3 5) with 18. change (h 18) with 13.
         generalize (h_add_18 n). lia. }
       lia.
Qed.

(* TODO : is there a version for substraction : p = A3 u - A3 v ? *)


(** * Comparing (f k) functions when k varies *)

Lemma f1_below_g n : f 1 n <= g n.
Proof.
 rewrite f_1_div2. apply g_Sdiv2_le.
Qed.

(** g_add_8 and h_add_8 are enough to show that g <= h *)

Lemma g_below_h n : g n <= h n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 8).
- (* compute for all n < 8 or : *)
  rewrite <- f_2_g. apply f_triangle_incrk. unfold quad; simpl. lia.
- replace n with (8+(n-8)) by lia.
  transitivity (5 + g (n - 8)). apply g_add_8.
  transitivity (5 + h (n - 8)). 2:apply h_add_8.
  specialize (IH (n-8)). lia.
Qed.

(** h_add_33 and f3_add_33 imply h <= f 4 *)

Lemma intvl_dec a b tst :
  (forallb tst (seq a (S b-a))) = true ->
  forall n, a <= n <= b -> tst n = true.
Proof.
 intros H n Hn.
 rewrite forallb_forall in H. apply H. rewrite in_seq. lia.
Qed.

Lemma intvl_dec_0 b tst :
  (forallb tst (seq 0 b)) = true ->
  forall n, n < b -> tst n = true.
Proof.
 intros H n Hn. destruct b as [|b]; try lia.
 replace (S b) with (S b-0) in H by lia.
 apply (@intvl_dec _ _ _ H n). lia.
Qed.

Lemma h_below_f4 n : h n <= f 4 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 33).
- clear IH.
  (* Alas f_triangle_incrq isn't enough : triangle(2+4)-3 = 18 < 33 *)
  unfold h. rewrite <- !fopt_spec, <- Nat.leb_le. revert n H.
  apply intvl_dec_0. now vm_compute.
- replace n with (33+(n-33)) by lia.
  transitivity (23 + h (n - 33)). apply h_add_33.
  transitivity (23 + f 4 (n - 33)).
  specialize (IH (n-33)). lia.
  apply (f4_add_33 (n-33)).
Qed.

(** Similarly, f 4 <= f 5 *)

Lemma f4_add_73 n : 51 + f 4 n <= f 4 (73+n) <= 54 + f 4 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f5_add_73 n : 54 + f 5 n <= f 5 (73+n) <= 57 + f 5 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f4_below_f5 n : f 4 n <= f 5 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 73).
- clear IH.
  rewrite <- !fopt_spec, <- Nat.leb_le. revert n H.
  apply intvl_dec_0. now vm_compute.
- replace n with (73+(n-73)) by lia.
  transitivity (54 + f 4 (n - 73)). apply (f4_add_73 (n-73)).
  transitivity (54 + f 5 (n - 73)).
  specialize (IH (n-73)). lia.
  apply (f5_add_73 (n-73)).
Qed.

(* And f 5 <= f 6 *)

Lemma f5_add_169 n : 125 + f 5 n <= f 5 (169+n) <= 129 + f 5 n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma f6_add_169 n : 129 + f 6 n <= f 6 (169+n) <= 135 + f 6 n.
Proof.
 apply decide_additivity. lia. now vm_compute.
Qed.

Lemma f5_below_f6 n : f 5 n <= f 6 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 169).
- clear IH.
  rewrite <- !fopt_spec, <- Nat.leb_le. revert n H.
  apply intvl_dec_0. now vm_compute.
- replace n with (169+(n-169)) by lia.
  transitivity (129 + f 5 (n - 169)). apply (f5_add_169 (n-169)).
  transitivity (129 + f 6 (n - 169)).
  specialize (IH (n-169)). lia.
  apply (f6_add_169 (n-169)).
Qed.

(* And f 5 <= f 7 *)

(*
Lemma f6_add_424 n : 326 + f 6 n <= f 6 (424+n) <= 333 + f 6 n.
Proof.
 apply decide_additivity. lia. now vm_compute.
Qed.

Lemma f7_add_424 n : 333 + f 7 n <= f 7 (424+n) <= 342 + f 7 n.
Proof.
 apply decide_additivity. lia. now vm_compute.
Qed.

Lemma f6_below_f7 n : f 6 n <= f 7 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 424).
- clear IH.
  rewrite <- !fopt_spec. rewrite <- Nat.leb_le.
  do 424 (destruct n; [now vm_compute|]). exfalso. lia.
- replace n with (424+(n-424)) by lia.
  transitivity (333 + f 6 (n - 424)). apply (f6_add_424 (n-424)).
  transitivity (333 + f 7 (n - 424)).
  specialize (IH (n-424)). lia.
  apply (f7_add_424 (n-424)).
Qed.
*)

(** General proof : cf WordGrowth.f_grows *)

(** * Strict order between [f k] and [f (S k)].

    We know that [f k (quad k) = f (S k) (quad k)] thanks to
    GenG.fk_fSk_last_equality. Now for small specific values of k,
    we can show there is no more equality for [n > quad k].
*)

Lemma f1_add_2 n : f 1 (2+n) = 1 + f 1 n.
Proof.
 rewrite !f_1_div2.
 replace (S (2+n)) with (S n + 1 * 2) by lia.
 rewrite Nat.div_add; lia.
Qed.

Lemma f1_lt_g n : quad 1 < n -> f 1 n < g n.
Proof.
 unfold quad, triangle; simpl.
 induction n as [n IH] using lt_wf_ind.
 intros Hn.
 destruct (Nat.le_gt_cases n 9).
 - clear IH. rewrite <- Nat.ltb_lt.
   apply (@intvl_dec 8 9 (fun n => f 1 n <? g n)). now vm_compute. lia.
 - replace n with (2+(n-2)) by lia.
   rewrite f1_add_2.
   apply Nat.lt_le_trans with (1 + g (n - 2)).
   + specialize (IH (n-2)). lia.
   + rewrite <- !f_2_g. apply fk_add_2. lia.
Qed.

Lemma g_lt_h n : quad 2 < n -> g n < h n.
Proof.
unfold quad, triangle; simpl.
induction n as [n IH] using lt_wf_ind. intros Hn.
destruct (Nat.le_gt_cases n 20).
- clear IH. rewrite <- Nat.ltb_lt. generalize (conj Hn H). clear Hn H.
  revert n. apply intvl_dec. now vm_compute.
- clear Hn. replace n with (8+(n-8)) by lia.
  apply Nat.le_lt_trans with (5 + g (n - 8)). apply g_add_8.
  apply Nat.lt_le_trans with (5 + h (n - 8)). 2:apply h_add_8.
  specialize (IH (n-8)). lia.
Qed.

Lemma h_lt_f4 n : quad 3 < n -> h n < f 4 n.
Proof.
unfold quad, triangle; simpl.
induction n as [n IH] using lt_wf_ind. intros Hn.
destruct (Nat.le_gt_cases n (18+33)).
- clear IH. unfold h. rewrite <- !fopt_spec, <- Nat.ltb_lt.
  generalize (conj Hn H). clear Hn H. revert n.
  apply intvl_dec. now vm_compute.
- clear Hn. replace n with (33+(n-33)) by lia.
  apply Nat.le_lt_trans with (23 + h (n - 33)). apply h_add_33.
  apply Nat.lt_le_trans with (23 + f 4 (n - 33)).
  specialize (IH (n-33)). lia.
  apply (f4_add_33 (n-33)).
Qed.

Lemma f4_lt_f5 n : quad 4 < n -> f 4 n < f 5 n.
Proof.
unfold quad, triangle; simpl.
induction n as [n IH] using lt_wf_ind. intros Hn.
destruct (Nat.le_gt_cases n (25+73)).
- clear IH. rewrite <- !fopt_spec, <- Nat.ltb_lt.
  generalize (conj Hn H). clear Hn H. revert n.
  apply intvl_dec. now vm_compute.
- clear Hn. replace n with (73+(n-73)) by lia.
  apply Nat.le_lt_trans with (54 + f 4 (n - 73)). apply (f4_add_73 (n-73)).
  apply Nat.lt_le_trans with (54 + f 5 (n - 73)).
  specialize (IH (n-73)). lia.
  apply (f5_add_73 (n-73)).
Qed.

Lemma f5_lt_f6 n : quad 5 < n -> f 5 n < f 6 n.
Proof.
unfold quad, triangle; simpl.
induction n as [n IH] using lt_wf_ind. intros Hn.
destruct (Nat.le_gt_cases n (33+169)).
- clear IH. rewrite <- !fopt_spec, <- Nat.ltb_lt.
  generalize (conj Hn H). clear Hn H. revert n.
  apply intvl_dec. now vm_compute.
- clear Hn. replace n with (169+(n-169)) by lia.
  apply Nat.le_lt_trans with (129 + f 5 (n - 169)). apply (f5_add_169 (n-169)).
  apply Nat.lt_le_trans with (129 + f 6 (n - 169)).
  specialize (IH (n-169)). lia.
  apply (f6_add_169 (n-169)).
Qed.

(** Consequence : GenG.fk_fSk_conjectures and the future
    WordGrowth.f_L_conjectures can be applied for these small k.
    For instance : *)

Lemma g_lt_h' n : n<>1 -> g n < h (S n).
Proof.
 rewrite <- f_2_g. apply fk_fSk_conjectures. lia.
 intros m Hm. rewrite f_2_g. now apply g_lt_h.
Qed.

Lemma h_lt_f4' n : n<>1 -> h n < f 4 (S n).
Proof.
 now apply fk_fSk_conjectures, h_lt_f4.
Qed.

Lemma f4_lt_f5' n : n<>1 -> f 4 n < f 5 (S n).
Proof.
 now apply fk_fSk_conjectures, f4_lt_f5.
Qed.

Lemma f5_lt_f6' n : n<>1 -> f 5 n < f 6 (S n).
Proof.
 now apply fk_fSk_conjectures, f5_lt_f6.
Qed.
