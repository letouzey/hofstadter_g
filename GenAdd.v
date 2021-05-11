
Require Import Arith Lia List Bool.
Require Import DeltaList FunG GenFib GenG.
Import ListNotations.
Set Implicit Arguments.

(** Study of quasi-additivity for [f k n] function defined in [GenG]:
    [f k (p+n)] is close to [f k p + f k n].
    Said otherwise, for some fixed p, few values are reached by
    [f k (p+n)-f k n] when n varies.
    For this study, we'll turn a strict k-decomposition of n into
    a lax decomp of (p+n).
*)

Lemma rev_inj {A} (l l' : list A) : rev l = rev l' -> l = l'.
Proof.
 intros. now rewrite <- (rev_involutive l), H, rev_involutive.
Qed.

Lemma rev_switch {A} (l l' : list A) : rev l = l' -> l = rev l'.
Proof.
 intros. now rewrite <- (rev_involutive l), H.
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
   transitivity a; auto. eapply Delta_le; eauto.
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
   apply Delta_app_iff. repeat split; auto using decomp_delta.
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
     rewrite Delta_app_iff. repeat split; auto.
     eapply Delta_up_last with a; auto. rewrite <- E'; auto.
     intros x x' IN IN'.
     rewrite in_app_iff in IN. destruct IN as [IN|[<-|[ ]]].
     * specialize (D3 x x').
       rewrite E', in_app_iff in D3.
       specialize (D3 (or_introl IN) IN'). lia.
     * specialize (D3 a x').
       rewrite E', in_app_iff in D3.
       specialize (D3 (or_intror (or_introl eq_refl)) IN'). lia.
   + apply decompminus_app_delta.
     rewrite <- app_assoc. apply Delta_app_iff; repeat split; auto.
     * rewrite Delta_app_iff; repeat split; auto.
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
 destruct (rev low) as [|a rlow'] eqn:E''.
 - apply rev_switch in E''. subst low. simpl.
   generalize (@A_nz k (bound_idx k p)). lia.
 - rewrite <- sumA_rev, E''.
   apply Nat.lt_le_trans with (A k (S a)).
   + apply decomp_max. rewrite <- E''. now apply DeltaRev_rev.
   + apply A_mono. specialize (B a).
     rewrite in_rev, E'' in B. simpl in B. intuition.
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
 rewrite !f_sumA_lax; auto.
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

Definition all_diffs k p :=
  let stk := ftabulate k (p + (add_bound k p - 1)) in
  map2 Nat.sub stk (npop p stk).

Lemma all_diffs_spec k p :
  all_diffs k p =
  map (fun x => f k (p+x)-f k x) (countdown (add_bound k p - 1)).
Proof.
 unfold all_diffs.
 set (m := add_bound _ _ - 1). clearbody m.
 rewrite ftabulate_spec.
 rewrite npop_map.
 replace p with ((p+m)-m) at 2 by lia.
 rewrite npop_countdown by lia.
 induction m.
 - simpl. destruct p; simpl; auto. f_equal. now destruct countdown.
 - rewrite Nat.add_succ_r. simpl. f_equal; auto.
Qed.

Definition check_additivity test k p :=
  forallb test (all_diffs k p).

Lemma check_additivity_spec test k p : k<>0 ->
  check_additivity test k p = true ->
  forall n, test (f k (p+n)-f k n) = true.
Proof.
 intros Hk E. unfold check_additivity in E.
 rewrite forallb_forall in E.
 intros n. destruct (@additivity_bounded k p Hk n) as (m & Hm & ->).
 apply E. rewrite all_diffs_spec.
 rewrite in_map_iff. exists m. split; auto.
 rewrite countdown_in. lia.
Qed.

Lemma decide_additivity k p a b : k<>0 ->
 check_additivity (fun m => andb (a <=? m) (m <=? b)) k p = true ->
 forall n, a + f k n <= f k (p+n) <= b + f k n.
Proof.
 intros.
 assert (f k n <= f k (p+n)) by (apply f_mono; lia).
 assert (a <= f k (p+n) - f k n <= b); try lia.
 { rewrite <- !Nat.leb_le.
   rewrite <- andb_true_iff.
   change ((fun m => andb (a <=? m) (m <=? b)) (f k (p+n)-f k n) = true).
   clear H1. revert n.
   apply check_additivity_spec; auto. }
Qed.


(** Particular case of function H, i.e. k=2 *)

Definition h := f 2.

Lemma h_add_1 n : h n <= h (1+n) <= 1 + h n.
Proof.
 unfold h. destruct (f_step 2 n); simpl; lia.
Qed.

Lemma h_add_2 n : 1 + h n <= h (2+n) <= 2 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma h_add_3 n : 1 + h n <= h (3+n) <= 3 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma h_add_4 n : 2 + h n <= h (4+n) <= 3 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma h_add_5 n : 3 + h n <= h (5+n) <= 4 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma h_add_6 n : 3 + h n <= h (6+n) <= 5 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma h_add_7 n : 4 + h n <= h (7+n) <= 6 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma h_add_8 n : 5 + h n <= h (8+n) <= 6 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma h_add_9 n : 5 + h n <= h (9+n) <= 7 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma h_add_10 n : 6 + h n <= h (10+n) <= 8 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

(* h(18+n) = h n + h 18 + [-2..0] *)
Lemma h_add_18 n : 11 + h n <= h (18+n) <= 13 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

(* For comparison with f 3 *)
Lemma h_add_33 n : 22 + h n <= h (33+n) <= 23 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

(* h(39+n) = h n + h 39 + [0..2] *)
Lemma h_add_39 n : 26 + h n <= h (39+n) <= 28 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

(* TODO: experimentally, h(n+m)-h(n)-h(m) is in [-2..2] in general
         and in [-1..1] when m is a [A 2] number.
   Proof: ??
*)

(* Combined with g_add_8, h_add_8 is enough to show that g <= h *)

Lemma g_below_h n : g n <= h n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 8).
- do 8 (destruct n; [compute; auto|]). lia.
- replace n with (8+(n-8)) by lia.
  transitivity (5 + g (n - 8)). apply g_add_8.
  transitivity (5 + h (n - 8)). 2:apply h_add_8.
  specialize (IH (n-8)). lia.
Qed.

(* TODO: g_below_h can be generalized into :
   Conjecture : forall k n, f k n <= f (S k) n
   Proof : ??
*)

(* f 3 *)

Lemma fk_add_1 k n : f k n <= f k (1+n) <= 1 + f k n.
Proof.
 unfold h. destruct (f_step k n); simpl; lia.
Qed.

Lemma fk_add_2 k n : 1 + f k n <= f k (2+n) <= 2 + f k n.
Proof.
 unfold h. split.
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

Lemma h_below_f3 n : h n <= f 3 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 33).
- clear IH.
  unfold h. rewrite <- !fopt_spec.
  do 33 (destruct n; [vm_compute; auto|]). exfalso. lia.
- replace n with (33+(n-33)) by lia.
  transitivity (23 + h (n - 33)). apply h_add_33.
  transitivity (23 + f 3 (n - 33)).
  specialize (IH (n-33)). lia.
  apply (f3_add_33 (n-33)).
Qed.

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
