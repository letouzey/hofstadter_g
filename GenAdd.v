
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

(** Some auxiliary lemmas *)

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
  | [] => None
  | a::l => Some (minlist a l, maxlist a l)
  end.

Lemma minlist_spec a l x : In x (a::l) -> minlist a l <= x.
Proof.
 induction l as [|b l IH].
 - intros [->|[ ]]. simpl. auto.
 - simpl in *. intuition; lia.
Qed.

Lemma maxlist_spec a l x : In x (a::l) -> x <= maxlist a l.
Proof.
 induction l as [|b l IH].
 - intros [->|[ ]]. simpl. auto.
 - simpl in *. intuition; lia.
Qed.

Lemma extrems_spec l a b x : In x l -> extrems l = Some (a,b) -> a<=x<=b.
Proof.
 intros IN.
 destruct l as [|n l]; try easy.
 simpl. intros [= <- <-]. split.
 now apply minlist_spec. now apply maxlist_spec.
Qed.

Definition calc_additivity k p := extrems (all_diffs k p).

Lemma decide_additivity k p a b : k<>0 ->
 calc_additivity k p = Some (a,b) ->
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

Lemma increase_bottom_decomp_k2 p :
  forall l, Delta 3 l ->
   exists l1 l1' l2,
     l = l1 ++ l2 /\
     sumA 2 l1' = p + sumA 2 l1 /\
     Below l1 (3 + invA_up 2 p) /\
     Delta 2 (l1'++l2).
Proof.
 intros l D.
 set (u := invA_up 2 p).
 assert (Hu : 0 < u).
 { unfold u, invA_up. lia. }
 destruct (cut_lt_ge u l) as (l1,l2) eqn:E.
 assert (E' := cut_app u l). rewrite E in E'.
 assert (B1 := cut_fst u l). rewrite E in B1. simpl in B1.
 assert (U := invA_up_spec 2 p).
 fold u in U.
 destruct l2 as [|a l2].
 - exists l1, (decomp 2 (p+sumA 2 l)), [].
   repeat split; auto.
   + rewrite decomp_sum. rewrite <- E', app_nil_r. auto.
   + intros x Hx. specialize (B1 x Hx). lia.
   + rewrite app_nil_r. apply Delta_S, decomp_delta.
 - assert (Ha : u <= a).
   { assert (B1' := @cut_snd u l a l2). rewrite E in B1'.
     simpl snd in B1'. specialize (B1' eq_refl). lia. }
   destruct (Nat.eq_dec a (u+2)).
   { set (l1' := decompminus 2 (l1++[S a]) (A2 (S a)-A2 a-p)).
     exists (l1++[a]), l1', l2.
     repeat split.
     * rewrite <- E'. now rewrite app_ass.
     * unfold l1'. rewrite decompminus_sum. rewrite !sumA_app.
       assert (LE : p <= A 2 (a-2)).
       { transitivity (A 2 u); auto. apply A_mono. lia. }
       clear -LE. simpl sumA. rewrite A_S. lia.
     * intro x. rewrite in_app_iff. intros [IN|[<-|[]]]; try lia.
       specialize (B1 x IN). lia.
     * { rewrite <- E', Delta_app_iff in D.
         destruct D as (D1 & D2 & D3).
         apply Delta_app with (S a).
         - apply decompminus_delta_lax.
           apply Delta_app_iff; repeat split.
           + apply Delta_S, D1.
           + constructor.
           + intros x x' Hx [<-|[]]. specialize (D3 x a Hx).
             simpl in D3. intuition.
         - now apply Delta_S_cons.
         - intro y. rewrite <- Nat.lt_succ_r. apply decompminus_below.
           intro z. rewrite in_app_iff. intros [Hz|[<-|[]]].
           + specialize (B1 z Hz). lia.
           + lia. }}
   destruct (Nat.eq_dec a (1+u)).
   { set (l1' := decompminus 2 (l1++[u;S a]) (A2 u + A2 (S a)-A2 a-p)).
     exists (l1++[a]), l1', l2.
     repeat split.
     * rewrite <- E'. now rewrite app_ass.
     * unfold l1'. rewrite decompminus_sum. rewrite !sumA_app. clear l1'.
       subst a. clearbody u. simpl. lia.
     * intro x. rewrite in_app_iff. intros [IN|[<-|[]]]; try lia.
       specialize (B1 x IN). lia.
     * { rewrite <- E', Delta_app_iff in D.
         destruct D as (D1 & D2 & D3).
         apply Delta_app with (S a).
         - apply decompminus_delta_lax.
           apply Delta_app_iff; repeat split.
           + apply Delta_S, D1.
           + constructor. lia. auto.
           + intros x x' Hx [<-|[<-|[]]].
             * specialize (D3 x a Hx). simpl in D3. intuition.
             * specialize (B1 _ Hx). lia.
         - now apply Delta_S_cons.
         - intro y. rewrite <- Nat.lt_succ_r. apply decompminus_below.
           intro z. rewrite in_app_iff. intros [Hz|[<-|[<-|[]]]].
           + specialize (B1 z Hz). lia.
           + lia.
           + lia. }}
   destruct (Nat.eq_dec a u).
   { subst a.
     set (l1' := decompminus 2 (l1++[u-1;1+u]) (A2 (2+u)-A2 u-p)).
     exists (l1++[u]), l1', l2.
     repeat split.
     * rewrite <- E'. now rewrite app_ass.
     * unfold l1'. rewrite decompminus_sum. rewrite !sumA_app. clear l1'.
       clearbody u. generalize (twice_A2_le u). simpl. lia.
     * intro x. rewrite in_app_iff. intros [IN|[<-|[]]]; try lia.
       specialize (B1 x IN). lia.
     * { rewrite <- E', Delta_app_iff in D.
         destruct D as (D1 & D2 & D3).
         apply Delta_app with (1+u).
         - apply decompminus_delta_lax.
           apply Delta_app_iff; repeat split.
           + apply Delta_S, D1.
           + constructor. lia. auto.
           + intros x x' Hx [<-|[<-|[]]].
             * specialize (D3 x u Hx). simpl in D3. intuition.
             * specialize (B1 _ Hx). lia.
         - now apply Delta_S_cons.
         - intro y. rewrite <- Nat.lt_succ_r. apply decompminus_below.
           intro z. rewrite in_app_iff. intros [Hz|[<-|[<-|[]]]].
           + specialize (B1 z Hz). lia.
           + lia.
           + lia. }}
   { set (l1' := decompminus 2 (l1++[1+u]) (A2 (1+u)-p)).
     exists l1, l1', (a::l2).
     repeat split.
     * auto.
     * unfold l1'. rewrite decompminus_sum. rewrite !sumA_app. clear l1'.
       clearbody u. simpl. lia.
     * intros x IN. specialize (B1 x IN). lia.
     * { rewrite <- E', Delta_app_iff in D.
         destruct D as (D1 & D2 & D3).
         apply Delta_app with (1+u).
         - apply decompminus_delta_lax.
           apply Delta_app_iff; repeat split.
           + apply Delta_S, D1.
           + constructor.
           + intros x x' Hx [<-|[]]. specialize (B1 _ Hx). lia.
         - constructor. lia. now apply Delta_S.
         - intro y. rewrite <- Nat.lt_succ_r. apply decompminus_below.
           intro z. rewrite in_app_iff. intros [Hz|[<-|[]]].
           + specialize (B1 z Hz). lia.
           + lia. }}
Qed.

Definition add_bound_k2 p := A2 (3 + invA_up 2 p).

Lemma additivity_bounded_k2 p :
 forall n, exists m,
   m < add_bound_k2 p /\
   h (p+n) - h n = h (p+m) - h m.
Proof.
 intros n.
 destruct (decomp_exists 2 n) as (l & E & D).
 destruct (@increase_bottom_decomp_k2 p l D)
   as (l1 & l1' & l2 & El & E1 & B1 & D1).
 exists (sumA 2 l1).
 split.
 - unfold add_bound_k2. set (q := 3+invA_up 2 p) in *. clearbody q.
   rewrite El in D. apply Delta_app_inv in D.
   rewrite <- DeltaRev_rev in D.
   rewrite <- sumA_rev.
   assert (B1r : Below (rev l1) q).
   { intro y. rewrite <- in_rev. apply B1. }
   destruct (rev l1) as [|a l1r].
   + simpl. apply A_nz.
   + apply Nat.lt_le_trans with (A2 (S a)).
     * apply decomp_max; auto. apply D.
     * apply A_mono. apply B1r. now left.
 - rewrite <- E.
   rewrite El at 1. rewrite sumA_app, Nat.add_assoc, <- E1, <- sumA_app.
   unfold h.
   rewrite !f_sumA_lax; auto using Delta_S.
   + rewrite El, !map_app, !sumA_app. lia.
   + rewrite El in D. apply Delta_app_inv in D. apply Delta_S, D.
   + apply Delta_app_inv in D1. apply D1.
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

Lemma h_add_11 n : 7 + h n <= h (11+n) <= 8 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

Lemma h_add_12 n : 7 + h n <= h (12+n) <= 9 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

(** All the earlier cases were satisfying h(p+n)-h(p)-h(n) = {-1,0,1}
    But for p=18, h(18+n) = h n + h 18 + [-2..0] *)
Lemma h_add_18 n : 11 + h n <= h (18+n) <= 13 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

(** For comparison with f 3 *)
Lemma h_add_33 n : 22 + h n <= h (33+n) <= 23 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
Qed.

(** h(39+n) = h n + h 39 + [0..2] *)
Lemma h_add_39 n : 26 + h n <= h (39+n) <= 28 + h n.
Proof.
 apply decide_additivity. auto. now vm_compute.
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
     generalize (@A_nz 2 (q-1)). unfold A2, h in *. lia. }
   clear E n.
   replace (add_bound_k2 (A2 q)) with (A2 (3+q)) in Hm.
   2:{ unfold add_bound_k2. f_equal. f_equal. rewrite invA_up_A; lia. }
   assert (D := decomp_delta 2 m).
   rewrite <- (decomp_sum 2 m). set (l := decomp 2 m) in *.
   destruct (destruct_last l) as [->|(a & l' & E)].
   + simpl. change (h 0) with 0.
     rewrite !Nat.add_0_r. unfold h. rewrite f_A. lia.
   + assert (Ha : a < 3+q).
     { apply (@A_lt_inv 2).
       rewrite <- (decomp_sum 2 m) in Hm. fold l in Hm.
       rewrite E in Hm. rewrite sumA_app in Hm. simpl sumA in Hm. lia. }
     clearbody l. subst l. clear m Hm.
     simpl in Ha. rewrite Nat.lt_succ_r, Nat.lt_eq_cases, or_comm in Ha.
     destruct Ha as [Ha|Ha].
     { (* a = q+2 *)
       clear IH.
       replace (A2 q + _) with (sumA 2 (l'++[S a])).
       2:{ rewrite !sumA_app. simpl. replace (a-2) with q; lia. }
       unfold h. rewrite !f_sumA; eauto using Delta_up_last.
       rewrite !map_app, !sumA_app. subst a; simpl. lia. }
     rewrite Nat.lt_succ_r, Nat.lt_eq_cases, or_comm in Ha.
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
       rewrite !f_sumA_lax by (try apply Delta_up_last with a; auto with arith).
       rewrite !map_app, !sumA_app. simpl.
       replace (pred a) with (a-1) by lia. lia. }
     { (* a <= q-2 *)
       clear IH.
       replace (A2 q + _) with (sumA 2 (l'++[a;q])).
       2:{ rewrite !sumA_app. simpl. lia. }
       unfold h. rewrite !f_sumA_lax; auto.
       - rewrite !map_app, !sumA_app. simpl. replace (pred q) with (q-1); lia.
       - apply Delta_app_iff in D. destruct D as (D1 & D2 & D3).
         apply Delta_app_iff; repeat split; auto.
         + constructor. lia. auto.
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
   unfold h at 1 5. rewrite f_sumA_lax; auto. simpl.
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

(** g_add_8 and h_add_8 are enough to show that g <= h *)

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

(** h_add33 and f3_add_33 imply h <= f 3 *)

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

(* TODO: Conjecture : forall k n, f k n <= f (S k) n
   Proof : ??
*)
