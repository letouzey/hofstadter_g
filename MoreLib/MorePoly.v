From Coq Require Import Arith Reals Lra Lia Permutation Morphisms.
From Hofstadter.HalfQuantum Require Import Complex Polynomial.
From Hofstadter.HalfQuantum Require FTA.
Require Import MoreList DeltaList MoreSets MoreComplex MoreSum.
Local Open Scope R.
Local Open Scope C.
Local Coercion INR : nat >-> R.
Local Open Scope poly_scope.

(** * More on QuantumLib polynomials *)

(** Some extra definitions about polynomials on C *)

Definition coef n (p : Polynomial) := nth n p 0.

Definition topcoef (p : Polynomial) := last (compactify p) 0.

Definition monom (c:C) (k:nat) := repeat 0 k ++ [c].

Definition _X_ := [0;1].

Definition Root c p := Peval p c = 0.

Definition monic p := topcoef p = 1.

Fixpoint linfactors l :=
  match l with
  | [] => [1]
  | c::l => linfactors l *, [-c;1]
  end.

(** Extra properties *)

Lemma eq_Peq p q : p = q -> p ≅ q.
Proof.
 intros ->. apply Peq_refl.
Qed.

Lemma Peq_iff p q : p ≅ q <-> compactify p = compactify q.
Proof.
 split. apply Peq_compactify_eq. apply compactify_eq_Peq.
Qed.

Lemma Pzero_alt : [0] ≅ [].
Proof.
 apply Peq_iff. apply (app_C0_compactify_reduce_1 []).
Qed.

Lemma compactify_last (p : Polynomial) :
 compactify p = [] \/ last (compactify p) 0 <> 0.
Proof.
 unfold compactify.
 induction (rev p); simpl; auto.
 destruct (Ceq_dec a 0) as [->|N]; auto.
 right. simpl. now rewrite last_last.
Qed.

Lemma prune_eqn (p : Polynomial) :
 let n := (length p - length (prune p))%nat in
 p = repeat 0 n ++ prune p.
Proof.
 induction p; cbn -[Nat.sub]; auto.
 destruct Ceq_dec as [->|N].
 - rewrite Nat.sub_succ_l. simpl. now f_equal.
   apply prune_length.
 - simpl. now rewrite Nat.sub_diag.
Qed.

Lemma compactify_eqn (p : Polynomial) :
 let n := (length p - length (compactify p))%nat in
 p = compactify p ++ repeat 0 n.
Proof.
 unfold compactify. rewrite rev_length.
 rewrite <- rev_repeat, <- rev_app_distr.
 now rewrite <- (rev_length p), <- prune_eqn, rev_involutive.
Qed.

Lemma compactify_Peq p : compactify p ≅ p.
Proof.
 apply Peq_iff, compactify_idempotent.
Qed.

Lemma Peq0_carac p : p≅[] <-> compactify p = [].
Proof.
 apply Peq_iff.
Qed.

Lemma Peq0_alt p : p≅[] <-> p = repeat 0 (length p).
Proof.
 rewrite Peq_iff. cbn.
 split.
 - intros H. rewrite (compactify_eqn p) at 1. rewrite H. simpl. f_equal. lia.
 - intros ->. apply (app_C0_compactify_reduce _ []).
Qed.

Lemma Peq0_cons c p : (c::p)≅[] <-> c=0 /\ p≅[].
Proof.
 split. apply Peq_nil_reduce. intros (->,H). rewrite H. apply Pzero_alt.
Qed.

Lemma prune_last (c:C) p :
  c<>0 \/ ~p≅[] ->
  prune (p ++ [c]) = (prune p) ++ [c].
Proof.
 induction p; simpl.
 - intros [H|H]. now destruct Ceq_dec. now destruct H.
 - intros [H|H]; destruct Ceq_dec; auto.
   subst. apply IHp. right. contradict H. rewrite H. apply Pzero_alt.
Qed.

Lemma compactify_cons_nz (c:C) p :
 ~(c::p)≅[] -> compactify (c::p) = c :: compactify p.
Proof.
 intros. unfold compactify. simpl. rewrite prune_last.
 - now rewrite rev_app_distr.
 - rewrite Peq0_cons in H.
   destruct (Ceq_dec c 0); auto.
   + right. contradict H. split; auto. rewrite Peq0_alt in H.
     rewrite rev_length in H. rewrite <- (rev_involutive p), H.
     rewrite rev_repeat. apply Peq0_alt. now rewrite repeat_length.
Qed.

Lemma Pplus_coef n p q : coef n (p +, q) = coef n p + coef n q.
Proof.
 revert n q.
 unfold coef.
 induction p; destruct q, n; simpl; auto; try ring.
Qed.

Lemma coef_monom c n m : coef n (monom c m) = if n =? m then c else 0.
Proof.
 unfold coef, monom.
 destruct (Nat.compare_spec n m); case Nat.eqb_spec; try lia; intros _.
 - subst. rewrite app_nth2; rewrite repeat_length; try lia.
   now rewrite Nat.sub_diag.
 - rewrite app_nth1, nth_repeat; rewrite ?repeat_length; trivial.
 - rewrite nth_overflow; trivial. rewrite app_length, repeat_length. simpl.
   lia.
Qed.

Lemma Psum_coef (f : nat -> Polynomial) (p n : nat) :
 coef p (big_sum f n) = big_sum (fun i : nat => coef p (f i)) n.
Proof.
 induction n; simpl. now destruct p. now rewrite Pplus_coef, IHn.
Qed.

Lemma compactify_coef n (p : Polynomial) :
 coef n (compactify p) = coef n p.
Proof.
 rewrite (compactify_eqn p) at 2.
 set (m := (_ - _)%nat). clearbody m.
 unfold coef.
 destruct (Nat.lt_ge_cases n (length (compactify p))).
 - now rewrite app_nth1.
 - rewrite app_nth2 by trivial. rewrite nth_overflow by trivial.
   symmetry. apply nth_repeat.
Qed.

Lemma coef_compat n (p q : Polynomial) : p ≅ q -> coef n p = coef n q.
Proof.
 intros E. apply Peq_compactify_eq in E.
 rewrite <- (compactify_coef n p), <- (compactify_coef n q). now f_equal.
Qed.

Global Instance : Proper (eq ==> Peq ==> eq) coef.
Proof.
 intros n n' <-. exact (coef_compat n).
Qed.

Global Instance : Proper (Peq ==> eq) topcoef.
Proof.
 intros p q E. unfold topcoef. now rewrite E.
Qed.

Lemma Pscale_coef c P n : coef n ([c] *, P) = c * coef n P.
Proof.
 unfold Pmult. rewrite Pzero_alt, Pplus_0_r. unfold coef.
 apply map_nth'. lca.
Qed.

Lemma topcoef_alt p : topcoef p = coef (degree p) p.
Proof.
 unfold degree, topcoef, coef. rewrite last_nth. apply compactify_coef.
Qed.

Lemma topcoef_0_iff p : topcoef p = 0 <-> p ≅ [].
Proof.
 split.
 - rewrite Peq0_carac. unfold topcoef. now destruct (compactify_last p).
 - now intros ->.
Qed.

Lemma topcoef_nz (p : Polynomial) :
 ~ p ≅ [] -> topcoef p <> 0.
Proof.
 intros H. contradict H. now apply topcoef_0_iff.
Qed.

Lemma coef_after_degree n p : (degree p < n)%nat -> coef n p = 0.
Proof.
 unfold degree. rewrite <- (compactify_Peq p) at 2.
 intros H.
 unfold coef. apply nth_overflow. lia.
Qed.

Lemma degree_length (p : Polynomial) : (degree p <= length p -1)%nat.
Proof.
 unfold degree. generalize (compactify_length p); lia.
Qed.

Lemma compactify_monom (c:C) k : c<>0 -> compactify (monom c k) = monom c k.
Proof.
 intros Hc.
 unfold monom, compactify.
 rewrite rev_app_distr. simpl.
 destruct (Ceq_dec c 0) as [->|N]. easy.
 simpl. now rewrite rev_involutive.
Qed.

Lemma monom_degree (c:C) k : c<>0 -> degree (monom c k) = k.
Proof.
 intros Hc. unfold degree. rewrite compactify_monom by trivial.
 unfold monom. rewrite app_length, repeat_length. simpl. lia.
Qed.

Lemma monom_nz (c:C) k : c<>0 -> ~monom c k ≅ [].
Proof.
 intros Hc E.
 apply Peq_compactify_eq in E. rewrite compactify_monom in E by trivial.
 unfold monom in E. destruct k; now simpl in E.
Qed.

Lemma monom_eval (c x:C) k : Peval (monom c k) x = c * x ^ k.
Proof.
 unfold monom. rewrite mul_by_x_to_n. cbn. ring.
Qed.

Lemma Pconst_eval c x : Peval [c] x = c.
Proof.
 cbn. lca.
Qed.

Lemma topcoef_monom c k : topcoef (monom c k) = c.
Proof.
 destruct (Ceq_dec c 0); subst.
 - unfold monom, topcoef.
   rewrite app_C0_compactify_reduce_1.
   change (repeat 0 k) with ([]++repeat 0 k).
   now rewrite app_C0_compactify_reduce.
 - unfold topcoef. rewrite compactify_monom; auto.
   unfold monom. apply last_last.
Qed.

Lemma Pscale_alt c p : [c] *, p ≅ List.map (Cmult c) p.
Proof.
 apply cons_singleton_mult.
Qed.

Lemma monom_scale c k : monom c k ≅ [c] *, monom 1 k.
Proof.
 unfold monom. rewrite Pscale_alt, map_app. simpl.
 apply Peq_iff. f_equal. f_equal.
 now rewrite map_repeat, Cmult_0_r.
 f_equal. lca.
Qed.

Lemma Pmult_X (p:Polynomial) : _X_ *, p ≅ 0::p.
Proof.
 simpl.
 rewrite <- Pscale_alt.
 rewrite Pzero_alt. simpl. rewrite Pplus_0_r.
 rewrite <- Pscale_alt.
 now rewrite Pmult_1_l.
Qed.

Lemma Pmult_repeat0_alt k p q :
 (repeat 0 k ++ p) *, q ≅ repeat 0 k ++ (p *, q).
Proof.
 induction k; simpl; try easy.
 rewrite IHk.
 rewrite <- (Pscale_alt 0 q), Pzero_alt. simpl. easy.
Qed.

Lemma Pmult_monom_coef n c k p : (k <= n)%nat ->
 coef n (monom c k *, p) = c * coef (n-k) p.
Proof.
 intros H. unfold monom. rewrite Pmult_repeat0_alt.
 unfold coef at 1. rewrite app_nth2; rewrite repeat_length; trivial.
 change (nth _ _ _) with (coef (n-k) ([c] *, p)).
 rewrite Pscale_alt. unfold coef. apply map_nth'. lca.
Qed.

Lemma coef_P0 k : coef k [] = 0.
Proof.
 now destruct k.
Qed.

Lemma Pmult_coef p q n:
 coef n (p*,q) = big_sum (fun k => coef k p * coef (n-k) q) (S n).
Proof.
 revert q n.
 induction p; intros.
 - simpl. rewrite coef_P0. rewrite big_sum_0. lca.
   intros k. rewrite coef_P0. lca.
 - simpl. rewrite <- Pscale_alt, Pplus_coef, Pscale_coef.
   replace (n-n)%nat with O by lia.
   destruct n as [|n]. unfold coef; simpl; lca.
   change (coef (S n) (0 :: _)) with (coef n (p*,q)).
   change (coef (S n) (a::p)) with (coef n p).
   rewrite IHp.
   symmetry. rewrite big_sum_shift. rewrite <- big_sum_extend_r.
   change (coef 0 (a::p)) with a.
   replace (n-n)%nat with O by lia.
   change Gplus with Cplus. rewrite Nat.sub_0_r. ring_simplify.
   rewrite <- !Cplus_assoc. f_equal. apply Cplus_comm.
Qed.

Lemma Popp_coef n p : coef n (-, p) = - coef n p.
Proof.
 change (-, p) with (monom (- (1)) 0 *, p).
 rewrite Pmult_monom_coef by lia. rewrite Nat.sub_0_r. ring.
Qed.

Lemma Pconst_nonzero (c:C) : c<>0 -> ~[c]≅[].
Proof.
 intros Hc. change [c] with (monom c 0). now apply monom_nz.
Qed.

Lemma Pscale_degree (c:C) p : c<>0 -> degree ([c] *, p) = degree p.
Proof.
 intros Hc.
 destruct (Peq_0_dec p) as [->|N].
 - simpl. now rewrite Pzero_alt.
 - rewrite Pmult_degree; auto.
   + change [c] with (monom c 0). now rewrite monom_degree.
   + now apply Pconst_nonzero.
Qed.

Lemma Popp_degree p : degree (-, p) = degree p.
Proof.
 apply Pscale_degree, Copp_neq_0_compat, C1_nz.
Qed.

Lemma Peval_compactify p c : Peval (compactify p) c = Peval p c.
Proof.
 rewrite (compactify_eqn p) at 2.
 set (n := Nat.sub _ _). clearbody n.
 rewrite app_eval_to_mul.
 generalize (mul_by_x_to_n [] n c). rewrite app_nil_r. intros ->.
 cbn. ring.
Qed.

Global Instance : Proper (Peq ==> eq ==> eq) Peval.
Proof.
 intros p p' Hp c c' <-.
 rewrite <- (Peval_compactify p c), <- (Peval_compactify p' c).
 now rewrite Hp.
Qed.

Global Instance : Proper (eq ==> Peq ==> iff) Root.
Proof.
 intros c c' <- p p' Hp. unfold Root. now rewrite Hp.
Qed.

Lemma Peq_via_coef q r : Peq q r <-> forall n, coef n q = coef n r.
Proof.
 split.
 - intros E n. now rewrite E.
 - intros E. apply Peq_iff.
   assert (E' : forall n, coef n (compactify q) = coef n (compactify r)).
   { intros n. rewrite !compactify_coef. apply E. }
   clear E.
   apply nth_ext with (d:=0) (d':=0); [|intros; apply E'].
   destruct (compactify_last q) as [Hq|Hq], (compactify_last r) as [Hr|Hr].
   + now rewrite Hq, Hr.
   + exfalso. rewrite Hq in E'. rewrite last_nth in Hr.
     unfold coef in E'. rewrite <- E' in Hr.
     now destruct (length _-1)%nat in Hr.
   + exfalso. rewrite Hr in E'. rewrite last_nth in Hq.
     unfold coef in E'. rewrite E' in Hq.
     now destruct (length _-1)%nat in Hq.
   + destruct (Nat.compare_spec (length (compactify q))
                                (length (compactify r)));
      trivial || exfalso.
     * apply Hr. rewrite last_nth. unfold coef in E'.
       rewrite <- E'. apply nth_overflow. lia.
     * apply Hq. rewrite last_nth. unfold coef in E'.
       rewrite E'. apply nth_overflow. lia.
Qed.

Lemma Pmult_Peq_reg_l (p q r : Polynomial) :
 ~(p ≅ []) -> p *, q ≅ p *, r -> q ≅ r.
Proof.
 intros N E.
 destruct (Peq_dec q r) as [E2|N2]; trivial. exfalso.
 apply (Pmult_neq_0 p (q +, -,r)); trivial.
 - change (~(q +, -, r ≅ [])). contradict N2.
   rewrite <- (Pplus_0_r r), <- N2.
   rewrite <- Pplus_assoc, (Pplus_comm r), Pplus_assoc, Pplus_opp_r.
   now rewrite Pplus_0_r.
 - change (p *, (q +, -,r) ≅ []).
   rewrite Pmult_plus_distr_l, E.
   unfold Popp. rewrite <- Pmult_assoc, (Pmult_comm _ [_]), Pmult_assoc.
   apply Pplus_opp_r.
Qed.

Lemma Pmult_Peq_reg_r (p q r : Polynomial) :
 ~(r ≅ []) -> p *, r ≅ q *, r -> p ≅ q.
Proof.
 intros R. rewrite !(Pmult_comm _ r). now apply Pmult_Peq_reg_l.
Qed.

Lemma Pplus_map (f g : nat -> C) l (p q : Polynomial) :
   (map f l ++ p) +, (map g l ++ q) ≅ map (fun k => f k + g k) l ++ (p +, q).
Proof.
 induction l; simpl. easy. now rewrite IHl.
Qed.

Lemma Pplus_map' (f g : nat -> C) l (p : Polynomial) :
   (map f l) +, (map g l ++ p) ≅ map (fun k => f k + g k) l ++ p.
Proof.
 rewrite <- (app_nil_r (map f l)). now rewrite Pplus_map.
Qed.

(** Euclidean division of polynomial *)

Fixpoint Pdiv_loop a b d :=
 match d with
 | 0 => ([],a)
 | S d' =>
   if (degree a <? degree b)%nat then
     ([], a)
   else
     let k := (degree a - degree b)%nat in
     let c := topcoef a / topcoef b in
     let '(q,r) := Pdiv_loop (a +, -, (monom c k *, b)) b d' in
     (q +, monom c k, r)
 end.

Definition Pdiv a b := Pdiv_loop a b (degree a).

Lemma Pdiv_eqn a b :
  Peq a (fst (Pdiv a b) *, b +, snd (Pdiv a b)).
Proof.
 unfold Pdiv. remember (degree a) as d. clear Heqd.
 revert a b.
 induction d; simpl; intros; try easy.
 case Nat.ltb_spec; intros. simpl; easy.
 set (k := (degree a - degree b)%nat).
 set (c := topcoef a / topcoef b).
 set (a' := a +, _).
 specialize (IHd a' b). destruct (Pdiv_loop a' b d) as (q,r).
 simpl in *. rewrite Pmult_plus_distr_r.
 rewrite Pplus_assoc, (Pplus_comm _ r), <- Pplus_assoc, <- IHd.
 unfold a'. rewrite Pplus_assoc, Pplus_opp_l.
 simpl. now rewrite Pplus_0_r.
Qed.

Lemma Pdiv_degree a b :
  (0 < degree b)%nat -> (degree (snd (Pdiv a b)) < degree b)%nat.
Proof.
 intros Hb. revert a.
 assert (forall d a, (degree a <= d)%nat ->
                     (degree (snd (Pdiv_loop a b d)) < degree b)%nat).
 { induction d; simpl; intros a D; try lia.
   case Nat.ltb_spec; [intros LE|intros LT]; trivial.
   set (top_a := topcoef a).
   set (top_b := topcoef b).
   set (k := (degree a - degree b)%nat).
   set (c := top_a / top_b).
   set (a' := a +, _).
   specialize (IHd a'). destruct (Pdiv_loop a' b d) as (q,r).
   simpl in *. apply IHd.
   assert (NZa : ~ a ≅ []).
   { intro H. rewrite H in LT. change (degree []) with O in LT. lia. }
   assert (NZb : ~ b ≅ []).
   { intro H. now rewrite H in Hb. }
   assert (NZ : top_a / top_b <> 0).
   { apply Cmult_neq_0. now apply topcoef_nz.
     apply nonzero_div_nonzero. now apply topcoef_nz. }
   assert (LE : (degree a' <= degree a)%nat).
   { unfold a'. etransitivity. eapply Pplus_degree1.
     rewrite Popp_degree, Pmult_degree, monom_degree. auto; try lia.
     apply NZ. now apply monom_nz. auto. }
   assert (Ha' : coef (degree a) a' = 0).
   { unfold a'. rewrite Pplus_coef. rewrite <- topcoef_alt. fold top_a.
     rewrite Popp_coef, Pmult_monom_coef by lia.
     replace (degree a - k)%nat with (degree b) by lia.
     rewrite <- topcoef_alt. fold top_b. unfold c. field.
     now apply topcoef_nz. }
   destruct (Nat.eq_dec (degree a') 0) as [E0|N0]; try lia.
   destruct (Nat.eq_dec (degree a') (degree a)) as [E|N]; try lia.
   rewrite <- E in Ha'. rewrite <- topcoef_alt in Ha'.
   apply topcoef_nz in Ha'; try lia.
   intro H. rewrite H in N0. now apply N0. }
 intros. now apply H.
Qed.

Lemma degree_is_1 (c c':C) : c'<>0 -> degree [c;c'] = 1%nat.
Proof.
 unfold degree, compactify. simpl. now destruct Ceq_dec.
Qed.

Lemma Pfactor_root p c : Root c p -> { q | p ≅ q *, [-c;1] }.
Proof.
 intros H.
 assert (D : degree [-c; 1] = 1%nat).
 { apply degree_is_1. apply C1_nz. }
 assert (E := Pdiv_eqn p [-c;1]).
 assert (LT := Pdiv_degree p [-c;1]).
 destruct (Pdiv p [-c;1]) as (q & r). simpl in *. rewrite D in LT.
 specialize (LT ltac:(lia)).
 exists q.
 assert (D' : degree r = O) by lia. clear D LT.
 rewrite <- (compactify_Peq r) in E. unfold degree in D'.
 destruct (compactify r) as [|c0 [|c1 s] ].
 - now rewrite Pplus_0_r in E.
 - rewrite E in H. red in H. rewrite Pplus_eval, Pmult_eval in H. cbn in H.
   ring_simplify in H. rewrite H in E. rewrite Pzero_alt in E.
   now rewrite Pplus_0_r in E.
 - now simpl in D'.
Qed.

Lemma linfactors_coef_after l n :
 (length l < n)%nat -> coef n (linfactors l) = 0.
Proof.
 revert n.
 induction l; simpl; intros n Hn.
 - unfold coef. now rewrite nth_overflow.
 - rewrite Pmult_comm. simpl. rewrite Pplus_coef.
   rewrite Pzero_alt, Pplus_0_r.
   unfold coef in *.
   rewrite map_nth' with (d':=0) by lca. rewrite IHl by lia. simpl.
   destruct n; try ring.
   rewrite map_nth' with (d':=0) by lca. rewrite IHl by lia. lca.
Qed.

Lemma linfactors_coef l : coef (length l) (linfactors l) = 1.
Proof.
 induction l; simpl; auto.
 rewrite Pmult_comm. simpl. rewrite Pplus_coef.
 rewrite Pzero_alt, Pplus_0_r.
 unfold coef in *.
 rewrite map_nth' with (d':=0) by lca.
 fold (coef (S (length l)) (linfactors l)).
 rewrite linfactors_coef_after by lia. simpl. ring_simplify.
 rewrite map_nth' with (d':=0) by lca. rewrite IHl. lca.
Qed.

Lemma linfactors_nz l : ~ linfactors l ≅ [].
Proof.
 intros H.
 destruct (nth_in_or_default (length l) (linfactors l) 0) as [H'|H'].
 - fold (coef (length l) (linfactors l)) in H'.
   rewrite linfactors_coef in H'. apply C1_nz.
   apply (Peq_nil_contains_C0 _ H 1 H').
 - apply C1_nz. rewrite <- (linfactors_coef l). unfold coef.
   now rewrite H'.
Qed.

Lemma linfactors_degree l : degree (linfactors l) = length l.
Proof.
 induction l; simpl.
 - change [1] with (monom 1 0). apply monom_degree. apply C1_nz.
 - rewrite Pmult_degree, IHl.
   rewrite degree_is_1. lia. apply C1_nz.
   apply linfactors_nz.
   change (~[-a;1]≅[]). intros H. apply Peq_compactify_eq in H. cbn in H.
   destruct Ceq_dec. now apply C1_nz. easy.
Qed.

Lemma degree_cons c p :
 degree (c::p) = if Peq_0_dec p then O else S (degree p).
Proof.
 unfold degree.
 destruct Peq_0_dec as [->|N].
 - cbn. destruct Ceq_dec; auto.
 - rewrite compactify_cons_nz. simpl.
   assert (O <> length (compactify p)); try lia.
   rewrite Peq0_carac in N. contradict N. now destruct (compactify p).
   rewrite Peq0_cons; intuition.
Qed.

Lemma topcoef_cons c p :
 topcoef (c::p) = if Peq_0_dec p then c else topcoef p.
Proof.
 unfold topcoef.
 destruct Peq_0_dec as [Z|N].
 - rewrite Z. cbn. destruct Ceq_dec; auto.
 - rewrite compactify_cons_nz. simpl.
   rewrite Peq0_carac in N. now destruct (compactify p).
   rewrite Peq0_cons; intuition.
Qed.

Lemma topcoef_plus_ltdeg p q :
 (degree p < degree q)%nat -> topcoef (p +, q) = topcoef q.
Proof.
 revert q.
 induction p; destruct q; simpl; auto.
 - inversion 1.
 - rewrite !degree_cons.
   rewrite !topcoef_cons.
   destruct (Peq_0_dec q). inversion 1.
   destruct (Peq_0_dec p) as [Hp|Hp];
   destruct (Peq_0_dec (p+,q)) as [Hpq|Hpq].
   + rewrite Hp in Hpq. cbn in Hpq. easy.
   + intros _. now rewrite Hp.
   + intros H. assert (E : p ≅ -, q).
     { generalize (Pplus_eq_compat _ _ _ _ Hpq (Peq_refl (-,q))).
       rewrite Pplus_assoc, Pplus_opp_r.
       now rewrite Pplus_0_r. }
     rewrite E, Popp_degree in H. lia.
   + intros LT. apply IHp. lia.
Qed.

Lemma topcoef_mult p q : topcoef (p *, q) = topcoef p * topcoef q.
Proof.
 unfold topcoef.
 destruct (Peq_0_dec p) as [->|Hp]. cbn. ring.
 destruct (Peq_0_dec q) as [->|Hq]. cbn. rewrite Pmult_0_r. cbn. ring.
 rewrite <- compactify_Pmult; auto.
 rewrite Peq0_carac in Hp, Hq.
 apply app_removelast_last with (d:=0) in Hp, Hq.
 set (p' := removelast (compactify p)) in *.
 set (q' := removelast (compactify q)) in *.
 set (a := last (compactify p) 0) in *.
 set (b := last (compactify q) 0) in *.
 rewrite Hp, Hq.
 destruct (Pmult_leading_terms a b p' q') as (r & -> & _).
 now rewrite last_last.
Qed.

Lemma topcoef_singl c : topcoef [c] = c.
Proof.
 cbn. destruct Ceq_dec; simpl; auto.
Qed.

Lemma topcoef_lin a b : a<>0 -> topcoef [b;a] = a.
Proof.
 intros. cbn. destruct Ceq_dec; easy.
Qed.

Lemma deg0_monic_carac p : degree p = O -> monic p -> p ≅ [1].
Proof.
 intros D M.
 apply Peq_iff.
 change [1] with (monom 1 0). rewrite compactify_monom by apply C1_nz.
  unfold monom; simpl.
 unfold monic, topcoef, degree in *.
 destruct (compactify p) as [|a [|b q] ]; simpl in *; subst; try easy.
 now destruct C1_nz.
Qed.

Lemma All_roots p : monic p -> exists l, p ≅ linfactors l.
Proof.
 remember (degree p) as d eqn:H. revert p H.
 induction d.
 - exists []. simpl. apply deg0_monic_carac; auto.
 - intros p D M.
   destruct (FTA.Fundamental_Theorem_Algebra p) as (c & Hc); try lia.
   destruct (Pfactor_root p c Hc) as (q & Hq).
   assert (degree q = d).
   { destruct (Peq_0_dec q) as [Hq0|Hq0].
     - rewrite Hq0 in Hq. simpl in Hq. now rewrite Hq in D.
     - rewrite Hq in D. rewrite Pmult_degree in D; auto.
       rewrite degree_is_1 in D. lia. apply C1_nz.
       change (~[-c;1]≅[]). rewrite Peq0_carac. cbn.
       destruct Ceq_dec; try easy. now destruct C1_nz. }
   assert (monic q).
   { unfold monic in *. rewrite Hq, topcoef_mult in M.
     rewrite topcoef_lin in M by apply C1_nz.
     now rewrite Cmult_1_r in M. }
   destruct (IHd q) as (l & Hl); try easy.
   exists (c::l). now rewrite Hq, Hl.
Qed.

Lemma linfactors_app l1 l2 :
 linfactors (l1++l2) ≅ linfactors l1 *, linfactors l2.
Proof.
 induction l1; cbn [linfactors app].
 - now rewrite Pmult_1_l.
 - now rewrite IHl1, !Pmult_assoc, (Pmult_comm (linfactors l2)).
Qed.

Lemma linfactors_monic l : monic (linfactors l).
Proof.
 unfold monic.
 induction l; simpl.
 - apply topcoef_singl.
 - rewrite topcoef_mult, IHl, topcoef_lin. lca. apply C1_nz.
Qed.

Lemma linfactors_roots l c : In c l <-> Root c (linfactors l).
Proof.
 revert c. induction l; unfold Root in *; cbn [linfactors In].
 - intros c. cbn. rewrite Cmult_1_r, Cplus_0_l. split. easy. apply C1_nz.
 - intros c. rewrite IHl, Pmult_eval, Cmult_integral. clear IHl.
   cbn. rewrite Cplus_0_l, !Cmult_1_r, Cmult_1_l.
   split; destruct 1 as [A|B]; auto.
   + right. subst. ring.
   + left. symmetry. apply Ceq_minus. now rewrite Cplus_comm in B.
Qed.

(** In [linfactors] we can freely permute the roots *)

Lemma linfactors_perm l l' :
 Permutation l l' -> linfactors l ≅ linfactors l'.
Proof.
 induction 1; cbn [linfactors]; try easy.
 - now rewrite IHPermutation.
 - now rewrite !Pmult_assoc, (Pmult_comm [_;_]).
 - now rewrite IHPermutation1, IHPermutation2.
Qed.

Lemma linfactors_perm_iff l l' :
 linfactors l ≅ linfactors l' <-> Permutation l l'.
Proof.
 split; [|apply linfactors_perm].
 revert l'.
 induction l; intros l'.
 - simpl. intros E. replace l' with (@nil C); try easy.
   symmetry. rewrite <- length_zero_iff_nil.
   rewrite <- linfactors_degree, <- E.
   generalize (degree_length [1]); simpl; lia.
 - simpl. intros E.
   assert (IN : In a l').
   { rewrite linfactors_roots, <- E. red. rewrite Pmult_eval.
     replace (Peval [-a;1] a) with 0; lca. }
   destruct (in_split _ _ IN) as (l1 & l2 & ->).
   apply Permutation_cons_app. apply IHl.
   rewrite linfactors_app in *. simpl in E. rewrite <- Pmult_assoc in E.
   apply Pmult_Peq_reg_r in E; trivial.
   rewrite <- topcoef_0_iff, topcoef_lin; intros [= ?]; lra.
Qed.

Lemma extra_roots_implies_null p l :
 NoDup l -> (forall r, In r l -> Root r p) ->
 (degree p < length l)%nat ->
 p ≅ [].
Proof.
 intros ND IN LT.
 rewrite <- topcoef_0_iff.
 destruct (Ceq_dec (topcoef p) 0) as [E|N]; trivial. exfalso.
 set (a := topcoef p) in *.
 set (p' := [/a] *, p).
 assert (D : degree p' = degree p).
 { apply Pscale_degree. now apply nonzero_div_nonzero. }
 assert (M : monic p').
 { unfold monic. rewrite topcoef_alt, D. unfold p'.
   rewrite Pscale_alt. unfold coef.
   rewrite map_nth' with (d':=0) by lca.
   change (/a * (coef (degree p) p) = 1). rewrite <- topcoef_alt.
   apply Cinv_l, N. }
 destruct (All_roots _ M) as (l', E').
 assert (length l <= length l')%nat.
 { apply NoDup_incl_length; trivial.
   intros r Hr. rewrite linfactors_roots, <- E'.
   apply IN in Hr. unfold Root, p' in *.
   now rewrite Pmult_eval, Hr, Cmult_0_r. }
 rewrite <- (linfactors_degree l'), <- E', D in H. lia.
Qed.

(** derivative of a polynomial *)

Fixpoint Pdiff p :=
 match p with
 | [] => []
 | c::p => p +, (0::Pdiff p)
 end.

Lemma Pdiff_compactify p : Pdiff (compactify p) ≅ Pdiff p.
Proof.
 induction p.
 - now cbn.
 - simpl. rewrite <- IHp.
   destruct (Peq_0_dec (a::p)) as [E|N].
   + rewrite E. apply Peq0_cons in E. destruct E as (E1,E2).
     rewrite E2. cbn. symmetry. apply Pzero_alt.
   + rewrite compactify_cons_nz by trivial. simpl.
     now rewrite compactify_Peq at 1.
Qed.

Global Instance : Proper (Peq ==> Peq) Pdiff.
Proof.
 intros p p' H. apply Peq_compactify_eq in H.
 now rewrite <- (Pdiff_compactify p), <- (Pdiff_compactify p'), H.
Qed.

Lemma Pdiff_plus p q : Pdiff (p+,q) ≅ Pdiff p +, Pdiff q.
Proof.
 revert q.
 induction p; simpl; try easy.
 destruct q; simpl. now rewrite Pplus_0_r.
 rewrite IHp. rewrite (Pplus_assoc p (0::Pdiff p)), <- (Pplus_assoc _ q).
 rewrite (Pplus_comm (_::_) q), !Pplus_assoc.
 simpl. now rewrite Cplus_0_l.
Qed.

Lemma Pdiff_scale c p : Pdiff ([c] *, p) ≅ [c] *, Pdiff p.
Proof.
 induction p; simpl; try easy.
 rewrite Pzero_alt, !Pplus_0_r, <- !Pscale_alt, IHp.
 rewrite Pmult_plus_distr_l. apply Pplus_eq_compat; try easy.
 simpl. now rewrite Pzero_alt, !Pplus_0_r, Cmult_0_r, Cplus_0_l.
Qed.

Lemma Pdiff_mult p q : Pdiff (p*,q) ≅ Pdiff p *, q +, p *, Pdiff q.
Proof.
 revert q.
 induction p; simpl; intros; try easy.
 rewrite Pdiff_plus. simpl. rewrite <- !Pscale_alt.
 rewrite IHp, !Pdiff_scale.
 rewrite Pmult_plus_distr_r.
 rewrite <- Pplus_assoc, (Pplus_comm _ (p*,q)), !Pplus_assoc.
 apply Pplus_eq_compat; try easy.
 rewrite <- Pplus_assoc, (Pplus_comm _ ([a]*,_)), !Pplus_assoc.
 apply Pplus_eq_compat; try easy.
 cbn. rewrite <- Pscale_alt. rewrite Pzero_alt. simpl.
 now rewrite Cplus_0_l.
Qed.

Lemma Pdiff_opp p : Pdiff (-, p) ≅ -, Pdiff p.
Proof.
 unfold Popp. apply Pdiff_scale.
Qed.

Lemma Pdiff_linfactors_repeat (c:C)(n:nat) :
 Pdiff (linfactors (repeat c (S n))) ≅
    [RtoC (S n)] *, linfactors (repeat c n).
Proof.
 induction n.
 - cbn [repeat linfactors].
   rewrite Pmult_1_l. simpl. rewrite !Cplus_0_r, Cmult_1_l.
   apply compactify_eq_Peq. apply (app_C0_compactify_reduce_1 [1]).
 - set (n' := S n) in *.
   cbn [repeat linfactors].
   rewrite Pdiff_mult, IHn. clear IHn.
   rewrite Pmult_assoc.
   change (linfactors (repeat c n) *, _) with (linfactors (repeat c n')).
   set (lin := linfactors _).
   rewrite !S_INR, !RtoC_plus.
   change [n'+1] with (Pplus [RtoC n'] [1]).
   rewrite Pmult_plus_distr_r.
   apply Pplus_eq_compat; try easy. clearbody lin.
   rewrite Pmult_comm. apply Pmult_eq_compat; try easy.
   cbn.
   rewrite !Cplus_0_r.
   apply compactify_eq_Peq. apply (app_C0_compactify_reduce_1 [1]).
Qed.

Lemma monom_S a k : monom a (S k) = 0 :: monom a k.
Proof.
 now unfold monom.
Qed.

Lemma diff_monom a k : Pdiff (monom a k) ≅ [RtoC k] *, monom a (pred k).
Proof.
 induction k.
 - simpl. now rewrite Cmult_0_l, Cplus_0_l.
 - simpl pred.
   rewrite monom_S, S_INR, RtoC_plus. cbn -[Pmult]. rewrite IHk.
   change [k+1] with (Pplus [RtoC k] [1]).
   rewrite Pmult_plus_distr_r.
   rewrite Pmult_1_l. rewrite Pplus_comm. apply Pplus_eq_compat; try easy.
   destruct k.
   + simpl. rewrite !Cmult_0_l, !Cplus_0_l.
     apply compactify_eq_Peq. apply (app_C0_compactify_reduce_1 [0]).
   + cbn [pred]. rewrite monom_S. cbn -[INR].
     now rewrite Cmult_0_r, Cplus_0_l, Pzero_alt, !Pplus_0_r.
Qed.

(** A multiple root of a polynomial is also a root of its derivative. *)

Lemma multiple_root_diff (l : list C) c :
  (1 < count_occ Ceq_dec l c)%nat -> Root c (Pdiff (linfactors l)).
Proof.
 intros Hc. unfold Root.
 set (n := count_occ Ceq_dec l c) in *.
 rewrite (linfactors_perm _ _ (movefront_perm Ceq_dec c l)).
 unfold movefront. fold n. set (l' := remove Ceq_dec c l). clearbody l'.
 rewrite linfactors_app, Pdiff_mult, Pplus_eval, !Pmult_eval.
 assert (E : forall m, (0<m)%nat -> Root c (linfactors (repeat c m))).
 { intros. rewrite <- linfactors_roots. destruct m. lia. now left. }
 rewrite E by lia.
 assert (E' : Root c (Pdiff (linfactors (repeat c n)))).
 { destruct n as [|n]; try lia. unfold Root.
   rewrite Pdiff_linfactors_repeat, Pmult_eval, E by lia. apply Cmult_0_r. }
 unfold Root in E'.
 now rewrite E', !Cmult_0_l, Cplus_0_l.
Qed.

(** A polynomial without common roots with its derivative has only
    simple roots. First, version for [linfactors] polynomials. *)

Lemma linfactors_separated_roots (l : list C) :
 (forall c, Root c (linfactors l) -> ~Root c (Pdiff (linfactors l))) -> NoDup l.
Proof.
 intros.
 apply (NoDup_count_occ' Ceq_dec).
 intros c Hc.
 assert (Hc' := Hc). rewrite (count_occ_In Ceq_dec) in Hc'.
 destruct (Nat.eq_dec (count_occ Ceq_dec l c) 1). trivial.
 apply linfactors_roots in Hc. specialize (H c Hc).
 destruct H. apply multiple_root_diff. lia.
Qed.

(** A polynomial without common roots with its derivative has only
    simple roots. Version for monic polynomial. *)

Lemma separated_roots f :
 monic f ->
 (forall c, Root c f -> ~Root c (Pdiff f)) ->
 exists l, NoDup l /\ f ≅ linfactors l.
Proof.
 intros Hf Df.
 destruct (All_roots f Hf) as (l & E).
 exists l; split; trivial.
 apply linfactors_separated_roots. intros c. rewrite <- E. apply Df.
Qed.

(** Product of a list of polynomial *)

Definition Plistsum (l : list Polynomial) := fold_right Pplus [] l.

Lemma Plistsum_mult_r {A} (f:A->Polynomial) l p :
  Plistsum (map f l) *, p ≅ Plistsum (map (fun x => f x *, p) l).
Proof.
 induction l; simpl; trivial. easy.
 rewrite Pmult_plus_distr_r.
 apply Pplus_eq_compat. easy. apply IHl.
Qed.

Lemma Peval_Plistsum (l:list Polynomial) c :
  Peval (Plistsum l) c = Clistsum (map (fun P => Peval P c) l).
Proof.
 induction l; simpl; now rewrite ?Pplus_eval, ?IHl.
Qed.

Lemma Pdiff_linfactors l :
  Pdiff (linfactors l) ≅
  Plistsum (map (fun i => linfactors (remove_at i l)) (seq 0 (length l))).
Proof.
 induction l; simpl.
 - apply (last_C0_Peq_front []).
 - rewrite Pdiff_mult. simpl. rewrite Cplus_0_r.
   rewrite <- seq_shift, map_map. simpl.
   rewrite Pplus_comm. apply Pplus_eq_compat.
   + now rewrite (last_C0_Peq_front [1]), Pmult_1_r.
   + rewrite IHl. apply Plistsum_mult_r.
Qed.

Lemma Peval_linfactors c l :
  Peval (linfactors l) c = G_big_mult (map (fun y => c-y) l).
Proof.
 induction l.
 - simpl. unfold Peval. simpl. lca.
 - simpl. rewrite Pmult_eval, IHl, Cmult_comm. f_equal.
   unfold Peval; simpl. lca.
Qed.

Lemma Peval_Pdiff_linfactors l i :
  NoDup l -> (i < length l)%nat ->
  Peval (Pdiff (linfactors l)) (l@i)
  = G_big_mult (map (fun y => l@i - y) (remove_at i l)).
Proof.
 intros Hl Hi.
 assert (Hl' := remove_at_length l i Hi).
 rewrite <- Peval_linfactors.
 rewrite Pdiff_linfactors, Peval_Plistsum, map_map.
 rewrite Clistsum_map with (d:=O).
 rewrite big_sum_kronecker with (m:=i).
 - now rewrite seq_nth.
 - now rewrite seq_length.
 - intros j Hj Hij. rewrite seq_length in Hj.
   rewrite seq_nth by trivial. simpl.
   change (Root (l@i) (linfactors (remove_at j l))).
   rewrite <- linfactors_roots. now apply remove_at_In.
Qed.

Definition reciprocal p := rev (compactify p).

Global Instance : Proper (Peq ==> eq) reciprocal.
Proof.
 intros p q E. unfold reciprocal. apply Peq_iff in E. now f_equal.
Qed.

Lemma reciprocal_coef p i : (i <= degree p)%nat ->
  coef i (reciprocal p) = coef (degree p - i) p.
Proof.
 unfold coef, reciprocal, degree.
 intros Hi.
 destruct (Nat.eq_dec (length (compactify p)) 0) as [E|N].
 - rewrite length_zero_iff_nil in E. rewrite E in *. simpl in *.
   replace i with O by lia.
   change (0 = coef 0 p). now rewrite <- compactify_coef, E.
 - set (n := length (compactify p)) in *.
   rewrite rev_nth by lia.
   replace (length _ - S i)%nat with (n-1-i)%nat by lia.
   apply compactify_coef.
Qed.

Lemma reciprocal_coef_0 p i :
  (degree p < i)%nat -> coef i (reciprocal p) = 0.
Proof.
 intros H. unfold reciprocal, coef.
 apply nth_overflow. rewrite rev_length. unfold degree in *. lia.
Qed.

Lemma reciprocal_degree q :
 coef 0 q <> 0 -> degree (reciprocal q) = degree q.
Proof.
 intros H.
 unfold degree, reciprocal. unfold compactify at 1.
 rewrite rev_involutive, rev_length.
 rewrite <- compactify_coef in H.
 destruct (compactify q) as [|x l]; simpl; try easy.
 unfold coef in H; simpl in H. now destruct Ceq_dec.
Qed.

Lemma Peval_rev_aux l x : x<>0 ->
  Peval (rev l) x * x = Peval l (/x) * x^length l.
Proof.
 intros Hx. induction l as [|a l IH].
 - cbn. lca.
 - simpl.
   rewrite app_eval_to_mul, rev_length, Pconst_eval, cons_eval.
   rewrite !Cmult_plus_distr_r, IH. now field.
Qed.

Lemma Peval_rev l x : x<>0 -> l<>[] ->
  Peval (rev l) x = Peval l (/x) * x^(length l - 1).
Proof.
 intros Hx Hl.
 apply Cmult_eq_reg_r with x; trivial.
 rewrite Peval_rev_aux; trivial. rewrite <- Cmult_assoc.
 f_equal. rewrite <- length_zero_iff_nil in Hl.
 replace (length l) with (S (length l - 1)) at 1 by lia. simpl. ring.
Qed.

Lemma Peval_reciprocal p x : x<>0 -> ~Peq p [] ->
  Peval (reciprocal p) x = Peval p (/x) * x^degree p.
Proof.
 intros Hx Hp.
 rewrite <- (Peval_compactify p). unfold reciprocal, degree.
 apply Peval_rev; trivial. contradict Hp. rewrite <- Hp.
 symmetry. apply compactify_Peq.
Qed.

Lemma Peval_reciprocal_0 p : Peval (reciprocal p) 0 = topcoef p.
Proof.
 unfold Peval, reciprocal, topcoef.
 rewrite rev_length.
 destruct (compactify p) as [|a q] eqn:E; try easy.
 simpl length.
 rewrite <- big_sum_extend_l.
 rewrite big_sum_0.
 2:{ intros x. simpl. lca. }
 rewrite (@app_removelast_last _ (a::q) 0) at 1; try easy.
 rewrite rev_app_distr. simpl. ring.
Qed.

Lemma reciprocal_root p x :
  x<>0 -> Root x (reciprocal p) <-> Root (/x) p.
Proof.
 intros Hx.
 destruct (Ceq_dec (topcoef p) 0) as [Y|N].
 - rewrite topcoef_0_iff in Y. unfold reciprocal. now rewrite Y.
 - rewrite topcoef_0_iff in N. unfold Root.
   rewrite Peval_reciprocal; trivial.
   split.
   + intros H. apply Cmult_integral in H. destruct H; trivial.
     now apply (Cpow_nz x (degree p)) in Hx.
   + intros ->. lca.
Qed.

Definition revfactors l := linfactors (map Cinv l).

Lemma Peval_revfactors l x :
  ~In 0 l -> x<>0 ->
  Peval (revfactors l) (/x) =
  Peval (revfactors l) 0 * Peval (linfactors l) x / x^length l.
Proof.
 unfold revfactors.
 induction l; intros Hl Hx.
 - simpl. rewrite !Pconst_eval. lca.
 - simpl. rewrite !Pmult_eval, IHl; trivial.
   2:{ contradict Hl. now right. }
   unfold Cdiv. rewrite !Cinv_mult.
   rewrite <- !Cmult_assoc. f_equal.
   rewrite (Cmult_comm (Peval _ 0)).
   rewrite <- !Cmult_assoc. f_equal.
   rewrite !(Cmult_comm (/ x^length l)).
   rewrite !Cmult_assoc. f_equal.
   rewrite !cons_eval. change (Peval [] _) with 0.
   field. split; trivial. contradict Hl. now left.
Qed.

Lemma revfactors_at_0 l :
 ~In 0 l -> Peval (revfactors l) 0 * Peval (linfactors l) 0 = 1.
Proof.
 induction l.
 - intros _. unfold revfactors. simpl. rewrite Pconst_eval. lca.
 - simpl. intros Hl.
   unfold revfactors. simpl. rewrite !Pmult_eval.
   change (linfactors (map _ _)) with (revfactors l).
   rewrite (Cmult_comm (Peval (revfactors l) 0)).
   rewrite Cmult_assoc, <- (Cmult_assoc (Peval [_;_] 0)).
   rewrite IHl by tauto.
   rewrite !cons_eval, !Cmult_0_l, !Cplus_0_r. field. tauto.
Qed.

Lemma reciprocal_revfactors l :
 ~In 0 l ->
 Peq (reciprocal (linfactors l))
     ([Peval (linfactors l) 0] *, revfactors l).
Proof.
 intros Hl.
 apply almost_Peq_implies_Peq. intros x Hx.
 rewrite Peval_reciprocal; trivial.
 2:{ rewrite <- topcoef_0_iff. rewrite linfactors_monic.
     intros [=H]; lra. }
 rewrite Pmult_eval, Pconst_eval.
 rewrite <- (Cinv_inv x) at 3.
 rewrite Peval_revfactors; trivial.
 2:{ now apply nonzero_div_nonzero. }
 rewrite linfactors_degree, Cpow_inv.
 unfold Cdiv. rewrite Cinv_inv. rewrite Cmult_assoc. f_equal.
 rewrite Cmult_assoc, (Cmult_comm (Peval _ 0)), revfactors_at_0; trivial.
 lca.
Qed.

(** Partial fraction decomposition for 1/P when P has simple roots *)

Module PartFrac.

Definition coef l i := / G_big_mult (map (fun r => l@i - r) (remove_at i l)).

Lemma coef_nz l i : NoDup l -> (i < length l)%nat -> coef l i <> 0.
Proof.
 intros Hl Hi.
 apply nonzero_div_nonzero.
 rewrite <- Peval_linfactors.
 change (~Root (l@i) (linfactors (remove_at i l))).
 rewrite <- linfactors_roots.
 apply remove_at_notIn; trivial.
Qed.

Lemma inv_linfactors (l:list C) : l<>[] -> NoDup l ->
 forall x, ~In x l ->
 Cinv (Peval (linfactors l) x) =
  big_sum (fun i => coef l i / (x - l@i)) (length l).
Proof.
 intros Hl0 Hl x Hx.
 symmetry. apply Cinv_eq.
 rewrite (@big_sum_mult_r _ _ _ _ C_is_ring).
 rewrite big_sum_eq_bounded with
     (g := fun i => Peval ([coef l i] *, linfactors (remove_at i l)) x).
 2:{ intros i Hi. rewrite Pmult_eval. simpl. rewrite Pconst_eval.
     unfold Cdiv. rewrite <- Cmult_assoc. f_equal.
     rewrite (linfactors_perm l (l@i :: remove_at i l)).
     2:{ unfold Cnth. now rewrite remove_at_permut. }
     simpl. rewrite Pmult_eval. rewrite cons_eval, Pconst_eval. field.
     rewrite <- Ceq_minus. contradict Hx. subst. now apply nth_In. }
 rewrite <- Psum_eval.
 rewrite Ceq_minus. unfold Cminus. rewrite <- (Pconst_eval (-(1)) x).
 rewrite <- Pplus_eval.
 rewrite (extra_roots_implies_null _ l); trivial.
 - intros r Hr. destruct (In_nth l r 0 Hr) as (i & Hi & E).
   red. rewrite Pplus_eval, Pconst_eval, Psum_eval.
   rewrite big_sum_kronecker with (m:=i); trivial.
   + rewrite Pmult_eval, Pconst_eval, Peval_linfactors, <- E.
     unfold coef. rewrite Cinv_l; try lca.
     rewrite <- (Cinv_inv (G_big_mult _)). apply nonzero_div_nonzero.
     now apply coef_nz.
   + intros j Hj Hij. rewrite Pmult_eval.
     apply Cmult_integral. right.
     change (Root r (linfactors (remove_at j l))).
     rewrite <- linfactors_roots, <- E.
     apply remove_at_In; trivial.
 - set (p := big_sum _ _).
   assert (degree p <= pred (length l))%nat.
   { apply Psum_degree.
     intros i Hi.
     rewrite Pscale_degree by now apply coef_nz.
     now rewrite linfactors_degree, remove_at_length. }
   generalize (Pplus_degree1 p [-(1)]).
   generalize (degree_length [-(1)]). simpl.
   rewrite <- length_zero_iff_nil in Hl0. lia.
Qed.

End PartFrac.

(** Binomial formula *)

Lemma binomial_formula (x y:C) n:
 (x+y)^n = big_sum (fun k => binom n k * x^k * y^(n-k)) (S n).
Proof.
 set (F := fun n k => binom n k * x^k * y^(n-k)).
 change ((x+y)^n = big_sum (F n) (S n)).
 induction n.
 - simpl. lca.
 - cbn - [big_sum]. rewrite IHn. clear IHn.
   rewrite Cmult_plus_distr_r.
   rewrite !big_sum_Cmult_l.
   rewrite (big_sum_shift (S n)), (big_sum_shift n (fun _ => y * _)).
   rewrite big_sum_eq_bounded with
     (f:=fun k => F _ _ ) (g:=fun k => (x * F n k + y * F n (S k))%G).
   2:{ intros k Hk. unfold F. simpl.
       rewrite plus_INR, RtoC_plus.
       destruct (Nat.eq_dec k n) as [->|Hk'].
       - rewrite (binom_zero n (S n)) by lia. simpl. ring.
       - replace (n - k)%nat with (S (n-S k))%nat by lia. simpl. ring. }
   rewrite big_sum_Cplus.
   rewrite (Cplus_comm (F (S n) O)), <-Cplus_assoc.
   f_equal. simpl. rewrite Cplus_comm, <- Cplus_assoc. f_equal.
   unfold F. simpl.
   rewrite Nat.sub_0_r, binom_one, binom_zero by lia. simpl. ring.
Qed.

(** ** Elementary symmetric functions *)

Definition sigma k (l:list C) := Clistsum (map G_big_mult (nsubsets k l)).

Lemma sigma_rec k x l :
 sigma (S k) (x::l) = x * sigma k l + sigma (S k) l.
Proof.
 unfold sigma. simpl nsubsets.
 rewrite map_app, map_map, Clistsum_app. f_equal.
 now rewrite Clistsum_factor_l, map_map.
Qed.

Lemma sigma_0 l : sigma 0 l = 1.
Proof.
 unfold sigma. destruct l; simpl; lca.
Qed.

Lemma sigma_1 l : sigma 1 l = Clistsum l.
Proof.
 induction l; try easy. rewrite sigma_rec, sigma_0, IHl. simpl; ring.
Qed.

Lemma sigma_len l : sigma (length l) l = G_big_mult l.
Proof.
 unfold sigma. rewrite nsubsets_all. simpl. lca.
Qed.

Lemma sigma_null k l : (length l < k)%nat -> sigma k l = 0.
Proof.
 unfold sigma. intros H. now rewrite nsubsets_empty.
Qed.

Lemma sigma_cons_0 k l : sigma k (0::l) = sigma k l.
Proof.
 destruct k. now rewrite !sigma_0. rewrite sigma_rec. ring.
Qed.

Lemma sigma_extend k p l : sigma k (repeat 0 p ++ l) = sigma k l.
Proof.
 induction p. trivial. simpl. now rewrite sigma_cons_0.
Qed.

Lemma sigma_app k (l1 l2 : list C) :
 sigma k (l1++l2) =
 big_sum (fun i => sigma i l1 * sigma (k-i) l2) (S k).
Proof.
 revert k.
 induction l1; intros k.
 - rewrite big_sum_shift. simpl. rewrite sigma_0, Nat.sub_0_r.
   rewrite big_sum_0; simpl; try ring.
   intros x. rewrite sigma_null; try ring. simpl; lia.
 - simpl app.
   destruct k.
   + simpl; rewrite !sigma_0. ring.
   + rewrite sigma_rec.
     rewrite big_sum_shift. rewrite sigma_0, Nat.sub_0_r.
     erewrite big_sum_eq_bounded.
     2:{ intros x Hx.
         now rewrite sigma_rec, Cmult_plus_distr_r, <- Cmult_assoc. }
     rewrite big_sum_Cplus, <- big_sum_Cmult_l.
     simpl Nat.sub. rewrite <- IHl1.
     rewrite (IHl1 (S k)).
     rewrite big_sum_shift. simpl Nat.sub. rewrite sigma_0.
     simpl; ring.
Qed.

Lemma sigma_perm k l l' : Permutation l l' -> sigma k l = sigma k l'.
Proof.
 intros H. revert k. induction H; trivial; try congruence.
 - destruct k.
   + now rewrite !sigma_0.
   + rewrite !sigma_rec. f_equal;[f_equal|]; apply IHPermutation.
 - destruct k as [|[|k]].
   + now rewrite !sigma_0.
   + rewrite !sigma_rec, !sigma_0. ring.
   + rewrite !sigma_rec. ring.
Qed.

(** Writing a polynomial in term of symmetric functions of its roots *)

Lemma linfactors_sigma (l:list C) :
 let n := length l in
 linfactors l ≅ map (fun k => (-1)^(n-k) * sigma (n-k) l) (seq 0 (S n)).
Proof.
 induction l.
 - simpl. rewrite sigma_0. apply eq_Peq. f_equal; lca.
 - cbn -[Cmult Cpow sigma Nat.sub seq].
   set (n := length l) in *. cbn zeta in IHl. rewrite IHl. clear IHl.
   remember (S n) as n' eqn:E in *. rewrite seq_S.
   rewrite map_app. simpl. replace (n'-n')%nat with O by lia.
   rewrite sigma_0.
   rewrite Pmult_comm.
   simpl Pmult. rewrite !map_map, C0_Peq_nil, Pplus_0_r.
   symmetry.
   rewrite map_ext_in with
       (g := fun k => -a * ((-1)^(n-k) * sigma (n-k) l)
                      + (-1)^(n'-k) * sigma (n'-k) l).
   2:{ intros k Hk.
       rewrite in_seq in Hk. replace (n'-k)%nat with (S (n-k)) by lia.
       rewrite sigma_rec. simpl. ring. }
   rewrite <- Pplus_map'. f_equiv.
   replace (seq 0 n') with (seq 0 (S n)) by (f_equal; lia).
   rewrite seq_S at 2. rewrite map_app. simpl.
   apply eq_Peq. f_equal; [|f_equal].
   + rewrite sigma_null. lca. lia.
   + rewrite <- seq_shift, map_map, E. simpl. apply map_ext.
     intros k. now rewrite Cmult_1_l.
   + rewrite Nat.sub_diag, sigma_0. simpl. f_equal. lca.
Qed.

Lemma linfactors_coefs (l:list C) n k :
  length l = n -> (k <= n)%nat ->
  coef k (linfactors l) = (-1)^(n-k) * sigma (n-k) l.
Proof.
 intros E LE. rewrite linfactors_sigma. rewrite E.
 unfold coef. rewrite nth_map_indep with (d':=O).
 2:{ rewrite seq_length. lia. }
 now rewrite seq_nth by lia.
Qed.

(** ** Newton functions (sums of powers) and newton identities *)

Definition newton_sum k l := Clistsum (map (fun r => Cpow r k) l).

Lemma newton_sum_0 l : newton_sum 0 l = length l.
Proof.
 unfold newton_sum. induction l. trivial.
 simpl in *. rewrite IHl. destruct (length l); lca.
Qed.

Lemma newton_sum_1 l : newton_sum 1 l = Clistsum l.
Proof.
 unfold newton_sum. f_equal. simpl.
 erewrite map_ext. 2:{ intros. apply Cmult_1_r. }
 apply map_id.
Qed.

Lemma newton_sum_cons k x l : newton_sum k (x::l) = x^k + newton_sum k l.
Proof.
 reflexivity.
Qed.

Lemma newton_sum_extend k p l : k<>O ->
 newton_sum k (repeat 0 p ++ l) = newton_sum k l.
Proof.
 intros Hk.
 induction p. trivial. simpl. rewrite newton_sum_cons, IHp.
 destruct k. easy. simpl. ring.
Qed.

Lemma newton_identities k l :
 sigma k l * k =
 big_sum (fun i => (-1)^i * sigma (k-S i) l * newton_sum (S i) l) k.
Proof.
 revert k. induction l; intros k.
 - destruct k. simpl; ring.
   rewrite sigma_null by (simpl; lia). rewrite big_sum_0; try lca.
   intros i. unfold newton_sum. simpl. ring.
 - destruct k; [simpl; lca|].
   set (sgn := fun i => (-1)^i) in *.
   rewrite <- big_sum_extend_r. change Gplus with Cplus.
   rewrite Nat.sub_diag. rewrite sigma_0.
   rewrite newton_sum_cons.
   erewrite big_sum_eq_bounded.
   2:{ intros i Hi.
       replace (S k-S i)%nat with (S (k-S i)) by lia.
       rewrite sigma_rec. replace (S (k-S i)) with (S k-S i)%nat by lia.
       rewrite newton_sum_cons.
       rewrite 2 Cmult_plus_distr_l, 2 Cmult_plus_distr_r, Cplus_assoc.
       rewrite (Cmult_comm a) at 1.
       rewrite <- 2 Cmult_assoc.
       replace (a*a^S i) with (a^(S (S i))) by (simpl; ring).
       rewrite Cmult_assoc.
       rewrite (Cmult_assoc _ a), (Cmult_comm _ a), <- 2 (Cmult_assoc a).
       reflexivity. }
   rewrite 3 big_sum_Cplus.
   set (f1 := fun i => _).
   set (f2 := fun i => _).
   set (f3 := fun i => _).
   set (f4 := fun i => _).
   assert (E := IHl (S k)). fold f4 in E.
   simpl big_sum in E.
   replace (big_sum f4 k) with (sigma (S k) l * S k - f4 k)
     by (rewrite E; ring).
   unfold f4. rewrite Nat.sub_diag, sigma_0. clear E f4.
   replace (big_sum f2 k) with (big_sum f2 (S k) +(- f2 k)) by (simpl; ring).
   rewrite big_sum_shift. rewrite (Cplus_comm (f2 O)).
   rewrite !Cplus_assoc.
   rewrite <- big_sum_Cplus, big_sum_0_bounded; simpl 0%G.
   2:{ intros i Hi. unfold f1, f2. simpl. unfold sgn; simpl; ring. }
   unfold f2. clear f1 f2.
   rewrite Nat.sub_diag, sigma_0.
   simpl Cpow. simpl Nat.sub. rewrite Nat.sub_0_r, S_INR, RtoC_plus.
   unfold sgn. symmetry. rewrite Ceq_minus. rewrite sigma_rec. ring_simplify.
   unfold f3. rewrite <- big_sum_Cmult_l. rewrite <- IHl. ring.
Qed.

Lemma newton_identities_nosigma l :
 sigma 1 l = 1 -> (forall p, (1<p<length l)%nat -> sigma p l = 0) ->
 forall p, (1<=p<length l)%nat -> newton_sum p l = 1.
Proof.
 intros H1 H0 p Hp.
 induction p as [|[|p] IH]; try easy.
 - rewrite newton_sum_1. now rewrite <- sigma_1.
 - assert (E := newton_identities (S (S p)) l).
   rewrite H0, Cmult_0_l in E; try lia.
   cbn -[Nat.sub] in E.
   rewrite Nat.sub_diag, sigma_0 in E.
   replace (S (S p) - S p)%nat with 1%nat in E by lia. rewrite H1 in E.
   rewrite big_sum_0_bounded in E.
   2:{ intros i Hi. rewrite H0 by lia. simpl. ring. }
   rewrite IH in E by lia. simpl in E.
   replace (RtoC (-1)) with (-(1)) in E by lca.
   rewrite Cplus_0_l, <- !Copp_mult_distr_l, Cmult_1_l in E.
   symmetry in E. apply Cminus_eq_0 in E.
   rewrite <- !Cmult_assoc in E. apply Cmult_eq_reg_l in E.
   now rewrite !Cmult_1_l in E.
   apply Cpow_nz. intros [= E' _]. revert E'. lra.
Qed.
