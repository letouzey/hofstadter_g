
From Coq Require Import Arith Reals Lra Lia Permutation Morphisms.
From QuantumLib
 Require Import Complex Polynomial Matrix VecSet Eigenvectors FTA.

Local Open Scope C.
Local Open Scope poly_scope.

(** Complement about C. TODO move elsewhere *)
Lemma Cinv0 : Cinv 0 = 0.
Proof.
 compute. f_equal; ring.
Qed.

Lemma Cmult_integral (c1 c2 : C) :
 (c1 * c2 = 0 <-> c1 = 0 \/ c2 = 0)%C.
Proof.
 split.
 - destruct (Ceq_dec c1 0) as [->|H1]. now left.
   destruct (Ceq_dec c2 0) as [->|H2]. now right.
   intros H. now destruct (Cmult_neq_0 c1 c2).
 - intros [-> | ->]; ring.
Qed.

Lemma Cminus_eq (c1 c2 : C) : c1 = c2 <-> c1 - c2 = C0.
Proof.
 split; intros.
 - subst. ring.
 - destruct (Ceq_dec c1 c2) as [->|N]. trivial.
   now apply Cminus_eq_contra in N.
Qed.


(** Some extra definitions about polynomials on C *)

Definition coef n (p : Polynomial) := nth n p C0.

Definition topcoef (p : Polynomial) := last (compactify p) C0.

Definition monom (c:C) (k:nat) := repeat C0 k ++ [c].

Definition Root c p := p[[c]] = C0.

Definition monic p := topcoef p = C1.

Definition monicify p := [/topcoef p] *, p.

Fixpoint linfactors l :=
  match l with
  | [] => [C1]
  | c::l => linfactors l *, [-c;C1]
  end.

(** Extra properties *)

Lemma Peq_iff p q : p ≅ q <-> compactify p = compactify q.
Proof.
 split. apply Peq_compactify_eq. apply compactify_eq_Peq.
Qed.

Lemma Pzero_alt : [C0] ≅ [].
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
 p = repeat C0 n ++ prune p.
Proof.
 induction p; cbn -[Nat.sub]; auto.
 destruct Ceq_dec as [->|N].
 - rewrite Nat.sub_succ_l. simpl. now f_equal.
   apply prune_length.
 - simpl. now rewrite Nat.sub_diag.
Qed.

Lemma compactify_eqn (p : Polynomial) :
 let n := (length p - length (compactify p))%nat in
 p = compactify p ++ repeat C0 n.
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

Lemma Peq0_alt p : p≅[] <-> p = repeat C0 (length p).
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

Lemma Peq0_carac' p : p≅[] <-> Forall (eq C0) p.
Proof.
 induction p.
 - intuition.
 - rewrite Peq0_cons, IHp. clear IHp. intuition.
   now inversion H. now inversion H.
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

Lemma last_nth {A}(l : list A) d :
 last l d = nth (length l - 1) l d.
Proof.
 induction l as [|x [|y l] IH]; simpl; auto.
 destruct l; simpl; auto.
Qed.

Global Instance : Proper (Peq ==> eq) topcoef.
Proof.
 intros p q E. unfold topcoef. now rewrite E.
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
 ~ p ≅ [] -> topcoef p <> C0.
Proof.
 intros H. contradict H. now apply topcoef_0_iff.
Qed.

Lemma topcoef_0 : topcoef [] = C0.
Proof.
 easy.
Qed.

Lemma coef_after_degree n p : (degree p < n)%nat -> coef n p = C0.
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

Lemma monom_eval (c x:C) k : (monom c k)[[x]] = c * x ^ k.
Proof.
 unfold monom. rewrite mul_by_x_to_n. cbn. ring.
Qed.

Lemma Pscale_alt c p : [c] *, p ≅ List.map (Cmult c) p.
Proof.
 apply cons_singleton_mult.
Qed.

Lemma Pmult_repeat0_alt k p q :
 (repeat C0 k ++ p) *, q ≅ repeat C0 k ++ (p *, q).
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
 rewrite Pscale_alt. unfold coef.
 replace C0 with (c * 0) at 1 by lca. apply map_nth.
Qed.

Lemma Popp_coef n p : coef n (-, p) = - coef n p.
Proof.
 change (-, p) with (monom (- C1) 0 *, p).
 rewrite Pmult_monom_coef by lia. rewrite Nat.sub_0_r. ring.
Qed.

Lemma Popp_alt p : -, p ≅ List.map Copp p.
Proof.
 unfold Popp. rewrite Pscale_alt. apply compactify_eq_Peq. f_equal.
 apply map_ext. intros. ring.
Qed.

Lemma Pconst_nonzero (c:C) : c<>C0 -> ~[c]≅[].
Proof.
 intros Hc. change [c] with (monom c 0). now apply monom_nz.
Qed.

Lemma Pscale_degree (c:C) p : c<>C0 -> degree ([c] *, p) = degree p.
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
 apply Pscale_degree, Copp_neq_0_compat, C1_neq_C0.
Qed.

Lemma Peval_compactify p c : (compactify p)[[c]] = p[[c]].
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

(* Euclidean division of polynomial *)

Lemma Pdiv (a b : Polynomial) :
  (0 < degree b)%nat ->
  { q & { r | a ≅ q *, b +, r /\ (degree r < degree b)%nat}}.
Proof.
 intros Hb.
 remember (degree a) as n eqn:Ha. revert a Ha.
 induction n as [n IH] using lt_wf_rec.
 intros a Ha.
 destruct (Nat.ltb (degree a) (degree b)) eqn:LT.
 - apply Nat.ltb_lt in LT.
   exists [], a. simpl; split; [easy | lia].
 - apply Nat.ltb_ge in LT.
   set (k := (degree a - degree b)%nat).
   set (top_a := topcoef a).
   set (top_b := topcoef b).
   assert (NZa : ~ a ≅ []).
   { intro H. rewrite H in LT. change (degree []) with O in LT. lia. }
   assert (NZb : ~ b ≅ []).
   { intro H. now rewrite H in Hb. }
   assert (NZ : top_a / top_b <> C0).
   { apply Cmult_neq_0. now apply topcoef_nz.
     apply nonzero_div_nonzero. now apply topcoef_nz. }
   set (a' := a +, -, (monom (top_a/top_b) k *, b)).
   assert (LE : (degree a' <= degree a)%nat).
   { unfold a'. etransitivity. eapply Pplus_degree1.
     rewrite Popp_degree, Pmult_degree, monom_degree; auto; try lia.
     now apply monom_nz. }
   assert (Ha' : coef (degree a) a' = C0).
   { unfold a'. rewrite Pplus_coef. rewrite <- topcoef_alt. fold top_a.
     rewrite Popp_coef, Pmult_monom_coef by lia.
     replace (degree a - k)%nat with (degree b) by lia.
     rewrite <- topcoef_alt. fold top_b. field. now apply topcoef_nz. }
   assert (LT' : (degree a' < n)%nat).
   { destruct (Nat.eq_dec (degree a') 0) as [E0|N0]; try lia.
     destruct (Nat.eq_dec (degree a') (degree a)) as [E|N]; try lia.
     rewrite <- E in Ha'. rewrite <- topcoef_alt in Ha'.
     apply topcoef_nz in Ha'; try lia.
     intro H. rewrite H in N0. now apply N0. }
   destruct (IH (degree a') LT' a' eq_refl) as (q & r & E & LTr).
   exists (q +, monom (top_a / top_b) k), r.
   split; trivial.
   rewrite Pmult_plus_distr_r.
   rewrite Pplus_assoc, (Pplus_comm _ r), <- Pplus_assoc.
   rewrite <- E. unfold a'. rewrite Pplus_assoc, Pplus_opp_l, Pplus_0_r.
   easy.
Qed.

Lemma degree_is_1 (c c':C) : c'<>0 -> degree [c;c'] = 1%nat.
Proof.
 unfold degree, compactify. simpl. now destruct Ceq_dec.
Qed.

Lemma Pfactor_root p c : p[[c]]=0 -> { q | p ≅ q *, [-c;C1] }.
Proof.
 intros H.
 assert (D : degree [-c; C1] = 1%nat).
 { apply degree_is_1. apply C1_neq_C0. }
 destruct (Pdiv p [-c;C1]) as (q & r & E & LT).
 - rewrite D; lia.
 - rewrite D in LT. exists q.
   assert (D' : degree r = O) by lia. clear D LT.
   rewrite <- (compactify_Peq r) in E. unfold degree in D'.
   destruct (compactify r) as [|c0 [|c1 s] ].
   + now rewrite Pplus_0_r in E.
   + rewrite E in H. rewrite Pplus_eval, Pmult_eval in H. cbn in H.
     ring_simplify in H. rewrite H in E. rewrite Pzero_alt in E.
     now rewrite Pplus_0_r in E.
   + now simpl in D'.
Qed.

Lemma linfactors_coef_after l n :
 (length l < n)%nat -> coef n (linfactors l) = C0.
Proof.
 revert n.
 induction l; simpl; intros n Hn.
 - unfold coef. now rewrite nth_overflow.
 - rewrite Pmult_comm. simpl. rewrite Pplus_coef.
   rewrite Pzero_alt, Pplus_0_r.
   unfold coef in *.
   replace C0 with (-a * 0) at 1 by ring.
   rewrite map_nth. rewrite IHl. 2:lia.
   destruct n.
   + simpl. ring.
   + simpl. replace C0 with (C1 * 0) at 2 by ring.
     rewrite map_nth. rewrite IHl. 2:lia. ring.
Qed.

Lemma linfactors_coef l : coef (length l) (linfactors l) = C1.
Proof.
 induction l; simpl; auto.
 rewrite Pmult_comm. simpl. rewrite Pplus_coef.
 rewrite Pzero_alt, Pplus_0_r.
 unfold coef in *.
 replace C0 with (-a * 0) at 1 by ring.
 rewrite map_nth. fold (coef (S (length l)) (linfactors l)).
 rewrite linfactors_coef_after by lia.
 simpl.
 replace C0 with (C1 * 0) at 2 by ring.
 rewrite map_nth. rewrite IHl. ring.
Qed.

Lemma linfactors_nz l : ~ linfactors l ≅ [].
Proof.
 intros H.
 destruct (nth_in_or_default (length l) (linfactors l) C0) as [H'|H'].
 - fold (coef (length l) (linfactors l)) in H'.
   rewrite linfactors_coef in H'. apply C1_neq_C0.
   apply (Peq_nil_contains_C0 _ H C1 H').
 - apply C1_neq_C0. rewrite <- (linfactors_coef l). unfold coef.
   now rewrite H'.
Qed.

Lemma linfactors_degree l : degree (linfactors l) = length l.
Proof.
 induction l; simpl.
 - change [C1] with (monom C1 0). apply monom_degree. apply C1_neq_C0.
 - rewrite Pmult_degree, IHl.
   rewrite degree_is_1. lia. apply C1_neq_C0.
   apply linfactors_nz.
   change (~[-a;C1]≅[]). intros H. apply Peq_compactify_eq in H. cbn in H.
   destruct Ceq_dec. now apply C1_neq_C0. easy.
Qed.

Lemma monicify_degree p : degree (monicify p) = degree p.
Proof.
 unfold monicify.
 destruct (compactify_last p) as [H|H].
 - apply Peq0_carac in H. rewrite H. now rewrite Pscale_alt.
 - apply Pscale_degree. now apply nonzero_div_nonzero.
Qed.

Lemma monicify_eval p c : (monicify p)[[c]] = p[[c]] / topcoef p.
Proof.
 unfold monicify. rewrite Pmult_eval. cbn. unfold Cdiv. ring.
Qed.

Lemma monicify_root p c : Root c (monicify p) <-> Root c p.
Proof.
 unfold Root. rewrite monicify_eval.
 destruct (Peq_0_dec p) as [->|N].
 - cbn. intuition. unfold Cdiv. rewrite Cinv0. ring.
 - rewrite <- topcoef_0_iff in N. split.
   + unfold Cdiv. intros H. apply Cmult_integral in H. destruct H; auto.
     apply nonzero_div_nonzero in N. easy.
   + intros ->. apply Cmult_0_l.
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

Lemma topcoef_scale c p : topcoef ([c] *, p) = c * topcoef p.
Proof.
 destruct (Ceq_dec c 0) as [->|N].
 - rewrite Pzero_alt. cbn. ring.
 - rewrite !topcoef_alt. rewrite Pscale_degree by trivial.
   rewrite Pscale_alt. unfold coef.
   replace C0 with (c*C0) at 1 by apply Cmult_0_r.
   apply map_nth.
Qed.

Lemma topcoef_mult p q : topcoef (p *, q) = topcoef p * topcoef q.
Proof.
 unfold topcoef.
 destruct (Peq_0_dec p) as [->|Hp]. cbn. ring.
 destruct (Peq_0_dec q) as [->|Hq]. cbn. rewrite Pmult_0_r. cbn. ring.
 rewrite <- compactify_Pmult; auto.
 rewrite Peq0_carac in Hp, Hq.
 apply app_removelast_last with (d:=C0) in Hp, Hq.
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

Lemma topcoef_lin a b : a<>C0 -> topcoef [b;a] = a.
Proof.
 intros. cbn. destruct Ceq_dec; easy.
Qed.

Lemma monicify_monic p : ~p≅[] -> monic (monicify p).
Proof.
 intros H.
 unfold monic, monicify. rewrite topcoef_mult, topcoef_singl.
 rewrite <- topcoef_0_iff in H. now field.
Qed.

Lemma deg0_monic_carac p : degree p = O -> monic p -> p ≅ [C1].
Proof.
 intros D M.
 apply Peq_iff.
 change [C1] with (monom C1 0). rewrite compactify_monom by apply C1_neq_C0.
  unfold monom; simpl.
 unfold monic, topcoef, degree in *.
 destruct (compactify p) as [|a [|b q] ]; simpl in *; subst; try easy.
 now destruct C1_neq_C0.
Qed.

Lemma All_roots p : monic p -> exists l, p ≅ linfactors l.
Proof.
 remember (degree p) as d eqn:H. revert p H.
 induction d.
 - exists []. simpl. apply deg0_monic_carac; auto.
 - intros p D M.
   destruct (Fundamental_Theorem_Algebra p) as (c & Hc); try lia.
   destruct (Pfactor_root p c Hc) as (q & Hq).
   assert (degree q = d).
   { destruct (Peq_0_dec q) as [Hq0|Hq0].
     - rewrite Hq0 in Hq. simpl in Hq. now rewrite Hq in D.
     - rewrite Hq in D. rewrite Pmult_degree in D; auto.
       rewrite degree_is_1 in D. lia. apply C1_neq_C0.
       change (~[-c;C1]≅[]). rewrite Peq0_carac. cbn.
       destruct Ceq_dec; try easy. now destruct C1_neq_C0. }
   assert (monic q).
   { unfold monic in *. rewrite Hq, topcoef_mult in M.
     rewrite topcoef_lin in M by apply C1_neq_C0.
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

(** In [linfactors] we can permute freely the roots *)

Lemma linfactors_perm l l' :
 Permutation l l' -> linfactors l ≅ linfactors l'.
Proof.
 induction 1; cbn [linfactors]; try easy.
 - now rewrite IHPermutation.
 - now rewrite !Pmult_assoc, (Pmult_comm [_;_]).
 - now rewrite IHPermutation1, IHPermutation2.
Qed.

Lemma linfactors_roots l c : In c l <-> Root c (linfactors l).
Proof.
 revert c. induction l; unfold Root in *; cbn [linfactors In].
 - intros c. cbn. rewrite Cmult_1_r, Cplus_0_l. split. easy. apply C1_neq_C0.
 - intros c. rewrite IHl, Pmult_eval, Cmult_integral. clear IHl.
   cbn. rewrite Cplus_0_l, !Cmult_1_r, Cmult_1_l.
   split; destruct 1 as [A|B]; auto.
   + right. subst. ring.
   + left. symmetry. apply Cminus_eq. now rewrite Cplus_comm in B.
Qed.

(* TODO: move elsewhere *)
Lemma count_occ_repeat [A](decA : forall x y : A, {x = y} + {x <> y})
  x n y :
  count_occ decA (repeat x n) y = if decA x y then n else O.
Proof.
 induction n; simpl; destruct decA; simpl; congruence.
Qed.
Lemma count_occ_remove [A](decA : forall x y : A, {x = y} + {x <> y})
  l x y :
  count_occ decA (remove decA x l) y =
   if decA x y then O else count_occ decA l y.
Proof.
 induction l; repeat (simpl; destruct decA); congruence.
Qed.

(** In a list, moving all the occurrences of a value at front. *)

Definition movefront [A](decA : forall x y : A, {x = y} + {x <> y}) x l :=
 repeat x (count_occ decA l x) ++ remove decA x l.

Lemma movefront_perm [A](decA : forall x y : A, {x = y} + {x <> y}) x l :
 Permutation l (movefront decA x l).
Proof.
 rewrite (Permutation_count_occ decA). intros y. unfold movefront.
 rewrite count_occ_app, count_occ_remove, count_occ_repeat.
 destruct decA; subst; lia.
Qed.


(** derivative of a polynomial *)

Fixpoint Pdiff p :=
 match p with
 | [] => []
 | c::p => p +, (C0::Pdiff p)
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
 rewrite IHp. rewrite (Pplus_assoc p (C0::Pdiff p)), <- (Pplus_assoc _ q).
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
    [RtoC (INR (S n))] *, linfactors (repeat c n).
Proof.
 induction n.
 - cbn [repeat linfactors].
   rewrite Pmult_1_l. simpl. rewrite !Cplus_0_r, Cmult_1_l.
   apply compactify_eq_Peq. apply (app_C0_compactify_reduce_1 [C1]).
 - set (n' := S n) in *.
   cbn [repeat linfactors].
   rewrite Pdiff_mult, IHn. clear IHn.
   rewrite Pmult_assoc.
   change (linfactors (repeat c n) *, _) with (linfactors (repeat c n')).
   set (lin := linfactors _).
   rewrite !S_INR, !RtoC_plus.
   change [INR n'+C1] with (Pplus [RtoC (INR n')] [C1]).
   rewrite Pmult_plus_distr_r.
   apply Pplus_eq_compat; try easy. clearbody lin.
   rewrite Pmult_comm. apply Pmult_eq_compat; try easy.
   cbn.
   rewrite !Cplus_0_r.
   apply compactify_eq_Peq. apply (app_C0_compactify_reduce_1 [C1]).
Qed.

Lemma monom_S a k : monom a (S k) = C0 :: monom a k.
Proof.
 now unfold monom.
Qed.

Lemma diff_monom a k : Pdiff (monom a k) ≅ [RtoC (INR k)] *, monom a (pred k).
Proof.
 induction k.
 - simpl. now rewrite Cmult_0_l, Cplus_0_l.
 - simpl pred.
   rewrite monom_S, S_INR, RtoC_plus. cbn -[Pmult]. rewrite IHk.
   change [INR k+C1] with (Pplus [RtoC (INR k)] [C1]).
   rewrite Pmult_plus_distr_r.
   rewrite Pmult_1_l. rewrite Pplus_comm. apply Pplus_eq_compat; try easy.
   destruct k.
   + simpl. rewrite !Cmult_0_l, !Cplus_0_l.
     apply compactify_eq_Peq. apply (app_C0_compactify_reduce_1 [C0]).
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
    simple roots. First, version for [linprod] polynomials. *)

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

(** Diagonalization *)

Definition Diag n l : Square n :=
 fun i j => if (i =? j)%nat then nth i l C0 else C0.

(* prep_mat A := A - X.Id
   hence DeterminantP (prep_mat A) isn't monic when n is odd.
   Instead of tweaking with prep_mat, we simply multiply by the parity
   afterwards. *)

Definition CharPoly {n} (A:Square n) := monicify (DeterminantP (prep_mat A)).

Lemma parity_alt n : parity n = (-C1)^n.
Proof.
 induction n as [|n IH]. simpl; auto. rewrite parity_S, IH. simpl. ring.
Qed.

Lemma parity_nz n : parity n <> C0.
Proof.
 induction n as [|n IH].
 apply C1_neq_C0.
 rewrite parity_S. apply Cmult_neq_0; auto.
 apply Copp_neq_0_compat, C1_neq_C0.
Qed.

Lemma CharPoly_deg {n} (A:Square n) : degree (CharPoly A) = n.
Proof.
 unfold CharPoly. now rewrite monicify_degree, detP_deg.
Qed.

Lemma detP_nz {n} (A:Square n) : ~DeterminantP (prep_mat A) ≅ [].
Proof.
 intro H.
 assert (H' := detP_deg A). rewrite H in H'. cbn in H'. subst n.
 revert H. cbn. rewrite Peq0_carac. cbn. destruct Ceq_dec; try easy.
 now destruct C1_neq_C0.
Qed.

Lemma detP_topcoef {n} (A:Square n) :
 topcoef (DeterminantP (prep_mat A)) <> C0.
Proof.
 rewrite topcoef_0_iff. apply detP_nz.
Qed.

Lemma CharPoly_monic {n} (A:Square n) : monic (CharPoly A).
Proof.
 apply monicify_monic. apply detP_nz.
Qed.

(* TODO : finir un jour
Lemma detP_topcoef_parity {n} (A:Square n) :
 topcoef (DeterminantP (prep_mat A)) = parity n.
Proof.
 rewrite topcoef_alt. rewrite detP_deg. unfold coef.
 induction n as [|[|n] IH].
 - easy.
 - easy.
 - simpl parity. rewrite DetP_simplify.
...
*)

Lemma reduce_compat {n} (A B : Square (S n)) : A == B ->
 forall x y, reduce A x y == reduce B x y.
Proof.
 intros E x y i j Hi Hj. unfold reduce.
 do 2 (case Nat.ltb_spec; intros); apply E; lia.
Qed.

Lemma Determinant_compat {n} (A B : Square n) : A == B ->
 Determinant A = Determinant B.
Proof.
 revert A B. induction n as [|[|] IH]; intros A B E; try easy.
 - simpl. apply E; lia.
 - rewrite !Det_simplify.
   apply big_sum_eq_bounded; intros x Hx.
   f_equal.
   + f_equal. apply E; lia.
   + apply IH. now apply reduce_compat.
Qed.

Global Instance : forall n, Proper (@mat_equiv n n ==> eq) Determinant.
Proof.
 exact @Determinant_compat.
Qed.

Lemma reduce_scale {n} (A:Square (S n)) x y c :
 reduce (c.*A) x y == c.*(reduce A x y).
Proof.
 intros i j Hi Hj. unfold reduce, scale. simpl.
 now do 2 destruct Nat.ltb.
Qed.

Lemma Determinant_scale {n} (A:Square n) c :
 Determinant (c .* A) = c ^ n * Determinant A.
Proof.
 revert A. induction n as [|[|] IH]; intros.
 - simpl. ring.
 - simpl. unfold scale. ring.
 - rewrite !Det_simplify.
   transitivity (Σ
    (fun i =>
     c ^ S (S n) * ((parity i * A i O) * Determinant (reduce A i 0)))
    (S (S n))).
   + apply big_sum_eq_bounded; intros.
     rewrite reduce_scale, IH. simpl Cpow. unfold scale. ring.
   + symmetry.
     apply (@big_sum_mult_l _ _ _ _ C_is_ring).
Qed.

Lemma Determinant_Mopp {n} (A:Square n) :
 Determinant (Mopp A) = parity n * Determinant A.
Proof.
 unfold Mopp. now rewrite Determinant_scale, parity_alt.
Qed.

Definition MatOfCols {n} (l : list (Vector n)) : Square n :=
 fun i j => (nth j l Zero) i O.

Lemma WF_MatOfCols {n} (l : list (Vector n)) :
 length l = n -> Forall WF_Matrix l -> WF_Matrix (MatOfCols l).
Proof.
 unfold MatOfCols.
 intros H F. red. intros x y Hxy.
 destruct (Nat.lt_ge_cases y n).
 - rewrite Forall_forall in F.
   apply (F (nth y l Zero)); try lia. apply nth_In; lia.
 - rewrite nth_overflow. easy. lia.
Qed.

Lemma MatOfCols_col {n} (l : list (Vector n)) j :
 get_vec j (MatOfCols l) == nth j l Zero.
Proof.
 unfold get_vec. intros x y Hx Hy. now replace y with O by lia.
Qed.

Lemma MatOfCols_col_eq {n} (l : list (Vector n)) j :
 length l = n -> Forall WF_Matrix l ->
 get_vec j (MatOfCols l) = nth j l Zero.
Proof.
 intros L F.
 apply mat_equiv_eq, MatOfCols_col.
 - apply WF_get_vec, WF_MatOfCols; auto.
 - destruct (Nat.ltb_spec j n); intros.
   + rewrite Forall_forall in F.
     apply (F (nth j l Zero)); try lia. apply nth_In. lia.
   + rewrite nth_overflow; auto with wf_db. lia.
Qed.

Lemma Diag_col n (l : list C) j :
 get_vec j (Diag n l) == (nth j l C0) .* e_i j.
Proof.
 intros x y Hx Hy.
 unfold Diag, get_vec. replace y with O by lia. simpl.
 unfold e_i, scale. case Nat.eqb_spec; simpl; intros; try ring.
 subst j.
 case Nat.ltb_spec; intros; simpl; try lia. ring.
Qed.

Lemma Diag_times_vect n (l : list C) (a : Vector n) :
 Diag n l × a == (fun i _ => nth i l C0 * a i O).
Proof.
 intros x y Hx Hy. unfold Mmult, Diag.
 induction n; simpl; auto. lia.
 case (Nat.eqb_spec x n); intros.
 - subst x. replace y with O by lia.
   rewrite big_sum_0_bounded, Cplus_0_l; trivial.
   intros x' Hx'. case Nat.eqb_spec; intros. lia. now rewrite Cmult_0_l.
 - rewrite IHn by lia. ring.
Qed.

Lemma WF_Diag n (l : list C) : length l = n -> WF_Matrix (Diag n l).
Proof.
 intros Hl x y Hxy. unfold Diag.
 case Nat.eqb_spec; intros; auto. subst. rewrite nth_overflow; auto. lia.
Qed.

Lemma MatOfCols_eqn {n} (A : Square n) (l : list (Vector n * C)) :
 length l = n ->
 Forall (fun '(v,c) => WF_Matrix v /\ v<>Zero /\ A × v = c .* v) l ->
 let B := MatOfCols (map fst l) in
 let D := Diag n (map snd l) in
 A × B = B × D.
Proof.
 intros H F B D. rewrite Forall_forall in F.
 apply det_by_get_vec. intros j.
 rewrite <- !get_vec_mult.
 assert (F' : Forall WF_Matrix (map fst l)).
 { rewrite Forall_forall. intros x.
   rewrite in_map_iff. intros ((v,c) & <- & IN). simpl.
   apply (F _ IN). }
 assert (WB : WF_Matrix B).
 { apply WF_MatOfCols; auto. now rewrite map_length. }
 assert (E : get_vec j B = nth j (map fst l) Zero).
 { apply MatOfCols_col_eq; auto. now rewrite map_length. }
 rewrite E.
 assert (E' : get_vec j D = nth j (map snd l) C0 .* e_i j).
 { apply mat_equiv_eq, Diag_col; auto with wf_db.
   apply WF_get_vec, WF_Diag. now rewrite map_length. }
 rewrite E', Mscale_mult_dist_r.
 destruct (Nat.lt_ge_cases j n) as [LT|GE].
 - rewrite <-H in LT.
   rewrite <- matrix_by_basis by lia. rewrite E.
   assert (IN := nth_In l (Zero,C0) LT).
   destruct (nth j l (Zero, C0)) as (v,c) eqn:E2.
   destruct (F _ IN) as (WF & _ & E3).
   change (@Zero n 1) with (fst (@Zero n 1,C0)).
   rewrite map_nth, E2. simpl.
   change C0 with (snd (@Zero n 1, C0)). now rewrite map_nth, E2.
 - rewrite !nth_overflow by (rewrite map_length; lia).
   now rewrite Mmult_0_r, Mscale_0_l.
Qed.

Lemma times_ei_col {n} (A : Square n) m :
 WF_Matrix A ->
 A × e_i m = get_vec m A.
Proof.
 intros HA.
 apply mat_equiv_eq; auto with wf_db.
 intros x y Hx Hy. replace y with O by lia. clear y Hy.
 unfold Mmult, e_i, get_vec. simpl.
 destruct (Nat.ltb_spec m n) as [Hm|Hm].
 - apply big_sum_unique. exists m. split. apply Hm. split.
   + case Nat.eqb_spec; intros; simpl; try lia.
     case Nat.ltb_spec; intros; simpl; try lia. ring.
   + intros y Hy Hy'.
     case Nat.eqb_spec; intros; simpl; try lia. ring.
 - replace (A x m) with C0 by (symmetry; apply HA; lia).
   apply (@big_sum_0_bounded _ C_is_monoid). intros y Hy.
   case Nat.eqb_spec; intros; simpl; try lia. ring.
Qed.

Lemma scale_integral {n} (v:Vector n) c : WF_Matrix v ->
 v <> Zero -> c .* v = Zero -> c = C0.
Proof.
 intros WF Hv E. destruct (nonzero_vec_nonzero_elem _ WF Hv) as (i,H).
 assert (E' : (c .* v) i O = C0) by now rewrite E.
 unfold scale in E'. apply Cmult_integral in E'. intuition.
Qed.

Definition VecZeroAbove {n} (v : Vector n) m := @WF_Matrix m 1 v.

Lemma exists_eigenbasis n (A : Square n) eigvals :
  WF_Matrix A ->
  CharPoly A ≅ linfactors eigvals ->
  NoDup eigvals ->
  exists B : Square n, WF_Matrix B /\ invertible B /\
                       A × B = B × Diag n eigvals.
Proof.
 intros HA D ND.
 assert (Step1 : forall c, In c eigvals -> det_eq_c C0 (A .+ (-c) .* I n)).
 { intros c Hc.
   red. split; trivial.
   rewrite linfactors_roots in Hc. rewrite <- D in Hc. unfold CharPoly in Hc.
   rewrite monicify_root in Hc. red in Hc.
   rewrite <- Peval_Det in Hc.
   rewrite <- Hc. clear Hc. apply Determinant_compat.
   unfold eval_matP, prep_mat in *.
   intros i j Hi Hj. unfold Mplus, scale, I.
   destruct andb; cbn; ring. }
 assert (Step2 : forall c, In c eigvals ->
          exists v:Vector n, WF_Matrix v /\ v<>Zero /\ A × v = c .* v).
 { intros c Hc. apply Step1 in Hc.
   apply lin_dep_det_eq_0 in Hc; auto with wf_db.
   destruct Hc as (v & H1 & H2 & H3).
   exists v; repeat split; auto.
   rewrite Mmult_plus_distr_r, Mscale_mult_dist_l, Mmult_1_l in H3; auto.
   assert (H4 : A × v .+ (-c .* v) .+ (c .* v) = (c .* v)).
   { rewrite H3. lma. }
   rewrite Mplus_assoc in H4.
   rewrite <- Mscale_plus_distr_l in H4.
   replace (-c + c)%C with C0 in H4 by lca.
   rewrite <- H4.
   lma. }
 assert (Step3 : forall l, NoDup l -> incl l eigvals ->
          exists eigpairs : list (Vector n * C),
          map snd eigpairs = l /\
          Forall (fun '(v,c) =>
                  WF_Matrix v /\ v<>Zero /\ A × v = c .* v) eigpairs).
 { induction l; intros NDl INl.
   - exists []; split; auto.
   - destruct IHl as (ep & E & F).
     now inversion NDl.
     unfold incl in *. simpl in INl; intuition.
     destruct (Step2 a) as (v & WF & Ha & Ev). apply INl; now left.
     exists ((v,a)::ep); split.
     + simpl. now f_equal.
     + constructor; auto. }
 destruct (Step3 eigvals ND (incl_refl _)) as (eigpairs & E & F).
 clear Step1 Step2 Step3.
 assert (Lv : length eigvals = n).
 { rewrite <- (CharPoly_deg A). rewrite D.
   symmetry. apply linfactors_degree. }
 clear D.
 assert (Lp : length eigpairs = n).
 { rewrite <- E in Lv. now rewrite map_length in Lv. }
 set (B := MatOfCols (map fst eigpairs)).
 assert (HB : WF_Matrix B).
 { apply WF_MatOfCols.
   + now rewrite map_length.
   + rewrite Forall_map.
     rewrite Forall_forall in *. intros (v,c) Hvc.
     specialize (F _ Hvc). now simpl in *. }
 assert (EQN : A × B = B × Diag n eigvals).
 { rewrite <- E. apply MatOfCols_eqn; auto. }
 exists B; repeat split; auto.
 apply lin_indep_invertible; auto.
 (* B linearly indep *)
 assert (IND : forall m (a:Vector n), (m <= n)%nat ->
          VecZeroAbove a m -> B × a = Zero -> a = Zero);
 [| intros a Ha; now apply (IND n a) ].
 induction m.
 - intros a _ Ha _.
   apply mat_equiv_eq; auto with wf_db.
   unfold VecZeroAbove, WF_Matrix in *. intuition.
   intros i j Hi Hj. apply Ha. lia.
 - intros a LE Ha E'.
   assert (WFa : WF_Matrix a).
   { unfold VecZeroAbove, WF_Matrix in *; intuition. }
   set (c := nth m eigvals C0).
   set (a' := (Diag n eigvals × a .+ (- c) .* a)).
   assert (WFa' : WF_Matrix a').
   { unfold a'. auto using WF_Diag with wf_db. }
   assert (Ha' : a' = Zero).
   { apply IHm. lia.
     - (* VecZeroAbove a' m *)
       intros i j Hij.
       destruct (Nat.leb_spec 1 j).
       + apply WFa'. lia.
       + destruct (Nat.leb_spec n i).
         * apply WFa'. lia.
         * replace j with O by lia.
           unfold a', Mplus, scale.
           rewrite Diag_times_vect by lia.
           destruct (Nat.ltb_spec m i).
           { replace (a i O) with C0 by (symmetry; apply Ha; lia). ring. }
           { replace i with m by lia. fold c. ring. }
     - (* B × a' = Zero *)
       unfold a'.
       rewrite Mmult_plus_distr_l.
       rewrite <- Mmult_assoc, <- EQN, Mmult_assoc, E', Mmult_0_r.
       rewrite Mscale_mult_dist_r, E'. now rewrite Mscale_0_r, Mplus_0_l. }
   assert (Ea : a = a m O .* e_i m).
   { apply mat_equiv_eq; auto with wf_db.
     intros x y Hxn Hy. replace y with O by lia. clear y Hy.
     unfold e_i, scale.
     case Nat.eqb_spec; intros; simpl.
     + subst. case Nat.ltb_spec; intros; simpl; try lia. ring.
     + rewrite Cmult_0_r.
       destruct (Nat.ltb_spec x m) as [Hxm|Hxm]; [|apply Ha; lia].
       assert (H : a' x O = 0) by now rewrite Ha'.
       unfold a', Mplus, scale in H.
       rewrite Diag_times_vect in H by lia.
       rewrite <- Cmult_plus_distr_r in H. apply Cmult_integral in H.
       destruct H as [H|H]; auto. exfalso.
       apply Cminus_eq in H. apply NoDup_nth in H; auto; lia. }
   rewrite Ea in E'. rewrite Mscale_mult_dist_r in E'.
   rewrite times_ei_col in E'; auto with wf_db.
   unfold B in E'.
   assert (Forall WF_Matrix (map fst eigpairs)).
   { rewrite Forall_forall in *. intros x.
     rewrite in_map_iff. intros ((v',c') & <- & IN). simpl.
     apply (F _ IN). }
   rewrite MatOfCols_col_eq in E' by (auto; rewrite map_length; lia).
   set (v := nth m (map fst eigpairs) Zero) in *.
   assert (IN : In (v,c) eigpairs).
   { unfold v, c. rewrite <- E.
     change (@Zero n 1) with (fst (@Zero n 1, C0)). rewrite map_nth.
     change C0 with (snd (@Zero n 1, C0)) at 2. rewrite map_nth.
     rewrite <- surjective_pairing. apply nth_In. lia. }
   rewrite Forall_forall in F. specialize (F _ IN). simpl in F.
   replace (a m O) with C0 in *. now rewrite Mscale_0_l in Ea.
   symmetry. apply (@scale_integral n v); intuition.
Qed.

(* Print Assumptions exists_eigenbasis. *)
