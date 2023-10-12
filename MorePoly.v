From Coq Require Import Arith Reals Lra Lia Permutation Morphisms.
From QuantumLib Require Import Complex Polynomial FTA.
Require Import MoreList MoreComplex.
Local Open Scope C.
Local Open Scope poly_scope.

(** * More on QuantumLib polynomials *)

(** Some extra definitions about polynomials on C *)

Definition coef n (p : Polynomial) := nth n p C0.

Definition topcoef (p : Polynomial) := last (compactify p) C0.

Definition monom (c:C) (k:nat) := repeat C0 k ++ [c].

Definition _X_ := [C0;C1].

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

Lemma topcoef_monom c k : topcoef (monom c k) = c.
Proof.
 destruct (Ceq_dec c 0); subst.
 - unfold monom, topcoef.
   rewrite app_C0_compactify_reduce_1.
   change (repeat C0 k) with ([]++repeat C0 k).
   now rewrite app_C0_compactify_reduce.
 - unfold topcoef. rewrite compactify_monom; auto.
   unfold monom. apply last_last.
Qed.

Lemma Pscale_alt c p : [c] *, p ≅ List.map (Cmult c) p.
Proof.
 apply cons_singleton_mult.
Qed.

Lemma monom_scale c k : monom c k ≅ [c] *, monom C1 k.
Proof.
 unfold monom. rewrite Pscale_alt, map_app. simpl.
 apply Peq_iff. f_equal. f_equal.
 now rewrite map_repeat, Cmult_0_r.
 f_equal. lca.
Qed.

Lemma Pmult_X (p:Polynomial) : _X_ *, p ≅ C0::p.
Proof.
 simpl.
 rewrite <- Pscale_alt.
 rewrite Pzero_alt. simpl. rewrite Pplus_0_r.
 rewrite <- Pscale_alt.
 now rewrite Pmult_1_l.
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

(** Euclidean division of polynomial *)

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

(** In [linfactors] we can freely permute the roots *)

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
   + left. symmetry. apply Ceq_minus. now rewrite Cplus_comm in B.
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
