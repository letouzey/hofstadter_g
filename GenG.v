
Require Import MoreFun MoreList DeltaList GenFib.
Require FunG.
Import ListNotations.
Set Implicit Arguments.

(** Study of the functional equation:
     - [Fq 0 = 0]
     - [Fq (S n) + Fq^(q+1) (n) = S n]
    where [Fq^(q+1) (n)] is [q+1] repeated applications of [Fq] at [n].

    Note: using [q+1] instead of [q] iterations allows to avoid
     the case of [0] iterations, where Fq^0 is identity, and hence
     Fq (S n) = 1 always.

    With this setting:
    - [F 0] is [fun x => floor((x+1)/2)] (see below).
    - [F 1] is Hofstadter's [G] i.e. [fun x => floor((x+1)/phi]
      See http://oeis.org/A5206
    - [F 2] is Hofstadter's [H], see http://oeis.org/A5374
    - [F 3] is http://oeis.org/A5375
    - [F 4] is http://oeis.org/A5376
*)

(** Coq representation of [F] as an inductive relation. This way,
    no need to convince Coq yet that [F] is indeed a function.
    - [F q n a] means that [Fq(n) = a].
    - [Fs q p n a] means that [Fq^p (n) = a].
*)

Inductive F (q:nat) : nat -> nat -> Prop :=
| F0 : F q 0 0
| FS n a b : Fs q (S q) n a -> S n = a+b -> F q (S n) b

with Fs (q:nat) : nat -> nat -> nat -> Prop :=
| Fs0 n : Fs q 0 n n
| FsS p a b c : Fs q p a b -> F q b c -> Fs q (S p) a c.

#[global] Hint Constructors F Fs : hof.

(** The early behavior of [F] and [Fs] when [n<=3] doesn't depend on q *)

Lemma Fs_0 q p : Fs q p 0 0.
Proof.
 induction p; eautoh.
Qed.
#[global] Hint Resolve Fs_0 : hof.

Lemma F_1 q : F q 1 1.
Proof.
 induction q; eautoh.
Qed.
#[global] Hint Resolve F_1 : hof.

Lemma Fs_1 q p : Fs q p 1 1.
Proof.
 induction p; eautoh.
Qed.
#[global] Hint Resolve Fs_1 : hof.

Lemma F_2 q : F q 2 1.
Proof.
 induction q; eautoh.
Qed.
#[global] Hint Resolve F_2 : hof.

Lemma Fs_2 q p : Fs q p 2 (1+(1-p)).
Proof.
 induction p; eautoh.
 simpl.
 eapply FsS. apply IHp. destruct p; simpl; autoh.
Qed.
#[global] Hint Resolve Fs_2 : hof.

Lemma F_3 q : F q 3 2.
Proof.
 induction q; eautoh.
Qed.
#[global] Hint Resolve F_3 : hof.

Lemma Fs_3 q p : Fs q p 3 (1+(2-p)).
Proof.
 induction p; eautoh.
 eapply FsS; eauto. destruct p as [|[|p]]; simpl; autoh.
Qed.
#[global] Hint Resolve Fs_3 : hof.

(** [F] and [Fs] aren't above the identity line *)

Lemma F_le q n a : F q n a -> a <= n.
Proof.
 induction 1; lia.
Qed.
#[global] Hint Resolve F_le : hof.

Lemma Fs_le q p n a : Fs q p n a -> a <= n.
Proof.
 induction 1; trivial.
 transitivity b; eautoh.
Qed.
#[global] Hint Resolve Fs_le : hof.

(** [F] and [Fs] are functional relations : unique output *)

Scheme F_ind2 := Induction for F Sort Prop
  with Fs_ind2  := Induction for Fs Sort Prop.

Combined Scheme F_Fs_ind from F_ind2, Fs_ind2.

Lemma F_Fs_fun q :
 (forall n a, F q n a -> forall a', F q n a' -> a = a') /\
 (forall p n a, Fs q p n a -> forall a', Fs q p n a' -> a = a').
Proof.
apply F_Fs_ind.
- inversion_clear 1; auto.
- intros n a b HFs IH Hab a' HF.
  inversion_clear HF; auto.
  apply IH in H; lia.
- inversion_clear 1; auto.
- intros p a b c HFs IH HF IH' a' HFs'.
  inversion_clear HFs'; auto.
  apply IH in H; subst; auto.
Qed.

Lemma F_fun q n a a' : F q n a -> F q n a' -> a = a'.
Proof.
 intro. now apply F_Fs_fun.
Qed.

Lemma Fs_fun q p n a a' : Fs p q n a -> Fs p q n a' -> a = a'.
Proof.
 intro. now apply F_Fs_fun.
Qed.

(** [F] does have an implementation : there exists a function [f]
    satisfying these equations. One possible tricq to define [f]
    via Coq structural recursion is to add an extra parameter [p]:
    [recf q p] is [f q] below [p] and arbitrary above.
*)

Fixpoint recf q p n :=
 match p, n with
 | S p, S n => S n - ((recf q p)^^(S q)) n
 | _, _ => 0
 end.

Definition f q n := recf q n n.
Notation fs q p := (f q ^^p).

Lemma recf_le q p n : recf q p n <= n.
Proof.
 induction p; cbn - ["-" "^^"]. lia. destruct n; lia.
Qed.

Lemma recfs_le a q p n : ((recf q p)^^a) n <= n.
Proof.
 induction a; simpl; auto. etransitivity. apply recf_le. apply IHa.
Qed.

Lemma recf_sound q p n : n <= p -> F q n (recf q p n).
Proof.
revert n.
induction p.
- inversion 1. simpl. constructor.
- destruct n.
  + simpl. constructor.
  + cbn - ["-" "^^"].
    assert (IHa : forall a m, m <= p -> Fs q a m ((recf q p ^^ a) m)).
    { induction a; intros; simpl; econstructor; eauto.
      apply IHp. transitivity m; auto using recfs_le. }
    econstructor. apply IHa. lia.
    generalize (recfs_le (S q) q p n). lia.
Qed.

Lemma f_sound q n : F q n (f q n).
Proof.
 now apply recf_sound.
Qed.
#[global] Hint Resolve f_sound : hof.

Lemma f_complete q n a : F q n a <-> f q n = a.
Proof.
split; intros H.
- apply (F_fun (f_sound q n) H).
- subst; autoh.
Qed.

(** A few examples *)

(*
Compute taqe 26 (f 0).
Compute taqe 26 (f 1).
Compute taqe 26 (f 2).
Compute taqe 26 (f 3).
*)
(*
f 0 : [0; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5; 6; 6; 7; 7]
f 1 : [0; 1; 1; 2; 3; 3; 4; 4; 5; 6; 6; 7; 8; 8; 9]
f 2 : [0; 1; 1; 2; 3; 4; 4; 5; 5; 6; 7; 7; 8; 9; 10]
f 3 : [0; 1; 1; 2; 3; 4; 5; 5; 6; 6; 7; 8; 8; 9; 10]
*)

(* The first values of [f] when [n<=3] do not depend on [q] *)

Lemma f_q_0 q : f q 0 = 0.
Proof.
 reflexivity.
Qed.

Lemma f_q_1 q : f q 1 = 1.
Proof.
 apply f_complete; autoh.
Qed.

Lemma f_q_2 q : f q 2 = 1.
Proof.
 apply f_complete; autoh.
Qed.

Lemma f_q_3 q : f q 3 = 2.
Proof.
 apply f_complete; autoh.
Qed.

(** Basic equations over [f] : the same as [F] *)

Lemma Fs_iter_f p q n : Fs q p n (fs q p n).
Proof.
induction p.
- simpl. autoh.
- eapply FsS; eauto. simpl.
  rewrite f_complete; autoh.
Qed.

Lemma fs_q_0 p q : fs q p 0 = 0.
Proof.
 induction p; simpl; auto.
 rewrite IHp. apply f_q_0.
Qed.

Lemma fs_q_1 p q : fs q p 1 = 1.
Proof.
 induction p; simpl; auto.
 rewrite IHp. apply f_q_1.
Qed.

Lemma fs_q_2 q p : 0<p -> fs q p 2 = 1.
Proof.
 destruct p. easy. intros _. now rewrite iter_S, f_q_2, fs_q_1.
Qed.

Lemma f_eqn q n : f q (S n) + fs q (S q) n = S n.
Proof.
 assert (H := f_sound q (S n)).
 inversion_clear H.
 assert (fs q (S q) n = a).
 { revert H0. apply Fs_fun. apply Fs_iter_f. }
 lia.
Qed.

Lemma f_eqn_pred q n : f q n + fs q (S q) (pred n) = n.
Proof.
destruct n.
- now rewrite fs_q_0.
- apply f_eqn.
Qed.

Lemma f_S q n : f q (S n) = S n - fs q (S q) n.
Proof.
 generalize (f_eqn q n). lia.
Qed.

Lemma f_pred q n : f q n = n - fs q (S q) (pred n).
Proof.
 generalize (f_eqn_pred q n). lia.
Qed.

(** Particular case *)

Lemma f_1_g n : f 1 n = FunG.g n.
Proof.
revert n.
apply FunG.g_unique.
- reflexivity.
- intros n. symmetry. now apply f_eqn.
Qed.

Lemma f_0_half n : f 0 (2*n) = n /\ f 0 (S (2*n)) = S n.
Proof.
induction n.
- now compute.
- assert (f 0 (2*(S n)) = S n).
  { rewrite f_pred; auto.
    simpl Nat.iter.
    replace (n + (S (n+0))) with (S (2*n)); lia. }
  split; auto.
  rewrite f_pred; auto.
  simpl Nat.iter.
  replace (S (n + (S (n+0)))) with (2*(S n)); lia.
Qed.

Lemma f_0_div2 n : f 0 n = (S n) / 2.
Proof.
rewrite <- Nat.div2_div.
destruct (Nat.Even_or_Odd n) as [(m,->)|(m,->)].
- destruct (f_0_half m) as (->,_).
  symmetry. apply Nat.div2_succ_double.
- rewrite Nat.add_comm, Nat.add_1_l.
  destruct (f_0_half m) as (_,->).
  simpl. f_equal.
  symmetry. apply (Nat.div2_double m).
Qed.

Lemma f_unique q h :
  h 0 = 0  ->
  (forall n, S n = h (S n)+ (h^^S q) n) ->
  forall n, h n = f q n.
Proof.
intros h_0 h_S.
induction n as [[|n] IH] using lt_wf_ind.
- now rewrite h_0.
- assert (forall p m, m <= n -> (h^^p) m = fs q p m).
  { induction p.
    - now simpl.
    - intros. simpl.
      rewrite IHp; auto. apply IH.
      rewrite Nat.lt_succ_r. apply Nat.le_trans with m; auto.
      eapply Fs_le. eapply Fs_iter_f. }
  rewrite f_S, <- H; auto. specialize (h_S n). lia.
Qed.

Lemma f_step q n : f q (S n) = f q n \/ f q (S n) = S (f q n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 destruct n.
 - rewrite f_q_0, f_q_1. now right.
 - rewrite 2 f_S.
   assert (forall p m, m <= n ->
           fs q p (S m) = fs q p m \/
           fs q p (S m) = S (fs q p m)).
   { induction p.
     - simpl; now right.
     - intros; simpl.
       destruct (IHp m H) as [-> | ->].
       + now left.
       + apply IH.
         rewrite Nat.lt_succ_r. apply Nat.le_trans with m; auto.
         eapply Fs_le. eapply Fs_iter_f. }
   specialize (H (S q) n). lia.
Qed.

Lemma fs_step q p n : fs q p (S n) = fs q p n \/
                      fs q p (S n) = S (fs q p n).
Proof.
 induction p; simpl.
 - now right.
 - destruct IHp as [-> | ->]. now left. apply f_step.
Qed.

Lemma f_mono_S q n : f q n <= f q (S n).
Proof.
 generalize (f_step q n). lia.
Qed.

Lemma fs_mono_S q p n : fs q p n <= fs q p (S n).
Proof.
 generalize (fs_step q p n). lia.
Qed.

Lemma f_le_add q n m : f q (n+m) <= n + f q m.
Proof.
induction n; trivial.
simpl. destruct (f_step q (n+m)); lia.
Qed.

Lemma f_mono q n m : n <= m -> f q n <= f q m.
Proof.
induction 1.
- trivial.
- transitivity (f q m); auto using f_mono_S.
Qed.

Lemma fs_mono q p n m : n <= m -> fs q p n <= fs q p m.
Proof.
induction 1.
- trivial.
- transitivity (fs q p m); auto using fs_mono_S.
Qed.

(** NB : in Coq, for natural numbers, 3-5 = 0 (truncated subtraction) *)

Lemma f_lipschitz q n m : f q m - f q n <= m - n.
Proof.
destruct (le_ge_dec n m) as [H|H].
- induction H; try generalize (f_step q m); lia.
- generalize (f_mono q H). lia.
Qed.

Lemma fs_lipschitz q p n m : fs q p m - fs q p n <= m - n.
Proof.
 revert n m. induction p; auto.
 intros. simpl. etransitivity. eapply f_lipschitz. eapply IHp.
Qed.

Lemma f_nonzero q n : 0 < n -> 0 < f q n.
Proof.
 unfold lt. intros. rewrite <- (f_q_1 q). now apply f_mono.
Qed.

Lemma f_nz q n : n <> 0 -> f q n <> 0.
Proof.
 generalize (@f_nonzero q n). lia.
Qed.

Lemma f_0_inv q n : f q n = 0 -> n = 0.
Proof.
 generalize (@f_nz q n). lia.
Qed.

Lemma fs_nonzero q n p : 0 < n -> 0 < fs q p n.
Proof.
 revert n. induction p; simpl; auto using f_nonzero.
Qed.

Lemma fs_0_inv q n p : fs q p n = 0 -> n = 0.
Proof.
 generalize (@fs_nonzero q n p). lia.
Qed.

Lemma f_fix q n : f q n = n <-> n <= 1.
Proof.
split.
- destruct n; auto.
  assert (H := f_eqn q n).
  intros.
  assert (H' : fs q (S q) n = 0) by lia.
  apply fs_0_inv in H'.
  now subst.
- inversion_clear 1. apply f_q_1.
  inversion_clear H0. apply f_q_0.
Qed.

Lemma f_le q n : f q n <= n.
Proof.
 eapply F_le; eautoh.
Qed.

Lemma fs_le q p n : fs q p n <= n.
Proof.
 eapply Fs_le, Fs_iter_f.
Qed.

Lemma f_lt q n : 1<n -> f q n < n.
Proof.
 generalize (f_le q n) (f_fix q n); lia.
Qed.
#[global] Hint Resolve f_lt : hof.

Lemma fs_lt q p n : 0<p -> 1<n -> fs q p n < n.
Proof.
 destruct p; [easy|intros _ Hn].
 change (f q (fs q p n) < n).
 destruct (Nat.eq_dec (fs q p n) 0) as [->|N0]; [cbn; lia| ].
 destruct (Nat.eq_dec (fs q p n) 1) as [->|N1]; [now rewrite f_q_1| ].
 apply Nat.lt_le_trans with (fs q p n); [|apply fs_le].
 apply f_lt. lia.
Qed.

(** Two special formulations for [f_step] *)

Lemma f_next q n a : f q n = a -> (f q (S n) <> a <-> f q (S n) = S a).
Proof.
 generalize (f_step q n). lia.
Qed.

Lemma f_prev q n a : n <> 0 -> f q n = a ->
 (f q (n-1) <> a <-> f q (n-1) = a - 1).
Proof.
 intros H Ha.
 assert (Ha' := f_nz q H).
 generalize (f_step q (n-1)). replace (S (n-1)) with n; lia.
Qed.

(** [f] cannot stay flat very long *)

Lemma f_nonflat q n : f q (1+n) = f q n -> f q (2+n) = S (f q n).
Proof.
 generalize (f_eqn q (1+n)) (f_eqn q n).
 rewrite !iter_S. intros. rewrite H1 in *. simpl in *. lia.
Qed.

Lemma f_nonflat' q n : f q (S n) = f q n -> f q (n-1) = f q n - 1.
Proof.
 destruct n.
 - now rewrite f_q_0, f_q_1.
 - replace (S n - 1) with n by lia.
   intros H.
   destruct (f_step q n) as [H'|H'].
   + apply f_nonflat in H'; auto. simpl in *. lia.
   + lia.
Qed.

Lemma f_SS q n : f q n < f q (S (S n)).
Proof.
 destruct (f_step q n) as [E|E].
 - generalize (f_nonflat _ _ E). simpl in *. lia.
 - apply Nat.lt_le_trans with (f q (S n)). lia. auto using f_mono_S.
Qed.

Lemma f_double_le q n : n <= f q (2*n).
Proof.
induction n.
- trivial.
- replace (2* S n) with (S (S (2*n))) by lia.
  transitivity (S (f q (2*n))). lia. now apply f_SS.
Qed.

Lemma f_div2_le q n : n/2 <= f q n.
Proof.
 rewrite <- Nat.div2_div.
 rewrite (Nat.div2_odd n) at 2.
 transitivity (f q (2*Nat.div2 n)).
 now apply f_double_le.
 apply f_mono. lia.
Qed.

Lemma fs_bound q n p :
  1 < n -> 1 < fs q p n -> fs q p n <= n-p.
Proof.
 revert n.
 induction p.
 - simpl. intros. lia.
 - intros. simpl in *.
   assert (LE : 1 <= fs q p n).
   { generalize (@fs_nonzero q n p). lia. }
   assert (NE : fs q p n <> 1).
   { intros EQ; rewrite EQ, f_q_1 in *. lia. }
   specialize (IHp n H).
   generalize (@f_lt q (fs q p n)). lia.
Qed.

Lemma fs_init q n p : 1 <= n <= S p -> fs q p n = 1.
Proof.
 intros N.
 destruct (Nat.eq_dec n 1) as [->|N']; [ apply fs_q_1 |].
 assert (H := @fs_nonzero q n p).
 destruct (Nat.eq_dec (fs q p n) 1); trivial.
 generalize (@fs_bound q n p). lia.
Qed.

Lemma f_init q n : 2 <= n <= q+3 -> f q n = n-1.
Proof.
 intros. rewrite f_pred. rewrite fs_init; lia.
Qed.

(* Said otherwise : for any n, [f q n] will eventually be stationary
   when q grows. More precisely, for [n>=2], [f q n = n-1] as soon as
   [q>=n-3]. And for [n<2], we always have [f q n = n].
   Hard theorem : at fixed n and growing q, [f q n] will be increasing.
   See [Words.f_grows].
*)

(*==============================================================*)

(** * Faster computation of f *)

(** Auxiliary function : [countdown n = [n;n-1;...0]] *)

Fixpoint countdown n :=
 match n with
 | 0 => [0]
 | S n' => n :: countdown n'
 end.

Lemma countdown_in n x : In x (countdown n) <-> x <= n.
Proof.
 induction n; simpl; rewrite ?IHn; lia.
Qed.

(** Auxiliary function : dropping [n] leftmost elements in a list *)

Fixpoint npop {A} n (l:list A) :=
 match n with
 | 0 => l
 | S n' =>
   match l with
   | [] => []
   | _::l' => npop  n' l'
   end
 end.

Lemma npop_map {A B} (f:A->B) l p :
 npop p (map f l) = map f (npop p l).
Proof.
 revert l. induction p; destruct l; simpl in *; auto.
Qed.

Lemma npop_countdown x y : x <= y ->
  npop (y - x) (countdown y) = countdown x.
Proof.
 induction 1.
 - now rewrite Nat.sub_diag.
 - replace (S m - x) with (S (m-x)) by lia. simpl; auto.
Qed.

(** With [ftabulate],  we will build at once the list
    [[f q n; f q (n-1); ... ; f q 0]].
    And [fdescend] visits this list to compute [fs q p n].
    Even with nat values, doing this way is way faster than the current [f].
*)

Fixpoint fdescend stq p n :=
  match p with
  | 0 => n
  | S p =>
    match stq with
    | [] => 0 (* normally won't occur *)
    | a::_ => fdescend (npop (n-a) stq) p a
    end
  end.

Fixpoint ftabulate q n :=
 match n with
 | 0 => [0]
 | S n =>
   let stq := ftabulate q n in
   (S n - fdescend stq (S q) n)::stq
 end.

Lemma fdescend_spec q stq p n :
 stq = map (f q) (countdown n) -> fdescend stq p n = fs q p n.
Proof.
 revert stq n.
 induction p; intros stq n E.
 - simpl; auto.
 - rewrite iter_S. simpl.
   destruct stq as [|a stq'] eqn:Stq.
   + now destruct n.
   + assert (a = f q n).
     { destruct n; simpl in E; inversion E; auto. }
     rewrite <- H.
     apply IHp.
     rewrite E. rewrite npop_map. f_equal.
     apply npop_countdown. subst a. apply f_le.
Qed.

Lemma ftabulate_spec q n : ftabulate q n = map (f q) (countdown n).
Proof.
 induction n.
 - reflexivity.
 - cbn -[minus fdescend].
   rewrite (fdescend_spec q); auto.
   rewrite <- f_S. f_equal; auto.
Qed.

(** Now comes a reasonably efficient [f] function
    (moreover, [ftabulate] can always be used when multiples
    images of [f] are needed at the same time). *)

Definition fopt q n := hd 0 (ftabulate q n).

Lemma fopt_spec q n : fopt q n = f q n.
Proof.
 unfold fopt. rewrite ftabulate_spec. destruct n; simpl; auto.
Qed.

Lemma fopt_iter q p n : (fopt q ^^p) n = fs q p n.
Proof.
 induction p; simpl; trivial. rewrite fopt_spec. now f_equal.
Qed.

Definition fsopt q p n := fdescend (ftabulate q n) p n.

Lemma fsopt_spec q p n : fsopt q p n = fs q p n.
Proof.
 apply fdescend_spec, ftabulate_spec.
Qed.

(*==============================================================*)

(** * Antecedents by [f q]

    Study of the reverse problem [f q n = a] for some [a]. *)

Lemma f_max_two_antecedents q n m :
  f q n = f q m -> n<m -> m = S n.
Proof.
 intros H H'.
 destruct (le_lt_dec (2+n) m) as [LE|LT]; try lia.
 apply (f_mono q) in LE.
 rewrite (f_nonflat q n) in LE. lia.
 apply Nat.le_antisymm.
 - rewrite H. now apply f_mono.
 - apply f_mono_S.
Qed.

(** Another formulation of the same fact *)

Lemma f_inv q n m :
  f q n = f q m -> (n = m \/ n = S m \/ m = S n).
Proof.
 intros.
 destruct (lt_eq_lt_dec n m) as [[LT|EQ]|LT]; auto.
 - generalize (@f_max_two_antecedents q n m); auto.
 - generalize (@f_max_two_antecedents q m n); auto.
Qed.

(** [f] is an onto map *)

Lemma f_onto q a : exists n, f q n = a.
Proof.
induction a.
- exists 0; trivial.
- destruct IHa as (n,Ha).
  destruct (f_step q n); [ | exists (S n); lia].
  destruct (f_step q (S n)); [ | exists (S (S n)); lia].
  exfalso.
  generalize (@f_max_two_antecedents q n (S (S n))). lia.
Qed.

(** We even have an explicit expression of one antecedent *)

Definition rchild q n := n + fs q q n.
Definition lchild q n := n + fs q q n - 1. (** left son, if there's one *)

Lemma f_onto_eqn q a : f q (rchild q a) = a.
Proof.
 destruct (f_onto q a) as (n,Hn).
 unfold rchild. rewrite <- Hn, <- iter_S.
 assert (E := f_eqn q n).
 destruct (f_step q n) as [<-|H]; f_equal; lia.
Qed.

Lemma rightmost_child_carac q a n : f q n = a ->
 (f q (S n) = S a <-> n = rchild q a).
Proof.
 intros Hn.
 assert (H' := f_eqn q n).
 rewrite iter_S in H'.
 rewrite Hn in H'.
 unfold rchild; lia.
Qed.

Lemma f_children q a n : f q n = a ->
  n = rchild q a \/ n = lchild q a.
Proof.
intros Hn.
destruct (f_step q n) as [H|H].
- right.
  destruct (f_step q (S n)) as [H'|H'].
  + exfalso.
    generalize (@f_max_two_antecedents q n (S (S n))). lia.
  + rewrite rightmost_child_carac in H'; trivial.
    rewrite H, Hn in H'. unfold lchild, rchild in *; lia.
- rewrite <- (@rightmost_child_carac q a n); lia.
Qed.

Lemma f_lchild q a :
 f q (lchild q a) = a - 1 \/ f q (lchild q a) = a.
Proof.
 destruct (le_gt_dec a 0).
  + replace a with 0 by lia. unfold lchild.
    rewrite fs_q_0. simpl. rewrite f_q_0. now left.
  + assert (0 < rchild q a)
     by (unfold rchild; generalize (@f_nonzero q a); lia).
    destruct (f_step q (lchild q a)) as [H'|H'];
    replace (S (lchild q a)) with (rchild q a) in * by
      (unfold lchild, rchild in *; lia);
    rewrite f_onto_eqn in *; lia.
Qed.


(** This provides easily a first relationship between f and
    generalized Fibonacci numbers *)

Lemma fs_A q n p : fs q p (A q n) = A q (n-p).
Proof.
revert p.
induction n; intros.
- simpl. apply fs_q_1.
- destruct p; auto.
  rewrite iter_S; simpl. rewrite <- (IHn p). f_equal.
  rewrite <- (IHn q). apply f_onto_eqn.
Qed.

Lemma f_A q n : f q (A q n) = A q (n-1).
Proof.
 apply (fs_A q n 1).
Qed.

Lemma f_SA q n : n<>0 -> f q (S (A q n)) = S (A q (n-1)).
Proof.
 intros.
 rewrite <- (@f_A q n).
 apply rightmost_child_carac; trivial.
 unfold rchild.
 rewrite f_A, fs_A.
 replace (n-1-q) with (n-S q) by lia.
 now apply A_sum.
Qed.

(** More generally, [f] is shifting down Zecqendorf decompositions *)

Definition fbis q n := sumA q (map pred (decomp q n)).

Lemma fbis_decomp q n :
  decomp q (fbis q n) = renorm q (map pred (decomp q n)).
Proof.
 apply decomp_carac.
 - apply renorm_delta.
   apply Delta_map with (S q).
   intros; lia. apply decomp_delta.
 - now rewrite renorm_sum.
Qed.

Lemma fsbis q p n : p <= S q ->
 (fbis q^^p) n = sumA q (map (decr p) (decomp q n)).
Proof.
 intros Hp.
 revert n.
 induction p; intros.
 - simpl. now rewrite map_decr_0, decomp_sum.
 - now rewrite iter_S, IHp, fbis_decomp, renorm_mapdecr, map_decr_S by lia.
Qed.

Lemma fbis_is_f q n : fbis q n = f q n.
Proof.
 apply f_unique.
 - reflexivity.
 - clear n. intros n.
   rewrite fsbis; auto.
   assert (Hn := decomp_sum q n).
   assert (D := decomp_delta q n).
   remember (decomp q n) as l eqn:Hl.
   destruct l as [|a l].
   + simpl in *. now subst.
   + unfold fbis. rewrite decomp_S, <- Hl. simpl.
     case Nat.leb_spec; intros.
     * rewrite <- map_decr_1.
       rewrite renormS_alt, renorm_mapdecr'; simpl; auto with arith hof.
       2: destruct q; lia.
       rewrite Nat.add_shuffle1.
       assert (~In 0 l).
       { apply (@Delta_nz' (S q) a); auto with arith. }
       rewrite <- sumA_eqn_pred; auto.
       rewrite decr_0.
       unfold decr. replace (a-S q) with 0; simpl in *; lia.
     * rewrite map_cons, sumA_cons.
       rewrite <- Nat.add_assoc.
       rewrite <- map_decr_1.
       rewrite <- sumA_eqn_pred; auto.
       eapply Delta_nz; eauto. lia.
Qed.

Lemma f_decomp q n : f q n = sumA q (map pred (decomp q n)).
Proof.
 symmetry. apply fbis_is_f.
Qed.

Lemma decomp_f q n : decomp q (f q n) = renorm q (map pred (decomp q n)).
Proof.
 now rewrite <- fbis_is_f, fbis_decomp.
Qed.

Lemma fs_decomp q p n :
  p <= S q -> fs q p n = sumA q (map (decr p) (decomp q n)).
Proof.
 intros. rewrite <- fsbis; auto. clear.
 induction p; simpl; now rewrite ?IHp, <- ?fbis_is_f.
Qed.

Lemma f_sumA q l : Delta (S q) l ->
 f q (sumA q l) = sumA q (map pred l).
Proof.
 intros. rewrite f_decomp. f_equal. f_equal. autoh.
Qed.

Lemma fs_sumA q p l : p <= S q -> Delta (S q) l ->
 fs q p (sumA q l) = sumA q (map (decr p) l).
Proof.
 intros. rewrite fs_decomp; auto. f_equal. f_equal. autoh.
Qed.

Lemma f_sumA_lax q l : q<>0 -> Delta q l ->
 f q (sumA q l) = sumA q (map pred l).
Proof.
 intros. rewrite <- renorm_sum.
 rewrite f_sumA; autoh.
 rewrite <- !map_decr_1, renorm_mapdecr; auto. lia.
Qed.

Lemma fs_sumA_lax q p l : p < S q -> Delta q l ->
 fs q p (sumA q l) = sumA q (map (decr p) l).
Proof.
 intros. rewrite <- renorm_sum.
 rewrite fs_sumA; auto with arith hof.
 apply renorm_mapdecr; lia.
Qed.

(** Extending theorem [fs_decomp] to larger iterates than [p <= S q] *)

Definition succrank q n :=
  match rank q n with
  | None => 0
  | Some r => S r
  end.

Lemma f_succrank q n : succrank q n <= S (succrank q (f q n)).
Proof.
 unfold succrank, rank. rewrite decomp_f.
 assert (H := renorm_head q (map pred (decomp q n))).
 destruct decomp as [|r l], renorm as [|r' l']; simpl in *; try lia.
 destruct H as (m, H). lia.
Qed.

Lemma fs_decomp_gen q p n : n = 0 \/ p <= q + succrank q n ->
 fs q p n = sumA q (map (decr p) (decomp q n)).
Proof.
 intros [->|H].
 - simpl. induction p; simpl; now rewrite ?IHp.
 - revert n H.
   induction p; intros.
   + simpl. now rewrite map_decr_0, decomp_sum.
   + rewrite iter_S, IHp; clear IHp.
     2:{ generalize (f_succrank q n); lia. }
     rewrite decomp_f.
     unfold succrank, rank in H.
     assert (D := decomp_delta q n).
     destruct decomp as [|r l]; trivial.
     destruct (Nat.eq_dec r 0) as [->|R].
     * rewrite renorm_mapdecr by lia.
       f_equal. symmetry. apply map_decr_S.
     * rewrite renorm_nop.
       { f_equal. symmetry. apply map_decr_S. }
       { apply Delta_pred; trivial.
         eapply Delta_nz; eauto with hof. lia. }
Qed.

(** Zone where [f q n = n-1].
    Note that [f q n] cannot be [n] or more except when [n<=1], see [f_lt].
    The conditions below are optimal, see [f_subid_inv] later. *)

Lemma f_subid q n : n<>1 -> n <= q+3 -> f q n = n-1.
Proof.
 intros Hn Hn'.
 destruct (Nat.eq_dec n 0).
 - subst. now rewrite f_q_0.
 - apply f_init; lia.
Qed.


(** Some particular cases : early diagonals *)

Lemma f_q_q q : q<>1 -> f q q = q-1.
Proof.
 intros. apply f_subid; lia.
Qed.

Lemma f_q_Sq q : q<>0 -> f q (S q) = q.
Proof.
 intros. rewrite f_subid; lia.
Qed.

Lemma f_q_plus_2 q : f q (2+q) = S q.
Proof.
 rewrite f_subid; lia.
Qed.

Lemma f_q_plus_3 q : f q (3+q) = 2+q.
Proof.
 rewrite f_subid; lia.
Qed.

Lemma f_q_plus_4 q : f q (4+q) = 2+q.
Proof.
 replace (4+q) with (sumA q [S (S q)]).
 2:{ cbn -[A]. rewrite A_S.
     replace (S q - q) with 1 by lia.
     rewrite !A_base; lia. }
 rewrite f_sumA; autoh. cbn -[A]. rewrite A_base; lia.
Qed.

Lemma f_q_plus_5 q : f q (5+q) = 3+q.
Proof.
 replace (5+q) with (sumA q [0;S (S q)]).
 2:{ cbn -[A]. rewrite A_S.
     replace (S q - q) with 1 by lia.
     rewrite !A_base; lia. }
 rewrite f_sumA; autoh. cbn -[A]. rewrite !A_base; lia.
Qed.

Lemma f_q_plus_6 q : f q (6+q) = 3+q.
Proof.
 replace (6+q) with (sumA q [1;S (S q)]).
 2:{ cbn -[A]. rewrite (A_S q (S q)).
     replace (S q - q) with 1 by lia.
     rewrite !A_base; lia. }
 rewrite f_sumA; autoh. cbn -[A]. rewrite !A_base; lia.
Qed.

Lemma f_q_plus_7 q : f q (7+q) = 4+q.
Proof.
 destruct (Nat.eq_dec q 0) as [->|Hq]. now compute.
 replace (7+q) with (sumA q [2;S (S q)]).
 2:{ cbn -[A]. rewrite (A_S q (S q)).
     replace (S q - q) with 1 by lia.
     rewrite !A_base; lia. }
 rewrite f_sumA_lax; autoh. cbn -[A]. rewrite !A_base; lia.
Qed.

Lemma f_subid_inv q n : f q n = n-1 -> n <> 1 /\ n <= q+3.
Proof.
 intros E. split.
 - intros ->. rewrite f_q_1 in E. discriminate.
 - rewrite Nat.le_ngt. intros LT.
   generalize (f_lipschitz q (4+q) n).
   rewrite f_q_plus_4, E. lia.
Qed.

(** Summarize some of the last results (note that [f 0 p = (p+1)/2]). *)

Lemma f_q_plus_some q p : 2 <= p <= 7 -> f q (q+p) = q + f 0 p.
Proof.
 intros Hp. rewrite !(Nat.add_comm q).
 destruct (Nat.eq_dec p 2) as [->|N2]. apply f_q_plus_2.
 destruct (Nat.eq_dec p 3) as [->|N3]. apply f_q_plus_3.
 destruct (Nat.eq_dec p 4) as [->|N4]. apply f_q_plus_4.
 destruct (Nat.eq_dec p 5) as [->|N5]. apply f_q_plus_5.
 destruct (Nat.eq_dec p 6) as [->|N6]. apply f_q_plus_6.
 destruct (Nat.eq_dec p 7) as [->|N7]. apply f_q_plus_7.
 lia.
Qed.

(** Decomposition and positions in the F tree *)

Lemma rchild_decomp q n :
 rchild q n = sumA q (map S (decomp q n)).
Proof.
 unfold rchild.
 rewrite fs_decomp; auto.
 rewrite <- (@decomp_sum q n) at 1.
 remember (decomp q n) as l.
 apply sumA_eqn.
Qed.

Lemma flat_rank_0 q n :
 f q (S n) = f q n <-> rank q n = Some 0.
Proof.
 rewrite !f_decomp.
 unfold rank.
 rewrite decomp_S.
 destruct (decomp q n) as [|a l] eqn:E.
 - simpl; now split.
 - simpl.
   case Nat.leb_spec; intros.
   + rewrite <- !map_decr_1.
     rewrite renormS_alt, renorm_mapdecr'.
     * simpl.
       rewrite decr_0.
       rewrite !A_base by (auto; lia).
       split. intros; f_equal; lia. intros [= ->]; lia.
     * apply Delta_S_cons. rewrite <- E; autoh.
     * simpl. destruct q; lia.
     * rewrite <- E. autoh.
   + simpl. split. intros; f_equal; lia. intros [= ->]; lia.
Qed.

Lemma step_rank_nz q n :
 f q (S n) = S (f q n) <-> rank q n <> Some 0.
Proof.
 rewrite <- flat_rank_0.
 generalize (f_step q n). lia.
Qed.

Lemma steps_ranks_nz q n p :
 f q (n+p) = f q n + p <-> (forall a, a<p -> rank q (n+a) <> Some 0).
Proof.
 induction p.
 - rewrite !Nat.add_0_r. intuition lia.
 - rewrite !Nat.add_succ_r.
   split.
   + intros E a Hq.
     assert (LE := f_le_add q p n). rewrite (Nat.add_comm p n) in LE.
     assert (LE' := f_le_add q 1 (n+p)). simpl in LE'.
     inversion Hq.
     * subst a. apply step_rank_nz. lia.
     * apply IHp; try lia.
   + intro H.
     assert (R : rank q (n+p) <> Some 0) by (apply H; lia).
     apply step_rank_nz in R. rewrite R. f_equal.
     apply IHp. intros a Ha. apply H. lia.
Qed.

(** At most [q+1] consecutive [+1] steps *)

Lemma f_maxsteps q n :
 f q (n+q+2) <= f q n + q+1.
Proof.
 destruct (rank_later_is_zero q n) as (p & LE & H).
 apply flat_rank_0 in H.
 transitivity (f q (S (p + n)) + (q+2-S p)).
 - generalize (f_lipschitz q (S (p+n)) (n+q+2)). lia.
 - rewrite H.
   generalize (f_lipschitz q n (p+n)). lia.
Qed.

(** A first example of such [q+1] consecutive [+1] steps : [n=2] *)

Lemma f_maxsteps_example2 q : f q (2+S q) = f q 2 + S q.
Proof.
 rewrite f_q_2. simpl. apply f_q_plus_3.
Qed.

(** More generally, [q+1] consecutive [+1] steps for numbers [2+n]
    when [n=0] or [rank q n > 2q]. *)

Lemma f_maxsteps_examples q n :
  (forall r, rank q n = Some r -> 2*q < r) ->
  f q ((2+n) + S q) = f q (2+n) + S q.
Proof.
 intros Hr.
 destruct (rank q n) as [r|] eqn:Hn.
 2:{ rewrite rank_none in Hn; subst n. apply f_maxsteps_example2. }
 specialize (Hr r eq_refl).
 apply steps_ranks_nz.
 intros a Ha. replace (2+n+a) with (S (S a) + n) by lia.
 rewrite <- (@A_base q (S a)) by lia.
 rewrite <- (decomp_sum q n).
 change (_+_) with (sumA q (S a::decomp q n)).
 unfold rank in *. rewrite <- renorm_sum, decomp_sum'.
 - generalize (renorm_head q (S a::decomp q n)). unfold HeadStep.
   destruct renorm as [|u l]; try easy. intros (b & ->) [= E].
 - apply renorm_delta. assert (D := decomp_delta q n).
   destruct decomp as [|u l]; try easy.
   injection Hn as ->. constructor; autoh.
Qed.

(* No other situations with [q+1] consecutive [+1] steps,
   except [f 0 1 = 1 + f 0 0]. *)

Lemma f_maxsteps_carac_aux q n r :
  rank q n = Some r -> S q <= r <= 2*q ->
  exists r', rank q (n+2+(r-S q)) = Some r' /\ r < r'.
Proof.
 intros Hn Hr.
 assert (E : forall a, a <= r-S q -> decomp q (n + S a) = a :: decomp q n).
 { intros a Ha. rewrite <- (@A_base q a) by lia.
   unfold rank in *. rewrite <- (decomp_sum q n) at 1.
   rewrite Nat.add_comm.
   change (_+_) with (sumA q (a::decomp q n)).
   apply decomp_sum'.
   assert (D := decomp_delta q n).
   destruct decomp as [|u l]; try easy.
   injection Hn as ->. constructor; auto. lia. }
 assert (LE : r-S q <= r-S q) by lia.
 specialize (E (r-S q) LE). clear LE.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l in E.
 unfold rank in *.
 destruct (decomp q n) as [|r' l] eqn:E'; try easy. injection Hn as ->.
 assert (E2 : decomp q (n+2 + (r-S q)) = renormS q r l).
 { rewrite !Nat.add_succ_r, Nat.add_0_r, Nat.add_succ_l.
   rewrite decomp_S, E. simpl.
   case Nat.leb_spec; try lia. intros _.
   case Nat.eqb_spec; trivial; lia. }
 rewrite E2.
 assert (H := renormS_head q r l).
 red in H. destruct renormS; try easy.
 destruct H as (a & ->). exists (S r + a*S q). split; auto. lia.
Qed.

Lemma f_maxsteps_carac q n :
  f q (n + S q) = f q n + S q <->
  (q=0 /\ n=0) \/ (2<=n /\ forall r, rank q (n-2) = Some r -> 2*q < r).
Proof.
 split.
 - intros E.
   destruct (Nat.le_gt_cases n 1) as [LE|LT].
   + left.
     destruct (Nat.eq_dec n 0) as [->|N].
     * rewrite f_q_0 in E. apply f_fix in E. lia.
     * replace n with 1 in * by lia. rewrite f_q_1 in *.
       apply f_fix in E. lia.
   + right.
     split; [lia| ].
     intros r Hr.
     rewrite steps_ranks_nz in E.
     apply Nat.lt_nge. intros LE.
     destruct (Nat.le_gt_cases r q) as [LE'|GT].
     * destruct (rank_later_is_zero q (n-1)) as (a & Ha & R).
       destruct (Nat.eq_dec a 0).
       { subst a. simpl in *.
         apply rank_next_high in Hr; auto. destruct Hr as (m & Hr).
         replace (S (n-2)) with (n-1) in Hr by lia.
         rewrite Hr in R. now injection R. }
       { apply (E (a-1)). lia.
         rewrite <- R. f_equal. lia. }
     * destruct (@f_maxsteps_carac_aux q (n-2) r Hr) as (a & Ha & Hq'); try lia.
       replace (n-2+2) with n in Ha by lia.
       apply (E (r-q)). lia.
       replace (n+(r-q)) with (S (n+(r-S q))) by lia.
       eapply rank_next_0; eauto. lia.
 - intros [(->,->) | (LE & H)].
   + reflexivity.
   + replace n with (2+(n-2)) by lia. apply f_maxsteps_examples; auto.
Qed.

(** Other characterization of max [+1] steps :
    the last term in the [+1] sequence is decomposed as [0;a*(S q);...]
    where [a<>0]. *)

Lemma f_steps_sub q n p :
 rank q n = Some (S p) -> p <= q -> f q (n - p) = f q n - p.
Proof.
 revert n.
 induction p.
 - intros n R. rewrite Nat.sub_0_r. lia.
 - intros n R Hp.
   assert (R' : rank q (n-1) = Some (S p)).
   { apply rank_pred in R; auto. simpl "-" in R.
     rewrite Nat.mod_small in R; auto; lia. }
   replace (n-S p) with (n-1-p) by lia.
   rewrite IHp; auto; try lia.
   assert (R0 : rank q (n-1) <> Some 0) by now rewrite R'.
   rewrite <- step_rank_nz in R0.
   destruct n as [|n].
   + reflexivity.
   + simpl in *. rewrite Nat.sub_0_r in *. lia.
Qed.

Lemma f_maxsteps_examples_alt q n a :
 rank q n = Some ((S a)*(S q)) ->
 f q ((n+1) - S q) = f q (n+1) - S q.
Proof.
 destruct (Nat.eq_dec q 0) as [->|Hq].
 - intros R. rewrite Nat.mul_1_r in R.
   replace (n+1-1) with n by lia.
   rewrite Nat.add_1_r.
   assert (R' : rank 0 n <> Some 0) by now rewrite R.
   rewrite <- step_rank_nz in R'. lia.
 - intros R.
   assert (R' : rank q n <> Some 0) by now rewrite R.
   rewrite <- step_rank_nz in R'.
   destruct (Nat.eq_dec n 0) as [->|Hn].
   + simpl. apply f_q_0.
   + assert (Rm : rank q (n-1) = Some q).
     { apply rank_pred in R. 2:(simpl; lia).
       replace (S a * S q - 1) with (q + a * (S q)) in R by lia.
       rewrite Nat.mod_add in R; auto.
       rewrite Nat.mod_small in R; auto; lia. }
     replace (n+1 - S q) with (n-1-(q-1)) by lia.
     rewrite f_steps_sub; try lia.
     2:rewrite Rm; f_equal; lia.
     assert (Rm' : rank q (n-1) <> Some 0) by (rewrite Rm; congruence).
     rewrite <- step_rank_nz in Rm'.
     rewrite Nat.add_1_r.
     replace (S (n-1)) with n in Rm'; lia.
Qed.

(** More about [fs q p], in particular when is it flat or not *)

Lemma fs_S_decomp q p n : p < succrank q n ->
 fs q p (S n) = sumA q (map (decr p) (decomp q (S n))).
Proof.
 unfold succrank, rank. rewrite decomp_S.
 destruct (decomp q n) as [|r l] eqn:E; simpl.
 - inversion 1.
 - intros Hp. case Nat.leb_spec; intros.
   + rewrite fs_decomp by lia. rewrite decomp_S, E. simpl.
     apply Nat.leb_le in H. now rewrite H.
   + revert p Hp.
     assert (D1 : forall m, m + S q <= r ->
                  Delta (S q) (map (decr m) (0 :: r :: l))).
     { intros m Hm. simpl. constructor. unfold decr; lia.
       apply (@Delta_map_decr _ _ (r::l)).
       - intros x IN. assert (D := decomp_delta q n).
         rewrite E in D. simpl in IN. destruct IN as [<-|IN]; try lia.
         apply Delta_le with (y:=x) in D; trivial. lia.
       - rewrite <- E. apply decomp_delta. }
     assert (E1 : forall m, m + S q <= r ->
                  fs q m (S n) = sumA q (map (decr m) (0::r::l))).
     { induction m.
       - rewrite map_decr_0. simpl Nat.iter.
         rewrite <- (decomp_sum q (S n)), decomp_S, E. f_equal.
         simpl. case Nat.leb_spec; trivial; lia.
       - simpl Nat.iter. intros Hm. rewrite IHm by lia. clear IHm.
         rewrite f_decomp.
         erewrite decomp_carac; [|apply (D1 m); lia|trivial].
         now rewrite map_decr_S'. }
     assert (E2 : forall m, m + S q <= r ->
                  decomp q (fs q m (S n)) = map (decr m) (0::r::l)).
     { intros m Hm. rewrite E1 by trivial. apply decomp_carac; auto. }
     clear D1 E1.
     assert (E3 : decomp q (fs q (r-q) (S n)) =
                  renorm q (S q :: map (decr (r-q)) l)).
     { replace (r-q) with (S (r-S q)) by lia. simpl Nat.iter.
       rewrite decomp_f, E2 by lia. rewrite <- map_decr_S'.
       simpl. unfold decr at 1. replace (r-_) with q by lia.
       replace (S (r-_)) with (r-q) by lia. apply renorm_low.
       replace q with (r-(r-q)) at 2 by lia.
       apply (@Delta_map_decr _ _ (r::l)).
       - intros x IN. assert (D := decomp_delta q n). rewrite E in D.
         simpl in IN. destruct IN as [<-|IN]; try lia.
         apply Delta_le with (y:=x) in D; trivial. lia.
       - rewrite <- E. apply decomp_delta. }
     intros p Hp.
     destruct (Nat.le_gt_cases p (r-S q)) as [LE|LT].
     * rewrite <- E2 by lia. now rewrite decomp_sum.
     * replace p with ((p+q-r)+(r-q)) by lia.
       rewrite iter_add. rewrite fs_decomp by lia.
       rewrite E3. rewrite renorm_mapdecr'; try (simpl; lia).
       { replace (S q) with (decr (r-q) (S r)) by (unfold decr; lia).
         rewrite (map_decr_decr _ (r-q) (S r::l)).
         replace (p+q-r+_) with p by lia; cbn -[decr sumA].
         replace (decr p (S r)) with (S (r-p)) by (unfold decr; lia).
         simpl. unfold decr at 2. replace (r-p-q) with 0; simpl; lia. }
       { apply Delta_S_cons.
         replace q with (decr (r-q) r) at 2 by (unfold decr; lia).
         apply (@Delta_map_decr _ _ (r::l)).
         - intros x IN. assert (D := decomp_delta q n). rewrite E in D.
           simpl in IN. destruct IN as [<-|IN]; try lia.
           apply Delta_le with (y:=x) in D; trivial. lia.
         - rewrite <- E. apply decomp_delta. }
Qed.

Lemma fs_nonflat q p n : p < succrank q n -> fs q p (S n) <> fs q p n.
Proof.
 intros Hp.
 rewrite (@fs_decomp_gen q p n) by lia.
 rewrite fs_S_decomp by auto.
 rewrite decomp_S.
 unfold succrank, rank in Hp.
 destruct decomp as [|r l] eqn:E; simpl;
   try case Nat.leb_spec; intros; simpl; try lia.
 rewrite renormS_alt by (rewrite <- E; autoh).
 rewrite renorm_mapdecr'.
 - rewrite map_cons, sumA_cons.
   unfold decr at 1 3. rewrite !A_base; auto; lia.
 - apply Delta_S_cons. rewrite <- E. apply decomp_delta.
 - simpl. lia.
Qed.

Lemma fs_first_flat q p n :
  n<>0 -> p = succrank q n -> fs q p (S n) = fs q p n.
Proof.
 intros N P.
 rewrite <- (rank_none q) in N.
 unfold succrank, rank in *.
 destruct (decomp q n) as [|r l] eqn:E; try easy. clear N. subst.
 assert (D := decomp_delta q n). rewrite E in D.
 destruct (Nat.le_gt_cases r q) as [LE|LT].
 - rewrite !fs_decomp by lia.
   rewrite decomp_S, E. simpl. case Nat.leb_spec; try lia. intros _.
   rewrite renormS_alt by trivial.
   rewrite renorm_mapdecr'; auto with hof; try (unfold LeHd; lia).
   simpl. unfold decr at 1 3. f_equal. f_equal. lia.
 - rewrite (@fs_decomp_gen q (S r) n);
    unfold succrank, rank; rewrite E; try lia.
   simpl map. unfold decr at 1. replace (r - S r) with 0 by lia.
   simpl Nat.iter. rewrite fs_S_decomp;
    unfold succrank, rank; rewrite ?decomp_S, ?E; try lia.
   simpl next_decomp. case Nat.leb_spec; try lia. intros _.
   simpl map. unfold decr at 1. rewrite Nat.sub_diag. simpl.
   change (S (S _)) with (sumA q (1::map (decr r) l)).
   assert (D' : Delta (S q) (0 :: map (decr r) l)).
   { rewrite <- (Nat.sub_diag r). apply (@Delta_map_decr _ _ (r::l)); auto.
     intros x [->|IN]; trivial. eapply Delta_le in D; eauto. lia. }
   rewrite <- renormS_sum, renormS_alt by auto.
   rewrite f_sumA by auto with hof.
   rewrite <- map_decr_1.
   rewrite renorm_mapdecr'; auto with hof; try (unfold LeHd; lia).
   simpl. now rewrite map_decr_decr.
Qed.

Lemma fs_stays_flat q p p' n :
  fs q p (S n) = fs q p n -> p <= p' -> fs q p' (S n) = fs q p' n.
Proof.
 intros Hp. induction 1; trivial. simpl Nat.iter. now rewrite IHle.
Qed.

Lemma fs_flat_iff q p n :
  fs q p (S n) = fs q p n <-> n<>0 /\ succrank q n <= p.
Proof.
 split.
 - intros H. split.
   + contradict H. subst. rewrite fs_q_1, fs_q_0. lia.
   + apply Nat.le_ngt. contradict H. now apply fs_nonflat.
 - intros (N,Hp). apply fs_stays_flat with (succrank q n); trivial.
   now apply fs_first_flat.
Qed.

Lemma fs_nonflat_iff q p n :
  fs q p (S n) = S (fs q p n) <-> n=0 \/ p < succrank q n.
Proof.
 assert (LE := fs_lipschitz q p n (S n)).
 replace (S n - n) with 1 in LE by lia.
 generalize (@fs_mono q p n (S n)) (fs_flat_iff q p n). lia.
Qed.

Lemma fs_flat_iff' q p n :
  fs q p (S n) = fs q p n <->
  match rank q n with
  | None => False
  | Some r => r < p
  end.
Proof.
 rewrite fs_flat_iff. unfold succrank.
 rewrite <- (rank_none q).
 destruct rank; simpl; intuition; easy || lia.
Qed.

Lemma fs_nonflat_iff' q p n :
  fs q p (S n) = S (fs q p n) <->
  match rank q n with
  | None => True
  | Some r => p <= r
  end.
Proof.
 rewrite fs_nonflat_iff. unfold succrank.
 rewrite <- (rank_none q).
 destruct rank; simpl; intuition; easy || lia.
Qed.

(** [fs q p] cannot have more than [p+1] consecutive flats *)

Lemma fs_maxflat q n p : p <= S q ->
 fs q p n < fs q p (n+p+1).
Proof.
 intros Hp.
 destruct (rank q n) as [r|] eqn:Hr.
 - destruct (@rank_later_is_high q n r p Hp Hr) as (r' & a & H1 & H2 & H3).
   assert (E : fs q p (S (a+n)) = S (fs q p (a+n))).
   { apply fs_nonflat_iff; auto. right. unfold succrank. rewrite H2. lia. }
   unfold lt.
   transitivity (S (fs q p (a+n))).
   + apply -> Nat.succ_le_mono. apply fs_mono. lia.
   + rewrite <- E. apply fs_mono. lia.
 - rewrite rank_none in *. subst.
   rewrite fs_q_0. apply fs_nonzero. lia.
Qed.

(** Study of the "triangular" zone of f, coming after the "n-1" zone
    seen in [f_subid]. Here [n <= triangle(q+4)-3 = A q (2*q+3) - 1].

    But first, we define [steps], an invert of the [triangle] function. *)

Fixpoint steps n :=
 match n with
 | 0 => 0
 | S n => S (steps (n - steps n))
 end.

Lemma steps_lt a b :
 a < b -> a*(a+1) < b*(b+1).
Proof.
 intros. apply Nat.mul_lt_mono; lia.
Qed.

Lemma steps_inv_lt a b :
 a*(a+1) < b*(b+1) -> a < b.
Proof.
 intros LT.
 destruct (Nat.lt_ge_cases a b) as [H|H]; auto.
 apply Nat.lt_eq_cases in H. destruct H.
 - apply steps_lt in H. lia.
 - subst. lia.
Qed.

Lemma steps_inv_le a b :
 a*(a+1) <= b*(b+1) -> a <= b.
Proof.
 intros LE.
 destruct (Nat.le_gt_cases a b) as [H|H]; auto.
 apply steps_lt in H. lia.
Qed.

Lemma steps_uniqueness n a b :
 a*(a+1) <= 2*n < (a+1)*(a+2) ->
 b*(b+1) <= 2*n < (b+1)*(b+2) ->
 a = b.
Proof.
 intros (Ha,Ha') (Hb,Hb').
 assert (a <= b) by (apply Nat.lt_succ_r, steps_inv_lt; lia).
 assert (b <= a) by (apply Nat.lt_succ_r, steps_inv_lt; lia).
 lia.
Qed.

Lemma steps_spec n :
 let q := steps n in
 q*(q+1) <= 2*n < (q+1)*(q+2).
Proof.
 induction n as [[|n] IH] using lt_wf_ind.
 - clear IH. simpl. lia.
 - simpl steps.
   intros q.
   replace (2 * S n) with (2+2*n) by lia.
   assert (LT : n < S n) by lia.
   assert (IH1 := IH n LT).
   assert (LT' : n - steps n < S n) by lia.
   assert (IH2 := IH _ LT'). clear IH.
   set (p := steps n) in *.
   set (p' := steps (n-p)) in *.
   unfold q; clear q. cbv zeta in *.
   replace (2*(n-p)) with (2*n-2*p) in IH2 by lia.
   assert (p' <= p).
   { apply Nat.lt_succ_r. apply steps_inv_lt. lia. }
   assert (p <= S p').
   { destruct (Nat.eq_dec p 0).
     - clearbody p. subst p. auto with arith.
     - assert (p-1 < S p'); try lia.
       apply steps_inv_lt.
       replace (p-1+1) with p by lia.
       apply Nat.le_lt_trans with (2*n-2*p); lia. }
   replace (S p') with (p'+1) by lia.
   replace (p'+1+1) with (p'+2) by lia.
   replace (p'+1+2) with (p'+3) by lia.
   rewrite !Nat.mul_add_distr_l in *.
   rewrite !Nat.mul_add_distr_r in *. lia.
Qed.

Lemma steps_spec' n :
 triangle (steps n) <= n < triangle (S (steps n)).
Proof.
 destruct (steps_spec n) as (LE,LT).
 set (q := steps n) in *. clearbody q.
 split.
 - unfold triangle. apply Nat.div_le_upper_bound; auto.
 - clear LE.
   replace ((q+1)*(q+2)) with (S q * (S q + 1)) in * by lia.
   rewrite <- double_triangle in LT. lia.
Qed.

Lemma steps_altspec q p :
 p <= q -> steps (triangle q + p) = q.
Proof.
 intros LE.
 apply steps_uniqueness with (triangle q + p).
 apply steps_spec.
 replace ((q+1)*(q+2)) with (S q * (S q + 1)) by lia.
 rewrite <- !double_triangle, triangle_succ. lia.
Qed.

Lemma steps_triangle q : steps (triangle q) = q.
Proof.
 rewrite <- (Nat.add_0_r (triangle q)). apply steps_altspec. lia.
Qed.

Lemma steps_triangle_minus q p : 1 <= p <= q ->
 steps (triangle q - p) = q - 1.
Proof.
 destruct q.
 - reflexivity.
 - intros LE.
   rewrite triangle_succ.
   replace (triangle q + S q - p) with (triangle q + (S q - p)) by lia.
   rewrite steps_altspec; lia.
Qed.

Lemma steps_incr n m :
  n <= m -> steps n <= steps m.
Proof.
 intros LE. apply Nat.lt_succ_r.
 apply steps_inv_lt.
 apply Nat.le_lt_trans with (2*n). apply steps_spec.
 apply Nat.le_lt_trans with (2*m). lia.
 generalize (steps_spec m). simpl. lia.
Qed.

Lemma steps_step n : steps (S n) <= S (steps n).
Proof.
 assert (H := steps_spec' n).
 set (q := steps n) in *.
 destruct (Nat.leb_spec (S n - triangle q) q).
 - replace (S n) with (triangle q + (S n - triangle q)) by lia.
   rewrite steps_altspec; auto.
 - rewrite triangle_succ in H.
   replace (S n) with (triangle q + S q) by lia.
   rewrite <- triangle_succ, steps_triangle; auto.
Qed.

Lemma steps_le_id n : steps n <= n.
Proof.
 induction n; auto.
 transitivity (S (steps n)). apply steps_step. lia.
Qed.

Lemma steps_after n : steps (n + S (steps n)) = S (steps n).
Proof.
 assert (H := steps_spec' n).
 set (q := steps n) in *.
 rewrite triangle_succ in H.
 replace (n + S q) with (triangle q + S q + (n - triangle q)) by lia.
 rewrite <- triangle_succ.
 apply steps_altspec; auto. lia.
Qed.

(* The number [triangle(q+4)-3] (which is also [A q (2*q+3) -1]) is
   the lowest number with three terms in its q-decomp. Let's call it
   [quad q]. *)

Definition quad q := triangle (q+4)-3.

Lemma quad_S q : quad (S q) = quad q + (q+5).
Proof.
 unfold quad. replace (S q + 4) with (S (q+4)) by lia.
 rewrite triangle_succ. generalize (triangle_aboveid (q+4)). lia.
Qed.

Lemma quad_min q : 7 <= quad q.
Proof.
 induction q. easy. rewrite quad_S. lia.
Qed.

Lemma quad_alt q : quad q = A q (2*q+3) - 1.
Proof.
 unfold quad. rewrite A_2q3_tri. lia.
Qed.

Lemma quad_other_eqn q : quad q = (q+2)*(q+7)/2.
Proof.
 apply Nat.div_unique with 0; try lia. unfold quad.
 generalize (triangle_aboveid q) (double_triangle (q+4)). lia.
Qed.

Lemma quad_decomp q : decomp q (quad q) = [0;q+1;2*q+2].
Proof.
 apply decomp_carac; [ repeat constructor; lia | ].
 rewrite quad_alt, A_2q3_eqn. rewrite Nat.add_1_r. simpl; lia.
Qed.

Lemma decomp_len_lt_3 q n : n < quad q -> length (decomp q n) < 3.
Proof.
 intros LT.
 assert (E := decomp_sum q n).
 assert (D := decomp_delta q n).
 destruct (decomp q n) as [|a [|b [|c l]]]; simpl; try lia.
 exfalso.
 rewrite 2 Delta_alt in D. destruct D as ((_,D1),D2).
 specialize (D2 b (or_introl eq_refl)).
 specialize (D1 c (or_introl eq_refl)).
 assert (A q (S q) <= A q b) by (apply A_mono; lia).
 assert (A q (2*q + 2) <= A q c) by (apply A_mono; lia).
 simpl in E. rewrite quad_alt, A_2q3_eqn in LT.
 generalize (A_nz q a). lia.
Qed.

(* The numbers below [quad q] also have rank 0 only when
   they are 1 or a successor of a [A] number. That's the qey for describing
   the "triangular" zone of f. Graphical interpretation : the bottom
   of the tree, where binary nodes are on the left edge. *)

Lemma low_rank0 q n :
  1 < n < quad q -> rank q n = Some 0 ->
  exists p, p < 2*q+3 /\ n = S (A q p).
Proof.
 unfold rank.
 intros (Hn,Hn') Hr.
 assert (L := decomp_len_lt_3 q Hn').
 assert (E := decomp_sum q n).
 assert (D := decomp_delta q n).
 destruct (decomp q n) as [|a [|b [|c l]]]; simpl in L;
  try easy; injection Hr as ->; simpl in E; try lia.
 exists b. split; try lia.
 apply A_lt_inv with q. rewrite quad_alt in *. lia.
Qed.

Lemma A_plus2 q n : n <= q+2 -> A q n <= n+2.
Proof.
 rewrite Nat.lt_eq_cases. intros [LT | ->].
 - rewrite A_base; lia.
 - rewrite Nat.add_succ_r, A_S, A_base; try lia.
   replace (q+1-q) with 1 by lia. now rewrite A_q_1.
Qed.

Lemma f_triangle q n : n<>1 -> n <= quad q -> f q n = n-1 - steps (n-q-3).
Proof.
 induction n.
 - reflexivity.
 - intros NE LE.
   destruct (Nat.leb_spec (S n) (q+3)).
   + rewrite f_subid; auto.
     replace (S n - q - 3) with 0 by lia. simpl. lia.
   + destruct (f_step q n) as [E|E].
     * rewrite E.
       rewrite flat_rank_0 in E.
       destruct (@low_rank0 q n) as (p & Hp & Hp'); auto; try lia.
       assert (q < p).
       { apply A_lt_inv with q. rewrite A_base by lia. lia. }
       rewrite IHn; try lia.
       assert (steps (S n - q - 3) = S (steps (n - q - 3))); try lia.
       { replace p with (q+(p-q)) in Hp' by lia.
         rewrite A_triangle in Hp'; try lia.
         rewrite Hp'.
         replace (_ - q - 3) with (triangle (p-q)) by lia.
         rewrite steps_triangle.
         replace (_ - q - 3) with (triangle (p-q) - 1) by lia.
         rewrite steps_triangle_minus; lia. }
     * rewrite E.
       rewrite step_rank_nz in E.
       rewrite IHn; clear IHn; try lia.
       assert (LE' := steps_le_id (n-q-3)).
       assert (steps (S n - q - 3) = steps (n - q - 3)); try lia.
       { clear LE'.
         destruct (@A_inv' q n) as (p,Hp); try lia.
         assert (q < p).
         { rewrite Nat.succ_lt_mono.
           apply A_lt_inv with q. rewrite A_base; lia. }
         assert (p < 2*q+3).
         { apply A_lt_inv with q. rewrite quad_alt in *. lia. }
         assert (LE' : p - q <= q + 2) by lia.
         assert (T := A_triangle q LE').
         replace (q+(p-q)) with p in T by lia.
         assert (n <> S (A q p)).
         { intro E'. apply E.
           unfold rank. replace (decomp q n) with [0;p]; auto.
           symmetry. apply decomp_carac; simpl; try lia.
           constructor; autoh. }
         destruct (Nat.eq_dec (A q p) n) as [E'|NE'].
         - clear Hp.
           assert (S q < p).
           { apply A_lt_inv with q. rewrite A_base; lia. }
           rewrite E' in T. rewrite T.
           replace (_ - q - 3) with (triangle (p-q) - 1) by lia.
           replace (_ - q - 3) with (triangle (p-q) - 2) by lia.
           rewrite !steps_triangle_minus; lia.
         - rewrite A_S in Hp.
           set (t := triangle (p-q)) in *. apply A_plus2 in LE'.
           replace (n-q-3) with (t + (n-q-3-t)) by lia.
           replace (S n-q-3) with (t + (S n-q-3-t)) by lia.
           unfold t at 1 3. rewrite !steps_altspec; lia. }
Qed.

(* We hence have [f q n <= f (S q) n] when n is in
   this triangular zone. *)

Lemma f_triangle_diag_incr q n :
  n<>1 -> n <= quad q -> f (S q) (S n) = S (f q n).
Proof.
 intros Hn LE.
 destruct (Nat.eq_dec n 0).
 - subst. now rewrite f_q_0, f_q_1.
 - rewrite !f_triangle; try lia. simpl.
   generalize (steps_le_id (n-q-3)). lia.
   rewrite quad_S; lia.
Qed.

Lemma f_triangle_incrq q n : n <= quad q -> f q n <= f (S q) n.
Proof.
 destruct (Nat.eq_dec n 1) as [->|NE].
 - intros _. now rewrite !f_q_1.
 - intros LE.
   destruct (f_step (S q) n) as [E|E].
   + rewrite <- E. rewrite f_triangle_diag_incr; auto.
   + rewrite f_triangle_diag_incr in E; lia.
Qed.

Lemma f_last_triangle_1 q n : n = quad q -> f q n = n - q - 3.
Proof.
 intros EQ.
 destruct (Nat.eq_dec n 1) as [->|NE].
 - exfalso. destruct q; try easy. rewrite quad_S in *. lia.
 - rewrite f_triangle by lia.
   rewrite EQ at 2. unfold quad.
   rewrite Nat.add_succ_r, triangle_succ.
   replace (triangle _ + _ - _ - _ - _)
     with (triangle (q+3) - 2) by lia.
   rewrite steps_triangle_minus; lia.
Qed.

Lemma f_last_triangle_2 q n : n = quad q -> f (S q) n = n - q - 3.
Proof.
 intros EQ.
 destruct (Nat.eq_dec n 1) as [->|NE].
 - exfalso. destruct q; try easy. rewrite quad_S in *. lia.
 - rewrite f_triangle; try lia.
   2:{ simpl. rewrite quad_S. lia. }
   rewrite EQ at 2.
   unfold quad. rewrite Nat.add_succ_r, triangle_succ.
   replace (triangle _ + _ - _ - _ - _)
     with (triangle (q+3) - 3) by lia.
   rewrite steps_triangle_minus; lia.
Qed.

(* Experimentally, this border of the triangle zone [n = triangle(q+4)-3]
   seems to be the last point where [f q n = f (S q) n].
   Conjecture : [forall m, triangle(q+4)-3 < m -> f q m < f (S q) m].
   Proof: ?! (TODO) *)

Lemma fq_fSq_last_equality q n :
 n = quad q -> f q n = f (S q) n.
Proof.
  intros EQ. now rewrite f_last_triangle_1, f_last_triangle_2.
Qed.

Lemma fq_fSq_conjectures q :
 (forall m, quad q < m -> f q m < f (S q) m) ->
 (forall n, n<>1 -> f q n < f (S q) (S n)).
Proof.
 intros C1 n Hn.
 destruct (Nat.ltb_spec (quad q) n) as [LT|LE].
 - apply C1 in LT. eapply Nat.lt_le_trans; eauto. apply f_mono; lia.
 - rewrite f_triangle_diag_incr; auto.
Qed.

(* [quad q] also appears to be the last point of equality between
   [rchild (q+1)] and [rchild (q+2)]. *)

Lemma quad_decomp_Sq q : decomp (S q) (quad q) = [q+1; 2*q+3].
Proof.
 apply decomp_carac; [ repeat constructor; lia | ].
 cbn - ["*" "/"].
 rewrite A_base by lia.
 replace (2*q+3) with (S q + (q+2)) by lia. rewrite A_triangle by lia.
 unfold quad. replace (q+4) with (S (S (q+2))); rewrite ?triangle_succ; lia.
Qed.

Lemma quad_decomp_SSq q : decomp (S (S q)) (quad q) = [q; 2*q+4].
Proof.
 apply decomp_carac; [ repeat constructor; lia | ].
 cbn - ["*" "/"].
 rewrite A_base by lia.
 replace (2*q+4) with (S (S q) + (q+2)) by lia.
 rewrite A_triangle by lia.
 unfold quad. replace (q+4) with (S (S (q+2))); rewrite ?triangle_succ; lia.
Qed.

Lemma rchild_Sq_quad q : rchild (S q) (quad q) = quad (S q) -1.
Proof.
 rewrite rchild_decomp, quad_decomp_Sq.
 rewrite <- (decomp_sum (S q) (quad (S q))), quad_decomp.
 cbn - ["*" "/" A]. replace (2*S q +2) with (S (2*q+3)); simpl; lia.
Qed.

Lemma rchild_SSq_quad q : rchild (S (S q)) (quad q) = quad (S q) -1.
Proof.
 rewrite rchild_decomp, quad_decomp_SSq.
 rewrite <- (decomp_sum (S (S q)) (quad (S q))), quad_decomp_Sq.
 cbn - ["*" "/" A]. replace (2*S q +3) with (S (2*q+4)) by lia.
 rewrite Nat.add_1_r. rewrite (@A_S (S (S q)) (S q)).
 replace (S q - S (S q)) with 0 by lia. simpl; lia.
Qed.

Lemma rchild_Sq_SSq_last_equality q n :
 n = quad q -> rchild (S q) n = rchild (S (S q)) n.
Proof.
 intros ->. now rewrite rchild_Sq_quad, rchild_SSq_quad.
Qed.

(* Some particular cases after the limit of the triangular zone *)

Lemma rchild_Sq_Squad q : rchild (S q) (S (quad q)) = S (quad (S q)).
Proof.
 rewrite rchild_decomp, decomp_S, quad_decomp_Sq. simpl.
 case Nat.leb_spec; try lia; intros _.
 case Nat.eqb_spec; try lia; intros _.
 rewrite quad_alt. simpl map. replace (S (S (_+3))) with (2*S q+3) by lia.
 cbn - ["*"]. generalize (@A_nz (S q) (2*S q+3)); lia.
Qed.

Lemma rchild_SSq_Squad q : rchild (S (S q)) (S (quad q)) = quad (S q).
Proof.
 rewrite rchild_decomp, decomp_S, quad_decomp_SSq. simpl.
 case Nat.leb_spec; try lia; intros _.
 case Nat.eqb_spec; try lia; intros _.
 rewrite <- (decomp_sum (S (S q)) (quad (S q))), quad_decomp_Sq.
 do 3 (f_equal; simpl; try lia).
Qed.

Lemma rchild_Sq_SSq_post_equality q n :
 n = S (quad q) -> rchild (S q) n = S (rchild (S (S q)) n).
Proof.
 intros ->. now rewrite rchild_Sq_Squad, rchild_SSq_Squad.
Qed.

Lemma f_after_triangle_1 q n :
 n = S (quad q) -> f q n = n - q - 4.
Proof.
 rewrite quad_alt.
 replace (S (_ -1)) with (A q (2*q+3))
  by (generalize (@A_nz q (2*q+3)); lia).
 intros ->. rewrite f_A. rewrite A_2q3_eqn.
 rewrite (@A_base q (S q)) by lia.
 replace (2*q+3-1) with (2*q+2); lia.
Qed.

Lemma f_after_triangle_2 q n :
 n = S (quad q) -> f q (S n) = n - q - 3.
Proof.
 rewrite quad_alt.
 replace (S (_ -1)) with (A q (2*q+3))
  by (generalize (@A_nz q (2*q+3)); lia).
 intros ->. rewrite f_SA; try lia.
 rewrite A_2q3_eqn.
 rewrite (@A_base q (S q)) by lia.
 replace (2*q+3-1) with (2*q+2); lia.
Qed.

Lemma f_after_triangle_3 q n :
 n = S (quad q) -> f (S q) n = n - q - 3.
Proof.
 intros E.
 rewrite f_triangle.
 2:{ rewrite E. destruct q; try easy. rewrite quad_S; lia. }
 2:{ rewrite quad_S. lia. }
 rewrite E at 2.
 unfold quad. rewrite Nat.add_succ_r, triangle_succ.
 replace (_ - S q - 3) with (triangle (q+3) -2)
  by (generalize (triangle_aboveid (q+3)); lia).
 rewrite steps_triangle_minus; lia.
Qed.

Lemma f_after_triangle_4 q n :
 n = S (quad q) -> f (S q) (S n) = n - q - 2.
Proof.
 intros E.
 rewrite f_triangle.
 2:{ lia. }
 2:{ rewrite quad_S. lia. }
 rewrite E at 2.
 unfold quad. rewrite Nat.add_succ_r, triangle_succ.
 replace (_ - S q - 3) with (triangle (q+3) -1) by lia.
 rewrite steps_triangle_minus; lia.
Qed.

(** Another observation : [quad (S q)] is where [f q] and [f (S q)]
    differ by 2 for the first time *)

Lemma quadS_decomp q : decomp q (quad (S q)) = [q+2;2*q+3].
Proof.
 apply decomp_carac.
 - repeat constructor. lia.
 - rewrite quad_S. rewrite <- (decomp_sum q (quad q)), quad_decomp.
   replace (q+2) with (S (q+1)) by lia.
   replace (2*q+3) with (S (2*q+2)) by lia.
   set (qq2 := 2*q+2). simpl.
   replace (qq2-q) with (S (q+1)) by lia. simpl.
   replace (q+1-q) with 1 by lia. simpl.
   rewrite (@A_base q (q+1)) by lia. lia.
Qed.

Lemma f_Sq_quadSq q : f (S q) (quad (S q)) = S (quad q).
Proof.
 rewrite f_last_triangle_1, quad_S by trivial. lia.
Qed.

Lemma f_q_quadSq q : f q (quad (S q)) = quad q - 1.
Proof.
 rewrite f_decomp, quadS_decomp.
 replace (q+2) with (S (q+1)) by lia.
 replace (2*q+3) with (S (2*q+2)) by lia. simpl.
 rewrite <- (decomp_sum q (quad q)), quad_decomp. simpl. lia.
Qed.

Lemma f_quad_diff_2 q n :
 n = quad (S q) -> f (S q) n = 2 + f q n.
Proof.
 intros ->. rewrite f_Sq_quadSq, f_q_quadSq. generalize (quad_min q). lia.
Qed.

(* TODO:
Lemma f_quad_first_diff_2 q n :
 n < quad (S q) -> f (S q) n <= 1 + f q n.
Proof.
Admitted.
*)

(** * Another equation about [f]

    This one will be used later when flipping [F] left/right. *)

Lemma f_alt_eqn q n : f q n + fs q q (f q (S n) - 1) = n.
Proof.
 destruct (Nat.eq_dec n 0) as [-> |Hn].
 - simpl. now rewrite fs_q_0.
 - assert (Hn' := f_nz q Hn).
   case (f_step q n) as [H|H].
   + (* n left child of a binary node *)
     rewrite H.
     generalize (f_eqn q (n-1)).
     case (f_step q (n - 1));
     replace (S (n - 1)) with n by lia.
     * generalize (@f_max_two_antecedents q (n-1) (S n)). lia.
     * intros. replace (f q n - 1) with (f q (n-1)) by lia.
       rewrite iter_S in *. lia.
   + (* n is rightmost child *)
     generalize (f_eqn q n).
     rewrite H, S_sub_1, <- iter_S.
     now injection 1.
Qed.


(** * Depth in the [f] tree *)

(** The depth of a node in the [f] tree is the number of
    iteration of [g] needed before reaching node 1 *)

Fixpoint depth_loop q n cpt :=
 match cpt with
 | 0 => 0
 | S cpt' =>
   match n with
   | 0 => 0
   | 1 => 0
   | _ => S (depth_loop q (f q n) cpt')
   end
 end.

Definition depth q n := depth_loop q n n.

Lemma depth_loop_ok q n c c' :
  n <= c -> n <= c' -> depth_loop q n c = depth_loop q n c'.
Proof.
 revert n c'.
 induction c as [|c IH]; destruct c' as [|c']; simpl; auto.
 - now inversion 1.
 - now inversion 2.
 - intros. destruct n as [|[|n]]; auto.
   f_equal. apply IH.
   + generalize (@f_lt q (S (S n))). lia.
   + generalize (@f_lt q (S (S n))). lia.
Qed.

Lemma depth_0 q : depth q 0 = 0.
Proof.
 reflexivity.
Qed.

Lemma depth_1 q : depth q 1 = 0.
Proof.
 reflexivity.
Qed.

Lemma depth_SS q n : depth q (S (S n)) = S (depth q (f q (S (S n)))).
Proof.
 unfold depth.
 remember (S n) as m.
 simpl depth_loop at 1. rewrite Heqm at 1.
 f_equal. apply depth_loop_ok; auto.
 generalize (@f_lt q (S m)). lia.
Qed.

Lemma depth_eqn q n : 1<n -> depth q n = S (depth q (f q n)).
Proof.
 destruct n as [|[|n]].
 - lia.
 - lia.
 - intros _. apply depth_SS.
Qed.

Lemma f_depth q n : depth q (f q n) = depth q n - 1.
Proof.
 destruct (le_lt_dec n 1) as [LE|LT].
 - assert (H : n=0 \/ n=1) by lia.
   destruct H as [-> | ->]; simpl; now rewrite ?f_q_0, ?f_q_1.
 - rewrite (depth_eqn q LT). lia.
Qed.

Lemma fs_depth q p n : depth q (fs q p n) = depth q n - p.
Proof.
 induction p; simpl.
 - lia.
 - rewrite f_depth, IHp. lia.
Qed.

Lemma depth_correct q n : n <> 0 -> fs q (depth q n) n = 1.
Proof.
 induction n as [[|[|n]] IH] using lt_wf_rec.
 - lia.
 - reflexivity.
 - intros _. rewrite depth_SS.
   set (n' := S (S n)) in *. rewrite iter_S. apply IH.
   + apply f_lt. unfold n'; lia.
   + apply f_nz. unfold n'; lia.
Qed.

Lemma depth_minimal q n : 1<n -> 1 < fs q (depth q n - 1) n.
Proof.
 induction n as [[|[|n]] IH] using lt_wf_rec.
 - lia.
 - lia.
 - intros _. rewrite depth_SS.
   simpl. rewrite Nat.sub_0_r.
   set (n' := S (S n)) in *.
   destruct (Nat.eq_dec (f q n') 1) as [->|NE].
   + simpl. unfold n'; lia.
   + assert (H : f q n' <> 0) by (apply f_nz; unfold n'; lia).
     assert (depth q (f q n') <> 0).
     { intro EQ. generalize (depth_correct q H). now rewrite EQ. }
     replace (depth q (f q n')) with (S (depth q (f q n') - 1)) by lia.
     rewrite iter_S.
     apply IH.
     * apply f_lt. unfold n'; lia.
     * lia.
Qed.

Lemma depth_mono q n m : n <= m -> depth q n <= depth q m.
Proof.
 revert m.
 induction n as [[|[|n]] IH] using lt_wf_rec; intros m H.
 - change (depth q 0) with 0. auto with arith.
 - change (depth q 1) with 0. auto with arith.
 - destruct m as [|[|m]]; try lia.
   rewrite 2 depth_SS.
   apply le_n_S.
   apply IH.
   + apply f_lt. lia.
   + now apply f_mono.
Qed.

Lemma depth_A q p : depth q (A q p) = p.
Proof.
 induction p as [|p IH].
 - reflexivity.
 - rewrite depth_eqn.
   + now rewrite f_A, S_sub_1, IH.
   + change 1 with (A q 0). apply A_lt. auto with arith.
Qed.

Lemma depth_SA q p : depth q (S (A q p)) = S p.
Proof.
 induction p as [|p IH].
 - simpl. unfold depth. simpl. rewrite f_init; simpl; lia.
 - rewrite depth_eqn.
   + rewrite f_SA, S_sub_1. f_equal. apply IH.
     auto with arith.
   + generalize (@A_nz q (S p)). lia.
Qed.

Lemma depth_is_0 q n : depth q n = 0 <-> n <= 1.
Proof.
 destruct n as [|[|n]].
 - rewrite depth_0; intuition.
 - rewrite depth_1; intuition.
 - rewrite depth_SS. lia.
Qed.

Lemma depth_carac q p n : p <> 0 ->
  (depth q n = p <-> S (A q (p-1)) <= n <= A q p).
Proof.
 intros Hp.
 split; intros H.
 - split.
   + destruct (le_lt_dec n (A q (p-1))) as [LE|LT]; trivial.
     apply (depth_mono q) in LE. rewrite depth_A in LE. lia.
   + destruct (le_lt_dec n (A q p)) as [LE|LT]; trivial.
     unfold lt in LT. apply (depth_mono q) in LT.
     rewrite depth_SA in LT; lia.
 - destruct H as (H1,H2).
   apply (depth_mono q) in H1. apply (depth_mono q) in H2.
   rewrite depth_A in H2. rewrite depth_SA in H1. lia.
Qed.

Lemma depth_init q n : depth q n = n-1 <-> n <= q+3.
Proof.
 destruct n as [|[|n]].
 - rewrite ?depth_0. lia.
 - rewrite ?depth_1. lia.
 - simpl.
   rewrite depth_carac by lia.
   rewrite S_sub_1.
   split; intros.
   + assert (A q n = S n) by (generalize (A_lt_id q n); lia).
     rewrite <- A_base_iff in *.
     lia.
   + simpl.
     rewrite A_base by lia.
     generalize (@A_nz q (n-q)). lia.
Qed.
