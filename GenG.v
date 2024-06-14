
Require Import MoreFun MoreList DeltaList GenFib.
Require FunG.
Import ListNotations.
Set Implicit Arguments.

(** Study of the functional equation:
     - [Fk 0 = 0]
     - [Fk (S n) + Fk^(k+1) (n) = S n]
    where [Fk^(k+1) (n)] is [k+1] repeated applications of [Fk] at [n].

    Note: using [k+1] instead of [k] iterations allows to avoid
     the case of [0] iterations, where Fk^0 is identity, and hence
     Fk (S n) = 1 always.

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
    - [F k n a] means that [Fk(n) = a].
    - [Fs k p n a] means that [Fk^p (n) = a].
*)

Inductive F (k:nat) : nat -> nat -> Prop :=
| F0 : F k 0 0
| FS n a b : Fs k (S k) n a -> S n = a+b -> F k (S n) b

with Fs (k:nat) : nat -> nat -> nat -> Prop :=
| Fs0 n : Fs k 0 n n
| FsS p a b c : Fs k p a b -> F k b c -> Fs k (S p) a c.

#[global] Hint Constructors F Fs : hof.

(** The early behavior of [F] and [Fs] when [n<=3] doesn't depend on k *)

Lemma Fs_0 k p : Fs k p 0 0.
Proof.
 induction p; eautoh.
Qed.
#[global] Hint Resolve Fs_0 : hof.

Lemma F_1 k : F k 1 1.
Proof.
 induction k; eautoh.
Qed.
#[global] Hint Resolve F_1 : hof.

Lemma Fs_1 k p : Fs k p 1 1.
Proof.
 induction p; eautoh.
Qed.
#[global] Hint Resolve Fs_1 : hof.

Lemma F_2 k : F k 2 1.
Proof.
 induction k; eautoh.
Qed.
#[global] Hint Resolve F_2 : hof.

Lemma Fs_2 k p : Fs k p 2 (1+(1-p)).
Proof.
 induction p; eautoh.
 simpl.
 eapply FsS. apply IHp. destruct p; simpl; autoh.
Qed.
#[global] Hint Resolve Fs_2 : hof.

Lemma F_3 k : F k 3 2.
Proof.
 induction k; eautoh.
Qed.
#[global] Hint Resolve F_3 : hof.

Lemma Fs_3 k p : Fs k p 3 (1+(2-p)).
Proof.
 induction p; eautoh.
 eapply FsS; eauto. destruct p as [|[|p]]; simpl; autoh.
Qed.
#[global] Hint Resolve Fs_3 : hof.

(** [F] and [Fs] aren't above the identity line *)

Lemma F_le k n a : F k n a -> a <= n.
Proof.
 induction 1; lia.
Qed.
#[global] Hint Resolve F_le : hof.

Lemma Fs_le k p n a : Fs k p n a -> a <= n.
Proof.
 induction 1; trivial.
 transitivity b; eautoh.
Qed.
#[global] Hint Resolve Fs_le : hof.

(** [F] and [Fs] are functional relations : unique output *)

Scheme F_ind2 := Induction for F Sort Prop
  with Fs_ind2  := Induction for Fs Sort Prop.

Combined Scheme F_Fs_ind from F_ind2, Fs_ind2.

Lemma F_Fs_fun k :
 (forall n a, F k n a -> forall a', F k n a' -> a = a') /\
 (forall p n a, Fs k p n a -> forall a', Fs k p n a' -> a = a').
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

Lemma F_fun k n a a' : F k n a -> F k n a' -> a = a'.
Proof.
 intro. now apply F_Fs_fun.
Qed.

Lemma Fs_fun k p n a a' : Fs p k n a -> Fs p k n a' -> a = a'.
Proof.
 intro. now apply F_Fs_fun.
Qed.

(** [F] does have an implementation : there exists a function [f]
    satisfying these equations. One possible trick to define [f]
    via Coq structural recursion is to add an extra parameter [p]:
    [recf k p] is [f k] below [p] and arbitrary above.
*)

Fixpoint recf k p n :=
 match p, n with
 | S p, S n => S n - ((recf k p)^^(S k)) n
 | _, _ => 0
 end.

Definition f k n := recf k n n.
Notation fs k p := (f k ^^p).

Lemma recf_le k p n : recf k p n <= n.
Proof.
 induction p; cbn - ["-" "^^"]. lia. destruct n; lia.
Qed.

Lemma recfs_le q k p n : ((recf k p)^^q) n <= n.
Proof.
 induction q; simpl; auto. etransitivity. apply recf_le. apply IHq.
Qed.

Lemma recf_sound k p n : n <= p -> F k n (recf k p n).
Proof.
revert n.
induction p.
- inversion 1. simpl. constructor.
- destruct n.
  + simpl. constructor.
  + cbn - ["-" "^^"].
    assert (IHq : forall q m, m <= p -> Fs k q m ((recf k p ^^ q) m)).
    { induction q; intros; simpl; econstructor; eauto.
      apply IHp. transitivity m; auto using recfs_le. }
    econstructor. apply IHq. lia.
    generalize (recfs_le (S k) k p n). lia.
Qed.

Lemma f_sound k n : F k n (f k n).
Proof.
 now apply recf_sound.
Qed.
#[global] Hint Resolve f_sound : hof.

Lemma f_complete k n a : F k n a <-> f k n = a.
Proof.
split; intros H.
- apply (F_fun (f_sound k n) H).
- subst; autoh.
Qed.

(** A few examples *)

(*
Compute take 26 (f 0).
Compute take 26 (f 1).
Compute take 26 (f 2).
Compute take 26 (f 3).
*)
(*
f 0 : [0; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5; 6; 6; 7; 7]
f 1 : [0; 1; 1; 2; 3; 3; 4; 4; 5; 6; 6; 7; 8; 8; 9]
f 2 : [0; 1; 1; 2; 3; 4; 4; 5; 5; 6; 7; 7; 8; 9; 10]
f 3 : [0; 1; 1; 2; 3; 4; 5; 5; 6; 6; 7; 8; 8; 9; 10]
*)

(* The first values of [f] when [n<=3] do not depend on [k] *)

Lemma f_k_0 k : f k 0 = 0.
Proof.
 reflexivity.
Qed.

Lemma f_k_1 k : f k 1 = 1.
Proof.
 apply f_complete; autoh.
Qed.

Lemma f_k_2 k : f k 2 = 1.
Proof.
 apply f_complete; autoh.
Qed.

Lemma f_k_3 k : f k 3 = 2.
Proof.
 apply f_complete; autoh.
Qed.

(** Basic equations over [f] : the same as [F] *)

Lemma Fs_iter_f p k n : Fs k p n (fs k p n).
Proof.
induction p.
- simpl. autoh.
- eapply FsS; eauto. simpl.
  rewrite f_complete; autoh.
Qed.

Lemma fs_k_0 p k : fs k p 0 = 0.
Proof.
 induction p; simpl; auto.
 rewrite IHp. apply f_k_0.
Qed.

Lemma fs_k_1 p k : fs k p 1 = 1.
Proof.
 induction p; simpl; auto.
 rewrite IHp. apply f_k_1.
Qed.

Lemma fs_k_2 k p : 0<p -> fs k p 2 = 1.
Proof.
 destruct p. easy. intros _. now rewrite iter_S, f_k_2, fs_k_1.
Qed.

Lemma f_eqn k n : f k (S n) + fs k (S k) n = S n.
Proof.
 assert (H := f_sound k (S n)).
 inversion_clear H.
 assert (fs k (S k) n = a).
 { revert H0. apply Fs_fun. apply Fs_iter_f. }
 lia.
Qed.

Lemma f_eqn_pred k n : f k n + fs k (S k) (pred n) = n.
Proof.
destruct n.
- now rewrite fs_k_0.
- apply f_eqn.
Qed.

Lemma f_S k n : f k (S n) = S n - fs k (S k) n.
Proof.
 generalize (f_eqn k n). lia.
Qed.

Lemma f_pred k n : f k n = n - fs k (S k) (pred n).
Proof.
 generalize (f_eqn_pred k n). lia.
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

Lemma f_unique k h :
  h 0 = 0  ->
  (forall n, S n = h (S n)+ (h^^S k) n) ->
  forall n, h n = f k n.
Proof.
intros h_0 h_S.
induction n as [[|n] IH] using lt_wf_ind.
- now rewrite h_0.
- assert (forall p m, m <= n -> (h^^p) m = fs k p m).
  { induction p.
    - now simpl.
    - intros. simpl.
      rewrite IHp; auto. apply IH.
      rewrite Nat.lt_succ_r. apply Nat.le_trans with m; auto.
      eapply Fs_le. eapply Fs_iter_f. }
  rewrite f_S, <- H; auto. specialize (h_S n). lia.
Qed.

Lemma f_step k n : f k (S n) = f k n \/ f k (S n) = S (f k n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 destruct n.
 - rewrite f_k_0, f_k_1. now right.
 - rewrite 2 f_S.
   assert (forall p m, m <= n ->
           fs k p (S m) = fs k p m \/
           fs k p (S m) = S (fs k p m)).
   { induction p.
     - simpl; now right.
     - intros; simpl.
       destruct (IHp m H) as [-> | ->].
       + now left.
       + apply IH.
         rewrite Nat.lt_succ_r. apply Nat.le_trans with m; auto.
         eapply Fs_le. eapply Fs_iter_f. }
   specialize (H (S k) n). lia.
Qed.

Lemma fs_step k p n : fs k p (S n) = fs k p n \/
                      fs k p (S n) = S (fs k p n).
Proof.
 induction p; simpl.
 - now right.
 - destruct IHp as [-> | ->]. now left. apply f_step.
Qed.

Lemma f_mono_S k n : f k n <= f k (S n).
Proof.
 generalize (f_step k n). lia.
Qed.

Lemma fs_mono_S k p n : fs k p n <= fs k p (S n).
Proof.
 generalize (fs_step k p n). lia.
Qed.

Lemma f_le_add k n m : f k (n+m) <= n + f k m.
Proof.
induction n; trivial.
simpl. destruct (f_step k (n+m)); lia.
Qed.

Lemma f_mono k n m : n <= m -> f k n <= f k m.
Proof.
induction 1.
- trivial.
- transitivity (f k m); auto using f_mono_S.
Qed.

Lemma fs_mono k p n m : n <= m -> fs k p n <= fs k p m.
Proof.
induction 1.
- trivial.
- transitivity (fs k p m); auto using fs_mono_S.
Qed.

(** NB : in Coq, for natural numbers, 3-5 = 0 (truncated subtraction) *)

Lemma f_lipschitz k n m : f k m - f k n <= m - n.
Proof.
destruct (le_ge_dec n m) as [H|H].
- induction H; try generalize (f_step k m); lia.
- generalize (f_mono k H). lia.
Qed.

Lemma fs_lipschitz k p n m : fs k p m - fs k p n <= m - n.
Proof.
 revert n m. induction p; auto.
 intros. simpl. etransitivity. eapply f_lipschitz. eapply IHp.
Qed.

Lemma f_nonzero k n : 0 < n -> 0 < f k n.
Proof.
 unfold lt. intros. rewrite <- (f_k_1 k). now apply f_mono.
Qed.

Lemma f_nz k n : n <> 0 -> f k n <> 0.
Proof.
 generalize (@f_nonzero k n). lia.
Qed.

Lemma f_0_inv k n : f k n = 0 -> n = 0.
Proof.
 generalize (@f_nz k n). lia.
Qed.

Lemma fs_nonzero k n p : 0 < n -> 0 < fs k p n.
Proof.
 revert n. induction p; simpl; auto using f_nonzero.
Qed.

Lemma fs_0_inv k n p : fs k p n = 0 -> n = 0.
Proof.
 generalize (@fs_nonzero k n p). lia.
Qed.

Lemma f_fix k n : f k n = n <-> n <= 1.
Proof.
split.
- destruct n; auto.
  assert (H := f_eqn k n).
  intros.
  assert (H' : fs k (S k) n = 0) by lia.
  apply fs_0_inv in H'.
  now subst.
- inversion_clear 1. apply f_k_1.
  inversion_clear H0. apply f_k_0.
Qed.

Lemma f_le k n : f k n <= n.
Proof.
 eapply F_le; eautoh.
Qed.

Lemma fs_le k p n : fs k p n <= n.
Proof.
 eapply Fs_le, Fs_iter_f.
Qed.

Lemma f_lt k n : 1<n -> f k n < n.
Proof.
 generalize (f_le k n) (f_fix k n); lia.
Qed.
#[global] Hint Resolve f_lt : hof.

Lemma fs_lt k p n : 0<p -> 1<n -> fs k p n < n.
Proof.
 destruct p; [easy|intros _ Hn].
 change (f k (fs k p n) < n).
 destruct (Nat.eq_dec (fs k p n) 0) as [->|N0]; [cbn; lia| ].
 destruct (Nat.eq_dec (fs k p n) 1) as [->|N1]; [now rewrite f_k_1| ].
 apply Nat.lt_le_trans with (fs k p n); [|apply fs_le].
 apply f_lt. lia.
Qed.

(** Two special formulations for [f_step] *)

Lemma f_next k n a : f k n = a -> (f k (S n) <> a <-> f k (S n) = S a).
Proof.
 generalize (f_step k n). lia.
Qed.

Lemma f_prev k n a : n <> 0 -> f k n = a ->
 (f k (n-1) <> a <-> f k (n-1) = a - 1).
Proof.
 intros H Ha.
 assert (Ha' := f_nz k H).
 generalize (f_step k (n-1)). replace (S (n-1)) with n; lia.
Qed.

(** [f] cannot stay flat very long *)

Lemma f_nonflat k n : f k (1+n) = f k n -> f k (2+n) = S (f k n).
Proof.
 generalize (f_eqn k (1+n)) (f_eqn k n).
 rewrite !iter_S. intros. rewrite H1 in *. simpl in *. lia.
Qed.

Lemma f_nonflat' k n : f k (S n) = f k n -> f k (n-1) = f k n - 1.
Proof.
 destruct n.
 - now rewrite f_k_0, f_k_1.
 - replace (S n - 1) with n by lia.
   intros H.
   destruct (f_step k n) as [H'|H'].
   + apply f_nonflat in H'; auto. simpl in *. lia.
   + lia.
Qed.

Lemma f_SS k n : f k n < f k (S (S n)).
Proof.
 destruct (f_step k n) as [E|E].
 - generalize (f_nonflat _ _ E). simpl in *. lia.
 - apply Nat.lt_le_trans with (f k (S n)). lia. auto using f_mono_S.
Qed.

Lemma f_double_le k n : n <= f k (2*n).
Proof.
induction n.
- trivial.
- replace (2* S n) with (S (S (2*n))) by lia.
  transitivity (S (f k (2*n))). lia. now apply f_SS.
Qed.

Lemma f_div2_le k n : n/2 <= f k n.
Proof.
 rewrite <- Nat.div2_div.
 rewrite (Nat.div2_odd n) at 2.
 transitivity (f k (2*Nat.div2 n)).
 now apply f_double_le.
 apply f_mono. lia.
Qed.

Lemma fs_bound k n p :
  1 < n -> 1 < fs k p n -> fs k p n <= n-p.
Proof.
 revert n.
 induction p.
 - simpl. intros. lia.
 - intros. simpl in *.
   assert (LE : 1 <= fs k p n).
   { generalize (@fs_nonzero k n p). lia. }
   assert (NE : fs k p n <> 1).
   { intros EQ; rewrite EQ, f_k_1 in *. lia. }
   specialize (IHp n H).
   generalize (@f_lt k (fs k p n)). lia.
Qed.

Lemma fs_init k n p : 1 <= n <= S p -> fs k p n = 1.
Proof.
 intros N.
 destruct (Nat.eq_dec n 1) as [->|N']; [ apply fs_k_1 |].
 assert (H := @fs_nonzero k n p).
 destruct (Nat.eq_dec (fs k p n) 1); trivial.
 generalize (@fs_bound k n p). lia.
Qed.

Lemma f_init k n : 2 <= n <= k+3 -> f k n = n-1.
Proof.
 intros. rewrite f_pred. rewrite fs_init; lia.
Qed.

(* Said otherwise : for any n, [f k n] will eventually be stationary
   when k grows. More precisely, for [n>=2], [f k n = n-1] as soon as
   [k>=n-3]. And for [n<2], we always have [f k n = n].
   Hard theorem : at fixed n and growing k, [f k n] will be increasing.
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
    [[f k n; f k (n-1); ... ; f k 0]].
    And [fdescend] visits this list to compute [fs k p n].
    Even with nat values, doing this way is way faster than the current [f].
*)

Fixpoint fdescend stk p n :=
  match p with
  | 0 => n
  | S p =>
    match stk with
    | [] => 0 (* normally won't occur *)
    | a::_ => fdescend (npop (n-a) stk) p a
    end
  end.

Fixpoint ftabulate k n :=
 match n with
 | 0 => [0]
 | S n =>
   let stk := ftabulate k n in
   (S n - fdescend stk (S k) n)::stk
 end.

Lemma fdescend_spec k stk p n :
 stk = map (f k) (countdown n) -> fdescend stk p n = fs k p n.
Proof.
 revert stk n.
 induction p; intros stk n E.
 - simpl; auto.
 - rewrite iter_S. simpl.
   destruct stk as [|a stk'] eqn:Stk.
   + now destruct n.
   + assert (a = f k n).
     { destruct n; simpl in E; inversion E; auto. }
     rewrite <- H.
     apply IHp.
     rewrite E. rewrite npop_map. f_equal.
     apply npop_countdown. subst a. apply f_le.
Qed.

Lemma ftabulate_spec k n : ftabulate k n = map (f k) (countdown n).
Proof.
 induction n.
 - reflexivity.
 - cbn -[minus fdescend].
   rewrite (fdescend_spec k); auto.
   rewrite <- f_S. f_equal; auto.
Qed.

(** Now comes a reasonably efficient [f] function
    (moreover, [ftabulate] can always be used when multiples
    images of [f] are needed at the same time). *)

Definition fopt k n :=
  match ftabulate k n with
  | a::_ => a
  | [] => 0
  end.

Lemma fopt_spec k n : fopt k n = f k n.
Proof.
 unfold fopt. rewrite ftabulate_spec. destruct n; simpl; auto.
Qed.


(*==============================================================*)

(** * Antecedents by [f k]

    Study of the reverse problem [f k n = a] for some [a]. *)

Lemma f_max_two_antecedents k n m :
  f k n = f k m -> n<m -> m = S n.
Proof.
 intros H H'.
 destruct (le_lt_dec (2+n) m) as [LE|LT]; try lia.
 apply (f_mono k) in LE.
 rewrite (f_nonflat k n) in LE. lia.
 apply Nat.le_antisymm.
 - rewrite H. now apply f_mono.
 - apply f_mono_S.
Qed.

(** Another formulation of the same fact *)

Lemma f_inv k n m :
  f k n = f k m -> (n = m \/ n = S m \/ m = S n).
Proof.
 intros.
 destruct (lt_eq_lt_dec n m) as [[LT|EQ]|LT]; auto.
 - generalize (@f_max_two_antecedents k n m); auto.
 - generalize (@f_max_two_antecedents k m n); auto.
Qed.

(** [f] is an onto map *)

Lemma f_onto k a : exists n, f k n = a.
Proof.
induction a.
- exists 0; trivial.
- destruct IHa as (n,Ha).
  destruct (f_step k n); [ | exists (S n); lia].
  destruct (f_step k (S n)); [ | exists (S (S n)); lia].
  exfalso.
  generalize (@f_max_two_antecedents k n (S (S n))). lia.
Qed.

(** We even have an explicit expression of one antecedent *)

Definition rchild k n := n + fs k k n.
Definition lchild k n := n + fs k k n - 1. (** left son, if there's one *)

Lemma f_onto_eqn k a : f k (rchild k a) = a.
Proof.
 destruct (f_onto k a) as (n,Hn).
 unfold rchild. rewrite <- Hn, <- iter_S.
 assert (E := f_eqn k n).
 destruct (f_step k n) as [<-|H]; f_equal; lia.
Qed.

Lemma rightmost_child_carac k a n : f k n = a ->
 (f k (S n) = S a <-> n = rchild k a).
Proof.
 intros Hn.
 assert (H' := f_eqn k n).
 rewrite iter_S in H'.
 rewrite Hn in H'.
 unfold rchild; lia.
Qed.

Lemma f_children k a n : f k n = a ->
  n = rchild k a \/ n = lchild k a.
Proof.
intros Hn.
destruct (f_step k n) as [H|H].
- right.
  destruct (f_step k (S n)) as [H'|H'].
  + exfalso.
    generalize (@f_max_two_antecedents k n (S (S n))). lia.
  + rewrite rightmost_child_carac in H'; trivial.
    rewrite H, Hn in H'. unfold lchild, rchild in *; lia.
- rewrite <- (@rightmost_child_carac k a n); lia.
Qed.

Lemma f_lchild k a :
 f k (lchild k a) = a - 1 \/ f k (lchild k a) = a.
Proof.
 destruct (le_gt_dec a 0).
  + replace a with 0 by lia. unfold lchild.
    rewrite fs_k_0. simpl. rewrite f_k_0. now left.
  + assert (0 < rchild k a)
     by (unfold rchild; generalize (@f_nonzero k a); lia).
    destruct (f_step k (lchild k a)) as [H'|H'];
    replace (S (lchild k a)) with (rchild k a) in * by
      (unfold lchild, rchild in *; lia);
    rewrite f_onto_eqn in *; lia.
Qed.


(** This provides easily a first relationship between f and
    generalized Fibonacci numbers *)

Lemma fs_A k n p : fs k p (A k n) = A k (n-p).
Proof.
revert p.
induction n; intros.
- simpl. apply fs_k_1.
- destruct p; auto.
  rewrite iter_S; simpl. rewrite <- (IHn p). f_equal.
  rewrite <- (IHn k). apply f_onto_eqn.
Qed.

Lemma f_A k n : f k (A k n) = A k (n-1).
Proof.
 apply (fs_A k n 1).
Qed.

Lemma f_SA k n : n<>0 -> f k (S (A k n)) = S (A k (n-1)).
Proof.
 intros.
 rewrite <- (@f_A k n).
 apply rightmost_child_carac; trivial.
 unfold rchild.
 rewrite f_A, fs_A.
 replace (n-1-k) with (n-S k) by lia.
 now apply A_sum.
Qed.

(** More generally, [f] is shifting down Zeckendorf decompositions *)

Definition fbis k n := sumA k (map pred (decomp k n)).

Lemma fbis_decomp k n :
  decomp k (fbis k n) = renorm k (map pred (decomp k n)).
Proof.
 apply decomp_carac.
 - apply renorm_delta.
   apply Delta_map with (S k).
   intros; lia. apply decomp_delta.
 - now rewrite renorm_sum.
Qed.

Lemma fsbis k p n : p <= S k ->
 (fbis k^^p) n = sumA k (map (decr p) (decomp k n)).
Proof.
 intros Hp.
 revert n.
 induction p; intros.
 - simpl. rewrite map_ext with (g:=id) by apply decr_0.
   rewrite map_id. symmetry. apply decomp_sum.
 - rewrite iter_S.
   rewrite IHp by lia.
   now rewrite fbis_decomp, renorm_mapdecr, map_decr_S by lia.
Qed.

Lemma fbis_is_f k n : fbis k n = f k n.
Proof.
 apply f_unique.
 - reflexivity.
 - clear n. intros n.
   rewrite fsbis; auto.
   assert (Hn := decomp_sum k n).
   assert (D := decomp_delta k n).
   remember (decomp k n) as l eqn:Hl.
   destruct l as [|a l].
   + simpl in *. now subst.
   + unfold fbis. rewrite decomp_S, <- Hl. simpl.
     case Nat.leb_spec; intros.
     * rewrite <- map_decr_1.
       rewrite renormS_alt, renorm_mapdecr'; simpl; auto with arith hof.
       2: destruct k; lia.
       rewrite Nat.add_shuffle1.
       assert (~In 0 l).
       { apply (@Delta_nz' (S k) a); auto with arith. }
       rewrite <- sumA_eqn_pred; auto.
       rewrite decr_0.
       unfold decr. replace (a-S k) with 0; simpl in *; lia.
     * rewrite map_cons, sumA_cons.
       rewrite <- Nat.add_assoc.
       rewrite <- map_decr_1.
       rewrite <- sumA_eqn_pred; auto.
       eapply Delta_nz; eauto. lia.
Qed.

Lemma f_decomp k n : f k n = sumA k (map pred (decomp k n)).
Proof.
 symmetry. apply fbis_is_f.
Qed.

Lemma decomp_f k n : decomp k (f k n) = renorm k (map pred (decomp k n)).
Proof.
 now rewrite <- fbis_is_f, fbis_decomp.
Qed.

Lemma fs_decomp k p n :
  p <= S k -> fs k p n = sumA k (map (decr p) (decomp k n)).
Proof.
 intros. rewrite <- fsbis; auto. clear.
 induction p; simpl; now rewrite ?IHp, <- ?fbis_is_f.
Qed.

Lemma f_sumA k l : Delta (S k) l ->
 f k (sumA k l) = sumA k (map pred l).
Proof.
 intros. rewrite f_decomp. f_equal. f_equal. autoh.
Qed.

Lemma fs_sumA k p l : p <= S k -> Delta (S k) l ->
 fs k p (sumA k l) = sumA k (map (decr p) l).
Proof.
 intros. rewrite fs_decomp; auto. f_equal. f_equal. autoh.
Qed.

Lemma f_sumA_lax k l : k<>0 -> Delta k l ->
 f k (sumA k l) = sumA k (map pred l).
Proof.
 intros. rewrite <- renorm_sum.
 rewrite f_sumA; autoh.
 rewrite <- !map_decr_1, renorm_mapdecr; auto. lia.
Qed.

Lemma fs_sumA_lax k p l : p < S k -> Delta k l ->
 fs k p (sumA k l) = sumA k (map (decr p) l).
Proof.
 intros. rewrite <- renorm_sum.
 rewrite fs_sumA; auto with arith hof.
 apply renorm_mapdecr; lia.
Qed.

(** Extending theorem [fs_decomp] to larger iterates than [p <= S k] *)

Definition succrank k n :=
  match rank k n with
  | None => 0
  | Some r => S r
  end.

Lemma f_succrank k n : succrank k n <= S (succrank k (f k n)).
Proof.
 unfold succrank, rank. rewrite decomp_f.
 assert (H := renorm_head k (map pred (decomp k n))).
 destruct decomp as [|r l], renorm as [|r' l']; simpl in *; try lia.
 destruct H as (m, H). lia.
Qed.

Lemma fs_decomp_gen k p n : n = 0 \/ p <= k + succrank k n ->
 fs k p n = sumA k (map (decr p) (decomp k n)).
Proof.
 intros [->|H].
 - simpl. induction p; simpl; now rewrite ?IHp.
 - revert n H.
   induction p; intros.
   + simpl. rewrite map_ext with (g:=id) by apply decr_0.
     rewrite map_id. symmetry. apply decomp_sum.
   + rewrite iter_S.
     rewrite IHp; clear IHp; auto with arith.
     2:{ generalize (f_succrank k n); lia. }
     rewrite decomp_f.
     unfold succrank, rank in H.
     assert (D := decomp_delta k n).
     destruct decomp as [|r l]; trivial.
     destruct (Nat.eq_dec r 0) as [->|R].
     * rewrite renorm_mapdecr by lia.
       f_equal. symmetry. apply map_decr_S.
     * rewrite renorm_nop.
       { f_equal. symmetry. apply map_decr_S. }
       { apply Delta_pred; trivial.
         eapply Delta_nz; eauto with hof. lia. }
Qed.

(** Zone where [f k n = n-1].
    Note that [f k n] cannot be [n] or more except when [n<=1], see [f_lt].
    The conditions below are optimal, see [f_subid_inv] later. *)

Lemma f_subid k n : n<>1 -> n <= k+3 -> f k n = n-1.
Proof.
 intros Hn Hn'.
 destruct (Nat.eq_dec n 0).
 - subst. now rewrite f_k_0.
 - apply f_init; lia.
Qed.


(** Some particular cases : early diagonals *)

Lemma f_k_k k : k<>1 -> f k k = k-1.
Proof.
 intros. apply f_subid; lia.
Qed.

Lemma f_k_Sk k : k<>0 -> f k (S k) = k.
Proof.
 intros. rewrite f_subid; lia.
Qed.

Lemma f_k_plus_2 k : f k (2+k) = S k.
Proof.
 rewrite f_subid; lia.
Qed.

Lemma f_k_plus_3 k : f k (3+k) = 2+k.
Proof.
 rewrite f_subid; lia.
Qed.

Lemma f_k_plus_4 k : f k (4+k) = 2+k.
Proof.
 replace (4+k) with (sumA k [S (S k)]).
 2:{ cbn -[A]. rewrite A_S.
     replace (S k - k) with 1 by lia.
     rewrite !A_base; lia. }
 rewrite f_sumA; autoh. cbn -[A]. rewrite A_base; lia.
Qed.

Lemma f_k_plus_5 k : f k (5+k) = 3+k.
Proof.
 replace (5+k) with (sumA k [0;S (S k)]).
 2:{ cbn -[A]. rewrite A_S.
     replace (S k - k) with 1 by lia.
     rewrite !A_base; lia. }
 rewrite f_sumA; autoh. cbn -[A]. rewrite !A_base; lia.
Qed.

Lemma f_k_plus_6 k : f k (6+k) = 3+k.
Proof.
 replace (6+k) with (sumA k [1;S (S k)]).
 2:{ cbn -[A]. rewrite (A_S k (S k)).
     replace (S k - k) with 1 by lia.
     rewrite !A_base; lia. }
 rewrite f_sumA; autoh. cbn -[A]. rewrite !A_base; lia.
Qed.

Lemma f_k_plus_7 k : f k (7+k) = 4+k.
Proof.
 destruct (Nat.eq_dec k 0) as [->|Hk]. now compute.
 replace (7+k) with (sumA k [2;S (S k)]).
 2:{ cbn -[A]. rewrite (A_S k (S k)).
     replace (S k - k) with 1 by lia.
     rewrite !A_base; lia. }
 rewrite f_sumA_lax; autoh. cbn -[A]. rewrite !A_base; lia.
Qed.

Lemma f_subid_inv k n : f k n = n-1 -> n <> 1 /\ n <= k+3.
Proof.
 intros E. split.
 - intros ->. rewrite f_k_1 in E. discriminate.
 - rewrite Nat.le_ngt. intros LT.
   generalize (f_lipschitz k (4+k) n).
   rewrite f_k_plus_4, E. lia.
Qed.

(** Summarize some of the last results (note that [f 0 p = (p+1)/2]). *)

Lemma f_k_plus_some k p : 2 <= p <= 7 -> f k (k+p) = k + f 0 p.
Proof.
 intros Hp. rewrite !(Nat.add_comm k).
 destruct (Nat.eq_dec p 2) as [->|N2]. apply f_k_plus_2.
 destruct (Nat.eq_dec p 3) as [->|N3]. apply f_k_plus_3.
 destruct (Nat.eq_dec p 4) as [->|N4]. apply f_k_plus_4.
 destruct (Nat.eq_dec p 5) as [->|N5]. apply f_k_plus_5.
 destruct (Nat.eq_dec p 6) as [->|N6]. apply f_k_plus_6.
 destruct (Nat.eq_dec p 7) as [->|N7]. apply f_k_plus_7.
 lia.
Qed.

(** Decomposition and positions in the F tree *)

Lemma rchild_decomp k n :
 rchild k n = sumA k (map S (decomp k n)).
Proof.
 unfold rchild.
 rewrite fs_decomp; auto.
 rewrite <- (@decomp_sum k n) at 1.
 remember (decomp k n) as l.
 apply sumA_eqn.
Qed.

Lemma flat_rank_0 k n :
 f k (S n) = f k n <-> rank k n = Some 0.
Proof.
 rewrite !f_decomp.
 unfold rank.
 rewrite decomp_S.
 destruct (decomp k n) as [|a l] eqn:E.
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
     * simpl. destruct k; lia.
     * rewrite <- E. autoh.
   + simpl. split. intros; f_equal; lia. intros [= ->]; lia.
Qed.

Lemma step_rank_nz k n :
 f k (S n) = S (f k n) <-> rank k n <> Some 0.
Proof.
 rewrite <- flat_rank_0.
 generalize (f_step k n). lia.
Qed.

Lemma steps_ranks_nz k n p :
 f k (n+p) = f k n + p <-> (forall q, q<p -> rank k (n+q) <> Some 0).
Proof.
 induction p.
 - rewrite !Nat.add_0_r. intuition lia.
 - rewrite !Nat.add_succ_r.
   split.
   + intros E q Hq.
     assert (LE := f_le_add k p n). rewrite (Nat.add_comm p n) in LE.
     assert (LE' := f_le_add k 1 (n+p)). simpl in LE'.
     inversion Hq.
     * subst q. apply step_rank_nz. lia.
     * apply IHp; try lia.
   + intro H.
     assert (R : rank k (n+p) <> Some 0) by (apply H; lia).
     apply step_rank_nz in R. rewrite R. f_equal.
     apply IHp. intros q Hq. apply H. lia.
Qed.

(** At most [k+1] consecutive [+1] steps *)

Lemma f_maxsteps k n :
 f k (n+k+2) <= f k n + k+1.
Proof.
 destruct (rank_later_is_zero k n) as (p & LE & H).
 apply flat_rank_0 in H.
 transitivity (f k (S (p + n)) + (k+2-S p)).
 - generalize (f_lipschitz k (S (p+n)) (n+k+2)). lia.
 - rewrite H.
   generalize (f_lipschitz k n (p+n)). lia.
Qed.

(** A first example of such [k+1] consecutive [+1] steps : [n=2] *)

Lemma f_maxsteps_example2 k : f k (2+S k) = f k 2 + S k.
Proof.
 rewrite f_k_2. simpl. apply f_k_plus_3.
Qed.

(** More generally, [k+1] consecutive [+1] steps for numbers [2+n]
    when [n=0] or [rank k n > 2k]. *)

Lemma f_maxsteps_examples k n :
  (forall r, rank k n = Some r -> 2*k < r) ->
  f k ((2+n) + S k) = f k (2+n) + S k.
Proof.
 intros Hr.
 destruct (rank k n) as [r|] eqn:Hn.
 2:{ rewrite rank_none in Hn; subst n. apply f_maxsteps_example2. }
 specialize (Hr r eq_refl).
 apply steps_ranks_nz.
 intros q Hq. replace (2+n+q) with (S (S q) + n) by lia.
 rewrite <- (@A_base k (S q)) by lia.
 rewrite <- (decomp_sum k n).
 change (_+_) with (sumA k (S q::decomp k n)).
 unfold rank in *. rewrite <- renorm_sum, decomp_sum'.
 - generalize (renorm_head k (S q::decomp k n)). unfold HeadStep.
   destruct renorm as [|a l]; try easy. intros (b & ->) [= E].
 - apply renorm_delta. assert (D := decomp_delta k n).
   destruct decomp as [|u l]; try easy.
   injection Hn as ->. constructor; autoh.
Qed.

(* No other situations with [k+1] consecutive [+1] steps,
   except [f 0 1 = 1 + f 0 0]. *)

Lemma f_maxsteps_carac_aux k n r :
  rank k n = Some r -> S k <= r <= 2*k ->
  exists q, rank k (n+2+(r-S k)) = Some q /\ r < q.
Proof.
 intros Hn Hr.
 assert (E : forall q, q <= r-S k -> decomp k (n + S q) = q :: decomp k n).
 { intros q Hq. rewrite <- (@A_base k q) by lia.
   unfold rank in *. rewrite <- (decomp_sum k n) at 1.
   rewrite Nat.add_comm.
   change (_+_) with (sumA k (q::decomp k n)).
   apply decomp_sum'.
   assert (D := decomp_delta k n).
   destruct decomp as [|u l]; try easy.
   injection Hn as ->. constructor; auto. lia. }
 assert (LE : r-S k <= r-S k) by lia.
 specialize (E (r-S k) LE). clear LE.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l in E.
 unfold rank in *.
 destruct (decomp k n) as [|r' l] eqn:E'; try easy. injection Hn as ->.
 assert (E2 : decomp k (n+2 + (r-S k)) = renormS k r l).
 { rewrite !Nat.add_succ_r, Nat.add_0_r, Nat.add_succ_l.
   rewrite decomp_S, E. simpl.
   case Nat.leb_spec; try lia. intros _.
   case Nat.eqb_spec; trivial; lia. }
 rewrite E2.
 assert (H := renormS_head k r l).
 red in H. destruct renormS; try easy.
 destruct H as (q & ->). exists (S r + q*S k). split; auto. lia.
Qed.

Lemma f_maxsteps_carac k n :
  f k (n + S k) = f k n + S k <->
  (k=0 /\ n=0) \/ (2<=n /\ forall r, rank k (n-2) = Some r -> 2*k < r).
Proof.
 split.
 - intros E.
   destruct (Nat.le_gt_cases n 1) as [LE|LT].
   + left.
     destruct (Nat.eq_dec n 0) as [->|N].
     * rewrite f_k_0 in E. apply f_fix in E. lia.
     * replace n with 1 in * by lia. rewrite f_k_1 in *.
       apply f_fix in E. lia.
   + right.
     split; [lia| ].
     intros r Hr.
     rewrite steps_ranks_nz in E.
     apply Nat.lt_nge. intros LE.
     destruct (Nat.le_gt_cases r k) as [LE'|GT].
     * destruct (rank_later_is_zero k (n-1)) as (q & Hq & R).
       destruct (Nat.eq_dec q 0).
       { subst q. simpl in *.
         apply rank_next_high in Hr; auto. destruct Hr as (m & Hr).
         replace (S (n-2)) with (n-1) in Hr by lia.
         rewrite Hr in R. now injection R. }
       { apply (E (q-1)). lia.
         rewrite <- R. f_equal. lia. }
     * destruct (@f_maxsteps_carac_aux k (n-2) r Hr) as (q & Hq & Hq'); try lia.
       replace (n-2+2) with n in Hq by lia.
       apply (E (r-k)). lia.
       replace (n+(r-k)) with (S (n+(r-S k))) by lia.
       eapply rank_next_0; eauto. lia.
 - intros [(->,->) | (LE & H)].
   + reflexivity.
   + replace n with (2+(n-2)) by lia. apply f_maxsteps_examples; auto.
Qed.

(** Other characterization of max [+1] steps :
    the last term in the [+1] sequence is decomposed as [0;q*(S k);...]
    where [q<>0]. *)

Lemma f_steps_sub k n p :
 rank k n = Some (S p) -> p <= k -> f k (n - p) = f k n - p.
Proof.
 revert n.
 induction p.
 - intros n R. rewrite Nat.sub_0_r. lia.
 - intros n R Hp.
   assert (R' : rank k (n-1) = Some (S p)).
   { apply rank_pred in R; auto. simpl "-" in R.
     rewrite Nat.mod_small in R; auto; lia. }
   replace (n-S p) with (n-1-p) by lia.
   rewrite IHp; auto; try lia.
   assert (R0 : rank k (n-1) <> Some 0) by now rewrite R'.
   rewrite <- step_rank_nz in R0.
   destruct n as [|n].
   + reflexivity.
   + simpl in *. rewrite Nat.sub_0_r in *. lia.
Qed.

Lemma f_maxsteps_examples_alt k n q :
 rank k n = Some ((S q)*(S k)) ->
 f k ((n+1) - S k) = f k (n+1) - S k.
Proof.
 destruct (Nat.eq_dec k 0) as [->|Hk].
 - intros R. rewrite Nat.mul_1_r in R.
   replace (n+1-1) with n by lia.
   rewrite Nat.add_1_r.
   assert (R' : rank 0 n <> Some 0) by now rewrite R.
   rewrite <- step_rank_nz in R'. lia.
 - intros R.
   assert (R' : rank k n <> Some 0) by now rewrite R.
   rewrite <- step_rank_nz in R'.
   destruct (Nat.eq_dec n 0) as [->|Hn].
   + simpl. apply f_k_0.
   + assert (Rm : rank k (n-1) = Some k).
     { apply rank_pred in R. 2:(simpl; lia).
       replace (S q * S k - 1) with (k + q * (S k)) in R by lia.
       rewrite Nat.mod_add in R; auto.
       rewrite Nat.mod_small in R; auto; lia. }
     replace (n+1 - S k) with (n-1-(k-1)) by lia.
     rewrite f_steps_sub; try lia.
     2:rewrite Rm; f_equal; lia.
     assert (Rm' : rank k (n-1) <> Some 0) by (rewrite Rm; congruence).
     rewrite <- step_rank_nz in Rm'.
     rewrite Nat.add_1_r.
     replace (S (n-1)) with n in Rm'; lia.
Qed.

(** Beware, when comparing an [option nat] and a [nat],
    [None] serves as a bottom element, not comparable with any [nat]. *)

Definition olt (o : option nat) n :=
 match o with
 | None => False
 | Some a => a < n
 end.

Declare Scope option_nat_scope.
Delimit Scope option_nat_scope with onat.

Infix "<" := olt : option_nat_scope.

Lemma rank_S_nz_iff k n :
  rank k (S n) <> Some 0 <-> (rank k n < S k)%onat.
Proof.
 unfold rank.
 rewrite decomp_S.
 destruct (decomp k n) as [|a l] eqn:E.
 - simpl. intuition.
 - simpl.
   case Nat.leb_spec; intros.
   + assert (Hd := renormS_head k a l).
     destruct renormS. intuith.
     destruct Hd as (m,Hd); simpl in Hd.
     split; auto with arith.
     intros _. injection 1 as ->. discriminate.
   + intuith.
Qed.

Lemma fs_flat_low_rank k p n : p <= S k ->
 fs k p (S n) = fs k p n <-> (rank k n < p)%onat.
Proof.
 intros Hp.
 apply Nat.lt_eq_cases in Hp.
 destruct Hp as [Hp| ->].
 - rewrite !fs_decomp by auto with arith.
   unfold rank.
   rewrite decomp_S.
   destruct (decomp k n) as [|a l] eqn:E.
   + simpl. intuition lia.
   + simpl.
     case Nat.leb_spec; intros.
     * rewrite renormS_alt by (rewrite <- E; autoh).
       rewrite renorm_mapdecr by lia.
       rewrite map_cons, sumA_cons.
       unfold decr at 1 3.
       rewrite !A_base by (auto; lia).
       lia.
     * simpl. intuition lia.
 - rewrite <- rank_S_nz_iff.
   rewrite <- step_rank_nz.
   rewrite 2 f_S.
   generalize (fs_le k (S k) n).
   lia.
Qed.

Lemma fs_nonflat_high_rank k p n : p <= S k ->
  fs k p (S n) = S (fs k p n) <-> ~(rank k n < p)%onat.
Proof.
 intros Hp.
 rewrite <- fs_flat_low_rank by trivial.
 assert (LE := fs_lipschitz k p n (S n)).
 replace (S n - n) with 1 in LE by lia.
 generalize (@fs_mono k p n (S n)). lia.
Qed.

Lemma fs_nonflat_high_rank' k p n : p <= S k ->
  fs k p (S n) = S (fs k p n) <->
  match rank k n with
  | None => True
  | Some a => p <= a
  end.
Proof.
 intros.
 rewrite fs_nonflat_high_rank by trivial.
 destruct rank; simpl; intuition lia.
Qed.

(** [fs k p] cannot have more than [p+1] consecutive flats *)

Lemma fs_maxflat k n p : p <= S k ->
 fs k p n < fs k p (n+p+1).
Proof.
 intros Hp.
 destruct (rank k n) as [r|] eqn:Hr.
 - destruct (@rank_later_is_high k n r p Hp Hr) as (r' & q & H1 & H2 & H3).
   assert (E : fs k p (S (q+n)) = S (fs k p (q+n))).
   { apply fs_nonflat_high_rank; auto. rewrite H2. simpl. lia. }
   unfold lt.
   transitivity (S (fs k p (q+n))).
   + apply -> Nat.succ_le_mono. apply fs_mono. lia.
   + rewrite <- E. apply fs_mono. lia.
 - rewrite rank_none in *. subst.
   rewrite fs_k_0. apply fs_nonzero. lia.
Qed.

(** Study of the "triangular" zone of f, coming after the "n-1" zone
    seen in [f_subid]. Here [n <= triangle(k+4)-3 = A k (2*k+3) - 1].

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
 let k := steps n in
 k*(k+1) <= 2*n < (k+1)*(k+2).
Proof.
 induction n as [[|n] IH] using lt_wf_ind.
 - clear IH. simpl. lia.
 - simpl steps.
   intros k.
   replace (2 * S n) with (2+2*n) by lia.
   assert (LT : n < S n) by lia.
   assert (IH1 := IH n LT).
   assert (LT' : n - steps n < S n) by lia.
   assert (IH2 := IH _ LT'). clear IH.
   set (p := steps n) in *.
   set (q := steps (n-p)) in *.
   unfold k; clear k. cbv zeta in *.
   replace (2*(n-p)) with (2*n-2*p) in IH2 by lia.
   assert (q <= p).
   { apply Nat.lt_succ_r. apply steps_inv_lt. lia. }
   assert (p <= S q).
   { destruct (Nat.eq_dec p 0).
     - clearbody p. subst p. auto with arith.
     - assert (p-1 < S q); try lia.
       apply steps_inv_lt.
       replace (p-1+1) with p by lia.
       apply Nat.le_lt_trans with (2*n-2*p); lia. }
   replace (S q) with (q+1) by lia.
   replace (q+1+1) with (q+2) by lia.
   replace (q+1+2) with (q+3) by lia.
   rewrite !Nat.mul_add_distr_l in *.
   rewrite !Nat.mul_add_distr_r in *. lia.
Qed.

Lemma steps_spec' n :
 triangle (steps n) <= n < triangle (S (steps n)).
Proof.
 destruct (steps_spec n) as (LE,LT).
 set (k := steps n) in *. clearbody k.
 split.
 - unfold triangle. apply Nat.div_le_upper_bound; auto.
 - clear LE.
   replace ((k+1)*(k+2)) with (S k * (S k + 1)) in * by lia.
   rewrite <- double_triangle in LT. lia.
Qed.

Lemma steps_altspec k p :
 p <= k -> steps (triangle k + p) = k.
Proof.
 intros LE.
 apply steps_uniqueness with (triangle k + p).
 apply steps_spec.
 replace ((k+1)*(k+2)) with (S k * (S k + 1)) by lia.
 rewrite <- !double_triangle, triangle_succ. lia.
Qed.

Lemma steps_triangle k : steps (triangle k) = k.
Proof.
 rewrite <- (Nat.add_0_r (triangle k)). apply steps_altspec. lia.
Qed.

Lemma steps_triangle_minus k p : 1 <= p <= k ->
 steps (triangle k - p) = k - 1.
Proof.
 destruct k.
 - reflexivity.
 - intros LE.
   rewrite triangle_succ.
   replace (triangle k + S k - p) with (triangle k + (S k - p)) by lia.
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
 set (k := steps n) in *.
 destruct (Nat.leb_spec (S n - triangle k) k).
 - replace (S n) with (triangle k + (S n - triangle k)) by lia.
   rewrite steps_altspec; auto.
 - rewrite triangle_succ in H.
   replace (S n) with (triangle k + S k) by lia.
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
 set (k := steps n) in *.
 rewrite triangle_succ in H.
 replace (n + S k) with (triangle k + S k + (n - triangle k)) by lia.
 rewrite <- triangle_succ.
 apply steps_altspec; auto. lia.
Qed.

(* The numbers below [A k (2*k+3) = triangle(k+4)-2] (cf A_2kp3_tri)
   have a decomposition of size at most 2, and have rank 0 only when
   they are 1 or a successor of a [A] number. That's the key for describing
   the "triangular" zone of f. Graphical interpretation : the bottom
   of the tree, where binary nodes are on the left edge. *)

Lemma decomp_len_lt_3 k n :
  n < A k (2*k+3) - 1 -> length (decomp k n) < 3.
Proof.
 intros LT.
 assert (E := decomp_sum k n).
 assert (D := decomp_delta k n).
 destruct (decomp k n) as [|r [|p [|q l]]]; simpl; try lia.
 exfalso.
 rewrite 2 Delta_alt in D. destruct D as ((_,D1),D2).
 specialize (D2 p (or_introl eq_refl)).
 specialize (D1 q (or_introl eq_refl)).
 assert (A k (S k) <= A k p) by (apply A_mono; lia).
 assert (A k (2*k + 2) <= A k q) by (apply A_mono; lia).
 simpl in E. rewrite A_2kp3_eqn in LT.
 generalize (A_nz k r). lia.
Qed.

Lemma decomp_len_3 k :
  decomp k (A k (2*k+3) - 1) = [0; S k; 2*S k].
Proof.
 apply decomp_carac.
 - repeat (constructor; try lia).
 - rewrite A_2kp3_eqn. replace (2*S k) with (2*k+2) by lia.
   simpl. replace (k-k) with 0; lia.
Qed.

Lemma low_rank0 k n :
  1 < n < A k (2*k+3) - 1 -> rank k n = Some 0 ->
  exists p, p < 2*k+3 /\ n = S (A k p).
Proof.
 unfold rank.
 intros (Hn,Hn') Hr.
 assert (L := decomp_len_lt_3 k Hn').
 assert (E := decomp_sum k n).
 assert (D := decomp_delta k n).
 destruct (decomp k n) as [|r [|p [|q l]]]; simpl in L;
  try easy; injection Hr as ->; simpl in E; try lia.
 exists p. split; try lia. apply A_lt_inv with k; lia.
Qed.

Lemma A_plus2 k n : n <= k+2 -> A k n <= n+2.
Proof.
 rewrite Nat.lt_eq_cases. intros [LT | ->].
 - rewrite A_base; lia.
 - rewrite Nat.add_succ_r, A_S, A_base; try lia.
   replace (k+1-k) with 1 by lia. now rewrite A_k_1.
Qed.

Lemma f_triangle k n :
  n<>1 -> n <= triangle(k+4)-3 ->
  f k n = n-1 - steps (n-k-3).
Proof.
 replace (_-3) with (triangle(k+4)-2-1) by lia. rewrite <- A_2kp3_tri.
 induction n.
 - reflexivity.
 - intros NE LE.
   destruct (Nat.leb_spec (S n) (k+3)).
   + rewrite f_subid; auto.
     replace (S n - k - 3) with 0 by lia. simpl. lia.
   + destruct (f_step k n) as [E|E].
     * rewrite E.
       rewrite flat_rank_0 in E.
       destruct (@low_rank0 k n) as (p & Hp & Hp'); auto; try lia.
       assert (k < p).
       { apply A_lt_inv with k. rewrite A_base by lia. lia. }
       rewrite IHn; try lia.
       assert (steps (S n - k - 3) = S (steps (n - k - 3))); try lia.
       { replace p with (k+(p-k)) in Hp' by lia.
         rewrite A_triangle in Hp'; try lia.
         rewrite Hp'.
         replace (_ - k - 3) with (triangle (p-k)) by lia.
         rewrite steps_triangle.
         replace (_ - k - 3) with (triangle (p-k) - 1) by lia.
         rewrite steps_triangle_minus; lia. }
     * rewrite E.
       rewrite step_rank_nz in E.
       rewrite IHn; clear IHn; try lia.
       assert (LE' := steps_le_id (n-k-3)).
       assert (steps (S n - k - 3) = steps (n - k - 3)); try lia.
       { clear LE'.
         destruct (@A_inv' k n) as (p,Hp); try lia.
         assert (k < p).
         { rewrite Nat.succ_lt_mono.
           apply A_lt_inv with k. rewrite A_base; lia. }
         assert (p < 2*k+3).
         { apply A_lt_inv with k. lia. }
         assert (LE' : p - k <= k + 2) by lia.
         assert (T := A_triangle k LE').
         replace (k+(p-k)) with p in T by lia.
         assert (n <> S (A k p)).
         { intro E'. apply E.
           unfold rank. replace (decomp k n) with [0;p]; auto.
           symmetry. apply decomp_carac; simpl; try lia.
           constructor; autoh. }
         destruct (Nat.eq_dec (A k p) n) as [E'|NE'].
         - clear Hp.
           assert (S k < p).
           { apply A_lt_inv with k. rewrite A_base; lia. }
           rewrite E' in T. rewrite T.
           replace (_ - k - 3) with (triangle (p-k) - 1) by lia.
           replace (_ - k - 3) with (triangle (p-k) - 2) by lia.
           rewrite !steps_triangle_minus; lia.
         - rewrite A_S in Hp.
           set (t := triangle (p-k)) in *. apply A_plus2 in LE'.
           replace (n-k-3) with (t + (n-k-3-t)) by lia.
           replace (S n-k-3) with (t + (S n-k-3-t)) by lia.
           unfold t at 1 3. rewrite !steps_altspec; lia. }
Qed.

(* We hence have [f k n <= f (S k) n] when n is in
   this triangular zone. *)

Lemma f_triangle_diag_incr k n :
  n<>1 -> n <= triangle(k+4)-3 ->
  f (S k) (S n) = S (f k n).
Proof.
 intros Hn LE.
 destruct (Nat.eq_dec n 0).
 - subst. now rewrite f_k_0, f_k_1.
 - rewrite !f_triangle; try lia. simpl.
   generalize (steps_le_id (n-k-3)). lia.
   simpl. rewrite triangle_succ. lia.
Qed.

Lemma f_triangle_incrk k n :
  n <= triangle(k+4)-3 -> f k n <= f (S k) n.
Proof.
 destruct (Nat.eq_dec n 1) as [->|NE].
 - intros _. now rewrite !f_k_1.
 - intros LE.
   destruct (f_step (S k) n) as [E|E].
   + rewrite <- E. rewrite f_triangle_diag_incr; auto.
   + rewrite f_triangle_diag_incr in E; lia.
Qed.

Lemma f_last_triangle_1 k n :
 n = triangle(k+4)-3 -> f k n = n - k - 3.
Proof.
 intros EQ.
 destruct (Nat.eq_dec n 1) as [->|NE].
 - exfalso. rewrite Nat.add_succ_r, triangle_succ in EQ.
   generalize (triangle_aboveid (k+3)). lia.
 - rewrite f_triangle by lia.
   rewrite EQ at 2.
   rewrite Nat.add_succ_r, triangle_succ.
   replace (triangle _ + _ - _ - _ - _)
     with (triangle (k+3) - 2) by lia.
   rewrite steps_triangle_minus; lia.
Qed.

Lemma f_last_triangle_2 k n :
 n = triangle(k+4)-3 -> f (S k) n = n - k - 3.
Proof.
 intros EQ.
 destruct (Nat.eq_dec n 1) as [->|NE].
 - exfalso. rewrite Nat.add_succ_r, triangle_succ in EQ.
   generalize (triangle_aboveid (k+3)). lia.
 - rewrite f_triangle; try lia.
   2:{ simpl. rewrite triangle_succ. lia. }
   rewrite EQ at 2.
   rewrite Nat.add_succ_r, triangle_succ.
   replace (triangle _ + _ - _ - _ - _)
     with (triangle (k+3) - 3) by lia.
   rewrite steps_triangle_minus; lia.
Qed.

(* Experimentally, this border of the triangle zone [n = triangle(k+4)-3]
   seems to be the last point where [f k n = f (S k) n].
   Conjecture : [forall m, triangle(k+4)-3 < m -> f k m < f (S k) m].
   Proof: ?! (TODO) *)

Lemma fk_fSk_last_equality k n :
 n = triangle(k+4)-3 -> f k n = f (S k) n.
Proof.
  intros EQ. now rewrite f_last_triangle_1, f_last_triangle_2.
Qed.

(* Some particular cases after the limit of the triangular zone *)

Lemma f_after_triangle_1 k n :
 n = triangle(k+4)-2 -> f k n = n - k - 4.
Proof.
 rewrite <- A_2kp3_tri. intros ->.
 rewrite f_A. rewrite A_2kp3_eqn.
 rewrite (@A_base k (S k)) by lia.
 replace (2*k+3-1) with (2*k+2); lia.
Qed.

Lemma f_after_triangle_2 k n :
 n = triangle(k+4)-2 -> f k (S n) = n - k - 3.
Proof.
 rewrite <- A_2kp3_tri. intros ->.
 rewrite f_SA; try lia.
 rewrite A_2kp3_eqn.
 rewrite (@A_base k (S k)) by lia.
 replace (2*k+3-1) with (2*k+2); lia.
Qed.

Lemma f_after_triangle_3 k n :
 n = triangle(k+4)-2 -> f (S k) n = n - k - 3.
Proof.
 intros E.
 rewrite f_triangle.
 2:{ rewrite E, Nat.add_succ_r, triangle_succ. lia. }
 2:{ simpl. rewrite triangle_succ. lia. }
 rewrite E at 2.
 rewrite Nat.add_succ_r, triangle_succ.
 replace (_ + S (k+3) - 2 - S k - 3) with (triangle (k+3) -2) by lia.
 rewrite steps_triangle_minus; lia.
Qed.

Lemma f_after_triangle_4 k n :
 n = triangle(k+4)-2 -> f (S k) (S n) = n - k - 2.
Proof.
 intros E.
 rewrite f_triangle.
 2:{ rewrite E, Nat.add_succ_r, triangle_succ. lia. }
 2:{ simpl. rewrite triangle_succ. lia. }
 simpl. rewrite E at 2.
 rewrite Nat.add_succ_r, triangle_succ.
 replace (_ + S (k+3) - 2 - k - 3) with (triangle (k+3) -1) by lia.
 rewrite steps_triangle_minus; lia.
Qed.

(** * Another equation about [f]

    This one will be used later when flipping [F] left/right. *)

Lemma f_alt_eqn k n : f k n + fs k k (f k (S n) - 1) = n.
Proof.
 destruct (Nat.eq_dec n 0) as [-> |Hn].
 - simpl. now rewrite fs_k_0.
 - assert (Hn' := f_nz k Hn).
   case (f_step k n) as [H|H].
   + (* n left child of a binary node *)
     rewrite H.
     generalize (f_eqn k (n-1)).
     case (f_step k (n - 1));
     replace (S (n - 1)) with n by lia.
     * generalize (@f_max_two_antecedents k (n-1) (S n)). lia.
     * intros. replace (f k n - 1) with (f k (n-1)) by lia.
       rewrite iter_S in *. lia.
   + (* n is rightmost child *)
     generalize (f_eqn k n).
     rewrite H, S_sub_1, <- iter_S.
     now injection 1.
Qed.


(** * Depth in the [f] tree *)

(** The depth of a node in the [f] tree is the number of
    iteration of [g] needed before reaching node 1 *)

Fixpoint depth_loop k n cpt :=
 match cpt with
 | 0 => 0
 | S cpt' =>
   match n with
   | 0 => 0
   | 1 => 0
   | _ => S (depth_loop k (f k n) cpt')
   end
 end.

Definition depth k n := depth_loop k n n.

Lemma depth_loop_ok k n c c' :
  n <= c -> n <= c' -> depth_loop k n c = depth_loop k n c'.
Proof.
 revert n c'.
 induction c as [|c IH]; destruct c' as [|c']; simpl; auto.
 - now inversion 1.
 - now inversion 2.
 - intros. destruct n as [|[|n]]; auto.
   f_equal. apply IH.
   + generalize (@f_lt k (S (S n))). lia.
   + generalize (@f_lt k (S (S n))). lia.
Qed.

Lemma depth_0 k : depth k 0 = 0.
Proof.
 reflexivity.
Qed.

Lemma depth_1 k : depth k 1 = 0.
Proof.
 reflexivity.
Qed.

Lemma depth_SS k n : depth k (S (S n)) = S (depth k (f k (S (S n)))).
Proof.
 unfold depth.
 remember (S n) as m.
 simpl depth_loop at 1. rewrite Heqm at 1.
 f_equal. apply depth_loop_ok; auto.
 generalize (@f_lt k (S m)). lia.
Qed.

Lemma depth_eqn k n : 1<n -> depth k n = S (depth k (f k n)).
Proof.
 destruct n as [|[|n]].
 - lia.
 - lia.
 - intros _. apply depth_SS.
Qed.

Lemma f_depth k n : depth k (f k n) = depth k n - 1.
Proof.
 destruct (le_lt_dec n 1) as [LE|LT].
 - assert (H : n=0 \/ n=1) by lia.
   destruct H as [-> | ->]; simpl; now rewrite ?f_k_0, ?f_k_1.
 - rewrite (depth_eqn k LT). lia.
Qed.

Lemma fs_depth k p n : depth k (fs k p n) = depth k n - p.
Proof.
 induction p; simpl.
 - lia.
 - rewrite f_depth, IHp. lia.
Qed.

Lemma depth_correct k n : n <> 0 -> fs k (depth k n) n = 1.
Proof.
 induction n as [[|[|n]] IH] using lt_wf_rec.
 - lia.
 - reflexivity.
 - intros _. rewrite depth_SS.
   set (n' := S (S n)) in *. rewrite iter_S. apply IH.
   + apply f_lt. unfold n'; lia.
   + apply f_nz. unfold n'; lia.
Qed.

Lemma depth_minimal k n : 1<n -> 1 < fs k (depth k n - 1) n.
Proof.
 induction n as [[|[|n]] IH] using lt_wf_rec.
 - lia.
 - lia.
 - intros _. rewrite depth_SS.
   simpl. rewrite Nat.sub_0_r.
   set (n' := S (S n)) in *.
   destruct (Nat.eq_dec (f k n') 1) as [->|NE].
   + simpl. unfold n'; lia.
   + assert (H : f k n' <> 0) by (apply f_nz; unfold n'; lia).
     assert (depth k (f k n') <> 0).
     { intro EQ. generalize (depth_correct k H). now rewrite EQ. }
     replace (depth k (f k n')) with (S (depth k (f k n') - 1)) by lia.
     rewrite iter_S.
     apply IH.
     * apply f_lt. unfold n'; lia.
     * lia.
Qed.

Lemma depth_mono k n m : n <= m -> depth k n <= depth k m.
Proof.
 revert m.
 induction n as [[|[|n]] IH] using lt_wf_rec; intros m H.
 - change (depth k 0) with 0. auto with arith.
 - change (depth k 1) with 0. auto with arith.
 - destruct m as [|[|m]]; try lia.
   rewrite 2 depth_SS.
   apply le_n_S.
   apply IH.
   + apply f_lt. lia.
   + now apply f_mono.
Qed.

Lemma depth_A k p : depth k (A k p) = p.
Proof.
 induction p as [|p IH].
 - reflexivity.
 - rewrite depth_eqn.
   + now rewrite f_A, S_sub_1, IH.
   + change 1 with (A k 0). apply A_lt. auto with arith.
Qed.

Lemma depth_SA k p : depth k (S (A k p)) = S p.
Proof.
 induction p as [|p IH].
 - simpl. unfold depth. simpl. rewrite f_init; simpl; lia.
 - rewrite depth_eqn.
   + rewrite f_SA, S_sub_1. f_equal. apply IH.
     auto with arith.
   + generalize (@A_nz k (S p)). lia.
Qed.

Lemma depth_is_0 k n : depth k n = 0 <-> n <= 1.
Proof.
 destruct n as [|[|n]].
 - rewrite depth_0; intuition.
 - rewrite depth_1; intuition.
 - rewrite depth_SS. lia.
Qed.

Lemma depth_carac k p n : p <> 0 ->
  (depth k n = p <-> S (A k (p-1)) <= n <= A k p).
Proof.
 intros Hp.
 split; intros H.
 - split.
   + destruct (le_lt_dec n (A k (p-1))) as [LE|LT]; trivial.
     apply (depth_mono k) in LE. rewrite depth_A in LE. lia.
   + destruct (le_lt_dec n (A k p)) as [LE|LT]; trivial.
     unfold lt in LT. apply (depth_mono k) in LT.
     rewrite depth_SA in LT; lia.
 - destruct H as (H1,H2).
   apply (depth_mono k) in H1. apply (depth_mono k) in H2.
   rewrite depth_A in H2. rewrite depth_SA in H1. lia.
Qed.

Lemma depth_init k n : depth k n = n-1 <-> n <= k+3.
Proof.
 destruct n as [|[|n]].
 - rewrite ?depth_0. lia.
 - rewrite ?depth_1. lia.
 - simpl.
   rewrite depth_carac by lia.
   rewrite S_sub_1.
   split; intros.
   + assert (A k n = S n) by (generalize (A_lt_id k n); lia).
     rewrite <- A_base_iff in *.
     lia.
   + simpl.
     rewrite A_base by lia.
     generalize (@A_nz k (n-k)). lia.
Qed.
