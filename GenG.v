
Require Import Arith Omega Wf_nat List Bool.
Require Import DeltaList Fib FunG GenFib.
Import ListNotations.
Require Extraction.
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
      See OEIS A5206
    - [F 2] is Hofstadter's [H], see OEIS A5374
*)

(** Coq representation of [F] as an inductive relation. This way,
    no need to convince Coq yet that [F] is indeed a function.
    - [F k n a] means that [Fk(n) = a].
    - [Fs p k n a] means that [Fk^p (n) = a].
*)

Inductive F : nat -> nat -> nat -> Prop :=
| F0 k : F k 0 0
| FS k n a b : Fs (S k) k n a -> S n = a+b -> F k (S n) b

with Fs : nat -> nat -> nat -> nat -> Prop :=
| Fs0 k n : Fs 0 k n n
| FsS p k a b c : Fs p k a b -> F k b c -> Fs (S p) k a c.

Hint Constructors F Fs.

(** Behavior of [F] and [Fs] when [n=0] and [1] *)

Lemma Fs_0 p k : Fs p k 0 0.
Proof.
 induction p; eauto.
Qed.
Hint Resolve Fs_0.

Lemma F_1 k : F k 1 1.
Proof.
 induction k; eauto.
Qed.
Hint Resolve F_1.

Lemma Fs_1 p k : Fs p k 1 1.
Proof.
 induction p; eauto.
Qed.
Hint Resolve Fs_1.

(** [F] and [Fs] aren't above the identity line *)

Lemma F_le k n a : F k n a -> a <= n.
Proof.
 induction 1; omega.
Qed.
Hint Resolve F_le.

Lemma Fs_le p k n a : Fs p k n a -> a <= n.
Proof.
 induction 1; trivial.
 transitivity b; eauto.
Qed.
Hint Resolve Fs_le.

(** [F] and [Fs] are functional relations : unique output *)

Scheme F_ind2 := Induction for F Sort Prop
  with Fs_ind2  := Induction for Fs Sort Prop.

Combined Scheme F_Fs_ind from F_ind2, Fs_ind2.

Lemma F_Fs_fun :
 (forall k n a, F k n a -> forall a', F k n a' -> a = a') /\
 (forall p k n a, Fs p k n a -> forall a', Fs p k n a' -> a = a').
Proof.
apply F_Fs_ind.
- inversion_clear 1; auto.
- intros k n a b HFs IH Hab a' HF.
  inversion_clear HF; auto.
  apply IH in H; omega.
- inversion_clear 1; auto.
- intros p k a b c HFs IH HF IH' a' HFs'.
  inversion_clear HFs'; auto.
  apply IH in H; subst; auto.
Qed.

Lemma F_fun k n a a' : F k n a -> F k n a' -> a = a'.
Proof.
 intro. now apply F_Fs_fun.
Qed.

Lemma Fs_fun p k n a a' : Fs p k n a -> Fs p k n a' -> a = a'.
Proof.
 intro. now apply F_Fs_fun.
Qed.

(** [F] does have an implementation : there exists a function [f]
    satisfying these equations. *)

Definition f_spec k n : { a : nat | F k n a }.
Proof.
induction n as [[|n] IH ] using lt_wf_rec.
- now exists 0.
- assert (Hs : forall p m, m <= n -> { a : nat | Fs p k m a }).
  { induction p.
    - intros. now exists m.
    - intros.
      destruct (IHp m H) as (a,Ha).
      destruct (IH a) as (b,Hb).
      apply Fs_le in Ha. omega.
      exists b; eauto. }
  destruct (Hs (S k) n) as (a,Ha); auto.
  exists (S n - a).
  eapply FS; eauto.
  apply Fs_le in Ha. omega.
Defined.

Definition f k n := proj1_sig (f_spec k n).

Lemma f_sound k n : F k n (f k n).
Proof.
unfold f; now destruct (f_spec k n).
Qed.
Hint Resolve f_sound.

Lemma f_complete k n a : F k n a <-> f k n = a.
Proof.
split; intros H.
- apply (F_fun (f_sound k n) H).
- subst; auto.
Qed.

(** A few examples *)

Definition nums := List.seq 0 26.

(*
Compute map (f 0) nums.
Compute map (f 1) nums.
Compute map (f 2) nums.
Compute map (f 3) nums.
*)
(*
f 0 = [0; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5; 6; 6; 7; 7]
f 1 = [0; 1; 1; 2; 3; 3; 4; 4; 5; 6; 6; 7; 8; 8; 9]
f 2 = [0; 1; 1; 2; 3; 4; 4; 5; 5; 6; 7; 7; 8; 9; 10]
f 3 = [0; 1; 1; 2; 3; 4; 5; 5; 6; 6; 7; 8; 8; 9; 10]
*)

(*
Extraction Inline lt_wf_rec induction_ltof2.
Recursive Extraction f.
*)

(** Basic equations over [f] : the same as [F] *)

Lemma f_k_0 k : f k 0 = 0.
Proof.
 reflexivity.
Qed.

Lemma f_k_1 k : f k 1 = 1.
Proof.
 now apply f_complete.
Qed.

Lemma Fs_iter_f p k n : Fs p k n ((f k ^^p) n).
Proof.
induction p.
- simpl. auto.
- eapply FsS; eauto. simpl.
  now rewrite f_complete.
Qed.

Lemma fs_k_0 p k : (f k ^^p) 0 = 0.
Proof.
 induction p; simpl; auto.
 rewrite IHp. apply f_k_0.
Qed.

Lemma fs_k_1 p k : (f k ^^p) 1 = 1.
Proof.
 induction p; simpl; auto.
 rewrite IHp. apply f_k_1.
Qed.

Lemma f_eqn k n : f k (S n) + (f k ^^ S k) n = S n.
Proof.
 assert (H := f_sound k (S n)).
 inversion_clear H.
 assert ((f k ^^ S k) n = a).
 { revert H0. apply Fs_fun. apply Fs_iter_f. }
 omega.
Qed.

Lemma f_eqn_pred k n : f k n + (f k ^^ S k) (pred n) = n.
Proof.
destruct n.
- now rewrite fs_k_0.
- apply f_eqn.
Qed.

Lemma f_S k n : f k (S n) = S n - (f k ^^ S k) n.
Proof.
 generalize (f_eqn k n). omega.
Qed.

Lemma f_pred k n : f k n = n - (f k ^^ S k) (pred n).
Proof.
 generalize (f_eqn_pred k n). omega.
Qed.

(** Particular case *)

Lemma f_1_g n : f 1 n = g n.
Proof.
revert n.
apply g_unique.
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
    replace (n + (S (n+0))) with (S (2*n)); omega. }
  split; auto.
  rewrite f_pred; auto.
  simpl Nat.iter.
  replace (S (n + (S (n+0)))) with (2*(S n)); omega.
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
- assert (forall p m, m <= n -> (h^^p) m = (f k ^^p) m).
  { induction p.
    - now simpl.
    - intros. simpl.
      rewrite IHp; auto. apply IH.
      rewrite Nat.lt_succ_r. apply le_trans with m; auto.
      eapply Fs_le. eapply Fs_iter_f. }
  rewrite f_S, <- H; auto. specialize (h_S n). omega.
Qed.

Lemma f_step k n : f k (S n) = f k n \/ f k (S n) = S (f k n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 destruct n.
 - rewrite f_k_0, f_k_1. now right.
 - rewrite 2 f_S.
   assert (forall p m, m <= n ->
           (f k ^^p) (S m) = (f k ^^p) m \/
           (f k ^^p) (S m) = S ((f k ^^p) m)).
   { induction p.
     - simpl; now right.
     - intros; simpl.
       destruct (IHp m H) as [-> | ->].
       + now left.
       + apply IH.
         rewrite Nat.lt_succ_r. apply le_trans with m; auto.
         eapply Fs_le. eapply Fs_iter_f. }
   specialize (H (S k) n). omega.
Qed.

Lemma fs_step k p n : (f k ^^p) (S n) = (f k ^^p) n \/
                      (f k ^^p) (S n) = S ((f k ^^p) n).
Proof.
 induction p; simpl.
 - now right.
 - destruct IHp as [-> | ->]. now left. apply f_step.
Qed.

Lemma f_mono_S k n : f k n <= f k (S n).
Proof.
 generalize (f_step k n). omega.
Qed.

Lemma fs_mono_S k p n : (f k ^^p) n <= (f k ^^p) (S n).
Proof.
 generalize (fs_step k p n). omega.
Qed.

Lemma f_le_add k n m : f k (n+m) <= n + f k m.
Proof.
induction n; trivial.
simpl. destruct (f_step k (n+m)); omega.
Qed.

Lemma f_mono k n m : n <= m -> f k n <= f k m.
Proof.
induction 1.
- trivial.
- transitivity (f k m); auto using f_mono_S.
Qed.

Lemma fs_mono k p n m : n <= m -> (f k^^p) n <= (f k^^p) m.
Proof.
induction 1.
- trivial.
- transitivity ((f k ^^p) m); auto using fs_mono_S.
Qed.

(** NB : in Coq, for natural numbers, 3-5 = 0 (truncated subtraction) *)

Lemma f_lipschitz k n m : f k m - f k n <= m - n.
Proof.
destruct (le_ge_dec n m) as [H|H].
- induction H; try generalize (f_step k m); omega.
- generalize (f_mono k H). omega.
Qed.

Lemma fs_lipschitz k p n m : (f k^^p) m - (f k^^p) n <= m - n.
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
 generalize (@f_nonzero k n). omega.
Qed.

Lemma f_0_inv k n : f k n = 0 -> n = 0.
Proof.
 generalize (@f_nz k n). omega.
Qed.

Lemma fs_nonzero k n p : 0 < n -> 0 < (f k ^^p) n.
Proof.
 revert n. induction p; simpl; auto using f_nonzero.
Qed.

Lemma fs_0_inv k n p : (f k ^^p) n = 0 -> n = 0.
Proof.
 generalize (@fs_nonzero k n p). omega.
Qed.

Lemma f_fix k n : f k n = n <-> n <= 1.
Proof.
split.
- destruct n; auto.
  assert (H := f_eqn k n).
  intros.
  assert (H' : (f k ^^S k) n = 0) by omega.
  apply fs_0_inv in H'.
  now subst.
- inversion_clear 1. apply f_k_1.
  inversion_clear H0. apply f_k_0.
Qed.

Lemma f_le k n : f k n <= n.
Proof.
 eapply F_le; eauto.
Qed.

Lemma fs_le k p n : (f k^^p) n <= n.
Proof.
 eapply Fs_le, Fs_iter_f.
Qed.

Lemma f_lt k n : 1<n -> f k n < n.
Proof.
intros H.
destruct (le_lt_or_eq _ _ (f_le k n)); trivial.
rewrite f_fix in *. omega.
Qed.
Hint Resolve f_lt.

(** Two special formulations for [f_step] *)

Lemma f_next k n a : f k n = a -> (f k (S n) <> a <-> f k (S n) = S a).
Proof.
 generalize (f_step k n). omega.
Qed.

Lemma f_prev k n a : n <> 0 -> f k n = a ->
 (f k (n-1) <> a <-> f k (n-1) = a - 1).
Proof.
 intros H Ha.
 assert (Ha' := f_nz k H).
 generalize (f_step k (n-1)). replace (S (n-1)) with n; omega.
Qed.

(** [f] cannot stay flat very long *)

Lemma f_nonflat k n : f k (1+n) = f k n -> f k (2+n) = S (f k n).
Proof.
 generalize (f_eqn k (1+n)) (f_eqn k n).
 rewrite !iter_S. intros. rewrite H1 in *. simpl in *. omega.
Qed.

Lemma f_nonflat' k n : f k (S n) = f k n -> f k (n-1) = f k n - 1.
Proof.
 destruct n.
 - now rewrite f_k_0, f_k_1.
 - replace (S n - 1) with n by omega.
   intros H.
   destruct (f_step k n) as [H'|H'].
   + apply f_nonflat in H'; auto. simpl in *. omega.
   + omega.
Qed.

Lemma f_SS k n : f k n < f k (S (S n)).
Proof.
 destruct (f_step k n) as [E|E].
 - generalize (f_nonflat _ _ E). simpl in *. omega.
 - apply Nat.lt_le_trans with (f k (S n)). omega. auto using f_mono_S.
Qed.

Lemma f_double_le k n : n <= f k (2*n).
Proof.
induction n.
- trivial.
- replace (2* S n) with (S (S (2*n))) by omega.
  transitivity (S (f k (2*n))). omega. now apply f_SS.
Qed.

Lemma f_div2_le k n : n/2 <= f k n.
Proof.
 rewrite <- Nat.div2_div.
 rewrite (Nat.div2_odd n) at 2.
 transitivity (f k (2*Nat.div2 n)).
 now apply f_double_le.
 apply f_mono. omega.
Qed.

Lemma fs_bound k n p :
  1 < n -> 1 < (f k ^^p) n -> (f k ^^p) n <= n-p.
Proof.
 revert n.
 induction p.
 - simpl. intros. omega.
 - intros. simpl in *.
   assert (LE : 1 <= (f k ^^p) n).
   { generalize (@fs_nonzero k n p). omega. }
   assert (NE : (f k^^p) n <> 1).
   { intros EQ; rewrite EQ, f_k_1 in *. omega. }
   specialize (IHp n H).
   generalize (@f_lt k ((f k^^p) n)). omega.
Qed.

Lemma fs_init k n : 1 <= n <= k+2 -> (f k^^(S k)) n = 1.
Proof.
 intros.
 destruct (Nat.eq_dec n 1) as [->|NE].
 - now rewrite fs_k_1.
 - destruct (le_lt_dec ((f k^^S k) n) 1) as [LE|LT].
   + generalize (@fs_nonzero k n (S k)). omega.
   + apply fs_bound in LT; try omega.
     generalize (@fs_nonzero k n (S k)). omega.
Qed.

Lemma f_init k n : 2 <= n <= k+3 -> f k n = n-1.
Proof.
 intros. rewrite f_pred. rewrite fs_init; omega.
Qed.

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
 induction n; simpl; rewrite ?IHn; omega.
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
 - replace (S m - x) with (S (m-x)) by omega. simpl; auto.
Qed.

(** With [ftabulate],  we will build at once the list
    [[f k n; f k (n-1); ... ; f k 0]].
    And [fdescend] visits this list to compute [((f k)^^p) n].
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
 stk = map (f k) (countdown n) -> fdescend stk p n = ((f k)^^p) n.
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
 destruct (le_lt_dec (2+n) m) as [LE|LT]; try omega.
 apply (f_mono k) in LE.
 rewrite (f_nonflat k n) in LE. omega.
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
  destruct (f_step k n); [ | exists (S n); omega].
  destruct (f_step k (S n)); [ | exists (S (S n)); omega].
  exfalso.
  generalize (@f_max_two_antecedents k n (S (S n))). omega.
Qed.

(** We even have an explicit expression of one antecedent *)

Definition rchild k n := n + (f k ^^ k) n.
Definition lchild k n := n + (f k ^^ k) n - 1. (** left son, if there's one *)

Lemma rightmost_child_carac k a n : f k n = a ->
 (f k (S n) = S a <-> n = rchild k a).
Proof.
 intros Hn.
 assert (H' := f_eqn k n).
 rewrite iter_S in H'.
 rewrite Hn in H'.
 unfold rchild; omega.
Qed.

Lemma f_onto_eqn k a : f k (rchild k a) = a.
Proof.
destruct (f_onto k a) as (n,Hn).
destruct (f_step k n) as [H|H].
- unfold rchild.
  rewrite <- Hn. rewrite <- H at 1 3. f_equal.
  rewrite <- iter_S. apply f_eqn.
- rewrite Hn in H.
  rewrite rightmost_child_carac in H; trivial. congruence.
Qed.

Lemma f_children k a n : f k n = a ->
  n = rchild k a \/ n = lchild k a.
Proof.
intros Hn.
destruct (f_step k n) as [H|H].
- right.
  destruct (f_step k (S n)) as [H'|H'].
  + exfalso.
    generalize (@f_max_two_antecedents k n (S (S n))). omega.
  + rewrite rightmost_child_carac in H'; trivial.
    rewrite H, Hn in H'. unfold lchild, rchild in *; omega.
- rewrite <- (@rightmost_child_carac k a n); omega.
Qed.

Lemma f_lchild k a :
 f k (lchild k a) = a - 1 \/ f k (lchild k a) = a.
Proof.
 destruct (le_gt_dec a 0).
  + replace a with 0 by omega. unfold lchild.
    rewrite fs_k_0. simpl. rewrite f_k_0. now left.
  + assert (0 < rchild k a)
     by (unfold rchild; generalize (@f_nonzero k a); omega).
    destruct (f_step k (lchild k a)) as [H'|H'];
    replace (S (lchild k a)) with (rchild k a) in * by
      (unfold lchild, rchild in *; omega);
    rewrite f_onto_eqn in *; omega.
Qed.


(** This provides easily a first relationship between f and
    generalized Fibonacci numbers *)

Lemma fs_A k n p : (f k ^^p) (A k n) = A k (n-p).
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
 replace (n-1-k) with (n-S k) by omega.
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
   intros; omega. apply decomp_delta.
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
   rewrite IHp; auto with arith.
   rewrite fbis_decomp.
   rewrite renorm_mapdecr; auto. f_equal.
   symmetry. apply map_decr_S.
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
       rewrite renorm_mapdecr'; simpl; auto with arith.
       rewrite Nat.add_shuffle1.
       assert (~In 0 l).
       { apply (@Delta_nz' (S k) a); auto with arith. }
       rewrite <- sumA_eqn_pred; auto.
       rewrite decr_0.
       unfold decr. replace (a-S k) with 0; simpl in *; omega.
     * rewrite map_cons, sumA_cons.
       rewrite <- Nat.add_assoc.
       rewrite <- map_decr_1.
       rewrite <- sumA_eqn_pred; auto.
       eapply Delta_nz; eauto. omega.
Qed.

Lemma f_decomp k n : f k n = sumA k (map pred (decomp k n)).
Proof.
 symmetry. apply fbis_is_f.
Qed.

Lemma fs_decomp k p n :
  p <= S k -> (f k^^p) n = sumA k (map (decr p) (decomp k n)).
Proof.
 intros.
 rewrite <- fsbis; auto.
 symmetry. clear.
 induction p; auto. simpl. rewrite IHp. apply fbis_is_f.
Qed.

Lemma f_sumA k l : Delta (S k) l ->
 f k (sumA k l) = sumA k (map pred l).
Proof.
 intros. rewrite f_decomp. f_equal. f_equal. auto.
Qed.

Lemma fs_sumA k p l : p <= S k -> Delta (S k) l ->
 (f k ^^p) (sumA k l) = sumA k (map (decr p) l).
Proof.
 intros. rewrite fs_decomp; auto. f_equal. f_equal. auto.
Qed.

Lemma f_sumA_lax k l : k<>0 -> Delta k l ->
 f k (sumA k l) = sumA k (map pred l).
Proof.
 intros. rewrite <- renorm_sum.
 rewrite f_sumA; auto.
 rewrite <- !map_decr_1, renorm_mapdecr; auto. omega.
Qed.

Lemma fs_sumA_lax k p l : p < S k -> Delta k l ->
 (f k ^^p) (sumA k l) = sumA k (map (decr p) l).
Proof.
 intros. rewrite <- renorm_sum.
 rewrite fs_sumA; auto with arith.
 now apply renorm_mapdecr.
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
     rewrite renorm_mapdecr'.
     * simpl.
       rewrite decr_0.
       rewrite !A_base by (auto; omega).
       split. intuition. injection 1 as ->. omega.
     * apply Delta_S_cons. rewrite <- E; auto.
     * simpl. auto with arith.
   + simpl. split. intuition. injection 1 as ->. omega.
Qed.

Lemma nonflat_rank_nz k n :
 f k (S n) = S (f k n) <-> rank k n <> Some 0.
Proof.
 rewrite <- flat_rank_0.
 generalize (f_step k n). omega.
Qed.

(** At most [k+1] consecutive [+1] steps *)

Lemma f_maxsteps k n :
 f k (n+k+2) <= f k n + k+1.
Proof.
 destruct (rank_later_is_zero k n) as (p & LE & H).
 apply flat_rank_0 in H.
 transitivity (f k (S (p + n)) + (k+2-S p)).
 - generalize (f_lipschitz k (S (p+n)) (n+k+2)). omega.
 - rewrite H.
   generalize (f_lipschitz k n (p+n)). omega.
Qed.

(** TODO: exactly [k+1] consecutive [+1] steps when [n = 2 + A k p]
    with [p>2k]. *)

(** Beware, when comparing an [option nat] and a [nat],
    [None] serves as a bottom element, not comparable with any [nat]. *)

Definition olt (o : option nat) n :=
 match o with
 | None => False
 | Some a => a < n
 end.

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
   + assert (Hd := renorm_head k (S a ::l)).
     destruct renorm. intuition.
     destruct Hd as (m,Hd); simpl in Hd.
     split; auto with arith.
     intros _. injection 1 as ->. discriminate.
   + intuition.
Qed.

Lemma fs_flat_low_rank k p n : p <= S k ->
 (f k ^^p) (S n) = (f k ^^p) n <-> (rank k n < p)%onat.
Proof.
 intros Hp.
 apply Nat.lt_eq_cases in Hp.
 destruct Hp as [Hp| ->].
 - rewrite !fs_decomp by auto with arith.
   unfold rank.
   rewrite decomp_S.
   destruct (decomp k n) as [|a l] eqn:E.
   + simpl. intuition.
   + simpl.
     case Nat.leb_spec; intros.
     * rewrite renorm_mapdecr by omega.
       rewrite map_cons, sumA_cons.
       unfold decr at 1 3.
       rewrite !A_base by (auto; omega).
       omega.
     * simpl. intuition.
 - rewrite <- rank_S_nz_iff.
   rewrite <- nonflat_rank_nz.
   rewrite 2 f_S.
   generalize (fs_le k (S k) n).
   omega.
Qed.

Lemma fs_nonflat_high_rank k p n : p <= S k ->
  (f k ^^p) (S n) = S ((f k ^^p) n) <-> ~(rank k n < p)%onat.
Proof.
 intros Hp.
 rewrite <- fs_flat_low_rank by trivial.
 assert (LE := fs_lipschitz k p n (S n)).
 replace (S n - n) with 1 in LE by omega.
 generalize (@fs_mono k p n (S n)). omega.
Qed.

Lemma fs_nonflat_high_rank' k p n : p <= S k ->
  (f k ^^p) (S n) = S ((f k ^^p) n) <->
  match rank k n with
  | None => True
  | Some a => p <= a
  end.
Proof.
 intros.
 rewrite fs_nonflat_high_rank by trivial.
 destruct rank; simpl; intuition.
Qed.

(** [(f k)^^p] cannot have more than [p+1] consecutive flats *)

Lemma fs_maxflat k n p : p <= S k ->
 (f k^^p) n < (f k^^p) (n+p+1).
Proof.
 intros Hp.
 destruct (rank k n) as [r|] eqn:Hr.
 - destruct (@rank_later_is_high k n r p Hp Hr) as (r' & q & H1 & H2 & H3).
   assert (E : (f k ^^p) (S (q+n)) = S ((f k^^p) (q+n))).
   { apply fs_nonflat_high_rank; auto. rewrite H2. simpl. omega. }
   unfold lt.
   transitivity (S ((f k ^^p) (q+n))).
   + apply -> Nat.succ_le_mono. apply fs_mono. omega.
   + rewrite <- E. apply fs_mono. omega.
 - rewrite rank_none in *. subst.
   rewrite fs_k_0. apply fs_nonzero. omega.
Qed.

(** * Another equation about [f]

    This one will be used later when flipping [F] left/right. *)

Lemma f_alt_eqn k n : f k n + (f k^^k) (f k (S n) - 1) = n.
Proof.
 destruct (Nat.eq_dec n 0) as [-> |Hn].
 - simpl. rewrite f_k_1. simpl. now rewrite fs_k_0.
 - assert (Hn' := f_nz k Hn).
   case (f_step k n) as [H|H].
   + (* n left child of a binary node *)
     rewrite H.
     generalize (f_eqn k (n-1)).
     case (f_step k (n - 1));
     replace (S (n - 1)) with n by omega.
     * generalize (@f_max_two_antecedents k (n-1) (S n)). omega.
     * intros. replace (f k n - 1) with (f k (n-1)) by omega.
       rewrite iter_S in *. omega.
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
   + generalize (@f_lt k (S (S n))). omega.
   + generalize (@f_lt k (S (S n))). omega.
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
 generalize (@f_lt k (S m)). omega.
Qed.

Lemma depth_eqn k n : 1<n -> depth k n = S (depth k (f k n)).
Proof.
 destruct n as [|[|n]].
 - omega.
 - omega.
 - intros _. apply depth_SS.
Qed.

Lemma f_depth k n : depth k (f k n) = depth k n - 1.
Proof.
 destruct (le_lt_dec n 1) as [LE|LT].
 - assert (H : n=0 \/ n=1) by omega.
   destruct H as [-> | ->]; simpl; now rewrite ?f_k_0, ?f_k_1.
 - rewrite (depth_eqn k LT). omega.
Qed.

Lemma fs_depth k p n : depth k ((f k ^^ p) n) = depth k n - p.
Proof.
 induction p; simpl.
 - omega.
 - rewrite f_depth, IHp. omega.
Qed.

Lemma depth_correct k n : n <> 0 -> (f k^^(depth k n)) n = 1.
Proof.
 induction n as [[|[|n]] IH] using lt_wf_rec.
 - omega.
 - reflexivity.
 - intros _. rewrite depth_SS.
   set (n' := S (S n)) in *. rewrite iter_S. apply IH.
   + apply f_lt. unfold n'; omega.
   + apply f_nz. unfold n'; omega.
Qed.

Lemma depth_minimal k n : 1<n -> 1 < ((f k^^(depth k n - 1)) n).
Proof.
 induction n as [[|[|n]] IH] using lt_wf_rec.
 - omega.
 - omega.
 - intros _. rewrite depth_SS.
   simpl. rewrite <- minus_n_O.
   set (n' := S (S n)) in *.
   destruct (Nat.eq_dec (f k n') 1) as [->|NE].
   + simpl. unfold n'; omega.
   + assert (H : f k n' <> 0) by (apply f_nz; unfold n'; omega).
     assert (depth k (f k n') <> 0).
     { intro EQ. generalize (depth_correct k H). now rewrite EQ. }
     replace (depth k (f k n')) with (S (depth k (f k n') - 1)) by omega.
     rewrite iter_S.
     apply IH.
     * apply f_lt. unfold n'; omega.
     * omega.
Qed.

Lemma depth_mono k n m : n <= m -> depth k n <= depth k m.
Proof.
 revert m.
 induction n as [[|[|n]] IH] using lt_wf_rec; intros m H.
 - change (depth k 0) with 0. auto with arith.
 - change (depth k 1) with 0. auto with arith.
 - destruct m as [|[|m]]; try omega.
   rewrite 2 depth_SS.
   apply le_n_S.
   apply IH.
   + apply f_lt. omega.
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
 - simpl. unfold depth. simpl. rewrite f_init; auto with arith.
 - rewrite depth_eqn.
   + rewrite f_SA, S_sub_1. f_equal. apply IH.
     auto with arith.
   + generalize (@A_nz k (S p)). omega.
Qed.

Lemma depth_is_0 k n : depth k n = 0 <-> n <= 1.
Proof.
 destruct n as [|[|n]].
 - rewrite depth_0; intuition.
 - rewrite depth_1; intuition.
 - rewrite depth_SS. omega.
Qed.

Lemma depth_carac k p n : p <> 0 ->
  (depth k n = p <-> S (A k (p-1)) <= n <= A k p).
Proof.
 intros Hp.
 split; intros H.
 - split.
   + destruct (le_lt_dec n (A k (p-1))) as [LE|LT]; trivial.
     apply (depth_mono k) in LE. rewrite depth_A in LE. omega.
   + destruct (le_lt_dec n (A k p)) as [LE|LT]; trivial.
     unfold lt in LT. apply (depth_mono k) in LT.
     rewrite depth_SA in LT; omega.
 - destruct H as (H1,H2).
   apply (depth_mono k) in H1. apply (depth_mono k) in H2.
   rewrite depth_A in H2. rewrite depth_SA in H1. omega.
Qed.

Lemma depth_init k n : depth k n = n-1 <-> n <= k+3.
Proof.
 destruct n as [|[|n]].
 - rewrite ?depth_0. omega.
 - rewrite ?depth_1. omega.
 - simpl.
   rewrite depth_carac by omega.
   rewrite S_sub_1.
   split; intros.
   + assert (A k n = S n) by (generalize (A_lt_id k n); omega).
     rewrite <- A_base_iff in *.
     omega.
   + simpl.
     rewrite A_base by omega.
     generalize (@A_nz k (n-k)). omega.
Qed.

(*========================================================*)

(** Study of quasi-additivity : [f k (p+n)] is close to [f k p + f k n].
    Said otherwise, for some fixed p, few values are reached by
    [f k (p+n)-f k n] when n varies.
    For this study, we'll turn a strict k-decomposition of n into
    a lax decomp of (p+n).
*)

(** Split a decomposition in two, all the left being <= p *)

Fixpoint getprefix p l :=
 match l with
 | [] => ([],[])
 | a::l' => if p <? a then ([],l)
            else let '(l1,l2) := getprefix p l' in (a::l1,l2)
 end.

Lemma getprefix_app p l :
  let '(l1,l2) := getprefix p l in l1++l2 = l.
Proof.
 induction l; simpl; auto.
 case Nat.ltb_spec; simpl; auto. intros LE.
 destruct getprefix. simpl. f_equal. auto.
Qed.

Lemma getprefix_fst p l :
  Below (fst (getprefix p l)) (S p).
Proof.
 induction l as [|a l IH]; simpl.
 - unfold Below; simpl. intuition.
 - case Nat.ltb_spec.
   + unfold Below; simpl; intuition.
   + destruct getprefix. unfold Below in *; simpl in *. intuition.
Qed.

Lemma getprefix_snd p l a l':
  snd (getprefix p l) = a::l' -> p < a.
Proof.
 induction l as [|b l IH]; simpl.
 - inversion 1.
 - case Nat.ltb_spec.
   + simpl. intros LT [= -> ->]; auto.
   + intros _. destruct getprefix. simpl in *; auto.
Qed.

Lemma Delta_getprefix k p m l :
 Delta k (p :: l) -> m < p+k -> getprefix m l = ([],l).
Proof.
 inversion_clear 1; auto. simpl.
 case Nat.ltb_spec; auto. omega.
Qed.

(** Any number has a [A] number above it. *)

Definition invA_up k n := S (invA k (n-2)).

Lemma invA_up_spec k n : n <= A k (invA_up k n).
Proof.
 unfold invA_up.
 destruct (invA_spec k (n-2)) as (_,H). omega.
Qed.

(* To add p to a strict k-decomposition (while possibly relaxing it),
   no need to dig deeper than value [3*k+(invA_up k p)-1].
   Note : tighter upper bounds than that could probably be found,
   but seem harder to prove *)

Lemma increase_bottom_decomp k p : k<>0 ->
  forall l, Delta (S k) l ->
   exists l1 l1' l2,
     l = l1 ++ l2 /\
     sumA k l1' = p + sumA k l1 /\
     Below l1 (3*k + invA_up k p - 1) /\
     Delta k (l1'++l2).
Proof.
 intros Hk l D.
 set (u := k+invA_up k p).
 assert (Hu : 0 < u).
 { unfold u, invA_up. omega. }
 destruct (getprefix (u-1) l) as (l1,l2) eqn:E.
 assert (E' := getprefix_app (u-1) l). rewrite E in E'.
 assert (B1 := getprefix_fst (u-1) l). rewrite E in B1. simpl in B1.
 replace (S (u-1)) with u in B1 by omega.
 assert (U := invA_up_spec k p).
 replace (invA_up k p) with (u-k) in U by omega.
 destruct l2 as [|a l2].
 - exists l1, (decomp k (p+sumA k l)), [].
   repeat split; auto.
   + rewrite decomp_sum. rewrite <- E', app_nil_r. auto.
   + intros x Hx. specialize (B1 x Hx). omega.
   + rewrite app_nil_r. apply Delta_S, decomp_delta.
 - assert (Ha : u <= a).
   { assert (B1' := @getprefix_snd (u-1) l a l2). rewrite E in B1'.
     simpl in B1'. specialize (B1' eq_refl). omega. }
   destruct (Nat.ltb_spec a (2*k+u-1)).
   + destruct (decompminus_spec k (l1++[S a]) (A k (S a)-A k a-p))
       as (l1' & E1' & D1' & B1').
     exists (l1++[a]), l1', l2.
     repeat split.
     * rewrite <- E'. now rewrite app_ass.
     * rewrite E1'. rewrite !sumA_app.
       assert (LE : p <= A k (a-k)).
       { transitivity (A k (u-k)); auto. apply A_mono. clear - Hu Ha. omega. }
       clear -LE.
       replace (A k (S a) - A k a) with (A k (a-k)); simpl; omega.
     * intro x. rewrite in_app_iff. intros [IN|[<-|[]]]; try omega.
       specialize (B1 x IN). omega.
     * { rewrite <- E', Delta_app_iff in D.
         destruct D as (D1 & D2 & D3).
         apply Delta_app with (S a).
         - apply D1'.
           apply Delta_app_iff; repeat split.
           + apply Delta_S, D1.
           + constructor.
           + intros x x' Hx [<-|[]]. specialize (D3 x a Hx).
             simpl in D3. intuition.
         - now apply Delta_S_cons.
         - intro y. rewrite <- Nat.lt_succ_r. apply B1'.
           intro z. rewrite in_app_iff. intros [Hz|[<-|[]]].
           + specialize (B1 z Hz). omega.
           + omega. }
   + destruct (decompminus_spec k (l1++[k+u-1]) (A k (k+u-1)-p))
       as (l1' & E1' & D1' & B1').
     exists l1,l1',(a::l2).
     repeat split.
     * symmetry. apply E'.
     * rewrite E1'. rewrite sumA_app.
       simpl.
       assert (LE : p <= A k (k+u-1)).
       { transitivity (A k (u-k)); auto.
         apply A_mono. omega. }
       omega.
     * intros x Hx. specialize (B1 x Hx). omega.
     * { rewrite <- E', Delta_app_iff in D.
         destruct D as (D1 & D2 & D3).
         apply Delta_app with (k+u-1).
         - apply D1'.
           apply Delta_app_iff; repeat split.
           + apply Delta_S, D1.
           + constructor.
           + intros x x' Hx [<-|[]]. specialize (B1 x Hx). omega.
         - constructor. omega. now apply Delta_S.
         - intro y. rewrite <- Nat.lt_succ_r. apply B1'.
           intro z. rewrite in_app_iff. intros [Hz|[<-|[]]].
           + specialize (B1 z Hz). omega.
           + omega. }
Qed.

(* So, all values taken by [f k (p+n)-f k n] when n varies in [nat] are
   values that are already encountered when n varies in just
   [0..add_bound k p[. *)

Definition add_bound k p := A k (3*k + invA_up k p - 1).

Lemma additivity_bounded k p : k<>0 ->
 forall n, exists m,
   m < add_bound k p /\
   f k (p+n) - f k n = f k (p+m) - f k m.
Proof.
 intros Hk n.
 destruct (decomp_exists k n) as (l & E & D).
 destruct (@increase_bottom_decomp k p Hk l D)
   as (l1 & l1' & l2 & El & E1 & B1 & D1).
 exists (sumA k l1).
 split.
 - unfold add_bound. set (q := 3*k+invA_up k p-1) in *. clearbody q.
   rewrite El in D. apply Delta_app_inv in D.
   rewrite <- DeltaRev_rev in D.
   rewrite <- sumA_rev.
   assert (B1r : Below (rev l1) q).
   { intro y. rewrite <- in_rev. apply B1. }
   destruct (rev l1) as [|a l1r].
   + simpl. apply A_nz.
   + apply Nat.lt_le_trans with (A k (S a)).
     * apply decomp_max; auto. apply D.
     * apply A_mono. apply B1r. now left.
 - rewrite <- E.
   rewrite El at 1. rewrite sumA_app, Nat.add_assoc, <- E1, <- sumA_app.
   rewrite !f_sumA_lax; auto using Delta_S.
   + rewrite El, !map_app, !sumA_app. omega.
   + rewrite El in D. apply Delta_app_inv in D. apply Delta_S, D.
   + apply Delta_app_inv in D1. apply D1.
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
 replace p with ((p+m)-m) at 2 by omega.
 rewrite npop_countdown by omega.
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
 rewrite countdown_in. omega.
Qed.

Lemma decide_additivity k p a b : k<>0 ->
 check_additivity (fun m => andb (a <=? m) (m <=? b)) k p = true ->
 forall n, a + f k n <= f k (p+n) <= b + f k n.
Proof.
 intros.
 assert (f k n <= f k (p+n)) by (apply f_mono; omega).
 assert (a <= f k (p+n) - f k n <= b); try omega.
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
 unfold h. destruct (f_step 2 n); simpl; omega.
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
         and in [-1..1] when m is a [A 3] number.
   Proof: ??
*)

(* Combined with g_add_8, h_add_8 is enough to show that g <= h *)

Lemma g_below_h n : g n <= h n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 8).
- do 8 (destruct n; [compute; auto|]). omega.
- replace n with (8+(n-8)) by omega.
  transitivity (5 + g (n - 8)). apply g_add_8.
  transitivity (5 + h (n - 8)). 2:apply h_add_8.
  specialize (IH (n-8)). omega.
Qed.

(* TODO: g_below_h can be generalized into :
   Conjecture : forall k n, f k n <= f (S k) n
   Proof : ??
*)

(* f 3 *)

Lemma fk_add_1 k n : f k n <= f k (1+n) <= 1 + f k n.
Proof.
 unfold h. destruct (f_step k n); simpl; omega.
Qed.

Lemma fk_add_2 k n : 1 + f k n <= f k (2+n) <= 2 + f k n.
Proof.
 unfold h. split.
 - generalize (f_SS k n). simpl. omega.
 - apply f_le_add.
Qed.

Lemma fk_add_3 k n : 1 + f k n <= f k (3+n) <= 3 + f k n.
Proof.
 split.
 - transitivity (f k (2+n)). apply fk_add_2. apply f_mono. omega.
 - apply f_le_add.
Qed.

Lemma fk_add_4 k n : 2 + f k n <= f k (4+n) <= 4 + f k n.
Proof.
 split.
 - transitivity (1 + f k (2 + n)).
   + generalize (fk_add_2 k n). omega.
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

Lemma h_below_f3 n : h n <= f 3 n.
Proof.
induction n as [n IH] using lt_wf_ind.
destruct (Nat.lt_ge_cases n 33).
- unfold h. rewrite <- !fopt_spec.
  do 33 (destruct n; [vm_compute; auto|]). omega.
- replace n with (33+(n-33)) by omega.
  transitivity (23 + h (n - 33)). apply h_add_33.
  transitivity (23 + f 3 (n - 33)).
  specialize (IH (n-33)). omega.
  apply (f3_add_33 (n-33)).
Qed.

(* TODO general bounds for f3(n+m)-f3(n)-f3(m) ??
   Same for any fk ??
*)
