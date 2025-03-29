
Require Import MoreTac MoreFun MoreList DeltaList GenFib.
Require FunG.
Import ListNotations.
Set Implicit Arguments.

(** Study of the functional equation:
     - [Fk 0 = 0]
     - [Fk (S n) + Fk^k (n) = S n]
    where [Fq^k (n)] is [k] repeated applications of [Fk] at [n].

    With this setting:
    - [F 0] is [fun n => match n with 0 => 0 | _ => 1 end].
    - [F 1] is [fun x => floor((x+1)/2)] (see below).
    - [F 2] is Hofstadter's [G] i.e. [fun x => floor((x+1)/phi]
      See http://oeis.org/A5206
    - [F 3] is Hofstadter's [H], see http://oeis.org/A5374
    - [F 4] is http://oeis.org/A5375
    - [F 5] is http://oeis.org/A5376
*)

(** Coq representation of [F] as an inductive relation. This way,
    no need to convince Coq yet that [F] is indeed a function.
    - [F k n a] means that [Fk(n) = a].
    - [Fs k p n a] means that [Fk^p (n) = a].
*)

Inductive F (k:nat) : nat -> nat -> Prop :=
| F0 : F k 0 0
| FS n a b : Fs k k n a -> S n = a+b -> F k (S n) b

with Fs (k:nat) : nat -> nat -> nat -> Prop :=
| Fs0 n : Fs k 0 n n
| FsS p a b c : Fs k p a b -> F k b c -> Fs k (S p) a c.

#[global] Hint Constructors F Fs : hof.

(** The early behavior of [F] and [Fs] when [n<=2] does not depend on k.
    Moreover [F] at 3 is always 2 as soon as [k<>0]. *)

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

Lemma F_3 k : k<>0 -> F k 3 2.
Proof.
 induction k; eautoh.
Qed.
#[global] Hint Resolve F_3 : hof.

Lemma Fs_3 k p : k<>0 -> Fs k p 3 (1+(2-p)).
Proof.
 intros Hk.
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
 | S p, S n => S n - ((recf k p)^^k) n
 | _, _ => 0
 end.

Definition f k n := recf k n n.
Notation fs k p := (f k ^^p).

Lemma recf_le k p n : recf k p n <= n.
Proof.
 induction p; cbn - ["-" "^^"]. lia. destruct n; lia.
Qed.

Lemma recfs_le a k p n : ((recf k p)^^a) n <= n.
Proof.
 induction a; simpl; auto. etransitivity. apply recf_le. apply IHa.
Qed.

Lemma recf_sound k p n : n <= p -> F k n (recf k p n).
Proof.
revert n.
induction p.
- inversion 1. simpl. constructor.
- destruct n.
  + simpl. constructor.
  + cbn - ["-" "^^"].
    assert (IHa : forall a m, m <= p -> Fs k a m ((recf k p ^^ a) m)).
    { induction a; intros; simpl; econstructor; eauto.
      apply IHp. transitivity m; auto using recfs_le. }
    econstructor. apply IHa. lia.
    generalize (recfs_le k k p n). lia.
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
Compute take 26 (f 1).
Compute take 26 (f 2).
Compute take 26 (f 3).
Compute take 26 (f 4).
*)
(*
f 1 : [0; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5; 6; 6; 7; 7]
f 2 : [0; 1; 1; 2; 3; 3; 4; 4; 5; 6; 6; 7; 8; 8; 9]
f 3 : [0; 1; 1; 2; 3; 4; 4; 5; 5; 6; 7; 7; 8; 9; 10]
f 4 : [0; 1; 1; 2; 3; 4; 5; 5; 6; 6; 7; 8; 8; 9; 10]
*)

(* The first values of [f] when [n<=2] do not depend on [q].
   Moreover [f k 3 = 2] as soon as [k<>0]. *)

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

Lemma f_k_3 k : k<>0 -> f k 3 = 2.
Proof.
 intros. apply f_complete; autoh.
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

Lemma f_eqn k n : f k (S n) + fs k k n = S n.
Proof.
 assert (H := f_sound k (S n)).
 inversion_clear H.
 assert (fs k k n = a).
 { revert H0. apply Fs_fun. apply Fs_iter_f. }
 lia.
Qed.

Lemma f_eqn_pred k n : f k n + fs k k (pred n) = n.
Proof.
destruct n.
- now rewrite fs_k_0.
- apply f_eqn.
Qed.

Lemma f_S k n : f k (S n) = S n - fs k k n.
Proof.
 generalize (f_eqn k n). lia.
Qed.

Lemma f_pred k n : f k n = n - fs k k (pred n).
Proof.
 generalize (f_eqn_pred k n). lia.
Qed.

(** Particular case *)

Lemma f_0 n : f 0 n = min 1 n.
Proof.
 rewrite f_pred. unfold fs. simpl. destruct n; lia.
Qed.

Lemma f_2_g n : f 2 n = FunG.g n.
Proof.
revert n.
apply FunG.g_unique.
- reflexivity.
- intros n. symmetry. now apply f_eqn.
Qed.

Lemma f_1_half n : f 1 (2*n) = n /\ f 1 (S (2*n)) = S n.
Proof.
induction n.
- now compute.
- assert (f 1 (2*(S n)) = S n).
  { rewrite f_pred; auto.
    simpl Nat.iter.
    replace (n + (S (n+0))) with (S (2*n)); lia. }
  split; auto.
  rewrite f_pred; auto.
  simpl Nat.iter.
  replace (S (n + (S (n+0)))) with (2*(S n)); lia.
Qed.

Lemma f_1_div2 n : f 1 n = (S n) / 2.
Proof.
rewrite <- Nat.div2_div.
destruct (Nat.Even_or_Odd n) as [(m,->)|(m,->)].
- destruct (f_1_half m) as (->,_).
  symmetry. apply Nat.div2_succ_double.
- rewrite Nat.add_1_r.
  destruct (f_1_half m) as (_,->).
  simpl. f_equal.
  symmetry. apply (Nat.div2_double m).
Qed.

Lemma f_unique k h :
  h 0 = 0  ->
  (forall n, S n = h (S n)+ (h^^k) n) ->
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
   specialize (H k n). lia.
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
  assert (H' : fs k k n = 0) by lia.
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
 generalize (f_step k (n-1)). fixpred; lia.
Qed.

(** [f] cannot stay flat very long *)

Lemma f_nonflat k n : k<>0 -> f k (1+n) = f k n -> f k (2+n) = S (f k n).
Proof.
 intros Hk.
 generalize (f_eqn k (1+n)) (f_eqn k n).
 replace (fs k k) with (fs k (S (k-1))) in * by (f_equal; lia).
 rewrite !iter_S. intros E1 E2 E3. rewrite E3 in *. simpl in *. lia.
Qed.

Lemma f_nonflat' k n : k<>0 -> f k (S n) = f k n -> f k (n-1) = f k n - 1.
Proof.
 intros K H.
 destruct n.
 - now rewrite f_k_0, f_k_1 in *.
 - fixpred. destruct (f_step k n) as [H'|H'].
   + apply f_nonflat in H'; auto. simpl in *. lia.
   + lia.
Qed.

Lemma f_SS k n : k<>0 -> f k n < f k (S (S n)).
Proof.
 intros K. destruct (f_step k n) as [E|E].
 - generalize (f_nonflat _ K E). simpl in *. lia.
 - apply Nat.lt_le_trans with (f k (S n)). lia. auto using f_mono_S.
Qed.

Lemma f_double_le k n : k<>0 -> n <= f k (2*n).
Proof.
intros K. induction n.
- trivial.
- replace (2* S n) with (S (S (2*n))) by lia.
  transitivity (S (f k (2*n))). lia. now apply f_SS.
Qed.

Lemma f_div2_le k n : k<>0 -> n/2 <= f k n.
Proof.
 intros K.
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

Lemma f_init k n : 2 <= n <= k+2 -> f k n = n-1.
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

(** * Antecedents by [f k]

    Study of the reverse problem [f k n = a] for some [a]. *)

Lemma f_max_two_antecedents k n m :
  k<>0 -> f k n = f k m -> n<m -> m = S n.
Proof.
 intros K H H'.
 destruct (le_lt_dec (2+n) m) as [LE|LT]; try lia.
 apply (f_mono k) in LE.
 rewrite (f_nonflat n K) in LE. lia.
 apply Nat.le_antisymm.
 - rewrite H. now apply f_mono.
 - apply f_mono_S.
Qed.

(** Another formulation of the same fact *)

Lemma f_inv k n m :
  k<>0 -> f k n = f k m -> (n = m \/ n = S m \/ m = S n).
Proof.
 intros.
 destruct (lt_eq_lt_dec n m) as [[LT|EQ]|LT]; auto.
 - generalize (@f_max_two_antecedents k n m); auto.
 - generalize (@f_max_two_antecedents k m n); auto.
Qed.

(** [f] is an onto map as soon as [k<>0] *)

Lemma f_onto k a : k<>0 -> exists n, f k n = a.
Proof.
intros K.
induction a.
- exists 0; trivial.
- destruct IHa as (n,Ha).
  destruct (f_step k n); [ | exists (S n); lia].
  destruct (f_step k (S n)); [ | exists (S (S n)); lia].
  exfalso.
  generalize (@f_max_two_antecedents k n (S (S n))). lia.
Qed.

(** We even have an explicit expression of one antecedent *)

Definition rchild k n := n + fs k (k-1) n.
Definition lchild k n := n + fs k (k-1) n - 1. (** left son, if there's one *)

Lemma f_onto_eqn k a : k<>0 -> f k (rchild k a) = a.
Proof.
 intros K.
 destruct (f_onto a K) as (n,Hn).
 unfold rchild. rewrite <- Hn, <- iter_S.
 assert (E := f_eqn k n). fixpred.
 destruct (f_step k n) as [<-|H]; f_equal; lia.
Qed.

Lemma rightmost_child_carac k a n : k<>0 -> f k n = a ->
 (f k (S n) = S a <-> n = rchild k a).
Proof.
 intros K Hn.
 assert (H' := f_eqn k n).
 replace (fs k k n) with (fs k (S (k-1)) n) in H' by (f_equal; lia).
 rewrite iter_S in H'.
 rewrite Hn in H'.
 unfold rchild; lia.
Qed.

Lemma f_children k a n : k<>0 -> f k n = a ->
  n = rchild k a \/ n = lchild k a.
Proof.
intros K Hn.
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
 k<>0 -> f k (lchild k a) = a - 1 \/ f k (lchild k a) = a.
Proof.
 intros K.
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

Lemma fs_A k n p : k<>0 -> fs k p (A k n) = A k (n-p).
Proof.
intros K. revert p.
induction n; intros.
- simpl. apply fs_k_1.
- destruct p; auto.
  rewrite iter_S; simpl. rewrite <- (IHn p). f_equal.
  rewrite <- (IHn (k-1)). now apply f_onto_eqn.
Qed.

Lemma f_A k n : k<>0 -> f k (A k n) = A k (n-1).
Proof.
 intros. now apply (@fs_A k n 1).
Qed.

Lemma f_SA k n : k<>0 -> n<>0 -> f k (S (A k n)) = S (A k (n-1)).
Proof.
 intros.
 rewrite <- (@f_A k n) by easy.
 apply rightmost_child_carac; trivial.
 unfold rchild.
 rewrite f_A, fs_A by easy.
 replace (n-1-(k-1)) with (n-k) by lia.
 now apply A_sum.
Qed.

(** More generally, [f] is shifting down Zeckendorf decompositions *)

Definition fbis k n := sumA k (map pred (decomp k n)).

Lemma fbis_decomp k n :
  k<>0 -> decomp k (fbis k n) = renorm k (map pred (decomp k n)).
Proof.
 intros K.
 apply decomp_carac; trivial.
 - apply renorm_delta; trivial.
   apply Delta_map with k.
   intros; lia. apply decomp_delta.
 - now rewrite renorm_sum.
Qed.

Lemma fsbis k p n : k<>0 -> p <= k ->
 (fbis k^^p) n = sumA k (map (decr p) (decomp k n)).
Proof.
 intros Hp.
 revert n.
 induction p; intros.
 - simpl. now rewrite map_decr_0, decomp_sum.
 - now rewrite iter_S, IHp, fbis_decomp, renorm_mapdecr, map_decr_S by lia.
Qed.

Lemma fbis_is_f k n : k<>0 -> fbis k n = f k n.
Proof.
 intros K. apply f_unique.
 - reflexivity.
 - clear n. intros n.
   rewrite fsbis; auto.
   assert (Hn := decomp_sum k n).
   assert (D := decomp_delta k n).
   remember (decomp k n) as l eqn:Hl.
   destruct l as [|a l].
   + simpl in *. now subst.
   + unfold fbis. rewrite decomp_S, <- Hl by trivial. simpl.
     case Nat.ltb_spec; intros.
     * rewrite <- map_decr_1.
       rewrite renormS_alt, renorm_mapdecr'; simpl; auto with arith.
       2:{ apply Delta_S_cons. now fixpred. }
       2:{ destruct (k-1); lia. }
       rewrite Nat.add_shuffle1.
       assert (~In 0 l).
       { apply (@Delta_nz' k a); auto with arith. lia. }
       rewrite <- sumA_eqn_pred; auto.
       rewrite decr_0.
       unfold decr. replace (a-k) with 0; simpl in *; lia.
     * rewrite map_cons, sumA_cons.
       rewrite <- Nat.add_assoc.
       rewrite <- map_decr_1.
       rewrite <- sumA_eqn_pred; auto.
       eapply Delta_nz; eauto. lia.
Qed.

Lemma f_decomp k n : k<>0 -> f k n = sumA k (map pred (decomp k n)).
Proof.
 intros. symmetry. now apply fbis_is_f.
Qed.

Lemma decomp_f k n :
  k<>0 -> decomp k (f k n) = renorm k (map pred (decomp k n)).
Proof.
 intros. now rewrite <- fbis_is_f, fbis_decomp.
Qed.

Lemma fs_decomp k p n :
  k<>0 -> p <= k -> fs k p n = sumA k (map (decr p) (decomp k n)).
Proof.
 intros K H. rewrite <- fsbis; auto. clear H.
 induction p; simpl; now rewrite ?IHp, <- ?fbis_is_f.
Qed.

Lemma f_sumA k l : k<>0 -> Delta k l ->
 f k (sumA k l) = sumA k (map pred l).
Proof.
 intros. rewrite f_decomp; trivial. f_equal. f_equal. autoh.
Qed.

Lemma fs_sumA k p l : k<>0 -> p <= k -> Delta k l ->
 fs k p (sumA k l) = sumA k (map (decr p) l).
Proof.
 intros. rewrite fs_decomp; auto. f_equal. f_equal. autoh.
Qed.

Lemma f_sumA_lax k l : 1<k -> Delta (k-1) l ->
 f k (sumA k l) = sumA k (map pred l).
Proof.
 intros. rewrite <- renorm_sum.
 rewrite f_sumA; try lia.
 - rewrite <- !map_decr_1, renorm_mapdecr; auto.
 - apply renorm_delta; trivial; lia.
Qed.

Lemma fs_sumA_lax k p l : p < k -> Delta (k-1) l ->
 fs k p (sumA k l) = sumA k (map (decr p) l).
Proof.
 intros. rewrite <- renorm_sum.
 rewrite fs_sumA; try lia.
 - apply renorm_mapdecr; lia.
 - apply renorm_delta; trivial; lia.
Qed.

(** Extending theorem [fs_decomp] to larger iterates than [p <= k] *)

Definition succrank k n :=
  match rank k n with
  | None => 0
  | Some r => S r
  end.

Lemma f_succrank k n : k<>0 -> succrank k n <= S (succrank k (f k n)).
Proof.
 intros K. unfold succrank, rank. rewrite decomp_f by easy.
 assert (H := @renorm_head k (map pred (decomp k n)) K).
 destruct decomp as [|r l], renorm as [|r' l']; simpl in *; try lia.
 destruct H as (m, H). lia.
Qed.

Lemma fs_decomp_gen k p n : k<>0 -> n = 0 \/ p < k + succrank k n ->
 fs k p n = sumA k (map (decr p) (decomp k n)).
Proof.
 intros K [->|H].
 - simpl. induction p; simpl; now rewrite ?IHp.
 - revert n H.
   induction p; intros.
   + simpl. now rewrite map_decr_0, decomp_sum.
   + rewrite iter_S, IHp; clear IHp.
     2:{ generalize (@f_succrank k n); lia. }
     rewrite decomp_f by easy.
     unfold succrank, rank in H.
     assert (D := decomp_delta k n).
     destruct decomp as [|r l]; trivial.
     destruct (Nat.eq_dec r 0) as [->|R].
     * rewrite renorm_mapdecr by lia.
       f_equal. symmetry. apply map_decr_S.
     * rewrite renorm_nop; trivial.
       { f_equal. symmetry. apply map_decr_S. }
       { apply Delta_pred; trivial.
         eapply Delta_nz; eauto with hof. lia. }
Qed.

(** Zone where [f k n = n-1].
    Note that [f k n] cannot be [n] or more except when [n<=1], see [f_lt].
    The conditions below are optimal, see [f_subid_inv] later. *)

Lemma f_subid k n : n<>1 -> n <= k+2 -> f k n = n-1.
Proof.
 intros Hn Hn'.
 destruct (Nat.eq_dec n 0).
 - subst. now rewrite f_k_0.
 - apply f_init; lia.
Qed.

(** Some particular cases : early diagonals *)

Lemma f_k_km1 k : k<>2 -> f k (k-1) = k-2.
Proof.
 intros. rewrite f_subid; lia.
Qed.

Lemma f_k_k k : k<>1 -> f k k = k-1.
Proof.
 intros. rewrite f_subid; lia.
Qed.

Lemma f_k_Sk k : k<>0 -> f k (S k) = k.
Proof.
 intros. rewrite f_subid; lia.
Qed.

Lemma f_k_plus_2 k : f k (2+k) = 1+k.
Proof.
 rewrite f_subid; lia.
Qed.

Lemma f_k_plus_3 k : k<>0 -> f k (3+k) = 1+k.
Proof.
 intros K. replace (3+k) with (sumA k [S k]).
 2:{ cbn -[A]. rewrite A_S.
     replace (k - _) with 1 by lia.
     rewrite !A_base; lia. }
 rewrite f_sumA; autoh. cbn -[A]. rewrite A_base; lia.
Qed.

Lemma f_k_plus_4 k : k<>0 -> f k (4+k) = 2+k.
Proof.
 intros K. replace (4+k) with (sumA k [0;S k]).
 2:{ cbn -[A]. rewrite A_S.
     replace (k - _) with 1 by lia.
     rewrite !A_base; lia. }
 rewrite f_sumA; autoh. cbn -[A]. rewrite !A_base; lia.
Qed.

Lemma f_k_plus_5 k : k<>0 -> f k (5+k) = 2+k.
Proof.
 intros K. replace (5+k) with (sumA k [1;S k]).
 2:{ cbn -[A]. rewrite (A_S k k).
     replace (k - _) with 1 by lia.
     rewrite !A_base; lia. }
 rewrite f_sumA; autoh. cbn -[A]. rewrite !A_base; lia.
Qed.

Lemma f_k_plus_6 k : k<>0 -> f k (6+k) = 3+k.
Proof.
 intros K. destruct (Nat.eq_dec k 1) as [->|Hq]. now compute.
 replace (6+k) with (sumA k [2;S k]).
 2:{ cbn -[A]. rewrite (A_S k k).
     replace (k - _) with 1 by lia.
     rewrite !A_base; lia. }
 rewrite f_sumA_lax; autoh. cbn -[A]. rewrite !A_base; lia.
 apply Delta_S_cons. fixpred. constructor. lia. constructor.
Qed.

Lemma f_subid_inv k n : f k n = n-1 -> n <> 1 /\ n <= k+2.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - rewrite f_0. lia.
 - intros E. split.
   + intros ->. rewrite f_k_1 in E. discriminate.
   + rewrite Nat.le_ngt. intros LT.
     generalize (f_lipschitz k (3+k) n).
     rewrite f_k_plus_3, E; lia.
Qed.

(** Summarize some of the last results *)

Lemma f_k_plus_some k p : k<>0 -> 1 <= p <= 6 -> f k (k+p) = k + p/2.
Proof.
 intros K Hp. rewrite !(Nat.add_comm k).
 destruct (Nat.eq_dec p 1) as [->|N1]. now apply f_k_Sk.
 destruct (Nat.eq_dec p 2) as [->|N2]. now apply f_k_plus_2.
 destruct (Nat.eq_dec p 3) as [->|N3]. now apply f_k_plus_3.
 destruct (Nat.eq_dec p 4) as [->|N4]. now apply f_k_plus_4.
 destruct (Nat.eq_dec p 5) as [->|N5]. now apply f_k_plus_5.
 destruct (Nat.eq_dec p 6) as [->|N6]. now apply f_k_plus_6.
 lia.
Qed.

Section Knonzero.
Variable k:nat.
Hypothesis K:k<>0.

(** Decomposition and positions in the F tree *)

Lemma rchild_decomp n :
 rchild k n = sumA k (map S (decomp k n)).
Proof.
 unfold rchild.
 rewrite fs_decomp by lia.
 rewrite <- (@decomp_sum k n) at 1.
 remember (decomp k n) as l.
 apply sumA_eqn.
Qed.

Lemma flat_rank_0 n :
 f k (S n) = f k n <-> rank k n = Some 0.
Proof.
 rewrite !f_decomp by trivial.
 unfold rank.
 rewrite decomp_S by trivial.
 destruct (decomp k n) as [|a l] eqn:E.
 - simpl; now split.
 - simpl.
   case Nat.ltb_spec; intros.
   + rewrite <- !map_decr_1.
     rewrite renormS_alt, renorm_mapdecr'; try lia.
     * simpl.
       rewrite decr_0.
       rewrite !A_base by (auto; lia).
       split. intros; f_equal; lia. intros [= ->]; lia.
     * apply Delta_S_cons. fixpred. rewrite <- E; autoh.
     * simpl. destruct (k-1); lia.
     * rewrite <- E. autoh.
   + simpl. split. intros; f_equal; lia. intros [= ->]; lia.
Qed.

Lemma step_rank_nz n :
 f k (S n) = S (f k n) <-> rank k n <> Some 0.
Proof.
 rewrite <- flat_rank_0; trivial.
 generalize (f_step k n). lia.
Qed.

Lemma steps_ranks_nz n p :
 f k (n+p) = f k n + p <-> (forall a, a<p -> rank k (n+a) <> Some 0).
Proof.
 induction p.
 - rewrite !Nat.add_0_r. intuition lia.
 - rewrite !Nat.add_succ_r.
   split.
   + intros E a Hq.
     assert (LE := f_le_add k p n). rewrite (Nat.add_comm p n) in LE.
     assert (LE' := f_le_add k 1 (n+p)). simpl in LE'.
     inversion Hq.
     * subst a. apply step_rank_nz. lia.
     * apply IHp; try lia.
   + intro H.
     assert (R : rank k (n+p) <> Some 0) by (apply H; lia).
     apply step_rank_nz in R. rewrite R. f_equal.
     apply IHp. intros a Ha. apply H. lia.
Qed.

(** At most [k] consecutive [+1] steps *)

Lemma f_maxsteps n :
 f k (n+k+1) <= f k n + k.
Proof.
 destruct (@rank_later_is_zero k n K) as (p & LE & H).
 apply flat_rank_0 in H.
 transitivity (f k (S (p + n)) + (k+1-S p)).
 - generalize (f_lipschitz k (S (p+n)) (n+k+1)). lia.
 - rewrite H.
   generalize (f_lipschitz k n (p+n)). lia.
Qed.

(** A first example of such [k] consecutive [+1] steps : [n=2] *)

Lemma f_maxsteps_example2 : f k (2+k) = f k 2 + k.
Proof.
 rewrite f_k_2. simpl. apply f_k_plus_2.
Qed.

(** More generally, [k] consecutive [+1] steps for numbers [2+n]
    when [n=0] or [rank k n >= 2k-1]. *)

Lemma f_maxsteps_examples n :
  (forall r, rank k n = Some r -> 2*k-1 <= r) ->
  f k ((2+n) + k) = f k (2+n) + k.
Proof.
 intros Hr.
 destruct (rank k n) as [r|] eqn:Hn.
 2:{ rewrite rank_none in Hn; subst n. apply f_maxsteps_example2. }
 specialize (Hr r eq_refl).
 apply steps_ranks_nz.
 intros a Ha. replace (2+n+a) with (S (S a) + n) by lia.
 rewrite <- (@A_base k (S a)) by lia.
 rewrite <- (decomp_sum k n).
 change (_+_) with (sumA k (S a::decomp k n)).
 unfold rank in *. rewrite <- renorm_sum, decomp_sum'; trivial.
 - generalize (@renorm_head k (S a::decomp k n) K). unfold HeadStep.
   destruct renorm as [|u l]; try easy. intros (b & ->) [= E].
 - apply renorm_delta; trivial. assert (D := decomp_delta k n).
   destruct decomp as [|u l]; try easy.
   apply Delta_S_cons. fixpred.
   injection Hn as ->. constructor; autoh.
Qed.

(* No other situations with [k] consecutive [+1] steps,
   except [f 0 1 = 1 + f 0 0]. *)

Lemma f_maxsteps_carac_aux n r :
  rank k n = Some r -> k <= r < 2*k-1 ->
  exists r', rank k (n+2+(r-k)) = Some r' /\ r < r'.
Proof.
 intros Hn Hr.
 assert (E : forall a, a <= r-k -> decomp k (n + S a) = a :: decomp k n).
 { intros a Ha. rewrite <- (@A_base k a) by lia.
   unfold rank in *. rewrite <- (decomp_sum k n) at 1.
   rewrite Nat.add_comm.
   change (_+_) with (sumA k (a::decomp k n)).
   apply decomp_sum'; trivial.
   assert (D := decomp_delta k n).
   destruct decomp as [|u l]; try easy.
   injection Hn as ->. constructor; auto. lia. }
 specialize (E (r-k) lia).
 rewrite Nat.add_succ_r, <- Nat.add_succ_l in E.
 unfold rank in *.
 destruct (decomp k n) as [|r' l] eqn:E'; try easy. injection Hn as ->.
 assert (E2 : decomp k (n+2 + (r-k)) = renormS k r l).
 { rewrite !Nat.add_succ_r, Nat.add_0_r, Nat.add_succ_l.
   rewrite decomp_S, E; trivial. simpl.
   case Nat.ltb_spec; try lia. intros _.
   case Nat.eqb_spec; trivial; lia. }
 rewrite E2.
 assert (H := renormS_head k r l).
 red in H. destruct renormS; try easy.
 destruct H as (a & ->). exists (S r + a*k). split; auto. lia.
Qed.

Lemma f_maxsteps_carac n :
  f k (n + k) = f k n + k <->
  (k=1 /\ n=0) \/ (2<=n /\ forall r, rank k (n-2) = Some r -> 2*k-1 <= r).
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
     apply Nat.le_ngt. intros LT'.
     destruct (Nat.le_gt_cases r (k-1)) as [LE'|GT].
     * destruct (@rank_later_is_zero k (n-1) K) as (a & Ha & R).
       destruct (Nat.eq_dec a 0).
       { subst a. simpl in *.
         apply rank_next_high in Hr; auto. destruct Hr as (m & Hr).
         replace (S (n-2)) with (n-1) in Hr by lia.
         rewrite Hr in R. now injection R. lia. }
       { apply (E (a-1)). lia.
         rewrite <- R. f_equal. lia. }
     * destruct (@f_maxsteps_carac_aux (n-2) r Hr) as (a & Ha & Hq'); try lia.
       replace (n-2+2) with n in Ha by lia.
       apply (E (r-(k-1))). lia.
       replace (n+(r-(k-1))) with (S (n+(r-k))) by lia.
       eapply rank_next_0; eauto. lia.
 - intros [(->,->) | (LE & H)].
   + reflexivity.
   + replace n with (2+(n-2)) by lia. apply f_maxsteps_examples; auto.
Qed.

(** Other characterization of max [+1] steps :
    the last term in the [+1] sequence is decomposed as [0;a*k;...]
    where [a<>0]. *)

Lemma f_steps_sub n p :
 rank k n = Some (S p) -> p < k -> f k (n - p) = f k n - p.
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

Lemma f_maxsteps_examples_alt n a :
 rank k n = Some ((S a)*k) ->
 f k ((n+1) - k) = f k (n+1) - k.
Proof.
 intros R.
 destruct (step_rank_nz n) as (_,R').
 destruct (Nat.eq_dec k 1) as [->|Hq].
 - rewrite Nat.mul_1_r in R.
   replace (n+1-1) with n by lia.
   rewrite Nat.add_1_r. rewrite R'. lia. now rewrite R.
 - assert (R2 : rank k n <> Some 0). { rewrite R. intros [= E]. lia. }
   specialize (R' R2).
   destruct (Nat.eq_dec n 0) as [->|Hn].
   + rewrite f_k_1. simpl. now destruct k.
   + assert (Rm : rank k (n-1) = Some (k-1)).
     { apply rank_pred in R. 2,3:(simpl; lia).
       replace (S a * k - 1) with (k-1 + a * k) in R by lia.
       rewrite Nat.mod_add in R; auto.
       rewrite Nat.mod_small in R; auto; lia. }
     replace (n+1 - k) with (n-1-(k-2)) by lia.
     rewrite f_steps_sub; try lia.
     2:rewrite Rm; f_equal; lia.
     assert (Rm' : rank k (n-1) <> Some 0). { rewrite Rm. intros [= E]. lia. }
     rewrite <- step_rank_nz in Rm'.
     rewrite Nat.add_1_r. fixpred. lia.
Qed.

(** More about [fs k p], in particular when is it flat or not *)

Lemma fs_S_decomp p n : p < succrank k n ->
 fs k p (S n) = sumA k (map (decr p) (decomp k (S n))).
Proof.
 unfold succrank, rank. rewrite decomp_S; trivial.
 destruct (decomp k n) as [|r l] eqn:E; simpl.
 - inversion 1.
 - intros Hp. case Nat.ltb_spec; intros.
   + rewrite fs_decomp by lia. rewrite decomp_S, E; trivial. simpl.
     apply Nat.ltb_lt in H. now rewrite H.
   + revert p Hp.
     assert (D1 : forall m, m + k <= r ->
                  Delta k (map (decr m) (0 :: r :: l))).
     { intros m Hm. simpl. constructor. unfold decr; lia.
       apply (@Delta_map_decr _ _ (r::l)).
       - intros x IN. assert (D := decomp_delta k n).
         rewrite E in D. simpl in IN. destruct IN as [<-|IN]; try lia.
         apply Delta_le with (y:=x) in D; trivial. lia.
       - rewrite <- E. apply decomp_delta. }
     assert (E1 : forall m, m + k <= r ->
                  fs k m (S n) = sumA k (map (decr m) (0::r::l))).
     { induction m.
       - rewrite map_decr_0. intros. simpl Nat.iter.
         rewrite <- (decomp_sum k (S n)), decomp_S, E; trivial. f_equal.
         simpl. case Nat.ltb_spec; trivial; lia.
       - simpl Nat.iter. intros Hm. rewrite IHm by lia. clear IHm.
         rewrite f_decomp; trivial. rewrite decomp_sum'; trivial.
         + now rewrite map_decr_S'.
         + apply D1; lia. }
     assert (E2 : forall m, m + k <= r ->
                  decomp k (fs k m (S n)) = map (decr m) (0::r::l)).
     { intros m Hm. rewrite E1 by trivial. apply decomp_sum'; auto. }
     clear D1 E1.
     assert (E3 : decomp k (fs k (r-(k-1)) (S n)) =
                  renorm k (k :: map (decr (r-(k-1))) l)).
     { replace (r-(k-1)) with (S (r-k)) by lia. simpl Nat.iter.
       rewrite decomp_f, E2 by lia. rewrite <- map_decr_S'.
       simpl. unfold decr at 1. replace (r-_) with (k-1) by lia.
       replace (S (r-_)) with (r-(k-1)) by lia. apply renorm_low; trivial.
       replace (k-1) with (r-(r-(k-1))) at 1 by lia.
       apply (@Delta_map_decr _ _ (r::l)).
       - intros x IN. assert (D := decomp_delta k n). rewrite E in D.
         simpl in IN. destruct IN as [<-|IN]; try lia.
         apply Delta_le with (y:=x) in D; trivial. lia.
       - rewrite <- E. apply decomp_delta. }
     intros p Hp.
     destruct (Nat.le_gt_cases p (r-k)) as [LE|LT].
     * rewrite <- E2 by lia. now rewrite decomp_sum.
     * replace p with ((p+(k-1)-r)+(r-(k-1))) by lia.
       rewrite iter_add. rewrite fs_decomp by lia.
       rewrite E3.
       set (p' := p+(k-1)-r).
       rewrite renorm_mapdecr'; try (simpl; lia).
       { replace k with (decr (r-(k-1)) (S r)) at 2 by (unfold decr; lia).
         rewrite (map_decr_decr _ (r-(k-1)) (S r::l)).
         replace (p'+_) with p by lia; cbn -[decr sumA].
         replace (decr p (S r)) with (S (r-p)) by (unfold decr; lia).
         simpl. unfold decr at 2. replace (r-p-(k-1)) with 0; simpl; lia. }
       { replace k with (S (k-1)) at 2 by lia. apply Delta_S_cons. fixpred.
         replace (k-1) with (decr (r-(k-1)) r) at 1 by (unfold decr; lia).
         apply (@Delta_map_decr _ _ (r::l)).
         - intros x IN. assert (D := decomp_delta k n). rewrite E in D.
           simpl in IN. destruct IN as [<-|IN]; try lia.
           apply Delta_le with (y:=x) in D; trivial. lia.
         - rewrite <- E. apply decomp_delta. }
Qed.

Lemma fs_nonflat p n : p < succrank k n -> fs k p (S n) <> fs k p n.
Proof.
 intros Hp.
 rewrite (@fs_decomp_gen k p n) by lia.
 rewrite fs_S_decomp by auto.
 rewrite decomp_S; trivial.
 unfold succrank, rank in Hp.
 destruct decomp as [|r l] eqn:E; simpl;
   try case Nat.ltb_spec; intros; simpl; try lia.
 rewrite renormS_alt by (trivial; rewrite <- E; autoh).
 rewrite renorm_mapdecr'; trivial.
 - rewrite map_cons, sumA_cons.
   unfold decr at 1 3. rewrite !A_base; auto; lia.
 - apply Delta_S_cons. fixpred. rewrite <- E. apply decomp_delta.
 - simpl. lia.
Qed.

Lemma fs_first_flat p n :
  n<>0 -> p = succrank k n -> fs k p (S n) = fs k p n.
Proof.
 intros N P.
 rewrite <- (rank_none k) in N.
 unfold succrank, rank in *.
 destruct (decomp k n) as [|r l] eqn:E; try easy. clear N. subst.
 assert (D := decomp_delta k n). rewrite E in D.
 destruct (Nat.le_gt_cases r (k-1)) as [LE|LT].
 - rewrite !fs_decomp by lia.
   rewrite decomp_S, E; trivial. simpl. case Nat.ltb_spec; try lia. intros _.
   rewrite renormS_alt by trivial.
   rewrite renorm_mapdecr'; auto with hof; try (unfold LeHd; lia).
   + simpl. unfold decr at 1 3. f_equal. f_equal. lia.
   + apply Delta_S_cons. now fixpred.
 - rewrite (@fs_decomp_gen k (S r) n); trivial;
    unfold succrank, rank; rewrite E; try lia.
   simpl map. unfold decr at 1. replace (r - S r) with 0 by lia.
   simpl Nat.iter. rewrite fs_S_decomp;
    unfold succrank, rank; rewrite ?decomp_S, ?E; try lia.
   simpl next_decomp. case Nat.ltb_spec; try lia. intros _.
   simpl map. unfold decr at 1. rewrite Nat.sub_diag. simpl.
   change (S (S _)) with (sumA k (1::map (decr r) l)).
   assert (D' : Delta k (0 :: map (decr r) l)).
   { rewrite <- (Nat.sub_diag r). apply (@Delta_map_decr _ _ (r::l)); auto.
     intros x [->|IN]; trivial. eapply Delta_le in D; eauto. lia. }
   rewrite <- renormS_sum, renormS_alt by auto.
   rewrite f_sumA; trivial.
   2:{ apply renorm_delta; trivial. apply Delta_S_cons. now fixpred. }
   rewrite <- map_decr_1.
   rewrite renorm_mapdecr'; auto with hof; try (unfold LeHd; lia).
   + simpl. now rewrite map_decr_decr.
   + apply Delta_S_cons. now fixpred.
Qed.

Lemma fs_stays_flat p p' n :
  fs k p (S n) = fs k p n -> p <= p' -> fs k p' (S n) = fs k p' n.
Proof.
 intros Hp. induction 1; trivial. simpl Nat.iter. now rewrite IHle.
Qed.

Lemma fs_flat_iff p n :
  fs k p (S n) = fs k p n <-> n<>0 /\ succrank k n <= p.
Proof.
 split.
 - intros H. split.
   + contradict H. subst. rewrite fs_k_1, fs_k_0. lia.
   + apply Nat.le_ngt. contradict H. now apply fs_nonflat.
 - intros (N,Hp). apply fs_stays_flat with (succrank k n); trivial.
   now apply fs_first_flat.
Qed.

Lemma fs_nonflat_iff p n :
  fs k p (S n) = S (fs k p n) <-> n=0 \/ p < succrank k n.
Proof.
 assert (LE := fs_lipschitz k p n (S n)).
 replace (S n - n) with 1 in LE by lia.
 generalize (@fs_mono k p n (S n)) (fs_flat_iff p n). lia.
Qed.

Lemma fs_flat_iff' p n :
  fs k p (S n) = fs k p n <->
  match rank k n with
  | None => False
  | Some r => r < p
  end.
Proof.
 rewrite fs_flat_iff. unfold succrank.
 rewrite <- (rank_none k).
 destruct rank; simpl; intuition; easy || lia.
Qed.

Lemma fs_nonflat_iff' p n :
  fs k p (S n) = S (fs k p n) <->
  match rank k n with
  | None => True
  | Some r => p <= r
  end.
Proof.
 rewrite fs_nonflat_iff. unfold succrank.
 rewrite <- (rank_none k).
 destruct rank; simpl; intuition; easy || lia.
Qed.

(** [fs k p] cannot have more than [p+1] consecutive flats *)

Lemma fs_maxflat n p : p <= k ->
 fs k p n < fs k p (n+p+1).
Proof.
 intros Hp.
 destruct (rank k n) as [r|] eqn:Hr.
 - destruct (@rank_later_is_high k n r p K Hp Hr) as (r' & a & H1 & H2 & H3).
   assert (E : fs k p (S (a+n)) = S (fs k p (a+n))).
   { apply fs_nonflat_iff; auto. right. unfold succrank. rewrite H2. lia. }
   unfold lt.
   transitivity (S (fs k p (a+n))).
   + apply -> Nat.succ_le_mono. apply fs_mono. lia.
   + rewrite <- E. apply fs_mono. lia.
 - rewrite rank_none in *. subst.
   rewrite fs_k_0. apply fs_nonzero. lia.
Qed.

End Knonzero.

(** Study of the "triangular" zone of f, coming after the "n-1" zone
    seen in [f_subid]. Here [n <= triangle(k+3)-3 = A k (2*k+1) - 1].

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
   replace ((q+1)*(q+2)) with (S q * (S q + 1)) in LT by lia.
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

(* The number [triangle(k+3)-3] (which is also [A k (2*k+1) -1]) is
   the lowest number with three terms in its k-decomp. Let's call it
   [quad k]. *)

Definition quad k := triangle (k+3)-3.

Lemma quad_S k : quad (S k) = quad k + (k+4).
Proof.
 unfold quad. replace (S k + 3) with (S (k+3)) by lia.
 rewrite triangle_succ. generalize (triangle_aboveid (k+3)). lia.
Qed.

Lemma quad_min k : 3 <= quad k.
Proof.
 induction k. easy. rewrite quad_S. lia.
Qed.

Lemma quad_alt k : k<>0 -> quad k = A k (2*k+1) - 1.
Proof.
 intros. unfold quad. rewrite A_2k1_tri; lia.
Qed.

Lemma quad_other_eqn k : quad k = (k+1)*(k+6)/2.
Proof.
 apply Nat.div_unique with 0; try lia. unfold quad.
 generalize (triangle_aboveid k) (double_triangle (k+3)). lia.
Qed.

Lemma quad_decomp k : k<>0 -> decomp k (quad k) = [0;k;2*k].
Proof.
 intros K. apply decomp_carac; trivial; [ repeat constructor; lia | ].
 rewrite quad_alt, A_2k1_eqn; trivial. simpl; lia.
Qed.

Lemma decomp_len_lt_3 k n : k<>0 -> n < quad k -> length (decomp k n) < 3.
Proof.
 intros K LT.
 assert (E := decomp_sum k n).
 assert (D := decomp_delta k n).
 destruct (decomp k n) as [|a [|b [|c l]]]; simpl; try lia.
 exfalso.
 rewrite 2 Delta_alt in D. destruct D as ((_,D1),D2).
 specialize (D2 b (or_introl eq_refl)).
 specialize (D1 c (or_introl eq_refl)).
 assert (A k k <= A k b) by (apply A_mono; lia).
 assert (A k (2*k) <= A k c) by (apply A_mono; lia).
 simpl in E. rewrite quad_alt, A_2k1_eqn in LT; trivial.
 generalize (A_nz k a). lia.
Qed.

(* The numbers below [quad q] also have rank 0 only when
   they are 1 or a successor of a [A] number. That's the key for describing
   the "triangular" zone of f. Graphical interpretation : the bottom
   of the tree, where binary nodes are on the left edge. *)

Lemma low_rank0 k n :
  k<>0 -> 1 < n < quad k -> rank k n = Some 0 ->
  exists p, p < 2*k+1 /\ n = S (A k p).
Proof.
 unfold rank.
 intros K (Hn,Hn') Hr.
 assert (L := decomp_len_lt_3 K Hn').
 assert (E := decomp_sum k n).
 assert (D := decomp_delta k n).
 destruct (decomp k n) as [|a [|b [|c l]]]; simpl in L;
  try easy; injection Hr as ->; simpl in E; try lia.
 exists b. split; try lia.
 apply A_lt_inv with k. rewrite quad_alt in *; trivial. lia.
Qed.

Lemma A_plus2 k n : k<>0 -> n <= k+1 -> A k n <= n+2.
Proof.
 intros K. rewrite Nat.lt_eq_cases. intros [LT | ->].
 - rewrite A_base; lia.
 - rewrite Nat.add_succ_r, A_S, A_base; try lia.
   replace (k+0-(k-1)) with 1 by lia. now rewrite A_k_1.
Qed.

Lemma f_triangle k n :
  k<>0 -> n<>1 -> n <= quad k -> f k n = n-1 - steps (n-k-2).
Proof.
 induction n.
 - reflexivity.
 - intros K NE LE.
   destruct (Nat.leb_spec (S n) (k+2)).
   + rewrite f_subid; auto.
     replace (S n - k - 2) with 0 by lia. simpl. lia.
   + destruct (f_step k n) as [E|E].
     * rewrite E.
       rewrite flat_rank_0 in E; trivial.
       destruct (@low_rank0 k n) as (p & Hp & Hp'); auto; try lia.
       assert (k-1 < p).
       { apply A_lt_inv with k. rewrite A_base; lia. }
       rewrite IHn; try lia.
       assert (steps (S n - k - 2) = S (steps (n - k - 2))); try lia.
       { replace p with (k-1+(p-(k-1))) in Hp' by lia.
         rewrite A_triangle in Hp'; try lia.
         rewrite Hp'.
         replace (_ - k - 2) with (triangle (p-(k-1))) by lia.
         rewrite steps_triangle.
         replace (_ - k - 2) with (triangle (p-(k-1)) - 1) by lia.
         rewrite steps_triangle_minus; lia. }
     * rewrite E.
       rewrite step_rank_nz in E; trivial.
       rewrite IHn; clear IHn; try lia.
       assert (LE' := steps_le_id (n-k-2)).
       assert (steps (S n - k - 2) = steps (n - k - 2)); try lia.
       { clear LE'.
         destruct (@A_inv' k n) as (p,Hp); try lia.
         assert (k-1 < p).
         { rewrite Nat.succ_lt_mono.
           apply A_lt_inv with k. rewrite A_base; lia. }
         assert (p < 2*k+1).
         { apply A_lt_inv with k. rewrite quad_alt in *; trivial; lia. }
         assert (LE' : p - (k-1) <= k + 1) by lia.
         assert (T := A_triangle K LE').
         replace (k-1+(p-(k-1))) with p in T by lia.
         assert (n <> S (A k p)).
         { intro E'. apply E.
           unfold rank. replace (decomp k n) with [0;p]; auto.
           symmetry. apply decomp_carac; simpl; try lia.
           constructor; autoh. }
         destruct (Nat.eq_dec (A k p) n) as [E'|NE'].
         - clear Hp.
           assert (k < p).
           { apply A_lt_inv with k. rewrite A_base; lia. }
           rewrite E' in T. rewrite T.
           replace (_ - k - 2) with (triangle (p-(k-1)) - 1) by lia.
           replace (_ - k - 2) with (triangle (p-(k-1)) - 2) by lia.
           rewrite !steps_triangle_minus; lia.
         - rewrite A_S in Hp.
           set (t := triangle (p-(k-1))) in *. apply A_plus2 in LE'; trivial.
           replace (n-k-2) with (t + (n-k-2-t)) by lia.
           replace (S n-k-2) with (t + (S n-k-2-t)) by lia.
           unfold t at 1 3. rewrite !steps_altspec; lia. }
Qed.

(* We hence have [f k n <= f (S k) n] when n is in
   this triangular zone. *)

Lemma f_triangle_diag_incr k n :
  k<>0 -> n<>1 -> n <= quad k -> f (S k) (S n) = S (f k n).
Proof.
 intros K Hn LE.
 destruct (Nat.eq_dec n 0).
 - subst. now rewrite f_k_0, f_k_1.
 - rewrite !f_triangle; try lia. simpl.
   generalize (steps_le_id (n-k-2)). lia.
   rewrite quad_S; lia.
Qed.

Lemma f_triangle_incrk k n : n <= quad k -> f k n <= f (S k) n.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K].
 - intros _. rewrite f_0, f_1_div2. destruct n. lia.
   simpl min. change 1 with (2/2). apply Nat.div_le_mono; lia.
 - destruct (Nat.eq_dec n 1) as [->|NE].
   + intros _. now rewrite !f_k_1.
   + intros LE.
     destruct (f_step (S k) n) as [E|E].
     * rewrite <- E. rewrite f_triangle_diag_incr; auto.
     * rewrite f_triangle_diag_incr in E; lia.
Qed.

Lemma f_last_triangle_1 k n : k<>0 -> n = quad k -> f k n = n - k - 2.
Proof.
 intros K EQ.
 destruct (Nat.eq_dec n 1) as [->|NE].
 - exfalso. generalize (quad_min k). lia.
 - rewrite f_triangle by lia.
   rewrite EQ at 2. unfold quad.
   rewrite Nat.add_succ_r, triangle_succ.
   replace (triangle _ + _ - _ - _ - _)
     with (triangle (k+2) - 2) by lia.
   rewrite steps_triangle_minus; lia.
Qed.

Lemma f_last_triangle_2 k n : k<>0 -> n = quad k -> f (S k) n = n - k - 2.
Proof.
 intros K EQ.
 destruct (Nat.eq_dec n 1) as [->|NE].
 - exfalso. generalize (quad_min k). lia.
 - rewrite f_triangle; try lia.
   2:{ simpl. rewrite quad_S. lia. }
   rewrite EQ at 2.
   unfold quad. rewrite Nat.add_succ_r, triangle_succ.
   replace (triangle _ + _ - _ - _ - _)
     with (triangle (k+2) - 3) by lia.
   rewrite steps_triangle_minus; lia.
Qed.

(* Experimentally, this border of the triangle zone [n = triangle(k+3)-3]
   seems to be the last point where [f k n = f (S k) n].
   Conjecture : [forall m, triangle(k+3)-3 < m -> f k m < f (S k) m].
   Proof: ?! (TODO) *)

Lemma fk_fSk_last_equality k n :
 k<>0 -> n = quad k -> f k n = f (S k) n.
Proof.
  intros K EQ. now rewrite f_last_triangle_1, f_last_triangle_2.
Qed.

Lemma fk_fSk_conjectures k : k<>0 ->
 (forall m, quad k < m -> f k m < f (S k) m) ->
 (forall n, n<>1 -> f k n < f (S k) (S n)).
Proof.
 intros K C1 n Hn.
 destruct (Nat.ltb_spec (quad k) n) as [LT|LE].
 - apply C1 in LT. eapply Nat.lt_le_trans; eauto. apply f_mono; lia.
 - rewrite f_triangle_diag_incr; auto.
Qed.

(* [quad q] also appears to be the last point of equality between
   [rchild (k+1)] and [rchild (k+2)]. *)

Lemma quad_decomp_Sk k : decomp (S k) (quad k) = [k; 2*k+1].
Proof.
 apply decomp_carac; [ easy | repeat constructor; lia | ].
 cbn - ["*" "/"].
 rewrite A_base by lia.
 replace (2*k+1) with ((S k)-1 + (k+1)) by lia. rewrite A_triangle by lia.
 unfold quad. replace (k+3) with (S (S (k+1))); rewrite ?triangle_succ; lia.
Qed.

Lemma quad_decomp_SSk k : k<>0 -> decomp (S (S k)) (quad k) = [k-1; 2*k+2].
Proof.
 intros K. apply decomp_carac; [ easy | repeat constructor; lia | ].
 cbn - ["*" "/"].
 rewrite A_base by lia.
 replace (2*k+2) with ((S (S k))-1 + (k+1)) by lia.
 rewrite A_triangle by lia.
 unfold quad. replace (k+3) with (S (S (k+1))); rewrite ?triangle_succ; lia.
Qed.

Lemma rchild_Sk_quad k : rchild (S k) (quad k) = quad (S k) -1.
Proof.
 rewrite rchild_decomp, quad_decomp_Sk by lia.
 rewrite <- (decomp_sum (S k) (quad (S k))), quad_decomp by lia.
 cbn - ["*" "/" A]. replace (2*S k) with (S (2*k+1)); simpl; lia.
Qed.

Lemma rchild_SSk_quad k : k<>0 -> rchild (S (S k)) (quad k) = quad (S k) -1.
Proof.
 intros K. rewrite rchild_decomp, quad_decomp_SSk by lia.
 rewrite <- (decomp_sum (S (S k)) (quad (S k))), quad_decomp_Sk.
 cbn - ["*" "/" A]. replace (2*S k +1) with (S (2*k+2)) by lia.
 rewrite (@A_S (S (S k)) k). fixpred.
 replace (k - S k) with 0 by lia. simpl; lia.
Qed.

Lemma rchild_k_Sk_last_equality k n :
 k<>0 -> n = quad k -> rchild (S k) n = rchild (S (S k)) n.
Proof.
 intros K ->. now rewrite rchild_Sk_quad, rchild_SSk_quad.
Qed.

(* Some particular cases after the limit of the triangular zone *)

Lemma rchild_Sk_Squad k : rchild (S k) (S (quad k)) = S (quad (S k)).
Proof.
 rewrite rchild_decomp, decomp_S, quad_decomp_Sk by easy. simpl.
 case Nat.ltb_spec; try lia; intros _.
 case Nat.eqb_spec; try lia; intros _.
 rewrite quad_alt by easy.
 simpl map. replace (S (S (_+1))) with (2*k+3) by lia.
 replace (2*S k+1) with (2*k+3) by lia.
 cbn - ["*"]. generalize (@A_nz (S k) (2*k+3)); lia.
Qed.

Lemma rchild_SSk_Squad k : rchild (S (S k)) (S (quad k)) = quad (S k).
Proof.
 destruct (Nat.eq_dec k 0) as [->|K]; [easy|].
 rewrite rchild_decomp, decomp_S, quad_decomp_SSk by easy. simpl.
 case Nat.ltb_spec; try lia; intros _.
 case Nat.eqb_spec; try lia; intros _.
 rewrite <- (decomp_sum (S (S k)) (quad (S k))), quad_decomp_Sk.
 do 3 (f_equal; simpl; try lia).
Qed.

Lemma rchild_Sk_SSk_post_equality k n :
 n = S (quad k) -> rchild (S k) n = S (rchild (S (S k)) n).
Proof.
 intros ->. now rewrite rchild_Sk_Squad, rchild_SSk_Squad.
Qed.

Lemma f_after_triangle_1 k n :
 n = S (quad k) -> f k n = n - k - 3.
Proof.
 destruct (Nat.eq_dec k 0) as [->|K]; [now intros ->|].
 rewrite quad_alt by trivial.
 replace (S (_ -1)) with (A k (2*k+1))
  by (generalize (@A_nz k (2*k+1)); lia).
 intros ->. rewrite f_A, A_2k1_eqn by easy.
 rewrite (@A_base k k) by lia.
 replace (2*k+1-1) with (2*k); lia.
Qed.

Lemma f_after_triangle_2 k n :
 k<>0 -> n = S (quad k) -> f k (S n) = n - k - 2.
Proof.
 intros K.
 rewrite quad_alt by trivial.
 replace (S (_ -1)) with (A k (2*k+1))
  by (generalize (@A_nz k (2*k+1)); lia).
 intros ->. rewrite f_SA, A_2k1_eqn by lia.
 rewrite (@A_base k k) by lia.
 replace (2*k+1-1) with (2*k); lia.
Qed.

Lemma f_after_triangle_3 k n :
 n = S (quad k) -> f (S k) n = n - k - 2.
Proof.
 intros E.
 rewrite f_triangle; try lia.
 2:{ rewrite E. generalize (quad_min k). lia. }
 2:{ rewrite quad_S. lia. }
 rewrite E at 2.
 unfold quad. rewrite Nat.add_succ_r, triangle_succ.
 replace (_ - S k - 2) with (triangle (k+2) -2)
  by (generalize (triangle_aboveid (k+2)); lia).
 rewrite steps_triangle_minus; lia.
Qed.

Lemma f_after_triangle_4 k n :
 n = S (quad k) -> f (S k) (S n) = n - k - 1.
Proof.
 intros E.
 rewrite f_triangle; try lia.
 2:{ rewrite quad_S. lia. }
 rewrite E at 2.
 unfold quad. rewrite Nat.add_succ_r, triangle_succ.
 replace (_ - S k - 2) with (triangle (k+2) -1) by lia.
 rewrite steps_triangle_minus; lia.
Qed.

(** Another observation : [quad (S k)] is where [f k] and [f (S k)]
    differ by 2 for the first time *)

Lemma quadS_decomp k : k<>0 -> decomp k (quad (S k)) = [k+1;2*k+1].
Proof.
 intros K. apply decomp_carac; trivial.
 - repeat constructor. lia.
 - rewrite quad_S. rewrite <- (decomp_sum k (quad k)), quad_decomp; trivial.
   replace (k+1) with (S k) by lia.
   replace (2*k+1) with (S (2*k)) by lia.
   set (k2 := 2*k). simpl.
   replace (k2-(k-1)) with (S k) by lia. simpl.
   replace (k-(k-1)) with 1 by lia. simpl.
   rewrite (@A_base k k) by lia. lia.
Qed.

Lemma f_Sk_quadSk k : f (S k) (quad (S k)) = S (quad k).
Proof.
 rewrite f_last_triangle_1, quad_S; lia.
Qed.

Lemma f_k_quadSk k : k<>0 -> f k (quad (S k)) = quad k - 1.
Proof.
 intros K. rewrite f_decomp, quadS_decomp by trivial.
 replace (k+1) with (S k) by lia.
 replace (2*k+1) with (S (2*k)) by lia. simpl.
 rewrite <- (decomp_sum k (quad k)), quad_decomp; simpl; lia.
Qed.

Lemma f_quad_diff_2 k n :
 k<>0 -> n = quad (S k) -> f (S k) n = 2 + f k n.
Proof.
 intros K ->. rewrite f_Sk_quadSk, f_k_quadSk; trivial.
 generalize (quad_min k). lia.
Qed.

(* TODO:
Lemma f_quad_first_diff_2 k n :
 n < quad (S k) -> f (S k) n <= 1 + f k n.
Proof.
Admitted.
*)

(** * Another equation about [f]

    This one will be used later when flipping [F] left/right. *)

Lemma f_alt_eqn k n : k<>0 -> f k n + fs k (k-1) (f k (S n) - 1) = n.
Proof.
 intros K. destruct (Nat.eq_dec n 0) as [-> |Hn].
 - rewrite f_k_1. simpl. apply fs_k_0.
 - assert (Hn' := f_nz k Hn).
   case (f_step k n) as [H|H].
   + (* n left child of a binary node *)
     rewrite H.
     generalize (f_eqn k (n-1)).
     case (f_step k (n - 1)); fixpred.
     * generalize (@f_max_two_antecedents k (n-1) (S n)). lia.
     * intros. replace (f k n - 1) with (f k (n-1)) by lia.
       rewrite <- iter_S. fixpred. lia.
   + (* n is rightmost child *)
     generalize (f_eqn k n). rewrite H, pred_succ, <- iter_S. fixpred; lia.
Qed.


(** * Depth in the [f] tree *)

(** The depth of a node in the [f] tree is the number of
    iteration of [f] needed before reaching node 1.
    Actually, it is equal to invA_up except when k=0 *)

Fixpoint depth_loop k n cpt :=
 match cpt with
 | 0 => 0
 | S cpt' => if n <=? 1 then 0 else S (depth_loop k (f k n) cpt')
 end.

Definition depth k n := depth_loop k n n.

Lemma depth_loop_ok k n c c' :
  n <= c -> n <= c' -> depth_loop k n c = depth_loop k n c'.
Proof.
 revert n c'.
 induction c as [|c IH]; destruct c' as [|c']; simpl; auto.
 - now inversion 1.
 - now inversion 2.
 - intros. case Nat.leb_spec; trivial; intros. f_equal.
   apply IH; generalize (@f_lt k n); lia.
Qed.

Lemma depth_0 k : depth k 0 = 0.
Proof.
 reflexivity.
Qed.

Lemma depth_1 k : depth k 1 = 0.
Proof.
 reflexivity.
Qed.

Lemma depth_eqn k n : 1<n -> depth k n = S (depth k (f k n)).
Proof.
 intros N.
 unfold depth. destruct n; try lia.
 simpl. case Nat.leb_spec; try lia; intros.
 f_equal. apply depth_loop_ok; trivial.
 generalize (@f_lt k (S n) N). lia.
Qed.

Lemma f_depth k n : k<>0 -> depth k (f k n) = depth k n - 1.
Proof.
 intros K. destruct (le_lt_dec n 1) as [LE|LT].
 - assert (H : n=0 \/ n=1) by lia.
   destruct H as [-> | ->]; simpl; now rewrite ?f_k_0, ?f_k_1.
 - rewrite (depth_eqn k LT). lia.
Qed.

Lemma fs_depth k p n : k<>0 -> depth k (fs k p n) = depth k n - p.
Proof.
 intros K. induction p; simpl.
 - lia.
 - rewrite f_depth, IHp; lia.
Qed.

Lemma depth_correct k n : n<>0 -> fs k (depth k n) n = 1.
Proof.
 induction n as [[|[|n]] IH] using lt_wf_rec.
 - lia.
 - reflexivity.
 - intros _. rewrite depth_eqn by lia.
   rewrite iter_S. apply IH.
   + apply f_lt. lia.
   + apply f_nz. lia.
Qed.

Lemma depth_minimal k n : 1<n -> 1 < fs k (depth k n - 1) n.
Proof.
 induction n as [[|[|n]] IH] using lt_wf_rec.
 - lia.
 - lia.
 - intros _. rewrite depth_eqn by lia.
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
 - rewrite (@depth_eqn k (S (S n))), (@depth_eqn k m) by lia.
   apply le_n_S.
   apply IH.
   + apply f_lt. lia.
   + now apply f_mono.
Qed.

Lemma depth_A k p : k<>0 -> depth k (A k p) = p.
Proof.
 intros K. induction p as [|p IH].
 - reflexivity.
 - rewrite depth_eqn.
   + now rewrite f_A, pred_succ, IH.
   + change 1 with (A k 0). apply A_lt. auto with arith.
Qed.

Lemma depth_SA k p : k<>0 -> depth k (S (A k p)) = S p.
Proof.
 intros K. induction p as [|p IH].
 - simpl. unfold depth. simpl. rewrite f_init; simpl; lia.
 - rewrite depth_eqn.
   + rewrite f_SA, pred_succ; try lia.
   + generalize (@A_nz k (S p)). lia.
Qed.

Lemma depth_k0 n : depth 0 n = if n <=? 1 then 0 else 1.
Proof.
 case Nat.leb_spec; intros.
 - destruct n. now rewrite depth_0. unfold depth. simpl.
   now replace n with 0 by lia.
 - rewrite depth_eqn by trivial. rewrite f_0.
   replace (min 1 n) with 1 by lia. now rewrite depth_1.
Qed.

Lemma depth_is_0 k n : depth k n = 0 <-> n <= 1.
Proof.
 destruct n as [|[|n]].
 - rewrite depth_0; intuition.
 - rewrite depth_1; intuition.
 - rewrite depth_eqn; lia.
Qed.

Lemma depth_carac k p n : k<>0 -> p<>0 ->
  (depth k n = p <-> S (A k (p-1)) <= n <= A k p).
Proof.
 intros K Hp.
 split; intros H.
 - split.
   + destruct (le_lt_dec n (A k (p-1))) as [LE|LT]; trivial.
     apply (depth_mono k) in LE. rewrite depth_A in LE; lia.
   + destruct (le_lt_dec n (A k p)) as [LE|LT]; trivial.
     unfold lt in LT. apply (depth_mono k) in LT.
     rewrite depth_SA in LT; lia.
 - destruct H as (H1,H2).
   apply (depth_mono k) in H1. apply (depth_mono k) in H2.
   rewrite depth_A in H2 by lia. rewrite depth_SA in H1; lia.
Qed.

Lemma depth_alt k n : k<>0 -> depth k n = invA_up k n.
Proof.
 intros K.
 destruct (Nat.le_gt_cases n 1).
 - replace (depth k n) with 0; symmetry. apply invA_up_is_0; lia.
   apply depth_is_0; lia.
 - rewrite depth_carac; trivial. 2:{ rewrite (invA_up_is_0 k); lia. }
   split. generalize (@invA_up_least k n). lia. apply invA_up_spec.
Qed.

Lemma depth_init k n : k<>0 -> depth k n = n-1 <-> n <= k+2.
Proof.
 intros K. destruct n as [|[|n]].
 - rewrite ?depth_0. lia.
 - rewrite ?depth_1. lia.
 - simpl.
   rewrite depth_carac by lia.
   rewrite pred_succ.
   split; intros.
   + assert (A k n = S n) by (generalize (A_lt_id k n); lia).
     rewrite <- A_base_iff in *; lia.
   + simpl.
     rewrite A_base by lia.
     generalize (@A_nz k (n-(k-1))); lia.
Qed.
