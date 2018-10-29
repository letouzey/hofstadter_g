
Require Import Arith Omega Wf_nat List.
Require Import DeltaList Fib FunG.
Require Extraction.
Set Implicit Arguments.

(** Study of the functional equation:
     - [Fk 0 = 0]
     - [Fk (S n) + Fk^k (n) = S n]
    where [Fk^k (n)] is [k] repeated applications of [Fk] at [n].

    Note that Hofstadter's [G] is [F2], [H] is [F3].
*)

(** Coq representation of [F] as an inductive relation. This way,
    no need to convince Coq yet that [F] is indeed a function.
    - [F k n a] means that [Fk(n) = a].
    - [Fs p k n a] means that [Fk^p (n) = a].
*)

Inductive F : nat -> nat -> nat -> Prop :=
| F0l n : F 0 n n
| F0r k : F k 0 0
| FS k n a b : Fs (S k) (S k) n a -> S n = a+b -> F (S k) (S n) b

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

Lemma Fs_le p k n a : Fs p k n a -> a <= n.
Proof.
 induction 1 as [k n | p k a b c H IH H']; trivial.
 apply F_le in H'. omega.
Qed.
Hint Resolve F_le Fs_le.

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
- destruct k.
  + now exists (S n).
  + assert (Hs : forall p m, m <= n -> { a : nat | Fs p (S k) m a }).
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

Definition f k n := let (a,_) := f_spec k n in a.

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

(** A few tests *)

Definition test := List.seq 0 20.

Compute List.map (f 0) test. (* 0 1 2 3 4 5 6 ... *)
Compute List.map (f 1) test. (* 0 1 1 2 2 3 3 4 4 5 5 6 6 ... *)
Compute List.map (f 2) test. (* 0 1 1 2 3 3 4 4 5 6 6 7 8 8 *)
Compute List.map (f 3) test. (* 0 1 1 2 3 4 4 5 5 6 7 7 8 9 *)
Compute List.map (f 4) test.

Extraction Inline lt_wf_rec induction_ltof2.
Recursive Extraction f.

(** Basic equations over [f] : the same as [F] *)

Lemma f_k_0 k : f k 0 = 0.
Proof.
 reflexivity.
Qed.

Lemma f_0_n n : f 0 n = n.
Proof.
 now apply f_complete.
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

Lemma f_eqn k n : k<>0 -> f k (S n) + ((f k)^^k) n = S n.
Proof.
destruct k.
 - now destruct 1.
 - intros _.
   assert (H := f_sound (S k) (S n)).
   inversion_clear H.
   assert ((f (S k) ^^(S k)) n = a).
   { revert H0. apply F_Fs_fun. apply Fs_iter_f. }
   omega.
Qed.

Lemma f_eqn_pred k n : k<>0 -> f k n + ((f k)^^k) (pred n) = n.
Proof.
intros.
destruct n.
- simpl. apply fs_k_0.
- now apply f_eqn.
Qed.

Lemma f_S k n : k<>0 -> f k (S n) = S n - (f k ^^k) n.
Proof.
 intros H. generalize (f_eqn n H). omega.
Qed.

Lemma f_pred k n : k<>0 -> f k n = n - (f k ^^k) (pred n).
Proof.
intros H. generalize (f_eqn_pred n H). omega.
Qed.

(** Particular case *)

Lemma f_2_g n : f 2 n = g n.
Proof.
revert n.
apply g_unique.
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
    replace (n + (S (n+0))) with (S (2*n)); omega. }
  split; auto.
  rewrite f_pred; auto.
  simpl Nat.iter.
  replace (S (n + (S (n+0)))) with (2*(S n)); omega.
Qed.

Lemma f_unique k g : k<>0 ->
  g 0 = 0  ->
  (forall n, S n = g (S n)+ (g^^k) n) ->
  forall n, g n = f k n.
Proof.
intros Hk g_0 g_S.
induction n as [[|n] IH] using lt_wf_ind.
- now rewrite g_0, f_k_0.
- assert (forall p m, m <= n -> (g^^p) m = ((f k)^^p) m).
  { induction p.
    - now simpl.
    - intros. simpl.
      rewrite IHp; auto. apply IH.
      rewrite Nat.lt_succ_r. apply le_trans with m; auto.
      eapply Fs_le. eapply Fs_iter_f. }
  rewrite f_S, <- H; auto. specialize (g_S n). omega.
Qed.

Lemma f_step k n : f k (S n) = f k n \/ f k (S n) = S (f k n).
Proof.
destruct k.
- rewrite !f_0_n. now right.
- induction n as [n IH] using lt_wf_ind.
  destruct n.
  + rewrite f_k_0, f_k_1; now right.
  + rewrite f_S; auto.
    rewrite f_S; auto.
    set (fSk := f (S k)) in *.
    assert (forall p m, m <= n ->
             (fSk^^p) (S m) = (fSk^^p) m \/
             (fSk^^p) (S m) = S ((fSk^^p) m)).
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

Lemma f_mono_S k n : f k n <= f k (S n).
Proof.
 generalize (f_step k n). omega.
Qed.

Lemma f_mono k n m : n <= m -> f k n <= f k m.
Proof.
induction 1.
- trivial.
- transitivity (f k m); auto using f_mono_S.
Qed.

(** NB : in Coq, for natural numbers, 3-5 = 0 (truncated subtraction) *)

Lemma f_lipschitz k n m : f k m - f k n <= m - n.
Proof.
destruct (le_ge_dec n m) as [H|H].
- induction H; try generalize (f_step k m); omega.
- generalize (f_mono k H). omega.
Qed.

Lemma f_nonzero k n : 0 < n -> 0 < f k n.
Proof.
 unfold lt. intros. rewrite <- (f_k_1 k). now apply f_mono.
Qed.

Lemma f_0_inv k n : f k n = 0 -> n = 0.
Proof.
destruct n; trivial.
assert (0 < f k (S n)) by (apply f_nonzero; auto with arith).
omega.
Qed.

Lemma fs_0_inv p k n : ((f k)^^p) n = 0 -> n = 0.
Proof.
 induction p.
 - now simpl.
 - simpl.
   intros. apply IHp. eapply f_0_inv; eauto.
Qed.

Lemma f_nz k n : n <> 0 -> f k n <> 0.
Proof.
intros H. contradict H. now apply (f_0_inv k).
Qed.

Lemma f_fix k n : f k n = n <-> k = 0 \/ n <= 1.
Proof.
split.
- destruct n; auto.
  destruct k; auto.
  assert (H := @f_eqn (S k) n).
  intros Eq; rewrite Eq in H; clear Eq.
  right.
  assert (H' : ((f (S k))^^(S k)) n = 0) by omega.
  apply fs_0_inv in H'.
  now subst.
- intros [->| ]. apply f_0_n.
  assert (Hn : n=0 \/ n=1) by omega.
  destruct Hn as [-> | ->]; auto using f_k_0, f_k_1.
Qed.

Lemma f_le k n : f k n <= n.
Proof.
 eapply F_le; eauto.
Qed.

Lemma f_lt k n : k<>0 -> 1<n -> f k n < n.
Proof.
intros Hk H.
destruct (le_lt_or_eq _ _ (f_le k n)); trivial.
rewrite f_fix in *. omega.
Qed.
Hint Resolve f_lt.

Lemma f_nonflat k n : f k (S n) = f k n -> f k (S (S n)) = S (f k n).
Proof.
 destruct k.
 - rewrite !f_0_n. omega.
 - intros H.
   assert (Hk : S k <> 0) by omega.
   generalize (f_eqn (S n) Hk) (f_eqn n Hk).
   rewrite !iter_S. rewrite H. omega.
Qed.

Lemma f_nonflat' k n : f k (S n) = f k n -> f k (n-1) = f k n - 1.
Proof.
 destruct n.
 - now rewrite f_k_0, f_k_1.
 - replace (S n - 1) with n by omega.
   intros H.
   destruct (f_step k n) as [H'|H'].
   + apply f_nonflat in H'. omega.
   + omega.
Qed.

Lemma f_SS k n : S (f k n) <= f k (S (S n)).
Proof.
 destruct (f_step k n) as [E|E].
 - generalize (f_nonflat _ _ E). omega.
 - transitivity (f k (S n)). omega. auto using f_mono_S.
Qed.

Lemma f_double_le k n : n <= f k (2*n).
Proof.
induction n.
- trivial.
- replace (2* S n) with (S (S (2*n))) by omega.
  transitivity (S (f k (2*n))). omega. apply f_SS.
Qed.

Lemma f_div2_le k n : n/2 <= f k n.
Proof.
 rewrite <- Nat.div2_div.
 rewrite (Nat.div2_odd n) at 2.
 transitivity (f k (2*Nat.div2 n)).
 apply f_double_le.
 apply f_mono. omega.
Qed.
