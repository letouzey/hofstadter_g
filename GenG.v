
Require Import Arith Omega Wf_nat List.
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

    With this setting, [F1] is Hofstadter's [G], and [F2] is [H].
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

Definition test := List.seq 0 15.

Compute map (f 0) test. (* [0; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5; 6; 6; 7; 7] *)
Compute map (f 1) test. (* [0; 1; 1; 2; 3; 3; 4; 4; 5; 6; 6; 7; 8; 8; 9] *)
Compute map (f 2) test. (* [0; 1; 1; 2; 3; 4; 4; 5; 5; 6; 7; 7; 8; 9; 10] *)
Compute map (f 3) test. (* [0; 1; 1; 2; 3; 4; 5; 5; 6; 6; 7; 8; 8; 9; 10] *)

Compute map (fun x => (x,(f 2^^3) x)) test.
Compute proj1_sig (decomp_exists 2 27).


Extraction Inline lt_wf_rec induction_ltof2.
Recursive Extraction f.

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

Lemma f_lt k n : 1<n -> f k n < n.
Proof.
intros H.
destruct (le_lt_or_eq _ _ (f_le k n)); trivial.
rewrite f_fix in *. omega.
Qed.
Hint Resolve f_lt.

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

Lemma f_SS k n : S (f k n) <= f k (S (S n)).
Proof.
 destruct (f_step k n) as [E|E].
 - generalize (f_nonflat _ _ E). simpl in *. omega.
 - transitivity (f k (S n)). omega. auto using f_mono_S.
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

Definition h k n := sumA k (map pred (decomp k n)).

Lemma decomp_h k n :
  decomp k (h k n) = renorm k (map pred (decomp k n)).
Proof.
 apply decomp_carac.
 - apply renorm_delta.
   apply Delta_map with (S k).
   intros; omega. apply decomp_delta.
 - now rewrite renorm_sum.
Qed.

Lemma hs k p n : p <= S k ->
 (h k^^p) n = sumA k (map (decr p) (decomp k n)).
Proof.
 intros Hp.
 revert n.
 induction p; intros.
 - simpl. rewrite map_ext with (g:=id) by apply decr_0.
   rewrite map_id. symmetry. apply decomp_sum.
 - rewrite iter_S.
   rewrite IHp; auto with arith.
   rewrite decomp_h.
   rewrite renorm_mapdecr; auto. f_equal.
   symmetry. apply map_decr_S.
Qed.

Lemma f_is_h k n : f k n = h k n.
Proof.
 symmetry.
 apply f_unique.
 - reflexivity.
 - clear n. intros n.
   rewrite hs; auto.
   assert (Hn := decomp_sum k n).
   assert (D := decomp_delta k n).
   remember (decomp k n) as l eqn:Hl.
   destruct l as [|a l].
   + simpl in *. now subst.
   + unfold h. rewrite decomp_S, <- Hl. simpl.
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

Lemma f_sumA k l : Delta (S k) l ->
 f k (sumA k l) = sumA k (map pred l).
Proof.
 intros.
 rewrite f_is_h; auto.
 unfold h.
 f_equal. f_equal.
 now apply decomp_carac.
Qed.

Lemma fs_sumA k p l : p <= S k -> Delta (S k) l ->
 (f k ^^p) (sumA k l) = sumA k (map (decr p) l).
Proof.
 intros.
 remember (sumA k l) as n eqn:Hn.
 rewrite <- (@decomp_carac k n l); auto.
 rewrite <- hs; auto.
 induction p; simpl; auto.
 rewrite IHp by omega. now apply f_is_h.
Qed.
