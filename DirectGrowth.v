Require Import MoreTac MoreFun MoreList GenFib GenG.
Import ListNotations.

(** * Direct proofs of monotonicity for the F function family *)

(** Here we use the definition of F given in GenG, which computes
    quite slowly, but is easier to manipulate in proofs. See Fast.f
    for faster computations if necessary. Anyway, we recall that
    F satisfies indeed [F k 0 = 0] and [F k n = n - ((F k)^^k) (n-1)]
    (where h^^n is h composed n times with itself).
    Moreover (Fs k p n) is an alias for ((F k)^^p)(n). *)

Notation F := GenG.f.
Notation Fs k p := (GenG.fs k p).

Lemma F_base k : F k 0 = 0.
Proof.
 apply f_k_0.
Qed.

Lemma F_rec k n : F k n = n - ((F k)^^k)(n-1).
Proof.
 replace (n-1) with (Nat.pred n) by lia. apply f_pred.
Qed.

(** ** Section 2 : Basic properties of function F *)

(** Righmost inverse of F have already been studied in GenG under
    the name rchild. *)

Notation L := rchild.

Lemma L_alt k n : L k n = n + Fs k (k-1) n.
Proof.
 easy.
Qed.

Lemma L_mono k n m : n <= m -> L k n <= L k m.
Proof.
 unfold L. intros. apply Nat.add_le_mono; trivial. now apply fs_mono.
Qed.

Lemma L_strmono k n m : n < m -> L k n < L k m.
Proof.
 unfold L. intros. apply Nat.add_lt_le_mono; trivial.
 apply fs_mono; lia.
Qed.

Lemma F_galois k n m : k<>0 -> F k n <= m <-> n <= L k m.
Proof.
 intros Hk. split; intros LE.
 - apply (L_mono k) in LE. rewrite <- LE.
   generalize (@f_children k _ n Hk eq_refl). unfold lchild, L; lia.
 - apply (f_mono k) in LE. rewrite f_onto_eqn in LE; trivial.
Qed.

Lemma F_galois_lt k n m : k<>0 -> m < F k n <-> L k m < n.
Proof.
 intros. rewrite !Nat.lt_nge. now rewrite F_galois.
Qed.

Lemma Fs_galois k p n m : k<>0 -> Fs k p n <= m <-> n <= (L k^^p) m.
Proof.
 intros Hk. revert n m.
 induction p; intros n m; try rewrite iter_S, IHp, F_galois; simpl; lia.
Qed.

Lemma Fs_galois_lt k p n m : k<>0 -> m < Fs k p n <-> (L k^^p) m < n.
Proof.
 intros. rewrite !Nat.lt_nge. now rewrite Fs_galois.
Qed.

(** Leftmost inverse of F and its iterates *)

Definition I k n := n + Fs k (k-1) (n-1).
Notation Is k p n := ((I k^^p) n).

Lemma I_0 k : I k 0 = 0.
Proof.
 unfold I. now rewrite fs_k_0.
Qed.

Lemma I_1 k : I k 1 = 1.
Proof.
 unfold I. now rewrite fs_k_0.
Qed.

Lemma I_above_id k n : n <= I k n.
Proof.
 unfold I. lia.
Qed.

Lemma I_as_L k n : n<>0 -> I k n = S (L k (n-1)).
Proof.
 intros Hn. unfold I, L. lia.
Qed.

Lemma I_is_inv k n : k<>0 -> F k (I k n) = n.
Proof.
 intros Hk.
 if (n = 0) as [->|Hn].
 - unfold I. simpl. now rewrite fs_k_0.
 - rewrite I_as_L by trivial.
   replace n with (S (n-1)) at 2 by lia.
   rewrite rightmost_child_carac; trivial.
   now apply f_onto_eqn.
Qed.

Lemma I_is_leftmost k n : k<>0 -> F k (I k n - 1) = n - 1.
Proof.
 intros Hk.
 if (n = 0) as [->|Hn].
 - unfold I. simpl. now rewrite fs_k_0.
 - rewrite I_as_L by trivial.
   replace (S _ -1) with (L k (n-1)) by lia.
   now apply f_onto_eqn.
Qed.

Lemma I_or k n :
  k<>0 -> I k n = L k n \/ I k n = L k n - 1.
Proof.
 intros Hk. apply f_children; trivial. now apply I_is_inv.
Qed.

Lemma F_onto_or k n a :
  k<>0 -> F k n = a -> n = I k a \/ n = L k a.
Proof.
 intros Hk <-.
 if (n = 0) as [->|Hn].
 - rewrite f_k_0, I_0. now left.
 - unfold I, L.
   destruct (f_step k (n-1)) as [H|H];
   replace (S (n-1)) with n in * by lia.
   + right. rewrite H at 2. rewrite <- iter_S.
     replace (S (k-1)) with k by lia.
     replace (n-1) with (pred n) by lia. symmetry. apply f_eqn_pred.
   + left. replace (F k n - 1) with (F k (n-1)) by lia.
     rewrite <- iter_S.
     replace (S (k-1)) with k by lia.
     replace (n-1) with (pred n) by lia. symmetry. apply f_eqn_pred.
Qed.

Lemma I_F k n : k<>0 -> I k (F k n) = n \/ I k (F k n) = n-1.
Proof.
 intros Hk.
 destruct (F_onto_or k n (f k n) Hk eq_refl).
 - now left.
 - rewrite H at 2 4. now apply I_or.
Qed.

Lemma I_F_le k n : k<>0 -> I k (F k n) <= n.
Proof.
 intros Hk. destruct (I_F k n Hk); lia.
Qed.

Lemma Is_0 k p : Is k p 0 = 0.
Proof.
 induction p; simpl; trivial. now rewrite IHp, I_0.
Qed.

Lemma Is_1 k p : Is k p 1 = 1.
Proof.
 induction p; simpl; trivial. now rewrite IHp, I_1.
Qed.

Lemma Is_above_id k p n : n <= Is k p n.
Proof.
 induction p; trivial. simpl. now rewrite <- I_above_id.
Qed.

Lemma Is_is_inv k p n : k<>0 -> Fs k p (Is k p n) = n.
Proof.
 intros Hk.
 induction p; try easy. rewrite (iter_S (F k)). simpl.
 rewrite I_is_inv; trivial.
Qed.

Lemma Is_is_leftmost k p n : k<>0 -> Fs k p (Is k p n - 1) = n - 1.
Proof.
 intros Hk.
 if (n = 0) as [->|Hn].
 - rewrite Is_0. apply fs_k_0.
 - induction p; trivial. rewrite (iter_S (f k)). simpl.
   rewrite I_is_leftmost; trivial.
Qed.

Lemma Is_as_Ls k p n : n<>0 -> Is k p n = S (((L k)^^p) (n-1)).
Proof.
 revert n. induction p. simpl. lia.
 intros n Hn. simpl. rewrite IHp; trivial. rewrite I_as_L by easy.
 simpl. now rewrite Nat.sub_0_r.
Qed.

Lemma I_mono k n m : n <= m -> I k n <= I k m.
Proof.
 intros H. unfold I.
 apply Nat.add_le_mono; trivial. apply fs_mono; lia.
Qed.

Lemma Is_mono k p n m : n <= m -> Is k p n <= Is k p m.
Proof.
 intro H. induction p. easy. simpl. apply I_mono, IHp.
Qed.

Lemma I_strmono k n m : n < m <-> I k n < I k m.
Proof.
 split.
 - intros H. unfold I.
   apply Nat.add_lt_le_mono; trivial. apply fs_mono; lia.
 - intros H. apply Nat.lt_nge. intros LE. apply (I_mono k) in LE. lia.
Qed.

Lemma Is_strmono k p n m : n < m <-> Is k p n < Is k p m.
Proof.
 induction p. easy. simpl. now rewrite <- I_strmono.
Qed.

Lemma Is_Fs_le k p n : k<>0 -> Is k p (Fs k p n) <= n.
Proof.
 intros Hk. induction p; trivial.
 rewrite iter_S. simpl. etransitivity; [|apply IHp].
 apply Is_mono. now apply I_F_le.
Qed.

(** Galois connection, but this time Is is the left adjoint
    (while L was the right one). *)

Lemma galois_again k p n m : k<>0 -> Is k p n <= m <-> n <= Fs k p m.
Proof.
 intros Hk.
 split; intros H.
 - rewrite <- (Is_is_inv k p n) by trivial. now apply fs_mono.
 - apply (Is_mono k p) in H. rewrite H. now apply Is_Fs_le.
Qed.

Lemma galois_again_lt k p n m : k<>0 -> Fs k p m < n <-> m < Is k p n.
Proof.
 intros Hk. rewrite !Nat.lt_nge. now rewrite galois_again.
Qed.

Lemma Is_gt_id k p n : k<>0 -> p<>0 -> 1<n -> n < Is k p n.
Proof.
 intros Hk Hp Hn.
 apply galois_again_lt; trivial. apply fs_lt; lia.
Qed.

(** ** Section 3. The key equation expressing Is *)

Lemma Is_eqn k p n : k<>0 -> p<=k ->
  Is k p n = n + list_sum (map (fun i => Fs k i (n-1)) (seq (k-p) p)).
Proof.
 intros Hk. revert n.
 induction p; intros n Hk'.
 - simpl. lia.
 - change (p < k) in Hk'.
   rewrite iter_S, IHp by lia.
   unfold I at 1.
   rewrite seq_S.
   replace (k - S p + p) with (k-1) by lia.
   rewrite map_app, list_sum_app. simpl.
   ring_simplify. f_equal. f_equal.
   replace (k-p) with (S (k-(1+p))) by lia.
   rewrite <- seq_shift, map_map.
   apply map_ext. intros a. rewrite iter_S, I_is_leftmost; trivial.
Qed.

Lemma list_sum_eq {A} (f g : A -> nat) (l : list A) :
  (forall x : A, In x l -> f x = g x) ->
  list_sum (map f l) = list_sum (map g l).
Proof.
 induction l; simpl; try lia.
 intros H. f_equal. apply H. now left. apply IHl. firstorder.
Qed.

Lemma Is_k_Sk_eqn k n : k<>0 ->
 Is k (k+1) n
 = 2*n-1 + 2*Fs k (k-1) (n-1)
   + list_sum (map (fun i => Fs k i (n-1)) (seq 0 (k-1))).
Proof.
 intros Hk. rewrite (Nat.add_1_r k).
 rewrite iter_S, Is_eqn by lia.
 rewrite Nat.sub_diag.
 replace (seq 0 k) with (seq 0 (S (k-1))) by (f_equal; lia).
 simpl seq. rewrite <- seq_shift. simpl.
 rewrite map_map.
 rewrite !Nat.add_assoc. f_equal.
 2:{ apply list_sum_eq.
     intros x _. rewrite iter_S. rewrite I_is_leftmost; lia. }
 unfold I. rewrite !Nat.add_0_r.
 destruct n; try lia. simpl. now rewrite fs_k_0.
Qed.

(** ** Section 4 : Direct proof of non-strict ordering *)

(** Vision by "blocks" between flat steps of F
    (but without explicitly referring to these flat steps) *)

Lemma Fs_itvl k p n : k<>0 ->
  let r := Fs k p n in Is k p r <= n < Is k p (r+1).
Proof.
 intros Hk r. split.
 - now apply Is_Fs_le.
 - apply galois_again_lt; lia.
Qed.

Lemma Fs_itvl_exists k p n : k<>0 ->
  exists r, Is k p r <= n < Is k p (r+1).
Proof.
 intros Hk. exists (fs k p n). now apply Fs_itvl.
Qed.

Lemma F_low k n r : k<>0 ->
 Is k k r < n -> F k n <= n - r.
Proof.
 intros Hk H. assert (H' : Is k k r <= n-1) by lia.
 rewrite galois_again in H' by trivial.
 rewrite f_eqn. lia.
Qed.

Lemma F_high k n r : k<>0 ->
 n <= Is k k (r+1) -> n - r <= F k n.
Proof.
 intros Hk H.
 if (n = 0) as [->|Hn]. { rewrite f_k_0; lia. }
 assert (H' : n-1 < Is k k (r+1)) by lia.
 rewrite <- galois_again_lt in H' by trivial.
 rewrite f_eqn. lia.
Qed.

Lemma F_itvl_eq k n r : k<>0 ->
 Is k k r < n <= Is k k (r+1) -> f k n = n - r.
Proof.
 intros Hk (H,H').
 apply F_low in H; trivial.
 apply F_high in H'; trivial. lia.
Qed.

(** Particular case of F_itvl_eq *)

Lemma F_via_Is k n r : k<>0 -> n = S (Is k k r) -> F k n = n - r.
Proof.
 intros.
 apply F_itvl_eq; trivial. generalize (Is_strmono k k r (r+1)). lia.
Qed.

(** Key lemma thanks to Is_eqn : *)

Lemma Is_grows_if k n : k<>0 ->
 (forall p, Fs k p (n-1) <= Fs (k+1) p (n-1)) ->
 Is k k n <= Is (k+1) (k+1) n.
Proof.
 rewrite !Nat.add_1_r.
 intros Hk H.
 rewrite !Is_eqn by lia. apply Nat.add_le_mono_l.
 simpl Nat.sub. rewrite Nat.sub_diag, seq_S.
 rewrite map_app, list_sum_app. simpl.
 rewrite <- (Nat.add_0_r (list_sum _)). apply Nat.add_le_mono; try lia.
 apply list_sum_le. intros; apply H.
Qed.

(** "Directissima" proof of monotonicity wrt k.
    NB: m = Fs k k (n-1) is also n - f k n *)

Theorem F_grows k n : F k n <= F (k+1) n.
Proof.
 if (k = 0) as [->|Hk].
 { rewrite f_0. destruct n. simpl. easy. simpl.
   generalize (@f_nonzero 1 (S n)). lia. }
 induction n as [n IH] using lt_wf_ind.
 assert (IH' : forall p m, m < n -> fs k p m <= fs (k+1) p m).
 { induction p; trivial.
   intros m Hm. rewrite !iter_S, IHp.
   - now apply fs_mono, IH.
   - apply Nat.le_lt_trans with m; trivial. apply f_le. }
 clear IH.
 if (n = 0) as [->|Hn]. { now rewrite !f_k_0. }
 assert (H := Fs_itvl k k (n-1) Hk). set (m := fs k k (n-1)) in H.
 cbv zeta in H.
 assert (Hm : m <= n-1) by apply fs_le.
 assert (H' : Is k k (m+1) <= Is (k+1) (k+1) (m+1)).
 { apply Is_grows_if; trivial. intros p. apply IH'. lia. }
 transitivity (n - m); [apply F_low | apply F_high]; lia.
Qed.

Lemma Fs_grows k p n : Fs k p n <= Fs (k+1) p n.
Proof.
 revert n. induction p; trivial; intros n.
 rewrite !iter_S, IHp. apply fs_mono, F_grows.
Qed.

Lemma Is_grows k n : Is k k n <= Is (k+1) (k+1) n.
Proof.
 if (k = 0) as [->|Hk].
 - simpl. unfold I. lia.
 - apply Is_grows_if; trivial. intros. apply Fs_grows.
Qed.

Lemma F_grows_gen k k' n n' : k <= k' -> n <= n' -> f k n <= f k' n'.
Proof.
 intros K N. transitivity (f k' n); [ | now apply f_mono]. clear n' N.
 induction K; trivial. now rewrite <- Nat.add_1_r, <- (F_grows m n).
Qed.


(** ** Section 5 : F k < F (k+1) for large enough points. *)

(** *** Section 5.1 : We start with many auxiliary results *)

Notation T := triangle.
Notation N := quad.

Lemma Np1 n : N (n+1) = N n + (n+4).
Proof.
 rewrite Nat.add_1_r. apply quad_S.
Qed.

Lemma Nm1 n : n<>0 -> N n = N (n-1) + (n+3).
Proof.
 intros. replace n with (n-1+1) at 1 by lia. rewrite Np1. lia.
Qed.

Lemma triangle_mono n m : n<=m -> T n <= T m.
Proof.
 induction 1. lia. rewrite triangle_succ. lia.
Qed.

Lemma triangle_aboveidp3 n : 3<=n -> 3+n <= T n.
Proof.
 intros. replace n with (S (S (S (n-3)))) at 2 by lia.
 rewrite !triangle_succ. generalize (triangle_aboveid (n-3)); lia.
Qed.

Lemma triangle_pred n : T n = T (n-1) + n.
Proof.
 destruct n. easy. simpl. rewrite Nat.sub_0_r; lia.
Qed.

Lemma triangle_as_sum n : T n = list_sum (seq 1 n).
Proof.
 induction n; trivial.
 rewrite triangle_succ, IHn, seq_S, list_sum_app. simpl. lia.
Qed.

Lemma triangle_mono_iff a b : a <= b <-> T a <= T b.
Proof.
 split. apply triangle_mono.
 intros H. apply Nat.le_ngt. intros LT. red in LT.
 apply triangle_mono in LT. rewrite triangle_succ in LT. lia.
Qed.

Lemma triangle_str_mono a b : a < b <-> T a < T b.
Proof.
 now rewrite !Nat.lt_nge, triangle_mono_iff.
Qed.

Lemma triangle_inv n : exists p, T p <= n < T (S p).
Proof.
 exists (steps n). apply steps_spec'.
Qed.

Lemma list_sum_S l n : n = length l -> list_sum (map S l) = n + list_sum l.
Proof.
 intros ->. induction l; simpl; trivial. rewrite IHl; lia.
Qed.

Lemma list_sum_sub a b c : a+b <= S c ->
 list_sum (map (fun i => c - i) (seq a b))
 = list_sum (seq (S c - a - b) b).
Proof.
 revert a c. induction b; intros; trivial.
 rewrite seq_S, map_app, list_sum_app, IHb, <- cons_seq by lia.
 replace (S (S c - _ - _)) with (S c - a - b) by lia.
 cbn -["-"]. rewrite Nat.add_comm. f_equal. lia.
Qed.

Lemma Is_triangle k n :
 1 < n <= k+2 -> Is k k n = T (n-1) + k+1.
Proof.
 intros Hn.
 if (k = 0). { subst. simpl. replace n with 2; simpl; lia. }
 rewrite Is_eqn, Nat.sub_diag by trivial.
 rewrite map_ext_in with (g := fun i => max 1 (n-1-i)).
 2:{ intros m. rewrite in_seq. intros. apply fs_init. lia. }
 if (n = k+2).
 - rewrite map_ext_in with (g := fun i => n-1-i).
   2:{ intros m. rewrite in_seq. lia. }
   rewrite list_sum_sub by lia. replace (_-0-_) with 2 by lia.
   rewrite triangle_as_sum. replace (n-1) with (S k); simpl; lia.
 - replace k with (n-1+(k-(n-1))) at 1 by lia.
   rewrite seq_app, map_app, list_sum_app.
   rewrite map_ext_in with (g := fun i => n-1-i).
   2:{ intros m. rewrite in_seq. lia. }
   rewrite list_sum_sub by lia. replace (_-0-_) with 1 by lia.
   rewrite map_ext_in with (g := fun _ => 1).
   2:{ intros m. rewrite in_seq. lia. }
   rewrite list_sum_const, seq_length, Nat.mul_1_l.
   rewrite <- triangle_as_sum. lia.
Qed.

Lemma Is_incr_ge_2 k n : k<>0 -> n<>0 ->
  2 + Is k k n <= Is k k (S n).
Proof.
 intros Hk Hn.
 rewrite !Is_eqn by lia. rewrite Nat.sub_diag.
 replace k with (S (k-1)) at 1 2 by lia. simpl.
 rewrite <- !Nat.add_succ_l, !Nat.add_assoc.
 apply Nat.add_le_mono; try lia.
 apply list_sum_le. intros x _. apply fs_mono; lia.
Qed.

Lemma Is_after_f_flat k n : k<>0 ->
  f k (n+1) = f k n -> Is k k (n+2) = 2 + Is k k (n+1).
Proof.
 intros Hk Hf.
 rewrite !Is_eqn by lia. rewrite Nat.sub_diag.
 replace k with (S (k-1)) at 1 2 by lia. simpl.
 rewrite <- !Nat.add_succ_l, !Nat.add_assoc. f_equal. lia.
 f_equal. apply map_ext_in. intros a. rewrite in_seq. intros (Ha,_).
 replace (n+2-1) with (n+1) by lia. replace (n+1-1) with n by lia.
 induction a; try lia. simpl. destruct a. simpl; trivial. rewrite IHa; lia.
Qed.

Lemma Is_after_Fs_step k n : k<>0 ->
  Fs k (k-1) (n+1) <> Fs k (k-1) n -> Is k k (n+2) = k+1 + Is k k (n+1).
Proof.
 intros Hk Hf.
 rewrite !Is_eqn by lia. rewrite Nat.sub_diag.
 replace (n+1-1) with n by lia.
 replace (n+2-1) with (n+1) by lia.
 assert (Hf' : Fs k (k-1) (n+1) = 1 + Fs k (k-1) n).
 { rewrite Nat.add_1_r in *. destruct (fs_step k (k-1) n); lia. }
 assert (forall p, Fs k (S p) (n+1) = 1 + Fs k (S p) n ->
                   Fs k p (n+1) = 1 + Fs k p n).
 { intros p H. rewrite !Nat.add_1_r in *.
   assert (H' : Fs k (S p) (S n) <> Fs k (S p) n).
   { destruct (fs_step k (S p) n); lia. }
   assert (H'' : Fs k p (S n) <> Fs k p n).
   { contradict H'. simpl. now rewrite H'. }
   destruct (fs_step k p n); lia. }
 set (g := F k) in *. clearbody g. clear Hk Hf.
 induction k. simpl; lia.
 rewrite seq_S, !map_app, !list_sum_app. simpl.
 replace (S k-1) with k in Hf' by lia. rewrite Hf'.
 rewrite Nat.add_assoc, IHk. lia.
 destruct k. simpl; lia.
 replace (S k-1) with k by lia. now apply H.
Qed.

Lemma Is_kp2 k : Is k k (k+2) = T (k+2) - 1.
Proof.
 if (k = 0). { now subst. }
 rewrite Is_triangle, (triangle_pred (k+2)); lia.
Qed.

Lemma Is_kp3 k : Is k k (k+3) = N k.
Proof.
 if (k = 0). { now subst. }
 replace (k+3) with (k+1+2) by lia.
 rewrite Is_after_Fs_step; trivial; try (rewrite !fs_init; lia).
 replace (k+1+1) with (k+2) by lia. rewrite Is_kp2.
 unfold quad. replace (k+3) with (S (k+2)) by lia.
 rewrite (triangle_succ (k+2)). generalize (triangle_aboveid (k+2)); lia.
Qed.

Lemma Is_kp4 k : k<>0 -> Is k k (k+4) = 2 + N k.
Proof.
 intros Hk. replace (k+4) with (k+2+2) by lia.
 rewrite Is_after_f_flat; trivial.
 - f_equal. replace (k+2+1) with (k+3) by lia. apply Is_kp3.
 - replace (k+2+1) with (3+k) by lia. rewrite f_k_plus_3, f_init; lia.
Qed.

Lemma Is_kp5 k : k<>0 -> Is k k (k+5) = N (k+1) - 1.
Proof.
 intros Hk. replace (k+5) with (k+3+2) by lia.
 rewrite Is_after_Fs_step; trivial.
 - replace (k+3+1) with (k+4) by lia. rewrite Is_kp4, Np1; lia.
 - if (k=1). { now subst. }
   replace (k-1) with (S (k-2)) by lia. rewrite !iter_S.
   replace (k+3+1) with (4+k) by lia. replace (k+3) with (3+k) by lia.
   rewrite f_k_plus_4, f_k_plus_3; trivial.
   rewrite !fs_init; lia.
Qed.

(* The first "overlap" between (Is k k) and
   (Is (S k) (S k) is actually an equality. *)

Lemma Is_kp2' k : Is (k+1) (k+1) (k+2) = quad k - k.
Proof.
 rewrite Is_triangle by lia.
 replace (_+_+1) with (T (k+2)) by (rewrite triangle_pred; lia).
 unfold quad.
 rewrite (Nat.add_succ_r k 2), triangle_succ. lia.
Qed.

Lemma Is_kp3' k : Is (k+1) (k+1) (k+3) = quad k + 2.
Proof.
 replace (k+3) with (k+1+2) by lia. rewrite Is_kp2.
 replace (k+1+2) with (k+3) by lia. unfold quad.
 generalize (triangle_aboveid (k+3)); lia.
Qed.

Lemma Is_overlap_eq k : k<>0 -> Is k k (k+4) = Is (k+1) (k+1) (k+3).
Proof.
 intros. rewrite Is_kp4, Is_kp3'; trivial; lia.
Qed.

Lemma F_triangle_low k n p : k<>0 -> 1 < n <= N k ->
 T p <= n-k-2 -> f k n <= n - p - 1.
Proof.
 intros Hk Hn Hp.
 if (p = 0). { subst. simpl. generalize (@f_lt k n); lia. }
 if (n <= k+2).
 { rewrite f_init by lia. replace (n-k-2) with 0 in Hp by lia.
   apply (triangle_mono_iff p 0) in Hp. lia. }
 assert (p < k+2).
 { apply triangle_str_mono.
   unfold N in Hn. replace (k+3) with (S (k+2)) in Hn by lia.
   rewrite triangle_succ in Hn. lia. }
 replace (n-p-1) with (n-(p+1)) by lia. apply F_low; trivial.
 rewrite Is_triangle by lia. replace (p+1-1) with p; lia.
Qed.

Lemma F_triangle_high k n p : k<>0 -> 1 < n <= N k ->
 n-k-2 < T p -> n - p <= F k n.
Proof.
 intros Hk Hn Hp.
 if (p = 0). { now subst. }
 if (n <= k+2). { rewrite f_init; lia. }
 apply F_high; trivial.
 if (p < k+2).
 - rewrite Is_triangle by lia. replace (p+1-1) with p; lia.
 - rewrite <- (Is_mono k k (k+3)) by lia. now rewrite Is_kp3.
Qed.

Lemma F_triangle k n p : k<>0 -> 1 < n <= N k ->
 T p <= n-k-2 < T (p+1) -> f k n = n - p - 1.
Proof.
 intros Hk Hn (Hp,Hp').
 apply F_triangle_low in Hp; trivial.
 apply F_triangle_high in Hp'; lia.
Qed.

Lemma Fs_triangle_low k n p : k<>0 -> 0 < n < N k ->
 T p <= n-k-1 -> p+1 <= Fs k k n.
Proof.
 intros Hk Hn Hp.
 replace (n-k-1) with (S n-k-2) in Hp by lia.
 apply F_triangle_low in Hp; try lia.
 generalize (f_eqn_S k n) (fs_le k k n); lia.
Qed.

(* Lower bounds for (Fs k (k-1) n). *)

Lemma Fs_triangle_ineq k n p : k<>0 -> k+1 <= n < N k ->
 T p <= n-k-1 -> p+2 <= Fs k (k-1) n.
Proof.
 intros Hk Hn Hp.
 apply Fs_triangle_low in Hp; try lia.
 transitivity (S (Fs k k n)); try lia.
 replace (Fs k k n) with (Fs k (S (k-1)) n) by (f_equal; lia).
 apply f_lt. red. replace 2 with (fs k (k-1) (k+1)).
 - apply fs_mono; lia.
 - rewrite fs_init; lia.
Qed.

Lemma Fs_triangle_ineqS k n p :
 k<>0 -> k+2 <= n < N (k+1) ->
 T p <= n-k-2 -> p+2 <= Fs (k+1) k n.
Proof.
 intros Hk Hn Hp.
 replace (n-k-2) with (n-S k -1) in Hp by lia.
 apply Fs_triangle_ineq in Hp; try lia.
 - rewrite Hp. simpl. now rewrite Nat.add_1_r, Nat.sub_0_r.
 - rewrite Nat.add_1_r in Hn; lia.
Qed.

Lemma Fs_pred_le_iter k p n : Fs k p n <= Fs (k+1) p (n-1) ->
 forall q, p <= q -> Fs k q n <= Fs (k+1) q (n-1).
Proof.
 intros. replace q with (q-p+p) by lia.
 rewrite !iter_add, Fs_grows. now apply fs_mono.
Qed.

Lemma Fs_pred_plus_1 k p n : Fs k p n <= Fs (k+1) p (n-1) + 1.
Proof.
 rewrite Fs_grows.
 if (n=0). { subst; rewrite !fs_k_0; lia. }
 generalize (fs_step (S k) p (n-1)).
 replace (S (n-1)) with n by lia. rewrite Nat.add_1_r; lia.
Qed.

(** *** Section 5.2 : Bootstrap

   Is k k (n+1) <= Is (k+1) (k+1) n when k+3 <= n <= N k.
   (without relying on the decomposition GenFib.decomp) *)

Module Bootstrap.

Lemma F_pred_eq_triangle k n p : k<>0 -> k+3 <= n <= N k ->
 T p <= n-k-2 <= T p + 1 -> F k n = F (k+1) (n-1).
Proof.
 intros Hk Hn Hp.
 if (p = 0).
 { subst. unfold T in *; simpl in *.
   replace n with (k+3) by lia.
   rewrite Nat.add_comm, f_k_plus_3.
   replace (3+k-1) with (S (k+1)) by lia. rewrite f_k_Sk; lia. }
 rewrite (F_triangle (k+1) (n-1) (p-1)), (F_triangle k n p);
  rewrite ?Np1; try lia.
 - split. easy. rewrite Nat.add_1_r, triangle_succ. lia.
 - split.
   + replace (n-1-S k-2) with ((n-k-2)-2) by lia.
     rewrite triangle_pred in Hp.
     if (p=1); try lia. subst; unfold triangle; simpl; lia.
   + replace (p-1+1) with p by lia. red.
     if (n-k-2 < 2); try lia.
     transitivity 1; try apply (triangle_mono 1 p); lia.
Qed.

Lemma Fs_pred_le_triangle0 k n p q : k<>0 -> k+3 <= n <= N k -> 0<q<=p ->
 T p <= n-k-2 <= T p + q -> Fs k q n <= Fs (k+1) q (n-1).
Proof.
 intros Hk. revert p n. induction q; try lia.
 intros p n Hn Hq Hp.
 if (F k n <= F (k+1) (n-1)). { now apply Fs_pred_le_iter with 1. }
 if (n-k-2 <= T p + 1). { generalize (F_pred_eq_triangle k n p); lia. }
 rewrite !iter_S. replace (F (k+1) (n-1)) with (F k n - 1).
 2:{ generalize (Fs_pred_plus_1 k 1 n); simpl; lia. }
 assert (f k n = n - p - 1).
 { apply F_triangle; try lia. rewrite Nat.add_1_r, triangle_succ. lia. }
 apply IHq with (p-1); try lia.
 - split; try lia.
   if (p = 2).
   + subst p. simpl in *. lia.
   + generalize (triangle_aboveidp3 p); lia.
 - rewrite (triangle_pred p) in *. lia.
Qed.

(* same, without the constraint q<=p *)
Lemma Fs_pred_le_triangle k n p q : k<>0 -> k+3 <= n <= N k -> 0<q ->
 T p <= n-k-2 <= T p + q -> Fs k q n <= Fs (k+1) q (n-1).
Proof.
 intros Hk Hn Hq Hp.
 destruct (triangle_inv (n-k-2)) as (p' & Hp').
 assert (H : p <= p'). { rewrite <- Nat.lt_succ_r, triangle_str_mono; lia. }
 set (q' := n-k-2 - T p').
 assert (q' <= q). { apply triangle_mono in H. lia. }
 assert (q' <= p'). { rewrite triangle_succ in *. lia. }
 if (q' = 0).
 - apply Fs_pred_le_iter with 1; try lia. simpl.
   generalize (F_pred_eq_triangle k n p'); lia.
 - apply Fs_pred_le_iter with q'; try lia.
   apply Fs_pred_le_triangle0 with p'; lia.
Qed.

Lemma Fs_pred_le_bound k n q :
  k<>0 -> k+3 <= n <= N k -> 0<q ->
  n <= k + T (q+2) -> Fs k q n <= Fs (k+1) q (n-1).
Proof.
 intros Hk Hn Hq Hn'.
 destruct (triangle_inv (n-k-2)) as (p & LE & LT).
 apply Fs_pred_le_triangle with p; trivial. split; trivial.
 assert (n-k-2 < T (q+2) - 1) by lia.
 assert (p < q+2) by (apply triangle_str_mono; lia).
 rewrite triangle_succ, Nat.add_succ_r, Nat.lt_succ_r in LT.
 if (q = p-1); try lia.
 subst q. replace (p-1+2) with (S p) in * by lia.
 rewrite triangle_succ in *. lia.
Qed.

Lemma bootstrap k n :
  k<>0 -> k+3 <= n <= N k -> Is k k (n+1) <= Is (k+1) (k+1) n.
Proof.
 intros Hk Hn.
 if (n = k+3) as [->|Hn'].
 { rewrite <- Is_overlap_eq; trivial. replace (k+3+1) with (k+4); lia. }
 (* for n>k+3 the inequality is actually strict (but we don't really care). *)
 apply Nat.lt_le_incl.
 destruct (triangle_inv (n-k-1)) as (p & Hp1 & Hp2).
 if (p <= 1) as [Hp|Hp].
 { rewrite triangle_succ in Hp2.
   generalize (triangle_mono _ _ Hp). simpl. lia. }
 red in Hp2. replace (S (n-k-1)) with (n-k) in Hp2 by lia.
 assert (p < k+2).
 { apply triangle_str_mono.
   apply Nat.le_lt_trans with (quad k -k-1); try lia.
   unfold quad. rewrite Nat.add_succ_r, triangle_succ.
   generalize (triangle_aboveid (k+2)); lia. }
 assert (Hp' : S p <= fs (k+1) k (n-1)).
 { replace (S p) with ((p-1)+2) by lia. apply Fs_triangle_ineqS. trivial.
   - split; try lia. rewrite Np1; lia.
   - transitivity (triangle p - 2); try lia.
     rewrite (triangle_pred p); lia. }
 set (q := p-1). replace p with (S q) in Hp' by lia.
 assert (Fs k q n <= Fs (k+1) q (n-1)).
 { apply Fs_pred_le_bound; try lia. replace (q+2) with (S p); lia. }
 (* now something similar to the future Is_overlap_if0 *)
 rewrite 2 Is_eqn; try lia.
 rewrite <- Nat.add_assoc. apply Nat.add_lt_mono_l.
 rewrite !Nat.sub_diag.
 rewrite (Nat.add_1_r k) at 1.
 rewrite seq_S, map_app, list_sum_app. simpl. rewrite Nat.add_0_r.
 rewrite (Nat.add_comm (list_sum _)).
 red. etransitivity; [|apply Nat.add_le_mono_r; eauto].
 simpl. rewrite <- 2 Nat.succ_le_mono.
 replace k with (q + (k-q)) at 1 2 by lia.
 rewrite seq_app, !map_app, !list_sum_app, !Nat.add_0_l.
 rewrite Nat.add_assoc. apply Nat.add_le_mono.
 - rewrite <- list_sum_S. 2:now rewrite map_length, seq_length.
   rewrite map_map.
   apply list_sum_le.
   intros x _. replace (n+1-1) with n by lia. rewrite <- Nat.add_1_r.
   apply Fs_pred_plus_1.
 - apply list_sum_le.
   intros x. rewrite in_seq. intros (Hx,_).
   replace (n+1-1) with n by lia.
   apply Fs_pred_le_iter with q; lia.
Qed.

End Bootstrap.

(** *** Section 5.3 : The main induction for strict ordering *)

Lemma F_low_eq k n : n <= k+2 -> F k n = F (k+1) n.
Proof.
 intros.
 if (n = 0). { now subst. }
 if (n = 1). { subst. now rewrite !f_k_1. }
 rewrite !f_init; lia.
Qed.

Lemma Is_overlap_if0 k n : k+3 <= n ->
  F k n <= F (k+1) (n-1) ->
  Is k k (n+1) <= Is (k+1) (k+1) n.
Proof.
 intros Hn Hf.
 if (k = 0) as [->|Hk]. { simpl. unfold I. simpl. lia. }
 rewrite 2 Is_eqn; try lia.
 rewrite <- Nat.add_assoc. apply Nat.add_le_mono_l.
 rewrite !Nat.sub_diag.
 rewrite (Nat.add_1_r k) at 1.
 rewrite seq_S, map_app, list_sum_app. simpl. rewrite Nat.add_0_r.
 replace k with (S (k-1)) at 1 2 by lia. simpl seq. simpl.
 replace (n+1-1) with n by lia.
 rewrite <- Nat.add_succ_l.
 rewrite (Nat.add_comm (_+_)), Nat.add_assoc. apply Nat.add_le_mono.
 - replace (S n) with (2+(n-1)) by lia. apply Nat.add_le_mono_r.
   replace 2 with (Fs (k+1) k (k+2)) by (rewrite fs_init; lia).
   apply fs_mono; lia.
 - apply list_sum_le.
   intros p. rewrite in_seq. intros (Hp,_).
   destruct p; try lia. rewrite !iter_S, Fs_grows. now apply fs_mono.
Qed.

Lemma Is_overlap_if k n :
  F k n < F (k+1) n -> Is k k (n+1) <= Is (k+1) (k+1) n.
Proof.
 intros Hf.
 assert (Hn : k+3 <= n).
 { if (n <= k+2) as [H|H]; try lia. generalize (F_low_eq _ _ H); lia. }
 apply Is_overlap_if0; trivial.
 generalize (f_step (k+1) (n-1)); replace (S (n-1)) with n; lia.
Qed.

(** And finally the strict monotonicity.
    NB: see fk_fSk_last_equality for the equality at (N k). *)

Theorem F_grows_strict k n : N k < n -> F k n < F (k+1) n.
Proof.
 if (k = 0) as [->|Hk].
 { rewrite f_0. unfold N. simpl.
   destruct n. lia. red. intros H. rewrite <- (@f_k_3 1 lia).
   apply f_mono. lia. }
 induction n as [n IH] using lt_wf_ind. intros Hn.
 destruct (Fs_itvl k k (n-1) lia) as (_,Hm).
 set (m := Fs k k (n-1)) in Hm.
 assert (Em : m = n - F k n).
 { rewrite f_eqn. generalize (@fs_le k k (n-1)); lia. }
 replace (F k n) with (n-m) by (generalize (f_le k n); lia).
 assert (m < n). { generalize (@f_nz k n); lia. }
 assert (k+3 <= m).
 { rewrite <- Nat.lt_succ_r, (Is_strmono k k), Is_kp3, <- Nat.add_1_r.
   lia. }
 red. replace (S (n-m)) with (n - (m-1)) by lia.
 apply F_high. lia. replace (m-1+1) with m by lia.
 transitivity (Is k k (m+1)); try lia.
 if (m <= N k).
 - apply Bootstrap.bootstrap; lia.
 - apply Is_overlap_if, IH; lia.
Qed.

Corollary Is_overlap k n :
 k+3 <= n -> Is k k (n+1) <= Is (k+1) (k+1) n.
Proof.
 intros Hn.
 if (k = 0) as [->|Hk]. { simpl; unfold I; simpl; lia. }
 if (n <= N k).
 - apply Bootstrap.bootstrap; lia.
 - apply Is_overlap_if, F_grows_strict; lia.
Qed.


(** Immediate consequences of the strict monotonicity *)

Corollary Fkn_le_FSkPn k n : N k < n -> F k n <= F (k+1) (n-1).
Proof.
 intros.
 generalize (F_grows_strict k n) (f_step (k+1) (n-1)).
  replace (S (n-1)) with n; lia.
Qed.

Corollary Fkn_lt_FSkSn k n : n<>1 -> F k n < F (k+1) (n+1).
Proof.
 intros Hn.
 if (k = 0) as [->|Hk].
 { rewrite f_0. destruct n.
   + rewrite f_k_1. simpl; lia.
   + simpl. rewrite f_1_div2. red. change 2 with (4/2).
     apply Nat.div_le_mono; simpl; lia. }
 rewrite !Nat.add_1_r. apply (@fk_fSk_conjectures k Hk); trivial.
 rewrite <- Nat.add_1_r. apply F_grows_strict.
Qed.

(** Section 6 : First difference of 2 between F k and F (k+1) *)

(* We prove in Fk_FSk_diff_le_1 below that
   F (S k) n - F k n is in {0,1} as long as n < N (S k).
   More precisely, the difference F (S k) n - F k n is:

     0      for n <= k+2                (see above F_low_eq)
     1      for n = k+3                 (see below Fk_FSk_first_diff)
     0      for n = k+4                 (see below Fk_FSk_kp4)
     0 or 1 for k+5 <= n < N k          (see below Fk_FSk_low_diff)
     0      for n = N k                 (see below Fk_FSk_last_equality)
     1      for N k < n < N (S k)       (see below Fk_FSk_diff_1)
     2      for n = N (S k)             (see below Fk_FSk_diff_2)
*)

Lemma Fk_FSk_first_diff k : S (F k (k+3)) = F (k+1) (k+3).
Proof.
 if (k = 0) as [->|Hk]. easy.
 rewrite (Nat.add_comm k 3), f_k_plus_3 by trivial.
 rewrite f_init; lia.
Qed.

Lemma Fk_FSk_kp4 k : k<>0 -> F k (k+4) = F (k+1) (k+4).
Proof.
 intros Hk.
 rewrite (Nat.add_comm k 4), f_k_plus_4 by trivial.
 replace (4+k) with (3+(k+1)) by lia.
 rewrite f_k_plus_3; lia.
Qed.

Lemma Fk_FSk_triangle_diff_1 k n : k<>0 -> k+3 <= n <= N k ->
 (exists p, n-k-2 = triangle p) -> F (k+1) n = F k n + 1.
Proof.
 intros Hk Hn (p,Hp).
 if (p = 0). { subst. unfold triangle in Hp; simpl in Hp. lia. }
 rewrite (F_triangle k n p); try lia.
 2:{ rewrite Nat.add_1_r, triangle_succ. lia. }
 replace (n-p-1+1) with (n-(p-1)-1) by (generalize (triangle_aboveid p); lia).
 apply F_triangle; rewrite ?Np1; try lia.
 replace (p-1+1) with p by lia. split; try lia.
 replace (n-_-2) with (triangle p - 1) by lia.
 rewrite (triangle_pred p). lia.
Qed.

Lemma Fk_FSk_triangle_diff_0 k n : k<>0 -> k+3 <= n <= N k ->
 (forall p, n-k-2 <> triangle p) -> F (k+1) n = F k n.
Proof.
 intros Hk Hn Hp.
 destruct (triangle_inv (n-k-2)) as (p & Hp1 & Hp2). specialize (Hp p).
 rewrite <- (Nat.add_1_r p) in Hp2.
 rewrite !F_triangle with (p:=p); rewrite ?Np1; lia.
Qed.

Lemma Fk_FSk_low_diff k n : k<>0 -> n <= N k ->
  F (k+1) n <= 1 + F k n.
Proof.
 intros Hk Hn.
 if (n < k+3) as [Hn'|Hn']. { rewrite <- F_low_eq; lia. }
 destruct (triangle_inv (n-k-2)) as (p & Hp1 & Hp2).
 if (triangle p = n-k-2) as [E|E].
 - rewrite (Fk_FSk_triangle_diff_1 k n); try lia. now exists p.
 - rewrite (Fk_FSk_triangle_diff_0 k n); try lia.
   intros p' Hp'. apply E. clear E. rewrite Hp' in *. clear Hp'. f_equal.
   apply triangle_mono_iff in Hp1.
   apply triangle_str_mono in Hp2. lia.
Qed.

Lemma F_N k : k<>0 -> F k (N k) = N (k-1) + 1.
Proof.
 intros Hk.
 replace (N (k-1)+1) with (N k - (k+2)) by (rewrite Nm1; lia).
 apply F_itvl_eq; trivial. replace (k+2+1) with (k+3) by lia.
 rewrite Is_kp2, Is_kp3. split; try lia.
 unfold N. rewrite (Nat.add_succ_r k 2), triangle_succ. lia.
Qed.

Lemma FS_N k : k<>0 -> F (k+1) (N k) = N (k-1) + 1.
Proof.
 intros Hk.
 replace (N (k-1)+1) with (N k - (k+2)) by (rewrite Nm1; lia).
 apply F_itvl_eq; try lia. replace (k+2+1) with (k+1+2) by lia.
 rewrite Is_kp2', Is_kp2. split.
 - unfold N. generalize (triangle_aboveid (k+3)); lia.
 - unfold N. replace (k+1+2) with (k+3) by lia. lia.
Qed.

Lemma Fk_FSk_last_equality k n :
 k<>0 -> n = N k -> F k n = F (k+1) n.
Proof.
 intros K ->. rewrite F_N, FS_N; trivial.
Qed.

Lemma Fk_FSk_diff_1 k n :
  k<>0 -> N k < n < N (k+1) -> f (k+1) n = 1 + f k n.
Proof.
 intros Hk Hn.
 assert (F (k+1) n <= 1 + F k n); try (generalize (F_grows_strict k n); lia).
 destruct (Fs_itvl k k (n-1) lia) as (Lo,Hi).
 set (m := Fs k k (n-1)) in *.
 assert (Em : m = n - F k n).
 { rewrite f_eqn. generalize (@fs_le k k (n-1)); lia. }
 assert (k+3 <= m).
 { rewrite <- Nat.lt_succ_r, (Is_strmono k k), Is_kp3, <- Nat.add_1_r.
   lia. }
 assert (m <= k+4).
 { rewrite <- Nat.lt_succ_r, <- Nat.add_succ_r, (Is_strmono k k).
   rewrite Is_kp5; lia. }
 replace (1+F k n) with (n-(m-1)) by (generalize (f_le k n); lia).
 apply F_low; try lia.
 assert (Is (k+1) (k+1) (m-1) <= Is k k m); try lia.
 if (m = k+3).
 - replace (m-1) with (k+2) by lia.
   replace m with (k+3) by lia.
   rewrite Is_kp2', Is_kp3. lia.
 - replace (m-1) with (k+3) by lia.
   replace m with (k+4) by lia.
   rewrite Is_kp3', Is_kp4; lia.
Qed.

Lemma Fk_FSk_diff_le_1 k n :
 k<>0 -> n < N (k+1) -> F (k+1) n <= 1 + F k n.
Proof.
 intros.
 if (n <= N k). { apply Fk_FSk_low_diff; lia. }
 rewrite Fk_FSk_diff_1; lia.
Qed.

Lemma F_NS k : k<>0 -> F k (N (k+1)) = N k - 1.
Proof.
 intros. rewrite F_via_Is with (r:=k+5); trivial.
 - rewrite Np1. lia.
 - rewrite Is_kp5; trivial. generalize (quad_min (k+1)); lia.
Qed.

Lemma Fk_FSk_diff_2 k n :
  k<>0 -> n = N (k+1) -> F (k+1) n = 2 + F k n.
Proof.
 intros Hk ->.
 rewrite F_NS, F_N by lia.
 replace (k+1-1) with k; generalize (quad_min k); lia.
Qed.


(** ** Section 7 : Two former conjectures *)

(** *** Section 7.1 : Strict ordering of L (k+1) and L k

   We can now prove that (N (k-1)) is indeed the last point of equality
   between (L k) and (L (k+1)). *)

Lemma F_predN k : k<>0 -> F k (N k - 1) = N (k-1).
Proof.
 intros Hk.
 replace (N (k-1)) with ((N k -1) - (k+2)) by (rewrite Nm1; lia).
 apply F_itvl_eq; trivial. replace (k+2+1) with (k+3) by lia.
 rewrite Is_kp2, Is_kp3. split; try lia.
 unfold N. rewrite (Nat.add_succ_r k 2), triangle_succ.
 generalize (triangle_aboveid (k+2)); lia.
Qed.

Lemma L_N k : k<>0 -> L k (N (k-1)) = N k - 1.
Proof.
 symmetry.
 apply rightmost_child_carac; trivial.
 - now apply F_predN.
 - replace (S _) with (N k) by (generalize (quad_min k); lia).
   rewrite F_N; lia.
Qed.

Lemma FS_predN k : 1<k -> F (k+1) (N k - 1) = N (k-1).
Proof.
 intros Hk.
 replace (N (k-1)) with (N k -1 - (k+2)) by (rewrite Nm1; lia).
 apply F_itvl_eq; try lia. replace (k+2+1) with (k+1+2) by lia.
 rewrite Is_kp2', Is_kp2. split.
 - unfold N. generalize (triangle_aboveid (k+3)); lia.
 - unfold N. replace (k+1+2) with (k+3); lia.
Qed.

Lemma L_Sk_N k : 1<k -> L (k+1) (N (k-1)) = N k - 1.
Proof.
 intros Hk.
 symmetry.
 apply rightmost_child_carac; trivial; try lia.
 - now apply FS_predN.
 - replace (S (N k - 1)) with (N k) by (generalize (quad_min k); lia).
   rewrite FS_N; lia.
Qed.

Lemma L_k_Sk_last_equality k n : 1<k ->
   n = N (k-1) -> L k n = L (k+1) n.
Proof.
 intros Hk ->. rewrite L_N, L_Sk_N; lia.
Qed.

(** ... and this is indeed the last equality *)

Lemma F_Np1 k : k<>0 -> F k (S (N k)) = S (N (k-1)).
Proof.
 intros Hk.
 rewrite F_via_Is with (r:=k+3); trivial.
 - rewrite Nm1; lia.
 - now rewrite Is_kp3.
Qed.

Lemma F_Np2 k : k<>0 -> F k (2 + N k) = 2 + N (k-1).
Proof.
 intros Hk.
 replace (2 + N (k-1)) with ((2+ N k) - (k+3)) by (rewrite Nm1; lia).
 apply F_itvl_eq; trivial.
 replace (k+3+1) with (k+4) by lia.
 rewrite Is_kp3, Is_kp4; lia.
Qed.

Lemma L_SN k : k<>0 -> L k (S (N (k-1))) = S (N k).
Proof.
 symmetry.
 apply rightmost_child_carac; trivial. now apply F_Np1. now apply F_Np2.
Qed.

Lemma L_Sk_lt_L_k k m : k<>0 ->
 N (k-1) < m -> L (k+1) m < L k m.
Proof.
 intros Hk Hm.
 rewrite <- F_galois_lt by lia.
 rewrite <- (@f_onto_eqn k m) at 1 by lia.
 apply F_grows_strict. red.
 rewrite <- L_SN by easy.
 apply L_mono; lia.
Qed.

Lemma L_SSk_lt_L_Sk k m :
 N k < m -> L (k+2) m < L (k+1) m.
Proof.
 intros Hm. replace (k+2) with (k+1+1) by lia.
 apply L_Sk_lt_L_k. lia. now replace (k+1-1) with k by lia.
Qed.

(** Version for I *)

Lemma I_SSk_lt_I_Sk k m :
 S (N k) < m -> I (k+2) m < I (k+1) m.
Proof.
 intros Hm.
 rewrite !I_as_L by lia. rewrite <-Nat.succ_lt_mono.
 apply L_SSk_lt_L_Sk. lia.
Qed.

(** *** Section 7.2 : Weak ordering of (Fs k (k+1)) and (Fs (k+1) (k+2)).

   Proof that Fs k (k+1) n >= Fs (k+1) (k+2) n
   (in the first JIS article, this is the conjecture after figure 7.1)
   Note that we do have equality for some points n,
   see Article1.Equality_LkSkSk_LSkSSkSk *)

Lemma L_1 n : L 1 n = 2*n.
Proof.
 unfold L. simpl. lia.
Qed.

Lemma L_F_above k n : k<>0 -> n <= L k (F k n).
Proof.
 intros Hk. apply F_galois; lia.
Qed.

Lemma Fkp_2FkSp k p n : k<>0 -> Fs k p n <= 2 * Fs k (p+1) n.
Proof.
 intros Hk.
 rewrite <- L_1. simpl. rewrite Nat.add_1_r.
 transitivity (L 1 (F 1 (Fs k p n))).
 2:{ simpl. apply L_mono. apply F_grows_gen; lia. }
 rewrite <- L_F_above; lia.
Qed.

Lemma Is_kSk_SkSSk k n : k<>0 ->
 Is k (k+1) n <= Is (k+1) (k+2) n.
Proof.
 intros Hk. replace (k+2) with (k+1+1) by lia.
 rewrite !Is_k_Sk_eqn by lia.
 rewrite <- !Nat.add_assoc. apply Nat.add_le_mono_l.
 replace (k+1-1) with (S (k-1)) by lia.
 rewrite seq_S, map_app, list_sum_app. simpl list_sum.
 replace (S (k-1)) with k by lia.
 rewrite (Nat.add_comm (list_sum _)), !Nat.add_assoc.
 apply Nat.add_le_mono.
 2:{ apply list_sum_le. intros x Hx. apply Fs_grows. }
 replace (2*_) with (Fs k (k - 1) (n - 1) + Fs k (k - 1) (n - 1)) by lia.
 rewrite Nat.add_0_r.
 apply Nat.add_le_mono. 2:apply Fs_grows.
 rewrite Fs_grows, Fkp_2FkSp by lia. replace (k-1+1) with k; lia.
Qed.

Lemma Fs_kSk_SkSSk k n : k<>0 -> Fs (k+1) (k+2) n <= Fs k (k+1) n.
Proof.
 intros Hk.
 rewrite <- galois_again by trivial.
 rewrite Is_kSk_SkSSk by trivial.
 now rewrite galois_again by lia.
Qed.
