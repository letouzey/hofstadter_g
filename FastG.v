From Coq Require Import List Arith NArith Lia.
Require Import MoreFun MoreList GenG.
Require FlexArray.
Import ListNotations.
Local Open Scope N.

(** * Faster computation of [GenG.f]

    For that, we use the binary numbers [N]
    and tabulate older values via a FlexArray (log access time). *)

Definition f_array (k:nat)(n:N) :=
 N.peano_rect _
  (FlexArray.singleton 0)
  (fun n t => FlexArray.snoc t (N.succ n - (FlexArray.get t ^^k) n))
  n.

Definition f (k:nat)(n:N) := FlexArray.get (f_array k n) n.

Lemma f_array_ok (k:nat) n : FlexArray.Ok (f_array k n).
Proof.
 rewrite <- (N2Nat.id n). induction (N.to_nat n) as [|nn IH]; clear n.
 - easy.
 - rewrite Nat2N.inj_succ.
   unfold f_array. rewrite N.peano_rect_succ. fold (f_array k (N.of_nat nn)).
   now apply FlexArray.snoc_ok.
Qed.

Lemma f_array_size (k:nat) n : FlexArray.size (f_array k n) = N.succ n.
Proof.
 rewrite <- (N2Nat.id n). induction (N.to_nat n) as [|nn IH]; clear n.
 - easy.
 - rewrite Nat2N.inj_succ.
   unfold f_array. rewrite N.peano_rect_succ. fold (f_array k (N.of_nat nn)).
   rewrite FlexArray.snoc_size, IH; trivial.
   apply f_array_ok.
Qed.

Section AuxProofs.
Variable k:nat.
Variable n:nat.
Hypothesis Hyp : FlexArray.to_list (f_array k (N.of_nat n)) =
                 map N.of_nat (map (GenG.f (k - 1)) (seq 0 (S n))).
Lemma f_array_aux1 m :
  (m <= n)%nat ->
  FlexArray.get (f_array k (N.of_nat n)) (N.of_nat m)
   = N.of_nat (GenG.f (k-1) m).
Proof.
 intros Hm.
 rewrite FlexArray.get_to_list with (d:=0).
 2:{ apply f_array_ok. }
 2:{ rewrite f_array_size. lia. }
 rewrite Nat2N.id. rewrite Hyp.
 rewrite map_map, nth_map_indep with (d':=0%nat);
  rewrite ?seq_nth, ?seq_length; trivial; lia.
Qed.
Lemma f_array_aux2 p m :
  (m <= n)%nat ->
  (FlexArray.get (f_array k (N.of_nat n)) ^^p) (N.of_nat m)
    = N.of_nat (fs (k-1) p m).
Proof.
 revert m. induction p as [|p IH]; intros m Hm; try easy.
 simpl Nat.iter. rewrite IH; trivial.
 apply f_array_aux1. transitivity m. apply fs_le. lia.
Qed.
End AuxProofs.

Lemma f_array_spec (k:nat) n :
 k<>O ->
 FlexArray.to_list (f_array k n) =
 map N.of_nat (map (GenG.f (k-1)) (seq 0%nat (S (N.to_nat n)))).
Proof.
 intros Hk.
 rewrite <- (N2Nat.id n) at 1.
 induction (N.to_nat n) as [|nn IH]; clear n; try easy.
 rewrite Nat2N.inj_succ.
 unfold f_array. rewrite N.peano_rect_succ. fold (f_array k (N.of_nat nn)).
 rewrite FlexArray.snoc_to_list by apply f_array_ok.
 rewrite IH, (seq_S 0 (S nn)), !map_app. f_equal.
 simpl. f_equal. rewrite GenG.f_S.
 rewrite Nat2N.inj_sub, Nat2N.inj_succ. f_equal.
 replace (S (k-1)) with k by lia.
 now apply f_array_aux2.
Qed.

Lemma f_spec (k:nat) n :
 k<>O -> f k n = N.of_nat (GenG.f (k-1) (N.to_nat n)).
Proof.
 intros Hk. unfold f. rewrite <- (N2Nat.id n) at 1 2.
 apply f_array_aux1; trivial.
 rewrite N2Nat.id. now apply f_array_spec.
Qed.

Lemma f_alt q n : GenG.f q n = N.to_nat (f (S q) (N.of_nat n)).
Proof.
 rewrite (f_spec (S q)) by lia. simpl.
 now rewrite Nat.sub_0_r, !Nat2N.id.
Qed.

(** Fast computation of GenG.rchild *)

Definition rchild (k:nat)(n:N) :=
  let tf := f_array k n in
  n + (FlexArray.get tf ^^(k-1)) n.

Lemma rchild_spec k n :
 k<>O -> rchild k n = N.of_nat (GenG.rchild (k-1) (N.to_nat n)).
Proof.
 intros Hk.
 unfold rchild, GenG.rchild. rewrite Nat2N.inj_add, N2Nat.id. f_equal.
 rewrite <- f_array_aux2 with (n:=N.to_nat n); rewrite ?N2Nat.id; trivial.
 now apply f_array_spec.
Qed.

(** Tabulation of all pairs (m, rchild k m) for m <= n. *)

Definition rchild_array k n :=
  let tf := f_array k n in
  FlexArray.mapi (fun n m => (n, n + (FlexArray.get tf ^^(k-2)) m)) tf.

Lemma rchild_array_ok k n : FlexArray.Ok (rchild_array k n).
Proof.
 apply FlexArray.mapi_ok, f_array_ok.
Qed.

Lemma rchild_array_spec k n :
  (1 < k)%nat ->
  FlexArray.to_list (rchild_array k n) =
  map (fun m => (N.of_nat m, N.of_nat (GenG.rchild (k-1) m)))
      (seq 0%nat (S (N.to_nat n))).
Proof.
 intros Hk.
 unfold rchild_array. rewrite FlexArray.mapi_spec' by apply f_array_ok.
 rewrite f_array_size, N2Nat.inj_succ.
 apply map_ext_in. intros a. rewrite in_seq. intros Ha.
 f_equal.
 rewrite <- iter_S. replace (S (k-2)) with (k-1)%nat by lia.
 unfold GenG.rchild. rewrite Nat2N.inj_add. f_equal.
 rewrite <- f_array_aux2 with (n:=N.to_nat n); rewrite ?N2Nat.id; try lia.
 apply f_array_spec; lia.
Qed.
