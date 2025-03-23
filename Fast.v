From Coq Require Import List Arith NArith Lia.
Require Import MoreFun MoreList.
Require FlexArray GenFib GenG.
Import ListNotations.
Local Open Scope N.

(** * Faster computation of [GenFib.A] and [GenG.f]

    For that, we use the binary numbers [N]
    and tabulate older values via a FlexArray (log access time). *)

Definition A (k n : N) :=
 let q := k-1 in
 let ones := N.iter q (FlexArray.cons 1) (FlexArray.singleton 1) in
 let stepA := fun t =>
   let m := FlexArray.get t 0 + FlexArray.get t q in
   FlexArray.tail_or_id (FlexArray.snoc t m)
 in
 FlexArray.get (N.iter n stepA ones) q.

Lemma A_spec k n : A k n = N.of_nat (GenFib.A (N.to_nat k) (N.to_nat n)).
Proof.
 revert k n.
 assert (H : forall k n, k<>0 ->
             A k n = N.of_nat (GenFib.A (N.to_nat k) (N.to_nat n))).
 { unfold A. intros k n Hk.
   set (ones := N.iter (k-1) _ _).
   set (stepA := fun t => _).
   set (A n := N.of_nat (GenFib.A (N.to_nat k) n)).
   set (A' n := if (n <? N.to_nat (k-1))%nat
                then 1 else A (n-N.to_nat (k-1))%nat).
   revert n.
   assert (OK0 : forall k',
           FlexArray.Ok (N.iter k'  (FlexArray.cons 1) (FlexArray.singleton 1))).
   { intros k'. rewrite N2Nat.inj_iter.
     induction (N.to_nat k'); simpl; trivial.
     now apply FlexArray.cons_ok. }
   assert (OK : forall n, FlexArray.Ok (N.iter n stepA ones)).
   { clear -OK0. intros n. rewrite N2Nat.inj_iter.
     induction (N.to_nat n); simpl.
     - apply OK0.
     - apply FlexArray.tail_or_id_ok, FlexArray.snoc_ok, IHn0. }
   assert (E : forall n, FlexArray.size (N.iter n stepA ones) = k).
   { clear - Hk OK0 OK. intros n'. rewrite <- (N2Nat.id n').
     induction (N.to_nat n') as [|n IH]. clear n'.
     - simpl. unfold ones. clear - Hk OK0.
       rewrite N2Nat.inj_iter.
       replace k with (N.succ (N.of_nat (N.to_nat (k-1)))) at 2 by lia.
       induction (N.to_nat (k-1)).
       + simpl; trivial.
       + simpl Nat.iter. rewrite FlexArray.cons_size, IHn. lia.
         rewrite Nat2N.inj_iter. apply OK0.
     - rewrite Nat2N.inj_succ, N.iter_succ.
       unfold stepA at 1.
       set (t := N.iter (N.of_nat n) _ _) in *.
       rewrite FlexArray.tail_or_id_size.
       rewrite FlexArray.snoc_size, IH. lia.
       apply OK. apply FlexArray.snoc_ok, OK. }
   assert (H : forall n,
              FlexArray.to_list (N.iter n stepA ones) =
              map A' (seq (N.to_nat n) (N.to_nat k)%nat)).
   { intros n'. rewrite <- (N2Nat.id n'), Nat2N.id.
     induction (N.to_nat n') as [|n IH]. clear n'.
     - simpl. unfold ones.
       rewrite map_ext_in with (g := fun _ => 1).
       2:{ intros a. rewrite in_seq. unfold A'. case Nat.ltb_spec; try lia.
           intros. replace (_-_)%nat with O by lia.
           unfold A. now rewrite GenFib.A_k_0. }
       rewrite N2Nat.inj_iter, N2Nat.inj_sub.
       change (N.to_nat 1) with 1%nat.
       replace (N.to_nat k) with (S (N.to_nat k -1)) at 2 by lia.
       clear - OK0.
       induction (N.to_nat k - 1)%nat; trivial.
       simpl. rewrite FlexArray.cons_to_list, IHn.
       2:{ rewrite Nat2N.inj_iter. apply OK0. }
       now rewrite <- seq_shift, map_map.
     - rewrite Nat2N.inj_succ, N.iter_succ.
       unfold stepA at 1.
       specialize (E (N.of_nat n)). specialize (OK (N.of_nat n)).
       set (t := N.iter (N.of_nat n) _ _) in *. clearbody t.
       clear - Hk t OK E IH.
       rewrite FlexArray.tail_or_id_spec.
       2:{ clear -OK. apply FlexArray.snoc_ok, OK. }
       2:{ rewrite FlexArray.snoc_size, E. lia. apply OK. }
       rewrite FlexArray.snoc_to_list, IH by apply OK.
       replace (N.to_nat k) with (S (N.to_nat k -1)) by lia.
       rewrite (seq_S (S n)), map_app. simpl. f_equal; f_equal.
       rewrite !FlexArray.get_to_list with (d:=0); try apply OK; try lia.
       rewrite IH.
       rewrite !nth_map_indep with (d':=O) by (rewrite seq_length; lia).
       rewrite !seq_nth by lia.
       clear IH E OK t.
       unfold A'. clear A'.
       rewrite Nat.add_0_r.
       repeat case Nat.ltb_spec; try lia;
         replace (S _-_)%nat with (S n) by lia.
       + intros. unfold A. rewrite !GenFib.A_base; lia.
       + intros. unfold A. rewrite GenFib.A_S.
         rewrite Nat2N.inj_add, N.add_comm. do 3 f_equal; lia. }
   clear OK0. intros n.
   rewrite FlexArray.get_to_list with (d:=0).
   2:{ apply OK. }
   2:{ rewrite E. lia. }
   rewrite H.
   clear - Hk.
   rewrite nth_map_indep with (d':=O) by (rewrite seq_length; lia).
   rewrite !seq_nth by lia. unfold A'. clear A'.
   case Nat.ltb_spec; try lia. intros. unfold A. f_equal. f_equal. lia. }
 intros k n. destruct (N.eq_dec k 0) as [->|K].
 - change (A 0 n) with (A 1 n). rewrite GenFib.A_0. now apply H.
 - now apply H.
Qed.

Lemma A_alt k n :
 GenFib.A k n = N.to_nat (A (N.of_nat k) (N.of_nat n)).
Proof.
 rewrite A_spec by lia. rewrite Nat2N.id. f_equal; lia.
Qed.


Definition f_array (k n:N) :=
 N.peano_rect _
  (FlexArray.singleton 0)
  (fun n t => FlexArray.snoc t (N.succ n - N.iter k (FlexArray.get t) n))
  n.

Definition f (k n:N) := FlexArray.get (f_array k n) n.

Lemma f_array_ok k n : FlexArray.Ok (f_array k n).
Proof.
 rewrite <- (N2Nat.id n). induction (N.to_nat n) as [|nn IH]; clear n.
 - easy.
 - rewrite Nat2N.inj_succ.
   unfold f_array. rewrite N.peano_rect_succ. fold (f_array k (N.of_nat nn)).
   now apply FlexArray.snoc_ok.
Qed.

Lemma f_array_size k n : FlexArray.size (f_array k n) = N.succ n.
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
Hypothesis Hyp : FlexArray.to_list (f_array (N.of_nat k) (N.of_nat n)) =
                 map N.of_nat (map (GenG.f k) (seq 0 (S n))).
Lemma f_array_aux1 m :
  (m <= n)%nat ->
  FlexArray.get (f_array (N.of_nat k) (N.of_nat n)) (N.of_nat m)
   = N.of_nat (GenG.f k m).
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
  (FlexArray.get (f_array (N.of_nat k) (N.of_nat n)) ^^p) (N.of_nat m)
    = N.of_nat (GenG.fs k p m).
Proof.
 revert m. induction p as [|p IH]; intros m Hm; try easy.
 simpl Nat.iter. rewrite IH; trivial.
 apply f_array_aux1. transitivity m. apply GenG.fs_le. lia.
Qed.
End AuxProofs.

Lemma f_array_spec k n :
 FlexArray.to_list (f_array k n) =
 map N.of_nat (map (GenG.f (N.to_nat k)) (seq 0%nat (S (N.to_nat n)))).
Proof.
 rewrite <- (N2Nat.id n) at 1.
 induction (N.to_nat n) as [|nn IH]; clear n; try easy.
 rewrite Nat2N.inj_succ.
 unfold f_array. rewrite N.peano_rect_succ. fold (f_array k (N.of_nat nn)).
 rewrite FlexArray.snoc_to_list by apply f_array_ok.
 rewrite IH, (seq_S 0 (S nn)), !map_app. f_equal.
 simpl. f_equal. rewrite GenG.f_S.
 rewrite Nat2N.inj_sub, Nat2N.inj_succ. f_equal.
 rewrite N2Nat.inj_iter.
 rewrite <- (N2Nat.id k) at 2.
 rewrite f_array_aux2; trivial. rewrite N2Nat.id. apply IH.
Qed.

Lemma f_spec k n :
 f k n = N.of_nat (GenG.f (N.to_nat k) (N.to_nat n)).
Proof.
 unfold f.
 rewrite <- (N2Nat.id n) at 1 2.
 rewrite <- (N2Nat.id k) at 1.
 apply f_array_aux1; trivial. rewrite !N2Nat.id. now apply f_array_spec.
Qed.

Lemma f_alt k n : GenG.f k n = N.to_nat (f (N.of_nat k) (N.of_nat n)).
Proof.
 rewrite f_spec. now rewrite !Nat2N.id.
Qed.

(** Faster computation of GenG.rchild *)

Definition rchild k n :=
  let tf := f_array k n in
  n + N.iter (k-1) (FlexArray.get tf) n.

Lemma rchild_spec k n :
 rchild k n = N.of_nat (GenG.rchild (N.to_nat k) (N.to_nat n)).
Proof.
 unfold rchild, GenG.rchild. rewrite Nat2N.inj_add, N2Nat.id. f_equal.
 rewrite N2Nat.inj_iter, N2Nat.inj_sub.
 rewrite <- f_array_aux2 with (n:=N.to_nat n); rewrite ?N2Nat.id; trivial.
 now apply f_array_spec.
Qed.

Lemma rchild_alt k n :
  GenG.rchild k n = N.to_nat (rchild (N.of_nat k) (N.of_nat n)).
Proof.
 rewrite rchild_spec. now rewrite !Nat2N.id.
Qed.

(** Tabulation of all pairs (m, rchild k m) for m <= n. *)

Definition rchild_array k n :=
  let tf := f_array k n in
  FlexArray.mapi (fun n m => (n, n + N.iter (k-2) (FlexArray.get tf) m)) tf.

Lemma rchild_array_ok k n : FlexArray.Ok (rchild_array k n).
Proof.
 apply FlexArray.mapi_ok, f_array_ok.
Qed.

Lemma rchild_array_spec k n :
  1 < k ->
  FlexArray.to_list (rchild_array k n) =
  map (fun m => (N.of_nat m, N.of_nat (GenG.rchild (N.to_nat k) m)))
      (seq 0%nat (S (N.to_nat n))).
Proof.
 intros Hk.
 unfold rchild_array. rewrite FlexArray.mapi_spec' by apply f_array_ok.
 rewrite f_array_size, N2Nat.inj_succ.
 apply map_ext_in. intros a. rewrite in_seq. intros Ha.
 f_equal.
 rewrite N2Nat.inj_iter, <- iter_S.
 unfold GenG.rchild. rewrite Nat2N.inj_add. f_equal.
 rewrite <- f_array_aux2 with (n:=N.to_nat n); rewrite ?N2Nat.id; try lia.
 f_equal. lia.
 apply f_array_spec; lia.
Qed.
