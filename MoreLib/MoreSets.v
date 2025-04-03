From Coq Require Export Arith Lia List.
Require Import MoreTac MoreList DeltaList.
Import ListNotations.

(** * More on lists seen as finite sets

    allsubsets: enumerating all subsets of a list
    nsubsets: all subsets of a given size
    binom: binomial coefficients, i.e. length of nsubsets
*)

Fixpoint allsubsets {A} (l:list A) :=
 match l with
 | [] => [[]]
 | x::l' =>
   let ll := allsubsets l' in
   map (cons x) ll ++ ll
 end.

Fixpoint nsubsets {A} n (l:list A) :=
 match n, l with
 | O, _ => [[]]
 | S n', [] => []
 | S n', x::l' => map (cons x) (nsubsets n' l') ++ nsubsets n l'
 end.

Fixpoint binom n k :=
 match n, k with
 | _, 0 => 1
 | 0, _ => 0
 | S n', S k' => binom n' k' + binom n' k
 end.

Lemma nsubsets_filter {A} n (l:list A) :
  nsubsets n l = filter (fun s => length s =? n) (allsubsets l).
Proof.
 revert n. induction l; destruct n; simpl; trivial.
 - rewrite filter_app. rewrite <- (IHl O).
   rewrite map_filter, filter_nop by easy. now destruct l.
 - now rewrite filter_app, !IHl, map_filter.
Qed.

Lemma allsubsets_nat_spec (l:list nat) :
 Delta 1 l -> forall s, In s (allsubsets l) <-> incl s l /\ Delta 1 s.
Proof.
 induction l; intros D; simpl; intros s.
 - split.
   + now intros [<-|[]].
   + intros (IN,_). left. symmetry. now apply incl_l_nil.
 - rewrite in_app_iff. apply Delta_alt in D.
   rewrite in_map_iff, IHl by easy.
   setoid_rewrite IHl; [|easy].
   split.
   + intros [(s' & <- & IN & D')|(IN,D')]; split; trivial.
     * apply incl_cons. now left. now apply incl_tl.
     * rewrite Delta_alt. split; try easy.
       intros y Hy. apply D. now apply IN.
     * now apply incl_tl.
   + intros (IN,D').
     destruct s as [|a' s'].
     { right. split. apply incl_nil_l. constructor. }
     red in IN. simpl in IN. destruct (IN a'). { now left. }
     * left. exists s'. split; subst; trivial.
       rewrite Delta_alt in D'. split; try easy.
       intros y Hy. destruct (IN y); trivial. now right. apply D' in Hy; lia.
     * right. split; trivial. apply incl_cons; trivial.
       intros y Hy. destruct (IN y); try easy. now right.
       rewrite Delta_alt in D'. apply D' in Hy. apply D in H. lia.
Qed.

Lemma nsubsets_nat_spec n (l:list nat) :
 Delta 1 l ->
 forall s, In s (nsubsets n l) <-> incl s l /\ Delta 1 s /\ length s = n.
Proof.
 intros D s.
 rewrite nsubsets_filter.
 rewrite filter_In, Nat.eqb_eq, allsubsets_nat_spec by trivial. tauto.
Qed.

Lemma allsubsets_map {A B}(f:A->B)(l:list A) :
 allsubsets (map f l) = map (map f) (allsubsets l).
Proof.
 induction l; trivial. simpl. now rewrite map_app, IHl, !map_map.
Qed.

Lemma nsubsets_map {A B}(f:A->B) n (l:list A) :
 nsubsets n (map f l) = map (map f) (nsubsets n l).
Proof.
 revert n.
 induction l; destruct n; trivial.
 simpl. now rewrite map_app, !IHl, !map_map.
Qed.

Lemma allsubsets_via_nat {A} (l:list A) (d:A) :
  allsubsets l =
  map (map (fun i => nth i l d)) (allsubsets (seq 0 (length l))).
Proof.
 rewrite <- (map_nth_seq_id l d) at 1. now rewrite allsubsets_map.
Qed.

Lemma nsubsets_via_nat {A} n (l:list A) (d:A) :
  nsubsets n l =
  map (map (fun i => nth i l d)) (nsubsets n (seq 0 (length l))).
Proof.
 rewrite <- (map_nth_seq_id l d) at 1. now rewrite nsubsets_map.
Qed.

Lemma binom_one n : binom n 0 = 1.
Proof.
 now destruct n.
Qed.

Lemma binom_zero n k : n < k -> binom n k = 0.
Proof.
 revert k. induction n; destruct k; try easy.
 intros Hk. simpl. rewrite !IHn; lia.
Qed.

Lemma binom_diag n : binom n n = 1.
Proof.
 induction n. trivial. simpl. rewrite IHn, binom_zero; lia.
Qed.

Lemma nsubsets_binom {A} n k (l:list A) :
  length l = n -> length (nsubsets k l) = binom n k.
Proof.
 intros <-. revert k. induction l; destruct k; simpl; trivial.
 rewrite app_length, map_length. f_equal; apply IHl.
Qed.

Lemma nsubsets_empty {A} k (l:list A) :
  length l < k -> nsubsets k l = [].
Proof.
 intros H. apply binom_zero in H.
 rewrite <- (nsubsets_binom (length l) k l eq_refl) in H.
 now (destruct (nsubsets k l)).
Qed.

Lemma nsubsets_all {A} (l:list A) : nsubsets (length l) l = [l].
Proof.
 induction l; try easy.
 simpl. rewrite IHl, nsubsets_empty. easy. lia.
Qed.
