
(** A slow (but tail-rec) definition of Fibonacci, using only +1.
    Seen in a student's answer to an exam. *)

Require Import Arith Lia List Program Program.Wf.
Import ListNotations.
Open Scope list.

(** First, a standard definition of Fibonacci, as a reference.
    This one is also slow (redundant sub-calls), but it's simple. *)

Fixpoint fib (n:nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' => fib n' + fib n''
    end
  end.

Lemma fib_eqn n : fib (S (S n)) = fib (S n) + fib n.
Proof.
 reflexivity.
Qed.

Definition sumfib l :=
 List.fold_right (fun n r => fib n + r) 0 l.

Definition sumpowtwo l :=
 List.fold_right (fun n r => 2^n + r) 0 l.

(** The slow Fibonacci inner loop *)

Program Fixpoint f l acc { measure (sumpowtwo l) } :
 { r : nat | r = acc + sumfib l } :=
 match l with
 | [] => acc
 | 0::l => f l acc
 | 1::l => f l (S acc)
 | (S (S n))::l => f ((S n)::n::l) acc
 end.
Next Obligation.
 clear.
 change (sumpowtwo (1::l)) with (2 + sumpowtwo l). auto with arith.
Qed.
Next Obligation.
 destruct f as (r,->). simpl. auto with arith.
Qed.
Next Obligation.
 clear.
 change (sumpowtwo (S (S n)::l)) with (2*(2*2^n) + sumpowtwo l).
 assert (2^n <> 0) by now apply Nat.pow_nonzero.
 lia.
Qed.
Next Obligation.
 destruct f as (r,->). simpl. auto with arith.
Qed.

(** And finally : *)

Program Definition slowfibo n : nat := f [n] 0.

Compute slowfibo 10. (* 55 *)

Lemma slowfibo_eqn n : slowfibo n = fib n.
Proof.
 unfold slowfibo.
 destruct f as (r,->). simpl. auto with arith.
Qed.

Extract Inductive sigT => "(*)" ["(,)"].
Recursive Extraction slowfibo.
