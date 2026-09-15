From Coq Require Import Lia.
Import PeanoNat BinNat BinPos BinInt.

(** * General tactics *)

(** using lia as argument to a lemma *)

Notation lia := (ltac:(lia)) (only parsing).

(** Lightweight destruct of a decidable statement *)

Inductive BoolSpecType (P Q : Prop) : bool -> Set :=
  | BoolSpecTypeT : P -> BoolSpecType P Q true
  | BoolSpecTypeF : Q -> BoolSpecType P Q false.

Class Dec3 (P Q : Prop) (b : bool) := dec3 : BoolSpecType P Q b.
Class Dec3P (P Q : Prop) (b : bool) := dec3P : BoolSpec P Q b.
Class Dec2 (P : Prop) (b : bool) := dec2 : Bool.reflect P b.

#[global] Instance dec3P3 P Q b (D : Dec3P P Q b) : Dec3 P Q b.
Proof.
 destruct b; constructor; now inversion D.
Qed.

#[global] Instance dec23 P b (D : Dec2 P b) : Dec3 P (~P) b :=
 match D with
 | Bool.ReflectT _ p => BoolSpecTypeT _ _ p
 | Bool.ReflectF _ np => BoolSpecTypeF _ _ np
 end.

#[global] Typeclasses Opaque lt. (* avoid mixing a < b with S a <= b *)

#[global] Instance Dec2_nat_eq a b : Dec2 _ _ := Nat.eqb_spec a b.
#[global] Instance Dec3_nat_le a b : Dec3P _ _ _ := Nat.leb_spec a b.
#[global] Instance Dec3_nat_lt a b : Dec3P _ _ _ := Nat.ltb_spec a b.
#[global] Instance Dec2_N_eq a b : Dec2 _ _ := N.eqb_spec a b.
#[global] Instance Dec3_N_le a b : Dec3P _ _ _ := N.leb_spec a b.
#[global] Instance Dec3_N_lt a b : Dec3P _ _ _ := N.ltb_spec a b.
#[global] Instance Dec2_Pos_eq a b : Dec2 _ _ := Pos.eqb_spec a b.
#[global] Instance Dec3_Pos_le a b : Dec3P _ _ _ := Pos.leb_spec a b.
#[global] Instance Dec3_Pos_lt a b : Dec3P _ _ _ := Pos.ltb_spec a b.
#[global] Instance Dec2_Z_eq a b : Dec2 _ _ := Z.eqb_spec a b.
#[global] Instance Dec3_Z_le a b : Dec3P _ _ _ := Z.leb_spec a b.
#[global] Instance Dec3_Z_lt a b : Dec3P _ _ _ := Z.ltb_spec a b.

Lemma Nat_even_spec n : BoolSpec (Nat.Even n) (Nat.Odd n) (Nat.even n).
Proof.
 assert (H := Nat.even_spec n).
 destruct (Nat.even n) eqn:E; constructor.
 - now rewrite <- H.
 - destruct (Nat.Even_or_Odd n); trivial. now rewrite <- H in *.
Qed.

Lemma Nat_odd_spec n : BoolSpec (Nat.Odd n) (Nat.Even n) (Nat.odd n).
Proof.
 assert (H := Nat.odd_spec n).
 destruct (Nat.odd n) eqn:E; constructor.
 - now rewrite <- H.
 - destruct (Nat.Even_or_Odd n); trivial. now rewrite <- H in *.
Qed.

Lemma N_even_spec n : BoolSpec (N.Even n) (N.Odd n) (N.even n).
Proof.
 assert (H := N.even_spec n).
 destruct (N.even n) eqn:E; constructor.
 - now rewrite <- H.
 - destruct (N.Even_or_Odd n); trivial. now rewrite <- H in *.
Qed.

Lemma N_odd_spec n : BoolSpec (N.Odd n) (N.Even n) (N.odd n).
Proof.
 assert (H := N.odd_spec n).
 destruct (N.odd n) eqn:E; constructor.
 - now rewrite <- H.
 - destruct (N.Even_or_Odd n); trivial. now rewrite <- H in *.
Qed.

Lemma Z_even_spec n : BoolSpec (Z.Even n) (Z.Odd n) (Z.even n).
Proof.
 assert (H := Z.even_spec n).
 destruct (Z.even n) eqn:E; constructor.
 - now rewrite <- H.
 - destruct (Z.Even_or_Odd n); trivial. now rewrite <- H in *.
Qed.

Lemma Z_odd_spec n : BoolSpec (Z.Odd n) (Z.Even n) (Z.odd n).
Proof.
 assert (H := Z.odd_spec n).
 destruct (Z.odd n) eqn:E; constructor.
 - now rewrite <- H.
 - destruct (Z.Even_or_Odd n); trivial. now rewrite <- H in *.
Qed.

#[global] Instance Dec3_nat_even n : Dec3P _ _ _ := Nat_even_spec n.
#[global] Instance Dec3_nat_odd n : Dec3P _ _ _ := Nat_odd_spec n.
#[global] Instance Dec3_N_even n : Dec3P _ _ _ := N_even_spec n.
#[global] Instance Dec3_N_odd n : Dec3P _ _ _ := N_odd_spec n.
#[global] Instance Dec3_Z_even n : Dec3P _ _ _ := Z_even_spec n.
#[global] Instance Dec3_Z_odd n : Dec3P _ _ _ := Z_odd_spec n.

Definition decide P {Q b} {D : Dec3 P Q b} := D.
Definition decideb {P Q} b {D : Dec3 P Q b} := D.

(* Negations are handled manually, to avoid loops in type class resolution *)
Definition decide_neg P {Q b} {D : Dec3 P Q b} : Dec3 Q P (negb b).
Proof.
 destruct D; now constructor.
Qed.

Tactic Notation "if" constr(x) "as" simple_intropattern(pat) :=
 match type of x with
 | bool => destruct (decideb x) as pat
 | _ => match x with
        | not ?y => destruct (decide_neg y) as pat
        | _ => destruct (decide x) as pat
        end
 end.

Tactic Notation "if" constr(x) := if x as [?H|?H].

(* TODO concerning this `if` tactic:
   - Do not accept patterns like `if (n <=? _)` even if the context is clear.
     With that, it could become a alternative to `case Nat.eqb_spec` and alii.
*)

(** Sometimes in Coquelicot, ring/field do not recognize the type
    of the current equality to solve *)

Ltac fixeq ty := change (@eq _) with (@eq ty).

(** A bit of ssreflect's wlog (without loss of generality) *)

Ltac withoutloss a P :=
 match (eval pattern a in P) with ?P _ =>
 pattern a;
 match goal with
 | |- ?G _ =>
   revert a; assert (WL : forall a, P a -> G a); cbn beta in *; intros a
 end
 end.

Ltac withoutloss2 a b P :=
 match (eval pattern a,b in P) with ?P _ _ =>
 pattern a,b;
 match goal with
 | |- ?G _ _ =>
   revert a b; assert (WL : forall a b, P a b -> G a b); cbn beta in *;
   intros a b
 end
 end.

(** Pseudo variadic setoid_rewrite *)

Tactic Notation "srewrite" constr(x1) :=
  setoid_rewrite x1.
Tactic Notation "srewrite" constr(x1) constr(x2) :=
  setoid_rewrite x1; srewrite x2.
Tactic Notation "srewrite" constr(x1) constr(x2) constr(x3) :=
  setoid_rewrite x1; srewrite x2 x3.
Tactic Notation "srewrite" constr(x1) constr(x2) constr(x3) constr(x4) :=
  setoid_rewrite x1; srewrite x2 x3 x4.
Tactic Notation "srewrite" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) :=
  setoid_rewrite x1; srewrite x2 x3 x4 x5.
Tactic Notation "srewrite" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) constr(x6) :=
  setoid_rewrite x1; srewrite x2 x3 x4 x5 x6.
Tactic Notation "srewrite" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) constr(x6) constr(x7) :=
  setoid_rewrite x1; srewrite x2 x3 x4 x5 x6 x7.
Tactic Notation "srewrite" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) :=
  setoid_rewrite x1; srewrite x2 x3 x4 x5 x6 x7 x8.

Tactic Notation "srewrite" "<-" constr(x1) :=
  setoid_rewrite <- x1.
Tactic Notation "srewrite" "<-" constr(x1) constr(x2) :=
  setoid_rewrite <- x1; srewrite <- x2.
Tactic Notation "srewrite" "<-" constr(x1) constr(x2) constr(x3) :=
  setoid_rewrite <- x1; srewrite <- x2 x3.
Tactic Notation "srewrite" "<-" constr(x1) constr(x2) constr(x3) constr(x4) :=
  setoid_rewrite <- x1; srewrite <- x2 x3 x4.
Tactic Notation "srewrite" "<-" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) :=
  setoid_rewrite <- x1; srewrite <- x2 x3 x4 x5.
Tactic Notation "srewrite" "<-" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) constr(x6) :=
  setoid_rewrite <- x1; srewrite <- x2 x3 x4 x5 x6.
Tactic Notation "srewrite" "<-" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) constr(x6) constr(x7) :=
  setoid_rewrite <- x1; srewrite <- x2 x3 x4 x5 x6 x7.
Tactic Notation "srewrite" "<-" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) :=
  setoid_rewrite <- x1; srewrite <- x2 x3 x4 x5 x6 x7 x8.

