From Coq Require Import Lia.
Import PeanoNat BinNat BinPos BinInt.

(** * General tactics *)

(** using lia as argument to a lemma *)

Notation lia := (ltac:(lia)) (only parsing).

(** Lightweight destruct of a decidable statement *)

Class Decide3 (P Q : Prop) (b : bool) := Decide3_spec : BoolSpec P Q b.
Class Decide2 (P : Prop) (b : bool) := Decide2_spec : Bool.reflect P b.

#[global] Instance decide23 P b {D : Decide2 P b} : Decide3 P (~P) b :=
 match D with
 | Bool.ReflectT _ p => BoolSpecT _ p
 | Bool.ReflectF _ np => BoolSpecF _ np
 end.

#[global] Instance Dec2_nat_eq a b : Decide2 _ _ := Nat.eqb_spec a b.
#[global] Instance Dec3_nat_le a b : Decide3 _ _ _ | 5 := Nat.leb_spec a b.
#[global] Instance Dec3_nat_lt a b : Decide3 _ _ _ | 3 := Nat.ltb_spec a b.
#[global] Instance Dec2_N_eq a b : Decide2 _ _ := N.eqb_spec a b.
#[global] Instance Dec3_N_le a b : Decide3 _ _ _ | 5 := N.leb_spec a b.
#[global] Instance Dec3_N_lt a b : Decide3 _ _ _ | 3 := N.ltb_spec a b.
#[global] Instance Dec2_Pos_eq a b : Decide2 _ _ := Pos.eqb_spec a b.
#[global] Instance Dec3_Pos_le a b : Decide3 _ _ _ | 5 := Pos.leb_spec a b.
#[global] Instance Dec3_Pos_lt a b : Decide3 _ _ _ | 3 := Pos.ltb_spec a b.
#[global] Instance Dec2_Z_eq a b : Decide2 _ _ := Z.eqb_spec a b.
#[global] Instance Dec3_Z_le a b : Decide3 _ _ _ | 5 := Z.leb_spec a b.
#[global] Instance Dec3_Z_lt a b : Decide3 _ _ _ | 3 := Z.ltb_spec a b.

#[global] Instance Dec3_nat_even n : Decide3 (Nat.Even n) (Nat.Odd n) (Nat.even n).
Proof.
 assert (H := Nat.even_spec n).
 destruct (Nat.even n) eqn:E; constructor.
 - now rewrite <- H.
 - destruct (Nat.Even_or_Odd n); trivial. now rewrite <- H in *.
Qed.

#[global] Instance Dec3_nat_odd n : Decide3 (Nat.Odd n) (Nat.Even n) (Nat.odd n).
Proof.
 assert (H := Nat.odd_spec n).
 destruct (Nat.odd n) eqn:E; constructor.
 - now rewrite <- H.
 - destruct (Nat.Even_or_Odd n); trivial. now rewrite <- H in *.
Qed.

Definition decide P {Q} {b} {D : Decide3 P Q b} := D.
Definition decideb {P Q} b {D : Decide3 P Q b} := D.

Tactic Notation "if" constr(x) :=
 match type of x with
 | bool => destruct (decideb x)
 | _ => destruct (decide x)
 end.

Tactic Notation "if" constr(x) "as" simple_intropattern(pat) :=
 match type of x with
 | bool => destruct (decideb x) as pat
 | _ => destruct (decide x) as pat
 end.

(* TODO concerning this `if` tactic:
   - Issue with `if (S a + b <= ...)` which half-reduce the +
     to see it as `(a + b < ...)` but leave the + unfolded.
     Current fix : `if (S (a+b) <= ...)` or `if (a+b < ...)`.
   - Do not work when the goal is in Type.
   - Do not accept patterns like `if (n <=? _)` even if the context is clear.
     With that, it could become a alternative to `case Nat.eqb_spec` and alii.
   - Maybe add someday `if (a <> b)` ?
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

