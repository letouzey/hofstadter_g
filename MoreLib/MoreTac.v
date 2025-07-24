From Coq Require Import Lia.

(** * General tactics *)

(** using lia as argument to a lemma *)

Notation lia := (ltac:(lia)) (only parsing).

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

