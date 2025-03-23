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
