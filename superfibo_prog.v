
Require Import superfibo.
Require Import Arith Omega Wf_nat List Program Program.Wf.
Set Implicit Arguments.

(* Same as g_spec, but via the Program framework *)

Program Fixpoint g_spec n { measure n } : { r : nat | G n r } :=
 match n with
 | O => O
 | S n => S n - g_spec (g_spec n)
 end.
Next Obligation.
 destruct g_spec; simpl. apply le_n_S. now apply G_le.
Defined.
Next Obligation.
 program_simpl.
 destruct (g_spec n) as (a,Ha).
 program_simpl.
 destruct (g_spec a) as (b,Hb).
 program_simpl.
 eapply GS; eauto. change (S n = S n - b + b).
 generalize (G_le Ha) (G_le Hb). omega.
Defined.

Definition g n := let (a,_) := g_spec n in a.

Eval lazy in g 55. (* Compute is very slow... *)

Recursive Extraction g. (* TODO: des let-in parasites *)
