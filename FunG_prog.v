(** * FunG_prog : Alternative definition of Hofstadter's G function *)

Require Import FunG.
Require Import Arith Lia Wf_nat List Program Program.Wf.
Set Implicit Arguments.

(** Same as [FunG.g_spec], but via the Program framework *)

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
 destruct (g_spec _) as (a,Ha).
 program_simpl.
 destruct (g_spec _) as (b,Hb).
 program_simpl.
 eapply GS; eauto. change (S n = S n - b + b).
 generalize (G_le Ha) (G_le Hb). lia.
Defined.

Definition g n := let (a,_) := g_spec n in a.

(*Eval lazy in g 55.*) (* Compute is very slow... *)

(*Recursive Extraction g.*) (* TODO: des let-in parasites *)

(** This is just an alternative presentation... *)

Lemma nothing_new n : g n = FunG.g n.
Proof.
 apply G_fun with n.
 unfold g. now destruct g_spec.
 apply FunG.g_correct.
Qed.
