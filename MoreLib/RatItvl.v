From Coq Require Import ZArith Lia QArith Reals Lra Qreals.
From Hofstadter.HalfQuantum Require Import Complex.
Require Import Approx MoreReals MoreComplex.

(** * Interval arithmetic for safe approximations of reals and complexes.

    We use rational numbers with a fixed denominator,
    hence manipulate only Z numbers. *)

Local Open Scope Z.

(** The unique denominator used, and its suggested implementations *)

Module Type DenoSig.
 Parameter Inline deno : positive.
End DenoSig.

Module Deno12 <: DenoSig.
 Definition deno := Eval compute in (10^12)%positive.
End Deno12.

Module Deno30 <: DenoSig.
 Definition deno := Eval compute in (10^30)%positive.
End Deno30.

Module Make (Import D:DenoSig).

Definition t := prod Z Z.

Definition to_Q ab := (Qmake (fst ab) deno, Qmake (snd ab) deno).

Definition of_Z (a:Z) := let a' := a * Z.pos deno in (a',a').

Definition zero := (0,0).
Definition one := (Z.pos deno, Z.pos deno).

Definition reduce_lb a := a / Z.pos deno.
Definition reduce_ub a :=
  if (a mod Z.pos deno =? 0) then a / Z.pos deno else a / Z.pos deno + 1.

Definition Zmax4 a b c d := Z.max (Z.max a b) (Z.max c d).
Definition Zmin4 a b c d := Z.min (Z.min a b) (Z.min c d).

Definition opp '(a,b) := (Z.opp b, Z.opp a).
Definition add '(a,b) '(c,d) := (a+c, b+d).
Definition sub ab cd := add ab (opp cd).
Definition mul '(a,b) '(c,d) :=
  (reduce_lb (Zmin4 (a*c) (a*d) (b*c) (b*d)),
   reduce_ub (Zmax4 (a*c) (a*d) (b*c) (b*d))).
Definition scal_pos c '(a,b) := (c*a,c*b).
Definition max '(a,b) '(c,d) := (Z.max a c, Z.max b d).
Definition min '(a,b) '(c,d) := (Z.min a c, Z.min b d).

Definition abs '(a,b) :=
  (if (Z.sgn a =? -1) && (Z.sgn b =? 1) then 0 else Z.min (Z.abs a) (Z.abs b),
   Z.max (Z.abs a) (Z.abs b)).

Definition Ok (ab:t)(r:R) := Approx (fst (to_Q ab)) r (snd (to_Q ab)).

Lemma Ok_alt ab r :
  Ok ab r <-> (IZR (fst ab) <= r * IZR (Z.pos deno) <= IZR (snd ab))%R.
Proof.
 unfold Ok, to_Q, Approx, Q2R. destruct ab as (a,b). simpl.
 split; intros (H1,H2); split.
 - rewrite <- (Rmult_1_r (IZR a)), <- (Rinv_l (IZR (Z.pos deno))).
   2:{ apply IZR_nz. }
   rewrite <- Rmult_assoc. apply Rmult_le_compat_r; trivial.
   apply IZR_le; lia.
 - rewrite <- (Rmult_1_r (IZR b)), <- (Rinv_l (IZR (Z.pos deno))).
   2:{ apply IZR_nz. }
   rewrite <- Rmult_assoc. apply Rmult_le_compat_r; trivial.
   apply IZR_le; lia.
 - rewrite <- (Rmult_1_r r), <- (Rinv_r (IZR (Z.pos deno))) by apply IZR_nz.
   rewrite <- Rmult_assoc. apply Rmult_le_compat_r; trivial.
   apply Rlt_le, Rinv_0_lt_compat. now apply IZR_lt.
 - rewrite <- (Rmult_1_r r), <- (Rinv_r (IZR (Z.pos deno))) by apply IZR_nz.
   rewrite <- Rmult_assoc. apply Rmult_le_compat_r; trivial.
   apply Rlt_le, Rinv_0_lt_compat. now apply IZR_lt.
Qed.

Lemma zero_ok : Ok zero 0.
Proof.
 apply Ok_alt. simpl. lra.
Qed.

Lemma one_ok : Ok one 1.
Proof.
 apply Ok_alt. simpl. lra.
Qed.

Lemma of_Z_ok (a:Z) : Ok (of_Z a) (IZR a).
Proof.
 apply Ok_alt. unfold of_Z. simpl. rewrite mult_IZR. lra.
Qed.

Lemma opp_ok ab r : Ok ab r -> Ok (opp ab) (-r).
Proof.
 rewrite !Ok_alt. destruct ab as (a,b). simpl. rewrite !opp_IZR. lra.
Qed.

Lemma add_ok ab cd r r' : Ok ab r -> Ok cd r' -> Ok (add ab cd) (r+r').
Proof.
 rewrite !Ok_alt. destruct ab as (a,b), cd as (c,d). simpl.
 rewrite !plus_IZR. lra.
Qed.

Lemma sub_ok ab cd r r' : Ok ab r -> Ok cd r' -> Ok (sub ab cd) (r-r').
Proof.
 unfold sub. intros H1 H2. apply add_ok; trivial. apply opp_ok; trivial.
Qed.

Lemma scal_pos_ok c ab r : 0<=c -> Ok ab r -> Ok (scal_pos c ab) (IZR c * r).
Proof.
 rewrite !Ok_alt. destruct ab as (a,b). simpl. rewrite !mult_IZR.
 intros Hc H. rewrite Rmult_assoc.
 split; apply Rmult_le_compat_l; try apply IZR_le; easy.
Qed.

Lemma max_ok ab cd r r' : Ok ab r -> Ok cd r' -> Ok (max ab cd) (Rmax r r').
Proof.
 rewrite !Ok_alt. destruct ab as (a,b), cd as (c,d). simpl.
 intros (H1,H2) (H3,H4).
 split.
 - apply Z.max_case; eapply Rle_trans; eauto;
   apply Rmult_le_compat_r; try apply IZR_le; try easy;
   apply Rmax_l || apply Rmax_r.
 - apply Rmax_case; eapply Rle_trans; eauto; apply IZR_le; lia.
Qed.

Lemma min_ok ab cd r r' : Ok ab r -> Ok cd r' -> Ok (min ab cd) (Rmin r r').
Proof.
 rewrite !Ok_alt. destruct ab as (a,b), cd as (c,d). simpl.
 intros (H1,H2) (H3,H4).
 split.
 - apply Rmin_case; eapply Rle_trans; eauto; apply IZR_le; lia.
 - apply Z.min_case; eapply Rle_trans; eauto;
   apply Rmult_le_compat_r; try apply IZR_le; try easy;
   apply Rmin_l || apply Rmin_r.
Qed.

Lemma reduce_lb_ok a : reduce_lb a * Z.pos deno <= a.
Proof.
 unfold reduce_lb. rewrite Z.mul_comm. now apply Z.mul_div_le.
Qed.

Lemma reduce_ub_ok a : a <= reduce_ub a * Z.pos deno.
Proof.
 unfold reduce_ub.
 rewrite (Z.div_mod a (Z.pos deno)) at 1 by easy. rewrite Z.mul_comm.
 case Z.eqb_spec; intros E; try lia.
 rewrite Z.mul_add_distr_r. generalize (Z.mod_pos_bound a (Z.pos deno)). lia.
Qed.

Lemma mul_ok ab cd r r' : Ok ab r -> Ok cd r' -> Ok (mul ab cd) (r*r').
Proof.
 rewrite !Ok_alt. destruct ab as (a,b), cd as (c,d). simpl.
 intros H1 H2. set (t := IZR (Z.pos deno)) in *.
 split.
 - assert (H := Rmult_ge_lowerbound _ _ _ _ _ _ H1 H2).
   rewrite <- !mult_IZR in *.
   apply Rmult_le_reg_r with t. now apply IZR_lt.
   unfold t at 1. rewrite <- mult_IZR.
   eapply Rle_trans; [eapply IZR_le, reduce_lb_ok|].
   replace (r*r'*t*t)%R with ((r*t)*(r'*t))%R by ring.
   set (m := Zmin4 _ _ _ _).
   assert (IZR m <= IZR (a*c) /\ IZR m <= IZR (a*d) /\
           IZR m <= IZR (b*c) /\ IZR m <= IZR (b*d))%R; try lra.
   { repeat split; apply IZR_le; unfold m, Zmin4; lia. }
 - assert (H := Rmult_le_upperbound _ _ _ _ _ _ H1 H2).
   rewrite <- !mult_IZR in *.
   apply Rmult_le_reg_r with t. now apply IZR_lt.
   unfold t at 3. rewrite <- mult_IZR.
   eapply Rle_trans;[|eapply IZR_le, reduce_ub_ok].
   replace (r*r'*t*t)%R with ((r*t)*(r'*t))%R by ring.
   set (m := Zmax4 _ _ _ _).
   assert (IZR m >= IZR (a*c) /\ IZR m >= IZR (a*d) /\
           IZR m >= IZR (b*c) /\ IZR m >= IZR (b*d))%R; try lra.
   { repeat split; apply IZR_ge; unfold m, Zmax4; lia. }
Qed.

Lemma abs_ok ab r : Ok ab r -> Ok (abs ab) (Rabs r).
Proof.
 rewrite !Ok_alt. destruct ab as (a,b). simpl. intros H.
 rewrite <- (Rabs_pos_eq (IZR (Z.pos deno))) by now apply IZR_le.
 rewrite <- Rabs_mult. set (r' := (r * _)%R) in *. clearbody r'. clear r.
 destruct a as [|a|a]; simpl.
 - assert (0 <= b). { apply le_IZR. lra. }
   replace (Z.abs b) with b by lia.
   replace (Z.min 0 b) with 0 by lia.
   replace (Z.max 0 b) with b by lia.
   rewrite Rabs_pos_eq; lra.
 - assert (Z.pos a <= b). { apply le_IZR. lra. }
   replace (Z.abs b) with b by lia.
   rewrite Rabs_pos_eq.
   2:{ apply Rle_trans with (IZR (Z.pos a)); [now apply IZR_le|easy]. }
   split.
   + apply Rle_trans with (IZR (Z.pos a)); [apply IZR_le; lia|easy].
   + apply Rle_trans with (IZR b); [easy|apply IZR_le; lia].
 - destruct b as [|b|b]; simpl.
   + unfold Z.min; simpl. unfold Z.max; simpl.
     rewrite Rabs_left' by lra.
     replace (IZR (Z.pos a)) with (-IZR (Z.neg a))%R. lra.
     now rewrite <- opp_IZR.
   + split;[ apply Rabs_pos |].
     apply Rabs_le.
     rewrite <- opp_IZR, Z.opp_max_distr. simpl.
     split.
     * apply Rle_trans with (IZR (Z.neg a)); [apply IZR_le; lia | easy].
     * apply Rle_trans with (IZR (Z.pos b)); [easy | apply IZR_le; lia].
   + rewrite Rabs_left'.
     2:{ apply Rle_trans with (IZR (Z.neg b)); [easy|now apply IZR_le]. }
     split; apply Ropp_le_cancel; rewrite Ropp_involutive, <- opp_IZR.
     * rewrite Z.opp_min_distr; simpl.
       apply Rle_trans with (IZR (Z.neg b)); [easy|apply IZR_le; lia].
     * rewrite Z.opp_max_distr; simpl.
       apply Rle_trans with (IZR (Z.neg a)); [apply IZR_le; lia|easy].
Qed.

Lemma abs_pos ab : 0 <= fst (abs ab).
Proof.
 destruct ab as (a,b). simpl. destruct andb; lia.
Qed.

Module C.

Definition t := (prod Make.t Make.t).

Definition mul '(re1,im1) '(re2,im2) :=
  (sub (mul re1 re2) (mul im1 im2),
   add (mul re1 im2) (mul im1 re2)).

Definition abs '(re,im) :=
  let '(a,b) := abs re in
  let '(c,d) := abs im in
  (Z.sqrt (a*a + c*c), Z.sqrt_up (b*b + d*d)).

Definition Ok (abcd:t) (c:C) := Ok (fst abcd) (Re c) /\ Ok (snd abcd) (Im c).

Lemma mul_ok abcd abcd' z z' :
  Ok abcd z -> Ok abcd' z' -> Ok (mul abcd abcd') (z*z')%C.
Proof.
 unfold Ok.
 destruct abcd as (ab,cd), abcd' as (ab',cd'), z as (x,y), z' as (x',y').
 simpl. intros (H1,H2) (H3,H4).
 split.
 - apply sub_ok; apply mul_ok; trivial.
 - apply add_ok; apply mul_ok; trivial.
Qed.

Lemma abs_ok abcd z : Ok abcd z -> Make.Ok (abs abcd) (Cmod z).
Proof.
 unfold Ok. unfold Cmod. destruct z as (x,y).
 cbn -[abs pow].
 intros (Hx,Hy). apply abs_ok in Hx, Hy.
 rewrite <- !Rsqr_pow2, (Rsqr_abs x), (Rsqr_abs y).
 set (x' := Rabs x) in *.
 set (y' := Rabs y) in *.
 rewrite !Ok_alt in *.
 destruct abcd as (ab,cd). cbn -[Make.abs pow] in *.
 assert (Hx' := abs_pos ab).
 assert (Hy' := abs_pos cd).
 destruct (Make.abs ab) as (a',b').
 destruct (Make.abs cd) as (c',d').
 cbn -[pow] in *. clear ab cd.
 split.
 - apply Rsqr_incr_0.
   2:{ apply IZR_le. apply Z.sqrt_nonneg. }
   2:{ apply Rmult_le_pos. apply sqrt_pos. now apply IZR_le. }
   rewrite Rsqr_mult, Rsqr_sqrt.
   2:{ apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
   apply Rle_trans with (IZR (a'*a'+c'*c')).
   + unfold Rsqr. rewrite <- mult_IZR. apply IZR_le.
     apply Z.sqrt_le_square; try lia. apply Z.sqrt_nonneg.
   + unfold Rsqr. rewrite plus_IZR, !mult_IZR.
     set (t := IZR (Z.pos deno)) in *.
     replace (_ * (t*t))%R with ((x'*t)*(x'*t)+(y'*t)*(y'*t))%R by ring.
     apply Rplus_le_compat; apply Rmult_le_compat; now try apply IZR_le.
 - apply Rsqr_incr_0.
   2:{ apply Rmult_le_pos. apply sqrt_pos. now apply IZR_le. }
   2:{ apply IZR_le. apply Z.sqrt_up_nonneg. }
   rewrite Rsqr_mult, Rsqr_sqrt.
   2:{ apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
   apply Rle_trans with (IZR (b'*b'+d'*d')).
   + unfold Rsqr. rewrite plus_IZR, !mult_IZR.
     set (t := IZR (Z.pos deno)) in *.
     replace (_ * (t*t))%R with ((x'*t)*(x'*t)+(y'*t)*(y'*t))%R by ring.
     apply Rplus_le_compat; apply Rmult_le_compat; try easy;
       apply Rmult_le_pos; try apply Rabs_pos; now apply IZR_le.
   + unfold Rsqr. rewrite <- mult_IZR. apply IZR_le.
     apply Z.sqrt_sqrt_up_spec.
     apply Z.add_nonneg_nonneg; apply Z.square_nonneg.
Qed.

End C.
End Make.
