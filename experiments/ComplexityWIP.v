
(* Leftover / problematic parts in complexity study of kseq *)


(** Apparemment:
    n<>1 -> is_k0 n = true ->
    SuffixWords (kprefix k n) (kword k) -> False.

 decomps 5:[0;3] 7:[0;4] 10:[0;5] 14:[0;6] 18:[0;3;6]

0 -> 2
1 -> 20
2 -> 201
3 -> 2012

take 5 


1 5 7 10 14 18

1; 2 20 201 2012 20 201 2012
 2 20 201 2012


2    n=1, is_k0 n = true   n=A2 0
20
201
2012
20122   n=5 is_k0 n = true  pas un A2, mais pas un prefix-suffix non plus
201220
2012202   n=7 is_k0 n = true
20122020
201220201


u0 kprefix donc u finit par k u =u'k
et u = s(v) donc v finit par k-1, v = w.k-1
s(w.k-1) = s(v) = u'k
du coup s(w.k) = s(w).k0 = u0 et pas deux zero de suite donc wk prefix

Mais pas suffix...x

v'v est kword (p-1) qui finit donc par (k-1)



Il y a des kword finissant par k (un sur k+1)

2  --
20
201
2012  --
201220
201220201
2012202012012 --
2012202012012201220
2012202012012201220201220201
20122020120122012202012202012012202012012 --

prefix pas kword:

20122  (len 5)
2012202  (len 7)
20122020  (len 8)
2012202012  (len 10)
20122020120  (len 11)
201220201201  (len 12)

Via decomp_prefix_kseq ?

kword k p = someprefix ++ kwords l  avec l = rev (decomp k n)

et on peut choisir p et someprefix pas trop large:

word k p = kword k (p-1) ++ kword k (p-1-k), donc
si n <= A k (p-1-k) on continue avec celui-là et ainsi de suite



*)

Lemma kprefix_suffixwords_kword k n :
 k<>0 -> n<>0 -> SuffixWords (kprefix k n) (kword k) -> exists p, n = A k p.
Proof.
 intros K.
 induction n as [n IH] using lt_wf_ind.
 intros N.
 destruct (Nat.le_gt_cases n (S k)) as [H|H].
 - destruct n as [|n]; try easy. exists n. rewrite A_base; lia.
 - set (u := kprefix k n) in *.
   intros (p & u' & E).
   assert (P : S k <= p).
   { apply (A_le_inv k). rewrite A_base by lia.
     transitivity n; try lia.
     rewrite <- (kword_len k p), <- E, app_length. unfold u.
     rewrite kprefix_length. lia. }
   set (n' := length u').
   assert (N' : n' < A k p).
   { rewrite <- (@kword_len k p), <- E, app_length. unfold u.
     rewrite kprefix_length. lia. }
   generalize (@kseq_take_inv k n' K).
   unfold is_k0. rewrite (kseq_alt k n' p 0) by trivial.
   rewrite <- E, app_nth2 by lia. replace (n'-length u') with 0 by lia.
   unfold u. rewrite kprefix_alt, take_nth, kseq_k_0 by lia.
   case Nat.eqb_spec; try easy. intros _. rewrite Nat.add_0_r.
   assert (U' : u' = take n' (kseq k)).
   { change (PrefixSeq u' (kseq k)).
     eapply Prefix_PrefixSeq; eauto using kword_prefixseq.
     exists u. apply E. }
   rewrite <- U'. set (v' := take _ _). intros E'.
   destruct (ksubst_prefix_inv' k u K) as (v & w & Hv & Hw & EQ);
    try apply kprefix_ok.

enoncé renforcé ?

u prefix
u ou u.X suffixe avec X<>0

u'++u = kword k p  /  u'++u++X = kword k p
u' suivi par <> 0 donc exists v', u' = s(v'). et v' prefix

u'++u suivi par <> 0 dans les deux cas, donc exists w', u'++u = s(w)
et w' prefix donc v' prefix de w' donc exists v, w'=v'v

Bref, u' = s(v'), u = s(v), u'++u = s(v')++s(v)

u prefix donc exists w prefix tq. u=s(w) ou u=s(w)++k

Quatre cas:

a) u=s(w) et u'++u = kword k p
   donc w=v, v'++v = kword k (p-1) et v prefix et suffix :
   IH sans X donne v kword, u=s(v) aussi

b) u=s(w) et u'++u++X = kword k p
   v'++w++X-1 = kword k (p-1)
   SI X<>1, X-1<>0 et donc IH avec X-1: w est un kword, donc u aussi
   SI X=1 ?!

c) u=s(w)++k et u'++u = kword k p
   donc u=s(w++k-1) donc v = w++k-1
   donc v'++w++k-1 = kword k (p-1)
   * Si w++k-1 est prefix, IH sur (w++k-1) donne w++k-1 kword donc u kword
   * Si w++k-1 pas prefix ??
     IH sur w avec X=k-1

   MAIS ENSUITE ??

d) u=s(w)++k et u'++u++X = kword k p, alors
   kword k p finit par kX et X<>0 impossible !




---------------------------------------------------------

u'++u = kword k p
et u prefix

v'++v = kword k (p-1) ou idem sans derniere lettre
v prefix

--> soit à gauche, suffix v kword et on est bon
--> soit à droite:
      s(v')++s(v)++k = kword k p  (NB: possible, un sur trois qui finit par k)


      s(v'++v++k-1) = s(v')++s(v)++k = kword k p
      donc v'++v++k-1 = kword k (p-1)

      si v++k-1 est encore prefix, on retombe sur premier cas, IH
      si v++k-1 pas prefix:
        s(v)++k = u est prefix
        donc c'est v++k qui est prefix,
        et s(v++k) = s(v)+k++0 = u.0 est encore prefix

        au final s(v'++v++k) = u'++u++0 = kword k n ++ 0
        pas problematique en soit






   assert (V' : Prefix v' (kword k (p-1))).
   { unfold v'. rewrite <- kprefix_alt. apply kprefix_prefix_kword.
     rewrite <- f_A. apply f_mono; lia. }
   destruct V' as (v & V').
   rewrite E' in E. replace p with (S (p-1)) in E by lia.
   rewrite kword_S, <- V', apply_app in E.
   apply app_inv_head in E.
   set (m := length v).





   assert (V : v = kprefix k m).
   { rewrite kprefix_alt. change (PrefixSeq v (kseq k)).
     apply ksubst_prefix_inv; auto.
     - rewrite <- E. apply kprefix_ok.
     - rewrite <- E. unfold u. rewrite kprefix_length.
     admit. }
   assert (M : m <> 0).
   { intros ->. unfold kprefix in V. rewrite firstn_O in V. subst v.
     simpl in E. apply length_zero_iff_nil in E. unfold u in E.
     now rewrite kprefix_length in E. }
   destruct (IH m) as (q & Q).
   + rewrite <- (kprefix_length k). fold u. rewrite E, V, kprefix_alt.
     rewrite length_apply_ksubst.
     generalize (count_k_nz k m). lia.
   + trivial.
   + exists (p-1). rewrite <- V. now exists v'.
   + clear IH.
     exists (S q). rewrite <- (kprefix_length k n). fold u.
     now rewrite E, V, Q, kprefix_A_kword, <- kword_S, kword_len.
Admitted.

(*
NB: pourquoi pas restreindre v à [k] ?? et alors but = u kword

u++v  kprefix
u suffix (et donc ici aussi prefix)
v prefix donc commence par k<>0

donc u=s(u') et u' aussi prefix


fins possibles : v= ... k|0    avancer la barrière v'++k prefix
                 v= ... k|nz   v' = ... k-1
                 v= ..<>k|nz   v' = ... <>k-1


v=s(v') et v' prefix et suivant <>0
ou bien v=s(v')+k et suivant 0, avec v' prefix et v'++k prefix

u++v = s(u')++s(v') ou s(u')++s(v')++k

w++u=kword k p
w=s(w')
w'++u'=kword k (p-1), donc u' suffix ok

a) Si v=s(v') avec v' prefix
   s(u'++v')=u++v
   u++v suivi par 0 ?
   - si non, u'++v' kprefix, donc IH donne
     u' largest kword strictly below |u'+v'|
     donc u largest kword strictly below |u+v| A VERIFIER
   - si non, u++v suivi par 0
     u++v = s(t)k
     or = s(u'++v') donc v' = v''.k-1 et u++v=s(u'++v'')k
     Bref : IH sur u' v'' (tailles ?)

b) Si v=s(v')+k avec v' prefix et v'++k prefix
   s(u'++v')+k = u+v
   donc u'++v' prefix
   u' largest kword strictly below |u'++v'|


distinguo :
 - si u++v suivi par <>0
   alors u++v=s(w') et w' aussi prefix et a u' comme prefix
   donc exists v', w'=u'v' et s(v')=v

   * soit kprefix v suivi par <>0
     et alors v' aussi kprefix, IH sur u',v' ça devrait suivre
   * soit kprefix v suivi par 0 (ie v Right-Special)
     donc v' finit par (k-1)
    ET ENSUITE ?

 - si u++v suivi par 0
   alors u++v.0 = s(w') et w' aussi prefix et a donc u' comme prefix
   donc exists v', w'=u'v' et s(v')=v.0 (v et v' finissent par k)

   * soit kprefix v suivi par 0 et donc v.0 prefix
     donc v' aussi (pas deux 0 de suite) donc IH pour u',v'.0 (si tailles <)
     puis ça roule

   * soit kprefix v suivi par <> 0 (i.e. v Right-Special)
     soit v'' =  v'-last+(k-1)
     s(v'') = v et v'' prefix et s(u'v'') = uv

     SOUCI
*)


Lemma prevk_unique k q u v :
  u<>[] -> v<>[] -> u++v = kprefix k q ->
  SuffixWords u (kword k) -> PrefixSeq v (kseq k) ->
  k+2 <= q /\ u = prevkword k q.
Proof.
 revert u v. induction q as [q IH] using lt_wf_ind.
 intros u v Hu Hv E SU PR.
 destruct (Nat.lt_trichotomy q (k+2)) as [Hq|[Hq|Hq]].
 - (* q < k+2 *)
   exfalso. clear IH.
   destruct q.
   { unfold kprefix in E. rewrite firstn_O in E. now destruct u. }
   replace (kprefix k (S q)) with (kword k q) in *.
   2:{ eapply PrefixSeq_unique; eauto using kword_prefixseq, kprefix_ok.
       rewrite kprefix_length, kword_len, A_base; lia. }
   rewrite kword_low in E by lia.
   destruct u as [|a u]; try easy. clear Hu. injection E as -> E.
   assert (F : firstn 1 v = [k]).
   { rewrite PR, firstn_take. easy. destruct v; simpl. easy. lia. }
   destruct v as [|a v]; try easy. simpl in F. injection F as ->.
   assert (In k (seq 0 q)).
   { rewrite <- E, in_app_iff. simpl. now (right; left). }
   rewrite in_seq in *; lia.
 - (* q = k+2 *)
   clear IH. split; [lia| ].
   rewrite prevkword_low by lia.
   replace (kprefix k q) with (kword k (S k)) in E.
   2:{ subst q.
       eapply PrefixSeq_unique; eauto using kword_prefixseq, kprefix_ok.
       rewrite kprefix_length, kword_len, A_base; lia. }
   rewrite kword_alt, Nat.sub_diag, !kword_low in * by lia.
   simpl in E.
   destruct u as [|a u]; try easy. injection E as -> E. clear Hu.
   assert (F : firstn 1 v = [k]).
   { rewrite PR, firstn_take. easy. destruct v; simpl. easy. lia. }
   destruct v as [|a v]; try easy. simpl in F. injection F as ->. clear Hv.
   assert (L : length (u++k::v) = S k).
   { unfold letter in *; rewrite E, app_length, seq_length; simpl; lia. }
   rewrite app_length in L. simpl in L.
   rewrite <- (firstn_skipn (length u) (seq 0 k)) in E.
   rewrite <- app_assoc in E.
   apply app_inv in E.
   2:{ rewrite firstn_length_le; rewrite ?seq_length; lia. }
   destruct E as (Eu,Ev).
   rewrite firstn_seq in Eu by lia.
   rewrite skipn_seq in Ev.
   destruct (k-length u) eqn:E.
   + simpl in Ev. injection Ev as ->.
     replace (length u) with (q-2) in Eu by lia. now f_equal.
   + injection Ev as Ev _. lia.
 - (* q > k+2 *)
   split; [lia|].
   destruct (Nat.eq_dec (length v) 1) as [EQ|NE].
   + replace v with [k] in *.
     2:{ eapply PrefixSeq_unique; eauto. rewrite <- kword_0.
         apply kword_prefixseq. }
     clear Hv PR EQ IH.
     (* length u = q-1 est un Ak, tout va bien *)
     admit.
   + set (v' := firstn (length v - 1) v).
     rewrite <- length_zero_iff_nil in Hv.
     assert (Hq' : q-1 < q) by lia.
     destruct (IH (q-1) Hq' u v') as (Q & U); clear IH; auto.
     * rewrite <- length_zero_iff_nil. unfold v'.
       rewrite firstn_length_le; lia.
     * unfold v'. rewrite <- firstn_app_2, E, !kprefix_alt.
       replace (_+_) with (length u + length v -1) by lia.
       rewrite <- app_length, E, kprefix_length.
       rewrite firstn_take; auto; lia.
     * red. unfold v'. rewrite PR at 2.
       rewrite firstn_take by lia.
       rewrite firstn_length_le; auto; lia.
     * destruct (invA_low_pred k q).
       { subst u. unfold prevkword in *. now f_equal. }
       { exfalso.
         apply (f_equal (@length nat)) in E.
         rewrite app_length, kprefix_length in E.
         rewrite U in E. unfold prevkword in E. rewrite kword_len in E.
         set (p := invA_low k (q-1)) in *.
         assert (A k p + 2 <= q) by lia.
         assert (Z : q = S (A k (invA_low k q)))
          by (apply invA_low_nonflat; lia). rewrite H in Z.
         admit. (* OUPS Probleme *)
       }
Admitted.



(* GENERATION DES FACTEURS PAR LEFT-EXTENSION ?? PAS SIMPLE

left-ext de 0 : 20
left-ext de 1 : 01
left-ext de 2 : 02,12,22

2 / / 0 1
02 12 22 / / 20 01

20 / 22 / 01 02 / 12
020 120 220 / 122 / 201 202 012

201 / 220 202 / 012 020 / 120 122
0201 1201 2201 / 1220 2202 / 2012 2020 / 0120 0122

2012 / 2201 2202 2020 / 0120 0122 0201 / 1201 1220
02012 12012 22012 / 12201 12202 22020 / 20120 20122 20201 01201 01220

20122 / 20120 20201 22012 22020 / 01201 01220 02012 / 12012 12201 12202
020122 120122 220122 / 020120 220201 122012 122020 / 201201 201220 202012 /
  012012 012201 012202

201220 / 201201 202012 220122 220201 / 012012 012201 012202 020120 020122 /
   120122 122012 122020

si a,b,c facteurs commençant par 2,0,1
alors a-1 inconnus (left-ext d'un 2xyz)
 mais au moins : 1+b commençant par 2 / 1+c commençant par 0 / 1 comm par 2



Comment trouver l'extension gauche d'un 2xyz, même quand on sait qu'elle
est unique (car 2xyz pas prefix du mot infini) ?
Parfois virer la dernière lettre et regarder ce qui s'est passé au coup
d'avant suffit (lorsque 2xyz diffère de kprefix pas seulement à la fin)
En fait on peut même virer plus de lettres parfois (tant qu'on a une
différence avec kprefix. P.ex. 20201 suffit de regarder left-ext de 202 =2
donc 220201)

Exemples problématique: 22 202 20120
 Cela vient après des moments où prefix est BiSpecial (sinon une seule
 ext droite)

Bref, facteur uZ avec u = prefix mais uZ pas prefix
on cherche X tq XuZ facteur.  donc u commence par k

Déjà, occurence de uZ n'est pas tout au début du mot infini (sinon prefix)
donc X existe dès la première occurence de uZ

Algorithmiquement : lookup dans mot infini.
Borne sur son apparition ?
*)



Lemma filter_remove (l : list word) u :
  filter (fun v => negb (listnat_eqb u v)) l
  = remove (list_eq_dec Nat.eq_dec) u l.
Proof.
 induction l; simpl; auto.
 case listnat_eqb_spec; simpl;
 destruct list_eq_dec; simpl; try easy. intros. f_equal; auto.
Qed.

Lemma remove_nodup_in_length {A}(dec: forall (a b : A), {a=b}+{a<>b}) l x :
 NoDup l -> In x l -> S (length (remove dec x l)) = length l.
Proof.
 induction l.
 - inversion 2.
 - inversion_clear 1. simpl. intros [<-|IN].
   + destruct dec; try easy. f_equal. f_equal. now apply notin_remove.
   + f_equal. destruct dec. now subst. simpl. now apply IHl.
Qed.


(* CI-DESSOUS, allsuffixes_extend_inv FAUX FINALEMENT.
   Contreexemple:
Compute allsuffixes 2 5.
(* p.ex. 1201++2 alors que 1201 n'est pas suffixe. Donc KO *)

Lemma allsuffixes_extend_inv k p q u :
 In (u ++ kword k q) (allsuffixes k (p + A k q)) ->
 In u (allsuffixes k p).
Proof.
 revert q u.
 induction p as [p IH] using lt_wf_ind.
 intros q u H.
 assert (P : length u = p).
 { rewrite allsuffixes_spec in *. destruct H as (E,_).
   rewrite app_length, kword_len in *. lia. }
 destruct (Nat.le_gt_cases p (A k (q+k))).
 - rewrite allsuffixes_spec in *. destruct H as (_,(n,H)).
   split; trivial.
   admit.
(*
   (* q = n mod S k et même ici n = q + x*(S k) *)
*)

 - set (p' := p - A k (q+k)).
   assert (E := firstn_skipn p' u).
   set (u' := firstn p' u) in *.
   replace (skipn p' u) with (kword k (q+k)) in E.
   2:{ admit. }
   assert (LT : p' < p).
   { unfold p'. generalize (A_nz k (q+k)). lia. }
   specialize (IH p' LT (S (q+k)) u').
   rewrite kword_alt in IH by lia. simpl A in IH.
   replace (q+k-k) with q in IH by lia.
   rewrite Nat.add_assoc in IH.
   replace (p'+A k (q+k)) with p in IH by lia.
   rewrite app_assoc, E in IH.
   specialize (IH H).
   rewrite <- E.
   rewrite allsuffixes_spec in IH. destruct IH as (P',(n & v' & N)).
   rewrite allsuffixes_spec.
   split.
   + now rewrite <- P, <- E, app_length, kword_len.
   + admit.
Admitted.
(* il faudrait (Suffix u' (kword k (q+2*k))
   du coup   (Suffix (u'++kword k (q+k)) (kword k (q+2k) ++ kword k (q+k)))
             (Suffix (u'++kword k (q+k)) (kword k (q+2k+1)))
   et on est bon...

   p' = p - A k (q+k)

 *)
*)

(*----------------------------------------------------------*)



(* WIP: existence de (kprefix k n) ne finissant pas par k et t.q.
   (kprefix k n ++ [k]) est encore facteur mais <> kprefix k (n+1)).
   Autrement dit, (kprefix k n) BiSpecial.
   Mais ces (prefix k n ++ [k]) ont tous klvalence 1.

Definition test k l := wordmem (l++[k]) (kfactors0opt k (S (length l))).

Definition moretest k n :=
  let w := kprefix k (S n) in
  if last w 0 =? k then false
  else
    let w' := removelast w in
    if last w' 0 =? k then false
    else test k w'.

Compute filter (moretest 4) (seq 2 500).
(*     = [2; 3; 4; 28; 37; 49; 273; 362; 480] *)

Compute (kprefix 2 15).
(*     = [2; 0; 1; 2; 2; 0; 2; 0; 1; 2; 0; 1; 2; 2; 0] *)
(* k=2 : 2;15;75;352 sont suffix les uns des autres *)

Compute filter (moretest 3) (seq 2 500).
(*     = [2; 3; 21; 29; 152; 210] *)

Compute map (kprefix 3) [2; 3; 21; 29; 152; 210].
(* k=3 suffix imbriqués un sur deux : 2 21 152 vs 3 29 210 *)

Compute listnat_eqb (lastn 28 (kprefix 4 273)) (kprefix 4 28).
(*       = [2; 0; 1; 2; 2; 0; 2; 0; 1; 2; 0; 1; 2; 2; 0] *)


Compute let k:=2 in map (fun n => kleftexts k (kprefix k n++[k]))
                        (filter (moretest k) (seq 2 500)).
(*      = [[2]; [0]; [1]; [2]] *)

Compute let k:=3 in map (fun n => kleftexts k (kprefix k n++[k]))
                        (filter (moretest k) (seq 2 500)).
(*      = [[3]; [0]; [1]; [2]; [3]; [0]] *)

Compute let k:=4 in map (fun n => kleftexts k (kprefix k n++[k]))
                        (filter (moretest k) (seq 2 500)).
(*     = [[4]; [0]; [1]; [2]; [3]; [4]; [0]; [1]; [2]] *)


Compute map (fun n => kleftexts 5 (kprefix 5 n++[5])) [2; 3; 4; 5; 36; 46; 59; 76; 450].
(*     = [[5]; [0]; [1]; [2]; [3]; [4]; [5]; [0]; [1]] *)



Compute kprefix 2 76.

Compute kleftexts 2 (kprefix 2 75 ++ [2]).


Compute test 3 [3;0;1;2;3;3;0;3;0;1;3;0;1;2;3;0;1;2].

Compute kleftexts 3 [3;0;1;3].
*)

(*----------------------------------------------*)

(* /!\ Problem with the last line of Lemma 3.7 : \tilde{p} = p cannot
   be obtained in general, since (ii) needs last letter to be different
   from k. Probably no big deal, since eventually the only LS words
   (the kprefix) have klvalence (S k), hence the same for their image
   by ksubst. But is this precise part of Lemma 3.7 reused in the rest
   of the article / corrigendum ??
*)

Lemma lemma_3_7_i_all k u l :
  2 <= length l ->
  AllLeftExts l u (kseq k) ->
  AllLeftExts (map (next_letter k) l) (apply (ksubst k) u) (kseq k).
Proof.
 intros Hl (ND,A).
 split.
 - apply NoDup_map_inv with (f:=prev_letter k).
   rewrite map_map, map_ext_in with (g:=id), map_id; auto.
   intros a Ha. apply prev_next_letter. rewrite A in Ha.
   now apply LeftExt_letter in Ha.
 - destruct (Nat.eq_dec (length u) 0) as [L|L].
   { rewrite length_zero_iff_nil in L. subst u.
     simpl in *. unfold LeftExt in *.
     intros a. rewrite <- all_letters_subseq in *.
     rewrite in_map_iff. split.
     - intros (a' & <- & Ha'). rewrite A, <- all_letters_subseq in Ha'.
       now apply next_letter_le.
     - intros Ha. exists (prev_letter k a). split.
       + now apply next_prev_letter.
       + rewrite A. now apply all_letters_subseq, prev_letter_le. }
   destruct (Nat.eq_dec (length u) 1) as [L'|L'].
   { destruct u as [|x [|y l']]; simpl in L'; try lia. clear L L'.
     intros a.
     simpl. unfold ksubst.
     case Nat.eqb_spec; intros X; subst; simpl.
     - rewrite in_map_iff. split.
       + intros (a' & <- & Ha'). unfold letter.
         replace [k;0] with (kprefix k 2).
         2:{ rewrite kprefix_alt. unfold take. simpl.
             now rewrite kseq_k_0, kseq_k_1. }
         apply kprefix_leftext, next_letter_le.
         apply A in Ha'. now apply LeftExt_letter in Ha'.
       + intros Ha. apply LeftExt_letter in Ha.
         exists (prev_letter k a). split. now apply next_prev_letter.
         apply A. unfold letter.
         replace [k] with (kprefix k 1).
         2:{ rewrite kprefix_alt. unfold take. simpl.
             now rewrite kseq_k_0. }
         now apply kprefix_leftext, prev_letter_le.
     - exfalso. clear a.
       assert (forall a, In a l -> a = prev_letter k x).
       { intros a. rewrite A. clear A.
         unfold LeftExt, SubSeq, subseq. simpl.
         intros (p & [= E E']).
         replace p with (S p - 1) in E by lia.
         rewrite kseq_prev_letter in E by lia. now rewrite <- E' in E. }
       destruct l as [|a [|b l']]; simpl in Hl; try lia.
       assert (a = b).
       { rewrite (H a), (H b); simpl; intuition. }
       inversion_clear ND. simpl in *; intuition. }
   intro a. rewrite in_map_iff. split.
   + intros (a' & <- & IN). apply lemma_3_7_i. now apply A.
   + intros Ha. exists (prev_letter k a). split.
     apply next_prev_letter. eapply LeftExt_letter; eauto.
     rewrite A.
     set (v := apply (ksubst k) u) in *.
     assert (Hv : hd 0 v <> 0).
     { admit. }
     destruct (Nat.eq_dec (last v 0) k) as [Hv'|Hv'].
     * (* v <> [] --> removelast v exists *)
       (* last u 0 = k-1 *)
       (* last last u = k-2 *)
       (* last (removelast v) <> k *)
       (* ksubst (removelast v) = removelast u *)
       (* leftext a (removelast v)
          exist u', ksubst u' = removelast v et
          leftext a u'
          u' = removelast u

          Bref leftext a (removelast u)
          et ensuite ?? *)
        admit.

     * destruct (lemma_3_7_ii_aux k v a Hv Hv' Ha) as (u' & Hu' & Ha').
       replace u' with u in * by (now apply ksubst_inv in Hu').
       auto.
Admitted.


(*----------------------------------------------*)

(** INFINITE LEFT SPECIAL : could be skipped if MaxLeftSpecial part is OK *)

Definition InfiniteLeftSpecial (f g : sequence) :=
 forall u, PrefixSeq u f -> LeftSpecial u g.

Lemma remark_3_6 k : k<>0 -> InfiniteLeftSpecial (kseq k) (kseq k).
Proof.
 intros Hk u Hu. red in Hu. rewrite <- kprefix_alt in Hu. rewrite Hu.
 rewrite ls_val. rewrite kprefix_klvalence. lia.
Qed.

Definition StrictPrefix {A} (u v : list A) := Prefix u v /\ u<>v.

Definition limword (f : nat -> word) : sequence :=
  fun (n:nat) => nth n (f (S n)) 0.

Lemma limword_ok (f : nat -> word) :
 (forall n, StrictPrefix (f n) (f (S n))) ->
 forall n, PrefixSeq (f n) (limword f).
Proof.
 intros P n. red. symmetry. apply take_carac; trivial.
 intros m a H. rewrite nth_indep with (d':=0) by trivial.
 unfold limword.
 assert (L : forall n, n <= length (f n)).
 { clear - P. induction n; try lia.
   apply Nat.le_lt_trans with (length (f n)); try lia.
   destruct (P n) as ((u,<-),NE). rewrite app_length.
   destruct u. now rewrite app_nil_r in NE. simpl; lia. }
 assert (P' : forall p q , p <= q -> Prefix (f p) (f q)).
 { induction 1. apply Prefix_id. eapply Prefix_trans; eauto. apply P. }
 destruct (Nat.le_ge_cases n (S m)) as [LE|GE].
 - apply P' in LE. rewrite Prefix_nth in LE. now apply LE.
 - apply P' in GE. rewrite Prefix_nth in GE. symmetry. apply GE. apply L.
Qed.

Lemma limword_unique (f : nat -> word) (g : sequence) :
 (forall n, StrictPrefix (f n) (f (S n))) ->
 (forall n, PrefixSeq (f n) g) ->
 forall n, g n = limword f n.
Proof.
 intros P PR n.
 assert (L : forall n, n <= length (f n)).
 { clear - P. induction n; try lia.
   apply Nat.le_lt_trans with (length (f n)); try lia.
   destruct (P n) as ((u,<-),NE). rewrite app_length.
   destruct u. now rewrite app_nil_r in NE. simpl; lia. }
 specialize (PR (S n)).
 assert (PR' := limword_ok f P (S n)).
 unfold PrefixSeq in *.
 rewrite <- (take_nth g (length (f (S n))) n 0) by apply L.
 rewrite <- PR, PR'. apply take_nth. apply L.
Qed.

Definition nextnonk k (f:sequence) n :=
 if Nat.eqb (f n) k then if Nat.eqb (f (S n)) k then S (S n) else S n else n.

Lemma nextnonk_spec1 k f n : n <= nextnonk k f n <= n+2.
Proof.
 unfold nextnonk; repeat case Nat.eqb_spec; lia.
Qed.

Lemma nextnonk_spec2 k f :
  k<>0 -> InfiniteLeftSpecial f (kseq k) -> forall n, f (nextnonk k f n) <> k.
Proof.
 intros K H n.
 unfold nextnonk. repeat case Nat.eqb_spec; try lia.
 intros E2 E1 E3.
 specialize (H (take (S (S (S n))) f)). unfold PrefixSeq in H.
 rewrite take_length in H. specialize (H eq_refl).
 apply LeftSpecial_SubSeq in H.
 rewrite !take_S, <- !app_assoc, E1, E2, E3 in H. simpl in H.
 eapply Sub_SubSeq in H; [|apply Sub_app_l, Sub_id].
 apply (lemma_4_5_ter k 3) in H; lia.
Qed.

Fixpoint iternext (next:nat->nat) n :=
 match n with
 | 0 => next 0
 | S n => next (S (iternext next n))
 end.

Lemma iternext_incr next :
  (forall n, n <= next n) -> forall n, iternext next n < iternext next (S n).
Proof.
 intros H n. simpl. apply (H (S (iternext next n))).
Qed.

Lemma iternext_spec next (P:nat -> Prop) :
  (forall n, P (next n)) -> (forall n, P (iternext next n)).
Proof.
 induction n; simpl; auto.
Qed.

Lemma StrictPrefix_take {A} (w : nat -> A) n m :
  n < m -> StrictPrefix (take n w) (take m w).
Proof.
 intros H; split. apply Prefix_take; lia.
 intros E. apply (f_equal (@length _)) in E. rewrite !take_length in E; lia.
Qed.

Lemma StrictPrefix_len {A} (u v : list A) :
  StrictPrefix u v -> length u < length v.
Proof.
 intros (P,N).
 assert (length u <> length v).
 { contradict N. now rewrite Prefix_equiv, N, firstn_all in P. }
 apply Prefix_len in P. lia.
Qed.

Lemma before_0_is_k k u v :
  u<>[] -> v<>[] -> SubSeq (u++v) (kseq k) -> hd 0 v = 0 -> last u 0 = k.
Proof.
 intros U V (q, SU) H.
 destruct v as [|x v]; try easy. simpl in *. subst. clear V.
 rewrite (app_removelast_last 0 U) in SU.
 unfold letter in *.
 set (u' := removelast u) in *. rewrite <- app_assoc, app_length in SU.
 simpl in SU. unfold subseq in SU. rewrite seq_app, map_app in SU.
 simpl in SU. apply app_inv in SU.
 2:{ now rewrite map_length, seq_length. }
 destruct SU as (_,[= E1 E2 _]).
 symmetry in E2. apply k0_pred_k in E2. simpl in E2. lia.
Qed.

(* Note : SubSeq (apply (ksubst k) u) (kseq k) doesn't imply
   SubSeq u (kseq k). Counterexemple: u=[k-1;k-1] not a factor but
   its substitution [k;k] is. *)

(* Note: hypothesis (last u 0 <> k) is mandatory below.
   Counter-example otherwise: Prefix [k] [k;0] but ~Prefix [k-1] [k].

   TODO: hypothesis (last u' 0 <> k) could be removed below.
   If last u' = k, then u'0 or u'k0 factors.

a) v' finit forcément par (k-1), soit v'' la fin changée en k, s(v'') = u'0
   on obtient Prefix v v''. Si prefix strict on est bon.
   Si égalité v=v'' alors s(v)=s(v'')=u'0 qui ne peut être prefix de u'

b) on applique thm avant sur u (u'k0) v v'k.
   on obtient Prefix v (v'k). Si Prefix strict on est bon.
   Si égalité v=v'k alors s(v)=u'k0 ne peut être prefix de u'
*)

Lemma Prefix_ksubst_inv k u u' v v' :
  last u 0 <> k ->
  last u' 0 <> k ->
  SubSeq u' (kseq k) ->
  u = apply (ksubst k) v ->
  u' = apply (ksubst k) v' ->
  Prefix u u' -> Prefix v v'.
Proof.
 intros L L' SU E E' (u2 & E2).
 destruct (listnat_eqb_spec u []) as [->|N].
 { change [] with (apply (ksubst k) []) in E. apply ksubst_inv in E.
   subst v. now exists v'. }
 destruct (listnat_eqb_spec u2 []) as [->|N2].
 { exists []. rewrite app_nil_r in *. apply (ksubst_inv k).
   now rewrite <- E, <- E', <- E2. }
 destruct (lemma_3_7_ii_cor k u2) as (v2 & V2 & S2).
 - clear v v' E E'. intros E. apply L. eapply before_0_is_k; eauto.
   unfold letter in *. now rewrite E2.
 - rewrite <- (last_app u u2), E2; trivial.
 - eapply Sub_SubSeq; eauto. eapply Suffix_Sub. now exists u.
 - exists v2. apply (ksubst_inv k). now rewrite apply_app, <- E, <- E', V2.
Qed.

(** Here, we assume FunctionalChoice (for the moment ?).
    This avoid having to find "sig" versions of many lemmas before. *)
Require ChoiceFacts.
Axiom choice : ChoiceFacts.FunctionalChoice.

Lemma proposition_3_8 k f :
  InfiniteLeftSpecial f (kseq k) ->
  exists g, InfiniteLeftSpecial g (kseq k) /\ SubstSeqSeq (ksubst k) g f.
Proof.
 intros I.
 assert (K : k<>0).
 { intros ->. red in I. destruct (I [f 0]) as (a & b & AB & A & B).
   - easy.
   - apply LeftExt_letter in A,B. lia. }
 set (h := fun n => take (S (iternext (nextnonk k f) n)) f).
 assert (LA : forall n, last (h n) 0 <> k).
 { intros n. unfold h. rewrite take_S, last_app; try easy. simpl.
   apply iternext_spec. clear n. apply nextnonk_spec2; trivial. }
 assert (LS : forall n, LeftSpecial (h n) (kseq k)).
 { intros n. apply I. unfold h. red. now rewrite take_length. }
 assert (EX : exists h', forall n,
              h n = apply (ksubst k) (h' n) /\ LeftSpecial (h' n) (kseq k)).
 { set (R := fun n w => h n = apply (ksubst k) w /\ LeftSpecial w (kseq k)).
   change (exists h', forall n, R n (h' n)).
   apply choice. intros n.
   destruct (lemma_3_7_ii_ls k (h n) (LA n) (LS n)) as (v & E & V).
   exists v; split; auto. }
 destruct EX as (h', EX).
 assert (IMB : forall n, StrictPrefix (h n) (h (S n))).
 { intros n. unfold h. apply StrictPrefix_take. simpl.
   set (m := S (iternext _ _)). generalize (nextnonk_spec1 k f m). lia. }
 assert (IMB' : forall n, StrictPrefix (h' n) (h' (S n))).
 { intros n. specialize (IMB n).
   destruct (EX n) as (E1,LS1), (EX (S n)) as (E2,LS2).
   split.
   - eapply Prefix_ksubst_inv; eauto. 2:apply IMB.
     apply LeftSpecial_SubSeq. apply LS.
   - intros E. rewrite <- E in E2. rewrite <- E2 in E1. rewrite <- E1 in IMB.
     now apply IMB. }
 assert (L : forall n, n <= length (h' n)).
   { clear -IMB'.
     induction n; simpl; try lia. specialize (IMB' n).
     apply StrictPrefix_len in IMB'. lia. }
 exists (limword h'). split.
 - intros u U.
   apply LeftSpecial_Prefix with (h' (length u)). 2:apply EX.
   eapply PrefixSeq_incl; eauto. apply limword_ok; auto.
 - intros u U.
   assert (P : Prefix u (h' (length u))).
   { eapply PrefixSeq_incl; eauto. apply limword_ok; auto. }
   set (n := length u) in *. destruct (EX n) as (Ev,_).
   apply Prefix_PrefixSeq with (h n).
   + rewrite Ev. destruct P as (w & <-). rewrite apply_app. now eexists.
   + unfold h. red. now rewrite take_length.
Qed.

Lemma theorem_3_9_aux k n f :
  InfiniteLeftSpecial f (kseq k) -> PrefixSeq (take n f) (kseq k).
Proof.
 intros F.
 assert (K : k<>0).
 { intros ->. destruct (F [f 0]) as (a & b & AB & A & B).
   - easy.
   - apply LeftExt_letter in A,B. lia. }
 revert f F.
 induction n as [n IH] using lt_wf_ind. intros f F.
 destruct (Nat.eq_dec n 0) as [->|N0]; try easy.
 destruct (Nat.eq_dec n 1) as [->|N1]; try easy.
 { specialize (F (take 1 f) eq_refl). cbn in *. apply ls_head_k in F.
   rewrite F. easy. }
 destruct (proposition_3_8 k f F) as (g & G & G').
(*
 destruct (DecrLemma k (take n f)) as (v & w & V & W & E & L).
 { rewrite take_length; lia. }
 { apply F. red. now rewrite take_length. }
 { intros _. exists (f n). rewrite <- take_S.
   apply F. red. now rewrite take_length. }
 KO : rien ne dit que (take n f ++ w) est encore Prefix de f...
*)
 assert (N' : n-1 < n) by lia.
(* (* Is this helpful ? *)
 assert (IH' := IH (n-1) N' f F).
*)
 (* Beware, the last letter of (take n f) is at position (n-1) *)
 set (m := nextnonk k f (n-1)).
 assert (M1 := nextnonk_spec1 k f (n-1)).
 replace (n-1+2) with (S n) in M1 by lia.
 assert (M2 := nextnonk_spec2 k f K F (n-1)). fold m in M1,M2.
 apply Prefix_PrefixSeq with (take (S m) f).
 - apply Prefix_take. lia.
 - destruct (lemma_3_7_ii_ls k (take (S m) f)) as (v & V & V').
   + now rewrite take_S, last_app.
   + apply F. red. now rewrite take_length.
   + rewrite <- V.
     specialize (IH (n-1) N' g G).
     red in G'.
     assert (forall q, PrefixSeq (apply (ksubst k) (take q g)) f).
     { intros q. apply G'. red. now rewrite take_length. }
     (* donc si length (apply (ksubst k) (take q g)) >= S m
        alors Prefix (take (S m) f) (apply (ksubst k) (take q g))
        alors Prefix (apply (ksubst k) v) (apply (ksubst k) (take q g))
        Peut-être peut-on en déduite Prefix v (take q g)
        mais ce n'est pas certain, cf Prefix_ksubst_inv et ses conditions.
        Si oui, v est bien un prefix de g. Reste à montrer qu'il est
        assez petit pour IH. *)
     apply ksubst_prefix.
     red in G, G'.
Admitted.

Lemma theorem_3_9 k f :
  InfiniteLeftSpecial f (kseq k) -> forall n, f n = kseq k n.
Proof.
 intros I n. apply (theorem_3_9_aux k (S n)) in I. red in I.
 rewrite take_length in I. rewrite !take_S in I.
 apply app_inv' in I; trivial. now destruct I as (_,[= <-]).
Qed.

(* END INFINITE LEFT SPECIAL part *)
