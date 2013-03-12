
Require Import coinsystem tactics.
Require Import List NPeano Bool.
Require Import Omega.

Set Implicit Arguments.

Definition vect := list nat.

Inductive ListNth A : list A -> nat -> A -> Prop :=
| Nth_0 : forall a As, ListNth (a::As) 0 a
| Nth_S : forall a As b n, ListNth As n b -> ListNth (a::As) (S n) b
.

Definition DecreasingOrder ns
  := forall i j x y , i < j -> ListNth ns i x -> ListNth ns j y -> x > y.

Definition LastIs1 ns :=  ListNth ns (pred (length ns)) 1.

Definition NotNil (ns:list nat) := ~ (ns = nil).

Inductive ReprValue : coinlist -> repr -> nat -> Prop :=
| ReprValue_nil : ReprValue nil nil 0
| ReprValue_cons : forall c C v V s t, 
                   ReprValue C V s ->
                   (c*v) + s = t ->
                   ReprValue (c::C) (v::V) t.

Inductive ReprSize : repr -> nat -> Prop :=
| ReprSize_nil : ReprSize nil 0
| ReprSize_cons : forall v V n' n,
                    ReprSize V n' ->
                    n = v + n' ->
                    ReprSize (v::V) n.

Hint Constructors ReprValue ReprSize : core.

(* V1 < V2 --> 
    V1 = (a1, a2, ... aj, ....)
    V2 = (b1, b2, ... bj, ....)
  where a1=b1 ... aj-1=bj-1 and aj<bj *)
Definition ReprLt V1 V2
  := exists j v1 v2,
       ListNth V1 j v1
       /\ ListNth V2 j v2
       /\ v1 < v2
       /\ (forall i x y, i < j -> ListNth V1 i x -> ListNth V2 i y -> x = y).

Definition ReprGt V1 V2 := ReprLt V2 V1.

(* ReprSum V U D ->  V = U + D *)
Inductive ReprSum : repr -> repr -> repr -> Prop :=
| ReprSum_nil : ReprSum nil nil nil
| ReprSum_cons : forall v V' u U' d D',
                   ReprSum V' U' D' ->
                   v = u + d ->
                   ReprSum (v::V') (u::U') (d::D').

Definition Lexic_Gtest C V
  := forall v, ReprValue C V v -> forall V', ReprValue C V' v -> ReprGt V V' \/ V = V'.

Definition Minimal C V
  := forall v s, ReprValue C V v -> ReprSize V s
                 -> forall V' s', ReprValue C V' v -> ReprSize V' s' -> s <= s'.

Definition Canonical C
  := forall V, Lexic_Gtest C V <-> Minimal C V.


(* ================================================================ *)

Ltac inversion_on e :=
  match goal with
    | H:e |- _ => inversion H
  end.


Goal ListNth (1 :: 2 :: 4 :: 6 :: nil) 2 4.
Proof.
  repeat constructor.
Qed.

Lemma ListNth_nil_0 : forall A a i (x:A), ListNth (a :: nil) i x -> 0 = i.
Proof.
  intros; inversion_on (ListNth (a :: nil) i x); auto.
  inversion_on (ListNth nil n x).
Qed.

Lemma ListNth_nil_x : forall A a i (x:A), ListNth (a :: nil) i x -> a = x.
Proof.
  intros; inversion_on (ListNth (a :: nil) i x); auto.
  inversion_on (ListNth nil n x).
Qed.
 
Lemma ListNth_0 : forall A n ns (x:A), ListNth (n::ns) 0 x -> n = x.
Proof.
  intros; inversion_on (ListNth (n::ns) 0 x); auto.
Qed.

Lemma ListNth_S : forall A n ns i (x:A), ListNth (n::ns) (S i) x -> ListNth ns i x.
Proof.
  intros; inversion_on (ListNth (n::ns) (S i) x); auto.
Qed.


Hint Immediate ListNth_nil_0 ListNth_nil_x ListNth_0 ListNth_S : core.

Lemma decr_order_smaller_than :
  forall i n ns, true = decreasing_order (n::ns) ->
               forall x, ListNth ns i x -> n > x.
Proof.
  induction i.
  intros n ns; case ns; simpl.
  intros; inversion_on (ListNth nil 0 x).
  clear ns; intros n' ns Hdecr x Lnth.
  replace x with n' in *; eauto.
  apply ltb_lt.
  elim (andb_true_eq _ _ Hdecr); auto.

  intros n ns; case ns; simpl.
  intros; inversion_on (ListNth nil (S i) x).
  clear ns; intros n' ns'; case ns'; clear ns'.
  intros; inversion_on (ListNth (n'::nil) (S i) x); inversion_on (ListNth nil i x); simpl.
  intros n'' ns Hdecr x Lnth.
  elim (andb_true_eq _ _ Hdecr); clear Hdecr; intros H1 H2.  
  elim (andb_true_eq _ _ H2); clear H2; intros H2 H3.
  apply IHi with (n''::ns); [idtac | eauto].
  replace (decreasing_order (n :: n'' :: ns) )
  with ((n'' <? n) && decreasing_order (n''::ns)); auto.
  elim (andb_true_iff ((n'' <? n)) (decreasing_order (n'' :: ns))).
  intros H4 H5; symmetry.
  apply H5; split; auto with arith.
  symmetry in H1; apply ltb_lt in  H1.
  symmetry in H2; apply ltb_lt in  H2.
  apply ltb_lt; omega.
Qed.

Theorem decr_order_correct : 
  forall ns, decreasing_order ns = true -> DecreasingOrder ns.
Proof.
  unfold DecreasingOrder.
  induction ns.
  intros; inversion_on (ListNth nil i x).
  
  revert IHns; case ns; simpl; intros.
  replace i with 0 in *; replace j with 0 in *; eauto; inversion_on (0 < 0).
  assert (exists j', j = S j').
  inversion_on (i < j); eauto.
  elim H3; clear H3; intros j' Hj'.
  replace j with (S j') in *; auto; clear Hj' j.
  inversion_clear H2.

  revert dependent i; intros i; case i; clear i.
  intros.
  replace x with a; [idtac | eauto].
  apply decr_order_smaller_than with j' (n::l); auto.
  intros i' Hij H2.
  assert (ListNth (n::l) i' x).
  inversion H2; auto.
  symmetry in H; elim (andb_true_eq _ _ H); intros H4 H5; clear H.
  apply IHns with i' j'; eauto.
  omega.
Qed.

Lemma DecreasingOrder_rest : forall n ns, DecreasingOrder (n::ns) -> DecreasingOrder ns.
Proof.
  unfold DecreasingOrder.
  intros n ns H i j x y H0 H1 H2.
  apply H with (S i) (S j); auto with arith;
  constructor; auto.
Qed.

Theorem decr_order_complete :
  forall ns, DecreasingOrder ns -> decreasing_order ns = true.
Proof.
  induction ns; simpl; auto.
  revert IHns; case ns; auto.
  clear ns; intros n ns IHns H.
  apply andb_true_intro; split; auto.
  unfold DecreasingOrder in H.
  apply ltb_lt; apply H with 0 1; auto;
  repeat constructor.
  apply IHns.
  apply DecreasingOrder_rest with a; auto.
Qed.

Hint Immediate decr_order_correct decr_order_complete DecreasingOrder_rest : core.

Lemma decr_order_rest :
  forall n ns, decreasing_order (n::ns) = true -> decreasing_order ns = true.
Proof.
  intros n ns H.
  assert (DecreasingOrder ns); auto.
  apply DecreasingOrder_rest with n; auto.
Qed.

Hint Immediate decr_order_rest : core.

Theorem last_1_correct : forall ns, true = last_is_1 ns -> LastIs1 ns.
Proof.
  unfold LastIs1.
  induction ns.
  simpl; intros H; inversion_on (true = false).
  replace (pred (length (a::ns))) with (length ns); auto.
  revert dependent ns; intros ns; case ns; clear ns.

  simpl.
  case a; clear a.
  simpl; intros IHns H; inversion_on (true = false).
  intros a; case a; clear a.
  constructor.
  simpl; intros; inversion_on (true = false).

  intros n ns IHns H.
  replace (length (n::ns)) with (S (length ns)); auto.
  constructor.
  apply IHns.
  revert dependent a; intros a; case a; clear a; auto.
  intros a; case a; clear a; auto.
Qed.

Theorem last_1_not_nil : forall ns, true = last_is_1 ns -> NotNil ns.
Proof.
  unfold NotNil, not; intros; replace ns with (@nil nat) in *; simpl in *;
  inversion_on (true = false).
Qed.

Lemma DecrLast1_not0 : forall C, DecreasingOrder (0 :: C) -> LastIs1 (0 :: C) -> False.
Proof.
  intros C Hdecr Hlast1.
  unfold DecreasingOrder, LastIs1 in *.
  absurd (0 > 1); auto with arith.
  apply (Hdecr 0 (length C) 0 1); auto.
  replace (pred (length (0::C))) with (length C) in Hlast1; auto.
  revert dependent C.
  intros C; case C; clear C.
  intros Hdecr Hlast1.
  simpl in Hlast1.
  absurd (0 = 1); auto.
  eapply ListNth_0; eauto.
  simpl; auto with arith.
  constructor.
Qed.  

Lemma LastIs1_rest : forall n n' ns, LastIs1 (n::n'::ns) -> LastIs1 (n'::ns).
Proof.
  intros n n' ns H.
  unfold LastIs1 in *.
  inversion H; auto.
Qed.

Lemma LastIs1_nil : forall c, LastIs1 (c::nil) -> c = 1.
Proof.
  intros c H.
  inversion H; auto.
Qed.

Hint Immediate LastIs1_nil : core.


(* =================================================== *)

Lemma greedy_size_0 : forall C, repr_size (greedy C 0) = 0.
Proof.
  intros C; induction C; simpl; auto;
  replace (0 mod a) with 0; [ rewrite IHC; replace (0 / a) with 0 | idtac ]; auto with arith;
  case a; simpl; auto with arith.
Qed.

Lemma greedy_ReprSize_0 : forall C, DecreasingOrder C -> LastIs1 C -> ReprSize (greedy C 0) 0.
Proof.
  intros C; induction C; simpl; auto; try constructor.
  revert IHC.
  case C; clear C; [intros IHC Hdecr Hlast1 | intros c C IHC Hdecr Hlast1].

  inversion_clear Hlast1.
  simpl; eauto.
  
  assert (a<>0).
  intros Habs; rewrite Habs in *; eapply DecrLast1_not0; eauto.
  replace (0 / a) with 0; try (symmetry; apply Nat.div_0_l); auto.
  replace (0 mod a) with 0; try (symmetry; apply Nat.mod_0_l); auto.
  apply ReprSize_cons with 0; auto with arith.
  apply IHC.
  eapply DecreasingOrder_rest; eauto.
  eapply LastIs1_rest; eauto.
Qed.

Hint Immediate greedy_size_0 greedy_ReprSize_0 : core.

Lemma greedy_repr_value : 
  forall C v, NotNil C -> DecreasingOrder C -> LastIs1 C -> repr_value C (greedy C v) = v.
Proof.
  induction C.

  (* C = nil *)
  simpl; intros; absurd (NotNil nil); auto.
  rename a into c; intros v Hnil Hdecr Hlast1.
  revert dependent C.
  intros C; case C; clear C.

  (* C = 1 :: nil *)  
  intros IHC Hnil Hdecr Hlast1.
  simpl.
  replace c with 1; symmetry; auto.
  replace (1 * (v / 1) + 0) with (1 * (v /1)); auto with arith.
  replace (1 * (v / 1)) with (v / 1); auto with arith.
  symmetry; apply Nat.div_1_r.

  (* C = c' :: C' *)
  intros c' C'.
  remember (c' :: C') as C.
  intros IHC Hnil Hdecr Hlast1.
  simpl; rewrite IHC; auto.
  symmetry; apply Nat.div_mod.
  intros Habs; replace c with 0 in *.

  eapply DecrLast1_not0; eauto.
  rewrite HeqC; unfold NotNil; discriminate.
  apply DecreasingOrder_rest with c; auto.
  rewrite HeqC in *; apply LastIs1_rest with c; auto.
Qed.

Lemma ReprValue_1 :
  forall v v', ReprValue (1 :: nil) (v :: nil) v' -> v' = v.
Proof.
  intros v v' H.
  inversion_on (ReprValue (1 :: nil) (v :: nil) v').
  inversion_on (ReprValue nil nil s).
  omega.
Qed.

Lemma greedy_ReprValue : 
  forall C v v', NotNil C -> DecreasingOrder C -> LastIs1 C -> ReprValue C (greedy C v) v' -> v = v'.
Proof.
  induction C.

  (* C = nil *)
  simpl; intros; absurd (NotNil nil); auto.
  rename a into c; intros v v' Hnil Hdecr Hlast1.
  revert dependent C.
  intros C; case C; clear C.
 
  (* C = 1 :: nil *)  
  intros IHC Hnil Hdecr Hlast1.
  simpl.
  replace c with 1; try symmetry; auto.
  replace (v/1) with v in *; try (symmetry; apply Nat.div_1_r).
  apply ReprValue_1; auto.

  (* C = c' :: C' *)
  intros c' C'.
  remember (c' :: C') as C.
  intros IHC Hnil Hdecr Hlast1 Hrepr; simpl in *.
  
  inversion Hrepr.
  assert (NotNil C /\ DecreasingOrder C /\ LastIs1 C) as (HnilC, (HdecrC, Hlast1C));
    [repeat split; eauto | idtac].
  rewrite HeqC; discriminate.
  rewrite HeqC in *; apply LastIs1_rest with c; auto.
  generalize (IHC _ _ HnilC HdecrC Hlast1C H4); intros Heq.
  rewrite <- Heq in *.
  rewrite <- H5.
  apply Nat.div_mod.
  intros Habs; rewrite Habs in *.
  eapply DecrLast1_not0; eauto.
Qed.

Lemma greedy_ReprGt :
  forall C v V, NotNil C -> DecreasingOrder C -> LastIs1 C -> ReprValue C V v
                 -> (ReprGt (greedy C v) V) \/ (greedy C v = V).
Proof.
  induction C.

  Case "C = nil".
  simpl; intros; absurd (NotNil nil); auto.

  rename a into c; intros v V Hnil Hdecr Hlast1.
  revert dependent C.
  intros C; case C; clear C.

  Case "C = 1 :: nil".
  Focus 1.
  intros IHC Hnil Hdecr Hlast1 .
  replace c with 1; try symmetry; auto.
  unfold greedy, repr_value.
  replace (v / 1) with v ; [idtac | symmetry; apply Nat.div_1_r].
  intros Hrepr.
  right.
  inversion_clear Hrepr.
  revert H0.
  inversion_clear H; intros.
  replace v0 with v; auto; omega.

  Case "C = c :: c' :: C' (i.e. not last one)".
  intros c' C'.
  remember (c' :: C') as C. (* need this to show that NotNil C later when applying the IH *)
  intros IHC Hnil Hdecr Hlast1 Hrepr; simpl.
  assert (c <> 0) as Hc0.
  intros Habs; rewrite Habs in *; eapply DecrLast1_not0; eauto.
  inversion_clear Hrepr.
  rewrite <- H0.
  clear v H0.
  (* So, V = v0 :: V0 where  reprValue C V0 = s  and  c*v0 <= v 
      so v = c*v0 + s
    Thus, greedy (c::C v) would produce  (c*v0+s) / c  as the number of the 
    first coin. i.e. would pick  v0 + s / c as the number of the first coin -
    now this is either greater than or equal to v0 - it depends if s is less than c 
    or not. *)

  replace (c * v0) with (v0 * c); auto with arith.
  rewrite Nat.div_add_l; auto.
  replace (v0 * c + s) with (s + v0 * c); auto with arith.
  rewrite Nat.mod_add; auto.

  (* now in the reference repr, V, either s (left-over portion after # of first coins)
     is gt-or-equal the first coin value, or is less than.
     In the first case, greedy would have then picked more of the first coin; in the 
     second, greedy would pick the same number, and the property would hold by IH
     on the rest *)
  assert (c <= s \/ s < c) as Hor; [omega | inversion_clear Hor; [SCase "c <= s" | SCase "s < c"]].
  assert (0 < s / c) as Hsc; [ apply Nat.div_str_pos; omega | idtac ].
  left.
  unfold ReprGt, ReprLt.
  exists 0; exists v0; exists (v0 + s / c).
  repeat (split; repeat constructor; auto).
  omega.
  intros i x y Habs; omega.

  rewrite Nat.div_small; auto.
  rewrite Nat.mod_small; auto. 
  replace (v0 + 0) with v0; auto with arith.
  case (IHC s V0); eauto.
  rewrite HeqC; unfold NotNil; discriminate.
  rewrite HeqC in *; eapply LastIs1_rest; eauto.
  clear IHC.

  SSCase "ReprGt (greedy C s) V0".
  Focus 1.
  intros (j, (v1, (v2, (HL1, (HL2, (Hv12, Hi)))))).
  left.
  exists (S j); exists v1; exists v2.
  repeat split; try constructor; auto.
  intros i; case i; clear i.
  intros x y Hlt Hl1 Hl2.
  inversion_on (ListNth (v0::V0) 0 x).
  inversion_on (ListNth (v0 :: greedy C s) 0 y).
  omega.

  intros i' x y HltS Hl1 Hl2.
  apply Hi with i'; auto with arith.
  inversion Hl1; auto.
  inversion Hl2; auto.
  
  SSCase "greedy C s = V0".
  intros Heq; rewrite Heq; right; auto.
Qed.

Theorem greedy_Lexic_Ctest :
  forall C v, NotNil C -> DecreasingOrder C -> LastIs1 C -> Lexic_Gtest C (greedy C v).
Proof.
  intros C v Hnil Hdecr Hlast1.
  intros v' Hrepr V' Hrepr'.
  apply greedy_ReprGt; auto.
  replace v with v'; auto; symmetry; apply greedy_ReprValue with C; auto.
Qed.  

Lemma ReprLt_cons_inv :
  forall a A b B, ReprLt (a::A) (b::B) -> a < b \/ (a = b /\ ReprLt A B).
Proof.
  intros a A b B (j, H); revert H; destruct j.
  intros (v1, (v2, (Hv1, (Hv2, (Hlt, H))))).
  left; replace a with v1; [ replace b with v2; auto | idtac ].
  inversion Hv2; auto.
  inversion Hv1; auto.

  intros (v1, (v2, (Hv1, (Hv2, (Hlt, H))))).
  right.
  assert (ListNth A j v1) as Hv1'; [inversion Hv1; auto | idtac].
  assert (ListNth B j v2) as Hv2'; [inversion Hv2; auto | idtac].
  rewrite (H 0 a b); try split; auto with arith; try constructor.
  exists j; exists v1; exists v2; repeat split; auto.
  intros i x y Hlt' Hx Hy; apply H with (S i); auto with arith;
  constructor; auto.
Qed.

Lemma ReprGt_cons_inv :
  forall a A b B, ReprGt (a::A) (b::B) -> a > b \/ (a = b /\ ReprGt A B).
Proof.
  unfold ReprGt; intros a A b B H.
  elim (ReprLt_cons_inv H); intros; [left | right; inversion_clear H0]; auto; split; auto with arith.
Qed.

Lemma ReprLt_cons :
  forall a A B, ReprLt A B -> ReprLt (a::A) (a::B).
Proof.
  intros a A B (i, (v1, (v2, (H1, (H2, (H3, H4)))))).
  exists (S i); exists v1; exists v2; repeat split; try constructor; auto.
  destruct i0 as [ | i']; intros x y H5 H6 H7.
  inversion H6; inversion H7; omega.
  apply H4 with i'; try omega; inversion H6; inversion H7; auto.
Qed.

Lemma ReprGt_cons :
  forall a A B, ReprGt A B -> ReprGt (a::A) (a::B).
Proof.
  unfold ReprGt; intros; apply ReprLt_cons; auto.
Qed.

Lemma reprsum_gt_preserve :
  forall A B D A' B', ReprGt A B -> ReprSum A' A D -> ReprSum B' B D -> ReprGt A' B'.
Proof.
  induction A.

  destruct B.
  intros D A' B' (j, (x, (y, (H1, (H2, H))))); inversion_on (ListNth nil j y).
  intros D A' B' (j, (x, (y, (H1, (H2, H))))); inversion_on (ListNth nil j y).
 
  destruct B as [ | b B].
  intros D A' B' (j, (x, (y, (H1, (H2, H))))); inversion_on (ListNth nil j x).
  destruct D as [ | d D]; [intros A' B' _ Hsum; inversion Hsum | idtac].
  destruct A' as [ | a' A']; [intros A' B' Hsum; inversion Hsum | idtac].
  destruct B' as [ | b' B']; [intros X' Y' Hsum; inversion Hsum | idtac].
  intros Hgt HsumA HsumB.
  assert (a'=a+d /\ ReprSum A' A D) as (Ha', HsumA').
  inversion HsumA; auto.
  assert (b'=b+d /\ ReprSum B' B D) as (Hb', HsumB').
  inversion HsumB; auto.
  destruct (ReprGt_cons_inv Hgt) as [Hab | (Hab1, Hab2)].
  exists 0; exists b'; exists a'.
  repeat split; auto; try constructor; auto; try omega.
  intros i x y Habs; inversion Habs.

  replace b' with a'; try omega.
  apply ReprGt_cons; auto.
  apply IHA with B D; auto.
Qed.


(*
Lemma greedy_sum :
  forall C V U D, ReprSum V U D -> Lexic_Gtest C V -> Lexic_Gtest C U.
Proof.
  intros C V U D H H0.
  intros v Hr U' Hr'.
  *)


(* ================================================================ *)


Lemma best_of_opt_aux1 :
  forall (F:vect->vect->bool) V c b,
    best_of F c V = b ->
    (c = b \/ In b V).
Proof.
  induction V; auto; simpl; intros c b Hbest.
  generalize (IHV _ _ Hbest); remember (F a c) as X; destruct X; intros IHbest.
  right; elim IHbest; auto.
  elim IHbest; auto.
Qed.

Lemma best_of_opt_aux2 :
  forall (F:vect->vect->bool)
         (Frefl:forall a, F a a = true)
         (Ftrans:forall a b c, F a b = true -> F b c = true -> F a c = true)
         V c b,
    best_of F c V = b ->
    F b c = true.
Proof.
  induction V as [ | v' V']; auto; simpl; intros c b Hbest.
  rewrite Hbest; auto.
  assert (F b (if F v' c then v' else c) = true); auto.
  apply Ftrans with (if F v' c then v' else c); auto.
  remember (F v' c) as b'; destruct b'; auto.
Qed.

Lemma best_of_opt :
  forall (F:vect->vect->bool)
         (Frefl:forall a, F a a = true)
         (Ftrans:forall a b c, F a b = true -> F b c = true -> F a c = true)
         (Fasym:forall a b, F a b = false -> F b a = true)
         V c b,
    best_of F c V = b ->
    forall v, In v V -> F b v = true.
Proof.
  induction V as [ | v' V']; auto; simpl; intros c b Hbest.
  elim (best_of_opt_aux1 _ _ _ Hbest); intros Hb;
    intros v Hor; destruct Hor as [Hv | Hv].
  rewrite Hv in *; clear v' Hv.
  remember (F v c) as X; destruct X; [SCase "F v c = true" | SCase "F v c = false"];
  rewrite Hb in *; auto.
  apply IHV' with  (if F v' c then v' else c); auto.
  
  rewrite Hv in *; clear v' Hv.
  assert (F b  (if F v c then v else c) = true); auto.
  apply best_of_opt_aux2 with V'; auto.
  remember (F v c) as b'; destruct b'; auto.
  assert (F c v = true); [ apply Fasym; symmetry; auto | apply Ftrans with c; auto].
  apply IHV' with (if F v' c then v' else c); auto.
Qed.













Lemma eq_vect_dec : forall (V V':vect), {V = V'} + {V <> V'}.
Proof.
  induction V as [ | v V]; destruct V' as [ | v' V']; auto; try (right; discriminate).
  elim (IHV V'); intros HeqV'; auto.
  compare v v'; intros Heqv'; auto.
  rewrite HeqV'; rewrite Heqv'; left; auto.
  right; rewrite HeqV'.
  intro Habs; inversion Habs; absurd (v = v'); auto.
  right; intro Habs; inversion Habs; absurd (v = v'); auto.
Qed.

Lemma canonical_or_not : forall C, Canonical C \/ ~Canonical C.
Proof.
  intros C; unfold Canonical, Lexic_Gtest, Minimal.
  



    