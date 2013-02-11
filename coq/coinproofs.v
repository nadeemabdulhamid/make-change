
Require Import coinsystem.
Require Import List NPeano Bool.
Require Import Omega.

Set Implicit Arguments.

Inductive List_Nth A : list A -> nat -> A -> Prop :=
| Nth_0 : forall a As, List_Nth (a::As) 0 a
| Nth_S : forall a As b n, List_Nth As n b -> List_Nth (a::As) (S n) b
.

Goal List_Nth (1 :: 2 :: 4 :: 6 :: nil) 2 4.
Proof.
  repeat constructor.
Qed.

Ltac inversion_on e :=
  match goal with
    | H:e |- _ => inversion H
  end.


Lemma List_Nth_nil_0 : forall A a i (x:A), List_Nth (a :: nil) i x -> 0 = i.
Proof.
  intros; inversion_on (List_Nth (a :: nil) i x); auto.
  inversion_on (List_Nth nil n x).
Qed.

Lemma List_Nth_nil_x : forall A a i (x:A), List_Nth (a :: nil) i x -> a = x.
Proof.
  intros; inversion_on (List_Nth (a :: nil) i x); auto.
  inversion_on (List_Nth nil n x).
Qed.
 
Lemma List_Nth_0 : forall A n ns (x:A), List_Nth (n::ns) 0 x -> n = x.
Proof.
  intros; inversion_on (List_Nth (n::ns) 0 x); auto.
Qed.

Lemma List_Nth_S : forall A n ns i (x:A), List_Nth (n::ns) (S i) x -> List_Nth ns i x.
Proof.
  intros; inversion_on (List_Nth (n::ns) (S i) x); auto.
Qed.


Hint Immediate List_Nth_nil_0 List_Nth_nil_x List_Nth_0 List_Nth_S : core.

Lemma decr_order_smaller_than :
  forall i n ns, true = decreasing_order (n::ns) ->
               forall x, List_Nth ns i x -> n > x.
Proof.
  induction i.
  intros n ns; case ns; simpl.
  intros; inversion_on (List_Nth nil 0 x).
  clear ns; intros n' ns Hdecr x Lnth.
  replace x with n' in *; eauto.
  apply ltb_lt.
  elim (andb_true_eq _ _ Hdecr); auto.

  intros n ns; case ns; simpl.
  intros; inversion_on (List_Nth nil (S i) x).
  clear ns; intros n' ns'; case ns'; clear ns'.
  intros; inversion_on (List_Nth (n'::nil) (S i) x); inversion_on (List_Nth nil i x); simpl.
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


Theorem decr_order_mean : 
  forall ns, true = decreasing_order ns -> 
             forall i j x y , i < j -> List_Nth ns i x -> List_Nth ns j y -> x > y.
Proof.
  induction ns.
  intros; inversion_on (List_Nth nil i x).
  
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
  assert (List_Nth (n::l) i' x).
  inversion H2; auto.
  elim (andb_true_eq _ _ H); intros H4 H5; clear H.
  apply IHns with i' j'; eauto.
  omega.
Qed.

Theorem last_1_List_Nth : forall ns, true = last_is_1 ns -> List_Nth ns (pred (length ns)) 1.
Proof.
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






