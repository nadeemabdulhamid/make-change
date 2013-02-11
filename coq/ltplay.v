
Require Arith.

(*
Inductive le (n : nat) : nat -> Prop :=
 | le_n : n <= n 
 | le_S : forall m : nat, n <= m -> n <= S m
*)


Fixpoint leb (n m : nat) : bool :=
  match n with
    | 0 => true
    | S n' => match m with
                | 0 => false
                | S m' => leb n' m'
              end
  end.

Eval compute in (leb 5 2).
Eval compute in (leb 50 2).
Eval compute in (leb 52 52).
Eval compute in (leb 100 424).

(*
Lemma le_0_any : forall m, 0 <= m.
Proof.
  induction m.
  constructor. (*  apply le_n. *)
  constructor.
  trivial.
Defined.
*)

Fixpoint le_0_any (m:nat) : 0 <= m :=
  match m return 0 <= m with
    | 0 => le_n 0
    | S m' => le_S _ _ (le_0_any m')
  end.


Definition le_n_S      : forall n m : nat, n <= m -> S n <= S m :=
fun (n m : nat) (H : n <= m) =>
le_ind n (fun m0 : nat => S n <= S m0) (le_n (S n))
  (fun (m0 : nat) (_ : n <= m0) (IHle : S n <= S m0) =>
   le_S (S n) (S m0) IHle) m H
.


Lemma leb_le : forall n m, leb n m = true -> n <= m.
Proof.
  induction n; try rename n into n'.
  intros m H.
  apply le_0_any.

  simpl.
  intros m.
  case m; clear m.
  intros Habs.
  discriminate.
  intros m'.
  intros H.
  generalize (IHn _ H); intros H1.
  apply le_n_S.
  trivial.
Defined.

Eval compute in (leb_le 4 9 (refl_equal _)).


Lemma le_leb : forall n m, n <= m -> leb n m = true.
Proof.
  induction n.
  intros m H.
  simpl.
  trivial.
  intros m.
  intros H.
  generalize (IHn _ H); intros H1.
  simpl.
  case m.
  intros Habs.

Qed.

(*
; A nat is
;  - 0  or
;  - S n

; le : nat nat -> boolean
(define (le n m)
  (cond [(n = 0) ...]
        [(n = S n')   .. (le n' ..)... ]))

..)


*)

