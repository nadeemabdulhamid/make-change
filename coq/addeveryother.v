
Require Import Arith.
Require Import Arith.Div2.
Require Import Arith.Even.
Require Import Omega.
Load "tactics.v".

(* addEveryOther 10  = addEveryOther 10 + 8 + 6 + 4 + 2 + 0 = 30
   addEveryOther 5 = 5 + 3 + 1 = 9 
  b is an artificial parameter to bound the recursion (see Coq'Art section 15.1)
*)
Fixpoint addEveryOther_aux (b:nat) (n:nat) : nat :=
  match b with
    | 0 => 0
    | S b' =>
      match n with
        | 0 => 0
        | 1 => 1
        | n => n + addEveryOther_aux b' (n-2)
      end
  end.

Eval compute in (addEveryOther_aux 10 10).
Eval compute in (addEveryOther_aux 10 5).

Definition addEveryOther (n:nat) : nat :=
  addEveryOther_aux n n.

(* Properties:
  if n is even, then addEveryOther n == (n/2)(n/2 + 1)
  if n is odd, then addEveryOther n ==  square( (n+1)/2 )
*)

Lemma add_aux_even_correct : 
  forall b n, n <= b -> even n -> addEveryOther_aux b n = (div2 n)*(S (div2 n)).
Proof.
  induction b; simpl.
  intros n Hle Heven; inversion Hle; auto.
  destruct n; [Case "n=0" | Case "n>=1"]; auto with arith.
  destruct n; [SCase "n=1" | SCase "n>=2"]; simpl.
  intros _ Habs; inversion Habs; inversion_on (odd 0).
  intros Hle Heven.
  assert (even n).
    inversion Heven; inversion_on (odd (S n)); auto.
  assert (n <= b).
    omega.
  replace (n - 0) with n; auto with arith.
  rewrite IHb; auto.
  apply eq_S.
  apply eq_S.
  rewrite (even_double n) at 1; auto.
  generalize (div2 n) as k; intros k.
  replace (double k) with (k + k);  auto with arith.
  replace (k * S (S k)) with (k * (2 + k)); auto.
  replace (k * (2 + k)) with (k * 2 + k * k) by
      (symmetry; apply  (mult_plus_distr_l k 2 k); auto).
  replace (k * (S k)) with (k * (1 + k)); auto.
  replace (k * (1 + k)) with (k * 1 + k * k) by
      (symmetry; apply  (mult_plus_distr_l k 1 k); auto).
  omega.
Qed.  

Theorem add_even_correct : forall n, even n -> addEveryOther n =  (div2 n)*(S (div2 n)).
Proof.
  intros n Heven; unfold addEveryOther.
  apply add_aux_even_correct; auto.
Qed.





