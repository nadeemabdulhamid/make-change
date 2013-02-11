
Require Import List.
Require Import NPeano EqNat Compare_dec.
Require Import Omega.


(* determine whether given list of numbers is in decreasing order *)
Fixpoint decreasing_order (ns : list nat) : bool :=
  match ns with
      | nil => true
      | a :: ns' => andb (match ns' with
                            | nil => true
                            | b :: _ => ltb b a
                          end)
                         (decreasing_order ns')
  end.

Fixpoint last_is_1 (ns : list nat) : bool :=
  match ns with
    | nil => false
    | 1 :: nil => true
    | _ :: nil => false
    | n :: ns' => last_is_1 ns'
  end.

Definition coinlist := list nat.
Definition repr := list nat.

Definition N := 4.
Definition C : coinlist := 25 :: 6 :: 5 :: 1 :: nil.

Eval compute in decreasing_order C.

(* this should follow from decreasing_order and last_is_1
Definition no_zeroes (C:coinlist) := forallb (fun c:nat => ltb 0 c) C.
*)

Fixpoint repr_value (C : coinlist) (V : repr) : nat :=  (* inner product V . C *)
  match C, V with
      | nil, nil => 0
      | c :: C', v :: V' => (c*v) + repr_value C' V'
      | _, _ => 0
  end. 

Eval compute in (beq_nat 38 (repr_value (25 :: 10 :: 5 :: 1 :: nil) (1 :: 1 :: 0 :: 3 :: nil))).

Fixpoint repr_size (A : repr) : nat :=
  match A with
      | nil => 0
      | a :: A' => a + repr_size A'
  end.

Eval compute in (beq_nat 5 (repr_size (1 :: 1 :: 0 :: 3 :: nil))).

Fixpoint repr_lt (U V : repr) : bool :=
  match U, V with
    | nil, nil => false
    | u :: U', v :: V' => 
      orb (ltb u v) (andb (beq_nat u v) (repr_lt U' V'))
    | _, _ => false
  end.

Definition repr_gt (U V : repr) : bool := repr_lt V U.

Eval compute in (repr_lt (1 :: 1 :: 0 ::  3 :: nil) (1 :: 3 :: 0 :: 0 :: nil)).
Eval compute in negb (repr_lt (1 :: 1 :: nil) (1 :: 1 :: nil)).
Eval compute in negb (repr_lt (3 :: 1 :: nil) (1 :: 1 :: nil)).

Fixpoint make_list (k:nat) (v:nat) :=
  match k with
    | 0 => nil
    | S k' => v :: make_list k' v
  end.

(* comp : is the first better than the second *)
Fixpoint best_of (comp : repr -> repr -> bool) (candidate : repr) (Rs : list repr) : repr :=
  match Rs with
      | nil => candidate
      | r :: Rs' => best_of comp (if (comp r candidate) then r else candidate) Rs'
  end.

Eval compute in 11 / 3.
Eval compute in 11 mod 3.

Fixpoint range (n:nat) : list nat :=
  match n with
    | 0 => nil
    | S n' => n' :: range n'
  end.

Fixpoint range_from (start num : nat) : list nat :=
  match num with
    | 0 => nil
    | S m => start :: range_from (S start) m
  end.

Eval compute in (range 5).
Eval compute in (range_from 10 5).

Fixpoint cons_each (x:nat) (V:list repr) :=
  match V with
    | nil => nil
    | v :: V' => (cons x v) :: cons_each x V'
  end.

Fixpoint all_reprs (C : coinlist) (v : nat) {struct C} : list repr :=
  match C with
      | nil => nil
      | c :: nil => (v :: nil) :: nil
      | c :: C' => let max_of_c := v / c in
                   let count_of_c_opts := range (S max_of_c) in
                   (fix all_reprs_iterate (X : list nat) : list repr :=
                      match X with
                        | nil => nil
                        | x :: X' =>
                          (* x .. c *)
                          app
                            (cons_each x (all_reprs C' (v - (x * c))))
                            (all_reprs_iterate X')
                      end) count_of_c_opts
  end.

Eval compute in (all_reprs C 17).

Definition more_minimal (new : repr) (cur : repr) : bool :=
  orb (ltb (repr_size new) (repr_size cur))
      (andb (beq_nat (repr_size new) (repr_size cur))
            (repr_lt cur new)).

Fixpoint make_repr_all_ones (n:nat) (v:nat) : repr :=
  match n with
    | 0 => nil
    | 1 => v :: nil
    | S n' => 0 :: make_repr_all_ones n' v
  end.

(* brute force computations of the minimal and greedy representations *)
Definition minimal_bf C v := best_of more_minimal (make_repr_all_ones (length C) v) (all_reprs C v).
Definition greedy_bf C v :=  best_of repr_gt  (make_repr_all_ones (length C) v) (all_reprs C v).

Fixpoint greedy (C:coinlist) (v:nat) : repr :=
  match C with
    | nil => nil
    | c :: C' => let q := v / c in
                 let r := v mod c in
                 q :: greedy C' r
  end.

Inductive Greedy : coinlist -> repr -> nat -> Prop :=
| Greedy_ones : forall v, Greedy (1 :: nil) (v :: nil) v
| Greedy_cons : forall  c C r R v,
                  v < c -> 
                  Greedy C R v ->
                  Greedy (c :: C) (r :: R) (c * r + v)
.

Inductive ReprValue : coinlist -> repr -> nat -> Prop :=
| ReprValue_ones : forall v, ReprValue (1 :: nil) (v :: nil) v
| ReprValue_cons : forall c C C' r R R' v v',
                     ReprValue C R v ->
                     C' = c :: C -> R' = r :: R -> v' = c*r + v ->
                     ReprValue C' R' v'
.

Inductive LastIs1 : coinlist -> Prop :=
| last1 : LastIs1 (1 :: nil)
| cons_last1 : forall c C, LastIs1 C -> LastIs1 (c :: C).

Lemma greedy_Greedy : forall C v, (Forall (fun c => 0 < c) C) -> LastIs1 C -> Greedy C (greedy C v) v.
Proof.
  induction C0.
  intros v H1 H2; inversion H2.
  intros v H1; inversion_clear H1;  intros H2; revert H0; inversion_clear H2; intros H3.
  unfold greedy.
  replace (v / 1) with v.
  constructor.
  unfold div; generalize (divmod_spec v 0 0 0 (le_n _)); elim (divmod v 0 0 0); simpl; intros; omega.
  simpl; unfold div.
  revert H; case a; simpl.
  intros; absurd (0 < 0); auto with arith.
  clear a; intros a H.
  generalize (divmod_spec v a 0 a (le_n _)); elim (divmod v a 0 a); simpl; intros q u (H1, H2).
  replace v with (q + a * q + (a - u)); try omega.
  constructor; auto; omega.
Qed.


Eval compute in (make_repr_all_ones 4 17).
Eval compute in (more_minimal  (0 :: 1 :: 1 :: 2 :: nil) (0 :: 0 :: 1 :: 12 :: nil)).
Eval compute in (more_minimal  (1 :: 2 :: 1 :: 0 :: nil) (0 :: 1 :: 1 :: 2 :: nil) ).

Eval compute in 
    let v := 83 in
    (minimal_bf C v , 
     greedy_bf C v, 
     greedy C v).





(* =================================================== *)
(* greedy produces same as greedy_bf *)

Lemma greedy_size_0 : forall C, repr_size (greedy C 0) = 0.
Proof.
  intros C; induction C; simpl; auto;
  replace (0 mod a) with 0; [ rewrite IHC; replace (0 / a) with 0 | idtac ]; auto with arith;
  case a; simpl; auto with arith.
Qed.

Lemma greedy_value_0 : forall C, repr_value C (greedy C 0) = 0.
Proof.
  intros C; induction C; simpl; auto;
  replace (0 mod a) with 0; [ rewrite IHC; replace (0 / a) with 0 | idtac ]; auto with arith; 
  case a; simpl; auto with arith; intros; try omega.
Qed.

Hint Immediate greedy_value_0 greedy_size_0 : core.

Lemma greedy_value : forall C v, (Forall (fun c => 0 < c) C) -> LastIs1 C -> repr_value C (greedy C v) = v.
Proof.
  induction C0; simpl; auto.
  intros v H1 H2; inversion H2.
  intros v H1 H2.
  inversion_clear H2; inversion_clear H1; simpl.
  generalize (divmod_spec v 0 0 0 (le_n _)); elim (divmod v 0 0 0); simpl; intros; omega.
  unfold div, modulo.
  revert H0; case a; clear a.
  intros Habs; inversion Habs.
  intros n Hlt.
  generalize (divmod_spec v n 0 n (le_n _)); elim (divmod v n 0 n); simpl;
  intros q u (H3, H4).
  pose (IHC0 (n-u) H2 H).
  rewrite e.
  replace (q * S n) with (q + n * q); try omega; auto with arith.
  replace (q * S n) with ((S n) * q); try omega; auto with arith.
Qed.

Inductive ReprGE : repr -> repr -> Prop :=
| ReprGE_nil : ReprGE nil nil
| ReprGE_eq  : forall v R R', ReprGE R R' -> ReprGE (v :: R) (v :: R')
| ReprGE_gt  : forall v v' R R', v' < v -> ReprGE (v :: R) (v' :: R')
.

(*
Lemma Greedy_lt: forall c C r R r' R' v,
                   Greedy (c::C) (r::R) v -> ReprValue (c::C) (r'::R') v -> r=r' \/ r>r'.
Proof.
  intros c C r R r' R' v HG.
  inversion_clear HG.
  intros HR.
  inversion_clear HR; auto.
  inversion H0.
  inversion H1.
  replace c0 with 1 in H2; replace r0 with r' in H2; replace r0 with r'; rewrite H2.
  case v0.
  left; auto with arith; omega.
  right; omega.

  remember (c*r + v0) as n.
  intros HR; revert H0.
  inversion HR. intros Habs.
  inversion Habs.

  intros HG.
  
  
  

Qed.*)




(* =================================================== *)
(* Pearson's algorithm to find smallest counterexample *)

Definition targetCvals (C:coinlist) : coinlist :=
  map (fun c => c - 1) C.

Eval compute in targetCvals (25 :: 10 :: 5 :: 1 :: nil).

Definition greedy_multi (C:coinlist) (V : list nat) : list repr :=
  map (greedy C) V.

Eval compute in (greedy_multi C (targetCvals C)).

Definition zero_out : repr -> repr :=
  map (fun x => 0).

Fixpoint generate_possible_ce (R : repr) (i : nat) : repr :=
  match R, i with
    | x :: R', 0 => x+1 :: zero_out R'
    | x :: R', S i' => x :: generate_possible_ce R' i'
    | _, _ => R
  end.

Definition generate_possible_ces_from (R : repr) (i j : nat) : list repr :=
  map (generate_possible_ce R) (range_from i (j - i)).

Eval compute in generate_possible_ce (2 :: 1 :: 3 :: 1 :: 2 :: 7 :: nil) 3.
Eval compute in generate_possible_ces_from (2 :: 1 :: 3 :: 1 :: 2 :: 7 :: nil) 1 4.

Fixpoint app_all (Rs : list (list repr)) : list repr :=
  match Rs with
    | nil => nil
    | x :: Rs' => app x (app_all Rs')
  end.

Definition generate_min_reprs_to_check (Gs : list repr) : list repr :=
  app_all (map (fun G => generate_possible_ces_from G 1 N) Gs).

Eval compute in generate_min_reprs_to_check  (greedy_multi C (targetCvals C)).

Definition is_min_lt_greedy_repr (R : repr) : bool :=
  ltb (repr_size R) (repr_size (greedy C (repr_value C R))).


Fixpoint findp (A:Type) (f: A -> bool) (As : list A) : option A :=
  match As with
    | nil => None
    | a :: As' => if (f a) then Some a else findp A f As'
  end.

Definition find_counterexample (C:coinlist) : option nat :=
  match 
    findp _ is_min_lt_greedy_repr (generate_min_reprs_to_check  (greedy_multi C (targetCvals C)))
  with
    | None => None
    | Some R => Some (repr_value C R)
  end.


Eval compute in (find_counterexample C).

Eval compute in 
    let v := 10 in
    (minimal_bf C v , 
     greedy_bf C v, 
     greedy C v).