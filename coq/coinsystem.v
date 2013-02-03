
Require Import List.
Require Import NPeano EqNat Compare_dec.


(* determine whether given list of numbers is in decreasing order *)
Fixpoint decreasing_order (ns : list nat) : bool :=
  match ns with
      | nil => true
      | _ :: nil => true
      | a :: b :: ns' =>  andb (ltb b a) (decreasing_order ns')
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
Definition C : coinlist := 25 :: 10 :: 5 :: 1 :: nil.

Lemma ClenN : length C = N.
 auto. Qed.
Lemma Cdecr : true = decreasing_order C.
  compute; repeat split; auto; apply leb_complete; auto.
  Qed.

(*
 Definition coinlist_valid (C : coinlist)
    := (length C) = N /\ decreasing_order C.

  Definition repr_valid (R : repr)
    := (length R) = N.
  
  Definition valid_coinlist := { C : coinlist | coinlist_valid C }.
  Definition valid_repr := { R : repr | repr_valid R }.

  Definition C : valid_coinlist.
    exists Cbase.
    repeat split.
    apply ClengthN.
    apply Cdecr.
  Defined.
*)
  
Fixpoint repr_value (V : repr) (C : coinlist) : nat :=  (* inner product V . C *)
  match V, C with
      | nil, nil => 0
      | v :: V', c :: C' => (v*c) + repr_value V' C'
      | _, _ => 0
  end. 

Eval compute in (beq_nat 38 (repr_value (1 :: 1 :: 0 :: 3 :: nil) (25 :: 10 :: 5 :: 1 :: nil))).

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
    | 0 => 0 :: nil
    | S n' => n :: range n'
  end.

Eval compute in (range 5).

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
                   let count_of_c_opts := range max_of_c in
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












