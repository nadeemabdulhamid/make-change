
Require Import List.
Require Import NPeano.
Require Import EqNat.
Require Import Compare_dec.


Definition min (m : nat) (n : nat) : nat :=
  if (geb m n) then n
  else m.


Fixpoint min_num_coins (n : nat) (vals : list nat) : nat :=
  match n with
      | 0 => 0
      | n' => let min_of_options := 
                  (fix make_change_choices (n : nat) (vals : list nat) : nat :=
                    match vals with
                        | nil => 1000
                        | val :: vals' =>
                            if  (geb n val) then (min (min_num_coins (n - val) vals)
                                                     (make_change_choices n vals'))
                            else (make_change_choices n vals')
                    end)
                    in
                      (S min_of_options)
  end.