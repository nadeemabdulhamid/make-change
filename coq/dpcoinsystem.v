
Require Import List.
Require Import NPeano EqNat Compare_dec.


Definition min (m : nat) (n : nat) : nat :=
  if (ltb m n) then m 
  else n.


Fixpoint min_num_coins (n : nat) (vals : list nat) : nat :=
  match n with
    | 0 => 0
    | n' => let min_of_options :=
                (fix make_change_choices (n : nat) (vals : list nat) : nat :=
                 match vals with
                   | nil => 1000
                   | val :: vals' => 
                       if  (ltb val n) then (make_change_choices n vals')
                       else (min (min_num_coins (n - val) vals)
                                 (make_change_choices n vals'))
                 end) n' vals
            in
              (S min_of_options)
  end.