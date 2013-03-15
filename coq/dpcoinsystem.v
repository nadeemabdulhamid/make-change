
Require Import List.
Require Import NPeano EqNat Compare_dec.


Fixpoint min (n : nat) (m : nat) : nat :=
  match n with
      | 0 => 0
      | S n' => match m with
                    | 0 => 0
                    | S m' => S (min n' m')
                end
  end.

Eval compute in (min 8 4).



Fixpoint min_num_coins (n : nat) (m : nat) (vals : list nat) : nat :=
  match n with
    | 0 => 0
    | S n' => 
             match m with
                | 0 => 0
                | S m' => 
                  let fix make_change_choices (vals0 : list nat) (m0 : nat) : nat :=
                  match vals0 with
                    | nil => 1000
                    | val :: vals' => let fix try_choice (m1 : nat) (val0: nat) : nat :=
                                          match val0 with 
                                            | 0 => (min_num_coins n' (m0 - val) vals)
                                            | S val1 => match m1 with
                                                        | 0 => 1000
                                                        | S m2 => (try_choice m2 val1)
                                                      end
                                          end
                                      in (min (try_choice m0 val)
                                              (make_change_choices vals' m0))
                  end
                  in
                    (S (make_change_choices vals m))
                end
  end.

Eval compute in (min_num_coins 16 16 (10 :: 8 :: 5 :: 1 :: nil)).


(*Fixpoint min_num_coins (n : nat) (vals : list nat) : nat :=
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
end.*)
