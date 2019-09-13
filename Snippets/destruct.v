Goal forall b:bool, b = true \/ b = false.
destruct b.
left.
reflexivity.
right.
reflexivity.