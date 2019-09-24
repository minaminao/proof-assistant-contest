Definition task := forall n : nat, 0 = n * 0.

Require Import Arith.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  ring.
Qed.