Definition task := forall n m, n * S m = n + n * m.

Require Import Arith.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  ring.
Qed.