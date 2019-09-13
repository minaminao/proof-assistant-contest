Require Import Omega.

Definition task := forall m n, m + n = 1 -> m = 0 \/ n = 0.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  omega.
Qed.