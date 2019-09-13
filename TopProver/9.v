Require Import List.

Definition task := forall l: list nat, app l (0 :: nil) <> nil.


Theorem solution: task.
Proof.
  unfold task.
  intros.
  destruct l.
  - simpl. congruence.
  - simpl. congruence.
Qed.