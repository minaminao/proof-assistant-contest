Definition plus_comm := forall n m : nat, n + m = m + n.

Theorem plus_comm_proof: plus_comm.
Proof.
  unfold plus_comm.
  induction n.
  - simpl.
    SearchRewrite (_ + _).
    intros.
    rewrite <- plus_n_O.
    reflexivity.
  - simpl.
    intros.
    SearchRewrite (_ + _).
    rewrite IHn.
    rewrite plus_n_Sm.
    reflexivity.
Qed.