Definition task := forall (f: bool -> bool) b, f (f (f b)) = f b.

(* Hint *)
Lemma lemma: forall (f: bool -> bool) b x y z,
    x = f b -> y = f x -> z = f y -> z = x.
Proof.
  intros.
  destruct b.
  - destruct x.
    + destruct y.
      * rewrite H1. symmetry. apply H.
      * symmetry in H0. rewrite H0 in H. discriminate.
    + destruct y.
      * rewrite H1. symmetry. apply H.
      * rewrite H1. symmetry. apply H0.
  - destruct x.
    + destruct y.
      * rewrite H1. symmetry. apply H0.
      * rewrite H1. symmetry. apply H.
    + destruct y.
      * symmetry in H. rewrite H in H0. discriminate.
      * rewrite H1. symmetry. apply H.
Qed.

Theorem solution: task.
Proof. unfold task. intros. eapply lemma; reflexivity. Qed.