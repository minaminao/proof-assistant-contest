Require Import Problem.

(*
  Prove task1 or task2. You can choose either one you like.
 *)

(*Lemma solution1: task1.
Proof.
  unfold task1.
  intros.
  destruct P,Q.
  (* FILL IN HERE *)
Qed.
*)

Theorem deMorgan1 (A B: Prop): ~(A\/B) -> ~A/\~B.
Proof.
  intro NAB.
  split.

  (* NAB: ~(A\/B) |- ~A *)
  - intro A1.
    apply NAB.
    left.
    exact A1.

  (* NAB ~(A\/B) |- ~B *)
  - intro B1.
    apply NAB.
    right.
    exact B1.
Qed.

Theorem deMorgan2 (A B: Prop): ~A/\~B -> ~(A\/B).
Proof.
  intros NANB AB.
  destruct NANB as [NA NB].
  destruct AB as [A1 | B1].

  (* NA:~A, NB:~B A1:A |- False *)
  - apply NA.
    exact A1.

  (* NA:~A, NB:~B B1:B |- False *)
  - apply NB.
    exact B1.
Qed.

Print deMorgan2.


Lemma solution2: task2.
Proof.
  unfold task2.
  intros.
  split.
  - apply deMorgan2.
  - apply deMorgan1.
Qed.


Theorem solution: task1 \/ task2.
Proof.
  right. apply solution2.
Qed.