Theorem biconditional_elimination :
  forall (p q : Prop), (p <-> q) <-> ((p -> q) /\ (q -> p)).
Proof.
  intros p q.
  split.

  intro H.
  destruct H as [H G].
  split.

  apply H.
  apply G.

  intro H.
  destruct H as [H G].
  split.

  apply H.
  apply G.
Qed.

Theorem non_contradiction :
  forall (p : Prop), (p /\ ~p) <-> False.
Proof.
  intro p.
  split.

  intro H.
  destruct H as [H G].

  absurd p.
  apply G.
  apply H.

  intro H.
  contradict H.
Qed.

Theorem commutativity_and :
  forall (p q : Prop), p /\ q <-> q /\ p.
Proof.
  intros p q.
  split.

  intro H.
  destruct H as [H G].
  split.

  apply G.
  apply H.

  intro H.
  destruct H as [H G].
  split.

  apply G.
  apply H.
Qed.

Theorem commutativity_or :
  forall (p q : Prop), p \/ q <-> q \/ p.
Proof.
  intros p q.
  split.

  intro H.
  destruct H as [H | H].

  right.
  apply H.

  left.
  apply H.

  intro H.
  destruct H as [H | H].

  right.
  apply H.

  left.
  apply H.
Qed.

Theorem associativity_and :
  forall (p q r : Prop), p /\ (q /\ r) <-> (p /\ q) /\ r.
Proof.
  intros p q r.
  split.

  intro H.
  destruct H as [H G].
  destruct G as [G I].
  split.
  split.

  apply H.
  apply G.
  apply I.

  intro H.
  destruct H as [H G].
  destruct H as [H I].

  split.
  apply H.

  split.
  apply I.

  apply G.
Qed.

Theorem associativity_or :
  forall (p q r : Prop), p \/ (q \/ r) <-> (p \/ q) \/ r.
Proof.
  intros p q r.
  split.

  intro H.
  destruct H as [H | H].

  left.
  left.
  apply H.

  destruct H as [H | H].
  left.
  right.
  apply H.

  right.
  apply H.

  intro H.
  destruct H as [H | H].
  destruct H as [H | H].

  left.
  apply H.

  right.
  left.
  apply H.

  right.
  right.
  apply H.
Qed.

Theorem idempotency_and :
  forall (p : Prop), p /\ p <-> p.
Proof.
  intro p.
  split.

  intro H.
  destruct H as [H _].

  apply H.

  intro H.
  split.

  apply H.
  apply H.
Qed.

Theorem idempotency_or :
  forall (p : Prop), p \/ p <-> p.
Proof.
  intro p.
  split.

  intro H.
  destruct H as [H | G].

  apply H.
  apply G.

  intro H.
  left.

  apply H.
Qed.

Theorem absorption_and :
  forall (p q : Prop), (p /\ (p \/ q)) <-> p.
Proof.
  intros p q.
  split.

  intro H.
  destruct H as [H _].
  apply H.

  intro H.
  split.

  apply H.

  left.
  apply H.
Qed.
