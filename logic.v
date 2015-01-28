Theorem biconditional_elimination :
  forall (p q : Prop), (p <-> q) -> ((p -> q) /\ (q -> p)).
Proof.
  intros p q H.
  destruct H as [H G].
  split.

  apply H.
  apply G.
Qed.

Theorem non_contradiction :
  forall (p : Prop), (p /\ ~p) -> False.
Proof.
  intros p H.
  destruct H as [H G].

  absurd p.
  apply G.
  apply H.
Qed.

Theorem commutativity_and :
  forall (p q : Prop), p /\ q -> q /\ p.
Proof.
  intros p q H.
  destruct H as [H G].
  split.

  apply G.
  apply H.
Qed.

Theorem commutativity_or :
  forall (p q : Prop), p \/ q -> q \/ p.
Proof.
  intros p q H.
  destruct H as [H | G].

  right.
  apply H.

  left.
  apply G.
Qed.

Theorem associativity_and :
  forall (p q r : Prop), p /\ (q /\ r) -> (p /\ q) /\ r.
Proof.
  intros p q r H.
  destruct H as [H G].
  destruct G as [G I].
  split.
  split.

  apply H.
  apply G.
  apply I.
Qed.

Theorem associativity_or :
  forall (p q r : Prop), p \/ (q \/ r) -> (p \/ q) \/ r.
Proof.
  intros p q r H.
  destruct H as [H | G].

  left.
  left.
  apply H.

  destruct G as [G | I].
  left.
  right.
  apply G.

  right.
  apply I.
Qed.

Theorem idempotency_and :
  forall (p : Prop), p /\ p -> p.
Proof.
  intros p H.
  destruct H as [H _].

  apply H.
Qed.

Theorem idempotency_or :
  forall (p : Prop), p \/ p -> p.
Proof.
  intros p H.
  destruct H as [H | G].

  apply H.
  apply G.
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
