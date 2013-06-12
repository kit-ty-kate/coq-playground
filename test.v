Fixpoint fact (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => n * fact n'
  end.

Class MonadExn (m : Type -> Type -> Type) :=
  { ret : forall {x exn}, x -> m x exn
  ; bind : forall {x exn}, m x exn -> (x -> m x exn) -> m x exn
  ; fail : forall {x exn}, exn -> m x exn
  ; catch : forall {x exn exn'}, m x exn -> (exn -> m x exn') -> m x exn'
  }.

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n'].
  simpl.
  reflexivity.

  simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Theorem plus_comm_help : forall n m:nat, n + S m = S (n + m).
Proof.
  intros n m.
  induction n as [| n'].
  simpl.
  reflexivity.

  simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Theorem plus_comm : forall n m:nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' ].
  symmetry.
  apply plus_0_r.

  induction m as [| m' ].
  simpl.
  rewrite IHn'.
  simpl.
  reflexivity.

  simpl.
  rewrite IHn'.
  simpl.
  rewrite plus_comm_help.
  reflexivity.
Qed.

Require Import Compare_dec.
Require Import Lt.

Definition g x :=
  match nat_compare x 100 with
    | Gt => 100
    | _ => x
  end.

Theorem test : forall x, g x <= 100.
Proof.
  intros x.
  unfold g.
  remember (nat_compare x 100) as y.
  destruct y.
  symmetry in Heqy.
  apply nat_compare_eq in Heqy.
  rewrite Heqy.
  apply le_n.

  symmetry in Heqy.
  apply nat_compare_lt in Heqy.
  apply lt_le_weak.
  apply Heqy.

  apply le_n.
Qed.
