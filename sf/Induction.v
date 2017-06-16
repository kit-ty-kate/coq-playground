(* https://softwarefoundations.cis.upenn.edu/current/Induction.html *)

Require Export Basics.
Require Coq.Setoids.Setoid.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intro n.
  induction n.
  { simpl. reflexivity. }
  { simpl. apply IHn. }
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  { simpl. reflexivity. }
  { simpl. rewrite IHn. reflexivity. }
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n.
  { simpl. rewrite <- plus_n_O. reflexivity. }
  { simpl. rewrite IHn. apply plus_n_Sm. }
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  { simpl. reflexivity. }
  { simpl. rewrite IHn. reflexivity. }
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intro n.
  induction n.
  { simpl. reflexivity. }
  { simpl. rewrite IHn. rewrite <- plus_n_Sm. reflexivity. }
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intro n.
  induction n.
  { simpl. reflexivity. }
  { rewrite IHn. rewrite negb_involutive. simpl. reflexivity. }
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  induction n.
  { simpl. reflexivity. }
  { simpl. rewrite IHn. apply plus_n_Sm. }
Qed.

Theorem mult_S : forall n m : nat,
  n * S m = n * m + n.
Proof.
  intros n m.
  induction n.
  { simpl. reflexivity. }
  { simpl. rewrite IHn.
    symmetry. rewrite plus_comm.
    simpl. rewrite plus_swap. rewrite (plus_comm n (n * m)).
    reflexivity. }
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction n.
  { simpl. apply mult_0_r. }
  { simpl. rewrite mult_S. rewrite plus_comm. rewrite IHn. reflexivity. }
Qed.

Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  intro n.
  induction n.
  { simpl. reflexivity. }
  { simpl. apply IHn. }
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intro n. simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros []; simpl; reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros n m p H.
  induction p.
  { simpl. apply H. }
  { simpl. apply IHp. }
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  intro n. simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intro n. simpl. rewrite plus_n_O. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros [] []; simpl; reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p.
  { rewrite_all mult_0_r. simpl. reflexivity. }
  { rewrite mult_comm. simpl.
    rewrite_all mult_S.
    rewrite mult_comm, IHp.
    rewrite plus_swap.
    rewrite plus_assoc, plus_assoc.
    rewrite (plus_comm (m * p) m).
    rewrite (plus_assoc (n * p + n) m (m * p)).
    reflexivity. }
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n.
  { simpl. reflexivity. }
  { simpl. rewrite mult_plus_distr_r.
    rewrite IHn. reflexivity. }
Qed.

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intro n.
  induction n.
  { simpl. reflexivity. }
  { simpl. apply IHn. }
Qed.

(*

Exercise: 3 stars, recommendedM (binary_commute)
Recall the incr and bin_to_nat functions that you wrote for the binary exercise in the Basics chapter. Prove that the following diagram commutes:
                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S
That is, incrementing a binary number and then converting it to a (unary) natural number yields the same result as first converting it to a natural number and then incrementing. Name your theorem bin_to_nat_pres_incr ("pres" for "preserves").
Before you start working on this exercise, copy the definitions from your solution to the binary exercise here so that this file can be graded on its own. If you want to change your original definitions to make the property easier to prove, feel free to do so!

(* FILL IN HERE *)
☐
Exercise: 5 stars, advancedM (binary_inverse)
This exercise is a continuation of the previous exercise about binary numbers. You will need your definitions and theorems from there to complete this one; please copy them to this file to make it self contained for grading.
(a) First, write a function to convert natural numbers to binary numbers. Then prove that starting with any natural number, converting to binary, then converting back yields the same natural number you started with.
(b) You might naturally think that we should also prove the opposite direction: that starting with a binary number, converting to a natural, and then back to binary yields the same number we started with. However, this is not true! Explain what the problem is.
(c) Define a "direct" normalization function — i.e., a function normalize from binary numbers to binary numbers such that, for any binary number b, converting to a natural and then back to binary yields (normalize b). Prove it. (Warning: This part is tricky!)
Again, feel free to change your earlier definitions if this helps here.

(* FILL IN HERE *)
☐

*)