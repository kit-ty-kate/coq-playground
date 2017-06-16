(* https://softwarefoundations.cis.upenn.edu/current/Basics.html *)

Definition nandb (b1:bool) (b2:bool) : bool := match b1, b2 with
  | true, false => true
  | false, false => true
  | false, true => true
  | true, true => false
end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool := match b1, b2, b3 with
  | true, true, true => true
  | _, _, _ => false
end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Fixpoint factorial (n:nat) : nat := match n with
  | 0 => 1
  | S m => n * factorial m
end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.


Definition blt_nat (n m : nat) : bool :=
  leb n m && negb (beq_nat n m)
.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2.
  rewrite H1, H2.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m H.
  rewrite H.
  reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros [] [] H.
  { reflexivity. }
  { simpl in H. apply H. }
  { reflexivity. }
  { simpl in H. apply H. }
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros [ | n].
  { simpl. reflexivity. }
  { simpl. reflexivity. }
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite H, H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite H, H.
  destruct b.
  { simpl. reflexivity. }
  { simpl. reflexivity. }
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros [] [] H.
  { reflexivity. }
  { simpl in H. rewrite H. reflexivity. }
  { simpl in H. rewrite H. reflexivity. }
  { reflexivity. }
Qed.

(* TODO

Exercise: 3 starsM (binary)
Consider a different, more efficient representation of natural numbers using a binary rather than unary system. That is, instead of saying that each natural number is either zero or the successor of a natural number, we can say that each binary number is either

    zero,
    twice a binary number, or
    one more than twice a binary number.

(a) First, write an inductive definition of the type bin corresponding to this description of binary numbers.
(Hint: Recall that the definition of nat above,
         Inductive nat : Type := | O : nat | S : nat → nat.
says nothing about what O and S "mean." It just says "O is in the set called nat, and if n is in the set then so is S n." The interpretation of O as zero and S as successor/plus one comes from the way that we use nat values, by writing functions to do things with them, proving things about them, and so on. Your definition of bin should be correspondingly simple; it is the functions you will write next that will give it mathematical meaning.)
(b) Next, write an increment function incr for binary numbers, and a function bin_to_nat to convert binary numbers to unary numbers.
(c) Write five unit tests test_bin_incr1, test_bin_incr2, etc. for your increment and binary-to-unary functions. (A "unit test" in Coq is a specific Example that can be proved with just reflexivity, as we've done for several of our definitions.) Notice that incrementing a binary number and then converting it to unary should yield the same result as first converting it to unary and then incrementing.

(* FILL IN HERE *)
☐

*)