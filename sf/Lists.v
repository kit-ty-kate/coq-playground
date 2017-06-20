Require Export Induction.
Module NatList.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intro. induction p. simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intro p. induction p. simpl. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | cons h t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | cons h t => h
  end.

Fixpoint nonzeros (l:natlist) : natlist := match l with
  | nil => nil
  | cons 0 xs => nonzeros xs
  | cons x xs => cons x (nonzeros xs)
end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist := match l with
  | nil => nil
  | cons x xs => if oddb x then cons x (oddmembers xs) else oddmembers xs
end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l)
.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist := match l1, l2 with
  | nil, l2 => l2
  | cons _ _, nil => l1
  | cons x xs, cons y ys => cons x (cons y (alternate xs ys))
end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4:
  alternate nil [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat := match s with
  | nil => 0
  | cons x xs => if beq_nat x v then S (count v xs) else count v xs
end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := alternate.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := cons v s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool := negb (beq_nat (count v s) 0).

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag := match s with
  | nil => nil
  | cons x xs => if beq_nat x v then xs else cons x (remove_one v xs)
end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag := match s with
  | nil => nil
  | cons x xs => if beq_nat x v then remove_all v xs else cons x (remove_all v xs)
end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool := match s1 with
  | nil => true
  | cons x xs => if leb (count x s1) (count x s2) then subset xs s2 else false
end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | cons h t => app (rev t) [h]
  end.

Theorem app_nil_r : forall l : natlist,
  app l nil = l.
Proof.
  intro l.
  induction l.
  { simpl. reflexivity. }
  { simpl. rewrite IHl. reflexivity. }
Qed.

Theorem app_comm : forall l1 l2 l3 : natlist,
  app l1 (app l2 l3) = app (app l1 l2) l3.
Proof.
  intros l1 l2 l3.
  induction l1.
  { simpl. reflexivity. }
  { simpl. rewrite IHl1. reflexivity. }
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (app l1 l2) = app (rev l2) (rev l1).
Proof.
  intros l1 l2.
  induction l1.
  { simpl. rewrite app_nil_r. reflexivity. }
  { simpl. rewrite IHl1. rewrite app_comm. reflexivity. }
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intro l.
  induction l.
  { simpl. reflexivity. }
  { simpl. rewrite rev_app_distr. simpl. rewrite IHl. reflexivity. }
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  app l1 (app l2 (app l3 l4)) = app (app (app l1 l2) l3) l4.
Proof.
  intros.
  induction l1.
  { simpl. apply app_comm. }
  { simpl. rewrite IHl1. reflexivity. }
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (app l1 l2) = app (nonzeros l1) (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1.
  { simpl. reflexivity. }
  { induction n.
    { simpl. apply IHl1. }
    { simpl. rewrite IHl1. reflexivity. } }
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool := match l1, l2 with
  | nil, nil => true
  | nil, _ | _, nil => false
  | cons x xs, cons y ys => if beq_nat x y then beq_natlist xs ys else false
end.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof. simpl. reflexivity. Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof. simpl. reflexivity. Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof. simpl. reflexivity. Qed.

Theorem beq_nat_refl : forall n : nat,
  beq_nat n n = true.
Proof.
  intro n.
  induction n.
  { simpl. reflexivity. }
  { simpl. apply IHn. }
Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intro l.
  induction l.
  { simpl. reflexivity. }
  { simpl. rewrite beq_nat_refl. apply IHl. }
Qed.

Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (cons 1 s)) = true.
Proof.
  intro s.
  induction s; simpl; reflexivity.
Qed.

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intro s.
  induction s.
  { simpl. reflexivity. }
  { induction n.
    { simpl. apply ble_n_Sn. }
    { simpl. apply IHs. } }
Qed.

Goal forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite rev_involutive.
  reflexivity.
Qed.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption := match l with
  | nil => None
  | cons x _ => Some x
end.

Example test_hd_error1 : hd_error nil = None.
Proof. simpl. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. simpl. reflexivity. Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. simpl. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default.
  induction l.
  { simpl. reflexivity. }
  { simpl. reflexivity. }
Qed.

End NatList.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  intro.
  induction x.
  induction n.
  { simpl. reflexivity. }
  { simpl in *. apply IHn. }
Qed.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.

Theorem find_update : forall x i n d v,
  find x (update (record i n d) x v) = find x (update d x v).
Proof.
  intros.
  simpl.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros.
  induction d.
  { simpl. rewrite <- beq_id_refl. reflexivity. }
  { rewrite find_update. apply IHd. }
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o H.
  induction d.
  { simpl. rewrite H. reflexivity. }
  { simpl. rewrite H. reflexivity. }
Qed.

End PartialMap.