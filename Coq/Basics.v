Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d: day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
  end.

Compute (next_weekday friday).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b: bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1: bool) (b2: bool) :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1: bool) (b2: bool) :=
  match b1 with
    | true => true
    | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition andb' (b1: bool) (b2: bool) : bool :=
  if b1 then b2
  else false.

Compute (andb' false false).
Example test_andb: (andb' false false) = false.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | false => true
    | true => negb b2
  end.
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
    | false => false
    | true => andb b2 b3
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Inductive rgb: Type :=
  | red
  | green
  | blue.

Inductive color: Type :=
  | black
  | white
  | prim (p: rgb).

Definition monochrome (c: color) : bool :=
  match c with
    | black => true
    | white => true
    | prim p => false
  end.

Definition isred (c: color) : bool :=
  match c with
    | prim red => true
    | _ => false
  end.

Example test_monochrome: monochrome black = true.
Proof. simpl. reflexivity. Qed.
Example test_monochrome2: monochrome (prim red) = false.
Proof. simpl. reflexivity. Qed.
Example test_isred: isred (prim red) = true.
Proof. simpl. reflexivity. Qed.
Example test_isred3: isred (prim blue) = false.
Proof. simpl. reflexivity. Qed.
Example test_isred4: isred white = false.
Proof. simpl. reflexivity. Qed.

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B0 B0 B0 B1).

Definition all_zero (nb: nybble) : bool :=
  match nb with
    | bits B0 B0 B0 B0 => true
    | bits _ _ _ _ => false
  end.

Compute (all_zero (bits B0 B0 B0 B0)).

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Compute (pred (S (S O))).

Check (S (S O)).

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minustwo (S (S (S (S O))))).
Compute (minustwo (S O)).

Fixpoint even (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => even n'
  end.

Compute (even (S (S (S O)))).

End NatPlayground.