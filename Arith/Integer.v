Require Import RA.Arith.Natural.
Require Import Setoid.

Declare Scope Integer_Scope.
Delimit Scope Integer_Scope with i.

Open Scope Integer_Scope.

Inductive num : Type :=
| diff (n m : Natural.num).

Notation "n -- m" :=
    (diff n m)
    (at level 5, no associativity)
    : Integer_Scope.

Definition eq (i j : num) : Prop :=
    match i, j with
    | n1 -- m1, n2 -- m2 => (n1 + m2 = n2 + m1)%n
    end.

Notation "i == j" :=
    (eq i j)
    (at level 70, no associativity)
    : Integer_Scope.

Theorem eq_refl :
    forall i : num, i == i.
Proof.
    intros [n m].
    reflexivity.
Qed.

Theorem eq_symm :
    forall i j : num, i == j -> j == i.
Proof.
    intros [n1 m1] [n2 m2] H.
    simpl in *.
    symmetry.
    apply H.
Qed.

Theorem eq_trans :
    forall i j k : num, i == j -> j == k -> i == k.
Proof.
    intros [n1 m1] [n2 m2] [n3 m3] H1 H2.
    simpl in *.
    rewrite plus_comm with (n := n1).
    rewrite plus_comm with (n := n3).
    apply plus_cancel_left with (n := n2).
    apply plus_cancel_right with (n := m2).
    do 2 rewrite <- plus_assoc.
    do 2 rewrite plus_assoc with (o := m2).
    rewrite H1.
    rewrite H2.
    apply plus_comm.
Qed.

Add Parametric Relation : (num) (@eq)
    reflexivity proved by (eq_refl)
    symmetry proved by (eq_symm)
    transitivity proved by (eq_trans)
    as eq_rel.

Definition plus (i j : num) : num :=
    match i, j with
    | n1 -- m1, n2 -- m2 => (n1 + n2)%n -- (m1 + m2)%n
    end.

Notation "i + j" :=
    (plus i j)
    (at level 50, left associativity)
    : Integer_Scope.

Theorem plus_comm :
    forall i j : num, i + j == j + i.
Proof.
    intros [n1 m1] [n2 m2].
    simpl.
    rewrite plus_comm with (n := n1).
    rewrite plus_comm with (n := m1).
    reflexivity.
Qed.

Theorem plus_assoc :
    forall i j k : num, (i + j) + k == i + (j + k).
Proof.
    intros [n1 m1] [n2 m2] [n3 m3].
    simpl.
    rewrite plus_assoc with (o := n3).
    rewrite plus_assoc with (o := m3).
    reflexivity.
Qed.

Close Scope Integer_Scope.
