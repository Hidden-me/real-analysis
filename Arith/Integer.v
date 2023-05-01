Require Import RA.Arith.Natural.
Require Import Setoid.

Declare Scope Integer_Scope.
Delimit Scope Integer_Scope with z.

Open Scope Integer_Scope.

Inductive num : Type :=
| diff (n m : Natural.num).

Notation "n -- m" :=
    (diff n m)
    (at level 5, no associativity)
    : Integer_Scope.

Definition zero : num :=
    z -- z.

Definition eq (i j : num) : Prop :=
    match i, j with
    | n1 -- m1, n2 -- m2 => (n1 + m2 = m1 + n2)%n
    end.

Notation "i == j" :=
    (eq i j)
    (at level 70, no associativity)
    : Integer_Scope.

Notation "i != j" :=
    (~ eq i j)
    (at level 70, no associativity)
    : Integer_Scope.
    
Theorem eq_refl :
    forall i : num, i == i.
Proof.
    intros [n m].
    simpl.
    apply plus_comm.
Qed.

Theorem eq_symm :
    forall i j : num, i == j -> j == i.
Proof.
    intros [n1 m1] [n2 m2] H.
    simpl in *.
    symmetry.
    rewrite plus_comm with (n := m2).
    rewrite plus_comm with (n := n2).
    apply H.
Qed.

Theorem eq_trans :
    forall i j k : num, i == j -> j == k -> i == k.
Proof.
    intros [n1 m1] [n2 m2] [n3 m3] H1 H2.
    simpl in *.
    assert (H : ((n1 + m2) + (n2 + m3) = (m1 + n2) + (m2 + n3))%n).
    {
        rewrite H1.
        rewrite H2.
        reflexivity.
    }
    do 2 rewrite <- plus_assoc in H.
    rewrite plus_assoc with (n := n1) in H.
    rewrite plus_assoc with (n := m1) in H.
    rewrite plus_comm with (n := m2) in H.
    do 2 rewrite plus_comm with (m := (n2 + m2)%n) in H.
    do 2 rewrite plus_assoc with (n := (n2 + m2)%n) in H.
    apply plus_cancel_left in H.
    apply H.
Qed.

Add Parametric Relation : (num) (@eq)
    reflexivity proved by (eq_refl)
    symmetry proved by (eq_symm)
    transitivity proved by (eq_trans)
    as eq_rel.

Lemma num_norm_step :
    forall n m : Natural.num, (s n) -- (s m) == n -- m.
Proof.
    intros.
    simpl.
    do 2 rewrite plus_succ_comm.
    rewrite plus_comm.
    reflexivity.
Qed.

Theorem num_norm :
    forall i : num, exists n : Natural.num,
    i == n -- z \/ i == z -- n.
Proof.
    intros [n1 m1].
    generalize m1.
    clear m1.
    induction n1 as [| n1' IH]; intros m1.
    {
        exists m1.
        right.
        reflexivity.
    }
    {
        destruct m1 as [| m1'].
        {
            exists (s n1').
            left.
            reflexivity.
        }
        {
            assert (H := IH m1').
            destruct H as [n H].
            exists n.
            rewrite num_norm_step.
            apply H.
        }
    }
Qed.

Theorem zero_or_nonzero :
    forall i : num, i == zero \/ i != zero.
Proof.
    intros [n m].
    simpl.
    apply Natural.eq_or_neq.
Qed.

Definition neg (i : num) : num :=
    match i with
    | n -- m => m -- n
    end.

Notation "- i" :=
    (neg i)
    (at level 35, no associativity, i at level 35)
    : Integer_Scope.

Add Parametric Morphism : (@neg)
    with signature (@eq) ==> (@eq) as neg_mor.
Proof.
    intros [n1 m1] [n2 m2] H.
    simpl in *.
    symmetry.
    apply H.
Qed.

Definition plus (i j : num) : num :=
    match i, j with
    | n1 -- m1, n2 -- m2 => (n1 + n2)%n -- (m1 + m2)%n
    end.

Notation "i + j" :=
    (plus i j)
    (at level 50, left associativity)
    : Integer_Scope.

Notation "i - j" :=
    (plus i (neg j))
    (at level 50, left associativity)
    : Integer_Scope.

Add Parametric Morphism : (@plus)
    with signature (@eq) ==> (@eq) ==> (@eq) as plus_mor.
Proof.
    intros [n1 m1] [n2 m2] H1 [n3 m3] [n4 m4] H2.
    simpl in *.
    do 2 rewrite <- plus_assoc.
    rewrite plus_assoc with (n := n1).
    rewrite plus_assoc with (n := m1).
    rewrite plus_comm with (n := n3).
    rewrite plus_comm with (n := m3).
    do 2 rewrite <- plus_assoc.
    rewrite plus_assoc with (o := m4).
    rewrite plus_assoc with (o := n4).
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

Theorem plus_comm :
    forall i j : num, i + j == j + i.
Proof.
    intros [n1 m1] [n2 m2].
    simpl.
    rewrite plus_comm with (n := n1).
    rewrite plus_comm with (n := m1).
    apply plus_comm.
Qed.

Theorem plus_assoc :
    forall i j k : num, (i + j) + k == i + (j + k).
Proof.
    intros [n1 m1] [n2 m2] [n3 m3].
    simpl.
    rewrite plus_assoc with (o := n3).
    rewrite plus_assoc with (o := m3).
    apply Natural.plus_comm.
Qed.

Theorem eq_iff_diff_is_zero :
    forall i j : num, i == j <-> i - j == zero.
Proof.
    intros [n1 m1] [n2 m2].
    split; intros H; apply H.
Qed.

Definition times (i j : num) : num :=
    match i, j with
    | n1 -- m1, n2 -- m2 => (n1 * n2 + m1 * m2)%n -- (n1 * m2 + m1 * n2)%n
    end.

Notation "i * j" :=
    (times i j)
    (at level 40, left associativity)
    : Integer_Scope.

Lemma times_mor_right :
    forall i j k : num, j == k -> i * j == i * k.
Proof.
    intros [n1 m1] [n2 m2] [n3 m3] H.
    simpl in *.
    do 2 rewrite <- Natural.plus_assoc.
    rewrite Natural.plus_assoc with (n := (n1 * n2)%n).
    rewrite Natural.plus_assoc with (n := (n1 * m2)%n).
    rewrite Natural.plus_comm with (n := (m1 * m2)%n).
    rewrite Natural.plus_comm with (n := (m1 * n2)%n).
    do 2 rewrite <- Natural.plus_assoc.
    do 2 rewrite <- times_plus_dist_right.
    do 2 rewrite Natural.plus_assoc.
    do 2 rewrite <- times_plus_dist_right.
    rewrite H.
    reflexivity.
Qed.

Lemma times_mor_left :
    forall i j k : num, j == k -> j * i == k * i.
Proof.
    intros [n1 m1] [n2 m2] [n3 m3] H.
    simpl in *.
    rewrite Natural.plus_comm with (n := (n3 * m1)%n).
    rewrite Natural.plus_comm with (n := (n2 * m1)%n).
    do 2 rewrite <- Natural.plus_assoc.
    rewrite Natural.plus_assoc with (n := (n2 * n1)%n).
    rewrite Natural.plus_assoc with (n := (m2 * n1)%n).
    rewrite Natural.plus_comm with (n := (m2 * m1)%n).
    rewrite Natural.plus_comm with (n := (n2 * m1)%n).
    do 2 rewrite <- Natural.plus_assoc.
    do 2 rewrite <- times_plus_dist_left.
    do 2 rewrite Natural.plus_assoc.
    do 2 rewrite <- times_plus_dist_left.
    rewrite H.
    reflexivity.
Qed.

Add Parametric Morphism : (@times)
    with signature (@eq) ==> (@eq) ==> (@eq) as times_mor.
Proof.
    intros i1 j1 H1 i2 j2 H2.
    apply times_mor_left with (i := i2) in H1.
    rewrite H1.
    apply times_mor_right.
    apply H2.
Qed.

Theorem times_comm :
    forall i j : num, i * j == j * i.
Proof.
    intros [n1 m1] [n2 m2].
    simpl.
    do 2 rewrite times_comm with (n := n1).
    do 2 rewrite times_comm with (n := m1).
    rewrite Natural.plus_comm with (n := (n2 * m1)%n).
    apply Natural.plus_comm.
Qed.

Theorem times_zero_right :
    forall i : num, i * zero == zero.
Proof.
    intros [n1 m1].
    reflexivity.
Qed.

Theorem times_zero_left :
    forall i : num, zero * i == zero.
Proof.
    intros i.
    rewrite times_comm.
    apply times_zero_right.
Qed.

Theorem times_assoc :
    forall i j k : num, (i * j) * k == i * (j * k).
Proof.
    intros [n1 m1] [n2 m2] [n3 m3].
    unfold times.
    repeat rewrite times_plus_dist_left.
    repeat rewrite times_plus_dist_right.
    repeat rewrite <- times_assoc.
    rewrite Natural.plus_comm with (n := (m1 * n2 * m3)%n).
    rewrite Natural.plus_comm with (n := (m1 * n2 * n3)%n).
    do 4 rewrite <- Natural.plus_assoc.
    rewrite Natural.plus_assoc with (o := (n1 * m2 * m3)%n).
    rewrite Natural.plus_assoc with (o := (m1 * m2 * n3)%n).
    rewrite Natural.plus_comm with (n := (m1 * m2 * n3)%n).
    rewrite Natural.plus_assoc with (o := (n1 * m2 * n3)%n).
    rewrite Natural.plus_assoc with (o := (m1 * m2 * m3)%n).
    rewrite Natural.plus_comm with (n := (m1 * m2 * m3)%n).
    reflexivity.
Qed.

Theorem times_plus_dist_right :
    forall i j k : num, i * (j + k) == i * j + i * k.
Proof.
    intros [n1 m1] [n2 m2] [n3 m3].
    unfold plus, times.
    repeat rewrite times_plus_dist_right.
    repeat rewrite <- Natural.plus_assoc.
    rewrite Natural.plus_assoc with (n := (n1 * n2)%n).
    rewrite Natural.plus_comm with (n := (n1 * n3)%n).
    rewrite <- Natural.plus_assoc with (n := (n1 * n2)%n).
    rewrite Natural.plus_assoc with (n := (n1 * m2)%n).
    rewrite Natural.plus_comm with (n := (n1 * m3)%n).
    rewrite <- Natural.plus_assoc with (n := (n1 * m2)%n).
    reflexivity.
Qed.

Theorem times_plus_dist_left :
    forall i j k : num, (j + k) * i == j * i + k * i.
Proof.
    intros.
    do 3 rewrite times_comm with (j := i).
    apply times_plus_dist_right.
Qed.

Theorem times_neg_comm_right :
    forall i j : num, - (i * j) == i * (- j).
Proof.
    intros [n1 m1] [n2 m2].
    unfold times, neg.
    reflexivity.
Qed.

Theorem times_neg_comm_left :
    forall i j : num, - (i * j) == (- i) * j.
Proof.
    intros i j.
    do 2 rewrite times_comm with (j := j).
    apply times_neg_comm_right.
Qed.

Theorem times_nonzero :
    forall i j : num, i != zero -> j != zero -> i * j != zero.
Proof.
    intros i j H1 H2 H.
    assert (Hi := num_norm i).
    assert (Hj := num_norm j).
    destruct Hi as [ni [Hi | Hi]];
    destruct Hj as [nj [Hj | Hj]];
    rewrite Hi in *; rewrite Hj in *; simpl in *;
    rewrite plus_zero in H;
    rewrite times_zero in H;
    assert (Hc : (ni * nj)%n <> z) by
        (apply times_nonzero; auto);
    apply Hc; auto.
Qed.

Theorem times_zero_destruct_right :
    forall i j : num, i * j == zero -> i != zero -> j == zero.
Proof.
    intros i j H1 H2.
    assert (Hj := zero_or_nonzero j).
    destruct Hj as [Hj | Hj].
    {
        apply Hj.
    }
    {
        assert (H := times_nonzero i j H2 Hj).
        exfalso.
        apply H.
        apply H1.
    }
Qed.

Theorem times_zero_destruct_left :
    forall i j : num, i * j == zero -> j != zero -> i == zero.
Proof.
    intros i j H1 H2.
    rewrite times_comm in H1.
    eapply times_zero_destruct_right; eauto.
Qed.

Theorem times_zero_destruct :
    forall i j : num, i * j == zero -> i == zero \/ j == zero.
Proof.
    intros i j H.
    assert (Hi := zero_or_nonzero i).
    destruct Hi as [Hi | Hi].
    {
        left.
        apply Hi.
    }
    {
        right.
        eapply times_zero_destruct_right; eauto.
    }
Qed.

Theorem times_cancel_right :
    forall i j k : num,
    j * i == k * i -> i != zero -> j == k.
Proof.
    intros i j k H1 H2.
    apply eq_iff_diff_is_zero in H1.
    apply eq_iff_diff_is_zero.
    rewrite times_neg_comm_left in H1.
    rewrite <- times_plus_dist_left in H1.
    eapply times_zero_destruct_left; eauto.
Qed.

Theorem times_cancel_left :
    forall i j k : num,
    i * j == i * k -> i != zero -> j == k.
Proof.
    intros i j k H1 H2.
    do 2 rewrite times_comm with (i := i) in H1.
    eapply times_cancel_right; eauto.
Qed.

Close Scope Integer_Scope.
