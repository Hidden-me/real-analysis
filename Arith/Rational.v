Require Import RA.Arith.Integer.
Require Import Setoid.

Declare Scope Rational_Scope.
Delimit Scope Rational_Scope with q.

Open Scope Rational_Scope.

Inductive num : Type :=
| quot (i j : Integer.num) (nz : (j != zero)%z).

Notation "i '//' j '~' nz" :=
    (quot i j nz)
    (at level 5, no associativity)
    : Rational_Scope.

Definition eq (p q : num) : Prop :=
    match p, q with
    | i1 // j1~nz1, i2 // j2~nz2 => (i1 * j2 == j1 * i2)%z
    end.

Notation "p == q" :=
    (eq p q)
    (at level 70, no associativity)
    : Rational_Scope.

Theorem eq_refl :
    forall p : num, p == p.
Proof.
    intros [i j nz].
    simpl.
    apply times_comm.
Qed.

Theorem eq_symm :
    forall p q : num, p == q -> q == p.
Proof.
    intros [i1 j1 nz1] [i2 j2 nz2] H.
    simpl in *.
    rewrite times_comm with (i := i2).
    rewrite times_comm with (i := j2).
    symmetry.
    apply H.
Qed.

Theorem eq_trans :
    forall p q r : num, p == q -> q == r -> p == r.
Proof.
    intros [i1 j1 nz1] [i2 j2 nz2] [i3 j3 nz3] H1 H2.
    simpl in *.
    assert (Hi2 := zero_or_nonzero i2).
    destruct Hi2 as [Hi2 | Hi2].
    {
        rewrite Hi2 in H1, H2.
        rewrite times_zero_left in H2.
        rewrite times_zero_right in H1.
        symmetry in H2.
        assert (Hi1 : (i1 == zero)%z) by
            (eapply times_zero_destruct_left; eauto).
        assert (Hi3 : (i3 == zero)%z) by
            (eapply times_zero_destruct_right; eauto).
        rewrite Hi1, Hi3.
        rewrite times_zero_left.
        rewrite times_zero_right.
        reflexivity.
    }
    {
        apply times_cancel_right with (i := (i2 * j2)%z).
        {
            do 2 rewrite times_assoc.
            do 2 rewrite times_comm with (j := (i2 * j2)%z).
            do 2 rewrite <- times_assoc with (j := (i2 * j2)%z).
            assert (Hr1 : (i1 * (i2 * j2) * j3 == i1 * j2 * (i2 * j3))%z).
            {
                rewrite times_comm with (i := i2).
                do 2 rewrite <- times_assoc.
                reflexivity.
            }
            rewrite Hr1.
            assert (Hr2 : (j1 * (i2 * j2) * i3 == j1 * i2 * (j2 * i3))%z).
            {
                do 2 rewrite <- times_assoc.
                reflexivity.
            }
            rewrite Hr2.
            rewrite H1, H2.
            reflexivity.
        }
        {
            apply times_nonzero; auto.
        }
    }
Qed.

Add Parametric Relation : (num) (@eq)
    reflexivity proved by (eq_refl)
    symmetry proved by (eq_symm)
    transitivity proved by (eq_trans)
    as eq_rel.

Close Scope Rational_Scope.
