Inductive num : Type :=
| z
| s (n : num).

Declare Scope Natural_Scope.
Delimit Scope Natural_Scope with n.

Open Scope Natural_Scope.

Theorem eq_or_neq :
    forall n m : num, n = m \/ n <> m.
Proof.
    induction n as [| n' IH].
    {
        destruct m as [| m'].
        {
            left.
            reflexivity.
        }
        {
            right.
            intros H.
            discriminate H.
        }
    }
    {
        intros [| m'].
        {
            right.
            intros H.
            discriminate H.
        }
        {
            assert (H := IH m').
            destruct H as [H | H].
            {
                rewrite H.
                left.
                reflexivity.
            }
            {
                right.
                intros Hc.
                apply H.
                injection Hc as Hc.
                apply Hc.
            }
        }
    }
Qed.

Fixpoint plus (n m : num) : num :=
    match m with
    | z => n
    | s m' => s (plus n m')
    end.

Notation "n + m" :=
    (plus n m)
    (at level 50, left associativity)
    : Natural_Scope.

Lemma plus_succ_comm :
    forall n m : num, (s n) + m = s (n + m).
Proof.
    induction m as [| m' IH].
    {
        reflexivity.
    }
    {
        simpl.
        rewrite IH.
        reflexivity.
    }
Qed.

Lemma plus_zero :
    forall n : num, z + n = n.
Proof.
    induction n as [| n' IH].
    {
        reflexivity.
    }
    {
        simpl.
        rewrite IH.
        reflexivity.
    }
Qed.

Theorem plus_comm :
    forall n m : num, n + m = m + n.
Proof.
    induction m as [| m' IH].
    {
        simpl.
        symmetry.
        apply plus_zero.
    }
    {
        simpl.
        rewrite plus_succ_comm.
        rewrite IH.
        reflexivity.
    }
Qed.

Theorem plus_assoc:
    forall n m o : num, (n + m) + o = n + (m + o).
Proof.
    intros.
    induction n as [| n' IH].
    {
        do 2 rewrite plus_zero.
        reflexivity.
    }
    {
        do 3 rewrite plus_succ_comm.
        rewrite IH.
        reflexivity.
    }
Qed.

Theorem plus_cancel_right :
    forall n m o : num, m + n = o + n -> m = o.
Proof.
    intros n m o H.
    induction n as [| n' IH].
    {
        simpl in H.
        apply H.
    }
    {
        simpl in H.
        apply IH.
        injection H as H'.
        apply H'.
    }
Qed.

Theorem plus_cancel_left :
    forall n m o : num, n + m = n + o -> m = o.
Proof.
    intros n m o H.
    do 2 rewrite plus_comm with (n := n) in H.
    eapply plus_cancel_right.
    apply H.
Qed.

Fixpoint times (n m : num) : num :=
    match m with
    | z => z
    | s m' => (times n m') + n
    end.

Notation "n * m" :=
    (times n m)
    (at level 40, left associativity)
    : Natural_Scope.

Lemma times_succ_dist :
    forall n m : num, (s n) * m = (n * m) + m.
Proof.
    induction m as [| m' IH].
    {
        reflexivity.
    }
    {
        simpl.
        rewrite IH.
        do 2 rewrite plus_assoc.
        rewrite plus_comm with (n := n).
        reflexivity.
    }
Qed.

Lemma times_zero :
    forall n : num, z * n = z.
Proof.
    induction n as [| n' IH].
    {
        reflexivity.
    }
    {
        simpl.
        rewrite IH.
        reflexivity.
    }
Qed.

Theorem times_comm :
    forall n m : num, n * m = m * n.
Proof.
    intros n m.
    induction m as [| m' IH].
    {
        rewrite times_zero.
        reflexivity.
    }
    {
        rewrite times_succ_dist.
        simpl.
        rewrite IH.
        reflexivity.
    }
Qed.

Theorem times_plus_dist_right :
    forall n m o : num, n * (m + o) = n * m + n * o.
Proof.
    intros.
    induction o as [| o' IH].
    {
        reflexivity.
    }
    {
        simpl.
        rewrite IH.
        apply plus_assoc.
    }
Qed.

Theorem times_plus_dist_left :
    forall n m o : num, (m + o) * n = m * n + o * n.
Proof.
    intros.
    do 3 rewrite times_comm with (m := n).
    apply times_plus_dist_right.
Qed.

Theorem times_assoc :
    forall n m o : num, (n * m) * o = n * (m * o).
Proof.
    intros.
    induction o as [| o' IH].
    {
        reflexivity.
    }
    {
        simpl.
        rewrite times_plus_dist_right.
        rewrite IH.
        reflexivity.
    }
Qed.

Theorem times_nonzero :
    forall n m : num, n <> z -> m <> z -> n * m <> z.
Proof.
    intros n m H1 H2 H.
    destruct n as [| n'];
    destruct m as [| m'];
    simpl in *; auto.
    {
        discriminate H.
    }
Qed.

Close Scope Natural_Scope.
