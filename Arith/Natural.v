Inductive num : Type :=
| z
| s (n : num).

Declare Scope Natural_Scope.
Delimit Scope Natural_Scope with n.

Open Scope Natural_Scope.

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


Close Scope Natural_Scope.
