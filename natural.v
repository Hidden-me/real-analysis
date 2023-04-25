Module Natural.

Inductive num : Type :=
| z
| s (n : num).

Fixpoint plus (n m : num) : num :=
    match m with
    | z => n
    | s m' => s (plus n m')
    end.

Lemma plus_succ_comm :
    forall n m : num, plus (s n) m = s (plus n m).
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
    forall n : num, plus z n = n.
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
    forall n m : num, plus n m = plus m n.
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
    forall n m o : num, plus (plus n m) o = plus n (plus m o).
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

End Natural.