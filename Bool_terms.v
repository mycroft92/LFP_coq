(*Introduction to propositional logic*)
From Coq Require Import List.
Import ListNotations.
Inductive tm : Set :=
| tTrue  : tm 
| tFalse : tm
| tVar   : nat -> tm
(* | tNot   : tm -> tm *)
| tAnd   : tm -> tm -> tm
| tOr    : tm -> tm -> tm
| tImpl  : tm -> tm -> tm.
(*  *)

 Notation " ⊤ " := tTrue (at level 0).
 Notation " ⊥ " := tFalse (at level 0).

 (* Notation " ! A " := (tImpl A tFalse) (at level 75). *)
 Notation " ¬ A " := (tImpl A tFalse) (at level 75).

 Notation "A '&&&' B" := (tAnd A B) (at level 80, right associativity). 
 Notation "A '|||' B" := (tOr A B) (at level 85, right associativity).
 Notation "A '-->' B" := (tImpl A B)  (at level 30, right associativity).

Definition context := (list tm)%type.

(*Semantics of tm*)
Definition assignment := list nat.
Fixpoint truthAssign (A: assignment) (t:tm) : Prop :=
    match t with
    | tTrue       => True
    | tFalse      => False
    | tVar n      => In n A
    | p_1 &&& p_2 => (truthAssign A p_1) /\ (truthAssign A p_2)
    | p_1 ||| p_2 => (truthAssign A p_1) \/ (truthAssign A p_2)
    | p_1 --> p_2 => (truthAssign A p_1) -> (truthAssign A p_2)
    end.

Lemma tm_eq_dec : forall x y:tm, {x=y}+{x<>y}.
Proof.
    induction x; destruct y; try (now right); try (now left).
    - destruct (Nat.eq_dec n n0) eqn:E; subst; auto. right. congruence.
    - destruct (IHx1 y1) eqn:E1.
        + destruct (IHx2 y2) eqn:E2; subst; auto.
          * right. congruence.
        + right. congruence.
    - destruct (IHx1 y1) eqn:E1.
        + destruct (IHx2 y2) eqn:E2; subst; auto.
            * right. congruence.
        + right. congruence.
    - destruct (IHx1 y1) eqn:E1.
        + destruct (IHx2 y2) eqn:E2; subst; auto.
            * right. congruence.
        + right. congruence.
Qed.