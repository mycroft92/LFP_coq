(*Natural deduction formalisation*)
From Coq Require Import Lists.ListSet.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import List.
Import ListNotations.
From LogicPlayground Require Import Bool_terms.


Create HintDb NDhints.

Coercion tVar : nat >-> tm.
    

Reserved Notation " A '||-' B" ( at level 90).
Inductive deductionTree : context -> tm -> Prop :=
| cTrue: forall c, 
    c ||- tTrue
| cAssumption: forall c p,
    In p c ->
    c ||- p
| cAndI: forall c p_1 p_2,
    c ||- p_1 ->
    c ||- p_2 ->
    c ||- (p_1 &&& p_2)
| cAndEl: forall c p_1 p_2,
    c ||- (p_1 &&& p_2) ->
    c ||- p_1
| cAndEr: forall c p_1 p_2,
    c ||- (p_1 &&& p_2) ->
    c ||- p_2
| cOrIl: forall c p_1 p_2,
    c ||- p_1 ->
    c ||- p_1 ||| p_2
| cOrIr: forall c p_1 p_2,
    c ||- p_1 ->
    c ||- p_2 ||| p_1
| cOrE: forall c p_1 p_2 q,
    c ||- p_1 ||| p_2 ->
    p_1 :: c ||- q  ->
    p_2 :: c ||- q  ->
    c ||- q
| cImplI: forall c p_1 p_2,
    p_1 ::c ||- p_2 ->
    c ||- p_1 --> p_2 
| cImplE: forall c p_1 p_2,
    c ||- p_1 --> p_2 ->
    c ||- p_1 ->
    c ||- p_2
| cEInt: forall c p,
    c ||- tFalse ->
    c ||- p
where " A '||-' B" := (deductionTree A B).

Hint Constructors deductionTree: NDhints.
Hint Resolve in_eq: NDhints.
Hint Unfold In: NDhints.


Lemma ex1 : forall A, [] ||- A --> A.
Proof.
    auto with NDhints.
    (* intros.  apply cImplI. apply cAssumption. apply in_eq. *)
Qed.

Lemma ex2 : forall A B, [] ||- A --> (B--> A).
Proof.
    info_auto 8 with NDhints.
    (* intros. apply cImplI. apply cImplI. apply cAssumption. auto. *)
Qed.

Lemma ex3: forall A B C, [] ||- (A-->(B-->C)) --> (A-->B) --> (A-->C).
Proof.
    intros.
    apply cImplI. apply cImplI. apply cImplI.
    apply cImplE with (p_1:=B); 
     apply cImplE with (p_1:=A); apply cAssumption; auto with NDhints. (*both branches have same rule applications*)
    (* - apply cImplE with (p_1:=A); apply cAssumption; auto. *)
Qed.



Definition listSat (A:assignment) (c:context) := List.Forall (fun x => truthAssign A x) c.

Definition logicalConsequence (c:context) (p:tm) := forall A, listSat A c -> truthAssign A p.


Hint Unfold logicalConsequence listSat truthAssign: NDhints.
Hint Extern 1 (logicalConsequence _) => (unfold logicalConsequence in *): NDhints.
Hint Extern 1 (listSat _ _) => (unfold listSat in *): NDhints.
Hint Extern 1 (truthAssign _ _) => (unfold truthAssign in *; fold truthAssign in *): NDhints.
Hint Constructors Forall: NDhints.
Hint Resolve Forall_forall : NDhints.



Notation "Gamma '|=' p" := (logicalConsequence Gamma p) (at level 90).

Ltac sound_help:=
    match goal with
    | [H: In ?x ?y |- _] => (unfold logicalConsequence in * ; unfold truthAssign in *; fold truthAssign in *;
                 intros ; unfold listSat in * ) 
    | H: ?c ||- ?x  , 
      IH: ?c |= ?x |- _ => (unfold logicalConsequence in * ; unfold truthAssign in *; fold truthAssign in *; auto with NDhints ) 
    end.
Theorem Soundness: forall c p, c ||- p -> c |= p.
Proof.
    intros c p H. induction H.
    - auto with NDhints. 
    - sound_help. unfold listSat in H0. 
        rewrite -> Forall_forall in H0. auto. 
    - sound_help.  
    - sound_help. intros * H_1. apply IHdeductionTree in H_1. destruct H_1 as [H_1l H_1r]. auto.
    - sound_help. intros * H_1. apply IHdeductionTree in H_1. destruct H_1 as [H_1l H_1r]. auto.
    - sound_help.
    - sound_help.
    - sound_help. intros * H_1. apply IHdeductionTree1 in H_1 as E. 
      destruct E as [El | Er].
      * assert (listSat A (p_1::c)) as H_2. { apply Forall_cons; auto. }
        auto.
      * assert (listSat A (p_2::c)) as H_2. { apply Forall_cons; auto. }
        auto.
    - sound_help.
    - sound_help.
    - sound_help. intros * H_1. apply IHdeductionTree in H_1. destruct H_1.
Qed.

