From Coq Require Import List.
Import ListNotations.

Inductive subseq {A:Type} : list A -> list A -> Prop :=
| SubNil   : forall (l:list A), subseq  nil l
| SubCons1 : forall (s l:list A) (x:A), subseq  s l -> subseq s (x::l)
| SubCons2 : forall (s l: list A) (x:A), subseq s l -> subseq (x::s) (x::l). 

Lemma sub_nil : forall (A:Type) (l: list A) , subseq l nil <-> l=nil.
Proof.
 split; intros.
    - inversion H. reflexivity.
    - subst. apply SubNil.
Qed.

Lemma sub_nil2 : forall (A:Type) (l: list A) , subseq l nil <-> l=nil.
Proof.
 split.
    -  destruct l eqn:E; intros.
        *  reflexivity.
        * inversion H.

    - intros. subst. apply SubNil.
Qed.