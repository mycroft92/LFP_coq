
Require Import Arith.
Require Import Arith.Compare_dec.
Require Import Coq.Relations.Relation_Definitions.
Require Import List.
Import ListNotations.
Require Import Arith.PeanoNat.

(*Syntax of tm exp*)
(*using De Bruijin indices*)

(*De Bruijin formulation taken from https://github.com/coq-contribs/tm/blob/master/Terms.v*)

Inductive tm : Type :=
| var : nat -> tm
| abs : tm -> tm
| app : tm -> tm -> tm.
Coercion var : nat >-> tm.
Notation " '\.' '[' x ']'" := (abs x).
Notation " x '>>' y" := (app x y) (at level 40, left associativity). 

Fixpoint freevars_rec (t: tm) (k:nat) : list nat :=
  match t with
  | var i   => if k <? i then [i] else []
  | abs l   => freevars_rec l (S k)
  | app l m => (freevars_rec l k) ++ (freevars_rec m k) 
  end.

Definition freevars t := freevars_rec t 0 .


(*auxiliary function to displace the indices to the proper level*)
Definition relocate (i k n : nat) :=
  match eq_nat_dec k i with
  | left _ (*k<=i*) => n+i  (*Free variable case*)
  | _      (*k> i*) => i    (*Bound variable case, nothing to do*)
  end.

(* lifting to term level,k=index being co\mpared and n is the current level of depth*)
Fixpoint lift_rec (t : tm ) (k:nat) (n:nat): tm := 
  match t with
  | var i     => var (relocate i k n) (*replace based on the number of scopes we passed*)
  | abs t'    => abs (lift_rec t' (S k) n) (*increment scope*)
  | app t1 t2 => app (lift_rec t1 k n) (lift_rec t2 k n)
  end.

Definition lift (n : nat) (t:tm) : tm := lift_rec t 0 n.

Definition insert_var (i k :nat) (v:tm) : tm :=
  match (lt_eq_lt_dec i k) with
  (*i<k*)| inleft (left _) => var i (*Nothing to do here*)
  (*i=k*)| inleft _        => lift (pred k) v(*substitute*)
  (*i>k*)| _               => var (pred i) (*a var got replaced, hence distance to the scope reduces by 1*)
  end.

Fixpoint subs_rec (t:tm) (k:nat) (v:tm) : tm :=
  match t with
  | var i     => insert_var i k v
  | abs t'    => (subs_rec t' (S k) v) (*increment whenever we cross scope*)
  | app t1 t2 => (app (subs_rec t1 k v) (subs_rec t2 k v))
  end.

Definition substitute t v := subs_rec t 0 v .


(*From here I follow the slides *)

Reserved Notation "t1 -->b t2" (at  level 50).
(*Definitions 15.4-15.5 clubbed into one inductive relation*)
Inductive beta1step : tm -> tm -> Prop :=
| appAbsStep : forall l m,
    (app (abs l) (m)) -->b (substitute (abs l) m)
| absStep    : forall l m,
    l -->b m ->
    abs l -->b abs m
| appLStep   : forall l m n,
    l -->b m ->
    app l n -->b app m n
| appRStep   : forall l m n,
    l -->b m ->
    app n l -->b app n m
  where "t1 -->b t2" := (beta1step t1 t2).

(*Generic form of multi step (reflexive transitive) relation*)
Inductive beta  : tm -> tm -> Prop :=
  | beta_refl   : forall (x : tm), beta x x
  | beta_step   : forall (x y  : tm),
                    beta1step x y ->
                    beta x y
  | beta_trans  : forall (x y z: tm), 
                  beta x y ->
                  beta y z ->
                  beta x z. 
Hint Constructors beta1step.
Hint Constructors beta.


Notation "l '-->*' m" := (beta l m) (at level 50).


Lemma betaAbsRed : forall l l', l -->* l' -> abs l -->* abs l'.
Proof.
    (*analyze how `l` can reach `l'` *)
    induction 1; 
    auto. (*if l =l' or if we reached from 1-step beta it's trivial*)
    apply beta_trans with (abs y); (*if `abs l -->* abs y and `abs y -->* absl'` use transitivity*)
    trivial.
Qed.
 

Lemma betaAppRedL : forall l l' m ,  l -->* l' ->  (app l m) -->* (app l' m).
Proof.
    induction 1; auto. apply beta_trans with (app y m); auto.
Qed.

Lemma betaAppRedR : forall l l' m ,  l -->* l' ->  (app m l) -->* (app m l').
Proof.
    induction 1; auto. apply beta_trans with (app m y); auto.
Qed.

Lemma betaAppRed : forall l l' m  m',  l -->* l' -> m -->* m' -> (app l m) -->* (app l' m').
Proof.
  intros. 
  apply (betaAppRedL l l' m) in H .
  apply (betaAppRedR m m' l') in H0. apply beta_trans with (app l' m); auto.
Qed.

Hint Resolve betaAppRed betaAppRedR betaAppRedL betaAbsRed.
(************Normalization related*************)
Fixpoint redux (t:tm) : Prop :=
  match t with
  | var i => False
  | app (abs L) (M) => True
  | app L M  => redux L \/ redux M
  | abs L => redux L
  end.

Example redTry : redux (abs (var 1)) -> False.
Proof.  auto. Qed.

Definition betaNF (t:tm) := redux t -> False.
Definition weakNormal (t:tm) := exists l, t -->* l /\ betaNF l.
(* Definition strongNormal (t:tm) := forall l, t -->* l ->  . *)

Notation K := (abs (abs (var 2))).
Notation I := (abs (var 1)).
Notation S := (abs (abs (abs (app (app (var 3) (var 1)) (app (var 2) (var 1)))))).
Notation W := (abs (app (var 1) (var 1))).
Definition OMEGA := (app (abs (app (var 1) (var 1))) (abs (app (var 1) (var 1)))).
(* Print S.
Print I.
Print W.
Print K. *)
Print OMEGA.


Example reduxOmega : redux OMEGA.
Proof. simpl. auto. Qed.

Compute (substitute W W).

Lemma W_noredex : forall l, W -->b l -> W = l.
Proof.
  intros. inversion H. inversion H1; inversion H6.
Qed.

  

Lemma omega_1step : forall l, OMEGA -->b l -> OMEGA = l.
Proof.
   intros. inversion H;
   try reflexivity; apply W_noredex in H3; rewrite <- H3; auto.
Qed.
   

(*Bad proof, don't know how to write it better*)
Lemma omega_red_omega : forall l,  OMEGA -->* l -> OMEGA = l.
Proof.
  intros. remember OMEGA as e.  induction H; auto. 
  - subst x; apply  omega_1step in H; auto.
  - subst x. assert (OMEGA = OMEGA). { auto. } apply IHbeta1 in  H1.
    symmetry in H1. apply IHbeta2 in H1. subst y. 
    assert  (OMEGA = OMEGA). { auto. } apply IHbeta1 in H1. auto.
Qed.


(*Notions of reduction*)

Reserved Notation "t1 '=b' t2" (at level 50, no associativity).
Inductive betaEquality : tm -> tm -> Prop :=
| basis : forall l m,
    l -->* m ->
    l =b m
| refl  : forall l,
    l =b l 
| symm  : forall l m,
    l =b m ->
    m =b l
| trans : forall l m n,
    l =b m ->
    m =b n ->
    l =b n
where "l =b n" := (betaEquality l n).
Hint Constructors betaEquality.

Lemma  BetaEqAbs: forall l m, l =b m -> abs l =b abs m.
Proof.
 induction 1; auto. apply trans with (\.[m]); auto.
Qed.

Lemma BetaEqAppL : forall l m n, l =b m -> app l n =b app m n.
Proof.
  induction 1;auto. apply trans with (m >> n); auto.
Qed.

Lemma BetaEqAppR : forall l m n, l =b m -> app n l =b app n m.
Proof.
  induction 1;auto. apply trans with (n >> m); auto.
Qed.

Lemma BetaEqApp : forall l l' m m', l =b l' -> m =b m' ->  app l m =b app l' m'.
Proof.
  intros. apply (BetaEqAppL l l' m) in H. apply (BetaEqAppR  m m' l') in H0.
  apply trans with (l' >> m); auto.
Qed.
Hint Resolve BetaEqAbs BetaEqAppL BetaEqAppR BetaEqApp.

(*To check if a relation is compatible*)
Definition compatible (R: relation tm) : Prop :=
forall l m, R l m -> R (abs l) (abs m) /\ 
forall l m n, R l m -> R (app l n) (app m n) /\
forall l m n, R l m -> R (app n l) (app n m).

Lemma betaEq_compatible : compatible betaEquality.
Proof.
  unfold compatible; split; auto.
Qed.

Lemma betaRed_compatible : compatible beta.
Proof.
  unfold compatible; split; auto.
Qed. 


Inductive CompatibleClosure  (R: relation tm) : relation tm :=
| baseComp : forall l m,
    R l m ->
    CompatibleClosure R l m
| absComp : forall l m ,
    CompatibleClosure R l m ->
    CompatibleClosure R (abs l) (abs m)
| appCompL : forall l m n,
    CompatibleClosure R l m ->
    CompatibleClosure R (app l n) (app m n)
| appCompR : forall l m n,
    CompatibleClosure R l m ->
    CompatibleClosure R (app  n l) (app n m).
Hint Constructors CompatibleClosure.

Lemma CompatibleClosure_is_compatible : forall R, compatible (CompatibleClosure R).
Proof.
  unfold compatible; split; auto.
Qed.

(*Eta reduction and confluence will come later*)

Compute freevars (\.[2 >> 1]).