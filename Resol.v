(*Trying out soundness of resolution*)
From Coq Require Export List.
From Coq Require Import Nat.
(* From Coq Require Export Arith.EqNat. *)
Import ListNotations.

Inductive lit : Type :=
| pos : nat -> lit
| neg : nat -> lit.

Definition litEq x y : bool := 
    match x,y with
    | pos x, pos y => x=?y
    | neg x, neg y => x=?y
    | _,_          => false
    end.


Definition clause  := list lit.
Definition formula := list clause.
Definition val     := list nat.


(*Cannot use Prop here because it's not an inductive type in Coq and thus cannot be case analyzed*)
Fixpoint natIn  (n: nat) (v: list nat) : bool :=
    match v with
    | nil   => false
    | x::xs => if  n =? x then true else natIn n xs
    end.


Definition literalValue (l:lit) (v:val): bool :=
    match l with
    | neg n => negb (natIn n v)
    | pos n => natIn n v
    end.

(*Probably cleaner as folds*)
Fixpoint clauseValue (c: clause) (v:val) : bool :=
    match c with
    | nil   => false (*empty clause is never satisfiable*)
    | x::xs => orb (literalValue x v) (clauseValue xs v)
    end.

Fixpoint formulaValue (f: formula) (v:val) : bool :=
    match f with
    | nil   => true (*empty formula is always sat*)
    | x::xs => andb (clauseValue x v) (formulaValue xs v)
    end. 


(*Clean-up related functions*)
Fixpoint litIn (x : lit) (c: clause) : bool :=
    match c with
    | nil   => false
    | y::ys => if (litEq x y) then true else litIn x ys
    end.


Definition clauseSubset (c1 c2:clause)  : bool :=
    fold_left (fun acc l =>  andb (litIn l c2) (acc)) c1 true.
    
(*Checks for complimentary pairs of literals in clauses*)    
Fixpoint clauseCompPair (c:clause) : bool  :=
    match c with 
    | nil => false
    | (neg x) :: xs => orb (litIn (pos x) xs) (clauseCompPair xs) 
    | (pos x) :: xs => orb (litIn (neg x) xs) (clauseCompPair xs) 
    end.

Fixpoint compPairCleanup (f: formula) : formula :=
    match f with
    | nil     => nil 
    | x :: xs => if (clauseCompPair x) then (compPairCleanup xs) else x :: (compPairCleanup xs) 
    end.

(* Definition noCompPair  := . *)




(* Fixpoint dupCleanup (f : formula) : formula :=
    match f with
    | nil   => nil
    | x::xs => if *)