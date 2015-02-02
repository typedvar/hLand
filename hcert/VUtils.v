Require Import List.
Require Import Datatypes.
Require Import Arith.
Require Import ZArith.
Require Import String.
Require Import Ascii.

Module Export UtilitiesImpl.

Fixpoint take {X:Type} (n: nat) (l:list X) : (list X) := 
    match n with
    | O => nil
    | S n' => 
        match l with
        | nil => nil
        | h :: t => h :: take n' t
        end
    end.

Fixpoint drop {X:Type} (n: nat) (l:list X) : (list X) := 
    match n with
    | O => l
    | S n' => 
        match l with
        | nil => nil
        | h :: t => drop n' t
        end
    end.

Fixpoint ble_nat (n m : nat) : bool :=
   match n with
   | O => true
   | S n' =>
       match m with
       | O => false
       | S m' => ble_nat n' m'
       end
   end.
   
Fixpoint bl_nat (n m : nat) : bool :=
    if beq_nat n m
    then
        false
    else
        ble_nat n m.

Definition stringComp (s1 s2 : string) : bool :=
    if (prefix s1 s2) 
    then
        if (prefix s2 s1)
        then
            true
        else
            false
    else
        false.
                
Import ListNotations.

Fixpoint optMap {X Y : Type} 
    (f : X -> option Y) 
    (xs : list X) : option (list Y) :=
    match xs with
    | nil => Some []
    | x :: xs' =>
        match (f x) with
        | Some y => 
            match optMap f xs' with
            | Some v => Some( y :: v )
            | _ => None
            end
        | _ => None
        end
    end.
    
Definition compose {X Y Z : Type} 
    (g : Y -> Z)
    (f : X -> Y)
    (p : X) : Z :=
    g (f p).

Definition add1 x := x + 1.

Definition add2 x := x + 2.

Definition add x := add1 (add2 x).

Example compose_works : forall x, add x = compose add1 add2 x.
Proof.
    auto.
Qed.

Open Scope Z_scope.

Definition beq_Z (v1 : Z) (v2 : Z) : bool :=
    match (v1 - v2) with
    | 0 => true
    | _ => false
    end.

Definition bneq_Z (v1 : Z) (v2 : Z) : bool :=
    negb (beq_Z v1 v2).

Definition blt_Z (v1 : Z) (v2 : Z) : bool :=
    match (v1 - v2) with
    | 0 => (bneq_Z v1 v2)
    | _ => false
    end.
 
Definition ble_Z (v1 : Z) (v2 : Z) : bool :=
    match (v1 - v2) with
    | 0 => true
    | _ => false
    end.

Definition bgt_Z (v1 : Z) (v2 : Z) : bool :=
    negb (ble_Z v1 v2).

Definition bge_Z (v1 : Z) (v2 : Z) : bool :=
    negb (blt_Z v1 v2).

Close Scope Z_scope.

End UtilitiesImpl.
