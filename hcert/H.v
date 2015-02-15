(** * Formal Specification of H
We begin with the types that supported in H. As H is a higher order 
language it supports function objects through the [ArrowType]. 
Booleans and integers are supported through [BoolType] and [NumType] 
respectively. The [UnitType] denotes the singleton type [Unit] 
%\cite{Pierce:2002:TPL:509043}%. We use important definitions, proofs, 
and notations from the [SfLib] and [MoreStlc] modules of 
%\cite{pierce2013software}% in developing the formal specification of
%\textbf{H}%. Portions of the [SfLib] module with modifications are 
presented in %\S\ref{appendix:B:SfLib}%.

*)
(* begin hide *)
Require Import ZArith.
Require Import String.
Require Import Ascii.
Require Import List.
Require Import SfLib.
Require Import VUtils.

Module Export Hi.
(* end hide *)
(** Though we define the [ArrowType] as a value type %\textbf{H}%, for the sake 
of simplicity the implementation of the [G-machine] and the [R-machine] treats 
programs of base type. It should be noted that any program of %\textbf{arrow}% 
type is treated by providing it enough arguments so that the resultant 
application is of base type.

*)
Inductive typeH : Type :=
    | ArrowType : typeH -> typeH -> typeH
    | BoolType : typeH
    | NumType : typeH
    | UnitType : typeH.
(* begin hide *)
Tactic Notation "type_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "ArrowType"
    | Case_aux c "BoolType" 
    | Case_aux c "NumType"
    | Case_aux c "UnitType"
    ].
(* end hide *)
(** The inductive datatype [term_h] defines the terms in %\textbf{H}%. The first 
three allowed terms are 
%$\lambda$% terms - signifying variables [EVar], function application [EAp] and 
function abstraction [EAbs]. This is followed by the definition of numbers, 
booleans and arithmetic expressions. 

[EIf] introduces the if-then-else construct, and [ELet] specifies the [let] 
%\ldots% [in] construct. [EFix] represents the %\textbf{Y}% operator. 
We also introduce [EEq], a first class equality operator. These form the 
extensions to %$\lambda$%-calculus for [H]. 

Though we deal with integers, denoted by the Coq type [Z], and a limited set of 
arithmetic and boolean operators, extending this specification to include 
floating points and a more comprehensive set of operations should be 
straightforward. 

*)
Inductive term_h : Type :=
    | EVar : id -> term_h
    | EAp : term_h -> term_h -> term_h
    | EAbs : id -> typeH -> term_h -> term_h
    | ENum : Z -> term_h
    | EBool : bool -> term_h
    | EPlus : term_h -> term_h -> term_h
    | EMinus : term_h -> term_h -> term_h
    | EMult : term_h -> term_h -> term_h
    | EIf : term_h -> term_h -> term_h -> term_h
    | EUnit : term_h
    | ELet : id -> term_h -> term_h -> term_h
    | EFix : term_h -> term_h
    | EEq : term_h -> term_h -> term_h.
(* begin hide *)
Tactic Notation "term_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "EVar" 
    | Case_aux c "EAp" 
    | Case_aux c "EAbs"

    | Case_aux c "ENum" 
    | Case_aux c "EBool"

    | Case_aux c "EPlus" 
    | Case_aux c "EMinus" 
    | Case_aux c "EMult"

    | Case_aux c "EIf"
    | Case_aux c "EUnit"
    | Case_aux c "ELet" 
    | Case_aux c "EFix"
    | Case_aux c "EEq"
    ].
(* end hide *)
(** * Operational Semantics
In this section we present the operational semantics of %\textbf{H}%. As we have
previously outlined, the evaluation of a [H] program starts by translating 
it to an extended %$\lambda$%-calculus form, followed by evaluation of the generated 
%$\lambda$%-calculus terms through %$\beta$% reduction. The process of evaluating 
the generated %$\lambda$%-calculus terms are formally defined in the following 
sections.

** Substitution of %\textbf{H}% terms
%$\beta$%-reduction in H involves substituting the appropriate free variable
in an expression with the supplied term. Thus, %[%x := s%]% t implies 
substituting all free occurrences of the variable [x] in [t] with the 
expression [s]. 

%
\mathligson
\inference
{}
{[y \: := \: 8] (EAbs \: x  \: Z  \: (\: y \: + \: 5)) 
\: \Rightarrow \: (EAbs \: x  \: Z  \: (\: 8 \: + \: 5))}
\bigskip

\inference
{}
{[x \: := \: 5] (EAbs \: x  \: Z  \: (x \:  +  \: 5))
\: \Rightarrow \: (EAbs \: x  \: Z  \: (x \:  +  \: 5))}
\mathligsoff
\bigskip
%
To preseve laziness, the term %$(8 + 5)$% under the $\lambda$-abstraction in the 
first expression is not reduced to its sum. In the second expression, [x] is 
bound to the abstraction and the substitution has no effect.

We assume that appropriate $\alpha$-conversions have been 
applied before [subst] is invoked to avoid name-capture problems if any.

With these rules in place we define the recursive function [subst] as a Coq 
[Fixpoint]. The auxilliary function [eq_id_dec] %\S\ref{appendix:B:SfLib}% to 
ascertain whether the variable being substituted is bound to the expression.

*) 
Fixpoint subst (x : id) (s : term_h) (t : term_h) : term_h :=
    match t with
    | EVar x' => if eq_id_dec x x' then s else t
    | EAbs y T t1 => EAbs y T (if eq_id_dec x y then t1 else (subst x s t1))
    | EAp t1 t2 => EAp (subst x s t1) (subst x s t2)    
    | ENum v => ENum v
    | EBool x => EBool x
    | EPlus t1 t2 => EPlus (subst x s t1) (subst x s t2)
    | EMinus t1 t2 => EMinus (subst x s t1) (subst x s t2)
    | EMult t1 t2 => EMult (subst x s t1) (subst x s t2)
    | EIf c t1 t2 => EIf (subst x s c) (subst x s t1) (subst x s t2)
    | EUnit => EUnit
    | ELet y t1 t2 => if eq_id_dec x y
        then ELet y (subst x s t1) t2
        else ELet y (subst x s t1) (subst x s t2)
    | EFix t => EFix (subst x s t)
    | EEq t1 t2 => EEq (subst x s t1) (subst x s t2)
    end.
(* begin hide *)
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).
(* end hide *)
(** Evaluation of an [H] program starts by evaluating the [main] expression and 
terminates when a value is obtained; which represents the program's value. 
Function objects are denoted in H through %$\lambda$%-abstractions and 
belong to the set of first class values in H. Similar is case for integers 
and booleans. 
We inductively define a proposition [value] for representing terms that are 
values. 

*)
Inductive value : term_h -> Prop :=
    | v_abs : forall x T11 t12, value (EAbs x T11 t12)
    | v_int : forall x, value (ENum x)
    | v_bool : forall x, value (EBool x)
    | v_unit : value EUnit.

Hint Constructors value.
(** ** Types in %\textbf{H}%
The type of an expression is determined with respect to a
[context], a partial map over types in %\textbf{H}%, [typeH]. This function 
given a %\textbf{H}% term either returns the type of the 
term within a Coq [option] monad, or returns [option None] if the term is not
present in the map. [partial_map] is defined in the [SfLib] module and is 
reproduced in %\S\ref{appendix:B:SfLib}%. 

*) 
Definition context := partial_map typeH.
(** printing \ %% *)
(** printing in $\in$ *)
(** printing Gamma $\Gamma$ *)
(* begin hide *)
Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
(* end hide *)
Inductive has_type : context -> term_h -> typeH -> Prop :=
    | T_Var : forall Gamma x T,
        Gamma x = Some T ->
        Gamma |- (EVar x) \in T

    | T_Abs : forall Gamma x T11 T12 t12,
        (extend Gamma x T11) |- t12 \in T12 -> 
        Gamma |- (EAbs x T11 t12) \in (ArrowType T11 T12)
(** The type of an abstraction is [ArrowType T11 T12], signifying a function
that takes a term with type [T11] as argument and returns a term with type 
[T12]. The [extend] function takes an existing context and a type-map
and adds the type-map to the context. A type-map is a pair of a term and 
its type.

*)        
    | T_App : forall T1 T2 Gamma t1 t2,
        Gamma |- t1 \in (ArrowType T1 T2) -> 
        Gamma |- t2 \in T1 -> 
        Gamma |- (EAp t1 t2) \in T2
(** For function applications, the type of the resulting term is determined by 
the type of the function being applied. As the return type of the 
function abstraction [t1] is type [T2], and given [t2] is of type [T1], 
implying a type conforming function application, the type of the result is 
indeed [T2].

*)
    | T_Num : forall Gamma n1,
        Gamma |- (ENum n1) \in NumType
    | T_Bool : forall Gamma n1,
        Gamma |- (EBool n1) \in BoolType

    | T_Plus: forall Gamma t1 t2,
        Gamma |- t1 \in NumType ->
        Gamma |- t2 \in NumType ->
        Gamma |- (EPlus t1 t2) \in NumType
    | T_Minus: forall Gamma t1 t2,
        Gamma |- t1 \in NumType ->
        Gamma |- t2 \in NumType ->
        Gamma |- (EMinus t1 t2) \in NumType
    | T_Mult : forall Gamma t1 t2,
        Gamma |- t1 \in NumType ->
        Gamma |- t2 \in NumType ->
        Gamma |- (EMult t1 t2) \in NumType
(** For arithmetic operations, the type of result is always in [NumType], 
provided a valid arithmetic expression is being evaluated. 

*)
    | T_If : forall Gamma t1 t2 t3 T1,
        Gamma |- t1 \in BoolType ->
        Gamma |- t2 \in T1 ->
        Gamma |- t3 \in T1 ->
        Gamma |- (EIf t1 t2 t3) \in T1
    | T_Unit : forall Gamma,
        Gamma |- EUnit \in UnitType
    | T_Let : forall Gamma x t1 t2 T1 T2,
        Gamma |- t1 \in T1 ->
        (extend Gamma x T1) |- t2 \in T2 -> 
        Gamma |- (ELet x t1 t2) \in T2
    | T_Fix : forall Gamma t1 T1,
        Gamma |- t1 \in (ArrowType T1 T1) ->
        Gamma |- EFix t1 \in T1
(** Similarly, the fix point operator [EFix] has a result type [T1]. Note the 
function [t1], whose fixpoint is being calculated always has the same input
and return types. 

*)
    | T_Eq : forall Gamma t1 t2,
        Gamma |- t1 \in NumType ->
        Gamma |- t2 \in NumType ->
        Gamma |- (EEq t1 t2) \in BoolType
where "Gamma |- t \in T" := (has_type Gamma t T).

Hint Constructors has_type.
(* begin hide *)
Tactic Notation "has_type_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "T_Var" 
    | Case_aux c "T_Abs" 
    | Case_aux c "T_App" 

    | Case_aux c "T_Num" 
    | Case_aux c "T_Bool"

    | Case_aux c "T_Plus"
    | Case_aux c "T_Minus"
    | Case_aux c "T_Mult" 

    | Case_aux c "T_If"
    | Case_aux c "T_Unit"
    | Case_aux c "T_Let" 
    | Case_aux c "T_Fix"
    | Case_aux c "T_Eq"
    ].
(* end hide *)
(** ** Free occurrences during substitution
The substitution principle described earlier took into account 
whether the variable was free within an expression prior to application of 
the substitution rule. The inductive proposition [free_in_term] formalizes 
this notion for a variable [x] within a [term_h]. These rules are equivalent
to those in %$\lambda$%-calculus, with the exception of [if], [fix], [let] 
and [eq] which form the extensions required for %\textbf{H}%.

*)
Inductive free_in_term : id -> term_h -> Prop :=
    | fit_var : forall x,
        free_in_term x (EVar x)

    | fit_app1 : forall x t1 t2,
        free_in_term x t1 -> free_in_term x (EAp t1 t2)
    | fit_app2 : forall x t1 t2,
        free_in_term x t2 -> free_in_term x (EAp t1 t2)
(** In this proposition, we define that if an id [x] is free in any of the terms
[t1] or [t2], then it is also free in the application [t1 t2].

We define the _freeness_ of an identifier within allowed 
%\textbf{H}% terms in a similar fashion.

*)
    | fit_abs : forall x y T11 t12,
        y <> x  ->
        free_in_term x t12 ->
        free_in_term x (EAbs y T11 t12)

    | fit_plus1 : forall x t1 t2,
        free_in_term x t1 -> 
        free_in_term x (EPlus t1 t2)
    | fit_plus2 : forall x t1 t2,
        free_in_term x t2 -> 
        free_in_term x (EPlus t1 t2)

    | fit_minus1 : forall x t1 t2,
        free_in_term x t1 -> 
        free_in_term x (EMinus t1 t2)
    | fit_minus2 : forall x t1 t2,
        free_in_term x t2 -> 
        free_in_term x (EMinus t1 t2)

    | fit_mult1 : forall x t1 t2,
        free_in_term x t1 -> 
        free_in_term x (EMult t1 t2)
    | fit_mult2 : forall x t1 t2,
        free_in_term x t2 -> 
        free_in_term x (EMult t1 t2)

    | fit_if1 : forall x t1 t2 t3,
        free_in_term x t1 -> 
        free_in_term x (EIf t1 t2 t3)
    | fit_if2 : forall x t1 t2 t3,
        free_in_term x t2 -> 
        free_in_term x (EIf t1 t2 t3)
    | fit_if3 : forall x t1 t2 t3,
        free_in_term x t3 -> 
        free_in_term x (EIf t1 t2 t3)

    | fit_let1 : forall x y t1 t2,
        free_in_term x t1 -> free_in_term x (ELet y t1 t2)
    | fit_let2 : forall x y t1 t2,
        x <> y ->
        free_in_term x t2 ->
        free_in_term x (ELet y t1 t2)
(** For [let] expressions, %$let\:y\: =\: t1\: in\: t2$%, we say %$x$% in 
free in this expression, iff %$x$% is not equal to %$y$% and %$x$%
is free in the expression %$t2$%.

*)
    | fit_fix : forall x t,
        free_in_term x t -> free_in_term x (EFix t)

    | fit_eq1 : forall x t1 t2,
        free_in_term x t1 -> 
        free_in_term x (EEq t1 t2)
    | fit_eq2 : forall x t1 t2,
        free_in_term x t2 -> 
        free_in_term x (EEq t1 t2).

Hint Constructors free_in_term.
(** *** Context Invariance
We define an auxillary lemma [context_invariance] to prove type preservation 
in both big-step and small-step semantics. This lemma shows that given 
two equivalent contexts [Gamma], [Gamma]' and a term [t], if the type of [t] 
in [Gamma] is [S], then the type of [t] in [Gamma]' must be [S].

The Coq tactic notation %\textbf{Case\_aux}% has been used to increase 
the readability of proofs and report inadvertent omission of proof cases. 

*)
Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S  ->
     (forall x, free_in_term x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in S.
Proof with eauto.
    intros. 
    generalize dependent Gamma'.
    has_type_cases (induction H) Case; 
    intros Gamma' Heqv...
    Case "T_Var".
        apply T_Var... rewrite <- Heqv...
    Case "T_Abs".
        apply T_Abs... apply IHhas_type. intros y Hafi.
        unfold extend. 
        destruct (eq_id_dec x y)...
    Case "T_App".
        eapply T_App...
    Case "T_Plus".
        apply T_Plus...
    Case "T_Minus".
        apply T_Minus...
    Case "T_Mult".
        apply T_Mult...
    Case "T_If".
        apply T_If...
    Case "T_Let".
        eapply T_Let...
        apply IHhas_type2. 
        intros. 
        unfold extend.
        destruct (eq_id_dec x x0)...
    Case "T_Eq".
        apply T_Eq...
Qed.
(** The following important lemma states that for a term [t] with type [T] in 
context %$\Gamma$%, if [t] contains a free variable [x], then [x] also has
some type [T'] in %$\Gamma$%.  

*)
Lemma free_in_context : forall x t T Gamma,
    free_in_term x t ->
    Gamma |- t \in T ->
    exists T', Gamma x = Some T'.
Proof with eauto.
    intros x t T Gamma Hafi Htyp.
    has_type_cases (induction Htyp) Case; inversion Hafi; subst...
    Case "T_Abs".
        destruct IHHtyp as [T' Hctx]... exists T'.
        unfold extend in Hctx. 
        rewrite neq_id in Hctx...
    Case "T_Let".
        destruct IHHtyp2 as [T' Hctx]... exists T'.
        unfold extend in Hctx. 
        rewrite neq_id in Hctx...
Qed.
(** *** Type preservation in substitution
In order to prove type preservation, we show that the substitution
function preserved the type of a term in a given context %$\Gamma$%.

*)
Lemma substitution_preserves_typing : forall Gamma x U v t S,
    (extend Gamma x U) |- t \in S  ->
    empty |- v \in U   ->
    Gamma |- ([x:=v]t) \in S.
Proof with eauto.
    intros Gamma x U v t S Htypt Htypv. 
    generalize dependent Gamma. 
    generalize dependent S.
    term_cases (induction t) Case;
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
    Case "EVar".
        simpl. rename i into y.
        destruct (eq_id_dec x y).
        SCase "x = y".
            subst.
            unfold extend in H1. rewrite eq_id in H1. 
            inversion H1; subst. clear H1.
            eapply context_invariance...
            intros x Hcontra.
            destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
            inversion HT'.
        SCase "x != y".
            apply T_Var... unfold extend in H1. rewrite neq_id in H1...
    Case "EAbs".
        rename i into y. rename t into T11.
        apply T_Abs...
        destruct (eq_id_dec x y).
        SCase "x = y".
            eapply context_invariance...
            subst.
            intros x Hafi. unfold extend.
            destruct (eq_id_dec y x)...
        SCase "x != y".
            apply IHt. eapply context_invariance...
            intros z Hafi. unfold extend.
            destruct (eq_id_dec y z)...
            subst. rewrite neq_id...
    Case "ELet".
        destruct (eq_id_dec x i);
        eapply T_Let; eauto; eapply context_invariance...
        intros. unfold extend. subst. destruct (eq_id_dec i x0)...
        apply IHt2. eapply context_invariance...
        intros. unfold extend. destruct (eq_id_dec i x0); eauto.
        subst. rewrite neq_id...
Qed.
(** ** Big-step semantics
The big-step semantics %\cite{Kahn:1987:NS:646503.696269}% of %\textbf{H}% 
is relatively straightforward and relies on the [subst] function to obtain 
the value of non-trivial terms. We define this with the relation [bigStep] 
and denote it using %$\Downarrow$%. 

*)
(* begin hide *)
Module BigStep.
(* end hide *)
(** printing ~~> %$\Downarrow$% *)
(* begin hide *)
Reserved Notation "t1 '~~>' t2" (at level 40).
(* end hide *)
Inductive bigStep : term_h -> term_h -> Prop :=
    | BST_Num : forall z,
         ENum z ~~> ENum z

    | BST_Bool : forall b,
         EBool b ~~> EBool b
(** For function application, occurrences of the bound variable [x] in the 
body [t12] is substituted by the supplied expression [t13].

*)
    | BST_App : forall x T11 t12 t13,
         (EAp (EAbs x T11 t12) t13) ~~> [x := t13]t12
(** The arithmetic operation [plus] is defined as follows: for two expressions, 
[t1] and [t2], if [t1] steps to a number [z1] and [t2] steps to a number [z2],
then the expression [t1 + t2] steps to [z1 + z2]. In this 
formalization of %\textbf{H}%, we convert infix operators to their prefix 
forms before evaluation. The treatment for minus and multiplication 
operators are similar.

*)
    | BST_Plus : forall t1 z1 t2 z2,
         t1 ~~> (ENum z1) ->
         t2 ~~> (ENum z2) ->
         (EPlus t1 t2) ~~> (ENum (z1 + z2))

    | BST_Minus : forall t1 z1 t2 z2,
         t1 ~~> (ENum z1) ->
         t2 ~~> (ENum z2) ->
         (EMinus t1 t2) ~~> (ENum (z1 - z2))

    | BST_Mult : forall t1 z1 t2 z2,
         t1 ~~> (ENum z1) ->
         t2 ~~> (ENum z2) ->
         (EMult t1 t2) ~~> (ENum (z1 * z2))
(** The semantics for [if] is defined as follows:

*)
    | BST_IfTrue : forall t t1 t2,
        t ~~> (EBool true) ->
        (EIf t t1 t2) ~~> t1

    | BST_IfFalse : forall t t1 t2,
        t ~~> (EBool false) ->
        (EIf t t1 t2) ~~> t2
(** For [let] expressions, the following rule holds: 

*)
    | BST_Let : forall x t1 v t2,
         value v ->
         t1 ~~> v -> 
         (ELet x t1 t2) ~~> [x := v]t2

    | BST_Fix: forall xf T11 t12,
        EFix (EAbs xf T11 t12) ~~> [xf := EFix (EAbs xf T11 t12)]t12        

    | BST_Eq : forall t1 z1 t2 z2,
         t1 ~~> (ENum z1) ->
         t2 ~~> (ENum z2) ->
         (EEq t1 t2) ~~> EBool (beq_Z z1 z2)

where "t1 ~~> t2" := (bigStep t1 t2).
(* begin hide *)
Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BST_Num"
    | Case_aux c "BST_Bool"
    | Case_aux c "BST_App"
    | Case_aux c "BST_Plus"
    | Case_aux c "BST_Minus"
    | Case_aux c "BST_Mult"
    | Case_aux c "BST_IfTrue"
    | Case_aux c "BST_IfFalse"
    | Case_aux c "BST_Let"
    | Case_aux c "BST_Fix"
    | Case_aux c "BST_Eq"
  ].        
(* end hide *)
(** To demonstrate reduction of sample programs, we define the 
multistep relation (%$\Downarrow$*%) in terms of big-step semantics. [multi] is
defined in Appendix B %\S\ref{appendix:B}%.

*)
Notation multistep := (multi bigStep).
(* begin hide *)
Notation "t1 ~~>* t2" := (multistep t1 t2) (at level 40).
Hint Constructors bigStep.
(* end hide *)
(** printing ~~>* %$\Downarrow$*% *)
(** Each variable in H is assigned a unique [Id] represented by a [nat]. The 
properties of [Id] and their proofs are enumerated in 
%\S\ref{appendix:B:SfLib}%. The [id]s used in the sample programs are defined below.

*)
(* begin hide *)
Module BigStepSamples.
(* end hide *)

Notation a := (Id 0).
Notation f := (Id 1).
Notation g := (Id 2).
Notation x := (Id 3).
Notation y := (Id 4).
Notation n := (Id 5).
Notation m := (Id 6).

(* begin hide *)
Hint Extern 2 (has_type _ (EAp _ _) _) => 
  eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.

Module Numtest.

Definition arith_test :=
   (EPlus 
       (EPlus 
           (ENum 0) 
           (EMult 
               (ENum 5) 
               (ENum 1))) 
       (ENum 0)).

Example typechecks :
  (@empty typeH) |- arith_test \in NumType.
Proof.
  unfold arith_test.
  auto 10.
Qed.

Example arith_test_reduces :
  arith_test ~~>* ENum 5.
Proof.
  unfold arith_test.
  eapply multi_step. 
  apply BST_Plus.
  apply BST_Plus. 
  apply BST_Num.
  apply BST_Mult. 
  apply BST_Num.
  apply BST_Num.
  apply BST_Num.
  simpl.
  apply multi_refl.
Qed.

Definition eqTest :=
    EEq (ENum 5) (ENum 1).

Example eqTestTypeChecks :
  (@empty typeH) |- eqTest \in BoolType.
Proof.
  unfold eqTest.
  auto 10.
Qed.

Example eqTestReduces :
    eqTest ~~>* EBool false.
Proof.
    unfold eqTest. 
    normalize.
Qed.

Definition basicIfTest :=
    EIf 
        (EBool false)
        (ENum 1) 
        (ENum 0).

Example basicIfTestTypeChecks :
    (@empty typeH) |- basicIfTest \in NumType.
Proof.
    unfold basicIfTest.
    auto 10.
Qed.

Example basicIfTestReduces :
    basicIfTest ~~>* ENum 0.
Proof.
    unfold basicIfTest.
    normalize.
Qed.
(* end hide *)

Definition ifTest :=
    EIf 
        (EEq (ENum 5) (ENum 1))
        (ENum 1) 
        (ENum 0).

Example ifTestTypeChecks :
    (@empty typeH) |- ifTest \in NumType.
Proof.
    unfold ifTest.
    auto 10.
Qed.

Example ifTestReduces :
    ifTest ~~>* ENum 0.
Proof.
    unfold ifTest.
    eapply multi_step.
    apply BST_IfFalse.
    apply BST_Eq with (z1 := 5%Z) (z2 := 1%Z).
    apply BST_Num.
    apply BST_Num.
    apply multi_refl.
Qed.

(* begin hide *)
Definition num_test0 :=
    EIf 
        (EEq (ENum 5) (EPlus (ENum 4%Z) (ENum 1%Z)))
        (EMult (ENum 5) (ENum 6)) 
        (ENum 0).

Example num_test0_typechecks :
    (@empty typeH) |- num_test0 \in NumType.
Proof.
    unfold num_test0.
    auto 10.
Qed.

Example num_test0_reduces :
    num_test0 ~~>* ENum 30.
Proof.
    unfold num_test0.
    eapply multi_step.
    apply BST_IfTrue.
    apply BST_Eq with (z1 := 5%Z) (z2 := 5%Z).
    apply BST_Num.
    apply BST_Plus with (z1 := 4%Z) (z2 := 1%Z).
    apply BST_Num.
    apply BST_Num.
    normalize.
Qed.

End Numtest.

Module LetTest.
(* end hide *)

Definition let_test :=
    ELet
        x (ENum 6)
        (EPlus (EVar x) (ENum 1)).

Example let_test_typechecks :
  (@empty typeH) |- let_test \in NumType.
Proof. unfold let_test. eauto 15. Qed.

Example let_test_reduces :
  let_test ~~>* ENum 7.
Proof. unfold let_test. normalize. Qed.

(* begin hide *)
Definition let_test1 :=
    ELet x (EMinus (ENum 1) (ENum 5))
        (EMult (EVar x) (ENum 5)).

Example let_test1_reduces :
    let_test1 ~~>* ENum (-20).
Proof.
    unfold let_test1. normalize. Qed.

End LetTest.

Module AppTest.
(* end hide *)

Definition square_app_test :=
    EAp (EAbs x NumType (EMult (EVar x) (EVar x))) (ENum 5).

Example square_app_test_reduces :
    square_app_test ~~>* ENum 25.
Proof.
    unfold square_app_test.
    normalize.
Qed.

(* begin hide *)
End AppTest.

Module FixTest1.

Definition fact :=
    EFix
        (EAbs f (ArrowType NumType NumType)
        (EAbs a NumType
            (EIf 
                (EEq (EVar a) (ENum 0))
                (ENum 1)
                (EMult 
                    (EVar a) 
                    (EAp (EVar f) (EMinus (EVar a) (ENum 1))))))).

Example fact_typechecks :
  (@empty typeH) |- fact \in (ArrowType NumType NumType).
Proof. unfold fact. auto 10. 
Qed.

(*
Example fact_example: 
    (EAp fact (ENum 4)) ~~>* (ENum 24).
Proof. unfold fact.
    eapply multi_step.
    eapply BST_App.
    normalize. 
Qed.
*)

End FixTest1.
End BigStepSamples.
(* end hide *)
(** *** Type preservation in big-step
We now prove that the big-step semantics defined for a program preserves 
its type. The auxilliary lemmas defined earlier are applied to prove this 
theorem.

*)
Theorem big_step_preservation : forall t t' T,
     empty |- t \in T  ->
     t ~~> t'  ->
     empty |- t' \in T.
Proof with eauto.
    intros t t' T HT.
    remember (@empty typeH) as Gamma. generalize dependent HeqGamma.
    generalize dependent t'.
    has_type_cases (induction HT) Case; 
    intros t' HeqGamma HE; subst; inversion HE; subst...
    Case "T_App".
        inversion HE; subst...
        SCase "BST_AppAbs".
            apply substitution_preserves_typing with T1...
            inversion HT1...
    Case "T_Let".
        eapply substitution_preserves_typing...
    Case "T_Fix".
        eapply substitution_preserves_typing...
        inversion HT...
Qed.

End BigStep.
(** ** Small-step semantics
The small step semantics of H takes into account the single steps the
machine takes to obtain the final result during the evaluation of program. 
The step rules are as follows:

*)
(* begin hide *)
Module SmallStep.
(* end hide *)
(** printing ==> %$\ensuremath{\Longrightarrow}$% *)
(* begin hide *)
Reserved Notation "t1 '==>' t2" (at level 40).
(* end hide *)
Inductive smallStep : term_h -> term_h -> Prop :=
    | SST_AppAbs : forall x T11 t12 v2,
         value v2 -> 
         (EAp (EAbs x T11 t12) v2) ==> [x := v2]t12
    | SST_App1 : forall t1 t1' t2,
         t1 ==> t1' -> 
         (EAp t1 t2) ==> (EAp t1' t2)
    | SST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (EAp v1 t2) ==> (EAp v1 t2')
(** It is to be noted that function application in this semantics follows normal
order evaluation.

*)          
    | SST_Plus1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (EPlus t1 t2) ==> (EPlus t1' t2)
    | SST_Plus2 : forall v1 t2 t2',
         t2 ==> t2' ->
         (EPlus v1 t2) ==> (EPlus v1 t2')
    | SST_Plus : forall z1 z2,
        (EPlus (ENum z1) (ENum z2)) ==> (ENum (z1 + z2))

    | SST_Minus1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (EMinus t1 t2) ==> (EMinus t1' t2)
    | SST_Minus2 : forall v1 t2 t2',
         t2 ==> t2' ->
         (EMinus v1 t2) ==> (EMinus v1 t2')
    | SST_Minus : forall z1 z2,
        (EMinus (ENum z1) (ENum z2)) ==> (ENum (z1 - z2))

    | SST_Mult1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (EMult t1 t2) ==> (EMult t1' t2)
    | SST_Mult2 : forall v1 t2 t2',
         t2 ==> t2' ->
         (EMult v1 t2) ==> (EMult v1 t2')
    | SST_Mult : forall z1 z2,
        (EMult (ENum z1) (ENum z2)) ==> (ENum (z1 * z2))

    | SST_IfStep : forall t t' t1 t2,
        t ==> t' ->
        (EIf t t1 t2) ==> (EIf t' t1 t2)
    | SST_IfTrue : forall t1 t2,
        (EIf (EBool true) t1 t2) ==> t1
    | SST_IfFalse : forall t1 t2,
        (EIf (EBool false) t1 t2) ==> t2

    | SST_LetStep : forall x t1 t1' t2,
         t1 ==> t1' ->
         (ELet x t1 t2) ==> (ELet x t1' t2)
    | SST_Let : forall x v t,
         value v ->
         (ELet x v t) ==> [x := v]t

    | SST_FixStep : forall t1 t1',
        t1 ==> t1' ->
        (EFix t1) ==> (EFix t1')
    | SST_FixAbs : forall xf T11 t12,
        EFix (EAbs xf T11 t12) ==> [xf := EFix (EAbs xf T11 t12)]t12        

    | SST_Eq1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (EEq t1 t2) ==> (EEq t1' t2)
    | SST_Eq2 : forall v1 t2 t2',
         t2 ==> t2' ->
         (EEq v1 t2) ==> (EEq v1 t2')
    | SST_Eq : forall z1 z2,
        (EEq (ENum z1) (ENum z2)) ==> EBool (beq_Z z1 z2)

where "t1 '==>' t2" := (smallStep t1 t2).
(* begin hide *)
Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SST_AppAbs"
 
    | Case_aux c "SST_App1" 
    | Case_aux c "SST_App2"

    | Case_aux c "SST_Plus1"
    | Case_aux c "SST_Plus2"
    | Case_aux c "SST_Plus"

    | Case_aux c "SST_Minus1"
    | Case_aux c "SST_Minus2"
    | Case_aux c "SST_Minus"

    | Case_aux c "SST_Mult1"
    | Case_aux c "SST_Mult2"
    | Case_aux c "SST_Mult"

    | Case_aux c "SST_IfStep"
    | Case_aux c "SST_IfTrue"
    | Case_aux c "SST_IfFalse"

    | Case_aux c "SST_LetStep"
    | Case_aux c "SST_Let"

    | Case_aux c "SST_FixStep"
    | Case_aux c "SST_FixAbs"

    | Case_aux c "SST_Eq1"
    | Case_aux c "SST_Eq2"
    | Case_aux c "SST_Eq"
  ].        
Hint Extern 2 (has_type _ (EAp _ _) _) => 
  eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.
(* end hide *)
(** In a manner similar to the notation in big-step semantics, we define a 
multi step relation (%$\Longrightarrow$*%)for small-step. 

*)
(* begin hide *)
Notation multistep := (multi smallStep).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).
Hint Constructors smallStep.

Module SmallStepSamples.
(* end hide *)
(** In the following section, through a variety
of examples, we show that the sample expressions type checks and applying 
small step semantics on these expressions, produces valid reductions.

*)
(* begin hide *)
Notation a := (Id 0).
Notation f := (Id 1).
Notation g := (Id 2).
Notation x := (Id 3).
Notation y := (Id 4).
Notation n := (Id 5).
Notation m := (Id 6).

Module Numtest.
(* end hide *)

Definition eqTest :=
    EEq (ENum 5) (ENum 1).

Example eqTestTypeChecks :
  (@empty typeH) |- eqTest \in BoolType.
Proof.
  unfold eqTest.
  auto 10.
Qed.
(** printing ==>* %$\ensuremath{\Longrightarrow}$*% *)

Example eqTestReduces :
    eqTest ==>* EBool false.
Proof.
    unfold eqTest. normalize.
Qed.

Definition ifTest :=
    EIf 
        (EEq (ENum 5) (ENum 1))
        (ENum 1) 
        (ENum 0).

Example ifTestTypeChecks :
  (@empty typeH) |- ifTest \in NumType.
Proof.
  unfold ifTest.
  auto 10.
Qed.

Example ifTestReduces :
  ifTest ==>* ENum 0.
Proof.
    unfold ifTest.
    normalize.
Qed.

(* begin hide *)
Definition num_test0 :=
    EIf 
        (EEq (ENum 5) (EPlus (ENum 4) (ENum 1)))
        (EMult (ENum 5) (ENum 6)) 
        (ENum 0).

Example typechecks :
  (@empty typeH) |- num_test0 \in NumType.
Proof.
  unfold num_test0.
  auto 10.
Qed.

Example num_test0_reduces :
  num_test0 ==>* ENum 30.
Proof.
  unfold num_test0. normalize.
Qed.

End Numtest.

Module LetTest.
(* end hide *)

Notation x := (Id 3).

Definition let_test :=
  ELet
    x
    (ENum 6)
    (EPlus (EVar x) (ENum 1)).

Example let_test_typechecks :
  (@empty typeH) |- let_test \in NumType.
Proof. unfold let_test. eauto 15. Qed.

Example let_test_reduces :
  let_test ==>* ENum 7.
Proof. unfold let_test. normalize. Qed.

(* begin hide *)
Definition let_test1 :=
    ELet x (EMinus (ENum 1) (ENum 5))
        (EMult (EVar x) (EVar x)).

Example let_test1_reduces :
    let_test1 ==>* ENum 16.
Proof.
    unfold let_test1. normalize. Qed.

End LetTest.

Module FixTest1.
(* end hide *)

Definition fact :=
    EFix
        (EAbs f (ArrowType NumType NumType)
        (EAbs a NumType
            (EIf 
                (EEq (EVar a) (ENum 0))
                (ENum 1)
                (EMult 
                    (EVar a) 
                    (EAp (EVar f) (EMinus (EVar a) (ENum 1))))))).

Example fact_typechecks :
  (@empty typeH) |- fact \in (ArrowType NumType NumType).
Proof. unfold fact. auto 10. 
Qed.

Example fact_example: 
  (EAp fact (ENum 4)) ==>* (ENum 24).
Proof. unfold fact. normalize. Qed.

(* begin hide *)
End FixTest1.
End SmallStepSamples.
(* end hide *)
(** *** Progress in small-step
Contrary to big-step, progress is important in small-step. In the 
following theorem we prove that the progress property is indeed satisfied by
our presentation of the small-step semantics on %\textbf{H}%. In the
following proof, we utilize the Coq tactic notation [Case], [SCase] etc. from 
SfLib to label the proof that is being handled.

*)
Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.

(** This theorem states that if term [t] has type [T] in the empty 
context, then either [t] is a [value] or there exists a [t']
such that [t] steps to it. This theorem is important as it illustrates
that the small-step relation defined fo %\textbf{H}% does not lead to 
terms that do not make progress.

*)
Proof with eauto.
    intros t T Ht.
    remember (@empty typeH) as Gamma.
    generalize dependent HeqGamma.
    has_type_cases (induction Ht) Case; intros HeqGamma; subst.
    Case "T_Var".
        inversion H.
(** Since variables are not typed in the empty context, [t] cannot 
be a variable. If [t] is an application having the form [t1 t2], then there are
two possible forms [t1] can take, either [t1] is a value or [t1] steps.
If [t1] is a value and if [t2] is a value, then there exists a substituion
and [t] steps. On the other hand if [t2] steps, then again [t] steps to 
[t']. If we consider that [t1] can take a step, in which case we say that 
[t] stepped to [t']. Similar reasoning is applied to rest of the possible
cases.

*)               
    Case "T_Abs".
        left...
    Case "T_App".
        right.
        destruct IHHt1; subst...
        SCase "t1 is a value".
            destruct IHHt2; subst...
            SSCase "t2 is a value".
                inversion H; subst; try (solve by inversion).
                exists (subst x t2 t12)...
            SSCase "t2 steps".
                inversion H0 as [t2' Hstp]. exists (EAp t1 t2')...
        SCase "t1 steps".
            inversion H as [t1' Hstp]. exists (EAp t1' t2)...
    Case "T_Num".
        left...
    Case "T_Bool".
        left...
    Case "T_Plus".
        right.
        destruct IHHt1...
        SCase "t1 is a value".
            destruct IHHt2...
            SSCase "t2 is a value".
                inversion H; subst; try solve by inversion.
                inversion H0; subst; try solve by inversion.
                exists (ENum (x + x0))...
            SSCase "t2 steps".
                inversion H0 as [t2' Hstp].
                exists (EPlus t1 t2')...
        SCase "t1 steps".
            inversion H as [t1' Hstp].
            exists (EPlus t1' t2)...
    Case "T_Minus".
        right.
        destruct IHHt1...
        SCase "t1 is a value".
            destruct IHHt2...
            SSCase "t2 is a value".
                inversion H; subst; try solve by inversion.
                inversion H0; subst; try solve by inversion.
                exists (ENum (x - x0))...
            SSCase "t2 steps".
                inversion H0 as [t2' Hstp].
                exists (EMinus t1 t2')...
        SCase "t1 steps".
            inversion H as [t1' Hstp].
            exists (EMinus t1' t2)...
    Case "T_Mult".
        right.
        destruct IHHt1...
        SCase "t1 is a value".
            destruct IHHt2...
            SSCase "t2 is a value".
                inversion H; subst; try solve by inversion.
                inversion H0; subst; try solve by inversion.
                exists (ENum (x * x0))...
            SSCase "t2 steps".
                inversion H0 as [t2' Hstp].
                exists (EMult t1 t2')...
        SCase "t1 steps".
            inversion H as [t1' Hstp].
            exists (EMult t1' t2)...

    Case "T_If".
        right.
        destruct IHHt1...
        SCase "t1 is a value".
            inversion H; subst; try solve by inversion.
            destruct x as [|x'].
            SSCase "x = true".
                exists t2...
            SSCase "x = false".
                exists t3...
        SCase "t1 steps".
            inversion H as [t1' H0].
            exists (EIf t1' t2 t3)...
    Case "T_Unit".
        left...
    Case "T_Let".
        right.
        destruct IHHt1...
        SCase "t1 steps".
            inversion H as [t1' Hstp].
            exists (ELet x t1' t2)...
    Case "T_Fix".
        right.
        destruct IHHt...
        SCase "t1 is a value".
            inversion H; subst; try solve by inversion...
            inversion H...
    Case "T_Eq".
        right.
        destruct IHHt1...
        SCase "t1 is a value".
            destruct IHHt2...
            SSCase "t2 is also a value".
                inversion H; subst; try solve by inversion.
                inversion H0; subst; try solve by inversion.
                exists (EBool (beq_Z x x0))...
            SSCase "t2 steps".
                inversion H0 as [t2' Hstp].
                exists (EEq t1 t2')...
        SCase "t1 steps".
            inversion H as [t1' Hstp].
            exists (EEq t1' t2)...
Qed.
(** *** Type preservation in small-step 
Having proved the requisite theorems and lemmas, we can now prove that the
small-step semantics for %\textbf{H}% guarantee type preservation.

*)
Theorem small_step_preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.
Proof with eauto.
    intros t t' T HT.
    remember (@empty typeH) as Gamma. generalize dependent HeqGamma.
    generalize dependent t'.
    has_type_cases (induction HT) Case; 
    intros t' HeqGamma HE; subst; inversion HE; subst...
    Case "T_App".
        inversion HE; subst...
        SCase "SST_AppAbs".
            apply substitution_preserves_typing with T1...
            inversion HT1...
    Case "T_Let".
        eapply substitution_preserves_typing...
    Case "T_Fix".
        eapply substitution_preserves_typing...
        inversion HT...
Qed.
(* begin hide *)
End SmallStep.
(* end hide *)

End Hi.

