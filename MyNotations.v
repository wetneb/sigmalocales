
Require Export MathClasses.interfaces.canonical_names.
Require Import QArith.

Ltac unfold_selected := repeat autounfold with *.

Instance Prop_equiv : Equiv Prop := iff.
Hint Unfold equiv Prop_equiv.

Class OpMult (Tf A : Type) := opmult : Tf -> A -> A -> A.
Notation "a ⊗ f b" := (opmult f a b) (at level 100).

Instance q_le : Le Q := Qle.
Instance q_equiv : Equiv Q := Qeq.
Instance q_lt : Lt Q := Qlt.
Instance q_zero : Zero Q := 0#1.
Instance q_plus : Plus Q := Qplus.
Instance q_mult : Mult Q := Qmult.


