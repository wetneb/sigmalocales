
Require Export MathClasses.interfaces.canonical_names.


Ltac unfold_selected := repeat autounfold with *.

Instance Prop_equiv : Equiv Prop := iff.
Hint Unfold equiv Prop_equiv.

