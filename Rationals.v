Require Import QArith.
Require Import JoinSemiLattice.
Require Import PreorderEquiv.
Require Import MathClasses.interfaces.canonical_names.

Section Rationals.

Instance q_le : Le Q := Qle.
Instance q_equiv : Equiv Q := Qeq.
Instance q_lt : Lt Q := Qlt.
Instance q_zero : Zero Q := 0#1.
Instance q_plus : Plus Q := Qplus.
Instance q_mult : Mult Q := Qmult.

Instance q_Preorder : Preorder q_le :=
  MkPreorder
    Q
    Qle
    Qle_refl
    Qle_trans.

Definition Qmax (x y :Q) : Q :=
  match x ?= y with
  | Gt => x
  | Lt => y
  end.

Instance q_join : Join Q := Qmax.

Lemma Qmax_l : forall x y, x ≤ x ⊔ y.
Proof.
  intros.
  unfold join, q_join, Qmax.
  destruct (x ?= y) eqn:?.
  - rewrite <- Qeq_alt in Heqc.
    rewrite Heqc.
    apply le_refl.
  - rewrite <- Qlt_alt in Heqc.
    apply Qlt_le_weak. assumption.
  - apply le_refl.
Qed.

Lemma Qmax_r : forall x y, y ≤ x ⊔ y.
Proof.
  intros.
  unfold join, q_join, Qmax.
  destruct (x ?= y) eqn:?.
  - apply le_refl.
  - apply le_refl.
  - rewrite <- Qgt_alt in Heqc.
    apply Qlt_le_weak. assumption.
Qed.

Lemma Qmax_univ : forall x y z, x ≤ z -> y ≤ z -> x ⊔ y ≤ z.
Proof.
  intros.
  unfold join, q_join, Qmax.
  destruct (x ?= y) eqn:?.
  - rewrite <- Qeq_alt in Heqc. assumption.
  - assumption.
  - assumption.
Qed.

Instance q_JSL : JoinSemiLattice q_le :=
  MkJSL
    Q
    q_le
    q_Preorder
    Qmax
    Qmax_l
    Qmax_r
    Qmax_univ.

End Rationals.
