Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import PreorderEquiv.
Require Import MyNotations.

Section JoinSemiLattice_definition.
  
  Class JoinSemiLattice `{T : Type} (Tle : Le T) :=
    MkJSL {
        (* preorder *)
        msl_preorder :> Preorder Tle;
        
        (* meet *)
        jsl_join :> Join T;
        join_l: forall x y, x ≤ x ⊔ y;
        join_r: forall x y, y ≤ x ⊔ y;
        join_univ: forall x y z, x ≤ z -> y ≤ z -> x ⊔ y ≤ z;
      }.

  Context {T : Type}.
  Variable Tle : Le T.
  Variable JSL : @JoinSemiLattice T Tle.

  Existing Instance Feq_equiv.

  Create HintDb joinsemilattice.
  Hint Resolve le_refl join_l join_r.
  Ltac joinsemilattice := auto with joinsemilattice.

  (** ** Properties of the join *)
  Lemma join_le_l : forall x y z, x ≤ y -> x ⊔ z ≤ y ⊔ z.
  Proof.
    intros.
    apply join_univ.
    apply (le_trans _ y _).
    assumption.
    apply join_l.
    apply join_r.
  Qed.

  Lemma join_le_r : forall x y z, x ≤ y -> z ⊔ x ≤ z ⊔ y.
  Proof.    
    intros.
    apply join_univ.
    apply join_l.
    apply (le_trans _ y _).
    assumption.
    apply join_r.
  Qed.

  Lemma join_le : forall x y z w, x ≤ y -> z ≤ w -> x ⊔ z ≤ y ⊔ w.
  Proof.
    intros.
    apply (le_trans _ (x ⊔ w) _).
    apply (join_le_r _ _ _ H0).
    apply (join_le_l _ _ _ H).
  Qed.

  Add Parametric Morphism : join with signature (Feq ==> Feq ==> Feq) as join_morphism.
  Proof.
    firstorder ; apply join_le ; assumption.
  Qed.

  Lemma join_comm : forall x y: T, x ⊔ y = y ⊔ x.
  Proof.
    unfold Feq.
    intros. split ; (
     apply join_univ ; [ apply join_r | apply join_l ]).
  Qed.

  Lemma join_assoc : forall x y z, x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z.
  Proof.  
    intros.
    unfold Feq. split ; apply join_univ.

    - apply (le_trans _ (x ⊔ y) _) ; joinsemilattice.
    - apply join_univ.
      apply (le_trans _ (x ⊔ y) _) ; joinsemilattice.
      apply join_r.
    - apply join_univ ; joinsemilattice.
      apply (le_trans _ (y ⊔ z) _) ; joinsemilattice.
    - apply (le_trans _ (y ⊔ z) _) ; joinsemilattice.
  Qed.

  Lemma join_idem : forall x, x ⊔ x = x.
  Proof.
    intros.
    unfold Feq. split.
    apply join_univ ; apply le_refl.
    apply join_l.
  Qed.

  Lemma order_then_join : forall x y, x ≤ y -> x ⊔ y = y.
  Proof.
    intros. split.
    apply join_univ.
    assumption.
    apply le_refl.
    apply join_r.
  Qed.

  Lemma join_then_order : forall x y, x ⊔ y = y -> x ≤ y.
  Proof.
    intros.
    setoid_rewrite <- H.
    apply join_l.
  Qed.
  
  Lemma order_join : forall x y, x ≤ y <-> x ⊔ y = y.
  Proof.
    intros ; split.
    apply order_then_join.
    apply join_then_order.
  Qed.

End JoinSemiLattice_definition.

  

