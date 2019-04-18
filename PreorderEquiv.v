Section PreorderEquiv.
  Require Import MyNotations.

  (** * Preorders and induced equivalence relations
      
      This module defines preorders and the equivalence
      relation they induce on their carrier. Following
      math-classes, this equivalence relation is 
      denoted by [=], and we reserve [≡] for coq's equality.
    *) 
  
  Context {T : Type}.
  Context {Tle : Le T}.

  Class Preorder {T : Type} (le : Le T) :=
    MkPreorder
      {
        le_refl : forall x, x ≤ x;
        le_trans : forall x y z, x ≤ y -> y ≤ z -> x ≤ z;
      }.

  Variable po : Preorder le.

  Definition Feq (x y : T) := x ≤ y /\ y ≤ x.
  Instance Feq_equiv : Equiv T := Feq.
  Hint Unfold Feq_equiv Feq.

  (** A simple tactic that tries to solve
      inequations with the preorder axioms. *)
  
  Ltac preorder :=
    unfold Feq_equiv, Feq in * ; repeat (
    match goal with
      | [ H : ?U /\ ?V |- _ ] => destruct H                           
      | [ |- ?H /\ ?G ] => split
      | [ H : ?A |- ?A ] => assumption
      | [ |- ?A -> ?B ] => intro 
      | [ |- ?x ≤ ?x ] => apply le_refl
      | [ H1 : ?a ≤ ?b, H2 : ?b ≤ ?c |- ?a ≤ ?c ] =>
        apply (le_trans a b c H1 H2)
    end).

  Lemma Feq_refl : Reflexive Feq.
  Proof.
    unfold Reflexive.
    intros. preorder.
  Qed.

  Lemma Feq_trans : Transitive Feq.
  Proof.
    unfold Transitive.
    intros. preorder.
  Qed.

  Lemma Feq_sym : Symmetric Feq.
  Proof.
    unfold Symmetric.
    intros. preorder.
  Qed.

  Definition Feq_equivalence :=
    Build_Equivalence Feq Feq_refl Feq_sym Feq_trans.

  Lemma le_proper_Feq (x y u v : T) : (x = y) -> (u = v) -> (x ≤ u) = (y ≤ v).
  Proof.
    unfold_selected.
    intros.
    preorder.
    assert (x ≤ v) ; preorder.
    assert (x ≤ v) ; preorder.
  Qed.

  Definition reformulate_Feq : forall eq : relation T,
      (forall x y, eq x y <-> x = y) -> Equivalence eq.
  Proof.
    intros.
    apply Build_Equivalence ; unfold Reflexive, Symmetric, Transitive ; setoid_rewrite H.
    exact Feq_refl.
    exact Feq_sym.
    exact Feq_trans.
  Qed.

End PreorderEquiv.


Add Parametric Relation (T : Type) (Tle : Le T) (PO : Preorder Tle): T Feq
    reflexivity proved by (Feq_refl PO)
    symmetry proved by (Feq_sym)
    transitivity proved by (Feq_trans PO)
      as setoid_msl.

Add Parametric Morphism (T : Type) (Tle : Le T) (PO : Preorder Tle) : Tle with signature (Feq ==> Feq ==> iff) as preorder_le_morphism.
Proof.
  intros. apply (le_proper_Feq PO) ; assumption.
Qed.

(** * Preorder morphisms *)

Section PreorderMorphism.
  Context {T1 T2 : Type}.
  Context {le1 : Le T1}.
  Context {le2 : Le T2}.

  Variable (po1 : Preorder le1).
  Variable (po2 : Preorder le2).

  Class POMorphism (f : T1 -> T2) :=
    MkPOMorphism
      {
        pomorph_le : forall x y, x ≤ y -> f x ≤ f y
      }.

  Variable f : T1 -> T2.
  Variable pom : POMorphism f.

  Proposition pomorphism_proper : Proper (Feq ==> Feq) f.
  Proof.
    unfold Proper, respectful, Feq.
    intros. destruct H.
    split ; apply pomorph_le ; assumption.
  Qed.
 

End PreorderMorphism.

Section PreorderMorphism2.
  Context {T1 T2 T3 : Type}.
  Context {le1 : Le T1}.
  Context {le2 : Le T2}.
  Context {le3 : Le T3}.

  Variable (po1 : Preorder le1).
  Variable (po2 : Preorder le2).
  Variable (po3 : Preorder le3).

  Class POMorphism2 (f : T1 -> T2 -> T3) :=
    MkPOMorphism2
      {
        pomorph2_le : forall x y a b, x ≤ y -> a ≤ b -> f x a ≤ f y b
      }.

  Variable f : T1 -> T2 -> T3.
  Variable pom : POMorphism2 f.

  Proposition pomorphism2_proper : Proper (Feq ==> Feq ==> Feq) f.
  Proof.
    unfold Proper, respectful, Feq.
    intros. destruct H, H0.
    split ; apply pomorph2_le ; assumption.
  Qed.

End PreorderMorphism2.

Add Parametric Morphism T1 T2 (le1 : Le T1) (le2 : Le T2) (f : T1 -> T2) (fm : POMorphism f): f with signature (Feq ==> Feq) as fm_morphism.
Proof.
  apply pomorphism_proper ; assumption.
Qed.

Section PreorderComp.
  
  Context {T1 T2 T3 : Type}.
  
  Context {le1 : Le T1}.
  Context {le2 : Le T2}.
  Context {le3 : Le T3}.

  Variable f : T1 -> T2.
  Variable g : T2 -> T3.
  Variable pomf : POMorphism f.
  Variable pomg : POMorphism g. 

  Definition POcomp : POMorphism (g ∘ f).
  Proof.
    apply MkPOMorphism.
    unfold compose.
    intros.
    apply pomorph_le.
    apply pomorph_le.
    assumption.
  Defined.
    
End PreorderComp.

