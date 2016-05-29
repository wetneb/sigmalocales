Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Coq.QArith.QArith.
Require Import Coq.Classes.Morphisms.

Module Type HasLeEquiv := EqLe' <+ IsEq.

Module Type IsPoset (Import T: HasLeEquiv).
  Axiom refl: Reflexive le.
  Axiom trans: Transitive le.
  Axiom antisym: forall x y, x <= y -> y <= x -> x == y.
  Axiom le_morphism : Proper (eq ==> eq ==> iff) le.
End IsPoset.

Module Type Poset := HasLeEquiv <+ IsPoset.

Open Scope signature_scope.
Module Rat <: Poset.
  Definition t := Q.
  Definition le := Qle.
  Definition eq := Qeq.
  Definition refl := Qle_refl.
  Definition trans := Qle_trans.
  Definition antisym := Qle_antisym.
  Definition eq_equiv := Q_Setoid.
  Definition le_morphism := Qle_comp.
End Rat.

Module PosRat <: Poset.
  Record t_orig := MkPosRat { rat:Q; posrat: (0 <= rat)%Q }.
  Definition t := t_orig.
  Definition le := fun (x y:t) =>  Qle (rat x) (rat y).
  Definition eq := fun (x y:t) =>  Qeq (rat x) (rat y).
  Lemma refl : forall x : t, le x x.
  Proof. intros. unfold le. apply Qle_refl. Qed.
  Lemma trans : forall x y z : t, le x y -> le y z -> le x z.
  Proof. unfold le. intros x y z. apply Qle_trans. Qed.
  Lemma antisym : forall x y : t, le x y -> le y x -> eq x y.
  Proof. unfold le. intros x y. apply Qle_antisym. Qed.
  Lemma eq_refl : Reflexive eq.
  Proof. unfold Reflexive, eq. intros. apply Qeq_refl. Qed.
  Lemma eq_sym : Symmetric eq.
  Proof. unfold Symmetric, eq. intros x y. apply Qeq_sym. Qed.
  Lemma eq_trans : Transitive eq.
  Proof. unfold Transitive, eq. intros x y z. apply Qeq_trans. Qed.
  Definition eq_equiv := (Build_Equivalence t eq eq_refl eq_sym eq_trans).
  Lemma le_morphism : Proper (eq ==> eq ==> iff) le.
  Proof.
    unfold Proper, respectful, le, eq.
    intros.
    setoid_rewrite H. setoid_rewrite H0.
    reflexivity.
  Qed.
End PosRat.
  
Module Type Commonoid (Import P:Poset).
  Parameter f : t -> t -> t.
  Parameter f_unit : t.

  Axiom f_unit_l : forall x, f f_unit x == x.
(*  Axiom f_unit_r : forall x, f x f_unit == x. *)
  Axiom f_incr_l : forall x y z, x <= y -> f x z <= f y z.
  Axiom f_comm: forall x y, f x y == f y x.
  Axiom f_assoc: forall x y z, f x (f y z) == f (f x y) z.
  Axiom f_proper: Proper (eq ==> eq ==> eq) f.
End Commonoid.

Module Commonoid' (Import P : Poset) (Import C : Commonoid P) <: (Commonoid P).
  Definition f := f.
  Definition f_unit := f_unit.
  Definition f_unit_l := f_unit_l.
  Definition f_incr_l := f_incr_l.
  Definition f_comm := f_comm.
  Definition f_assoc := f_assoc.
  Definition f_proper := f_proper.
  Lemma f_unit_r : forall x, f x f_unit == x.
  Proof.
    intros. setoid_rewrite (f_comm x f_unit).
    apply f_unit_l.
  Qed.
  Lemma f_incr_r : forall x y z, x <= y -> f z x <= f z y.
  Proof.
    intros.
    setoid_rewrite (f_comm z x).
    setoid_rewrite (f_comm z y).
    apply (f_incr_l _ _ _ H).
  Qed.
End Commonoid'.
  
Module Sum (T:Poset) (Com0 : Commonoid T).
  Module Com := Commonoid' T Com0.
  Definition plus := Com.f.
  Definition zero := Com.f_unit.
  Definition plus_0_l := Com.f_unit_l.
  Definition plus_0_r := Com.f_unit_r.
  Definition plus_le_l := Com.f_incr_l.
  Definition plus_le_r := Com.f_incr_r.
  Definition plus_comm := Com.f_comm.
  Definition plus_assoc := Com.f_assoc.
End Sum.

Module Mult (T:Poset) (Com0 : Commonoid T).
  Module Com := Commonoid' T Com0.
  Definition mult := Com.f.
  Definition one := Com.f_unit.
  Definition mult_1_l := Com.f_unit_l.
  Definition mult_1_r := Com.f_unit_r.
  Definition mult_le_l := Com.f_incr_l.
  Definition mult_le_r := Com.f_incr_r.
  Definition mult_comm := Com.f_comm.
  Definition mult_assoc := Com.f_assoc.
End Mult.

Module RatSumCommonoid <: Commonoid Rat.
  Definition f := fun x y => (x + y)%Q.
  Definition f_unit := (0%Q).
  Definition f_unit_l := Qplus_0_l.
  Lemma f_incr_l : forall x y z, (x <= y)%Q -> (f x z <= f y z)%Q.
  Proof.
    intros.
    apply (Qplus_le_compat _ _ _ _ H).
    apply Qle_refl.
  Qed.
  Definition f_comm := Qplus_comm.
  Definition f_assoc := Qplus_assoc.
  Definition f_proper := Qplus_comp.
End RatSumCommonoid.

Module PosRatSumCommonoid <: Commonoid PosRat.
  Import PosRat.
  Infix "≃" := eq (at level 70) : commonoid_rat_scope.
  Infix "⪯" := le (at level 70) : commonoid_rat_scope.
  Open Scope commonoid_rat_scope.
  
  Lemma sum_of_posrat : forall x y, 0 <= x -> 0 <= y -> 0 <= x + y.
  Proof. intros. rewrite <- Qplus_0_l.
         apply (Qplus_le_compat _ _ _ _ H H0).
  Qed.
  Definition f (x y : t) :=
    MkPosRat ((rat x) + (rat y))
             (sum_of_posrat (rat x) (rat y) (posrat x) (posrat y)).
  Infix "⊕" := f (at level 50) : commonoid_rat_scope.

  Definition f_unit := MkPosRat 0 (Qle_refl 0).
  Lemma f_unit_l : forall x, f_unit ⊕ x ≃ x.
  Proof.
    intros.
    unfold eq, f, f_unit. simpl.
    apply Qplus_0_l.
  Qed.
  Lemma f_incr_l : forall x y z, x ⪯ y -> x ⊕ z ⪯ y ⊕ z.
  Proof.
    unfold le, f. simpl. intros.
    setoid_rewrite (Qplus_le_l (rat x) (rat y) (rat z)).
    assumption.
  Qed.
  Lemma f_comm : forall x y, x ⊕ y ≃ y ⊕ x.
  Proof.
    unfold eq, f. simpl. intros. apply Qplus_comm.
  Qed.
  Lemma f_assoc : forall x y z, x ⊕ (y ⊕ z) ≃ (x ⊕ y) ⊕ z.
  Proof.
    unfold eq, f. simpl. intros.
    apply Qplus_assoc.
  Qed.
  Lemma f_proper : Proper (eq ==> eq ==> eq) f.
  Proof.
    unfold Proper, respectful, eq, f.
    intros. simpl.
    setoid_rewrite H.
    setoid_rewrite H0.
    reflexivity.
  Qed.
End PosRatSumCommonoid.

