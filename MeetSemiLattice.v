Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import Setoid.
Require Import MathClasses.interfaces.canonical_names.

Section MeetSemiLattice_definition.

Class MeetSemiLattice `{t : Type} `{Le t} :=
  MkMSL {
      (* preorder *)
      le_refl: forall x, x ≤ x;
      le_trans: forall x y z, x ≤ y -> y ≤ z -> x ≤ z;
      
      (* top, bottom *)
      msl_top :> Top t;
      top_le: forall x, x ≤ ⊤;
                     msl_bot :> Bottom t;
      bot_le: forall x, ⊥ ≤ x;

      (* meet *)
      msl_meet :> Meet t;
      meet_l: forall x y, x ⊓ y ≤ x;
      meet_r: forall x y, x ⊓ y ≤ y;
      meet_univ: forall x y z, z ≤ x -> z ≤ y -> z ≤ x ⊓ y;
    }.


Context {t : Type}.
Variable rel : Le t.
Variable MSL : @MeetSemiLattice t rel.

Definition Feq `{MeetSemiLattice t} (x y:t) : Prop :=
  (x ≤ y /\ y ≤ x).

Lemma Feq_refl : Reflexive Feq.
Proof.
  unfold Reflexive, Feq.
  intros. split. apply le_refl. apply le_refl.
Qed.

Lemma Feq_sym : Symmetric Feq.
Proof.
  firstorder.
Qed.

Lemma Feq_trans : Transitive Feq.
Proof.    
  unfold Transitive, Feq.
  intros.
  destruct H as [H1 H2].
  destruct H0 as [H3 H4].
  split.
  apply (le_trans _ y _ H1 H3).
  apply (le_trans _ y _ H4 H2).
Qed.

Definition Feq_equiv := Build_Equivalence Feq Feq_refl Feq_sym Feq_trans.
Instance Fequiv : Equiv t := Feq.

Add Setoid t Feq Feq_equiv as Feq_setoid.

Lemma le_proper : Proper ((=) ==> (=) ==> iff) le.
Proof.  
  unfold Proper, Feq, respectful.
  firstorder.
  apply (le_trans _ x _ H2).
  apply (le_trans _ x0 _ H3 H0).
  apply (le_trans _ y _ H).
  apply (le_trans _ y0 _ H3 H1).
Qed.

Add Parametric Morphism : le with signature ((=) ==> (=) ==> iff) as le_morphism.
Proof. apply le_proper. Qed.

(* meets *)
Lemma meet_le_l : forall x y z, x ≤ y -> x ⊓ z ≤ y ⊓ z.
Proof.
  intros.
  apply meet_univ.
  apply (le_trans _ x _).
  apply meet_l. assumption.
  apply meet_r.
Qed.

Lemma meet_le_r : forall x y z, x ≤ y -> z ⊓ x ≤ z ⊓ y.
Proof.    
  intros.
  apply meet_univ.
  apply meet_l.
  apply (le_trans _ x _).
  apply meet_r. assumption.
Qed.

Lemma meet_le : forall x y z w, x ≤ y -> z ≤ w -> x ⊓ z ≤ y ⊓ w.
Proof.
  intros.
  apply (le_trans _ (x ⊓ w) _).
  apply (meet_le_r _ _ _ H0).
  apply (meet_le_l _ _ _ H).
Qed.

Add Morphism meet : meet_morphism.
Proof.
  firstorder.
  apply (meet_le _ _ _ _ H H0).
  apply (meet_le _ _ _ _ H2 H1).
Qed.

Lemma meet_comm : forall x y, x ⊓ y = y ⊓ x.
Proof.
  unfold Feq.
  intros. split.
  apply meet_univ. apply meet_r. apply meet_l.
  apply meet_univ. apply meet_r. apply meet_l.
Qed.

Lemma meet_assoc : forall x y z, x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z.
Proof.  
  intros.
  unfold Feq. split ; apply meet_univ.

  apply meet_le_r.
  apply meet_l.
  apply (le_trans _ (x ⊓ z) _).
  apply meet_le_r.
  apply meet_r.
  apply meet_r.

  apply (le_trans _ (x ⊓ z) _).
  apply meet_le_l.
  apply meet_l.
  apply meet_l.
  apply meet_le_l.
  apply meet_r.
Qed.

Lemma meet_idem : forall x, x ⊓ x = x.
Proof.
  intros.
  unfold Feq. split.
  apply meet_l.
  apply (meet_univ x x x (le_refl x) (le_refl x)).
Qed.

Lemma meet_bot_l : forall x, ⊥ ⊓ x = ⊥.
Proof.
  intros. split.
  apply meet_l.
  apply meet_univ.
  apply le_refl.
  apply bot_le.
Qed.

Lemma meet_bot_r : forall x, x ⊓ ⊥ = ⊥.
Proof.
  intros. setoid_rewrite meet_comm.
  apply meet_bot_l.
Qed.

Lemma meet_top_l : forall x, ⊤ ⊓ x = x.
Proof.
  intro. split.
  apply meet_r.
  apply meet_univ.
  apply top_le.
  apply le_refl.
Qed.

Lemma meet_top_r : forall x, x ⊓ ⊤ = x.
Proof.
  intro. setoid_rewrite meet_comm.
  apply meet_top_l.
Qed.

Lemma order_meet : forall x y, x ≤ y <-> x ⊓ y = x.
Proof.
  intros.
  unfold iff. split.

  intros. split.
  apply meet_l.
  apply (le_trans _ (x ⊓ x) _).
  setoid_rewrite meet_idem. apply le_refl.
  apply meet_le_r.
  apply H.
  intro.
  setoid_rewrite <- H.
  apply meet_r.
Qed.

End MeetSemiLattice_definition.