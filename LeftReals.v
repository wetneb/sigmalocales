
Require Import Setoid.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.QArith.QArith.
Require Import Coq.Init.Notations.
Require Import Basics.

Module LeftCompletion (Q:Poset) <: Poset.

  Delimit Scope LC_scope with LR.
  Open Scope LC_scope.

  Infix "<=" := Q.le (at level 70).
  Infix "==" := Q.eq (at level 70).
  Add Setoid Q.t Q.eq Q.eq_equiv as qt_setoid.
  Add Morphism Q.le : qle_morphism.
  Proof.
    apply Q.le_morphism.
  Qed.

Definition MonotoneSeq (qs : nat -> Q.t) : Prop :=
  forall (x y : nat), (x <= y)%nat -> qs x <= qs y.
Definition BoundedSeq (qs : nat -> Q.t) : Prop :=
  exists q : Q.t, forall x : nat, qs x <= q.

Record t_orig : Type := MkLC
  {
    qlb : nat -> Q.t;
    qlb_monotone : MonotoneSeq qlb;
    qlb_bounded : BoundedSeq qlb
  }.
Definition t := t_orig.

Definition le (a b : t) : Prop :=
  forall x : nat, exists y : nat, qlb a x <= qlb b y.

Notation "a ⪯ b" := (le a b) (at level 70, no associativity) : LC_scope.

Lemma refl : forall r : t, r ⪯ r.
Proof.
  intros. unfold le. intros. exists x. apply Q.refl.
Qed.

Lemma trans : Transitive le.
Proof.
  unfold Transitive. unfold le. intros.
  specialize (H x0).
  destruct H as [y2 H].
  specialize (H0 y2).
  destruct H0 as [y3 H2].
  exists y3. apply (Q.trans _ (qlb y y2) _ H H2).
Qed.

Definition eq (a b : t) : Prop := a ⪯ b /\ b ⪯ a.

Infix "≃" := eq (at level 70, no associativity) : LC_scope.

Lemma eq_refl : Reflexive eq.
Proof.
  unfold Reflexive.
  intros. unfold eq. split.
  apply refl. apply refl.
Qed.

Lemma eq_sym : Symmetric eq.
Proof.
  unfold Symmetric.
  intros.
  unfold eq. destruct H as [H1 H2].
  split. assumption. assumption.
Qed.

Lemma eq_trans : Transitive eq.
Proof.
  unfold Transitive.
  intros.
  unfold eq. unfold eq in H, H0.
  destruct H, H0.
  split. apply (trans x y z H H0).
  apply (trans z y x H2 H1).
Qed.

Lemma antisym : forall x y : t, (x ⪯ y) -> (y ⪯ x) -> (x ≃ y).
Proof.
  intros. unfold eq. split. assumption. assumption.
Qed.

Lemma eq_seqs : forall x y : t, (forall n, (qlb x n) == (qlb y n)) -> x ≃ y.
Proof.
  intros.
  unfold eq. unfold le. split.

  intro a. exists a. setoid_rewrite (H a). apply Q.refl.
  intro a. exists a. setoid_rewrite (H a). apply Q.refl.
Qed.

Definition eq_equiv :=
  Build_Equivalence t eq eq_refl eq_sym eq_trans.

Add Setoid t eq eq_equiv as eq_setoid.
Add Morphism le : le_morphism.
Proof.
  unfold eq.
  intros. destruct H as [H1 H2]. destruct H0 as [H3 H4].
  unfold iff. split.

  intros. apply (trans _ x _ H2). apply (trans _ x0 _ H H3).

  intros. apply (trans _ y _ H1). apply (trans _ y0 _ H H4).
Qed.

(* Injection of the rationals *)
Definition cst_t (q : Q.t) := (fun _ : nat => q).

Lemma cst_t_increasing : forall q : Q.t, MonotoneSeq (cst_t q).
Proof.
  unfold MonotoneSeq.
  intros. unfold cst_t. apply Q.refl.
Qed.

Lemma cst_t_bounded : forall q : Q.t, BoundedSeq (cst_t q).
Proof.
  unfold BoundedSeq.
  intros. exists q. intros. unfold cst_t. apply Q.refl.
Qed.

Definition inj (q : Q.t) := MkLC (cst_t q) (cst_t_increasing q) (cst_t_bounded q).

Lemma inj_strictly_increasing : forall p q : Q.t, p <= q <-> (inj p ⪯ inj q).
Proof.
  intros. unfold iff. split.

  intros.
  unfold le.
  intros. exists x.
  simpl. unfold cst_t. apply H.

  intros.
  unfold le in H.
  specialize (H 0%nat). simpl in H.
  destruct H as [y H]. unfold cst_t in H.
  apply H.
Qed.

Lemma inj_injective : forall p q : Q.t, inj p ≃ inj q -> p == q.
Proof.
  intros.
  unfold eq in H.
  destruct H as [H1 H2].
  apply (inj_strictly_increasing p q) in H1.
  apply (inj_strictly_increasing q p) in H2.
  apply (Q.antisym p q H1 H2).
Qed.

Add Morphism inj : inj_proper.
Proof.
  intros.
  apply eq_seqs. simpl.
  intro. setoid_rewrite H.
  reflexivity.
Qed.

Close Scope LC_scope.

End LeftCompletion.